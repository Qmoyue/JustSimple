package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import java.util.*;

/** Method-local source relations, shared by reference extraction and current-bytecode queries. */
public final class CallShape {
    private CallShape() {}
    public enum SourceKind { ABSENT, PARAMETER, FIELD, ELEMENT, RETURN, CONSTANT, ALLOCATION, UNKNOWN }
    public enum UseKind { RECEIVER, ARGUMENT, RETURNED, STORED, CONDITION }
    /** Non-platform names are roles. They never identify a benchmark class or a reference method. */
    public record Signature(String owner,String name,String descriptor) {
        @Override public int hashCode(){return (Objects.hashCode(owner)*31+Objects.hashCode(name))*31+Objects.hashCode(descriptor);}
        @Override public boolean equals(Object other){return other instanceof Signature value && Objects.equals(owner,value.owner) && Objects.equals(name,value.name) && Objects.equals(descriptor,value.descriptor);}
    }
    public record Step(SourceKind kind,String type,int slot,List<Signature> call) {
        public Step {Objects.requireNonNull(kind);Objects.requireNonNull(type);call=List.copyOf(call);}
    }
    public record Operand(int value,int parameter,List<Step> steps) {
        public Operand {steps=List.copyOf(steps);}
        private Operand(int parameter,List<Step> steps){this(-1,parameter,steps);}
        public boolean unknown(){return steps.stream().anyMatch(s -> s.kind()==SourceKind.UNKNOWN);}
    }
    public record Destination(UseKind kind,int operand,List<Signature> call) {
        public Destination {Objects.requireNonNull(kind);call=List.copyOf(call);}
    }
    public record Pattern(Signature target,int opcode,List<Operand> operands,List<Destination> result,Set<GuardKind> guards) {
        public Pattern {Objects.requireNonNull(target);operands=List.copyOf(operands);result=List.copyOf(result);guards=Set.copyOf(guards);}
        public boolean useful() {
            boolean linked=false,constant=false;int direct=0;
            for(Operand operand:operands) {
                boolean known=true;
                for(Step step:operand.steps()) {
                    if(step.kind()==SourceKind.UNKNOWN || step.kind()==SourceKind.ABSENT)known=false;
                    linked|=step.kind()==SourceKind.FIELD || step.kind()==SourceKind.ELEMENT || step.kind()==SourceKind.RETURN || step.kind()==SourceKind.ALLOCATION;
                    constant|=step.kind()==SourceKind.CONSTANT;
                }
                if(known)direct++;
            }
            return relevant(target,opcode,result.size(),linked,direct,constant);
        }
        static boolean relevant(Signature target,int opcode,int results,boolean linked,int direct,boolean constant) {
            return !target.name().startsWith("<") && (results>0 || linked || direct>1 || opcode==184 && !target.owner().equals("*") && constant);
        }
    }
    public record Requirement(Site site,Pattern pattern) {}

    public static Signature signature(Program program,MethodId method) {
        boolean api=platform(program,method.owner(),method.loader());
        return new Signature(api?method.owner():"*",api || method.name().startsWith("<")?method.name():"*",descriptor(program,method.descriptor(),method.loader()));
    }
    private static boolean platform(Program program,String type,int loader){
        return (type.startsWith("java/") || type.startsWith("javax/") || type.startsWith("jdk/") || type.startsWith("sun/") || type.startsWith("com/sun/"))
                && program.platformType(type,loader);
    }
    private static String descriptor(Program program,String descriptor,int loader) {
        StringBuilder result=new StringBuilder();
        for(int i=0;i<descriptor.length();i++) {
            char at=descriptor.charAt(i);if(at!='L'){result.append(at);continue;}
            int end=descriptor.indexOf(';',i);if(end<0)throw new IllegalArgumentException("invalid descriptor: "+descriptor);
            String type=descriptor.substring(i+1,end);result.append('L').append(platform(program,type,loader)?type:"*").append(';');i=end;
        }
        return result.toString();
    }
    /** Only transparent bytecode producers are followed; this does not interpret target methods. */
    public static Pattern of(Program program,Call call) {
        Flow flow=program.flow(call.site().method());Map<Integer,Integer> parameters=new LinkedHashMap<>();Map<FieldId,Integer> fields=new LinkedHashMap<>();
        List<Sources> sources=new ArrayList<>();sources.add(call.receiver());sources.addAll(call.arguments());
        List<Operand> operands=new ArrayList<>();
        Map<Sources,Integer> values=new LinkedHashMap<>();
        for(Sources source:sources) {
            Operand shape=source(program,flow,source,parameters,fields,new HashSet<>(),0,call.site().method().loader());
            Sources producer=transparent(flow,source,new HashSet<>(),0);
            int value=producer.origins().size()==1?values.computeIfAbsent(producer,k -> values.size()):-1;
            operands.add(new Operand(value,shape.parameter(),shape.steps()));
        }
        List<Destination> uses=new ArrayList<>();
        for(Action action:flow.producers().values()) {
            if(action instanceof Call next) {
                if(contains(flow,next.receiver(),call.site().instruction(),new HashSet<>(),0))uses.add(new Destination(UseKind.RECEIVER,-1,List.of(signature(program,next.target()))));
                for(int i=0;i<next.arguments().size();i++)if(contains(flow,next.arguments().get(i),call.site().instruction(),new HashSet<>(),0))uses.add(new Destination(UseKind.ARGUMENT,i,List.of(signature(program,next.target()))));
            } else if(action instanceof Returned returned && contains(flow,returned.value(),call.site().instruction(),new HashSet<>(),0))uses.add(new Destination(UseKind.RETURNED,-1,List.of()));
            else if(action instanceof WriteField write && contains(flow,write.value(),call.site().instruction(),new HashSet<>(),0)
                    || action instanceof WriteArray array && contains(flow,array.value(),call.site().instruction(),new HashSet<>(),0))uses.add(new Destination(UseKind.STORED,-1,List.of()));
            else if(action instanceof Branch branch && branch.inputs().stream().anyMatch(s -> contains(flow,s,call.site().instruction(),new HashSet<>(),0)))uses.add(new Destination(UseKind.CONDITION,-1,List.of()));
        }
        Set<GuardKind> guards=new LinkedHashSet<>();program.facts(call.site().method()).guards().getOrDefault(call.site().instruction(),List.of()).forEach(g -> guards.add(g.kind()));
        uses=uses.stream().distinct().sorted(Comparator.comparing((Destination d) -> d.kind().ordinal()).thenComparingInt(Destination::operand).thenComparing(d -> d.call().toString())).toList();
        return new Pattern(signature(program,call.target()),call.opcode(),operands,uses,guards);
    }
    private static Operand source(Program program,Flow flow,Sources sources,Map<Integer,Integer> parameters,Map<FieldId,Integer> fields,Set<Integer> seen,int depth,int loader) {
        if(sources.origins().isEmpty())return new Operand(-1,List.of(new Step(SourceKind.ABSENT,"",-1,List.of())));
        if(depth>=8 || sources.origins().size()!=1)return unknown();
        Origin origin=sources.origins().iterator().next();
        if(origin instanceof Parameter parameter)return new Operand(parameters.computeIfAbsent(parameter.slot(),k -> parameters.size()),List.of(new Step(SourceKind.PARAMETER,"",-1,List.of())));
        if(!(origin instanceof Producer producer) || !seen.add(producer.instruction()))return unknown();
        Action action=flow.producers().get(producer.instruction());
        if(action instanceof Cast cast)return source(program,flow,cast.input(),parameters,fields,seen,depth+1,loader);
        if(action instanceof Assign assign)return source(program,flow,assign.input(),parameters,fields,seen,depth+1,loader);
        if(action instanceof ReadField field)return append(source(program,flow,field.receiver(),parameters,fields,seen,depth+1,loader),new Step(SourceKind.FIELD,descriptor(program,field.field().descriptor(),field.field().loader()),fields.computeIfAbsent(field.field(),k -> fields.size()),List.of()));
        if(action instanceof ReadArray array)return append(source(program,flow,array.array(),parameters,fields,seen,depth+1,loader),new Step(SourceKind.ELEMENT,"",index(flow,array.index()),List.of()));
        if(action instanceof Call call) {
            Operand base=call.receiver().origins().isEmpty()?new Operand(-1,List.of()):source(program,flow,call.receiver(),parameters,fields,seen,depth+1,loader);
            return append(base,new Step(SourceKind.RETURN,descriptor(program,call.target().descriptor(),call.target().loader()),-1,List.of(signature(program,call.target()))));
        }
        if(action instanceof Constant constant) {
            String type=constant.value() instanceof ClassConstant?"java/lang/Class":constant.value() instanceof LiteralConstant literal && literal.value()!=null?literal.value().getClass().getSimpleName():"null";
            return new Operand(-1,List.of(new Step(SourceKind.CONSTANT,type,-1,List.of())));
        }
        if(action instanceof Allocate allocate)return new Operand(-1,List.of(new Step(SourceKind.ALLOCATION,descriptor(program,"L"+allocate.type()+";",loader),-1,List.of())));
        if(action instanceof NewArray array)return new Operand(-1,List.of(new Step(SourceKind.ALLOCATION,descriptor(program,array.descriptor(),loader),-1,List.of())));
        return unknown();
    }
    private static int index(Flow flow,Sources sources) {
        if(sources.origins().size()==1 && sources.origins().iterator().next() instanceof Producer producer
                && flow.producers().get(producer.instruction()) instanceof Constant constant && constant.value() instanceof LiteralConstant literal && literal.value() instanceof Integer index)return index;
        return -1;
    }
    private static Operand append(Operand base,Step step){List<Step> steps=new ArrayList<>(base.steps());steps.add(step);return new Operand(base.parameter(),steps);}
    private static Operand unknown(){return new Operand(-1,List.of(new Step(SourceKind.UNKNOWN,"",-1,List.of())));}
    private static Sources transparent(Flow flow,Sources sources,Set<Integer> seen,int depth) {
        if(depth>=8 || sources.origins().size()!=1 || !(sources.origins().iterator().next() instanceof Producer producer) || !seen.add(producer.instruction()))return sources;
        Action action=flow.producers().get(producer.instruction());
        return action instanceof Cast cast?transparent(flow,cast.input(),seen,depth+1):action instanceof Assign assign?transparent(flow,assign.input(),seen,depth+1):sources;
    }
    private static boolean contains(Flow flow,Sources sources,int instruction,Set<Integer> seen,int depth) {
        if(depth>=8)return false;
        for(Origin origin:sources.origins())if(origin instanceof Producer producer) {
            if(producer.instruction()==instruction)return true;if(!seen.add(producer.instruction()))continue;
            Action action=flow.producers().get(producer.instruction());
            if(action instanceof Cast cast && contains(flow,cast.input(),instruction,seen,depth+1) || action instanceof Assign assign && contains(flow,assign.input(),instruction,seen,depth+1))return true;
        }
        return false;
    }
    public static boolean matches(Pattern expected,Pattern current) {
        if(!expected.target().equals(current.target()) || expected.opcode()!=current.opcode() || expected.operands().size()!=current.operands().size())return false;
        for(int i=0;i<expected.operands().size();i++) {
            Operand operand=expected.operands().get(i),actual=current.operands().get(i);
            if(!operand.unknown() && !actual.unknown() && (operand.parameter()!=actual.parameter() || !operand.steps().equals(actual.steps())))return false;
        }
        return current.result().containsAll(expected.result()) && current.guards().containsAll(expected.guards());
    }
}
