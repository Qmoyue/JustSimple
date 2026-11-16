package io.just.analysis;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import java.util.*;
import java.util.concurrent.CancellationException;
import org.objectweb.asm.Opcodes;

/** Proves a small, side-effect-free void call from bytecode without executing the target. */
final class BoundedEvaluation {
    record Proof(int depth,int work,List<Site> witnesses,List<Call> calls) {
        Proof {witnesses=List.copyOf(witnesses);calls=List.copyOf(calls);}
    }
    record Outcome(Optional<Proof> proof,long work,boolean exhausted) {}
    private static final class Allowance {
        long remaining,used;boolean incomplete,exhausted;
        Allowance(long remaining){this.remaining=remaining;}
        boolean take(){if(remaining==0){incomplete=true;exhausted=true;return false;}remaining--;used++;return true;}
    }
    private final Program program;
    private final JvmSemantics jvm;
    private final Map<MethodId,Optional<Proof>> cache=new HashMap<>();
    private int definitions=-1;
    BoundedEvaluation(Program program){this.program=program;this.jvm=new JvmSemantics(program);}

    Outcome evaluate(MethodId target,long budget) {
        if(budget<0)throw new IllegalArgumentException("evaluation budget must not be negative");
        if(definitions!=program.definitionCount()){definitions=program.definitionCount();cache.clear();}
        Allowance allowance=new Allowance(budget);
        Optional<Proof> proof=inspect(target,new LinkedHashSet<>(),allowance);
        return new Outcome(proof,allowance.used,allowance.exhausted);
    }
    private Optional<Proof> inspect(MethodId target,Set<MethodId> active,Allowance allowance) {
        Optional<Proof> cached=cache.get(target);if(cached!=null)return cached;
        if(Thread.currentThread().isInterrupted())throw new CancellationException("static evaluation interrupted");
        if(allowance.remaining==0){allowance.incomplete=true;allowance.exhausted=true;return Optional.empty();}
        if(active.size()>=32 || !active.add(target)){allowance.incomplete=true;return Optional.empty();}
        Optional<Proof> result=derive(target,active,allowance);active.remove(target);
        if(!allowance.incomplete){if(cache.size()>=8192)cache.clear();cache.put(target,result);}return result;
    }
    private Optional<Proof> derive(MethodId target,Set<MethodId> active,Allowance allowance) {
        Query<Method> resolved=program.lookup(target);
        if(!resolved.pending().isEmpty() || resolved.value().isEmpty())return Optional.empty();
        Method method=resolved.value().orElseThrow();
        if(method.isStatic() || !method.isPublic() || !method.hasBody() || (method.access() & Opcodes.ACC_SYNCHRONIZED)!=0 || !method.id().descriptor().equals("()V")
                || program.type(method.id().owner(),method.id().loader()).filter(type -> type.role()!=io.just.input.Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        Facts facts=program.facts(method.id());
        if(!facts.limitations().isEmpty() || !facts.handlers().isEmpty())return Optional.empty();
        int[] opcodes=program.opcodes(method.id());if(opcodes.length>256)return Optional.empty();
        Map<Integer,Action> actions=new HashMap<>();for(Action action:facts.actions())actions.put(action.site().instruction(),action);
        Map<Integer,List<Edge>> edges=program.outgoing(method.id());Map<Integer,Atom> values=new HashMap<>();Set<Integer> visited=new HashSet<>();
        ObjectValue self=new ObjectValue(-1,method.id().owner(),false,"static receiver",false,Optional.empty(),method.id().loader());
        List<Site> witnesses=new ArrayList<>();List<Call> calls=new ArrayList<>();int at=0,depth=1,work=0;
        while(at>=0 && at<opcodes.length && visited.add(at)) {
            if(Thread.currentThread().isInterrupted())throw new CancellationException("static evaluation interrupted");
            Action action=actions.get(at);Optional<Integer> successor=Optional.empty();
            if(action==null) {if(!transport(opcodes[at]))return Optional.empty();}
            else {
                if(!allowance.take() || ++work>256)return Optional.empty();witnesses.add(action.site());
                if(action instanceof Constant constant && constant.value() instanceof LiteralConstant literal)values.put(at,new Literal(literal.value()));
                else if(action instanceof Assign assign) {
                    Optional<Atom> value=value(assign.input(),values,visited,self);if(value.isEmpty())return Optional.empty();values.put(at,value.get());
                } else if(action instanceof Compute compute) {
                    if(compute.opcode()==Opcodes.INSTANCEOF)return Optional.empty();
                    List<Atom> operands=new ArrayList<>();for(Sources source:compute.inputs()) {
                        Optional<Atom> value=value(source,values,visited,self);if(value.isEmpty())return Optional.empty();operands.add(value.get());
                    }
                    JvmSemantics.Check check=jvm.check(compute,operands,OptionalInt.empty());
                    if(!(check instanceof JvmSemantics.Normal normal) || !normal.gaps().isEmpty() || !normal.possible().isEmpty())return Optional.empty();
                    Atom value=jvm.compute(compute,operands);if(!(value instanceof Literal))return Optional.empty();values.put(at,value);
                } else if(action instanceof Branch branch) {
                    List<Value> operands=new ArrayList<>();for(Sources source:branch.inputs()) {
                        Optional<Atom> value=value(source,values,visited,self);if(value.isEmpty())return Optional.empty();operands.add(Value.of(value.get()));
                    }
                    successor=jvm.successor(branch,operands,facts.cfg());if(successor.isEmpty())return Optional.empty();
                } else if(action instanceof Call call) {
                    Optional<Atom> receiver=value(call.receiver(),values,visited,self);
                    if(receiver.isEmpty() || !receiver.get().equals(self))return Optional.empty();
                    Optional<Proof> nested=forward(method,call,active,allowance);if(nested.isEmpty() || work+nested.get().work()>256)return Optional.empty();
                    work+=nested.get().work();depth=Math.max(depth,nested.get().depth()+1);witnesses.addAll(nested.get().witnesses());calls.add(call);calls.addAll(nested.get().calls());
                } else if(action instanceof Returned returned && returned.value().origins().isEmpty())return Optional.of(new Proof(depth,work,witnesses,calls));
                else return Optional.empty();
            }
            List<Edge> outgoing=edges.getOrDefault(at,List.of()).stream().filter(edge -> !edge.exceptional()).toList();
            if(successor.isPresent()) {
                int selected=successor.orElseThrow();
                if(outgoing.stream().noneMatch(edge -> edge.to()==selected))return Optional.empty();
                at=selected;
            } else {if(outgoing.size()!=1)return Optional.empty();at=outgoing.get(0).to();}
        }
        return Optional.empty();
    }
    private Optional<Proof> forward(Method method,Call call,Set<MethodId> active,Allowance allowance) {
        if(call.opcode()!=Opcodes.INVOKESPECIAL || !call.arguments().isEmpty() || !call.target().descriptor().equals("()V"))return Optional.empty();
        Optional<ClassInfo> owner=program.type(method.id().owner(),method.id().loader());
        if(owner.isEmpty() || !Objects.equals(owner.get().parent(),call.target().owner()))return Optional.empty();
        Optional<ClassInfo> parentType=program.type(call.target().owner(),call.target().loader());
        if(parentType.isEmpty())return Optional.empty();
        String child=owner.get().name(),parentName=parentType.get().name();
        boolean samePackage=owner.get().loader()==parentType.get().loader() && child.substring(0,Math.max(0,child.lastIndexOf('/'))).equals(parentName.substring(0,Math.max(0,parentName.lastIndexOf('/'))));
        if((parentType.get().access() & Opcodes.ACC_PUBLIC)==0 && !samePackage)return Optional.empty();
        Query<Method> parent=program.lookup(call.target());
        if(!parent.pending().isEmpty() || parent.value().filter(Method::isPublic).isEmpty())return Optional.empty();
        Query<Boolean> subtype=program.assignable(method.id().owner(),method.id().loader(),parent.value().orElseThrow().id().owner(),parent.value().orElseThrow().id().loader());
        if(!subtype.value().equals(Optional.of(true)) || !subtype.pending().isEmpty())return Optional.empty();
        return inspect(parent.value().orElseThrow().id(),active,allowance);
    }
    private Optional<Atom> value(Sources sources,Map<Integer,Atom> values,Set<Integer> visited,Atom self) {
        Set<Atom> found=new LinkedHashSet<>();
        for(Origin origin:sources.origins()) {
            if(origin instanceof Parameter parameter && parameter.slot()==0)found.add(self);
            else if(origin instanceof Producer producer) {
                Atom value=values.get(producer.instruction());if(value!=null)found.add(value);else if(visited.contains(producer.instruction()))return Optional.empty();
            } else return Optional.empty();
        }
        return found.size()==1?Optional.of(found.iterator().next()):Optional.empty();
    }
    private static boolean transport(int opcode) {
        return opcode<0 || opcode==Opcodes.NOP || opcode>=Opcodes.ILOAD && opcode<=Opcodes.ALOAD
                || opcode>=Opcodes.ISTORE && opcode<=Opcodes.ASTORE || opcode>=Opcodes.POP && opcode<=Opcodes.SWAP || opcode==Opcodes.GOTO;
    }
}
