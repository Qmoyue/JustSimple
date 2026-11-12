package io.just.knowledge;

import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Mechanisms.*;
import java.util.*;

/** Conditional class-definition frontier, verified against the selected platform's method bodies. */
final class ClassDefinitions implements Model {
    private static final String TEMPLATE="com/sun/org/apache/xalan/internal/xsltc/trax/TemplatesImpl";
    private static final List<MethodId> ENTRIES=List.of(new MethodId(TEMPLATE,"newTransformer","()Ljavax/xml/transform/Transformer;"),new MethodId(TEMPLATE,"getOutputProperties","()Ljava/util/Properties;"));
    private record Route(MethodId method,List<Site> sites,List<FieldId> fields) {}
    private record Boundary(MethodId api,List<Site> sites,List<FieldId> fields) {}
    private final Map<MethodId,Query<Boundary>> paths=new HashMap<>(); // At most the two API entries.
    static List<MethodId> entries(){return ENTRIES;}

    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        if(!ENTRIES.contains(call.call().target()) || !(call.receiver() instanceof ObjectValue receiver)
                || program.type(TEMPLATE).filter(c -> c.role()==Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        Query<Boundary> query=paths.computeIfAbsent(call.call().target(),root -> path(root,program));
        List<Gap> gaps=new ArrayList<>(Mechanisms.queryGaps(call,query));
        if(query.value().isEmpty()) {
            gaps.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"no class-definition path verified in the selected platform"));
            return Optional.of(Local.of(new Result(Value.of(new Unknown("platform definition path unavailable")).requiring(gaps))));
        }
        Boundary boundary=query.value().get();
        gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"class bytes and required template state are not verified"));
        gaps.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"internal loader/argument bindings and normal path to definition remain conditional"));
        gaps.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"platform template construction and class-loading access policies are not verified"));
        List<Effect> effects=new ArrayList<>();
        for(FieldId field:boundary.fields()) {
            boolean nativeSource=receiver.source().stream().flatMap(s -> s.path().stream()).anyMatch(Decoded.class::isInstance) && bindings.read(receiver,new Field(field)).empty();
            effects.add(new Need(new InputNeed(receiver,Optional.of(nativeSource?new SerializedField(field):new Field(field)),NeedKind.VALUE,field.descriptor(),List.of(),"class-byte array read on the current platform definition path")));
        }
        boolean known=false,stored=false;List<Effect> construction=new ArrayList<>();
        Atom loader=new LoaderValue(TEMPLATE,receiver.id());
        for(FieldId field:boundary.fields()) {
            Value arrays=bindings.read(receiver,new Field(field));
            if(arrays.empty())arrays=bindings.read(receiver,new SerializedField(field));
            for(Bound outer:arrays.under(call.path()).alternatives()) {
                ValueBindings.ArrayBindings candidates=ValueBindings.array(outer.atom(),bindings,outer.path(),call.call().site());
                if(!candidates.frontier().isEmpty())effects.add(new Observe(Kind.DYNAMIC_CALL,"template class-byte array frontier",List.of(call.call().site()),candidates.frontier()));
                for(ValueBindings.ArrayBinding bytes:candidates.values()) {
                for(int index=0;index<bytes.elements().size();index++) {
                    Atom data=bytes.elements().get(index);Value sizes=data instanceof Bytecode raw?Value.of(new Literal(raw.bytes().length)):data instanceof ObjectValue array?bindings.read(array,new Length()):Value.BOTTOM;
                    Value existing=bindings.read(receiver,new DefinedClass(index)).under(bytes.path());
                    if(!existing.empty())known=true;
                    for(Bound size:existing.empty()?sizes.under(bytes.path()).alternatives():Set.<Bound>of()) {
                        known=true;List<Atom> args=new ArrayList<>();int integer=0;
                        for(ValueType operand:program.signature(boundary.api()).parameters())args.add(operand.descriptor().equals("[B")?data:operand.descriptor().equals("Ljava/lang/String;")?new Literal(null):operand.descriptor().equals("I")?integer++==0?new Literal(0):size.atom():new Unknown("template loader operand "+operand.descriptor()));
                        List<Gap> required=new ArrayList<>(outer.gaps());required.addAll(bytes.gaps());required.addAll(size.gaps());
                        Local define=Local.of(new Dispatch(boundary.api(),loader,args,Kind.DYNAMIC_CALL,Evidence.CONDITIONAL,boundary.sites(),required,ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT));
                        effects.add(new Store(receiver,new DefinedClass(index),define));stored=true;
                    }
                    for(Bound defined:existing.alternatives())if(defined.atom() instanceof ClassValue type) {
                        Optional<String> parent=program.fieldConstant(new FieldId(TEMPLATE,"ABSTRACT_TRANSLET","Ljava/lang/String;")).filter(value -> value instanceof LiteralConstant literal && literal.value() instanceof String).map(value -> ((String)((LiteralConstant)value).value()).replace('.','/'));
                        if(parent.isPresent() && program.type(Values.type(type.descriptor()),type.loader()).filter(info -> parent.get().equals(info.parent())).isEmpty())continue;
                        Query<Method> constructor=program.constructor(Values.type(type.descriptor()),List.of(),false,type.loader());
                        constructor.value().ifPresent(target -> construction.add(new Conditional(defined.path(),defined.gaps(),defined.dependencies(),Local.of(new Construct(target.id(),List.of(),Kind.DYNAMIC_CALL,boundary.sites(),
                                List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"template main-class selection and required translet state")),ExceptionFlow.DIRECT)))));
                    }
                }
                }
            }
        }
        if(stored){effects.add(new Evaluate(call));return Optional.of(new Local(effects));}
        effects.addAll(construction);
        if(!known) {
            List<Atom> args=program.signature(boundary.api()).parameters().stream().map(t -> (Atom)new Unknown("definition operand "+t.descriptor()+" at "+boundary.sites().get(boundary.sites().size()-1))).toList();
            effects.add(new Dispatch(boundary.api(),loader,args,Kind.DYNAMIC_CALL,Evidence.CONDITIONAL,boundary.sites(),List.copyOf(gaps),ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
        }
        effects.add(new Result(Value.of(new Unknown("template transformer result")).requiring(gaps)));
        return Optional.of(new Local(effects));
    }

    private static Query<Boundary> path(MethodId root,Program program) {
        ArrayDeque<Route> queue=new ArrayDeque<>(List.of(new Route(root,List.of(),List.of())));Set<MethodId> seen=new HashSet<>();List<QueryIssue> issues=new ArrayList<>();
        while(!queue.isEmpty() && seen.size()<16) {
            Route route=queue.removeFirst();if(!seen.add(route.method()))continue;
            Query<Method> declaration=program.declaration(route.method());issues.addAll(declaration.pending());
            if(declaration.value().filter(Method::hasBody).isEmpty())continue;
            Facts facts=program.facts(route.method());
            for(Limitation limit:facts.limitations())if(limit.cause()==CoverageCause.BUDGET)issues.add(new QueryIssue(QueryCause.BUDGET,limit.detail()));
            List<FieldId> fields=new ArrayList<>(route.fields());
            for(Action action:facts.actions())if(action instanceof ReadField field && field.field().owner().equals(TEMPLATE) && field.field().descriptor().equals("[[B"))fields.add(field.field());
            for(Action action:facts.actions())if(action instanceof Call call && (call.target().owner().equals(TEMPLATE) || call.target().owner().startsWith(TEMPLATE+"$") || Mechanisms.impact(call.target()))) {
                Query<Method> selected=program.lookup(call.target());issues.addAll(selected.pending());if(selected.value().isEmpty())continue;
                MethodId target=selected.value().get().id();List<Site> sites=new ArrayList<>(route.sites());sites.add(call.site());
                if(Mechanisms.impact(target))return new Query<>(Optional.of(new Boundary(target,List.copyOf(sites),fields.stream().distinct().toList())),List.copyOf(issues));
                if(target.owner().equals(TEMPLATE) || target.owner().startsWith(TEMPLATE+"$"))queue.addLast(new Route(target,List.copyOf(sites),List.copyOf(fields)));
            }
        }
        if(!queue.isEmpty())issues.add(new QueryIssue(QueryCause.BUDGET,"platform definition path frontier (16)"));
        return new Query<>(Optional.empty(),List.copyOf(issues));
    }
}
