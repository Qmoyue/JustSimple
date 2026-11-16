package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import org.objectweb.asm.Opcodes;
import java.util.*;

/** Explicit model assembly; models emit local effects and never findings or solver mutations. */
public final class Mechanisms {
    public interface Bindings {
        Value read(ObjectValue object, Slot slot);
        default int alternatives(){return 64;}
        default Optional<ObjectValue> materialize(Symbolic value){return Optional.empty();}
    }
    private record LimitedBindings(Bindings source,int alternatives) implements Bindings {
        @Override public Value read(ObjectValue object,Slot slot){return source.read(object,slot);}
        @Override public Optional<ObjectValue> materialize(Symbolic value){return source.materialize(value);}
    }
    public enum Evaluation { CALL, COMPARED_KEYS }
    public record Invocation(Call call, Atom receiver, List<Atom> arguments, ObjectValue result, Path path,Evaluation evaluation) {
        public Invocation(Call call,Atom receiver,List<Atom> arguments,ObjectValue result,Path path){this(call,receiver,arguments,result,path,Evaluation.CALL);}
        public Invocation comparedKeys(){return new Invocation(call,receiver,arguments,result,path,Evaluation.COMPARED_KEYS);}
        public boolean is(String owner, String name, String descriptor) {
            MethodId id = call.target();
            return id.owner().equals(owner) && id.name().equals(name) && id.descriptor().equals(descriptor);
        }
    }
    public sealed interface Effect permits Result, Write, Dispatch, Construct, Initialize, DefineClass, Concat, Observe, Conditional, Store, IgnoreResult, Evaluate, Raise, Deferred, RequireNormal, Iterate, Need, Alternative {}
    public record Concat(Value prefix,Local suffix) implements Effect {}
    public static Atom concatenate(List<Atom> pieces){return Strings.concat(pieces);}
    public static Optional<InputNeed> stringInput(InputNeed need){return Strings.input(need);}
    /** Parsing/definition is committed by the analysis owner, never by a completion query. */
    public record DefineClass(Atom loader,Bytecode content,int offset,int length,String requested) implements Effect {}
    public record Initialize(String owner,int loader) implements Effect {public Initialize(String owner){this(owner,0);}}
    /** Allocate once at this effect position, initialize its class, then await its constructor. */
    public record Construct(MethodId constructor,List<Atom> arguments,Kind kind,List<Site> witnesses,List<Gap> gaps,ExceptionFlow exceptions) implements Effect {
        public Construct {arguments=List.copyOf(arguments);witnesses=List.copyOf(witnesses);gaps=List.copyOf(gaps);}
    }
    /** Request existing local semantics at this sequence position; no target call edge is invented. */
    public record Evaluate(Invocation invocation) implements Effect {}
    /** Wait for normal completion of a nested local sequence without forwarding its value. */
    public record IgnoreResult(Local local) implements Effect {}
    /** Mutually exclusive, still conditional target selections at the same dynamic boundary. */
    public record Alternative(int selection,int batch,Local local) implements Effect {
        public Alternative(int selection,Local local){this(selection,selection,local);}
    }
    public record Need(InputNeed input) implements Effect {}
    public record Iterate(ObjectValue iterator) implements Effect {}
    /** Preconditions of normal completion, distinct from uncertainty in the returned data. */
    public record RequireNormal(List<Gap> gaps,Optional<Invocation> operation) implements Effect {
        public RequireNormal(List<Gap> gaps){this(gaps,Optional.empty());}
        public RequireNormal {gaps=List.copyOf(gaps);}
    }
    public enum Timing { AFTER_INITIALIZATION, ASYNCHRONOUS }
    public record Deferred(Dispatch dispatch,Observe observation,Timing timing) implements Effect {
        public Deferred(Dispatch dispatch,Observe observation){this(dispatch,observation,Timing.AFTER_INITIALIZATION);}
    }
    public record Raise(String type) implements Effect {}
    /** A model's heap reads can add conditions and evidence to this particular effect. */
    public record Conditional(Path path, List<Gap> gaps, Set<Integer> dependencies, Local local) implements Effect {}
    public record Store(ObjectValue receiver,Slot slot,Local local,Optional<String> descriptor) implements Effect {
        public Store(ObjectValue receiver,Slot slot,Local local){this(receiver,slot,local,Optional.empty());}
    }
    public record Result(Value value) implements Effect {}
    public record Write(ObjectValue receiver, Slot slot, Value value) implements Effect {}
    public enum ReturnFlow { IGNORE, TO_RESULT }
    public record ExceptionRule(String wrapper,Optional<String> caught,List<String> bypass,List<FieldId> causes) {
        public ExceptionRule { bypass=List.copyOf(bypass);causes=List.copyOf(causes); }
    }
    public enum ExceptionFlow {
        DIRECT(Optional.empty()),
        REFLECTED(Optional.of(new ExceptionRule("java/lang/reflect/InvocationTargetException",Optional.empty(),List.of(),List.of(
                new FieldId("java/lang/Throwable","cause","Ljava/lang/Throwable;"),new FieldId("java/lang/reflect/InvocationTargetException","target","Ljava/lang/Throwable;"))))),
        PRIVILEGED(Optional.of(new ExceptionRule("java/security/PrivilegedActionException",Optional.of("java/lang/Exception"),List.of("java/lang/RuntimeException"),List.of(
                new FieldId("java/lang/Throwable","cause","Ljava/lang/Throwable;"),new FieldId("java/security/PrivilegedActionException","exception","Ljava/lang/Exception;")))));
        private final Optional<ExceptionRule> rule;
        ExceptionFlow(Optional<ExceptionRule> rule){this.rule=rule;}
        public Optional<ExceptionRule> rule(){return rule;}
    }
    public record Dispatch(MethodId target, Atom receiver, List<Atom> arguments, Kind kind,
                           Evidence evidence, List<Site> witnesses, List<Gap> gaps, ReturnFlow returns,ExceptionFlow exceptions) implements Effect {}
    public record Observe(Kind kind, String detail, List<Site> witnesses, List<Gap> gaps) implements Effect {}
    public enum ReceiverSemantics { JVM_IMPLEMENTATION, MODELED_STATE }
    public record Local(List<Effect> effects,ReceiverSemantics receiverSemantics) {
        public Local(List<Effect> effects){this(effects,ReceiverSemantics.JVM_IMPLEMENTATION);}
        public Local { effects = List.copyOf(effects); }
        public static Local of(Effect... effects) { return new Local(List.of(effects)); }
        public Local onModelState(){return new Local(effects,ReceiverSemantics.MODELED_STATE);}
    }
    interface Model { Optional<Local> apply(Invocation invocation, Bindings bindings, Program program); }
    private final List<Model> models;
    private final Program program;
    private final Catalog catalog;
    private final Guidance guidance;
    private final Dynamic dynamic;
    private final Set<MethodId> sinks;
    private final int alternatives;

    public Mechanisms(Program program) {
        this(program,Catalog.empty());
    }
    public Mechanisms(Program program,Catalog catalog) {this(program,catalog,Set.of());}
    public Mechanisms(Program program,Catalog catalog,Set<MethodId> sinks) {this(program,catalog,sinks,64);}
    public Mechanisms(Program program,Catalog catalog,Set<MethodId> sinks,int alternatives) {
        if(alternatives<1)throw new IllegalArgumentException("alternative budget must be positive");
        this.alternatives=alternatives;
        this.sinks=Set.copyOf(sinks);
        this.program=program;
        this.catalog=catalog;
        this.guidance=new Guidance(program,catalog,alternatives);
        this.dynamic=new Dynamic();
        JdkStructures structure = new JdkStructures(program);
        Containers containers=new Containers(structure);
        models = List.of(new ClassLoading(), new Reflection(new DynamicTargets(program,sinks,guidance)), new ArrayOperations(), new Constructors(guidance), dynamic, new Handles(), new Strings(), new HttpBridge(), new Threads(), new Processes(), new PrivilegedActions(), new NamingReferences(), new NamingFactories(structure), new ClassDefinitions(), new Serialization(structure,guidance,alternatives), containers, new Library(alternatives));
    }

    public void requireProgram(Program expected) {
        if (program != expected) throw new IllegalArgumentException("mechanisms and analysis must share one Program");
    }

    public boolean isImpact(MethodId id){return impact(id) || sinks.contains(id);}
    public Optional<Local> apply(Invocation invocation, Bindings bindings) {
        if(bindings.alternatives()!=alternatives)bindings=new LimitedBindings(bindings,alternatives);
        Call call=invocation.call();
        boolean unresolvedVirtual=false;
        if(call.bootstrap().isEmpty()) {
            MethodId requested=call.opcode()!=Opcodes.INVOKESTATIC && call.opcode()!=Opcodes.INVOKESPECIAL && invocation.receiver() instanceof ObjectValue object
                    ?program.method(object.type(),call.target().name(),call.target().descriptor(),object.loader()):call.target();
            Optional<Method> actual=program.lookup(requested).value();
            unresolvedVirtual=call.opcode()!=Opcodes.INVOKESTATIC && call.opcode()!=Opcodes.INVOKESPECIAL
                    && invocation.receiver() instanceof ObjectValue object && !object.exact()
                    && actual.filter(method -> (method.access() & Opcodes.ACC_FINAL)!=0).isEmpty()
                    && program.type(object.type(),object.loader()).filter(type -> (type.access() & Opcodes.ACC_FINAL)!=0).isEmpty();
            if(actual.isPresent())invocation=new Invocation(new Call(call.site(),actual.get().id(),call.opcode(),call.receiver(),call.arguments(),call.bootstrap()),invocation.receiver(),invocation.arguments(),invocation.result(),invocation.path(),invocation.evaluation());
        }
        for (Model model : models) {
            if(invocation.call().target().loader()!=0 && !(model instanceof Dynamic))continue;
            Optional<Local> local = model.apply(invocation, bindings, program);
            if (local.isPresent())return unresolvedVirtual && local.get().receiverSemantics()==ReceiverSemantics.JVM_IMPLEMENTATION?Optional.empty():local;
        }
        if(invocation.call().bootstrap().isPresent()) {
            Gap pending=gap(invocation,GapKind.UNSUPPORTED,"unsupported invokedynamic bootstrap: "+invocation.call().bootstrap().get().factory().target());
            return Optional.of(Local.of(new RequireNormal(List.of(pending)),
                    new Observe(Kind.DYNAMIC_CALL,pending.detail(),List.of(invocation.call().site()),List.of(pending)),
                    new Result(Value.of(new Unknown(pending.detail())).requiring(List.of(pending)))));
        }
        return Optional.empty();
    }
    /** Recheck the model's explicit completion contract after candidate choices become available. */
    public Optional<Boolean> normalCompletion(Invocation invocation,Bindings bindings) {
        return apply(invocation,bindings).flatMap(local -> normalCompletion(local,invocation.path()));
    }
    public static Optional<Boolean> normalCompletion(Local local,Path path) {
        boolean checked=false,pending=false,frontier=false,covered=true;List<Optional<Boolean>> branches=new ArrayList<>();
        for(Effect effect:local.effects()) {
            if(effect instanceof Initialize || effect instanceof DefineClass || effect instanceof Dispatch || effect instanceof Construct || effect instanceof Evaluate || effect instanceof Store || effect instanceof IgnoreResult || effect instanceof Alternative || effect instanceof Concat)return Optional.empty();
            if(effect instanceof Raise)return Optional.of(false);
            if(effect instanceof RequireNormal condition){checked=true;pending|=!condition.gaps().isEmpty();}
            if(effect instanceof Observe observation)frontier|=observation.gaps().stream().anyMatch(g -> g.kind()==GapKind.BUDGET || g.kind()==GapKind.UNSUPPORTED);
            if(effect instanceof Conditional conditional) {
                Optional<Path> selected=path.and(conditional.path());
                if(selected.isPresent()) {
                    covered&=selected.get().equals(path);
                    Optional<Boolean> branch=normalCompletion(conditional.local(),selected.get());
                    branches.add(!conditional.gaps().isEmpty() && branch.equals(Optional.of(true))?Optional.empty():branch);
                }
            }
        }
        if(!branches.isEmpty()) {
            if(covered && !frontier && branches.stream().allMatch(result -> result.equals(Optional.of(false))))return Optional.of(false);
            checked=true;pending|=!covered || branches.stream().anyMatch(result -> !result.equals(Optional.of(true)));
        }
        return checked && !pending && !frontier?Optional.of(true):Optional.empty();
    }
    public Optional<Atom> staticField(FieldId field) { return Library.staticField(field); }
    public Optional<Local> serializedProxy(Invocation invocation,int alternatives) {return dynamic.serializedProxy(invocation,program,guidance,alternatives);}
    public record MissingField(Atom value,List<InputNeed> needs) {public MissingField {needs=List.copyOf(needs);}}
    public MissingField missingField(ObjectValue receiver,FieldId field,Atom fallback){return Serialization.missingField(receiver,field,fallback,program);}

    /** Guidance has a different type and cannot manufacture Dispatch or evidence. */
    public record Reference(String entry,String location) {}
    public record Hint(MethodId anchor, String mechanism, String source, List<String> pendingRelations,List<CallShape.Requirement> requirements,List<Reference> references) {
        public Hint {pendingRelations=List.copyOf(pendingRelations);requirements=List.copyOf(requirements);references=List.copyOf(references);}
        public Hint(MethodId anchor,String mechanism,String source,List<String> pendingRelations,List<CallShape.Requirement> requirements){this(anchor,mechanism,source,pendingRelations,requirements,List.of());}
    }
    public Query<List<Hint>> hints(boolean enabled,Set<MethodId> entries) {
        guidance.enabled(enabled);
        if(!enabled || entries.isEmpty())return new Query<>(Optional.of(List.of()),List.of());
        Query<Set<MethodId>> scope=program.discover(entries,1024);
        Query<List<Hint>> structure=Structures.hints(program,scope.value().orElseThrow()),reference=catalog.hints(program,scope.value().orElseThrow());
        List<Hint> hints=new ArrayList<>(structure.value().orElseThrow());hints.addAll(reference.value().orElseThrow());
        List<QueryIssue> pending=new ArrayList<>(scope.pending());pending.addAll(structure.pending());pending.addAll(reference.pending());
        return new Query<>(Optional.of(List.copyOf(hints)),List.copyOf(new LinkedHashSet<>(pending)));
    }
    /** Reached dynamic methods need local shapes even when literal caller discovery could not see them. */
    public Query<List<Hint>> hints(MethodId reached) {
        return guidance.local(reached);
    }
    public Query<List<DefinedType>> preferredReceivers(MethodId requested,String upper,int loader){return guidance.receivers(requested,upper,loader);}
    public boolean preferredMember(MethodId member){return guidance.member(member);}
    public List<QueryIssue> rankingIssues(){return guidance.issues();}

    static Gap gap(Invocation call, GapKind kind, String detail) { return new Gap(kind, call.call().site(), detail); }
    static List<Gap> queryGaps(Invocation call,Program.Query<?> query) {
        return query.pending().stream().map(issue -> gap(call,issue.cause()==Program.QueryCause.BUDGET?GapKind.BUDGET:GapKind.MISSING_DEPENDENCY,issue.detail())).toList();
    }
    static Result result(Atom atom) { return new Result(Value.of(atom)); }
    static List<Gap> unknown(Invocation call, String detail) { return List.of(gap(call, GapKind.INPUT_BINDING, detail)); }

    private static final Set<MethodId> IMPACTS;
    static {
        Set<MethodId> methods = new LinkedHashSet<>();
        for (String descriptor : List.of("(Ljava/lang/String;)Ljava/lang/Process;", "([Ljava/lang/String;)Ljava/lang/Process;",
                "(Ljava/lang/String;[Ljava/lang/String;)Ljava/lang/Process;", "([Ljava/lang/String;[Ljava/lang/String;)Ljava/lang/Process;",
                "(Ljava/lang/String;[Ljava/lang/String;Ljava/io/File;)Ljava/lang/Process;", "([Ljava/lang/String;[Ljava/lang/String;Ljava/io/File;)Ljava/lang/Process;"))
            methods.add(new MethodId("java/lang/Runtime", "exec", descriptor));
        methods.add(new MethodId("java/lang/ProcessBuilder", "start", "()Ljava/lang/Process;"));
        for (String descriptor : List.of("([BII)Ljava/lang/Class;", "(Ljava/lang/String;[BII)Ljava/lang/Class;",
                "(Ljava/lang/String;[BIILjava/security/ProtectionDomain;)Ljava/lang/Class;", "(Ljava/lang/String;Ljava/nio/ByteBuffer;Ljava/security/ProtectionDomain;)Ljava/lang/Class;"))
            methods.add(new MethodId("java/lang/ClassLoader", "defineClass", descriptor));
        IMPACTS = Set.copyOf(methods);
    }
    public static boolean impact(MethodId id) { return IMPACTS.contains(id); }
    static Set<MethodId> impactTargets(){return IMPACTS;}
    /** Demand discovery is a mechanism policy, not JVM interpretation. */
    public static boolean demands(Call call) {
        MethodId api=call.target();
        return impact(api) || api.equals(Reflection.INVOKE) || Serialization.read(api)
                || api.owner().equals("java/lang/Class") && Set.of("forName","getMethod","getDeclaredMethod","getConstructor","getDeclaredConstructor","newInstance").contains(api.name())
                || api.owner().equals("java/lang/reflect/Constructor") && api.name().equals("newInstance")
                || api.owner().equals("java/lang/invoke/MethodHandle") && api.name().equals("invokeExact");
    }
}
