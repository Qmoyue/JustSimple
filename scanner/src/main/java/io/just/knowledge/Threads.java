package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Mechanisms.*;
import java.util.*;

/** Only the bound Thread/Runnable bridge. No thread or arbitrary native callback is executed. */
final class Threads implements Model {
    private static final Field TARGET=new Field(new FieldId("java/lang/Thread","target","Ljava/lang/Runnable;"));
    private static final Field STATUS=new Field(new FieldId("java/lang/Thread","threadStatus","I"));
    private Optional<List<Site>> witness=Optional.empty();
    private List<Site> witness(Program program) {
        if(witness.isPresent())return witness.get();List<Site> sites=new ArrayList<>();
        Facts run=program.facts(new MethodId("java/lang/Thread","run","()V"));
        for(Action action:run.actions())if(action instanceof Call call && call.target().equals(new MethodId("java/lang/Runnable","run","()V")))
            for(Origin origin:call.receiver().origins())if(origin instanceof Producer producer && program.flow(run.method().id()).producers().get(producer.instruction()) instanceof ReadField field && field.field().equals(TARGET.field()) && field.receiver().parameter(0))sites.add(call.site());
        Facts start=program.facts(new MethodId("java/lang/Thread","start","()V"));
        boolean nativeStart=start.actions().stream().anyMatch(a -> a instanceof Call c && c.target().equals(new MethodId("java/lang/Thread","start0","()V")) && c.receiver().parameter(0));
        if(!nativeStart || !run.limitations().isEmpty() || !start.limitations().isEmpty())sites.clear();
        witness=Optional.of(List.copyOf(sites));return witness.get();
    }
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        MethodId api=call.call().target();
        if(!api.owner().equals("java/lang/Thread") || !(call.receiver() instanceof ObjectValue thread)
                || program.type(api.owner()).filter(t -> t.role()==io.just.input.Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        if(api.name().equals("<init>") && Set.of("()V","(Ljava/lang/Runnable;)V","(Ljava/lang/Runnable;Ljava/lang/String;)V").contains(api.descriptor())) {
            if(call.arguments().size()==2 && call.arguments().get(1).equals(new Literal(null)))return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            Atom target=call.arguments().isEmpty()?new Literal(null):call.arguments().get(0);
            return Optional.of(Local.of(new RequireNormal(List.of()),new Write(thread,TARGET,Value.of(target)),new Write(thread,STATUS,Value.of(new Literal(0))),new Result(Value.NULL)));
        }
        if(call.is("java/lang/Thread","start","()V")) {
            Value status=bindings.read(thread,STATUS).under(call.path());
            if(!status.empty() && status.alternatives().stream().allMatch(b -> b.atom() instanceof Literal l && l.value() instanceof Number n && n.intValue()!=0))return Optional.of(Local.of(new Raise("java/lang/IllegalThreadStateException")));
            List<Gap> gaps=new ArrayList<>();gaps.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"VM scheduling of this Thread is assumed; asynchronous order and concurrent mutations are unresolved"));
            List<Site> sites=witness(program);if(sites.isEmpty())gaps.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"selected JDK Thread.start/run bridge is not verified"));
            List<Gap> normal=status.empty() && !thread.defaultFields() || status.alternatives().stream().anyMatch(b -> !(b.atom().equals(new Literal(0))))
                    ?List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"Thread must not have been started previously")):List.of();
            Query<Method> run=program.lookup(program.method(thread.type(),"run","()V",thread.loader()));gaps.addAll(Mechanisms.queryGaps(call,run));
            MethodId target=run.value().map(Method::id).orElse(program.method(thread.type(),"run","()V",thread.loader()));
            return Optional.of(Local.of(new RequireNormal(normal),new Write(thread,STATUS,Value.of(new Literal(1))),new Result(Value.NULL),
                    new Deferred(new Dispatch(target,thread,List.of(),Kind.DYNAMIC_CALL,Evidence.CONDITIONAL,sites,List.copyOf(gaps),ReturnFlow.IGNORE,ExceptionFlow.DIRECT),new Observe(Kind.DYNAMIC_CALL,"Thread.start bound to this Thread.run",sites,List.copyOf(gaps)),Timing.ASYNCHRONOUS)));
        }
        if(call.is("java/lang/Thread","run","()V")) {
            List<Effect> effects=new ArrayList<>();
            for(Bound bound:bindings.read(thread,TARGET).under(call.path()).alternatives()) {
                if(bound.atom().equals(new Literal(null))){effects.add(new Result(Value.NULL.under(bound.path())));continue;}
                Atom runnable=bound.atom();Query<Method> selected=runnable instanceof ObjectValue object?program.lookup(program.method(object.type(),"run","()V",object.loader())):new Query<>(Optional.empty(),List.of());
                MethodId target=selected.value().map(Method::id).orElse(new MethodId("java/lang/Runnable","run","()V"));
                effects.add(new Conditional(bound.path(),bound.gaps(),bound.dependencies(),Local.of(new Dispatch(target,runnable,List.of(),Kind.DYNAMIC_CALL,Evidence.CONDITIONAL,witness(program),Mechanisms.queryGaps(call,selected),ReturnFlow.IGNORE,ExceptionFlow.DIRECT),new Result(Value.NULL))));
            }
            if(effects.isEmpty())effects.add(new Result(Value.NULL.requiring(Mechanisms.unknown(call,"same Thread target Runnable binding is unavailable"))));
            return Optional.of(new Local(effects));
        }
        return Optional.empty();
    }
}
