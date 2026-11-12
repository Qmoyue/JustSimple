package io.just.knowledge;

import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import java.util.*;

/** One-argument platform action callbacks; no analysis privileges are granted. */
final class PrivilegedActions implements Model {
    private static final String ACTION="Ljava/security/PrivilegedAction;";
    private static final String CHECKED="Ljava/security/PrivilegedExceptionAction;";
    private static final String RUN="()Ljava/lang/Object;";

    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        boolean checked=call.is("java/security/AccessController","doPrivileged","("+CHECKED+")Ljava/lang/Object;");
        if(!checked && !call.is("java/security/AccessController","doPrivileged","("+ACTION+")Ljava/lang/Object;"))return Optional.empty();
        String contract=checked?CHECKED:ACTION;
        Optional<Method> api=program.declared(call.call().target());
        if(api.isEmpty() || !api.get().isStatic() || program.type(api.get().id().owner()).orElseThrow().role()!=Inputs.Role.PLATFORM)return Optional.empty();
        Atom action=call.arguments().get(0);
        if(action instanceof Literal literal && literal.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
        ValueBindings.Compatibility match=ValueBindings.compatible(action,contract,program);
        if(match.match()==ValueBindings.Match.INCOMPATIBLE)return Optional.empty();
        List<Gap> gaps=new ArrayList<>(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),match.pending())));
        MethodId target=new MethodId(Values.type(contract),"run",RUN);
        if(action instanceof ObjectValue object) {
            Query<Method> implementation=program.lookup(new MethodId(object.type(),"run",RUN));
            gaps.addAll(Mechanisms.queryGaps(call,implementation));
            target=implementation.value().map(Method::id).orElse(new MethodId(object.type(),"run",RUN));
            if(implementation.absent())gaps.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"privileged action has no run implementation"));
        }
        List<Effect> effects=new ArrayList<>();
        boolean concrete=action instanceof ObjectValue object && object.exact() || action instanceof LambdaValue || action instanceof ProxyValue;
        if(!concrete) {
            String reason="privileged callback requires the actual action receiver";
            gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,reason));
            effects.add(new Need(new InputNeed(action,Optional.empty(),NeedKind.RECEIVER_TYPE,contract,List.of(),reason)));
        }
        List<Site> witnesses=List.of(call.call().site());
        effects.add(new Dispatch(target,action,List.of(),Kind.DYNAMIC_CALL,gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,witnesses,List.copyOf(gaps),ReturnFlow.TO_RESULT,checked?ExceptionFlow.PRIVILEGED:ExceptionFlow.DIRECT));
        effects.add(new Observe(Kind.DYNAMIC_CALL,"platform privileged action callback",witnesses,List.copyOf(gaps)));
        return Optional.of(new Local(effects));
    }
}
