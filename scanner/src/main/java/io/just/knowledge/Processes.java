package io.just.knowledge;

import io.just.program.Program;
import io.just.knowledge.Values.*;
import io.just.knowledge.Mechanisms.*;
import java.util.*;

/** Finite invalid-command checks share the normal-flow semantics; no process is launched. */
final class Processes implements Model {
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        if(!call.call().target().owner().equals("java/lang/Runtime") || !call.call().target().name().equals("exec")
                || !Mechanisms.impact(call.call().target()) || program.type("java/lang/Runtime").filter(t -> t.role()==io.just.input.Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        Atom command=call.arguments().get(0);
        if(command.equals(new Literal(null)))return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
        if(command instanceof Literal literal && literal.value() instanceof String text && text.isEmpty())return Optional.of(Local.of(new Raise("java/lang/IllegalArgumentException")));
        if(program.signature(call.call().target()).parameters().get(0).descriptor().equals("[Ljava/lang/String;")) {
            ValueBindings.ArrayBindings arrays=ValueBindings.array(command,bindings,call.path(),call.call().site());List<Effect> effects=new ArrayList<>();
            for(ValueBindings.ArrayBinding array:arrays.values()) {
                Local result=array.elements().isEmpty()?Local.of(new Raise("java/lang/IndexOutOfBoundsException"))
                        :array.elements().stream().anyMatch(a -> a.equals(new Literal(null)))?Local.of(new Raise("java/lang/NullPointerException")):pending(call);
                effects.add(new Conditional(array.path(),array.gaps(),array.dependencies(),result));
            }
            if(!effects.isEmpty())return Optional.of(arrays.keeping(new Local(effects)));
        }
        return Optional.of(pending(call));
    }
    private static Local pending(Invocation call) {
        return Local.of(new RequireNormal(List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"process creation requires a valid command, permitted environment and available program"))),Mechanisms.result(call.result()));
    }
}
