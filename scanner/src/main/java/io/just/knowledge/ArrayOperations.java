package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import java.util.*;

/** Positional reflection on reference arrays; other array forms keep their ordinary fallback. */
final class ArrayOperations implements Model {
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        boolean get=call.is("java/lang/reflect/Array","get","(Ljava/lang/Object;I)Ljava/lang/Object;");
        boolean set=call.is("java/lang/reflect/Array","set","(Ljava/lang/Object;ILjava/lang/Object;)V");
        if(!(get || set) || program.type(call.call().target().owner(),call.call().target().loader())
                .filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        Atom input=call.arguments().get(0),offset=call.arguments().get(1);
        if(input instanceof Literal literal && literal.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
        if(input instanceof Literal literal && literal.value() instanceof String
                || input instanceof ObjectValue object && object.exact() && !object.type().startsWith("["))
            return Optional.of(Local.of(new Raise("java/lang/IllegalArgumentException")));
        if(!(input instanceof ObjectValue array) || !(offset instanceof Literal index) || !(index.value() instanceof Integer position))return Optional.empty();
        boolean knownArray=array.type().startsWith("[");
        boolean references=knownArray && (array.type().charAt(1)=='L' || array.type().charAt(1)=='[');
        if(knownArray && !references)return Optional.empty();
        if(set && !references && !definiteReference(call.arguments().get(2)))return Optional.empty();
        if(array.exact() && knownArray && position<0)return Optional.of(Local.of(new Raise("java/lang/ArrayIndexOutOfBoundsException")));
        if(position<0)return Optional.empty();
        Value lengths=bindings.read(array,new Length()).under(call.path());
        OptionalInt length=knownLength(lengths,call.path());
        if(array.exact() && knownArray && length.isPresent() && position>=length.getAsInt())
            return Optional.of(Local.of(new Raise("java/lang/ArrayIndexOutOfBoundsException")));
        List<Gap> normal=new ArrayList<>();
        if(!array.exact() || !knownArray)normal.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,
                get?"reflection requires a nonnull array":"reflection requires a nonnull reference array"));
        if(length.isEmpty() || position>=length.getAsInt())normal.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"reflection array index must be in bounds"));
        Slot slot=new Index(position);
        if(set) {
            Atom value=call.arguments().get(2);
            if(references) {
                ValueBindings.Compatibility match=ValueBindings.compatible(value,array.type().substring(1),program,array.loader());
                if(array.exact() && match.match()==ValueBindings.Match.INCOMPATIBLE && match.pending().isEmpty())
                    return Optional.of(Local.of(new Raise("java/lang/IllegalArgumentException")));
                if(!array.exact() || match.match()!=ValueBindings.Match.COMPATIBLE || !match.pending().isEmpty())
                    normal.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"reflection array component must accept the value"));
            } else normal.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"reflection array component must accept the value"));
            return Optional.of(Local.of(new RequireNormal(normal),new Write(array,slot,Value.of(value)),new Result(Value.NULL)));
        }
        Value value=bindings.read(array,slot).under(call.path());
        if(!references && value.alternatives().stream().anyMatch(bound -> !definiteReference(bound.atom())))return Optional.empty();
        if(value.empty() && references && array.defaultFields() && length.isPresent() && position<length.getAsInt())
            value=Value.NULL.under(call.path());
        if(value.empty()) {
            Gap missing=Mechanisms.gap(call,GapKind.INPUT_BINDING,"reflection array element is unspecified");
            ObjectValue element=new ObjectValue(call.result().id(),"java/lang/Object",false,"reflective array element",false,array.source().map(source -> source.at(slot)));
            value=Value.of(element,call.path()).requiring(List.of(missing));
        }
        return Optional.of(Local.of(new RequireNormal(normal),new Result(value)));
    }
    private static OptionalInt knownLength(Value lengths,Path path) {
        Integer size=null;boolean covered=false;
        for(Bound length:lengths.alternatives()) {
            if(!(length.atom() instanceof Literal literal) || !(literal.value() instanceof Integer count)
                    || length.gaps().stream().anyMatch(gap -> gap.kind()==GapKind.BUDGET || gap.kind()==GapKind.UNSUPPORTED)
                    || size!=null && size!=count)return OptionalInt.empty();
            size=count;covered|=length.path().equals(path);
        }
        return covered && size!=null?OptionalInt.of(size):OptionalInt.empty();
    }
    private static boolean definiteReference(Atom value) {
        if(value instanceof Literal literal)return literal.value()==null || literal.value() instanceof String;
        return value instanceof ObjectValue object && object.exact() && Library.primitive(object.type()).isEmpty()
                || value instanceof ClassValue || value instanceof Reflected || value instanceof ReflectedField || value instanceof ConstructorValue
                || value instanceof LambdaValue || value instanceof ProxyValue || value instanceof ArrayValue;
    }
}
