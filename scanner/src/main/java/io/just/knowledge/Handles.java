package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Mechanisms.*;
import java.util.*;
import static io.just.knowledge.ValueBindings.*;

/** Public, exact handles. Lookup MethodType and polymorphic invocation type are separate facts. */
final class Handles implements Model {
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        MethodId api=call.call().target();
        if(call.is("java/lang/invoke/MethodHandles","lookup","()Ljava/lang/invoke/MethodHandles$Lookup;") || call.is("java/lang/invoke/MethodHandles","publicLookup","()Ljava/lang/invoke/MethodHandles$Lookup;"))
            return Optional.of(Local.of(Mechanisms.result(new LookupValue(call.call().site().method().owner(),api.name().equals("publicLookup"),call.call().site()))));
        if(api.owner().equals("java/lang/invoke/MethodType") && api.name().equals("methodType") && api.descriptor().endsWith(")Ljava/lang/invoke/MethodType;")) {
            if(!call.arguments().isEmpty() && call.arguments().get(0) instanceof Literal nil && nil.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if(call.arguments().isEmpty() || !(call.arguments().get(0) instanceof ClassValue returned) || !returned.exact())return Optional.of(unresolved(call,"MethodType return Class is unspecified"));
            List<Atom> prefix=new ArrayList<>();Atom array=new Literal(null);
            for(int i=1;i<call.arguments().size();i++) {
                Atom argument=call.arguments().get(i);
                if(argument instanceof Literal literal && literal.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
                if(argument instanceof ClassValue)prefix.add(argument);else array=argument;
            }
            List<Effect> effects=new ArrayList<>();
            ArrayBindings arrays=array(array,bindings,call.path(),call.call().site());
            for(ArrayBinding tail:arrays.values()) {
                List<Atom> parameters=new ArrayList<>(prefix);parameters.addAll(tail.elements());
                if(parameters.stream().anyMatch(p -> !(p instanceof ClassValue c) || !c.exact()))return Optional.of(unresolved(call,"MethodType parameter Classes are unspecified"));
                if(parameters.stream().anyMatch(p -> ((ClassValue)p).descriptor().equals("V")))return Optional.of(Local.of(new Raise("java/lang/IllegalArgumentException")));
                effects.add(new Conditional(tail.path(),tail.gaps(),tail.dependencies(),Local.of(Mechanisms.result(new MethodTypeValue(returned,parameters.stream().map(ClassValue.class::cast).toList())))));
            }
            return Optional.of(arrays.keeping(effects.isEmpty()?unresolved(call,"MethodType parameter array is unspecified"):new Local(effects)));
        }
        if(api.owner().equals("java/lang/invoke/MethodHandles$Lookup") && Set.of("findStatic","findVirtual").contains(api.name())
                && api.descriptor().equals("(Ljava/lang/Class;Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/MethodHandle;")) {
            if(call.arguments().stream().anyMatch(a -> a instanceof Literal nil && nil.value()==null))return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if(!(call.receiver() instanceof LookupValue lookup))return Optional.of(unresolved(call,"Lookup origin and access are unspecified"));
            if(!(call.arguments().get(0) instanceof ClassValue owner) || !owner.exact() || !(call.arguments().get(1) instanceof Literal name) || !(name.value() instanceof String text) || !(call.arguments().get(2) instanceof MethodTypeValue type)) {
                List<Effect> missing=new ArrayList<>(unresolved(call,"exact Class, method name and actual MethodType are required").effects());
                if(!(call.arguments().get(2) instanceof MethodTypeValue))missing.add(new Need(new InputNeed(call.arguments().get(2),Optional.empty(),NeedKind.LOOKUP_TYPE,"Ljava/lang/invoke/MethodType;",List.of(),"actual lookup MethodType, independent of invokeExact descriptor")));
                return Optional.of(new Local(missing));
            }
            String requested=Values.type(owner.descriptor());Query<Method> query=program.lookup(program.method(requested,text,type.descriptor(),owner.loader()));
            if(query.absent())return Optional.of(Local.of(new Raise("java/lang/NoSuchMethodException")));
            if(query.value().isEmpty())return Optional.of(unresolved(call,"handle lookup is unresolved",Mechanisms.queryGaps(call,query)));
            Method target=query.value().get();boolean virtual=api.name().equals("findVirtual");
            if(!sameSignature(target.id(),new ArrayList<Atom>(type.parameters()),program)
                    || !sameType(type,methodType(target.id().descriptor(),program,target.id().loader())))return Optional.of(Local.of(new Raise("java/lang/NoSuchMethodException")));
            if(target.isStatic()==virtual)return Optional.of(Local.of(new Raise("java/lang/IllegalAccessException")));
            boolean publicClass=program.type(requested,owner.loader()).map(c -> (c.access() & org.objectweb.asm.Opcodes.ACC_PUBLIC)!=0).orElse(false);
            if(!target.isPublic() || !publicClass) {
                if(lookup.publicOnly())return Optional.of(Local.of(new Raise("java/lang/IllegalAccessException")));
                return Optional.of(unresolved(call,"non-public handle lookup access is outside the supported public subset"));
            }
            List<ClassValue> parameters=new ArrayList<>();if(virtual)parameters.add(owner);parameters.addAll(type.parameters());
            MethodTypeValue invocation=new MethodTypeValue(type.returned(),parameters);
            return Optional.of(Local.of(new Result(Value.of(new MethodHandleValue(target.id(),invocation,virtual,lookup,call.call().site())).requiring(Mechanisms.queryGaps(call,query)))));
        }
        if(api.owner().equals("java/lang/invoke/MethodHandle") && api.name().equals("invokeExact")) {
            if(!(call.receiver() instanceof MethodHandleValue handle))return Optional.of(unresolved(call,"handle has no exact supported lookup binding"));
            if(!sameType(handle.invocationType(),methodType(api.descriptor(),program,call.call().site().method().loader())))return Optional.of(Local.of(new Raise("java/lang/invoke/WrongMethodTypeException")));
            List<Gap> gaps=new ArrayList<>();MethodId target=handle.target();Atom receiver=new Literal(null);int first=0;
            List<ValueType> types=program.signature(api).parameters();
            for(int i=0;i<types.size();i++) {
                Compatibility compatibility=compatible(call.arguments().get(i),types.get(i).descriptor(),program,handle.invocationType().parameters().get(i).loader());
                if(compatibility.match()==Match.INCOMPATIBLE)return Optional.of(Local.of(new Raise("java/lang/ClassCastException")));
                gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),compatibility.pending())));
                if(compatibility.match()==Match.UNKNOWN)gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"invokeExact argument binding at slot "+i+" is unspecified"));
            }
            if(handle.virtual()) {
                receiver=call.arguments().get(0);first=1;
                if(receiver instanceof Literal l && l.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
                if(receiver instanceof ObjectValue object) {
                    Query<Method> actual=program.lookup(program.method(object.type(),target.name(),target.descriptor(),object.loader()));
                    gaps.addAll(Mechanisms.queryGaps(call,actual));target=actual.value().map(Method::id).orElse(target);
                    if(!object.exact())gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"virtual handle receiver runtime type is unspecified"));
                }
            }
            List<Site> witness=List.of(handle.lookup().source(),handle.source());
            return Optional.of(Local.of(new Dispatch(target,receiver,call.arguments().subList(first,call.arguments().size()),Kind.METHOD_HANDLE,gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,witness,gaps,ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT),new Observe(Kind.METHOD_HANDLE,"exact MethodHandle target",witness,gaps)));
        }
        return Optional.empty();
    }
    private static Local unresolved(Invocation call,String reason){return unresolved(call,reason,List.of());}
    private static Local unresolved(Invocation call,String reason,List<Gap> pending){
        List<Gap> gaps=new ArrayList<>(pending);gaps.add(Mechanisms.gap(call,GapKind.DYNAMIC_TARGET,reason));
        return Local.of(new Result(Value.of(new Unknown(reason)).requiring(gaps)),new Observe(Kind.METHOD_HANDLE,reason,List.of(call.call().site()),gaps));
    }
}
