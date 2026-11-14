package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Mechanisms.*;
import org.objectweb.asm.Opcodes;
import java.util.*;

/** JVM factory metadata and the particular created receiver determine dispatch. */
final class Dynamic implements Model {
    private static final String META="(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
    private static final String ALT="(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";
    private static final String HANDLER="(Ljava/lang/Object;Ljava/lang/reflect/Method;[Ljava/lang/Object;)Ljava/lang/Object;";

    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        if(call.call().target().owner().equals("java/lang/reflect/Proxy") && program.type("java/lang/reflect/Proxy",call.call().target().loader())
                .filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        if(call.is("java/lang/reflect/Proxy","<init>","(Ljava/lang/reflect/InvocationHandler;)V") && call.receiver() instanceof ObjectValue proxy) {
            Atom handler=call.arguments().get(0);
            if(handler.equals(new Literal(null)))return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            return Optional.of(Local.of(new RequireNormal(handler instanceof ObjectValue || handler instanceof LambdaValue || handler instanceof ProxyValue?List.of():Mechanisms.unknown(call,"nonnull proxy handler required")),new Write(proxy,new Field(new FieldId("java/lang/reflect/Proxy","h","Ljava/lang/reflect/InvocationHandler;")),Value.of(handler)),new Result(Value.NULL)));
        }
        if(call.is("java/lang/reflect/Proxy","getInvocationHandler","(Ljava/lang/Object;)Ljava/lang/reflect/InvocationHandler;")) {
            Atom value=call.arguments().get(0);
            if(value instanceof ProxyValue proxy)return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(proxy.handler())));
            if(value.equals(new Literal(null)))return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
        }
        if(call.is("java/lang/reflect/Proxy","isProxyClass","(Ljava/lang/Class;)Z")) {
            Atom value=call.arguments().get(0);
            if(value.equals(new Literal(null)))return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if(value instanceof ClassValue type) {
                if(type.source().filter(ValueSource.class::isInstance).map(ValueSource.class::cast).filter(source -> source.path().isEmpty() && source.producer() instanceof ProxyValue).isPresent())
                    return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new Literal(1))));
                if(type.exact()) {
                    Query<Boolean> compatible=program.assignable(Values.type(type.descriptor()),type.loader(),"java/lang/reflect/Proxy",0);
                    if(compatible.value().equals(Optional.of(false)) && compatible.pending().isEmpty())return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new Literal(0))));
                }
            }
        }
        if (call.call().bootstrap().filter(b -> b.factory().target().owner().equals("java/lang/invoke/LambdaMetafactory")).isPresent())
            return Optional.of(lambda(call,program));
        if (call.is("java/lang/Class","getClassLoader","()Ljava/lang/ClassLoader;") && call.receiver() instanceof ClassValue type && type.exact())
            return Optional.of(Local.of(Mechanisms.result(program.loaderIdentity(type.loader()).filter(Atom.class::isInstance).map(Atom.class::cast).orElse(new LoaderValue(Values.type(type.descriptor()))))));
        if (call.is("java/lang/reflect/Proxy","newProxyInstance","(Ljava/lang/ClassLoader;[Ljava/lang/Class;Ljava/lang/reflect/InvocationHandler;)Ljava/lang/Object;")) {
            ValueBindings.ArrayBindings interfaceArrays=ValueBindings.array(call.arguments().get(1),bindings,call.path(),call.call().site());
            List<ValueBindings.ArrayBinding> arrays=interfaceArrays.values();
            if (call.arguments().get(2) instanceof Literal literal && literal.value()==null) return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if (arrays.isEmpty()) {
                Gap pending=Mechanisms.gap(call,GapKind.INPUT_BINDING,"proxy interfaces must be a nonnull array of distinct, loader-visible interfaces; exact membership is unspecified");
                return Optional.of(interfaceArrays.keeping(Local.of(new Need(new InputNeed(call.arguments().get(1),Optional.empty(),NeedKind.ARGUMENTS,"[Ljava/lang/Class;",List.of(),pending.detail())),new RequireNormal(List.of(pending)),new Result(Value.of(new ProxyValue(call.result().id(),List.of(),call.arguments().get(2),call.call().site(),false)).requiring(List.of(pending))))));
            }
            List<Effect> effects=new ArrayList<>();
            for (ValueBindings.ArrayBinding array:arrays) {
                List<ClassValue> interfaces=new ArrayList<>();List<Gap> queryGaps=new ArrayList<>(); boolean valid=true,interfacesKnown=true;
                for (Atom value:array.elements()) {
                    if (!(value instanceof ClassValue type) || !type.exact()) {interfacesKnown=false;queryGaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"proxy interface element is unspecified"));continue;}
                    String name=Values.type(type.descriptor());
                    Optional<ClassInfo> typeInfo=program.type(name,type.loader());
                    if (typeInfo.isEmpty()) {interfaces.add(type);queryGaps.add(Mechanisms.gap(call,GapKind.MISSING_DEPENDENCY,"proxy interface declaration missing: "+name));}
                    else if ((typeInfo.get().access() & Opcodes.ACC_INTERFACE)!=0) interfaces.add(type); else { valid=false;break; }
                }
                if (!valid || interfaces.stream().map(type -> new DefinedType(type.descriptor(),type.loader())).distinct().count()!=interfaces.size()) {
                    effects.add(new Conditional(array.path(),array.gaps(),array.dependencies(),Local.of(new Raise("java/lang/IllegalArgumentException")))); continue;
                }
                List<Gap> gaps=new ArrayList<>(array.gaps());gaps.addAll(queryGaps);
                boolean visible=call.arguments().get(0) instanceof LoaderValue loader && interfaces.stream().allMatch(type -> Values.type(type.descriptor()).equals(loader.definingClass()) || program.type(Values.type(type.descriptor()),type.loader()).map(t -> t.role()==io.just.input.Inputs.Role.PLATFORM).orElse(false));
                if (!visible) gaps.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"interface visibility in the supplied loader is not established"));
                Atom handler=call.arguments().get(2);
                ValueBindings.Compatibility handlerMatch=ValueBindings.compatible(handler,"Ljava/lang/reflect/InvocationHandler;",program);
                gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),handlerMatch.pending())));
                if (!(handler instanceof ObjectValue object) || !object.exact() || handlerMatch.match()!=ValueBindings.Match.COMPATIBLE)
                    gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"same proxy handler runtime binding is unspecified"));
                effects.add(new Conditional(array.path(),List.copyOf(gaps),array.dependencies(),Local.of(Mechanisms.result(new ProxyValue(call.result().id(),interfaces,handler,call.call().site(),interfacesKnown)))));
            }
            return Optional.of(interfaceArrays.keeping(new Local(effects)));
        }
        if (call.receiver() instanceof LambdaValue lambda && call.call().target().name().equals(lambda.name())
                && (call.call().target().descriptor().equals(lambda.descriptor()) || lambda.bridges().contains(call.call().target().descriptor()))) {
            ValueBindings.Compatibility match=ValueBindings.compatible(lambda,"L"+call.call().target().owner()+";",program);
            if(match.match()==ValueBindings.Match.INCOMPATIBLE)return Optional.empty();
            return Optional.of(new Local(List.of(new Conditional(call.path(),Mechanisms.queryGaps(call,new Query<>(Optional.empty(),match.pending())),Set.of(),invokeLambda(call,lambda,program)))));
        }
        if (call.receiver() instanceof ProxyValue proxy) {
            MethodId api=call.call().target();
            boolean objectMethod=api.owner().equals("java/lang/Object") && Set.of("toString()Ljava/lang/String;","hashCode()I","equals(Ljava/lang/Object;)Z").contains(api.name()+api.descriptor());
            ValueBindings.Compatibility match=ValueBindings.compatible(proxy,"L"+api.owner()+";",program,api.loader());
            if (!objectMethod && match.match()==ValueBindings.Match.INCOMPATIBLE && !proxy.interfaces().isEmpty()) return Optional.empty();
            Query<Method> member=program.lookup(api);
            if (member.value().isEmpty()) return Optional.of(unknown(call,"proxy method declaration is missing",Mechanisms.queryGaps(call,member)));
            Atom handler=proxy.handler();
            MethodId handlerTarget=handler instanceof ObjectValue object?program.method(object.type(),"invoke",HANDLER,object.loader()):new MethodId("java/lang/reflect/InvocationHandler","invoke",HANDLER);
            Query<Method> target=program.lookup(handlerTarget);
            if(target.value().isEmpty() && !(handler instanceof LambdaValue || handler instanceof ProxyValue))return Optional.of(unknown(call,"handler invoke method is missing",Mechanisms.queryGaps(call,target)));
            MethodId declaration=member.value().orElseThrow().id();
            List<Atom> types=program.signature(declaration).parameters().stream().map(t -> (Atom)new ClassValue(t.descriptor(),true,Optional.empty(),program.scope(Values.type(t.descriptor()),declaration.loader()))).toList();
            Atom method=new Reflected(new ClassValue("L"+declaration.owner()+";",true,Optional.empty(),declaration.loader()),new Literal(api.name()),
                    new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",types),false,call.call().site());
            Atom arguments=call.arguments().isEmpty()?new Literal(null):new ArrayValue(call.result().id(),ArrayRole.PROXY_ARGUMENTS,"[Ljava/lang/Object;",call.arguments());
            List<Gap> gaps=new ArrayList<>(handler instanceof ObjectValue object && object.exact() || handler instanceof LambdaValue || handler instanceof ProxyValue?List.of():Mechanisms.unknown(call,"proxy handler runtime type is not exact"));
            if(!proxy.interfacesKnown() && !objectMethod)gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"actual proxy interface set must support "+api+" in its declaring loader"));
            gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),match.pending())));
            gaps.addAll(Mechanisms.queryGaps(call,member));gaps.addAll(Mechanisms.queryGaps(call,target));
            return Optional.of(Local.of(new Dispatch(target.value().map(Method::id).orElse(handlerTarget),handler,List.of(proxy,method,arguments),Kind.DYNAMIC_CALL,
                            gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,List.of(proxy.factory(),call.call().site()),gaps,ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT),
                    new Observe(Kind.DYNAMIC_CALL,"proxy interface call bound to its handler",List.of(proxy.factory(),call.call().site()),gaps)));
        }
        return Optional.empty();
    }

    private Local lambda(Invocation call,Program program) {
        Bootstrap bootstrap=call.call().bootstrap().orElseThrow(); MethodId factory=bootstrap.factory().target();
        boolean alternate=factory.name().equals("altMetafactory");
        if (!factory.owner().equals("java/lang/invoke/LambdaMetafactory") || bootstrap.factory().tag()!=Opcodes.H_INVOKESTATIC
                || !(factory.name().equals("metafactory") && factory.descriptor().equals(META) || alternate && factory.descriptor().equals(ALT)))
            return unknown(call,"invokedynamic bootstrap is not a supported LambdaMetafactory");
        List<JvmConstant> arguments=bootstrap.arguments();
        if (arguments.size()<3 || !(arguments.get(0) instanceof MethodTypeConstant sam) || !(arguments.get(1) instanceof HandleConstant implementation)
                || !(arguments.get(2) instanceof MethodTypeConstant instantiated)) return unknown(call,"invalid lambda bootstrap argument slots");
        List<String> bridges=new ArrayList<>(),markers=new ArrayList<>(); int cursor=3;
        if (alternate) {
            if (arguments.size()<4 || !(arguments.get(3) instanceof LiteralConstant value) || !(value.value() instanceof Integer flags) || flags<0 || (flags & ~7)!=0)
                return unknown(call,"invalid altMetafactory flags");
            cursor=4;
            if ((flags & 1)!=0) markers.add("java/io/Serializable");
            for (int flag:List.of(2,4)) if ((flags & flag)!=0) {
                if (cursor>=arguments.size() || !(arguments.get(cursor++) instanceof LiteralConstant count) || !(count.value() instanceof Integer size) || size<0 || size>arguments.size()-cursor)
                    return unknown(call,"invalid altMetafactory metadata count");
                for (int i=0;i<size;i++) {
                    JvmConstant metadata=arguments.get(cursor++);
                    if (flag==2 && !(metadata instanceof ClassConstant) || flag==4 && !(metadata instanceof MethodTypeConstant)) return unknown(call,"invalid altMetafactory metadata slot");
                    if (metadata instanceof MethodTypeConstant bridge) bridges.add(bridge.descriptor());
                    if (metadata instanceof ClassConstant marker) {
                        String name=Values.type(marker.descriptor());
                        Optional<ClassInfo> markerType=program.type(name,call.call().site().method().loader());
                        if(markerType.isEmpty())return unknown(call,"lambda marker declaration is missing",List.of(Mechanisms.gap(call,GapKind.MISSING_DEPENDENCY,"lambda marker declaration missing: "+name)));
                        if ((markerType.get().access() & Opcodes.ACC_INTERFACE)!=0) markers.add(name); else return unknown(call,"lambda marker is not an interface");
                    }
                }
            }
        }
        if (cursor!=arguments.size() || implementation.tag()<Opcodes.H_INVOKEVIRTUAL || implementation.tag()>Opcodes.H_INVOKEINTERFACE)
            return unknown(call,"unconsumed or invalid lambda bootstrap metadata");
        String owner=Values.type(program.signature(call.call().target()).returned().descriptor());
        Optional<ClassInfo> functionType=program.type(owner,call.call().site().method().loader());
        if(functionType.isEmpty())return unknown(call,"lambda functional interface declaration is missing",List.of(Mechanisms.gap(call,GapKind.MISSING_DEPENDENCY,"lambda functional interface declaration missing: "+owner)));
        if ((functionType.get().access() & Opcodes.ACC_INTERFACE)==0) return unknown(call,"lambda factory result is not an interface");
        if (program.signature(new MethodId(owner,call.call().target().name(),sam.descriptor())).parameters().size()!=program.signature(new MethodId(owner,call.call().target().name(),instantiated.descriptor())).parameters().size())
            return unknown(call,"lambda SAM/instantiated arity mismatch");
        return Local.of(Mechanisms.result(new LambdaValue(call.result().id(),owner,call.call().target().name(),sam.descriptor(),implementation,call.arguments(),bridges,markers,call.call().site())));
    }

    private Local invokeLambda(Invocation call,LambdaValue lambda,Program program) {
        HandleConstant handle=lambda.implementation(); MethodId selected=handle.target();
        List<Atom> arguments=new ArrayList<>(lambda.captured()); arguments.addAll(call.arguments());
        Atom receiver=new Literal(null); List<Effect> effects=new ArrayList<>(); List<Gap> gaps=new ArrayList<>();
        if (handle.tag()==Opcodes.H_NEWINVOKESPECIAL) {
            // Construction is scheduled by the same owner as reflective constructors.
        } else if (handle.tag()!=Opcodes.H_INVOKESTATIC) {
            if (arguments.isEmpty()) return unknown(call,"lambda instance receiver is missing");
            receiver=arguments.remove(0);
            if (receiver instanceof ObjectValue object) {
                Query<Boolean> match=program.assignable(object.type(),object.loader(),selected.owner(),selected.loader());
                if (match.value().equals(Optional.of(false))) return Local.of(new Raise("java/lang/ClassCastException"));
                gaps.addAll(Mechanisms.queryGaps(call,match));
                if (!object.exact()) gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"lambda receiver runtime type is unspecified"));
                if (handle.tag()!=Opcodes.H_INVOKESPECIAL) {
                    Query<Method> actual=program.lookup(program.method(object.type(),selected.name(),selected.descriptor(),object.loader()));
                    gaps.addAll(Mechanisms.queryGaps(call,actual));selected=actual.value().map(Method::id).orElse(selected);
                }
            } else if (receiver instanceof Literal literal && literal.value()==null) return Local.of(new Raise("java/lang/NullPointerException"));
            else return unknown(call,"lambda receiver binding is unsupported");
        }
        List<ValueType> parameters=program.signature(selected).parameters();
        if (arguments.size()!=parameters.size()) return unknown(call,"lambda implementation arity mismatch");
        for (int i=0;i<arguments.size();i++) {
            ValueBindings.Compatibility compatible=ValueBindings.compatible(arguments.get(i),parameters.get(i).descriptor(),program,selected.loader());
            gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),compatible.pending())));
            if (compatible.match()==ValueBindings.Match.INCOMPATIBLE) return Local.of(new Raise("java/lang/ClassCastException"));
            if (compatible.match()==ValueBindings.Match.UNKNOWN) gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"lambda argument adaptation is not established"));
        }
        if(handle.tag()==Opcodes.H_NEWINVOKESPECIAL)effects.add(new Construct(selected,List.copyOf(arguments),Kind.DYNAMIC_CALL,List.of(lambda.factory(),call.call().site()),List.copyOf(gaps),ExceptionFlow.DIRECT));
        else effects.add(new Dispatch(selected,receiver,List.copyOf(arguments),Kind.DYNAMIC_CALL,gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,
                List.of(lambda.factory(),call.call().site()),List.copyOf(gaps),handle.tag()==Opcodes.H_NEWINVOKESPECIAL?ReturnFlow.IGNORE:ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT));
        effects.add(new Observe(Kind.DYNAMIC_CALL,"lambda implementation from its designated bootstrap handle",List.of(lambda.factory(),call.call().site()),List.copyOf(gaps)));
        return new Local(effects);
    }
    private static Local unknown(Invocation call,String detail) {
        return unknown(call,detail,List.of());
    }
    private static Local unknown(Invocation call,String detail,List<Gap> pending) {
        List<Gap> gaps=pending.isEmpty()?List.of(Mechanisms.gap(call,GapKind.UNSUPPORTED,detail)):pending;
        return Local.of(new Result(Value.of(new Unknown(detail)).requiring(gaps)),new Observe(Kind.DYNAMIC_CALL,detail,List.of(call.call().site()),gaps));
    }
}
