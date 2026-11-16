package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import static io.just.knowledge.ValueBindings.*;
import org.objectweb.asm.Opcodes;
import java.util.*;

/** Lookup snapshots and argument/access checks; allocation and invocation belong to analysis. */
final class Constructors implements Model {
    private final Guidance guidance;
    Constructors(Guidance guidance){this.guidance=guidance;}
    private static final Field OVERRIDE=new Field(new FieldId("java/lang/reflect/AccessibleObject","override","Z"));
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        if(!Set.of("java/lang/Class","java/lang/reflect/Constructor").contains(call.call().target().owner()))return Optional.empty();
        Query<Method> api=program.declaration(call.call().target());
        if(api.value().flatMap(m -> program.type(m.id().owner())).filter(c -> c.role()==io.just.input.Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        if((call.is("java/lang/Class","getConstructors","()[Ljava/lang/reflect/Constructor;") || call.is("java/lang/Class","getDeclaredConstructors","()[Ljava/lang/reflect/Constructor;"))
                && call.receiver() instanceof ClassValue owner && owner.exact()) {
            boolean declared=call.call().target().name().equals("getDeclaredConstructors");int count=0;
            if(owner.descriptor().startsWith("L")) {
                Query<ClassInfo> type=program.definition(Values.type(owner.descriptor()),owner.loader());List<Gap> pending=Mechanisms.queryGaps(call,type);
                if(type.value().isEmpty())return Optional.of(Local.of(new RequireNormal(pending),new Result(Value.of(new Unknown("constructor collection declaration is missing")).requiring(pending))));
                count=(int)type.value().orElseThrow().methods().stream().filter(method -> method.id().name().equals("<init>") && (declared || method.isPublic())).count();
            }
            // The count is known; individual mutable Constructor objects stay unresolved until modeled.
            ObjectValue array=new ObjectValue(call.result().id(),"[Ljava/lang/reflect/Constructor;",true,"constructor collection",false);
            return Optional.of(Local.of(new RequireNormal(List.of()),new Write(array,new Length(),Value.of(new Literal(count))),Mechanisms.result(array)));
        }
        if(call.is("java/lang/Class","getConstructor","([Ljava/lang/Class;)Ljava/lang/reflect/Constructor;")
                || call.is("java/lang/Class","getDeclaredConstructor","([Ljava/lang/Class;)Ljava/lang/reflect/Constructor;")) {
            boolean declared=call.call().target().name().equals("getDeclaredConstructor");
            ArrayBindings signatureArrays=array(call.arguments().get(0),bindings,call.path(),call.call().site());
            List<ArrayBinding> signatures=signatureArrays.values();
            if(signatures.isEmpty() && call.receiver() instanceof ClassValue owner && owner.exact()) {
                List<Effect> choices=new ArrayList<>();
                List<Method> members=program.type(Values.type(owner.descriptor()),owner.loader()).map(ClassInfo::methods).orElse(List.of()).stream().filter(method -> method.id().name().equals("<init>") && (declared || method.isPublic())).toList();
                Query<List<Method>> ordered=guidance.order(members);
                if(!ordered.pending().isEmpty())choices.add(new Observe(Kind.REFLECTION,"constructor relation frontier",List.of(call.call().site()),Mechanisms.queryGaps(call,ordered)));
                int selection=0;
                for(Method target:ordered.value().orElseThrow()) {
                    if(selection>=bindings.alternatives()){choices.add(new Observe(Kind.REFLECTION,"constructor member frontier",List.of(call.call().site()),List.of(Mechanisms.gap(call,GapKind.BUDGET,"constructor target budget ("+bindings.alternatives()+")"))));break;}
                    List<Atom> signature=program.signature(target.id()).parameters().stream().map(p -> (Atom)new ClassValue(p.descriptor(),true,Optional.empty(),program.scope(Values.type(p.descriptor()),owner.loader()))).toList();
                    ArrayValue required=new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",signature);
                    choices.add(new Alternative(selection++,Local.of(new Need(new InputNeed(call.arguments().get(0),Optional.empty(),NeedKind.METHOD_TYPES,"[Ljava/lang/Class;",List.of(required),"constructor signature required by "+target.id())),
                            Mechanisms.result(new ConstructorValue(call.result().id(),owner,required,declared,call.call().site())))));
                }
                if(!choices.isEmpty())return Optional.of(signatureArrays.keeping(new Local(choices)));
            }
            if(signatures.isEmpty())return Optional.of(signatureArrays.keeping(unresolved(call,"constructor parameter Classes are unspecified",List.of(),List.of(
                    new Need(new InputNeed(call.arguments().get(0),Optional.empty(),NeedKind.METHOD_TYPES,"[Ljava/lang/Class;",List.of(),"constructor lookup signature at this use"))))));
            List<Effect> effects=new ArrayList<>();
            for(ArrayBinding signature:signatures) {
                List<Gap> gaps=new ArrayList<>(signature.gaps());Local lookup;
                if(call.receiver() instanceof ClassValue owner && owner.exact() && exact(signature.elements())) {
                    Query<Method> method=program.constructor(Values.type(owner.descriptor()),types(signature.elements()),declared,owner.loader());
                    gaps.addAll(Mechanisms.queryGaps(call,method));
                    lookup=method.absent() || method.value().isPresent() && !sameSignature(method.value().get().id(),signature.elements(),program)?Local.of(new Raise("java/lang/NoSuchMethodException")):
                            Local.of(new RequireNormal(gaps),new Result(Value.of(metadata(call,signature.elements(),declared)).requiring(gaps)));
                } else lookup=Local.of(new RequireNormal(Mechanisms.unknown(call,"constructor lookup must resolve its class and signature")),Mechanisms.result(metadata(call,signature.elements(),declared)));
                effects.add(new Conditional(signature.path(),List.copyOf(gaps),signature.dependencies(),lookup));
            }
            return Optional.of(signatureArrays.keeping(new Local(effects)));
        }
        if(call.receiver() instanceof ConstructorValue constructor && call.is("java/lang/reflect/Constructor","setAccessible","(Z)V"))
            return Optional.of(Local.of(new RequireNormal(List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"access suppression requires the target platform permission and module policy"))),
                    new Write(metadataObject(constructor),OVERRIDE,Value.of(call.arguments().get(0))),new Result(Value.NULL)));
        if(call.is("java/lang/Class","newInstance","()Ljava/lang/Object;"))
            return Optional.of(construct(call,call.receiver(),List.of(),List.of(),true,true,false,List.of(),List.of(call.call().site()),program));
        if(!call.is("java/lang/reflect/Constructor","newInstance","([Ljava/lang/Object;)Ljava/lang/Object;"))return Optional.empty();
        if(!(call.receiver() instanceof ConstructorValue constructor))return Optional.of(unresolved(call,"Constructor object has no lookup binding",List.of(),List.of()));
        ArrayBindings argumentArrays=array(call.arguments().get(0),bindings,call.path(),call.call().site());
        List<ArrayBinding> arguments=argumentArrays.values();
        List<Effect> demands=new ArrayList<>();
        if(arguments.isEmpty() && exact(constructor.parameterTypes().elements())) {
            Atom array=call.arguments().get(0);List<Atom> inferred=new ArrayList<>();int index=0;
            demands.add(new Need(new InputNeed(array,Optional.of(new Length()),NeedKind.VALUE,"I",List.of(new Literal(constructor.parameterTypes().elements().size())),"constructor argument count")));
            for(Atom parameter:constructor.parameterTypes().elements()) {
                String descriptor=((ClassValue)parameter).descriptor();Optional<InputSource> source=Values.source(array).map(s -> s.at(new Index(inferred.size())));
                Atom value=descriptor.length()==1?source.<Atom>map(s -> new ExternalValue(descriptor,s)).orElse(new Unknown("constructor primitive argument "+index)):new Symbolic(Values.type(descriptor),"constructor argument "+index,source,((ClassValue)parameter).loader());
                inferred.add(value);demands.add(new Need(new InputNeed(array,Optional.of(new Index(index++)),NeedKind.VALUE,descriptor,List.of(),"constructor argument slot")));
            }
            arguments=List.of(new ArrayBinding(List.copyOf(inferred),call.path(),Mechanisms.unknown(call,"constructor arguments remain conditional input"),Set.of()));
        }
        if(arguments.isEmpty())return Optional.of(argumentArrays.keeping(unresolved(call,"constructor argument array is unspecified",List.of(),List.of(
                new Need(new InputNeed(call.arguments().get(0),Optional.empty(),NeedKind.ARGUMENTS,"[Ljava/lang/Object;",List.of(),"constructor arguments at this invocation"))))));
        Value access=bindings.read(metadataObject(constructor),OVERRIDE);
        if(access.empty())access=Value.of(new Literal(0));
        List<Effect> effects=new ArrayList<>(demands);
        for(ArrayBinding args:arguments)for(ArrayBinding prepared:adapt(call,args,constructor.parameterTypes().elements(),bindings,effects))for(Bound flag:access.alternatives()) {
            Optional<Path> path=prepared.path().and(flag.path());if(path.isEmpty())continue;
            List<Gap> gaps=new ArrayList<>(prepared.gaps());gaps.addAll(flag.gaps());
            boolean known=flag.atom() instanceof Literal l && (l.value() instanceof Number || l.value() instanceof Boolean);
            boolean override=!known || flag.atom() instanceof Literal l && (l.value() instanceof Number n && n.intValue()!=0 || Boolean.TRUE.equals(l.value()));
            if(!known)gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"constructor access override is unresolved"));
            Set<Integer> dependencies=new LinkedHashSet<>(prepared.dependencies());dependencies.addAll(flag.dependencies());
            effects.add(new Conditional(path.get(),List.copyOf(gaps),Set.copyOf(dependencies),construct(call,constructor.declaringClass(),constructor.parameterTypes().elements(),prepared.elements(),constructor.declared(),false,override,gaps,List.of(constructor.lookup()),program)));
        }
        return Optional.of(argumentArrays.keeping(new Local(effects)));
    }
    private ConstructorValue metadata(Invocation call,List<Atom> signature,boolean declared) {
        return new ConstructorValue(call.result().id(),call.receiver(),new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",signature),declared,call.call().site());
    }
    private ObjectValue metadataObject(ConstructorValue value){return new ObjectValue(value.id(),"java/lang/reflect/Constructor",true,"constructor metadata",true);}
    private static boolean exact(List<Atom> signature){return signature.stream().allMatch(a -> a instanceof ClassValue c && c.exact());}
    private static List<String> types(List<Atom> signature){return signature.stream().map(a -> ((ClassValue)a).descriptor()).toList();}
    private Local construct(Invocation call,Atom owner,List<Atom> signature,List<Atom> arguments,boolean declared,boolean legacy,boolean override,List<Gap> required,List<Site> witnesses,Program program) {
        if(!(owner instanceof ClassValue type) || !type.exact())return unresolved(call,"construction requires an exact Class",required,List.of(
                new Need(new InputNeed(owner,Optional.empty(),NeedKind.RECEIVER_TYPE,"Ljava/lang/Class;",List.of(),"bind the Class being constructed"))));
        if(!exact(signature))return unresolved(call,"constructor signature is not exact",required,List.of(
                new Need(new InputNeed(call.receiver(),Optional.empty(),NeedKind.METHOD_TYPES,"[Ljava/lang/Class;",List.of(),"bind constructor lookup parameter Classes"))));
        if(!type.descriptor().startsWith("L"))return Local.of(new Raise("java/lang/InstantiationException"));
        String name=Values.type(type.descriptor());
        Optional<ClassInfo> info=program.type(name,type.loader());
        Query<Method> query=program.constructor(name,types(signature),declared,type.loader());
        List<Gap> gaps=new ArrayList<>(required);gaps.addAll(Mechanisms.queryGaps(call,query));
        if(query.value().isEmpty())return query.absent()?Local.of(new Raise(legacy?"java/lang/InstantiationException":"java/lang/NoSuchMethodException")):
                unresolved(call,"constructor declaration is unavailable",gaps,List.of());
        if((info.orElseThrow().access() & (Opcodes.ACC_ABSTRACT|Opcodes.ACC_INTERFACE))!=0)return Local.of(new Raise("java/lang/InstantiationException"));
        Method target=query.value().get();
        if(!sameSignature(target.id(),signature,program))return Local.of(new Raise("java/lang/NoSuchMethodException"));
        if(!override) {
            Query<Boolean> allowed=accessible(target,call.call().site().method(),info.orElseThrow(),program);
            gaps.addAll(Mechanisms.queryGaps(call,allowed));
            if(allowed.value().equals(Optional.of(false)))return Local.of(new Raise("java/lang/IllegalAccessException"));
        } else gaps.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"constructor access suppression must be permitted"));
        List<String> parameters=types(signature);
        if(parameters.size()!=arguments.size())return Local.of(new Raise("java/lang/IllegalArgumentException"));
        for(int i=0;i<parameters.size();i++) {
            Atom argument=arguments.get(i);String parameter=parameters.get(i);
            if(parameter.length()==1 && argument instanceof Literal l && l.value()==null)return Local.of(new Raise("java/lang/IllegalArgumentException"));
            if(parameter.length()==1 && argument instanceof ObjectValue boxed && Library.primitive(boxed.type()).filter(p -> !canUnbox(p,parameter)).isPresent())return Local.of(new Raise("java/lang/IllegalArgumentException"));
            Compatibility match=compatible(argument,parameter,program,target.id().loader());gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),match.pending())));
            if(match.match()==Match.INCOMPATIBLE)return Local.of(new Raise("java/lang/IllegalArgumentException"));
            if(match.match()==Match.UNKNOWN)gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"constructor argument compatibility at slot "+i+" is unresolved"));
        }
        return Local.of(new Construct(target.id(),arguments,Kind.REFLECTION,witnesses,List.copyOf(gaps),legacy?ExceptionFlow.DIRECT:ExceptionFlow.REFLECTED));
    }
    private Query<Boolean> accessible(Method method,MethodId caller,ClassInfo type,Program program) {
        boolean samePackage=caller.loader()==type.loader() && packageName(caller.owner()).equals(packageName(type.name()));
        if((type.access() & Opcodes.ACC_PUBLIC)==0 && !samePackage)return new Query<>(Optional.of(false),List.of());
        if((method.access() & Opcodes.ACC_PRIVATE)!=0)return program.nestmates(caller.owner(),caller.loader(),type.name(),type.loader());
        if(method.isPublic() || samePackage)return new Query<>(Optional.of(true),List.of());
        return (method.access() & Opcodes.ACC_PROTECTED)!=0?program.assignable(caller.owner(),caller.loader(),type.name(),type.loader()):new Query<>(Optional.of(false),List.of());
    }
    private String packageName(String name){return name.substring(0,Math.max(0,name.lastIndexOf('/')));}
    private Local unresolved(Invocation call,String reason,List<Gap> required,List<Effect> needs) {
        List<Gap> gaps=new ArrayList<>(required);
        if(gaps.isEmpty())gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,reason));
        List<Effect> effects=new ArrayList<>(needs);effects.add(new RequireNormal(List.copyOf(gaps)));
        effects.add(new Result(Value.of(new Unknown(reason)).requiring(List.copyOf(gaps))));
        effects.add(new Observe(Kind.REFLECTION,reason,List.of(call.call().site()),List.copyOf(gaps)));return new Local(effects);
    }
}
