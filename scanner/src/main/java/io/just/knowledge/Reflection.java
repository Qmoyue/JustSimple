package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Mechanisms.*;
import org.objectweb.asm.Opcodes;
import java.util.*;
import static io.just.knowledge.ValueBindings.*;

final class Reflection implements Model {
    private final DynamicTargets targets;
    private record RuntimeQuery(String upper,int upperLoader,boolean exact,String owner,int ownerLoader,boolean serialized) {}
    private record RuntimeView(List<ClassInfo> scope,LinkedHashMap<RuntimeQuery,List<ClassValue>> values) {}
    private Optional<RuntimeView> runtimes=Optional.empty();
    private record MemberFamily(String owner,String name,int loader) {}
    private record MemberChoices(Optional<MemberFamily> batch,ArrayDeque<Local> choices) {}
    Reflection(DynamicTargets targets){this.targets=targets;}
    static final MethodId INVOKE = new MethodId("java/lang/reflect/Method", "invoke", "(Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;");

    @Override public Optional<Local> apply(Invocation call, Bindings bindings, Program program) {
        if(call.is("java/lang/Class","getName","()Ljava/lang/String;") && call.receiver() instanceof ClassValue type) {
            if(!type.exact())return Optional.of(Local.of(new Result(Value.of(new Unknown("runtime Class name is unspecified")).requiring(Mechanisms.unknown(call,"Class.getName requires the actual runtime Class")))));
            String descriptor=type.descriptor();
            String name=switch(descriptor){case "Z" -> "boolean";case "B" -> "byte";case "C" -> "char";case "S" -> "short";case "I" -> "int";case "J" -> "long";case "F" -> "float";case "D" -> "double";case "V" -> "void";default -> descriptor.startsWith("L")?descriptor.substring(1,descriptor.length()-1).replace('/','.'):descriptor.replace('/','.');};
            return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new Literal(name))));
        }
        if (call.receiver() instanceof Reflected method) {
            if (call.is("java/lang/reflect/Method","getName","()Ljava/lang/String;")) return Optional.of(Local.of(Mechanisms.result(method.name())));
            if (call.is("java/lang/reflect/Method","getDeclaringClass","()Ljava/lang/Class;")) return Optional.of(Local.of(Mechanisms.result(method.declaringClass())));
            if (call.is("java/lang/reflect/Method","getParameterTypes","()[Ljava/lang/Class;")) return Optional.of(Local.of(Mechanisms.result(method.parameterTypes())));
            if(method.declaringClass() instanceof ClassValue owner && method.name() instanceof Literal name && name.value() instanceof String text && method.parameterTypes() instanceof ArrayValue parameters) {
                Query<Method> selected=program.reflect(Values.type(owner.descriptor()),text,parameters.elements().stream().filter(a -> a instanceof ClassValue).map(a -> ((ClassValue)a).descriptor()).toList(),method.declared(),owner.loader());
                if(selected.value().isPresent()) {
                    Method metadata=selected.value().get();
                    if(call.is("java/lang/reflect/Method","getParameterCount","()I"))return Optional.of(Local.of(Mechanisms.result(new Literal(program.signature(metadata.id()).parameters().size()))));
                    if(call.is("java/lang/reflect/Method","getReturnType","()Ljava/lang/Class;"))return Optional.of(Local.of(Mechanisms.result(new ClassValue(program.signature(metadata.id()).returned().descriptor(),true,Optional.empty(),program.scope(Values.type(program.signature(metadata.id()).returned().descriptor()),metadata.id().loader())))));
                    if(call.is("java/lang/reflect/Method","getModifiers","()I"))return Optional.of(Local.of(Mechanisms.result(new Literal(metadata.access()))));
                }
            }
        }
        if (call.is("java/lang/Object", "getClass", "()Ljava/lang/Class;")) {
            Atom value = call.receiver() instanceof ObjectValue object
                    ? new ClassValue(object.type().startsWith("[") ? object.type() : "L" + object.type() + ";", object.exact(),Values.location(object).filter(s -> s instanceof InputSource || !object.exact()).map(s -> s.at(new RuntimeClass())),object.loader())
                    : call.receiver() instanceof ArrayValue array ? new ClassValue(array.descriptor(),true)
                    : call.receiver() instanceof ClassValue ? new ClassValue("Ljava/lang/Class;", true)
                    : call.receiver() instanceof Reflected ? new ClassValue("Ljava/lang/reflect/Method;", true)
                    : call.receiver() instanceof Literal literal && literal.value() instanceof String
                    ? new ClassValue("Ljava/lang/String;", true) : new Unknown("runtime class is unspecified");
            return Optional.of(Local.of(new RequireNormal(call.receiver() instanceof ObjectValue object && !object.exact()?Mechanisms.unknown(call,"getClass requires a nonnull receiver"):List.of()),Mechanisms.result(value)));
        }
        if(call.is("java/lang/Class","getMethods","()[Ljava/lang/reflect/Method;") || call.is("java/lang/Class","getDeclaredMethods","()[Ljava/lang/reflect/Method;")) {
            if(!(call.receiver() instanceof ClassValue owner) || !owner.exact())return Optional.of(Local.of(new Result(Value.of(new Unknown("method collection class is unspecified")).requiring(Mechanisms.unknown(call,"method collection requires the declaring Class")))));
            boolean declared=call.call().target().name().equals("getDeclaredMethods");Query<List<Method>> query=program.methods(Values.type(owner.descriptor()),declared,owner.loader());
            List<Atom> values=new ArrayList<>();
            for(Method method:query.value().orElse(List.of())) {
                List<Atom> signature=program.signature(method.id()).parameters().stream().map(t -> (Atom)new ClassValue(t.descriptor(),true,Optional.empty(),program.scope(Values.type(t.descriptor()),method.id().loader()))).toList();
                values.add(new Reflected(new ClassValue("L"+method.id().owner()+";",true,Optional.empty(),method.id().loader()),new Literal(method.id().name()),new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",signature),declared,call.call().site()));
            }
            List<Gap> pending=Mechanisms.queryGaps(call,query),conditions=new ArrayList<>(pending);
            conditions.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"reflection method array order is unspecified"));
            ArrayValue snapshot=new ArrayValue(call.result().id(),ArrayRole.METHOD_COLLECTION,"[Ljava/lang/reflect/Method;",values,ArrayOrder.UNSPECIFIED,
                    query.pending().isEmpty()?ArrayExtent.EXACT:ArrayExtent.UNKNOWN,conditions);
            return Optional.of(Local.of(new RequireNormal(pending),new Result(Value.of(snapshot).requiring(pending))));
        }
        if (call.is("java/lang/Class", "getMethod", "(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;")
                || call.is("java/lang/Class", "getDeclaredMethod", "(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;")) {
            if(call.arguments().get(0) instanceof Literal nil && nil.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            boolean declared=call.call().target().name().equals("getDeclaredMethod");
            call=new Invocation(call.call(),call.receiver(),List.of(tracked(call,0,"Ljava/lang/String;"),tracked(call,1,"[Ljava/lang/Class;")),call.result(),call.path());
            ArrayBindings lookupArrays=array(call.arguments().get(1),bindings,call.path(),call.call().site());
            List<ArrayBinding> signatures=lookupArrays.values();
            if (signatures.isEmpty()) {
                Atom captured=snapshot(call,call.arguments().get(1));
                Invocation lookupCall=new Invocation(call.call(),call.receiver(),List.of(call.arguments().get(0),captured),call.result(),call.path());
                return Optional.of(lookupArrays.keeping(Local.of(new RequireNormal(Mechanisms.unknown(call,"lookup requires an existing member with this name and signature"),Optional.of(lookupCall)),Mechanisms.result(new Reflected(call.receiver(),call.arguments().get(0),captured,declared,call.call().site())))));
            }
            List<Effect> effects=new ArrayList<>();
            for (ArrayBinding signature:signatures) {
                Atom owner=call.receiver();
                Local lookup;
                if(signature.elements().stream().anyMatch(a -> a instanceof Literal literal && literal.value()==null)) {
                    effects.add(new Conditional(signature.path(),signature.gaps(),signature.dependencies(),Local.of(new Raise("java/lang/NoSuchMethodException"))));continue;
                }
                boolean exact=owner instanceof ClassValue lookupClass && lookupClass.exact() && call.arguments().get(0) instanceof Literal literal && literal.value() instanceof String
                        && signature.elements().stream().allMatch(v -> v instanceof ClassValue signatureType && signatureType.exact());
                if (exact) {
                    String type=Values.type(((ClassValue)owner).descriptor());
                    List<String> types=signature.elements().stream().map(v -> ((ClassValue)v).descriptor()).toList();
                    Query<Method> query=program.reflect(type,(String)((Literal)call.arguments().get(0)).value(),types,declared,((ClassValue)owner).loader());
                    Optional<Method> method=query.value();
                    if (query.absent() || method.isPresent() && !sameSignature(method.get().id(),signature.elements(),program)) lookup=Local.of(new Raise("java/lang/NoSuchMethodException"));
                    else {
                        if (method.isPresent()) owner=new ClassValue("L"+method.get().id().owner()+";",true,Optional.empty(),method.get().id().loader());
                        lookup=Local.of(new RequireNormal(Mechanisms.queryGaps(call,query)),new Result(Value.of(new Reflected(owner,call.arguments().get(0),new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",signature.elements()),declared,call.call().site())).requiring(Mechanisms.queryGaps(call,query))));
                    }
                } else {
                    ArrayValue captured=new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",signature.elements());
                    Invocation lookupCall=new Invocation(call.call(),owner,List.of(call.arguments().get(0),captured),call.result(),signature.path());
                    lookup=Local.of(new RequireNormal(Mechanisms.unknown(call,"lookup requires an existing member with this name and signature"),Optional.of(lookupCall)),Mechanisms.result(new Reflected(owner,call.arguments().get(0),captured,declared,call.call().site())));
                }
                effects.add(new Conditional(signature.path(),signature.gaps(),signature.dependencies(),lookup));
            }
            return Optional.of(lookupArrays.keeping(new Local(effects)));
        }
        if (!call.call().target().equals(INVOKE)) return Optional.empty();
        List<Gap> gaps = new ArrayList<>();
        if (!(call.receiver() instanceof Reflected reflected))
            return Optional.of(unresolved(call, List.of(Mechanisms.gap(call, GapKind.DYNAMIC_TARGET, "Method object has no verified lookup binding")), List.of()));
        List<Site> witnesses = List.of(reflected.lookup());
        if (!(reflected.declaringClass() instanceof ClassValue owner) || !owner.exact())
            gaps.add(Mechanisms.gap(call, GapKind.DYNAMIC_TARGET, "lookup class is not exact: " + reflected.declaringClass()));
        if (!(reflected.name() instanceof Literal name) || !(name.value() instanceof String))
            gaps.add(Mechanisms.gap(call, GapKind.INPUT_BINDING, "method name is not supplied"));
        ArrayBindings signatureArrays=array(reflected.parameterTypes(),bindings,call.path(),call.call().site());
        List<ArrayBinding> signatures=signatureArrays.values();
        ArrayBindings argumentArrays=array(call.arguments().get(1),bindings,call.path(),call.call().site());
        List<ArrayBinding> arguments=argumentArrays.values();
        if (signatures.isEmpty()) gaps.add(Mechanisms.gap(call, GapKind.INPUT_BINDING, "exact Class[] parameter signature is not supplied"));
        else if(signatures.stream().anyMatch(signature -> signature.elements().stream().anyMatch(a -> !(a instanceof ClassValue type) || !type.exact())))gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"parameter signature needs its actual Class values"));
        if (arguments.isEmpty()) gaps.add(Mechanisms.gap(call, GapKind.INPUT_BINDING, "same Object[] argument elements are not supplied"));
        if (!gaps.isEmpty()) return Optional.of(signatureArrays.keeping(argumentArrays.keeping(conditionalTargets(call,reflected,signatures,arguments,gaps,witnesses,program))));
        List<Effect> effects = new ArrayList<>();
        for (ArrayBinding signature : signatures) for (ArrayBinding original : arguments) for(ArrayBinding args:adapt(call,original,signature.elements(),bindings,effects)) {
            Optional<Path> path = signature.path().and(args.path());
            if (path.isEmpty()) continue;
            List<Gap> required = new ArrayList<>(signature.gaps()); required.addAll(args.gaps());
            Set<Integer> dependencies = new LinkedHashSet<>(signature.dependencies()); dependencies.addAll(args.dependencies());
            Local selected = invoke(call, reflected, signature.elements(), args.elements(), required, witnesses, program);
            effects.add(new Conditional(path.get(), List.copyOf(required), Set.copyOf(dependencies), selected));
            if (effects.size() > 64) {
                Gap limit = Mechanisms.gap(call, GapKind.BUDGET, "reflective array combination budget (64)");
                effects.add(new Conditional(call.path(), List.of(limit), Set.of(), unresolved(call,List.of(limit),witnesses)));
                return Optional.of(signatureArrays.keeping(argumentArrays.keeping(new Local(effects))));
            }
        }
        return Optional.of(signatureArrays.keeping(argumentArrays.keeping(new Local(effects))));
    }

    private Local conditionalTargets(Invocation call,Reflected reflected,List<ArrayBinding> signatures,List<ArrayBinding> arguments,List<Gap> missing,List<Site> witnesses,Program program) {
        if(!(reflected.declaringClass() instanceof ClassValue) && Values.location(reflected.declaringClass()).isEmpty())
            return unresolved(call,missing,witnesses);
        if(reflected.declaringClass() instanceof ClassValue type && !type.exact() && type.source().isEmpty() && type.descriptor().equals("Ljava/lang/Object;"))
            return unresolved(call,missing,witnesses);
        Query<List<Method>> members=targets.members(reflected.declaringClass(),reflected.declared());
        List<Effect> effects=new ArrayList<>();List<MemberChoices> families=new ArrayList<>();int count=0,examined=0;boolean omitted=false;
        Map<String,InputNeed> producers=new LinkedHashMap<>();Set<Gap> lookupFrontier=new LinkedHashSet<>();
        boolean unknownName=!(reflected.name() instanceof Literal l && l.value() instanceof String);
        Atom current=call.arguments().get(0);
        boolean produced=current instanceof ClassValue || current instanceof Reflected || current instanceof ConstructorValue
                || current instanceof ObjectValue object && object.exact() && object.defaultFields() && object.source().isEmpty();
        List<Method> ordered=members.value().orElseThrow();
        if(produced)ordered=ordered.stream().sorted(Comparator.comparing((Method method) -> method.isStatic() || !targets.priority(method.id()))).toList();
        candidates:for(Method method:ordered) {
            if(!unknownName && !method.id().name().equals(((Literal)reflected.name()).value()))continue;
            if(reflected.name() instanceof StringPrefix prefix && !method.id().name().startsWith(prefix.prefix()))continue;
            Atom receiver=call.arguments().get(0);
            if(!method.isStatic() && (receiver instanceof Unknown || receiver instanceof Truncated))continue;
            if(!method.isStatic() && (receiver instanceof Literal nil && nil.value()==null || compatible(receiver,"L"+method.id().owner()+";",program).match()==Match.INCOMPATIBLE))continue;
            List<String> descriptors=program.signature(method.id()).parameters().stream().map(ValueType::descriptor).toList();
            List<Atom> parameters=descriptors.stream().map(p -> (Atom)new ClassValue(p,true,Optional.empty(),program.scope(Values.type(p),method.id().loader()))).toList();
            List<ArrayBinding> matching=signatures.isEmpty()?List.of(new ArrayBinding(parameters,call.path(),List.of(),Set.of())):signatures.stream().filter(sig -> sig.elements().size()==parameters.size()
                    && java.util.stream.IntStream.range(0,parameters.size()).allMatch(i -> !(sig.elements().get(i) instanceof ClassValue actual) || !actual.exact() || actual.descriptor().equals(((ClassValue)parameters.get(i)).descriptor()))).toList();
            List<ArrayBinding> supplied=arguments.stream().filter(args -> args.elements().size()==parameters.size()
                    && java.util.stream.IntStream.range(0,parameters.size()).allMatch(i -> compatible(args.elements().get(i),descriptors.get(i),program,method.id().loader()).match()!=Match.INCOMPATIBLE)).toList();
            if(matching.isEmpty() || !arguments.isEmpty() && supplied.isEmpty())continue;
            if(examined++>=64){omitted=true;break;}
            List<MemberBinding> bindings=new ArrayList<>();
            for(MemberBinding binding:memberBindings(call,reflected,method,program)) {
                Query<Method> lookup=program.reflect(Values.type(binding.lookup().descriptor()),method.id().name(),descriptors,reflected.declared(),binding.lookup().loader());
                if(lookup.value().isPresent())bindings.add(binding);
                else if(!lookup.pending().isEmpty()) {
                    GapKind kind=lookup.pending().stream().anyMatch(issue -> issue.cause()==QueryCause.BUDGET)?GapKind.BUDGET:GapKind.MISSING_DEPENDENCY;
                    if(lookupFrontier.size()<64)lookupFrontier.add(Mechanisms.gap(call,kind,"candidate member lookup is unresolved: "+method.id()+" through "+binding.lookup().descriptor()+"; "+lookup.pending()));
                    else omitted=true;
                }
            }
            ArrayDeque<Local> variants=new ArrayDeque<>();
            methodVariants:for(ArrayBinding signature:matching) {
                List<ArrayBinding> tuples=arguments.isEmpty()?List.of(new ArrayBinding(java.util.stream.IntStream.range(0,parameters.size()).mapToObj(i -> argument(call.arguments().get(1),i,((ClassValue)parameters.get(i)).descriptor(),((ClassValue)parameters.get(i)).loader())).toList(),signature.path(),List.of(),Set.of())):supplied;
                for(ArrayBinding args:tuples) {
                    Optional<Path> path=signature.path().and(args.path());if(path.isEmpty())continue;
                    if(bindings.isEmpty()) {
                        producers.putIfAbsent(method.id().owner(),new InputNeed(receiver,Optional.empty(),NeedKind.RECEIVER_PRODUCER,"L"+method.id().owner()+";",List.of(),
                                "an actual receiver producer, constructor, factory, replacement return or compatible runtime subtype is required before selecting "+method.id()+"; the declaring type alone does not establish a concrete runtime object"));
                        continue;
                    }
                    for(MemberBinding binding:bindings) {
                        if(variants.size()>=64){omitted=true;break methodVariants;}
                        List<Gap> gaps=new ArrayList<>(signature.gaps());gaps.addAll(args.gaps());
                        Set<Integer> dependencies=new LinkedHashSet<>(signature.dependencies());dependencies.addAll(args.dependencies());
                        Reflected selected=new Reflected(binding.lookup(),new Literal(method.id().name()),new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",parameters),reflected.declared(),reflected.lookup());
                        List<Effect> candidate=new ArrayList<>();
                        if(unknownName)candidate.add(new Need(new InputNeed(reflected.name(),Optional.empty(),NeedKind.METHOD_NAME,"Ljava/lang/String;",List.of(new Literal(method.id().name())),"name required by "+method.id())));
                        if(!(reflected.declaringClass() instanceof ClassValue c && c.exact()))candidate.add(new Need(new InputNeed(reflected.declaringClass(),Optional.empty(),NeedKind.LOOKUP_TYPE,"Ljava/lang/Class;",List.of(selected.declaringClass()),"lookup Class required by "+method.id())));
                        binding.receiver().ifPresent(runtime -> candidate.add(new Need(new InputNeed(receiver,Optional.empty(),NeedKind.RECEIVER_TYPE,runtime.descriptor(),List.of(runtime),"runtime receiver required by "+method.id()))));
                        if(signatures.isEmpty() || signature.elements().stream().anyMatch(a -> !(a instanceof ClassValue type) || !type.exact()))candidate.add(new Need(new InputNeed(reflected.parameterTypes(),Optional.empty(),NeedKind.METHOD_TYPES,"[Ljava/lang/Class;",List.of(selected.parameterTypes()),"lookup signature required by "+method.id())));
                        if(arguments.isEmpty()) {
                            Atom array=call.arguments().get(1);
                            candidate.add(new Need(new InputNeed(array,Optional.empty(),NeedKind.ARGUMENTS,"[Ljava/lang/Object;",List.of(),"argument array type required by "+method.id())));
                            candidate.add(new Need(new InputNeed(array,Optional.of(new Length()),NeedKind.VALUE,"I",List.of(new Literal(parameters.size())),"argument count required by "+method.id())));
                            for(int i=0;i<parameters.size();i++)candidate.add(new Need(new InputNeed(array,Optional.of(new Index(i)),NeedKind.VALUE,((ClassValue)parameters.get(i)).descriptor(),List.of(),"argument type/value required by "+method.id())));
                        }
                        candidate.add(new Conditional(path.get(),List.copyOf(gaps),Set.copyOf(dependencies),Local.of(new Evaluate(call))));
                        variants.addLast(new Local(candidate));
                    }
                }
            }
            if(!variants.isEmpty()) {
                if(families.size()>=64){omitted=true;break candidates;}
                Optional<MemberFamily> batch=Mechanisms.impact(method.id())?Optional.of(new MemberFamily(method.id().owner(),method.id().name(),method.id().loader())):Optional.empty();
                families.add(new MemberChoices(batch,variants));
            }
        }
        ArrayDeque<MemberChoices> pending=new ArrayDeque<>(families);Map<MemberFamily,Integer> batches=new HashMap<>();int nextBatch=0;
        while(!pending.isEmpty() && count<64) {
            MemberChoices family=pending.removeFirst();int batch;
            if(family.batch().isEmpty())batch=nextBatch++;
            else {Integer known=batches.get(family.batch().get());if(known==null){batch=nextBatch++;batches.put(family.batch().get(),batch);}else batch=known;}
            effects.add(new Alternative(count++,batch,family.choices().removeFirst()));if(!family.choices().isEmpty())pending.addLast(family);
        }
        if(omitted || !pending.isEmpty())frontier(effects,List.of(Mechanisms.gap(call,GapKind.BUDGET,"conditional reflected target frontier (64)")),witnesses);
        if(!lookupFrontier.isEmpty())frontier(effects,List.copyOf(lookupFrontier),witnesses);
        for(InputNeed producer:producers.values()) {
            Gap gap=Mechanisms.gap(call,GapKind.INPUT_BINDING,producer.reason());
            effects.add(new Alternative(-1-effects.size(),Local.of(new Need(producer),
                    new Result(Value.of(new Unknown("receiver producer remains unresolved")).requiring(List.of(gap))),
                    new Observe(Kind.REFLECTION,"reflective member frontier requires an actual receiver producer: "+producer.descriptor(),witnesses,List.of(gap)))));
        }
        if(effects.isEmpty())effects.addAll(unresolved(call,missing,witnesses).effects());
        if(!members.pending().isEmpty())frontier(effects,Mechanisms.queryGaps(call,members),witnesses);
        if(unknownName && count==0)effects.add(new Need(new InputNeed(reflected.name(),Optional.empty(),NeedKind.METHOD_NAME,"Ljava/lang/String;",List.of(),"bind the name used by this lookup")));
        if(arguments.isEmpty() && count==0)effects.add(new Need(new InputNeed(call.arguments().get(1),Optional.empty(),NeedKind.ARGUMENTS,"[Ljava/lang/Object;",List.of(),"bind this invocation argument array")));
        return new Local(effects);
    }

    private static boolean serialized(Atom atom){return Values.source(atom).stream().flatMap(s -> s.path().stream()).anyMatch(s -> s instanceof Decoded);}
    private record MemberBinding(ClassValue lookup,Optional<ClassValue> receiver) {}
    private List<MemberBinding> memberBindings(Invocation call,Reflected reflected,Method method,Program program) {
        Optional<InputLocation> runtimeSource=Values.location(reflected.declaringClass()).filter(s -> !s.path().isEmpty() && s.path().get(s.path().size()-1) instanceof RuntimeClass);
        List<ClassValue> lookups;
        if(reflected.declaringClass() instanceof ClassValue exact && exact.exact())lookups=List.of(exact);
        else if(runtimeSource.isPresent()) {
            String upper=reflected.declaringClass() instanceof ClassValue type?Values.type(type.descriptor()):"java/lang/Object";
            lookups=runtimeTypes(upper,reflected.declaringClass() instanceof ClassValue type?type.loader():0,false,method.id().owner(),method.id().loader(),serialized(reflected.declaringClass()),program);
        } else {
            String owner=method.id().owner();int loader=method.id().loader();
            if(reflected.declaringClass() instanceof ClassValue type && program.assignable(Values.type(type.descriptor()),type.loader(),owner,loader).value().equals(Optional.of(true))){owner=Values.type(type.descriptor());loader=type.loader();}
            lookups=List.of(new ClassValue(owner.startsWith("[")?owner:"L"+owner+";",true,Optional.empty(),loader));
        }
        if(method.isStatic())return lookups.stream().limit(65).map(type -> new MemberBinding(type,Optional.empty())).toList();
        Atom receiver=call.arguments().get(0);
        if(!(receiver instanceof ObjectValue || receiver instanceof Symbolic || receiver instanceof ExternalValue || receiver instanceof UnboundValue))
            return lookups.stream().limit(65).map(type -> new MemberBinding(type,Optional.empty())).toList();
        String upper=runtimeType(receiver).orElse(receiver instanceof Symbolic symbolic?symbolic.type():"java/lang/Object");
        boolean exact=runtimeType(receiver).isPresent() && !(receiver instanceof ObjectValue object && !object.exact());
        List<ClassValue> receivers=runtimeTypes(upper,receiver instanceof ObjectValue object?object.loader():receiver instanceof Symbolic symbolic?symbolic.loader():0,exact,method.id().owner(),method.id().loader(),serialized(receiver),program);
        boolean same=runtimeSource.filter(source -> Values.location(receiver).equals(Optional.of(Values.parent(source)))).isPresent();
        List<MemberBinding> result=new ArrayList<>();
        if(same) {
            Map<Program.DefinedType,ClassValue> actuals=new HashMap<>();for(ClassValue actual:receivers)actuals.put(new Program.DefinedType(Values.type(actual.descriptor()),actual.loader()),actual);
            for(ClassValue lookup:lookups){ClassValue actual=actuals.get(new Program.DefinedType(Values.type(lookup.descriptor()),lookup.loader()));if(actual!=null){result.add(new MemberBinding(lookup,Optional.of(actual)));if(result.size()>=65)break;}}
        } else pairs:for(ClassValue lookup:lookups)for(ClassValue actual:receivers){result.add(new MemberBinding(lookup,Optional.of(actual)));if(result.size()>=65)break pairs;}
        return List.copyOf(result);
    }
    private List<ClassValue> runtimeTypes(String upper,int upperLoader,boolean exact,String owner,int ownerLoader,boolean serialized,Program program) {
        List<ClassInfo> scope=program.candidates();
        RuntimeView view=runtimes.filter(known -> known.scope()==scope).orElseGet(() -> {
            RuntimeView fresh=new RuntimeView(scope,new LinkedHashMap<>(16,.75f,true));runtimes=Optional.of(fresh);return fresh;
        });
        RuntimeQuery key=new RuntimeQuery(upper,upperLoader,exact,owner,ownerLoader,serialized);
        List<ClassValue> cached=view.values().get(key);if(cached!=null)return cached;
        Set<Program.DefinedType> candidates=new LinkedHashSet<>();candidates.add(new Program.DefinedType(upper,upperLoader));
        if(!exact){candidates.add(new Program.DefinedType(owner,ownerLoader));for(ClassInfo type:program.concreteTypes(owner,ownerLoader))candidates.add(new Program.DefinedType(type.name(),type.loader()));}
        List<ClassValue> result=new ArrayList<>();
        for(Program.DefinedType candidate:candidates) {
            String type=candidate.name();int loader=candidate.loader();
            if(!type.startsWith("[") && program.type(type,loader).filter(info -> (info.access() & (Opcodes.ACC_ABSTRACT|Opcodes.ACC_INTERFACE))==0).isEmpty())continue;
            Query<Boolean> member=program.assignable(type,loader,owner,ownerLoader),bound=program.assignable(type,loader,upper,upperLoader);
            if(member.value().equals(Optional.of(false)) && member.pending().isEmpty() || bound.value().equals(Optional.of(false)) && bound.pending().isEmpty())continue;
            if(serialized && !serializableRuntime(type,loader,program))continue;
            result.add(new ClassValue(type.startsWith("[")?type:"L"+type+";",true,Optional.empty(),loader));
        }
        List<ClassValue> values=List.copyOf(result);
        if(values.size()<=8192) {
            int retained=view.values().values().stream().mapToInt(List::size).sum();
            while(!view.values().isEmpty() && (view.values().size()>=64 || retained+values.size()>8192)) {
                RuntimeQuery oldest=view.values().keySet().iterator().next();retained-=view.values().remove(oldest).size();
            }
            view.values().put(key,values);
        }
        return values;
    }
    private static Atom tracked(Invocation call,int operand,String descriptor) {
        Atom value=call.arguments().get(operand);
        return value instanceof Unknown || value instanceof Truncated?new UnboundValue(call.result().id(),operand,descriptor,value):value;
    }
    private static Atom snapshot(Invocation call,Atom array) {
        return Values.source(array).<Atom>map(source -> new ExternalValue("[Ljava/lang/Class;",source)).orElse(array instanceof UnboundValue?array:new UnboundValue(call.result().id(),1,"[Ljava/lang/Class;",array));
    }
    private static boolean serializableRuntime(String type,int loader,Program program) {
        Query<Boolean> serializable=program.assignable(type,loader,"java/io/Serializable",0);
        return !serializable.value().equals(Optional.of(false)) || !serializable.pending().isEmpty();
    }
    private static Atom argument(Atom array,int index,String descriptor,int loader) {
        Optional<InputSource> source=Values.source(array).map(s -> s.at(new Index(index)));
        return descriptor.startsWith("L") || descriptor.startsWith("[")
                ? new Symbolic(Values.type(descriptor),"conditional argument slot "+index,source,loader)
                : source.<Atom>map(s -> new ExternalValue(descriptor,s)).orElseGet(() -> new Unknown("conditional argument slot "+index+": "+descriptor));
    }

    private Local invoke(Invocation call, Reflected reflected, List<Atom> signature, List<Atom> arguments,
                         List<Gap> required, List<Site> witnesses, Program program) {
        if (signature.stream().anyMatch(a -> !(a instanceof ClassValue c) || !c.exact()))
            return unresolved(call,List.of(Mechanisms.gap(call, GapKind.INPUT_BINDING,"parameter signature is not exact")),witnesses);
        String name = (String) ((Literal) reflected.name()).value();
        List<String> descriptors = signature.stream().map(a -> ((ClassValue)a).descriptor()).toList();
        Query<Method> query = program.reflect(Values.type(((ClassValue)reflected.declaringClass()).descriptor()), name, descriptors, reflected.declared(),((ClassValue)reflected.declaringClass()).loader());
        Optional<Method> target=query.value();
        if (target.isEmpty()) return unresolved(call,query.pending().isEmpty()?List.of(Mechanisms.gap(call,GapKind.DYNAMIC_TARGET,"no matching reflected method: " + name + descriptors)):Mechanisms.queryGaps(call,query),witnesses);
        if(!sameSignature(target.orElseThrow().id(),signature,program))return Local.of(new Raise("java/lang/NoSuchMethodException"));
        if (arguments.size()!=descriptors.size()) return Local.of(new Raise("java/lang/IllegalArgumentException"));
        List<Gap> gaps = new ArrayList<>(required); gaps.addAll(Mechanisms.queryGaps(call,query));
        for (int i=0;i<descriptors.size();i++) {
            Compatibility compatibility=compatible(arguments.get(i),descriptors.get(i),program,target.get().id().loader());
            gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),compatibility.pending())));
            if (compatibility.match()==Match.INCOMPATIBLE) return Local.of(new Raise("java/lang/IllegalArgumentException"));
            if (compatibility.match()==Match.UNKNOWN) gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"reflective argument type at slot " + i + " is not established"));
        }
        Atom receiver=call.arguments().get(0);
        Method selected=target.get();
        if (!selected.isStatic()) {
            if (receiver instanceof Literal literal && literal.value()==null) return Local.of(new Raise("java/lang/NullPointerException"));
            Compatibility receiverMatch=compatible(receiver,"L"+selected.id().owner()+";",program,selected.id().loader());
            if(receiverMatch.match()==Match.INCOMPATIBLE)return Local.of(new Raise("java/lang/IllegalArgumentException"));
            gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),receiverMatch.pending())));
            if(receiverMatch.match()==Match.UNKNOWN)gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"reflective receiver compatibility is not established"));
            if (!(receiver instanceof ProxyValue) && !(receiver instanceof LambdaValue)) {
                Optional<String> receiverType=runtimeType(receiver);
                if (receiverType.isEmpty()) gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"reflective receiver type is unspecified"));
                if (receiver instanceof ObjectValue object && !object.exact())
                    gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"reflective receiver runtime type is unspecified"));
                if (receiver instanceof ObjectValue object && !object.exact() && !program.assignable(object.type(),object.loader(),selected.id().owner(),selected.id().loader()).value().equals(Optional.of(true))) {
                    receiver=new ObjectValue(object.id(),selected.id().owner(),false,object.origin(),object.defaultFields(),object.source(),selected.id().loader());receiverType=Optional.of(selected.id().owner());
                }
                if (receiverType.isPresent()) {
                    Query<Method> actual=program.lookup(program.method(receiverType.get(),selected.id().name(),selected.id().descriptor(),receiver instanceof ObjectValue object?object.loader():0));
                    gaps.addAll(Mechanisms.queryGaps(call,actual));selected=actual.value().orElse(selected);
                }
            }
        }
        if (!selected.isPublic()) gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"non-public reflective access has not been established"));
        // Access is checked against the lookup member, before virtual dispatch to an override.
        // A public superclass/interface Method may legally dispatch to a nonpublic implementation.
        String declaring=target.get().id().owner(),caller=call.call().site().method().owner();
        if(program.type(declaring,target.get().id().loader()).map(c -> (c.access() & Opcodes.ACC_PUBLIC)==0).orElse(false)
                && !declaring.substring(0,Math.max(0,declaring.lastIndexOf('/'))).equals(caller.substring(0,Math.max(0,caller.lastIndexOf('/')))))
            gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"reflective access to the non-public declaring class has not been established: "+declaring));
        return Local.of(new Dispatch(selected.id(),receiver,arguments,Kind.REFLECTION,gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,witnesses,List.copyOf(gaps),ReturnFlow.TO_RESULT,ExceptionFlow.REFLECTED),
                new Observe(Kind.REFLECTION,"resolved reflective target " + selected.id(),witnesses,List.copyOf(gaps)));
    }

    private static Local unresolved(Invocation call,List<Gap> gaps,List<Site> witnesses) {
        return Local.of(Mechanisms.result(new Unknown("unresolved reflective target")),
                new Observe(Kind.REFLECTION,"generic Method.invoke; target requires concrete object and value bindings",witnesses,List.copyOf(gaps)));
    }
    private static void frontier(List<Effect> effects,List<Gap> gaps,List<Site> witnesses) {
        effects.add(new Observe(Kind.REFLECTION,"unresolved reflective target frontier",witnesses,gaps));
        // An unexplored target cannot also be the return value of a selected known target.
        effects.add(new Alternative(-1-effects.size(),Local.of(new Result(Value.of(new Unknown("unresolved reflective target")).requiring(gaps)))));
    }

}
