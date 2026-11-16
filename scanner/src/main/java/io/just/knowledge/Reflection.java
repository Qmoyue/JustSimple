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
    private static final Field OVERRIDE=new Field(new FieldId("java/lang/reflect/AccessibleObject","override","Z"));

    @Override public Optional<Local> apply(Invocation call, Bindings bindings, Program program) {
        if(call.is("java/lang/Class","getName","()Ljava/lang/String;") && call.receiver() instanceof ClassValue type) {
            if(!type.exact())return Optional.of(Local.of(new Result(Value.of(new Unknown("runtime Class name is unspecified")).requiring(Mechanisms.unknown(call,"Class.getName requires the actual runtime Class")))));
            String descriptor=type.descriptor();
            String name=switch(descriptor){case "Z" -> "boolean";case "B" -> "byte";case "C" -> "char";case "S" -> "short";case "I" -> "int";case "J" -> "long";case "F" -> "float";case "D" -> "double";case "V" -> "void";default -> descriptor.startsWith("L")?descriptor.substring(1,descriptor.length()-1).replace('/','.'):descriptor.replace('/','.');};
            return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new Literal(name))));
        }
        if(call.is("java/lang/Class","getInterfaces","()[Ljava/lang/Class;") && platformClass(call,program)) {
            if(!(call.receiver() instanceof ClassValue owner) || !owner.exact())
                return Optional.of(Local.of(new Result(Value.of(new Unknown("interface collection class is unspecified")).requiring(Mechanisms.unknown(call,"interface collection requires the actual Class")))));
            List<String> names;List<Gap> pending=new ArrayList<>();String descriptor=owner.descriptor();int loader=owner.loader();
            if(descriptor.startsWith("["))names=List.of("java/lang/Cloneable","java/io/Serializable");
            else if(descriptor.length()==1)names=List.of();
            else {
                Query<ClassInfo> type=program.definition(Values.type(descriptor),loader);pending.addAll(Mechanisms.queryGaps(call,type));
                if(type.value().isEmpty())return Optional.of(Local.of(new Result(Value.of(new Unknown("interface collection declaration is missing")).requiring(pending))));
                names=type.value().orElseThrow().interfaces();
                for(String name:names)pending.addAll(Mechanisms.queryGaps(call,program.definition(name,loader)));
            }
            ObjectValue array=new ObjectValue(call.result().id(),"[Ljava/lang/Class;",true,"Class.getInterfaces result");
            List<Effect> effects=new ArrayList<>();effects.add(new RequireNormal(pending));
            effects.add(new Write(array,new Length(),Value.of(new Literal(names.size())).requiring(pending)));
            for(int i=0;i<names.size();i++) {
                String name=names.get(i);effects.add(new Write(array,new Index(i),Value.of(new ClassValue("L"+name+";",true,Optional.empty(),program.scope(name,loader))).requiring(pending)));
            }
            effects.add(new Result(Value.of(array).requiring(pending)));return Optional.of(new Local(effects));
        }
        if((call.is("java/lang/Class","getClasses","()[Ljava/lang/Class;") || call.is("java/lang/Class","getDeclaredClasses","()[Ljava/lang/Class;"))
                && platformClass(call,program) && call.receiver() instanceof ClassValue owner && owner.exact()) {
            boolean declared=call.call().target().name().equals("getDeclaredClasses");
            Query<List<DefinedType>> query=program.memberClasses(Values.type(owner.descriptor()),declared,owner.loader(),Math.max(256,bindings.alternatives()));
            List<Gap> pending=Mechanisms.queryGaps(call,query);List<DefinedType> members=query.value().orElseThrow();
            ObjectValue array=new ObjectValue(call.result().id(),"[Ljava/lang/Class;",true,"reflected member class collection",false);
            Atom length=pending.isEmpty()?new Literal(members.size()):new Unknown("member class count is incomplete");
            List<Effect> effects=new ArrayList<>();effects.add(new RequireNormal(pending));effects.add(new Write(array,new Length(),Value.of(length).requiring(pending)));
            Set<Bound> values=new LinkedHashSet<>();
            for(DefinedType member:members)values.add(new Bound(new ClassValue("L"+member.name()+";",true,Optional.empty(),member.loader()),call.path()));
            if(!pending.isEmpty())values.add(new Bound(new Unknown("member class collection is incomplete"),call.path()));
            if(!values.isEmpty()) {
                List<Gap> order=new ArrayList<>(pending);order.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"reflection member class array order is unspecified"));
                effects.add(new Write(array,new Wildcard(),new Value(values).requiring(order)));
            }
            effects.add(new Result(Value.of(array).requiring(pending)));return Optional.of(new Local(effects));
        }
        if((call.is("java/lang/Class","getDeclaredFields","()[Ljava/lang/reflect/Field;") || call.is("java/lang/Class","getFields","()[Ljava/lang/reflect/Field;"))
                && platformClass(call,program) && call.receiver() instanceof ClassValue owner && owner.exact()) {
            boolean declared=call.call().target().name().equals("getDeclaredFields");String type=Values.type(owner.descriptor());
            Query<List<FieldInfo>> query=program.reflectiveFields(type,declared,owner.loader(),Math.max(256,bindings.alternatives()));
            List<Gap> pending=new ArrayList<>(Mechanisms.queryGaps(call,query));List<FieldInfo> fields=query.value().orElseThrow();
            boolean platform=owner.descriptor().startsWith("L") && program.type(type,owner.loader()).filter(info -> info.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()
                    || fields.stream().anyMatch(field -> program.type(field.id().owner(),field.id().loader()).filter(info -> info.role()==io.just.input.Inputs.Role.PLATFORM).isPresent());
            if(platform)pending.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"platform reflection field filtering depends on the target runtime"));
            ObjectValue array=new ObjectValue(call.result().id(),"[Ljava/lang/reflect/Field;",true,"reflected field collection",false);
            Atom length=pending.isEmpty()?new Literal(fields.size()):new Unknown("reflected field count is incomplete");
            List<Effect> effects=new ArrayList<>();effects.add(new RequireNormal(pending));effects.add(new Write(array,new Length(),Value.of(length).requiring(pending)));
            Set<Bound> members=new LinkedHashSet<>();int limit=bindings.alternatives();
            for(FieldInfo field:fields) {
                if(members.size()>=limit)break;
                members.add(new Bound(new ReflectedField(field.id(),field.access()),call.path()));
            }
            if(!members.isEmpty()) {
                List<Gap> order=new ArrayList<>(pending);order.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"reflection field array order is unspecified"));
                effects.add(new Write(array,new Wildcard(),new Value(members).requiring(order)));
            }
            if(members.size()<fields.size())effects.add(new Observe(Kind.REFLECTION,"field collection member frontier",List.of(call.call().site()),List.of(Mechanisms.gap(call,GapKind.BUDGET,"field metadata member budget ("+limit+")"))));
            effects.add(new Result(Value.of(array).requiring(pending)));return Optional.of(new Local(effects));
        }
        if(call.receiver() instanceof ReflectedField field && program.type("java/lang/reflect/Field").filter(info -> info.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()) {
            if(call.is("java/lang/reflect/Field","getName","()Ljava/lang/String;"))return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new Literal(field.field().name()))));
            if(call.is("java/lang/reflect/Field","getModifiers","()I"))return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new Literal(field.access()))));
            if(call.is("java/lang/reflect/Field","getType","()Ljava/lang/Class;"))return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new ClassValue(field.field().descriptor(),true,Optional.empty(),program.scope(Values.type(field.field().descriptor()),field.field().loader())))));
            if(call.is("java/lang/reflect/Field","getDeclaringClass","()Ljava/lang/Class;"))return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new ClassValue("L"+field.field().owner()+";",true,Optional.empty(),field.field().loader()))));
        }
        if(call.is("java/lang/Class","cast","(Ljava/lang/Object;)Ljava/lang/Object;") && platformClass(call,program) && call.receiver() instanceof ClassValue owner && owner.exact()) {
            Atom value=call.arguments().get(0);
            if(value instanceof Literal literal && literal.value()==null)return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(value)));
            if(owner.descriptor().length()>1) {
                Compatibility match=compatible(value,owner.descriptor(),program,owner.loader());
                if(match.match()==Match.INCOMPATIBLE)return Optional.of(Local.of(new Raise("java/lang/ClassCastException")));
                if(match.match()==Match.COMPATIBLE) {
                    List<Gap> pending=Mechanisms.queryGaps(call,new Query<>(Optional.empty(),match.pending()));
                    return Optional.of(Local.of(new RequireNormal(pending),new Result(Value.of(value).requiring(pending))));
                }
            }
        }
        if((call.is("java/lang/Class","getDeclaredField","(Ljava/lang/String;)Ljava/lang/reflect/Field;") || call.is("java/lang/Class","getField","(Ljava/lang/String;)Ljava/lang/reflect/Field;"))
                && platformClass(call,program) && call.receiver() instanceof ClassValue owner && owner.exact()) {
            boolean declared=call.call().target().name().equals("getDeclaredField");
            Atom name=call.arguments().get(0);
            if(name instanceof Literal literal && literal.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if(name instanceof Literal literal && literal.value() instanceof String text) {
                if(!owner.descriptor().startsWith("L"))return Optional.of(Local.of(new Raise("java/lang/NoSuchFieldException")));
                String type=Values.type(owner.descriptor());Query<ClassInfo> definition=program.definition(type,owner.loader());
                if(definition.value().isEmpty()) {
                    List<Gap> pending=Mechanisms.queryGaps(call,definition);
                    return Optional.of(Local.of(new RequireNormal(pending),new Result(Value.of(new Unknown("field declaration is missing")).requiring(pending))));
                }
                List<FieldInfo> found=program.fields(type,owner.loader()).stream().filter(field -> field.id().name().equals(text) && (declared || (field.access() & Opcodes.ACC_PUBLIC)!=0)).toList();
                if(found.isEmpty()) {
                    if(declared)return Optional.of(Local.of(new Raise("java/lang/NoSuchFieldException")));
                    return Optional.empty(); // Public fields can also be inherited.
                }
                if(found.size()!=1)return Optional.empty();
                ObjectValue field=new ObjectValue(call.result().id(),"java/lang/reflect/Field",true,"declared field metadata",false);
                FieldInfo target=found.get(0);
                return Optional.of(Local.of(new RequireNormal(List.of()),new Write(field,OVERRIDE,Value.of(new Literal(0))),
                        new Write(field,new FieldTarget(),Value.of(new ReflectedField(target.id(),target.access()))),Mechanisms.result(field)));
            }
        }
        if(call.receiver() instanceof ObjectValue field && field.type().equals("java/lang/reflect/Field")
                && Set.of("java/lang/reflect/Field","java/lang/reflect/AccessibleObject").contains(call.call().target().owner())
                && program.lookup(call.call().target()).value().flatMap(method -> program.type(method.id().owner(),method.id().loader())).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()) {
            if(call.is("java/lang/reflect/Field","getBoolean","(Ljava/lang/Object;)Z")) {
                List<Effect> choices=new ArrayList<>();boolean complete=true;
                for(Bound binding:bindings.read(field,new FieldTarget()).under(call.path()).alternatives()) {
                    if(!(binding.atom() instanceof ReflectedField target)){complete=false;break;}
                    FieldId id=target.field();int required=Opcodes.ACC_PUBLIC|Opcodes.ACC_STATIC|Opcodes.ACC_FINAL;
                    if(!id.descriptor().equals("Z") || (target.access() & required)!=required
                            || program.type(id.owner(),id.loader()).filter(type -> (type.access() & Opcodes.ACC_PUBLIC)!=0).isEmpty()
                            || program.declared(new MethodId(id.owner(),"<clinit>","()V",id.loader())).isPresent()){complete=false;break;}
                    Optional<JvmConstant> constant=program.fieldConstant(id);
                    if(constant.isPresent() && constant.get() instanceof LiteralConstant value && value.value() instanceof Integer number)
                        choices.add(new Conditional(binding.path(),binding.gaps(),binding.dependencies(),Local.of(new Initialize(id.owner(),id.loader()),new RequireNormal(List.of()),Mechanisms.result(new Literal(number)))));
                    else {complete=false;break;}
                }
                if(complete && !choices.isEmpty())return Optional.of(new Local(choices).onModelState());
            }
            Value access=bindings.read(field,OVERRIDE).under(call.path());
            if(call.is("java/lang/reflect/Field","set","(Ljava/lang/Object;Ljava/lang/Object;)V") && !access.empty()) {
                Optional<Local> write=fieldWrite(call,field,access,bindings,program);if(write.isPresent())return write;
            }
            if(!access.empty() && call.call().target().name().equals("isAccessible") && call.call().target().descriptor().equals("()Z"))
                return Optional.of(Local.of(new RequireNormal(List.of()),new Result(access)));
            if(!access.empty() && call.call().target().name().equals("setAccessible") && call.call().target().descriptor().equals("(Z)V"))
                return Optional.of(Local.of(new RequireNormal(List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"access suppression requires the target platform permission and module policy"))),
                        new Write(field,OVERRIDE,Value.of(call.arguments().get(0))),new Result(Value.NULL)));
        }
        if (call.receiver() instanceof Reflected method) {
            if(method.object()>=0 && Set.of("java/lang/reflect/Method","java/lang/reflect/AccessibleObject").contains(call.call().target().owner())) {
                if(call.call().target().name().equals("setAccessible") && call.call().target().descriptor().equals("(Z)V"))
                    return Optional.of(Local.of(new RequireNormal(List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"access suppression requires the target platform permission and module policy"))),
                            new Write(metadataObject(method),new MethodAccess(method.member()),Value.of(call.arguments().get(0))),new Result(Value.NULL)));
                if(call.call().target().name().equals("isAccessible") && call.call().target().descriptor().equals("()Z"))
                    return Optional.of(Local.of(new RequireNormal(List.of()),new Result(bindings.read(metadataObject(method),new MethodAccess(method.member())).under(call.path()))));
            }
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
                    : call.receiver() instanceof ProxyValue proxy ? new ClassValue("Ljava/lang/reflect/Proxy;",false,Optional.of(new ValueSource(call.result().id(),0,proxy,List.of())),0)
                    : call.receiver() instanceof Literal literal && literal.value() instanceof String
                    ? new ClassValue("Ljava/lang/String;", true) : new Unknown("runtime class is unspecified");
            return Optional.of(Local.of(new RequireNormal(call.receiver() instanceof ObjectValue object && !object.exact()?Mechanisms.unknown(call,"getClass requires a nonnull receiver"):List.of()),Mechanisms.result(value)));
        }
        if(call.is("java/lang/Class","getMethods","()[Ljava/lang/reflect/Method;") || call.is("java/lang/Class","getDeclaredMethods","()[Ljava/lang/reflect/Method;")) {
            if(!(call.receiver() instanceof ClassValue owner) || !owner.exact())return Optional.of(Local.of(new Result(Value.of(new Unknown("method collection class is unspecified")).requiring(Mechanisms.unknown(call,"method collection requires the declaring Class")))));
            boolean declared=call.call().target().name().equals("getDeclaredMethods");Query<List<Method>> query=program.methods(Values.type(owner.descriptor()),declared,owner.loader());
            List<Atom> values=new ArrayList<>();List<Effect> effects=new ArrayList<>();
            for(Method method:query.value().orElse(List.of())) {
                List<Atom> signature=program.signature(method.id()).parameters().stream().map(t -> (Atom)new ClassValue(t.descriptor(),true,Optional.empty(),program.scope(Values.type(t.descriptor()),method.id().loader()))).toList();
                Reflected value=new Reflected(new ClassValue("L"+method.id().owner()+";",true,Optional.empty(),method.id().loader()),new Literal(method.id().name()),new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",signature),declared,call.call().site(),call.result().id(),values.size());
                values.add(value);effects.add(initialAccess(value));
            }
            List<Gap> pending=Mechanisms.queryGaps(call,query),conditions=new ArrayList<>(pending);
            conditions.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"reflection method array order is unspecified"));
            ArrayValue snapshot=new ArrayValue(call.result().id(),ArrayRole.METHOD_COLLECTION,"[Ljava/lang/reflect/Method;",values,ArrayOrder.UNSPECIFIED,
                    query.pending().isEmpty()?ArrayExtent.EXACT:ArrayExtent.UNKNOWN,conditions);
            effects.add(0,new RequireNormal(pending));effects.add(new Result(Value.of(snapshot).requiring(pending)));return Optional.of(new Local(effects));
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
                Reflected result=new Reflected(call.receiver(),call.arguments().get(0),captured,declared,call.call().site(),call.result().id(),0);
                return Optional.of(lookupArrays.keeping(Local.of(new RequireNormal(Mechanisms.unknown(call,"lookup requires an existing member with this name and signature"),Optional.of(lookupCall)),initialAccess(result),Mechanisms.result(result))));
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
                        Reflected result=new Reflected(owner,call.arguments().get(0),new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",signature.elements()),declared,call.call().site(),call.result().id(),0);
                        lookup=Local.of(new RequireNormal(Mechanisms.queryGaps(call,query)),initialAccess(result),new Result(Value.of(result).requiring(Mechanisms.queryGaps(call,query))));
                    }
                } else {
                    ArrayValue captured=new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",signature.elements());
                    Invocation lookupCall=new Invocation(call.call(),owner,List.of(call.arguments().get(0),captured),call.result(),signature.path());
                    Reflected result=new Reflected(owner,call.arguments().get(0),captured,declared,call.call().site(),call.result().id(),0);
                    lookup=Local.of(new RequireNormal(Mechanisms.unknown(call,"lookup requires an existing member with this name and signature"),Optional.of(lookupCall)),initialAccess(result),Mechanisms.result(result));
                }
                effects.add(new Conditional(signature.path(),signature.gaps(),signature.dependencies(),lookup));
            }
            return Optional.of(lookupArrays.keeping(new Local(effects)));
        }
        if (!call.call().target().equals(INVOKE)) return Optional.empty();
        List<Gap> gaps = new ArrayList<>();
        if (!(call.receiver() instanceof Reflected reflected))
            return Optional.of(unresolved(call, List.of(Mechanisms.gap(call, GapKind.DYNAMIC_TARGET, "Method object has no verified lookup binding")), List.of()));
        Value access=reflected.object()>=0?bindings.read(metadataObject(reflected),new MethodAccess(reflected.member())).under(call.path())
                :Value.of(new Unknown("method access override is unspecified"),call.path());
        if(access.empty())return Optional.of(Local.of(new Result(Value.BOTTOM)));
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
        if (!gaps.isEmpty()) return Optional.of(signatureArrays.keeping(argumentArrays.keeping(conditionalTargets(call,reflected,signatures,arguments,gaps,witnesses,program,bindings.alternatives()))));
        List<Effect> effects = new ArrayList<>();
        int combinations=0;
        for (ArrayBinding signature : signatures) for (ArrayBinding original : arguments) for(ArrayBinding args:adapt(call,original,signature.elements(),bindings,effects)) {
            Optional<Path> path = signature.path().and(args.path());
            if (path.isEmpty()) continue;
            for(Bound flag:access.under(path.get()).alternatives()) {
            if (combinations++ >= bindings.alternatives()) {
                Gap limit = Mechanisms.gap(call, GapKind.BUDGET, "reflective array combination budget ("+bindings.alternatives()+")");
                effects.add(new Conditional(call.path(), List.of(limit), Set.of(), unresolved(call,List.of(limit),witnesses)));
                return Optional.of(signatureArrays.keeping(argumentArrays.keeping(new Local(effects))));
            }
            List<Gap> required = new ArrayList<>(signature.gaps()); required.addAll(args.gaps());required.addAll(flag.gaps());
            Set<Integer> dependencies = new LinkedHashSet<>(signature.dependencies()); dependencies.addAll(args.dependencies());dependencies.addAll(flag.dependencies());
            boolean known=flag.atom() instanceof Literal literal && (literal.value() instanceof Number || literal.value() instanceof Boolean);
            boolean override=known && flag.atom() instanceof Literal literal && (Boolean.TRUE.equals(literal.value()) || literal.value() instanceof Number number && number.intValue()!=0);
            Local selected = invoke(call, reflected, signature.elements(), args.elements(), required, witnesses, program,known,override);
            effects.add(new Conditional(flag.path(), List.copyOf(required), Set.copyOf(dependencies), selected));
            }
        }
        return Optional.of(signatureArrays.keeping(argumentArrays.keeping(new Local(effects))));
    }

    private Optional<Local> fieldWrite(Invocation call,ObjectValue field,Value access,Bindings bindings,Program program) {
        Value targets=bindings.read(field,new FieldTarget()).under(call.path());if(targets.empty())return Optional.empty();
        List<Effect> choices=new ArrayList<>();
        for(Bound target:targets.alternatives())for(Bound flag:access.under(target.path()).alternatives()) {
            if(!(target.atom() instanceof ReflectedField metadata) || !(flag.atom() instanceof Literal literal))return Optional.empty();
            boolean override=Boolean.TRUE.equals(literal.value()) || literal.value() instanceof Number number && number.intValue()!=0;
            if(!(literal.value() instanceof Boolean || literal.value() instanceof Number))return Optional.empty();
            FieldId id=metadata.field();if((metadata.access() & (Opcodes.ACC_STATIC|Opcodes.ACC_FINAL))!=0)return Optional.empty();
            Optional<ClassInfo> owner=program.type(id.owner(),id.loader());if(owner.isEmpty())return Optional.empty();
            Query<Boolean> allowed=fieldAccess(metadata,call.call().site().method(),owner.orElseThrow(),program);
            if(!override && (allowed.value().isEmpty() || !allowed.pending().isEmpty()))return Optional.empty();
            List<Gap> gaps=new ArrayList<>(target.gaps());gaps.addAll(flag.gaps());Set<Integer> dependencies=new LinkedHashSet<>(target.dependencies());dependencies.addAll(flag.dependencies());
            if(!override && allowed.value().equals(Optional.of(false))) {
                choices.add(new Conditional(flag.path(),gaps,dependencies,Local.of(new Raise("java/lang/IllegalAccessException"))));continue;
            }
            Atom receiver=call.arguments().get(0);
            if(receiver instanceof Literal nil && nil.value()==null) {
                choices.add(new Conditional(flag.path(),gaps,dependencies,Local.of(new Raise("java/lang/NullPointerException"))));continue;
            }
            if(!(receiver instanceof ObjectValue instance))return Optional.empty();
            Compatibility receiverMatch=compatible(instance,"L"+id.owner()+";",program,id.loader());
            if(receiverMatch.match()==Match.INCOMPATIBLE) {
                choices.add(new Conditional(flag.path(),gaps,dependencies,Local.of(new Raise("java/lang/IllegalArgumentException"))));continue;
            }
            List<Gap> normal=new ArrayList<>(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),receiverMatch.pending())));
            if(!instance.exact() || receiverMatch.match()==Match.UNKNOWN)normal.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"reflective field receiver must be nonnull and compatible"));
            gaps.addAll(normal);
            ArrayBinding input=new ArrayBinding(List.of(call.arguments().get(1)),flag.path(),List.copyOf(gaps),Set.copyOf(dependencies));
            List<Effect> failures=new ArrayList<>();
            for(ArrayBinding value:adapt(call,input,List.of(new ClassValue(id.descriptor(),true,Optional.empty(),program.scope(Values.type(id.descriptor()),id.loader()))),bindings,failures)) {
                Atom content=value.elements().get(0);Compatibility match=compatible(content,id.descriptor(),program,id.loader());
                List<Gap> required=new ArrayList<>(value.gaps());required.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),match.pending())));
                Local write;
                if(match.match()==Match.INCOMPATIBLE)write=Local.of(new Raise("java/lang/IllegalArgumentException"));
                else {
                    List<Gap> completion=new ArrayList<>(normal);
                    if(match.match()==Match.UNKNOWN) {Gap pending=Mechanisms.gap(call,GapKind.INPUT_BINDING,"reflective field value must be assignable");required.add(pending);completion.add(pending);}
                    write=Local.of(new RequireNormal(completion),new Write(instance,new Field(id),Value.of(content,value.path()).requiring(required).tracing(value.dependencies())),new Result(Value.NULL));
                }
                choices.add(new Conditional(value.path(),required,value.dependencies(),write));
            }
            choices.addAll(failures);
        }
        return choices.isEmpty()?Optional.empty():Optional.of(new Local(choices).onModelState());
    }

    private Query<Boolean> fieldAccess(ReflectedField field,MethodId caller,ClassInfo owner,Program program) {
        String name=owner.name(),from=caller.owner();
        boolean samePackage=caller.loader()==owner.loader() && name.substring(0,Math.max(0,name.lastIndexOf('/'))).equals(from.substring(0,Math.max(0,from.lastIndexOf('/'))));
        if((owner.access() & Opcodes.ACC_PUBLIC)==0 && !samePackage)return new Query<>(Optional.of(false),List.of());
        if((field.access() & Opcodes.ACC_PRIVATE)!=0)return program.nestmates(from,caller.loader(),name,owner.loader());
        if((field.access() & Opcodes.ACC_PUBLIC)!=0 || samePackage)return new Query<>(Optional.of(true),List.of());
        return (field.access() & Opcodes.ACC_PROTECTED)!=0?new Query<>(Optional.empty(),List.of()):new Query<>(Optional.of(false),List.of());
    }

    private Local conditionalTargets(Invocation call,Reflected reflected,List<ArrayBinding> signatures,List<ArrayBinding> arguments,List<Gap> missing,List<Site> witnesses,Program program,int limit) {
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
            if(examined++>=limit){omitted=true;break;}
            List<MemberBinding> bindings=new ArrayList<>();
            for(MemberBinding binding:memberBindings(call,reflected,method,program,limit)) {
                Query<Method> lookup=program.reflect(Values.type(binding.lookup().descriptor()),method.id().name(),descriptors,reflected.declared(),binding.lookup().loader());
                if(lookup.value().isPresent())bindings.add(binding);
                else if(!lookup.pending().isEmpty()) {
                    GapKind kind=lookup.pending().stream().anyMatch(issue -> issue.cause()==QueryCause.BUDGET)?GapKind.BUDGET:GapKind.MISSING_DEPENDENCY;
                    if(lookupFrontier.size()<limit)lookupFrontier.add(Mechanisms.gap(call,kind,"candidate member lookup is unresolved: "+method.id()+" through "+binding.lookup().descriptor()+"; "+lookup.pending()));
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
                        if(variants.size()>=limit){omitted=true;break methodVariants;}
                        List<Gap> gaps=new ArrayList<>(signature.gaps());gaps.addAll(args.gaps());
                        Set<Integer> dependencies=new LinkedHashSet<>(signature.dependencies());dependencies.addAll(args.dependencies());
                        Reflected selected=new Reflected(binding.lookup(),new Literal(method.id().name()),new ArrayValue(call.result().id(),ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",parameters),reflected.declared(),reflected.lookup(),reflected.object(),reflected.member());
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
                if(families.size()>=limit){omitted=true;break candidates;}
                Optional<MemberFamily> batch=Mechanisms.impact(method.id())?Optional.of(new MemberFamily(method.id().owner(),method.id().name(),method.id().loader())):Optional.empty();
                families.add(new MemberChoices(batch,variants));
            }
        }
        ArrayDeque<MemberChoices> pending=new ArrayDeque<>(families);Map<MemberFamily,Integer> batches=new HashMap<>();int nextBatch=0;
        while(!pending.isEmpty() && count<limit) {
            MemberChoices family=pending.removeFirst();int batch;
            if(family.batch().isEmpty())batch=nextBatch++;
            else {Integer known=batches.get(family.batch().get());if(known==null){batch=nextBatch++;batches.put(family.batch().get(),batch);}else batch=known;}
            effects.add(new Alternative(count++,batch,family.choices().removeFirst()));if(!family.choices().isEmpty())pending.addLast(family);
        }
        if(omitted || !pending.isEmpty())frontier(effects,List.of(Mechanisms.gap(call,GapKind.BUDGET,"conditional reflected target frontier ("+limit+")")),witnesses);
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
    private List<MemberBinding> memberBindings(Invocation call,Reflected reflected,Method method,Program program,int limit) {
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
        if(method.isStatic())return lookups.stream().limit((long)limit+1).map(type -> new MemberBinding(type,Optional.empty())).toList();
        Atom receiver=call.arguments().get(0);
        if(!(receiver instanceof ObjectValue || receiver instanceof Symbolic || receiver instanceof ExternalValue || receiver instanceof UnboundValue))
            return lookups.stream().limit((long)limit+1).map(type -> new MemberBinding(type,Optional.empty())).toList();
        String upper=runtimeType(receiver).orElse(receiver instanceof Symbolic symbolic?symbolic.type():"java/lang/Object");
        boolean exact=runtimeType(receiver).isPresent() && !(receiver instanceof ObjectValue object && !object.exact());
        List<ClassValue> receivers=runtimeTypes(upper,receiver instanceof ObjectValue object?object.loader():receiver instanceof Symbolic symbolic?symbolic.loader():0,exact,method.id().owner(),method.id().loader(),serialized(receiver),program);
        boolean same=runtimeSource.filter(source -> Values.location(receiver).equals(Optional.of(Values.parent(source)))).isPresent();
        List<MemberBinding> result=new ArrayList<>();
        if(same) {
            Map<Program.DefinedType,ClassValue> actuals=new HashMap<>();for(ClassValue actual:receivers)actuals.put(new Program.DefinedType(Values.type(actual.descriptor()),actual.loader()),actual);
            for(ClassValue lookup:lookups){ClassValue actual=actuals.get(new Program.DefinedType(Values.type(lookup.descriptor()),lookup.loader()));if(actual!=null){result.add(new MemberBinding(lookup,Optional.of(actual)));if(result.size()>limit)break;}}
        } else pairs:for(ClassValue lookup:lookups)for(ClassValue actual:receivers){result.add(new MemberBinding(lookup,Optional.of(actual)));if(result.size()>limit)break pairs;}
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
                         List<Gap> required, List<Site> witnesses, Program program,boolean accessKnown,boolean override) {
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
        Optional<ClassInfo> owner=program.type(target.orElseThrow().id().owner(),target.orElseThrow().id().loader());
        Query<Boolean> allowed=owner.map(type -> methodAccess(target.orElseThrow(),call.call().site().method(),type,program)).orElseGet(() -> new Query<>(Optional.empty(),query.pending()));
        gaps.addAll(Mechanisms.queryGaps(call,allowed));
        if(accessKnown && !override && allowed.value().equals(Optional.of(false)))return Local.of(new Raise("java/lang/IllegalAccessException"));
        if(!override && !allowed.value().equals(Optional.of(true)))gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,accessKnown?"reflective method access is unresolved":"reflective access override must permit this method"));
        if(override)gaps.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"method access suppression must be permitted"));
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
        Local accepted=Local.of(new Dispatch(selected.id(),receiver,arguments,Kind.REFLECTION,gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,witnesses,List.copyOf(gaps),ReturnFlow.TO_RESULT,ExceptionFlow.REFLECTED),
                new Observe(Kind.REFLECTION,"resolved reflective target " + selected.id(),witnesses,List.copyOf(gaps)));
        return !override && !allowed.value().equals(Optional.of(true))
                ?Local.of(new Alternative(0,Local.of(new Raise("java/lang/IllegalAccessException"))),new Alternative(1,accepted)):accepted;
    }

    private static ObjectValue metadataObject(Reflected method){return new ObjectValue(method.object(),"java/lang/reflect/Method",true,"method metadata",false);}
    private static Write initialAccess(Reflected method){return new Write(metadataObject(method),new MethodAccess(method.member()),Value.of(new Literal(0)));}
    private Query<Boolean> methodAccess(Method method,MethodId caller,ClassInfo owner,Program program) {
        String name=owner.name(),from=caller.owner();
        boolean samePackage=caller.loader()==owner.loader() && name.substring(0,Math.max(0,name.lastIndexOf('/'))).equals(from.substring(0,Math.max(0,from.lastIndexOf('/'))));
        if((owner.access() & Opcodes.ACC_PUBLIC)==0 && !samePackage)return new Query<>(Optional.of(false),List.of());
        if((method.access() & Opcodes.ACC_PRIVATE)!=0)return program.nestmates(from,caller.loader(),name,owner.loader());
        if(method.isPublic() || samePackage)return new Query<>(Optional.of(true),List.of());
        if((method.access() & Opcodes.ACC_PROTECTED)==0)return new Query<>(Optional.of(false),List.of());
        Query<Boolean> subclass=program.assignable(from,caller.loader(),name,owner.loader());
        return subclass.value().equals(Optional.of(false)) && subclass.pending().isEmpty()?subclass:new Query<>(Optional.empty(),subclass.pending());
    }

    private static Local unresolved(Invocation call,List<Gap> gaps,List<Site> witnesses) {
        return Local.of(Mechanisms.result(new Unknown("unresolved reflective target")),
                new Observe(Kind.REFLECTION,"generic Method.invoke; target requires concrete object and value bindings",witnesses,List.copyOf(gaps)));
    }
    private static boolean platformClass(Invocation call,Program program) {
        return program.type("java/lang/Class",call.call().target().loader()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent();
    }
    private static void frontier(List<Effect> effects,List<Gap> gaps,List<Site> witnesses) {
        effects.add(new Observe(Kind.REFLECTION,"unresolved reflective target frontier",witnesses,gaps));
        // An unexplored target cannot also be the return value of a selected known target.
        effects.add(new Alternative(-1-effects.size(),Local.of(new Result(Value.of(new Unknown("unresolved reflective target")).requiring(gaps)))));
    }

}
