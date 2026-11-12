package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Mechanisms.*;
import java.util.*;

final class Serialization implements Model {
    private final JdkStructures structure;
    private final Guidance guidance;
    private record NativeType(ClassInfo type,Optional<Method> hash,List<Method> hooks,List<QueryIssue> pending) {}
    private int candidateDefinitions=-1;
    private List<NativeType> nativeTypes=List.of();
    private List<QueryIssue> nativeFrontier=List.of();
    Serialization(JdkStructures structure,Guidance guidance) { this.structure = structure;this.guidance=guidance; }
    static MissingField missingField(ObjectValue receiver,FieldId field,Atom fallback,Program program) {
        if(receiver.source().filter(source -> source.path().stream().anyMatch(Decoded.class::isInstance)).isEmpty())return new MissingField(fallback,List.of());
        Optional<FieldInfo> declaration=program.fields(field.owner(),field.loader()).stream().filter(info -> info.id().equals(field)).findFirst();
        Query<Boolean> serial=program.assignable(field.owner(),field.loader(),"java/io/Serializable",0);
        if(declaration.isEmpty() || !serial.value().equals(Optional.of(true)))return new MissingField(new Unknown("field is not an ordinary serialized source slot: "+field),List.of());
        int access=declaration.orElseThrow().access();
        if((access & org.objectweb.asm.Opcodes.ACC_TRANSIENT)!=0) {
            Query<Boolean> external=program.assignable(receiver.type(),receiver.loader(),"java/io/Externalizable",0);
            String owner=receiver.type();int loader=receiver.loader();Set<DefinedType> seen=new HashSet<>();
            while(owner!=null && seen.size()<64 && seen.add(new DefinedType(owner,loader))) {
                Optional<ClassInfo> type=program.type(owner,loader);
                boolean inherited=!owner.equals(receiver.type()) || loader!=receiver.loader();
                if(type.isEmpty() || type.get().methods().stream().anyMatch(method -> readObjectHook(method)
                        || inherited && noDataHook(method)
                        || (!external.value().equals(Optional.of(false)) || !external.pending().isEmpty()) && readExternalHook(method)))
                    return new MissingField(new Unknown("custom native hook may initialize transient field: "+field),List.of());
                if(owner.equals("java/lang/Object"))return new MissingField(new Literal(field.descriptor().startsWith("L") || field.descriptor().startsWith("[")?null:0),List.of());
                owner=type.get().parent();if(owner!=null)loader=program.scope(owner,loader);
            }
            return new MissingField(new Unknown("native field hierarchy is unresolved: "+field),List.of());
        }
        InputSource source=receiver.source().orElseThrow().at(new SerializedField(field));
        Atom value=fallback instanceof ObjectValue object?new ObjectValue(object.id(),object.type(),false,object.origin(),false,Optional.of(source),object.loader()):new ExternalValue(field.descriptor(),source);
        return new MissingField(value,List.of(new InputNeed(receiver,Optional.of(new SerializedField(field)),NeedKind.VALUE,field.descriptor(),List.of(),"source field required by conditional native member")));
    }
    static boolean read(MethodId id) {
        return (id.owner().equals("java/io/ObjectInputStream") || id.owner().equals("java/io/ObjectInput"))
                && (id.name().equals("readObject") || id.owner().equals("java/io/ObjectInputStream") && id.name().equals("readUnshared"))
                && id.descriptor().equals("()Ljava/lang/Object;");
    }
    private static boolean readObjectHook(Method method) {
        return method.id().name().equals("readObject") && method.id().descriptor().equals("(Ljava/io/ObjectInputStream;)V")
                && !method.isStatic() && (method.access() & org.objectweb.asm.Opcodes.ACC_PRIVATE)!=0;
    }
    private static boolean readExternalHook(Method method) {
        return method.id().name().equals("readExternal") && method.id().descriptor().equals("(Ljava/io/ObjectInput;)V") && method.isPublic() && !method.isStatic();
    }
    private static boolean noDataHook(Method method) {
        return method.id().name().equals("readObjectNoData") && method.id().descriptor().equals("()V")
                && !method.isStatic() && (method.access() & org.objectweb.asm.Opcodes.ACC_PRIVATE)!=0;
    }

    @Override public Optional<Local> apply(Invocation call, Bindings bindings, Program program) {
        Optional<Local> basic=basicRead(call,bindings,program);if(basic.isPresent())return basic;
        // A symbolic owner may be a subclass; a user implementation of ObjectInput is not native OIS.
        MethodId symbolic=call.call().target();
        if(Set.of("readObject","readUnshared","defaultReadObject","readFields").contains(symbolic.name()) && call.receiver() instanceof ObjectValue receiver) {
            Query<Method> actual=program.lookup(program.method(receiver.type(),symbolic.name(),symbolic.descriptor(),receiver.loader()));
            if(actual.value().isPresent()) {
                MethodId target=actual.value().get().id();
                if(!target.owner().equals("java/io/ObjectInputStream") && !target.owner().equals("java/io/ObjectInput"))return Optional.empty();
                call=new Invocation(new Call(call.call().site(),target,call.call().opcode(),call.call().receiver(),call.call().arguments()),call.receiver(),call.arguments(),call.result(),call.path());
            }
        }
        if (call.is("java/io/ObjectInputStream","defaultReadObject","()V")) return Optional.of(defaultFields(call,bindings,program,false));
        if(call.is("java/io/ObjectInputStream","readFields","()Ljava/io/ObjectInputStream$GetField;"))
            return Optional.of(defaultFields(call,bindings,program,true));
        if(Set.of("java/io/ObjectInputStream$GetField","java/io/ObjectInputStream$GetFieldImpl").contains(symbolic.owner())
                && call.receiver() instanceof ObjectValue view && !bindings.read(view,new HookOwner()).under(call.path()).empty())
            return Optional.of(getField(call,view,bindings,program).onModelState());
        if (!read(call.call().target())) return Optional.empty();
        if (call.receiver() instanceof ObjectValue stream) {
            Value decoded=bindings.read(stream,new Decoded()).under(call.path());
            Value position=bindings.read(stream,new StreamCursor());
            if (!decoded.empty() && position.empty()) {
                List<Effect> effects=new ArrayList<>();
                effects.add(new Write(stream,new StreamCursor(),Value.of(new Literal(1))));
                for (Bound root:decoded.alternatives()) {
                    Local lifecycle=visit(call,stream,root.atom(),bindings,program,new LinkedHashSet<>());
                    effects.add(new Conditional(root.path(),root.gaps(),root.dependencies(),lifecycle));
                }
                return Optional.of(new Local(effects));
            }
        }
        Query<List<Bound>> origins=ValueBindings.sources(call.receiver(),bindings,call.path());
        List<Effect> alternatives=new ArrayList<>();List<Bound> sources=origins.value().orElseThrow();
        if(sources.isEmpty())return Optional.of(Local.of(new Conditional(call.path(),Mechanisms.queryGaps(call,origins),Set.of(),unbound(call,program,Optional.empty()))));
        for(Bound source:sources) {
            StreamRead occurrence=new StreamRead(call.result().id(),call.call().site(),"Ljava/lang/Object;");
            Optional<InputSource> position=Values.source(source.atom()).map(input -> input.at(occurrence));
            Local branch=Local.of(new Conditional(source.path(),source.gaps(),source.dependencies(),unbound(call,program,position)));
            alternatives.add(sources.size()==1?branch.effects().get(0):new Alternative(alternatives.size(),branch));
        }
        return Optional.of(Local.of(new Conditional(call.path(),Mechanisms.queryGaps(call,origins),Set.of(),new Local(alternatives))));
    }

    private static Optional<Local> basicRead(Invocation call,Bindings bindings,Program program) {
        MethodId api=call.call().target();
        if(!Set.of("java/io/ObjectInputStream","java/io/ObjectInput","java/io/DataInputStream","java/io/DataInput").contains(api.owner())
                || program.type(api.owner()).filter(t -> t.role()==io.just.input.Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        String descriptor=switch(api.name()) {
            case "readBoolean" -> "Z";case "readByte" -> "B";case "readUnsignedByte","readUnsignedShort","readInt" -> "I";
            case "readChar" -> "C";case "readShort" -> "S";case "readLong" -> "J";case "readFloat" -> "F";case "readDouble" -> "D";
            case "readUTF" -> "Ljava/lang/String;";default -> "";
        };
        if(descriptor.isEmpty() || !api.descriptor().equals("()"+descriptor))return Optional.empty();
        StreamRead position=new StreamRead(call.result().id(),call.call().site(),descriptor);
        Query<List<Bound>> origins=ValueBindings.sources(call.receiver(),bindings,call.path());
        Value values=Value.BOTTOM;
        for(Bound origin:origins.value().orElseThrow())if(Values.source(origin.atom()).isPresent()) {
            InputSource source=Values.source(origin.atom()).orElseThrow().at(position);
            Atom value=descriptor.startsWith("L")?new ObjectValue(call.result().id(),"java/lang/String",true,"UTF stream read",false,Optional.of(source)):new ExternalValue(descriptor,source);
            Path path=origin.path();
            if(api.name().equals("readUnsignedByte") || api.name().equals("readUnsignedShort"))
                path=path.restricting(source,value,descriptor,new IntegralRange(0,api.name().equals("readUnsignedByte")?255:65535)).orElseThrow();
            values=values.merge(Value.of(value,path).requiring(origin.gaps()).tracing(origin.dependencies()));
        }
        if(values.empty())values=Value.of(new Unknown("stream data at "+position)).requiring(Mechanisms.unknown(call,"stream identity and read layout are unspecified"));
        List<Gap> normal=new ArrayList<>(Mechanisms.queryGaps(call,origins));
        normal.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"normal "+api.name()+" requires available stream data at this read occurrence; wire layout and byte offset are unknown"));
        List<Effect> effects=new ArrayList<>();
        effects.add(new Alternative(0,Local.of(new RequireNormal(normal),new Result(values))));
        effects.add(new Alternative(1,Local.of(new Raise("java/io/EOFException"))));
        if(api.name().equals("readUTF"))effects.add(new Alternative(2,Local.of(new Raise("java/io/UTFDataFormatException"))));
        return Optional.of(new Local(effects));
    }

    private Local visit(Invocation call,ObjectValue stream,Atom atom,Bindings bindings,Program program,Set<Integer> visited) {
        if (!(atom instanceof ObjectValue object)) return Local.of(Mechanisms.result(atom));
        Query<Method> replacement=object.type().startsWith("[")?new Query<>(Optional.empty(),List.of()):resolveHook(program,object.type(),object.loader());
        Optional<Method> replacementHook=replacement.value();
        Value memo=bindings.read(stream,new ResolvedObject(object.id()));
        if (!memo.empty()) return ready(memo);
        boolean active=bindings.read(stream,new ActiveObject(object.id())).alternatives().stream().anyMatch(bound -> bound.atom() instanceof ObjectValue);
        if(active)return ready(Value.of(object).requiring(Mechanisms.queryGaps(call,replacement)).requiring(replacementHook.isPresent() || !replacement.pending().isEmpty()?List.of(Mechanisms.gap(call,GapKind.INPUT_BINDING,"active ancestor replacement is unresolved")):List.of()));
        if (!visited.add(object.id())) return ready(Value.of(atom).requiring(Mechanisms.queryGaps(call,replacement)).requiring(replacementHook.isPresent() || !replacement.pending().isEmpty()?List.of(Mechanisms.gap(call,GapKind.INPUT_BINDING,"cyclic readResolve identity is unresolved")):List.of()));
        if (visited.size()>64) return remembered(stream,object,Value.of(new Truncated("serialized object visit budget")).requiring(List.of(Mechanisms.gap(call,GapKind.BUDGET,"serialized object visit budget (64)"))));
        List<Effect> effects=new ArrayList<>();
        effects.add(new Write(stream,new ActiveObject(object.id()),Value.of(object)));
        List<Gap> gaps=new ArrayList<>(Mechanisms.queryGaps(call,replacement));
        Query<Boolean> serializable=program.assignable(object.type(),object.loader(),"java/io/Serializable",0);gaps.addAll(Mechanisms.queryGaps(call,serializable));
        if (!object.exact() || serializable.value().equals(Optional.of(false)) && serializable.pending().isEmpty())
            return remembered(stream,object,Value.of(new Unknown("native root/member type is not serializable")).requiring(List.of(Mechanisms.gap(call,GapKind.INPUT_BINDING,"native root/member runtime type or Serializable relationship is not established"))));
        if(!object.type().startsWith("[") && program.type(object.type(),object.loader()).map(t -> (t.access() & (org.objectweb.asm.Opcodes.ACC_RECORD|org.objectweb.asm.Opcodes.ACC_ENUM))!=0).orElse(false))
            return remembered(stream,object,Value.of(object).requiring(List.of(Mechanisms.gap(call,GapKind.UNSUPPORTED,"record/enum native construction is outside ordinary Serializable field restoration"))));
        if(object.type().equals("[B")) {
            Value content=bindings.read(object,new Content());
            if(content.alternatives().stream().anyMatch(bound -> bound.atom() instanceof Bytecode)) {
                Value known=Value.BOTTOM;for(Bound bound:content.alternatives())if(bound.atom() instanceof Bytecode)known=known.merge(Value.of(object,bound.path()).requiring(bound.gaps()).tracing(bound.dependencies()));
                return remembered(stream,object,known.requiring(gaps));
            }
        }
        if (object.type().startsWith("[")) {
            for (Bound length:bindings.read(object,new Length()).under(call.path()).alternatives())
                if (length.atom() instanceof Literal value && value.value() instanceof Integer size && size>=0) {
                    if(size>64)effects.add(memberFrontier(call,object,length,size));
                    for (int i=0;i<Math.min(size,64);i++) {
                        Value elements=bindings.read(object,new SerializedIndex(i));
                        if (elements.empty()) elements=bindings.read(object,new Index(i));
                        for (Bound element:elements.under(length.path()).alternatives()) effects.add(new Conditional(element.path(),element.gaps(),element.dependencies(),
                                Local.of(new Store(object,new Index(i),visit(call,stream,element.atom(),bindings,program,visited),referenceType(object.type().substring(1))))));
                    }
                }
        } else if (program.subtype(object.type(),"java/util/HashMap") || object.type().equals("java/util/HashSet")) {
            boolean set=object.type().equals("java/util/HashSet");
            JdkStructures.Witness witness=structure.decodedKeyPaths().stream().filter(p -> p.owner().equals(set?"java/util/HashSet":"java/util/HashMap"))
                    .map(JdkStructures.DecodedPath::witness).findFirst().orElse(new JdkStructures.Witness(List.of(),List.of()));
            for(Bound length:bindings.read(object,new Length()).under(call.path()).alternatives())
                if(length.atom() instanceof Literal literal && literal.value() instanceof Integer size && size>=0) {
                    if(size>64)effects.add(memberFrontier(call,object,length,size));
                    for(int i=0;i<Math.min(size,64);i++) {
                        Value keys=bindings.read(object,set?new SerializedIndex(i):new SerializedKey(i));
                        Value values=set?Value.NULL:bindings.read(object,new SerializedValue(i));
                        for(Bound key:keys.alternatives())for(Bound value:values.under(key.path()).alternatives()) {
                            List<Effect> insert=new ArrayList<>();
                            insert.add(new IgnoreResult(visit(call,stream,key.atom(),bindings,program,visited)));
                            if(!set)insert.add(new IgnoreResult(visit(call,stream,value.atom(),bindings,program,visited)));
                            Value resolvedKey=resolved(stream,key.atom(),bindings),resolvedValue=set?Value.NULL:resolved(stream,value.atom(),bindings);
                            for(Bound actual:resolvedKey.under(key.path()).alternatives())for(Bound entry:resolvedValue.under(actual.path()).alternatives()) {
                                List<Gap> required=new ArrayList<>(actual.gaps());required.addAll(entry.gaps());
                                Set<Integer> dependencies=new LinkedHashSet<>(actual.dependencies());dependencies.addAll(entry.dependencies());
                                insert.add(new Conditional(entry.path(),required,dependencies,Containers.decoded(call,object,actual.atom(),entry.atom(),witness)));
                            }
                            effects.add(new IgnoreResult(Local.of(new Conditional(key.path(),key.gaps(),key.dependencies(),new Local(insert)))));
                        }
                    }
                }
        } else {
            Query<List<ClassInfo>> ancestors=hierarchy(object.type(),object.loader(),program);List<ClassInfo> hierarchy=ancestors.value().orElseThrow();gaps.addAll(Mechanisms.queryGaps(call,ancestors));
            List<ClassInfo> storage=new ArrayList<>();String storageType=object.type();int storageLoader=object.loader();
            while(storage.size()<64) {
                Query<ClassInfo> definition=program.definition(storageType,storageLoader);gaps.addAll(Mechanisms.queryGaps(call,definition));
                if(definition.value().isEmpty() || storage.contains(definition.value().get()))break;
                ClassInfo type=definition.value().get();storage.add(type);if(type.parent()==null)break;
                storageType=type.parent();storageLoader=program.scope(storageType,type.loader());
            }
            for(ClassInfo owner:storage)for(FieldInfo field:program.fields(owner.name(),owner.loader()))if((field.access() & org.objectweb.asm.Opcodes.ACC_STATIC)==0)
                effects.add(new Write(object,new Field(field.id()),Value.of(new Literal(field.id().descriptor().startsWith("L") || field.id().descriptor().startsWith("[")?null:0))));
            Query<Boolean> external=program.assignable(object.type(),object.loader(),"java/io/Externalizable",0);gaps.addAll(Mechanisms.queryGaps(call,external));
            if(external.value().equals(Optional.of(true))) {
                Optional<Method> constructor=program.declared(program.method(object.type(),"<init>","()V",object.loader()));
                if(constructor.isEmpty() || !constructor.get().isPublic())return Local.of(new Raise("java/io/InvalidClassException"));
                JdkStructures.Witness protocol=structure.protocol("readExternal");
                List<Gap> required=protocolGaps(call,protocol);
                effects.add(new Dispatch(constructor.get().id(),object,List.of(),Kind.DESERIALIZATION,required.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,protocol.sites(),required,ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
                Query<Method> resolved=program.lookup(program.method(object.type(),"readExternal","(Ljava/io/ObjectInput;)V",object.loader()));
                List<Gap> hookGaps=Mechanisms.queryGaps(call,resolved);gaps.addAll(hookGaps);
                Optional<Method> hook=resolved.value().filter(Serialization::readExternalHook);
                if(hook.isEmpty() && resolved.pending().isEmpty())return Local.of(new Raise("java/io/InvalidClassException"));
                effects.add(new Dispatch(hook.map(Method::id).orElse(program.method(object.type(),"readExternal","(Ljava/io/ObjectInput;)V",object.loader())),object,List.of(stream),Kind.DESERIALIZATION,required.isEmpty() && hookGaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,protocol.sites(),unionIssues(call,required,new JdkStructures.Witness(List.of(),resolved.pending())),ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
            } else {
                String parent=hierarchy.isEmpty()?null:hierarchy.get(0).parent();
                if(parent!=null && !parent.equals("java/lang/Object")) {
                    Query<Method> declared=program.declaration(program.method(parent,"<init>","()V",hierarchy.get(0).loader()));gaps.addAll(Mechanisms.queryGaps(call,declared));
                    Optional<Method> constructor=declared.value();
                    if(declared.pending().isEmpty()) {
                    if(constructor.isEmpty() || (constructor.get().access() & org.objectweb.asm.Opcodes.ACC_PRIVATE)!=0
                            || !constructor.get().isPublic() && (constructor.get().access() & org.objectweb.asm.Opcodes.ACC_PROTECTED)==0 && !packageOf(parent).equals(packageOf(hierarchy.get(0).name())))
                        return Local.of(new Raise("java/io/InvalidClassException"));
                    JdkStructures.Witness protocol=structure.protocol("readObject");List<Gap> required=protocolGaps(call,protocol);
                    effects.add(new Dispatch(constructor.get().id(),object,List.of(),Kind.DESERIALIZATION,required.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,protocol.sites(),required,ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
                    }
                }
                for(ClassInfo owner:hierarchy)effects.add(new IgnoreResult(classSlot(call,stream,object,owner,bindings,program,visited)));
            }
            if(hierarchy.size()>=64)gaps.add(Mechanisms.gap(call,GapKind.BUDGET,"serialization hierarchy budget (64)"));
        }
        Optional<Method> resolve=replacementHook;
        if (resolve.isPresent()) {
            JdkStructures.Witness protocol=structure.protocol("readResolve");List<Site> witness=protocol.sites();
            gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),protocol.pending())));
            if (witness.isEmpty()) gaps.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"readResolve protocol dispatch structure not verified"));
            effects.add(new Dispatch(resolve.get().id(),object,List.of(),Kind.DESERIALIZATION,gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,witness,List.copyOf(gaps),ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT));
        } else effects.add(new Result(Value.of(object).requiring(gaps)));
        effects.add(new Observe(Kind.DESERIALIZATION,"native read/member bound to "+object.type(),List.of(call.call().site()),List.copyOf(gaps)));
        effects.add(new Write(stream,new ActiveObject(object.id()),Value.NULL));
        Local lifecycle=new Local(effects);
        return Local.of(new Store(stream,new ResolvedObject(object.id()),lifecycle),new Result(memo));
    }

    private static Value resolved(ObjectValue stream,Atom atom,Bindings bindings) {
        return atom instanceof ObjectValue object?bindings.read(stream,new ResolvedObject(object.id())):Value.of(atom);
    }
    private Local classSlot(Invocation call,ObjectValue stream,ObjectValue object,ClassInfo owner,Bindings bindings,Program program,Set<Integer> visited) {
        List<Effect> normal=new ArrayList<>();
        Optional<Method> hook=program.declared(new MethodId(owner.name(),"readObject","(Ljava/io/ObjectInputStream;)V",owner.loader())).filter(Serialization::readObjectHook);
        if(hook.isPresent()) {
            JdkStructures.Witness protocol=structure.protocol("readObject");List<Gap> required=protocolGaps(call,protocol);
            normal.add(new Write(stream,new HookReceiver(),Value.of(object)));
            normal.add(new Write(stream,new HookOwner(),Value.of(new Values.ClassValue("L"+owner.name()+";",true,Optional.empty(),owner.loader()))));
            normal.add(new Dispatch(hook.get().id(),object,List.of(stream),Kind.DESERIALIZATION,required.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,protocol.sites(),required,ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
            normal.add(new Write(stream,new HookReceiver(),Value.NULL));normal.add(new Write(stream,new HookOwner(),Value.NULL));
        } else normal.addAll(materialize(call,stream,object,owner,bindings,program,visited).effects());
        normal.add(new Result(Value.NULL));
        if(owner.name().equals(object.type()) && owner.loader()==object.loader())return new Local(normal);
        ClassData data=new ClassData(owner.name(),owner.loader());
        normal.add(0,new Need(new InputNeed(object,Optional.of(data),NeedKind.VALUE,"I",List.of(new Literal(1)),"serializable class data slot is present in this stream")));
        List<Effect> absent=new ArrayList<>();absent.add(new Need(new InputNeed(object,Optional.of(data),NeedKind.VALUE,"I",List.of(new Literal(0)),"serializable superclass data slot is absent in this stream")));
        Optional<Method> noData=program.declared(new MethodId(owner.name(),"readObjectNoData","()V",owner.loader())).filter(Serialization::noDataHook);
        if(noData.isPresent()) {
            JdkStructures.Witness protocol=structure.protocol("readObjectNoData");List<Gap> required=protocolGaps(call,protocol);
            absent.add(new Dispatch(noData.get().id(),object,List.of(),Kind.DESERIALIZATION,required.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,protocol.sites(),required,ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
        }
        absent.add(new Result(Value.NULL));
        Local alternatives=Local.of(new Alternative(0,new Local(normal)),new Alternative(1,new Local(absent)));
        Value supplied=bindings.read(object,data).under(call.path());
        if(supplied.empty())return alternatives;
        List<Effect> selected=new ArrayList<>();
        for(Bound value:supplied.alternatives()) {
            Local branch=value.atom().equals(new Literal(1))?new Local(normal):value.atom().equals(new Literal(0))?new Local(absent):alternatives;
            selected.add(new Conditional(value.path(),value.gaps(),value.dependencies(),branch));
        }
        return new Local(selected);
    }
    private static Effect memberFrontier(Invocation call,ObjectValue object,Bound length,int size) {
        Gap gap=Mechanisms.gap(call,GapKind.BUDGET,"serialized member frontier at object "+object.id()+": indices [64,"+size+")");
        return new Conditional(length.path(),length.gaps(),length.dependencies(),Local.of(new Observe(Kind.DESERIALIZATION,gap.detail(),List.of(call.call().site()),List.of(gap))));
    }
    private static Local remembered(ObjectValue stream,ObjectValue object,Value value) {
        return Local.of(new Write(stream,new ResolvedObject(object.id()),value),new Result(value));
    }
    private static Local ready(Value value) {
        return Local.of(new Result(value));
    }
    private static boolean trivialHash(Method method,Program program) {
        if(!method.hasBody())return false;Facts facts=program.facts(method.id());
        return facts.limitations().isEmpty() && !facts.actions().isEmpty() && facts.actions().stream().allMatch(action -> action instanceof Returned
                || action instanceof Call call && call.target().equals(new MethodId("java/lang/Object","hashCode","()I")));
    }
    private static Query<List<ClassInfo>> hierarchy(String name,int loader,Program program) {
        List<ClassInfo> result=new ArrayList<>();List<QueryIssue> pending=new ArrayList<>();String current=name;
        while(result.size()<64) {
            Query<Boolean> serial=program.assignable(current,loader,"java/io/Serializable",0);pending.addAll(serial.pending());
            if(serial.value().equals(Optional.of(false)) && serial.pending().isEmpty())break;
            Query<ClassInfo> definition=program.definition(current,loader);pending.addAll(definition.pending());
            if(definition.value().isEmpty() || result.contains(definition.value().get()))break;
            ClassInfo type=definition.value().get();result.add(type);if(type.parent()==null)break;
            current=type.parent();loader=program.scope(current,type.loader());
        }
        if(result.size()>=64)pending.add(new QueryIssue(QueryCause.BUDGET,"serialization hierarchy budget (64)"));
        Collections.reverse(result);return new Query<>(Optional.of(List.copyOf(result)),List.copyOf(pending));
    }
    private static List<Gap> protocolGaps(Invocation call,JdkStructures.Witness protocol) {
        List<Gap> gaps=new ArrayList<>(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),protocol.pending())));
        if(protocol.sites().isEmpty())gaps.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"native hook dispatch structure not verified"));
        return List.copyOf(gaps);
    }
    private Local defaultFields(Invocation call,Bindings bindings,Program program,boolean fieldView) {
        if(!(call.receiver() instanceof ObjectValue stream))return Local.of(new Raise("java/io/NotActiveException"));
        Value receivers=bindings.read(stream,new HookReceiver()),owners=bindings.read(stream,new HookOwner());
        if(receivers.alternatives().stream().anyMatch(bound -> bound.atom() instanceof Unknown)) {
            Gap gap=Mechanisms.gap(call,GapKind.INPUT_BINDING,"conditional native hook needs its concrete serialized receiver and fields");
            return Local.of(new Need(new InputNeed(stream,Optional.of(new HookReceiver()),NeedKind.SERIALIZED_MEMBERS,"Ljava/lang/Object;",List.of(),gap.detail())),new RequireNormal(List.of(gap)),new Result(Value.NULL.requiring(List.of(gap))));
        }
        List<Effect> effects=new ArrayList<>();
        for(Bound receiver:receivers.under(call.path()).alternatives())for(Bound owner:owners.under(receiver.path()).alternatives()) {
            if(!(receiver.atom() instanceof ObjectValue object) || !(owner.atom() instanceof Values.ClassValue declaring))continue;
            List<Effect> fields=new ArrayList<>();
            Value used=bindings.read(stream,new FieldsRead(object.id(),Values.type(declaring.descriptor()),declaring.loader())).under(owner.path());
            if(!used.empty())fields.add(new Raise("java/io/NotActiveException"));
            else {
                fields.add(new Write(stream,new FieldsRead(object.id(),Values.type(declaring.descriptor()),declaring.loader()),Value.of(new Literal(true))));
                fields.addAll(materialize(call,stream,object,program.type(Values.type(declaring.descriptor()),declaring.loader()).orElseThrow(),bindings,program,new LinkedHashSet<>(Set.of(object.id())),fieldView?call.result():object).effects());
                if(fieldView) {
                    fields.add(new Write(call.result(),new HookReceiver(),Value.of(object)));
                    fields.add(new Write(call.result(),new HookOwner(),Value.of(declaring)));
                }
                fields.add(new RequireNormal(List.of()));
                fields.add(Mechanisms.result(fieldView?call.result():new Literal(null)));
            }
            Set<Integer> dependencies=new LinkedHashSet<>(receiver.dependencies());dependencies.addAll(owner.dependencies());
            List<Gap> gaps=new ArrayList<>(receiver.gaps());gaps.addAll(owner.gaps());
            effects.add(new Conditional(owner.path(),gaps,dependencies,new Local(fields)));
        }
        return effects.isEmpty()?Local.of(new Raise("java/io/NotActiveException")):new Local(effects);
    }
    private Local materialize(Invocation call,ObjectValue stream,ObjectValue object,ClassInfo owner,Bindings bindings,Program program,Set<Integer> visited) {
        return materialize(call,stream,object,owner,bindings,program,visited,object);
    }
    private Local materialize(Invocation call,ObjectValue stream,ObjectValue object,ClassInfo owner,Bindings bindings,Program program,Set<Integer> visited,ObjectValue destination) {
        List<Effect> before=new ArrayList<>(),reads=new ArrayList<>(),after=new ArrayList<>();
        JdkStructures.FieldTiming timing=structure.fieldTiming();List<Gap> format=new ArrayList<>(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),timing.witness().pending())));
        if(timing.order()==JdkStructures.FieldOrder.UNKNOWN)format.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"selected JDK default-field timing is not verified"));
        if(program.fields(owner.name(),owner.loader()).stream().anyMatch(field -> field.id().name().equals("serialPersistentFields") && field.id().descriptor().equals("[Ljava/io/ObjectStreamField;")))
            format.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"custom serialPersistentFields layout is not verified"));
        if(!format.isEmpty())before.add(new RequireNormal(List.copyOf(format)));
        List<FieldInfo> fields=program.fields(owner.name(),owner.loader()).stream().filter(field -> (field.access() & (org.objectweb.asm.Opcodes.ACC_STATIC|org.objectweb.asm.Opcodes.ACC_TRANSIENT))==0)
                .sorted(Comparator.comparing((FieldInfo field) -> referenceType(field.id().descriptor()).isPresent()).thenComparing(field -> field.id().name())).toList();
        for(FieldInfo field:fields) {
            Value values=bindings.read(object,new SerializedField(field.id())).requiring(format),restored=Value.BOTTOM;
            Value presence=bindings.read(object,new FieldPresence(field.id())).under(call.path());
            if(values.empty() && presence.alternatives().stream().anyMatch(b -> b.atom().equals(new Literal(0)))) {
                Atom zero=new Literal(referenceType(field.id().descriptor()).isPresent()?null:switch(field.id().descriptor()){case "J" -> 0L;case "F" -> 0f;case "D" -> 0d;default -> (Object)0;});
                for(Bound absent:presence.alternatives())if(absent.atom().equals(new Literal(0)))restored=restored.merge(Value.of(zero,absent.path()).requiring(absent.gaps()).tracing(absent.dependencies()));
            } else if(values.empty()) {
                InputNeed need=new InputNeed(object,Optional.of(new SerializedField(field.id())),NeedKind.VALUE,field.id().descriptor(),List.of(),"serialized field consumed by default field restoration");
                before.add(new Need(need));
                Atom missing=object.source().<Atom>map(source -> field.id().descriptor().startsWith("L") || field.id().descriptor().startsWith("[")
                        ?new Symbolic(Values.type(field.id().descriptor()),"serialized source field "+field.id(),Optional.of(source.at(new SerializedField(field.id()))),program.scope(Values.type(field.id().descriptor()),field.id().loader()))
                        :new ExternalValue(field.id().descriptor(),source.at(new SerializedField(field.id())))).orElseGet(() -> new Unknown("serialized field not supplied: "+field.id()));
                restored=Value.of(missing).requiring(List.of(Mechanisms.gap(call,GapKind.INPUT_BINDING,need.reason())));
            } else for(Bound value:values.under(call.path()).alternatives()) {
                Value actual=resolved(stream,value.atom(),bindings);
                boolean cycle=value.atom() instanceof ObjectValue member && actual.empty() && (visited.contains(member.id())
                        || bindings.read(stream,new ActiveObject(member.id())).alternatives().stream().anyMatch(bound -> bound.atom() instanceof ObjectValue));
                Local child=visit(call,stream,value.atom(),bindings,program,visited);
                if(value.atom() instanceof ObjectValue)reads.add(new IgnoreResult(Local.of(new Conditional(value.path(),value.gaps(),value.dependencies(),child))));
                if(cycle) {
                    Query<Method> hook=resolveHook(program,((ObjectValue)value.atom()).type(),((ObjectValue)value.atom()).loader());
                    List<Gap> pending=new ArrayList<>(Mechanisms.queryGaps(call,hook));
                    if(hook.value().isPresent() || !hook.pending().isEmpty())pending.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"cyclic member replacement is unresolved"));
                    actual=Value.of(value.atom()).requiring(pending);
                }
                restored=restored.merge(actual.under(value.path()).requiring(value.gaps()).tracing(value.dependencies()));
            }
            Store assignment=new Store(destination,new Field(field.id()),Local.of(new Result(restored)),referenceType(field.id().descriptor()));
            if(referenceType(field.id().descriptor()).isEmpty() && timing.order()==JdkStructures.FieldOrder.PRIMITIVES_FIRST)before.add(assignment);else after.add(assignment);
        }
        before.addAll(reads);before.addAll(after);return new Local(before);
    }
    private static Optional<String> referenceType(String descriptor){return descriptor.startsWith("L") || descriptor.startsWith("[")?Optional.of(descriptor):Optional.empty();}

    private static Local getField(Invocation call,ObjectValue view,Bindings bindings,Program program) {
        MethodId api=call.call().target();boolean defaulted=api.name().equals("defaulted") && api.descriptor().equals("(Ljava/lang/String;)Z");
        if(!defaulted && !(api.name().equals("get") && call.arguments().size()==2))return Local.of(new Result(Value.of(new Unknown("GetField metadata operation is unsupported")).requiring(List.of(Mechanisms.gap(call,GapKind.UNSUPPORTED,"GetField metadata operation: "+api)))));
        Atom requested=call.arguments().get(0);
        if(requested instanceof Literal nil && nil.value()==null)return Local.of(new Raise("java/lang/NullPointerException"));
        if(!(requested instanceof Literal literal) || !(literal.value() instanceof String name))return Local.of(new Need(new InputNeed(requested,Optional.empty(),NeedKind.VALUE,"Ljava/lang/String;",List.of(),"finite serialized field name")),new Result(Value.of(new Unknown("GetField name is not finite")).requiring(Mechanisms.unknown(call,"GetField name is not finite"))));
        List<Effect> effects=new ArrayList<>();String expected=defaulted?"":program.signature(api).parameters().get(1).descriptor();
        for(Bound receiver:bindings.read(view,new HookReceiver()).under(call.path()).alternatives())for(Bound owner:bindings.read(view,new HookOwner()).under(receiver.path()).alternatives()) {
            if(!(receiver.atom() instanceof ObjectValue object) || !(owner.atom() instanceof Values.ClassValue type))continue;
            Optional<FieldInfo> field=program.fields(Values.type(type.descriptor()),type.loader()).stream().filter(f -> f.id().name().equals(name)
                    && (f.access() & (org.objectweb.asm.Opcodes.ACC_STATIC|org.objectweb.asm.Opcodes.ACC_TRANSIENT))==0
                    && (expected.isEmpty() || expected.equals("Ljava/lang/Object;") && referenceType(f.id().descriptor()).isPresent() || expected.equals(f.id().descriptor()))).findFirst();
            if(field.isEmpty()){effects.add(new Conditional(owner.path(),owner.gaps(),owner.dependencies(),Local.of(new Raise("java/lang/IllegalArgumentException"))));continue;}
            FieldId id=field.get().id();Value presence=bindings.read(object,new FieldPresence(id)).under(owner.path());
            Set<Integer> dependencies=new LinkedHashSet<>(receiver.dependencies());dependencies.addAll(owner.dependencies());
            List<Gap> required=new ArrayList<>(receiver.gaps());required.addAll(owner.gaps());
            for(int present=0;present<2;present++) {
                int selected=present;
                if(!presence.empty() && presence.alternatives().stream().allMatch(b -> b.atom() instanceof Literal l && l.value() instanceof Number number && number.intValue()!=selected))continue;
                Value result=defaulted?Value.of(new Literal(present==0?1:0)):present==0?Value.of(call.arguments().get(1)):bindings.read(view,new Field(id));
                if(result.empty())result=Value.of(new Unknown("serialized field value is unavailable: "+id)).requiring(Mechanisms.unknown(call,"serialized field value is unavailable: "+id));
                Local branch=Local.of(new Need(new InputNeed(object,Optional.of(new FieldPresence(id)),NeedKind.VALUE,"I",List.of(new Literal(present)),"incoming class descriptor field presence")),new RequireNormal(List.of()),new Result(result));
                if(presence.empty())effects.add(new Conditional(owner.path(),List.copyOf(required),Set.copyOf(dependencies),branch));
                else for(Bound flag:presence.alternatives()) {
                    if(flag.atom() instanceof Literal l && l.value() instanceof Number number && number.intValue()!=present)continue;
                    List<Gap> boundGaps=new ArrayList<>(required);boundGaps.addAll(flag.gaps());
                    Set<Integer> boundDependencies=new LinkedHashSet<>(dependencies);boundDependencies.addAll(flag.dependencies());
                    effects.add(new Conditional(flag.path(),List.copyOf(boundGaps),Set.copyOf(boundDependencies),branch));
                }
            }
        }
        if(effects.isEmpty())return Local.of(new Result(Value.of(new Unknown("GetField has no active readFields snapshot")).requiring(Mechanisms.unknown(call,"GetField snapshot and declaring class are unspecified"))));
        return new Local(effects);
    }

    private static Query<Method> resolveHook(Program program,String type,int loader) {
        String current=type;Set<DefinedType> seen=new HashSet<>();List<QueryIssue> pending=new ArrayList<>();
        while(seen.size()<64 && seen.add(new DefinedType(current,loader))) {
            Query<Method> declaration=program.declaration(program.method(current,"readResolve","()Ljava/lang/Object;",loader));pending.addAll(declaration.pending());
            Optional<Method> method=declaration.value();
            if(method.isPresent() && !method.get().isStatic() && method.get().hasBody()
                    && (current.equals(type) || (method.get().access() & org.objectweb.asm.Opcodes.ACC_PRIVATE)==0
                        && (method.get().isPublic() || (method.get().access() & org.objectweb.asm.Opcodes.ACC_PROTECTED)!=0 || packageOf(current).equals(packageOf(type)))))
                return new Query<>(method,List.copyOf(pending));
            Query<ClassInfo> definition=program.definition(current,loader);pending.addAll(definition.pending());
            if(definition.value().isEmpty() || definition.value().get().parent()==null)return new Query<>(Optional.empty(),List.copyOf(pending));
            ClassInfo owner=definition.value().get();current=owner.parent();loader=program.scope(current,owner.loader());
        }
        pending.add(new QueryIssue(QueryCause.BUDGET,"readResolve hierarchy budget/cycle (64)"));
        return new Query<>(Optional.empty(),List.copyOf(pending));
    }
    private static String packageOf(String name) { int split=name.lastIndexOf('/'); return split<0?"":name.substring(0,split); }
    private static List<Gap> unionIssues(Invocation call,List<Gap> input,JdkStructures.Witness witness) {
        List<Gap> gaps=new ArrayList<>(input);gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),witness.pending())));return List.copyOf(gaps);
    }
    /** Bytecode-only eligibility is shared by stream bindings; pending queries remain pending. */
    private List<NativeType> nativeTypes(Program program) {
        if(candidateDefinitions==program.definitionCount())return nativeTypes;
        List<ClassInfo> types=structure.targets();List<NativeType> preferred=new ArrayList<>(),examined=new ArrayList<>();
        List<QueryIssue> frontier=new ArrayList<>();int at=0;
        if(guidance.active())for(;at<types.size() && at<2048 && preferred.size()<48;at++) {
            Optional<NativeType> candidate=nativeType(types.get(at),program);if(candidate.isEmpty())continue;
            NativeType value=candidate.orElseThrow();examined.add(value);
            List<Method> callbacks=new ArrayList<>(value.hooks());value.hash().ifPresent(callbacks::add);
            Query<Boolean> match=guidance.callbacks(callbacks);frontier.addAll(match.pending());
            if(match.value().orElseThrow())preferred.add(value);
        }
        if(at==2048 && at<types.size())frontier.add(new QueryIssue(QueryCause.BUDGET,"relation native callback metadata frontier (2048)"));
        nativeFrontier=List.copyOf(new LinkedHashSet<>(frontier));
        ArrayDeque<NativeType> ranked=new ArrayDeque<>(preferred),plain=new ArrayDeque<>(examined);
        Set<ClassInfo> seen=new HashSet<>();List<NativeType> found=new ArrayList<>();int turn=0;
        while(found.size()<65 && (!ranked.isEmpty() || !plain.isEmpty() || at<types.size())) {
            if(plain.isEmpty())while(at<types.size() && plain.isEmpty())nativeType(types.get(at++),program).ifPresent(plain::addLast);
            NativeType candidate;
            if(!ranked.isEmpty() && (turn++%4!=3 || plain.isEmpty()))candidate=ranked.removeFirst();
            else if(!plain.isEmpty())candidate=plain.removeFirst();else break;
            if(seen.add(candidate.type()))found.add(candidate);
        }
        candidateDefinitions=program.definitionCount();nativeTypes=List.copyOf(found);return nativeTypes;
    }
    private Optional<NativeType> nativeType(ClassInfo type,Program program) {
        if((type.access() & (org.objectweb.asm.Opcodes.ACC_ABSTRACT|org.objectweb.asm.Opcodes.ACC_INTERFACE))!=0)return Optional.empty();
        Query<Boolean> serial=program.assignable(type.name(),type.loader(),"java/io/Serializable",0);
        if(serial.value().equals(Optional.of(false)) && serial.pending().isEmpty())return Optional.empty();
        List<QueryIssue> pending=new ArrayList<>(serial.pending());
        Query<Method> hashing=program.lookup(program.method(type.name(),"hashCode","()I",type.loader()));pending.addAll(hashing.pending());
        Optional<Method> hash=hashing.value().filter(m -> !m.id().owner().equals("java/lang/Object"));
        if(hash.isPresent() && trivialHash(hash.get(),program))hash=Optional.empty();
        Set<Method> hooks=new LinkedHashSet<>();Query<List<ClassInfo>> ancestors=hierarchy(type.name(),type.loader(),program);pending.addAll(ancestors.pending());
        for(ClassInfo ancestor:ancestors.value().orElseThrow())ancestor.methods().stream().filter(m -> readObjectHook(m) || !ancestor.name().equals(type.name()) && noDataHook(m)).forEach(hooks::add);
        Query<Method> replacement=resolveHook(program,type.name(),type.loader());replacement.value().ifPresent(hooks::add);pending.addAll(replacement.pending());
        Query<Boolean> external=program.assignable(type.name(),type.loader(),"java/io/Externalizable",0);pending.addAll(external.pending());
        if(!external.value().equals(Optional.of(false))) {
            Query<Method> hook=program.lookup(program.method(type.name(),"readExternal","(Ljava/io/ObjectInput;)V",type.loader()));pending.addAll(hook.pending());
            hook.value().filter(Serialization::readExternalHook).ifPresent(hooks::add);
        }
        return hash.isEmpty() && hooks.isEmpty()?Optional.empty():Optional.of(new NativeType(type,hash,List.copyOf(hooks),List.copyOf(new LinkedHashSet<>(pending))));
    }
    private Local unbound(Invocation call,Program program,Optional<InputSource> source) {
        List<Effect> effects = new ArrayList<>();
        List<Gap> missingInput = Mechanisms.unknown(call, "serialized root type, element membership and concrete field values were not provided as verified static input");
        ObjectValue decoded = new ObjectValue(call.result().id(), "java/lang/Object", false, "decoded object at " + call.call().site(),false,source.map(input -> input.at(new Decoded())));
        effects.add(new Result(Value.of(decoded).requiring(missingInput)));
        List<Atom> candidates=new ArrayList<>();
        effects.add(new Observe(Kind.DESERIALIZATION, "native object read; stream receiver=" + call.receiver(), List.of(call.call().site()), missingInput));
        List<NativeType> sources=nativeTypes(program);
        if(!nativeFrontier.isEmpty())effects.add(new Observe(Kind.DESERIALIZATION,"native member relation frontier",List.of(call.call().site()),Mechanisms.queryGaps(call,new Query<>(Optional.empty(),nativeFrontier))));
        for (NativeType candidate:sources) {
            ClassInfo type=candidate.type();Optional<Method> hash=candidate.hash();
            List<Gap> eligibility=new ArrayList<>(missingInput);eligibility.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),candidate.pending())));
            if(candidates.size()>=64) {effects.add(new Observe(Kind.DESERIALIZATION,"unexplored native member candidates",List.of(call.call().site()),List.of(Mechanisms.gap(call,GapKind.BUDGET,"conditional serialized type frontier (64)"))));break;}
            candidates.add(new Values.ClassValue("L"+type.name()+";",true,Optional.empty(),type.loader()));
            if (hash.isPresent() && !structure.decodedKeyPaths().isEmpty()) {
                for (JdkStructures.DecodedPath decodedPath : structure.decodedKeyPaths()) {
                    JdkStructures.Witness witness=decodedPath.witness();
                    List<Site> path=witness.sites();
                    Slot member=decodedPath.owner().equals("java/util/HashSet")?new SerializedIndex(0):new SerializedKey(0);
                    List<Effect> callback=new ArrayList<>();
                    callback.add(new Need(new InputNeed(decoded,Optional.empty(),NeedKind.RECEIVER_TYPE,"L"+decodedPath.owner()+";",List.of(new Values.ClassValue("L"+decodedPath.owner()+";",true)),"container required by decoded-key callback")));
                    callback.add(new Need(new InputNeed(decoded,Optional.of(member),NeedKind.SERIALIZED_MEMBERS,"L"+type.name()+";",List.of(new Values.ClassValue("L"+type.name()+";",true,Optional.empty(),type.loader())),"key/element required by this callback; map values do not trigger key hashing")));
                    callback.add(new Dispatch(hash.get().id(), new Symbolic(type.name(), "possible serialized container key/element; exact stream membership missing",decoded.source().map(s -> s.at(member)),type.loader()),
                            List.of(), Kind.CONTAINER_CALLBACK, Evidence.CONDITIONAL, path, unionIssues(call,eligibility,witness),ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
                    effects.add(new Alternative(effects.size(),new Local(callback)));
                }
            }
            for (Method method : candidate.hooks()) {
                MethodId id = method.id();
                boolean readObject = readObjectHook(method);
                boolean noData=noDataHook(method);
                boolean resolve = id.name().equals("readResolve") && id.descriptor().equals("()Ljava/lang/Object;") && !method.isStatic();
                boolean external = readExternalHook(method)
                        && !program.assignable(type.name(),type.loader(),"java/io/Externalizable",0).value().equals(Optional.of(false));
                if(!(readObject || noData || resolve || external))continue;
                ObjectValue instance=new ObjectValue(decoded.id(),type.name(),false,"conditional native hook receiver",false,decoded.source(),type.loader());
                List<Effect> hook=new ArrayList<>();
                hook.add(new Need(new InputNeed(decoded,Optional.empty(),NeedKind.RECEIVER_TYPE,"L"+type.name()+";",List.of(),"serialized receiver required by this native hook")));
                if(noData)hook.add(new Need(new InputNeed(instance,Optional.of(new ClassData(id.owner(),id.loader())),NeedKind.VALUE,"I",List.of(new Literal(0)),"readObjectNoData requires absent superclass data and no prior handle exception")));
                if(external) {
                    Optional<Method> constructor=program.declared(new MethodId(type.name(),"<init>","()V",type.loader()));
                    if(constructor.isEmpty() || !constructor.get().isPublic())continue;
                    JdkStructures.Witness protocol=structure.protocol("readExternal");
                    hook.add(new Dispatch(constructor.get().id(),instance,List.of(),Kind.DESERIALIZATION,Evidence.CONDITIONAL,protocol.sites(),protocolGaps(call,protocol),ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
                }
                if(readObject && call.receiver() instanceof ObjectValue stream) {
                    hook.add(new Write(stream,new HookReceiver(),Value.of(instance)));
                    hook.add(new Write(stream,new HookOwner(),Value.of(new Values.ClassValue("L"+id.owner()+";",true,Optional.empty(),id.loader()))));
                }
                JdkStructures.Witness protocol=structure.protocol(resolve?"readResolve":readObject?"readObject":noData?"readObjectNoData":"readExternal");
                List<Gap> hookGaps=new ArrayList<>(unionIssues(call,eligibility,protocol));
                if(protocol.sites().isEmpty())hookGaps.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"native hook dispatch structure is not verified"));
                hook.add(new Dispatch(id,instance,
                            resolve || noData ? List.of() : List.of(call.receiver()), Kind.DESERIALIZATION, Evidence.CONDITIONAL,
                            protocol.sites(),List.copyOf(hookGaps),resolve?ReturnFlow.TO_RESULT:ReturnFlow.IGNORE,ExceptionFlow.DIRECT));
                if(readObject && call.receiver() instanceof ObjectValue stream) {
                    hook.add(new Write(stream,new HookReceiver(),Value.NULL));hook.add(new Write(stream,new HookOwner(),Value.NULL));
                }
                hook.add(new Observe(Kind.DESERIALIZATION,"conditional native hook "+id,List.of(call.call().site()),missingInput));
                effects.add(new Alternative(effects.size(),new Local(hook)));
            }
        }
        effects.add(new Need(new InputNeed(call.receiver(),Optional.of(new Decoded()),NeedKind.SERIALIZED_MEMBERS,"Ljava/lang/Object;",candidates,"bind the decoded root and only the members consumed by this candidate; listed classes are possibilities")));
        if (structure.decodedKeyPaths().isEmpty())
            effects.add(new Observe(Kind.CONTAINER_CALLBACK, "target JDK serialized-key callback structure not verified", List.of(),
                    List.of(Mechanisms.gap(call, GapKind.UNSUPPORTED, "no verified readObject -> decoded key -> hashCode structure in target JDK"))));
        return new Local(effects);
    }
}
