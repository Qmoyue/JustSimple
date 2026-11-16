package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Mechanisms.*;
import java.util.*;

/** Small local value models used by the current input-to-dispatch flow. */
final class Library implements Model {
    private static final Map<String,String> PRIMITIVES=Map.of("java/lang/Integer","I","java/lang/Long","J","java/lang/Boolean","Z","java/lang/Byte","B",
            "java/lang/Character","C","java/lang/Short","S","java/lang/Float","F","java/lang/Double","D","java/lang/Void","V");
    private Optional<ObjectValue> runtime=Optional.empty();
    private Optional<ObjectValue> emptyMap=Optional.empty();
    private final int alternatives;
    Library(int alternatives){this.alternatives=alternatives;}
    static Optional<String> primitive(String type){return Optional.ofNullable(PRIMITIVES.get(type));}
    static Optional<Atom> staticField(FieldId field) {
        if(!field.name().equals("TYPE") || !field.descriptor().equals("Ljava/lang/Class;"))return Optional.empty();
        return Optional.ofNullable(PRIMITIVES.get(field.owner())).map(type -> new Values.ClassValue(type,true));
    }
    @Override public Optional<Local> apply(Invocation call, Bindings bindings, Program program) {
        MethodId api = call.call().target();
        if(call.is("java/util/AbstractMap","put","(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;")
                && program.type(api.owner()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent())
            return Optional.of(Local.of(new Raise("java/lang/UnsupportedOperationException")));
        if(call.is("java/util/Collections","emptyMap","()Ljava/util/Map;")) {
            if(emptyMap.isEmpty())emptyMap=singletonType(api,program).map(type -> new ObjectValue(call.result().id(),type,true,"platform empty-map singleton"));
            if(emptyMap.isPresent())return Optional.of(Local.of(new RequireNormal(List.of()),
                    new Write(emptyMap.get(),new Length(),Value.of(new Literal(0))),Mechanisms.result(emptyMap.get())));
        }
        boolean querySize=api.name().equals("size") && api.descriptor().equals("()I");
        boolean queryEmpty=api.name().equals("isEmpty") && api.descriptor().equals("()Z");
        if(querySize || queryEmpty) {
            Optional<ObjectValue> owner=call.receiver() instanceof CollectionView view?Optional.of(view.source()):
                    call.receiver() instanceof ObjectValue object && platformImplementation(call,object,program)
                        && (program.subtype(object.type(),"java/util/Collection") || program.subtype(object.type(),"java/util/Map"))?Optional.of(object):Optional.empty();
            if(owner.isPresent()) {
                Value lengths=bindings.read(owner.get(),new Length()).under(call.path());
                if(!lengths.empty()) {
                    Value result=Value.BOTTOM;
                    for(Bound length:lengths.alternatives()) {
                        Atom value=queryEmpty?length.atom() instanceof Literal l && l.value() instanceof Integer count?new Literal(count==0?1:0):new Unknown("collection emptiness is unspecified"):length.atom();
                        result=result.merge(Value.of(value,length.path()).requiring(length.gaps()).tracing(length.dependencies()));
                    }
                    return Optional.of(Local.of(new RequireNormal(List.of()),new Result(result)));
                }
            }
        }
        if(call.receiver() instanceof MapEntryValue entry && api.descriptor().equals("()Ljava/lang/Object;")) {
            if(api.name().equals("getKey"))return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(entry.key())));
            if(api.name().equals("getValue"))return Optional.of(Local.of(new RequireNormal(List.of()),new Result(bindings.read(entry.source(),new MapKey(entry.key())).under(call.path()))));
        }
        if(call.is("java/lang/Object","hashCode","()I"))return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new Unknown("identity hash value unspecified"))));
        if(call.is("java/lang/Object","equals","(Ljava/lang/Object;)Z") && call.receiver() instanceof ObjectValue receiver && call.arguments().get(0) instanceof ObjectValue other && receiver.exact() && other.exact())
            return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new Literal(receiver.id()==other.id()?1:0))));
        if(call.receiver() instanceof ObjectValue boxed && (call.is("java/lang/Integer","hashCode","()I") || call.is("java/lang/Integer","equals","(Ljava/lang/Object;)Z"))) {
            Value left=bindings.read(boxed,new Content()).under(call.path()),result=Value.BOTTOM;
            if(api.name().equals("hashCode"))result=left;
            else if(call.arguments().get(0) instanceof Literal nil && nil.value()==null)result=Value.of(new Literal(0));
            else if(call.arguments().get(0) instanceof ObjectValue other && other.type().equals("java/lang/Integer") && other.loader()==0) {
                int consumed=0;
                comparison:for(Bound a:left.alternatives())for(Bound b:bindings.read(other,new Content()).under(a.path()).alternatives()) {
                    if(consumed++>=64){result=result.merge(Value.of(new Truncated("integer equality binding budget (64)")).requiring(List.of(Mechanisms.gap(call,GapKind.BUDGET,"integer equality binding budget (64)"))));break comparison;}
                    if(a.atom() instanceof Literal x && x.value() instanceof Integer first && b.atom() instanceof Literal y && y.value() instanceof Integer second)
                        result=result.merge(Value.of(new Literal(first.equals(second)?1:0),b.path()).requiring(a.gaps()).requiring(b.gaps()).tracing(a.dependencies()).tracing(b.dependencies()));
                }
            } else if(call.arguments().get(0) instanceof Literal literal && literal.value() instanceof String)result=Value.of(new Literal(0));
            if(result.empty())result=Value.of(new Unknown("Integer content is not finite")).requiring(Mechanisms.unknown(call,"finite boxed Integer content is required"));
            return Optional.of(Local.of(new RequireNormal(List.of()),new Result(result)));
        }
        if(call.receiver() instanceof ObjectValue exception && (api.name().equals("getCause") && api.descriptor().equals("()Ljava/lang/Throwable;")
                || api.name().equals("getTargetException") && api.owner().equals("java/lang/reflect/InvocationTargetException") && api.descriptor().equals("()Ljava/lang/Throwable;")
                || api.name().equals("getException") && api.owner().equals("java/security/PrivilegedActionException") && api.descriptor().equals("()Ljava/lang/Exception;"))) {
            Query<Method> method=program.lookup(new MethodId(exception.type(),api.name(),api.descriptor()));
            if(method.value().flatMap(m -> program.type(m.id().owner())).filter(c -> c.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()) {
                String owner=method.value().orElseThrow().id().owner();
                if(Set.of("java/lang/Throwable","java/lang/reflect/InvocationTargetException","java/security/PrivilegedActionException").contains(owner)) {
                    String member=owner.equals("java/security/PrivilegedActionException")?"exception":"target";
                    Optional<FieldId> payload=program.fields(owner).stream().map(FieldInfo::id).filter(f -> f.name().equals(member) && f.descriptor().startsWith("L")).findFirst();
                    FieldId field=payload.orElse(new FieldId("java/lang/Throwable","cause","Ljava/lang/Throwable;"));
                    Value content=bindings.read(exception,new Field(field));
                    if(field.owner().equals("java/lang/Throwable") && field.name().equals("cause")) {
                        Value initialized=Value.BOTTOM;
                        for(Bound bound:content.alternatives())initialized=initialized.merge(Value.of(bound.atom().equals(exception)?new Literal(null):bound.atom(),bound.path()).requiring(bound.gaps()).tracing(bound.dependencies()));
                        content=initialized;
                    }
                    return Optional.of(Local.of(new RequireNormal(List.of()),new Result(content.requiring(Mechanisms.queryGaps(call,method)))));
                }
            }
        }
        if(api.name().equals("iterator") && api.descriptor().equals("()Ljava/util/Iterator;")) {
            if(call.receiver() instanceof CollectionView view)return iterator(call,bindings,view.source(),view.elements());
            if(call.receiver() instanceof ObjectValue receiver && platformImplementation(call,receiver,program)
                    && program.subtype(receiver.type(),"java/util/Collection"))return iterator(call,bindings,receiver,new Elements());
            return Optional.empty();
        }
        if (call.receiver() instanceof ObjectValue receiver) {
            if(receiver.exact() && receiver.loader()==0 && receiver.type().equals("java/util/Stack") && api.owner().equals("java/util/Stack")
                    && program.type(api.owner(),api.loader()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()) {
                Optional<Local> operation=stack(call,bindings,receiver);if(operation.isPresent())return operation;
            }
            if(call.is("java/util/ArrayList","add","(Ljava/lang/Object;)Z")) {
                Value lengths=bindings.read(receiver,new Length()).under(call.path());
                if(lengths.empty())lengths=Value.of(new Unknown("list length is unspecified"),call.path());
                List<Effect> effects=new ArrayList<>();
                for(Bound length:lengths.alternatives()) {
                    List<Effect> branch=new ArrayList<>();branch.add(new RequireNormal(List.of()));
                    Atom next=new Unknown("list length after add is unspecified");
                    if(length.atom() instanceof Literal l && l.value() instanceof Integer count && count>=0 && count<Integer.MAX_VALUE) {
                        branch.add(new Write(receiver,new Index(count),Value.of(call.arguments().get(0))));next=new Literal(count+1);
                    }
                    branch.add(new Write(receiver,new Elements(),Value.of(call.arguments().get(0))));
                    branch.add(new Write(receiver,new Length(),Value.of(next)));
                    branch.add(Mechanisms.result(new Literal(1)));
                    effects.add(new Conditional(length.path(),length.gaps(),length.dependencies(),new Local(branch)));
                }
                return Optional.of(new Local(effects));
            }
            if (api.name().equals("<init>") && api.descriptor().equals("(I)V")
                    && Set.of("java/util/HashMap","java/util/ArrayList").contains(api.owner())) {
                Atom capacity=call.arguments().get(0);
                if (capacity instanceof Literal literal && literal.value() instanceof Number number) {
                    if (number.intValue()<0) return Optional.of(Local.of(new Raise("java/lang/IllegalArgumentException")));
                    return Optional.of(Local.of(new RequireNormal(List.of()),new Write(receiver,new Length(),Value.of(new Literal(0))),new Result(Value.NULL)));
                }
                return Optional.of(Local.of(new RequireNormal(List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"constructor requires nonnegative capacity"))),
                        new Write(receiver,new Length(),Value.of(new Literal(0))),new Result(Value.NULL)));
            }
            if (api.name().equals("<init>") && Set.of("java/util/HashMap","java/util/LinkedHashMap","java/util/ArrayList").contains(api.owner()) && api.descriptor().equals("()V"))
                return Optional.of(Local.of(new RequireNormal(List.of()),new Write(receiver,new Length(),Value.of(new Literal(0))),new Result(Value.NULL)));
            if (call.is("java/util/LinkedHashMap","<init>","(IFZ)V")) {
                Atom capacity=call.arguments().get(0),factor=call.arguments().get(1);
                boolean known=capacity instanceof Literal c && c.value() instanceof Number && factor instanceof Literal f && f.value() instanceof Number;
                if (capacity instanceof Literal c && c.value() instanceof Number capacityNumber && capacityNumber.intValue()<0
                        || factor instanceof Literal f && f.value() instanceof Number factorNumber && !(factorNumber.floatValue()>0))
                    return Optional.of(Local.of(new Raise("java/lang/IllegalArgumentException")));
                List<Effect> effects=new ArrayList<>();
                effects.add(new RequireNormal(known?List.of():List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"constructor requires nonnegative capacity and positive load factor"))));
                effects.add(new Write(receiver,new Length(),Value.of(new Literal(0))));
                effects.add(new Write(receiver,new Field(new FieldId("java/util/LinkedHashMap","accessOrder","Z")),Value.of(call.arguments().get(2))));
                effects.add(new Result(Value.NULL)); return Optional.of(new Local(effects));
            }
            if (api.name().equals("<init>") && api.owner().equals("java/util/TreeMap")
                    && (api.descriptor().equals("()V") || api.descriptor().equals("(Ljava/util/Comparator;)V")))
                return Optional.of(Local.of(new RequireNormal(List.of()),new Write(receiver,new Field(new FieldId("java/util/TreeMap","comparator","Ljava/util/Comparator;")),
                        Value.of(call.arguments().isEmpty()?new Literal(null):call.arguments().get(0))),new Result(Value.NULL)));

            if (call.is("java/io/ByteArrayInputStream","<init>","([B)V") || call.is("java/io/ObjectInputStream","<init>","(Ljava/io/InputStream;)V")) {
                Atom source=call.arguments().get(0);
                if(source instanceof Literal literal && literal.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
                boolean array=api.owner().equals("java/io/ByteArrayInputStream");
                List<Gap> normal=array && source instanceof ObjectValue object && object.exact()?List.of():List.of(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,
                        array?"byte stream requires a nonnull buffer":"object stream header and source completion are not verified"));
                return Optional.of(Local.of(new RequireNormal(normal),new Write(receiver,new Content(),Value.of(source,call.path())),new Result(Value.NULL)));
            }
            boolean valueView=api.name().equals("values") && api.descriptor().equals("()Ljava/util/Collection;");
            boolean entryView=api.name().equals("entrySet") && api.descriptor().equals("()Ljava/util/Set;");
            boolean keyView=api.name().equals("keySet") && api.descriptor().equals("()Ljava/util/Set;");
            if ((valueView || entryView || keyView) && program.subtype(receiver.type(),"java/util/Map")) {
                Slot members=entryView?new MapEntries():keyView?new Elements():new MapValues();String view=valueView?"java/util/Collection":"java/util/Set";
                if(platformImplementation(call,receiver,program))return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new CollectionView(call.result().id(),view,receiver,members))));
                else if(!receiver.exact() && receiver.source().isPresent()) {
                    program.type("java/util/HashMap"); // Expose a supported possibility to ordinary virtual dispatch.
                    return Optional.empty();
                } else return Optional.empty();
            }
            if ((call.is("java/util/Iterator","hasNext","()Z") || call.is("java/util/Iterator","next","()Ljava/lang/Object;")) && !bindings.read(receiver,new Cursor()).empty()) {
                List<Effect> effects=new ArrayList<>();
                Value cursors=bindings.read(receiver,new Cursor()).under(call.path());
                if (api.name().equals("hasNext")) {
                    Value result=Value.BOTTOM;
                    for (Bound cursor:cursors.alternatives()) for (Bound length:bindings.read(receiver,new Length()).under(cursor.path()).alternatives())
                        if (cursor.atom() instanceof Literal c && c.value() instanceof Integer index && length.atom() instanceof Literal l && l.value() instanceof Integer size)
                            result=result.merge(Value.of(new Literal(index<size?1:0),length.path()).requiring(cursor.gaps()).requiring(length.gaps()).tracing(cursor.dependencies()).tracing(length.dependencies()));
                    return Optional.of(Local.of(new Result(result.empty()?Value.of(new Unknown("iterator bound is unspecified")):result)).onModelState());
                }
                for(Bound cursor:cursors.alternatives()) {
                    Value lengths=bindings.read(receiver,new Length()).under(cursor.path());
                    if(lengths.empty())lengths=Value.of(new Unknown("iterator length unspecified"),cursor.path());
                    for(Bound length:lengths.alternatives()) {
                        OptionalInt index=cursor.atom() instanceof Literal c && c.value() instanceof Integer n?OptionalInt.of(n):OptionalInt.empty();
                        OptionalInt size=length.atom() instanceof Literal l && l.value() instanceof Integer n?OptionalInt.of(n):OptionalInt.empty();
                        List<Gap> gaps=new ArrayList<>(cursor.gaps());gaps.addAll(length.gaps());
                        Set<Integer> dependencies=new LinkedHashSet<>(cursor.dependencies());dependencies.addAll(length.dependencies());
                        if(index.isPresent() && size.isPresent() && index.getAsInt()>=size.getAsInt()) {
                            effects.add(new Conditional(length.path(),gaps,dependencies,Local.of(new Raise("java/util/NoSuchElementException"))));continue;
                        }
                        List<Gap> normal=index.isPresent() && size.isPresent()?List.of():Mechanisms.unknown(call,"iterator cursor must be below its current length");
                        Slot slot=index.isPresent()?new Index(index.getAsInt()):new Elements();
                        Value values=bindings.read(receiver,slot).under(length.path());
                        if(values.empty())values=bindings.read(receiver,new Elements()).under(length.path());
                        List<Effect> branch=new ArrayList<>();branch.add(new RequireNormal(normal));
                        if(values.empty()) {
                            Gap required=Mechanisms.gap(call,GapKind.INPUT_BINDING,"same iterator member and position are unspecified: "+slot);
                            branch.add(new Need(new InputNeed(receiver,Optional.of(slot),NeedKind.SERIALIZED_MEMBERS,"Ljava/lang/Object;",List.of(),required.detail())));
                            values=Value.of(new ObjectValue(call.result().id(),"java/lang/Object",false,"conditional iterator element",false,receiver.source().map(s -> s.at(slot))),length.path()).requiring(List.of(required));
                        }
                        if(index.isPresent())branch.add(new Write(receiver,new Cursor(),Value.of(new Literal(index.getAsInt()+1))));
                        branch.add(new Result(values.requiring(normal)));
                        effects.add(new Conditional(length.path(),gaps,dependencies,new Local(branch)));
                    }
                }
                return Optional.of(new Local(effects).onModelState());
            }
            if (api.name().equals("<init>") && api.descriptor().equals("()V")
                    && Set.of("java/lang/Object", "java/util/HashSet").contains(api.owner()))
                return Optional.of(api.owner().equals("java/util/HashSet")?Local.of(new RequireNormal(List.of()),new Write(receiver,new Length(),Value.of(new Literal(0))),new Result(Value.NULL)):Local.of(new RequireNormal(List.of()),new Result(Value.NULL)));

        }
        if (call.is("java/util/Arrays","asList","([Ljava/lang/Object;)Ljava/util/List;")) {
            if(call.arguments().get(0) instanceof Literal l && l.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if(call.arguments().get(0) instanceof ObjectValue array)return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(new CollectionView(call.result().id(),"java/util/List",array,new Elements()))));
        }
        if (api.owner().equals("java/util/Base64") && Set.of("getDecoder","getUrlDecoder","getMimeDecoder").contains(api.name())
                && api.descriptor().equals("()Ljava/util/Base64$Decoder;")
                && program.type(api.owner(),api.loader()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent())
            return Optional.of(Local.of(new Write(call.result(),new DecoderKind(),Value.of(new Literal(api.name()))),Mechanisms.result(call.result())));
        if (call.is("java/util/Base64$Decoder", "decode", "(Ljava/lang/String;)[B")) {
            Atom input=call.arguments().get(0);
            if(input instanceof Literal literal && literal.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if(input instanceof Literal literal && literal.value() instanceof String encoded && encoded.length()<=87384
                    && call.receiver() instanceof ObjectValue decoder
                    && program.type(api.owner(),api.loader()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()) {
                List<Effect> choices=new ArrayList<>();boolean complete=true;
                for(Bound kind:bindings.read(decoder,new DecoderKind()).under(call.path()).alternatives()) {
                    if(!(kind.atom() instanceof Literal selected) || !(selected.value() instanceof String name)){complete=false;break;}
                    Base64.Decoder codec=switch(name) {case "getDecoder" -> Base64.getDecoder();case "getUrlDecoder" -> Base64.getUrlDecoder();case "getMimeDecoder" -> Base64.getMimeDecoder();default -> null;};
                    if(codec==null){complete=false;break;}
                    Local decoded;
                    try {
                        byte[] bytes=codec.decode(encoded);List<Effect> effects=new ArrayList<>();
                        effects.add(new RequireNormal(List.of()));effects.add(new Write(call.result(),new Content(),Value.of(input,call.path())));
                        effects.add(new Write(call.result(),new Length(),Value.of(new Literal(bytes.length))));
                        for(int i=0;i<bytes.length;i++)effects.add(new Write(call.result(),new Index(i),Value.of(new Literal((int)bytes[i]))));
                        effects.add(Mechanisms.result(call.result()));decoded=new Local(effects);
                    } catch(IllegalArgumentException invalid) {decoded=Local.of(new Raise("java/lang/IllegalArgumentException"));}
                    choices.add(new Conditional(kind.path(),kind.gaps(),kind.dependencies(),decoded));
                }
                if(complete && !choices.isEmpty())return Optional.of(new Local(choices).onModelState());
            }
            return Optional.of(Local.of(new RequireNormal(Mechanisms.unknown(call,"Base64 input must be nonnull and valid")),Mechanisms.result(call.result()), new Write(call.result(), new Content(), Value.of(input, call.path()))));
        }
        if (call.is("java/lang/Runtime", "getRuntime", "()Ljava/lang/Runtime;")) {
            if(runtime.isEmpty())runtime=Optional.of(new ObjectValue(call.result().id(), "java/lang/Runtime", true, "Runtime.getRuntime API result"));
            return Optional.of(Local.of(new RequireNormal(List.of()),Mechanisms.result(runtime.orElseThrow())));
        }
        String primitive=PRIMITIVES.get(api.owner());
        if(primitive!=null && !primitive.equals("V") && api.name().equals("valueOf") && api.descriptor().equals("("+primitive+")L"+api.owner()+";")
                && program.type(api.owner(),api.loader()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()) {
            Atom content=call.arguments().get(0);
            if(content instanceof Literal literal && literal.value() instanceof Number number)content=switch(primitive) {
                case "Z" -> new Literal(number.intValue()!=0);case "B" -> new Literal(number.byteValue());
                case "S" -> new Literal(number.shortValue());case "C" -> new Literal((char)number.intValue());default -> content;
            };
            return Optional.of(Local.of(new RequireNormal(List.of()),new Write(call.result(),new Content(),Value.of(content)),Mechanisms.result(call.result())));
        }
        return Optional.empty();
    }
    private Optional<Local> stack(Invocation call,Bindings bindings,ObjectValue receiver) {
        MethodId api=call.call().target();
        if(api.name().equals("<init>") && api.descriptor().equals("()V"))
            return Optional.of(Local.of(new RequireNormal(List.of()),new Write(receiver,new Length(),Value.of(new Literal(0))),new Result(Value.NULL)));
        boolean push=api.name().equals("push") && api.descriptor().equals("(Ljava/lang/Object;)Ljava/lang/Object;");
        boolean pop=api.name().equals("pop") && api.descriptor().equals("()Ljava/lang/Object;");
        boolean peek=api.name().equals("peek") && api.descriptor().equals("()Ljava/lang/Object;");
        boolean empty=api.name().equals("empty") && api.descriptor().equals("()Z");
        if(!push && !pop && !peek && !empty)return Optional.empty();
        Value lengths=bindings.read(receiver,new Length()).under(call.path());
        if(lengths.empty() || lengths.alternatives().stream().anyMatch(bound -> !(bound.atom() instanceof Literal literal && literal.value() instanceof Integer n && n>=0 && (!push || n<Integer.MAX_VALUE))))return Optional.empty();
        List<Effect> effects=new ArrayList<>();
        for(Bound length:lengths.alternatives()) {
            int size=(Integer)((Literal)length.atom()).value();List<Effect> branch=new ArrayList<>();
            if((pop || peek) && size==0)branch.add(new Raise("java/util/EmptyStackException"));
            else {
                branch.add(new RequireNormal(List.of()));
                if(push) {
                    branch.add(new Write(receiver,new Index(size),Value.of(call.arguments().get(0))));
                    branch.add(new Write(receiver,new Length(),Value.of(new Literal(size+1))));
                    branch.add(Mechanisms.result(call.arguments().get(0)));
                } else if(empty)branch.add(Mechanisms.result(new Literal(size==0?1:0)));
                else {
                    Slot slot=new Index(size-1);Value member=bindings.read(receiver,slot).under(length.path());
                    if(member.empty()) {
                        Gap gap=Mechanisms.gap(call,GapKind.INPUT_BINDING,"stack member at its current top is unspecified");
                        branch.add(new Need(new InputNeed(receiver,Optional.of(slot),NeedKind.VALUE,"Ljava/lang/Object;",List.of(),gap.detail())));
                        member=Value.of(new Unknown(gap.detail()),length.path()).requiring(List.of(gap));
                    }
                    if(pop)branch.add(new Write(receiver,new Length(),Value.of(new Literal(size-1))));
                    branch.add(new Result(member));
                }
            }
            effects.add(new Conditional(length.path(),length.gaps(),length.dependencies(),new Local(branch)));
        }
        return Optional.of(new Local(effects));
    }
    private static boolean platformImplementation(Invocation call,ObjectValue receiver,Program program) {
        Query<Method> actual=program.lookup(program.method(receiver.type(),call.call().target().name(),call.call().target().descriptor(),receiver.loader()));
        return actual.pending().isEmpty() && actual.value().filter(Method::hasBody)
                .flatMap(m -> program.type(m.id().owner(),m.id().loader())).filter(t -> t.role()==io.just.input.Inputs.Role.PLATFORM).isPresent();
    }
    /** Follow the selected platform's final static singleton, without naming a private implementation. */
    private static Optional<String> singletonType(MethodId factory,Program program) {
        if(program.type(factory.owner()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        Facts facts=program.facts(factory);
        if(!facts.limitations().isEmpty() || facts.actions().stream().anyMatch(action -> !(action instanceof ReadField || action instanceof Returned)))return Optional.empty();
        for(Action action:facts.actions())if(action instanceof Returned returned && returned.value().origins().size()==1)
            for(Origin origin:returned.value().origins())if(origin instanceof Producer producer
                    && program.flow(factory).producers().get(producer.instruction()) instanceof ReadField read && read.receiver().origins().isEmpty()
                    && program.fields(read.field().owner()).stream().anyMatch(field -> field.id().equals(read.field()) && (field.access() & org.objectweb.asm.Opcodes.ACC_FINAL)!=0)) {
                MethodId initializer=new MethodId(read.field().owner(),"<clinit>","()V");Facts initialization=program.facts(initializer);
                if(!initialization.limitations().isEmpty())return Optional.empty();
                for(Action initialized:initialization.actions())if(initialized instanceof WriteField write && write.field().equals(read.field()) && write.value().origins().size()==1)
                    for(Origin value:write.value().origins())if(value instanceof Producer allocation
                            && program.flow(initializer).producers().get(allocation.instruction()) instanceof Allocate object)return Optional.of(object.type());
            }
        return Optional.empty();
    }
    private Optional<Local> iterator(Invocation call,Bindings bindings,ObjectValue base,Slot summary) {
        Value keys=summary instanceof MapEntries?bindings.read(base,new Elements()).under(call.path()):Value.BOTTOM;
        Value elements=summary instanceof MapEntries?new Value(keys.alternatives().stream().map(b -> new Bound(new MapEntryValue(base,b.atom()),b.path(),b.gaps(),b.dependencies())).collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new))):bindings.read(base,summary).under(call.path());
        List<Effect> effects=new ArrayList<>();Value lengths=bindings.read(base,new Length());
        if(summary instanceof MapEntries)for(Bound key:keys.alternatives())for(Bound position:bindings.read(base,new KeyIndex(key.atom())).under(key.path()).alternatives())
            if(position.atom() instanceof Literal literal && literal.value() instanceof Integer index)
                effects.add(new Write(call.result(),new Index(index),Value.of(new MapEntryValue(base,key.atom()),position.path()).requiring(key.gaps()).requiring(position.gaps()).tracing(key.dependencies()).tracing(position.dependencies())));
        if(lengths.empty() && base.source().isPresent()) {
            Gap order=Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"iterator membership, length and order are conditional on this source object");
            elements=elements.requiring(List.of(order));
            effects.add(new Need(new InputNeed(base,Optional.of(new Length()),NeedKind.VALUE,"I",List.of(),"number of source members required by the selected iteration prefix")));
            effects.add(new Need(new InputNeed(base,Optional.of(new IterationOrder()),NeedKind.SERIALIZED_MEMBERS,"Ljava/util/Collection;",List.of(),order.detail())));
            effects.add(new RequireNormal(List.of(order)));
        }
        effects.add(new Write(call.result(),new Length(),lengths));
        Value order=bindings.read(base,new IterationOrder());
        if(!order.empty())elements=elements.requiring(order.alternatives().stream().flatMap(b -> b.gaps().stream()).distinct().toList());
        else if(!(summary instanceof MapEntries))for(Bound length:lengths.alternatives())if(length.atom() instanceof Literal value && value.value() instanceof Integer size && size>=0)
            for(int i=0;i<Math.min(size,alternatives);i++) {
                Value indexed=bindings.read(base,new Index(i)).under(length.path()).requiring(length.gaps()).tracing(length.dependencies());
                if(!indexed.empty())effects.add(new Write(call.result(),new Index(i),indexed));
            }
        ObjectValue iterator=new ObjectValue(call.result().id(),call.result().type(),false,call.result().origin(),false,base.source().map(s -> s.at(summary)));
        effects.add(Mechanisms.result(iterator));effects.add(new Write(iterator,new Elements(),elements));
        effects.add(new Write(iterator,new Cursor(),Value.of(new Literal(0))));effects.add(new Iterate(iterator));
        return Optional.of(new Local(effects));
    }
}
