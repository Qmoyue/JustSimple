package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import java.util.*;

/** Finite, lazy bytecode verifications scoped to the selected program. No scan bindings or queue. */
final class JdkStructures {
    record Witness(List<Site> sites,List<QueryIssue> pending) {
        Witness {sites=List.copyOf(sites);pending=List.copyOf(pending);}
    }
    record DecodedPath(String owner,Witness witness) {}
    private enum Shape { PUT_HASH,PUT_EQUALS,GET_HASH,GET_EQUALS,LINKED_HASH,LINKED_EQUALS,COMPARE,STRING,SET_ADD }
    private enum Hook { OBJECT,EXTERNAL,RESOLVE,NO_DATA }
    private record Work(MethodId method,int slot,List<Site> path) {}
    private final Program program;
    private final EnumMap<Shape,Witness> paths=new EnumMap<>(Shape.class);
    private final EnumMap<Hook,Witness> protocols=new EnumMap<>(Hook.class);
    private Optional<List<DecodedPath>> decoded=Optional.empty();
    enum FieldOrder { PRIMITIVES_FIRST, AFTER_MEMBERS, UNKNOWN }
    record FieldTiming(FieldOrder order,Witness witness) {}
    private Optional<FieldTiming> timing=Optional.empty();
    private Optional<Witness> naming=Optional.empty();
    private static final MethodId PUT=new MethodId("java/util/HashMap","put","(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");
    JdkStructures(Program program) {this.program=program;}
    /** Verify the local Reference branch, including exact forwarding and legacy construction. */
    Witness namingFactory() {
        if(naming.isPresent())return naming.get();
        String descriptor="(Ljava/lang/Object;Ljavax/naming/Name;Ljavax/naming/Context;Ljava/util/Hashtable;)Ljava/lang/Object;";
        MethodId root=new MethodId("javax/naming/spi/NamingManager","getObjectInstance",descriptor);
        ArrayDeque<Work> work=new ArrayDeque<>(List.of(new Work(root,0,List.of())));Set<MethodId> seen=new HashSet<>();List<QueryIssue> issues=new ArrayList<>();
        while(!work.isEmpty() && seen.size()<8) {
            Work current=work.removeFirst();if(!seen.add(current.method()))continue;
            if(program.type(current.method().owner()).filter(c -> c.role()==io.just.input.Inputs.Role.PLATFORM).isEmpty())continue;
            Optional<Facts> available=facts(current.method(),issues);if(available.isEmpty())continue;Facts body=available.get();
            List<Call> calls=body.actions().stream().filter(a -> a instanceof Call).map(a -> (Call)a).toList();
            for(Call name:calls)if(name.target().equals(new MethodId("javax/naming/Reference","getFactoryClassName","()Ljava/lang/String;")) && directReference(name.receiver(),body))
                for(Call select:calls)if(select.target().name().equals("getObjectFactoryFromReference") && select.target().owner().equals(current.method().owner()) && select.arguments().size()>=2
                        && select.arguments().get(0).equals(name.receiver()) && producer(select.arguments().get(1),body,new HashSet<>()).filter(name::equals).isPresent())
                    for(Call dispatch:calls)if(dispatch.target().equals(new MethodId("javax/naming/spi/ObjectFactory","getObjectInstance",descriptor)) && dispatch.arguments().get(0).equals(name.receiver())
                            && producer(dispatch.receiver(),body,new HashSet<>()).filter(select::equals).isPresent()
                            && java.util.stream.IntStream.range(1,4).allMatch(i -> fromParameter(dispatch.arguments().get(i),i,body,new HashSet<>()))
                            && mustPrecede(name.site().instruction(),select.site().instruction(),body,Set.of(0)) && mustPrecede(select.site().instruction(),dispatch.site().instruction(),body,Set.of(0))) {
                        Optional<Facts> factory=facts(select.target(),issues);if(factory.isEmpty())continue;
                        for(Action action:factory.get().actions())if(action instanceof Call construction && construction.target().equals(new MethodId("java/lang/Class","newInstance","()Ljava/lang/Object;"))) {
                            List<Site> loads=new ArrayList<>();boolean compatible=true;
                            for(Origin origin:construction.receiver().origins()) {
                                Action source=origin instanceof Producer p?program.flow(factory.get().method().id()).producers().get(p.instruction()):null;
                                if(source instanceof Constant c && c.value() instanceof LiteralConstant literal && literal.value()==null)continue;
                                if(source instanceof Call load && Set.of("loadClass","loadClassWithoutInit").contains(load.target().name()) && !load.arguments().isEmpty() && fromParameter(load.arguments().get(0),1,factory.get(),new HashSet<>()))loads.add(load.site());
                                else compatible=false;
                            }
                            if(compatible && !loads.isEmpty()) {
                                List<Site> sites=new ArrayList<>(current.path());sites.addAll(List.of(name.site(),select.site(),dispatch.site()));sites.addAll(loads);sites.add(construction.site());
                                Witness result=new Witness(sites,issues);naming=Optional.of(result);return result;
                            }
                        }
                    }
            if(current.path().size()<3)for(Call delegate:calls)if(delegate.target().name().equals("getObjectInstance") && delegate.arguments().size()>=4
                    && java.util.stream.IntStream.range(0,4).allMatch(i -> fromParameter(delegate.arguments().get(i),i,body,new HashSet<>()))) {
                List<Site> path=new ArrayList<>(current.path());path.add(delegate.site());work.addLast(new Work(delegate.target(),0,List.copyOf(path)));
            }
        }
        if(!work.isEmpty())issues.add(new QueryIssue(QueryCause.BUDGET,"local JNDI structure frontier budget (8)"));
        Witness result=new Witness(List.of(),issues);naming=Optional.of(result);return result;
    }
    private boolean directReference(Sources source,Facts facts) {
        for(Origin origin:source.origins())if(origin instanceof Producer p && program.flow(facts.method().id()).producers().get(p.instruction()) instanceof Cast cast
                && cast.type().equals("javax/naming/Reference") && fromParameter(cast.input(),0,facts,new HashSet<>()))return true;
        return false;
    }
    List<ClassInfo> targets() {return program.candidates();}
    FieldTiming fieldTiming() {
        if(timing.isPresent())return timing.get();
        List<QueryIssue> pending=new ArrayList<>();List<Site> sites=new ArrayList<>();FieldOrder order=FieldOrder.UNKNOWN;
        Query<Method> legacy=program.lookup(new MethodId("java/io/ObjectInputStream","defaultReadFields","(Ljava/lang/Object;Ljava/io/ObjectStreamClass;)V"));pending.addAll(legacy.pending());
        if(legacy.value().isPresent()) {
            Optional<Facts> available=facts(legacy.value().get().id(),pending);
            List<Call> calls=available.map(Facts::actions).orElse(List.of()).stream().filter(a -> a instanceof Call).map(a -> (Call)a).toList();
            Optional<Call> primitive=calls.stream().filter(c -> c.target().owner().equals("java/io/ObjectStreamClass") && c.target().name().equals("setPrimFieldValues")).findFirst();
            Optional<Call> member=calls.stream().filter(c -> c.target().owner().equals("java/io/ObjectInputStream") && c.target().name().equals("readObject0")).findFirst();
            Optional<Call> object=calls.stream().filter(c -> c.target().owner().equals("java/io/ObjectStreamClass") && c.target().name().equals("setObjFieldValues")).findFirst();
            if(primitive.isPresent() && member.isPresent() && object.isPresent() && available.isPresent()
                    && fromParameter(primitive.get().receiver(),2,available.get(),new HashSet<>()) && fromParameter(object.get().receiver(),2,available.get(),new HashSet<>())
                    && fromParameter(primitive.get().arguments().get(0),1,available.get(),new HashSet<>()) && fromParameter(object.get().arguments().get(0),1,available.get(),new HashSet<>())
                    && fromParameter(member.get().receiver(),0,available.get(),new HashSet<>())
                    && mustPrecede(primitive.get().site().instruction(),member.get().site().instruction(),available.get(),Set.of(0,1,2))
                    && ordered(member.get().site().instruction(),object.get().site().instruction(),available.get(),Set.of(0,1,2))) {
                order=FieldOrder.PRIMITIVES_FIRST;sites.addAll(List.of(primitive.get().site(),member.get().site(),object.get().site()));
            }
        } else {
            Query<Method> modern=program.lookup(new MethodId("java/io/ObjectInputStream","defaultReadObject","()V"));pending.addAll(modern.pending());
            if(modern.value().isPresent()) {
                Optional<Facts> available=facts(modern.value().get().id(),pending);
                List<Call> calls=available.map(Facts::actions).orElse(List.of()).stream().filter(a -> a instanceof Call).map(a -> (Call)a).toList();
                Optional<Call> read=calls.stream().filter(c -> c.target().owner().equals("java/io/ObjectInputStream$FieldValues") && c.target().name().equals("<init>")).findFirst();
                Optional<Call> set=calls.stream().filter(c -> c.target().owner().equals("java/io/ObjectInputStream$FieldValues") && c.target().name().equals("defaultSetFieldValues")).findFirst();
                if(read.isPresent() && set.isPresent() && available.isPresent() && read.get().receiver().origins().equals(set.get().receiver().origins()) && mustPrecede(read.get().site().instruction(),set.get().site().instruction(),available.get(),Set.of(0))) {
                    order=FieldOrder.AFTER_MEMBERS;sites.addAll(List.of(read.get().site(),set.get().site()));
                }
            }
        }
        FieldTiming found=new FieldTiming(order,new Witness(sites,pending));timing=Optional.of(found);return found;
    }
    Witness hashKeyPath(){return path(Shape.PUT_HASH);}
    Witness equalsKeyPath(){return path(Shape.PUT_EQUALS);}
    Witness getHashKeyPath(){return path(Shape.GET_HASH);}
    Witness getEqualsKeyPath(){return path(Shape.GET_EQUALS);}
    Witness linkedGetHashPath(){return path(Shape.LINKED_HASH);}
    Witness linkedGetEqualsPath(){return path(Shape.LINKED_EQUALS);}
    Witness compareKeyPath(){return path(Shape.COMPARE);}
    Witness stringPath(){return path(Shape.STRING);}
    Witness setAddPath(){return path(Shape.SET_ADD);}
    private Witness path(Shape shape) {
        Witness existing=paths.get(shape);if(existing!=null)return existing;
        Witness result;
        if(shape==Shape.SET_ADD) {
            Witness hash=hashKeyPath();List<Site> sites=new ArrayList<>();List<QueryIssue> issues=new ArrayList<>(hash.pending());
            MethodId add=new MethodId("java/util/HashSet","add","(Ljava/lang/Object;)Z");
            if(!hash.sites().isEmpty())for(Action action:facts(add,issues).map(Facts::actions).orElse(List.of()))
                if(action instanceof Call call && call.target().equals(PUT) && call.arguments().get(0).parameter(1)) {sites.add(call.site());sites.addAll(hash.sites());break;}
            result=new Witness(sites,issues);
        } else if(shape==Shape.STRING) {
            List<Site> sites=new ArrayList<>();List<QueryIssue> issues=new ArrayList<>();MethodId valueOf=new MethodId("java/lang/String","valueOf","(Ljava/lang/Object;)Ljava/lang/String;");
            for(Action action:facts(valueOf,issues).map(Facts::actions).orElse(List.of()))
                if(action instanceof Call call && call.target().equals(new MethodId("java/lang/Object","toString","()Ljava/lang/String;")) && call.receiver().parameter(0))sites.add(call.site());
            result=new Witness(sites,issues);
        } else {
            boolean equality=Set.of(Shape.PUT_EQUALS,Shape.GET_EQUALS,Shape.LINKED_EQUALS).contains(shape);
            boolean get=Set.of(Shape.GET_HASH,Shape.GET_EQUALS,Shape.LINKED_HASH,Shape.LINKED_EQUALS).contains(shape);
            String owner=shape==Shape.COMPARE?"java/util/TreeMap":Set.of(Shape.LINKED_HASH,Shape.LINKED_EQUALS).contains(shape)?"java/util/LinkedHashMap":"java/util/HashMap";
            MethodId root=new MethodId(owner,get?"get":"put",get?"(Ljava/lang/Object;)Ljava/lang/Object;":"(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");
            MethodId callback=shape==Shape.COMPARE?new MethodId("java/lang/Comparable","compareTo","(Ljava/lang/Object;)I")
                    :new MethodId("java/lang/Object",equality?"equals":"hashCode",equality?"(Ljava/lang/Object;)Z":"()I");
            result=keyCallback(root,1,callback);
        }
        paths.put(shape,result);return result;
    }
    List<DecodedPath> decodedKeyPaths() {
        if(decoded.isPresent())return decoded.get();
        Witness hash=hashKeyPath();List<DecodedPath> paths=new ArrayList<>();
        for(String type:List.of("java/util/HashSet","java/util/HashMap")) {
            MethodId read=new MethodId(type,"readObject","(Ljava/io/ObjectInputStream;)V");
            List<QueryIssue> issues=new ArrayList<>();Optional<Facts> query=facts(read,issues);
            if(query.isEmpty() || !query.get().limitations().isEmpty()) {
                if(!issues.isEmpty())paths.add(new DecodedPath(type,new Witness(List.of(),issues)));
                continue;
            }
            Facts facts=query.get();
            Map<Integer,Call> calls=new HashMap<>();for(Action action:facts.actions())if(action instanceof Call call)calls.put(call.site().instruction(),call);
            for(Call call:calls.values()) {
                if(!(call.target().equals(PUT) || call.target().equals(new MethodId("java/util/HashMap","hash","(Ljava/lang/Object;)I"))) || call.arguments().isEmpty())continue;
                Optional<Action> decoded=producer(call.arguments().get(0),facts,new HashSet<>());
                if(decoded.isEmpty() || !(decoded.get() instanceof Call source) || !Serialization.read(source.target())
                        || !fromParameter(source.receiver(),1,facts,new HashSet<>())
                        || !precedes(source.site().instruction(),call.site().instruction(),facts,Set.of(0,1)))continue;
                Witness suffix=call.target().equals(PUT)?hash:keyCallback(call.target(),0,new MethodId("java/lang/Object","hashCode","()I"));
                List<Site> sites=new ArrayList<>(List.of(source.site(),call.site()));sites.addAll(suffix.sites());
                List<QueryIssue> pending=new ArrayList<>(issues);pending.addAll(suffix.pending());
                if(!suffix.sites().isEmpty() || !pending.isEmpty())paths.add(new DecodedPath(type,new Witness(sites,pending)));
            }
        }
        decoded=Optional.of(List.copyOf(paths));return decoded.get();
    }
    Witness protocol(String hookName) {
        Hook hook=switch(hookName){case "readObject" -> Hook.OBJECT;case "readExternal" -> Hook.EXTERNAL;case "readResolve" -> Hook.RESOLVE;case "readObjectNoData" -> Hook.NO_DATA;default -> throw new IllegalArgumentException("unsupported hook: "+hookName);};
        return protocols.computeIfAbsent(hook,key -> {
            if(key==Hook.NO_DATA) {
                List<QueryIssue> issues=new ArrayList<>();List<Site> sites=new ArrayList<>();
                Optional<Facts> data=facts(new MethodId("java/io/ObjectInputStream","readSerialData","(Ljava/lang/Object;Ljava/io/ObjectStreamClass;)V"),issues);
                if(data.isPresent()) {
                    Facts body=data.get();
                    boolean hasData=body.actions().stream().anyMatch(a -> a instanceof ReadField f && f.field().name().equals("hasData") && f.field().descriptor().equals("Z"));
                    if(hasData)for(Action action:body.actions())if(action instanceof Call dispatch && dispatch.target().equals(new MethodId("java/io/ObjectStreamClass","invokeReadObjectNoData","(Ljava/lang/Object;)V")) && fromParameter(dispatch.arguments().get(0),1,body,new HashSet<>()))
                        for(Action guard:body.actions())if(guard instanceof Call available && available.target().equals(new MethodId("java/io/ObjectStreamClass","hasReadObjectNoDataMethod","()Z")) && available.receiver().equals(dispatch.receiver())) {sites.add(available.site());sites.add(dispatch.site());}
                }
                return new Witness(sites,issues);
            }
            List<Site> sites=new ArrayList<>();List<QueryIssue> issues=new ArrayList<>();String reader=key==Hook.OBJECT?"invokeReadObject":key==Hook.RESOLVE?"invokeReadResolve":"readExternalData";
            String owner=key==Hook.EXTERNAL?"java/io/ObjectInputStream":"java/io/ObjectStreamClass";
            String descriptor=key==Hook.OBJECT?"(Ljava/lang/Object;Ljava/io/ObjectInputStream;)V":key==Hook.RESOLVE?"(Ljava/lang/Object;)Ljava/lang/Object;":"(Ljava/io/Externalizable;Ljava/io/ObjectStreamClass;)V";
            Optional<Facts> available=facts(new MethodId(owner,reader,descriptor),issues);
            if(available.isPresent()) {
                Facts facts=available.get();
                for(Action action:facts.actions())if(action instanceof Call call) {
                    if(key==Hook.EXTERNAL && call.target().equals(new MethodId("java/io/Externalizable","readExternal","(Ljava/io/ObjectInput;)V"))
                            && fromParameter(call.receiver(),1,facts,new HashSet<>()) && fromParameter(call.arguments().get(0),0,facts,new HashSet<>()))sites.add(call.site());
                    if(key==Hook.EXTERNAL || !call.target().equals(Reflection.INVOKE) || !fromParameter(call.arguments().get(0),1,facts,new HashSet<>()))continue;
                    Optional<ReadField> method=fieldSource(call.receiver(),facts,new HashSet<>());
                    if(method.isEmpty() || !method.get().field().owner().equals(owner) || !method.get().field().descriptor().equals("Ljava/lang/reflect/Method;")
                            || !fromParameter(method.get().receiver(),0,facts,new HashSet<>()) || !precedes(method.get().site().instruction(),call.site().instruction(),facts,Set.of(0,1,2)))continue;
                    Optional<Action> args=producer(call.arguments().get(1),facts,new HashSet<>());
                    if(key==Hook.RESOLVE && args.filter(a -> a instanceof Constant c && c.value() instanceof LiteralConstant literal && literal.value()==null).isPresent())sites.add(call.site());
                    if(args.isPresent() && args.get() instanceof NewArray array && array.descriptor().equals("[Ljava/lang/Object;") && constant(array.length(),key==Hook.OBJECT?1:0,facts)) {
                        if(key==Hook.RESOLVE)sites.add(call.site());
                        else if(facts.actions().stream().filter(a -> a instanceof WriteArray write && producer(write.array(),facts,new HashSet<>()).filter(array::equals).isPresent()).count()==1)
                            for(Action item:facts.actions())if(item instanceof WriteArray write && producer(write.array(),facts,new HashSet<>()).filter(array::equals).isPresent()
                                && constant(write.index(),0,facts) && fromParameter(write.value(),2,facts,new HashSet<>())
                                && precedes(write.site().instruction(),call.site().instruction(),facts,Set.of(0,1,2))) {sites.add(write.site());sites.add(call.site());break;}
                    }
                }
            }
            return new Witness(sites,issues);
        });
    }
    private Optional<Action> producer(Sources source,Facts facts,Set<Integer> active) {
        if(source.origins().size()!=1 || !(source.origins().iterator().next() instanceof Producer producer) || !active.add(producer.instruction()))return Optional.empty();
        Action action=program.flow(facts.method().id()).producers().get(producer.instruction());
        return action instanceof Assign assign?producer(assign.input(),facts,active):action instanceof Cast cast?producer(cast.input(),facts,active):Optional.ofNullable(action);
    }
    private boolean constant(Sources source,int expected,Facts facts) {
        return producer(source,facts,new HashSet<>()).filter(a -> a instanceof Constant c && c.value() instanceof LiteralConstant literal && Objects.equals(literal.value(),expected)).isPresent();
    }
    private Optional<Facts> facts(MethodId id,List<QueryIssue> issues) {
        Query<Method> query=program.lookup(id);issues.addAll(query.pending());
        if(query.value().isEmpty() || !query.value().get().hasBody())return Optional.empty();
        Facts facts=program.facts(query.value().get().id());
        for(Limitation limitation:facts.limitations())if(limitation.cause()==CoverageCause.BUDGET)
            issues.add(new QueryIssue(QueryCause.BUDGET,limitation.detail()+": "+id));
        return facts.limitations().isEmpty()?Optional.of(facts):Optional.empty();
    }
    private Witness keyCallback(MethodId root,int slot,MethodId callback) {
        ArrayDeque<Work> pending=new ArrayDeque<>(List.of(new Work(root,slot,List.of())));Set<WorkKey> seen=new HashSet<>();List<QueryIssue> issues=new ArrayList<>();
        while(!pending.isEmpty() && seen.size()<64) {
            Work work=pending.removeFirst();if(!seen.add(new WorkKey(work.method(),work.slot())))continue;
            if(work.path().size()>=6) {issues.add(new QueryIssue(QueryCause.BUDGET,"JDK callback structure depth budget (6): "+root));continue;}
            Query<Method> query=program.lookup(work.method());issues.addAll(query.pending());
            if(query.value().isEmpty() || !query.value().get().hasBody())continue;
            Facts facts=program.facts(query.value().get().id());
            if(!facts.limitations().isEmpty()) {
                for(Limitation limitation:facts.limitations())if(limitation.cause()==CoverageCause.BUDGET)issues.add(new QueryIssue(QueryCause.BUDGET,limitation.detail()+": "+work.method()));
                continue;
            }
            for(Action action:facts.actions())if(action instanceof Call call) {
                List<Site> path=new ArrayList<>(work.path());path.add(call.site());
                if(call.target().equals(callback) && fromParameter(call.receiver(),work.slot(),facts,new HashSet<>())) {
                    if(!callback.name().equals("hashCode")) {
                        Optional<ReadField> key=fieldSource(call.arguments().get(0),facts,new HashSet<>());
                        if(key.isEmpty() || !precedes(key.get().site().instruction(),call.site().instruction(),facts,new HashSet<>(List.of(0,work.slot())))
                                || !keyField(key.get().field(),root.owner().equals("java/util/TreeMap")?1:2,issues))continue;
                        path.add(key.get().site());
                    }
                    return new Witness(path,issues);
                }
                int targetSlot=call.opcode()==org.objectweb.asm.Opcodes.INVOKESTATIC?0:1;List<ValueType> types=program.signature(call.target()).parameters();
                for(int i=0;i<call.arguments().size();i++) {
                    if(fromParameter(call.arguments().get(i),work.slot(),facts,new HashSet<>()) && call.target().owner().equals(root.owner()))pending.addLast(new Work(call.target(),targetSlot,List.copyOf(path)));
                    targetSlot+=types.get(i).slots();
                }
            }
        }
        if(!pending.isEmpty())issues.add(new QueryIssue(QueryCause.BUDGET,"JDK callback structure query budget (64): "+root));
        return new Witness(List.of(),issues);
    }
    private boolean fromParameter(Sources source,int slot,Facts facts,Set<Integer> active) {
        if(source.origins().isEmpty())return false;
        for(Origin origin:source.origins()) {
            if(origin instanceof Parameter parameter){if(parameter.slot()!=slot)return false;continue;}
            if(!(origin instanceof Producer producer) || !active.add(producer.instruction()))return false;
            Action action=program.flow(facts.method().id()).producers().get(producer.instruction());
            boolean matches=action instanceof Assign assign && fromParameter(assign.input(),slot,facts,active) || action instanceof Cast cast && fromParameter(cast.input(),slot,facts,active);
            active.remove(producer.instruction());if(!matches)return false;
        }
        return true;
    }
    private Optional<ReadField> fieldSource(Sources source,Facts facts,Set<Integer> active) {
        ReadField found=null;
        for(Origin origin:source.origins()) {
            if(!(origin instanceof Producer producer) || !active.add(producer.instruction()))return Optional.empty();
            Action action=program.flow(facts.method().id()).producers().get(producer.instruction());
            Optional<ReadField> field=action instanceof Assign assign?fieldSource(assign.input(),facts,active):action instanceof ReadField read?Optional.of(read):action instanceof Cast cast?fieldSource(cast.input(),facts,active):Optional.empty();
            active.remove(producer.instruction());
            if(field.isEmpty() || found!=null && !found.equals(field.get()))return Optional.empty();found=field.get();
        }
        return Optional.ofNullable(found);
    }
    private boolean ordered(int first,int second,Facts facts,Set<Integer> nonnull) {
        return reachable(first,second,-1,facts,nonnull) && !reachable(second,first,-1,facts,nonnull);
    }
    private boolean mustPrecede(int first,int second,Facts facts,Set<Integer> nonnull) {
        return ordered(first,second,facts,nonnull) && !reachable(0,second,first,facts,nonnull);
    }
    private boolean precedes(int first,int second,Facts facts,Set<Integer> nonnull) {
        return reachable(first,second,-1,facts,nonnull) && !reachable(0,second,first,facts,nonnull);
    }
    private boolean reachable(int start,int target,int blocked,Facts facts,Set<Integer> nonnull) {
        Set<Integer> seen=new HashSet<>();ArrayDeque<Integer> pending=new ArrayDeque<>(List.of(start));
        while(!pending.isEmpty()) {
            int at=pending.removeFirst();if(at==blocked || !seen.add(at))continue;if(at==target)return true;
            Action action=program.flow(facts.method().id()).producers().get(at);Optional<Boolean> jump=Optional.empty();
            if(action instanceof Branch branch && (branch.opcode()==org.objectweb.asm.Opcodes.IFNULL || branch.opcode()==org.objectweb.asm.Opcodes.IFNONNULL)
                    && nonnull.stream().anyMatch(slot -> fromParameter(branch.inputs().get(0),slot,facts,new HashSet<>())))
                jump=Optional.of(branch.opcode()==org.objectweb.asm.Opcodes.IFNONNULL);
            for(Edge edge:program.outgoing(facts.method().id()).getOrDefault(at,List.of()))if(!edge.exceptional()
                    && (jump.isEmpty() || (edge.to()==((Branch)action).jumpTarget())==jump.get()))pending.addLast(edge.to());
        }
        return false;
    }
    private boolean keyField(FieldId field,int slot,List<QueryIssue> issues) {
        Optional<ClassInfo> owner=program.type(field.owner());
        if (owner.isEmpty()) {issues.add(new QueryIssue(QueryCause.MISSING_DEPENDENCY,"container entry declaration missing: "+field.owner()));return false;}
        for(Method method:owner.get().methods())if(method.id().name().equals("<init>")) {
            Optional<Facts> available=facts(method.id(),issues);if(available.isEmpty())continue;Facts facts=available.get();
            List<Action> returns=facts.actions().stream().filter(a -> a instanceof Returned).toList();
            for(Action action:facts.actions())if(action instanceof WriteField write && write.field().equals(field) && !returns.isEmpty()
                    && fromParameter(write.receiver(),0,facts,new HashSet<>()) && fromParameter(write.value(),slot,facts,new HashSet<>())
                    && returns.stream().allMatch(a -> mustPrecede(write.site().instruction(),a.site().instruction(),facts,Set.of(0))))return true;
        }
        return false;
    }
    private record WorkKey(MethodId method, int slot) {}
}
