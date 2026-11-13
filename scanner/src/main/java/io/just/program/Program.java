package io.just.program;

import io.just.input.Inputs;
import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;

import java.util.*;

/** Scan-local JVM queries, called by the analysis owner. No target classes are loaded into the scanner VM. */
public final class Program {
    private static final Set<String> PRIMITIVES=Set.of("Z","B","C","S","I","J","F","D","V");
    public record MethodId(String owner, String name, String descriptor,int loader) {
        public MethodId(String owner,String name,String descriptor){this(owner,name,descriptor,0);}
        /** Validate external selectors without resolving or loading their classes. */
        public static boolean validDescriptor(String descriptor) {
            if (descriptor == null || descriptor.length() < 3 || descriptor.charAt(0) != '(') return false;
            int slots = 0;
            int index = 1;
            while (index < descriptor.length() && descriptor.charAt(index) != ')') {
                int end = fieldEnd(descriptor, index);
                if (end < 0) return false;
                char type = descriptor.charAt(index);
                slots += type == 'J' || type == 'D' ? 2 : 1;
                if (slots > 255) return false;
                index = end;
            }
            int returnType = index + 1;
            if (returnType >= descriptor.length()) return false;
            return descriptor.charAt(returnType) == 'V'
                    ? returnType == descriptor.length() - 1
                    : fieldEnd(descriptor, returnType) == descriptor.length();
        }

        private static int fieldEnd(String descriptor, int start) {
            int end = start;
            while (end < descriptor.length() && descriptor.charAt(end) == '[') {
                if (++end - start > 255) return -1;
            }
            if (end == descriptor.length()) return -1;
            char type = descriptor.charAt(end);
            if ("BCDFIJSZ".indexOf(type) >= 0) return end + 1;
            if (type != 'L') return -1;

            int segmentStart = end + 1;
            for (end = segmentStart; end < descriptor.length(); end++) {
                switch (descriptor.charAt(end)) {
                    case ';': return end > segmentStart ? end + 1 : -1;
                    case '/':
                        if (end == segmentStart) return -1;
                        segmentStart = end + 1;
                        break;
                    case '.', '[', '(', ')': return -1;
                    default: break;
                }
            }
            return -1;
        }
        @Override public String toString() { return owner.replace('/', '.') + "#" + name + descriptor+(loader==0?"":" [loader "+loader+"]"); }
    }
    public enum QueryCause { MISSING_DEPENDENCY, BUDGET }
    public record QueryIssue(QueryCause cause,String detail) {}
    /** An empty value is definitive absence only when pending is empty. */
    public record Query<T>(Optional<T> value,List<QueryIssue> pending) {
        public Query { pending=List.copyOf(pending); }
        public boolean absent() { return value.isEmpty() && pending.isEmpty(); }
        static <T> Query<T> found(T value) { return new Query<>(Optional.of(value),List.of()); }
    }
    public record VirtualTarget(Method method,Optional<DefinedType> receiver,List<QueryIssue> pending) {public VirtualTarget {pending=List.copyOf(pending);}}
    private QueryIssue queryBudget(String detail) {
        queryLimits.add(detail);return new QueryIssue(QueryCause.BUDGET,detail);
    }
    private QueryIssue unavailable(String type) {
        return unavailable.getOrDefault(type,new QueryIssue(QueryCause.MISSING_DEPENDENCY,"missing class while resolving hierarchy: "+type));
    }
    public record FieldId(String owner, String name, String descriptor,int loader) { public FieldId(String owner,String name,String descriptor){this(owner,name,descriptor,0);} }
    public record FieldInfo(FieldId id,int access) {}
    public record ValueType(String descriptor, int slots) {
        public boolean reference() { return descriptor.startsWith("L") || descriptor.startsWith("["); }
        public boolean isVoid() { return descriptor.equals("V"); }
    }
    public record Signature(List<ValueType> parameters, ValueType returned) {}
    public sealed interface JvmConstant permits LiteralConstant, ClassConstant, MethodTypeConstant, HandleConstant, UnsupportedConstant {}
    public record LiteralConstant(Object value) implements JvmConstant {}
    public record ClassConstant(String descriptor) implements JvmConstant {}
    public record MethodTypeConstant(String descriptor) implements JvmConstant {}
    public record HandleConstant(int tag,MethodId target,boolean interfaceOwner) implements JvmConstant {}
    public record Bootstrap(HandleConstant factory,List<JvmConstant> arguments) {}
    public record UnsupportedConstant(String kind) implements JvmConstant {}
    public record Site(MethodId method, int instruction, int line, String source) {
        @Override public String toString() { return method + " @insn " + instruction + (line > 0 ? " line " + line : ""); }
    }
    public record Annotation(String descriptor, Map<String, String> values) {}
    public record Method(MethodId id, int access, List<Annotation> annotations) {
        public boolean isStatic() { return (access & Opcodes.ACC_STATIC) != 0; }
        public boolean hasBody() { return (access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) == 0; }
        public boolean isPublic() { return (access & Opcodes.ACC_PUBLIC) != 0; }
    }
    public record ClassInfo(String name, String parent, List<String> interfaces, int access,
                            List<Method> methods, List<Annotation> annotations, Inputs.Role role,int loader) {}
    public sealed interface Origin permits Parameter, Producer, ExceptionOrigin, UnknownOrigin, LimitedOrigin {}
    public record Parameter(int slot) implements Origin {}
    public record Producer(int instruction) implements Origin {}
    public record ExceptionOrigin(int handler) implements Origin {}
    public record UnknownOrigin(String reason) implements Origin {}
    public record LimitedOrigin() implements Origin {}
    public record Sources(Set<Origin> origins) {
        public Sources { origins = Collections.unmodifiableSet(new LinkedHashSet<>(origins)); }
        public boolean parameter(int slot) { return origins.equals(Set.of(new Parameter(slot))); }
    }
    public enum GuardKind { BRANCH, NORMAL, HANDLER }
    public record Guard(int branch,int successor,GuardKind kind) { public Guard(int branch,int successor) { this(branch,successor,GuardKind.BRANCH); } }
    public record Handler(int start,int end,int target,String type) {}
    public record Edge(int from, int to, boolean exceptional) {}
    public sealed interface Action permits Constant, Allocate, NewArray, Cast, ReadField, WriteField,
            ReadArray, WriteArray, Call, Returned, Thrown, Compute, Branch, Assign {
        Site site();
    }
    /** Preserve a local value's control path or a loop-carried commit point. */
    public record Assign(Site site,Sources input) implements Action {}
    public record Constant(Site site, JvmConstant value) implements Action {}
    public record Allocate(Site site, String type, boolean repeated) implements Action {}
    public record NewArray(Site site, String descriptor, Sources length, boolean repeated) implements Action {}
    public record Cast(Site site, String type, Sources input) implements Action {}
    public record ReadField(Site site, FieldId field, Sources receiver) implements Action {}
    public record WriteField(Site site, FieldId field, Sources receiver, Sources value) implements Action {}
    public record ReadArray(Site site, Sources array, Sources index) implements Action {}
    public record WriteArray(Site site, Sources array, Sources index, Sources value) implements Action {}
    public record Call(Site site,MethodId target,int opcode,Sources receiver,List<Sources> arguments,Optional<Bootstrap> bootstrap) implements Action {
        public Call(Site site,MethodId target,int opcode,Sources receiver,List<Sources> arguments) { this(site,target,opcode,receiver,arguments,Optional.empty()); }
    }
    public record Returned(Site site, Sources value) implements Action {}
    public record Thrown(Site site,Sources value) implements Action {}
    public record Compute(Site site,int opcode,List<Sources> inputs,int operand,String type) implements Action { public Compute(Site site,int opcode,List<Sources> inputs) { this(site,opcode,inputs,0,""); } }
    public record Branch(Site site,int opcode,List<Sources> inputs,int jumpTarget,Map<Integer,Integer> cases) implements Action { public Branch(Site site,int opcode,List<Sources> inputs,int jumpTarget) { this(site,opcode,inputs,jumpTarget,Map.of()); } }
    public enum CoverageCause { UNSUPPORTED, BUDGET }
    public record Limitation(CoverageCause cause, String detail) {}
    public record Facts(Method method, List<Action> actions, List<Edge> cfg,
                        Map<Integer, List<Guard>> guards, List<Handler> handlers,List<Limitation> limitations) {
        public Facts(Method method,List<Action> actions,List<Edge> cfg,Map<Integer,List<Guard>> guards,List<Limitation> limitations) { this(method,actions,cfg,guards,List.of(),limitations); }
    }

    public static final class Failure extends RuntimeException {
        public Failure(String context, Exception cause) { super(context, cause); }
    }
    private record Parsed(ClassNode node, Inputs.ClassData data, ClassInfo info) {}
    private final Inputs inputs;
    private final int instructionLimit;
    private record ClassId(String name,int loader) {}
    private record DefinitionKey(Object loader,Object bytes,int offset,int length) {}
    private record DefinitionBytes(Object identity,int offset,int length) {}
    private final Map<ClassId, Optional<Parsed>> classes = new HashMap<>();
    private final Map<Object,Integer> loaders=new HashMap<>();
    private final Map<DefinitionKey,ClassId> definitions=new HashMap<>();
    private final Map<DefinitionBytes,Parsed> definitionBytes=new HashMap<>();
    private Optional<List<ClassInfo>> candidates=Optional.empty();
    private final Map<MethodId, Facts> facts = new HashMap<>();
    private final LinkedHashMap<MethodId,MethodNode> code=new LinkedHashMap<>(16,.75f,true);
    private int cachedInstructions;
    private final Map<MethodId,Flow> flows=new HashMap<>();
    private final Map<MethodId,MethodSyntax> methodSyntax=new HashMap<>();
    private final Map<MethodId,Map<Integer,List<Edge>>> outgoing=new HashMap<>();
    private final Map<MethodId, Signature> signatures = new HashMap<>();
    private record DispatchKey(MethodId method,String upper,int loader,List<DefinedType> preferred) {}
    private final LinkedHashMap<DispatchKey,Query<List<VirtualTarget>>> dispatches=new LinkedHashMap<>(16,.75f,true);
    private int dispatchRevision;
    private void invalidateDispatch() { dispatches.clear(); dispatchRevision++; }
    private record ReflectKey(String owner,String name,List<String> parameters,boolean declared,int loader) {ReflectKey {parameters=List.copyOf(parameters);}}
    private final LinkedHashMap<ReflectKey,Query<Method>> reflected=new LinkedHashMap<>(16,.75f,true);
    private record Implementations(Map<ClassId,List<ClassInfo>> known,Map<ClassInfo,List<QueryIssue>> unresolved) {}
    private Optional<Implementations> implementationTypes=Optional.empty();
    private final List<ClassInfo> targets;
    private final Set<String> missing = new LinkedHashSet<>();
    private final Set<String> queryLimits = new LinkedHashSet<>();
    private final Map<String,QueryIssue> unavailable=new HashMap<>();
    private static final int SCAN_INSTRUCTION_LIMIT=500_000;
    private long analyzedInstructions;
    private record MemberSignature(String name,String descriptor) {}
    private record Syntax(Map<MemberSignature,Map<MethodId,List<Site>>> callers,Map<MemberSignature,Map<FieldId,List<Site>>> writers,
                          Map<String,List<MethodId>> returned,boolean truncated) {}
    public record Candidates(List<Site> sites,String scope,boolean truncated,List<QueryIssue> pending) {public Candidates{sites=List.copyOf(sites);pending=List.copyOf(pending);}}
    private Optional<Syntax> syntax=Optional.empty();

    public Program(Inputs inputs, int instructionLimit) {
        this.inputs = inputs;
        this.instructionLimit = instructionLimit;
        for (Inputs.ClassData data : inputs.targetClasses()) {
            Parsed parsed = parse(data);
            classes.put(new ClassId(parsed.info().name(),0), Optional.of(parsed));
        }
        targets=classes.values().stream().flatMap(Optional::stream).map(Parsed::info)
                .sorted(Comparator.comparing(ClassInfo::name)).toList();
    }

    public Inputs.Summary inputSummary() { return inputs.summary(); }

    /** Application exposure and mechanism search deliberately have different scopes. */
    public List<ClassInfo> candidates() {
        if(candidates.isEmpty()) {
            Map<Integer,List<ClassInfo>> artifacts=new LinkedHashMap<>();
            for(Inputs.ClassData data:inputs.candidateClasses())if(data.scope()!=Inputs.Role.TARGET)artifacts.computeIfAbsent(data.artifact().id(),key -> new ArrayList<>()).add(parsed(data.name()).orElseThrow().info());
            ArrayDeque<Iterator<ClassInfo>> pending=new ArrayDeque<>();for(List<ClassInfo> members:artifacts.values()){members.sort(Comparator.comparing(ClassInfo::name));pending.addLast(members.iterator());}
            List<ClassInfo> ordered=new ArrayList<>(targets);while(!pending.isEmpty()){Iterator<ClassInfo> next=pending.removeFirst();ordered.add(next.next());if(next.hasNext())pending.addLast(next);}
            definitions.values().stream().distinct().sorted(Comparator.comparingInt(ClassId::loader).thenComparing(ClassId::name)).forEach(id -> ordered.add(classes.get(id).orElseThrow().info()));
            candidates=Optional.of(List.copyOf(ordered));
        }
        return candidates.get();
    }
    public Optional<Object> loaderIdentity(int loader){return loaders.entrySet().stream().filter(entry -> entry.getValue()==loader).map(Map.Entry::getKey).findFirst();}
    public int loader(Object identity){return loaders.getOrDefault(identity,0);}
    public int scope(String name,int loader){
        if(name.startsWith("[")){int component=0;while(component<name.length() && name.charAt(component)=='[')component++;return component<name.length() && name.charAt(component)=='L'?scope(name.substring(component+1,name.length()-1),loader):0;}
        return loader!=0 && classes.containsKey(new ClassId(name,loader))?loader:0;}
    public Optional<Inputs.ClassData> classData(String name){return inputs.find(name);}
    public Optional<Inputs.ClassData> classData(String name,int loader){return scope(name,loader)==0?classData(name):parsed(name,loader).map(Parsed::data);}
    public boolean platformType(String name,int loader){return scope(name,loader)==0 && inputs.platformType(name);}
    /** Definition is static classfile parsing, never JVM class loading. Identity belongs to this program. */
    public MethodId method(String owner,String name,String descriptor,int loader){return new MethodId(owner,name,descriptor,scope(owner,loader));}
    public static final class DefinitionConflict extends RuntimeException {
        private final DefinedType type;
        DefinitionConflict(DefinedType type){super("incompatible class facts: "+type);this.type=type;}
        public DefinedType type(){return type;}
    }
    public record DefinedType(String name,int loader) {}
    public int definitionCount(){return definitions.size();}
    public Query<DefinedType> define(Object loader,Object identity,byte[] bytes,int offset,int length,String requested) {return define(loader,identity,bytes,offset,length,requested,"static classfile");}
    public Query<DefinedType> define(Object loader,Object identity,byte[] bytes,int offset,int length,String requested,String source) {
        DefinitionKey key=new DefinitionKey(loader,identity,offset,length);ClassId old=definitions.get(key);if(old!=null){if(requested!=null && !requested.equals(old.name()))throw new IllegalArgumentException("defined name differs from classfile: "+requested+" / "+old.name());return Query.found(new DefinedType(old.name(),old.loader()));}
        if(definitions.size()>=1024)return new Query<>(Optional.empty(),List.of(queryBudget("static class definition budget (1024)")));
        int scope=loaders.computeIfAbsent(loader,k -> loaders.size()+1);
        Parsed base=definitionBytes.computeIfAbsent(new DefinitionBytes(identity,offset,length),ignored -> {
            byte[] slice=offset==0 && length==bytes.length?bytes:Arrays.copyOfRange(bytes,offset,offset+length);
            Inputs.ClassData data=new Inputs.ClassData(requested==null?"defined":requested,slice,new Inputs.Artifact(-1,source,Inputs.Role.DEPENDENCY),"classfile["+offset+":"+length+"]");
            try{return parse(data);}catch(Failure invalid){throw new IllegalArgumentException("invalid definition classfile from "+source,invalid);}
        });
        ClassInfo info=base.info();String name=info.name();
        if(requested!=null && !requested.equals(name))throw new IllegalArgumentException("defined name differs from classfile: "+requested+" / "+name);
        ClassId id=new ClassId(name,scope);
        Optional<Parsed> existing=classes.getOrDefault(id,Optional.empty());
        if(existing.isPresent()) {
            if(!Arrays.equals(existing.get().data().bytes(),base.data().bytes()))throw new DefinitionConflict(new DefinedType(name,scope));
            definitions.put(key,id);return Query.found(new DefinedType(name,scope));
        }
        List<Method> members=info.methods().stream().map(m -> new Method(new MethodId(name,m.id().name(),m.id().descriptor(),scope),m.access(),m.annotations())).toList();
        Parsed parsed=new Parsed(base.node(),base.data(),new ClassInfo(name,info.parent(),info.interfaces(),info.access(),members,info.annotations(),info.role(),scope));
        classes.put(id,Optional.of(parsed));definitions.put(key,id);invalidateDispatch();reflected.clear();candidates=Optional.empty();implementationTypes=Optional.empty();syntax=Optional.empty();return Query.found(new DefinedType(name,scope));
    }
    public List<ClassInfo> targets() {
        return targets;
    }

    /** Bounded reverse syntax frontier. Members are search candidates, never dispatch evidence. */
    public Query<List<Method>> candidateMethods(Set<MethodId> goals,int budget) {
        Map<MethodId,Method> result=new LinkedHashMap<>();Set<MethodId> seen=new LinkedHashSet<>();
        List<QueryIssue> issues=new ArrayList<>();ArrayDeque<MethodId> seeds=new ArrayDeque<>(goals);
        ArrayDeque<Iterator<MethodId>> callersPending=new ArrayDeque<>();
        while((!seeds.isEmpty() || !callersPending.isEmpty()) && seen.size()<budget) {
            MethodId id;
            if(!seeds.isEmpty())id=seeds.removeFirst();
            else {Iterator<MethodId> batch=callersPending.removeFirst();id=batch.next();if(batch.hasNext())callersPending.addLast(batch);}
            if(!seen.add(id))continue;
            Query<Method> member=lookup(id);issues.addAll(member.pending());
            member.value().filter(m -> m.isPublic() && !m.id().name().startsWith("<")).ifPresent(m -> result.putIfAbsent(m.id(),m));
            Candidates callers=callers(id);issues.addAll(callers.pending());
            if(callers.truncated())issues.add(new QueryIssue(QueryCause.BUDGET,"candidate caller index truncated"));
            Map<String,LinkedHashSet<MethodId>> families=new LinkedHashMap<>();
            for(Site use:callers.sites())if(!seen.contains(use.method()))families.computeIfAbsent(use.method().owner(),k -> new LinkedHashSet<>()).add(use.method());
            for(Set<MethodId> family:families.values()) {
                MethodId first=family.iterator().next();
                if(type(first.owner(),first.loader()).filter(info -> info.role()==Inputs.Role.TARGET).isPresent())callersPending.addFirst(family.iterator());
                else callersPending.addLast(family.iterator());
            }
        }
        if(!seeds.isEmpty() || !callersPending.isEmpty())issues.add(new QueryIssue(QueryCause.BUDGET,"dynamic goal frontier ("+budget+")"));
        return new Query<>(Optional.of(List.copyOf(result.values())),List.copyOf(new LinkedHashSet<>(issues)));
    }

    private Parsed parse(Inputs.ClassData data) {return parse(data,0);}
    private Parsed parse(Inputs.ClassData data,int loader) {
        ClassNode node = new ClassNode(Opcodes.ASM9);
        readClass(data, node, ClassReader.SKIP_CODE | ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
        List<Method> methods = node.methods.stream().map(m -> new Method(
                new MethodId(node.name, m.name, m.desc,loader), m.access, annotations(m.visibleAnnotations, m.invisibleAnnotations))).toList();
        node.methods.clear();
        return new Parsed(node, data, new ClassInfo(node.name, node.superName, List.copyOf(node.interfaces),
                node.access, methods, annotations(node.visibleAnnotations, node.invisibleAnnotations), data.scope(),loader));
    }

    private static void readClass(Inputs.ClassData data, ClassVisitor visitor, int flags) {
        try {
            new ClassReader(data.bytes()).accept(visitor, flags);
        } catch (IllegalArgumentException | ArrayIndexOutOfBoundsException invalid) {
            throw new Failure("invalid class file: " + data.source(), invalid);
        }
    }

    private static List<Annotation> annotations(List<AnnotationNode> visible, List<AnnotationNode> invisible) {
        List<Annotation> result = new ArrayList<>();
        for (List<AnnotationNode> nodes : Arrays.asList(visible, invisible)) {
            if (nodes == null) continue;
            for (AnnotationNode annotation : nodes) {
                Map<String, String> values = new LinkedHashMap<>();
                if (annotation.values != null)
                    for (int i = 0; i < annotation.values.size(); i += 2)
                        values.put((String) annotation.values.get(i), String.valueOf(annotation.values.get(i + 1)));
                result.add(new Annotation(annotation.desc, Map.copyOf(values)));
            }
        }
        return List.copyOf(result);
    }

    private Optional<Parsed> parsed(String name) {return parsed(name,0);}
    private Optional<Parsed> parsed(String name,int loader) {
        return classes.computeIfAbsent(new ClassId(name,scope(name,loader)), key -> {
            String n=key.name();Inputs.Lookup read=inputs.lookup(n);
            Optional<Parsed> parsed = read.value().map(this::parse);
            if(parsed.filter(p -> p.info().role()==Inputs.Role.PLATFORM && (p.info().access() & (Opcodes.ACC_ABSTRACT|Opcodes.ACC_INTERFACE))==0).isPresent())invalidateDispatch();
            if (parsed.isEmpty()) {
                if(read.truncated().isPresent())unavailable.put(n,new QueryIssue(QueryCause.BUDGET,read.truncated().get()+" while reading "+n));
                else missing.add(n);
            }
            return parsed;
        });
    }

    public Optional<ClassInfo> type(String name) {return type(name,0);}
    public Optional<ClassInfo> type(String name,int loader) {return parsed(name,loader).map(Parsed::info);}
    public Query<ClassInfo> definition(String name) {return definition(name,0);}
    public Query<ClassInfo> definition(String name,int loader) {
        Optional<ClassInfo> value=type(name,loader);
        return new Query<>(value,value.isPresent()?List.of():List.of(unavailable(name)));
    }
    /** Private reflection access uses reciprocal nest metadata, without loading either class. */
    public Query<Boolean> nestmates(String first,String second) {return nestmates(first,0,second,0);}
    public Query<Boolean> nestmates(String first,int firstLoader,String second,int secondLoader) {
        int scope=scope(first,firstLoader);if(scope!=scope(second,secondLoader))return Query.found(false);
        if(first.equals(second))return Query.found(true);
        Optional<Parsed> left=parsed(first,scope),right=parsed(second,scope);List<QueryIssue> issues=new ArrayList<>();
        if(left.isEmpty())issues.add(unavailable(first));if(right.isEmpty())issues.add(unavailable(second));
        if(!issues.isEmpty())return new Query<>(Optional.empty(),issues);
        ClassNode a=left.orElseThrow().node(),b=right.orElseThrow().node();
        String host=a.nestHostClass==null?a.name:a.nestHostClass,other=b.nestHostClass==null?b.name:b.nestHostClass;
        String pkg=first.substring(0,Math.max(0,first.lastIndexOf('/')));
        if(a.version<Opcodes.V11 || b.version<Opcodes.V11 || !host.equals(other) || !pkg.equals(second.substring(0,Math.max(0,second.lastIndexOf('/'))))
                || !pkg.equals(host.substring(0,Math.max(0,host.lastIndexOf('/')))))return new Query<>(Optional.of(false),List.of());
        Optional<Parsed> declaration=parsed(host,scope);
        if(declaration.isEmpty())return new Query<>(Optional.empty(),List.of(unavailable(host)));
        ClassNode node=declaration.get().node();
        boolean valid=node.version>=Opcodes.V11 && node.nestHostClass==null
                && (host.equals(first) || node.nestMembers!=null && node.nestMembers.contains(first))
                && (host.equals(second) || node.nestMembers!=null && node.nestMembers.contains(second));
        return new Query<>(Optional.of(valid),List.of());
    }
    public Signature signature(MethodId method) {
        return signatures.computeIfAbsent(method, id -> new Signature(Arrays.stream(Type.getArgumentTypes(id.descriptor()))
                .map(t -> new ValueType(t.getDescriptor(), t.getSize())).toList(),
                new ValueType(Type.getReturnType(id.descriptor()).getDescriptor(), Type.getReturnType(id.descriptor()).getSize())));
    }
    /** Positive projection; a negative conclusion must consume lookupField's pending reasons. */
    public Optional<FieldId> field(FieldId requested) {
        return lookupField(requested).value();
    }
    public Query<FieldId> lookupField(FieldId requested) {
        Set<ClassId> seen=new HashSet<>();List<QueryIssue> issues=new ArrayList<>();
        ArrayDeque<ClassId> pending=new ArrayDeque<>(List.of(new ClassId(requested.owner(),scope(requested.owner(),requested.loader()))));
        while (!pending.isEmpty() && seen.size()<256) {
            ClassId current=pending.removeFirst();if (!seen.add(current))continue;
            Optional<Parsed> type=parsed(current.name(),current.loader());
            if (type.isEmpty()) {issues.add(unavailable(current.name()));continue;}
            for (FieldNode field:type.get().node().fields)
                if (field.name.equals(requested.name()) && field.desc.equals(requested.descriptor()))
                    return new Query<>(Optional.of(new FieldId(current.name(),field.name,field.desc,current.loader())),issues);
            if (type.get().info().parent()!=null){String parent=type.get().info().parent();pending.addFirst(new ClassId(parent,scope(parent,current.loader())));}
            List<String> faces=type.get().info().interfaces();for(int index=faces.size()-1;index>=0;index--){String face=faces.get(index);pending.addFirst(new ClassId(face,scope(face,current.loader())));}
        }
        if (!pending.isEmpty())issues.add(queryBudget("field hierarchy query budget: "+requested));
        return new Query<>(Optional.empty(),issues);
    }
    public List<String> missingClasses() {
        return List.copyOf(missing);
    }
    public boolean instanceField(FieldId field) {
        return parsed(field.owner(),field.loader()).map(p -> p.node().fields.stream().anyMatch(f -> f.name.equals(field.name())
                && f.desc.equals(field.descriptor()) && (f.access & Opcodes.ACC_STATIC)==0)).orElse(false);
    }
    public List<FieldInfo> fields(String owner) {return fields(owner,0);}
    public List<FieldInfo> fields(String owner,int loader) {
        return parsed(owner,loader).map(p -> p.node().fields.stream().map(f -> new FieldInfo(new FieldId(owner,f.name,f.desc,p.info().loader()),f.access)).toList()).orElse(List.of());
    }
    public int instructionLimit() { return instructionLimit; }
    public List<String> limitations() {
        return queryLimits.stream().sorted().toList();
    }
    /** Positive proof only. Callers disproving compatibility use assignable instead. */
    public boolean subtype(String child,String parent) {
        return assignable(child,parent).value().orElse(false);
    }
    public Query<Boolean> assignable(String child,String parent) {
        if (child.equals(parent) || parent.equals("java/lang/Object"))return Query.found(true);
        if (child.startsWith("[")) {
            if (parent.equals("java/lang/Cloneable") || parent.equals("java/io/Serializable"))return Query.found(true);
            if (!parent.startsWith("["))return Query.found(false);
            String left=child.substring(1),right=parent.substring(1);
            if (left.length()==1 || right.length()==1)return Query.found(left.equals(right));
            return assignable(left.startsWith("L")?left.substring(1,left.length()-1):left,right.startsWith("L")?right.substring(1,right.length()-1):right);
        }
        if (parent.startsWith("["))return Query.found(false);
        Optional<ClassInfo> required=type(parent);
        if(required.filter(info -> (info.access() & Opcodes.ACC_FINAL)!=0).isPresent())return Query.found(false);
        boolean interfaces=required.map(info -> (info.access() & Opcodes.ACC_INTERFACE)!=0).orElse(true);
        Set<String> seen=new HashSet<>();List<QueryIssue> issues=new ArrayList<>();
        ArrayDeque<String> pending=new ArrayDeque<>(List.of(child));
        while (!pending.isEmpty() && seen.size()<256) {
            String current=pending.removeFirst();if (!seen.add(current))continue;
            if (current.equals(parent))return Query.found(true);
            Optional<ClassInfo> info=type(current);
            if (info.isEmpty()) {issues.add(unavailable(current));continue;}
            if (info.get().parent()!=null)pending.addLast(info.get().parent());
            if(interfaces)pending.addAll(info.get().interfaces());
        }
        if (!pending.isEmpty())issues.add(queryBudget("type hierarchy query budget: "+child+" -> "+parent));
        return issues.isEmpty()?Query.found(false):new Query<>(Optional.empty(),issues);
    }

    public Query<Boolean> assignable(String child,int loader,String parent,int parentLoader) {
        if(loader==0 && parentLoader==0)return assignable(child,parent);
        if(parent.equals("java/lang/Object") && scope(parent,parentLoader)==0)return Query.found(true);
        if(child.startsWith("[") || parent.startsWith("[")) {
            if(!child.startsWith("[") || !parent.startsWith("["))return assignable(child,parent);
            String left=child.substring(1),right=parent.substring(1);
            if(left.length()==1 || right.length()==1)return Query.found(left.equals(right));
            return assignable(left.startsWith("L")?left.substring(1,left.length()-1):left,loader,right.startsWith("L")?right.substring(1,right.length()-1):right,parentLoader);
        }
        ClassId required=new ClassId(parent,scope(parent,parentLoader));Set<ClassId> seen=new HashSet<>();List<QueryIssue> issues=new ArrayList<>();
        if(!new ClassId(child,scope(child,loader)).equals(required) && type(parent,parentLoader).filter(info -> (info.access() & Opcodes.ACC_FINAL)!=0).isPresent())return Query.found(false);
        boolean interfaces=type(parent,parentLoader).map(info -> (info.access() & Opcodes.ACC_INTERFACE)!=0).orElse(true);
        ArrayDeque<ClassId> pending=new ArrayDeque<>(List.of(new ClassId(child,scope(child,loader))));
        while(!pending.isEmpty() && seen.size()<256) {
            ClassId current=pending.removeFirst();if(!seen.add(current))continue;if(current.equals(required))return Query.found(true);
            Optional<ClassInfo> info=type(current.name(),current.loader());if(info.isEmpty()){issues.add(unavailable(current.name()));continue;}
            List<String> parents=interfaces?new ArrayList<>(info.get().interfaces()):new ArrayList<>();if(info.get().parent()!=null)parents.add(info.get().parent());
            for(String name:parents)pending.addLast(new ClassId(name,scope(name,current.loader())));
        }
        if(!pending.isEmpty())issues.add(queryBudget("scoped hierarchy budget: "+child+" -> "+parent));
        return issues.isEmpty()?Query.found(false):new Query<>(Optional.empty(),List.copyOf(issues));
    }

    public Optional<Method> declared(MethodId id) {
        return declaration(id).value();
    }
    public Query<Method> declaration(MethodId id) {
        Optional<ClassInfo> metadata=type(id.owner(),id.loader());
        Query<ClassInfo> owner=new Query<>(metadata,metadata.isPresent()?List.of():List.of(unavailable(id.owner())));
        return new Query<>(owner.value().flatMap(c -> c.methods().stream().filter(m -> m.id().name().equals(id.name()) && m.id().descriptor().equals(id.descriptor())).findFirst()),owner.pending());
    }

    /** Positive projection for search/expansion; absence is interpreted through lookup. */
    public Optional<Method> resolve(MethodId id) {
        return lookup(id).value();
    }
    /** Class overrides take priority over default interface methods. */
    public Query<Method> lookup(MethodId id) {
        if(id.name().equals("<init>") || id.name().equals("<clinit>"))return declaration(id);
        if(id.owner().startsWith("[")) {
            if(id.name().equals("clone") && id.descriptor().equals("()Ljava/lang/Object;"))return Query.found(new Method(id,Opcodes.ACC_PUBLIC|Opcodes.ACC_FINAL|Opcodes.ACC_NATIVE,List.of()));
            return lookup(new MethodId("java/lang/Object",id.name(),id.descriptor()));
        }
        List<ClassId> interfaces=new ArrayList<>();Set<ClassId> seen=new HashSet<>();
        List<QueryIssue> issues=new ArrayList<>();ClassId current=new ClassId(id.owner(),scope(id.owner(),id.loader()));
        while (current!=null && seen.add(current) && seen.size()<=256) {
            Optional<ClassInfo> info=type(current.name(),current.loader());
            if (info.isEmpty())return new Query<>(Optional.empty(),List.of(unavailable(current.name())));
            Optional<Method> own=declared(new MethodId(current.name(),id.name(),id.descriptor(),current.loader()));
            if (own.isPresent())return new Query<>(own,List.of());
            for(String face:info.get().interfaces())interfaces.add(new ClassId(face,scope(face,current.loader())));
            String parent=info.get().parent();current=parent==null?null:new ClassId(parent,scope(parent,current.loader()));
        }
        if (current!=null && seen.size()>256)issues.add(queryBudget("method hierarchy query budget: "+id));
        ArrayDeque<ClassId> pending=new ArrayDeque<>(interfaces);List<Method> matches=new ArrayList<>();
        while (!pending.isEmpty() && seen.size()<=256) {
            current=pending.removeFirst();if (!seen.add(current))continue;
            Optional<ClassInfo> info=type(current.name(),current.loader());
            if (info.isEmpty()) {issues.add(unavailable(current.name()));continue;}
            Optional<Method> own=declared(new MethodId(current.name(),id.name(),id.descriptor(),current.loader()));
            own.filter(m -> !m.isStatic() && (m.access() & Opcodes.ACC_PRIVATE)==0).ifPresent(matches::add);
            for(String face:info.get().interfaces())pending.addLast(new ClassId(face,scope(face,current.loader())));
        }
        if (!pending.isEmpty())issues.add(queryBudget("interface method query budget: "+id));
        List<Method> maximal=matches.stream().filter(candidate -> matches.stream().noneMatch(other -> !candidate.equals(other)
                && assignable(other.id().owner(),other.id().loader(),candidate.id().owner(),candidate.id().loader()).value().equals(Optional.of(true)))).toList();
        List<Method> concrete=maximal.stream().filter(Method::hasBody).toList();
        if(concrete.size()>1) {
            issues.add(new QueryIssue(QueryCause.MISSING_DEPENDENCY,"ambiguous maximally-specific interface methods: "+id));
            return new Query<>(Optional.empty(),issues);
        }
        return new Query<>(concrete.stream().findFirst().or(() -> maximal.stream().findFirst()),issues);
    }

    /** Finite known implementations of a virtual receiver upper bound. */
    public List<ClassInfo> concreteTypes(String upper) {return concreteTypes(upper,0);}
    public List<ClassInfo> concreteTypes(String upper,int loader) {
        Implementations index=implementationTypes();Set<ClassInfo> known=new LinkedHashSet<>(index.known().getOrDefault(new ClassId(upper,scope(upper,loader)),List.of()));
        Set<ClassInfo> types=new LinkedHashSet<>(known);types.addAll(index.unresolved().keySet());
        boolean interfaces=type(upper,loader).map(info -> (info.access() & Opcodes.ACC_INTERFACE)!=0).orElse(true);
        return types.stream().filter(type -> known.contains(type) || interfaces || !assignable(type.name(),type.loader(),upper,loader).value().equals(Optional.of(false))).toList();
    }
    public Query<List<VirtualTarget>> implementations(MethodId requested,String upper,int loader) {
        return implementations(requested,upper,loader,List.of());
    }
    /** Preferences guide body-backed scanner expansion; they are not dispatch evidence. */
    public Query<List<VirtualTarget>> implementations(MethodId requested, String upper, int loader,
                                                       List<DefinedType> preferred) {
        DispatchKey key = new DispatchKey(requested, upper, loader, List.copyOf(preferred));
        Query<List<VirtualTarget>> cached = dispatches.get(key);
        if (cached != null) return cached;
        int revision = dispatchRevision;
        Query<List<VirtualTarget>> selected = new Dispatch(this).discover(requested, upper, loader, preferred);
        for (QueryIssue issue : selected.pending())
            if (issue.cause() == QueryCause.BUDGET) queryBudget(issue.detail());
        if (revision == dispatchRevision) {
            if (dispatches.size() >= 1024) dispatches.remove(dispatches.keySet().iterator().next());
            dispatches.put(key, selected);
        }
        return selected;
    }

    List<DefinedType> dispatchCandidates(String upper, int loader) {
        LinkedHashSet<DefinedType> receivers = new LinkedHashSet<>();
        classes.values().stream().flatMap(Optional::stream).map(Parsed::info)
                .filter(type -> type.role() == Inputs.Role.PLATFORM
                        && (type.access() & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_INTERFACE)) == 0)
                .sorted(Comparator.comparing(ClassInfo::name))
                .forEach(type -> receivers.add(new DefinedType(type.name(), type.loader())));
        for (ClassInfo type : concreteTypes(upper, loader))
            receivers.add(new DefinedType(type.name(), type.loader()));
        return List.copyOf(receivers);
    }
    /** Read each candidate hierarchy once, shared by all virtual member queries. */
    private Implementations implementationTypes() {
        if(implementationTypes.isPresent())return implementationTypes.get();
        Map<ClassId,List<ClassInfo>> known=new HashMap<>();Map<ClassInfo,List<QueryIssue>> unresolved=new LinkedHashMap<>();
        for(ClassInfo candidate:candidates()) {
            if((candidate.access() & (Opcodes.ACC_ABSTRACT|Opcodes.ACC_INTERFACE))!=0)continue;
            Set<ClassId> seen=new LinkedHashSet<>();List<QueryIssue> issues=new ArrayList<>();ArrayDeque<ClassId> pending=new ArrayDeque<>(List.of(new ClassId(candidate.name(),candidate.loader())));
            while(!pending.isEmpty() && seen.size()<256) {
                ClassId id=pending.removeFirst();if(!seen.add(id))continue;
                Optional<ClassInfo> info=type(id.name(),id.loader());if(info.isEmpty()){issues.add(unavailable(id.name()));continue;}
                if(info.get().parent()!=null)pending.addLast(new ClassId(info.get().parent(),scope(info.get().parent(),id.loader())));
                for(String parent:info.get().interfaces())pending.addLast(new ClassId(parent,scope(parent,id.loader())));
            }
            if(!pending.isEmpty())issues.add(queryBudget("implementation hierarchy frontier (256): "+candidate.name()));
            seen.add(new ClassId("java/lang/Object",0));for(ClassId id:seen)known.computeIfAbsent(id,key -> new ArrayList<>()).add(candidate);
            if(!issues.isEmpty())unresolved.put(candidate,List.copyOf(issues));
        }
        implementationTypes=Optional.of(new Implementations(known,unresolved));return implementationTypes.get();
    }

    /** Constructors belong only to the requested declaration; they are never inherited. */
    public Query<Method> constructor(String owner,List<String> parameters,boolean declared) {return constructor(owner,parameters,declared,0);}
    public Query<Method> constructor(String owner,List<String> parameters,boolean declared,int loader) {
        if(owner.startsWith("[") || PRIMITIVES.contains(owner))return new Query<>(Optional.empty(),List.of());
        Optional<ClassInfo> info=type(owner,loader);
        if(info.isEmpty())return new Query<>(Optional.empty(),List.of(unavailable(owner)));
        Optional<Method> method=info.get().methods().stream().filter(m -> m.id().name().equals("<init>") && (declared || m.isPublic())
                && signature(m.id()).parameters().stream().map(ValueType::descriptor).toList().equals(parameters)).findFirst();
        return new Query<>(method,List.of());
    }
    public Query<Method> reflect(String owner,String name,List<String> parameters,boolean declared) {return reflect(owner,name,parameters,declared,0);}
    public Query<Method> reflect(String owner,String name,List<String> parameters,boolean declared,int loader) {
        ReflectKey key=new ReflectKey(owner,name,parameters,declared,loader);Query<Method> known=reflected.get(key);if(known!=null)return known;
        Query<Method> result=reflectMember(owner,name,parameters,declared,loader);
        if(reflected.size()>=4096)reflected.remove(reflected.keySet().iterator().next());
        reflected.put(key,result);return result;
    }
    private Query<Method> reflectMember(String owner,String name,List<String> parameters,boolean declared,int loader) {
        Query<List<Method>> query=methods(owner,declared,loader);
        Optional<Method> selected=Optional.empty();
        for(Method method:query.value().orElseThrow())if(method.id().name().equals(name)
                && signature(method.id()).parameters().stream().map(ValueType::descriptor).toList().equals(parameters))
            selected=Optional.of(selected.isEmpty()?method:preferred(selected.get(),method));
        return new Query<>(selected,query.pending());
    }

    private Method preferred(Method first,Method second) {
        boolean firstInterface=type(first.id().owner(),first.id().loader()).map(c -> (c.access() & Opcodes.ACC_INTERFACE)!=0).orElse(false);
        boolean secondInterface=type(second.id().owner(),second.id().loader()).map(c -> (c.access() & Opcodes.ACC_INTERFACE)!=0).orElse(false);
        if(firstInterface!=secondInterface)return firstInterface?second:first;
        if(!first.id().owner().equals(second.id().owner()) || first.id().loader()!=second.id().loader()) {
            if(assignable(second.id().owner(),second.id().loader(),first.id().owner(),first.id().loader()).value().equals(Optional.of(true)))return second;
            if(assignable(first.id().owner(),first.id().loader(),second.id().owner(),second.id().loader()).value().equals(Optional.of(true)))return first;
        }
        String a=signature(first.id()).returned().descriptor(),b=signature(second.id()).returned().descriptor();
        if(!a.equals(b) && (b.startsWith("L") || b.startsWith("[")) && (a.startsWith("L") || a.startsWith("["))
                && assignable(Type.getType(b).getInternalName(),second.id().loader(),Type.getType(a).getInternalName(),first.id().loader()).value().equals(Optional.of(true)))return second;
        if(!a.equals(b) && (b.startsWith("L") || b.startsWith("[")) && (a.startsWith("L") || a.startsWith("["))
                && assignable(Type.getType(a).getInternalName(),first.id().loader(),Type.getType(b).getInternalName(),second.id().loader()).value().equals(Optional.of(true)))return first;
        if((first.access() & Opcodes.ACC_BRIDGE)!=0 && (second.access() & Opcodes.ACC_BRIDGE)==0)return second;
        return first;
    }

    public Map<Integer,List<Edge>> outgoing(MethodId id) {
        return outgoing.computeIfAbsent(id,key -> {
            Map<Integer,List<Edge>> edges=new HashMap<>();
            for (Edge edge:facts(key).cfg()) edges.computeIfAbsent(edge.from(),k -> new ArrayList<>()).add(edge);
            Map<Integer,List<Edge>> immutable=new HashMap<>(); edges.forEach((at,value) -> immutable.put(at,List.copyOf(value)));
            return Map.copyOf(immutable);
        });
    }

    /** Metadata candidates, independent of invocation access and of reflection array order. */
    public Query<List<Method>> methods(String owner,boolean declared) {return methods(owner,declared,0);}
    public Query<List<Method>> methods(String owner,boolean declared,int loader) {
        if(PRIMITIVES.contains(owner))return Query.found(List.of());
        if(owner.startsWith("["))return declared?Query.found(List.of()):methods("java/lang/Object",false,0);
        Map<String,Method> result=new LinkedHashMap<>();Set<ClassId> seen=new HashSet<>();List<QueryIssue> issues=new ArrayList<>();
        ClassId root=new ClassId(owner,scope(owner,loader));ArrayDeque<ClassId> pending=new ArrayDeque<>(List.of(root));
        while(!pending.isEmpty() && seen.size()<256) {
            ClassId current=pending.removeFirst();if(!seen.add(current))continue;
            Optional<ClassInfo> type=type(current.name(),current.loader());
            if(type.isEmpty()){issues.add(unavailable(current.name()));continue;}
            boolean inheritedInterface=!current.equals(root) && (type.get().access() & Opcodes.ACC_INTERFACE)!=0;
            for(Method method:type.get().methods())if(!method.id().name().startsWith("<") && (declared || method.isPublic()) && !(inheritedInterface && method.isStatic())) {
                result.merge(method.id().name()+method.id().descriptor(),method,this::preferred);
                if(result.size()>=256){issues.add(queryBudget("method metadata enumeration budget (256): "+owner));return new Query<>(Optional.of(List.copyOf(result.values())),issues);}
            }
            if(!declared){if(type.get().parent()!=null && (type.get().access() & Opcodes.ACC_INTERFACE)==0){String parent=type.get().parent();pending.addLast(new ClassId(parent,scope(parent,current.loader())));}for(String face:type.get().interfaces())pending.addLast(new ClassId(face,scope(face,current.loader())));}
        }
        if(!pending.isEmpty())issues.add(queryBudget("method metadata hierarchy budget: "+owner));
        return new Query<>(Optional.of(List.copyOf(result.values())),issues);
    }

    public Optional<JvmConstant> fieldConstant(FieldId field) {
        return parsed(field.owner(),field.loader()).flatMap(p -> p.node().fields.stream().filter(f -> f.name.equals(field.name()) && f.desc.equals(field.descriptor()) && f.value!=null && (f.access & Opcodes.ACC_STATIC)!=0).map(f -> MethodFlow.constant(f.value)).findFirst());
    }

    public Facts facts(MethodId id) {
        Facts result = facts.computeIfAbsent(id, this::analyze);
        for (Limitation limitation : result.limitations())
            if (limitation.cause() == CoverageCause.BUDGET) queryLimits.add(limitation.detail() + ": " + id);
        return result;
    }

    public record SymbolicCall(Site site,MethodId target,int opcode) {}
    private record MethodSyntax(List<SymbolicCall> calls,List<MethodId> references,boolean truncated) {}
    /** Syntactic references never establish receiver binding or execution. */
    public Query<List<MethodId>> references(MethodId id) {
        Query<MethodSyntax> query=syntaxQuery(id);
        return new Query<>(query.value().map(MethodSyntax::references),query.pending());
    }
    public Query<List<SymbolicCall>> calls(MethodId id) {
        Query<MethodSyntax> query=syntaxQuery(id);
        return new Query<>(query.value().map(MethodSyntax::calls),query.pending());
    }
    private Query<MethodSyntax> syntaxQuery(MethodId id) {
        Optional<MethodSyntax> syntax=Optional.ofNullable(methodSyntax.get(id));
        List<QueryIssue> pending=new ArrayList<>();
        if(syntax.isEmpty()) {
            Query<Method> declaration=declaration(id);pending.addAll(declaration.pending());
            syntax=declaration.value().map(method -> syntaxMethod(method.id()));
        }
        if(syntax.filter(MethodSyntax::truncated).isPresent())pending.add(new QueryIssue(QueryCause.BUDGET,"syntactic method instruction budget (20000): "+id));
        return new Query<>(syntax,List.copyOf(pending));
    }
    private MethodSyntax syntaxMethod(MethodId id) {
        return methodSyntax.computeIfAbsent(id,key -> {
            Parsed owner=parsed(key.owner(),key.loader()).orElseThrow();MethodNode method=code(key);
            List<SymbolicCall> calls=new ArrayList<>();Set<MethodId> references=new LinkedHashSet<>();int index=0,line=-1;
            for(AbstractInsnNode instruction:method.instructions) {
                if(index>=20_000)break;if(instruction instanceof LineNumberNode number)line=number.line;
                if(instruction instanceof MethodInsnNode call) {
                    MethodId target=new MethodId(call.owner,call.name,call.desc,key.loader());references.add(target);calls.add(new SymbolicCall(new Site(key,index,line,owner.data().source()),target,call.getOpcode()));
                } else if(instruction instanceof InvokeDynamicInsnNode dynamic && dynamic.bsm.getOwner().equals("java/lang/invoke/LambdaMetafactory")
                        && dynamic.bsmArgs.length>1 && dynamic.bsmArgs[1] instanceof Handle handle)
                    references.add(new MethodId(handle.getOwner(),handle.getName(),handle.getDesc(),key.loader()));
                index++;
            }
            return new MethodSyntax(List.copyOf(calls),List.copyOf(references),index<method.instructions.size());
        });
    }
    public Query<Set<MethodId>> discover(Set<MethodId> roots,int budget) {
        Set<MethodId> seen=new LinkedHashSet<>();List<QueryIssue> pending=new ArrayList<>();ArrayDeque<MethodId> queue=new ArrayDeque<>(roots);
        Set<String> targetNames=new HashSet<>();for(ClassInfo type:targets)targetNames.add(type.name());
        while(!queue.isEmpty()) {
            MethodId id=queue.removeFirst();if(seen.contains(id))continue;
            if(seen.size()>=budget){pending.add(new QueryIssue(QueryCause.BUDGET,"target reference discovery budget: "+budget));break;}
            seen.add(id);
            Query<List<MethodId>> references=references(id);pending.addAll(references.pending());
            for(MethodId reference:references.value().orElse(List.of()))if(targetNames.contains(reference.owner())) {
                Query<Method> resolved=lookup(new MethodId(reference.owner(),reference.name(),reference.descriptor(),id.loader()));pending.addAll(resolved.pending());
                resolved.value().filter(Method::hasBody).filter(m -> type(m.id().owner()).orElseThrow().role()==Inputs.Role.TARGET).ifPresent(m -> queue.addLast(m.id()));
            }
        }
        return new Query<>(Optional.of(Collections.unmodifiableSet(seen)),List.copyOf(new LinkedHashSet<>(pending)));
    }

    /** Method-local origins are immutable and shared; invocation consumers remain with analysis. */
    public record Flow(Map<Integer,Action> producers,Map<Integer,Set<Origin>> inputs) {
        public Flow {producers=Map.copyOf(producers);inputs=Map.copyOf(inputs);}
    }
    public Flow flow(MethodId id) {
        return flows.computeIfAbsent(id,k -> {
            Facts method=facts(k);Map<Integer,Action> actions=new LinkedHashMap<>();Map<Integer,Set<Origin>> inputs=new LinkedHashMap<>();
            for(Action action:method.actions()) {
                int instruction=action.site().instruction();actions.put(instruction,action);Set<Origin> origins=new LinkedHashSet<>();
                for(Sources source:sources(action))origins.addAll(source.origins());
                for(Guard guard:method.guards().getOrDefault(instruction,List.of()))origins.add(new Producer(guard.branch()));
                inputs.put(instruction,Collections.unmodifiableSet(origins));
            }
            return new Flow(actions,inputs);
        });
    }

    public static List<Sources> sources(Action action) {
        if(action instanceof Assign assign)return List.of(assign.input());
        if (action instanceof Call call) {
            List<Sources> all = new ArrayList<>(call.arguments()); all.add(call.receiver()); return List.copyOf(all);
        }
        if (action instanceof Cast cast) return List.of(cast.input());
        if (action instanceof NewArray array) return List.of(array.length());
        if (action instanceof ReadField field) return List.of(field.receiver());
        if (action instanceof WriteField field) return List.of(field.receiver(), field.value());
        if (action instanceof ReadArray array) return List.of(array.array(), array.index());
        if (action instanceof WriteArray array) return List.of(array.array(), array.index(), array.value());
        if (action instanceof Returned returned) return List.of(returned.value());
        if (action instanceof Thrown thrown) return List.of(thrown.value());
        if (action instanceof Compute compute) return compute.inputs();
        if (action instanceof Branch branch) return branch.inputs();
        return List.of();
    }

    /** These target-bytecode sites are candidate sources; no receiver or reachability is implied. */
    public Candidates callers(MethodId method) {
        Syntax index=syntax();Set<Site> sites=new LinkedHashSet<>();List<QueryIssue> pending=new ArrayList<>();
        for(var entry:index.callers().getOrDefault(new MemberSignature(method.name(),method.descriptor()),Map.of()).entrySet()) {
            if(entry.getKey().equals(method))sites.addAll(entry.getValue());
            else {
                Query<Method> resolved=lookup(entry.getKey());pending.addAll(resolved.pending());if(resolved.value().map(Method::id).filter(method::equals).isPresent())sites.addAll(entry.getValue());
            }
        }
        return new Candidates(List.copyOf(sites),"application/dependency classfile callsites; symbolic and requested declaration identities",index.truncated(),pending);
    }
    public Candidates fieldWriters(FieldId field) {
        Syntax index=syntax();Set<Site> sites=new LinkedHashSet<>();List<QueryIssue> pending=new ArrayList<>();Query<FieldId> requested=lookupField(field);pending.addAll(requested.pending());
        for(var entry:index.writers().getOrDefault(new MemberSignature(field.name(),field.descriptor()),Map.of()).entrySet()) {
            Query<FieldId> resolved=lookupField(entry.getKey());pending.addAll(resolved.pending());
            if(entry.getKey().equals(field) || requested.value().isPresent() && resolved.value().equals(requested.value()))sites.addAll(entry.getValue());
        }
        return new Candidates(List.copyOf(sites),"application/dependency classfile field writes; requested declaration aliases",index.truncated(),List.copyOf(new LinkedHashSet<>(pending)));
    }
    /** Actual uses of constructors and methods returning this type; no object or return alias is implied. */
    public Candidates producers(String descriptor) {return producers(descriptor,0);}
    public Candidates producers(String descriptor,int loader) {
        Set<MethodId> members=new LinkedHashSet<>();List<QueryIssue> pending=new ArrayList<>();
        String type=Type.getType(descriptor).getInternalName();
        Query<ClassInfo> definition=definition(type,loader);pending.addAll(definition.pending());
        definition.value().ifPresent(info -> info.methods().stream().filter(m -> m.id().name().equals("<init>")).map(Method::id).forEach(members::add));
        for(MethodId method:syntax().returned().getOrDefault(descriptor,List.of()))if(scope(type,method.loader())==scope(type,loader))members.add(method);
        Set<Site> sites=new LinkedHashSet<>();boolean truncated=false;
        search:for(MethodId member:members) {
            Candidates uses=callers(member);pending.addAll(uses.pending());truncated|=uses.truncated();
            for(Site site:uses.sites()) {
                if(sites.size()>=128 && !sites.contains(site)){truncated=true;break search;}
                sites.add(site);
            }
        }
        return new Candidates(List.copyOf(sites),"application/dependency constructor and matching return-type callsites (128); receiver and returned identity remain unbound",truncated,List.copyOf(new LinkedHashSet<>(pending)));
    }
    private Syntax syntax() {
        if(syntax.isPresent())return syntax.get();
        Map<MethodId,List<Site>> calls=new LinkedHashMap<>();Map<FieldId,List<Site>> writes=new LinkedHashMap<>();int count=0;boolean truncated=false;
        scan:for(ClassInfo info:candidates()) {
            Parsed type=parsed(info.name(),info.loader()).orElseThrow();
            ClassNode body=new ClassNode(Opcodes.ASM9);readClass(type.data(),body,ClassReader.SKIP_FRAMES);
            for(MethodNode method:body.methods) {
                int index=0,line=-1;MethodId id=new MethodId(info.name(),method.name,method.desc,info.loader());
                for(AbstractInsnNode instruction:method.instructions) {
                    if(++count>200_000){truncated=true;break scan;}
                    if(instruction instanceof LineNumberNode number)line=number.line;
                    Site site=new Site(id,index++,line,type.data().source());
                    if(instruction instanceof MethodInsnNode call) {
                        MethodId symbolic=method(call.owner,call.name,call.desc,info.loader());calls.computeIfAbsent(symbolic,k -> new ArrayList<>()).add(site);

                    }
                    if(instruction instanceof FieldInsnNode field && (field.getOpcode()==Opcodes.PUTSTATIC || field.getOpcode()==Opcodes.PUTFIELD))writes.computeIfAbsent(new FieldId(field.owner,field.name,field.desc,scope(field.owner,info.loader())),k -> new ArrayList<>()).add(site);
                }
            }
        }
        Map<MemberSignature,Map<MethodId,List<Site>>> callers=new LinkedHashMap<>();
        calls.forEach((key,value) -> callers.computeIfAbsent(new MemberSignature(key.name(),key.descriptor()),ignored -> new LinkedHashMap<>()).put(key,List.copyOf(value)));
        callers.replaceAll((key,value) -> Collections.unmodifiableMap(value));
        Map<MemberSignature,Map<FieldId,List<Site>>> writers=new LinkedHashMap<>();
        writes.forEach((key,value) -> writers.computeIfAbsent(new MemberSignature(key.name(),key.descriptor()),ignored -> new LinkedHashMap<>()).put(key,List.copyOf(value)));
        writers.replaceAll((key,value) -> Collections.unmodifiableMap(value));
        Map<String,List<MethodId>> returned=new LinkedHashMap<>();
        for(ClassInfo info:candidates())for(Method method:info.methods())if(!method.id().name().startsWith("<"))
            returned.computeIfAbsent(signature(method.id()).returned().descriptor(),ignored -> new ArrayList<>()).add(method.id());
        returned.replaceAll((key,value) -> List.copyOf(value));
        Syntax result=new Syntax(Collections.unmodifiableMap(callers),Collections.unmodifiableMap(writers),Collections.unmodifiableMap(returned),truncated);syntax=Optional.of(result);return result;
    }

    /** Metadata remains small; only requested method bodies enter the bounded bytecode cache. */
    MethodNode code(MethodId id) {
        MethodNode cached=code.get(id);if(cached!=null)return cached;
        Parsed owner=parsed(id.owner(),id.loader()).orElseThrow();MethodNode[] selected=new MethodNode[1];
        readClass(owner.data(),new ClassVisitor(Opcodes.ASM9) {
            @Override public MethodVisitor visitMethod(int access,String name,String descriptor,String signature,String[] exceptions) {
                if(!name.equals(id.name()) || !descriptor.equals(id.descriptor()))return null;
                MethodNode method=new MethodNode(Opcodes.ASM9,access,name,descriptor,signature,exceptions);selected[0]=method;return method;
            }
        },ClassReader.SKIP_FRAMES);
        MethodNode method=Objects.requireNonNull(selected[0],"missing method body: "+id);
        while(!code.isEmpty() && cachedInstructions+method.instructions.size()>500_000) {
            MethodId first=code.keySet().iterator().next();cachedInstructions-=code.remove(first).instructions.size();
        }
        if(method.instructions.size()<=500_000){code.put(id,method);cachedInstructions+=method.instructions.size();}
        return method;
    }

    private Facts analyze(MethodId id) {
        Method method = declared(id).orElseThrow(() -> new IllegalArgumentException("no method: " + id));
        Parsed parsed = parsed(id.owner(),id.loader()).orElseThrow();
        MethodNode node = code(id);
        if (!method.hasBody()) return new Facts(method, List.of(), List.of(), Map.of(), List.of(new Limitation(CoverageCause.UNSUPPORTED, "native or abstract method body")));
        int count=node.instructions.size();
        String limit=count>instructionLimit?"method instruction budget ("+instructionLimit+"): "+count+" instructions"
                :analyzedInstructions+count>SCAN_INSTRUCTION_LIMIT?"scan instruction budget ("+SCAN_INSTRUCTION_LIMIT+"): "+analyzedInstructions+" used, "+count+" requested":null;
        if(limit!=null)return new Facts(method,List.of(),List.of(),Map.of(),List.of(new Limitation(CoverageCause.BUDGET,limit)));
        analyzedInstructions+=count;
        return MethodFlow.analyze(method,node,parsed.data().source());
    }

    public static boolean exceptional(Action action) {
        return action instanceof Call || action instanceof ReadField || action instanceof WriteField || action instanceof ReadArray || action instanceof WriteArray
                || action instanceof Cast || action instanceof NewArray || action instanceof Thrown || action instanceof Compute c &&
                (c.opcode()==Opcodes.ARRAYLENGTH || c.opcode()==Opcodes.IDIV || c.opcode()==Opcodes.LDIV || c.opcode()==Opcodes.IREM || c.opcode()==Opcodes.LREM);
    }

}
