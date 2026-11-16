package io.just.analysis;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.ValueBindings;
import io.just.analysis.ExecutionPoint.*;
import java.util.*;

/** Owns positioned heap writes and temporal visibility. Returns dependencies and changes, never schedules work. */
final class HeapStore {
    record Cell(int object,Slot slot) {}
    record Use(ExecutionPoint point,Site site,Path path,List<Edge> cfg,boolean ownWrites) {}
    record Read(Value value,Set<Cell> dependencies) {}
    record Reachable(List<ObjectValue> objects,Set<Cell> dependencies,int consumed,boolean truncated) {}
    private record Frame(int context,int instruction,int iteration,List<Integer> effects) {}
    private record Graph(List<Edge> edges) {
        @Override public int hashCode(){return System.identityHashCode(edges);}
        @Override public boolean equals(Object other){return other instanceof Graph graph && graph.edges==edges;}
    }
    private record ReadKey(int object,String type,Slot slot,ExecutionPoint point,Site site,Path path,boolean ownWrites,Graph graph) {}
    private record CachedRead(long objectVersion,long conditionsVersion,int definitions,List<Edge> cfg,Read read) {}
    private static final int READ_CACHE_LIMIT=8192;
    private final Map<Integer,Map<Slot,Map<ExecutionPoint,Value>>> objects=new LinkedHashMap<>();
    private final Map<Integer,List<Frame>> ancestry=new HashMap<>();
    private final Map<Integer,Long> versions=new HashMap<>();
    private final Map<ReadKey,CachedRead> cachedReads=new LinkedHashMap<>();
    private final Set<String> limitations=new LinkedHashSet<>();
    private final Conditions conditions;
    private final Program program;
    private final int alternatives;

    HeapStore(Program program,Conditions conditions,int alternatives) {this.program=program;this.conditions=conditions;this.alternatives=alternatives;}
    void context(int id,int parent,int instruction,int iteration) {
        context(id,parent,instruction,iteration,List.of());
    }
    void context(int id,int parent,int instruction,int iteration,List<Integer> effects) {
        List<Frame> path=new ArrayList<>(parent<0?List.of():ancestry.get(parent));
        path.add(new Frame(id,instruction,iteration,effects));if(ancestry.put(id,List.copyOf(path))!=null)cachedReads.clear();
    }
    void seed(ObjectValue object,Slot slot,Value value) {
        Map<ExecutionPoint,Value> writes=writes(object,slot);ExecutionPoint point=new ExecutionPoint(-1,-1);
        Value old=writes.get(point),joined=writes.merge(point,value,Value::merge);
        if(!Objects.equals(old,joined))versions.merge(object.id(),1L,Long::sum);
    }
    boolean write(ObjectValue object,Slot slot,ExecutionPoint writer,Value value,Site site) {
        Map<ExecutionPoint,Value> writes=writes(object,slot);
        Value old=writes.getOrDefault(writer,Value.BOTTOM),joined=bounded(old.merge(value),site);
        if(old.equals(joined))return false;writes.put(writer,joined);versions.merge(object.id(),1L,Long::sum);return true;
    }
    /** Same-object producer candidates; callers must still use read() for temporal/path semantics. */
    private Map<Slot,Map<ExecutionPoint,Value>> slots(ObjectValue object){return objects.getOrDefault(object.id(),Map.of());}
    private Map<ExecutionPoint,Value> writes(ObjectValue object,Slot slot) {
        return objects.computeIfAbsent(object.id(),key -> new LinkedHashMap<>()).computeIfAbsent(slot,key -> {
            versions.merge(object.id(),1L,Long::sum);return new LinkedHashMap<>();
        });
    }
    List<ExecutionPoint> writers(ObjectValue object,Slot slot){return List.copyOf(slots(object).getOrDefault(slot,Map.of()).keySet());}
    Read read(ObjectValue object,Slot slot,Use use) {
        Map<Slot,Map<ExecutionPoint,Value>> slots=slots(object);
        int writes=slots.getOrDefault(slot,Map.of()).size()+slots.getOrDefault(new Mutation(),Map.of()).size();
        if(slot instanceof Index)writes+=slots.getOrDefault(new Wildcard(),Map.of()).size();
        if(writes<16 && (!(slot instanceof Elements) || slots.size()<16)) {
            Set<Cell> dependencies=new LinkedHashSet<>();Value value=read(object,slot,use,dependencies);
            return new Read(value,Set.copyOf(dependencies));
        }
        ReadKey key=new ReadKey(object.id(),object.type(),slot,use.point(),use.site(),use.path(),use.ownWrites(),new Graph(use.cfg()));
        long version=versions.getOrDefault(object.id(),0L),condition=conditions.revision();int definitions=program.definitionCount();
        CachedRead cached=cachedReads.get(key);
        if(cached!=null && cached.objectVersion()==version && cached.conditionsVersion()==condition && cached.definitions()==definitions && cached.cfg().equals(use.cfg()))return cached.read();
        Set<Cell> dependencies=new LinkedHashSet<>();
        Value value=read(object,slot,use,dependencies);
        Read result=new Read(value,Set.copyOf(dependencies));
        if(cached==null && cachedReads.size()>=READ_CACHE_LIMIT)cachedReads.remove(cachedReads.keySet().iterator().next());
        cachedReads.put(key,new CachedRead(version,condition,definitions,List.copyOf(use.cfg()),result));return result;
    }
    /** Visible mutable references only; serialized source slots and model bookkeeping are not live fields. */
    Reachable reachable(List<Atom> roots,Use use,int allowance) {
        Map<Integer,ObjectValue> objects=new LinkedHashMap<>();Set<Cell> dependencies=new LinkedHashSet<>();
        ArrayDeque<Atom> pending=new ArrayDeque<>(roots);Set<Atom> visited=new HashSet<>();int consumed=0;boolean truncated=false;
        search:while(!pending.isEmpty()) {
            Atom value=pending.removeFirst();if(!visited.add(value))continue;
            if(!(value instanceof ObjectValue object)) {
                List<Atom> references=ValueBindings.mutableReferences(value);
                if(references.isEmpty())continue;
                if(consumed>=allowance){truncated=true;break;}consumed++;
                pending.addAll(references);continue;
            }
            if(objects.containsKey(object.id()))continue;
            if(objects.size()>=64){truncated=true;break;}objects.put(object.id(),object);
            Set<Slot> slots=new LinkedHashSet<>();
            for(Slot slot:slots(object).keySet())if(mutable(object,slot))slots.add(slot);
            Set<DefinedType> seen=new HashSet<>();Optional<ClassInfo> type=object.type().startsWith("[")?Optional.empty():program.type(object.type(),object.loader());
            while(type.isPresent() && seen.size()<64 && seen.add(new DefinedType(type.get().name(),type.get().loader()))) {
                ClassInfo owner=type.get();
                for(FieldInfo field:program.fields(owner.name(),owner.loader()))if((field.access() & org.objectweb.asm.Opcodes.ACC_STATIC)==0
                        && (field.id().descriptor().startsWith("L") || field.id().descriptor().startsWith("[")))slots.add(new Field(field.id()));
                type=owner.parent()==null?Optional.empty():program.type(owner.parent(),program.scope(owner.parent(),owner.loader()));
            }
            if(type.isPresent() && seen.size()>=64)truncated=true;
            for(Slot slot:slots) {
                if(consumed>=allowance){truncated=true;break search;}consumed++;
                for(Bound bound:read(object,slot,use,dependencies).alternatives())pending.addLast(bound.atom());
            }
        }
        return new Reachable(List.copyOf(objects.values()),Set.copyOf(dependencies),consumed,truncated);
    }
    private Value read(ObjectValue object,Slot slot,Use use,Set<Cell> dependencies) {
        Cell cell=new Cell(object.id(),slot);dependencies.add(cell);
        Cell mutation=new Cell(object.id(),new Mutation());
        Map<Slot,Map<ExecutionPoint,Value>> slots=slots(object);
        Map<ExecutionPoint,Value> mutations=mutable(object,slot)?slots.getOrDefault(mutation.slot(),Map.of()):Map.of();
        if(mutable(object,slot))dependencies.add(mutation);
        Map<ExecutionPoint,Value> direct=slots.getOrDefault(slot,Map.of());
        if(direct.isEmpty() && mutations.isEmpty() && !(slot instanceof Index || slot instanceof Elements))return Value.BOTTOM;
        List<Map.Entry<ExecutionPoint,Value>> writes=new ArrayList<>(direct.entrySet());writes.addAll(mutations.entrySet());
        List<Map.Entry<ExecutionPoint,Value>> available=new ArrayList<>();
        for(var write:writes) {
            if(!use.ownWrites() && write.getKey().equals(use.point()))continue;
            if(write.getKey().phase() instanceof Request && use.point().phase() instanceof Request && !write.getKey().phase().equals(use.point().phase()))continue;
            boolean localMemo=use.ownWrites() && write.getKey().context()==use.point().context() && write.getKey().instruction()==use.point().instruction() && write.getKey().iteration()==use.point().iteration() && write.getKey().phase().equals(use.point().phase());
            if(!localMemo && order(write.getKey(),use.point())>0 && (!write.getKey().phase().equals(use.point().phase()) || use.point().iteration()>=0
                    || !inLoop(use.cfg(),Math.min(use.point().instruction(),write.getKey().instruction()),Math.max(use.point().instruction(),write.getKey().instruction()))))continue;
            if(write.getValue().alternatives().stream().noneMatch(bound -> bound.path().compatible(use.path())))continue;
            available.add(write);
        }
        // Keep maximal covering writes as a small frontier before testing conditional replacements.
        // An unordered/asynchronous write never displaces an ordered witness here.
        // The frontier pays for itself on long histories; short histories use the direct check.
        List<Map.Entry<ExecutionPoint,Value>> covering=available.size()>=64?new ArrayList<>():List.of();
        if(available.size()>=64 && !(slot instanceof Elements || slot instanceof MapValues || slot instanceof Wildcard))for(var candidate:available) {
            if(mutations.containsKey(candidate.getKey()) || candidate.getValue().alternatives().stream().noneMatch(b -> conditions.implied(b.path(),use.path())))continue;
            if(covering.stream().anyMatch(later -> replaces(candidate.getKey(),later.getKey(),use)))continue;
            covering.removeIf(earlier -> replaces(earlier.getKey(),candidate.getKey(),use));covering.add(candidate);
        }
        Value value=Value.BOTTOM;
        for(var write:available)for(Bound bound:write.getValue().alternatives()) {
            Optional<Path> atUse=bound.path().and(use.path());if(atUse.isEmpty())continue;
            if(!covering.isEmpty() && covering.stream().anyMatch(later -> replaces(write.getKey(),later.getKey(),use)
                    && later.getValue().alternatives().stream().anyMatch(replacement -> conditions.implied(replacement.path(),atUse.get()))))continue;
            boolean overwritten=false;Set<Gap> changed=new LinkedHashSet<>();
            if(!(slot instanceof Elements || slot instanceof MapValues || slot instanceof Wildcard) || !mutations.isEmpty())
                for(var later:available)if(replaces(write.getKey(),later.getKey(),use)) {
                    if((slot instanceof Elements || slot instanceof MapValues || slot instanceof Wildcard) && !mutations.containsKey(later.getKey()))continue;
                    for(Bound replacement:later.getValue().alternatives())
                        if(atUse.get().compatible(replacement.path()) && conditions.implied(replacement.path(),atUse.get())) {
                            if(mutations.containsKey(later.getKey()))changed.addAll(replacement.gaps());else {overwritten=true;break;}
                        }
                    if(overwritten)break;
                }
            if(!overwritten) {
                Bound visible=atUse.get().equals(bound.path())?bound:new Bound(bound.atom(),atUse.get(),bound.gaps(),bound.dependencies());
                value=bounded(value.merge(new Value(Set.of(visible)).requiring(List.copyOf(changed))),use.site());
            }
        }
        if(slot instanceof Index)value=bounded(value.merge(read(object,new Wildcard(),use,dependencies)),use.site());
        if(slot instanceof Elements && (object.type().startsWith("[") || program.subtype(object.type(),"java/util/List"))) {
            // A may-summary is separate from exact positions; both are subscribed by the caller.
            for(Slot indexed:slots(object).keySet())if(indexed instanceof Index) {
                value=bounded(value.merge(read(object,indexed,use,dependencies)),use.site());
            }
        }
        value=value.under(use.path());
        if(!(slot instanceof Elements || slot instanceof MapValues)) {
            List<Bound> bindings=new ArrayList<>(value.alternatives());boolean ambiguous=false;
            for(int i=0;i<bindings.size() && !ambiguous;i++)for(int j=i+1;j<bindings.size();j++)
                if(!bindings.get(i).atom().equals(bindings.get(j).atom()) && bindings.get(i).path().compatible(bindings.get(j).path())) {ambiguous=true;break;}
            if(ambiguous)value=value.requiring(List.of(new Gap(GapKind.UNSUPPORTED,use.site(),"multiple compatible heap writes; exact temporal binding not established for object "+object.id()+" "+slot)));
        }
        return value;
    }
    private static boolean mutable(ObjectValue object,Slot slot) {
        // Array length belongs to the identity; opaque calls can only change its contents.
        if(slot instanceof Length && object.type().startsWith("["))return false;
        return slot instanceof Field || slot instanceof MethodAccess || slot instanceof Index || slot instanceof Wildcard || slot instanceof Length || slot instanceof Content
                || slot instanceof Elements || slot instanceof MapKey || slot instanceof MapValues || slot instanceof KeyIndex
                || slot instanceof IterationOrder || slot instanceof Cursor || slot instanceof StreamCursor;
    }
    private boolean replaces(ExecutionPoint earlier,ExecutionPoint later,Use use) {
        return order(earlier,later)<0 && (!(later.phase() instanceof Asynchronous) || later.phase().equals(use.point().phase()))
                && (!(use.point().phase() instanceof Asynchronous async) || later.phase().equals(use.point().phase())
                    || order(earlier,async.launch())<0 && order(later,async.launch())<0);
    }
    boolean before(ExecutionPoint first,ExecutionPoint second){return order(first,second)<0;}
    private int order(ExecutionPoint first,ExecutionPoint second) {
        if(first.context()<0)return second.context()<0?0:-1;if(second.context()<0)return 1;
        if(first.context()==second.context() && first.phase().equals(second.phase()))
            return position(first.instruction(),second.instruction(),first.iteration(),second.iteration(),first.effects(),second.effects());
        List<Frame> leftPath=ancestry.get(first.context()),rightPath=ancestry.get(second.context());
        int common=0;while(common<leftPath.size() && common<rightPath.size() && leftPath.get(common).context()==rightPath.get(common).context())common++;
        if(common==0)return 0;
        if(!first.phase().equals(second.phase())) {
            if(first.phase() instanceof Asynchronous && second.phase() instanceof Asynchronous)return 0;
            if(second.phase() instanceof Asynchronous async)return order(first,async.launch())<0?-1:0;
            if(first.phase() instanceof Asynchronous async)return order(async.launch(),second)>0?1:0;
            if(first.phase() instanceof Startup)return -1;if(second.phase() instanceof Startup)return 1;return 0;
        }
        int leftInstruction=common==leftPath.size()?first.instruction():leftPath.get(common).instruction();
        int rightInstruction=common==rightPath.size()?second.instruction():rightPath.get(common).instruction();
        int leftIteration=common==leftPath.size()?first.iteration():leftPath.get(common).iteration();
        int rightIteration=common==rightPath.size()?second.iteration():rightPath.get(common).iteration();
        List<Integer> left=common==leftPath.size()?first.effects():leftPath.get(common).effects();
        List<Integer> right=common==rightPath.size()?second.effects():rightPath.get(common).effects();
        return position(leftInstruction,rightInstruction,leftIteration,rightIteration,left,right);
    }
    private static int position(int leftInstruction,int rightInstruction,int leftIteration,int rightIteration,List<Integer> left,List<Integer> right) {
        if(leftIteration>=0 && rightIteration>=0 && leftIteration!=rightIteration)return Integer.compare(leftIteration,rightIteration);
        if(leftInstruction!=rightInstruction)return Integer.compare(leftInstruction,rightInstruction);
        for(int i=0;i<Math.min(left.size(),right.size());i++)if(!left.get(i).equals(right.get(i)))return Integer.compare(left.get(i),right.get(i));
        return Integer.compare(left.size(),right.size());
    }
    static boolean inLoop(List<Edge> cfg,int low,int high) {return cfg.stream().anyMatch(e -> !e.exceptional() && e.to()<=low && e.from()>=high);}
    private Value bounded(Value value,Site site) {
        if(value.alternatives().size()<=alternatives)return value;
        String detail="value alternative budget at "+site;limitations.add(detail);
        return value.limited(alternatives,new Gap(GapKind.BUDGET,site,"value alternative budget: "+alternatives));
    }
    int cells() {return objects.values().stream().mapToInt(Map::size).sum();}
    List<String> limitations() {return List.copyOf(limitations);}
}
