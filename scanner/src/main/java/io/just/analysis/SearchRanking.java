package io.just.analysis;

import io.just.knowledge.*;
import io.just.knowledge.Mechanisms.Hint;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.program.Program;
import io.just.program.Program.*;
import java.util.*;

/** Ranks current source relations and compatible bindings, never reference counts or proof. */
final class SearchRanking {
    enum Rank { NONE, PARTIAL, BOUND, CONTINUED }
    enum RelationState { SUPPORTED, PENDING, REFUTED, ABSENT }
    record Match(RelationState state,int priority) {}
    private enum ArrayOrigin { FACTS, REQUESTED }
    private record ArrayKey(Atom atom,Path path) {}
    private record ArrayView(ValueBindings.ArrayBindings data,ArrayOrigin origin) {}
    record SelectionKey(Map<ArrayKey,ArrayView> arrays,int definitions) {SelectionKey {arrays=Map.copyOf(arrays);}}
    record Selection(List<Value> operands,SelectionKey key) {Selection {operands=List.copyOf(operands);}}
    private record MemberMatch(RelationState state,int preference) {}
    private static final Selection EMPTY=new Selection(List.of(),new SelectionKey(Map.of(),0));
    record Progress(Optional<Site> site,Optional<MethodId> target,List<Atom> operands,Path path,Rank rank,Optional<Integer> witness,Set<Site> visited) {
        static final Progress EMPTY=new Progress(Optional.empty(),Optional.empty(),List.of(),Path.EMPTY,Rank.NONE,Optional.empty(),Set.of());
    }
    private final Mechanisms knowledge;
    private final Program program;
    private final Map<Site,Set<CallShape.Pattern>> requirements=new HashMap<>();
    private final Set<Site> uncertainSources=new HashSet<>();
    private final Set<MethodId> learned=new HashSet<>();
    private final Set<Hint> hints=new LinkedHashSet<>();
    private final Set<QueryIssue> issues=new LinkedHashSet<>();
    private int associations;
    private boolean enabled;
    SearchRanking(Mechanisms knowledge,Program program){this.knowledge=knowledge;this.program=program;}
    void configure(boolean enabled,List<Hint> initial){this.enabled=enabled;initial.forEach(this::add);}
    private void add(Hint hint) {
        List<CallShape.Requirement> retained=new ArrayList<>();
        for(var requirement:hint.requirements()) {
            Set<CallShape.Pattern> known=requirements.getOrDefault(requirement.site(),Set.of());
            if(!known.contains(requirement.pattern())) {
                if(associations>=8192){issues.add(new QueryIssue(QueryCause.BUDGET,"ranking source relation frontier (8192)"));continue;}
                if(!requirements.containsKey(requirement.site())) {
                    Action action=program.flow(requirement.site().method()).producers().get(requirement.site().instruction());
                    if(!(action instanceof Call call))throw new IllegalStateException("ranking requirement is not a call: "+requirement.site());
                    if(CallShape.of(program,call).operands().stream().anyMatch(CallShape.Operand::unknown))uncertainSources.add(requirement.site());
                }
                requirements.computeIfAbsent(requirement.site(),k -> new LinkedHashSet<>()).add(requirement.pattern());associations++;
            }
            retained.add(requirement);
        }
        if(!retained.isEmpty()) {
            if(hints.size()<8192)hints.add(new Hint(hint.anchor(),hint.mechanism(),hint.source(),hint.pendingRelations(),retained,hint.references()));
            else issues.add(new QueryIssue(QueryCause.BUDGET,"ranking hint output frontier (8192)"));
        }
    }
    private Set<CallShape.Pattern> at(Site site) {
        if(!enabled)return Set.of();
        if(learned.add(site.method())) {
            Query<List<Hint>> local=knowledge.hints(site.method());local.value().orElseThrow().forEach(this::add);issues.addAll(local.pending());
        }
        return requirements.getOrDefault(site,Set.of());
    }
    Progress advance(Progress parent,Site site,MethodId target,Atom receiver,List<Atom> arguments,Path path) {
        return advance(parent,site,target,receiver,arguments,path,Optional.empty());
    }
    Progress advance(Progress parent,Site site,MethodId target,Atom receiver,List<Atom> arguments,Path path,Optional<ScanResult.Relation> edge) {
        Set<CallShape.Pattern> shapes=at(site);if(shapes.isEmpty())return Progress.EMPTY;
        List<Atom> tuple=new ArrayList<>();tuple.add(receiver);tuple.addAll(arguments);
        boolean callback=edge.filter(relation -> switch(relation.kind()) {
            case DESERIALIZATION,CONTAINER_CALLBACK,REFLECTION,METHOD_HANDLE,DYNAMIC_CALL,HTTP_CALLBACK -> true;default -> false;
        }).isPresent();
        // A callback has its own tuple. It must not be compared with the API's operand positions.
        Match match=callback?new Match(RelationState.PENDING,1):match(site,shapes,tuple,path,EMPTY);
        if(match.state()==RelationState.REFUTED)return Progress.EMPTY;
        Rank rank=match.state()==RelationState.SUPPORTED?Rank.BOUND:Rank.PARTIAL;
        boolean data=parent.witness().isPresent() && edge.stream().flatMap(relation -> relation.supports().stream()).anyMatch(s -> s.dependencies().contains(parent.witness().orElseThrow()));
        boolean handoff=parent.target().equals(Optional.of(site.method())) && !parent.target().equals(Optional.of(target))
                && parent.site().isPresent() && !parent.visited().contains(site) && parent.visited().size()<64 && parent.path().compatible(path)
                && data && tuple.stream().anyMatch(value -> parent.operands().stream().anyMatch(previous -> handoff(previous,value,callback,parent.path(),path)));
        if(handoff)rank=Rank.CONTINUED;
        Set<Site> visited=new LinkedHashSet<>(parent.visited());if(visited.size()<64)visited.add(site);
        return new Progress(Optional.of(site),Optional.of(target),List.copyOf(tuple),path,rank,edge.map(ScanResult.Relation::id),Set.copyOf(visited));
    }
    private static boolean handoff(Atom from,Atom to,boolean callback,Path before,Path after) {
        boolean requested=requestedBinding(from,before) && requestedBinding(to,after);
        if(from instanceof ObjectValue a && to instanceof ObjectValue b && a.id()==b.id() && a.loader()==b.loader())return !requested;
        if(from instanceof LambdaValue a && to instanceof LambdaValue b)return a.id()==b.id() && a.factory().equals(b.factory());
        if(from instanceof ProxyValue a && to instanceof ProxyValue b)return a.id()==b.id() && a.factory().equals(b.factory());
        Optional<InputLocation> first=Values.location(from),second=Values.location(to);
        if(first.isPresent() && first.equals(second))return !requested;
        // A modeled read may produce a child of its actual stream/source. This is lineage, not aliasing.
        return callback && first.isPresent() && first.get() instanceof InputSource a && second.isPresent() && second.get() instanceof InputSource b
                && a.entry().equals(b.entry()) && a.parameterSlot()==b.parameterSlot() && a.path().size()<b.path().size()
                && b.path().subList(0,a.path().size()).equals(a.path());
    }
    Rank work(Progress progress,Optional<Call> call) {
        if(!enabled)return Rank.NONE;
        if(call.isPresent())return at(call.get().site()).isEmpty()?Rank.NONE:Rank.PARTIAL;
        return progress.rank();
    }
    Match match(Site site,List<Atom> tuple,Path path) {
        return match(site,at(site),tuple,path,EMPTY);
    }
    private Match match(Site site,Set<CallShape.Pattern> patterns,List<Atom> tuple,Path path,Selection selection) {
        if(patterns.isEmpty())return new Match(RelationState.ABSENT,0);
        Match best=new Match(RelationState.REFUTED,0);
        Atom[] projected=null;
        var arrays=selection.key().arrays();
        for(CallShape.Pattern pattern:patterns) {
            if(tuple.size()>pattern.operands().size())continue;
            boolean conflict=false,pending=uncertainSources.contains(site) || pattern.operands().stream().anyMatch(CallShape.Operand::unknown);int supported=0;
            for(int i=0;i<tuple.size();i++) {
                Atom original=tuple.get(i);
                var operand=pattern.operands().get(i);
                int binding=operand.value();
                for(int j=0;binding>=0 && j<i;j++) {
                    if(binding!=pattern.operands().get(j).value())continue;
                    if(projected==null)projected=new Atom[tuple.size()];
                    if(projected[i]==null)projected[i]=CandidateBindings.project(original,path);
                    if(projected[j]==null)projected[j]=CandidateBindings.project(tuple.get(j),path);
                    Atom atom=projected[i],previous=projected[j];
                    if(!atom.equals(previous)) {
                        Optional<Boolean> different=atom instanceof Literal a && previous instanceof Literal b?Optional.of(!a.equals(b)):
                                new JvmSemantics(program).branchTaken(new Branch(site,org.objectweb.asm.Opcodes.IF_ACMPNE,List.of(),0),List.of(Value.of(atom),Value.of(previous)));
                        if(different.orElse(false))conflict=true;
                        else if(different.isEmpty())pending=true;
                    }
                }
                if(!ValueBindings.finiteBinding(original) || requestedBinding(original,path)
                        || !arrays.isEmpty() && arrays.entrySet().stream().anyMatch(e -> e.getKey().atom().equals(original)
                        && e.getKey().path().compatible(path) && e.getValue().origin()==ArrayOrigin.REQUESTED))pending=true;
                else if(!operand.unknown() && operand.steps().stream().noneMatch(s -> s.kind()==CallShape.SourceKind.ABSENT))supported++;
            }
            if(conflict)continue;
            MemberMatch member=member(site,tuple,path,selection);if(member.state()==RelationState.REFUTED)continue;
            // Finite but irrelevant values cannot outrank an actual member/receiver relationship.
            int priority=member.preference()>0?3+member.preference():supported>0?2:1;
            RelationState state=!pending && tuple.size()==pattern.operands().size() && member.state()!=RelationState.PENDING?RelationState.SUPPORTED:RelationState.PENDING;
            if(priority>best.priority() || priority==best.priority() && state==RelationState.SUPPORTED)best=new Match(state,priority);
        }
        return best;
    }
    private static boolean requestedBinding(Atom value,Path path) {
        // JVM projection can use a selected type without turning the question into a supplied fact.
        return Values.location(value).map(source -> value instanceof ObjectValue
                ?path.selected(source.at(new RuntimeClass())).isPresent()
                :value instanceof ClassValue && path.selected(source).isPresent()).orElse(false);
    }
    private MemberMatch member(Site site,List<Atom> tuple,Path path,Selection selection) {
        if(tuple.isEmpty())return new MemberMatch(RelationState.ABSENT,0);
        Action action=program.flow(site.method()).producers().get(site.instruction());if(!(action instanceof Call operation))return new MemberMatch(RelationState.ABSENT,0);
        boolean invoke=operation.target().owner().equals("java/lang/reflect/Method") && operation.target().name().equals("invoke");
        boolean lookup=operation.target().owner().equals("java/lang/Class") && Set.of("getMethod","getDeclaredMethod").contains(operation.target().name());
        if(!invoke && !lookup)return new MemberMatch(RelationState.ABSENT,0);
        if(invoke && tuple.get(0) instanceof Reflected reflected && reflected.declaringClass() instanceof ClassValue owner && owner.exact()
                && reflected.name() instanceof Literal name && name.value() instanceof String text) {
            Optional<List<Atom>> signature=contents(reflected.parameterTypes(),path,selection,site);
            if(signature.isEmpty() || !signature.get().stream().allMatch(a -> a instanceof ClassValue type && type.exact()))return new MemberMatch(RelationState.PENDING,0);
            Query<Method> selected=program.reflect(Values.type(owner.descriptor()),text,signature.get().stream().map(a -> ((ClassValue)a).descriptor()).toList(),reflected.declared(),owner.loader());
            if(selected.absent() || selected.value().isPresent() && !ValueBindings.sameSignature(selected.value().get().id(),signature.get(),program))return new MemberMatch(RelationState.REFUTED,0);
            if(selected.value().isEmpty())return new MemberMatch(RelationState.PENDING,0);
            if(tuple.size()>1 && !selected.value().get().isStatic()) {
                Atom receiver=tuple.get(1);
                if(ValueBindings.compatible(receiver,"L"+selected.value().get().id().owner()+";",program,selected.value().get().id().loader()).match()==ValueBindings.Match.INCOMPATIBLE)return new MemberMatch(RelationState.REFUTED,0);
            }
            if(tuple.size()>2) {
                Optional<List<Atom>> arguments=contents(tuple.get(2),path,selection,site);
                if(arguments.isEmpty())return new MemberMatch(RelationState.PENDING,knowledge.preferredMember(selected.value().get().id())?2:1);
                List<ValueType> expected=program.signature(selected.value().get().id()).parameters();if(expected.size()!=arguments.get().size())return new MemberMatch(RelationState.REFUTED,0);
                for(int i=0;i<expected.size();i++)if(ValueBindings.compatible(arguments.get().get(i),expected.get(i).descriptor(),program,selected.value().get().id().loader()).match()==ValueBindings.Match.INCOMPATIBLE)return new MemberMatch(RelationState.REFUTED,0);
            }
            return new MemberMatch(RelationState.SUPPORTED,knowledge.preferredMember(selected.value().get().id())?2:1);
        }
        if(lookup && tuple.get(0) instanceof ClassValue owner && owner.exact() && tuple.size()>1 && tuple.get(1) instanceof Literal name && name.value() instanceof String text) {
            boolean declared=operation.target().name().equals("getDeclaredMethod");
            if(tuple.size()>2) {
                Optional<List<Atom>> signature=contents(tuple.get(2),path,selection,site);
                if(signature.isPresent() && signature.get().stream().allMatch(a -> a instanceof ClassValue type && type.exact())) {
                    Query<Method> selected=program.reflect(Values.type(owner.descriptor()),text,signature.get().stream().map(a -> ((ClassValue)a).descriptor()).toList(),declared,owner.loader());
                    if(selected.absent() || selected.value().isPresent() && !ValueBindings.sameSignature(selected.value().get().id(),signature.get(),program))return new MemberMatch(RelationState.REFUTED,0);
                    return selected.value().map(method -> new MemberMatch(RelationState.SUPPORTED,knowledge.preferredMember(method.id())?2:1)).orElse(new MemberMatch(RelationState.PENDING,0));
                }
            }
            Query<List<Method>> methods=program.methods(Values.type(owner.descriptor()),declared,owner.loader());
            List<Method> named=methods.value().orElseThrow().stream().filter(method -> method.id().name().equals(text)).toList();
            if(named.isEmpty())return new MemberMatch(methods.pending().isEmpty()?RelationState.REFUTED:RelationState.PENDING,0);
            return new MemberMatch(RelationState.PENDING,named.stream().anyMatch(method -> knowledge.preferredMember(method.id()))?2:1);
        }
        return new MemberMatch(RelationState.PENDING,0);
    }
    private Optional<List<Atom>> contents(Atom atom,Path path,Selection selection,Site site) {
        if(atom instanceof ArrayValue || atom instanceof Literal literal && literal.value()==null) {
            var values=ValueBindings.array(atom,(object,slot) -> Value.BOTTOM,path,site);
            return values.frontier().isEmpty() && values.values().size()==1?Optional.of(values.values().get(0).elements()):Optional.empty();
        }
        List<ValueBindings.ArrayBinding> candidates=new ArrayList<>();
        for(var entry:selection.key().arrays().entrySet())if(entry.getKey().atom().equals(atom) && entry.getKey().path().compatible(path)) {
            if(!entry.getValue().data().frontier().isEmpty())return Optional.empty();
            entry.getValue().data().values().stream().filter(value -> value.path().compatible(path)).forEach(candidates::add);
        }
        return candidates.size()==1?Optional.of(candidates.get(0).elements()):Optional.empty();
    }
    Selection selection(Call call,List<Value> operands,Path path,Mechanisms.Bindings heap,int definitions) {
        Map<ArrayKey,ArrayView> arrays=new LinkedHashMap<>();
        boolean lookup=call.target().owner().equals("java/lang/Class") && Set.of("getMethod","getDeclaredMethod").contains(call.target().name());
        boolean invoke=call.target().owner().equals("java/lang/reflect/Method") && call.target().name().equals("invoke");
        if((lookup || invoke) && operands.size()>2)for(Bound bound:operands.get(2).alternatives())path.and(bound.path()).ifPresent(selected -> snapshot(call,bound.atom(),selected,heap,arrays));
        if(invoke)for(Bound bound:operands.get(0).alternatives())if(bound.atom() instanceof Reflected member)path.and(bound.path()).ifPresent(selected -> snapshot(call,member.parameterTypes(),selected,heap,arrays));
        return new Selection(operands,new SelectionKey(arrays,definitions));
    }
    private void snapshot(Call call,Atom atom,Path path,Mechanisms.Bindings heap,Map<ArrayKey,ArrayView> arrays) {
        if(!(atom instanceof ObjectValue object) || !object.type().startsWith("["))return;
        ArrayKey key=new ArrayKey(atom,path);if(arrays.containsKey(key))return;
        Set<ArrayOrigin> origins=EnumSet.of(ArrayOrigin.FACTS);
        var result=ValueBindings.array(atom,(receiver,slot) -> {
            Value value=heap.read(receiver,slot);
            if(value.empty() && Values.location(receiver).flatMap(source -> path.selected(source.at(slot))).isPresent())origins.add(ArrayOrigin.REQUESTED);
            return value;
        },path,call.site());
        arrays.put(key,new ArrayView(result,origins.contains(ArrayOrigin.REQUESTED)?ArrayOrigin.REQUESTED:ArrayOrigin.FACTS));
    }
    List<Bound> order(Call call,Combinations.Combination prefix,List<Bound> values) {return order(call,prefix,values,EMPTY);}
    List<Bound> order(Call call,Combinations.Combination prefix,List<Bound> values,Selection selection) {
        if(values.size()<2)return values;
        Set<CallShape.Pattern> patterns=at(call.site());
        if(patterns.isEmpty())return values;
        record Scored(Bound value,Match match) {}
        List<Scored> scored=new ArrayList<>(values.size());
        int prefixSize=prefix.atoms().size();
        List<Atom> tuple=new ArrayList<>(Math.max(prefixSize+1,selection.operands().size()));
        tuple.addAll(prefix.atoms());
        for(Bound value:values) {
            Optional<Path> path=prefix.path().and(value.path());
            if(path.isEmpty()) {
                scored.add(new Scored(value,new Match(RelationState.REFUTED,0)));
                continue;
            }
            tuple.add(value.atom());
            // Only single known suffixes are previewed; there is no Cartesian lookahead.
            while(path.isPresent() && tuple.size()<selection.operands().size()) {
                Set<Bound> suffix=selection.operands().get(tuple.size()).alternatives();if(suffix.size()!=1)break;
                Bound next=suffix.iterator().next();path=path.get().and(next.path());tuple.add(next.atom());
            }
            scored.add(new Scored(value,path.isEmpty()?new Match(RelationState.REFUTED,0):match(call.site(),patterns,tuple,path.get(),selection)));
            while(tuple.size()>prefixSize)tuple.remove(tuple.size()-1);
        }
        scored.sort(Comparator.comparingInt((Scored item) -> item.match().priority()).reversed()
                .thenComparing(item -> item.match().state()!=RelationState.SUPPORTED));
        Set<Bound> result=new LinkedHashSet<>();
        int plain=0;
        for(Scored item:scored) {
            result.add(item.value());
            if(result.size()%4!=3)continue;
            while(plain<values.size() && result.contains(values.get(plain)))plain++;
            if(plain<values.size())result.add(values.get(plain++));
        }
        return List.copyOf(result);
    }
    boolean applies(Call call){return !at(call.site()).isEmpty();}
    Query<List<DefinedType>> receivers(Call call,String upper,int loader) {
        if(!enabled)return new Query<>(Optional.of(List.of()),List.of());
        Query<List<DefinedType>> query=knowledge.preferredReceivers(call.target(),upper,loader);issues.addAll(query.pending());return query;
    }
    List<Hint> hints(){return List.copyOf(hints);}
    void note(Collection<QueryIssue> pending){issues.addAll(pending);}
    Set<QueryIssue> issues(){return Set.copyOf(issues);}
}
