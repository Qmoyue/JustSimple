package io.just.analysis;

import io.just.analysis.ScanResult.*;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.EntryPoints.Entry;
import java.util.*;

/** Owns relation identity, necessary evidence and the single candidate conclusion. No scheduling. */
final class EvidenceGraph {
    record Context(int parent,int parentRelation,Entry entry,List<Gap> required) {}
    enum Control { NORMAL,HANDLER,BRANCH,SAFETY }
    private enum ControlPart { WITNESS,ALTERNATIVE }
    private record ControlKey(Control role,int operand,ControlPart part) {}
    private record Key(int context,Site site,Kind kind,Optional<MethodId> target,Atom receiver,
                       List<Atom> arguments,Path path,Optional<Slot> slot,Optional<ControlKey> control) { Key {arguments=List.copyOf(arguments);} }
    private record Observation(int context,int relation,List<Integer> additional) {
        Observation {additional=List.copyOf(additional);}
    }
    private final int relationLimit,findingLimit,supportLimit;
    private final Map<Key,Integer> ids=new LinkedHashMap<>();
    private final List<Relation> relations=new ArrayList<>();
    private long derivations;
    long derivations(){return derivations;}
    private final Set<Observation> observations=new LinkedHashSet<>();
    private final Conditions conditions;
    private final Set<String> limitations=new LinkedHashSet<>();
    private final List<Breakpoint> coverage=new ArrayList<>();
    private record Family(MethodId entry,Kind boundary,Optional<MethodId> terminal,Set<Kind> mechanisms,Set<MethodId> triggers) {}
    private record Member(String owner,String name,int loader) {}
    private record MemberFamily(MethodId entry,Kind boundary,Optional<Member> terminal,Set<Kind> mechanisms,Set<MethodId> triggers) {}

    EvidenceGraph(int relationLimit,int findingLimit,int supportLimit,Conditions conditions) {this.relationLimit=relationLimit;this.findingLimit=findingLimit;this.supportLimit=supportLimit;this.conditions=conditions;}
    int record(int context,Site site,Kind kind,Optional<MethodId> target,Evidence evidence,Atom receiver,List<Atom> arguments,
               List<Site> witnesses,List<Gap> gaps,Path path,String detail,Collection<Integer> dependencies,Optional<Slot> slot) {
        return record(context,site,kind,target,evidence,receiver,arguments,witnesses,gaps,path,detail,dependencies,slot,Optional.empty());
    }
    private int record(int context,Site site,Kind kind,Optional<MethodId> target,Evidence evidence,Atom receiver,List<Atom> arguments,
               List<Site> witnesses,List<Gap> gaps,Path path,String detail,Collection<Integer> dependencies,Optional<Slot> slot,Optional<ControlKey> control) {
        Key key=new Key(context,site,kind,target,receiver,arguments,path,slot,control);
        List<Gap> required=union(gaps,conditions.gaps(path));Integer existing=ids.get(key);
        Support support=new Support(evidence,witnesses,required,dependencies.stream().distinct().sorted().toList());
        if (existing!=null) {
            Relation old=relations.get(existing);
            if(old.supports().contains(support))return existing;
            if(old.supports().size()>=supportLimit){limitations.add("relation alternative support budget: "+supportLimit);return existing;}
            List<Support> alternatives=new ArrayList<>(old.supports());alternatives.add(support);
            derivations++;
            relations.set(existing,new Relation(existing,context,kind,site,target,receiver,old.arguments(),alternatives,path,old.detail(),slot));
            return existing;
        }
        if (relations.size()>=relationLimit) {limitations.add("relation budget: "+relationLimit);return -1;}
        int id=relations.size();ids.put(key,id);
        derivations++;
        relations.add(new Relation(id,context,kind,site,target,receiver,arguments,List.of(support),path,detail,slot));
        return id;
    }
    void observe(int context,int relation,List<Integer> additional) {
        if (relation>=0)observations.add(new Observation(context,relation,additional));
    }
    List<Relation> snapshot() {return List.copyOf(relations);}
    Optional<Relation> relation(int id){return id>=0 && id<relations.size()?Optional.of(relations.get(id)):Optional.empty();}
    int size() {return relations.size();}
    List<String> limitations() {return List.copyOf(limitations);}
    List<Breakpoint> coverage(){return List.copyOf(coverage);}
    private Family family(Observation observation,List<Context> contexts) {
        Relation endpoint=relations.get(observation.relation());Context context=contexts.get(observation.context());
        Set<Kind> mechanisms=new LinkedHashSet<>();Set<MethodId> triggers=new LinkedHashSet<>();
        while(context.parent()>=0) {
            if(context.parentRelation()>=0) {
                Relation call=relations.get(context.parentRelation());mechanisms.add(call.kind());
                if(call.kind()==Kind.CONTAINER_CALLBACK)for(Support support:call.supports())for(Site witness:support.witnesses())triggers.add(witness.method());
            }
            context=contexts.get(context.parent());
        }
        for(int edge:observation.additional())mechanisms.add(relations.get(edge).kind());
        Optional<MethodId> target=endpoint.target();
        if(target.isEmpty())for(int edge:observation.additional())if(relations.get(edge).target().isPresent())target=relations.get(edge).target();
        return new Family(context.entry().method().id(),endpoint.kind(),target,Set.copyOf(mechanisms),Set.copyOf(triggers));
    }
    private List<Observation> ordered(List<Context> contexts) {
        Map<MemberFamily,Map<Family,ArrayDeque<Observation>>> families=new LinkedHashMap<>();
        for(Observation observation:observations) {
            Family exact=family(observation,contexts);
            MemberFamily member=new MemberFamily(exact.entry(),exact.boundary(),exact.terminal().map(id -> new Member(id.owner(),id.name(),id.loader())),exact.mechanisms(),exact.triggers());
            families.computeIfAbsent(member,key -> new LinkedHashMap<>()).computeIfAbsent(exact,key -> new ArrayDeque<>()).addLast(observation);
        }
        List<ArrayDeque<Observation>> chains=new ArrayList<>(),fragments=new ArrayList<>();
        for(var member:families.entrySet()) {
            ArrayDeque<Observation> variants=interleave(member.getValue().values());
            (member.getKey().boundary()==Kind.IMPACT?chains:fragments).add(variants);
        }
        List<ArrayDeque<Observation>> boundaries=new ArrayList<>();
        if(!chains.isEmpty())boundaries.add(interleave(chains));
        if(!fragments.isEmpty())boundaries.add(interleave(fragments));
        return List.copyOf(interleave(boundaries));
    }
    private static <T> ArrayDeque<T> interleave(Collection<ArrayDeque<T>> families) {
        ArrayDeque<ArrayDeque<T>> queue=new ArrayDeque<>(families);ArrayDeque<T> result=new ArrayDeque<>();
        while(!queue.isEmpty()){ArrayDeque<T> family=queue.removeFirst();result.addLast(family.removeFirst());if(!family.isEmpty())queue.addLast(family);}
        return result;
    }

    private record ValueKey(Atom atom,Path path) {}
    private record ChainKey(MethodId entry,Kind boundary,List<Integer> path,Path conditions) {}
    /** Factor alternative derivations of one value into this graph, without multiplying downstream tuples. */
    Value compact(int context,Site site,Value value) {
        if(value.alternatives().size()<2)return value;
        Map<ValueKey,List<Bound>> groups=new LinkedHashMap<>();
        for(Bound bound:value.alternatives())groups.computeIfAbsent(new ValueKey(bound.atom(),bound.path()),k -> new ArrayList<>()).add(bound);
        Set<Bound> result=new LinkedHashSet<>();
        for(var group:groups.entrySet()) {
            if(group.getValue().size()==1){result.add(group.getValue().get(0));continue;}
            ValueKey valueKey=group.getKey();Atom receiver=new Literal(null);
            Key key=new Key(context,site,Kind.VALUE_FLOW,Optional.empty(),receiver,List.of(valueKey.atom()),valueKey.path(),Optional.empty(),Optional.empty());
            int fact=ids.getOrDefault(key,-1);
            Set<Gap> common=new LinkedHashSet<>(group.getValue().get(0).gaps());
            for(Bound bound:group.getValue()) {
                if(!common.isEmpty())common.retainAll(new HashSet<>(bound.gaps()));
                if(fact>=0 && bound.dependencies().equals(Set.of(fact)))continue;
                fact=record(context,site,Kind.VALUE_FLOW,Optional.empty(),Evidence.PROVEN,receiver,List.of(bound.atom()),List.of(site),bound.gaps(),bound.path(),"alternative bytecode value derivation",bound.dependencies(),Optional.empty());
            }
            if(fact<0)result.addAll(group.getValue());
            else {Bound first=group.getValue().get(0);result.add(new Bound(first.atom(),first.path(),List.copyOf(common),Set.of(fact)));}
        }
        return new Value(result);
    }

    /** Any compatible control witness suffices; its necessary conditions remain on that witness. */
    Value control(int context,Site site,Value completions,Path use) {
        return control(context,site,completions,use,Control.NORMAL,0);
    }
    Value control(int context,Site site,Value completions,Path use,Control role,int operand) {
        Value visible=completions.under(use);if(visible.empty())return Value.BOTTOM;
        int fact=-1;Optional<Set<Gap>> common=Optional.empty();
        for(Bound bound:visible.alternatives()) {
            if(common.isEmpty())common=Optional.of(new LinkedHashSet<>(bound.gaps()));else if(!common.get().isEmpty())common.get().retainAll(new HashSet<>(bound.gaps()));
            int witness=record(context,site,Kind.CONTROL_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(bound.atom()),List.of(site),bound.gaps(),bound.path(),role+" reachability witness",bound.dependencies(),Optional.empty(),Optional.of(new ControlKey(role,operand,ControlPart.WITNESS)));
            if(witness<0)return visible;
            fact=record(context,site,Kind.CONTROL_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(),List.of(site),List.of(),use,"one compatible "+role+" witness suffices",Set.of(witness),Optional.empty(),Optional.of(new ControlKey(role,operand,ControlPart.ALTERNATIVE)));
        }
        Atom completion=visible.alternatives().stream().allMatch(b -> b.atom()==NormalValue.CERTAIN)?NormalValue.CERTAIN:new Literal(null);
        return fact<0?Value.BOTTOM:Value.of(completion,use).requiring(List.copyOf(common.orElseThrow())).tracing(Set.of(fact));
    }

    List<Finding> findings(List<Context> contexts) {
        List<Finding> result=new ArrayList<>();Set<ChainKey> emitted=new HashSet<>();List<Observation> ordered=ordered(contexts);coverage.clear();
        long remaining=relationLimit*4L;

        for (int position=0;position<ordered.size();position++) {
            Observation observation=ordered.get(position);
            if (result.size()>=findingLimit) {
                limitations.add("finding/path budget: "+findingLimit+"; observed variants not displayed: "+(ordered.size()-position));
                Map<Family,List<Observation>> omitted=new LinkedHashMap<>();
                for(Observation item:ordered.subList(position,ordered.size()))omitted.computeIfAbsent(family(item,contexts),k -> new ArrayList<>()).add(item);
                for(List<Observation> group:omitted.values()) {
                    Observation first=group.get(0);Relation endpoint=relations.get(first.relation());
                    coverage.add(new Breakpoint(first.context(),endpoint.site(),endpoint.conditions(),Optional.of(endpoint.receiver()),endpoint.slot(),List.of(endpoint.id()),GapKind.BUDGET,Optional.empty(),Optional.of(endpoint.site()),"finding/path budget: "+group.size()+" observed variants in this entry/terminal/mechanism family remain in relations"));
                }
                break;
            }
            Context current=contexts.get(observation.context());Entry entry=current.entry();
            List<Integer> path=new ArrayList<>();Set<Gap> gaps=new LinkedHashSet<>();
            while (current.parent()>=0) {
                if (current.parentRelation()>=0)path.add(current.parentRelation());
                else gaps.add(new Gap(GapKind.BUDGET,relations.get(observation.relation()).site(),"call relation omitted by relation budget"));
                gaps.addAll(current.required());current=contexts.get(current.parent());
            }
            Collections.reverse(path);path.addAll(observation.additional());path.add(observation.relation());
            path=new ArrayList<>(new LinkedHashSet<>(path));
            Relation endpoint=relations.get(observation.relation());
            Recovery search=new Recovery(remaining);
            Pending pending=null;for(int at=path.size()-1;at>=0;at--)pending=new Pending(path.get(at),false,pending);
            search.seek(pending,List.copyOf(gaps),endpoint.conditions());
            remaining-=search.visited;
            if(search.best==null && !search.truncated)continue; // Every explored support contradicts this binding.
            Trace selected=search.best!=null?search.best:frontier(endpoint,endpoint.conditions(),"chain support selection budget");
            Map<Integer,Integer> chosen=selected.chosen();Path selection=selected.path();
            Set<Integer> supporting=new LinkedHashSet<>(chosen.keySet());supporting.removeAll(path);
            if(!emitted.add(new ChainKey(entry.method().id(),endpoint.kind(),List.copyOf(path),selection)))continue;
            result.add(new Finding(result.size(),entry,endpoint.kind(),List.copyOf(path),List.copyOf(supporting),
                    selected.gaps(),selection,endpoint.detail(),chosen.entrySet().stream().map(e -> new ProofUse(e.getKey(),e.getValue())).toList()));
        }
        return List.copyOf(result);
    }
    private record Trace(List<Gap> gaps,Map<Integer,Integer> chosen,Path path) {}
    private record Pending(int relation,boolean finish,Pending next) {}
    private record Trial(Pending pending,List<Gap> gaps,Path path,int choices,Set<Integer> active,int support,boolean cyclic) {}
    /** Prefer a compatible non-cyclic assignment; keep a cyclic one as an unresolved fallback. */
    private final class Recovery {
        final long budget;Trace best;int visited;boolean truncated;
        Recovery(long budget){this.budget=budget;}
        void seek(Pending initial,List<Gap> initialGaps,Path initialPath) {
            ArrayDeque<Trial> trials=new ArrayDeque<>();trials.addLast(new Trial(initial,initialGaps,initialPath,0,Set.of(),0,false));
            Map<Integer,Integer> chosen=new LinkedHashMap<>();List<Integer> choices=new ArrayList<>();
            while(!trials.isEmpty()) {
                Trial trial=trials.removeLast();
                while(choices.size()>trial.choices())chosen.remove(choices.remove(choices.size()-1));
                // A compatible cyclic fallback is retained; only an acyclic derivation can improve it.
                if(best!=null && trial.cyclic())continue;
                Pending pending=trial.pending();List<Gap> gaps=trial.gaps();Path selected=trial.path();Set<Integer> active=new HashSet<>(trial.active());int start=trial.support();boolean cyclic=trial.cyclic();
                while(pending!=null) {
                    int id=pending.relation();Relation relation=relations.get(id);
                    if(pending.finish()){active.remove(id);pending=pending.next();continue;}
                    if(chosen.containsKey(id)) {
                        if(active.contains(id)) {
                            if(best!=null)break;
                            cyclic=true;gaps=union(gaps,List.of(new Gap(GapKind.UNSUPPORTED,relation.site(),"selected support contains a cycle")));
                        }
                        pending=pending.next();continue;
                    }
                    if(Thread.currentThread().isInterrupted())throw new java.util.concurrent.CancellationException("chain recovery interrupted");
                    if(visited>=budget || active.size()>=512) {
                        truncated=true;limitations.add("chain recovery budget");
                        Gap limit=new Gap(GapKind.BUDGET,relation.site(),"chain recovery budget");
                        Trace cut=new Trace(union(gaps,List.of(limit)),Collections.unmodifiableMap(new LinkedHashMap<>(chosen)),selected);
                        if(best==null)best=cut;else best=new Trace(union(best.gaps(),List.of(limit)),best.chosen(),best.path());
                        return;
                    }
                    visited++;
                    boolean matched=false;
                    for(int position=start;position<relation.supports().size();position++) {
                        int index=position;Support support=relation.supports().get(index);Optional<Path> path=selected.and(relation.conditions());
                        for(int dependency:support.dependencies())if(path.isPresent())path=path.get().and(relations.get(dependency).conditions());
                        if(path.isEmpty() || !conditions.compatible(path.get(),union(gaps,support.gaps())))continue;
                        if(position+1<relation.supports().size())trials.addLast(new Trial(pending,gaps,selected,choices.size(),Set.copyOf(active),position+1,cyclic));
                        chosen.put(id,index);choices.add(id);gaps=union(gaps,support.gaps());selected=path.get();
                        Pending next=new Pending(id,true,pending.next());
                        for(int at=support.dependencies().size()-1;at>=0;at--)next=new Pending(support.dependencies().get(at),false,next);
                        active.add(id);pending=next;matched=true;break;
                    }
                    start=0;if(!matched)break;
                }
                if(pending!=null)continue;
                Set<Gap> required=new LinkedHashSet<>(gaps);required.addAll(conditions.gaps(selected));
                if(!conditions.compatible(selected,required))continue;
                Path binding=selected;required.removeIf(g -> conditions.satisfied(g,binding));
                Trace complete=new Trace(List.copyOf(required),Collections.unmodifiableMap(new LinkedHashMap<>(chosen)),selected);
                if(!cyclic){best=complete;return;}
                if(best==null)best=complete;
            }
        }
    }
    private Trace frontier(Relation relation,Path path,String detail) {
        return new Trace(List.of(new Gap(GapKind.BUDGET,relation.site(),detail)),Map.of(),path);
    }
    private static <T> List<T> union(List<T> first,List<T> second) {
        if(second.isEmpty())return first;if(first.isEmpty())return List.copyOf(second);
        Set<T> values=new LinkedHashSet<>(first);values.addAll(second);
        return values.size()==first.size()?first:List.copyOf(values);
    }
}
