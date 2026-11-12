package io.just.analysis;

import io.just.analysis.ScanResult.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import java.util.*;
import java.util.concurrent.CancellationException;

/** Checks selected, already-derived supports; never guesses a support or reconstructs heap bindings. */
public final class ConnectionCheck {
    private ConnectionCheck() {}
    public enum State { CLOSED, PENDING, CONTRADICTED }
    public record Result(State state, int budget, int inspected, List<ProofUse> uses, List<Integer> frontier,
                         List<Gap> gaps, List<String> pending, String detail) {
        public Result {uses=List.copyOf(uses);frontier=List.copyOf(frontier);gaps=List.copyOf(gaps);pending=List.copyOf(pending);}
    }
    public static Result query(Program program, List<Relation> evidence, List<Integer> roots, List<ProofUse> choices, int budget) {
        if(budget<1 || roots.isEmpty())throw new IllegalArgumentException("connection check requires roots and positive budget");
        Map<Integer,Relation> relations=new HashMap<>();evidence.forEach(r -> relations.put(r.id(),r));
        Map<Integer,Integer> selected=new HashMap<>();
        for(ProofUse use:choices) {
            Relation relation=relations.get(use.relation());
            if(relation==null || use.support()<0 || use.support()>=relation.supports().size())throw new IllegalArgumentException("unknown support: "+use);
            Integer previous=selected.putIfAbsent(use.relation(),use.support());
            if(previous!=null && previous!=use.support())throw new IllegalArgumentException("choose one support per relation");
        }
        for(int root:roots)if(!relations.containsKey(root))throw new IllegalArgumentException("unknown relation: "+root);
        ArrayDeque<Integer> queue=new ArrayDeque<>(roots);Set<Integer> seen=new LinkedHashSet<>(),frontier=new LinkedHashSet<>();
        List<ProofUse> uses=new ArrayList<>();Set<Gap> gaps=new LinkedHashSet<>();Set<String> pending=new LinkedHashSet<>();
        Map<Integer,List<Integer>> dependencies=new HashMap<>();Path path=Path.EMPTY;
        while(!queue.isEmpty()) {
            if(Thread.currentThread().isInterrupted())throw new CancellationException("connection check interrupted");
            int id=queue.removeFirst();if(seen.contains(id))continue;
            if(seen.size()>=budget){frontier.add(id);continue;}
            Relation relation=relations.get(id);
            if(relation==null){frontier.add(id);pending.add("dependency not present in this result: "+id);continue;}
            seen.add(id);Optional<Path> merged=path.and(relation.conditions());
            if(merged.isEmpty() || merged.get().selections().values().stream().anyMatch(s -> !CandidateBindings.compatible(s,program)))
                return new Result(State.CONTRADICTED,budget,seen.size(),uses,List.copyOf(frontier),List.copyOf(gaps),List.copyOf(pending),"selected relations require incompatible paths or value selections");
            path=merged.get();Integer support=selected.get(id);
            if(support==null && relation.supports().size()==1)support=0;
            if(support==null){frontier.add(id);pending.add("select one of "+relation.supports().size()+" alternative supports for relation "+id);continue;}
            Support proof=relation.supports().get(support);uses.add(new ProofUse(id,support));gaps.addAll(proof.gaps());
            if(proof.evidence()!=Evidence.PROVEN && proof.gaps().isEmpty())pending.add("support evidence remains "+proof.evidence()+" at relation "+id);
            dependencies.put(id,proof.dependencies());queue.addAll(proof.dependencies());
        }
        if(cyclic(dependencies))pending.add("selected support dependencies contain a cycle");
        if(!connected(roots,dependencies))pending.add("requested roots have no selected support dependency connecting them");
        if(!frontier.isEmpty())pending.add("unexpanded or unselected support frontier");
        State state=gaps.isEmpty() && pending.isEmpty()?State.CLOSED:State.PENDING;
        return new Result(state,budget,seen.size(),uses,List.copyOf(frontier),List.copyOf(gaps),List.copyOf(pending),
                "stored derivation closure and shared path/value compatibility only; CLOSED does not establish attacker control or exploitation");
    }
    private static boolean connected(List<Integer> roots,Map<Integer,List<Integer>> graph) {
        if(roots.size()<2)return true;
        Map<Integer,Set<Integer>> adjacent=new HashMap<>();
        graph.forEach((id,next) -> {for(int dependency:next){adjacent.computeIfAbsent(id,k -> new HashSet<>()).add(dependency);adjacent.computeIfAbsent(dependency,k -> new HashSet<>()).add(id);}});
        Set<Integer> seen=new HashSet<>();ArrayDeque<Integer> queue=new ArrayDeque<>(List.of(roots.get(0)));
        while(!queue.isEmpty()){int id=queue.removeFirst();if(seen.add(id))queue.addAll(adjacent.getOrDefault(id,Set.of()));}
        return seen.containsAll(roots);
    }
    private static boolean cyclic(Map<Integer,List<Integer>> graph) {
        Map<Integer,Integer> indegree=new HashMap<>();graph.keySet().forEach(id -> indegree.put(id,0));
        graph.values().forEach(next -> next.forEach(id -> {if(indegree.containsKey(id))indegree.merge(id,1,Integer::sum);}));
        ArrayDeque<Integer> queue=new ArrayDeque<>();indegree.forEach((id,n) -> {if(n==0)queue.add(id);});int removed=0;
        while(!queue.isEmpty()){int id=queue.removeFirst();removed++;for(int next:graph.get(id))if(indegree.containsKey(next) && indegree.merge(next,-1,Integer::sum)==0)queue.add(next);}
        return removed<graph.size();
    }
}
