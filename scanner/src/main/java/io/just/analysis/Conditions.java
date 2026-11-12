package io.just.analysis;

import io.just.knowledge.Values.*;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.Mechanisms.Invocation;
import io.just.program.Program;
import io.just.program.Program.*;
import java.util.*;

/** One owner of unresolved choices; propagation, heap visibility and conclusions query the same facts. */
final class Conditions {
    sealed interface Decision permits Pending,Unknown,Taken {}
    record Pending() implements Decision {}
    record Unknown() implements Decision {}
    record Taken(int target) implements Decision {}
    record Paths(Set<Integer> possible,Set<Integer> ready,boolean unknown) {}
    private final Program program;
    private final Mechanisms mechanisms;
    private sealed interface Condition permits Unresolved,Operation,Exclusions {}
    private record Unresolved(Gap gap) implements Condition {}
    private record Exclusions(List<Path> paths,Gap gap) implements Condition {}
    private record Read(ObjectValue object,Slot slot) {}
    private record Operation(Invocation invocation,List<Gap> gaps,Map<Read,Value> reads) implements Condition {}
    private record CompletionKey(Invocation invocation,Map<Read,Value> reads,int definitions) {}
    private final Map<ChoiceKey,Condition> unresolved=new HashMap<>();
    private final Map<CompletionKey,Optional<Boolean>> normalChecks=new LinkedHashMap<>();
    private final Map<Selection,Boolean> typeChecks=new LinkedHashMap<>();
    private int definitions;
    Conditions(Program program,Mechanisms mechanisms) {this.program=program;this.mechanisms=mechanisms;}
    void uncertain(ChoiceKey choice,Gap gap) {unresolved.put(choice,new Unresolved(gap));}
    void excluding(ChoiceKey choice,List<Path> paths,Gap gap) {
        unresolved.put(choice,new Exclusions(List.copyOf(paths),new Gap(gap.kind(),gap.site(),gap.detail(),Optional.of(choice))));
    }
    void normal(NormalChoice choice,Invocation invocation,List<Gap> gaps,Mechanisms.Bindings bindings) {
        Map<Read,Value> reads=new LinkedHashMap<>();
        mechanisms.normalCompletion(invocation,(object,slot) -> reads.computeIfAbsent(new Read(object,slot),key -> bindings.read(object,slot)));
        unresolved.put(choice,new Operation(invocation,gaps.stream().map(g -> new Gap(g.kind(),g.site(),g.detail(),Optional.of(choice))).toList(),Map.copyOf(reads)));
    }
    boolean satisfied(Gap gap,Path path) {
        return gap.condition().map(unresolved::get).map(condition ->
                condition instanceof Operation operation && completion(operation,path).equals(Optional.of(true))
                || condition instanceof Exclusions excluded && excluded.paths().stream().noneMatch(previous -> previous.compatible(path))).orElse(false);
    }
    boolean uncertain(ChoiceKey choice) {return unresolved.containsKey(choice);}
    boolean compatible(Path path){
        return compatible(path,List.of());
    }
    boolean compatible(Path path,Collection<Gap> gaps){
        if(definitions!=program.definitionCount()){definitions=program.definitionCount();typeChecks.clear();}
        Set<ChoiceKey> choices=new LinkedHashSet<>(path.choices().keySet());
        for(Gap gap:gaps)gap.condition().ifPresent(choices::add);
        for(ChoiceKey choice:choices) {
            Condition condition=unresolved.get(choice);
            if(condition instanceof Operation operation && completion(operation,path).equals(Optional.of(false)))return false;
            if(condition instanceof Exclusions excluded && excluded.paths().stream().anyMatch(previous -> implied(previous,path)))return false;
        }
        for(Selection selection:path.selections().values()) {
            Boolean known=typeChecks.get(selection);
            if(known==null) {
                known=CandidateBindings.compatible(selection,program);
                if(typeChecks.size()>=2048)typeChecks.remove(typeChecks.keySet().iterator().next());
                typeChecks.put(selection,known);
            }
            if(!known)return false;
        }
        return true;
    }
    List<Gap> gaps(Path path) {
        List<Gap> result=new ArrayList<>();
        for (ChoiceKey choice:path.choices().keySet())result.addAll(gaps(choice,path));
        return List.copyOf(result);
    }
    private List<Gap> gaps(ChoiceKey choice,Path path) {
        Condition condition=unresolved.get(choice);
        if(condition instanceof Unresolved value)return List.of(value.gap());
        if(condition instanceof Exclusions excluded && excluded.paths().stream().anyMatch(previous -> previous.compatible(path)))return List.of(excluded.gap());
        if(condition instanceof Operation operation && !completion(operation,path).equals(Optional.of(true)))return operation.gaps();
        return List.of();
    }
    private Optional<Boolean> completion(Operation operation,Path path) {
        Invocation bound=CandidateBindings.project(operation.invocation(),path);
        CompletionKey key=new CompletionKey(bound,operation.reads(),program.definitionCount());
        Optional<Boolean> known=normalChecks.get(key);if(known!=null)return known;
        boolean[] missing={false};
        Optional<Boolean> result=mechanisms.normalCompletion(bound,(object,slot) -> {
            Value value=operation.reads().get(new Read(object,slot));
            if(value==null){missing[0]=true;return Value.BOTTOM;}return value.under(path);
        });
        if(missing[0])result=Optional.empty();
        if(normalChecks.size()>=1024)normalChecks.remove(normalChecks.keySet().iterator().next());
        normalChecks.put(key,result);return result;
    }
    boolean implied(Path requirement,Path actual) {
        if(requirement==actual || requirement.equals(Path.EMPTY))return true;
        for(var choice:requirement.choices().entrySet()) {
            Integer selected=actual.choices().get(choice.getKey());
            // A settled choice can be omitted, but an explicit different successor is a contradiction.
            if(selected!=null ? !selected.equals(choice.getValue()) : !gaps(choice.getKey(),actual).isEmpty())return false;
        }
        for(var required:requirement.selections().entrySet()) {
            Selection selected=actual.selections().get(required.getKey());
            if(selected==null || !required.getValue().impliedBy(selected))return false;
        }
        return true;
    }
    Paths paths(Facts facts,Map<Integer,Decision> branches) {
        Set<Integer> possible=reachable(facts,branches,false,-1),ready=reachable(facts,branches,true,-1);
        boolean unknown=branches.entrySet().stream().anyMatch(e -> ready.contains(e.getKey()) && e.getValue() instanceof Unknown);
        return new Paths(possible,ready,unknown);
    }
    Set<Integer> reachable(Facts facts,Map<Integer,Decision> branches,boolean ready,int blocked) {
        return reachable(facts,branches,ready,blocked,0);
    }
    Set<Integer> reachable(Facts facts,Map<Integer,Decision> branches,boolean ready,int blocked,int start) {
        Set<Integer> reached=new HashSet<>();ArrayDeque<Integer> pending=new ArrayDeque<>(List.of(start));
        // Handler admission is checked separately against actual thrown values by the caller.
        if(start==0)for(Handler handler:facts.handlers())pending.addLast(handler.target());
        while(!pending.isEmpty()) {
            int at=pending.removeFirst();if(at==blocked || !reached.add(at))continue;
            Decision branch=branches.get(at);
            if(ready && branch instanceof Pending)continue;
            for(Edge edge:program.outgoing(facts.method().id()).getOrDefault(at,List.of()))
                if(!edge.exceptional() && (!(branch instanceof Taken taken) || taken.target()==edge.to()))pending.addLast(edge.to());
        }
        return Set.copyOf(reached);
    }
}
