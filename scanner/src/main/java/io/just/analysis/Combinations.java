package io.just.analysis;

import io.just.knowledge.Values.*;
import java.util.*;
import java.util.function.BiFunction;

/** One instruction's bounded join view. Removed operands replace the view, including strong writes. */
final class Combinations {
    record Combination(List<Atom> atoms,Path path,List<Gap> gaps,Set<Integer> dependencies) {}
    record Frontier(int operand,Path path) {}
    record Result(List<Combination> values,List<Frontier> frontier,long consumed,long reused) {
        boolean truncated(){return !frontier.isEmpty();}
    }
    private record Pair(Combination prefix,Bound bound) {}
    private record Prefix(List<Atom> atoms,Path path) {}
    private record Binding(Atom atom,Path path) {}
    private record Column(Map<Pair,Combination> pairs,Set<Combination> prefixes,Set<Bound> bounds,boolean complete) {}
    private record Input(List<Value> operands,Combination seed,int limit,Gap budget,Object view) {}
    private Optional<Input> input=Optional.empty();
    private List<Column> columns=List.of();
    private Result result=new Result(List.of(),List.of(),0,0);
    private boolean exhausted;

    Result join(List<Value> values,Combination initial,int limit,Gap budget) {
        return join(values,initial,limit,budget,Long.MAX_VALUE);
    }
    Result join(List<Value> values,Combination initial,int limit,Gap budget,long allowance) {
        return join(values,initial,limit,budget,allowance,(prefix,bounds) -> bounds,0);
    }
    Result join(List<Value> values,Combination initial,int limit,Gap budget,long allowance,BiFunction<Combination,List<Bound>,List<Bound>> order,Object view) {
        Input request=new Input(List.copyOf(values),initial,limit,budget,view);
        if(input.filter(previous -> !previous.view().equals(view)).isPresent())columns=List.of();
        if(!exhausted && input.filter(request::equals).isPresent())return new Result(result.values(),result.frontier(),0,result.values().size());
        long consumed=0,reused=0;exhausted=false;
        List<Combination> joined=List.of(initial);List<Column> next=new ArrayList<>();List<Frontier> frontier=new ArrayList<>();
        for(int index=0;index<values.size();index++) {
            Column old=index<columns.size()?columns.get(index):new Column(Map.of(),Set.of(),Set.of(),true);
            Set<Combination> prefixes=new LinkedHashSet<>(joined);Set<Bound> bounds=values.get(index).alternatives();
            Set<Prefix> previousPrefixes=new HashSet<>();old.prefixes().forEach(p -> previousPrefixes.add(new Prefix(p.atoms(),p.path())));
            Set<Binding> previousBounds=new HashSet<>();old.bounds().forEach(b -> previousBounds.add(new Binding(b.atom(),b.path())));
            Set<Combination> freshPrefixes=new LinkedHashSet<>();prefixes.stream().filter(p -> !previousPrefixes.contains(new Prefix(p.atoms(),p.path()))).forEach(freshPrefixes::add);
            Set<Bound> freshBounds=new LinkedHashSet<>();bounds.stream().filter(b -> !previousBounds.contains(new Binding(b.atom(),b.path()))).forEach(freshBounds::add);
            Join column=new Join(old,limit,allowance-consumed);
            Map<Combination,List<Bound>> ordered=new HashMap<>();
            java.util.function.Function<Combination,List<Bound>> choices=prefix -> ordered.computeIfAbsent(prefix,p -> order.apply(p,List.copyOf(bounds)));
            // New objects and paths get a turn before evidence refreshes refill a bounded view.
            Map<Combination,Iterator<Bound>> fresh=new LinkedHashMap<>();for(Combination prefix:freshPrefixes)fresh.put(prefix,choices.apply(prefix).iterator());
            while(!fresh.isEmpty() && !column.stopped) {
                Iterator<Map.Entry<Combination,Iterator<Bound>>> pending=fresh.entrySet().iterator();
                while(pending.hasNext() && !column.stopped) {
                    var entry=pending.next();if(entry.getValue().hasNext())column.add(new Pair(entry.getKey(),entry.getValue().next()));else pending.remove();
                }
            }
            if(!column.stopped)for(Combination prefix:prefixes)if(!freshPrefixes.contains(prefix)) {
                for(Bound bound:choices.apply(prefix))if(freshBounds.contains(bound) && !column.add(new Pair(prefix,bound)))break;
                if(column.stopped)break;
            }
            // Support-only changes still reach consumers; unchanged cross products are not visited.
            if(!column.stopped)for(Combination prefix:prefixes)if(!freshPrefixes.contains(prefix) && !old.prefixes().contains(prefix)) {
                for(Bound bound:choices.apply(prefix))if(!freshBounds.contains(bound) && !column.add(new Pair(prefix,bound)))break;
                if(column.stopped)break;
            }
            if(!column.stopped)for(Combination prefix:prefixes)if(old.prefixes().contains(prefix)) {
                for(Bound bound:choices.apply(prefix))if(!freshBounds.contains(bound) && !old.bounds().contains(bound) && !column.add(new Pair(prefix,bound)))break;
                if(column.stopped)break;
            }
            if(!column.stopped)for(Pair pair:old.pairs().keySet())
                if(prefixes.contains(pair.prefix()) && bounds.contains(pair.bound()) && !column.add(pair))break;
            // An incomplete prefix is a frontier, never a complete summary. More room resumes omitted pairs.
            if(!column.stopped && !old.complete())outer:for(Combination prefix:prefixes)if(old.prefixes().contains(prefix))
                for(Bound bound:choices.apply(prefix))if(old.bounds().contains(bound) && !old.pairs().containsKey(new Pair(prefix,bound)))
                    if(!column.add(new Pair(prefix,bound)))break outer;
            consumed+=column.consumed;reused+=column.reused;exhausted|=column.exhausted;
            if(column.stopped)frontier.add(new Frontier(index,column.frontier));
            next.add(new Column(Collections.unmodifiableMap(column.pairs),Set.copyOf(prefixes),Set.copyOf(bounds),!column.stopped));
            joined=List.copyOf(column.values);
        }
        input=Optional.of(request);columns=List.copyOf(next);
        result=new Result(joined,List.copyOf(frontier),consumed,reused);return result;
    }
    private static final class Join {
        final Column old;final int limit;final long allowance;
        final Map<Pair,Combination> pairs=new LinkedHashMap<>();final Set<Combination> values=new LinkedHashSet<>();
        long consumed,reused;boolean stopped,exhausted;Path frontier=Path.EMPTY;
        Join(Column old,int limit,long allowance){this.old=old;this.limit=limit;this.allowance=allowance;}
        boolean add(Pair pair) {
            if(pairs.containsKey(pair))return true;
            Combination value=old.pairs().get(pair);
            if(value==null) {
                if(consumed>=allowance){stopped=true;exhausted=true;frontier=pair.prefix().path();return false;}
                consumed++;
                Optional<Path> path=pair.prefix().path().and(pair.bound().path());if(path.isEmpty())return true;
                List<Atom> atoms=new ArrayList<>(pair.prefix().atoms());atoms.add(pair.bound().atom());
                Set<Gap> gaps=new LinkedHashSet<>(pair.prefix().gaps());gaps.addAll(pair.bound().gaps());
                Set<Integer> dependencies=new LinkedHashSet<>(pair.prefix().dependencies());dependencies.addAll(pair.bound().dependencies());
                value=new Combination(List.copyOf(atoms),path.get(),List.copyOf(gaps),Set.copyOf(dependencies));
            } else reused++;
            if(!values.contains(value) && values.size()>=limit){stopped=true;frontier=value.path();return false;}
            pairs.put(pair,value);values.add(value);return true;
        }
    }
}
