package io.just.program;

import io.just.program.Program.*;
import java.util.*;
import java.util.concurrent.CancellationException;

/** Batches syntactic graph work. Edges are references, never object bindings or execution proofs. */
public final class GraphQuery {
    private GraphQuery() {}
    public enum Direction { OUTGOING, INCOMING }
    public record Cursor(MethodId method, int depth, int offset) {
        public Cursor { if(depth<0 || offset<0)throw new IllegalArgumentException("negative graph cursor"); }
    }
    public record Edge(MethodId from, MethodId to, Site site, int opcode) {}
    public record Result(Direction direction, List<Cursor> scope, int depth, int methodBudget, int edgeBudget,
                         List<Edge> edges, List<Cursor> frontier, int inspected, List<QueryIssue> pending,List<Limitation> limitations) {
        public Result { scope=List.copyOf(scope);edges=List.copyOf(edges);frontier=List.copyOf(frontier);pending=List.copyOf(pending);limitations=List.copyOf(limitations); }
    }
    public static Result expand(Program program, Direction direction, List<Cursor> scope,
                                int depth, int methods, int edges) {
        if(depth<1 || methods<1 || edges<1)throw new IllegalArgumentException("graph budgets must be positive");
        Map<MethodId,Integer> offsets=new HashMap<>();
        for(Cursor cursor:scope)if(offsets.putIfAbsent(cursor.method(),cursor.offset())!=null)throw new IllegalArgumentException("one graph cursor per method is required");
        // Supplied frontiers may have different depths. Always process the shallowest work first.
        TreeMap<Integer,ArrayDeque<Cursor>> queue=new TreeMap<>();
        java.util.function.Consumer<Cursor> offer=cursor -> queue.computeIfAbsent(cursor.depth(),key -> new ArrayDeque<>()).addLast(cursor);
        scope.forEach(offer);
        Set<MethodId> seen=new HashSet<>();List<Edge> found=new ArrayList<>();
        List<Cursor> frontier=new ArrayList<>();List<Limitation> limitations=new ArrayList<>();Set<QueryIssue> pending=new LinkedHashSet<>();int inspected=0;
        while(!queue.isEmpty()) {
            if(Thread.currentThread().isInterrupted())throw new CancellationException("graph query interrupted");
            ArrayDeque<Cursor> level=queue.firstEntry().getValue();Cursor cursor=level.removeFirst();
            if(level.isEmpty())queue.pollFirstEntry();
            if(seen.contains(cursor.method()))continue;
            if(inspected>=methods || found.size()>=edges || cursor.depth()>=depth) {frontier.add(cursor);continue;}
            seen.add(cursor.method());inspected++;
            List<Edge> adjacent=new ArrayList<>();
            if(direction==Direction.OUTGOING) {
                program.declaration(cursor.method()).value().filter(m -> !m.hasBody()).ifPresent(m -> limitations.add(new Limitation(CoverageCause.UNSUPPORTED,"native or abstract body: "+m.id())));
                Query<List<SymbolicCall>> calls=program.calls(cursor.method());pending.addAll(calls.pending());
                for(SymbolicCall call:calls.value().orElse(List.of()))adjacent.add(new Edge(cursor.method(),call.target(),call.site(),call.opcode()));
            } else {
                Program.Candidates callers=program.callers(cursor.method());pending.addAll(callers.pending());
                if(callers.truncated())pending.add(new QueryIssue(QueryCause.BUDGET,"incoming syntax index is truncated"));
                for(Site site:callers.sites())adjacent.add(new Edge(site.method(),cursor.method(),site,-1));
            }
            if(cursor.offset()>adjacent.size())throw new IllegalArgumentException("graph cursor offset exceeds adjacency");
            for(int i=cursor.offset();i<adjacent.size();i++) {
                if(found.size()>=edges) {frontier.add(new Cursor(cursor.method(),cursor.depth(),i));break;}
                Edge edge=adjacent.get(i);found.add(edge);
                MethodId next=direction==Direction.OUTGOING?edge.to():edge.from();
                if(!seen.contains(next))offer.accept(new Cursor(next,cursor.depth()+1,offsets.getOrDefault(next,0)));
            }
        }
        Map<MethodId,Cursor> remaining=new LinkedHashMap<>();
        for(Cursor cursor:frontier)remaining.merge(cursor.method(),cursor,(a,b) ->
                new Cursor(a.method(),Math.min(a.depth(),b.depth()),Math.min(a.offset(),b.offset())));
        if(!remaining.isEmpty())pending.add(new QueryIssue(QueryCause.BUDGET,"graph expansion frontier; resume supplied cursors with chosen budgets"));
        return new Result(direction,scope,depth,methods,edges,found,List.copyOf(remaining.values()),inspected,List.copyOf(pending),limitations);
    }
}
