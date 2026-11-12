package io.just.program;

import io.just.program.Program.*;
import java.util.*;
import java.util.concurrent.CancellationException;

/** Method-local source questions. No heap, dispatch or scanner state is created. */
public final class SourceTrace {
    private SourceTrace() {}

    public record Plan(Set<Integer> producers, Set<Parameter> parameters, List<Call> returns,
                       List<ReadField> fields, List<ReadArray> elements, List<Origin> unresolved,
                       List<Origin> frontier, int visited, boolean cyclic) {
        public Plan {
            producers = Collections.unmodifiableSet(new LinkedHashSet<>(producers));
            parameters = Collections.unmodifiableSet(new LinkedHashSet<>(parameters));
            returns = List.copyOf(returns);
            fields = List.copyOf(fields);
            elements = List.copyOf(elements);
            unresolved = List.copyOf(unresolved);
            frontier = List.copyOf(frontier);
        }

        public boolean truncated() { return !frontier.isEmpty(); }
    }

    public record Trace(MethodId method, Origin origin, int budget, Plan plan,
                        List<Limitation> limitations) {
        public Trace { limitations = List.copyOf(limitations); }
    }

    public static Query<Trace> query(Program program, MethodId method, Origin origin, int budget) {
        if (budget < 1) throw new IllegalArgumentException("source query budget must be positive");
        Query<Method> declaration = program.declaration(method);
        if (declaration.value().isEmpty())
            return new Query<>(Optional.empty(), declaration.pending());

        Method selected = declaration.value().orElseThrow();
        if (origin instanceof Parameter parameter) {
            int slot = selected.isStatic() ? 0 : 1;
            Set<Integer> slots = new HashSet<>();
            if (!selected.isStatic()) slots.add(0);
            for (ValueType type : program.signature(selected.id()).parameters()) {
                slots.add(slot);
                slot += type.slots();
            }
            if (!slots.contains(parameter.slot()))
                throw new IllegalArgumentException("parameter slot " + parameter.slot() + " is not declared by " + method);
            Plan plan = trace(Map.of(), Map.of(), origin, budget);
            return new Query<>(Optional.of(new Trace(selected.id(), origin, budget, plan, List.of())), declaration.pending());
        }
        Facts facts = program.facts(selected.id());
        Plan plan = trace(program.flow(facts.method().id()).producers(), facts.guards(), origin, budget);
        List<QueryIssue> pending = new ArrayList<>(declaration.pending());
        for (Limitation limitation : facts.limitations())
            if (limitation.cause() == CoverageCause.BUDGET)
                pending.add(new QueryIssue(QueryCause.BUDGET, limitation.detail() + ": " + method));
        if (plan.truncated())
            pending.add(new QueryIssue(QueryCause.BUDGET, "source frontier (" + budget + " origins): " + method));
        return new Query<>(Optional.of(new Trace(facts.method().id(), origin, budget, plan, facts.limitations())),
                List.copyOf(new LinkedHashSet<>(pending)));
    }

    static Plan trace(Map<Integer, Action> actions, Map<Integer, List<Guard>> guards,
                      Origin origin, int budget) {
        if (budget < 1) throw new IllegalArgumentException("source query budget must be positive");
        Set<Origin> seen = new LinkedHashSet<>();
        Set<Integer> producers = new LinkedHashSet<>();
        Set<Parameter> parameters = new LinkedHashSet<>();
        List<Call> returns = new ArrayList<>();
        List<ReadField> fields = new ArrayList<>();
        List<ReadArray> elements = new ArrayList<>();
        List<Origin> unresolved = new ArrayList<>();
        ArrayDeque<Origin> queue = new ArrayDeque<>(List.of(origin));
        Map<Origin, List<Origin>> edges = new LinkedHashMap<>();
        while (!queue.isEmpty() && seen.size() < budget) {
            if (Thread.currentThread().isInterrupted())
                throw new CancellationException("source query interrupted");
            Origin at = queue.removeFirst();
            if (!seen.add(at)) continue;
            if (at instanceof Parameter parameter) {
                parameters.add(parameter);
                continue;
            }
            if (!(at instanceof Producer source)) {
                unresolved.add(at);
                continue;
            }
            producers.add(source.instruction());
            Action action = actions.get(source.instruction());
            if (action == null) {
                unresolved.add(at);
                continue;
            }
            List<Origin> upstream = new ArrayList<>();
            for (Guard guard : guards.getOrDefault(source.instruction(), List.of()))
                upstream.add(new Producer(guard.branch()));
            if (action instanceof Call call) returns.add(call);
            else if (action instanceof ReadField field) fields.add(field);
            else if (action instanceof ReadArray array) elements.add(array);
            else for (Sources inputs : Program.sources(action)) upstream.addAll(inputs.origins());
            edges.put(at, List.copyOf(upstream));
            queue.addAll(upstream);
        }
        List<Origin> frontier = queue.stream().filter(at -> !seen.contains(at)).distinct().toList();
        return new Plan(producers, parameters, returns, fields, elements, unresolved,
                frontier, seen.size(), cyclic(origin, edges));
    }

    private record Frame(Origin origin, Iterator<Origin> edges) {}

    private static boolean cyclic(Origin origin, Map<Origin, List<Origin>> edges) {
        Set<Origin> done = new HashSet<>(), active = new HashSet<>();
        ArrayDeque<Frame> stack = new ArrayDeque<>();
        active.add(origin);
        stack.push(new Frame(origin, edges.getOrDefault(origin, List.of()).iterator()));
        while (!stack.isEmpty()) {
            if (Thread.currentThread().isInterrupted())
                throw new CancellationException("source query interrupted");
            Frame frame = stack.peek();
            if (!frame.edges().hasNext()) {
                active.remove(frame.origin());
                done.add(frame.origin());
                stack.pop();
                continue;
            }
            Origin next = frame.edges().next();
            if (active.contains(next)) return true;
            if (done.contains(next)) continue;
            active.add(next);
            stack.push(new Frame(next, edges.getOrDefault(next, List.of()).iterator()));
        }
        return false;
    }
}
