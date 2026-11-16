package io.just.program;

import io.just.program.Program.*;
import java.util.*;
import java.util.concurrent.CancellationException;
import java.util.function.Predicate;
import org.objectweb.asm.Opcodes;

/** Dispatch metadata within an explicit receiver scope; never a concrete object binding. */
public final class Dispatch {
    public record Budget(int receivers, int targets) {
        public Budget {
            if (receivers < 1 || targets < 1)
                throw new IllegalArgumentException("dispatch query budgets must be positive");
        }
    }

    public record Result(MethodId requested, String upper, int loader, List<DefinedType> scope, Budget budget,
                         List<VirtualTarget> targets, List<DefinedType> frontier, int inspected) {
        public Result {
            scope = List.copyOf(scope);
            targets = List.copyOf(targets);
            frontier = List.copyOf(frontier);
        }
    }

    private final Program program;
    private record Member(MethodId requested, String upper, int loader) {}

    public Dispatch(Program program) { this.program = program; }

    /** Only supplied receiver candidates are inspected. Native targets retain their metadata. */
    public Query<Result> within(MethodId requested, String upper, int loader,
                                List<DefinedType> receivers, Budget budget) {
        return within(requested,upper,loader,receivers,List.of(),budget);
    }

    /** Preferences order this scope without adding receivers to it. */
    public Query<Result> within(MethodId requested, String upper, int loader,
                                List<DefinedType> receivers,List<DefinedType> preferred,Budget budget) {
        List<DefinedType> scope = List.copyOf(new LinkedHashSet<>(receivers));
        Set<DefinedType> allowed=new HashSet<>(scope);
        List<DefinedType> ranked=preferred.stream().filter(allowed::contains).distinct().toList();
        return resolve(new Member(requested, upper, loader), scope, ranked, budget, Query.found(List.of()),
                method -> (method.access() & Opcodes.ACC_ABSTRACT) == 0);
    }

    /** Scanner discovery retains candidate order and limits body-backed targets per query. */
    Query<List<VirtualTarget>> discover(MethodId requested, String upper, int loader,
                                        List<DefinedType> preferred,int targetLimit) {
        List<VirtualTarget> targets = new ArrayList<>();
        List<QueryIssue> issues = new ArrayList<>();
        Member member = new Member(requested, upper, loader);
        Query<Method> base = program.lookup(program.method(upper, requested.name(), requested.descriptor(), loader));
        Optional<DefinedType> runtime = program.type(upper, loader)
                .filter(type -> (type.access() & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_INTERFACE)) == 0)
                .map(type -> new DefinedType(type.name(), type.loader()));
        Query<Boolean> owner = runtime.map(receiver -> compatible(receiver, member))
                .orElseGet(() -> Query.found(true));
        if (!owner.value().equals(Optional.of(false)) || !owner.pending().isEmpty()) {
            base.value().filter(Method::hasBody).ifPresent(method -> {
                List<QueryIssue> required = new ArrayList<>(base.pending());
                required.addAll(owner.pending());
                targets.add(new VirtualTarget(method, runtime, required));
            });
        }
        if (base.value().isEmpty()) issues.addAll(base.pending());
        Query<Result> query = resolve(member, program.dispatchCandidates(upper, loader), preferred,
                new Budget(Integer.MAX_VALUE, targetLimit), new Query<>(Optional.of(targets), issues), Method::hasBody);
        return new Query<>(query.value().map(Result::targets), query.pending());
    }

    private Query<Result> resolve(Member member, List<DefinedType> ordinary, List<DefinedType> preferred,
                                   Budget budget, Query<List<VirtualTarget>> prefix, Predicate<Method> eligible) {
        List<VirtualTarget> targets = new ArrayList<>(prefix.value().orElse(List.of()));
        Set<DefinedType> seen = new LinkedHashSet<>();
        targets.forEach(target -> target.receiver().ifPresent(seen::add));
        List<QueryIssue> issues = new ArrayList<>(prefix.pending());
        Set<DefinedType> scope = new LinkedHashSet<>(ordinary);
        scope.addAll(preferred);
        ArrayDeque<DefinedType> plain = new ArrayDeque<>(ordinary);
        ArrayDeque<DefinedType> ranked = new ArrayDeque<>(preferred);
        int turn = 0, inspected = 0;
        while ((!plain.isEmpty() || !ranked.isEmpty())
                && targets.size() < budget.targets() && inspected < budget.receivers()) {
            if (Thread.currentThread().isInterrupted())
                throw new CancellationException("dispatch query interrupted");
            DefinedType receiver = !ranked.isEmpty() && (turn++ % 4 != 3 || plain.isEmpty())
                    ? ranked.removeFirst() : plain.removeFirst();
            if (!seen.add(receiver)) continue;
            inspected++;
            Query<Boolean> match = compatible(receiver, member);
            if (match.value().equals(Optional.of(false)) && match.pending().isEmpty()) continue;
            Query<Method> actual = program.lookup(new MethodId(receiver.name(), member.requested().name(),
                    member.requested().descriptor(), receiver.loader()));
            List<QueryIssue> required = new ArrayList<>(match.pending());
            required.addAll(actual.pending());
            actual.value().filter(eligible).ifPresent(method ->
                    targets.add(new VirtualTarget(method, Optional.of(receiver), required)));
            if (actual.value().isEmpty()) issues.addAll(required);
        }
        List<DefinedType> frontier = scope.stream().filter(receiver -> !seen.contains(receiver)).toList();
        if (!frontier.isEmpty()) {
            String detail = targets.size() >= budget.targets()
                    ? "virtual target frontier (" + budget.targets() + "): " + member.requested()
                    : "receiver inspection frontier (" + budget.receivers() + "): " + member.requested();
            issues.add(new QueryIssue(QueryCause.BUDGET, detail));
        }
        Result result = new Result(member.requested(), member.upper(), member.loader(), List.copyOf(scope),
                budget, targets, frontier, inspected);
        return new Query<>(Optional.of(result), List.copyOf(new LinkedHashSet<>(issues)));
    }

    private Query<Boolean> compatible(DefinedType receiver, Member member) {
        Query<Boolean> bound = program.assignable(receiver.name(), receiver.loader(), member.upper(), member.loader());
        if (bound.value().equals(Optional.of(false)) && bound.pending().isEmpty()) return bound;
        if (member.requested().owner().equals(member.upper()) && member.requested().loader() == member.loader()) return bound;
        Query<Boolean> owner = program.assignable(receiver.name(), receiver.loader(),
                member.requested().owner(), member.requested().loader());
        if (owner.value().equals(Optional.of(false)) && owner.pending().isEmpty()) return owner;
        Set<QueryIssue> pending = new LinkedHashSet<>(bound.pending());
        pending.addAll(owner.pending());
        Optional<Boolean> value = bound.value().equals(Optional.of(true)) && owner.value().equals(Optional.of(true))
                ? Optional.of(true) : Optional.empty();
        return new Query<>(value, List.copyOf(pending));
    }
}
