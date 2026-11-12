package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.Hint;
import java.util.*;

/** Small bytecode shapes guide scheduling only; no object or call facts are emitted. */
final class Structures {
    static Query<List<Hint>> local(Program program,MethodId method) {
        Query<List<Program.SymbolicCall>> query=program.calls(method);List<MethodId> goals=new ArrayList<>();
        for(Program.SymbolicCall call:query.value().orElse(List.of())) {
            MethodId target=call.target(),current=program.method(target.owner(),target.name(),target.descriptor(),target.loader());
            if(Mechanisms.demands(new Call(call.site(),current,call.opcode(),new Sources(Set.of()),List.of())))goals.add(target);
        }
        return new Query<>(Optional.of(goals.isEmpty()?List.of():List.of(new Hint(method,"local-dynamic-boundary","current reached bytecode",List.of("actual receiver, operands and path remain required"),requirements(program,method,new LinkedHashSet<>(goals))))),query.pending());
    }
    static Query<List<Hint>> hints(Program program,Set<MethodId> scope) {
        List<QueryIssue> issues=new ArrayList<>();
        Map<MethodId,Hint> anchors=new LinkedHashMap<>();
        for (ClassInfo type:program.targets()) for (Method method:type.methods()) if (method.hasBody() && scope.contains(method.id())) {
            Query<List<MethodId>> references=program.references(method.id());
            Set<MethodId> calls=new LinkedHashSet<>(references.value().orElse(List.of()));
            issues.addAll(references.pending());
            if(calls.contains(Reflection.INVOKE))anchors.put(method.id(),new Hint(method.id(),"method-invoke-forwarder-candidate",
                    "current bytecode contains Method.invoke",List.of("same receiver and argument identities","concrete lookup signature","path conditions"),requirements(program,method.id(),Set.of(Reflection.INVOKE))));
            List<MethodId> reads=calls.stream().filter(Serialization::read).toList();
            if(!reads.isEmpty())anchors.putIfAbsent(method.id(),new Hint(method.id(),"native-read-boundary",
                    "Java serialization API in current bytecode",List.of("root/member identities","hook state","field values"),requirements(program,method.id(),new LinkedHashSet<>(reads))));
        }
        List<Hint> hints=new ArrayList<>(anchors.values());
        for (Hint anchor:anchors.values()) {
            ArrayDeque<MethodId> pending=new ArrayDeque<>(List.of(anchor.anchor())); Set<MethodId> seen=new HashSet<>();
            while (!pending.isEmpty()) {
                MethodId target=pending.removeFirst();if(seen.contains(target))continue;
                if(seen.size()>=256){issues.add(new QueryIssue(QueryCause.BUDGET,"structure caller discovery budget (256): "+anchor.anchor()));break;}
                seen.add(target);
                Candidates candidates=program.callers(target);issues.addAll(candidates.pending());
                if(candidates.truncated())issues.add(new QueryIssue(QueryCause.BUDGET,"target caller syntax index truncated"));
                for(MethodId caller:candidates.sites().stream().map(Site::method).filter(scope::contains).distinct().toList()) {
                    hints.add(new Hint(caller,"caller-of-"+anchor.mechanism(),"current bytecode references "+target,List.of("dispatch receiver","arguments and path conditions"),requirements(program,caller,Set.of(target))));
                    pending.add(caller);
                }
            }
        }
        return new Query<>(Optional.of(List.copyOf(new LinkedHashSet<>(hints))),List.copyOf(new LinkedHashSet<>(issues)));
    }
    private static List<CallShape.Requirement> requirements(Program program,MethodId method,Set<MethodId> targets) {
        return program.facts(method).actions().stream().filter(Call.class::isInstance).map(Call.class::cast).filter(call -> targets.contains(call.target()))
                .map(call -> new CallShape.Requirement(call.site(),CallShape.of(program,call))).toList();
    }
}
