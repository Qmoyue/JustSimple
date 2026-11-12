package io.just.analysis;

import io.just.analysis.ScanResult.*;
import io.just.knowledge.Values.*;
import io.just.program.Program.Site;
import java.util.*;

/** Projects existing evidence and frontiers; it performs no searches and changes no conclusions. */
final class Breakpoints {
    private record Use(int context,Site site) {}
    private record Cause(Relation relation,Support support) {}
    static List<Breakpoint> locate(List<Relation> relations,List<InputRequirement> needs,List<DemandFrontier> frontiers) {
        Set<Breakpoint> result=new LinkedHashSet<>();Map<Use,List<Integer>> known=new HashMap<>();
        Map<Gap,Cause> causes=new LinkedHashMap<>();
        for(Relation relation:relations) {
            known.computeIfAbsent(new Use(relation.context(),relation.site()),k -> new ArrayList<>()).add(relation.id());
            for(Support support:relation.supports())for(Gap gap:support.gaps()) {
                Cause previous=causes.get(gap);
                boolean exact=relation.site().equals(gap.site());
                if(previous==null || exact && !previous.relation().site().equals(gap.site())
                        || previous.relation().id()==relation.id() && support.dependencies().toString().compareTo(previous.support().dependencies().toString())<0)
                    causes.put(gap,new Cause(relation,support));
            }
        }
        // Locate a cause where it arose, rather than repeating it at every downstream consumer.
        // Labels/implicit checks may have no relation at that exact site: retain their first real use.
        causes.forEach((gap,cause) -> result.add(at(cause,gap)));
        for(InputRequirement need:needs) {
            Optional<Slot> slot=need.needed().slot().or(() -> need.source().filter(source -> !source.path().isEmpty()).map(source -> source.path().get(source.path().size()-1)));
            result.add(new Breakpoint(need.context(),need.use(),need.conditions(),Optional.of(need.needed().subject()),slot,need.dependencies(),GapKind.INPUT_BINDING,Optional.empty(),Optional.empty(),need.needed().reason()));
        }
        for(DemandFrontier frontier:frontiers) {
            GapKind reason=switch(frontier.state()) {
                case BUDGET -> GapKind.BUDGET;case MISSING_DEPENDENCY -> GapKind.MISSING_DEPENDENCY;
                case EXTERNAL,MISSING_CALLER -> GapKind.INPUT_BINDING;case CYCLE -> GapKind.CONTROL_CONDITION;case UNRESOLVED -> GapKind.UNSUPPORTED;
            };
            result.add(new Breakpoint(frontier.context(),frontier.use(),frontier.conditions(),Optional.empty(),Optional.empty(),List.copyOf(known.getOrDefault(new Use(frontier.context(),frontier.use()),List.of())),reason,Optional.of(frontier.state()),Optional.empty(),frontier.detail()));
        }
        return List.copyOf(result);
    }
    private static Breakpoint at(Cause cause,Gap gap) {
        Relation relation=cause.relation();
        List<Integer> support=new ArrayList<>(cause.support().dependencies());support.add(relation.id());
        return new Breakpoint(relation.context(),relation.site(),relation.conditions(),Optional.of(relation.receiver()),relation.slot(),List.copyOf(support),gap.kind(),Optional.empty(),Optional.of(gap.site()),gap.detail());
    }
}
