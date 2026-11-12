package io.just.analysis;

import io.just.knowledge.EntryPoints.Mode;
import io.just.knowledge.EntryPoints.Entry;

import io.just.input.Inputs;
import io.just.input.StaticData;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import java.util.*;

public record ScanResult(Mode mode, Execution execution, Outcome outcome, Inputs.Summary input, Optional<StaticData.Summary> staticData,
                         Analyzer.Limits analysisBudgets, int methodInstructionBudget,
                         List<Entry> entries, List<Hint> hints, List<Relation> relations,
                         List<Finding> findings, List<String> limitations, List<String> missingClasses,
                         Statistics statistics,List<InputRequirement> inputRequirements,List<DemandFrontier> demandFrontier,List<Breakpoint> breakpoints) {
    public ScanResult {
        entries=List.copyOf(entries);hints=List.copyOf(hints);relations=List.copyOf(relations);findings=List.copyOf(findings);
        limitations=List.copyOf(limitations);missingClasses=List.copyOf(missingClasses);
        inputRequirements=List.copyOf(inputRequirements);demandFrontier=List.copyOf(demandFrontier);breakpoints=List.copyOf(breakpoints);
    }
    public enum Execution { FINISHED, TRUNCATED }
    public enum Outcome { FINDINGS, NO_FINDINGS }
    public record Support(Evidence evidence,List<Site> witnesses,List<Gap> gaps,List<Integer> dependencies) {
        public Support {witnesses=List.copyOf(witnesses);gaps=List.copyOf(gaps);dependencies=List.copyOf(dependencies);}
    }
    public record Relation(int id,int context,Kind kind,Site site,Optional<MethodId> target,Atom receiver,List<Atom> arguments,
                           List<Support> supports,Path conditions,String detail,Optional<Slot> slot) {
        public Relation {arguments=List.copyOf(arguments);supports=List.copyOf(supports);if(supports.isEmpty())throw new IllegalArgumentException("relation requires a derivation");}

    }
    public record ProofUse(int relation,int support) {}
    public record Finding(int id, Entry entry, Kind boundary, List<Integer> path,
                          List<Integer> supportingRelations, List<Gap> gaps, Path conditions, String detail,List<ProofUse> proof) {
        public Finding {path=List.copyOf(path);supportingRelations=List.copyOf(supportingRelations);gaps=List.copyOf(gaps);proof=List.copyOf(proof);}
    }
    public record InputRequirement(int id,MethodId entry,int context,Site use,Path conditions,Optional<InputSource> source,
                                   InputNeed needed,List<Integer> dependencies) {public InputRequirement {dependencies=List.copyOf(dependencies);}}
    public enum DemandState { EXTERNAL, UNRESOLVED, CYCLE, BUDGET, MISSING_CALLER, MISSING_DEPENDENCY }
    public record DemandFrontier(int context,Site use,Origin origin,Path conditions,DemandState state,List<Site> candidates,String detail) {public DemandFrontier {candidates=List.copyOf(candidates);}}
    public record Breakpoint(int context,Site use,Path conditions,Optional<Atom> subject,Optional<Slot> slot,List<Integer> knownRelations,
                             GapKind reason,Optional<DemandState> frontier,Optional<Site> cause,String detail) {public Breakpoint {knownRelations=List.copyOf(knownRelations);}}
    public record Statistics(long elapsedMillis, int contexts, long workItems, int heapCells, int relations, int findings,
                             long backwardQueries,boolean demandGuidance,long summaryApplications,long refinementWork,long combinationReuses,long rankingWork,long rankingConnections,long modelReuses,long effectReuses) {}
}
