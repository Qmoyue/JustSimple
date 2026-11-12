package io.just.analysis;

import io.just.knowledge.Values.*;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class CombinationsTest {
    private final Site site=new Site(new MethodId("Fixture","call","()V"),4,1,"source fixture");
    private final Gap budget=new Gap(GapKind.BUDGET,site,"combination budget");
    private final Combinations.Combination seed=new Combinations.Combination(List.of(),Path.EMPTY,List.of(),Set.of());
    @Test void growthOnEitherSideAndEvidenceOnlyChangesReachTheJoinedTuple() {
        Combinations join=new Combinations();Value left=Value.of(new Literal("a")),right=Value.of(new Literal(1));
        assertEquals(1,join.join(List.of(left,right),seed,64,budget).values().size());
        left=left.merge(Value.of(new Literal("b")));assertEquals(2,join.join(List.of(left,right),seed,64,budget).values().size());
        right=right.merge(Value.of(new Literal(2)));assertEquals(4,join.join(List.of(left,right),seed,64,budget).values().size());
        right=right.tracing(Set.of(31));var result=join.join(List.of(left,right),seed,64,budget);
        assertTrue(result.values().stream().allMatch(c -> c.dependencies().contains(31)));
        var replaced=join.join(List.of(Value.of(new Literal("replacement")),Value.of(new Literal(9))),seed,64,budget);
        assertEquals(List.of(new Literal("replacement"),new Literal(9)),replaced.values().get(0).atoms());assertEquals(1,replaced.values().size());
    }
    @Test void aLateValueDoesNotReplayUnchangedIncompatiblePairs() {
        BranchKey key=new BranchKey(0,1);Path yes=Path.EMPTY.with(key,1).orElseThrow(),no=Path.EMPTY.with(key,2).orElseThrow();
        Value left=Value.of(new Literal("a"),yes).merge(Value.of(new Literal("b"),no));
        Value right=Value.of(new Literal(1),yes).merge(Value.of(new Literal(2),no));
        Combinations join=new Combinations();join.join(List.of(left,right),seed,64,budget);
        var grown=join.join(List.of(left,right.merge(Value.of(new Literal(3),yes))),seed,64,budget);
        assertEquals(3,grown.values().size());
        assertEquals(2,grown.consumed(),"only the late operand meets both existing prefixes; unchanged conflicts consume no work");
        assertTrue(grown.values().stream().anyMatch(c -> c.atoms().equals(List.of(new Literal("a"),new Literal(3)))));
    }
    @Test void newObjectsKeepTheirTurnWhenOldBindingsGainEvidenceInTheSameUpdate() {
        Combinations join=new Combinations();Value receivers=Value.of(new Literal("left")).merge(Value.of(new Literal("right")));
        Value arguments=Value.of(new Literal("old-a")).merge(Value.of(new Literal("old-b")));
        join.join(List.of(receivers,arguments),seed,2,budget);
        ObjectValue returned=new ObjectValue(92,"java/lang/Runtime",true,"new factory return");
        var update=join.join(List.of(receivers,arguments.tracing(Set.of(63)).merge(Value.of(returned).tracing(Set.of(71)))),seed,2,budget);
        assertTrue(update.truncated());
        assertTrue(update.values().stream().anyMatch(tuple -> tuple.atoms().contains(returned) && tuple.dependencies().contains(71)),"evidence-only changes must not crowd the newly produced object out of every binding");
    }
    @Test void incompatibleBranchesNeverCrossAndBudgetRemainsExplicit() {
        BranchKey key=new BranchKey(0,1);Path yes=Path.EMPTY.with(key,1).orElseThrow(),no=Path.EMPTY.with(key,2).orElseThrow();
        Value left=Value.of(new Literal("a"),yes).merge(Value.of(new Literal("b"),no));
        Value right=Value.of(new Literal(1),yes).merge(Value.of(new Literal(2),no));
        Combinations join=new Combinations();var result=join.join(List.of(left,right),seed,64,budget);
        assertEquals(2,result.values().size());
        assertTrue(result.values().stream().allMatch(c -> c.atoms().equals(List.of(new Literal("a"),new Literal(1))) || c.atoms().equals(List.of(new Literal("b"),new Literal(2)))));
        var limited=join.join(List.of(left,right),seed,1,budget);assertTrue(limited.truncated());
        assertTrue(limited.values().stream().allMatch(c -> c.gaps().isEmpty()),"omitted alternatives do not weaken an evaluated tuple");
        assertFalse(limited.frontier().isEmpty(),"the omitted branch remains a located frontier");
        assertEquals(2,join.join(List.of(left,right),seed,64,budget).values().size(),"growth after truncation must be reconsidered");
    }
    @Test void metadataVariantsDoNotCrowdALaterObjectReturnOutOfEveryConsumer() {
        Value value=Value.BOTTOM;
        for(int i=0;i<80;i++)value=value.merge(Value.of(new io.just.knowledge.Values.ClassValue("LType"+i+";",true)));
        ObjectValue returned=new ObjectValue(90,"java/lang/Runtime",true,"actual factory return");
        Value retained=value.merge(Value.of(returned).tracing(Set.of(42))).limited(8,budget);
        var joined=new Combinations().join(List.of(retained),seed,8,budget);
        assertTrue(joined.values().stream().anyMatch(tuple -> tuple.atoms().equals(List.of(returned)) && tuple.dependencies().contains(42)),"object production remains usable beside a larger metadata family");
        assertTrue(retained.alternatives().stream().anyMatch(bound -> bound.atom() instanceof Truncated));
        assertTrue(retained.alternatives().stream().filter(bound -> !(bound.atom() instanceof Truncated)).allMatch(bound -> bound.gaps().isEmpty()));
    }
    @Test void aNewReturnGetsABindingBeforeThePreviouslySelectedTuplesRefillTheBudget() {
        Combinations join=new Combinations();
        Value receivers=Value.of(new Literal("left")).merge(Value.of(new Literal("right")));
        Value arguments=Value.of(new Literal("old-a")).merge(Value.of(new Literal("old-b")));
        assertTrue(join.join(List.of(receivers,arguments),seed,2,budget).truncated());
        ObjectValue returned=new ObjectValue(91,"java/lang/Runtime",true,"actual factory return");
        var grown=join.join(List.of(receivers,arguments.merge(Value.of(returned).tracing(Set.of(71)))),seed,2,budget);
        assertTrue(grown.truncated());
        assertTrue(grown.values().stream().anyMatch(tuple -> tuple.atoms().contains(returned) && tuple.dependencies().contains(71)));
        assertTrue(grown.values().stream().allMatch(tuple -> tuple.gaps().isEmpty()));
        assertTrue(join.join(List.of(receivers,arguments),seed,2,budget).values().stream().noneMatch(tuple -> tuple.atoms().contains(returned)),"a replaced operand must not reuse a stale return");
        BranchKey choice=new BranchKey(0,12);
        Path first=Path.EMPTY.with(choice,1).orElseThrow(),later=Path.EMPTY.with(choice,2).orElseThrow();
        Combinations paths=new Combinations();
        Value singleton=Value.of(returned,first).tracing(Set.of(72)).merge(Value.of(new Literal("earlier alternative")));
        paths.join(List.of(receivers,singleton),seed,2,budget);
        var newlyBound=paths.join(List.of(receivers,singleton.merge(Value.of(returned,later).tracing(Set.of(73)))),seed,2,budget);
        assertTrue(newlyBound.values().stream().anyMatch(tuple -> tuple.path().equals(later) && tuple.dependencies().contains(73)),"the same singleton returned through a new path must get a consumer binding");
    }
    @Test void equivalentPrefixesShareTheirTupleAndTheWorkAllowanceIsEnforced() {
        BranchKey choice=new BranchKey(0,8);
        Path selected=Path.EMPTY.with(choice,1).orElseThrow();
        Value prefixes=Value.of(new Literal("same"),Path.EMPTY).merge(Value.of(new Literal("same"),selected));
        Value suffix=Value.of(new Literal("first"),selected).merge(Value.of(new Literal("late"),selected));
        var joined=new Combinations().join(List.of(prefixes,suffix),seed,2,budget);
        assertEquals(2,joined.values().size());
        assertTrue(joined.values().stream().anyMatch(value -> value.atoms().contains(new Literal("late"))));
        Combinations bounded=new Combinations();
        var limited=bounded.join(List.of(prefixes,suffix),seed,64,budget,1);
        assertTrue(limited.truncated());assertEquals(1,limited.consumed());
        var grown=bounded.join(List.of(prefixes,suffix),seed,64,budget,64);
        assertFalse(grown.truncated());
        assertEquals(0,bounded.join(List.of(prefixes,suffix),seed,64,budget,64).consumed());
    }
}
