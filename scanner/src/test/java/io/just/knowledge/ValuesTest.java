package io.just.knowledge;

import io.just.knowledge.Values.*;
import io.just.program.Program.MethodId;
import io.just.program.Program.Site;
import java.util.*;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class ValuesTest {
    @Test void requiringAddsNewGapsEvenWhenOldGapsRepeat() {
        Site site=new Site(new MethodId("Fixture","read","()V"),1,1,"fixture");
        Gap a=new Gap(GapKind.UNSUPPORTED,site,"first"),b=new Gap(GapKind.MISSING_DEPENDENCY,site,"second");
        var branch=new BranchKey(0,1);
        Path left=Path.EMPTY.with(branch,2).orElseThrow(),right=Path.EMPTY.with(branch,3).orElseThrow();
        Bound unchanged=new Bound(new Literal("left"),left,List.of(a,b),Set.of(1));
        Bound repeated=new Bound(new Literal("right"),right,List.of(a,a),Set.of(2));
        Value value=new Value(new LinkedHashSet<>(List.of(unchanged,repeated)));
        assertEquals(List.of(unchanged,new Bound(repeated.atom(),right,List.of(a,b),Set.of(2))),
                List.copyOf(value.requiring(List.of(b,a,b)).alternatives()));
        assertSame(value,value.requiring(List.of(a)));
    }

    @Test void compatibilityAndMergeRespectValuesRangesAndBranchChoices() {
        var source=new InputSource(new MethodId("Fixture","read","(I)V"),0,List.of());
        var unknown=new Symbolic("I","argument");
        Path low=Path.EMPTY.restricting(source,unknown,"I",new IntegralRange(1,4)).orElseThrow();
        Path high=Path.EMPTY.restricting(source,unknown,"I",new IntegralRange(3,7)).orElseThrow();
        Path overlap=low.and(high).orElseThrow();
        assertTrue(low.compatible(high));
        assertEquals(Optional.of(new IntegralRange(3,4)),overlap.selections().get(source).range());
        assertTrue(low.selections().get(source).impliedBy(overlap.selections().get(source)));
        assertFalse(overlap.selections().get(source).impliedBy(low.selections().get(source)));
        Path outside=Path.EMPTY.selecting(source,new Literal(7),"I").orElseThrow();
        assertFalse(low.compatible(outside));
        assertTrue(low.and(outside).isEmpty());
        assertTrue(high.compatible(outside));
        assertEquals(Optional.of(new Literal(7)),high.and(outside).orElseThrow().selected(source));
        BranchKey branch=new BranchKey(0,1);
        Path left=low.with(branch,2).orElseThrow(),right=high.with(branch,3).orElseThrow();
        assertFalse(left.compatible(right));
        assertTrue(left.and(right).isEmpty());

        Path string=Path.EMPTY.selecting(source,new Literal("text"),"Ljava/lang/String;").orElseThrow();
        Path sequence=Path.EMPTY.selecting(source,new Literal("text"),"Ljava/lang/CharSequence;").orElseThrow();
        assertTrue(string.compatible(sequence));
        assertEquals(Set.of("Ljava/lang/String;","Ljava/lang/CharSequence;"),
                string.and(sequence).orElseThrow().selections().get(source).types());
    }
}
