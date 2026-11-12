package io.just.analysis;

import io.just.analysis.ScanResult.*;
import io.just.input.Inputs;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import io.just.program.Program.*;
import java.util.*;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class ConnectionCheckTest {
    @TempDir java.nio.file.Path temp;
    private Inputs input;
    private Program program;
    private static final MethodId METHOD=new MethodId("Fixture","entry","()V");
    private static final Site SITE=new Site(METHOD,7,1,"Fixture.java");
    private static final Support GROUNDED=new Support(Evidence.PROVEN,List.of(SITE),List.of(),List.of());

    @BeforeEach void open()throws Exception {
        input=Inputs.open(temp,List.of(),java.nio.file.Path.of(System.getProperty("java.home")),Inputs.Limits.defaults());
        program=new Program(input,100);
    }
    @AfterEach void close()throws Exception {if(input!=null)input.close();}

    @Test void alternativesNeedAnExplicitSelectionAndIndependentRootsStayDisconnected() {
        var evidence=List.of(relation(3,List.of(GROUNDED)),relation(11,List.of(dependent(3),GROUNDED)));
        var unselected=ConnectionCheck.query(program,evidence,List.of(11),List.of(),10);
        assertEquals(ConnectionCheck.State.PENDING,unselected.state());
        assertEquals(List.of(11),unselected.frontier());
        assertTrue(unselected.pending().contains("select one of 2 alternative supports for relation 11"));
        var connected=ConnectionCheck.query(program,evidence,List.of(3,11),List.of(new ProofUse(11,0)),10);
        assertEquals(ConnectionCheck.State.CLOSED,connected.state());
        assertEquals(List.of(new ProofUse(3,0),new ProofUse(11,0)),connected.uses());
        assertEquals(List.of(),connected.gaps());assertEquals(List.of(),connected.pending());
        var separate=ConnectionCheck.query(program,evidence,List.of(3,11),List.of(new ProofUse(11,1)),10);
        assertEquals(ConnectionCheck.State.PENDING,separate.state());
        assertEquals(List.of("requested roots have no selected support dependency connecting them"),separate.pending());
    }
    @Test void aJointSupportChecksEveryDependencyAndKeepsItsConcreteGap() {
        Gap gap=new Gap(GapKind.CONTROL_CONDITION,SITE,"unresolved branch");
        var evidence=List.of(relation(3,List.of(GROUNDED)),relation(7,List.of(new Support(Evidence.CONDITIONAL,List.of(SITE),List.of(gap),List.of()))),
                relation(11,List.of(dependent(3,7))));
        var result=ConnectionCheck.query(program,evidence,List.of(11),List.of(),10);
        assertEquals(ConnectionCheck.State.PENDING,result.state());assertEquals(3,result.inspected());
        assertEquals(List.of(new ProofUse(11,0),new ProofUse(3,0),new ProofUse(7,0)),result.uses());
        assertEquals(List.of(gap),result.gaps());assertEquals(List.of(),result.frontier());assertEquals(List.of(),result.pending());
    }
    @Test void budgetsReturnUnvisitedIdentitiesAndIncompatiblePathsContradict() {
        var evidence=List.of(relation(3,List.of(GROUNDED)),relation(11,List.of(dependent(3))));
        var limited=ConnectionCheck.query(program,evidence,List.of(11),List.of(),1);
        assertEquals(ConnectionCheck.State.PENDING,limited.state());assertEquals(1,limited.inspected());
        assertEquals(List.of(3),limited.frontier());assertEquals(List.of(new ProofUse(11,0)),limited.uses());
        assertEquals(List.of("unexpanded or unselected support frontier"),limited.pending());
        var first=Path.EMPTY.with(new BranchKey(0,7),8).orElseThrow();
        var other=Path.EMPTY.with(new BranchKey(0,7),9).orElseThrow();
        var conflict=ConnectionCheck.query(program,List.of(relation(3,List.of(GROUNDED),first),relation(11,List.of(dependent(3)),other)),List.of(11),List.of(),10);
        assertEquals(ConnectionCheck.State.CONTRADICTED,conflict.state());
        assertTrue(conflict.detail().contains("incompatible paths"));
    }
    @Test void cyclesMissingDependenciesAndUnknownEvidenceRemainDifferentPendingReasons() {
        var cycle=ConnectionCheck.query(program,List.of(relation(3,List.of(dependent(3)))),List.of(3),List.of(),10);
        assertEquals(ConnectionCheck.State.PENDING,cycle.state());
        assertEquals(List.of("selected support dependencies contain a cycle"),cycle.pending());
        var absent=ConnectionCheck.query(program,List.of(relation(11,List.of(dependent(3)))),List.of(11),List.of(),10);
        assertEquals(ConnectionCheck.State.PENDING,absent.state());assertEquals(List.of(3),absent.frontier());
        assertTrue(absent.pending().contains("dependency not present in this result: 3"));
        var unknown=ConnectionCheck.query(program,List.of(relation(3,List.of(new Support(Evidence.UNKNOWN,List.of(),List.of(),List.of())))),List.of(3),List.of(),10);
        assertEquals(ConnectionCheck.State.PENDING,unknown.state());
        assertEquals(List.of("support evidence remains UNKNOWN at relation 3"),unknown.pending());
    }
    @Test void invalidRootsAndSupportChoicesAreErrorsRatherThanPendingEvidence() {
        var evidence=List.of(relation(3,List.of(GROUNDED,dependent(3))));
        assertThrows(IllegalArgumentException.class,() -> ConnectionCheck.query(program,evidence,List.of(0),List.of(),10));
        assertThrows(IllegalArgumentException.class,() -> ConnectionCheck.query(program,evidence,List.of(3),List.of(new ProofUse(3,2)),10));
        assertThrows(IllegalArgumentException.class,() -> ConnectionCheck.query(program,evidence,List.of(3),List.of(new ProofUse(3,0),new ProofUse(3,1)),10));
        assertThrows(IllegalArgumentException.class,() -> ConnectionCheck.query(program,evidence,List.of(3),List.of(),0));
    }
    private static Support dependent(int... ids) {
        return new Support(Evidence.PROVEN,List.of(SITE),List.of(),Arrays.stream(ids).boxed().toList());
    }
    private static Relation relation(int id,List<Support> supports) {return relation(id,supports,Path.EMPTY);}
    private static Relation relation(int id,List<Support> supports,Path path) {
        return new Relation(id,0,Kind.IMPACT,SITE,Optional.of(METHOD),new Literal(null),List.of(),supports,path,"fixture derivation",Optional.empty());
    }
}
