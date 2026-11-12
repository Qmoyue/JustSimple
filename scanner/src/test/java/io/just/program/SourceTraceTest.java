package io.just.program;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.program.Program.*;
import java.nio.file.Path;
import java.util.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class SourceTraceTest {
    @TempDir Path temp;

    private static final MethodId METHOD = new MethodId("Graph", "value", "(I)I");

    private static Assign assign(int instruction, Origin... inputs) {
        return new Assign(new Site(METHOD, instruction, -1, "graph"),
                new Sources(new LinkedHashSet<>(List.of(inputs))));
    }

    @Test void sharedSourcesAtTheBudgetBoundaryAreNotAnUnexploredFrontier() {
        Map<Integer, Action> graph = Map.of(
                0, assign(0, new Producer(1), new Producer(2)),
                1, assign(1, new Parameter(0)),
                2, assign(2, new Parameter(0)));
        var trace = SourceTrace.trace(graph, Map.of(), new Producer(0), 4);
        assertFalse(trace.truncated());
        assertFalse(trace.cyclic());
        assertEquals(Set.of(new Parameter(0)), trace.parameters());
        assertEquals(4, trace.visited());
    }

    @Test void longSourcesAndCyclesDoNotUseTheJavaCallStack() {
        Map<Integer, Action> graph = new HashMap<>();
        for (int i = 0; i < 6000; i++) graph.put(i, assign(i, new Producer(i + 1)));
        graph.put(6000, assign(6000, new Parameter(0)));
        var complete = SourceTrace.trace(graph, Map.of(), new Producer(0), 6002);
        assertFalse(complete.cyclic());
        assertFalse(complete.truncated());
        assertEquals(Set.of(new Parameter(0)), complete.parameters());
        graph.put(6000, assign(6000, new Producer(3000)));
        assertTrue(SourceTrace.trace(graph, Map.of(), new Producer(0), 6002).cyclic());
    }

    @Test void callersChooseTheNextSourceQuestionAndItsBudgetWithoutAScanner() throws Exception {
        Path classes = BytecodeFixtures.compile(temp, 17, Map.of("Source.java", """
                public class Source {
                  public static class Box { public Object value; }
                  public static Object read(Box box, long count) { return box.value; }
                  public static int calculate(int value) { return (value + 1) * (value + 2); }
                }
                """));
        try (Inputs input = Inputs.open(classes, List.of(), Path.of(System.getProperty("java.home")), Inputs.Limits.defaults())) {
            Program program = new Program(input, 20000);
            MethodId read = new MethodId("Source", "read", "(LSource$Box;J)Ljava/lang/Object;");
            Returned returned = program.facts(read).actions().stream().filter(Returned.class::isInstance)
                    .map(Returned.class::cast).findFirst().orElseThrow();
            Origin origin = returned.value().origins().iterator().next();
            var field = SourceTrace.query(program, read, origin, 16).value().orElseThrow();
            assertEquals(1, field.plan().fields().size());
            assertTrue(field.plan().parameters().isEmpty(), "field values remain questions about the owning object");
            Origin receiver = field.plan().fields().get(0).receiver().origins().iterator().next();
            var owner = SourceTrace.query(program, read, receiver, 1).value().orElseThrow();
            assertEquals(Set.of(new Parameter(0)), owner.plan().parameters());
            assertThrows(IllegalArgumentException.class, () -> SourceTrace.query(program, read, new Parameter(2), 1));
            var formal = SourceTrace.query(new Program(input, 1), read, new Parameter(0), 1).value().orElseThrow();
            assertEquals(Set.of(new Parameter(0)), formal.plan().parameters());
            assertTrue(formal.limitations().isEmpty(), "formal parameters need signature metadata, not method interpretation");

            MethodId calculate = new MethodId("Source", "calculate", "(I)I");
            Returned value = program.facts(calculate).actions().stream().filter(Returned.class::isInstance)
                    .map(Returned.class::cast).findFirst().orElseThrow();
            Origin result = value.value().origins().iterator().next();
            var partial = SourceTrace.query(program, calculate, result, 1);
            assertTrue(partial.value().orElseThrow().plan().truncated());
            assertTrue(partial.pending().stream().anyMatch(issue -> issue.cause() == QueryCause.BUDGET));
            var complete = SourceTrace.query(program, calculate, result, 32);
            assertFalse(complete.value().orElseThrow().plan().truncated());
            assertEquals(Set.of(new Parameter(0)), complete.value().orElseThrow().plan().parameters());
            assertTrue(program.limitations().stream().noneMatch(detail -> detail.contains("source frontier")));
            assertTrue(SourceTrace.query(program, new MethodId("Source", "absent", "()V"), new Producer(0), 1).absent());
            assertFalse(SourceTrace.query(program, new MethodId("Missing", "read", "()V"), new Producer(0), 1).pending().isEmpty());
        }
    }
}
