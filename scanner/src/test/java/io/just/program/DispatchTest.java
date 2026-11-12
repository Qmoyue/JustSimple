package io.just.program;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.program.Program.*;
import java.nio.file.Path;
import java.util.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class DispatchTest {
    @TempDir Path temp;

    @Test void scopeAndBudgetsBelongToEachQueryAndDoNotChangeScannerDefaults() throws Exception {
        Path classes = BytecodeFixtures.compile(temp, 17, Map.of("Receivers.java", """
                public class Receivers {
                  public interface Action { int run(); }
                  public static class One implements Action { public int run() { return 1; } }
                  public static class Two implements Action { public int run() { return 2; } }
                  public static class Native implements Action { public native int run(); }
                  public static class Other { public int run() { return 3; } }
                }
                """));
        try (Inputs input = Inputs.open(classes, List.of(), Path.of(System.getProperty("java.home")), Inputs.Limits.defaults())) {
            Program program = new Program(input, 20000);
            Dispatch dispatch = new Dispatch(program);
            MethodId requested = new MethodId("Receivers$Action", "run", "()I");
            List<DefinedType> scope = List.of(new DefinedType("Receivers$One", 0), new DefinedType("Receivers$Two", 0));
            var partial = dispatch.within(requested, requested.owner(), 0, scope, new Dispatch.Budget(1, 8));
            assertEquals(1, partial.value().orElseThrow().targets().size());
            assertEquals(List.of(scope.get(1)), partial.value().orElseThrow().frontier());
            assertTrue(partial.pending().stream().anyMatch(issue -> issue.cause() == QueryCause.BUDGET));
            var complete = dispatch.within(requested, requested.owner(), 0, scope, new Dispatch.Budget(8, 8));
            assertEquals(scope, complete.value().orElseThrow().targets().stream().map(t -> t.receiver().orElseThrow()).toList());
            assertTrue(complete.pending().isEmpty());
            var other = dispatch.within(requested, requested.owner(), 0, List.of(new DefinedType("Receivers$Other", 0)), new Dispatch.Budget(1, 1));
            assertTrue(other.value().orElseThrow().targets().isEmpty());
            assertTrue(other.pending().isEmpty());
            var broad = dispatch.within(requested, "java/lang/Object", 0,
                    List.of(new DefinedType("Receivers$Other", 0)), new Dispatch.Budget(1, 1));
            assertTrue(broad.value().orElseThrow().targets().isEmpty(),
                    "a broad receiver upper bound must still satisfy the bytecode member owner");
            assertTrue(program.implementations(requested, "Receivers$Other", 0).value().orElseThrow().isEmpty());
            var nativeTarget = dispatch.within(requested, requested.owner(), 0,
                    List.of(new DefinedType("Receivers$Native", 0)), new Dispatch.Budget(1, 1));
            assertFalse(nativeTarget.value().orElseThrow().targets().get(0).method().hasBody());
            var missing = dispatch.within(requested, requested.owner(), 0,
                    List.of(new DefinedType("Missing", 0)), new Dispatch.Budget(1, 1));
            assertTrue(missing.value().orElseThrow().targets().isEmpty());
            assertTrue(missing.pending().stream().anyMatch(issue -> issue.cause() == QueryCause.MISSING_DEPENDENCY));
            assertTrue(program.limitations().stream().noneMatch(detail -> detail.contains("inspection frontier")));
            assertEquals(2, program.implementations(requested, requested.owner(), 0).value().orElseThrow().size());
        }
    }

    @Test void metadataLoadedDuringDiscoveryMustNotFreezeAnOlderReceiverScope() throws Exception {
        Path classes = BytecodeFixtures.compile(temp, 17, Map.of("Child.java", "public class Child extends java.util.ArrayList<Object> {}"));
        try (Inputs input = Inputs.open(classes, List.of(), Path.of(System.getProperty("java.home")), Inputs.Limits.defaults())) {
            Program program = new Program(input, 20000);
            MethodId requested = new MethodId("java/util/List", "size", "()I");
            program.implementations(requested, requested.owner(), 0);
            var refreshed = program.implementations(requested, requested.owner(), 0).value().orElseThrow();
            assertTrue(refreshed.stream().anyMatch(target -> target.receiver().equals(Optional.of(new DefinedType("java/util/ArrayList", 0)))),
                    "a cached query must include concrete platform types exposed while preparing its first scope");
        }
    }
}
