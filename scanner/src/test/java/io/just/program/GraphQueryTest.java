package io.just.program;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.program.Program.*;
import java.nio.file.Path;
import java.util.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class GraphQueryTest {
    @TempDir Path temp;
    @Test void shallowerSharedPathsAreExpandedBeforeDeepCursorsWithoutResettingContinuationOffsets() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Graph.java","""
                public class Graph {
                  public static void start() { shared(); }
                  public static void shared() { first(); tail(); }
                  public static void first() {}
                  public static void tail() { sink(); }
                  public static void sink() {}
                }
                """));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            MethodId start=new MethodId("Graph","start","()V"),shared=new MethodId("Graph","shared","()V"),tail=new MethodId("Graph","tail","()V");
            var shallow=new GraphQuery.Cursor(start,0,0);var deep=new GraphQuery.Cursor(shared,2,0);
            for(var scope:List.of(List.of(deep,shallow),List.of(shallow,deep))) {
                var result=GraphQuery.expand(program,GraphQuery.Direction.OUTGOING,scope,3,10,20);
                assertTrue(result.edges().stream().anyMatch(edge -> edge.from().equals(tail) && edge.to().name().equals("sink")));
                assertEquals(4,result.edges().size());
            }
            var resumed=GraphQuery.expand(program,GraphQuery.Direction.OUTGOING,List.of(new GraphQuery.Cursor(shared,2,1),shallow),3,10,20);
            assertEquals(List.of("tail"),resumed.edges().stream().filter(edge -> edge.from().equals(shared)).map(edge -> edge.to().name()).toList());
            assertTrue(resumed.edges().stream().anyMatch(edge -> edge.from().equals(tail)));
        }
    }
}
