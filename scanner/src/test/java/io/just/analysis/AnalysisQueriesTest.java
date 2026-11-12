package io.just.analysis;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.program.*;
import io.just.program.Bytecode;
import io.just.program.Program.*;
import java.util.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class AnalysisQueriesTest {
    @TempDir java.nio.file.Path temp;
    private static final MethodId ENTRY=new MethodId("Calls","entry","(Ljava/lang/Object;)Ljava/lang/Object;");
    private java.nio.file.Path compile()throws Exception {
        return BytecodeFixtures.compile(temp,17,Map.of("Calls.java","""
                public class Calls {
                  static { if(System.nanoTime()!=0)throw new AssertionError("must never run"); }
                  public static Object entry(Object value) { return sink(value); }
                  public static Object sink(Object value) { return value; }
                  public static Object reflect(java.lang.reflect.Method m,Object receiver,Object[] args)throws Exception { return m.invoke(receiver,args); }
                  public static Runnable lambda() { return () -> sink("constant"); }
                  public static int branch(int key) { switch(key) { case 3:return 4;case 10:return 7;default:return -1; } }
                }
                """));
    }
    @Test void actualInstructionsExposeBootstrapSwitchAndSourceIdentities()throws Exception {
        try(Inputs input=Inputs.open(compile(),List.of(),java.nio.file.Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            var body=Bytecode.query(program,ENTRY,0,100).value().orElseThrow();
            var invoke=body.instructions().stream().filter(i -> i.mnemonic().equals("INVOKESTATIC")).findFirst().orElseThrow();
            assertEquals(184,invoke.opcode());
            assertTrue(program.facts(ENTRY).actions().stream().anyMatch(a -> a instanceof Call && a.site().equals(invoke.site())));
            assertTrue(Bytecode.query(program,new MethodId("Calls","lambda","()Ljava/lang/Runnable;"),0,100).value().orElseThrow().instructions().stream()
                    .anyMatch(i -> i.mnemonic().equals("INVOKEDYNAMIC") && i.operands().containsKey("bootstrap")));
            var branch=Bytecode.query(program,new MethodId("Calls","branch","(I)I"),0,100).value().orElseThrow().instructions().stream()
                    .filter(i -> i.mnemonic().equals("LOOKUPSWITCH")).findFirst().orElseThrow();
            assertTrue(branch.operands().containsKey("targets"));
            assertThrows(UnsupportedOperationException.class,() -> ((List<?>)branch.operands().get("keys")).clear());
            assertThrows(IllegalArgumentException.class,() -> Bytecode.query(program,ENTRY,Integer.MAX_VALUE,1));
        }
    }
    @Test void knowledgeSelectionPreservesAllGuidanceAndOnlySelectedAttribution()throws Exception {
        try(Inputs input=Inputs.open(compile(),List.of(),java.nio.file.Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);Catalog catalog=Catalog.builtin();
            Set<MethodId> scope=Set.of(new MethodId("Calls","reflect","(Ljava/lang/reflect/Method;Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;"));
            Set<String> all=new LinkedHashSet<>();catalog.entries().forEach(e -> all.add(e.id()));
            var before=catalog.hints(program,scope);assertFalse(before.value().orElseThrow().isEmpty());
            assertEquals(before,catalog.select(all).hints(program,scope));
            String id=before.value().orElseThrow().get(0).references().get(0).entry();Catalog selected=catalog.select(Set.of(id));
            assertEquals(List.of(id),selected.entries().stream().map(Catalog.Entry::id).toList());
            var references=selected.hints(program,scope).value().orElseThrow().stream().flatMap(h -> h.references().stream()).toList();
            assertFalse(references.isEmpty(),"selected guidance must still match the actual reflective call");
            assertEquals(Set.of(id),references.stream().map(r -> r.entry()).collect(java.util.stream.Collectors.toSet()));
            assertEquals(catalog.material(id),selected.material(id));assertTrue(catalog.select(Set.of()).hints(program,scope).value().orElseThrow().isEmpty());
            assertThrows(IllegalArgumentException.class,() -> catalog.select(Set.of("not-a-reference")));
        }
    }
}
