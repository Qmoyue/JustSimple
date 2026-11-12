package io.just;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class RelationSelectionTest {
    @TempDir Path temp;
    @Test void nativeSelectionUsesTheDispatchedHookRatherThanAnUncalledMethodOfItsClass()throws Exception {
        Path reference=BytecodeFixtures.compile(temp,8,Map.of("History.java","class History {Next owned;void step(){owned.accept();}} class Next {void accept(){}}"));
        Path file;
        try(Inputs input=Inputs.open(reference,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            file=ReferenceFixtures.write(temp.resolve("native-reference.json"),new Program(input,20000),new MethodId("History","step","()V"));
        }
        for(boolean overwritten:List.of(false,true)) {
            StringBuilder source=new StringBuilder("""
                public class NativeRoutes {
                  public static class Stage implements java.io.Serializable {public void accept(){terminal();}}
                  public static class Quiet extends Stage {public void accept(){}}
                  public static class ZOwner implements java.io.Serializable {
                    Stage owned;
                    private void readObject(java.io.ObjectInputStream input)throws Exception {input.defaultReadObject();OVERWRITE owned.accept();}
                  }
                  public static void scan(java.io.ObjectInputStream input)throws Exception {ordinary();input.readObject();}
                  static void terminal(){}static void ordinary(){}
                """.replace("OVERWRITE",overwritten?"owned=new Quiet();":""));
            for(int i=0;i<90;i++)source.append("public static class A").append(String.format("%02d",i)).append(" implements java.io.Serializable {Stage unrelated;public void unused(){unrelated.accept();}private void readObject(java.io.ObjectInputStream input)throws Exception{input.defaultReadObject();}}\n");
            source.append('}');Path classes=BytecodeFixtures.compile(temp,8,Map.of("NativeRoutes.java",source.toString()));
            MethodId terminal=new MethodId("NativeRoutes","terminal","()V"),ordinary=new MethodId("NativeRoutes","ordinary","()V");
            try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
                Program program=new Program(input,20000);
                var result=new Analyzer(program,new Mechanisms(program,Catalog.read(file),Set.of(terminal,ordinary)),Analyzer.Limits.defaults())
                        .scan(EntryPoints.Mode.APPLICATION,true,Set.of(new MethodId("NativeRoutes","scan","(Ljava/io/ObjectInputStream;)V")));
                assertEquals(!overwritten,result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT && result.relations().get(f.path().get(f.path().size()-1)).target().equals(Optional.of(terminal))),"uncalled matching methods must not consume the native hook preference frontier; a strong write still selects Quiet");
                assertTrue(result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT && result.relations().get(f.path().get(f.path().size()-1)).target().equals(Optional.of(ordinary))));
                assertTrue(result.limitations().stream().anyMatch(s -> s.contains("serialized type frontier")));
            }
        }
    }
    @Test void anOwnedFieldHandoffSelectsAnImplementationBeyond64WithoutGivingItProof()throws Exception {
        Path reference=BytecodeFixtures.compile(temp,17,Map.of("Historical.java","""
            class Historical { Next owned; void handoff(){owned.accept();} }
            class Next {void accept(){}}
            """));
        Path file;
        try(Inputs input=Inputs.open(reference,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            file=ReferenceFixtures.write(temp.resolve("reference.json"),new Program(input,20000),new MethodId("Historical","handoff","()V"));
        }
        StringBuilder source=new StringBuilder("""
            public class Routes {
              public interface Step extends java.io.Serializable {void step();}
              public static class Forward implements java.io.Serializable {String text;public void accept(){terminal(text);}}
              public static class ZUseful implements Step {Forward owned;public void step(){owned.accept();}}
              static void noise(){} static void terminal(String value){} static void ordinary(){}
              public static void entry(Step receiver){receiver.step();ordinary();}
            """);
        for(int i=0;i<90;i++)source.append("public static class A").append(String.format("%02d",i)).append(" implements Step {public void step(){noise();}}\n");
        source.append('}');Path classes=BytecodeFixtures.compile(temp,17,Map.of("Routes.java",source.toString()));
        MethodId terminal=new MethodId("Routes","terminal","(Ljava/lang/String;)V"),ordinary=new MethodId("Routes","ordinary","()V");
        for(boolean enabled:List.of(false,true))try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            var result=new Analyzer(program,new Mechanisms(program,Catalog.read(file),Set.of(terminal,ordinary)),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,enabled,Set.of(new MethodId("Routes","entry","(LRoutes$Step;)V")));
            assertEquals(enabled,result.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.target().equals(Optional.of(terminal))),"the useful implementation is beyond the old virtual target frontier");
            assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.target().equals(Optional.of(ordinary))),"ordinary work remains scheduled");
            assertTrue(result.limitations().stream().anyMatch(s -> s.contains("virtual target frontier")),"omitted implementations remain visible");
            if(enabled) {
                assertTrue(result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).anyMatch(f -> !f.proof().isEmpty()));
                assertTrue(result.relations().stream().filter(r -> r.target().equals(Optional.of(terminal))).flatMap(r -> r.supports().stream()).flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.INPUT_BINDING),"the unknown owned field is still an input condition");
            }
        }
    }
}
