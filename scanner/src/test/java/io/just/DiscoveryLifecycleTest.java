package io.just;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.program.Program;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class DiscoveryLifecycleTest {
    @TempDir Path temp;
    private Inputs input(Path classes)throws Exception {
        return Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults());
    }
    @Test void analysisAndMechanismsMustShareTheSameFactScope() throws Exception {
        Path classes = BytecodeFixtures.compile(temp, 8, Map.of("Scope.java", "public class Scope {}"));
        try (Inputs input = input(classes)) {
            Program program = new Program(input, 20_000);
            assertThrows(IllegalArgumentException.class, () -> new Analyzer(program,
                    new Mechanisms(new Program(input, 20_000)), Analyzer.Limits.defaults()));
        }
    }
    @Test void entryDiscoveryReportsMissingMetadataWithoutDiscardingKnownRoutes()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of(
            "org/springframework/web/bind/annotation/RestController.java","package org.springframework.web.bind.annotation; public @interface RestController {}",
            "org/springframework/web/bind/annotation/RequestMapping.java","package org.springframework.web.bind.annotation; public @interface RequestMapping {}",
            "Healthy.java","@org.springframework.web.bind.annotation.RestController public class Healthy {@org.springframework.web.bind.annotation.RequestMapping public void route(){}}",
            "MissingMarker.java","public @interface MissingMarker {}",
            "Marked.java","@MissingMarker public class Marked {public void run(){}}",
            "MissingParent.java","public class MissingParent {}",
            "Child.java","public class Child extends MissingParent {public void run(){}}"));
        Files.delete(classes.resolve("MissingMarker.class"));Files.delete(classes.resolve("MissingParent.class"));
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);
            var entries=new EntryPoints(program).find(EntryPoints.Mode.APPLICATION,Set.of());
            assertTrue(entries.value().orElseThrow().stream().anyMatch(entry -> entry.method().id().equals(new MethodId("Healthy","route","()V"))));
            for(String missing:List.of("MissingMarker","MissingParent"))assertTrue(entries.pending().stream().anyMatch(issue -> issue.cause()==QueryCause.MISSING_DEPENDENCY && issue.detail().contains(missing)),missing);
        }
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);
            var entries=new EntryPoints(program).find(EntryPoints.Mode.COMPONENT,Set.of());
            assertTrue(entries.value().orElseThrow().stream().anyMatch(entry -> entry.method().id().equals(new MethodId("Child","run","()V"))));
            assertTrue(entries.pending().isEmpty());
            assertTrue(program.missingClasses().isEmpty(),"declared component boundaries do not require HTTP metadata or parent resolution");
        }
    }
    @Test void analyzerRejectsReuseAndIndependentScansDoNotCarryEntriesOrRelations()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Lifetime.java","public class Lifetime {public static void first(){a();}public static void second(){b();}static void a(){}static void b(){}}"));
        for(String entry:List.of("first","second"))try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);Analyzer analyzer=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults());
            var result=analyzer.scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("Lifetime",entry,"()V")));
            assertEquals(List.of(entry),result.entries().stream().map(e -> e.method().id().name()).toList());
            Set<String> calls=new HashSet<>();result.relations().forEach(r -> r.target().filter(t -> t.owner().equals("Lifetime")).ifPresent(t -> calls.add(t.name())));
            assertTrue(calls.contains(entry.equals("first")?"a":"b"));assertFalse(calls.contains(entry.equals("first")?"b":"a"));
            assertThrows(IllegalStateException.class,() -> analyzer.scan(EntryPoints.Mode.COMPONENT,false));
        }
    }
    @Test void inheritedFieldWritersResolveSymbolicOwnersAndMissingDeclarationStaysPending()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of(
                "Base.java","public class Base {public int value;public void action(){}}",
                "Child.java","public class Child extends Base {public void write(){value=1;}public void invoke(){action();}}",
                "Missing.java","public class Missing {public int value;}",
                "Ghost.java","public class Ghost extends Missing {public void write(){value=2;}}"));
        Files.delete(classes.resolve("Missing.class"));
        Path library=Files.createDirectory(temp.resolve("library"));Files.move(classes.resolve("Child.class"),library.resolve("Child.class"));
        try(Inputs input=Inputs.open(classes,List.of(library),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            var writers=program.fieldWriters(new FieldId("Base","value","I"));
            assertTrue(writers.sites().stream().anyMatch(s -> s.method().owner().equals("Child")));
            assertTrue(program.callers(new MethodId("Base","action","()V")).sites().stream().anyMatch(s -> s.method().owner().equals("Child") && s.method().name().equals("invoke")));
            var unresolved=program.fieldWriters(new FieldId("Ghost","value","I"));
            assertFalse(unresolved.sites().isEmpty());assertTrue(unresolved.pending().stream().anyMatch(p -> p.cause()==QueryCause.MISSING_DEPENDENCY));
        }
    }
    @Test void discoveryHasItsOwnVisibleFrontierAndIgnoresUnrelatedMethodFacts()throws Exception {
        StringBuilder helpers=new StringBuilder();for(int i=0;i<260;i++)helpers.append("static void h").append(i).append("(){").append(i==259?"server.createContext(\"/\", exchange -> {});":"h"+(i+1)+"();").append("}");
        Path classes=BytecodeFixtures.compile(temp,8,Map.of(
                "Deep.java","public class Deep {static com.sun.net.httpserver.HttpServer server;public static void main(String[] args){h0();}"+helpers+"}",
                "Selected.java","public class Selected {public static void run()throws Exception {Object.class.getMethod(\"toString\").invoke(new Object());}static void unrelated()throws Exception {"+"Class.forName(\"java.lang.Object\");".repeat(8000)+"}}"));
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);
            var entries=new EntryPoints(program).find(EntryPoints.Mode.APPLICATION,Set.of());
            assertEquals(1,entries.value().orElseThrow().size());assertTrue(entries.pending().stream().anyMatch(p -> p.cause()==QueryCause.BUDGET));
            var scope=program.discover(Set.of(new MethodId("Deep","main","([Ljava/lang/String;)V")),1);
            assertEquals(1,scope.value().orElseThrow().size());assertFalse(scope.pending().isEmpty());
            Program limited=new Program(input,1);
            var hints=new Mechanisms(limited).hints(true,Set.of(new MethodId("Selected","run","()V")));
            assertTrue(hints.pending().isEmpty(),"guidance reads syntax without consuming the method proof budget");
            assertTrue(limited.facts(new MethodId("Selected","run","()V")).limitations().stream().anyMatch(p -> p.cause()==CoverageCause.BUDGET));
        }
        for(boolean guidance:List.of(false,true))try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);
            var result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,guidance,Set.of(new MethodId("Selected","run","()V")));
            assertEquals(ScanResult.Execution.FINISHED,result.execution(),result.limitations().toString());
            assertTrue(result.relations().stream().anyMatch(r -> r.target().filter(t -> t.owner().equals("java/lang/Object") && t.name().equals("toString")).isPresent()));
        }
    }
}
