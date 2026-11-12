package io.just;

import com.google.gson.*;
import io.just.analysis.*;
import io.just.analysis.ScanResult.*;
import io.just.input.*;
import io.just.program.Program;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.report.Reports;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.nio.file.Path;
import java.io.*;
import java.util.*;
import java.util.stream.Collectors;
import static org.junit.jupiter.api.Assertions.*;

class InputNeedsTest {
    @TempDir Path temp;
    private Path fixture() throws IOException {
        return BytecodeFixtures.compile(temp,8,Map.of("Needs.java","""
                public class Needs {
                  public static class Box {public String name;public String noise;}
                  public static class Target {public static void alpha(){}public static void beta(){}}
                  public static void run(Box box)throws Exception {Target.class.getMethod(box.name,new Class[0]).invoke(null,new Object[0]);}
                }
                """));
    }
    private ScanResult scan(Path classes,Optional<Path> snapshot) throws IOException {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults(),true).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Needs","run","(LNeeds$Box;)V")),snapshot.map(path -> {try{return StaticData.read(path);}catch(IOException e){throw new UncheckedIOException(e);}}));
        }
    }
    private Path snapshot(String basis,String field,String value) throws IOException {
        Path path=Files.createTempFile(temp,"facts-",".json");
        Files.writeString(path,"""
                {"source":"finite source-built fixture","basis":"BASIS","entry":{"owner":"Needs","name":"run","descriptor":"(LNeeds$Box;)V","arguments":[{"ref":"box"}]},"objects":[{"id":"box","type":"Needs$Box","fields":[{"owner":"Needs$Box","name":"FIELD","descriptor":"Ljava/lang/String;","value":"VALUE"}]}]}
                """.replace("BASIS",basis).replace("FIELD",field).replace("VALUE",value));return path;
    }
    private Set<String> targets(ScanResult result){return result.relations().stream().flatMap(r -> r.target().stream()).filter(m -> m.owner().equals("Needs$Target")).map(Program.MethodId::name).collect(Collectors.toSet());}
    @Test void candidatesRequireOnlyUsedInputAndVerifiedBindingIsDistinctFromAssumptionAndReference() throws IOException {
        Path classes=fixture();ScanResult unknown=scan(classes,Optional.empty());
        assertEquals(Set.of("alpha","beta"),targets(unknown));
        var name=unknown.inputRequirements().stream().filter(r -> r.needed().kind()==NeedKind.METHOD_NAME).findFirst().orElseThrow();
        assertEquals(0,name.source().orElseThrow().parameterSlot());assertTrue(name.source().get().path().stream().anyMatch(s -> s instanceof Field f && f.field().name().equals("name")));
        assertFalse(unknown.inputRequirements().stream().anyMatch(r -> r.source().stream().flatMap(s -> s.path().stream()).anyMatch(s -> s instanceof Field f && f.field().name().equals("noise"))));
        assertTrue(unknown.statistics().backwardQueries()>0);assertFalse(unknown.demandFrontier().isEmpty());
        assertTrue(unknown.breakpoints().stream().anyMatch(point -> point.reason()==GapKind.INPUT_BINDING && point.use().equals(name.use()) && point.subject().filter(name.needed().subject()::equals).isPresent()));
        assertTrue(unknown.breakpoints().stream().anyMatch(point -> point.slot().filter(slot -> slot instanceof Field field && field.field().name().equals("name")).isPresent()));
        ScanResult binding=scan(classes,Optional.of(snapshot("BINDING","name","alpha")));
        assertEquals(Set.of("alpha"),targets(binding));assertTrue(binding.inputRequirements().isEmpty(),binding.inputRequirements().toString());
        ScanResult unrelated=scan(classes,Optional.of(snapshot("BINDING","noise","irrelevant")));assertEquals(targets(unknown),targets(unrelated));
        ScanResult assumption=scan(classes,Optional.of(snapshot("ASSUMPTION","name","alpha")));assertEquals(Set.of("alpha"),targets(assumption));
        assertTrue(assumption.findings().stream().flatMap(f -> f.gaps().stream()).noneMatch(g -> g.kind()==GapKind.CONTROL_CONDITION),"an assumed input must not add an unrelated normal-return condition to this empty, resolved target");
        ScanResult reference=scan(classes,Optional.of(snapshot("REFERENCE","name","alpha")));assertEquals(targets(unknown),targets(reference));
        ScanResult contradiction=scan(classes,Optional.of(snapshot("BINDING","name","absent")));assertTrue(contradiction.findings().isEmpty());assertTrue(targets(contradiction).isEmpty());
    }
    @Test void reportPreservesTypedNeedsAndTemplateCannotBeMistakenForFacts() throws IOException {
        ScanResult result=scan(fixture(),Optional.empty());Path output=temp.resolve("report");Reports.write(result,output);
        JsonObject report=JsonParser.parseString(Files.readString(output.resolve("report.json"))).getAsJsonObject();
        assertEquals(result.inputRequirements().size(),report.getAsJsonArray("inputRequirements").size());assertFalse(report.getAsJsonArray("demandFrontier").isEmpty());
        assertEquals(result.breakpoints().size(),report.getAsJsonArray("breakpoints").size());
        for(var gap:result.relations().stream().flatMap(relation -> relation.supports().stream().flatMap(s -> s.gaps().stream())).distinct().toList())
            assertTrue(result.breakpoints().stream().anyMatch(point -> point.reason()==gap.kind() && point.cause().filter(gap.site()::equals).isPresent() && point.detail().equals(gap.detail())),"every cause remains located: "+gap);
        var first=result.breakpoints().stream().filter(point -> point.subject().isPresent()).findFirst().orElseThrow();
        assertTrue(report.getAsJsonArray("breakpoints").asList().stream().anyMatch(row -> row.getAsJsonObject().get("reason").getAsString().equals(first.reason().name()) && row.getAsJsonObject().get("context").getAsInt()==first.context()));
        JsonObject template=JsonParser.parseString(Files.readString(output.resolve("input-requirements.json"))).getAsJsonObject();
        assertEquals("INPUT_REQUIREMENTS_TEMPLATE",template.get("kind").getAsString());
        for(JsonElement row:template.getAsJsonArray("requirements")) {
            assertEquals("UNRESOLVED",row.getAsJsonObject().get("state").getAsString());
            assertEquals("UNKNOWN",row.getAsJsonObject().getAsJsonObject("proposedValue").get("kind").getAsString());
        }
        assertThrows(IOException.class,() -> StaticData.read(output.resolve("input-requirements.json")));
        assertTrue(Files.readString(output.resolve("report.md")).contains("METHOD_NAME"));
        assertTrue(Files.readString(output.resolve("report.md")).contains(first.reason().name()+" context "+first.context()));
    }
}
