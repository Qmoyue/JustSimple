package io.just;

import com.google.gson.*;
import io.just.analysis.*;
import io.just.app.Main;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.program.Program;
import io.just.program.Program.MethodId;
import io.just.report.Reports;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.Path;
import java.util.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class CliProgressTest {
    @TempDir Path temp;
    private static final MethodId ENTRY=new MethodId("ProgressFixture","entry","(Ljava/lang/Object;)Ljava/lang/Object;");
    private static final MethodId SINK=new MethodId("ProgressFixture","sink",ENTRY.descriptor());
    private Path compile()throws Exception {
        return BytecodeFixtures.compile(temp,17,Map.of("ProgressFixture.java","""
                public class ProgressFixture {
                  static { if(System.nanoTime()!=0)throw new AssertionError("must never execute"); }
                  public static Object entry(Object value) { return sink(value); }
                  public static Object sink(Object value) { return value; }
                  public static void numbers() { numbers(Double.NaN,Double.POSITIVE_INFINITY,Float.NEGATIVE_INFINITY,"NaN"); }
                  public static void numbers(double a,double b,float c,String text) {}
                }
                """));
    }
    @Test void cliAcceptsUnicodeClassAndMethodSelectors()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("审计.java","public class 审计 { public static Object 入口(Object value){return 终点(value);} public static Object 终点(Object value){return value;} }"));
        ByteArrayOutputStream errors=new ByteArrayOutputStream();
        int code=Main.run(new String[]{"--input",classes.toString(),"--jdk-home",System.getProperty("java.home"),"--output",temp.resolve("unicode").toString(),
                "--mode","component","--entry","审计#入口(Ljava/lang/Object;)Ljava/lang/Object;","--sink","审计#终点(Ljava/lang/Object;)Ljava/lang/Object;","--no-guidance"},
                new PrintStream(OutputStream.nullOutputStream(),true,StandardCharsets.UTF_8),new PrintStream(errors,true,StandardCharsets.UTF_8));
        assertEquals(0,code,errors.toString(StandardCharsets.UTF_8));
        JsonObject json=JsonParser.parseString(Files.readString(temp.resolve("unicode/report.json"))).getAsJsonObject();
        assertEquals(1,json.getAsJsonArray("findings").size());
    }

    @Test void cliRejectsAnExistingOutputBeforeIndexingInput() throws Exception {
        Path output = Files.createDirectory(temp.resolve("existing"));
        Path marker = Files.writeString(output.resolve("keep.txt"), "keep");
        ByteArrayOutputStream errors = new ByteArrayOutputStream();
        try (PrintStream out = new PrintStream(OutputStream.nullOutputStream(), true, StandardCharsets.UTF_8);
             PrintStream err = new PrintStream(errors, true, StandardCharsets.UTF_8)) {
            int code = Main.run(new String[]{"--input", temp.resolve("not-read").toString(),
                    "--jdk-home", System.getProperty("java.home"), "--output", output.toString()}, out, err);
            assertEquals(2, code);
        }
        String diagnostics = errors.toString(StandardCharsets.UTF_8);
        assertTrue(diagnostics.contains("report directory already exists"), diagnostics);
        assertFalse(diagnostics.contains("[read]"), diagnostics);
        assertEquals("keep", Files.readString(marker));
    }
    @Test void reportWritingCooperatesWithCancellationAndPreservesExistingOutputs()throws Exception {
        ScanResult result=scan(compile(),Optional.empty());
        Writer interrupting=new Writer() {
            @Override public void write(char[] chars,int offset,int length){Thread.currentThread().interrupt();}
            @Override public void flush() {}
            @Override public void close() {}
        };
        try { assertThrows(java.util.concurrent.CancellationException.class,() -> Reports.json(result,interrupting)); }
        finally { Thread.interrupted(); }
        Path output=temp.resolve("cancelled");Thread.currentThread().interrupt();
        try { assertThrows(java.util.concurrent.CancellationException.class,() -> Reports.write(result,output)); }
        finally { Thread.interrupted(); }
        assertFalse(Files.exists(output));
        try(var files=Files.list(temp)){assertTrue(files.noneMatch(file -> file.getFileName().toString().startsWith(".justsimple-report-")));}
        Reports.write(result,output);
        String original=Files.readString(output.resolve("report.json"));
        assertThrows(FileAlreadyExistsException.class,() -> Reports.write(result,output));
        assertEquals(original,Files.readString(output.resolve("report.json")));
    }
    @Test void cliWritesStagesToStderrAndKeepsTheFinalResultOnStdout()throws Exception {
        Path classes=compile();ByteArrayOutputStream stdout=new ByteArrayOutputStream(),stderr=new ByteArrayOutputStream();
        int code=Main.run(new String[]{"--input",classes.toString(),"--jdk-home",System.getProperty("java.home"),
                "--output",temp.resolve("report").toString(),"--mode","component","--entry",ENTRY.toString(),"--sink",SINK.toString(),"--no-guidance"},
                new PrintStream(stdout,true,StandardCharsets.UTF_8),new PrintStream(stderr,true,StandardCharsets.UTF_8));
        assertEquals(0,code,stderr.toString(StandardCharsets.UTF_8));
        String status=stderr.toString(StandardCharsets.UTF_8);int previous=-1;
        for(String phase:List.of("[read]","[entries]","[knowledge]","[analysis]","[recovery]","[write]")) {
            int at=status.indexOf(phase);assertTrue(at>previous,"ordered CLI phase: "+phase);previous=at;
        }
        assertTrue(status.contains("steps="));assertTrue(status.contains("queued="));
        assertTrue(stdout.toString(StandardCharsets.UTF_8).startsWith("FINISHED FINDINGS:"));
    }
    @Test void observingProgressPreservesCanonicalEvidenceAndReportsActualWork()throws Exception {
        Path classes=compile();List<Analyzer.ScanProgress> observed=new ArrayList<>();
        ScanResult quiet=scan(classes,Optional.empty()),visible=scan(classes,Optional.of(observed));
        assertEquals(normalize(quiet),normalize(visible));
        assertTrue(observed.stream().anyMatch(p -> p.stage()==Analyzer.Stage.ANALYSIS));
        Analyzer.ScanProgress last=observed.get(observed.size()-1);
        assertEquals(Analyzer.Stage.RECOVERY,last.stage());assertEquals(visible.statistics().workItems(),last.steps());
        assertEquals(visible.statistics().contexts(),last.contexts());assertEquals(visible.relations().size(),last.relations());
        long previous=0;for(Analyzer.ScanProgress progress:observed){assertTrue(progress.steps()>=previous);previous=progress.steps();}
    }
    @Test void specialFloatingPointValuesDoNotPreventReportPublication()throws Exception {
        Path classes=compile(),output=temp.resolve("numbers");ByteArrayOutputStream errors=new ByteArrayOutputStream();
        int code=Main.run(new String[]{"--input",classes.toString(),"--jdk-home",System.getProperty("java.home"),
                "--output",output.toString(),"--mode","component","--entry","ProgressFixture#numbers()V",
                "--sink","ProgressFixture#numbers(DDFLjava/lang/String;)V","--no-guidance"},
                new PrintStream(OutputStream.nullOutputStream(),true,StandardCharsets.UTF_8),new PrintStream(errors,true,StandardCharsets.UTF_8));
        assertEquals(0,code,errors.toString(StandardCharsets.UTF_8));
        JsonObject json=JsonParser.parseString(Files.readString(output.resolve("report.json"))).getAsJsonObject();
        List<JsonElement> values=json.getAsJsonObject("references").getAsJsonArray("values").asList().stream()
                .map(JsonElement::getAsJsonObject).filter(v -> v.get("kind").getAsString().equals("Literal"))
                .map(v -> v.getAsJsonObject("value").get("value")).toList();
        for(String expected:List.of("{\"type\":\"Double\",\"value\":\"NaN\"}","{\"type\":\"Double\",\"value\":\"Infinity\"}","{\"type\":\"Float\",\"value\":\"-Infinity\"}"))
            assertTrue(values.contains(JsonParser.parseString(expected)),expected);
        assertTrue(values.contains(new JsonPrimitive("NaN")),"a string must remain distinct from a numeric NaN");
        assertTrue(Files.exists(output.resolve("report.md")));assertTrue(Files.exists(output.resolve("input-requirements.json")));
    }
    private ScanResult scan(Path classes,Optional<List<Analyzer.ScanProgress>> observed)throws Exception {
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);
            Analyzer analyzer=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(SINK)),Analyzer.Limits.defaults());
            return observed.isPresent()?analyzer.scan(EntryPoints.Mode.COMPONENT,false,Set.of(ENTRY),Optional.empty(),observed.get()::add)
                    :analyzer.scan(EntryPoints.Mode.COMPONENT,false,Set.of(ENTRY));
        }
    }
    private JsonObject normalize(ScanResult result)throws Exception {
        StringWriter writer=new StringWriter();Reports.json(result,writer);
        JsonObject json=JsonParser.parseString(writer.toString()).getAsJsonObject();json.getAsJsonObject("statistics").addProperty("elapsedMillis",0);return json;
    }
}
