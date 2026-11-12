package io.just;

import io.just.input.*;
import io.just.program.Program;
import io.just.analysis.*;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.io.*;
import java.nio.ByteBuffer;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import java.util.zip.*;
import static org.junit.jupiter.api.Assertions.*;

class InputBoundaryTest {
    @TempDir Path temp;

    @Test void anEmptyModulesDirectoryCannotBeUsedAsPlatformLibraries() throws Exception {
        Path jdk = Files.createDirectory(temp.resolve("empty-jdk"));
        Files.writeString(jdk.resolve("release"), "JAVA_VERSION=\"17.0.1\"\n");
        Files.createDirectory(jdk.resolve("jmods"));
        Path target = Files.createDirectory(temp.resolve("target"));
        IOException failure = assertThrows(IOException.class, () -> {
            try (Inputs ignored = Inputs.open(target, List.of(), jdk, Inputs.Limits.defaults())) {}
        });
        assertTrue(failure.getMessage().contains("target JDK needs rt.jar or jmods"), failure.toString());
    }

    @Test void directoryTraversalChargesNonClassMembersAndRetainsAnExplicitReadFrontier() throws Exception {
        Path target=Files.createDirectory(temp.resolve("target"));Files.createDirectories(target.resolve("first/second"));
        try(Inputs input=Inputs.open(target,List.of(),Path.of(System.getProperty("java.home")),new Inputs.Limits(1<<20,1,100,4,1<<20))) {
            assertTrue(input.summary().limitations().stream().anyMatch(detail -> detail.contains("entry budget")));
            assertEquals(2,input.summary().entriesRead());
            assertTrue(input.targetClasses().isEmpty());
            assertTrue(input.lookup("Missing").truncated().isPresent(),"unvisited members cannot prove a class absent");
        }
    }
    @Test void cancelledInputOpeningStopsBeforeReadingAndKeepsTheInterrupt() throws Exception {
        Thread.currentThread().interrupt();
        try {
            assertThrows(java.util.concurrent.CancellationException.class,() -> {
                try(Inputs ignored=Inputs.open(temp,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {}
            });
            assertTrue(Thread.currentThread().isInterrupted());
        } finally {Thread.interrupted();}
        try(Inputs input=Inputs.open(temp,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            assertTrue(input.summary().limitations().isEmpty());
        }
    }
    @Test void individualClassInputsKeepTheirInternalNamesAndDependencyRoles() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("client/Use.java","package client; public class Use {public static String run(){return dep.Helper.value();}}",
            "dep/Helper.java","package dep; public class Helper {public static String value(){return \"ok\";}}"));
        Path target=Files.copy(classes.resolve("client/Use.class"),temp.resolve("standalone.CLASS"));
        Path dependency=classes.resolve("dep/Helper.class");
        try(Inputs input=Inputs.open(target,List.of(dependency),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            assertEquals(Inputs.Role.TARGET,input.lookup("client/Use").value().orElseThrow().scope());
            assertEquals(Inputs.Role.DEPENDENCY,input.lookup("dep/Helper").value().orElseThrow().scope());
            Program program=new Program(input,20_000);
            assertTrue(program.lookup(new Program.MethodId("dep/Helper","value","()Ljava/lang/String;")).value().orElseThrow().hasBody());
            assertEquals("client/Use",program.targets().get(0).name());
            assertEquals(dependency.toRealPath().toString(),input.lookup("dep/Helper").value().orElseThrow().artifact().location());
        }
    }
    private byte[] archive(Map<String,byte[]> entries) throws IOException {
        ByteArrayOutputStream bytes=new ByteArrayOutputStream();
        try(ZipOutputStream out=new ZipOutputStream(bytes)) {
            for(var entry:entries.entrySet()) {
                ZipEntry file=new ZipEntry(entry.getKey());file.setMethod(ZipEntry.STORED);file.setSize(entry.getValue().length);
                CRC32 crc=new CRC32();crc.update(entry.getValue());file.setCrc(crc.getValue());out.putNextEntry(file);out.write(entry.getValue());out.closeEntry();
            }
        }
        return bytes.toByteArray();
    }

    @Test void directoryEntryDataCountsAgainstTheMemberByteLimit() throws Exception {
        Path jar = temp.resolve("directory-entry.jar");
        Files.write(jar, archive(Map.of("resources/", new byte[32])));
        var limits = new Inputs.Limits(1024, 10, 10, 0, 16);
        try (Inputs input = Inputs.open(jar, List.of(), Path.of(System.getProperty("java.home")), limits)) {
            assertEquals(List.of("input member byte budget: 16"), input.summary().limitations());
        }
    }

    @Test void malformedMethodBodiesRetainTheClassfileLocation() throws Exception {
        Path classes = BytecodeFixtures.compile(temp, 17, Map.of("RecordBody.java",
                "public class RecordBody { public static String label() { return \"record\"; } }"));
        Path file = classes.resolve("RecordBody.class");
        byte[] bytes = Files.readAllBytes(file);
        int constant = -1;
        for (int at = 0; at + 6 < bytes.length; at++) {
            if (bytes[at] == 0 && bytes[at + 1] == 0 && bytes[at + 2] == 0 && bytes[at + 3] == 3
                    && bytes[at + 4] == 18 && bytes[at + 6] == (byte) 176) {
                constant = at + 5;
                break;
            }
        }
        assertTrue(constant >= 0, "fixture must contain ldc followed by areturn");
        bytes[constant] = 0;
        Files.write(file, bytes);
        try (Inputs inputs = Inputs.open(classes, List.of(), Path.of(System.getProperty("java.home")), Inputs.Limits.defaults())) {
            Program program = new Program(inputs, 20_000);
            var method = new Program.MethodId("RecordBody", "label", "()Ljava/lang/String;");
            assertTrue(program.declaration(method).value().isPresent());
            Program.Failure failure = assertThrows(Program.Failure.class, () -> io.just.program.Bytecode.query(program, method, 0, 10));
            assertTrue(failure.getMessage().contains("!/RecordBody.class"), failure.toString());
            assertNotNull(failure.getCause());
        }
    }

    @Test void nestedDependenciesCannotConsumeTheBudgetBeforeTheEnclosingApplication() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Application.java","public class Application {public static void run(){}}","Library.java","public class Library {}"));
        byte[] application=Files.readAllBytes(classes.resolve("Application.class"));
        byte[] library=archive(Map.of("Library.class",Files.readAllBytes(classes.resolve("Library.class"))));
        for(boolean libraryFirst:List.of(false,true)) {
            LinkedHashMap<String,byte[]> entries=new LinkedHashMap<>();
            if(libraryFirst)entries.put("BOOT-INF/lib/library.jar",library);
            entries.put("BOOT-INF/classes/Application.class",application);
            if(!libraryFirst)entries.put("BOOT-INF/lib/library.jar",library);
            Path jar=temp.resolve("application-"+libraryFirst+".jar");Files.write(jar,archive(entries));
            try(Inputs input=Inputs.open(jar,List.of(),Path.of(System.getProperty("java.home")),new Inputs.Limits(1<<20,100,1,3,1<<20))) {
                assertEquals(List.of("Application"),input.targetClasses().stream().map(Inputs.ClassData::name).toList());
                assertFalse(input.summary().limitations().isEmpty());
                assertTrue(input.lookup("Library").truncated().isPresent());
            }
        }
    }
    @Test void discardedResourcesStillConsumeLimitsAndCorruptionIsNotReplacedBySelectionBudget() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("A.java","public class A {}","B.java","public class B {}"));
        byte[] a=Files.readAllBytes(classes.resolve("A.class")),b=Files.readAllBytes(classes.resolve("B.class"));
        LinkedHashMap<String,byte[]> entries=new LinkedHashMap<>();entries.put("A.class",a);entries.put("large.bin",new byte[8192]);
        Path bounded=temp.resolve("bounded.jar");Files.write(bounded,archive(entries));
        try(Inputs input=Inputs.open(bounded,List.of(),Path.of(System.getProperty("java.home")),new Inputs.Limits(1<<20,100,100,3,1024))) {
            assertEquals(1,input.targetClasses().size());assertTrue(input.summary().bytesRead()>a.length);assertFalse(input.summary().limitations().isEmpty());
        }
        byte[] marker="CORRUPT_RESOURCE_SENTINEL".getBytes(java.nio.charset.StandardCharsets.UTF_8);
        entries.clear();entries.put("A.class",a);entries.put("nested.jar",archive(Map.of("B.class",b)));entries.put("broken.bin",marker);
        byte[] broken=archive(entries);int offset=-1;
        outer:for(int i=0;i<=broken.length-marker.length;i++) {
            for(int j=0;j<marker.length;j++)if(broken[i+j]!=marker[j])continue outer;offset=i;break;
        }
        assertTrue(offset>=0);broken[offset]^=1;Path corrupt=temp.resolve("corrupt.jar");Files.write(corrupt,broken);
        IOException failure=assertThrows(IOException.class,() -> Inputs.open(corrupt,List.of(),Path.of(System.getProperty("java.home")),new Inputs.Limits(1<<20,100,1,3,1<<20)));
        assertTrue(failure.getMessage().contains("corrupt.jar"));
        assertTrue(failure.getMessage().contains("CRC"),failure.toString());assertNotNull(failure.getCause());
    }
    @Test void malformedStaticShapesIncludeTheFileAndRealJsonPosition() throws Exception {
        for(var example:Map.of("[]","/", "{\"source\":\"x\",\"basis\":\"BINDING\",\"entry\":null,\"objects\":[]}","/entry",
                "{\"source\":\"x\",\"basis\":\"INVALID\",\"entry\":{\"owner\":\"A\",\"name\":\"run\",\"descriptor\":\"()V\",\"arguments\":[]},\"objects\":[]}","/basis",
                "{\"source\":\"x\",\"basis\":\"BINDING\",\"entry\":{\"owner\":\"A\",\"name\":\"run\",\"descriptor\":\"()V\",\"arguments\":[[]]},\"objects\":[]}","/entry/arguments/0").entrySet()) {
            Path file=Files.createTempFile(temp,"invalid-",".json");Files.writeString(file,example.getKey());
            IOException failure=assertThrows(IOException.class,() -> StaticData.read(file));
            assertTrue(failure.getMessage().contains(file.toAbsolutePath().normalize().toString()));assertTrue(failure.getMessage().contains(example.getValue()),failure.toString());
        }
    }

    @Test void staticDataRejectsNonJsonSyntaxWithTheInputPath() throws Exception {
        Path file = temp.resolve("commented.json");
        Files.writeString(file, """
                /* a comment is not JSON */
                {"source":"fixture","basis":"REFERENCE","entry":{"owner":"Example","name":"run","descriptor":"()V","arguments":[]},"objects":[]}
                """);
        IOException failure = assertThrows(IOException.class, () -> StaticData.read(file));
        assertTrue(failure.getMessage().contains(file.toAbsolutePath().normalize().toString()), failure.toString());
        assertInstanceOf(com.google.gson.JsonParseException.class, failure.getCause());
    }

    @Test void staticObjectBudgetIsCheckedBeforeOpeningAnAttachment() throws Exception {
        Path file = temp.resolve("too-many-objects.json");
        String first = "{\"id\":\"attachment\",\"type\":\"[B\",\"classfile\":\"missing.class\"}";
        Files.writeString(file, """
                {"source":"fixture","basis":"REFERENCE","entry":{"owner":"Example","name":"run","descriptor":"()V","arguments":[]},"objects":[
                """ + first + ",{\"id\":\"item\",\"type\":\"Example\"}".repeat(256) + "]}");
        IOException failure = assertThrows(IOException.class, () -> StaticData.read(file));
        assertTrue(failure.getMessage().contains("/objects"), failure.toString());
        assertTrue(failure.getMessage().contains("static object budget: 256"), failure.toString());
    }

    @Test void staticHeaderAndAssignmentBudgetAreCheckedBeforeOpeningAnAttachment() throws Exception {
        Path file = temp.resolve("invalid-static.json");
        String prefix = "{\"source\":\"fixture\",\"basis\":\"%s\",\"entry\":{\"owner\":\"Example\",\"name\":\"run\",\"descriptor\":\"()V\",\"arguments\":[]},\"objects\":[";
        String attachment = "{\"id\":\"file\",\"type\":\"[B\",\"classfile\":\"missing.class\"}";
        Files.writeString(file, prefix.formatted("INVALID") + attachment + "]}");
        IOException invalid = assertThrows(IOException.class, () -> StaticData.read(file));
        assertTrue(invalid.getMessage().contains("/basis"), invalid.toString());

        String fields = String.join(",", Collections.nCopies(2048,
                "{\"owner\":\"Example\",\"name\":\"value\",\"descriptor\":\"I\",\"value\":1}"));
        Files.writeString(file, prefix.formatted("REFERENCE") + attachment + ",{\"id\":\"values\",\"type\":\"Example\",\"fields\":[" + fields + "]}]}");
        IOException limited = assertThrows(IOException.class, () -> StaticData.read(file));
        assertTrue(limited.getMessage().contains("static assignment budget: 2048"), limited.toString());
    }
    @Test void staticAssignmentsPointAtNumericObjectFieldAndElementItems() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Located.java","public class Located {public String name;public static void run(Located value,Object[] array){}}"));
        Path file=temp.resolve("locations.json");Files.writeString(file,"""
                {"source":"positions fixture","basis":"BINDING","entry":{"owner":"Located","name":"run","descriptor":"(LLocated;[Ljava/lang/Object;)V","arguments":[{"ref":"named/id"},{"ref":"array"}]},"objects":[{"id":"named/id","type":"Located","fields":[{"owner":"Located","name":"name","descriptor":"Ljava/lang/String;","value":"name"}]},{"id":"array","type":"[Ljava/lang/Object;","elements":["element"]}]}
                """);
        StaticData data=StaticData.read(file);assertEquals("/objects/0",data.nodes().get(0).pointer());assertEquals("/objects/0/fields/0",data.nodes().get(0).fields().get(0).pointer());
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            var result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Located","run","(LLocated;[Ljava/lang/Object;)V")),Optional.of(data));
            Set<String> sources=new HashSet<>();for(var r:result.relations())if(r.kind()==Kind.INPUT_BINDING)sources.add(r.site().source());
            assertTrue(sources.contains(data.location()+"#/objects/0/fields/0/value"));
            assertTrue(sources.contains(data.location()+"#/objects/1/elements/0"));assertTrue(sources.contains(data.location()+"#/objects/1/elements"));
            Files.writeString(file,Files.readString(file).replace("\"value\":\"name\"","\"value\":0"));
            StaticData incompatible=StaticData.read(file);
            InvalidInput failure=assertThrows(InvalidInput.class,() -> new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Located","run","(LLocated;[Ljava/lang/Object;)V")),Optional.of(incompatible)));
            assertTrue(failure.getMessage().contains(data.location()+"#/objects/0/fields/0/value"));
        }
    }
    @Test void relativeAndAbsoluteClassfilePathsReuseTheSameAttachment() throws Exception {
        Path manifests = Files.createDirectory(temp.resolve("输入 清单"));
        Path file = manifests.resolve("facts.json"), asset = temp.resolve("External.class");
        byte[] bytes = new byte[600 * 1024];
        ByteBuffer.wrap(bytes).putInt(0xcafebabe);
        Files.write(asset, bytes);
        Files.writeString(file, """
                {"source":"attachment fixture","basis":"REFERENCE","entry":{"owner":"Example","name":"run","descriptor":"()V","arguments":[]},
                 "objects":[{"id":"relative","type":"[B","classfile":"../External.class"},
                            {"id":"absolute","type":"[B","classfile":%s}]}
                """.formatted(new com.google.gson.Gson().toJson(asset.toString())));

        StaticData data = StaticData.read(file);
        assertEquals(file.toString(), data.location());
        for (var node : data.nodes()) {
            var classfile = node.classfile().orElseThrow();
            assertEquals(asset.toString(), classfile.location());
            assertArrayEquals(bytes, classfile.bytes());
        }
    }

    @Test void classfileAssetsRejectWrongShapesMissingFilesAndInvalidOrOversizedContent() throws Exception {
        Path file=temp.resolve("classfile.json");Files.write(temp.resolve("invalid.class"),new byte[12]);
        Files.write(temp.resolve("oversized.class"),new byte[(1<<20)+1]);
        for(Map<String,Object> node:List.<Map<String,Object>>of(
                Map.of("id","code","type","java/lang/Object","classfile","invalid.class"),
                Map.of("id","code","type","[B","elements",List.of(1),"classfile","invalid.class"),
                Map.of("id","code","type","[B","classfile","invalid.class"),
                Map.of("id","code","type","[B","classfile","oversized.class"),
                Map.of("id","code","type","[B","classfile","missing.class"))) {
            Files.writeString(file,new com.google.gson.Gson().toJson(Map.of("source","invalid asset fixture","basis","BINDING",
                    "entry",Map.of("owner","AssetBoundary","name","run","descriptor","([B)V","arguments",List.of(Map.of("ref","code"))),"objects",List.of(node))));
            IOException failure=assertThrows(IOException.class,() -> StaticData.read(file));
            assertTrue(failure.getMessage().contains(node.get("classfile").equals("missing.class")?"missing.class":"/objects/0/classfile"),failure.toString());
        }
    }
}
