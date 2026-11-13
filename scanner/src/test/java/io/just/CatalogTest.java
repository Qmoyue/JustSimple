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

class CatalogTest {
    @TempDir Path temp;
    @Test void thirdPartyPlatformLikePackagesRemainRenameableWhileJdkCallsKeepTheirIdentity()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of(
                "com/sun/vendor/Adapter.java","package com.sun.vendor; public class Adapter { public Object apply(Object value){return value;} }",
                "example/Renamed.java","package example; public class Renamed { public Object apply(Object value){return value;} }",
                "Use.java","""
                    public class Use {
                      public static Object historical(com.sun.vendor.Adapter target,Object value){return target.apply(value);}
                      public static Object renamed(example.Renamed target,Object value){return target.apply(value);}
                      public static String platform(com.sun.net.httpserver.HttpExchange exchange){return exchange.getRequestMethod();}
                    }
                    """));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);
            MethodId historical=new MethodId("Use","historical","(Lcom/sun/vendor/Adapter;Ljava/lang/Object;)Ljava/lang/Object;");
            MethodId renamed=new MethodId("Use","renamed","(Lexample/Renamed;Ljava/lang/Object;)Ljava/lang/Object;");
            Catalog catalog=Catalog.read(ReferenceFixtures.write(temp.resolve("platform-role.json"),program,historical));
            assertFalse(catalog.hints(program,Set.of(renamed)).value().orElseThrow().isEmpty(),"a dependency in a platform-like namespace is still a role");
            MethodId platform=new MethodId("Use","platform","(Lcom/sun/net/httpserver/HttpExchange;)Ljava/lang/String;");
            var call=program.facts(platform).actions().stream().filter(Program.Call.class::isInstance).map(Program.Call.class::cast).findFirst().orElseThrow();
            var before=inputs.summary();
            assertEquals("com/sun/net/httpserver/HttpExchange",CallShape.of(program,call).target().owner());
            assertEquals(before.bytesRead(),inputs.summary().bytesRead(),"class ownership uses archive metadata, not the scan input budget");
            assertEquals(before.entriesRead(),inputs.summary().entriesRead());
        }
    }
    @Test void packagedReferencesExpandStructuralFactsWithoutRawInstructionsOrEvaluationAnswers()throws Exception {
        Catalog catalog=Catalog.builtin();int relations=0;var json=new com.google.gson.Gson();
        for(Catalog.Entry entry:catalog.entries()) {
            var material=com.google.gson.JsonParser.parseString(catalog.material(entry.id())).getAsJsonObject();
            assertEquals(entry.id(),material.get("id").getAsString());assertPublishedReference(material);
            for(var item:material.getAsJsonArray("relations")) {
                var pattern=json.fromJson(item.getAsJsonObject().get("pattern"),CallShape.Pattern.class);
                assertTrue(pattern.useful());assertFalse(pattern.operands().isEmpty());relations++;
            }
        }
        assertTrue(relations>0,"local knowledge queries must expose source relations and conditions");
    }
    @Test void expandingSharedKnowledgeIsBoundedWithoutPoisoningASmallerQuery()throws Exception {
        var pattern=new CallShape.Pattern(new CallShape.Signature("java/lang/Class","forName","(Ljava/lang/String;)Ljava/lang/Class;"),
                org.objectweb.asm.Opcodes.INVOKESTATIC,List.of(
                new CallShape.Operand(-1,-1,List.of(new CallShape.Step(CallShape.SourceKind.ABSENT,"",-1,List.of()))),
                new CallShape.Operand(0,0,List.of(new CallShape.Step(CallShape.SourceKind.PARAMETER,"L"+"Role".repeat(2048)+";",0,List.of())))),
                List.of(new CallShape.Destination(CallShape.UseKind.RETURNED,-1,List.of())),Set.of());
        var json=new com.google.gson.Gson();var root=new com.google.gson.JsonObject();root.addProperty("schema","just.local-reference/v1");
        root.add("chains",new com.google.gson.JsonArray());root.add("bytecodeObservations",new com.google.gson.JsonArray());
        var patterns=new com.google.gson.JsonArray();patterns.add(json.toJsonTree(pattern));root.add("patterns",patterns);
        var fragments=new com.google.gson.JsonArray();root.add("fragments",fragments);
        for(String id:List.of("large","small")) {
            var entry=new com.google.gson.JsonObject();entry.addProperty("id",id);entry.addProperty("kind","generic");
            var relations=new com.google.gson.JsonArray();for(int i=0;i<(id.equals("large")?4096:1);i++)relations.add(0);
            entry.add("relations",relations);fragments.add(entry);
        }
        Path file=temp.resolve("shared.json");Files.writeString(file,root.toString());Catalog catalog=Catalog.read(file);
        var failure=assertThrows(java.io.IOException.class,() -> catalog.material("large"));
        assertTrue(failure.getMessage().contains("output exceeds"));assertTrue(failure.getMessage().contains("large"));
        assertEquals(pattern,json.fromJson(com.google.gson.JsonParser.parseString(catalog.material("small")).getAsJsonObject()
                .getAsJsonArray("relations").get(0).getAsJsonObject().get("pattern"),CallShape.Pattern.class));
    }
    private static void assertPublishedReference(com.google.gson.JsonElement value) {
        if(value.isJsonObject())for(var field:value.getAsJsonObject().entrySet()) {
            assertFalse(Set.of("instruction","evaluationLabel","aliases","review").contains(field.getKey()),field.getKey());
            assertPublishedReference(field.getValue());
        }
        else if(value.isJsonArray())for(var item:value.getAsJsonArray())assertPublishedReference(item);
    }
    @Test void localGuidanceDistinguishesMissingMetadataFromAnAbsentMember()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Known.java","public class Known { public static void present() {} }"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);
            for(Catalog catalog:List.of(Catalog.empty(),Catalog.builtin())) {
                Mechanisms mechanisms=new Mechanisms(program,catalog);
                var missing=mechanisms.hints(new MethodId("Missing","run","()V"));
                assertTrue(missing.value().orElseThrow().isEmpty());
                assertTrue(missing.pending().stream().anyMatch(issue -> issue.cause()==QueryCause.MISSING_DEPENDENCY));
                assertEquals(missing.pending(),catalog.hints(program,Set.of(new MethodId("Missing","run","()V"))).pending());
                var absent=mechanisms.hints(new MethodId("Known","absent","()V"));
                assertTrue(absent.value().orElseThrow().isEmpty());assertTrue(absent.pending().isEmpty());
                var empty=mechanisms.hints(new MethodId("Known","present","()V"));
                assertTrue(empty.value().orElseThrow().isEmpty());assertTrue(empty.pending().isEmpty());
            }
        }
    }
    @Test void renamedStructureMatchesAndSameApiWithDifferentDataFlowDoesNotBorrowIt()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Shapes.java","""
            public class Shapes {
              public static Object historical(Object receiver,String name,Object value)throws Exception {return receiver.getClass().getMethod(name,String.class).invoke(receiver,value);}
              public static Object renamed(Object receiver,String name,Object value)throws Exception {return receiver.getClass().getMethod(name,String.class).invoke(receiver,value);}
              public static Object unrelated(Object receiver,java.lang.reflect.Method method,Object value)throws Exception {receiver.getClass().getMethod("toString");return method.invoke(new Object(),value);}
            }
            """));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);MethodId historical=new MethodId("Shapes","historical","(Ljava/lang/Object;Ljava/lang/String;Ljava/lang/Object;)Ljava/lang/Object;");
            Path file=ReferenceFixtures.write(temp.resolve("knowledge.json"),program,historical);
            var nullable=com.google.gson.JsonParser.parseString(Files.readString(file)).getAsJsonObject();
            nullable.getAsJsonArray("fragments").get(0).getAsJsonObject().add("referenceHops",com.google.gson.JsonNull.INSTANCE);
            Files.writeString(file,nullable.toString());Catalog catalog=Catalog.read(file);
            MethodId renamed=new MethodId("Shapes","renamed",historical.descriptor());MethodId unrelated=new MethodId("Shapes","unrelated","(Ljava/lang/Object;Ljava/lang/reflect/Method;Ljava/lang/Object;)Ljava/lang/Object;");
            Mechanisms mechanisms=new Mechanisms(program,catalog);
            var hints=mechanisms.hints(renamed).value().orElseThrow().stream().filter(h -> h.mechanism().equals("reference:source-relations")).toList();
            assertFalse(hints.isEmpty());assertTrue(hints.stream().flatMap(h -> h.requirements().stream()).allMatch(r -> r.site().method().equals(renamed)));
            assertTrue(mechanisms.hints(unrelated).value().orElseThrow().stream().filter(h -> h.mechanism().startsWith("reference:")).flatMap(h -> h.requirements().stream()).noneMatch(r -> r.pattern().target().owner().equals("java/lang/reflect/Method")),"an unrelated Method parameter cannot borrow the lookup result relationship");
            byte[] bytes=Files.readAllBytes(classes.resolve("Shapes.class"));int loader=program.define(new Object(),bytes,bytes,0,bytes.length,null).value().orElseThrow().loader();
            var defined=new MethodId("Shapes","renamed",historical.descriptor(),loader);
            assertTrue(mechanisms.hints(defined).value().orElseThrow().stream().flatMap(h -> h.requirements().stream()).allMatch(r -> r.site().method().loader()==loader));
            assertTrue(com.google.gson.JsonParser.parseString(catalog.material("source-relations")).getAsJsonObject().get("referenceHops").isJsonNull());
            var encoded=com.google.gson.JsonParser.parseString(Files.readString(file)).getAsJsonObject();
            var patterns=new com.google.gson.JsonArray();var relations=encoded.getAsJsonArray("fragments").get(0).getAsJsonObject().getAsJsonArray("relations");
            for(int i=0;i<relations.size();i++) {var relation=relations.get(i).getAsJsonObject();patterns.add(relation.get("pattern"));relations.set(i,new com.google.gson.JsonPrimitive(i));}
            Path material=temp.resolve("material.json");Files.copy(file,material);encoded.addProperty("referenceMaterial","material.json");ReferenceFixtures.encode(encoded,patterns);Files.writeString(file,encoded.toString());
            Catalog packed=Catalog.read(file);
            var packedHints=new Mechanisms(program,packed).hints(renamed).value().orElseThrow().stream().filter(h -> h.mechanism().equals("reference:source-relations")).toList();
            assertEquals(hints.stream().map(Mechanisms.Hint::requirements).toList(),packedHints.stream().map(Mechanisms.Hint::requirements).toList());
            assertTrue(packedHints.stream().flatMap(h -> h.references().stream()).allMatch(r -> r.location().startsWith(material.toString())));
            assertTrue(packed.material("source-relations").contains("relations"));
            var raw=com.google.gson.JsonParser.parseString(Files.readString(material)).getAsJsonObject();var rawRelations=raw.getAsJsonArray("fragments").get(0).getAsJsonObject().getAsJsonArray("relations");
            int alternative=rawRelations.size();rawRelations.add(rawRelations.get(0).deepCopy());Files.writeString(material,raw.toString());
            var repeated=new com.google.gson.JsonObject();repeated.addProperty("pattern",0);repeated.addProperty("reference",0);relations.add(repeated);
            var another=repeated.deepCopy();another.addProperty("reference",alternative);relations.add(another);Files.writeString(file,encoded.toString());
            var distinct=new Mechanisms(program,Catalog.read(file)).hints(renamed).value().orElseThrow().stream().filter(h -> h.mechanism().equals("reference:source-relations")).toList();
            assertEquals(packedHints.stream().map(Mechanisms.Hint::requirements).toList(),distinct.stream().map(Mechanisms.Hint::requirements).toList());
            assertEquals(packedHints.stream().mapToLong(h -> h.references().size()).sum()+1,distinct.stream().mapToLong(h -> h.references().size()).sum(),"exact duplicates do not add weight; another reference location remains navigable");
            Files.writeString(material,"{}");assertThrows(java.io.IOException.class,() -> Catalog.read(file).material("source-relations"));Files.writeString(material,raw.toString());
            var definition=encoded.getAsJsonArray("encodedPatterns").get(0).getAsJsonArray();var opcode=definition.get(1);definition.set(1,new com.google.gson.JsonPrimitive(0));Files.writeString(file,encoded.toString());
            assertTrue(assertThrows(java.io.IOException.class,() -> Catalog.read(file)).getMessage().contains("/encodedPatterns/0"));definition.set(1,opcode);
            relations.set(0,new com.google.gson.JsonPrimitive(patterns.size()));Files.writeString(file,encoded.toString());
            assertTrue(assertThrows(java.io.IOException.class,() -> Catalog.read(file)).getMessage().contains("/fragments/0/relations/0"));
            Files.writeString(file,"{broken");assertThrows(java.io.IOException.class,() -> Catalog.read(file));
            Files.writeString(file,"{\"schema\":\"just.local-reference/v1\",\"chains\":[],\"bytecodeObservations\":[],\"fragments\":[{\"id\":\"bad\",\"kind\":\"generic\",\"relations\":[{\"pattern\":{}}]}]}");
            var error=assertThrows(java.io.IOException.class,() -> Catalog.read(file));assertTrue(error.getMessage().contains("/fragments/0/relations/0"));
        }
    }
    @Test void defaultScanUsesPackagedRelationsWithoutAnExternalKnowledgeFile()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Embedded.java","""
            public class Embedded {
              static String display;
              public static void scan(java.io.ObjectInputStream input)throws Exception {
                java.io.ObjectInputStream.GetField fields=input.readFields();
                Object value=fields.get("content",null);
                if(value!=null)display=value.toString();
              }
            }
            """));
        for(boolean enabled:List.of(true,false)) {
            Path output=temp.resolve(enabled?"default":"disabled");
            List<String> args=new ArrayList<>(List.of("--input",classes.toString(),"--jdk-home",System.getProperty("java.home"),"--mode","component",
                    "--entry","Embedded#scan(Ljava/io/ObjectInputStream;)V","--output",output.toString()));
            if(!enabled)args.add("--no-guidance");
            var messages=new java.io.ByteArrayOutputStream();int code;
            try(var stream=new java.io.PrintStream(messages)) {code=io.just.app.Main.run(args.toArray(String[]::new),stream,stream);}
            assertTrue(code==0 || code==3,messages.toString());
            var report=com.google.gson.JsonParser.parseString(Files.readString(output.resolve("report.json"))).getAsJsonObject();
            boolean matched=false;
            for(var hint:report.getAsJsonArray("hints")) {
                boolean stringification=false;
                for(var requirement:hint.getAsJsonObject().getAsJsonArray("requirements")) {
                    var target=requirement.getAsJsonObject().getAsJsonObject("pattern").getAsJsonObject("target");
                    stringification|=target.get("owner").getAsString().equals("java/lang/Object") && target.get("name").getAsString().equals("toString");
                }
                if(!stringification)continue;
                for(var reference:hint.getAsJsonObject().getAsJsonArray("references")) {
                var item=reference.getAsJsonObject();
                    matched=true;assertTrue(item.get("location").getAsString().startsWith("classpath:/io/just/knowledge/reference-knowledge.json#"));
                }
            }
            assertEquals(enabled,matched,"built-in structure must guide the default scan but not disabled guidance");
        }
    }
}
