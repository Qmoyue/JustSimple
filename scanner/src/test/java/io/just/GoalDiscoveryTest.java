package io.just;

import io.just.analysis.*;
import io.just.analysis.ScanResult.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

/** Compile and inspect only: these targets are never loaded or invoked. */
class GoalDiscoveryTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String method,String descriptor) throws Exception {
        return scan(classes,List.of(),method,descriptor);
    }
    private ScanResult scan(Path classes,List<Path> dependencies,String method,String descriptor) throws Exception {
        try(Inputs input=Inputs.open(classes,dependencies,Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Goals",method,descriptor)));
        }
    }
    @Test void unknownArgumentsOnAnExplicitDependencyKeepOverloadsAndRejectWrongKnownSignature() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
                public class Goals {
                  public static void run(String name,Object[] args)throws Exception {Class.forName("dep.Member").getMethod(name,new Class[]{String.class}).invoke(null,args);}
                  public static void wrong(Object[] args)throws Exception {Class.forName("dep.Member").getMethod("accept",new Class[]{Integer.class}).invoke(null,args);}
                }
                ""","dep/Member.java","package dep; public class Member {public static void accept(String value){}public static void accept(int value){}}"));
        Path dep=java.nio.file.Files.createDirectory(temp.resolve("dependency"));java.nio.file.Files.createDirectory(dep.resolve("dep"));
        java.nio.file.Files.move(classes.resolve("dep/Member.class"),dep.resolve("dep/Member.class"));
        ScanResult result=scan(classes,List.of(dep),"run","(Ljava/lang/String;[Ljava/lang/Object;)V");
        assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.owner().equals("dep/Member") && t.descriptor().equals("(Ljava/lang/String;)V")).isPresent()));
        assertTrue(result.relations().stream().noneMatch(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.descriptor().equals("(I)V")).isPresent()));
        ScanResult wrong=scan(classes,List.of(dep),"wrong","([Ljava/lang/Object;)V");
        assertTrue(wrong.relations().stream().noneMatch(r -> r.kind()==Kind.REFLECTION && r.target().isPresent()));
    }
    @Test void nativeKeyCandidateCarriesSourceFieldsAndArgumentsWithoutAProvidedObjectGraph() throws Exception {
        String source="""
                public class Goals {
                  public static class Token implements java.io.Serializable {
                    public Object target;public String name;public Class<?>[] signature;public Object[] args;
                    public int hashCode(){try{target.getClass().getMethod(name,signature).invoke(target,args);}catch(Exception e){}return 1;}
                  }
                  public static final class Receiver implements java.io.Serializable {
                    public void accept(String value)throws Exception {Runtime.getRuntime().exec(value);}
                  }
                  public static void run(java.io.ObjectInputStream in)throws Exception {in.readObject();}
                }
                """;
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java",source));
        ScanResult result=scan(classes,"run","(Ljava/io/ObjectInputStream;)V");
        var impact=result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).findFirst().orElseThrow();
        assertTrue(impact.path().stream().map(result.relations()::get).anyMatch(r -> r.kind()==Kind.CONTAINER_CALLBACK));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.source().filter(s -> s.parameterSlot()==0 && s.path().stream().anyMatch(SerializedKey.class::isInstance)
                && s.path().stream().anyMatch(p -> p instanceof SerializedField f && f.field().name().equals("name"))).isPresent()));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.source().filter(s -> s.path().stream().anyMatch(p -> p instanceof SerializedField f && f.field().name().equals("args")) && s.path().contains(new Index(0))).isPresent()));
        assertTrue(result.staticData().isEmpty());
        for(String negative:List.of(source.replace("Receiver implements java.io.Serializable","Receiver"),source.replace("public String name","public transient String name"))) {
            ScanResult broken=scan(BytecodeFixtures.compile(temp,8,Map.of("Goals.java",negative)),"run","(Ljava/io/ObjectInputStream;)V");
            assertTrue(broken.relations().stream().noneMatch(r -> r.kind()==Kind.IMPACT && r.target().filter(t -> t.owner().equals("java/lang/Runtime")).isPresent()),"nonserializable final receiver and default-null transient name must not become source bindings");
        }
    }
    @Test void unknownClassNameAndArraysRetainFiniteGoalCandidatesAndPositionedRequirements() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
                public class Goals {
                  public static void run(Class<?> owner,String name,Class<?>[] types,Object receiver,Object[] args)throws Exception {
                    owner.getMethod(name,types).invoke(receiver,args);
                  }
                  public static void absent(Class<?> owner,Class<?>[] types,Object receiver,Object[] args)throws Exception {
                    owner.getMethod("noSuchMember",types).invoke(receiver,args);
                  }
                }
                ""","Noise.java","public class Noise {"+java.util.stream.IntStream.range(0,80).mapToObj(i -> "public static void member"+i+"(){}").collect(java.util.stream.Collectors.joining())+"}"));
        ScanResult result=scan(classes,"run","(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/Class;Ljava/lang/Object;[Ljava/lang/Object;)V");
        assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.target().orElseThrow().owner().equals("java/lang/Runtime")));
        assertEquals(6,result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.target().stream()).filter(t -> t.owner().equals("java/lang/Runtime") && t.name().equals("exec")).map(Program.MethodId::descriptor).distinct().count(),"all finite overload goals get a turn before unrelated member families exhaust target selection");

        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.LOOKUP_TYPE));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.source().filter(s -> s.parameterSlot()==4 && s.path().contains(new Index(0))).isPresent()));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().slot().filter(Length.class::isInstance).isPresent()));
        ScanResult absent=scan(classes,"absent","(Ljava/lang/Class;[Ljava/lang/Class;Ljava/lang/Object;[Ljava/lang/Object;)V");
        assertTrue(absent.relations().stream().noneMatch(r -> r.kind()==Kind.IMPACT));
    }
    @Test void goalQueryKeepsAvailableMembersAndReportsMissingAndBudgetFrontiers() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","public class Goals {public static void run(){}}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);
            Set<Program.MethodId> goals=new LinkedHashSet<>(List.of(new Program.MethodId("Goals","run","()V"),new Program.MethodId("missing/Type","absent","()V")));
            var cut=program.candidateMethods(goals,1);assertEquals(1,cut.value().orElseThrow().size());
            assertTrue(cut.pending().stream().anyMatch(p -> p.cause()==Program.QueryCause.BUDGET));
            var missing=program.candidateMethods(goals,8);assertEquals(1,missing.value().orElseThrow().size());
            assertTrue(missing.pending().stream().anyMatch(p -> p.cause()==Program.QueryCause.MISSING_DEPENDENCY));
        }
    }
    @Test void nativeHooksRetainAlternativeContentSourcesAndSourceBudgetIsExplicit() throws Exception {
        String wrappers="";
        for(int i=0;i<18;i++)wrappers+="current=new java.io.ObjectInputStream(current);";
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
                public class Goals {
                  static class Hook implements java.io.Serializable {
                    Object receiver;String name;Class<?>[] signature;Object[] arguments;
                    private void readObject(java.io.ObjectInputStream in)throws Exception {
                      in.defaultReadObject();receiver.getClass().getMethod(name,signature).invoke(receiver,arguments);
                    }
                  }
                  public static final class Receiver implements java.io.Serializable {
                    public void accept(String value)throws Exception {Runtime.getRuntime().exec(value);}
                  }
                  public static void run(boolean choice,String one,String two)throws Exception {
                    byte[] data=java.util.Base64.getDecoder().decode(choice?one:two);
                    new java.io.ObjectInputStream(new java.io.ByteArrayInputStream(data)).readObject();
                  }
                  public static void deep(String input)throws Exception {
                    java.io.InputStream current=new java.io.ByteArrayInputStream(java.util.Base64.getDecoder().decode(input));
                    WRAPPERS
                    new java.io.ObjectInputStream(current).readObject();
                  }
                }
                """.replace("WRAPPERS",wrappers)));
        ScanResult result=scan(classes,"run","(ZLjava/lang/String;Ljava/lang/String;)V");
        assertTrue(result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT));
        Set<Integer> sourceSlots=result.inputRequirements().stream().filter(r -> r.source().filter(s -> s.path().stream().anyMatch(SerializedField.class::isInstance)).isPresent()).map(r -> r.source().orElseThrow().parameterSlot()).collect(java.util.stream.Collectors.toSet());
        assertEquals(Set.of(1,2),sourceSlots,"both actual content alternatives must remain traceable through the native hook");
        ScanResult deep=scan(classes,"deep","(Ljava/lang/String;)V");
        assertEquals(Execution.TRUNCATED,deep.execution());
        assertTrue(deep.limitations().stream().anyMatch(s -> s.contains("content source frontier")));
        assertTrue(deep.relations().stream().flatMap(r -> r.supports().stream().flatMap(s -> s.gaps().stream())).anyMatch(g -> g.kind()==GapKind.BUDGET && g.detail().contains("content source")));
    }
    @Test void reflectedHelperForwardsItsActualTupleAndConstantReturnBreaksTheContinuation() throws Exception {
        for(boolean forward:List.of(true,false)) {
            Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
                    public class Goals {
                      public static Object relay(Object value){return RETURN;}
                      public static void run(String command)throws Exception {
                        java.lang.reflect.Method selected=Runtime.class.getMethod("exec",String.class);
                        java.lang.reflect.Method relay=Goals.class.getMethod("relay",Object.class);
                        Object value=relay.invoke(null,new Object[]{selected});
                        ((java.lang.reflect.Method)value).invoke(Runtime.getRuntime(),new Object[]{command});
                      }
                    }
                    """.replace("RETURN",forward?"value":"null")));
            ScanResult result=scan(classes,"run","(Ljava/lang/String;)V");
            assertEquals(forward,result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT));
            if(forward)assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.arguments().stream()).anyMatch(a -> Values.source(a).filter(s -> s.parameterSlot()==0).isPresent()));
        }
    }
    @Test void opaqueObjectReturnKeepsItsOwnRuntimeClassBindingWithoutBecomingAnInputParameter() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
                public class Goals {
                  public static native Object opaque();
                  public static void run(Class<?>[] types,Object[] args)throws Exception {
                    Object value=opaque();value.getClass().getMethod("exec",types).invoke(value,args);
                  }
                  public static void wrong()throws Exception {
                    Object value=opaque();value.getClass().getMethod("exec",Integer.class).invoke(value,new Object[]{1});
                  }
                  public static void fixed()throws Exception {
                    Object value="fixed";value.getClass().getMethod("exec",String.class).invoke(value,new Object[]{"argument"});
                  }
                  public static void swapped(Class<?>[] types,Object[] args)throws Exception {
                    Object value=opaque();value.getClass().getMethod("exec",types).invoke("fixed",args);
                  }
                }
                """));
        ScanResult result=scan(classes,"run","([Ljava/lang/Class;[Ljava/lang/Object;)V");
        var impacts=result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT && result.relations().get(f.path().get(f.path().size()-1)).target().filter(t -> t.owner().equals("java/lang/Runtime")).isPresent()).toList();
        assertFalse(impacts.isEmpty(),"an actual opaque producer remains a conditional receiver, even without an external InputSource");
        assertTrue(impacts.stream().allMatch(f -> java.util.stream.Stream.concat(f.path().stream(),f.supportingRelations().stream()).map(result.relations()::get).flatMap(r -> r.target().stream()).anyMatch(t -> t.name().equals("opaque"))),"the chain retains the actual producing call");
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.RECEIVER_TYPE && r.source().isEmpty() && Values.location(r.needed().subject()).filter(ObjectSource.class::isInstance).isPresent()),"internal identity is a fact to resolve, not an invented controllable parameter");
        for(String entry:List.of("wrong","fixed"))assertTrue(scan(classes,entry,"()V").relations().stream().noneMatch(r -> r.kind()==Kind.IMPACT));
        assertTrue(scan(classes,"swapped","([Ljava/lang/Class;[Ljava/lang/Object;)V").relations().stream().noneMatch(r -> r.kind()==Kind.IMPACT),"metadata from one produced object cannot fill the incompatible receiver of another call");
        Path output=temp.resolve("opaque-report");io.just.report.Reports.write(result,output);
        var refs=com.google.gson.JsonParser.parseString(java.nio.file.Files.readString(output.resolve("report.json"))).getAsJsonObject().getAsJsonObject("references");
        boolean internalClass=false;
        for(var item:refs.getAsJsonArray("values")) {
            var value=item.getAsJsonObject();if(!value.get("kind").getAsString().equals("ClassValue"))continue;
            var source=value.getAsJsonObject("value").get("source");if(source.isJsonNull())continue;
            assertTrue(source.isJsonPrimitive(),"Class origins use the shared source table");
            internalClass|=refs.getAsJsonArray("sources").get(source.getAsInt()).getAsJsonObject().get("kind").getAsString().equals("ObjectSource");
        }
        assertTrue(internalClass,"the exported chain keeps its internal Class origin without expanding it into every value");
    }
    @Test void inheritedDefinitionApiRetainsTheBytecodeBoundaryWithoutInventingANewClassInitializer() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
                public class Goals {
                  static class Reader extends ClassLoader {
                    public Class<?> accept(byte[] input){return defineClass(null,input,0,input.length);}
                  }
                  public static void run(byte[] input){new Reader().accept(input);}
                }
                """));
        ScanResult result=scan(classes,"run","([B)V");
        assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.target().filter(t -> t.owner().equals("java/lang/ClassLoader") && t.name().equals("defineClass")).isPresent()));
        assertTrue(result.relations().stream().noneMatch(r -> r.kind()==Kind.IMPACT && r.target().filter(t -> t.owner().equals("java/lang/Runtime")).isPresent()));
    }
    @Test void ordinaryResourceHandlersDoNotCreateNewConditionIdentitiesAtEveryConsumer() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
                public class Goals {
                  public static String run() {
                    try(java.io.ByteArrayOutputStream bytes=new java.io.ByteArrayOutputStream();
                        java.io.ObjectOutputStream output=new java.io.ObjectOutputStream(bytes)) {
                      output.flush();return "done";
                    }catch(java.io.IOException error){return "fallback";}
                  }
                  public static void detached(){run();}
                }
                """));
        ScanResult result=scan(classes,"run","()Ljava/lang/String;");
        assertEquals(Execution.FINISHED,result.execution(),result.limitations().toString());
        assertTrue(result.relations().stream().flatMap(r -> r.supports().stream().flatMap(s -> s.gaps().stream())).filter(g -> g.detail().contains("normal flow requires")).allMatch(g -> g.site().method().owner().equals("Goals")));
        ScanResult ignored=scan(classes,"detached","()V");
        assertEquals(Execution.FINISHED,ignored.execution(),ignored.limitations().toString());
    }
    @Test void templateDefinitionRequiresTheActualPlatformPathAndRemainsConditional() throws Exception {
        String owner="com/sun/org/apache/xalan/internal/xsltc/trax/TemplatesImpl";
        String source="public class Goals {public static void run(Object template)throws Exception {Class.forName(\""+owner.replace('/','.')+"\").getMethod(\"newTransformer\",new Class[0]).invoke(template,new Object[0]);}}";
        for(boolean platform:List.of(true,false)) {
            Map<String,String> sources=new LinkedHashMap<>();sources.put("Goals.java",source);
            if(!platform)sources.put(owner+".java","package com.sun.org.apache.xalan.internal.xsltc.trax; public class TemplatesImpl {public Object newTransformer(){return null;}}");
            ScanResult result=scan(BytecodeFixtures.compile(temp,8,sources),"run","(Ljava/lang/Object;)V");
            var definitions=result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).toList();
            assertEquals(platform,!definitions.isEmpty(),result.limitations().toString());
            if(platform) {

                assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().descriptor().equals("[[B")));
                assertTrue(definitions.stream().allMatch(f -> f.gaps().stream().anyMatch(g -> g.kind()==GapKind.DEPLOYMENT)));
                assertTrue(result.relations().stream().noneMatch(r -> r.kind()==Kind.IMPACT && r.target().filter(t -> t.owner().equals("java/lang/Runtime")).isPresent()));
            }
        }
    }
    private Path application(boolean carry) throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
                @org.springframework.web.bind.annotation.RestController
                public class Goals {
                  public static class Frame implements java.io.Serializable {
                    Object receiver;String member;Class<?>[] signature;Object[] arguments;
                    public Object apply(Object current)throws Exception {
                      Object value=current.getClass().getMethod(member,signature).invoke(current,arguments);
                      return RETURN;
                    }
                    public int hashCode(){try{apply(receiver);}catch(Exception e){}return 1;}
                  }
                  public static class Playlist implements java.io.Serializable {
                    java.util.Map<Integer,Frame> frames;
                    public Object replay()throws Exception {
                      Object value=null;for(Frame frame:frames.values()) {
                        if(value==null)value=frame.receiver;
                        value=frame.apply(value);
                      }return value;
                    }
                  }
                  @org.springframework.web.bind.annotation.PostMapping
                  public void run(String encoded)throws Exception {
                    java.io.ObjectInputStream in=new java.io.ObjectInputStream(new java.io.ByteArrayInputStream(java.util.Base64.getDecoder().decode(encoded)));
                    in.readObject();
                  }
                  public static class Wrapper extends java.util.HashMap<Object,Object> {java.util.Map<Object,Object> delegate;public java.util.Collection<Object> values(){return delegate.values();}}
                  @org.springframework.web.bind.annotation.PostMapping public void noise(java.util.Map<Object,Object> input){input.values();}
                  @org.springframework.web.bind.annotation.PostMapping public void other(java.util.Map<Object,Object> input){input.values();}
                }
                """.replace("RETURN",carry?"value":"null"),
                "org/springframework/web/bind/annotation/RestController.java","package org.springframework.web.bind.annotation; @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface RestController {}",
                "org/springframework/web/bind/annotation/PostMapping.java","package org.springframework.web.bind.annotation; @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface PostMapping {}"));
        // Missing ancestors are unresolved alternatives, not 64 invented concrete member lookups.
        for(int i=0;i<64;i++) {
            var writer=new org.objectweb.asm.ClassWriter(0);
            writer.visit(org.objectweb.asm.Opcodes.V1_8,org.objectweb.asm.Opcodes.ACC_PUBLIC,"Fragment"+i,null,"absent/Parent"+i,new String[]{"java/io/Serializable"});writer.visitEnd();
            java.nio.file.Files.write(classes.resolve("Fragment"+i+".class"),writer.toByteArray());
        }
        return classes;
    }
    @Test void applicationWithoutFactsConnectsSourceCallbackAndOrderedReturnsButDiscardingReturnsBreaksIt() throws Exception {
        for(boolean carry:List.of(true,false)) {
            try(Inputs inputs=Inputs.open(application(carry),List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
                Program program=new Program(inputs,20_000);
                ScanResult result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.APPLICATION,false);
                var impacts=result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT && result.relations().get(f.path().get(f.path().size()-1)).target().filter(t -> t.owner().equals("java/lang/Runtime")).isPresent()).toList();
                assertEquals(carry,!impacts.isEmpty(),result.statistics()+"; impacts in relations="+result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).map(r -> r.target()).distinct().toList()+"; "+result.limitations());
                if(carry) {

                    assertTrue(impacts.stream().anyMatch(f -> {
                        List<Relation> proof=f.proof().stream().map(use -> result.relations().get(use.relation())).toList();
                        Set<String> methods=proof.stream().flatMap(r -> r.target().stream()).map(Program.MethodId::name).collect(java.util.stream.Collectors.toSet());
                        Relation endpoint=result.relations().get(f.path().get(f.path().size()-1));
                        boolean set=f.proof().stream().flatMap(use -> result.relations().get(use.relation()).supports().get(use.support()).witnesses().stream()).anyMatch(site -> site.method().owner().equals("java/util/HashSet"));
                        return methods.containsAll(Set.of("hashCode","replay","forName","getMethod","getRuntime","exec")) && set
                                && endpoint.target().orElseThrow().descriptor().startsWith("([Ljava/lang/String;")
                                && endpoint.receiver() instanceof ObjectValue object && object.origin().equals("Runtime.getRuntime API result");
                    }),"recovered method sets: "+impacts.stream().map(f -> java.util.stream.Stream.concat(f.path().stream(),f.supportingRelations().stream()).map(result.relations()::get).flatMap(r -> r.target().stream()).map(Program.MethodId::name).collect(java.util.stream.Collectors.toSet())).distinct().limit(12).toList()+"; "+result.limitations());
                    assertTrue(result.inputRequirements().stream().anyMatch(r -> r.source().filter(s -> s.path().contains(new Index(3))).isPresent()));
                    assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.CLASS_NAME && r.needed().descriptor().equals("Ljava/lang/String;")
                            && r.source().filter(s -> s.path().contains(new Index(0)) && !s.path().contains(new NamedClass())).isPresent()),"the required class name belongs to the original string slot, not the derived Class value");
                }
            }
        }
    }
    @Test void localTargetBatchesKeepBothInputPathsAndTheirActualSupports()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Goals.java","""
            public class Goals {
              public static class Target {public void first(){}public void second(){}}
              private static String left(String name){return name;}
              private static String right(String name){return name;}
              public static void run(String name,boolean side)throws Exception {
                String selected=side?left(name):right(name);
                Target.class.getMethod(selected).invoke(new Target());
              }
            }
            """));
        ScanResult result=scan(classes,"run","(Ljava/lang/String;Z)V");
        for(String member:List.of("first","second")) {
            Map<BranchKey,Set<Integer>> paths=new HashMap<>();
            for(Finding finding:result.findings())if(finding.proof().stream().anyMatch(use -> result.relations().get(use.relation()).target().filter(target -> target.owner().equals("Goals$Target") && target.name().equals(member)).isPresent()))
                finding.conditions().choices().forEach((choice,selected) -> {if(choice instanceof BranchKey branch && branch.context()==0)paths.computeIfAbsent(branch,key -> new HashSet<>()).add(selected);});
            assertTrue(paths.values().stream().anyMatch(choices -> choices.size()==2),member+" must retain both real input paths: "+paths+"; "+result.limitations());
        }
    }
    @Test void aFiniteBatchKeepsLaterOverloadsOfAKnownReceiverWithinTheSameWorkBudget()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Overloads.java","""
            public class Overloads {
              public static void run(String name,Class<?>[] types,Object[] arguments)throws Exception {
                Runtime runtime=Runtime.getRuntime();Runtime.class.getMethod(name,types).invoke(runtime,arguments);
              }
            }
            """));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);
            Set<Program.MethodId> expected=program.methods("java/lang/Runtime",false).value().orElseThrow().stream().map(Program.Method::id).filter(id -> id.name().equals("exec")).collect(java.util.stream.Collectors.toSet());
            ScanResult result=new Analyzer(program,new Mechanisms(program),new Analyzer.Limits(500,500,12,2000,100,64))
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Overloads","run","(Ljava/lang/String;[Ljava/lang/Class;[Ljava/lang/Object;)V")));
            Set<Program.MethodId> actual=result.relations().stream().filter(edge -> edge.kind()==Kind.IMPACT).flatMap(edge -> edge.target().stream()).collect(java.util.stream.Collectors.toSet());
            assertEquals(6,expected.size());assertTrue(actual.containsAll(expected),actual+"; "+result.statistics());
        }
    }
}
