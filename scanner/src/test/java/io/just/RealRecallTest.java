package io.just;

import io.just.knowledge.EntryPoints;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

/** Independent source-built bytecode. None of these classes or callbacks is executed. */
class RealRecallTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String owner,String entry,String descriptor,List<Path> dependencies)throws Exception {
        try(Inputs input=Inputs.open(classes,dependencies,Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId(owner,entry,descriptor)));
        }
    }
    private boolean impact(ScanResult result,String name){return result.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.target().filter(t -> t.name().equals(name)).isPresent());}
    @Test void constantBase64ClassBytesRetainTheirDefinitionAndIdentity()throws Exception {
        Path stage=BytecodeFixtures.compile(temp,8,Map.of("EncodedStage.java","public class EncodedStage {public static void run()throws Exception {Runtime.getRuntime().exec(\"encoded-stage\");}}"));
        String encoded=Base64.getEncoder().encodeToString(java.nio.file.Files.readAllBytes(stage.resolve("EncodedStage.class")));
        Path root=BytecodeFixtures.compile(temp,8,Map.of("EncodedRoot.java","""
                public class EncodedRoot extends ClassLoader {
                  public static void run()throws Exception {
                    byte[] bytes=java.util.Base64.getDecoder().decode("%s");
                    Class<?> type=new EncodedRoot().defineClass("EncodedStage",bytes,0,bytes.length);
                    type.getMethod("run").invoke(null);
                  }
                  protected Class<?> findClass(String name){
                    byte[] bytes=java.util.Base64.getDecoder().decode("%s");
                    return defineClass(name,bytes,0,bytes.length);
                  }
                  public static void delegate()throws Exception {
                    new EncodedRoot().loadClass("EncodedStage").getMethod("run").invoke(null);
                  }
                }
                """.formatted(encoded,encoded)));
        ScanResult result=scan(root,"EncodedRoot","run","()V",List.of());
        assertTrue(impact(result,"defineClass"));
        assertTrue(result.relations().stream().anyMatch(r -> r.site().method().owner().equals("EncodedStage") && r.target().filter(t -> t.name().equals("exec")).isPresent()),result.limitations().toString());
        ScanResult delegated=scan(root,"EncodedRoot","delegate","()V",List.of());
        assertTrue(delegated.relations().stream().anyMatch(r -> r.target().filter(t -> t.owner().equals("EncodedRoot") && t.name().equals("findClass")).isPresent()));
        assertTrue(delegated.relations().stream().anyMatch(r -> r.site().method().owner().equals("EncodedStage") && r.target().filter(t -> t.name().equals("exec")).isPresent()),delegated.limitations().toString());
    }
    @Test void classResourceDefinitionContinuesThroughThisClassInitializationAndConstruction()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("LoaderRoot.java","""
            public class LoaderRoot extends ClassLoader {
              Class<?> accept(byte[] bytes){return defineClass(null,bytes,0,bytes.length);}
              public static void run()throws Exception {
                byte[] bytes=LoaderRoot.class.getResourceAsStream("/Stage.class").readAllBytes();
                new LoaderRoot().accept(bytes).newInstance();
              }
              public static void onlyLoad()throws Exception {Class.forName("Stage",false,LoaderRoot.class.getClassLoader());}
              public static void initialize()throws Exception {Class.forName("Stage",true,LoaderRoot.class.getClassLoader());}
              public static void missing(byte[] bytes){new LoaderRoot().accept(bytes);}
              public static void invalid()throws Exception {try{new LoaderRoot().accept(new byte[]{1,2,3});}catch(ClassFormatError expected){Runtime.getRuntime().exec("caught");}}
            }
            ""","Stage.java","""
            public class Stage {static {try{Runtime.getRuntime().exec("initialization");}catch(Exception ignored){}}public Stage()throws Exception{Runtime.getRuntime().exec("construction");if(Class.forName("Stage")==Stage.class)Runtime.getRuntime().exec("scoped");else Runtime.getRuntime().exec("wrong-scope");}}
            """));
        ScanResult defined=scan(classes,"LoaderRoot","run","()V",List.of());
        assertTrue(impact(defined,"defineClass"));assertTrue(impact(defined,"exec"),defined.limitations().toString());
        assertTrue(defined.relations().stream().anyMatch(r -> r.site().method().owner().equals("Stage") && r.site().method().loader()!=0 && r.site().method().name().equals("<clinit>")));
        assertTrue(defined.relations().stream().anyMatch(r -> r.site().method().owner().equals("Stage") && r.site().method().name().equals("<init>")));
        assertTrue(defined.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.arguments().contains(new Literal("scoped"))));
        assertFalse(defined.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.arguments().contains(new Literal("wrong-scope"))),"one-argument forName uses the defining class's loader");
        assertFalse(impact(scan(classes,"LoaderRoot","onlyLoad","()V",List.of()),"exec"));
        assertTrue(impact(scan(classes,"LoaderRoot","initialize","()V",List.of()),"exec"));
        ScanResult missing=scan(classes,"LoaderRoot","missing","([B)V",List.of());assertTrue(impact(missing,"defineClass"));assertFalse(impact(missing,"exec"));
        assertTrue(impact(scan(classes,"LoaderRoot","invalid","()V",List.of()),"exec"));
    }
    @Test void namedPlatformClassUsesTheSameLoadingAndInvocationSemantics()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Named.java","public class Named {public static void run()throws Exception {Object runtime=Class.forName(\"java.lang.Runtime\").getMethod(\"getRuntime\").invoke(null);Runtime.class.getMethod(\"exec\",String.class).invoke(runtime,\"static-only\");}}"));
        ScanResult result=scan(classes,"Named","run","()V",List.of());assertTrue(impact(result,"exec"),result.limitations().toString());
    }
    @Test void unknownInitializationFlagKeepsTheLoadOnlyContinuationWhenInitializationThrows()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("FlagBoundary.java","""
            public class FlagBoundary {
              public static void run(boolean initialize)throws Exception {Class.forName("Failing",initialize,FlagBoundary.class.getClassLoader());Runtime.getRuntime().exec("after-load");}
              public static void force()throws Exception {run(true);}
            }
            ""","Failing.java","public class Failing {static {fail();}static void fail(){throw new RuntimeException();}}"));
        assertTrue(impact(scan(classes,"FlagBoundary","run","(Z)V",List.of()),"exec"));
        assertFalse(impact(scan(classes,"FlagBoundary","force","()V",List.of()),"exec"));
    }
    @Test void sameBinaryNameInDifferentLoadersUsesDifferentMethodFactsAndDoesNotTrustNegativeCache()throws Exception {
        Path first=BytecodeFixtures.compile(temp,8,Map.of("Separate.java","public class Separate implements Runnable {public void run(){value();}public static int value(){return 1;}}"));
        Path second=BytecodeFixtures.compile(temp,8,Map.of("Separate.java","public class Separate implements Runnable {public void run(){value();}public static int value(){return 2;}}"));
        Path root=BytecodeFixtures.compile(temp,8,Map.of("Root.java","public class Root {}"));
        try(Inputs input=Inputs.open(root,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);assertTrue(program.definition("Separate").value().isEmpty());
            assertTrue(program.reflect("Separate","value",List.of(),false).value().isEmpty());
            var run=new Program.MethodId("java/lang/Runnable","run","()V");program.implementations(run,"java/lang/Runnable",0);
            byte[] a=java.nio.file.Files.readAllBytes(first.resolve("Separate.class")),b=java.nio.file.Files.readAllBytes(second.resolve("Separate.class"));
            var one=program.define(new LoaderValue("first"),a,a,0,a.length,null).value().orElseThrow();
            var two=program.define(new LoaderValue("second"),b,b,0,b.length,null).value().orElseThrow();
            assertNotEquals(one.loader(),two.loader());
            for(var definition:List.of(one,two)) {
                var method=program.method("Separate","value","()I",definition.loader());
                assertEquals(method,program.reflect("Separate","value",List.of(),false,definition.loader()).value().orElseThrow().id());
                assertTrue(program.facts(method).actions().stream().anyMatch(action -> action instanceof Program.Constant c && c.value().equals(new Program.LiteralConstant(definition==one?1:2))));
                assertTrue(program.callers(method).sites().stream().anyMatch(site -> site.method().owner().equals("Separate") && site.method().loader()==definition.loader()));
            }
            assertEquals(Set.of(one.loader(),two.loader()),program.implementations(run,"java/lang/Runnable",0).value().orElseThrow().stream().flatMap(t -> t.receiver().stream()).filter(t -> t.name().equals("Separate")).map(Program.DefinedType::loader).collect(java.util.stream.Collectors.toSet()));
        }
    }
    @Test void inheritedVirtualBodySeesEachConcreteRuntimeClassFromADependency()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of(
                "Use.java","public class Use {public static void run(Runnable receiver){receiver.run();}}",
                "Parent.java","public class Parent implements Runnable {public void run(){try{Runtime.getRuntime().exec(getClass().getName());}catch(Exception ignored){}}}",
                "First.java","public class First extends Parent {}","Second.java","public class Second extends Parent {}"));
        Path library=java.nio.file.Files.createDirectory(temp.resolve("dispatch-library"));
        for(String name:List.of("Parent","First","Second"))java.nio.file.Files.move(classes.resolve(name+".class"),library.resolve(name+".class"));
        ScanResult result=scan(classes,"Use","run","(Ljava/lang/Runnable;)V",List.of(library));
        Set<Atom> commands=result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.arguments().stream()).collect(java.util.stream.Collectors.toSet());
        assertTrue(commands.containsAll(Set.of(new Literal("First"),new Literal("Second"))),commands.toString());
    }
    @Test void anUnresolvedInitializerOnlyBlocksTheBindingThatActivelyUsesIt()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of(
                "Boundary.java","public class Boundary {public static void read(java.io.ObjectInputStream input)throws Exception{input.readObject();}}",
                "AWaiting.java","public class AWaiting implements java.io.Serializable {static Object value=again();static Object again(){return again();}public int hashCode(){Object current=value;try{Runtime.getRuntime().exec(\"blocked\");}catch(Exception ignored){}return 1;}}",
                "BAvailable.java","public class BAvailable implements java.io.Serializable {public int hashCode(){try{Runtime.getRuntime().exec(\"independent\");}catch(Exception ignored){}return 1;}}"));
        ScanResult result=scan(classes,"Boundary","read","(Ljava/io/ObjectInputStream;)V",List.of());
        Set<Atom> commands=result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.arguments().stream()).collect(java.util.stream.Collectors.toSet());
        assertTrue(commands.contains(new Literal("independent")),result.limitations().toString());
        assertFalse(commands.contains(new Literal("blocked")),"active use still waits for its own initializer");
    }
    @Test void interfaceUpperBoundFindsAnImplementationInAnExplicitDependency()throws Exception {
        Path use=BytecodeFixtures.compile(temp,8,Map.of("Use.java","public class Use {public static void run(Runnable callback){callback.run();}public static void map(java.util.Map<?,?> callback){callback.values();}}","Lib.java","public class Lib implements Runnable {public void run(){try{Runtime.getRuntime().exec(\"dependency\");}catch(Exception ignored){}}}",
                "Missing.java","public class Missing {}","Noisy.java","public class Noisy extends Missing {public void run(){try{Runtime.getRuntime().exec(\"noisy\");}catch(Exception ignored){}}}",
                "CustomMap.java","public class CustomMap extends java.util.HashMap<Object,Object> {public java.util.Collection<Object> values(){try{Runtime.getRuntime().exec(\"override\");}catch(Exception ignored){}return java.util.Collections.emptyList();}}"));
        Path dep=java.nio.file.Files.createDirectory(temp.resolve("dep"));
        for(String type:List.of("Lib","Noisy","CustomMap"))java.nio.file.Files.move(use.resolve(type+".class"),dep.resolve(type+".class"));java.nio.file.Files.delete(use.resolve("Missing.class"));
        ScanResult result=scan(use,"Use","run","(Ljava/lang/Runnable;)V",List.of(dep));assertTrue(impact(result,"exec"));
        assertTrue(result.entries().stream().allMatch(e -> e.method().id().owner().equals("Use")));
        var good=result.findings().stream().filter(f -> result.relations().get(f.path().get(f.path().size()-1)).arguments().contains(new Literal("dependency"))).toList();
        assertFalse(good.isEmpty());assertTrue(good.stream().allMatch(f -> f.gaps().stream().noneMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY && g.detail().contains("Missing"))),"another implementation's missing parent cannot become this chain's prerequisite");
        assertTrue(result.findings().stream().anyMatch(f -> result.relations().get(f.path().get(f.path().size()-1)).arguments().contains(new Literal("noisy")) && f.gaps().stream().anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY && g.detail().contains("Missing"))));
        ScanResult overridden=scan(use,"Use","map","(Ljava/util/Map;)V",List.of(dep));
        assertTrue(overridden.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.arguments().contains(new Literal("override"))),"a conditional platform model cannot suppress an ordinary dependency override");
    }
    @Test void nullableStringKeepsBothNormalAndCatchPathsAndModernConcatKeepsItsPrefix()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("TextBoundary.java","""
            public class TextBoundary {
              public static void run(String input)throws Exception {try{input.length();Runtime.getRuntime().exec("normal");}catch(NullPointerException expected){Runtime.getRuntime().exec("caught");}}
              public static void concat(String suffix)throws Exception {Runtime.class.getMethod("get"+suffix).invoke(null);}
            }
            """));
        ScanResult nullable=scan(classes,"TextBoundary","run","(Ljava/lang/String;)V",List.of());
        Set<String> commands=new HashSet<>();nullable.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.arguments().stream()).filter(a -> a instanceof Literal).forEach(a -> commands.add(String.valueOf(((Literal)a).value())));
        assertTrue(commands.containsAll(Set.of("normal","caught")),commands.toString());
        for(int release:List.of(8,17)) {
            Path target=release==17?classes:BytecodeFixtures.compile(temp,8,Map.of("TextBoundary.java","public class TextBoundary {public static void concat(String suffix)throws Exception {Runtime.class.getMethod(\"get\"+suffix).invoke(null);}}"));
            ScanResult concat=scan(target,"TextBoundary","concat","(Ljava/lang/String;)V",List.of());
            assertTrue(concat.relations().stream().anyMatch(r -> r.target().filter(t -> t.owner().equals("java/lang/Runtime") && t.name().equals("getRuntime")).isPresent()),"Java "+release);
            assertFalse(concat.relations().stream().anyMatch(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.name().equals("exec")).isPresent()),"Java "+release);
        }
    }
    @Test void unknownConstructorArgumentsAndProxyInterfacesKeepKnownCreationSources()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Creation.java","""
            import java.lang.reflect.*;
            public class Creation {
              public static class Product {public Product(String value)throws Exception {Runtime.getRuntime().exec("constructor");}}
              public interface Service {void call()throws Exception;}
              public static void constructor(Class<?>[] types,Object[] args)throws Exception {Product.class.getConstructor(types).newInstance(args);}
              public static void proxy(Class<?> face)throws Exception {
                Service service=(Service)Proxy.newProxyInstance(Creation.class.getClassLoader(),new Class[]{face},(p,m,a)->{Runtime.getRuntime().exec("handler");return null;});service.call();
              }
              public static void comparator()throws Exception {
                java.util.TreeMap<String,String> map=new java.util.TreeMap<>((a,b)->{try{Runtime.getRuntime().exec("comparator");}catch(Exception ignored){}return 1;});
                map.put("A","first");map.put("B","second");
              }
            }
            """));
        assertTrue(impact(scan(classes,"Creation","constructor","([Ljava/lang/Class;[Ljava/lang/Object;)V",List.of()),"exec"));
        assertTrue(impact(scan(classes,"Creation","proxy","(Ljava/lang/Class;)V",List.of()),"exec"));
        assertTrue(impact(scan(classes,"Creation","comparator","()V",List.of()),"exec"));
    }
    @Test void inheritedGadgetInASeparateLibraryRetainsItsSerializableChildAndMissingAncestors()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Read.java","public class Read {public static void run(java.io.ObjectInputStream input)throws Exception{input.readObject();}}",
                "Parent.java","public class Parent {public int hashCode(){try{Runtime.getRuntime().exec(\"inherited\");}catch(Exception ignored){}return 1;}}",
                "Child.java","public class Child extends Parent implements java.io.Serializable {}",
                "Missing.java","public class Missing {}","Open.java","public class Open extends Missing {public int hashCode(){try{Runtime.getRuntime().exec(\"unknown-parent\");}catch(Exception ignored){}return 1;}}"));
        java.nio.file.Files.delete(classes.resolve("Missing.class"));
        Path library=java.nio.file.Files.createDirectory(temp.resolve("library"));
        for(String name:List.of("Parent","Child","Open"))java.nio.file.Files.move(classes.resolve(name+".class"),library.resolve(name+".class"));
        ScanResult result=scan(classes,"Read","run","(Ljava/io/ObjectInputStream;)V",List.of(library));
        assertTrue(impact(result,"exec"));assertTrue(result.missingClasses().contains("Missing"));
        assertTrue(result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT && f.path().stream().map(result.relations()::get).anyMatch(r -> r.target().filter(t -> t.owner().equals("Parent") && t.name().equals("hashCode")).isPresent())));
        byte[] entry=java.nio.file.Files.readAllBytes(classes.resolve("Read.class"));
        java.io.ByteArrayOutputStream dependency=new java.io.ByteArrayOutputStream();
        try(java.util.jar.JarOutputStream jar=new java.util.jar.JarOutputStream(dependency)) {
            for(String name:List.of("Parent","Child")){jar.putNextEntry(new java.util.jar.JarEntry(name+".class"));jar.write(java.nio.file.Files.readAllBytes(library.resolve(name+".class")));jar.closeEntry();}
        }
        Path fat=temp.resolve("nested.jar");
        try(java.util.jar.JarOutputStream jar=new java.util.jar.JarOutputStream(java.nio.file.Files.newOutputStream(fat))) {
            jar.putNextEntry(new java.util.jar.JarEntry("BOOT-INF/classes/Read.class"));jar.write(entry);jar.closeEntry();
            jar.putNextEntry(new java.util.jar.JarEntry("BOOT-INF/lib/library.jar"));jar.write(dependency.toByteArray());jar.closeEntry();
        }
        ScanResult embedded=scan(fat,"Read","run","(Ljava/io/ObjectInputStream;)V",List.of());
        assertTrue(impact(embedded,"exec"));assertEquals(2,embedded.input().dependencyClasses());
    }
    @Test void genericLoopRevisitsItsCarriedValueWhenTheRealReflectionReturnGrows()throws Exception {
        for(boolean keep:List.of(true,false)) {
            Path classes=BytecodeFixtures.compile(temp,8,Map.of("Growth.java","""
                public class Growth {
                  public static void run(int limit,String command)throws Exception {
                    Object value=Runtime.class;
                    for(int i=0;i<limit;i++) {
                      if(value instanceof Class) {KEEP ((Class<?>)value).getMethod("getRuntime",new Class[0]).invoke(null,new Object[0]);}
                      else {((Runtime)value).exec(command);}
                    }
                  }
                  static void fail(){throw new IllegalStateException();}
                  public static void blocked(int limit,String command)throws Exception {
                    for(int i=0;i<limit;i++){if(i==0)fail();else Runtime.getRuntime().exec(command);}
                  }
                  public static void invariant(int limit,boolean flag,String command)throws Exception {
                    for(int i=0;i<limit;i++){if(flag){if(i==0)fail();else Runtime.getRuntime().exec(command);}}
                  }
                }
                """.replace("KEEP",keep?"value=":"")));
            ScanResult result=scan(classes,"Growth","run","(ILjava/lang/String;)V",List.of());
            assertEquals(keep,impact(result,"exec"),"a new method return must reach later consumers; a discarded return cannot fill them");
            if(keep)assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.receiver() instanceof ObjectValue object && object.type().equals("java/lang/Runtime") && object.origin().equals("Runtime.getRuntime API result") && r.arguments().stream().anyMatch(a -> io.just.knowledge.Values.source(a).filter(s -> s.parameterSlot()==1).isPresent())));
            if(keep) {
                assertFalse(impact(scan(classes,"Growth","blocked","(ILjava/lang/String;)V",List.of()),"exec"),"an iteration that definitely throws cannot reach a later iteration");
                assertFalse(impact(scan(classes,"Growth","invariant","(IZLjava/lang/String;)V",List.of()),"exec"),"one unchanged boolean cannot skip the failure and then become true in the next iteration");
            }
        }
    }
    @Test void finiteLoopsCarryNonNullValuesAndRespectAnEarlyExit()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("LoopBoundary.java","""
            public class LoopBoundary {
              public static void carry()throws Exception {
                java.util.LinkedHashMap<Integer,String> values=new java.util.LinkedHashMap<>();values.put(1,"X");values.put(2,"Y");
                String current="seed";for(String value:values.values())current=current.concat(value);Runtime.getRuntime().exec(current);
              }
              public static void exit()throws Exception {
                java.util.LinkedHashMap<Integer,String> values=new java.util.LinkedHashMap<>();values.put(1,"first");values.put(2,"stop");values.put(3,"late");
                String current="seed";for(String value:values.values()){if(value.equals("stop"))break;current=value;Runtime.getRuntime().exec(value);}Runtime.getRuntime().exec(current);
              }
            }
            """));
        for(String entry:List.of("carry","exit")) {
            ScanResult result=scan(classes,"LoopBoundary",entry,"()V",List.of());Set<String> commands=new HashSet<>();
            result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.arguments().stream()).filter(a -> a instanceof Literal).forEach(a -> commands.add(String.valueOf(((Literal)a).value())));
            assertEquals(entry.equals("carry")?Set.of("seedXY"):Set.of("first"),commands,result.limitations().toString());
            assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.site().method().owner().equals("LoopBoundary")));
        }
    }
    @Test void composedAndInheritedMappingsRemainApplicationBoundaries()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of(
                "org/springframework/web/bind/annotation/RestController.java","package org.springframework.web.bind.annotation;@java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface RestController {}",
                "org/springframework/web/bind/annotation/GetMapping.java","package org.springframework.web.bind.annotation;@java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface GetMapping {}",
                "Endpoint.java","@org.springframework.web.bind.annotation.GetMapping @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface Endpoint {}",
                "Controller.java","@org.springframework.web.bind.annotation.RestController @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface Controller {}",
                "WebParent.java","public class WebParent {@Endpoint public void handle()throws Exception{Runtime.getRuntime().exec(\"mapped\");}}",
                "WebChild.java","@Controller public class WebChild extends WebParent {}",
                "Unexposed.java","public class Unexposed {public void direct()throws Exception{Runtime.getRuntime().exec(\"unexposed\");}}"));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);ScanResult result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.APPLICATION,false);
            assertTrue(impact(result,"exec"));assertEquals(1,result.entries().size());
            assertEquals("WebParent",result.entries().get(0).method().id().owner());assertTrue(result.entries().get(0).boundary().contains("WebChild"));
            assertFalse(result.relations().stream().anyMatch(r -> r.site().method().owner().equals("Unexposed")));
        }
    }
    @Test void recursiveWorkInOneBranchDoesNotConsumeEveryOtherCallersTurn()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("BranchBoundary.java","""
            public class BranchBoundary {
              static int expand(int value){return expand(value+1)+expand(value+2);}
              public static void run(boolean crowded)throws Exception {
                if(crowded)expand(0);else Runtime.getRuntime().exec("independent-branch");
              }
              public static void onlyCrowded()throws Exception {run(true);}
            }
            """));
        for(String entry:List.of("run","onlyCrowded"))try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            ScanResult result=new Analyzer(program,new Mechanisms(program),new Analyzer.Limits(500,10000,12,600,100,32))
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("BranchBoundary",entry,entry.equals("run")?"(Z)V":"()V")));
            assertEquals(entry.equals("run"),impact(result,"exec"),result.statistics()+"; "+result.limitations());
            assertEquals(ScanResult.Execution.TRUNCATED,result.execution(),"unfinished recursion remains visible");
        }
    }
}
