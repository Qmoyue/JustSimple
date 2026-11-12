package io.just;

import io.just.analysis.*;
import io.just.input.*;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

/** Regression examples at the scan boundary, compiled and inspected without target execution. */
class SemanticRepairTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String owner,String name,String descriptor) throws Exception {
        return scan(classes,owner,name,descriptor,Optional.empty());
    }
    private ScanResult scan(Path classes,String owner,String name,String descriptor,Optional<StaticData> facts) throws Exception {
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId(owner,name,descriptor)),facts);
        }
    }
    private boolean calls(ScanResult result,String owner,String method) {
        return result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals(owner) && t.name().equals(method));
    }
    @Test void unsupportedBootstrapKeepsItsUnknownResultAndNormalCompletionCondition()throws Exception {
        Path classes=Files.createDirectory(temp.resolve("bootstrap"));
        var writer=new org.objectweb.asm.ClassWriter(org.objectweb.asm.ClassWriter.COMPUTE_MAXS);
        writer.visit(org.objectweb.asm.Opcodes.V17,org.objectweb.asm.Opcodes.ACC_PUBLIC|org.objectweb.asm.Opcodes.ACC_SUPER,"UnknownBootstrap",null,"java/lang/Object",null);
        String descriptor="(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
        var factory=writer.visitMethod(org.objectweb.asm.Opcodes.ACC_PUBLIC|org.objectweb.asm.Opcodes.ACC_STATIC,"factory",descriptor,null,null);
        factory.visitCode();factory.visitInsn(org.objectweb.asm.Opcodes.ACONST_NULL);factory.visitInsn(org.objectweb.asm.Opcodes.ARETURN);factory.visitMaxs(0,0);factory.visitEnd();
        var run=writer.visitMethod(org.objectweb.asm.Opcodes.ACC_PUBLIC|org.objectweb.asm.Opcodes.ACC_STATIC,"run","()V",null,null);run.visitCode();
        run.visitInvokeDynamicInsn("name","()Ljava/lang/String;",new org.objectweb.asm.Handle(org.objectweb.asm.Opcodes.H_INVOKESTATIC,"UnknownBootstrap","factory",descriptor,false));
        run.visitMethodInsn(org.objectweb.asm.Opcodes.INVOKESTATIC,"UnknownBootstrap","consume","(Ljava/lang/String;)V",false);
        run.visitInsn(org.objectweb.asm.Opcodes.RETURN);run.visitMaxs(0,0);run.visitEnd();
        var consume=writer.visitMethod(org.objectweb.asm.Opcodes.ACC_PUBLIC|org.objectweb.asm.Opcodes.ACC_STATIC,"consume","(Ljava/lang/String;)V",null,null);
        consume.visitCode();consume.visitInsn(org.objectweb.asm.Opcodes.RETURN);consume.visitMaxs(0,0);consume.visitEnd();writer.visitEnd();
        Files.write(classes.resolve("UnknownBootstrap.class"),writer.toByteArray());
        var result=scan(classes,"UnknownBootstrap","run","()V");
        assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.DYNAMIC_CALL).anyMatch(r -> r.supports().stream().flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.UNSUPPORTED)));
        assertTrue(result.relations().stream().filter(r -> r.target().filter(target -> target.name().equals("consume")).isPresent())
                .anyMatch(r -> r.arguments().get(0) instanceof Unknown
                        && r.conditions().choices().keySet().stream().anyMatch(NormalChoice.class::isInstance)
                        && r.supports().stream().allMatch(s -> s.gaps().stream().anyMatch(g -> g.kind()==GapKind.UNSUPPORTED))));
    }
    @Test void missingCallbackAncestorDoesNotEraseTheContainerCallback()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Callback.java","""
                public class Callback {
                  public static class Parent {public int hashCode(){return 1;}}
                  public static class Key extends Parent {}
                  public static void run(){new java.util.HashMap<Object,Object>().put(new Key(),"value");}
                }
                """));
        Files.delete(classes.resolve("Callback$Parent.class"));
        var result=scan(classes,"Callback","run","()V");
        assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.CONTAINER_CALLBACK && r.target().filter(t -> t.owner().equals("Callback$Key") && t.name().equals("hashCode")).isPresent())
                .anyMatch(r -> r.supports().stream().flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY)));
    }
    @Test void incompleteMethodEnumerationCannotProveAnIndexIsOutOfBounds()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Enumeration.java","""
                public class Enumeration {
                  public static class Parent {public void inherited(){}}
                  public static class Known extends Parent {public void hit(){}}
                  public static void run()throws Exception {Known.class.getMethods()[20].invoke(new Known(),new Object[0]);}
                  static void boundsHandler(){}
                  public static void knownBounds()throws Exception {try{Known.class.getDeclaredMethods()[20].invoke(new Known(),new Object[0]);}catch(ArrayIndexOutOfBoundsException expected){boundsHandler();}}
                }
                """));
        Files.delete(classes.resolve("Enumeration$Parent.class"));
        var result=scan(classes,"Enumeration","run","()V");
        assertTrue(result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Enumeration$Known") && t.name().equals("hit")).isPresent())
                .anyMatch(r -> r.supports().stream().flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY)));
        var complete=scan(classes,"Enumeration","knownBounds","()V");
        assertTrue(calls(complete,"Enumeration","boundsHandler"));assertFalse(calls(complete,"Enumeration$Known","hit"));
    }
    @Test void nativeContainerMemoHitsKeepRestoredNestedFieldsBeforeTheCallback()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("NestedRestore.java","""
                public class NestedRestore {
                  public static class Behavior implements java.io.Serializable {public void apply(Object value){}}
                  public static class Effect extends Behavior {public Function function;public Resolved resolver;public void apply(Object value){function.touch(value);}}
                  public static class Function implements java.io.Serializable {public void touch(Object value){hit();}}
                  public static class Resolved implements java.io.Serializable {static final Resolved INSTANCE=new Resolved();private Object readResolve(){return INSTANCE;}}
                  public static class Key implements java.io.Serializable {public Behavior behavior;public Object reference;public int hashCode(){behavior.apply(reference);return 0;}}
                  public static void hit(){}
                  public static Object read(java.io.ObjectInputStream in)throws Exception{return in.readObject();}
                }
                """));
        Path file=temp.resolve("nested.json");Files.writeString(file,"""
                {"source":"source-built nested restoration","basis":"BINDING","entry":{"owner":"NestedRestore","name":"read","descriptor":"(Ljava/io/ObjectInputStream;)Ljava/lang/Object;","arguments":[{"ref":"stream"}]},"objects":[
                  {"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"set"}},
                  {"id":"set","type":"java/util/HashSet","elements":[{"ref":"key"}]},
                  {"id":"key","type":"NestedRestore$Key","fields":[{"owner":"NestedRestore$Key","name":"behavior","descriptor":"LNestedRestore$Behavior;","value":{"ref":"effect"}},{"owner":"NestedRestore$Key","name":"reference","descriptor":"Ljava/lang/Object;","value":"ordinary"}]},
                  {"id":"effect","type":"NestedRestore$Effect","fields":[{"owner":"NestedRestore$Effect","name":"function","descriptor":"LNestedRestore$Function;","value":{"ref":"function"}},{"owner":"NestedRestore$Effect","name":"resolver","descriptor":"LNestedRestore$Resolved;","value":{"ref":"resolver"}}]},
                  {"id":"function","type":"NestedRestore$Function"},{"id":"resolver","type":"NestedRestore$Resolved"}]}
                """);
        var result=scan(classes,"NestedRestore","read","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;",Optional.of(StaticData.read(file)));
        assertTrue(calls(result,"NestedRestore","hit"));
        assertTrue(calls(result,"NestedRestore$Resolved","readResolve"));
    }
    @Test void customIteratorsKeepTheirBodiesAndStandardViewsKeepTheirBindings() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Iterators.java","""
                public class Iterators {
                  static void visible(){}
                  public static class Custom implements Iterable<String> {public java.util.Iterator<String> iterator(){visible();return java.util.Collections.emptyIterator();}}
                  public static class Inherited extends Custom {}
                  public static class Target {public static void hit(){}}
                  public static void own(){new Custom().iterator();}
                  public static void inherited(){new Inherited().iterator();}
                  public static void list()throws Exception {String n=java.util.Arrays.asList("hit").iterator().next();Target.class.getMethod(n,new Class[0]).invoke(null,new Object[0]);}
                  public static void map()throws Exception {java.util.Map<String,String> m=new java.util.LinkedHashMap<>();m.put("key","hit");String n=m.values().iterator().next();Target.class.getMethod(n,new Class[0]).invoke(null,new Object[0]);}
                }
                """));
        for(String method:List.of("own","inherited"))assertTrue(calls(scan(classes,"Iterators",method,"()V"),"Iterators","visible"),method);
        for(String method:List.of("list","map"))assertTrue(calls(scan(classes,"Iterators",method,"()V"),"Iterators$Target","hit"),method);
    }
    @Test void missingExceptionHierarchyRetainsTheConditionalHandler() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Exceptions.java","""
                public class Exceptions {
                  public static class Base extends RuntimeException {}
                  public static class Child extends Base {}
                  static void kept(){}
                  public static void run(){try{throw new Child();}catch(RuntimeException e){kept();}}
                }
                """));
        assertTrue(calls(scan(classes,"Exceptions","run","()V"),"Exceptions","kept"));
        Files.delete(classes.resolve("Exceptions$Base.class"));
        var result=scan(classes,"Exceptions","run","()V");
        assertTrue(calls(result,"Exceptions","kept"));
        assertTrue(result.relations().stream().flatMap(r -> r.supports().stream().flatMap(s -> s.gaps().stream())).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
    }
    @Test void java17ConcatCanBindAReflectionTargetAlongsideLambdaAndBuilder() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Concat.java","""
                public class Concat {
                  public static class Target {public static void reached(){}}
                  static void lookup(String name)throws Exception {Class.forName("Concat$"+name).getMethod("reached",new Class[0]).invoke(null,new Object[0]);}
                  public static void run()throws Exception {Runnable r=()->Target.reached();r.run();lookup(new StringBuilder("Tar").append("get").toString());}
                }
                """));
        var result=scan(classes,"Concat","run","()V");
        assertEquals(ScanResult.Execution.FINISHED,result.execution(),result.limitations().toString());
        assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.REFLECTION && r.target().equals(Optional.of(new MethodId("Concat$Target","reached","()V")))));
        assertTrue(calls(result,"Concat$Target","reached"));
    }
    @Test void missingHookAncestorKeepsKnownNativeHooksAndTheQueryReason() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("NativeQuery.java","""
                public class NativeQuery {
                  public static class Parent {}
                  public static class Child extends Parent implements java.io.Serializable {private void readObject(java.io.ObjectInputStream in){seen();}}
                  static void seen(){}
                  public static Object run(java.io.ObjectInputStream in)throws Exception{return in.readObject();}
                }
                """));
        Path json=temp.resolve("native.json");Files.writeString(json,"""
                {"source":"compiled fixture relationships","basis":"BINDING","entry":{"owner":"NativeQuery","name":"run","descriptor":"(Ljava/io/ObjectInputStream;)Ljava/lang/Object;","arguments":[{"ref":"stream"}]},"objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"child"}},{"id":"child","type":"NativeQuery$Child"}]}
                """);
        Files.delete(classes.resolve("NativeQuery$Parent.class"));
        var result=scan(classes,"NativeQuery","run","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;",Optional.of(StaticData.read(json)));
        assertTrue(calls(result,"NativeQuery","seen"));
        assertTrue(result.findings().stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));

    }
    @Test void storesRaiseKnownJvmExceptionsAndOnlyNormalPathsContinue() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Stores.java","""
                public class Stores {
                  public static class Box {Object value;}
                  static void ok(){} static void bad(){}
                  public static void field(){Box b=null;try{b.value="x";bad();}catch(NullPointerException e){ok();}}
                  public static void nullArray(){Object[] a=null;try{a[0]="x";bad();}catch(NullPointerException e){ok();}}
                  public static void bounds(){Object[] a=new Object[1];try{a[1]="x";bad();}catch(ArrayIndexOutOfBoundsException e){ok();}}
                  public static void incompatible(){Object[] a=new String[1];try{a[0]=new Object();bad();}catch(ArrayStoreException e){ok();}}
                  public static void valid(){Object[] a=new String[1];a[0]="x";Box b=new Box();b.value=a[0];ok();}
                  public static void unhandled(){Box b=null;b.value="x";bad();}
                }
                """));
        for(String method:List.of("field","nullArray","bounds","incompatible","valid")) {
            var result=scan(classes,"Stores",method,"()V");
            assertTrue(calls(result,"Stores","ok"),method+": "+result.limitations());
            assertFalse(calls(result,"Stores","bad"),method);
        }
        assertFalse(calls(scan(classes,"Stores","unhandled","()V"),"Stores","bad"));
    }
}
