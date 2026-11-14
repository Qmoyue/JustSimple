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
    @Test void handlersNeedAnExceptionalOperationButKeepRealThrows()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("CatchFlow.java","""
                public class CatchFlow {
                  static void yes(){} static void no(){} static void use(int value){}
                  public static void safe(){try{int value=1;}catch(ArithmeticException impossible){no();}yes();}
                  public static void zero(){int divisor=0;try{use(1/divisor);no();}catch(ArithmeticException expected){yes();}}
                  public static void unknown(int divisor){try{use(1/divisor);no();}catch(ArithmeticException possible){yes();}}
                  public static void nested(int divisor){boolean enabled=false;if(enabled){try{use(1/divisor);}catch(ArithmeticException ignored){}no();}yes();}
                  public static void monitor(Object lock){try{synchronized(lock){}}catch(NullPointerException possible){yes();}}
                }
                """));
        var safe=scan(classes,"CatchFlow","safe","()V");assertTrue(calls(safe,"CatchFlow","yes"));assertFalse(calls(safe,"CatchFlow","no"));
        var zero=scan(classes,"CatchFlow","zero","()V");assertTrue(calls(zero,"CatchFlow","yes"));assertFalse(calls(zero,"CatchFlow","no"));
        var unknown=scan(classes,"CatchFlow","unknown","(I)V");assertTrue(calls(unknown,"CatchFlow","yes"));assertTrue(calls(unknown,"CatchFlow","no"));
        var nested=scan(classes,"CatchFlow","nested","(I)V");assertTrue(calls(nested,"CatchFlow","yes"));assertFalse(calls(nested,"CatchFlow","no"));
        assertTrue(calls(scan(classes,"CatchFlow","monitor","(Ljava/lang/Object;)V"),"CatchFlow","yes"));
    }
    @Test void interfaceEnumerationUsesOnlyTheKnownDirectInterfaces()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Interfaces.java","""
                public class Interfaces {
                  interface Marker {}
                  static class Parent implements Marker {}
                  static class Child extends Parent {}
                  static void yes(){} static void no(){}
                  public static void direct(){if(Parent.class.getInterfaces().length==1)yes();else no();}
                  public static void inherited(){if(Child.class.getInterfaces().length==1)no();else yes();}
                  public static void array(){if(String[].class.getInterfaces().length==2)yes();else no();}
                  public static void primitive(){if(int.class.getInterfaces().length==0)yes();else no();}
                  public static void element(){if(Parent.class.getInterfaces()[0]==Marker.class)yes();else no();}
                  public static void mutation(){Class<?>[] values=Parent.class.getInterfaces();values[0]=String.class;if(values[0]==String.class)yes();else no();}
                  public static void unknown(Class<?> type){if(type.getInterfaces().length==1)yes();else no();}
                }
                """));
        for(String entry:List.of("direct","inherited","array","primitive","element","mutation")) {
            var result=scan(classes,"Interfaces",entry,"()V");
            assertTrue(calls(result,"Interfaces","yes"),entry);
            assertFalse(calls(result,"Interfaces","no"),entry);
        }
        var unknown=scan(classes,"Interfaces","unknown","(Ljava/lang/Class;)V");
        assertTrue(calls(unknown,"Interfaces","yes"));assertTrue(calls(unknown,"Interfaces","no"));
        Files.delete(classes.resolve("Interfaces$Parent.class"));
        var missing=scan(classes,"Interfaces","direct","()V");
        assertTrue(calls(missing,"Interfaces","yes"));assertTrue(calls(missing,"Interfaces","no"));
        assertTrue(missing.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Interfaces") && t.name().equals("yes")).isPresent())
                .flatMap(r -> r.supports().stream()).flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
    }
    @Test void applicationClassNamedLikeThePlatformKeepsItsOwnBody()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Shadow.java","""
                public class Shadow {
                  static void yes(){} static void no(){}
                  public static void run(){if(String.class.getInterfaces().length==0)yes();else no();}
                }
                """));
        var writer=new org.objectweb.asm.ClassWriter(org.objectweb.asm.ClassWriter.COMPUTE_MAXS);
        writer.visit(org.objectweb.asm.Opcodes.V1_8,org.objectweb.asm.Opcodes.ACC_PUBLIC,"java/lang/Class",null,"java/lang/Object",null);
        var method=writer.visitMethod(org.objectweb.asm.Opcodes.ACC_PUBLIC,"getInterfaces","()[Ljava/lang/Class;",null,null);
        method.visitCode();method.visitInsn(org.objectweb.asm.Opcodes.ICONST_0);method.visitTypeInsn(org.objectweb.asm.Opcodes.ANEWARRAY,"java/lang/Class");
        method.visitInsn(org.objectweb.asm.Opcodes.ARETURN);method.visitMaxs(0,0);method.visitEnd();writer.visitEnd();
        Path shadow=classes.resolve("java/lang/Class.class");Files.createDirectories(shadow.getParent());Files.write(shadow,writer.toByteArray());
        var result=scan(classes,"Shadow","run","()V");
        assertTrue(calls(result,"Shadow","yes"));assertFalse(calls(result,"Shadow","no"));
    }
    @Test void classCastPreservesSuccessfulAndExceptionalPaths()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ClassCasts.java","""
                public class ClassCasts {
                  static class Parent {} static class Child extends Parent {}
                  static void yes(){} static void no(){}
                  public static void compatible(){try{Parent.class.cast(new Child());yes();}catch(ClassCastException e){no();}}
                  public static void incompatible(){try{Child.class.cast(new Parent());no();}catch(ClassCastException e){yes();}}
                  public static void nullValue(){try{Child.class.cast(null);yes();}catch(ClassCastException e){no();}}
                  public static void unknown(Object value){try{Child.class.cast(value);yes();}catch(ClassCastException e){no();}}
                }
                """));
        for(String entry:List.of("compatible","incompatible","nullValue")) {
            var result=scan(classes,"ClassCasts",entry,"()V");
            assertTrue(calls(result,"ClassCasts","yes"),entry);assertFalse(calls(result,"ClassCasts","no"),entry);
        }
        var unknown=scan(classes,"ClassCasts","unknown","(Ljava/lang/Object;)V");
        assertTrue(calls(unknown,"ClassCasts","yes"));assertTrue(calls(unknown,"ClassCasts","no"));
    }
    @Test void declaredFieldLookupDistinguishesOwnMissingAndInheritedMembers()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("FieldLookup.java","""
                public class FieldLookup {
                  static class Parent {public int inherited;} static class Child extends Parent {private String own;}
                  static void yes(){} static void no(){}
                  public static void found(){try{Child.class.getDeclaredField("own");yes();}catch(NoSuchFieldException e){no();}}
                  public static void absent(){try{Child.class.getDeclaredField("missing");no();}catch(NoSuchFieldException e){yes();}}
                  public static void inherited(){try{Child.class.getDeclaredField("inherited");no();}catch(NoSuchFieldException e){yes();}}
                  public static void unknown(String name){try{Child.class.getDeclaredField(name);yes();}catch(NoSuchFieldException e){no();}}
                }
                """));
        for(String entry:List.of("found","absent","inherited")) {
            var result=scan(classes,"FieldLookup",entry,"()V");
            assertTrue(calls(result,"FieldLookup","yes"),entry);assertFalse(calls(result,"FieldLookup","no"),entry);
        }
        var unknown=scan(classes,"FieldLookup","unknown","(Ljava/lang/String;)V");
        assertTrue(calls(unknown,"FieldLookup","yes"));assertTrue(calls(unknown,"FieldLookup","no"));
        Files.delete(classes.resolve("FieldLookup$Child.class"));
        var missing=scan(classes,"FieldLookup","found","()V");
        assertTrue(calls(missing,"FieldLookup","yes"));assertTrue(calls(missing,"FieldLookup","no"));
        assertTrue(missing.relations().stream().flatMap(r -> r.supports().stream()).flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
    }
    @Test void proxyClassChecksUseTheActualClassOrigin()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ProxyCheck.java","""
                import java.lang.reflect.*;
                public class ProxyCheck {
                  interface Face {void call();}
                  static class Handler implements InvocationHandler {public Object invoke(Object proxy,Method method,Object[] arguments){return null;}}
                  static void yes(){} static void no(){}
                  public static void generated(){Object value=Proxy.newProxyInstance(Face.class.getClassLoader(),new Class[]{Face.class},new Handler());if(Proxy.isProxyClass(value.getClass()))yes();else no();}
                  public static void ordinary(){if(Proxy.isProxyClass(String.class))no();else yes();}
                  public static void unknown(Class<?> value){if(Proxy.isProxyClass(value))yes();else no();}
                }
                """));
        for(String entry:List.of("generated","ordinary")) {
            var result=scan(classes,"ProxyCheck",entry,"()V");
            assertTrue(calls(result,"ProxyCheck","yes"),entry);assertFalse(calls(result,"ProxyCheck","no"),entry);
        }
        var unknown=scan(classes,"ProxyCheck","unknown","(Ljava/lang/Class;)V");
        assertTrue(calls(unknown,"ProxyCheck","yes"));assertTrue(calls(unknown,"ProxyCheck","no"));
    }
    @Test void constructorCountsUseDeclaredVisibilityAndKeepUnknownClassesUnresolved()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ConstructorCounts.java","""
                public class ConstructorCounts {
                  static class Type {public Type(){} private Type(int number){}}
                  static void yes(){} static void no(){}
                  public static void known(){if(Type.class.getDeclaredConstructors().length==2 && Type.class.getConstructors().length==1)yes();else no();}
                  public static void unknown(Class<?> type){if(type.getConstructors().length==1)yes();else no();}
                }
                """));
        var known=scan(classes,"ConstructorCounts","known","()V");
        assertTrue(calls(known,"ConstructorCounts","yes"));assertFalse(calls(known,"ConstructorCounts","no"));
        var unknown=scan(classes,"ConstructorCounts","unknown","(Ljava/lang/Class;)V");
        assertTrue(calls(unknown,"ConstructorCounts","yes"));assertTrue(calls(unknown,"ConstructorCounts","no"));
        Files.delete(classes.resolve("ConstructorCounts$Type.class"));
        var missing=scan(classes,"ConstructorCounts","known","()V");
        assertTrue(calls(missing,"ConstructorCounts","yes"));assertTrue(calls(missing,"ConstructorCounts","no"));
        assertTrue(missing.relations().stream().flatMap(r -> r.supports().stream()).flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
    }
    @Test void reflectedFieldAccessFlagsBelongToTheSelectedFieldObject()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("FieldAccess.java","""
                import java.lang.reflect.*;
                public class FieldAccess {
                  static class Target {private int value;}
                  static void yes(){} static void no(){}
                  public static void fresh()throws Exception {Field field=Target.class.getDeclaredField("value");if(field.isAccessible())no();else yes();}
                  public static void changed()throws Exception {Field field=Target.class.getDeclaredField("value");field.setAccessible(true);if(field.isAccessible())yes();else no();}
                  public static void separate()throws Exception {Field first=Target.class.getDeclaredField("value"),second=Target.class.getDeclaredField("value");first.setAccessible(true);if(second.isAccessible())no();else yes();}
                }
                """));
        for(String entry:List.of("fresh","separate")) {
            var result=scan(classes,"FieldAccess",entry,"()V");
            assertTrue(calls(result,"FieldAccess","yes"),entry);assertFalse(calls(result,"FieldAccess","no"),entry);
        }
        var changed=scan(classes,"FieldAccess","changed","()V");assertTrue(calls(changed,"FieldAccess","yes"));
        assertTrue(changed.relations().stream().flatMap(r -> r.supports().stream()).flatMap(s -> s.gaps().stream())
                .anyMatch(g -> g.kind()==GapKind.CONTROL_CONDITION && g.detail().contains("access suppression")));
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
