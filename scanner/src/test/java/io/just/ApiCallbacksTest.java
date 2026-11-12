package io.just;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

/** Exercises API callback targets and return/exception flow using bytecode only. */
class ApiCallbacksTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String owner,String entry,String descriptor)throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId(owner,entry,descriptor)));
        }
    }
    private Set<String> targets(ScanResult result,String owner) {
        Set<String> targets=new HashSet<>();result.relations().forEach(r -> r.target().filter(t -> t.owner().equals(owner)).ifPresent(t -> targets.add(t.name())));return targets;
    }
    @Test void privilegedReturnsUseTheActualInheritedOrLambdaActionAndComposeWithReflection()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Actions.java","""
                import java.security.*;
                public class Actions {
                  public static class Base implements PrivilegedAction<String> {public String run(){return "hit";}}
                  public static class Inherited extends Base {}
                  public static class Named implements PrivilegedAction<String> {String name;public Named(String name){this.name=name;}public String run(){return name;}}
                  public static class Metadata implements PrivilegedAction<java.lang.reflect.Method> {public java.lang.reflect.Method run(){try{return Target.class.getMethod("hit");}catch(NoSuchMethodException missing){throw new IllegalStateException(missing);}}}
                  public static class Handler implements java.lang.reflect.InvocationHandler {public Object invoke(Object proxy,java.lang.reflect.Method method,Object[] arguments){return "hit";}}
                  public static class Target {public static void hit(){}public static void unrelated(){}public static void pair(String first,String second){}}
                  static void use(Object name)throws Exception {Target.class.getMethod((String)name).invoke(null);}
                  static String invoke(Named action){return AccessController.doPrivileged(action);}
                  public static void inherited()throws Exception {use(AccessController.doPrivileged(new Inherited()));}
                  public static void captured()throws Exception {String prefix="h";use(AccessController.doPrivileged((PrivilegedAction<String>)()->prefix+"it"));}
                  public static void reflected()throws Exception {use(AccessController.class.getMethod("doPrivileged",PrivilegedAction.class).invoke(null,new Object[]{new Inherited()}));}
                  public static void metadata()throws Exception {AccessController.doPrivileged(new Metadata()).invoke(null);}
                  public static void proxied()throws Exception {PrivilegedAction<?> action=(PrivilegedAction<?>)java.lang.reflect.Proxy.newProxyInstance(Actions.class.getClassLoader(),new Class[]{PrivilegedAction.class},new Handler());use(AccessController.doPrivileged(action));}
                  public static void paired(){Target.pair(invoke(new Named("first")),invoke(new Named("second")));}
                }
                """));
        for(String entry:List.of("inherited","captured","reflected","metadata","proxied")) {
            var result=scan(classes,"Actions",entry,"()V");
            assertEquals(Set.of("hit"),targets(result,"Actions$Target"),entry);
        }
        var paired=scan(classes,"Actions","paired","()V");
        assertTrue(paired.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Actions$Target") && t.name().equals("pair")).isPresent())
                .anyMatch(r -> r.arguments().equals(List.of(new Literal("first"),new Literal("second")))));
    }
    @Test void nullAndThrowingActionsRetainJvmExceptionsAndBlockNormalSuccessors()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("AbruptActions.java","""
                import java.security.*;
                public class AbruptActions {
                  public static class Throwing implements PrivilegedAction<Object> {public Object run(){throw new IllegalStateException();}}
                  static void reached(){}static void impossible(){}
                  public static void nullAction(){try{AccessController.doPrivileged((PrivilegedAction<Object>)null);impossible();}catch(NullPointerException expected){reached();}}
                  public static void throwing(){try{AccessController.doPrivileged(new Throwing());impossible();}catch(IllegalStateException expected){reached();}}
                }
                """));
        for(String entry:List.of("nullAction","throwing")) {
            var result=scan(classes,"AbruptActions",entry,"()V");
            assertTrue(targets(result,"AbruptActions").contains("reached"),entry);
            assertFalse(targets(result,"AbruptActions").contains("impossible"),entry);
        }
    }
    @Test void unresolvedActionRequiresItsReceiverWithoutSelectingUnrelatedImplementations()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("UnknownAction.java","""
                import java.security.*;
                public class UnknownAction {
                  public static class Unrelated implements PrivilegedAction<Object> {public Object run(){return "unrelated";}}
                  public static Object run(PrivilegedAction<?> action){return AccessController.doPrivileged(action);}
                }
                """));
        var result=scan(classes,"UnknownAction","run","(Ljava/security/PrivilegedAction;)Ljava/lang/Object;");
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.RECEIVER_TYPE));
        assertTrue(targets(result,"UnknownAction$Unrelated").isEmpty());

    }
    @Test void aTargetClassWithTheSameApiSignatureKeepsItsOwnBody()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of(
                "java/security/AccessController.java","package java.security;public class AccessController {public static <T>T doPrivileged(PrivilegedAction<T> action){return null;}}",
                "OwnApi.java","""
                import java.security.*;
                public class OwnApi {
                  static void impossible(){}
                  public static void run(){AccessController.doPrivileged((PrivilegedAction<Object>)()->{impossible();return null;});}
                }
                """));
        var result=scan(classes,"OwnApi","run","()V");
        assertTrue(targets(result,"java/security/AccessController").contains("doPrivileged"));
        assertFalse(targets(result,"OwnApi").contains("impossible"));
    }
    @Test void aMissingActionAncestorRetainsItsCallbackAndDependencyReason()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("MissingAction.java","""
                import java.security.*;
                public class MissingAction {
                  public static class Parent implements PrivilegedAction<Object> {public Object run(){return "hidden";}}
                  public static class Child extends Parent {}
                  public static Object run(){return AccessController.doPrivileged(new Child());}
                }
                """));
        java.nio.file.Files.delete(classes.resolve("MissingAction$Parent.class"));
        var result=scan(classes,"MissingAction","run","()Ljava/lang/Object;");
        assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.DYNAMIC_CALL && r.target().filter(t -> t.owner().equals("MissingAction$Child") && t.name().equals("run")).isPresent())
                .anyMatch(r -> r.supports().stream().flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY)));
        assertTrue(result.inputRequirements().isEmpty(),"an exact receiver with a missing ancestor needs dependencies, not a replacement input type");
    }
    private Path checkedActions()throws Exception {
        return BytecodeFixtures.compile(temp,8,Map.of("CheckedActions.java","""
                import java.security.*;import java.lang.reflect.*;import java.io.*;
                public class CheckedActions {
                  static void good(){}static void wrong(){}
                  public static void throwing()throws IOException {throw new IOException();}
                  public static void checked(){PrivilegedExceptionAction<Object> action=()->{throw new IOException();};try{AccessController.doPrivileged(action);wrong();}catch(PrivilegedActionException expected){if(expected.getException() instanceof IOException)good();else wrong();}}
                  public static void runtime(){PrivilegedExceptionAction<Object> action=()->{throw new IllegalStateException();};try{AccessController.doPrivileged(action);wrong();}catch(IllegalStateException expected){good();}catch(PrivilegedActionException wrong){wrong();}}
                  public static void error(){PrivilegedExceptionAction<Object> action=()->{throw new AssertionError();};try{AccessController.doPrivileged(action);wrong();}catch(AssertionError expected){good();}catch(PrivilegedActionException wrong){wrong();}}
                  public static void nil(){try{AccessController.doPrivileged((PrivilegedExceptionAction<Object>)null);wrong();}catch(NullPointerException expected){good();}catch(PrivilegedActionException wrong){wrong();}}
                  public static void normal()throws Exception {if("good".equals(AccessController.doPrivileged((PrivilegedExceptionAction<String>)()->"good")))good();else wrong();}
                  public static void reflected()throws Exception {Method method=AccessController.class.getMethod("doPrivileged",PrivilegedExceptionAction.class);Object[] args={(PrivilegedExceptionAction<Object>)()->{throw new IOException();}};try{method.invoke(null,args);wrong();}catch(InvocationTargetException expected){Throwable cause=expected.getCause();if(cause instanceof PrivilegedActionException && ((PrivilegedActionException)cause).getException() instanceof IOException)good();else wrong();}}
                  public static void reverse(){PrivilegedExceptionAction<Object> action=()->{CheckedActions.class.getMethod("throwing").invoke(null);return null;};try{AccessController.doPrivileged(action);wrong();}catch(PrivilegedActionException expected){Exception cause=expected.getException();if(cause instanceof InvocationTargetException && cause.getCause() instanceof IOException)good();else wrong();}}
                }
                """));
    }
    @Test void checkedActionsWrapOnlyCheckedExceptionsAndKeepNormalValues()throws Exception {
        Path classes=checkedActions();
        for(String entry:List.of("checked","runtime","error","nil","normal")) {
            var result=scan(classes,"CheckedActions",entry,"()V");
            var calls=targets(result,"CheckedActions");
            assertTrue(calls.contains("good"),entry);assertFalse(calls.contains("wrong"),entry);
        }
    }
    @Test void reflectionAndPrivilegedWrappingRetainTheirNestingOrder()throws Exception {
        Path classes=checkedActions();
        for(String entry:List.of("reflected","reverse")) {
            var result=scan(classes,"CheckedActions",entry,"()V");var calls=targets(result,"CheckedActions");
            assertTrue(calls.contains("good"),entry);assertFalse(calls.contains("wrong"),entry);
        }
    }
    @Test void missingExceptionHierarchyKeepsTheWrappingDecisionPending()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("MissingException.java","""
                import java.security.*;
                public class MissingException {
                  public static class Parent extends Exception{}public static class Child extends Parent{}
                  public static class Action implements PrivilegedExceptionAction<Object> {public Object run()throws Exception {throw new Child();}}
                  static void checked()throws java.io.IOException {Runtime.getRuntime().exec("symbolic");}
                  static void direct()throws java.io.IOException {Runtime.getRuntime().exec("symbolic");}
                  public static void run()throws Exception {Action action=new Action();try{AccessController.doPrivileged(action);}catch(PrivilegedActionException maybe){checked();}catch(Exception maybe){direct();}}
                }
                """));
        java.nio.file.Files.delete(classes.resolve("MissingException$Parent.class"));
        var result=scan(classes,"MissingException","run","()V");
        var impacts=result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).toList();
        assertFalse(impacts.isEmpty());

        assertTrue(impacts.stream().anyMatch(f -> f.gaps().stream().anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY)),"the necessary closure must retain missing hierarchy evidence even when control facts are shared");
    }
}
