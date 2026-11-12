package io.just;

import io.just.knowledge.EntryPoints;

import io.just.analysis.Analyzer;
import io.just.analysis.ScanResult;
import io.just.analysis.ScanResult.*;
import io.just.input.Inputs;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.*;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import static org.junit.jupiter.api.Assertions.*;

/** The fixture compiler emits bytecode only. No target classes are loaded or invoked. */
class DemandTest {
    @TempDir Path temp;
    private final Path jdk=Path.of(System.getProperty("java.home"));

    private Path compile(String name,String source) throws IOException {
        return BytecodeFixtures.compile(temp,8,Map.of(name+".java",source));
    }
    private ScanResult scan(Path classes,String owner,String name,String descriptor,boolean demand,Analyzer.Limits limits) throws IOException {
        try(Inputs inputs=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);
            return new Analyzer(program,new Mechanisms(program),limits,demand)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId(owner,name,descriptor)));
        }
    }
    private ScanResult scan(Path classes,String owner,String name,String descriptor) throws IOException {
        return scan(classes,owner,name,descriptor,true,Analyzer.Limits.defaults());
    }
    private Set<String> targets(ScanResult result,Kind kind) {
        return result.relations().stream().filter(r -> r.kind()==kind).flatMap(r -> r.target().stream()).map(Object::toString).collect(Collectors.toSet());
    }
    @Test void repeatedQueriesReuseFactsWithoutChargingInputBudgetsAgain() throws Exception {
        Path classes=compile("Queries","public class Queries {public static String value(String s){return s;}}");
        try(Inputs inputs=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);long before=inputs.summary().bytesRead();
            Program.MethodId method=new Program.MethodId("Queries","value","(Ljava/lang/String;)Ljava/lang/String;");
            Program.Facts facts=program.facts(method);
            Program.ClassInfo type=program.type("java/lang/String").orElseThrow();
            assertSame(facts,program.facts(method));assertSame(type,program.type("java/lang/String").orElseThrow());
            assertFalse(facts.actions().isEmpty());
            assertEquals(1,inputs.summary().platformClasses());
            assertEquals(inputs.find("java/lang/String").orElseThrow().bytes().length,inputs.summary().bytesRead()-before);
        }
    }

    @Test void exhaustedInputBudgetIsNotAProofOfMissingDependency() throws IOException {
        Path classes=compile("Budget","public class Budget {public static void run(){}}");
        long bytes=Files.size(classes.resolve("Budget.class"));
        try(Inputs inputs=Inputs.open(classes,List.of(),jdk,new Inputs.Limits(bytes+1,100,100,1,1<<20))) {
            Program program=new Program(inputs,20_000);
            var result=program.lookup(new Program.MethodId("java/lang/Object","toString","()Ljava/lang/String;"));
            assertFalse(result.absent());assertTrue(result.value().isEmpty());
            assertTrue(result.pending().stream().anyMatch(p -> p.cause()==Program.QueryCause.BUDGET));
            assertFalse(program.missingClasses().contains("java/lang/Object"),"a read frontier must not be recorded as a missing class");
        }
        try(Inputs inputs=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);
            var missing=program.lookup(new Program.MethodId("does/not/Exist","run","()V"));
            assertTrue(missing.pending().stream().anyMatch(p -> p.cause()==Program.QueryCause.MISSING_DEPENDENCY));
            assertFalse(missing.pending().stream().anyMatch(p -> p.cause()==Program.QueryCause.BUDGET));
        }
    }

    @Test void demandGuidancePreservesObjectArgumentAndBranchEvidence() throws IOException {
        Path classes=compile("Correlated","""
                public class Correlated {
                  public static class A {public void alpha(String s){} public void beta(String s){}}
                  public static class B {public void alpha(String s){} public void beta(String s){}}
                  private static void dispatch(Object receiver,String name,String value)throws Exception {
                    receiver.getClass().getMethod(name,new Class[]{String.class}).invoke(receiver,new Object[]{value});
                  }
                  public static void run(boolean choice)throws Exception {
                    if(choice)dispatch(new A(),"alpha","first");else dispatch(new B(),"beta","second");
                  }
                }
                """);
        ScanResult one=scan(classes,"Correlated","run","(Z)V",true,Analyzer.Limits.defaults());
        assertEquals(Execution.FINISHED,one.execution(),one.limitations().toString());
        assertEquals(Set.of("Correlated$A#alpha(Ljava/lang/String;)V","Correlated$B#beta(Ljava/lang/String;)V"),targets(one,Kind.REFLECTION));
        ScanResult plain=scan(classes,"Correlated","run","(Z)V",false,Analyzer.Limits.defaults());
        assertEquals(targets(one,Kind.REFLECTION),targets(plain,Kind.REFLECTION));
    }

    @Test void relationBudgetRetainsTheReachedImpactAndLocatesUnprocessedInstructions() throws IOException {
        String noise=java.util.stream.IntStream.range(0,80).mapToObj(i -> "pass(\"value"+i+"\");").collect(Collectors.joining());
        Path classes=compile("RelationCut","public class RelationCut {static String pass(String value){return value;}public static void run()throws Exception {Runtime.getRuntime().exec(\"first\");"+noise+"}}");
        ScanResult result=scan(classes,"RelationCut","run","()V",false,new Analyzer.Limits(500,2000,20,32,100,64));
        assertEquals(Execution.TRUNCATED,result.execution());
        assertTrue(result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT && result.relations().get(f.path().get(f.path().size()-1)).target().filter(t -> t.name().equals("exec")).isPresent()));
        assertTrue(result.breakpoints().stream().anyMatch(b -> b.reason()==GapKind.BUDGET && b.use().method().owner().equals("RelationCut")),"unprocessed bytecode remains a located budget frontier");
        assertTrue(result.statistics().workItems()<result.analysisBudgets().steps(),"a relation cutoff stops further expansion without spending the remaining work budget");
    }

    @Test void truncatedWorkBudgetRetainsConditionalFindings() throws IOException {
        Path classes=compile("WorkBudget","""
                public class WorkBudget {
                  public static void run(java.io.ObjectInputStream input)throws Exception {input.readObject();NOISE}
                }
                """.replace("NOISE","System.nanoTime();".repeat(100)));
        Analyzer.Limits d=Analyzer.Limits.defaults(),small=new Analyzer.Limits(d.contexts(),15,d.depth(),d.relations(),d.findings(),d.alternatives());
        ScanResult one=scan(classes,"WorkBudget","run","(Ljava/io/ObjectInputStream;)V",true,small);
        assertEquals(Execution.TRUNCATED,one.execution());assertFalse(one.findings().isEmpty());

        assertTrue(one.statistics().workItems()<=small.steps());
        assertTrue(one.limitations().stream().anyMatch(reason -> reason.contains("scheduled instruction budget") || reason.contains("work budget")));
    }

    @Test void staticInitializerAndFiniteBuilderRecoverLookupWithoutFacts() throws IOException {
        Path classes=compile("Initialized","""
                public class Initialized {
                  private static String owner;
                  private static String name;
                  static {owner=new StringBuilder("Initialized$").append("Target").toString();name="rea".concat("ched");}
                  public static class Target {public static void reached(){}}
                  public static void run()throws Exception {Class.forName(owner).getMethod(name,new Class[0]).invoke(null,new Object[0]);}
                }
                """);
        ScanResult result=scan(classes,"Initialized","run","()V");
        assertEquals(Execution.FINISHED,result.execution(),result.limitations().toString());
        assertEquals(Set.of("Initialized$Target#reached()V"),targets(result,Kind.REFLECTION));

    }

    @Test void methodArrayIndexDoesNotInventRuntimeOrder() throws IOException {
        Path classes=compile("MethodOrder","""
                public class MethodOrder {
                  public static class Target {public static void alpha(){}public static void beta(){}}
                  public static void run()throws Exception {Target.class.getDeclaredMethods()[0].invoke(null,new Object[0]);}
                }
                """);
        ScanResult result=scan(classes,"MethodOrder","run","()V");
        assertEquals(Set.of("MethodOrder$Target#alpha()V","MethodOrder$Target#beta()V"),targets(result,Kind.REFLECTION));
        assertFalse(result.findings().isEmpty());
        assertTrue(result.findings().stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.CONTROL_CONDITION && g.detail().contains("array order")));
    }

    @Test void recursiveClassInitializationUsesOneLogicalInitializationOrder() throws IOException {
        Path classes=compile("RecursiveInit","""
                public class RecursiveInit {
                  public static class A {static String owner=B.owner;static int count;}
                  public static class B {static String owner="RecursiveInit$Target";static int prior=A.count;}
                  public static class Target {public static void reached(){}}
                  public static void run()throws Exception {String a=A.owner;String b=B.owner;Class.forName(a).getMethod("reached",new Class[0]).invoke(null,new Object[0]);}
                }
                """);
        ScanResult one=scan(classes,"RecursiveInit","run","()V");
        assertEquals(Execution.FINISHED,one.execution(),one.limitations().toString());
        assertEquals(Set.of("RecursiveInit$Target#reached()V"),targets(one,Kind.REFLECTION));
    }

    @Test void defaultSuperinterfacesInitializeWithClassesButNotWithChildInterfaces() throws IOException {
        Path classes=compile("InterfaceInit","""
                public class InterfaceInit {
                  static class State {static String owner;}
                  interface Parent {String INIT=boot();static String boot(){State.owner="InterfaceInit$Target";return "ready";}default void marker(){}}
                  interface Child extends Parent {String INIT_CHILD=bootChild();static String bootChild(){return "child";}}
                  public static class Impl implements Child {}
                  public static class Target {public static void reached(){}}
                  public static void viaClass()throws Exception {new Impl();Class.forName(State.owner).getMethod("reached",new Class[0]).invoke(null,new Object[0]);}
                  public static void viaInterface()throws Exception {String trigger=Child.INIT_CHILD;Class.forName(State.owner).getMethod("reached",new Class[0]).invoke(null,new Object[0]);}
                }
                """);
        assertEquals(Set.of("InterfaceInit$Target#reached()V"),targets(scan(classes,"InterfaceInit","viaClass","()V"),Kind.REFLECTION));
        assertTrue(targets(scan(classes,"InterfaceInit","viaInterface","()V"),Kind.REFLECTION).isEmpty());
    }

    @Test void arrayCloneQueryDoesNotLookForANonexistentArrayClassfile() throws IOException {
        Path classes=compile("ArrayMetadata","public class ArrayMetadata {public static Object copy(String[] values){return values.clone();}}");
        try(Inputs input=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);var query=program.lookup(new Program.MethodId("[Ljava/lang/String;","clone","()Ljava/lang/Object;"));
            assertTrue(query.value().orElseThrow().isPublic());assertTrue(query.pending().isEmpty());assertTrue(program.missingClasses().isEmpty());
        }
    }

    @Test void knownNullLookupNamesAreExceptionsRatherThanConditionalMemberCandidates() throws IOException {
        Path classes=compile("NullLookup","""
                public class NullLookup {
                  public static class Target {public static void reached(){}}
                  public static void run()throws Exception {Target.class.getMethod(null,new Class[0]).invoke(null,new Object[0]);}
                }
                """);
        ScanResult result=scan(classes,"NullLookup","run","()V");
        assertTrue(result.findings().isEmpty());assertTrue(targets(result,Kind.REFLECTION).isEmpty());assertTrue(result.inputRequirements().isEmpty());
    }

    @Test void publicMethodOnNonpublicForeignClassStillRequiresAccessEvidence() throws IOException {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ForeignLookup.java","""
                public class ForeignLookup {
                  public static void run()throws Exception {Class.forName("hidden.Hidden").getMethod("reached",new Class[0]).invoke(null,new Object[0]);}
                }
                ""","hidden/Hidden.java","package hidden; class Hidden {public static void reached(){}}"));
        ScanResult result=scan(classes,"ForeignLookup","run","()V");
        assertEquals(Set.of("hidden.Hidden#reached()V"),targets(result,Kind.REFLECTION));
        assertTrue(result.findings().stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.INPUT_BINDING && g.detail().contains("declaring class")));
    }

    @Test void constrainedClassAndNameDoNotRequireAnExactArgumentArrayToDiscoverCandidates() throws IOException {
        Path classes=compile("UnknownArguments","""
                public class UnknownArguments {
                  public static class Target {public static void accept(String text){}public static void accept(int number){}public static void other(){}}
                  public static void run(Class[] signature,Object[] arguments)throws Exception {Target.class.getMethod("accept",signature).invoke(null,arguments);}
                }
                """);
        ScanResult result=scan(classes,"UnknownArguments","run","([Ljava/lang/Class;[Ljava/lang/Object;)V");
        assertEquals(Set.of("UnknownArguments$Target#accept(Ljava/lang/String;)V","UnknownArguments$Target#accept(I)V"),targets(result,Kind.REFLECTION));

        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.METHOD_TYPES));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().slot().filter(s -> s instanceof Index i && i.index()==0).isPresent()));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().slot().filter(s -> s instanceof Length).isPresent()));
        assertTrue(result.inputRequirements().stream().filter(r -> r.needed().slot().isPresent()).allMatch(r -> r.source().isPresent()));
    }

    @Test void methodMetadataFiltersStayBoundToTheirDeclaringClassAndSignature() throws IOException {
        Path classes=compile("MethodFilter","""
                import java.lang.reflect.Method;
                public class MethodFilter {
                  public static class Target {public static void alpha(){}public static void beta(){}public static void alpha(String ignored){}}
                  public static class Other {public static void alpha(){}}
                  public static void run()throws Exception {
                    for(Method method:Target.class.getDeclaredMethods())
                      if(method.getName().equals("alpha") && method.getParameterCount()==0)method.invoke(null,new Object[0]);
                  }
                }
                """);
        ScanResult result=scan(classes,"MethodFilter","run","()V");
        assertEquals(Set.of("MethodFilter$Target#alpha()V"),targets(result,Kind.REFLECTION),result.limitations().toString());
    }

    private Path handles() throws IOException {
        return compile("ExactHandles","""
                import java.lang.invoke.*;
                public class ExactHandles {
                  public static class Target {
                    public static String echo(String value){return value;}
                    public String instance(String value){return value;}
                  }
                  public static void exactStatic()throws Throwable {
                    MethodHandle h=MethodHandles.publicLookup().findStatic(Target.class,"echo",MethodType.methodType(String.class,String.class));
                    String value=(String)h.invokeExact("ordinary");
                  }
                  public static void exactVirtual()throws Throwable {
                    MethodHandle h=MethodHandles.lookup().findVirtual(Target.class,"instance",MethodType.methodType(String.class,String.class));
                    String value=(String)h.invokeExact(new Target(),"ordinary");
                  }
                  public static void wrongLookupType()throws Throwable {
                    MethodHandle h=MethodHandles.publicLookup().findStatic(Target.class,"echo",MethodType.methodType(Object.class,String.class));
                    String value=(String)h.invokeExact("ordinary");
                  }
                  public static void wrongInvocationType()throws Throwable {
                    MethodHandle h=MethodHandles.publicLookup().findStatic(Target.class,"echo",MethodType.methodType(String.class,String.class));
                    Object value=(Object)h.invokeExact("ordinary");
                  }
                  public static void wrongStaticKind()throws Throwable {
                    MethodHandle h=MethodHandles.publicLookup().findVirtual(Target.class,"echo",MethodType.methodType(String.class,String.class));
                    String value=(String)h.invokeExact(new Target(),"ordinary");
                  }
                  public static void unknownType(MethodType type)throws Throwable {
                    MethodHandle h=MethodHandles.publicLookup().findStatic(Target.class,"echo",type);
                    String value=(String)h.invokeExact("ordinary");
                  }
                }
                """);
    }

    @Test void exactHandlesUseActualLookupTypeAndVirtualReceiver() throws IOException {
        Path classes=handles();
        ScanResult statik=scan(classes,"ExactHandles","exactStatic","()V");
        assertEquals(Set.of("ExactHandles$Target#echo(Ljava/lang/String;)Ljava/lang/String;"),targets(statik,Kind.METHOD_HANDLE));

        ScanResult virtual=scan(classes,"ExactHandles","exactVirtual","()V");
        assertEquals(Set.of("ExactHandles$Target#instance(Ljava/lang/String;)Ljava/lang/String;"),targets(virtual,Kind.METHOD_HANDLE));
        assertTrue(virtual.relations().stream().filter(r -> r.kind()==Kind.METHOD_HANDLE && r.target().map(t -> t.owner().equals("ExactHandles$Target")).orElse(false))
                .allMatch(r -> r.receiver() instanceof ObjectValue o && o.type().equals("ExactHandles$Target") && r.arguments().equals(List.of(new Literal("ordinary")))));
    }

    @Test void incompatibleHandlesCannotBeRescuedByTheInvokeDescriptor() throws IOException {
        Path classes=handles();
        for(String entry:List.of("wrongLookupType","wrongInvocationType","wrongStaticKind")) {
            ScanResult result=scan(classes,"ExactHandles",entry,"()V");
            assertTrue(targets(result,Kind.METHOD_HANDLE).isEmpty(),entry+" must not create a target dispatch");
            assertTrue(result.findings().isEmpty(),entry+" has a proven exceptional lookup or invocation");
        }
        ScanResult unknown=scan(classes,"ExactHandles","unknownType","(Ljava/lang/invoke/MethodType;)V");
        assertTrue(targets(unknown,Kind.METHOD_HANDLE).isEmpty());
        assertFalse(unknown.findings().isEmpty());

    }
}
