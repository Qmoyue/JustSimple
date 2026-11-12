package io.just;

import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class ResolutionTest {
    @TempDir Path temp;
    private Inputs input(Path classes) throws Exception {return Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults());}
    @Test void reflectionOnArraysAndPrimitiveTypesUsesJvmMetadataRules() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Existing.java","public class Existing {}"));
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);
            for(String array:List.of("[I","[Ljava/lang/String;")) {
                assertEquals("java/lang/Object",program.reflect(array,"toString",List.of(),false).value().orElseThrow().id().owner());
                assertTrue(program.reflect(array,"clone",List.of(),false).absent());
                assertTrue(program.reflect(array,"toString",List.of(),true).absent());
            }
            for(String primitive:List.of("I","V")) {
                assertTrue(program.methods(primitive,false).pending().isEmpty());
                assertTrue(program.methods(primitive,false).value().orElseThrow().isEmpty());
            }
            assertTrue(program.missingClasses().isEmpty(),"arrays and primitive classes do not require classfiles with descriptor names");
        }
    }
    @Test void syntaxQueriesDistinguishMissingInputFromAnAbsentMember() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Existing.java","public class Existing {public void empty(){}}"));
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);
            var missing=program.calls(new MethodId("Missing","run","()V"));
            assertTrue(missing.value().isEmpty());assertFalse(missing.absent());
            assertTrue(missing.pending().stream().anyMatch(issue -> issue.cause()==QueryCause.MISSING_DEPENDENCY));
            assertTrue(program.calls(new MethodId("Existing","missing","()V")).absent());
            assertTrue(program.calls(new MethodId("Existing","empty","()V")).value().orElseThrow().isEmpty());
        }
    }
    @Test void publicInterfaceStaticsAreDeclaredMembersButAreNeverInherited() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Members.java","""
            public class Members {
              public interface Parent {static void interfaceStatic(){} default void inherited(){}}
              public interface Child extends Parent {}
              public static class Base {public static void classStatic(){}}
              public static class Receiver extends Base implements Child {}
            }
            """));
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);
            assertTrue(program.reflect("Members$Receiver","interfaceStatic",List.of(),false).absent());
            assertTrue(program.reflect("Members$Child","interfaceStatic",List.of(),false).absent());
            assertEquals("Members$Parent",program.reflect("Members$Parent","interfaceStatic",List.of(),false).value().orElseThrow().id().owner());
            assertEquals("Members$Base",program.reflect("Members$Receiver","classStatic",List.of(),false).value().orElseThrow().id().owner());
            assertEquals("Members$Parent",program.reflect("Members$Receiver","inherited",List.of(),false).value().orElseThrow().id().owner());
        }
    }
    @Test void methodHandlesRetainTheirInitiatingLoaderUntilTheTargetIsDefined() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Later.java","public class Later {public static void hit(){}}",
            "Host.java","public class Host {public static Runnable lambda(){return Later::hit;} public static java.lang.invoke.MethodHandle direct(){return null;}}"));
        var node=new org.objectweb.asm.tree.ClassNode();new org.objectweb.asm.ClassReader(Files.readAllBytes(classes.resolve("Host.class"))).accept(node,0);
        var direct=node.methods.stream().filter(m -> m.name.equals("direct")).findFirst().orElseThrow();direct.instructions.clear();
        direct.instructions.add(new org.objectweb.asm.tree.LdcInsnNode(new org.objectweb.asm.Handle(org.objectweb.asm.Opcodes.H_INVOKESTATIC,"Later","hit","()V",false)));
        direct.instructions.add(new org.objectweb.asm.tree.InsnNode(org.objectweb.asm.Opcodes.ARETURN));direct.maxStack=1;
        var writer=new org.objectweb.asm.ClassWriter(0);node.accept(writer);byte[] host=writer.toByteArray();
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);Object loader=new Object();
            int scope=program.define(loader,host,host,0,host.length,null).value().orElseThrow().loader();
            List<HandleConstant> handles=new ArrayList<>();
            for(String name:List.of("lambda","direct")) {
                String descriptor=name.equals("lambda")?"()Ljava/lang/Runnable;":"()Ljava/lang/invoke/MethodHandle;";
                for(Action action:program.facts(new MethodId("Host",name,descriptor,scope)).actions()) {
                    if(action instanceof Call call)call.bootstrap().ifPresent(bootstrap -> bootstrap.arguments().stream().filter(HandleConstant.class::isInstance).map(HandleConstant.class::cast).forEach(handles::add));
                    if(action instanceof Constant constant && constant.value() instanceof HandleConstant handle)handles.add(handle);
                }
            }
            assertEquals(2,handles.size());
            for(HandleConstant handle:handles)assertEquals(0,program.lookup(handle.target()).value().orElseThrow().id().loader());
            byte[] later=Files.readAllBytes(classes.resolve("Later.class"));program.define(loader,later,later,0,later.length,null);
            for(HandleConstant handle:handles)assertEquals(scope,program.lookup(handle.target()).value().orElseThrow().id().loader(),"a same-named input class cannot own a handle from the defined Host");
        }
    }
    @Test void inheritedMembersKeepTheDefiningScopeAtEveryHierarchyHop() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Base.java","public class Base {public int value;public String method(){return \"base\";}}","Parent.java","public class Parent extends Base {}","Child.java","public class Child extends Parent {}"));
        Path shadow=BytecodeFixtures.compile(temp,17,Map.of("Base.java","public class Base {public int value;public String method(){return \"shadow\";}public void wrong(){}}"));
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);Object loader=new Object();
            byte[] base=Files.readAllBytes(shadow.resolve("Base.class")),child=Files.readAllBytes(classes.resolve("Child.class"));
            int scope=program.define(loader,base,base,0,base.length,null).value().orElseThrow().loader();
            program.define(loader,child,child,0,child.length,null);
            assertEquals(0,program.lookup(new MethodId("Child","method","()Ljava/lang/String;",scope)).value().orElseThrow().id().loader());
            assertEquals(0,program.reflect("Child","method",List.of(),false,scope).value().orElseThrow().id().loader());
            assertEquals(0,program.lookupField(new FieldId("Child","value","I",scope)).value().orElseThrow().loader());
            assertTrue(program.methods("Child",false,scope).value().orElseThrow().stream().noneMatch(m -> m.id().name().equals("wrong")));
            assertTrue(program.lookup(new MethodId("Child","wrong","()V",scope)).absent());
            assertEquals(Optional.of(false),program.nestmates("Child",0,"Child",scope).value());
        }
    }
    @Test void mostSpecificDefaultAndCovariantReturnWinRegardlessOfClassfileOrder() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","""
            public class Fixture {
              public interface A {default Object value(){return null;}}
              public interface B extends A {default Object value(){return "b";}}
              public static class C implements A,B {}
              public static class Parent<T> {public T value(){return null;}}
              public static class Child extends Parent<String> {public String value(){return "child";}}
            }
            """));
        Path file=classes.resolve("Fixture$Child.class");
        var node=new org.objectweb.asm.tree.ClassNode();new org.objectweb.asm.ClassReader(Files.readAllBytes(file)).accept(node,0);
        node.methods.sort(Comparator.comparingInt(m -> (m.access & org.objectweb.asm.Opcodes.ACC_BRIDGE)!=0?0:1));
        var writer=new org.objectweb.asm.ClassWriter(0);node.accept(writer);Files.write(file,writer.toByteArray());
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);
            assertEquals("Fixture$B",program.lookup(new MethodId("Fixture$C","value","()Ljava/lang/Object;")).value().orElseThrow().id().owner());
            assertEquals("Fixture$B",program.reflect("Fixture$C","value",List.of(),false).value().orElseThrow().id().owner());
            assertEquals("()Ljava/lang/String;",program.reflect("Fixture$Child","value",List.of(),false).value().orElseThrow().id().descriptor());
            assertEquals("()Ljava/lang/String;",program.reflect("Fixture$Child","value",List.of(),true).value().orElseThrow().id().descriptor());
            assertTrue(program.reflect("Fixture$A","toString",List.of(),false).absent(),"reflection does not inherit Object members into an interface");
        }
    }
    @Test void factsKeepSymbolicReferencesForDefinitionsThatArriveLater() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Later.java","public class Later {public static int value;public static void hit(){}}","Host.java","public class Host {public static int run(){Later.hit();return Later.value;}}"));
        try(Inputs input=input(classes)) {
            Program program=new Program(input,20_000);Object loader=new Object();byte[] host=Files.readAllBytes(classes.resolve("Host.class"));
            int scope=program.define(loader,host,host,0,host.length,null).value().orElseThrow().loader();
            Facts facts=program.facts(new MethodId("Host","run","()I",scope));
            Call call=(Call)facts.actions().stream().filter(Call.class::isInstance).findFirst().orElseThrow();
            MethodId syntax=program.calls(new MethodId("Host","run","()I",scope)).value().orElseThrow().get(0).target();
            ReadField field=(ReadField)facts.actions().stream().filter(ReadField.class::isInstance).findFirst().orElseThrow();
            assertEquals(0,program.lookup(call.target()).value().orElseThrow().id().loader());
            byte[] later=Files.readAllBytes(classes.resolve("Later.class"));program.define(loader,later,later,0,later.length,null);
            assertEquals(scope,program.lookup(call.target()).value().orElseThrow().id().loader());
            assertEquals(scope,program.lookup(syntax).value().orElseThrow().id().loader());
            assertEquals(scope,program.lookupField(field.field()).value().orElseThrow().loader());
            Set<MethodId> reachable=program.discover(Set.of(new MethodId("Host","run","()I",scope)),32).value().orElseThrow();
            assertTrue(reachable.contains(new MethodId("Later","hit","()V",scope)),"helper discovery resolves a symbolic reference in its actual caller's loader");
            assertFalse(reachable.contains(new MethodId("Later","hit","()V")),"a same-named class in the input loader cannot supply the helper body");
        }
    }
    @Test void originLimitsKeepKnownProducersBesideTheTruncationFrontier() throws Exception {
        StringBuilder branches=new StringBuilder();for(int i=0;i<70;i++)branches.append("case ").append(i).append(": value=\"v").append(i).append("\";break;");
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Merge.java","public class Merge {public static Object run(int choice){Object value;switch(choice){"+branches+"default:value=\"other\";}return value;}}"));
        try(Inputs input=input(classes)) {
            Facts facts=new Program(input,20_000).facts(new MethodId("Merge","run","(I)Ljava/lang/Object;"));
            Returned returned=(Returned)facts.actions().stream().filter(Returned.class::isInstance).findFirst().orElseThrow();
            assertTrue(returned.value().origins().contains(new LimitedOrigin()));
            assertEquals(64,returned.value().origins().stream().filter(Producer.class::isInstance).count());
            assertTrue(facts.limitations().stream().anyMatch(l -> l.cause()==CoverageCause.BUDGET));
        }
    }
}
