package io.just.analysis;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.program.Program;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class ConditionsTest {
    @TempDir Path temp;
    @Test void scalarRangesProveOnlyTheCompatibleBranch()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","public class Fixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Conditions conditions=new Conditions(program,new Mechanisms(program));
            MethodId entry=new MethodId("Fixture","run","(I)V");Site site=new Site(entry,4,1,"fixture");
            InputSource source=new InputSource(entry,0,List.of());ExternalValue upper=new ExternalValue("I",source);
            Branch branch=new Branch(site,org.objectweb.asm.Opcodes.IF_ICMPGE,List.of(new Sources(Set.of()),new Sources(Set.of())),10);
            BranchKey key=new BranchKey(0,4,0);
            conditions.branch(key,branch,List.of(Value.of(new Literal(2)),Value.of(upper)),List.of(new Edge(4,5,false),new Edge(4,10,false)),
                    new Gap(GapKind.CONTROL_CONDITION,site,"unknown bound"));
            var continued=io.just.knowledge.Values.Path.EMPTY.with(key,5).orElseThrow();
            var exited=io.just.knowledge.Values.Path.EMPTY.with(key,10).orElseThrow();
            var above=io.just.knowledge.Values.Path.EMPTY.restricting(source,upper,"I",new IntegralRange(3,10)).orElseThrow();
            var below=io.just.knowledge.Values.Path.EMPTY.restricting(source,upper,"I",new IntegralRange(-5,2)).orElseThrow();
            InputSource other=new InputSource(entry,1,List.of());ExternalValue otherUpper=new ExternalValue("I",other);
            var anotherInput=io.just.knowledge.Values.Path.EMPTY.restricting(other,otherUpper,"I",new IntegralRange(3,10)).orElseThrow();
            assertTrue(conditions.implied(continued,above));assertFalse(conditions.implied(exited,above));
            assertTrue(conditions.implied(exited,below));assertFalse(conditions.implied(continued,below));
            assertFalse(conditions.implied(continued,io.just.knowledge.Values.Path.EMPTY));
            assertFalse(conditions.implied(continued,anotherInput));
            conditions.branch(key,branch,List.of(Value.of(new Literal(2)).merge(Value.of(new Literal(9))),Value.of(upper)),
                    List.of(new Edge(4,5,false),new Edge(4,10,false)),new Gap(GapKind.CONTROL_CONDITION,site,"multiple counters"));
            assertFalse(conditions.implied(continued,above));
        }
    }
    @Test void finiteRuntimeTypeGroupsIntersectWithoutBorrowingAnotherLoaderOrReceiver() {
        MethodId entry=new MethodId("Fixture","run","(Ljava/lang/Object;Ljava/lang/Object;)V");
        InputSource first=new InputSource(entry,0,List.of(new RuntimeClass())),second=new InputSource(entry,1,List.of(new RuntimeClass()));
        ClassValue a=new ClassValue("LA;",true),b=new ClassValue("LB;",true),otherLoader=new ClassValue("LA;",true,Optional.empty(),1);
        var group=io.just.knowledge.Values.Path.EMPTY.selecting(first,new RuntimeTypes(List.of(a,b))).orElseThrow();
        var selectA=io.just.knowledge.Values.Path.EMPTY.selecting(first,a).orElseThrow();
        var foreign=io.just.knowledge.Values.Path.EMPTY.selecting(first,otherLoader).orElseThrow();
        assertTrue(group.and(selectA).isPresent());assertFalse(group.and(foreign).isPresent());
        assertTrue(group.and(io.just.knowledge.Values.Path.EMPTY.selecting(second,otherLoader).orElseThrow()).isPresent());
        var overlap=io.just.knowledge.Values.Path.EMPTY.selecting(first,new RuntimeTypes(List.of(b,otherLoader))).orElseThrow();
        assertEquals(b,group.and(overlap).orElseThrow().selected(first).orElseThrow());
    }
    @Test void heapGrowthRefreshesNormalCompletionAndContradictionOnlyRejectsThatChoice() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","public class Fixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Conditions conditions=new Conditions(program,new Mechanisms(program));
            Site site=new Site(new MethodId("Fixture","run","()V"),4,1,"fixture");
            ObjectValue iterator=new ObjectValue(1,"java/util/Iterator",false,"iterator");
            Call call=new Call(site,new MethodId("java/util/Iterator","next","()Ljava/lang/Object;"),org.objectweb.asm.Opcodes.INVOKEINTERFACE,new Sources(Set.of()),List.of());
            Invocation invocation=new Invocation(call,iterator,List.of(),new ObjectValue(2,"java/lang/Object",false,"result"),io.just.knowledge.Values.Path.EMPTY);
            NormalChoice key=new NormalChoice(0,4,-1,List.of(),call.target(),iterator,List.of());
            var path=io.just.knowledge.Values.Path.EMPTY.with(key,0).orElseThrow();
            Gap pending=new Gap(GapKind.CONTROL_CONDITION,site,"iterator needs a valid cursor",Optional.of(key));
            Map<Slot,Value> heap=new HashMap<>();heap.put(new Cursor(),Value.of(new Literal(0)));heap.put(new Length(),Value.of(new Unknown("late length")));
            Bindings bindings=(object,slot) -> heap.getOrDefault(slot,Value.BOTTOM);
            conditions.normal(key,invocation,List.of(pending),bindings);assertFalse(conditions.gaps(path).isEmpty());assertTrue(conditions.compatible(path));
            heap.put(new Length(),Value.of(new Literal(1)));heap.put(new Index(0),Value.of(new Literal("member")));
            conditions.normal(key,invocation,List.of(pending),bindings);assertTrue(conditions.gaps(path).isEmpty());assertTrue(conditions.satisfied(pending,path));
            heap.put(new Cursor(),Value.of(new Literal(1)));conditions.normal(key,invocation,List.of(pending),bindings);
            assertFalse(conditions.compatible(path));assertTrue(conditions.compatible(io.just.knowledge.Values.Path.EMPTY));
        }
    }
    @Test void aDefinitionArrivingAfterTheFirstQueryRefreshesTheSameCompletion() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","public class Fixture {}"));
        Path fresh=BytecodeFixtures.compile(temp,17,Map.of("Fresh.java","public class Fresh {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Mechanisms mechanisms=new Mechanisms(program);Conditions conditions=new Conditions(program,mechanisms);
            ObjectValue loader=new ObjectValue(1,"java/lang/ClassLoader",false,"loader");byte[] host=Files.readAllBytes(classes.resolve("Fixture.class"));program.define(loader,host,host,0,host.length,null);
            Site site=new Site(new MethodId("Fixture","run","()V"),2,1,"fixture");
            Call call=new Call(site,new MethodId("java/lang/Class","forName","(Ljava/lang/String;ZLjava/lang/ClassLoader;)Ljava/lang/Class;"),org.objectweb.asm.Opcodes.INVOKESTATIC,new Sources(Set.of()),List.of());
            Invocation invocation=new Invocation(call,new Literal(null),List.of(new Literal("Fresh"),new Literal(0),loader),new ObjectValue(3,"java/lang/Class",false,"result"),io.just.knowledge.Values.Path.EMPTY);
            NormalChoice key=new NormalChoice(0,2,-1,List.of(),call.target(),invocation.receiver(),invocation.arguments());
            var path=io.just.knowledge.Values.Path.EMPTY.with(key,0).orElseThrow();Gap gap=new Gap(GapKind.MISSING_DEPENDENCY,site,"Fresh is not yet defined",Optional.of(key));
            conditions.normal(key,invocation,List.of(gap),(object,slot) -> Value.BOTTOM);assertFalse(conditions.gaps(path).isEmpty());
            byte[] bytes=Files.readAllBytes(fresh.resolve("Fresh.class"));program.define(loader,bytes,bytes,0,bytes.length,null);
            assertTrue(conditions.gaps(path).isEmpty());assertEquals(2,program.definitionCount());
        }
    }
    @Test void oneKnownFailingHeapBranchDoesNotRejectTheStillUnknownComplement()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","public class Fixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Mechanisms mechanisms=new Mechanisms(new Program(inputs,20_000));Site site=new Site(new MethodId("Fixture","read","()V"),1,1,"fixture");
            ObjectValue iterator=new ObjectValue(1,"java/util/Iterator",false,"iterator");
            var yes=io.just.knowledge.Values.Path.EMPTY.with(new BranchKey(0,2),1).orElseThrow();
            Invocation invocation=new Invocation(new Call(site,new MethodId("java/util/Iterator","next","()Ljava/lang/Object;"),org.objectweb.asm.Opcodes.INVOKEINTERFACE,new Sources(Set.of()),List.of()),iterator,List.of(),new ObjectValue(2,"java/lang/Object",false,"result"),io.just.knowledge.Values.Path.EMPTY);
            Bindings partial=(object,slot) -> slot instanceof Cursor || slot instanceof Length?Value.of(new Literal(1),yes):Value.BOTTOM;
            assertTrue(mechanisms.normalCompletion(invocation,partial).isEmpty());
            Invocation selected=new Invocation(invocation.call(),iterator,List.of(),invocation.result(),yes);
            assertEquals(Optional.of(false),mechanisms.normalCompletion(selected,partial));
        }
    }
}
