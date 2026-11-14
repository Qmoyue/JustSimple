package io.just.analysis;

import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class HeapStoreTest {
    @TempDir Path temp;
    @Test void sameContextOrderingRespectsIterationsEffectsAndRequestBoundaries()throws Exception {
        Path classes=io.just.BytecodeFixtures.compile(temp,8,Map.of("HeapFixture.java","public class HeapFixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);HeapStore heap=new HeapStore(program,new Conditions(program,new io.just.knowledge.Mechanisms(program)),64);heap.context(0,-1,-1,-1);
            var request=new ExecutionPoint.Request(1);
            var earlierLoop=new ExecutionPoint(0,20,0,request);var laterLoop=new ExecutionPoint(0,3,1,request);
            assertTrue(heap.before(earlierLoop,laterLoop));assertFalse(heap.before(laterLoop,earlierLoop));
            var first=new ExecutionPoint(0,7,-1,request,List.of(1,2));var second=new ExecutionPoint(0,7,-1,request,List.of(1,3));
            assertTrue(heap.before(first,second));assertFalse(heap.before(second,first));
            var otherRequest=new ExecutionPoint(0,8,-1,new ExecutionPoint.Request(2));
            assertFalse(heap.before(first,otherRequest));assertFalse(heap.before(otherRequest,first));
        }
    }
    @Test void opaqueMutationKeepsArrayLengthButStillChangesElementsAndCollectionSize()throws Exception {
        Path classes=io.just.BytecodeFixtures.compile(temp,8,Map.of("HeapFixture.java","public class HeapFixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);HeapStore heap=new HeapStore(program,new Conditions(program,new io.just.knowledge.Mechanisms(program)),64);heap.context(0,-1,-1,-1);
            ObjectValue array=new ObjectValue(1,"[Ljava/lang/Object;",true,"array"),list=new ObjectValue(2,"java/util/ArrayList",true,"list");
            Site site=new Site(new MethodId("HeapFixture","inspect","()V"),10,1,"fixture");
            heap.write(array,new Length(),new ExecutionPoint(0,1),Value.of(new Literal(3)).tracing(Set.of(10)),site);
            heap.write(array,new Index(0),new ExecutionPoint(0,1),Value.of(new Literal("before")),site);
            heap.write(list,new Length(),new ExecutionPoint(0,1),Value.of(new Literal(3)),site);
            Gap gap=new Gap(GapKind.UNSUPPORTED,site,"opaque mutation");Value change=Value.of(new Unknown("changed")).requiring(List.of(gap));
            for(ObjectValue object:List.of(array,list))heap.write(object,new Mutation(),new ExecutionPoint(0,2),change,site);
            var use=new HeapStore.Use(new ExecutionPoint(0,10),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false);
            var length=heap.read(array,new Length(),use);
            assertEquals(Value.of(new Literal(3)).tracing(Set.of(10)),length.value(),"a call can alter elements but cannot resize this array object");
            assertFalse(length.dependencies().contains(new HeapStore.Cell(array.id(),new Mutation())));
            assertTrue(heap.read(array,new Index(0),use).value().alternatives().stream().anyMatch(b -> b.atom() instanceof Unknown && b.gaps().contains(gap)));
            assertTrue(heap.read(list,new Length(),use).value().alternatives().stream().anyMatch(b -> b.atom() instanceof Unknown && b.gaps().contains(gap)),"collection size remains mutable");
        }
    }
    @Test void longConditionalHistoryPreservesBranchesConcurrentWritesAndMutationRecovery()throws Exception {
        Path classes=io.just.BytecodeFixtures.compile(temp,8,Map.of("HeapFixture.java","public class HeapFixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Conditions conditions=new Conditions(program,new io.just.knowledge.Mechanisms(program));
            HeapStore heap=new HeapStore(program,conditions,64);heap.context(0,-1,-1,-1);heap.context(1,0,10,-1);
            ObjectValue object=new ObjectValue(1,"HeapFixture",true,"shared");Slot slot=new Content();
            Site site=new Site(new MethodId("HeapFixture","inspect","()V"),140,1,"fixture");BranchKey branch=new BranchKey(0,0);
            conditions.uncertain(branch,new Gap(GapKind.CONTROL_CONDITION,site,"unknown branch"));
            List<io.just.knowledge.Values.Path> paths=java.util.stream.IntStream.range(0,3).mapToObj(i -> io.just.knowledge.Values.Path.EMPTY.with(branch,i).orElseThrow()).toList();
            for(int i=0;i<100;i++)heap.write(object,slot,new ExecutionPoint(0,i+1),Value.of(new Literal(i),paths.get(i%3)).tracing(Set.of(i+1)),site);
            var async=new ExecutionPoint.Asynchronous(1,new ExecutionPoint(0,10));
            heap.write(object,slot,new ExecutionPoint(1,5,-1,async),Value.of(new Literal(555),paths.get(0)).tracing(Set.of(500)),site);
            Gap opaque=new Gap(GapKind.UNSUPPORTED,site,"opaque update");
            heap.write(object,new Mutation(),new ExecutionPoint(0,105),Value.of(new Unknown("changed"),paths.get(1)).requiring(List.of(opaque)),site);
            var use=new HeapStore.Use(new ExecutionPoint(0,140),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false);
            Value value=heap.read(object,slot,use).value();
            assertEquals(Set.of(new Literal(97),new Literal(98),new Literal(99),new Literal(555),new Unknown("changed")),value.alternatives().stream().map(Bound::atom).collect(java.util.stream.Collectors.toSet()));
            for(int i:List.of(97,98,99))assertTrue(value.alternatives().stream().filter(b -> b.atom().equals(new Literal(i))).allMatch(b -> b.dependencies().contains(i+1)),"the latest write on each branch retains its own support");
            Value unaffected=heap.read(object,slot,new HeapStore.Use(new ExecutionPoint(0,140),site,paths.get(2),List.of(),false)).value();
            assertEquals(Value.of(new Literal(98),paths.get(2)).tracing(Set.of(99)),unaffected);
            heap.write(object,slot,new ExecutionPoint(0,110),Value.of(new Literal(111),paths.get(1)).tracing(Set.of(1005)),site);
            Value repaired=heap.read(object,slot,use).value();
            assertEquals(Set.of(new Literal(111),new Literal(98),new Literal(99),new Literal(555)),repaired.alternatives().stream().map(Bound::atom).collect(java.util.stream.Collectors.toSet()));
            assertTrue(repaired.alternatives().stream().filter(b -> b.atom().equals(new Literal(111))).allMatch(b -> b.dependencies().contains(1005) && !b.gaps().contains(opaque)));
        }
    }
    @Test void incompatibleWritesDoNotConsumeTheReadBindingBudget()throws Exception {
        Path classes=io.just.BytecodeFixtures.compile(temp,8,Map.of("HeapFixture.java","public class HeapFixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);HeapStore heap=new HeapStore(program,new Conditions(program,new io.just.knowledge.Mechanisms(program)),2);heap.context(0,-1,-1,-1);
            ObjectValue object=new ObjectValue(1,"HeapFixture",true,"one object");Site site=new Site(new MethodId("HeapFixture","inspect","()V"),30,1,"fixture");BranchKey branch=new BranchKey(0,1);
            for(int i=0;i<20;i++)heap.write(object,new Content(),new ExecutionPoint(0,i+2),Value.of(new Literal(i),io.just.knowledge.Values.Path.EMPTY.with(branch,i).orElseThrow()),site);
            var selected=io.just.knowledge.Values.Path.EMPTY.with(branch,19).orElseThrow();
            Value value=heap.read(object,new Content(),new HeapStore.Use(new ExecutionPoint(0,30),site,selected,List.of(),false)).value();
            assertEquals(Value.of(new Literal(19),selected),value);
            assertTrue(heap.limitations().isEmpty(),"mutually exclusive writes are irrelevant to this bounded read");
        }
    }

    @Test void crossingTheCoveringWriteThresholdKeepsBothExclusiveBranches()throws Exception {
        Path classes=io.just.BytecodeFixtures.compile(temp,8,Map.of("HeapFixture.java","public class HeapFixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);
            HeapStore heap=new HeapStore(program,new Conditions(program,new io.just.knowledge.Mechanisms(program)),8);
            heap.context(0,-1,-1,-1);
            ObjectValue object=new ObjectValue(1,"HeapFixture",true,"object");
            Slot slot=new Content();Site site=new Site(new MethodId("HeapFixture","read","()V"),65,1,"fixture");
            var path=io.just.knowledge.Values.Path.EMPTY;
            BranchKey branch=new BranchKey(0,0);
            Value left=Value.of(new Literal("left"),path.with(branch,1).orElseThrow()).tracing(Set.of(1));
            Value right=Value.of(new Literal("right"),path.with(branch,2).orElseThrow());
            for(int i=1;i<=62;i++)heap.write(object,slot,new ExecutionPoint(0,i),left,site);
            var use=new HeapStore.Use(new ExecutionPoint(0,65),site,path,List.of(),false);
            for(int i=63;i<=64;i++) {
                Value latest=right.tracing(Set.of(i));
                heap.write(object,slot,new ExecutionPoint(0,i),latest,site);
                assertEquals(left.merge(latest),heap.read(object,slot,use).value(),"writes: "+i);
            }
        }
    }
    @Test void elementSummariesRespectOverwriteTimePathsAndRequestIdentity() throws Exception {
        java.nio.file.Path classes=io.just.BytecodeFixtures.compile(temp,8,Map.of("HeapFixture.java","public class HeapFixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),java.nio.file.Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);HeapStore heap=new HeapStore(program,new Conditions(program,new io.just.knowledge.Mechanisms(program)),64);heap.context(0,-1,-1,-1);
            ObjectValue array=new ObjectValue(1,"[Ljava/lang/String;",true,"array");Site site=new Site(new MethodId("HeapFixture","inspect","()V"),4,1,"fixture");
            heap.write(array,new Index(0),new ExecutionPoint(0,1),Value.of(new Literal("first")),site);
            heap.write(array,new Index(0),new ExecutionPoint(0,2),Value.of(new Literal("later")),site);
            heap.write(array,new Index(0),new ExecutionPoint(0,7),Value.of(new Literal("future")),site);
            HeapStore.Use use=new HeapStore.Use(new ExecutionPoint(0,4),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false);
            var summary=heap.read(array,new Elements(),use);
            assertEquals(Value.of(new Literal("later")),summary.value());
            assertTrue(summary.dependencies().contains(new HeapStore.Cell(array.id(),new Index(0))));
            assertEquals(Value.of(new Literal("first")),heap.read(array,new Elements(),new HeapStore.Use(new ExecutionPoint(0,2),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false)).value());
            var branch=new BranchKey(0,3);var left=io.just.knowledge.Values.Path.EMPTY.with(branch,1).orElseThrow();var right=io.just.knowledge.Values.Path.EMPTY.with(branch,2).orElseThrow();
            heap.write(array,new Index(0),new ExecutionPoint(0,3),Value.of(new Literal("branch"),left),site);
            assertEquals(Value.of(new Literal("later"),right),heap.read(array,new Elements(),new HeapStore.Use(new ExecutionPoint(0,4),site,right,List.of(),false)).value());
            heap.write(array,new Index(1),new ExecutionPoint(0,3,-1,new ExecutionPoint.Request(1)),Value.of(new Literal("other request")),site);
            assertTrue(heap.read(array,new Index(1),new HeapStore.Use(new ExecutionPoint(0,4,-1,new ExecutionPoint.Request(2)),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false)).value().empty());
        }
    }
    @Test void positionedWritesPreserveReadDependenciesAndEvidenceGrowth() throws Exception {
        Path classes=io.just.BytecodeFixtures.compile(temp,8,Map.of("HeapFixture.java","public class HeapFixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);HeapStore heap=new HeapStore(program,new Conditions(program,new io.just.knowledge.Mechanisms(program)),64);heap.context(0,-1,-1,-1);
            ObjectValue object=new ObjectValue(1,"HeapFixture",true,"fixture");Slot slot=new Content();Site site=new Site(new MethodId("HeapFixture","inspect","()V"),4,1,"compiled fixture");
            heap.write(object,slot,new ExecutionPoint(0,0),Value.of(new Literal("first")),site);
            assertFalse(heap.write(object,slot,new ExecutionPoint(0,0),Value.of(new Literal("first")),site));
            HeapStore.Read snapshot=heap.read(object,slot,new HeapStore.Use(new ExecutionPoint(0,4),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false));
            assertTrue(snapshot.dependencies().contains(new HeapStore.Cell(object.id(),slot)));
            heap.write(object,new Length(),new ExecutionPoint(0,1),Value.of(new Literal(3)),site);
            assertEquals(snapshot,heap.read(object,slot,new HeapStore.Use(new ExecutionPoint(0,4),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false)));
            heap.write(object,slot,new ExecutionPoint(0,2),Value.of(new Literal("later")),site);
            assertEquals(Value.of(new Literal("first")),snapshot.value(),"later writes must not mutate an earlier read result");
            assertEquals(Value.of(new Literal("later")),heap.read(object,slot,new HeapStore.Use(new ExecutionPoint(0,4),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false)).value());
            assertTrue(heap.write(object,slot,new ExecutionPoint(0,2),Value.of(new Literal("later")).tracing(Set.of(42)),site));
            assertTrue(heap.read(object,slot,new HeapStore.Use(new ExecutionPoint(0,4),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false)).value().alternatives().stream().anyMatch(b -> b.dependencies().contains(42)));
        }
    }
    @Test void coveringWritesKeepConcurrentValuesAndDefiniteMutationRecovery()throws Exception {
        Path classes=io.just.BytecodeFixtures.compile(temp,8,Map.of("HeapFixture.java","public class HeapFixture {}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);HeapStore heap=new HeapStore(program,new Conditions(program,new io.just.knowledge.Mechanisms(program)),64);
            heap.context(0,-1,-1,-1);heap.context(1,0,10,-1);
            ObjectValue object=new ObjectValue(1,"HeapFixture",true,"shared");Slot slot=new Content();
            Site site=new Site(new MethodId("HeapFixture","inspect","()V"),30,1,"fixture");
            var async=new ExecutionPoint.Asynchronous(1,new ExecutionPoint(0,10));
            heap.write(object,slot,new ExecutionPoint(0,1),Value.of(new Literal(1)),site);
            heap.write(object,slot,new ExecutionPoint(1,2,-1,async),Value.of(new Literal(2)),site);
            heap.write(object,slot,new ExecutionPoint(0,20),Value.of(new Literal(3)),site);
            var use=new HeapStore.Use(new ExecutionPoint(0,30),site,io.just.knowledge.Values.Path.EMPTY,List.of(),false);
            assertEquals(Set.of(new Literal(2),new Literal(3)),heap.read(object,slot,use).value().alternatives().stream().map(Bound::atom).collect(java.util.stream.Collectors.toSet()));
            Gap opaque=new Gap(GapKind.UNSUPPORTED,site,"opaque update");
            heap.write(object,new Mutation(),new ExecutionPoint(0,22),Value.of(new Unknown("changed")).requiring(List.of(opaque)),site);
            assertTrue(heap.read(object,slot,use).value().alternatives().stream().filter(b -> b.atom().equals(new Literal(3))).allMatch(b -> b.gaps().contains(opaque)));
            heap.write(object,slot,new ExecutionPoint(0,25),Value.of(new Literal(4)),site);
            Value recovered=heap.read(object,slot,use).value();
            assertEquals(Set.of(new Literal(2),new Literal(4)),recovered.alternatives().stream().map(Bound::atom).collect(java.util.stream.Collectors.toSet()));
            assertTrue(recovered.alternatives().stream().filter(b -> b.atom().equals(new Literal(4))).allMatch(b -> !b.gaps().contains(opaque)),"the concurrent value still has its own ambiguity; the definite repair removes the opaque update");
        }
    }
}
