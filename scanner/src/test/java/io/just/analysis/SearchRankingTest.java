package io.just.analysis;

import io.just.BytecodeFixtures;
import io.just.ReferenceFixtures;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.knowledge.Mechanisms.Hint;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.program.Program;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.nio.file.Files;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class SearchRankingTest {
    @TempDir Path temp;
    @Test void unresolvedBytecodeSourcesRemainPendingAndKnownBindingsLeadEqualPriority()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Sources.java","""
            public class Sources {
              Object field;
              static void pair(Object left,Object right) {}
              public void known(Object value) { pair(field,value); }
              public void merged(boolean choice,Object value) { pair(field,choice ? value : new Object()); }
            }
            """));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            MethodId known=new MethodId("Sources","known","(Ljava/lang/Object;)V");
            MethodId merged=new MethodId("Sources","merged","(ZLjava/lang/Object;)V");
            Path file=ReferenceFixtures.write(temp.resolve("source.json"),program,known);
            SearchRanking ranking=new SearchRanking(new Mechanisms(program,Catalog.read(file)),program);ranking.configure(true,List.of());
            Call first=program.facts(known).actions().stream().filter(Call.class::isInstance).map(Call.class::cast).filter(c -> c.target().name().equals("pair")).findFirst().orElseThrow();
            Call second=program.facts(merged).actions().stream().filter(Call.class::isInstance).map(Call.class::cast).filter(c -> c.target().name().equals("pair")).findFirst().orElseThrow();
            Atom left=new ObjectValue(1,"java/lang/Object",true,"left"),right=new ObjectValue(2,"java/lang/Object",true,"right");
            var path=io.just.knowledge.Values.Path.EMPTY;
            assertEquals(SearchRanking.RelationState.SUPPORTED,ranking.match(first.site(),List.of(new Literal(null),left,right),path).state());
            assertEquals(SearchRanking.RelationState.PENDING,ranking.match(second.site(),List.of(new Literal(null),left,right),path).state(),"a finite value does not resolve a merged bytecode source");
            Bound uncertain=Value.of(new ObjectValue(3,"java/lang/Object",false,"unknown")).alternatives().iterator().next();
            Bound confirmed=Value.of(right).alternatives().iterator().next();
            var prefix=new Combinations.Combination(List.of(new Literal(null),left),path,List.of(),Set.of());
            assertEquals(List.of(confirmed,uncertain),ranking.order(first,prefix,List.of(uncertain,confirmed)),"supported bindings lead equally useful unresolved choices without dropping them");
        }
    }
    @Test void equalShapesDoNotConflateSeparateValuesAndPossibleAliasesStayPending()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Sources.java","""
            public class Sources {
              Object field;
              static void use(Object left,Object right){}
              public void separate(){Object before=field;field=new Object();use(before,field);}
              public static void constants(){use("left","right");}
              public static void same(Object input){use(input,input);}
            }
            """));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            List<MethodId> methods=List.of(new MethodId("Sources","separate","()V"),new MethodId("Sources","constants","()V"),new MethodId("Sources","same","(Ljava/lang/Object;)V"));
            Path file=ReferenceFixtures.write(temp.resolve("sources.json"),program,methods.toArray(MethodId[]::new));
            SearchRanking ranking=new SearchRanking(new Mechanisms(program,Catalog.read(file)),program);ranking.configure(true,List.of());
            List<Call> calls=methods.stream().map(m -> program.facts(m).actions().stream().filter(Call.class::isInstance).map(Call.class::cast).filter(c -> c.target().name().equals("use")).findFirst().orElseThrow()).toList();
            var path=io.just.knowledge.Values.Path.EMPTY;
            ObjectValue first=new ObjectValue(1,"java/lang/Object",true,"first"),second=new ObjectValue(2,"java/lang/Object",true,"second");
            assertEquals(SearchRanking.RelationState.SUPPORTED,ranking.match(calls.get(0).site(),List.of(new Literal(null),first,second),path).state());
            assertEquals(SearchRanking.RelationState.SUPPORTED,ranking.match(calls.get(1).site(),List.of(new Literal(null),new Literal("left"),new Literal("right")),path).state());
            assertEquals(SearchRanking.RelationState.REFUTED,ranking.match(calls.get(2).site(),List.of(new Literal(null),first,second),path).state());
            assertEquals(SearchRanking.RelationState.PENDING,ranking.match(calls.get(2).site(),List.of(new Literal(null),new ObjectValue(3,"java/lang/Object",false,"possible"),second),path).state());
            ObjectValue unspecified=new ObjectValue(4,"java/lang/Object",false,"runtime type not supplied");
            var required=path.selecting(Values.location(unspecified).orElseThrow().at(new RuntimeClass()),new ClassValue("Ljava/lang/String;",true)).orElseThrow();
            Atom projected=CandidateBindings.project(unspecified,required);
            assertTrue(ValueBindings.finiteBinding(projected),"JVM checks can use a candidate's selected runtime type");
            assertEquals(SearchRanking.RelationState.PENDING,ranking.match(calls.get(2).site(),List.of(new Literal(null),projected,projected),required).state(),"selecting a hypothetical runtime type does not supply a new binding fact");
            ClassValue knownClass=new ClassValue("Ljava/lang/String;",true);
            assertEquals(SearchRanking.RelationState.SUPPORTED,ranking.match(calls.get(2).site(),List.of(new Literal(null),knownClass,knownClass),path).state());
            InputSource classSource=new InputSource(methods.get(2),0,List.of());
            ClassValue requestedClass=new ClassValue("Ljava/lang/String;",true,Optional.of(classSource));
            var classRequirement=path.selecting(classSource,requestedClass).orElseThrow();
            assertEquals(SearchRanking.RelationState.PENDING,ranking.match(calls.get(2).site(),List.of(new Literal(null),requestedClass,requestedClass),classRequirement).state());
        }
    }
    @Test void finiteExistingMembersUseTheirHandoffBeforeAColumnBudgetAndRefreshArrayFacts()throws Exception {
        StringBuilder members=new StringBuilder();for(int i=0;i<40;i++)members.append("public void a").append(i).append("(){}\n");
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Members.java","""
            public class Members {
              public static class Next {public void accept(){}}
              public static class Correct {Next owned; METHODS public void z(){owned.accept();}}
              public static class Other {METHODS public void z(){}}
              public static java.lang.reflect.Method lookup(Class<?> owner,String name,Class<?>[] signature)throws Exception{return owner.getMethod(name,signature);}
            }
            """.replace("METHODS",members)));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);var reference=ReferenceFixtures.write(temp.resolve("finite.json"),program,new MethodId("Members$Correct","z","()V"));
            SearchRanking ranking=new SearchRanking(new Mechanisms(program,Catalog.read(reference)),program);ranking.configure(true,List.of());
            MethodId caller=new MethodId("Members","lookup","(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;");
            Call call=program.facts(caller).actions().stream().filter(Call.class::isInstance).map(Call.class::cast).findFirst().orElseThrow();
            Value owners=Value.of(new ClassValue("LMembers$Other;",true)).merge(Value.of(new ClassValue("LMembers$Correct;",true)));
            Value names=Value.BOTTOM;for(int i=0;i<39;i++)names=names.merge(Value.of(new Literal("a"+i)));names=names.merge(Value.of(new Literal("z")));
            ObjectValue signature=new ObjectValue(91,"[Ljava/lang/Class;",true,"actual signature",false);
            List<Value> operands=List.of(owners,names,Value.of(signature));
            var seed=new Combinations.Combination(List.of(),io.just.knowledge.Values.Path.EMPTY,List.of(),Set.of());
            // The same array identity first lacks a producer, then receives actual length information.
            var pending=ranking.selection(call,operands,io.just.knowledge.Values.Path.EMPTY,(object,slot) -> Value.BOTTOM,0);
            var available=ranking.selection(call,operands,io.just.knowledge.Values.Path.EMPTY,(object,slot) -> slot instanceof Length?Value.of(new Literal(0)):Value.BOTTOM,0);
            assertNotEquals(pending.key(),available.key(),"new slot facts must invalidate a selection view even when the outer array value is unchanged");
            Combinations combinations=new Combinations();var joined=combinations.join(operands,seed,64,new Gap(GapKind.BUDGET,call.site(),"64 tuples"),10000,(prefix,bounds) -> ranking.order(call,prefix,bounds,available),available.key());
            assertTrue(joined.values().stream().anyMatch(tuple -> tuple.atoms().get(0).equals(new ClassValue("LMembers$Correct;",true)) && tuple.atoms().get(1).equals(new Literal("z"))),"all names are finite and exist; only the owned-field handoff merits this selection");
            assertTrue(joined.truncated());
            var plain=new Combinations().join(operands,seed,64,new Gap(GapKind.BUDGET,call.site(),"64 tuples"));
            assertFalse(plain.values().stream().anyMatch(tuple -> tuple.atoms().get(0).equals(new ClassValue("LMembers$Correct;",true)) && tuple.atoms().get(1).equals(new Literal("z"))));
            assertEquals(0,combinations.join(operands,seed,64,new Gap(GapKind.BUDGET,call.site(),"64 tuples"),10000,(prefix,bounds) -> ranking.order(call,prefix,bounds,available),available.key()).consumed());
        }
    }
    @Test void finiteMembersStillRequireTheActualReceiverArgumentTupleAndLoader()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","""
            public class Fixture {public static Object invoke(java.lang.reflect.Method method,Object receiver,Object[] arguments)throws Exception{return method.invoke(receiver,arguments);}}
            ""","Target.java","public class Target {public void go(Item item){}}","Item.java","public class Item {}"));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);int[] loaders=new int[2];
            for(int i=0;i<2;i++) {
                Object identity=new Object();byte[] item=Files.readAllBytes(classes.resolve("Item.class"));byte[] target=Files.readAllBytes(classes.resolve("Target.class"));
                loaders[i]=program.define(identity,item,item,0,item.length,null).value().orElseThrow().loader();program.define(identity,target,target,0,target.length,null);
            }
            MethodId caller=new MethodId("Fixture","invoke","(Ljava/lang/reflect/Method;Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;");
            Call call=program.facts(caller).actions().stream().filter(Call.class::isInstance).map(Call.class::cast).findFirst().orElseThrow();
            SearchRanking ranking=new SearchRanking(new Mechanisms(program),program);ranking.configure(true,List.of());
            var owner=new ClassValue("LTarget;",true,Optional.empty(),loaders[0]);var signature=new ArrayValue(1,ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",List.of(new ClassValue("LItem;",true,Optional.empty(),loaders[0])));
            var member=new Reflected(owner,new Literal("go"),signature,false,call.site());var receiver=new ObjectValue(2,"Target",true,"actual receiver",false,Optional.empty(),loaders[0]);
            var arguments=new ArrayValue(3,ArrayRole.PROXY_ARGUMENTS,"[Ljava/lang/Object;",List.of(new ObjectValue(4,"Item",true,"actual argument",false,Optional.empty(),loaders[0])));
            assertEquals(SearchRanking.RelationState.SUPPORTED,ranking.match(call.site(),List.of(member,receiver,arguments),io.just.knowledge.Values.Path.EMPTY).state());
            assertEquals(SearchRanking.RelationState.REFUTED,ranking.match(call.site(),List.of(member,new ObjectValue(5,"java/lang/Integer",true,"unrelated finite receiver"),arguments),io.just.knowledge.Values.Path.EMPTY).state());
            var otherSignature=new ArrayValue(6,ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",List.of(new ClassValue("LItem;",true,Optional.empty(),loaders[1])));
            assertEquals(SearchRanking.RelationState.REFUTED,ranking.match(call.site(),List.of(new Reflected(owner,new Literal("go"),otherSignature,false,call.site()),receiver,arguments),io.just.knowledge.Values.Path.EMPTY).state());
            var otherArguments=new ArrayValue(7,ArrayRole.PROXY_ARGUMENTS,"[Ljava/lang/Object;",List.of(new ObjectValue(8,"Item",true,"other loader",false,Optional.empty(),loaders[1])));
            assertEquals(SearchRanking.RelationState.REFUTED,ranking.match(call.site(),List.of(member,receiver,otherArguments),io.just.knowledge.Values.Path.EMPTY).state());
        }
    }
    @Test void selectionPrecedesColumnTruncationAndUnrelatedMatchesDoNotContinue()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","""
            public class Fixture {
              public static java.lang.reflect.Method lookup(Class<?> type,String name,Class<?>[] signature)throws Exception {return type.getMethod(name,signature);}
              public static java.lang.reflect.Method other(Class<?> type,String name,Class<?>[] signature)throws Exception {return type.getMethod(name,signature);}
            }
            """));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);MethodId caller=new MethodId("Fixture","lookup","(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;");
            Call call=program.facts(caller).actions().stream().filter(Call.class::isInstance).map(Call.class::cast).findFirst().orElseThrow();
            MethodId other=new MethodId("Fixture","other",caller.descriptor());
            Call next=program.facts(other).actions().stream().filter(Call.class::isInstance).map(Call.class::cast).findFirst().orElseThrow();
            SearchRanking ranking=new SearchRanking(new Mechanisms(program),program);ranking.configure(true,List.of());
            Atom owner=new ClassValue("Ljava/lang/String;",true);Atom signature=new ArrayValue(1,ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",List.of());
            Value names=Value.BOTTOM;for(int i=0;i<80;i++)names=names.merge(Value.of(new Literal("unrelated"+i)));names=names.merge(Value.of(new Literal("length")));
            var seed=new Combinations.Combination(List.of(),io.just.knowledge.Values.Path.EMPTY,List.of(),Set.of());
            var joined=new Combinations().join(List.of(Value.of(owner),names,Value.of(signature)),seed,2,new Gap(GapKind.BUDGET,call.site(),"two choices"),1000,
                    (prefix,bounds) -> ranking.order(call,prefix,bounds),0);
            assertTrue(joined.values().stream().anyMatch(tuple -> tuple.atoms().get(1).equals(new Literal("length"))),"a valid name past the original 64 alternatives must be selected before truncation");
            assertTrue(joined.truncated(),"unexplored ordinary choices remain an explicit frontier");
            assertTrue(joined.values().stream().anyMatch(tuple -> !tuple.atoms().get(1).equals(new Literal("length"))),"ordinary choices keep a share");
            assertEquals(SearchRanking.RelationState.SUPPORTED,ranking.match(call.site(),List.of(owner,new Literal("length"),signature),io.just.knowledge.Values.Path.EMPTY).state());
            assertEquals(SearchRanking.RelationState.REFUTED,ranking.match(call.site(),List.of(owner,new Literal("unrelated"),signature),io.just.knowledge.Values.Path.EMPTY).state());
            assertEquals(SearchRanking.RelationState.PENDING,ranking.match(call.site(),List.of(owner,new Unknown("name"),signature),io.just.knowledge.Values.Path.EMPTY).state());
            InputSource nameSource=new InputSource(caller,1,List.of());Atom requested=new ExternalValue("Ljava/lang/String;",nameSource);
            var requestedPath=io.just.knowledge.Values.Path.EMPTY.selecting(nameSource,new Literal("length"),"Ljava/lang/String;").orElseThrow();
            assertEquals(SearchRanking.RelationState.PENDING,ranking.match(call.site(),List.of(owner,requested,signature),requestedPath).state(),"a name requested by a mechanism is still a question, not new binding support");
            var progress=ranking.advance(SearchRanking.Progress.EMPTY,call.site(),call.target(),owner,List.of(new Literal("length"),signature),io.just.knowledge.Values.Path.EMPTY);
            assertNotEquals(SearchRanking.Rank.CONTINUED,ranking.advance(progress,next.site(),next.target(),owner,List.of(new Literal("length"),signature),io.just.knowledge.Values.Path.EMPTY).rank(),"two independent API matches are not a data handoff");
            assertEquals(SearchRanking.Rank.PARTIAL,ranking.work(progress,Optional.of(next)),"an unrelated call cannot inherit the parent's bound priority");
            InputSource stream=new InputSource(caller,0,List.of());
            Atom inputObject=new ObjectValue(101,"java/io/ObjectInputStream",false,"stream",false,Optional.of(stream));
            Atom child=new ObjectValue(102,"java/lang/Object",true,"decoded child",false,Optional.of(stream.at(new Index(0))));
            var firstEdge=edge(91,call.site(),other,inputObject,List.of());
            var parent=ranking.advance(SearchRanking.Progress.EMPTY,call.site(),other,inputObject,List.of(),io.just.knowledge.Values.Path.EMPTY,Optional.of(firstEdge));
            var secondEdge=edge(92,next.site(),call.target(),child,List.of(91));
            var continued=ranking.advance(parent,next.site(),call.target(),child,List.of(),io.just.knowledge.Values.Path.EMPTY,Optional.of(secondEdge));
            assertEquals(SearchRanking.Rank.CONTINUED,continued.rank(),"a supported modeled read has actual source lineage, even before child fields are known");
            assertNotEquals(SearchRanking.Rank.CONTINUED,ranking.advance(parent,next.site(),call.target(),child,List.of(),io.just.knowledge.Values.Path.EMPTY,Optional.of(edge(93,next.site(),call.target(),child,List.of()))).rank(),"expected lineage alone is not an actual support dependency");
            Atom unrelatedChild=new ObjectValue(103,"java/lang/Object",true,"other input",false,Optional.of(new InputSource(caller,2,List.of(new Index(0)))));
            assertNotEquals(SearchRanking.Rank.CONTINUED,ranking.advance(parent,next.site(),call.target(),unrelatedChild,List.of(),io.just.knowledge.Values.Path.EMPTY,Optional.of(secondEdge)).rank());
            var typeQuestion=io.just.knowledge.Values.Path.EMPTY.selecting(stream.at(new RuntimeClass()),new ClassValue("Ljava/io/ObjectInputStream;",true)).orElseThrow();
            Atom requestedStream=CandidateBindings.project(inputObject,typeQuestion);
            var assumed=ranking.advance(SearchRanking.Progress.EMPTY,call.site(),other,requestedStream,List.of(),typeQuestion,Optional.of(firstEdge));
            assertNotEquals(SearchRanking.Rank.CONTINUED,ranking.advance(assumed,next.site(),call.target(),requestedStream,List.of(),typeQuestion,Optional.of(secondEdge)).rank(),"reusing a requested runtime type is not a new source handoff");
            assertEquals(SearchRanking.Rank.CONTINUED,ranking.advance(assumed,next.site(),call.target(),child,List.of(),typeQuestion,Optional.of(secondEdge)).rank(),"an actual modeled child read still adds source lineage under a type condition");
            assertNotEquals(SearchRanking.Rank.CONTINUED,ranking.advance(continued,call.site(),other,inputObject,List.of(),io.just.knowledge.Values.Path.EMPTY,Optional.of(edge(94,call.site(),other,inputObject,List.of(92)))).rank(),"a repeated site is not fresh continuation support");
            ranking.configure(false,List.of());
            var plain=new Combinations().join(List.of(Value.of(owner),names,Value.of(signature)),seed,2,new Gap(GapKind.BUDGET,call.site(),"two choices"));
            assertFalse(plain.values().stream().anyMatch(tuple -> tuple.atoms().get(1).equals(new Literal("length"))));
        }
    }
    private static ScanResult.Relation edge(int id,Site site,MethodId target,Atom receiver,List<Integer> dependencies) {
        return new ScanResult.Relation(id,0,Kind.DESERIALIZATION,site,Optional.of(target),receiver,List.of(),
                List.of(new ScanResult.Support(Evidence.CONDITIONAL,List.of(site),List.of(),dependencies)),io.just.knowledge.Values.Path.EMPTY,"modeled read",Optional.empty());
    }
}
