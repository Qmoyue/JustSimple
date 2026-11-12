package io.just.analysis;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.EntryPoints.Entry;
import io.just.knowledge.Values.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class EvidenceGraphTest {
    @TempDir Path temp;
    @Test void cyclicFallbackVariantsCannotExhaustRecoveryBeforeAnIndependentSupport()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Proofs.java","public class Proofs {public static void run(){}}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Method method=program.declared(new MethodId("Proofs","run","()V")).orElseThrow();
            Site site=new Site(method.id(),0,1,"fixture");Entry entry=new Entry(method,"fixture",List.of());
            EvidenceGraph graph=new EvidenceGraph(128,16,64,new Conditions(program,new io.just.knowledge.Mechanisms(program)));
            int cycle=graph.record(0,site,Kind.VALUE_FLOW,Optional.empty(),Evidence.CONDITIONAL,new Literal(null),List.of(new Literal("cycle")),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"circular source",List.of(0),Optional.empty());
            List<Integer> joint=new ArrayList<>(List.of(cycle));
            for(int index=0;index<12;index++) {
                int alternative=-1;
                for(int choice=0;choice<2;choice++) {
                    int source=graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal(index*2+choice)),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"independent source",List.of(),Optional.empty());
                    alternative=graph.record(0,site,Kind.VALUE_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal("choice"+index)),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"alternative source",List.of(source),Optional.empty());
                }
                joint.add(alternative);
            }
            int good=graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal("good")),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"independent completion",List.of(),Optional.empty());
            graph.record(0,site,Kind.IMPACT,Optional.of(method.id()),Evidence.CONDITIONAL,new Literal(null),List.of(),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"terminal",joint,Optional.empty());
            int end=graph.record(0,site,Kind.IMPACT,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"terminal",List.of(good),Optional.empty());
            graph.observe(0,end,List.of());
            var found=graph.findings(List.of(new EvidenceGraph.Context(-1,-1,entry,List.of())));
            assertEquals(1,found.size());
            assertTrue(found.get(0).supportingRelations().contains(good),"a known cyclic fallback must not multiply unrelated alternatives ahead of an independent witness");
            assertFalse(found.get(0).supportingRelations().contains(cycle));
            assertTrue(found.get(0).gaps().isEmpty());
        }
    }
    @Test void breakpointsUseTheSupportThatActuallyContainsTheGap() {
        Site site=new Site(new MethodId("Proofs","run","()V"),3,1,"fixture");
        Gap gap=new Gap(GapKind.INPUT_BINDING,site,"second support requires this input");
        var first=new ScanResult.Support(Evidence.PROVEN,List.of(site),List.of(),List.of(10));
        var second=new ScanResult.Support(Evidence.CONDITIONAL,List.of(site),List.of(gap),List.of(20));
        for(var supports:List.of(List.of(first,second),List.of(second,first))) {
            var relation=new ScanResult.Relation(0,0,Kind.DYNAMIC_CALL,site,Optional.empty(),new Literal(null),List.of(),supports,io.just.knowledge.Values.Path.EMPTY,"fixture",Optional.empty());
            var points=Breakpoints.locate(List.of(relation),List.of(),List.of());
            assertEquals(1,points.size());assertEquals(List.of(20,0),points.get(0).knownRelations());
        }
    }
    @Test void independentProtocolTriggersGetReportSlotsBeforeMoreVariantsOfOneTrigger()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Proofs.java","public class Proofs {public static void run(){}public static void callback(String input){}public static void firstProtocol(){}public static void secondProtocol(){}}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Method method=program.declared(new MethodId("Proofs","run","()V")).orElseThrow();
            Site site=new Site(method.id(),0,1,"fixture");Entry entry=new Entry(method,"fixture",List.of());
            EvidenceGraph graph=new EvidenceGraph(64,2,64,new Conditions(program,new io.just.knowledge.Mechanisms(program)));
            List<EvidenceGraph.Context> contexts=new ArrayList<>();contexts.add(new EvidenceGraph.Context(-1,-1,entry,List.of()));
            for(String protocol:List.of("firstProtocol","secondProtocol")) {
                Site witness=new Site(new MethodId("Proofs",protocol,"()V"),0,1,"protocol callback");
                int call=graph.record(0,site,Kind.CONTAINER_CALLBACK,Optional.of(new MethodId("Proofs","callback","(Ljava/lang/String;)V")),Evidence.PROVEN,new Literal(null),List.of(new Literal(protocol)),List.of(witness),List.of(),io.just.knowledge.Values.Path.EMPTY,"protocol dispatch",List.of(),Optional.empty());
                int context=contexts.size();contexts.add(new EvidenceGraph.Context(0,call,entry,List.of()));
                for(int variant=0;variant<(context==1?10:1);variant++) {
                    int end=graph.record(context,site,Kind.IMPACT,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(new Literal(variant)),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"terminal",List.of(),Optional.empty());
                    graph.observe(context,end,List.of());
                }
            }
            var findings=graph.findings(contexts);
            assertEquals(Set.of("firstProtocol","secondProtocol"),findings.stream().flatMap(f -> f.proof().stream()).flatMap(use -> graph.snapshot().get(use.relation()).supports().get(use.support()).witnesses().stream()).map(w -> w.method().name()).filter(name -> name.endsWith("Protocol")).collect(java.util.stream.Collectors.toSet()));
            assertFalse(graph.coverage().isEmpty());
        }
    }
    @Test void terminalOverloadsAndUnconnectedFragmentsEachKeepReportSlots()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Proofs.java","public class Proofs {public static void run(){}public static void sink(String value){}public static void sink(String[] value){}}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Method method=program.declared(new MethodId("Proofs","run","()V")).orElseThrow();Site site=new Site(method.id(),0,1,"fixture");
            EvidenceGraph graph=new EvidenceGraph(64,3,64,new Conditions(program,new io.just.knowledge.Mechanisms(program)));
            for(int index=0;index<20;index++) {
                int fragment=graph.record(0,site,Kind.REFLECTION,Optional.empty(),Evidence.CONDITIONAL,new Literal(null),List.of(new Literal(index)),List.of(site),List.of(new Gap(GapKind.DYNAMIC_TARGET,site,"unresolved member")),io.just.knowledge.Values.Path.EMPTY,"unconnected fragment",List.of(),Optional.empty());
                graph.observe(0,fragment,List.of());
            }
            for(int index=0;index<11;index++) {
                MethodId target=new MethodId("Proofs","sink",index<10?"(Ljava/lang/String;)V":"([Ljava/lang/String;)V");
                int edge=graph.record(0,site,Kind.IMPACT,Optional.of(target),Evidence.PROVEN,new Literal(null),List.of(new Literal(index)),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"overloaded terminal",List.of(),Optional.empty());
                graph.observe(0,edge,List.of());
            }
            var findings=graph.findings(List.of(new EvidenceGraph.Context(-1,-1,new Entry(method,"fixture",List.of()),List.of())));
            assertEquals(Set.of("(Ljava/lang/String;)V","([Ljava/lang/String;)V"),findings.stream().filter(f -> f.boundary()==Kind.IMPACT).map(f -> graph.snapshot().get(f.path().get(f.path().size()-1)).target().orElseThrow().descriptor()).collect(java.util.stream.Collectors.toSet()));
            assertTrue(findings.stream().anyMatch(f -> f.boundary()==Kind.REFLECTION));
            assertFalse(graph.coverage().isEmpty(),"omitted variants remain an explicit report frontier");
        }
    }
    @Test void manyJointSiblingsRemainAProofWithinTheRelationBudget()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Proofs.java","public class Proofs {public static void run(){}}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Method method=program.declared(new MethodId("Proofs","run","()V")).orElseThrow();Site site=new Site(method.id(),0,1,"fixture");
            EvidenceGraph graph=new EvidenceGraph(1500,16,64,new Conditions(program,new io.just.knowledge.Mechanisms(program)));
            List<Integer> joint=new ArrayList<>();
            for(int index=0;index<1000;index++)joint.add(graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal(index)),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"necessary sibling",List.of(),Optional.empty()));
            int end=graph.record(0,site,Kind.IMPACT,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"joint",joint,Optional.empty());graph.observe(0,end,List.of());
            var found=graph.findings(List.of(new EvidenceGraph.Context(-1,-1,new Entry(method,"fixture",List.of()),List.of()))).get(0);assertTrue(found.supportingRelations().containsAll(joint),"sibling dependencies are necessary together and must not be dropped or treated as recursion");
        }
    }
    @Test void jointSupportsSelectOneCompatibleAlternativeAndRejectContradictoryBranches()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Proofs.java","public class Proofs {public static void run(){}}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Method method=program.declared(new MethodId("Proofs","run","()V")).orElseThrow();Site site=new Site(method.id(),0,1,"fixture");
            EvidenceGraph graph=new EvidenceGraph(100,16,64,new Conditions(program,new io.just.knowledge.Mechanisms(program)));
            var left=io.just.knowledge.Values.Path.EMPTY.with(new BranchKey(0,4),1).orElseThrow();
            var right=io.just.knowledge.Values.Path.EMPTY.with(new BranchKey(0,4),2).orElseThrow();
            int a=graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal("a")),List.of(site),List.of(),left,"left",Set.of(),Optional.empty());
            int b=graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal("b")),List.of(site),List.of(),right,"right",Set.of(),Optional.empty());
            int alternative=-1;
            for(int dependency:List.of(a,b))alternative=graph.record(0,site,Kind.VALUE_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"alternative",Set.of(dependency),Optional.empty());
            int joint=graph.record(0,site,Kind.IMPACT,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"compatible",List.of(alternative,b),Optional.empty());
            graph.observe(0,joint,List.of());var contexts=List.of(new EvidenceGraph.Context(-1,-1,new Entry(method,"fixture",List.of()),List.of()));
            var findings=graph.findings(contexts);assertEquals(1,findings.size());
            assertTrue(findings.get(0).supportingRelations().contains(b));assertFalse(findings.get(0).supportingRelations().contains(a));
            int conflict=graph.record(0,new Site(method.id(),1,1,"fixture"),Kind.IMPACT,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"contradictory",List.of(a,b),Optional.empty());
            graph.observe(0,conflict,List.of());assertEquals(1,graph.findings(contexts).size(),"individually possible branches cannot jointly prove one candidate");
        }
    }
    @Test void replayedControlCannotProveItselfOrHideAnIndependentWitness()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Proofs.java","public class Proofs {public static void run(){}}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Method method=program.declared(new MethodId("Proofs","run","()V")).orElseThrow();
            Site site=new Site(method.id(),0,1,"fixture");Entry entry=new Entry(method,"fixture",List.of());
            var left=io.just.knowledge.Values.Path.EMPTY.with(new BranchKey(0,4),1).orElseThrow();
            var right=io.just.knowledge.Values.Path.EMPTY.with(new BranchKey(0,4),2).orElseThrow();
            for(boolean independent:List.of(false,true))for(boolean additionalDependency:List.of(false,true)) {
                EvidenceGraph graph=new EvidenceGraph(64,16,64,new Conditions(program,new io.just.knowledge.Mechanisms(program)));
                int leftSource=graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal("left")),List.of(site),List.of(),left,"left source",Set.of(),Optional.empty());
                Value first=graph.control(0,site,Value.of(NormalValue.CERTAIN,left).tracing(Set.of(leftSource)),io.just.knowledge.Values.Path.EMPTY);
                int rightSource=graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal("right")),List.of(site),List.of(),right,"right source",Set.of(),Optional.empty());
                Value replay=additionalDependency?first.tracing(Set.of(rightSource)):first;
                if(independent)replay=replay.merge(Value.of(NormalValue.CERTAIN,right).tracing(Set.of(rightSource)));
                Value completion=graph.control(0,site,replay,io.just.knowledge.Values.Path.EMPTY);
                int end=graph.record(0,site,Kind.IMPACT,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(),List.of(site),List.of(),right,"right continuation",completion.alternatives().iterator().next().dependencies(),Optional.empty());
                graph.observe(0,end,List.of());
                var found=graph.findings(List.of(new EvidenceGraph.Context(-1,-1,entry,List.of())));
                assertEquals(1,found.size());
                if(independent) {
                    assertTrue(found.get(0).supportingRelations().contains(rightSource),"the compatible independent completion must be selected");
                    assertTrue(found.get(0).gaps().stream().noneMatch(g -> g.detail().contains("cycle")));
                } else {
                    assertTrue(found.get(0).gaps().stream().anyMatch(g -> g.detail().contains("cycle")),"a circular completion remains an explicit unresolved candidate");
                    if(additionalDependency)assertTrue(found.get(0).supportingRelations().contains(rightSource),"a dependency after the circular edge must also remain in the selected evidence");
                }
            }
        }
    }
    @Test void alternativeProofsDoNotBecomeConjunctiveButJointDependenciesStillMatter() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Proofs.java","public class Proofs {public static void run(){}}"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Method method=program.declared(new MethodId("Proofs","run","()V")).orElseThrow();
            Site site=new Site(method.id(),0,1,"fixture");Entry entry=new Entry(method,"fixture",List.of());
            for(boolean completeFirst:List.of(false,true)) {
                EvidenceGraph graph=new EvidenceGraph(64,16,64,new Conditions(program,new io.just.knowledge.Mechanisms(program)));
                Gap missing=new Gap(GapKind.INPUT_BINDING,site,"independent unresolved support");
                int bad=graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.CONDITIONAL,new Literal(null),List.of(new Literal("bad")),List.of(site),List.of(missing),io.just.knowledge.Values.Path.EMPTY,"fixture",List.of(),Optional.empty());
                int good=graph.record(0,site,Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(new Literal("good")),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"fixture",List.of(),Optional.empty());
                int observation=-1;
                for(boolean complete:List.of(completeFirst,!completeFirst))
                    observation=graph.record(0,site,Kind.REFLECTION,Optional.of(method.id()),complete?Evidence.PROVEN:Evidence.CONDITIONAL,new Literal(null),List.of(),List.of(site),complete?List.of():List.of(missing),io.just.knowledge.Values.Path.EMPTY,"alternative",List.of(complete?good:bad),Optional.empty());
                graph.observe(0,observation,List.of());
                var result=graph.findings(List.of(new EvidenceGraph.Context(-1,-1,entry,List.of())));
                assertEquals(Set.of(completeFirst?good:bad),Set.copyOf(result.get(0).supportingRelations()));
                int joint=graph.record(0,new Site(method.id(),1,1,"fixture"),Kind.REFLECTION,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(),List.of(site),List.of(),io.just.knowledge.Values.Path.EMPTY,"joint",List.of(bad,good),Optional.empty());
                graph.observe(0,joint,List.of());
                Value a=new Value(Set.of(new Bound(new Literal("same"),io.just.knowledge.Values.Path.EMPTY,List.of(),Set.of(bad))));
                Value b=new Value(Set.of(new Bound(new Literal("same"),io.just.knowledge.Values.Path.EMPTY,List.of(),Set.of(good))));
                assertEquals(2,a.merge(b).alternatives().size(),"independent supports must not become one joint dependency set");
                assertEquals(2,a.merge(a.tracing(Set.of(good))).alternatives().size(),"additional evidence must remain independently observable");
                Value cut=a.merge(b).limited(1,new Gap(GapKind.BUDGET,site,"one value budget"));
                assertTrue(cut.merge(a).alternatives().stream().anyMatch(v -> v.atom().equals(new Literal("same"))),"a cutoff marker must not swallow later known facts");
                Site valueSite=new Site(method.id(),2,1,"fixture");
                Value fact=graph.compact(0,valueSite,a.requiring(List.of(missing)).merge(b));
                var combination=new Combinations().join(List.of(fact),new Combinations.Combination(List.of(),io.just.knowledge.Values.Path.EMPTY,List.of(),Set.of()),1,new Gap(GapKind.BUDGET,valueSite,"one semantic value"));
                assertFalse(combination.truncated(),"independent witnesses of one value must not consume a tuple budget twice");
                int use=graph.record(0,valueSite,Kind.REFLECTION,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(),List.of(valueSite),List.of(),io.just.knowledge.Values.Path.EMPTY,"factored value",combination.values().get(0).dependencies(),Optional.empty());
                graph.observe(0,use,List.of());
                var selected=graph.findings(List.of(new EvidenceGraph.Context(-1,-1,entry,List.of()))).get(2);assertEquals(1,selected.supportingRelations().stream().filter(id -> id==good || id==bad).count());
                var left=io.just.knowledge.Values.Path.EMPTY.with(new BranchKey(0,7),1).orElseThrow();
                var right=io.just.knowledge.Values.Path.EMPTY.with(new BranchKey(0,7),2).orElseThrow();
                Value completions=Value.NULL.under(left).tracing(Set.of(bad)).merge(Value.NULL.under(right).tracing(Set.of(good)));
                for(var condition:List.of(left,right)) {
                    Site normalSite=new Site(method.id(),3,1,"fixture");Value normal=graph.control(0,normalSite,completions,condition);
                    int reached=graph.record(0,normalSite,Kind.REFLECTION,Optional.of(method.id()),Evidence.PROVEN,new Literal(null),List.of(),List.of(normalSite),List.of(),condition,"normal continuation",normal.alternatives().iterator().next().dependencies(),Optional.empty());
                    graph.observe(0,reached,List.of());
                    var all=graph.findings(List.of(new EvidenceGraph.Context(-1,-1,entry,List.of())));
                    var continued=all.stream().filter(f -> f.path().contains(reached)).findFirst().orElseThrow();
                    assertTrue(continued.supportingRelations().contains(condition.equals(left)?bad:good));
                    assertFalse(continued.supportingRelations().contains(condition.equals(left)?good:bad),"normal continuation keeps only its compatible source");
                }
                var points=Breakpoints.locate(graph.snapshot(),List.of(),List.of());
                assertEquals(1,points.stream().filter(point -> point.detail().equals(missing.detail())).count(),"one source condition is indexed once even when many downstream relations or alternative supports consume it");
            }
        }
    }
}
