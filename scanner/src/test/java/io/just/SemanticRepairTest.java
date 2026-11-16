package io.just;

import io.just.analysis.*;
import io.just.input.*;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.report.Reports;
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
    @Test void reflectivePublicBooleanConstantsPreserveTheirValues()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("FieldConstants.java","""
                public class FieldConstants {
                  public static final boolean TRUE=true, FALSE=false;
                  static void yes(){} static void no(){}
                  public static void run()throws Exception {
                    if(FieldConstants.class.getField("TRUE").getBoolean(null))yes();else no();
                    if(FieldConstants.class.getField("FALSE").getBoolean(null))no();else yes();
                  }
                }
                """));
        var result=scan(classes,"FieldConstants","run","()V");
        assertTrue(calls(result,"FieldConstants","yes"));assertFalse(calls(result,"FieldConstants","no"));
    }
    @Test void reflectedFieldCollectionsUseDeclaredAndInheritedClassMetadata()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of(
                "FieldParent.java","public class FieldParent {public int inherited;private int hidden;}",
                "FieldChild.java","public class FieldChild extends FieldParent {public int own;private String secret;}",
                "FieldCollections.java","""
                public class FieldCollections {
                  static void yes(){} static void no(){}
                  public static void run(){
                    if(FieldChild.class.getDeclaredFields().length==2 && FieldChild.class.getFields().length==2)yes();else no();
                  }
                  public static void names(){
                    for(java.lang.reflect.Field field:FieldChild.class.getDeclaredFields())if(field.getName().equals("absent"))no();
                    yes();
                  }
                  public static void mutation(){
                    java.lang.reflect.Field[] fields=FieldChild.class.getDeclaredFields();fields[0]=null;
                    if(fields[0]==null)yes();
                  }
                }
                """));
        var result=scan(classes,"FieldCollections","run","()V");
        assertTrue(calls(result,"FieldCollections","yes"));assertFalse(calls(result,"FieldCollections","no"));
        var names=scan(classes,"FieldCollections","names","()V");
        assertTrue(calls(names,"FieldCollections","yes"));assertFalse(calls(names,"FieldCollections","no"));
        assertTrue(calls(scan(classes,"FieldCollections","mutation","()V"),"FieldCollections","yes"));
        Files.delete(classes.resolve("FieldParent.class"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Query<List<FieldInfo>> partial=new Program(inputs,20_000).reflectiveFields("FieldChild",false,0,256);
            assertTrue(partial.pending().stream().anyMatch(issue -> issue.cause()==QueryCause.MISSING_DEPENDENCY));
            assertTrue(partial.value().orElseThrow().stream().anyMatch(field -> field.id().name().equals("own")));
        }
    }
    @Test void reflectiveFieldWritesRespectAccessAndUpdateTheSelectedObject()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("FieldOwner.java","public class FieldOwner {public int visible;private int hidden;}","FieldCaller.java","""
                public class FieldCaller {
                  static void yes(){} static void no(){} static void badValue(){} static void badAccess(){}
                  public static void allowed()throws Exception {
                    FieldOwner owner=new FieldOwner();
                    try {FieldOwner.class.getDeclaredField("visible").set(owner,7);if(owner.visible==7)yes();else badValue();}
                    catch(IllegalAccessException impossible){badAccess();}
                  }
                  public static void denied()throws Exception {
                    try {FieldOwner.class.getDeclaredField("hidden").set(new FieldOwner(),7);no();}
                    catch(IllegalAccessException expected){yes();}
                  }
                  public static void opened()throws Exception {
                    java.lang.reflect.Field field=FieldOwner.class.getDeclaredField("hidden");field.setAccessible(true);
                    try {field.set(new FieldOwner(),7);yes();}catch(IllegalAccessException impossible){no();}
                  }
                  public static void invalid()throws Exception {
                    try {FieldOwner.class.getDeclaredField("visible").set(new FieldOwner(),"not a number");no();}
                    catch(IllegalArgumentException expected){yes();}
                  }
                }
                """));
        for(String entry:List.of("allowed","denied","opened","invalid")) {
            var result=scan(classes,"FieldCaller",entry,"()V");
            assertTrue(calls(result,"FieldCaller","yes"),entry);assertFalse(calls(result,"FieldCaller","no"),entry);
            assertFalse(calls(result,"FieldCaller","badValue"),entry+" value");assertFalse(calls(result,"FieldCaller","badAccess"),entry+" access");
        }
    }
    @Test void reflectedMethodsKeepTheirOwnAccessStateAndEnforcePrivateAccess()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of(
                "MethodOwner.java","public class MethodOwner {private void first(){MethodCaller.target();} private void second(){MethodCaller.target();}}",
                "ExternalMutator.java","public class ExternalMutator {public static void accept(java.lang.reflect.Method method){}}",
                "MethodCaller.java","""
                import java.lang.reflect.*;
                public class MethodCaller {
                  static void yes(){} static void no(){} static void target(){} static void continued(){} static void caught(){}
                  private void own(){target();}
                  public static void denied()throws Exception {
                    try {MethodOwner.class.getDeclaredMethod("first").invoke(new MethodOwner());no();}
                    catch(IllegalAccessException expected){yes();}
                  }
                  public static void opened()throws Exception {
                    Method m=MethodOwner.class.getDeclaredMethod("first");m.setAccessible(true);
                    try {m.invoke(new MethodOwner());yes();}catch(IllegalAccessException impossible){no();}
                  }
                  public static void closed()throws Exception {
                    Method m=MethodOwner.class.getDeclaredMethod("first");m.setAccessible(true);m.setAccessible(false);
                    try {m.invoke(new MethodOwner());no();}catch(IllegalAccessException expected){yes();}
                  }
                  public static void separate()throws Exception {
                    Method a=MethodOwner.class.getDeclaredMethod("first"),b=MethodOwner.class.getDeclaredMethod("second");a.setAccessible(true);
                    try {b.invoke(new MethodOwner());no();}catch(IllegalAccessException expected){yes();}
                  }
                  public static void sameMember()throws Exception {
                    Method a=MethodOwner.class.getDeclaredMethod("first"),b=MethodOwner.class.getDeclaredMethod("first");a.setAccessible(true);
                    try {b.invoke(new MethodOwner());no();}catch(IllegalAccessException expected){yes();}
                  }
                  public static void sameClass()throws Exception {
                    try {MethodCaller.class.getDeclaredMethod("own").invoke(new MethodCaller());yes();}
                    catch(IllegalAccessException impossible){no();}
                  }
                  public static void varying(boolean open)throws Exception {
                    Method m=MethodOwner.class.getDeclaredMethod("first");m.setAccessible(open);
                    try {m.invoke(new MethodOwner());continued();}catch(IllegalAccessException expected){caught();}
                  }
                  public static void changed()throws Exception {
                    Method m=MethodOwner.class.getDeclaredMethod("first");ExternalMutator.accept(m);
                    try {m.invoke(new MethodOwner());continued();}catch(IllegalAccessException expected){caught();}
                  }
                }
                """));
        for(String entry:List.of("denied","opened","closed","separate","sameMember","sameClass")) {
            var result=scan(classes,"MethodCaller",entry,"()V");
            assertTrue(calls(result,"MethodCaller","yes"),entry+": "+result.limitations());
            assertFalse(calls(result,"MethodCaller","no"),entry);
            assertEquals(Set.of("opened","sameClass").contains(entry),calls(result,"MethodCaller","target"),entry);
        }
        var varying=scan(classes,"MethodCaller","varying","(Z)V");
        assertTrue(calls(varying,"MethodCaller","continued"));assertTrue(calls(varying,"MethodCaller","caught"));
        Files.delete(classes.resolve("ExternalMutator.class"));
        var changed=scan(classes,"MethodCaller","changed","()V");
        assertTrue(calls(changed,"MethodCaller","continued"));assertTrue(calls(changed,"MethodCaller","caught"));
    }
    @Test void base64DecoderKeepsAlphabetExceptionsAndMutableArrayContents()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("DecodedValues.java","""
                public class DecodedValues {
                  static void yes(){} static void no(){}
                  public static void url(){byte[] bytes=java.util.Base64.getUrlDecoder().decode("_w==");
                    if(bytes.length==1 && bytes[0]==-1)yes();else no();bytes[0]=3;if(bytes[0]==3)yes();else no();}
                  public static void invalid(){try{java.util.Base64.getDecoder().decode("_w==");no();}catch(IllegalArgumentException expected){yes();}}
                }
                """));
        for(String entry:List.of("url","invalid")) {
            var result=scan(classes,"DecodedValues",entry,"()V");
            assertTrue(calls(result,"DecodedValues","yes"),entry);assertFalse(calls(result,"DecodedValues","no"),entry);
        }
    }
    @Test void knownCounterLoopsUseTheAvailableBudgetAndUnknownBoundsRemainExplicit()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("LoopBounds.java","""
                public class LoopBounds {
                  static void yes(){}
                  public static void known(){for(int i=0;i<12;i++)if(i==11)yes();}
                  public static void unknown(int size){for(int i=0;i<size;i++)if(i==11)yes();}
                }
                """));
        var known=scan(classes,"LoopBounds","known","()V");
        assertTrue(calls(known,"LoopBounds","yes"),known.limitations().toString());
        assertTrue(known.limitations().stream().noneMatch(limit -> limit.startsWith("counter loop prefix")));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Analyzer.Limits limits=new Analyzer.Limits(5000,200_000,20,30_000,1000,8);
            var limited=new Analyzer(program,new Mechanisms(program),limits).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("LoopBounds","known","()V")));
            assertTrue(limited.limitations().stream().anyMatch(limit -> limit.startsWith("finite counter loop budget (8)")));
        }
        var unknown=scan(classes,"LoopBounds","unknown","(I)V");
        assertTrue(unknown.limitations().stream().anyMatch(limit -> limit.startsWith("counter loop prefix")));
    }
    @Test void constantMethodSummariesKeepTheirCallingPath()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("SummaryPaths.java","""
                public class SummaryPaths {
                  static int one(){return 1;} static int two(){return 2;}
                  static void yes(){} static void no(){}
                  public static void run(boolean choose){
                    int value;if(choose)value=one();else value=two();
                    if(choose){if(value==2)no();}else{if(value==1)no();}
                    yes();
                  }
                }
                """));
        var result=scan(classes,"SummaryPaths","run","(Z)V");
        assertTrue(result.statistics().summaryApplications()>0);
        assertTrue(calls(result,"SummaryPaths","yes"));assertFalse(calls(result,"SummaryPaths","no"));
    }
    @Test void aProvenFinalInstanceTypeNarrowsVirtualDispatchButUnknownBranchesRemainOpen()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("TypeGuards.java","""
                public class TypeGuards {
                  interface Action {void run();}
                  public static final class Exact implements Action {public void run(){hit();}}
                  public static class OtherA implements Action {public void run(){other();}}
                  public static class OtherB implements Action {public void run(){other();}}
                  public static class OtherC implements Action {public void run(){other();}}
                  static void hit(){} static void other(){} static void alternate(){}
                  public static void selected(Action action){if(action instanceof Exact)action.run();else alternate();}
                  public static void unknown(Action action){if(!(action instanceof Exact))action.run();}
                }
                """));
        for(String entry:List.of("selected","unknown"))try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Analyzer.Limits limits=new Analyzer.Limits(5000,200_000,20,30_000,1000,2);
            var result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(),2),limits)
                    .scan(EntryPoints.Mode.COMPONENT,true,Set.of(new MethodId("TypeGuards",entry,"(LTypeGuards$Action;)V")));
            boolean frontier=result.limitations().stream().anyMatch(limit -> limit.startsWith("virtual target frontier"));
            if(entry.equals("selected")) {
                assertTrue(calls(result,"TypeGuards","hit"));assertTrue(calls(result,"TypeGuards","alternate"));
                assertFalse(calls(result,"TypeGuards","other"));assertFalse(frontier,result.limitations().toString());
            } else {
                assertTrue(calls(result,"TypeGuards","other"));assertTrue(frontier,"an unknown receiver still keeps the unexplored frontier");
            }
        }
    }
    @Test void sideEffectFreeVirtualForwardersDoNotConsumeContextsNeededByRealTargets()throws Exception {
        StringBuilder source=new StringBuilder("""
                public class ManyActions {
                  public static class Base {public void run(){}}
                  static void hit(){} static void done(){} static void caught(){}
                """);
        for(int i=0;i<24;i++)source.append("public static class Quiet").append(i).append(" extends Base {public void run(){super.run();}}");
        source.append("""
                  public static class ZUseful extends Base {public void run(){hit();}}
                  public static class ZThrows extends Base {public void run(){throw new IllegalStateException();}}
                  public static void scan(Base input){try{input.run();done();}catch(IllegalStateException expected){caught();}}
                }
                """);
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ManyActions.java",source.toString()));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Analyzer.Limits limits=new Analyzer.Limits(16,200_000,20,30_000,1000,64);
            var result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(),64),limits)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("ManyActions","scan","(LManyActions$Base;)V")));
            assertTrue(calls(result,"ManyActions","hit"),result.limitations().toString());
            assertTrue(calls(result,"ManyActions","caught"));assertTrue(calls(result,"ManyActions","done"));
            assertTrue(result.limitations().stream().noneMatch(limit -> limit.startsWith("invocation context budget")),result.limitations().toString());
            assertTrue(result.relations().stream().filter(r -> r.detail().contains("evaluated from bytecode"))
                    .flatMap(r -> r.supports().stream()).flatMap(s -> s.witnesses().stream()).anyMatch(site -> site.method().owner().startsWith("ManyActions$Quiet")),"the evaluated forwarding call remains inspectable as bytecode evidence");
        }
    }
    @Test void boundedConstantBranchesReduceVirtualExpansionWithoutHidingEffectsOrExceptions()throws Exception {
        StringBuilder source=new StringBuilder("""
                public class CalculatedActions {
                  public static class Base {public void run(){}}
                  static void hit(){} static void bad(){} static void caught(){}
                """);
        for(int i=0;i<24;i++)source.append("public static class Quiet").append(i).append(" extends Base {public void run(){int value=2;value=value*3;if(value==6)super.run();else bad();}}");
        source.append("""
                  public static class ZUseful extends Base {public void run(){hit();}}
                  public static class ZThrows extends Base {public void run(){int zero=0;int value=1/zero;}}
                  public static void scan(Base input){try{input.run();}catch(ArithmeticException expected){caught();}}
                }
                """);
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("CalculatedActions.java",source.toString()));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Analyzer.Limits limits=new Analyzer.Limits(16,200_000,20,30_000,1000,64);
            var result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(),64),limits)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("CalculatedActions","scan","(LCalculatedActions$Base;)V")));
            assertTrue(calls(result,"CalculatedActions","hit"),result.limitations().toString());
            assertTrue(calls(result,"CalculatedActions","caught"));assertFalse(calls(result,"CalculatedActions","bad"));
            assertTrue(result.limitations().stream().noneMatch(limit -> limit.startsWith("invocation context budget")),result.limitations().toString());
        }
    }
    @Test void boundedEvaluationPreservesImpactInForwardedCalls()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ForwardedImpact.java","""
                public class ForwardedImpact {
                  public static class Base {public void run(){}}
                  public static class First extends Base {public void run(){super.run();}}
                  public static class Second extends Base {public void run(){super.run();}}
                  public static void exact(){new First().run();}
                  public static void unknown(Base value){value.run();}
                }
                """));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);MethodId sink=new MethodId("ForwardedImpact$Base","run","()V");
            for(MethodId entry:List.of(new MethodId("ForwardedImpact","exact","()V"),new MethodId("ForwardedImpact","unknown","(LForwardedImpact$Base;)V"))) {
                var result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(sink),8),new Analyzer.Limits(100,200_000,20,30_000,1000,8))
                        .scan(EntryPoints.Mode.COMPONENT,false,Set.of(entry));
                assertTrue(result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).anyMatch(f ->
                        f.path().stream().map(result.relations()::get).flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("ForwardedImpact$First") && t.name().equals("run"))
                        && f.path().stream().map(result.relations()::get).flatMap(r -> r.target().stream()).anyMatch(sink::equals)),entry.toString());
            }
        }
    }
    @Test void equivalentPureTargetsRetainReceiverIdentityAcrossLaterCalls()throws Exception {
        StringBuilder source=new StringBuilder("""
                public class ReceiverGroups {
                  public static class Base {public void first(){} public void second(){}}
                  public static class Holder {Base value;}
                  static void a(){} static void b(){} static void c(){}
                """);
        for(int i=0;i<16;i++)source.append("public static class Quiet").append(i).append(" extends Base {public void first(){super.first();} public void second(){")
                .append(i==0?"a();":i==1?"b();":"").append("}}");
        source.append("""
                  public static class ZEffect extends Base {int marker;public void first(){marker=1;} public void second(){if(marker==1)c();}}
                  public static void scan(Base input){input.first();input.second();}
                  public static void replace(Holder holder){holder.value.first();holder.value=new ZEffect();holder.value.first();holder.value.second();}
                }
                """);
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ReceiverGroups.java",source.toString()));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Analyzer.Limits limits=new Analyzer.Limits(100,200_000,20,30_000,1000,4);
            Set<MethodId> sinks=Set.of(new MethodId("ReceiverGroups","a","()V"),new MethodId("ReceiverGroups","b","()V"),new MethodId("ReceiverGroups","c","()V"));
            var result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),sinks,4),limits)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("ReceiverGroups","scan","(LReceiverGroups$Base;)V")));
            for(String method:List.of("a","b","c"))assertTrue(calls(result,"ReceiverGroups",method),method+": "+result.limitations());
            assertTrue(result.limitations().stream().noneMatch(limit -> limit.startsWith("virtual target frontier")),result.limitations().toString());
            var effects=result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT)
                    .filter(f -> f.path().stream().map(result.relations()::get).flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("ReceiverGroups") && t.name().equals("c"))).toList();
            assertFalse(effects.isEmpty());
            assertTrue(effects.stream().allMatch(f -> java.util.stream.Stream.concat(f.path().stream(),f.supportingRelations().stream()).map(result.relations()::get)
                    .flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("ReceiverGroups$ZEffect") && t.name().equals("first"))),"the later call must not borrow the mutated object from a different runtime type");
            java.io.StringWriter report=new java.io.StringWriter();Reports.json(result,report);
            assertTrue(report.toString().contains("\"RuntimeTypes\""),"the grouped receiver types remain inspectable in the report");
            var replaced=new Analyzer(program,new Mechanisms(program,Catalog.empty(),sinks,4),limits)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("ReceiverGroups","replace","(LReceiverGroups$Holder;)V")));
            assertTrue(calls(replaced,"ReceiverGroups","c"),"a later field write creates a different receiver and must not inherit the earlier group");
        }
    }
    @Test void groupedDispatchReportsUninspectedTargetsUntilTheBudgetCoversThem()throws Exception {
        StringBuilder source=new StringBuilder("""
                public class GroupFrontier {
                  public static class Base {public void run(){}}
                  static void hit(){}
                """);
        for(int i=0;i<80;i++)source.append("public static class Quiet").append(i).append(" extends Base {public void run(){super.run();}}");
        source.append("public static class ZEffect extends Base {public void run(){hit();}} public static void scan(Base input){input.run();}}");
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("GroupFrontier.java",source.toString()));
        List<ScanResult> results=new ArrayList<>();
        for(int alternatives:List.of(1,2))try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);
            results.add(new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(),alternatives),
                    new Analyzer.Limits(100,200_000,20,30_000,1000,alternatives)).scan(EntryPoints.Mode.COMPONENT,false,
                    Set.of(new MethodId("GroupFrontier","scan","(LGroupFrontier$Base;)V"))));
        }
        assertTrue(results.get(0).limitations().stream().anyMatch(limit -> limit.startsWith("virtual target frontier")),results.get(0).limitations().toString());
        assertTrue(results.get(1).limitations().stream().noneMatch(limit -> limit.startsWith("virtual target frontier")),results.get(1).limitations().toString());
        assertTrue(calls(results.get(1),"GroupFrontier","hit"),"the uncovered, effectful target remains reachable when the search budget grows");
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);
            var limited=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(),2),new Analyzer.Limits(100,1500,20,30_000,1000,2))
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("GroupFrontier","scan","(LGroupFrontier$Base;)V")));
            assertTrue(limited.limitations().stream().anyMatch(limit -> limit.startsWith("static evaluation work allowance")),limited.limitations().toString());
        }
    }
    @Test void expandingTheAlternativeBudgetAlsoExpandsSerializedTypeDiscovery()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("NativeCandidates.java","""
                import java.io.*;
                public class NativeCandidates {
                  public static class A implements Serializable {private void readObject(ObjectInputStream in){}}
                  public static class B implements Serializable {private void readObject(ObjectInputStream in){}}
                  public static class C implements Serializable {private void readObject(ObjectInputStream in){}}
                  public static void read(ObjectInputStream in)throws Exception {in.readObject();}
                }
                """));
        List<ScanResult> results=new ArrayList<>();
        for(int alternatives:List.of(1,4))try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Mechanisms mechanisms=new Mechanisms(program,Catalog.empty(),Set.of(),alternatives);
            Analyzer.Limits limits=new Analyzer.Limits(5000,200_000,20,30_000,1000,alternatives);
            results.add(new Analyzer(program,mechanisms,limits).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("NativeCandidates","read","(Ljava/io/ObjectInputStream;)V"))));
        }
        assertTrue(results.get(0).limitations().stream().anyMatch(limit -> limit.startsWith("conditional serialized type frontier")));
        assertTrue(results.get(1).limitations().stream().noneMatch(limit -> limit.startsWith("conditional serialized type frontier")));
        assertTrue(calls(results.get(1),"NativeCandidates$C","readObject"));
    }
    @Test void serializedMembersUseTheConfiguredAlternativeBudget()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("NativeArray.java","public class NativeArray {public static Object read(java.io.ObjectInputStream in)throws Exception{return in.readObject();}}"));
        Path facts=temp.resolve("native-array.json");Files.writeString(facts,"""
                {"source":"source-built array","basis":"BINDING","entry":{"owner":"NativeArray","name":"read","descriptor":"(Ljava/io/ObjectInputStream;)Ljava/lang/Object;","arguments":[{"ref":"stream"}]},
                 "objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"array"}},{"id":"array","type":"[Ljava/lang/String;","elements":["a","b","c"]}]}
                """);
        List<ScanResult> results=new ArrayList<>();
        for(int alternatives:List.of(2,4))try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Analyzer.Limits limits=new Analyzer.Limits(5000,200_000,20,30_000,1000,alternatives);
            results.add(new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(),alternatives),limits)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("NativeArray","read","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;")),Optional.of(StaticData.read(facts))));
        }
        assertTrue(results.get(0).limitations().stream().anyMatch(limit -> limit.startsWith("serialized member frontier")),results.get(0).limitations().toString());
        assertTrue(results.get(1).limitations().stream().noneMatch(limit -> limit.startsWith("serialized member frontier")),results.get(1).limitations().toString());
    }
    @Test void finiteReflectedArraysReportAndExpandTheirIterationBudget()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ArrayLoop.java","""
                public class ArrayLoop {
                  public static void target(String a,String b,String c,String d,String e,String f,String g,String h,Long last){}
                  static void yes(){}
                  public static void run()throws Exception {
                    for(Class<?> type:ArrayLoop.class.getDeclaredMethod("target",String.class,String.class,String.class,String.class,
                        String.class,String.class,String.class,String.class,Long.class).getParameterTypes())if(type==Long.class)yes();
                  }
                }
                """));
        List<ScanResult> results=new ArrayList<>();
        for(int alternatives:List.of(8,16))try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Analyzer.Limits limits=new Analyzer.Limits(5000,200_000,20,30_000,1000,alternatives);
            results.add(new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(),alternatives),limits)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("ArrayLoop","run","()V"))));
        }
        assertTrue(results.get(0).limitations().stream().anyMatch(limit -> limit.startsWith("finite array iteration budget (8)")),results.get(0).limitations().toString());
        assertTrue(results.get(1).limitations().stream().noneMatch(limit -> limit.startsWith("finite array iteration budget")),results.get(1).limitations().toString());
        assertTrue(calls(results.get(1),"ArrayLoop","yes"));
    }
    @Test void finiteIteratorsReportAndExpandTheirIterationBudget()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("IteratorLoop.java","""
                public class IteratorLoop {
                  static void yes(){}
                  public static void run(){
                    for(String value:java.util.Arrays.asList("a","b","c","d","e","f","g","h","last"))
                      if("last".equals(value))yes();
                  }
                }
                """));
        List<ScanResult> results=new ArrayList<>();
        for(int alternatives:List.of(8,16))try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);Analyzer.Limits limits=new Analyzer.Limits(5000,200_000,20,30_000,1000,alternatives);
            results.add(new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(),alternatives),limits)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("IteratorLoop","run","()V"))));
        }
        assertTrue(results.get(0).limitations().stream().anyMatch(limit -> limit.startsWith("finite iterator budget (8)")),results.get(0).limitations().toString());
        assertTrue(results.get(1).limitations().stream().noneMatch(limit -> limit.startsWith("finite iterator budget")),results.get(1).limitations().toString());
        assertTrue(calls(results.get(1),"IteratorLoop","yes"));
    }
    @Test void onePossibleExceptionDoesNotHideAnotherOperandDependentException()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("MixedExceptions.java","""
                public class MixedExceptions {
                  static void nullPath(){} static void incompatiblePath(){}
                  public static void run(boolean absent,Object value){
                    Object[] array=absent?null:new String[1];
                    try {array[0]=value;}
                    catch(NullPointerException expected){nullPath();}
                    catch(ArrayStoreException expected){incompatiblePath();}
                  }
                }
                """));
        var result=scan(classes,"MixedExceptions","run","(ZLjava/lang/Object;)V");
        assertTrue(calls(result,"MixedExceptions","nullPath"));
        assertTrue(calls(result,"MixedExceptions","incompatiblePath"));
    }
    @Test void serializedInterfaceCanBindItsOwnProxyHandlerAndOrdinaryImplementation()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("SerializedProxy.java","""
                import java.io.*;
                import java.lang.reflect.*;
                public class SerializedProxy {
                  interface Service {void send(String value);}
                  static void proxyPath(String value){} static void directPath(String value){}
                  public static class Direct implements Service,Serializable {public void send(String value){directPath(value);}}
                  public static class Handler implements InvocationHandler,Serializable {
                    public Object invoke(Object proxy,Method method,Object[] args){
                      if(method.getName().equals("send"))proxyPath((String)args[0]);return null;
                    }
                  }
                  public static class Wrapper implements Serializable {
                    Service service;String value;
                    private void readObject(ObjectInputStream in)throws Exception {in.defaultReadObject();service.send(value);}
                  }
                  public static void read(ObjectInputStream in)throws Exception {in.readObject();}
                  public static void direct(){new Direct().send("fixed");}
                }
                """));
        var result=scan(classes,"SerializedProxy","read","(Ljava/io/ObjectInputStream;)V");
        assertTrue(calls(result,"SerializedProxy","directPath"),result.limitations().toString());
        assertTrue(calls(result,"SerializedProxy","proxyPath"),result.limitations().toString());
        assertTrue(result.inputRequirements().stream().filter(need -> need.needed().reason().equals("handler restored for this serialized proxy"))
                .flatMap(need -> need.source().stream()).anyMatch(source -> source.path().stream().anyMatch(slot -> slot instanceof SerializedField field && field.field().name().equals("service"))
                        && source.path().get(source.path().size()-1).equals(new SerializedField(new FieldId("java/lang/reflect/Proxy","h","Ljava/lang/reflect/InvocationHandler;")))));
        var direct=scan(classes,"SerializedProxy","direct","()V");
        assertTrue(calls(direct,"SerializedProxy","directPath"));assertFalse(calls(direct,"SerializedProxy","proxyPath"));
    }
    @Test void assumedPlatformInitializationDoesNotImplyDefaultStaticValues()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("PlatformState.java","""
                public class PlatformState {
                  static class Local {static Object absent;static Object initialized=new Object();}
                  static void yes(){} static void no(){}
                  public static void print(){System.out.println("sample");yes();}
                  public static void unknown(){if(System.out==null)yes();else no();}
                  public static void local(){if(Local.absent==null && Local.initialized!=null)yes();else no();}
                }
                """));
        var print=scan(classes,"PlatformState","print","()V");assertTrue(calls(print,"PlatformState","yes"));
        assertTrue(print.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("PlatformState") && t.name().equals("yes")).isPresent())
                .flatMap(r -> r.supports().stream()).flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.DEPLOYMENT));
        var unknown=scan(classes,"PlatformState","unknown","()V");assertTrue(calls(unknown,"PlatformState","yes"));assertTrue(calls(unknown,"PlatformState","no"));
        var local=scan(classes,"PlatformState","local","()V");assertTrue(calls(local,"PlatformState","yes"));assertFalse(calls(local,"PlatformState","no"));
    }
    @Test void handlersOnlyReceiveCompatibleJvmExceptions()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ArrayThrows.java","""
                public class ArrayThrows {
                  static class Input {String value;}
                  static void normal(){} static void storeFailure(){} static void nullFailure(){}
                  public static void typed(Input input){
                    Object[] array=new String[1];
                    try{array[0]=input.value;normal();}
                    catch(ArrayStoreException e){storeFailure();}
                    catch(NullPointerException e){nullFailure();}
                  }
                  public static void unknown(Object value){
                    Object[] array=new String[1];
                    try{array[0]=value;normal();}catch(ArrayStoreException e){storeFailure();}
                  }
                  public static void incompatible(){
                    Object[] array=new String[1];
                    try{array[0]=new Object();normal();}catch(ArrayStoreException e){storeFailure();}
                  }
                }
                """));
        var typed=scan(classes,"ArrayThrows","typed","(LArrayThrows$Input;)V");
        assertTrue(calls(typed,"ArrayThrows","normal"));assertFalse(calls(typed,"ArrayThrows","storeFailure"));assertTrue(calls(typed,"ArrayThrows","nullFailure"));
        var unknown=scan(classes,"ArrayThrows","unknown","(Ljava/lang/Object;)V");
        assertTrue(calls(unknown,"ArrayThrows","normal"));assertTrue(calls(unknown,"ArrayThrows","storeFailure"));
        var incompatible=scan(classes,"ArrayThrows","incompatible","()V");
        assertFalse(calls(incompatible,"ArrayThrows","normal"));assertTrue(calls(incompatible,"ArrayThrows","storeFailure"));
    }
    @Test void possibleArithmeticExceptionReachesReflectiveCaller()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("PossibleThrow.java","""
                import java.lang.reflect.*;
                public class PossibleThrow {
                  public static class Target {public void divide(int divisor){int value=1/divisor;}}
                  static void normal(){} static void caught(){}
                  static void invoke(int divisor)throws Exception {
                    Method method=Target.class.getMethod("divide",int.class);
                    try{method.invoke(new Target(),divisor);normal();}catch(InvocationTargetException e){caught();}
                  }
                  public static void unknown(int value)throws Exception {invoke(value);}
                  public static void nonzero()throws Exception {invoke(1);}
                  public static void zero()throws Exception {invoke(0);}
                }
                """));
        var unknown=scan(classes,"PossibleThrow","unknown","(I)V");assertTrue(calls(unknown,"PossibleThrow","normal"));assertTrue(calls(unknown,"PossibleThrow","caught"));
        var nonzero=scan(classes,"PossibleThrow","nonzero","()V");assertTrue(calls(nonzero,"PossibleThrow","normal"));assertFalse(calls(nonzero,"PossibleThrow","caught"));
        var zero=scan(classes,"PossibleThrow","zero","()V");assertFalse(calls(zero,"PossibleThrow","normal"));assertTrue(calls(zero,"PossibleThrow","caught"));
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
