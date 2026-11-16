package io.just;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class RankingTest {
    @TempDir Path temp;
    @Test void preferenceLimitDoesNotDiscardOrdinaryDispatchOrMarkItTruncated()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Preferred.java","""
                public class Preferred {
                  interface Action {void run();}
                  static class Box {void use(Object value){}}
                  public static class One implements Action {Box box;public void run(){box.use(this);}}
                  public static class Two implements Action {Box box;public void run(){box.use(this);}}
                  public static class Three implements Action {Box box;public void run(){box.use(this);}}
                  public static class Four implements Action {Box box;public void run(){box.use(this);}}
                }
                """));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);MethodId requested=new MethodId("Preferred$Action","run","()V");
            Path reference=ReferenceFixtures.write(temp.resolve("ranking.json"),program,new MethodId("Preferred$One","run","()V"));
            Mechanisms mechanisms=new Mechanisms(program,Catalog.read(reference),Set.of(),4);
            var preferred=mechanisms.preferredReceivers(requested,requested.owner(),0);
            assertEquals(3,preferred.value().orElseThrow().size());assertTrue(preferred.pending().isEmpty());
            var resolved=program.implementations(requested,requested.owner(),0,preferred.value().orElseThrow(),4);
            assertEquals(4,resolved.value().orElseThrow().size());assertTrue(resolved.pending().isEmpty());
        }
    }
    @Test void laterDispatchRanksWithinTheProvenReceiverGroup()throws Exception {
        StringBuilder source=new StringBuilder("""
                public class GroupRank {
                  public static class Box {public void use(Object value){}}
                  public static class Base {public void first(){} public void second(){}}
                  static void hit(){} static void noise(){}
                """);
        for(int i=0;i<12;i++)source.append("public static class Quiet").append(i).append(" extends Base {public void second(){noise();}}");
        source.append("public static class ZPreferred extends Base {Box box;public void second(){box.use(this);hit();}} public static void scan(Base input){input.first();input.second();}}");
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("GroupRank.java",source.toString()));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);MethodId preferred=new MethodId("GroupRank$ZPreferred","second","()V");
            Path reference=ReferenceFixtures.write(temp.resolve("group-ranking.json"),program,preferred);
            var result=new Analyzer(program,new Mechanisms(program,Catalog.read(reference),Set.of(),3),new Analyzer.Limits(100,200_000,20,30_000,1000,3))
                    .scan(EntryPoints.Mode.COMPONENT,true,Set.of(new MethodId("GroupRank","scan","(LGroupRank$Base;)V")));
            Set<String> reached=new HashSet<>();result.relations().stream().flatMap(relation -> relation.target().stream())
                    .filter(target -> target.owner().equals("GroupRank")).map(MethodId::name).forEach(reached::add);
            assertTrue(reached.contains("hit"),"the later call must use its own ranking within the selected receiver group");
            assertTrue(reached.contains("noise"),"an ordinary receiver must retain a turn");
        }
    }
    @Test void tentativeHandoffsGainTimeWithoutStarvingAnOrdinaryEntry()throws Exception {
        StringBuilder source=new StringBuilder("public class Fair {static class Box {void use(Object value){}} static class Input {Box box;} static void valuable(){} static void ordinary(){} static void noise(){} public static void selected(Input in){in.box.use(in);valuable();} public static void holdout(){ordinary();}");
        for(int i=0;i<20;i++)source.append("public static void n").append(i).append("(){noise();noise();noise();noise();}");source.append('}');
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fair.java",source.toString()));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);MethodId selected=new MethodId("Fair","selected","(LFair$Input;)V");
            Path file=ReferenceFixtures.write(temp.resolve("reference.json"),program,selected);
            Set<MethodId> entries=new LinkedHashSet<>();for(int i=0;i<20;i++)entries.add(new MethodId("Fair","n"+i,"()V"));
            entries.add(new MethodId("Fair","holdout","()V"));entries.add(selected);
            var result=new Analyzer(program,new Mechanisms(program,Catalog.read(file)),new Analyzer.Limits(500,70,20,5000,100,64))
                    .scan(EntryPoints.Mode.COMPONENT,true,entries);
            Set<String> reached=new HashSet<>();result.relations().stream().flatMap(r -> r.target().stream())
                    .filter(t -> t.owner().equals("Fair") && Set.of("valuable","ordinary").contains(t.name())).forEach(t -> reached.add(t.name()));
            assertEquals(Set.of("valuable","ordinary"),reached,"tentative guidance and an independent ordinary path both receive a turn");
        }
    }
    @Test void partialMemberShapesDoNotDisplaceTheOrdinaryProducerAndImpactFamilies()throws Exception {
        StringBuilder noise=new StringBuilder("public class Noise {StringBuilder owned;");
        for(int i=0;i<80;i++)noise.append("public String a").append(i).append("(){return owned.toString();}");
        noise.append('}');
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Noise.java",noise.toString(),"Calls.java","""
            public class Calls {public static void run(Class<?> owner,String name,Class<?>[] signature,Object receiver,Object[] arguments)throws Exception {
              Object produced=owner.getMethod(name,signature).invoke(receiver,arguments);
              produced.getClass().getMethod("exec",String.class).invoke(produced,new Object[]{"text"});
            }}
            """));
        for(boolean reference:List.of(false,true))try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            Path file=ReferenceFixtures.write(temp.resolve("noise-reference.json"),program,new MethodId("Noise","a0","()Ljava/lang/String;"),new MethodId("Calls","run","(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/Class;Ljava/lang/Object;[Ljava/lang/Object;)V"));
            var result=new Analyzer(program,new Mechanisms(program,reference?Catalog.read(file):Catalog.empty()),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,true,Set.of(new MethodId("Calls","run","(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/Class;Ljava/lang/Object;[Ljava/lang/Object;)V")));
            assertEquals(6,result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.target().stream()).filter(m -> m.owner().equals("java/lang/Runtime") && m.name().equals("exec")).map(MethodId::descriptor).distinct().count(),"a partial body shape cannot consume the ordinary factory/member frontier");
            assertTrue(result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).anyMatch(f -> java.util.stream.Stream.concat(f.path().stream(),f.supportingRelations().stream()).map(result.relations()::get).flatMap(r -> r.target().stream()).anyMatch(m -> m.owner().equals("java/lang/Runtime") && m.name().equals("getRuntime"))),"a produced receiver must continue to the next reflective call; reference="+reference);
        }
    }
    @Test void knowledgeCannotBorrowAnotherMapsKeyOrAnotherProxysHandler()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Isolated.java","""
            public class Isolated {
              interface Action {void act(String value);}
              static class Good implements Action {public void act(String value){hit(value);}}
              static class Quiet implements Action {public void act(String value){}}
              static void hit(String value){}
              static Action proxy(Action target) {
                return (Action)java.lang.reflect.Proxy.newProxyInstance(Action.class.getClassLoader(),new Class[]{Action.class},
                  (proxy,method,args)->{target.act((String)args[0]);return null;});
              }
              static void maps(boolean side,boolean positive) {
                java.util.Map<String,Action> left=new java.util.HashMap<>(),right=new java.util.HashMap<>();
                left.put("active",new Good());left.put("quiet",new Quiet());right.put("active",new Quiet());
                java.util.Map<String,Action> selected;String key;
                if(side){selected=left;key=positive?"active":"quiet";}else{selected=right;key="active";}
                selected.get(key).act("text");
              }
              public static void positive(){maps(true,true);proxy(new Good()).act("text");}
              public static void negative(boolean side){maps(side,false);Action unused=proxy(new Good());proxy(new Quiet()).act("text");}
            }
            """));
        for(boolean guidance:List.of(false,true))for(String entry:List.of("positive","negative"))try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            Path file=ReferenceFixtures.write(temp.resolve("isolated-reference.json"),program,new MethodId("Isolated","maps","(ZZ)V"),new MethodId("Isolated","proxy","(LIsolated$Action;)LIsolated$Action;"));
            MethodId sink=new MethodId("Isolated","hit","(Ljava/lang/String;)V");
            var result=new Analyzer(program,new Mechanisms(program,Catalog.read(file),Set.of(sink)),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,guidance,Set.of(new MethodId("Isolated",entry,entry.equals("positive")?"()V":"(Z)V")));
            assertEquals(entry.equals("positive"),result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT),"map identity, key and handler belong to their actual path: "+entry+" guidance="+guidance+"; "+result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).map(f -> f.path().stream().map(result.relations()::get).map(r -> r.site()+" -> "+r.target()+" receiver="+r.receiver()+" arguments="+r.arguments()).toList()).toList());
        }
    }
    @Test void aPartialReferenceOrdersActualBindingsWhileAnUnmatchedPathKeepsItsTurn()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Renamed.java","""
            public class Renamed {
              public static class Bound {public void accept(String value){terminal(value);}}
              public static class Other {public void accept(String value){wrong();}}
              static void wrong(){}static void terminal(String value){}static void holdout(String value){}
              static void forward(Object receiver,String name,String value)throws Exception {receiver.getClass().getMethod(name,String.class).invoke(receiver,value);}
              public static void run(String value)throws Exception {forward(new Bound(),"accept",value);holdout(value);}
            }
            """));
        for(boolean guidance:List.of(false,true))try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);Set<MethodId> sinks=Set.of(new MethodId("Renamed","terminal","(Ljava/lang/String;)V"),new MethodId("Renamed","holdout","(Ljava/lang/String;)V"));
            Path file=ReferenceFixtures.write(temp.resolve("reference.json"),program,new MethodId("Renamed","forward","(Ljava/lang/Object;Ljava/lang/String;Ljava/lang/String;)V"));
            var result=new Analyzer(program,new Mechanisms(program,Catalog.read(file),sinks),new Analyzer.Limits(300,5000,20,5000,100,64))
                    .scan(EntryPoints.Mode.COMPONENT,guidance,Set.of(new MethodId("Renamed","run","(Ljava/lang/String;)V")));
            Set<MethodId> reached=new HashSet<>();result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.target().stream()).forEach(reached::add);
            assertEquals(sinks,reached,"an independent ordinary path keeps its exploration opportunity");
            assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.IMPACT).allMatch(r -> r.arguments().stream().anyMatch(a -> Values.source(a).filter(s -> s.parameterSlot()==0).isPresent())));
            assertFalse(result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("Renamed$Other") || t.name().equals("wrong")));
            if(guidance) {
                assertTrue(result.statistics().rankingWork()>0);
                assertTrue(result.hints().stream().anyMatch(h -> h.mechanism().equals("reference:source-relations")));
            } else assertEquals(0,result.statistics().rankingWork());
        }
    }
}
