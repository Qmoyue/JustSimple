package io.just;

import io.just.analysis.*;
import io.just.input.*;
import io.just.knowledge.*;
import io.just.program.Program;
import io.just.program.Program.MethodId;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class MechanismHandoffTest {
    @TempDir Path temp;
    @Test void externalizableCanConsumeAnotherStreamAndReachNoDataWithoutLosingItsCallers()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","""
            import java.io.*;
            public class Fixture {
              static ObjectInputStream next;
              static void boundary(){}
              public static Object read(ObjectInputStream outer,ObjectInputStream inner)throws Exception {next=inner;return outer.readObject();}
              public static class Envelope implements Externalizable {
                public Envelope(){}
                public void readExternal(ObjectInput in)throws IOException,ClassNotFoundException {next.readObject();}
                public void writeExternal(ObjectOutput out){}
              }
              public static abstract class Parent implements Serializable {private void readObjectNoData(){boundary();}}
              public static class Child extends Parent {private void readObject(ObjectInputStream in){}}
            }
            """));
        MethodId entry=new MethodId("Fixture","read","(Ljava/io/ObjectInputStream;Ljava/io/ObjectInputStream;)Ljava/lang/Object;");
        MethodId sink=new MethodId("Fixture","boundary","()V");
        for(boolean present:List.of(false,true)) {
            Path data=temp.resolve("data-"+present+".json");Files.writeString(data,"""
                {"source":"independent source-built mechanism handoff","basis":"BINDING",
                 "entry":{"owner":"Fixture","name":"read","descriptor":"(Ljava/io/ObjectInputStream;Ljava/io/ObjectInputStream;)Ljava/lang/Object;","arguments":[{"ref":"outer"},{"ref":"inner"}]},
                 "objects":[{"id":"outer","type":"java/io/ObjectInputStream","decoded":{"ref":"envelope"}},
                 {"id":"inner","type":"java/io/ObjectInputStream","decoded":{"ref":"child"}},
                 {"id":"envelope","type":"Fixture$Envelope"},
                 {"id":"child","type":"Fixture$Child","classData":[{"owner":"Fixture$Parent","present":PRESENT}]}]}
                """.replace("PRESENT",String.valueOf(present)));
            try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
                Program program=new Program(input,20_000);Mechanisms mechanisms=new Mechanisms(program,Catalog.empty(),Set.of(sink));
                ScanResult result=new Analyzer(program,mechanisms,Analyzer.Limits.defaults()).scan(EntryPoints.Mode.APPLICATION,false,Set.of(entry),Optional.of(StaticData.read(data)));
                var hits=result.findings().stream().filter(f -> !f.path().isEmpty() && result.relations().get(f.path().get(f.path().size()-1)).target().filter(sink::equals).isPresent()).toList();
                assertEquals(!present,!hits.isEmpty(),result.limitations().toString());
                if(present)continue;
                assertTrue(hits.stream().anyMatch(f -> {
                    Set<String> methods=new HashSet<>();f.path().stream().map(result.relations()::get).flatMap(r -> r.target().stream()).forEach(m -> methods.add(m.name()));
                    return methods.containsAll(Set.of("readExternal","readObjectNoData","boundary"));
                }),"the nested route must preserve both protocol callers");
                for(var hit:hits) {
                    Map<Integer,Integer> proof=new HashMap<>();hit.proof().forEach(use -> proof.put(use.relation(),use.support()));
                    assertTrue(proof.keySet().containsAll(hit.path()));
                    proof.forEach((relation,support) -> assertTrue(proof.keySet().containsAll(result.relations().get(relation).supports().get(support).dependencies()),"selected support must be closed"));
                }
            }
        }
    }
}
