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

class ReferenceTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String entry,String descriptor)throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,false,
                    Set.of(new Program.MethodId("ReferencesFlow",entry,descriptor)));
        }
    }
    private Set<String> targets(ScanResult result){Set<String> names=new HashSet<>();result.relations().forEach(r -> r.target().filter(t -> t.owner().equals("ReferencesFlow")).ifPresent(t -> names.add(t.name())));return names;}
    private Path fixture()throws Exception {
        return BytecodeFixtures.compile(temp,8,Map.of("ReferencesFlow.java","""
                import javax.naming.*;
                public class ReferencesFlow {
                  static void hit(){}static void wrong(){}static void good(){}static void caught(){}
                  public static class Own extends Reference {public Own(){super("kind", "wrong",null);}public String getFactoryClassName(){return "hit";}}
                  static void use(String name)throws Exception {ReferencesFlow.class.getDeclaredMethod(name).invoke(null);}
                  public static void names()throws Exception {Reference first=new Reference("kind",new StringRefAddr("name","hit"),"Factory",null);first.add(new StringRefAddr("name","wrong"));Reference other=new Reference("other",new StringRefAddr("name","wrong"));if(!first.getClassName().equals("kind")||!first.getFactoryClassName().equals("Factory")||first.getFactoryClassLocation()!=null||first.size()!=2)wrong();use((String)first.get("name").getContent());if(!other.get("name").getContent().equals("wrong")||!first.get(1).getContent().equals("wrong"))wrong();}
                  public static void clear()throws Exception {Reference ref=new Reference("kind",new StringRefAddr("name","wrong"));ref.clear();ref.add(new StringRefAddr("name","hit"));use((String)ref.get("name").getContent());}
                  public static void absent(){Reference ref=new Reference("kind");if(ref.get((String)null)==null && ref.get("missing")==null && ref.size()==0)good();else wrong();}
                  public static void nullContent(){StringRefAddr addr=new StringRefAddr("name",null);if(addr.getContent()==null && addr.getType().equals("name"))good();else wrong();}
                  public static void nullName(){Reference ref=new Reference("kind",new StringRefAddr("name","hit"));try{ref.get((String)null);wrong();}catch(NullPointerException expected){caught();}}
                  public static void nullAddress(){Reference ref=new Reference("kind",(RefAddr)null);try{ref.get("name");wrong();}catch(NullPointerException expected){caught();}}
                  public static void changed()throws Exception {Reference ref=new Reference("kind",new StringRefAddr("name","wrong"));ref.add(0,new StringRefAddr("name","hit"));use((String)ref.get("name").getContent());}
                  public static void override()throws Exception {use(new Own().getFactoryClassName());}
                  public static void unknown(String text){Reference ref=new Reference("kind",new StringRefAddr("name",text));if(ref.get("name").getContent()==null)caught();else good();}
                }
                """));
    }
    @Test void referenceFieldsAndOrderedAddressesStayWithTheirObjects()throws Exception {
        Path classes=fixture();assertEquals(Set.of("use","hit"),targets(scan(classes,"names","()V")));
        assertEquals(Set.of("use","hit"),targets(scan(classes,"clear","()V")));
        assertEquals(Set.of("use","hit"),targets(scan(classes,"override","()V")));
    }
    @Test void absenceNullAndNullDereferenceHaveDifferentResults()throws Exception {
        Path classes=fixture();
        for(String entry:List.of("absent","nullContent"))assertEquals(Set.of("good"),targets(scan(classes,entry,"()V")),entry);
        for(String entry:List.of("nullName","nullAddress"))assertEquals(Set.of("caught"),targets(scan(classes,entry,"()V")),entry);
    }
    @Test void unsupportedMutationInvalidatesPrecisionAndUnknownContentDoesNotBecomeNull()throws Exception {
        Path classes=fixture();var changed=scan(classes,"changed","()V");
        assertTrue(changed.findings().stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.UNSUPPORTED));
        assertTrue(changed.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("ReferencesFlow") && t.name().equals("wrong")).isPresent()).noneMatch(r -> r.supports().stream().anyMatch(s -> s.gaps().isEmpty())));
        var unknown=scan(classes,"unknown","(Ljava/lang/String;)V");
        assertTrue(targets(unknown).containsAll(Set.of("caught","good")));
        assertTrue(unknown.relations().stream().filter(r -> r.kind()==Kind.FIELD_FLOW).flatMap(r -> r.arguments().stream()).anyMatch(a -> a instanceof ObjectValue o && o.source().isPresent()));
    }
}
