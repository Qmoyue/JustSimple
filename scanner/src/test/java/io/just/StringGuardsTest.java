package io.just;

import io.just.knowledge.EntryPoints;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.Mechanisms;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class StringGuardsTest {
    @TempDir Path temp;
    private Set<String> targets(Path classes,String entry,String descriptor)throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            var result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Guards",entry,descriptor)));
            Set<String> names=new HashSet<>();
            result.relations().forEach(r -> r.target().filter(t -> t.owner().equals("Guards")).ifPresent(t -> names.add(t.name())));
            return names;
        }
    }
    private Path fixture()throws Exception {
        return BytecodeFixtures.compile(temp,8,Map.of("Guards.java","""
                public class Guards {
                  static void wrong(){} static void empty(){} static void unicode(){} static void denied(){}
                  static void yes(){} static void no(){} static void after(){} static void caught(){}
                  static boolean allowed(String text){return text.startsWith("allow");}
                  public static void known(){if(!"allowed".startsWith("all"))wrong();if("".isEmpty())empty();if("😀".length()==2)unicode();else wrong();if("blocked".startsWith("all"))wrong();else denied();}
                  public static void nulls(){try{"abc".startsWith(null);wrong();}catch(NullPointerException expected){caught();}try{String nil=null;nil.isEmpty();wrong();}catch(NullPointerException expected){after();}}
                  public static void unknown(String prefix){if("allowed".startsWith(prefix))yes();else no();after();}
                  public static void separate(){if(allowed("allowed")&&allowed("blocked"))wrong();"blocked".startsWith("allow");if(allowed("allowed"))yes();else no();after();}
                  public static void both(){if("allowed".startsWith("allow"))yes();else no();after();}
                  public static void classNames(){if(String.class.getName().equals("java.lang.String") && int.class.getName().equals("int") && String[].class.getName().equals("[Ljava.lang.String;"))yes();else wrong();}
                }
                """));
    }
    @Test void finitePredicatesSelectOnlyTheCompatibleBranches()throws Exception {
        Set<String> calls=targets(fixture(),"known","()V");
        assertTrue(calls.containsAll(Set.of("empty","unicode","denied")));
        assertFalse(calls.contains("wrong"));
    }
    @Test void nullsThrowAndUnknownPrefixesKeepBothBranches()throws Exception {
        Path classes=fixture();
        Set<String> nulls=targets(classes,"nulls","()V");
        assertTrue(nulls.containsAll(Set.of("caught","after")));assertFalse(nulls.contains("wrong"));
        assertTrue(targets(classes,"unknown","(Ljava/lang/String;)V").containsAll(Set.of("yes","no","after")));
    }
    @Test void guardsRemainLocalToTheirValuesAndActualControlFlow()throws Exception {
        Path classes=fixture();
        Set<String> separate=targets(classes,"separate","()V");
        assertTrue(separate.containsAll(Set.of("yes","after")));assertFalse(separate.contains("wrong"));assertFalse(separate.contains("no"));
        assertTrue(targets(classes,"both","()V").contains("after"));
        Set<String> names=targets(classes,"classNames","()V");assertTrue(names.contains("yes"));assertFalse(names.contains("wrong"));
    }
}
