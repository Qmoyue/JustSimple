package io.just;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.program.Program;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

/** Cross-component regressions at the scan boundary; target bytecode is never executed. */
class PropagationBoundaryTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String name,String descriptor)throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.APPLICATION,false,Set.of(new MethodId("Fixture",name,descriptor)));
        }
    }
    private boolean calls(ScanResult result,String name) {
        return result.relations().stream().flatMap(relation -> relation.target().stream())
                .anyMatch(target -> target.owner().equals("Fixture") && target.name().equals(name));
    }
    private Path compile(String source)throws Exception{return BytecodeFixtures.compile(temp,17,Map.of("Fixture.java",source));}

    @Test void platformSummariesKeepUnknownReceiverOverridesAndExactControls()throws Exception {
        Path classes=compile("""
            import java.util.*;
            public class Fixture {
              static void putHit(){} static void viewHit(){} static void platformHit(){}
              public static class Custom extends HashMap<String,String> {
                public String put(String key,String value){putHit();return null;}
                public Set<Map.Entry<String,String>> entrySet(){viewHit();return Collections.emptySet();}
              }
              public static class Inherited extends Custom {}
              public static void put(HashMap<String,String> map){map.put("key","value");}
              public static void view(HashMap<String,String> map){map.entrySet();}
              public static void exact(){put(new Inherited());view(new Inherited());}
              public static void platform(){HashMap<String,String> map=new HashMap<>();map.put("key","value");if("value".equals(map.get("key")))platformHit();map.entrySet();}
            }
            """);
        assertTrue(calls(scan(classes,"put","(Ljava/util/HashMap;)V"),"putHit"));
        assertTrue(calls(scan(classes,"view","(Ljava/util/HashMap;)V"),"viewHit"));
        ScanResult exact=scan(classes,"exact","()V");
        assertTrue(calls(exact,"putHit"));assertTrue(calls(exact,"viewHit"));
        ScanResult platform=scan(classes,"platform","()V");
        assertTrue(calls(platform,"platformHit"));
        assertFalse(calls(platform,"putHit"));assertFalse(calls(platform,"viewHit"));
    }

    @Test void opaqueCallsFollowViewsEntriesCapturedValuesAndNestedReferences()throws Exception {
        Path classes=compile("""
            import java.util.*;
            public class Fixture {
              static native void opaque(Object value);
              static void hit(){} static void wrong(){}
              public static class Holder {public Object value="before";}
              public static void map(){HashMap<String,String> map=new HashMap<>();map.put("key","before");opaque(map);if(map.get("key")==null)hit();}
              public static void entry(){HashMap<String,String> map=new HashMap<>();map.put("key","before");opaque(map.entrySet().iterator().next());if(map.get("key")==null)hit();}
              public static void view(){HashMap<String,String> map=new HashMap<>();map.put("key","before");opaque(map.values());if(map.get("key")==null)hit();}
              public static void holder(){Holder h=new Holder();opaque(h);if(h.value==null)hit();}
              public static void captured(){Holder h=new Holder();Runnable r=()->h.value=null;opaque(r);if(h.value==null)hit();}
              public static void nested(){HashMap<String,String> map=new HashMap<>();map.put("key","before");Holder h=new Holder();h.value=map.values();opaque(h);if(map.get("key")==null)hit();}
              public static void array(){Object[] values=new Object[]{"before"};opaque(values);if(values.length!=1)wrong();if(values[0]==null)hit();}
              public static void restored(){Holder h=new Holder();Runnable r=()->h.value=null;opaque(r);h.value="after";if(h.value==null)wrong();else hit();}
              public static void unrelated(){Holder h=new Holder();HashMap<String,String> map=new HashMap<>();map.put("key","before");opaque(map.values());if(h.value==null)wrong();else hit();}
            }
            """);
        for(String method:List.of("map","entry","view","holder","captured","nested"))
            assertTrue(calls(scan(classes,method,"()V"),"hit"),method);
        for(String method:List.of("restored","unrelated")) {
            ScanResult result=scan(classes,method,"()V");
            assertTrue(calls(result,"hit"),method);assertFalse(calls(result,"wrong"),method);
        }
        ScanResult array=scan(classes,"array","()V");
        assertTrue(calls(array,"hit"),"array elements remain subject to the opaque mutation");
        assertFalse(calls(array,"wrong"),"the same array retains its length after the call");
    }

    @Test void conditionalEffectsKeepNormalAndExceptionalBranchesSeparate()throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void hit(){} static void wrong(){} static void caught(){}
              public static class Known {public void accept(String value){hit();}}
              public static void mixed(boolean flag)throws Exception {
                Class<?> type=flag?String.class:Integer.class;
                Known.class.getMethod("accept",new Class[]{type}).invoke(new Known(),"value");
                if(!flag)wrong();
              }
              public static void valid()throws Exception {Known.class.getMethod("accept",String.class).invoke(new Known(),"value");}
              public static void invalid()throws Exception {
                try{Known.class.getMethod("accept",Integer.class).invoke(new Known(),"value");wrong();}catch(NoSuchMethodException expected){caught();}
              }
              public static void before()throws Exception {
                Known.class.getMethod("absent",String.class);
                Known.class.getMethod("accept",String.class).invoke(new Known(),"value");
              }
              public static void after()throws Exception {
                Known.class.getMethod("accept",String.class);
                Known.class.getMethod("absent",String.class);
                wrong();
              }
            }
            """);
        ScanResult mixed=scan(classes,"mixed","(Z)V");
        assertTrue(calls(mixed,"hit"));assertFalse(calls(mixed,"wrong"));
        assertTrue(calls(scan(classes,"valid","()V"),"hit"));
        ScanResult invalid=scan(classes,"invalid","()V");
        assertTrue(calls(invalid,"caught"));assertFalse(calls(invalid,"hit"));assertFalse(calls(invalid,"wrong"));
        assertFalse(calls(scan(classes,"before","()V"),"hit"));
        assertFalse(calls(scan(classes,"after","()V"),"wrong"));
    }

    @Test void definitionsDistinguishReplaySequentialCallsPathsAndLoaders()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","""
            public class Fixture {
              static void hit(){}static void wrong(){}static void caught(){}
              public static class Loader extends ClassLoader {public Class<?> make(byte[] bytes){return defineClass(null,bytes,0,bytes.length);}}
              static byte[] bytes()throws Exception{return Fixture.class.getResourceAsStream("/Stage.class").readAllBytes();}
              public static void once()throws Exception {new Loader().make(bytes()).getMethod("done").invoke(null);hit();}
              public static void twice()throws Exception {
                Loader loader=new Loader();byte[] code=bytes();loader.make(code);
                try{loader.make(code);wrong();}catch(LinkageError expected){caught();}
              }
              public static void freshRead()throws Exception {
                Loader loader=new Loader();loader.make(bytes());
                try{loader.make(bytes());wrong();}catch(LinkageError expected){caught();}
              }
              public static void exclusive(boolean flag)throws Exception {
                Loader loader=new Loader();byte[] code=bytes();
                if(flag)loader.make(code);else loader.make(code);hit();
              }
              public static void separate()throws Exception {byte[] code=bytes();new Loader().make(code);new Loader().make(code);hit();}
            }
            ""","Stage.java","public class Stage {public static void done(){}}"));
        for(String method:List.of("once","separate"))assertTrue(calls(scan(classes,method,"()V"),"hit"),method);
        assertTrue(calls(scan(classes,"exclusive","(Z)V"),"hit"));
        for(String method:List.of("twice","freshRead")) {
            ScanResult result=scan(classes,method,"()V");
            assertTrue(calls(result,"caught"),method);assertFalse(calls(result,"wrong"),method);
        }
    }

    @Test void smallCollectionsUseKnownLengthsActualOverridesAndImmutableFailures()throws Exception {
        Path classes=compile("""
            import java.util.*;
            public class Fixture {
              static void hit(){}static void wrong(){}static void caught(){}
              public static class Custom extends ArrayList<String> {public int size(){hit();return 7;}public boolean add(String value){hit();return true;}}
              public static void list(){List<String> list=new ArrayList<>();list.add("x");if(list.size()==0)wrong();if(list.size()==1)hit();}
              public static void view(){String[] array={"a","b"};List<String> list=Arrays.asList(array);if(list.size()==0)wrong();if(list.size()==2)hit();}
              public static void immutable(){Map<String,String> map=Collections.emptyMap();if(map.size()==0)hit();try{map.put("a","b");wrong();}catch(UnsupportedOperationException expected){caught();}}
              public static void emptyIdentity(){if(Collections.emptyMap()!=Collections.emptyMap())wrong();else hit();}
              public static void override(){List<String> list=new Custom();list.add("x");if(list.size()==7)hit();}
              public static void unknown(List<String> list){if(list.size()==0)hit();}
            }
            """);
        for(String method:List.of("list","view","immutable","emptyIdentity")) {
            ScanResult result=scan(classes,method,"()V");
            assertTrue(calls(result,"hit"),method);assertFalse(calls(result,"wrong"),method);
            if(method.equals("immutable"))assertTrue(calls(result,"caught"));
        }
        assertTrue(calls(scan(classes,"override","()V"),"hit"));
        assertTrue(calls(scan(classes,"unknown","(Ljava/util/List;)V"),"hit"));
    }

    @Test void integralConditionsKeepSourceIdentityApiRangesAndOverflowUncertainty()throws Exception {
        Path classes=compile("""
            import java.io.*;
            public class Fixture {
              static void hit(){}static void wrong(){}
              public static class Bad {} public static class Safe {}
              public static void zero(int n){if(n==0 && n>0)wrong();}
              public static void positive(int n){if(n>0 && n<=5)hit();}
              public static void independent(int a,int b){if(a==0 && b>0)hit();}
              public static void loop(int n){Object value=n==0?new Bad():new Safe();for(int i=0;i<n;i++)if(value instanceof Bad)wrong();}
              public static void unsigned(ObjectInputStream in)throws IOException {if(in.readUnsignedByte()<0)wrong();}
              public static void shortRange(ObjectInputStream in)throws IOException {if(in.readShort()>32767)wrong();}
              public static void unsignedShort(ObjectInputStream in)throws IOException {if(in.readUnsignedShort()>65535)wrong();}
              public static void readPositive(ObjectInputStream in)throws IOException {if(in.readUnsignedByte()==255)hit();}
              public static void overflow(int n){if(n>0 && n+Integer.MAX_VALUE<0)hit();}
            }
            """);
        for(String method:List.of("zero","loop"))assertFalse(calls(scan(classes,method,"(I)V"),"wrong"),method);
        for(String method:List.of("unsigned","shortRange","unsignedShort"))
            assertFalse(calls(scan(classes,method,"(Ljava/io/ObjectInputStream;)V"),"wrong"),method);
        for(String method:List.of("positive","overflow"))assertTrue(calls(scan(classes,method,"(I)V"),"hit"),method);
        assertTrue(calls(scan(classes,"independent","(II)V"),"hit"));
        assertTrue(calls(scan(classes,"readPositive","(Ljava/io/ObjectInputStream;)V"),"hit"));
    }
}
