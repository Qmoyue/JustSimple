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

    @Test void stackOperationsPreserveContentsExceptionsAndOverrides()throws Exception {
        Path classes=compile("""
            import java.util.*;
            public class Fixture {
              static void hit(){} static void wrong(){} static void caught(){}
              public static class Custom extends Stack<String> {public String pop(){hit();return "custom";}}
              public static void known(){
                Stack<String> first=new Stack<>(),second=new Stack<>();
                if(!first.empty())wrong();
                first.push("a");first.push("b");second.push("other");
                if(!"b".equals(first.pop()))wrong();
                if(!"other".equals(second.pop()))wrong();
                if(!"a".equals(first.pop()))wrong();
                if(!first.empty())wrong();
                try{first.pop();wrong();}catch(EmptyStackException expected){caught();}
                hit();
              }
              public static void override(){new Custom().pop();}
              public static void unknown(Stack<String> stack){try{stack.pop();hit();}catch(EmptyStackException expected){caught();}}
            }
            """);
        ScanResult known=scan(classes,"known","()V");
        assertTrue(calls(known,"hit"));assertTrue(calls(known,"caught"));assertFalse(calls(known,"wrong"));
        assertTrue(calls(scan(classes,"override","()V"),"hit"));
        ScanResult unknown=scan(classes,"unknown","(Ljava/util/Stack;)V");
        assertTrue(calls(unknown,"hit"));assertTrue(calls(unknown,"caught"));
    }

    @Test void loopGuardsAndMutationsUseTheSameObservedHeapVersion()throws Exception {
        Path classes=compile("""
            import java.util.*;
            public class Fixture {
              int fieldCount;
              static void hit(){} static void wrong(){}
              public static void guarded(int count){
                Stack<String> stack=new Stack<>();stack.push("a");stack.push("b");
                try{for(int i=0;i<count;i++)if(!stack.empty())stack.pop();}
                catch(EmptyStackException expected){wrong();}
              }
              public void guardedField(){
                Stack<String> stack=new Stack<>();stack.push("a");stack.push("b");
                try{for(int i=0;i<fieldCount;i++)if(!stack.empty())stack.pop();}
                catch(EmptyStackException expected){wrong();}
              }
              public void thisIsNonNull(){try{fieldCount++;}catch(NullPointerException impossible){wrong();}}
              public static void argumentCanBeNull(Fixture value){try{value.fieldCount++;}catch(NullPointerException expected){hit();}}
              public static void unguarded(int count){
                Stack<String> stack=new Stack<>();stack.push("a");stack.push("b");
                try{for(int i=0;i<count;i++)stack.pop();}
                catch(EmptyStackException expected){hit();}
              }
              public static void changed(){
                Stack<String> stack=new Stack<>();stack.push("a");boolean wasEmpty=stack.empty();stack.pop();
                try{if(!wasEmpty)stack.pop();}catch(EmptyStackException expected){hit();}
              }
              public static void separate(){
                Stack<String> first=new Stack<>(),second=new Stack<>();first.push("a");
                try{if(!first.empty())second.pop();}catch(EmptyStackException expected){hit();}
              }
              public static void afterLoop(){
                Stack<String> stack=new Stack<>();int i=0;while(i<1)i++;
                try{if(i==0)stack.pop();}catch(EmptyStackException expected){wrong();}
              }
            }
            """);
        assertFalse(calls(scan(classes,"guarded","(I)V"),"wrong"));
        assertFalse(calls(scan(classes,"guardedField","()V"),"wrong"));
        assertFalse(calls(scan(classes,"thisIsNonNull","()V"),"wrong"));
        assertTrue(calls(scan(classes,"argumentCanBeNull","(LFixture;)V"),"hit"));
        assertTrue(calls(scan(classes,"unguarded","(I)V"),"hit"));
        for(String name:List.of("changed","separate"))assertTrue(calls(scan(classes,name,"()V"),"hit"),name);
        assertFalse(calls(scan(classes,"afterLoop","()V"),"wrong"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);MethodId entry=new MethodId("Fixture","changed","()V"),sink=new MethodId("Fixture","hit","()V");
            Site firstPop=program.facts(entry).actions().stream().filter(Call.class::isInstance).map(Call.class::cast)
                    .filter(call -> call.target().name().equals("pop")).findFirst().orElseThrow().site();
            ScanResult result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(sink),8),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.APPLICATION,false,Set.of(entry));
            assertTrue(result.findings().stream().filter(f -> f.boundary()==Values.Kind.IMPACT).anyMatch(f ->
                    java.util.stream.Stream.concat(f.path().stream(),f.supportingRelations().stream()).map(result.relations()::get)
                            .anyMatch(r -> r.site().equals(firstPop) && r.slot().filter(Values.Length.class::isInstance).isPresent()
                                    && r.arguments().contains(new Values.Literal(0)))),"the exception must retain the write that made the stack empty");
        }
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

    @Test void provenLoopExitCoversEarlierExitsWithoutHidingAnUnknownContinuation()throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void zero(){} static void one(){} static void two(){} static void hit(){}
              public static void bounded(int count){
                int seen=0;
                for(int i=0;i<count;i++){if(i==2)break;seen=i+1;}
                if(seen==0)zero();if(seen==1)one();if(seen==2)two();
              }
              public static void mayContinue(int count,boolean stop){
                for(int i=0;i<count;i++){if(i==2 && stop)break;hit();}
              }
              public static void mayContinueWithoutEffects(int count,boolean stop){
                for(int i=0;i<count;i++)if(i==2 && stop)break;
              }
              public static void finiteEarlyExit(){
                int seen=0;for(int i=0;i<3;i++){if(i==0)break;seen=i+1;}if(seen==0)zero();
              }
              public static void finiteExceptionalExit(){
                int seen=0;try{for(int i=0;i<3;i++){if(i==0)throw null;seen=i+1;}}
                catch(NullPointerException expected){}if(seen==0)zero();
              }
              public static void sequentialLoops(int count){
                int seen=0;for(int i=0;i<count;i++){if(i==1)break;seen=1;}
                for(int i=0;i<1;i++){}if(seen==0)zero();if(seen==1)one();
              }
              public static void finiteWithoutBreak(){
                int seen=0;for(int i=0;i<2;i++)seen=i+1;if(seen==0)zero();if(seen==2)two();
              }
            }
            """);
        ScanResult bounded=scan(classes,"bounded","(I)V");
        for(String method:List.of("zero","one","two"))assertTrue(calls(bounded,method),method);
        assertEquals(ScanResult.Execution.FINISHED,bounded.execution(),bounded.limitations().toString());
        ScanResult unknown=scan(classes,"mayContinue","(IZ)V");
        assertTrue(calls(unknown,"hit"));
        assertEquals(ScanResult.Execution.TRUNCATED,unknown.execution());
        assertTrue(unknown.limitations().stream().anyMatch(limit -> limit.startsWith("counter loop prefix")));
        assertEquals(ScanResult.Execution.TRUNCATED,scan(classes,"mayContinueWithoutEffects","(IZ)V").execution());
        assertTrue(calls(scan(classes,"finiteEarlyExit","()V"),"zero"));
        assertTrue(calls(scan(classes,"finiteExceptionalExit","()V"),"zero"));
        ScanResult sequential=scan(classes,"sequentialLoops","(I)V");
        assertTrue(calls(sequential,"zero"));assertTrue(calls(sequential,"one"));
        ScanResult finite=scan(classes,"finiteWithoutBreak","()V");
        assertFalse(calls(finite,"zero"));assertTrue(calls(finite,"two"));
    }

    @Test void reflectiveArrayAccessRespectsWritesAndObjectIdentity()throws Exception {
        Path classes=compile("""
            import java.lang.reflect.Array;
            public class Fixture {
              static void hit(){} static void wrong(){} static void caught(){}
              static native void mutate(Object value);
              public static class Target {void invoke(){hit();}}
              public static void replaced(Object array){
                try{Array.set(array,0,"safe");((Target)Array.get(array,0)).invoke();wrong();}
                catch(RuntimeException expected){}
              }
              public static void inserted(Object array){
                try{Array.set(array,0,new Target());((Target)Array.get(array,0)).invoke();}
                catch(RuntimeException expected){}
              }
              public static void otherIndex(Object array){
                try{Array.set(array,0,"safe");if(Array.get(array,1) instanceof Target)hit();}
                catch(RuntimeException expected){}
              }
              public static void otherObject(Object first,Object second){
                try{Array.set(first,0,"safe");if(Array.get(second,0) instanceof Target)hit();}
                catch(RuntimeException expected){}
              }
              public static void changed(Object array){
                try{Array.set(array,0,"safe");mutate(array);if(Array.get(array,0) instanceof Target)hit();}
                catch(RuntimeException expected){}
              }
              public static void exact(){
                Object[] array={"before"};Array.set(array,0,"after");
                if("after".equals(Array.get(array,0)))hit();if("before".equals(Array.get(array,0)))wrong();
              }
              public static void nullArray(){try{Array.get(null,0);}catch(NullPointerException expected){hit();}}
              public static void nonArray(){try{Array.get("not array",0);}catch(IllegalArgumentException expected){hit();}}
              public static void outOfBounds(){try{Array.get(new Object[0],0);}catch(ArrayIndexOutOfBoundsException expected){hit();}}
              public static void incompatible(){
                try{Array.set(new String[1],0,new Target());wrong();}catch(IllegalArgumentException expected){hit();}
              }
              public static void primitive(){
                int[] array={1};Array.set(array,0,Integer.valueOf(2));if(Array.get(array,0) instanceof Integer)hit();
              }
              public static void mixedLength(boolean flag){
                Object[] array=new Object[flag?0:1];
                try{Array.set(array,0,"safe");hit();}catch(ArrayIndexOutOfBoundsException expected){caught();}
              }
              public static void defaultElement(){
                Object[] array=new Object[1];try{((Target)Array.get(array,0)).invoke();wrong();}
                catch(NullPointerException expected){caught();}
              }
            }
            """);
        ScanResult replaced=scan(classes,"replaced","(Ljava/lang/Object;)V");
        assertFalse(calls(replaced,"hit"));assertFalse(calls(replaced,"wrong"));
        for(String method:List.of("inserted","otherIndex","otherObject","changed","nullArray","nonArray","outOfBounds","incompatible","primitive"))
            assertTrue(calls(scan(classes,method,method.equals("otherObject")?"(Ljava/lang/Object;Ljava/lang/Object;)V":
                    Set.of("inserted","otherIndex","changed").contains(method)?"(Ljava/lang/Object;)V":"()V"),"hit"),method);
        assertFalse(calls(scan(classes,"incompatible","()V"),"wrong"));
        ScanResult mixed=scan(classes,"mixedLength","(Z)V");assertTrue(calls(mixed,"hit"));assertTrue(calls(mixed,"caught"));
        ScanResult defaults=scan(classes,"defaultElement","()V");
        assertTrue(calls(defaults,"caught"));assertFalse(calls(defaults,"hit"));assertFalse(calls(defaults,"wrong"));
        ScanResult exact=scan(classes,"exact","()V");assertTrue(calls(exact,"hit"));assertFalse(calls(exact,"wrong"));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20_000);MethodId entry=new MethodId("Fixture","inserted","(Ljava/lang/Object;)V"),sink=new MethodId("Fixture","hit","()V");
            Site write=program.facts(entry).actions().stream().filter(Call.class::isInstance).map(Call.class::cast)
                    .filter(call -> call.target().owner().equals("java/lang/reflect/Array") && call.target().name().equals("set"))
                    .findFirst().orElseThrow().site();
            ScanResult result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(sink),8),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.APPLICATION,false,Set.of(entry));
            assertTrue(result.findings().stream().filter(f -> f.boundary()==Values.Kind.IMPACT).anyMatch(f ->
                    java.util.stream.Stream.concat(f.path().stream(),f.supportingRelations().stream()).map(result.relations()::get)
                            .anyMatch(r -> r.site().equals(write) && r.slot().equals(Optional.of(new Values.Index(0))))),
                    "the finding must retain the write that supplied the invoked receiver");
        }
    }

    @Test void memberClassCollectionsUseDeclarationsAndSuperclassVisibility()throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void hit(){} static void wrong(){}
              public static class Parent {
                public static class Inherited {int p;}
                private static class HiddenParent {int p;}
              }
              public static class Host extends Parent {
                public static class First {int a;}
                public static class Second {int b;}
                private static class Hidden {int c;}
              }
              public static void publicCount(){if(Host.class.getClasses().length==3)hit();else wrong();}
              public static void declaredCount(){if(Host.class.getDeclaredClasses().length==3)hit();else wrong();}
              public static void parentCount(){if(Parent.class.getClasses().length==1 && Parent.class.getDeclaredClasses().length==2)hit();else wrong();}
              public static void primitiveAndArray(){if(int.class.getClasses().length==0 && String[].class.getDeclaredClasses().length==0)hit();else wrong();}
              public static void modified(){Class<?>[] members=Host.class.getClasses();members[0]=String.class;if(members[0]==String.class)hit();}
              public static void sum(){int fields=0;for(Class<?> member:Host.class.getClasses())fields+=member.getDeclaredFields().length;
                if(fields==3)hit();else wrong();}
            }
            """);
        for(String method:List.of("publicCount","declaredCount","parentCount","primitiveAndArray","modified","sum")) {
            ScanResult result=scan(classes,method,"()V");assertTrue(calls(result,"hit"),method);assertFalse(calls(result,"wrong"),method);
        }
    }

    @Test void unknownReferenceArrayMembersKeepTheirTypeAndIdentity()throws Exception {
        Path classes=compile("""
            public class Fixture {
              interface Callback { void run(); }
              static class Active implements Callback { public void run(){hit();} }
              static class Quiet implements Callback { public void run(){safe();} }
              static void hit(){} static void safe(){}
              public static void input(Callback[] a){ a[0].run(); a[0].run(); }
              public static void fresh(){ Callback[] a=new Callback[1]; if(a[0]!=null)a[0].run(); else safe(); }
              public static void overwritten(Callback[] a){ a[0]=new Quiet(); a[0].run(); }
            }
            """);
        ScanResult input=scan(classes,"input","([LFixture$Callback;)V");
        assertTrue(calls(input,"hit"),"an unknown typed array element can be an active implementation");
        List<Values.ObjectValue> receivers=input.relations().stream()
                .filter(r -> r.target().filter(t -> t.owner().equals("Fixture$Active") && t.name().equals("run")).isPresent())
                .map(ScanResult.Relation::receiver).filter(Values.ObjectValue.class::isInstance).map(Values.ObjectValue.class::cast).toList();
        assertTrue(receivers.size()>=2,"both calls must expand");
        assertEquals(1,receivers.stream().map(Values.ObjectValue::id).distinct().count(),"repeated reads of the same slot share an identity");
        assertTrue(receivers.stream().allMatch(r -> r.source().map(s -> s.path().contains(new Values.Index(0))).orElse(false)));
        ScanResult fresh=scan(classes,"fresh","()V");
        assertTrue(calls(fresh,"safe"));assertFalse(calls(fresh,"hit"),"a fresh reference array starts with null elements");
        ScanResult overwritten=scan(classes,"overwritten","([LFixture$Callback;)V");
        assertTrue(calls(overwritten,"safe"));assertFalse(calls(overwritten,"hit"),"a known write replaces the conditional input");
    }

    @Test void unknownSerializedKeysRunTheirOwnHookBeforeHashing()throws Exception {
        for(String outcome:List.of("ready","quiet","throws")) {
            String action=switch(outcome){case "ready" -> "flag=true;";case "quiet" -> "flag=false;";default -> "throw new IOException();";};
            Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","""
                import java.io.*;
                public class Fixture {
                  static void hit(){}
                  public static class Key implements Serializable {
                    transient boolean flag;
                    private void readObject(ObjectInputStream in)throws IOException {%s}
                    public int hashCode(){if(flag)hit();return 0;}
                  }
                  public static void read(ObjectInputStream in)throws Exception {in.readObject();}
                }
                """.formatted(action)));
            try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
                Program program=new Program(inputs,20_000);MethodId entry=new MethodId("Fixture","read","(Ljava/io/ObjectInputStream;)V"),sink=new MethodId("Fixture","hit","()V");
                ScanResult result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(sink),64),Analyzer.Limits.defaults())
                        .scan(EntryPoints.Mode.APPLICATION,false,Set.of(entry));
                var findings=result.findings().stream().filter(f -> f.boundary()==Values.Kind.IMPACT).toList();
                assertEquals(outcome.equals("ready"),!findings.isEmpty(),outcome+": "+result.limitations());
                if(outcome.equals("ready"))assertTrue(findings.stream().anyMatch(f -> {
                    List<ScanResult.Relation> proof=java.util.stream.Stream.concat(f.path().stream(),f.supportingRelations().stream()).map(result.relations()::get).toList();
                    return proof.stream().filter(hash -> hash.target().filter(t -> t.owner().equals("Fixture$Key") && t.name().equals("hashCode")).isPresent())
                            .anyMatch(hash -> proof.stream().anyMatch(hook -> hook.receiver().equals(hash.receiver()) && hook.target().filter(t -> t.owner().equals("Fixture$Key") && t.name().equals("readObject")).isPresent())
                                    && proof.stream().anyMatch(write -> write.receiver().equals(hash.receiver())
                                            && write.slot().filter(slot -> slot instanceof Values.Field field && field.field().name().equals("flag")).isPresent()
                                            && write.arguments().contains(new Values.Literal(1))));
                }),"the same serialized key must carry its hook write into the hash callback");
            }
        }
    }

    @Test void unknownSerializedKeysHashTheReadResolveResult()throws Exception {
        for(String outcome:List.of("self","replacement","null","throws","unknown")) {
            String replacement=switch(outcome){case "self" -> "return this;";case "replacement" -> "return new Replacement();";case "null" -> "return null;";case "unknown" -> "return external();";default -> "throw new IllegalStateException();";};
            Path classes=compile("""
                import java.io.*;
                public class Fixture {
                  static void oldHash(){} static void newHash(){} static native Object external();
                  public static class Key implements Serializable {
                    private Object readResolve(){%s}
                    public int hashCode(){oldHash();return 0;}
                  }
                  public static class Replacement { public int hashCode(){newHash();return 0;} }
                  public static void read(ObjectInputStream in)throws Exception {in.readObject();}
                }
                """.formatted(replacement));
            ScanResult result=scan(classes,"read","(Ljava/io/ObjectInputStream;)V");
            assertEquals(outcome.equals("self") || outcome.equals("unknown"),calls(result,"oldHash"),outcome+": original key");
            assertEquals(outcome.equals("replacement"),calls(result,"newHash"),outcome+": replacement key");
            if(outcome.equals("self"))assertTrue(result.relations().stream()
                    .filter(hash -> hash.target().filter(t -> t.owner().equals("Fixture$Key") && t.name().equals("hashCode")).isPresent())
                    .anyMatch(hash -> result.relations().stream().anyMatch(resolve -> resolve.receiver().equals(hash.receiver())
                            && resolve.target().filter(t -> t.owner().equals("Fixture$Key") && t.name().equals("readResolve")).isPresent())));
            if(outcome.equals("unknown"))assertTrue(result.relations().stream().flatMap(r -> r.supports().stream())
                    .flatMap(s -> s.gaps().stream()).anyMatch(g -> g.detail().contains("readResolve replacement identity")));
        }
    }
}
