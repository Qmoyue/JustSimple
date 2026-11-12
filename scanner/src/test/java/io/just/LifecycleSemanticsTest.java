package io.just;

import io.just.analysis.*;
import io.just.input.*;
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

/** Source-built bytecode and finite input snapshots; the target is never loaded or called. */
class LifecycleSemanticsTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String name,String descriptor,Optional<StaticData> data)throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("Fixture",name,descriptor)),data);
        }
    }
    private ScanResult scan(Path classes,String name,String descriptor)throws Exception{return scan(classes,name,descriptor,Optional.empty());}
    private boolean calls(ScanResult result,String name){return result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("Fixture") && t.name().equals(name));}
    private Path compile(String source)throws Exception{return BytecodeFixtures.compile(temp,17,Map.of("Fixture.java",source));}
    private StaticData decoded(String objects)throws Exception {
        Path file=Files.createTempFile(temp,"decoded-",".json");
        Files.writeString(file,"{\"source\":\"source-built finite stream metadata\",\"basis\":\"BINDING\",\"entry\":{\"owner\":\"Fixture\",\"name\":\"read\",\"descriptor\":\"(Ljava/io/ObjectInputStream;)Ljava/lang/Object;\",\"arguments\":[{\"ref\":\"stream\"}]},\"objects\":[{\"id\":\"stream\",\"type\":\"java/io/ObjectInputStream\",\"decoded\":{\"ref\":\"root\"}},"+objects+"]}");
        return StaticData.read(file);
    }
    private ScanResult read(Path classes,String objects)throws Exception{return scan(classes,"read","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;",Optional.of(decoded(objects)));}

    @Test void entryViewsKeepTheirMapKeyAndObserveLaterValueReplacement()throws Exception {
        Path classes=compile("""
            import java.util.*;
            public class Fixture {
              static void good(){}static void wrong(){}
              public static void run(){
                Map<String,String> a=new HashMap<>(),b=new HashMap<>();a.put("key","old");b.put("key","other");
                Map.Entry<String,String> entry=a.entrySet().iterator().next();a.put("key","new");
                if("key".equals(entry.getKey()) && "new".equals(entry.getValue()))good();else wrong();
              }
              public static void ordered(){
                Map<String,String> a=new LinkedHashMap<>();a.put("a","one");a.put("b","two");
                Iterator<Map.Entry<String,String>> it=a.entrySet().iterator();
                if("a".equals(it.next().getKey()) && "two".equals(it.next().getValue()))good();else wrong();
              }
            }
            """);
        for(String entry:List.of("run","ordered")) {
            var result=scan(classes,entry,"()V");assertTrue(calls(result,"good"),entry+result.limitations());assertFalse(calls(result,"wrong"),entry+result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Fixture") && t.name().equals("wrong")).isPresent()).map(r -> r.site()+" "+r.supports()).toList());
        }
    }
    @Test void primitiveReadsRetainTypeStreamAndReadOccurrenceAndPossibleExceptions()throws Exception {
        Path classes=compile("""
            import java.io.*;
            public class Fixture {
              static void shortValue(short value){}static void text(String value){}static void eof(){}static void malformed(){}
              public static void run(ObjectInputStream first,ObjectInputStream second)throws IOException {
                try{shortValue(first.readShort());text(first.readUTF());text(second.readUTF());}
                catch(EOFException expected){eof();}catch(UTFDataFormatException expected){malformed();}
              }
            }
            """);
        var result=scan(classes,"run","(Ljava/io/ObjectInputStream;Ljava/io/ObjectInputStream;)V");
        assertTrue(calls(result,"shortValue"));assertTrue(calls(result,"text"));assertTrue(calls(result,"eof"));assertTrue(calls(result,"malformed"));
        var values=result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Fixture") && Set.of("shortValue","text").contains(t.name())).isPresent()).flatMap(r -> r.arguments().stream()).toList();
        assertTrue(values.stream().anyMatch(a -> a instanceof ExternalValue value && value.descriptor().equals("S")));
        var sources=values.stream().flatMap(a -> Values.source(a).stream()).toList();
        assertTrue(sources.stream().anyMatch(s -> s.parameterSlot()==0));assertTrue(sources.stream().anyMatch(s -> s.parameterSlot()==1));
        assertTrue(sources.stream().allMatch(s -> s.path().stream().anyMatch(StreamRead.class::isInstance)));
    }
    @Test void getFieldUsesItsDeclaringSnapshotAndOnlyKnownAbsenceSelectsTheDefault()throws Exception {
        Path classes=compile("""
            import java.io.*;
            public class Fixture {
              static void good(){}static void wrong(){}
              public static class Root implements Serializable {
                String value,missing;
                private void readObject(ObjectInputStream in)throws Exception {
                  ObjectInputStream.GetField fields=in.readFields();
                  if(value!=null)wrong();
                  if(!fields.defaulted("value") && fields.defaulted("missing") && "bound".equals(fields.get("value","fallback")) && "fallback".equals(fields.get("missing","fallback")))good();else wrong();
                }
              }
              public static Object read(ObjectInputStream in)throws Exception{return in.readObject();}
            }
            """);
        var result=read(classes,"""
            {"id":"root","type":"Fixture$Root","fields":[{"owner":"Fixture$Root","name":"value","descriptor":"Ljava/lang/String;","value":"bound"}],"absentFields":[{"owner":"Fixture$Root","name":"missing","descriptor":"Ljava/lang/String;"}]}
            """);
        assertTrue(calls(result,"good"),result.limitations().toString());assertFalse(calls(result,"wrong"));
        Set<Integer> used=new HashSet<>();ArrayDeque<Integer> pending=new ArrayDeque<>();result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Fixture") && t.name().equals("good")).isPresent()).forEach(r -> pending.add(r.id()));
        while(!pending.isEmpty()){int id=pending.removeFirst();if(used.add(id))result.relations().get(id).supports().forEach(s -> pending.addAll(s.dependencies()));}
        assertTrue(used.stream().map(result.relations()::get).anyMatch(r -> r.kind()==Kind.INPUT_BINDING && r.site().source().contains("/absentFields/0")),"the selected default must retain its absence metadata evidence");
        assertTrue(result.relations().stream().noneMatch(r -> r.supports().stream().flatMap(s -> s.gaps().stream()).anyMatch(g -> g.detail().contains("readFields/GetField is not modeled"))));
    }
    @Test void noDataRequiresAnAbsentSerializableSuperclassSlotAndKeepsExceptionalOrdering()throws Exception {
        for(boolean throwing:List.of(false,true)) {
            Path classes=compile("""
                import java.io.*;
                public class Fixture {
                  static void absent(){}static void child(){}
                  public static abstract class Parent implements Serializable {private void readObjectNoData()throws ObjectStreamException{absent();THROW}}
                  public static class Root extends Parent {private void readObject(ObjectInputStream in){child();}}
                  public static Object read(ObjectInputStream in)throws Exception{return in.readObject();}
                }
                """.replace("THROW",throwing?"throw new InvalidObjectException(\"bad\");":""));
            for(boolean present:List.of(false,true)) {
                var result=read(classes,"{\"id\":\"root\",\"type\":\"Fixture$Root\",\"classData\":[{\"owner\":\"Fixture$Parent\",\"present\":"+present+"}]}");
                assertEquals(!present,calls(result,"absent"),"present="+present+result.limitations());
                assertEquals(present || !throwing,calls(result,"child"),"present="+present+", throwing="+throwing+result.limitations());
            }
            var unknown=read(classes,"{\"id\":\"root\",\"type\":\"Fixture$Root\"}");
            assertTrue(calls(unknown,"absent"));
            assertTrue(unknown.inputRequirements().stream().anyMatch(r -> r.needed().slot().filter(ClassData.class::isInstance).isPresent()));
        }
    }
    @Test void threadStartUsesOnlyItsBoundRunnableAndRetainsAsynchronousConditions()throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void good(){}static void wrong(){}static void repeated(){}
              public static class Task implements Runnable {String value;Task(String value){this.value=value;}public void run(){if("bound".equals(value))good();else wrong();}}
              public static void run(){new Thread(new Task("other"));Thread thread=new Thread(new Task("bound"));thread.start();try{thread.start();wrong();}catch(IllegalThreadStateException expected){repeated();}}
              public static void captured(){String value="bound";new Thread(()->{if("bound".equals(value))good();else wrong();}).start();}
              public static void before(){Task task=new Task("old");task.value="bound";new Thread(task).start();}
              public static void after(){Task task=new Task("bound");new Thread(task).start();task.value="later";}
              public static class Own extends Thread {public void run(){good();}}
              public static void overridden(){new Own().start();}
            }
            """);
        for(String entry:List.of("run","captured","overridden","before")) {
            var result=scan(classes,entry,"()V");assertTrue(calls(result,"good"),entry+result.limitations());assertFalse(calls(result,"wrong"),entry+result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Fixture") && t.name().equals("wrong")).isPresent()).map(r -> r.site()+" "+r.supports()).toList());
            assertTrue(result.relations().stream().flatMap(r -> r.supports().stream()).flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.DEPLOYMENT && g.detail().contains("asynchronous")));
            if(entry.equals("run"))assertTrue(calls(result,"repeated"));
        }
        var uncertain=scan(classes,"after","()V");assertTrue(calls(uncertain,"good"));assertTrue(calls(uncertain,"wrong"),"a later caller write has no fixed order relative to the asynchronous callback");
    }
    @Test void unknownProxyInterfacesKeepTheActualHandlerWithoutBorrowingAnotherObject()throws Exception {
        Path classes=compile("""
            import java.lang.reflect.*;
            public class Fixture {
              public interface Face {void call();}
              static void good(){}static void wrong(){}
              public static class Handler implements InvocationHandler {String value;Handler(String value){this.value=value;}public Object invoke(Object proxy,Method method,Object[] args){if("bound".equals(value))good();else wrong();return null;}}
              public static void run(Class<?>[] interfaces){new Handler("other");Handler handler=new Handler("bound");Face proxy=(Face)Proxy.newProxyInstance(Fixture.class.getClassLoader(),interfaces,handler);if(Proxy.getInvocationHandler(proxy)==handler)proxy.call();else wrong();}
            }
            """);
        var result=scan(classes,"run","([Ljava/lang/Class;)V");assertTrue(calls(result,"good"),result.limitations().toString());assertFalse(calls(result,"wrong"));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.ARGUMENTS));
    }
    @Test void impactArgumentsKeepConstantsOverridesAndLambdaCapturesWithoutATaintGate()throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void caught(){}static void wrong(){}
              public static void empty()throws Exception{try{Runtime.getRuntime().exec("");wrong();}catch(IllegalArgumentException expected){caught();}}
              public static void reflected()throws Exception{try{Runtime.class.getMethod("exec",String.class).invoke(Runtime.getRuntime(),"");wrong();}catch(java.lang.reflect.InvocationTargetException expected){if(expected.getCause() instanceof IllegalArgumentException)caught();}}
              public static void fixed()throws Exception{Runtime.getRuntime().exec("fixed-program");}
              public static class Holder {String command;}
              public static void overwritten(String input)throws Exception{Holder h=new Holder();h.command=input;h.command="";try{Runtime.getRuntime().exec(h.command);wrong();}catch(IllegalArgumentException expected){caught();}}
              public static void captured(String input)throws Exception{java.util.concurrent.Callable<String> fn=()->input;Runtime.getRuntime().exec(fn.call());}
              public static void arrays(boolean branch)throws Exception{Runtime.getRuntime().exec(branch?new String[0]:new String[]{"program"});}
            }
            """);
        for(String entry:List.of("empty","reflected","overwritten")) {
            var result=scan(classes,entry,entry.equals("overwritten")?"(Ljava/lang/String;)V":"()V");
            assertTrue(calls(result,"caught"),entry+result.limitations());assertFalse(calls(result,"wrong"),entry);
            assertTrue(result.relations().stream().noneMatch(r -> r.kind()==Kind.IMPACT && r.target().filter(t -> t.owner().equals("java/lang/Runtime") && t.name().equals("exec")).isPresent()),entry);
            assertTrue(result.relations().stream().anyMatch(r -> r.target().filter(t -> t.owner().equals("java/lang/Runtime") && t.name().equals("exec")).isPresent()),"the rejected call boundary remains reviewable");
        }
        var fixed=scan(classes,"fixed","()V");assertTrue(fixed.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.arguments().equals(List.of(new Literal("fixed-program")))));
        var captured=scan(classes,"captured","(Ljava/lang/String;)V");assertTrue(captured.relations().stream().filter(r -> r.kind()==Kind.IMPACT).flatMap(r -> r.arguments().stream()).anyMatch(a -> Values.source(a).filter(s -> s.parameterSlot()==0).isPresent()));
        assertTrue(scan(classes,"arrays","(Z)V").relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT));
    }
    @Test void resourceBytesDefineTwoSeparateLoaderResultsAndContinueIntoReflection()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Fixture.java","""
            import java.io.*;
            public class Fixture {
              public static class Loader extends ClassLoader {public Class<?> make(byte[] code){return defineClass(null,code,0,code.length);}}
              public static void run()throws Exception {byte[] code=Fixture.class.getResourceAsStream("/Stage.class").readAllBytes();new Loader().make(code).getMethod("hit").invoke(null);new Loader().make(code).getMethod("hit").invoke(null);}
            }
            ""","Stage.java","public class Stage {public static void hit(){}}"));
        var result=scan(classes,"run","()V");
        Set<Integer> loaders=new HashSet<>();result.relations().stream().filter(r -> r.kind()==Kind.REFLECTION).flatMap(r -> r.target().stream()).filter(t -> t.owner().equals("Stage") && t.name().equals("hit")).forEach(t -> loaders.add(t.loader()));
        assertEquals(2,loaders.size(),result.limitations().toString());assertFalse(loaders.contains(0));
    }
    @Test void nestedNativeReadsDoNotReuseTheOuterDecodedTypeSelection()throws Exception {
        Path classes=compile("""
            import java.io.*;
            public class Fixture {
              static void good(String value){}static void wrong(){}
              public static class Leaf implements Serializable {public void accept(String value){good(value);}}
              public static class Root implements Externalizable {
                public Root(){}public void writeExternal(ObjectOutput out){}
                public void readExternal(ObjectInput in)throws IOException,ClassNotFoundException {Leaf leaf=(Leaf)in.readObject();leaf.accept(in.readUTF());}
              }
              public static Object read(ObjectInputStream in)throws Exception{return in.readObject();}
            }
            """);
        var result=scan(classes,"read","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;");
        assertTrue(calls(result,"good"),result.limitations().toString());
        assertTrue(result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Fixture") && t.name().equals("good")).isPresent()).flatMap(r -> r.arguments().stream()).anyMatch(a -> Values.source(a).filter(s -> s.path().stream().anyMatch(StreamRead.class::isInstance)).isPresent()));
    }
    @Test void anUnboundNoDataHookMayInitializeInheritedTransientState()throws Exception {
        for(boolean hook:List.of(false,true)) {
            Path classes=compile("""
                import java.io.*;
                public class Fixture {
                  static void good(){}
                  public static abstract class Parent implements Serializable {protected transient Object value;HOOK}
                  public static class Child extends Parent {public int hashCode(){if(value!=null)good();return 1;}}
                  public static Object read(ObjectInputStream in)throws Exception{return in.readObject();}
                }
                """.replace("HOOK",hook?"private void readObjectNoData(){value=new Object();}":""));
            var result=scan(classes,"read","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;");
            assertEquals(hook,calls(result,"good"),"an unresolved superclass data slot cannot prove a transient field is always null");
        }
    }
    @Test void aTargetWithTheProxyApiSignatureKeepsItsActualBody()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("java/lang/reflect/Proxy.java","package java.lang.reflect;public class Proxy {public static Object newProxyInstance(ClassLoader loader,Class<?>[] faces,InvocationHandler handler){return null;}}","Fixture.java","""
            import java.lang.reflect.*;
            public class Fixture {
              interface Face {void call();}static void good(){}static void wrong(){}
              public static class Handler implements InvocationHandler {public Object invoke(Object proxy,Method method,Object[] args){wrong();return null;}}
              public static void run(){try{((Face)Proxy.newProxyInstance(Fixture.class.getClassLoader(),new Class[]{Face.class},new Handler())).call();wrong();}catch(NullPointerException expected){good();}}
            }
            """));
        var result=scan(classes,"run","()V");assertTrue(calls(result,"good"));assertFalse(calls(result,"wrong"));
    }
}
