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

/** Source-built regressions; only the scanner and compiler run. */
class HotspotCycleTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String name,String descriptor) throws Exception {return scan(classes,name,descriptor,Optional.empty());}
    private ScanResult scan(Path classes,String name,String descriptor,Optional<StaticData> data) throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new MethodId("Fixture",name,descriptor)),data);
        }
    }
    private boolean calls(ScanResult result,String name) {return result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(m -> m.owner().equals("Fixture") && m.name().equals(name));}
    private Path compile(String source) throws Exception {return BytecodeFixtures.compile(temp,17,Map.of("Fixture.java",source));}
    private StaticData data(String name,String descriptor,String arguments) throws Exception {
        Path file=temp.resolve(name+".json");
        Files.writeString(file,"{\"source\":\"source-built values\",\"basis\":\"BINDING\",\"entry\":{\"owner\":\"Fixture\",\"name\":\""+name+"\",\"descriptor\":\""+descriptor+"\",\"arguments\":"+arguments+"},\"objects\":[]}");
        return StaticData.read(file);
    }
    @Test void runtimeSingletonAndKnownDecodeNullSelectOnlyTheCorrectSuccessors() throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void yes(){} static void no(){}
              public static void singleton(){if(Runtime.getRuntime()==Runtime.getRuntime())yes();else no();}
              public static void decode(){try{java.util.Base64.getDecoder().decode((String)null);no();}catch(NullPointerException expected){yes();}}
            }
            """);
        for(String name:List.of("singleton","decode")) {var result=scan(classes,name,"()V");assertTrue(calls(result,"yes"),name);assertFalse(calls(result,"no"),name);}
    }
    @Test void primitiveSnapshotsUseJvmBooleanFloatAndWideValues() throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void yes(){} static void no(){}
              public static void bool(boolean value){if(value)yes();else no();}
              public static void rounded(float value){if(value==16777216f)yes();else no();}
              public static void wide(long value){if(value==9007199254740993L)yes();else no();}
            }
            """);
        for(String[] row:List.of(new String[]{"bool","(Z)V","[true]"},new String[]{"rounded","(F)V","[16777217]"},new String[]{"wide","(J)V","[9007199254740993]"})) {
            var result=scan(classes,row[0],row[1],Optional.of(data(row[0],row[1],row[2])));assertTrue(calls(result,"yes"),row[0]);assertFalse(calls(result,"no"),row[0]);
        }
        InvalidInput invalid=assertThrows(InvalidInput.class,() -> scan(classes,"rounded","(F)V",Optional.of(data("rounded","(F)V","[1e100]"))));
        assertTrue(invalid.getMessage().contains("/entry/arguments/0"));
    }
    @Test void reflectiveIntegerArgumentsAreUnboxedWidenedAndNeverNarrowed() throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void yes(){} static void no(){}
              public static void accept(long value){if(value==7L)yes();else no();}
              public static void narrow(byte value){no();}
              public static void run()throws Exception {Fixture.class.getMethod("accept",long.class).invoke(null,Integer.valueOf(7));}
              public static void reject()throws Exception {try{Fixture.class.getMethod("narrow",byte.class).invoke(null,Integer.valueOf(7));no();}catch(IllegalArgumentException expected){yes();}}
            }
            """);
        for(String name:List.of("run","reject")) {var result=scan(classes,name,"()V");assertTrue(calls(result,"yes"),name+result.limitations());assertFalse(calls(result,"no"),name);}
    }
    @Test void equalKeysReplaceTheSameMappingAndUnequalKeysRetainIt() throws Exception {
        Path classes=compile("""
            public class Fixture {
              public static class Key {final int id;Key(int id){this.id=id;}public int hashCode(){return 1;}public boolean equals(Object other){return id==((Key)other).id;}}
              static void yes(){} static void no(){}
              public static void equal(){java.util.Map<Key,String> map=new java.util.HashMap<>();Key key=new Key(1);map.put(key,"old");map.put(new Key(1),"new");if("new".equals(map.get(key)))yes();else no();}
              public static void different(){java.util.Map<Key,String> map=new java.util.HashMap<>();Key key=new Key(1);map.put(key,"old");map.put(new Key(2),"new");if("old".equals(map.get(key)))yes();else no();}
              public static void sorted(){java.util.Map<String,String> map=new java.util.TreeMap<>((a,b)->0);map.put("one","old");map.put("two","new");if("new".equals(map.get("one")))yes();else no();}
            }
            """);
        for(String name:List.of("equal","different","sorted")) {var result=scan(classes,name,"()V");assertTrue(calls(result,"yes"),name+result.limitations());assertFalse(calls(result,"no"),name);}
    }
    @Test void knownEmptyAndExhaustedIteratorsThrowWithoutCreatingAnotherMember() throws Exception {
        Path classes=compile("""
            public class Fixture {
              static void yes(){} static void no(){}
              public static void empty(){java.util.Iterator<Object> iterator=java.util.Arrays.asList(new Object[0]).iterator();try{iterator.next();no();}catch(java.util.NoSuchElementException expected){yes();}}
              public static void exhausted(){java.util.Iterator<String> iterator=java.util.Arrays.asList("only").iterator();iterator.next();try{iterator.next();no();}catch(java.util.NoSuchElementException expected){yes();}}
            }
            """);
        for(String name:List.of("empty","exhausted")) {var result=scan(classes,name,"()V");assertTrue(calls(result,"yes"),name+result.limitations());assertFalse(calls(result,"no"),name);}
    }
    @Test void objectStringificationContributesItsReturnToTheBuilderContent() throws Exception {
        Path classes=compile("""
            public class Fixture {
              public static class Named {public String toString(){return "middle";}}
              static void yes(){} static void no(){}
              public static void run(){String value=new StringBuilder("pre-").append(new Named()).append("-post").toString();if("pre-middle-post".equals(value))yes();else no();}
            }
            """);
        var result=scan(classes,"run","()V");assertTrue(calls(result,"yes"),result.limitations().toString());assertFalse(calls(result,"no"));
    }
    @Test void java8And17StringNamesKeepTheSuffixAndDeriveOnlyTheRawUnknownInput() throws Exception {
        String source="""
            public class Fixture {
              public static class AlphaTail {public static void hit(){yes();}}
              public static class nullTail {public static void hit(){nil();}}
              static void yes(){} static void nil(){}
              public static void run(String part)throws Exception {Class.forName("Fixture$"+part+"Tail").getMethod("hit").invoke(null);}
            }
            """;
        for(int release:List.of(8,17)) {
            Path classes=BytecodeFixtures.compile(temp,release,Map.of("Fixture.java",source));
            var unknown=scan(classes,"run","(Ljava/lang/String;)V");assertTrue(calls(unknown,"yes"),"Java "+release+unknown.limitations());
            assertTrue(unknown.inputRequirements().stream().anyMatch(r -> r.source().filter(s -> s.parameterSlot()==0 && s.path().isEmpty()).isPresent() && r.needed().choices().equals(List.of(new Literal("Alpha")))),"derived input removes both the prefix and suffix");
            var missing=scan(classes,"run","(Ljava/lang/String;)V",Optional.of(data("run","(Ljava/lang/String;)V","[\"Missing\"]")));assertFalse(calls(missing,"yes"));
            var nil=scan(classes,"run","(Ljava/lang/String;)V",Optional.of(data("run","(Ljava/lang/String;)V","[null]")));assertTrue(calls(nil,"nil"));assertFalse(calls(nil,"yes"));
        }
    }
    @Test void unknownMutationMarksOnlyThePassedObjectAndLaterWritesRestorePrecision() throws Exception {
        Path classes=compile("""
            public class Fixture {
              public static class Box {public String value;public Box child;}
              public static native void mutate(Box box);
              static void use(String value){}
              public static void run(){Box changed=new Box(),other=new Box();changed.child=new Box();changed.value="before";changed.child.value="nested";other.value="unrelated";mutate(changed);use(changed.value);use(changed.child.value);use(other.value);changed.value="after";use(changed.value);}
            }
            """);
        var result=scan(classes,"run","()V");
        var uses=result.relations().stream().filter(r -> r.target().filter(m -> m.owner().equals("Fixture") && m.name().equals("use")).isPresent()).toList();
        assertTrue(uses.stream().anyMatch(r -> r.arguments().equals(List.of(new Literal("before"))) && r.supports().stream().allMatch(s -> s.gaps().stream().anyMatch(g -> g.kind()==GapKind.UNSUPPORTED))));
        assertTrue(uses.stream().anyMatch(r -> r.arguments().equals(List.of(new Literal("nested"))) && r.supports().stream().allMatch(s -> s.gaps().stream().anyMatch(g -> g.kind()==GapKind.UNSUPPORTED))));
        assertTrue(uses.stream().anyMatch(r -> r.arguments().equals(List.of(new Literal("unrelated")))));
        assertTrue(uses.stream().anyMatch(r -> r.arguments().equals(List.of(new Literal("after")))));
        assertTrue(result.relations().stream().anyMatch(r -> r.slot().filter(Mutation.class::isInstance).isPresent()));
    }
    @Test void lateReturnAndStrongOverwriteKeepTheReturnedObjectAndCurrentValue() throws Exception {
        Path classes=compile("""
            public class Fixture {
              public static class Box {String value;}
              static Box relay(Box box){return box;} static Box create(){return relay(new Box());}
              static void use(String value){}
              public static void run(){Box box=create();box.value="first";box.value="second";use(box.value);}
            }
            """);
        var result=scan(classes,"run","()V");
        var uses=result.relations().stream().filter(r -> r.target().filter(m -> m.name().equals("use")).isPresent()).toList();
        assertTrue(uses.stream().anyMatch(r -> r.arguments().equals(List.of(new Literal("second")))));
        assertFalse(uses.stream().anyMatch(r -> r.arguments().equals(List.of(new Literal("first")))));
        assertTrue(calls(result,"relay") && calls(result,"create"));
    }
    @Test void inheritedTransientDefaultsAndCustomHooksStayDistinct() throws Exception {
        int scenario=0;
        for(var hook:Map.of("",false,
                "private void readObject(String input){value=new Object();}",false,
                "public void readExternal(java.io.ObjectInput input){value=new Object();}",false,
                "private void readObject(java.io.ObjectInputStream input){value=new Object();}",true,
                "private native void readObject(java.io.ObjectInputStream input);",true).entrySet()) {
            Path classes=compile("""
                public class Fixture {
                  public static class Parent implements java.io.Serializable {protected transient Object value;HOOK}
                  public static class Child extends Parent {public int hashCode(){if(value!=null)seen();return 1;}}
                  static void seen(){}
                  public static Object read(java.io.ObjectInputStream in)throws Exception{return in.readObject();}
                }
                """.replace("HOOK",hook.getKey()));
            Path file=temp.resolve("hook-"+(scenario++)+".json");
            Files.writeString(file,"{\"source\":\"inherited transient field\",\"basis\":\"BINDING\",\"entry\":{\"owner\":\"Fixture\",\"name\":\"read\",\"descriptor\":\"(Ljava/io/ObjectInputStream;)Ljava/lang/Object;\",\"arguments\":[{\"ref\":\"stream\"}]},\"objects\":[{\"id\":\"stream\",\"type\":\"java/io/ObjectInputStream\",\"decoded\":{\"ref\":\"set\"}},{\"id\":\"set\",\"type\":\"java/util/HashSet\",\"elements\":[{\"ref\":\"child\"}]},{\"id\":\"child\",\"type\":\"Fixture$Child\"}]}");
            var result=scan(classes,"read","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;",Optional.of(StaticData.read(file)));
            assertEquals(hook.getValue(),calls(result,"seen"),hook.getKey()+result.limitations());
            if(!hook.getValue())assertFalse(calls(scan(classes,"read","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;"),"seen"),"a conditional child cannot invent a nonnull inherited transient source field");
        }
    }
    @Test void malformedEntryAndSinkDescriptorsFailAtTheOptionBoundary() throws Exception {
        for(String option:List.of("--entry","--sink"))for(String descriptor:List.of("(V)V","(I)","()Vextra","([V)V","(Ljava/lang/String)V","()")) {
            var output=new java.io.ByteArrayOutputStream();
            int exit=io.just.app.Main.run(new String[]{"--input",temp.resolve("missing").toString(),"--jdk-home",System.getProperty("java.home"),"--output",temp.resolve("output").toString(),option,"Fixture#run"+descriptor},new java.io.PrintStream(output),new java.io.PrintStream(output));
            assertEquals(2,exit);assertTrue(output.toString().contains(option+" needs exact"),output.toString());
        }
    }
    @Test void serializedArraysAndContainersKeepTheKnownPrefixBeyond64Members() throws Exception {
        Path classes=compile("""
            public class Fixture {
              public static class Key implements java.io.Serializable {private Object readResolve(){seen();return this;}public int hashCode(){return 1;}}
              static void seen(){}
              public static Object read(java.io.ObjectInputStream in)throws Exception{return in.readObject();}
            }
            """);
        String members=String.join(",",Collections.nCopies(65,"{\"ref\":\"item\"}"));
        for(String type:List.of("[Ljava/lang/Object;","java/util/HashSet")) {
            Path file=temp.resolve(type.startsWith("[")?"array.json":"set.json");
            Files.writeString(file,"{\"source\":\"65 source members\",\"basis\":\"BINDING\",\"entry\":{\"owner\":\"Fixture\",\"name\":\"read\",\"descriptor\":\"(Ljava/io/ObjectInputStream;)Ljava/lang/Object;\",\"arguments\":[{\"ref\":\"stream\"}]},\"objects\":[{\"id\":\"stream\",\"type\":\"java/io/ObjectInputStream\",\"decoded\":{\"ref\":\"root\"}},{\"id\":\"root\",\"type\":\""+type+"\",\"elements\":["+members+"]},{\"id\":\"item\",\"type\":\"Fixture$Key\"}]}");
            var result=scan(classes,"read","(Ljava/io/ObjectInputStream;)Ljava/lang/Object;",Optional.of(StaticData.read(file)));
            assertTrue(calls(result,"seen"),type+result.limitations());
            assertTrue(result.relations().stream().flatMap(r -> r.supports().stream()).flatMap(s -> s.gaps().stream()).anyMatch(g -> g.kind()==GapKind.BUDGET && g.detail().contains("[64,65)")),type);
        }
    }
}
