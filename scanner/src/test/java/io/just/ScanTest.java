package io.just;

import io.just.knowledge.EntryPoints;

import io.just.analysis.Analyzer;
import io.just.analysis.ScanResult;
import io.just.analysis.ScanResult.*;
import io.just.app.Main;
import io.just.input.Inputs;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import io.just.report.Reports;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import java.util.jar.*;
import java.util.stream.Collectors;
import static org.junit.jupiter.api.Assertions.*;

/** All targets are compiled and read, never loaded or invoked. No external benchmark is needed. */
class ScanTest {
    @TempDir Path temp;
    private final Path jdk = Path.of(System.getProperty("java.home"));

    private Path compile(String name, String source) throws IOException {
        return compile(Map.of(name + ".java", source));
    }
    private Path compile(Map<String, String> sources) throws IOException {
        return BytecodeFixtures.compile(temp,8,sources);
    }

    private ScanResult scan(Path input) throws IOException { return scan(input, Analyzer.Limits.defaults(), true); }
    private ScanResult scan(Path input, Analyzer.Limits budget, boolean guidance) throws IOException {
        try (Inputs inputs = Inputs.open(input, List.of(), jdk, Inputs.Limits.defaults())) {
            Program program = new Program(inputs, 20_000);
            return new Analyzer(program, new Mechanisms(program), budget).scan(EntryPoints.Mode.COMPONENT, guidance);
        }
    }
    private ScanResult scanBound(Path classes,String json,Program.MethodId entry) throws IOException {
        Path facts=Files.createTempFile(temp,"bindings-",".json"); Files.writeString(facts,json);
        try (Inputs inputs=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);
            return new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,true,Set.of(entry),Optional.of(io.just.input.StaticData.read(facts)));
        }
    }
    private Set<String> targets(ScanResult result, String entry, Kind kind) {
        Set<Integer> path = result.findings().stream().filter(f -> f.entry().method().id().name().equals(entry))
                .flatMap(f -> f.path().stream()).collect(Collectors.toSet());
        return result.relations().stream().filter(r -> path.contains(r.id()) && r.kind() == kind && r.target().isPresent())
                .map(r -> r.target().orElseThrow().toString()).collect(Collectors.toSet());
    }
    private List<Finding> findings(ScanResult result, String entry) {
        return result.findings().stream().filter(f -> f.entry().method().id().name().equals(entry)).toList();
    }

    @Test void exactReflectionUsesRealLookupWithoutDirectTargetInstruction() throws IOException {
        Path classes = compile("Exact", """
                public class Exact {
                  static { if (Boolean.parseBoolean("true")) throw new AssertionError("must never initialize target"); }
                  public static void run() throws Exception {
                    Target.class.getMethod("ping", new Class[0]).invoke(new Target(), new Object[0]);
                  }
                  public static class Target { public void ping() {} }
                }
                """);
        ScanResult result = scan(classes);
        assertEquals(Execution.FINISHED, result.execution(), result.limitations().toString());
        assertTrue(targets(result, "run", Kind.REFLECTION).stream().anyMatch(t -> t.contains("Exact$Target#ping()V")));

        assertTrue(result.relations().stream().filter(r -> r.kind() == Kind.REFLECTION && r.target().map(t -> t.owner().equals("Exact$Target")).orElse(false))
                .flatMap(r -> r.supports().stream()).allMatch(support -> !support.witnesses().isEmpty()));
    }

    @Test void contextsReturnsAndReceiverFieldsDoNotMixObjects() throws IOException {
        Path classes = compile("Context", """
                public class Context {
                  static class A { public void alpha() {} public void beta() {} }
                  static class B { public void alpha() {} public void beta() {} }
                  static class Box { Object target; String name; Box(Object t,String n) { target=t; name=n; } }
                  static Box make(Object t,String n) { return new Box(t,n); }
                  static void dispatch(Box b) throws Exception {
                    b.target.getClass().getMethod(b.name,new Class[0]).invoke(b.target,new Object[0]);
                  }
                  public static void run() throws Exception {
                    Box a=make(new A(),"alpha"); Box b=make(new B(),"beta"); dispatch(a); dispatch(b);
                  }
                }
                """);
        ScanResult result = scan(classes);
        Set<String> reflected = targets(result, "run", Kind.REFLECTION);
        assertTrue(reflected.stream().anyMatch(t -> t.contains("Context$A#alpha")), result.limitations().toString());
        assertTrue(reflected.stream().anyMatch(t -> t.contains("Context$B#beta")));
        assertFalse(reflected.stream().anyMatch(t -> t.contains("Context$A#beta") || t.contains("Context$B#alpha")));
        assertFalse(result.relations().stream().filter(r -> r.kind() == Kind.FIELD_FLOW).toList().isEmpty());
    }

    @Test void reflectiveApiResultsFeedLaterReflectiveCallsWithoutExecutingTargets() throws IOException {
        Path classes = compile("ReflectiveSteps", """
                public class ReflectiveSteps {
                  public static class Hub {
                    public static Hub acquire() { return new Hub(); }
                    public void finish() {}
                  }
                  static Object step(Object input,String name,Class[] types,Object[] args) throws Exception {
                    return input.getClass().getMethod(name,types).invoke(input,args);
                  }
                  public static void run() throws Exception {
                    Object value=step(Class.class,"forName",new Class[]{String.class},new Object[]{"ReflectiveSteps$Hub"});
                    value=step(value,"getMethod",new Class[]{String.class,Class[].class},new Object[]{"acquire",null});
                    value=step(value,"invoke",new Class[]{Object.class,Object[].class},new Object[]{null,null});
                    step(value,"finish",new Class[0],new Object[0]);
                  }
                }
                """);
        ScanResult result = scan(classes);
        Set<String> reflected = targets(result, "run", Kind.REFLECTION);
        assertTrue(reflected.stream().anyMatch(t -> t.contains("java.lang.Class#forName")), result.limitations().toString());
        assertTrue(reflected.stream().anyMatch(t -> t.contains("ReflectiveSteps$Hub#acquire")));
        assertTrue(reflected.stream().anyMatch(t -> t.contains("ReflectiveSteps$Hub#finish")));
        assertTrue(findings(result, "run").stream().anyMatch(f -> f.detail().contains("Hub#finish")));
    }

    @Test void conditionalSignatureCannotLoseItsRequiredBranch() throws IOException {
        Path classes = compile("ConditionalSignature", """
                public class ConditionalSignature {
                  public static class Target { public void accept(String value) {} }
                  public static void run(boolean flag) throws Exception {
                    Class[] types=new Class[1];
                    if(flag) types[0]=String.class;
                    Target.class.getMethod("accept",types).invoke(new Target(),new Object[]{"value"});
                  }
                }
                """);
        ScanResult result = scan(classes);
        assertTrue(targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#accept")));

        assertTrue(findings(result,"run").stream().anyMatch(f -> f.gaps().stream().anyMatch(g -> g.kind()==GapKind.CONTROL_CONDITION)));
    }

    @Test void suppliedBranchConditionsRetainTheirSourceEvenWhenTheTargetArgumentsAreConstants() throws IOException {
        Path classes=compile("ConditionSource", """
                public class ConditionSource {
                  public static class Target {public void yes(){}public void no(){}}
                  public static void run(int flag)throws Exception {
                    if(flag==1)Target.class.getMethod("yes",new Class[0]).invoke(new Target(),new Object[0]);
                    else Target.class.getMethod("no",new Class[0]).invoke(new Target(),new Object[0]);
                  }
                  public static void length(Object[] input)throws Exception {
                    try {int ignored=input.length;Target.class.getMethod("yes",new Class[0]).invoke(new Target(),new Object[0]);}
                    catch(NullPointerException absent) {}
                  }
                }
                """);
        String facts="""
                {"source":"branch input snapshot","basis":"BINDING","entry":{"owner":"ConditionSource","name":"run","descriptor":"(I)V","arguments":[1]},"objects":[]}
                """;
        Program.MethodId entry=new Program.MethodId("ConditionSource","run","(I)V");
        for (String basis:List.of("BINDING","ASSUMPTION")) {
            ScanResult result=scanBound(classes,facts.replace("BINDING",basis),entry);
            Finding finding=findings(result,"run").stream().filter(f -> f.detail().contains("Target#yes")).findFirst().orElseThrow();
            assertFalse(targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#no")));
            assertTrue(finding.supportingRelations().stream().map(result.relations()::get).anyMatch(r -> r.kind()==Kind.INPUT_BINDING && r.site().source().endsWith("#/entry/arguments/0")));
        }
        String arrayFacts="""
                {"source":"nonnull array assumption","basis":"ASSUMPTION","entry":{"owner":"ConditionSource","name":"length","descriptor":"([Ljava/lang/Object;)V","arguments":[{"ref":"array"}]},"objects":[{"id":"array","type":"[Ljava/lang/Object;","elements":[]}]}
                """;
        ScanResult length=scanBound(classes,arrayFacts,new Program.MethodId("ConditionSource","length","([Ljava/lang/Object;)V"));
        Finding afterLength=findings(length,"length").stream().filter(f -> f.detail().contains("Target#yes")).findFirst().orElseThrow();
        assertTrue(afterLength.gaps().stream().anyMatch(g -> g.kind()==GapKind.INPUT_BINDING));
    }

    @Test void necessaryFieldEvidenceFollowsReturnsAndExcludesUnrelatedReads() throws IOException {
        Path classes=compile("Necessary", """
                public class Necessary {
                  public static class Target { public void ping() {} }
                  static class Box { Object target; Object noise; }
                  static Object pick(Box box) { return box.target; }
                  public static void run() throws Exception {
                    Box box=new Box(); box.target=new Target(); box.noise=new Object();
                    Object ignored=box.noise;
                    Object value=pick(box);
                    value.getClass().getMethod("ping",new Class[0]).invoke(value,new Object[0]);
                  }
                }
                """);
        ScanResult result=scan(classes);
        Finding found=findings(result,"run").stream().filter(f -> f.detail().contains("Target#ping")).findFirst().orElseThrow();
        List<Relation> evidence=found.supportingRelations().stream().map(result.relations()::get).toList();
        assertTrue(evidence.stream().anyMatch(r -> r.slot().filter(slot -> slot instanceof Field field && field.field().name().equals("target")).isPresent()));
        assertFalse(evidence.stream().anyMatch(r -> r.slot().filter(slot -> slot instanceof Field field && field.field().name().equals("noise")).isPresent()));
    }

    @Test void suppliedStaticFactsBindObjectsAndKeepAssumptionsAndReferencesDistinct() throws IOException {
        Path classes=compile("Snapshot", """
                public class Snapshot {
                  public static class Good { public void ping() {} }
                  public static class Other { public void wrong() {} }
                  public static class Box { Object target; String name; byte tiny; }
                  public static abstract class AbstractValue {}
                  public static void run(Box box) throws Exception {
                    box.target.getClass().getMethod(box.name,new Class[0]).invoke(box.target,new Object[0]);
                  }
                }
                """);
        String document="""
                {"source":"independent finite fixture snapshot","basis":"BINDING",
                 "entry":{"owner":"Snapshot","name":"run","descriptor":"(LSnapshot$Box;)V","arguments":[{"ref":"box"}]},
                 "objects":[
                  {"id":"box","type":"Snapshot$Box","fields":[
                    {"owner":"Snapshot$Box","name":"target","descriptor":"Ljava/lang/Object;","value":{"ref":"good"}},
                    {"owner":"Snapshot$Box","name":"name","descriptor":"Ljava/lang/String;","value":"ping"}]},
                  {"id":"good","type":"Snapshot$Good"}, {"id":"other","type":"Snapshot$Other"},
                  {"id":"spare","type":"Snapshot$Box","fields":[
                    {"owner":"Snapshot$Box","name":"target","descriptor":"Ljava/lang/Object;","value":{"ref":"other"}},
                    {"owner":"Snapshot$Box","name":"name","descriptor":"Ljava/lang/String;","value":"wrong"}]}]}
                """;
        Path facts=temp.resolve("facts.json");
        for (String basis:List.of("BINDING","ASSUMPTION","REFERENCE")) {
            Files.writeString(facts,document.replace("BINDING",basis));
            try (Inputs input=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
                Program program=new Program(input,20000);
                ScanResult result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                        .scan(EntryPoints.Mode.COMPONENT,true,Set.of(new Program.MethodId("Snapshot","run","(LSnapshot$Box;)V")),Optional.of(io.just.input.StaticData.read(facts)));
                Set<String> bound=targets(result,"run",Kind.REFLECTION);
                if(!basis.equals("REFERENCE")) {
                    assertFalse(bound.stream().anyMatch(t -> t.contains("Other#wrong")));
                    assertTrue(bound.stream().anyMatch(t -> t.contains("Good#ping")));
                } else {
                    assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.REFLECTION && r.target().map(t -> t.owner().startsWith("Snapshot$")).orElse(false)).allMatch(r -> !r.conditions().selections().isEmpty() || r.supports().stream().allMatch(s -> !s.gaps().isEmpty())));
                    assertFalse(result.inputRequirements().isEmpty(),"reference values must still require an actual input binding");
                }
                assertEquals(basis,result.staticData().orElseThrow().basis().name());
            }
        }
        Files.writeString(facts,document.replace("\"ref\":\"good\"","\"ref\":\"missing\""));
        IOException dangling=assertThrows(IOException.class,() -> io.just.input.StaticData.read(facts));
        assertTrue(dangling.getMessage().contains("unresolved object reference"));
        Files.writeString(facts,document.replace("\"name\":\"target\"","\"name\":\"absentField\""));
        ByteArrayOutputStream errors=new ByteArrayOutputStream();
        int code=Main.run(new String[]{"--input",classes.toString(),"--jdk-home",jdk.toString(),"--mode","component","--entry","Snapshot#run(LSnapshot$Box;)V",
                "--facts",facts.toString(),"--output",temp.resolve("invalid-facts").toString()},System.out,new PrintStream(errors,true,StandardCharsets.UTF_8));
        assertEquals(2,code); assertTrue(errors.toString(StandardCharsets.UTF_8).contains("missing field"));
        assertFalse(Files.exists(temp.resolve("invalid-facts")));
        Map<String,String> invalid=Map.of(
                "object runtime type must be concrete",document.replace("\"objects\":[","\"objects\":[{\"id\":\"abstract\",\"type\":\"Snapshot$AbstractValue\"},"),
                "incompatible binding",document.replace("\"name\":\"name\",\"descriptor\":\"Ljava/lang/String;\",\"value\":\"ping\"","\"name\":\"tiny\",\"descriptor\":\"B\",\"value\":300"));
        for (var bad:invalid.entrySet()) {
            Files.writeString(facts,bad.getValue());errors.reset();
            assertEquals(2,Main.run(new String[]{"--input",classes.toString(),"--jdk-home",jdk.toString(),"--mode","component","--entry","Snapshot#run(LSnapshot$Box;)V",
                    "--facts",facts.toString(),"--output",temp.resolve("invalid-facts-extra").toString()},System.out,new PrintStream(errors,true,StandardCharsets.UTF_8)));
            assertTrue(errors.toString(StandardCharsets.UTF_8).contains(bad.getKey()),errors.toString(StandardCharsets.UTF_8));
        }
    }

    @Test void finiteIterationFeedsEachReflectiveReturnToTheNextElement() throws IOException {
        String source="""
                import java.util.*;
                public class Ordered {
                  public static class Hub { public static Hub acquire() { return new Hub(); } public void finish() {} }
                  public static class Stage {
                    Object seed; String name; Class[] types; Object[] args;
                    Stage(Object s,String n,Class[] t,Object[] a) {seed=s;name=n;types=t;args=a;}
                    Object step(Object input) throws Exception { return input.getClass().getMethod(name,types).invoke(input,args); }
                  }
                  public static Object run() throws Exception {
                    Stage first=new Stage(Class.class,"forName",new Class[]{String.class},new Object[]{"Ordered$Hub"});
                    Stage second=new Stage(null,"getMethod",new Class[]{String.class,Class[].class},new Object[]{"acquire",null});
                    Stage third=new Stage(null,"invoke",new Class[]{Object.class,Object[].class},new Object[]{null,null});
                    Stage fourth=new Stage(null,"finish",new Class[0],new Object[0]);
                    Collection<Stage> stages=Arrays.asList(first,second,third,fourth);
                    Object value=null;
                    for(Stage stage:stages) { if(value==null) value=stage.seed; value=stage.step(value); }
                    return value;
                  }
                }
                """;
        ScanResult result=scan(compile("Ordered",source));
        assertTrue(targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Hub#finish")),result.limitations().toString());
        assertTrue(findings(result,"run").stream().anyMatch(f -> f.detail().contains("Hub#finish")));
        ScanResult swapped=scan(compile("Ordered",source.replace("Arrays.asList(first,second,third,fourth)","Arrays.asList(second,first,third,fourth)")));
        assertFalse(targets(swapped,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Hub#finish")));
    }

    @Test void laterCertainFieldWriteReplacesEarlierValueWithoutMixingObjects() throws IOException {
        Path classes=compile("Overwrite", """
                public class Overwrite {
                  public static class Target { public void old() {} public void current() {} }
                  static class Box { String name; }
                  public static void run() throws Exception {
                    Box box=new Box(); box.name="old"; box.name="current";
                    Target target=new Target();
                    target.getClass().getMethod(box.name,new Class[0]).invoke(target,new Object[0]);
                  }
                }
                """);
        ScanResult result=scan(classes);
        assertTrue(targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#current")));
        assertFalse(targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#old")));

    }

    @Test void suppliedLinkedMapOrderCannotBeReplacedWithKeysOrAnUnorderedSummary() throws IOException {
        Path classes=compile("MapOrder", """
                import java.util.*;
                public class MapOrder {
                  public static class Head { public Tail next() { return new Tail(); } }
                  public static class Tail { public void finish() {} }
                  public static class Stage { Object seed; String name; }
                  public static class Service {
                    Map<String,Stage> stages;
                    public Object fold() throws Exception {
                      stages.put("first",stages.get("first"));
                      Object value=null;
                      for(Stage stage:stages.values()) {
                        if(value==null) value=stage.seed;
                        value=value.getClass().getMethod(stage.name,new Class[0]).invoke(value,new Object[0]);
                      }
                      return value;
                    }
                  }
                }
                """);
        String json="""
                {"source":"finite map snapshot","basis":"BINDING",
                 "entry":{"owner":"MapOrder$Service","name":"fold","descriptor":"()Ljava/lang/Object;","receiver":{"ref":"service"},"arguments":[]},
                 "objects":[
                  {"id":"service","type":"MapOrder$Service","fields":[{"owner":"MapOrder$Service","name":"stages","descriptor":"Ljava/util/Map;","value":{"ref":"map"}}]},
                  {"id":"map","type":"java/util/LinkedHashMap","fields":[{"owner":"java/util/LinkedHashMap","name":"accessOrder","descriptor":"Z","value":false}],"entries":[{"key":"first","value":{"ref":"first"}},{"key":"second","value":{"ref":"second"}}]},
                  {"id":"head","type":"MapOrder$Head"},
                  {"id":"first","type":"MapOrder$Stage","fields":[{"owner":"MapOrder$Stage","name":"seed","descriptor":"Ljava/lang/Object;","value":{"ref":"head"}},{"owner":"MapOrder$Stage","name":"name","descriptor":"Ljava/lang/String;","value":"next"}]},
                  {"id":"second","type":"MapOrder$Stage","fields":[{"owner":"MapOrder$Stage","name":"seed","descriptor":"Ljava/lang/Object;","value":null},{"owner":"MapOrder$Stage","name":"name","descriptor":"Ljava/lang/String;","value":"finish"}]}]}
                """;
        Program.MethodId entry=new Program.MethodId("MapOrder$Service","fold","()Ljava/lang/Object;");
        ScanResult result=scanBound(classes,json,entry);
        assertTrue(findings(result,"fold").stream().anyMatch(f -> f.detail().contains("Tail#finish")),result.limitations().toString());
        assertEquals(2,findings(result,"fold").stream().filter(f -> f.boundary()==Kind.REFLECTION).count(),"overwriting an existing snapshot key must preserve size and position");
        ScanResult reversed=scanBound(classes,json.replace("\"ref\":\"first\"","\"ref\":\"temporary\"").replace("\"ref\":\"second\"","\"ref\":\"first\"").replace("\"ref\":\"temporary\"","\"ref\":\"second\""),entry);
        assertFalse(targets(reversed,"fold",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Tail#finish")));
        ScanResult accessOrder=scanBound(classes,json.replace("\"value\":false","\"value\":true"),entry);
        String hash=json.replace("\"fields\":[{\"owner\":\"java/util/LinkedHashMap\",\"name\":\"accessOrder\",\"descriptor\":\"Z\",\"value\":false}],","").replace("java/util/LinkedHashMap","java/util/HashMap");
        ScanResult unordered=scanBound(classes,hash,entry);
        for(ScanResult conditional:List.of(accessOrder,unordered)) {
            assertTrue(!conditional.breakpoints().isEmpty(),"unresolved iteration keeps a located frontier");
            assertTrue(findings(conditional,"fold").stream().filter(f -> f.detail().contains("Tail#finish")).allMatch(f -> f.gaps().stream().anyMatch(g -> g.detail().contains("order"))),"unstable iteration cannot supply an unconditional ordered return chain");
        }
    }

    @Test void unorderedElementsCannotExchangeTheirReflectionFields() throws IOException {
        Path classes=compile("Tuple", """
                import java.util.*;
                public class Tuple {
                  public static class Target {public void first(String value){}public void second(Integer value){}public void first(Integer trap){}public void second(String trap){}}
                  public static class Item {Object target;String name;Class[] types;Object[] args;}
                  public static void run(Set<Item> items)throws Exception {
                    for(Item item:items) item.target.getClass().getMethod(item.name,item.types).invoke(item.target,item.args);
                  }
                }
                """);
        String json="""
                {"source":"independent unordered members","basis":"BINDING",
                 "entry":{"owner":"Tuple","name":"run","descriptor":"(Ljava/util/Set;)V","arguments":[{"ref":"items"}]},
                 "objects":[{"id":"items","type":"java/util/HashSet","elements":[{"ref":"a"},{"ref":"b"}]},
                  {"id":"target","type":"Tuple$Target"},{"id":"number","type":"java/lang/Integer"},
                  {"id":"a","type":"Tuple$Item","fields":[{"owner":"Tuple$Item","name":"target","descriptor":"Ljava/lang/Object;","value":{"ref":"target"}},
                    {"owner":"Tuple$Item","name":"name","descriptor":"Ljava/lang/String;","value":"first"},{"owner":"Tuple$Item","name":"types","descriptor":"[Ljava/lang/Class;","value":{"ref":"ta"}},
                    {"owner":"Tuple$Item","name":"args","descriptor":"[Ljava/lang/Object;","value":{"ref":"aa"}}]},
                  {"id":"b","type":"Tuple$Item","fields":[{"owner":"Tuple$Item","name":"target","descriptor":"Ljava/lang/Object;","value":{"ref":"target"}},
                    {"owner":"Tuple$Item","name":"name","descriptor":"Ljava/lang/String;","value":"second"},{"owner":"Tuple$Item","name":"types","descriptor":"[Ljava/lang/Class;","value":{"ref":"tb"}},
                    {"owner":"Tuple$Item","name":"args","descriptor":"[Ljava/lang/Object;","value":{"ref":"ab"}}]},
                  {"id":"ta","type":"[Ljava/lang/Class;","elements":[{"class":"Ljava/lang/String;"}]},{"id":"tb","type":"[Ljava/lang/Class;","elements":[{"class":"Ljava/lang/Integer;"}]},
                  {"id":"aa","type":"[Ljava/lang/Object;","elements":["text"]},{"id":"ab","type":"[Ljava/lang/Object;","elements":[{"ref":"number"}]}]}
                """;
        ScanResult result=scanBound(classes,json,new Program.MethodId("Tuple","run","(Ljava/util/Set;)V"));
        Set<String> calls=targets(result,"run",Kind.REFLECTION);
        assertTrue(calls.stream().anyMatch(t -> t.contains("#first(Ljava/lang/String;)")),calls.toString());
        assertTrue(calls.stream().anyMatch(t -> t.contains("#second(Ljava/lang/Integer;)")),calls.toString());
        assertFalse(calls.stream().anyMatch(t -> t.contains("#first(Ljava/lang/Integer;)") || t.contains("#second(Ljava/lang/String;)")),calls.toString());

    }

    @Test void callbackReceiversRespectCollisionsPriorKeysAndNaturalComparison() throws IOException {
        Path classes=compile("Callbacks", """
                import java.util.*;
                public class Callbacks {
                  public static class Key { public int hashCode(){return 0;} public boolean equals(Object other){return false;} }
                  public static class Different extends Key { public int hashCode(){return 1;} }
                  public static class OrderedKey implements Comparable<OrderedKey> { public int compareTo(OrderedKey other){return 0;} }
                  public static void collide(){ Map<Object,Object> map=new HashMap<>(); map.put(new Key(),"one");map.put(new Key(),"two"); }
                  public static void separate(){ Map<Object,Object> map=new HashMap<>(); map.put(new Key(),"one");map.put(new Different(),"two"); }
                  public static void compare(){ Map<Object,Object> map=new TreeMap<>();map.put(new OrderedKey(),"one");map.put(new OrderedKey(),"two"); }
                }
                """);
        ScanResult result=scan(classes);
        assertTrue(targets(result,"collide",Kind.CONTAINER_CALLBACK).stream().anyMatch(t -> t.contains("Key#equals")),result.limitations().toString());
        assertFalse(targets(result,"separate",Kind.CONTAINER_CALLBACK).stream().anyMatch(t -> t.contains("#equals")));
        assertTrue(targets(result,"compare",Kind.CONTAINER_CALLBACK).stream().anyMatch(t -> t.contains("#compareTo")));
        assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.CONTAINER_CALLBACK && r.target().map(t -> t.name().equals("equals")).orElse(false)).flatMap(r -> r.supports().stream()).allMatch(support -> !support.witnesses().isEmpty()));
    }

    @Test void mapLookupAndStringificationReturnValuesFeedReflection() throws IOException {
        Path classes=compile("LibraryFlow", """
                import java.util.*;
                public class LibraryFlow {
                  public static class Target { public void ping() {} public void wrong() {} }
                  public static class Name { public String toString(){return "ping";} }
                  static void dispatch(String name)throws Exception {Target.class.getMethod(name,new Class[0]).invoke(new Target(),new Object[0]);}
                  public static void builders()throws Exception {
                    StringBuilder builder=new StringBuilder();
                    if(builder.append((Object)null)==builder && builder.append((Object)"text")==builder) dispatch("ping");else dispatch("wrong");
                  }
                  public static void run() throws Exception {
                    Map<Object,Object> map=new HashMap<>();map.put("key",new Target());
                    Object target=map.get("key");
                    String name=String.valueOf(new Name());
                    target.getClass().getMethod(name,new Class[0]).invoke(target,new Object[0]);
                  }
                }
                """);
        ScanResult result=scan(classes);
        assertTrue(targets(result,"run",Kind.CONTAINER_CALLBACK).stream().anyMatch(t -> t.contains("Name#toString")));
        assertTrue(findings(result,"run").stream().anyMatch(f -> f.detail().contains("Target#ping")));
        assertTrue(targets(result,"builders",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#ping")));
        assertFalse(targets(result,"builders",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#wrong")));
    }

    @Test void boundNativeRootFindsDependencyReadResolveAndUsesItsReplacement() throws IOException {
        Path classes=compile("Roots", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class Roots {
                  public static class Old implements Serializable { private Object readResolve(){return new Replacement();} }
                  public static class Wrong implements Serializable {
                    private static Object readResolve(){return new Replacement();}
                    public void readObject(ObjectInputStream input) {}
                  }
                  public static class Replacement { public void replacement() {} }
                  public static void run(ObjectInputStream input) throws Exception {
                    Object value=input.readObject();
                    value.getClass().getMethod("replacement",new Class[0]).invoke(value,new Object[0]);
                  }
                }
                """);
        Path main=temp.resolve("native-main.jar"),library=temp.resolve("native-library.jar");
        try (JarOutputStream jar=new JarOutputStream(Files.newOutputStream(main))) { member(jar,"Roots.class",Files.readAllBytes(classes.resolve("Roots.class"))); }
        try (JarOutputStream jar=new JarOutputStream(Files.newOutputStream(library))) {
            for (String name:List.of("Old","Wrong","Replacement")) member(jar,"Roots$"+name+".class",Files.readAllBytes(classes.resolve("Roots$"+name+".class")));
        }
        String json="""
                {"source":"native callback input fixture","basis":"BINDING",
                 "entry":{"owner":"Roots","name":"run","descriptor":"(Ljava/io/ObjectInputStream;)V","arguments":[{"ref":"stream"}]},
                 "objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"root"}}, {"id":"root","type":"Roots$Old"}]}
                """;
        Path facts=temp.resolve("native.json");
        for (boolean valid:List.of(true,false)) {
            Files.writeString(facts,valid?json:json.replace("Roots$Old","Roots$Wrong"));
            try (Inputs input=Inputs.open(main,List.of(library),jdk,Inputs.Limits.defaults())) {
                Program program=new Program(input,20000);
                ScanResult result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                        .scan(EntryPoints.Mode.COMPONENT,true,Set.of(new Program.MethodId("Roots","run","(Ljava/io/ObjectInputStream;)V")),Optional.of(io.just.input.StaticData.read(facts)));
                assertEquals(valid,targets(result,"run",Kind.DESERIALIZATION).stream().anyMatch(t -> t.contains("Old#readResolve")));
                assertEquals(valid,targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Replacement#replacement")));
                assertFalse(targets(result,"run",Kind.DESERIALIZATION).stream().anyMatch(t -> t.contains("Wrong#readObject") || t.contains("Wrong#readResolve")));
                if (valid) assertTrue(findings(result,"run").stream().anyMatch(f -> f.detail().contains("Replacement#replacement")),result.limitations().toString());
            }
        }
    }

    @Test void nativeMembershipBindsTheCallbackKeyAndNeverPromotesAMapValue() throws IOException {
        Path classes=compile("NativeKeys", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class NativeKeys {
                  public static class Target implements Serializable { public void ping() {} }
                  public static class Key implements Serializable {
                    Target target;
                    public int hashCode(){target.ping();return 0;}
                  }
                  public static void run(ObjectInputStream input) throws Exception {input.readObject();}
                }
                """);
        String json="""
                {"source":"native member snapshot","basis":"BINDING",
                 "entry":{"owner":"NativeKeys","name":"run","descriptor":"(Ljava/io/ObjectInputStream;)V","arguments":[{"ref":"stream"}]},
                 "objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"root"}},
                  {"id":"root","type":"java/util/HashSet","elements":[{"ref":"key"}]},
                  {"id":"key","type":"NativeKeys$Key","fields":[{"owner":"NativeKeys$Key","name":"target","descriptor":"LNativeKeys$Target;","value":{"ref":"target"}}]},
                  {"id":"target","type":"NativeKeys$Target"}]}
                """;
        Program.MethodId entry=new Program.MethodId("NativeKeys","run","(Ljava/io/ObjectInputStream;)V");
        ScanResult member=scanBound(classes,json,entry);
        assertTrue(targets(member,"run",Kind.CONTAINER_CALLBACK).stream().anyMatch(t -> t.contains("Key#hashCode")));
        assertTrue(member.relations().stream().anyMatch(r -> r.target().map(t -> t.owner().equals("NativeKeys$Target") && t.name().equals("ping")).orElse(false)));
        ScanResult value=scanBound(classes,json.replace("\"type\":\"java/util/HashSet\",\"elements\":[{\"ref\":\"key\"}]","\"type\":\"java/util/HashMap\",\"entries\":[{\"key\":\"plain\",\"value\":{\"ref\":\"key\"}}]"),entry);
        assertFalse(targets(value,"run",Kind.CONTAINER_CALLBACK).stream().anyMatch(t -> t.contains("Key#hashCode")));
    }

    @Test void nativeDefaultFieldsRespectHookTimingScopeAndExceptions() throws IOException {
        Path classes=compile("Timing", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class Timing {
                  public static class Target implements Serializable { public void before(){} public void after(){} public void caught(){} public void parent(){} }
                  public static class Ordered implements Serializable {
                    Target target;
                    private void readObject(ObjectInputStream in)throws Exception {if(target!=null)target.before();in.defaultReadObject();target.after();}
                  }
                  public static class Skipped implements Serializable {
                    Target target;
                    private void readObject(ObjectInputStream in){if(target!=null)target.before();}
                  }
                  public static class Repeated implements Serializable {
                    Target target;
                    private void readObject(ObjectInputStream in)throws Exception {in.defaultReadObject();try{in.defaultReadObject();target.before();}catch(NotActiveException expected){target.caught();}target.after();}
                  }
                  public static class Parent implements Serializable {
                    Target target;
                    private void readObject(ObjectInputStream in)throws Exception {in.defaultReadObject();target.parent();}
                  }
                  public static class Child extends Parent {
                    Target child;
                    private void readObject(ObjectInputStream in)throws Exception {if(child!=null)child.before();in.defaultReadObject();child.after();target.parent();}
                  }
                  public static class Cycle implements Serializable {
                    Cycle next; Target target;
                    private void readObject(ObjectInputStream in)throws Exception {in.defaultReadObject();if(next==this)target.after();}
                  }
                  public static class Aggregate implements Serializable {
                    Target alpha;Observer beta;int flag;
                    private void readObject(ObjectInputStream in)throws Exception {in.defaultReadObject();alpha.after();}
                  }
                  public static class Observer implements Serializable {
                    Aggregate owner;
                    private void readObject(ObjectInputStream in)throws Exception {in.defaultReadObject();if(owner.alpha!=null)owner.alpha.before();if(owner.flag!=0)new Target().before();}
                  }
                  public static class Stream extends ObjectInputStream {public Stream()throws IOException{super();}}
                  public static void run(ObjectInputStream in)throws Exception{in.readObject();}
                  public static void inherited(Stream in)throws Exception{in.readObject();}
                  public static void illegal(ObjectInputStream in)throws Exception{in.defaultReadObject();new Target().before();}
                }
                """);
        for(String type:List.of("Ordered","Skipped","Repeated","Child","Cycle","Aggregate")) {
            String owner=type.equals("Child")?"Parent":type;
            String fields="{\"owner\":\"Timing$"+owner+"\",\"name\":\"target\",\"descriptor\":\"LTiming$Target;\",\"value\":{\"ref\":\"target\"}}";
            if(type.equals("Child"))fields+=",{\"owner\":\"Timing$Child\",\"name\":\"child\",\"descriptor\":\"LTiming$Target;\",\"value\":{\"ref\":\"target\"}}";
            if(type.equals("Cycle"))fields+=",{\"owner\":\"Timing$Cycle\",\"name\":\"next\",\"descriptor\":\"LTiming$Cycle;\",\"value\":{\"ref\":\"root\"}}";
            if(type.equals("Aggregate"))fields=fields.replace("\"name\":\"target\"","\"name\":\"alpha\"")+",{\"owner\":\"Timing$Aggregate\",\"name\":\"beta\",\"descriptor\":\"LTiming$Observer;\",\"value\":{\"ref\":\"observer\"}},{\"owner\":\"Timing$Aggregate\",\"name\":\"flag\",\"descriptor\":\"I\",\"value\":1}";
            String facts="""
                    {"source":"compiled lifecycle fixture","basis":"BINDING",
                     "entry":{"owner":"Timing","name":"run","descriptor":"(Ljava/io/ObjectInputStream;)V","arguments":[{"ref":"stream"}]},
                     "objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"root"}},
                     {"id":"root","type":"Timing$%s","fields":[%s]},{"id":"target","type":"Timing$Target"}%s]}
                    """.formatted(type,fields,type.equals("Aggregate")?",{\"id\":\"observer\",\"type\":\"Timing$Observer\",\"fields\":[{\"owner\":\"Timing$Observer\",\"name\":\"owner\",\"descriptor\":\"LTiming$Aggregate;\",\"value\":{\"ref\":\"root\"}}]}":"");
            ScanResult result=scanBound(classes,facts,new Program.MethodId("Timing","run","(Ljava/io/ObjectInputStream;)V"));
            Set<String> calls=result.relations().stream().flatMap(r -> r.target().stream()).map(Object::toString).collect(Collectors.toSet());
            assertFalse(calls.stream().anyMatch(t -> t.contains("Target#before")),type+calls);
            assertEquals(!type.equals("Skipped"),calls.stream().anyMatch(t -> t.contains("Target#after")),type+result.limitations()+calls);
            if(type.equals("Repeated"))assertTrue(calls.stream().anyMatch(t -> t.contains("Target#caught")),calls.toString());
            if(type.equals("Child"))assertTrue(calls.stream().anyMatch(t -> t.contains("Target#parent")),calls.toString());
            assertFalse(result.relations().stream().flatMap(r -> r.supports().stream().flatMap(s -> s.gaps().stream())).anyMatch(g -> g.detail().contains("custom hook field materialization/order")));
            if(type.equals("Ordered")) {
                ScanResult inherited=scanBound(classes,facts.replace("\"name\":\"run\"","\"name\":\"inherited\"").replace("\"descriptor\":\"(Ljava/io/ObjectInputStream;)V\"","\"descriptor\":\"(LTiming$Stream;)V\"").replace("\"type\":\"java/io/ObjectInputStream\"","\"type\":\"Timing$Stream\""),new Program.MethodId("Timing","inherited","(LTiming$Stream;)V"));
                assertTrue(inherited.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("Timing$Target") && t.name().equals("after")),inherited.limitations().toString());
                ScanResult illegal=scanBound(classes,facts.replace("\"name\":\"run\"","\"name\":\"illegal\""),new Program.MethodId("Timing","illegal","(Ljava/io/ObjectInputStream;)V"));
                assertFalse(illegal.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.name().equals("before")));
            }
        }
    }

    @Test void customObjectInputImplementationKeepsItsOwnReturnInsteadOfNativeCallbacks() throws IOException {
        Path classes=compile("UserInput", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class UserInput extends DataInputStream implements ObjectInput {
                  public UserInput(){super(null);}public Object readObject(){return new Target();}
                  public static class Target {public void ok(){}}
                  public static class Decoy implements Serializable {private Object readResolve(){return new Wrong();}}
                  public static class Wrong {public void ok(){}}
                  public static void run(ObjectInput in)throws Exception{Object value=in.readObject();value.getClass().getMethod("ok",new Class[0]).invoke(value,new Object[0]);}
                }
                """);
        String facts="""
                {"source":"compiled ObjectInput implementation","basis":"BINDING",
                "entry":{"owner":"UserInput","name":"run","descriptor":"(Ljava/io/ObjectInput;)V","arguments":[{"ref":"stream"}]},
                "objects":[{"id":"stream","type":"UserInput","decoded":{"ref":"root"}},{"id":"root","type":"UserInput$Decoy"}]}
                """;
        ScanResult result=scanBound(classes,facts,new Program.MethodId("UserInput","run","(Ljava/io/ObjectInput;)V"));
        assertTrue(targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("UserInput$Target#ok")),result.limitations().toString());
        assertFalse(result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("UserInput$Decoy") || t.owner().equals("UserInput$Wrong")));
    }

    @Test void externalizableConstructorMustReturnBeforeHookUsesItsState() throws IOException {
        Path classes=compile("External", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class External {
                  public static class Target { public void ready(){} }
                  public static class Decoy extends Target {public void ready(){wrong();}public void wrong(){}}
                  public static class Good implements Externalizable {
                    Target target; public Good(){target=new Target();}
                    public void readExternal(ObjectInput in){target.ready();} public void writeExternal(ObjectOutput out){}
                  }
                  public static class Hidden implements Externalizable {
                    private Hidden(){} public void readExternal(ObjectInput in){new Target().ready();}public void writeExternal(ObjectOutput out){}
                  }
                  public static class Broken implements Externalizable {
                    public Broken(){throw new IllegalStateException();} public void readExternal(ObjectInput in){new Target().ready();}public void writeExternal(ObjectOutput out){}
                  }
                  public static class Missing implements Externalizable {
                    public Missing(String value){} public void readExternal(ObjectInput in){new Target().ready();}public void writeExternal(ObjectOutput out){}
                  }
                  public static class Conditional implements Externalizable {
                    Target target;public Conditional(){if(System.currentTimeMillis()>0)target=new Target();}
                    public void readExternal(ObjectInput in){target.ready();}public void writeExternal(ObjectOutput out){}
                  }
                  public static void run(ObjectInputStream in)throws Exception{in.readObject();}
                }
                """);
        for(String type:List.of("Good","Hidden","Broken","Missing","Conditional")) {
            String facts="""
                    {"source":"compiled constructor fixture","basis":"BINDING",
                    "entry":{"owner":"External","name":"run","descriptor":"(Ljava/io/ObjectInputStream;)V","arguments":[{"ref":"stream"}]},
                    "objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"root"}},{"id":"root","type":"External$%s"%s},{"id":"decoy","type":"External$Decoy"}]}
                    """.formatted(type,type.equals("Good")?",\"fields\":[{\"owner\":\"External$Good\",\"name\":\"target\",\"descriptor\":\"LExternal$Target;\",\"value\":{\"ref\":\"decoy\"}}]":"");
            ScanResult result=scanBound(classes,facts,new Program.MethodId("External","run","(Ljava/io/ObjectInputStream;)V"));
            assertEquals(type.equals("Good") || type.equals("Conditional"),result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("External$Target") && t.name().equals("ready")),type+result.limitations());
            assertEquals(type.equals("Good") || type.equals("Conditional"),result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("External$"+type) && t.name().equals("readExternal")),type+result.limitations());
            assertFalse(result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.owner().equals("External$Decoy")));
            if(type.equals("Conditional"))assertTrue(result.relations().stream().filter(r -> r.target().filter(t -> t.name().equals("ready")).isPresent()).allMatch(r -> r.supports().stream().allMatch(s -> !s.gaps().isEmpty()) || !r.conditions().choices().isEmpty()));
        }
    }

    @Test void serializedFieldTypeIsCheckedAfterReplacementAndBeforeHookContinuation() throws IOException {
        Path classes=compile("FieldResolve", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class FieldResolve {
                  public static class Desired {public void hit(){}public void caught(){}}
                  public static class Good implements Serializable {private Object readResolve(){return new Desired();}}
                  public static class Bad implements Serializable {private Object readResolve(){return "wrong type";}}
                  public static class Root implements Serializable {
                    Desired field;
                    private void readObject(ObjectInputStream in)throws Exception {try{in.defaultReadObject();field.hit();}catch(ClassCastException expected){new Desired().caught();}}
                  }
                  public static void run(ObjectInputStream in)throws Exception {in.readObject();}
                }
                """);
        for(String type:List.of("Good","Bad")) {
            String facts="""
                    {"source":"compiled field replacement fixture","basis":"BINDING",
                    "entry":{"owner":"FieldResolve","name":"run","descriptor":"(Ljava/io/ObjectInputStream;)V","arguments":[{"ref":"stream"}]},
                    "objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"root"}},
                    {"id":"root","type":"FieldResolve$Root","fields":[{"owner":"FieldResolve$Root","name":"field","descriptor":"LFieldResolve$Desired;","value":{"ref":"form"}}]},
                    {"id":"form","type":"FieldResolve$%s"}]}
                    """.formatted(type);
            ScanResult result=scanBound(classes,facts,new Program.MethodId("FieldResolve","run","(Ljava/io/ObjectInputStream;)V"));
            assertEquals(type.equals("Good"),result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.name().equals("hit")),type+result.limitations());
            assertEquals(type.equals("Bad"),result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.name().equals("caught")),type+result.limitations());
        }
    }

    @Test void nativeContainerUsesReadResolveReplacementInsteadOfOriginalKeyOrMapValue() throws IOException {
        Path classes=compile("ReplaceKeys", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class ReplaceKeys {
                  public static class Old implements Serializable {private Object readResolve(){return new Replacement();}public int hashCode(){wrong();return 0;}public void wrong(){} }
                  public static class Nil implements Serializable {private Object readResolve(){return null;}public int hashCode(){wrong();return 0;}public void wrong(){} }
                  public static class Self implements Serializable {private Object readResolve(){return this;}public int hashCode(){right();return 0;}public void right(){} }
                  public static class Broken implements Serializable {private Object readResolve(){throw new IllegalStateException();}public int hashCode(){wrong();return 0;}public void wrong(){} }
                  public static class Replacement {public int hashCode(){right();return 0;}public void right(){} }
                  public static void run(ObjectInputStream in)throws Exception{in.readObject();}
                }
                """);
        for(String type:List.of("Old","Nil","Self","Broken")) {
            String facts="""
                    {"source":"compiled replacement fixture","basis":"BINDING",
                    "entry":{"owner":"ReplaceKeys","name":"run","descriptor":"(Ljava/io/ObjectInputStream;)V","arguments":[{"ref":"stream"}]},
                    "objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"root"}},
                    {"id":"root","type":"java/util/HashSet","elements":[{"ref":"key"}]},{"id":"key","type":"ReplaceKeys$%s"}]}
                    """.formatted(type);
            ScanResult result=scanBound(classes,facts,new Program.MethodId("ReplaceKeys","run","(Ljava/io/ObjectInputStream;)V"));
            assertFalse(result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.name().equals("wrong")),type+result.limitations());
            assertEquals(type.equals("Old") || type.equals("Self"),result.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.name().equals("right")),type+result.limitations());
            if(type.equals("Old")) {
                ScanResult value=scanBound(classes,facts.replace("\"type\":\"java/util/HashSet\",\"elements\":[{\"ref\":\"key\"}]","\"type\":\"java/util/HashMap\",\"entries\":[{\"key\":\"plain\",\"value\":{\"ref\":\"key\"}}]"),new Program.MethodId("ReplaceKeys","run","(Ljava/io/ObjectInputStream;)V"));
                assertFalse(value.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.name().equals("right")));
            }
        }
    }

    @Test void nativeResolvedKeysRespectCollisionMemoStreamScopeAndFailureOrder() throws IOException {
        Path classes=compile("NativeOrder", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class NativeOrder {
                  public static class Old implements Serializable {private Object readResolve(){return new Key();}}
                  public static class Broken implements Serializable {private Object readResolve(){throw new IllegalStateException();}}
                  public static class Key {public int hashCode(){return 0;}public boolean equals(Object other){return false;}}
                  public static void run(ObjectInputStream in)throws Exception{in.readObject();}
                  public static void twice(ObjectInputStream first,ObjectInputStream second)throws Exception{first.readObject();second.readObject();}
                }
                """);
        String template="""
                {"source":"compiled native collision fixture","basis":"BINDING",
                "entry":{"owner":"NativeOrder","name":"run","descriptor":"(Ljava/io/ObjectInputStream;)V","arguments":[{"ref":"stream"}]},
                "objects":[{"id":"stream","type":"java/io/ObjectInputStream","decoded":{"ref":"root"}},
                {"id":"root","type":"java/util/HashSet","elements":[%s]},
                {"id":"a","type":"NativeOrder$Old"},{"id":"b","type":"NativeOrder$Old"},{"id":"bad","type":"NativeOrder$Broken"}]}
                """;
        for(String members:List.of("{\"ref\":\"a\"},{\"ref\":\"b\"}","{\"ref\":\"a\"},{\"ref\":\"a\"}","{\"ref\":\"bad\"},{\"ref\":\"b\"}")) {
            ScanResult result=scanBound(classes,template.formatted(members),new Program.MethodId("NativeOrder","run","(Ljava/io/ObjectInputStream;)V"));
            List<Relation> equals=result.relations().stream().filter(r -> r.kind()==Kind.CONTAINER_CALLBACK && r.target().filter(t -> t.owner().equals("NativeOrder$Key") && t.name().equals("equals")).isPresent()).toList();
            assertEquals(members.contains("\"b\"") && !members.contains("bad"),!equals.isEmpty(),members+result.limitations());
            for(Relation relation:equals) {
                assertTrue(relation.receiver() instanceof ObjectValue receiver && relation.arguments().get(0) instanceof ObjectValue prior && receiver.type().equals("NativeOrder$Key") && prior.type().equals(receiver.type()) && receiver.id()!=prior.id());
                assertTrue(relation.supports().stream().flatMap(s -> s.gaps().stream()).noneMatch(g -> g.kind()==GapKind.INPUT_BINDING),relation.supports().toString());
            }
            if(!members.contains("b"))assertEquals(1,result.relations().stream().filter(r -> r.kind()==Kind.DESERIALIZATION && r.target().filter(t -> t.name().equals("readResolve")).isPresent()).count());
            if(members.contains("bad"))assertFalse(result.relations().stream().anyMatch(r -> r.kind()==Kind.CONTAINER_CALLBACK && r.target().filter(t -> t.owner().equals("NativeOrder$Key")).isPresent()));
        }
        var facts=com.google.gson.JsonParser.parseString(template.formatted("{\"ref\":\"a\"}")).getAsJsonObject();
        facts.getAsJsonObject("entry").addProperty("name","twice");facts.getAsJsonObject("entry").addProperty("descriptor","(Ljava/io/ObjectInputStream;Ljava/io/ObjectInputStream;)V");
        facts.getAsJsonObject("entry").getAsJsonArray("arguments").add(com.google.gson.JsonParser.parseString("{\"ref\":\"second\"}"));
        facts.getAsJsonArray("objects").add(com.google.gson.JsonParser.parseString("{\"id\":\"second\",\"type\":\"java/io/ObjectInputStream\",\"decoded\":{\"ref\":\"other-root\"}}"));
        facts.getAsJsonArray("objects").add(com.google.gson.JsonParser.parseString("{\"id\":\"other-root\",\"type\":\"java/util/HashSet\",\"elements\":[{\"ref\":\"a\"}]}"));
        ScanResult twice=scanBound(classes,facts.toString(),new Program.MethodId("NativeOrder","twice","(Ljava/io/ObjectInputStream;Ljava/io/ObjectInputStream;)V"));
        assertEquals(2,twice.relations().stream().filter(r -> r.kind()==Kind.DESERIALIZATION && r.target().filter(t -> t.owner().equals("NativeOrder$Old") && t.name().equals("readResolve")).isPresent()).count());
    }

    @Test void reusableForwardersAndGettersUseCurrentArgumentsObjectAndStrongWrite() throws IOException {
        Path classes=compile("Forwarders", """
                public class Forwarders {
                  public interface Target {void hit();}
                  public static class A implements Target {public void hit(){}}
                  public static class B implements Target {public void hit(){}}
                  public static class Box {Target target;public Target get(){return target;}}
                  public static Target identity(Target value){return value;}
                  public static Target selected(Box first,Box second,boolean choose){if(choose)return first.get();return second.get();}
                  public static void run(){
                    Box first=new Box(),second=new Box();first.target=new A();second.target=new B();
                    identity(first.get()).hit();
                    first.target=new B();identity(first.get()).hit();
                    selected(second,first,true).hit();
                  }
                }
                """);
        ScanResult result;
        try(Inputs input=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults(),true).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Forwarders","run","()V")));
        }
        List<Relation> hits=result.relations().stream().filter(r -> r.site().method().name().equals("run") && r.target().filter(t -> t.name().equals("hit")).isPresent()).toList();
        assertEquals(3,hits.size(),hits.toString());
        hits=hits.stream().sorted(Comparator.comparingInt(r -> r.site().instruction())).toList();
        assertEquals(List.of("Forwarders$A","Forwarders$B","Forwarders$B"),hits.stream().map(r -> r.target().orElseThrow().owner()).toList());
        assertTrue(hits.stream().flatMap(r -> r.supports().stream()).allMatch(support -> support.gaps().stream().noneMatch(g -> g.kind()==GapKind.INPUT_BINDING)),hits.toString());
        assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.FIELD_FLOW && r.site().method().name().equals("get") && r.slot().filter(s -> s instanceof Field f && f.field().name().equals("target")).isPresent()));
    }

    @Test void switchArrayLengthArithmeticAndReferenceTypesSelectOnlyFeasibleTargets() throws IOException {
        Path classes=compile("JvmPaths", """
                public class JvmPaths {
                  public static class Target {public void right(){} public void wrong(){}}
                  static void dispatch(String name) throws Exception {Target.class.getMethod(name,new Class[0]).invoke(new Target(),new Object[0]);}
                  public static void run() throws Exception {
                    int[] values=new int[2]; int key=values.length+2;
                    switch(key) {case -10:dispatch("wrong");break;case 4:dispatch("right");break;case 1000:dispatch("wrong");break;default:dispatch("wrong");}
                    Object first=new Target(),second=new Object();
                    if(first==second) dispatch("wrong");
                    if(!(first instanceof Target)) dispatch("wrong");
                    if((7L+2L)!=9L) dispatch("wrong");
                  }
                  public static void dense() throws Exception {
                    int key=2;
                    switch(key) {case 0:dispatch("wrong");break;case 1:dispatch("wrong");break;case 2:dispatch("right");break;default:dispatch("wrong");}
                  }
                }
                """);
        ScanResult result=scan(classes);
        for (String entry:List.of("run","dense")) {
            assertTrue(targets(result,entry,Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#right")));
            assertFalse(targets(result,entry,Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#wrong")));
        }
    }

    @Test void exceptionHandlersSeparateKnownNormalKnownThrowAndUnknownFlow() throws IOException {
        Path classes=compile("Exceptional", """
                public class Exceptional {
                  public static class Target {public void caught(){} public void wrong(){}}
                  static void dispatch(String name) throws Exception {Target.class.getMethod(name,new Class[0]).invoke(new Target(),new Object[0]);}
                  public static void knownThrow() throws Exception {
                    try {int divisor=0;int value=5/divisor;dispatch("wrong");}
                    catch(ArithmeticException expected){dispatch("caught");}
                  }
                  public static void knownNormal() throws Exception {
                    try {int[] array=new int[1];int value=array[0];}
                    catch(ArithmeticException impossible){dispatch("wrong");}
                  }
                  public static void unknown(int divisor) throws Exception {
                    try {int value=5/divisor;}catch(ArithmeticException possible){dispatch("caught");}
                  }
                  public static void wrongHandler() throws Exception {
                    try {int divisor=0;int value=5/divisor;}catch(ClassCastException impossible){dispatch("wrong");}
                    dispatch("wrong");
                  }
                }
                """);
        ScanResult result=scan(classes);
        assertTrue(targets(result,"knownThrow",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#caught")));
        assertFalse(targets(result,"knownThrow",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#wrong")));
        assertTrue(findings(result,"knownThrow").stream().anyMatch(f -> f.detail().contains("Target#caught")));
        assertFalse(targets(result,"knownNormal",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#wrong")));
        assertFalse(targets(result,"wrongHandler",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#wrong")));

        assertTrue(findings(result,"unknown").stream().anyMatch(f -> f.gaps().stream().anyMatch(g -> g.kind()==GapKind.CONTROL_CONDITION)));
    }

    @Test void lambdaCapturesConstructorReferencesAndAltMetadataKeepTheirOwnBindings() throws IOException {
        Path classes=compile("Lambdas", """
                import java.io.Serializable;
                import java.util.function.Supplier;
                public class Lambdas {
                  public interface Task {Object run() throws Exception;}
                  public static class A {public void alpha(){} public void beta(){}}
                  public static class B {public void alpha(){} public void beta(){}}
                  static Task make(Object target,String name){return () -> target.getClass().getMethod(name,new Class[0]).invoke(target,new Object[0]);}
                  public static void run() throws Exception {Task first=make(new A(),"alpha"),second=make(new B(),"beta");first.run();second.run();}
                  public static void construct() throws Exception {Supplier<A> factory=A::new;A value=factory.get();value.getClass().getMethod("alpha",new Class[0]).invoke(value,new Object[0]);}
                  public static void alternate() throws Exception {A value=new A();Task task=(Task & Serializable)() -> value.getClass().getMethod("alpha",new Class[0]).invoke(value,new Object[0]);task.run();}
                  public static void metadataTrap() {}
                }
                """);
        ScanResult result=scan(classes);
        Set<String> bound=targets(result,"run",Kind.REFLECTION);
        assertTrue(bound.stream().anyMatch(t -> t.contains("A#alpha")),result.limitations().toString());
        assertTrue(bound.stream().anyMatch(t -> t.contains("B#beta")));
        assertFalse(bound.stream().anyMatch(t -> t.contains("A#beta") || t.contains("B#alpha")));
        for (String entry:List.of("construct","alternate")) assertTrue(findings(result,entry).stream().anyMatch(f -> f.detail().contains("A#alpha")));
        org.objectweb.asm.tree.ClassNode node=new org.objectweb.asm.tree.ClassNode();
        new org.objectweb.asm.ClassReader(Files.readAllBytes(classes.resolve("Lambdas.class"))).accept(node,0);
        for (var method:node.methods) if (method.name.equals("alternate")) for (var instruction:method.instructions)
            if (instruction instanceof org.objectweb.asm.tree.InvokeDynamicInsnNode dynamic) {
                Object[] metadata=Arrays.copyOf(dynamic.bsmArgs,dynamic.bsmArgs.length+1);
                metadata[metadata.length-1]=new org.objectweb.asm.Handle(org.objectweb.asm.Opcodes.H_INVOKESTATIC,"Lambdas","metadataTrap","()V",false);
                dynamic.bsmArgs=metadata;
            }
        var writer=new org.objectweb.asm.ClassWriter(0);node.accept(writer);Files.write(classes.resolve("Lambdas.class"),writer.toByteArray());
        ScanResult invalid=scan(classes);
        assertFalse(targets(invalid,"alternate",Kind.DYNAMIC_CALL).stream().anyMatch(t -> t.contains("metadataTrap")));
        assertFalse(targets(invalid,"alternate",Kind.REFLECTION).stream().anyMatch(t -> t.contains("A#alpha")));
        assertTrue(findings(invalid,"alternate").stream().anyMatch(f -> f.gaps().stream().anyMatch(g -> g.kind()==GapKind.UNSUPPORTED)));
        Path missing=compile("MissingFaces","""
                public class MissingFaces {
                  interface Marker {}
                  interface Task {void run();}
                  public static void marker(){Runnable task=(Runnable & Marker)()->{};task.run();}
                  public static void function(){Task task=()->{};task.run();}
                }
                """);
        Files.delete(missing.resolve("MissingFaces$Marker.class"));Files.delete(missing.resolve("MissingFaces$Task.class"));
        ScanResult incomplete=scan(missing);
        for(String entry:List.of("marker","function"))
            assertTrue(findings(incomplete,entry).stream().flatMap(f -> f.gaps().stream())
                    .anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY && g.detail().contains("lambda")),entry);
    }

    @Test void proxyCallsUseTheCreatedHandlerAndDoNotBypassItForDefaults() throws IOException {
        Path classes=compile("Proxies", """
                import java.lang.reflect.*;
                public class Proxies {
                  public interface Service {
                    Object call(String name) throws Exception;
                    default void bypass() throws Exception {A.class.getMethod("bad",new Class[0]).invoke(new A(),new Object[0]);}
                  }
                  public static class A implements Service {
                    public void alpha(){}public void beta(){}public void bad(){}
                    public Object call(String name) throws Exception {return getClass().getMethod(name,new Class[0]).invoke(this,new Object[0]);}
                  }
                  public static class B implements Service {
                    public void alpha(){}public void beta(){}
                    public Object call(String name) throws Exception {return getClass().getMethod(name,new Class[0]).invoke(this,new Object[0]);}
                  }
                  public static class Forward implements InvocationHandler {
                    Object target;Forward(Object value){target=value;}
                    public Object invoke(Object proxy,Method method,Object[] args) throws Throwable {return method.invoke(target,args);}
                  }
                  public static class Ignore implements InvocationHandler {public Object invoke(Object proxy,Method method,Object[] args){return null;}}
                  public static void run() throws Exception {
                    Service first=(Service)Proxy.newProxyInstance(Service.class.getClassLoader(),new Class[]{Service.class},new Forward(new A()));
                    Service second=(Service)Proxy.newProxyInstance(Service.class.getClassLoader(),new Class[]{Service.class},new Forward(new B()));
                    first.call("alpha");second.call("beta");
                  }
                  public static void defaults() throws Exception {Service value=(Service)Proxy.newProxyInstance(Service.class.getClassLoader(),new Class[]{Service.class},new Ignore());value.bypass();}
                  public static void missing(Service value) throws Exception {value.call("alpha");}
                }
                """);
        ScanResult result=scan(classes);
        Set<String> bound=targets(result,"run",Kind.REFLECTION);
        assertTrue(bound.stream().anyMatch(t -> t.contains("A#alpha")),result.limitations().toString());
        assertTrue(bound.stream().anyMatch(t -> t.contains("B#beta")));
        assertFalse(bound.stream().anyMatch(t -> t.contains("A#beta") || t.contains("B#alpha")));
        assertFalse(targets(result,"defaults",Kind.REFLECTION).stream().anyMatch(t -> t.contains("#bad")));
        assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.owner().endsWith("$A") && t.name().equals("alpha")).isPresent()).flatMap(r -> r.supports().stream()).allMatch(support -> !support.gaps().isEmpty()),"an unspecified interface receiver is a conditional candidate");
        assertTrue(findings(result,"run").stream().anyMatch(f -> f.detail().contains("A#alpha")));
    }

    @Test void methodLookupSnapshotsItsSignatureBeforeTheArrayIsModified() throws IOException {
        Path classes=compile("LookupSnapshot", """
                import java.lang.reflect.*;
                public class LookupSnapshot {
                  public static class Target { public void choose(String value){} public void choose(Object value){} }
                  public static void run() throws Exception {
                    Class[] signature={String.class};Method method=Target.class.getMethod("choose",signature);
                    signature[0]=Object.class;method.invoke(new Target(),new Object[]{"text"});
                  }
                }
                """);
        ScanResult result=scan(classes);
        Set<String> bound=targets(result,"run",Kind.REFLECTION);
        assertTrue(bound.stream().anyMatch(t -> t.contains("choose(Ljava/lang/String;)")));
        assertFalse(bound.stream().anyMatch(t -> t.contains("choose(Ljava/lang/Object;)")));
    }

    @Test void reflectedTargetExceptionsReachTheInvocationTargetHandler() throws IOException {
        Path classes=compile("Wrapped", """
                import java.lang.reflect.*;
                public class Wrapped {
                  public static class Target {public void caught(){}public void wrong(){}}
                  public static class Thrower {public void fail(){throw new IllegalStateException();}}
                  static void dispatch(String name) throws Exception {Target.class.getMethod(name,new Class[0]).invoke(new Target(),new Object[0]);}
                  public static void run() throws Exception {
                    Method method=Thrower.class.getMethod("fail",new Class[0]);Thrower value=new Thrower();
                    try {method.invoke(value,new Object[0]);dispatch("wrong");}
                    catch(InvocationTargetException expected){dispatch("caught");}
                  }
                }
                """);
        ScanResult result=scan(classes);
        assertTrue(targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#caught")));
        assertFalse(targets(result,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#wrong")));
    }

    @Test void structuralGuidanceFindsRenamedForwardersWithoutChangingProof() throws IOException {
        String source="""
                import java.lang.reflect.*;
                public class Shapes {
                  public static void noise(){NOISE}
                  private static Object forward(Method method,Object target,Object[] args) throws Exception {return method.invoke(target,args);}
                  public static Object run(Method method,Object target,Object[] args) throws Exception {return forward(method,target,args);}
                }
                """.replace("NOISE","System.nanoTime();".repeat(100));
        Analyzer.Limits budget=new Analyzer.Limits(100,600,10,1000,100,64);
        Path classes=compile("Shapes",source);
        ScanResult guided=scan(classes,budget,true),plain=scan(classes,budget,false);
        assertTrue(guided.hints().stream().anyMatch(h -> h.anchor().name().equals("run") && h.mechanism().contains("forwarder")));
        assertTrue(findings(guided,"run").stream().anyMatch(f -> f.boundary()==Kind.REFLECTION),guided.statistics()+"; "+guided.relations().stream().map(r -> r.kind()+":"+r.site()+":"+r.target()).limit(22).toList()+"; "+guided.limitations());
        assertTrue(findings(plain,"run").stream().anyMatch(f -> f.boundary()==Kind.REFLECTION && f.gaps().stream().anyMatch(g -> g.kind()==GapKind.DYNAMIC_TARGET)),"an unbound Method stays unresolved under ordinary discovery");
        assertTrue(guided.relations().stream().filter(r -> r.kind()==Kind.REFLECTION).allMatch(r -> r.target().isEmpty()),"a structure hint cannot invent the missing Method target");

        ScanResult renamed=scan(compile("Renamed",source.replace("Shapes","Renamed").replace("forward","transfer")),budget,true);
        assertTrue(findings(renamed,"run").stream().anyMatch(f -> f.boundary()==Kind.REFLECTION));
        ScanResult removed=scan(compile("Removed",source.replace("Shapes","Removed").replace("return method.invoke(target,args)","return null")),budget,true);
        assertTrue(removed.hints().stream().noneMatch(h -> h.anchor().name().equals("run")));
        assertTrue(findings(removed,"run").isEmpty());
    }

    @Test void httpRegistrationsKeepHandlersCapturesAndRequestBodiesSeparate() throws IOException {
        Path classes=compile("HttpApp", """
                import com.sun.net.httpserver.*;import java.io.*;
import java.nio.charset.StandardCharsets;
                public class HttpApp {
                  static class Holder {String name;Holder(String name){this.name=name;}}
                  public static class Target {public void before(){}public void alpha(){}public void beta(){}public void gamma(){}public void unused(){}}
                  static void handle(Holder holder,HttpExchange exchange) throws IOException {
                    try {
                      Target.class.getMethod(holder.name,new Class[0]).invoke(new Target(),new Object[0]);
                      new ObjectInputStream(exchange.getRequestBody()).readObject();
                    } catch(ReflectiveOperationException unavailable) {}
                  }
                  static class Handler implements HttpHandler {Holder holder;Handler(Holder h){holder=h;}public void handle(HttpExchange e)throws IOException{HttpApp.handle(holder,e);}}
                  private static native HttpHandler missing();
                  public static void main(String[] args)throws IOException {
                    HttpServer server=HttpServer.create();Holder a=new Holder("before"),b=new Holder("beta"),c=new Holder("gamma");
                    server.createContext("/a",new Handler(a));a.name="alpha";
                    server.createContext("/b",new Handler(b));server.createContext("/c",e -> handle(c,e));
                    HttpHandler unregistered=new Handler(new Holder("unused"));
                    server.createContext("/missing",missing());server.start();
                  }
                }
                """);
        ScanResult result;
        try (Inputs input=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.APPLICATION,true);
        }
        assertEquals(1,result.entries().size());assertEquals("main",result.entries().get(0).method().id().name());
        Set<String> targets=targets(result,"main",Kind.REFLECTION);
        for (String name:List.of("alpha","beta","gamma")) assertTrue(targets.stream().anyMatch(t -> t.contains("Target#"+name)),targets.toString());
        assertFalse(targets.stream().anyMatch(t -> t.contains("#before") || t.contains("#unused")),targets.toString());
        assertEquals(3,result.relations().stream().filter(r -> r.kind()==Kind.DESERIALIZATION).map(r -> r.receiver()).distinct().count());
        assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.HTTP_CALLBACK && r.supports().stream().flatMap(s -> s.gaps().stream()).anyMatch(g -> g.detail().contains("handler runtime type"))));
        assertTrue(result.findings().stream().allMatch(f -> f.gaps().stream().anyMatch(g -> g.kind()==GapKind.DEPLOYMENT)));
        assertEquals(3,result.relations().stream().filter(r -> r.kind()==Kind.REFLECTION && r.target().map(t -> t.owner().endsWith("$Target")).orElse(false)).count());
        Path invalid=compile("InvalidHttp", """
                import com.sun.net.httpserver.*;
                public class InvalidHttp {
                  static class H implements HttpHandler {public void handle(HttpExchange exchange){}}
                  public static void main(String[] args)throws Exception{HttpServer.create().createContext("/invalid",null);}
                }
                """);
        try (Inputs input=Inputs.open(invalid,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            ScanResult rejected=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.APPLICATION,true);
            assertTrue(rejected.relations().stream().noneMatch(r -> r.kind()==Kind.HTTP_CALLBACK));
        }
    }

    @Test void realDependencyVisitorBytecodeKeepsReceiverAndOpcodeConditions() throws IOException {
        Path classes=compile("VisitorAudit", """
                import org.objectweb.asm.*;import org.objectweb.asm.tree.*;
                public class VisitorAudit {
                  public static class Target {public void seen(){}public void wrong(){}}
                  static class Visitor extends MethodVisitor {
                    String name;Visitor(String value){super(Opcodes.ASM9);name=value;}
                    public void visitInsn(int opcode) {
                      if(opcode==Opcodes.IRETURN) try {Target.class.getMethod(name,new Class[0]).invoke(new Target(),new Object[0]);}
                      catch(ReflectiveOperationException unavailable) {}
                    }
                  }
                  public static void run() {Visitor selected=new Visitor("seen"),unused=new Visitor("wrong");new InsnNode(Opcodes.IRETURN).accept(selected);}
                  public static void wrongOpcode() {new InsnNode(Opcodes.RETURN).accept(new Visitor("wrong"));}
                }
                """);
        List<Path> dependencies=Arrays.stream(System.getProperty("surefire.test.class.path",System.getProperty("java.class.path")).split(java.io.File.pathSeparator))
                .map(Path::of).filter(p -> Set.of("asm-9.8.jar","asm-tree-9.8.jar").contains(p.getFileName().toString())).toList();
        assertEquals(2,dependencies.size(),"default Maven dependencies must be present; this check must not silently skip");
        try (Inputs input=Inputs.open(classes,dependencies,jdk,Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            ScanResult guided=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,true);
            ScanResult plain=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,false);
            assertTrue(guided.relations().stream().anyMatch(r -> r.site().method().owner().equals("org/objectweb/asm/tree/InsnNode") && r.target().map(t -> t.owner().equals("VisitorAudit$Visitor") && t.name().equals("visitInsn")).orElse(false)));
            assertTrue(targets(guided,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#seen")));
            assertFalse(targets(guided,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#wrong")));
            assertTrue(findings(guided,"wrongOpcode").isEmpty());
            assertEquals(signatures(guided),signatures(plain));
            assertEquals(Execution.FINISHED,guided.execution(),guided.limitations().toString());
        }
    }

    @Test void loopCarriedReflectionKeepsItsCandidateAndIterationGap() throws IOException {
        Path classes = compile("Carried", """
                public class Carried {
                  public static class Stage { Object seed; String name; Class[] types; Object[] args; }
                  static Object step(Object value,String name,Class[] types,Object[] args) throws Exception {
                    return value.getClass().getMethod(name,types).invoke(value,args);
                  }
                  public static Object run(java.util.Collection<Stage> stages) throws Exception {
                    Object value=null;
                    for(Stage stage:stages) {
                      if(value==null) value=stage.seed;
                      value=step(value,stage.name,stage.types,stage.args);
                    }
                    return value;
                  }
                }
                """);
        ScanResult result = scan(classes);
        assertTrue(findings(result, "run").stream().anyMatch(f -> f.boundary() == Kind.REFLECTION), result.limitations().toString());

        assertTrue(result.relations().stream().flatMap(r -> r.supports().stream().flatMap(s -> s.gaps().stream())).anyMatch(g -> g.detail().contains("loop-carried")));
        assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.owner().equals("Carried") && t.name().equals("run")).isPresent()),"a later stage can reflectively invoke run with another collection");
        assertEquals(Execution.TRUNCATED, result.execution(), result.limitations().toString());
        assertTrue(result.relations().stream().flatMap(r -> r.supports().stream().flatMap(s -> s.gaps().stream())).anyMatch(g -> g.kind()==GapKind.BUDGET && g.detail().contains("call depth")),"recursive alternatives stop at an explicit frontier without removing the candidate");
    }

    @Test void exactEntrySelectionIsDistinctFromApplicationExposure() throws IOException {
        Path classes = compile("Select", """
                public class Select {
                  public static class Target { public void ping() {} }
                  public static void chosen() throws Exception { Target.class.getMethod("ping",new Class[0]).invoke(new Target(),new Object[0]); }
                  public static void other() {}
                }
                """);
        Path output = temp.resolve("selected");
        ByteArrayOutputStream errors = new ByteArrayOutputStream();
        String[] command = {"--input",classes.toString(),"--jdk-home",jdk.toString(),"--mode","component","--entry","Select#chosen()V","--output",output.toString()};
        assertEquals(0, Main.run(command, System.out, new PrintStream(errors,true,StandardCharsets.UTF_8)), errors.toString(StandardCharsets.UTF_8));
        var result = com.google.gson.JsonParser.parseString(Files.readString(output.resolve("report.json"))).getAsJsonObject();
        assertEquals(1, result.getAsJsonArray("entries").size());
        assertFalse(result.getAsJsonArray("findings").isEmpty());
        command[5] = "application";
        command[9] = temp.resolve("invalid-selection").toString();
        assertEquals(0, Main.run(command, System.out, new PrintStream(errors,true,StandardCharsets.UTF_8)));
        var explicit=com.google.gson.JsonParser.parseString(Files.readString(temp.resolve("invalid-selection/report.json"))).getAsJsonObject();
        assertTrue(explicit.getAsJsonArray("entries").get(0).getAsJsonObject().get("boundary").getAsString().contains("caller unspecified"));
    }

    @Test void mapValueViewNeverSubstitutesKeysForIteratedValues() throws IOException {
        Path classes = compile("ValueView", """
                import java.util.*;
                public class ValueView {
                  public static class Key { public void keyOnly() {} }
                  public static class Item { public void valueOnly() {} }
                  public static void run() throws Exception {
                    Map<Object,Object> map=new LinkedHashMap<>();
                    Collection<Object> values=map.values();
                    map.put(new Key(),new Item());
                    Object item=values.iterator().next();
                    item.getClass().getMethod("valueOnly",new Class[0]).invoke(item,new Object[0]);
                  }
                }
                """);
        ScanResult result = scan(classes);
        Set<String> reflected = targets(result, "run", Kind.REFLECTION);
        assertTrue(reflected.stream().anyMatch(t -> t.contains("ValueView$Item#valueOnly")));
        assertFalse(reflected.stream().anyMatch(t -> t.contains("ValueView$Key#")));
    }

    @Test void mutuallyExclusiveBranchBindingsStayCorrelated() throws IOException {
        Path classes = compile("Branches", """
                public class Branches {
                  public static class A { public void alpha() {} public void beta() {} }
                  public static class B { public void alpha() {} public void beta() {} }
                  public static void run(boolean flag) throws Exception {
                    Object target; String name;
                    if(flag) { target=new A(); name="alpha"; } else { target=new B(); name="beta"; }
                    target.getClass().getMethod(name,new Class[0]).invoke(target,new Object[0]);
                  }
                }
                """);
        ScanResult result = scan(classes);
        Set<String> reflected = targets(result, "run", Kind.REFLECTION);
        assertTrue(reflected.stream().anyMatch(t -> t.contains("Branches$A#alpha")));
        assertTrue(reflected.stream().anyMatch(t -> t.contains("Branches$B#beta")));
        assertFalse(reflected.stream().anyMatch(t -> t.contains("Branches$A#beta") || t.contains("Branches$B#alpha")));

        assertTrue(findings(result, "run").stream().anyMatch(f -> f.gaps().stream().anyMatch(g -> g.kind() == GapKind.CONTROL_CONDITION)));
    }

    @Test void inheritedFieldsAndWideParameterSlotsKeepTheSameReceiverBinding() throws IOException {
        Path classes = compile("Inherited", """
                public class Inherited {
                  public static class Target { public void ping() {} }
                  static class Parent { Object target; String name; Parent(Object t,String n) { target=t; name=n; } }
                  static class Child extends Parent { Child(Object t,String n) { super(t,n); } }
                  static Child make(long wide,double other,Object t,String n) { return new Child(t,n); }
                  public static void run() throws Exception {
                    Child child=make(1L,2.0,new Target(),"ping");
                    child.target.getClass().getMethod(child.name,new Class[0]).invoke(child.target,new Object[0]);
                  }
                }
                """);
        ScanResult result = scan(classes);
        assertTrue(targets(result, "run", Kind.REFLECTION).stream().anyMatch(t -> t.contains("Inherited$Target#ping")), result.limitations().toString());

    }

    @Test void knownFalseBranchIsPrunedByTheSameConditionSemantics() throws IOException {
        Path classes = compile("Prune", """
                public class Prune {
                  public static class Target { public void yes() {} public void no() {} }
                  static int zero() { return 0; }
                  public static void run() throws Exception {
                    Target target=new Target();
                    if(zero()!=0) Target.class.getMethod("no",new Class[0]).invoke(target,new Object[0]);
                    Target.class.getMethod("yes",new Class[0]).invoke(target,new Object[0]);
                  }
                }
                """);
        ScanResult result = scan(classes);
        assertTrue(targets(result, "run", Kind.REFLECTION).stream().anyMatch(t -> t.contains("#yes")));
        assertFalse(targets(result, "run", Kind.REFLECTION).stream().anyMatch(t -> t.contains("#no")));
    }

    @Test void hashCallbackUsesKeyAndSelectedJdkBytecodeNotMapValue() throws IOException {
        Path classes = compile("Keys", """
                import java.util.*;
                public class Keys {
                  static class Key { public int hashCode() { return 1; } }
                  static class Value { public int hashCode() { return 2; } }
                  public static void run() { Map<Object,Object> map=new HashMap<>(); map.put(new Key(),new Value()); }
                }
                """);
        ScanResult result = scan(classes);
        Set<String> callbacks = targets(result, "run", Kind.CONTAINER_CALLBACK);
        assertTrue(callbacks.stream().anyMatch(t -> t.contains("Keys$Key#hashCode")), result.limitations().toString());
        assertFalse(callbacks.stream().anyMatch(t -> t.contains("Keys$Value#hashCode")));
        assertTrue(result.relations().stream().filter(r -> r.kind() == Kind.CONTAINER_CALLBACK && r.target().map(t -> t.owner().equals("Keys$Key")).orElse(false))
                .anyMatch(r -> r.supports().stream().flatMap(s -> s.witnesses().stream()).anyMatch(w -> w.method().owner().equals("java/util/HashMap"))));
        Path changed=compile(Map.of("java/util/HashMap.java","""
                package java.util;
                public class HashMap<K,V> extends AbstractMap<K,V> {
                  public V put(K key,V value){return null;}
                  public Set<Map.Entry<K,V>> entrySet(){return null;}
                }
                """));
        try(Inputs input=Inputs.open(classes,List.of(changed),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            ScanResult altered=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Keys","run","()V")));
            List<Relation> callbacksAfterChange=altered.relations().stream().filter(r -> r.kind()==Kind.CONTAINER_CALLBACK && r.target().isPresent()).toList();
            assertFalse(callbacksAfterChange.isEmpty(),"an unverified structure retains the conditional candidate");
            assertTrue(callbacksAfterChange.stream().flatMap(r -> r.supports().stream()).allMatch(support -> support.evidence()==Evidence.CONDITIONAL && support.witnesses().isEmpty()
                    && support.gaps().stream().anyMatch(g -> g.kind()==GapKind.UNSUPPORTED)));
        }
    }

    @Test void absentDynamicValuesPreserveMechanismAndKeepGoalTargetsConditional() throws IOException {
        Path classes = compile("Unknown", """
                public class Unknown {
                  public static void run(Object target,String name,Class[] types,Object[] args) throws Exception {
                    target.getClass().getMethod(name,types).invoke(target,args);
                  }
                }
                """);
        ScanResult result = scan(classes);
        assertFalse(findings(result, "run").isEmpty());

        assertTrue(result.relations().stream().filter(r -> r.kind()==Kind.REFLECTION && r.target().isPresent() && r.supports().stream().anyMatch(s -> s.evidence()==Evidence.PROVEN))
                .allMatch(r -> !r.conditions().selections().isEmpty()),"local proof within a finite choice does not prove the external binding");
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.LOOKUP_TYPE && r.source().isPresent()));
        assertTrue(findings(result, "run").stream().anyMatch(f -> f.gaps().stream().anyMatch(g -> g.kind() == GapKind.DYNAMIC_TARGET)));
    }

    @Test void serializedMembershipIsConditionalAndHintsCannotPromoteProof() throws IOException {
        Path classes = compile("Serialized", """
                import java.io.*;
import java.nio.charset.StandardCharsets;
                public class Serialized {
                  static class Key implements Serializable {
                    Object target; String name; Class[] types; Object[] args;
                    public int hashCode() {
                      try { target.getClass().getMethod(name,types).invoke(target,args); }
                      catch(Exception ignored) {} return 1;
                    }
                  }
                  public static void run(ObjectInputStream in) throws Exception { in.readObject(); }
                }
                """);
        ScanResult guided = scan(classes);
        ScanResult unguided = scan(classes, Analyzer.Limits.defaults(), false);
        assertTrue(targets(guided, "run", Kind.CONTAINER_CALLBACK).stream().anyMatch(t -> t.contains("Serialized$Key#hashCode")));
        assertTrue(findings(guided, "run").stream().anyMatch(f -> f.boundary() == Kind.REFLECTION));

        for(ScanResult result:List.of(guided,unguided)) {
            assertTrue(targets(result,"run",Kind.CONTAINER_CALLBACK).stream().anyMatch(t -> t.contains("Serialized$Key#hashCode")));
            var reflection=findings(result,"run").stream().filter(f -> f.boundary()==Kind.REFLECTION).toList();
            assertFalse(reflection.isEmpty());
            for(Finding finding:reflection) {
                assertFalse(finding.gaps().isEmpty(),"a search hint cannot supply a missing serialized binding");
                if(finding.gaps().stream().noneMatch(g -> g.kind()==GapKind.BUDGET)) {
                    assertTrue(finding.gaps().stream().anyMatch(g -> g.kind()==GapKind.INPUT_BINDING));
                    assertTrue(finding.proof().stream().flatMap(use -> result.relations().get(use.relation()).supports().get(use.support()).gaps().stream())
                            .anyMatch(g -> g.kind()==GapKind.INPUT_BINDING),"the candidate must retain its actual input support");
                }
            }
        }
        assertFalse(guided.hints().isEmpty());
        assertTrue(unguided.hints().isEmpty());
    }

    private record ProofContract(Program.MethodId entry,Kind boundary,Set<Program.MethodId> targets,
                                 Set<Program.Site> witnesses,Set<GapKind> missing,Set<Program.FieldId> fields,Set<List<Atom>> literalArguments) {}
    private Set<ProofContract> signatures(ScanResult result) {
        return result.findings().stream().map(finding -> {
            Set<Integer> needed=new LinkedHashSet<>(finding.path());needed.addAll(finding.supportingRelations());
            List<Relation> relations=needed.stream().map(result.relations()::get).toList();
            Set<Program.FieldId> fields=new HashSet<>();
            for(Relation relation:relations)relation.slot().ifPresent(slot -> {if(slot instanceof Field field)fields.add(field.field());});
            return new ProofContract(finding.entry().method().id(),finding.boundary(),
                    relations.stream().flatMap(r -> r.target().stream()).collect(Collectors.toSet()),
                    finding.proof().stream().flatMap(use -> result.relations().get(use.relation()).supports().get(use.support()).witnesses().stream()).collect(Collectors.toSet()),
                    finding.gaps().stream().map(Gap::kind).collect(Collectors.toSet()),fields,
                    relations.stream().filter(r -> r.arguments().stream().allMatch(a -> a instanceof Literal || a instanceof io.just.knowledge.Values.ClassValue))
                            .map(Relation::arguments).collect(Collectors.toSet()));
        }).collect(Collectors.toSet());
    }

    @Test void budgetExhaustionRetainsFindingsAndDoesNotPretendConvergence() throws IOException {
        Path classes = compile("Budget", """
                public class Budget {
                  static class Key implements java.io.Serializable { public int hashCode() { return 1; } }
                  public static void run(java.io.ObjectInputStream input) throws Exception { input.readObject(); }
                }
                """);
        Analyzer.Limits normal = Analyzer.Limits.defaults();
        ScanResult result = scan(classes, new Analyzer.Limits(normal.contexts(), 1, normal.depth(), normal.relations(), normal.findings(), normal.alternatives()), true);
        assertEquals(Execution.TRUNCATED, result.execution());
        assertFalse(result.limitations().isEmpty());
        ScanResult relationLimit = scan(classes, new Analyzer.Limits(normal.contexts(), normal.steps(), normal.depth(), 1, normal.findings(), normal.alternatives()), true);
        assertEquals(Execution.TRUNCATED, relationLimit.execution());
        assertFalse(relationLimit.relations().isEmpty());
    }

    @Test void hierarchyBudgetIsNotReportedAsOrdinaryMissingMethod() throws IOException {
        StringBuilder source = new StringBuilder("class P260 { public void ping() {} }\n");
        for (int i = 259; i >= 0; i--) source.append("class P").append(i).append(" extends P").append(i + 1).append(" {}\n");
        source.append("public class Hierarchy { public static void run(P0 value) { value.ping(); } }\n");
        ScanResult result = scan(compile("Hierarchy", source.toString()));
        assertEquals(Execution.TRUNCATED, result.execution());
        assertTrue(result.limitations().stream().anyMatch(l -> l.contains("hierarchy query budget")));
        assertTrue(result.relations().stream().flatMap(r -> r.supports().stream().flatMap(s -> s.gaps().stream())).anyMatch(g -> g.kind()==GapKind.BUDGET && g.detail().contains("hierarchy query budget")));
        assertFalse(result.relations().stream().flatMap(r -> r.supports().stream().flatMap(s -> s.gaps().stream())).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
    }

    @Test void cliPublishesBothReportsAndPreservesExistingOutputOnFailure() throws IOException {
        Path classes = compile("Report", "public class Report { public static void run(java.io.ObjectInputStream in) throws Exception { in.readObject(); } }");
        Path output = temp.resolve("report");
        ByteArrayOutputStream stdout = new ByteArrayOutputStream(), stderr = new ByteArrayOutputStream();
        String[] command = {"--input", classes.toString(), "--jdk-home", jdk.toString(), "--mode", "component", "--output", output.toString()};
        assertEquals(0, Main.run(command, new PrintStream(stdout,true,StandardCharsets.UTF_8), new PrintStream(stderr,true,StandardCharsets.UTF_8)), stderr.toString(StandardCharsets.UTF_8));
        assertFalse(Files.readString(output.resolve("report.json")).contains("\"status\""));
        assertTrue(Files.readString(output.resolve("report.md")).contains("DESERIALIZATION"));
        String before = Files.readString(output.resolve("report.json"));
        var statistics=com.google.gson.JsonParser.parseString(before).getAsJsonObject().getAsJsonObject("statistics");
        assertTrue(Collections.disjoint(statistics.keySet(),Set.of("workers","peakComputations","localTasks","computeNanos","waitingNanos","commitNanos","staleComputations")));
        assertEquals(2, Main.run(command, new PrintStream(stdout,true,StandardCharsets.UTF_8), new PrintStream(stderr,true,StandardCharsets.UTF_8)));
        assertEquals(before, Files.readString(output.resolve("report.json")));
        assertTrue(stderr.toString(StandardCharsets.UTF_8).contains("FAILED"));
    }

    @Test void malformedInputAndInvalidOptionsFailWithContext() throws IOException {
        Path broken = temp.resolve("Broken.class");
        Files.write(broken, new byte[]{1,2,3,4});
        ByteArrayOutputStream stderr = new ByteArrayOutputStream();
        String[] command = {"--input", broken.toString(), "--jdk-home", jdk.toString(), "--mode", "component", "--output", temp.resolve("failed").toString()};
        assertEquals(2, Main.run(command, System.out, new PrintStream(stderr,true,StandardCharsets.UTF_8)));
        assertTrue(stderr.toString(StandardCharsets.UTF_8).contains("Broken.class"));
        assertFalse(Files.exists(temp.resolve("failed")));
        assertEquals(2, Main.run(new String[]{"--bogus"}, System.out, new PrintStream(stderr,true,StandardCharsets.UTF_8)));
        stderr.reset();
        assertEquals(2, Main.run(new String[]{"--workers","1"}, System.out, new PrintStream(stderr,true,StandardCharsets.UTF_8)));
        assertTrue(stderr.toString(StandardCharsets.UTF_8).contains("unknown option: --workers"));
    }

    @Test void fatJarAndNestedExplicitDependenciesUseProductionPath() throws IOException {
        Path classes = compile("Boot", """
                public class Boot {
                  public static void run() throws Exception { Library.dispatch(); }
                }
                class Library {
                  public static void dispatch() throws Exception {
                    Target.class.getMethod("ping",new Class[0]).invoke(new Target(),new Object[0]);
                  }
                }
                class Target { public void ping() {} }
                """);
        ByteArrayOutputStream dependency = new ByteArrayOutputStream();
        try (JarOutputStream jar = new JarOutputStream(dependency)) {
            member(jar, "Library.class", Files.readAllBytes(classes.resolve("Library.class")));
            member(jar, "Target.class", Files.readAllBytes(classes.resolve("Target.class")));
        }
        Path fat = temp.resolve("boot.jar");
        try (JarOutputStream jar = new JarOutputStream(Files.newOutputStream(fat))) {
            member(jar, "BOOT-INF/classes/Boot.class", Files.readAllBytes(classes.resolve("Boot.class")));
            member(jar, "BOOT-INF/lib/library.jar", dependency.toByteArray());
            // A packaging loader at the archive root is not an application entry.
            member(jar, "Loader.class", Files.readAllBytes(compile("Loader", "public class Loader { public static void bootstrap() {} }").resolve("Loader.class")));
        }
        ScanResult result = scan(fat);
        assertEquals(1, result.input().applicationClasses());
        assertEquals(3, result.input().dependencyClasses());
        assertFalse(result.entries().stream().anyMatch(e -> e.method().id().owner().equals("Loader")));
        assertTrue(targets(result, "run", Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#ping")));
        Path explicit = temp.resolve("dependency.jar"); Files.write(explicit, dependency.toByteArray());
        try (Inputs input = Inputs.open(classes.resolve("Boot.class"), List.of(explicit), jdk, Inputs.Limits.defaults())) {
            Program program = new Program(input, 20_000);
            ScanResult single = new Analyzer(program, new Mechanisms(program), Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT, true);
            assertTrue(targets(single, "run", Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#ping")));
        }
    }

    @Test void applicationEntryAnnotationsAndRequestValueReachDeserialization() throws IOException {
        Path classes = compile(Map.of(
                "org/springframework/web/bind/annotation/RestController.java", "package org.springframework.web.bind.annotation; @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface RestController {}",
                "org/springframework/web/bind/annotation/PostMapping.java", "package org.springframework.web.bind.annotation; @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface PostMapping { String[] value(); }",
                "Controller.java", """
                        @org.springframework.web.bind.annotation.RestController
                        public class Controller {
                          private Service service;
                          public Controller(Service service) { this.service=service; }
                          @org.springframework.web.bind.annotation.PostMapping("/upload")
                          public void upload(String data) throws Exception { service.decode(data); }
                          public void helper() {}
                        }
                        class Service {
                          void decode(String data) throws Exception {
                            java.io.ByteArrayInputStream bytes=new java.io.ByteArrayInputStream(java.util.Base64.getDecoder().decode(data));
                            new java.io.ObjectInputStream(bytes).readObject();
                          }
                        }
                        """));
        try (Inputs input = Inputs.open(classes, List.of(), jdk, Inputs.Limits.defaults())) {
            Program program = new Program(input, 20_000);
            ScanResult result = new Analyzer(program, new Mechanisms(program), Analyzer.Limits.defaults()).scan(EntryPoints.Mode.APPLICATION, true);
            assertEquals(1, result.entries().size());
            assertTrue(result.entries().get(0).boundary().contains("/upload"));
            assertTrue(result.findings().stream().anyMatch(f -> f.boundary() == Kind.DESERIALIZATION && f.entry().method().id().name().equals("upload")));
            Relation request=result.relations().stream().filter(r -> r.kind()==Kind.INPUT_BINDING && r.site().method().name().equals("upload") && r.detail().equals("entry parameter slot 1")).findFirst().orElseThrow();
            assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.ELEMENT_FLOW && r.arguments().contains(request.arguments().get(0))));
            assertTrue(result.findings().stream().anyMatch(f -> f.supportingRelations().contains(request.id())));

        }
    }

    @Test void multiReleaseSelectionRequiresManifestAndTargetCompatibleVersion() throws IOException {
        Path base = compile("Versioned", "public class Versioned { public static void oldMethod() {} }");
        Path modern = compile("Versioned", "public class Versioned { public static void newMethod() {} }");
        for (boolean multiRelease : List.of(false, true)) {
            Path jar = temp.resolve(multiRelease ? "mr.jar" : "plain.jar");
            Manifest manifest = new Manifest();
            manifest.getMainAttributes().putValue("Manifest-Version", "1.0");
            if (multiRelease) manifest.getMainAttributes().putValue("Multi-Release", "true");
            try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar), manifest)) {
                member(out, "Versioned.class", Files.readAllBytes(base.resolve("Versioned.class")));
                member(out, "META-INF/versions/9/Versioned.class", Files.readAllBytes(modern.resolve("Versioned.class")));
                member(out, "META-INF/versions/99/Versioned.class", Files.readAllBytes(base.resolve("Versioned.class")));
            }
            try (Inputs input = Inputs.open(jar, List.of(), jdk, Inputs.Limits.defaults())) {
                Program program = new Program(input, 20_000);
                var methods = program.targets().get(0).methods();
                assertEquals(multiRelease, methods.stream().anyMatch(m -> m.id().name().equals("newMethod")));
                assertEquals(!multiRelease, methods.stream().anyMatch(m -> m.id().name().equals("oldMethod")));
            }
        }
    }

    @Test void incompatibleReflectionArgumentsCannotCreateConcreteDispatch() throws IOException {
        Path classes = compile("Arguments", """
                public class Arguments {
                  public static class Target { public void accept(String value) {} }
                  public static void run() throws Exception {
                    Target.class.getMethod("accept",new Class[]{String.class}).invoke(new Target(),new Object[]{new Object()});
                  }
                }
                """);
        ScanResult result = scan(classes);
        assertFalse(targets(result, "run", Kind.REFLECTION).stream().anyMatch(t -> t.contains("Target#accept")));
    }

    @Test void libraryConstructorsMustNotInventNormalCompletion() throws IOException {
        Path classes=compile("ConstructorConditions", """
                public class ConstructorConditions {
                  public static class Target {public void reached(){}}
                  static void dispatch()throws Exception {Target.class.getMethod("reached",new Class[0]).invoke(new Target(),new Object[0]);}
                  public static void negative()throws Exception {new StringBuilder(-1);dispatch();}
                  public static void valid()throws Exception {new StringBuilder(0);dispatch();}
                  public static void unknown(int capacity)throws Exception {new StringBuilder(capacity);dispatch();}
                  public static void negativeList()throws Exception {new java.util.ArrayList(-1);dispatch();}
                  public static void nullString()throws Exception {new StringBuilder((String)null);dispatch();}
                  public static void caughtNegative()throws Exception {try {new StringBuilder(-1);}catch(NegativeArraySizeException expected){dispatch();}}
                  public static void validHandlerTrap()throws Exception {try {new StringBuilder(0);}catch(NegativeArraySizeException impossible){dispatch();}}
                  public static void nullBuffer()throws Exception {new java.io.ByteArrayInputStream(null);dispatch();}
                  public static void negativeMap(float factor)throws Exception {new java.util.LinkedHashMap(-1,factor,false);dispatch();}
                  public static void unverifiedHeader()throws Exception {new java.io.ObjectInputStream(new java.io.ByteArrayInputStream(new byte[0]));dispatch();}
                }
                """);
        ScanResult result=scan(classes);
        for(String entry:List.of("negative","negativeList","nullString","nullBuffer","negativeMap"))
            assertTrue(findings(result,entry).isEmpty(),entry+" cannot normally reach reflection");

        assertFalse(findings(result,"unknown").isEmpty());


        assertTrue(findings(result,"validHandlerTrap").isEmpty());
        assertFalse(findings(result,"unverifiedHeader").isEmpty());

    }

    @Test void incompleteHierarchyMustNotBecomeAProvenMissingReflectiveMethod() throws IOException {
        Path classes=compile(Map.of(
                "LookupParent.java","public class LookupParent {public void inherited(){}}",
                "LookupChild.java","""
                public class LookupChild extends LookupParent {
                  public static void run()throws Exception {LookupChild.class.getMethod("inherited",new Class[0]).invoke(new LookupChild(),new Object[0]);}
                  public static void absent()throws Exception {LookupChild.class.getMethod("absentMember",new Class[0]).invoke(new LookupChild(),new Object[0]);}
                }
                """));
        ScanResult complete=scan(classes);
        assertTrue(targets(complete,"run",Kind.REFLECTION).stream().anyMatch(t -> t.contains("LookupParent#inherited")));
        assertTrue(findings(complete,"absent").isEmpty());
        ScanResult missing=scan(classes.resolve("LookupChild.class"));
        assertTrue(missing.missingClasses().contains("LookupParent"));
        assertFalse(findings(missing,"run").isEmpty(),"unknown inherited declaration must retain the mechanism");

        assertTrue(findings(missing,"run").stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
    }

    @Test void relationArgumentsKeepTheirPositionsAndAlternativeTuples() throws IOException {
        Path classes=compile("ArgumentTuples", """
                import java.util.Set;
                public class ArgumentTuples {
                  public static void run(Set<String> values){for(String value:values)sink(value,"fixed");}
                  private static void sink(String first,String second){}
                }
                """);
        String json="""
                {"source":"ordinary unordered strings","basis":"BINDING",
                 "entry":{"owner":"ArgumentTuples","name":"run","descriptor":"(Ljava/util/Set;)V","arguments":[{"ref":"values"}]},
                 "objects":[{"id":"values","type":"java/util/HashSet","elements":["first","second"]}]}
                """;
        ScanResult result=scanBound(classes,json,new Program.MethodId("ArgumentTuples","run","(Ljava/util/Set;)V"));
        List<Relation> calls=result.relations().stream().filter(r -> r.target().map(t -> t.owner().equals("ArgumentTuples") && t.name().equals("sink")).orElse(false)).toList();
        assertFalse(calls.isEmpty());
        assertTrue(calls.stream().allMatch(r -> r.arguments().size()==2),"a two-argument method must keep two positioned arguments per binding");
        assertEquals(Set.of(List.of(new Literal("first"),new Literal("fixed")),List.of(new Literal("second"),new Literal("fixed"))),
                calls.stream().map(Relation::arguments).collect(Collectors.toSet()));
    }

    @Test void unusedStructuresCannotSpendTheReflectionInstructionBudget() throws IOException {
        Path classes=compile("LazyStructures", """
                public class LazyStructures {
                  public static class Target {public void reached(){}}
                  public static void run()throws Exception {Target.class.getMethod("reached",new Class[0]).invoke(new Target(),new Object[0]);}
                }
                """);
        try(Inputs input=Inputs.open(classes,List.of(),jdk,Inputs.Limits.defaults())) {
            Program program=new Program(input,100);
            ScanResult result=new Analyzer(program,new Mechanisms(program),Analyzer.Limits.defaults())
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("LazyStructures","run","()V")));
            assertEquals(Execution.FINISHED,result.execution(),result.limitations().toString());

        }
    }

    @Test void instructionBudgetKeepsAnAlreadyObservedCandidate() throws IOException {
        Path classes=compile("Retained", """
                public class Retained {
                  public static void first(java.io.ObjectInputStream input)throws Exception {input.readObject();}
                  public static void noise(){NOISE}
                }
                """.replace("NOISE","System.nanoTime();".repeat(100)));
        Analyzer.Limits normal=Analyzer.Limits.defaults();
        ScanResult result=scan(classes,new Analyzer.Limits(normal.contexts(),15,normal.depth(),normal.relations(),normal.findings(),normal.alternatives()),false);
        assertEquals(Execution.TRUNCATED,result.execution());
        assertTrue(findings(result,"first").stream().anyMatch(f -> f.boundary()==Kind.DESERIALIZATION));

        assertTrue(result.limitations().stream().anyMatch(l -> l.equals("scheduled instruction budget: 15") || l.startsWith("work item budget: 15;")),result.limitations().toString());
    }

    @Test void reportReferencesPreserveTypedBindingsAndResolveEveryEvidencePointer() throws IOException {
        Path classes=compile("ReferenceReport", """
                public class ReferenceReport {
                  public static class Target {public void reached(String value){}}
                  public static void run(int selected)throws Exception {if(selected!=0)return;Target.class.getMethod("reached",new Class[]{String.class}).invoke(new Target(),new Object[]{"ordinary"});}
                }
                """);
        ScanResult result=scan(classes);Path output=temp.resolve("references");Reports.write(result,output);
        var document=com.google.gson.JsonParser.parseString(Files.readString(output.resolve("report.json"))).getAsJsonObject();
        assertEquals(4,document.get("schemaVersion").getAsInt());
        var references=document.getAsJsonObject("references");
        var values=references.getAsJsonArray("values");var sites=references.getAsJsonArray("sites");
        var gaps=references.getAsJsonArray("gaps");var conditions=references.getAsJsonArray("conditions");
        Set<String> choiceKinds=new HashSet<>();
        for(var condition:conditions) {
            var choices=condition.getAsJsonObject().get("choices");
            if(choices.isJsonArray())for(var pair:choices.getAsJsonArray())
                choiceKinds.add(references.getAsJsonArray("choices").get(pair.getAsJsonArray().get(0).getAsInt()).getAsJsonObject().get("kind").getAsString());
            else assertTrue(choices.getAsJsonObject().isEmpty());
        }
        assertTrue(choiceKinds.contains("BranchKey"));
        boolean bound=false;Set<String> slotKinds=new HashSet<>();
        for(var item:document.getAsJsonArray("relations")) {
            var relation=item.getAsJsonObject();
            assertTrue(relation.get("receiver").getAsInt()>=0 && relation.get("receiver").getAsInt()<values.size());
            assertTrue(relation.get("site").getAsInt()>=0 && relation.get("site").getAsInt()<sites.size());
            assertTrue(relation.get("conditions").getAsInt()>=0 && relation.get("conditions").getAsInt()<conditions.size());
            for(var support:relation.getAsJsonArray("supports"))for(var gap:support.getAsJsonObject().getAsJsonArray("gaps"))assertTrue(gap.getAsInt()>=0 && gap.getAsInt()<gaps.size());
            for(var argument:relation.getAsJsonArray("arguments"))assertTrue(argument.getAsInt()>=0 && argument.getAsInt()<values.size());
            if(!relation.get("slot").isJsonNull())slotKinds.add(relation.getAsJsonObject("slot").get("kind").getAsString());
            if(relation.has("target") && !relation.get("target").isJsonNull() && relation.getAsJsonObject("target").get("name").getAsString().equals("reached")) {
                var arguments=relation.getAsJsonArray("arguments");assertEquals(1,arguments.size());
                var literal=values.get(arguments.get(0).getAsInt()).getAsJsonObject();
                assertEquals("Literal",literal.get("kind").getAsString());
                assertEquals("ordinary",literal.getAsJsonObject("value").get("value").getAsString());bound=true;
            }
        }
        assertTrue(bound);
        assertTrue(slotKinds.containsAll(Set.of("Length","Index")));
        assertTrue(Files.readString(output.resolve("report.md")).contains("Evidence references"));
    }

    private void member(JarOutputStream jar, String name, byte[] bytes) throws IOException {
        jar.putNextEntry(new JarEntry(name)); jar.write(bytes); jar.closeEntry();
    }

    @Test void inputBudgetPreservesAlreadyReadClassesAndReportsTruncation() throws IOException {
        Path classes = compile("Small", "public class Small { public static int run() { return 7; } }");
        byte[] bytes = Files.readAllBytes(classes.resolve("Small.class"));
        Path jar = temp.resolve("bounded.jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            member(out, "Small.class", bytes); member(out, "large-resource.bin", new byte[8192]);
        }
        try (Inputs input = Inputs.open(jar, List.of(), jdk, new Inputs.Limits(bytes.length + 1024L, 100, 100, 1, 16384))) {
            assertEquals(1, input.targetClasses().size());
            assertFalse(input.summary().limitations().isEmpty());
        }
    }
}
