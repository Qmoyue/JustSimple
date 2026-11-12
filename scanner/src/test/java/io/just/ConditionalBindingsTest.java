package io.just;

import io.just.analysis.*;
import io.just.analysis.ScanResult.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

/** Source is compiled and read; no fixture class or reflective target is executed. */
class ConditionalBindingsTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String entry,String descriptor)throws Exception {
        return scan(classes,entry,descriptor,Analyzer.Limits.defaults());
    }
    private ScanResult scan(Path classes,String entry,String descriptor,Analyzer.Limits limits)throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            Program.MethodId method=new Program.MethodId("Choices",entry,descriptor);
            Path reference=ReferenceFixtures.write(temp.resolve("bindings-reference.json"),program,method);
            return new Analyzer(program,new Mechanisms(program,Catalog.read(reference)),limits).scan(EntryPoints.Mode.COMPONENT,true,Set.of(method));
        }
    }
    @Test void aFinitePrefixNarrowsTheMemberAndProjectsTheRequiredSuffix()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  public static void getGood(String command)throws Exception {Runtime.getRuntime().exec(command);}
                  public static void other(String command)throws Exception {Runtime.getRuntime().exec(command);}
                  public static void run(String suffix,String command)throws Exception {Choices.class.getMethod("get"+suffix,String.class).invoke(null,new Object[]{command});}
                  public static void wrong(String suffix,String command)throws Exception {Choices.class.getMethod("absent"+suffix,String.class).invoke(null,new Object[]{command});}
                }
                """));
        ScanResult result=scan(classes,"run","(Ljava/lang/String;Ljava/lang/String;)V");
        assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.name().equals("getGood")).isPresent()));
        assertFalse(result.relations().stream().anyMatch(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.name().equals("other")).isPresent()));
        assertTrue(result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.METHOD_NAME && r.source().filter(s -> s.parameterSlot()==0).isPresent() && r.needed().choices().equals(List.of(new Literal("Good")))));
        assertTrue(scan(classes,"wrong","(Ljava/lang/String;Ljava/lang/String;)V").findings().stream().noneMatch(f -> f.boundary()==Kind.IMPACT));
    }
    @Test void oneSourceCannotSelectTwoNamesButSeparateParameterSlotsRemainIndependent()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  public static class First {public static void alpha(){}}
                  public static class Second {public static void beta(String command)throws Exception {Runtime.getRuntime().exec(command);}}
                  public static void same(String name,String command)throws Exception {First.class.getMethod(name).invoke(null);Second.class.getMethod(name,String.class).invoke(null,new Object[]{command});}
                  public static void separate(String first,String second,String command)throws Exception {First.class.getMethod(first).invoke(null);Second.class.getMethod(second,String.class).invoke(null,new Object[]{command});}
                }
                """));
        ScanResult same=scan(classes,"same","(Ljava/lang/String;Ljava/lang/String;)V");
        assertTrue(same.findings().stream().noneMatch(f -> f.boundary()==Kind.IMPACT),"the same string cannot simultaneously be alpha and beta");
        assertTrue(same.findings().stream().anyMatch(f -> f.boundary()==Kind.REFLECTION),"refuting the continuation must retain the earlier local capability");
        ScanResult separate=scan(classes,"separate","(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V");
        Finding impact=separate.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).findFirst().orElseThrow();
        assertTrue(impact.conditions().selections().entrySet().stream().anyMatch(e -> e.getKey() instanceof InputSource s && s.parameterSlot()==0 && e.getValue().value().equals(new Literal("alpha"))));
        assertTrue(impact.conditions().selections().entrySet().stream().anyMatch(e -> e.getKey() instanceof InputSource s && s.parameterSlot()==1 && e.getValue().value().equals(new Literal("beta"))));
        io.just.knowledge.Values.Path combined=impact.conditions();
        for(ProofUse use:impact.proof())combined=combined.and(separate.relations().get(use.relation()).conditions()).orElseThrow();
    }
    @Test void aKnownForNameInitializationFailureBlocksOnlyItsNormalContinuation()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  public static class Broken {static int value=fail();static int fail(){throw new IllegalStateException();}}
                  static void good(){}static void wrong(){}
                  public static void run()throws Exception {try{Class.forName("Choices$Broken");wrong();}catch(ExceptionInInitializerError expected){good();}}
                }
                """));
        ScanResult result=scan(classes,"run","()V");
        assertTrue(result.relations().stream().anyMatch(r -> r.target().filter(t -> t.name().equals("good")).isPresent()));
        assertTrue(result.relations().stream().noneMatch(r -> r.target().filter(t -> t.name().equals("wrong")).isPresent()));
    }
    @Test void aNullSignatureElementAndNullNameReachTheirDifferentActualHandlers()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  public static void take(String value){}static void signatureFailure(){}static void nameFailure(){}static void wrong(){}
                  public static void run()throws Exception {
                    try{Choices.class.getMethod("take",new Class[]{null});wrong();}
                    catch(NoSuchMethodException expected){signatureFailure();}catch(NullPointerException wrongType){wrong();}
                    try{Choices.class.getMethod(null,new Class[0]);wrong();}
                    catch(NullPointerException expected){nameFailure();}
                  }
                }
                """));
        ScanResult result=scan(classes,"run","()V");
        assertTrue(result.relations().stream().anyMatch(r -> r.target().filter(t -> t.name().equals("signatureFailure")).isPresent()));
        assertTrue(result.relations().stream().anyMatch(r -> r.target().filter(t -> t.name().equals("nameFailure")).isPresent()));
        assertTrue(result.relations().stream().noneMatch(r -> r.target().filter(t -> t.name().equals("wrong")).isPresent()));
    }
    @Test void aPartialSignatureRetainsItsOriginalClassNameAndLookupSnapshotButArgumentsUseCurrentWrites()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  public static void take(String command)throws Exception {Runtime.getRuntime().exec(command);}
                  public static void run(String type,String command)throws Exception {
                    Class<?>[] signature={Class.forName(type)};
                    java.lang.reflect.Method method=Choices.class.getMethod("take",signature);
                    signature[0]=Integer.class;method.invoke(null,new Object[]{command});
                  }
                  public static void overwritten(String type,String command)throws Exception {
                    Class<?>[] signature={Class.forName(type)};Object[] arguments={command};
                    java.lang.reflect.Method method=Choices.class.getMethod("take",signature);
                    arguments[0]=new Object();method.invoke(null,arguments);
                  }
                }
                """));
        ScanResult kept=scan(classes,"run","(Ljava/lang/String;Ljava/lang/String;)V");
        assertTrue(kept.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT),"mutating the lookup array must not change the already captured Method");
        assertTrue(kept.inputRequirements().stream().anyMatch(r -> r.needed().kind()==NeedKind.CLASS_NAME && r.source().filter(s -> s.parameterSlot()==0 && s.path().isEmpty()).isPresent()
                && r.needed().choices().equals(List.of(new Literal("java.lang.String")))));
        assertTrue(scan(classes,"overwritten","(Ljava/lang/String;Ljava/lang/String;)V").findings().stream().noneMatch(f -> f.boundary()==Kind.IMPACT),"an old conditional argument cannot hide the current incompatible array element");
    }
    @Test void aNonserializableDecodedReceiverKeepsItsProducerFrontierWithoutInventingTheCall()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  public static final class Product {public void go()throws Exception {Runtime.getRuntime().exec("command");}}
                  public static Product factory(){return new Product();}
                  public static void run(java.io.ObjectInputStream in)throws Exception {Object value=in.readObject();value.getClass().getMethod("go").invoke(value);}
                }
                """));
        ScanResult result=scan(classes,"run","(Ljava/io/ObjectInputStream;)V");
        assertTrue(result.findings().stream().anyMatch(f -> f.gaps().stream().anyMatch(g -> g.detail().contains("actual receiver producer") || g.detail().contains("cannot directly supply this nonserializable runtime class"))));
        assertTrue(result.inputRequirements().stream().anyMatch(r -> r.needed().descriptor().equals("LChoices$Product;") && r.needed().reason().contains("factory")));
        assertTrue(result.demandFrontier().stream().anyMatch(f -> f.candidates().stream().anyMatch(s -> s.method().name().equals("factory"))),"existing constructors/factories remain source candidates, without an invented return binding");
        assertTrue(result.relations().stream().noneMatch(r -> r.target().filter(t -> t.owner().equals("Choices$Product") && t.name().equals("go")).isPresent()));
    }
    @Test void serializableRuntimeImplementationsKeepInheritedDefaultsAndTheirActualOverride()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  public interface Action {default void fire(String command)throws Exception {Runtime.getRuntime().exec(command);}}
                  public interface Marker {}
                  public static final class First implements Action,java.io.Serializable {public void fire(String command){}}
                  public static final class Second implements Action,Marker,java.io.Serializable {}
                  public static void run(java.io.ObjectInputStream in,String command)throws Exception {Object value=in.readObject();value.getClass().getMethod("fire",String.class).invoke(value,new Object[]{command});}
                  public static void typed(Second value,String command)throws Exception {value.getClass().getMethod("fire",String.class).invoke(value,new Object[]{command});}
                  public static void mixed(Marker value,String command)throws Exception {value.getClass().getMethod("fire",String.class).invoke(value,new Object[]{command});}
                  public static void exact(Marker value,String command)throws Exception {Marker.class.getMethod("fire",String.class).invoke(value,new Object[]{command});}
                }
                """));
        ScanResult decoded=scan(classes,"run","(Ljava/io/ObjectInputStream;Ljava/lang/String;)V");
        assertTrue(decoded.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT));
        assertTrue(decoded.relations().stream().anyMatch(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.owner().equals("Choices$First") && t.name().equals("fire")).isPresent()));
        assertTrue(decoded.relations().stream().filter(r -> r.kind()==Kind.REFLECTION && r.target().filter(t -> t.owner().equals("Choices$Action") && t.name().equals("fire")).isPresent())
                .allMatch(r -> r.receiver() instanceof ObjectValue object && object.type().equals("Choices$Second")),"the default body cannot borrow the instance with an overriding implementation");
        assertTrue(scan(classes,"typed","(LChoices$Second;Ljava/lang/String;)V").findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT),"the declaring interface and concrete getClass result have different types");
        assertTrue(scan(classes,"mixed","(LChoices$Marker;Ljava/lang/String;)V").findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT),"unrelated interfaces can have the same actual implementation");
        assertTrue(scan(classes,"exact","(LChoices$Marker;Ljava/lang/String;)V").findings().stream().noneMatch(f -> f.boundary()==Kind.IMPACT),"an exact lookup on Marker itself still has no fire member");
    }
    @Test void modeledLambdaAndProxyReceiversKeepTheirDispatchWhenArgumentsRemainExternal()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  public interface Action {void fire(String command)throws Exception;}
                  public static class Handler implements java.lang.reflect.InvocationHandler {
                    public Object invoke(Object receiver,java.lang.reflect.Method method,Object[] values)throws Exception {
                      Runtime.getRuntime().exec((String)values[0]);return null;
                    }
                  }
                  public static void lambda(Object[] arguments)throws Exception {
                    Action action=command -> {Runtime.getRuntime().exec(command);};
                    Action.class.getMethod("fire",String.class).invoke(action,arguments);
                  }
                  public static void proxy(Object[] arguments)throws Exception {
                    Action action=(Action)java.lang.reflect.Proxy.newProxyInstance(Choices.class.getClassLoader(),new Class[]{Action.class},
                      new Handler());
                    Action.class.getMethod("fire",String.class).invoke(action,arguments);
                  }
                }
                """));
        for(String entry:List.of("lambda","proxy")) {
            ScanResult result=scan(classes,entry,"([Ljava/lang/Object;)V");
            assertTrue(result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT),entry+" has an actual modeled producer, so only its arguments remain conditional");
            assertTrue(result.inputRequirements().stream().noneMatch(r -> r.needed().kind()==NeedKind.RECEIVER_PRODUCER && r.needed().descriptor().equals("LChoices$Action;")));
        }
    }
    @Test void noiseOverloadsDoNotStarveAnotherMemberOrHideTheOutputFrontier()throws Exception {
        StringBuilder overloads=new StringBuilder();
        for(int index=0;index<80;index++)overloads.append("public static final class N").append(index).append("{} public static void a(N").append(index).append(" value){}\n");
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                public class Choices {
                  OVERLOADS
                  public static void z(String command)throws Exception {Runtime.getRuntime().exec(command);}
                  public static void run(String name,Class<?>[] types,Object[] args)throws Exception {Choices.class.getMethod(name,types).invoke(null,args);}
                  public static void exact(Class<?>[] types,Object[] args)throws Exception {Choices.class.getMethod("z",types).invoke(null,args);}
                }
                """.replace("OVERLOADS",overloads)));
        Analyzer.Limits budgets=new Analyzer.Limits(5000,200000,20,30000,8,64);
        ScanResult unknown=scan(classes,"run","(Ljava/lang/String;[Ljava/lang/Class;[Ljava/lang/Object;)V",budgets);
        assertTrue(unknown.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT),"a later independent member must survive both target and display limits");
        assertTrue(unknown.breakpoints().stream().anyMatch(p -> p.reason()==GapKind.BUDGET && !p.knownRelations().isEmpty() && p.detail().contains("observed variants")));
        ScanResult exact=scan(classes,"exact","([Ljava/lang/Class;[Ljava/lang/Object;)V",budgets);
        assertTrue(exact.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).anyMatch(f -> f.gaps().stream().noneMatch(g -> g.kind()==GapKind.BUDGET)),"constraints take effect before unrelated overloads consume the target budget");
    }
    @Test void anUnresolvedMemberCannotProvideTheNullReturnOfAKnownNonNullMember()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
            public class Choices extends Missing {
              public static Class<?> load()throws Exception {return Class.forName("java.lang.Runtime");}
              public static void run(String name,Class<?>[] types)throws Exception {
                Object value=Choices.class.getMethod(name,types).invoke(null,new Object[0]);
                if(value==null)Runtime.getRuntime().exec("nullable-frontier");
                else ((Runtime)((Class<?>)value).getMethod("getRuntime",new Class[0]).invoke(null,new Object[0])).exec("known-member");
              }
            }
            ""","Missing.java","public class Missing {}"));
        java.nio.file.Files.delete(classes.resolve("Missing.class"));
        ScanResult result=scan(classes,"run","(Ljava/lang/String;[Ljava/lang/Class;)V");
        var withLoad=result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT && f.proof().stream().anyMatch(use -> result.relations().get(use.relation()).target().filter(id -> id.owner().equals("Choices") && id.name().equals("load")).isPresent())).toList();
        assertTrue(withLoad.stream().anyMatch(f -> result.relations().get(f.path().get(f.path().size()-1)).arguments().contains(new Literal("known-member"))),result.limitations().toString());
        assertTrue(withLoad.stream().noneMatch(f -> result.relations().get(f.path().get(f.path().size()-1)).arguments().contains(new Literal("nullable-frontier"))));
        assertTrue(result.breakpoints().stream().anyMatch(point -> point.reason()==GapKind.MISSING_DEPENDENCY));
    }
    @Test void aNativeReplacementFollowsItsFactoryAndHelperReturnWithoutBindingTheProductAsInput()throws Exception {
        for(boolean produce:List.of(true,false)) {
            Path classes=BytecodeFixtures.compile(temp,8,Map.of("Choices.java","""
                    public class Choices {
                      public static class Carrier implements java.io.Serializable {
                        String command;private Object readResolve(){return RETURN;}
                      }
                      public static final class Product {String command;Product(String command){this.command=command;}public String command(){return command;}}
                      static Product factory(String command){return helper(command);}
                      static Product helper(String command){return new Product(command);}
                      public static void run(java.io.ObjectInputStream in)throws Exception {Product value=(Product)in.readObject();Runtime.getRuntime().exec(value.command());}
                    }
                    """.replace("RETURN",produce?"factory(command)":"null")));
            ScanResult result=scan(classes,"run","(Ljava/io/ObjectInputStream;)V");
            boolean connected=result.findings().stream().filter(f -> f.boundary()==Kind.IMPACT).anyMatch(f -> {
                Set<String> calls=new HashSet<>();
                for(ProofUse use:f.proof())result.relations().get(use.relation()).target().ifPresent(id -> calls.add(id.name()));
                return calls.containsAll(Set.of("readResolve","factory","helper","<init>","exec"));
            });
            assertEquals(produce,connected,"only the actual readResolve return may supply this nonserializable product");
            assertTrue(result.inputRequirements().stream().noneMatch(r -> r.needed().kind()==NeedKind.SERIALIZED_MEMBERS && r.needed().descriptor().equals("LChoices$Product;")));
        }
    }
}
