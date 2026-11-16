package io.just;

import io.just.analysis.*;
import io.just.input.Inputs;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.nio.file.Files;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class ConstructionTest {
    @TempDir Path temp;
    private ScanResult scan(Path classes,String entry,String descriptor)throws Exception {
        return scan(classes,entry,descriptor,Analyzer.Limits.defaults());
    }
    private ScanResult scan(Path classes,String entry,String descriptor,Analyzer.Limits limits)throws Exception {
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            return new Analyzer(program,new Mechanisms(program),limits)
                    .scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("Construction",entry,descriptor)));
        }
    }
    private Set<String> targets(ScanResult result){Set<String> names=new HashSet<>();result.relations().forEach(r -> r.target().filter(t -> t.owner().equals("Construction")).ifPresent(t -> names.add(t.name())));return names;}
    private Path fixture()throws Exception {
        return BytecodeFixtures.compile(temp,8,Map.of("Construction.java","""
                import java.lang.reflect.*;import java.io.*;
                public class Construction {
                  static void hit(){}static void wrong(){}static void good(){}
                  public static class Product {static String prefix=prefix();String name;static String prefix(){return "h";}public Product(){name=prefix+"it";}public Product(String first,String second){name=first+second;}public Product(Integer wrong){name="wrong";}public String name(){return name;}}
                  public static class Primitive {int count;public Primitive(int count){this.count=count;}public int count(){return count;}}
                  public static class Flag {boolean enabled;public Flag(boolean enabled){this.enabled=enabled;}}
                  public static class Small {int value;public Small(byte value){this.value=value;}public Small(short value){this.value=value;}public Small(char value){this.value=value;}}
                  public static class Private {private Private(){}}
                  public static abstract class Abstract {public Abstract(){}}
                  public static class Base {public Base(String text){}}
                  public static class Child extends Base {public Child(){super("");}}
                  public static class Throwing {public Throwing()throws IOException {throw new IOException();}}
                  public static class Broken {static int value=breakIt();static int breakIt(){throw new IllegalStateException();}public Broken(){}}
                  public static class MissingParent extends Error{}public static class MissingChild extends MissingParent{}
                  public static class MissingInit {static int value=breakIt();static int breakIt(){throw new MissingChild();}public MissingInit(){}}
                  static void use(Product value)throws Exception {Construction.class.getDeclaredMethod(value.name()).invoke(null);}
                  public static void bound()throws Exception {Class<?>[] types={String.class,String.class};Constructor<Product> ctor=Product.class.getConstructor(types);types[0]=Integer.class;use(ctor.newInstance("h","it"));}
                  public static void legacy()throws Exception {use(Product.class.newInstance());}
                  public static void primitive()throws Exception {Primitive p=Primitive.class.getConstructor(int.class).newInstance(7);if(p.count()==7)good();else wrong();}
                  public static void flagFalse()throws Exception {Flag f=Flag.class.getConstructor(boolean.class).newInstance(false);if(f.enabled)wrong();else good();}
                  public static void flagTrue()throws Exception {Flag f=Flag.class.getConstructor(boolean.class).newInstance(true);if(f.enabled)good();else wrong();}
                  public static void boxedByte()throws Exception {Small s=Small.class.getConstructor(byte.class).newInstance((byte)7);if(s.value==7)good();else wrong();}
                  public static void boxedShort()throws Exception {Small s=Small.class.getConstructor(short.class).newInstance((short)8);if(s.value==8)good();else wrong();}
                  public static void boxedChar()throws Exception {Small s=Small.class.getConstructor(char.class).newInstance('x');if(s.value=='x')good();else wrong();}
                  public static void access()throws Exception {Constructor<Private> ctor=Private.class.getDeclaredConstructor();try{ctor.newInstance();wrong();}catch(IllegalAccessException expected){good();}}
                  public static void override()throws Exception {Constructor<Private> ctor=Private.class.getDeclaredConstructor();ctor.setAccessible(true);ctor.newInstance();good();}
                  public static void abstractType()throws Exception {Constructor<Abstract> ctor=Abstract.class.getConstructor();try{ctor.newInstance();wrong();}catch(InstantiationException expected){good();}}
                  public static void absent()throws Exception {try{Child.class.getConstructor(String.class);wrong();}catch(NoSuchMethodException expected){good();}}
                  public static void interfaceType()throws Exception {try{Runnable.class.newInstance();wrong();}catch(InstantiationException expected){good();}}
                  public static void concrete()throws Exception {try{Product.class.getDeclaredConstructor().newInstance();good();}catch(InstantiationException impossible){wrong();}}
                  public static void arguments()throws Exception {Constructor<Product> ctor=Product.class.getConstructor(String.class,String.class);try{ctor.newInstance("h",8);wrong();}catch(IllegalArgumentException expected){good();}}
                  public static void primitiveNull()throws Exception {Constructor<Primitive> ctor=Primitive.class.getConstructor(int.class);try{ctor.newInstance(new Object[]{null});wrong();}catch(IllegalArgumentException expected){good();}}
                  public static void primitiveNarrowing()throws Exception {Constructor<Primitive> ctor=Primitive.class.getConstructor(int.class);Object[] args={7L};try{ctor.newInstance(args);wrong();}catch(IllegalArgumentException expected){good();}}
                  public static void reflectedThrow()throws Exception {Constructor<Throwing> ctor=Throwing.class.getConstructor();try{ctor.newInstance();wrong();}catch(InvocationTargetException expected){if(expected.getCause() instanceof IOException)good();else wrong();}}
                  public static void legacyThrow()throws Exception {try{Throwing.class.newInstance();wrong();}catch(Exception expected){if(expected instanceof IOException)good();else wrong();}}
                  public static void initialization()throws Exception {Constructor<Broken> ctor=Broken.class.getConstructor();try{ctor.newInstance();wrong();}catch(ExceptionInInitializerError expected){good();}}
                  public static void missingInitialization()throws Exception {Constructor<MissingInit> ctor=MissingInit.class.getConstructor();try{ctor.newInstance();wrong();}catch(MissingChild maybe){good();}catch(ExceptionInInitializerError maybe){hit();}}
                  public static Object unknown(Class<?> type)throws Exception {return type.getConstructor().newInstance();}
                }
                """));
    }
    @Test void signaturesAreSnapshotsAndConstructorWritesReachLaterCalls()throws Exception {
        Path classes=fixture();
        for(String entry:List.of("bound","legacy"))assertEquals(Set.of("use","hit"),targets(scan(classes,entry,"()V")),entry);
        assertEquals(Set.of("good"),targets(scan(classes,"primitive","()V")));
    }
    @Test void boxedConstructorArgumentsKeepTheirPrimitiveValues()throws Exception {
        Path classes=fixture();
        for(String entry:List.of("flagFalse","flagTrue","boxedByte","boxedShort","boxedChar"))assertEquals(Set.of("good"),targets(scan(classes,entry,"()V")),entry);
    }
    @Test void constructorsDoNotInheritAndInvalidAccessTypesOrArgumentsThrow()throws Exception {
        Path classes=fixture();
        for(String entry:List.of("access","abstractType","absent","interfaceType","arguments","primitiveNull","primitiveNarrowing"))assertEquals(Set.of("good"),targets(scan(classes,entry,"()V")),entry);
        assertEquals(Set.of("good"),targets(scan(classes,"concrete","()V")),"a known concrete constructor does not throw InstantiationException");
        var overridden=scan(classes,"override","()V");assertTrue(targets(overridden).contains("good"));
        assertTrue(overridden.relations().stream().filter(r -> r.target().filter(t -> t.name().equals("good")).isPresent()).anyMatch(r -> r.supports().stream().allMatch(s -> !s.gaps().isEmpty())));
    }
    @Test void constructionAndInitializationExceptionsKeepTheirDifferentContracts()throws Exception {
        Path classes=fixture();
        for(String entry:List.of("reflectedThrow","legacyThrow","initialization")) {
            var result=scan(classes,entry,"()V");
            assertEquals(Set.of("good"),targets(result),entry);
        }
    }
    @Test void unknownClassesStayUnboundAndMissingClassesKeepDependencyReasons()throws Exception {
        Path classes=fixture();var unknown=scan(classes,"unknown","(Ljava/lang/Class;)Ljava/lang/Object;");
        assertTrue(unknown.inputRequirements().stream().anyMatch(r -> Set.of(NeedKind.CLASS_NAME,NeedKind.RECEIVER_TYPE).contains(r.needed().kind())));
        assertFalse(unknown.relations().stream().flatMap(r -> r.target().stream()).anyMatch(t -> t.name().equals("<init>") && t.owner().startsWith("Construction$")));
        Files.delete(classes.resolve("Construction$Product.class"));
        var missing=scan(classes,"bound","()V");
        assertTrue(missing.findings().stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY));
    }
    @Test void constructionDepthBudgetStaysOnDownstreamEvidence()throws Exception {
        var result=scan(fixture(),"bound","()V",new Analyzer.Limits(50,5000,1,100,20,16));
        assertEquals(ScanResult.Execution.TRUNCATED,result.execution());
        assertTrue(result.findings().stream().flatMap(f -> f.gaps().stream()).anyMatch(g -> g.kind()==GapKind.BUDGET));
        assertTrue(result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Construction") && t.name().equals("hit")).isPresent())
                .flatMap(r -> r.supports().stream()).allMatch(support -> support.gaps().stream().anyMatch(g -> g.kind()==GapKind.BUDGET)));
    }
    @Test void missingInitializerExceptionHierarchyDoesNotDiscardTheDirectErrorAlternative()throws Exception {
        Path classes=fixture();Files.delete(classes.resolve("Construction$MissingParent.class"));
        var result=scan(classes,"missingInitialization","()V");
        assertTrue(targets(result).contains("good"));
        assertTrue(result.relations().stream().filter(r -> r.target().filter(t -> t.owner().equals("Construction") && t.name().equals("good")).isPresent())
                .flatMap(r -> r.supports().stream()).allMatch(support -> support.gaps().stream().anyMatch(g -> g.kind()==GapKind.MISSING_DEPENDENCY)));
        assertFalse(targets(result).contains("wrong"));
    }
    @Test void privateConstructorsAllowVerifiedJava17Nestmates()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Construction.java","""
                public class Construction {
                  private static class Member {String name;private Member(){name="hit";}}
                  static void good(){}static void wrong(){}
                  public static void nested()throws Exception {Member member=Member.class.getDeclaredConstructor().newInstance();if(member.name.equals("hit"))good();else wrong();}
                }
                """));
        assertEquals(Set.of("good"),targets(scan(classes,"nested","()V")));
    }
}
