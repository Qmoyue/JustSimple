package io.just.knowledge;

import io.just.BytecodeFixtures;
import io.just.ReferenceFixtures;
import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class LocalContractsTest {
    @TempDir Path temp;
    private Inputs input() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Empty.java","public class Empty {}"));
        return Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults());
    }
    private final Site site=new Site(new MethodId("Empty","run","()V"),3,1,"source fixture");
    private Invocation call(MethodId target,Atom receiver,List<Atom> arguments) {
        return new Invocation(new Call(site,target,org.objectweb.asm.Opcodes.INVOKEVIRTUAL,new Sources(Set.of()),List.of()),receiver,arguments,new ObjectValue(99,"java/lang/Object",false,"result"),Values.Path.EMPTY);
    }
    @Test void reflectionReceivesTheConfiguredArrayBudget()throws Exception {
        try(Inputs input=input()) {
            Program program=new Program(input,20_000);ObjectValue signature=new ObjectValue(1,"[Ljava/lang/Class;",true,"signature",false);
            Bindings heap=(object,slot) -> slot instanceof Length?Value.of(new Literal(65)):slot instanceof Index?Value.of(new ClassValue("Ljava/lang/String;",true)):Value.BOTTOM;
            Invocation lookup=call(new MethodId("java/lang/Class","getDeclaredMethod","(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;"),new ClassValue("LEmpty;",true),List.of(new Literal("missing"),signature));
            Local limited=new Mechanisms(program,Catalog.empty(),Set.of(),64).apply(lookup,heap).orElseThrow();
            Local expanded=new Mechanisms(program,Catalog.empty(),Set.of(),128).apply(lookup,heap).orElseThrow();
            assertTrue(limited.effects().stream().filter(Observe.class::isInstance).map(Observe.class::cast).flatMap(o -> o.gaps().stream()).anyMatch(g -> g.kind()==GapKind.BUDGET));
            assertTrue(expanded.effects().stream().noneMatch(Observe.class::isInstance));
            assertTrue(expanded.effects().stream().filter(Conditional.class::isInstance).map(Conditional.class::cast)
                    .flatMap(choice -> choice.local().effects().stream()).anyMatch(Raise.class::isInstance));
        }
    }
    @Test void fieldCollectionLimitsMembersWithoutChangingTheKnownArrayLength()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("TwoFields.java","public class TwoFields {public int first;private int second;}"));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            Invocation request=call(new MethodId("java/lang/Class","getDeclaredFields","()[Ljava/lang/reflect/Field;"),new ClassValue("LTwoFields;",true),List.of());
            for(int budget:List.of(1,2)) {
                Local result=new Mechanisms(program,Catalog.empty(),Set.of(),budget).apply(request,(object,slot) -> Value.BOTTOM).orElseThrow();
                assertTrue(result.effects().stream().filter(Write.class::isInstance).map(Write.class::cast).filter(write -> write.slot() instanceof Length)
                        .flatMap(write -> write.value().alternatives().stream()).anyMatch(bound -> bound.atom().equals(new Literal(2))));
                boolean frontier=result.effects().stream().filter(Observe.class::isInstance).map(Observe.class::cast)
                        .flatMap(observation -> observation.gaps().stream()).anyMatch(gap -> gap.kind()==GapKind.BUDGET);
                assertEquals(budget==1,frontier);
            }
        }
    }
    @Test void reflectiveMemberFrontiersExpandWithoutFalseCutoffsAtTheExactLimit()throws Exception {
        StringBuilder source=new StringBuilder("public class Many {");
        for(int i=0;i<6;i++) {
            source.append("public Many(");
            for(int p=0;p<i;p++){if(p>0)source.append(',');source.append("int p").append(p);}
            source.append("){} public static void method").append(i).append("(){}");
        }
        source.append('}');
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Many.java",source.toString()));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);ClassValue owner=new ClassValue("LMany;",true);
            Invocation constructors=call(new MethodId("java/lang/Class","getDeclaredConstructor","([Ljava/lang/Class;)Ljava/lang/reflect/Constructor;"),owner,List.of(new Unknown("signature")));
            Reflected reflected=new Reflected(owner,new Unknown("name"),new Unknown("signature"),true,site);
            Invocation methods=call(Reflection.INVOKE,reflected,List.of(new Literal(null),new Literal(null)));
            for(int budget:List.of(4,6,8)) {
                Mechanisms mechanisms=new Mechanisms(program,Catalog.empty(),Set.of(),budget);
                for(Invocation request:List.of(constructors,methods)) {
                    Local result=mechanisms.apply(request,(object,slot) -> Value.BOTTOM).orElseThrow();
                    assertEquals(Math.min(6,budget),result.effects().stream().filter(Alternative.class::isInstance).map(Alternative.class::cast).filter(choice -> choice.selection()>=0).count(),request.call().target().toString());
                    boolean frontier=result.effects().stream().filter(Observe.class::isInstance).map(Observe.class::cast)
                            .flatMap(observation -> observation.gaps().stream()).anyMatch(gap -> gap.kind()==GapKind.BUDGET);
                    assertEquals(budget<6,frontier,"only omitted member candidates mark the result truncated");
                }
            }
        }
    }
    @Test void reflectiveSignatureAndArgumentProductsRespectTheSharedBudget()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Overloads.java","""
                public class Overloads {
                  public static void accept(Object value){}
                  public static void accept(String value){}
                }
                """));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            ObjectValue types=new ObjectValue(1,"[Ljava/lang/Class;",true,"types",false),args=new ObjectValue(2,"[Ljava/lang/Object;",true,"args",false);
            Reflected method=new Reflected(new ClassValue("LOverloads;",true),new Literal("accept"),types,true,site);
            Invocation invoke=call(Reflection.INVOKE,method,List.of(new Literal(null),args));
            Bindings heap=(object,slot) -> {
                if(slot instanceof Length)return Value.of(new Literal(1));
                if(!(slot instanceof Index))return Value.BOTTOM;
                if(object.equals(types))return Value.of(new ClassValue("Ljava/lang/Object;",true)).merge(Value.of(new ClassValue("Ljava/lang/String;",true)));
                return Value.of(new Literal("a")).merge(Value.of(new Literal("b"))).merge(Value.of(new Literal("c")));
            };
            for(int budget:List.of(4,6)) {
                Local result=new Mechanisms(program,Catalog.empty(),Set.of(),budget).apply(invoke,heap).orElseThrow();
                List<Conditional> choices=result.effects().stream().filter(Conditional.class::isInstance).map(Conditional.class::cast).toList();
                assertEquals(Math.min(6,budget),choices.stream().filter(choice -> choice.gaps().stream().noneMatch(gap -> gap.kind()==GapKind.BUDGET)).count());
                assertEquals(budget<6,choices.stream().flatMap(choice -> choice.gaps().stream()).anyMatch(gap -> gap.kind()==GapKind.BUDGET));
            }
        }
    }
    @Test void rankingMetadataLimitKeepsAllSemanticCandidatesAndReportsItsOwnIssue()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("RankSource.java","""
                public class RankSource {
                  static class Box {void accept(Object value){}}
                  static void reference(Box box){box.accept(box);}
                }
                """));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);
            Path reference=ReferenceFixtures.write(temp.resolve("rank-source.json"),program,new MethodId("RankSource","reference","(LRankSource$Box;)V"));
            Guidance guidance=new Guidance(program,Catalog.read(reference),64);
            List<Method> methods=java.util.stream.IntStream.range(0,2049)
                    .mapToObj(i -> new Method(new MethodId("RankSource","candidate"+i,"()V"),org.objectweb.asm.Opcodes.ACC_PUBLIC,List.of())).toList();
            Query<List<Method>> ordered=guidance.order(methods);
            assertEquals(methods,ordered.value().orElseThrow());assertTrue(ordered.pending().isEmpty());
            assertTrue(guidance.issues().stream().anyMatch(issue -> issue.detail().startsWith("relation member metadata frontier")));
            guidance.enabled(false);assertTrue(guidance.issues().isEmpty());
        }
    }
    @Test void completionQueriesReadTheRealHeapAndNeverDefineClasses() throws Exception {
        try(Inputs input=input()) {
            Program program=new Program(input,20_000);Mechanisms mechanisms=new Mechanisms(program);
            Path fresh=BytecodeFixtures.compile(temp,17,Map.of("Fresh.java","public class Fresh {}"));
            byte[] bytes=Files.readAllBytes(fresh.resolve("Fresh.class"));
            Bytecode code=new Bytecode("Fresh","source-built class",bytes);
            ObjectValue buffer=new ObjectValue(1,"[B",true,"bytes"),loader=new ObjectValue(2,"java/lang/ClassLoader",false,"loader");
            var define=call(new MethodId("java/lang/ClassLoader","defineClass","([BII)Ljava/lang/Class;"),loader,List.of(buffer,new Literal(0),new Literal(bytes.length)));
            Bindings heap=(object,slot) -> object.equals(buffer) && slot instanceof Content?Value.of(code):Value.BOTTOM;
            for(int i=0;i<3;i++)assertTrue(mechanisms.normalCompletion(define,heap).isEmpty());
            assertEquals(0,program.definitionCount());
            assertTrue(mechanisms.apply(define,heap).orElseThrow().effects().stream().filter(Conditional.class::isInstance).map(Conditional.class::cast).flatMap(c -> c.local().effects().stream()).anyMatch(DefineClass.class::isInstance));
            ObjectValue iterator=new ObjectValue(3,"java/util/Iterator",false,"iterator");
            var next=call(new MethodId("java/util/Iterator","next","()Ljava/lang/Object;"),iterator,List.of());
            Bindings exhausted=(object,slot) -> slot instanceof Cursor?Value.of(new Literal(1)):slot instanceof Length?Value.of(new Literal(1)):Value.BOTTOM;
            assertEquals(Optional.of(false),mechanisms.normalCompletion(next,exhausted));
            assertEquals(0,program.definitionCount());
        }
    }
    @Test void nestedClassBytesPreserveBothAlternativePathsAndIntermediateEvidence() throws Exception {
        try(Inputs input=input()) {
            Program program=new Program(input,20_000);ClassLoading model=new ClassLoading();
            byte[] bytes={0,1};Bytecode code=new Bytecode("candidate","static bytes",bytes);
            ObjectValue root=new ObjectValue(1,"java/nio/ByteBuffer",true,"outer"),middle=new ObjectValue(2,"[B",true,"inner"),loader=new ObjectValue(3,"java/lang/ClassLoader",false,"loader");
            var define=call(new MethodId("java/lang/ClassLoader","defineClass","(Ljava/lang/String;Ljava/nio/ByteBuffer;Ljava/security/ProtectionDomain;)Ljava/lang/Class;"),loader,List.of(new Literal(null),root,new Literal(null)));
            BranchKey choice=new BranchKey(0,2);var left=Values.Path.EMPTY.with(choice,0).orElseThrow();var right=Values.Path.EMPTY.with(choice,1).orElseThrow();
            Gap a=new Gap(GapKind.INPUT_BINDING,site,"outer left"),b=new Gap(GapKind.DEPLOYMENT,site,"outer right"),c=new Gap(GapKind.CONTROL_CONDITION,site,"inner");
            Bindings heap=(object,slot) -> object.equals(root)?Value.of(middle,left).requiring(List.of(a)).tracing(Set.of(10)).merge(Value.of(middle,right).requiring(List.of(b)).tracing(Set.of(11))):object.equals(middle)?Value.of(code).requiring(List.of(c)).tracing(Set.of(12)):Value.BOTTOM;
            var alternatives=model.apply(define,heap,program).orElseThrow().effects().stream().filter(Conditional.class::isInstance).map(Conditional.class::cast).toList();
            assertEquals(2,alternatives.size());
            assertTrue(alternatives.stream().anyMatch(value -> value.path().equals(left) && value.dependencies().equals(Set.of(10,12)) && value.gaps().containsAll(List.of(a,c))));
            assertTrue(alternatives.stream().anyMatch(value -> value.path().equals(right) && value.dependencies().equals(Set.of(11,12)) && value.gaps().containsAll(List.of(b,c))));
        }
    }
    @Test void stringExpressionsRetainSuffixesAndEveryUnknownOperand() {
        Atom first=new ExternalValue("Ljava/lang/String;",new InputSource(site.method(),0,List.of()));
        Atom second=new ExternalValue("Ljava/lang/String;",new InputSource(site.method(),1,List.of()));
        Atom result=Mechanisms.concatenate(List.of(new Literal("pre"),first,new Literal("mid"),second,new Literal("post")));
        assertInstanceOf(StringPrefix.class,result);
        var sequence=assertInstanceOf(StringConcat.class,((StringPrefix)result).suffix());
        assertEquals(List.of(first,new Literal("mid"),second,new Literal("post")),sequence.pieces());
        assertEquals(new Literal("prefix"),Mechanisms.concatenate(List.of(new Literal("pre"),new Literal("fix"))));
        assertInstanceOf(Truncated.class,Mechanisms.concatenate(Collections.nCopies(65,first)));
    }
    @Test void multipleArrayLengthsShareOneTupleBudgetAndGrowthCanBeQueriedAgain() throws Exception {
        try(Inputs input=input()) {
            ObjectValue array=new ObjectValue(1,"[Ljava/lang/Object;",true,"array");
            Value lengths=Value.BOTTOM;for(int i=1;i<=64;i++)lengths=lengths.merge(Value.of(new Literal(i)));
            Value allLengths=lengths;
            Bindings heap=(object,slot) -> slot instanceof Length?allLengths:Value.of(new Literal("a")).merge(Value.of(new Literal("b")));
            var result=ValueBindings.array(array,heap,Values.Path.EMPTY,site);
            assertTrue(result.values().size()<=64);assertFalse(result.frontier().isEmpty());
            var changed=ValueBindings.array(array,(object,slot) -> slot instanceof Length?Value.of(new Literal(1)):Value.of(new Literal("late")),Values.Path.EMPTY,site);
            assertEquals(List.of(new Literal("late")),changed.values().get(0).elements());
        }
    }
    @Test void handleAndProxyTypesKeepTheirDefiningLoadersEvenWithIdenticalDescriptors() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Peer.java","public interface Peer {}","Target.java","public class Target {public static Peer accept(Peer value){return value;}}"));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);Object loader=new Object();byte[] peer=Files.readAllBytes(classes.resolve("Peer.class")),target=Files.readAllBytes(classes.resolve("Target.class"));
            int scope=program.define(loader,peer,peer,0,peer.length,null).value().orElseThrow().loader();program.define(loader,target,target,0,target.length,null);
            ClassValue parentPeer=new ClassValue("LPeer;",true),childPeer=new ClassValue("LPeer;",true,Optional.empty(),scope);
            Handles handles=new Handles();LookupValue lookup=new LookupValue("Empty",true,site);
            MethodId find=new MethodId("java/lang/invoke/MethodHandles$Lookup","findStatic","(Ljava/lang/Class;Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/MethodHandle;");
            Invocation wrong=call(find,lookup,List.of(new ClassValue("LTarget;",true,Optional.empty(),scope),new Literal("accept"),new MethodTypeValue(parentPeer,List.of(parentPeer))));
            assertTrue(handles.apply(wrong,(object,slot) -> Value.BOTTOM,program).orElseThrow().effects().stream().anyMatch(effect -> effect instanceof Raise raised && raised.type().equals("java/lang/NoSuchMethodException")));
            Invocation exact=call(find,lookup,List.of(new ClassValue("LTarget;",true,Optional.empty(),scope),new Literal("accept"),new MethodTypeValue(childPeer,List.of(childPeer))));
            MethodHandleValue handle=(MethodHandleValue)handles.apply(exact,(object,slot) -> Value.BOTTOM,program).orElseThrow().effects().stream().filter(Result.class::isInstance).map(Result.class::cast).flatMap(result -> result.value().alternatives().stream()).map(Bound::atom).findFirst().orElseThrow();
            Invocation invoke=call(new MethodId("java/lang/invoke/MethodHandle","invokeExact","(LPeer;)LPeer;"),handle,List.of(new ObjectValue(10,"Peer",true,"peer",false,Optional.empty(),scope)));
            assertTrue(handles.apply(invoke,(object,slot) -> Value.BOTTOM,program).orElseThrow().effects().stream().anyMatch(effect -> effect instanceof Raise raised && raised.type().equals("java/lang/invoke/WrongMethodTypeException")));
            Site childSite=new Site(new MethodId("Target","run","()V",scope),3,1,"defined fixture");
            Invocation sameScope=new Invocation(new Call(childSite,invoke.call().target(),org.objectweb.asm.Opcodes.INVOKEVIRTUAL,new Sources(Set.of()),List.of()),handle,invoke.arguments(),invoke.result(),invoke.path());
            assertTrue(handles.apply(sameScope,(object,slot) -> Value.BOTTOM,program).orElseThrow().effects().stream().anyMatch(effect -> effect instanceof Dispatch dispatch && dispatch.target().loader()==scope));
            ProxyValue proxy=new ProxyValue(11,List.of(childPeer),new Unknown("handler"),site);
            assertEquals(ValueBindings.Match.INCOMPATIBLE,ValueBindings.compatible(proxy,"LPeer;",program,0).match());
            assertEquals(ValueBindings.Match.COMPATIBLE,ValueBindings.compatible(proxy,"LPeer;",program,scope).match());
            assertThrows(IllegalArgumentException.class,() -> program.define(loader,peer,peer,0,peer.length,"Different"));
        }
    }
    @Test void nativeCandidatesUseTheirDefiningLoaderInsteadOfTheSameNamedParentType() throws Exception {
        Path parent=BytecodeFixtures.compile(temp,17,Map.of("Receiver.java","public class Receiver {}"));
        Path child=BytecodeFixtures.compile(temp,17,Map.of("Receiver.java","public class Receiver implements java.io.Serializable {public int hashCode(){return 37;}}"));
        try(Inputs input=Inputs.open(parent,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20_000);byte[] bytes=Files.readAllBytes(child.resolve("Receiver.class"));
            int scope=program.define(new Object(),bytes,bytes,0,bytes.length,null).value().orElseThrow().loader();
            Invocation read=call(new MethodId("java/io/ObjectInputStream","readObject","()Ljava/lang/Object;"),new ObjectValue(1,"java/io/ObjectInputStream",true,"stream"),List.of());
            Local local=new Mechanisms(program).apply(read,(object,slot) -> Value.BOTTOM).orElseThrow();
            List<Effect> effects=new ArrayList<>();ArrayDeque<Local> pending=new ArrayDeque<>(List.of(local));
            while(!pending.isEmpty())for(Effect effect:pending.removeFirst().effects()) {
                effects.add(effect);
                if(effect instanceof Conditional conditional)pending.add(conditional.local());
                if(effect instanceof Alternative alternative)pending.add(alternative.local());
            }
            assertTrue(effects.stream().anyMatch(effect -> effect instanceof Dispatch dispatch && dispatch.target().owner().equals("Receiver") && dispatch.target().loader()==scope && dispatch.receiver() instanceof Symbolic receiver && receiver.loader()==scope),"the serializable child declaration supplies the callback");
            assertTrue(effects.stream().filter(Need.class::isInstance).map(Need.class::cast).flatMap(need -> need.input().choices().stream()).anyMatch(value -> value instanceof ClassValue type && type.descriptor().equals("LReceiver;") && type.loader()==scope),"native member requirements retain the same defining loader");
        }
    }
}
