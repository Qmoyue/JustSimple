package io.just.knowledge;

import io.just.BytecodeFixtures;
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
