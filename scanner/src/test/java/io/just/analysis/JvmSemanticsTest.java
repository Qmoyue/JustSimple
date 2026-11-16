package io.just.analysis;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.knowledge.Values;
import io.just.program.Program;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.objectweb.asm.Opcodes;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class JvmSemanticsTest {
    @TempDir Path temp;
    @Test void runtimeTypeChecksAndReferenceArrayStoresKeepLoaderIdentity() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Same.java","public class Same {}"));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);JvmSemantics jvm=new JvmSemantics(program);
            byte[] bytes=java.nio.file.Files.readAllBytes(classes.resolve("Same.class"));
            int loader=program.define(new Object(),bytes,bytes,0,bytes.length,null).value().orElseThrow().loader();
            Values.ObjectValue local=new Values.ObjectValue(1,"Same",true,"local",false,Optional.empty(),0);
            Values.ObjectValue foreign=new Values.ObjectValue(2,"Same",true,"foreign",false,Optional.empty(),loader);
            Site site=new Site(new MethodId("Same","test","()V"),0,-1,"fixture");
            Compute test=new Compute(site,Opcodes.INSTANCEOF,List.of(),0,"Same");
            assertEquals(new Values.Literal(0),jvm.compute(test,List.of(foreign)));
            assertEquals(new Values.Literal(1),jvm.compute(test,List.of(local)));
            Compute scoped=new Compute(new Site(new MethodId("Same","test","()V",loader),0,-1,"fixture"),Opcodes.INSTANCEOF,List.of(),0,"Same");
            assertEquals(new Values.Literal(1),jvm.compute(scoped,List.of(foreign)));
            assertEquals(new Values.Literal(0),jvm.compute(scoped,List.of(local)));
            Values.ObjectValue unresolved=new Values.ObjectValue(4,"Missing",true,"unknown runtime hierarchy",false);
            assertInstanceOf(Values.Unknown.class,jvm.compute(test,List.of(unresolved)));
            Values.ObjectValue array=new Values.ObjectValue(3,"[LSame;",true,"array",false,Optional.empty(),loader);
            Sources empty=new Sources(Set.of());WriteArray store=new WriteArray(site,empty,empty,empty);
            assertEquals(new JvmSemantics.Normal(List.of(),List.of()),jvm.check(store,List.of(array,new Values.Literal(0),foreign),OptionalInt.of(1)));
            assertEquals(new JvmSemantics.Rejected("java/lang/ArrayStoreException"),jvm.check(store,List.of(array,new Values.Literal(0),local),OptionalInt.of(1)));
        }
    }
    @Test void nullChecksDoNotTreatUnboundReflectionInputsAsNonNull() throws Exception {
        try(Inputs input=Inputs.open(temp,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            JvmSemantics jvm=new JvmSemantics(new Program(input,20000));
            Site site=new Site(new MethodId("Test","run","()V"),0,-1,"fixture");
            Values.Value unknown=Values.Value.of(new Values.UnboundValue(1,0,"Ljava/lang/Object;",new Values.Unknown("reflection input")));
            for(int opcode:List.of(Opcodes.IFNULL,Opcodes.IFNONNULL)) {
                Branch branch=new Branch(site,opcode,List.of(),1);
                assertEquals(Optional.empty(),jvm.branchTaken(branch,List.of(unknown)));
                assertEquals(Optional.of(opcode==Opcodes.IFNULL),jvm.branchTaken(branch,List.of(Values.Value.NULL)));
                assertEquals(Optional.of(opcode==Opcodes.IFNONNULL),jvm.branchTaken(branch,List.of(Values.Value.of(new Values.Literal("known string")))));
            }
        }
    }
    @Test void completeEmptyVoidBodyCanReturnNormallyButTruncatedFactsCannotProveIt() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Budget.java","public class Budget {public static void empty(){}}"));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            MethodId id=new MethodId("Budget","empty","()V");
            Call call=new Call(new Site(id,0,1,"fixture"),id,Opcodes.INVOKESTATIC,new Sources(Set.of()),List.of());
            assertTrue(new JvmSemantics(new Program(input,20_000)).normal(call,List.of(io.just.knowledge.Values.Value.NULL),Map.of()));
            Program limited=new Program(input,1);
            assertFalse(limited.facts(id).limitations().isEmpty());
            assertFalse(new JvmSemantics(limited).normal(call,List.of(io.just.knowledge.Values.Value.NULL),Map.of()));
        }
    }
    @Test void missingInterfacesCannotMakeAnObjectSubclassAnUnrelatedClass() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Candidate.java","public class Candidate implements Missing {}","Missing.java","public interface Missing {}","Other.java","public class Other {}","UnknownParent.java","public class UnknownParent {}","UnknownChild.java","public class UnknownChild extends UnknownParent {}"));
        java.nio.file.Files.delete(classes.resolve("Missing.class"));
        java.nio.file.Files.delete(classes.resolve("UnknownParent.class"));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);
            assertEquals(Optional.of(false),program.assignable("Candidate","Other").value());
            assertEquals(Optional.of(false),program.assignable("Candidate","java/lang/Class").value());
            assertTrue(program.assignable("Candidate","java/lang/Runnable").value().isEmpty(),"the missing interface may still extend a required interface");
            assertEquals(Optional.of(false),program.assignable("UnknownChild","java/lang/Class").value(),"a missing parent cannot permit extending a final class");
            assertTrue(program.assignable("UnknownChild","Other").value().isEmpty());
        }
    }
}
