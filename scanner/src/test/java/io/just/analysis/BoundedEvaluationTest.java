package io.just.analysis;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.MethodId;
import java.nio.file.*;
import java.util.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import static org.junit.jupiter.api.Assertions.*;

class BoundedEvaluationTest {
    @TempDir Path temp;
    @Test void unmodeledMonitorOperationsAndMutableStateNeverBecomePureProofs()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Stateful.java","public class Stateful {int flag;public void run(){if(flag!=0)flag=1;}}"));
        ClassWriter writer=new ClassWriter(ClassWriter.COMPUTE_MAXS);
        writer.visit(Opcodes.V1_8,Opcodes.ACC_PUBLIC,"MonitorProbe",null,"java/lang/Object",null);
        MethodVisitor method=writer.visitMethod(Opcodes.ACC_PUBLIC,"run","()V",null,null);
        method.visitCode();method.visitVarInsn(Opcodes.ALOAD,0);method.visitInsn(Opcodes.MONITORENTER);
        method.visitVarInsn(Opcodes.ALOAD,0);method.visitInsn(Opcodes.MONITOREXIT);method.visitInsn(Opcodes.RETURN);
        method.visitMaxs(0,0);method.visitEnd();writer.visitEnd();Files.write(classes.resolve("MonitorProbe.class"),writer.toByteArray());
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            BoundedEvaluation evaluator=new BoundedEvaluation(new Program(input,20_000));
            assertTrue(evaluator.evaluate(new MethodId("MonitorProbe","run","()V"),100).proof().isEmpty());
            assertTrue(evaluator.evaluate(new MethodId("Stateful","run","()V"),100).proof().isEmpty());
        }
    }
    @Test void anExhaustedProofCanBeRetriedAndCachedWorkIsNotChargedAgain()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Forward.java","""
                public class Forward {
                  public static class Base {public void run(){}}
                  public static class Child extends Base {public void run(){super.run();}}
                }
                """));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            BoundedEvaluation evaluator=new BoundedEvaluation(new Program(input,20_000));MethodId method=new MethodId("Forward$Child","run","()V");
            var partial=evaluator.evaluate(method,1);assertTrue(partial.proof().isEmpty());assertEquals(1,partial.work());assertTrue(partial.exhausted());
            var complete=evaluator.evaluate(method,100);assertTrue(complete.proof().isPresent());assertTrue(complete.work()>0);
            var reused=evaluator.evaluate(method,0);assertTrue(reused.proof().isPresent());assertEquals(0,reused.work());
        }
    }
}
