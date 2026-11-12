package io.just;

import com.google.gson.Gson;
import io.just.analysis.*;
import io.just.input.*;
import io.just.knowledge.*;
import io.just.knowledge.Values.*;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.objectweb.asm.*;
import java.nio.file.*;
import java.nio.file.Path;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class TemplateLoadingTest {
    @TempDir Path temp;
    @Test void templateByteArrayUsesTheActualDefinitionResultBeforeItsInitializer()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("TemplateBoundary.java","public class TemplateBoundary {public static void run(javax.xml.transform.Templates value)throws Exception{value.newTransformer();}public static void mark(){}}"));
        ClassWriter writer=new ClassWriter(ClassWriter.COMPUTE_MAXS);
        String parent="com/sun/org/apache/xalan/internal/xsltc/runtime/AbstractTranslet";
        writer.visit(Opcodes.V1_8,Opcodes.ACC_PUBLIC,"IndependentTranslet",null,parent,null);
        MethodVisitor constructor=writer.visitMethod(Opcodes.ACC_PUBLIC,"<init>","()V",null,null);constructor.visitCode();constructor.visitVarInsn(Opcodes.ALOAD,0);constructor.visitMethodInsn(Opcodes.INVOKESPECIAL,parent,"<init>","()V",false);constructor.visitInsn(Opcodes.RETURN);constructor.visitMaxs(0,0);constructor.visitEnd();
        MethodVisitor initializer=writer.visitMethod(Opcodes.ACC_STATIC,"<clinit>","()V",null,null);initializer.visitCode();initializer.visitMethodInsn(Opcodes.INVOKESTATIC,"TemplateBoundary","mark","()V",false);initializer.visitInsn(Opcodes.RETURN);initializer.visitMaxs(0,0);initializer.visitEnd();
        for(String descriptor:List.of("(Lcom/sun/org/apache/xalan/internal/xsltc/DOM;[Lcom/sun/org/apache/xml/internal/serializer/SerializationHandler;)V","(Lcom/sun/org/apache/xalan/internal/xsltc/DOM;Lcom/sun/org/apache/xml/internal/dtm/DTMAxisIterator;Lcom/sun/org/apache/xml/internal/serializer/SerializationHandler;)V")) {
            MethodVisitor method=writer.visitMethod(Opcodes.ACC_PUBLIC,"transform",descriptor,null,null);method.visitCode();method.visitInsn(Opcodes.RETURN);method.visitMaxs(0,0);method.visitEnd();
        }
        writer.visitEnd();Files.write(temp.resolve("fixture.class"),writer.toByteArray());
        String template="com/sun/org/apache/xalan/internal/xsltc/trax/TemplatesImpl";
        Map<String,Object> snapshot=Map.of("source","independent compiled classfile fixture","basis","BINDING","entry",Map.of("owner","TemplateBoundary","name","run","descriptor","(Ljavax/xml/transform/Templates;)V","arguments",List.of(Map.of("ref","template"))),"objects",List.of(
                Map.of("id","template","type",template,"fields",List.of(Map.of("owner",template,"name","_bytecodes","descriptor","[[B","value",Map.of("ref","matrix")))),
                Map.of("id","matrix","type","[[B","elements",List.of(Map.of("ref","classfile"))),Map.of("id","classfile","type","[B","classfile","fixture.class")));
        Path facts=temp.resolve("classfile-data.json");Files.writeString(facts,new Gson().toJson(snapshot));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);var marker=new Program.MethodId("TemplateBoundary","mark","()V");
            ScanResult result=new Analyzer(program,new Mechanisms(program,Catalog.empty(),Set.of(marker)),Analyzer.Limits.defaults()).scan(EntryPoints.Mode.COMPONENT,false,Set.of(new Program.MethodId("TemplateBoundary","run","(Ljavax/xml/transform/Templates;)V")),Optional.of(StaticData.read(facts)));
            assertTrue(result.relations().stream().anyMatch(r -> r.kind()==Kind.IMPACT && r.target().filter(t -> t.name().equals("defineClass")).isPresent()));
            assertTrue(result.findings().stream().anyMatch(f -> f.boundary()==Kind.IMPACT && result.relations().get(f.path().get(f.path().size()-1)).target().equals(Optional.of(marker))),result.limitations().toString());
            assertTrue(result.relations().stream().anyMatch(r -> r.site().method().owner().equals("IndependentTranslet") && r.site().method().name().equals("<clinit>") && r.site().method().loader()!=0));
        }
    }
}
