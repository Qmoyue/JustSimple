package io.just.knowledge;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.program.Program;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.nio.file.Files;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class StructureEvidenceTest {
    @TempDir Path temp;
    @Test void localNamingWitnessRequiresTheSelectedNameAndUnchangedFactoryArguments()throws Exception {
        String source="""
                package javax.naming.spi;
                import javax.naming.*;import java.util.*;
                public class NamingManager {
                  public static Object getObjectInstance(Object value,Name name,Context context,Hashtable<?,?> env)throws Exception {
                    Reference ref=(Reference)value;String factoryName=ref.getFactoryClassName();
                    ObjectFactory factory=getObjectFactoryFromReference(ref,SELECT);
                    return factory.getObjectInstance(ref,ARGUMENT,context,env);
                  }
                  static ObjectFactory getObjectFactoryFromReference(Reference ref,String name)throws Exception {return (ObjectFactory)loadClass(name).newInstance();}
                  static Class<?> loadClass(String name)throws Exception {return Class.forName(name);}
                }
                """;
        Path target=Files.createDirectory(temp.resolve("target"));
        for(int variant=0;variant<3;variant++) {
            String code=source.replace("SELECT",variant==2?"\"unrelated.Factory\"":"factoryName").replace("ARGUMENT",variant==1?"null":"name");
            Path classes=BytecodeFixtures.compile(temp,8,Map.of("javax/naming/spi/NamingManager.java",code));
            Path jdk=Files.createDirectory(temp.resolve("jdk-"+variant));Files.writeString(jdk.resolve("release"),"JAVA_VERSION=\"1.8.0\"\n");
            Files.createDirectories(jdk.resolve("jre/lib"));
            try(ZipOutputStream zip=new ZipOutputStream(Files.newOutputStream(jdk.resolve("jre/lib/rt.jar")))) {
                zip.putNextEntry(new ZipEntry("javax/naming/spi/NamingManager.class"));zip.write(Files.readAllBytes(classes.resolve("javax/naming/spi/NamingManager.class")));zip.closeEntry();
            }
            try(Inputs input=Inputs.open(target,List.of(),jdk,Inputs.Limits.defaults())) {
                var witness=new JdkStructures(new Program(input,20_000)).namingFactory();
                assertEquals(variant==0,!witness.sites().isEmpty(),"variant "+variant);
                var limited=new JdkStructures(new Program(input,1)).namingFactory();
                assertTrue(limited.sites().isEmpty());assertTrue(limited.pending().stream().anyMatch(p -> p.cause()==Program.QueryCause.BUDGET));
            }
        }
    }
    @Test void protocolWitnessNeedsTheStoredMethodObjectReceiverAndActualStreamArgument() throws Exception {
        String source="""
                package java.io;
                public class ObjectStreamClass {
                  java.lang.reflect.Method readObjectMethod; static boolean flag;
                  public void invokeReadObject(Object value,ObjectInputStream stream)throws Exception { BODY }
                }
                """;
        for(String body:List.of(
                "readObjectMethod.invoke(value,new Object[]{stream});",
                "readObjectMethod.invoke(new Object(),new Object[]{stream});",
                "readObjectMethod.invoke(value,new Object[]{null});",
                "Object[] args=new Object[1];if(flag){args[0]=stream;}else{readObjectMethod.invoke(value,args);}",
                "Object[] args=new Object[]{stream};args[0]=null;readObjectMethod.invoke(value,args);")) {
            Path classes=BytecodeFixtures.compile(temp,8,Map.of("java/io/ObjectStreamClass.java",source.replace("BODY",body)));
            try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
                var proof=new JdkStructures(new Program(input,20_000)).protocol("readObject");
                assertEquals(body.equals("readObjectMethod.invoke(value,new Object[]{stream});"),!proof.sites().isEmpty(),body);
                var truncated=new JdkStructures(new Program(input,1)).protocol("readObject");
                assertTrue(truncated.sites().isEmpty());assertTrue(truncated.pending().stream().anyMatch(p -> p.cause()==Program.QueryCause.BUDGET));
            }
        }
    }
    @Test void fieldRecoveryNeedsCompatibleControlFlowAndTheSameObjectAndDescriptor() throws Exception {
        String prefix="""
                package java.io;
                public class ObjectInputStream {
                  public Object readObject0(boolean unshared){return null;}
                  public void defaultReadFields(Object value,ObjectStreamClass desc){ BODY }
                }
                """;
        String desc="package java.io;public class ObjectStreamClass {public void setPrimFieldValues(Object value,byte[] data){}public void setObjFieldValues(Object value,Object[] data){}}";
        for(String body:List.of(
                "desc.setPrimFieldValues(value,new byte[0]);readObject0(false);desc.setObjFieldValues(value,new Object[0]);",
                "if(value==null){desc.setPrimFieldValues(value,new byte[0]);}else{readObject0(false);desc.setObjFieldValues(value,new Object[0]);}",
                "new ObjectStreamClass().setPrimFieldValues(value,new byte[0]);readObject0(false);desc.setObjFieldValues(value,new Object[0]);")) {
            Path classes=BytecodeFixtures.compile(temp,8,Map.of("java/io/ObjectInputStream.java",prefix.replace("BODY",body),"java/io/ObjectStreamClass.java",desc));
            try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
                var timing=new JdkStructures(new Program(input,20_000)).fieldTiming();
                assertEquals(body.startsWith("desc.setPrim")?JdkStructures.FieldOrder.PRIMITIVES_FIRST:JdkStructures.FieldOrder.UNKNOWN,timing.order(),body);
            }
        }
    }
}
