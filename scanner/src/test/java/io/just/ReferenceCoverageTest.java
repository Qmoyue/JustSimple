package io.just;

import io.just.input.Inputs;
import io.just.knowledge.Catalog;
import io.just.program.Program;
import io.just.program.Program.MethodId;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;
import static org.junit.jupiter.api.Assertions.*;

class ReferenceCoverageTest {
    @TempDir Path temp;

    @Test void lazyHashAndPropertyReadersRetainTheirOwnValues()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("LazyLinks.java","""
            import java.lang.reflect.*;
            public class LazyLinks {
              interface Initializer {Object initialize();}
              interface Getter {Object get(Object value);}
              static class Holder {
                Initializer initializer; Object value;
                Object get(){if(value==null)value=initializer.initialize();return value;}
                Object direct(){if(value==null)return initializer.initialize();return value;}
              }
              Holder holder; Getter[] getters; Method method;
              int hash(){return ((Integer)holder.get()).intValue();}
              int unrelated(Integer value){holder.get();return value.intValue();}
              Object property(Object value,int index){return getters[index].get(value);}
              Object unrelatedProperty(Object value,int index,Getter other){return other.get(value);}
              Object reflect(Object value){try{return method.invoke(value,new Object[0]);}catch(Exception ignored){return null;}}
              Object unrelatedReflect(Object value,Method other){try{return other.invoke(value,new Object[0]);}catch(Exception ignored){return null;}}
            }
            """));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Catalog catalog=Catalog.builtin();String id="hibernate-lazy-property-handoff";
            assertTrue(references(catalog,program,new MethodId("LazyLinks$Holder","get","()Ljava/lang/Object;"),id,"*"));
            assertFalse(references(catalog,program,new MethodId("LazyLinks$Holder","direct","()Ljava/lang/Object;"),id,"*"));
            assertTrue(references(catalog,program,new MethodId("LazyLinks","hash","()I"),id,"intValue"));
            assertFalse(references(catalog,program,new MethodId("LazyLinks","unrelated","(Ljava/lang/Integer;)I"),id,"intValue"));
            assertTrue(references(catalog,program,new MethodId("LazyLinks","property","(Ljava/lang/Object;I)Ljava/lang/Object;"),id,"*"));
            assertFalse(references(catalog,program,new MethodId("LazyLinks","unrelatedProperty","(Ljava/lang/Object;ILLazyLinks$Getter;)Ljava/lang/Object;"),id,"*"));
            assertTrue(references(catalog,program,new MethodId("LazyLinks","reflect","(Ljava/lang/Object;)Ljava/lang/Object;"),id,"invoke"));
            assertFalse(references(catalog,program,new MethodId("LazyLinks","unrelatedReflect","(Ljava/lang/Object;Ljava/lang/reflect/Method;)Ljava/lang/Object;"),id,"invoke"));
        }
    }

    @Test void jdbcAndAccessibleReflectionFollowTheActualValues()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("DriverLinks.java","""
            import java.lang.reflect.*;
            import java.net.*;
            import java.sql.*;
            import java.util.*;
            public class DriverLinks {
              String url, driverName;
              Object bean;
              URLClassLoader loader;
              Connection connect(String user,String password)throws SQLException {
                return DriverManager.getConnection(url,user,password);
              }
              Connection direct(String url,String user,String password)throws SQLException {
                return DriverManager.getConnection(url,user,password);
              }
              void load() { try { Class.forName(driverName); } catch(ClassNotFoundException ignored) {} }
              void loadConstant() { try { Class.forName("fixed"); } catch(ClassNotFoundException ignored) {} }
              Object declared() {
                try {
                  Method method=bean.getClass().getDeclaredMethod("get",new Class<?>[0]);
                  method.setAccessible(true);
                  return method.invoke(bean);
                } catch(Exception ignored) { return null; }
              }
              Object unrelated(Method other) {
                try {
                  Method method=bean.getClass().getDeclaredMethod("get",new Class<?>[0]);
                  method.setAccessible(true);
                  return other.invoke(bean);
                } catch(Exception ignored) { return null; }
              }
              Connection loaded(String name,String url,Properties properties) {
                try { Driver driver=(Driver)loader.loadClass(name).newInstance(); return driver.connect(url,properties); }
                catch(Exception ignored) { return null; }
              }
              Connection unrelatedDriver(String name,String url,Properties properties,Driver other) {
                try { loader.loadClass(name).newInstance(); return other.connect(url,properties); }
                catch(Exception ignored) { return null; }
              }
            }
            """));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Catalog catalog=Catalog.builtin();
            String connect="(Ljava/lang/String;Ljava/lang/String;)Ljava/sql/Connection;";
            assertTrue(references(catalog,program,new MethodId("DriverLinks","connect",connect),"jdbc-datasource-credentials","getConnection"));
            assertFalse(references(catalog,program,new MethodId("DriverLinks","direct","(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)Ljava/sql/Connection;"),"jdbc-datasource-credentials","getConnection"));
            assertTrue(references(catalog,program,new MethodId("DriverLinks","load","()V"),"jdbc-driver-class-loading","forName"));
            assertFalse(references(catalog,program,new MethodId("DriverLinks","loadConstant","()V"),"jdbc-driver-class-loading","forName"));
            assertTrue(references(catalog,program,new MethodId("DriverLinks","declared","()Ljava/lang/Object;"),"reflective-declared-access","getDeclaredMethod"));
            assertFalse(references(catalog,program,new MethodId("DriverLinks","unrelated","(Ljava/lang/reflect/Method;)Ljava/lang/Object;"),"reflective-declared-access","getDeclaredMethod"));
            String loaded="(Ljava/lang/String;Ljava/lang/String;Ljava/util/Properties;)Ljava/sql/Connection;";
            assertTrue(references(catalog,program,new MethodId("DriverLinks","loaded",loaded),"jdbc-loaded-driver","newInstance"));
            assertFalse(references(catalog,program,new MethodId("DriverLinks","unrelatedDriver","(Ljava/lang/String;Ljava/lang/String;Ljava/util/Properties;Ljava/sql/Driver;)Ljava/sql/Connection;"),"jdbc-loaded-driver","newInstance"));
        }
    }

    @Test void jndiReadersAndReflectiveNamesFollowTheirActualInputs()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("ReferenceLinks.java","""
            import java.io.*;
            import java.util.*;
            import javax.naming.*;
            public class ReferenceLinks {
              String name;
              public void properties(Reference source) throws NamingException {
                Properties result=new Properties(); Enumeration<RefAddr> entries=source.getAll();
                while(entries.hasMoreElements()) { RefAddr entry=entries.nextElement(); result.setProperty(entry.getType(),(String)entry.getContent()); }
              }
              public void unrelated(Reference source,RefAddr other) throws NamingException {
                Properties result=new Properties(); Enumeration<RefAddr> entries=source.getAll();
                while(entries.hasMoreElements()) { entries.nextElement(); result.setProperty(other.getType(),(String)other.getContent()); }
              }
              public Object member(Class<?> type) {
                try { return type.getDeclaredMethod("get"+name); } catch(Exception failure) { return null; }
              }
              public Object unrelatedMember(Class<?> type) {
                try { String unused="get"+name; return type.getDeclaredMethod("fixed"); } catch(Exception failure) { return null; }
              }
              static class ReaderWrapper extends Reader {
                Reader delegate;
                public int read(char[] buffer,int offset,int size)throws IOException {return delegate.read(buffer,offset,size);}
                public void close()throws IOException {delegate.close();}
              }
              public static int direct(Reader reader,char[] buffer,int offset,int size)throws IOException {return reader.read(buffer,offset,size);}
            }
            """));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Catalog catalog=Catalog.builtin();
            assertTrue(references(catalog,program,new MethodId("ReferenceLinks","properties","(Ljavax/naming/Reference;)V"),"jndi-reference-properties","nextElement"));
            assertFalse(references(catalog,program,new MethodId("ReferenceLinks","unrelated","(Ljavax/naming/Reference;Ljavax/naming/RefAddr;)V"),"jndi-reference-properties","nextElement"));
            assertTrue(references(catalog,program,new MethodId("ReferenceLinks","member","(Ljava/lang/Class;)Ljava/lang/Object;"),"gleipner-reflection-name","toString"));
            assertFalse(references(catalog,program,new MethodId("ReferenceLinks","unrelatedMember","(Ljava/lang/Class;)Ljava/lang/Object;"),"gleipner-reflection-name","toString"));
            assertTrue(references(catalog,program,new MethodId("ReferenceLinks$ReaderWrapper","read","([CII)I"),"reader-stream-delegation","read"));
            assertFalse(references(catalog,program,new MethodId("ReferenceLinks","direct","(Ljava/io/Reader;[CII)I"),"reader-stream-delegation","read"));
        }
    }

    @Test void referenceRelationsFollowTheActualReceiverAndResult() throws Exception {
        Path classes=BytecodeFixtures.compile(temp,8,Map.of("Handoffs.java","""
            import java.lang.reflect.Method;
            import java.lang.reflect.Type;
            public class Handoffs {
              static class Transform { Object apply(Object value) { return value; } }
              static class Hash { int hash(Object value) { return 0; } }
              Transform transform;
              Hash hash;
              String property;
              int derived(Object value) { return hash.hash(transform.apply(value)); }
              int direct(Object value) { return hash.hash(value); }
              static Object lookup(Object bean, String name) { return bean; }
              private int order(Object left, Object right) { return 0; }
              int compare(Object left, Object right) {
                if (property == null) return 0;
                try { return order(lookup(left, property), lookup(right, property)); }
                catch (RuntimeException failure) { return 0; }
              }
              int compareDirect(Object left, Object right) {
                if (property == null) return 0;
                try { lookup(left, property); lookup(right, property); return order(left, right); }
                catch (RuntimeException failure) { return 0; }
              }
              static Object convert(Type type, Object value) { return value; }
              Object typed(Method method, Object value) {
                if (method.getParameterTypes().length == 0) return convert(method.getGenericReturnType(), value);
                return null;
              }
              Object unrelated(Method method, Object value) {
                if (method.getParameterTypes().length == 0) { method.getGenericReturnType(); return convert(Object.class, value); }
                return null;
              }
              Object reflect(Object receiver, String name, Class<?>[] types, Object[] args) {
                try { return receiver.getClass().getMethod(name, types).invoke(receiver, args); }
                catch (Exception failure) { return null; }
              }
              Object unrelatedReflection(Object receiver, String name, Class<?>[] types, Object[] args, Method other) {
                try { receiver.getClass().getMethod(name, types); return other.invoke(receiver, args); }
                catch (Exception failure) { return null; }
              }
            }
            """));
        try(Inputs inputs=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(inputs,20000);Catalog catalog=Catalog.builtin();
            String hash="(Ljava/lang/Object;)I",typed="(Ljava/lang/reflect/Method;Ljava/lang/Object;)Ljava/lang/Object;";
            assertTrue(references(catalog,program,new MethodId("Handoffs","derived",hash),"functional-equivalence"));
            assertFalse(references(catalog,program,new MethodId("Handoffs","direct",hash),"functional-equivalence"));
            assertTrue(references(catalog,program,new MethodId("Handoffs","typed",typed),"proxy-conversion"));
            assertFalse(references(catalog,program,new MethodId("Handoffs","unrelated",typed),"proxy-conversion"));
            String compare="(Ljava/lang/Object;Ljava/lang/Object;)I";
            assertTrue(references(catalog,program,new MethodId("Handoffs","compare",compare),"bean-property-comparison"));
            assertFalse(references(catalog,program,new MethodId("Handoffs","compareDirect",compare),"bean-property-comparison"));
            String reflect="(Ljava/lang/Object;Ljava/lang/String;[Ljava/lang/Class;[Ljava/lang/Object;)Ljava/lang/Object;";
            String unrelated="(Ljava/lang/Object;Ljava/lang/String;[Ljava/lang/Class;[Ljava/lang/Object;Ljava/lang/reflect/Method;)Ljava/lang/Object;";
            assertTrue(references(catalog,program,new MethodId("Handoffs","reflect",reflect),"reflective-field-handoff","getMethod"));
            assertFalse(references(catalog,program,new MethodId("Handoffs","unrelatedReflection",unrelated),"reflective-field-handoff","getMethod"));
        }
    }

    private static boolean references(Catalog catalog,Program program,MethodId method,String id) {
        return references(catalog,program,method,id,null);
    }
    private static boolean references(Catalog catalog,Program program,MethodId method,String id,String target) {
        var hints=catalog.hints(program,Set.of(method));assertTrue(hints.pending().isEmpty(),hints.pending().toString());
        return hints.value().orElseThrow().stream().filter(h -> target==null || h.requirements().stream().anyMatch(r -> r.pattern().target().name().equals(target)))
                .flatMap(h -> h.references().stream()).anyMatch(reference -> reference.entry().equals(id));
    }
}
