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
