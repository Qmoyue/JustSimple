package io.just.knowledge;

import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Mechanisms.*;
import io.just.input.Inputs;
import io.just.program.Program;
import io.just.BytecodeFixtures;
import io.just.program.Program.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class ArrayBindingsTest {
    @TempDir java.nio.file.Path temp;
    @Test void overflowKeepsCompleteTuplesAndReportsOmittedCombinationsSeparately() {
        Site site=new Site(new MethodId("ArrayBoundary","run","()V"),3,1,"source-built array consumer");
        ObjectValue array=new ObjectValue(1,"[Ljava/lang/Object;",true,"finite array",false);
        Set<Bound> values=new LinkedHashSet<>();for(int i=0;i<70;i++)values.add(new Bound(new Literal(i),Path.EMPTY));
        Mechanisms.Bindings heap=(object,slot) -> slot instanceof Length?Value.of(new Literal(2)):slot.equals(new Index(0))?new Value(values):slot.equals(new Index(1))?Value.of(new Literal("tail")):Value.BOTTOM;
        var result=ValueBindings.array(array,heap,Path.EMPTY,site);
        assertEquals(64,result.values().size());
        assertTrue(result.values().stream().allMatch(tuple -> tuple.elements().size()==2 && tuple.elements().get(1).equals(new Literal("tail")) && tuple.elements().get(0) instanceof Literal));
        assertTrue(result.values().stream().allMatch(tuple -> tuple.gaps().isEmpty()),"retained exact tuples do not depend on the cutoff");
        assertTrue(result.frontier().stream().anyMatch(g -> g.kind()==GapKind.BUDGET && g.site().equals(site)));
        assertTrue(ValueBindings.array(array,(object,slot) -> slot instanceof Length?Value.of(new Literal(100)):Value.BOTTOM,Path.EMPTY,site).frontier().stream().anyMatch(g -> g.kind()==GapKind.BUDGET));
    }
    @Test void unboxingOverflowRetainsConvertedArgumentTuples() throws Exception {
        var classes=BytecodeFixtures.compile(temp,8,Map.of("PrimitiveTarget.java","public class PrimitiveTarget {public PrimitiveTarget(long left,long right){}}"));
        try(Inputs input=Inputs.open(classes,List.of(),java.nio.file.Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);Site site=new Site(new MethodId("ArrayBoundary","run","()V"),3,1,"finite boxed argument consumer");
            ConstructorValue constructor=new ConstructorValue(1,new ClassValue("LPrimitiveTarget;",true),new ArrayValue(2,ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",List.of(new ClassValue("J",true),new ClassValue("J",true))),false,site);
            ObjectValue left=new ObjectValue(3,"java/lang/Integer",true,"left box",false),right=new ObjectValue(4,"java/lang/Integer",true,"right box",false);
            Bindings heap=(object,slot) -> {
                if(!(slot instanceof Content))return Value.BOTTOM;
                Set<Bound> values=new LinkedHashSet<>();for(int i=0;i<(object.equals(left)?9:8);i++)values.add(new Bound(new Literal(i),Path.EMPTY));return new Value(values);
            };
            Sources none=new Sources(Set.of());Call call=new Call(site,new MethodId("java/lang/reflect/Constructor","newInstance","([Ljava/lang/Object;)Ljava/lang/Object;"),org.objectweb.asm.Opcodes.INVOKEVIRTUAL,none,List.of(none));
            Invocation invocation=new Invocation(call,constructor,List.of(new ArrayValue(5,ArrayRole.PROXY_ARGUMENTS,"[Ljava/lang/Object;",List.of(left,right))),new ObjectValue(6,"java/lang/Object",false,"result",false),Path.EMPTY);
            Local local=new Constructors(new Guidance(program,Catalog.empty())).apply(invocation,heap,program).orElseThrow();
            var constructions=local.effects().stream().filter(Conditional.class::isInstance).map(Conditional.class::cast).flatMap(c -> c.local().effects().stream()).filter(Construct.class::isInstance).map(Construct.class::cast).toList();
            assertEquals(64,constructions.size());
            assertTrue(constructions.stream().allMatch(c -> c.arguments().size()==2 && c.arguments().stream().allMatch(a -> a instanceof Literal l && l.value() instanceof Long)),"retained tuples reach construction with their real primitive conversions");
            assertTrue(local.effects().stream().filter(Observe.class::isInstance).map(Observe.class::cast).anyMatch(o -> o.gaps().stream().anyMatch(g -> g.kind()==GapKind.BUDGET)));
        }
    }
}
