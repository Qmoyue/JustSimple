package io.just.analysis;

import io.just.BytecodeFixtures;
import io.just.input.Inputs;
import io.just.knowledge.Mechanisms.Bindings;
import io.just.knowledge.Values;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.program.Program;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class CandidateBindingsTest {
    @TempDir Path temp;
    @Test void conditionalClassBoundsUseTheActualDefiningLoaderAndPermitDelegatedSubclasses()throws Exception {
        Path classes=BytecodeFixtures.compile(temp,17,Map.of("Bound.java","public class Bound {}", "Child.java","public class Child extends Bound {}"));
        try(Inputs input=Inputs.open(classes,List.of(),Path.of(System.getProperty("java.home")),Inputs.Limits.defaults())) {
            Program program=new Program(input,20000);CandidateBindings bindings=new CandidateBindings(program);
            byte[] base=Files.readAllBytes(classes.resolve("Bound.class")),child=Files.readAllBytes(classes.resolve("Child.class"));
            int shadow=program.define(new Object(),base,base,0,base.length,null).value().orElseThrow().loader();
            int delegated=program.define(new Object(),child,child,0,child.length,null).value().orElseThrow().loader();
            Bindings heap=(object,slot) -> Value.BOTTOM;
            for(int scope:List.of(0,shadow)) {
                ClassValue bound=new ClassValue("LBound;",false,Optional.of(new ObjectSource(1,List.of())),scope);
                ClassValue same=new ClassValue("LBound;",true,Optional.empty(),scope);
                ClassValue other=new ClassValue("LBound;",true,Optional.empty(),scope==0?shadow:0);
                assertTrue(bindings.require(Values.Path.EMPTY,new InputNeed(bound,Optional.empty(),NeedKind.VALUE,"Ljava/lang/Class;",List.of(other),"bounded class argument"),heap).isEmpty());
                assertTrue(bindings.require(Values.Path.EMPTY,new InputNeed(bound,Optional.empty(),NeedKind.VALUE,"Ljava/lang/Class;",List.of(same),"bounded class argument"),heap).isPresent());
            }
            ClassValue bound=new ClassValue("LBound;",false,Optional.of(new ObjectSource(2,List.of())),0);
            ClassValue subtype=new ClassValue("LChild;",true,Optional.empty(),delegated);
            assertTrue(bindings.require(Values.Path.EMPTY,new InputNeed(bound,Optional.empty(),NeedKind.VALUE,"Ljava/lang/Class;",List.of(subtype),"delegated superclass"),heap).isPresent());
        }
    }
}
