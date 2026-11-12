package io.just.program;

import io.just.program.Program.MethodId;
import java.util.List;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class MethodIdTest {
    @Test void externalMethodDescriptorsRequireCompleteTypesAndRespectJvmLimits() {
        for(String valid:List.of("()V","(ID[Ljava/lang/String;)Ljava/lang/Object;","([[I)L包/类型;","("+"I".repeat(255)+")V",
                "("+"J".repeat(127)+"[D)V","()"+"[".repeat(255)+"I"))
            assertTrue(MethodId.validDescriptor(valid),valid);
        for(String invalid:List.of("()Vextra","(V)V","()","(Lfoo)V","([V)V","()Ljava.lang.String;","()L/foo;","()Lpkg//Type;","()Lpkg/;",
                "("+"[".repeat(256)+"I)V","("+"J".repeat(128)+")V"))
            assertFalse(MethodId.validDescriptor(invalid),invalid);
    }

    @Test void longQualifiedNamesUseTheSameValidationRules() {
        String name = "pkg/".repeat(8_000) + "Type";
        assertTrue(MethodId.validDescriptor("()L" + name + ";"));
        assertFalse(MethodId.validDescriptor("()L" + name));
    }
}
