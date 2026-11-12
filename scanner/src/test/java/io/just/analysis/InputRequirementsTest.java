package io.just.analysis;

import io.just.knowledge.Values.*;
import io.just.program.Program.*;
import java.util.*;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class InputRequirementsTest {
    @Test void aTypedQuestionCanReplaceAGenericVariantOfItsSourceAtTheBudget() {
        MethodId entry=new MethodId("Needs","run","(Ljava/lang/String;Ljava/lang/String;)V");
        InputRequirements questions=new InputRequirements(2);Site value=new Site(entry,1,1,"fixture"),lookup=new Site(entry,2,1,"fixture");
        InputNeed first=need(entry,0,"generic");
        assertTrue(questions.add(0,entry,value,Path.EMPTY,new InputNeed(first.subject(),Optional.empty(),NeedKind.VALUE,"Ljava/lang/String;",first.choices(),"value before lookup"),Set.of()));
        assertTrue(questions.add(0,entry,value,Path.EMPTY,need(entry,1,"other"),Set.of()));
        assertFalse(questions.add(1,entry,lookup,Path.EMPTY,new InputNeed(first.subject(),Optional.empty(),NeedKind.CLASS_NAME,"Ljava/lang/String;",List.of(new Literal("java.lang.Runtime")),"class name at the lookup"),Set.of()));
        assertTrue(questions.snapshot().stream().anyMatch(row -> row.needed().kind()==NeedKind.CLASS_NAME && row.use().equals(lookup)));
        assertTrue(questions.snapshot().stream().anyMatch(row -> row.source().orElseThrow().parameterSlot()==1));
    }
    @Test void laterSourcesKeepAQuestionWithoutDroppingEveryEarlierSourceOrHidingTheBudget() {
        MethodId entry=new MethodId("Needs","run","(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V");
        Site first=new Site(entry,3,1,"fixture"),later=new Site(entry,4,1,"fixture"),last=new Site(entry,5,1,"fixture");
        InputRequirements questions=new InputRequirements(4);
        for(int i=0;i<4;i++)assertTrue(questions.add(0,entry,first,Path.EMPTY,need(entry,0,"first"+i),Set.of(i)));
        assertFalse(questions.add(1,entry,later,Path.EMPTY,need(entry,1,"later"),Set.of(9)),"replacing a redundant variant still reports the omitted question");
        var rows=questions.snapshot();assertEquals(4,rows.size());
        assertTrue(rows.stream().anyMatch(r -> r.source().orElseThrow().parameterSlot()==1 && r.dependencies().equals(List.of(9))));
        assertTrue(rows.stream().anyMatch(r -> r.needed().choices().equals(List.of(new Literal("first0")))),"the first source keeps a representative");
        assertFalse(questions.add(2,entry,last,Path.EMPTY,need(entry,2,"last"),Set.of(10)));
        assertEquals(Set.of(0,1,2),questions.snapshot().stream().map(r -> r.source().orElseThrow().parameterSlot()).collect(java.util.stream.Collectors.toSet()));
        assertFalse(questions.add(2,entry,last,Path.EMPTY,need(entry,2,"another"),Set.of(11)));
        assertEquals(4,questions.snapshot().size());
        assertEquals(List.of(0,1,2,3),questions.snapshot().stream().map(r -> r.id()).toList());
    }
    private InputNeed need(MethodId entry,int slot,String name) {
        return new InputNeed(new ExternalValue("Ljava/lang/String;",new InputSource(entry,slot,List.of())),Optional.empty(),NeedKind.METHOD_NAME,"Ljava/lang/String;",List.of(new Literal(name)),"name at the actual consumer");
    }
}
