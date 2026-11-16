package io.just;

import io.just.knowledge.EntryPoints.Mode;
import io.just.knowledge.EntryPoints.Entry;

import com.google.gson.*;
import io.just.analysis.*;
import io.just.analysis.ScanResult.*;
import io.just.input.Inputs;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Values.Path;
import io.just.program.Program.*;
import io.just.report.Reports;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import java.nio.file.Files;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

class ReportBindingsTest {
    @TempDir java.nio.file.Path temp;
    @Test void aFiniteSelectionWithoutABranchStillLinksItsConditionInMarkdown()throws Exception {
        MethodId method=new MethodId("ReportFixture","run","(Ljava/lang/String;)V");Site site=new Site(method,1,2,"fixture.class");
        Path path=Path.EMPTY.selecting(new InputSource(method,0,List.of()),new Literal("member"),"Ljava/lang/String;").orElseThrow();
        Gap gap=new Gap(GapKind.INPUT_BINDING,site,"the selected external name remains conditional");
        Relation relation=new Relation(0,0,Kind.REFLECTION,site,Optional.of(method),new Literal(null),List.of(),List.of(new Support(Evidence.PROVEN,List.of(site),List.of(gap),List.of())),path,"finite choice",Optional.empty());
        Entry entry=new Entry(new Method(method,org.objectweb.asm.Opcodes.ACC_STATIC|org.objectweb.asm.Opcodes.ACC_PUBLIC,List.of()),"component",List.of());
        Finding finding=new Finding(0,entry,Kind.REFLECTION,List.of(0),List.of(),List.of(gap),path,"finite choice",List.of(new ProofUse(0,0)));
        ScanResult result=new ScanResult(Mode.COMPONENT,Execution.FINISHED,Outcome.FINDINGS,
                new Inputs.Summary(List.of(),Inputs.Limits.defaults(),0,0,0,0,0,17,List.of(),List.of()),Optional.empty(),Analyzer.Limits.defaults(),20000,
                List.of(entry),List.of(),List.of(relation),List.of(finding),List.of(),List.of(),new Statistics(0,1,1,0,1,1,0,false,0,0,0,0,0,0,0),List.of(),List.of(),List.of(),List.of(new QueryIssue(QueryCause.BUDGET,"ranking metadata limit")));
        var output=temp.resolve("finite");Reports.write(result,output);String markdown=Files.readString(output.resolve("report.md"));
        assertTrue(markdown.contains("Path conditions: C"));assertTrue(markdown.contains("S0 selects V"));
        assertTrue(markdown.contains("Ranking guidance incomplete: ranking metadata limit"));
        JsonObject json=JsonParser.parseString(Files.readString(output.resolve("report.json"))).getAsJsonObject();
        assertEquals("FINISHED",json.get("execution").getAsString());assertEquals("ranking metadata limit",json.getAsJsonArray("rankingIssues").get(0).getAsJsonObject().get("detail").getAsString());
    }
    @Test void bothReportsRetainNestedTypesBindingsAndTheChosenAlternativeSupport()throws Exception {
        MethodId method=new MethodId("ReportFixture","run","()V");Site site=new Site(method,1,2,"fixture.class");
        ArrayValue types=new ArrayValue(2,ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",List.of(new Unknown("same reason"),new Truncated("same reason")));
        Reflected reflected=new Reflected(new ClassValue("LReportFixture;",true),new Literal("run"),types,true,site);
        LambdaValue lambda=new LambdaValue(3,"java/lang/Runnable","run","()V",new HandleConstant(org.objectweb.asm.Opcodes.H_INVOKESTATIC,method,false),List.of(reflected,types),List.of(),List.of(),site);
        ProxyValue proxy=new ProxyValue(4,List.of(new io.just.knowledge.Values.ClassValue("Ljava/lang/Runnable;",true)),lambda,site);
        ConstructorValue constructor=new ConstructorValue(6,new ClassValue("LReportFixture;",true),new ArrayValue(7,ArrayRole.METHOD_TYPES,"[Ljava/lang/Class;",List.of(new ClassValue("Ljava/lang/String;",true))),true,site);
        ClassValue scoped=new ClassValue("LReportFixture;",true,Optional.empty(),3);
        MethodTypeValue signature=new MethodTypeValue(scoped,List.of(scoped));
        MethodHandleValue handle=new MethodHandleValue(new MethodId("ReportFixture","forward",signature.descriptor(),3),signature,true,new LookupValue("ReportFixture",false,site),site);
        StringConcat text=new StringConcat(List.of(new Literal("prefix"),new Unknown("input"),new Literal("suffix")));
        NormalChoice normal=new NormalChoice(0,1,-1,List.of(2),method,reflected,List.of(types));
        InputSource source=new InputSource(method,0,List.of(new Index(2)));
        Path path=Path.EMPTY.with(normal,1).orElseThrow().selecting(source,new Literal("run"),"Ljava/lang/String;").orElseThrow()
                .selecting(new ObjectSource(4,List.of(new RuntimeClass())),new ClassValue("Ljava/lang/Object;",true)).orElseThrow()
                .selecting(new ValueSource(6,1,new Unknown("lookup operand"),List.of(new Length())),new Literal(0),"I").orElseThrow();
        Gap gap=new Gap(GapKind.INPUT_BINDING,site,"unavailable alternative",Optional.of(normal));
        Relation relation=new Relation(0,0,Kind.REFLECTION,site,Optional.of(method),proxy,List.of(reflected,types,constructor,new Literal("second"),handle,text),
                List.of(new Support(Evidence.CONDITIONAL,List.of(site),List.of(gap),List.of()),new Support(Evidence.PROVEN,List.of(site),List.of(),List.of())),path,"binding projection",Optional.of(new KeyComparison(reflected,handle)));
        Entry entry=new Entry(new Method(method,org.objectweb.asm.Opcodes.ACC_STATIC|org.objectweb.asm.Opcodes.ACC_PUBLIC,List.of()),"component",List.of());
        Finding finding=new Finding(0,entry,Kind.REFLECTION,List.of(0),List.of(),List.of(),path,"chosen independent proof",List.of(new ProofUse(0,1)));
        InputRequirement need=new InputRequirement(0,method,0,site,path,Optional.of(source),new InputNeed(new ExternalValue("Ljava/lang/String;",source),Optional.empty(),NeedKind.METHOD_NAME,"Ljava/lang/String;",List.of(new Literal("run")),"selected member"),List.of(0));
        ScanResult result=new ScanResult(Mode.COMPONENT,Execution.FINISHED,Outcome.FINDINGS,
                new Inputs.Summary(List.of(),Inputs.Limits.defaults(),0,0,0,0,0,17,List.of(),List.of()),Optional.empty(),Analyzer.Limits.defaults(),20_000,
                List.of(entry),List.of(),List.of(relation),List.of(finding),List.of(),List.of(),new Statistics(0,1,1,0,1,1,0,false,0,0,0,0,0,0,0),List.of(need),List.of(),List.of(),List.of());
        var output=temp.resolve("reports");Reports.write(result,output);
        JsonObject json=JsonParser.parseString(Files.readString(output.resolve("report.json"))).getAsJsonObject();
        JsonArray values=json.getAsJsonObject("references").getAsJsonArray("values");JsonObject reported=json.getAsJsonArray("relations").get(0).getAsJsonObject();
        JsonObject receiver=values.get(reported.get("receiver").getAsInt()).getAsJsonObject().getAsJsonObject("value");
        JsonObject invocationType=values.get(values.get(reported.getAsJsonArray("arguments").get(4).getAsInt()).getAsJsonObject().getAsJsonObject("value").get("invocationType").getAsInt()).getAsJsonObject().getAsJsonObject("value");
        assertEquals(3,values.get(invocationType.get("returned").getAsInt()).getAsJsonObject().getAsJsonObject("value").get("loader").getAsInt());
        assertEquals(invocationType.get("returned"),invocationType.getAsJsonArray("parameters").get(0));
        JsonObject expression=values.get(reported.getAsJsonArray("arguments").get(5).getAsInt()).getAsJsonObject().getAsJsonObject("value");
        assertEquals("suffix",values.get(expression.getAsJsonArray("pieces").get(2).getAsInt()).getAsJsonObject().getAsJsonObject("value").get("value").getAsString());
        assertEquals(reported.getAsJsonArray("arguments").get(4),reported.getAsJsonObject("slot").get("existing"));
        assertEquals(4,receiver.get("id").getAsInt());JsonObject handler=values.get(receiver.get("handler").getAsInt()).getAsJsonObject();assertEquals("LambdaValue",handler.get("kind").getAsString());
        JsonObject captured=values.get(handler.getAsJsonObject("value").getAsJsonArray("captured").get(0).getAsInt()).getAsJsonObject();assertEquals("Reflected",captured.get("kind").getAsString());
        JsonArray nested=values.get(captured.getAsJsonObject("value").get("parameterTypes").getAsInt()).getAsJsonObject().getAsJsonObject("value").getAsJsonArray("elements");
        assertEquals(List.of("Unknown","Truncated"),nested.asList().stream().map(v -> values.get(v.getAsInt()).getAsJsonObject().get("kind").getAsString()).toList());
        assertEquals(6,reported.getAsJsonArray("arguments").size());assertEquals(2,reported.getAsJsonArray("supports").size());
        JsonObject constructed=json.getAsJsonObject("references").getAsJsonArray("values").get(reported.getAsJsonArray("arguments").get(2).getAsInt()).getAsJsonObject();
        assertEquals("ConstructorValue",constructed.get("kind").getAsString());
        assertEquals("ClassValue",values.get(constructed.getAsJsonObject("value").get("declaringClass").getAsInt()).getAsJsonObject().get("kind").getAsString());
        assertEquals("ClassValue",values.get(values.get(constructed.getAsJsonObject("value").get("parameterTypes").getAsInt()).getAsJsonObject().getAsJsonObject("value").getAsJsonArray("elements").get(0).getAsInt()).getAsJsonObject().get("kind").getAsString());
        assertEquals(1,json.getAsJsonArray("findings").get(0).getAsJsonObject().getAsJsonArray("proof").get(0).getAsJsonObject().get("support").getAsInt());
        JsonObject condition=json.getAsJsonObject("references").getAsJsonArray("conditions").get(reported.get("conditions").getAsInt()).getAsJsonObject();
        assertEquals(3,condition.getAsJsonArray("selections").size());
        JsonObject choice=json.getAsJsonObject("references").getAsJsonArray("choices").get(condition.getAsJsonArray("choices").get(0).getAsJsonArray().get(0).getAsInt()).getAsJsonObject();
        assertEquals("NormalChoice",choice.get("kind").getAsString());
        assertEquals("Reflected",values.get(choice.get("receiver").getAsInt()).getAsJsonObject().get("kind").getAsString());
        JsonArray sources=json.getAsJsonObject("references").getAsJsonArray("sources");assertEquals(3,sources.size());
        assertEquals("InputSource",sources.get(0).getAsJsonObject().get("kind").getAsString());
        assertEquals("Unknown",values.get(sources.get(2).getAsJsonObject().get("producer").getAsInt()).getAsJsonObject().get("kind").getAsString());
        JsonObject template=JsonParser.parseString(Files.readString(output.resolve("input-requirements.json"))).getAsJsonObject();
        assertEquals(0,template.getAsJsonArray("requirements").get(0).getAsJsonObject().get("requirement").getAsInt());
        assertEquals("report.json",template.get("report").getAsString());
        String markdown=Files.readString(output.resolve("report.md"));
        for(String token:List.of("\"handler\"","\"captured\"","\"parameterTypes\"","\"elements\"","Unknown","Truncated","#0/S1","S0 CONDITIONAL","S1 PROVEN","S0 selects V","normal 0:1:-1"))assertTrue(markdown.contains(token),token);
        assertTrue(Files.exists(output.resolve("input-requirements.json")));
    }
}
