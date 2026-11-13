package io.just.agent.bridge;

import com.google.gson.JsonParser;
import io.just.analysis.Analyzer;
import io.just.input.Inputs;
import java.nio.file.*;
import java.util.List;
import javax.tools.ToolProvider;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class ScannerToolsTest {
    @TempDir Path temp;

    @Test void noReferenceKnowledgeKeepsBytecodeRankingEnabled()throws Exception {
        Path classes=Files.createDirectory(temp.resolve("classes"));
        Path source=temp.resolve("ReflectionSample.java");
        Files.writeString(source,"""
            public class ReflectionSample {
              public static Object run() throws Exception { return String.class.getMethod("toString").invoke("text"); }
            }
            """);
        assertEquals(0,ToolProvider.getSystemJavaCompiler().run(null,null,null,"-encoding","UTF-8","--release","8","-d",classes.toString(),source.toString()));
        var config=new ScannerTools.Config(classes.toString(),System.getProperty("java.home"),List.of(),null,
                temp.resolve("results").toString(),20000,8,20_000_000,2,Inputs.Limits.defaults(),Analyzer.Limits.defaults());
        try(ScannerTools tools=new ScannerTools(config)) {
            var request=JsonParser.parseString("""
                {"knowledge":"none","entries":[{"owner":"ReflectionSample","name":"run","descriptor":"()Ljava/lang/Object;"}]}
                """).getAsJsonObject();
            var reply=(ScannerTools.Reply)tools.execute("scan_target",request,ignored -> {});
            assertTrue(reply.summary().getAsJsonObject("statistics").get("rankingWork").getAsLong()>0,"bytecode-based ranking remains active");
            var pageRequest=JsonParser.parseString("{\"path\":[\"hints\"]}").getAsJsonObject();pageRequest.addProperty("resultRef",reply.resultRef());
            var page=(ResultStore.Page)tools.execute("read_result",pageRequest,ignored -> {});
            assertFalse(page.data().getAsJsonArray().isEmpty());
            page.data().getAsJsonArray().forEach(hint -> assertTrue(hint.getAsJsonObject().getAsJsonArray("references").isEmpty()));
        }
    }
}
