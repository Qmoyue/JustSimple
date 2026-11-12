package io.just.agent.bridge;

import com.google.gson.JsonParser;
import io.just.analysis.Analyzer;
import io.just.input.Inputs;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.concurrent.TimeUnit;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class TransportTest {
    @TempDir Path temp;

    @Test void startupDiagnosticsUseUtf8WithAnAsciiHostDefault()throws Exception {
        Process child=start(temp.resolve("缺少输入😀"));
        try {
            assertTrue(child.waitFor(20,TimeUnit.SECONDS));assertNotEquals(0,child.exitValue());
            assertTrue(Files.readString(temp.resolve("stderr.txt")).contains("缺少输入😀"));
        } finally {if(child.isAlive())child.destroyForcibly().waitFor();}
    }

    @Test void malformedUtf8RequestsFailInsteadOfChangingTheirIdentity()throws Exception {
        Process child=start(Files.createDirectory(temp.resolve("input")));
        try {
            byte[] request="{\"id\":\"X\",\"tool\":\"unknown\",\"args\":{}}\n".getBytes(StandardCharsets.UTF_8);
            request[7]=(byte)0x80;
            try(var input=child.getOutputStream()){input.write(request);}
            assertTrue(child.waitFor(20,TimeUnit.SECONDS));assertNotEquals(0,child.exitValue());
            assertTrue(Files.readString(temp.resolve("stderr.txt")).contains("MalformedInputException"));
        } finally {if(child.isAlive())child.destroyForcibly().waitFor();}
    }

    @Test void oversizedRequestIsRejectedWithoutWaitingForItsNewline() throws Exception {
        Process child = start(Files.createDirectory(temp.resolve("input")));
        try (var input = child.getOutputStream()) {
            input.write(" ".repeat(1_000_001).getBytes(StandardCharsets.US_ASCII));
            input.flush();
            assertTrue(child.waitFor(8, TimeUnit.SECONDS), "host must exit while stdin is still open");
            assertNotEquals(0, child.exitValue());
            assertTrue(Files.readString(temp.resolve("stderr.txt")).contains("tool request exceeds 1M characters"));
        } finally { if (child.isAlive()) child.destroyForcibly().waitFor(); }
    }

    @Test void wireEncodingIsUtf8EvenWithAnAsciiHostDefault()throws Exception {
        Process child=start(Files.createDirectory(temp.resolve("中文输入😀")));
        try {
            try(var request=child.getOutputStream()) {
                request.write("{\"id\":\"对象☃😀\",\"tool\":\"unknown\",\"args\":{}}\r\n".getBytes(StandardCharsets.UTF_8));
            }
            assertTrue(child.waitFor(20,TimeUnit.SECONDS),"tool host must settle after EOF");
            assertEquals(0,child.exitValue(),Files.readString(temp.resolve("stderr.txt")));
            String[] replies=new String(child.getInputStream().readAllBytes(),StandardCharsets.UTF_8).strip().split("\\R");
            assertEquals(2,replies.length);
            assertEquals("ready",JsonParser.parseString(replies[0]).getAsJsonObject().get("id").getAsString());
            var reply=JsonParser.parseString(replies[1]).getAsJsonObject();
            assertEquals("对象☃😀",reply.get("id").getAsString());
            assertEquals("INVALID_ARGUMENT",reply.getAsJsonObject("error").get("code").getAsString());
        } finally {if(child.isAlive())child.destroyForcibly().waitFor();}
    }

    @Test void nonObjectToolArgumentsAreRejectedAsInvalidArguments() throws Exception {
        Process child = start(Files.createDirectory(temp.resolve("input")));
        try {
            try (var input = child.getOutputStream()) {
                input.write("{\"id\":\"1\",\"tool\":\"unknown\",\"args\":[]}\n".getBytes(StandardCharsets.UTF_8));
            }
            assertTrue(child.waitFor(20, TimeUnit.SECONDS));
            assertEquals(0, child.exitValue(), Files.readString(temp.resolve("stderr.txt")));
            try (var replies = child.inputReader(StandardCharsets.UTF_8)) {
                assertEquals("ready", JsonParser.parseString(replies.readLine()).getAsJsonObject().get("id").getAsString());
                var reply = JsonParser.parseString(replies.readLine()).getAsJsonObject();
                assertEquals("1", reply.get("id").getAsString());
                assertEquals("INVALID_ARGUMENT", reply.getAsJsonObject("error").get("code").getAsString());
            }
        } finally { if (child.isAlive()) child.destroyForcibly().waitFor(); }
    }

    @Test void nonObjectBudgetsAreReportedAsInvalidArguments() throws Exception {
        Process child = start(Files.createDirectory(temp.resolve("input")));
        try {
            try (var input = child.getOutputStream()) {
                input.write("{\"id\":\"1\",\"tool\":\"scan_target\",\"args\":{\"budgets\":[]}}\n".getBytes(StandardCharsets.UTF_8));
            }
            assertTrue(child.waitFor(20, TimeUnit.SECONDS));
            assertEquals(0, child.exitValue(), Files.readString(temp.resolve("stderr.txt")));
            try (var replies = child.inputReader(StandardCharsets.UTF_8)) {
                assertEquals("ready", JsonParser.parseString(replies.readLine()).getAsJsonObject().get("id").getAsString());
                var reply = JsonParser.parseString(replies.readLine()).getAsJsonObject();
                var error = reply.getAsJsonObject("error");
                assertEquals("INVALID_ARGUMENT", error.get("code").getAsString());
                assertTrue(error.get("message").getAsString().contains("budgets must be an object"));
            }
        } finally { if (child.isAlive()) child.destroyForcibly().waitFor(); }
    }

    private Process start(Path input)throws Exception {
        Path configuration=temp.resolve("config.json");
        var config=new ScannerTools.Config(input.toString(),System.getProperty("java.home"),java.util.List.of(),null,
                temp.resolve("结果😀").toString(),20000,4,100000,1,Inputs.Limits.defaults(),Analyzer.Limits.defaults());
        Files.writeString(configuration,ToolJson.GSON.toJson(config),StandardCharsets.UTF_8);
        String executable=Path.of(System.getProperty("java.home"),"bin",System.getProperty("os.name").startsWith("Windows")?"java.exe":"java").toString();
        return new ProcessBuilder(executable,"-Dfile.encoding=US-ASCII","-Dsun.stdout.encoding=US-ASCII","-Dsun.stderr.encoding=US-ASCII","-cp",
                System.getProperty("surefire.test.class.path",System.getProperty("java.class.path")),ToolMain.class.getName(),configuration.toString())
                .redirectError(temp.resolve("stderr.txt").toFile()).start();
    }
}
