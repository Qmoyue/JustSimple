package io.just;

import io.just.app.Main;
import io.just.input.StaticData;
import io.just.knowledge.Catalog;
import java.io.IOException;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.TimeUnit;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import static org.junit.jupiter.api.Assertions.*;

class EncodingTest {
    @TempDir Path temp;

    @Test void compilerCliDiagnosticsAndReportsUseUtf8WithAnAsciiDefault()throws Exception {
        Path output=temp.resolve("中文 报告😀");
        Path stdout=temp.resolve("stdout.txt"),stderr=temp.resolve("stderr.txt");
        Process child=start(stdout,stderr,Fixture.class.getName(),temp.toString(),"scan");
        await(child,0);
        assertTrue(Files.readString(stdout).contains("中文 报告😀"));
        assertTrue(Files.readString(stderr).contains("中文 输入😀"));
        assertTrue(Files.readString(output.resolve("report.json")).contains("中文值😀"));
        assertTrue(Files.readString(output.resolve("report.md")).contains("中文值😀"));
        child=start(stdout,stderr,Fixture.class.getName(),temp.toString(),"invalid");
        await(child,2);
        assertTrue(Files.readString(stderr).contains("--未知选项😀"));
    }

    @Test void staticDataRejectsMalformedUtf8InsteadOfChangingItsSource()throws Exception {
        Path input=malformed("facts.json","""
                {"source":"BROKEN","basis":"REFERENCE","entry":{"owner":"Example","name":"run","descriptor":"()V","arguments":[]},"objects":[]}
                """);
        IOException failure=assertThrows(IOException.class,() -> StaticData.read(input));
        assertInstanceOf(CharacterCodingException.class,failure.getCause());
        assertTrue(failure.getMessage().contains(input.toString()));
    }

    @Test void knowledgeRejectsMalformedUtf8InsteadOfChangingReferenceIds()throws Exception {
        Path input=malformed("knowledge.json","""
                {"schema":"just.local-reference/v1","chains":[],"fragments":[{"id":"BROKEN","relations":[]}],"bytecodeObservations":[]}
                """);
        IOException failure=assertThrows(IOException.class,() -> Catalog.read(input));
        assertInstanceOf(CharacterCodingException.class,failure.getCause());
        assertTrue(failure.getMessage().contains(input.toString()));
    }

    private Path malformed(String name,String json)throws IOException {
        byte[] bytes=json.getBytes(StandardCharsets.UTF_8);bytes[json.indexOf("BROKEN")]=(byte)0x80;
        return Files.write(temp.resolve(name),bytes);
    }
    private Process start(Path stdout,Path stderr,String main,String... args)throws IOException {
        Path executable=Path.of(System.getProperty("java.home"),"bin",System.getProperty("os.name").startsWith("Windows")?"java.exe":"java");
        List<String> command=new ArrayList<>(List.of(executable.toString(),"-Dfile.encoding=US-ASCII","-Dsun.stdout.encoding=US-ASCII","-Dsun.stderr.encoding=US-ASCII",
                "-cp",System.getProperty("surefire.test.class.path",System.getProperty("java.class.path")),main));
        command.addAll(List.of(args));
        return new ProcessBuilder(command).redirectOutput(stdout.toFile()).redirectError(stderr.toFile()).start();
    }
    private void await(Process child,int expected)throws Exception {
        try {assertTrue(child.waitFor(30,TimeUnit.SECONDS));assertEquals(expected,child.exitValue(),Files.readString(temp.resolve("stderr.txt")));}
        finally {if(child.isAlive())child.destroyForcibly().waitFor();}
    }

    /** Test host compiles and statically scans the fixture; target classes are never loaded. */
    public static class Fixture {
        public static void main(String[] args)throws Exception {
            if(args[1].equals("invalid")){Main.main(new String[]{"--未知选项😀"});return;}
            Path root=Path.of(args[0]),input=Files.createDirectory(root.resolve("中文 输入😀"));
            Path classes=BytecodeFixtures.compile(input,17,Map.of("UnicodeFixture.java","""
                    public class UnicodeFixture {
                      static { if(System.nanoTime()!=0)throw new AssertionError("never execute"); }
                      public static void entry() { sink("中文值😀"); }
                      public static void sink(String value) {}
                    }
                    ""","编码样例.java","public class 编码样例 { public static String value(){ return \"源文件😀\"; } }"));
            assertTrue(Files.isRegularFile(classes.resolve("编码样例.class")));
            AssertionError invalid=assertThrows(AssertionError.class,() -> BytecodeFixtures.compile(input,17,Map.of("Broken.java","public class Broken { 缺失类型 value; }")));
            assertTrue(invalid.getMessage().contains("缺失类型"));
            Main.main(new String[]{"--input",classes.toString(),"--jdk-home",System.getProperty("java.home"),"--output",root.resolve("中文 报告😀").toString(),
                    "--mode","component","--entry","UnicodeFixture#entry()V","--sink","UnicodeFixture#sink(Ljava/lang/String;)V","--no-guidance"});
        }
    }
}
