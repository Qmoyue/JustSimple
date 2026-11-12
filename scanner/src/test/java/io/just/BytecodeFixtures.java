package io.just;

import javax.tools.ToolProvider;
import java.nio.charset.StandardCharsets;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

/** Emits source-built test bytecode. It never loads or invokes the target. */
public final class BytecodeFixtures {
    private BytecodeFixtures() {}
    public static Path compile(Path temp,int release,Map<String,String> sources) throws IOException {
        Path directory=Files.createTempDirectory(temp,"fixture-"),classes=Files.createDirectory(directory.resolve("classes"));
        var compiler=ToolProvider.getSystemJavaCompiler();assertNotNull(compiler,"tests require a JDK");
        List<String> args=List.of("--release",Integer.toString(release),"-encoding","UTF-8","-g","-parameters","-classpath",
                System.getProperty("surefire.test.class.path",System.getProperty("java.class.path")),"-d",classes.toString());
        List<Path> files=new ArrayList<>();
        for(var source:sources.entrySet()) {
            Path file=directory.resolve(source.getKey());Files.createDirectories(file.getParent());Files.writeString(file,source.getValue(),StandardCharsets.UTF_8);files.add(file);
        }
        StringWriter diagnostics=new StringWriter();
        try(var manager=compiler.getStandardFileManager(null,Locale.ROOT,StandardCharsets.UTF_8)) {
            assertTrue(compiler.getTask(diagnostics,manager,null,args,null,manager.getJavaFileObjectsFromPaths(files)).call(),diagnostics.toString());
        }
        return classes;
    }
}
