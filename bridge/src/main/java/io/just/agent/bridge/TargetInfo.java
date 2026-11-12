package io.just.agent.bridge;

import com.google.gson.Gson;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.zip.*;

/** Bounded classfile-header hints, independent of the user's selected platform. */
public final class TargetInfo {
    private int classes,minimum,multiRelease;
    private boolean partial;
    private static final int LIMIT=40_000;

    public static void main(String[] args)throws IOException {
        System.setErr(new PrintStream(System.err,true,StandardCharsets.UTF_8));
        if(args.length!=1)throw new IllegalArgumentException("expected target path");
        TargetInfo info=new TargetInfo();Path path=Path.of(args[0]).toRealPath();
        if(Files.isDirectory(path)) {
            try(var paths=Files.walk(path)) {
                Iterator<Path> entries=paths.iterator();int visited=0;
                while(entries.hasNext()) {
                    Path entry=entries.next();
                    if(++visited>150_000 || info.classes>=LIMIT){info.partial=true;break;}
                    if(Files.isSymbolicLink(entry))throw new IOException("linked input member: "+entry);
                    if(Files.isRegularFile(entry) && entry.toString().endsWith(".class"))
                        try(InputStream in=Files.newInputStream(entry)){info.header(in,path.relativize(entry).toString().replace('\\','/'));}
                }
            }
        } else if(path.toString().toLowerCase(Locale.ROOT).endsWith(".class")) {
            try(InputStream in=Files.newInputStream(path)){info.header(in,path.getFileName().toString());}
        } else {
            try(ZipFile archive=new ZipFile(path.toFile(),StandardCharsets.UTF_8)) {
                Enumeration<? extends ZipEntry> entries=archive.entries();int visited=0;
                while(entries.hasMoreElements()) {
                    ZipEntry entry=entries.nextElement();
                    if(++visited>150_000 || info.classes>=LIMIT){info.partial=true;break;}
                    if(entry.getName().endsWith(".class"))try(InputStream in=archive.getInputStream(entry)){info.header(in,entry.getName());}
                    else if(entry.getName().endsWith(".jar"))info.partial=true;
                }
            }
        }
        try(PrintWriter out=new PrintWriter(System.out,true,StandardCharsets.UTF_8)) {
            out.println(new Gson().toJson(Map.of("path",path.toString(),"classes",info.classes,"minimumJdk",info.minimum,
                    "multiReleaseMax",info.multiRelease,"partial",info.partial)));
        }
    }
    private void header(InputStream source,String name)throws IOException {
        DataInputStream in=new DataInputStream(source);
        if(in.readInt()!=0xCAFEBABE)throw new IOException("invalid classfile: "+name);
        in.readUnsignedShort();int feature=in.readUnsignedShort()-44;
        if(feature<1)throw new IOException("invalid classfile version: "+name);
        classes++;
        if(name.startsWith("META-INF/versions/"))multiRelease=Math.max(multiRelease,feature);
        else minimum=Math.max(minimum,feature);
    }
}
