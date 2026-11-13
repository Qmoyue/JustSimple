package io.just.input;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.jar.Manifest;
import java.util.zip.*;
import java.util.concurrent.CancellationException;
import org.objectweb.asm.ClassReader;

/** One scan owns this bounded byte snapshot and its lazily read platform archives. */
public final class Inputs implements AutoCloseable {
    public enum Role { TARGET, DEPENDENCY, PLATFORM }
    public record Artifact(int id, String location, Role role) {}
    public record ClassData(String name, byte[] bytes, Artifact artifact, String entry, Role scope) {
        public ClassData(String name, byte[] bytes, Artifact artifact, String entry) { this(name, bytes, artifact, entry, artifact.role()); }
        // Bytes belong to the snapshot; the program reader must not mutate them.
        public String source() { return artifact.location() + "!/" + entry; }
    }
    public record Limits(long bytes, int entries, int classes, int depth, int entryBytes) {
        public Limits {
            if (bytes < 1 || entries < 1 || classes < 1 || depth < 0 || entryBytes < 1)
                throw new IllegalArgumentException("input budgets must be positive (depth may be zero)");
        }
        public static Limits defaults() { return new Limits(256L << 20, 150_000, 40_000, 4, 64 << 20); }
    }
    public record Summary(List<Artifact> artifacts, Limits budgets, int applicationClasses, int dependencyClasses,
                          int platformClasses, long bytesRead, int entriesRead, int jdkFeature,
                          List<String> limitations, List<String> duplicates) {}
    /** A read frontier is not evidence that a class is absent. */
    public record Lookup(Optional<ClassData> value, Optional<String> truncated) {}
    public static final class Failure extends RuntimeException {
        public Failure(String message, Exception cause) { super(message, cause); }
    }
    private static final class Exhausted extends IOException {
        Exhausted(String message) { super(message); }
    }
    private record Selected(ClassData data, int version) {}
    private record Nested(Artifact artifact,byte[] bytes) {}
    private record Platform(Artifact artifact, ZipFile zip, String prefix) {}
    private final Limits limits;
    private final Map<String, Selected> classes = new LinkedHashMap<>();
    private final Map<String, ClassData> platformClasses = new HashMap<>();
    private final Map<String, Lookup> reads = new HashMap<>();
    private final Map<String,Boolean> platformTypes = new LinkedHashMap<>();
    private final List<Platform> platform = new ArrayList<>();
    private final List<Artifact> artifacts = new ArrayList<>();
    private final List<String> limitations = new ArrayList<>();
    private final List<String> duplicates = new ArrayList<>();
    private final byte[] readBuffer = new byte[8192];
    private long bytesRead;
    private int entriesRead;
    private int targetClassCount;
    private int feature;

    private Inputs(Limits limits) { this.limits = limits; }

    public static Inputs open(Path target, List<Path> dependencies, Path jdk, Limits limits) throws IOException {
        interrupted();
        Inputs inputs = new Inputs(limits);
        try {
            inputs.openPlatform(jdk.toRealPath());
            try {
                inputs.load(target.toRealPath(), Role.TARGET);
                for (Path dependency : dependencies) inputs.load(dependency.toRealPath(), Role.DEPENDENCY);
            } catch (Exhausted limit) {
                inputs.limitations.add(limit.getMessage());
            }
            for (Selected selected : inputs.classes.values()) {
                if (selected.data().scope() == Role.TARGET) inputs.targetClassCount++;
            }
            return inputs;
        } catch (IOException | RuntimeException failure) {
            try { inputs.close(); } catch (IOException closing) { failure.addSuppressed(closing); }
            throw failure;
        }
    }

    private Artifact artifact(String path, Role role) {
        Artifact artifact = new Artifact(artifacts.size(), path, role);
        artifacts.add(artifact);
        return artifact;
    }

    private void openPlatform(Path jdk) throws IOException {
        Properties release = new Properties();
        try (Reader reader = Files.newBufferedReader(jdk.resolve("release"),StandardCharsets.UTF_8)) { release.load(reader); }
        String version = release.getProperty("JAVA_VERSION", "").replace("\"", "");
        String[] parts = version.split("[._+\\-]");
        try { feature = Integer.parseInt(parts[0].equals("1") ? parts[1] : parts[0]); }
        catch (NumberFormatException | ArrayIndexOutOfBoundsException invalid) {
            throw new IOException("invalid target JDK release: " + jdk, invalid);
        }
        Path rt = jdk.resolve("jre/lib/rt.jar");
        if (!Files.isRegularFile(rt)) rt = jdk.resolve("lib/rt.jar");
        if (Files.isRegularFile(rt)) {
            Path library = rt.getParent();
            for (String name : List.of("rt.jar", "jce.jar", "jsse.jar", "charsets.jar")) {
                Path path = library.resolve(name);
                if (Files.isRegularFile(path)) addPlatform(path, "");
            }
        } else {
            Path modules = jdk.resolve("jmods");
            if (Files.isDirectory(modules)) {
                try (var files = Files.list(modules)) {
                    for (Path path : files.filter(p -> p.toString().endsWith(".jmod")).sorted().toList())
                        addPlatform(path, "classes/");
                }
            }
            if (platform.isEmpty()) throw new IOException("target JDK needs rt.jar or jmods: " + jdk);
        }
    }

    private void addPlatform(Path path, String prefix) throws IOException {
        interrupted();
        platform.add(new Platform(artifact(path.toString(), Role.PLATFORM), new ZipFile(path.toFile(),StandardCharsets.UTF_8), prefix));
    }

    private void load(Path path, Role role) throws IOException {
        Artifact artifact = artifact(path.toString(), role);
        if (Files.isDirectory(path)) {
            try (var paths = Files.walk(path)) {
                Iterator<Path> iterator = paths.iterator();
                while (iterator.hasNext()) {
                    interrupted();
                    Path member = iterator.next();
                    if (member.equals(path)) continue;
                    entry();
                    if (Files.isSymbolicLink(member)) throw new IOException("linked input member: " + member);
                    if (!Files.isRegularFile(member) || !member.toString().endsWith(".class")) continue;
                    String name = path.relativize(member).toString().replace('\\', '/');
                    try (InputStream in = Files.newInputStream(member)) {
                        select(name, read(in), artifact, 0);
                    }
                }
            }
        } else if (path.getFileName().toString().toLowerCase(Locale.ROOT).endsWith(".class")) {
            entry();
            try (InputStream in = Files.newInputStream(path)) {
                byte[] bytes = read(in);
                String name;
                try { name = new ClassReader(bytes).getClassName(); }
                catch (IllegalArgumentException | ArrayIndexOutOfBoundsException invalid) {
                    throw new IOException("invalid class file: " + path, invalid);
                }
                select(name + ".class", bytes, artifact, 0);
            }
        } else {
            try (InputStream in = Files.newInputStream(path)) { archive(in, artifact, 0); }
        }
    }

    private void archive(InputStream in, Artifact artifact, int depth) throws IOException {
        if (depth > limits.depth()) throw new Exhausted("nested archive depth budget: " + artifact.location());
        Map<String, Selected> members = new LinkedHashMap<>();
        List<Nested> nestedArchives = new ArrayList<>();
        boolean multiRelease = false;
        try (ZipInputStream zip = new ZipInputStream(in,StandardCharsets.UTF_8);
             OutputStream discard = OutputStream.nullOutputStream()) {
            boolean any = false;
            for (ZipEntry member; (member = zip.getNextEntry()) != null;) {
                any = true;
                entry();
                String path = member.getName();
                // Advancing the ZIP stream would otherwise drain skipped entries outside the budget.
                boolean retained=path.equalsIgnoreCase("META-INF/MANIFEST.MF") || path.endsWith(".jar") || path.endsWith(".class");
                if(!retained){transfer(zip,discard);continue;}
                byte[] bytes = read(zip);
                if (path.equalsIgnoreCase("META-INF/MANIFEST.MF")) {
                    multiRelease = "true".equalsIgnoreCase(new Manifest(new ByteArrayInputStream(bytes))
                            .getMainAttributes().getValue("Multi-Release"));
                }
                if (path.endsWith(".jar")) {
                    Artifact nested = artifact(artifact.location() + "!/" + path, Role.DEPENDENCY);
                    nestedArchives.add(new Nested(nested,bytes));
                } else if (path.endsWith(".class")) {
                    int version = 0;
                    String logical = path;
                    if (path.startsWith("META-INF/versions/")) {
                        String[] split = path.split("/", 4);
                        if (split.length != 4) throw new IOException("invalid versioned class entry: " + path);
                        try { version = Integer.parseInt(split[2]); }
                        catch (NumberFormatException bad) { throw new IOException("invalid class version entry: " + path, bad); }
                        logical = split[3];
                    }
                    if (version > feature) continue;
                    String key = version + ":" + logical;
                    if (members.putIfAbsent(key, new Selected(new ClassData(logical, bytes, artifact, path), version)) != null)
                        throw new IOException("duplicate archive member: " + artifact.location() + "!/" + path);
                    if (members.size() + classes.size() > limits.classes())
                        throw new Exhausted("class entry budget in " + artifact.location());
                }
            }
            if (!any) throw new IOException("empty or invalid archive: " + artifact.location());
        } catch(Exhausted budget) {
            try{selectMembers(members,multiRelease,artifact);}
            catch(Exhausted selection){budget.addSuppressed(selection);limitations.add(selection.getMessage());}
            throw budget;
        } catch(IOException failure) {
            throw new IOException("reading archive "+artifact.location()+": "+failure.getMessage(),failure);
        }
        selectMembers(members,multiRelease,artifact);
        // Preserve enclosing application classes before libraries can consume the class budget.
        // Retained archive bytes have already been charged to the input byte budget.
        for(Nested nested:nestedArchives)archive(new ByteArrayInputStream(nested.bytes()),nested.artifact(),depth+1);
    }

    private void selectMembers(Map<String,Selected> members,boolean multiRelease,Artifact artifact) throws Exhausted {
        boolean packagedApplication=members.values().stream().anyMatch(s -> s.data().name().startsWith("BOOT-INF/classes/") || s.data().name().startsWith("WEB-INF/classes/"));
        for(Selected selected:members.values())if(selected.version()==0 || multiRelease) {
            ClassData data=selected.data();boolean applicationClass=data.name().startsWith("BOOT-INF/classes/") || data.name().startsWith("WEB-INF/classes/");
            Role scope=artifact.role()==Role.TARGET && packagedApplication && !applicationClass?Role.DEPENDENCY:artifact.role();
            select(data.name(),data.bytes(),artifact,selected.version(),scope);
        }
    }

    private void select(String path, byte[] bytes, Artifact artifact, int version) throws Exhausted {
        select(path, bytes, artifact, version, artifact.role());
    }
    private void select(String path, byte[] bytes, Artifact artifact, int version, Role scope) throws Exhausted {
        String logical = path.replaceFirst("^(BOOT-INF|WEB-INF)/classes/", "");
        if (logical.equals("module-info.class") || logical.startsWith("META-INF/")) return;
        String name = logical.substring(0, logical.length() - 6);
        Selected old = classes.get(name);
        ClassData data = new ClassData(name, bytes, artifact, path, scope);
        if (old == null) {
            if (classes.size() + platformClasses.size() >= limits.classes())
                throw new Exhausted("loaded class budget: " + limits.classes());
            classes.put(name, new Selected(data, version));
        } else if (old.data().artifact().equals(artifact) && old.data().scope() == scope && old.version() < version) {
            classes.put(name, new Selected(data, version));
        } else if (old.data().scope() == Role.DEPENDENCY && scope == Role.TARGET) {
            classes.put(name, new Selected(data, version));
        } else if (!old.data().artifact().equals(artifact) && duplicates.size() < 100) {
            duplicates.add(name + ": retained " + old.data().source() + ", ignored " + data.source());
        }
    }

    private void entry() throws Exhausted {
        interrupted();
        if (++entriesRead > limits.entries()) throw new Exhausted("input entry budget: " + limits.entries());
    }

    private byte[] read(InputStream in) throws IOException {
        ByteArrayOutputStream out=new ByteArrayOutputStream();transfer(in,out);return out.toByteArray();
    }
    private void transfer(InputStream in,OutputStream out) throws IOException {
        long size=0;
        for(int count;(count=in.read(readBuffer))!=-1;) {
            interrupted();
            bytesRead+=count;size+=count;
            if(bytesRead>limits.bytes())throw new Exhausted("input expanded byte budget: "+limits.bytes());
            if(size>limits.entryBytes())throw new Exhausted("input member byte budget: "+limits.entryBytes());
            out.write(readBuffer,0,count);
        }
    }

    public List<ClassData> candidateClasses() { return classes.values().stream().map(Selected::data).toList(); }

    public List<ClassData> targetClasses() {
        return classes.values().stream().map(Selected::data).filter(c -> c.scope() == Role.TARGET).toList();
    }

    public Optional<ClassData> find(String name) { return lookup(name).value(); }

    /** Check class ownership from archive metadata without reading bytes or consuming input budgets. */
    public boolean platformType(String name) {
        if(classes.containsKey(name))return false;
        if(platformClasses.containsKey(name))return true;
        Boolean known=platformTypes.get(name);if(known!=null)return known;
        boolean present=platform.stream().anyMatch(source -> source.zip().getEntry(source.prefix()+name+".class")!=null);
        if(platformTypes.size()>=8192)platformTypes.remove(platformTypes.keySet().iterator().next());
        platformTypes.put(name,present);return present;
    }

    public Lookup lookup(String name) {
        interrupted();
        Lookup existing=reads.get(name);
        if(existing!=null)return existing;
        Lookup result=readClass(name);reads.put(name,result);return result;
    }

    private Lookup readClass(String name) {
        Selected selected = classes.get(name);
        if (selected != null) return new Lookup(Optional.of(selected.data()),Optional.empty());
        if (platformClasses.containsKey(name)) return new Lookup(Optional.of(platformClasses.get(name)),Optional.empty());
        try {
            for (Platform source : platform) {
                ZipEntry entry = source.zip().getEntry(source.prefix() + name + ".class");
                if (entry == null) continue;
                entry();
                if (classes.size() + platformClasses.size() >= limits.classes()) throw new Exhausted("loaded class budget");
                try (InputStream in = source.zip().getInputStream(entry)) {
                    ClassData data = new ClassData(name, read(in), source.artifact(), entry.getName());
                    platformClasses.put(name, data);
                    return new Lookup(Optional.of(data),Optional.empty());
                }
            }
            return new Lookup(Optional.empty(),limitations.isEmpty()?Optional.empty():Optional.of(String.join("; ",limitations)));
        } catch (Exhausted limit) {
            if (!limitations.contains(limit.getMessage())) limitations.add(limit.getMessage());
            return new Lookup(Optional.empty(),Optional.of(limit.getMessage()));
        } catch (IOException failure) { throw new Failure("reading platform class " + name, failure); }
    }

    public Summary summary() {
        return new Summary(List.copyOf(artifacts), limits, targetClassCount, classes.size() - targetClassCount, platformClasses.size(),
                bytesRead, entriesRead, feature, List.copyOf(limitations), List.copyOf(duplicates));
    }

    private static void interrupted() {
        if(Thread.currentThread().isInterrupted())throw new CancellationException("input read interrupted");
    }

    @Override public void close() throws IOException {
        IOException failure = null;
        for (Platform source : platform) {
            try { source.zip().close(); }
            catch (IOException closing) {
                if (failure == null) failure = closing; else failure.addSuppressed(closing);
            }
        }
        if (failure != null) throw failure;
    }
}
