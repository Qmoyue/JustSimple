package io.just.agent.bridge;

import com.google.gson.*;
import com.google.gson.stream.*;
import java.io.*;
import java.nio.channels.ClosedByInterruptException;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.CancellationException;

/** Tool-owned evidence files. Only issued references are addressable; reads never accept filesystem paths. */
final class ResultStore implements AutoCloseable {
    @FunctionalInterface interface Write { void to(Writer writer)throws IOException; }
    record Page(String resultRef,List<String> path,String kind,int offset,int next,JsonElement data) {}
    record Selection(String resultRef,List<String> path,List<Integer> deferred,JsonArray data) {}
    private record Stored(Path file,long bytes) {}
    private final Path directory;
    private final String input;
    private final int capacity;
    private final long byteLimit;
    private final Map<String,Stored> files=new LinkedHashMap<>();
    private long bytes;
    private int sequence;

    ResultStore(Path directory,String input,int capacity,long byteLimit)throws IOException {
        if(capacity<1 || byteLimit<1)throw new IllegalArgumentException("result capacity must be positive");
        this.directory=directory;this.input=input;this.capacity=capacity;this.byteLimit=byteLimit;
        Files.createDirectories(directory);
    }
    String save(Write write)throws IOException {
        requireCapacity();
        String ref=input+"/"+(++sequence);Path file=Files.createTempFile(directory,"result-",".json");
        long available=byteLimit-bytes;
        try {
            LimitedOutput output=new LimitedOutput(Files.newOutputStream(file),available);
            try(Writer writer=new BufferedWriter(new OutputStreamWriter(output,StandardCharsets.UTF_8))) {write.to(writer);}
            long size=available-output.remaining;
            files.put(ref,new Stored(file,size));bytes+=size;return ref;
        } catch(IOException|RuntimeException failure) {
            try{Files.deleteIfExists(file);}catch(IOException cleanup){failure.addSuppressed(cleanup);}throw failure;
        }
    }
    void requireCapacity()throws IOException {
        if(files.size()>=capacity || bytes>=byteLimit)throw new IOException("result capacity reached; release unused result references");
    }
    String save(Object value)throws IOException {
        try{return save(writer -> ToolJson.GSON.toJson(value,writer));}
        catch(JsonIOException failure){if(failure.getCause() instanceof IOException)throw new IOException(failure.getMessage(),failure);throw failure;}
    }
    void release(String ref)throws IOException {
        Stored stored=result(ref);
        Files.deleteIfExists(stored.file());
        files.remove(ref);
        bytes-=stored.bytes();
    }
    private Stored result(String ref) {
        Stored stored=files.get(ref);if(stored==null)throw new IllegalArgumentException("unknown or released result reference: "+ref);return stored;
    }
    long export(String ref,Path output,long limit)throws IOException {
        checkCancellation("export");
        Path source=result(ref).file();long size=Files.size(source);
        if(limit<1 || size>limit)throw new IOException("durable evidence exceeds storage budget");
        boolean created = false;
        try (InputStream input = Files.newInputStream(source);
             OutputStream copy = Files.newOutputStream(output, StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE)) {
            created = true;
            long copied = input.transferTo(new LimitedOutput(copy, limit));
            checkCancellation("export");
            return copied;
        } catch (IOException | RuntimeException failure) {
            if (created) try { Files.deleteIfExists(output); }
            catch (IOException cleanup) { failure.addSuppressed(cleanup); }
            if (failure instanceof ClosedByInterruptException interrupted) throw cancelled("export", interrupted);
            throw failure;
        }
    }
    /** Positions come from the retained scan snapshot; IDs are never interpreted as array indexes. */
    Selection select(String ref,List<String> path,Map<Integer,Integer> positions,int limit,int characters)throws IOException {
        if(limit<1 || limit>100 || characters<256 || characters>16000)throw new IllegalArgumentException("invalid selection page budget");
        Set<Integer> remaining=new LinkedHashSet<>(positions.values());JsonArray data=new JsonArray();int available=characters-2;
        try(JsonReader reader=openResult(result(ref).file())) {
            seek(reader,path);reader.beginArray();int index=0;
            while(!remaining.isEmpty() && data.size()<limit && available>0 && reader.hasNext()) {
                Integer id=positions.get(index);
                if(id==null){reader.skipValue();index++;continue;}
                int separator = data.isEmpty() ? 0 : 1;
                JsonElement row=bounded(reader,available-separator);
                if(row==null) row=pointer(path,index,id);
                else if(!row.isJsonObject() || !row.getAsJsonObject().has("id") || row.getAsJsonObject().get("id").getAsInt()!=id)
                    throw new IOException("evidence snapshot and stored record identities differ at "+path+"/"+index);
                int length = row.toString().length() + separator;
                if (length > available) {
                    if (data.isEmpty()) throw new IllegalArgumentException("result path exceeds characters budget");
                    return new Selection(ref,List.copyOf(path),List.copyOf(remaining),data);
                }
                data.add(row);available-=length;remaining.remove(id);index++;
            }
            if(!remaining.isEmpty() && !reader.hasNext())throw new IOException("stored evidence array ends before its scan snapshot");
        }
        return new Selection(ref,List.copyOf(path),List.copyOf(remaining),data);
    }
    Page read(String ref,List<String> path,int offset,int limit,int characters)throws IOException {
        if(offset<0 || limit<1 || limit>100 || characters<256 || characters>16000)throw new IllegalArgumentException("invalid result page budget");
        Path file=result(ref).file();
        try(JsonReader reader=openResult(file)) {
            seek(reader,path);JsonToken kind=reader.peek();
            if(kind==JsonToken.BEGIN_ARRAY) {
                reader.beginArray();int index=0;while(index<offset && reader.hasNext()){reader.skipValue();index++;}
                if(index<offset)throw new IllegalArgumentException("array offset exceeds length");
                JsonArray data=new JsonArray();int remaining=characters-2;
                while(data.size()<limit && remaining>0 && reader.hasNext()) {
                    int separator = data.isEmpty() ? 0 : 1;
                    JsonElement item=bounded(reader,remaining-separator);
                    if(item==null)item=pointer(path,index,null);
                    int length = item.toString().length() + separator;
                    if (length > remaining) {
                        if (data.isEmpty()) throw new IllegalArgumentException("result path exceeds characters budget");
                        return new Page(ref,path,"array",offset,index,data);
                    }
                    data.add(item);remaining-=length;index++;
                }
                return new Page(ref,path,"array",offset,reader.hasNext()?index:-1,data);
            }
            if(kind==JsonToken.STRING) {
                String text=reader.nextString();if(offset>text.length())throw new IllegalArgumentException("string offset exceeds length");
                if(splitsPair(text,offset))throw new IllegalArgumentException("string offset splits a surrogate pair");
                int end=(int)Math.min(text.length(),(long)offset+characters);
                if(splitsPair(text,end))end--;
                return new Page(ref,path,"string",offset,end<text.length()?end:-1,new JsonPrimitive(text.substring(offset,end)));
            }
            if(kind==JsonToken.BEGIN_OBJECT && offset>0)return keys(reader,ref,path,offset,limit,characters);
            if(offset!=0)throw new IllegalArgumentException("offset applies to arrays or strings");
            JsonElement data=bounded(reader,characters);
            if(data!=null)return new Page(ref,path,kind==JsonToken.BEGIN_OBJECT?"object":"scalar",0,-1,data);
        }
        // An oversized object remains addressable; expose its keys rather than a malformed JSON prefix.
        try(JsonReader reader=openResult(file)) {
            seek(reader,path);return keys(reader,ref,path,offset,limit,characters);
        }
    }

    private static JsonObject pointer(List<String> path, int index, Integer id) {
        List<String> location = new ArrayList<>(path);
        location.add(Integer.toString(index));
        JsonObject pointer = new JsonObject();
        if (id != null) pointer.addProperty("id", id);
        pointer.add("path", ToolJson.GSON.toJsonTree(location));
        pointer.addProperty("requiresNarrowerPath", true);
        return pointer;
    }

    private static JsonReader openResult(Path file) throws IOException {
        checkCancellation("read");
        Reader source = new InputStreamReader(Files.newInputStream(file), StandardCharsets.UTF_8.newDecoder());
        return new JsonReader(new FilterReader(source) {
            @Override public int read(char[] chars, int offset, int length) throws IOException {
                checkCancellation("read");
                try { return super.read(chars, offset, length); }
                catch (ClosedByInterruptException interrupted) { throw cancelled("read", interrupted); }
            }
        });
    }

    private static void checkCancellation(String operation) {
        if (Thread.currentThread().isInterrupted()) throw new CancellationException("result " + operation + " interrupted");
    }

    private static CancellationException cancelled(String operation, ClosedByInterruptException interrupted) {
        CancellationException cancelled = new CancellationException("result " + operation + " interrupted");
        cancelled.initCause(interrupted);
        return cancelled;
    }

    private static Page keys(JsonReader reader,String ref,List<String> path,int offset,int limit,int characters)throws IOException {
        reader.beginObject();int index=0,used=2;
        while(index<offset && reader.hasNext()){reader.nextName();reader.skipValue();index++;}
        if(index<offset)throw new IllegalArgumentException("object key offset exceeds length");
        JsonArray keys=new JsonArray();
        while(reader.hasNext() && index-offset<limit) {
            String key=reader.nextName();int length=new JsonPrimitive(key).toString().length()+1;
            if(used+length>characters) {
                if(keys.isEmpty())throw new IllegalArgumentException("object key exceeds characters budget");
                return new Page(ref,path,"object-keys",offset,index,keys);
            }
            keys.add(key);used+=length;index++;reader.skipValue();
        }
        return new Page(ref,path,"object-keys",offset,reader.hasNext()?index:-1,keys);
    }
    private static boolean splitsPair(String text,int index) {
        return index>0 && index<text.length() && Character.isHighSurrogate(text.charAt(index-1)) && Character.isLowSurrogate(text.charAt(index));
    }
    private static void seek(JsonReader reader,List<String> path)throws IOException {
        for(String part:path) {
            if(reader.peek()==JsonToken.BEGIN_OBJECT) {
                reader.beginObject();boolean found=false;
                while(reader.hasNext()){String key=reader.nextName();if(key.equals(part)){found=true;break;}reader.skipValue();}
                if(!found)throw new IllegalArgumentException("unknown result path component: "+part);
            } else if(reader.peek()==JsonToken.BEGIN_ARRAY) {
                int index;
                try{index=Integer.parseInt(part);}catch(NumberFormatException invalid){throw new IllegalArgumentException("array path needs an index: "+part);}
                if(index<0)throw new IllegalArgumentException("negative array index");
                reader.beginArray();int seen=0;while(seen<index && reader.hasNext()){reader.skipValue();seen++;}
                if(!reader.hasNext())throw new IllegalArgumentException("array path exceeds length");
            } else throw new IllegalArgumentException("result path crosses a scalar: "+part);
        }
    }
    private static JsonElement bounded(JsonReader reader,int limit)throws IOException {
        StringWriter text=new StringWriter();boolean[] overflow={false};
        Writer bounded=new Writer() {
            @Override public void write(char[] chars,int offset,int length) {
                if(text.getBuffer().length()+length<=limit && !overflow[0])text.write(chars,offset,length);else overflow[0]=true;
            }
            @Override public void flush() {}
            @Override public void close() {}
        };
        JsonWriter writer=new JsonWriter(bounded);writer.setSerializeNulls(true);copy(reader,writer,overflow);writer.flush();
        return overflow[0]?null:JsonParser.parseString(text.toString());
    }
    private static void copy(JsonReader in,JsonWriter out,boolean[] overflow)throws IOException {
        checkCancellation("read");
        if(overflow[0]){in.skipValue();out.nullValue();return;}
        switch(in.peek()) {
            case BEGIN_OBJECT -> {in.beginObject();out.beginObject();while(in.hasNext()){out.name(in.nextName());copy(in,out,overflow);}in.endObject();out.endObject();}
            case BEGIN_ARRAY -> {in.beginArray();out.beginArray();while(in.hasNext())copy(in,out,overflow);in.endArray();out.endArray();}
            case STRING -> out.value(in.nextString());
            case NUMBER -> out.jsonValue(in.nextString());
            case BOOLEAN -> out.value(in.nextBoolean());
            case NULL -> {in.nextNull();out.nullValue();}
            default -> throw new IOException("unexpected result token: "+in.peek());
        }
    }
    @Override public void close()throws IOException {
        IOException failure=null;
        for(Stored stored:files.values())try{Files.deleteIfExists(stored.file());}catch(IOException problem){if(failure==null)failure=problem;else failure.addSuppressed(problem);}
        files.clear();bytes=0;if(failure!=null)throw failure;
    }
    private static final class LimitedOutput extends FilterOutputStream {
        private long remaining;
        LimitedOutput(OutputStream output,long remaining){super(output);this.remaining=remaining;}
        @Override public void write(byte[] bytes,int offset,int length)throws IOException {
            require(length);out.write(bytes,offset,length);remaining-=length;
        }
        @Override public void write(int c)throws IOException {
            require(1);out.write(c);remaining--;
        }
        private void require(int count)throws IOException {
            checkCancellation("write");
            if(count>remaining)throw new IOException("result storage budget exceeded; release unused results");
        }
    }
}
