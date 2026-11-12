package io.just.knowledge;

import com.google.gson.*;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;
import com.google.gson.stream.JsonWriter;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.Hint;
import java.io.*;
import java.net.URL;
import java.net.URLConnection;
import java.nio.charset.StandardCharsets;
import java.nio.charset.CharacterCodingException;
import java.nio.ByteBuffer;
import java.nio.file.*;
import java.util.*;

/** Immutable reference material. Only typed source relations can participate in exploration. */
public final class Catalog {
    public record Entry(String id,String category,String pointer) {}
    private sealed interface Definition permits Inline,Encoded {CallShape.Signature target();CallShape.Pattern value();}
    private record Source(Entry entry,int relation) {}
    private static final class Shape {
        private final Definition definition;private final List<Source> locations;
        private Optional<List<Mechanisms.Reference>> references=Optional.empty();
        Shape(Definition definition,List<Source> locations){this.definition=definition;this.locations=List.copyOf(locations);}
        Definition definition(){return definition;}
        List<Mechanisms.Reference> sources(String file) {
            if(references.isEmpty()) {
                List<Mechanisms.Reference> values=new ArrayList<>();
                for(Source source:locations)values.add(new Mechanisms.Reference(source.entry().id(),new StringBuilder(file).append('#').append(source.entry().pointer()).append("/relations/").append(source.relation()).toString()));
                references=Optional.of(List.copyOf(values));
            }
            return references.orElseThrow();
        }
    }
    private sealed interface PatternReference permits Inline,Shared {}
    private record Inline(CallShape.Pattern value) implements PatternReference,Definition {public CallShape.Signature target(){return value.target();}}
    private record Shared(int index) implements PatternReference {}
    private record Use(int pattern,int reference) {
        @Override public int hashCode(){return pattern*31+reference;}
        @Override public boolean equals(Object other){return other instanceof Use value && pattern==value.pattern && reference==value.reference;}
    }
    private record Pending(PatternReference pattern,int row,int reference) {}
    private record Owned(String entry,List<Pending> relations) {}
    private record Material(URL resource,String location) {}
    private final Map<String,Entry> entries;
    private final Map<CallShape.Signature,List<Shape>> calls;
    private final List<Definition> definitions;
    private final String source,snapshot;
    private final Optional<Material> referenceMaterial;
    private Optional<JsonObject> material=Optional.empty();
    private Catalog(Map<String,Entry> entries,Map<CallShape.Signature,List<Shape>> calls,String source,String snapshot,Optional<Material> referenceMaterial,List<Definition> definitions) {
        this.entries=Collections.unmodifiableMap(new LinkedHashMap<>(entries));this.calls=Map.copyOf(calls);this.source=source;this.snapshot=snapshot;this.referenceMaterial=referenceMaterial;this.definitions=List.copyOf(definitions);
    }
    public static Catalog empty(){return new Catalog(Map.of(),Map.of(),"no reference corpus","{}",Optional.empty(),List.of());}
    public Collection<Entry> entries(){return entries.values();}
    public Optional<Entry> entry(String id){return Optional.ofNullable(entries.get(id));}
    /** Restrict guidance by reference identity; decoded structures and source attribution stay shared. */
    public Catalog select(Set<String> ids) {
        for(String id:ids)if(!entries.containsKey(id))throw new IllegalArgumentException("unknown reference: "+id);
        Map<String,Entry> selected=new LinkedHashMap<>();
        entries.forEach((id,entry) -> {if(ids.contains(id))selected.put(id,entry);});
        Map<CallShape.Signature,List<Shape>> filtered=new LinkedHashMap<>();
        calls.forEach((signature,shapes) -> {
            List<Shape> kept=new ArrayList<>();
            for(Shape shape:shapes) {
                List<Source> locations=shape.locations.stream().filter(s -> ids.contains(s.entry().id())).toList();
                if(!locations.isEmpty())kept.add(new Shape(shape.definition(),locations));
            }
            if(!kept.isEmpty())filtered.put(signature,List.copyOf(kept));
        });
        return new Catalog(selected,filtered,source,snapshot,referenceMaterial,definitions);
    }
    public String material(String id)throws IOException {
        Entry entry=entries.get(id);if(entry==null)throw new IllegalArgumentException("unknown reference: "+id);
        if(material.isEmpty()) {
            String raw=snapshot;
            if(referenceMaterial.isPresent()) {
                Material item=referenceMaterial.get();raw=readResource(item.resource(),item.location());
            }
            try {
                JsonObject parsed=JsonParser.parseString(raw).getAsJsonObject();
                if(referenceMaterial.isPresent()) {
                    JsonObject active=JsonParser.parseString(snapshot).getAsJsonObject();
                    for(String group:List.of("chains","fragments","bytecodeObservations"))for(int i=0;i<active.getAsJsonArray(group).size();i++) {
                        JsonObject entryValue=active.getAsJsonArray(group).get(i).getAsJsonObject(),original=parsed.getAsJsonArray(group).get(i).getAsJsonObject();
                        if(!entryValue.get("id").equals(original.get("id")))throw new IOException("reference material identity differs at /"+group+"/"+i);
                        if(!original.has("relations"))original.add("relations",entryValue.getAsJsonArray("relations"));
                    }
                }
                material=Optional.of(parsed);
            }
            catch(JsonParseException|IllegalStateException|ClassCastException|NullPointerException|IndexOutOfBoundsException invalid){throw new IOException("invalid reference material for "+id+" at "+referenceMaterial.map(Material::location).orElse(source),invalid);}
        }
        String[] pointer=entry.pointer().split("/");JsonObject value=material.orElseThrow().getAsJsonArray(pointer[1]).get(Integer.parseInt(pointer[2])).getAsJsonObject();
        if(!value.get("id").getAsString().equals(id))throw new IOException("reference material identity differs at "+entry.pointer());
        return referenceMaterial.isPresent()?value.toString():expanded(value,id);
    }
    private String expanded(JsonObject value,String id)throws IOException {
        StringBuilder text=new StringBuilder();
        Writer limited=new Writer() {
            @Override public void write(char[] chars,int offset,int length)throws IOException {
                if((long)text.length()+length>16*1024*1024)throw new IOException("reference material output exceeds 16 Mi characters: "+id);
                text.append(chars,offset,length);
            }
            @Override public void flush() {}
            @Override public void close() {}
        };
        Gson json=new GsonBuilder().serializeNulls().create();JsonWriter out=new JsonWriter(limited);
        try {
            out.beginObject();
            for(var field:value.entrySet()) {
                out.name(field.getKey());
                if(!field.getKey().equals("relations")){json.toJson(field.getValue(),out);continue;}
                out.beginArray();for(JsonElement item:field.getValue().getAsJsonArray()) {
                    JsonObject relation;
                    if(item.isJsonPrimitive()){relation=new JsonObject();relation.add("pattern",item);}
                    else relation=item.getAsJsonObject();
                    out.beginObject();for(var detail:relation.entrySet()) {
                        out.name(detail.getKey());
                        if(detail.getKey().equals("pattern") && detail.getValue().isJsonPrimitive())
                            json.toJson(definitions.get(detail.getValue().getAsInt()).value(),CallShape.Pattern.class,out);
                        else json.toJson(detail.getValue(),out);
                    }out.endObject();
                }out.endArray();
            }
            out.endObject();out.flush();return text.toString();
        } catch(JsonIOException failure) {
            if(failure.getCause() instanceof IOException io)throw io;
            throw new IOException("cannot render reference material: "+id,failure);
        }
    }
    public static Catalog read(Path file) throws IOException {
        if(Files.size(file)>16*1024*1024)throw new IOException("reference corpus exceeds 16 MiB: "+file);
        Path absolute=file.toAbsolutePath();return read(readResource(absolute.toUri().toURL(),absolute.toString()),absolute.toString(),Optional.of(absolute));
    }
    public static Catalog builtin() throws IOException {
        String name="reference-knowledge.json",source="classpath:/io/just/knowledge/"+name;
        URL resource=Catalog.class.getResource(name);if(resource==null)throw new IOException("missing built-in reference corpus: "+source);
        return read(readResource(resource,source),source,Optional.empty());
    }
    private static String readResource(URL resource,String location)throws IOException {
        URLConnection connection=resource.openConnection();connection.setUseCaches(false);
        try(InputStream input=connection.getInputStream()) {
            byte[] bytes=input.readNBytes(16*1024*1024+1);
            if(bytes.length>16*1024*1024)throw new IOException("reference data exceeds 16 MiB: "+location);
            try{return StandardCharsets.UTF_8.newDecoder().decode(ByteBuffer.wrap(bytes)).toString();}
            catch(CharacterCodingException invalid){throw new IOException("reference data is not UTF-8: "+location,invalid);}
        }
    }
    private static Catalog read(String snapshot,String source,Optional<Path> file) throws IOException {
        String location="root";
        JsonReader reader=new JsonReader(new StringReader(snapshot));
        try(reader) {
        try {
            Map<String,Entry> entries=new LinkedHashMap<>();List<Shape> patterns=new ArrayList<>();Map<Integer,List<Source>> sharedSources=new LinkedHashMap<>();
            List<Definition> shared=new ArrayList<>();List<Owned> owned=new ArrayList<>();List<int[]> encoded=new ArrayList<>();List<CallShape.Signature> signatures=new ArrayList<>();List<String> types=new ArrayList<>();
            String schema="";Optional<Material> materialFile=Optional.empty();Set<String> groups=new HashSet<>();int count=0;reader.beginObject();
            while(reader.hasNext()) {
                String group=reader.nextName();
                if(!groups.add(group))throw new IllegalArgumentException("duplicate root field: "+group);
                if(group.equals("patterns")) {
                    reader.beginArray();while(reader.hasNext()) {
                        location=at("/patterns",shared.size());if(shared.size()>=16384)throw new IllegalArgumentException("reference pattern budget (16384)");
                        CallShape.Pattern pattern=pattern(reader);validate(pattern);shared.add(new Inline(pattern));
                    }
                    reader.endArray();continue;
                }
                if(group.equals("encodedPatterns")) {
                    location="/encodedPatterns";reader.beginArray();while(reader.hasNext()){if(encoded.size()>=16384)throw new IllegalArgumentException("reference pattern budget (16384)");encoded.add(integers(reader));}reader.endArray();continue;
                }
                if(group.equals("signatures")) {reader.beginArray();while(reader.hasNext()){if(signatures.size()>=16384)throw new IllegalArgumentException("signature table budget");signatures.add(signature(reader));}reader.endArray();continue;}
                if(group.equals("types")) {reader.beginArray();while(reader.hasNext()){if(types.size()>=16384)throw new IllegalArgumentException("source type table budget");types.add(reader.nextString());}reader.endArray();continue;}
                if(group.equals("schema")){schema=reader.nextString();continue;}
                if(group.equals("referenceMaterial")) {
                    String name=reader.nextString();
                    if(file.isPresent()) {
                        Path path=file.get().getParent().resolve(name).normalize();
                        if(Files.size(path)>16*1024*1024)throw new IOException("reference material exceeds 16 MiB: "+path);
                        materialFile=Optional.of(new Material(path.toUri().toURL(),path.toString()));
                    } else {
                        URL resource=Catalog.class.getResource(name);
                        if(resource==null)throw new IOException("missing built-in reference material: "+name);
                        materialFile=Optional.of(new Material(resource,"classpath:/io/just/knowledge/"+name));
                    }
                    continue;
                }
                if(!Set.of("chains","fragments","bytecodeObservations").contains(group)){reader.skipValue();continue;}
                reader.beginArray();int index=0;String parent="/".concat(group);
                while(reader.hasNext()) {
                    String pointer=at(parent,index++);location=pointer;String id="",category=group;
                    List<Pending> relations=new ArrayList<>();Set<Use> uses=new HashSet<>();reader.beginObject();
                    while(reader.hasNext()) {
                        String field=reader.nextName();
                        if(field.equals("id"))id=reader.nextString();
                        else if(field.equals("kind") && group.equals("fragments"))category=reader.nextString();
                        else if(field.equals("relations")) {
                            location=pointer.concat("/relations");reader.beginArray();int relation=0;
                            while(reader.hasNext()) {
                                if(++count>16384)throw new IllegalArgumentException("reference relation budget (16384)");
                                Pending next=relation(reader,relation++);
                                if(!(next.pattern() instanceof Shared value) || uses.add(new Use(value.index(),next.reference())))relations.add(next);
                            }
                            reader.endArray();
                        } else if(field.equals("referenceHops")) {
                            if(reader.peek()==JsonToken.NULL)reader.nextNull();
                            else {reader.beginArray();while(reader.hasNext())reader.skipValue();reader.endArray();}
                        } else reader.skipValue();
                    }
                    reader.endObject();Entry entry=new Entry(id,category,pointer);
                    if(id.isBlank() || entries.putIfAbsent(id,entry)!=null)throw new IllegalArgumentException("empty/duplicate reference identity: "+id);
                    if(entries.size()>4096)throw new IllegalArgumentException("reference entry budget (4096)");
                    owned.add(new Owned(id,List.copyOf(relations)));
                }
                reader.endArray();
            }
            reader.endObject();if(reader.peek()!=JsonToken.END_DOCUMENT)throw new IllegalArgumentException("trailing reference data");
            if(!groups.containsAll(Set.of("chains","fragments","bytecodeObservations")))throw new IllegalArgumentException("missing reference arrays");
            if(!schema.equals("just.local-reference/v1"))throw new IllegalArgumentException("unsupported reference schema");
            if(groups.contains("patterns") && groups.contains("encodedPatterns"))throw new IllegalArgumentException("multiple pattern encodings");
            signatures=List.copyOf(signatures);types=List.copyOf(types);
            for(int i=0;i<encoded.size();i++){location=at("/encodedPatterns",i);shared.add(new Encoded(encoded.get(i),signatures,types));}
            for(Owned owner:owned) {
                for(Pending relation:owner.relations()) {
                    Entry entry=entries.get(owner.entry());
                    Source reference=new Source(entry,relation.reference());
                    if(relation.pattern() instanceof Inline inline)patterns.add(new Shape(inline,List.of(reference)));
                    else {
                        int index=((Shared)relation.pattern()).index();if(index<0 || index>=shared.size()){location=at(entry.pointer().concat("/relations"),relation.row());throw new IllegalArgumentException("unknown shared pattern: "+index);}
                        List<Source> sources=sharedSources.get(index);
                        if(sources==null){sources=new ArrayList<>();sharedSources.put(index,sources);}sources.add(reference);
                    }
                }
            }
            for(var item:sharedSources.entrySet())patterns.add(new Shape(shared.get(item.getKey()),item.getValue()));
            Map<CallShape.Signature,List<Shape>> calls=new LinkedHashMap<>();
            for(Shape shape:patterns) {
                List<Shape> shapes=calls.get(shape.definition().target());
                if(shapes==null){shapes=new ArrayList<>();calls.put(shape.definition().target(),shapes);}shapes.add(shape);
            }
            for(var item:calls.entrySet())item.setValue(List.copyOf(item.getValue()));
            return new Catalog(entries,calls,source,snapshot,materialFile,shared);
        } catch(JsonParseException|IllegalArgumentException|IllegalStateException|NullPointerException|com.google.gson.stream.MalformedJsonException|EOFException malformed) {
            String inputPath=reader.getPath().substring(1).replace('.', '/').replace('[','/').replace("]","");
            throw new IOException("invalid reference corpus "+source+" at "+location+"; input "+inputPath+": "+malformed.getMessage(),malformed);
        }
        }
    }
    private static String at(String parent,int index){return new StringBuilder(parent).append('/').append(index).toString();}
    private static int[] integers(JsonReader reader)throws IOException {
        int[] values=new int[32];int size=0;reader.beginArray();
        while(reader.hasNext()) {
            if(size>=65536)throw new IllegalArgumentException("encoded pattern size budget (65536)");
            if(size==values.length)values=Arrays.copyOf(values,values.length*2);values[size++]=reader.nextInt();
        }
        reader.endArray();return Arrays.copyOf(values,size);
    }
    private static final class Cursor {
        final int[] data;int at;
        Cursor(int[] data){this.data=data;}
        int next(){if(at>=data.length)throw new IllegalArgumentException("truncated pattern");return data[at++];}
        int count(int maximum){int value=next();if(value<0 || value>maximum)throw new IllegalArgumentException("invalid pattern count/code: "+value);return value;}
        int index(int size){int value=next();if(value<0 || value>=size)throw new IllegalArgumentException("unknown pattern table entry: "+value);return value;}
        void end(){if(at!=data.length)throw new IllegalArgumentException("trailing pattern data");}
    }
    /** Validated wire data is decoded once, only for an actually queried invocation role. */
    private static final class Encoded implements Definition {
        private final int[] data;private final List<CallShape.Signature> signatures;private final List<String> types;private final CallShape.Signature target;
        private Optional<CallShape.Pattern> decoded=Optional.empty();
        Encoded(int[] data,List<CallShape.Signature> signatures,List<String> types) {
            this.data=data;this.signatures=signatures;this.types=types;Cursor in=new Cursor(data);target=signatures.get(in.index(signatures.size()));int opcode=in.next();
            if(opcode<182 || opcode>186)throw new IllegalArgumentException("invalid invocation opcode");
            int operands=in.count(256);if(operands!=org.objectweb.asm.Type.getArgumentTypes(target.descriptor()).length+1)throw new IllegalArgumentException("operand count differs from invocation descriptor");
            boolean linked=false,constant=false;int direct=0;
            for(int i=0;i<operands;i++) {
                int value=in.next(),parameter=in.next();if(value < -1 || value>=operands || parameter < -1)throw new IllegalArgumentException("invalid source value/parameter");
                int steps=in.count(9);boolean known=true;
                for(int s=0;s<steps;s++) {
                    int kind=in.count(7);in.index(types.size());in.next();int calls=in.count(1);if(calls==1)in.index(signatures.size());
                    if(kind==CallShape.SourceKind.ABSENT.ordinal() || kind==CallShape.SourceKind.UNKNOWN.ordinal())known=false;
                    linked|=kind==CallShape.SourceKind.FIELD.ordinal() || kind==CallShape.SourceKind.ELEMENT.ordinal() || kind==CallShape.SourceKind.RETURN.ordinal() || kind==CallShape.SourceKind.ALLOCATION.ordinal();
                    constant|=kind==CallShape.SourceKind.CONSTANT.ordinal();
                }
                if(known)direct++;
            }
            int results=in.count(256);
            for(int i=0;i<results;i++){in.count(4);in.next();if(in.count(1)==1)in.index(signatures.size());}
            int guards=in.count(3);for(int i=0;i<guards;i++)in.count(2);in.end();
            if(!CallShape.Pattern.relevant(target,opcode,results,linked,direct,constant))throw new IllegalArgumentException("relation has no source or result consumer");
        }
        public CallShape.Signature target(){return target;}
        public CallShape.Pattern value() {
            if(decoded.isPresent())return decoded.get();
            Cursor in=new Cursor(data);in.next();int opcode=in.next(),count=in.next();List<CallShape.Operand> operands=new ArrayList<>();
            for(int i=0;i<count;i++) {
                int value=in.next(),parameter=in.next(),steps=in.next();List<CallShape.Step> source=new ArrayList<>();
                for(int s=0;s<steps;s++){var kind=CallShape.SourceKind.values()[in.next()];String type=types.get(in.next());int slot=in.next();var calls=in.next()==0?List.<CallShape.Signature>of():List.of(signatures.get(in.next()));source.add(new CallShape.Step(kind,type,slot,calls));}
                operands.add(new CallShape.Operand(value,parameter,source));
            }
            count=in.next();List<CallShape.Destination> result=new ArrayList<>();
            for(int i=0;i<count;i++){var kind=CallShape.UseKind.values()[in.next()];int operand=in.next();var calls=in.next()==0?List.<CallShape.Signature>of():List.of(signatures.get(in.next()));result.add(new CallShape.Destination(kind,operand,calls));}
            count=in.next();Set<GuardKind> guards=new LinkedHashSet<>();for(int i=0;i<count;i++)guards.add(GuardKind.values()[in.next()]);
            CallShape.Pattern value=new CallShape.Pattern(target,opcode,operands,result,guards);decoded=Optional.of(value);return value;
        }
    }
    private static CallShape.Signature signature(JsonReader reader)throws IOException {
        String owner=null,name=null,descriptor=null;
        if(reader.peek()==JsonToken.BEGIN_ARRAY) {reader.beginArray();owner=reader.nextString();name=reader.nextString();descriptor=reader.nextString();reader.endArray();}
        else {reader.beginObject();
        while(reader.hasNext())switch(reader.nextName()) {
            case "owner" -> owner=reader.nextString();case "name" -> name=reader.nextString();case "descriptor" -> descriptor=reader.nextString();default -> reader.skipValue();
        }
        reader.endObject();}Objects.requireNonNull(owner,"owner");Objects.requireNonNull(name,"name");Objects.requireNonNull(descriptor,"descriptor");
        if(owner.isBlank() || name.isBlank())throw new IllegalArgumentException("empty invocation role");
        try {
            var parameters=org.objectweb.asm.Type.getArgumentTypes(descriptor);var returned=org.objectweb.asm.Type.getReturnType(descriptor);
            if(!org.objectweb.asm.Type.getMethodDescriptor(returned,parameters).equals(descriptor))throw new IllegalArgumentException("invalid method descriptor");
            for(var parameter:parameters)if(parameter.getSort()==org.objectweb.asm.Type.VOID)throw new IllegalArgumentException("invalid method descriptor");
        } catch(IllegalArgumentException|IndexOutOfBoundsException invalid){throw new IllegalArgumentException("invalid relation descriptor: "+descriptor,invalid);}
        return new CallShape.Signature(owner,name,descriptor);
    }
    private static List<CallShape.Signature> signatures(JsonReader reader)throws IOException {
        List<CallShape.Signature> result=new ArrayList<>();reader.beginArray();while(reader.hasNext())result.add(signature(reader));reader.endArray();
        if(result.size()>1)throw new IllegalArgumentException("a producer/destination has at most one invocation");return List.copyOf(result);
    }
    private static Pending relation(JsonReader reader,int row)throws IOException {
        if(reader.peek()==JsonToken.NUMBER)return new Pending(new Shared(reader.nextInt()),row,row);
        PatternReference pattern=null;int reference=row;reader.beginObject();
        while(reader.hasNext())switch(reader.nextName()) {
            case "pattern" -> {
                if(pattern!=null)throw new IllegalArgumentException("duplicate relation pattern");
                if(reader.peek()==JsonToken.NUMBER)pattern=new Shared(reader.nextInt());
                else {CallShape.Pattern value=pattern(reader);validate(value);pattern=new Inline(value);}
            }
            case "reference" -> {reference=reader.nextInt();if(reference<0)throw new IllegalArgumentException("invalid reference index");}
            default -> reader.skipValue();
        }
        reader.endObject();return new Pending(Objects.requireNonNull(pattern,"pattern"),row,reference);
    }
    private static CallShape.Pattern pattern(JsonReader reader)throws IOException {
        CallShape.Signature target=null;Integer opcode=null;List<CallShape.Operand> operands=null;List<CallShape.Destination> result=null;Set<GuardKind> guards=null;
        reader.beginObject();while(reader.hasNext())switch(reader.nextName()) {
            case "target" -> target=signature(reader);case "opcode" -> opcode=reader.nextInt();
            case "operands" -> {operands=new ArrayList<>();reader.beginArray();while(reader.hasNext())operands.add(operand(reader));reader.endArray();}
            case "result" -> {result=new ArrayList<>();reader.beginArray();while(reader.hasNext())result.add(destination(reader));reader.endArray();}
            case "guards" -> {guards=new LinkedHashSet<>();reader.beginArray();while(reader.hasNext())guards.add(GuardKind.valueOf(reader.nextString()));reader.endArray();}
            default -> reader.skipValue();
        }
        reader.endObject();return new CallShape.Pattern(target,Objects.requireNonNull(opcode,"opcode"),operands,result,guards);
    }
    private static CallShape.Operand operand(JsonReader reader)throws IOException {
        Integer value=null,parameter=null;List<CallShape.Step> steps=null;
        reader.beginObject();while(reader.hasNext())switch(reader.nextName()) {
            case "value" -> value=reader.nextInt();case "parameter" -> parameter=reader.nextInt();
            case "steps" -> {steps=new ArrayList<>();reader.beginArray();while(reader.hasNext())steps.add(step(reader));reader.endArray();}
            default -> reader.skipValue();
        }
        reader.endObject();return new CallShape.Operand(Objects.requireNonNull(value,"value"),Objects.requireNonNull(parameter,"parameter"),steps);
    }
    private static CallShape.Step step(JsonReader reader)throws IOException {
        CallShape.SourceKind kind=null;String type=null;Integer slot=null;List<CallShape.Signature> calls=null;
        reader.beginObject();while(reader.hasNext())switch(reader.nextName()) {
            case "kind" -> kind=CallShape.SourceKind.valueOf(reader.nextString());case "type" -> type=reader.nextString();case "slot" -> slot=reader.nextInt();case "call" -> calls=signatures(reader);default -> reader.skipValue();
        }
        reader.endObject();return new CallShape.Step(kind,type,Objects.requireNonNull(slot,"slot"),calls);
    }
    private static CallShape.Destination destination(JsonReader reader)throws IOException {
        CallShape.UseKind kind=null;Integer operand=null;List<CallShape.Signature> calls=null;
        reader.beginObject();while(reader.hasNext())switch(reader.nextName()) {
            case "kind" -> kind=CallShape.UseKind.valueOf(reader.nextString());case "operand" -> operand=reader.nextInt();case "call" -> calls=signatures(reader);default -> reader.skipValue();
        }
        reader.endObject();return new CallShape.Destination(kind,Objects.requireNonNull(operand,"operand"),calls);
    }
    private static void validate(CallShape.Pattern pattern) {
        Objects.requireNonNull(pattern,"pattern");Objects.requireNonNull(pattern.target().owner(),"target.owner");Objects.requireNonNull(pattern.target().name(),"target.name");
        String descriptor=Objects.requireNonNull(pattern.target().descriptor(),"target.descriptor");
        if(!descriptor.startsWith("(") || !descriptor.contains(")") || pattern.opcode()<182 || pattern.opcode()>186)throw new IllegalArgumentException("invalid invocation shape");
        if(pattern.operands().isEmpty() || pattern.operands().size()>256 || pattern.result().size()>256)throw new IllegalArgumentException("invalid operand/result count");
        if(pattern.operands().size()!=org.objectweb.asm.Type.getArgumentTypes(descriptor).length+1)throw new IllegalArgumentException("operand count differs from invocation descriptor");
        for(CallShape.Operand operand:pattern.operands()) {
            if(operand.steps().size()>9 || operand.parameter() < -1 || operand.value() < -1 || operand.value()>=pattern.operands().size())throw new IllegalArgumentException("invalid source path/value");
            for(CallShape.Step step:operand.steps()) {Objects.requireNonNull(step.kind(),"source.kind");Objects.requireNonNull(step.type(),"source.type");Objects.requireNonNull(step.call(),"source.call");}
        }
        if(!pattern.useful())throw new IllegalArgumentException("relation has no source or result consumer");
    }
    boolean applicable(CallShape.Signature signature){return calls.containsKey(signature);}
    boolean emptyRelations(){return calls.isEmpty();}
    public Query<List<Hint>> hints(Program program,Set<MethodId> scope) {
        List<Hint> result=new ArrayList<>();List<QueryIssue> pending=new ArrayList<>();
        for(MethodId method:scope) {
            Query<List<Program.SymbolicCall>> query=program.calls(method);pending.addAll(query.pending());
            Map<Integer,Call> actual=new HashMap<>();
            for(Program.SymbolicCall call:query.value().orElse(List.of())) {
                List<Shape> candidates=calls.getOrDefault(CallShape.signature(call.target()),List.of());if(candidates.isEmpty())continue;
                if(actual.isEmpty()) {
                    Facts facts=program.facts(method);facts.actions().stream().filter(Call.class::isInstance).map(Call.class::cast).forEach(action -> actual.put(action.site().instruction(),action));
                    facts.limitations().stream().filter(l -> l.cause()==CoverageCause.BUDGET).forEach(l -> pending.add(new QueryIssue(QueryCause.BUDGET,l.detail()+": "+method)));
                }
                Call binding=actual.get(call.site().instruction());if(binding==null)continue;
                CallShape.Pattern current=CallShape.of(program,binding);
                Map<CallShape.Pattern,Set<Mechanisms.Reference>> matched=new LinkedHashMap<>();
                for(Shape shape:candidates) {CallShape.Pattern pattern=shape.definition().value();if(CallShape.matches(pattern,current))matched.computeIfAbsent(pattern,k -> new LinkedHashSet<>()).addAll(shape.sources(referenceMaterial.map(Material::location).orElse(source)));}
                for(var match:matched.entrySet()) {
                    List<Mechanisms.Reference> references=List.copyOf(match.getValue());
                    result.add(new Hint(method,"reference:"+references.get(0).entry(),source+"; current ASM site "+call.site(),
                            List.of("current binding, visible slots, path and normal completion remain required"),List.of(new CallShape.Requirement(call.site(),match.getKey())),references));
                    if(result.size()>=4096) {
                        pending.add(new QueryIssue(QueryCause.BUDGET,"reference relation match budget (4096)"));return new Query<>(Optional.of(List.copyOf(result)),List.copyOf(pending));
                    }
                }
            }
        }
        return new Query<>(Optional.of(List.copyOf(result)),List.copyOf(new LinkedHashSet<>(pending)));
    }
}
