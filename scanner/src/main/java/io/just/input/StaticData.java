package io.just.input;

import com.google.gson.*;
import java.io.*;
import java.nio.ByteBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

/** A supplied finite snapshot, never a construction program or a serialized byte stream. */
public record StaticData(String location, String source, Basis basis, Entry entry, List<Node> nodes) {
    private static final Gson JSON = new GsonBuilder().setStrictness(Strictness.STRICT).create();
    private static final int BYTE_LIMIT = 1 << 20;
    private static final int CLASSFILE_ASSIGNMENTS = 2;
    public enum Basis { BINDING, ASSUMPTION, REFERENCE }
    public sealed interface Value permits Reference, ClassLiteral, Scalar {}
    public record Reference(String id,String pointer) implements Value {}
    public record ClassLiteral(String descriptor) implements Value {}
    public record Scalar(Object value) implements Value {}
    public record MethodName(String owner, String name, String descriptor) {}
    public record Entry(MethodName method, Optional<Value> receiver, List<Value> arguments) {}
    public record Field(String owner, String name, String descriptor, Value value,String pointer) {}
    public record AbsentField(String owner,String name,String descriptor,String pointer) {}
    public record ClassData(String owner,boolean present,String pointer) {}
    public record MapEntry(Value key, Value value) {}
    public record ClassFile(String location,byte[] bytes) {}
    public record Node(String id, String type, List<Field> fields, Optional<List<Value>> elements,
                       List<MapEntry> entries, Optional<Value> decoded,Optional<ClassFile> classfile,List<AbsentField> absentFields,List<ClassData> classData,String pointer) {}
    public record Summary(String location, String source, Basis basis, int objects, int assignments, String contract) {}

    public Summary summary() {
        int assignments=nodes.stream().mapToInt(StaticData::assignments).sum();
        return new Summary(location,source,basis,nodes.size(),assignments,
                "BINDING supplies analysis facts checked against bytecode, not evidence that a dynamic stream ran; ASSUMPTION remains conditional; REFERENCE is not seeded");
    }

    private static int assignments(Node node) {
        return node.fields().size() + node.absentFields().size() + node.classData().size() + node.entries().size() * 2
                + node.elements().map(List::size).orElse(0) + (node.classfile().isPresent() ? CLASSFILE_ASSIGNMENTS : 0);
    }

    public static StaticData read(Path path) throws IOException {
        Path manifest=path.toAbsolutePath().normalize();
        byte[] bytes;
        try (InputStream input=Files.newInputStream(manifest)) { bytes=input.readNBytes(BYTE_LIMIT + 1); }
        if (bytes.length>BYTE_LIMIT) throw new IOException("static data exceeds 1 MiB: " + manifest);
        try {
            String json=StandardCharsets.UTF_8.newDecoder().decode(ByteBuffer.wrap(bytes)).toString();
            JsonObject root=object(JSON.fromJson(json,JsonElement.class),"/");
            keys(root,"/","source","basis","entry","objects");
            JsonObject entry=object(root.get("entry"),"/entry");keys(entry,"/entry","owner","name","descriptor","receiver","arguments");
            Entry binding=new Entry(new MethodName(text(entry,"owner","/entry").replace('.','/'),text(entry,"name","/entry"),text(entry,"descriptor","/entry")),
                    entry.has("receiver")?Optional.of(value(entry.get("receiver"),"/entry/receiver")):Optional.empty(),values(array(entry,"arguments","/entry"),"/entry/arguments"));
            JsonArray items=array(root,"objects","");
            if (items.size()>256) throw invalid("/objects","static object budget: 256");
            String source = text(root,"source","");
            Basis basis;
            try { basis=Basis.valueOf(text(root,"basis","")); }
            catch (IllegalArgumentException invalid) { throw invalid("/basis","expected BINDING, ASSUMPTION or REFERENCE"); }
            List<Node> nodes=new ArrayList<>();Set<String> ids=new HashSet<>();
            Map<Integer,String> attachments = new LinkedHashMap<>();
            int assignmentCount = 0;
            for(int index=0;index<items.size();index++) {
                String pointer="/objects/"+index;JsonObject node=object(items.get(index),pointer);keys(node,pointer,"id","type","fields","elements","entries","decoded","classfile","absentFields","classData");
                String id=text(node,"id",pointer);if(!ids.add(id))throw invalid(pointer+"/id","duplicate object id: "+id);
                List<Field> fields=new ArrayList<>();JsonArray definitions=optionalArray(node,"fields",pointer);
                for(int i=0;i<definitions.size();i++) {
                    String at=pointer+"/fields/"+i;JsonObject field=object(definitions.get(i),at);keys(field,at,"owner","name","descriptor","value");
                    fields.add(new Field(text(field,"owner",at).replace('.','/'),text(field,"name",at),text(field,"descriptor",at),value(field.get("value"),at+"/value"),at));
                }
                List<MapEntry> entries=new ArrayList<>();JsonArray pairs=optionalArray(node,"entries",pointer);
                for(int i=0;i<pairs.size();i++) {
                    String at=pointer+"/entries/"+i;JsonObject pair=object(pairs.get(i),at);keys(pair,at,"key","value");
                    entries.add(new MapEntry(value(pair.get("key"),at+"/key"),value(pair.get("value"),at+"/value")));
                }
                List<AbsentField> absentFields=new ArrayList<>();JsonArray absent=optionalArray(node,"absentFields",pointer);
                for(int i=0;i<absent.size();i++) {
                    String at=pointer+"/absentFields/"+i;JsonObject field=object(absent.get(i),at);keys(field,at,"owner","name","descriptor");
                    absentFields.add(new AbsentField(text(field,"owner",at).replace('.','/'),text(field,"name",at),text(field,"descriptor",at),at));
                }
                List<ClassData> classData=new ArrayList<>();JsonArray slots=optionalArray(node,"classData",pointer);
                for(int i=0;i<slots.size();i++) {
                    String at=pointer+"/classData/"+i;JsonObject slot=object(slots.get(i),at);keys(slot,at,"owner","present");
                    JsonElement present=slot.get("present");
                    if(present==null || !present.isJsonPrimitive() || !present.getAsJsonPrimitive().isBoolean())throw invalid(at+"/present","expected boolean");
                    classData.add(new ClassData(text(slot,"owner",at).replace('.','/'),present.getAsBoolean(),at));
                }
                String type=text(node,"type",pointer).replace('.','/');
                boolean attachment = node.has("classfile");
                if(attachment) {
                    if(!type.equals("[B") || node.has("elements") || !fields.isEmpty() || !entries.isEmpty() || node.has("decoded"))throw invalid(pointer+"/classfile","classfile content requires an otherwise empty byte[] node");
                    attachments.put(index, text(node,"classfile",pointer));
                }
                Node parsed = new Node(id,type,List.copyOf(fields),
                        node.has("elements")?Optional.of(values(array(node,"elements",pointer),pointer+"/elements")):Optional.empty(),List.copyOf(entries),
                        node.has("decoded")?Optional.of(value(node.get("decoded"),pointer+"/decoded")):Optional.empty(),Optional.empty(),List.copyOf(absentFields),List.copyOf(classData),pointer);
                assignmentCount += assignments(parsed) + (attachment ? CLASSFILE_ASSIGNMENTS : 0);
                if (assignmentCount>2048) throw invalid("/objects","static assignment budget: 2048");
                nodes.add(parsed);
            }
            List<Value> references=new ArrayList<>(binding.arguments()); binding.receiver().ifPresent(references::add);
            for (Node node:nodes) {
                for (Field field:node.fields()) references.add(field.value());
                node.elements().ifPresent(references::addAll); node.decoded().ifPresent(references::add);
                for (MapEntry pair:node.entries()) { references.add(pair.key()); references.add(pair.value()); }
            }
            for (Value reference:references) if (reference instanceof Reference ref && !ids.contains(ref.id()))
                throw invalid(ref.pointer(),"unresolved object reference: "+ref.id());
            if (!attachments.isEmpty()) loadAttachments(manifest, nodes, attachments, bytes.length);
            return new StaticData(manifest.toString(),source,basis,binding,List.copyOf(nodes));
        } catch (CharacterCodingException invalid) {
            throw new IOException("static data is not UTF-8: "+manifest,invalid);
        } catch (JsonParseException | IllegalArgumentException | IllegalStateException invalid) {
            throw new IOException("invalid static data " + manifest + ": " + invalid.getMessage(),invalid);
        }
    }

    private static void loadAttachments(Path manifest, List<Node> nodes, Map<Integer,String> attachments, int bytes) throws IOException {
        Map<Path,ClassFile> classfiles = new HashMap<>();
        for (var attachment : attachments.entrySet()) {
            int index = attachment.getKey();
            Node node = nodes.get(index);
            Path file = manifest.getParent().resolve(attachment.getValue()).normalize();
            ClassFile content = classfiles.get(file);
            if (content == null) {
                byte[] data;
                try (InputStream input = Files.newInputStream(file)) { data = input.readNBytes(BYTE_LIMIT - bytes + 1); }
                bytes += data.length;
                String pointer = node.pointer() + "/classfile";
                if (bytes > BYTE_LIMIT) throw invalid(pointer,"static data and classfile byte budget: 1 MiB");
                if (data.length < 8 || data[0] != (byte)0xca || data[1] != (byte)0xfe || data[2] != (byte)0xba || data[3] != (byte)0xbe)
                    throw invalid(pointer,"expected a classfile header");
                content = new ClassFile(file.toString(), data);
                classfiles.put(file, content);
            }
            nodes.set(index, new Node(node.id(),node.type(),node.fields(),node.elements(),node.entries(),node.decoded(),
                    Optional.of(content),node.absentFields(),node.classData(),node.pointer()));
        }
    }

    private static Value value(JsonElement element,String pointer) {
        if(element==null)throw invalid(pointer,"missing value");
        if(element.isJsonNull())return new Scalar(null);
        if(element.isJsonObject()) {
            JsonObject object=element.getAsJsonObject();
            if(object.size()!=1)throw invalid(pointer,"value needs one ref or class");
            if(object.has("ref"))return new Reference(text(object,"ref",pointer),pointer);
            keys(object,pointer,"class");return new ClassLiteral(text(object,"class",pointer));
        }
        if(!element.isJsonPrimitive())throw invalid(pointer,"expected scalar, ref or class");
        JsonPrimitive primitive=element.getAsJsonPrimitive();
        if(primitive.isBoolean())return new Scalar(primitive.getAsBoolean());
        if(primitive.isString())return new Scalar(primitive.getAsString());
        java.math.BigDecimal number=primitive.getAsBigDecimal();
        try{return new Scalar(number.intValueExact());}
        catch(ArithmeticException nonInt) {
            try{return new Scalar(number.longValueExact());}
            catch(ArithmeticException nonLong){return new Scalar(number.doubleValue());}
        }
    }
    private static List<Value> values(JsonArray array,String pointer) {
        if(array.size()>256)throw invalid(pointer,"static sequence budget: 256");
        List<Value> result=new ArrayList<>();for(int i=0;i<array.size();i++)result.add(value(array.get(i),pointer+"/"+i));return List.copyOf(result);
    }
    private static String text(JsonObject object,String name,String pointer) {
        JsonElement value=object.get(name);
        if(value==null || !value.isJsonPrimitive() || !value.getAsJsonPrimitive().isString())throw invalid(pointer+"/"+name,"expected string");
        String text=value.getAsString();if(text.isBlank() || text.length()>2048)throw invalid(pointer+"/"+name,"invalid text");return text;
    }
    private static JsonObject object(JsonElement value,String pointer) {
        if(value==null || !value.isJsonObject())throw invalid(pointer,"expected object");return value.getAsJsonObject();
    }
    private static JsonArray array(JsonObject object,String name,String pointer) {
        JsonElement value=object.get(name);if(value==null || !value.isJsonArray())throw invalid(pointer+"/"+name,"expected array");return value.getAsJsonArray();
    }
    private static JsonArray optionalArray(JsonObject object,String name,String pointer) {return object.has(name)?array(object,name,pointer):new JsonArray();}
    private static void keys(JsonObject object,String pointer,String... allowed) {
        Set<String> names=Set.of(allowed);
        for(String name:object.keySet())if(!names.contains(name))throw invalid(pointer+"/"+name,"unknown property");
    }
    private static IllegalArgumentException invalid(String pointer,String detail){return new IllegalArgumentException(pointer+": "+detail);}
}
