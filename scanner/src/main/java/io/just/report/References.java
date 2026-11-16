package io.just.report;

import com.google.gson.*;
import com.google.gson.stream.JsonWriter;
import com.google.gson.stream.JsonReader;
import com.google.gson.reflect.TypeToken;
import io.just.analysis.ScanResult;
import io.just.analysis.ScanResult.Relation;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.program.Program.Site;
import java.io.IOException;
import java.lang.reflect.Type;
import java.util.*;

/** Output-local reference numbering. The result remains the sole source of facts and conclusions. */
final class References {
    private final Map<Site,Integer> sites=new LinkedHashMap<>();
    private final Map<Gap,Integer> gaps=new LinkedHashMap<>();
    private final Map<Path,Integer> conditions=new LinkedHashMap<>();
    private final Map<ChoiceKey,Integer> choices=new LinkedHashMap<>();
    private final Map<Atom,Integer> values=new LinkedHashMap<>();
    private final Map<InputLocation,Integer> sources=new LinkedHashMap<>();
    private final Gson plain=builder().create();
    private final TypeAdapterFactory valueReferences=new TypeAdapterFactory() {
        @Override public <T> TypeAdapter<T> create(Gson gson,TypeToken<T> type) {
            if(!Atom.class.isAssignableFrom(type.getRawType()))return null;
            return new TypeAdapter<>() {
                @Override public void write(JsonWriter out,T atom)throws IOException {if(atom==null)out.nullValue();else out.value(value((Atom)atom));}
                @Override public T read(JsonReader in){throw new UnsupportedOperationException("report output only");}
            };
        }
    };
    private final Gson table=builder().registerTypeAdapter(ClassValue.class,(JsonSerializer<ClassValue>)(v,t,c) -> {
                JsonObject value=new JsonObject();value.addProperty("descriptor",v.descriptor());value.addProperty("exact",v.exact());
                value.add("source",v.source().<JsonElement>map(s -> new JsonPrimitive(source(s))).orElse(JsonNull.INSTANCE));value.addProperty("loader",v.loader());return value;
            }).registerTypeAdapterFactory(valueReferences)
            .registerTypeAdapter(Site.class,(JsonSerializer<Site>)(v,t,c) -> new JsonPrimitive(site(v)))
            .registerTypeAdapter(Gap.class,(JsonSerializer<Gap>)(v,t,c) -> new JsonPrimitive(gap(v)))
            .registerTypeAdapter(Path.class,(JsonSerializer<Path>)(v,t,c) -> new JsonPrimitive(condition(v)))
            .registerTypeHierarchyAdapter(ChoiceKey.class,(JsonSerializer<ChoiceKey>)(v,t,c) -> new JsonPrimitive(choice(v)))
            .registerTypeAdapter(InputSource.class,(JsonSerializer<InputSource>)(v,t,c) -> new JsonPrimitive(source(v))).create();
    private final Gson indexed=builder()
            .registerTypeAdapter(Relation.class,(JsonSerializer<Relation>)(r,t,c) -> {
                JsonObject value=new JsonObject();
                value.addProperty("id",r.id());value.addProperty("context",r.context());value.addProperty("kind",r.kind().name());
                value.add("site",c.serialize(r.site()));value.add("target",c.serialize(r.target()));value.add("receiver",c.serialize(r.receiver()));
                value.add("arguments",c.serialize(r.arguments()));value.add("conditions",c.serialize(r.conditions()));value.addProperty("detail",r.detail());value.add("slot",c.serialize(r.slot()));
                value.add("supports",c.serialize(r.supports()));
                return value;
            })
            .registerTypeAdapter(InputSource.class,(JsonSerializer<InputSource>)(v,t,c) -> new JsonPrimitive(source(v)))
            .registerTypeAdapter(Site.class,(JsonSerializer<Site>)(v,t,c) -> new JsonPrimitive(site(v)))
            .registerTypeAdapter(Gap.class,(JsonSerializer<Gap>)(v,t,c) -> new JsonPrimitive(gap(v)))
            .registerTypeAdapter(Path.class,(JsonSerializer<Path>)(v,t,c) -> new JsonPrimitive(condition(v)))
            .registerTypeHierarchyAdapter(Atom.class,(JsonSerializer<Atom>)(v,t,c) -> new JsonPrimitive(value(v))).create();
    static GsonBuilder builder() {
        return new GsonBuilder().serializeNulls().disableHtmlEscaping().enableComplexMapKeySerialization()
                .registerTypeHierarchyAdapter(Number.class,(JsonSerializer<Number>)(number,t,c) -> {
                    if((number instanceof Double || number instanceof Float) && !Double.isFinite(number.doubleValue())) {
                        JsonObject value=new JsonObject();value.addProperty("type",number.getClass().getSimpleName());
                        value.addProperty("value",number.toString());return value;
                    }
                    return new JsonPrimitive(number);
                })
                .registerTypeHierarchyAdapter(ChoiceKey.class,(JsonSerializer<ChoiceKey>)(key,t,c) -> {
                    JsonObject value=new JsonObject();value.addProperty("kind",key.getClass().getSimpleName());
                    value.addProperty("context",key.context());value.addProperty("instruction",key.instruction());value.addProperty("iteration",key.iteration());
                    if(key instanceof TargetChoice target)value.add("effects",c.serialize(target.effects()));
                    if(key instanceof NormalChoice normal) {
                        value.add("effects",c.serialize(normal.effects()));value.add("target",c.serialize(normal.target()));
                        value.add("receiver",c.serialize(normal.receiver()));value.add("arguments",c.serialize(normal.arguments()));
                    }return value;
                })
                .registerTypeHierarchyAdapter(InputLocation.class,(JsonSerializer<InputLocation>)(location,t,c) -> {
                    JsonObject value=new JsonObject();value.addProperty("kind",location.getClass().getSimpleName());
                    if(location instanceof InputSource source) {
                        value.add("entry",c.serialize(source.entry()));value.addProperty("parameterSlot",source.parameterSlot());value.add("path",c.serialize(source.path()));
                    } else if(location instanceof ObjectSource source){value.addProperty("object",source.object());value.add("path",c.serialize(source.path()));}
                    else {ValueSource source=(ValueSource)location;value.addProperty("value",source.value());value.addProperty("operand",source.operand());value.add("producer",c.serialize(source.producer()));value.add("path",c.serialize(source.path()));}
                    return value;
                })
                .registerTypeAdapterFactory(new SlotTypes())
                .registerTypeHierarchyAdapter(Optional.class,(JsonSerializer<Optional<?>>)(v,t,c) -> v.map(c::serialize).orElse(JsonNull.INSTANCE));
    }
    /** Empty slots such as Length and Elements must remain distinguishable in the output. */
    private static final class SlotTypes implements TypeAdapterFactory {
        @Override public <T> TypeAdapter<T> create(Gson gson,TypeToken<T> type) {
            if(!Slot.class.isAssignableFrom(type.getRawType()) || type.getRawType().isInterface())return null;
            TypeAdapter<T> delegate=gson.getDelegateAdapter(this,type);
            return new TypeAdapter<>() {
                @Override public void write(JsonWriter out,T slot) throws IOException {
                    if(slot==null){out.nullValue();return;}
                    JsonObject value=delegate.toJsonTree(slot).getAsJsonObject();value.addProperty("kind",type.getRawType().getSimpleName());
                    gson.getAdapter(JsonElement.class).write(out,value);
                }
                @Override public T read(JsonReader in) {throw new UnsupportedOperationException("report adapters only write completed results");}
            };
        }
    }
    int site(Site value) {return id(sites,value);}
    int gap(Gap value) {int result=id(gaps,value);site(value.site());value.condition().ifPresent(this::choice);return result;}
    int condition(Path path) {
        Integer old=conditions.get(path);if(old!=null)return old;int result=id(conditions,path);
        path.choices().keySet().forEach(this::choice);
        path.selections().forEach((key,selection) -> {source(key);value(selection.value());});return result;
    }
    int choice(ChoiceKey key){int result=id(choices,key);if(key instanceof NormalChoice normal){value(normal.receiver());normal.arguments().forEach(this::value);}return result;}
    int value(Atom atom) {
        Integer old=values.get(atom);if(old!=null)return old;int result=id(values,atom);
        if(atom instanceof Reflected r){value(r.declaringClass());value(r.name());value(r.parameterTypes());site(r.lookup());}
        else if(atom instanceof RuntimeTypes types)types.members().forEach(this::value);
        else if(atom instanceof ConstructorValue c){value(c.declaringClass());value(c.parameterTypes());site(c.lookup());}
        else if(atom instanceof ArrayValue array){array.elements().forEach(this::value);array.conditions().forEach(this::gap);}
        else if(atom instanceof LambdaValue lambda){lambda.captured().forEach(this::value);site(lambda.factory());}
        else if(atom instanceof ProxyValue proxy){proxy.interfaces().forEach(this::value);value(proxy.handler());site(proxy.factory());}
        else if(atom instanceof UnboundValue unbound)value(unbound.original());
        else if(atom instanceof StringPrefix prefix)value(prefix.suffix());
        else if(atom instanceof StringConcat sequence)sequence.pieces().forEach(this::value);
        else if(atom instanceof InstanceTest test)value(test.receiver());
        else if(atom instanceof MethodTypeValue type){value(type.returned());type.parameters().forEach(this::value);}
        else if(atom instanceof CollectionView view){value(view.source());slot(view.elements());}
        else if(atom instanceof MapEntryValue entry){value(entry.source());value(entry.key());}
        else if(atom instanceof MethodHandleValue handle){value(handle.invocationType());value(handle.lookup());site(handle.source());}
        else if(atom instanceof LookupValue lookup)site(lookup.source());
        valueSource(atom).ifPresent(this::source);return result;
    }
    private Optional<InputLocation> valueSource(Atom atom){return atom instanceof ClassValue type?type.source():io.just.knowledge.Values.source(atom).map(s -> (InputLocation)s);}
    int source(InputLocation location){Integer old=sources.get(location);if(old!=null)return old;int result=id(sources,location);
        if(location instanceof ValueSource produced){value(produced.producer());produced.path().forEach(this::slot);}
        else if(location instanceof InputSource input)input.path().forEach(this::slot);else ((ObjectSource)location).path().forEach(this::slot);return result;
    }
    private void slot(Slot slot){if(slot instanceof MapKey key)value(key.key());else if(slot instanceof KeyIndex key)value(key.key());else if(slot instanceof KeyComparison key){value(key.incoming());value(key.existing());}else if(slot instanceof StreamRead read)site(read.site());}
    @SuppressWarnings("unchecked")
    private <T extends Atom> TypeAdapter<T> valueBody(T value) {return table.getDelegateAdapter(valueReferences,(TypeToken<T>)TypeToken.get(value.getClass()));}
    String binding(Atom value) {return valueBody(value).toJson(value);}
    private static <T> int id(Map<T,Integer> ids,T value) {
        Integer existing=ids.get(value);if(existing!=null)return existing;
        int next=ids.size();ids.put(value,next);return next;
    }
    private void field(JsonWriter out,String name,Object value) throws IOException {
        out.name(name);indexed.toJson(value,value==null?Object.class:value.getClass(),out);
    }
    void json(ScanResult result,JsonWriter out) throws IOException {
        out.beginObject();out.name("schemaVersion").value(4);
        field(out,"mode",result.mode());field(out,"execution",result.execution());field(out,"outcome",result.outcome());
        field(out,"input",result.input());field(out,"staticData",result.staticData());field(out,"analysisBudgets",result.analysisBudgets());
        field(out,"methodInstructionBudget",result.methodInstructionBudget());field(out,"entries",result.entries());field(out,"hints",result.hints());
        // Each record is written separately; no complete report tree or string copy is built.
        out.name("relations").beginArray();for(var relation:result.relations())indexed.toJson(relation,relation.getClass(),out);out.endArray();
        out.name("findings").beginArray();for(var finding:result.findings())indexed.toJson(finding,finding.getClass(),out);out.endArray();
        out.name("inputRequirements").beginArray();for(var need:result.inputRequirements())indexed.toJson(need,need.getClass(),out);out.endArray();
        out.name("demandFrontier").beginArray();for(var frontier:result.demandFrontier())indexed.toJson(frontier,frontier.getClass(),out);out.endArray();
        out.name("breakpoints").beginArray();for(var point:result.breakpoints())indexed.toJson(point,point.getClass(),out);out.endArray();
        field(out,"limitations",result.limitations());field(out,"rankingIssues",result.rankingIssues());field(out,"missingClasses",result.missingClasses());field(out,"statistics",result.statistics());
        for(var relation:result.relations())relation.slot().ifPresent(this::slot);
        for(var requirement:result.inputRequirements()){requirement.source().ifPresent(this::source);requirement.needed().slot().ifPresent(this::slot);}
        out.name("references").beginObject();
        table(out,"sites",sites,Site.class);
        out.name("gaps").beginArray();for(Gap gap:gaps.keySet())table.getDelegateAdapter(valueReferences,TypeToken.get(Gap.class)).write(out,gap);out.endArray();
        out.name("conditions").beginArray();
        for(Path path:conditions.keySet()) {
            out.beginObject();out.name("choices").beginArray();
            for(var selected:path.choices().entrySet())out.beginArray().value(choice(selected.getKey())).value(selected.getValue()).endArray();
            out.endArray();
            out.name("selections").beginArray();
            for(var selection:path.selections().entrySet()) {
                out.beginObject();out.name("source").value(source(selection.getKey()));out.name("value").value(value(selection.getValue().value()));
                out.name("types");plain.toJson(selection.getValue().types(),Set.class,out);
                if(selection.getValue().range().isPresent()) {
                    IntegralRange range=selection.getValue().range().get();
                    out.name("integralRange").beginObject();out.name("minimum").value(range.minimum());out.name("maximum").value(range.maximum());out.endObject();
                }
                out.endObject();
            }
            out.endArray();out.endObject();
        }
        out.endArray();
        out.name("choices").beginArray();for(ChoiceKey choice:choices.keySet())writeChoice(out,choice);out.endArray();
        out.name("sources").beginArray();for(InputLocation location:sources.keySet())table.toJson(location,InputLocation.class,out);out.endArray();
        out.name("values").beginArray();
        for(Atom atom:values.keySet()) {
            out.beginObject();out.name("kind").value(atom.getClass().getSimpleName());out.name("value");valueBody(atom).write(out,atom);out.endObject();
        }
        out.endArray();out.endObject();out.endObject();
    }
    void inputTemplate(ScanResult result,JsonWriter out) throws IOException {
        out.beginObject();out.name("schemaVersion").value(2);out.name("kind").value("INPUT_REQUIREMENTS_TEMPLATE");
        out.name("report").value("report.json");out.name("contract").value("Requirement IDs reference report.json. Proposed values are unknown and are not facts; supply independently verified data with source and basis.");
        out.name("requirements").beginArray();
        for(var requirement:result.inputRequirements()) {
            out.beginObject();out.name("requirement").value(requirement.id());out.name("state").value("UNRESOLVED");
            out.name("proposedValue").beginObject();out.name("kind").value("UNKNOWN");out.name("descriptor").value(requirement.needed().descriptor());out.endObject();out.endObject();
        }
        out.endArray();out.endObject();
    }
    private <T> void table(JsonWriter out,String name,Map<T,Integer> table,Type type) throws IOException {
        out.name(name).beginArray();for(T item:table.keySet())plain.toJson(item,type,out);out.endArray();
    }
    List<Gap> gaps() {return List.copyOf(gaps.keySet());}
    List<Atom> values() {return List.copyOf(values.keySet());}
    List<Path> conditions() {return List.copyOf(conditions.keySet());}
    List<ChoiceKey> choices(){return List.copyOf(choices.keySet());}
    List<InputLocation> sources(){return List.copyOf(sources.keySet());}
    String conditionText(Path path) {
        List<String> choices=new ArrayList<>();
        for(var item:path.choices().entrySet())choices.add("Q"+choice(item.getKey())+"="+item.getValue());
        for(var item:path.selections().entrySet())choices.add("S"+source(item.getKey())+" selects V"+value(item.getValue().value())+" requires "+item.getValue().types()+item.getValue().range().map(range -> " in ["+range.minimum()+", "+range.maximum()+"]").orElse(""));
        return choices.toString();
    }
    private void writeChoice(JsonWriter out,ChoiceKey key)throws IOException {
        out.beginObject();out.name("kind").value(key.getClass().getSimpleName());out.name("context").value(key.context());
        out.name("instruction").value(key.instruction());out.name("iteration").value(key.iteration());
        if(key instanceof TargetChoice target){out.name("effects");plain.toJson(target.effects(),List.class,out);}
        if(key instanceof NormalChoice normal){out.name("effects");plain.toJson(normal.effects(),List.class,out);out.name("target");plain.toJson(normal.target(),normal.target().getClass(),out);
            out.name("receiver").value(value(normal.receiver()));out.name("arguments").beginArray();for(Atom argument:normal.arguments())out.value(value(argument));out.endArray();}
        out.endObject();
    }
    String choiceText(ChoiceKey key) {
        if(key instanceof NormalChoice normal)return "normal "+normal.context()+":"+normal.instruction()+":"+normal.iteration()+" effects "+normal.effects()+" "+normal.target()+" receiver V"+value(normal.receiver())+" args "+normal.arguments().stream().map(a -> "V"+value(a)).toList();
        return key.toString();
    }
    String sourceText(InputLocation source){return table.toJson(source,InputLocation.class);}
}
