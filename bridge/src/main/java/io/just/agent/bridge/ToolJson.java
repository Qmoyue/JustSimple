package io.just.agent.bridge;

import com.google.gson.*;
import com.google.gson.reflect.TypeToken;
import com.google.gson.stream.*;
import io.just.program.Program;
import io.just.knowledge.Values;
import java.io.IOException;
import java.util.Optional;

/** Wire projections retain variant names; canonical scan evidence uses Reports.json instead. */
final class ToolJson {
    private ToolJson() {}
    static final Gson GSON = new GsonBuilder().disableHtmlEscaping().serializeNulls()
            .registerTypeHierarchyAdapter(Number.class,(JsonSerializer<Number>)(number,type,context) -> {
                if((number instanceof Double || number instanceof Float) && !Double.isFinite(number.doubleValue())) {
                    JsonObject value=new JsonObject();value.addProperty("type",number.getClass().getSimpleName());
                    value.addProperty("value",number.toString());return value;
                }
                return new JsonPrimitive(number);
            })
            .registerTypeHierarchyAdapter(Optional.class, (JsonSerializer<Optional<?>>)(value,type,context) ->
                    value.map(context::serialize).orElse(JsonNull.INSTANCE))
            .registerTypeAdapterFactory(new TypeAdapterFactory() {
                @Override public <T> TypeAdapter<T> create(Gson gson, TypeToken<T> type) {
                    Class<?> raw=type.getRawType();
                    if(!Program.Action.class.isAssignableFrom(raw) && !Program.Origin.class.isAssignableFrom(raw)
                            && !Program.JvmConstant.class.isAssignableFrom(raw) && !Values.ChoiceKey.class.isAssignableFrom(raw)
                            && !Values.Slot.class.isAssignableFrom(raw) && !Values.Atom.class.isAssignableFrom(raw)
                            && !Values.InputLocation.class.isAssignableFrom(raw))return null;
                    TypeAdapter<T> delegate=gson.getDelegateAdapter(this,type);
                    return new TypeAdapter<>() {
                        @Override public void write(JsonWriter out,T value)throws IOException {
                            if(value==null){out.nullValue();return;}
                            JsonObject tree=delegate.toJsonTree(value).getAsJsonObject();
                            tree.addProperty("kind",value.getClass().getSimpleName());gson.getAdapter(JsonElement.class).write(out,tree);
                        }
                        @Override public T read(JsonReader in){throw new UnsupportedOperationException("tool projections are read-only");}
                    };
                }
            }).create();
}
