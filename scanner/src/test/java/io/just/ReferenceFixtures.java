package io.just;

import com.google.gson.*;
import io.just.knowledge.CallShape;
import io.just.program.Program;
import io.just.program.Program.*;
import java.nio.file.*;
import java.util.*;

/** Source-built reference shapes; reference classes are parsed, never executed. */
public final class ReferenceFixtures {
    private ReferenceFixtures() {}
    public static void encode(JsonObject root,JsonArray patterns) {
        Map<CallShape.Signature,Integer> signatures=new LinkedHashMap<>();Map<String,Integer> types=new LinkedHashMap<>();JsonArray encoded=new JsonArray();
        java.util.function.Function<CallShape.Signature,Integer> sid=s -> signatures.computeIfAbsent(s,k -> signatures.size());
        for(JsonElement element:patterns) {
            CallShape.Pattern p=new Gson().fromJson(element,CallShape.Pattern.class);List<Integer> data=new ArrayList<>(List.of(sid.apply(p.target()),p.opcode(),p.operands().size()));
            for(var operand:p.operands()) {
                data.addAll(List.of(operand.value(),operand.parameter(),operand.steps().size()));
                for(var step:operand.steps()) {
                    data.addAll(List.of(step.kind().ordinal(),types.computeIfAbsent(step.type(),k -> types.size()),step.slot(),step.call().size()));step.call().forEach(s -> data.add(sid.apply(s)));
                }
            }
            data.add(p.result().size());for(var use:p.result()){data.addAll(List.of(use.kind().ordinal(),use.operand(),use.call().size()));use.call().forEach(s -> data.add(sid.apply(s)));}
            data.add(p.guards().size());p.guards().stream().map(Enum::ordinal).sorted().forEach(data::add);encoded.add(new Gson().toJsonTree(data));
        }
        Gson json=new Gson();root.add("encodedPatterns",encoded);root.add("signatures",json.toJsonTree(signatures.keySet().stream().map(ReferenceFixtures::signature).toList()));root.add("types",json.toJsonTree(types.keySet()));
    }
    private static List<String> signature(CallShape.Signature value){return List.of(value.owner(),value.name(),value.descriptor());}
    public static Path write(Path file,Program program,MethodId... methods)throws Exception {
        JsonObject root=new JsonObject();root.addProperty("schema","just.local-reference/v1");root.add("chains",new JsonArray());root.add("bytecodeObservations",new JsonArray());
        JsonArray fragments=new JsonArray();JsonObject entry=new JsonObject();entry.addProperty("id","source-relations");entry.addProperty("kind","generic");JsonArray relations=new JsonArray();
        Set<CallShape.Pattern> seen=new HashSet<>();
        for(MethodId method:methods)for(Action action:program.facts(method).actions())if(action instanceof Call call) {
            CallShape.Pattern pattern=CallShape.of(program,call);if(!pattern.useful() || !seen.add(pattern))continue;
            JsonObject relation=new JsonObject();relation.add("pattern",new Gson().toJsonTree(pattern));relation.addProperty("asmInstruction",call.site().instruction());relations.add(relation);
        }
        entry.add("relations",relations);fragments.add(entry);root.add("fragments",fragments);Files.writeString(file,new Gson().toJson(root));return file;
    }
}
