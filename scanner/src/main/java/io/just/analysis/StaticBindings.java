package io.just.analysis;

import io.just.input.StaticData;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import org.objectweb.asm.Opcodes;
import java.util.*;

/** Validates supplied snapshots against classfiles without invoking construction or callbacks. */
final class StaticBindings {
    record Assignment(ObjectValue object,Slot slot,Atom value,String pointer) {}
    record Snapshot(Optional<Atom> receiver,List<Atom> arguments,List<Assignment> assignments,int nextId) {}

    static Snapshot check(StaticData data,Program program,int firstId) {
        Map<String,ObjectValue> objects=new LinkedHashMap<>();
        int next=firstId;
        for (StaticData.Node node:data.nodes()) {
            if (node.type().startsWith("[")) descriptor(data,node.type(),program,node.pointer()+"/type");
            if (!node.type().startsWith("[")) {
                ClassInfo type=program.type(node.type()).orElseThrow(() -> invalid(data,node.pointer()+"/type","missing object type: "+node.type()));
                if ((type.access() & (Opcodes.ACC_ABSTRACT|Opcodes.ACC_INTERFACE))!=0) throw invalid(data,node.pointer()+"/type","object runtime type must be concrete: "+node.type());
            }
            objects.put(node.id(),new ObjectValue(next++,node.type(),true,"static input "+node.id(),false));
        }
        List<Assignment> assignments=new ArrayList<>();Map<StaticData.ClassFile,Bytecode> classfiles=new HashMap<>();
        Set<String> serialized=serialized(data);
        for (StaticData.Node node:data.nodes()) {
            ObjectValue object=objects.get(node.id()); String pointer=node.pointer();
            boolean source=serialized.contains(node.id());
            Set<FieldId> fields=new HashSet<>();
            for (StaticData.Field field:node.fields()) {
                FieldId declared=new FieldId(field.owner(),field.name(),field.descriptor());
                Query<FieldId> fieldQuery=program.lookupField(declared);
                if (!fieldQuery.pending().isEmpty())throw invalid(data,field.pointer(),"cannot verify field: "+fieldQuery.pending());
                FieldId actual=fieldQuery.value().orElseThrow(() -> invalid(data,field.pointer(),"missing field: "+declared));
                if (!program.instanceField(actual) || !subtype(data,node.type(),actual.owner(),program,field.pointer()) || !fields.add(actual)) throw invalid(data,field.pointer(),"invalid or repeated instance field: "+actual);
                Atom value=atom(field.value(),objects);
                if(!(source && value instanceof ObjectValue && (actual.descriptor().startsWith("L") || actual.descriptor().startsWith("["))))value=compatible(data,value,actual.descriptor(),program,field.pointer()+"/value");
                assignments.add(new Assignment(object,source?new SerializedField(actual):new Field(actual),value,field.pointer()+"/value"));
                if(source) {
                    assignments.add(new Assignment(object,new FieldPresence(actual),new Literal(1),field.pointer()+"/value"));
                    assignments.add(new Assignment(object,new ClassData(actual.owner(),actual.loader()),new Literal(1),field.pointer()+"/value"));
                }
            }
            for(StaticData.AbsentField field:node.absentFields()) {
                FieldId declared=new FieldId(field.owner(),field.name(),field.descriptor());Query<FieldId> query=program.lookupField(declared);
                if(!query.pending().isEmpty())throw invalid(data,field.pointer(),"cannot verify absent field: "+query.pending());
                FieldId actual=query.value().orElseThrow(() -> invalid(data,field.pointer(),"missing local field: "+declared));
                if(!source || !program.instanceField(actual) || !subtype(data,node.type(),actual.owner(),program,field.pointer()) || !fields.add(actual)
                        || program.fields(actual.owner(),actual.loader()).stream().filter(f -> f.id().equals(actual)).anyMatch(f -> (f.access() & Opcodes.ACC_TRANSIENT)!=0))
                    throw invalid(data,field.pointer(),"absentFields requires a distinct ordinary serialized field");
                assignments.add(new Assignment(object,new FieldPresence(actual),new Literal(0),field.pointer()));
            }
            Set<String> classSlots=new HashSet<>();
            for(StaticData.ClassData slot:node.classData()) {
                if(!source || !classSlots.add(slot.owner()) || !subtype(data,node.type(),slot.owner(),program,slot.pointer())
                        || !subtype(data,slot.owner(),"java/io/Serializable",program,slot.pointer()) || !slot.present() && slot.owner().equals(node.type())
                        || !slot.present() && node.fields().stream().anyMatch(f -> f.owner().equals(slot.owner())))
                    throw invalid(data,slot.pointer(),"classData must describe distinct serializable hierarchy slots; the leaf and supplied fields require data");
                assignments.add(new Assignment(object,new ClassData(slot.owner(),program.scope(slot.owner(),object.loader())),new Literal(slot.present()?1:0),slot.pointer()+"/present"));
            }
            node.classfile().ifPresent(content -> {
                assignments.add(new Assignment(object,new Content(),classfiles.computeIfAbsent(content,key -> new Bytecode("classfile",key.location(),key.bytes())),pointer+"/classfile"));
                assignments.add(new Assignment(object,new Length(),new Literal(content.bytes().length),pointer+"/classfile"));
            });
            if (node.elements().isPresent()) {
                boolean array=node.type().startsWith("[");
                if (!array && !subtype(data,node.type(),"java/util/Collection",program,pointer+"/elements")) throw invalid(data,pointer+"/elements","elements need array or Collection: "+node.type());
                List<StaticData.Value> values=node.elements().orElseThrow();
                assignments.add(new Assignment(object,new Length(),new Literal(values.size()),pointer+"/elements"));
                for (int i=0;i<values.size();i++) {
                    Atom value=atom(values.get(i),objects);
                    if (array && !(source && value instanceof ObjectValue && (node.type().substring(1).startsWith("L") || node.type().substring(1).startsWith("["))))value=compatible(data,value,node.type().substring(1),program,pointer+"/elements/"+i);
                    Slot slot=source?new SerializedIndex(i):array || subtype(data,node.type(),"java/util/List",program,pointer+"/elements")?new Index(i):new Elements();
                    assignments.add(new Assignment(object,slot,value,pointer+"/elements/"+i));
                }
            }
            if (!node.entries().isEmpty()) {
                if (!subtype(data,node.type(),"java/util/Map",program,pointer+"/entries")) throw invalid(data,pointer+"/entries","entries need Map: "+node.type());
                int index=0; Set<Atom> keys=new HashSet<>();
                for (StaticData.MapEntry entry:node.entries()) {
                    Atom key=atom(entry.key(),objects),value=atom(entry.value(),objects);
                    if (!keys.add(key)) throw invalid(data,pointer+"/entries/"+index+"/key","duplicate map key in snapshot: "+key);
                    assignments.add(new Assignment(object,source?new SerializedKey(index):new Elements(),key,pointer+"/entries/"+index+"/key"));
                    assignments.add(new Assignment(object,source?new SerializedValue(index):new MapValues(),value,pointer+"/entries/"+index+"/value"));
                    if(!source)assignments.add(new Assignment(object,new MapKey(key),value,pointer+"/entries/"+index+"/value"));
                    if (!source && node.type().equals("java/util/LinkedHashMap")) {
                        assignments.add(new Assignment(object,new Index(index),value,pointer+"/entries/"+index+"/value"));
                        assignments.add(new Assignment(object,new KeyIndex(key),new Literal(index),pointer+"/entries/"+index+"/key"));
                    }
                    index++;
                }
                assignments.add(new Assignment(object,new Length(),new Literal(index),pointer+"/entries"));
            }
            node.decoded().ifPresent(value -> {
                if (!subtype(data,node.type(),"java/io/ObjectInput",program,pointer+"/decoded")) throw invalid(data,pointer+"/decoded","decoded binding requires ObjectInput: "+node.type());
                assignments.add(new Assignment(object,new Decoded(),atom(value,objects),pointer+"/decoded"));
            });
        }
        StaticData.MethodName method=data.entry().method();
        MethodId id=new MethodId(method.owner(),method.name(),method.descriptor());
        Method target=program.declared(id).orElseThrow(() -> invalid(data,"/entry","missing entry method: "+id));
        Optional<Atom> receiver=data.entry().receiver().map(v -> atom(v,objects));
        if (!target.isStatic() && receiver.filter(a -> a instanceof Literal l && l.value()==null).isPresent()) throw invalid(data,"/entry/receiver","entry receiver is null");
        if (!target.isStatic()) compatible(data,receiver.orElseThrow(() -> invalid(data,"/entry/receiver","instance entry requires receiver")),"L"+id.owner()+";",program,"/entry/receiver");
        if (target.isStatic() && receiver.isPresent()) throw invalid(data,"/entry/receiver","static entry cannot have receiver");
        List<Atom> arguments=new ArrayList<>(data.entry().arguments().stream().map(v -> atom(v,objects)).toList());
        List<ValueType> parameters=program.signature(id).parameters();
        if (parameters.size()!=arguments.size()) throw invalid(data,"/entry/arguments","entry argument count mismatch");
        for (int i=0;i<arguments.size();i++) arguments.set(i,compatible(data,arguments.get(i),parameters.get(i).descriptor(),program,"/entry/arguments/"+i));
        return new Snapshot(receiver,List.copyOf(arguments),List.copyOf(assignments),next);
    }

    private static Set<String> serialized(StaticData data) {
        Map<String,StaticData.Node> nodes=new HashMap<>();for(StaticData.Node node:data.nodes())nodes.put(node.id(),node);
        Set<String> seen=new HashSet<>();ArrayDeque<StaticData.Value> pending=new ArrayDeque<>();
        for(StaticData.Node node:data.nodes())node.decoded().ifPresent(pending::add);
        while(!pending.isEmpty())if(pending.removeFirst() instanceof StaticData.Reference reference && seen.add(reference.id())) {
            StaticData.Node node=nodes.get(reference.id());
            for(StaticData.Field field:node.fields())pending.add(field.value());
            node.elements().ifPresent(pending::addAll);
            for(StaticData.MapEntry entry:node.entries()){pending.add(entry.key());pending.add(entry.value());}
            node.decoded().ifPresent(pending::add);
        }
        return seen;
    }

    private static Atom atom(StaticData.Value value,Map<String,ObjectValue> objects) {
        if (value instanceof StaticData.Reference ref) return Objects.requireNonNull(objects.get(ref.id()),"unresolved "+ref.id());
        if (value instanceof StaticData.ClassLiteral type) return new ClassValue(type.descriptor(),true);
        return new Literal(((StaticData.Scalar)value).value());
    }
    private static Atom compatible(StaticData data,Atom atom,String descriptor,Program program,String pointer) {
        boolean valid;
        if (atom instanceof ObjectValue object) valid=subtype(data,object.type(),io.just.knowledge.Values.type(descriptor),program,pointer);
        else if (atom instanceof ClassValue type) {
            descriptor(data,type.descriptor(),program,pointer+"/class");
            valid= subtype(data,"java/lang/Class",io.just.knowledge.Values.type(descriptor),program,pointer);
        } else {
            Object value=((Literal)atom).value();
            valid=value==null ? descriptor.startsWith("L") || descriptor.startsWith("[")
                    : value instanceof String ? subtype(data,"java/lang/String",io.just.knowledge.Values.type(descriptor),program,pointer)
                    : value instanceof Boolean ? descriptor.equals("Z")
                    : value instanceof Integer number ? switch(descriptor) {
                        case "B" -> number>=Byte.MIN_VALUE && number<=Byte.MAX_VALUE;
                        case "S" -> number>=Short.MIN_VALUE && number<=Short.MAX_VALUE;
                        case "C" -> number>=Character.MIN_VALUE && number<=Character.MAX_VALUE;
                        case "I","J","F","D" -> true;
                        default -> false;
                    }
                    : value instanceof Long ? "JFD".contains(descriptor) && descriptor.length()==1
                    : value instanceof Double number && Double.isFinite(number) && (descriptor.equals("F") || descriptor.equals("D"));
        }
        if (!valid) throw invalid(data,pointer,"incompatible binding: "+atom+" for "+descriptor);
        if(atom instanceof Literal literal && descriptor.length()==1) {
            Object value=literal.value();
            if(value instanceof Boolean flag)return new Literal(flag?1:0);
            if(value instanceof Number number) {
                if(descriptor.equals("F")) {
                    float converted=number.floatValue();
                    if(!Float.isFinite(converted))throw invalid(data,pointer,"float binding exceeds finite range: "+value);
                    return new Literal(converted);
                }
                if(descriptor.equals("D"))return new Literal(number.doubleValue());
                if(descriptor.equals("J"))return new Literal(number.longValue());
                return new Literal(number.intValue());
            }
        }
        return atom;
    }
    private static void descriptor(StaticData data,String descriptor,Program program,String pointer) {
        if (!descriptor.matches("(?:V|\\[*[ZBCSIJFD]|\\[*L[^.;\\[()]+;)") || descriptor.equals("")) throw invalid(data,pointer,"invalid JVM type: "+descriptor);
        String component=descriptor.replaceFirst("^\\[+","");
        if (component.startsWith("L") && program.type(io.just.knowledge.Values.type(component)).isEmpty()) throw invalid(data,pointer,"missing class literal/array component: "+component);
    }
    private static boolean subtype(StaticData data,String child,String parent,Program program,String pointer) {
        Query<Boolean> query=program.assignable(child,parent);
        if (!query.pending().isEmpty())throw invalid(data,pointer,"cannot verify supplied type relationship: "+query.pending());
        return query.value().orElseThrow();
    }
    private static InvalidInput invalid(StaticData data,String pointer,String detail) { return new InvalidInput("static data "+data.location()+"#"+pointer+": "+detail); }
}
