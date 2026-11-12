package io.just.analysis;

import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.ValueBindings;
import io.just.knowledge.Values;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.program.Program;
import java.util.*;

/** Finite choices belong to an immutable candidate path, never to the input or heap. */
final class CandidateBindings {
    private final Program program;
    CandidateBindings(Program program){this.program=program;}

    Optional<Path> require(Path path,InputNeed need,Bindings heap) {
        Optional<InputNeed> normalized=Mechanisms.stringInput(need);
        if(normalized.isEmpty())return Optional.empty();
        if(!normalized.get().equals(need))return require(path,normalized.get(),heap);
        Atom current=project(need.subject(),path);
        Optional<InputLocation> source=Values.location(need.subject());
        if(need.slot().isPresent()) {
            Slot slot=need.slot().get();source=source.map(s -> s.at(slot));
            if(current instanceof ArrayValue array) {
                if(slot instanceof Length)current=new Literal(array.elements().size());
                else if(slot instanceof Index index && index.index()<array.elements().size())current=array.elements().get(index.index());
                else current=new Unknown("unselected array slot");
            } else if(current instanceof ObjectValue object) {
                Set<Atom> known=new LinkedHashSet<>();
                for(Bound bound:heap.read(object,slot).under(path).alternatives())known.add(project(bound.atom(),path));
                current=known.size()==1?known.iterator().next():new Unknown("slot has no single current binding");
            } else current=new Unknown("unselected slot");
        }
        if(need.kind()==NeedKind.SERIALIZED_MEMBERS && !(need.choices().size()==1 && need.choices().get(0) instanceof ClassValue type && type.descriptor().equals(need.descriptor()) && !need.descriptor().equals("Ljava/lang/Object;")))return Optional.of(path);
        if(need.kind()==NeedKind.RECEIVER_TYPE || need.kind()==NeedKind.SERIALIZED_MEMBERS) {
            ClassValue runtime=need.choices().size()==1 && need.choices().get(0) instanceof ClassValue type?type:new ClassValue(need.descriptor(),true);
            if(ValueBindings.compatible(current,need.descriptor(),program,runtime.loader()).match()==ValueBindings.Match.INCOMPATIBLE)return Optional.empty();
            if(current instanceof ObjectValue object && object.exact() || current instanceof Literal)return Optional.of(path);
            return source.isPresent()?path.selecting(source.get().at(new RuntimeClass()),runtime):Optional.of(path);
        }
        if(need.kind()==NeedKind.ARGUMENTS && source.isPresent()) {
            if(current instanceof Literal literal && literal.value()==null)return Optional.of(path);
            if(ValueBindings.compatible(current,need.descriptor(),program).match()==ValueBindings.Match.INCOMPATIBLE)return Optional.empty();
            return path.selecting(source.get(),new Symbolic(Values.type(need.descriptor()),"conditional array type",source.filter(InputSource.class::isInstance).map(InputSource.class::cast)),need.descriptor());
        }
        Atom chosen;
        if(need.choices().size()==1)chosen=need.choices().get(0);
        else if(need.choices().isEmpty() && need.slot().filter(Index.class::isInstance).isPresent() && source.isPresent()) {
            if(ValueBindings.compatible(current,need.descriptor(),program).match()==ValueBindings.Match.INCOMPATIBLE)return Optional.empty();
            chosen=current instanceof Literal || current instanceof ClassValue || current instanceof ObjectValue object && object.exact()?current
                    :need.descriptor().startsWith("L") || need.descriptor().startsWith("[")?new Symbolic(Values.type(need.descriptor()),"conditional argument",source.filter(InputSource.class::isInstance).map(InputSource.class::cast))
                    :source.get() instanceof InputSource input?new ExternalValue(need.descriptor(),input):new Unknown("conditional primitive argument");
        } else return Optional.of(path);
        if(chosen instanceof ArrayValue array) {
            if(current instanceof ArrayValue actual) {
                if(actual.elements().size()!=array.elements().size())return Optional.empty();
                Optional<Path> selected=Optional.of(path);
                for(int index=0;index<actual.elements().size() && selected.isPresent();index++)selected=require(selected.get(),new InputNeed(actual.elements().get(index),Optional.empty(),NeedKind.VALUE,"Ljava/lang/Class;",List.of(array.elements().get(index)),need.reason()),heap);
                return selected;
            }
            if(current instanceof Literal literal && literal.value()==null && !array.elements().isEmpty())return Optional.empty();
            if(source.isEmpty())return Optional.of(path);
            Optional<Path> selected=path.selecting(source.get(),new Symbolic(array.descriptor(),"conditional signature array",source.filter(InputSource.class::isInstance).map(InputSource.class::cast)),array.descriptor());
            if(selected.isPresent())selected=require(selected.get(),new InputNeed(need.subject(),Optional.of(new Length()),NeedKind.VALUE,"I",List.of(new Literal(array.elements().size())),need.reason()),heap);
            for(int i=0;i<array.elements().size() && selected.isPresent();i++)selected=require(selected.get(),new InputNeed(need.subject(),Optional.of(new Index(i)),NeedKind.VALUE,"Ljava/lang/Class;",List.of(array.elements().get(i)),need.reason()),heap);
            return selected;
        }
        if(current instanceof Literal && !current.equals(chosen))return Optional.empty();
        if(current instanceof ClassValue actual && chosen instanceof ClassValue expected) {
            if(actual.exact() && (!actual.descriptor().equals(expected.descriptor()) || actual.loader()!=expected.loader()))return Optional.empty();
            if(actual.source().filter(location -> !location.path().isEmpty() && location.path().get(location.path().size()-1) instanceof NamedClass).isPresent()
                    && program.scope(Values.type(expected.descriptor()),actual.loader())!=expected.loader())return Optional.empty();
            if(!actual.exact()) {
                if(expected.descriptor().length()==1)return Optional.empty();
                var match=program.assignable(Values.type(expected.descriptor()),expected.loader(),Values.type(actual.descriptor()),actual.loader());
                if(match.value().equals(Optional.of(false)) && match.pending().isEmpty())return Optional.empty();
            }
        }
        Optional<Path> selected=source.isPresent()?path.selecting(source.get(),chosen,need.descriptor()):Optional.of(path);
        if(selected.isPresent() && source.isPresent() && chosen instanceof ClassValue type) {
            InputLocation input=source.get();
            if(!input.path().isEmpty() && input.path().get(input.path().size()-1) instanceof NamedClass) {
                InputLocation original=Values.parent(input);Literal name=new Literal(Values.type(type.descriptor()).replace('/','.'));
                selected=selected.get().selecting(original,name,"Ljava/lang/String;");
                if(selected.isPresent() && original instanceof ValueSource value && value.path().isEmpty())
                    selected=require(selected.get(),new InputNeed(value.producer(),Optional.empty(),NeedKind.CLASS_NAME,"Ljava/lang/String;",List.of(name),need.reason()),heap);
            }
        }
        if(selected.isPresent() && source.isPresent() && !compatible(selected.get().selections().get(source.get()),program))return Optional.empty();
        return selected;
    }

    static boolean compatible(Selection selection,Program program) {
            Atom value=selection.value();
            for(String descriptor:selection.types())if(ValueBindings.compatible(value,descriptor,program).match()==ValueBindings.Match.INCOMPATIBLE)return false;
            if(selection.types().size()<2)return true;
            for(String descriptor:selection.types()) {
                if(!(descriptor.startsWith("L") || descriptor.startsWith("[")))continue;
                String type=Values.type(descriptor);
                if(!type.startsWith("[") && program.type(type).filter(c -> (c.access() & org.objectweb.asm.Opcodes.ACC_FINAL)!=0).isEmpty())continue;
                ObjectValue exact=new ObjectValue(-1,type,true,"finite type requirement",false);
                for(String required:selection.types())if(ValueBindings.compatible(exact,required,program).match()==ValueBindings.Match.INCOMPATIBLE)return false;
            }
        return true;
    }

    static Invocation project(Invocation call,Path path) {
        return new Invocation(call.call(),project(call.receiver(),path),call.arguments().stream().map(a -> project(a,path)).toList(),call.result(),path,call.evaluation());
    }
    static Atom project(Atom atom,Path path) {
        if(atom instanceof ArrayValue array) {
            List<Atom> elements=array.elements().stream().map(value -> project(value,path)).toList();
            return elements.equals(array.elements())?array:new ArrayValue(array.id(),array.role(),array.descriptor(),elements,array.order(),array.extent(),array.conditions());
        }
        if(atom instanceof StringPrefix prefix) {
            Atom suffix=project(prefix.suffix(),path);
            return Mechanisms.concatenate(List.of(new Literal(prefix.prefix()),suffix));
        }
        if(atom instanceof StringConcat sequence)return Mechanisms.concatenate(sequence.pieces().stream().map(piece -> project(piece,path)).toList());
        if(atom instanceof Reflected method)return new Reflected(project(method.declaringClass(),path),project(method.name(),path),project(method.parameterTypes(),path),method.declared(),method.lookup());
        Optional<InputLocation> source=Values.location(atom);
        if(source.isEmpty())return atom;
        Atom selection=path.selected(source.get()).orElse(null);
        if(selection!=null && !(selection instanceof Symbolic || selection instanceof ExternalValue || selection instanceof UnboundValue))return selection;
        Optional<IntegralRange> range=Optional.ofNullable(path.selections().get(source.get())).flatMap(Selection::range);
        if(range.isPresent() && range.get().minimum()==range.get().maximum()) {
            long number=range.get().minimum();
            String primitive=atom instanceof ExternalValue external?external.descriptor():atom instanceof Symbolic symbolic?symbolic.type():atom instanceof UnboundValue value?value.descriptor():"";
            Object literal=switch(primitive) {
                case "Z" -> number!=0;case "B" -> (byte)number;case "S" -> (short)number;case "C" -> (char)number;
                case "I" -> (int)number;case "J" -> number;default -> null;
            };
            if(literal!=null)return new Literal(literal);
        }
        if(atom instanceof ObjectValue object) {
            Atom runtime=path.selected(source.get().at(new RuntimeClass())).orElse(null);
            if(runtime instanceof ClassValue type)return new ObjectValue(object.id(),Values.type(type.descriptor()),true,object.origin(),object.defaultFields(),object.source(),type.loader());
            if(object.type().startsWith("["))return object; // Current heap writes take precedence over input shape choices.
            if(!object.exact() && object.type().equals("java/lang/Object") && selection instanceof Symbolic typed && !typed.type().equals("java/lang/Object"))
                return new ObjectValue(object.id(),typed.type(),false,object.origin(),object.defaultFields(),object.source(),typed.loader());
        }
        String descriptor=atom instanceof ObjectValue object?object.type():atom instanceof ExternalValue external?external.descriptor():atom instanceof Symbolic symbolic?symbolic.type():atom instanceof UnboundValue value?value.descriptor():"";
        if(descriptor.startsWith("[")) {
            Atom size=path.selected(source.get().at(new Length())).orElse(null);
            if(size instanceof Literal literal && literal.value() instanceof Integer count && count>=0 && count<=64) {
                List<Atom> elements=new ArrayList<>();
                for(int i=0;i<count;i++) {
                    InputLocation slot=source.get().at(new Index(i));Atom element=path.selected(slot).orElse(null);
                    if(element==null)return atom;elements.add(element);
                }
                return new ArrayValue(-1,descriptor.equals("[Ljava/lang/Class;")?ArrayRole.METHOD_TYPES:ArrayRole.PROXY_ARGUMENTS,descriptor,elements);
            }
        }
        return atom instanceof Symbolic && selection instanceof Symbolic?selection:atom;
    }
}
