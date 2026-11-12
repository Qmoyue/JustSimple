package io.just.analysis;

import io.just.analysis.ScanResult.InputRequirement;
import io.just.knowledge.Values;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.program.Program.*;
import java.util.*;

/** The analysis owns these typed needs; reports never infer them from diagnostic prose. */
final class InputRequirements {
    private record Question(Atom subject,Optional<Slot> slot,NeedKind kind,String descriptor,List<Atom> choices) {}
    private record Use(int context,Site site) {}
    private record Coordinate(Use use,Path path,Question question) {}
    private final Map<Use,Map<Path,Map<Question,InputRequirement>>> requirements=new LinkedHashMap<>();
    private final Map<Optional<InputLocation>,LinkedHashSet<Coordinate>> sources=new LinkedHashMap<>();
    private final int limit;
    private int size;
    InputRequirements(int limit){this.limit=limit;}
    boolean add(int context,MethodId entry,Site use,Path path,InputNeed original,Collection<Integer> dependencies) {
        boolean retained=true;
        if(original.choices().size()==1 && original.choices().get(0) instanceof ArrayValue chosen && original.subject() instanceof ArrayValue actual
                && actual.elements().size()==chosen.elements().size()) {
            for(int index=0;index<actual.elements().size();index++)retained&=className(context,entry,use,path,actual.elements().get(index),chosen.elements().get(index),original.reason(),dependencies);
        } else if(original.choices().size()==1)retained=className(context,entry,use,path,original.subject(),original.choices().get(0),original.reason(),dependencies);
        Optional<InputNeed> normalized=Mechanisms.stringInput(original);
        if(normalized.isEmpty())return retained;
        InputNeed input=normalized.get();
        Optional<InputLocation> topic=Values.location(input.subject());
        if(input.slot().isPresent())topic=topic.map(s -> s.at(input.slot().get()));
        Optional<InputSource> source=topic.filter(InputSource.class::isInstance).map(InputSource.class::cast);
        Optional<InputSource> location=source;
        Use at=new Use(context,use);Map<Path,Map<Question,InputRequirement>> paths=requirements.get(at);
        Map<Question,InputRequirement> rows=paths==null?Map.of():paths.getOrDefault(path,Map.of());
        java.util.function.Predicate<InputRequirement> same=item -> location.isPresent()?item.source().equals(location):item.needed().subject().equals(input.subject()) && item.needed().slot().equals(input.slot());
        if(input.kind()==NeedKind.VALUE && rows.values().stream().anyMatch(item -> same.test(item) && item.needed().kind()!=NeedKind.VALUE))return retained;
        if(input.kind()!=NeedKind.VALUE && !rows.isEmpty()) {
            for(var row:List.copyOf(rows.entrySet()))if(same.test(row.getValue()) && row.getValue().needed().kind()==NeedKind.VALUE)remove(new Coordinate(at,path,row.getKey()));
        }
        Question key=new Question(input.subject(),input.slot(),input.kind(),input.descriptor(),input.choices());InputRequirement previous=rows.get(key);
        if(previous==null && size>=limit) {if(!makeRoom(topic,input.kind()))return false;retained=false;}
        Set<Integer> required=new LinkedHashSet<>(dependencies);if(previous!=null)required.addAll(previous.dependencies());
        paths=requirements.computeIfAbsent(at,k -> new LinkedHashMap<>());rows=paths.computeIfAbsent(path,k -> new LinkedHashMap<>());
        rows.put(key,new InputRequirement(previous==null?size++:previous.id(),entry,context,use,path,source,input,required.stream().sorted().toList()));
        if(previous==null)sources.computeIfAbsent(topic,k -> new LinkedHashSet<>()).add(new Coordinate(at,path,key));return retained;
    }
    private Optional<InputLocation> location(InputRequirement row) {
        if(row.source().isPresent())return row.source().map(source -> (InputLocation)source);
        Optional<InputLocation> location=Values.location(row.needed().subject());return row.needed().slot().isPresent()?location.map(source -> source.at(row.needed().slot().get())):location;
    }
    private void unindex(Optional<InputLocation> source,Coordinate coordinate) {
        Set<Coordinate> group=sources.get(source);group.remove(coordinate);if(group.isEmpty())sources.remove(source);
    }
    private void remove(Coordinate coordinate) {
        Map<Path,Map<Question,InputRequirement>> paths=requirements.get(coordinate.use());Map<Question,InputRequirement> rows=paths.get(coordinate.path());
        InputRequirement row=rows.remove(coordinate.question());unindex(location(row),coordinate);size--;
        if(rows.isEmpty())paths.remove(coordinate.path());if(paths.isEmpty())requirements.remove(coordinate.use());
    }
    private Coordinate last(Collection<Coordinate> rows) {return rows.stream().reduce((first,next) -> next).orElseThrow();}
    private boolean makeRoom(Optional<InputLocation> source,NeedKind kind) {
        Set<Coordinate> own=sources.getOrDefault(source,new LinkedHashSet<>());
        List<Coordinate> generic=own.stream().filter(row -> row.question().kind()==NeedKind.VALUE).toList();
        if(kind!=NeedKind.VALUE && !generic.isEmpty()){remove(last(generic));return true;}
        int count=own.size();
        for(var group:sources.entrySet())if(!group.getKey().equals(source) && group.getValue().size()>Math.max(1,count)) {
            List<Coordinate> values=group.getValue().stream().filter(row -> row.question().kind()==NeedKind.VALUE).toList();
            if(!values.isEmpty()){remove(last(values));return true;}
            Map<NeedKind,Integer> kinds=new EnumMap<>(NeedKind.class);for(Coordinate row:group.getValue())kinds.merge(row.question().kind(),1,Integer::sum);
            List<Coordinate> repeated=group.getValue().stream().filter(row -> kinds.get(row.question().kind())>1).toList();
            remove(last(repeated.isEmpty()?group.getValue():repeated));return true;
        }
        return false;
    }
    private boolean className(int context,MethodId entry,Site use,Path path,Atom subject,Atom choice,String reason,Collection<Integer> dependencies) {
        Optional<InputLocation> named=Values.location(subject).filter(location -> !location.path().isEmpty() && location.path().get(location.path().size()-1) instanceof NamedClass);
        if(named.isEmpty() || !(choice instanceof ClassValue type) || !type.exact())return true;
        InputLocation location=Values.parent(named.get());Atom original;
        if(location instanceof InputSource input)original=new ExternalValue("Ljava/lang/String;",input);
        else if(location instanceof ValueSource value && value.path().isEmpty())original=value.producer();
        else return true;
        return add(context,entry,use,path,new InputNeed(original,Optional.empty(),NeedKind.CLASS_NAME,"Ljava/lang/String;",
                List.of(new Literal(Values.type(type.descriptor()).replace('/','.'))),reason),dependencies);
    }
    List<InputRequirement> snapshot(){return snapshot(path -> true);}
    List<InputRequirement> snapshot(java.util.function.Predicate<Path> possible){
        List<InputRequirement> result=new ArrayList<>();
        for(var paths:requirements.values())for(var rows:paths.values())for(InputRequirement item:rows.values()) {
            if(!possible.test(item.conditions()))continue;
            result.add(new InputRequirement(result.size(),item.entry(),item.context(),item.use(),item.conditions(),item.source(),item.needed(),item.dependencies()));
        }
        return List.copyOf(result);
    }
}
