package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import java.util.*;

/** Static entry discovery, independent of local models, heap bindings and analysis scheduling. */
public final class EntryPoints {
    public enum Mode { APPLICATION, COMPONENT }
    public record Entry(Method method,String boundary,List<String> assumptions) {
        public Entry {assumptions=List.copyOf(assumptions);}
    }
    private static final Set<String> CONTROLLERS=Set.of(
            "Lorg/springframework/web/bind/annotation/RestController;","Lorg/springframework/stereotype/Controller;");
    private static final Set<String> MAPPINGS=Set.of(
            "Lorg/springframework/web/bind/annotation/RequestMapping;","Lorg/springframework/web/bind/annotation/GetMapping;",
            "Lorg/springframework/web/bind/annotation/PostMapping;","Lorg/springframework/web/bind/annotation/PutMapping;",
            "Lorg/springframework/web/bind/annotation/DeleteMapping;","Lorg/springframework/web/bind/annotation/PatchMapping;");
    private final Program program;

    public EntryPoints(Program program){this.program=program;}

    public Query<List<Entry>> find(Mode mode,Set<MethodId> selected) {
        List<Entry> entries=new ArrayList<>();Set<QueryIssue> pending=new LinkedHashSet<>();
        if(!selected.isEmpty()) {
            for(MethodId id:selected) {
                Query<Method> query=program.declaration(id);pending.addAll(query.pending());
                query.value().filter(Method::hasBody).ifPresent(method -> entries.add(new Entry(method,
                        "explicit static boundary (caller unspecified)",List.of("caller reachability and input availability are supplied boundary assumptions"))));
            }
        } else if(mode==Mode.COMPONENT) {
            for(ClassInfo type:program.targets())for(Method method:type.methods())
                if(method.hasBody() && method.isPublic() && !method.id().name().startsWith("<"))
                    entries.add(new Entry(method,"public component method (caller and arguments unspecified)",List.of()));
        } else {
            for(ClassInfo type:program.targets()) {
                List<ClassInfo> hierarchy=hierarchy(type,pending);
                if(!annotated(hierarchy.stream().flatMap(parent -> parent.annotations().stream()).toList(),CONTROLLERS,pending))continue;
                Query<List<Method>> methods=program.methods(type.name(),false);pending.addAll(methods.pending());
                for(Method method:methods.value().orElseThrow()) {
                    if(!method.hasBody() || !method.isPublic() || method.id().name().startsWith("<"))continue;
                    List<Annotation> routes=hierarchy.stream().flatMap(parent -> parent.methods().stream())
                            .filter(member -> member.id().name().equals(method.id().name()) && member.id().descriptor().equals(method.id().descriptor()))
                            .flatMap(member -> member.annotations().stream()).filter(annotation -> annotated(List.of(annotation),MAPPINGS,pending)).toList();
                    if(!routes.isEmpty())entries.add(new Entry(method,"Spring MVC "+type.name()+" "+type.annotations().stream().filter(a -> MAPPINGS.contains(a.descriptor())).toList()+" "+routes,
                            List.of("controller registration and HTTP exposure are deployment assumptions")));
                }
            }
            Query<List<Entry>> http=HttpBridge.entries(program);entries.addAll(http.value().orElseThrow());pending.addAll(http.pending());
        }
        return new Query<>(Optional.of(List.copyOf(entries)),List.copyOf(pending));
    }

    private boolean annotated(List<Annotation> annotations,Set<String> markers,Set<QueryIssue> issues) {
        Set<String> seen=new HashSet<>();ArrayDeque<Annotation> pending=new ArrayDeque<>(annotations);
        while(!pending.isEmpty() && seen.size()<64) {
            Annotation annotation=pending.removeFirst();String descriptor=annotation.descriptor();
            if(markers.contains(descriptor))return true;
            if(!seen.add(descriptor) || descriptor.startsWith("Ljava/lang/annotation/"))continue;
            Query<ClassInfo> type=program.definition(Values.type(descriptor),0);issues.addAll(type.pending());
            type.value().ifPresent(info -> pending.addAll(info.annotations()));
        }
        if(!pending.isEmpty())issues.add(new QueryIssue(QueryCause.BUDGET,"entry annotation frontier (64)"));
        return false;
    }

    private List<ClassInfo> hierarchy(ClassInfo type,Set<QueryIssue> issues) {
        List<ClassInfo> result=new ArrayList<>();Set<String> seen=new HashSet<>();ArrayDeque<ClassInfo> pending=new ArrayDeque<>(List.of(type));
        while(!pending.isEmpty() && seen.size()<64) {
            ClassInfo current=pending.removeFirst();if(!seen.add(current.name()))continue;result.add(current);
            List<String> parents=new ArrayList<>(current.interfaces());if(current.parent()!=null)parents.add(0,current.parent());
            for(String name:parents) {
                Query<ClassInfo> parent=program.definition(name,current.loader());issues.addAll(parent.pending());parent.value().ifPresent(pending::addLast);
            }
        }
        if(!pending.isEmpty())issues.add(new QueryIssue(QueryCause.BUDGET,"entry hierarchy frontier (64): "+type.name()));
        return List.copyOf(result);
    }
}
