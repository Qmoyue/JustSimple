package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.Hint;
import java.util.*;

/** Scan-local structural queries. No invocation bindings, heap or scheduling state live here. */
final class Guidance {
    private final Program program;
    private final Catalog catalog;
    private final LinkedHashMap<MethodId,Query<List<Hint>>> reached=new LinkedHashMap<>(16,.75f,true);
    private int retainedHints;
    private record Dispatch(MethodId method,String upper,int loader) {}
    private final LinkedHashMap<Dispatch,Query<List<DefinedType>>> preferred=new LinkedHashMap<>();
    private int definitions=-1;
    private boolean enabled=true;
    Guidance(Program program,Catalog catalog){this.program=program;this.catalog=catalog;}
    void enabled(boolean value){enabled=value;}
    boolean active(){return enabled && !catalog.emptyRelations();}
    private void refresh(){if(definitions!=program.definitionCount()){definitions=program.definitionCount();reached.clear();preferred.clear();retainedHints=0;}}
    Query<List<Hint>> local(MethodId method) {
        refresh();Query<List<Hint>> cached=reached.get(method);if(cached!=null)return cached;
        Query<List<Hint>> builtin=Structures.local(program,method),reference=catalog.hints(program,Set.of(method));
        List<Hint> values=new ArrayList<>(builtin.value().orElseThrow());values.addAll(reference.value().orElseThrow());
        Set<QueryIssue> pending=new LinkedHashSet<>(builtin.pending());pending.addAll(reference.pending());
        Query<List<Hint>> result=new Query<>(Optional.of(List.copyOf(values)),List.copyOf(pending));
        if(values.size()<=8192) {
            while(!reached.isEmpty() && (reached.size()>=1024 || retainedHints+values.size()>8192))retainedHints-=reached.remove(reached.keySet().iterator().next()).value().orElseThrow().size();
            reached.put(method,result);retainedHints+=values.size();
        }
        return result;
    }
    boolean member(MethodId method) {
        if(!enabled || catalog.emptyRelations())return false;
        if(program.declared(method).filter(Method::hasBody).isEmpty())return false;
        if(program.calls(method).value().orElseThrow().stream().noneMatch(call -> catalog.applicable(CallShape.signature(program,call.target()))))return false;
        // A receiver read from an owned slot is a useful handoff; a bare super forwarder is not.
        return local(method).value().orElseThrow().stream().filter(h -> !h.references().isEmpty()).flatMap(h -> h.requirements().stream())
                .anyMatch(r -> r.pattern().operands().get(0).steps().stream().anyMatch(s -> s.kind()==CallShape.SourceKind.FIELD || s.kind()==CallShape.SourceKind.ELEMENT || s.kind()==CallShape.SourceKind.RETURN));
    }
    Query<List<DefinedType>> receivers(MethodId requested,String upper,int loader) {
        if(!enabled || catalog.emptyRelations())return new Query<>(Optional.of(List.of()),List.of());
        refresh();Dispatch key=new Dispatch(requested,upper,loader);Query<List<DefinedType>> cached=preferred.get(key);if(cached!=null)return cached;
        List<DefinedType> result=new ArrayList<>();List<QueryIssue> pending=new ArrayList<>();int checked=0;
        for(ClassInfo type:program.concreteTypes(upper,loader)) {
            if(checked++>=2048){pending.add(new QueryIssue(QueryCause.BUDGET,"relation receiver metadata frontier (2048): "+requested));break;}
            MethodId candidate=new MethodId(type.name(),requested.name(),requested.descriptor(),type.loader());
            if(program.declared(candidate).filter(Method::hasBody).isEmpty())continue;
            if(member(candidate)){result.add(new DefinedType(type.name(),type.loader()));if(result.size()>=48){pending.add(new QueryIssue(QueryCause.BUDGET,"relation receiver preference frontier (48): "+requested));break;}}
        }
        Query<List<DefinedType>> query=new Query<>(Optional.of(List.copyOf(result)),pending);
        if(preferred.size()>=1024)preferred.remove(preferred.keySet().iterator().next());preferred.put(key,query);return query;
    }
    Query<List<Method>> order(List<Method> methods) {
        if(!enabled || catalog.emptyRelations())return new Query<>(Optional.of(methods),List.of());
        ArrayDeque<Method> ranked=new ArrayDeque<>();Set<MethodId> chosen=new HashSet<>();List<QueryIssue> pending=new ArrayList<>();int examined=0;
        for(Method method:methods) {
            if(examined++>=2048){pending.add(new QueryIssue(QueryCause.BUDGET,"relation member metadata frontier (2048)"));break;}
            if(member(method.id())){ranked.add(method);chosen.add(method.id());if(ranked.size()>=48)break;}
        }
        if(ranked.isEmpty())return new Query<>(Optional.of(methods),pending);
        ArrayDeque<Method> plain=new ArrayDeque<>(methods);List<Method> result=new ArrayList<>();int turn=0;
        while(!plain.isEmpty() || !ranked.isEmpty()) {
            if(!ranked.isEmpty() && (turn++%4==0 || plain.isEmpty()))result.add(ranked.removeFirst());
            else {Method method=plain.removeFirst();if(!chosen.contains(method.id()))result.add(method);}
        }
        return new Query<>(Optional.of(List.copyOf(result)),pending);
    }
    /** A class's uncalled methods cannot justify preferring a different callback of that class. */
    Query<Boolean> callbacks(Collection<Method> methods) {
        Set<MethodId> roots=new LinkedHashSet<>();
        for(Method method:methods)if(method.hasBody()) {
            if(member(method.id()))return new Query<>(Optional.of(true),List.of());
            roots.add(method.id());
        }
        if(roots.isEmpty())return new Query<>(Optional.of(false),List.of());
        Query<Set<MethodId>> scope=program.discover(roots,256);
        return new Query<>(Optional.of(scope.value().orElseThrow().stream().anyMatch(this::member)),scope.pending());
    }
}
