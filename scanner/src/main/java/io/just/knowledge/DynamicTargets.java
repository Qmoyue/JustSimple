package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import java.util.*;

/** Finite goals and their bytecode callers. This service proposes members, not bindings. */
final class DynamicTargets {
    private record Family(String owner,String name) {}
    private final Program program;
    private record Goals(List<ClassInfo> scope,Query<List<Method>> members,Query<List<Method>> publicMembers) {}
    private Optional<Goals> goals=Optional.empty();
    private final Set<MethodId> sinks;
    private final Guidance guidance;
    DynamicTargets(Program program,Set<MethodId> sinks,Guidance guidance){this.program=program;this.sinks=Set.copyOf(sinks);this.guidance=guidance;}

    Query<List<Method>> members(Atom owner,boolean declared) {
        if(owner instanceof ClassValue type && type.exact()) {
            Query<List<Method>> known=program.methods(Values.type(type.descriptor()),declared,type.loader());
            List<Method> ordered=known.value().orElseThrow().stream().sorted(Comparator.comparing((Method m) -> !priority(m.id()))).toList();
            int goals=0;while(goals<ordered.size() && priority(ordered.get(goals).id()))goals++;
            Query<List<Method>> selected=order(ordered,goals);List<QueryIssue> pending=new ArrayList<>(known.pending());pending.addAll(selected.pending());
            return new Query<>(selected.value(),pending);
        }
        List<ClassInfo> scope=program.candidates();
        Goals view=goals.filter(known -> known.scope()==scope).orElseGet(() -> {
            Set<MethodId> seeds=new LinkedHashSet<>(sinks);
            // A public factory returning a public impact receiver is a producer goal, not a recipe.
            List<QueryIssue> pending=new ArrayList<>();
            for(String receiver:Mechanisms.impactTargets().stream().filter(id -> program.lookup(id).value().filter(Method::isPublic).isPresent()).map(MethodId::owner).distinct().sorted().toList()) {
                Query<List<Method>> methods=program.methods(receiver,false);pending.addAll(methods.pending());
                for(Method method:methods.value().orElse(List.of()))
                    if(method.isStatic() && program.signature(method.id()).returned().descriptor().equals("L"+receiver+";"))seeds.add(method.id());
            }
            seeds.add(new MethodId("java/lang/Class","forName","(Ljava/lang/String;)Ljava/lang/Class;"));
            seeds.add(new MethodId("java/lang/Class","getMethod","(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;"));
            seeds.add(Reflection.INVOKE);
            seeds.addAll(Mechanisms.impactTargets().stream().sorted(Comparator.comparing(MethodId::toString)).toList());
            seeds.addAll(ClassDefinitions.entries());
            Query<List<Method>> found=program.candidateMethods(seeds,128);pending.addAll(found.pending());
            Map<MethodId,Method> all=new LinkedHashMap<>();
            for(MethodId seed:seeds)program.lookup(seed).value().filter(m -> !m.id().name().startsWith("<")).ifPresent(m -> all.putIfAbsent(m.id(),m));
            int goalCount=all.size();
            found.value().orElseThrow().stream().filter(m -> program.type(m.id().owner(),m.id().loader()).filter(info -> info.role()==io.just.input.Inputs.Role.TARGET).isPresent()).forEach(m -> all.putIfAbsent(m.id(),m));
            for(ClassInfo type:program.targets())for(Method method:type.methods())if(!method.id().name().startsWith("<"))all.putIfAbsent(method.id(),method);
            found.value().orElseThrow().forEach(m -> all.putIfAbsent(m.id(),m));
            for(ClassInfo type:scope)for(Method method:type.methods())if(!method.id().name().startsWith("<"))all.putIfAbsent(method.id(),method);
            Query<List<Method>> selected=order(List.copyOf(all.values()),goalCount);pending.addAll(selected.pending());List<QueryIssue> issues=List.copyOf(new LinkedHashSet<>(pending));
            Goals prepared=new Goals(scope,new Query<>(selected.value(),issues),
                    new Query<>(Optional.of(selected.value().orElseThrow().stream().filter(Method::isPublic).toList()),issues));
            goals=Optional.of(prepared);return prepared;
        });
        Query<List<Method>> candidates=declared?view.members():view.publicMembers();
        if(!(owner instanceof ClassValue type) || type.descriptor().equals("Ljava/lang/Object;") && type.loader()==0)return candidates;
        List<Method> result=candidates.value().orElseThrow().stream().filter(method -> {
            Query<Boolean> match=program.assignable(method.id().owner(),method.id().loader(),Values.type(type.descriptor()),type.loader());
            if(!match.value().equals(Optional.of(false)) || !match.pending().isEmpty())return true;
            Query<Boolean> inherited=program.assignable(Values.type(type.descriptor()),type.loader(),method.id().owner(),method.id().loader());
            if(!inherited.value().equals(Optional.of(false)) || !inherited.pending().isEmpty())return true;
            Optional<ClassInfo> upper=program.type(Values.type(type.descriptor()),type.loader()),declaration=program.type(method.id().owner(),method.id().loader());
            if(upper.isEmpty() || declaration.isEmpty())return true;
            // An open class and an interface, or two interfaces, can share a concrete implementation.
            return (upper.get().access() & org.objectweb.asm.Opcodes.ACC_FINAL)==0 && (declaration.get().access() & org.objectweb.asm.Opcodes.ACC_FINAL)==0
                    && ((upper.get().access() | declaration.get().access()) & org.objectweb.asm.Opcodes.ACC_INTERFACE)!=0;
        }).toList();
        return new Query<>(Optional.of(result),candidates.pending());
    }
    /** Existing producers and impact goals precede a merely partial candidate-body shape. */
    private Query<List<Method>> order(List<Method> methods,int goals) {
        Query<List<Method>> selected=guidance.order(methods.subList(goals,methods.size()));
        List<Method> result=new ArrayList<>(methods.subList(0,goals));result.addAll(selected.value().orElseThrow());
        return new Query<>(Optional.of(fair(result)),selected.pending());
    }
    boolean priority(MethodId id) {
        return sinks.contains(id) || Mechanisms.impact(id) || ClassDefinitions.entries().contains(id) || id.equals(Reflection.INVOKE)
                || (id.equals(new MethodId("java/lang/Class","forName","(Ljava/lang/String;)Ljava/lang/Class;")) || id.equals(new MethodId("java/lang/Class","getMethod","(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;")))
                || program.declared(id).filter(Method::isStatic).isPresent() && program.signature(id).returned().descriptor().equals("L"+id.owner()+";");
    }
    private List<Method> fair(List<Method> methods) {
        Map<Family,ArrayDeque<Method>> families=new LinkedHashMap<>();
        for(Method method:methods)families.computeIfAbsent(new Family(method.id().owner(),method.id().name()),k -> new ArrayDeque<>()).addLast(method);
        List<Method> result=new ArrayList<>();ArrayDeque<ArrayDeque<Method>> pending=new ArrayDeque<>(families.values());
        while(!pending.isEmpty()) {
            ArrayDeque<Method> family=pending.removeFirst();Method first=family.removeFirst();result.add(first);
            if(sinks.contains(first.id()) || Mechanisms.impact(first.id()))while(!family.isEmpty() && (sinks.contains(family.peekFirst().id()) || Mechanisms.impact(family.peekFirst().id())))result.add(family.removeFirst());
            if(!family.isEmpty())pending.addLast(family);
        }
        return List.copyOf(result);
    }
}
