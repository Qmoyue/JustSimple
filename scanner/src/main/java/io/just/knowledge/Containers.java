package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Mechanisms.*;
import java.util.*;

final class Containers implements Model {
    private final JdkStructures structure;
    Containers(JdkStructures structure) { this.structure=structure; }

    /** Native insertion uses the same key/equality semantics, with the native read witnesses. */
    static Local decoded(Invocation read,ObjectValue container,Atom key,Atom value,JdkStructures.Witness witness) {
        boolean set=container.type().equals("java/util/HashSet");
        MethodId api=new MethodId(set?"java/util/HashSet":"java/util/HashMap",set?"add":"put",set?"(Ljava/lang/Object;)Z":"(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");
        Call call=new Call(read.call().site(),api,org.objectweb.asm.Opcodes.INVOKEVIRTUAL,new Sources(Set.of()),List.of());
        List<Gap> gaps=new ArrayList<>(Mechanisms.queryGaps(read,new Query<>(Optional.empty(),witness.pending())));
        if(witness.sites().isEmpty())gaps.add(Mechanisms.gap(read,GapKind.UNSUPPORTED,"selected JDK serialized-key structure not verified"));
        return Local.of(new Conditional(read.path(),gaps,Set.of(),Local.of(
                new Evaluate(new Invocation(call,container,set?List.of(key):List.of(key,value),read.result(),read.path())),
                new Observe(Kind.CONTAINER_CALLBACK,"native insertion of the resolved key",witness.sites(),List.of()))));
    }

    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        MethodId api=call.call().target();
        if ((call.is("java/lang/String","valueOf","(Ljava/lang/Object;)Ljava/lang/String;")
                || call.is("java/lang/StringBuilder","append","(Ljava/lang/Object;)Ljava/lang/StringBuilder;"))) {
            Atom value=call.arguments().get(0);
            List<Effect> effects=new ArrayList<>();
            boolean builder=api.owner().equals("java/lang/StringBuilder");
            if (value instanceof Literal literal && literal.value()==null) {if (!builder) effects.add(Mechanisms.result(new Literal("null")));}
            else if (value instanceof ObjectValue object) {
                List<Gap> gaps=object.exact()?List.of():Mechanisms.unknown(call,"stringification receiver runtime type is not exact");
                addCallback(effects,call,object,"toString","()Ljava/lang/String;",List.of(),structure.stringPath(),gaps,program,
                        ReturnFlow.TO_RESULT);
            } else if (value instanceof Literal literal && literal.value() instanceof String) {if (!builder) effects.add(Mechanisms.result(value));}
            else if (!builder) effects.add(Mechanisms.result(new Unknown("stringification value is unspecified")));
            if (effects.isEmpty()) effects.add(new Result(Value.of(new Unknown("unmodeled platform stringification")).requiring(List.of(Mechanisms.gap(call,GapKind.UNSUPPORTED,"platform stringification result is unspecified")))));
            if(builder && call.receiver() instanceof ObjectValue receiver) {
                Local stringified=new Local(effects);
                return Optional.of(Local.of(new Store(receiver,new Content(),Local.of(new Concat(bindings.read(receiver,new Content()),stringified))),Mechanisms.result(receiver)));
            }
            return Optional.of(new Local(effects));
        }
        if (!(call.receiver() instanceof ObjectValue receiver)) return Optional.empty();
        boolean map=program.subtype(receiver.type(),"java/util/Map");
        boolean put=map && api.name().equals("put") && api.descriptor().equals("(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");
        boolean get=map && api.name().equals("get") && api.descriptor().equals("(Ljava/lang/Object;)Ljava/lang/Object;");
        boolean add=receiver.type().equals("java/util/HashSet") && api.name().equals("add") && api.descriptor().equals("(Ljava/lang/Object;)Z");
        if (!put && !get && !add) return Optional.empty();
        Optional<Method> implementation=program.resolve(program.method(receiver.type(),api.name(),api.descriptor(),receiver.loader()));
        if (implementation.isEmpty() || !(Set.of("java/util/HashMap","java/util/TreeMap","java/util/HashSet","java/util/LinkedHashMap").contains(implementation.get().id().owner()))) return Optional.empty();
        boolean linkedGet=get && implementation.get().id().owner().equals("java/util/LinkedHashMap");
        boolean tree=implementation.get().id().owner().equals("java/util/TreeMap");
        Atom key=call.arguments().get(0);
        List<Effect> effects=new ArrayList<>();
        boolean stableOrder=true;
        if (receiver.type().equals("java/util/LinkedHashMap")) {
            Value flag=bindings.read(receiver,new Field(new FieldId("java/util/LinkedHashMap","accessOrder","Z")));
            stableOrder=flag.empty()?receiver.defaultFields():flag.alternatives().stream().allMatch(b -> b.atom() instanceof Literal l && (Boolean.FALSE.equals(l.value()) || l.value() instanceof Number n && n.intValue()==0));
            if (!stableOrder) effects.add(new Write(receiver,new IterationOrder(),Value.of(new Unknown("access-order mutation is not modeled")).requiring(List.of(Mechanisms.gap(call,GapKind.UNSUPPORTED,"LinkedHashMap access ordering may change iteration positions")))));
        }
        List<Gap> keyGaps=key instanceof ObjectValue object && object.exact() && receiver.exact()?List.of():Mechanisms.unknown(call,"container implementation or key runtime type is not exact");
        if (call.evaluation()==Evaluation.CALL && !tree && key instanceof ObjectValue object)
            addCallback(effects,call,object,"hashCode","()I",List.of(),add?structure.setAddPath():linkedGet?structure.linkedGetHashPath():get?structure.getHashKeyPath():structure.hashKeyPath(),keyGaps,program,ReturnFlow.IGNORE);
        Value priorKeys=bindings.read(receiver,new Elements()).under(call.path());
        Value comparator=tree?bindings.read(receiver,new Field(new FieldId("java/util/TreeMap","comparator","Ljava/util/Comparator;"))).under(call.path()):Value.BOTTOM;
        if(call.evaluation()==Evaluation.CALL && tree && priorKeys.empty())for(Bound selected:comparator.alternatives())if(!(selected.atom() instanceof Literal nil && nil.value()==null)) {
            Atom value=selected.atom();MethodId target=value instanceof ObjectValue object?program.method(object.type(),"compare","(Ljava/lang/Object;Ljava/lang/Object;)I",object.loader()):new MethodId("java/util/Comparator","compare","(Ljava/lang/Object;Ljava/lang/Object;)I");
            effects.add(new Conditional(selected.path(),selected.gaps(),selected.dependencies(),Local.of(new Dispatch(target,value,List.of(key,key),Kind.CONTAINER_CALLBACK,Evidence.CONDITIONAL,List.of(call.call().site()),List.of(),ReturnFlow.IGNORE,ExceptionFlow.DIRECT))));
        }
        Atom canonical=key;Value matches=Value.BOTTOM;List<Effect> comparisons=new ArrayList<>();
        boolean uncertain=false;
        for(Bound prior:priorKeys.alternatives()) {
            if(prior.atom().equals(key)){matches=matches.merge(Value.of(prior.atom(),prior.path()).requiring(prior.gaps()).tracing(prior.dependencies()));continue;}
            Value comparison=call.evaluation()==Evaluation.COMPARED_KEYS?bindings.read(call.result(),new KeyComparison(key,prior.atom())).under(prior.path()):Value.BOTTOM;
            if(comparison.empty() && key instanceof Literal a && prior.atom() instanceof Literal b) {
                if(tree && comparator.alternatives().stream().allMatch(bound -> bound.atom() instanceof Literal nil && nil.value()==null) && a.value() instanceof String left && b.value() instanceof String right)comparison=Value.of(new Literal(left.compareTo(right)),prior.path());
                else if(!tree)comparison=Value.of(new Literal(Objects.equals(a.value(),b.value())?1:0),prior.path());
            }
            if(comparison.empty() && call.evaluation()==Evaluation.CALL) {
                List<Gap> gaps=new ArrayList<>(keyGaps);gaps.addAll(prior.gaps());List<Effect> callbacks=new ArrayList<>();
                if(tree) {
                    for(Bound selected:comparator.under(prior.path()).alternatives())if(!(selected.atom() instanceof Literal nil && nil.value()==null)) {
                        Atom value=selected.atom();MethodId target=value instanceof ObjectValue object?program.method(object.type(),"compare","(Ljava/lang/Object;Ljava/lang/Object;)I",object.loader()):new MethodId("java/util/Comparator","compare","(Ljava/lang/Object;Ljava/lang/Object;)I");
                        callbacks.add(new Conditional(selected.path(),selected.gaps(),selected.dependencies(),Local.of(new Dispatch(target,value,List.of(key,prior.atom()),Kind.CONTAINER_CALLBACK,Evidence.CONDITIONAL,List.of(call.call().site()),gaps,ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT))));
                    }
                    boolean natural=comparator.empty() || comparator.alternatives().stream().anyMatch(bound -> bound.atom() instanceof Literal nil && nil.value()==null);
                    if(natural && key instanceof ObjectValue incoming)addCallback(callbacks,call,incoming,"compareTo","(Ljava/lang/Object;)I",List.of(prior.atom()),structure.compareKeyPath(),gaps,program,ReturnFlow.TO_RESULT);
                } else if(key instanceof ObjectValue incoming) {
                    OptionalInt incomingHash=hash(key,bindings,call.path(),program),priorHash=hash(prior.atom(),bindings,call.path(),program);
                    if(incomingHash.isPresent() && priorHash.isPresent() && incomingHash.getAsInt()!=priorHash.getAsInt())continue;
                    if(incomingHash.isEmpty() || priorHash.isEmpty())gaps.add(Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"equal key hashes/collision are not established"));
                    addCallback(callbacks,call,incoming,"equals","(Ljava/lang/Object;)Z",List.of(prior.atom()),linkedGet?structure.linkedGetEqualsPath():get?structure.getEqualsKeyPath():structure.equalsKeyPath(),gaps,program,ReturnFlow.TO_RESULT);
                }
                if(!callbacks.isEmpty()) {
                    comparisons.add(new Conditional(prior.path(),prior.gaps(),prior.dependencies(),Local.of(new Store(call.result(),new KeyComparison(key,prior.atom()),new Local(callbacks)))));
                    continue;
                }
            }
            boolean resolved=!comparison.empty();Set<Integer> outcomes=new HashSet<>();
            for(Bound result:comparison.alternatives()) {
                if(!(result.atom() instanceof Literal literal) || !(literal.value() instanceof Number number)){resolved=false;continue;}
                outcomes.add(number.intValue()==(tree?0:1)?1:0);
                if(number.intValue()==(tree?0:1)) {
                    canonical=prior.atom();
                    matches=matches.merge(Value.of(prior.atom(),result.path()).requiring(prior.gaps()).requiring(result.gaps()).tracing(prior.dependencies()).tracing(result.dependencies()));
                }
            }
            if(outcomes.size()>1)resolved=false;
            if(!resolved) {
                uncertain=true;
                Gap gap=Mechanisms.gap(call,GapKind.CONTROL_CONDITION,"container key equality remains unresolved for this binding");
                List<Gap> gaps=new ArrayList<>(prior.gaps());gaps.add(gap);Set<Integer> dependencies=new LinkedHashSet<>(prior.dependencies());
                for(Bound result:comparison.alternatives()){gaps.addAll(result.gaps());dependencies.addAll(result.dependencies());}
                matches=matches.merge(Value.of(prior.atom(),prior.path()).requiring(gaps).tracing(dependencies));
            }
        }
        if(!comparisons.isEmpty()) {effects.addAll(comparisons);effects.add(new Evaluate(call.comparedKeys()));return Optional.of(new Local(effects));}
        if(uncertain && receiver.type().equals("java/util/LinkedHashMap")) {
            stableOrder=false;
            effects.add(new Write(receiver,new IterationOrder(),Value.of(new Unknown("key replacement ordering remains conditional")).requiring(Mechanisms.unknown(call,"key equality must be established before reusing an iteration position"))));
        }
        if (get) {
            Value values=bindings.read(receiver,new MapKey(key)).under(call.path());
            for(Bound match:matches.alternatives())values=values.merge(bindings.read(receiver,new MapKey(match.atom())).under(match.path()).requiring(match.gaps()).tracing(match.dependencies()));
            if(uncertain)values=values.requiring(Mechanisms.unknown(call,"container lookup depends on unresolved key equality"));
            if (values.empty()) values=Value.of(new Unknown("map key equality/value binding is not supplied")).requiring(Mechanisms.unknown(call,"map lookup has no exact key binding"));
            effects.add(new Result(values));
            return Optional.of(new Local(effects));
        }
        effects.add(new Write(receiver,new Elements(),Value.of(key)));
        if(!receiver.type().equals("java/util/LinkedHashMap"))for(Bound length:bindings.read(receiver,new Length()).under(call.path()).alternatives()) {
            Atom size=uncertain?new Unknown("container size depends on unresolved key equality"):length.atom() instanceof Literal literal && literal.value() instanceof Integer count?new Literal(count+(matches.empty()?1:0)):new Unknown("container size unspecified");
            effects.add(new Write(receiver,new Length(),Value.of(size,length.path()).requiring(length.gaps()).tracing(length.dependencies())));
        }
        if (put) {
            Atom value=call.arguments().get(1);
            effects.add(new Write(receiver,new MapValues(),Value.of(value)));
            effects.add(new Write(receiver,new MapKey(key),Value.of(value)));
            for(Bound match:matches.alternatives()) {
                Value replacement=Value.of(value,match.path()).requiring(match.gaps()).tracing(match.dependencies());
                if(uncertain)replacement=replacement.merge(bindings.read(receiver,new MapKey(match.atom())).under(match.path()).requiring(Mechanisms.unknown(call,"prior key may remain distinct")));
                effects.add(new Write(receiver,new MapKey(match.atom()),replacement));
            }
            if (receiver.type().equals("java/util/LinkedHashMap") && stableOrder) {
                Value positions=bindings.read(receiver,new KeyIndex(canonical));
                if (positions.empty()) positions=bindings.read(receiver,new Length());
                for (Bound position:positions.under(call.path()).alternatives()) if (position.atom() instanceof Literal literal && literal.value() instanceof Integer index) {
                    effects.add(new Write(receiver,new Index(index),Value.of(value,position.path()).requiring(position.gaps()).tracing(position.dependencies())));
                    effects.add(new Write(receiver,new KeyIndex(key),Value.of(new Literal(index),position.path()).requiring(position.gaps()).tracing(position.dependencies())));
                    if (bindings.read(receiver,new KeyIndex(canonical)).empty()) effects.add(new Write(receiver,new Length(),Value.of(new Literal(index+1),position.path()).requiring(position.gaps()).tracing(position.dependencies())));
                }
            }
        }
        Value previous=Value.BOTTOM;
        for(Bound match:matches.alternatives())previous=previous.merge(bindings.read(receiver,new MapKey(match.atom())).under(match.path()).requiring(match.gaps()).tracing(match.dependencies()));
        effects.add(new Result(put?(previous.empty()?Value.NULL:previous):uncertain?Value.of(new Unknown("set membership unresolved")):Value.of(new Literal(matches.empty()?1:0))));
        return Optional.of(new Local(effects));
    }

    private static void addCallback(List<Effect> effects,Invocation call,ObjectValue receiver,String name,String descriptor,List<Atom> arguments,
                                    JdkStructures.Witness witness,List<Gap> required,Program program,ReturnFlow returns) {
        Query<Method> resolution=program.lookup(program.method(receiver.type(),name,descriptor,receiver.loader()));
        Optional<Method> target=resolution.value();
        if (target.isEmpty() && resolution.pending().isEmpty()) return;
        List<Gap> gaps=new ArrayList<>(required);
        gaps.addAll(Mechanisms.queryGaps(call,resolution));
        gaps.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),witness.pending())));
        List<Site> witnesses=witness.sites();
        if (witnesses.isEmpty()) gaps.add(Mechanisms.gap(call,GapKind.UNSUPPORTED,"selected JDK callback structure not verified: "+name));
        MethodId selected=target.map(Method::id).orElse(new MethodId(receiver.type(),name,descriptor));
        effects.add(new Dispatch(selected,receiver,arguments,Kind.CONTAINER_CALLBACK,gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,witnesses,List.copyOf(gaps),returns,ExceptionFlow.DIRECT));
        effects.add(new Observe(Kind.CONTAINER_CALLBACK,"callback "+selected+" on the bound receiver",witnesses,List.copyOf(gaps)));
    }

    private static OptionalInt hash(Atom atom,Bindings bindings,Path path,Program program) {
        if (atom instanceof Literal literal && literal.value() instanceof String string) { int hash=0; for (int i=0;i<string.length();i++) hash=31*hash+string.charAt(i); return OptionalInt.of(hash); }
        if(atom instanceof ObjectValue object && object.type().equals("java/lang/Integer") && object.loader()==0) {
            Set<Integer> values=new HashSet<>();
            for(Bound bound:bindings.read(object,new Content()).under(path).alternatives()) {
                if(!(bound.atom() instanceof Literal literal) || !(literal.value() instanceof Integer number))return OptionalInt.empty();values.add(number);
            }
            return values.size()==1?OptionalInt.of(values.iterator().next()):OptionalInt.empty();
        }
        if (!(atom instanceof ObjectValue object) || !object.exact()) return OptionalInt.empty();
        Optional<Method> method=program.resolve(program.method(object.type(),"hashCode","()I",object.loader()));
        if (method.isEmpty() || !method.get().hasBody()) return OptionalInt.empty();
        Facts facts=program.facts(method.get().id());
        if (!facts.limitations().isEmpty() || facts.actions().stream().anyMatch(a -> !(a instanceof Constant || a instanceof Returned))) return OptionalInt.empty();
        Set<Integer> values=new HashSet<>();
        for (Action action:facts.actions()) if (action instanceof Returned returned) for (Origin origin:returned.value().origins()) {
            if (!(origin instanceof Producer producer)) return OptionalInt.empty();
            for (Action source:facts.actions()) if (source.site().instruction()==producer.instruction() && source instanceof Constant constant && constant.value() instanceof LiteralConstant value && value.value() instanceof Integer number) values.add(number);
        }
        return values.size()==1?OptionalInt.of(values.iterator().next()):OptionalInt.empty();
    }
}
