package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Mechanisms.*;
import java.util.*;

/** Shared value/array operations used by concrete mechanisms; no scheduling or heap ownership. */
public final class ValueBindings {
    private ValueBindings() {}
    /** Direct mutable backing/captured references; callers own traversal, visibility and its budget. */
    public static List<Atom> mutableReferences(Atom value) {
        if(value instanceof CollectionView view)return List.of(view.source());
        if(value instanceof MapEntryValue entry)return List.of(entry.source(),entry.key());
        if(value instanceof LambdaValue lambda)return lambda.captured();
        if(value instanceof ProxyValue proxy)return List.of(proxy.handler());
        if(value instanceof Reflected method && method.object()>=0)return List.of(new ObjectValue(method.object(),"java/lang/reflect/Method",true,"method metadata",false));
        if(value instanceof ArrayValue array)return array.elements();
        if(value instanceof UnboundValue unbound)return List.of(unbound.original());
        return List.of();
    }
    public static boolean finiteBinding(Atom atom) {
        return atom instanceof Literal || atom instanceof ObjectValue object && object.exact() || atom instanceof ClassValue type && type.exact()
                || atom instanceof Reflected member && member.declaringClass() instanceof ClassValue owner && owner.exact()
                    && member.name() instanceof Literal name && name.value() instanceof String
                    && member.parameterTypes() instanceof ArrayValue signature && signature.extent()==ArrayExtent.EXACT
                    && signature.elements().stream().allMatch(value -> value instanceof ClassValue type && type.exact())
                || atom instanceof ConstructorValue || atom instanceof MethodHandleValue || atom instanceof LambdaValue
                || atom instanceof ProxyValue proxy && proxy.interfacesKnown()
                || atom instanceof ArrayValue array && array.extent()==ArrayExtent.EXACT && array.elements().stream().allMatch(ValueBindings::finiteBinding) || atom instanceof Bytecode;
    }
    public static MethodTypeValue methodType(String descriptor,Program program,int loader) {
        Signature signature=program.signature(new MethodId("<method-type>","type",descriptor));
        ClassValue returned=new ClassValue(signature.returned().descriptor(),true,Optional.empty(),program.scope(Values.type(signature.returned().descriptor()),loader));
        return new MethodTypeValue(returned,signature.parameters().stream().map(type -> new ClassValue(type.descriptor(),true,Optional.empty(),program.scope(Values.type(type.descriptor()),loader))).toList());
    }
    static boolean sameType(MethodTypeValue left,MethodTypeValue right) {
        if(!left.descriptor().equals(right.descriptor()) || left.returned().loader()!=right.returned().loader())return false;
        for(int index=0;index<left.parameters().size();index++)if(left.parameters().get(index).loader()!=right.parameters().get(index).loader())return false;
        return true;
    }
    /** Only modeled content links contribute origins; each alternative keeps its path and evidence. */
    static Query<List<Bound>> sources(Atom atom,Bindings bindings,Path path) {
        Set<Bound> seen=new HashSet<>(),sources=new LinkedHashSet<>();ArrayDeque<Bound> pending=new ArrayDeque<>(List.of(new Bound(atom,path)));
        while(!pending.isEmpty() && seen.size()<16) {
            Bound value=pending.removeFirst();if(!seen.add(value))continue;
            if(Values.source(value.atom()).isPresent())sources.add(value);
            else if(value.atom() instanceof ObjectValue object)for(Bound content:bindings.read(object,new Content()).under(value.path()).requiring(value.gaps()).tracing(value.dependencies()).alternatives())pending.addLast(content);
        }
        List<QueryIssue> gaps=pending.isEmpty()?List.of():List.of(new QueryIssue(QueryCause.BUDGET,"modeled content source frontier (16)"));
        return new Query<>(Optional.of(List.copyOf(sources)),gaps);
    }
    public static Optional<String> runtimeType(Atom atom) {
        if (atom instanceof ObjectValue object) return Optional.of(object.type());
        if (atom instanceof CollectionView view) return Optional.of(view.type());
        if (atom instanceof MapEntryValue) return Optional.of("java/util/Map$Entry");
        if (atom instanceof ClassValue) return Optional.of("java/lang/Class");
        if (atom instanceof Reflected) return Optional.of("java/lang/reflect/Method");
        if (atom instanceof ReflectedField) return Optional.of("java/lang/reflect/Field");
        if (atom instanceof ConstructorValue) return Optional.of("java/lang/reflect/Constructor");
        if(atom instanceof LookupValue)return Optional.of("java/lang/invoke/MethodHandles$Lookup");
        if(atom instanceof MethodTypeValue)return Optional.of("java/lang/invoke/MethodType");
        if(atom instanceof MethodHandleValue)return Optional.of("java/lang/invoke/MethodHandle");
        if (atom instanceof Literal literal && literal.value() instanceof String) return Optional.of("java/lang/String");
        return Optional.empty();
    }

    public enum Match { COMPATIBLE, INCOMPATIBLE, UNKNOWN }
    public record Compatibility(Match match,List<QueryIssue> pending) { public Compatibility {pending=List.copyOf(pending);} }
    private static final Compatibility COMPATIBLE=new Compatibility(Match.COMPATIBLE,List.of());
    private static final Compatibility INCOMPATIBLE=new Compatibility(Match.INCOMPATIBLE,List.of());
    private static final Compatibility UNKNOWN=new Compatibility(Match.UNKNOWN,List.of());
    private static Compatibility reference(String child,String parent,boolean exact,Program program) {
        Query<Boolean> query=program.assignable(child,parent);
        if (query.value().isEmpty())return new Compatibility(Match.UNKNOWN,query.pending());
        return query.value().get()?COMPATIBLE:exact?INCOMPATIBLE:UNKNOWN;
    }
    public static boolean sameSignature(MethodId method,List<Atom> signature,Program program) {
        List<ValueType> expected=program.signature(method).parameters();
        return expected.size()==signature.size() && java.util.stream.IntStream.range(0,expected.size()).allMatch(i -> signature.get(i) instanceof ClassValue type && type.exact() && type.descriptor().equals(expected.get(i).descriptor()) && type.loader()==program.scope(Values.type(type.descriptor()),method.loader()));
    }
    public static Compatibility compatible(Atom atom,String descriptor,Program program,int loader) {
        if(descriptor.length()>1 && atom instanceof ProxyValue proxy)return proxyCompatibility(proxy,Values.type(descriptor),program,loader);
        if(descriptor.length()>1 && atom instanceof LambdaValue lambda)return lambdaCompatibility(lambda,Values.type(descriptor),program,loader);
        if(atom instanceof ObjectValue object && descriptor.length()>1 && (object.loader()!=0 || loader!=0)) {
            Query<Boolean> query=program.assignable(object.type(),object.loader(),Values.type(descriptor),loader);
            return query.value().isEmpty()?new Compatibility(Match.UNKNOWN,query.pending()):query.value().get()?COMPATIBLE:object.exact()?INCOMPATIBLE:UNKNOWN;
        }
        return compatible(atom,descriptor,program);
    }
    public static Compatibility compatible(Atom atom, String descriptor, Program program) {
        if(atom instanceof ObjectValue object && object.loader()!=0 && descriptor.length()>1)return compatible(atom,descriptor,program,0);
        if(atom instanceof UnboundValue value)return compatible(value.original(),descriptor,program);
        if(atom instanceof StringPrefix || atom instanceof StringConcat)return reference("java/lang/String",Values.type(descriptor),true,program);
        if (atom instanceof Unknown || atom instanceof Symbolic || atom instanceof Truncated || atom instanceof ExternalValue) return UNKNOWN;
        if (descriptor.length() == 1) {
            if (!(atom instanceof Literal literal)) return UNKNOWN;
            Object value = literal.value();
            String targets = value instanceof Integer ? "IJFD" : value instanceof Long ? "JFD" : value instanceof Float ? "FD"
                    : value instanceof Double ? "D" : value instanceof Boolean ? "Z" : value instanceof Character ? "CIJFD"
                    : value instanceof Short ? "SIJFD" : value instanceof Byte ? "BSIJFD" : "";
            return targets.contains(descriptor) ? COMPATIBLE : INCOMPATIBLE;
        }
        if (atom instanceof Literal literal) {
            if (literal.value() == null) return COMPATIBLE;
            if (literal.value() instanceof String) return reference("java/lang/String",Values.type(descriptor),true,program);
            return UNKNOWN;
        }
        if (atom instanceof ObjectValue object) return reference(object.type(),Values.type(descriptor),object.exact()
                || program.type(object.type()).filter(c -> (c.access() & org.objectweb.asm.Opcodes.ACC_FINAL)!=0).isPresent(),program);
        if (atom instanceof CollectionView view) return reference(view.type(),Values.type(descriptor),false,program);
        if (atom instanceof MapEntryValue) return reference("java/util/Map$Entry",Values.type(descriptor),false,program);
        if (atom instanceof ProxyValue proxy) return proxyCompatibility(proxy,Values.type(descriptor),program,0);
        if (atom instanceof LambdaValue lambda) return lambdaCompatibility(lambda,Values.type(descriptor),program,0);
        if (atom instanceof ArrayValue array) return reference(array.descriptor(),Values.type(descriptor),true,program);
        if (atom instanceof LoaderValue) return reference("java/lang/ClassLoader",Values.type(descriptor),true,program);
        if (atom instanceof Reflected) return reference("java/lang/reflect/Method",Values.type(descriptor),true,program);
        if (atom instanceof ConstructorValue) return reference("java/lang/reflect/Constructor",Values.type(descriptor),true,program);
        if (atom instanceof ClassValue) return reference("java/lang/Class",Values.type(descriptor),true,program);
        if(atom instanceof LookupValue || atom instanceof MethodTypeValue || atom instanceof MethodHandleValue)return reference(runtimeType(atom).orElseThrow(),Values.type(descriptor),true,program);
        return UNKNOWN;
    }
    private static Compatibility proxyCompatibility(ProxyValue proxy,String type,Program program,int loader) {
        if(Set.of("java/lang/Object","java/lang/reflect/Proxy").contains(type) && program.scope(type,loader)==0)return COMPATIBLE;
        Compatibility known=interfaces(proxy.interfaces(),type,program,loader);return known.match()==Match.INCOMPATIBLE && !proxy.interfacesKnown()?UNKNOWN:known;
    }
    private static Compatibility lambdaCompatibility(LambdaValue lambda,String type,Program program,int loader) {
        List<String> names=new ArrayList<>(lambda.markers());names.add(lambda.owner());
        return interfaces(names.stream().map(name -> new ClassValue("L"+name+";",true,Optional.empty(),program.scope(name,lambda.factory().method().loader()))).toList(),type,program,loader);
    }
    private static Compatibility interfaces(List<ClassValue> types,String parent,Program program,int loader) {
        List<QueryIssue> pending=new ArrayList<>();
        for(ClassValue type:types) {
            Query<Boolean> query=program.assignable(Values.type(type.descriptor()),type.loader(),parent,loader);
            if(query.value().equals(Optional.of(true)))return COMPATIBLE;
            pending.addAll(query.pending());
        }
        return pending.isEmpty()?INCOMPATIBLE:new Compatibility(Match.UNKNOWN,pending);
    }

    public record ArrayBinding(List<Atom> elements, Path path, List<Gap> gaps, Set<Integer> dependencies) {
        public ArrayBinding {elements=List.copyOf(elements);gaps=List.copyOf(gaps);dependencies=Set.copyOf(dependencies);}
    }

    public record ArrayBindings(List<ArrayBinding> values,List<Gap> frontier) {
        public ArrayBindings {values=List.copyOf(values);frontier=List.copyOf(frontier);}
        Local keeping(Local local) {
            if(frontier.isEmpty())return local;
            List<Effect> effects=new ArrayList<>(local.effects());effects.add(new Observe(Kind.DYNAMIC_CALL,"array query frontier",List.of(),frontier));return new Local(effects);
        }
    }
    public static ArrayBindings array(Atom atom, Bindings bindings, Path path, Site site) {
        if (atom instanceof ArrayValue array) return array.extent()==ArrayExtent.EXACT && array.order()==ArrayOrder.INDEXED
                ?new ArrayBindings(List.of(new ArrayBinding(array.elements(),path,array.conditions(),Set.of())),List.of()):new ArrayBindings(List.of(),array.conditions());
        if (atom instanceof Literal value && value.value()==null)
            return new ArrayBindings(List.of(new ArrayBinding(List.of(),path,List.of(),Set.of())),List.of());
        if (!(atom instanceof ObjectValue object) || !object.type().startsWith("[")) return new ArrayBindings(List.of(),List.of());
        Set<ArrayBinding> result=new LinkedHashSet<>();Set<Gap> frontier=new LinkedHashSet<>();int limit=bindings.alternatives(),lengthLimit=Math.max(64,limit);
        Value lengths=bindings.read(object,new Length()).under(path);
        if(lengths.empty())lengths=Values.location(object).flatMap(source -> path.selected(source.at(new Length()))).map(value -> Value.of(value,path)).orElse(Value.BOTTOM);
        for (Bound length : lengths.alternatives()) {
            int remaining=limit-result.size();
            if(remaining==0){frontier.add(new Gap(GapKind.BUDGET,site,"reflective array query frontier ("+limit+" tuples)"));break;}
            if (!(length.atom() instanceof Literal number) || !(number.value() instanceof Integer size) || size<0)continue;
            if(size>lengthLimit){frontier.add(new Gap(GapKind.BUDGET,site,"reflective array length frontier ("+lengthLimit+"): "+size));continue;}
            List<ArrayBinding> tuples=List.of(new ArrayBinding(List.of(),length.path(),length.gaps(),length.dependencies()));
            for (int index=0;index<size;index++) {
                int position=index;
                List<ArrayBinding> next=new ArrayList<>();
                combinations:for (ArrayBinding tuple:tuples) {
                    Value contents=bindings.read(object,new Index(index)).under(tuple.path());
                    if(contents.empty())contents=Values.location(object).flatMap(source -> tuple.path().selected(source.at(new Index(position)))).map(value -> Value.of(value,tuple.path())).orElse(Value.BOTTOM);
                    if(contents.empty() && object.defaultFields())contents=Value.NULL.under(tuple.path());
                    if(contents.empty() && object.source().isPresent()) {
                        InputSource source=object.source().get().at(new Index(index));String descriptor=object.type().substring(1);
                        Atom member=descriptor.startsWith("L") || descriptor.startsWith("[")?new Symbolic(Values.type(descriptor),"conditional array member",Optional.of(source),object.loader()):new ExternalValue(descriptor,source);
                        contents=Value.of(member,tuple.path()).requiring(List.of(new Gap(GapKind.INPUT_BINDING,site,"array member remains conditional input at slot "+index)));
                    }
                    for (Bound value:contents.alternatives()) {
                    if(next.size()>=remaining){frontier.add(new Gap(GapKind.BUDGET,site,"reflective array binding frontier ("+limit+" total tuples)"));break combinations;}
                    List<Atom> elements=new ArrayList<>(tuple.elements()); elements.add(value.atom());
                    Set<Gap> gaps=new LinkedHashSet<>(tuple.gaps()); gaps.addAll(value.gaps());
                    Set<Integer> dependencies=new LinkedHashSet<>(tuple.dependencies()); dependencies.addAll(value.dependencies());
                    next.add(new ArrayBinding(List.copyOf(elements),value.path(),List.copyOf(gaps),Set.copyOf(dependencies)));
                    }
                }
                tuples=next;
            }
            result.addAll(tuples);
        }
        return new ArrayBindings(List.copyOf(result),List.copyOf(frontier));
    }
    static List<ArrayBinding> adapt(Invocation call,ArrayBinding args,List<Atom> signature,Bindings bindings,List<Effect> frontiers) {
        if(args.elements().size()!=signature.size() || !signature.stream().allMatch(value -> value instanceof ClassValue type && type.exact()))return List.of(args);
        List<ArrayBinding> tuples=List.of(new ArrayBinding(List.of(),args.path(),args.gaps(),args.dependencies()));
        for(int i=0;i<signature.size();i++) {
            Atom argument=args.elements().get(i);Value value=Value.of(argument);
            String parameter=((ClassValue)signature.get(i)).descriptor();
            if(parameter.length()==1 && (argument instanceof Literal nil && nil.value()==null
                    || argument instanceof ObjectValue object && Library.primitive(object.type()).filter(source -> !canUnbox(source,parameter)).isPresent())) {
                frontiers.add(new Conditional(args.path(),args.gaps(),args.dependencies(),Local.of(new Raise("java/lang/IllegalArgumentException"))));return List.of();
            }
            if(parameter.length()==1 && argument instanceof ObjectValue object && Library.primitive(object.type()).filter(p -> canUnbox(p,parameter)).isPresent()) {
                value=bindings.read(object,new Content());
                if(value.empty())value=Value.of(new Unknown("boxed argument has no finite content")).requiring(Mechanisms.unknown(call,"boxed argument content is unspecified"));
                Value converted=Value.BOTTOM;
                for(Bound bound:value.alternatives()) {
                    Atom atom=bound.atom();
                    if(atom instanceof Literal l && l.value() instanceof Number n)atom=switch(parameter){case "J" -> new Literal(n.longValue());case "F" -> new Literal(n.floatValue());case "D" -> new Literal(n.doubleValue());default -> atom;};
                    converted=converted.merge(Value.of(atom,bound.path()).requiring(bound.gaps()).tracing(bound.dependencies()));
                }
                value=converted;
            }
            List<ArrayBinding> next=new ArrayList<>();
            combinations:for(ArrayBinding tuple:tuples)for(Bound bound:value.under(tuple.path()).alternatives()) {
                if(next.size()>=bindings.alternatives()){frontiers.add(new Observe(Kind.REFLECTION,"primitive argument adaptation frontier",List.of(call.call().site()),List.of(Mechanisms.gap(call,GapKind.BUDGET,"primitive argument adaptation combinations ("+bindings.alternatives()+")"))));break combinations;}
                List<Atom> elements=new ArrayList<>(tuple.elements());elements.add(bound.atom());
                List<Gap> gaps=new ArrayList<>(tuple.gaps());gaps.addAll(bound.gaps());Set<Integer> dependencies=new LinkedHashSet<>(tuple.dependencies());dependencies.addAll(bound.dependencies());
                next.add(new ArrayBinding(List.copyOf(elements),bound.path(),List.copyOf(gaps),Set.copyOf(dependencies)));
            }
            tuples=next;
        }
        return tuples;
    }
    static boolean canUnbox(String source,String target) {
        return (switch(source){case "Z" -> "Z";case "B" -> "BSIJFD";case "C" -> "CIJFD";case "S" -> "SIJFD";case "I" -> "IJFD";case "J" -> "JFD";case "F" -> "FD";case "D" -> "D";default -> "";}).contains(target);
    }
}
