package io.just.knowledge;

import io.just.program.Program.*;
import java.util.*;

/** Immutable bindings exchanged with local models. Heap and scheduling remain in analysis. */
public final class Values {
    private Values() {}
    public sealed interface Atom permits Literal, ObjectValue, ClassValue, RuntimeTypes, Reflected, ReflectedField, ConstructorValue, LambdaValue, ProxyValue, ArrayValue, CollectionView, MapEntryValue, LoaderValue, HttpServerValue, Unknown, Symbolic, Truncated, LookupValue, MethodTypeValue, MethodHandleValue, ExternalValue, NormalValue, UnboundValue, StringPrefix, StringConcat, InstanceTest, Bytecode {}
    /** A JVM instanceof result retains the tested value until a branch can refine it. */
    public record InstanceTest(Atom receiver,String type,int loader) implements Atom {}
    public record ReflectedField(FieldId field,int access) implements Atom {}
    /** Borrows read-only class bytes from the scan. Reports retain their source and length. */
    public static final class Bytecode implements Atom {
        private final String name,source;private final int length;private final transient byte[] bytes;
        public Bytecode(String name,String source,byte[] bytes){this.name=name;this.source=source;this.bytes=bytes;length=bytes.length;}
        public String name(){return name;}public String source(){return source;}public byte[] bytes(){return bytes;}
        @Override public String toString(){return "class bytes "+name+" ("+length+") from "+source;}
    }
    public record UnboundValue(int id,int operand,String descriptor,Atom original) implements Atom {}
    public record StringPrefix(String prefix,Atom suffix) implements Atom {}
    public record StringConcat(List<Atom> pieces) implements Atom {public StringConcat {pieces=List.copyOf(pieces);}}
    public enum NormalValue implements Atom { CERTAIN, CONDITIONAL }
    public record CollectionView(int id,String type,ObjectValue source,Slot elements) implements Atom {}
    public record MapEntryValue(ObjectValue source,Atom key) implements Atom {}
    public record Literal(Object value) implements Atom {}
    public sealed interface InputLocation permits InputSource,ObjectSource,ValueSource {InputLocation at(Slot slot);List<Slot> path();}
    public record ValueSource(int value,int operand,Atom producer,List<Slot> path) implements InputLocation {
        public ValueSource {path=List.copyOf(path);}
        public ValueSource at(Slot slot){List<Slot> next=new ArrayList<>(path);next.add(slot);return new ValueSource(value,operand,producer,next);}
    }
    public record ObjectSource(int object,List<Slot> path) implements InputLocation {
        public ObjectSource {path=List.copyOf(path);}
        public ObjectSource at(Slot slot){List<Slot> next=new ArrayList<>(path);next.add(slot);return new ObjectSource(object,next);}
    }
    public static final class InputSource implements InputLocation {
        private final MethodId entry;private final int parameterSlot;private final List<Slot> path;private final transient int hash;
        public InputSource(MethodId entry,int parameterSlot,List<Slot> path){this.entry=entry;this.parameterSlot=parameterSlot;this.path=List.copyOf(path);hash=31*(31*entry.hashCode()+parameterSlot)+this.path.hashCode();}
        public MethodId entry(){return entry;}public int parameterSlot(){return parameterSlot;}public List<Slot> path(){return path;}
        public InputSource at(Slot slot){List<Slot> next=new ArrayList<>(path);next.add(slot);return new InputSource(entry,parameterSlot,next);}
        @Override public int hashCode(){return hash;}
        @Override public boolean equals(Object other){return this==other || other instanceof InputSource source && hash==source.hash && parameterSlot==source.parameterSlot && entry.equals(source.entry) && path.equals(source.path);}
        @Override public String toString(){return "InputSource[entry="+entry+", parameterSlot="+parameterSlot+", path="+path+"]";}
    }
    public record ExternalValue(String descriptor,InputSource source) implements Atom {}
    public record ObjectValue(int id, String type, boolean exact, String origin, boolean defaultFields,Optional<InputSource> source,int loader) implements Atom {
        public ObjectValue(int id,String type,boolean exact,String origin,boolean defaultFields,Optional<InputSource> source){this(id,type,exact,origin,defaultFields,source,0);}
        public ObjectValue(int id,String type,boolean exact,String origin,boolean defaultFields){this(id,type,exact,origin,defaultFields,Optional.empty());}
        public ObjectValue(int id,String type,boolean exact,String origin) { this(id,type,exact,origin,exact); }
        @Override public String toString() { return "object#"+id+":"+type+(exact?" (exact)":" (possible)"); }
    }
    public record ClassValue(String descriptor, boolean exact,Optional<InputLocation> source,int loader) implements Atom {
        public ClassValue(String descriptor,boolean exact,Optional<? extends InputLocation> source){this(descriptor,exact,source.map(s -> (InputLocation)s),0);}
        public ClassValue(String descriptor,boolean exact){this(descriptor,exact,Optional.empty());}
    }
    /** A finite disjunction of exact runtime classes for one object identity. */
    public record RuntimeTypes(List<ClassValue> members) implements Atom {
        public RuntimeTypes {members=List.copyOf(new LinkedHashSet<>(members));if(members.isEmpty() || members.stream().anyMatch(type -> !type.exact()))throw new IllegalArgumentException("runtime type set requires exact classes");}
    }
    public record Reflected(Atom declaringClass, Atom name, Atom parameterTypes, boolean declared, Site lookup,int object,int member) implements Atom {
        public Reflected(Atom declaringClass,Atom name,Atom parameterTypes,boolean declared,Site lookup){this(declaringClass,name,parameterTypes,declared,lookup,-1,0);}
    }
    public record ConstructorValue(int id,Atom declaringClass,ArrayValue parameterTypes,boolean declared,Site lookup) implements Atom {}
    public record LookupValue(String caller,boolean publicOnly,Site source) implements Atom {}
    public record MethodTypeValue(ClassValue returned,List<ClassValue> parameters) implements Atom {
        public MethodTypeValue {parameters=List.copyOf(parameters);}
        public String descriptor(){return "("+String.join("",parameters.stream().map(ClassValue::descriptor).toList())+")"+returned.descriptor();}
    }
    public record MethodHandleValue(MethodId target,MethodTypeValue invocationType,boolean virtual,LookupValue lookup,Site source) implements Atom {}
    public record LambdaValue(int id,String owner,String name,String descriptor,HandleConstant implementation,List<Atom> captured,List<String> bridges,List<String> markers,Site factory) implements Atom {
        public LambdaValue { captured=List.copyOf(captured);bridges=List.copyOf(bridges);markers=List.copyOf(markers); }
        @Override public String toString(){return "lambda#"+id+":"+owner+"."+name+descriptor;}
    }
    public record ProxyValue(int id,List<ClassValue> interfaces,Atom handler,Site factory,boolean interfacesKnown) implements Atom { public ProxyValue(int id,List<ClassValue> interfaces,Atom handler,Site factory){this(id,interfaces,handler,factory,true);} public ProxyValue { interfaces=List.copyOf(interfaces); } @Override public String toString(){return "proxy#"+id+":"+interfaces;} }
    public enum ArrayRole { METHOD_TYPES, PROXY_ARGUMENTS, METHOD_COLLECTION }
    public enum ArrayOrder { INDEXED, UNSPECIFIED }
    public enum ArrayExtent { EXACT, UNKNOWN }
    public record ArrayValue(int id,ArrayRole role,String descriptor,List<Atom> elements,ArrayOrder order,ArrayExtent extent,List<Gap> conditions) implements Atom {
        public ArrayValue(int id,ArrayRole role,String descriptor,List<Atom> elements){this(id,role,descriptor,elements,ArrayOrder.INDEXED,ArrayExtent.EXACT,List.of());}
        public ArrayValue {elements=List.copyOf(elements);conditions=List.copyOf(conditions);} @Override public String toString(){return "array#"+id+":"+role+" size="+elements.size();} }
    public record LoaderValue(String definingClass,int object) implements Atom {public LoaderValue(String definingClass){this(definingClass,0);}}
    public record HttpServerValue(int id,Site factory) implements Atom {}
    public record Unknown(String reason) implements Atom {}
    public record Symbolic(String type, String requirement,Optional<InputSource> source,int loader) implements Atom {
        public Symbolic(String type,String requirement,Optional<InputSource> source){this(type,requirement,source,0);}
        public Symbolic(String type,String requirement){this(type,requirement,Optional.empty());}
    }
    public record Truncated(String reason) implements Atom {}
    public enum NeedKind { VALUE, CLASS_NAME, METHOD_NAME, METHOD_TYPES, ARGUMENTS, RECEIVER_TYPE, RECEIVER_PRODUCER, SERIALIZED_MEMBERS, LOOKUP_TYPE }
    public record InputNeed(Atom subject,Optional<Slot> slot,NeedKind kind,String descriptor,List<Atom> choices,String reason) {
        public InputNeed {choices=List.copyOf(choices);}
    }
    public static Optional<InputSource> source(Atom atom){return atom instanceof ObjectValue object?object.source():atom instanceof ClassValue type?type.source().filter(InputSource.class::isInstance).map(InputSource.class::cast):atom instanceof ExternalValue value?Optional.of(value.source()):atom instanceof Symbolic symbolic?symbolic.source():Optional.empty();}
    public static Optional<InputLocation> location(Atom atom){return atom instanceof ClassValue type?type.source():source(atom).map(s -> (InputLocation)s).or(() -> atom instanceof ObjectValue object?Optional.of(new ObjectSource(object.id(),List.of())):atom instanceof UnboundValue value?Optional.of(new ValueSource(value.id(),value.operand(),value.original(),List.of())):Optional.empty());}
    public static InputLocation parent(InputLocation location) {
        List<Slot> path=location.path().subList(0,location.path().size()-1);
        if(location instanceof InputSource input)return new InputSource(input.entry(),input.parameterSlot(),path);
        if(location instanceof ObjectSource object)return new ObjectSource(object.object(),path);
        ValueSource value=(ValueSource)location;return new ValueSource(value.value(),value.operand(),value.producer(),path);
    }
    public sealed interface ChoiceKey permits BranchKey, ObjectChoice, ElementChoice, TargetChoice, NormalChoice { int context(); int instruction(); int iteration(); }
    public record NormalChoice(int context,int instruction,int iteration,List<Integer> effects,MethodId target,Atom receiver,List<Atom> arguments) implements ChoiceKey {
        public NormalChoice {effects=List.copyOf(effects);arguments=List.copyOf(arguments);}
    }
    public record BranchKey(int context, int instruction, int iteration) implements ChoiceKey { public BranchKey(int context,int instruction) { this(context,instruction,-1); } }
    public record ObjectChoice(int context,int instruction,int iteration) implements ChoiceKey {}
    public record ElementChoice(int context,int instruction,int iteration) implements ChoiceKey {}
    public record TargetChoice(int context,int instruction,int iteration,List<Integer> effects) implements ChoiceKey {
        public TargetChoice {effects=List.copyOf(effects);}
        public TargetChoice(int context,int instruction,int iteration){this(context,instruction,iteration,List.of());}
    }
    public record IntegralRange(long minimum,long maximum) {
        public IntegralRange {if(minimum>maximum)throw new IllegalArgumentException("empty integral range");}
        public Optional<IntegralRange> and(IntegralRange other) {
            long low=Math.max(minimum,other.minimum),high=Math.min(maximum,other.maximum);
            return low>high?Optional.empty():Optional.of(low==minimum && high==maximum?this:low==other.minimum && high==other.maximum?other:new IntegralRange(low,high));
        }
        public static OptionalLong literal(Atom atom) {
            if(!(atom instanceof Literal literal))return OptionalLong.empty();
            Object value=literal.value();
            if(value instanceof Byte || value instanceof Short || value instanceof Integer || value instanceof Long)return OptionalLong.of(((Number)value).longValue());
            if(value instanceof Character character)return OptionalLong.of(character);
            if(value instanceof Boolean flag)return OptionalLong.of(flag?1:0);
            return OptionalLong.empty();
        }
    }
    /** Finite value, type and integral constraints share one source selection. */
    public record Selection(Atom value,Set<String> types,Optional<IntegralRange> range) {
        public Selection(Atom value,Set<String> types){this(value,types,Optional.empty());}
        public Selection {types=Collections.unmodifiableSet(new LinkedHashSet<>(types));}
        static Selection of(Atom value,String descriptor) {
            Set<String> types=new LinkedHashSet<>();if(!descriptor.isEmpty())types.add(descriptor);
            if(value instanceof Symbolic symbolic)types.add(symbolic.type().startsWith("[") || symbolic.type().length()==1 && "ZBCSIJFD".contains(symbolic.type())?symbolic.type():"L"+symbolic.type()+";");
            if(value instanceof ExternalValue external)types.add(external.descriptor());
            return new Selection(value,types);
        }
        public boolean impliedBy(Selection actual) {
            if(equals(actual))return true;
            if(!actual.types.containsAll(types))return false;
            if(range.isPresent()) {
                IntegralRange needed=range.get(),selected=actual.range.orElse(null);
                if(selected==null || needed.minimum()>selected.minimum() || needed.maximum()<selected.maximum())return false;
            }
            return actual.value.equals(actual.commonValue(this));
        }
        private boolean compatible(Selection other) {return equals(other) || commonValue(other)!=null;}
        Optional<Selection> and(Selection other) {
            return Optional.ofNullable(merge(other));
        }
        private Selection merge(Selection other) {
            if(equals(other))return this;
            Atom chosen=commonValue(other);
            if(chosen==null)return null;
            Optional<IntegralRange> narrowed=range.isEmpty()?other.range:other.range.isEmpty()?range:range.get().and(other.range.get());
            if(chosen.equals(value) && types.containsAll(other.types) && narrowed.equals(range))return this;
            if(chosen.equals(other.value) && other.types.containsAll(types) && narrowed.equals(other.range))return other;
            Set<String> combined=new LinkedHashSet<>(types);combined.addAll(other.types);
            return new Selection(chosen,combined,narrowed);
        }
        private Atom commonValue(Selection other) {
            Atom chosen;
            boolean left=value instanceof Symbolic || value instanceof ExternalValue || value instanceof UnboundValue,right=other.value instanceof Symbolic || other.value instanceof ExternalValue || other.value instanceof UnboundValue;
            if(value instanceof RuntimeTypes first && other.value instanceof RuntimeTypes second) {
                Set<ClassValue> allowed=new HashSet<>(second.members());List<ClassValue> common=first.members().stream().filter(allowed::contains).toList();
                if(common.isEmpty())return null;chosen=common.size()==1?common.get(0):common.equals(first.members())?first:new RuntimeTypes(common);
            } else if(value instanceof RuntimeTypes types && other.value instanceof ClassValue type) {
                if(!types.members().contains(type))return null;chosen=type;
            } else if(value instanceof ClassValue type && other.value instanceof RuntimeTypes types) {
                if(!types.members().contains(type))return null;chosen=type;
            } else {
                chosen=value;
                if(!left && !right && !value.equals(other.value))return null;
                if(left && !right)chosen=other.value;
                if(value instanceof Symbolic first && first.type().equals("java/lang/Object") && other.value instanceof Symbolic)chosen=other.value;
            }
            if(range.isEmpty() && other.range.isEmpty())return chosen;
            long low=Math.max(range.isPresent()?range.get().minimum():Long.MIN_VALUE,other.range.isPresent()?other.range.get().minimum():Long.MIN_VALUE);
            long high=Math.min(range.isPresent()?range.get().maximum():Long.MAX_VALUE,other.range.isPresent()?other.range.get().maximum():Long.MAX_VALUE);
            if(low>high)return null;
            OptionalLong literal=IntegralRange.literal(chosen);
            return literal.isPresent() && (literal.getAsLong()<low || literal.getAsLong()>high)?null:chosen;
        }
    }
    public static final class Path {
        private final Map<ChoiceKey,Integer> choices;
        private final Map<InputLocation,Selection> selections;
        private final transient int hash;
        public static final Path EMPTY = new Path(Map.of());
        public Path(Map<ChoiceKey,Integer> choices) { this(new LinkedHashMap<>(choices),Map.of()); }
        private Path(Map<ChoiceKey,Integer> owned,Map<InputLocation,Selection> selections) { choices=Collections.unmodifiableMap(owned);this.selections=Collections.unmodifiableMap(selections);hash=31*owned.hashCode()+selections.hashCode(); }
        public Map<ChoiceKey,Integer> choices(){return choices;}
        public Map<InputLocation,Selection> selections(){return selections;}
        public Optional<Atom> selected(InputLocation location){return Optional.ofNullable(selections.get(location)).map(Selection::value);}
        public Path retainingChoices(Map<ChoiceKey,Integer> retained){return new Path(new LinkedHashMap<>(retained),selections);}
        @Override public int hashCode(){return hash;}
        @Override public boolean equals(Object other){return this==other || other instanceof Path path && hash==path.hash && choices.equals(path.choices) && selections.equals(path.selections);}
        @Override public String toString(){return "Path[choices="+choices+", selections="+selections+"]";}
        public Optional<Path> selecting(InputLocation source,Atom value) {
            return selecting(source,value,"");
        }
        public Optional<Path> selecting(InputLocation source,Atom value,String descriptor) {
            return selecting(source,Selection.of(value,descriptor));
        }
        public Optional<Path> restricting(InputLocation source,Atom value,String descriptor,IntegralRange range) {
            Selection selection=Selection.of(value,descriptor);
            return selecting(source,new Selection(selection.value(),selection.types(),Optional.of(range)));
        }
        private Optional<Path> selecting(InputLocation source,Selection selection) {
            Selection previous=selections.get(source);
            if(previous!=null) {
                Optional<Selection> merged=previous.and(selection);if(merged.isEmpty())return Optional.empty();
                if(merged.get().equals(previous))return Optional.of(this);selection=merged.get();
            }
            Map<InputLocation,Selection> next=new LinkedHashMap<>(selections);next.put(source,selection);
            return Optional.of(new Path(choices,next));
        }
        public Optional<Path> with(ChoiceKey branch, int successor) {
            Integer old = choices.get(branch);
            if (old != null) return old == successor ? Optional.of(this) : Optional.empty();
            LinkedHashMap<ChoiceKey, Integer> next = new LinkedHashMap<>(choices);
            next.put(branch, successor);
            return Optional.of(new Path(next,selections));
        }
        /** Same compatibility as and(), without allocating a merged path for a boolean question. */
        public boolean compatible(Path other) {
            if(this==other)return true;
            if(!compatibleChoices(other))return false;
            Path smaller=selections.size()<=other.selections.size()?this:other,larger=smaller==this?other:this;
            for(var selection:smaller.selections.entrySet()) {
                Selection selected=larger.selections.get(selection.getKey());
                if(selected!=null && !selected.compatible(selection.getValue()))return false;
            }
            return true;
        }
        private boolean compatibleChoices(Path other) {
            Path smaller=choices.size()<=other.choices.size()?this:other,larger=smaller==this?other:this;
            for(var choice:smaller.choices.entrySet()) {
                Integer selected=larger.choices.get(choice.getKey());
                if(selected!=null && !selected.equals(choice.getValue()))return false;
            }
            return true;
        }
        public Optional<Path> and(Path other) {
            if(this==other || contains(other))return Optional.of(this);
            if(other.contains(this))return Optional.of(other);
            if(!selections.equals(other.selections)) {
                if(!compatibleChoices(other))return Optional.empty();
                Map<InputLocation,Selection> combined=new LinkedHashMap<>(selections);
                for(var selection:other.selections.entrySet()) {
                    Selection old=combined.putIfAbsent(selection.getKey(),selection.getValue());
                    if(old!=null) {
                        Optional<Selection> value=old.and(selection.getValue());if(value.isEmpty())return Optional.empty();
                        combined.put(selection.getKey(),value.get());
                    }
                }
                Map<ChoiceKey,Integer> merged=new LinkedHashMap<>(choices);
                merged.putAll(other.choices);
                return Optional.of(new Path(merged,combined));
            }
            if(this==other || other.choices.isEmpty())return Optional.of(this);
            if(choices.isEmpty())return Optional.of(other);
            Path smaller=choices.size()<=other.choices.size()?this:other,larger=smaller==this?other:this;
            boolean subset=true;
            for (var choice : smaller.choices.entrySet()) {
                Integer old=larger.choices.get(choice.getKey());
                if(old==null)subset=false;
                else if(!old.equals(choice.getValue()))return Optional.empty();
            }
            if(subset) {
                if(larger==this || choices.size()==other.choices.size())return Optional.of(this);
                return Optional.of(other);
            }
            LinkedHashMap<ChoiceKey,Integer> merged=new LinkedHashMap<>(choices);merged.putAll(other.choices);
            return Optional.of(new Path(merged,selections));
        }
        private boolean contains(Path other) {
            if(choices.size()<other.choices.size() || selections.size()<other.selections.size())return false;
            for(var choice:other.choices.entrySet())if(!Objects.equals(choices.get(choice.getKey()),choice.getValue()))return false;
            for(var item:other.selections.entrySet()) {
                Selection own=selections.get(item.getKey());
                if(own==null || !item.getValue().impliedBy(own))return false;
            }
            return true;
        }
    }
    public static final class Bound {
        private final Atom atom;private final Path path;private final List<Gap> gaps;private final Set<Integer> dependencies;private final transient int hash;
        public Bound(Atom atom,Path path,List<Gap> gaps,Set<Integer> dependencies) {
            this.atom=atom;this.path=path;this.gaps=List.copyOf(gaps);this.dependencies=Set.copyOf(dependencies);
            hash=Objects.hash(atom,path,this.gaps,this.dependencies);
        }
        public Bound(Atom atom, Path path, List<Gap> gaps) { this(atom, path, gaps, Set.of()); }
        public Bound(Atom atom, Path path) { this(atom, path, List.of()); }
        public Atom atom(){return atom;}public Path path(){return path;}public List<Gap> gaps(){return gaps;}public Set<Integer> dependencies(){return dependencies;}
        @Override public int hashCode(){return hash;}
        @Override public boolean equals(Object other){return this==other || other instanceof Bound bound && hash==bound.hash && atom.equals(bound.atom) && path.equals(bound.path) && gaps.equals(bound.gaps) && dependencies.equals(bound.dependencies);}
        @Override public String toString(){return "Bound[atom="+atom+", path="+path+", gaps="+gaps+", dependencies="+dependencies+"]";}
    }
    public record Value(Set<Bound> alternatives) {
        public static final Value BOTTOM = new Value(Set.of());
        public static final Value NULL = of(new Literal(null));
        public Value {
            if (alternatives.isEmpty()) alternatives=Set.of();
            else if (alternatives.size()==1) alternatives=Set.of(alternatives.iterator().next());
            else alternatives=Collections.unmodifiableSet(new LinkedHashSet<>(alternatives));
        }
        public static Value of(Atom atom) { return new Value(Set.of(new Bound(atom, Path.EMPTY))); }
        public static Value of(Atom atom, Path path) { return new Value(Set.of(new Bound(atom, path))); }
        public boolean empty() { return alternatives.isEmpty(); }
        public Value merge(Value other) {
            if (other.empty() || equals(other)) return this;
            if (empty()) return other;
            Set<Bound> all = new LinkedHashSet<>(alternatives);
            if(!all.addAll(other.alternatives))return this;
            return new Value(all);
        }
        /** Retain known alternatives and one explicit frontier; truncation is not an absorbing value. */
        public Value limited(int limit,Gap reason) {
            if(alternatives.size()<=limit)return this;
            Set<Bound> kept=new LinkedHashSet<>();
            Map<Class<?>,Map<Atom,ArrayDeque<Bound>>> groups=new LinkedHashMap<>();
            for(Bound bound:alternatives)if(!(bound.atom() instanceof Truncated))groups.computeIfAbsent(bound.atom().getClass(),k -> new LinkedHashMap<>()).computeIfAbsent(bound.atom(),k -> new ArrayDeque<>()).addLast(bound);
            ArrayDeque<ArrayDeque<ArrayDeque<Bound>>> pending=new ArrayDeque<>();
            for(var family:groups.values())pending.addLast(new ArrayDeque<>(family.values()));
            while(!pending.isEmpty() && kept.size()<limit-1) {
                var family=pending.removeFirst();var group=family.removeFirst();kept.add(group.removeFirst());
                if(!group.isEmpty())family.addLast(group);if(!family.isEmpty())pending.addLast(family);
            }
            kept.add(new Bound(new Truncated(reason.detail()),Path.EMPTY,List.of(reason)));return new Value(kept);
        }
        public Value under(Path path) {
            if (path.choices().isEmpty() && path.selections().isEmpty()) return this;
            Set<Bound> result = new LinkedHashSet<>();
            boolean changed=false;
            for (Bound bound : alternatives) {
                Optional<Path> merged=bound.path().and(path);
                if (merged.isEmpty()) {changed=true;continue;}
                if (merged.get()==bound.path()) result.add(bound);
                else {changed=true;result.add(new Bound(bound.atom(),merged.get(),bound.gaps(),bound.dependencies()));}
            }
            if (!changed) return this;
            return new Value(result);
        }
        public Value requiring(List<Gap> gaps) {
            if (gaps.isEmpty()) return this;
            Set<Bound> result=null;
            for (Bound bound : alternatives) {
                if(bound.gaps().equals(gaps) || bound.gaps().containsAll(gaps)) {
                    if(result!=null)result.add(bound);
                    continue;
                }
                if(result==null) {
                    result=new LinkedHashSet<>();
                    for(Bound previous:alternatives) {
                        if(previous==bound)break;
                        result.add(previous);
                    }
                }
                Set<Gap> all=new LinkedHashSet<>(bound.gaps());
                all.addAll(gaps);
                result.add(new Bound(bound.atom(),bound.path(),List.copyOf(all),bound.dependencies()));
            }
            return result==null?this:new Value(result);
        }
        public Value tracing(Collection<Integer> dependencies) {
            if (dependencies.isEmpty()) return this;
            if (alternatives.stream().allMatch(b -> b.dependencies().containsAll(dependencies))) return this;
            Set<Bound> result = new LinkedHashSet<>();
            for (Bound bound : alternatives) {
                Set<Integer> all = new LinkedHashSet<>(bound.dependencies()); all.addAll(dependencies);
                result.add(new Bound(bound.atom(), bound.path(), bound.gaps(), all));
            }
            return new Value(result);
        }
    }
    public sealed interface Slot permits Field, SerializedField, FieldPresence, ClassData, SerializedIndex, SerializedKey, SerializedValue, Index, Wildcard, Elements, MapEntries, MapValues, MapKey, KeyIndex, KeyComparison, Mutation, Length, Content, DecoderKind, FieldTarget, MethodAccess, Decoded, RuntimeClass, NamedClass, Cursor, StreamCursor, StreamRead, HookReceiver, HookOwner, FieldsRead, ActiveObject, ResolvedObject, IterationOrder, DefinedClass, FactoryName {}
    public record Mutation() implements Slot {}
    public record KeyComparison(Atom incoming,Atom existing) implements Slot {}
    public record DefinedClass(int index) implements Slot {}
    public record RuntimeClass() implements Slot {}
    public record NamedClass() implements Slot {}
    public record IterationOrder() implements Slot {}
    public record Field(FieldId field) implements Slot {}
    public record SerializedField(FieldId field) implements Slot {}
    public record FieldPresence(FieldId field) implements Slot {}
    public record ClassData(String owner,int loader) implements Slot {}
    public record SerializedIndex(int index) implements Slot {}
    public record SerializedKey(int index) implements Slot {}
    public record SerializedValue(int index) implements Slot {}
    public record Index(int index) implements Slot {}
    public record Wildcard() implements Slot {}
    public record Elements() implements Slot {}
    public record MapValues() implements Slot {}
    public record MapEntries() implements Slot {}
    public record MapKey(Atom key) implements Slot {}
    public record KeyIndex(Atom key) implements Slot {}
    public record Length() implements Slot {}
    public record Content() implements Slot {}
    public record DecoderKind() implements Slot {}
    public record FieldTarget() implements Slot {}
    public record MethodAccess(int member) implements Slot {}
    /** Actual overridden Reference getter result at one NamingManager invocation. */
    public record FactoryName() implements Slot {}
    public record Decoded() implements Slot {}
    public record Cursor() implements Slot {}
    public record StreamCursor() implements Slot {}
    /** Static read occurrence, not a claimed byte offset in an unknown wire layout. */
    public record StreamRead(int id,Site site,String descriptor) implements Slot {}
    public record HookReceiver() implements Slot {}
    public record HookOwner() implements Slot {}
    public record FieldsRead(int object,String owner,int loader) implements Slot {}
    public record ActiveObject(int object) implements Slot {}
    public record ResolvedObject(int object) implements Slot {}
    public enum GapKind { INPUT_BINDING, DYNAMIC_TARGET, MISSING_DEPENDENCY, UNSUPPORTED, CONTROL_CONDITION, BUDGET, DEPLOYMENT }
    /** Evidence is immutable and shared by many values; hashing must not walk its source repeatedly. */
    public static final class Gap {
        private final GapKind kind;
        private final Site site;
        private final String detail;
        private final Optional<ChoiceKey> condition;
        private final transient int hash;
        public Gap(GapKind kind,Site site,String detail) {
            this(kind,site,detail,Optional.empty());
        }
        public Gap(GapKind kind,Site site,String detail,Optional<ChoiceKey> condition) {
            this.kind=Objects.requireNonNull(kind);this.site=Objects.requireNonNull(site);this.detail=Objects.requireNonNull(detail);
            this.condition=condition;hash=31*(31*(31*kind.hashCode()+site.hashCode())+detail.hashCode())+condition.hashCode();
        }
        public GapKind kind(){return kind;}
        public Site site(){return site;}
        public String detail(){return detail;}
        public Optional<ChoiceKey> condition(){return condition;}
        @Override public int hashCode(){return hash;}
        @Override public boolean equals(Object other){return this==other || other instanceof Gap gap && hash==gap.hash && kind==gap.kind && site.equals(gap.site) && detail.equals(gap.detail) && condition.equals(gap.condition);}
        @Override public String toString(){return "Gap[kind="+kind+", site="+site+", detail="+detail+"]";}
    }
    public enum Evidence { PROVEN, CONDITIONAL, UNKNOWN }
    public enum Kind { DIRECT_CALL, VIRTUAL_CALL, DESERIALIZATION, CONTAINER_CALLBACK, REFLECTION,
        FIELD_FLOW, ELEMENT_FLOW, VALUE_FLOW, CONTROL_FLOW, INPUT_BINDING, DYNAMIC_CALL, METHOD_HANDLE, HTTP_CALLBACK, IMPACT }

    public static String type(String descriptor) {
        if (descriptor.startsWith("L") && descriptor.endsWith(";")) return descriptor.substring(1, descriptor.length() - 1);
        return descriptor;
    }
}
