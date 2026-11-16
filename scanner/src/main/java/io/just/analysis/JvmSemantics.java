package io.just.analysis;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.ValueBindings;
import org.objectweb.asm.Opcodes;
import java.util.*;

/** JVM operations and their normal/exception conditions. Operands are values, never solver units. */
final class JvmSemantics {
    sealed interface Conversion permits Converted,Rejected {}
    record Converted(Value value) implements Conversion {}
    record Possible(String type,String detail) {}
    sealed interface Check permits Normal,Rejected {List<Possible> possible();}
    record Normal(List<Gap> gaps,List<Possible> possible) implements Check {}
    record Rejected(String exception,List<Possible> possible) implements Conversion,Check {
        Rejected(String exception){this(exception,List.of());}
    }
    private final Program program;
    JvmSemantics(Program program) {this.program=program;}
    /** Upper bounds for synchronous exceptions; unknown calls and explicit throws remain unrestricted. */
    static Optional<List<String>> exceptionFamilies(Action action) {
        List<String> runtime;
        if(action instanceof ReadField || action instanceof WriteField)runtime=List.of("java/lang/NullPointerException");
        else if(action instanceof ReadArray)runtime=List.of("java/lang/NullPointerException","java/lang/IndexOutOfBoundsException");
        else if(action instanceof WriteArray)runtime=List.of("java/lang/NullPointerException","java/lang/IndexOutOfBoundsException","java/lang/ArrayStoreException");
        else if(action instanceof NewArray)runtime=List.of("java/lang/NegativeArraySizeException");
        else if(action instanceof Cast)runtime=List.of("java/lang/ClassCastException");
        else if(action instanceof Compute compute && compute.opcode()==Opcodes.ARRAYLENGTH)return Optional.of(List.of("java/lang/NullPointerException"));
        else if(action instanceof Compute compute && Set.of(Opcodes.IDIV,Opcodes.LDIV,Opcodes.IREM,Opcodes.LREM).contains(compute.opcode()))return Optional.of(List.of("java/lang/ArithmeticException"));
        else return Optional.empty();
        List<String> families=new ArrayList<>(runtime);families.add("java/lang/Error");return Optional.of(List.copyOf(families));
    }
    static List<Gap> queryGaps(Site site,Query<?> query) {
        return query.pending().stream().map(i -> new Gap(i.cause()==QueryCause.BUDGET?GapKind.BUDGET:GapKind.MISSING_DEPENDENCY,site,i.detail())).toList();
    }
    Check check(Action action,List<Atom> operands,OptionalInt length) {
        return check(action,operands,length,false);
    }
    Check check(Action action,List<Atom> operands,OptionalInt length,boolean nonNullReceiver) {
        List<Gap> gaps=new ArrayList<>();List<Possible> possible=new ArrayList<>();
        if(action instanceof NewArray) {
            if(operands.get(0) instanceof Literal l && l.value() instanceof Number n) {
                if(n.intValue()<0)return new Rejected("java/lang/NegativeArraySizeException");
            } else {gaps.add(new Gap(GapKind.CONTROL_CONDITION,action.site(),"array length must be nonnegative"));possible.add(new Possible("java/lang/NegativeArraySizeException","array length may be negative"));}
        }
        boolean field=action instanceof ReadField r && !r.receiver().origins().isEmpty()
                || action instanceof WriteField w && !w.receiver().origins().isEmpty();
        boolean array=action instanceof ReadArray || action instanceof WriteArray;
        if(field || array || action instanceof Compute c && c.opcode()==Opcodes.ARRAYLENGTH) {
            Atom receiver=operands.get(0);
            if(receiver instanceof Literal l && l.value()==null)return new Rejected("java/lang/NullPointerException");
            if(!nonNullReceiver && !nonNull(Value.of(receiver))) {gaps.add(new Gap(GapKind.CONTROL_CONDITION,action.site(),"memory operation requires a nonnull receiver"));possible.add(new Possible("java/lang/NullPointerException","memory operation receiver may be null"));}
            if(array) {
                int size=receiver instanceof ArrayValue snapshot?snapshot.extent()==ArrayExtent.EXACT?snapshot.elements().size():-1:length.orElse(-1);
                if(size==0)return new Rejected("java/lang/ArrayIndexOutOfBoundsException",List.copyOf(possible));
                if(operands.get(1) instanceof Literal l && l.value() instanceof Integer index) {
                    if(index<0 || size>=0 && index>=size)return new Rejected("java/lang/ArrayIndexOutOfBoundsException",List.copyOf(possible));
                    if(size<0){gaps.add(new Gap(GapKind.CONTROL_CONDITION,action.site(),"array index must be within the current array length"));possible.add(new Possible("java/lang/ArrayIndexOutOfBoundsException","array index may exceed the current length"));}
                } else {gaps.add(new Gap(GapKind.CONTROL_CONDITION,action.site(),"array index must be within the current array length"));possible.add(new Possible("java/lang/ArrayIndexOutOfBoundsException","array index may be out of bounds"));}
                if(action instanceof WriteArray && receiver instanceof ObjectValue object && object.type().startsWith("[")
                        && (object.type().charAt(1)=='L' || object.type().charAt(1)=='[')) {
                    var match=ValueBindings.compatible(operands.get(2),object.type().substring(1),program,object.loader());
                    if(match.match()==ValueBindings.Match.INCOMPATIBLE)return new Rejected("java/lang/ArrayStoreException",List.copyOf(possible));
                    gaps.addAll(queryGaps(action.site(),new Query<>(Optional.empty(),match.pending())));
                    if(match.match()==ValueBindings.Match.UNKNOWN || !object.exact()) {
                        gaps.add(new Gap(GapKind.CONTROL_CONDITION,action.site(),"array store requires a compatible runtime component type"));
                        possible.add(new Possible("java/lang/ArrayStoreException","array value may be incompatible with the runtime component type"));
                    }
                }
            }
        }
        if(action instanceof Compute c && Set.of(Opcodes.IDIV,Opcodes.LDIV,Opcodes.IREM,Opcodes.LREM).contains(c.opcode())) {
            if(operands.get(1) instanceof Literal l && l.value() instanceof Number n) {
                if(n.longValue()==0)return new Rejected("java/lang/ArithmeticException");
            } else {gaps.add(new Gap(GapKind.CONTROL_CONDITION,action.site(),"integer divisor must be nonzero"));possible.add(new Possible("java/lang/ArithmeticException","integer divisor may be zero"));}
        }
        return new Normal(List.copyOf(gaps),List.copyOf(possible));
    }
    Conversion cast(Cast cast,Atom atom) {
        ValueBindings.Compatibility match=ValueBindings.compatible(atom,cast.type().startsWith("[")?cast.type():"L"+cast.type()+";",program,program.scope(cast.type(),cast.site().method().loader()));
        if(match.match()==ValueBindings.Match.INCOMPATIBLE)return new Rejected("java/lang/ClassCastException");
        List<Gap> gaps=new ArrayList<>();
        for(QueryIssue issue:match.pending())gaps.add(new Gap(issue.cause()==QueryCause.BUDGET?GapKind.BUDGET:GapKind.MISSING_DEPENDENCY,cast.site(),issue.detail()));
        if(match.match()==ValueBindings.Match.UNKNOWN && gaps.isEmpty())gaps.add(new Gap(GapKind.INPUT_BINDING,cast.site(),"runtime cast compatibility is unspecified"));
        if(atom instanceof ObjectValue object && !object.exact())atom=new ObjectValue(object.id(),cast.type(),false,object.origin(),object.defaultFields(),object.source(),program.scope(cast.type(),cast.site().method().loader()));
        return new Converted(Value.of(atom).requiring(gaps));
    }
    boolean normal(Action action,List<Value> values,Map<Integer,Integer> lengths) {
        if(action instanceof Call call) {
            Value receiver=values.get(values.size()-1);
            if(call.opcode()!=Opcodes.INVOKESTATIC && !nonNull(receiver))return false;
            MethodId id=call.target();
            if(call.opcode()!=Opcodes.INVOKESTATIC && call.opcode()!=Opcodes.INVOKESPECIAL && receiver.alternatives().size()==1
                    && receiver.alternatives().iterator().next().atom() instanceof ObjectValue object && object.exact())
                id=program.method(object.type(),id.name(),id.descriptor(),object.loader());
            Query<Method> query=program.lookup(id);
            return query.pending().isEmpty() && query.value().filter(Method::hasBody)
                    .map(method -> {
                        Facts facts=program.facts(method.id());
                        return facts.limitations().isEmpty() && facts.actions().stream().anyMatch(a -> a instanceof Returned)
                                && facts.actions().stream().allMatch(a -> a instanceof Constant || a instanceof Returned);
                    }).orElse(false);
        }
        if(action instanceof ReadField r)return r.receiver().origins().isEmpty() || nonNull(values.get(0));
        if(action instanceof WriteField w)return w.receiver().origins().isEmpty() || nonNull(values.get(0));
        if(action instanceof Compute compute) {
            if(compute.opcode()==Opcodes.ARRAYLENGTH)return nonNull(values.get(0));
            if(Set.of(Opcodes.IDIV,Opcodes.LDIV,Opcodes.IREM,Opcodes.LREM).contains(compute.opcode()))
                return !values.get(1).empty() && values.get(1).alternatives().stream().allMatch(b -> b.atom() instanceof Literal l && l.value() instanceof Number n && n.longValue()!=0);
        }
        if(action instanceof Cast cast)return !values.get(0).empty() && values.get(0).alternatives().stream().allMatch(b ->
                cast(cast,b.atom()) instanceof Converted converted && converted.value().alternatives().stream().allMatch(v -> v.gaps().isEmpty()));
        if(action instanceof NewArray)return !values.get(0).empty() && values.get(0).alternatives().stream().allMatch(b -> b.atom() instanceof Literal l && l.value() instanceof Number n && n.intValue()>=0);
        if(action instanceof ReadArray || action instanceof WriteArray) {
            if(!nonNull(values.get(0)) || values.get(1).empty())return false;
            for(Bound array:values.get(0).alternatives()) {
                int size=array.atom() instanceof ArrayValue snapshot?snapshot.extent()==ArrayExtent.EXACT?snapshot.elements().size():-1:array.atom() instanceof ObjectValue object?lengths.getOrDefault(object.id(),-1):-1;
                if(size<0 || values.get(1).alternatives().stream().anyMatch(b -> !(b.atom() instanceof Literal l) || !(l.value() instanceof Integer index) || index<0 || index>=size))return false;
                if(action instanceof WriteArray) {
                    if(values.get(2).empty())return false;
                    for(Bound index:values.get(1).alternatives())for(Bound value:values.get(2).alternatives())
                        if(!(check(action,List.of(array.atom(),index.atom(),value.atom()),OptionalInt.of(size)) instanceof Normal n) || !n.gaps().isEmpty())return false;
                }
            }
            return true;
        }
        return !(action instanceof Thrown || action instanceof WriteArray);
    }
    static List<Sources> safetyInputs(Action action) {
        if (action instanceof Call call) return call.receiver().origins().isEmpty()?List.of():List.of(call.receiver());
        if (action instanceof ReadField field) return List.of(field.receiver());
        if (action instanceof WriteField field) return List.of(field.receiver());
        if (action instanceof ReadArray array) return List.of(array.array(),array.index());
        if (action instanceof WriteArray array) return List.of(array.array(),array.index(),array.value());
        if (action instanceof Cast cast) return List.of(cast.input());
        if (action instanceof NewArray array) return List.of(array.length());
        if (action instanceof Compute compute) {
            if (compute.opcode()==Opcodes.ARRAYLENGTH) return compute.inputs();
            if (Set.of(Opcodes.IDIV,Opcodes.LDIV,Opcodes.IREM,Opcodes.LREM).contains(compute.opcode())) return List.of(compute.inputs().get(1));
        }
        return List.of();
    }

    Atom compute(Compute compute,List<Atom> atoms) {
        int op=compute.opcode();
        if (op==Opcodes.INSTANCEOF) {
            Atom atom=atoms.get(0);
            if (atom instanceof Literal literal && literal.value()==null) return new Literal(0);
            if(atom instanceof ObjectValue object && !object.exact())
                return new InstanceTest(object,compute.type(),program.scope(compute.type(),compute.site().method().loader()));
            String type=io.just.knowledge.ValueBindings.runtimeType(atom).orElse("");
            if(type.isEmpty())return new Unknown("instanceof runtime type is unspecified");
            int loader=atom instanceof ObjectValue object?object.loader():0;
            Query<Boolean> match=program.assignable(type,loader,compute.type(),program.scope(compute.type(),compute.site().method().loader()));
            return match.value().<Atom>map(found -> new Literal(found?1:0)).orElseGet(() -> new Unknown("instanceof hierarchy is unresolved: "+match.pending()));
        }
        if (atoms.stream().anyMatch(a -> !(a instanceof Literal l) || !(l.value() instanceof Number))) return new Unknown("JVM operation has unspecified operands: "+op);
        Number a=(Number)((Literal)atoms.get(0)).value(),b=atoms.size()>1?(Number)((Literal)atoms.get(1)).value():0;
        return switch(op) {
            case Opcodes.IINC -> new Literal(a.intValue()+compute.operand());
            case Opcodes.IADD -> new Literal(a.intValue()+b.intValue()); case Opcodes.ISUB -> new Literal(a.intValue()-b.intValue());
            case Opcodes.IMUL -> new Literal(a.intValue()*b.intValue()); case Opcodes.IDIV -> new Literal(a.intValue()/b.intValue()); case Opcodes.IREM -> new Literal(a.intValue()%b.intValue());
            case Opcodes.IAND -> new Literal(a.intValue()&b.intValue()); case Opcodes.IOR -> new Literal(a.intValue()|b.intValue()); case Opcodes.IXOR -> new Literal(a.intValue()^b.intValue());
            case Opcodes.ISHL -> new Literal(a.intValue()<<b.intValue()); case Opcodes.ISHR -> new Literal(a.intValue()>>b.intValue()); case Opcodes.IUSHR -> new Literal(a.intValue()>>>b.intValue());
            case Opcodes.INEG -> new Literal(-a.intValue());
            case Opcodes.LADD -> new Literal(a.longValue()+b.longValue()); case Opcodes.LSUB -> new Literal(a.longValue()-b.longValue()); case Opcodes.LMUL -> new Literal(a.longValue()*b.longValue());
            case Opcodes.LDIV -> new Literal(a.longValue()/b.longValue()); case Opcodes.LREM -> new Literal(a.longValue()%b.longValue()); case Opcodes.LNEG -> new Literal(-a.longValue());
            case Opcodes.LAND -> new Literal(a.longValue()&b.longValue()); case Opcodes.LOR -> new Literal(a.longValue()|b.longValue()); case Opcodes.LXOR -> new Literal(a.longValue()^b.longValue());
            case Opcodes.LSHL -> new Literal(a.longValue()<<b.intValue()); case Opcodes.LSHR -> new Literal(a.longValue()>>b.intValue()); case Opcodes.LUSHR -> new Literal(a.longValue()>>>b.intValue());
            case Opcodes.FADD -> new Literal(a.floatValue()+b.floatValue()); case Opcodes.FSUB -> new Literal(a.floatValue()-b.floatValue()); case Opcodes.FMUL -> new Literal(a.floatValue()*b.floatValue());
            case Opcodes.FDIV -> new Literal(a.floatValue()/b.floatValue()); case Opcodes.FREM -> new Literal(a.floatValue()%b.floatValue()); case Opcodes.FNEG -> new Literal(-a.floatValue());
            case Opcodes.DADD -> new Literal(a.doubleValue()+b.doubleValue()); case Opcodes.DSUB -> new Literal(a.doubleValue()-b.doubleValue()); case Opcodes.DMUL -> new Literal(a.doubleValue()*b.doubleValue());
            case Opcodes.DDIV -> new Literal(a.doubleValue()/b.doubleValue()); case Opcodes.DREM -> new Literal(a.doubleValue()%b.doubleValue()); case Opcodes.DNEG -> new Literal(-a.doubleValue());
            case Opcodes.I2B -> new Literal((int)(byte)a.intValue()); case Opcodes.I2C -> new Literal((int)(char)a.intValue()); case Opcodes.I2S -> new Literal((int)(short)a.intValue());
            case Opcodes.L2I,Opcodes.F2I,Opcodes.D2I -> new Literal(a.intValue()); case Opcodes.I2L,Opcodes.F2L,Opcodes.D2L -> new Literal(a.longValue());
            case Opcodes.I2F,Opcodes.L2F,Opcodes.D2F -> new Literal(a.floatValue()); case Opcodes.I2D,Opcodes.L2D,Opcodes.F2D -> new Literal(a.doubleValue());
            case Opcodes.LCMP -> new Literal(Long.compare(a.longValue(),b.longValue()));
            case Opcodes.FCMPL,Opcodes.FCMPG -> new Literal(Float.isNaN(a.floatValue()) || Float.isNaN(b.floatValue())?(op==Opcodes.FCMPL?-1:1):a.floatValue()==b.floatValue()?0:a.floatValue()>b.floatValue()?1:-1);
            case Opcodes.DCMPL,Opcodes.DCMPG -> new Literal(Double.isNaN(a.doubleValue()) || Double.isNaN(b.doubleValue())?(op==Opcodes.DCMPL?-1:1):a.doubleValue()==b.doubleValue()?0:a.doubleValue()>b.doubleValue()?1:-1);
            default -> new Unknown("JVM operation not modeled: "+op);
        };
    }

    Optional<Boolean> branchTaken(Branch branch,List<Value> values) {
        int operation=branch.opcode();
        if(operation>=Opcodes.IFEQ && operation<=Opcodes.IF_ICMPLE) {
            Optional<IntegralRange> left=range(values.get(0)),right=values.size()>1?range(values.get(1)):Optional.of(new IntegralRange(0,0));
            if(left.isPresent() && right.isPresent())return compare(operation,left.get(),right.get());
        }
        List<Atom> args = new ArrayList<>();
        for (Value value : values) {
            Set<Atom> atoms = new LinkedHashSet<>();
            for (Bound bound : value.alternatives()) atoms.add(bound.atom());
            if (atoms.size() != 1) return Optional.empty();
            args.add(atoms.iterator().next());
        }
        int op = branch.opcode();
        if (op == Opcodes.IFNULL || op == Opcodes.IFNONNULL) {
            Atom atom = args.get(0);
            if (atom instanceof Literal literal && literal.value() == null) return Optional.of(op == Opcodes.IFNULL);
            return nonNull(Value.of(atom))?Optional.of(op == Opcodes.IFNONNULL):Optional.empty();
        }
        if (op==Opcodes.IF_ACMPEQ || op==Opcodes.IF_ACMPNE) {
            Atom first=args.get(0),second=args.get(1); Optional<Boolean> equal=Optional.empty();
            if (first instanceof ObjectValue left && left.exact() && second instanceof ObjectValue right && right.exact()) equal=Optional.of(left.id()==right.id());
            else if(first instanceof ClassValue left && left.exact() && second instanceof ClassValue right && right.exact())equal=Optional.of(left.loader()==right.loader() && left.descriptor().equals(right.descriptor()));
            else if (first instanceof Literal left && left.value()==null && second instanceof Literal right && right.value()==null) equal=Optional.of(true);
            else if (first instanceof Literal left && left.value()==null && second instanceof ObjectValue right && right.exact()
                    || second instanceof Literal rightNull && rightNull.value()==null && first instanceof ObjectValue leftObject && leftObject.exact()) equal=Optional.of(false);
            return equal.map(value -> op==Opcodes.IF_ACMPEQ?value:!value);
        }
        if (args.stream().anyMatch(a -> !(a instanceof Literal literal) || !(literal.value() instanceof Number))) return Optional.empty();
        long a = ((Number) ((Literal) args.get(0)).value()).longValue();
        long b = args.size() > 1 ? ((Number) ((Literal) args.get(1)).value()).longValue() : 0;
        return switch (op) {
            case Opcodes.IFEQ, Opcodes.IF_ICMPEQ -> Optional.of(a == b);
            case Opcodes.IFNE, Opcodes.IF_ICMPNE -> Optional.of(a != b);
            case Opcodes.IFLT, Opcodes.IF_ICMPLT -> Optional.of(a < b);
            case Opcodes.IFGE, Opcodes.IF_ICMPGE -> Optional.of(a >= b);
            case Opcodes.IFGT, Opcodes.IF_ICMPGT -> Optional.of(a > b);
            case Opcodes.IFLE, Opcodes.IF_ICMPLE -> Optional.of(a <= b);
            default -> Optional.empty();
        };
    }

    /** Refine the same scalar source on the selected JVM branch; holes stay unknown. */
    Optional<Path> assume(Branch branch,int successor,List<Value> values,Path path) {
        int operation=branch.opcode();
        if(operation<Opcodes.IFEQ || operation>Opcodes.IF_ICMPLE)return Optional.of(path);
        List<Atom> atoms=new ArrayList<>();
        for(Value value:values) {
            Set<Atom> alternatives=new LinkedHashSet<>();
            for(Bound bound:value.under(path).alternatives())alternatives.add(CandidateBindings.project(bound.atom(),path));
            if(alternatives.size()!=1)return Optional.of(path);
            atoms.add(alternatives.iterator().next());
        }
        boolean taken=successor==branch.jumpTarget();
        if(atoms.size()==1 && atoms.get(0) instanceof InstanceTest test && (operation==Opcodes.IFEQ || operation==Opcodes.IFNE)) {
            boolean matches=operation==Opcodes.IFNE?taken:!taken;
            if(!matches || !(test.receiver() instanceof ObjectValue object) || object.exact() || test.type().startsWith("["))return Optional.of(path);
            Optional<ClassInfo> type=program.type(test.type(),test.loader());
            if(type.isEmpty() || (type.get().access() & Opcodes.ACC_FINAL)==0)return Optional.of(path);
            Query<Boolean> compatible=program.assignable(test.type(),test.loader(),object.type(),object.loader());
            if(compatible.value().equals(Optional.of(false)) && compatible.pending().isEmpty())return Optional.empty();
            if(!compatible.value().equals(Optional.of(true)) || !compatible.pending().isEmpty())return Optional.of(path);
            Optional<InputLocation> source=Values.location(object);
            return source.isEmpty()?Optional.of(path):path.selecting(source.get().at(new RuntimeClass()),new ClassValue("L"+test.type()+";",true,Optional.empty(),test.loader()));
        }
        Optional<IntegralRange> left=range(atoms.get(0),path),right=atoms.size()>1?range(atoms.get(1),path):Optional.of(new IntegralRange(0,0));
        if(left.isEmpty() || right.isEmpty())return Optional.of(path);
        Optional<Boolean> known=compare(operation,left.get(),right.get());
        if(known.isPresent())return known.get()==taken?Optional.of(path):Optional.empty();
        int operand=0;IntegralRange constant=right.get(),domain=left.get();
        if(constant.minimum()!=constant.maximum()) {
            if(atoms.size()!=2 || left.get().minimum()!=left.get().maximum())return Optional.of(path);
            operand=1;constant=left.get();domain=right.get();
            operation=switch(operation) {case Opcodes.IF_ICMPLT -> Opcodes.IF_ICMPGT;case Opcodes.IF_ICMPLE -> Opcodes.IF_ICMPGE;case Opcodes.IF_ICMPGT -> Opcodes.IF_ICMPLT;case Opcodes.IF_ICMPGE -> Opcodes.IF_ICMPLE;default -> operation;};
        }
        Atom original=atoms.get(operand);Optional<InputLocation> source=Values.location(original);
        if(source.isEmpty())return Optional.of(path);
        long number=constant.minimum(),low=domain.minimum(),high=domain.maximum();
        int comparison=switch(operation) {
            case Opcodes.IF_ICMPEQ -> Opcodes.IFEQ;case Opcodes.IF_ICMPNE -> Opcodes.IFNE;
            case Opcodes.IF_ICMPLT -> Opcodes.IFLT;case Opcodes.IF_ICMPGE -> Opcodes.IFGE;
            case Opcodes.IF_ICMPGT -> Opcodes.IFGT;case Opcodes.IF_ICMPLE -> Opcodes.IFLE;default -> operation;
        };
        if(!taken)comparison=switch(comparison) {
            case Opcodes.IFEQ -> Opcodes.IFNE;case Opcodes.IFNE -> Opcodes.IFEQ;
            case Opcodes.IFLT -> Opcodes.IFGE;case Opcodes.IFGE -> Opcodes.IFLT;
            case Opcodes.IFGT -> Opcodes.IFLE;case Opcodes.IFLE -> Opcodes.IFGT;default -> throw new IllegalStateException("not an integral branch: "+operation);
        };
        if(comparison==Opcodes.IFEQ){low=Math.max(low,number);high=Math.min(high,number);}
        else if(comparison==Opcodes.IFNE) {
            if(low==number){if(number==Long.MAX_VALUE)return Optional.empty();low++;}
            else if(high==number){if(number==Long.MIN_VALUE)return Optional.empty();high--;}
            else return Optional.of(path);
        } else if(comparison==Opcodes.IFLT){if(number==Long.MIN_VALUE)return Optional.empty();high=Math.min(high,number-1);}
        else if(comparison==Opcodes.IFGE)low=Math.max(low,number);
        else if(comparison==Opcodes.IFGT){if(number==Long.MAX_VALUE)return Optional.empty();low=Math.max(low,number+1);}
        else high=Math.min(high,number);
        return low>high?Optional.empty():path.restricting(source.get(),original,descriptor(original),new IntegralRange(low,high));
    }

    private static String descriptor(Atom atom) {
        return atom instanceof ExternalValue value?value.descriptor():atom instanceof Symbolic value?value.type():atom instanceof UnboundValue value?value.descriptor():"";
    }
    private static Optional<IntegralRange> range(Atom atom,Path path) {
        OptionalLong literal=IntegralRange.literal(atom);
        if(literal.isPresent())return Optional.of(new IntegralRange(literal.getAsLong(),literal.getAsLong()));
        Optional<IntegralRange> domain=switch(descriptor(atom)) {
            case "Z" -> Optional.of(new IntegralRange(0,1));case "B" -> Optional.of(new IntegralRange(Byte.MIN_VALUE,Byte.MAX_VALUE));
            case "S" -> Optional.of(new IntegralRange(Short.MIN_VALUE,Short.MAX_VALUE));case "C" -> Optional.of(new IntegralRange(Character.MIN_VALUE,Character.MAX_VALUE));
            case "I" -> Optional.of(new IntegralRange(Integer.MIN_VALUE,Integer.MAX_VALUE));case "J" -> Optional.of(new IntegralRange(Long.MIN_VALUE,Long.MAX_VALUE));default -> Optional.empty();
        };
        Optional<IntegralRange> required=Values.location(atom).map(path.selections()::get).flatMap(Selection::range);
        return domain.isPresent() && required.isPresent()?domain.get().and(required.get()):domain;
    }
    private static Optional<IntegralRange> range(Value value) {
        IntegralRange result=null;
        for(Bound bound:value.alternatives()) {
            Optional<IntegralRange> next=range(bound.atom(),bound.path());if(next.isEmpty())return Optional.empty();
            result=result==null?next.get():new IntegralRange(Math.min(result.minimum(),next.get().minimum()),Math.max(result.maximum(),next.get().maximum()));
        }
        return Optional.ofNullable(result);
    }
    private static Optional<Boolean> compare(int operation,IntegralRange left,IntegralRange right) {
        boolean disjoint=left.maximum()<right.minimum() || right.maximum()<left.minimum();
        return switch(operation) {
            case Opcodes.IFEQ,Opcodes.IF_ICMPEQ -> disjoint?Optional.of(false):left.minimum()==left.maximum() && left.equals(right)?Optional.of(true):Optional.empty();
            case Opcodes.IFNE,Opcodes.IF_ICMPNE -> compare(Opcodes.IFEQ,left,right).map(equal -> !equal);
            case Opcodes.IFLT,Opcodes.IF_ICMPLT -> left.maximum()<right.minimum()?Optional.of(true):left.minimum()>=right.maximum()?Optional.of(false):Optional.empty();
            case Opcodes.IFGE,Opcodes.IF_ICMPGE -> compare(Opcodes.IFLT,left,right).map(less -> !less);
            case Opcodes.IFGT,Opcodes.IF_ICMPGT -> compare(Opcodes.IFLT,right,left);
            case Opcodes.IFLE,Opcodes.IF_ICMPLE -> compare(Opcodes.IFGT,left,right).map(greater -> !greater);
            default -> Optional.empty();
        };
    }

    Optional<Integer> successor(Branch branch,List<Value> values,List<Edge> cfg) {
        if (branch.opcode()==Opcodes.TABLESWITCH || branch.opcode()==Opcodes.LOOKUPSWITCH) {
            Set<Atom> atoms=new HashSet<>(); for (Bound value:values.get(0).alternatives()) atoms.add(value.atom());
            if (atoms.size()==1 && atoms.iterator().next() instanceof Literal value && value.value() instanceof Number number)
                return Optional.of(branch.cases().getOrDefault(number.intValue(),branch.jumpTarget()));
            return Optional.empty();
        }
        return branchTaken(branch,values).map(t -> t?branch.jumpTarget():cfg.stream().filter(e -> e.from()==branch.site().instruction() && !e.exceptional() && e.to()!=branch.jumpTarget()).map(Edge::to).findFirst().orElse(branch.jumpTarget()));
    }

    static boolean nonNull(Value value) {
        return !value.empty() && value.alternatives().stream().allMatch(v -> v.atom() instanceof ObjectValue object && object.exact() || v.atom() instanceof CollectionView || v.atom() instanceof MapEntryValue || v.atom() instanceof ClassValue || v.atom() instanceof Reflected || v.atom() instanceof ReflectedField || v.atom() instanceof ConstructorValue || v.atom() instanceof LambdaValue || v.atom() instanceof ProxyValue || v.atom() instanceof ArrayValue || v.atom() instanceof LoaderValue || v.atom() instanceof MethodHandleValue || v.atom() instanceof MethodTypeValue || v.atom() instanceof LookupValue || v.atom() instanceof HttpServerValue || v.atom() instanceof StringPrefix || v.atom() instanceof StringConcat || v.atom() instanceof Literal literal && literal.value() instanceof String);
    }
}
