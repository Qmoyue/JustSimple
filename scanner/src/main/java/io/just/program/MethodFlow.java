package io.just.program;

import io.just.program.Program.*;
import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.tree.analysis.*;
import java.util.*;
import static io.just.program.Program.sources;
import static io.just.program.Program.exceptional;

/** Method-local bytecode to immutable facts. No input, hierarchy, heap or query cache is owned here. */
final class MethodFlow {
    private MethodFlow() {}
    static Facts analyze(Method method,MethodNode node,String source) {
        MethodId id=method.id();
        for (AbstractInsnNode instruction : node.instructions) {
            if (instruction.getOpcode() == Opcodes.JSR || instruction.getOpcode() == Opcodes.RET)
                return new Facts(method, List.of(), List.of(), Map.of(), List.of(new Limitation(CoverageCause.UNSUPPORTED, "unsupported legacy JSR/RET control flow")));
        }
        Map<AbstractInsnNode, Integer> indexes = new IdentityHashMap<>();
        for (int i = 0; i < node.instructions.size(); i++) indexes.put(node.instructions.get(i), i);
        FlowInterpreter interpreter = new FlowInterpreter(indexes,node);
        Set<Edge> edges = new LinkedHashSet<>();
        Analyzer<FlowValue> analyzer = new Analyzer<>(interpreter) {
            @Override protected void newControlFlowEdge(int from, int to) { edges.add(new Edge(from, to, false)); }
            @Override protected boolean newControlFlowExceptionEdge(int from, int to) {
                edges.add(new Edge(from, to, true));
                return true;
            }
        };
        try {
            Frame<FlowValue>[] frames = analyzer.analyze(id.owner(), node);
            int[] loopCoverage=new int[node.instructions.size()+1];
            for(Edge edge:edges)if(!edge.exceptional() && edge.to()<=edge.from()){loopCoverage[edge.to()]++;loopCoverage[edge.from()+1]--;}
            List<Action> actions = new ArrayList<>();
            int line = -1,loops=0;
            for (int index = 0; index < node.instructions.size(); index++) {
                AbstractInsnNode instruction = node.instructions.get(index);
                loops+=loopCoverage[index];
                if (instruction instanceof LineNumberNode l) line = l.line;
                Frame<FlowValue> frame = frames[index];
                if (frame == null || instruction.getOpcode() < 0) continue;
                Site site = new Site(id, index, line, source);
                Action action = action(site, instruction, frame, indexes, loops>0,interpreter.guardedCopies);
                if (action != null) actions.add(action);
            }
            Map<Integer,List<Guard>> guards=guards(node,edges,actions);
            actions=localReads(actions,guards,node);
            return new Facts(method, List.copyOf(actions), List.copyOf(edges), guards,node.tryCatchBlocks.stream().map(h -> new Handler(indexes.get(h.start),indexes.get(h.end),indexes.get(h.handler),h.type==null?"java/lang/Throwable":h.type)).toList(),
                    interpreter.truncated ? List.of(new Limitation(CoverageCause.BUDGET, "method value origin budget (64 alternatives)")) : List.of());
        } catch (AnalyzerException invalid) { throw new Failure("invalid JVM stack/control flow: " + id + " from " + source, invalid); }
    }

    private static Sources stack(Frame<FlowValue> frame, int fromTop) {
        return new Sources(frame.getStack(frame.getStackSize() - 1 - fromTop).origins());
    }

    /** Keep only reads that carry a control requirement across a weaker consumer/join. */
    private static List<Action> localReads(List<Action> actions,Map<Integer,List<Guard>> guards,MethodNode node) {
        Map<Integer,Sources> aliases=new LinkedHashMap<>();Set<Integer> needed=new HashSet<>();
        for(Action action:actions)if(action instanceof Assign assign) {
            int opcode=node.instructions.get(action.site().instruction()).getOpcode();
            if(opcode>=Opcodes.ILOAD && opcode<=Opcodes.ALOAD)aliases.put(action.site().instruction(),assign.input());
        }
        if(aliases.isEmpty())return actions;
        for(Action action:actions)for(Sources source:sources(action))for(Origin origin:source.origins())if(origin instanceof Producer producer && aliases.containsKey(producer.instruction())
                && !containsGuards(guards.getOrDefault(action.site().instruction(),List.of()),guards.getOrDefault(producer.instruction(),List.of())))needed.add(producer.instruction());
        needed.forEach(aliases::remove);
        Map<Integer,Sources> expanded=new HashMap<>();
        for(var alias:aliases.entrySet())expanded.put(alias.getKey(),expand(alias.getValue(),aliases,expanded));
        java.util.function.UnaryOperator<Sources> resolve=source -> expand(source,aliases,expanded);
        List<Action> result=new ArrayList<>();
        for(Action action:actions) {
            if(aliases.containsKey(action.site().instruction()))continue;
            if(sources(action).stream().noneMatch(s -> s.origins().stream().anyMatch(o -> o instanceof Producer p && aliases.containsKey(p.instruction())))){result.add(action);continue;}
            if(action instanceof Assign a)action=new Assign(a.site(),resolve.apply(a.input()));
            else if(action instanceof Call a)action=new Call(a.site(),a.target(),a.opcode(),resolve.apply(a.receiver()),a.arguments().stream().map(resolve).toList(),a.bootstrap());
            else if(action instanceof Cast a)action=new Cast(a.site(),a.type(),resolve.apply(a.input()));
            else if(action instanceof NewArray a)action=new NewArray(a.site(),a.descriptor(),resolve.apply(a.length()),a.repeated());
            else if(action instanceof ReadField a)action=new ReadField(a.site(),a.field(),resolve.apply(a.receiver()));
            else if(action instanceof WriteField a)action=new WriteField(a.site(),a.field(),resolve.apply(a.receiver()),resolve.apply(a.value()));
            else if(action instanceof ReadArray a)action=new ReadArray(a.site(),resolve.apply(a.array()),resolve.apply(a.index()));
            else if(action instanceof WriteArray a)action=new WriteArray(a.site(),resolve.apply(a.array()),resolve.apply(a.index()),resolve.apply(a.value()));
            else if(action instanceof Compute a)action=new Compute(a.site(),a.opcode(),a.inputs().stream().map(resolve).toList(),a.operand(),a.type());
            else if(action instanceof Branch a)action=new Branch(a.site(),a.opcode(),a.inputs().stream().map(resolve).toList(),a.jumpTarget(),a.cases());
            else if(action instanceof Returned a)action=new Returned(a.site(),resolve.apply(a.value()));
            else if(action instanceof Thrown a)action=new Thrown(a.site(),resolve.apply(a.value()));
            result.add(action);
        }
        return result;
    }
    private static boolean containsGuards(List<Guard> consumer,List<Guard> required) {
        int at=0;
        for(Guard guard:required) {
            while(at<consumer.size() && compareGuard(consumer.get(at),guard)<0)at++;
            if(at==consumer.size() || !consumer.get(at++).equals(guard))return false;
        }
        return true;
    }
    private static int compareGuard(Guard left,Guard right) {
        int order=Integer.compare(left.branch(),right.branch());if(order!=0)return order;
        order=left.kind().compareTo(right.kind());return order!=0?order:Integer.compare(left.successor(),right.successor());
    }
    private static Sources expand(Sources source,Map<Integer,Sources> aliases,Map<Integer,Sources> expanded) {
        if(source.origins().stream().noneMatch(o -> o instanceof Producer p && aliases.containsKey(p.instruction())))return source;
        Set<Origin> result=new LinkedHashSet<>(),seen=new HashSet<>();ArrayDeque<Origin> pending=new ArrayDeque<>(source.origins());
        while(!pending.isEmpty()) {
            Origin origin=pending.removeFirst();if(!seen.add(origin))continue;
            if(origin instanceof Producer producer && aliases.containsKey(producer.instruction())) {
                Sources known=expanded.get(producer.instruction());if(known!=null)result.addAll(known.origins());else pending.addAll(aliases.get(producer.instruction()).origins());
            } else result.add(origin);
        }
        if(result.isEmpty())result.add(new UnknownOrigin("cyclic local source"));
        return new Sources(result);
    }
    private static Sources empty() { return new Sources(Set.of()); }
    private static List<Sources> arguments(Frame<FlowValue> frame, int count) {
        List<Sources> args = new ArrayList<>();
        for (int i = count - 1; i >= 0; i--) args.add(stack(frame, i));
        return List.copyOf(args);
    }

    private static Action action(Site site, AbstractInsnNode instruction, Frame<FlowValue> frame,
                                 Map<AbstractInsnNode, Integer> indexes, boolean repeated,boolean guardedCopies) {
        int op = instruction.getOpcode();
        if(guardedCopies && op>=Opcodes.ILOAD && op<=Opcodes.ALOAD)return new Assign(site,new Sources(frame.getLocal(((VarInsnNode)instruction).var).origins()));
        if(repeated && op>=Opcodes.ISTORE && op<=Opcodes.ASTORE)return new Assign(site,stack(frame,0));
        if (instruction instanceof MethodInsnNode call) {
            int count = Type.getArgumentTypes(call.desc).length;
            return new Call(site, new MethodId(call.owner, call.name, call.desc,site.method().loader()), op,
                    op == Opcodes.INVOKESTATIC ? empty() : stack(frame, count), arguments(frame, count));
        }
        if (instruction instanceof InvokeDynamicInsnNode call) {
            return new Call(site, new MethodId("<invokedynamic>", call.name, call.desc), op, empty(),
                    arguments(frame, Type.getArgumentTypes(call.desc).length),Optional.of(new Bootstrap(handle(call.bsm),Arrays.stream(call.bsmArgs).map(value -> scoped(constant(value),site.method().loader())).toList())));
        }
        if (instruction instanceof FieldInsnNode field) {
            FieldId id = new FieldId(field.owner, field.name, field.desc,site.method().loader());
            return switch (op) {
                case Opcodes.GETFIELD -> new ReadField(site, id, stack(frame, 0));
                case Opcodes.GETSTATIC -> new ReadField(site, id, empty());
                case Opcodes.PUTFIELD -> new WriteField(site, id, stack(frame, 1), stack(frame, 0));
                case Opcodes.PUTSTATIC -> new WriteField(site, id, empty(), stack(frame, 0));
                default -> throw new IllegalStateException("field opcode " + op);
            };
        }
        if (instruction instanceof TypeInsnNode type) {
            return switch (op) {
                case Opcodes.NEW -> new Allocate(site, type.desc, repeated);
                case Opcodes.ANEWARRAY -> new NewArray(site, "[" + (type.desc.startsWith("[") ? type.desc : "L" + type.desc + ";"), stack(frame, 0), repeated);
                case Opcodes.CHECKCAST -> new Cast(site, type.desc, stack(frame, 0));
                default -> new Compute(site, op, List.of(stack(frame, 0)),0,type.desc);
            };
        }
        if (instruction instanceof LdcInsnNode constant) {
            JvmConstant value = scoped(constant(constant.cst),site.method().loader());
            return new Constant(site, value);
        }
        if (instruction instanceof IntInsnNode number) {
            if (op == Opcodes.NEWARRAY) return new NewArray(site, "[" + switch (number.operand) {
                case Opcodes.T_BOOLEAN -> "Z"; case Opcodes.T_BYTE -> "B"; case Opcodes.T_CHAR -> "C";
                case Opcodes.T_SHORT -> "S"; case Opcodes.T_INT -> "I"; case Opcodes.T_LONG -> "J";
                case Opcodes.T_FLOAT -> "F"; case Opcodes.T_DOUBLE -> "D";
                default -> throw new IllegalStateException("array type");
            }, stack(frame, 0), repeated);
            return new Constant(site, new LiteralConstant(number.operand));
        }
        if (op == Opcodes.ACONST_NULL) return new Constant(site, new LiteralConstant(null));
        if (op >= Opcodes.ICONST_M1 && op <= Opcodes.ICONST_5) return new Constant(site, new LiteralConstant(op - Opcodes.ICONST_0));
        if (op == Opcodes.LCONST_0 || op == Opcodes.LCONST_1) return new Constant(site, new LiteralConstant((long) (op - Opcodes.LCONST_0)));
        if (op >= Opcodes.FCONST_0 && op <= Opcodes.FCONST_2) return new Constant(site, new LiteralConstant((float) (op - Opcodes.FCONST_0)));
        if (op == Opcodes.DCONST_0 || op == Opcodes.DCONST_1) return new Constant(site, new LiteralConstant((double) (op - Opcodes.DCONST_0)));
        if (op >= Opcodes.IALOAD && op <= Opcodes.SALOAD) return new ReadArray(site, stack(frame, 1), stack(frame, 0));
        if (op >= Opcodes.IASTORE && op <= Opcodes.SASTORE) return new WriteArray(site, stack(frame, 2), stack(frame, 1), stack(frame, 0));
        if (op >= Opcodes.IRETURN && op <= Opcodes.ARETURN) return new Returned(site, stack(frame, 0));
        if (op == Opcodes.RETURN) return new Returned(site, empty());
        if (instruction instanceof JumpInsnNode jump) {
            if (op == Opcodes.GOTO) return null;
            int count = op >= Opcodes.IF_ICMPEQ && op <= Opcodes.IF_ACMPNE ? 2 : 1;
            return new Branch(site, op, arguments(frame, count), indexes.get(jump.label));
        }
        if (instruction instanceof TableSwitchInsnNode table) {
            Map<Integer,Integer> cases=new LinkedHashMap<>();
            for (int i=0;i<table.labels.size();i++) cases.put(table.min+i,indexes.get(table.labels.get(i)));
            return new Branch(site,op,List.of(stack(frame,0)),indexes.get(table.dflt),Map.copyOf(cases));
        }
        if (instruction instanceof LookupSwitchInsnNode lookup) {
            Map<Integer,Integer> cases=new LinkedHashMap<>();
            for (int i=0;i<lookup.keys.size();i++) cases.put(lookup.keys.get(i),indexes.get(lookup.labels.get(i)));
            return new Branch(site,op,List.of(stack(frame,0)),indexes.get(lookup.dflt),Map.copyOf(cases));
        }
        if (op==Opcodes.ATHROW) return new Thrown(site,stack(frame,0));
        if (op >= Opcodes.IADD && op <= Opcodes.LXOR) {
            int count = op >= Opcodes.INEG && op <= Opcodes.DNEG ? 1 : 2;
            return new Compute(site, op, arguments(frame, count));
        }
        if (op >= Opcodes.I2L && op <= Opcodes.DCMPG) {
            int count = op >= Opcodes.LCMP ? 2 : 1;
            return new Compute(site, op, arguments(frame, count));
        }
        if (op == Opcodes.ARRAYLENGTH || op == Opcodes.INSTANCEOF) return new Compute(site, op, List.of(stack(frame, 0)));
        if (instruction instanceof IincInsnNode increment)
            return new Compute(site, op, List.of(new Sources(frame.getLocal(increment.var).origins())),increment.incr,"");
        if (instruction instanceof MultiANewArrayInsnNode multi)
            return new Compute(site, op, arguments(frame, multi.dims));
        return null; // Stack transport is interpreted by ASM, not duplicated here.
    }

    /** Required branch choices. Alternative value producers retain their own choices at joins. */
    private static Map<Integer, List<Guard>> guards(MethodNode node, Set<Edge> edges,List<Action> actions) {
        Set<Integer> exceptional= new HashSet<>();for(Action action:actions)if(exceptional(action))exceptional.add(action.site().instruction());
        Map<Integer, List<Edge>> outgoing = new HashMap<>();
        for (Edge edge : edges) if (!edge.exceptional() || exceptional.contains(edge.from())) outgoing.computeIfAbsent(edge.from(), k -> new ArrayList<>()).add(edge);
        Map<Integer, Set<Guard>> values = new HashMap<>();
        ArrayDeque<Integer> work = new ArrayDeque<>();
        values.put(0, Set.of());
        work.add(0);
        while (!work.isEmpty()) {
            int from = work.removeFirst();
            for (Edge edge : outgoing.getOrDefault(from, List.of())) {
                Set<Guard> next = new LinkedHashSet<>(values.get(from));
                AbstractInsnNode instruction = node.instructions.get(from);
                if (edge.exceptional()) next.add(new Guard(edge.to(),edge.to(),GuardKind.HANDLER));
                else if (outgoing.get(from).stream().anyMatch(Edge::exceptional)) next.add(new Guard(from,edge.to(),GuardKind.NORMAL));
                if (!edge.exceptional() && (instruction instanceof JumpInsnNode && instruction.getOpcode() != Opcodes.GOTO
                        || instruction instanceof TableSwitchInsnNode || instruction instanceof LookupSwitchInsnNode))
                    next.add(new Guard(from, edge.to()));
                Set<Guard> previous = values.get(edge.to());
                if (previous != null) next.retainAll(previous);
                if (!next.equals(previous)) {
                    values.put(edge.to(), Set.copyOf(next));
                    work.add(edge.to());
                }
            }
        }
        // ASM visits every handler, even when its protected block contains only safe instructions.
        // Keep unknown operations conservative without weakening guards on already reachable joins.
        if(!node.tryCatchBlocks.isEmpty() && node.tryCatchBlocks.stream().anyMatch(handler -> !values.containsKey(node.instructions.indexOf(handler.handler)))) {
            Set<Integer> possible=new HashSet<>(values.keySet());
            for(TryCatchBlockNode handler:node.tryCatchBlocks) {
                int start=node.instructions.indexOf(handler.start),end=node.instructions.indexOf(handler.end),target=node.instructions.indexOf(handler.handler);
                boolean safe=true;for(int i=start;i<end && safe;i++)safe=cannotThrow(node.instructions.get(i).getOpcode());
                if(!safe && possible.add(target))work.add(target);
            }
            while(!work.isEmpty())for(Edge edge:outgoing.getOrDefault(work.removeFirst(),List.of()))if(possible.add(edge.to()))work.add(edge.to());
            for(Action action:actions)if(!possible.contains(action.site().instruction())) {
                int at=action.site().instruction();values.put(at,Set.of(new Guard(at,at,GuardKind.UNREACHABLE)));
            }
        }
        Map<Integer, List<Guard>> result = new LinkedHashMap<>();
        values.forEach((key, guards) -> result.put(key, guards.stream().sorted(MethodFlow::compareGuard).toList()));
        return Map.copyOf(result);
    }

    private static boolean cannotThrow(int opcode) {
        return opcode<0 || opcode==Opcodes.NOP || opcode>=Opcodes.ACONST_NULL && opcode<=Opcodes.SIPUSH
                || opcode>=Opcodes.ILOAD && opcode<=Opcodes.ALOAD || opcode>=Opcodes.ISTORE && opcode<=Opcodes.ASTORE
                || opcode>=Opcodes.POP && opcode<=Opcodes.SWAP || opcode==Opcodes.IINC
                || opcode>=Opcodes.IADD && opcode<=Opcodes.LXOR && opcode!=Opcodes.IDIV && opcode!=Opcodes.LDIV && opcode!=Opcodes.IREM && opcode!=Opcodes.LREM
                || opcode>=Opcodes.I2L && opcode<=Opcodes.DCMPG || opcode>=Opcodes.IFEQ && opcode<=Opcodes.GOTO
                || opcode==Opcodes.IFNULL || opcode==Opcodes.IFNONNULL || opcode==Opcodes.TABLESWITCH || opcode==Opcodes.LOOKUPSWITCH
                || opcode>=Opcodes.IRETURN && opcode<=Opcodes.RETURN;
    }

    private static JvmConstant scoped(JvmConstant value,int loader) {
        if(value instanceof HandleConstant handle){MethodId target=handle.target();return new HandleConstant(handle.tag(),new MethodId(target.owner(),target.name(),target.descriptor(),loader),handle.interfaceOwner());}return value;
    }
    private static HandleConstant handle(Handle handle) { return new HandleConstant(handle.getTag(),new MethodId(handle.getOwner(),handle.getName(),handle.getDesc()),handle.isInterface()); }
    static JvmConstant constant(Object value) {
        if (value instanceof Type type) return type.getSort()==Type.METHOD?new MethodTypeConstant(type.getDescriptor()):new ClassConstant(type.getDescriptor());
        if (value instanceof Handle handle) return handle(handle);
        if (value instanceof ConstantDynamic) return new UnsupportedConstant("ConstantDynamic");
        return new LiteralConstant(value);
    }

    private record FlowValue(BasicValue basic, Set<Origin> origins) implements org.objectweb.asm.tree.analysis.Value {
        @Override public int getSize() { return basic.getSize(); }
    }
    private static final class FlowInterpreter extends Interpreter<FlowValue> {
        private final BasicInterpreter basic = new BasicInterpreter();
        private final Map<AbstractInsnNode, Integer> indexes;
        private boolean truncated;
        private final BitSet loopAssignments=new BitSet();
        private final boolean guardedCopies;
        FlowInterpreter(Map<AbstractInsnNode, Integer> indexes,MethodNode method) {
            super(Opcodes.ASM9);this.indexes=indexes;
            // A branch can select an already-produced local. Preserve the read's control path at merges.
            guardedCopies=!method.tryCatchBlocks.isEmpty() || indexes.keySet().stream().anyMatch(i -> i instanceof JumpInsnNode jump && jump.getOpcode()!=Opcodes.GOTO || i instanceof TableSwitchInsnNode || i instanceof LookupSwitchInsnNode);
            for(var entry:indexes.entrySet())if(entry.getKey() instanceof JumpInsnNode jump && indexes.get(jump.label)<entry.getValue())loopAssignments.set(indexes.get(jump.label),entry.getValue()+1);
        }
        private FlowValue result(AbstractInsnNode instruction, BasicValue value) {
            return value == null ? null : new FlowValue(value, Set.of(new Producer(indexes.get(instruction))));
        }
        @Override public FlowValue newValue(Type type) {
            BasicValue value = basic.newValue(type);
            return value == null ? null : new FlowValue(value, Set.of(new UnknownOrigin("uninitialized or exception value")));
        }
        @Override public FlowValue newExceptionValue(TryCatchBlockNode handler,Frame<FlowValue> frame,Type type) {
            return new FlowValue(basic.newValue(type),Set.of(new ExceptionOrigin(indexes.get(handler.handler))));
        }
        @Override public FlowValue newParameterValue(boolean instance, int local, Type type) {
            return new FlowValue(basic.newValue(type), Set.of(new Parameter(local)));
        }
        @Override public FlowValue newOperation(AbstractInsnNode instruction) throws AnalyzerException {
            return result(instruction, basic.newOperation(instruction));
        }
        @Override public FlowValue copyOperation(AbstractInsnNode instruction, FlowValue value) {
            int opcode=instruction.getOpcode();return guardedCopies && opcode>=Opcodes.ILOAD && opcode<=Opcodes.ALOAD || opcode>=Opcodes.ISTORE && opcode<=Opcodes.ASTORE && loopAssignments.get(indexes.get(instruction))?result(instruction,value.basic()):value;
        }
        @Override public FlowValue unaryOperation(AbstractInsnNode instruction, FlowValue value) throws AnalyzerException {
            return result(instruction, basic.unaryOperation(instruction, value.basic()));
        }
        @Override public FlowValue binaryOperation(AbstractInsnNode instruction, FlowValue a, FlowValue b) throws AnalyzerException {
            return result(instruction, basic.binaryOperation(instruction, a.basic(), b.basic()));
        }
        @Override public FlowValue ternaryOperation(AbstractInsnNode instruction, FlowValue a, FlowValue b, FlowValue c) throws AnalyzerException {
            return result(instruction, basic.ternaryOperation(instruction, a.basic(), b.basic(), c.basic()));
        }
        @Override public FlowValue naryOperation(AbstractInsnNode instruction, List<? extends FlowValue> values) throws AnalyzerException {
            return result(instruction, basic.naryOperation(instruction, values.stream().map(FlowValue::basic).toList()));
        }
        @Override public void returnOperation(AbstractInsnNode instruction, FlowValue value, FlowValue expected) {}
        @Override public FlowValue merge(FlowValue a, FlowValue b) {
            if (a.equals(b)) return a;
            BasicValue merged = basic.merge(a.basic(), b.basic());
            Set<Origin> origins = new LinkedHashSet<>(a.origins());
            origins.addAll(b.origins());
            boolean limited=origins.remove(new LimitedOrigin());
            if (origins.size() > 64) {
                truncated = true;
                origins=new LinkedHashSet<>(origins.stream().sorted(Comparator.comparingInt(origin -> origin instanceof Parameter p?p.slot():origin instanceof Producer p?p.instruction()+65536:Integer.MAX_VALUE)).limit(64).toList());
                limited=true;
            }
            if(limited)origins.add(new LimitedOrigin());
            return new FlowValue(merged, Collections.unmodifiableSet(origins));
        }
    }
}
