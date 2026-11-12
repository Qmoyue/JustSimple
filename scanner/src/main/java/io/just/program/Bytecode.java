package io.just.program;

import io.just.program.Program.*;
import org.objectweb.asm.tree.*;
import java.util.*;
import java.util.concurrent.CancellationException;

/** Read-only ASM-normalized classfile instructions, using the same indexes and body cache as Program.facts. */
public final class Bytecode {
    private Bytecode() {}
    public record Instruction(Site site, int opcode, String mnemonic, Map<String,Object> operands) {
        public Instruction { operands = Collections.unmodifiableMap(new LinkedHashMap<>(operands)); }
    }
    public record Body(Method method, int maxStack, int maxLocals, int total, int offset, int next,
                       List<Instruction> instructions, List<Handler> handlers) {
        public Body { instructions = List.copyOf(instructions); handlers = List.copyOf(handlers); }
    }
    private static final String[] OPCODES = ("NOP ACONST_NULL ICONST_M1 ICONST_0 ICONST_1 ICONST_2 ICONST_3 ICONST_4 ICONST_5 "
            + "LCONST_0 LCONST_1 FCONST_0 FCONST_1 FCONST_2 DCONST_0 DCONST_1 BIPUSH SIPUSH LDC LDC_W LDC2_W "
            + "ILOAD LLOAD FLOAD DLOAD ALOAD ILOAD_0 ILOAD_1 ILOAD_2 ILOAD_3 LLOAD_0 LLOAD_1 LLOAD_2 LLOAD_3 "
            + "FLOAD_0 FLOAD_1 FLOAD_2 FLOAD_3 DLOAD_0 DLOAD_1 DLOAD_2 DLOAD_3 ALOAD_0 ALOAD_1 ALOAD_2 ALOAD_3 "
            + "IALOAD LALOAD FALOAD DALOAD AALOAD BALOAD CALOAD SALOAD ISTORE LSTORE FSTORE DSTORE ASTORE "
            + "ISTORE_0 ISTORE_1 ISTORE_2 ISTORE_3 LSTORE_0 LSTORE_1 LSTORE_2 LSTORE_3 FSTORE_0 FSTORE_1 FSTORE_2 FSTORE_3 "
            + "DSTORE_0 DSTORE_1 DSTORE_2 DSTORE_3 ASTORE_0 ASTORE_1 ASTORE_2 ASTORE_3 IASTORE LASTORE FASTORE DASTORE AASTORE BASTORE CASTORE SASTORE "
            + "POP POP2 DUP DUP_X1 DUP_X2 DUP2 DUP2_X1 DUP2_X2 SWAP IADD LADD FADD DADD ISUB LSUB FSUB DSUB "
            + "IMUL LMUL FMUL DMUL IDIV LDIV FDIV DDIV IREM LREM FREM DREM INEG LNEG FNEG DNEG ISHL LSHL ISHR LSHR IUSHR LUSHR "
            + "IAND LAND IOR LOR IXOR LXOR IINC I2L I2F I2D L2I L2F L2D F2I F2L F2D D2I D2L D2F I2B I2C I2S "
            + "LCMP FCMPL FCMPG DCMPL DCMPG IFEQ IFNE IFLT IFGE IFGT IFLE IF_ICMPEQ IF_ICMPNE IF_ICMPLT IF_ICMPGE IF_ICMPGT IF_ICMPLE "
            + "IF_ACMPEQ IF_ACMPNE GOTO JSR RET TABLESWITCH LOOKUPSWITCH IRETURN LRETURN FRETURN DRETURN ARETURN RETURN "
            + "GETSTATIC PUTSTATIC GETFIELD PUTFIELD INVOKEVIRTUAL INVOKESPECIAL INVOKESTATIC INVOKEINTERFACE INVOKEDYNAMIC "
            + "NEW NEWARRAY ANEWARRAY ARRAYLENGTH ATHROW CHECKCAST INSTANCEOF MONITORENTER MONITOREXIT WIDE MULTIANEWARRAY IFNULL IFNONNULL GOTO_W JSR_W").split(" ");

    public static Query<Body> query(Program program, MethodId id, int offset, int limit) {
        if (offset < 0 || limit < 1 || limit > 1000) throw new IllegalArgumentException("bytecode page: offset >= 0, limit 1..1000");
        Query<Method> declaration = program.declaration(id);
        if (declaration.value().isEmpty()) return new Query<>(Optional.empty(), declaration.pending());
        Method method = declaration.value().orElseThrow();
        MethodNode code = program.code(method.id());
        if (offset > code.instructions.size()) throw new IllegalArgumentException("offset exceeds method size");
        int end = (int)Math.min(code.instructions.size(), (long)offset + limit), line = -1;
        List<Instruction> instructions = new ArrayList<>();
        String source = program.classData(id.owner(), id.loader()).orElseThrow().source();
        for (int i = 0; i < end; i++) {
            if (Thread.currentThread().isInterrupted()) throw new CancellationException("bytecode query interrupted");
            AbstractInsnNode at = code.instructions.get(i);
            if (at instanceof LineNumberNode number) line = number.line;
            if (i >= offset) instructions.add(new Instruction(new Site(method.id(), i, line, source), at.getOpcode(), name(at), operands(at, code.instructions)));
        }
        List<Handler> handlers = code.tryCatchBlocks.stream().map(h -> new Handler(code.instructions.indexOf(h.start),
                code.instructions.indexOf(h.end), code.instructions.indexOf(h.handler), h.type)).toList();
        return new Query<>(Optional.of(new Body(method, code.maxStack, code.maxLocals, code.instructions.size(), offset,
                end < code.instructions.size() ? end : -1, instructions, handlers)), declaration.pending());
    }

    private static String name(AbstractInsnNode at) {
        if (at instanceof LabelNode) return "LABEL";
        if (at instanceof LineNumberNode) return "LINE";
        return at.getOpcode() >= 0 ? OPCODES[at.getOpcode()] : "FRAME";
    }
    private static Map<String,Object> operands(AbstractInsnNode at, InsnList code) {
        Map<String,Object> value = new LinkedHashMap<>();
        if (at instanceof VarInsnNode n) value.put("slot", n.var);
        else if (at instanceof IntInsnNode n) value.put("operand", n.operand);
        else if (at instanceof TypeInsnNode n) value.put("type", n.desc);
        else if (at instanceof FieldInsnNode n) { value.put("owner", n.owner); value.put("name", n.name); value.put("descriptor", n.desc); }
        else if (at instanceof MethodInsnNode n) { value.put("owner", n.owner); value.put("name", n.name); value.put("descriptor", n.desc); value.put("interfaceOwner", n.itf); }
        else if (at instanceof InvokeDynamicInsnNode n) { value.put("name", n.name); value.put("descriptor", n.desc); value.put("bootstrap", MethodFlow.constant(n.bsm)); value.put("arguments", Arrays.stream(n.bsmArgs).map(MethodFlow::constant).toList()); }
        else if (at instanceof JumpInsnNode n) value.put("target", code.indexOf(n.label));
        else if (at instanceof LdcInsnNode n) value.put("constant", MethodFlow.constant(n.cst));
        else if (at instanceof IincInsnNode n) { value.put("slot", n.var); value.put("increment", n.incr); }
        else if (at instanceof TableSwitchInsnNode n) { value.put("minimum", n.min); value.put("maximum", n.max); value.put("default", code.indexOf(n.dflt)); value.put("targets", n.labels.stream().map(code::indexOf).toList()); }
        else if (at instanceof LookupSwitchInsnNode n) { value.put("keys", List.copyOf(n.keys)); value.put("default", code.indexOf(n.dflt)); value.put("targets", n.labels.stream().map(code::indexOf).toList()); }
        else if (at instanceof MultiANewArrayInsnNode n) { value.put("descriptor", n.desc); value.put("dimensions", n.dims); }
        else if (at instanceof LineNumberNode n) { value.put("line", n.line); value.put("start", code.indexOf(n.start)); }
        return value;
    }
}
