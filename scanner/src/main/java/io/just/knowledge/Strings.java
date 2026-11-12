package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import java.util.*;

/** Finite string content; no target conversion or callback is executed. */
final class Strings implements Model {
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        MethodId api=call.call().target();
        if(call.is("java/lang/String","length","()I") || call.is("java/lang/String","isEmpty","()Z") || call.is("java/lang/String","startsWith","(Ljava/lang/String;)Z")) {
            Atom receiver=call.receiver();
            Atom prefix=call.arguments().isEmpty()?new Literal(""):call.arguments().get(0);
            if(receiver instanceof Literal receiverNull && receiverNull.value()==null || prefix instanceof Literal prefixNull && prefixNull.value()==null)
                return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if(receiver instanceof Literal literal && literal.value() instanceof String text && prefix instanceof Literal p && p.value() instanceof String start) {
                int answer=switch(api.name()){case "length" -> text.length();case "isEmpty" -> text.isEmpty()?1:0;default -> text.startsWith(start)?1:0;};
                return Optional.of(Local.of(Mechanisms.result(new Literal(answer))));
            }
            List<Gap> normal=receiver instanceof Literal || receiver instanceof ObjectValue o && o.exact()?List.of():Mechanisms.unknown(call,"string guard receiver must be nonnull");
            if(!(prefix instanceof Literal || prefix instanceof ObjectValue o && o.exact()))normal=Mechanisms.unknown(call,"string guard prefix must be nonnull");
            return Optional.of(Local.of(new RequireNormal(normal),new Result(Value.of(new Unknown("string guard content is not finite")).requiring(Mechanisms.unknown(call,"string guard requires finite string content")))));
        }
        if(api.owner().equals("java/lang/StringBuilder") && call.receiver() instanceof ObjectValue builder) {
            if(api.name().equals("<init>") && Set.of("()V","(I)V","(Ljava/lang/String;)V").contains(api.descriptor())) {
                Atom initial=new Literal("");List<Gap> normal=List.of();
                if(api.descriptor().equals("(I)V")) {
                    Atom capacity=call.arguments().get(0);
                    if(capacity instanceof Literal l && l.value() instanceof Number n) {if(n.intValue()<0)return Optional.of(Local.of(new Raise("java/lang/NegativeArraySizeException")));}
                    else normal=Mechanisms.unknown(call,"StringBuilder capacity must be nonnegative");
                } else if(api.descriptor().equals("(Ljava/lang/String;)V")) {
                    initial=call.arguments().get(0);
                    if(initial instanceof Literal l && l.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
                    if(!(initial instanceof Literal l && l.value() instanceof String))normal=Mechanisms.unknown(call,"StringBuilder initial string must be nonnull");
                }
                return Optional.of(Local.of(new RequireNormal(normal),new Write(builder,new Content(),Value.of(initial)),new Result(Value.NULL)));
            }
            if(api.name().equals("append") && (Set.of("(Z)Ljava/lang/StringBuilder;","(C)Ljava/lang/StringBuilder;","(I)Ljava/lang/StringBuilder;","(J)Ljava/lang/StringBuilder;","(F)Ljava/lang/StringBuilder;","(D)Ljava/lang/StringBuilder;","(Ljava/lang/String;)Ljava/lang/StringBuilder;").contains(api.descriptor())
                    || api.descriptor().equals("(Ljava/lang/Object;)Ljava/lang/StringBuilder;") && call.arguments().get(0) instanceof Literal)) {
                Value content=bindings.read(builder,new Content());Value output=Value.BOTTOM;
                Optional<String> suffix=text(call.arguments().get(0),api.descriptor().substring(1,2));
                for(Bound part:content.alternatives()) {
                    Atom value=concat(List.of(part.atom(),suffix.<Atom>map(Literal::new).orElse(call.arguments().get(0))));
                    output=output.merge(finite(value,call).value().under(part.path()).requiring(part.gaps()).tracing(part.dependencies()));
                }
                if(output.empty())output=Value.of(new Unknown("StringBuilder content has no producer")).requiring(Mechanisms.unknown(call,"StringBuilder content is unspecified"));
                return Optional.of(Local.of(new RequireNormal(List.of()),new Write(builder,new Content(),output),Mechanisms.result(builder)));
            }
            if(call.is("java/lang/StringBuilder","toString","()Ljava/lang/String;"))return Optional.of(Local.of(new RequireNormal(List.of()),new Result(bindings.read(builder,new Content()))));
        }
        if(call.receiver() instanceof Literal left && left.value() instanceof String value) {
            if(call.is("java/lang/String","concat","(Ljava/lang/String;)Ljava/lang/String;")) {
                Atom other=call.arguments().get(0);
                if(other instanceof Literal l && l.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
                return Optional.of(Local.of(new RequireNormal(other instanceof Literal l && l.value() instanceof String?List.of():Mechanisms.unknown(call,"concat requires a nonnull string")),finite(other instanceof Literal l && l.value() instanceof String right?joined(value,right):new StringPrefix(value,other),call)));
            }
            if((call.is("java/lang/String","equals","(Ljava/lang/Object;)Z") || call.is("java/lang/Object","equals","(Ljava/lang/Object;)Z") && call.call().opcode()==org.objectweb.asm.Opcodes.INVOKEVIRTUAL) && call.arguments().get(0) instanceof Literal right)
                return Optional.of(Local.of(Mechanisms.result(new Literal(value.equals(right.value())?1:0))));
        }
        if(api.owner().equals("<invokedynamic>") && call.call().bootstrap().isPresent()) {
            Bootstrap bootstrap=call.call().bootstrap().get();MethodId factory=bootstrap.factory().target();
            if(!factory.owner().equals("java/lang/invoke/StringConcatFactory"))return Optional.empty();
            List<Atom> pieces=new ArrayList<>();List<ValueType> types=program.signature(api).parameters();
            for(int i=0;i<call.arguments().size();i++)pieces.add(text(call.arguments().get(i),types.get(i).descriptor()).<Atom>map(Literal::new).orElse(call.arguments().get(i)));
            if(factory.name().equals("makeConcat"))return Optional.of(Local.of(finite(concat(pieces),call)));
            if(factory.name().equals("makeConcatWithConstants") && !bootstrap.arguments().isEmpty() && bootstrap.arguments().get(0) instanceof LiteralConstant recipe && recipe.value() instanceof String pattern) {
                List<Atom> ordered=new ArrayList<>();StringBuilder literal=new StringBuilder();int argument=0,constant=1;
                for(int i=0;i<pattern.length();i++) {
                    char ch=pattern.charAt(i);
                    if(ch==1 || ch==2) {
                        if(literal.length()>0){ordered.add(new Literal(literal.toString()));literal.setLength(0);}
                        if(ch==1){if(argument>=pieces.size())return Optional.empty();ordered.add(pieces.get(argument++));}
                        else {if(constant>=bootstrap.arguments().size() || !(bootstrap.arguments().get(constant++) instanceof LiteralConstant c))return Optional.empty();ordered.add(new Literal(String.valueOf(c.value())));}
                    } else literal.append(ch);
                }
                if(literal.length()>0)ordered.add(new Literal(literal.toString()));
                if(argument==pieces.size() && constant==bootstrap.arguments().size())return Optional.of(Local.of(finite(concat(ordered),call)));
            }
        }
        return Optional.empty();
    }
    static Atom concat(List<Atom> pieces) {
        List<Atom> flat=new ArrayList<>();ArrayDeque<Atom> pending=new ArrayDeque<>(pieces);int length=0;
        while(!pending.isEmpty()) {
            Atom piece=pending.removeFirst();
            if(piece instanceof StringPrefix prefix){pending.addFirst(prefix.suffix());pending.addFirst(new Literal(prefix.prefix()));continue;}
            if(piece instanceof StringConcat sequence){for(int i=sequence.pieces().size()-1;i>=0;i--)pending.addFirst(sequence.pieces().get(i));continue;}
            if(piece instanceof Literal literal && literal.value() instanceof String text) {
                length+=text.length();if(length>4096)return new Truncated("finite string length budget (4096)");
                if(!flat.isEmpty() && flat.get(flat.size()-1) instanceof Literal prior && prior.value() instanceof String prefix)flat.set(flat.size()-1,new Literal(prefix+text));
                else if(!text.isEmpty())flat.add(piece);
            } else flat.add(piece);
            if(flat.size()>64)return new Truncated("string operand budget (64)");
        }
        if(flat.isEmpty())return new Literal("");if(flat.size()==1)return flat.get(0);
        if(flat.get(0) instanceof Literal literal && literal.value() instanceof String prefix)
            return new StringPrefix(prefix,flat.size()==2?flat.get(1):new StringConcat(flat.subList(1,flat.size())));
        return new StringConcat(flat);
    }
    /** Derive a raw string constraint only when exactly one operand is unknown. */
    static Optional<InputNeed> input(InputNeed need) {
        if(need.choices().size()!=1 || !(need.choices().get(0) instanceof Literal literal) || !(literal.value() instanceof String name))return Optional.of(need);
        if(need.subject() instanceof StringPrefix prefix) {
            if(!name.startsWith(prefix.prefix()))return Optional.empty();
            return input(new InputNeed(prefix.suffix(),need.slot(),need.kind(),need.descriptor(),List.of(new Literal(name.substring(prefix.prefix().length()))),need.reason()));
        }
        if(!(need.subject() instanceof StringConcat sequence))return Optional.of(need);
        Atom unknown=null;StringBuilder before=new StringBuilder(),after=new StringBuilder();
        for(Atom piece:sequence.pieces()) {
            if(piece instanceof Literal text && text.value() instanceof String value){if(unknown==null)before.append(value);else after.append(value);}
            else if(unknown==null)unknown=piece;else return Optional.of(need);
        }
        if(!name.startsWith(before.toString()) || !name.endsWith(after.toString()) || name.length()<before.length()+after.length())return Optional.empty();
        if(unknown==null)return Optional.of(need);
        return input(new InputNeed(unknown,need.slot(),need.kind(),need.descriptor(),List.of(new Literal(name.substring(before.length(),name.length()-after.length()))),need.reason()));
    }
    private static Atom joined(String a,String b){return a.length()+b.length()>4096?new Truncated("finite string length budget (4096)"):new Literal(a+b);}
    private static Result finite(Atom value,Invocation call){return new Result(Value.of(value).requiring(value instanceof Truncated t?List.of(Mechanisms.gap(call,GapKind.BUDGET,t.reason())):List.of()));}
    private static Optional<String> text(Atom atom,String descriptor) {
        if(!(atom instanceof Literal literal))return Optional.empty();Object value=literal.value();
        if(descriptor.equals("C") && value instanceof Number number)return Optional.of(String.valueOf((char)number.intValue()));
        if(descriptor.equals("Z") && value instanceof Number number)return Optional.of(number.intValue()==0?"false":"true");
        return Optional.of(String.valueOf(value));
    }
}
