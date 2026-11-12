package io.just.analysis;

import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import java.util.*;

/** Recognizes a bounded iteration plan from facts. The caller owns execution and subscriptions. */
final class Iterations {
    record Loop(int start,int end,int count,OptionalInt iterator,int counterInitial,int counterAdvance,boolean prefix) {
        Loop(int start,int end,int count,int iterator){this(start,end,count,OptionalInt.of(iterator),-1,-1,false);}
        Loop(int start,int end,int count,int iterator,int initial,int advance){this(start,end,count,OptionalInt.of(iterator),initial,advance,false);}
        Loop asPrefix(){return new Loop(start,end,count,iterator,counterInitial,counterAdvance,true);}
    }
    static Optional<Loop> arrayPlan(Facts facts,int factory,ArrayValue array,List<Loop> existing) {
        if(array.extent()!=ArrayExtent.EXACT || array.elements().size()>64)return Optional.empty();
        Map<Integer,Action> actions=new HashMap<>();for(Action action:facts.actions())actions.put(action.site().instruction(),action);
        for(Edge edge:facts.cfg()) {
            if(edge.exceptional() || edge.to()<=factory || edge.to()>=edge.from() || existing.stream().anyMatch(l -> l.start()<=edge.to() && edge.to()<=l.end()))continue;
            List<Action> body=facts.actions().stream().filter(a -> edge.to()<=a.site().instruction() && a.site().instruction()<=edge.from()).toList();
            for(Action action:body)if(action instanceof Branch header && header.opcode()==org.objectweb.asm.Opcodes.IF_ICMPGE && header.inputs().size()==2) {
                if(header.inputs().get(1).origins().stream().noneMatch(o -> o instanceof Producer p && actions.get(p.instruction()) instanceof Compute c && c.opcode()==org.objectweb.asm.Opcodes.ARRAYLENGTH && c.inputs().get(0).origins().equals(Set.of(new Producer(factory)))))continue;
                int initial=-1,advance=-1;boolean supported=true;
                for(Origin origin:header.inputs().get(0).origins()) {
                    if(!(origin instanceof Producer p)){supported=false;break;}
                    Action source=actions.get(p.instruction());
                    if(source instanceof Constant c && c.value() instanceof LiteralConstant l && Integer.valueOf(0).equals(l.value()) && p.instruction()<edge.to())initial=p.instruction();
                    else if(source instanceof Compute c && c.opcode()==org.objectweb.asm.Opcodes.IINC && c.operand()==1 && p.instruction()<=edge.from())advance=p.instruction();
                    else supported=false;
                }
                if(!supported || initial<0 || advance<0)continue;
                return Optional.of(new Loop(edge.to(),edge.from(),array.elements().size(),array.id(),initial,advance));
            }
        }
        return Optional.empty();
    }
    static Optional<Value> counter(Sources sources,Optional<Loop> loop,int iteration) {
        if(loop.isEmpty() || loop.get().counterInitial()<0)return Optional.empty();Loop plan=loop.get();
        return sources.origins().equals(Set.of(new Producer(plan.counterInitial()),new Producer(plan.counterAdvance())))?Optional.of(Value.of(new Literal(iteration))):Optional.empty();
    }
    static Optional<Loop> counterPlan(Facts facts,Branch header,Value upper,int budget,List<Loop> existing) {
        int at=header.site().instruction();
        if(header.opcode()!=org.objectweb.asm.Opcodes.IF_ICMPGE || header.inputs().size()!=2 || existing.stream().anyMatch(loop -> loop.start()<=at && at<=loop.end()))return Optional.empty();
        Map<Integer,Action> actions=new HashMap<>();for(Action action:facts.actions())actions.put(action.site().instruction(),action);
        for(Edge edge:facts.cfg()) {
            if(edge.exceptional() || edge.to()>=edge.from() || at<edge.to() || at>edge.from())continue;
            if(facts.handlers().stream().anyMatch(handler -> edge.to()<=handler.target() && handler.target()<=edge.from()))continue;
            if(facts.cfg().stream().anyMatch(other -> !other.exceptional() && other.to()<=other.from() && edge.to()<=other.to() && other.from()<=edge.from() && !other.equals(edge)))continue;
            int initial=-1,advance=-1;boolean valid=true;
            for(Origin origin:header.inputs().get(0).origins()) {
                if(!(origin instanceof Producer producer)){valid=false;break;}
                Action source=actions.get(producer.instruction());
                if(source instanceof Constant c && c.value() instanceof LiteralConstant literal && Integer.valueOf(0).equals(literal.value()) && producer.instruction()<edge.to() && initial<0)initial=producer.instruction();
                else if(source instanceof Compute c && c.opcode()==org.objectweb.asm.Opcodes.IINC && c.operand()==1 && edge.to()<=producer.instruction() && producer.instruction()<=edge.from() && advance<0)advance=producer.instruction();
                else valid=false;
            }
            if(!valid || initial<0 || advance<0)continue;
            Map<Integer,List<Integer>> outgoing=new HashMap<>();
            for(Edge path:facts.cfg())if(!path.exceptional() && edge.to()<=path.to() && path.to()<=edge.from())outgoing.computeIfAbsent(path.from(),key -> new ArrayList<>()).add(path.to());
            Set<Integer> reached=new HashSet<>();ArrayDeque<Integer> pending=new ArrayDeque<>(List.of(edge.to()));
            while(!pending.isEmpty()) {
                int next=pending.removeFirst();if(next==advance || !reached.add(next))continue;
                pending.addAll(outgoing.getOrDefault(next,List.of()));
            }
            if(reached.contains(edge.from()))continue;
            boolean invariant=header.inputs().get(1).origins().stream().noneMatch(origin -> origin instanceof Producer p && edge.to()<=p.instruction() && p.instruction()<=edge.from() && !(actions.get(p.instruction()) instanceof Constant));
            Set<Integer> bounds=new LinkedHashSet<>();boolean known=invariant;
            for(Bound bound:upper.alternatives())if(bound.atom() instanceof Literal literal && literal.value() instanceof Integer value)bounds.add(Math.max(0,value));else known=false;
            int count=known && bounds.size()==1?Math.min(budget,bounds.iterator().next()):budget;
            return Optional.of(new Loop(edge.to(),edge.from(),count,OptionalInt.empty(),initial,advance,!known || bounds.size()!=1 || bounds.iterator().next()>budget));
        }
        return Optional.empty();
    }
    static Optional<Loop> plan(Facts facts,int factory,int object,int count,List<Loop> existing) {
        Map<Integer,Action> producers=new HashMap<>();for(Action action:facts.actions())producers.put(action.site().instruction(),action);
        for(Edge edge:facts.cfg()) {
            if(edge.exceptional() || edge.to()<=factory || edge.to()>=edge.from() || existing.stream().anyMatch(l -> l.start()<=edge.to() && edge.to()<=l.end()))continue;
            List<Action> body=facts.actions().stream().filter(a -> edge.to()<=a.site().instruction() && a.site().instruction()<=edge.from()).toList();
            List<Call> tests=body.stream().filter(a -> a instanceof Call c && c.target().owner().equals("java/util/Iterator") && c.target().name().equals("hasNext")).map(a -> (Call)a).toList();
            long next=body.stream().filter(a -> a instanceof Call c && c.target().owner().equals("java/util/Iterator") && c.target().name().equals("next")).count();
            if(tests.size()!=1 || next!=1 || !tests.get(0).receiver().origins().equals(Set.of(new Producer(factory))))continue;
            return Optional.of(new Loop(edge.to(),edge.from(),count,object));
        }
        return Optional.empty();
    }
    static Optional<Value> cursor(Slot slot,ObjectValue object,Optional<Loop> loop,int iteration,boolean unknownLoop,Site site) {
        if(!(slot instanceof Cursor))return Optional.empty();
        if(loop.filter(l -> l.iterator().isPresent() && l.iterator().getAsInt()==object.id()).isPresent())return Optional.of(Value.of(new Literal(iteration)));
        if(unknownLoop)return Optional.of(Value.of(new Unknown("iteration position is not established")).requiring(List.of(new Gap(GapKind.CONTROL_CONDITION,site,"iteration order is not established"))));
        return Optional.empty();
    }
}
