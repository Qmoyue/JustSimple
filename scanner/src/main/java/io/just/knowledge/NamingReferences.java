package io.just.knowledge;

import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import java.util.*;

/** Standard Reference fields and its ordered address vector, using the existing heap service. */
final class NamingReferences implements Model {
    private static final String REF="javax/naming/Reference",ADDR="javax/naming/RefAddr",STRING="javax/naming/StringRefAddr";
    private static Field field(String owner,String name,String descriptor){return new Field(new FieldId(owner,name,descriptor));}
    private static final Field ADDRESSES=field(REF,"addrs","Ljava/util/Vector;");
    private static final Field TYPE=field(ADDR,"addrType","Ljava/lang/String;");
    private static final class SearchBudget {int remaining=256;boolean spend(){return remaining-->0;}}
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        MethodId api=call.call().target();
        if(!Set.of(REF,ADDR,STRING).contains(api.owner()) || !(call.receiver() instanceof ObjectValue receiver))return Optional.empty();
        Query<Method> method=api.name().equals("<init>")?program.declaration(api):program.lookup(new MethodId(receiver.type(),api.name(),api.descriptor()));
        if(method.value().flatMap(m -> program.type(m.id().owner())).filter(c -> c.role()==Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        String owner=method.value().orElseThrow().id().owner();
        if(!Set.of(REF,ADDR,STRING).contains(owner))return Optional.empty();
        if(api.name().equals("<init>")) {
            if(api.owner().equals(ADDR) && api.descriptor().equals("(Ljava/lang/String;)V"))
                return Optional.of(Local.of(new RequireNormal(List.of()),new Write(receiver,TYPE,Value.of(call.arguments().get(0))),new Result(Value.NULL)));
            if(api.owner().equals(STRING) && api.descriptor().equals("(Ljava/lang/String;Ljava/lang/String;)V"))
                return Optional.of(Local.of(new RequireNormal(List.of()),new Write(receiver,TYPE,Value.of(call.arguments().get(0))),
                        new Write(receiver,field(STRING,"contents","Ljava/lang/String;"),Value.of(call.arguments().get(1))),new Result(Value.NULL)));
            if(api.owner().equals(REF) && Set.of("(Ljava/lang/String;)V","(Ljava/lang/String;Ljavax/naming/RefAddr;)V","(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V","(Ljava/lang/String;Ljavax/naming/RefAddr;Ljava/lang/String;Ljava/lang/String;)V").contains(api.descriptor())) {
                boolean address=api.descriptor().contains("Ljavax/naming/RefAddr;");
                int factory=address?2:1;List<Atom> args=call.arguments();
                ObjectValue vector=new ObjectValue(call.result().id(),"java/util/Vector",true,"Reference address vector",true);
                List<Effect> effects=new ArrayList<>(List.of(new RequireNormal(List.of()),new Write(receiver,field(REF,"className","Ljava/lang/String;"),Value.of(args.get(0))),
                        new Write(receiver,field(REF,"classFactory","Ljava/lang/String;"),Value.of(args.size()>factory?args.get(factory):new Literal(null))),
                        new Write(receiver,field(REF,"classFactoryLocation","Ljava/lang/String;"),Value.of(args.size()>factory+1?args.get(factory+1):new Literal(null))),
                        new Write(receiver,ADDRESSES,Value.of(vector)),new Write(vector,new Length(),Value.of(new Literal(address?1:0)))));
                if(address)effects.add(new Write(vector,new Index(0),Value.of(args.get(1))));
                effects.add(new Result(Value.NULL));return Optional.of(new Local(effects));
            }
            return Optional.empty();
        }
        if(api.name().equals("getType") && api.descriptor().equals("()Ljava/lang/String;") && owner.equals(ADDR))return Optional.of(read(call,bindings,receiver,TYPE,method));
        if(api.name().equals("getContent") && api.descriptor().equals("()Ljava/lang/Object;") && owner.equals(STRING))return Optional.of(read(call,bindings,receiver,field(STRING,"contents","Ljava/lang/String;"),method));
        if(!owner.equals(REF))return Optional.empty();
        if(api.descriptor().equals("()Ljava/lang/String;")) {
            String name=switch(api.name()){case "getClassName" -> "className";case "getFactoryClassName" -> "classFactory";case "getFactoryClassLocation" -> "classFactoryLocation";default -> "";};
            if(!name.isEmpty())return Optional.of(read(call,bindings,receiver,field(REF,name,"Ljava/lang/String;"),method));
        }
        if(!Set.of("add","remove","clear","get","getAll","size").contains(api.name()))return Optional.empty();
        List<Effect> effects=new ArrayList<>();
        for(Bound address:bindings.read(receiver,ADDRESSES).under(call.path()).alternatives()) {
            Local operation=address.atom() instanceof ObjectValue vector?addresses(call,bindings,program,vector):unknown(call,"Reference address vector is unspecified",GapKind.INPUT_BINDING);
            effects.add(new Conditional(address.path(),address.gaps(),address.dependencies(),operation));
        }
        return Optional.of(effects.isEmpty()?unknown(call,"Reference data has no current producer",GapKind.INPUT_BINDING):new Local(effects));
    }
    private Local read(Invocation call,Bindings bindings,ObjectValue receiver,Slot slot,Query<Method> method){
        Value value=bindings.read(receiver,slot);
        if(value.empty())return Local.of(new Need(new InputNeed(receiver,Optional.of(slot),NeedKind.VALUE,"Ljava/lang/String;",List.of(),"Reference field at this getter")),
                new Result(Value.of(new Symbolic("java/lang/String","Reference field",receiver.source().map(s -> s.at(slot)))).requiring(Mechanisms.unknown(call,"Reference field has no current producer"))));
        return Local.of(new RequireNormal(List.of()),new Result(value.requiring(Mechanisms.queryGaps(call,method))));
    }
    private Local addresses(Invocation call,Bindings bindings,Program program,ObjectValue vector) {
        MethodId api=call.call().target();
        if(call.is(REF,"clear","()V"))return Local.of(new RequireNormal(List.of()),new Write(vector,new Length(),Value.of(new Literal(0))),new Result(Value.NULL));
        if(call.is(REF,"getAll","()Ljava/util/Enumeration;"))return unknown(call,"Reference address Enumeration is not modeled",GapKind.UNSUPPORTED);
        if(call.is(REF,"add","(ILjavax/naming/RefAddr;)V") || call.is(REF,"remove","(I)Ljava/lang/Object;")) {
            Gap gap=Mechanisms.gap(call,GapKind.UNSUPPORTED,"indexed Reference mutation invalidates address ordering");
            Value changed=Value.of(new Unknown(gap.detail())).requiring(List.of(gap));
            return Local.of(new RequireNormal(List.of(gap)),new Write(vector,new Length(),changed),new Write(vector,new Wildcard(),changed),new Result(api.name().equals("add")?Value.NULL:changed));
        }
        List<Effect> effects=new ArrayList<>();
        for(Bound length:bindings.read(vector,new Length()).under(call.path()).alternatives()) {
            Local operation;
            if(!(length.atom() instanceof Literal l && l.value() instanceof Integer size && size>=0)) {
                operation=unknown(call,"Reference address count/order is unresolved",length.gaps().stream().anyMatch(g -> g.kind()==GapKind.UNSUPPORTED)?GapKind.UNSUPPORTED:GapKind.INPUT_BINDING);
                if(call.is(REF,"add","(Ljavax/naming/RefAddr;)V")) {
                    Value changed=Value.of(new Unknown("Reference append position is unspecified")).requiring(Mechanisms.unknown(call,"Reference append position is unspecified"));
                    operation=Local.of(new RequireNormal(changed.alternatives().iterator().next().gaps()),new Write(vector,new Length(),changed),new Write(vector,new Wildcard(),Value.of(call.arguments().get(0))),new Result(Value.NULL));
                }
            } else if(call.is(REF,"size","()I"))operation=Local.of(new RequireNormal(List.of()),Mechanisms.result(new Literal(size)));
            else if(call.is(REF,"add","(Ljavax/naming/RefAddr;)V"))operation=Local.of(new RequireNormal(List.of()),new Write(vector,new Index(size),Value.of(call.arguments().get(0))),new Write(vector,new Length(),Value.of(new Literal(size+1))),new Result(Value.NULL));
            else if(call.is(REF,"get","(I)Ljavax/naming/RefAddr;")) {
                Atom index=call.arguments().get(0);
                if(index instanceof Literal literal && literal.value() instanceof Integer position)
                    operation=position<0 || position>=size?Local.of(new Raise("java/lang/ArrayIndexOutOfBoundsException")):Local.of(new RequireNormal(List.of()),new Result(bindings.read(vector,new Index(position))));
                else operation=unknown(call,"Reference index is unspecified",GapKind.INPUT_BINDING);
            } else if(call.is(REF,"get","(Ljava/lang/String;)Ljavax/naming/RefAddr;"))operation=size>64?unknown(call,"Reference address search count budget (64)",GapKind.BUDGET):find(call,bindings,program,vector,size,0,new SearchBudget());
            else operation=unknown(call,"unsupported Reference operation: "+api,GapKind.UNSUPPORTED);
            effects.add(new Conditional(length.path(),length.gaps(),length.dependencies(),operation));
        }
        return effects.isEmpty()?unknown(call,"Reference data has no current producer",GapKind.INPUT_BINDING):new Local(effects);
    }
    private Local find(Invocation call,Bindings bindings,Program program,ObjectValue vector,int size,int index,SearchBudget budget) {
        if(!budget.spend())return unknown(call,"Reference address search alternatives budget (256)",GapKind.BUDGET);
        if(index==size)return Local.of(new RequireNormal(List.of()),new Result(Value.NULL));
        List<Effect> effects=new ArrayList<>();
        for(Bound address:bindings.read(vector,new Index(index)).under(call.path()).alternatives()) {
            if(!budget.spend()){effects.addAll(unknown(call,"Reference address search alternatives budget (256)",GapKind.BUDGET).effects());break;}
            Local selected;
            if(address.atom() instanceof Literal l && l.value()==null)selected=Local.of(new Raise("java/lang/NullPointerException"));
            else if(address.atom() instanceof ObjectValue object) {
                Query<Method> getter=program.lookup(new MethodId(object.type(),"getType","()Ljava/lang/String;"));
                if(getter.value().filter(m -> m.id().owner().equals(ADDR)).flatMap(m -> program.type(m.id().owner())).filter(c -> c.role()==Inputs.Role.PLATFORM).isEmpty())
                    selected=unknown(call,"Reference address type override is not modeled",GapKind.UNSUPPORTED);
                else {
                    List<Effect> choices=new ArrayList<>();
                    for(Bound type:bindings.read(object,TYPE).under(address.path()).alternatives()) {
                        if(!budget.spend()){choices.addAll(unknown(call,"Reference address search alternatives budget (256)",GapKind.BUDGET).effects());break;}
                        Local match;Atom requested=call.arguments().get(0);
                        if(type.atom() instanceof Literal t && t.value()==null || requested instanceof Literal q && q.value()==null)match=Local.of(new Raise("java/lang/NullPointerException"));
                        else if(type.atom() instanceof Literal t && t.value() instanceof String name && requested instanceof Literal q && q.value() instanceof String target)
                            match=name.equals(target)?Local.of(new RequireNormal(List.of()),Mechanisms.result(object)):find(call,bindings,program,vector,size,index+1,budget);
                        else {
                            Gap pending=Mechanisms.gap(call,GapKind.INPUT_BINDING,"earlier Reference address type comparisons must be resolved");
                            match=Local.of(new Conditional(call.path(),List.of(pending),Set.of(),Local.of(new RequireNormal(List.of()),Mechanisms.result(object))),
                                    new Conditional(call.path(),List.of(pending),Set.of(),find(call,bindings,program,vector,size,index+1,budget)));
                        }
                        List<Gap> gaps=new ArrayList<>(type.gaps());gaps.addAll(Mechanisms.queryGaps(call,getter));
                        choices.add(new Conditional(type.path(),List.copyOf(gaps),type.dependencies(),match));
                    }
                    selected=choices.isEmpty()?unknown(call,"Reference data has no current producer",GapKind.INPUT_BINDING):new Local(choices);
                }
            } else selected=unknown(call,"Reference address identity is unspecified",GapKind.INPUT_BINDING);
            effects.add(new Conditional(address.path(),address.gaps(),address.dependencies(),selected));
        }
        return effects.isEmpty()?unknown(call,"Reference data has no current producer",GapKind.INPUT_BINDING):new Local(effects);
    }
    private Local unknown(Invocation call,String reason,GapKind kind) {
        List<Gap> gaps=List.of(Mechanisms.gap(call,kind,reason));
        return Local.of(new RequireNormal(gaps),new Result(Value.of(new Unknown(reason)).requiring(gaps)),new Observe(Kind.DYNAMIC_CALL,reason,List.of(call.call().site()),gaps));
    }
}
