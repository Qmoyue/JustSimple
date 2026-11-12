package io.just.knowledge;

import io.just.input.Inputs;
import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import org.objectweb.asm.Opcodes;
import java.util.*;

/** Conditional local Reference factory branch. Providers, builders and remote loading stay unresolved. */
final class NamingFactories implements Model {
    private static final String DESCRIPTOR="(Ljava/lang/Object;Ljavax/naming/Name;Ljavax/naming/Context;Ljava/util/Hashtable;)Ljava/lang/Object;";
    private static final Field FACTORY=new Field(new FieldId("javax/naming/Reference","classFactory","Ljava/lang/String;"));
    private final JdkStructures structures;
    NamingFactories(JdkStructures structures){this.structures=structures;}
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        if(!call.is("javax/naming/spi/NamingManager","getObjectInstance",DESCRIPTOR))return Optional.empty();
        Query<Method> api=program.declaration(call.call().target());
        if(api.value().flatMap(m -> program.type(m.id().owner())).filter(c -> c.role()==Inputs.Role.PLATFORM).isEmpty())return Optional.empty();
        List<Gap> required=new ArrayList<>(Mechanisms.queryGaps(call,api));
        JdkStructures.Witness shape=structures.namingFactory();
        required.addAll(Mechanisms.queryGaps(call,new Query<>(Optional.empty(),shape.pending())));
        if(shape.sites().isEmpty())return Optional.of(unresolved(call,"selected JDK local Reference factory path is not verified",required,required.isEmpty()?GapKind.UNSUPPORTED:required.get(0).kind()));
        Atom input=call.arguments().get(0);
        if(!(input instanceof ObjectValue reference))return Optional.of(unresolved(call,"local factory selection requires the actual Reference",required,GapKind.INPUT_BINDING));
        Query<Boolean> referenceType=program.assignable(reference.type(),"javax/naming/Reference");required.addAll(Mechanisms.queryGaps(call,referenceType));
        if(!referenceType.value().equals(Optional.of(true)))return Optional.of(unresolved(call,"Referenceable/provider result has no verified Reference binding",required,GapKind.UNSUPPORTED));
        Query<Method> getter=program.lookup(new MethodId(reference.type(),"getFactoryClassName","()Ljava/lang/String;"));required.addAll(Mechanisms.queryGaps(call,getter));
        if(getter.value().isEmpty())return Optional.of(unresolved(call,"Reference factory-name getter is unavailable",required,GapKind.MISSING_DEPENDENCY));
        Value names;
        if(getter.value().get().id().owner().equals("javax/naming/Reference"))names=bindings.read(reference,FACTORY);
        else {
            names=bindings.read(call.result(),new FactoryName());
            if(names.empty())return Optional.of(Local.of(new Store(call.result(),new FactoryName(),Local.of(new Dispatch(getter.value().get().id(),reference,List.of(),Kind.DYNAMIC_CALL,Evidence.PROVEN,List.of(call.call().site()),Mechanisms.queryGaps(call,getter),ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT))),new Evaluate(call)));
        }
        required.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"local JNDI Reference branch requires no overriding ObjectFactoryBuilder"));
        required.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"the selected class loader must resolve the named factory to this local class"));
        required.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"selected JDK object-factory filter and access policy must permit this factory"));
        List<Site> witnesses=new ArrayList<>(List.of(call.call().site()));witnesses.addAll(shape.sites());
        List<Effect> choices=new ArrayList<>();
        for(Bound name:names.under(call.path()).alternatives()) {
            List<Gap> gaps=new ArrayList<>(required);gaps.addAll(name.gaps());Local selected;
            if(name.atom() instanceof Literal l && l.value() instanceof String factory)
                selected=local(call,bindings,program,factory.replace('.','/'),witnesses);
            else {
                boolean absent=name.atom() instanceof Literal l && l.value()==null;
                selected=unresolved(call,absent?"Reference has no named factory; URL/provider selection is not modeled":"factory name is unspecified",gaps,absent?GapKind.UNSUPPORTED:GapKind.INPUT_BINDING);
                if(!(name.atom() instanceof Literal)) {
                    List<Effect> pending=new ArrayList<>();pending.add(new Need(new InputNeed(name.atom(),Optional.empty(),NeedKind.CLASS_NAME,"Ljava/lang/String;",List.of(),"name of the local Reference factory")));
                    pending.addAll(selected.effects());selected=new Local(pending);
                }
            }
            choices.add(new Conditional(name.path(),List.copyOf(gaps),name.dependencies(),selected));
        }
        return Optional.of(choices.isEmpty()?unresolved(call,"Reference factory field has no current producer",required,GapKind.INPUT_BINDING):new Local(choices));
    }
    private Local local(Invocation call,Bindings bindings,Program program,String factory,List<Site> witnesses) {
        Query<Method> constructor=program.constructor(factory,List.of(),true);
        List<Gap> gaps=new ArrayList<>(Mechanisms.queryGaps(call,constructor));
        Optional<ClassInfo> type=program.type(factory);
        if(type.isEmpty())return unresolved(call,"named local factory class is unavailable; remote locations are data only",gaps,GapKind.MISSING_DEPENDENCY);
        if((type.get().access() & (Opcodes.ACC_ABSTRACT|Opcodes.ACC_INTERFACE))!=0)return Local.of(new Raise("java/lang/InstantiationException"));
        if(constructor.value().isEmpty())return constructor.absent()?Local.of(new Raise("java/lang/InstantiationException")):unresolved(call,"factory constructor is unresolved",gaps,GapKind.MISSING_DEPENDENCY);
        if(!constructor.value().get().isPublic() || (type.get().access() & Opcodes.ACC_PUBLIC)==0)return Local.of(new Raise("java/lang/IllegalAccessException"));
        Query<Boolean> compatible=program.assignable(factory,"javax/naming/spi/ObjectFactory");gaps.addAll(Mechanisms.queryGaps(call,compatible));
        Value instances=bindings.read(call.result(),new Content());
        if(instances.empty()) {
            Local create=Local.of(new Construct(constructor.value().get().id(),List.of(),Kind.DYNAMIC_CALL,witnesses,List.copyOf(gaps),ExceptionFlow.DIRECT));
            return Local.of(new Store(call.result(),new Content(),create),new Evaluate(call));
        }
        List<Effect> effects=new ArrayList<>();
        for(Bound instance:instances.under(call.path()).alternatives()) {
            if(!(instance.atom() instanceof ObjectValue object) || !object.type().equals(factory))continue;
            Local invoke;
            if(compatible.value().equals(Optional.of(false)))invoke=Local.of(new Raise("java/lang/ClassCastException"));
            else {
                Query<Method> implementation=program.lookup(new MethodId(factory,"getObjectInstance",DESCRIPTOR));
                List<Gap> pending=new ArrayList<>(gaps);pending.addAll(instance.gaps());pending.addAll(Mechanisms.queryGaps(call,implementation));
                if(implementation.value().isEmpty())invoke=unresolved(call,"local ObjectFactory implementation is unavailable",pending,GapKind.UNSUPPORTED);
                else invoke=Local.of(new Dispatch(implementation.value().get().id(),object,call.arguments(),Kind.DYNAMIC_CALL,Evidence.CONDITIONAL,witnesses,List.copyOf(pending),ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT),
                        new Observe(Kind.DYNAMIC_CALL,"named local ObjectFactory callback",witnesses,List.copyOf(pending)));
            }
            effects.add(new Conditional(instance.path(),instance.gaps(),instance.dependencies(),invoke));
        }
        return effects.isEmpty()?unresolved(call,"constructed factory binding does not match the selected name",gaps,GapKind.INPUT_BINDING):new Local(effects);
    }
    private Local unresolved(Invocation call,String reason,List<Gap> required,GapKind kind) {
        List<Gap> gaps=new ArrayList<>(required);gaps.add(Mechanisms.gap(call,kind,reason));
        return Local.of(new RequireNormal(List.copyOf(gaps)),new Result(Value.of(new Unknown(reason)).requiring(List.copyOf(gaps))),
                new Observe(Kind.DYNAMIC_CALL,reason,List.of(call.call().site()),List.copyOf(gaps)));
    }
}
