package io.just.analysis;

import io.just.program.Program.*;
import io.just.program.Program;
import io.just.knowledge.Mechanisms.Bindings;
import io.just.knowledge.Values.*;
import java.util.*;

/** Relation templates only: straight parameter forwarding or one same-object field read. */
final class Summaries {
    sealed interface Template permits Forward,FieldReturn,ConstantReturn {}
    record Forward(Parameter parameter) implements Template {}
    record FieldReturn(Parameter parameter,ReadField field) implements Template {}
    record ConstantReturn(Atom value) implements Template {}
    static Optional<Template> derive(Facts facts) {
        if(!facts.limitations().isEmpty() || !facts.handlers().isEmpty() || facts.cfg().stream().anyMatch(e -> e.exceptional() || e.to()<=e.from()))return Optional.empty();
        Map<Integer,Integer> successors=new HashMap<>();for(Edge edge:facts.cfg())if(successors.merge(edge.from(),1,Integer::sum)>1)return Optional.empty();
        if(facts.actions().size()==1 && facts.actions().get(0) instanceof Returned returned)
            return parameter(returned.value()).map(Forward::new);
        if(facts.actions().size()==2 && facts.actions().get(0) instanceof Constant constant && constant.value() instanceof LiteralConstant literal
                && facts.actions().get(1) instanceof Returned returned && returned.value().origins().equals(Set.of(new Producer(constant.site().instruction()))))
            return Optional.of(new ConstantReturn(new Literal(literal.value())));
        if(facts.actions().size()==2 && facts.actions().get(0) instanceof ReadField field
                && facts.actions().get(1) instanceof Returned returned && returned.value().origins().equals(Set.of(new Producer(field.site().instruction()))))
            return parameter(field.receiver()).map(p -> new FieldReturn(p,field));
        return Optional.empty();
    }
    private static Optional<Parameter> parameter(Sources source) {
        return source.origins().size()==1 && source.origins().iterator().next() instanceof Parameter parameter?Optional.of(parameter):Optional.empty();
    }
    static Optional<Value> apply(Template template,Map<Integer,Value> parameters,Bindings reads,Program program) {
        if(template instanceof ConstantReturn constant)return Optional.of(Value.of(constant.value()));
        if(template instanceof Forward forward)return Optional.of(parameters.getOrDefault(forward.parameter().slot(),Value.BOTTOM));
        FieldReturn field=(FieldReturn)template;
        Value source=parameters.getOrDefault(field.parameter().slot(),Value.BOTTOM);
        Value result=Value.BOTTOM;
        for(Bound bound:source.alternatives()) {
            if(!(bound.atom() instanceof ObjectValue object) || !object.exact())return Optional.empty();
            Value value=reads.read(object,new Field(program.field(field.field().field()).orElse(field.field().field())));
            if(value.empty())return Optional.empty();
            result=result.merge(value.under(bound.path()).requiring(bound.gaps()).tracing(bound.dependencies()));
        }
        return result.empty()?Optional.empty():Optional.of(result);
    }
}
