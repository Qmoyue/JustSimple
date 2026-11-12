package io.just.knowledge;

import io.just.knowledge.EntryPoints.Entry;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Mechanisms.*;
import org.objectweb.asm.Opcodes;
import java.util.*;

/** Registration creates a future request boundary, not a synchronous call to handle. */
final class HttpBridge implements Model {
    static final MethodId REGISTER=new MethodId("com/sun/net/httpserver/HttpServer","createContext","(Ljava/lang/String;Lcom/sun/net/httpserver/HttpHandler;)Lcom/sun/net/httpserver/HttpContext;");
    private static final String HANDLE="(Lcom/sun/net/httpserver/HttpExchange;)V";

    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        MethodId api=call.call().target();
        if (api.owner().equals("com/sun/net/httpserver/HttpServer") && api.name().equals("create")
                && Set.of("()Lcom/sun/net/httpserver/HttpServer;","(Ljava/net/InetSocketAddress;I)Lcom/sun/net/httpserver/HttpServer;").contains(api.descriptor()))
            return Optional.of(Local.of(Mechanisms.result(new HttpServerValue(call.result().id(),call.call().site()))));
        if (api.equals(REGISTER)) {
            Atom handler=call.arguments().get(1); MethodId target=new MethodId("com/sun/net/httpserver/HttpHandler","handle",HANDLE);
            if (handler instanceof Literal literal && literal.value()==null || call.arguments().get(0) instanceof Literal path && path.value()==null)
                return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            if (call.arguments().get(0) instanceof Literal path && path.value() instanceof String text && !text.startsWith("/"))
                return Optional.of(Local.of(new Raise("java/lang/IllegalArgumentException")));
            List<Gap> gaps=new ArrayList<>();
            gaps.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"request evaluated after selected initialization; server start, request timing and actual exposure are assumptions"));
            if (!(call.receiver() instanceof HttpServerValue)) gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"server factory/receiver binding is unspecified"));
            if (handler instanceof ObjectValue object) {
                target=program.resolve(new MethodId(object.type(),"handle",HANDLE)).map(Method::id).orElse(target);
                if (!object.exact()) gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"registered handler runtime type is unspecified"));
            } else if (!(handler instanceof LambdaValue || handler instanceof ProxyValue))
                gaps.add(Mechanisms.gap(call,GapKind.INPUT_BINDING,"registered handler value is unspecified"));
            List<Site> witnesses=List.of(call.call().site());
            return Optional.of(Local.of(Mechanisms.result(call.result()),new Deferred(new Dispatch(target,handler,
                    List.of(new Symbolic("com/sun/net/httpserver/HttpExchange","request exchange for this registration")),Kind.HTTP_CALLBACK,Evidence.CONDITIONAL,witnesses,List.copyOf(gaps),ReturnFlow.IGNORE,ExceptionFlow.DIRECT),
                    new Observe(Kind.HTTP_CALLBACK,"registered request callback",witnesses,List.copyOf(gaps)))));
        }
        if (api.owner().equals("com/sun/net/httpserver/HttpExchange") && api.name().equals("getRequestBody") && api.descriptor().equals("()Ljava/io/InputStream;"))
            return Optional.of(Local.of(Mechanisms.result(call.result()),new Write(call.result(),new Content(),Value.of(call.receiver()))));
        if (api.owner().equals("com/sun/net/httpserver/HttpServer") && api.name().equals("start") && api.descriptor().equals("()V"))
            return Optional.of(Local.of(new Result(Value.NULL)));
        return Optional.empty();
    }

    static Query<List<Entry>> entries(Program program) {
        List<Entry> entries=new ArrayList<>();List<QueryIssue> pending=new ArrayList<>();
        for(ClassInfo type:program.targets())for(Method method:type.methods())
            if(method.isPublic() && method.isStatic() && method.id().name().equals("main") && method.id().descriptor().equals("([Ljava/lang/String;)V")
                    && method.hasBody()) {
                Query<Set<MethodId>> scope=program.discover(Set.of(method.id()),256);pending.addAll(scope.pending());
                boolean registered=scope.value().orElseThrow().stream().anyMatch(id -> program.references(id).value().orElse(List.of()).contains(REGISTER));
                if(registered || !scope.pending().isEmpty())entries.add(new Entry(method,"JDK HTTP registration lifecycle",scope.pending().isEmpty()
                        ?List.of("selected main lifecycle, server start and HTTP exposure remain deployment assumptions")
                        :List.of("registration discovery is incomplete; actual registration and exposure remain unresolved")));
            }
        return new Query<>(Optional.of(List.copyOf(entries)),List.copyOf(pending));
    }
}
