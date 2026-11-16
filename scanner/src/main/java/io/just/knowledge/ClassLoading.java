package io.just.knowledge;

import io.just.program.Program;
import io.just.program.Program.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Mechanisms.*;
import java.util.*;

/** Static classfile data and JVM loading identities. No target class enters the host JVM. */
final class ClassLoading implements Model {
    private final Map<io.just.input.Inputs.ClassData,Bytecode> resources=new IdentityHashMap<>();
    private final Map<List<Atom>,Bytecode> arrays=new HashMap<>();
    @Override public Optional<Local> apply(Invocation call,Bindings bindings,Program program) {
        MethodId api=call.call().target();
        if(api.name().equals("getResourceAsStream") && api.descriptor().equals("(Ljava/lang/String;)Ljava/io/InputStream;")
                && (api.owner().equals("java/lang/Class") || program.subtype(api.owner(),"java/lang/ClassLoader"))
                && program.type(api.owner(),api.loader()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()) {
            if(!(call.arguments().get(0) instanceof Literal literal) || !(literal.value() instanceof String name))return Optional.empty();
            if(!name.startsWith("/") && call.receiver() instanceof ClassValue owner) {
                String type=Values.type(owner.descriptor());int end=type.lastIndexOf('/');name=(end<0?"":type.substring(0,end+1))+name;
            }
            if(name.startsWith("/"))name=name.substring(1);
            if(!name.endsWith(".class"))return Optional.empty();
            String binary=name.substring(0,name.length()-6);
            int loader=call.receiver() instanceof ClassValue owner?owner.loader():program.loader(call.receiver());
            Optional<io.just.input.Inputs.ClassData> data=program.classData(binary,loader);
            if(data.isEmpty())return Optional.of(unresolved(call,"class resource unavailable: "+name));
            Bytecode bytes=resources.computeIfAbsent(data.get(),key -> new Bytecode(binary,key.source(),key.bytes()));
            return Optional.of(Local.of(new Write(call.result(),new Content(),Value.of(bytes)),Mechanisms.result(call.result())));
        }
        boolean read=api.name().equals("readAllBytes") && api.descriptor().equals("()[B")
                && program.type(api.owner(),api.loader()).filter(type -> type.role()==io.just.input.Inputs.Role.PLATFORM).isPresent()
                || Set.of("org/apache/commons/io/IOUtils","com/google/common/io/ByteStreams").contains(api.owner()) && api.name().equals("toByteArray") && api.descriptor().equals("(Ljava/io/InputStream;)[B");
        if(read) {
            Atom stream=call.arguments().isEmpty()?call.receiver():call.arguments().get(0);
            if(stream instanceof ObjectValue object) {
                Value content=bindings.read(object,new Content());
                if(!content.empty()) {
                    List<Effect> effects=new ArrayList<>();effects.add(new Write(call.result(),new Content(),content));
                    for(Bound bound:content.alternatives())if(bound.atom() instanceof Bytecode bytes)effects.add(new Write(call.result(),new Length(),Value.of(new Literal(bytes.bytes().length),bound.path()).requiring(bound.gaps()).tracing(bound.dependencies())));
                    effects.add(Mechanisms.result(call.result()));return Optional.of(new Local(effects).onModelState());
                }
            }
        }
        if(call.is("java/nio/ByteBuffer","wrap","([B)Ljava/nio/ByteBuffer;"))return Optional.of(Local.of(new Write(call.result(),new Content(),Value.of(call.arguments().get(0))),Mechanisms.result(call.result())));
        boolean forName=api.owner().equals("java/lang/Class") && api.name().equals("forName")
                && Set.of("(Ljava/lang/String;)Ljava/lang/Class;","(Ljava/lang/String;ZLjava/lang/ClassLoader;)Ljava/lang/Class;").contains(api.descriptor());
        boolean load=api.name().equals("loadClass") && Set.of("(Ljava/lang/String;)Ljava/lang/Class;","(Ljava/lang/String;Z)Ljava/lang/Class;").contains(api.descriptor())
                && program.lookup(api).value().filter(m -> m.id().owner().equals("java/lang/ClassLoader")).isPresent();
        if(load && call.receiver() instanceof ObjectValue receiver && program.lookup(program.method(receiver.type(),api.name(),api.descriptor(),receiver.loader())).value().filter(m -> !m.id().owner().equals("java/lang/ClassLoader")).isPresent())return Optional.empty();
        if(forName || load) {
            Atom name=call.arguments().get(0);if(name instanceof Literal nil && nil.value()==null)return Optional.of(Local.of(new Raise("java/lang/NullPointerException")));
            Atom loader=forName?(call.arguments().size()==3?call.arguments().get(2):new LoaderValue(call.call().site().method().owner())):call.receiver();
            int scope=forName && call.arguments().size()==1?call.call().site().method().loader():program.loader(loader);List<Effect> effects=new ArrayList<>();
            boolean initialize=forName && (call.arguments().size()==1 || !(call.arguments().get(1) instanceof Literal flag && (Integer.valueOf(0).equals(flag.value()) || Boolean.FALSE.equals(flag.value()))));
            if(name instanceof Literal literal && literal.value() instanceof String text) {
                String descriptor=text.startsWith("[")?text.replace('.','/'):"L"+text.replace('.','/')+";";
                String binary=Values.type(descriptor);scope=program.scope(binary,scope);
                List<Gap> gaps=program.type(binary,scope).isPresent() || descriptor.startsWith("[")?List.of():Mechanisms.queryGaps(call,program.definition(binary));
                Local loaded=Local.of(new RequireNormal(gaps),new Result(Value.of(new ClassValue(descriptor,true,Optional.empty(),scope)).requiring(gaps)));
                if(load && !descriptor.startsWith("[") && call.receiver() instanceof ObjectValue receiver && receiver.exact()) {
                    MethodId requested=program.method(receiver.type(),"findClass","(Ljava/lang/String;)Ljava/lang/Class;",receiver.loader());
                    Query<Method> finder=program.lookup(requested);
                    if(finder.value().filter(method -> !method.id().owner().equals("java/lang/ClassLoader") && method.hasBody()).isPresent()) {
                        List<Gap> fallback=new ArrayList<>(Mechanisms.queryGaps(call,finder));
                        fallback.add(Mechanisms.gap(call,GapKind.DEPLOYMENT,"parent and previously loaded classes do not resolve the requested name before findClass"));
                        Local child=Local.of(new Dispatch(finder.value().orElseThrow().id(),receiver,List.of(name),Kind.DYNAMIC_CALL,Evidence.CONDITIONAL,
                                List.of(call.call().site()),List.copyOf(fallback),ReturnFlow.TO_RESULT,ExceptionFlow.DIRECT));
                        return Optional.of(Local.of(new Alternative(0,loaded),new Alternative(1,child)));
                    }
                }
                if(forName && call.arguments().size()==3 && !(call.arguments().get(1) instanceof Literal flag && (flag.value() instanceof Number || flag.value() instanceof Boolean))) {
                    for(int selected=0;selected<2;selected++) {
                        List<Effect> branch=new ArrayList<>();branch.add(new Need(new InputNeed(call.arguments().get(1),Optional.empty(),NeedKind.VALUE,"Z",List.of(new Literal(selected==1)),"Class.forName initialization flag")));
                        if(selected==1 && descriptor.startsWith("L"))branch.add(new Initialize(binary,scope));branch.addAll(loaded.effects());
                        effects.add(new Alternative(selected,new Local(branch)));
                    }
                } else {
                    if(initialize && descriptor.startsWith("L"))effects.add(new Initialize(binary,scope));effects.addAll(loaded.effects());
                }
            } else {
                Optional<InputLocation> source=Values.location(name);
                if(source.isEmpty() && (name instanceof StringPrefix || name instanceof StringConcat))source=Optional.of(new ValueSource(call.result().id(),0,name,List.of()));
                int selectedLoader=scope;
                Atom value=source.<Atom>map(location -> new ClassValue("Ljava/lang/Object;",false,Optional.of(location.at(new NamedClass())),selectedLoader)).orElse(new Unknown("loaded class name is unspecified"));
                effects.add(new RequireNormal(Mechanisms.unknown(call,"class name and loader must identify an available class")));
                effects.add(new Result(Value.of(value).requiring(Mechanisms.unknown(call,"class name and loader must identify an available class"))));
            }
            return Optional.of(new Local(effects));
        }
        if(!api.name().equals("defineClass") || program.lookup(api).value().filter(m -> m.id().owner().equals("java/lang/ClassLoader")).isEmpty())return Optional.empty();
        List<ValueType> parameters=program.signature(api).parameters();int index=-1;
        for(int i=0;i<parameters.size();i++)if(Set.of("[B","Ljava/nio/ByteBuffer;").contains(parameters.get(i).descriptor())){index=i;break;}
        if(index<0)return Optional.empty();
        List<Gap> frontier=new ArrayList<>();
        Atom input=call.arguments().get(index);List<Bound> bytes=bytes(input,bindings,call.path(),call,new HashSet<>(),new int[]{64},frontier);
        List<Effect> effects=new ArrayList<>();
        if(!frontier.isEmpty())effects.add(new Observe(Kind.DYNAMIC_CALL,"classfile content frontier",List.of(call.call().site()),List.copyOf(frontier)));
        if(bytes.isEmpty()) {
            effects.addAll(unresolved(call,"class definition reached; concrete classfile bytes or slice are unspecified").effects());
            return Optional.of(new Local(effects));
        }
        for(Bound bound:bytes) {
            Bytecode data=(Bytecode)bound.atom();int offset=0,length=data.bytes().length;
            if(parameters.get(index).descriptor().equals("[B")) {
                Atom start=call.arguments().get(index+1),size=call.arguments().get(index+2);
                if(!(start instanceof Literal s && s.value() instanceof Number) || !(size instanceof Literal n && n.value() instanceof Number)) {effects.addAll(unresolved(call,"definition slice offset and length are unspecified").effects());continue;}
                offset=((Number)((Literal)start).value()).intValue();length=((Number)((Literal)size).value()).intValue();
            }
            Local result;
            if(offset<0 || length<0 || offset>data.bytes().length-length)result=Local.of(new Raise("java/lang/IndexOutOfBoundsException"));
            else {
                Atom supplied=index==0?new Literal(null):call.arguments().get(0);String requested=supplied instanceof Literal l && l.value() instanceof String text?text.replace('.','/'):null;
                result=Local.of(new DefineClass(call.receiver(),data,offset,length,requested));
            }
            effects.add(new Conditional(bound.path(),bound.gaps(),bound.dependencies(),result));
        }
        return Optional.of(new Local(effects));
    }
    private List<Bound> bytes(Atom input,Bindings bindings,Path path,Invocation call,Set<Integer> visited,int[] allowance,List<Gap> frontier) {
        if(allowance[0]--<=0){frontier.add(Mechanisms.gap(call,GapKind.BUDGET,"classfile content query frontier (64)"));return List.of();}
        if(input instanceof Bytecode bytes)return List.of(new Bound(bytes,path));
        if(!(input instanceof ObjectValue object) || visited.contains(object.id()))return List.of();
        if(visited.size()>=16){frontier.add(Mechanisms.gap(call,GapKind.BUDGET,"classfile content source frontier (16)"));return List.of();}
        visited.add(object.id());
        try {
        List<Bound> result=new ArrayList<>();
        for(Bound content:bindings.read(object,new Content()).under(path).alternatives()) {
            if(content.atom() instanceof Bytecode)result.add(content);
            else if(content.atom() instanceof ObjectValue nested)for(Bound found:bytes(nested,bindings,content.path(),call,visited,allowance,frontier)) {
                Set<Gap> gaps=new LinkedHashSet<>(content.gaps());gaps.addAll(found.gaps());
                Set<Integer> dependencies=new LinkedHashSet<>(content.dependencies());dependencies.addAll(found.dependencies());
                result.add(new Bound(found.atom(),found.path(),List.copyOf(gaps),Set.copyOf(dependencies)));
            }
        }
        if(!result.isEmpty())return List.copyOf(result);
        for(Bound length:bindings.read(object,new Length()).under(path).alternatives())if(length.atom() instanceof Literal literal && literal.value() instanceof Integer size && size>=0) {
            if(size>65536){frontier.add(Mechanisms.gap(call,GapKind.BUDGET,"raw classfile byte array frontier (65536): "+size));continue;}
            byte[] bytes=new byte[size];List<Atom> identity=new ArrayList<>();Path selected=length.path();Set<Gap> gaps=new LinkedHashSet<>(length.gaps());Set<Integer> dependencies=new LinkedHashSet<>(length.dependencies());boolean known=true;
            for(int i=0;i<size;i++) {
                Value cell=bindings.read(object,new Index(i)).under(selected);
                if(cell.alternatives().size()!=1){known=false;break;}Bound value=cell.alternatives().iterator().next();
                if(!(value.atom() instanceof Literal l && l.value() instanceof Number number)){known=false;break;}
                bytes[i]=number.byteValue();identity.add(value.atom());selected=value.path();gaps.addAll(value.gaps());dependencies.addAll(value.dependencies());
            }
            if(known){Bytecode data=arrays.computeIfAbsent(List.copyOf(identity),key -> new Bytecode("array","byte array at "+call.call().site(),bytes));result.add(new Bound(data,selected,List.copyOf(gaps),Set.copyOf(dependencies)));}
        }
        return List.copyOf(result);
        } finally {visited.remove(object.id());}
    }
    private static Local unresolved(Invocation call,String detail) {
        List<Gap> gaps=Mechanisms.unknown(call,detail);
        return Local.of(new Observe(Kind.DYNAMIC_CALL,detail,List.of(call.call().site()),gaps),new Result(Value.of(new Unknown(detail)).requiring(gaps)));
    }
}
