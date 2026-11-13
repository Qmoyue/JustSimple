package io.just.agent.bridge;

import com.google.gson.*;
import io.just.analysis.*;
import io.just.analysis.ScanResult.ProofUse;
import io.just.input.*;
import io.just.knowledge.*;
import io.just.program.*;
import io.just.program.Program.*;
import io.just.report.Reports;
import java.io.*;
import java.nio.file.Path;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.ToIntFunction;

/** Input-scoped tool assembly. Domain semantics remain in program, knowledge and analysis. */
final class ScannerTools implements AutoCloseable {
    record Config(String input,String jdk,List<String> dependencies,String staticData,String results,
                         int methodInstructions,int maxResults,long resultBytes,int maxScans,
                         Inputs.Limits inputLimits,Analyzer.Limits scanLimits) {
        public Config {
            Objects.requireNonNull(input);Objects.requireNonNull(jdk);Objects.requireNonNull(results);
            dependencies=List.copyOf(dependencies);
            if(methodInstructions<1 || maxScans<1)throw new IllegalArgumentException("tool limits must be positive");
            inputLimits=inputLimits==null?Inputs.Limits.defaults():inputLimits;
            scanLimits=scanLimits==null?new Analyzer.Limits(Integer.MAX_VALUE,Integer.MAX_VALUE,Integer.MAX_VALUE,Integer.MAX_VALUE,Integer.MAX_VALUE,Integer.MAX_VALUE):scanLimits;
        }
    }
    record Reply(String inputId,String resultRef,String operation,long elapsedMillis,JsonObject summary) {}
    private record QueryResult(String inputId,String scanRef,Inputs.Summary input,int methodInstructionBudget,
                               List<String> programLimitations,List<String> missingClasses,Object value) {}
    private record TypeDefinition(String name,String parent,List<String> interfaces,int access,int loader,Inputs.Role role,
                                  List<Program.Annotation> annotations,List<Program.FieldInfo> fields) {}
    private record Scope(String scanRef,Inputs input,Program program) {}
    private record Scan(Inputs input,Program program,ScanResult result) {}
    private final Config config;
    private final String identity=UUID.randomUUID().toString();
    private final Inputs input;
    private final Program program;
    private final Catalog catalog;
    private final ResultStore results;
    private final Map<String,Scan> scans=new LinkedHashMap<>();

    ScannerTools(Config config)throws IOException {
        this.config=config;this.catalog=Catalog.builtin();this.input=open();
        try {
            this.program=new Program(input,config.methodInstructions());
            this.results=new ResultStore(Path.of(config.results()),identity,config.maxResults(),config.resultBytes());
        } catch(IOException|RuntimeException failure){try{input.close();}catch(IOException close){failure.addSuppressed(close);}throw failure;}
    }
    private Inputs open()throws IOException {return Inputs.open(Path.of(config.input()),config.dependencies().stream().map(Path::of).toList(),Path.of(config.jdk()),config.inputLimits());}
    String identity(){return identity;}
    Analyzer.Limits scanLimits(){return config.scanLimits();}
    Analyzer.Limits scanDefaults(){
        var defaults=Analyzer.Limits.defaults();var max=config.scanLimits();
        return new Analyzer.Limits(Math.min(defaults.contexts(),max.contexts()),Math.min(defaults.steps(),max.steps()),
                Math.min(defaults.depth(),max.depth()),Math.min(defaults.relations(),max.relations()),Math.min(defaults.findings(),max.findings()),Math.min(defaults.alternatives(),max.alternatives()));
    }

    Object execute(String operation,JsonObject args,Consumer<Analyzer.ScanProgress> progress)throws IOException {
        if(!Set.of("read_result","export_scan","export_result").contains(operation))results.requireCapacity();
        Scope scope=scope(operation.equals("check_connection")?required(args,"resultRef"):text(args,"scanRef",""));
        Program program=scope.program();Inputs input=scope.input();
        long start=System.nanoTime();JsonObject summary=new JsonObject();Object value;
        switch(operation) {
            case "find_symbols" -> {
                String owner=text(args,"owner",""),query=text(args,"query","").toLowerCase(Locale.ROOT);
                String search=text(args,"scope","target");
                if(!search.equals("target") && !search.equals("candidates"))throw new IllegalArgumentException("unknown symbol scope: "+search);
                List<ClassInfo> classes;List<QueryIssue> pending=new ArrayList<>();
                int loader=number(args,"loader",0,0,Integer.MAX_VALUE);loader(program,loader);
                if(!owner.isEmpty()) {Query<ClassInfo> type=program.definition(owner,loader);pending.addAll(type.pending());classes=type.value().stream().toList();}
                else classes=search.equals("target")?program.targets():program.candidates();
                List<Method> matches=new ArrayList<>();
                for(ClassInfo type:classes)for(Method method:type.methods()) {
                    interrupted();if(method.id().toString().toLowerCase(Locale.ROOT).contains(query))matches.add(method);
                }
                Map<String,Object> symbols=new LinkedHashMap<>();
                if(!owner.isEmpty())symbols.put("classes",classes.stream().map(type -> new TypeDefinition(type.name(),type.parent(),type.interfaces(),
                        type.access(),type.loader(),type.role(),type.annotations(),program.fields(type.name(),type.loader()))).toList());
                symbols.put("scope",owner.isEmpty()?search:owner);symbols.put("methods",matches);symbols.put("pending",pending);value=symbols;
                summary.addProperty("scope",owner.isEmpty()?search:owner);summary.addProperty("classes",classes.size());
                summary.addProperty("methods",matches.size());issues(summary,pending);
            }
            case "find_entries" -> {
                var found=new EntryPoints(program).find(mode(args),methods(program,args,"entries"));value=found;
                summary.addProperty("entries",found.value().map(List::size).orElse(0));issues(summary,found.pending());
            }
            case "inspect_method" -> {
                MethodId method=method(program,args.get("method"));String view=text(args,"view","bytecode");
                if(view.equals("bytecode")) {
                    var body=Bytecode.query(program,method,number(args,"offset",0,0,Integer.MAX_VALUE),number(args,"limit",80,1,1000));value=body;
                    body.value().ifPresent(b -> {summary.addProperty("offset",b.offset());summary.addProperty("instructions",b.instructions().size());summary.addProperty("totalInstructions",b.total());summary.addProperty("next",b.next());summary.addProperty("hasBody",b.method().hasBody());});
                    issues(summary,body.pending());
                } else if(view.equals("facts")) {
                    Query<Method> declaration=program.declaration(method);
                    value=Map.of("facts",declaration.value().map(m -> program.facts(m.id())),"pending",declaration.pending());
                    issues(summary,declaration.pending());
                    declaration.value().ifPresent(m -> {Facts facts=program.facts(m.id());summary.addProperty("actions",facts.actions().size());limitations(summary,facts.limitations());});
                } else throw new IllegalArgumentException("unknown method view: "+view);
            }
            case "expand_graph" -> {
                List<GraphQuery.Cursor> cursors=new ArrayList<>();
                for(JsonElement item:array(args,"scope",1,1000)) {
                    JsonObject cursor=object(item,"graph cursor");
                    cursors.add(new GraphQuery.Cursor(method(program,cursor.get("method")),number(cursor,"depth",0,0,Integer.MAX_VALUE),number(cursor,"offset",0,0,Integer.MAX_VALUE)));
                }
                var graph=GraphQuery.expand(program,GraphQuery.Direction.valueOf(text(args,"direction","OUTGOING")),cursors,
                        number(args,"depth",1,1,Integer.MAX_VALUE),number(args,"methods",32,1,Integer.MAX_VALUE),number(args,"edges",128,1,Integer.MAX_VALUE));value=graph;
                summary.addProperty("edges",graph.edges().size());summary.addProperty("inspected",graph.inspected());summary.addProperty("frontier",graph.frontier().size());issues(summary,graph.pending());limitations(summary,graph.limitations());
            }
            case "resolve_dispatch" -> {
                List<DefinedType> receivers=new ArrayList<>();
                for(JsonElement item:array(args,"receivers",0,10000)) {
                    JsonObject receiver=object(item,"receiver");int scopeLoader=number(receiver,"loader",0,0,Integer.MAX_VALUE);loader(program,scopeLoader);
                    receivers.add(new DefinedType(required(receiver,"name"),scopeLoader));
                }
                loader(program,number(args,"loader",0,0,Integer.MAX_VALUE));
                var dispatch=new io.just.program.Dispatch(program).within(method(program,args.get("method")),required(args,"upper"),
                        number(args,"loader",0,0,Integer.MAX_VALUE),receivers,new io.just.program.Dispatch.Budget(number(args,"receiverBudget",64,1,Integer.MAX_VALUE),number(args,"targetBudget",64,1,Integer.MAX_VALUE)));value=dispatch;
                dispatch.value().ifPresent(d -> {summary.addProperty("targets",d.targets().size());summary.addProperty("inspected",d.inspected());summary.addProperty("frontier",d.frontier().size());});issues(summary,dispatch.pending());
            }
            case "trace_source" -> {
                JsonObject origin=object(args.get("origin"),"origin");Origin root=switch(required(origin,"kind")) {
                    case "Parameter" -> new Parameter(number(origin,"slot",-1,0,65535));
                    case "Producer" -> new Producer(number(origin,"instruction",-1,0,Integer.MAX_VALUE));
                    default -> throw new IllegalArgumentException("source origin must be Parameter or Producer");
                };
                var trace=SourceTrace.query(program,method(program,args.get("method")),root,number(args,"budget",128,1,Integer.MAX_VALUE));value=trace;
                trace.value().ifPresent(t -> {summary.addProperty("visited",t.plan().visited());summary.addProperty("frontier",t.plan().frontier().size());limitations(summary,t.limitations());});issues(summary,trace.pending());
            }
            case "lookup_knowledge" -> {
                Set<MethodId> methods=methods(program,args,"methods");Set<String> ids=strings(args,"ids");
                if(!methods.isEmpty()) {
                    var hints=(ids.isEmpty()?catalog:catalog.select(ids)).hints(program,methods);value=hints;summary.addProperty("hints",hints.value().map(List::size).orElse(0));issues(summary,hints.pending());
                } else if(!ids.isEmpty()) {
                    Map<String,JsonElement> material=new LinkedHashMap<>();for(String id:ids){interrupted();material.put(id,JsonParser.parseString(catalog.material(id)));}
                    value=material;summary.addProperty("references",material.size());
                } else {value=catalog.entries();summary.addProperty("references",catalog.entries().size());}
            }
            case "check_connection" -> {
                String ref=required(args,"resultRef");Scan scan=scans.get(ref);
                if(scan==null)throw new IllegalArgumentException("connection check requires an unreleased scan result from this input");
                List<Integer> roots=new ArrayList<>();for(JsonElement root:array(args,"relations",1,1000))roots.add(identity(root,"relation"));
                List<ProofUse> choices=new ArrayList<>();
                if(args.has("supports"))for(JsonElement item:array(args,"supports",0,30000)) {
                    JsonObject choice=object(item,"support");choices.add(new ProofUse(identity(choice.get("relation"),"relation"),identity(choice.get("support"),"support")));
                }
                var connection=ConnectionCheck.query(scan.program(),scan.result().relations(),roots,choices,number(args,"budget",128,1,Integer.MAX_VALUE));value=connection;
                summary.addProperty("state",connection.state().name());summary.addProperty("inspected",connection.inspected());summary.addProperty("frontier",connection.frontier().size());summary.addProperty("gaps",connection.gaps().size());summary.addProperty("pendingCount",connection.pending().size());summary.add("pending",ToolJson.GSON.toJsonTree(connection.pending().stream().limit(4).map(ScannerTools::brief).toList()));summary.addProperty("sourceResult",ref);
            }
            case "scan_target" -> {return scan(args,start,progress);}
            case "export_scan" -> {
                Scan scan=scans.get(required(args,"resultRef"));
                if(scan==null)throw new IllegalArgumentException("export requires an unreleased scan result");
                Path output=Path.of(required(args,"output")).toAbsolutePath().normalize();
                Reports.write(scan.result(),output);
                return Map.of("directory",output.toString(),"files",List.of("report.json","report.md","input-requirements.json"));
            }
            case "export_result" -> {
                long bytes=results.export(required(args,"resultRef"),Path.of(required(args,"output")),number(args,"bytes",32<<20,1,256<<20));
                return Map.of("bytes",bytes);
            }
            case "read_result" -> {
                String ref=required(args,"resultRef");
                String action=text(args,"action","read");
                if(!action.equals("read") && !action.equals("release"))throw new IllegalArgumentException("unknown result action: "+action);
                if(action.equals("release")) {
                    results.release(ref);Scan scan=scans.remove(ref);if(scan!=null)scan.input().close();return Map.of("inputId",identity,"released",ref);
                }
                List<String> path=args.has("path")?array(args,"path",0,64).asList().stream().map(item -> string(item,"path component")).toList():List.of();
                if(args.has("ids"))return select(ref,path,args);
                return results.read(ref,path,number(args,"offset",0,0,Integer.MAX_VALUE),number(args,"limit",20,1,100),number(args,"characters",6000,256,16000));
            }
            default -> throw new IllegalArgumentException("unknown scanner tool: "+operation);
        }
        Inputs.Summary coverage=input.summary();List<String> limitations=program.limitations(),missing=program.missingClasses();
        summary.addProperty("inputLimitations",coverage.limitations().size());summary.addProperty("programLimitations",limitations.size());summary.addProperty("missingClasses",missing.size());
        if(!scope.scanRef().isEmpty())summary.addProperty("scanRef",scope.scanRef());
        return new Reply(identity,results.save(new QueryResult(identity,scope.scanRef(),coverage,config.methodInstructions(),limitations,missing,value)),operation,elapsed(start),summary);
    }
    private Object select(String ref,List<String> path,JsonObject args)throws IOException {
        Scan scan=scans.get(ref);
        if(scan==null || path.size()!=1)throw new IllegalArgumentException("ID selection needs an unreleased scan and one evidence section");
        if(number(args,"offset",0,0,Integer.MAX_VALUE)!=0)throw new IllegalArgumentException("ID selection resumes with deferred IDs, not offset");
        Set<Integer> requested=new LinkedHashSet<>();
        for(JsonElement id:array(args,"ids",1,64))requested.add(identity(id,"evidence ID"));
        Map<Integer,Integer> positions=switch(path.get(0)) {
            case "relations" -> positions(scan.result().relations(),requested,ScanResult.Relation::id);
            case "findings" -> positions(scan.result().findings(),requested,ScanResult.Finding::id);
            case "inputRequirements" -> positions(scan.result().inputRequirements(),requested,ScanResult.InputRequirement::id);
            default -> throw new IllegalArgumentException("ID selection supports relations, findings and inputRequirements");
        };
        Set<Integer> missing=new LinkedHashSet<>(requested);missing.removeAll(positions.values());
        ResultStore.Selection selected=results.select(ref,path,positions,number(args,"limit",20,1,100),number(args,"characters",6000,256,16000));
        return Map.of("resultRef",ref,"kind","selection","path",path,"requested",requested,"missing",missing,"deferred",selected.deferred(),"data",selected.data());
    }
    private static <T> Map<Integer,Integer> positions(List<T> rows,Set<Integer> requested,ToIntFunction<T> identity) {
        Map<Integer,Integer> positions = new LinkedHashMap<>();
        for (int index = 0; index < rows.size() && positions.size() < requested.size(); index++) {
            int id = identity.applyAsInt(rows.get(index));
            if (requested.contains(id)) positions.put(index, id);
        }
        return positions;
    }
    private Scope scope(String ref) {
        if(ref.isEmpty())return new Scope("",input,program);
        Scan scan=scans.get(ref);if(scan==null)throw new IllegalArgumentException("local query requires an unreleased scan result from this input: "+ref);
        return new Scope(ref,scan.input(),scan.program());
    }
    private static void loader(Program program,int loader) {
        if(loader!=0 && program.loaderIdentity(loader).isEmpty())throw new IllegalArgumentException("unknown loader in selected input: "+loader+"; choose its scanRef");
    }
    private Reply scan(JsonObject args,long start,Consumer<Analyzer.ScanProgress> progress)throws IOException {
        if(scans.size()>=config.maxScans())throw new IOException("scan result capacity reached; release an unused scan result");
        Analyzer.Limits max=config.scanLimits(),defaults=scanDefaults();JsonObject limits=args.has("budgets")?object(args.get("budgets"),"budgets"):new JsonObject();
        Analyzer.Limits budget=new Analyzer.Limits(number(limits,"contexts",defaults.contexts(),1,max.contexts()),number(limits,"steps",defaults.steps(),1,max.steps()),
                number(limits,"depth",defaults.depth(),1,max.depth()),number(limits,"relations",defaults.relations(),1,max.relations()),number(limits,"findings",defaults.findings(),1,max.findings()),number(limits,"alternatives",defaults.alternatives(),1,max.alternatives()));
        String selection=text(args,"knowledge","all");
        Set<String> ids=strings(args,"knowledgeIds");
        if(selection.equals("selected")!=!ids.isEmpty())throw new IllegalArgumentException("knowledge selected requires knowledgeIds; other modes do not accept IDs");
        Catalog selected=switch(selection){case "all" -> catalog;case "none" -> Catalog.empty();case "selected" -> catalog.select(ids);default -> throw new IllegalArgumentException("unknown knowledge selection: "+selection);};
        boolean demandGuidance=bool(args,"demandGuidance",true);
        // Independent scan state prevents exploratory queries from consuming the complete scanner's budgets.
        Inputs scanInput=open();boolean retained=false;
        try {
            Program scanProgram=new Program(scanInput,config.methodInstructions());
            Optional<StaticData> data=config.staticData()==null?Optional.empty():Optional.of(StaticData.read(Path.of(config.staticData())));
            ScanResult result=new Analyzer(scanProgram,new Mechanisms(scanProgram,selected,methods(scanProgram,args,"sinks")),budget,
                    demandGuidance).scan(mode(args),true,methods(scanProgram,args,"entries"),data,progress);
            String ref=results.save(writer -> Reports.json(result,writer));scans.put(ref,new Scan(scanInput,scanProgram,result));retained=true;
            JsonObject summary=new JsonObject();summary.addProperty("execution",result.execution().name());summary.addProperty("outcome",result.outcome().name());
            summary.addProperty("entries",result.entries().size());summary.addProperty("relations",result.relations().size());summary.addProperty("findings",result.findings().size());summary.addProperty("breakpoints",result.breakpoints().size());summary.addProperty("demandFrontier",result.demandFrontier().size());
            summary.add("statistics",ToolJson.GSON.toJsonTree(result.statistics()));summary.add("budgets",ToolJson.GSON.toJsonTree(budget));summary.addProperty("limitations",result.limitations().size());summary.addProperty("missingClasses",result.missingClasses().size());
            if(!result.limitations().isEmpty())summary.addProperty("firstLimitation",brief(result.limitations().get(0)));
            return new Reply(identity,ref,"scan_target",elapsed(start),summary);
        } finally {if(!retained)scanInput.close();}
    }
    private static EntryPoints.Mode mode(JsonObject args){return EntryPoints.Mode.valueOf(text(args,"mode","COMPONENT"));}
    private static MethodId method(JsonElement item) {
        JsonObject value=object(item,"method");
        String owner=required(value,"owner"),name=required(value,"name"),descriptor=required(value,"descriptor");
        if(!MethodId.validDescriptor(descriptor))throw new IllegalArgumentException("invalid method descriptor: "+descriptor);
        return new MethodId(owner,name,descriptor,number(value,"loader",0,0,Integer.MAX_VALUE));
    }
    private static MethodId method(Program program,JsonElement value) {
        MethodId method=method(value);loader(program,method.loader());return method;
    }
    private static Set<MethodId> methods(Program program,JsonObject args,String key) {
        Set<MethodId> result=new LinkedHashSet<>();if(args.has(key))for(JsonElement value:array(args,key,0,1000))result.add(method(program,value));return result;
    }
    private static Set<String> strings(JsonObject args,String key) {
        Set<String> result=new LinkedHashSet<>();if(args.has(key))for(JsonElement value:array(args,key,0,1000))result.add(string(value,key));return result;
    }
    private static JsonObject object(JsonElement value,String key) {
        if(value==null || !value.isJsonObject())throw new IllegalArgumentException(key+" must be an object");return value.getAsJsonObject();
    }
    private static JsonArray array(JsonObject args,String key,int minimum,int maximum) {
        JsonElement value=args.get(key);
        if(value==null || !value.isJsonArray() || value.getAsJsonArray().size()<minimum || value.getAsJsonArray().size()>maximum)
            throw new IllegalArgumentException(key+" requires an array of "+minimum+".."+maximum+" items");
        return value.getAsJsonArray();
    }
    private static String required(JsonObject args,String key){String value=text(args,key,"");if(value.isEmpty())throw new IllegalArgumentException(key+" is required");return value;}
    private static String text(JsonObject args,String key,String fallback) {
        return args.has(key)?string(args.get(key),key):fallback;
    }
    private static String string(JsonElement value,String key) {
        if(!value.isJsonPrimitive() || !value.getAsJsonPrimitive().isString())throw new IllegalArgumentException(key+" must be a string");
        return value.getAsString();
    }
    private static boolean bool(JsonObject args,String key,boolean fallback) {
        if(!args.has(key))return fallback;JsonElement value=args.get(key);
        if(!value.isJsonPrimitive() || !value.getAsJsonPrimitive().isBoolean())throw new IllegalArgumentException(key+" must be a boolean");
        return value.getAsBoolean();
    }
    private static long integer(JsonElement value,String key) {
        if(value==null || !value.isJsonPrimitive() || !value.getAsJsonPrimitive().isNumber())throw new IllegalArgumentException(key+" must be an integer");
        try{return value.getAsBigDecimal().longValueExact();}
        catch(ArithmeticException invalid){throw new IllegalArgumentException(key+" must be an exact 64-bit integer",invalid);}
    }
    private static int identity(JsonElement value,String key) {
        long id=integer(value,key);
        if(id<0 || id>Integer.MAX_VALUE)throw new IllegalArgumentException(key+" must be within 0.."+Integer.MAX_VALUE);return (int)id;
    }
    private static int number(JsonObject args,String key,int fallback,int minimum,int maximum) {
        return (int)number(args,key,(long)fallback,minimum,maximum);
    }
    private static long number(JsonObject args,String key,long fallback,long minimum,long maximum) {
        long value=args.has(key)?integer(args.get(key),key):fallback;
        if(value<minimum || value>maximum)throw new IllegalArgumentException(key+" must be within "+minimum+".."+maximum);return value;
    }
    private static String brief(String detail){return detail.length()>512?detail.substring(0,512)+"…":detail;}
    private static void issues(JsonObject summary,List<QueryIssue> pending) {
        summary.addProperty("pendingCount",pending.size());
        summary.add("pending",ToolJson.GSON.toJsonTree(pending.stream().limit(4).map(i -> new QueryIssue(i.cause(),brief(i.detail()))).toList()));
    }
    private static void limitations(JsonObject summary,List<Limitation> pending) {
        summary.addProperty("limitationsCount",pending.size());
        summary.add("limitations",ToolJson.GSON.toJsonTree(pending.stream().limit(4).map(i -> new Limitation(i.cause(),brief(i.detail()))).toList()));
    }
    private static long elapsed(long start){return (System.nanoTime()-start)/1_000_000;}
    private static void interrupted(){if(Thread.currentThread().isInterrupted())throw new java.util.concurrent.CancellationException("tool query interrupted");}
    @Override public void close()throws IOException {
        IOException failure=null;
        for(Scan scan:scans.values())try{scan.input().close();}catch(IOException problem){if(failure==null)failure=problem;else failure.addSuppressed(problem);}
        scans.clear();try{results.close();}catch(IOException problem){if(failure==null)failure=problem;else failure.addSuppressed(problem);}
        try{input.close();}catch(IOException problem){if(failure==null)failure=problem;else failure.addSuppressed(problem);}
        if(failure!=null)throw failure;
    }
}
