package io.just.app;

import io.just.knowledge.EntryPoints;

import io.just.input.Inputs;
import io.just.input.StaticData;
import io.just.program.Program;
import io.just.program.Program.MethodId;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.Catalog;
import io.just.analysis.Analyzer;
import io.just.analysis.ScanResult;
import io.just.analysis.InvalidInput;
import io.just.report.Reports;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

public final class Main {
    private Main() {}
    private static final String USAGE = """
            JustSimple - Java bytecode static analysis (scanner requires Java 17+)
            java -jar justsimple-0.1.0.jar --input <jar|war|class|directory> --jdk-home <target-jdk> --output <new-directory>
                [--dependency <jar|directory>]... [--mode application|component] [--no-guidance]
                [--entry 'package.Class#method(descriptor)return'] [--sink 'package.Class#method(descriptor)return']... [--facts <static-data.json>]
                [--max-contexts N] [--max-steps N] [--max-depth N] [--max-relations N] [--max-findings N]
                [--max-alternatives N] [--max-method-instructions N] [--no-demand-guidance]
                [--max-input-bytes N] [--max-entries N] [--max-classes N] [--max-nesting N] [--max-entry-bytes N]
            Exit: 0 finished (findings or no findings), 3 truncated, 2 failed. No target execution.
            Output must not already exist; JSON and Markdown are published together.
            License: GPL-3.0-or-later (META-INF/JustSimple/LICENSE). No warranty.
            """;

    public static void main(String[] args) {
        System.setOut(new PrintStream(System.out,true,StandardCharsets.UTF_8));
        System.setErr(new PrintStream(System.err,true,StandardCharsets.UTF_8));
        System.exit(run(args,System.out,System.err));
    }

    public static int run(String[] args, PrintStream out, PrintStream err) {
        if (args.length == 1 && (args[0].equals("--help") || args[0].equals("-h"))) { out.print(USAGE); return 0; }
        Options options;
        try {
            options = parse(args);
        } catch (IllegalArgumentException configuration) {
            err.println("FAILED configuration: " + configuration.getMessage());
            err.print(USAGE);
            return 2;
        }
        try {
            Path output=Reports.requireNewOutput(options.output());
            long started=System.nanoTime();
            ScanResult result = analyze(options,err,started);
            err.println("[write] Publishing reports: " + output);
            Reports.write(result, output);
            out.println(result.execution() + " " + result.outcome() + ": " + result.findings().size() + " findings, "
                    + result.relations().size() + " relations; " + output);
            if(result.execution()==ScanResult.Execution.TRUNCATED) {
                err.println("[limit] "+result.limitations().get(0));
                return 3;
            }
            return 0;
        } catch (IOException | Inputs.Failure | Program.Failure failure) {
            err.println("FAILED: " + failure.getMessage());
            failure.printStackTrace(err);
            return 2;
        } catch (InvalidInput invalid) {
            err.println("FAILED configuration: " + invalid.getMessage());
            return 2;
        } catch (RuntimeException internal) {
            err.println("FAILED internal analysis error: " + internal.getMessage());
            internal.printStackTrace(err);
            return 2;
        }
    }


    private static ScanResult analyze(Options options,PrintStream progress,long started) throws IOException {
        progress.println("[read] Indexing input: " + options.input().toAbsolutePath());progress.flush();
        try (Inputs inputs = Inputs.open(options.input(), options.dependencies(), options.jdk(), options.inputLimits())) {
            Program program = new Program(inputs,options.methodInstructions(),Math.max(Program.DEFAULT_SCAN_INSTRUCTION_LIMIT,options.analysisLimits().steps()));
            Inputs.Summary input=inputs.summary();
            progress.printf(Locale.ROOT,"[read] classes=%d dependencies=%d target-jdk=%d%n",input.applicationClasses(),input.dependencyClasses(),input.jdkFeature());
            Catalog catalog = options.guidance() ? Catalog.builtin() : Catalog.empty();
            Mechanisms knowledge = new Mechanisms(program, catalog, options.sinks(),options.analysisLimits().alternatives());
            Optional<StaticData> facts = options.facts().isPresent()
                    ? Optional.of(StaticData.read(options.facts().get())) : Optional.empty();
            Analyzer analyzer = new Analyzer(program, knowledge, options.analysisLimits(), options.demandGuidance());
            return analyzer.scan(options.mode(), options.guidance(), options.entries(), facts,status -> {
                progress.printf(Locale.ROOT,"[%s] %.1fs entries=%d contexts=%d steps=%d/%d relations=%d queued=%d%n",
                        status.stage().name().toLowerCase(Locale.ROOT),(System.nanoTime()-started)/1_000_000_000.0,
                        status.entries(),status.contexts(),status.steps(),options.analysisLimits().steps(),status.relations(),status.queued());
                progress.flush();
            });
        }
    }

    private record Options(Path input, List<Path> dependencies, Path jdk, Path output, EntryPoints.Mode mode,
                           boolean guidance, Set<MethodId> entries, Optional<Path> facts, Inputs.Limits inputLimits, Analyzer.Limits analysisLimits, int methodInstructions,boolean demandGuidance,Set<MethodId> sinks) {}

    private static Options parse(String[] args) {
        Map<String, String> values = new LinkedHashMap<>();
        List<Path> dependencies = new ArrayList<>();
        Set<MethodId> sinks=new LinkedHashSet<>();
        boolean guidance = true;
        boolean demandGuidance=true;
        Set<String> known = Set.of("--input", "--jdk-home", "--output", "--mode", "--entry", "--facts", "--max-contexts", "--max-steps", "--max-depth",
                "--max-relations", "--max-findings", "--max-alternatives", "--max-method-instructions", "--max-input-bytes",
                "--max-entries", "--max-classes", "--max-nesting", "--max-entry-bytes");
        for (int i = 0; i < args.length; i++) {
            String option = args[i];
            if (option.equals("--no-guidance")) { guidance = false; continue; }
            if (option.equals("--no-demand-guidance")) { demandGuidance=false;continue; }
            if (!known.contains(option) && !option.equals("--dependency") && !option.equals("--sink")) throw new IllegalArgumentException("unknown option: " + option);
            if (++i == args.length) throw new IllegalArgumentException("missing value for " + option);
            if (option.equals("--dependency")) dependencies.add(Path.of(args[i]));
            else if(option.equals("--sink"))sinks.add(entry(args[i],"--sink"));
            else if (values.putIfAbsent(option, args[i]) != null) throw new IllegalArgumentException("duplicate option: " + option);
        }
        for (String required : List.of("--input", "--jdk-home", "--output"))
            if (!values.containsKey(required)) throw new IllegalArgumentException("required: " + required);
        Inputs.Limits input = Inputs.Limits.defaults();
        Analyzer.Limits analysis = Analyzer.Limits.defaults();
        return new Options(Path.of(values.get("--input")), List.copyOf(dependencies), Path.of(values.get("--jdk-home")),
                Path.of(values.get("--output")), EntryPoints.Mode.valueOf(values.getOrDefault("--mode", "application").toUpperCase(Locale.ROOT)), guidance,
                values.containsKey("--entry") ? Set.of(entry(values.get("--entry"),"--entry")) : Set.of(),
                Optional.ofNullable(values.get("--facts")).map(Path::of),
                new Inputs.Limits(number(values, "--max-input-bytes", input.bytes()), integer(values, "--max-entries", input.entries()),
                        integer(values, "--max-classes", input.classes()), integer(values, "--max-nesting", input.depth()), integer(values, "--max-entry-bytes", input.entryBytes())),
                new Analyzer.Limits(integer(values, "--max-contexts", analysis.contexts()), number(values, "--max-steps", analysis.steps()),
                        integer(values, "--max-depth", analysis.depth()), integer(values, "--max-relations", analysis.relations()),
                        integer(values, "--max-findings", analysis.findings()), integer(values, "--max-alternatives", analysis.alternatives())),
                integer(values, "--max-method-instructions", 20_000),demandGuidance,Set.copyOf(sinks));
    }

    private static MethodId entry(String selector,String option) {
        int owner = selector.indexOf('#'), descriptor = selector.indexOf('(', owner + 1);
        if (owner < 1 || descriptor <= owner + 1 || !MethodId.validDescriptor(selector.substring(descriptor))
                || !selector.substring(0,owner).matches("(?U)[\\w$/]+(?:\\.[\\w$]+)*")
                || !selector.substring(owner+1,descriptor).matches("(?U)(?:[\\w$]+|<init>|<clinit>)"))
            throw new IllegalArgumentException(option+" needs exact owner#method JVM descriptor: " + selector);
        return new MethodId(selector.substring(0, owner).replace('.', '/'), selector.substring(owner + 1, descriptor), selector.substring(descriptor));
    }

    private static int integer(Map<String, String> values, String key, int fallback) {
        long value = number(values, key, fallback);
        if (value > Integer.MAX_VALUE) throw new IllegalArgumentException("too large: " + key);
        return (int) value;
    }
    private static long number(Map<String, String> values, String key, long fallback) {
        if (!values.containsKey(key)) return fallback;
        long value = Long.parseLong(values.get(key));
        if (value < 0 || value == 0 && !key.equals("--max-nesting")) throw new IllegalArgumentException("invalid budget: " + key);
        return value;
    }
}
