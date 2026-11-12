package io.just.report;

import com.google.gson.stream.JsonWriter;
import io.just.analysis.ScanResult;
import io.just.analysis.ScanResult.*;
import java.io.IOException;
import java.io.Writer;
import java.io.FilterWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.CancellationException;

/** Projects one completed result. A directory rename publishes reports and input needs together. */
public final class Reports {
    private Reports() {}
    /** Machine evidence only; does not produce or publish a human audit report. The caller owns the writer. */
    public static void json(ScanResult result, Writer writer) throws IOException {
        interrupted();
        JsonWriter out=new JsonWriter(interruptible(writer));new References().json(result,out);out.flush();
    }
    /** Check the output before a caller starts analysis. Publishing checks it again. */
    public static Path requireNewOutput(Path output) throws FileAlreadyExistsException {
        Path destination = output.toAbsolutePath().normalize();
        if (Files.exists(destination, LinkOption.NOFOLLOW_LINKS))
            throw new FileAlreadyExistsException("report directory already exists: " + destination);
        return destination;
    }

    public static void write(ScanResult result, Path output) throws IOException {
        interrupted();
        Path destination = requireNewOutput(output);
        Path parent = destination.getParent();
        Files.createDirectories(parent);
        Path staging = Files.createTempDirectory(parent, ".justsimple-report-");
        References references=new References();
        try {
            try (Writer json = interruptible(Files.newBufferedWriter(staging.resolve("report.json"), StandardCharsets.UTF_8))) {
                JsonWriter out=new JsonWriter(json);
                references.json(result,out);out.flush();
                json.write('\n');
            }
            try (Writer markdown = interruptible(Files.newBufferedWriter(staging.resolve("report.md"), StandardCharsets.UTF_8))) {
                markdown(result, markdown,references);
            }
            try (Writer template = interruptible(Files.newBufferedWriter(staging.resolve("input-requirements.json"), StandardCharsets.UTF_8))) {
                JsonWriter out=new JsonWriter(template);references.inputTemplate(result,out);out.flush();template.write('\n');
            }
            interrupted();Files.move(staging, destination, StandardCopyOption.ATOMIC_MOVE);
        } catch (IOException | RuntimeException failure) {
            for (Path file : List.of(staging.resolve("report.json"), staging.resolve("report.md"), staging.resolve("input-requirements.json"), staging)) {
                try { Files.deleteIfExists(file); }
                catch (IOException | SecurityException cleanup) { failure.addSuppressed(cleanup); }
            }
            throw failure;
        }
    }

    /** Cancellation is checked before buffered writes as well as before publishing. */
    private static Writer interruptible(Writer writer) {
        return new FilterWriter(writer) {
            @Override public void write(int value)throws IOException {interrupted();out.write(value);}
            @Override public void write(char[] chars,int offset,int length)throws IOException {interrupted();out.write(chars,offset,length);}
            @Override public void write(String text,int offset,int length)throws IOException {interrupted();out.write(text,offset,length);}
            @Override public void flush()throws IOException {interrupted();out.flush();}
        };
    }
    private static void interrupted() {
        if(Thread.currentThread().isInterrupted())throw new CancellationException("report write interrupted");
    }

    private static void markdown(ScanResult result, Writer writer,References references) throws IOException {
        Text out = new Text(writer);
        out.append("# JustSimple static analysis\n\n");
        out.append("Report schema 4. V/G/C/Q references below identify values, missing conditions, paths and individual choices.\n\n");
        out.append("Mode: ").append(result.mode()).append("; execution: ").append(result.execution())
                .append("; outcome: ").append(result.outcome()).append(".\n\n")
                .append("Candidate chains describe static connections and their conditions. Target code was never executed. NO_FINDINGS is scoped to this scan.\n\n")
                .append("Locations use ASM instruction indexes (including labels/debug nodes), not byte offsets.\n\n")
                .append("Statistics: ").append(result.statistics()).append("\n\n");
        out.append("Input budgets: ").append(result.input().budgets()).append("\n\nAnalysis budgets: ").append(result.analysisBudgets())
                .append("; method instructions: ").append(result.methodInstructionBudget()).append("\n\n");
        out.append("## Inputs and coverage\n\n").append("Target JDK feature: ").append(result.input().jdkFeature()).append("\n\n");
        if (result.staticData().isPresent()) out.append("Static bindings: ").append(escape(result.staticData().get().toString())).append("\n\n");
        for (var artifact : result.input().artifacts()) out.append("- ").append(artifact.role()).append(" `").append(escape(artifact.location())).append("`\n");
        out.append("\n");
        for (String limitation : result.limitations()) out.append("- TRUNCATED: ").append(escape(limitation)).append("\n");
        for (String missing : result.missingClasses()) out.append("- Missing class: `").append(escape(missing)).append("`\n");
        for (String duplicate : result.input().duplicates()) out.append("- Duplicate: ").append(escape(duplicate)).append("\n");
        out.append("\n## Entries\n\n");
        for (var entry : result.entries()) {
            out.append("- `").append(escape(entry.method().id().toString())).append("`: ").append(escape(entry.boundary())).append("\n");
            for (String assumption : entry.assumptions()) out.append("  - Deployment: ").append(escape(assumption)).append("\n");
        }
        out.append("\n## Findings\n\n");
        for (Finding finding : result.findings()) {
            out.append("### ").append(finding.id()).append(" · ").append(finding.boundary()).append("\n\n")
                    .append("Entry: `").append(escape(finding.entry().method().id().toString())).append("`\n\n")
                    .append(escape(finding.detail())).append("\n\n");
            for (int id : finding.path()) {
                Relation relation = result.relations().get(id);
                Optional<ProofUse> support=finding.proof().stream().filter(p -> p.relation()==id).findFirst();
                out.append("- #").append(id).append(support.map(p -> "/S"+p.support()).orElse("/UNRESOLVED"))
                        .append(" ").append(support.map(p -> relation.supports().get(p.support()).evidence().name()).orElse("UNRESOLVED")).append(" ").append(relation.kind())
                        .append(" `").append(escape(relation.site().toString())).append("` → `")
                        .append(escape(relation.target().map(Object::toString).orElse("local binding"))).append("`\n")
                        .append("  - Receiver: ").append("V"+references.value(relation.receiver())).append("; args: ").append(relation.arguments().stream().map(atom -> "V"+references.value(atom)).toList()).append("\n");
            }
            if (!finding.supportingRelations().isEmpty()) out.append("\nData evidence: ").append(finding.proof().stream().filter(p -> finding.supportingRelations().contains(p.relation())).map(p -> "#"+p.relation()+"/S"+p.support()).toList()).append("\n");
            if (!finding.conditions().choices().isEmpty() || !finding.conditions().selections().isEmpty()) out.append("\nPath conditions: ").append("C"+references.condition(finding.conditions())).append("\n");
            if(!finding.gaps().isEmpty())out.append("\nRequired conditions: ").append(finding.gaps().stream().map(gap -> "G"+references.gap(gap)).toList()).append("\n");
            out.append("\n");
        }
        out.append("## Required input\n\n");
        out.append("Only demands emitted by analysis are listed. Candidate choices remain conditional; they are not supplied facts. JVM parameter slots and typed source paths identify the requested location.\n\n");
        out.append("[Unresolved input template](input-requirements.json) uses explicit UNKNOWN/UNRESOLVED markers and cannot be loaded as facts. Code-derived values stay in the evidence; supplied BINDING/ASSUMPTION/REFERENCE data retains its original basis above.\n\n");
        for(InputRequirement requirement:result.inputRequirements()) {
            var need=requirement.needed();
            out.append("- I").append(requirement.id()).append(" UNRESOLVED ").append(need.kind()).append(" `").append(escape(need.descriptor())).append("`\n")
                    .append("  - Entry: `").append(escape(requirement.entry().toString())).append("`; context: ").append(requirement.context()).append("; use: `").append(escape(requirement.use().toString())).append("`\n")
                    .append("  - Source: ").append(escape(requirement.source().map(source -> "S"+references.source(source)).orElse("not established"))).append("; subject: V").append(references.value(need.subject())).append("; slot: ").append(escape(need.slot().map(Object::toString).orElse("value itself"))).append("\n")
                    .append("  - Constraint: ").append(escape(need.reason())).append("; conditional choices: ").append(need.choices().stream().map(atom -> "V"+references.value(atom)).toList()).append("\n")
                    .append("  - Dependencies: ").append(requirement.dependencies()).append("; conditions: C").append(references.condition(requirement.conditions())).append("\n");
        }
        if(result.inputRequirements().isEmpty())out.append("No concrete input requirement was produced in the explored scope. Missing dependencies, unsupported behavior and budget frontiers may still prevent proof.\n");
        out.append("\n## Demand frontier\n\n");
        for(DemandFrontier frontier:result.demandFrontier()) {
            out.append("- ").append(frontier.state()).append(" context ").append(frontier.context()).append(" at `").append(escape(frontier.use().toString())).append("`: ").append(escape(frontier.detail())).append("\n")
                    .append("  - Origin: ").append(escape(frontier.origin().toString())).append("; conditions: C").append(references.condition(frontier.conditions())).append("\n");
            for(var candidate:frontier.candidates())out.append("  - Candidate source (requires binding): `").append(escape(candidate.toString())).append("`\n");
        }
        out.append("\n## Verified and conditional relations\n\n");
        for (Relation relation : result.relations()) {
            out.append("- #").append(relation.id()).append(" context ").append(relation.context()).append(" ").append(relation.kind())
                    .append(" `").append(escape(relation.site().toString())).append("` → `").append(escape(relation.target().map(Object::toString).orElse("local binding")))
                    .append("`: ").append(escape(relation.detail())).append("\n")
                    .append("  - Receiver: ").append("V"+references.value(relation.receiver())).append("; args: ").append(relation.arguments().stream().map(atom -> "V"+references.value(atom)).toList()).append("\n")
                    .append("  - Input: `").append(escape(relation.site().source())).append("`\n");
            for(int i=0;i<relation.supports().size();i++) {
                Support support=relation.supports().get(i);
                out.append("  - S").append(i).append(" ").append(support.evidence()).append("; joint dependencies: ").append(support.dependencies()).append("\n");
                for (var site : support.witnesses()) out.append("    - Bytecode witness: `").append(escape(site.toString())).append("` in `").append(escape(site.source())).append("`\n");
                if(!support.gaps().isEmpty())out.append("    - Required conditions: ").append(support.gaps().stream().map(gap -> "G"+references.gap(gap)).toList()).append("\n");
            }
        }
        out.append("\n## Breakpoints\n\n");
        for(Breakpoint point:result.breakpoints())out.append("- ").append(point.reason()).append(" context ").append(point.context()).append(" at `").append(escape(point.use().toString())).append("`; object ")
                .append(point.subject().map(value -> "V"+references.value(value)).orElse("unbound")).append("; slot ").append(escape(point.slot().map(Object::toString).orElse("unspecified")))
                .append("; known relations ").append(point.knownRelations()).append("; ").append(escape(point.detail())).append("\n");
        out.append("\n## Evidence references\n\n");
        for(var gap:references.gaps())out.append("- G").append(references.gap(gap)).append(" ").append(gap.kind()).append(": ").append(escape(gap.detail())).append(" (`").append(escape(gap.site().toString())).append("` in `").append(escape(gap.site().source())).append("`)\n");
        for(var value:references.values())out.append("- V").append(references.value(value)).append(" ").append(value.getClass().getSimpleName()).append(": ").append(escape(references.binding(value))).append("\n");
        for(var condition:references.conditions())out.append("- C").append(references.condition(condition)).append(" ").append(escape(references.conditionText(condition))).append("\n");
        for(var choice:references.choices())out.append("- Q").append(references.choice(choice)).append(" ").append(escape(references.choiceText(choice))).append("\n");
        for(var source:references.sources())out.append("- S").append(references.source(source)).append(" ").append(escape(references.sourceText(source))).append("\n");
        out.append("\n## Search hints (reference only)\n\n");
        for (var hint : result.hints()) out.append("- `").append(escape(hint.anchor().toString())).append("`: ").append(escape(hint.mechanism())).append("; ")
                .append(escape(hint.source())).append("; verify ").append(escape(hint.pendingRelations().toString())).append("\n");
    }

    /** Keeps formatting incremental; IOException retains its original cause. */
    private record Text(Writer writer) {
        Text append(Object value) throws IOException { writer.write(String.valueOf(value)); return this; }
    }

    private static String escape(String text) { return text.replace("`", "'").replace("\r", " ").replace("\n", " "); }
}
