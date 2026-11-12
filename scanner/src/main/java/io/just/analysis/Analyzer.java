package io.just.analysis;

import io.just.knowledge.EntryPoints.Mode;
import io.just.knowledge.EntryPoints.Entry;

import io.just.input.Inputs;
import io.just.input.StaticData;
import io.just.program.Program;
import io.just.program.SourceTrace;
import io.just.program.Program.*;
import io.just.knowledge.Mechanisms;
import io.just.knowledge.EntryPoints;
import io.just.knowledge.Mechanisms.*;
import io.just.knowledge.Values.*;
import io.just.knowledge.Values.ClassValue;
import io.just.knowledge.Values;
import io.just.analysis.ScanResult.*;
import io.just.analysis.ExecutionPoint.*;
import io.just.analysis.HeapStore.Cell;
import io.just.analysis.Iterations.Loop;
import io.just.analysis.Combinations.Combination;
import static io.just.program.Program.sources;
import static io.just.knowledge.ValueBindings.finiteBinding;
import static io.just.program.Program.exceptional;
import static io.just.analysis.JvmSemantics.safetyInputs;
import org.objectweb.asm.Opcodes;
import java.util.*;
import java.util.concurrent.CancellationException;
import java.util.function.Consumer;

/** One bounded, dependency-driven queue owns all derived facts for this scan. */
public final class Analyzer {
    public enum Stage { ENTRIES, KNOWLEDGE, ANALYSIS, RECOVERY }
    public record ScanProgress(Stage stage,int entries,int contexts,long steps,int relations,int queued) {}
    private static final Consumer<ScanProgress> NO_PROGRESS=progress -> {};
    public record Limits(int contexts, long steps, int depth, int relations, int findings, int alternatives) {
        public Limits {
            if (contexts < 1 || steps < 1 || depth < 1 || relations < 1 || findings < 1 || alternatives < 1)
                throw new IllegalArgumentException("analysis budgets must be positive");
        }
        public static Limits defaults() { return new Limits(5000, 200_000, 20, 30_000, 1000, 64); }
    }
    private record CallBinding(Atom receiver,List<Atom> arguments) { CallBinding {arguments=List.copyOf(arguments);} }
    private record ValueBinding(Atom value,Path path) {}
    private record ReceiverTarget(MethodId method,Optional<DefinedType> receiver) {}
    private record InvocationKey(int parent, Site call, MethodId target, Path path, int iteration, Phase phase, CallBinding binding,List<Integer> effects) {
        InvocationKey(int parent,Site call,MethodId target,Path path){this(parent,call,target,path,-1,new Startup(),new CallBinding(new Literal(null),List.of()),List.of());}
        InvocationKey(int parent,Site call,MethodId target,Path path,int iteration,Phase phase,CallBinding binding){this(parent,call,target,path,iteration,phase,binding,List.of());}
    }
    private record ObjectKey(int context, int instruction, String type, String role, int loader,int iteration, Phase phase,List<Integer> effects) {}
    private record ExternalField(int object, FieldId field) {}
    private record Initialization(int root,String owner,int loader) {}
    private record Registration(int context,Site site,MethodId target,Atom receiver,List<Atom> arguments,Path path,int iteration) {}
    private static final class Activation {
        final Invocation invocation;
        final Dispatch dispatch;
        final Observe observation;
        final Phase phase;
        final Set<Gap> gaps=new LinkedHashSet<>();
        final Set<Integer> dependencies=new LinkedHashSet<>();
        final Unit unit;
        Activation(Unit source,Invocation invocation,Deferred deferred,int id) {
            this.invocation=invocation;this.dispatch=deferred.dispatch();this.observation=deferred.observation();
            this.phase=deferred.timing()==Timing.ASYNCHRONOUS?new Asynchronous(id,new ExecutionPoint(source.state.id,source.action.site().instruction(),source.iteration.map(Iteration::index).orElse(-1),source.activation.<Phase>map(a -> a.phase).orElse(source.state.key.phase()),source.effects)):new Request(id);
            this.unit=new Unit(source.state,source.action);unit.iteration=source.iteration;unit.activation=Optional.of(this);
        }
    }
    private record Iteration(Loop loop,int index) {}
    private record Position(int instruction,int iteration) {}
    private record Carried(Value input,Edge loop,Value output) {}
    private record Control(Optional<Iteration> scope,Path path,Conditions.Paths paths,List<Unit> waiting) {}
    /** Enumeration progress is shared by proof variants; each candidate still checks its own path. */
    private record AlternativeScope(MethodId target,CallBinding binding,List<Integer> effects) {}
    private sealed interface Reachability permits PendingGuard, ImpossibleGuard, ActiveGuard {}
    private record PendingGuard() implements Reachability {}
    private record ImpossibleGuard() implements Reachability {}
    private record ActiveGuard(Path path) implements Reachability {}
    private sealed interface Progress permits Waiting, Finished {}
    private record Waiting() implements Progress {}
    private record Finished(Value value) implements Progress {}
    private sealed interface EffectResult permits Produced,CompletedVoid,Awaiting,Exceptional {}
    private record Produced(Value value) implements EffectResult {}
    private record CompletedVoid() implements EffectResult {}
    private record Awaiting() implements EffectResult {}
    private record Exceptional() implements EffectResult {}
    private enum EffectState { NORMAL, WAITING, EXCEPTIONAL }
    private record HeapQuery(ObjectValue object,Slot slot,HeapStore.Use use) {}
    private record ReturnedView(Value value,Value thrown,List<Optional<Value>> completions) {
        static ReturnedView of(State state){return new ReturnedView(state.returned,state.thrown,state.units.stream().map(u -> u.normal).toList());}
    }
    private record ModelView(Invocation invocation,Optional<Local> local,Map<HeapQuery,Value> reads,int definitions) {}
    private record EffectRequest(Invocation invocation,Local local,List<Gap> gaps,Set<Integer> dependencies,int depth,List<Integer> previous,List<ExceptionFlow> wrappers,List<Integer> position) {}
    private record EffectView(EffectRequest request,EffectResult result,Map<HeapQuery,Value> reads,Map<State,ReturnedView> returns,Map<Integer,Integer> supports,int definitions,int operations) {}
    /** The current local consumption only; its reads and actual callees determine invalidation. */
    private static final class Consumption {
        final Map<HeapQuery,Value> reads=new LinkedHashMap<>();final Set<State> callees=new LinkedHashSet<>();boolean incomplete;
    }
    private static final class State {
        final int id;
        final InvocationKey key;
        final Entry entry;
        final Facts facts;
        final List<Unit> units = new ArrayList<>();
        final Map<Integer, Unit> producers = new HashMap<>();
        final List<Loop> loops=new ArrayList<>();
        final Set<Unit> abruptUnits=new LinkedHashSet<>();
        final Map<Integer,Set<Unit>> handlerSources=new HashMap<>();
        final Map<Position,Unit> iterations=new HashMap<>();
        final Map<Origin, Set<Unit>> consumers = new HashMap<>();
        final Set<Unit> returnConsumers = new LinkedHashSet<>();
        final Map<Origin,Set<Backward>> reverseConsumers=new HashMap<>();
        final Set<Backward> returnDemands=new LinkedHashSet<>();
        final Map<Integer, Value> parameters = new HashMap<>();
        final Set<Gap> required = new LinkedHashSet<>();
        final Set<Unit> controlWaiters=new LinkedHashSet<>();
        Optional<Control> control=Optional.empty();
        final boolean compoundControl;
        final boolean mechanism;
        final int parentRelation;
        final SearchRanking.Progress ranking;
        Value returned = Value.BOTTOM;
        Value thrown = Value.BOTTOM;
        State(int id, InvocationKey key, Entry entry, Facts facts, int parentRelation,boolean mechanism,SearchRanking.Progress ranking) {
            this.id = id; this.key = key; this.entry = entry; this.facts = facts; this.parentRelation = parentRelation;
            this.mechanism=mechanism;this.ranking=ranking;
            compoundControl=facts.actions().stream().filter(a -> a instanceof Branch).count()>1
                    && facts.cfg().stream().noneMatch(e -> !e.exceptional() && e.to()<=e.from());
        }
    }
    private sealed interface Work permits Unit, Backward {}
    private record DemandKey(int context,Site use,Origin origin,Path path,int iteration) {}
    private static final class Backward implements Work {
        final DemandKey key;
        final int depth;
        final SearchRanking.Rank rank;
        Backward(DemandKey key,int depth,SearchRanking.Rank rank){this.key=key;this.depth=depth;this.rank=rank;}
    }
    private static final class Unit implements Work {
        final State state;
        final Action action;
        final Set<Unit> completionConsumers = new LinkedHashSet<>();
        Unit previousEffect;
        Progress progress = new Waiting();
        Optional<Value> normal=Optional.empty();
        Value thrown = Value.BOTTOM;
        final Set<Gap> prerequisites=new LinkedHashSet<>();
        final Set<Integer> controlDependencies=new LinkedHashSet<>();
        Optional<Iteration> iteration=Optional.empty();
        Optional<Path> executionPath=Optional.empty();
        Optional<Carried> carried=Optional.empty();
        Optional<Activation> activation=Optional.empty();
        final Combinations combinations=new Combinations();
        final Set<State> dataReturns=new LinkedHashSet<>();
        List<Integer> effects=List.of();
        final Map<AlternativeScope,Integer> alternativeTurns=new HashMap<>();
        final Map<ReceiverTarget,Integer> virtualSelections=new LinkedHashMap<>();
        Optional<ModelView> modelView=Optional.empty();Optional<EffectView> effectView=Optional.empty();
        Optional<Consumption> consumption=Optional.empty();
        Unit(State state, Action action) { this.state = state; this.action = action; }
    }

    private final Program program;
    private final Mechanisms knowledge;
    private final Limits limits;
    private final JvmSemantics jvm;
    private final CandidateBindings candidateBindings;
    private final List<State> states = new ArrayList<>();
    private final Map<InvocationKey, State> contexts = new LinkedHashMap<>();
    private final Map<ObjectKey, ObjectValue> objects = new HashMap<>();
    private final Map<ExternalField, ObjectValue> fields = new HashMap<>();
    private final Map<Initialization,List<State>> initializers=new HashMap<>();
    private final HeapStore heap;
    private record DefinitionOperation(ExecutionPoint point,Path path) {}
    private final Map<DefinedType,Map<DefinitionOperation,Unit>> definitions=new HashMap<>();
    private int definitionOperations;
    private final Conditions conditions;
    private final Map<Cell, Set<Unit>> readers = new HashMap<>();
    private final WorkQueue queue = new WorkQueue();
    private final Set<Work> pending = new HashSet<>();
    private final Map<DemandKey,Backward> demands=new LinkedHashMap<>();
    private record SourceQuery(MethodId method,Origin origin) {}
    private final Map<SourceQuery,SourceTrace.Plan> sourcePlans=new HashMap<>();
    private final Map<MethodId,Optional<Summaries.Template>> summaries=new HashMap<>();
    private final Map<Unit,Set<Backward>> demandReaders=new IdentityHashMap<>();
    private final Map<Cell,Set<Backward>> demandHeapReaders=new HashMap<>();
    private final Map<DemandKey,List<DemandFrontier>> frontiers=new LinkedHashMap<>();
    private long backwardQueries;
    private final SearchRanking ranking;
    private long rankingWork;
    private SearchRanking.Rank rank(Unit unit){return ranking.work(unit.state.ranking,Optional.of(unit.action).filter(Call.class::isInstance).map(Call.class::cast));}
    private final Set<Work> urgent=new LinkedHashSet<>();
    private final Map<Registration,Activation> registrations=new LinkedHashMap<>();
    private final ArrayDeque<Activation> deferred=new ArrayDeque<>();
    private final EvidenceGraph evidence;
    private final InputRequirements requirements;
    private final Set<String> limitations = new LinkedHashSet<>();
    private int nextObject;
    private long steps;
    private long unitsCreated;
    private long rootInstructionBudget;
    private final boolean demandGuidance;
    private long summaryApplications;
    private long refinementWork,combinationReuses;
    private long modelReuses,effectReuses;
    private boolean started;
    private Consumer<ScanProgress> observer=NO_PROGRESS;
    private Stage progressPhase;
    private int entryCount;
    private long nextProgress;

    public Analyzer(Program program, Mechanisms knowledge, Limits limits) {
        this(program,knowledge,limits,true);
    }
    public Analyzer(Program program, Mechanisms knowledge, Limits limits,boolean demandGuidance) {
        knowledge.requireProgram(program);
        this.demandGuidance=demandGuidance;
        this.program = program; this.knowledge = knowledge; this.limits = limits;
        this.conditions=new Conditions(program,knowledge);
        this.ranking=new SearchRanking(knowledge,program);
        this.evidence=new EvidenceGraph(limits.relations(),limits.findings(),limits.alternatives(),conditions);
        this.requirements=new InputRequirements(Math.min(2048,limits.relations()));
        this.heap=new HeapStore(program,conditions,limits.alternatives());
        this.jvm=new JvmSemantics(program);
        this.candidateBindings=new CandidateBindings(program);
    }

    public ScanResult scan(Mode mode, boolean guidance) {
        return scan(mode, guidance, Set.of());
    }

    public ScanResult scan(Mode mode, boolean guidance, Set<MethodId> selectedEntries) {
        return scan(mode,guidance,selectedEntries,Optional.empty());
    }

    public ScanResult scan(Mode mode, boolean guidance, Set<MethodId> selectedEntries, Optional<StaticData> data) {
        return scan(mode,guidance,selectedEntries,data,NO_PROGRESS);
    }

    /** Optional, read-only observations; default library calls do not emit progress or console output. */
    public ScanResult scan(Mode mode, boolean guidance, Set<MethodId> selectedEntries, Optional<StaticData> data, Consumer<ScanProgress> observer) {
        if(started)throw new IllegalStateException("Analyzer is single-use; create a new instance for each scan");
        this.observer=Objects.requireNonNull(observer);
        started=true;
        long started = System.nanoTime();
        progress(Stage.ENTRIES);
        Query<List<Entry>> discovered=new EntryPoints(program).find(mode,selectedEntries);
        List<Entry> entries=discovered.value().orElseThrow();
        rootInstructionBudget=limits.steps()/Math.max(2,entries.size());
        for(QueryIssue issue:discovered.pending())limit("entry discovery: "+issue.cause()+": "+issue.detail());
        if (!selectedEntries.isEmpty()) {
            entries = entries.stream().filter(e -> selectedEntries.contains(e.method().id())).toList();
            Set<MethodId> found = new HashSet<>();
            for (Entry entry : entries) found.add(entry.method().id());
            if (!found.containsAll(selectedEntries)) throw new InvalidInput("entry is not an eligible " + mode + " boundary: " + selectedEntries);
        }
        if (data.isPresent()) {
            StaticData.MethodName method=data.get().entry().method();
            if (entries.stream().noneMatch(e -> e.method().id().equals(new MethodId(method.owner(),method.name(),method.descriptor()))))
                throw new InvalidInput("static data entry is not an eligible boundary in this scan");
        }
        entryCount=entries.size();progress(Stage.KNOWLEDGE);
        Query<List<Hint>> suggested=knowledge.hints(guidance,entries.stream().map(e -> e.method().id()).collect(java.util.stream.Collectors.toSet()));
        List<Hint> hints=suggested.value().orElseThrow();
        for(QueryIssue issue:suggested.pending())limit("guidance discovery: "+issue.cause()+": "+issue.detail());
        Set<MethodId> anchors = new HashSet<>();
        for (Hint hint : hints) {
            anchors.add(hint.anchor());
        }
        ranking.configure(guidance,hints);
        List<Entry> scheduled = new ArrayList<>(entries);
        if (guidance) scheduled.sort(Comparator.comparing((Entry e) -> !anchors.contains(e.method().id())));
        progress(Stage.ANALYSIS);
        for (int index = 0; index < scheduled.size(); index++) {
            Entry entry = scheduled.get(index);
            MethodId method = entry.method().id();
            Site site = new Site(method, -1, -1, "analysis boundary");
            InvocationKey key = new InvocationKey(-index - 1, site, method, Path.EMPTY);
            State state = create(key, entry, -1);
            if (state == null) {limit("unexplored entry boundaries: "+(scheduled.size()-index));break;}
            int slot = 0;
            if (!entry.method().isStatic()) {
                state.parameters.put(slot, boundary(state,site,slot,object(state,-1,method.owner(),"entry receiver",false))); slot++;
            }
            for (ValueType type : program.signature(method).parameters()) {
                Atom argument = external(state, -slot - 2, type.descriptor(), "entry parameter slot " + slot);
                state.parameters.put(slot, boundary(state,site,slot,argument));
                slot += type.slots();
            }
            if (data.isPresent() && data.get().entry().method().equals(new StaticData.MethodName(method.owner(),method.name(),method.descriptor()))
                    && data.get().basis()!=StaticData.Basis.REFERENCE) seed(state,data.get());
            initialize(state);
            progress(Stage.ANALYSIS);
            if(steps>=limits.steps() && index+1<scheduled.size()) {limit("unexplored entry boundaries: "+(scheduled.size()-index-1));break;}
        }
        drain();
        progress(Stage.RECOVERY);
        return result(mode, entries, data, started);
    }

    private void progress(Stage phase) {
        if(observer==NO_PROGRESS)return;
        long now=System.nanoTime();
        if(phase==progressPhase && now<nextProgress)return;
        progressPhase=phase;nextProgress=now+2_000_000_000L;
        observer.accept(new ScanProgress(phase,entryCount,states.size(),steps,evidence.size(),queue.size()+deferred.size()));
    }

    private ScanResult result(Mode mode, List<Entry> entries, Optional<StaticData> data, long started) {
        int pendingWork=queue.size()+deferred.size();
        String workFrontier=evidence.size()>=limits.relations()?"relation budget: "+limits.relations():"work item budget: "+limits.steps();
        for(Work work:queue)if(work instanceof Backward query)frontiers.put(query.key,List.of(new DemandFrontier(query.key.context(),query.key.use(),query.key.origin(),query.key.path(),DemandState.BUDGET,List.of(),"backward query pending at "+workFrontier)));
        for (State state : states) {
            long waiting = state.units.stream().filter(u -> u.progress instanceof Waiting).count();
            if (waiting > 0 && pendingWork==0)
                limit("unresolved cyclic/local dependencies in " + state.key.target() + ": " + waiting + " instructions");
        }
        List<Finding> findings = evidence.findings(states.stream().map(state -> new EvidenceGraph.Context(state.key.parent(),state.parentRelation,state.entry,List.copyOf(state.required))).toList());
        List<Relation> relations=evidence.snapshot();List<InputRequirement> needs=requirements.snapshot(conditions::compatible);List<DemandFrontier> demandFrontier=new ArrayList<>(frontiers.values().stream().flatMap(Collection::stream).toList());
        record ProducerQuery(String descriptor,int loader) {}
        Map<ProducerQuery,Candidates> producers=new HashMap<>();
        for(InputRequirement need:needs)if(need.needed().kind()==NeedKind.RECEIVER_PRODUCER) {
            int loader=need.needed().subject() instanceof ObjectValue object?object.loader():0;
            Candidates sources=producers.computeIfAbsent(new ProducerQuery(need.needed().descriptor(),loader),key -> program.producers(key.descriptor(),key.loader()));
            demandFrontier.add(new DemandFrontier(need.context(),need.use(),new Producer(need.use().instruction()),need.conditions(),DemandState.UNRESOLVED,sources.sites(),
                    "constructor/factory uses are candidate sources; no same-object return binding is established: "+need.needed().descriptor()));
            if(sources.truncated()){limit("receiver producer frontier (128): "+need.needed().descriptor());demandFrontier.add(new DemandFrontier(need.context(),need.use(),new Producer(need.use().instruction()),need.conditions(),DemandState.BUDGET,sources.sites(),sources.scope()));}
            for(QueryIssue issue:sources.pending()) {
                demandFrontier.add(new DemandFrontier(need.context(),need.use(),new Producer(need.use().instruction()),need.conditions(),issue.cause()==QueryCause.BUDGET?DemandState.BUDGET:DemandState.MISSING_DEPENDENCY,sources.sites(),issue.detail()));
                if(issue.cause()==QueryCause.BUDGET)limit(issue.detail());
            }
        }
        List<Breakpoint> breakpoints=new ArrayList<>(Breakpoints.locate(relations,needs,demandFrontier));breakpoints.addAll(evidence.coverage());
        for(Work work:queue)if(work instanceof Unit unit)breakpoints.add(new Breakpoint(unit.state.id,unit.action.site(),unit.state.key.path(),Optional.empty(),Optional.empty(),List.of(),GapKind.BUDGET,Optional.empty(),Optional.empty(),"instruction pending at "+workFrontier));
        for(QueryIssue issue:ranking.issues())if(issue.cause()==QueryCause.BUDGET)limit("ranking discovery: "+issue.detail());
        Inputs.Summary input = program.inputSummary();
        limitations.addAll(input.limitations());
        limitations.addAll(program.limitations());
        limitations.addAll(heap.limitations());
        limitations.addAll(evidence.limitations());
        List<String> reported=new ArrayList<>(limitations.size()+1);
        if(pendingWork>0)reported.add(workFrontier+"; pending="+pendingWork);
        reported.addAll(limitations);
        return new ScanResult(mode, reported.isEmpty() ? Execution.FINISHED : Execution.TRUNCATED,
                findings.isEmpty() ? Outcome.NO_FINDINGS : Outcome.FINDINGS, input, data.map(StaticData::summary), limits, program.instructionLimit(), entries, ranking.hints(),
                relations, findings, reported, program.missingClasses(),
                new Statistics((System.nanoTime() - started) / 1_000_000, states.size(), steps,
                        heap.cells(), evidence.size(), findings.size(),backwardQueries,demandGuidance,summaryApplications,refinementWork,combinationReuses,rankingWork,states.stream().filter(state -> state.ranking.rank()!=SearchRanking.Rank.NONE).count(),modelReuses,effectReuses),needs,demandFrontier,List.copyOf(breakpoints));
    }

    /** One fair queue: a noisy entry cannot fill the FIFO ahead of every other entry's callees. */
    private final class WorkQueue implements Iterable<Work> {
        private enum Priority { RANKED, TARGET_MECHANISM, MECHANISM, ORDINARY }
        private record Root(int id,Priority priority) {}
        private final LinkedHashMap<Root,ArrayDeque<Work>> roots=new LinkedHashMap<>();
        private final double[] service=new double[Priority.values().length];
        private int size;private double floor;
        private Root rootId(Work work){State state=work instanceof Unit unit?unit.state:states.get(((Backward)work).key.context());
            boolean mechanism=state.mechanism || work instanceof Backward && demandGuidance || work instanceof Unit unit && (unit.activation.isPresent() || unit.action instanceof Call call && (Mechanisms.demands(call) || knowledge.isImpact(call.target())));
            SearchRanking.Rank rank=work instanceof Unit unit?rank(unit):((Backward)work).rank;
            Priority priority=rank.compareTo(SearchRanking.Rank.BOUND)>=0?Priority.RANKED:!mechanism?Priority.ORDINARY:program.type(state.facts.method().id().owner(),state.facts.method().id().loader()).filter(type -> type.role()==Inputs.Role.TARGET).isPresent()?Priority.TARGET_MECHANISM:Priority.MECHANISM;
            State origin=state;
            while(origin.key.parent()>=0 && states.get(origin.key.parent()).mechanism==origin.mechanism)origin=states.get(origin.key.parent());
            return new Root(origin.id,priority);}
        private ArrayDeque<Work> bucket(Work work) {
            Root id=rootId(work);
            if(roots.keySet().stream().noneMatch(root -> root.priority()==id.priority()))service[id.priority().ordinal()]=Math.max(service[id.priority().ordinal()],floor);
            return roots.computeIfAbsent(id,key -> new ArrayDeque<>());
        }
        void addLast(Work work){bucket(work).addLast(work);size++;}
        void addFirst(Work work){bucket(work).addFirst(work);size++;}
        Work removeFirst(){
            Root id=roots.keySet().stream().min(Comparator.comparingDouble(root -> service[root.priority().ordinal()])).orElseThrow();
            ArrayDeque<Work> bucket=roots.remove(id);Work work=bucket.removeFirst();if(!bucket.isEmpty())roots.put(id,bucket);size--;return work;}
        void consumed(Work work,long cost) {
            Priority priority=rootId(work).priority();
            int share=switch(priority){case RANKED -> 24;case TARGET_MECHANISM -> 22;case MECHANISM -> 7;case ORDINARY -> 1;};
            service[priority.ordinal()]+=(double)cost/share;
            floor=roots.keySet().stream().mapToDouble(root -> service[root.priority().ordinal()]).min().orElse(service[priority.ordinal()]);
        }
        void removeAll(Collection<Work> work){for(Work item:work){Root id=rootId(item);ArrayDeque<Work> bucket=roots.get(id);if(bucket!=null && bucket.remove(item)){size--;if(bucket.isEmpty())roots.remove(id);}}}
        int size(){return size;}boolean isEmpty(){return size==0;}
        public Iterator<Work> iterator(){return roots.values().stream().flatMap(Collection::stream).iterator();}
    }

    private void drain() {
        while ((!queue.isEmpty() || !deferred.isEmpty()) && steps<limits.steps() && evidence.size()<limits.relations()) {
            if (queue.isEmpty()) offer(deferred.removeFirst().unit);
            // A bounded FIFO turn keeps demand prioritization from starving queued work.
            int turn=(int)Math.min(Math.min(32,queue.size()),limits.steps()-steps);
            for(int i=0;i<turn && steps<limits.steps() && evidence.size()<limits.relations();i++) {
                if(Thread.currentThread().isInterrupted())throw new CancellationException("scan interrupted");
                Work work=queue.removeFirst();pending.remove(work);steps++;
                boolean ranked=(work instanceof Unit unit?rank(unit):((Backward)work).rank)!=SearchRanking.Rank.NONE;
                long consumed=steps;
                if(work instanceof Unit unit)execute(unit);else backward((Backward)work);
                long cost=steps-consumed+1;queue.consumed(work,cost);
                if(ranked)rankingWork+=cost;
            }
            if(demandGuidance && !urgent.isEmpty()) {
                List<Work> prioritized=urgent.stream().filter(pending::contains).toList();
                queue.removeAll(prioritized);for(int i=prioritized.size()-1;i>=0;i--)queue.addFirst(prioritized.get(i));urgent.clear();
            }
            progress(Stage.ANALYSIS);
        }
    }

    private Optional<Local> model(Unit unit,Invocation invocation) {
        Invocation bound=CandidateBindings.project(invocation,invocation.path());
        if(unit.consumption.isPresent())return knowledge.apply(bound,(object,slot) -> read(unit,object,slot));
        if(unit.modelView.filter(view -> view.definitions()==program.definitionCount() && view.invocation().equals(bound) && unchanged(unit,view.reads())).isPresent()) {
            modelReuses++;return unit.modelView.orElseThrow().local();
        }
        Map<HeapQuery,Value> reads=new LinkedHashMap<>();
        Optional<Local> local=knowledge.apply(bound,(object,slot) -> {
            Value value=read(unit,object,slot);reads.put(new HeapQuery(object,slot,use(unit,slot instanceof ResolvedObject)),value);return value;
        });
        unit.modelView=Optional.of(new ModelView(bound,local,Map.copyOf(reads),program.definitionCount()));return local;
    }
    private HeapStore.Use use(Unit unit,boolean ownWrites) {
        Path path=unit.executionPath.orElse(unit.state.key.path());return new HeapStore.Use(writer(unit),unit.action.site(),path,unit.state.facts.cfg(),ownWrites);
    }
    private boolean unchanged(Unit unit,Map<HeapQuery,Value> reads) {
        for(var prior:reads.entrySet()) {
            HeapQuery query=prior.getKey();HeapStore.Read current=heap.read(query.object(),query.slot(),query.use());
            for(Cell dependency:current.dependencies())readers.computeIfAbsent(dependency,k -> new LinkedHashSet<>()).add(unit);
            if(!current.value().equals(prior.getValue()))return false;
        }
        return true;
    }

    private Phase phase(Unit unit) { return unit.activation.<Phase>map(a -> a.phase).orElse(unit.state.key.phase()); }
    private ExecutionPoint writer(Unit unit) { return new ExecutionPoint(unit.state.id,unit.action.site().instruction(),iteration(unit),phase(unit),unit.effects); }

    private void defer(Unit source,Invocation invocation,Deferred deferred,List<Gap> gaps,Set<Integer> dependencies) {
        Dispatch dispatch=deferred.dispatch();
        Registration key=new Registration(source.state.id,source.action.site(),dispatch.target(),dispatch.receiver(),dispatch.arguments(),invocation.path(),iteration(source));
        Activation activation=registrations.get(key);
        boolean fresh=activation==null;
        if (fresh) {
            if (unitsCreated++>=limits.steps()) {limit("deferred registration instruction budget");return;}
            activation=new Activation(source,invocation,deferred,registrations.size());registrations.put(key,activation);
            this.deferred.addLast(activation);
        }
        boolean changed=activation.gaps.addAll(gaps) | activation.dependencies.addAll(dependencies);
        if (!fresh && changed) offer(activation.unit);
    }

    private Value boundary(State state,Site site,int slot,Atom atom) {
        InputSource source=new InputSource(state.key.target(),slot,List.of());
        if(atom instanceof ObjectValue object)atom=new ObjectValue(object.id(),object.type(),object.exact(),object.origin(),object.defaultFields(),Optional.of(source));
        return boundary(state,site,slot,atom,List.of());
    }
    private Value boundary(State state,Site site,int slot,Atom atom,List<Gap> gaps) {
        int id=relation(state.id,site,Kind.INPUT_BINDING,Optional.empty(),Evidence.PROVEN,new Literal(null),List.of(atom),List.of(),gaps,Path.EMPTY,"entry parameter slot "+slot,Set.of());
        return Value.of(atom).requiring(gaps).tracing(id<0?Set.of():Set.of(id));
    }

    private void seed(State state,StaticData data) {
        StaticBindings.Snapshot snapshot=StaticBindings.check(data,program,nextObject); nextObject=snapshot.nextId();
        Site site=new Site(state.key.target(),-1,-1,data.location());
        List<Gap> gaps=data.basis()==StaticData.Basis.BINDING?List.of():List.of(new Gap(GapKind.INPUT_BINDING,site,"supplied assumption: "+data.source()));
        for (StaticBindings.Assignment assignment:snapshot.assignments()) {
            Site source=new Site(state.key.target(),-1,-1,data.location()+"#"+assignment.pointer());
            int id=relation(state.id,source,Kind.INPUT_BINDING,Optional.empty(),gaps.isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,
                    assignment.object(),List.of(assignment.value()),List.of(),gaps,Path.EMPTY,"supplied static "+assignment.slot(),Set.of(),Optional.of(assignment.slot()));
            Value value=Value.of(assignment.value()).requiring(gaps).tracing(id<0?Set.of():Set.of(id));
            heap.seed(assignment.object(),assignment.slot(),value);
        }
        int slot=0;
        if (!state.facts.method().isStatic()) {
            state.parameters.put(slot,boundary(state,new Site(state.key.target(),-1,-1,data.location()+"#/entry/receiver"),slot,snapshot.receiver().orElseThrow(),gaps));slot++;
        }
        List<ValueType> types=program.signature(state.key.target()).parameters();
        for (int i=0;i<types.size();i++) { state.parameters.put(slot,boundary(state,new Site(state.key.target(),-1,-1,data.location()+"#/entry/arguments/"+i),slot,snapshot.arguments().get(i),gaps)); slot+=types.get(i).slots(); }
    }

    private void limit(String detail) { if (limitations.size() < 100) limitations.add(detail); }

    private State create(InvocationKey key, Entry entry, int relation) {
        if (states.size() >= limits.contexts()) { limit("invocation context budget: " + limits.contexts()); return null; }
        boolean mechanism=key.parent()>=0 && (states.get(key.parent()).mechanism || evidence.relation(relation).filter(edge -> switch(edge.kind()) {
            case DESERIALIZATION,CONTAINER_CALLBACK,REFLECTION,METHOD_HANDLE,DYNAMIC_CALL,HTTP_CALLBACK -> true;default -> false;
        }).isPresent());
        SearchRanking.Progress progress=SearchRanking.Progress.EMPTY;
        if(key.parent()>=0) {
            progress=ranking.advance(states.get(key.parent()).ranking,key.call(),key.target(),key.binding().receiver(),key.binding().arguments(),key.path(),evidence.relation(relation));
        }
        State state = new State(states.size(), key, entry, program.facts(key.target()), relation,mechanism,progress);
        states.add(state);
        heap.context(state.id,key.parent(),key.call().instruction(),key.iteration(),key.effects());
        contexts.put(key, state);
        for (Limitation gap : state.facts.limitations()) {
            GapKind kind = gap.cause() == CoverageCause.BUDGET ? GapKind.BUDGET : GapKind.UNSUPPORTED;
            state.required.add(new Gap(kind, key.call(), gap.detail()));
            if (kind == GapKind.BUDGET) limit(gap.detail() + ": " + key.target());
        }
        return state;
    }

    private void initialize(State state) {
        Unit previous = null;
        for (Action action : state.facts.actions()) {
            boolean scanLimit=unitsCreated>=limits.steps();
            if (scanLimit || state.key.parent()<0 && state.units.size()>=rootInstructionBudget) {
                String detail=scanLimit?"scheduled instruction budget: "+limits.steps()
                        :"entry instruction budget: "+rootInstructionBudget+" at "+state.key.target();
                Gap gap = new Gap(GapKind.BUDGET, action.site(), detail);
                state.required.add(gap);
                limit(gap.detail());
                state.returned = Value.of(new Truncated(gap.detail())).requiring(List.of(gap));
                break;
            }
            unitsCreated++;
            Unit unit = new Unit(state, action);
            state.units.add(unit);
            state.producers.put(action.site().instruction(), unit);
            previous=chain(unit,previous);
            subscribe(unit);
        }
        if (state.units.isEmpty()) state.returned = Value.of(new Unknown("method body unavailable")).requiring(List.copyOf(state.required));
        if(state.key.parent()>=0) {
            List<Work> ready=state.units.stream().filter(pending::contains).map(unit -> (Work)unit).toList();
            queue.removeAll(ready);for(int i=ready.size()-1;i>=0;i--)queue.addFirst(ready.get(i));
        }
    }

    private Unit chain(Unit unit,Unit previous) {
        Action action=unit.action;
        boolean activeUse=action instanceof Allocate || action instanceof ReadField read && read.receiver().origins().isEmpty();
        boolean memory=activeUse || action instanceof Call || action instanceof ReadField || action instanceof WriteField
                || action instanceof ReadArray || action instanceof WriteArray || action instanceof Returned;
        if (memory) {
            while(previous!=null && !precedes(previous,unit))previous=previous.previousEffect;
            unit.previousEffect=previous;
            if (previous!=null) previous.completionConsumers.add(unit);
        }
        return activeUse || action instanceof Call || action instanceof WriteField || action instanceof WriteArray?unit:previous;
    }
    private boolean precedes(Unit previous,Unit next) {
        List<Guard> before=next.state.facts.guards().getOrDefault(previous.action.site().instruction(),List.of());
        List<Guard> after=next.state.facts.guards().getOrDefault(next.action.site().instruction(),List.of());
        if(!after.containsAll(before) || after.stream().anyMatch(g -> g.kind()==GuardKind.HANDLER && !before.contains(g)))return false;
        if(previous.iteration.isPresent() && next.iteration.isPresent() && previous.iteration.get().loop().equals(next.iteration.get().loop())
                && previous.iteration.get().index()<next.iteration.get().index())return true;
        return !conditions.reachable(next.state.facts,Map.of(),false,previous.action.site().instruction()).contains(next.action.site().instruction());
    }
    private void subscribe(Unit unit) {
        State state=unit.state;
        if (exceptional(unit.action)) for (Handler handler:state.facts.handlers())
            if (handler.start()<=unit.action.site().instruction() && unit.action.site().instruction()<handler.end()) state.handlerSources.computeIfAbsent(handler.target(),k -> new LinkedHashSet<>()).add(unit);
        for(Origin origin:program.flow(state.key.target()).inputs().getOrDefault(unit.action.site().instruction(),Set.of()))
            state.consumers.computeIfAbsent(origin,k -> new LinkedHashSet<>()).add(unit);
        offer(unit);
    }

    private int iteration(Unit unit) { return unit.iteration.map(Iteration::index).orElse(-1); }
    private Optional<Loop> loop(State state,int instruction) { return state.loops.stream().filter(l -> l.start()<=instruction && instruction<=l.end()).findFirst(); }
    private Unit producer(Unit consumer,int instruction,boolean carried) {
        Optional<Loop> scope=loop(consumer.state,instruction);
        if (scope.isEmpty()) return consumer.state.producers.get(instruction);
        Loop plan=scope.get(); int index=plan.count()-1;
        if (consumer.iteration.isPresent() && consumer.iteration.get().loop().equals(plan)) {
            index=iteration(consumer);
            if (carried && instruction>=consumer.action.site().instruction()) index--;
        } else {
            OptionalInt exit=finiteExit(consumer,plan);
            Unit original=consumer.state.producers.get(instruction);
            if(exit.isEmpty() && original!=null && original.action instanceof Branch branch
                    && (plan.counterInitial()>=0 && branch.opcode()==Opcodes.IF_ICMPGE || branch.inputs().stream().flatMap(input -> input.origins().stream()).anyMatch(origin -> origin instanceof Producer value && consumer.state.producers.get(value.instruction())!=null && consumer.state.producers.get(value.instruction()).action instanceof Call call && call.target().owner().equals("java/util/Iterator") && call.target().name().equals("hasNext"))))index=plan.count();
            if(exit.isPresent()) {
                index=exit.getAsInt();
                while(index>=0) {
                    Unit candidate=consumer.state.iterations.get(new Position(instruction,index));
                    if(candidate==null || !(candidate.progress instanceof Finished done) || !done.value().empty())break;
                    index--;
                }
            }
        }
        Unit selected=consumer.state.iterations.get(new Position(instruction,index));
        if(carried && index>0 && selected!=null && selected.progress instanceof Finished done && done.value().empty()
                && program.flow(consumer.state.key.target()).inputs().entrySet().stream().anyMatch(use -> plan.start()<=use.getKey() && use.getKey()<=instruction && use.getValue().contains(new Producer(instruction)))) {
            while(index>0 && selected!=null && selected.progress instanceof Finished prior && prior.value().empty())selected=consumer.state.iterations.get(new Position(instruction,--index));
        }
        return selected;
    }

    private OptionalInt finiteExit(Unit consumer,Loop plan) {
        for(int iteration=0;iteration<plan.count();iteration++)for(Guard guard:consumer.state.facts.guards().getOrDefault(plan.end(),List.of())) {
            if(guard.kind()!=GuardKind.BRANCH)continue;
            Unit source=consumer.state.iterations.get(new Position(guard.branch(),iteration));
            if(source==null || !(source.action instanceof Branch branch) || !(source.progress instanceof Finished done))continue;
            Optional<Integer> taken=successor(source,branch);
            if(taken.isPresent() && taken.get()!=guard.successor()
                    && conditions.reachable(consumer.state.facts,Map.of(guard.branch(),new Conditions.Taken(taken.get())),false,taken.get()).contains(plan.end()+1)) {
                requireControl(consumer,evidence.control(source.state.id,source.action.site(),done.value(),consumer.state.key.path(),EvidenceGraph.Control.BRANCH,0),consumer.state.key.path());
                return OptionalInt.of(iteration);
            }
        }
        return OptionalInt.empty();
    }

    private void orderedLoop(Unit iterator,ObjectValue receiver) {
        State state=iterator.state;
        Value lengths=read(iterator,receiver,new Length(),true);
        Set<Integer> sizes=new LinkedHashSet<>();
        for (Bound bound:lengths.alternatives()) if (bound.atom() instanceof Literal value && value.value() instanceof Integer size) sizes.add(size);
        if (sizes.size()!=1) {
            if(receiver.source().isPresent())Iterations.plan(state.facts,iterator.action.site().instruction(),receiver.id(),Math.min(8,limits.alternatives()),state.loops).ifPresent(plan -> {
                limit("symbolic iterator prefix ("+plan.count()+") at "+iterator.action.site());instantiate(iterator,plan.asPrefix(),iterator);
            });
            return;
        }
        int count=sizes.iterator().next();
        int available=0;
        if(count>=0)while(available<Math.min(count,64) && !read(iterator,receiver,new Index(available),true).empty())available++;
        if(available==0 && count>0)return; // Unordered summaries continue through the generic loop.
        boolean prefix=available<count;
        if(prefix){limit("iterator member prefix ("+available+") at "+iterator.action.site());count=available;}

        Optional<Loop> candidate=Iterations.plan(state.facts,iterator.action.site().instruction(),receiver.id(),count,state.loops);
        if(candidate.isPresent()) {
            Loop plan=candidate.get();
            if(count<0 || count>64) {limit("finite iteration budget (64) at "+iterator.action.site());return;}
            instantiate(iterator,prefix?plan.asPrefix():plan,iterator);
        }
    }
    private void instantiate(Unit iterator,Loop plan,Unit initialEffect) {
            State state=iterator.state;int count=plan.count();
            if(plan.prefix())for(Unit after:state.units)if(after.action.site().instruction()>plan.end())after.prerequisites.add(new Gap(GapKind.BUDGET,iterator.action.site(),"loop exit lies beyond the symbolic iterator prefix"));
            List<Unit> body=state.units.stream().filter(u -> plan.start()<=u.action.site().instruction() && u.action.site().instruction()<=plan.end()).toList();
            state.loops.add(plan);
            Unit previous=initialEffect;
            for (int index=0;index<=count;index++) for (Unit original:body) {
                if (index>0 && unitsCreated++>=limits.steps()) { limit("finite iteration instruction budget"); return; }
                Unit unit=index==0?original:new Unit(state,original.action);
                if (index>0) state.units.add(unit);
                unit.iteration=Optional.of(new Iteration(plan,index));
                state.iterations.put(new Position(unit.action.site().instruction(),index),unit);
                previous=chain(unit,previous); subscribe(unit);
            }
            Unit finalEffect=initialEffect;
            if (count>0) for (Unit original:body) if (original.action instanceof Call || original.action instanceof WriteField || original.action instanceof WriteArray)
                finalEffect=state.iterations.get(new Position(original.action.site().instruction(),count-1));
            for (Unit unit:state.units) if (unit.action.site().instruction()>plan.end() && unit.iteration.isEmpty() && unit.previousEffect!=null
                    && loop(state,unit.previousEffect.action.site().instruction()).filter(plan::equals).isPresent()) {
                unit.previousEffect=finalEffect; finalEffect.completionConsumers.add(unit);
            }
    }

    private void offer(Work work) {if(pending.add(work))queue.addLast(work);}

    private void demand(State state,Site use,Origin origin,Path path,int iteration,int depth) {
        demand(state,use,origin,path,iteration,depth,SearchRanking.Rank.NONE);
    }
    private void demand(State state,Site use,Origin origin,Path path,int iteration,int depth,SearchRanking.Rank rank) {
        DemandKey key=new DemandKey(state.id,use,origin,path,iteration);
        if(demands.containsKey(key))return;
        if(depth>32 || demands.size()>=limits.steps()) {
            frontiers.put(key,List.of(new DemandFrontier(state.id,use,origin,path,DemandState.BUDGET,List.of(),"backward context/source budget")));limit("backward context/source budget");return;
        }
        Backward query=new Backward(key,depth,rank);demands.put(key,query);offer(query);
    }
    private Unit demandProducer(State state,int instruction,int iteration) {
        Optional<Loop> loop=loop(state,instruction);
        if(loop.isPresent())return state.iterations.get(new Position(instruction,iteration<0?Math.max(0,loop.get().count()-1):iteration));
        return state.producers.get(instruction);
    }
    private void watch(Backward query,Unit producer) {
        if(producer==null)return;demandReaders.computeIfAbsent(producer,k -> new LinkedHashSet<>()).add(query);
        if(producer.progress instanceof Waiting){offer(producer);if(demandGuidance)urgent.add(producer);}
    }
    private void frontier(Backward query,DemandState reason,List<Site> candidates,String detail) {
        frontiers.computeIfAbsent(query.key,k -> new ArrayList<>()).add(new DemandFrontier(query.key.context(),query.key.use(),query.key.origin(),query.key.path(),reason,candidates,detail));
    }
    private List<Site> candidates(Backward query,Candidates candidates) {
        if(candidates.truncated()){frontier(query,DemandState.BUDGET,candidates.sites(),"syntactic candidate index truncated: "+candidates.scope());limit("syntactic candidate instruction budget (200000)");}
        for(QueryIssue issue:candidates.pending()) {
            frontier(query,issue.cause()==QueryCause.BUDGET?DemandState.BUDGET:DemandState.MISSING_DEPENDENCY,candidates.sites(),issue.detail());
            if(issue.cause()==QueryCause.BUDGET)limit(issue.detail());
        }
        return candidates.sites();
    }
    private void required(Backward query,Atom subject,Optional<Slot> slot,String descriptor,Collection<Integer> dependencies) {
        if(!requirements.add(query.key.context(),states.get(query.key.context()).entry.method().id(),query.key.use(),query.key.path(),new InputNeed(subject,slot,NeedKind.VALUE,descriptor,List.of(),"value needed by this backward source query"),dependencies))limit("input requirement budget");
    }
    private void backward(Backward query) {
        backwardQueries++;frontiers.remove(query.key);State state=states.get(query.key.context());
        SourceTrace.Plan plan = sourcePlans.computeIfAbsent(new SourceQuery(state.key.target(), query.key.origin()),
                key -> SourceTrace.query(program, key.method(), key.origin(), 128).value().orElseThrow().plan());
        if(plan.cyclic() && query.key.origin() instanceof Producer origin) {
            Unit source=demandProducer(state,origin.instruction(),query.key.iteration());
            if(source==null || source.progress instanceof Waiting || ((Finished)source.progress).value().alternatives().stream().anyMatch(b -> b.atom() instanceof Unknown || b.atom() instanceof Truncated))frontier(query,DemandState.CYCLE,List.of(),"bytecode source cycle has no resolved value at this frontier");
        }
        if(plan.truncated()){frontier(query,DemandState.BUDGET,List.of(),"backward method frontier (128 origins)");limit("backward method frontier (128 origins)");}
        for(int instruction:plan.producers())watch(query,demandProducer(state,instruction,query.key.iteration()));
        for(Parameter parameter:plan.parameters()) {
            state.reverseConsumers.computeIfAbsent(parameter,k -> new LinkedHashSet<>()).add(query);
            if(state.key.parent()>=0 && evidence.relation(state.parentRelation).map(r -> r.kind()==Kind.DIRECT_CALL || r.kind()==Kind.VIRTUAL_CALL).orElse(false)) {
                State parent=states.get(state.key.parent());Unit caller=demandProducer(parent,state.key.call().instruction(),state.key.iteration());
                if(caller!=null && caller.action instanceof Call actual) {
                    Sources inputs=new Sources(Set.of());int slot=0;
                    if(!state.facts.method().isStatic()){if(parameter.slot()==0)inputs=actual.receiver();slot=1;}
                    List<ValueType> types=program.signature(state.key.target()).parameters();
                    for(int i=0;i<types.size() && i<actual.arguments().size();i++){if(slot==parameter.slot())inputs=actual.arguments().get(i);slot+=types.get(i).slots();}
                    for(Origin origin:inputs.origins())demand(parent,query.key.use(),origin,query.key.path(),state.key.iteration(),query.depth+1,query.rank);
                }
            }
            Value value=state.parameters.getOrDefault(parameter.slot(),Value.BOTTOM).under(query.key.path());
            if(state.key.parent()>=0 && evidence.relation(state.parentRelation).filter(r -> r.kind()!=Kind.DIRECT_CALL && r.kind()!=Kind.VIRTUAL_CALL).isPresent()) {
                // Dynamic effects already supply the callee tuple. Outer API operand ordinals differ.
                Optional<Atom> selected=parameter.slot()==0 && !state.facts.method().isStatic()?Optional.of(state.key.binding().receiver()):Optional.empty();
                int slot=state.facts.method().isStatic()?0:1;
                List<ValueType> types=program.signature(state.key.target()).parameters();
                for(int i=0;i<types.size();i++) {
                    ValueType type=types.get(i);
                    if(slot==parameter.slot())selected=Optional.of(state.key.binding().arguments().get(i));slot+=type.slots();
                }
                if(selected.isPresent() && Values.source(selected.get()).isPresent())for(Bound bound:value.alternatives())
                    if(Values.source(bound.atom()).equals(Values.source(selected.get()))) {
                        String descriptor=bound.atom() instanceof ExternalValue external?external.descriptor():bound.atom() instanceof ObjectValue object?object.type().startsWith("[")?object.type():"L"+object.type()+";":"Ljava/lang/Object;";
                        required(query,bound.atom(),Optional.empty(),descriptor,bound.dependencies());
                    }
            }
            if(value.empty()){frontier(query,DemandState.MISSING_CALLER,candidates(query,program.callers(state.key.target())),"parameter has no actual caller binding in this context");continue;}
            for(Bound bound:value.alternatives())if(Values.source(bound.atom()).isPresent()) {
                frontier(query,DemandState.EXTERNAL,List.of(),"entry value remains an external boundary; caller control is not established");
                if(bound.atom() instanceof ExternalValue external)required(query,external,Optional.empty(),external.descriptor(),bound.dependencies());
                else if(bound.atom() instanceof ObjectValue object && object.type().equals("java/lang/String"))required(query,object,Optional.empty(),"Ljava/lang/String;",bound.dependencies());
            }
        }
        for(Call call:plan.returns()) {
            Unit source=demandProducer(state,call.site().instruction(),query.key.iteration());watch(query,source);
            List<State> children=(source==null?java.util.stream.Stream.<State>empty():source.dataReturns.stream()).filter(s -> s.key.parent()==state.id && s.key.call().equals(call.site()) && s.key.path().and(query.key.path()).isPresent() && (query.key.iteration()<0 || s.key.iteration()==query.key.iteration())).toList();
            if(children.isEmpty()) {
                if(source==null || source.progress instanceof Waiting)frontier(query,DemandState.UNRESOLVED,candidates(query,program.callers(call.target())),"call result awaits an actual dispatch/return; syntax candidates do not bind it");
                else if(((Finished)source.progress).value().alternatives().stream().anyMatch(b -> b.atom() instanceof Unknown || b.atom() instanceof Truncated))frontier(query,DemandState.UNRESOLVED,List.of(call.site()),"call result has no supported concrete producer");
            }
            for(State child:children) {
                child.returnDemands.add(query);
                for(Unit returned:child.units)if(returned.action instanceof Returned action)for(Origin origin:action.value().origins())demand(child,query.key.use(),origin,child.key.path(),iteration(returned),query.depth+1,query.rank);
            }
        }
        for(ReadField field:plan.fields()) {
            Unit use=demandProducer(state,field.site().instruction(),query.key.iteration());if(use==null)continue;
            FieldId actual=program.field(field.field()).orElse(field.field());
            Value receivers=field.receiver().origins().isEmpty()?Value.of(staticObject(state,actual.owner(),actual.loader())):resolve(use,field.receiver());
            for(Bound bound:receivers.under(query.key.path()).alternatives())if(bound.atom() instanceof ObjectValue object)backwardSlot(query,use,object,new Field(actual),actual.descriptor(),Optional.of(actual));
        }
        for(ReadArray array:plan.elements()) {
            Unit use=demandProducer(state,array.site().instruction(),query.key.iteration());if(use==null)continue;
            Value indices=resolve(use,array.index());
            for(Bound bound:resolve(use,array.array()).under(query.key.path()).alternatives())if(bound.atom() instanceof ObjectValue object)for(Bound index:indices.alternatives())backwardSlot(query,use,object,index(index.atom()),object.type().startsWith("[")?object.type().substring(1):"Ljava/lang/Object;",Optional.empty());
        }
        for(Origin origin:plan.unresolved())frontier(query,origin instanceof LimitedOrigin?DemandState.BUDGET:DemandState.UNRESOLVED,List.of(),"unsupported or unavailable bytecode source: "+origin);
    }
    private void backwardSlot(Backward query,Unit use,ObjectValue object,Slot slot,String descriptor,Optional<FieldId> candidateField) {
        Cell cell=new Cell(object.id(),slot);demandHeapReaders.computeIfAbsent(cell,k -> new LinkedHashSet<>()).add(query);
        Value value=read(use,object,slot).under(query.key.path());
        if(!value.empty() && value.alternatives().stream().allMatch(b -> finiteBinding(b.atom())))return;
        List<Site> candidates=candidateField.map(field -> candidates(query,program.fieldWriters(field))).orElse(List.of());
        if(value.empty() && !object.defaultFields()) {
            required(query,object,Optional.of(slot),descriptor,Set.of());frontier(query,DemandState.EXTERNAL,candidates,"same-object slot has no visible value; candidate writes are not bindings");
        }
        for(ExecutionPoint writer:heap.writers(object,slot))if(writer.context()>=0) {
            State scope=states.get(writer.context());Unit producer=demandProducer(scope,writer.instruction(),writer.iteration());watch(query,producer);
            if(producer!=null) {
                Sources source=producer.action instanceof WriteField field?field.value():producer.action instanceof WriteArray array?array.value():new Sources(Set.of());
                for(Origin origin:source.origins())demand(scope,query.key.use(),origin,query.key.path(),writer.iteration(),query.depth+1,query.rank);
            }
        }
    }

    private void finish(Unit unit, Value value) {
        long supports=evidence.derivations();
        Value limited = bounded(evidence.compact(unit.state.id,unit.action.site(),value.requiring(List.copyOf(unit.prerequisites)).tracing(unit.controlDependencies)), unit.action.site());
        Value old = unit.progress instanceof Finished complete ? complete.value() : Value.BOTTOM;
        Value joined = bounded(evidence.compact(unit.state.id,unit.action.site(),old.merge(limited)), unit.action.site());
        boolean first = unit.progress instanceof Waiting;
        if (!first && old.equals(joined) && evidence.derivations()==supports) return;
        unit.progress = new Finished(joined);
        boolean newValue=hasNewBinding(old,joined);
        boolean later=unit.state.control.flatMap(Control::scope).filter(scope -> unit.iteration.filter(i -> i.loop().equals(scope.loop()) && i.index()>scope.index()).isPresent()).isPresent();
        if(!later)unit.state.control=Optional.empty();
        for(Backward reader:demandReaders.getOrDefault(unit,Set.of()))offer(reader);
        if (unit.activation.isPresent()) return;
        if (unit.action instanceof Branch) {
            unit.state.control=Optional.empty();
            for (Unit consumer:unit.state.controlWaiters) offer(consumer);
            unit.state.controlWaiters.clear();
        }
        for (Unit consumer : unit.state.consumers.getOrDefault(new Producer(unit.action.site().instruction()), Set.of())) {offer(consumer);if(demandGuidance && newValue)urgent.add(consumer);}
        for (Unit consumer : unit.completionConsumers) offer(consumer);
        if(!unit.state.thrown.empty() && unit.state.units.stream().allMatch(u -> u.progress instanceof Finished))
            for(Unit consumer:unit.state.returnConsumers)offer(consumer);
        for (Handler handler:unit.state.facts.handlers()) if (handler.start()<=unit.action.site().instruction() && unit.action.site().instruction()<handler.end())
            for (Unit consumer:unit.state.consumers.getOrDefault(new Producer(handler.target()),Set.of())) offer(consumer);
    }

    private Value bounded(Value value, Site site) {
        if (value.alternatives().size() <= limits.alternatives()) return value;
        limit("value alternative budget at " + site);
        // Keep the frontier explicitly uncertain instead of silently dropping later values.
        return value.limited(limits.alternatives(),new Gap(GapKind.BUDGET,site,"value alternative budget: "+limits.alternatives()));
    }
    private static boolean hasNewBinding(Value old,Value added) {
        if(old.empty())return !added.empty();
        Set<Atom> known=new HashSet<>();Set<ValueBinding> bindings=new HashSet<>();
        for(Bound bound:old.alternatives()) {known.add(bound.atom());if(finiteBinding(bound.atom()))bindings.add(new ValueBinding(bound.atom(),bound.path()));}
        // A singleton can reach the same consumer through a newly established return path.
        return added.alternatives().stream().anyMatch(bound -> !known.contains(bound.atom())
                || finiteBinding(bound.atom()) && !bindings.contains(new ValueBinding(bound.atom(),bound.path())));
    }
    private Value merge(Unit unit,Value current,Value added) {
        Value joined=current.merge(added);
        return joined.alternatives().size()<=limits.alternatives()?joined:bounded(evidence.compact(unit.state.id,unit.action.site(),joined),unit.action.site());
    }

    private Value resolve(Unit consumer, Sources sources) {
        Optional<Value> counter=Iterations.counter(sources,consumer.iteration.map(Iteration::loop),iteration(consumer));
        if(counter.isPresent())return counter.get();
        State state = consumer.state;
        Value result = Value.BOTTOM;
        for (Origin origin : sources.origins()) {
            Value value;
            if (origin instanceof Parameter parameter) {
                if(consumer.iteration.isPresent() && iteration(consumer)>0 && sources.origins().stream().anyMatch(o -> o instanceof Producer p && p.instruction()>=consumer.action.site().instruction() && p.instruction()<=consumer.iteration.get().loop().end()))continue;
                value=state.parameters.getOrDefault(parameter.slot(),Value.BOTTOM);
            }
            else if (origin instanceof Producer producer) {
                Optional<Loop> carriedLoop=consumer.iteration.map(Iteration::loop);
                if (carriedLoop.isPresent() && iteration(consumer)>0 && producer.instruction()<carriedLoop.get().start()
                        && sources.origins().stream().anyMatch(o -> o instanceof Producer p && p.instruction()>=consumer.action.site().instruction()
                            && p.instruction()<=carriedLoop.get().end())) continue;
                if (consumer.iteration.isEmpty()) {
                    boolean fromExecutedLoop=sources.origins().stream().anyMatch(o -> o instanceof Producer p && loop(state,p.instruction()).filter(l -> l.count()>0 && consumer.action.site().instruction()>l.end()).isPresent());
                    if (fromExecutedLoop && loop(state,producer.instruction()).isEmpty()) {
                        Optional<Loop> previousLoop=state.loops.stream().filter(l -> l.end()<consumer.action.site().instruction()).max(Comparator.comparingInt(Loop::end));
                        if (previousLoop.isPresent() && producer.instruction()<previousLoop.get().start()
                                && state.facts.actions().stream().noneMatch(a -> a instanceof Branch && a.site().instruction()>previousLoop.get().end() && a.site().instruction()<consumer.action.site().instruction())) continue;
                    }
                }
                Unit unit = producer(consumer,producer.instruction(),true);
                value = unit != null && unit.progress instanceof Finished complete ? complete.value() : Value.BOTTOM;
                if (!value.empty() && consumer.iteration.isEmpty() && producer.instruction() >= consumer.action.site().instruction()) {
                    Optional<Edge> loop = state.facts.cfg().stream().filter(e -> !e.exceptional()
                            && e.to() <= consumer.action.site().instruction() && e.from() >= producer.instruction()).findFirst();
                    if (loop.isPresent()) value = acrossIterations(consumer,value,loop.get());
                }
                if (unit!=null) {
                    Set<Bound> selected=new LinkedHashSet<>();
                    Map<Atom,Integer> elements=new LinkedHashMap<>();
                    ObjectChoice choice=new ObjectChoice(state.id,producer.instruction(),iteration(unit));
                    if (value.alternatives().stream().map(Bound::atom).distinct().limit(2).count()>1)
                        conditions.uncertain(choice,new Gap(GapKind.CONTROL_CONDITION,unit.action.site(),"object selection among multiple possible values at this producer"));
                    if(value.alternatives().stream().filter(b -> b.atom() instanceof Reflected).map(Bound::atom).distinct().limit(2).count()>1)
                        conditions.uncertain(new ElementChoice(state.id,producer.instruction(),iteration(unit)),new Gap(GapKind.CONTROL_CONDITION,unit.action.site(),"metadata element selection is conditional"));
                    for (Bound bound:value.alternatives()) {
                        if (bound.atom() instanceof ObjectValue object)
                            bound.path().with(choice,object.id()).ifPresent(p -> selected.add(new Bound(object,p,bound.gaps(),bound.dependencies())));
                        else if(bound.atom() instanceof Reflected) {
                            int position=elements.computeIfAbsent(bound.atom(),k -> elements.size());
                            bound.path().with(new ElementChoice(state.id,producer.instruction(),iteration(unit)),position).ifPresent(p -> selected.add(new Bound(bound.atom(),p,bound.gaps(),bound.dependencies())));
                        } else selected.add(bound);
                    }
                    value=new Value(selected);
                }
            } else if (origin instanceof ExceptionOrigin exception) {
                value=caught(state,exception.handler()).values();
            } else if (origin instanceof LimitedOrigin) {
                value = Value.of(new Truncated("method value origin budget"))
                        .requiring(List.of(new Gap(GapKind.BUDGET, state.key.call(), "method value origin budget")));
            } else value = Value.of(new Unknown(((UnknownOrigin) origin).reason()))
                    .requiring(List.of(new Gap(GapKind.UNSUPPORTED, state.key.call(), ((UnknownOrigin) origin).reason())));
            result = bounded(result.merge(value), state.key.call());
        }
        return result;
    }

    private Value acrossIterations(Unit consumer,Value value,Edge loop) {
        Optional<Carried> previous=consumer.carried.filter(item -> item.input()==value && item.loop().equals(loop));
        if(previous.isPresent())return previous.get().output();
        State state=consumer.state;Site use=consumer.action.site();
        Set<Bound> result = new LinkedHashSet<>();
        Gap gap = new Gap(GapKind.CONTROL_CONDITION, use, "loop-carried value; exact iteration order is not established");
        for (Bound bound : value.alternatives()) {
            Map<ChoiceKey, Integer> retained = bound.path().choices();
            for (var choice : bound.path().choices().entrySet()) {
                State scope = states.get(choice.getKey().context());
                while (scope.id != state.id && scope.key.parent() >= 0 && scope.key.parent() != state.id)
                    scope = states.get(scope.key.parent());
                int position = scope.id == state.id ? choice.getKey().instruction()
                        : scope.key.parent() == state.id ? scope.key.call().instruction() : -1;
                if(position>=loop.to() && position<=loop.from()) {
                    if(retained==bound.path().choices())retained=new LinkedHashMap<>(retained);
                    retained.remove(choice.getKey());
                }
            }
            result.add(new Bound(bound.atom(),retained==bound.path().choices()?bound.path():bound.path().retainingChoices(retained),union(bound.gaps(),List.of(gap)),bound.dependencies()));
        }
        Value output=new Value(result);consumer.carried=Optional.of(new Carried(value,loop,output));return output;
    }

    private BranchKey branchKey(State state,int instruction,Optional<Iteration> iteration) {
        boolean invariant=iteration.isPresent() && state.producers.get(instruction)!=null && state.producers.get(instruction).action instanceof Branch branch
                && branch.inputs().stream().flatMap(input -> input.origins().stream()).noneMatch(origin -> origin instanceof Producer p && iteration.get().loop().start()<=p.instruction() && p.instruction()<=iteration.get().loop().end());
        return new BranchKey(state.id,instruction,invariant?-1:iteration.map(Iteration::index).orElse(-1));
    }

    private Reachability precedingIteration(Unit consumer,Path path) {
        Iteration current=consumer.iteration.orElseThrow();Loop loop=current.loop();int previous=current.index()-1;
        Optional<Iteration> scope=Optional.of(new Iteration(loop,previous));
        Optional<Control> cached=consumer.state.control.filter(c -> c.scope().equals(scope) && c.path().equals(path));
        if(cached.isPresent())return iterationControl(consumer,cached.get());
        Map<Integer,Conditions.Decision> decisions=new HashMap<>();List<Unit> waiting=new ArrayList<>();
        for(Unit source:consumer.state.units)if(source.iteration.filter(i -> i.loop().equals(loop) && i.index()==previous).isPresent()) {
            int instruction=source.action.site().instruction();
            if(source.progress instanceof Waiting || source.progress instanceof Finished done && done.value().empty() && source.thrown.empty()) {
                decisions.put(instruction,new Conditions.Pending());waiting.add(source);
            } else if(source.progress instanceof Finished done && done.value().empty())decisions.put(instruction,new Conditions.Taken(-1));
            else if(source.action instanceof Branch branch) {
                Integer selected=path.choices().get(branchKey(source.state,instruction,source.iteration));
                decisions.put(instruction,selected!=null?new Conditions.Taken(selected):successor(source,branch).<Conditions.Decision>map(Conditions.Taken::new).orElseGet(Conditions.Unknown::new));
            }
        }
        Conditions.Paths paths=new Conditions.Paths(conditions.reachable(consumer.state.facts,decisions,false,-1,loop.start()),conditions.reachable(consumer.state.facts,decisions,true,-1,loop.start()),true);
        Control result=new Control(scope,path,paths,List.copyOf(waiting));consumer.state.control=Optional.of(result);return iterationControl(consumer,result);
    }
    private Reachability iterationControl(Unit consumer,Control control) {
        Loop loop=control.scope().orElseThrow().loop();
        if(!control.paths().possible().contains(loop.end()))return new ImpossibleGuard();
        if(!control.paths().ready().contains(loop.end())) {
            for(Unit source:control.waiting())source.completionConsumers.add(consumer);consumer.state.controlWaiters.add(consumer);return new PendingGuard();
        }
        consumer.prerequisites.add(new Gap(GapKind.CONTROL_CONDITION,new Site(consumer.state.key.target(),loop.end(),-1,consumer.action.site().source()),"normal completion of the preceding loop iteration is conditional"));
        return new ActiveGuard(consumer.state.key.path());
    }

    private Reachability guard(Unit unit) {
        if(unit.iteration.filter(i -> i.loop().prefix() && i.index()>=i.loop().count()).isPresent())return new ImpossibleGuard();
        if (unit.activation.isPresent()) return new ActiveGuard(unit.activation.get().invocation.path());
        Path path = unit.state.key.path();
        if(unit.iteration.isPresent() && iteration(unit)>0) {
            Loop loop=unit.iteration.get().loop();int previous=iteration(unit)-1;
            for(Guard continuation:unit.state.facts.guards().getOrDefault(loop.end(),List.of())) {
                Unit source=unit.state.iterations.get(new Position(continuation.branch(),previous));
                if(source==null)continue;
                if(source.progress instanceof Waiting){source.completionConsumers.add(unit);unit.state.controlWaiters.add(unit);return new PendingGuard();}
                if(continuation.kind()==GuardKind.BRANCH && source.action instanceof Branch branch) {
                    Optional<Integer> taken=successor(source,branch);
                    if(taken.isPresent() && taken.get()!=continuation.successor())return new ImpossibleGuard();
                    Optional<Path> selected=path.with(branchKey(unit.state,continuation.branch(),Optional.of(new Iteration(loop,previous))),continuation.successor());
                    if(selected.isEmpty())return new ImpossibleGuard();path=selected.get();
                } else if(continuation.kind()==GuardKind.NORMAL && ((Finished)source.progress).value().empty())return new ImpossibleGuard();
            }
        }
        for (Unit source:unit.state.abruptUnits) if (source.action.site().instruction()<unit.action.site().instruction() && !source.thrown.empty()
                && (source.iteration.isEmpty() || source.iteration.equals(unit.iteration))
                && source.progress instanceof Finished done && done.value().empty() && uncaught(source)
                && source.thrown.alternatives().stream().allMatch(v -> v.path().choices().entrySet().stream().allMatch(c -> Objects.equals(unit.state.key.path().choices().get(c.getKey()),c.getValue()) || !conditions.uncertain(c.getKey())))
                && dominates(unit.state,source.action.site().instruction(),unit.action.site().instruction())) return new ImpossibleGuard();
        for (Guard guard : unit.state.facts.guards().getOrDefault(unit.action.site().instruction(), List.of())) {
            Optional<Iteration> scope=unit.iteration.filter(i -> i.loop().start()<=guard.branch() && guard.branch()<=i.loop().end());
            BranchKey key=guard.kind()==GuardKind.BRANCH?branchKey(unit.state,guard.branch(),scope):new BranchKey(unit.state.id,guard.branch(),scope.map(Iteration::index).orElse(-1));
            if (guard.kind()==GuardKind.HANDLER) {
                CatchFlow flow=caught(unit.state,guard.branch());
                if (flow.values().empty()) return flow.pending()?new PendingGuard():new ImpossibleGuard();
                Site handler=new Site(unit.state.key.target(),guard.branch(),-1,unit.action.site().source());
                List<Gap> gaps=flow.values().alternatives().stream().flatMap(v -> v.gaps().stream()).toList();
                if (!gaps.isEmpty()) conditions.uncertain(key,new Gap(GapKind.CONTROL_CONDITION,handler,"exception handler reachability is conditional"));
                Optional<Path> merged=path.with(key,guard.successor()); if (merged.isEmpty()) return new ImpossibleGuard(); path=merged.get();
                requireControl(unit,evidence.control(unit.state.id,handler,flow.values(),path,EvidenceGraph.Control.HANDLER,0),path);
                continue;
            }
            if (guard.kind()==GuardKind.NORMAL) {
                Unit source=producer(unit,guard.branch(),false);
                if (source==null || source.progress instanceof Waiting) return new PendingGuard();
                if (source.progress instanceof Finished done && done.value().empty()) return new ImpossibleGuard();
                if(source.normal.isPresent() && !source.normal.get().under(path).empty()) {
                    requireControl(unit,evidence.control(source.state.id,source.action.site(),source.normal.get(),path),path);
                }
                else if (safe(source)) {
                    List<Sources> inputs=safetyInputs(source.action);
                    for(int index=0;index<inputs.size();index++)requireControl(unit,evidence.control(source.state.id,source.action.site(),resolve(source,inputs.get(index)),path,EvidenceGraph.Control.SAFETY,index),path);
                }
                else conditions.uncertain(key,new Gap(GapKind.CONTROL_CONDITION,source.action.site(),"normal flow requires this operation to return without an exception"));
                Optional<Path> merged=path.with(key,guard.successor()); if (merged.isEmpty()) return new ImpossibleGuard(); path=merged.get();
                continue;
            }
            Unit branchUnit = producer(unit,guard.branch(),false);
            if (branchUnit == null || !(branchUnit.action instanceof Branch branch)) continue;
            if (branchUnit.progress instanceof Waiting) return new PendingGuard();
            Optional<Integer> taken = successor(branchUnit,branch);
            if (taken.isPresent() && taken.get()!=guard.successor()) return new ImpossibleGuard();
            if (taken.isEmpty()) conditions.uncertain(key, new Gap(GapKind.CONTROL_CONDITION, branch.site(), "branch outcome depends on unspecified or unsupported values"));
            Optional<Path> merged = path.with(key, guard.successor());
            if (merged.isEmpty()) return new ImpossibleGuard();
            path = merged.get();
            Optional<Path> refined=jvm.assume(branch,guard.successor(),branch.inputs().stream().map(input -> resolve(branchUnit,input)).toList(),path);
            if(refined.isEmpty())return new ImpossibleGuard();path=refined.get();
            Value outcomes=((Finished)branchUnit.progress).value().under(path);
            if(outcomes.empty())return new ImpossibleGuard();
            requireControl(unit,evidence.control(branchUnit.state.id,branch.site(),outcomes,path,EvidenceGraph.Control.BRANCH,0),path);
        }
        // Later branch guards can refine the path after a normal-flow guard was visited.
        for(Guard guard:unit.state.facts.guards().getOrDefault(unit.action.site().instruction(),List.of()))if(guard.kind()==GuardKind.NORMAL) {
            Unit source=producer(unit,guard.branch(),false);
            if(source!=null && source.normal.isPresent() && source.normal.get().under(path).empty())return new ImpossibleGuard();
        }
        if (unit.state.compoundControl) {
            Conditions.Paths control=unit.state.control.map(Control::paths).orElseGet(() -> {
                Conditions.Paths result=conditions.paths(unit.state.facts,branchDecisions(unit.state));unit.state.control=Optional.of(new Control(Optional.empty(),unit.state.key.path(),result,List.of()));return result;
            });
            int at=unit.action.site().instruction();
            if (!control.possible().contains(at)) return new ImpossibleGuard();
            if (!control.ready().contains(at)) {unit.state.controlWaiters.add(unit);return new PendingGuard();}
            if (control.unknown() && unit.state.facts.guards().getOrDefault(at,List.of()).stream().noneMatch(g -> g.kind()==GuardKind.BRANCH)
                    && conditions.reachable(unit.state.facts,branchDecisions(unit.state),true,at).stream().anyMatch(i -> unit.state.producers.get(i)!=null && unit.state.producers.get(i).action instanceof Returned))
                unit.prerequisites.add(new Gap(GapKind.CONTROL_CONDITION,unit.action.site(),"compound control flow depends on unspecified branch outcomes"));
        }
        return new ActiveGuard(path);
    }

    private void requireControl(Unit unit,Value values,Path path) {
        Value witnesses=values.under(path);
        for (Bound bound:witnesses.alternatives()) {
            unit.prerequisites.addAll(bound.gaps());unit.controlDependencies.addAll(bound.dependencies());
        }
    }

    private void demandControl(Unit unit) {
        if (!(unit.action instanceof Call call) || !(Mechanisms.demands(call) || knowledge.isImpact(call.target()))) return;
        SearchRanking.Rank rank=rank(unit);
        Path path=unit.state.key.path();
        for (Guard guard:unit.state.facts.guards().getOrDefault(call.site().instruction(),List.of())) {
            if (guard.kind()==GuardKind.HANDLER) continue;
            Unit source=producer(unit,guard.branch(),false);
            if (source!=null && source.progress instanceof Waiting)
                demand(unit.state,call.site(),new Producer(guard.branch()),path,iteration(source),0,rank);
        }
        if (unit.previousEffect!=null && unit.previousEffect.progress instanceof Waiting)
            demand(unit.state,call.site(),new Producer(unit.previousEffect.action.site().instruction()),path,iteration(unit.previousEffect),0,rank);
    }

    /** Normal completion depends on safety operands, not the unused returned object's data graph. */
    private Map<Integer,Conditions.Decision> branchDecisions(State state) {
        Map<Integer,Conditions.Decision> decisions=new HashMap<>();
        for(Unit unit:state.units)if(unit.action instanceof Branch branch) {
            Conditions.Decision decision=unit.progress instanceof Waiting?new Conditions.Pending():successor(unit,branch)
                    .<Conditions.Decision>map(Conditions.Taken::new).orElseGet(Conditions.Unknown::new);
            decisions.put(branch.site().instruction(),decision);
        }
        return decisions;
    }

    private Optional<Integer> successor(Unit unit,Branch branch) {
        return jvm.successor(branch,branch.inputs().stream().map(source -> resolve(unit,source)).toList(),unit.state.facts.cfg());
    }
    private record CatchFlow(Value values,boolean pending) {}
    private CatchFlow caught(State state,int target) {
        Value values=Value.BOTTOM; boolean pending=false;
        for (Handler handler:state.facts.handlers()) if (handler.target()==target) for (Unit source:state.handlerSources.getOrDefault(target,Set.of())) {
            int index=source.action.site().instruction();
            if (index<handler.start() || index>=handler.end() || !exceptional(source.action)) continue;
            if (source.progress instanceof Waiting) { pending=true; continue; }
            if (source.progress instanceof Finished done && done.value().empty() && source.thrown.empty()) continue;
            for (Bound value:source.thrown.alternatives()) if (value.atom() instanceof ObjectValue object) {
                Query<Boolean> match=program.assignable(object.type(),handler.type());
                if(!match.value().equals(Optional.of(false)) || !match.pending().isEmpty())
                    values=values.merge(new Value(Set.of(value)).requiring(JvmSemantics.queryGaps(source.action.site(),match)));
            }
            if (source.thrown.empty() && !safe(source)) values=values.merge(Value.of(object(state,-target-3,handler.type(),"possible exception handler value",false))
                    .requiring(List.of(new Gap(GapKind.CONTROL_CONDITION,source.action.site(),"operation may transfer to exception handler"))));
        }
        return new CatchFlow(values,pending);
    }
    private boolean safe(Unit unit) {
        if(!unit.thrown.empty())return false;
        if(unit.normal.isPresent())return !unit.normal.get().empty() && unit.normal.get().alternatives().stream().allMatch(b -> b.atom()==NormalValue.CERTAIN);
        List<Value> operands=sources(unit.action).stream().map(source -> resolve(unit,source)).toList();
        Map<Integer,Integer> lengths=new HashMap<>();
        if(unit.action instanceof ReadArray || unit.action instanceof WriteArray)for(Bound array:operands.get(0).alternatives())if(array.atom() instanceof ObjectValue object)
            length(unit,object).ifPresent(size -> lengths.put(object.id(),size));
        return jvm.normal(unit.action,operands,lengths);
    }
    private boolean uncaught(Unit source) {
        int index=source.action.site().instruction();
        return source.thrown.alternatives().stream().anyMatch(b -> b.atom() instanceof ObjectValue object && source.state.facts.handlers().stream().filter(h -> h.start()<=index && index<h.end())
                .map(h -> program.assignable(object.type(),h.type())).allMatch(q -> q.value().equals(Optional.of(false)) && q.pending().isEmpty()));
    }
    private boolean dominates(State state,int blocked,int target) {
        Set<Integer> seen=new HashSet<>(); ArrayDeque<Integer> todo=new ArrayDeque<>(List.of(0));
        while (!todo.isEmpty()) {
            int at=todo.removeFirst(); if (at==blocked || !seen.add(at)) continue;
            if (at==target) return false;
            for (Edge edge:state.facts.cfg()) if (edge.from()==at) {
                Unit source=state.producers.get(at);
                if (edge.exceptional() && (source==null || safe(source))) continue;
                todo.add(edge.to());
            }
        }
        return true;
    }
    private void throwing(Unit unit,Value value) {
        value=value.requiring(List.copyOf(unit.prerequisites)).tracing(unit.controlDependencies);
        Value joined=bounded(evidence.compact(unit.state.id,unit.action.site(),unit.thrown.merge(value)),unit.action.site());
        if (joined.equals(unit.thrown)) return;
        unit.thrown=joined;
        unit.state.control=Optional.empty();
        if (unit.activation.isPresent()) return;
        unit.state.abruptUnits.add(unit);
        Value escaped=Value.BOTTOM;
        for (Bound bound:value.alternatives()) if (bound.atom() instanceof ObjectValue object) {
            int index=unit.action.site().instruction();
            boolean caught=false;List<Gap> pending=new ArrayList<>();
            for(Handler handler:unit.state.facts.handlers())if(handler.start()<=index && index<handler.end()) {
                Query<Boolean> match=program.assignable(object.type(),handler.type());
                if(match.value().equals(Optional.of(true)) && match.pending().isEmpty()){caught=true;break;}
                pending.addAll(JvmSemantics.queryGaps(unit.action.site(),match));
            }
            if(!caught)escaped=escaped.merge(new Value(Set.of(bound)).requiring(pending));
        }
        if (!escaped.empty()) {
            unit.state.thrown=bounded(evidence.compact(unit.state.id,unit.action.site(),unit.state.thrown.merge(escaped)),unit.action.site());
            for (Unit consumer:unit.state.returnConsumers) offer(consumer);
        }
        for (Handler handler:unit.state.facts.handlers()) {
            for (Unit consumer:unit.state.consumers.getOrDefault(new Producer(handler.target()),Set.of())) offer(consumer);
            for (Unit consumer:unit.state.consumers.getOrDefault(new ExceptionOrigin(handler.target()),Set.of())) offer(consumer);
        }
    }
    private void throwing(Unit unit,String type,Path path,List<Gap> gaps) {
        throwing(unit,Value.of(object(unit,unit.action.site().instruction(),type,"JVM exceptional result",true),path).requiring(gaps));
    }

    private List<Combination> combinations(Unit unit, List<Value> values, Path path) {
        String detail="binding combination budget at "+unit.action.site();
        Combination initial=new Combination(List.of(),path,union(List.copyOf(unit.state.required),List.copyOf(unit.prerequisites)),Set.copyOf(unit.controlDependencies));
        java.util.function.BiFunction<Combination,List<Bound>,List<Bound>> order=(prefix,bounds) -> bounds;Object selection=program.definitionCount();
        if(unit.action instanceof Call call && ranking.applies(call)) {
            SearchRanking.Selection view=ranking.selection(call,values,path,(object,slot) -> read(unit,object,slot),program.definitionCount());
            selection=view.key();order=(prefix,bounds) -> ranking.order(call,prefix,bounds,view);
        }
        Combinations.Result joined=unit.combinations.join(values,initial,limits.alternatives(),new Gap(GapKind.BUDGET,unit.action.site(),detail),Math.min(limits.steps()-steps,Math.max(64L,limits.alternatives()*8L)*values.size()),
                order,selection);
        steps+=joined.consumed();refinementWork+=joined.consumed();combinationReuses+=joined.reused();
        if(joined.truncated()) {
            limit(detail);
            for(Combinations.Frontier frontier:joined.frontier())
                relation(unit.state.id,unit.action.site(),Kind.VALUE_FLOW,Optional.empty(),Evidence.UNKNOWN,new Literal(null),List.of(new Truncated(detail)),List.of(),List.of(new Gap(GapKind.BUDGET,unit.action.site(),detail)),frontier.path(),"unexpanded binding operand "+frontier.operand(),Set.of());
        }
        return joined.values().stream().filter(c -> conditions.compatible(c.path(),c.gaps()) && compatibleGuards(unit,c.path()))
                .map(c -> new Combination(c.atoms().stream().map(a -> CandidateBindings.project(a,c.path())).toList(),c.path(),c.gaps(),c.dependencies())).toList();
    }

    private boolean compatibleGuards(Unit unit,Path path) {
        for(Guard guard:unit.state.facts.guards().getOrDefault(unit.action.site().instruction(),List.of()))if(guard.kind()==GuardKind.BRANCH) {
            Unit source=producer(unit,guard.branch(),false);
            if(source!=null && source.action instanceof Branch branch && source.progress instanceof Finished done) {
                Value outcomes=done.value().under(path);
                if(outcomes.empty() || outcomes.alternatives().stream().allMatch(b -> b.atom() instanceof Literal l && l.value() instanceof Boolean decision && decision!=(guard.successor()==branch.jumpTarget())))return false;
            }
        }
        return true;
    }

    private void execute(Unit unit) {
        // These prerequisites describe this evaluation; earlier path views are alternative evidence.
        unit.prerequisites.clear();unit.controlDependencies.clear();
        try {
        if (unit.activation.isPresent()) {
            Activation active=unit.activation.get();
            unit.executionPath=Optional.of(active.invocation.path());
            Local callback=Local.of(active.dispatch,active.observation);
            EffectResult result=effects(unit,active.invocation,callback,List.copyOf(active.gaps),Set.copyOf(active.dependencies),0,List.of(),List.of());
            if(result instanceof Produced value)finish(unit,value.value());
            else if(result instanceof CompletedVoid)finish(unit,Value.NULL.under(active.invocation.path()));
            else if(result instanceof Exceptional)finish(unit,Value.BOTTOM);
            return;
        }
        Reachability guarded = guard(unit);
        if (guarded instanceof PendingGuard) { demandControl(unit); return; }
        if (guarded instanceof ImpossibleGuard) { finish(unit, Value.BOTTOM); return; }
        Path path = ((ActiveGuard) guarded).path();
        unit.executionPath=Optional.of(path);
        if(unit.iteration.filter(i -> i.loop().iterator().isEmpty() && i.index()>0).isPresent()) {
            Reachability continuation=precedingIteration(unit,path);
            if(continuation instanceof PendingGuard)return;
            if(continuation instanceof ImpossibleGuard){finish(unit,Value.BOTTOM);return;}
        }
        boolean skipped=unit.previousEffect!=null && (unit.previousEffect.progress instanceof Waiting || unit.previousEffect.progress instanceof Finished prior && prior.value().empty())
                && unit.iteration.filter(i -> i.loop().iterator().isEmpty()).isPresent() && unit.previousEffect.iteration.filter(i -> i.loop().equals(unit.iteration.get().loop()) && i.index()<iteration(unit)).isPresent();
        if (!skipped && unit.previousEffect != null && unit.previousEffect.progress instanceof Waiting) { demandControl(unit); return; }
        if(!skipped && unit.previousEffect!=null && unit.previousEffect.progress instanceof Finished previous && previous.value().empty()){finish(unit,Value.BOTTOM);return;}
        if(!skipped && unit.previousEffect!=null && unit.previousEffect.normal.isPresent()) {
            if(unit.previousEffect.normal.get().under(path).empty()){finish(unit,Value.BOTTOM);return;}
            requireControl(unit,evidence.control(unit.previousEffect.state.id,unit.previousEffect.action.site(),unit.previousEffect.normal.get(),path),path);
        }
        if (!skipped && unit.previousEffect!=null && unit.previousEffect.progress instanceof Finished previous)
            for (Bound value:previous.value().under(path).alternatives()) {
                for (Gap gap:value.gaps()) if (unit.previousEffect.prerequisites.contains(gap)) unit.prerequisites.add(gap);
                unit.controlDependencies.addAll(unit.previousEffect.controlDependencies);
            }
        Action action = unit.action;
        State state = unit.state;
        String initialized=action instanceof ReadField f && f.receiver().origins().isEmpty()?f.field().owner()
                :action instanceof WriteField f && f.receiver().origins().isEmpty()?f.field().owner()
                :action instanceof Call c && c.opcode()==Opcodes.INVOKESTATIC?c.target().owner()
                :action instanceof Allocate a?a.type():null;
        if(initialized!=null && !initialized.equals("<invokedynamic>") && !initialized(unit,initialized,path,new LinkedHashSet<>()))return;
        if(action instanceof Assign assign){finish(unit,resolve(unit,assign.input()).under(path));}
        else if (action instanceof Constant constant) {
            Atom atom = constant.value() instanceof ClassConstant type ? new ClassValue(type.descriptor(), true,Optional.empty(),program.scope(Values.type(type.descriptor()),state.key.target().loader()))
                    : constant.value() instanceof MethodTypeConstant type ? io.just.knowledge.ValueBindings.methodType(type.descriptor(),program,constant.site().method().loader())
                    : constant.value() instanceof UnsupportedConstant unsupported ? new Unknown("unsupported JVM constant: " + unsupported.kind())
                    : constant.value() instanceof LiteralConstant literal?new Literal(literal.value()):new Unknown("unmodeled JVM constant: "+constant.value());
            Value value = Value.of(atom, path);
            if (constant.value() instanceof UnsupportedConstant unsupported)
                value = value.requiring(List.of(new Gap(GapKind.UNSUPPORTED, constant.site(), unsupported.kind())));
            finish(unit, value);
        } else if (action instanceof Allocate allocate) {
            finish(unit, Value.of(object(unit, action.site().instruction(), allocate.type(), "allocation", !allocate.repeated() || unit.iteration.isPresent()), path));
        } else if (action instanceof NewArray array) {
            List<Combination> combinations = combinations(unit, List.of(resolve(unit, array.length())), path);
            if (combinations.isEmpty()) return;
            ObjectValue object = object(unit, action.site().instruction(), array.descriptor(), "array", !array.repeated() || unit.iteration.isPresent());
            Value result = Value.BOTTOM;
            for (Combination c : combinations) {
                JvmSemantics.Check check=jvm.check(array,c.atoms(),OptionalInt.empty());
                if(check instanceof JvmSemantics.Rejected rejected){throwing(unit,rejected.exception(),c.path(),c.gaps());continue;}
                c=new Combination(c.atoms(),c.path(),union(c.gaps(),((JvmSemantics.Normal)check).gaps()),c.dependencies());
                write(unit, object, new Length(), Value.of(c.atoms().get(0), c.path()).requiring(c.gaps()).tracing(c.dependencies()));
                result = merge(unit,result,Value.of(object, c.path()).requiring(c.gaps()).tracing(c.dependencies()));
            }
            finish(unit, result);
        } else if (action instanceof Cast cast) {
            Value source = resolve(unit, cast.input());
            if (source.empty()) return;
            Value result = Value.BOTTOM;
            for (Bound bound : source.under(path).alternatives()) {
                JvmSemantics.Conversion conversion=jvm.cast(cast,CandidateBindings.project(bound.atom(),bound.path()));
                if(conversion instanceof JvmSemantics.Rejected rejected)throwing(unit,rejected.exception(),bound.path(),bound.gaps());
                else result=merge(unit,result,((JvmSemantics.Converted)conversion).value().under(bound.path()).requiring(bound.gaps()).tracing(bound.dependencies()));
            }
            finish(unit, result);
        } else if (action instanceof ReadField field) {
            fieldRead(unit, field, path);
        } else if (action instanceof WriteField requested) {
            WriteField field=new WriteField(requested.site(),program.field(requested.field()).orElse(requested.field()),requested.receiver(),requested.value());
            List<Value> values = List.of(field.receiver().origins().isEmpty() ? Value.of(staticObject(state, field.field().owner(),field.field().loader())) : resolve(unit, field.receiver()), resolve(unit, field.value()));
            List<Combination> combinations = combinations(unit, values, path);
            if (combinations.isEmpty()) return;
            Value completed=Value.BOTTOM;
            for (Combination c : combinations) {
                JvmSemantics.Check check=jvm.check(field,c.atoms(),OptionalInt.empty());
                if(check instanceof JvmSemantics.Rejected rejected){throwing(unit,rejected.exception(),c.path(),c.gaps());continue;}
                List<Gap> gaps=union(c.gaps(),((JvmSemantics.Normal)check).gaps());
                if(c.atoms().get(0) instanceof ObjectValue object)
                    write(unit,object,new Field(field.field()),Value.of(c.atoms().get(1),c.path()).requiring(gaps).tracing(c.dependencies()));
                completed=completed.merge(Value.NULL.under(c.path()).requiring(gaps).tracing(c.dependencies()));
            }
            finish(unit,completed);
        } else if (action instanceof ReadArray array) {
            List<Combination> combinations = combinations(unit, List.of(resolve(unit, array.array()), resolve(unit, array.index())), path);
            if (combinations.isEmpty()) return;
            Value value = Value.BOTTOM;
            for (Combination c:combinations) {
                Atom receiver=c.atoms().get(0);
                OptionalInt size=receiver instanceof ObjectValue object?length(unit,object):OptionalInt.empty();
                JvmSemantics.Check check=jvm.check(array,c.atoms(),size);
                if(check instanceof JvmSemantics.Rejected rejected){throwing(unit,rejected.exception(),c.path(),c.gaps());continue;}
                List<Gap> gaps=union(c.gaps(),((JvmSemantics.Normal)check).gaps());
                if(receiver instanceof ArrayValue snapshot) {
                    if(snapshot.order()==ArrayOrder.UNSPECIFIED) {
                        for(Atom element:snapshot.elements())value=value.merge(Value.of(element,c.path()).requiring(union(gaps,snapshot.conditions())).tracing(c.dependencies()));
                        if(snapshot.extent()==ArrayExtent.UNKNOWN)value=value.merge(Value.of(new Unknown("array snapshot has unresolved members"),c.path()).requiring(union(gaps,snapshot.conditions())).tracing(c.dependencies()));
                    } else if(c.atoms().get(1) instanceof Literal literal && literal.value() instanceof Integer index)
                        value=value.merge(Value.of(snapshot.elements().get(index),c.path()).requiring(gaps).tracing(c.dependencies()));
                    else for(Atom element:snapshot.elements())value=value.merge(Value.of(element,c.path()).requiring(gaps).tracing(c.dependencies()));
                } else if(receiver instanceof ObjectValue object) {
                    Slot slot=index(c.atoms().get(1));
                    Value element=read(unit,object,slot).under(c.path());
                    if(element.empty() && object.defaultFields() && size.isPresent() && slot instanceof Index) {
                        String component=object.type().substring(1);
                        element=Value.of(new Literal(component.startsWith("L") || component.startsWith("[")?null:0),c.path());
                    }
                    if(element.empty())element=Value.of(new Unknown("array element not supplied"),c.path()).requiring(List.of(new Gap(GapKind.INPUT_BINDING,array.site(),"array element binding is unspecified")));
                    value=value.merge(element.requiring(gaps).tracing(c.dependencies()));
                } else value=value.merge(Value.of(new Unknown("array receiver is unspecified"),c.path()).requiring(gaps).tracing(c.dependencies()));
            }
            finish(unit, value);
        } else if (action instanceof WriteArray array) {
            List<Combination> combinations = combinations(unit, List.of(resolve(unit, array.array()), resolve(unit, array.index()), resolve(unit, array.value())), path);
            if (combinations.isEmpty()) return;
            Value completed=Value.BOTTOM;
            for (Combination c : combinations) {
                OptionalInt size=c.atoms().get(0) instanceof ObjectValue object?length(unit,object):OptionalInt.empty();
                JvmSemantics.Check check=jvm.check(array,c.atoms(),size);
                if(check instanceof JvmSemantics.Rejected rejected){throwing(unit,rejected.exception(),c.path(),c.gaps());continue;}
                List<Gap> gaps=union(c.gaps(),((JvmSemantics.Normal)check).gaps());
                if(c.atoms().get(0) instanceof ObjectValue object)
                    write(unit,object,index(c.atoms().get(1)),Value.of(c.atoms().get(2),c.path()).requiring(gaps).tracing(c.dependencies()));
                else gaps=union(gaps,List.of(new Gap(GapKind.UNSUPPORTED,array.site(),"array receiver mutation is not represented by positioned heap slots")));
                completed=completed.merge(Value.NULL.under(c.path()).requiring(gaps).tracing(c.dependencies()));
            }
            finish(unit,completed);
        } else if (action instanceof Call call) {
            call(unit, call, path);
        } else if (action instanceof Thrown thrown) {
            Value value=resolve(unit,thrown.value()).under(path);
            if (value.empty()) return;
            for (Bound bound:value.alternatives()) {
                if (bound.atom() instanceof Literal literal && literal.value()==null) throwing(unit,"java/lang/NullPointerException",bound.path(),bound.gaps());
                else throwing(unit,new Value(Set.of(bound)));
            }
            finish(unit,Value.BOTTOM);
        } else if (action instanceof Returned returned) {
            Value value = returned.value().origins().isEmpty() ? Value.NULL.under(path) : resolve(unit, returned.value()).under(path);
            if (value.empty() && !returned.value().origins().isEmpty()) return;
            if(state.facts.limitations().isEmpty())unit.normal=Optional.of(Value.of(NormalValue.CERTAIN,path).requiring(union(List.copyOf(state.required),List.copyOf(unit.prerequisites))).tracing(unit.controlDependencies));
            value = value.requiring(List.copyOf(state.required));
            Value joined = bounded(evidence.compact(state.id,action.site(),state.returned.merge(value)), action.site());
            if (!joined.equals(state.returned)) {boolean newValue=hasNewBinding(state.returned,joined);state.returned = joined; for (Unit caller : state.returnConsumers) {offer(caller);if(demandGuidance && newValue)urgent.add(caller);}for(Backward query:state.returnDemands)offer(query); }
            finish(unit, value);
        } else if (action instanceof Branch branch) {
            List<Value> inputs=branch.inputs().stream().map(source -> resolve(unit,source)).toList();
            if (inputs.stream().anyMatch(Value::empty)) return;
            if(unit.iteration.isEmpty() && !(unit.progress instanceof Finished done && !done.value().empty()) && inputs.size()==2) {
                Iterations.counterPlan(state.facts,branch,inputs.get(1),Math.min(8,limits.alternatives()),state.loops).ifPresent(plan -> {
                    Unit previous=state.producers.get(plan.counterInitial());
                    for(Unit body:state.units)if(plan.start()<=body.action.site().instruction() && body.action.site().instruction()<=plan.end()
                            && body.previousEffect!=null && body.previousEffect.action.site().instruction()<plan.start()){previous=body.previousEffect;break;}
                    if(plan.prefix())limit("counter loop prefix ("+plan.count()+") at "+branch.site());
                    instantiate(unit,plan,previous);
                });
                inputs=branch.inputs().stream().map(source -> resolve(unit,source)).toList();
            }
            Value result=Value.BOTTOM;
            for (Combination c:combinations(unit,inputs,path)) {
                Optional<Integer> taken=jvm.successor(branch,c.atoms().stream().map(Value::of).toList(),state.facts.cfg());
                Optional<Path> selected=taken.isPresent()?c.path().with(branchKey(state,branch.site().instruction(),unit.iteration),taken.get()):Optional.of(c.path());
                if(selected.isPresent())result=merge(unit,result,Value.of(taken.<Atom>map(target -> new Literal(target==branch.jumpTarget())).orElseGet(() -> new Unknown("branch outcome unspecified")),selected.get()).requiring(c.gaps()).tracing(c.dependencies()));
            }
            finish(unit,result);
        } else if (action instanceof Compute compute) {
            List<Combination> combinations = combinations(unit, compute.inputs().stream().map(s -> resolve(unit, s)).toList(), path);
            if (combinations.isEmpty()) return;
            Value result = Value.BOTTOM;
            for (Combination c : combinations) {
                JvmSemantics.Check check=jvm.check(compute,c.atoms(),OptionalInt.empty());
                if(check instanceof JvmSemantics.Rejected rejected){throwing(unit,rejected.exception(),c.path(),c.gaps());continue;}
                c=new Combination(c.atoms(),c.path(),union(c.gaps(),((JvmSemantics.Normal)check).gaps()),c.dependencies());
                if (compute.opcode()==Opcodes.ARRAYLENGTH && c.atoms().get(0) instanceof ArrayValue arrayValue) {
                    Atom size=arrayValue.extent()==ArrayExtent.EXACT?new Literal(arrayValue.elements().size()):new Unknown("array snapshot length is unresolved");
                    result=merge(unit,result,Value.of(size,c.path()).requiring(c.gaps()).tracing(c.dependencies()));
                }
                else if (compute.opcode()==Opcodes.ARRAYLENGTH && c.atoms().get(0) instanceof ObjectValue array) {
                    Value size=read(unit,array,new Length()).under(c.path()).requiring(c.gaps()).tracing(c.dependencies());
                    if (size.empty()) size=Value.of(new Unknown("array length is unspecified"),c.path()).requiring(List.of(new Gap(GapKind.INPUT_BINDING,compute.site(),"array length binding is unspecified")));
                    result=merge(unit,result,size);
                }
                else result = merge(unit,result,Value.of(jvm.compute(compute,c.atoms()), c.path()).requiring(c.gaps()).tracing(c.dependencies()));
            }
            finish(unit, result);
        }
        } finally {unit.executionPath=Optional.empty();}
    }

    private ObjectValue object(State state, int instruction, String type, String role, boolean exact) {
        int loader=program.scope(type,state.key.target().loader());
        return objects.computeIfAbsent(new ObjectKey(state.id, instruction, type, role,loader, -1,state.key.phase(),List.of()), k ->
                new ObjectValue(nextObject++, type, exact, role + " in context " + state.id + " at " + state.key.target() + " insn " + instruction,exact,Optional.empty(),loader));
    }
    private ObjectValue object(Unit unit,int instruction,String type,String role,boolean exact) {
        return object(unit,instruction,type,role,exact,unit.state.key.target().loader());
    }
    private ObjectValue object(Unit unit,int instruction,String type,String role,boolean exact,int initiatingLoader) {
        int loader=program.scope(type,initiatingLoader);
        return objects.computeIfAbsent(new ObjectKey(unit.state.id,instruction,type,role,loader,iteration(unit),phase(unit),unit.effects),k ->
                new ObjectValue(nextObject++,type,exact,role+" at "+unit.action.site(),exact,Optional.empty(),loader));
    }
    private State root(State state){while(state.key.parent()>=0)state=states.get(state.key.parent());return state;}
    private ObjectValue staticObject(State state,String owner,int loader) {
        State root=root(state);return objects.computeIfAbsent(new ObjectKey(root.id,-2,owner,"static fields",loader,-1,root.key.phase(),List.of()),key -> new ObjectValue(nextObject++,owner,true,"static fields",true,Optional.empty(),loader));
    }

    private boolean initialized(Unit consumer,String owner,Path path,Set<DefinedType> visiting) {
        return initialized(consumer,owner,path,visiting,List.of(),consumer.state.key.target().loader(),false);
    }
    private boolean initialized(Unit consumer,String owner,Path path,Set<DefinedType> visiting,List<ExceptionFlow> wrappers) {return initialized(consumer,owner,path,visiting,wrappers,consumer.state.key.target().loader(),false);}
    private boolean initialized(Unit consumer,String owner,Path path,Set<DefinedType> visiting,List<ExceptionFlow> wrappers,int loader) {return initialized(consumer,owner,path,visiting,wrappers,loader,false);}
    private boolean initialized(Unit consumer,String owner,Path path,Set<DefinedType> visiting,List<ExceptionFlow> wrappers,int loader,boolean demanded) {
        loader=program.scope(owner,loader);
        if(!visiting.add(new DefinedType(owner,loader)))return true; // JVM recursive initialization on this logical thread.
        Optional<ClassInfo> type=program.type(owner,loader);
        if(type.isEmpty()) {
            for(QueryIssue issue:program.lookup(new MethodId(owner,"<clinit>","()V",loader)).pending())consumer.prerequisites.add(new Gap(issue.cause()==QueryCause.BUDGET?GapKind.BUDGET:GapKind.MISSING_DEPENDENCY,consumer.action.site(),issue.detail()));return true;
        }
        if(type.get().role()==Inputs.Role.PLATFORM && !demanded){
            consumer.prerequisites.add(new Gap(GapKind.DEPLOYMENT,root(consumer.state).key.call(),"platform runtime initialization before this entry is assumed"));return true;
        }
        if(visiting.size()>256){consumer.prerequisites.add(new Gap(GapKind.BUDGET,consumer.action.site(),"initialization hierarchy budget (256)"));limit("initialization hierarchy budget");return true;}
        Initialization key=new Initialization(root(consumer.state).id,owner,loader);
        State existing=initializers.getOrDefault(key,List.of()).stream().filter(state -> state.key.path().and(path).isPresent()).findFirst().orElse(null);
        if(existing!=null) {
            State ancestor=consumer.state;
            while(true){if(ancestor==existing)return true;if(ancestor.key.parent()<0)break;ancestor=states.get(ancestor.key.parent());}
            existing.returnConsumers.add(consumer);
            consumer.consumption.ifPresent(active -> active.callees.add(existing));
            if(!existing.thrown.empty()) {
                boolean first=consumer.state.id==existing.key.parent() && consumer.action.site().equals(existing.key.call()) && iteration(consumer)==existing.key.iteration();
                for(Bound thrown:existing.thrown.under(path).alternatives()) {
                    Value failure;
                    if(!first)failure=Value.of(object(consumer,consumer.action.site().instruction(),"java/lang/NoClassDefFoundError","initialization failure",true),thrown.path()).requiring(thrown.gaps()).tracing(thrown.dependencies());
                    else {
                        Query<Boolean> error=thrown.atom() instanceof ObjectValue object?program.assignable(object.type(),"java/lang/Error"):new Query<>(Optional.empty(),List.of());
                        List<Gap> required=union(thrown.gaps(),JvmSemantics.queryGaps(consumer.action.site(),error));
                        if(error.value().equals(Optional.of(true)))failure=new Value(Set.of(thrown)).requiring(required);
                        else {
                            failure=Value.of(object(consumer,consumer.action.site().instruction(),"java/lang/ExceptionInInitializerError","initialization failure",true),thrown.path()).requiring(required).tracing(thrown.dependencies());
                            if(error.value().isEmpty())failure=failure.merge(new Value(Set.of(thrown)).requiring(required));
                        }
                    }
                    throwing(consumer,wrapped(consumer,failure,wrappers,path,List.of()));
                }
                if(existing.returned.empty()) {
                    if(existing.units.stream().allMatch(u -> u.progress instanceof Finished))finish(consumer,Value.BOTTOM);
                    return false;
                }
            }
            Value normal=existing.returned.under(path);if(normal.empty())return false;
            requireControl(consumer,evidence.control(existing.id,existing.key.call(),normal,path),path);
            return true;
        }
        if((type.get().access() & Opcodes.ACC_INTERFACE)==0) {
            if(type.get().parent()!=null && !initialized(consumer,type.get().parent(),path,visiting,wrappers,loader))return false;
            if(!defaultInterfaces(consumer,type.get().interfaces(),type.get().loader(),path,visiting,new LinkedHashSet<>(),wrappers))return false;
        }
        MethodId method=program.method(owner,"<clinit>","()V",loader);
        if(program.declared(method).isEmpty())return true;
        int edge=relation(consumer,Kind.DIRECT_CALL,Optional.of(method),Evidence.PROVEN,new Literal(null),List.of(),List.of(consumer.action.site()),List.of(),path,"demanded JVM class initialization",Set.of());
        State child=create(new InvocationKey(consumer.state.id,consumer.action.site(),method,path,iteration(consumer),phase(consumer),new CallBinding(new Literal(null),List.of())),consumer.state.entry,edge);
        if(child==null){consumer.prerequisites.add(new Gap(GapKind.BUDGET,consumer.action.site(),"class initialization context budget"));return true;}
        initializers.computeIfAbsent(key,ignored -> new ArrayList<>()).add(child);child.returnConsumers.add(consumer);initialize(child);return false;
    }
    private boolean defaultInterfaces(Unit consumer,List<String> interfaces,int loader,Path path,Set<DefinedType> initialization,Set<DefinedType> seen,List<ExceptionFlow> wrappers) {
        for(String iface:interfaces)if(seen.add(new DefinedType(iface,program.scope(iface,loader)))) {
            if(seen.size()>256){consumer.prerequisites.add(new Gap(GapKind.BUDGET,consumer.action.site(),"default interface initialization budget (256)"));limit("default interface initialization budget");return true;}
            Optional<ClassInfo> info=program.type(iface,loader);
            if(info.isEmpty()){consumer.prerequisites.add(new Gap(GapKind.MISSING_DEPENDENCY,consumer.action.site(),"default interface hierarchy unavailable: "+iface));continue;}
            if(!defaultInterfaces(consumer,info.get().interfaces(),info.get().loader(),path,initialization,seen,wrappers))return false;
            if(info.get().methods().stream().anyMatch(m -> !m.isStatic() && m.hasBody() && (m.access() & Opcodes.ACC_PRIVATE)==0 && !m.id().name().startsWith("<")) && !initialized(consumer,iface,path,initialization,wrappers,info.get().loader()))return false;
        }
        return true;
    }
    private Atom external(State state, int instruction, String descriptor, String role) {
        if (descriptor.startsWith("L") || descriptor.startsWith("[")) return object(state, instruction, Values.type(descriptor), role, false);
        return new ExternalValue(descriptor,new InputSource(state.key.target(),-instruction-2,List.of()));
    }
    private static Slot index(Atom atom) {
        return atom instanceof Literal literal && literal.value() instanceof Integer number ? new Index(number) : new Wildcard();
    }

    private void fieldRead(Unit unit, ReadField requested, Path path) {
        ReadField field=new ReadField(requested.site(),program.field(requested.field()).orElse(requested.field()),requested.receiver());
        State state = unit.state;
        if(field.receiver().origins().isEmpty()) {
            Optional<Atom> constant=knowledge.staticField(field.field());
            if(constant.isEmpty())constant=program.fieldConstant(field.field()).filter(c -> c instanceof LiteralConstant).map(c -> new Literal(((LiteralConstant)c).value()));
            if(constant.isPresent()) {finish(unit,Value.of(constant.get(),path));return;}
        }
        Value receivers = field.receiver().origins().isEmpty() ? Value.of(staticObject(state, field.field().owner(),field.field().loader())) : resolve(unit, field.receiver());
        if (receivers.empty()) return;
        Value result = Value.BOTTOM;
        for (Combination c : combinations(unit, List.of(receivers), path)) {
            JvmSemantics.Check check=jvm.check(field,c.atoms(),OptionalInt.empty());
            if(check instanceof JvmSemantics.Rejected rejected){throwing(unit,rejected.exception(),c.path(),c.gaps());continue;}
            c=new Combination(c.atoms(),c.path(),union(c.gaps(),((JvmSemantics.Normal)check).gaps()),c.dependencies());
            if (!(c.atoms().get(0) instanceof ObjectValue receiver)) {
                result=merge(unit,result,Value.of(new Unknown("field receiver has no positioned heap binding"),c.path()).requiring(c.gaps()).tracing(c.dependencies()));continue;
            }
            Value value = read(unit, receiver, new Field(field.field())).under(c.path()).requiring(c.gaps()).tracing(c.dependencies());
            if (value.empty()) {
                String descriptor = field.field().descriptor();
                Atom atom;
                if (receiver.defaultFields()) atom = new Literal(descriptor.startsWith("L") || descriptor.startsWith("[") ? null : 0);
                else if (descriptor.startsWith("L") || descriptor.startsWith("[")) {
                    atom = fields.computeIfAbsent(new ExternalField(receiver.id(), field.field()), key -> new ObjectValue(nextObject++, Values.type(descriptor), false,
                            "field " + field.field().owner() + "." + field.field().name() + " of object " + receiver.id() + " (" + receiver.origin() + ")",false,receiver.source().map(s -> s.at(new Field(field.field()))),program.scope(Values.type(descriptor),field.field().loader())));
                } else atom = receiver.source().<Atom>map(s -> new ExternalValue(descriptor,s.at(new Field(field.field())))).orElseGet(() -> new Unknown("field " + field.field() + " of object " + receiver.id() + " not supplied"));
                Mechanisms.MissingField missing=knowledge.missingField(receiver,field.field(),atom);
                atom=missing.value();
                for(InputNeed need:missing.needs())if(!requirements.add(state.id,state.entry.method().id(),field.site(),c.path(),need,c.dependencies()))limit("input requirement budget");
                value = Value.of(atom, c.path()).requiring(c.gaps()).tracing(c.dependencies());
            }
            for(Bound bound:value.alternatives()) {
                Set<Integer> required=new LinkedHashSet<>(c.dependencies());required.addAll(bound.dependencies());
                int edge=relation(unit.state.id,unit.action.site(),Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,receiver,List.of(),List.of(field.site()),bound.gaps(),bound.path(),"read "+field.field(),required,Optional.of(new Field(field.field())));
                result=merge(unit,result,new Value(Set.of(bound)).tracing(edge<0?Set.of():Set.of(edge)));
            }
        }
        finish(unit, result);
    }

    private Value read(Unit unit,ObjectValue object,Slot slot) { return read(unit,object,slot,slot instanceof ResolvedObject); }

    private Value read(Unit unit, ObjectValue object, Slot slot,boolean ownWrites) {
        Optional<Value> cursor=Iterations.cursor(slot,object,unit.iteration.map(Iteration::loop),iteration(unit),
                unit.iteration.isEmpty() && inLoop(unit.state.facts,unit.action.site().instruction(),unit.action.site().instruction()),unit.action.site());
        if(cursor.isPresent())return cursor.get();
        Path path=unit.executionPath.orElseGet(() -> guard(unit) instanceof ActiveGuard active?active.path():unit.state.key.path());
        HeapStore.Use use=new HeapStore.Use(writer(unit),unit.action.site(),path,unit.state.facts.cfg(),ownWrites);
        HeapStore.Read read=heap.read(object,slot,use);
        unit.consumption.ifPresent(active -> active.reads.put(new HeapQuery(object,slot,use),read.value()));
        for(Cell dependency:read.dependencies())readers.computeIfAbsent(dependency,k -> new LinkedHashSet<>()).add(unit);
        return read.value();
    }
    private static boolean inLoop(Facts facts,int low,int high) {return HeapStore.inLoop(facts.cfg(),low,high);}

    private void write(Unit unit, ObjectValue object, Slot slot, Value value) {
        long before=evidence.derivations();
        Cell cell = new Cell(object.id(), slot);
        Value recorded=Value.BOTTOM;
        for (Bound bound:value.alternatives()) {
            if(bound.atom() instanceof Symbolic symbolic)bound=new Bound(symbolic(unit,symbolic),bound.path(),bound.gaps(),bound.dependencies());
            int id=relation(unit.state.id,unit.action.site(),slot instanceof Field?Kind.FIELD_FLOW:Kind.ELEMENT_FLOW,Optional.empty(),Evidence.PROVEN,object,
                    List.of(bound.atom()),List.of(unit.action.site()),bound.gaps(),bound.path(),"write " + slot,bound.dependencies(),Optional.of(slot));
            recorded=recorded.merge(new Value(Set.of(new Bound(bound.atom(),bound.path(),bound.gaps(),id<0?bound.dependencies():Set.of(id)))));
        }
        if (!heap.write(object,slot,writer(unit),recorded,unit.action.site()) && evidence.derivations()==before)return;
        for(Backward reader:demandHeapReaders.getOrDefault(cell,Set.of()))offer(reader);
        for (Unit reader : readers.getOrDefault(cell, Set.of()))if(!(slot instanceof Mutation) || reader!=unit)offer(reader);
        if (slot instanceof Index) for (Unit reader : readers.getOrDefault(new Cell(object.id(), new Elements()), Set.of())) offer(reader);
    }

    private OptionalInt length(Unit unit,ObjectValue object) {
        Value values=read(unit,object,new Length()); Set<Integer> lengths=new HashSet<>();
        for (Bound value:values.alternatives()) if (value.atom() instanceof Literal l && l.value() instanceof Integer number) lengths.add(number); else return OptionalInt.empty();
        return lengths.size()==1?OptionalInt.of(lengths.iterator().next()):OptionalInt.empty();
    }

    private void call(Unit unit, Call call, Path path) {
        State state = unit.state;
        List<Value> values = new ArrayList<>();
        values.add(call.receiver().origins().isEmpty() ? Value.NULL : resolve(unit, call.receiver()));
        for (Sources argument : call.arguments()) values.add(resolve(unit, argument));
        boolean mechanismDemand=Mechanisms.demands(call) || knowledge.isImpact(call.target());
        List<Sources> operands=new ArrayList<>();operands.add(call.receiver());operands.addAll(call.arguments());
        SearchRanking.Rank rank=rank(unit);
        for(int i=0;i<operands.size();i++)if((mechanismDemand || rank!=SearchRanking.Rank.NONE) && (values.get(i).empty() || values.get(i).alternatives().stream().anyMatch(bound -> !finiteBinding(bound.atom()))))
            for(Origin origin:operands.get(i).origins())demand(state,call.site(),origin,path,iteration(unit),0,rank);
        List<Combination> combinations = combinations(unit, values, path);
        if (combinations.isEmpty()) return;
        Value returned = Value.BOTTOM;
        boolean waiting = false;
        for (Combination c : combinations) {
            Atom receiver = c.atoms().get(0);
            if (call.opcode()!=Opcodes.INVOKESTATIC && call.opcode()!=Opcodes.INVOKEDYNAMIC && receiver instanceof Literal literal && literal.value()==null) {
                throwing(unit,"java/lang/NullPointerException",c.path(),c.gaps()); continue;
            }
            List<Atom> arguments = c.atoms().subList(1, c.atoms().size());
            ValueType returnType = program.signature(call.target()).returned();
            ObjectValue resultObject = object(unit, call.site().instruction(), Values.type(returnType.descriptor()), "call result", false);
            Invocation invocation = new Invocation(call, receiver, arguments, resultObject, c.path());
            Optional<Local> model = model(unit,invocation);
            Optional<MethodId> boundaryImpact=knowledge.isImpact(call.target())?Optional.of(call.target()):program.lookup(call.target()).value().map(Method::id).filter(knowledge::isImpact);
            if (boundaryImpact.isPresent()) {
                boolean possible=model.flatMap(local -> Mechanisms.normalCompletion(local,c.path())).orElse(true);
                int relation = relation(unit, possible?Kind.IMPACT:Kind.VIRTUAL_CALL, boundaryImpact, Evidence.PROVEN, receiver, arguments,
                        List.of(call.site()), c.gaps(), c.path(), possible?"impact API boundary; input sources are separate from parameter control":"impact call reached; finite JVM/API preconditions reject this binding", c.dependencies());
                if(possible)observe(unit, relation, List.of());
            }
            if (model.isPresent()) {
                EffectResult output=effects(unit,invocation,model.get(),c.gaps(),c.dependencies(),0,List.of(),List.of());
                if(output instanceof Produced value)returned=merge(unit,returned,value.value());
                else if(output instanceof CompletedVoid) {
                    if(!returnType.isVoid())throw new IllegalStateException("nonvoid mechanism omitted its result: "+call.target());
                    returned=merge(unit,returned,Value.NULL.under(c.path()).requiring(c.gaps()).tracing(c.dependencies()));
                } else if(output instanceof Awaiting)waiting=true;
            } else {
                Query<List<VirtualTarget>> resolution = dispatch(call, receiver);
                List<Optional<VirtualTarget>> choices=resolution.value().orElse(List.of()).stream().map(Optional::of).toList();
                if(!resolution.pending().isEmpty() && !choices.isEmpty()) {
                    int frontier=relation(unit,Kind.DYNAMIC_CALL,Optional.empty(),Evidence.CONDITIONAL,receiver,arguments,List.of(call.site()),JvmSemantics.queryGaps(call.site(),resolution),c.path(),"virtual target search frontier",c.dependencies());
                    observe(unit,frontier,List.of());
                }
                if(choices.isEmpty())choices=List.of(Optional.empty());
                AlternativeScope scope=new AlternativeScope(call.target(),new CallBinding(receiver,arguments),unit.effects);
                int allowed=unit.alternativeTurns.getOrDefault(scope,1),selection=0;
                for(Optional<VirtualTarget> choice:choices) {
                    if(selection>=allowed){unit.alternativeTurns.put(scope,allowed+1);offer(unit);waiting=true;break;}
                    Optional<Method> target=choice.map(VirtualTarget::method);
                    selection++;int selected=unit.virtualSelections.computeIfAbsent(new ReceiverTarget(target.map(Method::id).orElse(call.target()),choice.flatMap(VirtualTarget::receiver)),key -> unit.virtualSelections.size());
                    Path targetPath=choices.size()==1?c.path():c.path().with(new TargetChoice(state.id,call.site().instruction(),iteration(unit),unit.effects),selected).orElseThrow();
                    Atom actualReceiver=receiver;
                    if(receiver instanceof ObjectValue object && !object.exact() && choice.flatMap(VirtualTarget::receiver).isPresent()) {
                        DefinedType runtime=choice.orElseThrow().receiver().orElseThrow();
                        InputNeed need=new InputNeed(receiver,Optional.empty(),NeedKind.RECEIVER_TYPE,"L"+runtime.name()+";",List.of(new ClassValue("L"+runtime.name()+";",true,Optional.empty(),runtime.loader())),"runtime type required by this virtual dispatch");
                        Optional<Path> narrowed=candidateBindings.require(targetPath,need,(value,slot) -> read(unit,value,slot));if(narrowed.isEmpty())continue;
                        targetPath=narrowed.get();actualReceiver=CandidateBindings.project(receiver,targetPath);
                    }
                List<Gap> gaps = new ArrayList<>(c.gaps());
                for(QueryIssue issue:choice.map(VirtualTarget::pending).orElse(resolution.pending()))gaps.add(new Gap(issue.cause()==QueryCause.BUDGET?GapKind.BUDGET:GapKind.MISSING_DEPENDENCY,call.site(),issue.detail()));
                Evidence evidence = Evidence.PROVEN;
                if (call.opcode() == Opcodes.INVOKEVIRTUAL || call.opcode() == Opcodes.INVOKEINTERFACE) {
                    if (!(receiver instanceof ObjectValue object) || !object.exact()) {
                        evidence = Evidence.CONDITIONAL;
                        gaps.add(new Gap(GapKind.INPUT_BINDING, call.site(), "runtime receiver binding is unspecified: " + receiver));
                    }
                }
                if(!knowledge.isImpact(call.target()) && target.filter(m -> knowledge.isImpact(m.id())).isPresent()) {
                    int impact=relation(unit,Kind.IMPACT,Optional.of(target.orElseThrow().id()),Evidence.PROVEN,receiver,arguments,List.of(call.site()),gaps,targetPath,"resolved inherited impact API boundary",c.dependencies());
                    observe(unit,impact,List.of());
                }
                Invocation selectedCall=target.isPresent()?new Invocation(new Call(call.site(),target.get().id(),call.opcode(),call.receiver(),call.arguments(),call.bootstrap()),actualReceiver,arguments,resultObject,targetPath):invocation;
                Optional<Local> selectedModel=target.isPresent()?model(unit,selectedCall):Optional.empty();
                if(selectedModel.isPresent()) {
                    int edge=relation(unit,Kind.VIRTUAL_CALL,target.map(Method::id),evidence,actualReceiver,arguments,List.of(call.site()),gaps,targetPath,"selected JVM mechanism",c.dependencies());
                    Set<Integer> dependencies=new LinkedHashSet<>(c.dependencies());if(edge>=0)dependencies.add(edge);
                    EffectResult output=effects(unit,selectedCall,selectedModel.get(),gaps,Set.copyOf(dependencies),0,List.of(),List.of());
                    if(output instanceof Produced value)returned=merge(unit,returned,value.value());
                    else if(output instanceof CompletedVoid)returned=merge(unit,returned,Value.NULL.under(targetPath).requiring(gaps).tracing(dependencies));
                    else if(output instanceof Awaiting)waiting=true;
                } else if (target.isPresent() && target.get().hasBody() && !knowledge.isImpact(target.get().id())
                        && program.type(target.get().id().owner(),target.get().id().loader()).orElseThrow().role() != Inputs.Role.PLATFORM) {
                    int relation = relation(unit, call.opcode() == Opcodes.INVOKESTATIC || call.opcode() == Opcodes.INVOKESPECIAL ? Kind.DIRECT_CALL : Kind.VIRTUAL_CALL,
                            Optional.of(target.get().id()), evidence, actualReceiver, arguments, List.of(call.site()), gaps, targetPath, "JVM invocation", c.dependencies());
                    Value output = invoke(unit, target.get().id(), actualReceiver, arguments, targetPath, gaps, relation);
                    if (output.empty()) { if (unit.thrown.empty()) waiting = true; } else returned = merge(unit,returned,output.tracing(relation < 0 ? Set.of() : Set.of(relation)));
                } else {
                    gaps=new ArrayList<>(externalCall(unit,call.target(),actualReceiver,arguments,targetPath,gaps,c.dependencies()));
                    if (call.target().owner().equals("<invokedynamic>")) gaps.add(new Gap(GapKind.UNSUPPORTED, call.site(), "invokedynamic bootstrap semantics not modeled"));
                    else if (target.isEmpty() && resolution.pending().isEmpty()) gaps.add(new Gap(GapKind.MISSING_DEPENDENCY, call.site(), "method body unavailable: " + call.target()));
                    else if (!returnType.isVoid()) gaps.add(new Gap(GapKind.UNSUPPORTED, call.site(), "unmodeled platform/native result: " + call.target()));
                    if (call.target().name().equals("<init>")) {
                        Gap normal=new Gap(GapKind.CONTROL_CONDITION,call.site(),"unmodeled constructor normal-completion conditions: "+call.target());
                        gaps.add(normal);unit.prerequisites.add(normal);unit.controlDependencies.addAll(c.dependencies());
                    }
                    int producer=relation(unit, call.opcode() == Opcodes.INVOKESTATIC || call.opcode() == Opcodes.INVOKESPECIAL ? Kind.DIRECT_CALL : Kind.VIRTUAL_CALL,
                            target.map(Method::id).or(() -> Optional.of(call.target())), evidence, actualReceiver, arguments, List.of(call.site()), gaps, targetPath, "external JVM call; body not expanded", c.dependencies());
                    Atom atom = returnType.isVoid() ? new Literal(null)
                            : returnType.reference() ? resultObject
                            : new Unknown("result of " + call.target());
                    returned = merge(unit,returned,unresolvedReturn(unit,atom,targetPath,gaps,producer<0?c.dependencies():Set.of(producer)));
                }
                }
            }
        }
        if (!waiting || !returned.empty()) {
            for(Bound bound:returned.alternatives())if(bound.atom() instanceof ArrayValue array)
                Iterations.arrayPlan(state.facts,call.site().instruction(),array,state.loops).ifPresent(plan -> instantiate(unit,plan,unit));
            finish(unit, returned);
        }
    }

    /** A dynamically selected API consumes exactly the same registered local semantics. */
    private EffectResult effects(Unit unit, Invocation invocation, Local local, List<Gap> incoming, Set<Integer> dependencies, int depth, List<Integer> previous,List<ExceptionFlow> wrappers) {
        if(unit.consumption.isPresent())return evaluateEffects(unit,invocation,local,incoming,dependencies,depth,previous,wrappers);
        EffectRequest request=new EffectRequest(invocation,local,incoming,dependencies,depth,previous,wrappers,unit.effects);
        if(unit.effectView.filter(view -> view.definitions()==program.definitionCount() && view.operations()==definitionOperations && view.request().equals(request)
                && unchanged(unit,view.reads()) && view.returns().entrySet().stream().allMatch(e -> e.getValue().equals(ReturnedView.of(e.getKey())))
                && view.supports().entrySet().stream().allMatch(e -> evidence.relation(e.getKey()).map(r -> r.supports().size()==e.getValue()).orElse(false))).isPresent()) {
            effectReuses++;return unit.effectView.orElseThrow().result();
        }
        Consumption active=new Consumption();unit.consumption=Optional.of(active);
        try {
            EffectResult output=evaluateEffects(unit,invocation,local,incoming,dependencies,depth,previous,wrappers);
            if(!active.incomplete && !(output instanceof Awaiting) && steps<limits.steps() && evidence.size()<limits.relations()
                    && (!(output instanceof Produced produced) || produced.value().alternatives().stream().noneMatch(b -> b.atom() instanceof Truncated || b.gaps().stream().anyMatch(g -> g.kind()==GapKind.BUDGET)))) {
                Map<State,ReturnedView> returns=new LinkedHashMap<>();active.callees.forEach(c -> returns.put(c,ReturnedView.of(c)));
                Set<Integer> supports=new LinkedHashSet<>(dependencies);
                active.reads.values().forEach(value -> value.alternatives().forEach(b -> supports.addAll(b.dependencies())));
                returns.values().forEach(value -> {value.value().alternatives().forEach(b -> supports.addAll(b.dependencies()));value.thrown().alternatives().forEach(b -> supports.addAll(b.dependencies()));});
                Map<Integer,Integer> versions=new LinkedHashMap<>();supports.forEach(id -> evidence.relation(id).ifPresent(r -> versions.put(id,r.supports().size())));
                unit.effectView=Optional.of(new EffectView(request,output,Map.copyOf(active.reads),Map.copyOf(returns),Map.copyOf(versions),program.definitionCount(),definitionOperations));
            } else unit.effectView=Optional.empty();
            return output;
        } finally {unit.consumption=Optional.empty();}
    }
    private EffectResult evaluateEffects(Unit unit,Invocation invocation,Local local,List<Gap> incoming,Set<Integer> dependencies,int depth,List<Integer> previous,List<ExceptionFlow> wrappers) {
        List<Integer> parent=unit.effects;
        try {
        AlternativeScope alternativeScope=new AlternativeScope(invocation.call().target(),new CallBinding(invocation.receiver(),invocation.arguments()),parent);
        int allowed=unit.alternativeTurns.getOrDefault(alternativeScope,1);
        Map<Integer,Integer> batches=new HashMap<>();
        Value result = Value.BOTTOM;
        EffectState state=EffectState.NORMAL;
        Optional<EffectState> conditionalState=Optional.empty();
        boolean alternatives=false;
        List<Integer> dispatched = new ArrayList<>(previous);
        for(Effect effect:local.effects())if(effect instanceof Need need) {
            Optional<Path> selected=candidateBindings.require(invocation.path(),need.input(),(object,slot) -> read(unit,object,slot));
            if(selected.isEmpty())return new Exceptional();
            invocation=CandidateBindings.project(invocation,selected.get());
        }
        for(Effect effect:local.effects())if(effect instanceof Need need)
            if(!requirements.add(unit.state.id,unit.state.entry.method().id(),unit.action.site(),invocation.path(),need.input(),dependencies))limit("input requirement budget");
        int position=0;
        for(Effect effect:local.effects()) {
            if(!(effect instanceof Conditional || effect instanceof Observe || effect instanceof Need) && conditionalState.isPresent()) {
                state=conditionalState.get();conditionalState=Optional.empty();
            }
            if(effect instanceof Alternative choice && batches.computeIfAbsent(choice.batch(),key -> batches.size())>=allowed) {
                unit.consumption.ifPresent(active -> active.incomplete=true);
                alternatives=true;unit.alternativeTurns.put(alternativeScope,allowed+1);offer(unit);state=EffectState.WAITING;
                if(positioned(effect))position++;continue;
            }

            if(steps>=limits.steps()) {
                String detail="local mechanism work budget at "+unit.action.site();limit(detail);
                return new Produced(bounded(result.merge(Value.of(new Truncated(detail),invocation.path()).requiring(List.of(new Gap(GapKind.BUDGET,unit.action.site(),detail)))),unit.action.site()));
            }
            steps++;
            unit.effects=effectPosition(parent,position);if(positioned(effect))position++;
            if(effect instanceof Need)continue;
            if(effect instanceof Alternative choice) {
                if(state==EffectState.EXCEPTIONAL)continue;
                alternatives=true;TargetChoice key=new TargetChoice(unit.state.id,unit.action.site().instruction(),iteration(unit),parent);
                conditions.uncertain(key,new Gap(GapKind.INPUT_BINDING,unit.action.site(),"conditional dynamic target selection requires an actual binding"));
                Optional<Path> selected=invocation.path().with(key,choice.selection());if(selected.isEmpty())continue;
                Invocation bound=new Invocation(invocation.call(),invocation.receiver(),invocation.arguments(),invocation.result(),selected.get(),invocation.evaluation());
                EffectResult output=effects(unit,bound,choice.local(),incoming,dependencies,depth,previous,wrappers);
                if(output instanceof Produced value)result=merge(unit,result,value.value());
                else if(output instanceof Awaiting)state=EffectState.WAITING;
                continue;
            }
            if(state!=EffectState.NORMAL && !(effect instanceof Observe || effect instanceof Conditional))continue;
            if (effect instanceof RequireNormal normal) {
                Invocation operation=normal.operation().orElse(invocation);
                NormalChoice key=new NormalChoice(unit.state.id,unit.action.site().instruction(),iteration(unit),unit.effects,operation.call().target(),operation.receiver(),operation.arguments());
                if(!normal.gaps().isEmpty() || conditions.uncertain(key))conditions.normal(key,operation,normal.gaps(),(object,slot) -> read(unit,object,slot));
                if(!normal.gaps().isEmpty()) {
                    invocation=CandidateBindings.project(invocation,invocation.path().with(key,0).orElseThrow());
                }
                Value completion=Value.of(normal.gaps().isEmpty()?NormalValue.CERTAIN:NormalValue.CONDITIONAL,invocation.path()).requiring(union(incoming,List.copyOf(unit.prerequisites))).tracing(dependencies);
                unit.normal=Optional.of(unit.normal.orElse(Value.BOTTOM).merge(completion));
            } else if(effect instanceof DefineClass definition) {
                try {
                    int previousDefinitions=program.definitionCount();
                    Query<DefinedType> defined=program.define(definition.loader(),definition.content(),definition.content().bytes(),definition.offset(),definition.length(),definition.requested(),definition.content().source());
                    if(defined.value().isEmpty()) {
                        List<Gap> gaps=JvmSemantics.queryGaps(unit.action.site(),defined);gaps.forEach(gap -> limit(gap.detail()));
                        result=merge(unit,result,Value.of(new Unknown("definition budget"),invocation.path()).requiring(union(incoming,gaps)).tracing(dependencies));
                    } else {
                        DefinedType type=defined.value().orElseThrow();
                        Optional<Path> normal=definition(unit,type,invocation,incoming,dependencies);
                        if(normal.isEmpty()){state=EffectState.EXCEPTIONAL;continue;}
                        List<Gap> policy=List.of(new Gap(GapKind.DEPLOYMENT,unit.action.site(),"target VM verification and defining-loader access/dependency resolution must permit this class"));
                        result=merge(unit,result,Value.of(new ClassValue("L"+type.name()+";",true,Optional.empty(),type.loader()),normal.get()).requiring(union(incoming,policy)).tracing(dependencies));
                        if(program.definitionCount()!=previousDefinitions)for(State context:states)for(Unit consumer:context.units) {
                            Action action=consumer.action;
                            if(action instanceof Cast || action instanceof ReadField field && field.field().owner().equals(type.name())
                                    || action instanceof WriteField field && field.field().owner().equals(type.name())
                                    || action instanceof Call call && (call.target().owner().equals(type.name())
                                        || Set.of("java/lang/Class","java/lang/reflect/Method","java/lang/reflect/Constructor","java/lang/invoke/MethodHandles$Lookup").contains(call.target().owner())))offer(consumer);
                        }
                    }
                } catch(IllegalArgumentException | ArrayIndexOutOfBoundsException invalid) {
                    throwing(unit,"java/lang/ClassFormatError",invocation.path(),incoming);state=EffectState.EXCEPTIONAL;
                } catch(Program.DefinitionConflict duplicate) {
                    Optional<Path> normal=definition(unit,duplicate.type(),invocation,incoming,dependencies);
                    if(normal.isEmpty())state=EffectState.EXCEPTIONAL;
                    else {
                        Gap conflict=new Gap(GapKind.UNSUPPORTED,unit.action.site(),duplicate.getMessage()+" on alternative definition paths");
                        result=merge(unit,result,Value.of(new Unknown(conflict.detail()),normal.get()).requiring(union(incoming,List.of(conflict))).tracing(dependencies));
                    }
                }
            } else if(effect instanceof Initialize initialization) {
                if(!initialized(unit,initialization.owner(),invocation.path(),new LinkedHashSet<>(),wrappers,initialization.loader(),true))
                    state=unit.thrown.under(invocation.path()).empty()?EffectState.WAITING:EffectState.EXCEPTIONAL;
            } else if (effect instanceof Iterate iteration) {
                orderedLoop(unit,iteration.iterator());
            } else if (effect instanceof Deferred deferredCall) {
                defer(unit,invocation,deferredCall,incoming,dependencies);
            } else if (effect instanceof Raise raised) {
                Value exception=Value.of(object(unit,unit.action.site().instruction(),raised.type(),"intrinsic exceptional result",true),invocation.path()).requiring(incoming);
                throwing(unit,wrapped(unit,exception,wrappers,invocation.path(),incoming));state=EffectState.EXCEPTIONAL;
            } else if(effect instanceof Evaluate evaluation) {
                if(depth>=limits.depth()) {limit("local evaluation depth budget at "+unit.action.site());state=EffectState.WAITING;}
                else {
                    Optional<Path> path=invocation.path().and(evaluation.invocation().path());if(path.isEmpty())continue;
                    Invocation selected=CandidateBindings.project(evaluation.invocation(),path.get());
                    Local evaluated=model(unit,selected).orElseThrow(() -> new IllegalStateException("local evaluation has no mechanism: "+evaluation.invocation().call().target()));
                    EffectResult output=effects(unit,selected,evaluated,incoming,dependencies,depth+1,dispatched,wrappers);
                    if(output instanceof Produced value)result=merge(unit,result,value.value());
                    else if(output instanceof Awaiting)state=EffectState.WAITING;
                    else if(output instanceof Exceptional)state=EffectState.EXCEPTIONAL;
                }
            } else if(effect instanceof IgnoreResult ignored) {
                EffectResult output=effects(unit,invocation,ignored.local(),incoming,dependencies,depth,previous,wrappers);
                if(output instanceof Awaiting)state=EffectState.WAITING;else if(output instanceof Exceptional)state=EffectState.EXCEPTIONAL;
            } else if(effect instanceof Concat concat) {
                EffectResult suffix=effects(unit,invocation,concat.suffix(),incoming,dependencies,depth,previous,wrappers);
                if(suffix instanceof Produced produced) {
                    int count=0;
                    concatenation:for(Bound prefix:concat.prefix().under(invocation.path()).alternatives())for(Bound end:produced.value().under(prefix.path()).alternatives()) {
                        if(count++>=limits.alternatives()){limit("string concatenation binding budget at "+unit.action.site());break concatenation;}
                        Atom value=Mechanisms.concatenate(List.of(prefix.atom(),end.atom()));
                        List<Gap> gaps=union(prefix.gaps(),end.gaps());
                        if(value instanceof Truncated truncated)gaps=union(gaps,List.of(new Gap(GapKind.BUDGET,unit.action.site(),truncated.reason())));
                        Set<Integer> required=new LinkedHashSet<>(prefix.dependencies());required.addAll(end.dependencies());
                        result=merge(unit,result,Value.of(value,end.path()).requiring(gaps).tracing(required));
                    }
                } else if(suffix instanceof Awaiting)state=EffectState.WAITING;else if(suffix instanceof Exceptional)state=EffectState.EXCEPTIONAL;
            } else if (effect instanceof Store store) {
                EffectResult stored=effects(unit,invocation,store.local(),incoming,dependencies,depth,previous,wrappers);
                if(stored instanceof Awaiting){state=EffectState.WAITING;continue;}
                if(stored instanceof Exceptional){state=EffectState.EXCEPTIONAL;continue;}
                if(!(stored instanceof Produced produced))throw new IllegalStateException("store sequence requires a value: "+store.slot());
                Value output=produced.value();
                if(store.descriptor().isPresent()) {
                    Value checked=Value.BOTTOM;
                    for(Bound value:output.alternatives()) {
                        JvmSemantics.Conversion conversion=jvm.cast(new Cast(unit.action.site(),Values.type(store.descriptor().get()),new Sources(Set.of())),value.atom());
                        if(conversion instanceof JvmSemantics.Converted converted) {
                            for(Bound binding:converted.value().alternatives())unit.prerequisites.addAll(binding.gaps());
                            checked=checked.merge(converted.value().under(value.path()).requiring(value.gaps()).tracing(value.dependencies()));
                        }
                        else throwing(unit,((JvmSemantics.Rejected)conversion).exception(),value.path(),value.gaps());
                    }
                    output=checked;
                }
                unit.effects=effectPosition(unit.effects,(int)store.local().effects().stream().filter(Analyzer::positioned).count());
                if(output.empty())state=unit.thrown.empty()?EffectState.WAITING:EffectState.EXCEPTIONAL;else write(unit,store.receiver(),store.slot(),output);
            } else if (effect instanceof Conditional conditional) {
                if(state!=EffectState.NORMAL)continue;
                for (Gap gap:conditional.gaps()) if (gap.kind()==GapKind.BUDGET) limit(gap.detail());
                Optional<Path> path = invocation.path().and(conditional.path());
                if (path.isEmpty()) continue;
                Invocation selected = new Invocation(invocation.call(), invocation.receiver(), invocation.arguments(), invocation.result(), path.get(),invocation.evaluation());
                Set<Integer> required = new LinkedHashSet<>(dependencies); required.addAll(conditional.dependencies());
                EffectResult output=effects(unit,selected,conditional.local(),union(incoming,conditional.gaps()),Set.copyOf(required),depth,previous,wrappers);
                EffectState branch=output instanceof Awaiting?EffectState.WAITING:output instanceof Exceptional?EffectState.EXCEPTIONAL:EffectState.NORMAL;
                if(output instanceof Produced value)result=merge(unit,result,value.value());
                conditionalState=Optional.of(conditionalState.isEmpty()?branch:
                        conditionalState.get()==EffectState.NORMAL || branch==EffectState.NORMAL?EffectState.NORMAL:
                        conditionalState.get()==EffectState.WAITING || branch==EffectState.WAITING?EffectState.WAITING:EffectState.EXCEPTIONAL);
            } else if (effect instanceof Result returned) {
                if(returned.value().empty())state=EffectState.WAITING;
                for (Bound bound:returned.value().alternatives()) for (Gap gap:bound.gaps()) if (gap.kind()==GapKind.BUDGET) limit(gap.detail());
                result = merge(unit,result,returned.value().under(invocation.path()).requiring(incoming).tracing(dependencies));
            }
            else if (effect instanceof Write write) {
                write(unit,write.receiver(),write.slot(),write.value().under(invocation.path()).requiring(incoming).tracing(dependencies));
            }
            else if(effect instanceof Construct construction) {
                if(!initialized(unit,construction.constructor().owner(),invocation.path(),new LinkedHashSet<>(),wrappers,construction.constructor().loader())) {
                    state=unit.thrown.under(invocation.path()).empty()?EffectState.WAITING:EffectState.EXCEPTIONAL;continue;
                }
                ObjectValue allocated=object(unit,unit.action.site().instruction(),construction.constructor().owner(),"constructed instance",true,construction.constructor().loader());
                Local initialize=Local.of(new Dispatch(construction.constructor(),allocated,construction.arguments(),construction.kind(),construction.gaps().isEmpty()?Evidence.PROVEN:Evidence.CONDITIONAL,
                        construction.witnesses(),construction.gaps(),ReturnFlow.TO_RESULT,construction.exceptions()),
                        new Observe(construction.kind(),"resolved constructor "+construction.constructor(),construction.witnesses(),construction.gaps()));
                EffectResult completed=effects(unit,invocation,initialize,incoming,dependencies,depth,previous,wrappers);
                if(completed instanceof Produced produced)for(Bound normal:produced.value().alternatives()) {
                    result=merge(unit,result,Value.of(allocated,normal.path()).requiring(normal.gaps()).tracing(normal.dependencies()));
                    for(int edge:normal.dependencies())if(!dispatched.contains(edge))dispatched.add(edge);
                }
                else if(completed instanceof Awaiting)state=EffectState.WAITING;
                else if(completed instanceof Exceptional)state=EffectState.EXCEPTIONAL;
            } else if (effect instanceof Dispatch dispatch) {
                Atom receiver = CandidateBindings.project(dispatch.receiver(),invocation.path());
                if (receiver instanceof Symbolic symbolic)
                    receiver = symbolic(unit,symbolic);
                Path selectedPath=invocation.path();
                List<Atom> arguments=dispatch.arguments().stream().map(a -> CandidateBindings.project(a,selectedPath)).map(a -> a instanceof Symbolic symbolic?(Atom)symbolic(unit,symbolic):a).toList();
                List<Gap> gaps = union(incoming, dispatch.gaps());
                if(knowledge.isImpact(dispatch.target())) {
                    ObjectValue impactResult=object(unit,unit.action.site().instruction(),Values.type(program.signature(dispatch.target()).returned().descriptor()),"impact condition result",false);
                    Invocation impactCall=new Invocation(new Call(unit.action.site(),dispatch.target(),Opcodes.INVOKEVIRTUAL,new Sources(Set.of()),List.of()),receiver,arguments,impactResult,invocation.path());
                    Optional<Local> localImpact=model(unit,impactCall);
                    if(localImpact.flatMap(check -> Mechanisms.normalCompletion(check,impactCall.path())).equals(Optional.of(false))) {
                        relation(unit,dispatch.kind(),Optional.of(dispatch.target()),dispatch.evidence(),receiver,arguments,dispatch.witnesses(),gaps,invocation.path(),"impact call reached; finite JVM/API preconditions reject this binding",dependencies);
                        effects(unit,impactCall,localImpact.orElseThrow(),gaps,dependencies,depth+1,previous,wrapping(dispatch.exceptions(),wrappers));
                        state=EffectState.EXCEPTIONAL;continue;
                    }
                }
                for(Gap gap:gaps)if(gap.kind()==GapKind.BUDGET)limit(gap.detail());
                int edge = relation(unit, dispatch.kind(), Optional.of(dispatch.target()), dispatch.evidence(), receiver,
                        arguments, dispatch.witnesses(), gaps, invocation.path(), "local mechanism dispatch", dependencies);
                if (edge >= 0) dispatched.add(edge);
                if (knowledge.isImpact(dispatch.target())) {
                    int impact = relation(unit, Kind.IMPACT, Optional.of(dispatch.target()), dispatch.evidence(), receiver, dispatch.arguments(),
                            dispatch.witnesses(), gaps, invocation.path(), "dynamically bound impact API; no target execution performed");
                    observe(unit, impact, dispatched);
                }
                Value output;
                if(knowledge.isImpact(dispatch.target()) && !dispatch.target().name().equals("defineClass")) {
                    // The requested impact is this API boundary. Its implementation is not a new search root.
                    Atom value=program.signature(dispatch.target()).returned().isVoid()?new Literal(null):object(unit,unit.action.site().instruction(),Values.type(program.signature(dispatch.target()).returned().descriptor()),"impact API result",false);
                    output=Value.of(value,invocation.path()).requiring(union(gaps,List.of(new Gap(GapKind.CONTROL_CONDITION,unit.action.site(),"impact API normal completion is not established"))));
                } else if (depth >= limits.depth()) {
                    String detail = "local mechanism expansion depth budget at " + unit.action.site();
                    limit(detail);
                    output = Value.of(new Truncated(detail), invocation.path()).requiring(union(gaps, List.of(new Gap(GapKind.BUDGET, unit.action.site(), detail))));
                } else {
                    Call target = new Call(unit.action.site(), dispatch.target(), Opcodes.INVOKEVIRTUAL, new Sources(Set.of()), List.of());
                    ObjectValue object = object(unit, unit.action.site().instruction(), Values.type(program.signature(dispatch.target()).returned().descriptor()),
                            "dynamic result of " + dispatch.target(), false);
                    Invocation bound = new Invocation(target, receiver, arguments, object, invocation.path());
                    Optional<Local> model = model(unit,bound);
                    if(model.isPresent()) {
                        EffectResult computed=effects(unit,bound,model.get(),gaps,dependencies,depth+1,dispatched,wrapping(dispatch.exceptions(),wrappers));
                        if(computed instanceof Awaiting){state=EffectState.WAITING;continue;}
                        if(computed instanceof Exceptional){state=EffectState.EXCEPTIONAL;continue;}
                        if(computed instanceof Produced produced)output=produced.value();
                        else {
                            if(!program.signature(dispatch.target()).returned().isVoid())throw new IllegalStateException("nonvoid dispatch mechanism omitted its result: "+dispatch.target());
                            output=Value.NULL.under(invocation.path()).requiring(gaps).tracing(dependencies);
                        }
                    } else if(program.type(dispatch.target().owner(),dispatch.target().loader()).filter(info -> info.role()==Inputs.Role.PLATFORM).isPresent()) {
                        List<Gap> pending=externalCall(unit,dispatch.target(),receiver,arguments,invocation.path(),gaps,dependencies);
                        output=unresolvedReturn(unit,program.signature(dispatch.target()).returned().isVoid()?new Literal(null):object,invocation.path(),pending,edge<0?dependencies:Set.of(edge));
                        int frontier=relation(unit,Kind.DYNAMIC_CALL,Optional.of(dispatch.target()),Evidence.CONDITIONAL,receiver,arguments,dispatch.witnesses(),pending,invocation.path(),"platform callback frontier",edge<0?dependencies:Set.of(edge));observe(unit,frontier,List.of());
                    } else output=invoke(unit,dispatch.target(),receiver,arguments,invocation.path(),gaps,edge,wrapping(dispatch.exceptions(),wrappers),dispatch.returns()==ReturnFlow.TO_RESULT);
                }
                if(output.empty())state=unit.thrown.under(invocation.path()).empty()?EffectState.WAITING:EffectState.EXCEPTIONAL;
                else if (dispatch.returns() == ReturnFlow.TO_RESULT) result = merge(unit,result,output.tracing(edge < 0 ? Set.of() : Set.of(edge)));
            } else if (effect instanceof Observe observation) {
                for(Gap gap:observation.gaps())if(gap.kind()==GapKind.BUDGET)limit(gap.detail());
                int edge = relation(unit, observation.kind(), Optional.empty(), observation.gaps().isEmpty() ? Evidence.PROVEN : Evidence.CONDITIONAL,
                        invocation.receiver(), invocation.arguments(), observation.witnesses(), union(incoming, observation.gaps()), invocation.path(), observation.detail(), dependencies);
                observe(unit, edge, dispatched);
            }
        }
        if(conditionalState.isPresent())state=conditionalState.get();
        if(state==EffectState.EXCEPTIONAL)return new Exceptional();
        if(alternatives && !result.empty())return new Produced(result);
        if(state==EffectState.WAITING || alternatives && result.empty())return new Awaiting();
        return result.empty()?new CompletedVoid():new Produced(result);
        }finally{unit.effects=parent;}
    }

    private static boolean positioned(Effect effect) {
        return !(effect instanceof Observe || effect instanceof Need || effect instanceof Result || effect instanceof RequireNormal);
    }

    /** Program owns parsed facts; this scan owns actual positioned definition attempts. */
    private Optional<Path> definition(Unit unit,DefinedType type,Invocation invocation,List<Gap> gaps,Set<Integer> dependencies) {
        Map<DefinitionOperation,Unit> uses=definitions.computeIfAbsent(type,key -> new LinkedHashMap<>());
        ExecutionPoint point=writer(unit);List<Path> previous=new ArrayList<>();
        for(DefinitionOperation operation:uses.keySet())if(!operation.point().equals(point)
                && heap.before(operation.point(),point) && operation.path().compatible(invocation.path())) {
            Path overlap=operation.path().and(invocation.path()).orElseThrow();
            throwing(unit,Value.of(object(unit,unit.action.site().instruction(),"java/lang/LinkageError","duplicate class definition",true),overlap).requiring(gaps).tracing(dependencies));
            if(conditions.implied(operation.path(),invocation.path()))return Optional.empty();
            previous.add(operation.path());
        }
        if(uses.putIfAbsent(new DefinitionOperation(point,invocation.path()),unit)==null) {
            definitionOperations++;uses.values().stream().filter(consumer -> consumer!=unit).forEach(this::offer);
        }
        if(previous.isEmpty())return Optional.of(invocation.path());
        NormalChoice key=new NormalChoice(unit.state.id,unit.action.site().instruction(),iteration(unit),unit.effects,invocation.call().target(),invocation.receiver(),invocation.arguments());
        conditions.excluding(key,previous,new Gap(GapKind.CONTROL_CONDITION,unit.action.site(),"normal class definition requires no earlier definition of this name in the same loader"));
        return invocation.path().with(key,0);
    }

    private ObjectValue symbolic(Unit unit,Symbolic value) {
        ObjectValue object=object(unit,unit.action.site().instruction(),value.type(),value.requirement(),false,value.loader());
        return new ObjectValue(object.id(),object.type(),false,object.origin(),false,value.source(),program.scope(value.type(),value.loader()));
    }

    private static List<Integer> effectPosition(List<Integer> parent,int index) {
        List<Integer> position=new ArrayList<>(parent);position.add(index);return List.copyOf(position);
    }

    private Query<List<VirtualTarget>> dispatch(Call call, Atom receiver) {
        if(call.opcode()!=Opcodes.INVOKESTATIC && call.opcode()!=Opcodes.INVOKESPECIAL && receiver instanceof ObjectValue object && !object.exact())
            return program.implementations(call.target(),object.type(),object.loader(),ranking.receivers(call,object.type(),object.loader()).value().orElseThrow());
        Query<Method> selected=call.opcode()==Opcodes.INVOKESTATIC || call.opcode()==Opcodes.INVOKESPECIAL?program.lookup(call.target()):receiver instanceof ObjectValue object?program.lookup(program.method(object.type(),call.target().name(),call.target().descriptor(),object.loader())):program.lookup(call.target());
        return new Query<>(Optional.of(selected.value().map(m -> List.of(new VirtualTarget(m,Optional.empty(),selected.pending()))).orElse(List.of())),selected.value().isPresent()?List.of():selected.pending());
    }

    private static boolean sameBinding(Atom first,Atom second) {
        if(first instanceof Unknown || first instanceof Truncated || second instanceof Unknown || second instanceof Truncated)return false;
        if(first.equals(second))return true;
        if(first.getClass()!=second.getClass())return false;
        if(first instanceof ObjectValue a && second instanceof ObjectValue b)return a.loader()==b.loader() && a.type().equals(b.type()) && a.source().isPresent() && a.source().equals(b.source());
        if(first instanceof Symbolic a && second instanceof Symbolic b)return a.type().equals(b.type()) && a.source().isPresent() && a.source().equals(b.source());
        if(first instanceof ArrayValue a && second instanceof ArrayValue b)return a.extent()==ArrayExtent.EXACT && b.extent()==ArrayExtent.EXACT && a.order()==ArrayOrder.INDEXED && b.order()==ArrayOrder.INDEXED && a.elements().size()==b.elements().size() && java.util.stream.IntStream.range(0,a.elements().size()).allMatch(i -> sameBinding(a.elements().get(i),b.elements().get(i)));
        if(first instanceof Reflected a && second instanceof Reflected b)return a.lookup().equals(b.lookup()) && a.declared()==b.declared() && sameBinding(a.declaringClass(),b.declaringClass()) && sameBinding(a.name(),b.name()) && sameBinding(a.parameterTypes(),b.parameterTypes());
        return false;
    }

    private Value invoke(Unit caller,MethodId target,Atom receiver,List<Atom> arguments,Path path,List<Gap> gaps,int relation) {
        return invoke(caller,target,receiver,arguments,path,gaps,relation,List.of(),true);
    }
    private Value invoke(Unit caller, MethodId target, Atom receiver, List<Atom> arguments, Path path, List<Gap> gaps, int relation,List<ExceptionFlow> wrappers,boolean dataReturn) {
        Query<Method> declaration=program.declaration(target);
        if(declaration.absent())declaration=program.lookup(target);
        if(declaration.value().isEmpty() || !declaration.value().get().hasBody()) {
            Set<Integer> dependencies=relation<0?Set.of():Set.of(relation);
            List<Gap> required=union(externalCall(caller,target,receiver,arguments,path,gaps,dependencies),JvmSemantics.queryGaps(caller.action.site(),declaration));
            required=union(required,List.of(new Gap(GapKind.CONTROL_CONDITION,caller.action.site(),"selected callback normal completion is unresolved: "+target)));
            Atom value=program.signature(target).returned().isVoid()?new Literal(null):new Unknown("selected callback body unavailable: "+target);
            return unresolvedReturn(caller,value,path,required,dependencies);
        }
        target=declaration.value().get().id();
        State recursive=caller.state;
        while(true) {
            CallBinding previous=recursive.key.binding();
            if(recursive.key.target().equals(target) && sameBinding(previous.receiver(),receiver) && previous.arguments().size()==arguments.size()
                    && java.util.stream.IntStream.range(0,arguments.size()).allMatch(i -> sameBinding(previous.arguments().get(i),arguments.get(i)))
                    && recursive.key.path().and(path).isPresent()) {
                recursive.returnConsumers.add(caller);
                State selected=recursive;caller.consumption.ifPresent(active -> active.callees.add(selected));
                if(recursive.returned.empty()) {
                    Gap cycle=new Gap(GapKind.UNSUPPORTED,caller.action.site(),"recursive invocation awaits the same receiver and argument context");
                    int frontier=relation(caller,Kind.DYNAMIC_CALL,Optional.of(target),Evidence.CONDITIONAL,receiver,arguments,List.of(caller.action.site()),union(gaps,List.of(cycle)),path,cycle.detail(),relation<0?Set.of():Set.of(relation));observe(caller,frontier,List.of());
                }
                return recursive.returned.under(path);
            }
            if(recursive.key.parent()<0)break;recursive=states.get(recursive.key.parent());
        }
        int depth = 0;
        State ancestor = caller.state;
        while (ancestor.key.parent() >= 0) { ancestor = states.get(ancestor.key.parent()); depth++; }
        if (depth >= limits.depth()) {
            limit("call depth budget at " + caller.action.site());
            return unresolvedReturn(caller,new Unknown("call depth truncated"),path,union(gaps,List.of(new Gap(GapKind.BUDGET,caller.action.site(),"call depth budget"))),relation<0?Set.of():Set.of(relation));
        }
        InvocationKey key = new InvocationKey(caller.state.id, caller.action.site(), target, path,iteration(caller),phase(caller),new CallBinding(receiver,arguments),caller.effects);
        State child = contexts.get(key);
        boolean fresh = child == null;
        if (fresh) {
            child = create(key, caller.state.entry, relation);
            if (child == null) return unresolvedReturn(caller,new Unknown("invocation context truncated"),path,union(gaps,List.of(new Gap(GapKind.BUDGET,caller.action.site(),"invocation context budget"))),relation<0?Set.of():Set.of(relation));
        }
        child.returnConsumers.add(caller);
        State selectedChild=child;caller.consumption.ifPresent(active -> active.callees.add(selectedChild));
        if(dataReturn)caller.dataReturns.add(child);
        int slot = 0;
        if (!child.facts.method().isStatic()) updateParameter(child, slot++, Value.of(receiver, path).requiring(gaps).tracing(relation < 0 ? Set.of() : Set.of(relation)));
        List<ValueType> types = program.signature(target).parameters();
        for (int i = 0; i < arguments.size(); i++) {
            updateParameter(child, slot, Value.of(arguments.get(i), path).requiring(gaps).tracing(relation < 0 ? Set.of() : Set.of(relation)));
            slot += types.get(i).slots();
        }
        Optional<Summaries.Template> summary=summaries.computeIfAbsent(target,k -> Summaries.derive(program.facts(k)));
        if(child.units.isEmpty() && summary.isPresent()) {
            Optional<Value> applied=Summaries.apply(summary.get(),child.parameters,(object,cell) -> read(caller,object,cell),program);
            if(applied.isPresent()) {
                summaryApplications++;
                Value value=applied.get();
                if(summary.get() instanceof Summaries.FieldReturn fieldReturn) {
                    ReadField field=fieldReturn.field();
                    for(Bound binding:child.parameters.get(fieldReturn.parameter().slot()).alternatives()) {
                        Set<Integer> dependencies=new LinkedHashSet<>(binding.dependencies());for(Bound returned:value.alternatives())dependencies.addAll(returned.dependencies());
                        int edge=relation(child.id,field.site(),Kind.FIELD_FLOW,Optional.empty(),Evidence.PROVEN,binding.atom(),List.of(),List.of(field.site()),binding.gaps(),binding.path(),"read "+field.field(),dependencies,Optional.of(new Field(field.field())));
                        if(edge>=0)value=value.tracing(Set.of(edge));
                    }
                }
                child.returned=bounded(child.returned.merge(value),caller.action.site());
                Value completed=Value.of(NormalValue.CERTAIN,path).tracing(relation<0?Set.of():Set.of(relation));
                if(summary.get() instanceof Summaries.FieldReturn fieldReturn) {
                    completed=Value.BOTTOM;
                    for(Bound receiverBinding:child.parameters.get(fieldReturn.parameter().slot()).alternatives())
                        completed=completed.merge(Value.of(NormalValue.CERTAIN,receiverBinding.path()).requiring(receiverBinding.gaps()).tracing(receiverBinding.dependencies()));
                }
                Value completion=evidence.control(child.id,caller.action.site(),completed,path);
                caller.normal=Optional.of(bounded(caller.normal.orElse(Value.BOTTOM).merge(completion),caller.action.site()));
                return child.returned;
            }
        }
        if (fresh || child.units.isEmpty()) initialize(child);
        if (!child.thrown.empty()) throwing(caller,wrapped(caller,child.thrown,wrappers,path,gaps));
        Value normal=Value.BOTTOM;
        for(Unit returned:child.units)if(returned.action instanceof Returned && returned.normal.isPresent())normal=normal.merge(returned.normal.get());
        if(!normal.empty()) {
            Value completion=evidence.control(child.id,caller.action.site(),normal,path).tracing(relation<0?Set.of():Set.of(relation));
            caller.normal=Optional.of(bounded(evidence.compact(caller.state.id,caller.action.site(),caller.normal.orElse(Value.BOTTOM).merge(completion)),caller.action.site()));
            // A void return conveys completion, not a tuple for each internal return path.
            if(program.signature(target).returned().isVoid()) {
                Set<Bound> values=new LinkedHashSet<>();for(Bound bound:completion.alternatives())values.add(new Bound(new Literal(null),bound.path(),bound.gaps(),bound.dependencies()));
                return new Value(values);
            }
        }
        return child.returned;
    }

    private Value unresolvedReturn(Unit caller,Atom value,Path path,List<Gap> gaps,Set<Integer> dependencies) {
        Value completion=Value.of(NormalValue.CONDITIONAL,path).requiring(gaps).tracing(dependencies);
        caller.normal=Optional.of(caller.normal.orElse(Value.BOTTOM).merge(completion));
        return Value.of(value,path).requiring(gaps).tracing(dependencies);
    }
    private List<Gap> externalCall(Unit unit,MethodId target,Atom receiver,List<Atom> arguments,Path path,List<Gap> incoming,Set<Integer> dependencies) {
        Gap missing=new Gap(GapKind.UNSUPPORTED,unit.action.site(),"unmodeled call normal completion, result and reachable object effects: "+target);
        List<Gap> gaps=union(incoming,List.of(missing));
        List<Atom> affected=new ArrayList<>(arguments);affected.add(receiver);
        HeapStore.Reachable reachable=heap.reachable(affected,
                new HeapStore.Use(writer(unit),unit.action.site(),path,unit.state.facts.cfg(),false),(int)Math.min(256,limits.steps()-steps));
        steps+=reachable.consumed();refinementWork+=reachable.consumed();
        for(Cell dependency:reachable.dependencies())readers.computeIfAbsent(dependency,key -> new LinkedHashSet<>()).add(unit);
        if(reachable.truncated()) {
            String detail="unmodeled call reachable-object frontier (64 objects/256 reference and slot reads) at "+unit.action.site();limit(detail);
            gaps=union(gaps,List.of(new Gap(GapKind.BUDGET,unit.action.site(),detail)));
        }
        for(ObjectValue object:reachable.objects())
            write(unit,object,new Mutation(),Value.of(new Unknown("object may have changed in "+target),path).requiring(gaps).tracing(dependencies));
        return gaps;
    }

    private static List<ExceptionFlow> wrapping(ExceptionFlow inner,List<ExceptionFlow> outer) {
        if(inner.rule().isEmpty())return outer;
        List<ExceptionFlow> rules=new ArrayList<>();rules.add(inner);rules.addAll(outer);return List.copyOf(rules);
    }
    private Query<Boolean> wraps(ExceptionRule rule,Atom exception) {
        if(rule.caught().isEmpty())return new Query<>(Optional.of(true),List.of());
        Optional<String> type=io.just.knowledge.ValueBindings.runtimeType(exception);
        if(type.isEmpty())return new Query<>(Optional.empty(),List.of());
        Query<Boolean> caught=program.assignable(type.get(),rule.caught().get());
        if(caught.value().equals(Optional.of(false)))return caught;
        List<QueryIssue> pending=new ArrayList<>(caught.pending());boolean unknown=caught.value().isEmpty();
        for(String bypass:rule.bypass()) {
            Query<Boolean> match=program.assignable(type.get(),bypass);
            if(match.value().equals(Optional.of(true)))return new Query<>(Optional.of(false),match.pending());
            pending.addAll(match.pending());unknown|=match.value().isEmpty();
        }
        return new Query<>(unknown?Optional.empty():Optional.of(true),List.copyOf(new LinkedHashSet<>(pending)));
    }
    private Value wrapped(Unit caller,Value exception,List<ExceptionFlow> wrappers,Path path,List<Gap> gaps) {
        Value value=exception.under(path).requiring(gaps);
        for (int level=0;level<wrappers.size();level++) {
            ExceptionRule rule=wrappers.get(level).rule().orElseThrow();Value output=Value.BOTTOM;
            for(Bound bound:value.alternatives()) {
                Query<Boolean> decision=wraps(rule,bound.atom());
                List<Gap> required=union(bound.gaps(),JvmSemantics.queryGaps(caller.action.site(),decision));
                if(decision.value().isEmpty() && decision.pending().isEmpty())required=union(required,List.of(new Gap(GapKind.CONTROL_CONDITION,caller.action.site(),"exception wrapping requires its runtime type")));
                Value cause=Value.of(bound.atom(),bound.path()).requiring(required).tracing(bound.dependencies());
                if(!decision.value().equals(Optional.of(true)))output=output.merge(cause);
                if(decision.value().equals(Optional.of(false)))continue;
                ObjectValue wrapper=object(caller,caller.action.site().instruction(),rule.wrapper(),"exception wrapper layer "+level,true);
                for(FieldId field:rule.causes()) {
                    Query<FieldId> declared=program.lookupField(field);required=union(required,JvmSemantics.queryGaps(caller.action.site(),declared));
                    if(declared.value().isPresent())write(caller,wrapper,new Field(declared.value().get()),cause);
                }
                output=output.merge(Value.of(wrapper,bound.path()).requiring(required).tracing(bound.dependencies()));
            }
            value=output;
        }
        return value;
    }

    private void updateParameter(State state, int slot, Value value) {
        Value old = state.parameters.getOrDefault(slot, Value.BOTTOM);
        Value joined = bounded(old.merge(value), state.key.call());
        if (old.equals(joined)) return;
        state.parameters.put(slot, joined);
        state.control=Optional.empty();
        for(Backward query:state.reverseConsumers.getOrDefault(new Parameter(slot),Set.of()))offer(query);
        for (Unit consumer : state.consumers.getOrDefault(new Parameter(slot), Set.of())) offer(consumer);
    }

    private int relation(Unit unit,Kind kind,Optional<MethodId> target,Evidence proof,Atom receiver,List<Atom> arguments,
                         List<Site> witnesses,List<Gap> gaps,Path path,String detail) {
        return relation(unit,kind,target,proof,receiver,arguments,witnesses,gaps,path,detail,Set.of());
    }
    private int relation(Unit unit,Kind kind,Optional<MethodId> target,Evidence proof,Atom receiver,List<Atom> arguments,
                         List<Site> witnesses,List<Gap> gaps,Path path,String detail,Collection<Integer> dependencies) {
        return relation(unit.state.id,unit.action.site(),kind,target,proof,receiver,arguments,witnesses,gaps,path,detail,dependencies,Optional.empty());
    }
    private int relation(int context,Site site,Kind kind,Optional<MethodId> target,Evidence proof,Atom receiver,List<Atom> arguments,
                         List<Site> witnesses,List<Gap> gaps,Path path,String detail,Collection<Integer> dependencies) {
        return relation(context,site,kind,target,proof,receiver,arguments,witnesses,gaps,path,detail,dependencies,Optional.empty());
    }
    private int relation(int context,Site site,Kind kind,Optional<MethodId> target,Evidence proof,Atom receiver,List<Atom> arguments,
                         List<Site> witnesses,List<Gap> gaps,Path path,String detail,Collection<Integer> dependencies,Optional<Slot> slot) {
        return evidence.record(context,site,kind,target,proof,receiver,arguments,witnesses,gaps,path,detail,dependencies,slot);
    }
    private void observe(Unit unit,int relation,List<Integer> additional) {evidence.observe(unit.state.id,relation,additional);}
    private static <T> List<T> union(List<T> a,List<T> b) {
        if(b.isEmpty())return a;if(a.isEmpty())return b;
        Set<T> result=new LinkedHashSet<>(a);result.addAll(b);return result.size()==a.size()?a:List.copyOf(result);
    }
}
