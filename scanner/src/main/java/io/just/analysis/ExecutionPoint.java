package io.just.analysis;

import java.util.*;

/** Immutable execution identity shared by scheduling and heap visibility. */
record ExecutionPoint(int context,int instruction,int iteration,Phase phase,List<Integer> effects) {
    ExecutionPoint {effects=List.copyOf(effects);}
    ExecutionPoint(int context,int instruction,int iteration,Phase phase){this(context,instruction,iteration,phase,List.of());}
    sealed interface Phase permits Startup,Request,Asynchronous {}
    record Startup() implements Phase {}
    record Request(int registration) implements Phase {}
    record Asynchronous(int registration,ExecutionPoint launch) implements Phase {}
    ExecutionPoint(int context,int instruction) {this(context,instruction,-1,new Startup());}
}
