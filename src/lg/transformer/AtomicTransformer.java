/*
 * Copyright (c) 2013, Khilan Gudka.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without 
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, 
 *    this list of conditions and the following disclaimer. 
 * 2. Redistributions in binary form must reproduce the above copyright notice, 
 *    this list of conditions and the following disclaimer in the documentation 
 *    and/or other materials provided with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" 
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE 
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF 
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
 * POSSIBILITY OF SUCH DAMAGE.
 */

package lg.transformer;

import java.io.*;
import java.util.*;
import java.util.concurrent.*;

import lg.analysis.VMMethodMarker;
import lg.analysis.local.*;
import lg.analysis.locks.*;
import lg.analysis.locks.dominators.LockDominatorsAnalysis;
import lg.analysis.paths.*;
import lg.analysis.paths.automata.Automaton;
import lg.analysis.paths.transformer.ITransformer;
import lg.analysis.paths.transformer.fast.Transformer;
import lg.analysis.paths.transformer.state.*;
import lg.cfg.*;
import lg.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.paddle.*;
import soot.jimple.toolkits.callgraph.*;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class AtomicTransformer extends SceneTransformer {

    public static boolean DEBUG = false;
    public static boolean REDUCE_CFG = false;
    public static boolean REDUCE_CFG_DELTA = false;
    public static boolean SHOW_SUMMARY = false;
    public static boolean OUTPUT_DOT = false;
    public static boolean EXCEPTIONS = false;
    public static boolean LVALUES = false;
    public static boolean AGGREGATE_EDGES = false;
    public static boolean NFA_TO_DFA = false;
    public static boolean LOCKS = false;
    public static boolean LOCKS_PRINT = false;
    public static boolean SAVE_NFAS = false;
    public static boolean NFA_LOCKS = false;
    public static boolean INTERMEDIATE_RESULTS = false;
    public static boolean LIBRARY = false;
    public static boolean NOTAILS = false;
    public static boolean TIME_COMPOSE = false;
    public static boolean COLD = false;
    public static boolean INSTRUMENT = false;
    public static boolean DELTAS = false;
    public static boolean HASHSET = false;
    public static boolean SWEEP = false;
    public static int START_COMPACTION = 0;
    public static int COMPACT_EVERY = 0;
    public static int THREADS = 0;
    public static ExecutorService POOL = null;
    public static boolean STORE_ENTRY = false;
    public static boolean COMPACT = false;
    public static boolean COMPACT_SUMMARIES = false;
    public static boolean STATS = false;
    public static boolean AVOID_DEADLOCK = false;
    public static List<Integer> METHODS_TO_IGNORE = new ArrayList<Integer>();
    public static String LOAD_SUMMARIES_FROM_FILE = null;
    public static String SAVE_SUMMARIES_TO_FILE = null;
    public static boolean ORDER_WORKLISTS = false;
    public static boolean METHOD_LIST = false;
    public static String MEM_INFO = null;
    public static boolean INSTRUMENT_DEBUG = false;
    public static List<String> TYPES_TO_IGNORE = null;
    public static boolean JUC = false;
    public static boolean REMOVE_REDUNDANT_IMPLICIT_LOCKING = false;
    public static boolean REMOVE_REDUNDANT_READ_LOCKS = false;
    public static boolean CLIENT_LIB_STATS_ONLY = false;
    public static boolean IGNORE_WAIT_NOTIFY = false;
    public static boolean THREAD_LOCAL = false;
    public static boolean THREAD_LOCAL_DEBUG = false;
    public static boolean INSTANCE_LOCAL = false;
    public static boolean REMOVE_DOMINATED_LOCKS = false;
    public static boolean CLASS_LOCAL = false;
    public static boolean METHOD_LOCAL = false;
    public static boolean GLOBAL_LOCK = false;
    public static boolean MANUAL_LOCKS = false;
    public static boolean IGNORE_UNREACHABLE_ATOMICS = false;
    public static boolean SLOW_TRANSFORMERS = false;
    
    @Override
	protected void internalTransform(String phaseName, Map options) {

		DEBUG = Boolean.parseBoolean((String)options.get("debug"));
		REDUCE_CFG = Boolean.parseBoolean((String)options.get("reduce-cfg"));
		REDUCE_CFG_DELTA = Boolean.parseBoolean((String)options.get("reduce-cfg-delta"));
		SHOW_SUMMARY = Boolean.parseBoolean((String)options.get("show-summary"));
		OUTPUT_DOT = Boolean.parseBoolean((String)options.get("output-dot"));
		EXCEPTIONS = Boolean.parseBoolean((String)options.get("exceptions"));
		LVALUES = Boolean.parseBoolean((String)options.get("lvalues"));
		AGGREGATE_EDGES = Boolean.parseBoolean((String)options.get("aggregate"));
		NFA_TO_DFA = Boolean.parseBoolean((String)options.get("dfa"));
		LOCKS = Boolean.parseBoolean((String)options.get("locks"));
		LOCKS_PRINT = Boolean.parseBoolean((String)options.get("locks-print"));
		INTERMEDIATE_RESULTS = Boolean.parseBoolean((String)options.get("intermediate-results"));
		LIBRARY = Boolean.parseBoolean((String)options.get("library"));
		NOTAILS = Boolean.parseBoolean((String)options.get("notails"));
		int methodStart= Integer.parseInt((String)options.get("method"));
		SAVE_NFAS = Boolean.parseBoolean((String)options.get("savenfas"));
		NFA_LOCKS = Boolean.parseBoolean((String)options.get("nfalocks"));
		COLD = Boolean.parseBoolean((String)options.get("cold"));
		INSTRUMENT = Boolean.parseBoolean((String)options.get("instrument"));
		TIME_COMPOSE = Boolean.parseBoolean((String)options.get("timecompose"));
		DELTAS = Boolean.parseBoolean((String)options.get("deltas"));
		HASHSET = Boolean.parseBoolean((String)options.get("hashset"));
		START_COMPACTION = Integer.parseInt((String)options.get("compaction"));
		COMPACT_EVERY = Integer.parseInt((String)options.get("compact-every"));
		SWEEP = Boolean.parseBoolean((String)options.get("sweep"));
		THREADS = Integer.parseInt((String)options.get("threads"));
//		POOL = Executors.newFixedThreadPool(THREADS);
		POOL = new MyThreadPoolExecutor(THREADS, THREADS, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue<Runnable>());
		STORE_ENTRY = Boolean.parseBoolean((String)options.get("store-entry"));
		COMPACT = Boolean.parseBoolean((String)options.get("compact"));
		COMPACT_SUMMARIES = Boolean.parseBoolean((String)options.get("compact-summaries"));
		STATS = Boolean.parseBoolean((String)options.get("stats"));
		AVOID_DEADLOCK = Boolean.parseBoolean((String)options.get("avoid-deadlock"));
		LOAD_SUMMARIES_FROM_FILE = (String)options.get("load-summaries");
		SAVE_SUMMARIES_TO_FILE = (String)options.get("save-summaries");
		ORDER_WORKLISTS = Boolean.parseBoolean((String)options.get("order-worklists"));;
		MEM_INFO = (String)options.get("meminfo");
		METHOD_LIST = Boolean.parseBoolean((String)options.get("method-list"));;
		INSTRUMENT_DEBUG = Boolean.parseBoolean((String)options.get("instrument-debug"));
		JUC = Boolean.parseBoolean((String)options.get("juc"));
		REMOVE_REDUNDANT_IMPLICIT_LOCKING = Boolean.parseBoolean((String)options.get("implicit-locking"));
		REMOVE_REDUNDANT_READ_LOCKS = Boolean.parseBoolean((String)options.get("read-locks"));
		CLIENT_LIB_STATS_ONLY = Boolean.parseBoolean((String)options.get("client-lib-stats-only"));
		IGNORE_WAIT_NOTIFY = Boolean.parseBoolean((String)options.get("ignore-wait-notify"));
		THREAD_LOCAL = Boolean.parseBoolean((String)options.get("thread-local"));
		THREAD_LOCAL_DEBUG = Boolean.parseBoolean((String)options.get("thread-local-debug"));
		INSTANCE_LOCAL = Boolean.parseBoolean((String)options.get("instance-local"));
		REMOVE_DOMINATED_LOCKS = Boolean.parseBoolean((String)options.get("lock-dominators"));
		CLASS_LOCAL = Boolean.parseBoolean((String)options.get("class-local"));
		METHOD_LOCAL = Boolean.parseBoolean((String)options.get("method-local"));
		GLOBAL_LOCK = Boolean.parseBoolean((String)options.get("global-lock"));
		MANUAL_LOCKS = Boolean.parseBoolean((String)options.get("manual-locks"));
		IGNORE_UNREACHABLE_ATOMICS = Boolean.parseBoolean((String)options.get("ignore-unreachable-atomics"));
		SLOW_TRANSFORMERS = Boolean.parseBoolean((String)options.get("slow-transformers"));
		
		Logger.println("");
		Logger.println("Running with options " + options);
		Logger.println("");
		printInfo();		
		
		startMemoryMonitor();

		// mark VM-specific methods
        VMMethodMarker.markMethods();
        
	    AtomicsFinder atomicFinder = new AtomicsFinder();
	    List<AtomicSection> atomics = atomicFinder.findAtomics();
	    
	    int reachable = 0;
	    for (AtomicSection a : atomics) {
	        reachable += (a.isReachable() ? 1 : 0);
	    }
	    Logger.println("Found " + atomics.size() + " atomics of which " + reachable + " are reachable");

	    for (AtomicSection a : atomics) {
	        Logger.println(" " + (a.isReachable() ? "** " : "") + a.getId() + " in " + a.getEnclosingUnitGraph().getBody().getMethod());
	    }

        outputClientLibStats(atomics);
	    
        if (CLIENT_LIB_STATS_ONLY) {
            stopMemoryMonitor();
            POOL.shutdown();
            return;
        }
        
        if (IGNORE_UNREACHABLE_ATOMICS && !MANUAL_LOCKS && !GLOBAL_LOCK) {
            Logger.println("Removing unreachable atomics from set");
            List<AtomicSection> unreachable = new ArrayList<AtomicSection>();
            for (AtomicSection a : atomics) {
                if (!a.isReachable()) {
                    unreachable.add(a);
                }
            }
            Logger.println(" - " + unreachable.size() + " unreachable atomics");
            atomics.removeAll(unreachable);
        }
        
	    
        PrintStream pathTimesFile, lockCountsFile, lockTimesFile, methodListFile;
        try {
            pathTimesFile = new PrintStream("pathsTimes.txt");
            lockCountsFile = new PrintStream("lockcounts.txt");
            lockTimesFile = new PrintStream("locksTimes.txt");
            methodListFile = new PrintStream("methods.txt");
        }
        catch(Exception e) {
            throw new RuntimeException(e);
        }
	    
        Map<AtomicSection,LockSet> atomicToLocks = new HashMap<AtomicSection, LockSet>();
        
        ThreadLocalAnalysis tla = null;
        if (AtomicTransformer.THREAD_LOCAL) {
            long startThreadLocal = System.currentTimeMillis();
            
            tla = new PaddleThreadLocalAnalysis();
            tla.doAnalysis();
            
            long threadLocalTook = System.currentTimeMillis() - startThreadLocal;
            AnalysisTimer.addForThreadLocalAnalysis(threadLocalTook);
        }
        InstanceLocalAnalysisTransformer ila = new InstanceLocalAnalysisTransformer();
        if (AtomicTransformer.INSTANCE_LOCAL) {
            long startInstanceLocal = System.currentTimeMillis();
            ila = new InstanceLocalAnalysisTransformer();
            ila.doAnalysis();
            long instanceLocalTook = System.currentTimeMillis() - startInstanceLocal;
            AnalysisTimer.addForInstanceLocalAnalysis(instanceLocalTook);
        }
        ClassLocalAnalysisTransformer cla = new ClassLocalAnalysisTransformer();
        if (AtomicTransformer.CLASS_LOCAL) {
            long startClassLocal = System.currentTimeMillis();
            cla = new ClassLocalAnalysisTransformer();
            cla.doAnalysis();
            long classLocalTook = System.currentTimeMillis() - startClassLocal;
            AnalysisTimer.addForClassLocalAnalysis(classLocalTook);
        }
        
        int atomicsDone = 0;
	    for (AtomicSection a : atomics) {
	        
	        Set<Component> components = new HashSet<Component>();
	        
	        // find all components
	        for (SootMethod m : a.getCalledMethods()) {
	            StronglyConnectedComponents scc = new StronglyConnectedComponents(m);
	            components.addAll(scc.getComponents());
	        }

	        if (METHOD_LIST) {
	            for (Component c : components) {
	                for (SootMethod m : c) {
	                    methodListFile.println(m.toString());
	                }
	            }
	            continue;
	        }
	        
	        Logger.println(components.size() + " components found");

	        int largestComponent = 0;
	        int numMethods = 0;
	        for (Component c : components) {
	            numMethods += c.size();
	            largestComponent = Math.max(c.size(), largestComponent);
	        }
	        
            Logger.println("\n");
            Logger.println("==============================================================");
            Logger.println("Atomic " + ++atomicsDone + " of " + atomics.size() + ": " + a.getId(), ANSICode.FG_MAGENTA);
            Logger.println("Enclosing method: " + a.getBody().getMethod());
            Logger.println("Largest component size: " + largestComponent);
            Logger.println("Total number of methods: " + numMethods);
            Logger.println("==============================================================");
            
            if (GLOBAL_LOCK) {
                // use a write type lock on java.lang.Object for the global lock
                LockSet locks = new LockSet();
                Type lockedType = RefType.v("java.lang.Object");
                TypeLock tl = new TypeLock(lockedType, true, false, false, false, false);
                locks.add(tl);
                atomicToLocks.put(a, locks);
                
                if (LOCKS_PRINT) {
                    locks.print();
                }
            }
            else if (MANUAL_LOCKS) {
                // use a write type lock on the monitor local
                LockSet locks = new LockSet();
                Local monitorLocal = a.getMonitorLocal();
                PathLock pl = new PathLock(null, new LocalLookup(monitorLocal, null), true, false, false, null, false, false, false, false, false, false);
                locks.add(pl);
                atomicToLocks.put(a, locks);

                if (LOCKS_PRINT) {
                    locks.print();
                }
            }
            else {
                long startPathsAnalysis = System.currentTimeMillis();
    
                StronglyConnectedComponentsDAG sccDag = new StronglyConnectedComponentsDAG(components);
                PathsAnalysis p = new PathsAnalysis(a, components, sccDag);
                p.doAnalysis();
                ITransformer atomicSummary = p.getAtomicSummary();
                Logger.println("Atomic's summary has " + atomicSummary.size() + " edges");
                    
                long pathsAnalysisTook = System.currentTimeMillis() - startPathsAnalysis;
                AnalysisTimer.addForPathsAnalysis(pathsAnalysisTook);
                
                Date pathsAnalysisTookDate = new Date(pathsAnalysisTook);
                Logger.println("Paths took: " + String.format("%2d:%2d:%2d", pathsAnalysisTookDate.getHours(), pathsAnalysisTookDate.getMinutes(), pathsAnalysisTookDate.getSeconds()));
                
                SootMethod m = a.getBody().getMethod();
                pathTimesFile.println((LIBRARY ? m.toString() : a.getId()) + "," + pathsAnalysisTook);
                
                if (AtomicTransformer.LOCKS) {
                    Logger.println("");
                    Logger.println("Locks:", ANSICode.FG_BLUE);
                    Logger.println("");
    
                    long startLocks = System.currentTimeMillis();
                    Automaton accesses = atomicSummary.getAccessesNfa();
                    Set<State> reachables = accesses.cleanup();
                    Logger.println("NFA size: " + accesses.size() + ", reachables: " + reachables.size());
                    
                    AutomatonToLocks convertor = new AutomatonToLocks(accesses, tla, ila, cla);
                    LockSet locks = (LockSet)convertor.getLocks();
    
                    long locksTook = System.currentTimeMillis()-startLocks;
                    AnalysisTimer.addForLocks(locksTook);            
                    
                    lockTimesFile.println((LIBRARY ? a.getBody().getMethod() : a.getId()) + "," + locksTook);
                    Date locksTookDate = new Date(locksTook);               
                    
                    if (INSTANCE_LOCAL) {
                        // add locks to protect instance and class local accesses (these local locks will not be instrumented)
                        long addInstanceLocalstartTime = System.currentTimeMillis();
                        locks.addRequiredLocksForInstanceLocalAccesses();
                        AnalysisTimer.addForInstanceLocalAnalysis(System.currentTimeMillis()-addInstanceLocalstartTime);
                    }
    
                    if (CLASS_LOCAL) {
                        long addClassLocalstartTime = System.currentTimeMillis();
                        locks.addRequiredLocksForClassLocalAccesses();
                        AnalysisTimer.addForClassLocalAnalysis(System.currentTimeMillis()-addClassLocalstartTime);
                    }
                    
                    // remove read locks if write lock already exists
                    locks.removeSubsumed();
                    
                    // remove method-local locks
                    if (METHOD_LOCAL) {
                        MethodEscapeAnalysisTransformer methodEscapeAnalysis = new MethodEscapeAnalysisTransformer(a, locks);
                        methodEscapeAnalysis.doAnalysis();
                    }
                    
                    Pair<Set<Lock>,Set<Lock>> sepLocks = locks.separateLocks();
                    Set<Lock> typeLocks = sepLocks.getFirst();
                    Set<Lock> pathLocks = sepLocks.getSecond();
                    
                    Logger.println("Locks: " + locks.size() + ", types: " + typeLocks.size() + ", paths: " + pathLocks.size() +", took: " + String.format("%2d:%2d:%2d", locksTookDate.getHours(), locksTookDate.getMinutes(), locksTookDate.getSeconds()));
    
                    atomicToLocks.put(a, locks);
                }
            }
	    }
	    
	    lockTimesFile.println("*," + AnalysisTimer.getTotalLocksAnalysis());

	    if (!GLOBAL_LOCK && !MANUAL_LOCKS) {
	    
    	    if (REMOVE_REDUNDANT_READ_LOCKS) {
    	        Logger.println("");
    	        Logger.println("* Performing redundant-read-locking optimisation");
    	        performRemoveRedundantReadLocksOptimisations(atomicToLocks);
    	        Logger.println("");
    	    }
            if (REMOVE_REDUNDANT_IMPLICIT_LOCKING) {
                Logger.println("");
                Logger.println("* Performing redundant-implicit-locking optimisation");
                performRemoveRedundantImplicitLockingOptimisation(atomicToLocks);
                Logger.println("");
            }	    
    	    // perform this last so that read-only locks do not become dominators
    	    if (REMOVE_DOMINATED_LOCKS) {
    	        Logger.println("");
    	        Logger.println(" * Performing lock dominators analysis");
    	        performLockDominatorsAnalysis(atomicToLocks);
    	        Logger.println("");		        
    	    }
    	    
	    }
	    
	    // output list locks again after all optimisations have been performed
	    // so that markings can be seen
	    if (LOCKS_PRINT) {
	        atomicsDone=0;
            for (AtomicSection a : atomics) {
                LockSet locks = atomicToLocks.get(a);
                Logger.println("\n");
                Logger.println("==============================================================");
                Logger.println("Atomic " + ++atomicsDone + " of " + atomics.size() + ": " + a.getId(), ANSICode.FG_MAGENTA);
                Logger.println("Enclosing method: " + a.getBody().getMethod());
                Logger.println("==============================================================");
                locks.print();
                Logger.println("==============================================================");
                Logger.println("These locks will be taken:");
                Logger.println("==============================================================");
                locks.print(true);
            }
	    }
	    
	    outputLockTotals(atomics, atomicToLocks, lockCountsFile);
	    pathTimesFile.println("*," + AnalysisTimer.getTotalPathsAnalysis());
	    
	    if (AtomicTransformer.INSTRUMENT) {
		    for (AtomicSection a : atomics) {
		        LockSet locks = atomicToLocks.get(a);
		        if (locks.willBeAcquired()) {
                    LocksInstrumenter instrumenter = new LocksInstrumenter(a, locks, GLOBAL_LOCK, MANUAL_LOCKS);
                    instrumenter.instrument();
                    // IMPORTANT: invalidate enclosing method's cfg incase 
                    // it is called by some other atomic
                    CFGCache.invalidateCFG(a.getBody().getMethod());
		        }
            }
	    }
	    
	    pathTimesFile.flush();
	    lockCountsFile.flush();
	    lockTimesFile.flush();
	    methodListFile.flush();
	    
	    pathTimesFile.close();
	    lockCountsFile.close();
	    lockTimesFile.close();
	    methodListFile.close();
		    
		outputAnalysisTimes();
		
		Info.outputMemoryStatistics(null);
		POOL.shutdown();
		stopMemoryMonitor();
    }

    private void outputLockTotals(List<AtomicSection> atomics, Map<AtomicSection,LockSet> atomicToLocks, PrintStream lockResults) {
        
        long[] overallTotals = new long[4];
        long[] overallAcquiredTotals = new long[4];
        long[] threadLocalTotals = new long[4];
        long[] instanceLocalTotals = new long[4];
        long[] classLocalTotals = new long[4];
        long[] dominatedTotals = new long[4];
        long[] readOnlyTotals = new long[4];
        long[] implicitLockingTotals = new long[4];
        long[] methodLocalTotals = new long[4];
        
        for (AtomicSection a : atomics) {
            Set<Lock> locks = atomicToLocks.get(a);
            long[] overallA = new long[4];
            long[] overallAcquiredA = new long[4];
            long[] threadLocalA = new long[4];
            long[] instanceLocalA = new long[4];
            long[] classLocalA = new long[4];
            long[] dominatedA = new long[4];
            long[] readOnlyA = new long[4];
            long[] implicitLockingA = new long[4];
            long[] methodLocalA = new long[4];
            for (Lock l : locks) {
                int idx = -1;
                if (l instanceof PathLock) {
                    PathLock pl = (PathLock)l;
                    if (pl.isWrite()) {
                        idx=1;
                    } else {
                        idx=0;
                    }
                } else {
                    if (l.isWrite()) {
                        idx=3;
                    } else {
                        idx=2;
                    }
                }
                // update totals
                overallA[idx]++;
                overallTotals[idx]++;
                if (l.isThreadLocal()) {
                    threadLocalA[idx]++;
                    threadLocalTotals[idx]++;
                }
                if (l.isInstanceLocal()) {
                    instanceLocalA[idx]++;
                    instanceLocalTotals[idx]++;                        
                }
                if (l.isClassLocal()) {
                    classLocalA[idx]++;
                    classLocalTotals[idx]++;
                }
                if (l.isDominated()) {
                    dominatedA[idx]++;
                    dominatedTotals[idx]++;
                }
                if (l.isReadOnly()) {
                    readOnlyA[idx]++;
                    readOnlyTotals[idx]++;
                }
                if (l.isMethodLocal()) {
                    methodLocalA[idx]++;
                    methodLocalTotals[idx]++;   
                }
                if (l instanceof PathLock && !((PathLock)l).doMultiLocking()) {
                    implicitLockingA[idx]++;
                    implicitLockingTotals[idx]++;
                }
                if (l.willBeAcquired()) {
                    overallAcquiredA[idx]++;
                    overallAcquiredTotals[idx]++;
                }
            }
            
            String id = LIBRARY ? a.getBody().getMethod().toString() : ("" + a.getId());
            String atomicCounts = generateCountsString(id, overallA, overallAcquiredA, threadLocalA, instanceLocalA, classLocalA, dominatedA, readOnlyA, implicitLockingA, methodLocalA);
            lockResults.println(atomicCounts);
        }

        String totalCounts = generateCountsString("*", overallTotals, overallAcquiredTotals, threadLocalTotals, instanceLocalTotals, classLocalTotals, dominatedTotals, readOnlyTotals, implicitLockingTotals, methodLocalTotals);
        lockResults.println(totalCounts);

    }

    private String generateCountsString(String id, long[]... counts) {
        String format = "%s";
        Object[] values = new Object[1 + counts.length*4];
        values[0] = id;
        int idx=1;
        for (long[] count : counts) {
            format += ",%d,%d,%d,%d";
            for (int i=0; i<count.length; i++) {
                values[idx++] = count[i];
            }
        }
        
        return String.format(format, values);
    }

    private void performLockDominatorsAnalysis(Map<AtomicSection, LockSet> atomicToLocks) {
        long startTime = System.currentTimeMillis();
        LockDominatorsAnalysis lda = new LockDominatorsAnalysis(atomicToLocks);
        lda.calculateDominatorLocks();
        long took = System.currentTimeMillis()-startTime;
        AnalysisTimer.addForDominatorsAnalysis(took);
    }

    // Optimisation 1: remove implicit type locking
    private void performRemoveRedundantImplicitLockingOptimisation(Map<AtomicSection, LockSet> atomicToLocks) {
        
        long startTime = System.currentTimeMillis();
        
        // build up set of types that are acquired
        Set<Type> typesLocked = new HashSet<Type>();
        for (AtomicSection a : atomicToLocks.keySet()) {
            LockSet locks = atomicToLocks.get(a);
            for (Lock l : locks) {
                if (l instanceof TypeLock && l.willBeAcquired()) {
                    TypeLock tl = (TypeLock)l;
                    typesLocked.add(tl.getType());
                }
            }
        }
        
        // Go through each path lock and if all it's possible run-time types are never
        // acquired then mark them for no implicit locking.
        for (AtomicSection a : atomicToLocks.keySet()) {
            LockSet locks = atomicToLocks.get(a);
            for (Lock l : locks) {
                if (l instanceof PathLock && l.willBeAcquired()) {
                    PathLock pl = (PathLock)l;
                    boolean doMultiLocking = false;
                    if (pl.isStatic()) {
                        // special case for locks on Class objects because
                        // they don't have an allocation site
                        RefType classType = RefType.v("java.lang.Class");
                        doMultiLocking = typesLocked.contains(classType);
                    }
                    else {
                        BDDPointsToSet pts = (BDDPointsToSet)pl.getPointsToSet();
                        Set<Type> possibleRuntimeTypes = pts.possibleTypes();
                        for (Type t : possibleRuntimeTypes) {
                            if (typesLocked.contains(t)) {
                                doMultiLocking = true;
                                break;
                            }
                        }
                    }
                    pl.setDoMultiLocking(doMultiLocking);
                    if (!doMultiLocking) {
                        Logger.println("(" + a.getId() + ") " + pl + " does not need implicit locking", ANSICode.FG_GREEN);
                    }
                }
            }
        }
        
        long took = System.currentTimeMillis()-startTime;
        AnalysisTimer.addForImplicitLockingAnalysis(took);
    }
    
    private void performRemoveRedundantReadLocksOptimisations(Map<AtomicSection, LockSet> atomicToLocks) {
        long startTime = System.currentTimeMillis();
        
        // build up set of types that are acquired
        Set<Type> typeLockTypes = new HashSet<Type>();
        Set<PathLock> pathLocks = new HashSet<PathLock>(); 
        Set<TypeLock> typeLocks = new HashSet<TypeLock>(); 
        
        // Separate path and type locks
        for (LockSet locks : atomicToLocks.values()) {
            Pair<Set<Lock>,Set<Lock>> sepLocks = locks.separateLocks();
            Set<Lock> atomicTypeLocks = sepLocks.getFirst();
            for (Lock l : atomicTypeLocks) {
                if (l.willBeAcquired()) {
                    TypeLock tl = (TypeLock)l;
                    Type t = tl.getType();
                    typeLockTypes.add(t);
                    typeLocks.add(tl);
                }
            }
            Set<Lock> atomicPathLocks = sepLocks.getSecond();
            for (Lock l : atomicPathLocks) {
                if (l.willBeAcquired()) {
                    PathLock pl = (PathLock)l;
                    pathLocks.add(pl);
                }
            }
        }
            
        //
        // STEP 1
        // Cache points-to "abstract" objects that are write-locked
        //
        final Set<Node> writeSet = new HashSet<Node>();
        for (final PathLock pl : pathLocks) {
            BDDPointsToSet pts = (BDDPointsToSet)pl.getPointsToSet();
            if (pts == null) continue;
            pts.forall(new P2SetVisitor() {
                @Override
                public void visit(ContextAllocNode cn) {
                    Node n = cn.node();
                    // ptoToWrite(n) = ptoToWrite(n) |_| pl.isWrite()
                    if (pl.isWrite()) {
                        writeSet.add(n);
                    }
                }
            });
        }
        
        // 
        // STEP 2
        // Cache static locks that are write-locked
        //
        Set<SootClass> staticsWriteLocked = new HashSet<SootClass>();
        for (PathLock pl : pathLocks) {
            if (pl.isStatic() && pl.isWrite()) {
                StaticLookup sl = (StaticLookup)pl.getLookup();
                SootClass c = sl.getClazz();
                staticsWriteLocked.add(c);
            }
        }

        //
        // STEP 3
        // Cache types that are write-locked
        //
        Set<Type> typesWriteLocked = new HashSet<Type>();
        for (TypeLock tl : typeLocks) {
            Type t = tl.getType();
            if (tl.isWrite()) {
                typesWriteLocked.add(t);
            }
        }

        //
        // STEP 4
        // Find paths that are read-only. This means that they could not be
        // involved in a read-write or write-write conflict with other
        // lock acquisitions of the same object or with the object's type lock
        //
        Set<PathLock> killedPathLocks = new HashSet<PathLock>();
        for (final PathLock pl : pathLocks) {
            // If any of the objects that pl may point to is write locked
            // then pl may be involved in a read-write or write-write conflict
            if (pl.isStatic()) {
                // special case for locks on Class objects (because they have no
                // allocation site)
                StaticLookup sl = (StaticLookup)pl.getLookup();
                SootClass c = sl.getClazz();
                RefType classType = RefType.v("java.lang.Class");
                boolean readOnly = !pl.isWrite() && !staticsWriteLocked.contains(c) && !typesWriteLocked.contains(classType);
                if (readOnly) {
                    Logger.println(pl + " is read-only", ANSICode.FG_MAGENTA);
                    killedPathLocks.add(pl);
                }
                else {
                    Logger.println(pl + " IS NOT read-only (" + pl.isWrite() + "," + staticsWriteLocked.contains(c) + "," + typesWriteLocked.contains(classType) + ")", ANSICode.FG_RED);
                }
            }
            else {
                BDDPointsToSet pts = (BDDPointsToSet)pl.getPointsToSet();
                final boolean[] readOnly = new boolean[1];
                readOnly[0] = !pl.isWrite();
                if (readOnly[0]) {
                    pts.forall(new P2SetVisitor() {
                        @Override
                        public void visit(ContextAllocNode cn) {
                            Node n = cn.node();
                            if (writeSet.contains(n)) {
                                readOnly[0] = false;
                                // how could we break out of here?
                            }
                        }
                    });
                }
                // if still read-only then check types
                if (readOnly[0]) {
                    Set<Type> types = pts.possibleTypes();
                    for (Type t : types) {
                        if (typesWriteLocked.contains(t)) {
                            readOnly[0] = false;
                            break;
                        }
                    }
                }
                if (readOnly[0]) {
                    // pl is read-only
                    Logger.println(pl + " is read-only (pts: " + pts.size() + ")", ANSICode.FG_BLUE);
                    killedPathLocks.add(pl);
                }
                else {
                    Logger.println(pl + " IS NOT read-only (" + pl.isWrite() + "): " + pts, ANSICode.FG_RED);
                }
            }
        }
        
        //
        // STEP 5
        // Type locks can be removed if read-only and no instance is acquired 
        // in write mode
        //
        Set<TypeLock> killedTypeLocks = new HashSet<TypeLock>();
        for (TypeLock tl : typeLocks) {
            Type t = tl.getType();
            boolean readOnly = !typesWriteLocked.contains(t);
            if (readOnly) {
                // check paths that may have run-time type t
                for (Node n : writeSet) {
                    Type nt = n.getType();
                    if (t.equals(nt)) {
                        // t has a path that is write-locked
                        Logger.println(tl + " is NOT read-only because instance " + n + " is write-locked", ANSICode.FG_RED);
                        readOnly = false;
                        break;
                    }
                }
            }
            else {
                Logger.println(tl + " is NOT read-only because it is a write lock", ANSICode.FG_RED);
            }
            if (readOnly) {
                Logger.println(tl + " is read-only", ANSICode.FG_GREEN);
                killedTypeLocks.add(tl);
            }
        }
        
        //
        // STEP 6
        // Mark read-only locks so that we know that they are so in the
        // results.
        //
        for (AtomicSection a : atomicToLocks.keySet()) {
            Set<Lock> kill = new HashSet<Lock>();
            Set<Lock> gen = new HashSet<Lock>();
            LockSet locks = atomicToLocks.get(a);
            for (Lock l : locks) {
                if (killedPathLocks.contains(l)) {
                    PathLock pl = (PathLock)l;
                    PathLock pl2 = new PathLock(pl.getPrefix(), pl.getLookup(), pl.isWrite(), pl.isThreadLocal(), pl.isInstanceLocal(), pl.getPointsToSet(), pl.isDominated(), pl.isDuplicate(), pl.isClassLocal(), true, pl.doMultiLocking(), pl.isMethodLocal());
                    kill.add(pl);
                    gen.add(pl2);
                }
                else if (killedTypeLocks.contains(l)) {
                    TypeLock tl = (TypeLock)l;
                    TypeLock tl2 = new TypeLock(tl.getType(), tl.isWrite(), tl.isThreadLocal(), tl.isInstanceLocal(), tl.isDominated(), true);
                    kill.add(tl);
                    gen.add(tl2);
                }
            }
            locks.removeAll(kill);
            locks.addAll(gen);
            Logger.println("(" + a.getId() + ") Kill: " + kill);
            Logger.println("(" + a.getId() + ") Gen: " + gen);
            Logger.println("");
        }
        
        long took = System.currentTimeMillis() - startTime;
        AnalysisTimer.addForReadLocksAnalysis(took);
        
//        // path lock can be removed if read-only && run-time types are not
//        // acquired in write mode
//        for (AtomicSection a : atomicToLocks.keySet()) {
//            LockSet locks = atomicToLocks.get(a);
//            Pair<Set<Lock>,Set<Lock>> sepLocks = locks.separateLocks();
//            Set<Lock> atomicTypeLocks = sepLocks.getFirst();
//            Set<Lock> atomicPathLocks = sepLocks.getSecond();
//            Set<Lock> kill = new HashSet<Lock>();
//            
//            for (final Lock l : atomicPathLocks) {
//                PathLock pl = (PathLock)l;
//                PathLock prefix = pl.getPrefix();
//                PathLookup lookup = pl.getLookup();
//                boolean readOnly = true;  // note: if null, then will count as read-only and so will be optimised away
//                Set<Node> nodes = null;
//                if (prefix == null && lookup instanceof StaticLookup) { // special case for class instance lock (no aliasing so don't need points-to analysis)
//                     for (PathLock pl2 : pathLocks) {
//                         PathLock prefix2 = pl2.getPrefix();
//                         PathLookup lookup2 = pl2.getLookup();
//                         if (prefix2 == null && lookup2 instanceof StaticLookup) {
//                             if (lookup.equals(lookup2)) {
//                                 readOnly = readOnly && !pl2.isWrite();
//                             }
//                         }
//                     }
//                }
//                else {
//                    PointsToSetInternal pts = (PointsToSetInternal)pathLockToPointsToSet(pl);
//                    final Set<Node> nodes2 = new HashSet<Node>();
//                    if (pts == null) continue;
//                    pts.forall(new P2SetVisitor() {
//                        @Override
//                        public void visit(Node n) {
//                            nodes2.add(n);
//                        }
//                    });
//                    nodes = nodes2;
//                    // is path lock read-only?
//                    for (Node n : nodes) {
//                        Boolean write = ptoToWrite.get(n);
//                        boolean oldReadOnly = readOnly;
//                        readOnly = readOnly && !write.booleanValue();
//                        if (oldReadOnly && !readOnly) {
//                            Logger.println(pl + " is not read-only because of " + n);
//                        }
//                    }
//                }
//                // check if pl's run-time types are not acquired in write mode
//                // This covers both cases above
//                Set<Type> types = pathLockToRuntimeTypes(pl);
//                for (Type t : types) {
////                    if (!t.toString().equals("java.lang.String")) { // special case
//                        for (TypeLock tl : typeLocks) {
//                            if (tl.getType().equals(t)) {
//                                boolean oldReadOnly = readOnly;
//                                readOnly = readOnly && !tl.isWrite();
//                                if (oldReadOnly && !readOnly) {
//                                    Logger.println(pl + " is not read-only because of " + t);
//                                }
//                            }
//                        }
////                    }
//                }
//                
//                if (readOnly) {
//                    if (DEBUG) {
//                        Logger.println("path lock " + pl + " is read-only", ANSICode.FG_BLUE);
//                        if (nodes != null) {
//                            for (Node n : nodes) {
//                                Logger.println("\tn: " + n + ", write? " + ptoToWrite.get(n));
//                            }
//                        }
//                    }
//                    counter++;
//                    kill.add(pl);
//                }
//            }
//        
//            // type locks can be removed if read-only and no instance is acquired 
//            // in write mode
//            for (Lock l : atomicTypeLocks) {
//                TypeLock tl = (TypeLock)l;
//                Type t = tl.getType();
//                boolean readOnly = !tl.isWrite(); // covers the case when no instances are locked
////                if (t.toString().equals("java.lang.String")) { // special case
////                    readOnly = true;
////                }
////                else {
//                    for (Node n : ptoToWrite.keySet()) {
//                        Set<Type> runtimeTypes = n.getP2Set().possibleTypes();
//                        if (runtimeTypes.contains(t)) {
//                            readOnly = readOnly && !ptoToWrite.get(n).booleanValue();
//                        }
//                    }
////                }
//                if (readOnly) {
//                    if (DEBUG) Logger.println("type lock " + tl + " is read-only", ANSICode.FG_BLUE);
//                    counter++;
//                    kill.add(tl);
//                }
//            }
//            
//            if (DEBUG) Logger.println("kill: " + kill);
//            atomicToKills.put(a, kill);
//        }
//        Logger.println(counter + " read locks removed");
    }

    private Set<Type> pathLockToRuntimeTypes(PathLock pl) {
        PointsToSet pts = pl.getPointsToSet();
        Set<Type> types = pts == null ? new HashSet<Type>() : new HashSet<Type>(pts.possibleTypes()); 

        // if pl starts with a static lookup, add java.lang.Class to types
        PathLock prefix = pl;
        while (prefix.getPrefix() != null) {
            prefix = prefix.getPrefix();
        }
        if (prefix.getLookup() instanceof StaticLookup) {
            types.add(RefType.v("java.lang.Class"));
        }
        return types;
    }

//    private PointsToSet pathLockToPointsToSet(PathLock pl) {
//        
//        PointsToSet pts = null;
//
//        PathLock prefix = pl.getPrefix();
//        if (prefix != null) {
//            pts = pathLockToPointsToSet(prefix);
//        }
//        
//        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
//        
//        PathLookup lookup = pl.getLookup();
//        if (lookup instanceof LocalLookup) {
//            LocalLookup ll = (LocalLookup)lookup;
//            Local l = ll.getLocal();
//            pts = pta.reachingObjects(l);
//        }
//        else if (lookup instanceof FieldLookup) {
//            FieldLookup fl = (FieldLookup)lookup;
//            SootField f = fl.getField();
//            try {
//                pts = (pts == null) ? pta.reachingObjects(f) : pta.reachingObjects(pts, f);
//            }
//            catch (Exception e) {
//                Logger.println("Offending path lock: " + pl, ANSICode.FG_RED);
//                e.printStackTrace();
//                
//            }
//        }
//        else if (lookup instanceof ArrayLookup) {
//            pts = pta.reachingObjectsOfArrayElement(pts);
//        }
//        
//        return pts;
//        
//    }

    MemoryMonitor m;
    
    private void startMemoryMonitor() {
        m = new MemoryMonitor(MEM_INFO);
        new Thread(m).start();
    }
    
    private void stopMemoryMonitor() {
        m.stop();
    }

    Set<SootMethod> libMethods = new HashSet<SootMethod>();
    Set<SootMethod> clientMethods = new HashSet<SootMethod>();
    Set<Component> clientOnlyComponents = new HashSet<Component>();
    Set<Component> libOnlyComponents = new HashSet<Component>();
    Set<Component> mixedComponents = new HashSet<Component>();

    private void outputClientLibStats(List<AtomicSection> atomics) {
        try {
            PrintWriter printer = new PrintWriter("libclient.txt");
            printer.println("per-atomic stats");
            printer.println("atomic id,enclosing method,total methods,lib methods,client methods,lib-only componenets,client-only components,mixed components");
            for (AtomicSection a : atomics) {
                Set<Component> components = new HashSet<Component>();
                for (SootMethod m : a.getCalledMethods()) {
                    StronglyConnectedComponents scc = new StronglyConnectedComponents(
                            m);
                    components.addAll(scc.getComponents());
                }
                checkLibClient(a, components, printer);
            }
    
            printer.println("");
            printer.println("global stats:");
            printer.println("total method count:" + (libMethods.size()+clientMethods.size()));
            printer.println("lib methods:" + libMethods.size());
            printer.println("client methods:" + clientMethods.size());
            printer.println("lib-only components:" + libOnlyComponents.size());
            printer.println("client-only components:" + clientOnlyComponents.size());
            printer.println("mixed components:" + mixedComponents.size());
            
            printer.println("");
            printer.println("Library methods:");
            printer.println("");
            for (SootMethod m : libMethods) {
                printer.println(m.toString());
            }
            
            printer.println("");
            printer.println("Client methods:");
            printer.println("");
            for (SootMethod m : clientMethods) {
                printer.println(m.toString());
            }
            
            printer.flush();
            printer.close();
        }
        catch (FileNotFoundException fnfe) {
            throw new RuntimeException(fnfe);
        }
    }

    private void outputAnalysisTimes() {
        long[] times = new long[] { 
                AnalysisTimer.getLibIntra(),
                AnalysisTimer.getClientIntra(), 
                AnalysisTimer.getLibInter(),
                AnalysisTimer.getClientInter(),
                AnalysisTimer.getLibReduction(),
                AnalysisTimer.getClientReduction(),
                AnalysisTimer.getLibAtomic(), 
                AnalysisTimer.getClientAtomic(), 
                AnalysisTimer.getTotalPathsAnalysis(),
                AnalysisTimer.getLibLocks(), 
                AnalysisTimer.getClientLocks(), 
                AnalysisTimer.getTotalLocksAnalysis(),
                AnalysisTimer.getTotalThreadLocalAnalysis(),
                AnalysisTimer.getTotalInstanceLocalAnalysis(),
                AnalysisTimer.getTotalClassLocalAnalysis(),
                AnalysisTimer.getTotalDominatorsAnalysis(),
                AnalysisTimer.getTotalReadLocksAnalysis(),
                AnalysisTimer.getTotalImplicitLockingAnalysis(),
                AnalysisTimer.getTotalMethodLocalAnalysis()
        };
        try {
            PrintWriter p = new PrintWriter("times.txt");
            String s = "";
            boolean first = true;
            for (long ms : times) {
                // turn into seconds (round up to nearest)
                double seconds = (ms / 1000.0);// + ((ms % 1000 == 0) ? 0 : 1);
                if (!first) {
                    s += ",";
                }
                s += seconds;
                first = false;
            }
            p.println("lib intra,client intra,lib inter,client inter,lib reduction,client reduction,lib atomic,client atomic,total analysis,lib locks,client locks,total locks,thread local,instance local,class local,dominated,read only,implicit locking,method local");
            p.println(s);
            p.flush();
            p.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void checkLibClient(AtomicSection a, Set<Component> components, PrintWriter printer) {
        int libMethods = 0;
        int clientMethods = 0;
        int onlyClientComponents = 0;
        int onlyLibComponents = 0;
        int mixedComponents = 0;
        for (Component c : components) {
            boolean clientMethodFound = false;
            boolean libMethodFound = false;
            for (SootMethod m : c) {
                if (isLibrary(m)) {
                    libMethods++;
                    libMethodFound = true;
                    this.libMethods.add(m);
                } else {
                    clientMethods++;
                    clientMethodFound = true;
                    this.clientMethods.add(m);
                }
            }
            if (clientMethodFound) {
                if (libMethodFound) {
                    mixedComponents++;
                    this.mixedComponents.add(c);
                } else {
                    onlyClientComponents++;
                    clientOnlyComponents.add(c);
                }
            } else {
                onlyLibComponents++;
                libOnlyComponents.add(c);
            }
        }
        printer.println(String.format("%d,%s,%d,%d,%d,%d,%d,%d", a.getId(), a.getEnclosingUnitGraph().getBody().getMethod().toString(),
                libMethods+clientMethods,libMethods, clientMethods, onlyLibComponents,
                onlyClientComponents, mixedComponents));
    }

    private boolean isLibrary(SootMethod m) {
        return m.getDeclaringClass().isLibraryClass();
//        String clazzPackage = m.getDeclaringClass().getJavaPackageName();
//        return !(clazzPackage.startsWith("org.hsqldb") || clazzPackage
//                .startsWith("dacapo"));
    }

    private void convertAccessNFAsToLocks() {
        PrintStream results;
        try {
            results = new PrintStream("locks.csv");
        } catch (FileNotFoundException fnfe) {
            throw new RuntimeException(fnfe);
        }

        FileInputStream fis = null;
        ObjectInputStream in = null;

        try {
            fis = new FileInputStream("nfas.lg");
            in = new ObjectInputStream(fis);

            int methodCount = in.readInt();

            Date startTime = new Date();
            for (int i = 1; i <= methodCount; i++) {
                Date currStartTime = new Date();
                SootMethod m = (SootMethod) in.readObject();
                Automaton nfa = (Automaton) in.readObject();

                Logger.println("Converting locks for method " + i + " of "
                        + methodCount);
                Logger.println("Method: " + m);

                AutomatonToLocks converter = new AutomatonToLocks(nfa, null, null, null);
                LockSet locks = (LockSet) converter.getLocks();

                int ri = 0, wi = 0, rt = 0, wt = 0;
                for (Lock l : locks) {
                    if (l instanceof PathLock) {
                        if (l.isWrite()) {
                            wi++;
                        } else {
                            ri++;
                        }
                    } else {
                        if (l.isWrite()) {
                            wt++;
                        } else {
                            rt++;
                        }
                    }
                }

                Date time = new Date(System.currentTimeMillis()
                        - startTime.getTime());
                Date took = new Date(System.currentTimeMillis()
                        - currStartTime.getTime());
                Logger.println("Took: "
                        + String.format("%2d:%2d:%2d", took.getHours() - 1,
                                took.getMinutes(), took.getSeconds()));
                Logger.println("Time: "
                        + String.format("%2d:%2d:%2d", time.getHours() - 1,
                                time.getMinutes(), time.getSeconds()));

                double tookSeconds = took.getTime() / 1000.0;
                SootClass c = m.getDeclaringClass();
                results.println(c.getName() + "," + m.getName() + "," + ri
                        + "," + wi + "," + rt + "," + wt + "," + tookSeconds);

                Logger.println("\n");
            }

            in.close();

            double timeSecs = (System.currentTimeMillis() - startTime.getTime()) / 1000.0;
            Logger.println("Analysis took " + timeSecs + "secs");
            results.println(timeSecs);

            Info.outputMemoryStatistics(results);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }

        results.flush();
        results.close();
    }

    private void inferPaths(int methodStart) {
        PrintStream results;
        try {
            results = new PrintStream("paths.csv");
        } catch (FileNotFoundException fnfe) {
            throw new RuntimeException(fnfe);
        }

        Date startTime = new Date();
        int methodsDone = 0;
        long methodCount = Info.countNonPrivateMethods();
        for (SootClass c : Scene.v().getClasses()) {
            Logger.println("\n");
            Logger.println("Class: " + c, ANSICode.FG_BLUE);
            String pkg = c.getJavaPackageName().split("\\.")[0];
            for (SootMethod m : c.getMethods()) {
                if (m.isConcrete() && !m.isPrivate()) {
                    methodsDone++;
                    if (methodsDone < methodStart) {
                        continue;
                    }
                    Logger.println("\n");
                    Logger.println("Method " + methodsDone + " of "
                            + methodCount + ": " + m, ANSICode.FG_MAGENTA);
                    Date currStartTime = new Date();
                    StronglyConnectedComponents scc = new StronglyConnectedComponents(
                            m);
                    Set<Component> cs = new HashSet<Component>(scc
                            .getComponents());
                    StronglyConnectedComponentsDAG sccDag = new StronglyConnectedComponentsDAG(
                            cs);
                    PathsAnalysis p = new PathsAnalysis(null, cs, sccDag);
                    p.doAnalysis();
                    Date took = new Date(System.currentTimeMillis()
                            - currStartTime.getTime());
                    Date time = new Date(System.currentTimeMillis()
                            - startTime.getTime());
                    double tookSeconds = took.getTime() / 1000.0;
                    results.println(pkg + "," + c.getName() + "," + m.getName()
                            + "," + tookSeconds);
                    Logger.println("Took: "
                            + String.format("%2d:%2d:%2d", took.getHours() - 1,
                                    took.getMinutes(), took.getSeconds()));
                    Logger.println("Time: "
                            + String.format("%2d:%2d:%2d", time.getHours() - 1,
                                    time.getMinutes(), time.getSeconds()));
                    Logger.println("\n");
                }
            }
        }

        Logger.println("");
        double timeTaken = (System.currentTimeMillis() - startTime.getTime()) / 1000.0;
        Logger.println("Analysis took " + timeTaken + "secs");
        results.println(timeTaken);
        Info.outputMemoryStatistics(results);

        results.flush();
        results.close();
    }

    //
    //
    private void writeAccessNFAsToDisk(Map<AtomicSection,Automaton> atomicToNfas) {

        Logger.println("Writing access NFAs to disk");

        FileOutputStream fos = null;
        ObjectOutputStream out = null;

        try {
            fos = new FileOutputStream("nfas.lg");
            out = new ObjectOutputStream(fos);

            out.writeObject(atomicToNfas);    
            
            // serialize relevant points-to type information
            Map<Stmt,Set<Type>> stmtToTypes = new HashMap<Stmt, Set<Type>>();
            for (SootMethod m : PathsAnalysis.getMethods()) {
                ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
                for (Unit u : cfg) {
                    Stmt s = (Stmt)u;
                    Local l = null;
                    if (s.containsArrayRef()) {
                        ArrayRef ar = s.getArrayRef();
                        l = (Local)ar.getBase();
                    }
                    else if (s.containsFieldRef()) {
                        FieldRef fr = s.getFieldRef();
                        if (fr instanceof InstanceFieldRef) {
                            InstanceFieldRef ifr = (InstanceFieldRef)fr;
                            l = (Local)ifr.getBase();
                        }
                    }
                    
                    if (l != null) {
                        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
                        PointsToSet pts = pta.reachingObjects(l);
                        Set<Type> types = pts.possibleTypes();
                        stmtToTypes.put(s, types);
                    }
                }
            }
            out.writeObject(stmtToTypes);

            // serialise StateFactory's numToState mapping
            out.writeObject(StateFactory.getNumToStateMap());
            
            // serialise State's counter field
            out.writeInt(State.getCounterValue());
            
            // serialise start state
            out.writeObject(StartState.v());

            out.close();
        } catch (IOException ioe) {
            throw new RuntimeException(ioe);
        }
    }

    private void printInfo() {
        Logger.println("Number of fields: " + Info.countFields());
        Logger.println("Number of fields in field numberer object: "
                + Scene.v().getFieldNumberer().size());
        Logger.println("Number of classes: " + Info.countClasses());
        Logger.println("Number of classes2: " + Info.countClasses2());
        Logger.println("Number of methods: " + Info.countMethods());
        Logger.println("Number of non-private methods: " + Info.countNonPrivateMethods());
        Logger.println("Number of locals in local numberer object: "
                + Scene.v().getLocalNumberer().size());
        Logger
                .println("Number of stmts: "
                        + Scene.v().getUnitNumberer().size());
    }

    private void outputCgDot() {
        CallGraph cg = Scene.v().getCallGraph();

        SootMethod main = Scene.v().getMainMethod();
        TransitiveTargets targets = new TransitiveTargets(Scene.v()
                .getCallGraph(), new Filter(new ExplicitEdgesPred()));
        Set<SootMethod> reachables = new HashSet<SootMethod>();

        for (Iterator<MethodOrMethodContext> reachableMethodsIt = targets
                .iterator(main); reachableMethodsIt.hasNext();) {
            reachables.add(reachableMethodsIt.next().method());
        }

        reachables.add(main);

        Logger.println("Reachable methods: " + reachables.size());

        try {
            PrintWriter p = new PrintWriter("cg.dot");
            p.println("digraph G {");
            p.println("\tconcentrate=\"true\";");
            for (SootMethod m : reachables) {
                p.println("\tm" + m.getNumber() + " [label=\"" + m.getName()
                        + "\",style=filled,color=\"red\"];");
            }
            Iterator<Edge> edgesIt = cg.listener();
            while (edgesIt.hasNext()) {
                Edge e = edgesIt.next();
                if (e.isExplicit()) {
                    SootMethod src = e.src();
                    SootMethod tgt = e.tgt();
                    if (reachables.contains(src) && tgt.isConcrete()) {
                        p.println("\tm" + src.getNumber() + " -> m"
                                + tgt.getNumber() + ";");
                    }
                }
            }

            p.println("}");
            p.flush();
            p.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

//    private void convertSummariesToLocks() {
//        PrintStream results;
//        try {
//            results = new PrintStream("locks.csv");
//        } catch (FileNotFoundException fnfe) {
//            throw new RuntimeException(fnfe);
//        }
//
//        Logger.println("Converting summaries to locks");
//        Date startTime = new Date();
//        Set<SootMethod> methods = PathsAnalysis.getMethods();
//        int count = 0;
//        for (SootMethod m : methods) {
//            Logger.println("\n");
//            Logger.println("Converting locks for method " + (count++) + " of "
//                    + methods.size());
//            Logger.println("Method: " + m);
//            Date currStartTime = new Date();
//            Transformer summary = PathsAnalysis.getSummary(m);
//            Automaton nfa = summary.getAccessesNfa();
//            AutomatonToLocks converter = new AutomatonToLocks(nfa);
//            Set<Lock> locks = converter.getLocks();
//            int ri = 0, wi = 0, rt = 0, wt = 0;
//
//            for (Lock l : locks) {
//                if (l instanceof PathLock) {
//                    if (l.isWrite()) {
//                        wi++;
//                    } else {
//                        ri++;
//                    }
//                } else {
//                    if (l.isWrite()) {
//                        wt++;
//                    } else {
//                        rt++;
//                    }
//                }
//            }
//
//            SootClass c = m.getDeclaringClass();
//            String pkg = c.getJavaPackageName().split("\\.")[0];
//            Date time = new Date(System.currentTimeMillis()
//                    - startTime.getTime());
//            Date took = new Date(System.currentTimeMillis()
//                    - currStartTime.getTime());
//            double tookSeconds = took.getTime() / 1000.0;
//            Logger.println("Took: "
//                    + String.format("%2d:%2d:%2d", took.getHours() - 1, took
//                            .getMinutes(), took.getSeconds()));
//            Logger.println("Time: "
//                    + String.format("%2d:%2d:%2d", time.getHours() - 1, time
//                            .getMinutes(), time.getSeconds()));
//            results.println(pkg + "," + c.getName() + "," + m.getName() + ","
//                    + ri + "," + wi + "," + rt + "," + wt + "," + tookSeconds);
//        }
//        double timeSecs = (System.currentTimeMillis() - startTime.getTime()) / 1000.0;
//        Logger.println("\n");
//        Logger.println("Analysis took " + timeSecs + "secs");
//        results.println(timeSecs);
//        Info.outputMemoryStatistics(results);
//
//        results.flush();
//        results.close();
//    }

    private void writeSummariesToDisk() {
        PrintStream results;
        try {
            results = new PrintStream(SAVE_SUMMARIES_TO_FILE + ".csv");
        } catch (FileNotFoundException fnfe) {
            throw new RuntimeException(fnfe);
        }

        Date startTime = new Date();
        Set<SootMethod> methods = PathsAnalysis.getMethods();
        int count = 0;

        // write summary to one file so that common objects don't get serialised
        // multiple times
        FileOutputStream fos = null;
        ObjectOutputStream out = null;
        try {
            fos = new FileOutputStream(SAVE_SUMMARIES_TO_FILE);
            out = new ObjectOutputStream(fos);
            out.writeInt(methods.size());
            for (SootMethod m : methods) {
                Logger.println("Writing summary " + (++count) + " of "
                        + methods.size());
                Logger.println("   Method: " + m);
                Date currStartTime = new Date();
                ITransformer t = PathsAnalysis.getSummary(m);
                out.writeObject(m);
                out.writeObject(t);
                Date time = new Date(System.currentTimeMillis()
                        - startTime.getTime());
                Date took = new Date(System.currentTimeMillis()
                        - currStartTime.getTime());
                double tookSeconds = took.getTime() / 1000.0;
//                Logger.println("   Took: "
//                        + String.format("%2d:%2d:%2d", took.getHours() - 1,
//                                took.getMinutes(), took.getSeconds()));
//                Logger.println("   Time: "
//                        + String.format("%2d:%2d:%2d", time.getHours() - 1,
//                                time.getMinutes(), time.getSeconds()));
                SootClass c = m.getDeclaringClass();
                results.println(c.getName() + "," + m.getName() + ","
                        + tookSeconds);
            }
            
            // serialize relevant points-to type information
            Map<Stmt,Set<Type>> stmtToTypes = new HashMap<Stmt, Set<Type>>();
            for (SootMethod m : methods) {
                ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
                for (Unit u : cfg) {
                    Stmt s = (Stmt)u;
                    Local l = null;
                    if (s.containsArrayRef()) {
                        ArrayRef ar = s.getArrayRef();
                        l = (Local)ar.getBase();
                    }
                    else if (s.containsFieldRef()) {
                        FieldRef fr = s.getFieldRef();
                        if (fr instanceof InstanceFieldRef) {
                            InstanceFieldRef ifr = (InstanceFieldRef)fr;
                            l = (Local)ifr.getBase();
                        }
                    }
                    
                    if (l != null) {
                        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
                        PointsToSet pts = pta.reachingObjects(l);
                        Set<Type> types = pts.possibleTypes();
                        stmtToTypes.put(s, types);
                    }
                }
            }
            out.writeObject(stmtToTypes);

            // serialise StateFactory's numToState mapping
            out.writeObject(StateFactory.getNumToStateMap());
            
            // serialise State's counter field
            out.writeInt(State.getCounterValue());
            
            // serialise start state
            out.writeObject(StartState.v());
            
            out.close();
        } catch (IOException ioe) {
            throw new RuntimeException(ioe);
        }

        double timeSecs = (System.currentTimeMillis() - startTime.getTime()) / 1000.0;
        Logger.println("Writing summaries took " + timeSecs + "secs");
        results.println(timeSecs);

        Info.outputMemoryStatistics(results);

        results.flush();
        results.close();
    }
    
    public static void main(String[] args) {
    }

}

class MyThreadPoolExecutor extends ThreadPoolExecutor {

    public MyThreadPoolExecutor(int corePoolSize, int maximumPoolSize,
            long keepAliveTime, TimeUnit unit, BlockingQueue<Runnable> workQueue) {
        super(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue);
    }

    @Override
    protected void afterExecute(Runnable r, Throwable t) {
        super.afterExecute(r, t);
        if (r instanceof FutureTask) {
            FutureTask ft = (FutureTask) r;
            try {
                ft.get();
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }

}
