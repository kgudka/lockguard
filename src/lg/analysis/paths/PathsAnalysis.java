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

package lg.analysis.paths;

import static lg.analysis.paths.transformer.TransformerFactory.*;
import gnu.trove.map.hash.TIntIntHashMap;

import java.util.*;
import java.util.concurrent.Callable;
import java.util.concurrent.atomic.AtomicInteger;

import lg.analysis.locks.AutomatonToLocks;
import lg.analysis.paths.automata.Automaton;
import lg.analysis.paths.transformer.*;
import lg.analysis.paths.transformer.fast.*;
import lg.analysis.paths.transformer.fast.Transformer;
import lg.analysis.paths.transformer.state.*;
import lg.cfg.*;
import lg.cg.NonColdEdgesPred;
import lg.dot.CFGToDotGraphWithLabels;
import lg.transformer.AtomicTransformer;
import lg.util.*;
import lg.util.Timer;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.*;
import soot.toolkits.graph.*;
import soot.util.cfgcmd.CFGToDotGraph;
import soot.util.dot.DotGraph;

public class PathsAnalysis {
    
	Map<Unit,ITransformer> unitToTransformer;
	Map<Unit,ITransformer> unitToTransformerDelta;
	Map<Unit,ITransformer> unitToEntry;
//	Map<Unit,Transformer> unitToEntryDelta;
	Map<Unit,ITransformer> unitToExit;
	Map<Unit,ITransformer> unitToExitDelta;
	Map<Unit,List<Unit>> unitToPreds;
	Map<Unit,List<Unit>> unitToSuccs;
	
	Map<Unit,List<Unit>> unitToJumpPreds;
	Map<Unit,Map<Unit,ITransformer>> unitToJumpSuccs;
	
	Map<Unit,TIntIntHashMap> callToParamsArgs;
	Map<Unit,List<SootMethod>> callerToCallees;
	Map<SootMethod,List<Unit>> calleeToCallers;
	Map<SootMethod,Unit> methodToStartUnit;
	Map<SootMethod,Unit> methodToEndUnit;
	Map<Unit,SootMethod> startUnitToMethod;
	Map<Unit,SootMethod> unitToMethod;
	
	Map<Unit,Integer> numbers;

	static Map<SootMethod,ITransformer> methodToSummary = Collections.synchronizedMap(new HashMap<SootMethod, ITransformer>());

	AtomicSection a;
	Set<Component> components;
	StronglyConnectedComponentsDAG dag;
	
	ITransformer identityTransformer;
	ITransformer initialDeltaTransformer;
	ITransformer atomicSummary;
	
	final boolean debug;
	final boolean reduceCfg;
	final boolean showSummary;
	final boolean outputDot;
	final boolean exceptions;
	final boolean useDeltas;

	CFGToDotGraph cfgToDotter;
	CallGraph cg;
	NonColdEdgesPred edgesPred;
	
	List<Unit> unitsToCompactInComponent;
	
	boolean storeEntry;
	
	//Map<Unit,Set<Unit>> unitToReachables;
	
	public PathsAnalysis(AtomicSection as, Set<Component> cs, StronglyConnectedComponentsDAG componentsDag) {
	    
        debug = AtomicTransformer.DEBUG;
        reduceCfg = AtomicTransformer.REDUCE_CFG;
        showSummary = AtomicTransformer.SHOW_SUMMARY;
        outputDot = AtomicTransformer.OUTPUT_DOT;
        exceptions = AtomicTransformer.EXCEPTIONS;
        storeEntry = AtomicTransformer.STORE_ENTRY;
        useDeltas = AtomicTransformer.DELTAS;	    
	    
		unitToTransformer = Collections.synchronizedMap(new HashMap<Unit, ITransformer>());
		unitToTransformerDelta = useDeltas ? Collections.synchronizedMap(new HashMap<Unit, ITransformer>()) : null;
		unitToEntry = Collections.synchronizedMap(new HashMap<Unit, ITransformer>());
//		unitToEntryDelta = Collections.synchronizedMap(new HashMap<Unit, Transformer>());
		unitToExit = Collections.synchronizedMap(new HashMap<Unit, ITransformer>());
		unitToExitDelta = useDeltas ? Collections.synchronizedMap(new HashMap<Unit, ITransformer>()) : null;
		unitToPreds = Collections.synchronizedMap(new HashMap<Unit, List<Unit>>());
		unitToSuccs = Collections.synchronizedMap(new HashMap<Unit, List<Unit>>());
		unitToJumpPreds = Collections.synchronizedMap(new HashMap<Unit, List<Unit>>());
		unitToJumpSuccs = Collections.synchronizedMap(new HashMap<Unit, Map<Unit,ITransformer>>());
		methodToStartUnit = Collections.synchronizedMap(new HashMap<SootMethod, Unit>());
		methodToEndUnit = Collections.synchronizedMap(new HashMap<SootMethod, Unit>());
		startUnitToMethod = Collections.synchronizedMap(new HashMap<Unit,SootMethod>());
		unitToMethod = Collections.synchronizedMap(new HashMap<Unit, SootMethod>());
		numbers = Collections.synchronizedMap(new HashMap<Unit, Integer>());
		callerToCallees = Collections.synchronizedMap(new HashMap<Unit, List<SootMethod>>());
		calleeToCallers = Collections.synchronizedMap(new HashMap<SootMethod, List<Unit>>());
		callToParamsArgs = Collections.synchronizedMap(new HashMap<Unit, TIntIntHashMap>());
		a = as;
		components = cs;
		numComponents = 0;
		for (Component c : components) {
		    if (!hasAlreadyBeenAnalysed(c)) {
		        numComponents++;
		    }
		}
		
		dag = componentsDag;
		identityTransformer = TransformerFactory.newIdentityTransformer();
		initialDeltaTransformer = InitialDeltaTransformer.v();
		
		
		cfgToDotter = new CFGToDotGraphWithLabels();
		cg = Scene.v().getCallGraph();
		edgesPred = new NonColdEdgesPred();
		
		unitsToCompactInComponent = Collections.synchronizedList(new ArrayList<Unit>());
	}
	
	
	/* 
	  1. compute strongly connected components (SCC) of the call graph
	  2. create a DAG of the components

	  3. perform bottom-up interprocedural analysis of SCC-DAG (post order traversal)

	     For each component, put end nodes of all/one of the methods onto the worklist
	     To process a node n from the worklist, 
	     (a) take the meet of all transformers of successors to give t1
	     (b) compose t1 with the node's transformer tn to give tn o t1
	     (c) if this transformer is different to what was previously in n's entry,
	         add all predecessors to the work list.  
	 */
	
	public void init(final Component c) {	
		
	    long startTime = System.currentTimeMillis();
	    
		for (SootMethod m : c) {
			methodToSummary.put(m, identityTransformer);
		}

        final AtomicInteger invokeCount = new AtomicInteger(0);
        final AtomicInteger allInLowerComponentsCount = new AtomicInteger(0);

        List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
		// populate maps
		for (final SootMethod m : c) {
		    tasks.add(new Callable<Object>() {
		        public Object call() {
        			// Cache preds and succs so we can insert start and end nodes.
        			// We have to code it up the following way, in case we have a static 
        			// method that begins with a while loop (thus it will multiple entry
        		    // nodes). 
        			ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
//        			Logger.println("m: " + m, ANSICode.FG_BLUE);
        			for (Unit u : cfg) {
        				unitToPreds.put(u, new ArrayList<Unit>(exceptions ? cfg.getPredsOf(u) : cfg.getUnexceptionalPredsOf(u)));
        				unitToSuccs.put(u, new ArrayList<Unit>(exceptions ? cfg.getSuccsOf(u) : cfg.getUnexceptionalSuccsOf(u)));
        				unitToTransformer.put(u, createTransformer(u, m));
        //				unitToExitDelta.put(u, initialDeltaTransformer);
        				unitToMethod.put(u, m);
        				u.addTag(new ContainingMethodTag(m));
        			}
        
        			// insert single start node
        			Stmt start = new StartStmt();
        			startUnitToMethod.put(start, m);
        			unitToTransformer.put(start, createTransformer(start, m));
        			for (Unit h : cfg.getHeads()) {
        				List<Unit> preds = unitToPreds.get(h);
        				preds.add(start);
        			}
        			unitToPreds.put(start, new ArrayList<Unit>());
        			unitToSuccs.put(start, cfg.getHeads());
        			unitToEntry.put(start, identityTransformer);
        //			unitToExitDelta.put(start, initialDeltaTransformer);
        			unitToMethod.put(start, m);
        			methodToStartUnit.put(m, start);
        			
        			// insert single end node
        			Stmt end = new EndStmt();
        			for (Unit t : cfg.getTails()) {
        				List<Unit> succs = unitToSuccs.get(t);
        				succs.add(end);
        			}
        			List<Unit> tails = cfg.getTails();
        			unitToPreds.put(end, tails);
        			unitToSuccs.put(end, new ArrayList<Unit>());
        			methodToEndUnit.put(m, end);
        			unitToTransformer.put(end, createTransformer(end, m));
        //			unitToExitDelta.put(end, initialDeltaTransformer);
        			unitToMethod.put(end, m);
        			
        			// calculate pseudo topological ordering
                    List<Unit> orderedUnits = new PseudoTopologicalOrderer().newList(cfg, true);
                    numbers.put(end, 1);
                    int i = 2;
                    for (Unit u : orderedUnits) {
                        numbers.put(u, new Integer(i));
                        i++;
                    }
                    numbers.put(start, i);
        
                    // record caller to callees, create invoke stmt transformers
                    for (Unit u : cfg) {
                        Stmt s = (Stmt)u;
                        if (s.containsInvokeExpr()) {
                            List<SootMethod> targets = new ArrayList<SootMethod>();
                            for (Iterator<Edge> edgesIt=cg.edgesOutOf(u); edgesIt.hasNext(); ) {
                                Edge e = edgesIt.next();
                                if (edgesPred.want(e)) {
                                    SootMethod tgt = e.tgt();
                                    if (tgt.isConcrete()) {
                                        targets.add(tgt);
                                        if (c.contains(tgt)) { // we don't want callees from other components
                                            List<Unit> callers = calleeToCallers.get(tgt);
                                            if (callers == null) {
                                                callers = Collections.synchronizedList(new ArrayList<Unit>());
                                                calleeToCallers.put(tgt, callers);
                                            }
                                            callers.add(u);
                                        }
                                    }
                                }
                            }
//                            if (u.toString().contains("next") || u.toString().contains("get")) {
//                                Logger.println("u: " + u, ANSICode.FG_BLUE);
//                                Logger.println("targets: " + targets, ANSICode.FG_BLUE);
//                            }
                            callerToCallees.put(s, targets);
                            
                            boolean allInLowerComponents = true;
                            for (SootMethod t : targets) {
                                if (c.contains(t)) {
                                    allInLowerComponents = false;
                                }
                            }
                            if (allInLowerComponents) {
                                allInLowerComponentsCount.incrementAndGet();
                            }
                            invokeCount.incrementAndGet();
                            
                            callToParamsArgs.put(s, createParamsToArgsMapping(s));
                            unitToTransformer.put(s, createInvokeTransformer(s));
                        }
                    }
        			
        			if (reduceCfg) {
        			    if (useDeltas && AtomicTransformer.REDUCE_CFG_DELTA) {
        			        createIntraJumpsDeltas(m, cfg, c);
        			    }
        			    else {
        			        createIntraJumps(m, cfg, c);
        			    }
//        			    for (Unit u : unitToJumpSuccs2.keySet()) {
//        			        if (unitToMethod.get(u) == m) {
//        			            Map<Unit,Transformer> jump1 = unitToJumpSuccs.get(u);
//        			            Map<Unit,Transformer> jump2 = unitToJumpSuccs2.get(u);
//        			            if (!jump1.equals(jump2)) {
//        			                Logger.println(u.toString(), ANSICode.FG_RED);
//                                    Logger.println(m.toString(), ANSICode.FG_RED);
//                                    Logger.println("jump1: " + jump1.size(), ANSICode.FG_BLUE);
//                                    Logger.println("  " + jump1.keySet(), ANSICode.FG_BLUE);
//                                    Logger.println("jump2: " + jump2.size(), ANSICode.FG_BLUE);
//                                    Logger.println("  " + jump2.keySet(), ANSICode.FG_BLUE);
//                                    ProfilerSupport.waitForKeyPress();
//        			            }
//        			        }
//        			    }
        			}
        			
        			// calculate which units to involve in component-wide 
        			// compaction
                    for (Unit u : cfg) {
                        Map<Unit,ITransformer> jumpSuccs = unitToJumpSuccs.get(u);
                        if (jumpSuccs != null) {
                            // check that succ is not only endstmt
                            boolean onlySuccIsEnd = true;
                            for (Unit s : jumpSuccs.keySet()) {
                                if (!(s instanceof EndStmt)) {
                                    onlySuccIsEnd = false;
                                }
                            }
                            if (!onlySuccIsEnd) {
                                unitsToCompactInComponent.add(u);
                            }
                        }
                    }
                    unitsToCompactInComponent.add(start);        			
        			
        			return null;
		        }
		    });
		}
		
		try {
		    AtomicTransformer.POOL.invokeAll(tasks);
		}
		catch (Exception e) {
		    throw new RuntimeException(e);
		}
		
//		for (Callable<Object> ct : tasks) {
//		    try {
//		        ct.call();
//		    }
//		    catch (Exception e) {
//		        throw new RuntimeException(e);
//		    }
//		}
		
		long took = System.currentTimeMillis() - startTime;
		Logger.println(String.format("Took: %.2f seconds", (took/1000.0)));
		
		if (AtomicTransformer.INTERMEDIATE_RESULTS)
		    Logger.println("Invocations: " + invokeCount + " of which " + allInLowerComponentsCount + " have all their targets in lower components");
	}
	
    // free memory
	private void clear() {
        unitToEntry.clear();
//        unitToEntryDelta.clear();
        unitToExit.clear();
       
        unitToPreds.clear();
        unitToSuccs.clear();
        unitToJumpPreds.clear();
        unitToJumpSuccs.clear();
        unitToTransformer.clear();

        methodToStartUnit.clear();
        methodToEndUnit.clear();
        startUnitToMethod.clear();
        unitToMethod.clear();
        callerToCallees.clear();
        calleeToCallers.clear();
        callToParamsArgs.clear();
        numbers.clear();
        unitsToCompactInComponent.clear();
        //callToReturnTransformer.clear();
        //callToCallTransformer.clear();
//        StateFactory.clear();
        //methodToSummaryDelta.clear();
        
        if (useDeltas) {
            unitToExitDelta.clear();
            unitToTransformerDelta.clear();
        }
        
	}
	
	public void outputDot() {
		for (Component c : components) {
			if (hasAlreadyBeenAnalysed(c)) {
				outputDot(c);
			}
		}
	}
	
	public void outputDot(Component c) {
		for (SootMethod m : c) {
		    DotGraph cfg = cfgToDotter.drawCFG(CFGCache.getCFG(m));
		    cfg.plot("m" + m.getNumber() + "cfg.dot");
			ITransformer t = methodToSummary.get(m);
			t.outputDot(m, AtomicTransformer.AGGREGATE_EDGES, "m" + m.getNumber() + ".dot");
			Automaton nfa = t.getAccessesNfa();
			nfa.outputDot("m" + m.getNumber() + "nfa.dot", null);
			if (AtomicTransformer.NFA_TO_DFA) {
			    Pair<Map<State,Set<State>>, Automaton> p = nfa.convertToDfa();
	            Automaton dfa = p.getSecond();
	            dfa.outputDot("m" + m.getNumber() + "dfa.dot", null);
//			    Transformer tReduced = t.removeRedundancy();
//			    tReduced.outputDot(m, AtomicTransformer.AGGREGATE_EDGES, "m" + m.getNumber() + "reduced.dot");
			}
	        AutomatonToLocks convertor = new AutomatonToLocks(nfa,null,null,null);
	        LockSet locks = (LockSet)convertor.getLocks();
	        locks.output("m" + m.getNumber() + "locks.txt");
		}
	}
	
	private void createIntraJumps(SootMethod m, ExceptionalUnitGraph cfg, Component c) {
		
	    boolean debug = false;//AtomicTransformer.DEBUG = m.toString().contains("void reap()");
		
		Map<Unit,Map<Unit,ITransformer>> unitToJumpEntry = new HashMap<Unit, Map<Unit,ITransformer>>();
		Map<Unit,Map<Unit,ITransformer>> unitToJumpExit = new HashMap<Unit, Map<Unit,ITransformer>>();
//		List<Unit> worklist = new ArrayList<Unit>();
		SortedSet<Unit> worklist = constructWorklist(numbers);
		List<Unit> invokesToFold = new ArrayList<Unit>();
		
		// build up list of end node + all invoke stmts (that have targets in the current component)
		List<Unit> targetUnits = new ArrayList<Unit>();
		targetUnits.add(methodToEndUnit.get(m));
		outer: for (Unit u : cfg) {
			if (((Stmt)u).containsInvokeExpr()) {
			    List<SootMethod> callees = callerToCallees.get(u);
			    for (SootMethod callee : callees) {
			        if (c.contains(callee)) {
			            targetUnits.add(u);
			            continue outer;
			        }
			    }
			    invokesToFold.add(u);
			}
		}
		
		// create initial maps for jump targets and add preds to the worklist
		for (Unit jumpTarget : targetUnits) {
			// { u --> id }
			Map<Unit,ITransformer> jumpMap = new HashMap<Unit, ITransformer>();
			jumpMap.put(jumpTarget, identityTransformer);
			unitToJumpEntry.put(jumpTarget, jumpMap);
			
			// add preds to the worklist
			for (Unit pred : unitToPreds.get(jumpTarget)) {
				if (!worklist.contains(pred)) {
					worklist.add(pred);
				}
			}
		}
		
		// compute reduced cfg
		while (!worklist.isEmpty()) {
//			Unit u = worklist.remove(0);
		    Unit u = worklist.first();
		    worklist.remove(u);
			
			// calculate meet
			Map<Unit,ITransformer> newExit = new HashMap<Unit, ITransformer>();
			for (Unit succ : unitToSuccs.get(u)) {
				Map<Unit,ITransformer> sEntry = unitToJumpEntry.get(succ);
				if (sEntry != null) {
					for (Unit jumpTarget : sEntry.keySet()) {
						ITransformer altPathTransformer = sEntry.get(jumpTarget);
						ITransformer alreadyAccumulatedPathTransformer = newExit.get(jumpTarget);
						if (alreadyAccumulatedPathTransformer == null) {
							alreadyAccumulatedPathTransformer = newEmptyTransformer();
							newExit.put(jumpTarget, alreadyAccumulatedPathTransformer);
							alreadyAccumulatedPathTransformer.overwriteWith(altPathTransformer);
						}
						else {
							alreadyAccumulatedPathTransformer.unionWith(altPathTransformer);
						}
					}
				}
			}
			
//			for(Unit j : newExit.keySet()) {
//			    ITransformer t = newExit.get(j);
//			    t.toArraySets();
//			    t.cleanup();
//			}

			// if start or invoke node (those that cannot be folded), store in exit for later
			if (u instanceof StartStmt || (((Stmt)u).containsInvokeExpr() && !invokesToFold.contains(u))) {
				unitToJumpExit.put(u, newExit);
			}
			// otherwise, push through unit 
			else {
				ITransformer t = unitToTransformer.get(u);
				Map<Unit,ITransformer> oldEntry = unitToJumpEntry.get(u);
				Map<Unit,ITransformer> newEntry = new HashMap<Unit, ITransformer>();
				// point-wise function composition
				if (debug) Logger.println("u: " + u);
				if (debug) Logger.println("========");
				if (debug) Logger.println("NEW ENTRY:");
				for (Unit jumpTarget : newExit.keySet()) {
					ITransformer pathTransformer = newExit.get(jumpTarget);
					ITransformer updatedPathTransformer = pathTransformer.composeWith(t);
					if (debug) Logger.println("t: " + jumpTarget, ANSICode.FG_RED);
					if (debug) Logger.println("before: " + pathTransformer.size(), ANSICode.FG_RED);
					if (debug) Logger.println("after: " + updatedPathTransformer.size(), ANSICode.FG_RED);
					if (debug) Logger.println("------");
					newEntry.put(jumpTarget, updatedPathTransformer);
				}

				if (oldEntry != null) {
    				if (debug) Logger.println("OLD ENTRY:");
    				for (Unit jumpTarget : oldEntry.keySet()) {
                        if (debug) Logger.println("t: " + jumpTarget, ANSICode.FG_BLUE);
                        if (debug) Logger.println("val: " + oldEntry.get(jumpTarget).size(), ANSICode.FG_BLUE);
                        if (debug) Logger.println("------");
    				}
				}
				// add preds to worklist if entry changed
				if (oldEntry == null || !oldEntry.equals(newEntry)) {
				    
				    if (debug) Logger.println("not equal");
				    if (debug && oldEntry != null) {
				        for (Unit target : oldEntry.keySet()) {
				            ITransformer oldT = oldEntry.get(target);
				            ITransformer newT = newEntry.get(target);
				            if (!oldT.equals(newT)) {
				                Logger.println("manual check not equal (for " + target + ")");
				            }
				        }
				    }
//				    Logger.println("u: " + u);
//				    Logger.println("old: " + oldEntry);
//				    Logger.println("new: " + newEntry);
//				    if (m.toString().contains("void reap")) {
//				        ProfilerSupport.waitForKeyPress();
//				    }
					unitToJumpEntry.put(u, newEntry);
					for (Unit pred : unitToPreds.get(u)) {
						if (!worklist.contains(pred)) {
							worklist.add(pred);
						}
					}
				}
				if (debug) Logger.println("=========");
				if (debug) ProfilerSupport.waitForKeyPress();
			}
		}
		
		// Store map from units to their jump preds and succs, together with
		// the path transformers
		for (Unit u : unitToJumpExit.keySet()) {
			Map<Unit,ITransformer> pathTransformers = unitToJumpExit.get(u);
			unitToJumpSuccs.put(u, pathTransformers);
			for (Unit jumpTarget : pathTransformers.keySet()) {
				List<Unit> jumpTargetPreds = unitToJumpPreds.get(jumpTarget);
				if (jumpTargetPreds == null) {
					jumpTargetPreds = new ArrayList<Unit>();
					unitToJumpPreds.put(jumpTarget, jumpTargetPreds);
				}
				if (!jumpTargetPreds.contains(u)) {
					jumpTargetPreds.add(u);
				}
			}
		}
		// don't forget the end node
		unitToJumpSuccs.put(methodToEndUnit.get(m), new HashMap<Unit, ITransformer>());
	}
	
//	private Map<Unit, Map<Unit,Transformer>> unitToJumpSuccs2 = new HashMap<Unit, Map<Unit,Transformer>>();
//	private Map<Unit, List<Unit>> unitToJumpPreds2 = new HashMap<Unit, List<Unit>>();

    private void createIntraJumpsDeltas(SootMethod m, ExceptionalUnitGraph cfg, Component c) {
        
        long start = System.currentTimeMillis();
        boolean debug = false;//AtomicTransformer.DEBUG = m.toString().contains("void reap()");
        
        Map<Unit,Map<Unit,ITransformer>> unitToJumpEntry = new HashMap<Unit, Map<Unit,ITransformer>>();
        Map<Unit,Map<Unit,ITransformer>> unitToJumpExit = new HashMap<Unit, Map<Unit,ITransformer>>();
        Map<Unit,Map<Unit,ITransformer>> unitToJumpExitDelta = new HashMap<Unit, Map<Unit,ITransformer>>();
        
//      List<Unit> worklist = new ArrayList<Unit>();
        SortedSet<Unit> worklist = constructWorklist(numbers);
        List<Unit> invokesToFold = new ArrayList<Unit>();
        
        // build up list of end node + all invoke stmts (that have targets in the current component)
        List<Unit> targetUnits = new ArrayList<Unit>();
        targetUnits.add(methodToEndUnit.get(m));
        outer: for (Unit u : cfg) {
            if (((Stmt)u).containsInvokeExpr()) {
                List<SootMethod> callees = callerToCallees.get(u);
                for (SootMethod callee : callees) {
                    if (c.contains(callee)) {
                        targetUnits.add(u);
                        continue outer;
                    }
                }
                invokesToFold.add(u);
            }
        }
        
        // create initial maps for jump targets and add preds to the worklist
        for (Unit jumpTarget : targetUnits) {
            // { u --> id }
            Map<Unit,ITransformer> jumpMap = new HashMap<Unit, ITransformer>();
            jumpMap.put(jumpTarget, identityTransformer);
            unitToJumpEntry.put(jumpTarget, jumpMap);
            
            // add preds to the worklist
            for (Unit pred : unitToPreds.get(jumpTarget)) {
                if (!worklist.contains(pred)) {
                    worklist.add(pred);
                }
                Map<Unit,ITransformer> predDeltaExit = unitToJumpExitDelta.get(pred);
                if (predDeltaExit == null) {
                    predDeltaExit = new HashMap<Unit, ITransformer>();
                    unitToJumpExitDelta.put(pred, predDeltaExit);
                }
            }
        }
        
        // compute reduced cfg
        while (!worklist.isEmpty()) {
            Unit u = worklist.first();
            worklist.remove(u);
            
            ITransformer t = unitToTransformer.get(u);
            
            Map<Unit,ITransformer> exit = unitToJumpExit.get(u);
            Map<Unit,ITransformer> deltaExit = unitToJumpExitDelta.get(u);
            Map<Unit,ITransformer> entry = null;
            
            if (exit == null) {
                exit = new HashMap<Unit, ITransformer>();
                unitToJumpExit.put(u, exit);
                
                // take meet of successors
                for (Unit succ : unitToSuccs.get(u)) {
                    Map<Unit,ITransformer> sEntry = null;
                    if (storeEntry || targetUnits.contains(succ)) {
                        sEntry = unitToJumpEntry.get(succ);
                    }
                    else {
                        Map<Unit,ITransformer> sExit = unitToJumpExit.get(succ);
                        if (sExit != null) {
                            ITransformer sT = unitToTransformer.get(succ);
                            sEntry = new HashMap<Unit, ITransformer>();
                            for (Unit jS : sExit.keySet()) {
                                ITransformer jSExit = sExit.get(jS);
                                ITransformer jSExitUpdated = jSExit.composeWith(sT);
                                sEntry.put(jS, jSExitUpdated);
                            }
                        }
                    }
                    if (sEntry != null) {
                        for (Unit jumpTarget : sEntry.keySet()) {
                            ITransformer altPathTransformer = sEntry.get(jumpTarget);
                            ITransformer alreadyAccumulatedPathTransformer = exit.get(jumpTarget);
                            if (alreadyAccumulatedPathTransformer == null) {
                                alreadyAccumulatedPathTransformer = newEmptyTransformer();
                                exit.put(jumpTarget, alreadyAccumulatedPathTransformer);
                                alreadyAccumulatedPathTransformer.overwriteWith(altPathTransformer);
                            }
                            else {
                                alreadyAccumulatedPathTransformer.unionWith(altPathTransformer);
                            }
                        }
                    }
                }
                
                if (!(u instanceof StartStmt || (((Stmt)u).containsInvokeExpr() && !invokesToFold.contains(u)))) {
                    
                    if (storeEntry) {
                        entry = new HashMap<Unit, ITransformer>();
                        unitToJumpEntry.put(u, entry);
                        
                        for (Unit j : exit.keySet()) {
                            ITransformer pathTransformer = exit.get(j);
                            ITransformer updatedPathTransformer = pathTransformer.composeWith(t);
                            entry.put(j, updatedPathTransformer);                    
                        }
                    
//                        unitToJumpEntry.put(u, entry);
                    }
                    
                    for (Unit p : unitToPreds.get(u)) {
                        if (!worklist.contains(p)) {
                            worklist.add(p);
                        }
                        Map<Unit,ITransformer> predDeltaExit = unitToJumpExitDelta.get(p);
                        if (predDeltaExit == null) {
                            predDeltaExit = new HashMap<Unit, ITransformer>();
                            unitToJumpExitDelta.put(p, predDeltaExit);
                        }
                        for (Unit j : exit.keySet()) {
                            predDeltaExit.put(j, null);
                        }
                    }
                    
                }
                
            }
            else {

                entry = unitToJumpEntry.get(u);
                
                for (Unit j : deltaExit.keySet()) {

                    ITransformer jOldExit = exit.get(j);
                    ITransformer jNewExit = null;
                    ITransformer jOldEntry = storeEntry ? (entry == null ? null : entry.get(j)) : null;
                    ITransformer jNewEntry = null;
                    ITransformer jDeltaExit = deltaExit.get(j);
                    ITransformer jDeltaEntry = null;
                    
                    if (jDeltaExit == null) {
                    
                        // take meet of succs' entry(j)
                        jNewExit = newEmptyTransformer();
                        
                        boolean first = true;
                        for (Unit succ : unitToSuccs.get(u)) {
                            ITransformer jSuccEntry = null;
                            if (storeEntry || targetUnits.contains(succ)) {
                                Map<Unit,ITransformer> sEntry = unitToJumpEntry.get(succ);
                                if (sEntry != null) {
                                    jSuccEntry = sEntry.get(j);
                                }
                            }
                            else {
                                Map<Unit,ITransformer> sExit = unitToJumpExit.get(succ);
                                if (sExit != null) {
                                    ITransformer sT = unitToTransformer.get(succ);
                                    ITransformer jSuccExit = sExit.get(j);
                                    if (jSuccExit != null) {
                                        jSuccEntry = jSuccExit.composeWith(sT);
                                    }
                                }
                            }
                            if (jSuccEntry != null) {
                                if (first) {
                                    jNewExit.overwriteWith(jSuccEntry);
                                    first = false;
                                }
                                else {
                                    jNewExit.unionWith(jSuccEntry);
                                }
                            }
                        }
                        
                        // recompute delta exit in case new exit subsumes old exit
                        if (jOldExit != null && jNewExit.subsumes(jOldExit)) {
                            jDeltaExit = jNewExit.differenceWith(jOldExit);
                        }
                    }

                    if (jDeltaExit == null) {

                        if (!(u instanceof StartStmt || (((Stmt)u).containsInvokeExpr() && !invokesToFold.contains(u)))) {

                            if (storeEntry) {
                                jNewEntry = jNewExit.composeWith(t);
                                
                                if (jOldEntry != null && jNewEntry.subsumes(jOldEntry)) {
                                    jDeltaEntry = jNewEntry.differenceWith(jOldEntry);
                                }
                                else {
                                    jDeltaEntry = null;
                                }
                            }
                            else {
                                jDeltaEntry = null;
                            }
                            
                            //entry.put(j, jNewEntry); // todo: comment
                            
                        }
                        
                    }
                    else {
                        
//                        Logger.println("  jDeltaExit not null");
                        // refine deltaExit
                        DeltaTransformer newJDeltaExit = new DeltaTransformer();
                        jNewExit = jOldExit.addAllReturnDelta(jDeltaExit, newJDeltaExit);
                        jDeltaExit = newJDeltaExit;

                        if (!(u instanceof StartStmt || (((Stmt)u).containsInvokeExpr() && !invokesToFold.contains(u)))) {
//                            Logger.println("  Computing jDeltaEntry");
                            jDeltaEntry = jDeltaExit.composeWith(t);
                            if (storeEntry) {
                                DeltaTransformer newJDeltaEntry = new DeltaTransformer();
                                jNewEntry = jOldEntry.addAllReturnDelta(jDeltaEntry, newJDeltaEntry);
                                jDeltaEntry = newJDeltaEntry;
                            }
                        
                        }
                        
                    }

                    exit.put(j, jNewExit);
                    
                    if (!(u instanceof StartStmt || (((Stmt)u).containsInvokeExpr() && !invokesToFold.contains(u)))) {
                        
                        if (storeEntry) {
                            entry.put(j, jNewEntry);
                        }
                        
                        if (jDeltaEntry == null || !jDeltaEntry.isEmpty()) {
                            
                            for (Unit p : unitToPreds.get(u)) {
                                if (!worklist.contains(p)) {
                                    worklist.add(p);
                                }
                                // propagate jDeltaEntry to p's deltaExit
                                Map<Unit,ITransformer> pDeltaExit = unitToJumpExitDelta.get(p);
                                if (pDeltaExit == null) {
                                    pDeltaExit = new HashMap<Unit, ITransformer>();
                                    unitToJumpExitDelta.put(p, pDeltaExit);
                                }
                                ITransformer jPredDeltaExit = pDeltaExit.get(j);
                                if (jPredDeltaExit == null || jDeltaEntry == null) {
                                    pDeltaExit.put(j, null);
                                }
                                else {
                                    ITransformer newJPredDeltaExit = jPredDeltaExit.addAll(jDeltaEntry);
                                    pDeltaExit.put(j, newJPredDeltaExit);
                                }
                            }
                            
                        }
                        
                    }
                    
                }
                
            }
            
            // reset deltaExit
            for (Unit j : exit.keySet()) {
                deltaExit.put(j, new DeltaTransformer()); // reset
            }
            
        }
            
        // Store map from units to their jump preds and succs, together with
        // the path transformers
        for (Unit u : unitToJumpExit.keySet()) {
            if (u instanceof StartStmt || (((Stmt)u).containsInvokeExpr() && !invokesToFold.contains(u))) { 
                Map<Unit,ITransformer> pathTransformers = unitToJumpExit.get(u);
                unitToJumpSuccs.put(u, pathTransformers);
                for (Unit jumpTarget : pathTransformers.keySet()) {
                    List<Unit> jumpTargetPreds = unitToJumpPreds.get(jumpTarget);
                    if (jumpTargetPreds == null) {
                        jumpTargetPreds = new ArrayList<Unit>();
                        unitToJumpPreds.put(jumpTarget, jumpTargetPreds);
                    }
                    if (!jumpTargetPreds.contains(u)) {
                        jumpTargetPreds.add(u);
                    }
                }
            }
        }
        
        // don't forget the end node
        unitToJumpSuccs.put(methodToEndUnit.get(m), new HashMap<Unit, ITransformer>());
        
        long took = System.currentTimeMillis()-start;
        AnalysisTimer.addForReduction(took, m);
    }
	
	// for call m(a1,a2,a3) for method with declaration m(p1,p2,p3), creates
	// the mapping { p1 -> a1, p2 -> a2, p3 -> a3 }
	private TIntIntHashMap createParamsToArgsMapping(Stmt s) {
        InvokeExpr invokeExpr = s.getInvokeExpr();
        TIntIntHashMap paramsToArgs = new TIntIntHashMap();
        // 'this' variable mapping
        if (invokeExpr instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr instInvokeExpr = (InstanceInvokeExpr)invokeExpr;
            Local receiver = (Local)instInvokeExpr.getBase();
            paramsToArgs.put(SymbolNumberer.getNumber(ThisVariable.v()), SymbolNumberer.getNumber(receiver));
        }
        // '$ret' variable mapping
        if (s instanceof AssignStmt) {
            AssignStmt assStmt = (AssignStmt)s;
            Local x = (Local)assStmt.getLeftOp();
            if (x.getType() instanceof RefLikeType) {
                paramsToArgs.put(SymbolNumberer.getNumber(ReturnVariable.v()), SymbolNumberer.getNumber(assStmt.getLeftOp()));
            }
        }
        // remaining parameters (only store mapping for args that are local vars)
        int i=0;
        for (Object arg : invokeExpr.getArgs()) {
            if (arg instanceof Local) {
                Local la = (Local)arg;
                if (la.getType() instanceof RefLikeType) {
                    ParameterVariable param = ParameterVariable.v(i);
                    paramsToArgs.put(SymbolNumberer.getNumber(param), SymbolNumberer.getNumber(arg));
                }
            }
            i++;
        }
        return paramsToArgs;
//		InvokeExpr invokeExpr = s.getInvokeExpr();
//		Map<ParameterVariable, Local> paramsToArgs = new HashMap<ParameterVariable, Local>(invokeExpr.getArgCount()+2, 1);
//		// 'this' variable mapping
//		if (invokeExpr instanceof InstanceInvokeExpr) {
//			InstanceInvokeExpr instInvokeExpr = (InstanceInvokeExpr)invokeExpr;
//			paramsToArgs.put(ThisVariable.v(), (Local)instInvokeExpr.getBase());
//		}
//		// '$ret' variable mapping
//		if (s instanceof AssignStmt) {
//			AssignStmt assStmt = (AssignStmt)s;
//			Local x = (Local)assStmt.getLeftOp();
//			if (x.getType() instanceof RefLikeType) {
//				paramsToArgs.put(ReturnVariable.v(), (Local)assStmt.getLeftOp());
//			}
//		}
//		// remaining parameters (only store mapping for args that are local vars)
//		int i=0;
//		for (Object arg : invokeExpr.getArgs()) {
//			if (arg instanceof Local) {
//				Local la = (Local)arg;
//				if (la.getType() instanceof RefLikeType) {
//					ParameterVariable param = ParameterVariable.v(i);
//					paramsToArgs.put(param, (Local)arg);
//				}
//			}
//			i++;
//		}
//		return paramsToArgs;
	}

	private ITransformer createInvokeTransformer(Unit u) {
		ITransformer t = newEmptyTransformer();
		boolean firstTarget = true;
		for (SootMethod target : callerToCallees.get(u)) {
			if (!target.isConcrete()) {
				throw new RuntimeException(target.toString() + " is not concrete");
			}
			ITransformer summary = methodToSummary.get(target);
			if (firstTarget) {
				t.overwriteWith(summary);
				firstTarget = false;
			}
			else {
				t.unionWith(summary);
			}
		}
		//Logger.println("Invoke transformer for " + u + ": " + t);
		t = t.calleeToCallerContext(callToParamsArgs.get(u));
//		t.toArraySets();
		t.cleanup();
		return t;
	}

//   private Transformer createInvokeLowerTransformer(Unit u) {
//        Transformer t = null;
//        List<SootMethod> calleesCurrentComponent = callerToCalleesCurrentComponent.get(u);
//        boolean firstTarget = true;
//        for (SootMethod target : callerToCallees.get(u)) {
//            
//            // skip target if in current component
//            if (calleesCurrentComponent != null && calleesCurrentComponent.contains(target)) {
//                continue;
//            }
//            
//            if (!target.isConcrete()) {
//                throw new RuntimeException(target.toString() + " is not concrete");
//            }
//            Transformer summary = methodToSummary.get(target);
//            if (summary == null) {
//                throw new RuntimeException("u: " + u + " target: " + target.toString());
//            }
//            if (firstTarget) {
//                if (t == null) {
//                    t = new Transformer();
//                }
//                t.overwriteWith(summary);
//                firstTarget = false;
//            }
//            else {
//                t.unionWith(summary);
//            }
//        }
//        if (t != null) {
//            t = t.calleeToCallerContext(callToParamsArgs.get(u));
//            t.cleanup();
//        }
//        
//        return t;
//    }
	
	/*private Transformer createReturnTransformer(Stmt s) {
		// x = m(..) or x = r.m(..)
		AssignStmt assStmt = (AssignStmt)s;
		Local x = (Local)assStmt.getLeftOp();
		if (x.getType() instanceof RefLikeType) {
			return new ReturnTransformer(x);
		}
		else {
			return identityTransformer;
		}
	}

	private Transformer createCallTransformer(Stmt s) {
		return new CallTransformer(s.getInvokeExpr());
	}*/

	private ITransformer createTransformer(Unit u, SootMethod m) {
		if (u instanceof DefinitionStmt) {
			DefinitionStmt defSt = (DefinitionStmt)u;

			Value lval = defSt.getLeftOp();
			Value rval = defSt.getRightOp();

			// transformers
			if(lval instanceof Local && lval.getType() instanceof RefLikeType/* && lval.getType() != stringType*/) {
				Local x = (Local)lval;
				// x = blah
				if (rval instanceof Local) {
					// x = y
	            	Local y = (Local)rval;
	                return newLocalCopyTransformer(x, y);
				}
				else if (rval instanceof NullConstant) {
					// x = null
					return newNullCopyTransformer(x);
				}
				else if (rval instanceof NewExpr || rval instanceof NewArrayExpr || rval instanceof NewMultiArrayExpr) {
	            	// x = new/newarray/newmultiarray
					return newNullCopyTransformer(x);
				}
				else if (rval instanceof StringConstant) {
					// x = ""
					return newNullCopyTransformer(x);
				}
	            else if(rval instanceof CastExpr) {
	                CastExpr castEx = (CastExpr)rval;
	                if(castEx.getOp() instanceof Local) {
	                	// x = (type)y
	                	Local y = (Local)castEx.getOp();
                		return newLocalCopyTransformer(x, y);
	                }
	                else if(castEx.getOp() instanceof NullConstant) {
	                	// x = (type)null
	                	return newNullCopyTransformer(x);
	                }
	                else if(castEx.getOp() instanceof StringConstant) {
	                	// x = (String)""
	                	return newNullCopyTransformer(x);
	                }
		        }
	            else if (rval instanceof InstanceFieldRef) {
		        	// x = y.f
		        	InstanceFieldRef instFieldRef = (InstanceFieldRef)rval;
		        	Local y = (Local)instFieldRef.getBase();
		        	SootField f = instFieldRef.getField();
	        	    return newFieldLoadTransformer(x, y, f, defSt);
	            }
	            else if (rval instanceof StaticFieldRef) {
	            	// x = C.f
	            	StaticFieldRef staticFieldRef = (StaticFieldRef)rval;
	            	SootField f = staticFieldRef.getField();
	            	SootClass c = f.getDeclaringClass();
//	            	Logger.println("x=C.f");
//	            	Logger.println("C.getNumber(): " + c.getNumber());
            		return newFieldLoadTransformer(x, c, f, defSt);
	            }
	            else if (rval instanceof ArrayRef) {
	            	// x = y[i]
	            	ArrayRef arrRef = (ArrayRef)rval;
	            	Local y = (Local)arrRef.getBase();
            		return newArrayLoadTransformer(x, y, defSt);
	            }
	            else if (rval instanceof ThisRef) {
	            	ThisVariable thisVar = ThisVariable.v();
	            	return newLocalCopyTransformer(x, thisVar);
	            }
	            else if (rval instanceof ParameterRef) {
	            	ParameterRef pRef = (ParameterRef)rval;
	            	int n = pRef.getIndex();
	            	ParameterVariable pVar = ParameterVariable.v(n);
	            	return newLocalCopyTransformer(x, pVar);
	            }
	            else if (rval instanceof CaughtExceptionRef) {
	            	return newNullCopyTransformer(x);
	            }
			}
			else if (lval instanceof InstanceFieldRef && lval.getType() instanceof RefLikeType/* && lval.getType() != stringType*/) {
				// x.f = blah
            	InstanceFieldRef instFieldRef = (InstanceFieldRef)lval;
            	Local x = (Local)instFieldRef.getBase();
            	SootField f = instFieldRef.getField();
            	if (rval instanceof Local) {
					// x.f = y
            		Local y = (Local)rval;
            		return newFieldStoreTransformer(x, f, y, defSt);
            	}
            	else if (rval instanceof NullConstant) {
					// x.f = null
					return newAccessTransformer(x, defSt, true);
				}
            	else if (rval instanceof StringConstant) {
            		// x.f = "";
            		return newAccessTransformer(x, defSt, true);
            	}
			}
			else if (lval instanceof StaticFieldRef && lval.getType() instanceof RefLikeType/* && lval.getType() != stringType*/) {
				// C.f = blah
            	StaticFieldRef staticFieldRef = (StaticFieldRef)lval;
            	SootField f = staticFieldRef.getField();
            	SootClass c = f.getDeclaringClass();
            	if (rval instanceof Local) {
					// C.f = y
            		Local y = (Local)rval;
            		return newStaticFieldStoreTransformer(c, f, y, defSt);            		
            	}
            	else if (rval instanceof NullConstant) {
					// C.f = null
					return newStaticFieldStoreNullTransformer(c, f, defSt);
				}
            	else if (rval instanceof StringConstant) {
            		// C.f = ""
            		return newStaticFieldStoreNullTransformer(c, f, defSt);
            	}
			}
			else if (lval instanceof ArrayRef && lval.getType() instanceof RefLikeType) {
				// x[i] = blah
				ArrayRef arrRef = (ArrayRef)lval;
				Local x = (Local)arrRef.getBase();
				if (rval instanceof Local) {
					// x[i] = y
					Local y = (Local)rval;
					return newArrayStoreTransformer(x, y, defSt);
				}
				else if (rval instanceof NullConstant) {
					// x[i] = null
					return newAccessTransformer(x, defSt, true);
				}
				else if (rval instanceof StringConstant) {
					// x[i] = ""
					return newAccessTransformer(x, defSt, true);
				}
			}

			// just accesses
			if(lval instanceof InstanceFieldRef) {
				InstanceFieldRef instFieldRef = (InstanceFieldRef)lval;
				Local x = (Local)instFieldRef.getBase();
				return newAccessTransformer(x, defSt, true);
			}
			else if(lval instanceof StaticFieldRef) {
				StaticFieldRef staticFieldRef = (StaticFieldRef)lval;
				SootClass c = staticFieldRef.getField().getDeclaringClass();
				return newAccessTransformer(c, defSt, true);				
			}
			else if(lval instanceof ArrayRef) {
				ArrayRef arrRef = (ArrayRef)lval;
				Local x = (Local)arrRef.getBase();
				return newAccessTransformer(x, defSt, true);
			}
			else if(rval instanceof InstanceFieldRef) {
				InstanceFieldRef instFieldRef = (InstanceFieldRef)rval;
				Local x = (Local)instFieldRef.getBase();
				return newAccessTransformer(x, defSt, false);
			}
			else if(rval instanceof StaticFieldRef) {
				StaticFieldRef staticFieldRef = (StaticFieldRef)rval;
				SootClass c = staticFieldRef.getField().getDeclaringClass();
				return newAccessTransformer(c, defSt, false);				
			}
			else if(rval instanceof ArrayRef) {
				ArrayRef arrRef = (ArrayRef)rval;
				Local x = (Local)arrRef.getBase();
				return newAccessTransformer(x, defSt, false);
			}
			
			return identityTransformer;
		}
		else if (u instanceof ReturnStmt) {
			ReturnStmt r = (ReturnStmt)u;
			Value val = r.getOp();
			if (val instanceof Local && val.getType() instanceof RefLikeType/* && val.getType() != stringType*/) {
				Local x = (Local)val;
				return newReturnStmtTransformer(x);
			}
			else if (val instanceof NullConstant) {
				return newReturnNullTransformer();
			}
			else if (val instanceof StringConstant) {
				return newReturnNullTransformer();
			}
			
			return identityTransformer;
		}
		else if (u instanceof ThrowStmt) {
		    boolean doesMethodReturn = m != null && m.getReturnType() != VoidType.v();
		    if (doesMethodReturn) {
		        return newThrowTransformer();
		    }
		    else {
		        return identityTransformer;
		    }
		}
		else {
			return identityTransformer;
		}
    }
	
	public void doAnalysis() {

		long startTime = System.currentTimeMillis();
		
		// perform post-order traversal of components
		for (Component c : dag.getRoots()) {
			doAnalysis(c);
		}
		
		double timeTaken = (System.currentTimeMillis()-startTime)/1000.0;
		Logger.println("Analysed " + components.size() + " components in " + timeTaken + " seconds.");
		
		if (a != null) {
		    propagateAtomic();
		}

	}
	
	private void propagateAtomic() {
	    
	    long startTime = System.currentTimeMillis();
	    
	    Logger.println("");
	    Logger.println("----------------------------------");
	    Logger.println("Initialising atomic section " + a.getId());
	    
        for (Unit u : a) {
            unitToPreds.put(u, new ArrayList<Unit>(exceptions ? a.getPredsOf(u) : a.getUnexceptionalPredsOf(u)));
            unitToSuccs.put(u, new ArrayList<Unit>(exceptions ? a.getSuccsOf(u) : a.getUnexceptionalSuccsOf(u)));
            unitToTransformer.put(u, createTransformer(u, null));
            u.addTag(new ContainingMethodTag(a.getBody().getMethod()));
        }
        
        // insert single start node
        Stmt start = new StartStmt();
        unitToTransformer.put(start, createTransformer(start, null));
        for (Unit h : a.getHeads()) {
            List<Unit> preds = unitToPreds.get(h);
            preds.add(start);
        }
        unitToPreds.put(start, new ArrayList<Unit>());
        unitToSuccs.put(start, a.getHeads());
        unitToEntry.put(start, identityTransformer);
        
        // insert single end node
        Stmt end = new EndStmt();
        List<Unit> atails = a.getTails();
        for (Unit t : atails) {
            List<Unit> succs = unitToSuccs.get(t);
            succs.add(end);
        }
        List<Unit> tails = a.getTails();
        unitToPreds.put(end, tails);
        unitToSuccs.put(end, new ArrayList<Unit>());
        unitToTransformer.put(end, createTransformer(end, null));

        // order nodes
        List<Unit> orderedUnits = new PseudoTopologicalOrderer().newList(a, true);
        numbers.put(end, 1);
        int i = 2;
        for (Unit u : orderedUnits) {
            numbers.put(u, new Integer(i));
            i++;
        }
        numbers.put(start, i);
        
        // record caller to callees, create invoke stmt transformers
        for (Unit u : a) {
            Stmt s = (Stmt)u;
            if (s.containsInvokeExpr()) {
                List<SootMethod> targets = new ArrayList<SootMethod>();
                for (Iterator<Edge> edgesIt=cg.edgesOutOf(u); edgesIt.hasNext(); ) {
                    Edge e = edgesIt.next();
                    if (edgesPred.want(e)) {
                        SootMethod tgt = e.tgt();
                        if (tgt.isConcrete()) {
                            targets.add(tgt);
                        }
                    }
                }
                if (u.toString().contains("next") || u.toString().contains("get")) {
                    Logger.println("u: " + u, ANSICode.FG_BLUE);
                    Logger.println("targets: " + targets, ANSICode.FG_BLUE);
                }
                callerToCallees.put(s, targets);
                
                callToParamsArgs.put(s, createParamsToArgsMapping(s));
                unitToTransformer.put(s, createInvokeTransformer(s));
            }
        }
        
        SortedSet<Unit> worklist = constructWorklist(numbers);
        worklist.add(end);
        
        Logger.println("Running analysis");
        Timer.start();
        
        while (!worklist.isEmpty()) {
            if (debug) Logger.println("worklist: " + worklist, ANSICode.FG_DEFAULT, ANSICode.BG_YELLOW);
            Unit u = worklist.first();
            worklist.remove(u);
            
            if (debug) Logger.println("");
            if (debug) Logger.println("");
            if (debug) Logger.println("Unit: " + u + " (" + StateFactory.v((Stmt)u).getNumber() + ")");
            ITransformer t = unitToTransformer.get(u);
            if (debug) Logger.println("Transformer: " + t, ANSICode.FG_BLUE);
            
            // take meet of all successors
            ITransformer newExit = newEmptyTransformer();
            boolean firstSucc = true;
            for (Unit s : unitToSuccs.get(u)) {
                ITransformer succEntry = unitToEntry.get(s);
                if (succEntry != null) { // in case we reach u before s (e.g in if (b) { ... } ; x = y; )
                    if (firstSucc) {
                        newExit.overwriteWith(succEntry);
                        firstSucc = false;
                    }
                    else {
                        newExit.unionWith(succEntry);
                    }
                }
            }
            newExit.cleanup();
//            newExit.compact();
            
            if (debug) Logger.println("Exit (new): " + newExit, ANSICode.FG_MAGENTA);
            
            // apply transformer to meet and add preds to worklist if
            // change detected
            ITransformer oldEntry = unitToEntry.get(u);
            ITransformer newEntry = newExit.composeWith(t); // don't remove method local vars if u is a start stmt because we may need to lock them
            if (oldEntry == null || !oldEntry.equals(newEntry)) {
                unitToEntry.put(u, newEntry);
                List<Unit> preds = unitToPreds.get(u);
                for (Unit p : preds) {
                    if (!worklist.contains(p)) {
                        worklist.add(p);
                    }
                }
            }
            if (debug) Logger.println("Entry (new): " + newEntry, ANSICode.FG_MAGENTA);
            if (debug) ProfilerSupport.waitForKeyPress(); // single-step
        }
        
        atomicSummary = unitToEntry.get(start);
        atomicSummary = atomicSummary.removeDeadEdges();
        
        long took = System.currentTimeMillis()-startTime;
        AnalysisTimer.addForAtomic(took, a.getBody().getMethod());
        
        Timer.stop();
        Timer.printDuration();
        
    }
   

	int componentCounter = 0;
	int numComponents;

	public void doAnalysis(Component c) {
	    
		if (!hasAlreadyBeenAnalysed(c)) {
			
			for (Component c2 : dag.getSuccsOf(c)) {
				doAnalysis(c2);
			}
			
			final boolean debug = AtomicTransformer.DEBUG;
			final boolean stats = AtomicTransformer.STATS;

			if (debug) Logger.println("Analysing " + c);
			
            if (stats) Logger.printstats("*********************************************************************");
            if (stats) Logger.printstats("Initialising component " + c.getId() + " (" + c.size() + " methods)");
            if (stats) Logger.printstats("*********************************************************************");
			
			// All dependent components have been analysed, now analyse c
			long startTime = System.currentTimeMillis();
			
			if (AtomicTransformer.INTERMEDIATE_RESULTS) {
    			Logger.println("Initialising component " + c.getId() + " (" + c.size() + " methods) (" + ++componentCounter + " of " + numComponents + ") (total: " + components.size() + ")");
    			if (c.size() == 1) {
    				Logger.println("Singleton method: " + c.first());
    			}
			}
			
			init(c);
			
			if (stats) Logger.printstats("cfg nodes: " + unitToJumpSuccs.size());

//			List<Unit> intraWorklist = new ArrayList<Unit>();
			final List<Unit> intraWorklist = new ArrayList<Unit>();
			final List<Unit> interWorklist = new ArrayList<Unit>();
			
			// calculate per-method unit ordering
	        
            Logger.println("First method: " + c.first());
			for (SootMethod mm : c) {
				intraWorklist.add(methodToEndUnit.get(mm));
			}

			if (AtomicTransformer.INTERMEDIATE_RESULTS)
			    Logger.println("Running analysis");
			
//			Map<SootMethod,List<Unit>> callersToBeUpdated = new HashMap<SootMethod, List<Unit>>();
			
//			Map<SootMethod,Transformer> methodToCommonTransformer = new HashMap<SootMethod, Transformer>();
			final Set<SootMethod> methodsToComputeCommonTransformer = Collections.synchronizedSet(new HashSet<SootMethod>());
			final Set<SootMethod> methodsToCompact = Collections.synchronizedSet(new HashSet<SootMethod>());
			for (SootMethod m : c) {
			    ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
			    int stmtCount = 0;
			    for (Unit u : cfg) {
                    if (unitToJumpSuccs.containsKey(u)) {
    			        // check that succ is not only endstmt
                        boolean onlySuccIsEnd = true;
                        for (Unit s : unitToJumpSuccs.get(u).keySet()) {
                            if (!(s instanceof EndStmt)) {
                                onlySuccIsEnd = false;
                            }
                        }
                        if (!onlySuccIsEnd) {
                            stmtCount++;
                        }
                    }
			    }
			    stmtCount++; // 1 more for start stmt
			    if (stmtCount > 1) {
			        methodsToCompact.add(m);
			    }
			}
			
			Logger.println(methodsToCompact.size() + " methods can be compacted");
			
//          THE FOLLOWING CODE IS WRONG:
//			Set<SootMethod> methodsWithOneRecursiveCall = new HashSet<SootMethod>();
//			for (SootMethod m : c) {
//			    ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
//			    int stmtCount = 0;
//			    Unit first = null;
//			    for (Unit u : cfg) {
//			        Map<Unit,Transformer> jumpSuccs = unitToJumpSuccs.get(u);
//			        if (jumpSuccs != null) {
//			            first = u;
//			            stmtCount++;
//			        }
//			    }
//			    if (stmtCount == 1) {
//			        Map<Unit,Transformer> firstJumpSuccs = unitToJumpSuccs.get(first);
//			        if (firstJumpSuccs.size() == 1) {
//			            methodsWithOneRecursiveCall.add(m);
//			        }
//			    }
//			}
//			
//			Logger.println(methodsWithOneRecursiveCall.size() + " methods with one recursive call");
			
//			Set<SootMethod> component = new HashSet<SootMethod>(c);
//			component.removeAll(methodsToCompact);
//			component.removeAll(methodsWithOneRecursiveCall);
//			Logger.println("not in both: " + component);
//			
//			for (SootMethod m : component) {
//			    for (Unit u : unitToJumpSuccs.keySet()) {
//			        if (unitToMethod.get(u) == m) {
//			            Logger.println("u: " + u);
//			            Logger.println("succs: " + unitToJumpSuccs.get(u).keySet());
//			        }
//			    }
//			}
			
//			int totalStmtCount = unitToJumpSuccs.keySet().size();
//			Logger.println(unitsToCompactInComponent.size() + " stmts (of " + totalStmtCount + ") can be compacted");
			
			final AtomicInteger entry_deltas = new AtomicInteger(0), entry_nondeltas = new AtomicInteger(0), transformer_delta = new AtomicInteger(0), transformer_nondelta = new AtomicInteger(0);
			
			int compactionCounter = 0;
			final int startCompaction = AtomicTransformer.START_COMPACTION;
			boolean sweep = AtomicTransformer.SWEEP;
			boolean intra = true;
			while (!intraWorklist.isEmpty() || !interWorklist.isEmpty()) {
//				Logger.println("Inter worklist: " + interWorklist, ANSICode.FG_DEFAULT, ANSICode.BG_YELLOW);
//				Logger.println("Intra worklist: " + intraWorklist, ANSICode.FG_DEFAULT, ANSICode.BG_YELLOW);
//			    if (++counter == 100) {
//			        Logger.println("e_deltas: " + entry_deltas + ", e: " + entry_nondeeltas + ", t_deltas: " + transformer_delta + ", t: " + transformer_nondelta + ", intra: " + intraWorklist.size() + ", inter: " + interWorklist.size());
//			        counter = 0;
//			    }
				if((sweep && intra) || (!sweep && !intraWorklist.isEmpty())) {
//				    
//                    // organise worklist into per-method worklists
				    
                    Logger.println("e_deltas: " + entry_deltas + ", e: " + entry_nondeltas + ", t_deltas: " + transformer_delta + ", t: " + transformer_nondelta + ", intra: " + intraWorklist.size() + ", inter: " + interWorklist.size());
				    
                    final Map<SootMethod,SortedSet<Unit>> methodToWorklist = new HashMap<SootMethod, SortedSet<Unit>>();
                    for (Unit u : intraWorklist) {
                        SootMethod mm = unitToMethod.get(u);
                        SortedSet<Unit> mWorklist = methodToWorklist.get(mm);
                        if (mWorklist == null) {
                            mWorklist = constructWorklist(numbers);
                            methodToWorklist.put(mm, mWorklist);
                        }
                        mWorklist.add(u);
                    }
                    intraWorklist.clear(); // clear here as no need to keep it
//                    
                    List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
                    for (final SootMethod mm : methodToWorklist.keySet()) {
				    
                        tasks.add(new Callable<Object>(){
                            public Object call() {
                                SortedSet<Unit> worklist = methodToWorklist.get(mm);
        //				        List<Unit> worklist = intraWorklist;
                                
                                long start = System.currentTimeMillis();
                                
                                while (!worklist.isEmpty()) {
                				    Unit u = worklist.first();
                				    worklist.remove(u);
        //                            SootMethod mm = unitToMethod.get(u);
                
                                    if (methodsToCompact.contains(mm)) {
                                        methodsToComputeCommonTransformer.add(mm);
                                    }
                                    
                                    if (debug) Logger.println("");
                                    if (debug) Logger.println("");
                                    if (debug) Logger.println("Unit: " + u + " (" + StateFactory.v((Stmt)u).getNumber() + ")");
                                    if (debug) Logger.println("Method: " + unitToMethod.get(u));
                                    ITransformer t = unitToTransformer.get(u);
                                    if (debug) Logger.println("Transformer: " + t, ANSICode.FG_BLUE);

//                                    if (stats) Logger.printstats("Unit: " + u);
//                                    if (stats) Logger.printstats("Method: " + unitToMethod.get(u));
//                                    if (stats) Logger.printstats("Transformer: " + t.size());
                                    
                                    // Take meet of all successors
                                    // Step 1: determine if any have non-delta aggregates
//                                    Collection<Unit> succs = reduceCfg ? unitToJumpSuccs.get(u).keySet() : unitToSuccs.get(u);
                                    ITransformer oldExit = getResult(u, unitToExit);//unitToExit.get(u);
                                    if (debug) Logger.println("Exit (old): " + oldExit, ANSICode.FG_RED);
                                    ITransformer newExit = useDeltas ? getResult(u, unitToExitDelta) : null;//unitToExit.get(u);
                                    if (debug) Logger.println("Exit (delta): " + newExit, ANSICode.FG_RED);
                                    
//                                    if (stats) Logger.printstats("Exit (delta): " + (newExit == null ? "null" : newExit.size()));                                    
                                    
                                    boolean useDeltasThisTime = newExit != null && newExit != initialDeltaTransformer;
                                    if (useDeltasThisTime) entry_deltas.incrementAndGet(); else entry_nondeltas.incrementAndGet();
                //                    if (useDeltas) {
                //                        for (Unit s : succs) {
                //                            if (unitToEntryDelta.get(s) == null) {
                ////                                Logger.println(s + "'s delta is null", ANSICode.FG_RED);
                //                                useDeltas = false;
                //                                break;
                //                            }
                //                        }
                //                    }
                //                    else {
                ////                        Logger.println("not using deltas (1)");
                //                    }
                                    
                //                    if (useDeltas) {
                //                        Logger.println("using deltas to compute entry", ANSICode.FG_GREEN);
                //                    }
                //                    else {
                //                        Logger.println("not using deltas to compute entry", ANSICode.FG_BLUE);
                //                    }
                                    
                                    // Step 2: take meet
                                    if (newExit == null) {
                //                        Transformer newExit = useDeltas ? new DeltaTransformer() : new Transformer();
                                        newExit = newEmptyTransformer();
                                        if (reduceCfg) {
                                            boolean firstSucc = true;
                                            Map<Unit,ITransformer> jumpSuccs = unitToJumpSuccs.get(u);
                    //                        Logger.println("Succs: " + jumpSuccs.keySet());
                                            for (Unit s : jumpSuccs.keySet()) {
                                                ITransformer succEntry = null;
                                                if (storeEntry) {
                                                    succEntry = getResult(s, unitToEntry);
                                                }
                                                else {
                                                    ITransformer succExit = getResult(s, unitToExit);
                                                    if (succExit != null) {
                                                        ITransformer succT = getResult(s, unitToTransformer);
                                                        succEntry = succExit.composeWith(succT);
                                                    }
                                                }
//                                                Transformer succEntry = getResult(s, unitToEntry);//unitToEntryDelta.get(s) : unitToEntry.get(s);
                                                if (succEntry != null) {
                                                    ITransformer pathTransformer = jumpSuccs.get(s);
                                                    ITransformer succEntryTransformed = succEntry.composeWith(pathTransformer);
                                                    if (firstSucc) {
                                                        newExit.overwriteWith(succEntryTransformed);
                                                        firstSucc = false;
                                                    }
                                                    else {
                                                        newExit.unionWith(succEntryTransformed);
                                                    }
                                                }
                                            }
                                            if (!useDeltasThisTime) {
                                                newExit.cleanup();
                                            }
//                                            newExit.compact();
                                        }
                                        else {
                                            boolean firstSucc = true;
                                            for (Unit s : unitToSuccs.get(u)) {
                                                ITransformer succEntry = getResult(s, unitToEntry); //unitToEntryDelta.get(s) : unitToEntry.get(s);
                                                if (succEntry != null) { // in case we reach u before s (e.g in if (b) { ... } ; x = y; )
                                                    if (firstSucc) {
                                                        newExit.overwriteWith(succEntry);
                                                        firstSucc = false;
                                                    }
                                                    else {
                                                        newExit.unionWith(succEntry);
                                                    }
                                                }
                    //                            else {
                                                    // successor result still hasn't been computed
                                                    // therefore skip unit u (u will be added to the
                                                    // worklist again anyway)
                                                    // THIS DOESN'T WORK WHEN USING DELTAS AND WHEN IN 
                                                    // A LOOP BECAUSE INITIALLY DELTA IS NULL
                    //                                Logger.println(s + "'s entry is null, skipping " + u, ANSICode.FG_RED);
                    //                                continue outer;
                    //                            }
                                            }
                                            if (!useDeltasThisTime) {
                                                newExit.cleanup();
                                            }
                                        }
//                                        newExit.toArraySets();
                                        if (debug) Logger.println("Exit (new): " + newExit, ANSICode.FG_MAGENTA);

                                        // even if originally Æexit was null,
                                        // the new exit might be a superset of
                                        // the old exit
                                        if (useDeltas) {
                                            if (!storeEntry && oldExit != null && newExit.subsumes(oldExit)) {
                                                newExit = newExit.differenceWith(oldExit);
                                                useDeltasThisTime = true;
                                            }
                                        }
                                    }
                                    
                //                    boolean firstSucc = true;
                //                    Map<Unit,Transformer> jumpSuccs = unitToJumpSuccs.get(u);
                //                    Transformer exit2 = new Transformer();
                //                    for (Unit s : jumpSuccs.keySet()) {
                //                        Transformer succEntry = unitToEntry.get(s);
                //                        if (succEntry != null) {
                //                            Transformer pathTransformer = jumpSuccs.get(s);
                //                            Transformer succEntryTransformed = succEntry.composeWith(pathTransformer);
                //                            if (firstSucc) {
                //                                exit2.overwriteWith(succEntryTransformed);
                //                                firstSucc = false;
                //                            }
                //                            else {
                //                                exit2.unionWith(succEntryTransformed);
                //                            }
                //                        }
                //                    }
                //                    exit2.cleanup();
                
                                    // Step 3: update stored exit
                                    DeltaTransformer deltaExit = null;
//                                    int oldExitSize = oldExit == null ? 0 : oldExit.size();
//                                    int oldDeltaExitSize = newExit.size();
                                    if (useDeltasThisTime) {
                //                        deltaExit = (DeltaTransformer)newExit;
                //                        newExit = oldExit.addAll(deltaExit);
                                        deltaExit = new DeltaTransformer();
                                        newExit = oldExit.addAllReturnDelta(newExit, deltaExit);
                //                        newExit.cleanup();
                //                        oldExit.addAllModify(deltaExit);
                //                        newExit = oldExit;
                                    }
                                    //unitToExit.put(u, newExit);
                                    newExit.compact();
                                    storeResult(u, newExit, unitToExit);
                                    if (useDeltas) {
                                        storeResult(u, new DeltaTransformer(), unitToExitDelta); // reset Æexit
                                    }
                                    
//                                    if (stats) Logger.printstats("Exit (new): " + newExit.size());
                                    
                //                    outputLocalStats(u, newExit, "Exit");
                                    
                //                    int numRelevantEdges = newExit.howManyEdgesWouldBeTransformed(t);
                //                    Logger.println("newExit.size: " + newExit.size() +" relevant: " + numRelevantEdges + ", t.size: " + t.size());
                                    
                //                    Logger.println("useDeltas: " + useDeltas + ", oldExit: " + (oldExit==null ? "null" : oldExit.size()) + ", deltaExit: " + (deltaExit==null ? "null" : deltaExit.size()) + ", newExit: " + newExit.size() + ", exit2: " + exit2.size());
                //                    if (!newExit.equals(exit2)) {
                //                        Logger.println("useDeltas: " + useDeltas + ", oldExit: " + (oldExit==null ? "null" : oldExitSize) + ", deltaExit (old): " + oldDeltaExitSize + ", deltaExit (new): " + (deltaExit==null ? "null" : deltaExit.size()) + ", newExit: " + newExit.size() + ", exit2: " + exit2.size(), ANSICode.FG_RED);
                //                        ExceptionalUnitGraph cfg = CFGCache.getCFG(mm);
                //                        for (Unit u2 : cfg) {
                //                            Map<Unit,Transformer> jumpSuccs2 = unitToJumpSuccs.get(u2);
                //                            if (jumpSuccs2 != null) {
                //                                Logger.println("u: " + u2 + "(" + u2.getNumber() + ")");
                //                                for (Unit s2 : jumpSuccs2.keySet()) {
                //                                    Logger.println("(" + s2.getNumber() + ")" + s2.toString(), ANSICode.FG_GREEN);
                //                                }
                //                            }
                //                        }
                //                        ProfilerSupport.waitForKeyPress();
                //                    }
                                    // Step 3: if Æexit:
                                    //             Æentry = tn o Æexit
                                    //             newEntry = oldEntry U Æentry
                                    //         else
                                    //             newEntry = tn o newExit
                                    //             if newEntry subsumes oldEntry,
                                    //                 Æentry = newEntry - oldEntry
                                    //             else
                                    //                 Æentry = null
                                    
                                    ITransformer oldEntry = getResult(u, unitToEntry); //unitToEntry.get(u);
                                    if (debug) Logger.println("Entry (old): " + oldEntry, ANSICode.FG_RED);
                                    ITransformer newEntry = null;
                                    DeltaTransformer deltaEntry = null;
//                                    int oldEntrySize = oldEntry == null ? 0 : oldEntry.size();
                                    if (useDeltasThisTime) {
                                        deltaEntry = (u instanceof StartStmt) ? (DeltaTransformer)deltaExit.removeMethodLocalVars() : (DeltaTransformer)deltaExit.composeWith(t);
                //                        if (mm.toString().equals("<java.lang.System: java.lang.String getProperty(java.lang.String)>")) {
                //                            Set<TransformerEdge> edges = deltaEntry.getEdges("<java.security.Permission: java.lang.String name>");
                //                            if (edges != null) {
                //                                for (TransformerEdge te3 : edges) {
                //                                    if (te3.getJumpFunction() == IdentityJumpFunction.v()) {
                //                                        if (te3.getDest().toString().equals("<java.security.Permission: java.lang.String name>")) {
                //                                            Logger.println("method has the id edge in deltaEntry");
                //                                        }
                //                                    }
                //                                }
                //                            }
                //                        }
                //                        newEntry = oldEntry.addAll(deltaEntry);
                //                        newEntry.cleanup();
                //                        DeltaTransformer newDeltaEntry = newEntry.differenceWith(oldEntry);
                //                        DeltaTransformer oldDeltaEntry = (DeltaTransformer)unitToEntryDelta.get(u);
                //                        if (oldDeltaEntry != null && ((Stmt)u).containsInvokeExpr()) {
                //                            oldDeltaEntry.addAll(deltaEntry);
                //                            deltaEntry = oldDeltaEntry;
                //                        }
                                        if (storeEntry) {
                                            DeltaTransformer newDeltaEntry = new DeltaTransformer();
                                            newEntry = oldEntry.addAllReturnDelta(deltaEntry, newDeltaEntry);
                                            // debugging
                    //                        if (!newDeltaEntry.equals(deltaEntry)) {
                    //                            Logger.println("--- newDeltaEntry does not equal deltaEntry", ANSICode.FG_RED);
                    //                        }
                                            deltaEntry = newDeltaEntry;
                                        }
                //                        deltaEntry = oldEntry.addAllModifyReturnDelta(deltaEntry);
                //                        newEntry = oldEntry;
                                    }
                                    else {
                                        if (storeEntry) {
                                            newEntry = (u instanceof StartStmt) ? newExit.removeMethodLocalVars() : newExit.composeWith(t);
                                            newEntry.cleanup();
                                            if (useDeltas) {
                                                if (oldEntry != null && newEntry.subsumes(oldEntry)) {
                                                    deltaEntry = (DeltaTransformer)newEntry.differenceWith(oldEntry);
                                                }
                                                else {
                                                    deltaEntry = null;
                                                }
                                            }
                                        }
                                        else {
                                            deltaEntry = null;
                                        }
                                    }
                                    
                                    
                //                    Transformer tmpEntry = (u instanceof StartStmt) ? exit2.removeMethodLocalVars() : exit2.composeWith(t);
                //                    if (!newEntry.equals(tmpEntry)) {
                //                        Logger.println("useDeltas: " + useDeltas + ", t o exit2: " + tmpEntry.size() + ", oldEntry: " + oldEntrySize + ", newEntry: " + newEntry.size(), ANSICode.FG_RED);
                //                        ProfilerSupport.waitForKeyPress();
                //                    }
                //                    outputLocalStats(u, newExit, "Entry");
                //                    Transformer newEntry2 = newEntry.clone();
                //                    Transformer newEntry3 = newEntry2.removeDeadEdges();
                //                    Logger.println("newEntry.size: " + newEntry.size() + ", newEntry3.size: " + newEntry3.size());
                
                //                    if (mm.toString().equals("<java.lang.System: java.lang.String getProperty(java.lang.String)>")) {
                //                        Set<TransformerEdge> edges = newEntry.getEdges("<java.security.Permission: java.lang.String name>");
                //                        if (edges != null) {
                //                            for (TransformerEdge te3 : edges) {
                //                                if (te3.getJumpFunction() == IdentityJumpFunction.v()) {
                //                                    if (te3.getDest().toString().equals("<java.security.Permission: java.lang.String name>")) {
                //                                        Logger.println("method has the id edge in newEntry");
                //                                    }
                //                                }
                //                            }
                //                        }
                //                    }
                //                    if (deltaEntry != null && mm.toString().equals("<java.lang.System: java.lang.String getProperty(java.lang.String)>")) {
                //                        Set<TransformerEdge> edges = deltaEntry.getEdges("<java.security.Permission: java.lang.String name>");
                //                        if (edges != null) {
                //                            for (TransformerEdge te3 : edges) {
                //                                if (te3.getJumpFunction() == IdentityJumpFunction.v()) {
                //                                    if (te3.getDest().toString().equals("<java.security.Permission: java.lang.String name>")) {
                //                                        Logger.println("method has the id edge in deltaEntry (2)");
                //                                    }
                //                                }
                //                            }
                //                        }
                //                    }                    
                //                    Transformer entry2 = (u instanceof StartStmt) ? exit2.removeMethodLocalVars() : exit2.composeWith(t);
                //                    entry2.cleanup();
                //                    Logger.println("useDeltas: " + useDeltas + ", oldEntry: " + (oldEntry==null ? "null" : oldEntry.size()) + ", newEntry: " + newEntry.size() + ", deltaEntry: " + (deltaEntry==null ? "null" : deltaEntry.size()) + ", entry2: " + entry2.size());
                //                    if (!newEntry.equals(entry2)) {
                //                        ProfilerSupport.waitForKeyPress();
                //                    }
                //                    
                //                    unitToEntry.put(u, newEntry);
                //                    unitToEntryDelta.put(u, deltaEntry);
                                    
                                    if (storeEntry) {
                                        newEntry.compact();
                                        storeResult(u, newEntry, unitToEntry);
                                    }
//                                    storeResult(u, deltaEntry, unitToEntryDelta);
                                    
                                    if (u instanceof StartStmt) {
                                        if (!storeEntry) {
                                            newEntry = newExit.removeMethodLocalVars();
                                            newEntry.compact();
                                        }
                                        SootMethod m = startUnitToMethod.get(u);
                                        methodToSummary.put(m, newEntry);
                                        // Summary deltas accumulate, however, if it has been
                                        // set to null in the current round of updates 
                                        // (due to a deletion), it must remain null so that 
                                        // callers get the full transformer
                                        
                //                        DeltaTransformer oldSummaryDelta = (DeltaTransformer)methodToSummaryDelta.get(m);
                //                        DeltaTransformer newSummaryDelta = null;
                //                        
                //                        // if oldSummaryDelta is null, it stays null
                //                        if (oldSummaryDelta != null) {
                //                            if (deltaEntry == null) {
                //                                newSummaryDelta = null;
                //                            }
                //                            else {
                //                                newSummaryDelta = (DeltaTransformer)oldSummaryDelta.addAll(deltaEntry);
                //                            }
                //                            if (newSummaryDelta == null) {
                //                                Logger.println(m.toString() + ": setting summaryDelta to null");
                //                            }
                //                            else {
                //                                Logger.println(m.toString() + ": setting summaryDelta to non-null");
                //                            }
                //                            methodToSummaryDelta.put(m, newSummaryDelta);
                //                        }
                                    }
                                    
                                    if (debug) Logger.println("Entry (new): " + newEntry, ANSICode.FG_MAGENTA);
                                    if (debug) Logger.println("Entry (delta): " + deltaEntry, ANSICode.FG_MAGENTA);

//                                    if (stats) Logger.printstats("Entry (new): " + newEntry.size());
//                                    if (stats) Logger.printstats("Entry (delta): " + (deltaEntry == null ? "null" : deltaEntry.size()));                                    
                                    
                                    // Step 4: If a change occurred, put preds onto worklist
                                    if (useDeltas) {
                                        if (deltaEntry == null || !deltaEntry.isEmpty()) {
                    
                                            if (u instanceof EndStmt) {
                                                deltaEntry = new DeltaTransformer();
                    //                          unitToEntryDelta.put(u, deltaEntry);
    //                                            storeResult(u, deltaEntry, unitToEntryDelta);
                                            }
                                            
                                            if (u instanceof StartStmt) {
                                                // method entry
                                                SootMethod m = startUnitToMethod.get(u);
                                                List<Unit> callers = calleeToCallers.get(m);
                                                if (callers != null) {
                                                    for (Unit caller : callers) {
                                                        if (caller == null) {
                                                            Logger.println("caller is null!");
                                                            Logger.println("m: " + mm);
                                                            Logger.println("callers: " + callers);
                                                        }
                                                        synchronized(caller) {
                                                            synchronized(interWorklist) {
                                                                if (!interWorklist.contains(caller)) {
                                                                    interWorklist.add(caller);
                                                                }
                                                            }
                                                            // update caller's delta
                                                            if (deltaEntry == null) {
                        //                                        unitToTransformerDelta.put(caller, null);
                        //                                        Logger.println(m + " is setting caller's deltaT to null");
                                                                storeResult(caller, null, unitToTransformerDelta);
                                                            }
                                                            else {
                                                                DeltaTransformer deltaT = (DeltaTransformer)getResult(caller, unitToTransformerDelta); //unitToTransformerDelta.get(caller);
                                                                if (deltaT != null) {
                                                                    // if delta is null, it stays null until it is reset
                                                                    DeltaTransformer newDeltaT = (DeltaTransformer)deltaT.addAll(deltaEntry);
                                                                    storeResult(caller, newDeltaT, unitToTransformerDelta);
                        //                                            deltaT.addAllModify(deltaEntry);
                                                                    
                                                                    //boolean found = false;
                        //                                            if (mm.toString().equals("<java.lang.System: java.lang.String getProperty(java.lang.String)>")) {
                        //                                                Logger.println("Updating deltaT for " + caller);
                        //                                                Set<TransformerEdge> edges = newDeltaT.getEdges("<java.security.Permission: java.lang.String name>");
                        //                                                if (edges != null) {
                        //                                                    for (TransformerEdge te3 : edges) {
                        //                                                        if (te3.getJumpFunction() == IdentityJumpFunction.v()) {
                        //                                                            if (te3.getDest().toString().equals("<java.security.Permission: java.lang.String name>")) {
                        //                                                                found = true;
                        //                                                                Logger.println("id edge is in newDeltaT");
                        //                                                            }
                        //                                                        }
                        //                                                    }
                        //                                                }
                        //                                                if (!found) {
                        //                                                    Logger.println("id edge not found");
                        //                                                }
                        //                                            }
                                                                    //unitToTransformerDelta.put(caller, newDeltaT);
                                                                    
                                                                }
                                                                else {
                        //                                            Logger.println(m + "'s caller's deltaT is null");
                                                                }
                                                            }
                                                        }
                                                        
                    //                                    SootMethod callerMethod = unitToMethod.get(caller);
                    //                                    if (!callerMethodsToPropagate.contains(callerMethod)) {
                    //                                        callerMethodsToPropagate.add(callerMethod);
                    //                                    }
                                                    }
                    //                                callersToBeUpdated.put(m, callers);
                                                }
                                            }
                                            else {
                                                List<Unit> preds = reduceCfg ? unitToJumpPreds.get(u) : unitToPreds.get(u);
                    //                            boolean addU = false; // add u last
                                                if (preds == null) {
                                                    Logger.println("preds null --> u: " + u + " of " + mm);
                                                }
                                                for (Unit p : preds) { // no need to sync on p as this implementation is per-method single-threaded
                    //                                if (p == u) {
                    //                                    addU = true;
                    //                                }
                                                    if (!worklist.contains(p)) {
                                                        worklist.add(p);
                                                    }
                                                    ITransformer predDeltaExit = getResult(p, unitToExitDelta);
                                                    if (predDeltaExit != null) { // if null, leave null. will be reset when p is processed
                                                        Map<Unit,ITransformer> predSuccTransformers = unitToJumpSuccs.get(p);
                                                        ITransformer predSuccTransformer = reduceCfg ? predSuccTransformers.get(u) : null;
                                                        if (deltaEntry == null) {
                                                            storeResult(p, null, unitToExitDelta);
                                                        }
                                                        else {
                                                            ITransformer tmp = reduceCfg ? deltaEntry.composeWith(predSuccTransformer) : deltaEntry;
                                                            ITransformer newPredDeltaExit = predDeltaExit.addAll(tmp);
                                                            storeResult(p, newPredDeltaExit, unitToExitDelta);
                                                        }
                                                    }
                                                }
                    //                            if (addU) {
                    //                                // add to the end
                    //                                intraWorklist.remove(u); // (in case already in list)
                    //                                intraWorklist.add(u);
                    //                            }
                                            }
                                        }
                                    }
                                    else {
                                        if (oldEntry == null || !newEntry.equals(oldEntry)) {
                                            if (u instanceof StartStmt) {
                                                // method entry
                                                SootMethod m = startUnitToMethod.get(u);
                                                List<Unit> callers = calleeToCallers.get(m);
                                                if (callers != null) {
                                                    for (Unit caller : callers) {
                                                        synchronized(interWorklist) {
                                                            if (!interWorklist.contains(caller)) {
                                                                interWorklist.add(caller);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                            else {
                                                List<Unit> preds = reduceCfg ? unitToJumpPreds.get(u) : unitToPreds.get(u);
                                                for (Unit p : preds) { // no need to sync on p as this implementation is per-method single-threaded
                                                    if (!worklist.contains(p)) {
                                                        worklist.add(p);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    
        //                            if (debug) Logger.println("Entry: " + newEntry, ANSICode.FG_MAGENTA);
        //                            if (intraWorklist.isEmpty()) {
        //        //                        Logger.println("Switching to inter", ANSICode.FG_BLUE);
        //                                intra = false;
        //                            }
                                    if(debug) ProfilerSupport.waitForKeyPress(); // single-step
                                
                                    if (stats) {
                                        int exitSize = newExit.size();
                                        int exitLocalCount = newExit.countLocalAccesses();
                                        int exitXCount = 0;
                                        if (u instanceof AssignStmt) {
                                            Local x = (Local)((AssignStmt)u).getLeftOp();
                                            exitXCount = newExit.countLocalAccesses(x);
                                        }
                                        int entrySize = newEntry.size();
                                        int entryLocalCount = newEntry.countLocalAccesses();
                                        int tSize = t.size();
                                        int exit_live = newExit.clone().removeDeadEdges().size();
                                        int entry_live = newEntry.clone().removeDeadEdges().size();
                                        Logger.printstats("**************************");
                                        Logger.printstats("u: " + u);
                                        Logger.printstats("m: " + mm);
                                        Logger.printstats(String.format("%d (exit: %d %d %d, entry: %d %d, t: %d)", (exitSize + entrySize + tSize), exitSize, exitLocalCount, exitXCount, entrySize, entryLocalCount, tSize));
                                        Logger.printstats(String.format("%d (exit_live: %d, entry_live: %d", (exit_live + entry_live + tSize), exit_live, entry_live));
                                    }
                                }
                                
                                long took = System.currentTimeMillis()-start;
                                AnalysisTimer.addForIntra(took, mm);
                                
                                return null;
                            }
                        });
                    }
                    
//                    for (Callable<Object> ca : tasks) {
//                        try {
//                            ca.call();
//                        }
//                        catch (Exception e) {
//                            throw new RuntimeException(e);
//                        }
//                    }
                    
                    try {
                        AtomicTransformer.POOL.invokeAll(tasks);
                    }
                    catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                    
                    intra = false;
                }
				else {
				    
				    Logger.println("e_deltas: " + entry_deltas + ", e: " + entry_nondeltas + ", t_deltas: " + transformer_delta + ", t: " + transformer_nondelta + ", intra: " + intraWorklist.size() + ", inter: " + interWorklist.size());
				    
				    if (entry_nondeltas.intValue() == startCompaction && !methodsToComputeCommonTransformer.isEmpty() && ++compactionCounter == AtomicTransformer.COMPACT_EVERY) {
				        compactExits(methodsToComputeCommonTransformer);
				        if (AtomicTransformer.COMPACT_SUMMARIES) {
				            compactSummaries(c);
				        }
				        methodsToComputeCommonTransformer.clear();
				        compactionCounter = 0;
				        
				    }
				    
//                    if (entry_nondeeltas.intValue() == startCompaction && ++compactionCounter == AtomicTransformer.COMPACT_EVERY) {
//                        compactExitsAcrossComponent(c);
//                        compactionCounter = 0;
//                    }				    
//				        Logger.println("    performing compaction for " + methodsToComputeCommonTransformer.size() + " methods", ANSICode.FG_BLUE);
//				        long startCompactTime = System.currentTimeMillis();
//				        List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
//				        for (final SootMethod m : methodsToComputeCommonTransformer) {
//				            tasks.add(new Callable<Object>() {
//				                public Object call() {
//        				            ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
//        				            Transformer common = new Transformer();
//        				            boolean first = true;
//        				            for (Unit u : cfg) {
//        				                Transformer entry = unitToEntry.get(u);
//        				                if (entry != null) {
//        				                    if (first) {
//        				                        common.overwriteWith(entry);
//        				                        first = false;
//        				                    }
//        				                    else {
//        				                        common.retainAll(entry);
//        				                    }
//        				                }
//        				            }
//        				            // now re-calculate entry transformers
//        				            // by taking difference with "common"
//        				            for (Unit u : cfg) {
//        				                Transformer entry = unitToEntry.get(u);
//        				                if (entry != null) {
//        				                    entry.differenceWithInPlace(common);
//        				                }
//        				            }
//        				            return null;
//				                }
//				            });
//				        }
//				        
//				        try {
//				            AtomicTransformer.POOL.invokeAll(tasks);
//				        }
//				        catch (Exception e) {
//				            throw new RuntimeException(e);
//				        }
//				        
//				        methodsToComputeCommonTransformer.clear();
//				        compactionCounter = 0;
//				        
//				        long took = System.currentTimeMillis() - startCompactTime;
//				        Logger.println("    took " + String.format("%.2f", (took/1000.0)) + " secs", ANSICode.FG_BLUE);
//				    }

				    List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
				    for (final Unit u : interWorklist) {
				        tasks.add(new Callable<Object>() {
				            public Object call() {
            //                    Unit u = interWorklist.remove(0);
                                SootMethod mm = unitToMethod.get(u);
                                long start = System.currentTimeMillis();
            //                    Logger.println(u.toString(), ANSICode.FG_MAGENTA);
            //                    Logger.println(mm.toString(), ANSICode.FG_MAGENTA);
                                if (debug) Logger.println("");
                                if (debug) Logger.println("");
                                if (debug) Logger.println("Unit: " + u + " (" + StateFactory.v((Stmt)u).getNumber() + ")");
                                if (debug) Logger.println("Method: " + unitToMethod.get(u));
                                // u contains an invoke stmt
                                // Calculate meet of all target methods to give tm and apply
                                // tm to current exit transformer
                                
                                // Step 1: are we using deltas or full transformers?
            //                    List<SootMethod> targets = callerToCallees.get(u);
                                ITransformer oldT = getResult(u, unitToTransformer);//unitToTransformer.get(u);
                                if (debug) Logger.println("T (old): " + oldT, ANSICode.FG_RED);
                                ITransformer newT = null;
                                DeltaTransformer deltaT = useDeltas ? (DeltaTransformer)getResult(u, unitToTransformerDelta) : null; //unitToTransformerDelta.get(u);
                                if (debug) Logger.println("T (delta): " + deltaT, ANSICode.FG_RED);
            //                    for (SootMethod target : targets) {
            //                        if (methodToSummaryDelta.get(target) == null) {
            //                            Logger.println(target.toString() + "'s summaryDelta is null", ANSICode.FG_RED);
            //                            useDeltas = false;
            //                            break;
            //                        }
            //                    }
            //                    Transformer t2 = new Transformer();
            //                    boolean fTarget = true;
            //                    for (SootMethod target : callerToCallees.get(u)) {
            //                        Transformer summary2 = methodToSummary.get(target);
            //                        Set<TransformerEdge> edges = summary2.getEdges("<java.security.Permission: java.lang.String name>");
            //                        if (edges != null) {
            //                            for (TransformerEdge te3 : edges) {
            //                                if (te3.getJumpFunction() == IdentityJumpFunction.v()) {
            //                                    if (te3.getDest().toString().equals("<java.security.Permission: java.lang.String name>")) {
            //                                        Logger.println(target.toString() + " has the id edge");
            //                                    }
            //                                }
            //                            }
            //                        }
            //                        if (fTarget) {
            //                            t2.overwriteWith(summary2);
            //                            fTarget = false;
            //                        }
            //                        else {
            //                            t2.unionWith(summary2);
            //                        }
            //                    }
            //                    t2 = t2.calleeToCallerContext(callToParamsArgs.get(u));
            //                    Logger.println("starting cleanup");
            //                    t2.cleanup();
            //                    Logger.println("finished");
            
            //                    int newTSizeBeforeCleanup = -1;
                                if (deltaT == null) transformer_nondelta.incrementAndGet(); else transformer_delta.incrementAndGet();
                                if (deltaT == null) {
            //                        Logger.println("Using non-deltas to compute transformer", ANSICode.FG_BLUE);
                                    //newT = unitToLowerTransformer.get(u);
                                    newT = newEmptyTransformer();
                                    boolean firstTarget = true;
                                    for (SootMethod target : callerToCallees.get(u)) {
                                        ITransformer summary = methodToSummary.get(target);
                                        if (firstTarget) {
                                            newT.overwriteWith(summary);
                                            firstTarget = false;
                                        }
                                        else {
                                            newT.unionWith(summary);
                                        }
                //                        List<Unit> targetCallers = callersToBeUpdated.get(target);
                //                        // if targetCallers is null, then target is in another
                //                        // component or their summary hasn't been updated yet
                ////                        if (targetCallers == null && c.contains(target)) {
                ////                            throw new RuntimeException("targetCallers is null but target is in current component!");
                ////                        }
                //                        if (targetCallers != null) {
                //                            targetCallers.remove(u);
                //                            if (targetCallers.isEmpty()) {
                //                                methodToSummaryDelta.put(target, new DeltaTransformer());
                //                            }
                //                        }
                                    }
            //                        newT.toArraySets();
                                    newT = newT.calleeToCallerContext(callToParamsArgs.get(u));
                                    newT.cleanup();
//                                    newT.compact();
                                    // optimisation
                                    if (useDeltas && !storeEntry && oldT != null && newT.subsumes(oldT)) {
                                        deltaT = (DeltaTransformer)newT.differenceWith(oldT);
                                        deltaT.compact();
                                    }
                                }
                                else if (useDeltas) {
            //                        Logger.println("Using deltas to compute transformer", ANSICode.FG_GREEN);
                                    // PROBLEMATIC W.R.T. ALIASING (requires composeWith* to be pure) 
                                    deltaT = (DeltaTransformer)deltaT.calleeToCallerContext(callToParamsArgs.get(u));
            //                        newT = oldT.addAll(deltaT);
            ////                        newT.cleanup();
            //                        // recompute delta as a lot of the time it is smaller
            //                        deltaT = newT.differenceWith(oldT);
            //                        deltaT = oldT.addAllModifyReturnDelta(deltaT);
            //                        newT = oldT;
                                    DeltaTransformer newDeltaT = new DeltaTransformer();
                                    newT = oldT.addAllReturnDelta(deltaT, newDeltaT);
                                    deltaT = newDeltaT;
                                    deltaT.compact();
                                }
            
                                
            //                    Logger.println("oldT: " + (oldT == null ? "null" : oldT.size()) + ", newTBeforeCleanup: " + newTSizeBeforeCleanup + ", newT: " + newT.size() + ", deltaT: " + (deltaT == null ? "null" : deltaT.size()) + ", t2: " + t2.size(), ANSICode.FG_MAGENTA);
                                
            //                    if (!newT.equals(t2)) {
            //                        Logger.println("diff1: " + newT.differenceWith(t2), ANSICode.FG_MAGENTA);
            //                        Logger.println("diff2: " + t2.differenceWith(newT), ANSICode.FG_MAGENTA);
            //                        Logger.println("newT: " + newT.getEdges("<java.security.Permission: java.lang.String name>"), ANSICode.FG_MAGENTA);
            //                        Logger.println("t2: " + t2.getEdges("<java.security.Permission: java.lang.String name>"), ANSICode.FG_MAGENTA);
            //                        
            //                        ProfilerSupport.waitForKeyPress();
            //                    }
                                
                                if (debug) Logger.println("T (new): " + newT, ANSICode.FG_MAGENTA);
            
            //                    if (useDeltas) {
            //                        Logger.println("Computing transfer func from deltas", ANSICode.FG_GREEN);
            //                        deltaT = (DeltaTransformer)t;
            //                        newT = oldT.addAll(deltaT); // using deltas, so oldT cannot be null
            ////                        if (!newT.subsumes(oldT)) {
            ////                            Logger.errprintln("newT does not subsume oldT!", ANSICode.FG_RED);
            ////                            ProfilerSupport.waitForKeyPress();
            ////                        }
            ////                        DeltaTransformer newDeltaT = newT.differenceWith(oldT); 
            //                        // debugging
            ////                        if (!newDeltaT.equals(deltaT)) {
            ////                            Logger.errprintln("--- newDeltaT does not equal deltaT", ANSICode.FG_RED);
            ////                        }
            ////                        deltaT = newDeltaT;
            //    
            //                        // test that newT is the same as what would have been obtained if we
            //                        // took the full meet.
            ////                        if (!newT.equals(t2)) {
            ////                            Logger.println("delta and non-delta transfer func are not the same!", ANSICode.FG_RED);
            ////                            Logger.println("u: " + u, ANSICode.FG_RED);
            ////                            Logger.println("m: " + unitToMethod.get(u), ANSICode.FG_RED);
            ////                            Logger.println("targets: " + callerToCallees.get(u), ANSICode.FG_RED);
            ////                        }
            //                    }
            //                    else {
            //                        Logger.println("Computing transfer func from non-deltas", ANSICode.FG_BLUE);
            //                        newT = t;
            //                        if (oldT != null && newT.subsumes(oldT)) {
            //                            deltaT = newT.differenceWith(oldT);
            //                        }
            //                        else {
            //                            deltaT = null;
            //                        }
            //                    }
            
            //                    unitToTransformer.put(u, newT);
                                newT.compact();
                                storeResult(u, newT, unitToTransformer);
                                //                    unitToTransformerDelta.put(u, deltaT);
                                
                                int exitSize = 0;
                                int entrySize = 0;

                                if (useDeltas) {
                                    if (deltaT == null || !deltaT.isEmpty()) {
                
                                        ITransformer oldEntry = getResult(u, unitToEntry); //unitToEntry.get(u);
                                        ITransformer newEntry = null;
                                        ITransformer deltaEntry = null;
                                        ITransformer exit = getResult(u, unitToExit); //unitToExit.get(u);
                                        if (stats) exitSize = exit.size();
                                        
                                        if (debug) Logger.println("Exit: " + exit, ANSICode.FG_RED);
                                        if (debug) Logger.println("Entry (old): " + oldEntry, ANSICode.FG_RED);
                                        if (deltaT == null) {
                                            // t o e
                                            if (storeEntry) {
                                                if (exit == null) {
                                                    Logger.println("exit null");
                                                    Logger.println("u: " + u);
                                                    Logger.println("m: " + mm);
                                                    Logger.println("entry: " + oldEntry);
                                                }
                                                newEntry = exit.composeWith(newT);
                                                if (newEntry.subsumes(oldEntry)) {
                                                    deltaEntry = newEntry.differenceWith(oldEntry);
                                                }
                                                else {
                                                    deltaEntry = null;
                                                }
                                            }
                                            else {
                                                deltaEntry = null;
                                            }
                                        }
                                        else {
                                            // Æt o e
                                            deltaEntry = deltaT.composeWithAbove((Transformer)exit);
                //                            newEntry = oldEntry.addAll(deltaEntry);
                //                            newEntry.cleanup();
                //                            deltaEntry = newEntry.differenceWith(oldEntry); // improves performance a lot
                                            if (storeEntry) {
                                                DeltaTransformer newDeltaEntry = new DeltaTransformer();
                                                newEntry = oldEntry.addAllReturnDelta(deltaEntry, newDeltaEntry);
                                                deltaEntry = newDeltaEntry;
                                            }
                //                            deltaEntry = oldEntry.addAllModifyReturnDelta(deltaEntry);
                //                            newEntry = oldEntry;
                                        }
                                        if (storeEntry) {
                                            newEntry.compact();
                                        }
                                        if (deltaEntry != null) deltaEntry.compact();
                                        if (stats) entrySize = newEntry == null ? 0 : newEntry.size();
                //                        unitToEntry.put(u, newEntry);
                //                        unitToEntryDelta.put(u, deltaEntry);
                                        if (storeEntry) {
                                            storeResult(u, newEntry, unitToEntry);
                                        }
                                        
                                        if (debug) Logger.println("Entry (new): " + newEntry, ANSICode.FG_MAGENTA);
                                        if (debug) Logger.println("Entry (delta): " + deltaEntry, ANSICode.FG_MAGENTA);
    //                                    storeResult(u, deltaEntry, unitToEntryDelta);
                                          
                                        if (deltaEntry == null || !deltaEntry.isEmpty()) {
                                            List<Unit> preds = reduceCfg ? unitToJumpPreds.get(u) : unitToPreds.get(u);
                //                            boolean addU = false;
                //                            for (Unit p : preds) {
                //                                if (p == u) {
                //                                    addU = true;
                //                                }
                //                                else if (!intraWorklist.contains(p)) {
                //                                    intraWorklist.add(p);
                //                                }
                //                            }
                //                            if (addU) {
                //                                intraWorklist.add(u);
                //                            }
                //                            
                //                            // the following "if" ensures that when the 
                //                            // if(intra) line is uncommented, u's deltaEntry 
                //                            // is not overwritten before all u's preds have 
                //                            // read it (achieved by moving u to after preds
                //                            // in intra
                //                            if (sweep && deltaEntry != null) {
                //                                if (intraWorklist.contains(u)) {
                //                                    intraWorklist.remove(u); 
                //                                    intraWorklist.add(u);
                //                                }
                //                            }
                                            for (Unit p : preds) {
                                                synchronized(p) {
                                                    synchronized(intraWorklist) {
                                                        if (!intraWorklist.contains(p)) {
                                                            intraWorklist.add(p);
                                                        }
                                                    }
                                                    ITransformer predDeltaExit = getResult(p, unitToExitDelta);
                                                    if (predDeltaExit != null) { // if null, leave null. will be reset when p is processed
                                                        Map<Unit,ITransformer> predSuccTransformers = unitToJumpSuccs.get(p);
                                                        ITransformer predSuccTransformer = reduceCfg ? predSuccTransformers.get(u) : null;
                                                        if (deltaEntry == null) {
                                                            storeResult(p, null, unitToExitDelta);
                                                        }
                                                        else {
                                                            ITransformer tmp = reduceCfg ? deltaEntry.composeWith(predSuccTransformer) : deltaEntry;
                                                            ITransformer newPredDeltaExit = predDeltaExit.addAll(tmp);
                                                            storeResult(p, newPredDeltaExit, unitToExitDelta);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                else {
                                    if (oldT == null || !newT.equals(oldT)) {
                                        synchronized (intraWorklist) {
                                            if (!intraWorklist.contains(u)) {
                                                intraWorklist.add(u);
                                            }
                                        }
                                    }
                                }
            //                    else if (!deltaT.isEmpty()) {
            //                        // Æt o e
            //                        Transformer exit = unitToExit.get(u);
            //                        if (exit != null) {
            //                            Transformer oldEntry = unitToEntry.get(u);
            //                            Transformer newEntry = null;
            //                            Transformer deltaEntry = null;
            //                            // Æt o e
            //                            //deltaEntry = exit.composeWith(deltaT);
            //                            deltaEntry = deltaT.composeWithAbove(exit);
            //                            newEntry = oldEntry.addAll(deltaEntry);
            //                            deltaEntry = newEntry.differenceWith(oldEntry); // improves performance a lot
            //                            
            //                            unitToEntry.put(u, newEntry);
            //                            unitToEntryDelta.put(u, deltaEntry);
            //                            
            //                            if (!deltaEntry.isEmpty()) {
            //                                List<Unit> preds = reduceCfg ? unitToJumpPreds.get(u) : unitToPreds.get(u);
            //                                for (Unit p : preds) {
            //                                    if (!intraWorklist.contains(p)) {
            //                                        intraWorklist.add(p);
            //                                    }
            //                                }
            //                            }
            //                        }
            //                    }
                                
                                // reset transformer delta
            //                    unitToTransformerDelta.put(u, new DeltaTransformer());
                                if (useDeltas) {
                                    storeResult(u, new DeltaTransformer(), unitToTransformerDelta);
                                }
                                if (debug) ProfilerSupport.waitForKeyPress();
        //                        if (interWorklist.isEmpty()) {
        //    //                        Logger.println("Switching to intra", ANSICode.FG_BLUE);
        //                            intra = true;
        //                        }
                                if (stats) {
                                    int tSize = newT.size();
                                    Logger.printstats("**************************");
                                    Logger.printstats("u: " + u);
                                    Logger.printstats("m: " + mm);
                                    Logger.printstats(String.format("%d (exit: %d, entry: %d, t: %d)", (exitSize + entrySize + tSize), exitSize, entrySize, tSize));
                                }
                                
                                long took = System.currentTimeMillis()-start;
                                AnalysisTimer.addForInter(took, mm);
                                
                                return null;
				            }
				        });
				    }
				    
				    try {
				        AtomicTransformer.POOL.invokeAll(tasks);
				    }
				    catch (InterruptedException ie) {
				        throw new RuntimeException(ie);
				    }
				    
//				    for (Callable<Object> ca : tasks) {
//				        try {
//				            ca.call();
//				        }
//				        catch (Exception e) {
//				            throw new RuntimeException(e);
//				        }
//				    }
				    
				    interWorklist.clear();
				    intra = true;
				}
				
				
				// compact transformers
//				if (AtomicTransformer.COMPACT) {
//    				List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
//    				for (final Unit u : unitToEntry.keySet()) {
//    				    tasks.add(new Callable<Object>() {
//                            public Object call() throws Exception {
//                                Transformer entry = unitToEntry.get(u);
//                                entry.compact();
//                                Transformer exit = unitToExit.get(u);
//                                exit.compact();
//                                return null;
//                            }
//    				    });
//    				}
//    				
//    				try {
//    				    AtomicTransformer.POOL.invokeAll(tasks);
//    				}
//    				catch (InterruptedException ie) {
//    				    throw new RuntimeException(ie);
//    				}
//				}
			}

//			Logger.println("intra: " + intraWorklist.size() + ", inter: " + interWorklist.size());
			
			if (AtomicTransformer.INTERMEDIATE_RESULTS) {
			    Logger.println("* Finished analysis in " + (System.currentTimeMillis()-startTime)/1000.0 + " seconds");
			}

			Logger.println("Removing dead edges");
            List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
			long startRemoveDeadEdges = System.currentTimeMillis();
			if (c.size() > 1) {
    			for (final SootMethod m : c) {
    			    tasks.add(new Callable<Object>() {
    			        public Object call() {
    			            ITransformer summary = methodToSummary.get(m);
    			            methodToSummary.put(m, summary.removeDeadEdges());
    			            return null;
    			        }
    			    });
    			}

    			try {
    			    AtomicTransformer.POOL.invokeAll(tasks);
    			}
    			catch (InterruptedException ie) {
    			    throw new RuntimeException(ie);
    			}
    			
    			// compact summaries
    			if (AtomicTransformer.COMPACT_SUMMARIES) {
    			    compactSummaries(c);
    			}
			}
			else {
			    for (SootMethod m : c) {
			        ITransformer summary = methodToSummary.get(m);
			        methodToSummary.put(m, summary.removeDeadEdges());
			    }
			}
			long took = System.currentTimeMillis() - startRemoveDeadEdges;
			Logger.println(String.format("Took %.2f seconds", took/1000.0));
			
//			outputDot(c);
			
			// remove dead (i.e. non-reachable NFA) edges from all summaries
			// and reset summary deltas to id
//			List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
//			for (final SootMethod m : c) {
//			    tasks.add(new Callable<Object>() {
//			        public Object call() {
//        			    Transformer summary = methodToSummary.get(m);
//        			    Logger.println(m + ": " + summary.size());
//        			    methodToSummary.put(m, summary.removeDeadEdges());
//        			    return null;
//			        }
//			    });
////			    methodToSummaryDelta.put(m, new DeltaTransformer());
//			}
//			
//            try {
//                AtomicTransformer.POOL.invokeAll(tasks);
//            }
//            catch (InterruptedException ie) {
//                throw new RuntimeException(ie);
//            }
			
//			calculateCommonExitEdges(c);
//			calculateCommonExitEdgesAcrossComponent(c);
			calculateCommonSummaryEdges(c);
			
			
			if (AtomicTransformer.INTERMEDIATE_RESULTS)
			    Logger.println("");
			
			clear();
		}		
	}
	
//    private Transformer compactSummaries(Component c) {
//        Logger.println("    compacting summaries");
//        Transformer common = new Transformer();
//        boolean first = true;
//        for (SootMethod m : c) {
//            Transformer summary = methodToSummary.get(m);
//            if (first) {
//                common.overwriteWith(summary);
//                first = false;
//            }
//            else {
//                common.retainAll(summary);
//            }
//        }
//        
//        Logger.println("    " + common.size() + " edges in common");
//        
//        // now re-calculate summaries
//        // by taking difference with "common"
//        for (SootMethod m : c) {
//            Transformer summary = methodToSummary.get(m);
//            summary.differenceWithInPlace(common);
//        }
//        
//        return common;
//    }


    protected SortedSet<Unit> constructWorklist(final Map<Unit, Integer> numbers) {
        if (AtomicTransformer.ORDER_WORKLISTS) {
            return new TreeSet<Unit>(new Comparator<Unit>() {
                public int compare(Unit o1, Unit o2) {
                    Integer i1 = numbers.get(o1);
                    Integer i2 = numbers.get(o2);
                    return (i1.intValue() - i2.intValue());
                }
            });
        }
        else {
            return new SortedSetList<Unit>();
        }
    }
    
    private void compactExits(Set<SootMethod> methodsToComputeCommonTransformer) {
      Logger.println("    performing compaction for " + methodsToComputeCommonTransformer.size() + " methods", ANSICode.FG_BLUE);
      long startCompactTime = System.currentTimeMillis();
      final AtomicInteger commonEdgeCount = new AtomicInteger(0);
      List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
      for (final SootMethod m : methodsToComputeCommonTransformer) {
          tasks.add(new Callable<Object>() {
              public Object call() {
                  ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
                  ITransformer common = newEmptyTransformer();
                  List<Unit> exitsToCompact = new ArrayList<Unit>();
                  List<Unit> transformersToCompact = new ArrayList<Unit>();
                  boolean first = true;
                  for (Unit u : cfg) {
                      // check that succ is not only endstmt
                      Map<Unit,ITransformer> jumpSuccs = unitToJumpSuccs.get(u);
                      if (jumpSuccs != null) {
                          boolean onlySuccIsEnd = true;
                          for (Unit s : jumpSuccs.keySet()) {
                              if (!(s instanceof EndStmt)) {
                                  onlySuccIsEnd = false;
                              }
                          }
                          if (!onlySuccIsEnd) {
                              exitsToCompact.add(u);
                              ITransformer exit = unitToExit.get(u);
                              if (first) {
                                  common.overwriteWith(exit);
                                  first = false;
                              }
                              else {
                                  common.retainAll(exit);
                              }
                          }
                          ITransformer t = unitToTransformer.get(u);
                          if (first) {
                              common.overwriteWith(t);
                              first = false;
                          }
                          else {
                              common.retainAll(t);
                          }
                          if (!(u instanceof EndStmt)) {
                              transformersToCompact.add(u);
                          }
                      }
                  }
                  Unit start = methodToStartUnit.get(m);
                  ITransformer exit = unitToExit.get(start);
                  if (first) {
                      common.overwriteWith(exit);
                      first = false;
                  }
                  else {
                      common.retainAll(exit);
                  }
                  exitsToCompact.add(start);
                  
                  common.compact();
                  
                  // now re-calculate entry transformers
                  // by taking difference with "common"
                  for (Unit u : exitsToCompact) {
                      ITransformer exit2 = unitToExit.get(u);
                      exit2.differenceWithInPlace(common);
                  }
                  for (Unit u : transformersToCompact) {
                      ITransformer t = unitToTransformer.get(u);
                      t.differenceWithInPlace(common);
                  }
                  
                  commonEdgeCount.addAndGet(common.size());
                  return null;
              }
          });
      }
      
      try {
          AtomicTransformer.POOL.invokeAll(tasks);
      }
      catch (Exception e) {
          throw new RuntimeException(e);
      }
      
      long took = System.currentTimeMillis() - startCompactTime;
      Logger.println("    took " + String.format("%.2f", (took/1000.0)) + " secs (common avg: " + (commonEdgeCount.get()/(float)methodsToComputeCommonTransformer.size()) + ")", ANSICode.FG_BLUE);

    }
    
    private void compactSummaries(Component c) {
        Logger.println("    compacting summaries", ANSICode.FG_MAGENTA);
        long startCompactTime = System.currentTimeMillis();
        final ITransformer common = newEmptyTransformer();
        long numEdgesTotal = 0;
        boolean first = true;
        for (SootMethod m : c) {
            ITransformer summary = methodToSummary.get(m);
            numEdgesTotal += summary.size();
            if (first) {
                common.overwriteWith(summary);
                first = false;
            }
            else {
                common.retainAll(summary);
            }
        }
        
//        List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
//        for (final SootMethod m : c) {
//            tasks.add(new Callable<Object>() {
//                public Object call() {
//                    Transformer summary = methodToSummary.get(m);
//                    summary.differenceWithInPlace(common);
//                    return null;
//                }
//            });
//        }
        
//        try {
//            AtomicTransformer.POOL.invokeAll(tasks);
//        }
//        catch (InterruptedException ie) {
//            throw new RuntimeException(ie);
//        }
        
        long took = System.currentTimeMillis() - startCompactTime;
        Logger.println("    took " + String.format("%.2f", (took/1000.0)) + " secs (common: " + common.size() + ", avg: " + (numEdgesTotal/(double)c.size()) + ")", ANSICode.FG_MAGENTA);
    }        
    
    
    private void compactExitsAcrossComponent(Component c) {
        Logger.println("    performing compaction for entire component", ANSICode.FG_BLUE);
        long startCompactTime = System.currentTimeMillis();

        // this must be done sequentially
        boolean first = true;
        final ITransformer common = newEmptyTransformer();
        int maxExit = 0;
        for (Unit u : unitsToCompactInComponent) {
            ITransformer exit = unitToExit.get(u);
            if (first) {
                common.overwriteWith(exit);
                first = false;
            }
            else {
                common.retainAll(exit);
            }
            maxExit = Math.max(maxExit, exit.size());
        }
        
        List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
        for (final Unit u : unitsToCompactInComponent) {
            tasks.add(new Callable<Object>() {
                public Object call() {
                    ITransformer exit = unitToTransformer.get(u);
                    exit.differenceWithInPlace(common);
                    return null;
                }
            });
        }
        
        try {
            AtomicTransformer.POOL.invokeAll(tasks);
        }
        catch(InterruptedException ie) {
            throw new RuntimeException(ie);
        }        
        
        long took = System.currentTimeMillis() - startCompactTime;
        Logger.println("    took " + String.format("%.2f", (took/1000.0)) + " secs (stmts: " + unitsToCompactInComponent.size() + ", common: " + common.size() + ", max: " + maxExit + ")", ANSICode.FG_BLUE);

    }    
    
    private void calculateCommonExitEdges(Component c) {
        for (SootMethod m : c) {
            ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
            ITransformer common = newEmptyTransformer();
            boolean first = true;
            int maxExit = 0;
            int stmtCount = 0;
            for (Unit u : cfg) {
                ITransformer exit = unitToExit.get(u);
                if (exit != null) {
                    // check that succ is not only endstmt
                    boolean onlySuccIsEnd = true;
                    for (Unit s : unitToJumpSuccs.get(u).keySet()) {
                        if (!(s instanceof EndStmt)) {
                            onlySuccIsEnd = false;
                        }
                    }
                    if (!onlySuccIsEnd) {
                        stmtCount++;
                        if (first) {
                            common.overwriteWith(exit);
                            first = false;
                        }
                        else {
                            common.retainAll(exit);
                        }
                        maxExit = Math.max(maxExit, exit.size());
                    }
                }
            }
            Unit start = methodToStartUnit.get(m);
            ITransformer exit = unitToExit.get(start);
            stmtCount++;
            if (first) {
                common.overwriteWith(exit);
                first = false;
            }
            else {
                common.retainAll(exit);
            }
            
            if (stmtCount > 1) {
                Logger.println(common.size() + " common edges across " + stmtCount + " stmts (max: " + maxExit + " ), m: " + m);
            }
        }
    }    

    private void calculateCommonExitEdgesAcrossComponent(Component c) {
        List<Unit> unitsToCompact = new ArrayList<Unit>();
        for (SootMethod m : c) {
            ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
            for (Unit u : cfg) {
                ITransformer exit = unitToExit.get(u);
                if (exit != null) {
                    // check that succ is not only endstmt
                    boolean onlySuccIsEnd = true;
                    for (Unit s : unitToJumpSuccs.get(u).keySet()) {
                        if (!(s instanceof EndStmt)) {
                            onlySuccIsEnd = false;
                        }
                    }
                    if (!onlySuccIsEnd) {
                        unitsToCompact.add(u);
                    }
                }
            }
            Unit start = methodToStartUnit.get(m);
            unitsToCompact.add(start);
        }
        boolean first = true;
        ITransformer common = newEmptyTransformer();
        int maxExit = 0;
        for (Unit u : unitsToCompact) {
            ITransformer exit = unitToExit.get(u);
            if (first) {
                common.overwriteWith(exit);
                first = false;
            }
            else {
                common.retainAll(exit);
            }
            maxExit = Math.max(maxExit, exit.size());
        }
        Logger.println(common.size() + " common edges across " + unitsToCompact.size() + " stmts (max exit: " + maxExit + ")");
    }    

    private void calculateCommonSummaryEdges(Component c) {
        int maxSummary = 0;
        ITransformer common = newEmptyTransformer();
        boolean first = true;
        for (SootMethod m : c) {
            ITransformer summary = methodToSummary.get(m);
            if (first) {
                common.overwriteWith(summary);
                first = false;
            }
            else {
                common.retainAll(summary);
            }
            maxSummary = Math.max(maxSummary, summary.size());
        }
        Logger.println(common.size() + " common edges across all summaries (max summary: " + maxSummary + ")");
    }        
    
	private void calculateCommonEdges(Component c) {
	    for (SootMethod m : c) {
	        ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
	        ITransformer common = newEmptyTransformer();
	        boolean first = true;
	        int stmtCount = 0;
	        for (Unit u : cfg) {
	            ITransformer entry = unitToEntry.get(u);
	            if (entry != null) {
	                stmtCount++;
	                if (first) {
	                    common.overwriteWith(entry);
	                    first = false;
	                }
	                else {
	                    common.retainAll(entry);
	                }
	            }
	        }
	        Logger.println(common.size() + " common entry edges across " + stmtCount + " stmts for method " + m);
	    }
    }


//    private void outputLocalStats(Unit u, Transformer t, String tName) {
//        Stmt s = (Stmt)u;
//        if (s.containsInvokeExpr()) {
//            int xEdges = 0;
//            if (s instanceof AssignStmt) {
//                Local x = (Local)((AssignStmt)s).getLeftOp();
//                xEdges = t.countLocalAccesses(x);
//            }
//            else {
//                xEdges = -1;
//            }
//            Logger.println(tName + " - locals: " + t.countLocalAccesses() + " of which x: " + xEdges);
//        }
//
//    }


    private void storeResult(Unit u, ITransformer t, Map<Unit, ITransformer> store) {
//	    if (t != null) {// && store != unitToTransformer && store != unitToTransformerDelta && store != unitToEntryDelta) {
//	        t.toArraySets();
//	    }
	    store.put(u, t);
    }
	
	private ITransformer getResult(Unit u, Map<Unit, ITransformer> store) {
	    return store.get(u);
	}
	
    public boolean hasAlreadyBeenAnalysed(Component c) {
	    for (SootMethod m : c) {
	        if (!methodToSummary.containsKey(m)) {
	            return false;
	        }
	    }
	    return true;
	}
	
//    private void printRedundancyStats() {
//	    for (Component c : components) {
//	        for (SootMethod m : c) {
//	            Transformer summary = methodToSummary.get(m);
//	            Automaton nfa = summary.getAccessesNfa();
//	            Set<State> reachables = nfa.cleanup();
//	            System.err.println(m.getName() + "," + summary.countAccesses() + "," + nfa.getTransitions().size() + "," + summary.removeDeadEdges().countAccesses() + "," + summary.countLoads() + "," + summary.countLiveLoads(reachables));
//	        }
//	    }
//    }


    /*private Transformer renameParamsToArgs(Unit u, Transformer t) {
		if (u instanceof AssignStmt) {
			Transformer tRet = callToReturnTransformer.get(u);
			t = tRet.composeWith(t);
		}
		Transformer tCall = callToCallTransformer.get(u);
		t = t.composeWith(tCall);
		t.removeParamVarsAndRetVar();
		return t;
	}*/
	
//	private int countTrue(boolean[] bs) {
//		int count=0;
//		for (int i=0; i<bs.length; i++) {
//			count += (bs[i] ? 1 : 0);
//		}
//		return count;
//	}
	
	public static ITransformer getSummary(SootMethod m) {
	    return methodToSummary.get(m);
	}
	
	public static void storeSummary(SootMethod m, ITransformer t) {
	    // m may have been loaded from a file so get the current instance of m
	    SootMethod mCurrent = Scene.v().getMethod(m.toString());
	    methodToSummary.put(mCurrent, t);
	}

    public static Set<SootMethod> getMethods() {
        return methodToSummary.keySet();
    }
    
    public ITransformer getAtomicSummary() {
        return atomicSummary;
    }
	
//	public boolean hasBeenAnalysed(Component c) {
//		return analysed[c.getId()];
//	}
	
}
