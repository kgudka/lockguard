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

package lg.util;

import java.io.PrintWriter;
import java.util.*;

import lg.analysis.singlethread.SingleThreadTag;
import lg.cfg.*;
import lg.cg.NonColdEdgesPred;
import lg.transformer.AtomicTransformer;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.*;
import soot.jimple.toolkits.thread.mhp.RunMethodsPred;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.queue.QueueReader;

public class AtomicsFinder {

    List<AtomicSection> atomicSections;

    RefType atomicType;

    // callgraph
    CallGraph callGraph;
    EdgePredicate explicitEdgePred;
    EdgePredicate runMethodPred;

    // bookkeeping
    Set<SootMethod> visitedMethods;
    Set<Unit> visitedUnits;
    
    Set<SootMethod> reachableMethods;

    public AtomicsFinder() {
        atomicSections = new ArrayList<AtomicSection>();
        atomicType = RefType.v(Atomic.class.getCanonicalName());
        callGraph = Scene.v().getCallGraph();
        explicitEdgePred = new NonColdEdgesPred();
        runMethodPred = new RunMethodsPred();
        visitedMethods = new GoogleHashSet<SootMethod>();
        visitedUnits = new GoogleHashSet<Unit>();
        atomicType = RefType.v(Atomic.class.getCanonicalName());
        reachableMethods = new HashSet<SootMethod>();
    }

    public List<AtomicSection> findAtomics() {

        atomicSections.clear();
        visitedMethods.clear();
        visitedUnits.clear();

//        findAtomics(Scene.v().getMainMethod());
        
//        Collection<SootMethod> entryPoints = EntryPoints.v().mainsOfApplicationClasses();
        Collection<SootMethod> entryPoints = EntryPoints.v().methodsOfApplicationClasses();
        
        calculateReachableMethods();
        
        if (AtomicTransformer.LIBRARY) {
            Logger.println("entryPoints: " + entryPoints.size());

            int count=0;
            Set<SootMethod> nonPrivEntries = new HashSet<SootMethod>();
            try {
                PrintWriter p = new PrintWriter("entries.txt");
                for (SootMethod entryPoint : entryPoints) {
                    if (entryPoint.isConcrete() && !entryPoint.isPrivate()) {
                        p.println(entryPoint.toString());
                        nonPrivEntries.add(entryPoint);
                        count++;
                    }
                }
                p.flush();
                p.close();
            }
            catch (Exception e) {
                throw new RuntimeException(e);
            }
            entryPoints = nonPrivEntries;
            Logger.println("Of which concrete and non-private: " + count);
        }
        
//        
//        int count2=0;
//        Set<SootMethod> nonPrivEntries2 = new HashSet<SootMethod>();
//        for (SootClass c : Scene.v().getClasses()) {
//            for (SootMethod m : c.getMethods()) {
//                if (m.isConcrete() && !m.isPrivate()) {
//                    nonPrivEntries2.add(m);
//                    count2++;
//                }
//            }
//        }
//        Logger.println("count2: " + count2);
//        
//        Set<SootMethod> diff1 = new HashSet<SootMethod>(nonPrivEntries);
//        diff1.removeAll(nonPrivEntries2);
//        Logger.println("Diff1: " + diff1.size());
//
//        Set<SootMethod> diff2 = new HashSet<SootMethod>(nonPrivEntries2);
//        diff2.removeAll(nonPrivEntries);
//        Logger.println("Diff2: " + diff2.size());        
//        
//        for (SootMethod m : diff2) {
//            Logger.println(m.toString());
//        }
        
        int count=0;
        Logger.println("Searching for atomics in " + entryPoints.size() + " methods");
        for (SootMethod entryPoint : entryPoints) {
            findAtomics(entryPoint);
        }

//        Set<AtomicSection> kill = new HashSet<AtomicSection>();
//        for (AtomicSection a : atomicSections) {
//            if (a.getBody().getMethod().toString().contains("GraphImage")) {
//                kill.add(a);
//            }
//        }
//        atomicSections.removeAll(kill);
        
        // remove any atomics that call wait or notify or notifyAll
        if (AtomicTransformer.IGNORE_WAIT_NOTIFY) {
            Set<AtomicSection> kill = new HashSet<AtomicSection>();
            for (AtomicSection a : atomicSections) {
                for (Unit u : a.getBody().getUnits()) {
                    // if u is invocation to wait/notify/notifyAll, we ignore a
                    if (isWaitNotify(u)) {
                        Logger.println("found: " + u, ANSICode.FG_RED);
                        kill.add(a);
                        break;
                    }
                }
            }
            atomicSections.removeAll(kill);
        }
        return atomicSections;

    }

    private void calculateReachableMethods() {
        CallGraph cg = Scene.v().getCallGraph();
        SootMethod mainMethod = Scene.v().getMainMethod();
        EdgePredicate explicitOrRunEdgePred = new EdgePredicate() {
            @Override
            public boolean want(Edge e) {
//                Logger.println("Want " + e.kind() + " call to " + e.tgt() + "? " + (explicitEdgePred.want(e) || runMethodPred.want(e)), ANSICode.FG_RED);
                return explicitEdgePred.want(e) || runMethodPred.want(e);
            }
        };
        reachableMethods.add(mainMethod);
        TransitiveTargets tt = new TransitiveTargets(cg, new Filter(explicitOrRunEdgePred));
        for (Iterator<MethodOrMethodContext> methodsIt=tt.iterator(mainMethod); methodsIt.hasNext(); ) {
            SootMethod m = methodsIt.next().method();
//            if (m.getDeclaringClass().isApplicationClass()) Logger.println("RM: " + m, ANSICode.FG_BLUE);
            reachableMethods.add(m);
        }
//        ProfilerSupport.waitForKeyPress();
    }

    private boolean isWaitNotify(Unit u) {
        Stmt s = (Stmt)u;
        if (s.containsInvokeExpr()) {
            String sStr = s.toString();
            if (sStr.contains("java.lang.Object: void wait()") || 
                sStr.contains("java.lang.Object: void notify()") ||
                sStr.contains("java.lang.Object: void notifyAll()")) {
                return true;
            }
        }
        return false;
    }
    
    private void findAtomics(SootMethod m) {
//        Logger.println("Searching for atomics in " + m);
        if (m.isConcrete() && !visitedMethods.contains(m)) { // && !(!AtomicTransformer.LIBRARY && isLibraryMethod(m))) {

            visitedMethods.add(m);            
            ExceptionalUnitGraph cfg = CFGCache.getCFG(m);

            if (m.getDeclaringClass().isLibraryClass()) {
                Logger.println(m.getDeclaringClass() + " is a library class");
                return;
            }
            
            // if synchronized method, turn into sync block
            boolean searchFromHeads = true;
            if (m.isSynchronized() || AtomicTransformer.LIBRARY) {
                // look out for wait/notify/notifyAll
                if (AtomicTransformer.IGNORE_WAIT_NOTIFY) {
                    for (Unit u : cfg) {
                        if (isWaitNotify(u)) {
                            Logger.println("Method " + m + " contains wait/notify/notifyAll");
                            return;
                        }
                    }
                }
                if (AtomicTransformer.INSTRUMENT) {
                    SyncMethodToSyncBlock.convertSyncMethodToSyncBlock(m, cfg);
                    CFGCache.invalidateCFG(m);
                    cfg = CFGCache.getCFG(m);
                }
                else {
                    searchFromHeads = false;
                    atomicSections.add(new AtomicMethod(m, cfg, reachableMethods.contains(m)));
                }
//                CFGToDotGraph drawer = new CFGToDotGraph();
//                DotGraph g = drawer.drawCFG(cfg);
//                g.plot(m.toString() + "sync.dot");
//                Logger.println("method: " + m.toString());
//                Logger.println("heads:" + cfg.getHeads());
//                Logger.println(cfg.toString(), ANSICode.FG_BLUE);
            }
            if (searchFromHeads) {
                for (Unit h : cfg.getHeads()) {
                    findAtomicsHelper(h, h, cfg, m.retrieveActiveBody().getUnits());
                }
            }
        }
    }

    private boolean isLibraryMethod(SootMethod m) {
        String pkg = m.getDeclaringClass().getJavaPackageName();
        return pkg.startsWith("java") || pkg.startsWith("javax") || pkg.startsWith("gnu") || pkg.startsWith("org") || pkg.startsWith("sun") || pkg.startsWith("com.ibm"); 
    }

    private void findAtomicsHelper(Unit first, Unit curr, ExceptionalUnitGraph cfg, PatchingChain<Unit> units) {

        if (!visitedUnits.contains(curr)) {

            visitedUnits.add(curr);

            if (curr instanceof EnterMonitorStmt) {

                EnterMonitorStmt enterMonitorStmt = (EnterMonitorStmt) curr;
                Local monitor = (Local)enterMonitorStmt.getOp();
                Type monitorType = monitor.getType();

//                if (monitorType == atomicType) {
                
                    List<Unit> exits = new ArrayList<Unit>();
                    // pass a private copy of visibleUnits because we may want to 
                    // search for inner sync blocks (see below)
                    findAtomicExits(curr, curr, cfg, units, exits, 0, new HashSet<Unit>(visitedUnits));

                    atomicSections.add(new AtomicSection(cfg, curr, exits, monitor, reachableMethods.contains(cfg.getBody().getMethod())));
                    
                    // recurse on exits if doing atomic sections, otherwise
                    // recurse on succs (otherwise we might miss inner sync blocks).
                    if (AtomicTransformer.MANUAL_LOCKS || AtomicTransformer.GLOBAL_LOCK) {
                        for (Unit succ : cfg.getSuccsOf(curr)) {
                            findAtomicsHelper(succ, succ, cfg, units);
                        }
                    }
                    else {
                        for (Unit exit : exits) {
                            findAtomicsHelper(exit, exit, cfg, units);
                        }
                    }

                    return;

//                }

            } else {

                // method calls
                Stmt currStmt = (Stmt) curr;

                if (currStmt.containsInvokeExpr()) {
                    for (Iterator<Edge> edgesIt = callGraph.edgesOutOf(currStmt); edgesIt.hasNext();) {
                        Edge e = edgesIt.next();
                        if (explicitEdgePred.want(e) || runMethodPred.want(e)) {
                            SootMethod callee = e.tgt();
                            findAtomics(callee);
                        }
                    }
                }

            }

            // recurse on successors
            for (Unit succ : cfg.getSuccsOf(curr)) {
//                if (succ == first) {
//                    CFGToDotGraph drawer = new CFGToDotGraph();
//                    DotGraph g = drawer.drawCFG(cfg);
//                    g.plot(cfg.getBody().getMethod().toString() + "sync.dot");
//                    Logger.println("method: " + cfg.getBody().getMethod());
//                    Logger.println("first and succ are the same");
//                    Logger.println("first: " + first);
//                    Logger.println("succ: " + succ);
//                    Logger.println("succs: " + cfg.getSuccsOf(curr));
//                    new Exception().printStackTrace();
//                    ProfilerSupport.waitForKeyPress();
//                }
                findAtomicsHelper(first, succ, cfg, units);
            }

        }

    }

    private void findAtomicExits(Unit enter, Unit curr, ExceptionalUnitGraph cfg, PatchingChain<Unit> units, List<Unit> exits, int nestingDepth, Set<Unit> visited) {

        if (curr == enter || !visited.contains(curr)) {
            visited.add(curr);

            if (curr instanceof MonitorStmt) {
                if (curr instanceof EnterMonitorStmt && curr != enter) {
                    nestingDepth++;
                } else if (curr instanceof ExitMonitorStmt) {
                    if (nestingDepth == 0) {
                        exits.add(curr);
                        return;
                    } else {
                        nestingDepth--;
                    }
                }
            }

            // recurse on successors
            for (Unit succ : cfg.getSuccsOf(curr)) {
                findAtomicExits(enter, succ, cfg, units, exits, nestingDepth, visited);
            }
        }

    }

}
