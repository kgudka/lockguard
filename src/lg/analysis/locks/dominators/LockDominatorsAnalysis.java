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

package lg.analysis.locks.dominators;

import java.util.*;
import java.util.Map.Entry;

import lg.analysis.locks.*;
import lg.analysis.paths.LockSet;
import lg.cfg.AtomicSection;
import lg.util.*;
import soot.*;
import soot.jimple.AnyNewExpr;
import soot.jimple.paddle.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.thread.mhp.findobject.AllocNodesFinderPaddle;
import soot.jimple.toolkits.thread.mhp.pegcallgraph.PegCallGraph;

public class LockDominatorsAnalysis {
   
    private Map<AtomicSection,LockSet> atomicToLocks;
    
    public LockDominatorsAnalysis(Map<AtomicSection,LockSet> aToL) {
        atomicToLocks = aToL;
    }
    
    public void calculateDominatorLocks() {
        
        CallGraph cg = Scene.v().getCallGraph();
        PegCallGraph pcg = new PegCallGraph(cg); 
        
        AllocNodesFinderPaddle anf = new AllocNodesFinderPaddle(pcg, cg, null);
        
        Set<AllocNode> multiRunAllocNodes = anf.getMultiRunAllocNodes();
        
        // PREPROCESSING STEP: remove path locks that alias each other
        // first step: map single unique points-to objects to their path locks
        for (AtomicSection a : atomicToLocks.keySet()) {
            LockSet locks = atomicToLocks.get(a);
            final Map<AllocNode,List<Lock>> allocToLocks = new HashMap<AllocNode, List<Lock>>(); 
            for (Lock l : locks) {
                if (l instanceof PathLock) {
                    final PathLock pl = (PathLock)l;
                    BDDPointsToSet pts = (BDDPointsToSet)pl.getPointsToSet();
                    if (isSingleUniqueObject(pts, multiRunAllocNodes)) {
                        pts.forall(new P2SetVisitor() {
                            @Override
                            public void visit(ContextAllocNode n) {
                                AllocNode an = n.obj();
                                List<Lock> anLocks = allocToLocks.get(an);
                                if (anLocks == null) {
                                    anLocks = new ArrayList<Lock>();
                                    allocToLocks.put(an, anLocks);
                                }
                                anLocks.add(pl);
                            }
                        });
                    }
                }
            }
            // for each alloc node, pick one lock and remove the rest
            for (AllocNode an : allocToLocks.keySet()) {
                Logger.println("LOCKS FOR " + an);
                List<Lock> anLocks = allocToLocks.get(an);
                // first calculate meet of R/W of all locks
                boolean isWrite = false;
                boolean isDuplicate = anLocks.size() > 1;
                for (Lock l : anLocks) {
                    Logger.println(" + " + l);
                    isWrite |= l.isWrite();
                    l.setDuplicate(isDuplicate);
                }
                
                // keep first lock and remove the rest
                PathLock keep = (PathLock)anLocks.get(0);
                if (!keep.isWrite() && isWrite) {
                    locks.remove(keep);
                    keep = new PathLock(keep.getPrefix(), keep.getLookup(), isWrite, keep.isThreadLocal(), keep.isInstanceLocal(), keep.getPointsToSet(), keep.isDominated(), false, keep.isClassLocal(), keep.isReadOnly(), keep.doMultiLocking(), keep.isMethodLocal());
                    locks.add(keep);
                }
                keep.setDuplicate(false);
            }
        }
        
        final Map<AllocNode, Set<AllocNode>> dominatedToDominators = new HashMap<AllocNode, Set<AllocNode>>();
        Map<AtomicSection, Set<AllocNode>> atomicToAllocs = new HashMap<AtomicSection, Set<AllocNode>>();
        
        // l1 dominates l2 iff:
        //   - l1 is locked if l2 is locked
        //   - l1 refers to a unique run-time object
        //   - l1 will be acquired at run-time (i.e. not read-only, instance-local, etc.)
        //
        // Initialise dominatedToDominators with initial assumption
        for (AtomicSection a : atomicToLocks.keySet()) {
            final Set<AllocNode> potentialDominators = new HashSet<AllocNode>();
            final Set<AllocNode> potentialDominated = new HashSet<AllocNode>();
            final Set<AllocNode> allocs = new HashSet<AllocNode>();
            LockSet locks = atomicToLocks.get(a);
            for (Lock l : locks) {
                if (l instanceof PathLock && l.willBeAcquired()) {
                    PathLock pl = (PathLock)l;
                    PointsToSetReadOnly pts = (PointsToSetReadOnly)pl.getPointsToSet();
                    if (isSingleUniqueObject(pts, multiRunAllocNodes)) {
                        Logger.println(l + " in atomic " + a.getId() + " is a potential dominator lock", ANSICode.FG_BLUE);
                        pts.forall(new P2SetVisitor() {
                            public void visit(ContextAllocNode n) {
                                AllocNode an = (AllocNode)n.obj();
                                potentialDominators.add(an); 
                                potentialDominated.add(an); // all locks dominate themselves
                                allocs.add(an);
                            }
                        });
                    }
                    else {
                        pts.forall(new P2SetVisitor() {
                            @Override
                            public void visit(ContextAllocNode n) {
                                AllocNode an = (AllocNode)n.obj();
                                potentialDominated.add(an);
                                allocs.add(an);
                            }
                        });
                    }
                }
            }
            
            // potentialDominated contains all AllocNodes for locks that will
            // be acquired at run-time.
            // Initial assumption is that all potentially dominated locks are 
            // dominated by all potential dominators.
            for (AllocNode dominated : potentialDominated) {
                Set<AllocNode> existingDominators = dominatedToDominators.get(dominated);
                if (existingDominators == null) {
                    existingDominators = new HashSet<AllocNode>();
                    dominatedToDominators.put(dominated, existingDominators);
                }
                existingDominators.addAll(potentialDominators);
            }
            
            atomicToAllocs.put(a, allocs);
            
        }
        
        // dominatedToDominators is the initial assumption, repeatedly refine
        // until we reach a fixed point.
        // On each iteration, go through each lockset and remove those points-to
        // objs O that are no longer dominators, because they are not acquired
        // with the lock they supposedly dominate.
        
        boolean changed;
        do {
            changed = false;
            
            for (AtomicSection a : atomicToAllocs.keySet()) {
                Set<AllocNode> allocs = atomicToAllocs.get(a);
                Set<AllocNode> killed = new HashSet<AllocNode>();
                for (AllocNode an : allocs) {
                    // check that all of an's dominators are also in allocs
                    Set<AllocNode> dominators = dominatedToDominators.get(an);
                    if (dominators != null) {
                        // remove all dominators that are not in allocs
                        for (AllocNode d : dominators) {
                            if (!allocs.contains(d)) {
                                killed.add(d);
                            }
                        }
                        if (dominators.removeAll(killed)) {
                            changed = true;
                        }
                        if (dominators.isEmpty()) {
                            dominatedToDominators.remove(an);
                        }
                    }
                }
            }
            
        } while (changed);
        
        // Make final selection of the dominator locks
        // First collate all dominators and then cross off one at a time
        Set<AllocNode> dominators = new HashSet<AllocNode>();
        for (Set<AllocNode> d : dominatedToDominators.values()) {
            dominators.addAll(d);
        }
        
        // each lock is dominated by at most one dominator lock
        final Map<AllocNode,AllocNode> dominatedToDominator = new HashMap<AllocNode, AllocNode>();
        
        for (AllocNode d : dominators) {
            dominatedToDominators.remove(d);
            Logger.println("dominator: " + d);
            // find all alloc nodes that are dominated by d
            Set<AllocNode> killedDominated = new HashSet<AllocNode>();
            for (Entry<AllocNode, Set<AllocNode>> e : dominatedToDominators.entrySet()) {
                if (e.getValue().contains(d)) {
                    AllocNode dominated = e.getKey();
                    Logger.println("  - " + dominated);
                    killedDominated.add(dominated);
                    dominatedToDominator.put(dominated, d);
                }
            }
            for (AllocNode kd : killedDominated) {
                dominatedToDominators.remove(kd);
            }
            killedDominated.clear();
            Logger.println("");
        }
     
        // mark locks as dominated
        for (AtomicSection a : atomicToLocks.keySet()) {
            LockSet locks = atomicToLocks.get(a);
            for (Lock l : locks) {
                // check if l is dominated
                if (l instanceof PathLock) {
                    final PathLock pl = (PathLock)l;
                    PointsToSetReadOnly pts = (PointsToSetReadOnly)pl.getPointsToSet();
                    // pts may contain multiple alloc nodes, they must all
                    // be dominated for l to be dominated
                    boolean isDominated = !pl.isStatic() && !pts.isEmpty() && pts.forall(new P2SetVisitor() {
                        boolean returnValue2 = true;
                        @Override
                        public void visit(ContextAllocNode n) {
                            AllocNode an = n.obj();
                            returnValue2 &= dominatedToDominator.containsKey(an); 
                        }
                        @Override
                        public boolean getReturnValue() {
                            return returnValue2;
                        }
                    });
                    // pre: pl.willBeAcquired() == true ?
                    pl.setDominated(isDominated);
                    // post: isDominated -> pl.willBeAcquired() == false ?
                    
//                    if (pts.isEmpty()) {
//                        Logger.println("POINTS TO SET IS EMPTY - DOMINATED BY DEFAULT!");
//                    }
                }
            }
        }
        
        // To take meet of r/w modes, you need to first find out the 
        // dominator lock -> dominated locks relationship per-atomic
        Map<AllocNode,Set<AllocNode>> dominatorToDominated = new HashMap<AllocNode, Set<AllocNode>>();
        for (Entry<AllocNode,AllocNode> e : dominatedToDominator.entrySet()) {
            AllocNode dd = e.getKey();
            AllocNode dr = e.getValue();
            Set<AllocNode> dominatedSet = dominatorToDominated.get(dr);
            if (dominatedSet == null) {
                dominatedSet = new HashSet<AllocNode>();
                dominatorToDominated.put(dr, dominatedSet);
            }
            dominatedSet.add(dd);
        }
        
        // Now build dominator lock -> dominated locks relation:
        // First, build dominator -> dominator locks relation.
        Logger.println("BUILDING DOMINATOR -> DOMINATOR LOCKS RELATION");
        for (AtomicSection a : atomicToLocks.keySet()) {
            final Map<Lock,Set<Lock>> dominatorToDominatedLocks = new HashMap<Lock, Set<Lock>>();
            final Map<AllocNode,Set<Lock>> dominatorToLocks = new HashMap<AllocNode, Set<Lock>>();
            LockSet locks = atomicToLocks.get(a);
            for (Lock l : locks) {
                if (l instanceof PathLock) {
                    final PathLock pl = (PathLock)l;
                    BDDPointsToSet pts = (BDDPointsToSet)pl.getPointsToSet();
                    pts.forall(new P2SetVisitor() {
                        @Override
                        public void visit(ContextAllocNode n) {
                            AllocNode an = n.obj();
                            if (dominatedToDominator.containsValue(an)) {
                                Set<Lock> dLocks = dominatorToLocks.get(an);
                                if (dLocks == null) {
                                    dLocks = new HashSet<Lock>();
                                    dominatorToLocks.put(an, dLocks);
                                }
                                dLocks.add(pl);
                            }
                        }
                    });
                }
            }
            // Second, build dominator lock -> dominated locks relation
            for (Lock l : locks) {
                if (l instanceof PathLock) {
                    final PathLock pl = (PathLock)l;
                    if (pl.isDominated()) {
                        // find all dominator locks for this atomic and add pl
                        // to their sets
                        BDDPointsToSet pts = (BDDPointsToSet)pl.getPointsToSet();
                        pts.forall(new P2SetVisitor() {
                            @Override
                            public void visit(ContextAllocNode n) {
                                AllocNode an = n.obj();
                                AllocNode dr = dominatedToDominator.get(an);
                                if (dr != null) {
                                    Set<Lock> drlocks = dominatorToLocks.get(dr);
                                    if (drlocks != null) {
                                        for (Lock drlock : drlocks) {
                                            Set<Lock> ddlocks = dominatorToDominatedLocks.get(drlock);
                                            if (ddlocks == null) {
                                                ddlocks = new HashSet<Lock>();
                                                dominatorToDominatedLocks.put(drlock, ddlocks);
                                            }
                                            ddlocks.add(pl);
                                        }
                                    }
                                }
                            }
                        });
                    }
                }
            }
            // Third, take meet of R/W modes
            Set<Lock> kill = new HashSet<Lock>();
            Set<Lock> gen = new HashSet<Lock>();
            for (Lock drlock : dominatorToDominatedLocks.keySet()) {
                Logger.println(drlock + " DOMINATES", ANSICode.FG_MAGENTA);
                boolean isWrite = drlock.isWrite();
                Set<Lock> ddlocks = dominatorToDominatedLocks.get(drlock);
                for (Lock ddlock : ddlocks) {
                    isWrite |= ddlock.isWrite();
                    Logger.println(" - " + ddlock, ANSICode.FG_MAGENTA);
                }
                if (!drlock.isWrite() && isWrite) {
                    Logger.println(drlock + ": R -> W");
                    kill.add(drlock);
                    if (drlock instanceof PathLock) {
                        PathLock drlockp = (PathLock)drlock;
                        gen.add(new PathLock(drlockp.getPrefix(), drlockp.getLookup(), isWrite, drlockp.isThreadLocal(), drlockp.isInstanceLocal(), drlockp.getPointsToSet(), drlockp.isDominated(), drlockp.isDuplicate(), drlockp.isClassLocal(), drlockp.isReadOnly(), drlockp.doMultiLocking(), drlockp.isMethodLocal()));
                    }
                }
            }
            
            locks.removeAll(kill);
            locks.addAll(gen);
        }
    }
    
    private boolean isSingleUniqueObject(PointsToSet pts, final Set<AllocNode> multiRunAllocNodes) {
        if (pts instanceof PointsToSetReadOnly) {
            PointsToSetReadOnly ptsi = (PointsToSetReadOnly)pts;
            if (ptsi.size() == 1) {
                final boolean[] b = new boolean[1];
                b[0] = false;
                ptsi.forall(new P2SetVisitor() {
                    @Override
                    public void visit(ContextAllocNode n) {
                        // check that the AllocNode n is only ever executed once
                        // (i.e. so that the created object is unique)
                        AllocNode an = (AllocNode)n.obj();
                        b[0] = isSingleRunAllocNode(an, multiRunAllocNodes);
                    }
                });
                return b[0];
            }
            else {
                return false;
            }
        }
        else {
            throw new UnsupportedOperationException("pts is not a PointsToSetReadOnly, it has type : " + pts.getClass());
        }
    }

    private boolean isSingleRunAllocNode(AllocNode n, Set<AllocNode> multiRunAllocNodes) {
        Object ne = n.getNewExpr();
//        AnyNewExpr nne;
//        if (o instanceof soot.toolkits.scalar.Pair) {
//            soot.toolkits.scalar.Pair p = (soot.toolkits.scalar.Pair)o;
//            nne = (AnyNewExpr)p.getO1();
//        }
//        else {
//            nne = (AnyNewExpr)o;
//        }
        for (AllocNode n2 : multiRunAllocNodes) {
            if (ne == n2.getNewExpr()) {
                return false;
            }
        }
        return true;
    }
    
}
