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

package lg.analysis.local;

import java.util.*;

import lg.transformer.AtomicTransformer;

import soot.*;
import soot.jimple.*;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.sets.*;
import soot.jimple.toolkits.thread.AbstractRuntimeThread;
import soot.jimple.toolkits.thread.mhp.SynchObliviousMhpAnalysis;

public class ThreadLocalAnalysis {

    protected Set<Node> shared;
    
    public ThreadLocalAnalysis() {
        shared = new HashSet<Node>();
    }
    
    public boolean isThreadLocal(SootMethod m, Local l) {
        return !isThreadShared(l);
    }
    
    public boolean isThreadShared(Local l) {
        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
        PointsToSetInternal pts = (PointsToSetInternal)pta.reachingObjects(l);
        
        try {
            pts.forall(new P2SetVisitor() {
                @Override
                public void visit(Node n) {
                    if (shared.contains(n)) {
                        // no need to check further
                        throw new RuntimeException("shared");
                    }
                }
            });
        }
        catch (RuntimeException re) {
            if (re.getMessage().equals("shared")) {
                return true;
            }
            else {
                throw re;
            }
        }

        return false;
    }
    
    public void doAnalysis() {
        
        G.v().out.println("[wjtp.lg] tla: starting mhp");
        SynchObliviousMhpAnalysis mhp = new SynchObliviousMhpAnalysis();
        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();

        List<AbstractRuntimeThread> threads = new ArrayList<AbstractRuntimeThread>();
        List<Set<Node>> accesses = new ArrayList<Set<Node>>();

        G.v().out.println("[wjtp.lg] building per-thread access sets");
        for (AbstractRuntimeThread t : mhp.getThreads()) {

            // stores all accesses potentially made by t
            final Set<Node> tAccesses = new HashSet<Node>();
            
            for (SootClass c : Scene.v().getClasses()) {
                for (SootMethod m : c.getMethods()) {
                    if (t.containsMethod(m)) {
                        // Is it sufficient to find out what all locals point to? This is too conservative.
                        // IMPORTANT: We define an access as an object dereference.
//                        for (Local l : m.retrieveActiveBody().getLocals()) {
//                            PointsToSetInternal pts = (PointsToSetInternal)pta.reachingObjects(l);
//                            // add all obs in pts to t's set of object accesses
//                            pts.forall(new P2SetVisitor() {
//                                @Override
//                                public void visit(Node n) {
//                                    tAccesses.add(n);
//                                }
//                            });
//                        }
                        for (Unit u : m.retrieveActiveBody().getUnits()) {
                            Stmt s = (Stmt)u;
                            Local x = null;

                            // two types of dereference: 1) field, 2) array
                            if (s.containsFieldRef()) {
                                FieldRef fr = s.getFieldRef();
                                if (fr instanceof InstanceFieldRef) { // y = x.f or x.f = y
                                    InstanceFieldRef ifr = (InstanceFieldRef)fr;
                                    x = (Local)ifr.getBase();
                                }
                            }
                            else if (s.containsArrayRef()) {
                                ArrayRef ar = s.getArrayRef();
                                x = (Local)ar.getBase();
                            }
                            
                            if (x != null) {
                                PointsToSetInternal pts = (PointsToSetInternal)pta.reachingObjects(x);
                                // add all obs in pts to t's set of object accesses
                                pts.forall(new P2SetVisitor() {
                                    @Override
                                    public void visit(Node n) {
                                        tAccesses.add(n);
                                    }
                                });
                            }
                        }                        
                    }
                }
            }
            
            threads.add(t);
            accesses.add(tAccesses);
        
        }

        G.v().out.println("[wjtp.lg] tla: finding shared objects");
        
        // find shared objects
        for (int i=0; i<threads.size(); i++) {
            Set<Node> t1Accesses = accesses.get(i);
            for (Node n : t1Accesses) {
                // check if n is accessed by any other thread
                for (int j=i+1; j<threads.size(); j++) {
                    Set<Node> t2Accesses = accesses.get(j);
                    if (t2Accesses.contains(n)) {
                        if (AtomicTransformer.THREAD_LOCAL_DEBUG) G.v().out.println("[wjtp.lg]        " + n + " is shared between t" + i + " and t" + j);
                        shared.add(n);
                        break;
                    }
                }
            }
        }
        
        // calculate total number of object accesses
        Set<Node> totalAccesses = new HashSet<Node>();
        for (Set<Node> tAccesses : accesses) {
            totalAccesses.addAll(tAccesses);
        }
        
        G.v().out.println("[wjtp.lg] tla: " + shared.size() + "/" + totalAccesses.size() + " shared objects");
        
        
    }
    
}
