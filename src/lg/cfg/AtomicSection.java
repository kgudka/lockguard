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

package lg.cfg;

import java.util.*;

import lg.cg.NonColdEdgesPred;

import soot.*;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.*;
import soot.toolkits.exceptions.ThrowAnalysis;
import soot.toolkits.graph.ExceptionalUnitGraph;

public class AtomicSection extends ExceptionalUnitGraph {

    protected final ExceptionalUnitGraph enclosingCfg;
    protected final List<Unit> heads, tails;
    protected final List<Unit> visibleUnits;
    protected Local monitorLocal;
    protected boolean isReachable;

    static int counter = 1;
    int id;
    
    
    private AtomicSection(ExceptionalUnitGraph cfg) {
        super(cfg.getBody());
        enclosingCfg = cfg;
        heads = new ArrayList<Unit>();
        tails = new ArrayList<Unit>();
        visibleUnits = new ArrayList<Unit>();
        id = counter++;
    }

    // pre: head and tails are in fullUnitGraph and head precedes each tail
    public AtomicSection(ExceptionalUnitGraph cfg, Unit head, List<? extends Unit> t, Local monitor, boolean reachable) {
        this(cfg);
        heads.add(head);
        tails.addAll(t);
        monitorLocal = monitor;
        isReachable = reachable;
        buildVisibleUnitsSet();
    }

    // pre: heads and tails are in fullUnitGraph and each head precedes each
    // tail
    public AtomicSection(ExceptionalUnitGraph cfg, List<? extends Unit> h, List<? extends Unit> t, Local monitor, boolean reachable) {
        this(cfg);
        heads.addAll(h);
        tails.addAll(t);
        monitorLocal = monitor;
        isReachable = reachable;
        buildVisibleUnitsSet();
    }
    
    @Override
    protected void initialize(ThrowAnalysis throwAnalysis, boolean omitExceptingUnitEdges) {
    }

    protected void buildVisibleUnitsSet() {
        for (Unit head : heads) {
            buildVisibleUnitsSet(head);
        }
    }

    protected void buildVisibleUnitsSet(Unit u) {

        if (!visibleUnits.contains(u)) {

            visibleUnits.add(u);

            if (!tails.contains(u)) {

                for (Unit u2 : enclosingCfg.getSuccsOf(u)) {
                    buildVisibleUnitsSet(u2);
                }

            }

        }

    }

    @Override
    public List<Unit> getHeads() {
        return heads;
    }

    @Override
    public List<Unit> getTails() {
        return tails;
    }

    @Override
    public List<Unit> getPredsOf(Unit u) {

        if (!visibleUnits.contains(u)) {
            throw new UnsupportedOperationException("Unit " + u
                    + " does not exist in this sub graph");
        } else if (heads.contains(u)) {
            return new ArrayList<Unit>();
        } else {

            List<Unit> preds = new ArrayList<Unit>();

            for (Unit p : enclosingCfg.getPredsOf(u)) {

                if (visibleUnits.contains(p)) {
                    preds.add(p);
                }

            }

            return preds;

        }

    }

    @Override
    public List<Unit> getSuccsOf(Unit u) {

        if (!visibleUnits.contains(u)) {
            throw new UnsupportedOperationException("Unit " + u
                    + " does not exist in this sub graph");
        } else if (tails.contains(u)) {
            return new ArrayList<Unit>();
        } else {

            List<Unit> succs = new ArrayList<Unit>();

            for (Unit s : enclosingCfg.getSuccsOf(u)) {

                if (visibleUnits.contains(s)) {
                    succs.add(s);
                }

            }

            return succs;

        }

    }

    @Override
    public List<Unit> getExceptionalPredsOf(Unit u) {

        if (!visibleUnits.contains(u)) {
            throw new UnsupportedOperationException("Unit " + u
                    + " does not exist in this sub graph");
        } else if (heads.contains(u)) {
            return new ArrayList<Unit>();
        } else {
            return enclosingCfg.getExceptionalPredsOf(u);
        }

    }

    @Override
    public List<Unit> getExceptionalSuccsOf(Unit u) {

        if (!visibleUnits.contains(u)) {
            throw new UnsupportedOperationException("Unit " + u
                    + " does not exist in this sub graph");
        } else if (tails.contains(u)) {
            return new ArrayList<Unit>();
        } else {
            return enclosingCfg.getExceptionalSuccsOf(u);
        }

    }

    @Override
    public Collection<ExceptionDest> getExceptionDests(Unit u) {

        if (!visibleUnits.contains(u)) {
            throw new UnsupportedOperationException("Unit " + u
                    + " does not exist in this sub graph");
        } else {
            return enclosingCfg.getExceptionDests(u);
        }

    }

    @Override
    public List<Unit> getUnexceptionalPredsOf(Unit u) {

        if (!visibleUnits.contains(u)) {
            throw new UnsupportedOperationException("Unit " + u
                    + " does not exist in this sub graph");
        } else if (heads.contains(u)) {
            return new ArrayList<Unit>();
        } else {
            return enclosingCfg.getUnexceptionalPredsOf(u);
        }

    }

    @Override
    public List<Unit> getUnexceptionalSuccsOf(Unit u) {

        if (!visibleUnits.contains(u)) {
            throw new UnsupportedOperationException("Unit " + u
                    + " does not exist in this sub graph");
        } else if (tails.contains(u)) {
            return new ArrayList<Unit>();
        } else {
            return enclosingCfg.getUnexceptionalSuccsOf(u);
        }

    }

    @Override
    public List<Unit> getExtendedBasicBlockPathBetween(Unit from, Unit to) {
        throw new UnsupportedOperationException("Method not supported");
    }

    @Override
    public Body getBody() {
        return enclosingCfg.getBody();
    }

    public boolean containsUnit(Unit u) {
        return visibleUnits.contains(u);
    }

    @Override
    public Iterator<Unit> iterator() {
        return visibleUnits.iterator();
    }

    @Override
    public int size() {
        return visibleUnits.size();
    }

    @Override
    public String toString() {
        return visibleUnits.toString();
    }

    public ExceptionalUnitGraph getEnclosingUnitGraph() {
        return enclosingCfg;
    }
    
    public int getId() {
        return id;
    }
    
    public Set<SootMethod> getCalledMethods() {
        Set<SootMethod> callees = new HashSet<SootMethod>();
        CallGraph cg = Scene.v().getCallGraph();
        NonColdEdgesPred edgesPred = new NonColdEdgesPred();
        for (Unit u : this) {
            if (u instanceof Stmt) {
                Stmt s = (Stmt)u;
                if (s.containsInvokeExpr()) {
                    for (Iterator<Edge> edgesIt=cg.edgesOutOf(s); edgesIt.hasNext(); ) {
                        Edge e = edgesIt.next();
                        if (edgesPred.want(e)) {
                            SootMethod tgt = e.getTgt().method();
//                            if (tgt.isConcrete()) {
                                callees.add(tgt);
//                            }
                        }
                    }
                }
            }
        }
        return callees;
    }
    
    public Local getMonitorLocal() {
        return monitorLocal;
    }
    
    public boolean isReachable() {
        return isReachable;
    }

}