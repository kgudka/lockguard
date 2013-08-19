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

package lg.analysis.locks;

import java.util.*;

import lg.analysis.local.*;
import lg.analysis.paths.*;
import lg.analysis.paths.automata.*;
import lg.analysis.paths.transformer.*;
import lg.analysis.paths.transformer.fast.*;
import lg.analysis.paths.transformer.state.*;
import lg.transformer.AtomicTransformer;
import lg.util.*;
import lg.util.Timer;
import soot.*;
import soot.jimple.*;

public class AutomatonToLocks {

    private Automaton fa;
    private Set<Lock> locks;
    private Set<State> cyclicStates;
    private Set<State> threadLocalStates;
    private static Map<Stmt, Set<Type>> stmtToTypesCache = new HashMap<Stmt, Set<Type>>();
    private ThreadLocalAnalysis tla;
    private InstanceLocalAnalysisTransformer ila;
    private ClassLocalAnalysisTransformer cla;

    private Map<State,Set<Transition>> stateToIncidentTransitions;
    
    public AutomatonToLocks(Automaton a, ThreadLocalAnalysis t, InstanceLocalAnalysisTransformer i, ClassLocalAnalysisTransformer c) {
        fa = a;
        locks = new LockSet();
        cyclicStates = new HashSet<State>();
        threadLocalStates = new HashSet<State>();
        tla = t;
        ila = i;
        cla = c;
        stateToIncidentTransitions = new HashMap<State, Set<Transition>>();
        buildStateToIncidentTransitions();
        convert();
    }
    
    private void buildStateToIncidentTransitions() {
        for (Set<Transition> ts : fa.getTransitions()) {
            for (Transition t : ts) {
                State dest = t.getDst();
                Set<Transition> destIncident = stateToIncidentTransitions.get(dest);
                if (destIncident == null) {
                    destIncident = new HashSet<Transition>();
                    stateToIncidentTransitions.put(dest, destIncident);
                }
                destIncident.add(t);
            }
        }
    }

    public Set<Lock> getLocks() {
        return locks;
    }
    
    private void convert() {
        Logger.println("Finding cyclic states");
        Timer.start();
        findCyclicStates();
        Logger.println("    " + cyclicStates.size() + " cyclic states");
        Timer.stop();
        Timer.printDuration();
        
        if (AtomicTransformer.THREAD_LOCAL) {
            Logger.println("Finding thread-local states");
            Timer.start();
            findThreadLocalStates();
            Logger.println("    " + threadLocalStates.size() + " thread-local states");
//            Logger.println("    " + threadLocalStates);
            Timer.stop();
            Timer.printDuration();
        }
        
        Logger.println("Converting graph to locks");
        Timer.start();
        convertPaths();
        Timer.stop();
        Timer.printDuration();
    }
    
    private void findThreadLocalStates() {
        findThreadLocalStatesHelper(fa.getStartState(), new HashSet<State>());
    }

    private void findThreadLocalStatesHelper(State s, HashSet<State> visited) {
        if (!visited.contains(s)) {
            visited.add(s);
            if (isThreadLocal(s)) {
                threadLocalStates.add(s);
            }
            Set<Transition> outgoingTransitions = fa.getTransitions(s);
            if (outgoingTransitions != null) {
                for (Transition t : outgoingTransitions) {
                    State dest = t.getDst();
                    findThreadLocalStatesHelper(dest, visited);
                }
            }
        }
    }

    private boolean isThreadLocal(State s) {
        Stmt n = s.getStmt();
        if (n != null) {
            Local l = getLocalFromStmt(n);
            if (l != null) {
                ContainingMethodTag mTag = (ContainingMethodTag)n.getTag(ContainingMethodTag.TAG_NAME);
                SootMethod m = mTag.getMethod();
                return tla.isThreadLocal(m, l);
            }
            return false;
        }
        return false;
    }
    
    private void convertPaths() {
        convertPathsHelper(fa.getStartState(), null);
    }

    Set<State> convertedCyclicStates = new HashSet<State>();
    private void convertPathsHelper(State s, PathLock prefix) {
        if (cyclicStates.contains(s)) { 
            convertCyclicPathsHelper(s);
        }
        else {
            Set<Transition> outgoingTransitions = fa.getTransitions(s);
            if (outgoingTransitions != null) {
                for (Transition t : outgoingTransitions) {
                    Object lbl = t.getLbl();
                    State dest = t.getDst();
                    PathLookup lookup = lblToLookup(lbl, prefix, s, dest);
                    boolean isWrite = t.isWrite();
                    boolean threadLocal = threadLocalStates.contains(dest);
                    boolean instanceLocal = false;
                    boolean classLocal = false;
                    PointsToSet pts = stateToPointsToSet(dest);
                    if (AtomicTransformer.INSTANCE_LOCAL) {
                        if (lbl instanceof SootField) {
                            SootField f = (SootField)lbl;
                            instanceLocal = ila.isLocal(f);
                        }
                        else if (lbl instanceof ArrayElement) {
                            Set<Type> types = stateToTypes(s); // get possible array types
                            instanceLocal = true;
                            for (Type type : types) {
                                if (!ila.isArrayAccessLocal(type)) {
                                    instanceLocal = false;
                                    break;
                                }
                            }
                        }
                    }
                    if (AtomicTransformer.CLASS_LOCAL) {
                        if (lbl instanceof SootField) {
                            SootField f = (SootField)lbl;
                            if (f.isStatic()) {
                                classLocal = cla.isLocal(f);
                                if (!prefix.isStatic()) {
                                    throw new IllegalStateException("field is static but prefix lock is not a class! prefix: " + prefix + ", field: " + f);
                                }
                            }
                        }
                    }
                    PathLock lock = new PathLock(prefix, lookup, isWrite, threadLocal, instanceLocal, pts, false, false, classLocal, false, true, false);
                    if (pts.isEmpty()) {
//                        Logger.println("VERIFY EMPTY POINTS-TO SET FOR " + lock);
//                        ProfilerSupport.waitForKeyPress();
                    }
                    //                    Logger.println(lock + " is instanceLocal?: " + instanceLocal);
//                    if (lock.toStringPath().contains("java.util.Collections.EMPTY_LIST")) {
//                        ContainingMethodTag tag = (ContainingMethodTag)s.getStmt().getTag("ContainingMethodTag");
//                        SootMethod m = tag.getMethod();
//                        Logger.println(lock.toString(), ANSICode.FG_RED);
//                        Logger.println("\tstmt: " + s.getStmt(), ANSICode.FG_BLUE);
//                        Logger.println("\tmethod: " + m, ANSICode.FG_BLUE);
//                    }
                    locks.add(lock);
                    convertPathsHelper(dest, lock);
                }
            }
        }
    }

    private void convertCyclicPathsHelper(State s) {
        if (!convertedCyclicStates.contains(s)) {
            convertedCyclicStates.add(s);
            Set<Transition> outgoingTransitions = fa.getTransitions(s);
            if (outgoingTransitions != null) {
                for (Transition ot : outgoingTransitions) {
                    //Object lbl = ot.getLbl();
                    //Type t2 = lblToType(lbl, t);
                    State dest = ot.getDst();
                    Set<Type> types = stateToTypes(dest);
                    boolean instanceLocal = AtomicTransformer.INSTANCE_LOCAL ? isStateInstanceLocal(dest) : false;
                    boolean isWrite = ot.isWrite();
                    boolean threadLocal = threadLocalStates.contains(dest);
                    for (Type t : types) {
//                        if (t.toString().contains("java.lang.String")) {
//                            Stmt dstStmt = dest.getStmt();
//                            SootMethod m = null;
//                            if (dstStmt.hasTag(ContainingMethodTag.TAG_NAME)) {
//                                ContainingMethodTag tag = (ContainingMethodTag)dstStmt.getTag(ContainingMethodTag.TAG_NAME);
//                                m = tag.getMethod();
//                            }
//                            Logger.println("Lock on j.l.String: stmt = " + dstStmt + ", m = " + m);
//                            ProfilerSupport.waitForKeyPress();
//                        }
                        locks.add(new TypeLock(t, isWrite, threadLocal, instanceLocal, false, false));
                    }
                    convertCyclicPathsHelper(dest);
                }
            }
        }
    }

    private boolean isStateInstanceLocal(State s) {
        // all incoming transitions to s should be local
        // first find all incoming transitions
        Set<Transition> incidentTransitions = stateToIncidentTransitions.get(s);
        if (incidentTransitions == null) {
            throw new RuntimeException("incident transitions for " + s + " is null but shouldn't be!");
        }
        else {
            for (Transition t : incidentTransitions) {
                Object lbl = t.getLbl();
                if (lbl instanceof SootField) {
                    SootField f = (SootField)lbl;
                    if (!ila.isLocal(f)) {
                        return false;
                    }
                }
                else if (lbl instanceof ArrayElement) {
                    Set<Type> types = stateToTypes(s); // get possible array types
                    for (Type type : types) {
                        if (!ila.isArrayAccessLocal(type)) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

    private Set<Type> stateToTypesDfa(DfaState ds) {
        Set<Type> typesAll = new HashSet<Type>();
        for (State s : ds.getStates()) {
            Stmt n = s.getStmt();
            Set<Type> types = stmtToTypesCache.get(n);
            if (types == null) {
                Local l;
                if (n.containsFieldRef()) {
                    FieldRef fr = n.getFieldRef();
                    if (fr instanceof InstanceFieldRef) {
                        InstanceFieldRef ifr = (InstanceFieldRef)fr;
                        l = (Local)ifr.getBase();
                    }
                    else {
                        throw new UnsupportedOperationException("Unknown unbounded access starting from static: " + n);
                    }
                }
                else if (n.containsArrayRef()) {
                    ArrayRef ar = (ArrayRef)n.getArrayRef();
                    l = (Local)ar.getBase();
                }
                else {
                    throw new UnsupportedOperationException("Unknown access generating stmt: " + n);
                }
                
                PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
                PointsToSet pts = pta.reachingObjects(l);
                types = pts.possibleTypes();
                stmtToTypesCache.put(n, types);
            }
            typesAll.addAll(types);
        }
        return typesAll;
    }

    
    private Set<Type> stateToTypes(State s) {
        if (s instanceof DfaState) {
            return stateToTypesDfa((DfaState)s);
        }
        else {
            return stateToTypesNormal(s);
        }
    }

    private Set<Type> stateToTypesNormal(State s) {
        Stmt n = s.getStmt();
        Set<Type> types = stmtToTypesCache.get(n);
        if (types == null) {
            Local l = getLocalFromStmt(n);
            if (l != null) {
                PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
                PointsToSet pts = pta.reachingObjects(l);
                types = pts.possibleTypes();
                stmtToTypesCache.put(n, types);
            }
        }
        return types;
    }
    
    private PointsToSet stateToPointsToSet(State s) {
        Stmt n = s.getStmt();
        Local l = getLocalFromStmt(n);
        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
        PointsToSet pts = pta.reachingObjects(l);
        return pts;
    }

    private Local getLocalFromStmt(Stmt n) {
        if (n.containsFieldRef()) {
            FieldRef fr = n.getFieldRef();
            if (fr instanceof InstanceFieldRef) {
                InstanceFieldRef ifr = (InstanceFieldRef)fr;
                return (Local)ifr.getBase();
            }
            else {
                return null;
            }
        }
        else if (n.containsArrayRef()) {
            ArrayRef ar = (ArrayRef)n.getArrayRef();
            return (Local)ar.getBase();
        }
        else {
            throw new UnsupportedOperationException("Unknown access generating stmt: " + n);
        }
    }

    public static void storeStmtToTypeMapping(Stmt n, Set<Type> types) {
        stmtToTypesCache.put(n, types);
    }
    
    /*
   private Type lblToType(Object lbl, Type t) {
        if (lbl instanceof Local) {
            Local l = (Local)lbl;
            return l.getType();
        }
        else if (lbl instanceof ThisVariable) {
            return enclosingMethod.getDeclaringClass().getType();
        }
        else if (lbl instanceof ParameterVariable) {
            ParameterVariable pv = (ParameterVariable)lbl;
            return enclosingMethod.getParameterType(pv.getNum());
        }
        else if (lbl instanceof SootField) {
            SootField f = (SootField)lbl;
            return f.getType();
        }
        else if (lbl instanceof ArrayElement) {
            try {
                ArrayType at = (ArrayType)t;
                return at.getArrayElementType();
            }
            catch(ClassCastException cce) {
                throw new RuntimeException(cce);
            }
            
        }
        else {
            throw new UnsupportedOperationException("Unknown lookup: " + lbl);
        }
    }*/
    /*
    private Type getTypeOf(PathLock p) {
        PathLookup pl = p.getLookup();
        return pl.getType();
    }*/

    public Set<State> getCycleStates() {
        return cyclicStates;
    }
    
    private void findCyclicStates() {        
        findCyclicStatesHelper(fa.getStartState(), new HashSet<State>(), new HashSet<State>());
    }

    private void findCyclicStatesHelper(State s, Set<State> visited, Set<State> stack) {
        if (cyclicStates.contains(s)) {
            return;
        }
        else if (stack.contains(s)) {
            cyclicStates.add(s);
            collectAllReachable(s);
        }
        else if (!visited.contains(s)) {
            visited.add(s);
            stack.add(s);
            Set<Transition> outgoingTransitions = fa.getTransitions(s);
            if (outgoingTransitions != null) {
                for (Transition t : outgoingTransitions) {
                    State s2 = t.getDst();
                    findCyclicStatesHelper(s2, visited, stack);
                }
            }
            stack.remove(s);
        }
    }

    private void collectAllReachable(State s) {
        collectAllHelper(s, new HashSet<State>());
    }

    private void collectAllHelper(State s, HashSet<State> visited) {
        if (!visited.contains(s)) {
            visited.add(s);
            cyclicStates.add(s);
            Set<Transition> ts = fa.getTransitions(s);
            if (ts != null) {
                for (Transition t : ts) {
                    State s2 = t.getDst();
                    collectAllHelper(s2, visited);
                }
            }
        }
    }

    private PathLookup lblToLookup(Object lbl, PathLock prefix, State prefixState, State currState) {
        PathLookup lookup;
        if (lbl instanceof Local) {
            lookup = new LocalLookup((Local)lbl, stateToTypes(currState));
        }
        else if (lbl instanceof ThisVariable) {
            ThisVariable th = (ThisVariable)lbl;
            lookup = new ParamLookup(th, stateToTypes(currState));
        }
        else if (lbl instanceof ParameterVariable) {
            ParameterVariable pv = (ParameterVariable)lbl;
            lookup = new ParamLookup(pv, stateToTypes(currState));
        }
        else if (lbl instanceof SootClass) {
            SootClass c = (SootClass)lbl;
            lookup = new StaticLookup(c);
        }
        else if (lbl instanceof SootField) {
            lookup = new FieldLookup((SootField)lbl);
        }
        else if (lbl instanceof ArrayElement) {
            ArrayElement ae = (ArrayElement)lbl;
            //PathLookup prefixLookup = prefix.getLookup();
            //ArrayType at = (ArrayType)prefixLookup.getType();
            lookup = new ArrayLookup(ae, stateToTypes(currState));
        }
        else {
            throw new UnsupportedOperationException("Unknown lookup: " + lbl);
        }
        return lookup;
    }
    
}
