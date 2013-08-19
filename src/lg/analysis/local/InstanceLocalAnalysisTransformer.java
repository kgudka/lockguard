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

import gnu.trove.list.TIntList;
import gnu.trove.list.array.TIntArrayList;

import java.util.*;

import lg.analysis.local.InstanceLocalAnalysisTransformer.EscapeState;
import lg.cfg.CFGCache;
import lg.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.*;
import soot.jimple.toolkits.pointer.StrongLocalMustAliasAnalysis;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.*;
// flow-insensitive escape analysis
public class InstanceLocalAnalysisTransformer extends SceneTransformer {

    enum EscapeState {

        // External < Local
        INTERNAL (2) { public String toString() { return "Internal"; } },
        EXTERNAL (1) { public String toString() { return "External"; } };
        
        int id;
        EscapeState(int i) {
            id = i;
        }
        
        EscapeState meet(EscapeState s) {
            if (this.id <= s.id) {
                return this;
            }
            else {
                return s;
            }
        }
    }
    
    private static SootField ARRAY_ELEMS_FIELD;
    
    Map<SootClass, Map<SootField,EscapeState>> classToSummary;
    Map<SootMethod, Map<EquivalentValue,EscapeState>> methodToSummary;
    Map<SootMethod, StrongLocalMustAliasAnalysis> methodToLocalAliasAnalysis;
       
    Set<String> safeMethods;

    public static boolean DEBUG = false;
    
    SootMethod mainMethod;
    
    public InstanceLocalAnalysisTransformer() {
        classToSummary = new HashMap<SootClass, Map<SootField,EscapeState>>();
        methodToSummary = new HashMap<SootMethod, Map<EquivalentValue,EscapeState>>();
        methodToLocalAliasAnalysis = new HashMap<SootMethod, StrongLocalMustAliasAnalysis>();
        mainMethod = Scene.v().getMainMethod();
        initSafeMethods();
    }
    
    private void initSafeMethods() {
        safeMethods = new HashSet<String>();
        safeMethods.add("<java.lang.System: void arraycopy(java.lang.Object,int,java.lang.Object,int,int)>");
        safeMethods.add("<java.util.Arrays: void fill(java.lang.Object[],int,int,java.lang.Object)>");
        safeMethods.add("<java.util.AbstractCollection: boolean equals(java.lang.Object,java.lang.Object)>");
        safeMethods.add("<java.lang.Object: java.lang.Object clone()>");
        safeMethods.add("java.lang.Object clone()");
    }
    
    private Map<Stmt,TIntList> invokeToHandoverArgs;
    private Map<SootMethod,TIntList> methodToHandoverParams;
    
    @SuppressWarnings("unchecked")
    private void findHandoverArgs(Set<SootMethod> methods, Set<SootClass> classes) {
        G.v().out.println("[wjtp.ila] finding handover arguments2");
        invokeToHandoverArgs = new HashMap<Stmt, TIntList>();
        for (SootMethod m : methods) {
            if (m.getDeclaringClass().isApplicationClass()) {
                Logger.println("******************************************");
                Logger.println(m.toString());
            }
            long startTime = System.currentTimeMillis();
            ExceptionalUnitGraph cfg = CFGCache.getCFG(m);
            CombinedAnalysis duAnalysis = CombinedDUAnalysis.v(cfg);
            Map<Unit,Set<Unit>> unitToReachables = new HashMap<Unit, Set<Unit>>();
            buildReachableUnitsMap(cfg, unitToReachables);
            List<Stmt> mHandoverCallSites = new ArrayList<Stmt>();
            boolean printDebug = false; //m.getName().contains("createCar");
            for (Unit u : cfg) {
                Stmt s = (Stmt)u;
                if (s.containsInvokeExpr()) {
                    if (printDebug) { Logger.println("s: " + s); }
                    List<Value> args = s.getInvokeExpr().getArgs();
                    int i = 0;
                    for (Value a : args) {
                        if (a instanceof Local && a.getType() instanceof RefLikeType) {
                            Local l = (Local)a;
                            
                            if (printDebug) { Logger.println("l: " + l); }
                            
                            // 1. get all defs of l and aliases of l
                            Set<Local> aliases = new HashSet<Local>();
                            Set<Unit> lDefs = getDefs(l, s, duAnalysis, aliases, printDebug);
                            if (lDefs.isEmpty()) {
                                if (printDebug) { Logger.println("lDefs is empty", ANSICode.FG_RED); }
                                continue;
                            }
                            
                            // 2. get all uses of collected defs and check they are
                            //    legitimate:
                            //    a. passed as arg only to s
                            //    b. may call <init> on l or alias
                            //    c. may call Thread.start() on l or alias
                            //    d. may call Thread.join() on l or alias
                            //    e. may do local-to-local copy (i.e. aliasing)
                            boolean validateUses = checkUses(l, s, lDefs, duAnalysis, aliases, printDebug);
                            if (!validateUses) {
                                if (printDebug) { Logger.println("uses are invalid", ANSICode.FG_RED); }
                                continue;
                            }
                            
                            // 3. check no cyclic call of s after def  (i.e. obj
                            //    may be handed over to multiple objs if this is
                            //    the case). cyclic calls of the other above 
                            //    allowed uses is fine.
                            boolean cyclicAccess = checkIfCalledMultipleBeforeDef(s, lDefs, cfg, unitToReachables);
                            if (cyclicAccess) {
                                if (printDebug) { Logger.println("cyclic access", ANSICode.FG_RED); }
                                continue; // may still handover for another arg
                            }
                            
                            // l is a handover argument!
                            TIntList handoverArgs = invokeToHandoverArgs.get(s);
                            if (handoverArgs == null) {
                                handoverArgs = new TIntArrayList();
                                invokeToHandoverArgs.put(s, handoverArgs);
                                mHandoverCallSites.add(s);
                            }
                            handoverArgs.add(i);
                        }
                        i++;
                    }
                }
            }
            if (!mHandoverCallSites.isEmpty() && m.getDeclaringClass().isApplicationClass()) {
                G.v().out.println("[wjtp.ila] " + m);
                for (Stmt invoke : mHandoverCallSites) {
                    G.v().out.println("[wjtp.ila]     " + invoke + ": " + invokeToHandoverArgs.get(invoke));
                }
            }
            if (printDebug) { ProfilerSupport.waitForKeyPress(); }
            long took = System.currentTimeMillis()-startTime;
            if (m.getDeclaringClass().isApplicationClass()) {
                Logger.println("Took: " + took/1000.0f + " seconds");
                Logger.println("******************************************");
            }
        }
    }

    private boolean checkIfCalledMultipleBeforeDef(Unit invoke, Set<Unit> defs, ExceptionalUnitGraph cfg, Map<Unit, Set<Unit>> unitToReachables) {
        return checkIfCalledMultipleBeforeDefHelper(null, invoke, defs, cfg, unitToReachables, new ArrayList<Unit>());
    }

    private boolean checkIfCalledMultipleBeforeDefHelper(Unit curr, Unit invoke, Set<Unit> defs, ExceptionalUnitGraph cfg, Map<Unit, Set<Unit>> unitToReachables, List<Unit> visited) {
        if (curr == null) {
            curr = invoke;
        }
        else if (curr == invoke) {
            return true; // bingo!
        }
        else if (visited.contains(curr)) {
            return false; // hit cycle, backtrack
        }
        else if (!unitToReachables.get(curr).contains(invoke)) {
            return false; // hit deadend, backtrack
        }
        else if (defs.contains(curr) && ((DefinitionStmt)curr).getRightOp() instanceof NewExpr) {
            return false; // we've hit an x = new T(), backtrack and try another path
        }

        visited.add(curr);
        for (Unit s : cfg.getSuccsOf(curr)) {
            if (checkIfCalledMultipleBeforeDefHelper(s, invoke, defs, cfg, unitToReachables, visited)) {
                return true;
            }
        }
        visited.remove(curr);
        return false;
    }

    @SuppressWarnings("unchecked")
    private boolean checkUses(Local l, Stmt invoke, Set<Unit> defs, CombinedAnalysis duAnalysis, Set<Local> aliases, boolean printDebug) {
        for (Unit def : defs) {
            List<UnitValueBoxPair> defUsePairs = duAnalysis.getUsesOf(def);
            for (UnitValueBoxPair duPair : defUsePairs) {
                Stmt duSt = (Stmt)duPair.getUnit();
                if (duSt == invoke) {
                    // Ok
                }
                else if (duSt.containsInvokeExpr()) {
                    InvokeExpr ie = duSt.getInvokeExpr();
                    SootMethod tgt = ie.getMethod();
                    if (tgt.getName().equals("<init>")) {
                        // Ok as long as constructor is called on l or an alias
                        InstanceInvokeExpr iie = (InstanceInvokeExpr)ie;
                        Local base = (Local)iie.getBase();
                        if (equivTo(base, l, aliases)) {
                            // Ok
//                          Logger.println("<init>");
                        }
                        else {
                            if (printDebug) {
                                Logger.println("1 checkUses returned false because of " + duSt);
                                Logger.println("l: " + l);
                                Logger.println("aliases: " + aliases);
                            }
                            return false;
                        }
                    }
                    else if (tgt.getSignature().equals("<java.lang.Thread: void start()>")) {
                        // Ok
//                        Logger.println("Thread.start()");
                    }
                    else if (tgt.getSignature().equals("<java.lang.Thread: void join()>")) {
                        // Ok
//                        Logger.println("Thread.join()");
                    }
                    else {
                        if (printDebug) { Logger.println("2 checkUses returned false because of " + duSt); }
                        // abort
                        return false;
                    }
                }
                else if (duSt instanceof DefinitionStmt) {
                    DefinitionStmt duDefSt = (DefinitionStmt)duSt;
                    Value lhs = duDefSt.getLeftOp();
                    Value rhs = duDefSt.getRightOp();
                    boolean lhsOk = lhs instanceof Local;
                    boolean rhsOk = rhs instanceof Local || (rhs instanceof CastExpr && ((CastExpr)rhs).getOp() instanceof Local) || ((rhs instanceof CastExpr) && ((CastExpr)rhs).getOp() instanceof NullConstant) || rhs instanceof NewExpr || rhs instanceof NullConstant;
                    if (lhsOk && rhsOk) {
                        // Ok
//                        Logger.println("local-to-local");
                    }
                    else {
                        // abort
                        if (printDebug) { Logger.println("3 checkUses returned false because of " + duSt); }
                        return false;
                    }
                }
                else {
                    // abort
                    if (printDebug) { Logger.println("4 checkUses returned false because of " + duSt); }
                    return false;
                }
            }
        }
        return true;
    }

    private boolean equivTo(Local b, Local l, Set<Local> aliases) {
        if (b.equivTo(l)) {
            return true;
        }
        else {
            for (Local a : aliases) {
                if (b.equivTo(a)) {
                    return true;
                }
            }
            return false;
        }
    }

    private Set<Unit> getDefs(Local l, Stmt s, CombinedAnalysis duAnalysis, Set<Local> aliases, boolean printDebug) {
        List<Unit> lDefs = duAnalysis.getDefsOfAt(l, s);
        Set<Unit> allDefs = new HashSet<Unit>(); 
        for (Unit lDef : lDefs) {
            DefinitionStmt lDefSt = (DefinitionStmt)lDef;
            Value rhs = lDefSt.getRightOp();
            if (printDebug) { Logger.println("lDef: " + lDef); }
            if (rhs instanceof Local || (rhs instanceof CastExpr && ((CastExpr)rhs).getOp() instanceof Local)) {
                Local r = (Local)(rhs instanceof CastExpr ? ((CastExpr)rhs).getOp() : rhs);
                // Recurse on r
                Set<Unit> rDefs = getDefs(r, lDefSt, duAnalysis, aliases, printDebug);
                if (rDefs.isEmpty()) {
                    // means that somewhere higher up we found an aborting def, so propagate
                    return new HashSet<Unit>();
                }
                else {
                    allDefs.addAll(rDefs);
                    // add ldef
                    allDefs.add(lDef);
                }
                aliases.add(r);
            }
            else if (rhs instanceof CastExpr && ((CastExpr)rhs).getOp() instanceof NullConstant) {
                allDefs.add(lDef);
            }
            else if (rhs instanceof NewExpr) {
                allDefs.add(lDef);
            }
            else if (rhs instanceof NullConstant) {
                allDefs.add(lDef);
            }
            else {
                // abort: l is not a handover
                if (printDebug) { Logger.println("Aborting because of " + lDef, ANSICode.FG_BLUE); }
                return new HashSet<Unit>();
            }
        }
        return allDefs;
    }

    private void buildReachableUnitsMap(ExceptionalUnitGraph cfg, Map<Unit, Set<Unit>> unitToReachables) {
        for (Unit u : cfg.getHeads()) {
            buildReachableUnitsMapHelper(u, cfg, unitToReachables, new HashSet<Unit>(), new ArrayList<Unit>());
        }
    }

    private void buildReachableUnitsMapHelper(Unit u, ExceptionalUnitGraph cfg, Map<Unit, Set<Unit>> unitToReachables, Set<Unit> reachable, List<Unit> visited) {
        if (visited.contains(u)) {
            return; // cycle
        }
        else if (unitToReachables.containsKey(u)) {
            reachable.addAll(unitToReachables.get(u)); // already processed this node
        }
        else {
            visited.add(u);
            reachable.add(u);
            Set<Unit> localReachables = new HashSet<Unit>();
            for (Unit s : cfg.getSuccsOf(u)) {
                buildReachableUnitsMapHelper(s, cfg, unitToReachables, localReachables, visited);
            }
            unitToReachables.put(u, localReachables);
            reachable.addAll(localReachables);
            visited.remove(u);
        }
    }

    
    public void outputResults(SootClass c) {
        G.v().out.println("[lg.ila] Escape states for fields in " + c);
        Map<SootField, EscapeState> cSummary = getClassSummary(c);
        for (SootField f : c.getFields()) {
            G.v().out.println("[lg.ila]         " + f.getName() + ": " + cSummary.get(f));
        }
        G.v().out.println("[lg.ila]         " + ARRAY_ELEMS_FIELD.getName() + ": " + cSummary.get(ARRAY_ELEMS_FIELD));
        G.v().out.println();
    }
    
    public void outputResults(SootMethod m) {
        Map<EquivalentValue,EscapeState> mSummary = methodToSummary.get(m);
        G.v().out.println("[lg.ila] Escape states for {this,params,return} in " + m);
        for (EquivalentValue ev : mSummary.keySet()) {
            G.v().out.println("[lg.ila]         " + ev + ": " + mSummary.get(ev));
        }
    }
    
    public boolean isArrayAccessLocal(Type t) {
        if (t instanceof ArrayType) {
            t = ((ArrayType)t).baseType;
        }
        if (t instanceof AnySubType) {
            AnySubType ast = (AnySubType)t;
            t = ast.getBase();
        }
        if (t instanceof RefType) {
            RefType rt = (RefType)t;
            SootClass c = rt.getSootClass();
            Map<SootField,EscapeState> cSummary = classToSummary.get(c);
            if (cSummary == null) {
//                throw new IllegalArgumentException("Class " + c + " does not have a summary (" + ARRAY_ELEMS_FIELD.getName() + ")");
                return false;
            }
            else {
                return cSummary.get(ARRAY_ELEMS_FIELD) == EscapeState.INTERNAL;
            }
        }
        else if (t instanceof PrimType) {
            return true;
        }
        else {
            throw new RuntimeException("Illegal array base type: " + t);
        }
    }
    
//    public boolean isInstanceLocal(SootMethod m, Local l) {
//        Map<EquivalentValue,EscapeState> mSummary = methodToSummary.get(m);
//        if (mSummary == null) {
//            throw new IllegalArgumentException("Method " + m + " does not have a summary (" + l + ")");
//        }
//        else {
//            return mSummary.get(getLocalRef(l)) == EscapeState.LOCAL;
//        }
//    }
    
    public boolean isLocal(SootField f) {
        SootClass c = f.getDeclaringClass();
        Map<SootField, EscapeState> cSummary = classToSummary.get(c);
        if (cSummary == null) {
//            throw new IllegalArgumentException("Class " + c + " does not have a summary (" + f + ")");
            return false;
        }
        else {
            return cSummary.get(f) == EscapeState.INTERNAL;
        }
    }
    
    public void doAnalysis() {
        G.v().out.println("[wjtp.ila] instance local analysis running");
        internalTransform(null, null);
    }
    
    // per-class summary: { fields, arrayelem } -> { NoEscape, CallerEscape, GlobalEscape }
    // per-method summary: { this, params, return } -> { NoEscape, CallerEscape, GlobalEscape }
    // iterate through all methods until there is no change
    protected void internalTransform(String phaseName, Map options) {
        
        ARRAY_ELEMS_FIELD = new SootField("$elem$", NullType.v());
        
        Set<SootMethod> methods = new HashSet<SootMethod>();
        Set<SootClass> classes = new HashSet<SootClass>();
        
        List<SootMethod> entryPoints = EntryPoints.v().methodsOfApplicationClasses();
//        System.out.println("entryPoints: " + entryPoints);
        CallGraph cg = Scene.v().getCallGraph();
        EdgePredicate edgePred = new ExplicitEdgesPred();
        TransitiveTargets tt = new TransitiveTargets(Scene.v().getCallGraph(), new Filter(edgePred));
        for (SootMethod entryPoint : entryPoints) {
            methods.add(entryPoint);
            classes.add(entryPoint.getDeclaringClass());
            for (Iterator<MethodOrMethodContext> ttIt = tt.iterator(entryPoint); ttIt.hasNext(); ) {
                SootMethod t = ttIt.next().method();
                if (t.isConcrete()) { //throw new AssertionError("method " + t + " is not concrete!");
                    methods.add(t);
                }
                // even if method is "interface" or "abstract" still add class
                // because may have arrays of it's type.
                classes.add(t.getDeclaringClass());
            }
        }
        
        // build callee to callers map
        Map<SootMethod,List<Stmt>> calleeToCallers = new HashMap<SootMethod, List<Stmt>>();
        for (SootMethod m : methods) {
            List<Stmt> callers = new ArrayList<Stmt>();
            calleeToCallers.put(m, callers);
            for (Iterator<Edge> edgesIt=cg.edgesInto(m); edgesIt.hasNext(); ) {
                Edge e = edgesIt.next();
                SootMethod src = e.src();
                Stmt invoke = e.srcStmt();
                if (edgePred.want(e) && methods.contains(src)) {
                    callers.add(invoke);
                }
            }
        }

        // build initial per-class summaries
        for (SootClass c : classes) {
            classToSummary.put(c, constructClassSummary(c));
        }
        
        // find handover arguments
        findHandoverArgs(methods, classes);
        
        methodToHandoverParams = new HashMap<SootMethod, TIntList>();
        
        // build initial per-method summaries
        for (SootMethod m : methods) {
            // initial assumption is that:
            // for private, protected methods: this, params, return are all LOCAL
            // for public, package: this, params, return are all EXTERNAL
            Map<EquivalentValue, EscapeState> summary = new HashMap<EquivalentValue, InstanceLocalAnalysisTransformer.EscapeState>();
            
//            boolean local = false;
            boolean local = false;
            
            if (m.isStatic()) {
                // if outer-class instance accessor method (called access$XXX) then treat as local
                local = isOuterClassInstanceAccessor(m);
//                if (local) Logger.println(m + " is an outerclass instance accessor method");
            }
            else {
                summary.put(getThisRef(m), EscapeState.INTERNAL); // "this" is always local
//                local = !m.isPublic() || isInnerClassConstructor(m) || isSafeMethod(m);
                local = true;
            }

            EscapeState defaultEscapeState = local ? EscapeState.INTERNAL : EscapeState.EXTERNAL;
            List<Stmt> callers = calleeToCallers.get(m);

            for (int i=0; i<m.getParameterCount(); i++) {
                EquivalentValue paramRef = getParameterRef(m, i);
                // if all args at call sites are handovers, then the escape state
                // is LOCAL otherwise revert to defaultEscapeState
//                EscapeState callerMeet = callers.isEmpty() ? defaultEscapeState : EscapeState.INTERNAL;
                boolean isHandoverParam = !callers.isEmpty();
                for (Stmt caller : callers) {
                    TIntList handoverArgs = invokeToHandoverArgs.get(caller);
                    isHandoverParam &= (handoverArgs != null && handoverArgs.contains(i));
//                    callerMeet = callerMeet.meet((handoverArgs != null && handoverArgs.contains(i)) ? EscapeState.INTERNAL : defaultEscapeState);
                }
                if (isHandoverParam && m.getDeclaringClass().isApplicationClass() && !callers.isEmpty()) {
                    Logger.println("Arg " + i + " of " + m + " is HANDOVER");
                    TIntList handoverParams = methodToHandoverParams.get(m);
                    if (handoverParams == null) {
                        handoverParams = new TIntArrayList();
                        methodToHandoverParams.put(m, handoverParams);
                    }
                    handoverParams.add(i);
//                    ProfilerSupport.waitForKeyPress();
                }
                EscapeState paramState = isHandoverParam ? EscapeState.INTERNAL : defaultEscapeState;
                summary.put(paramRef, paramState);
            }
            if (m.getReturnType() != VoidType.v()) {
                summary.put(getReturnRef(m), defaultEscapeState);
            }

            methodToSummary.put(m, summary);
        }
        
        G.v().out.println("[wjtp.ila] Starting escape analysis of " + methods.size() + " methods, " + classes.size() + " classes");
        
        boolean changed = false;
        long iterationCount = 0;
        do {
            changed = false;
            iterationCount++;
            if (DEBUG) G.v().out.println("[lg.ila] *******************************");
            if (DEBUG) G.v().out.println("[lg.ila] Iteration: " + iterationCount);
            if (DEBUG) G.v().out.println("[lg.ila] *******************************");
            for (SootMethod m : methods) {
//                DEBUG = m.getSignature().equals("<java.util.Vector: void removeAllElements()>"); // && m.getDeclaringClass().toString().equals("java.util.Vector");
                if (DEBUG) G.v().out.println("[lg.ila] Current method: " + m);
                Map<EquivalentValue,EscapeState> summary = methodToSummary.get(m);
                for (Unit u : m.retrieveActiveBody().getUnits()) {
                    if (DEBUG) G.v().out.println("[lg.ila]     u: " + u);
                    // apply transfer function to update m's summary and possibly other method and class summaries
                    if (DEBUG) G.v().out.println("[lg.ila]         state before: " + summary);
                    if (applyTransferFunction(u, m, summary)) {
                        changed = true;
                    }
//                    if (DEBUG) G.v().out.println("[lg.ila]         state after (changed=" + changed + "): " + summary);
                    if (DEBUG) G.v().out.println();
                    if (DEBUG) ProfilerSupport.waitForKeyPress();
                }
            }
        }
        while (changed);
        
        G.v().out.println("[wjtp.ila] Finished escape analysis in " + iterationCount + " iterations, outputting results for application classes.");
        
        // output results
        for (SootClass c : classes) {
            if (c.isApplicationClass()) {
                outputResults(c);
            }
        }
        
        methodToLocalAliasAnalysis.clear();
        methodToSummary.clear();
        methodToHandoverParams.clear();
        
        methodToLocalAliasAnalysis = null;
        methodToSummary = null;
        methodToHandoverParams = null;
    }
    
    private boolean isOuterClassInstanceAccessor(SootMethod m) {
        return m.getName().startsWith("access$");
    }

    private boolean isInnerClassConstructor(SootMethod m) {
        SootClass mClass = m.getDeclaringClass();
        boolean res = mClass.getName().contains("$") && m.getName().equals("<init>");
//        if (res) {
//            Logger.println(m + " is an inner class constructor", ANSICode.FG_BLUE);
//        }
        return res;
    }

    private Map<SootField, EscapeState> constructClassSummary(SootClass c) {
        Map<SootField,EscapeState> summary = new HashMap<SootField,EscapeState>();
        for (SootField f : c.getFields()) {
            if (f.isStatic()) {
                summary.put(f, EscapeState.EXTERNAL);
            }
            else {
                summary.put(f, EscapeState.INTERNAL);
            }
        }
        summary.put(ARRAY_ELEMS_FIELD, EscapeState.INTERNAL); // for representing array accesses on arrays of type c
        return summary;
    }

    private boolean applyTransferFunction(Unit u, SootMethod m, Map<EquivalentValue,EscapeState> mSummary) {
        boolean[] changed = { false };
        if (u instanceof DefinitionStmt) {

            DefinitionStmt defSt = (DefinitionStmt)u;

            Value lval = defSt.getLeftOp();
            Value rval = defSt.getRightOp();

            // transformers
            if(lval instanceof Local && lval.getType() instanceof RefLikeType/* && lval.getType() != stringType*/) {
                Local x = (Local)lval;
                // x = blah
                EquivalentValue xv = init(x, mSummary, changed);
                if (rval instanceof Local) {
                    // x = y
                    Local y = (Local)rval;
                    EquivalentValue yv = init(y, mSummary, changed);
                    EscapeState newState = mSummary.get(xv).meet(mSummary.get(yv));
                    if (updateSummary(m, defSt, mSummary, x, xv, newState)) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, defSt, mSummary, y, yv, newState)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof NullConstant) {
                    // x = null
                    // no change to x's escape state because e ^ local = e
                }
                else if (rval instanceof NewExpr || rval instanceof NewArrayExpr || rval instanceof NewMultiArrayExpr) {
                    // x = new/newarray/newmultiarray
                    // no change in all 3 cases (e ^ local = e)
                    // EXTERNAL if current method is the application's main method, 
                    // INTERNAL otherwises
                    if (m == mainMethod || m.toString().contains("run()")) {
                        Logger.println("MAIN/RUN METHOD ALLOCATION u: " + u);
//                        ProfilerSupport.waitForKeyPress();
                        if (updateSummary(m, defSt, mSummary, x, xv, EscapeState.EXTERNAL)) {
                            changed[0] = true;
                        }
                    }
                }
                else if (rval instanceof StringConstant) {
                    // x = ""
                    // no change to x's escape state because e ^ local = e
                }
                else if(rval instanceof CastExpr) {
                    CastExpr castEx = (CastExpr)rval;
                    if(castEx.getOp() instanceof Local) {
                        // x = (type)y
                        Local y = (Local)castEx.getOp();
                        EquivalentValue yv = init(y, mSummary, changed);
                        EscapeState newState = mSummary.get(xv).meet(mSummary.get(yv));
                        if(updateSummary(m, defSt, mSummary, x, xv, newState)) {
                            changed[0] = true;
                        }
                        if (updateSummary(m, defSt, mSummary, y, yv, newState)) {
                            changed[0] = true;
                        }
                    }
                    else if(castEx.getOp() instanceof NullConstant) {
                        // x = (type)null
                        // no change
                    }
                    else if(castEx.getOp() instanceof StringConstant) {
                        // x = (String)""
                        // no change
                    }
                }
                else if (rval instanceof InstanceFieldRef) {
                    // x = y.f
                    InstanceFieldRef instFieldRef = (InstanceFieldRef)rval;
                    Local y = (Local)instFieldRef.getBase();
                    SootField f = instFieldRef.getField();
                    SootClass c = f.getDeclaringClass();
                    Map<SootField,EscapeState> cSummary = getClassSummary(c);
                    EquivalentValue yv = init(y, mSummary, changed);
                    
//                    SootClass mClass = m.getDeclaringClass();
//                    if (hasOuterClass(mClass) && getOuterClass(mClass) == c) {
//                        // f is defined in outerclass c and is thus accessed via 
//                        // "this$0.f" so we treat f as not escaping (as if inlined)
//                        return changed[0];
//                    }
                    EscapeState newState = cSummary.get(f).meet(mSummary.get(xv)).meet(mSummary.get(yv));
                    if (updateSummary(m, defSt, cSummary, f, newState)) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, defSt, mSummary, x, xv, newState)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof StaticFieldRef) {
                    // x = C.f
                    StaticFieldRef staticFieldRef = (StaticFieldRef)rval;
                    SootField f = staticFieldRef.getField();
//                    SootClass c = f.getDeclaringClass();
                    if (updateSummary(m, defSt, mSummary, x, xv, EscapeState.EXTERNAL)) {
                        changed[0] = true;
                    }
//                  Logger.println("x=C.f");
//                  Logger.println("C.getNumber(): " + c.getNumber());
                }
                else if (rval instanceof ArrayRef) {
                    // x = y[i]
                    ArrayRef arrRef = (ArrayRef)rval;
                    Local y = (Local)arrRef.getBase();
                    EquivalentValue yv = init(y, mSummary, changed);
                    PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
                    PointsToSet pts = pta.reachingObjects(y);
                    PointsToSet ptsElements = pta.reachingObjectsOfArrayElement(pts);
                    Set<Type> elemTypes = ptsElements.possibleTypes();
                    Set<Type> arrayTypes = pts.possibleTypes();
                    EscapeState escapeMeet = EscapeState.INTERNAL;
                    for (Type type : arrayTypes) {
                        if (!(type instanceof ArrayType)) {
//                            throw new RuntimeException("type " + type + " is not an array type!");
                            // skip type
                        }
                        else {
                            ArrayType aType = (ArrayType)type;
                            Type baseType = aType.baseType;
//                            if (baseType instanceof AnySubType) {
//                                baseType = ((AnySubType)baseType).getBase();
//                            }
                            if (baseType instanceof RefType) {
                                RefType rBaseType = (RefType)baseType;
                                SootClass c = rBaseType.getSootClass();
                                Map<SootField,EscapeState> cSummary = getClassSummary(c);
                                escapeMeet = escapeMeet.meet(cSummary.get(ARRAY_ELEMS_FIELD));
                                if (updateSummary(m, defSt, cSummary, ARRAY_ELEMS_FIELD, cSummary.get(ARRAY_ELEMS_FIELD).meet(mSummary.get(xv)).meet(mSummary.get(yv)))) {
                                    changed[0] = true;
                                }
                            }
                        }
                    }
                    if (updateSummary(m, defSt, mSummary, x, xv, mSummary.get(xv).meet(mSummary.get(yv)).meet(escapeMeet))) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof ThisRef) {
                    // x = @this
                    EquivalentValue thisv = getThisRef(m);
                    EscapeState newState = mSummary.get(xv).meet(mSummary.get(thisv));
                    if (updateSummary(m, defSt, mSummary, x, xv, newState)) {
                        changed[0] = true;
                    }
//                    if (updateSummary(m, mSummary, thisv, newState)) {
//                        changed[0] = true;
//                    }
                }
                else if (rval instanceof ParameterRef) {
                    // x = @pn
                    ParameterRef pRef = (ParameterRef)rval;
                    EquivalentValue pv = getParameterRef(m, pRef.getIndex());
                    EscapeState newState = mSummary.get(xv).meet(mSummary.get(pv));
                    if (updateSummary(m, defSt, mSummary, x, xv, newState)) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, mSummary, pv, newState)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof CaughtExceptionRef) {
                    // x = @caughtexception
                }
            }
            else if (lval instanceof InstanceFieldRef && lval.getType() instanceof RefLikeType/* && lval.getType() != stringType*/) {
                // x.f = blah
                InstanceFieldRef instFieldRef = (InstanceFieldRef)lval;
                Local x = (Local)instFieldRef.getBase();
                EquivalentValue xv = init(x, mSummary, changed);
                SootField f = instFieldRef.getField();
                SootClass c = f.getDeclaringClass();
//                SootClass mClass = m.getDeclaringClass();
//                if (hasOuterClass(mClass) && getOuterClass(mClass) == c) {
//                    // f is defined in outerclass c and is thus accessed via 
//                    // "this$0.f" so we treat f as not escaping (as if inlined)
//                    return changed[0];
//                }
                Map<SootField, EscapeState> cSummary = getClassSummary(c);
                if (rval instanceof Local) {
                    // x.f = y
                    Local y = (Local)rval;
                    EquivalentValue yv = init(y, mSummary, changed);
                    EscapeState newState =  cSummary.get(f).meet(mSummary.get(yv)).meet(mSummary.get(xv));
                    if (updateSummary(m, defSt, cSummary, f, newState)) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, defSt, mSummary, y, yv, newState)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof NullConstant) {
                    // x.f = null
                    if (updateSummary(m, defSt, cSummary, f, cSummary.get(f).meet(mSummary.get(xv)))) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof StringConstant) {
                    // x.f = "";
                    if (updateSummary(m, defSt, cSummary, f, cSummary.get(f).meet(mSummary.get(xv)))) {
                        changed[0] = true;
                    }
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
                    EquivalentValue yv = init(y, mSummary, changed);
                    // c(.f) will be ESCAPE as it is static
                    if (updateSummary(m, defSt, mSummary, y, yv, EscapeState.EXTERNAL)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof NullConstant) {
                    // C.f = null
                    // nothing to do
                }
                else if (rval instanceof StringConstant) {
                    // C.f = ""
                    // nothing to do
                }
            }
            else if (lval instanceof ArrayRef && lval.getType() instanceof RefLikeType) {
                // x[i] = blah
                ArrayRef arrRef = (ArrayRef)lval;
                Local x = (Local)arrRef.getBase();
                EquivalentValue xv = init(x, mSummary, changed);
                PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
                PointsToSet pts = pta.reachingObjects(x);
                Set<Type> types = pts.possibleTypes();
                if (rval instanceof Local) {
                    // x[i] = y
                    Local y = (Local)rval;
                    EquivalentValue yv = init(y, mSummary, changed);
                    EscapeState escapeMeet = EscapeState.INTERNAL;
                    for (Type type : types) {
                        if (!(type instanceof ArrayType)) {
//                            throw new RuntimeException("type " + type + " is not an array type!");
                            // skip
                        }
                        else {
                            ArrayType aType = (ArrayType)type;
                            Type baseType = aType.baseType;
                            if (baseType instanceof RefType) {
                                RefType rBaseType = (RefType)baseType;
                                SootClass c = rBaseType.getSootClass();
                                Map<SootField,EscapeState> cSummary = getClassSummary(c);
                                escapeMeet = escapeMeet.meet(cSummary.get(ARRAY_ELEMS_FIELD));
                                if (updateSummary(m, defSt, cSummary, ARRAY_ELEMS_FIELD, cSummary.get(ARRAY_ELEMS_FIELD).meet(mSummary.get(xv)).meet(mSummary.get(yv)))) {
                                    changed[0] = true;
                                }
                            }
                        }
                    }
                    if (updateSummary(m, defSt, mSummary, y, yv, mSummary.get(yv).meet(mSummary.get(xv)).meet(escapeMeet))) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof NullConstant || rval instanceof StringConstant) {
                    // x[i] = null or x[i] = ""
                    for (Type type : types) {
                        if (!(type instanceof ArrayType)) {
//                            throw new RuntimeException("type " + type + " is not an array type!");
                            // skip
                        }
                        else {
                            ArrayType aType = (ArrayType)type;
                            Type baseType = aType.baseType;
                            if (baseType instanceof RefType) {
                                RefType rBaseType = (RefType)baseType;
                                SootClass c = rBaseType.getSootClass();
                                Map<SootField,EscapeState> cSummary = getClassSummary(c);
                                if (updateSummary(m, defSt, cSummary, ARRAY_ELEMS_FIELD, cSummary.get(ARRAY_ELEMS_FIELD).meet(mSummary.get(xv)))) {
                                    changed[0] = true;
                                }
                            }
                        }
                    }
                }
            }

            // just accesses (non-ref accesses)
//            if(lval instanceof InstanceFieldRef) {
//                InstanceFieldRef instFieldRef = (InstanceFieldRef)lval;
//                Local x = (Local)instFieldRef.getBase();
//            }
//            else if(lval instanceof StaticFieldRef) {
//                StaticFieldRef staticFieldRef = (StaticFieldRef)lval;
//                SootClass c = staticFieldRef.getField().getDeclaringClass();
//            }
//            else if(lval instanceof ArrayRef) {
//                ArrayRef arrRef = (ArrayRef)lval;
//                Local x = (Local)arrRef.getBase();
//            }
//            else if(rval instanceof InstanceFieldRef) {
//                InstanceFieldRef instFieldRef = (InstanceFieldRef)rval;
//                Local x = (Local)instFieldRef.getBase();
//            }
//            else if(rval instanceof StaticFieldRef) {
//                StaticFieldRef staticFieldRef = (StaticFieldRef)rval;
//                SootClass c = staticFieldRef.getField().getDeclaringClass();
//            }
//            else if(rval instanceof ArrayRef) {
//                ArrayRef arrRef = (ArrayRef)rval;
//                Local x = (Local)arrRef.getBase();
//            }
        }
        else if (u instanceof ReturnStmt) {
            ReturnStmt r = (ReturnStmt)u;
            Value val = r.getOp();
            if (val instanceof Local && val.getType() instanceof RefLikeType/* && val.getType() != stringType*/) {
                Local x = (Local)val;
                EquivalentValue xv = init(x, mSummary, changed);
                EquivalentValue rv = getReturnRef(m);
                EscapeState newState = mSummary.get(xv).meet(mSummary.get(rv));
                if (updateSummary(m, r, mSummary, x, xv, newState)) {
                    changed[0] = true;
                }
                if (updateSummary(m, mSummary, rv, newState)) {
                    changed[0] = true;
                }
            }
            else if (val instanceof NullConstant) {
                // no change
            }
            else if (val instanceof StringConstant) {
                // no change
            }
        }
        else if (u instanceof ThrowStmt) {
            // exception variable escapes
            ThrowStmt t = (ThrowStmt)u;
            if (t.getOp() instanceof Local) {
                Local e = (Local)t.getOp();
                EquivalentValue ev = getLocalRef(e);
                if (updateSummary(m, t, mSummary, e, ev, EscapeState.EXTERNAL)) {
                    changed[0] = true;
                }
            }
        }

        // interprocedural propagation
        Stmt s = (Stmt)u;
        if (s.containsInvokeExpr()) {
            InvokeExpr ie = s.getInvokeExpr();
            // x = y.m(a1,...,an) or y.m(a1,...,an)
            CallGraph cg = Scene.v().getCallGraph();
            for (Iterator<Edge> edgesIt=cg.edgesOutOf(u); edgesIt.hasNext(); ) {
                Edge e = edgesIt.next();
                if (DEBUG) Logger.println("tgt: " + e.tgt());
                if (e.isExplicit()) {
                    SootMethod tgt = e.tgt();
                    // if tgt is a safe method, it won't affect the escape state
                    if (isSafeMethod(tgt)) {
                        if (DEBUG) Logger.println(tgt + " is safe");
//                        ProfilerSupport.waitForKeyPress();
                        continue;
                    }
//                    else if (isConstructor(tgt)) {
//                        if (DEBUG) Logger.println(tgt + " is a constructor");
//                        continue;
//                    }
                    else {
                        if (DEBUG) Logger.println("tgt: " + tgt);
                    }
                    if (tgt.isConcrete()) {
                        Map<EquivalentValue,EscapeState> tgtSummary = methodToSummary.get(tgt);

                        // y <-> this
                        EquivalentValue yv = null;
                        if (ie instanceof InstanceInvokeExpr) {
                            InstanceInvokeExpr iie = (InstanceInvokeExpr)ie;
                            Local y = (Local)iie.getBase();
                            yv = init(y, mSummary, changed);
                            // INVARIANT: "this" is always INTERNAL
//                            EquivalentValue thisv = getThisRef(tgt);
//                            EscapeState newState = mSummary.get(yv).meet(tgtSummary.get(thisv));
//                            if (updateSummary(m, mSummary, yv, newState)) {
//                                changed[0] = true;
//                            }
//                            if (updateSummary(tgt, tgtSummary, thisv, newState)) {
//                                changed[0] = true;
//                            }
                        }
                        
                        // if y is external, then return val and all args become
                        // external as well
                        
                        // x <-> @r
                        if (s instanceof DefinitionStmt) {
                            Local x = (Local)((DefinitionStmt)s).getLeftOp();
                            EquivalentValue xv = init(x, mSummary, changed);
                            EquivalentValue rv = getReturnRef(tgt);
                            EscapeState newState = mSummary.get(xv).meet(tgtSummary.get(rv));
                            if (ie instanceof InstanceInvokeExpr) {
                                newState = newState.meet(mSummary.get(yv));
                            }
                            if (updateSummary(m, s, mSummary, x, xv, newState)) {
                                changed[0] = true;
                            }
                            if (updateSummary(tgt, tgtSummary, rv, newState)) {
                                changed[0] = true;
                            }
                        }
                                                
                        // a1,...,an <-> p1,...,pn
                        for (int i=0; i<tgt.getParameterCount(); i++) {
                            Value ai = ie.getArg(i);
                            if (ai instanceof Local) {
                                Local lai = (Local)ai;
                                EquivalentValue aiv = init(lai, mSummary, changed);
                                EquivalentValue piv = getParameterRef(tgt, i);
                                EscapeState newState = tgtSummary.get(piv).meet(mSummary.get(aiv));
                                if (ie instanceof InstanceInvokeExpr && !isHandoverParam(tgt, i)) {
                                    // we only take the meet with the type of the 
                                    // receiver object if this is an instance
                                    // invocation AND this is NOT a handover 
                                    // parameter
                                    newState = newState.meet(mSummary.get(yv));
                                }
                                if (!(i == 0 && isInnerClassConstructor(tgt))) {
                                    // "this" is passed as the first argument from
                                    // the outer class to the inner class constructor
                                    // and then stored in the field "this$0" in the
                                    // inner class. To ensure that "this" and "this$0"
                                    // remain INTERNAL, we don't update the parameter's type,
                                    // however, we do propagate back the type of
                                    // the parameter to the argument
                                    if (updateSummary(tgt, tgtSummary, piv, newState)) {
                                        changed[0] = true;
                                    }
                                }
                                if (updateSummary(m, s, mSummary, lai, aiv, newState)) {
                                    changed[0] = true;
                                }
                                // TODO: check if passing to inner class constructor
                                //       or utility method
                            }
                        }
                        
                    }
                }
            }
        }
        
        return changed[0];
    }

    private boolean isHandoverParam(SootMethod m, int i) {
        TIntList handoverParams = methodToHandoverParams.get(m);
        return handoverParams != null && handoverParams.contains(i);
    }

    private SootClass getOuterClass(SootClass c) {
        String cName = c.getName();
        String outerName = cName.substring(0, cName.length()-2);
//        Logger.println("outer class of " + cName + " is " + outerName);
        return Scene.v().getSootClass(outerName);
    }

    private boolean hasOuterClass(SootClass c) {
        String cName = c.getName();
        return cName.charAt(cName.length()-2) == '$';
    }
    
    private boolean isSafeMethod(SootMethod m) {
//        Logger.println("Checking if " + m + " is safe");
        String msig = m.getSignature();
        for (String sm : safeMethods) {
            if (msig.equals(sm) || msig.contains(sm)) {
                return true;
            }
        }
        return false;
    }

    // lazily construct class summary for c if doesn't already exist
    private Map<SootField, EscapeState> getClassSummary(SootClass c) {
        Map<SootField, EscapeState> summary = classToSummary.get(c);
        if (summary == null) {
            summary = constructClassSummary(c);
            classToSummary.put(c, summary);
        }
        return summary;
    }

//    static String[] watchList = { "rotary.Car: rotary.Driver driver" }; // "elementData", "this$0", "data", "buckets", "entries", "$elem$", "succ", "root", "current", "last" };
    
    private boolean updateSummary(SootMethod m, Stmt s, Map<SootField, EscapeState> summary, SootField key, EscapeState value) {
        EscapeState oldValue = summary.put(key, value);
        boolean changed = oldValue != value;
        if (changed) {
//            G.v().out.println("[lg.ila]             c(" + (key == ARRAY_ELEMS_FIELD ? "$elem" : key) + "): " + oldValue + " -> " + value);
//            for (String f : watchList) {
//                if ((key == ARRAY_ELEMS_FIELD ? "$elem" : key).toString().contains(f)) {
//                    Logger.println(m + " made " + f + " external - " + s);
//                    ProfilerSupport.waitForKeyPress();
//                }
//            }
        }
        return changed;
    }
    
    private boolean updateSummary(SootMethod m, Stmt s, Map<EquivalentValue, EscapeState> summary, Local x, EquivalentValue key, EscapeState value) {
        // only update if not an alias of this
        if (mustAliasesThis(x, m, s)) {
            return false;
        }
        else {
            EscapeState oldValue = summary.put(key, value);
            boolean changed = oldValue != value;
//            if (changed) {
//                G.v().out.println("[lg.ila]             m(" + key + "): " + oldValue + " -> " + value);
//                String var = "r1";
//                if (key.toString().contains(var) && m.getDeclaringClass().getName().contains("Vector$1")) {
//                    Logger.println(var + " just became external");
//                }
//            }
            return changed;
        }
    }

    private boolean updateSummary(SootMethod m, Map<EquivalentValue, EscapeState> summary, EquivalentValue key, EscapeState value) {
        // only update if not an alias of this
        EscapeState oldValue = summary.put(key, value);
        boolean changed = oldValue != value;
//        if (changed) {
//            G.v().out.println("[lg.ila]             m(" + key + "): " + oldValue + " -> " + value);
//            String var = "@parameter0";
//            if (key.toString().contains(var) && m.getDeclaringClass().getName().contains("Vector$")) {
//                Logger.println(var + " just became external");
//            }
//        }
        return changed;
    }
    
    // returns true <-> x is a must-alias of "this" at s
    private boolean mustAliasesThis(Local x, SootMethod m, Stmt s) {
        if (m.isStatic()) {
            return false;
        }
        
//        if (m.getName().equals("clone")) {
//            return true;
//        }
        
        StrongLocalMustAliasAnalysis localAliasAnalysis = methodToLocalAliasAnalysis.get(m);
        if (localAliasAnalysis == null) {
            localAliasAnalysis = new StrongLocalMustAliasAnalysis(new ExceptionalUnitGraph(m.retrieveActiveBody()));
            methodToLocalAliasAnalysis.put(m, localAliasAnalysis);
        }
        Local thisLocal = m.retrieveActiveBody().getThisLocal();
        return localAliasAnalysis.mustAlias(thisLocal, s, x, s);
    }

    // returns null <-> summary didn't previously have a mapping for x
    private EquivalentValue init(Local x, Map<EquivalentValue, EscapeState> summary, boolean[] changed) {
        EquivalentValue xv = getLocalRef(x);
        if (!summary.containsKey(xv)) {
            summary.put(xv, EscapeState.INTERNAL);
            if (DEBUG) G.v().out.println("[lg.ila]             m(" + xv + "): " + EscapeState.INTERNAL);
            changed[0] = true;
        }
        return xv;
    }

    private EquivalentValue getLocalRef(Local l) {
        return new EquivalentValue(l);
    }
    
    private EquivalentValue getThisRef(SootMethod m) {
        return new EquivalentValue(new ThisRef(m.getDeclaringClass().getType()));
    }
    
    private EquivalentValue getParameterRef(SootMethod m, int i) {
        return new EquivalentValue(new ParameterRef(m.getParameterType(i), i));
    }

    private EquivalentValue getReturnRef(SootMethod m) {
        return new EquivalentValue(new ParameterRef(m.getReturnType(), -1));
    }

}
