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

import lg.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.*;
// flow-insensitive escape analysis
public class ClassLocalAnalysisTransformer extends SceneTransformer {

    enum ClassEscapeState {

        // External < Local
        LOCAL (2) { public String toString() { return "Local"; } },
        EXTERNAL (1) { public String toString() { return "External"; } };
        
        int id;
        ClassEscapeState(int i) {
            id = i;
        }
        
        ClassEscapeState meet(ClassEscapeState s) {
            if (this.id <= s.id) {
                return this;
            }
            else {
                return s;
            }
        }
    }
    
    private static SootField ARRAY_ELEMS_FIELD;
    
    Map<SootClass, Map<SootField,ClassEscapeState>> classToSummary;
    Map<SootMethod, Map<EquivalentValue,ClassEscapeState>> methodToSummary;
    
    public static boolean DEBUG = false;
    
    public ClassLocalAnalysisTransformer() {
        classToSummary = new HashMap<SootClass, Map<SootField,ClassEscapeState>>();
        methodToSummary = new HashMap<SootMethod, Map<EquivalentValue,ClassEscapeState>>();
    }
    
    public void outputResults(SootClass c) {
        G.v().out.println("[lg.cla] Escape states for static fields in " + c);
        Map<SootField, ClassEscapeState> cSummary = getClassSummary(c);
        for (SootField f : c.getFields()) {
            if (f.isStatic()) {
                G.v().out.println("[lg.cla]         " + f.getName() + ": " + cSummary.get(f));
            }
        }
        G.v().out.println();
    }
    
    public void outputResults(SootMethod m) {
        Map<EquivalentValue,ClassEscapeState> mSummary = methodToSummary.get(m);
        G.v().out.println("[lg.cla] Escape states for {this,params,return} in " + m);
        for (EquivalentValue ev : mSummary.keySet()) {
            G.v().out.println("[lg.cla]         " + ev + ": " + mSummary.get(ev));
        }
    }
   
    
    public void doAnalysis() {
        G.v().out.println("[wjtp.cla] class local analysis running");
        internalTransform(null, null);
    }
    
    // iterate through all methods until there is no change
    protected void internalTransform(String phaseName, Map options) {
        
        ARRAY_ELEMS_FIELD = new SootField("$elem$", NullType.v());
        
        Set<SootMethod> methods = new HashSet<SootMethod>();
        Set<SootClass> classes = new HashSet<SootClass>();
        
        List<SootMethod> entryPoints = EntryPoints.v().methodsOfApplicationClasses();
        TransitiveTargets tt = new TransitiveTargets(Scene.v().getCallGraph(), new Filter(new ExplicitEdgesPred()));
        for (SootMethod entryPoint : entryPoints) {
            methods.add(entryPoint);
            classes.add(entryPoint.getDeclaringClass());
            for (Iterator<MethodOrMethodContext> ttIt = tt.iterator(entryPoint); ttIt.hasNext(); ) {
                SootMethod t = ttIt.next().method();
                if (t.isConcrete()) { //throw new AssertionError("method " + t + " is not concrete!");
                    methods.add(t);
                }
                // even if method is "interface" or "abstract" still add class
                // because may have arrays of it's type and the classes may also
                // have static fields.
                classes.add(t.getDeclaringClass());
            }
        }

        // build initial per-class summaries
        for (SootClass c : classes) {
            classToSummary.put(c, constructClassSummary(c));
        }
        
        // want to build summaries for all classes referenced in methods
        
        // build initial per-method summaries
        for (SootMethod m : methods) {
            // initial assumption is that:
            // for private methods: return is LOCAL
            // for all other: this, params, return are all EXTERNAL
            Map<EquivalentValue, ClassEscapeState> summary = new HashMap<EquivalentValue, ClassLocalAnalysisTransformer.ClassEscapeState>();
            
            summary.put(getThisRef(m), ClassEscapeState.LOCAL); // "this" is always local and "params" are always external
            for (int i=0; i<m.getParameterCount(); i++) {
                summary.put(getParameterRef(m, i), ClassEscapeState.EXTERNAL);
            }
//            if (m.getReturnType() != VoidType.v()) {
            if (m.getReturnType() != VoidType.v()) {
                ClassEscapeState state = m.isPrivate() ? ClassEscapeState.LOCAL : ClassEscapeState.EXTERNAL;
                summary.put(getReturnRef(m), state);
            }
            
            methodToSummary.put(m, summary);
        }
        
        G.v().out.println("[wjtp.cla] Starting class escape analysis of " + methods.size() + " methods, " + classes.size() + " classes");
        
        boolean changed = false;
        long iterationCount = 0;
        do {
            changed = false;
            iterationCount++;
            if (DEBUG) G.v().out.println("[lg.cla] *******************************");
            if (DEBUG) G.v().out.println("[lg.cla] Iteration: " + iterationCount);
            if (DEBUG) G.v().out.println("[lg.cla] *******************************");
            for (SootMethod m : methods) {
//                DEBUG = m.getSignature().equals("<java.util.Vector: void removeAllElements()>"); // && m.getDeclaringClass().toString().equals("java.util.Vector");
                if (DEBUG) G.v().out.println("[lg.cla] Current method: " + m);
                Map<EquivalentValue,ClassEscapeState> summary = methodToSummary.get(m);
                for (Unit u : m.retrieveActiveBody().getUnits()) {
                    if (DEBUG) G.v().out.println("[lg.cla]     u: " + u);
                    // apply transfer function to update m's summary and possibly other method and class summaries
                    if (DEBUG) G.v().out.println("[lg.cla]         state before: " + summary);
                    if (applyTransferFunction(u, m, summary)) {
                        changed = true;
                    }
                    if (DEBUG) G.v().out.println();
                    if (DEBUG) ProfilerSupport.waitForKeyPress();
                }
            }
        }
        while (changed);
        
        G.v().out.println("[wjtp.cla] Finished escape analysis in " + iterationCount + " iterations, outputting results for application classes.");
        
        // output results
        for (SootClass c : classes) {
            if (c.isApplicationClass()) {
                outputResults(c);
            }
        }
        
        methodToSummary.clear();
        methodToSummary = null;
    }
    
    private Map<SootField, ClassEscapeState> constructClassSummary(SootClass c) {
        Map<SootField,ClassEscapeState> summary = new HashMap<SootField,ClassEscapeState>();
        for (SootField f : c.getFields()) {
            if (f.isStatic()) {
                summary.put(f, ClassEscapeState.LOCAL);
            }
            else {
                summary.put(f, ClassEscapeState.EXTERNAL);
            }
        }
        summary.put(ARRAY_ELEMS_FIELD, ClassEscapeState.EXTERNAL); // for representing array accesses on arrays of type c
        return summary;
    }

    private boolean applyTransferFunction(Unit u, SootMethod m, Map<EquivalentValue,ClassEscapeState> mSummary) {
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
                    ClassEscapeState newState = mSummary.get(xv).meet(mSummary.get(yv));
                    if (updateSummary(m, mSummary, xv, newState)) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, mSummary, yv, newState)) {
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
                        ClassEscapeState newState = mSummary.get(xv).meet(mSummary.get(yv));
                        if(updateSummary(m, mSummary, xv, newState)) {
                            changed[0] = true;
                        }
                        if (updateSummary(m, mSummary, yv, newState)) {
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
                    Map<SootField,ClassEscapeState> cSummary = getClassSummary(c);
                    EquivalentValue yv = init(y, mSummary, changed);
                    
//                    SootClass mClass = m.getDeclaringClass();
//                    if (hasOuterClass(mClass) && getOuterClass(mClass) == c) {
//                        // f is defined in outerclass c and is thus accessed via 
//                        // "this$0.f" so we treat f as not escaping (as if inlined)
//                        return changed[0];
//                    }
                    if (updateSummary(m, cSummary, f, cSummary.get(f).meet(mSummary.get(yv)))) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, cSummary, f, cSummary.get(f).meet(mSummary.get(xv)))) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, mSummary, xv, mSummary.get(xv).meet(cSummary.get(f)))) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof StaticFieldRef) {
                    // x = C.f
                    StaticFieldRef staticFieldRef = (StaticFieldRef)rval;
                    SootField f = staticFieldRef.getField();
                    SootClass c = f.getDeclaringClass();
                    Map<SootField,ClassEscapeState> cSummary = getClassSummary(c);
                    if (updateSummary(m, cSummary, f, cSummary.get(f).meet(mSummary.get(xv)))) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, mSummary, xv, mSummary.get(xv).meet(cSummary.get(f)))) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof ArrayRef) {
                    // x = y[i]
                    ArrayRef arrRef = (ArrayRef)rval;
                    Local y = (Local)arrRef.getBase();
//                    EquivalentValue yv = init(y, mSummary, changed);
//                    PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
//                    PointsToSet pts = pta.reachingObjects(y);
//                    Set<Type> types = pts.possibleTypes();
//                    ClassEscapeState escapeMeet = ClassEscapeState.LOCAL;
//                    for (Type type : types) {
//                        if (!(type instanceof ArrayType)) {
////                            throw new RuntimeException("type " + type + " is not an array type!");
//                            // skip type
//                        }
//                        else {
//                            ArrayType aType = (ArrayType)type;
//                            Type baseType = aType.baseType;
////                            if (baseType instanceof AnySubType) {
////                                baseType = ((AnySubType)baseType).getBase();
////                            }
//                            if (baseType instanceof RefType) {
//                                RefType rBaseType = (RefType)baseType;
//                                SootClass c = rBaseType.getSootClass();
//                                Map<SootField,ClassEscapeState> cSummary = getClassSummary(c);
//                                escapeMeet = escapeMeet.meet(cSummary.get(ARRAY_ELEMS_FIELD));
//                                if (updateSummary(m, cSummary, ARRAY_ELEMS_FIELD, cSummary.get(ARRAY_ELEMS_FIELD).meet(mSummary.get(xv)).meet(mSummary.get(yv)))) {
//                                    changed[0] = true;
//                                }
//                            }
//                        }
//                    }
                    // we know that array elements are always external, so
                    // we just need to make x external
                    if (updateSummary(m, mSummary, xv, ClassEscapeState.EXTERNAL)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof ThisRef) {
                    // x = @this
                    EquivalentValue thisv = getThisRef(m);
                    ClassEscapeState newState = mSummary.get(xv).meet(mSummary.get(thisv));
                    if (updateSummary(m, mSummary, xv, newState)) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, mSummary, thisv, newState)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof ParameterRef) {
                    // x = @pn
                    ParameterRef pRef = (ParameterRef)rval;
                    EquivalentValue pv = getParameterRef(m, pRef.getIndex());
                    ClassEscapeState newState = mSummary.get(xv).meet(mSummary.get(pv));
                    if (updateSummary(m, mSummary, xv, newState)) {
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
//                Map<SootField, ClassEscapeState> cSummary = getClassSummary(c);
//                if (updateSummary(m, cSummary, f, cSummary.get(f).meet(mSummary.get(xv)))) {
//                    changed[0] = true;
//                }
                if (rval instanceof Local) {
                    // x.f = y
                    Local y = (Local)rval;
                    EquivalentValue yv = init(y, mSummary, changed);
//                    if (updateSummary(m, cSummary, f, cSummary.get(f).meet(mSummary.get(yv)))) {
//                        changed[0] = true;
//                    }
//                    // update y iff y != this
//                    if (!mustAliasesThis(y, m, defSt)) {
//                        if (updateSummary(m, mSummary, yv, mSummary.get(yv).meet(cSummary.get(f)))) {
//                            changed[0] = true;
//                        }
//                    }
                    // instance fields are always EXTERNAL, so just update y
                    if (updateSummary(m, mSummary, yv, ClassEscapeState.EXTERNAL)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof NullConstant) {
                    // x.f = null
                    // nothing to do
                }
                else if (rval instanceof StringConstant) {
                    // x.f = "";
                    // nothing to do
                }
            }
            else if (lval instanceof StaticFieldRef && lval.getType() instanceof RefLikeType/* && lval.getType() != stringType*/) {
                // C.f = blah
                StaticFieldRef staticFieldRef = (StaticFieldRef)lval;
                SootField f = staticFieldRef.getField();
                SootClass c = f.getDeclaringClass();
                Map<SootField,ClassEscapeState> cSummary = getClassSummary(c);
                if (rval instanceof Local) {
                    // C.f = y
                    Local y = (Local)rval;
                    EquivalentValue yv = init(y, mSummary, changed);
                    if (updateSummary(m, cSummary, f, cSummary.get(f).meet(mSummary.get(yv)))) {
                        changed[0] = true;
                    }
                    if (updateSummary(m, mSummary, yv, mSummary.get(yv).meet(cSummary.get(f)))) {
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
//                    ClassEscapeState escapeMeet = ClassEscapeState.LOCAL;
//                    for (Type type : types) {
//                        if (!(type instanceof ArrayType)) {
////                            throw new RuntimeException("type " + type + " is not an array type!");
//                            // skip
//                        }
//                        else {
//                            ArrayType aType = (ArrayType)type;
//                            Type baseType = aType.baseType;
//                            if (baseType instanceof RefType) {
//                                RefType rBaseType = (RefType)baseType;
//                                SootClass c = rBaseType.getSootClass();
//                                Map<SootField,ClassEscapeState> cSummary = getClassSummary(c);
//                                escapeMeet = escapeMeet.meet(cSummary.get(ARRAY_ELEMS_FIELD));
//                                if (updateSummary(m, cSummary, ARRAY_ELEMS_FIELD, cSummary.get(ARRAY_ELEMS_FIELD).meet(mSummary.get(xv)).meet(mSummary.get(yv)))) {
//                                    changed[0] = true;
//                                }
//                            }
//                        }
//                    }
                    // array accesses are EXTERNAL, so just update y
                    if (updateSummary(m, mSummary, yv, ClassEscapeState.EXTERNAL)) {
                        changed[0] = true;
                    }
                }
                else if (rval instanceof NullConstant || rval instanceof StringConstant) {
                    // x[i] = null or x[i] = ""
//                    ClassEscapeState escapeMeet = ClassEscapeState.LOCAL;
//                    for (Type type : types) {
//                        if (!(type instanceof ArrayType)) {
////                            throw new RuntimeException("type " + type + " is not an array type!");
//                            // skip
//                        }
//                        else {
//                            ArrayType aType = (ArrayType)type;
//                            Type baseType = aType.baseType;
//                            if (baseType instanceof RefType) {
//                                RefType rBaseType = (RefType)baseType;
//                                SootClass c = rBaseType.getSootClass();
//                                Map<SootField,ClassEscapeState> cSummary = getClassSummary(c);
//                                escapeMeet = escapeMeet.meet(cSummary.get(ARRAY_ELEMS_FIELD));
//                                if (updateSummary(m, cSummary, ARRAY_ELEMS_FIELD, cSummary.get(ARRAY_ELEMS_FIELD).meet(mSummary.get(xv)))) {
//                                    changed[0] = true;
//                                }
//                            }
//                        }
//                    }
                    // nothing to do
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
                ClassEscapeState newState = mSummary.get(xv).meet(mSummary.get(rv));
                if (updateSummary(m, mSummary, xv, newState)) {
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
                if (updateSummary(m, mSummary, ev, ClassEscapeState.EXTERNAL)) {
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
//                    if (isSafeMethod(tgt)) {
//                        if (DEBUG) Logger.println(tgt + " is safe");
////                        ProfilerSupport.waitForKeyPress();
//                        continue;
//                    }
//                    else if (isConstructor(tgt)) {
//                        if (DEBUG) Logger.println(tgt + " is a constructor");
//                        continue;
//                    }
//                    else {
//                        if (DEBUG) Logger.println("tgt: " + tgt);
//                    }
                    if (tgt.isConcrete()) {
                        Map<EquivalentValue,ClassEscapeState> tgtSummary = methodToSummary.get(tgt);

                        // x <-> @r
                        if (s instanceof DefinitionStmt) {
                            Local x = (Local)((DefinitionStmt)s).getLeftOp();
                            EquivalentValue xv = init(x, mSummary, changed);
                            EquivalentValue rv = getReturnRef(tgt);
                            if (updateSummary(m, mSummary, xv, mSummary.get(xv).meet(tgtSummary.get(rv)))) {
                                changed[0] = true;
                            }
                            if (updateSummary(tgt, tgtSummary, rv, tgtSummary.get(rv).meet(mSummary.get(xv)))) {
                                changed[0] = true;
                            }
                        }
                        
                        // y <-> this
                        EquivalentValue yv = null;
                        if (ie instanceof InstanceInvokeExpr) {
                            InstanceInvokeExpr iie = (InstanceInvokeExpr)ie;
                            Local y = (Local)iie.getBase();
                            yv = init(y, mSummary, changed);
                            EquivalentValue thisv = getThisRef(tgt);
                            if (updateSummary(m, mSummary, yv, mSummary.get(yv).meet(tgtSummary.get(thisv)))) {
                                changed[0] = true;
                            }
                            // "this" always remains LOCAL, hence update is unidirectional
                        }
                        
                        // a1,...,an <-> p1,...,pn
                        // if y is external, then all args become external as well
                        for (int i=0; i<tgt.getParameterCount(); i++) {
                            Value ai = ie.getArg(i);
                            if (ai instanceof Local) {
                                Local lai = (Local)ai;
                                EquivalentValue aiv = init(lai, mSummary, changed);
                                EquivalentValue piv = getParameterRef(tgt, i);
                                if (updateSummary(tgt, tgtSummary, piv, tgtSummary.get(piv).meet(mSummary.get(aiv)))) {
                                    changed[0] = true;
                                }
                                if (ie instanceof InstanceInvokeExpr) {
                                    if (updateSummary(m, mSummary, aiv, mSummary.get(aiv).meet(tgtSummary.get(piv)))) {
                                        changed[0] = true;
                                    }
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

    // lazily construct class summary for c if doesn't already exist
    private Map<SootField, ClassEscapeState> getClassSummary(SootClass c) {
        Map<SootField, ClassEscapeState> summary = classToSummary.get(c);
        if (summary == null) {
            summary = constructClassSummary(c);
            classToSummary.put(c, summary);
        }
        return summary;
    }

//    static String[] watchList = { "carsList" }; // "elementData", "this$0", "data", "buckets", "entries", "$elem$", "succ", "root", "current", "last" };
    
    private boolean updateSummary(SootMethod m, Map<SootField, ClassEscapeState> summary, SootField key, ClassEscapeState value) {
        ClassEscapeState oldValue = summary.put(key, value);
        boolean changed = oldValue != value;
        if (changed) {
            G.v().out.println("[lg.cla]             c(" + (key == ARRAY_ELEMS_FIELD ? "$elem" : key) + "): " + oldValue + " -> " + value);
//            for (String f : watchList) {
//                if (key.getName().contains(f)/* && m.getDeclaringClass().getName().contains("TreeMap")*/) {
//                    Logger.println(m + " made " + f + " external");
//                    ProfilerSupport.waitForKeyPress();
//                }
//            }
        }
        return changed;
    }

    private boolean updateSummary(SootMethod m, Map<EquivalentValue, ClassEscapeState> summary, EquivalentValue key, ClassEscapeState value) {
        ClassEscapeState oldValue = summary.put(key, value);
        boolean changed = oldValue != value;
        if (changed) {
//            G.v().out.println("[lg.cla]             m(" + key + "): " + oldValue + " -> " + value);
            String var = "r0";
            if (key.toString().equals(var) && m.toString().equals("<java.util.LinkedHashMap$LinkedHashEntry: void access()>")) {
                Logger.println(var + " just became external");
            }
        }
        return changed;
    }

    // returns true <-> x is a must-alias of "this" at s
//    private boolean mustAliasesThis(Local x, SootMethod m, Stmt s) {
//        if (m.isStatic()) {
//            return false;
//        }
//        
//        if (m.getName().equals("clone")) {
//            return true;
//        }
//        
//        StrongLocalMustAliasAnalysis localAliasAnalysis = methodToLocalAliasAnalysis.get(m);
//        if (localAliasAnalysis == null) {
//            localAliasAnalysis = new StrongLocalMustAliasAnalysis(new ExceptionalUnitGraph(m.retrieveActiveBody()));
//            methodToLocalAliasAnalysis.put(m, localAliasAnalysis);
//        }
//        Local thisLocal = m.retrieveActiveBody().getThisLocal();
//        return localAliasAnalysis.mustAlias(thisLocal, s, x, s);
//    }

    // returns null <-> summary didn't previously have a mapping for x
    private EquivalentValue init(Local x, Map<EquivalentValue, ClassEscapeState> summary, boolean[] changed) {
        EquivalentValue xv = getLocalRef(x);
        if (!summary.containsKey(xv)) {
            summary.put(xv, ClassEscapeState.LOCAL);
            if (DEBUG) G.v().out.println("[lg.cla]             m(" + xv + "): " + ClassEscapeState.LOCAL);
            changed[0] = true;
        }
        return xv;
    }

    public boolean isLocal(SootField f) {
        SootClass c = f.getDeclaringClass();
        Map<SootField, ClassEscapeState> cSummary = getClassSummary(c);
        if (cSummary == null) {
//            throw new IllegalArgumentException("Class " + c + " does not have a summary (" + f + ")");
            return false;
        }
        else {
            return cSummary.get(f) == ClassEscapeState.LOCAL;
        }
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
