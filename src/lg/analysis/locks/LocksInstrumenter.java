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

import lg.analysis.paths.LockSet;
import lg.analysis.paths.transformer.*;
import lg.analysis.paths.transformer.fast.*;
import lg.cfg.AtomicSection;
import lg.transformer.AtomicTransformer;
import lg.util.*;
import soot.*;
import soot.jimple.*;
import soot.util.*;

public class LocksInstrumenter {

    AtomicSection atomic;
    LockSet locks;

    int counter;
    Jimple jimpleFactory;
    SootClass synchroniser;
    
    boolean globalLock;
    boolean manualLocks;
    
    public LocksInstrumenter(AtomicSection a, LockSet l, boolean gl, boolean ml) {
        atomic = a;
        locks = l;
        counter = 0;
        jimpleFactory = Jimple.v();
        synchroniser = AtomicTransformer.JUC ? Scene.v().getSootClass("java.util.concurrent.locks.multi.AtomicSynchroniser") : Scene.v().getSootClass("lg.runtime.AtomicSynchroniser");
        globalLock = gl;
        manualLocks = ml;
    }
    
    public void instrument() {
        Pair<Set<Lock>,Set<Lock>> typeInstanceLocks = locks.separateLocks();
        Set<Lock> typeLocks = typeInstanceLocks.getFirst();
        Set<Lock> pathLocks = typeInstanceLocks.getSecond();
        
        SootMethod enterAtomic = null;
        if (globalLock) {
            enterAtomic = synchroniser.getMethodByName("enterAtomicGlobal");
        }
        else if (manualLocks) {
            enterAtomic = synchroniser.getMethodByName("enterAtomicManual");
        }
        else {
            enterAtomic = synchroniser.getMethodByName("enterAtomic");
        }
        
        Chain<Unit> lockingCode = new HashChain<Unit>();
        
        List<Value> enterAtomicArgs = new ArrayList<Value>();
        if (manualLocks) {
            Local monitorLocal = atomic.getMonitorLocal();
            enterAtomicArgs.add(monitorLocal);
        }
        InvokeExpr invokeEnterAtomicExpr = jimpleFactory.newStaticInvokeExpr(enterAtomic.makeRef(), enterAtomicArgs);
        InvokeStmt invokeEnterAtomic = jimpleFactory.newInvokeStmt(invokeEnterAtomicExpr);

        lockingCode.add(invokeEnterAtomic);
        
        PatchingChain<Unit> atomicChain = atomic.getBody().getUnits();
        Unit firstAtomicUnit = atomic.getHeads().get(0);
        if (firstAtomicUnit instanceof IdentityStmt) {
            for (Iterator<Unit> unitsIt=atomicChain.iterator(); unitsIt.hasNext();) {
                Unit u = unitsIt.next();
                if (u instanceof IdentityStmt) {
                    continue;
                }
                else {
                    firstAtomicUnit = u;
                    break;
                }
            }
        }
        
        // locking code
        Unit fakeFirstAtomicUnit = jimpleFactory.newNopStmt();
        atomicChain.insertBeforeNoRedirect(fakeFirstAtomicUnit, firstAtomicUnit);

        Local isOuterAtomicLocal = null;
        SootMethod isOuterAtomic = null;
        StaticInvokeExpr isOuterAtomicExpr = null;
        AssignStmt isOuterAtomicAssign = null;
        IfStmt ifOuterAtomic = null;
        
        if (!globalLock && !manualLocks) {
        
            // check if this is an outermost atomic
            isOuterAtomicLocal = jimpleFactory.newLocal("$isOuterAtomic", BooleanType.v());
            atomic.getBody().getLocals().add(isOuterAtomicLocal);
            isOuterAtomic = synchroniser.getMethodByName("isOuterAtomic");
            isOuterAtomicExpr = jimpleFactory.newStaticInvokeExpr(isOuterAtomic.makeRef());
            isOuterAtomicAssign = jimpleFactory.newAssignStmt(isOuterAtomicLocal, isOuterAtomicExpr);
            ifOuterAtomic = jimpleFactory.newIfStmt(jimpleFactory.newEqExpr(isOuterAtomicLocal, IntConstant.v(0)), firstAtomicUnit);
            lockingCode.add(isOuterAtomicAssign);
            lockingCode.add(ifOuterAtomic);
    
            Unit firstLockingUnit = jimpleFactory.newNopStmt();
            lockingCode.add(firstLockingUnit);
    
            // type locks
            for (Lock l : typeLocks) {
                TypeLock tl = (TypeLock)l;
                Type t = tl.getType();
                TypeSwitch ts = new TypeSwitch() {
                    @Override
                    public void caseRefType(RefType rt) {
                        SootClass c = rt.getSootClass();
                        setResult(c.getName());
                    }
                    
                    @Override
                    public void caseAnySubType(AnySubType ast) {
                        RefType rt = ast.getBase();
                        SootClass c = rt.getSootClass();
                        setResult(c.getName());
                    }
                    
                    @Override
                    public void caseArrayType(ArrayType at) {
                        Type base = at.baseType;
                        int dim = at.numDimensions;
                        String classConstant = "";
                        for (int i=0; i<dim; i++) {
                            classConstant += "[";
                        }
                        TypeSwitch ts = new TypeSwitch() {
                            @Override
                            public void caseBooleanType(BooleanType t) {
                                setResult("Z");
                            }
    
                            @Override
                            public void caseByteType(ByteType t) {
                                setResult("B");
                            }
    
                            @Override
                            public void caseCharType(CharType t) {
                                setResult("C");
                            }
    
                            @Override
                            public void caseDoubleType(DoubleType t) {
                                setResult("D");
                            }
    
                            @Override
                            public void caseFloatType(FloatType t) {
                                setResult("F");
                            }
    
                            @Override
                            public void caseIntType(IntType t) {
                                setResult("I");
                            }
    
                            @Override
                            public void caseLongType(LongType t) {
                                setResult("J");
                            }
    
                            @Override
                            public void caseRefType(RefType t) {
                                SootClass c = t.getSootClass();
                                setResult("L" + c.getName() + ";"); 
                            }
    
                            @Override
                            public void caseShortType(ShortType t) {
                                setResult("S");
                            }
    
                            @Override
                            public void defaultCase(Type t) {
                                throw new UnsupportedOperationException("array base type " + t + " is not supported");
                            }
                            
                        };
                        base.apply(ts);
                        classConstant += (String)ts.getResult();
                        //classConstant += ";";
                        setResult(classConstant);
                    }
                    
                    @Override
                    public void defaultCase(Type t) {
                        throw new UnsupportedOperationException("could not generate locking code for " + t);
                    }
                };
    //            if (t instanceof RefType) {
    //                RefType rt = (RefType)t;
    //            }
    //            else if (t instanceof AnySubType){
    //                AnySubType ast = (AnySubType)t;
    //                RefType rt = ast.getBase();
    //                SootClass c = rt.getSootClass();
    //                classConstant = c.getName();
    //            }
    //            else if (t instanceof ArrayType) {
    //                // Class constants for arrays are constructed as follows
    //                // String     --> class "java/lang/String"
    //                // String[]   --> class "[Ljava/lang/String;"
    //                // String[][] --> class "[[Ljava/lang/String;"
    //                ArrayType at = (ArrayType)t;
    //                Type base = at.baseType;
    //                int dim = at.numDimensions;
    //                for (int i=0; i<dim; i++) {
    //                    classConstant += "[";
    //                }
    //                classConstant += "L";
    //                if (base instanceof RefType) {
    //                    RefType rt = (RefType)base;
    //                    SootClass c = rt.getSootClass();
    //                    classConstant += c.getName();
    //                    classConstant += ";";
    //                }
    //                else {
    //                    throw new UnsupportedOperationException("array base type " + base + " is not supported");
    //                }
    //            }
    //            else {
    //                throw new UnsupportedOperationException("could not generate locking code for " + t);
    //            }
                t.apply(ts);
                String classConstant = (String)ts.getResult();
                
                Local classLocal = jimpleFactory.newLocal("$class" + counter, RefType.v("java.lang.Class"));
                atomic.getBody().getLocals().add(classLocal);
                AssignStmt classAssign = jimpleFactory.newAssignStmt(classLocal, ClassConstant.v(classConstant.replace('.', '/')));
                lockingCode.add(classAssign);
                
                if (tl.willBeAcquired()) {
                    SootMethod lock = tl.isWrite() ? synchroniser.getMethodByName("lockTypeWrite") : synchroniser.getMethodByName("lockTypeRead");
                    StaticInvokeExpr lockExpr = jimpleFactory.newStaticInvokeExpr(lock.makeRef(), classLocal);
                    Local lockedLocal = jimpleFactory.newLocal("$locked" + counter, BooleanType.v());
                    atomic.getBody().getLocals().add(lockedLocal);
                    AssignStmt lockedAssign = jimpleFactory.newAssignStmt(lockedLocal, lockExpr);
                    IfStmt ifLocked = jimpleFactory.newIfStmt(jimpleFactory.newEqExpr(lockedLocal, IntConstant.v(0)), firstLockingUnit);
                    lockingCode.add(lockedAssign);
                    lockingCode.add(ifLocked);
                }
    //            else if (tl.isReadOnly()) {
    //                Logger.println("not instrumenting read only lock " + tl);
    //            }
                
                counter++;
            }
            
            Chain<Unit> instLockCode = instanceLockingCode(pathLocks, firstAtomicUnit, firstLockingUnit);
            lockingCode.addAll(instLockCode);
            
        }
        
        atomicChain.insertBefore(lockingCode, fakeFirstAtomicUnit);
        
        for (Unit t : atomic.getTails()) {
            if (globalLock) {
                SootMethod exitAtomicGlobal = synchroniser.getMethodByName("exitAtomicGlobal");
                StaticInvokeExpr exitAtomicGlobalExpr = jimpleFactory.newStaticInvokeExpr(exitAtomicGlobal.makeRef());
                InvokeStmt exitAtomicGlobalStmt = jimpleFactory.newInvokeStmt(exitAtomicGlobalExpr);
                try {
                    atomicChain.insertBefore(exitAtomicGlobalStmt, t);
                } catch (Exception e) {
                    e.printStackTrace();
                    Logger.println("gt: " + t);
                }
            }
            else if (manualLocks) {
                SootMethod exitAtomicManual = synchroniser.getMethodByName("exitAtomicManual");
                StaticInvokeExpr exitAtomicManualExpr = jimpleFactory.newStaticInvokeExpr(exitAtomicManual.makeRef());
                InvokeStmt exitAtomicManualStmt = jimpleFactory.newInvokeStmt(exitAtomicManualExpr);
                try {
                    atomicChain.insertBefore(exitAtomicManualStmt, t);
                } catch (Exception e) {
                    e.printStackTrace();
                    Logger.println("mt: " + t + ", does chain contain? " + atomicChain.contains(t));
                    Logger.println("tails: " + atomic.getTails());
                    Logger.println("contents of chain for " + atomic.getBody().getMethod() + ":");
                    for (Unit u : atomicChain) {
                        Logger.println("   u: " + u);
                    }
                }
            }
            else {
                SootMethod unlockAll = synchroniser.getMethodByName("unlockAll");
                StaticInvokeExpr unlockAllExpr = jimpleFactory.newStaticInvokeExpr(unlockAll.makeRef());
                InvokeStmt unlockAllStmt = jimpleFactory.newInvokeStmt(unlockAllExpr);
    
                SootMethod exitAtomic = synchroniser.getMethodByName("exitAtomic");
                StaticInvokeExpr exitAtomicExpr = jimpleFactory.newStaticInvokeExpr(exitAtomic.makeRef());
                InvokeStmt exitAtomicStmt = jimpleFactory.newInvokeStmt(exitAtomicExpr);
                
                isOuterAtomicExpr = jimpleFactory.newStaticInvokeExpr(isOuterAtomic.makeRef());
                isOuterAtomicAssign = jimpleFactory.newAssignStmt(isOuterAtomicLocal, isOuterAtomicExpr);
                ifOuterAtomic = jimpleFactory.newIfStmt(jimpleFactory.newEqExpr(isOuterAtomicLocal, IntConstant.v(0)), exitAtomicStmt);
                
                atomicChain.insertBefore(isOuterAtomicAssign, t);
                atomicChain.insertBefore(ifOuterAtomic, t);
                atomicChain.insertBefore(unlockAllStmt, t);
                atomicChain.insertBefore(exitAtomicStmt, t);
            }
        }
        
        // do tail-swapping separately because multiple atomics may have
        // the same tail (i.e. if we are also finding inner sync blocks).
        for (Unit t : atomic.getTails()) {
            try {
                atomicChain.swapWith(t, jimpleFactory.newNopStmt());
            }
            catch (Exception e) {
                // silently ignore
            }
        }
        
        for (Unit h : atomic.getHeads()) {
            atomicChain.swapWith(h, jimpleFactory.newNopStmt());
        }
        
    }

    
    private Chain<Unit> instanceLockingCode(Set<? extends Lock> pathLocks, Unit firstUnitAfterInstanceLockingCode, Unit firstLockingUnit) {
        List<PathLock> pathLocksList = new ArrayList<PathLock>((Set<PathLock>)pathLocks);
        Map<PathLock,Unit> pathLockToFirstUnit = new HashMap<PathLock, Unit>();
        Map<PathLock,Unit> pathLockToIdxUnit = new HashMap<PathLock, Unit>();
        Map<PathLock,Local> pathLockToLocal = new HashMap<PathLock, Local>();
        Map<PathLock,Unit> pathLockToTypeCheck = new HashMap<PathLock, Unit>();
        Chain<Unit> code = instanceLockingCodeHelper(firstUnitAfterInstanceLockingCode, firstLockingUnit, pathLocksList, pathLockToFirstUnit, pathLockToLocal, pathLockToIdxUnit, null, new HashMap<String,Local>(), pathLockToTypeCheck);
        
        // insert null checks
        pathLocksList = new ArrayList<PathLock>((Set<PathLock>)pathLocks);
        insertNullAndTypeChecks(pathLocksList, pathLockToFirstUnit, pathLockToLocal, pathLockToIdxUnit, pathLockToTypeCheck, code);
        
        return code;
    }

    private void insertNullAndTypeChecks(List<PathLock> locks, Map<PathLock, Unit> lockToFirstUnit, Map<PathLock, Local> lockToLocal, Map<PathLock, Unit> lockToIdxUnit, Map<PathLock, Unit> lockToTypeCheck, Chain<Unit> code) {
        if (!locks.isEmpty()) {
            PathLock pl = locks.remove(0);
            String plStr = pl.toStringPath();
            if (plStr.endsWith("]")) {
                List<PathLock> arrayExtendingLocks = new ArrayList<PathLock>();
                for (int i=0; i<locks.size(); i++) {
                    PathLock pl2 = locks.get(i);
                    String pl2Str = pl2.toStringPath();
                    if (pl2Str.startsWith(plStr)) {
                        arrayExtendingLocks.add(pl2);
                    }
                }
                locks.removeAll(arrayExtendingLocks);
                insertNullAndTypeChecks(arrayExtendingLocks, lockToFirstUnit, lockToLocal, lockToIdxUnit, lockToTypeCheck, code);
            }
            else {
                Local plLocal = lockToLocal.get(pl);
                Unit plFirstUnit = lockToFirstUnit.get(pl);
                if (plFirstUnit != null) {
                    // if pl is a non-static field lookup, need to skip the type check
                    IfStmt typeCheck = (IfStmt)lockToTypeCheck.get(pl);
                    if (typeCheck != null) {
                        plFirstUnit = code.getSuccOf(typeCheck);
                    }
                    // find next non-extending path
                    boolean found = false;
                    for (int i=0; i<locks.size(); i++) {
                        PathLock pl2 = locks.get(i);
                        String pl2Str = pl2.toStringPath();
                        if (!pl2Str.startsWith(plStr)) {
                            // pl2 is first lock after pl to not extend it, therefore
                            // if pl's path is null, should jump to pl2's locking code
                            Unit pl2FirstUnit = lockToFirstUnit.get(pl2);
                            if (pl2FirstUnit == null) {
                                Logger.println("pl: " + pl);
                                Logger.println("pl2: " + pl2);
                            }
//                            if (pl2FirstUnit != null) {
                                // if ($plLocal == null) goto pl2FirstUnit
        //                        System.out.println("pl2Str: " + pl2Str);
        //                        System.out.println("plStr: " + plStr);
                                
                                genNullCheck(pl, plFirstUnit, plLocal, pl2FirstUnit, code);
                                
                                if (typeCheck != null) {
                                    typeCheck.setTarget(pl2FirstUnit);
                                }
                                
                                found = true;
                                break;
                            }
//                        }
                    }
                    if (!found) {
                        // jump to end of instance locking code
                        // if pl is inside a loop (i.e. contains [*]), then have
                        // to jump to the idx stmt
                        Unit jumpTarget = lockToIdxUnit.get(pl);
    //                    System.out.println("pl: " + pl.toStringPath());
    //                    System.out.println("jumpTarget: " + jumpTarget);
                        genNullCheck(pl, plFirstUnit, plLocal, jumpTarget, code);
    
                        if (typeCheck != null) {
                            typeCheck.setTarget(jumpTarget);
                        }
                    }
                }
            }
            
            // process remaining locks
            insertNullAndTypeChecks(locks, lockToFirstUnit, lockToLocal, lockToIdxUnit, lockToTypeCheck, code);
        }
    }

    private void genNullCheck(PathLock lock, Unit lockFirstUnit, Local local, Unit jumpTarget, Chain<Unit> code) {
        EqExpr nullCond = jimpleFactory.newEqExpr(local, NullConstant.v());
        IfStmt ifNull = jimpleFactory.newIfStmt(nullCond, jumpTarget);
        PathLookup lookup = lock.getLookup();
        if (lock.getPrefix() == null && !(lookup instanceof StaticLookup)) {
            code.insertBefore(ifNull, lockFirstUnit);
        }
        else {
            if (lookup instanceof FieldLookup && !((FieldLookup)lookup).getField().isStatic()) {
                // skip cast and lookup assignment
                code.insertAfter(ifNull, code.getSuccOf(code.getSuccOf(lockFirstUnit)));
            }
            else {
                code.insertAfter(ifNull, lockFirstUnit);
            }
        }
    }

    // pre: pathLocks is sorted in extending order (e.g. { x, x.f, x.f.g, x.h, x.h.i, x.m })
    //      whereby extending paths consecutively follow each other.
//    private Chain<Unit> instanceLockingCode(Set<Lock> pathLocks, Unit firstUnitAfterInstanceLockingCode, Unit firstLockingUnit) {
//        
//        Map<PathLookup,List<PathLock>> baseToPaths = new HashMap<PathLookup, List<List<PathLock>>>();
//        for (Lock l : pathLocks) {
//            PathLock pl = (PathLock)l;
//            PathLookup base = null;
//            // find base
//            PathLock pl2 = pl;
//            while (pl2.getPrefix() != null) {
//                pl2 = pl2.getPrefix();
//            }
//            base = pl2.getLookup();
//            
//            // add pl to base's list of extending path locks
//            List<List<PathLock>> extendingPathLocksChain = baseToPaths.get(base);
//            if (extendingPathLocksChain == null) {
//                extendingPathLocksChain = new ArrayList<List<PathLock>>();
//                baseToPaths.put(base, extendingPathLocksChain);
//            }
//            
//            extendingPathLocks.add(pl);
//        }
//        
//        Chain<Unit> instChain = new PatchingChain<Unit>(new HashChain<Unit>());
//        
//        Unit nextLock = firstUnitAfterInstanceLockingCode;
//        
//        for (List<PathLock> locksWithSameBase : baseToPaths.values()) {
//            
////            Iterator<PathLock> locksIt = locksWithSameBase.iterator();
//            
//            // To preserve jumps to the next lock, insert nop before each per-base
//            // locking code block (code generated by instanceLockingCodeHelper will contain jumps
//            // to nextLock. Consequently, these jumps are lost by PatchingChain.insertBefore because 
//            // of the redirecting)
//            Unit nop = jimpleFactory.newNopStmt();
//            if (nextLock == firstUnitAfterInstanceLockingCode) {
//                instChain.add(nop);
//            }
//            else {
//                instChain.insertBefore(nop, nextLock);
//            }
//            
//            Chain<Unit> baseChain = instanceLockingCodeHelper(nextLock, firstLockingUnit, locksWithSameBase, null, new HashMap<String,Local>());
//            instChain.insertBefore(baseChain, nop);
//            nextLock = baseChain.getFirst();
//        }
//        
//        return instChain;
//    }
    
    // assumes locks in locksIt are all extensions of each other
    private Chain<Unit> instanceLockingCodeHelper(Unit firstUnitAfterLock, Unit firstLockingUnit, List<PathLock> locks, Map<PathLock,Unit> lockToFirstUnit, Map<PathLock,Local> lockToLocal, Map<PathLock,Unit> lockToFirstUnitAfterLock, Local prefixLocal, Map<String,Local> localsCache, Map<PathLock,Unit> lockToIfTypeCheck) {

        Chain<Unit> code = new PatchingChain<Unit>(new HashChain<Unit>());
        
        if (!locks.isEmpty()) {

            counter++;
            
            PathLock pl = locks.remove(0);
            PathLock prefix = pl.getPrefix();
            PathLookup lookup = pl.getLookup();
            
            lockToFirstUnitAfterLock.put(pl, firstUnitAfterLock);

            if (prefix == null) {
                if (lookup instanceof LocalLookup) {
                    LocalLookup llookup = (LocalLookup)lookup;
                    prefixLocal = llookup.getLocal();
                }
                else if (lookup instanceof ParamLookup) {
                    ParamLookup plookup = (ParamLookup)lookup;
                    ParameterVariable pvar = plookup.getParamVar();
                    if (pvar instanceof ThisVariable) {
                        prefixLocal = atomic.getBody().getThisLocal();
                    }
                    else {
                        prefixLocal = atomic.getBody().getParameterLocal(pvar.getNum());
                    }
                }
                else if (lookup instanceof StaticLookup) {
                    StaticLookup slookup = (StaticLookup)lookup;
                    SootClass c = slookup.getClazz();
                    prefixLocal = jimpleFactory.newLocal("$p" + counter, RefType.v("java.lang.Class"));
                    atomic.getBody().getLocals().add(prefixLocal);
                    AssignStmt clazzAssign = jimpleFactory.newAssignStmt(prefixLocal, ClassConstant.v(c.getName().replace('.', '/')));
                    code.add(clazzAssign);
                }
                else {
                    throw new UnsupportedOperationException("unknown lookup: " + lookup);
                }
            }
            else {
                Local lookupLocal = null;
//                System.out.println("prefix: " + prefix);
                prefixLocal = localsCache.get(prefix.toStringPath());
                
//                System.out.println("pl: " + pl);
                
                if (prefixLocal == null) {
                    throw new RuntimeException("local: " + prefixLocal + " not in cache (lock: " + pl + ")");
                }
                
                if (lookup instanceof FieldLookup) {
                    FieldLookup fl = (FieldLookup)lookup;
                    SootField f = fl.getField();
                    SootFieldRef fRef = f.makeRef();
                    FieldRef ref;
                    Type fieldDeclaringClassType = f.getDeclaringClass().getType();
                    
                    // cast prefixLocal to the type of the class containing the field
                    if (!f.isStatic()) {
                        // debugging output of types for lhs and rhs of cast:
                        // $class = rhs.getClass();
//                        Local classLocal = jimpleFactory.newLocal("$class", RefType.v("java.lang.Class"));
//                        SootMethod getClassMethod = Scene.v().getSootClass("java.lang.Object").getMethod("java.lang.Class getClass()");
//                        InstanceInvokeExpr getClassInvokeExpr = jimpleFactory.newVirtualInvokeExpr(prefixLocal, getClassMethod.makeRef());
//                        AssignStmt classAssign = jimpleFactory.newAssignStmt(classLocal, getClassInvokeExpr);
//                        
//                        atomic.getBody().getLocals().add(classLocal);
//                        code.add(classAssign);              
                        
//                        RefType printStreamType = RefType.v("java.io.PrintStream");
//                        RefType systemType = RefType.v("java.lang.System");
//                        SootClass systemClass = systemType.getSootClass();
//                        SootField outField = systemClass.getFieldByName("out");
//                        SootFieldRef outFieldRef = outField.makeRef();
//                        StaticFieldRef outStaticFieldRef = jimpleFactory.newStaticFieldRef(outFieldRef);
//                        Local outLocal = jimpleFactory.newLocal("$out", printStreamType);
//                        AssignStmt outAssign = jimpleFactory.newAssignStmt(outLocal, outStaticFieldRef);
//                        
//                        SootClass printStreamClass = printStreamType.getSootClass();
//                        SootMethod println = printStreamClass.getMethod("void println(java.lang.Object)");
//                        List args = new ArrayList<IntConstant>();
//                        args.add(classLocal);
//                        InstanceInvokeExpr printlnInvokeExpr = jimpleFactory.newVirtualInvokeExpr(outLocal, println.makeRef(), args);
//                        InvokeStmt printlnInvokeStmt = jimpleFactory.newInvokeStmt(printlnInvokeExpr);
//                        
//                        atomic.getBody().getLocals().add(outLocal);
//                        code.add(outAssign);
//                        code.add(printlnInvokeStmt);                        
                        
                        // Add run-time type check followed by cast
                        // if ($p1 instanceof T) {
                        //     $c2 = (T)$p1
                        //     $p2 = $c2.f;
                        //     ...
                        // }
                        
                        // $typeOk = $p instanceof T
                        Local typeCheckLocal = jimpleFactory.newLocal("$typeOk" + counter, BooleanType.v());
                        atomic.getBody().getLocals().add(typeCheckLocal);
                        InstanceOfExpr instanceOfExpr = jimpleFactory.newInstanceOfExpr(prefixLocal, fieldDeclaringClassType);
                        AssignStmt typeCheckAssign = jimpleFactory.newAssignStmt(typeCheckLocal, instanceOfExpr);
                        code.add(typeCheckAssign);
                        
                        // if $typeOk == 0 goto nop (nop is a placeholder that will be replaced later on with an actual target)
                        NopStmt nop = jimpleFactory.newNopStmt();
                        EqExpr notTypeOkExpr = jimpleFactory.newEqExpr(typeCheckLocal, IntConstant.v(0));
                        IfStmt ifNotTypeOk = jimpleFactory.newIfStmt(notTypeOkExpr, nop);
                        code.add(ifNotTypeOk);
                        code.add(nop);
                        lockToIfTypeCheck.put(pl, ifNotTypeOk);
                        
                        // $c = (T)$p
                        Local castLocal = jimpleFactory.newLocal("$c" + counter, f.getDeclaringClass().getType());
                        atomic.getBody().getLocals().add(castLocal);
                        CastExpr castExpr = jimpleFactory.newCastExpr(prefixLocal, fieldDeclaringClassType);
                        AssignStmt castAssign = jimpleFactory.newAssignStmt(castLocal, castExpr);
                        code.add(castAssign);
    
                        // code below assumes that prefixLocal points to the local
                        // of the prefix, but in this case that is castLocal.
                        prefixLocal = castLocal;
                    }
                    
                    if (f.isStatic()) {
                        ref = jimpleFactory.newStaticFieldRef(fRef);
                    }
                    else {
                        ref = jimpleFactory.newInstanceFieldRef(prefixLocal, fRef);
                    }
                    
                    lookupLocal = jimpleFactory.newLocal("$p" + counter, ref.getType());
                    atomic.getBody().getLocals().add(lookupLocal);
                    AssignStmt assign = jimpleFactory.newAssignStmt(lookupLocal, ref);
                    code.add(assign);
                }
                else if (lookup instanceof ArrayLookup) {

                    // recurse, but only pass in locks that extend current array lookup [*]
                    // as it is only these locks that need to be taken in the loop.
                    List<PathLock> arrayExtendingLocks = new ArrayList<PathLock>();
                    String plStr = pl.toStringPath();
                    for (PathLock pl2 : locks) {
                        if (pl2.toStringPath().startsWith(plStr)) {
                            // pl is a prefix of pl2
                            arrayExtendingLocks.add(pl2);
                        }
                    }
                    // locking code for locks in 'arrayExtendingLocks' will be
                    // generated by the recursive call and so they should be 
                    // removed from the 'locks' list
                    locks.removeAll(arrayExtendingLocks);
                    
                    // recurse (so we know where to jump to when exiting the loop)
                    Chain<Unit> restCode = instanceLockingCodeHelper(firstUnitAfterLock, firstLockingUnit, locks, lockToFirstUnit, lockToLocal, lockToFirstUnitAfterLock, prefixLocal, localsCache, lockToIfTypeCheck);
                    NopStmt nop = jimpleFactory.newNopStmt();
                    restCode.addFirst(nop);
                    firstUnitAfterLock = nop;
                    
                    counter++;
                    
                    // generate for loop:

                    // $idx0 = 0; 
                    Local idxLocal = jimpleFactory.newLocal("$idx" + counter, IntType.v());
                    atomic.getBody().getLocals().add(idxLocal);
                    AssignStmt idxInit = jimpleFactory.newAssignStmt(idxLocal, IntConstant.v(0));

                    // $len0 = lengthof local  (*)
                    // if ($idx0 >= $len0) goto firstUnitAfterLock 
                    Local lenLocal = jimpleFactory.newLocal("$len" + counter, IntType.v());
                    atomic.getBody().getLocals().add(lenLocal);
                    LengthExpr lenExpr = jimpleFactory.newLengthExpr(prefixLocal);
                    AssignStmt len = jimpleFactory.newAssignStmt(lenLocal, lenExpr);
                    GeExpr cond = jimpleFactory.newGeExpr(idxLocal, lenLocal);
                    IfStmt ifTest = jimpleFactory.newIfStmt(cond, firstUnitAfterLock);
                                        
                    // $idx0 = $idx0 + 1
                    AddExpr add1 = jimpleFactory.newAddExpr(idxLocal, IntConstant.v(1));
                    AssignStmt idxInc = jimpleFactory.newAssignStmt(idxLocal, add1);
                    
                    // goto (*) above
                    GotoStmt iterate = jimpleFactory.newGotoStmt(len);
                    
                    code.add(idxInit);
                    code.add(len);
                    code.add(ifTest);
                    
                    // $elem0 = local[$idx0]
                    ArrayType localType = (ArrayType)prefixLocal.getType();
                    Local elemLocal = jimpleFactory.newLocal("$elem" + counter, localType.getArrayElementType());
                    atomic.getBody().getLocals().add(elemLocal);
                    AssignStmt elemInit = jimpleFactory.newAssignStmt(elemLocal, jimpleFactory.newArrayRef(prefixLocal, idxLocal));
                    
                    code.add(elemInit);
                    
                    // generate lock code for $elem0
                    lockAcquisitionCode(idxInc, firstLockingUnit, elemLocal, code, pl, true);
                    
//                    System.out.println("adding " + pl.toStringPath() + "->" + elemLocal + " to cache");
                    localsCache.put(pl.toStringPath(), elemLocal);
                    
                    Chain<Unit> innerLoopCode = instanceLockingCodeHelper(idxInc, firstLockingUnit, arrayExtendingLocks, lockToFirstUnit, lockToLocal, lockToFirstUnitAfterLock, elemLocal, localsCache, lockToIfTypeCheck);
                    code.insertAfter(innerLoopCode, code.getLast());
                    
                    code.add(idxInc);
                    code.add(iterate);
                    
                    code.insertAfter(restCode, iterate);
                    return code;
                }

                if (!(lookup instanceof ArrayLookup)) {
                    prefixLocal = lookupLocal;
                }
            }
            
            if (!(lookup instanceof ArrayLookup)) {
                localsCache.put(pl.toStringPath(), prefixLocal);
            
                boolean nullCheck = false; //!(prefix == null && lookup instanceof StaticLookup); 
                lockAcquisitionCode(firstUnitAfterLock, firstLockingUnit, prefixLocal, code, pl, nullCheck);
            }
            
//            if (kill == null || !kill.contains(pl)) {
            if (code.isEmpty()) {
//                Logger.println("code is empty - pl: " + pl);
                code.add(jimpleFactory.newNopStmt());
            }
            lockToFirstUnit.put(pl, code.getFirst());
//            }
            lockToLocal.put(pl, prefixLocal);
         
            // recurse
            Chain<Unit> restCode = instanceLockingCodeHelper(firstUnitAfterLock, firstLockingUnit, locks, lockToFirstUnit, lockToLocal, lockToFirstUnitAfterLock, prefixLocal, localsCache, lockToIfTypeCheck);
            if (code.isEmpty()) {
//                Logger.println("code is empty");
                code.add(jimpleFactory.newNopStmt());
            }
            code.insertAfter(restCode, code.getLast());
        }
        
        return code;
    }

    long printCounter = 0;
    
    private void lockAcquisitionCode(Unit nextLock, Unit firstLockingUnit, Local local, Chain<Unit> code, PathLock pl, boolean nullCheck) {

        if (nullCheck) {
            // if ($p == null) goto firstUnitAfterLock
            EqExpr nullCond = jimpleFactory.newEqExpr(local, NullConstant.v());
            IfStmt ifNull = jimpleFactory.newIfStmt(nullCond, nextLock);
            code.add(ifNull);
        }
        
        if (pl.willBeAcquired()) {        
        
            if (AtomicTransformer.INSTRUMENT_DEBUG) {
                // add print statement for debugging, so know which lock is being acquired
                RefType printStreamType = RefType.v("java.io.PrintStream");
                RefType systemType = RefType.v("java.lang.System");
                SootClass systemClass = systemType.getSootClass();
                SootField outField = systemClass.getFieldByName("out");
                SootFieldRef outFieldRef = outField.makeRef();
                StaticFieldRef outStaticFieldRef = jimpleFactory.newStaticFieldRef(outFieldRef);
                Local outLocal = jimpleFactory.newLocal("$out", printStreamType);
                AssignStmt outAssign = jimpleFactory.newAssignStmt(outLocal, outStaticFieldRef);
                
                SootClass printStreamClass = printStreamType.getSootClass();
        //        SootMethod println = printStreamClass.getMethod("void println(long)");
                SootMethod println = printStreamClass.getMethod("void println(java.lang.String)");
                List args = new ArrayList<IntConstant>();
        //        args.add(LongConstant.v(printCounter));
                args.add(StringConstant.v(pl.toString()));
                InstanceInvokeExpr printlnInvokeExpr = jimpleFactory.newVirtualInvokeExpr(outLocal, println.makeRef(), args);
                InvokeStmt printlnInvokeStmt = jimpleFactory.newInvokeStmt(printlnInvokeExpr);
                
                atomic.getBody().getLocals().add(outLocal);
                code.add(outAssign);
                code.add(printlnInvokeStmt);
            }
            
            // code to take the lock
            SootMethod lock = pl.isWrite() ? synchroniser.getMethodByName("lockInstanceWrite") : synchroniser.getMethodByName("lockInstanceRead");
            IntConstant multi = IntConstant.v(pl.doMultiLocking() ? 1 : 0);
            StaticInvokeExpr lockExpr = jimpleFactory.newStaticInvokeExpr(lock.makeRef(), local, multi);
            Local lockedLocal = jimpleFactory.newLocal("$locked" + counter, BooleanType.v());
            atomic.getBody().getLocals().add(lockedLocal);
            AssignStmt lockedAssign = jimpleFactory.newAssignStmt(lockedLocal, lockExpr);
    
            EqExpr ifCond = jimpleFactory.newEqExpr(lockedLocal, IntConstant.v(0));
            IfStmt ifLocked = jimpleFactory.newIfStmt(ifCond, firstLockingUnit);
            code.add(lockedAssign);
            code.add(ifLocked);
        }
//        else if (pl.isReadOnly()) {
//            Logger.println("not instrumenting read only lock " + pl);
//        }
        
        printCounter++;
        
    }
    
}
