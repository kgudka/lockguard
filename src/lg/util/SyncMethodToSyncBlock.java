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

import java.lang.reflect.Modifier;
import java.util.*;

import org.jikesrvm.compilers.opt.ir.operand.ClassConstantOperand;

import lg.cfg.CFGCache;

import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.Chain;

public class SyncMethodToSyncBlock {

    public static void convertSyncMethodToSyncBlock(SootMethod m, ExceptionalUnitGraph cfg) {
        m.setModifiers(m.getModifiers() & ~Modifier.SYNCHRONIZED);
        
        // surround method with try/catch
        PatchingChain<Unit> units = cfg.getBody().getUnits();
        Jimple jimpleFactory = Jimple.v();
        
        /* Insert try/finally
         * 
         * synchronized void m() {
         *     i=0;
         *     j=0;
         * }
         * 
         * becomes:
         * 
         * void m() {
         *     entermonitor;
         *     i=0;
         *     j=0;
         *     exitmonitor;
         *     return;
         *     
         *     $p = @caughtexception;
         *     exitmonitor;
         *     throw $p;     
         */
        
        // if m is a static method that takes no parameters, insert a nop so
        // there is only one head. This simplifies the AtomicsFinder algorithm
//        if (m.isStatic() && m.getParameterCount() == 0) {
//            Logger.println(m.toString() + " is static with no params");
//            units.insertBeforeNoRedirect(jimpleFactory.newNopStmt(), units.getFirst());
//        }

        
        Unit firstNonIdentityUnit = null;
        Unit lastIdentityUnit = null;
        for (Iterator<Unit> unitsIt=units.iterator(); unitsIt.hasNext();) {
            Unit u = unitsIt.next();
            if (u instanceof IdentityStmt) {
                lastIdentityUnit = u;
                continue;
            }
            else {
                firstNonIdentityUnit = u;
                break;
            }
        }
        
        // entermonitor
        
        // if m is a static method that takes no parameters, insert a nop so
        // there is only one head. This simplifies the AtomicsFinder algorithm
        Local classLocal = null;
        Local thisLocal = null;
        if (m.isStatic()) {
            Constant classConstant = ClassConstant.v(m.getDeclaringClass().getName().replace('.', '/'));
            classLocal = jimpleFactory.newLocal("$c0", RefType.v("java.lang.Class"));
            cfg.getBody().getLocals().add(classLocal);
            AssignStmt assignSt = jimpleFactory.newAssignStmt(classLocal, classConstant);
            MonitorStmt enter = jimpleFactory.newEnterMonitorStmt(classLocal);
            if (m.getParameterCount() == 0) {
                units.addFirst(enter);
                units.addFirst(assignSt);                
            }
            else {
                units.insertAfter(enter, lastIdentityUnit);
                units.insertAfter(assignSt, lastIdentityUnit);
            }
        }
        else {
            thisLocal = cfg.getBody().getThisLocal();
            MonitorStmt enter = jimpleFactory.newEnterMonitorStmt(thisLocal);            
            units.insertAfter(enter, lastIdentityUnit);
        }
        
        // exitmonitor before each non-throw tail
        for (Unit t : cfg.getTails()) {
            if (!(t instanceof ThrowStmt)) {
                units.insertBefore(jimpleFactory.newExitMonitorStmt(m.isStatic() ? classLocal : thisLocal), t);
            }
        }
        
        // hander code
        Local eLocal = jimpleFactory.newLocal("$e", RefType.v("java.lang.Throwable"));
        cfg.getBody().getLocals().add(eLocal);
        IdentityStmt catchAssign = jimpleFactory.newIdentityStmt(eLocal, jimpleFactory.newCaughtExceptionRef());
        ExitMonitorStmt exitMonitor = jimpleFactory.newExitMonitorStmt(m.isStatic() ? classLocal : thisLocal);
        ThrowStmt throwStmt = jimpleFactory.newThrowStmt(eLocal);
        
        units.add(catchAssign);
        units.add(exitMonitor);
        units.add(throwStmt);

        // rebuild cfg
        CFGCache.invalidateCFG(m);
        cfg = CFGCache.getCFG(m);

        // traps
        SootClass throwable = Scene.v().getSootClass("java.lang.Throwable");
        Unit beginStmt = null;
        for (Unit u : units) {
            if (u instanceof IdentityStmt || u instanceof EnterMonitorStmt) {
                continue;
            }
            else if (beginStmt == null) {
//                Logger.println("Setting beginStmt = " + u);
                beginStmt = u;
            }
            /* FIX: don't filter out throw tail statements because now we cover 
             * both cases of when an exception is thrown in the body of the
             * atomic and also by a throw tail statement. In both cases, we 
             * catch the exception, perform unlocking and then propagate the 
             * exception. 
             */
            else if (cfg.getTails().contains(u)) { 
//                if (!(u instanceof ThrowStmt)) {  
                    cfg.getBody().getTraps().add(jimpleFactory.newTrap(throwable, beginStmt, u, catchAssign));
                    beginStmt = null;
//                }
            }
        }
    }
    
}
