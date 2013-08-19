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

package lg.tlo;

import java.util.*;

import soot.*;
import soot.jimple.FieldRef;
import soot.jimple.toolkits.thread.ThreadLocalObjectsAnalysis;
import soot.jimple.toolkits.thread.mhp.*;

public class ThreadLocalSceneTransformer extends SceneTransformer {

    private static Transformer instance = new ThreadLocalSceneTransformer();
    private ThreadLocalObjectsAnalysis tloa;

    public static Transformer v() {
        return instance;
    }
    
    private ThreadLocalObjectsAnalysis getTLOA() {
        MhpTester mhp = new SynchObliviousMhpAnalysis(); 
        ThreadLocalObjectsAnalysis tloa = new ThreadLocalObjectsAnalysis(mhp);
        return tloa;
    }

    @Override
    protected void internalTransform(String phaseName, Map options) {
        tloa = getTLOA();
        tloa.precompute();
        iterateAllMethods();
    }

    private void iterateAllMethods() {

        // Find methods
        Iterator<SootClass> getClassesIt = Scene.v().getApplicationClasses().iterator();
        while (getClassesIt.hasNext()) {
            SootClass appClass = getClassesIt.next();
            Iterator<SootMethod> getMethodsIt = appClass.getMethods().iterator();
            while (getMethodsIt.hasNext()) {
                SootMethod method = getMethodsIt.next();
                analyzeMethod(method);
            }
        }
    }

    private void analyzeMethod(SootMethod method) {
        if (!method.hasActiveBody()) {
            return;
        }
        Body activeBody = method.getActiveBody();

        List<ValueBox> useAndDefBoxes = activeBody.getUseAndDefBoxes();
        for (ValueBox valueBox : useAndDefBoxes) {
            Value value = valueBox.getValue();
            if (value instanceof FieldRef) {
                analyzeField(method, value);
            }
            else if (value instanceof Local) {
                analyzeLocal(method, value);
            }
        }
    }

    private void analyzeLocal(SootMethod method, Value value) {
        Local l = (Local)value;
        boolean objIsThreadLocal = tloa.isObjectThreadLocal(l, method);
        if (objIsThreadLocal) {
            G.v().out.println("[lg.tlo] LOCAL " + l.toString() + " is thread-local in method " + method);
        }
        else {
            G.v().out.println("[lg.tlo] LOCAL " + l.toString() + " is thread-shared in method " + method);
        }
    }
    
    private void analyzeField(SootMethod method, Value value) {
        FieldRef fr = (FieldRef) value;
        boolean fieldIsThreadLocal = tloa.isObjectThreadLocal(fr, method);
        if (fieldIsThreadLocal) {
            G.v().out.println("[lg.tlo] FIELD " + fr.toString() + " is thread-local in method " + method);
        }
        else {
            G.v().out.println("[lg.tlo] FIELD " + fr.toString() + " is thread-shared in method " + method);
        }
    }
    
}
