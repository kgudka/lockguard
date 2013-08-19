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

package lg.analysis.singlethread;

import java.util.Map;

import soot.*;
import soot.jimple.toolkits.thread.mhp.SynchObliviousMhpAnalysis;

// analysis that checks whether a given method is only ever executed by a single
// thread, so that proving that all accesses made while executing it do not 
// require concurrency control
public class SingleThreadedExecution extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map options) {
        
        // run MHP
        SynchObliviousMhpAnalysis mhp = new SynchObliviousMhpAnalysis();

        // print out mhp info
//        mhp.printMhpSummary();
        
        SootClass createDBclass = Scene.v().getSootClass("test.singlethread.SimpleNegative1");
        SootMethod createDBmethod1 = createDBclass.getMethodByName("m");
        SootMethod createDBmethod2 = createDBclass.getMethodByName("n");
        
//        for (SootClass c : Scene.v().getClasses()) {
//            for (SootMethod m : c.getMethods()) {
////                System.out.println("Comparing " + createDBmethod + " and " + m);
//                if (mhp.mayHappenInParallel(createDBmethod, m)) {
//                    System.out.println("createDB runs in parallel with " + m);
//                    return;
//                }
//            }
//        }
//        System.out.println("createDB is only executed by one thread!");
        
        if (mhp.mayHappenInParallel(createDBmethod1, createDBmethod1)) {
            System.out.println(createDBmethod1 + "||" + createDBmethod1);
        }

        if (mhp.mayHappenInParallel(createDBmethod1, createDBmethod2)) {
            System.out.println(createDBmethod1 + "||" + createDBmethod2);
        }
        
    }
    
}
