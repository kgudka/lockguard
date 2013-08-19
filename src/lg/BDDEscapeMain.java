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

package lg;

import lg.analysis.local.BDDEscapeAnalysisTransformer;
import soot.*;

public class BDDEscapeMain {

    /**
     * @param args
     */
    public static void main(String[] args) {
        
        Pack wjtp = PackManager.v().getPack("wjtp");
        Transform t = new Transform("wjtp.bddescape", new BDDEscapeAnalysisTransformer());
        t.setDeclaredOptions("enabled");
        t.setDefaultOptions("enabled:true");
        wjtp.add(t);
               
        Scene.v().addBasicClass("java.io.FileSystem",SootClass.HIERARCHY);
        
        String[] args2 = "-trim-cfgs -w -p cg enabled:true,implicit-entry:true,verbose:false -p cg.paddle enabled:true,context:kobjsens,k:1,context-heap:false,bdd:true --app RunnableBug FixPointBug".split(" ");
        
        soot.Main.main(args2);
        
    }

}
