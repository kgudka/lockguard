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

package lg.analysis;

import java.util.List;

import lg.util.*;
import soot.*;
import soot.util.Chain;

// marks methods that refer to VM-specific classes as being VM-methods
public class VMMethodMarker {

    static String[] vmRefs = new String[] { "org.jikesrvm", 
                                            "org.vmmagic", 
                                            "org.mmtk", 
                                            "org.vmutil",
                                            "JikesRVMSupport",
                                            "JikesRVMHelpers" };
    
    public static void markMethods() {
        // A VM-method is one that (a) is not in the VM library but (b) refers
        // to classes in the VM:
        //   a) Field access
        //   b) Type reference (lhs or rhs)
        //   c) VM method call
        // we achieve all this by simple string comparison
       
        Logger.println("*********************", ANSICode.FG_BLUE);
        Logger.println("VM Reference methods", ANSICode.FG_BLUE);
        Logger.println("*********************", ANSICode.FG_BLUE);
        Chain<SootClass> classes = Scene.v().getClasses();
        for (SootClass c : classes) {
//            System.out.println(c.toString());
            if (containsVMRef(c.toString())) {
                // skip vm classes
                continue;
            }
            List<SootMethod> cMethods = c.getMethods();
            // check each method in turn
            for (SootMethod m : cMethods) {
                boolean marked = false;
                if (containsVMRef(m.toString())) {
                    mark(m);
                    marked = true;
                }
                else {
                    if (m.isConcrete()) {
                        Chain<Unit> units = m.retrieveActiveBody().getUnits();
                        for (Unit u : units) {
                            if (containsVMRef(u.toString())) {
                                mark(m);
                                marked = true;
                                break;
                            }
                        }
                    }
                }
                if (marked) {
                    Logger.println("\t" + m.toString(), ANSICode.FG_MAGENTA);
                }
            }
        }
    }

    private static void mark(SootMethod m) {
        m.addTag(new VMRefMethodTag());
    }

    private static boolean containsVMRef(String s) {
        for (int r=0; r<vmRefs.length; r++) {
            if (s.contains(vmRefs[r])) {
                return true;
            }
        }
        return false;
    }
    
    public static boolean isMarked(SootMethod m) {
        return m.hasTag(VMRefMethodTag.NAME);
    }
    
}
