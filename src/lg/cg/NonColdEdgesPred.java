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

package lg.cg;

import lg.analysis.VMMethodMarker;
import lg.util.*;
import soot.SootMethod;
import soot.jimple.toolkits.callgraph.*;
import soot.tagkit.*;

public class NonColdEdgesPred extends ExplicitEdgesPred {

    @Override
    public boolean want(Edge e) {
//        if (super.want(e)) {
//            // check if target is @Cold
//            SootMethod tgt = e.tgt();
////            String tgtStr = tgt.toString();
////            if (tgtStr.equals("<java.util.AbstractMap: int hashCode(java.lang.Object)>")) {
////                return false;
////            }
////            if (tgtStr.equals("<java.security.CodeSource: int hashCode()>")) {
////                return false;
////            }
////            if (tgtStr.equals("<java.util.AbstractCollection: int hashCode(java.lang.Object)>")) {
////                return false;
////            }
////            if (tgtStr.equals("<java.util.AbstractSet: int hashCode()>")) {
////                return false;
////            }
//            if (AtomicTransformer.COLD) {
        SootMethod src = e.src();
        SootMethod tgt = e.tgt();

//        for (Tag t : tgt.getTags()) {
//            if (t instanceof VisibilityAnnotationTag) {
//                VisibilityAnnotationTag v = (VisibilityAnnotationTag)t;
//                for (AnnotationTag a : v.getAnnotations()) {
//                    if (a.getType().equals("Llg/util/Cold;")) {
//                        Logger.println(tgt.toString() + " is cold");
//                        ProfilerSupport.waitForKeyPress();
//                        return false;
//                    }
//                }
//            }
//        }
//            }
//            return true;
//        }
//        else {
//            return false;
//        }
//        if (!e.tgt().isConcrete() && super.want(e)) {
//            throw new RuntimeException(e.tgt() + " is not concrete");
//        }
        String[] exclude = new String[] { "org.jikesrvm", 
                                          "org.vmmagic", 
                                          "org.mmtk", 
                                          "org.vmutil",
                                          "GraphImage" };
        for (int i=0; i<exclude.length; i++) {
            String pkg = exclude[i];
            if (src.getDeclaringClass().toString().contains(pkg) || tgt.getDeclaringClass().toString().contains(pkg)) {
                return false;
            }
        }
        
        return tgt.isConcrete() && super.want(e) && !VMMethodMarker.isMarked(tgt);
    }
    
}
