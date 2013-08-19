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

import soot.*;
import soot.jimple.paddle.*;

public class PaddleThreadLocalAnalysis extends ThreadLocalAnalysis{

    Set<AllocNode> shared;
    
    public PaddleThreadLocalAnalysis() {
        shared = new HashSet<AllocNode>();
    }
    
    public boolean isThreadShared(Local l) {
        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
        PointsToSetReadOnly pts = (PointsToSetReadOnly)pta.reachingObjects(l);
        
        try {
            pts.forall(new P2SetVisitor() {
                @Override
                public void visit(ContextAllocNode n) {
                    AllocNode obj = n.obj();
                    if (shared.contains(obj)) {
                        // no need to check further
                        throw new RuntimeException("shared");
                    }
                }
            });
        }
        catch (RuntimeException re) {
            if (re.getMessage().equals("shared")) {
                return true;
            }
            else {
                throw re;
            }
        }

        return false;
    }
    
    public void doAnalysis() {
        
        G.v().out.println("[wjtp.lg] tla: running bdd escape analysis");
        
        BDDEscapeAnalysis bddEscape = new BDDEscapeAnalysis();
        bddEscape.analyze();

        G.v().out.println("[wjtp.lg] tla: storing thread-shared objects");
        
        for (Iterator sharedIt=bddEscape.escapesThread(); sharedIt.hasNext(); ) {
            shared.add((AllocNode)sharedIt.next());
        }
        
    }
    
}
