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

package lg.analysis.locks.dominators;

import soot.jimple.spark.pag.*;
import soot.jimple.spark.sets.*;

public class PointsToSetContainer {

    private final PointsToSetInternal pts;
    private final int hashCode;
    private final boolean singleUniqueObject;
    private final AllocNode singleNode;
    
    public PointsToSetContainer(PointsToSetInternal pt, boolean single) {
        pts = pt;
        final int[] h = new int[1];
        h[0] = 0;
        pt.forall(new P2SetVisitor() {
            @Override
            public void visit(Node n) {
                h[0] ^= n.hashCode();
            }
        });
        hashCode = h[0];
        singleUniqueObject = single;

        // cache single alloc node if there is one
        if (singleUniqueObject) {
            final AllocNode[] a = new AllocNode[1];
            pts.forall(new P2SetVisitor() {
                @Override
                public void visit(Node n) {
                    a[0] = (AllocNode)n;
                }
            });
            singleNode = a[0];
        }
        else {
            singleNode = null;
        }
        
    }
    
    @Override
    public int hashCode() {
        return hashCode;
    }
    
    @Override
    public boolean equals(Object o) {
        // if points to sets refer to single object then compare the alloc nodes
        if (o instanceof PointsToSetContainer) {
            PointsToSetContainer p = (PointsToSetContainer)o;
            if (singleUniqueObject == p.singleUniqueObject) {
                if (singleUniqueObject) {
                    return singleNode == p.singleNode;
                }
                else {
                    return pts == p.pts;
                }
            }
        }
        return false;
    }
    
}
