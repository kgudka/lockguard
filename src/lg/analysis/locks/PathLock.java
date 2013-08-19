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

import soot.PointsToSet;
import soot.jimple.paddle.*;


public class PathLock extends Lock {

    PathLock prefix;
    PathLookup lookup;
    boolean multi;
    PointsToSet pts;
    
    public PathLock(PathLock p, PathLookup l, boolean w, boolean threadLocal, boolean instanceLocal, PointsToSet pt, boolean dominated, boolean duplicate, boolean classLocal, boolean readOnly, boolean m, boolean mLocal) {
        super(w, threadLocal, instanceLocal, dominated, duplicate, classLocal, readOnly, mLocal);
        prefix = p;
        lookup = l;
        multi = m;
        pts = pt;
    }
    
    public PathLock getPrefix() {
        return prefix;
    }
    
    public PathLookup getLookup() {
        return lookup;
    }
    
    @Override
    public String toString() {
        return (isWrite() ? "W" : "R") + "(" + ((prefix == null) ? "" : prefix.toStringPath()) + lookup.toString() + ")";
    }
    
    public String toStringPath() {
        return ((prefix == null) ? "" : prefix.toStringPath()) + lookup.toString();
    }

    @Override
    public int hashCode() {
        return (prefix == null ? 1 : prefix.hashCode()) ^ lookup.hashCode();
    }
    
    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        else if (o == null) {
            return false;
        }
        else if (o instanceof PathLock) {
            PathLock p = (PathLock)o;
            boolean baseSame = super.equals(p);
            boolean prefixSame = prefix == null ? prefix == p.prefix : prefix.equals(p.prefix);
            return baseSame && prefixSame && lookup.equals(p.lookup);// && pointsToSetEquals(pts, p.pts);
        }
        else {
            return false;
        }
    }
    
    @Override
    public boolean subsumes(Lock l) {
        if (isWrite()) {
            if (l instanceof PathLock) {
                PathLock pl = (PathLock)l;
                boolean prefixSame = prefix == null ? prefix == pl.prefix : prefix.equals(pl.prefix);
                return prefixSame && lookup.equals(pl.lookup) && !pl.isWrite() && isDominated() == pl.isDominated() && isDuplicate() == pl.isDuplicate() && isClassLocal() == pl.isClassLocal() && isMethodLocal() == pl.isMethodLocal();// && pointsToSetEquals(pts, pl.pts);
            }
        }
        return false;
    }
    
    public int length() {
        if (prefix == null) {
            return 1;
        }
        else {
            return 1 + prefix.length();
        }
    }

    public void setDoMultiLocking(boolean b) {
        multi = b;
    }

    public boolean doMultiLocking() {
        return multi;
    }
    
    public PointsToSet getPointsToSet() {
        return pts;
    }
    
    public boolean isStatic() {
        return lookup instanceof StaticLookup;
    }

//    private boolean pointsToSetEquals(PointsToSet pts1, PointsToSet pts2) {
//        BDDPointsToSet bpts1 = (BDDPointsToSet)pts1;
//        BDDPointsToSet bpts2 = (BDDPointsToSet)pts2;
//        return superSetOf(bpts1, bpts2) && superSetOf(bpts2, bpts1);
//    }
//    
//    private boolean superSetOf(final BDDPointsToSet pts1, BDDPointsToSet pts2) {
//        return pts2.forall(new P2SetVisitor() {
//            boolean returnValue2 = true;
//            @Override
//            public void visit(ContextAllocNode n) {
//                returnValue2 &= pts1.contains(n); 
//            }
//            @Override
//            public boolean getReturnValue() {
//                return returnValue2;
//            }
//        });
//    }
    
}
