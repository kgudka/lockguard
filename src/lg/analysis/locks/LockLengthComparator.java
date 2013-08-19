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

import java.util.Comparator;

public class LockLengthComparator implements Comparator<Lock> {

    public int compare(Lock l1, Lock l2) {
        if (l1 instanceof TypeLock) {
            TypeLock tl1 = (TypeLock)l1;
            if (l2 instanceof TypeLock) {
                TypeLock tl2 = (TypeLock)l2;
                String tl1Type = tl1.getType().toString();
                String tl2Type = tl2.getType().toString();
                return tl1Type.compareTo(tl2Type);
            }
            else {
                return -1;
            }
        }
        else if (l1 instanceof PathLock) {
            PathLock pl1 = (PathLock)l1;
            if (l2 instanceof PathLock) {
                PathLock pl2 = (PathLock)l2;
                String pl1Path = pl1.toStringPath();
                String pl2Path = pl2.toStringPath();
                return pl1Path.compareTo(pl2Path);
            }
            else {
                return 1;
            }
        }
        else {
            throw new UnsupportedOperationException("unknown lock type: " + l1.getClass());
        }
    }

}
