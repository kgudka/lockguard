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

import soot.*;

public class TypeLock extends Lock {

    Type type;
    final int hashCode;
    
    public TypeLock(Type t, boolean w, boolean threadLocal, boolean instanceLocal, boolean dominated, boolean readOnly) {
        super(w, threadLocal, instanceLocal, dominated, false, false, readOnly, false);
        type = t;
        hashCode = hash();
    }
    
    private int hash() {
        return type.hashCode();
    }
    
    @Override
    public String toString() {
        return (isWrite() ? "W" : "R") + "(" + type.toString() + ")";
    }
    
    @Override
    public int hashCode() {
        return hashCode;
    }
    
    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        else if (o == null) {
            return false;
        }
        else if (o instanceof TypeLock) {
            TypeLock t = (TypeLock)o;
            boolean baseSame = super.equals(t);
            return baseSame && type.equals(t.type);
        }
        else {
            return false;
        }
    }

    @Override
    public boolean subsumes(Lock l) {
        if (isWrite()) {
            if (l instanceof TypeLock) {
                TypeLock tl = (TypeLock)l;
                return type.equals(tl.type) && !tl.isWrite();
            }
        }
        return false;
    }
    
    public Type getType() {
        return type;
    }
    
}
