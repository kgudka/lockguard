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

public abstract class Lock {

    boolean write;
    boolean threadLocal;
    boolean instanceLocal;
    boolean readOnly;
    boolean dominated;
    boolean duplicate;
    boolean classLocal;
    boolean methodLocal;
    
    public Lock(boolean w, boolean tl, boolean il, boolean d, boolean dup, boolean cl, boolean ro, boolean ml) {
        write = w;
        threadLocal = tl;
        instanceLocal = il;
        dominated = d;
        duplicate = dup;
        classLocal = cl;
        readOnly = ro;
        methodLocal = ml;
    }
    
    public boolean isWrite() {
        return write;
    }
    
    public boolean isThreadLocal() {
        return threadLocal;
    }
    
    public boolean isInstanceLocal() {
        return instanceLocal;
    }
    
    public boolean isDominated() {
        return dominated;
    }
    
    public boolean isDuplicate() {
        return duplicate;
    }
    
    public void setDuplicate(boolean dup) {
        duplicate = dup;
    }
    
    public void setDominated(boolean d) {
        dominated = d;
    }

    public boolean isClassLocal() {
        return classLocal;
    }
    
    public boolean isReadOnly() {
        return readOnly;
    }
    
    public boolean isMethodLocal() {
        return methodLocal;
    }
    
    public abstract boolean subsumes(Lock l);
    
    public boolean willBeAcquired() {
        return !isThreadLocal() && !isInstanceLocal() && !isClassLocal() && !isDominated() && !isDuplicate() && !isReadOnly() && !isMethodLocal();
    }
    
    @Override
    public boolean equals(Object o) {
        // assume that subclasses have performed instanceof checks already
        Lock l = (Lock)o;
        return isWrite() == l.isWrite() && isThreadLocal() == l.isThreadLocal() && isInstanceLocal() == l.isInstanceLocal() && isDominated() == l.isDominated() && isDuplicate() == l.isDuplicate() && isClassLocal() == l.isClassLocal() && isReadOnly() == l.isReadOnly() && isMethodLocal() == l.isMethodLocal();
    }
    
}
