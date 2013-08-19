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

package lg.util;

import gnu.trove.procedure.TLongProcedure;
import gnu.trove.set.hash.TLongHashSet;

import java.util.Collection;

public class TwoLevelSet extends TLongHashSet {

    TLongHashSet parent;
    TLongHashSet child;
    
    public TwoLevelSet(TLongHashSet p, TLongHashSet c) {
        super(0);
        parent = p;
        child = c;
    }

    public boolean add(long l) {
        throw new UnsupportedOperationException();
    }
    
    @Override
    public boolean addAll(long[] array) {
        throw new UnsupportedOperationException();
    }

    public void clear() {
        throw new UnsupportedOperationException();
    }

    public boolean contains(long l) {
        return child.contains(l) || parent.contains(l); // search child first as it should be smaller
    }

    public boolean isEmpty() {
        return parent.isEmpty() && child.isEmpty();
    }

    public boolean remove(Object o) {
        throw new UnsupportedOperationException();
    }

    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    public int size() {
        return parent.size() + child.size();
    }

    public long[] toArray() {
        throw new UnsupportedOperationException();
    }
    
    @Override
    public boolean forEach(TLongProcedure procedure) {
        boolean ret = parent.forEach(procedure);
        if (ret) {
            // only continue if parent returned true
            return child.forEach(procedure);
        }
        return ret;
    }
    
    @Override
    public Object clone() {
        return new TwoLevelSet(parent, new TLongHashSet(child));
    }
    
    @Override
    public void compact() { // parent should already be compacted
        child.compact(); 
    }
    
    public TLongHashSet getChild() {
        return child;
    }
    
}
