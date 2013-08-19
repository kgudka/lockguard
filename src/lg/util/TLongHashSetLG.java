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

import gnu.trove.set.hash.TLongHashSet;

public class TLongHashSetLG extends TLongHashSet {

    public TLongHashSetLG() {
    }

    public TLongHashSetLG(int initialCapacity) {
        super(initialCapacity);
    }

    public TLongHashSetLG(long[] array) {
        super(array);
    }

    public TLongHashSetLG(TLongHashingStrategy strategy) {
        super(strategy);
    }

    public TLongHashSetLG(int initialCapacity, float loadFactor) {
        super(initialCapacity, loadFactor);
    }

    public TLongHashSetLG(int initialCapacity, TLongHashingStrategy strategy) {
        super(initialCapacity, strategy);
    }

    public TLongHashSetLG(long[] array, TLongHashingStrategy strategy) {
        super(array, strategy);
    }

    public TLongHashSetLG(int initialCapacity, float loadFactor,
            TLongHashingStrategy strategy) {
        super(initialCapacity, loadFactor, strategy);
    }
    
    public int capacity() {
        return super.capacity();
    }
    
    @Override
    public void compact() {
        // we don't find the next prime but instead just make it large enough
//        int oldCapacity = capacity();
//        int newCapacity = fastCeil((float)size() / _loadFactor) + 1;
//        System.out.println("size: " + size() + ", old capacity: " + oldCapacity + ", new capacity: " + newCapacity);
//        rehash(newCapacity);
//        computeMaxSize(capacity());
//        if(_autoCompactionFactor != 0.0F)
//            computeNextAutoCompactionAmount(size());
        super.compact();
    }
    
    private int fastCeil(float v) {
        int possible_result = (int)v;
        if(v - (float)possible_result > 0.0F)
            possible_result++;
        return possible_result;
    }
    
    private void computeMaxSize(int capacity) {
        _maxSize = Math.min(capacity - 1, (int)((float)capacity * _loadFactor));
        _free = capacity - _size;
    }
    
    private void computeNextAutoCompactionAmount(int size) {
        if(_autoCompactionFactor != 0.0F) {
            _autoCompactRemovesRemaining = (int)((float)size * _autoCompactionFactor + 0.5F);
        }
    }
    
}
