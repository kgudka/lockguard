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

import java.util.*;

import lg.analysis.paths.transformer.fast.TransformerEdge;


public class SortedHashedArraySet<T> implements Set<T> {
    
    private static final int DEFAULT_INITIAL_CAPACITY = 16;
    private static final float DEFAULT_LOAD_FACTOR = 0.75f;
    
    Set<T>[] buckets;
    int size;    
    int threshold;
    float loadFactor;
    int hashCode;
    
    public SortedHashedArraySet() {
        buckets = (SortedArraySet<T>[])new SortedArraySet[DEFAULT_INITIAL_CAPACITY];
        loadFactor = DEFAULT_LOAD_FACTOR;
        threshold = (int)(DEFAULT_INITIAL_CAPACITY*loadFactor);
    }

    public SortedHashedArraySet(int size) {
        int initialCapacity = Math.max((int)(size / DEFAULT_LOAD_FACTOR)+1, DEFAULT_INITIAL_CAPACITY);
        buckets = (SortedArraySet<T>[])new SortedArraySet[initialCapacity];
        loadFactor = DEFAULT_LOAD_FACTOR;
        threshold = (int)(initialCapacity*loadFactor);
    }
    
    public SortedHashedArraySet(Set<T> other) {
        int initialCapacity = Math.max((int)(other.size() / DEFAULT_LOAD_FACTOR)+1, DEFAULT_INITIAL_CAPACITY);
        buckets = (SortedArraySet<T>[])new SortedArraySet[initialCapacity];
        loadFactor = DEFAULT_LOAD_FACTOR;
        threshold = (int)(initialCapacity*loadFactor);
        addAll(other);
    }
    
    public boolean add(T elem) {
        int idx = hash(elem);
        Set<T> entries = buckets[idx];
        if (entries == null) {
            entries = new SortedArraySet<T>();
            buckets[idx] = entries;
        }
        if (entries.add(elem)) {
            hashCode += elem.hashCode();
            if (++size > threshold) {
                rehash();
            }
            return true;
        }
        return false;
    }

    private int hash(Object o) {
        return Math.abs(o.hashCode()) % buckets.length;
    }

    public void rehash() {
        Set<T>[] oldBuckets = buckets;
        int newCapacity = (buckets.length * 2) + 1;
        threshold = (int) (newCapacity * loadFactor);
        buckets = (SortedArraySet<T>[])new SortedArraySet[newCapacity];
        
        for (int i=0; i<oldBuckets.length; i++) {
            Set<T> entries = oldBuckets[i];
            if (entries != null) {
                for (T t : entries) {
                    int idx = hash(t);
                    Set<T> newEntries = buckets[idx];
                    if (newEntries == null) {
                        newEntries = new SortedArraySet<T>();
                        buckets[idx] = newEntries;
                    }
                    newEntries.add(t);
                }
            }
        }
    }

    public boolean addAll(Collection<? extends T> c) {
        boolean modified = false;
        for (T t : c) {
            if (add(t)) {
                modified = true;
            }
        }
        return modified;
    }

    public void clear() {
        throw new UnsupportedOperationException();
    }

    public boolean contains(Object o) {
        int idx = hash(o);
        Set<T> entries = buckets[idx];
        if (entries == null) {
            return false;
        }
        else {
            return entries.contains(o);
        }
    }

    public boolean containsAll(Collection<?> c) {
        Collection<T> cT = (Collection<T>)c;
        for (T t : cT) {
            if (!contains(t)) {
                return false;
            }
        }
        return true;
    }

    public boolean isEmpty() {
        return size == 0;
    }

    public Iterator<T> iterator() {
        return new SortedHashedArraySetIterator<T>();
//        Set<T> elems = new HashSet<T>();
//        for (int i=0; i<buckets.length; i++) {
//            Set<T> entries = buckets[i];
//            if (entries != null) {
//                elems.addAll(entries);
//            }
//        }
//        return elems.iterator();
    }
    
    private class SortedHashedArraySetIterator<V> implements Iterator<V> {
        int nextBucketIdx;
        Iterator<T> currItr;

        SortedHashedArraySetIterator() {
            nextBucketIdx = 0;
            if (buckets[nextBucketIdx] != null) {
                currItr = buckets[nextBucketIdx].iterator();
            }
        }

        public boolean hasNext() {
            if (currItr == null || !currItr.hasNext()) {
                while (++nextBucketIdx < buckets.length) {
                    Set<T> entries = buckets[nextBucketIdx];
                    if (entries != null) {
                        currItr = entries.iterator();
                        if (currItr.hasNext()) {
                            return true;
                        }
                        else {
                            currItr = null;
                        }
                    }
                }
                return false;
            }
            else {
                return true;
            }
        }

        @SuppressWarnings("unchecked")
        final public V next() throws NoSuchElementException {
            if(currItr == null) {
                throw new NoSuchElementException();
            }
            return (V) currItr.next();
        }

        final public void remove() throws NoSuchElementException {
            throw new UnsupportedOperationException();
        }
    }

    public boolean remove(Object o) {
        int idx = hash(o);
        Set<T> entries = buckets[idx];
        if (entries == null) {
            return false;
        }
        else if (entries.remove(o)) {
            size--;
            hashCode -= o.hashCode();
            return true;
        }
        else {
            return false;
        }
    }

    public boolean removeAll(Collection<?> c) {
        Collection<T> cT = (Collection<T>)c;
        boolean modified = false;
        for (T t : cT) {
            if (remove(t)) {
                modified = true;
            }
        }
        return modified;
    }

    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    public int size() {
        return size;
    }

    public Object[] toArray() {
        throw new UnsupportedOperationException();
    }

    public <T> T[] toArray(T[] a) {
        throw new UnsupportedOperationException();
    }
    
    @Override
    public String toString() {
        String s = "{";
//        boolean first = true;
//        for (T t : this) {
//            if (first) {
//                first = false;
//            }
//            else {
//                s += ",";
//            }
//            s += t.toString();
//        }
        for (int i=0; i<buckets.length; i++) {
            Set<T> entries = buckets[i];
            if (entries != null) {
                s += entries.toString();
            }
        }
        return s += "}";
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
        else if (o instanceof SortedHashedArraySet) {
            SortedHashedArraySet<T> s = (SortedHashedArraySet<T>)o;
            return size == s.size && containsAll(s);
        }
        else {
            return false;
        }
    }
    
}
