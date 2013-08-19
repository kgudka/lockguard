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


public class SortedArraySet<T> implements Set<T> {
    
    T[] elements;
    int size;
    int hashCode;
    
    public static final int DEFAULT_SIZE = 32;
    
    public SortedArraySet() {
        elements = (T[])new Object[DEFAULT_SIZE];
        size = 0;
        hashCode = 0;
    }
    
    public SortedArraySet(Set<T> other) {
        if (!(other instanceof SortedArraySet)) {
            throw new RuntimeException("other is not a SortedArraySet");
        }
        int newSize = other.size();
        if (newSize < DEFAULT_SIZE) {
            newSize = DEFAULT_SIZE;
        }
        else {
            newSize = other.size();
        }
        elements = (T[])new TransformerEdge[newSize];
        // We know other is a set so no need for containment testing
        // Assume that iteration order is the same as sort order
//        addAll(other);
        int i=0;
        for (T t : other) {
            elements[i++] = t;
            hashCode += hashCode(t);
        }
        size = i;
    }
    
    public boolean add(T elem) {
        boolean added = false;
        int idx = binarySearch(elem);
        if (idx < 0) { // elem not in set
            int ins = -(idx+1);
            if (size == elements.length) {
                expand(size*2);
            }
            System.arraycopy(elements, ins, elements, ins+1, (size-1-ins)+1);
            elements[ins] = elem;
            size++;
            added = true;
            hashCode += hashCode(elem);
        }
        return added;
    }
    
    private void expand(int newSize) {
        if (newSize > elements.length) {
            T[] newElements = (T[])new TransformerEdge[newSize];
            System.arraycopy(elements, 0, newElements, 0, size);
            elements = newElements;
        }
    }
    
    public boolean contains(Object elem) {
        return binarySearch((T)elem) >= 0;
    }
    
    private final int binarySearch(T elem) {
        int low = 0;
        int high = size-1;
        long key = key(elem);

        int count = 0;
        while (low <= high) {
            count++;
            int mid = (low + high) >> 1;
            T midVal = elements[mid];
            int cmp = compareTo(midVal, key);

            if (cmp < 0) {
                low = mid + 1;
            }
            else if (cmp > 0) {
                high = mid - 1;
            } else {
                // key found (look for specific element)
//                int start = mid;
//                while (start >= 0 && key(elements[start]) == key) {
//                    start--;
//                }
//                int i;
//                for (i=start+1; i<size; i++) {
//                    T e = elements[i];
//                    if (key(e) > key) {
//                        break;
//                    }
//                    else if (e.equals(elem)) {
//                        return i;
//                    }
//                }
//                return -(i + 1);
                return mid;
            }
        }
        return -(low + 1);  // key not found.
    }
    
    private int compareTo(T elem, long hashKey) {
        long elemKey = key(elem);
        if (elemKey < hashKey) {
            return -1;
        }
        else if (elemKey == hashKey) {
            return 0;
        }
        else {
            return 1;
        }
    }

    public boolean addAll(Collection<? extends T> other) {
        expand(size+other.size());
        boolean modified = false;
        for (T t : other) {
            if (add(t)) {
                modified = true;
            }
        }
        return modified;
    }

    public void clear() {
        throw new UnsupportedOperationException();
    }

    public boolean containsAll(Collection<?> other) {
        Collection<T> otherT = (Collection<T>)other;
        for (T t : otherT) {
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
        return new SortedArraySetIterator<T>();
    }
    
    private class SortedArraySetIterator<V> implements Iterator<V> {
        int nextIndex;

        SortedArraySetIterator() {
            nextIndex = 0;
        }

        final public boolean hasNext() {
            return nextIndex < size;
        }

        @SuppressWarnings("unchecked")
        final public V next() throws NoSuchElementException {
            if(!(nextIndex < size))
                throw new NoSuchElementException();

            return (V) elements[nextIndex++];
        }

        final public void remove() throws NoSuchElementException {
            throw new UnsupportedOperationException();
        }
    }

    public boolean remove(Object elem) {
        int idx = binarySearch((T)elem);
        if (idx < 0) { // key not found
            return false;
        }
        else {
            System.arraycopy(elements, idx+1, elements, idx, size-1-idx);
            elements[size-1] = null;
            size--;
            hashCode -= hashCode((T)elem);
            return true;
        }
    }

    public boolean removeAll(Collection<?> other) {
        Collection<T> otherT = (Collection<T>)other;
        boolean modified = false;
        for (T t : otherT) {
            if (remove(t)) {
                modified = true;
            }
        }
        return modified;
    }

    public boolean retainAll(Collection<?> arg0) {
        throw new UnsupportedOperationException();
    }

    public int size() {
        return size;
    }

    public Object[] toArray() {
        throw new UnsupportedOperationException();
    }

    public <T> T[] toArray(T[] arg0) {
        throw new UnsupportedOperationException();
    }
    
    @Override
    public String toString() {
        String s = "[";
        for (int i=0; i<size; i++) {
            if (i != 0) {
                s += ",";
            }
            s += key(elements[i]);
        }
        return s + "]";
    }
    
    @Override
    public int hashCode() {
        return hashCode;
    }
    
    private int hashCode(T t) {
        return t == null ? 0 : t.hashCode();
    }
    
    private final long key(T t) {
        return t.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        else if (o == null) {
            return false;
        }
        else if (o instanceof SortedArraySet) {
            SortedArraySet s = (SortedArraySet)o;
//                for (int i=0; i<size; i++) {
//                    if (elements[i] == null || s.elements[i] == null) {
//                        if (elements[i] != s.elements[i]) {
//                            return false;
//                        }
//                    }
//                    else if (!elements[i].equals(s.elements[i])) {
//                        return false;
//                    }
//                }
//                return true;
            return size == s.size && containsAll(s);
        }
        return false;
    }
    
    
}
