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

package lg.analysis.paths.automata;

import java.io.Serializable;

import lg.analysis.paths.transformer.state.State;

public class Transition implements Serializable {
    
    private static final long serialVersionUID = 1L;
    
    final State src;
    final State dst;
    final Object lbl;
    final boolean write;
    final int hashCode;
    
    public Transition(State s, State d, Object l, boolean w) {
        src = s;
        dst = d;
        lbl = l;
        write = w;
//        hashCode = xorHash();
        hashCode = DJBHash();
    }
    
    private int xorHash() {
        return src.hashCode() ^ dst.hashCode() ^ lbl.hashCode();
    }
    
    private int DJBHash() {
        int hash = 5381;
        hash = ((hash << 5) + hash) + src.hashCode();
        hash = ((hash << 5) + hash) + dst.hashCode();
        hash = ((hash << 5) + hash) + lbl.hashCode();
        return hash;
    }    
    
    public State getSrc() {
        return src;
    }
    
    public State getDst() {
        return dst;
    }
    
    public Object getLbl() {
        return lbl;
    }
    
    public boolean isWrite() {
        return write;
    }
    
    public int hashCode() {
        return hashCode;
    }

    public boolean equals(Transition o) {
        if (o == this) {
            return true;
        }
        else if (o == null) {
            return false;
        }
        else if (o instanceof Transition) {
            Transition ot = (Transition)o;
            return src == ot.src && dst == ot.dst && lbl.equals(ot.lbl) && write == ot.write; 
        }
        else {
            return false;
        }
    }
    
    @Override
    public String toString() {
        return src.getNumber() + "--(" + lbl + "," + write + ")-->" + dst.getNumber();
    }
}