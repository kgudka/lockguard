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

package lg.runtime;

public enum LockMode {
    NONE (0) { // N
        boolean isCompatibleWith(LockMode m) { return true; } 
    },
    READ (2) { // S
        boolean isCompatibleWith(LockMode m) { return m == READ || m == INTENTION_READ; }
    }, 
    WRITE (4) { // X
        boolean isCompatibleWith(LockMode m) { return false; }
    }, 
    INTENTION_READ (1) { // IS
        boolean isCompatibleWith(LockMode m) { return m == READ || m == INTENTION_READ || m == INTENTION_WRITE; }
    },
    INTENTION_WRITE (2) { // IX
        boolean isCompatibleWith(LockMode m) { return m == INTENTION_READ || m == INTENTION_WRITE; }
    },
    READ_INTENTION_WRITE (3) { // SIX
        boolean isCompatibleWith(LockMode m) { return m == INTENTION_READ; } 
    };
    
    int order;
    
    private LockMode(int o) {
        order = o;
    }
    
    public LockMode lub(LockMode m) {
        if (this == m) {
            return this;
        }
        else if (order > m.order) {
            return this;
        }
        else if (order < m.order) { 
            return m;
        }
        else { // note: order == m.order && this != m, hence must be S U IX = SIX
            return READ_INTENTION_WRITE;
        }
    }
    
    public boolean doesNotSubsume(LockMode m) {
        return order < m.order || (this != m && order == m.order);
    }
    
    abstract boolean isCompatibleWith(LockMode m);
    
}
