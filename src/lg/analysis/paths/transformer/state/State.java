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

package lg.analysis.paths.transformer.state;

import java.io.Serializable;

import lg.analysis.paths.transformer.fast.TransformerEdgeFactory;

import soot.jimple.Stmt;
import soot.util.Numberable;

public class State implements Numberable, Serializable {
    
    private static final long serialVersionUID = -8076415227657336062L;
    
    static int counter = TransformerEdgeFactory.INITIAL_STATE_COUNTER;
    int number;
    
    Stmt n;
    
    public State(Stmt nn) {
        number = counter++;
        n = nn;
    }

    public State() {
        this(null);
    }
    
    public int getNumber() {
        return number;
    }
    
    public Stmt getStmt() {
        return n;
    }
    
    public void setNumber(int number) {
        throw new RuntimeException("Method State.setNumber(int) not yet implemented");
    }
    
    @Override
    public String toString() {
        return "" + n + " (" + number + ")";
    }
    
    public static int getCounterValue() {
        return counter;
    }
    
    public static void setCounterValue(int c) {
        counter = c;
    }
    
}
