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

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

import lg.analysis.paths.transformer.fast.TransformerEdgeFactory;

import soot.jimple.Stmt;

public class StateFactory {

    static Map<Stmt,State> stmtToState = new ConcurrentHashMap<Stmt, State>();
    static Map<Integer,State> numToState = new ConcurrentHashMap<Integer, State>();
    static Map<Set<State>,State> statesToState = new ConcurrentHashMap<Set<State>, State>();
    
    private StateFactory() { }
    
    // units in a method will be processed by the same thread
    // (later calls to this method will only access the the state and not
    // cause one to be created).
    public static State v(Stmt n) {
        State s = stmtToState.get(n);
        if (s == null) {
            synchronized(stmtToState) {
                s = stmtToState.get(n);
                if (s == null) {
                    s = new State(n);
                    stmtToState.put(n, s);
                    numToState.put(s.getNumber(), s);
                }
            }
        }
        return s;
    }
    
    public static State lookup(int i) {
        if (i == TransformerEdgeFactory.START_STATE) {
            return StartState.v();
        }
        else {
            State s = numToState.get(i);
            if (s == null) {
                throw new UnsupportedOperationException("state is null: " + i);
            }
            return s;
        }
    }
    
    public static State v(Set<State> states) {
        State s = statesToState.get(states);
        if (s == null) {
            if (states.size() == 1) {
                s = states.iterator().next();
            }
            else {
//                s = new State();
                s = new DfaState(states);
            }
            statesToState.put(states, s);
        }
        return s;
    }

    public static void clear() {
        statesToState.clear();
        stmtToState.clear();
    }
    
    public static Map<Integer, State> getNumToStateMap() {
        return numToState;
    }
    
    public static void setNumToStateMap(Map<Integer, State> map) {
        numToState = map;
    }
    
}
