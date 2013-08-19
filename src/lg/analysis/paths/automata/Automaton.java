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

import java.io.*;
import java.util.*;

import lg.analysis.locks.AutomatonToLocks;
import lg.analysis.paths.ContainingMethodTag;
import lg.analysis.paths.transformer.state.*;
import lg.util.*;
import soot.*;
import soot.jimple.Stmt;

public class Automaton implements Serializable {
    
    private static final long serialVersionUID = 1L;
    
    State start;
    Map<State,Set<Transition>> stateToTransitions;
    
    public Automaton(State initial) {
        start = initial;
        stateToTransitions = new HashMap<State, Set<Transition>>();
    }
   
    public void addTransition(Transition t) {
        State src = t.getSrc();
        Set<Transition> srcTransitions = stateToTransitions.get(src);
        if (srcTransitions == null) {
            srcTransitions = new HashSet<Transition>();
            stateToTransitions.put(src, srcTransitions);
        }
        srcTransitions.add(t);
    }
    
    // removes states (and edges) not reachable from the start state
    public Set<State> cleanup() {
        // delete states which are not reachable
        Set<State> reachables = new HashSet<State>();
        cleanupHelper(start, reachables);
        Set<State> kill = new HashSet<State>();
        for (State s : stateToTransitions.keySet()) {
            if (!reachables.contains(s)) {
                kill.add(s);
            }
        }
        for (State s : kill) {
            stateToTransitions.remove(s);
        }
        return reachables;
    }
    
    private void cleanupHelper(State s, Set<State> reachables) {
        if (!reachables.contains(s)) {
            reachables.add(s);
            Set<Transition> transitions = stateToTransitions.get(s);
            if (transitions != null) {
                for (Transition t : transitions) {
                    State s2 = t.getDst();
                    cleanupHelper(s2, reachables);
                }
            }
        }
    }
    
    public int size() {
        int size = 0;
        for (Set<Transition> ts : stateToTransitions.values()) {
            size += ts.size();
        }
        return size;
    }
    
    public void outputDegrees() {
        SortedSet<Integer> degrees = new TreeSet<Integer>();
        for (Set<Transition> ts : stateToTransitions.values()) {
            degrees.add(ts.size());
        }
        try {
            PrintWriter p = new PrintWriter("degrees.txt");
            for (Integer i : degrees) {
                p.println(i);
            }
            p.flush();
            p.close();
        }
        catch (Exception e) {
            throw new RuntimeException(e);
        }
        
    }

    public void outputDot(String filename, AutomatonToLocks a) {
        Set<State> cycleStates = a == null? null : a.getCycleStates();
        try {
            PrintWriter p = new PrintWriter(filename);
            p.println("digraph automaton {");
            p.println("\trankdir=LR;");
            p.println("\tranksep=\"2in\";");

            Set<State> visited = new HashSet<State>();
            Stack<State> tovisit = new Stack<State>();
            tovisit.push(start);

            while (!tovisit.isEmpty()) {
                State s = tovisit.pop();
                String cycleStr = cycleStates == null ? "" : (cycleStates.contains(s) ? ",style=filled,color=lightgray" : "");
                p.println("\t\t" + s.getNumber() + " [label=\"" + s.toString() + "\"" + cycleStr + "];");
                visited.add(s);
                Set<Transition> transitions = stateToTransitions.get(s);
                if (transitions != null) {
                    for (Transition t : transitions) {
                        State d = t.getDst();
                        cycleStr = cycleStates == null ? "" : (cycleStates.contains(d) ? ",style=filled,color=lightgray" : "");
                        Stmt st = d.getStmt();
                        ContainingMethodTag tag = (ContainingMethodTag)st.getTag(ContainingMethodTag.TAG_NAME);
                        SootMethod m = null;
                        if (tag != null) {
                            m = tag.getMethod();
                        }
//                        Logger.println("state: " + d.toString());
//                        Logger.println("stmt: " + st);
//                        Logger.println("method: " + m);
//                        Logger.println("------------");
                        p.println("\t\t" + d.getNumber() + " [label=\"" + d.toString() + "\"" + cycleStr + "];");
                        Object l = t.getLbl();
                        String lStr = lblToString(l);
                        String colour = t.isWrite() ? "red" : "blue";
                        p.println("\t\t" + s.getNumber() + " -> " + d.getNumber() + " [label=\"" + lStr + "\",color=\"" + colour + "\"];");
                        if (!tovisit.contains(d) && !visited.contains(d)) {
                            tovisit.push(d);
                        }
                    }
                }
            }
            
            p.println("}");
            p.close();
        }
        catch (FileNotFoundException fnfe) {
            throw new RuntimeException(fnfe);
        }
    }
    
    private String lblToString(Object o) {
        if (o instanceof SootField) {
            SootField f = (SootField)o;
            return f.getName();
        }
        else if (o instanceof SootClass) {
            SootClass c = (SootClass)o;
            return c.getName();
        }
        else if (o instanceof Local) {
            Local l = (Local)o;
            return l.getName();
        }
        return o.toString();
    }

    public Pair<Map<State,Set<State>>,Automaton> convertToDfa() {

        Automaton dfa = new Automaton(start);

        // unmarked stores dfa states yet to be processed,
        // marked stores dfa states already processed
        Stack<Set<State>> unmarked = new Stack<Set<State>>();
        Set<Set<State>> marked = new HashSet<Set<State>>();
        
        // we begin from the start state (we stick with sets as it's easier)
        Set<State> startSet = new HashSet<State>();
        startSet.add(start);
        unmarked.push(startSet);
        
        while (!unmarked.isEmpty()) {
            Set<State> sources = unmarked.pop();
            marked.add(sources);
            State src = StateFactory.v(sources);
            Map<Object,Boolean> labelToRW = getAllOutgoingLabelsRW(sources);
            for (Object lbl : labelToRW.keySet()) {
                Set<State> dests = getAllDests(sources, lbl);
                State dst = StateFactory.v(dests);
                boolean write = labelToRW.get(lbl).booleanValue(); // ?
                dfa.addTransition(new Transition(src, dst, lbl, write));
                if (!marked.contains(dests) && !unmarked.contains(dests)) {
                    unmarked.push(dests);
                }
            }
        }

        // build up mapping from nfa states to dfa states
        Map<State,Set<State>> nfaStateToDfaStates = new HashMap<State, Set<State>>();
        for (Set<State> nfaStates : marked) {
            addNfaStatesToDfaStatesMapping(nfaStateToDfaStates, nfaStates, StateFactory.v(nfaStates)); // update mapping
        }
        
        return new Pair<Map<State,Set<State>>, Automaton>(nfaStateToDfaStates, dfa);
    }

    private void addNfaStatesToDfaStatesMapping(Map<State, Set<State>> nfaStateToDfaStates, Set<State> nfaStates, State dfaState) {
        for (State nfaState : nfaStates) {
            Set<State> dfaStates = nfaStateToDfaStates.get(nfaState);
            if (dfaStates == null) {
                dfaStates = new HashSet<State>();
                nfaStateToDfaStates.put(nfaState, dfaStates);
            }
            dfaStates.add(dfaState);
        }
    }

    private Set<Object> getAllOutgoingLabels(Set<State> states) {
        Set<Object> labels = new HashSet<Object>();
        for (State s : states) {
            Set<Transition> transitions = stateToTransitions.get(s);
            if (transitions != null) {
                for (Transition t : transitions) {
                    labels.add(t.getLbl());
                }
            }
        }
        return labels;
    }
    
    private Map<Object,Boolean> getAllOutgoingLabelsRW(Set<State> states) {
        Map<Object,Boolean> labelToRW = new HashMap<Object, Boolean>();
        for (State s : states) {
            Set<Transition> transitions = stateToTransitions.get(s);
            if (transitions != null) {
                for (Transition t : transitions) {
                    Object lbl = t.getLbl();
                    Boolean write = labelToRW.get(lbl);
                    if (write == null) {
                        write = t.isWrite();
                    }
                    else if (!write.booleanValue()) { // if currently read, update with t's RW
                        write = t.isWrite();
                    }
                    labelToRW.put(lbl, write);
                }
            }
        }
        return labelToRW;
    }    
    
    private Set<State> getAllDests(Set<State> sources, Object lbl) {
        Set<State> dests = new HashSet<State>();
        for (State s : sources) {
            Set<Transition> transitions = stateToTransitions.get(s);
            if (transitions != null) {
                for (Transition t : transitions) {
                    if (t.getLbl().equals(lbl)) {
                        dests.add(t.getDst());
                    }
                }
            }
        }
        return dests;
    }
    
    public Set<State> getStates() {
        return stateToTransitions.keySet();
    }
    
    public State getStartState() {
        return start;
    }
    
    public Set<Transition> getTransitions(State s) {
        return stateToTransitions.get(s);
    }
    
    public Collection<Set<Transition>> getTransitions() {
//        Set<Transition> ts = new HashSet<Transition>();
//        for (Set<Transition> t : stateToTransitions.values()) {
//            ts.addAll(t);
//        }
//        return ts;
        return stateToTransitions.values();
    }
    
}
