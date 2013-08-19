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

package lg.analysis.paths.transformer.slow;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import lg.analysis.paths.automata.*;
import lg.analysis.paths.transformer.state.*;
import lg.transformer.AtomicTransformer;
import lg.util.*;
import soot.*;
import soot.util.ArraySet;

public class Transformer implements Cloneable, Serializable {
    	
    private static final long serialVersionUID = 1L;
    
    Map<Object,Set<TransformerEdge>> map;
	static final JumpFunction idJumpFn = IdentityJumpFunction.v();
	static final JumpFunction storeJumpFn = StoreJumpFunction.v();
	static final KillTransformerEdge killEdge = KillTransformerEdge.v();
	static final Access capitalLambda = Access.v();
	static final ArrayElement arrElem = ArrayElement.v();
	static final ReturnVariable retVar = ReturnVariable.v();
	static final ThisVariable thisVar = ThisVariable.v();
	static final State startState = StartState.v();
	
	public Transformer() {
		map = new HashMap<Object, Set<TransformerEdge>>(8);
	}
	
	// Overwrite with contents from t.
	// Differs from unionWith, as it doesn't make implicit edges explicit.
	public void overwriteWith(Transformer t) {
		// don't use map.putAll as it causes problems due to aliasing
	    // (it doesn't create new HashSets)
		for (Object o : t.map.keySet()) {
			map.put(o, newEdgeSet(t.map.get(o)));
		}
	}
	
	// Is this >= t
	public boolean subsumes(Transformer t) {
	    Set<Object> keys = map.keySet();
	    if (keys.containsAll(t.map.keySet())) {
	        for (Object o : keys) {
	            Set<TransformerEdge> edges = new HashSet<TransformerEdge>(map.get(o));
	            Set<TransformerEdge> tEdges = t.map.get(o);
	            if (tEdges != null) {
	                tEdges = new HashSet<TransformerEdge>(tEdges);
	            }
	            if (tEdges != null && !edges.containsAll(tEdges)) {
	                return false;
	            }
	        }
	        return true;
	    }
	    else {
	        return false;
	    }
	}
	
	public void unionWith(Transformer t) {
		// Merge 'this' with 't'
		// Remember to make implicit edges explicit where necessary
		for (Object o : map.keySet()) {
			Set<TransformerEdge> edges = new HashSet<TransformerEdge>(map.get(o));
			Set<TransformerEdge> tEdges = t.map.get(o);
			if (tEdges == null) {
				if (o != capitalLambda) {
					// make implicit edge explicit
					edges.add(new TransformerEdge(idJumpFn, o));
				}
			}
			else {
				edges.addAll(tEdges);
			}
			map.put(o, newEdgeSet(edges));
		}
		// Merge remaining edges in 't' with 'this' and make implicit edges
		// explicit where necessary
		for (Object o : t.map.keySet()) {
		    if (!map.containsKey(o)) {
    			Set<TransformerEdge> tEdges = t.map.get(o);
    			Set<TransformerEdge> edges = map.get(o);
    			if (edges == null) {
    				// make implicit edge explicit unless i == A
    				edges = new HashSet<TransformerEdge>();
    				if (o != capitalLambda) {
    					edges.add(new TransformerEdge(idJumpFn, o));
    				}
    				//map.put(o, edges);
    			}
    			else {
    			    edges = new HashSet<TransformerEdge>(edges);
    			}
    			edges.addAll(tEdges);
    			map.put(o, newEdgeSet(edges));
		    }
		}
		
		cleanup(this);
	}

	// t o this
	public Transformer composeWith(Transformer t) {
		if (this instanceof IdentityTransformer || map.isEmpty()) {
			return t;
		}
		else if (t instanceof IdentityTransformer || t.map.isEmpty()) {
			return this;
		}
		else {
			Transformer closure = new Transformer();
			for (Object o : map.keySet()) {
				Set<TransformerEdge> edges = map.get(o);
				Set<TransformerEdge> newEdges = new HashSet<TransformerEdge>();
				// transitive closure
				for (TransformerEdge te : edges) {
					if (te == killEdge) {
						// o --> e goes through (note we have implicit e --> e)
						newEdges.add(te);
					}
					else {
						// o --> d
						Object d = te.getDest();
						Set<TransformerEdge> dEdges = t.map.get(d);
						if (dEdges == null) {
							// implicit edge in t
							newEdges.add(te);
						}
						else {
							for (TransformerEdge te2 : dEdges) {
								if (te2 == killEdge) {
									newEdges.add(te2);
								}
								else {
									newEdges.add(new TransformerEdge(composeJumpFunctions(te.getJumpFunction(),te2.getJumpFunction()),te2.getDest()));
								}
							}
						}
					}
				}
				closure.map.put(o, newEdges);
			}
			// take account of implicit edges in 'this' transformer. 
			for (Object o : t.map.keySet()) {
				if (o == capitalLambda) {
					// implicit A --> A edge in 'this'. Pass on accesses.
					Set<TransformerEdge> transEdges = closure.map.get(o);
					if (transEdges == null) {
						transEdges = new HashSet<TransformerEdge>();
						closure.map.put(o, transEdges);
					}
					Set<TransformerEdge> accesses = t.map.get(o);
					transEdges.addAll(accesses);
				}
				else {
					Set<TransformerEdge> edges = map.get(o);
					if (edges == null) {
					    // implicit edge o --> o exists in 'this'
						Set<TransformerEdge> transEdges = closure.map.get(o);
						if (transEdges == null) { // transEdges should always be null here
							transEdges = new HashSet<TransformerEdge>();
							closure.map.put(o, transEdges);
						}
						Set<TransformerEdge> oEdges = t.map.get(o);
						transEdges.addAll(oEdges);
					}
				}
			}

			cleanup(closure);
			
			// use compact ArraySet for storage
//			for (Entry<Object,Set<TransformerEdge>> e : closure.map.entrySet()) {
//			    Object k = e.getKey();
//			    Set<TransformerEdge> v = e.getValue();
//			    closure.map.put(k, newEdgeSet(v));
//			}
			
			return closure;
		}
	}
	
	// NOT SURE IF THIS IS SOUND
	// clean up -->e edges and redundant x --> x transformer edges
	// This is required to keep the transformer as sparse as possible
	private void cleanup(Transformer t) {
		Set<Object> kill = new HashSet<Object>();
		for (Object o : t.map.keySet()) {
			Set<TransformerEdge> edges = t.map.get(o);
			if (edges.size() > 1) {
				edges.remove(killEdge);
			}
			if (edges.size() == 1) {
				for (TransformerEdge te : edges) {
					if (te.getJumpFunction() == idJumpFn && te.getDest() == o) {
						kill.add(o);
					}
					else if (o == capitalLambda && te == killEdge) {
						kill.add(o);
					}
				}
			}
			else if (edges.size() == 0) {
				kill.add(o);
			}
		}
		for (Object o : kill) {
			t.map.remove(o);
		}
	}
	
	private JumpFunction composeJumpFunctions(JumpFunction f1, JumpFunction f2) {
		if (f1 == idJumpFn) {
			return f2;
		}
		else if (f2 == idJumpFn) {
			return f1;
		}
		else if (f1 instanceof EdgeJumpFunction) {
			EdgeJumpFunction e1 = (EdgeJumpFunction)f1;
			if (f2 instanceof LoadJumpFunction) {
				LoadJumpFunction l2 = (LoadJumpFunction)f2;
				return new EdgeJumpFunction(l2.getN(), e1.getDst(), e1.isWrite());
			}
			else if (f2 == storeJumpFn) {
				return new EdgeJumpFunction(startState, e1.getDst(), e1.isWrite());
			}
		}
		else if (f1 instanceof LoadJumpFunction && f2 == storeJumpFn) {
			return f2;
		}
		else if (f1 == storeJumpFn && f2 instanceof LoadJumpFunction) {
			return f2;
		}
		else if (f1 instanceof LoadJumpFunction && f2 instanceof LoadJumpFunction) {
			return f2;
		}
		else if (f1 == storeJumpFn && f2 == storeJumpFn) {
			return f2;
		}
		throw new RuntimeException("Unknown pair of jump functions: f1 = " + f1.toString() + ", f2 = " + f2.toString());
	}

	/*public Transformer clone() {
		try {
			Transformer t = (Transformer)super.clone();
			t.map = new HashMap<Object, Set<TransformerEdge>>(map);
			return t;
		} catch (CloneNotSupportedException e) {
			throw new RuntimeException(e);
		}
	}*/
	
	public int hashCode() {
		return map.hashCode();
	}
	
	@Override
	public boolean equals(Object other) {
		if (other == this) {
			return true;
		}
		else if (other == null) {
			return false;
		}
		/*else if (o.getClass() != getClass()) {
			return false;
		}*/
		else {
			if (other instanceof Transformer) {
				Transformer t = (Transformer) other;
				if (map.keySet().equals(t.map.keySet())) {
				    for (Object o : map.keySet()) {
				        Set<TransformerEdge> edges = map.get(o);
				        Set<TransformerEdge> tEdges = t.map.get(o);
				        if (edges == null || tEdges == null) {
				            if (edges != tEdges) {
				                return false;
				            }
				        }
				        else {
				            // using HashSets are much faster
				            edges = new HashSet<TransformerEdge>(edges);
				            tEdges = new HashSet<TransformerEdge>(tEdges);
				            if (!edges.equals(tEdges)) {
				                return false;
				            }
				        }
				    }
				    return true;
				}
				else {
				    return false;
				}
				//return map.equals(t.map);
			}
			else {
				return false;
			}
		}
	}
	
	@Override
	public String toString() {
		return map.toString();
		/*String s = "{";
		for (Object o : map.keySet()) {
			Local x = (Local)o;
			s += x.getName() + "(" + x.getNumber() + "),";
		}
		return s + "}";*/
	}

	// returns a copy of this transformer but without any method local vars
	public Transformer removeMethodLocalVars() {
		Transformer t = new Transformer();
		for (Object o : map.keySet()) {
			if (o instanceof Local) {
				// skip
				continue;
			}
			else {
				Set<TransformerEdge> edgesToKeep = new HashSet<TransformerEdge>();
				for (TransformerEdge te : map.get(o)) {
					if (te == killEdge) {
						edgesToKeep.add(te);
					}
					else if (!(te.getDest() instanceof Local)) {
						edgesToKeep.add(te);
					}
				}
				if (!edgesToKeep.isEmpty()) {
					t.map.put(o, newEdgeSet(edgesToKeep));
				}
			}
		}
		cleanup(t);
		return t;
	}
	
	public void removeParamVarsAndRetVar() {
		Set<Object> kill = new HashSet<Object>();
		for (Object o : map.keySet()) {
			if (o == thisVar || o == retVar || o instanceof ParameterVariable) {
				kill.add(o);
			}
		}
		for (Object o : kill) 
			map.remove(o);
	}

	// renames params in transformer to args, wrt the given mapping
	public Transformer calleeToCallerContext(Map<ParameterVariable,Local> paramsToArgs) {
		Transformer t = new Transformer();
		for (Object o : map.keySet()) {
			if (o == retVar && paramsToArgs.get(o) == null) {
				// return value is not used by caller so ignore edges $ret --> *
				continue;
			}
			Set<TransformerEdge> newEdges = new HashSet<TransformerEdge>();
			for (TransformerEdge te : map.get(o)) {
				Object d = te.getDest();
				if (d instanceof ParameterVariable || d == thisVar) {
					Local arg = paramsToArgs.get(d);
					if (arg == null) {
						newEdges.add(killEdge);
					}
					else {
						newEdges.add(new TransformerEdge(te.getJumpFunction(), arg));
					}
				}
				else {
					newEdges.add(te);
				}
			}
			// rename $ret to actual return variable
			if (o == retVar) {
				o = paramsToArgs.get(o);
			}
			t.map.put(o, newEdgeSet(newEdges));
		}
		cleanup(t);
		
		/*Local actualRetVar = paramsToArgs.get(retVar);
		if (actualRetVar != null) {
			// insert actualRetVar --> e, if no mapping for it exists already
			Set<TransformerEdge> edges = t.map.get(actualRetVar);
			if (edges == null) {
				edges = new HashSet<TransformerEdge>(4);
				edges.add(killEdge);
				t.map.put(actualRetVar, edges);
			}
		}*/
		return t;
	}
	
	public int edgeCount() {
		int count = 0;
		for (Set<TransformerEdge> edges : map.values()) {
			count += edges.size();
		}
		return count;
	}
	
	public void results() {
		try {
			int count = 0;
			PrintWriter p = new PrintWriter("results.txt");
			for (Object o : map.keySet()) {
				Set<TransformerEdge> edges = map.get(o);
				p.println(o.toString() + ": " + edges.size());
				count += edges.size();
			}
			p.println(count);
			p.flush();
			p.close();
		}
		catch(FileNotFoundException e) {
			throw new RuntimeException(e);
		}
	}
	
	/*
	   example transformer in dot
	   digraph G {
 	   		ranksep="5in"
	   		rankdir=BT;
	   		node [shape=record];
			incoming [label = "<a> a |<b> b |<c> c |<d> d", rank=1, width="4in"];
			outgoing [label = "<a> a |<b> b |<c> c |<d> d", rank=2, width="4in"];
			outgoing -> incoming [weight=10000,style=invis];
			incoming:a -> outgoing:b ;
			incoming:a -> outgoing:c [label="L(1,2)"];
			incoming:a -> outgoing:c [label="L(1,3)"];
			incoming:b -> outgoing:c [label="L(0,2)"];
	   }
	 * 
	 */
	
	public void outputDot(SootMethod m, boolean aggregate, String filename) {
//		System.out.println("---");
//		System.out.println(m.toString());
//		System.out.println(this);
		try {
			PrintWriter p = new PrintWriter(filename);
			p.println("digraph m" + m.getNumber() + " {");
			p.println("\tlabel=\"" + m.toString() + "\";");
			p.println("\tlabelloc=t;");
 			p.println("\tranksep=\"5in\"");
 		    p.println("\trankdir=BT;");
 		    p.println("\tnode [shape=record];");
			
			// determine the set D
			Set<Object> d = new HashSet<Object>();
			for (Object o : map.keySet()) {
				d.add(o);
				Set<TransformerEdge> edges = map.get(o);
				for (TransformerEdge e : edges) {
					if (e == killEdge) { continue; }
					d.add(e.getDest());
				}
			}
			int dSize = d.size();
			
			String label = "<access> &#x039B; | <kill> &#x2205;";
			for (Object o : d) {
				
				if (o == capitalLambda) {
					continue;
				}
				
				label += " | ";
				
				if (o instanceof SootField) {
					SootField f = (SootField)o;
					label += ("<f" + SymbolNumberer.getNumber(f) +"> ." + f.getName()/* + " (" + f.getType() + ")"*/);
				}
				else if (o instanceof SootClass) {
					SootClass c = (SootClass)o;
					label += ("<class" + SymbolNumberer.getNumber(c) + "> " + c.getName());
				}
				else if (o instanceof Local) {
					Local l = (Local)o;
					label += ("<l" + SymbolNumberer.getNumber(l) +"> " + l.getName());
				}
				else if (o == arrElem) {
					label += ("<arr> []");
				}
				else if (o == retVar) {
					label += ("<r> $r");
				}
				else if (o == thisVar) {
					label += ("<this> @this");
				}
				else if (o instanceof ParameterVariable) {
					ParameterVariable param = (ParameterVariable)o;
					label += ("<p" + param.getNum() + "> @param" + param.getNum());
				}
				else {
					throw new RuntimeException("Unsupported symbol: " + o);
				}
			}
			
			p.println("\tincoming [label=\"" + label + "\",width=\"" + dSize + "in\"];");
			p.println("\toutgoing [label=\"" + label + "\",width=\"" + dSize + "in\"];");
			p.println("\toutgoing -> incoming [weight=10000,style=invis];");
			
			for (Object o1 : d) {
				Set<TransformerEdge> edges = map.get(o1);
				String colour = o1 == capitalLambda ? "green" : "black";
				if (edges != null) {
				    String s1 = determineSymbolId(o1);
				    if (aggregate) {
				        Map<Object, Integer> aggregateCounts = new HashMap<Object, Integer>();
	                    for (TransformerEdge te : edges) {
//	                      System.out.println(te);
	                        Object o2 = te.getDest();
	                        Integer oldAggregateCount = aggregateCounts.get(o2);
	                        int newAggregateCount = (oldAggregateCount == null) ? 1 : oldAggregateCount.intValue() + 1;
	                        aggregateCounts.put(o2, newAggregateCount);
	                    }
	                    for (Object o2 : aggregateCounts.keySet()) {
	                        String s2 = determineSymbolId(o2);
	                        p.println("\tincoming:" + s1 + " -> outgoing:" + s2 + " [label=\"" + aggregateCounts.get(o2) + "\"fontcolor=\"" + colour + "\",color=\"" + colour + "\"];");
	                    }
				    }
				    else {
    					for (TransformerEdge te : edges) {
    //						System.out.println(te);
    						Object o2 = te.getDest();
    						String s2 = determineSymbolId(o2);
    						p.println("\tincoming:" + s1 + " -> outgoing:" + s2 + " [label=\"" + edgeLabel(te) + "\"fontcolor=\"" + colour + "\",color=\"" + colour + "\"];");
    					}
				    }
				}
			}
			
			p.println("}");
			p.flush();
			p.close();
		}
		catch(FileNotFoundException e) {
			throw new RuntimeException(e);
		}
	}
	
	private String edgeLabel(TransformerEdge te) {
		JumpFunction fn = te.getJumpFunction();
		if (fn != null) {
			if (fn instanceof LoadJumpFunction) {
				LoadJumpFunction lfn = (LoadJumpFunction)fn;
				return "L("+lfn.getN().getNumber()+")";
			}
			else if (fn instanceof StoreJumpFunction) {
				return "S";
			}
			else if (fn instanceof IdentityJumpFunction) {
				return "";
			}
			else {
				EdgeJumpFunction efn = (EdgeJumpFunction)fn;
				State src = efn.getSrc();
				State dst = efn.getDst();
				return "(" + (src == null ? 0 : src.getNumber())  + "," + dst.getNumber() + ")";
			}
		}
		return "";
	}
	
	private String determineSymbolId(Object o) {
		if (o == capitalLambda) {
			return "access";
		}
		else if (o == null) {
			return "kill";
		}
		else if (o instanceof SootField) {
			SootField f = (SootField)o;
			return "f" + SymbolNumberer.getNumber(f);
		}
		else if (o instanceof SootClass) {
			SootClass c = (SootClass)o;
			return "class" + SymbolNumberer.getNumber(c);
		}
		else if (o instanceof Local) {
			Local l = (Local)o;
			return "l" + SymbolNumberer.getNumber(l);
		}
		else if (o == arrElem) {
			return "arr";
		}
		else if (o == retVar) {
			return "r";
		}
		else if (o == thisVar) {
			return "this";
		}
		else if (o instanceof ParameterVariable) {
			ParameterVariable param = (ParameterVariable)o;
			return "p" + param.getNum();
		}
		else {
			throw new RuntimeException("Unknown symbol " + o);
		}
	}
	
	public Automaton getAccessesNfa() {
	    Automaton nfa = new Automaton(startState);
	    Set<TransformerEdge> accesses = map.get(capitalLambda);
	    if (accesses != null) {
    	    for (TransformerEdge te : accesses) {
    	        EdgeJumpFunction fn = (EdgeJumpFunction)te.getJumpFunction();
    	        // convert transformer edge into automaton transition
    	        State src = fn.getSrc();
    	        State dst = fn.getDst();
    	        Object lbl = te.getDest();
    	        boolean write = fn.isWrite();
    	        nfa.addTransition(new Transition(src, dst, lbl, write));
    	    }
	    }
	    return nfa;
	}
	
	public Transformer removeDeadEdges() {
	    Automaton nfa = getAccessesNfa();
	    Set<State> reachables = nfa.cleanup();

        Set<TransformerEdge> accessEdges = new HashSet<TransformerEdge>();
        for (Transition tn : nfa.getTransitions()) {
            accessEdges.add(new TransformerEdge(new EdgeJumpFunction(tn.getSrc(), tn.getDst(), tn.isWrite()), tn.getLbl()));
        }
            
        Transformer result = new Transformer();
        result.map.put(capitalLambda, newEdgeSet(accessEdges));
            
        for (Object d : map.keySet()) {
            if (d != capitalLambda) {
                Set<TransformerEdge> dEdges = map.get(d);
                Set<TransformerEdge> newEdges = new HashSet<TransformerEdge>();
                for (TransformerEdge dEdge : dEdges) {
                    JumpFunction fn = dEdge.getJumpFunction();
                    if (fn instanceof LoadJumpFunction) {
                        LoadJumpFunction lfn = (LoadJumpFunction)fn;
                        State n = lfn.getN();
                        if (reachables.contains(n)) {
                            newEdges.add(dEdge);
                        }
                    }
                    else {
                        newEdges.add(dEdge);
                    }
                }
                if (!newEdges.isEmpty()) {
                    result.map.put(d, newEdgeSet(newEdges));
                }
            }
        }
        
        return result;
	}
	
	public Transformer removeRedundancy() {
	    Automaton nfa = getAccessesNfa();
	    Pair<Map<State,Set<State>>, Automaton> p = nfa.convertToDfa();
	    Automaton dfa = p.getSecond();
	    
	    Set<TransformerEdge> accessEdges = newEdgeSet();
	    for (Transition tn : dfa.getTransitions()) {
	        accessEdges.add(new TransformerEdge(new EdgeJumpFunction(tn.getSrc(), tn.getDst(), tn.isWrite()), tn.getLbl()));
	    }
	    
	    Transformer result = new Transformer();
	    result.map.put(capitalLambda, accessEdges);
	    
	    // now update load edges and pass on all other transformer edges
	    Map<State,Set<State>> nfaStateToDfaStates = p.getFirst();
	    
	    for (Object d : map.keySet()) {
	        if (d != capitalLambda) {
	            Set<TransformerEdge> dEdges = map.get(d);
	            Set<TransformerEdge> newEdges = newEdgeSet();
	            for (TransformerEdge dEdge : dEdges) {
	                JumpFunction fn = dEdge.getJumpFunction();
	                if (fn instanceof LoadJumpFunction) {
	                    LoadJumpFunction lfn = (LoadJumpFunction)fn;
	                    State n = lfn.getN();
	                    Set<State> dfaStates = nfaStateToDfaStates.get(n);
	                    if (dfaStates == null) {
	                        //throw new RuntimeException("No dfa state for state " + n);
	                        continue;
	                    }
	                    else {
	                        for (State dfaState : dfaStates) {
	                            if(!newEdges.add(new TransformerEdge(new LoadJumpFunction(dfaState), dEdge.getDest()))) {
//	                                System.err.println("Adding failed because transformer edge already exists");	                                
	                            }
	                        }
//	                        System.err.println("Added " + dfaStates.size() + " load statements instead of 1");
	                    }
	                }
	                else {
	                    // identify jump function or store jump function goes through unchanged
	                    newEdges.add(dEdge);
	                }
	            }
	            if (!newEdges.isEmpty()) {
	                result.map.put(d, newEdges);
	            }
	        }
	    }

	    return result;
	}
	
	public String getLabel(Object o) {
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
        else if (o == arrElem) {
            return "[]";
        }
        else if (o == retVar) {
            return "$r";
        }
        else if (o == thisVar) {
            return "@this";
        }
        else if (o instanceof ParameterVariable) {
            ParameterVariable param = (ParameterVariable)o;
            return "@param" + param.getNum();
        }
        else {
            throw new RuntimeException("Unknown object: " + o);
        }
	}

    public int size() {
        int edgeCount = 0;
        for (Set<TransformerEdge> edges : map.values()) {
            edgeCount += edges.size();
        }
        return edgeCount;
    }
    
    public int numSymbols() {
        return map.keySet().size();
    }
    
    public int countAccesses() {
        Set<TransformerEdge> accesses = map.get(capitalLambda);
        return accesses == null ? 0 : accesses.size();
    }
    
    public int countLoads() {
        int loadCount = 0;
        for (Set<TransformerEdge> edges : map.values()) {
            for (TransformerEdge e : edges) {
                if (e.getJumpFunction() instanceof LoadJumpFunction) {
                    loadCount++;
                }
            }
        }
        return loadCount;
    }
    
    public int countLiveLoads(Set<State> reachables) {
        int liveLoadCount = 0;
        for (Set<TransformerEdge> edges : map.values()) {
            for (TransformerEdge e : edges) {
                JumpFunction fn = e.getJumpFunction();
                if (fn instanceof LoadJumpFunction) {
                    LoadJumpFunction lfn = (LoadJumpFunction)fn;
                    if (reachables.contains(lfn.getN())) {
                        liveLoadCount++;
                    }
                }
            }
        }
        return liveLoadCount;
    }
    
    private Set<TransformerEdge> newEdgeSet() {
        return new HashSet<TransformerEdge>();
    }
    
    private Set<TransformerEdge> newEdgeSet(Set<TransformerEdge> other) {
//        Set<TransformerEdge> clone = (ArraySet<TransformerEdge>)newEdgeSet();
//        for (TransformerEdge t : other) {
//            clone.addElement(t);
//        }
//        return clone;
        return new HashSet<TransformerEdge>(other);
    }
    
}
