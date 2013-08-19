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

import java.io.*;
import java.util.*;

import lg.cg.NonColdEdgesPred;
import lg.transformer.AtomicTransformer;
import soot.*;
import soot.jimple.toolkits.callgraph.*;


public class StronglyConnectedComponents {

	CallGraph cg;
	static NonColdEdgesPred edgesPred = new NonColdEdgesPred();
	List<Component> components;
	
	Stack<SootMethod> s;
	Map<SootMethod,Integer> indices;
	Map<SootMethod,Integer> lowlinks;
	int index;
		
	public StronglyConnectedComponents(SootMethod m) {
		cg = Scene.v().getCallGraph();
		
		s = new Stack<SootMethod>();
		indices = new HashMap<SootMethod, Integer>();
		lowlinks = new HashMap<SootMethod, Integer>();
		index = 0;
		components = new ArrayList<Component>();
		
		findComponents(m);
		
		s = null;
		indices = null;
		lowlinks = null;
	}

	private void findComponents(SootMethod m) {
		tarjan(m);
	}

	// See http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
	// or Robert Tarjan: Depth-first search and linear graph algorithms. 
	//    In: SIAM Journal on Computing. Vol. 1 (1972), No. 2, P. 146-160.
	private void tarjan(SootMethod m) {
		indices.put(m, index);
		lowlinks.put(m, index);
		index++;
		s.push(m);
		
		Iterator<Edge> edges = cg.edgesOutOf(m);  // iterate through m's succs
		while (edges.hasNext()) {
			Edge e = edges.next();
			if (edgesPred.want(e)) {
				SootMethod mSucc = e.getTgt().method();
				if (!indices.containsKey(mSucc)) {
					tarjan(mSucc);
					lowlinks.put(m, Math.min(lowlinks.get(m).intValue(), lowlinks.get(mSucc).intValue()));
				}
				else if (s.contains(mSucc)) {
					lowlinks.put(m, Math.min(lowlinks.get(m).intValue(), indices.get(mSucc).intValue()));
				}
			}
		}
		
		if (lowlinks.get(m).intValue() == indices.get(m).intValue()) {  // Is m the root of an SCC?
			Component scc = new Component();
			SootMethod m2;
			do {
				m2 = s.pop();
				scc.add(m2);
			} while (m != m2);
			components.add(scc);
		}
	}
	
	public List<Component> getComponents() {
		return components;
	}
	
//	public void outputDot(PathsAnalysis p) {
//		for (Component c : components) {
//			if (p.hasAlreadyBeenAnalysed(c)) {
//				outputDot(c);
//			}
//		}
//	}
	
	public void outputDot() {
	    for (Component c : components) {
	        outputDot(c);
	    }
	}
	
	public void outputDot(Component c) {
		try {
			PrintWriter p = new PrintWriter("c" + c.getId() + ".dot");
			p.println("strict digraph c" + c.getId() + " {");
			p.println("\tconcentrated = true;");
			
			CallGraph cg = Scene.v().getCallGraph();

			for (SootMethod m : c) {
//				if (m.toString().contains("writeChars")) {
//					p.println("\tm" + m.getNumber() + " [label=\"" + m.toString() + "\",color=lightgrey,style=filled];");
//				}
//				else {
					p.println("\tm" + m.getNumber() + " [label=\"" + m.toString() + "\",href=\"\\N.html\"];");
//				}
			}
			
			for (SootMethod m : c) {
				for (Iterator<Edge> edgesIt=cg.edgesOutOf(m); edgesIt.hasNext(); ) {
					Edge e = edgesIt.next();
					if (edgesPred.want(e)) {
						SootMethod tgt = e.tgt();
						if (c.contains(tgt)) {
							p.println("\tm" + m.getNumber() + " -> m" + tgt.getNumber() + ";");
						}
						else {
							for (Component c2 : components) {
								if (c2.contains(tgt)) {
									p.println("\tc" + c2.getId() + " [href=\"\\N.svg\",style=filled,color=yellow];");
									p.println("\tm" + m.getNumber() + " -> c" + c2.getId() + ";");
									//p.println("\tm" + tgt.getNumber() + " [href=\"\\N.html\",style=filled,color=yellow];");
									//p.println("\tm" + m.getNumber() + " -> m" + tgt.getNumber() + ";");
								}
							}
						}
					}
				}
			}
			
			p.println("}");
			p.flush();
			p.close();
		}
		catch (FileNotFoundException fnfe) {
			throw new RuntimeException(fnfe);
		}
	}

}
