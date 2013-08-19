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

package lg.analysis.paths;

import java.io.*;
import java.util.*;

import lg.cg.NonColdEdgesPred;
import lg.transformer.AtomicTransformer;
import lg.util.*;

import org.omg.PortableInterceptor.SUCCESSFUL;

import soot.*;
import soot.jimple.toolkits.callgraph.*;

public class StronglyConnectedComponentsDAG {

	Map<Component,Set<Component>> componentToPreds;
	Map<Component,Set<Component>> componentToSuccs;
	Set<Component> components;
	Set<Component> roots;
	
	NonColdEdgesPred edgesPred;
	

	public StronglyConnectedComponentsDAG(Set<Component> cs) {
		componentToPreds = new HashMap<Component, Set<Component>>();
		componentToSuccs = new HashMap<Component, Set<Component>>();
		roots = new HashSet<Component>();
		components = cs;
		edgesPred = new NonColdEdgesPred();
		// initialise maps
		for (Component c : cs) {
			componentToPreds.put(c, new HashSet<Component>());
			componentToSuccs.put(c, new HashSet<Component>());
		}
		computeDAG();
	}
	
	private void computeDAG() {
		
		// keep track of which component each method is in for fast lookup
		Map<SootMethod,Component> methodToComponent = new HashMap<SootMethod, Component>();
		for (Component c : components) {
			for (SootMethod m : c) {
				methodToComponent.put(m, c);
			}
		}
		
		// compute actual dag
		CallGraph cg = Scene.v().getCallGraph();
		for (Component c : components) {
			Set<Component> succs = getSuccsOf(c);
			for (SootMethod m : c) {
				for (Iterator<Edge> edgesIt = cg.edgesOutOf(m); edgesIt.hasNext(); ) {
					Edge e = edgesIt.next();
					if (edgesPred.want(e)) {
						SootMethod tgt = e.tgt();
						if (!AtomicTransformer.METHODS_TO_IGNORE.contains(tgt.getNumber()) && tgt.isConcrete()) {
							Component c2 = methodToComponent.get(tgt);
							if (c2 != c) {
								succs.add(c2);
								Set<Component> preds = getPredsOf(c2);
								preds.add(c);
							}
						}
					}
				}
			}
		}
		
		// calculate roots
		for (Component c : components) {
			if (getPredsOf(c).isEmpty()) {
				roots.add(c);
			}
		}

	}


	public Set<Component> getRoots() {
		return roots;
	}

	public Set<Component> getPredsOf(Component s) {
		return componentToPreds.get(s);
	}

	public Set<Component> getSuccsOf(Component s) {
		return componentToSuccs.get(s);
	}
	
//	public void outputDot(PathsAnalysis pa) {
//		
//		try {
//			PrintWriter p = new PrintWriter("scc.dot");
//			p.println("strict digraph scc {");
//			p.println("\tconcentrated=true;");
//			p.println("\trankdir=LR;");
//			p.println("\tranksep=\"2in\";");
//			
//			for (Component c : components) {
//				int id = c.getId();
//				String color = pa != null && pa.hasAlreadyBeenAnalysed(c) ? "green" : "red";
////				if (c.size() == 1) {
////					p.println("\tc" + id + " [label=\"" + c.get(0).toString() + "\"];");	
////				}
////				else {
////					p.println("\tc" + id + " [label=\"c" + id + ": " + c.size() + "\",URL=\"\\N.svg\"];");
////				}
//				Set<Component> succs = getSuccsOf(c);
//				if (getPredsOf(c).isEmpty()){
//					p.println("\tc" + id + " [label=\"c" + id + ": " + c.size() + "\",URL=\"\\N.svg\",rank=min,style=filled,color=" + color + "];");
//				}
//				else if (succs.isEmpty()) {
//					p.println("\tc" + id + " [label=\"c" + id + ": " + c.size() + "\",URL=\"\\N.svg\",rank=max,style=filled,color=" + color + "];");
//				}
//				else {
//					p.println("\tc" + id + " [label=\"c" + id + ": " + c.size() + "\",URL=\"\\N.svg\",style=filled,color=" + color + "];");
//				}
//				
//				if (!succs.isEmpty()) {
//					p.print("\tc" + id + " -> {"); 
//					for (Component c2 : succs) {
//						p.print(" c" + c2.getId());
//					}
//					p.println("}");
//				}
//			}
//			
//			p.println("}");
//			p.flush();
//			p.close();
//		}
//		catch (FileNotFoundException fnfe) {
//			throw new RuntimeException(fnfe);
//		}
//		
//		//scc.outputDot();
//	}

	// output dot graph but where nodes are ranked based on the maximum length 
	// of the path from root nodes to each component 
//	public void outputDot2(PathsAnalysis pa) {
//
//		Map<Component,Integer> componentToRank = new HashMap<Component, Integer>();
//		
//		// bfs
//		Set<Component> currentLevel = new HashSet<Component>();
//		Set<Component> nextLevel = new HashSet<Component>();
//		currentLevel.addAll(roots);
//
//		int currentRank = 0;
//		while (!currentLevel.isEmpty()) {
//			for (Component c : currentLevel) {
//				componentToRank.put(c, currentRank);
//				nextLevel.addAll(getSuccsOf(c));
//			}
//			currentLevel = new HashSet<Component>(nextLevel);
//			nextLevel.clear();
//			currentRank++;
//		}
//		
//		// build reverse mapping from rank to components
//		Map<Integer,Set<Component>> rankToComponents = new HashMap<Integer, Set<Component>>();
//		for (Component c : componentToRank.keySet()) {
//			Integer cRank = componentToRank.get(c);
//			Set<Component> cRankComponents = rankToComponents.get(cRank);
//			if (cRankComponents == null) {
//				cRankComponents = new HashSet<Component>();
//				rankToComponents.put(cRank, cRankComponents);
//			}
//			cRankComponents.add(c);
//		}
//
//		int minRank = 0;
//		int maxRank = currentRank-1;
//		
//		try {
//			PrintWriter p = new PrintWriter("scc.dot");
//			p.println("strict digraph scc {");
//			p.println("\trankdir=LR;");
//			p.println("\tranksep=\"2in\";");
//			
//			for (Component c : components) {
//				int cId = c.getId();
//				for (Component c2 : getSuccsOf(c)) {
//					p.println("\tc" + cId + " -> c" + c2.getId());
//				}
//			}
//
//			for (int rank : rankToComponents.keySet()) {
//				p.println("\t{");
//				p.println("\t\trank=same;");
//				p.println("\t\tr" + rank + "[rank=" + rank + "]");
//				for (Component c : rankToComponents.get(rank)) {
//					int cId = c.getId();
//					String color = pa != null && pa.hasAlreadyBeenAnalysed(c) ? "green" : "red";
//					p.println("\t\tc" + cId + " [label=\"c" + cId + " (" + c.size() + "): " + c + "\",URL=\"\\N.svg\",style=filled,color=" + color + ",rank=" + rank + "];");
//				}
//				p.println("\t}");
//			}
//			
//			for (int i=minRank; i<=maxRank ; i++) {
//				if (i==minRank) {
//					p.print("\tr" + i);
//				}
//				else {
//					p.print(" -> r" + i);
//				}
//			}
//			p.println(";");			
//			p.println("}");
//			p.flush();
//			p.close();
//		}
//		catch (FileNotFoundException fnfe) {
//			throw new RuntimeException(fnfe);
//		}
//		
//		//scc.outputDot();
//	}

	
}
