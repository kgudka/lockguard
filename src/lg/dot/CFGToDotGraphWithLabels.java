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

package lg.dot;

import java.util.*;

import lg.analysis.paths.transformer.state.StateFactory;
import soot.*;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.*;
import soot.util.cfgcmd.CFGToDotGraph;
import soot.util.dot.*;

public class CFGToDotGraphWithLabels extends CFGToDotGraph {

	protected String formatNodeLabel(Object node, String nodeLabel) {
		if (node instanceof Stmt) {
			Stmt n = (Stmt)node;
			return nodeLabel + " (" + StateFactory.v(n) + ")";
		}
		else {
			return nodeLabel;
		}
	}
	
	protected void addHref(Object node, DotGraphNode dotNode) {
//		if (node instanceof Stmt) {
//			Stmt s = (Stmt)node;
//			if (s.containsInvokeExpr()) {
//				dotNode.setAttribute("href","m"+s.getInvokeExpr().getMethod().getNumber()+".html");
//				dotNode.setAttribute("target", "_parent");
//			}
//		}
	}

	protected Set<DotGraphNode> addCalleeNodesHelper(DotGraph canvas, Object node, DotGraphNode dotNode) {
		Set<DotGraphNode> calleeNodes = null;
		if (node instanceof Stmt) {
			Stmt s = (Stmt)node;
			if (s.containsInvokeExpr()) {
				calleeNodes = new HashSet<DotGraphNode>();
				CallGraph cg = Scene.v().getCallGraph();
				for (Iterator<Edge> edgesIt=cg.edgesOutOf(s); edgesIt.hasNext(); ) {
					Edge e = edgesIt.next();
					SootMethod tgt = e.tgt();
					if (tgt.isConcrete()) {
						DotGraphNode n = canvas.drawNode("m" + tgt.getNumber());
						n.setLabel(tgt.getDeclaringClass().getName());
						n.setAttribute("href", "\"\\N.html\"");
						n.setAttribute("target", "\"right\"");
						n.setAttribute("color", "yellow");
						n.setStyle("filled");
						calleeNodes.add(n);
					}
				}
			}
		}
		return calleeNodes;
	}
	
}
