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

import java.util.*;

import lg.analysis.paths.transformer.ParameterVariable;
import lg.util.SymbolNumberer;
import soot.*;
import soot.jimple.*;

public class CallTransformer extends SlowTransformer {

    private static final long serialVersionUID = 1L;
    
	public CallTransformer(InvokeExpr invokeExpr) {
		if (invokeExpr instanceof InstanceInvokeExpr) {
			// @this --> receiver
			InstanceInvokeExpr instInvokeExpr = (InstanceInvokeExpr)invokeExpr;
			Local receiver = (Local)instInvokeExpr.getBase();
			Set<TransformerEdge> edges = new HashSet<TransformerEdge>(1,1);
			edges.add(new TransformerEdge(idJumpFn, receiver));
			map.put(SymbolNumberer.getNumber(thisVar), edges);
		}
		// do all other params: @paramn --> local or e
		List<?> args = invokeExpr.getArgs();
		for (int i=0; i<args.size(); i++) {
			Value arg = invokeExpr.getArg(i);
			ParameterVariable param = ParameterVariable.v(i);
			Set<TransformerEdge> edges = new HashSet<TransformerEdge>(1,1);
			if (arg instanceof Local) {
				edges.add(new TransformerEdge(idJumpFn, (Local)arg));
			}
			else {
				edges.add(killEdge);
			}
			map.put(SymbolNumberer.getNumber(param), edges);
		}
	}
	
}
