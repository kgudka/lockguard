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

package lg.analysis.paths.transformer.fast;

import lg.analysis.paths.transformer.state.StateFactory;
import lg.util.SymbolNumberer;
import soot.*;
import soot.jimple.Stmt;
import soot.util.Numberable;

public class FieldLoadTransformer extends Transformer {

    private static final long serialVersionUID = 1L;
    
	// A --> y or C
	// x --> .f
	public FieldLoadTransformer(Local x, Object y, SootField f, Stmt n) {
	    long e1 = TransformerEdgeFactory.newAccessEdge(startState, StateFactory.v(n), false, y);
		long e2 = TransformerEdgeFactory.newLoadEdge(StateFactory.v(n), f);
		addEdge(capitalLambda, e1);
		addEdge(SymbolNumberer.getNumber(x), e2);
	}

}
