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

import lg.analysis.paths.transformer.state.StateFactory;
import lg.util.SymbolNumberer;
import soot.*;
import soot.jimple.Stmt;

public class StaticFieldStoreTransformer extends SlowTransformer {

    private static final long serialVersionUID = 1L;
    
	// A --> C
	// .f --> y
	public StaticFieldStoreTransformer(SootClass c, SootField f, Local y, Stmt n) {
		Set<TransformerEdge> accesses = new HashSet<TransformerEdge>(1, 1);
		accesses.add(new TransformerEdge(new EdgeJumpFunction(startState, StateFactory.v(n), true), c));
		map.put(SymbolNumberer.getNumber(capitalLambda), accesses);
		// no aliases, so no need for .f --> .f
		Set<TransformerEdge> transformations = new HashSet<TransformerEdge>(1, 1);
		transformations.add(new TransformerEdge(storeJumpFn, y));
		map.put(SymbolNumberer.getNumber(f), transformations);
	}

}
