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

import java.io.Serializable;

import lg.util.SymbolNumberer;
import soot.util.Numberable;


public class TransformerEdge implements Serializable {

    private static final long serialVersionUID = 1L;
    
	private JumpFunction fn;
	private Integer dst;
	private final int hashCode;
	
	public TransformerEdge(JumpFunction f, Object d) {
		this(f, SymbolNumberer.getNumber(d), f.hashCode() ^ SymbolNumberer.getNumber(d));
	}

    public TransformerEdge(JumpFunction f, Integer i) {
        this(f, i.intValue(), f.hashCode() ^ i.intValue());
    }	
	
	public TransformerEdge(JumpFunction f, int d, int hash) {
		fn = f;
		dst = d;
		hashCode = hash; 
	}
	
	public JumpFunction getJumpFunction() {
		return fn;
	}
	
	public Integer getDest() {
		return dst;
	}
	
	public int hashCode() {
		return hashCode;
	}
	
	@Override
	public boolean equals(Object o) {
		if (o == this) {
			return true;
		}
		else if (o == null) {
			return false;
		}
		else {
			if (o instanceof TransformerEdge) {
				TransformerEdge te = (TransformerEdge) o;
				return fn.equals(te.fn) && dst.equals(te.dst);
			}
			else {
				return false;
			}
		}
	}
	
	@Override
	public String toString() {
		return fn.toString() + "-->" + dst.toString();
	}
	
}
