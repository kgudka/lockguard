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

import lg.analysis.paths.transformer.state.State;

// lambda l . [src,dst]
public class EdgeJumpFunction extends JumpFunction {
	
	/**
     * 
     */
    private static final long serialVersionUID = 1L;
    protected State src;
	protected State dst;
	protected boolean write;
	protected final int hashCode;
	
	public EdgeJumpFunction(State s, State d, boolean w) {
		src = s;
		dst = d;
		write = w;
		hashCode = src == null ? dst.hashCode() : (src.hashCode() ^ dst.hashCode());
	}
	
	public State getSrc() {
		return src;
	}
	
	public State getDst() {
		return dst;
	}
	
	public boolean isWrite() {
	    return write;
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
			if (o instanceof EdgeJumpFunction) {
				EdgeJumpFunction e = (EdgeJumpFunction)o;
				return src == e.src && dst == e.dst && write == e.write;
			}
			else {
				return false;
			}
		}
	}
	
	public String toString() {
		return "\u03bbl.[" + src.getNumber() + "," + dst.getNumber() + "," + write + "]";
	}
	
}
