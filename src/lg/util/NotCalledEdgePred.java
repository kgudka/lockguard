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

import soot.jimple.toolkits.callgraph.*;

public class NotCalledEdgePred implements EdgePredicate {

	public boolean want(Edge e) {
		if(e.src().getDeclaringClass().getName().contains("FilePermission") || e.tgt().getDeclaringClass().getName().contains("FilePermission") 
				|| e.src().getDeclaringClass().getName().contains("SocketPermission") || e.tgt().getDeclaringClass().getName().contains("SocketPermission")
				|| e.src().getDeclaringClass().getName().contains("Inet6Address") || e.tgt().getDeclaringClass().getName().contains("Inet6Address")
				|| e.src().getDeclaringClass().getName().contains("Inet4Address") || e.tgt().getDeclaringClass().getName().contains("Inet4Address")
				|| e.src().getDeclaringClass().getName().contains("CodeSource") || e.tgt().getDeclaringClass().getName().contains("CodeSource")
				|| !e.isExplicit()) {
			System.out.println("Found edge that we don't want from: " + e.src() + " to " + e.tgt());
			return false;
		}
		else {
			return true;
		}
	}

}
