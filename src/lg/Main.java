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

package lg;

import java.util.Arrays;

import lg.transformer.AtomicTransformer;
import soot.*;

public class Main {

	/**
	 * @param args
	 */
	public static void main(String[] args) {

        Pack wjtp = PackManager.v().getPack("wjtp");
        
        Transform lg = new Transform("wjtp.lg", new AtomicTransformer());
        lg.setDeclaredOptions("enabled debug reduce-cfg show-summary output-dot exceptions lvalues aggregate dfa locks intermediate-results library notails method savenfas nfalocks cold instrument timecompose deltas hashset compaction sweep threads reduce-cfg-delta store-entry compact stats compact-every locks-print compact-summaries avoid-deadlock load-summaries save-summaries order-worklists meminfo method-list instrument-debug ignore-types juc implicit-locking read-locks client-lib-stats-only ignore-wait-notify thread-local thread-local-debug instance-local lock-dominators class-local method-local global-lock manual-locks ignore-unreachable-atomics slow-transformers");
        lg.setDefaultOptions("enabled:true debug:false reduce-cfg:true show-summary:false output-dot:false exceptions:true lvalues:true aggregate:false dfa:false locks:true intermediate-results:true library:false notails:false method:1 savenfas:false nfalocks:false cold:false instrument:true timecompose:false deltas:true hashset:false compaction:99999 sweep:true threads:1 reduce-cfg-delta:true store-entry:true compact:false stats:false compact-every:1 locks-print:true compact-summaries:false avoid-deadlock:true load-summaries:null save-summaries:null order-worklists:true meminfo:mem.txt method-list:false instrument-debug:false ignore-types:null juc:true implicit-locking:false read-locks:false client-lib-stats-only:false ignore-wait-notify:false thread-local:false thread-local-debug:false instance-local:false lock-dominators:false class-local:false method-local:false global-lock:false manual-locks:false ignore-unreachable-atomics:false slow-transformers:false");
        wjtp.add(lg);
                
        System.out.println(Arrays.toString(args));

        soot.Main.main(args);

	}

}
