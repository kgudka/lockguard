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

package lg.transformer;

import java.util.Map;

import lg.util.*;
import soot.*;
import soot.jimple.spark.pag.*;
import soot.jimple.spark.sets.*;
import soot.util.Chain;

public class PointsToTransformer extends SceneTransformer {

	@Override
	protected void internalTransform(String phaseName, Map options) {
	    SootMethod main = Scene.v().getMainMethod();
	    PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
	    Chain<Local> locals = main.retrieveActiveBody().getLocals();
	    
	    PointsToSetInternal o3pts = null, o4pts = null;
	    for (Local l : locals) {
	        PointsToSetInternal pts = (PointsToSetInternal)pta.reachingObjects(l);
	        Logger.println("l: " + l + ", pts: " + pts);
	        if (l.getName().equals("o3")) {
	            o3pts = pts;
	        }
	        else if (l.getName().equals("o4")) {
	            o4pts = pts;
	        }
	    }
	    
	    if (o3pts != null && o4pts != null) {
    	    Logger.println("o3pts: " + o3pts.getClass());
    	    Logger.println("o4pts: " + o4pts.getClass());
    	    
    	    Logger.println("o3pts==o4pts: " + (o3pts==o4pts));
    	    Logger.println("o3pts.equals(o4pts): " + (o3pts.equals(o4pts)));
    
    	    final PointsToSetInternal o4ptsf = o4pts;
    	    
    	    o3pts.forall(new P2SetVisitor() {
                @Override
                public void visit(final Node n) {
                    Logger.println("n: " + n);
                    o4ptsf.forall(new P2SetVisitor() {
                        @Override
                        public void visit(Node n2) {
                            Logger.println("  n2: " + n2, ANSICode.FG_BLUE);
                            Logger.println("  n==n2: " + (n==n2), ANSICode.FG_BLUE);
                            Logger.println("  n.equals(n2): " + (n.equals(n2)), ANSICode.FG_BLUE);
                        }
                    });
                }
            });
	    }
	    
	    
//	    for (Unit u : cfg) {
//	        Stmt s = (Stmt)u;
//	        if (s.containsFieldRef()) {
//	            FieldRef fr = (FieldRef)s.getFieldRef();
//	            if (fr instanceof InstanceFieldRef) {
//	                InstanceFieldRef ifr = (InstanceFieldRef)fr;
//	                Local x = (Local)ifr.getBase();
//	                SootField f = ifr.getField();
//	                PointsToSet xobjs = pta.reachingObjects(x);
//	                System.out.println("---");
//	                System.out.println("* Points to set for receiver in " + s + ":");
//	                System.out.println(xobjs.toString());
//	                System.out.println("* Possible run-time types:");
//	                System.out.println(xobjs.possibleTypes());
//	                System.out.println("---");
//	            }
//	            else {
//	                StaticFieldRef sfr = (StaticFieldRef)fr;
//	                SootField f = sfr.getField();
//	            }
//	        }
//	    }
	}

}
