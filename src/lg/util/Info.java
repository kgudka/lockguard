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

import java.io.PrintStream;

import soot.*;

public class Info {

	public static int countFields() {
		int count=0;
		for (SootClass c : Scene.v().getClasses()) {
			count += c.getFields().size();
		}
		return count;
	}
	
	public static int countClasses() {
		return Scene.v().getClasses().size();
	}
	
	public static int countClasses2() {
		return Scene.v().getClassNumberer().size();
	}

	public static double avgVarCountPerMethod() {
		int varCount=0;
		int methodCount=0;
		for (SootClass c : Scene.v().getClasses()) {
			for (SootMethod m : c.getMethods()) {
				if (m.isConcrete()) {
					methodCount++;
					varCount += (m.getParameterCount() + m.retrieveActiveBody().getLocals().size());
				}
			}
		}
		return (double)varCount/(double)methodCount;
	}
	
	public static Pair<Integer,SootMethod> maxVarCountPerMethod() {
		int maxVarCount=0;
		SootMethod maxMethod = null;
		for (SootClass c : Scene.v().getClasses()) {
			for (SootMethod m : c.getMethods()) {
				if (m.isConcrete()) {
					int varCount = m.getParameterCount() + m.retrieveActiveBody().getLocals().size();
					if (varCount > maxVarCount) {
						maxVarCount = varCount;
						maxMethod = m;
					}
				}
			}
		}
		return new Pair(maxVarCount, maxMethod);
	}
	
	public static int countMethods() {
		int count=0;
		for (SootClass c : Scene.v().getClasses()) {
			for (SootMethod m : c.getMethods()) {
				if (m.isConcrete()) {
					count++;
				}
			}
		}
		return count;
	}
	
    public static int countNonPrivateMethods() {
        int count=0;
        for (SootClass c : Scene.v().getClasses()) {
            for (SootMethod m : c.getMethods()) {
                if (m.isConcrete() && !m.isPrivate()) {
                    count++;
                }
            }
        }
        return count;
    }	
    
    public static void outputMemoryStatistics(PrintStream results) {
        Logger.println("Memory statistics:");
        Runtime r = Runtime.getRuntime();
        long totalMem = r.totalMemory();
        long freeMem = r.freeMemory();
        long usedMem = totalMem-freeMem;
        long maxMem = r.maxMemory();
        String totalMemStr = String.format("%1$.2fMB", bytesToMegabytes(totalMem));
        String freeMemStr = String.format("%1$.2fMB", bytesToMegabytes(freeMem));
        String usedMemStr = String.format("%1$.2fMB", bytesToMegabytes(usedMem));
        String maxMemStr = String.format("%1$.2fMB", bytesToMegabytes(maxMem));
        Logger.println("Total memory: " + totalMem + " (" + totalMemStr + ")");
        Logger.println("Free memory: " + freeMem + " (" + freeMemStr + ")");
        Logger.println("Used memory: " + usedMem + " (" + usedMemStr + ")");
        Logger.println("Max memory: " + maxMem + " (" + maxMemStr + ")");
        if (results != null) {
            results.println(totalMemStr + "," + freeMemStr + "," + usedMemStr + "," + maxMemStr);
        }
    }
	
    private static double bytesToMegabytes(long bytes) {
        return (bytes/1024.0)/1024.0;
    }
    
}
