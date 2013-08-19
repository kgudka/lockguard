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

import java.io.*;
import java.util.Date;

import lg.analysis.locks.*;
import lg.analysis.paths.LockSet;
import lg.analysis.paths.automata.Automaton;
import lg.util.*;
import soot.*;

public class LocksMain {

    public static void main(String[] args) throws Exception {
        
        PrintStream locksResults = new PrintStream("locks.csv");
                
        FileInputStream fis = null;
        ObjectInputStream in = null;
        
        try {
            fis = new FileInputStream("nfas.lg");
            in = new ObjectInputStream(fis);
        
            int methodCount = in.readInt();
        
            Date startTime = new Date();
            for (int i=1; i<=methodCount; i++) {
                Date currStartTime = new Date();
                String mStr = (String)in.readObject();
                Automaton nfa = (Automaton)in.readObject();

                Logger.println("Converting locks for method " + i + " of " + methodCount);
                Logger.println("   Method: " + mStr);

                AutomatonToLocks converter = new AutomatonToLocks(nfa, null, null, null);
                LockSet locks = (LockSet)converter.getLocks();

                int ri = 0, wi = 0, rt = 0, wt = 0;                
                for (Lock l : locks) {
                    if (l instanceof PathLock) {
                        if (l.isWrite()) {
                            wi++;
                        }
                        else {
                            ri++;
                        }
                    }
                    else {
                        if (l.isWrite()) {
                            wt++;
                        }
                        else {
                            rt++;
                        }                               
                    }
                }
                
                Date time = new Date(System.currentTimeMillis()-startTime.getTime());
                Date took = new Date(System.currentTimeMillis()-currStartTime.getTime());
                Logger.println("   Took: " + String.format("%2d:%2d:%2d", took.getHours()-1, took.getMinutes(), took.getSeconds()));
                Logger.println("   Time: " + String.format("%2d:%2d:%2d", time.getHours()-1, time.getMinutes(), time.getSeconds()));

                double tookSeconds = took.getTime()/1000.0;
                locksResults.println(mStr + "," + ri + "," + wi + "," + rt + "," + wt + "," + tookSeconds);
                
                System.out.println("Locks for " + mStr + ":");
                locks.print();
            }
            
            in.close();
            
            double timeSecs = (System.currentTimeMillis()-startTime.getTime())/1000.0;
            Logger.println("Analysis took " + timeSecs + "secs");
            locksResults.println(timeSecs);
            
            Info.outputMemoryStatistics(locksResults);
            
            locksResults.flush();
        }
        catch(Exception e) {
            throw new RuntimeException(e);
        }

    }
    
}
