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
import java.lang.management.*;

public class MemoryMonitor implements Runnable {

    volatile boolean stop = false;
    PrintStream out = null;
    
    public MemoryMonitor(String filename) {
        try {
            out = new PrintStream(filename);
        }
        catch (Exception e) {
            throw new RuntimeException(e);
        }
    }
    
    public void stop() {
        stop = true;
    }
    
    public void run() {
        MemoryMXBean m = ManagementFactory.getMemoryMXBean();
        while (!stop) {
            MemoryUsage usage = m.getHeapMemoryUsage();
            long bytes = usage.getUsed();
            float mbytes = (float)((bytes / 1024.0) / 1024.0);
            out.println(mbytes);
            try {
                Thread.sleep(1000);
            }
            catch(InterruptedException ie) {
                throw new RuntimeException(ie);
            }
            // we do gc if free memory is < 10% of allocated RAM
            // Sometimes, i've found that automatic gc won't run (Oracle Java 6b16)
            // causing the JVM to run out of memory, so have to force it.
//            double totalMemory = Runtime.getRuntime().totalMemory();
//            double freeMemory = Runtime.getRuntime().freeMemory();
//            if ((freeMemory/totalMemory) < 0.10) {
//                Logger.println(" *** PERFORMING GC, ratio: " + (freeMemory/totalMemory), ANSICode.FG_RED);
//                System.gc();
//            }
        }
        out.close();
    }

}
