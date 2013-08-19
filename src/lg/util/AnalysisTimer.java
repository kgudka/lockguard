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

import java.util.concurrent.atomic.AtomicLong;

import soot.SootMethod;

public class AnalysisTimer {

    static AtomicLong libIntra = new AtomicLong(0);
    static AtomicLong clientIntra = new AtomicLong(0);
    static AtomicLong libInter = new AtomicLong(0);
    static AtomicLong clientInter = new AtomicLong(0);
    static AtomicLong libReduction = new AtomicLong(0);
    static AtomicLong clientReduction = new AtomicLong(0);
    static AtomicLong libAtomic = new AtomicLong(0);
    static AtomicLong clientAtomic = new AtomicLong(0);
    static AtomicLong pathsAnalysis = new AtomicLong(0);
    
    static AtomicLong libLocks = new AtomicLong(0);
    static AtomicLong clientLocks = new AtomicLong(0);
    static AtomicLong locks = new AtomicLong(0);
    
    static AtomicLong threadLocal = new AtomicLong(0);
    static AtomicLong instanceLocal = new AtomicLong(0);
    static AtomicLong classLocal = new AtomicLong(0);
    static AtomicLong dominators = new AtomicLong(0);
    static AtomicLong readLocks = new AtomicLong(0);
    static AtomicLong implicitLocking = new AtomicLong(0);
    static AtomicLong methodLocal = new AtomicLong(0);
    
    public static void addForIntra(long ms, SootMethod m) {
        if (isLibrary(m)) {
            libIntra.addAndGet(ms);
        }
        else {
            clientIntra.addAndGet(ms);
        }
    }

    public static void addForInter(long ms, SootMethod m) {
        if (isLibrary(m)) {
            libInter.addAndGet(ms);
        }
        else {
            clientInter.addAndGet(ms);
        }
    }
    
    public static void addForReduction(long ms, SootMethod m) {
        if (isLibrary(m)) {
            libReduction.addAndGet(ms);
        }
        else {
            clientReduction.addAndGet(ms);
        }
    }
    
    public static void addForAtomic(long ms, SootMethod m) {
        if (isLibrary(m)) {
            libAtomic.addAndGet(ms);
        }
        else {
            clientAtomic.addAndGet(ms);
        }
    }
    
    public static void addForPathsAnalysis(long ms) {
        pathsAnalysis.addAndGet(ms);
    }
    
    public static void addForLocks(long ms, SootMethod m) {
        if (isLibrary(m)) {
            libLocks.addAndGet(ms);
        }
        else {
            clientLocks.addAndGet(ms);
        }
    }
    
    public static void addForLocks(long ms) {
        locks.addAndGet(ms);
    }
    
    public static void addForThreadLocalAnalysis(long ms) {
        threadLocal.addAndGet(ms);
    }
    
    public static void addForInstanceLocalAnalysis(long ms) {
        instanceLocal.addAndGet(ms);
    }
    
    public static void addForClassLocalAnalysis(long ms) {
        classLocal.addAndGet(ms);
    }

    public static void addForDominatorsAnalysis(long ms) {
        dominators.addAndGet(ms);
    }
    
    public static void addForReadLocksAnalysis(long ms) {
        readLocks.addAndGet(ms);
    }
    
    public static void addForImplicitLockingAnalysis(long ms) {
        implicitLocking.addAndGet(ms);
    }
    
    public static void addForMethodLocalAnalysis(long ms) {
        methodLocal.addAndGet(ms);
    }
    
    private static boolean isLibrary(SootMethod m) {
        return m.getDeclaringClass().isLibraryClass();
//        String clazzPackage = m.getDeclaringClass().getJavaPackageName();
//        return !(clazzPackage.startsWith("org.hsqldb") || clazzPackage.startsWith("dacapo"));
//        return !clazzPackage.startssWith("test");
    }

    public static long getLibInter() {
        return libInter.get();
    }

    public static long getLibIntra() {
        return libIntra.get();
    }

    public static long getClientIntra() {
        return clientIntra.get();
    }

    public static long getClientInter() {
        return clientInter.get();
    }

    public static long getLibReduction() {
        return libReduction.get();
    }

    public static long getClientReduction() {
        return clientReduction.get();
    }
    
    public static long getLibAtomic() {
        return libAtomic.get();
    }

    public static long getClientAtomic() {
        return clientAtomic.get();
    }    

    public static long getLibLocks() {
        return libLocks.get();
    }

    public static long getClientLocks() {
        return clientLocks.get();
    }
    
    public static long getTotalPathsAnalysis() {
//        return libIntra.get()+clientIntra.get()+libInter.get()+clientInter.get()+libReduction.get()+clientReduction.get()+libAtomic.get()+clientAtomic.get();
        return pathsAnalysis.get();
    }
    
    public static long getTotalLocksAnalysis() {
//        return libLocks.get()+clientLocks.get();
        return locks.get();
    }
    
    public static long getTotalThreadLocalAnalysis() {
        return threadLocal.get();
    }
    
    public static long getTotalInstanceLocalAnalysis() {
        return instanceLocal.get();
    }

    public static long getTotalClassLocalAnalysis() {
        return classLocal.get();
    }
    
    public static long getTotalDominatorsAnalysis() {
        return dominators.get();
    }

    public static long getTotalReadLocksAnalysis() {
        return readLocks.get();
    }
    
    public static long getTotalImplicitLockingAnalysis() {
        return implicitLocking.get();
    }

    public static long getTotalMethodLocalAnalysis() {
        return methodLocal.get();
    }

}
