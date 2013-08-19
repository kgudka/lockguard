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

package java.util.concurrent.locks.multi;

import java.util.concurrent.locks.*;

public class AtomicSynchroniser {

//    private static ThreadLocal<Integer> numAttempts = new ThreadLocal<Integer>() {
//       protected Integer initialValue() {
//           return new Integer(0);
//       }
//    };
//    
//    private static ThreadLocal<Integer> backoffInterval = new ThreadLocal<Integer>() {
//        protected Integer initialValue() {
//            return new Integer(10 + new Random().nextInt(10));
//        };
//    };
    
    public static final boolean DEBUG = false;

    private static final int MAX_POLL = 1000;
    private static final int WAIT_BETWEEN_POLLS = 50;
    
    public static volatile boolean multiThreadedMode = false; // all threads need to see updates to this value, therefore volatile
    public static long spawnedThreadCount = 0; // assume that threads are spawned only by the main thread
    
    public static Lock globalLock = new InstanceLock(null).writeLock();
    
//    private static AtomicLong retries = new AtomicLong(0);
    
    public static final boolean lockInstanceRead(Object o, boolean multi) {
        ReadWriteLock l = o.ilock(multi);
        Lock lock = l.readLock();
//        System.out.println("Read lock instance: ");
        return lock(lock);
    }
    
    public static final boolean lockInstanceWrite(Object o, boolean multi) {
        ReadWriteLock l = o.ilock(multi);
        Lock lock = l.writeLock();
//        System.out.println("Write lock instance: ");
        return lock(lock);
    }

    public static final boolean lockTypeRead(Class<?> c) {
        TypeLock l = c.tlock();
        Lock lock = l.readLock();
//        System.out.println("Read lock type: ");
        return lock(lock);
    }
    
    public static final boolean lockTypeWrite(Class<?> c) {
        TypeLock l = c.tlock();
        Lock lock = l.writeLock();
//        System.out.println("Write lock type: ");
        return lock(lock);
    }

    private static final boolean lock(Lock lock) {
//        System.out.println(lock);
//        boolean locked = lock.tryLock();
//        if (locked) {
//            Thread.currentThread().acquireLock(lock, false);
//            if (DEBUG) System.out.println(Thread.currentThread().getId() + " acquired lock " + lock);
//        }
//        else {
//            if (DEBUG) System.out.println(Thread.currentThread().getId() + " blocking on lock " + lock);
//            blockNoDeadlock(lock);
//        }
//        return locked;
//        lock.lock();
//        if (DEBUG) System.out.println("lock: " + lock);
        // we use an adaptive deadlock-avoidance mechanism, try to acquire the lock N times after which 
        // release all locks reacquire
        // 
        if (lock.tryLock()) {
            Thread.currentThread().acquireLock(lock, false);
            return true;
        }
        else {
            int counter=0;
//            int waitBetweenPolls = 0;//20 + Thread.currentThread().getRnd().nextInt(MAX_WAIT_BETWEEN_POLL-20);
            while (counter < MAX_POLL && !lock.tryLock()) { 
                counter++;
                for (int i=0; i<WAIT_BETWEEN_POLLS; i++) { }
            }
    //        System.out.println(counter + " tries");
    //        System.out.println("thread: " + Thread.currentThread().getId());
            if (counter == MAX_POLL) {
    //            System.out.println("max poll");
                if (DEBUG) System.out.println(Thread.currentThread().getId() + " blocking on lock " + lock);
                blockNoDeadlock(lock);
                return false;
            }
            else {
    //            while (!lock.tryLock()) { }
                if (DEBUG) System.out.println(Thread.currentThread().getId() + " acquired lock " + lock);
                Thread.currentThread().acquireLock(lock, false);
    //            System.out.println(Thread.currentThread().getId() + " acquired lock " + lock + " with " + counter + " retries");
                return true;            
            }
            
        }
//        return lock.tryLock();
    }
    
    public static final void blockNoDeadlock(Lock l) {
        // unlock all currently acquired locks to avoid deadlock
        unlockAll();
        
        // Ideally we would like to park here but not sure how to integrate that
        // with AQS, instead we poll every 10ms.
//        Random r = Thread.currentThread().getRnd();
//        long sleepInterval = r.nextInt(10);
        
        while (!l.tryLock()) {
//            try {
//                if (DEBUG) System.out.println(Thread.currentThread().getId() + " could not acquire lock " + l + ", sleeping for " + (sleepInterval) + "ms");
//                Thread.sleep(sleepInterval);
//                sleepInterval*=2;
//            }
//            catch (InterruptedException ie) {
//                ie.printStackTrace();
//            }
        }
//        l.lock();
        
//        retries.incrementAndGet();
        
        // l has been acquired: release as we will begin acquiring locks again
        // from the start (note: owner has already been unlocked above) 
        l.unlock();
//        if (DEBUG) System.out.println(Thread.currentThread().getId() + " released lock " + l + ": " + l.getClass());
//
        // backoff before trying to acquire locks again
        Thread currentThread = Thread.currentThread();
        int attempts = currentThread.incNumAcquireAttempts();
        int interval = currentThread.getBackOffInterval();
//        int multiplier = currentThread.getRnd().nextInt(5);
        try {
            int sleep = attempts*interval;
            if (sleep > 0) {
//                System.out.println(currentThread.getId() + " backing off for " + (sleep) + "ms");
                Thread.sleep(sleep);
            }
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    public static void unlockAll() {
        Thread.currentThread().unlockAll(false);
//        printNumRetries();
        if (DEBUG) System.out.println(Thread.currentThread().getId() + " released all locks");
//        try {
//            Thread.sleep(500);
//        } catch (InterruptedException e) {
//            e.printStackTrace();
//        }
    }
    
    public static void enterAtomic() {
        Thread currentThread = Thread.currentThread();
        currentThread.incAtomicNestingCount();
        currentThread.resetNumAcquireAttempts();
//        if (currentThread.getAtomicNestingCount() == 1) {
//            System.out.println("Thread " + currentThread.getId() + " called enterAtomic()");
//            threadsInAtomics.incrementAndGet();
//        }
    }
    
    public static void exitAtomic() {
        Thread currentThread = Thread.currentThread();
        currentThread.decAtomicNestingCount();
//        if (currentThread.getAtomicNestingCount() == 0) {
//            System.out.println("Thread " + currentThread.getId() + " called exitAtomic()");
//            threadsInAtomics.decrementAndGet();
//        }
    }
    
    public static void enterAtomicGlobal() {
        globalLock.lock();
    }
    
    public static void exitAtomicGlobal() {
        globalLock.unlock();
    }
    
    public static void enterAtomicManual(Object o) {
        ReadWriteLock rwl = o.ilock(false);
        Lock lock = rwl.writeLock();
        lock.lock();
        Thread.currentThread().acquireLock(lock, false);
    }

    public static void exitAtomicManual() {
        // we unlock the last lock
        Thread.currentThread().unlockLast();
    }
    
    // called immediately after enterAtomic()
    public static boolean isOuterAtomic() {
        // 1st condition is a hack to avoid locking if in single-threaded mode
        return !isSingleThreaded() && Thread.currentThread().getAtomicNestingCount() == 1; 
    }
    
    // this may be called by multiple threads
    public static synchronized void startThread() {
        spawnedThreadCount++;
        if (spawnedThreadCount == 1) {
//            System.out.println("** multi-threaded mode");
            multiThreadedMode = true;
        }
    }
    
    public static synchronized void joinThread() {
        spawnedThreadCount--;
        if (spawnedThreadCount == 0) {
//            System.out.println("** single-threaded mode");
            multiThreadedMode = false;
        }
    }
    
    public static boolean isSingleThreaded() {
        return !multiThreadedMode;
    }
    
//    public static void printNumRetries() {
////        System.out.println("NUMBER OF RETRIES: " + retries.get());
//    }

    public static void main(String[] args) {
         
        // locking phase
        AtomicSynchroniser.enterAtomic();
        if (AtomicSynchroniser.isOuterAtomic()) {
            while (true) {
                if (AtomicSynchroniser.lockInstanceRead(args, true)) {
                    if (AtomicSynchroniser.lockInstanceRead(args, true)) {
                        break; // i.e. go to atomic body
                    }
                }
            }
        }

        try {
            // atomic body
        }
        finally {
            if (AtomicSynchroniser.isOuterAtomic()) {
                AtomicSynchroniser.unlockAll();
            }
            AtomicSynchroniser.exitAtomic();
        }
    }
    
}
