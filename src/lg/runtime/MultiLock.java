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

package lg.runtime;

import static lg.runtime.LockMode.*;
import gnu.classpath.Pair;

import java.util.*;
import java.util.Map.Entry;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.LockSupport;

import soot.jimple.toolkits.thread.synchronization.LockableReferenceAnalysis;

import lg.util.*;

interface Lock {
    boolean lock();
    void unlock();
    long getId();
//    void block();
}

public abstract class MultiLock {
    
    class ReadLock implements Lock {

        @Override
        public boolean lock() {
            return lockRead();
        }

        @Override
        public void unlock() {
            unlockRead();
        }

        @Override
        public long getId() {
            return getMultiLockId();
        }
        
//        public void block() {
//            blockCurrentThread();
//        }
        
    }
    
    class WriteLock implements Lock {

        @Override
        public boolean lock() {
            return lockWrite();
        }

        @Override
        public void unlock() {
            unlockWrite();
            
        }

        @Override
        public long getId() {
            return getMultiLockId();
        }        

//        public void block() {
//            blockCurrentThread();
//        }
        
    }
    
    static class HoldCounter {
        long x = 0;
        long s = 0;
        long ix = 0;
        long is = 0;
        
        public HoldCounter() {
            x = s = ix = is = 0;
        }
        
        public HoldCounter(HoldCounter other) {
            x = other.x;
            s = other.s;
            ix = other.ix;
            is = other.is;
        }
        
        // performs subtraction of other's values from this's values
        public HoldCounter subtract(HoldCounter other) {
            HoldCounter result = new HoldCounter(this);
            result.x -= other.x;
            result.s -= other.s;
            result.ix -= other.ix;
            result.is -= other.is;
            return result;
        }
        
        public boolean countsAllZero() {
            return x == 0 && s == 0 && ix == 0 && is == 0;
        }
        
        public String toString() {
            return "[" + x + "," + s + "," + ix + "," + is + "]";
        }
    }

    ThreadLocal<HoldCounter> holdCount;
    HoldCounter globalHoldCount;

    MultiLock owner;
    Thread exclusiveOwner;
    
    ReadLock readLock;
    WriteLock writeLock;
    
    List<Thread> waiters;
    
    static AtomicLong counter = new AtomicLong(0);
    
    long id = 0;
    
    public MultiLock(MultiLock o) {
        owner = o;
        holdCount = new ThreadLocal<HoldCounter>() {
            protected HoldCounter initialValue() {
                return new HoldCounter();
            }
        };
        globalHoldCount = new HoldCounter();
        readLock = new ReadLock();
        writeLock = new WriteLock();
        id = counter.incrementAndGet();
        waiters = new ArrayList<Thread>();
    }
    
    public Lock readLock() {
        return readLock;
    }
    
    public Lock writeLock() {
        return writeLock;
    }
    
    public boolean lockRead() {
        boolean ownerLocked = true;
        if (owner != null) {
            ownerLocked = owner.lockIntentionRead();
        }
        if (ownerLocked) {
            if (lock(READ)) {
                return true;
            }
            else {
                if (owner != null) {
                    owner.unlockIntentionRead();
                }
            }
        }
        return false;
    }
    
    public boolean lockWrite() {
        boolean ownerLocked = true;
        if (owner != null) {
            ownerLocked = owner.lockIntentionWrite();
        }
        if (ownerLocked) {
            if (lock(WRITE)) {
                return true;
            }
            else {
                if (owner != null) {
                    owner.unlockIntentionWrite();
                }
            }
        }
        return false;
    }

    public boolean lockIntentionRead() {
        boolean ownerLocked = true;
        if (owner != null) {
            ownerLocked = owner.lockIntentionRead();
        }
        if (ownerLocked) {
            if (lock(INTENTION_READ)) {
                return true;
            }
            else {
                if (owner != null) {
                    owner.unlockIntentionRead();
                }
            }
        }
        return false;
    }
       
    public boolean lockIntentionWrite() {
        boolean ownerLocked = true;
        if (owner != null) {
            ownerLocked = owner.lockIntentionWrite();
        }
        if (ownerLocked) {
            if (lock(INTENTION_WRITE)) {
                return true;
            }
            else {
                if (owner != null) {
                    owner.unlockIntentionWrite();
                }
            }
        }
        return false;
    }
    
    public void unlockRead() {
        unlock(READ);
        if (owner != null) {
            owner.unlockIntentionRead();
        }
    }

    public void unlockWrite() {
        unlock(WRITE);
        if (owner != null) {
            owner.unlockIntentionWrite();
        }
    }
        
    public void unlockIntentionRead() {
        unlock(INTENTION_READ);
        if (owner != null) {
            owner.unlockIntentionRead();
        }
    }
    
    public void unlockIntentionWrite() {
        unlock(INTENTION_WRITE);
        if (owner != null) {
            owner.unlockIntentionWrite();
        }
    }
    
    public MultiLock getOwner() {
        return owner;
    }
    
    public synchronized boolean lock(LockMode req) {
        Thread currThread = Thread.currentThread();
        HoldCounter currHoldCount = holdCount.get();
        HoldCounter groupCounts = globalHoldCount.subtract(currHoldCount);
        if (req == WRITE) {
            if (globalHoldCount.countsAllZero()) {
                globalHoldCount.x++;
                currHoldCount.x++;
                exclusiveOwner = currThread;
//                Logger.println("Write lock " + getMultiLockId() + " acquired by " + currThread.getId());
//                Logger.println("  -- New lock counts: " + globalHoldCount);
                return true;
            }
            else {
                // check that non-X counts are only for current thread
                if (groupCounts.countsAllZero()) {
                    globalHoldCount.x++;
                    currHoldCount.x++;
                    exclusiveOwner = currThread;
//                    Logger.println("Write lock " + getMultiLockId() + " acquired by " + currThread.getId());
//                    Logger.println("  -- New lock counts: " + globalHoldCount);
                    return true;
                }
                else {
                    return false;
                }
            }
        }
        else {
            // req is S, IS or IX
            if (globalHoldCount.x != 0 && exclusiveOwner != currThread) {
                // someone else already is X
                if (AtomicSynchroniser.DEBUG2) Logger.println("Failed to acquire (" + getMultiLockId() + ") because " + exclusiveOwner.getId() + " has it in X mode.");
                return false;
            }

            // either no X or current is X
            
            if (req == INTENTION_READ) {
                // IS is compatible with S, IX, IS
                globalHoldCount.is++;
                currHoldCount.is++;
                return true;
            }
            else if (req == INTENTION_WRITE) {
                // two cases: S == 0 (ok) and S != 0 (thread check)
                if (globalHoldCount.s == 0 || groupCounts.s == 0 || exclusiveOwner == currThread) {
                    // ok
                    globalHoldCount.ix++;
                    currHoldCount.ix++;
                    return true;
                }
            }
            else if (req == READ) {
                // two cases: IX == 0 (ok) and IX != 0 (thread check)
                if (globalHoldCount.ix == 0 || groupCounts.ix == 0  || exclusiveOwner == currThread) {
                    globalHoldCount.s++;
                    currHoldCount.s++;
                    return true;
                }
                if (AtomicSynchroniser.DEBUG2) Logger.println("Failed to acquire (" + getMultiLockId() + "), counts: " + globalHoldCount);
            }
        }
        return false;
    }
    
    public synchronized void unlock(LockMode req) {
        HoldCounter currHoldCount = holdCount.get();
        if (req == WRITE) {
            globalHoldCount.x--;
            currHoldCount.x--;
            if (globalHoldCount.x == 0) {
                exclusiveOwner = null;
            }
//            Logger.println("Write lock " + getMultiLockId() + " released by " + Thread.currentThread().getId());
//            Logger.println("  -- New lock counts: " + globalHoldCount);
        }
        else if (req == READ) {
            globalHoldCount.s--;
            currHoldCount.s--;            
        }
        else if (req == INTENTION_READ) {
            globalHoldCount.is--;
            currHoldCount.is--;
        }
        else if (req == INTENTION_WRITE) {
            globalHoldCount.ix--;
            currHoldCount.ix--;
        }
        // wake up any thread that might be waiting for this lock
        // to become available.
//        notifyWaiters();
    }
    
    public long getMultiLockId() {
        return id;
    }
    
    public void blockCurrentThread() {
        synchronized (this) {
            waiters.add(Thread.currentThread());
        }
        LockSupport.park();
    }
    
//    private synchronized void notifyWaiters() {
//        for (Thread t : waiters) {
//            LockSupport.unpark(t);
//        }
//        waiters.clear();
//    }
    
}
