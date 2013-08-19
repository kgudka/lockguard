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

import java.util.*;

import lg.util.*;

import org.jikesrvm.objectmodel.MiscHeader;

public class AtomicSynchroniser {

    public static final boolean DEBUG = false;
    
    public static final boolean DEBUG2 = false;
    
    public static final boolean DEBUG3 = false;
    
    private static ThreadLocal<LinkedList<Lock>> acquired = new ThreadLocal<LinkedList<Lock>>() {
        protected LinkedList<Lock> initialValue() {
            return new LinkedList<Lock>();
        }
    };
    
    private static ThreadLocal<Integer> atomicNestingLevel = new ThreadLocal<Integer>() {
        protected Integer initialValue() {
            return new Integer(0);
        }
    };
    
    // Use a wrapper for the attempt counter to prevent lots of temporary
    // Long/Integer instances from being created.
    static class AttemptCounter {
        long count = 0;
    }
    
    private static ThreadLocal<AttemptCounter> numAttempts = new ThreadLocal<AttemptCounter>() {
       protected AttemptCounter initialValue() {
           return new AttemptCounter();
       }
    };
    
    static int seed = 0;
    public static synchronized int getNextBackoff() {
        seed = (seed+1) % 20;
        return seed;
    }
    
    private static ThreadLocal<Integer> backoffInterval = new ThreadLocal<Integer>() {
        protected Integer initialValue() {
//            int rand = new Random().nextInt(10);
//            Logger.println("backoff interval for " + Thread.currentThread() + ": " + rand);
//            return rand;
            return getNextBackoff();
        };
    };
    
//    private static Map<ObjectWrapper,InstanceLock> objToLock = new HashMap<ObjectWrapper, InstanceLock>();
    
    private static Map<Object,TypeLock> typeToLock = new HashMap<Object, TypeLock>();
    
    public static boolean lockInstanceRead(Object o, boolean multi) {
        InstanceLock l = getInstanceLock(o);
//        Logger.println(Thread.currentThread().getId() + " got instance lock (" + l.readLock().getId() + ") - " + l + " for obj " + o, ANSICode.FG_MAGENTA);
        return lock(l.readLock());
    }
    
    public static boolean lockInstanceWrite(Object o, boolean multi) {
        InstanceLock l = getInstanceLock(o);
//        Logger.println(Thread.currentThread().getId() + " got instance lock (" + l.writeLock().getId() + ") - " + l + " for obj " + o, ANSICode.FG_MAGENTA);
        return lock(l.writeLock());
    }

    public static boolean lockTypeRead(Class<?> c) {
        TypeLock l = getTypeLock(c);
//        Logger.println(Thread.currentThread().getId() + " got type lock (" + l.readLock().getId() + ") - " + l + " for type " + c, ANSICode.FG_MAGENTA);
        return lock(l.readLock());
    }
    
    public static boolean lockTypeWrite(Class<?> c) {
        TypeLock l = getTypeLock(c);
//        Logger.println(Thread.currentThread().getId() + " got type lock (" + l.writeLock().getId() + ") - " + l + " for type " + c, ANSICode.FG_MAGENTA);
        return lock(l.writeLock());
    }
    
    public static boolean lock(Lock l) {
        if (DEBUG2) Logger.println(Thread.currentThread().getId() + " acquiring (" + l.getId() + ") - " + l);
        if (l.lock()) {
//            Logger.println(Thread.currentThread().getId() + " acquired (" + l.getId() + ") - " + l, ANSICode.FG_BLUE);
            acquired.get().add(l);
            // reset the num of attempts counter            
//            AttemptCounter c = numAttempts.get();
//            c.count = 0;
            return true;
        }
        else {
//            Logger.println(Thread.currentThread().getId() + " unable to acquire (" + l.getId() + ") - " + l, ANSICode.FG_RED);
            blockNoDeadlock(l);
            return false;
        }
    }
    
    public static void blockNoDeadlock(Lock l) {
        // unlock all currently acquired locks to avoid deadlock
        unlockAll();

        // block on l
        if (AtomicSynchroniser.DEBUG2) Logger.println(Thread.currentThread().getId() + " going to sleep: " + l.getClass(), ANSICode.FG_RED);
//        l.block();

        if (AtomicSynchroniser.DEBUG2) System.out.println(Thread.currentThread().getId() + " woke up waiting for " + l.getClass());

        // backoff before trying to acquire locks again
        AttemptCounter c = numAttempts.get();
        long attempts = ++c.count;
        int interval = backoffInterval.get();
        try {
//            Logger.println(Thread.currentThread().getId() + " going to back off for " + (attempts*interval) + "ms", ANSICode.FG_RED);
            Thread.sleep(attempts*interval);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }
    
    public static void unlockAll() {
        if (DEBUG2) Logger.println(Thread.currentThread().getId() + " unlocking all locks", ANSICode.FG_GREEN);
        LinkedList<Lock> locks = acquired.get();
//        Logger.println("  -- locks: " + locks, ANSICode.FG_GREEN);
        for (Lock l : locks) {
            l.unlock();
            if (DEBUG2) Logger.println(Thread.currentThread().getId() + " released (" + l.getId() + ") - " + l, ANSICode.FG_GREEN);
        }
        locks.clear();
    }
    
    public static void enterAtomic() {
        if (DEBUG2) Logger.println(Thread.currentThread().getId() + " entering atomic");
        atomicNestingLevel.set(atomicNestingLevel.get()+1);
        AttemptCounter c = numAttempts.get();
        c.count = 0;
    }
    
    public static void exitAtomic() {
        if (DEBUG2) Logger.println(Thread.currentThread().getId() + " exiting atomic");
        atomicNestingLevel.set(atomicNestingLevel.get()-1);
    }
    
    public static boolean isOuterAtomic() {
        return atomicNestingLevel.get().intValue() == 1;
    }
    
    // we use an ObjectWrapper, because performing get(o) on some object o can
    // lead to concurrent modification exceptions if the object is modified 
    // while the hashCode() function is iterating through it! The wrapper ensures
    // that hashCode just returns a simple value
    static class ObjectWrapper {
        Object o;
        
        public ObjectWrapper(Object obj) {
            o = obj;
        }
        
        public int hashCode() {
            return System.identityHashCode(o);
        }
        
        @Override
        public boolean equals(Object o) {
            if (o instanceof ObjectWrapper) {
                ObjectWrapper w = (ObjectWrapper)o;
                return w.o == this.o;
            }
            return false;
        }
        
    }
    
    private static InstanceLock getInstanceLock(Object o) {
        // We cannot maintain a map from object -> lock, because
        // if the object is a collection, it may traversing it when
        // hashCode() is called, which can lead to concurrent modification
        // exceptions. Thus, we store the lock in the object's header.
        // Besides, storing a collection in another collection is a 
        // bad idea because its hashcode() changes when its elements change.
        
        // Also, by using a map, objects will not be garbage collected as
        // the map keeps a reference to them. 
        InstanceLock ilock = (InstanceLock)MiscHeader.getLock(o);
        if (ilock == null) {
          synchronized(o) {
            ilock = (InstanceLock)MiscHeader.getLock(o);
            if (ilock == null) {
              Class<?> c = o.getClass();
              TypeLock tlock = getTypeLock(c);
              ilock = new InstanceLock(tlock);
              MiscHeader.setLock(o, ilock);
            }
          }
        }
        return ilock;

//        synchronized (objToLock) {
//            ObjectWrapper wrapper = new ObjectWrapper(o);
//            InstanceLock ilock = objToLock.get(wrapper);
//            if (ilock == null) {
//                Class<?> c = o.getClass();
//                TypeLock tlock = getTypeLock(c);
//                ilock = new InstanceLock(tlock);
//                objToLock.put(wrapper, ilock);
//            }
//            return ilock;
//        }
    }
    
    private static TypeLock getTypeLock(Class<?> c) {
        synchronized (typeToLock) {
            TypeLock tlock = typeToLock.get(c);
            if (tlock == null) {
                tlock = new TypeLock();
                typeToLock.put(c, tlock);
            }
            return tlock;
        }
    }    
}
