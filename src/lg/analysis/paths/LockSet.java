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

package lg.analysis.paths;

import java.io.*;
import java.util.*;

import lg.analysis.locks.*;
import lg.util.*;
import soot.Type;

public class LockSet extends HashSet<Lock> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

//    public LockSet() {
//        super(new LockLengthComparator());
//    }
    
//    @Override
//    public boolean add(Lock o) {
//        Lock kill = null;
//        for (Lock l : this) {
//            if (l.subsumes(o)) {
//                return false;
//            }
//            else if (o.subsumes(l)) {
//                kill = l;
//                break;
//            }
//        }
//        
//        remove(kill);
//        //super.add(o);
//        
//        return super.add(o);
//    }

    // post: returns a pair of sets corresponding to type locks and path locks
    //       respectively. This method guarantees that path locks are in prefix
    //       order (i.e. prefixes always precede). 
    public Pair<Set<Lock>,Set<Lock>> separateLocks() {
        Set<Lock> types = new LockSet();
        Set<Lock> lvalues = new TreeSet<Lock>(new Comparator<Lock>() {
            public int compare(Lock l1, Lock l2) {
                PathLock p1 = (PathLock)l1;
                PathLock p2 = (PathLock)l2;
                int stringPathCmp = p1.toStringPath().compareTo(p2.toStringPath());
                if (stringPathCmp == 0) {
                    return p1.toString().compareTo(p2.toString());
                }
                else {
                    return stringPathCmp;
                }
            }
        });
        
        for (Lock l : this) {
            if (l instanceof TypeLock) {
                types.add(l);
            }
            else {
                PathLock pl = (PathLock)l;
                lvalues.add(pl);
            }
        }
        return new Pair<Set<Lock>,Set<Lock>>(types, lvalues);
    }
    
    public String toString() {
        String s = "";
        Pair<Set<Lock>,Set<Lock>> setPair = separateLocks();
        Set<Lock> types = setPair.getFirst();
        Set<Lock> lvalues = setPair.getSecond();
        
        s += "Type locks:\n";
        for (Lock l : types) {
            s += (l.toString() + "\n");
        }
        s += "\nInstance locks:\n";
        for (Lock l : lvalues) {
            s += (l.toString() + "\n");
        }
        return s;
    }
    
    public void addRequiredLocksForInstanceLocalAccesses() {
        Set<Lock> newLocks = new HashSet<Lock>();
        for (Lock l : this) {
            if (l instanceof PathLock && l.isInstanceLocal()) {
                PathLock pl = (PathLock)l; 
                // find non-local prefix 
                while (pl.isInstanceLocal()) {
                    pl = pl.getPrefix();
                }
                // add a new lock with the r/w mode of l
                PathLock pl2 = new PathLock(pl.getPrefix(), pl.getLookup(), l.isWrite(), pl.isThreadLocal(), pl.isInstanceLocal(), pl.getPointsToSet(), pl.isDominated(), pl.isDuplicate(), pl.isClassLocal(), pl.isReadOnly(), pl.doMultiLocking(), pl.isMethodLocal());
                Logger.println("Adding " + pl2 + " to protect instance local " + l, ANSICode.FG_GREEN);
                newLocks.add(pl2);
            }
        }
        addAll(newLocks);
    }

    public void addRequiredLocksForClassLocalAccesses() {
        Set<Lock> newLocks = new HashSet<Lock>();
        for (Lock l : this) {
            if (l instanceof PathLock && l.isClassLocal()) {
                PathLock pl = (PathLock)l; 
                // get lock on class 
                pl = pl.getPrefix();
                // add a new lock with the r/w mode of l
                PathLock pl2 = new PathLock(pl.getPrefix(), pl.getLookup(), l.isWrite(), pl.isThreadLocal(), pl.isInstanceLocal(), pl.getPointsToSet(), pl.isDominated(), pl.isDuplicate(), pl.isClassLocal(), pl.isReadOnly(), pl.doMultiLocking(), pl.isMethodLocal());
                Logger.println("Adding " + pl2 + " to protect class local " + l, ANSICode.FG_GREEN);
                newLocks.add(pl2);
            }
        }
        addAll(newLocks);
    }
    
    public void removeSubsumed() {
        Set<Lock> kill = new HashSet<Lock>();
        for (Lock l : this) {
            if (l.isWrite()) {
                for (Lock l2 : this) {
                    if (l.subsumes(l2)) {
                        kill.add(l2);
                    }
                }
            }
        }
        removeAll(kill);
    }
    
    public void removeIgnoredTypes(List<String> ignoredTypes) {
        Set<Lock> kill = new HashSet<Lock>();
        for (Lock l : this) {
            if (l instanceof TypeLock) {
                TypeLock tl = (TypeLock)l;
                Type t = tl.getType();
                if (ignoredTypes.contains(t.toString())) {
                    kill.add(l);
                }
            }
            else {
                PathLock pl = (PathLock)l;
                String pathStr = pl.toStringPath();
                for (String s : ignoredTypes) {
                    if (pathStr.startsWith(s)) {
                        kill.add(pl);
                    }
                }
            }
        }
        for (Lock l : kill) {
            Logger.println("Ignoring lock " + l, ANSICode.FG_RED);
        }
        removeAll(kill);
    }
    
    public Pair<Set<String>,Set<String>> toStrings() {
        
        Pair<Set<Lock>,Set<Lock>> setPair = separateLocks();
        Set<Lock> types = setPair.getFirst();
        Set<Lock> paths = setPair.getSecond();
        
        Set<String> typesStr = new HashSet<String>();
        for (Lock l : types) {
            typesStr.add(l.toString());
        }
        
        Set<String> pathsStr = new HashSet<String>();
        for (Lock l : paths) {
            pathsStr.add(l.toString());
        }
        
        return new Pair<Set<String>, Set<String>>(typesStr, pathsStr);
    }
    
    public void print() {
        print(false);
    }
    
    public void print(boolean onlyAcquired) {
        Pair<Set<Lock>,Set<Lock>> setPair = separateLocks();
        Set<Lock> types = setPair.getFirst();
        Set<Lock> lvalues = setPair.getSecond();
        
        Logger.println("");
        Logger.println("Type locks:");
        for (Lock l : types) {
            if (!onlyAcquired || (onlyAcquired && l.willBeAcquired())) {
                Logger.println((l.isMethodLocal() ? "^" : "") + (l.isReadOnly() ? "&" : "") + (l.isThreadLocal() ? "*" : "") + (l.isInstanceLocal() ? "#" : "") + l.toString(), ANSICode.FG_RED);
            }
        }
        Logger.println("");
        Logger.println("Instance locks:");
        for (Lock l : lvalues) {
            if (!onlyAcquired || (onlyAcquired && l.willBeAcquired())) {
                Logger.println((l.isMethodLocal() ? "^" : "") + (l.isReadOnly() ? "&" : "") + (l.isDuplicate() ? "$" : "") + (l.isDominated() ? "%" : "") + (l.isThreadLocal() ? "*" : "") + (l.isClassLocal() ? "£" : "") + (l.isInstanceLocal() ? "#" : "") + l.toString(), ANSICode.FG_BLUE);
            }
        }
    }
    
    public void output(String filename) {
        try {
            PrintStream p = new PrintStream(filename);
            String s = toString();
            p.println(s);
            p.flush();
            p.close();
        }
        catch (FileNotFoundException fnfe) {
        }
    }
    
    // true <-> this set is not empty and contains at least one lock that will be acquired at run-time
    public boolean willBeAcquired() {
        for (Lock l : this) {
            if (l.willBeAcquired()) {
                return true;
            }
        }
        return false;
    }
    
}
