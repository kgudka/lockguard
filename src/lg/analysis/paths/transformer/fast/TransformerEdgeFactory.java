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

package lg.analysis.paths.transformer.fast;

import lg.analysis.paths.transformer.state.*;
import lg.util.*;
import soot.Scene;
import soot.jimple.Jimple;
import soot.util.*;

public class TransformerEdgeFactory {

    public static final int INITIAL_STATE_COUNTER = 1; // 0 is reserved to allow passing on values by using bit-wise OR (|)
    public static final long START_STATE = 2097151; // 2^21 - 1 (i.e. all 1's in src state field)
    private static final long KILL_EDGE = -1L;
    
    private static final long CLEAR_SRC_D = 0xC00001FFFFF00000L;
    private static final long CLEAR_D = 0xFFFFFFFFFFF00000L;
    
    public static final long newAccessEdge(State src, State dst, boolean write, Object d) {
        long srcNum = src.getNumber();
        long dstNum = dst.getNumber();
        long dNum = SymbolNumberer.getNumber(d);
        checkState(srcNum);
        checkState(dstNum);
        checkSymbol(dNum);
        return 1L << 63 | (write ? 1L : 0L) << 62 | srcNum << 41 | dstNum << 20 | dNum; 
    }
    
    private static void checkSymbol(long d) {
        if (!(0 <= d && d <= 1048575)) {
            throw new IllegalArgumentException("symbol " + d + " doesn't fit");
        }
    }

    private static void checkState(long s) {
        if (!(0 <= s && s <= START_STATE)) {
            throw new IllegalArgumentException("state " + s + " doesn't fit");
        }
    }

    public static final long newLoadEdge(State src, Object d) {
        long srcNum = src.getNumber();
        long dNum = SymbolNumberer.getNumber(d);
        checkState(srcNum);
        checkSymbol(dNum);
        return srcNum << 41 | dNum;
    }
    
    public static final long newStoreEdge(Object d) {
        long dNum = SymbolNumberer.getNumber(d);
        checkSymbol(dNum);
        return START_STATE << 41 | dNum;
    }    

    public static final long newKillEdge() {
        return KILL_EDGE;
    }
    
    public static final long newIdEdge(Object d) {
        int dNum = SymbolNumberer.getNumber(d);
        checkSymbol(dNum);
        return dNum;
    }

    public static final long newIdEdge(int d) {
        checkSymbol(d);
        return d;
    }    
    
    // post: e2 o e1
    public static final long composeEdges(long e1, long e2) {
        if (isId(e2)) {
            return (e1 & CLEAR_D) | e2;
        }
        else if (isKill(e2)) {
            return e2;
        }
        else if (isAccess(e1)) {
            return (e1 & CLEAR_SRC_D) | e2;
        }
        else {
            return e2;
        }
    }
    
    public static final long updateD(long e, int d) {
        checkSymbol(d);
        return (e & CLEAR_D) | d;
    }
    
    public static final boolean isId(long e) {
        return (e >> 20) == 0;
    }
    
    public static final boolean isKill(long e) {
        return e == KILL_EDGE;
    }
    
    private static final boolean isAccess(long e) {
        return (e >>> 63) == 1;
    }
    
    private static String long2BitStr(long e) {
        String s = "";
        for (int i=0; i<64; i++) {
            s = ((e & 1L) == 1 ? "1" : "0") + s;
            e = e >>> 1;
        }
        return s;
    }

    private static void outputFields(long e, boolean write, State src, State dst, Object d) {
        System.out.println();
        System.out.println("e: " + long2BitStr(e));
        System.out.println("access: " + isAccess(e));
        System.out.println("kill: " + isKill(e));
        System.out.println("id: " + isId(e));
        System.out.println("write: " + isWrite(e));
        System.out.println("write (real): " + write);
        System.out.println("src: " + getSrc(e));
        System.out.println("src (real): " + (src == null ? 0 : src.getNumber()));
        System.out.println("dst: " + getDst(e));
        System.out.println("dst (real): " + (dst == null ? 0 : dst.getNumber()));
        System.out.println("d: " + getD(e));
        System.out.println("d (real): " + (d == null ? 0 : SymbolNumberer.getNumber(d)));
        System.out.println();
    }
    
    private static final long getSrc(long e) {
        return (e & ~CLEAR_SRC_D) >> 41;
    }
    
    private static final long getDst(long e) {
        return (e >>> 20) & 0x00000000001FFFFFL;
    }
    
    public static final State getSrcState(long e) {
        return getState(getSrc(e));
    }
    
    public static final State getDstState(long e) {
        return getState(getDst(e));
    }
    
    private static final State getState(long n) {
        return StateFactory.lookup((int)n);
    }
    
    public static final int getD(long e) {
        return (int)(e & ~CLEAR_D);
    }
    
    public static final boolean isWrite(long e) {
        return (e & 0x4000000000000000L) > 0;
    }
    
    // test harness
    public static void main(String[] args) {
        Jimple j = Jimple.v();
        
        System.out.println("clear_d: " + long2BitStr(CLEAR_D));
        System.out.println("clear_src_d: " + long2BitStr(CLEAR_SRC_D));
        
        boolean write = true;
        State s1 = StartState.v();
        State s2 = new State();
        Numberable d = new Numberable() {
            public int getNumber() {
                return 1048575;
            }
            public void setNumber(int number) {
            }
        };
        
        // test each field of access edge
        long e1 = newAccessEdge(s1, s2, write, d);
        outputFields(e1, write, s1, s2, d);
        
        // test write bit
        write = false;
        long e2 = newAccessEdge(s1, s2, write, d);
        outputFields(e2, write, s1, s2, d);

        // test clear_src_d
        write = true;
        s2 = StartState.v();
        long e3 = newAccessEdge(s1, s2, write, d);
        outputFields(e3, write, s1, s2, d);
        long e4 = e3 & CLEAR_SRC_D;
        outputFields(e4, write, null, s2, null);        

        // test clear_d
        long e5 = e3 & CLEAR_D;
        outputFields(e5, write, s1, s2, null);
        
        // test load
        long e6 = newLoadEdge(s1, d);
        outputFields(e6, false, s1, null, d);
        
        // test store
        long e7 = newStoreEdge(d);
        outputFields(e7, false, s1, null, d);
        
        // test kill
        long e8 = newKillEdge();
        outputFields(e8, true, null, null, null);

        // test id
        long e9 = newIdEdge(d);
        outputFields(e9, false, null, null, d);
        
        // test updateD
        d = new Numberable() {
            public void setNumber(int number) {
            }
            public int getNumber() {
                return 123;
            }
        };
        long e10 = updateD(e8, d.getNumber());
        outputFields(e10, false, null, null, d);
        
        System.out.println(1001 % 1000);
    }
    
    private static boolean isLoad(long e) {
        return ((e & ~CLEAR_SRC_D) & CLEAR_D) >> 41 != START_STATE;
    }
    
    public static String toString(long e) {
        if (isKill(e)) {
            return "-->\u2205";
        }
        else {
            int d = getD(e);
            try {
                String dStr = SymbolNumberer.getObject(d).toString();
                if (isId(e)) {
                    return "-->" + dStr;
                }
                else if (isAccess(e)) {
                    long src = getSrc(e);
                    String srcStr = src == START_STATE ? "start" : ("" + src);
                    return "(" + srcStr + "," + getDst(e) + "," + isWrite(e) + ")-->" + dStr;
                }
                else if (isLoad(e)) {
                    return "L(" + getSrc(e) + ")-->" + dStr; 
                }
                else {
                    return "S-->" + dStr;
                }
            } catch (NullPointerException npe) {
                Logger.println("d: " + d);
                Logger.println("e: " + long2BitStr(e));
                throw npe;
            }
        }
    }
    
}
