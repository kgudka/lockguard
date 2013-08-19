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

package lg.analysis.local;

import java.util.*;

import lg.analysis.locks.*;
import lg.analysis.paths.LockSet;
import lg.cfg.AtomicSection;
import lg.util.*;
import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.ForwardFlowAnalysis;

// only need to run this analysis on methods that contain atomic sections
public class MethodEscapeAnalysisTransformer {

    ExceptionalUnitGraph enclosingMethodCfg;
    AtomicSection atomic;
    LockSet locks;
    
    public MethodEscapeAnalysisTransformer(AtomicSection a, LockSet l) {
        enclosingMethodCfg = a.getEnclosingUnitGraph();
        atomic = a;
        locks = l;
    }
    
    public void doAnalysis() {

        long startTime = System.currentTimeMillis();
        
        IntraMethodEscapeAnalysis analysis = new IntraMethodEscapeAnalysis(enclosingMethodCfg);
        analysis.doAnalysis();
        
        // remove locks on locals that do not escape just before the atomic
        Unit head = atomic.getHeads().get(0);
        Set<Local> escapingLocals = analysis.getFlowBefore(head);
        Logger.println("Escaping locals: " + escapingLocals);
//        ProfilerSupport.waitForKeyPress();
        
        Set<Lock> kill = new HashSet<Lock>();
        for (Lock l : locks) {
            if (l instanceof PathLock) {
                PathLock pl = (PathLock)l;
                if (pl.getPrefix() == null) {
                    PathLookup plookup = pl.getLookup();
                    if (plookup instanceof LocalLookup) {
                        LocalLookup llookup = (LocalLookup)plookup;
                        Local x = llookup.getLocal();
                        if (!contains(escapingLocals, x)) {
                            Logger.println(x + " is a method-local object", ANSICode.FG_GREEN);
                            kill.add(pl);
                        }
                    }
                }
            }
        }
        
        locks.removeAll(kill);
        for (Lock l : kill) {
            PathLock pl = (PathLock)l;
            locks.add(new PathLock(pl.getPrefix(), pl.getLookup(), pl.isWrite(), pl.isThreadLocal(), pl.isInstanceLocal(), pl.getPointsToSet(), pl.isDominated(), pl.isDuplicate(), pl.isClassLocal(), pl.isReadOnly(), pl.doMultiLocking(), true));
        }
        
        long took = System.currentTimeMillis() - startTime;
        AnalysisTimer.addForMethodLocalAnalysis(took);
    }   
    
    private boolean contains(Set<Local> escapingLocals, Local x) {
        for (Local l : escapingLocals) {
            if (l.equivTo(x)) { // equals() won't work
                return true;
            }
        }
        return false;
    }

    class IntraMethodEscapeAnalysis extends ForwardFlowAnalysis<Unit, Set<Local>> {

        public IntraMethodEscapeAnalysis(DirectedGraph<Unit> graph) {
            super(graph);
        }

        @Override
        protected void flowThrough(Set<Local> in, Unit u, Set<Local> out) {
            
            out.clear();
            out.addAll(in);
            Stmt d = (Stmt)u;
            if (d instanceof DefinitionStmt) {
                DefinitionStmt defSt = (DefinitionStmt)d;

                Value lval = defSt.getLeftOp();
                Value rval = defSt.getRightOp();

                if(lval instanceof Local && lval.getType() instanceof RefLikeType) {
                    Local x = (Local)lval;
                    // x = blah
                    out.remove(x);
                    if (rval instanceof Local) {
                        // x = y
                        Local y = (Local)rval;
                        if (in.contains(y)) {
                            out.add(x);
                        }
                    }
                    else if (rval instanceof NullConstant) {
                        // x = null
                    }
                    else if (rval instanceof NewExpr || rval instanceof NewArrayExpr || rval instanceof NewMultiArrayExpr) {
                        // x = new/newarray/newmultiarray
                    }
                    else if (rval instanceof StringConstant) {
                        // x = ""
                    }
                    else if(rval instanceof CastExpr) {
                        CastExpr castEx = (CastExpr)rval;
                        if(castEx.getOp() instanceof Local) {
                            // x = (type)y
                            Local y = (Local)castEx.getOp();
                            if (in.contains(y)) {
                                out.add(x);
                            }
                        }
                        else if(castEx.getOp() instanceof NullConstant) {
                            // x = (type)null
                        }
                        else if(castEx.getOp() instanceof StringConstant) {
                            // x = (String)""
                        }
                    }
                    else if (rval instanceof InstanceFieldRef) {
                        // x = y.f
                        out.add(x);
                    }
                    else if (rval instanceof StaticFieldRef) {
                        // x = C.f
                        out.add(x);
                    }
                    else if (rval instanceof ArrayRef) {
                        // x = y[i]
                        out.add(x);
                    }
                    else if (rval instanceof ThisRef) {
                        // x = @this
                        out.add(x);
                    }
                    else if (rval instanceof ParameterRef) {
                        // x = @parameterN
                        out.add(x);
                    }
                    else if (rval instanceof CaughtExceptionRef) {
                        // x = @caughtexception
                        out.add(x);
                    }
                    else if (rval instanceof InvokeExpr) {
                        out.add(x);
                    }
                }
                else if (lval instanceof InstanceFieldRef && lval.getType() instanceof RefLikeType) {
                    // x.f = blah
                    InstanceFieldRef instFieldRef = (InstanceFieldRef)lval;
                    Local x = (Local)instFieldRef.getBase();
                    if (rval instanceof Local) {
                        // x.f = y
                        Local y = (Local)rval;
                        if (in.contains(x)) {
                            out.add(y);
                        }
                    }
                    else if (rval instanceof NullConstant) {
                        // x.f = null
                    }
                    else if (rval instanceof StringConstant) {
                        // x.f = "";
                    }
                }
                else if (lval instanceof StaticFieldRef && lval.getType() instanceof RefLikeType) {
                    // C.f = blah
                    if (rval instanceof Local) {
                        // C.f = y
                        Local y = (Local)rval;
                        out.add(y);
                    }
                    else if (rval instanceof NullConstant) {
                        // C.f = null
                    }
                    else if (rval instanceof StringConstant) {
                        // C.f = ""
                    }
                }
                else if (lval instanceof ArrayRef && lval.getType() instanceof RefLikeType) {
                    // x[i] = blah
                    ArrayRef arrRef = (ArrayRef)lval;
                    Local x = (Local)arrRef.getBase();
                    if (rval instanceof Local) {
                        // x[i] = y
                        Local y = (Local)rval;
                        if (in.contains(x)) {
                            out.add(y);
                        }
                    }
                    else if (rval instanceof NullConstant) {
                        // x[i] = null
                    }
                    else if (rval instanceof StringConstant) {
                        // x[i] = ""
                    }
                }
            }
            else if (d instanceof ReturnStmt) {
                ReturnStmt r = (ReturnStmt)d;
                Value val = r.getOp();
                if (val instanceof Local && val.getType() instanceof RefLikeType) {
                    Local x = (Local)val;
                    out.add(x);
                }
                else if (val instanceof NullConstant) {
                }
                else if (val instanceof StringConstant) {
                }
            }
            else if (d instanceof ThrowStmt) {
                ThrowStmt t = (ThrowStmt)d;
                Value v = t.getOp();
                if (v instanceof Local) {
                    Local x = (Local)v;
                    out.add(x);
                }
            }
            
            if (d.containsInvokeExpr()) {
                // add all args as escaping
                InvokeExpr ie = d.getInvokeExpr();
                List<Value> args = ie.getArgs();
                for (Value v : args) {
                    if (v instanceof Local) {
                        Local l = (Local)v;
                        out.add(l);
                    }
                }
            }
            
//            Logger.println("***************************************", ANSICode.FG_MAGENTA);
//            Logger.println("u: " + u, ANSICode.FG_MAGENTA);
//            Logger.println("in: " + in, ANSICode.FG_RED);
//            Logger.println("out: " + out, ANSICode.FG_BLUE);
//            Logger.println("***************************************", ANSICode.FG_MAGENTA);
//            ProfilerSupport.waitForKeyPress();
        }

        @Override
        protected Set<Local> newInitialFlow() {
            return new HashSet<Local>();
        }

        @Override
        protected Set<Local> entryInitialFlow() {
            return new HashSet<Local>();
        }

        @Override
        protected void merge(Set<Local> in1, Set<Local> in2, Set<Local> out) {
            out.clear();
            out.addAll(in1);
            out.addAll(in2);
        }

        @Override
        protected void copy(Set<Local> source, Set<Local> dest) {
            dest.clear();
            dest.addAll(source);
        }
        
        public void doAnalysis() {
            super.doAnalysis();
        }

    }

}
