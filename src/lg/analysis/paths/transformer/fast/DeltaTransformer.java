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

import gnu.trove.procedure.*;
import gnu.trove.set.hash.TLongHashSet;
import lg.analysis.paths.transformer.ITransformer;

public class DeltaTransformer extends Transformer {
        
    private static final long serialVersionUID = 1L;

    public DeltaTransformer() {
        super();
    }
    
    public DeltaTransformer(Transformer t) {
        super(t);
    }
    
    @Override
    // this = this U t
    public void unionWith(ITransformer it) {
        Transformer t = (Transformer)it;
        t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, TLongHashSet tEdges) {
                final TLongHashSet edges = map.get(o);
                if (edges == null) {
                    map.put(o, new TLongHashSet(tEdges));
                }
                else {
                    tEdges.forEach(new TLongProcedure() {
                        public boolean execute(long e) {
                            edges.add(e);
                            return true;
                        }
                    });
                }
                return true;
            }
        });
        
//
//        for (Object o : t.map.keySet()) {
//            Set<TransformerEdge> edges = map.get(o);
//            if (edges == null) {
//                edges = newSet();
//                map.put(o, edges);
//            }
//            edges.addAll(t.map.get(o));
//        }
    }
    
    @Override
    public Transformer composeWith(Transformer t) {
        Transformer res = composeWithBelow(t);
//        res.map.forEachValue(new TObjectProcedure<TLongHashSet>() {
//            @Override
//            public boolean execute(TLongHashSet arg0) {
//                TLongHashSetLG set = (TLongHashSetLG)arg0;
//                Logger.println("set size: " + arg0.size() + ", capacity: " + set.capacity());
//                return true;
//            }
//        });
        return res;
    }
    
    // (t o Æthis)(e) = t(this(e)) (i.e. "this" is below and "t" is above)
    // This is the most common case
//    public Transformer composeWithBelowExp(Transformer t) {
//        if (t instanceof IdentityTransformer || t.map.isEmpty()) {
//            return newInstance(this);
//        }
//        else {
//            Transformer closure = newInstance();
//            for (Object o : map.keySet()) {
//                Set<TransformerEdge> edges = map.get(o);
//                Set<TransformerEdge> newEdges = newSetFast(edges);
//                Set<TransformerEdge> kill = newSet();
//                Set<TransformerEdge> gen = newSet(edges.size());
//
//                // transitive closure
//                for (TransformerEdge te : edges) {
//                    if (te != killEdge) {
//                        // o --> d
//                        Object d = te.getDest();
//                        Set<TransformerEdge> dEdges = t.map.get(d);
//                        if (dEdges != null) {
//                            kill.add(te);
//                            for (TransformerEdge te2 : dEdges) {
//                                if (te2 == killEdge) {
//                                    gen.add(te2);
//                                }
//                                else {
//                                    gen.add(new TransformerEdge(JumpFunctionFactory.composeJumpFunctions(te.getJumpFunction(),te2.getJumpFunction()),te2.getDest()));
//                                }
//                            }
//                        }
//                    }
//                }
//                kill.removeAll(gen);
//                newEdges.removeAll(kill);
//                newEdges.addAll(gen);
//                closure.map.put(o, newEdges);
//            }
//
////            cleanup(closure);
//            
//            return closure;
//        }
//    }
    
    public Transformer composeWithBelow(final Transformer t) {
        if (t instanceof IdentityTransformer || t.map.isEmpty()) {
            return newInstance(this);
        }
        else {
            final Transformer closure = newInstance();
            map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
                public boolean execute(int o, TLongHashSet edges) {
                    final TLongHashSet newEdges = newSet(edges.size()*2); // *2 to anticipate doubling
//                    final TLongHashSet newEdges = newSet(); // *2 to anticipate doubling
                    // transitive closure
                    edges.forEach(new TLongProcedure() {
                        public boolean execute(final long te) {
                            if (te == killEdge) {
                                // o --> e goes through (note we have implicit e --> e)
                                newEdges.add(te);
                            }
                            else {
                                // o --> d
                                int d = TransformerEdgeFactory.getD(te);
                                TLongHashSet dEdges = t.map.get(d);
                                if (dEdges == null) {
                                    // implicit edge in t
                                    newEdges.add(te);
                                }
                                else {
                                    dEdges.forEach(new TLongProcedure() {
                                        public boolean execute(long te2) {
                                            long composed = TransformerEdgeFactory.composeEdges(te, te2);
                                            newEdges.add(composed);
                                            return true;
                                        }
                                    });
                                }
                            }
                            return true;
                        }
                    });
                    closure.map.put(o, newEdges);
                    return true;
                }
            });
            
            // compact all sets
//            compact(closure);
            
            return closure;
        }
//        if (t instanceof IdentityTransformer || t.map.isEmpty()) {
//            return newInstance(this);
//        }
//        else {
//            Transformer closure = newInstance();
//            for (Object o : map.keySet()) {
//                Set<TransformerEdge> edges = map.get(o);
//                Set<TransformerEdge> newEdges = newSet(edges.size()*2);
//                // transitive closure
//                for (TransformerEdge te : edges) {
//                    if (te == killEdge) {
//                        // o --> e goes through (note we have implicit e --> e)
//                        newEdges.add(te);
//                    }
//                    else {
//                        // o --> d
//                        Object d = te.getDest();
//                        Set<TransformerEdge> dEdges = t.map.get(d);
//                        if (dEdges == null) {
//                            // implicit edge in t
//                            newEdges.add(te);
//                        }
//                        else {
//                            for (TransformerEdge te2 : dEdges) {
//                                if (te2 == killEdge) {
//                                    newEdges.add(te2);
//                                }
//                                else {
//                                    newEdges.add(new TransformerEdge(JumpFunctionFactory.composeJumpFunctions(te.getJumpFunction(),te2.getJumpFunction()),te2.getDest()));
//                                }
//                            }
//                        }
//                    }
//                }
//                closure.map.put(o, newEdges);
//            }
//
////            cleanup(closure);
//            
//            return closure;
//        }
    }

    
    // (Æthis o t)(e) = this(t(e)) (i.e. "Æthis" is above and "t" is below)
    public Transformer composeWithAbove(final Transformer t) {
        if (t instanceof IdentityTransformer || t.map.isEmpty()) {
            return newInstance(this);
        }
        else {
            final Transformer closure = newInstance();
            t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
                public boolean execute(int o, TLongHashSet edges) {
                    final TLongHashSet newEdges = newSet(edges.size()*2); // *2 to anticipate doubling
                    // transitive closure
                    edges.forEach(new TLongProcedure() {
                        public boolean execute(final long te) {
                            // o --> d
                            int d = TransformerEdgeFactory.getD(te);
                            TLongHashSet dEdges = map.get(d);
                            // NO IMPLICIT EDGES IN "THIS"
                            if (dEdges != null) {
                                dEdges.forEach(new TLongProcedure() {
                                    public boolean execute(long te2) {
                                        long composed = TransformerEdgeFactory.composeEdges(te, te2);
                                        newEdges.add(composed);
                                        return true;
                                    }
                                });
                            }
                            return true;
                        }
                    });
                    closure.map.put(o, newEdges);
                    return true;
                }
            });

            // take account of implicit edges in 't' transformer.
            map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
                public boolean execute(int o, TLongHashSet edges) {
                    TLongHashSet tEdges = t.map.get(o);
                    if (o == capitalLambda || tEdges == null) {
                        // implicit A --> A edge in 't'. Pass on accesses.
                        final TLongHashSet closureEdges = closure.map.get(o);
                        if (closureEdges == null) {
                            closure.map.put(o, new TLongHashSet(edges));
                        }
                        else {
                            closureEdges.ensureCapacity(edges.size());
                            closureEdges.addAll(edges);
//                            edges.forEach(new TLongProcedure() {
//                                public boolean execute(long e) {
//                                    closureEdges.add(e);
//                                    return true;
//                                }
//                            });
                        }
                    }
                    return true;
                }
            });
            
//            closure.map.forEachValue(new TObjectProcedure<TLongHashSet>() {
//                @Override
//                public boolean execute(TLongHashSet arg0) {
//                    TLongHashSetLG set = (TLongHashSetLG)arg0;
//                    Logger.println("set size: " + arg0.size() + ", capacity: " + set.capacity());
//                    return true;
//                }
//            });
            return closure;
        }
//        if (t instanceof IdentityTransformer || t.map.isEmpty()) {
//            return newInstance(this);
//        }
//        else {
//            Transformer closure = newInstance();
//            for (Object o : t.map.keySet()) {
//                Set<TransformerEdge> edges = t.map.get(o);
//                Set<TransformerEdge> newEdges = newSet(edges.size()*2);
//                // transitive closure
//                for (TransformerEdge te : edges) {
//                    // o --> d
//                    Object d = te.getDest();
//                    Set<TransformerEdge> dEdges = map.get(d);
//                    // NO IMPLICIT EDGES IN THIS
//                    if (dEdges != null) {
//                        for (TransformerEdge te2 : dEdges) {
//                            if (te2 == killEdge) {
//                                newEdges.add(te2);
//                            }
//                            else {
//                                newEdges.add(new TransformerEdge(JumpFunctionFactory.composeJumpFunctions(te.getJumpFunction(),te2.getJumpFunction()),te2.getDest()));
//                            }
//                        }
//                    }
//                }
//                closure.map.put(o, newEdges);
//            }
//            // take account of implicit edges in 't' transformer. 
//            for (Object o : map.keySet()) {
//                if (o == capitalLambda) {
//                    // implicit A --> A edge in 't'. Pass on accesses.
//                    Set<TransformerEdge> transEdges = closure.map.get(o);
//                    if (transEdges == null) {
//                        transEdges = newSet();
//                        closure.map.put(o, transEdges);
//                    }
//                    Set<TransformerEdge> accesses = map.get(o);
//                    transEdges.addAll(accesses);
//                }
//                else {
//                    Set<TransformerEdge> tEdges = t.map.get(o);
//                    if (tEdges == null) {
//                        // implicit edge o --> o exists in 't'
//                        Set<TransformerEdge> transEdges = closure.map.get(o);
//                        if (transEdges == null) { // transEdges should always be null
//                            transEdges = newSet();
//                            closure.map.put(o, transEdges);
//                        }
//                        Set<TransformerEdge> oEdges = map.get(o);
//                        transEdges.addAll(oEdges);
//                    }
//                }
//            }
//            
//            // use compact ArraySet for storage
////            for (Object o : closure.map.keySet()) {
////                closure.map.put(o, newArraySet(closure.map.get(o)));
////            }
//
////            cleanup(closure);
//            
//            return closure;
//        }
    }
    
    @Override
    protected void cleanup(Transformer t) {
        // no-op
    }
    
    @Override
    protected Transformer newInstance() {
        return new DeltaTransformer();
    }

    @Override
    protected Transformer newInstance(Transformer t) {
        return new DeltaTransformer(t);
    }
    
    @Override
    public Transformer clone() {
        return new DeltaTransformer(this);
    }
    
    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        else if (other == null) {
            return false;
        }
        else {
            if (other instanceof DeltaTransformer) {
                DeltaTransformer t = (DeltaTransformer) other;
//              if (map.keySet().equals(t.map.keySet())) {
//                  for (Object o : map.keySet()) {
//                      Set<TransformerEdge> edges = map.get(o);
//                      Set<TransformerEdge> tEdges = t.map.get(o);
//                      if (edges == null || tEdges == null) {
//                          if (edges != tEdges) {
//                              return false;
//                          }
//                      }
//                      else {
//                          // using HashSets are much faster
//                          edges = new HashSet<TransformerEdge>(edges);
//                          tEdges = new HashSet<TransformerEdge>(tEdges);
//                          if (!edges.equals(tEdges)) {
//                              return false;
//                          }
//                      }
//                  }
//                  return true;
//              }
//              else {
//                  return false;
//              }
                return map.equals(t.map);
            }
            else {
                return false;
            }
        }
    }
    
}
