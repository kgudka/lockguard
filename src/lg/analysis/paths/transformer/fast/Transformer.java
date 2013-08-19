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

import gnu.trove.map.hash.*;
import gnu.trove.procedure.*;
import gnu.trove.set.hash.TLongHashSet;

import java.io.Serializable;
import java.util.*;

import lg.analysis.paths.automata.*;
import lg.analysis.paths.transformer.*;
import lg.analysis.paths.transformer.state.*;
import lg.transformer.AtomicTransformer;
import lg.util.*;
import soot.*;
import soot.util.*;

public class Transformer implements Cloneable, Serializable, ITransformer {
        
    private static final long serialVersionUID = 1L;
    
    protected TIntObjectHashMap<TLongHashSet> map;
    protected static final long killEdge = TransformerEdgeFactory.newKillEdge();
    protected static final int capitalLambda = SymbolNumberer.getNumber(Access.v());
    protected static final ArrayElement arrElem = ArrayElement.v();
    protected static final int retVar = SymbolNumberer.getNumber(ReturnVariable.v());
    protected static final int thisVar = SymbolNumberer.getNumber(ThisVariable.v()); 
    protected static final State startState = StartState.v();
    
    public Transformer() {
        map = new TIntObjectHashMap<TLongHashSet>();  
    }
    
    protected Transformer(Transformer t) {
        this();
        overwriteWith(t);
    }
    
    // Overwrite with contents from t.
    // Differs from unionWith, as it doesn't make implicit edges explicit.
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#overwriteWith(lg.analysis.paths.transformer.Transformer)
     */
    public void overwriteWith(Transformer t) {
        // don't use map.putAll as it causes problems due to aliasing
        // (it doesn't create new HashSets)
        t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, TLongHashSet d) {
                map.put(o, new TLongHashSet(d));
                return true;
            }
        });
//        for (Object o : t.map.keySet()) {
//            map.put(o, newSetFast(t.map.get(o)));
//        }
    }

    // retains only the edges that are both in "this" and "t"
    // (i.e. like intersection)
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#retainAll(lg.analysis.paths.transformer.Transformer)
     */
    public void retainAll(final Transformer t) {
        map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, final TLongHashSet edges) {
                final TLongHashSet tEdges = t.map.get(o);
                if (tEdges == null) {
                    map.remove(o);
                }
                else {
                    edges.forEach(new TLongProcedure() {
                        public boolean execute(long value) {
                            if (!tEdges.contains(value)) {
                                edges.remove(value);
                            }
                            return true;
                        }
                    });
                }
                return true;
            }
        });      
//        Set<Object> kill = new HashSet<Object>();
//        for (Object o : map.keySet()) {
//            Set<TransformerEdge> tEdges = t.map.get(o);
//            if (tEdges == null) {
//                kill.add(o);
//            }
//            else {
//                Set<TransformerEdge> edges = map.get(o);
//                edges.retainAll(tEdges);
//            }
//        }
//        for (Object o : kill) {
//            map.remove(o);
//        }
    }   
    
    // use hashsets instead of arraysets 
    // TODO: rename to something more meaningful
//    public void overwriteWith2(Transformer t) {
//        // don't use map.putAll as it causes problems due to aliasing
//        // (it doesn't create new HashSets)
//        for (Object o : t.map.keySet()) {
//            map.put(o, new HashSet<TransformerEdge>(t.map.get(o)));
//        }
//    }

    // Is this >= t
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#subsumes(lg.analysis.paths.transformer.Transformer)
     */
    public boolean subsumes(final Transformer t) {
        return map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, final TLongHashSet edges) {
                final TLongHashSet tEdges = t.map.get(o);
                if (tEdges == null) {
                    long idEdge = TransformerEdgeFactory.newIdEdge(o);
                    return edges.contains(idEdge); // implicit edge o-->o lost?
                }
                else {
                    return tEdges.forEach(new TLongProcedure() {
                        public boolean execute(long e) {
                            return edges.contains(e); 
                        }
                    });
                }
            }
        });
//        Set<Object> keys = map.keySet();
//        if (keys.containsAll(t.map.keySet())) {
//            for (Object o : keys) {
//                Set<TransformerEdge> edges = map.get(o);
//                Set<TransformerEdge> tEdges = t.map.get(o);
//                if (tEdges == null) {
//                    if (!edges.contains(new TransformerEdge(idJumpFn, o))) {
//                        return false; // implicit edge o-->o lost
//                    }
//                }
//                else {
//                    if (!edges.containsAll(tEdges)) {
//                        return false;
//                    }
//                }
//            }
//            return true;
//        }
//        else {
//            return false;
//        }
    }
    
    // this - t
    // post: returns all edges in "this" that are not in "t"
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#differenceWith(lg.analysis.paths.transformer.Transformer)
     */
    public DeltaTransformer differenceWith(final Transformer t) {
        final DeltaTransformer difference = new DeltaTransformer();
        map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int d, TLongHashSet thisEdges) {
                final TLongHashSet tEdges = t.map.get(d);
                if (tEdges == null) {
                    difference.map.put(d, new TLongHashSet(thisEdges));
                }
                else {
                    final TLongHashSet edgesDiff = newSet(thisEdges.size()*2);
                    thisEdges.forEach(new TLongProcedure() {
                        public boolean execute(long e) {
                            if (!tEdges.contains(e)) {
                                edgesDiff.add(e);
                            }
                            return true;
                        }
                    });
                    if (!edgesDiff.isEmpty()) { // keep delta transformer sparse
                        difference.map.put(d, edgesDiff);
                    }
                }
                return true;
            }
        });
        return difference;
//        DeltaTransformer difference = new DeltaTransformer();
//        for (Object d : map.keySet()) {
//            Set<TransformerEdge> thisEdges = map.get(d);
//            Set<TransformerEdge> tEdges = t.map.get(d);
//            if (tEdges == null) {
//                difference.map.put(d, newSet(thisEdges));
//            }
//            else {
//                Set<TransformerEdge> edgesDiff = newSet();
//                for (TransformerEdge e : thisEdges) {
//                    if (!tEdges.contains(e)) {
//                        edgesDiff.add(e);
//                    }
//                }
//                if (!edgesDiff.isEmpty()) { // keep delta transformer sparse
//                    difference.map.put(d, edgesDiff);
//                }
//            }
//        }
//        return difference;
    }

    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#differenceWithInPlace(lg.analysis.paths.transformer.Transformer)
     */
    public void differenceWithInPlace(final Transformer t) {
        map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int d, TLongHashSet thisEdges) {
                TLongHashSet tEdges = t.map.get(d);
                if (tEdges != null) {
                    final TLongHashSet thisExclusiveEdges = (thisEdges instanceof TwoLevelSet) ? ((TwoLevelSet)thisEdges).getChild() : thisEdges;
                    tEdges.forEach(new TLongProcedure() {
                        public boolean execute(long e) {
                            thisExclusiveEdges.remove(e);  // note: t only ever grows
                            return true;
                        }
                    });
                    if (AtomicTransformer.COMPACT) {
                        thisExclusiveEdges.compact(); // tEdges should already be compacted
                    }
                    TLongHashSet newThisEdges = new TwoLevelSet(tEdges, thisExclusiveEdges);
                    map.put(d, newThisEdges);
                }
                return true;
            }
        });
//        for (Object d : map.keySet()) {
//            Set<TransformerEdge> tEdges = t.map.get(d);
//            if (tEdges != null) {
//                Set<TransformerEdge> thisEdges = map.get(d);
//                if (thisEdges instanceof TwoLevelSet) {
//                    TwoLevelSet<TransformerEdge> thisEdgesTwoLevel = (TwoLevelSet<TransformerEdge>)thisEdges;
//                    thisEdges = thisEdgesTwoLevel.getChild();
//                }
//                thisEdges.removeAll(tEdges); // note: t only ever grows
//                Set<TransformerEdge> newThisEdges = new TwoLevelSet<TransformerEdge>(tEdges, thisEdges);
//                map.put(d, newThisEdges);
//            }
//        }
    }   
    
    
//    public void differenceWithInPlace(final Transformer t) {
//        for (Object d : map.keySet()) {
//            Set<TransformerEdge> tEdges = t.map.get(d);
//            if (tEdges != null) {
//                Set<TransformerEdge> thisEdges = map.get(d);
//                if (thisEdges instanceof TwoLevelSet) {
//                    TwoLevelSet<TransformerEdge> thisEdgesTwoLevel = (TwoLevelSet<TransformerEdge>)thisEdges;
//                    thisEdges = thisEdgesTwoLevel.getChild();
//                }
//                thisEdges.removeAll(tEdges); // note: t only ever grows
//                Set<TransformerEdge> newThisEdges = new TwoLevelSet<TransformerEdge>(tEdges, thisEdges);
//                map.put(d, newThisEdges);
//            }
//        }
//    }   
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#addAll(lg.analysis.paths.transformer.Transformer)
     */
    public Transformer addAll(Transformer t) {
        final Transformer result = this;
        t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, TLongHashSet tEdges) {
                final TLongHashSet edges = result.map.get(o);
                if (edges == null) {
                    result.map.put(o, new TLongHashSet(tEdges));
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
        return result;
//        Transformer result = this;
//        for (Object o : t.map.keySet()) {
//            Set<TransformerEdge> edges = result.map.get(o);
//            if (edges == null) {
//                edges = newSet();
//                result.map.put(o, edges);
//            }
//            Set<TransformerEdge> tEdges = t.map.get(o);
//            edges.addAll(tEdges);
//        }
//        return result;
    }

    /*public void addAllModify(Transformer t) {
        for (Object o : t.map.keySet()) {
            Set<TransformerEdge> edges = map.get(o);
            Set<TransformerEdge> tEdges = t.map.get(o);
            if (edges == null) {
                edges = new HashSet<TransformerEdge>(tEdges);
//                map.put(o, edges);
            }
            else {
                edges = new HashSet<TransformerEdge>(edges);
                edges.addAll(tEdges);
            }
            map.put(o, newArraySet(edges));
        }
    }*/
    
/*    public DeltaTransformer addAllModifyReturnDelta(Transformer t) {
        DeltaTransformer delta = new DeltaTransformer();
        for (Object o : t.map.keySet()) {
            Set<TransformerEdge> edges = map.get(o);
            Set<TransformerEdge> deltaEdges = null;
            Set<TransformerEdge> tEdges = t.map.get(o);
            if (edges == null) {
                edges = new HashSet<TransformerEdge>(tEdges);
                deltaEdges = new HashSet<TransformerEdge>(tEdges);
                map.put(o, edges);
                delta.map.put(o, deltaEdges);
            }
            else {
                deltaEdges = new HashSet<TransformerEdge>();
                for (TransformerEdge e : tEdges) {
                    if (edges.add(e)) {
                        deltaEdges.add(e);
                    }
                }
                if (!deltaEdges.isEmpty()) {
                    delta.map.put(o, deltaEdges);
                }
            }
        }
        return delta;
    }*/

    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#addAllReturnDelta(lg.analysis.paths.transformer.Transformer, lg.analysis.paths.transformer.DeltaTransformer)
     */
    public Transformer addAllReturnDelta(Transformer t, final DeltaTransformer delta) {
        final Transformer result = this;
        t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, TLongHashSet tEdges) {
                final TLongHashSet edges = result.map.get(o);
                if (edges == null) {
                    result.map.put(o, new TLongHashSet(tEdges));
                    delta.map.put(o, new TLongHashSet(tEdges));
                }
                else {
                    final TLongHashSet deltaEdges = newSet(tEdges.size());
                    tEdges.forEach(new TLongProcedure() {
                        public boolean execute(long e) {
                            if (edges.add(e)) {
                                deltaEdges.add(e);
                            }
                            return true;
                        }
                    });
                    if (!deltaEdges.isEmpty()) {
                        delta.map.put(o, deltaEdges);
                    }
                }
                return true;
            }
        });
        return result;
//        Transformer result = this;//clone();
//        for (Object o : t.map.keySet()) {
//            Set<TransformerEdge> edges = result.map.get(o);
//            Set<TransformerEdge> deltaEdges = null;
//            Set<TransformerEdge> tEdges = t.map.get(o);
//            if (edges == null) {
//                result.map.put(o, newSet(tEdges));
//                delta.map.put(o, newSet(tEdges));
//            }
//            else {
//                deltaEdges = newSet(tEdges.size());
//                if (edges instanceof GoogleHashSet)
//                    ((GoogleHashSet)edges).ensureSizeForAdditional(tEdges.size());
//                for (TransformerEdge e : tEdges) {
//                    if (edges.add(e)) {
//                        deltaEdges.add(e);
//                    }
//                }
//                if (!deltaEdges.isEmpty()) {
//                    delta.map.put(o, deltaEdges);
//                }
//            }
//        }
//        return result;
    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#unionWith(lg.analysis.paths.transformer.Transformer)
     */
    public void unionWith(final Transformer t) {
        // Merge 'this' with 't'
        // Remember to make implicit edges explicit where necessary
        map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, final TLongHashSet edges) {
                TLongHashSet tEdges = t.map.get(o);
                if (tEdges == null) {
                    if (o != capitalLambda) {
                        // make implicit edge explicit
                        long idEdge = TransformerEdgeFactory.newIdEdge(o);
                        edges.add(idEdge);
                    }
                }
                else {
                    tEdges.forEach(new TLongProcedure() {
                        public boolean execute(long e) {
                            edges.add(e);
                            return true;
                        }
                    });
                }
                map.put(o, edges);
                return true;
            }
        });

        // Merge remaining edges in 't' with 'this' and make implicit edges
        // explicit where necessary
        t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, TLongHashSet tEdges) {
                TLongHashSet edges = map.get(o);
                if (edges == null) { // if edges != null, the unioning would have been done in the above for loop
                    // make implicit edge explicit unless o == A
                    edges = new TLongHashSet(tEdges);
                    if (o != capitalLambda) {
                        long idEdge = TransformerEdgeFactory.newIdEdge(o);
                        edges.add(idEdge);
                    }
                    map.put(o, edges);
                }
                return true;
            }
        });
        
//        compact(this);
        
//        for (Object o : map.keySet()) {
////          Set<TransformerEdge> edges = new HashSet<TransformerEdge>(map.get(o));
//            Set<TransformerEdge> edges = map.get(o);
////          if (edges instanceof ArraySet<?>) {
////              throw new RuntimeException("edges is of type ArraySet");
////          }
//            Set<TransformerEdge> tEdges = t.map.get(o);
//            if (tEdges == null) {
//                if (o != capitalLambda) {
//                    // make implicit edge explicit
////                  Logger.println("Generating explicit edge for " + o);
//                    edges.add(new TransformerEdge(idJumpFn, o));
//                }
//            }
//            else {
//                edges.addAll(tEdges);
//            }
////          map.put(o, newArraySet(edges));
//            map.put(o, edges);
//        }
//        // Merge remaining edges in 't' with 'this' and make implicit edges
//        // explicit where necessary
//        for (Object o : t.map.keySet()) {
////          if (!map.containsKey(o)) {
//                Set<TransformerEdge> edges = map.get(o);
//                if (edges == null) { // if edges != null, the unioning would have been done in the above for loop
//                    // make implicit edge explicit unless o == A
//                    edges = newSet(t.map.get(o));
//                    if (o != capitalLambda) {
////                      Logger.println("Generating explicit edge for " + o);
//                        edges.add(new TransformerEdge(idJumpFn, o));
//                    }
//                    map.put(o, edges);
////                  map.put(o, newArraySet(edges));
//                }
////              else {
////                  edges = new HashSet<TransformerEdge>(edges);
////              }
////              edges.addAll(tEdges);
//                
////          }
//        }
        
//      cleanup(this);
    }

//    public Transformer composeWithExperimental(Transformer t) {
//        if (this instanceof IdentityTransformer || map.isEmpty()) {
//            return newInstance(t);  // can lead to aliasing problems if not careful in other parts of the implementation
//        }
//        else if (t instanceof IdentityTransformer || t.map.isEmpty()) {
//            return newInstance(this);
//        }
//        else {
//            Transformer closure = newInstance();
//            for (Object o : map.keySet()) {
//                Set<TransformerEdge> edges = map.get(o);
//                Set<TransformerEdge> newEdges = newSetFast(edges);  // use *2 to anticipate doubling, speeds up composition
//                Set<TransformerEdge> kill = newSet();
//                Set<TransformerEdge> gen = newSet(edges.size());
//                // transitive closure
//                for (TransformerEdge te : edges) {
//                    if (te != killEdge) {
//                        // o --> d
//                        Object d = te.getDest();
//                        Set<TransformerEdge> dEdges = t.map.get(d);
//                        if (dEdges != null) {
//                            if (dEdges.isEmpty()) {
//                                throw new RuntimeException("dEdges is not null but empty!");
//                            }
//                            kill.add(te);
//                            for (TransformerEdge te2 : dEdges) {
//                                if (te2 == killEdge) {
//                                    gen.add(te2);
//                                }
//                                else {
//                                    TransformerEdge te3 = new TransformerEdge(JumpFunctionFactory.composeJumpFunctions(te.getJumpFunction(),te2.getJumpFunction()),te2.getDest());
//                                    gen.add(te3);
//                                }
//                            }
//                        }
//                    }
//                }
//                kill.removeAll(gen);
////                gen.removeAll(newEdges);
//                newEdges.removeAll(kill);
//                newEdges.addAll(gen);
//                closure.map.put(o, newEdges);
//            }
//            // take account of implicit edges in 'this' transformer. 
//            for (Object o : t.map.keySet()) {
//                if (o == capitalLambda) {
//                    // implicit A --> A edge in 'this'. Pass on accesses.
//                    Set<TransformerEdge> transEdges = closure.map.get(o);
//                    if (transEdges == null) {
//                        transEdges = newSet();
//                        closure.map.put(o, transEdges);
//                    }
//                    Set<TransformerEdge> accesses = t.map.get(o);
//                    transEdges.addAll(accesses);
//                }
//                else {
//                    Set<TransformerEdge> edges = map.get(o);
//                    if (edges == null) {
//                        // implicit edge o --> o exists in 'this'
//                        // or 'unknownSet' so we pass edges in t on
//                        Set<TransformerEdge> transEdges = closure.map.get(o);
//                        if (transEdges == null) { // transEdges should always be null
//                            transEdges = newSet();
//                            closure.map.put(o, transEdges);
//                        }
//                        Set<TransformerEdge> oEdges = t.map.get(o);
//                        transEdges.addAll(oEdges);
//                    }
//                }
//            }
//            
//            cleanup(closure);
//            
//            return closure;
//        }
//    }   
    
    // (t o this)(e) = t(this(e)) (i.e. "this" is below and "t" is above)
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#composeWith(lg.analysis.paths.transformer.Transformer)
     */
    public Transformer composeWith(final Transformer t) {
        if (this instanceof IdentityTransformer || map.isEmpty()) {
            return newInstance(t);  // can lead to aliasing problems if not careful in other parts of the implementation
        }
        else if (t instanceof IdentityTransformer || t.map.isEmpty()) {
            return newInstance(this);
        }
        else {
            final Transformer closure = newInstance();
            map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
                public boolean execute(int o, TLongHashSet edges) {
                    final TLongHashSet newEdges = newSet(edges.size()*2);  // use *2 to anticipate doubling, speeds up composition
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
                                    newEdges.ensureCapacity(dEdges.size());
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
            // take account of implicit edges in 'this' transformer.
            t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
                public boolean execute(int o, TLongHashSet tEdges) {
                    TLongHashSet edges = map.get(o);
                    if (o == capitalLambda || edges == null) {
                        // implicit A --> A or o --> o edge in 'this'. Pass on edges
                        final TLongHashSet transEdges = closure.map.get(o);
                        if (transEdges == null) {
                            closure.map.put(o, new TLongHashSet(tEdges));
                        }
                        else {
                            transEdges.ensureCapacity(tEdges.size());
                            tEdges.forEach(new TLongProcedure() {
                                public boolean execute(long e) {
                                    transEdges.add(e);
                                    return true;
                                }
                            });
                        }
                    }
                    return true;
                }
            });
            cleanup(closure);

            return closure;
//            Transformer closure = newInstance();
//            for (Object o : map.keySet()) {
//                Set<TransformerEdge> edges = map.get(o);
//                Set<TransformerEdge> newEdges = newSet(edges.size()*2);  // use *2 to anticipate doubling, speeds up composition
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
//            // take account of implicit edges in 'this' transformer. 
//            for (Object o : t.map.keySet()) {
//                if (o == capitalLambda) {
//                    // implicit A --> A edge in 'this'. Pass on accesses.
//                    Set<TransformerEdge> transEdges = closure.map.get(o);
//                    if (transEdges == null) {
//                        transEdges = newSet();
//                        closure.map.put(o, transEdges);
//                    }
//                    Set<TransformerEdge> accesses = t.map.get(o);
//                    transEdges.addAll(accesses);
//                }
//                else {
//                    Set<TransformerEdge> edges = map.get(o);
//                    if (edges == null) {
//                        // implicit edge o --> o exists in 'this'
//                        // or 'unknownSet' so we pass edges in t on
//                        Set<TransformerEdge> transEdges = closure.map.get(o);
//                        if (transEdges == null) { // transEdges should always be null
//                            transEdges = newSet();
//                            closure.map.put(o, transEdges);
//                        }
//                        Set<TransformerEdge> oEdges = t.map.get(o);
//                        transEdges.addAll(oEdges);
//                    }
//                }
//            }
//            
//            cleanup(closure);
//            
//            // use compact ArraySet for storage
////          for (Object o : closure.map.keySet()) {
////              closure.map.put(o, newArraySet(closure.map.get(o)));
////          }
//            
//            return closure;
        }
    }

//    public Transformer composeWithExp(final Transformer t) {
//        if (this instanceof IdentityTransformer || map.isEmpty()) {
//            return newInstance(t);  // can lead to aliasing problems if not careful in other parts of the implementation
//        }
//        else if (t instanceof IdentityTransformer || t.map.isEmpty()) {
//            return newInstance(this);
//        }
//        else {
//            final Transformer closure = newInstance();
//            map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
//                public boolean execute(int o, TLongHashSet edges) {
//                    final TLongHashSet newEdges = new TLongHashSet(edges);
//                    // transitive closure
//                    final TLongHashSet kill = newSet();
//                    final TLongHashSet gen = newSet();
//                    edges.forEach(new TLongProcedure() {
//                        public boolean execute(final long te) {
//                            if (te != killEdge) {
//                                // o --> d
//                                int d = TransformerEdgeFactory.getD(te);
//                                TLongHashSet dEdges = t.map.get(d);
//                                if (dEdges != null) {
//                                    kill.add(te);
//                                    dEdges.forEach(new TLongProcedure() {
//                                        public boolean execute(long te2) {
//                                            long composed = TransformerEdgeFactory.composeEdges(te, te2);
//                                            gen.add(composed);
//                                            return true;
//                                        }
//                                    });
//                                }
//                            }
//                            return true;
//                        }
//                    });
//                    gen.forEach(new TLongProcedure() {
//                        public boolean execute(long e) {
//                            kill.remove(e);
//                            return true;
//                        }
//                    });
//                    kill.forEach(new TLongProcedure() {
//                        public boolean execute(long e) {
//                            newEdges.remove(e);
//                            return true;
//                        }
//                    });
//                    gen.forEach(new TLongProcedure() {
//                        public boolean execute(long e) {
//                            newEdges.add(e);
//                            return true;
//                        }
//                    });
//                    closure.map.put(o, newEdges);
//                    return true;
//                }
//            });
//            // take account of implicit edges in 'this' transformer.
//            t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
//                public boolean execute(int o, TLongHashSet tEdges) {
//                    TLongHashSet edges = map.get(o);
//                    if (o == capitalLambda || edges == null) {
//                        // implicit A --> A or o --> o edge in 'this'. Pass on edges
//                        final TLongHashSet transEdges = closure.map.get(o);
//                        if (transEdges == null) {
//                            closure.map.put(o, new TLongHashSet(tEdges));
//                        }
//                        else {
//                            tEdges.forEach(new TLongProcedure() {
//                                public boolean execute(long e) {
//                                    transEdges.add(e);
//                                    return true;
//                                }
//                            });
//                        }
//                    }
//                    return true;
//                }
//            });
//            cleanup(closure);
//
////            compact(closure);
//            
//            return closure;
////            Transformer closure = newInstance();
////            for (Object o : map.keySet()) {
////                Set<TransformerEdge> edges = map.get(o);
////                Set<TransformerEdge> newEdges = newSet(edges.size()*2);  // use *2 to anticipate doubling, speeds up composition
////                // transitive closure
////                for (TransformerEdge te : edges) {
////                    if (te == killEdge) {
////                        // o --> e goes through (note we have implicit e --> e)
////                        newEdges.add(te);
////                    }
////                    else {
////                        // o --> d
////                        Object d = te.getDest();
////                        Set<TransformerEdge> dEdges = t.map.get(d);
////                        if (dEdges == null) {
////                            // implicit edge in t
////                            newEdges.add(te);
////                        }
////                        else {
////                            for (TransformerEdge te2 : dEdges) {
////                                if (te2 == killEdge) {
////                                    newEdges.add(te2);
////                                }
////                                else {
////                                    newEdges.add(new TransformerEdge(JumpFunctionFactory.composeJumpFunctions(te.getJumpFunction(),te2.getJumpFunction()),te2.getDest()));
////                                }
////                            }
////                        }
////                    }
////                }
////                closure.map.put(o, newEdges);
////            }
////            // take account of implicit edges in 'this' transformer. 
////            for (Object o : t.map.keySet()) {
////                if (o == capitalLambda) {
////                    // implicit A --> A edge in 'this'. Pass on accesses.
////                    Set<TransformerEdge> transEdges = closure.map.get(o);
////                    if (transEdges == null) {
////                        transEdges = newSet();
////                        closure.map.put(o, transEdges);
////                    }
////                    Set<TransformerEdge> accesses = t.map.get(o);
////                    transEdges.addAll(accesses);
////                }
////                else {
////                    Set<TransformerEdge> edges = map.get(o);
////                    if (edges == null) {
////                        // implicit edge o --> o exists in 'this'
////                        // or 'unknownSet' so we pass edges in t on
////                        Set<TransformerEdge> transEdges = closure.map.get(o);
////                        if (transEdges == null) { // transEdges should always be null
////                            transEdges = newSet();
////                            closure.map.put(o, transEdges);
////                        }
////                        Set<TransformerEdge> oEdges = t.map.get(o);
////                        transEdges.addAll(oEdges);
////                    }
////                }
////            }
////            
////            cleanup(closure);
////            
////            // use compact ArraySet for storage
//////          for (Object o : closure.map.keySet()) {
//////              closure.map.put(o, newArraySet(closure.map.get(o)));
//////          }
////            
////            return closure;
//        }
//    }
    
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#compact()
     */
    public void compact() {
        compact(this);
    }
    
    protected void compact(Transformer t) {
        if (AtomicTransformer.COMPACT) {
//            System.out.println("Compacting!");
            t.map.forEachValue(new TObjectProcedure<TLongHashSet>() {
                public boolean execute(TLongHashSet v) {
                    v.compact();
                    return true;
                }
            });
        }
    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#cleanup()
     */
    public void cleanup() {
        cleanup(this);
    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#cleanup2(lg.analysis.paths.transformer.Transformer)
     */
    public void cleanup2(final Transformer t) {
        t.map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, TLongHashSet edges) {
                if (edges.size() > 1) {
                    edges.remove(killEdge);
                }
                if (edges.size() == 1) {
                    if (o == capitalLambda) {
                        edges.remove(killEdge);
                    }
                    else {
                        long idEdge = TransformerEdgeFactory.newIdEdge(o);
                        edges.remove(idEdge);
                    }
                }
                if (edges.isEmpty()) {
                    t.map.remove(o);
                }
                return true;
            }
        });
//        Set<Object> kill = new HashSet<Object>();
//        for (Object o : t.map.keySet()) {
//            Set<TransformerEdge> edges = t.map.get(o);
//            if (edges.size() > 1) {
//                if (edges.remove(killEdge)) {
////                Logger.println("Removing kill edge for " + o);
//                }
//            }
//            if (edges.size() == 1) {
//                for (TransformerEdge te : edges) {
//                    if (te.getJumpFunction() == idJumpFn && te.getDest() == o) {
////                    Logger.println("Removing id edge for " + o);
//                        kill.add(o);
//                    }
//                    else if (o == capitalLambda && te == killEdge) {
////                    Logger.println("Removing kill edge for " + o);
//                        kill.add(o);
//                    }
//                }
//            }
//            else if (edges.size() == 0) {
//                kill.add(o);
//            }
////          t.map.put(o, newArraySet(edges));
//        }
//        for (Object o : kill) {
//            t.map.remove(o);
//        }
    }

    
    // NOT SURE IF THIS IS SOUND
    // clean up -->e edges and redundant x --> x transformer edges
    // This is required to keep the transformer as sparse as possible
    protected void cleanup(Transformer t) {
        /*Set<Object> kill = new HashSet<Object>();
        for (Object o : t.map.keySet()) {
            Set<TransformerEdge> edges = t.map.get(o);
            if (edges.size() > 1) {
                if (edges.remove(killEdge)) {
//                  Logger.println("Removing kill edge for " + o);
                }
            }
            if (edges.size() == 1) {
                for (TransformerEdge te : edges) {
                    if (te.getJumpFunction() == idJumpFn && te.getDest() == o) {
//                      Logger.println("Removing id edge for " + o);
                        kill.add(o);
                    }
                    else if (o == capitalLambda && te == killEdge) {
//                      Logger.println("Removing kill edge for " + o);
                        kill.add(o);
                    }
                }
            }
            else if (edges.size() == 0) {
                kill.add(o);
            }
        }
        for (Object o : kill) {
            t.map.remove(o);
        }*/
    }

    
    
//  protected long composeJumpFunctions(long f1, long f2) {
//      if (f1 == idJumpFn) {
//          return f2;
//      }
//      else if (f2 == idJumpFn) {
//          return f1;
//      }
//      else if (f1 instanceof EdgeJumpFunction) {
//          EdgeJumpFunction e1 = (EdgeJumpFunction)f1;
//          if (f2 instanceof LoadJumpFunction) {
//              LoadJumpFunction l2 = (LoadJumpFunction)f2;
//              return new EdgeJumpFunction(l2.getN(), e1.getDst(), e1.isWrite());
//          }
//          else if (f2 == storeJumpFn) {
//              return new EdgeJumpFunction(startState, e1.getDst(), e1.isWrite());
//          }
//      }
//      else if (f1 instanceof LoadJumpFunction && f2 == storeJumpFn) {
//          return f2;
//      }
//      else if (f1 == storeJumpFn && f2 instanceof LoadJumpFunction) {
//          return f2;
//      }
//      else if (f1 instanceof LoadJumpFunction && f2 instanceof LoadJumpFunction) {
//          return f2;
//      }
//      else if (f1 == storeJumpFn && f2 == storeJumpFn) {
//          return f2;
//      }
//      throw new RuntimeException("Unknown pair of jump functions: f1 = " + f1.toString() + ", f2 = " + f2.toString());
//  }

    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#clone()
     */
    public Transformer clone() {
        return new Transformer(this);
    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#hashCode()
     */
    public int hashCode() {
        return map.hashCode();
    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        else if (other == null) {
            return false;
        }
        /*else if (o.getClass() != getClass()) {
            return false;
        }*/
        else {
            if (other instanceof Transformer) {
                Transformer t = (Transformer) other;
//              if (map.keySet().equals(t.map.keySet())) {
//                  for (Object o : map.keySet()) {
//                          Set<TransformerEdge> edges = map.get(o);
//                      Set<TransformerEdge> tEdges = t.map.get(o);
//                      if (edges == null || tEdges == null) {
//                          if (edges != tEdges) {
////                                if (AtomicTransformer.DEBUG) {
////                                    Logger.println("t or e is null");
////                                }
//                              return false;
//                          }
//                      }
//                      else {
//                          // using HashSets are much faster
//                          if (!edges.equals(tEdges)) {
////                                if (AtomicTransformer.DEBUG) {
////                                    Logger.println("e: " + edges.size() + " t: " + tEdges.size());
////                                    Logger.println("e: " + edges);
////                                    Logger.println("t: " + tEdges);
////                                }
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
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#toString()
     */
    @Override
    public String toString() {
        final StringBuilder s = new StringBuilder("{");
        map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            boolean first = true;
            public boolean execute(int o, TLongHashSet edges) {
                if (!first) {
                    s.append("; ");
                }
                String oStr = SymbolNumberer.getObject(o).toString();
                s.append(oStr + "=[");
                edges.forEach(new TLongProcedure() {
                    boolean first = true;
                    public boolean execute(long e) {
                        if (!first) {
                            s.append(", ");
                        }
                        s.append(TransformerEdgeFactory.toString(e));
                        first = false;
                        return true;
                    }
                });
                s.append("]");
                first = false;
                return true;
            }
        });
        s.append("}");
        return s.toString();
    }

    // returns a copy of this transformer but without any method local vars
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#removeMethodLocalVars()
     */
    public ITransformer removeMethodLocalVars() {
        final Transformer t = newInstance();
        map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int d, TLongHashSet edges) {
                Object o = SymbolNumberer.getObject(d);
                if (o instanceof Local) {
                    // skip
                }
                else {
                    final TLongHashSet edgesToKeep = newSet(edges.size()*2);
                    edges.forEach(new TLongProcedure() {
                        public boolean execute(long te) {
                            if (te == killEdge) {
                                edgesToKeep.add(te);
                            }
                            else {
                                long d2 = TransformerEdgeFactory.getD(te);
                                Object o2 = SymbolNumberer.getObject(d2);
                                if (!(o2 instanceof Local)) {
                                    edgesToKeep.add(te);
                                }
                            }
                            return true;
                        }
                    });
                    if (!edgesToKeep.isEmpty()) {
                        t.map.put(d, edgesToKeep);
                    }
                }
                return true;
            }
        });
        return t;
//        Transformer t = newInstance();
//        for (Object o : map.keySet()) {
//            if (o instanceof Local) {
//                // skip
//                continue;
//            }
//            else {
//                Set<TransformerEdge> edgesToKeep = newSet();
//                for (TransformerEdge te : map.get(o)) {
//                    if (te == killEdge) {
//                        edgesToKeep.add(te);
//                    }
//                    else if (!(te.getDest() instanceof Local)) {
//                        edgesToKeep.add(te);
//                    }
//                }
//                if (!edgesToKeep.isEmpty()) {
//                    t.map.put(o, edgesToKeep);
//                }
//            }
//        }
//        //cleanup(t);
//        return t;
    }
    
//    public void removeParamVarsAndRetVar() {
//        Set<Object> kill = new HashSet<Object>();
//        for (Object o : map.keySet()) {
//            if (o == thisVar || o == retVar || o instanceof ParameterVariable) {
//                kill.add(o);
//            }
//        }
//        for (Object o : kill) 
//            map.remove(o);
//    }

    // renames params in transformer to args, wrt the given mapping
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#calleeToCallerContext(gnu.trove.map.hash.TIntIntHashMap)
     */
    public ITransformer calleeToCallerContext(final TIntIntHashMap paramsToArgs) {
        final Transformer t = newInstance();
        map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int o, TLongHashSet edges) {
                if (o == retVar && !paramsToArgs.containsKey(o)) {
                    // return value is not used by caller so ignore edges $ret --> *
                    // continue;
                }
                else {
                    final TLongHashSet newEdges = newSet(edges.size()*2);
                    edges.forEach(new TLongProcedure() {
                        public boolean execute(long te) {
                            if (TransformerEdgeFactory.isKill(te)) {
                                newEdges.add(te);
                            }
                            else {
                                int d = TransformerEdgeFactory.getD(te);
                                Object o = null;
                                try {
                                    o = SymbolNumberer.getObject(d);
                                }
                                catch (ArrayIndexOutOfBoundsException e) {
                                    Logger.println(TransformerEdgeFactory.toString(te));
                                    System.exit(-1);
                                    ProfilerSupport.waitForKeyPress();
                                }
                                if (o instanceof ParameterVariable) {
                                    int arg = paramsToArgs.get(d);
                                    if (arg == 0) {
                                        newEdges.add(killEdge);
                                    }
                                    else {
                                        newEdges.add(TransformerEdgeFactory.updateD(te, arg));
                                    }
                                }
                                else {
                                    newEdges.add(te);
                                }
                            }
                            return true;
                        }
                    });
                    // rename $ret to actual return variable
                    if (o == retVar) {
                        o = paramsToArgs.get(o);
                    }
                    t.map.put(o, newEdges);
                }
                return true;
            }
        });
//        for (Object o : map.keySet()) {
//            if (o == retVar && paramsToArgs.get(o) == null) {
//                // return value is not used by caller so ignore edges $ret --> *
//                continue;
//            }
//            Set<TransformerEdge> newEdges = newSet();
//            for (TransformerEdge te : map.get(o)) {
//                Object d = te.getDest();
//                if (d instanceof ParameterVariable || d == thisVar) {
//                    Local arg = paramsToArgs.get(d);
//                    if (arg == null) {
//                        newEdges.add(killEdge);
//                    }
//                    else {
//                        newEdges.add(new TransformerEdge(te.getJumpFunction(), arg));
//                    }
//                }
//                else {
//                    newEdges.add(te);
//                }
//            }
//            // rename $ret to actual return variable
//            if (o == retVar) {
//                o = paramsToArgs.get(o);
//            }
//            t.map.put(o, newEdges);
//        }
//      cleanup(t);
        
        /*Local actualRetVar = paramsToArgs.get(retVar);
        if (actualRetVar != null) {
            // insert actualRetVar --> e, if no mapping for it exists already
            Set<TransformerEdge> edges = t.map.get(actualRetVar);
            if (edges == null) {
                edges = new HashSet<TransformerEdge>(4);
                edges.add(killEdge);
                t.map.put(actualRetVar, edges);
            }
        }*/
        return t;
    }
    
//    public int edgeCount() {
//        int count = 0;
//        for (Set<TransformerEdge> edges : map.values()) {
//            count += edges.size();
//        }
//        return count;
//    }
    
//    public void results() {
//        try {
//            int count = 0;
//            PrintWriter p = new PrintWriter("results.txt");
//            for (Object o : map.keySet()) {
//                Set<TransformerEdge> edges = map.get(o);
//                p.println(o.toString() + ": " + edges.size());
//                count += edges.size();
//            }
//            p.println(count);
//            p.flush();
//            p.close();
//        }
//        catch(FileNotFoundException e) {
//            throw new RuntimeException(e);
//        }
//    }
    
    /*
       example transformer in dot
       digraph G {
            ranksep="5in"
            rankdir=BT;
            node [shape=record];
            incoming [label = "<a> a |<b> b |<c> c |<d> d", rank=1, width="4in"];
            outgoing [label = "<a> a |<b> b |<c> c |<d> d", rank=2, width="4in"];
            outgoing -> incoming [weight=10000,style=invis];
            incoming:a -> outgoing:b ;
            incoming:a -> outgoing:c [label="L(1,2)"];
            incoming:a -> outgoing:c [label="L(1,3)"];
            incoming:b -> outgoing:c [label="L(0,2)"];
       }
     * 
     */
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#outputDot(soot.SootMethod, boolean, java.lang.String)
     */
    public void outputDot(SootMethod m, boolean aggregate, String filename) {
//      System.out.println("---");
//      System.out.println(m.toString());
//      System.out.println(this);
//        try {
//            PrintWriter p = new PrintWriter(filename);
//            p.println("digraph m" + m.getNumber() + " {");
//            p.println("\tlabel=\"" + m.toString() + "\";");
//            p.println("\tlabelloc=t;");
//            p.println("\tranksep=\"5in\"");
//            p.println("\trankdir=BT;");
//            p.println("\tnode [shape=record];");
//            
//            // determine the set D
//            final TIntHashSet d = new TIntHashSet();
//            map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
//                public boolean execute(int o, TLongHashSet edges) {
//                    d.add(o);
//                    edges.forEach(new TLongProcedure() {
//                        public boolean execute(long e) {
//                            if (e != killEdge) {
//                                int d2 = TransformerEdgeFactory.getD(e);
//                                d.add(d2);
//                            }
//                            return true;
//                        }
//                    });
//                    return true;
//                }
//            });
//            
//            int dSize = d.size();
//            
//            String label = "<access> &#x039B; | <kill> &#x2205;";
//            for (Object o : d) {
//                
//                if (o == capitalLambda) {
//                    continue;
//                }
//                
//                label += " | ";
//                
//                if (o instanceof SootField) {
//                    SootField f = (SootField)o;
//                    label += ("<f" + f.getNumber() +"> ." + f.getName()/* + " (" + f.getType() + ")"*/);
//                }
//                else if (o instanceof SootClass) {
//                    SootClass c = (SootClass)o;
//                    label += ("<class" + c.getNumber() + "> " + c.getName());
//                }
//                else if (o instanceof Local) {
//                    Local l = (Local)o;
//                    label += ("<l" + l.getNumber() +"> " + l.getName());
//                }
//                else if (o == arrElem) {
//                    label += ("<arr> []");
//                }
//                else if (o == retVar) {
//                    label += ("<r> $r");
//                }
//                else if (o == thisVar) {
//                    label += ("<this> @this");
//                }
//                else if (o instanceof ParameterVariable) {
//                    ParameterVariable param = (ParameterVariable)o;
//                    label += ("<p" + param.getNum() + "> @param" + param.getNum());
//                }
//                else {
//                    throw new RuntimeException("Unsupported symbol: " + o);
//                }
//            }
//            
//            p.println("\tincoming [label=\"" + label + "\",width=\"" + dSize + "in\"];");
//            p.println("\toutgoing [label=\"" + label + "\",width=\"" + dSize + "in\"];");
//            p.println("\toutgoing -> incoming [weight=10000,style=invis];");
//            
//            for (Object o1 : d) {
//                Set<TransformerEdge> edges = map.get(o1);
//                String colour = o1 == capitalLambda ? "green" : "black";
//                if (edges != null) {
//                    String s1 = determineSymbolId(o1);
//                    if (aggregate) {
//                        Map<Object, Integer> aggregateCounts = new HashMap<Object, Integer>();
//                        for (TransformerEdge te : edges) {
////                        System.out.println(te);
//                            Object o2 = te.getDest();
//                            Integer oldAggregateCount = aggregateCounts.get(o2);
//                            int newAggregateCount = (oldAggregateCount == null) ? 1 : oldAggregateCount.intValue() + 1;
//                            aggregateCounts.put(o2, newAggregateCount);
//                        }
//                        for (Object o2 : aggregateCounts.keySet()) {
//                            String s2 = determineSymbolId(o2);
//                            p.println("\tincoming:" + s1 + " -> outgoing:" + s2 + " [label=\"" + aggregateCounts.get(o2) + "\"fontcolor=\"" + colour + "\",color=\"" + colour + "\"];");
//                        }
//                    }
//                    else {
//                        for (TransformerEdge te : edges) {
//    //                      System.out.println(te);
//                            Object o2 = te.getDest();
//                            String s2 = determineSymbolId(o2);
//                            p.println("\tincoming:" + s1 + " -> outgoing:" + s2 + " [label=\"" + edgeLabel(te) + "\"fontcolor=\"" + colour + "\",color=\"" + colour + "\"];");
//                        }
//                    }
//                }
//            }
//            
//            p.println("}");
//            p.flush();
//            p.close();
//            for (Object o : map.keySet()) {
//                d.add(o);
//                Set<TransformerEdge> edges = map.get(o);
//                for (TransformerEdge e : edges) {
//                    if (e == killEdge) { continue; }
//                    d.add(e.getDest());
//                }
//            }
//            int dSize = d.size();
//            
//            String label = "<access> &#x039B; | <kill> &#x2205;";
//            for (Object o : d) {
//                
//                if (o == capitalLambda) {
//                    continue;
//                }
//                
//                label += " | ";
//                
//                if (o instanceof SootField) {
//                    SootField f = (SootField)o;
//                    label += ("<f" + f.getNumber() +"> ." + f.getName()/* + " (" + f.getType() + ")"*/);
//                }
//                else if (o instanceof SootClass) {
//                    SootClass c = (SootClass)o;
//                    label += ("<class" + c.getNumber() + "> " + c.getName());
//                }
//                else if (o instanceof Local) {
//                    Local l = (Local)o;
//                    label += ("<l" + l.getNumber() +"> " + l.getName());
//                }
//                else if (o == arrElem) {
//                    label += ("<arr> []");
//                }
//                else if (o == retVar) {
//                    label += ("<r> $r");
//                }
//                else if (o == thisVar) {
//                    label += ("<this> @this");
//                }
//                else if (o instanceof ParameterVariable) {
//                    ParameterVariable param = (ParameterVariable)o;
//                    label += ("<p" + param.getNum() + "> @param" + param.getNum());
//                }
//                else {
//                    throw new RuntimeException("Unsupported symbol: " + o);
//                }
//            }
//            
//            p.println("\tincoming [label=\"" + label + "\",width=\"" + dSize + "in\"];");
//            p.println("\toutgoing [label=\"" + label + "\",width=\"" + dSize + "in\"];");
//            p.println("\toutgoing -> incoming [weight=10000,style=invis];");
//            
//            for (Object o1 : d) {
//                Set<TransformerEdge> edges = map.get(o1);
//                String colour = o1 == capitalLambda ? "green" : "black";
//                if (edges != null) {
//                    String s1 = determineSymbolId(o1);
//                    if (aggregate) {
//                        Map<Object, Integer> aggregateCounts = new HashMap<Object, Integer>();
//                        for (TransformerEdge te : edges) {
////                        System.out.println(te);
//                            Object o2 = te.getDest();
//                            Integer oldAggregateCount = aggregateCounts.get(o2);
//                            int newAggregateCount = (oldAggregateCount == null) ? 1 : oldAggregateCount.intValue() + 1;
//                            aggregateCounts.put(o2, newAggregateCount);
//                        }
//                        for (Object o2 : aggregateCounts.keySet()) {
//                            String s2 = determineSymbolId(o2);
//                            p.println("\tincoming:" + s1 + " -> outgoing:" + s2 + " [label=\"" + aggregateCounts.get(o2) + "\"fontcolor=\"" + colour + "\",color=\"" + colour + "\"];");
//                        }
//                    }
//                    else {
//                        for (TransformerEdge te : edges) {
//    //                      System.out.println(te);
//                            Object o2 = te.getDest();
//                            String s2 = determineSymbolId(o2);
//                            p.println("\tincoming:" + s1 + " -> outgoing:" + s2 + " [label=\"" + edgeLabel(te) + "\"fontcolor=\"" + colour + "\",color=\"" + colour + "\"];");
//                        }
//                    }
//                }
//            }
//            
//            p.println("}");
//            p.flush();
//            p.close();
        }
//        catch(FileNotFoundException e) {
//            throw new RuntimeException(e);
//        }
//    }
    
//    private String edgeLabel(TransformerEdge te) {
//        long fn = te.getJumpFunction();
//        if (JumpFunctionFactory.isLoadFunction(fn)) {
//            State src = JumpFunctionFactory.getSrcState(fn);
//            return "L("+src.getNumber()+")";
//        }
//        else if (fn == storeJumpFn) {
//            return "S";
//        }
//        else if (fn == idJumpFn) {
//            return "";
//        }
//        else {
//            State src = JumpFunctionFactory.getSrcState(fn);
//            State dst = JumpFunctionFactory.getDstState(fn);
//            return "(" + (src == null ? 0 : src.getNumber())  + "," + dst.getNumber() + ")";
//        }
//    }
//    
//    private String determineSymbolId(Object o) {
//        if (o == capitalLambda) {
//            return "access";
//        }
//        else if (o == null) {
//            return "kill";
//        }
//        else if (o instanceof SootField) {
//            SootField f = (SootField)o;
//            return "f" + f.getNumber();
//        }
//        else if (o instanceof SootClass) {
//            SootClass c = (SootClass)o;
//            return "class" + c.getNumber();
//        }
//        else if (o instanceof Local) {
//            Local l = (Local)o;
//            return "l" + l.getNumber();
//        }
//        else if (o == arrElem) {
//            return "arr";
//        }
//        else if (o == retVar) {
//            return "r";
//        }
//        else if (o == thisVar) {
//            return "this";
//        }
//        else if (o instanceof ParameterVariable) {
//            ParameterVariable param = (ParameterVariable)o;
//            return "p" + param.getNum();
//        }
//        else {
//            throw new RuntimeException("Unknown symbol " + o);
//        }
//    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#getAccessesNfa()
     */
    public Automaton getAccessesNfa() {
        final Automaton nfa = new Automaton(startState);
        TLongHashSet accesses = map.get(capitalLambda);
        if (accesses != null) {
            accesses.forEach(new TLongProcedure() {
                public boolean execute(long te) {
                    // convert transformer edge into automaton transition
                    if (TransformerEdgeFactory.isKill(te)) {
                        return true; // skip kill edges (will be present if compacting summaries)
                    }
                    State src = TransformerEdgeFactory.getSrcState(te);
                    State dst = TransformerEdgeFactory.getDstState(te);
                    int d = TransformerEdgeFactory.getD(te);
                    Object lbl = SymbolNumberer.getObject(d);
                    if (lbl != null) {
                        boolean write = TransformerEdgeFactory.isWrite(te);
                        nfa.addTransition(new Transition(src, dst, lbl, write));
                    }
                    return true;
                }
            });
            
//            for (TransformerEdge te : accesses) {
//                long fn = te.getJumpFunction();
//                // convert transformer edge into automaton transition
//                State src = JumpFunctionFactory.getSrcState(fn);
//                State dst = JumpFunctionFactory.getDstState(fn);
//                Object lbl = te.getDest();
//                if (lbl != null) {
//                    boolean write = JumpFunctionFactory.isWrite(fn);
//                    nfa.addTransition(new Transition(src, dst, lbl, write));
//                }
//            }
        }
        return nfa;
    }

    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#removeDeadEdges()
     */
    public ITransformer removeDeadEdges() {
        if (!AtomicTransformer.COMPACT_SUMMARIES) {
            cleanup2(this);  // breaks two-level set implementation
        }
        Automaton nfa = getAccessesNfa();
        final Set<State> reachables = nfa.cleanup();

        TLongHashSet accessEdges = newSet(nfa.size());
        for (Set<Transition> tns : nfa.getTransitions()) {
            for (Transition tn : tns) {
                accessEdges.add(TransformerEdgeFactory.newAccessEdge(tn.getSrc(), tn.getDst(), tn.isWrite(), (Numberable)tn.getLbl()));
            }
        }
            
        final Transformer result = newInstance();
        result.map.put(capitalLambda, accessEdges);

        map.forEachEntry(new TIntObjectProcedure<TLongHashSet>() {
            public boolean execute(int d, TLongHashSet dEdges) {
                if (d != capitalLambda) {
                    final TLongHashSet newEdges = newSet(dEdges.size());
                    dEdges.forEach(new TLongProcedure() {
                        public boolean execute(long dEdge) {
                            if (!TransformerEdgeFactory.isId(dEdge) && !TransformerEdgeFactory.isKill(dEdge)) { // i.e. store or load edge (accesses already dealt with above)
                                State n = TransformerEdgeFactory.getSrcState(dEdge); // store edge will always go through because src state is nfa 'start' which is reachable (but don't have a way of uniquely identifying loads as there is no need elsewhere)
                                if (reachables.contains(n)) {
                                    newEdges.add(dEdge);
                                }
                            }
                            else {
                                newEdges.add(dEdge);
                            }
                            return true;
                        }
                    });
                    if (!newEdges.isEmpty()) {
//                        newEdges.compact();
                        result.map.put(d, newEdges);
                    }
                }
                return true;
            }
        });
//        for (Object d : map.keySet()) {
//            if (d != capitalLambda) {
//                Set<TransformerEdge> dEdges = map.get(d);
//                Set<TransformerEdge> newEdges = newSet();
//                for (TransformerEdge dEdge : dEdges) {
//                    long fn = dEdge.getJumpFunction();
//                    if (JumpFunctionFactory.isLoadFunction(fn)) {
//                        State n = JumpFunctionFactory.getSrcState(fn);
//                        if (reachables.contains(n)) {
//                            newEdges.add(dEdge);
//                        }
//                    }
//                    else {
//                        newEdges.add(dEdge);
//                    }
//                }
//                if (!newEdges.isEmpty()) {
//                    result.map.put(d, newEdges);
//                }
//            }
//        }
        
//        result.map.forEachValue(new TObjectProcedure<TLongHashSet>() {
//            public boolean execute(TLongHashSet v) {
//                v.compact();
//                return true;
//            }
//        });        
        
        if (AtomicTransformer.COMPACT_SUMMARIES) {
            cleanup2(result);
        }
        return result;
    }
    
//    public boolean hasOutgoingEdge(Object o) {
//        return map.containsKey(o);
//    }
    
//  public Transformer removeRedundancy() {
//      Automaton nfa = getAccessesNfa();
//      Pair<Map<State,Set<State>>, Automaton> p = nfa.convertToDfa();
//      Automaton dfa = p.getSecond();
//      
//      Set<TransformerEdge> accessEdges = new HashSet<TransformerEdge>();
//      for (Transition tn : dfa.getTransitions()) {
//          accessEdges.add(new TransformerEdge(new EdgeJumpFunction(tn.getSrc(), tn.getDst(), tn.isWrite()), tn.getLbl()));
//      }
//      
//      Transformer result = newInstance();
//      result.map.put(capitalLambda, accessEdges);
//      
//      // now update load edges and pass on all other transformer edges
//      Map<State,Set<State>> nfaStateToDfaStates = p.getFirst();
//      
//      for (Object d : map.keySet()) {
//          if (d != capitalLambda) {
//              Set<TransformerEdge> dEdges = map.get(d);
//              Set<TransformerEdge> newEdges = new HashSet<TransformerEdge>();
//              for (TransformerEdge dEdge : dEdges) {
//                  JumpFunction fn = dEdge.getJumpFunction();
//                  if (fn instanceof LoadJumpFunction) {
//                      LoadJumpFunction lfn = (LoadJumpFunction)fn;
//                      State n = lfn.getN();
//                      Set<State> dfaStates = nfaStateToDfaStates.get(n);
//                      if (dfaStates == null) {
//                          //throw new RuntimeException("No dfa state for state " + n);
//                          continue;
//                      }
//                      else {
//                          for (State dfaState : dfaStates) {
//                              if(!newEdges.add(new TransformerEdge(new LoadJumpFunction(dfaState), dEdge.getDest()))) {
////                                    System.err.println("Adding failed because transformer edge already exists");                                    
//                              }
//                          }
////                            System.err.println("Added " + dfaStates.size() + " load statements instead of 1");
//                      }
//                  }
//                  else {
//                      // identify jump function or store jump function goes through unchanged
//                      newEdges.add(dEdge);
//                  }
//              }
//              if (!newEdges.isEmpty()) {
//                  result.map.put(d, newEdges);
//              }
//          }
//      }
//
//      return result;
//  }
    
//    public String getLabel(Object o) {
//        if (o instanceof SootField) {
//            SootField f = (SootField)o;
//            return f.getName();
//        }
//        else if (o instanceof SootClass) {
//            SootClass c = (SootClass)o;
//            return c.getName();
//        }
//        else if (o instanceof Local) {
//            Local l = (Local)o;
//            return l.getName();
//        }
//        else if (o == arrElem) {
//            return "[]";
//        }
//        else if (o == retVar) {
//            return "$r";
//        }
//        else if (o == thisVar) {
//            return "@this";
//        }
//        else if (o instanceof ParameterVariable) {
//            ParameterVariable param = (ParameterVariable)o;
//            return "@param" + param.getNum();
//        }
//        else {
//            throw new RuntimeException("Unknown object: " + o);
//        }
//    }

//    public int size() {
//        int edgeCount = 0;
//        for (Set<TransformerEdge> edges : map.values()) {
//            edgeCount += edges.size();
//        }
//        return edgeCount;
//    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#numSymbols()
     */
    public int numSymbols() {
        return map.size();
//        return map.keySet().size();
    }
    
//    public int countAccesses() {
//        Set<TransformerEdge> accesses = map.get(capitalLambda);
//        return accesses == null ? 0 : accesses.size();
//    }
//
//    public int countLocalAccesses() {
//        Set<TransformerEdge> accesses = map.get(capitalLambda);
//        int localCount = 0;
//        if (accesses != null) {
//            for (TransformerEdge te : accesses) {
//                if (te.getDest() instanceof Local) {
//                    localCount++;
//                }
//            }
//        }
//        return localCount;
//    }
//
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#countLocalAccesses()
     */
    public int countLocalAccesses() {
        TLongHashSet accesses = map.get(capitalLambda);
        final IntWrapper localCount = new IntWrapper();
        if (accesses != null) {
            accesses.forEach(new TLongProcedure() {
                public boolean execute(long e) {
                    if (!TransformerEdgeFactory.isKill(e)) {
                        int d = TransformerEdgeFactory.getD(e);
                        Object o = SymbolNumberer.getObject(d);
                        if (o instanceof Local) {
                            localCount.add(1);
                        }
                    }
                    return true;
                }
            });
        }
        return localCount.get();
    }

    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#countLocalAccesses(soot.Local)
     */
    public int countLocalAccesses(Local x) {
        TLongHashSet accesses = map.get(capitalLambda);
        final int xNum = SymbolNumberer.getNumber(x);
        final IntWrapper localCount = new IntWrapper();
        if (accesses != null) {
            accesses.forEach(new TLongProcedure() {
                public boolean execute(long e) {
                    int d = TransformerEdgeFactory.getD(e); 
                    if (d == xNum) {
                        localCount.add(1);
                    }
                    return true;
                }
            });
        }
        return localCount.get();
    }
//    
//    public int countLoads() {
//        int loadCount = 0;
//        for (Set<TransformerEdge> edges : map.values()) {
//            for (TransformerEdge e : edges) {
//                if (JumpFunctionFactory.isLoadFunction(e.getJumpFunction())) {
//                    loadCount++;
//                }
//            }
//        }
//        return loadCount;
//    }
//    
//    public int countLiveLoads(Set<State> reachables) {
//        int liveLoadCount = 0;
//        for (Set<TransformerEdge> edges : map.values()) {
//            for (TransformerEdge e : edges) {
//                long fn = e.getJumpFunction();
//                if (JumpFunctionFactory.isLoadFunction(fn)) {
//                    State src = JumpFunctionFactory.getSrcState(fn);
//                    if (reachables.contains(src)) {
//                        liveLoadCount++;
//                    }
//                }
//            }
//        }
//        return liveLoadCount;
//    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#isEmpty()
     */
    public boolean isEmpty() {
        return map.isEmpty();
    }
    
//    
//    protected Set<TransformerEdge> newArraySet(Set<TransformerEdge> other) {
//        ArraySet<TransformerEdge> clone = new ArraySet<TransformerEdge>(other.size());
//        for (TransformerEdge t : other) {
//            clone.addElement(t);
//        }
//        return clone;
//    }
//    
//    protected Set<TransformerEdge> newHashSet(Set<TransformerEdge> other) {
//        return new HashSet<TransformerEdge>(other);
//    }
    
    protected Transformer newInstance() {
        return new Transformer();
    }

    protected Transformer newInstance(Transformer t) {
        return new Transformer(t);
    }
    
//    public Set<TransformerEdge> getEdges(String fieldSig) {
//        for (Object o : map.keySet()) {
//            if(o instanceof SootField) {
//                SootField f = (SootField)o;
//                if (f.toString().equals(fieldSig)) {
//                    return map.get(o);
//                }
//            }
//        }
//        return null;
//    }
    
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#toArraySets()
     */
    public void toArraySets() {
//        for (Object o : map.keySet()) {
//            map.put(o, newArraySet(map.get(o)));
//        }
    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#toHashSets()
     */
    public void toHashSets() {
//        for (Object o : map.keySet()) {
//            map.put(o, new HashSet<TransformerEdge>(map.get(o)));
//        }        
    }
    
//    public TLongHashSet newSet() {
////        return new TLongHashSetLG(10, 0.9f); // custom implementation of TLongHashSet with modified compact() method
//        return new TLongHashSet(10, 0.9f);
//    }

    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#newSet(int)
     */
    public TLongHashSet newSet(int size) {
        return new TLongHashSet(size, 0.9f);
    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#newSetFast(java.util.Set)
     */
    
    /*
    public TLongHashSet getEdges() {
        final TLongHashSet edges = newSet();
        map.forEachValue(new TObjectProcedure<TLongHashSet>() {
            public boolean execute(TLongHashSet v) {
                v.forEach(new TLongProcedure() {
                    public boolean execute(long e) {
                        edges.add(e);
                        return true;
                    }
                });
                return true;
            }
        });
        return edges;        
//        Set<TransformerEdge> edges = newSet();
//        for (Set<TransformerEdge> v : map.values()) {
//            edges.addAll(v);
//        }
//        return edges;
    }
    */

//    public int howManyEdgesWouldBeTransformed(Transformer t) {
//        int numEdgesTransformed = 0;
//        for (Set<TransformerEdge> edges : map.values()) {
//            for (TransformerEdge e : edges) {
//                Object d = e.getDest(); // o --> d
//                if (t.hasOutgoingEdge(d)) {
//                    // d --> d' exists, therefore o --> d would be transformed
//                    // to o --> d''
//                    numEdgesTransformed++;
//                }
//            }
//        }
//        return numEdgesTransformed;
//    }
    
    protected final void addEdge(int d, long e) {
        TLongHashSet edges = map.get(d);
        if (edges == null) {
            edges = newSet(10);
            map.put(d, edges);
        }
        edges.add(e);
    }
    
    /* (non-Javadoc)
     * @see lg.analysis.paths.transformer.TransformerInterface#size()
     */
    public int size() {
        final IntWrapper i = new IntWrapper();
        map.forEachValue(new TObjectProcedure<TLongHashSet>() {
            public boolean execute(TLongHashSet v) {
                i.add(v.size());
                return true;
            }
        });
        return i.get();
    }
    
    private class IntWrapper {
        int value = 0;
        public int get() {
            return value;
        }
        public void add(int inc) {
            value += inc;
        }
    }

    @Override
    public void overwriteWith(ITransformer t) {
        overwriteWith((Transformer)t);
    }

    @Override
    public void retainAll(ITransformer t) {
        retainAll((Transformer)t);
    }

    @Override
    public boolean subsumes(ITransformer t) {
        return subsumes((Transformer)t);
    }

    @Override
    public ITransformer differenceWith(ITransformer t) {
        return differenceWith((Transformer)t);
    }

    @Override
    public void differenceWithInPlace(ITransformer t) {
        differenceWithInPlace((Transformer)t);
    }
    
    @Override
    public void unionWith(final ITransformer t) {
        unionWith((Transformer)t);
    }

    @Override
    public ITransformer addAll(ITransformer t) {
        return addAll((Transformer)t);
    }

    @Override
    public ITransformer addAllReturnDelta(ITransformer t, ITransformer delta) {
        return addAllReturnDelta((Transformer)t, (DeltaTransformer)delta);
    }

    @Override
    public ITransformer composeWith(ITransformer t) {
        return composeWith((Transformer)t);
    }

    @Override
    public void cleanup2(ITransformer t) {
        cleanup2((Transformer)t);
    }
}
