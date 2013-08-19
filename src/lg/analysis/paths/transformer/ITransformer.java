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

package lg.analysis.paths.transformer;

import gnu.trove.map.hash.TIntIntHashMap;
import gnu.trove.set.hash.TLongHashSet;

import java.util.Set;

import lg.analysis.paths.automata.Automaton;
import lg.analysis.paths.transformer.fast.*;
import lg.analysis.paths.transformer.fast.Transformer;
import soot.*;

public interface ITransformer {

    // Overwrite with contents from t.
    // Differs from unionWith, as it doesn't make implicit edges explicit.
    public abstract void overwriteWith(ITransformer t);

    // retains only the edges that are both in "this" and "t"
    // (i.e. like intersection)
    public abstract void retainAll(ITransformer t);

    // Is this >= t
    public abstract boolean subsumes(ITransformer t);

    // this - t
    // post: returns all edges in "this" that are not in "t"
    public abstract ITransformer differenceWith(ITransformer t);

    public abstract void differenceWithInPlace(ITransformer t);

    public abstract ITransformer addAll(ITransformer t);

    public abstract ITransformer addAllReturnDelta(ITransformer t,
            ITransformer delta);

    public abstract void unionWith(ITransformer t);

    // (t o this)(e) = t(this(e)) (i.e. "this" is below and "t" is above)
    public abstract ITransformer composeWith(ITransformer t);

    public abstract void compact();

    public abstract void cleanup();

    public abstract void cleanup2(ITransformer t);

    public abstract ITransformer clone();

    // returns a copy of this transformer but without any method local vars
    public abstract ITransformer removeMethodLocalVars();

    // renames params in transformer to args, wrt the given mapping
    public abstract ITransformer calleeToCallerContext( 
            TIntIntHashMap paramsToArgs);

    public abstract void outputDot(SootMethod m, boolean aggregate,
            String filename);

    public abstract Automaton getAccessesNfa();

    public abstract ITransformer removeDeadEdges();

    public abstract int numSymbols();

    public abstract int countLocalAccesses();

    public abstract int countLocalAccesses(Local x);

    public abstract boolean isEmpty();

    public abstract int size();

}