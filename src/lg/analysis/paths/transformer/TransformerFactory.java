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

import lg.analysis.paths.transformer.fast.*;
import lg.analysis.paths.transformer.fast.Transformer;
import lg.analysis.paths.transformer.slow.SlowTransformer;
import lg.transformer.AtomicTransformer;
import soot.*;
import soot.jimple.*;
import soot.util.Numberable;

public class TransformerFactory {

    public static ITransformer newAccessTransformer(Object x, Stmt n, boolean write) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.AccessTransformer(x, n, write) : new AccessTransformer(x, n, write);
    }
    
    public static ITransformer newArrayLoadTransformer(Local x, Local y, Stmt n) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.ArrayLoadTransformer(x, y, n) : new ArrayLoadTransformer(x, y, n);
    }

    public static ITransformer newArrayStoreTransformer(Local x, Local y, Stmt n) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.ArrayStoreTransformer(x, y, n) : new ArrayStoreTransformer(x, y, n);
    }
    
    public static ITransformer newCallTransformer(InvokeExpr invokeExpr) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.CallTransformer(invokeExpr) : new CallTransformer(invokeExpr);
    }

    public static ITransformer newFieldLoadTransformer(Local x, Numberable y, SootField f, Stmt n) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.FieldLoadTransformer(x, y, f, n) : new FieldLoadTransformer(x, y, f, n);
    }
    
    public static ITransformer newFieldStoreTransformer(Local x, SootField f, Local y, Stmt n) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.FieldStoreTransformer(x, f, y, n) : new FieldStoreTransformer(x, f, y, n);
    }

    public static ITransformer newIdentityTransformer() {
        return AtomicTransformer.SLOW_TRANSFORMERS ? lg.analysis.paths.transformer.slow.IdentityTransformer.v() : IdentityTransformer.v();
    }
    
    public static ITransformer newLocalCopyTransformer(Local x, Object y) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.LocalCopyTransformer(x, y) : new LocalCopyTransformer(x, y);
    }
    
    public static ITransformer newNullCopyTransformer(Local x) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.NullCopyTransformer(x) : new NullCopyTransformer(x);
    }
    
    public static ITransformer newReturnNullTransformer() {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.ReturnNullTransformer() : new ReturnNullTransformer();
    }

    public static ITransformer newReturnStmtTransformer(Local x) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.ReturnStmtTransformer(x) : new ReturnStmtTransformer(x);
    }
    
    public static ITransformer newReturnTransformer(Local x) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.ReturnTransformer(x) : new ReturnTransformer(x);
    }
    
    public static ITransformer newStaticFieldStoreNullTransformer(SootClass c, SootField f, Stmt n) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.StaticFieldStoreNullTransformer(c, f, n) : new StaticFieldStoreNullTransformer(c, f, n);
    }
    
    public static ITransformer newStaticFieldStoreTransformer(SootClass c, SootField f, Local y, Stmt n) {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.StaticFieldStoreTransformer(c, f, y, n) : new StaticFieldStoreTransformer(c, f, y, n);
    }
    
    public static ITransformer newThrowTransformer() {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new lg.analysis.paths.transformer.slow.ThrowTransformer() : new lg.analysis.paths.transformer.fast.ThrowTransformer();
    }
    
    public static ITransformer newEmptyTransformer() {
        return AtomicTransformer.SLOW_TRANSFORMERS ? new SlowTransformer() : new Transformer();
    }
    
}
