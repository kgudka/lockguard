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

package lg.util;

import java.io.*;

public class Logger {

    private static PrintStream out;
    private static PrintStream outFile;
    private static PrintStream err;
    private static PrintStream stats;
    
    static {
        try {
            out = new PrintStream(System.out, true, "UTF-8");
            outFile = new PrintStream(new FileOutputStream(new File("out.txt")), true, "UTF-8");
            err = new PrintStream(System.err, true, "UTF-8");
            stats = new PrintStream(new FileOutputStream(new File("stats.txt")), true, "UTF-8");
        }
        catch (UnsupportedEncodingException uee) {
            out = System.out;
            err = System.err;
        }
        catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    public static void printstats(String s) {
        stats.println(s);
    }
    
	public static void println(String s) {
		println(s, ANSICode.FG_DEFAULT, ANSICode.BG_DEFAULT);
	}
	
	public static void println(String s, ANSICode fgcolour) {
	    println(s, fgcolour, ANSICode.BG_DEFAULT);
	}
	
	public synchronized static void println(String s, ANSICode fgcolour, ANSICode bgcolour) {
	    out.println("\033[" + fgcolour.getVal() + ";1m\033[" + bgcolour.getVal() + "m" + s + "\033[0m");
	    outFile.println(s);	    
	}

    public static void errprintln(String s) {
        errprintln(s, ANSICode.FG_DEFAULT, ANSICode.BG_DEFAULT);
    }
    
    public static void errprintln(String s, ANSICode fgcolour) {
        errprintln(s, fgcolour, ANSICode.BG_DEFAULT);
    }

	
	public static void errprintln(String s, ANSICode fgcolour, ANSICode bgcolour) {
	    err.println("\033[" + fgcolour.getVal() + ";1m\033[" + bgcolour.getVal() + "m" + s + "\033[0m");
	}
	
}
