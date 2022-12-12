# libatomic-chimera

This is a replacement for GCC libatomic. It's ABI-compatible with libatomic
and provides the same compiler helpers and other APIs.

It does not come with a header file. Its purposes are two:

* to provide a compatibility library for existing binaries
* to provide emulation symbols for compiler intrinsics

To build and install it, just use the supplied Makefile, or compile it by hand.
The Clang compiler is needed to build this; it may not compile with GCC.

The code is based on `atomic.c` from LLVM's `compiler-rt`, and therefore is
available under the same license (Apache-2.0). Extra implementations have been
added for completeness/compatibility with GCC libatomic.
