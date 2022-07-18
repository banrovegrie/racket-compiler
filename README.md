## Nano Pass Compiler

This is a nano pass compiler implementation which spans a subset of the racket language.
Current features of the language that has been covered:
- Integer and boolean data type
- Arithmetic operations including + and -
- Register allocation using graph coloring
- Smart partial evaluation
- Support for booleans and conditional if statement
- Support for while loops, and begin construct
- Support for mutable variables
- Support for fixed size heap allocated vectors
- Support for garbage collection via a 2 space copy collector
- Support for functions, recursion and efficient tail recursion


### Structure and Running

The `runtime.c` file needs to be compiled and linked with the assembly
code that your compiler produces. To compile `runtime.c`, do the
following
```
   gcc -c -g -std=c99 runtime.c
```
This will produce a file named `runtime.o`. The -g flag is to tell the
compiler to produce debug information that you may need to use
the gdb (or lldb) debugger.

Next, suppose your compiler has translated the Racket program in file
`foo.rkt` into the x86 assembly program in file `foo.s` (The .s filename
extension is the standard one for assembly programs.) To produce
an executable program, you can then do
```
  gcc -g runtime.o foo.s
```
which will produce the executable program named a.out.

There is an example "compiler" in the file `compiler.rkt`.  That
file defines two passes that translate R_0 programs to R_0 programs
and tests them using the `interp-tests` function from `utilities.rkt`. It
tests the passes on the three example programs in the tests
subdirectory. You may find it amusing (I did!) to insert bugs in the
compiler and see the errors reported. Note that `interp-tests` does not
test the final output assembly code; you need to use `compiler-tests`
for that purpose. The usage of `compiler-tests` is quite similar to
`interp-tests`. Example uses of these testing procedures appear in
`run-tests.rkt`.

As new languages are added, `run-tests.rkt` will be extended to
test new passes. You will be provided with new iterations of
the script for each assignment.
