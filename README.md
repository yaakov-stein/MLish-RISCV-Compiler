MLish Compiler
===

A basic ML-ish to RISC-V(32 bits) compiler. 

The Compiler parses ML-ish using lex/yacc and then compiles that into a scheme-ish language.

Then, it is compiled down to a c-like language.

It is then compiled to a intermediate basic-block language in order to construct a control-flow graph. This is used 
to perform Register Allocation and basic optimizations. Afterwards the basic-blocks are compiled to RISC-V(32 bits).

In order to run the compiler, simply go to the command line and use the following commands:

```
(1) make
(2) ./final_mlish [file_to_compile].ml [output_file].s

(Example: ./final_mlish more_tests/auto-compile-001.ml tmp.s)
```

After that, the compiled RISC-V code will be located in the output file you gave as input and can be run on RISC-V(32 bit) machines or in an emulator (qemu, temu, gem5, etc.)

Notes
===
Currently, the Scheme-ish to C-ish compilation is a WIP and does not work for most "interesting" ML tests. Hoping to fix that up soon.
