# Partial Evaluation and Automatic Program Generation

https://www.itu.dk/people/sestoft/pebook/

30 years old PE textbook, still relevant as an introductory material.

# Reading Notes

## Ch 1: Intros

- How PE can be useful
  + Specialize interpreters into compilers
  + Specialize compilers into compiler generators
- common notions (double brackets and T-tetromino)
- Futumura projections

## Ch 2: Intros to basic PL knowledge 

Nothing special.

## Ch 3: Intros to mini-langauges and their interpreters

Intros to untyped lambda calculus, and 3 mini languages:
1. untyped CBV LC (expression only)
2. (1) + recursive equations (i.e. toplevel bindings)
3. (imperative) langauge with store updates and goto

What can/can't specialization of interpreters achieve:
- Can: remove interpretation overhead
- Can't: change data structure / langauge paradigm (functional expr to
  imperative machine instr)
