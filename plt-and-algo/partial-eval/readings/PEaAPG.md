# Partial Evaluation and Automatic Program Generation

https://www.itu.dk/people/sestoft/pebook/

30 years old PE textbook, still relevant as an introductory material.

# Reading Notes

## Ch 1: Intros

- How PE can be useful
  + Specialize interpreters into compilers
  + Specialize compilers into compiler generators
- common notions (double brackets and T-tetromino)
- Futamura projections (also see [Futamura.hs](../peaapg/hs/Futamura.hs))

## Ch 2: Intros to basic PL knowledge 

Nothing special.

## Ch 3: Intros to mini-langauges and their interpreters

Intros to untyped lambda calculus, and 3 mini languages:

1. an untyped CBV LC (expression only)
2. (1) + recursive equations (i.e. toplevel bindings)
3. "flow chart": an imperative langauge with store updates and goto

What can/can't specialization of interpreters achieve:

- Can: remove interpretation overhead
- Can't: change data structure / language paradigm (functional expr to
  imperative machine instr)

## Ch 4: PE on the flow chart language

Core idea: specialize all the reachable program points `pp`
and stores `vs` (named poly)

1. **Division**: Classify variables into static ones and dynamic ones. The static ones
   will be evaluated at specialization time, while the dynamic ones will be
   evaluated at the runtime (as residue programs).
2. Start from the initial state `(pp_0, vs_0)`, where `vs_0` contains the
   static inputs
3. Compute each of the next reachable `(pp_i, vs_i)`, following the
   general evaluation rules.
   + Control dependency on dynamic values are also residual
   + Assignments to static variables update `vs` instead.
   + Keep track of visited `(pp_i, vs_i)` and don't recompute. Though
     a seen `pp_i` with a different `vs_i` is still considered to be a
     new state.
4. The residue program is generated as poly is fully visited.

Things to consider:

- **Division** (the process of computing that is BTA, binding-time analysis)
  + Must be *uniformly congruent*: any variable that depends on dynamic
    variants must itself be dynamic.
  + Choosing the wrong division can cause PE to not terminate
  + The right division is not computable (or we solve halting problem)
  + This chapter assumes that the same division ("uniform") is applicable
    to the whole input program
  + A simple way is to repeatedly propagate dynamic values by looking
    at the static input program
- **Transition Compression**
  + Used to shorten the code generated (e.g. `goto Label; Label:`)
  + Looks like a kind of peephole optimization, but can't be unconditionally
    applied
  + I don't completely understand this, need to read again
- **Offline vs Online**: Online PEs use the concrete values computed during
  specialization to make further decisions, while offline PEs make
  decisions (e.g. BTA and compression) before the specialization.
- **Base Functions**: host-provided functions that are available at
  both specialization time and runtime. This is important to keep the
  core of `mix` small.

Specializing `mix` itself to make a compiler

- BTA on mix: manually done to show the reasoning (a more friendly
  way is to let user provide BTA annotation)
- Resulting residual program is structured roughly the same way
  as the interpreter
- The `division` variable needs to be static to get good result
  on self-application.

Binding-time improvement

- Re-structure part of the program to surface more static variables.
- **The Trick**: If a function takes a dynamic yet finite input, its return
  value can indeed by static.

Granularity of BTA

- **Uniform**: All `pp` share the same division.
- **Pointwise**: Takes control flow into consideration, so the
  resulting BTA is a map from `pp` to division.
- For imperative languages, the global store can contain dead static
  variables. This leads to superfluous specializations. Need to do
  liveness analysis and reclassify dead static vars as dynamic.
- **Polyvariant**: Each pp can be reached different and have different
  division, so the resulting BTA is a map from `pp` to set of divisions.
  + Two ways to use this information in `mix`: Either lookup the
    division+edge mapping in `mix`, or split the BBs in the source program
    before calling mix.

4.10 contains a size and time comparison for all PE combinations
on this language.

## Ch 5: PE on a first order recursive ULC

### Language: Scheme0

Applicative (pure) operators, no anonymous lambdas, no currying.
Scheme-ish, has quote to support `value->expr` reification.

### Division

Multiple precision to choose from:
- Monovariant: Every function has a mapping of `var -> division`. This is
  roughly the pointwise division for flow chart lang.
- Polyvariant: Every function has multiple mappings of `var -> division`.
  Can be achieved by making multiple copies of the same monovariant
  functions, prior to specialization.

### Congruence

Remember in flow chart lang, a var is static only if all of its assignments'
rhs are static. In Scheme0, a var is created by function application, so an
argument is static only if every value supplied to the call site is be static.

### Specialized program point

Naturally we treat `(function, static arguments)` as program points.
It's also beneficial to add `if` branches as program points (see also:
conditional constant propagation). We can preprocess ifs by moving
each branch to a new function.

### Transition compression

AKA function inlining. Need to avoid infinite inlining (probably
undecidable?). Several conservative ways exist, and the author choose
to only inline functions with fully static arguments.

### Binding-time analysis

- Abstract interpretation on the domain of `{S, D}`
- Type inference on constraints of binding time.

### Division annotations

Idea: Annotate the source with division information. Greatly simplifies
the BTA. Scheme0 contains two variant for each AST: e.g. `call` and `calls`.
(Feels like staged computation?)
