# Early Days

## Naive Parser
5k decls per file cause the parser to stack overflow.

### Large files
10k decls total, 5 files: 1.5-2.3s (after JIT warms up: .9s)
20k decls total, 15 files: 2s

### Small files
20k decls total, 1500 files: 0.8s

## Naive Whole-Program Type Inferencing (stlc)

This essentially treats all the modules as a whole huge file (because
each use can recursively depend on defs from all modules). So this is
extremely slow -- unification has to keep all tyvars around.

### Benchmark settings
- Best of 10 runs, Java 8, 8th gen i7
- Time spent sololy on type inferencing
- Decls generated randomly split between given number of modules, 50% import
 and 50 def. Def is a simple Int -> Int function (see e645224 poet.kt:addDef).

### Large files
10k decls total, 5 files: 1.2s 
20k decls total, 15 files: 4s

### Small files
20k decls total, 1500 files: 7.2s

## Per-Module Type Inferencing (stlc)

An obvious optimization is to disallow module-level cycles (but still treat
intra-module bindings as arbitrarily recursive bindings). This is what GHC
does -- There're no module-level cycles. Once a module type-checks, its
"contributed bindings" never changes.

This gives okay speed up on large modules (because inside a module we still
allow arbitrary recursive definitions), and makes small modules super fast
to type-check (e.g. even faster than toposort!).

The main improvement is that we never need to do any unifications on imports
(because we already know the exact type). In the naive case, a long import
chain will cause lots of unifications.

Being able to clean up the unification context is just a tiny improvement
 (might be more significant when we are dealing with huge projects).

### Large files
10k decls total, 5 files: 0.5s
20k decls total, 15 files: 0.5s

### Small files
20k decls total, 1500 files: 0.04s

## Per-Module Type Inferencing +Intra-Module SCC (stlc)

A further optimization is based on the observation that not all of the
bindings inside a module are recursive. In fact, usually only few of the
bindings are recursive. This means that we only need to make tyvar placeholders
for each strongly connected components.

This gives a bit more speed up for non-recursive bindings.

### Large files
10k decls total, 5 files: 0.24s
20k decls total, 15 files: 0.31s

### Small files
20k decls total, 1500 files: 0.047s

(Any benchmarks above are generated with 50% def and 50% import and no
actual recursive bindings inside a module)

But what about recursive bindings? Let's say each SCC has 1-9 mutually recursive
bindings. And we have 1/3 imports, 1/3 non-rec defs, and 1/3 rec defs (we will
continue to use this setting until explicitly saying otherwise)

### Large files
10k decls total, 5 files: 0.30s
20k decls total, 15 files: 0.32s

### Small files
20k decls total, 1500 files: 0.07s

## Detour

Sometimes it's worth doing profiling if we don't know where's the bottleneck.
So I used IntelliJ's excellent Java CPU profiling tool to capture a flame
graph. Turned out that the `infer` function was doing excessive copying on the
passed tyEnv (a Map), which was taking >90% of execution time ;D

Optimizing that with a chained map resulted in a 10x to 30x speed up on large
files. And it's even better on JIT-ed code (as excessive allocation is not
something that the compiler can optimize away, and the allocated map is used
immediately so no escape analysis / allocation sinking can be done).

Now SCC calculation takes almost the same time as type inference!

### Large files
10k decls total, 5 files: 0.006s
20k decls total, 15 files: 0.01s
100k decls total, 15 files: 0.088s (Almost linear! SCC takes 0.15s)

### Small files
20k decls total, 1.5k files: 0.013s
100k decls total, 1.5k files: 0.069s (Linear!)

## Introducing HM-style inference (seems to be algorithm W)

Following Jones's Typing Haskell in Haskell. The downside is that
substitutions are applied too often and we don't have many of the purely
functional data structure (so essentially we become quadratic again!).

The result is horrendous for slightly larger files, due to applyFrom spending
too much time. Why?
- Substitutions are represented as immutable maps and needs o be constantly
  updated with new substitutions. Whereas Ocaml and Prolog use ref cells
  inside tyVars to destructively apply substitutions.
- Generalization over large type env is also expensive (See
  [Oleg Kiselyov's article](http://okmij.org/ftp/ML/generalization.html),
  section generalization)

### Large files
1.5k decls total, 5 files: 0.5s

### Small files
1.5k decls total, 50 files: 0.026s
20k decls total, 1.5k files: 0.1s

## Fast unification with ML-style destructive substitution

We now represent TyVars as mutable cells, and substs are implicitly applied
as destructive updates. So we only need to do copying on generalization and
instantiation. Another optimization is to treat toplevel bindings as
immutable and assume they never contain unbound TyVars. This is only true
because we do type inference in topological SCC order. (But this assumption
will be invalidated once we allow mutability...)

### Large files
10k decls total, 5 files: 0.013s
20k decls total, 15 files: 0.022s
100k decls total, 15 files: 0.064s (Even faster than STLC?)

### Small files
20k decls total, 1.5k files: 0.031s
100k decls total, 1.5k files: 0.082s (Still linear)
