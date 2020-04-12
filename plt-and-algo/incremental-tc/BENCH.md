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

This gives tremendeous speed up for non-recursive bindings.

### Large files
10k decls total, 5 files: 0.001s
20k decls total, 15 files: 0.002s

### Small files
20k decls total, 1500 files: 0.004s

(Any benchmarks above are generated with 50% def and 50% import and no
actual recursive bindings inside a module)

But what about recursive bindings?
