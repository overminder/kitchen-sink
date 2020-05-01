### Goal

How to balance:
- Language expressiveness (polymorphism, HKT, first class modules,
  type inference etc)
- Featureful IDE (code navigation, auto-completion, auto-fix etc)
- Performance of the compiler, IDE, and build system (incremental type
  checking / resolution / codegen etc)

### Relationship with Kt compiler

JetBrains (IntelliJ Idea) seems to be doing the IDE part really well.
Kotlin compiler does contain a lot of machinery for incremental analysis.
I should read more about it (see this-repo/readings/kt-compiler)

### Other readings

- [Self Adjusting Computation](http://www.umut-acar.org/self-adjusting-computation)
- [MIT Id language (book by Shail Aditya Gupta)](https://dl.acm.org/doi/book/10.5555/888484)
- [Also a shorter version of above: Incremental polymorphism, by Shail Aditya Gupta](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.26.5066&rep=rep1&type=pdf)
- Incremental On-Line Type Inference (Thomas L. Robinson)

So looks that at least for typing this is a solved problem?

- [Ekmett's papers](https://www.reddit.com/r/haskell/comments/3u9wak/incremental_unification_and_program_manipulation/)

- [Haskell-code-explorer](https://github.com/alexwl/haskell-code-explorer/issues/2):
  Compares the output of two Haskell code indexers.

