### Alias Analysis

- http://www.cis.upenn.edu/~cis570/slides/lecture10.pdf
- http://www.seas.harvard.edu/courses/cs252/2011sp/slides/Lec06-PointerAnalysis.pdf
- Demand Driven, JVM: http://www.ics.uci.edu/~guoqingx/papers/yan-issta11.pdf
- OOP: http://manu.sridharan.net/files/aliasAnalysisChapter.pdf
- Compositional Escape Analysis, Java: http://people.csail.mit.edu/rinard/paper/oopsla99.pdf

### SSA: Dominator Construction

- http://ssabook.gforge.inria.fr/latest/book.pdf
- http://compilers.cs.uni-saarland.de/papers/bbhlmz13cc.pdf
- http://www-plan.cs.colorado.edu/diwan/7135/p1684-brandis.pdf
- https://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/a%20fast%20algorithm%20for%20finding.pdf

### SSA: Sea of Nodes IR

- [Cliff 1995](http://paperhub.s3.amazonaws.com/24842c95fb1bc5d7c5da2ec735e106f0.pdf)
- http://hllvm.group.iteye.com/group/topic/39493
- http://darksi.de/d.sea-of-nodes/
- http://www.masonchang.com/blog/2010/8/9/sea-of-nodes-compilation-approach.html
- http://ariya.ofilabs.com/2014/08/javascript-and-v8-turbofan.html
- https://github.com/MatzeB/libfirm
- https://github.com/WebKit/webkit/blob/master/Source/JavaScriptCore/b3

### Sea of Nodes: Graal

- http://lafo.ssw.uni-linz.ac.at/papers/2013_VMIL_GraalIR.pdf
- http://ssw.t/General/Staff/GD/APPLC-2013-paper_12.pdf
- http://ssw.t/Research/Papers/Stadler14PhD/Thesis_Stadler_14.pdf

### SSA: SCCP

- [Wegman Zadeck 1991](https://www.cs.utexas.edu/users/lin/cs380c/wegman.pdf)
- [Click 1995](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.17.8510&rep=rep1&type=pdf)

### SSA: GCM

- [Click 1995](http://c9x.me/comp-bib/click-gvn.pdf)

### SSA: Reg Alloc

- Theory: http://www.rw.cdl.uni-saarland.de/~grund/papers/cc06-ra_ssa.pdf
- Survey: http://compilers.cs.ucla.edu/fernando/publications/drafts/survey.pdf
- LSRA on SSA: http://www.christianwimmer.at/Publications/Wimmer10a/Wimmer10a.pdf
- CSSA / Global Min Algorithm: http://web.cs.ucla.edu/~palsberg/paper/cc09.pdf
- Mem-to-mem free SSA elimination: http://compilers.cs.ucla.edu/fernando/publications/drafts/ssaElimination.pdf
- Puzzle Solving: http://web.cs.ucla.edu/~palsberg/paper/PereiraPalsberg08.pdf
- Embedded JIT: https://arxiv.org/pdf/0710.3642.pdf
- [Graal LinearScan](https://github.com/graalvm/graal-core/blob/master/graal/com.oracle.graal.lir/src/com/oracle/graal/lir/alloc/lsra/LinearScan.java)
- LinearScan impl in Rust: https://github.com/indutny/linearscan.rs

### Other Reg Alloc

- Combinatorial: http://arxiv.org/pdf/1409.7628v1.pdf
- CPS: http://grothoff.org/christian/teaching/2007/3353/papers/cps.pdf
  (Notice the similarity with the SSA-based allocator - they both do
   spilling before (optimal) coloring. Though in Appel's stackless
   compilation approach, spill slots are heap-allocated!)

### Trace Compilation

- http://static.usenix.org/events/vee06/full_papers/p144-gal.pdf

### Misc

- http://the.gregor.institute/t/5k/842/reading.html
- http://c9x.me/compile/bib/
- Extended Linear Scan: http://link.springer.com/chapter/10.1007/978-3-540-71229-9_10

