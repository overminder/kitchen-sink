There's a two level hierarchy:
- graph, which is a function
- environment, which is likely a lexical scope of the function.

- Environment can be merged.
- Branches are built in environments and then merged to the outer scope?

# Bytecodes

- d8 --print-bytecode dumps the bytecodes. 
- Bunch of addressing modes: a is the accumulator, r0-r15 are the locals, a0-a15 are the arguments. `[0]` is overloaded -- can be immediate, property in constant pool, feedback vector index (fvi), loop depth, etc.
- interpreter-generator.cc and bytecode-graph-builder.cc help to explain the bytecode semantics.

```
- Ld a Zero: a <- 0
- St a r0: a -> r0
- Test{Equal,GreaterThan,...} a0, [fvi]: lhs (a0) is any reg, rhs is always the accumulator. Set test result to accumulator.
- Jump{,IfFalse,...} [relative offset]: if accumulator matches the conditional, jump by offset to somewhere. There's a (addr @ bci) that shows the target bci.
- JumpLoop [relative offset], [loop depth]: jump to loop header, by negative offset. Loop depth is for OSR check.
- {Add,Sub,...} lhs, [fvi]: lhs is any reg. accumulator <- lhs op accumulator
- Mov lhs, rhs: lhs <- rhs
```

# Loops

- BuildLoopHeaderEnvironment is called for each bytecode index (bci). If this bci is a loop header (from bytecode analysis), create:
  + A Loop node (the loop header)
  + A bunch of value and effect phis (also from bytecode analysis)
  + A Terminate node to end the loop (abruptly? Is this for OSR?)

- JumpConditional calls MergeIntoSuccessorEnvironment -- For while it's jump forward so it's effectful. Creates:
  + A sub_environment
  + A IfFalse projection
  + Calls PrepareForLoopExit to build (for OSR?)
  + A fresh Merge node, or some phis to add to the merge

- JumpLoop node merge the current env back to the loop header. This also calls MergeIntoSuccessorEnvironment, but for while loops it's jumping backwards and doesn't do anything. Creates:
  + A fresh Merge node, or some phis to add to the merge
