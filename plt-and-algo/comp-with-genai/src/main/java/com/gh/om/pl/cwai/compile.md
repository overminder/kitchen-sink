# Architectural design of a simple JIT compiler

## Inefficiency in the interpreter

The evaluation rules mentioned in interp.md are high-level and concise. However, our interpreter is not optimized for speed. It does a lot of work that can be done at compile time. For instance,

- The env is a string-keyed map, so lookup takes a lot more than one instruction. A compiler can emit a single instruction to load the value from a variable.
- The binding of variables in let-exp and letrec-exp is non-destructive, which means that it allocates a new map on the heap every time. A compiled runtime can use stack allocation for variables.
- The introduction of cells from letrec adds a read barrier to all lookups (not just the ones bound by letrec). Static analysis would allow non-barriered lookups.
- Unbound variables throw errors at runtime, whereas static analysis would allow the interpreter to throw errors at compile time.
- Integers are always boxed due to Java's safe type system, whereas a compiled runtime can use tagged integers to avoid boxing.
- Visiting the AST is a lot of work. The actual evaluation can be just a few instructions. For instance, every time the interpreter visits an EInt, it needs to do a type-check and extract its value. A compiler can emit a single instruction
  `mov $rax, <int>`.

## Simple stack-based compiler

When emitting machine code, operations often need to use registers as operands. Registers are fast to access, but they are limited in number and requires register allocation if we want to use them for everything. For now, we'll use a simple stack-based approach:

* Store variables on the stack. Allocate each variable a fixed offset from the stack pointer.
* Use one or two temporary registers as the register operands if the instruction requires it.
* At each function's prologue, locate the arguments by following the platform's calling
  convention, and immediately store the arguments on the stack.
* Properly handle tail calls by not allocating a new stack frame if the function is called at tail position.
    * TODO: x86_64 only has 6 register arguments, so we need to spill arguments to the stack if there are more than 6 arguments, and that makes tail call harder (caller clean up but we don't have a caller after tail call)

## Garbage collection

The interpreter also doesn't have to worry about garbage collection, since it's hosted in a garbage collected language. But a compiled runtime does.

We'll use a simple stop-the-world semi-space copying collector. This requires special handling from the compiled code, because we'll be moving objects around. A basic idea is:

* Have 2 heaps: a "from-heap" where we'll be allocating in, and a "to-heap" for copying the living objects to when the from-heap is full. After each collection, the role of the heaps will swap.
* Have GC safe points where the runtime can pause the program and move objects around.
* Maintain a root set of all objects that are currently reachable.

### Allocation routine

We'll dedicate 2 registers: one as the heap pointer, and one as the heap limit pointer (e.g. %r10 and %r11 since they are caller saved "volatile" registers). These 2 registers will be checked at every allocation to see if the allocation will overflow the heap.

- If it doesn't, we can process with the allocation by bumping the heap pointer ("bump pointer allocation")
- If it does, the control will be transferred from the compiled program to the garbage collector for collection. This is a GC safe point (and is the only safe point that we'll use in this implementation). The callee will pass the GC roots to the collector as well.

### Root set management

In general, living objects can be found either on the register, stack, or transitively reachable from them. In our implementation, we simplify things by the following strategy:

* The caller will pass its frame pointer and stack layout descriptor to the runtime.
* The stack layout descriptor will reveal live objects on the stack (we assume all objects on the stack are alive).
* The stack layout descriptor + frame pointer will also link to the caller's frame, and we can continue to find live objects on the caller's stack.
* We require callers to save registers on the stack, so the runtime doesn't need to check registers for roots.

## Object layout

We'll use a simple object layout where each object has a header and a payload. The header will describe the object's type and a GC redirect pointer (pointing to the moved object in the to-heap) . The payload will contain the object's fields.

Note that we'll use tagged pointers for integers: Since heap objects are 8-byte aligned, their least significant bit will always be 0. We can set this bit to 1 for integers, and use the pointer as the integer value. This means we have 63-bit integers (called "fixnums").

## Code generation rules

We'll still need to follow interp.md for the evaluation rules. The compiler will visit the AST, and emit machine code which evaluates the AST by pushing the values on the stack. If an exp takes arguments, these arguments must already been pushed on the stack, so the exp should pop them, do the operation, and push the result back on the stack. Before returning a function, the last expression should be evaluated and pushed on the stack, and we want to the callee to pop the return value to the platform's return register (e.g. %rax on x64).

- (compile 1) => push 1
- (compile some-var) => load some-var from the stack, then push to the stack
- (compile (+# exp1 exp2)) => compile exp1, compile exp2, pop exp2 to a register, add the register to the top of stack (here we save one pop/push since x86_64's add instruction can take one memory operand)
- (compile (if cond t f)) => compile cond, pop cond to a register, compare the register with the value of #f, if true jump to label for t (which contains code from (compile t)), else jump to label for f (which contains code from (compile f)). At the end of t and f, we need to pop the result from the stack and jump to the next instruction.
- (compile (let bindings body)) => compile rhs of each binding. For each binding, pop it from the stack to a temporary register, and store the register to the fixed offset for that variable on stack, then compile body.

### Example code generation

Define and call a fibonacci function:

```
(letrec
  ([fibo (lambda (n)
           (if (<# n 2)
               n
               (+# (fibo (-# n 1)) (fibo (-# n 2)))))])
  (fibo 10))
```

can be code generated as (pseudo code):

fibo:
; arguments 2: n, closure-object. The closure object represents an instantiated fibo lambda (because the body of fibo lexically captures fibo symbol)
; prologue: adjust frame and stack pointer
; save arguments n and closure-object to a fixed offset on the stack
; compile (<# n 2) by pushing n on the stack, 2 on the stack, popping 2 to temporary register (e.g. %rax), and comparing %rax with top of stack
; compile if by jump to different labels (ifTrue / ifFalse)
ifTrue:
; compile n (push n on the stack)
; compile return (pop top of stack to %rax, clean up stack, then ret)
ifFalse:
; compile (-# n 1) by pushing n and 1 on the stack, then popping 1 to %rax, and sub %rax with top of stack
; compile (fibo _). This is a function call, following the platform's c calling convention. the function to call is
extracted from closure-object (e.g. to a register), then call
func-ptr(_, closure-ptr), and push the return value on the stack
; similarly compile (fibo (-# n 2))
; similarly compile (+# _ _) and return

main:
; compile (letrec ([fibo ...]) (fibo 10)), which is a bit more involved.
; Step 1-5 is for [fibo ...] (allocating the cell and the closure pointer, and initializing them)
; Step 6
; 1. do a real allocation of cell by bumping the heap pointer, or call into runtime if allocation fails
; 2. initialize the cell ptr by setting its header (indicating it's a cell)
; 3. do another allocation, for the closure pointer of fibo.
; 4. initialize the fibo lambda by setting its header (indicating it's a fibo lambda) and payload (which contains the cell allocated from (1), because the rhs of fibo captures a fibo variable)
; 5. finally populate the cell by setting its payload (the fibo lambda)
; 6. tail call (fibo 10) (be sure to include the closure pointer in the arguments, which is is a hidden argument to the call)

### Memory management for compiled code

Check platform-memory.kt for how to allocate code buffer for JIT compilation.

