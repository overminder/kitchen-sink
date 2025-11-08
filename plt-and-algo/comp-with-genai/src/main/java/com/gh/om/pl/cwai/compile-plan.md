# Plan: Implement `compileAndRun(exp: Exp): IValue`

This plan breaks the JIT pipeline into incremental, testable phases. It is grounded in the existing code and notes:

- `compile.kt` defines `compileAndRun(exp: Exp): IValue`.
- `ast.kt` defines the AST (`Exp`) with `EInt`, `EBool`, `EPrimOp`, `ESym`, `ELet` (and `letrec` via `isRec`), `EIf`, `EAbs`, `EApp`.
- `interp.kt` defines interpreter runtime values `IValue` and semantics we will eventually match.
- `compile.md` outlines a stack-based codegen, object layout, and GC approach.
- `platform-memory.kt` shows how to allocate and invoke JIT code on Windows x64.

The strategy: start closed, effect-free, allocation-free expressions (e.g., `EInt`, `EPrimOp`), then add control flow (`EIf`), stack variables (`ELet`), functions (`EAbs`, `EApp`) without capture, closures and `letrec`, then memory management and GC, finally parity checks and optimizations.

---

## Value representation and object layout (v0)

- Two-bit tagging in low bits:
  - `00` = heap pointer (aligned objects ensure lower 2 bits are 0).
  - `01` = fixnum integer: encode as `(value << 1) | 0x1`.
  - `10` = boolean immediate: use dedicated constants `BOOL_FALSE = 0x2`, `BOOL_TRUE = 0x6`.
- Heap objects (for later phases): 8-byte aligned blocks with header + payload as in `compile.md`.
  - Header has type tag and forwarding pointer for copying GC.
  - Special objects: cell (for `letrec`), closure (code pointer + env pointer).
  - Alignment guarantees low 2 bits are `00`.

## Calling convention and stack model

- Target: Windows x86-64 SysV-like but use Windows x64 ABI (RCX, RDX, R8, R9 for first 4 args; 32-byte shadow space in prologue).
- Use a simple stack machine model per `compile.md`:
  - Keep evaluation results on a virtual operand stack mapped to the machine stack.
  - Locals/let-bound variables get fixed stack offsets from RBP.
  - Temporary registers: use RAX (and optionally RDX) for arithmetic and comparisons.
  - Dedicated GC/allocator registers per `compile.md`: R10 = heap ptr, R11 = heap limit.
- Function prologue/epilogue for compiled entry:
  - `push rbp; mov rbp, rsp; sub rsp, <locals + shadow space + alignment>`
  - `leave; ret`
- For calls (later phases): adhere to Windows x64 shadow space and argument passing; maintain 16-byte alignment at calls.

## Core infrastructure to build first

1. Code buffer and encoder
   - Abstraction `CodeBuffer` to append bytes and track current RIP.
   - Minimal x64 encoders we need first: `mov rax, imm64`, `push imm64` (or `mov [rsp-8], imm64; sub rsp, 8`), `add`, `sub`, `cmp`, `sete/setl`, `cmov`, `test`, `jmp` rel32, `jz/jnz` rel32, `ret`, `push rbp/mov rbp,rsp/leave`.
   - Helpers for stack push/pop to keep virtual stack consistent.

2. Labels and relocations (`linker.kt`)
   - Label definition + resolution with backpatching for rel32 jumps and calls.
   - Absolute pointer materialization via `mov rax, imm64; call rax` to avoid RIP-relative extern relocations in v0.

3. Executable memory and invocation
   - Small wrapper to turn `CodeBuffer` into an invocable function pointer and call it (no args initially).

4. `compileAndRun` skeleton
   - Builds a `Compiler` and emits a single-entry function for the given `Exp`.
   - Decodes the returned tagged value to `IValue` via low-2-bit tag:
    - If tag `01` (fixnum) -> decode `value = rax >> 1` -> `IValue.IVInt(value)`.
    - If tag `10` (boolean) -> `rax == 0x6` => `IVBool(true)`, `rax == 0x2` => `IVBool(false)`; otherwise error.
    - Else (tag `00` pointer) -> heap object; handle in later phases (closures, cells, envs).

## Phase 1: EInt only (closed expressions)

Goal: `compileAndRun(EInt(n))` returns `IVInt(n)`.

- Codegen rule: push tagged immediate `(n << 1) | 1` onto stack; at function end, pop into RAX and `ret`.
- Implement minimal prologue/epilogue and result convention (return value in RAX).
- Unit tests: compile and run `1`, `42`, `-5`.

Deliverables
- `Compiler.compile(exp)` supports `EInt`.
- `compileAndRun` invokes compiled code and converts the result to `IVInt`.
---

## Phase 2: EBool and If (truthiness)

Goal: handle `EBool`, and `EIf` with truthiness (v0) to enable branching.

- `EBool` codegen: push `BOOL_TRUE`/`BOOL_FALSE`.
- `EIf(cond, t, f)`:
  - Compile `cond`; pop to RAX; compare with `BOOL_FALSE`; `je elseLbl`.
  - thenLbl: compile `t`; jump endLbl.
  - elseLbl: compile `f`.
  - endLbl: value of selected branch is on stack.
- Unit tests: `(if #t 10 20)`, `(if #f 10 20)`, nested ifs.

Note: strict boolean checking to match interpreter will come later (Phase 9).

---

## Phase 3: Primitive ops (+#, -#, <#)

Goal: arithmetic and comparison over tagged ints.

- Evaluate args left-to-right, push results.
- For `(+# a b)`:
  - Compile `a`, `b`.
  - Pop `b` into RAX; add RAX to top-of-stack memory (or pop both, compute in RAX); fixnum addition needs to untag/tag:
    - Option A: when adding two `(x<<1|1)`, compute `RAX = RAX + [rsp]; sub RAX, 1` to correct the extra tag bit.
  - Push result.
- For `(-# a b)`:
  - Similar: `RAX = [a] - [b]`; add `1` after subtraction to restore tag.
- For `(<# a b)`:
  - Compare fixnums: either arithmetic-shift-right by 1 into temps then `cmp`, or rely on ordering equivalence of uniformly tagged values.
  - `setl al` -> 0/1; zero-extend into RAX; convert to boolean immediate with `lea rax, [rax*4 + BOOL_FALSE]` (so 0 -> 0x2 false, 1 -> 0x6 true).
- Unit tests mirroring `InterpTest.testAddSubLt`.

---

## Phase 4: Variables and non-recursive let (ESym, ELet with isRec=false)

Goal: lexical locals on stack with fixed offsets.

- Environment layout:
  - During codegen of a scope, allocate each binding a slot at `rbp - offset`.
  - Maintain a map `Map<String, Slot>` in the compiler environment.
- `ESym(name)`: load from its slot and push.
- `ELet(bindings, body, isRec=false)`:
  - For each binding `(name, rhs)`:
    - Compile `rhs`; pop to RAX; store RAX into `slot(name)`.
  - Compile `body` with extended env.
- Unit tests: `let` examples from `InterpTest.testLetBasic`.

---

## Phase 5: If (strict boolean) [optional now, or Phase 9]

Goal: match interpreter’s error semantics: if-condition must be boolean.

- Insert runtime tag check for `EIf` cond:
  - Accept only `FALSE_ENC` or `TRUE_ENC`; otherwise call a runtime trap that throws `IllegalArgumentException` mirroring interpreter message.
- Keep a Kotlin-side runtime helper `throwIfCondNotBool()` which we can call via absolute call through RAX.

---

## Phase 6: Functions without capture (EAbs/EApp, non-closure)

Goal: first-class functions with no free variables.

- Representation v0: function pointer (code address) as an immediate constant; application compiles as a direct call.
- `EAbs(args, body)`:
  - Emit a separate code block (label) with its own prologue; its arguments arrive via Windows x64 ABI.
  - Immediately spill args into the callee’s stack frame slots.
  - Compile `body`; return via RAX.
  - In the outer context, materialize the function’s entry address as an immediate and push it (acts as callee value).
- `EApp(callee, args)`:
  - Evaluate args; place up to 4 into RCX/RDX/R8/R9; others spill to stack per ABI; maintain 16-byte alignment and 32-byte shadow space.
  - Evaluate callee; resolve to entry address; `call` it; push returned RAX.
- Unit tests: simple lambdas that don’t capture, from `InterpTest.testLambdaApplication` second case.

---

## Phase 7: Closures and `letrec` (cells) [allocation begins]

Goal: lexical capture and recursion via closure and cell objects.

- Object layout (heap):
  - Cell: header | payload (one pointer-sized field).
  - Closure: header | codePtr | envPtr (or inline fixed arity captured vars; v0: single envPtr to an environment object).
- Allocation fast path:
  - Use R10 (heap ptr) and R11 (limit). Bump allocate; if overflow, call into GC.
- `letrec`:
  - Allocate cells first; extend env slots with cell pointers.
  - Compile RHS under extended env; for recursive references, `ESym` loads the cell pointer and dereferences at use-sites (v0: direct pointer; later add read barrier if needed).
  - Initialize cells with closure pointers.
- `EAbs` with capture:
  - Build a closure: allocate; write header, codePtr, envPtr.
  - Env object v0: a flat heap object holding captured slots from the current lexical scope.
- `EApp` with closure:
  - Evaluate callee to closure; load codePtr and envPtr.
  - Hidden closure/env arg convention: pass `envPtr` in RCX (arg0), user args shift by one (RDX, R8, R9, ...). Document this in the compiler.
  - In function prologue, first spill `envPtr` and user args to stack slots; captured vars are accessed via `envPtr` fields.
- Unit tests: `letrec` recursive sum and `fibo` from `InterpTest`.

---

## Phase 8: Garbage collection (copying semi-space)

Goal: correctness under allocation pressure.

- Heap manager in Kotlin:
  - Two `Memory` regions (from-heap, to-heap); manage as byte arrays via JNA `Memory` or `VirtualAlloc`.
  - Metadata: allocation cursor, limit, heap base.
- Safe points: allocation slow path only (as in `compile.md`).
- Root set:
  - Pass callee’s frame pointer (RBP) and a stack layout descriptor to GC.
  - Require compilers to spill volatile registers at entry and before GC calls.
  - Stack map: for each compiled function, a compact descriptor of which frame slots contain pointers.
- Copying algorithm:
  - Cheney’s algorithm over roots (stack slots + transitively referenced objects).
  - Set forwarding pointers in headers; update roots and references; swap heaps.
- Integration:
  - Emit slow-path call stub `ensureAlloc(bytes, framePtr, stackMapPtr)` that either bumps R10 or triggers GC and returns new allocation address.
  - Re-establish R10/R11 after GC.
- Tests: force small heap size; allocate enough closures/envs/cells to trigger GC; validate results unchanged.

---

## Phase 9: Error handling and semantic parity with interpreter

Goal: match `interp.kt` error behaviors.

- If condition not boolean: emit check (see Phase 5) and call a Kotlin helper that throws with matching message.
- Arity mismatch: validate at call sites; emit trap on mismatch.
- Calling non-function: validate value shape (closure/function ptr) before call.
- Unbound variable: statically prevent (by construction) for compiled closed programs; for dynamic cases, emit trap.

---

## Phase 10: Optimizations and quality-of-life

- Tail-call elimination for self/mutual recursion (careful with Windows x64 caller cleanup and >4 args spilling).
- Constant folding, dead code elimination for simple patterns.
- Better instruction selection: use memory operands to reduce push/pop.
- Optional: register allocation for hot paths.

---

## Implementation checklist per phase

- Phase 1
  - Compiler skeleton, `EInt`, prologue/epilogue, return.
  - `compileAndRun` minimal path and IVInt conversion.
- Phase 2
  - `EBool`, `EIf` (truthiness), IVBool conversion.
- Phase 3
  - `EPrimOp` (+#, -#, <#), tagged arithmetic helpers.
- Phase 4
  - Locals layout, `ESym`, `ELet` (non-rec).
- Phase 5/9
  - Strict boolean checks and traps for parity.
- Phase 6
  - Non-capturing functions: separate code blocks, calling convention.
- Phase 7
  - Closures/env objects, `letrec` cells, hidden env arg.
- Phase 8
  - Alloc slow-path + copying GC, stack maps, safe points.
- Phase 10
  - TCO, basic optimizations.

---

## Testing plan

- Add JIT tests mirroring `InterpTest.kt` expressions, starting from constants and primitives, then `let`, `if`, simple lambdas, `letrec`, fibo.
- Create stress tests for GC by constraining heap size and allocating many closures/envs.
- Cross-check results against `eval()` for semantic parity where applicable.

---

## File and API placements

- `compile.kt`: implement `compileAndRun(exp)` and small compiler entry.
- `linker.kt`: labels, relocations, and a simple assembler/encoder facade.
- `platform-memory.kt`: reuse allocation/invocation utilities, extend with heap management and GC entry points.
- `ast.kt` / `interp.kt`: unchanged; used for parsing and result conversion only.

---

## Milestones

1) M1: EInt end-to-end (no allocations). 1–2 sessions.
2) M2: EBool/If (+ truthiness), Primitives. 1–2 sessions.
3) M3: ESym/ELet (non-rec). 1–2 sessions.
4) M4: Non-capturing functions (EAbs/EApp). 2–3 sessions.
5) M5: Closures + letrec (allocations, no GC). 3–4 sessions.
6) M6: Copying GC + safe points + stack maps. 4–6 sessions.
7) M7: Parity checks (errors), TCO, small opts. 2–4 sessions.

