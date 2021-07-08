# Operator

- "Class" of nodes, potentially shared
- Defines opcode, arithmetic properties (in a bitset), name, and number of value/effect/control inputs and outputs.
  + Nodes always have that many input and outputs (unless during temporary edge modifications, but that state is only visible internally.)
- Operator1 takes an additional parameter that's meaningful for its opcode.

## Common operators

`common-operator.cc` defines generic operators such as Dead/Unreachable. This can be a good starting point for understanding v8's sea of nodes implementation.

### Most basic ones

- Start(n): o(EC; V ** n). n is the number of function arguments plus some extra runtime argument (closure ptr, argc, context).
- End(n): i(C ** n). Consumes n C.

- Parameter(ix, name): io(V). Input is the start node, ix is the parameter index.
- Return(n): i(VEC; V ** n), o(C). Takes one more V than n, and still chains the C (to the end node I guess?)

- Loop(n): i(C ** n), o(C). Need to revisit this.
- Merge: Same as above.

- Branch(hint, safetyCheck): i(VC), o(CC). Takes a V and a C, and goes to two branches.

### Others

COMMON_CACHED_OP_LIST defines:

- Dead: o(VEC) only. I guess this is a source of dead input, and any node depending on this will also be dead.
- Unreachable: i(EC), o(VE). Not sure about this... Chaining the E while converting C into V.
- If{True,False}: io(C) only. Guess this is a projection node ffrom Cliff's paper.
- IfSuccess: Same as above.
- IfException: everything except for i(V). I can at least understand the need for chaining E and C.. For o(V) -- Maybe it's holding the value being thrown?
- Throw/Terminate: i(EC), o(C). Chaining the C makes sense, and the E is consumed.
- LoopExit: i(CC), o(C). Why two C? I remember that a loop header usually has two C inputs (from before the loop, from end of the loop) and two outputs (to start of the loop, to outside of the loop).
- LoopExitEffect: i(EC), o(E), ps=noThrow. Chaining the E and consuming the C. Not sure about this.
- Checkpoint: Same as above, just ps=Kontrol.
- BeginRegion(jsObservability): io(E). Looks like memory region.
- FinishRegion: i(VE), o(VE). Paired with above.
- Retain: i(VE), o(E). This one makes sense -- Keep a V alive until the E is chained.

More in CommonOperatorBuilder:

- DeadValue(machineRep): io(V). Is this simply for marking a value as dead?
- Switch(n): i(VC), o(C ** n). Takes a V and a C, and goes to n branches.
- IfValue(value, order, hint) / IfDefault: io(C). Not sure about this.
- Deoptimize(kind, reason, feedbackSource): i(VEC), o(C). Need to read more.
- Deoptimize{If,Unless}(kind, reason, feedbackSource, safetyCheck):
  i(VVEC), o(EC). Additionally chains the E, and takes another V.
- Trap{If,Unless}(id): i(VEC), o(C). Not sure about this.


- OsrValue(ix): i(C), o(V). Converts C into a V, interesting.

- constants (ints, ptrs, compressed ptrs, relocs): o(V).

- Select(machineRep, branchHint): i(VVV), o(V). I remember Cliff talked about this... Is this related to phi?
- Phi(machineRep, n > 0): i(C; V ** n), o(V). So this takes only one C.
- EffectPhi(n > 0): i(C; E ** n), o(E). Same as above.
- InductionVariablePhi(n >= 4): i(C; V ** n), o(V). Looks like a bounded loop phi -- Doc says the value inputs are the entry, backedge, increment, and at least one bound.
- LoopExitValue(machineRep): i(VC), o(V). Consumes the loop exit C to pull the final value out?
- StateValues(n, bitmask): i(V ** n), o(V). Is this the same as graal's state (for deopt)? Are the inputs all SomeStates?
- TypedStateValues(types, bitmask): Same as above, just typed.
- ArgumentsElementsState(argStateType): o(V). Kind of related to how js arguments is created, but not too sure.
- ArgumentsLengthState: o(V). Roughly the same as above.
- ObjectState(id, slot): i(V ** slot), o(V). Not sure about this.
- TypedObjectState(id, types): same as above.
- FrameState(bailoutId, stateCombine, functionInfo): i(V ** 5), o(V). Looks like indeed it's for deopt. What are the 5 inputs here?
- Call(callDescriptor): first input is the target.

### CallDescriptor

Abstracts every aspect around the call. Has these fields:

- target (JS / wasm / runtime?)
- finer grained flags (need framestate, no alloc, caller saved registers, special handling for tail calls to more optimized tier, etc)
- target location (see more at LinkageLocation)
- location signature (arg and return count, and their locations. See more at Signature)
- arithmetic properties (same as an operator)
- list of callee saved registers (this is more fine grained than the caller saved regs in flags, need to think about why)
- stack argument order
- allocatable registers (what is this?)
- return slot count (wasn't this already specified in location signature?)

linkage.cc constructs some common CallDescriptors:

- GetRuntimeCallDescriptor/GetCEntryStubCallDescriptor:
  + Add return regs (arch dependent, jsptr type) to signature
  + Add arguments on stack ("ForCallerFrameSlot", jsptr type) to signature
  + Add runtime function (cptr), arg count (i32), js context (jsptr?) to signature (on arch-dep reg)
  + Set target to be any reg (jsptr). This is not the cptr target, so it must be a trampoline to the actual cptr target?

- GetJSCallDescriptor:
  + one return value, arch-dep ret reg, jsptr type
  + js args on stack, jsptr
  + arch-dep target (jsptr), count (i32), and context (jsptr) args
  + target (jsptr) can be:
    * On a known stack slot, when calling into OSR from unoptimized code
    * On arch-dep js function reg, otherwise

- GetStubCallDescriptor
- GetBytecodeDispatchCallDescriptor
