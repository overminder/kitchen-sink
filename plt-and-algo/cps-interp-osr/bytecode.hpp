#ifndef _BYTECODE_HPP
#define _BYTECODE_HPP

#define BYTECODE_OP_NAMES(V)                                      \
  /* stack.push(stack[oparg_i8]) */                               \
  V(LoadLocal)                                                    \
  /* ix = oparg_i8; ps = stack.pop(); stack.push(ps[ix]) */       \
  V(LoadPayload)                                                  \
  /* stack.push(globals[oparg_i8]) */                             \
  V(LoadGlobal)                                                   \
  /* n = oparg_i8; ps = stack.pops(n); closure = stack.pop(); */  \
  /* assert code_ptr.arity == n; stack = [closure_ptr] + ps; */   \
  V(TailCall)                                                     \
  /* if stack.pop() == 0: code_ptr += oparg_i16 */                \
  V(JifZ)                                                         \
  /* n = oparg_i8, info_ix = oparg_i16; */                        \
  /* stack, payloads = stack[:-n], stack[-n:]; */                 \
  /* stack.push(mk_closure(info[info_ix], payloads)) */           \
  V(PrimAllocClosure)                                             \
  /* stack.push(oparg_i16) */                                     \
  V(PrimInt)                                                      \
  V(PrimHalt)                                                     \
  /* y = stack.pop(); x = stack.pop(); stack.push(x + y) */       \
  V(PrimIntAdd)                                                   \
  /* y = stack.pop(); x = stack.pop(); stack.push(x - y) */       \
  V(PrimIntSub)                                                   \
  /* y = stack.pop(); x = stack.pop(); stack.push(x < y) */       \
  V(PrimIntLt)

enum Op {
#define MK_OP(x) x,
  BYTECODE_OP_NAMES(MK_OP)
#undef MK_OP
};

#endif  // _BYTECODE_HPP
