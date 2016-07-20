enum Op {
  // stack.push(stack[oparg_i8])
  LoadLocal,

  // ix = oparg_i8; ps = stack.pop(); stack.push(ps[ix])
  LoadPayload,

  // stack.push(globals[oparg_i8])
  LoadGlobal,

  // n = oparg_i8; ps = stack.pops(n); closure = stack.pop();
  // assert code_ptr.arity == n; stack = [closure_ptr] + ps;
  TailCall,

  // if stack.pop() == 0: code_ptr += oparg_i16
  JifZ,

  // n = oparg_i8, info_ix = oparg_i16;
  // stack, payloads = stack[:-n], stack[-n:];
  // stack.push(mk_closure(info[info_ix], payloads))
  PrimAllocClosure,

  // stack.push(oparg_i16)
  PrimInt,

  PrimHalt,

  // y = stack.pop(); x = stack.pop(); stack.push(x + y)
  PrimIntAdd,

  // y = stack.pop(); x = stack.pop(); stack.push(x - y)
  PrimIntSub,

  // y = stack.pop(); x = stack.pop(); stack.push(x < y)
  PrimIntLt,
}
