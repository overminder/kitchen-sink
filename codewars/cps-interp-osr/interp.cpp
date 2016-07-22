#include "value.hpp"
#include "bytecode.hpp"

void interpret(Value *func, Value **stackBase, Value **globals) {
  auto stack = stackBase;
  intptr_t oparg;
  auto codePtr = &func->info().bytecodes()[0];

#define DECODE_OPARG_I8()                       \
  oparg = (int8_t) *codePtr++

#define DECODE_OPARG_I16()                      \
  oparg = *(int16_t *) codePtr;                 \
  codePtr += 2

#define PUSH(x)                                 \
  --stack;                                      \
  *stack = (x)

#define POP()                                   \
  *stack++

  static void *dispatchTable[] = {
#define MK_DISPATCH_ENTRY(x)                    \
    [x] = &&Label ## x,
    BYTECODE_OP_NAMES(MK_DISPATCH_ENTRY)
#undef MK_DISPATCH_ENTRY
  };

#define CASE(x) Label ## x:

  CASE(LoadLocal) {
    DECODE_OPARG_I8();
    PUSH(stackBase[oparg]);
  }

  CASE(LoadPayload) {
    DECODE_OPARG_I8();
    Value *top = POP();
    PUSH(stackBase[oparg]);
  }

  CASE(LoadGlobal) {
    DECODE_OPARG_I8();
    PUSH(globals[oparg]);
  }
}
