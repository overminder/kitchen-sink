#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static intptr_t runDirectThreading(intptr_t n, intptr_t *SP) {
  void *LR;
  intptr_t R0;

// main:
  R0 = n;
  LR = &&main_call_ret;
  goto fibo;

fibo:
  if (R0 < 2) {
    goto *LR;
  }
  SP -= 2;
  SP[0] = R0;
  SP[1] = (intptr_t) LR;
  R0 -= 1;
  LR = &&fibo_call1_ret;
  goto fibo;

fibo_call1_ret:
  LR = (void **) R0;
  R0 = SP[0] - 2;
  SP[0] = (intptr_t) LR;
  LR = &&fibo_call2_ret;
  goto fibo;

fibo_call2_ret:
  R0 = SP[0] + R0;
  SP += 2;
  goto *(void **) SP[-1];
  // ^ Branch mispredication here.

main_call_ret:
  return R0;
}

static intptr_t runWithPredictor(intptr_t n, intptr_t *SP) {
  void *LR;
  intptr_t R0;

// main:
  R0 = n;
  LR = &&main_call_ret;
  goto fibo;

fibo:
  if (R0 < 2) {
    goto *LR;
  }
  SP -= 2;
  SP[0] = R0;
  SP[1] = (intptr_t) LR;
  R0 -= 1;
  LR = &&fibo_call1_ret;
  goto fibo;

fibo_call1_ret:
  LR = (void **) R0;
  R0 = SP[0] - 2;
  SP[0] = (intptr_t) LR;
  LR = &&fibo_call2_ret;
  goto fibo;

fibo_call2_ret:
  R0 = SP[0] + R0;
  SP += 2;
  {
    // | Manually predictes the branch destination.
    void **retAddr = (void **) SP[-1];
    if (retAddr == &&fibo_call1_ret) {
      goto fibo_call1_ret;
    }
    else if (retAddr == &&fibo_call2_ret) {
      goto fibo_call2_ret;
    }
    else {
      goto *retAddr;
    }
  }

main_call_ret:
  return R0;
}

static intptr_t runNative(intptr_t n) {
  if (n < 2) {
    return n;
  }
  return runNative(n - 1) + runNative(n - 2);
  // ^ Return stack buffer suits best in this scenario.
}

intptr_t fiboInterp(intptr_t arg, const char *which) {
  intptr_t (*f)(intptr_t, intptr_t *);
  intptr_t stack[1024];
  intptr_t res;

  if (strcmp(which, "native") == 0) {
    res = runNative(arg);
  }
  else {
    f = strcmp(which, "fast") == 0 ? runWithPredictor : runDirectThreading;
    res = f(arg, stack + 1024);
  }
  return res;
}
