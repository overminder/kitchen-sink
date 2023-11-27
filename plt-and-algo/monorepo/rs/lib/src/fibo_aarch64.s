.globl _fibo_asm_internal
_fibo_asm_internal:
; fibo(n: i64) -> i64
.fibo_entry:
    ; if n < 2: return n
    cmp x0, #2
    b.ge .fibo_recur
    ret
.fibo_recur:
    ; Store n to stack
    ; Note that sp needs to be 16-byte aligned, so we allocate 32 bytes to
    ; to store [fibo(n - 1), n, saved lr, saved fp]
    sub sp, sp, #32
    str fp, [sp]
    str lr, [sp, #-8]
    str x0, [sp, #-16]
    mov fp, sp

    ; Call fibo(n - 1)
    sub x0, x0, #1
    bl .fibo_entry

    ; Store ret val of fibo(n - 1) to stack
    str x0, [sp, #-24]

    ; Call fibo(n - 2)
    ldr x0, [sp, #-16]
    sub x0, x0, #2
    bl .fibo_entry

    ; Add ret vals and restore lr, fp, sp
    ldr x1, [sp, #-24]
    ldr lr, [sp, #-8]
    ldr fp, [sp]
    add x0, x0, x1
    add sp, sp, #32
    ret

.globl _get1
_get1:
    mov x0, #1
    ret
