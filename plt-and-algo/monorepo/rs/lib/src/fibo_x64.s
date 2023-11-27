.globl _fibo_asm_internal
_fibo_asm_internal:
# fibo(n: i64) -> i64
.fibo_entry:
    cmp $2, %rdi
    jge .fibo_recur
    mov %rdi, %rax
    ret
.fibo_recur:
    sub $24, %rsp
    mov %rbp, (%rsp)
    mov %rsp, %rbp
    mov %rdi, 8(%rsp)
    sub $1, %rdi
    call .fibo_entry
    mov %rax, 16(%rsp)
    mov 8(%rsp), %rdi
    sub $2, %rdi
    call .fibo_entry
    add 16(%rsp), %rax
    mov (%rsp), %rbp
    add $24, %rsp
    ret

.globl _get1
_get1:
    xor %eax, %eax
    ret
