 .globl main
main:
 pushq %rbp
 movq %rsp, %rbp
 pushq %rbx
 pushq %r12
 pushq %r13
 pushq %r14
 subq $0, %rsp
 movq $16384, %rdi
 movq $16, %rsi
 callq initialize
 movq rootstack_begin(%rip), %r15
 jmp main_start
main_start:
 movq $42, %r10
 movq %r10, %r10
 movq %r10, %rax
 jmp main_conclusion
main_conclusion:
 movq %rax, %rdi
 callq print_int
 movq $0, %rax
 subq $0, %r15
 addq $0, %rsp
 popq %r14
 popq %r13
 popq %r12
 popq %rbx
 popq %rbp
 retq
