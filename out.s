	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	subq $-16, %rsp
	movl $1, %r11d
	cmpl $1, %r11d
	movl $0, -4(%rbp)
	sete -4(%rbp)
	movl -4(%rbp), %eax
	movq %rbp, %rsp
	popq %rbp
	ret
	movl $0, %eax
	movq %rbp, %rsp
	popq %rbp
	ret
	.section .note.GNU-stack,"",@progbits
