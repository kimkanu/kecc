	.file	"test.c"
	.option pic
	.text
	.align	1
	.globl	main
	.type	main, @function
main:
	addi	sp,sp,-32
	sd	s0,24(sp)
	addi	s0,sp,32
	sw	zero,-28(s0)
	sw	zero,-24(s0)
	lw	a5,-28(s0)
	fcvt.s.w	fa5,a5
	flw	fa4,-24(s0)
	fadd.s	fa5,fa4,fa5
	fsw	fa5,-20(s0)
	flw	fa5,-20(s0)
	fcvt.w.s a5,fa5,rtz
	sext.w	a5,a5
	mv	a0,a5
	ld	s0,24(sp)
	addi	sp,sp,32
	jr	ra
	.size	main, .-main
	.ident	"GCC: (Ubuntu 10-20200411-0ubuntu1) 10.0.1 20200411 (experimental) [master revision bb87d5cc77d:75961caccb7:f883c46b4877f637e0fa5025b4d6b5c9040ec566]"
	.section	.note.GNU-stack,"",@progbits
