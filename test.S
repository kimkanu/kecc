main:
        addi	sp,sp,-32
        sd	ra,24(sp)
        sd	s0,16(sp)
        addi	s0,sp,32
        mv	a0,zero
        sd	a0,-20(s0)
        li	a0,0
        fcvt.s.w	fa0,a0
        fsw	a0,-24(s0)
        fsw	a0,-24(s0)
        flw	fa0,-24(s0)
        li	fa1,0
        fadd.s	fa0,fa0,fa1
        fsw	fa0,-28(s0)
        fsw	a0,-28(s0)
        flw	fa0,-28(s0)
        fcvt.w.s	a0,fa0,rtz
        sw	fa0,-32(s0)
        sw	a0,-32(s0)
        lw	a0,-32(s0)
        ld	sp,16(s0)
        ld	sp,24(ra)
        addi	sp,sp,32
        ret
