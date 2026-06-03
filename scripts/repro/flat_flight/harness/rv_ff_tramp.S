.section .text
.global rv_ff_call
rv_ff_call:                 # a0=&st a1=&s -> a0 (cmd); s11=0 for native pointer deref ([s11+ptr]=[ptr])
    addi sp,sp,-16
    sw ra,0(sp)
    sw s11,4(sp)
    li s11,0
    call flat_flight
    lw s11,4(sp)
    lw ra,0(sp)
    addi sp,sp,16
    ret
