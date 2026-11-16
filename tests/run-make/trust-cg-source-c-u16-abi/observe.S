
.text
.macro OBSERVE name, target
.globl _\name
.p2align 2
_\name:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    bl _\target
    ldp x29, x30, [sp], #16
    ret
.endm
OBSERVE observe_id_w0, trust_c_u16_id
OBSERVE observe_not_w0, trust_c_u16_not
OBSERVE observe_xor_w0, trust_c_u16_xor
OBSERVE observe_constant_w0, trust_c_u16_constant
OBSERVE observe_trunc_w0, trust_c_u16_trunc
OBSERVE observe_raw_id_w0, trust_c_u16_id
OBSERVE observe_raw_not_w0, trust_c_u16_not

OBSERVE observe_rust_typed_not_w0, trust_c_u16_rust_typed_not
