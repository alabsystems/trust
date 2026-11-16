// Same non-narrowing observer protocol as trust-cg-source-c-u8-abi/observe.S.
// New symbols bind only this fixture; the old six-function subject/anchor is
// neither included nor linked. W0 is returned untouched by each wrapper.
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
OBSERVE observe_ordinary_c_byte_w0, ordinary_c_byte
OBSERVE observe_ordinary_c_byte_raw_w0, ordinary_c_byte
OBSERVE observe_ordinary_wide_byte_raw_w0, ordinary_wide_byte
OBSERVE observe_ordinary_signed_byte_raw_w0, ordinary_signed_byte

// Observer sensitivity control only, not compiler output or proof authority.
.globl _observe_bad_byte_w0
.p2align 2
_observe_bad_byte_w0:
    mov w9, #0x5a
    eor w0, w0, w9
    orr w0, w0, #0xffffff00
    ret
