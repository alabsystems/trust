// THE SELF-TEST CORPUS — clang-assembled ground truth.
//
// Every word the differential's fast tier checks comes out of the assembler, so
// each one is an instruction clang chose to emit at an encoding it chose. That
// is what makes it ground truth: nothing here is hand-encoded, and hand-encoding
// has produced a wrong word three times in this program.
//
// TWO JOBS, and the second constrains what may be added:
//
//   1. The model must AGREE with the hardware on every word here. A mismatch
//      fails the gate outright.
//   2. The non-vacuity battery (`mutate.rs`) is run over exactly this corpus,
//      and every mutation must be CAUGHT on it. So the corpus has to contain a
//      carrier for each mutation's state component: a taken branch, a
//      flag-setting form, a store, a GPR write, and a SIMD/FP register write.
//
// Adding an instruction whose model is known to diverge would break job 1, so
// the SIMD entries below are deliberately the DATA-MOVEMENT forms only. Scalar
// FP arithmetic and the int<->FP converts are bitvector approximations of IEEE
// operations (see baseline.json) and must not appear here until they are either
// exact or refused.
//
// x18 is avoided as a base or destination throughout: it is the Darwin platform
// register and words touching it are excluded from comparison (harness bug 3),
// which would silently shrink this corpus.
//
// That claim was HALF TRUE until 2026-08-18. x18 was never an addressing base,
// but two words WROTE it — `movk x18, #0xbeef, lsl #32` and
// `csel x18, x19, x20, ne` — so both were excluded and the corpus was quietly
// two words smaller than it reads. They now target x17 (which the MOVZ above
// also writes, making the canonical MOVZ/MOVK pair) and x28. A comment
// asserting an invariant the file violates is worse than no comment: it is the
// blind spot the inventory in `src/main.rs` exists to forbid.

.text
.globl _p
_p:
    nop
    add   x0, x1, x2
    sub   w3, w4, w5
    adds  x7, x8, x9
    subs  w10, w11, w12
    and   x13, x14, x15
    orr   x16, x17, x18
    eor   x19, x20, x21
    add   x22, x23, x24, lsl #3
    sub   x25, x26, x27, asr #7
    add   w28, w29, w30, lsr #11
    lsl   x0, x1, #17
    lsr   w2, w3, #9
    asr   x4, x5, #33
    ubfx  x6, x7, #5, #11
    sbfx  x8, x9, #3, #17
    bfi   x10, x11, #7, #13
    orr   x12, xzr, #0x0f0f0f0f0f0f0f0f
    and   x13, x14, #0xfffffffffffff000
    eor   x15, x16, #0x8000000000000000
    movz  x17, #0x1234, lsl #16
    movk  x17, #0xbeef, lsl #32
    movn  x19, #0x00ff
    ldr   x20, [x21]
    ldr   w22, [x23, #16]
    ldrb  w24, [x25, #3]
    ldrsb x26, [x27, #5]
    ldrh  w28, [x29, #6]
    ldrsh x0, [x1, #8]
    ldrsw x2, [x3, #12]
    str   x4, [x5]
    strb  w6, [x7, #1]
    strh  w8, [x9, #2]
    stur  x10, [x11, #-8]
    ldur  w12, [x13, #-4]
    ldp   x14, x15, [x16]
    stp   x18, x19, [x20, #16]
    ldp   w22, w23, [x24, #8]
    ldr   x0, [x1, x2]
    ldr   x3, [x4, w5, sxtw]
    ldr   x6, [x7, x8, lsl #3]
    str   x9, [x10, x11]
    adr   x12, .
    nop
    b.eq  .+16
    cbz   x14, .+8
    cbnz  x15, .+12
    tbz   x16, #5, .+20
    tbnz  x17, #40, .+24
    csel  x28, x19, x20, ne
    csinc x21, x22, x23, lt
    cset  x24, gt
    csneg x25, x26, x27, mi
    madd  x28, x29, x30, x0
    msub  x1, x2, x3, x4
    mul   x5, x6, x7
    smull x8, w9, w10
    umull x11, w12, w13
    udiv  x14, x15, x16
    sdiv  x17, x18, x19
    clz   x20, x21
    rbit  x22, x23
    rev   x24, x25
    rev16 w26, w27
    rev32 x28, x29
    sxtb  x0, w1
    sxth  x2, w3
    sxtw  x4, w5
    uxtb  w6, w7
    uxth  w8, w9
    neg   x10, x11
    mvn   x12, x13
    cmp   x14, x15
    cmn   w16, w17
    tst   x18, x19
    ccmp  x20, x21, #3, eq
    ccmn  w22, w23, #7, ne
    extr  x24, x25, x26, #19
    ror   x27, x28, #23
    add   x0, x1, #291
    sub   w2, w3, #1092, lsl #12
    adds  x4, x5, #4095
    subs  w6, w7, #17
    add   x8, x9, w10, uxtb #2
    sub   x11, x12, w13, sxth #3

    // SIMD&FP DATA MOVEMENT. These are here because of family 1: `str
    // d13,[x28,#0xa0]` was modeled as a store of the GPR X13, and no word in
    // this corpus could see it. A differential with no SIMD carrier cannot
    // catch a SIMD bug, and the `fp-write-to-gpr` mutation exists to prove
    // these are actually being compared.
    ldr   d0, [x1, #8]
    ldr   s2, [x3, #4]
    ldr   q4, [x5, #16]
    ldr   b6, [x7, #1]
    ldr   h8, [x9, #2]
    str   d10, [x11, #24]
    str   s12, [x13, #12]
    str   q14, [x15, #32]
    str   b16, [x17, #3]
    str   h20, [x21, #6]
    // THESE FOUR ARE CURRENTLY REFUSED BY THE DECODER — unscaled (LDUR/STUR)
    // and register-offset SIMD&FP forms. They are kept here deliberately. A
    // refusal is the correct fail-closed disposition and costs only coverage,
    // so they show up in the run as `decoder refuses the word` rather than as
    // comparisons. But the moment someone teaches the decoder these forms, they
    // become live comparisons in this corpus automatically — so adding decode
    // support without correct semantics behind it fails stage 1 immediately,
    // instead of quietly becoming a wrong answer where a refusal used to be.
    ldur  d22, [x23, #-8]
    stur  q24, [x25, #-16]
    ldr   d26, [x27, x28]
    str   d30, [x0, x1, lsl #3]

    // SCALAR FP ARITHMETIC and the CONTROL-FLOW forms. Both classes were
    // outside this oracle until now — `FADD`/`FSUB`/`FMUL`/`FDIV` because the
    // concrete replayer refused every FP `Formula` node, and `B`/`BL`/`RET`
    // because it refused `Effect::Branch`/`Call`/`Return`. Both were ACCEPTED by
    // the model throughout, so the output gate could reach Proven on them while
    // nothing compared them: `sem_bl` returning to pc+8 instead of pc+4 was
    // measured to pass the whole standing gate.
    //
    // They are carriers, not decoration: `perturb-fp-value` and
    // `perturb-pc-target` in `mutate.rs` are checked over exactly this corpus,
    // so if either class silently stops being replayed the battery goes BLIND
    // and the gate fails before any sweep number is believed.
    //
    // The int<->FP converts and FMOV-immediate are still absent on purpose —
    // they are the recorded-diverging families and would break job 1.
    fadd  d0, d1, d2
    fsub  d3, d4, d5
    fmul  s6, s7, s8
    fdiv  s9, s10, s11
    fadd  s12, s13, s14
    fsub  d15, d16, d17
    fmul  d19, d20, d21
    fdiv  d22, d23, d24
    b     .+64
    bl    .+128
    ret
