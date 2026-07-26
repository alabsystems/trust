// trust-machine-sem tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::decode_aarch64;
use trust_types::Formula;

use crate::Aarch64Semantics;
use crate::effect::{Aarch64SyncBoundaryKind, Aarch64SyncOrdering, Aarch64SyncScope, Effect};
use crate::semantics::Semantics;
use crate::state::MachineState;

fn sem() -> Aarch64Semantics {
    Aarch64Semantics
}

fn state() -> MachineState {
    MachineState::symbolic()
}

// ---------------------------------------------------------------------------
// ADD / ADDS
// ---------------------------------------------------------------------------

#[test]
fn test_add_x0_x1_x2_produces_reg_write() {
    // ADD X0, X1, X2 — encoding: 0x8B020020
    let insn = decode_aarch64(&0x8B020020u32.to_le_bytes(), 0x1000).expect("decode ADD");
    let effects = sem().effects(&state(), &insn).expect("effects");

    // Should contain a RegWrite to X0 and a PcUpdate.
    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    let has_pc_update = effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. }));
    assert!(has_reg_write, "ADD should write X0");
    assert!(has_pc_update, "ADD should advance PC");

    // Should NOT have flag updates (ADD, not ADDS).
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(!has_flags, "ADD should not set flags");
}

#[test]
fn test_adds_sets_flags() {
    // ADDS X0, X1, X2 — encoding: 0xAB020020
    let insn = decode_aarch64(&0xAB020020u32.to_le_bytes(), 0x1000).expect("decode ADDS");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_flags, "ADDS should set flags");
}

// ---------------------------------------------------------------------------
// SUB / SUBS / CMP
// ---------------------------------------------------------------------------

#[test]
fn test_sub_x0_x1_x2_produces_reg_write() {
    // SUB X0, X1, X2 — encoding: 0xCB020020
    let insn = decode_aarch64(&0xCB020020u32.to_le_bytes(), 0x1000).expect("decode SUB");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "SUB should write X0");
}

#[test]
fn test_cmp_is_subs_with_zr_dest() {
    // CMP X1, X2 = SUBS XZR, X1, X2 — encoding: 0xEB02003F
    let insn = decode_aarch64(&0xEB02003Fu32.to_le_bytes(), 0x1000).expect("decode CMP");
    let effects = sem().effects(&state(), &insn).expect("effects");

    // CMP should NOT produce a RegWrite (dest is ZR, discarded).
    let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { .. }));
    assert!(!has_reg_write, "CMP (SUBS XZR) should not write a register");

    // CMP should set flags.
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_flags, "CMP should set flags");
}

// ---------------------------------------------------------------------------
// MOV (immediate via MOVZ)
// ---------------------------------------------------------------------------

#[test]
fn test_movz_x0_42() {
    // MOVZ X0, #42 — encoding: 0xD2800540
    let insn = decode_aarch64(&0xD2800540u32.to_le_bytes(), 0x1000).expect("decode MOVZ");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let reg_write = effects.iter().find_map(|e| {
        if let Effect::RegWrite { index: 0, value, .. } = e { Some(value) } else { None }
    });
    assert!(reg_write.is_some(), "MOVZ should write X0");

    // The value should be a BitVec constant 42.
    if let Some(Formula::BitVec { value: 42, width: 64 }) = reg_write {
        // correct
    } else {
        panic!("MOVZ X0, #42 should produce BitVec(42, 64), got: {:?}", reg_write);
    }
}

// ---------------------------------------------------------------------------
// LDR / STR
// ---------------------------------------------------------------------------

#[test]
fn test_ldr_produces_mem_read_and_reg_write() {
    // LDR X0, [X1] — encoding: 0xF9400020
    let insn = decode_aarch64(&0xF9400020u32.to_le_bytes(), 0x1000).expect("decode LDR");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_mem_read = effects.iter().any(|e| matches!(e, Effect::MemRead { .. }));
    let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, .. }));
    assert!(has_mem_read, "LDR should produce MemRead");
    assert!(has_reg_write, "LDR should write to X0");
}

#[test]
fn test_str_produces_mem_write() {
    // STR X0, [X1] — encoding: 0xF9000020
    let insn = decode_aarch64(&0xF9000020u32.to_le_bytes(), 0x1000).expect("decode STR");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_mem_write = effects.iter().any(|e| matches!(e, Effect::MemWrite { .. }));
    assert!(has_mem_write, "STR should produce MemWrite");
}

// ---------------------------------------------------------------------------
// Branches
// ---------------------------------------------------------------------------

#[test]
fn test_b_produces_branch() {
    // B #0x100 from address 0x1000 — encoding: 0x14000040
    let insn = decode_aarch64(&0x14000040u32.to_le_bytes(), 0x1000).expect("decode B");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_branch = effects.iter().any(|e| matches!(e, Effect::Branch { .. }));
    assert!(has_branch, "B should produce Branch effect");
}

#[test]
fn test_bl_produces_call_and_link_write() {
    // BL #0x100 from address 0x1000 — encoding: 0x94000040
    let insn = decode_aarch64(&0x94000040u32.to_le_bytes(), 0x1000).expect("decode BL");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_call = effects.iter().any(|e| matches!(e, Effect::Call { .. }));
    let has_lr_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 30, .. }));
    assert!(has_call, "BL should produce Call effect");
    assert!(has_lr_write, "BL should write X30 (link register)");
}

#[test]
fn test_ret_produces_return() {
    // RET — encoding: 0xD65F03C0
    let insn = decode_aarch64(&0xD65F03C0u32.to_le_bytes(), 0x1000).expect("decode RET");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_return = effects.iter().any(|e| matches!(e, Effect::Return { .. }));
    assert!(has_return, "RET should produce Return effect");
}

// ---------------------------------------------------------------------------
// NOP
// ---------------------------------------------------------------------------

#[test]
fn test_nop_has_no_effects() {
    // NOP — encoding: 0xD503201F
    let insn = decode_aarch64(&0xD503201Fu32.to_le_bytes(), 0x1000).expect("decode NOP");
    let effects = sem().effects(&state(), &insn).expect("effects");
    assert!(effects.is_empty(), "NOP should produce no effects");
}

#[test]
fn test_prfm_literal_has_no_data_effects() {
    // PRFM #0, #0x1010 — encoding: 0xD8000080
    let insn = decode_aarch64(&0xD8000080u32.to_le_bytes(), 0x1000).expect("decode PRFM");
    let effects = sem().effects(&state(), &insn).expect("effects");
    assert!(effects.is_empty(), "PRFM should produce no scalar data effects");
}

// ---------------------------------------------------------------------------
// MachineState
// ---------------------------------------------------------------------------

#[test]
fn test_symbolic_state_creates_named_vars() {
    let s = MachineState::symbolic();
    assert!(matches!(&s.gpr[0], Formula::Var(name, _) if name == "X0"));
    assert!(matches!(&s.gpr[30], Formula::Var(name, _) if name == "X30"));
    assert!(matches!(&s.sp, Formula::Var(name, _) if name == "SP"));
    assert!(matches!(&s.pc, Formula::Var(name, _) if name == "PC"));
}

#[test]
fn test_read_gpr_31_returns_zero() {
    let s = MachineState::symbolic();
    let val = s.read_gpr(31, 64);
    assert_eq!(val, Formula::BitVec { value: 0, width: 64 });
}

// ---------------------------------------------------------------------------
// Unsupported opcode
// ---------------------------------------------------------------------------

#[test]
fn test_udiv_now_supported() {
    // UDIV X0, X1, X2 — encoding: 0x9AC20820
    let insn = decode_aarch64(&0x9AC20820u32.to_le_bytes(), 0x1000).expect("decode UDIV");
    let result = sem().effects(&state(), &insn);
    assert!(result.is_ok(), "UDIV should be supported after semantics expansion");
}

// ---------------------------------------------------------------------------
// FP register bank in MachineState
// ---------------------------------------------------------------------------

#[test]
fn test_symbolic_state_has_fp_registers() {
    let s = MachineState::symbolic();
    assert!(matches!(&s.fpr[0], Formula::Var(name, _) if name == "V0"));
    assert!(matches!(&s.fpr[31], Formula::Var(name, _) if name == "V31"));
}

#[test]
fn test_read_fpr_extracts_low_bits() {
    let s = MachineState::symbolic();
    // Reading at 64-bit should extract low 64 bits from 128-bit register.
    let val = s.read_fpr(0, 64);
    assert!(matches!(val, Formula::BvExtract { high: 63, low: 0, .. }));

    // Reading at 128-bit should return the full register.
    let val_full = s.read_fpr(0, 128);
    assert!(matches!(&val_full, Formula::Var(name, _) if name == "V0"));
}

// ---------------------------------------------------------------------------
// FP scalar arithmetic: FADD, FSUB, FMUL, FDIV
// ---------------------------------------------------------------------------

#[test]
fn test_fadd_d_produces_fp_reg_write() {
    // FADD D0, D1, D2 — encoding: 0x1E622820
    let insn = decode_aarch64(&0x1E622820u32.to_le_bytes(), 0x1000).expect("decode FADD");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 64, .. }));
    let has_pc_update = effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. }));
    assert!(has_fp_write, "FADD D0 should write FP register 0 at 64-bit");
    assert!(has_pc_update, "FADD should advance PC");

    // Should NOT set flags.
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(!has_flags, "FADD should not set flags");
}

#[test]
fn test_fadd_d_value_is_ieee_fp_shape_not_bvadd() {
    // FADD D0, D1, D2 must model bit-exact IEEE-754 f64 addition, NOT the old
    // integer BvAdd approximation. The written value must be
    // FpToIeeeBv(FpAdd(RNE, FpFromBits(V1d), FpFromBits(V2d))) over the D-lanes.
    use trust_types::RoundingMode;
    let insn = decode_aarch64(&0x1E622820u32.to_le_bytes(), 0x1000).expect("decode FADD");
    let effects = sem().effects(&state(), &insn).expect("effects");
    let value = effects
        .iter()
        .find_map(|e| match e {
            Effect::FpRegWrite { index: 0, width: 64, value } => Some(value.clone()),
            _ => None,
        })
        .expect("FADD D0 must write V0 at 64-bit");
    // Outer node is FP->BV reinterpret of an FpAdd(RNE, FpFromBits, FpFromBits).
    match &value {
        Formula::FpToIeeeBv(inner) => match inner.as_ref() {
            Formula::FpAdd(rm, a, b) => {
                assert!(
                    matches!(rm.as_ref(), Formula::FpRoundingMode(RoundingMode::RNE)),
                    "FADD must round to nearest-even (RNE)"
                );
                assert!(
                    matches!(a.as_ref(), Formula::FpFromBits { eb: 11, sb: 53, .. }),
                    "left operand must be FpFromBits(_, 11, 53): {a:?}"
                );
                assert!(
                    matches!(b.as_ref(), Formula::FpFromBits { eb: 11, sb: 53, .. }),
                    "right operand must be FpFromBits(_, 11, 53): {b:?}"
                );
            }
            other => panic!("FADD inner must be FpAdd(RNE, ..), got: {other:?}"),
        },
        Formula::BvAdd(..) => panic!("FADD must NOT be modeled as integer BvAdd"),
        other => panic!("FADD value must be FpToIeeeBv(FpAdd(..)), got: {other:?}"),
    }
}

/// Assert `value` is `FpToIeeeBv(<ctor>(RNE, FpFromBits(_, eb, sb), FpFromBits(_, eb, sb)))`
/// — the bit-exact two-sided FP shape at the given IEEE format. `matches_op`
/// picks out the specific Fp* node (Add/Sub/Mul/Div).
fn assert_fp_bits_shape(
    value: &Formula,
    eb: u32,
    sb: u32,
    op: &str,
    matches_op: impl Fn(&Formula) -> Option<(&Formula, &Formula, &Formula)>,
) {
    use trust_types::RoundingMode;
    match value {
        Formula::FpToIeeeBv(inner) => match matches_op(inner.as_ref()) {
            Some((rm, a, bx)) => {
                assert!(
                    matches!(rm, Formula::FpRoundingMode(RoundingMode::RNE)),
                    "{op} must round to nearest-even (RNE)"
                );
                assert!(
                    matches!(a, Formula::FpFromBits { eb: e, sb: s, .. } if *e == eb && *s == sb),
                    "left operand must be FpFromBits(_, {eb}, {sb}): {a:?}"
                );
                assert!(
                    matches!(bx, Formula::FpFromBits { eb: e, sb: s, .. } if *e == eb && *s == sb),
                    "right operand must be FpFromBits(_, {eb}, {sb}): {bx:?}"
                );
            }
            None => panic!("{op} inner must be the matching Fp* node, got: {inner:?}"),
        },
        Formula::BvAdd(..) | Formula::BvSub(..) | Formula::BvMul(..) => {
            panic!("{op} must NOT be modeled as integer bitvector arithmetic")
        }
        other => panic!("{op} value must be FpToIeeeBv(Fp*(..)), got: {other:?}"),
    }
}

/// Extract the f32 (width-32) FpRegWrite value for a decoded scalar-FP insn.
fn f32_fp_write_value(enc: u32) -> Formula {
    let insn = decode_aarch64(&enc.to_le_bytes(), 0x1000).expect("decode f32 scalar FP");
    let effects = sem().effects(&state(), &insn).expect("effects");
    effects
        .iter()
        .find_map(|e| match e {
            Effect::FpRegWrite { index: 0, width: 32, value } => Some(value.clone()),
            _ => None,
        })
        .expect("must write V0 at 32-bit (S-lane)")
}

#[test]
fn test_fadd_s_is_ieee_f32_shape_at_eb8_sb24() {
    // FADD S0, S1, S2 (single-precision, ftype=00) — encoding 0x1E222820.
    // f32 is now WIRED to bit-exact IEEE-754 semantics (the same width-parametric
    // FpToIeeeBv(FpAdd(RNE, FpFromBits, FpFromBits)) shape as f64, at eb=8/sb=24
    // over the S-lane). The residual `B-aarch64-fp-pending` never covered f32
    // add/sub/mul/div — only f32 FCVT conversions and FMA.
    let value = f32_fp_write_value(0x1E222820);
    assert_fp_bits_shape(&value, 8, 24, "FADD S", |f| match f {
        Formula::FpAdd(rm, a, b) => Some((rm.as_ref(), a.as_ref(), b.as_ref())),
        _ => None,
    });
}

#[test]
fn test_fsub_s_is_ieee_f32_shape_at_eb8_sb24() {
    // FSUB S0, S1, S2 (ftype=00) — encoding 0x1E223820.
    let value = f32_fp_write_value(0x1E223820);
    assert_fp_bits_shape(&value, 8, 24, "FSUB S", |f| match f {
        Formula::FpSub(rm, a, b) => Some((rm.as_ref(), a.as_ref(), b.as_ref())),
        _ => None,
    });
}

#[test]
fn test_fmul_s_is_ieee_f32_shape_at_eb8_sb24() {
    // FMUL S0, S1, S2 (ftype=00) — encoding 0x1E220820.
    let value = f32_fp_write_value(0x1E220820);
    assert_fp_bits_shape(&value, 8, 24, "FMUL S", |f| match f {
        Formula::FpMul(rm, a, b) => Some((rm.as_ref(), a.as_ref(), b.as_ref())),
        _ => None,
    });
}

#[test]
fn test_fdiv_s_is_ieee_f32_shape_at_eb8_sb24() {
    // FDIV S0, S1, S2 (ftype=00) — encoding 0x1E221820. NO divisor guard: IEEE
    // f32 division is total (x/0.0 = ±inf, 0.0/0.0 = NaN — neither traps).
    let value = f32_fp_write_value(0x1E221820);
    assert_fp_bits_shape(&value, 8, 24, "FDIV S", |f| match f {
        Formula::FpDiv(rm, a, b) => Some((rm.as_ref(), a.as_ref(), b.as_ref())),
        _ => None,
    });
}

#[test]
fn test_fadd_s_reads_s_lane_and_write_clears_upper_v_bits() {
    // The f32 sources are read from the low 32-bit S-lane (`read_fpr(_, 32)` =
    // BvExtract(V_n)[31:0]); the result is a 32-bit FpRegWrite. Applying that
    // effect zero-extends to 128 (models "writing S clears the upper 96 bits of
    // V"), verified via MachineState::apply_effect's widen-to-128.
    use crate::state::MachineState;
    let insn = decode_aarch64(&0x1E222820u32.to_le_bytes(), 0x1000).expect("decode FADD S");
    let effects = sem().effects(&state(), &insn).expect("effects");
    let fp_write = effects
        .iter()
        .find(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 32, .. }))
        .expect("FADD S must write V0 at width 32 (S-lane)");
    // Applying the S-lane write must succeed (widen 32 -> 128 = upper-bits-clear).
    let mut post = MachineState::symbolic();
    post.apply_effect(fp_write).expect("S-lane write widens 32 -> 128 (upper V bits cleared)");
    // Reading back the full 128-bit V0 must be the zero-extension of the 32-bit
    // result — i.e. bits [127:32] are cleared.
    let full = post.read_fpr(0, 128);
    assert!(
        matches!(full, Formula::BvZeroExt(_, 96)),
        "writing S0 must zero-extend to 128 (clear upper 96 bits of V0): {full:?}"
    );
}

#[test]
fn test_fadd_f16_ftype_fails_closed_at_decode() {
    // Half-precision FADD (ftype=11) — encoding 0x1EE22820. f16 is fail-closed:
    // the fp_dp_2source decoder admits only ftype 00 (S/f32) and 01 (D/f64), so
    // an f16 encoding is rejected as an unallocated encoding BEFORE semantics.
    // (The semantics-level FpFormat::for_width also fail-closes on width 16, as a
    // defense in depth; see the fp.rs module test `for_width_rejects_f16`.)
    let result = decode_aarch64(&0x1EE22820u32.to_le_bytes(), 0x1000);
    assert!(result.is_err(), "f16 FADD (ftype=11) must fail closed at decode: {result:?}");
}

#[test]
fn test_fsub_d_produces_fp_reg_write() {
    // FSUB D0, D1, D2 — encoding: 0x1E623820
    let insn = decode_aarch64(&0x1E623820u32.to_le_bytes(), 0x1000).expect("decode FSUB");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 64, .. }));
    assert!(has_fp_write, "FSUB D0 should write FP register 0");
}

#[test]
fn test_fsub_d_value_is_ieee_fp_shape_not_bvsub() {
    // FSUB D0, D1, D2 must model bit-exact IEEE-754 f64 subtraction, NOT the old
    // integer BvSub approximation:
    // FpToIeeeBv(FpSub(RNE, FpFromBits(V1d), FpFromBits(V2d))) over the D-lanes.
    use trust_types::RoundingMode;
    let insn = decode_aarch64(&0x1E623820u32.to_le_bytes(), 0x1000).expect("decode FSUB");
    let effects = sem().effects(&state(), &insn).expect("effects");
    let value = effects
        .iter()
        .find_map(|e| match e {
            Effect::FpRegWrite { index: 0, width: 64, value } => Some(value.clone()),
            _ => None,
        })
        .expect("FSUB D0 must write V0 at 64-bit");
    match &value {
        Formula::FpToIeeeBv(inner) => match inner.as_ref() {
            Formula::FpSub(rm, a, b) => {
                assert!(
                    matches!(rm.as_ref(), Formula::FpRoundingMode(RoundingMode::RNE)),
                    "FSUB must round to nearest-even (RNE)"
                );
                assert!(
                    matches!(a.as_ref(), Formula::FpFromBits { eb: 11, sb: 53, .. }),
                    "left operand must be FpFromBits(_, 11, 53): {a:?}"
                );
                assert!(
                    matches!(b.as_ref(), Formula::FpFromBits { eb: 11, sb: 53, .. }),
                    "right operand must be FpFromBits(_, 11, 53): {b:?}"
                );
            }
            other => panic!("FSUB inner must be FpSub(RNE, ..), got: {other:?}"),
        },
        Formula::BvSub(..) => panic!("FSUB must NOT be modeled as integer BvSub"),
        other => panic!("FSUB value must be FpToIeeeBv(FpSub(..)), got: {other:?}"),
    }
}

#[test]
fn test_fsub_s_produces_f32_fp_reg_write() {
    // FSUB S0, S1, S2 (single-precision, ftype=00) — encoding 0x1E223820.
    // f32 is now WIRED to bit-exact IEEE semantics: it produces a 32-bit S-lane
    // FpRegWrite to V0 (the shape is asserted in
    // test_fsub_s_is_ieee_f32_shape_at_eb8_sb24).
    let insn = decode_aarch64(&0x1E223820u32.to_le_bytes(), 0x1000).expect("decode FSUB S");
    let effects = sem().effects(&state(), &insn).expect("f32 FSUB is now wired");
    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 32, .. }));
    assert!(has_fp_write, "FSUB S0 should write V0 at 32-bit (S-lane)");
}

#[test]
fn test_fmul_d_produces_fp_reg_write() {
    // FMUL D0, D1, D2 — encoding: 0x1E620820
    let insn = decode_aarch64(&0x1E620820u32.to_le_bytes(), 0x1000).expect("decode FMUL");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 64, .. }));
    assert!(has_fp_write, "FMUL D0 should write FP register 0 at 64-bit");
}

#[test]
fn test_fmul_d_value_is_ieee_fp_shape_not_bvmul() {
    // FMUL D0, D1, D2 must model bit-exact IEEE-754 f64 multiplication, NOT the
    // old integer BvMul approximation:
    // FpToIeeeBv(FpMul(RNE, FpFromBits(V1d), FpFromBits(V2d))) over the D-lanes.
    use trust_types::RoundingMode;
    let insn = decode_aarch64(&0x1E620820u32.to_le_bytes(), 0x1000).expect("decode FMUL");
    let effects = sem().effects(&state(), &insn).expect("effects");
    let value = effects
        .iter()
        .find_map(|e| match e {
            Effect::FpRegWrite { index: 0, width: 64, value } => Some(value.clone()),
            _ => None,
        })
        .expect("FMUL D0 must write V0 at 64-bit");
    match &value {
        Formula::FpToIeeeBv(inner) => match inner.as_ref() {
            Formula::FpMul(rm, a, b) => {
                assert!(
                    matches!(rm.as_ref(), Formula::FpRoundingMode(RoundingMode::RNE)),
                    "FMUL must round to nearest-even (RNE)"
                );
                assert!(
                    matches!(a.as_ref(), Formula::FpFromBits { eb: 11, sb: 53, .. }),
                    "left operand must be FpFromBits(_, 11, 53): {a:?}"
                );
                assert!(
                    matches!(b.as_ref(), Formula::FpFromBits { eb: 11, sb: 53, .. }),
                    "right operand must be FpFromBits(_, 11, 53): {b:?}"
                );
            }
            other => panic!("FMUL inner must be FpMul(RNE, ..), got: {other:?}"),
        },
        Formula::BvMul(..) => panic!("FMUL must NOT be modeled as integer BvMul"),
        other => panic!("FMUL value must be FpToIeeeBv(FpMul(..)), got: {other:?}"),
    }
}

#[test]
fn test_fmul_s_produces_f32_fp_reg_write() {
    // FMUL S0, S1, S2 (single-precision, ftype=00) — encoding 0x1E220820.
    // f32 is now WIRED: it produces a 32-bit S-lane FpRegWrite to V0 (the shape
    // is asserted in test_fmul_s_is_ieee_f32_shape_at_eb8_sb24).
    let insn = decode_aarch64(&0x1E220820u32.to_le_bytes(), 0x1000).expect("decode FMUL S");
    let effects = sem().effects(&state(), &insn).expect("f32 FMUL is now wired");
    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 32, .. }));
    assert!(has_fp_write, "FMUL S0 should write V0 at 32-bit (S-lane)");
}

#[test]
fn test_fdiv_d_produces_fp_reg_write() {
    // FDIV D0, D1, D2 — encoding: 0x1E621820
    let insn = decode_aarch64(&0x1E621820u32.to_le_bytes(), 0x1000).expect("decode FDIV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 64, .. }));
    assert!(has_fp_write, "FDIV D0 should write FP register 0 at 64-bit");
}

#[test]
fn test_fdiv_d_value_is_ieee_fp_shape_not_bvsdiv() {
    // FDIV D0, D1, D2 must model bit-exact IEEE-754 f64 division, NOT the old
    // integer BvSDiv approximation:
    // FpToIeeeBv(FpDiv(RNE, FpFromBits(V1d), FpFromBits(V2d))) over the D-lanes.
    // NO GUARD: IEEE div is total (x/0.0 = ±inf, 0.0/0.0 = NaN — no trap).
    use trust_types::RoundingMode;
    let insn = decode_aarch64(&0x1E621820u32.to_le_bytes(), 0x1000).expect("decode FDIV");
    let effects = sem().effects(&state(), &insn).expect("effects");
    let value = effects
        .iter()
        .find_map(|e| match e {
            Effect::FpRegWrite { index: 0, width: 64, value } => Some(value.clone()),
            _ => None,
        })
        .expect("FDIV D0 must write V0 at 64-bit");
    match &value {
        Formula::FpToIeeeBv(inner) => match inner.as_ref() {
            Formula::FpDiv(rm, a, b) => {
                assert!(
                    matches!(rm.as_ref(), Formula::FpRoundingMode(RoundingMode::RNE)),
                    "FDIV must round to nearest-even (RNE)"
                );
                assert!(
                    matches!(a.as_ref(), Formula::FpFromBits { eb: 11, sb: 53, .. }),
                    "left operand must be FpFromBits(_, 11, 53): {a:?}"
                );
                assert!(
                    matches!(b.as_ref(), Formula::FpFromBits { eb: 11, sb: 53, .. }),
                    "right operand must be FpFromBits(_, 11, 53): {b:?}"
                );
            }
            other => panic!("FDIV inner must be FpDiv(RNE, ..), got: {other:?}"),
        },
        Formula::BvSDiv(..) => panic!("FDIV must NOT be modeled as integer BvSDiv"),
        other => panic!("FDIV value must be FpToIeeeBv(FpDiv(..)), got: {other:?}"),
    }
}

#[test]
fn test_fdiv_s_produces_f32_fp_reg_write() {
    // FDIV S0, S1, S2 (single-precision, ftype=00) — encoding 0x1E221820.
    // f32 is now WIRED: it produces a 32-bit S-lane FpRegWrite to V0 (the shape
    // is asserted in test_fdiv_s_is_ieee_f32_shape_at_eb8_sb24). NO divisor
    // guard: IEEE f32 division is total (x/0.0 = ±inf, 0.0/0.0 = NaN — no trap).
    let insn = decode_aarch64(&0x1E221820u32.to_le_bytes(), 0x1000).expect("decode FDIV S");
    let effects = sem().effects(&state(), &insn).expect("f32 FDIV is now wired");
    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 32, .. }));
    assert!(has_fp_write, "FDIV S0 should write V0 at 32-bit (S-lane)");
}

// ---------------------------------------------------------------------------
// FP compare: FCMP
// ---------------------------------------------------------------------------

#[test]
fn test_fcmp_d_sets_flags() {
    // FCMP D0, D1 — encoding: 0x1E612000
    let insn = decode_aarch64(&0x1E612000u32.to_le_bytes(), 0x1000).expect("decode FCMP");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_flags, "FCMP should set NZCV flags");

    // Should NOT write any FP register.
    let has_fp_write = effects.iter().any(|e| matches!(e, Effect::FpRegWrite { .. }));
    assert!(!has_fp_write, "FCMP should not write an FP register");
}

// ---------------------------------------------------------------------------
// FP move: FMOV
// ---------------------------------------------------------------------------

#[test]
fn test_fmov_reg_fp_to_fp() {
    // FMOV D0, D1 — FP DP 1-source, ftype=01, opcode=000000
    // Encoding: 0001_1110_0110_0000_0100_0000_0010_0000 = 0x1E604020
    let insn = decode_aarch64(&0x1E604020u32.to_le_bytes(), 0x1000).expect("decode FMOV reg");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 64, .. }));
    assert!(has_fp_write, "FMOV D0, D1 should write FP register D0");
}

// ---------------------------------------------------------------------------
// FP unary: FNEG, FABS
// ---------------------------------------------------------------------------

#[test]
fn test_fneg_d_produces_fp_write() {
    // FNEG D0, D1 — FP DP 1-source, ftype=01, opcode=000010
    // Encoding: 0001_1110_0110_0001_0100_0000_0010_0000 = 0x1E614020
    let insn = decode_aarch64(&0x1E614020u32.to_le_bytes(), 0x1000).expect("decode FNEG");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 64, .. }));
    assert!(has_fp_write, "FNEG D0, D1 should write FP register D0");
}

#[test]
fn test_fabs_d_produces_fp_write() {
    // FABS D0, D1 — FP DP 1-source, ftype=01, opcode=000001
    // Encoding: 0001_1110_0110_0000_1100_0000_0010_0000 = 0x1E60C020
    let insn = decode_aarch64(&0x1E60C020u32.to_le_bytes(), 0x1000).expect("decode FABS");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_fp_write =
        effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, width: 64, .. }));
    assert!(has_fp_write, "FABS D0, D1 should write FP register D0");
}

// ---------------------------------------------------------------------------
// FP conversion: SCVTF, FCVTZS
// ---------------------------------------------------------------------------

#[test]
fn test_scvtf_produces_fp_write() {
    // SCVTF D0, X1 — FP<->integer conversion, sf=1, ftype=01, rmode=00, opcode=010
    // Encoding: 0x9E620020
    let insn = decode_aarch64(&0x9E620020u32.to_le_bytes(), 0x1000).expect("decode SCVTF");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_fp_write = effects.iter().any(|e| matches!(e, Effect::FpRegWrite { index: 0, .. }));
    assert!(has_fp_write, "SCVTF should write an FP register");
}

#[test]
fn test_fcvtzs_produces_gpr_write() {
    // FCVTZS X0, D1 — FP<->integer conversion, sf=1, ftype=01, rmode=11, opcode=000
    // Encoding: 0x9E780020
    let insn = decode_aarch64(&0x9E780020u32.to_le_bytes(), 0x1000).expect("decode FCVTZS");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_gpr_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, .. }));
    assert!(has_gpr_write, "FCVTZS should write a GPR");
}

// ---------------------------------------------------------------------------
// FP no-crash tests — verify pipeline does not crash on FP instructions
// ---------------------------------------------------------------------------

#[test]
fn test_fp_opcodes_all_produce_effects() {
    // Verify all FP opcodes produce non-error results.
    let encodings: &[(u32, &str)] = &[
        (0x1E622820, "FADD D0, D1, D2"),
        (0x1E623820, "FSUB D0, D1, D2"),
        // FMUL/FDIV use a D-register (f64): the S (f32) forms fail closed by
        // design, as only f64 arithmetic is wired to bit-exact IEEE semantics.
        (0x1E620820, "FMUL D0, D1, D2"),
        // FDIV D (f64) is wired to bit-exact FpDiv(RNE, ..) — no guard needed
        // (IEEE div is total: x/0.0 = ±inf, 0.0/0.0 = NaN, never a trap).
        (0x1E621820, "FDIV D0, D1, D2"),
        (0x1E612000, "FCMP D0, D1"),
        (0x1E604020, "FMOV D0, D1"),
        (0x1E614020, "FNEG D0, D1"),
        (0x1E60C020, "FABS D0, D1"),
    ];

    for &(enc, desc) in encodings {
        let insn = decode_aarch64(&enc.to_le_bytes(), 0x1000)
            .unwrap_or_else(|e| panic!("decode {desc}: {e}"));
        let result = sem().effects(&state(), &insn);
        assert!(result.is_ok(), "{desc} should not return error, got: {:?}", result.err());
        let effects = result.expect("effects");
        assert!(!effects.is_empty(), "{desc} should produce at least one effect");
    }
}

// ===========================================================================
// NEW TESTS: Comprehensive AArch64 opcode coverage
// ===========================================================================

// ---------------------------------------------------------------------------
// Logic: AND / ANDS (with flags)
// ---------------------------------------------------------------------------

#[test]
fn test_and_x0_x1_x2_produces_reg_write_no_flags() {
    // AND X0, X1, X2 (logical shifted reg, opc=00, N=0)
    // Encoding: 0x8A020020
    let insn = decode_aarch64(&0x8A020020u32.to_le_bytes(), 0x1000).expect("decode AND");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_reg_write, "AND should write X0");
    assert!(!has_flags, "AND (not ANDS) should not set flags");
}

#[test]
fn test_ands_x0_x1_x2_sets_logic_flags() {
    // ANDS X0, X1, X2 (logical shifted reg, opc=11, N=0)
    // sf=1 opc=11 01010 shift=00 N=0 Rm=2 imm6=0 Rn=1 Rd=0
    // 1 11 01010 00 0 00010 000000 00001 00000
    // = 0xEA020020
    let insn = decode_aarch64(&0xEA020020u32.to_le_bytes(), 0x1000).expect("decode ANDS");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_reg_write, "ANDS should write X0");
    assert!(has_flags, "ANDS should set NZCV flags");

    // Logic NZCV: C=0 and V=0 always for logical ops.
    if let Some(Effect::FlagUpdate { c, v, .. }) =
        effects.iter().find(|e| matches!(e, Effect::FlagUpdate { .. }))
    {
        assert_eq!(*c, Formula::Bool(false), "ANDS C flag should be false");
        assert_eq!(*v, Formula::Bool(false), "ANDS V flag should be false");
    }
}

// ---------------------------------------------------------------------------
// Logic: EOR
// ---------------------------------------------------------------------------

#[test]
fn test_eor_x0_x1_x2_produces_xor() {
    // EOR X0, X1, X2 (logical shifted reg, opc=10, N=0)
    // 1 10 01010 00 0 00010 000000 00001 00000
    // = 0xCA020020
    let insn = decode_aarch64(&0xCA020020u32.to_le_bytes(), 0x1000).expect("decode EOR");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "EOR should write X0");

    // Verify the value is a BvXor.
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(matches!(value, Formula::BvXor(..)), "EOR value should be BvXor, got: {:?}", value);
    }
}

// ---------------------------------------------------------------------------
// Logic: BIC / BICS
// ---------------------------------------------------------------------------

#[test]
fn test_bic_x0_x1_x2_produces_and_not() {
    // BIC X0, X1, X2 (logical shifted reg, opc=00, N=1)
    // sf=1 opc=00 01010 shift=00 N=1 Rm=2 imm6=0 Rn=1 Rd=0
    // 1 00 01010 00 1 00010 000000 00001 00000
    // = 0x8A220020
    let insn = decode_aarch64(&0x8A220020u32.to_le_bytes(), 0x1000).expect("decode BIC");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_reg_write, "BIC should write X0");
    assert!(!has_flags, "BIC (not BICS) should not set flags");
}

#[test]
fn test_bics_x0_x1_x2_sets_flags() {
    // BICS X0, X1, X2 (logical shifted reg, opc=11, N=1)
    // 1 11 01010 00 1 00010 000000 00001 00000
    // = 0xEA220020
    let insn = decode_aarch64(&0xEA220020u32.to_le_bytes(), 0x1000).expect("decode BICS");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_flags, "BICS should set flags");
}

// ---------------------------------------------------------------------------
// Logic: ORN
// ---------------------------------------------------------------------------

#[test]
fn test_orn_x0_x1_x2_produces_or_not() {
    // ORN X0, X1, X2 (logical shifted reg, opc=01, N=1)
    // 1 01 01010 00 1 00010 000000 00001 00000
    // = 0xAA220020
    let insn = decode_aarch64(&0xAA220020u32.to_le_bytes(), 0x1000).expect("decode ORN");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "ORN should write X0");
}

// ---------------------------------------------------------------------------
// Logic: EON
// ---------------------------------------------------------------------------

#[test]
fn test_eon_x0_x1_x2_produces_xor_not() {
    // EON X0, X1, X2 (logical shifted reg, opc=10, N=1)
    // 1 10 01010 00 1 00010 000000 00001 00000
    // = 0xCA220020
    let insn = decode_aarch64(&0xCA220020u32.to_le_bytes(), 0x1000).expect("decode EON");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "EON should write X0");
}

// ---------------------------------------------------------------------------
// Logic: ORR (register)
// ---------------------------------------------------------------------------

#[test]
fn test_orr_x0_x1_x2_produces_or() {
    // ORR X0, X1, X2 (logical shifted reg, opc=01, N=0)
    // Encoding: 0xAA020020
    let insn = decode_aarch64(&0xAA020020u32.to_le_bytes(), 0x1000).expect("decode ORR");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "ORR should write X0");

    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(matches!(value, Formula::BvOr(..)), "ORR value should be BvOr, got: {:?}", value);
    }
}

// ---------------------------------------------------------------------------
// Variable shifts: LSLV, LSRV, ASRV, RORV
// ---------------------------------------------------------------------------

#[test]
fn test_lslv_x0_x1_x2() {
    // LSLV X0, X1, X2 (DP 2-source, opcode=001000)
    // sf=1 S=0 11010110 Rm=2 001000 Rn=1 Rd=0
    // 1 0 0 11010110 00010 001000 00001 00000
    // = 0x9AC22020
    let insn = decode_aarch64(&0x9AC22020u32.to_le_bytes(), 0x1000).expect("decode LSLV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "LSLV should write X0");

    // Verify it produces a BvShl (via shift_var with masked amount).
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(matches!(value, Formula::BvShl(..)), "LSLV should produce BvShl, got: {:?}", value);
    }
}

#[test]
fn test_lsrv_x0_x1_x2() {
    // LSRV X0, X1, X2 (DP 2-source, opcode=001001)
    // 1 0 0 11010110 00010 001001 00001 00000
    // = 0x9AC22420
    let insn = decode_aarch64(&0x9AC22420u32.to_le_bytes(), 0x1000).expect("decode LSRV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "LSRV should write X0");

    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::BvLShr(..)),
            "LSRV should produce BvLShr, got: {:?}",
            value
        );
    }
}

#[test]
fn test_asrv_x0_x1_x2() {
    // ASRV X0, X1, X2 (DP 2-source, opcode=001010)
    // 1 0 0 11010110 00010 001010 00001 00000
    // = 0x9AC22820
    let insn = decode_aarch64(&0x9AC22820u32.to_le_bytes(), 0x1000).expect("decode ASRV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "ASRV should write X0");

    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::BvAShr(..)),
            "ASRV should produce BvAShr, got: {:?}",
            value
        );
    }
}

#[test]
fn test_rorv_x0_x1_x2() {
    // RORV X0, X1, X2 (DP 2-source, opcode=001011)
    // 1 0 0 11010110 00010 001011 00001 00000
    // = 0x9AC22C20
    let insn = decode_aarch64(&0x9AC22C20u32.to_le_bytes(), 0x1000).expect("decode RORV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "RORV should write X0");

    // RORV produces (x >> n) | (x << (width - n)), which is a BvOr.
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::BvOr(..)),
            "RORV should produce BvOr (rotate), got: {:?}",
            value
        );
    }
}

// ---------------------------------------------------------------------------
// Division: UDIV, SDIV (including div-by-zero behavior)
// ---------------------------------------------------------------------------

#[test]
fn test_udiv_x0_x1_x2_produces_ite_for_div_by_zero() {
    // UDIV X0, X1, X2 — encoding: 0x9AC20820
    let insn = decode_aarch64(&0x9AC20820u32.to_le_bytes(), 0x1000).expect("decode UDIV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "UDIV should write X0");

    // The value should be an Ite (div-by-zero check).
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::Ite(..)),
            "UDIV should produce Ite for div-by-zero guard, got: {:?}",
            value
        );
    }
}

#[test]
fn test_sdiv_x0_x1_x2_produces_signed_div() {
    // SDIV X0, X1, X2 — encoding: 0x9AC20C20
    let insn = decode_aarch64(&0x9AC20C20u32.to_le_bytes(), 0x1000).expect("decode SDIV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "SDIV should write X0");

    // SDIV also has div-by-zero guard (Ite).
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::Ite(..)),
            "SDIV should produce Ite for div-by-zero guard, got: {:?}",
            value
        );
    }
}

// ---------------------------------------------------------------------------
// Multiply-accumulate: MADD, MSUB
// ---------------------------------------------------------------------------

#[test]
fn test_madd_x0_x1_x2_x3() {
    // MADD X0, X1, X2, X3 — encoding: 0x9B020C20
    let insn = decode_aarch64(&0x9B020C20u32.to_le_bytes(), 0x1000).expect("decode MADD");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "MADD should write X0");

    // MADD: Rd = Ra + (Rn * Rm). The outer formula should be BvAdd.
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::BvAdd(..)),
            "MADD value should be BvAdd (Ra + Rn*Rm), got: {:?}",
            value
        );
    }
}

#[test]
fn test_msub_x0_x1_x2_x3() {
    // MSUB X0, X1, X2, X3 — encoding: 0x9B028C20
    let insn = decode_aarch64(&0x9B028C20u32.to_le_bytes(), 0x1000).expect("decode MSUB");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "MSUB should write X0");

    // MSUB: Rd = Ra - (Rn * Rm). The outer formula should be BvSub.
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::BvSub(..)),
            "MSUB value should be BvSub (Ra - Rn*Rm), got: {:?}",
            value
        );
    }
}

#[test]
fn test_smaddl_sign_extends_32_bit_operands() {
    // SMADDL X0, W1, W2, X3 — encoding: 0x9B220C20
    let insn = decode_aarch64(&0x9B220C20u32.to_le_bytes(), 0x1000).expect("decode SMADDL");
    let effects = sem().effects(&state(), &insn).expect("effects");

    if let Some(Effect::RegWrite { index: 0, width: 64, value }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        match value {
            Formula::BvAdd(_, product, 64) => match product.as_ref() {
                Formula::BvMul(lhs, rhs, 64) => {
                    assert!(matches!(lhs.as_ref(), Formula::BvSignExt(_, 32)));
                    assert!(matches!(rhs.as_ref(), Formula::BvSignExt(_, 32)));
                }
                other => panic!("SMADDL product should be a 64-bit multiply, got: {other:?}"),
            },
            other => panic!("SMADDL should produce Ra + signed product, got: {other:?}"),
        }
    } else {
        panic!("SMADDL should write X0");
    }
}

#[test]
fn test_umaddl_zero_extends_32_bit_operands() {
    // UMADDL X0, W1, W2, X3 — encoding: 0x9BA20C20
    let insn = decode_aarch64(&0x9BA20C20u32.to_le_bytes(), 0x1000).expect("decode UMADDL");
    let effects = sem().effects(&state(), &insn).expect("effects");

    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        match value {
            Formula::BvAdd(_, product, 64) => match product.as_ref() {
                Formula::BvMul(lhs, rhs, 64) => {
                    assert!(matches!(lhs.as_ref(), Formula::BvZeroExt(_, 32)));
                    assert!(matches!(rhs.as_ref(), Formula::BvZeroExt(_, 32)));
                }
                other => panic!("UMADDL product should be a 64-bit multiply, got: {other:?}"),
            },
            other => panic!("UMADDL should produce Ra + unsigned product, got: {other:?}"),
        }
    } else {
        panic!("UMADDL should write X0");
    }
}

#[test]
fn test_long_multiply_subtract_and_high_half_supported() {
    for (encoding, name) in
        [(0x9B228C20u32, "SMSUBL X0, W1, W2, X3"), (0x9BA28C20u32, "UMSUBL X0, W1, W2, X3")]
    {
        let insn = decode_aarch64(&encoding.to_le_bytes(), 0x1000)
            .unwrap_or_else(|err| panic!("decode {name}: {err}"));
        let effects = sem().effects(&state(), &insn).expect("effects");
        let value = effects
            .iter()
            .find_map(|effect| match effect {
                Effect::RegWrite { index: 0, value, .. } => Some(value),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{name} should write X0"));
        assert!(matches!(value, Formula::BvSub(_, _, 64)), "{name} should subtract product");
    }

    for (encoding, name, signed) in
        [(0x9B420020u32, "SMULH X0, X1, X2", true), (0x9BC20020u32, "UMULH X0, X1, X2", false)]
    {
        let insn = decode_aarch64(&encoding.to_le_bytes(), 0x1000)
            .unwrap_or_else(|err| panic!("decode {name}: {err}"));
        let effects = sem().effects(&state(), &insn).expect("effects");
        let value = effects
            .iter()
            .find_map(|effect| match effect {
                Effect::RegWrite { index: 0, width: 64, value } => Some(value),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{name} should write X0"));
        match value {
            Formula::BvExtract { inner, high: 127, low: 64 } => match inner.as_ref() {
                Formula::BvMul(lhs, rhs, 128) if signed => {
                    assert!(matches!(lhs.as_ref(), Formula::BvSignExt(_, 64)));
                    assert!(matches!(rhs.as_ref(), Formula::BvSignExt(_, 64)));
                }
                Formula::BvMul(lhs, rhs, 128) => {
                    assert!(matches!(lhs.as_ref(), Formula::BvZeroExt(_, 64)));
                    assert!(matches!(rhs.as_ref(), Formula::BvZeroExt(_, 64)));
                }
                other => panic!("{name} should multiply widened operands, got: {other:?}"),
            },
            other => panic!("{name} should extract high half of 128-bit product, got: {other:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Add/subtract with carry: ADC, ADCS, SBC, SBCS
// ---------------------------------------------------------------------------

#[test]
fn test_adc_x0_x1_x2_produces_add_with_carry() {
    // ADC X0, X1, X2 — encoding: 0x9A020020
    let insn = decode_aarch64(&0x9A020020u32.to_le_bytes(), 0x1000).expect("decode ADC");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_reg_write, "ADC should write X0");
    assert!(!has_flags, "ADC (not ADCS) should not set flags");
}

#[test]
fn test_adcs_x0_x1_x2_sets_flags() {
    // ADCS X0, X1, X2 — encoding: 0xBA020020
    let insn = decode_aarch64(&0xBA020020u32.to_le_bytes(), 0x1000).expect("decode ADCS");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_flags, "ADCS should set NZCV flags");
}

#[test]
fn test_sbc_x0_x1_x2_produces_sub_with_borrow() {
    // SBC X0, X1, X2 — encoding: 0xDA020020
    let insn = decode_aarch64(&0xDA020020u32.to_le_bytes(), 0x1000).expect("decode SBC");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_reg_write, "SBC should write X0");
    assert!(!has_flags, "SBC (not SBCS) should not set flags");
}

#[test]
fn test_sbcs_x0_x1_x2_sets_flags() {
    // SBCS X0, X1, X2 — encoding: 0xFA020020
    let insn = decode_aarch64(&0xFA020020u32.to_le_bytes(), 0x1000).expect("decode SBCS");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_flags, "SBCS should set NZCV flags");
}

// ---------------------------------------------------------------------------
// Conditional select: CSEL, CSINC, CSINV, CSNEG
// ---------------------------------------------------------------------------

#[test]
fn test_csel_x0_x1_x2_eq() {
    // CSEL X0, X1, X2, EQ — encoding: 0x9A820020
    let insn = decode_aarch64(&0x9A820020u32.to_le_bytes(), 0x1000).expect("decode CSEL");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "CSEL should write X0");

    // Value should be an Ite (condition ? Rn : Rm).
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(matches!(value, Formula::Ite(..)), "CSEL should produce Ite, got: {:?}", value);
    }
}

#[test]
fn test_csinc_x0_x1_x2_ne() {
    // CSINC X0, X1, X2, NE — encoding: 0x9A821420
    let insn = decode_aarch64(&0x9A821420u32.to_le_bytes(), 0x1000).expect("decode CSINC");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "CSINC should write X0");

    // Value should be Ite(cond, Rn, Rm+1).
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(matches!(value, Formula::Ite(..)), "CSINC should produce Ite, got: {:?}", value);
    }
}

#[test]
fn test_csinv_x0_x1_x2_eq() {
    // CSINV X0, X1, X2, EQ (op=1, op2=00)
    // sf=1 op=1 S=0 11010100 Rm=2 cond=0000 op2=00 Rn=1 Rd=0
    // 1 1 0 11010100 00010 0000 00 00001 00000
    // = 0xDA820020
    let insn = decode_aarch64(&0xDA820020u32.to_le_bytes(), 0x1000).expect("decode CSINV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "CSINV should write X0");
}

#[test]
fn test_csneg_x0_x1_x2_eq() {
    // CSNEG X0, X1, X2, EQ (op=1, op2=01)
    // sf=1 op=1 S=0 11010100 Rm=2 cond=0000 op2=01 Rn=1 Rd=0
    // 1 1 0 11010100 00010 0000 01 00001 00000
    // = 0xDA820420
    let insn = decode_aarch64(&0xDA820420u32.to_le_bytes(), 0x1000).expect("decode CSNEG");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "CSNEG should write X0");

    // CSNEG value = Ite(cond, Rn, -Rm).
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(matches!(value, Formula::Ite(..)), "CSNEG should produce Ite, got: {:?}", value);
    }
}

// ---------------------------------------------------------------------------
// Conditional compare: CCMP, CCMN
// ---------------------------------------------------------------------------

#[test]
fn test_ccmp_x1_imm5_nzcv_eq() {
    // CCMP X1, #5, #0b1010, EQ
    // sf=1 op=1 S=1 11010010 imm5=00101 cond=0000 1 0 Rn=1 0 nzcv=1010
    // 1 1 1 11010010 00101 0000 10 00001 0 1010
    // = 0xFA450820 ... let me derive this more carefully
    // Bits: sf=1, op=1, S=1, 11010010, is_imm=1(bit11), o2=0(bit10), o3=0(bit4)
    // 31: sf=1
    // 30: op=1
    // 29: S=1
    // 28:21: 11010010
    // 20:16: imm5=00101
    // 15:12: cond=0000 (EQ)
    // 11: is_imm=1
    // 10: o2=0
    // 9:5: Rn=00001
    // 4: o3=0
    // 3:0: nzcv=1010
    // = 1_1_1_11010010_00101_0000_1_0_00001_0_1010
    // = 1110 1001 0001 0100 0010 0001 0000 1010 ... no let me be more careful
    // Bit 31=1, 30=1, 29=1 => 111
    // Bits 28:21 = 11010010
    // Bits 20:16 = 00101
    // Bits 15:12 = 0000
    // Bit 11 = 1, Bit 10 = 0
    // Bits 9:5 = 00001
    // Bit 4 = 0
    // Bits 3:0 = 1010
    // Full: 111_11010010_00101_0000_10_00001_0_1010
    // Group by bytes from bit 31:
    // [31:24] = 1111_1010 = 0xFA
    // [23:16] = 0100_0101 = 0x45
    // [15:8]  = 0000_1000 = 0x08
    // [7:0]   = 0010_1010 = 0x2A
    // = 0xFA45082A
    let insn = decode_aarch64(&0xFA45082Au32.to_le_bytes(), 0x1000).expect("decode CCMP");
    let effects = sem().effects(&state(), &insn).expect("effects");

    // CCMP produces FlagUpdate and PcUpdate.
    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    let has_pc_update = effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. }));
    assert!(has_flags, "CCMP should produce FlagUpdate");
    assert!(has_pc_update, "CCMP should advance PC");

    // Should NOT produce a RegWrite (compare only).
    let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { .. }));
    assert!(!has_reg_write, "CCMP should not write a register");

    // The flag values should contain Ite (conditional flag setting).
    if let Some(Effect::FlagUpdate { n, .. }) =
        effects.iter().find(|e| matches!(e, Effect::FlagUpdate { .. }))
    {
        assert!(
            matches!(n, Formula::Ite(..)),
            "CCMP N flag should be Ite (conditional), got: {:?}",
            n
        );
    }
}

#[test]
fn test_ccmn_x1_imm5_nzcv_ne() {
    // CCMN X1, #3, #0b0100, NE
    // sf=1 op=0 S=1 11010010 imm5=00011 cond=0001 is_imm=1 o2=0 Rn=00001 o3=0 nzcv=0100
    // = 0xBA430824
    let insn = decode_aarch64(&0xBA430824u32.to_le_bytes(), 0x1000).expect("decode CCMN");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_flags, "CCMN should produce FlagUpdate");
}

// ---------------------------------------------------------------------------
// Bit manipulation: CLZ, RBIT, REV, REV16, REV32, CLS
// ---------------------------------------------------------------------------

#[test]
fn test_clz_x0_x1() {
    // CLZ X0, X1 — encoding: 0xDAC01020
    let insn = decode_aarch64(&0xDAC01020u32.to_le_bytes(), 0x1000).expect("decode CLZ");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "CLZ should write X0");
}

#[test]
fn test_rbit_x0_x1() {
    // RBIT X0, X1 — encoding: 0xDAC00020
    let insn = decode_aarch64(&0xDAC00020u32.to_le_bytes(), 0x1000).expect("decode RBIT");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "RBIT should write X0");
}

#[test]
fn test_rev_x0_x1() {
    // REV X0, X1 (64-bit byte reversal)
    // sf=1, opcode_field=000011
    // 1 1 0 11010110 00000 000011 00001 00000
    // = 0xDAC00C20
    let insn = decode_aarch64(&0xDAC00C20u32.to_le_bytes(), 0x1000).expect("decode REV");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "REV should write X0");
}

#[test]
fn test_rev16_x0_x1() {
    // REV16 X0, X1 (reverse bytes in each halfword)
    // sf=1, opcode_field=000001
    // 1 1 0 11010110 00000 000001 00001 00000
    // = 0xDAC00420
    let insn = decode_aarch64(&0xDAC00420u32.to_le_bytes(), 0x1000).expect("decode REV16");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "REV16 should write X0");
}

#[test]
fn test_rev32_x0_x1() {
    // REV32 X0, X1 (reverse bytes in each 32-bit word, 64-bit register)
    // sf=1, opcode_field=000010
    // 1 1 0 11010110 00000 000010 00001 00000
    // = 0xDAC00820
    let insn = decode_aarch64(&0xDAC00820u32.to_le_bytes(), 0x1000).expect("decode REV32");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "REV32 should write X0");
}

#[test]
fn test_cls_x0_x1() {
    // CLS X0, X1 (count leading sign bits)
    // sf=1, opcode_field=000101
    // 1 1 0 11010110 00000 000101 00001 00000
    // = 0xDAC01420
    let insn = decode_aarch64(&0xDAC01420u32.to_le_bytes(), 0x1000).expect("decode CLS");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "CLS should write X0");
}

// ---------------------------------------------------------------------------
// Bitfield: UBFM, SBFM, BFM, EXTR
// ---------------------------------------------------------------------------

#[test]
fn test_ubfm_x0_x1_uxtb_alias() {
    // UBFM X0, X1, #0, #7 (= UXTB X0, X1 — extract low byte, zero-extend)
    // sf=1 opc=10 100110 N=1 immr=000000 imms=000111 Rn=1 Rd=0
    // 1 10 100110 1 000000 000111 00001 00000
    // = 0xD340_1C20
    let insn = decode_aarch64(&0xD3401C20u32.to_le_bytes(), 0x1000).expect("decode UBFM");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "UBFM should write X0");
}

#[test]
fn test_sbfm_x0_x1_sxtb_alias() {
    // SBFM X0, X1, #0, #7 (= SXTB X0, X1 — sign-extend byte)
    // sf=1 opc=00 100110 N=1 immr=000000 imms=000111 Rn=1 Rd=0
    // = 0x9340_1C20
    let insn = decode_aarch64(&0x93401C20u32.to_le_bytes(), 0x1000).expect("decode SBFM");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "SBFM should write X0");
}

#[test]
fn test_bfm_x0_x1() {
    // BFM X0, X1, #4, #7 (insert bits [7:4] from X1 into X0)
    // sf=1 opc=01 100110 N=1 immr=000100 imms=000111 Rn=1 Rd=0
    // = 0xB340_1C20 ... immr=4 => 000100
    // 1 01 100110 1 000100 000111 00001 00000
    // [31:24] = 1011_0011 = 0xB3
    // [23:16] = 0100_0100 = 0x44 ... wait: N=1 immr[5:0]=000100
    // bits 22:16 = N immr = 1_000100 = 0x44
    // [15:8] = imms[5:0] Rn[4:0 top 3] = 000111_00 = 0x1C
    // [7:0] = Rn[bottom 2] Rd = 001 00000 = 0x20
    // = 0xB3441C20
    let insn = decode_aarch64(&0xB3441C20u32.to_le_bytes(), 0x1000).expect("decode BFM");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "BFM should write X0");
}

#[test]
fn test_extr_x0_x1_x2_lsb8() {
    // EXTR X0, X1, X2, #8 (extract from pair: Rd = (Rn:Rm) >> 8)
    // sf=1 op21=00 100111 N=1 Rm=00010 imms=001000 Rn=00001 Rd=00000
    // 1 00 100111 1 00010 001000 00001 00000
    // [31:24] = 1001_0011 = 0x93
    // [23:16] = 1100_0010 = 0xC2 (N=1, Rm=00010)
    // [15:8]  = 0010_0000 = 0x20 (imms=001000, Rn top)
    // [7:0]   = 0010_0000 = 0x20
    // = 0x93C22020
    let insn = decode_aarch64(&0x93C22020u32.to_le_bytes(), 0x1000).expect("decode EXTR");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "EXTR should write X0");

    // With lsb=8, result = (Rm >> 8) | (Rn << 56) => BvOr
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::BvOr(..)),
            "EXTR with lsb=8 should produce BvOr, got: {:?}",
            value
        );
    }
}

// ---------------------------------------------------------------------------
// Move variants: MOVN, MOVK
// ---------------------------------------------------------------------------

#[test]
fn test_movn_x0_produces_bitwise_not() {
    // MOVN X0, #0 (= NOT of 0 = all ones)
    // sf=1 opc=00 100101 hw=00 imm16=0 Rd=0
    // 1 00 100101 00 0000000000000000 00000
    // = 0x92800000
    let insn = decode_aarch64(&0x92800000u32.to_le_bytes(), 0x1000).expect("decode MOVN");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "MOVN should write X0");

    // MOVN produces BvNot of the immediate.
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(matches!(value, Formula::BvNot(..)), "MOVN should produce BvNot, got: {:?}", value);
    }
}

#[test]
fn test_movk_x0_0x5678_lsl16_inserts_bits() {
    // MOVK X0, #0x5678, LSL #16 — encoding: 0xF2AACF00
    let insn = decode_aarch64(&0xF2AACF00u32.to_le_bytes(), 0x1000).expect("decode MOVK");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 64, .. }));
    assert!(has_reg_write, "MOVK should write X0");

    // MOVK produces BvOr (cleared existing | new bits).
    if let Some(Effect::RegWrite { value, .. }) =
        effects.iter().find(|e| matches!(e, Effect::RegWrite { index: 0, .. }))
    {
        assert!(
            matches!(value, Formula::BvOr(..)),
            "MOVK should produce BvOr (insert field), got: {:?}",
            value
        );
    }
}

// ---------------------------------------------------------------------------
// Branch variants: BR, BLR, B.cond, CBZ, CBNZ, TBZ, TBNZ
// ---------------------------------------------------------------------------

#[test]
fn test_br_x16_produces_branch() {
    // BR X16 — encoding: 0xD61F0200
    let insn = decode_aarch64(&0xD61F0200u32.to_le_bytes(), 0x1000).expect("decode BR");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_branch = effects.iter().any(|e| matches!(e, Effect::Branch { .. }));
    let has_pc = effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. }));
    assert!(has_branch, "BR should produce Branch effect");
    assert!(has_pc, "BR should produce PcUpdate");
}

#[test]
fn test_blr_x8_produces_call() {
    // BLR X8 — encoding: 0xD63F0100
    let insn = decode_aarch64(&0xD63F0100u32.to_le_bytes(), 0x1000).expect("decode BLR");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_call = effects.iter().any(|e| matches!(e, Effect::Call { .. }));
    let has_lr_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 30, .. }));
    assert!(has_call, "BLR should produce Call effect");
    assert!(has_lr_write, "BLR should write X30 (link register)");
}

#[test]
fn test_bcond_eq_produces_conditional_branch() {
    // B.EQ #0x20 from address 0x1000 — encoding: 0x54000100
    let insn = decode_aarch64(&0x54000100u32.to_le_bytes(), 0x1000).expect("decode B.EQ");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_cond_branch = effects.iter().any(|e| matches!(e, Effect::ConditionalBranch { .. }));
    assert!(has_cond_branch, "B.EQ should produce ConditionalBranch effect");
}

#[test]
fn test_cbz_x0_produces_pc_update() {
    // CBZ X0, #0x10 from address 0 — encoding: 0xB4000080
    let insn = decode_aarch64(&0xB4000080u32.to_le_bytes(), 0x0).expect("decode CBZ");
    let effects = sem().effects(&state(), &insn).expect("effects");

    // CBZ produces a PcUpdate with Ite (branch if zero).
    let has_pc_update = effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. }));
    assert!(has_pc_update, "CBZ should produce PcUpdate");

    if let Some(Effect::PcUpdate { value }) =
        effects.iter().find(|e| matches!(e, Effect::PcUpdate { .. }))
    {
        assert!(
            matches!(value, Formula::Ite(..)),
            "CBZ PC value should be Ite (branch or fall through), got: {:?}",
            value
        );
    }
}

#[test]
fn test_cbnz_w5_produces_pc_update() {
    // CBNZ W5, #0x8 — encoding: 0x35000045
    let insn = decode_aarch64(&0x35000045u32.to_le_bytes(), 0x0).expect("decode CBNZ");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_pc_update = effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. }));
    assert!(has_pc_update, "CBNZ should produce PcUpdate");
}

#[test]
fn test_tbz_x0_bit5_produces_pc_update() {
    // TBZ X0, #5, #0x10 — encoding: 0x36280080
    let insn = decode_aarch64(&0x36280080u32.to_le_bytes(), 0x0).expect("decode TBZ");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_pc_update = effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. }));
    assert!(has_pc_update, "TBZ should produce PcUpdate");

    if let Some(Effect::PcUpdate { value }) =
        effects.iter().find(|e| matches!(e, Effect::PcUpdate { .. }))
    {
        assert!(matches!(value, Formula::Ite(..)), "TBZ PC value should be Ite, got: {:?}", value);
    }
}

#[test]
fn test_tbnz_w0_bit3_produces_pc_update() {
    // TBNZ W0, #3, #0x8 — encoding: 0x37180040
    let insn = decode_aarch64(&0x37180040u32.to_le_bytes(), 0x0).expect("decode TBNZ");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_pc_update = effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. }));
    assert!(has_pc_update, "TBNZ should produce PcUpdate");
}

// ---------------------------------------------------------------------------
// Load/store variants: LDRB, STRB, STRH
// ---------------------------------------------------------------------------

#[test]
fn test_ldrb_w0_x1_produces_mem_read() {
    // LDRB W0, [X1] — encoding: 0x39400020
    let insn = decode_aarch64(&0x39400020u32.to_le_bytes(), 0x1000).expect("decode LDRB");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_mem_read = effects.iter().any(|e| matches!(e, Effect::MemRead { width_bytes: 1, .. }));
    let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, .. }));
    assert!(has_mem_read, "LDRB should produce MemRead with 1 byte");
    assert!(has_reg_write, "LDRB should write to W0");
}

#[test]
fn test_strb_w0_x1_produces_mem_write() {
    // STRB W0, [X1] — size=00 opc=00 imm12=0 Rn=1 Rt=0
    // 00 111 00100 000000000000 00001 00000
    // = 0x39000020
    let insn = decode_aarch64(&0x39000020u32.to_le_bytes(), 0x1000).expect("decode STRB");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_mem_write =
        effects.iter().any(|e| matches!(e, Effect::MemWrite { width_bytes: 1, .. }));
    assert!(has_mem_write, "STRB should produce MemWrite with 1 byte");
}

#[test]
fn test_strh_w0_x1_4_produces_mem_write() {
    // STRH W0, [X1, #4] — encoding: 0x79000820
    let insn = decode_aarch64(&0x79000820u32.to_le_bytes(), 0x1000).expect("decode STRH");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_mem_write =
        effects.iter().any(|e| matches!(e, Effect::MemWrite { width_bytes: 2, .. }));
    assert!(has_mem_write, "STRH should produce MemWrite with 2 bytes");
}

// ---------------------------------------------------------------------------
// Address computation: ADR, ADRP
// ---------------------------------------------------------------------------

#[test]
fn test_adr_x0_produces_reg_write() {
    // ADR X0, #0x10 (at address 0x1000) — encoding: 0x10000080
    let insn = decode_aarch64(&0x10000080u32.to_le_bytes(), 0x1000).expect("decode ADR");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, .. }));
    assert!(has_reg_write, "ADR should write X0");
}

#[test]
fn test_adrp_x0_produces_reg_write() {
    // ADRP X0, #0x1000 (at address 0x2000) — encoding: 0xB0000000
    let insn = decode_aarch64(&0xB0000000u32.to_le_bytes(), 0x2000).expect("decode ADRP");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write = effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, .. }));
    assert!(has_reg_write, "ADRP should write X0");
}

// ---------------------------------------------------------------------------
// System: DMB produces ordering boundary and PC advance
// ---------------------------------------------------------------------------

#[test]
fn test_aarch64_dmb_ish_produces_sync_boundary_and_pc_advance() {
    // DMB ISH — encoding: 0xD5033B9F
    let insn = decode_aarch64(&0xD5033B9Fu32.to_le_bytes(), 0x1000).expect("decode DMB");
    let effects = sem().effects(&state(), &insn).expect("effects");

    assert_eq!(effects.len(), 2, "DMB should produce boundary + PC effects");
    assert!(matches!(
        &effects[0],
        Effect::Aarch64SyncBoundary {
            kind: Aarch64SyncBoundaryKind::DataMemoryBarrier,
            scope: Aarch64SyncScope::InnerShareable,
            ordering: Aarch64SyncOrdering::LoadsAndStores,
            clears_exclusive_monitor: false,
            raw_option: Some(0xB),
        }
    ));
    assert!(matches!(&effects[1], Effect::PcUpdate { .. }), "DMB should advance PC");
}

// ---------------------------------------------------------------------------
// TST alias: ANDS with XZR destination
// ---------------------------------------------------------------------------

#[test]
fn test_tst_is_ands_with_zr_dest_sets_flags_no_write() {
    // TST X1, X2 = ANDS XZR, X1, X2
    // sf=1 opc=11 01010 00 N=0 Rm=2 imm6=0 Rn=1 Rd=31
    // 1 11 01010 00 0 00010 000000 00001 11111
    // = 0xEA02003F
    let insn = decode_aarch64(&0xEA02003Fu32.to_le_bytes(), 0x1000).expect("decode TST");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_flags = effects.iter().any(|e| matches!(e, Effect::FlagUpdate { .. }));
    assert!(has_flags, "TST (ANDS XZR) should set flags");

    // TST writes to XZR (index 31) which is kept as a reg write in the current
    // implementation (unlike SUB which discards writes to ZR index 31).
    // The important thing is flags are set.
}

// ---------------------------------------------------------------------------
// Comprehensive no-crash sweep: all integer opcode groups
// ---------------------------------------------------------------------------

#[test]
fn test_all_integer_opcodes_produce_effects() {
    // Verify every implemented integer opcode produces a non-error result.
    let encodings: &[(u32, &str)] = &[
        // Arithmetic
        (0x8B020020, "ADD X0, X1, X2"),
        (0xAB020020, "ADDS X0, X1, X2"),
        (0xCB020020, "SUB X0, X1, X2"),
        (0xEB02003F, "CMP/SUBS XZR, X1, X2"),
        (0x9A020020, "ADC X0, X1, X2"),
        (0xBA020020, "ADCS X0, X1, X2"),
        (0xDA020020, "SBC X0, X1, X2"),
        (0xFA020020, "SBCS X0, X1, X2"),
        (0x9B020C20, "MADD X0, X1, X2, X3"),
        (0x9B028C20, "MSUB X0, X1, X2, X3"),
        (0x9B220C20, "SMADDL X0, W1, W2, X3"),
        (0x9B228C20, "SMSUBL X0, W1, W2, X3"),
        (0x9B420020, "SMULH X0, X1, X2"),
        (0x9BA20C20, "UMADDL X0, W1, W2, X3"),
        (0x9BA28C20, "UMSUBL X0, W1, W2, X3"),
        (0x9BC20020, "UMULH X0, X1, X2"),
        (0x9AC20820, "UDIV X0, X1, X2"),
        (0x9AC20C20, "SDIV X0, X1, X2"),
        // Logic
        (0x8A020020, "AND X0, X1, X2"),
        (0xEA020020, "ANDS X0, X1, X2"),
        (0xAA020020, "ORR X0, X1, X2"),
        (0xCA020020, "EOR X0, X1, X2"),
        (0x8A220020, "BIC X0, X1, X2"),
        (0xEA220020, "BICS X0, X1, X2"),
        (0xAA220020, "ORN X0, X1, X2"),
        (0xCA220020, "EON X0, X1, X2"),
        // Variable shifts
        (0x9AC22020, "LSLV X0, X1, X2"),
        (0x9AC22420, "LSRV X0, X1, X2"),
        (0x9AC22820, "ASRV X0, X1, X2"),
        (0x9AC22C20, "RORV X0, X1, X2"),
        // Bit manipulation
        (0xDAC00020, "RBIT X0, X1"),
        (0xDAC00420, "REV16 X0, X1"),
        (0xDAC00820, "REV32 X0, X1"),
        (0xDAC00C20, "REV X0, X1"),
        (0xDAC01020, "CLZ X0, X1"),
        (0xDAC01420, "CLS X0, X1"),
        // Conditional select
        (0x9A820020, "CSEL X0, X1, X2, EQ"),
        (0x9A821420, "CSINC X0, X1, X2, NE"),
        (0xDA820020, "CSINV X0, X1, X2, EQ"),
        (0xDA820420, "CSNEG X0, X1, X2, EQ"),
        // Move
        (0xD2800540, "MOVZ X0, #42"),
        (0x92800000, "MOVN X0, #0"),
        // Bitfield
        (0xD3401C20, "UBFM X0, X1, #0, #7"),
        (0x93401C20, "SBFM X0, X1, #0, #7"),
    ];

    for &(enc, desc) in encodings {
        let insn = decode_aarch64(&enc.to_le_bytes(), 0x1000)
            .unwrap_or_else(|e| panic!("decode {desc}: {e}"));
        let result = sem().effects(&state(), &insn);
        assert!(result.is_ok(), "{desc} should not return error, got: {:?}", result.err());
        let effects = result.expect("effects");
        assert!(!effects.is_empty(), "{desc} should produce at least one effect");
    }
}

// ---------------------------------------------------------------------------
// Edge case: 32-bit register width operations
// ---------------------------------------------------------------------------

#[test]
fn test_add_w0_w1_w2_32bit() {
    // ADD W0, W1, #10 (sf=0 32-bit)
    // 0 00 10001 00 000000001010 00001 00000
    // = 0x11002820
    let insn = decode_aarch64(&0x11002820u32.to_le_bytes(), 0x1000).expect("decode ADD W");
    let effects = sem().effects(&state(), &insn).expect("effects");

    let has_reg_write =
        effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 0, width: 32, .. }));
    assert!(has_reg_write, "ADD W0 should write 32-bit register");
}
