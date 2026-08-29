//! WHICH DECODER FUNCTION handled this word.
//!
//! This MIRRORS the dispatch tree of
//! `crates/trust-disasm/src/aarch64/decode.rs` (read at HEAD, 2026-08-10) — only
//! the routing conditions, never the bodies. A mirror can drift from what it
//! mirrors, so it is SELF-CHECKED: `producible` lists, for each leaf, the exact
//! set of `Opcode`s that leaf's body can construct (extracted from the same
//! source), and the harness asserts on EVERY successfully decoded word that the
//! opcode trust-disasm actually produced is in the attributed leaf's set. Any
//! violation is counted and reported as an ATTRIBUTION ERROR rather than silently
//! mis-ranked.

use trust_disasm::Opcode;

#[inline]
fn bits(v: u32, hi: u32, lo: u32) -> u32 {
    (v >> lo) & ((1 << (hi - lo + 1)) - 1)
}
#[inline]
fn bit(v: u32, p: u32) -> u32 {
    (v >> p) & 1
}

/// Name of the decoder function that would construct the `Instruction` for `enc`,
/// or the function that refuses it. Mirrors `decode_instruction`'s dispatch.
#[must_use]
pub fn decoder_fn(enc: u32) -> &'static str {
    match bits(enc, 28, 25) {
        0b0000 => "decode_instruction",
        0b1000 | 0b1001 => dp_imm(enc),
        0b1010 | 0b1011 => branch_sys(enc),
        0b0100 | 0b0110 | 0b1100 | 0b1110 => load_store(enc),
        0b0101 | 0b1101 => dp_reg(enc),
        0b0111 | 0b1111 => simd_fp(enc),
        _ => "decode_instruction",
    }
}

fn dp_imm(enc: u32) -> &'static str {
    match bits(enc, 25, 23) {
        0b000 | 0b001 => "decode_pc_rel",
        0b010 | 0b011 => "decode_add_sub_imm",
        0b100 => "decode_logical_imm",
        0b101 => "decode_move_wide",
        0b110 => "decode_bitfield",
        _ => "decode_extract",
    }
}

fn branch_sys(enc: u32) -> &'static str {
    let top6 = bits(enc, 31, 26);
    if top6 == 0b000101 {
        return "decode_b";
    }
    if top6 == 0b100101 {
        return "decode_bl";
    }
    let top7 = bits(enc, 31, 25);
    if top7 == 0b0101010 {
        return "decode_b_cond";
    }
    let tp = bits(enc, 30, 25);
    if tp == 0b011010 {
        return "decode_cbz_cbnz";
    }
    if tp == 0b011011 {
        return "decode_tbz_tbnz";
    }
    if top7 == 0b1101011 {
        return "decode_br_reg";
    }
    if bits(enc, 31, 24) == 0b11010100 {
        return "decode_exception";
    }
    if bits(enc, 31, 22) == 0b1101010100 {
        return system(enc);
    }
    "decode_branch_sys"
}

fn system(enc: u32) -> &'static str {
    let l = bit(enc, 21);
    let op0 = bits(enc, 20, 19);
    let op1 = bits(enc, 18, 16);
    let crn = bits(enc, 15, 12);
    let rt = bits(enc, 4, 0);
    if l == 0 && op0 == 0 && op1 == 0b011 && crn == 0b0010 && rt == 31 {
        return "decode_hint";
    }
    if l == 0 && op0 == 0 && op1 == 0b011 && crn == 0b0011 {
        return "decode_barrier";
    }
    "decode_system"
}

fn load_store(enc: u32) -> &'static str {
    let op0 = bits(enc, 31, 28);
    let op1 = bit(enc, 26);
    let op2 = bits(enc, 24, 23);
    let b2927 = bits(enc, 29, 27);
    if b2927 == 0b011 && op1 == 0 {
        return "decode_load_literal";
    }
    if op0 & 0b0010 == 0 && op1 == 0 && op2 & 0b10 == 0 {
        return "decode_load_store_exclusive";
    }
    if b2927 == 0b101 && op1 == 0 {
        return "decode_load_store_pair";
    }
    if (b2927 == 0b111 || b2927 == 0b110) && op1 == 0 {
        return "decode_load_store_reg";
    }
    if (b2927 == 0b111 || b2927 == 0b110) && op1 == 1 {
        return "decode_simd_fp_load_store_reg_unsigned_offset";
    }
    "decode_load_store"
}

fn dp_reg(enc: u32) -> &'static str {
    let op1 = bit(enc, 28);
    let op2 = bits(enc, 24, 21);
    if op1 == 0 {
        if op2 & 0b1000 == 0 {
            return "decode_logical_shifted_reg";
        }
        // HEAD: bit 21 alone separates shifted from extended; bits[23:22] are
        // the shift type, so LSR/ASR add/sub now route here too.
        if bit(enc, 21) == 0 {
            return "decode_add_sub_shifted_reg";
        }
        if bits(enc, 23, 22) == 0 {
            return "decode_add_sub_extended_reg";
        }
    } else {
        if op2 == 0b0000 {
            return "decode_add_sub_carry";
        }
        if op2 == 0b0010 || op2 == 0b0011 {
            return "decode_cond_compare";
        }
        if op2 == 0b0100 || op2 == 0b0101 {
            return "decode_cond_select";
        }
        if op2 == 0b0110 {
            // `decode_dp_2source` forwards to `decode_dp_1source` on bit 30.
            return if bit(enc, 30) == 1 { "decode_dp_1source" } else { "decode_dp_2source" };
        }
        if op2 & 0b1000 != 0 {
            return "decode_dp_3source";
        }
    }
    "decode_dp_reg"
}

fn simd_fp(enc: u32) -> &'static str {
    let is_fp_prefix = bits(enc, 28, 24) == 0b11110 && bit(enc, 21) == 1;
    let is_dp_prefix = bits(enc, 31, 29) == 0b000 && is_fp_prefix;
    let is_int_conv_prefix = bits(enc, 30, 29) == 0b00 && is_fp_prefix;
    if is_dp_prefix {
        return match bits(enc, 11, 10) {
            0b10 => "decode_fp_dp_2source",
            0b11 => "decode_fp_csel",
            // HEAD: bit 13 is `imm8<0>`, not part of the selector; bits 12/13/14
            // partition this slot.
            0b00 => {
                if bit(enc, 12) == 1 {
                    "decode_fp_imm"
                } else if bit(enc, 13) == 1 {
                    "decode_fp_compare"
                } else if bit(enc, 14) == 1 {
                    "decode_fp_dp_1source"
                } else {
                    "decode_fp_int_conv"
                }
            }
            _ => "decode_fp_int_conv",
        };
    }
    if is_int_conv_prefix && bit(enc, 31) == 1 {
        return "decode_fp_int_conv";
    }
    "decode_simd_fp"
}

/// Exactly the `Opcode`s each leaf's BODY can construct, transcribed from the
/// source. Used to self-check the mirror above.
#[must_use]
pub fn producible(f: &str) -> &'static [Opcode] {
    use Opcode as O;
    match f {
        "decode_pc_rel" => &[O::Adr, O::Adrp],
        "decode_add_sub_imm" => &[O::Add, O::Adds, O::Sub, O::Subs],
        "decode_logical_imm" => &[O::And, O::Orr, O::Eor, O::Ands],
        "decode_move_wide" => &[O::Movn, O::Movz, O::Movk],
        "decode_bitfield" => &[O::Sbfm, O::Bfm, O::Ubfm],
        "decode_extract" => &[O::Extr],
        "decode_b" => &[O::B],
        "decode_bl" => &[O::Bl],
        "decode_b_cond" => &[O::BCond],
        "decode_cbz_cbnz" => &[O::Cbz, O::Cbnz],
        "decode_tbz_tbnz" => &[O::Tbz, O::Tbnz],
        "decode_br_reg" => &[O::Br, O::Blr, O::Ret],
        "decode_exception" => &[O::Svc, O::Hvc, O::Smc, O::Brk, O::Hlt],
        "decode_system" => &[O::Msr, O::Mrs],
        "decode_hint" => &[O::Nop, O::Yield, O::Wfe, O::Wfi, O::Sev, O::Sevl],
        "decode_barrier" => &[O::Clrex, O::Dsb, O::Dmb, O::Isb],
        "decode_load_literal" => &[O::LdrLiteral, O::Ldrsw, O::Prfm],
        "decode_load_store_exclusive" => &[O::Ldar, O::Stlr, O::Ldxr, O::Stxr, O::Ldaxr, O::Stlxr],
        "decode_load_store_pair" => &[O::Ldp, O::Stp, O::Ldpsw],
        "decode_load_store_reg" => &[
            O::Strb,
            O::Ldrb,
            O::Ldrsb,
            O::Strh,
            O::Ldrh,
            O::Ldrsh,
            O::Str,
            O::Ldr,
            O::Ldrsw,
            O::Prfm,
        ],
        "decode_simd_fp_load_store_reg_unsigned_offset" => &[O::Str, O::Ldr],
        "decode_logical_shifted_reg" => {
            &[O::And, O::Bic, O::Orr, O::Orn, O::Eor, O::Eon, O::Ands, O::Bics]
        }
        "decode_add_sub_shifted_reg" | "decode_add_sub_extended_reg" => {
            &[O::Add, O::Adds, O::Sub, O::Subs]
        }
        "decode_add_sub_carry" => &[O::Adc, O::Adcs, O::Sbc, O::Sbcs],
        "decode_cond_compare" => &[O::Ccmn, O::Ccmp],
        "decode_cond_select" => &[O::Csel, O::Csinc, O::Csinv, O::Csneg],
        "decode_dp_2source" => &[O::Udiv, O::Sdiv, O::Lslv, O::Lsrv, O::Asrv, O::Rorv],
        "decode_dp_1source" => &[O::Rbit, O::Rev16, O::Rev32, O::Rev, O::Clz, O::Cls],
        "decode_dp_3source" => {
            &[O::Madd, O::Msub, O::Smaddl, O::Smsubl, O::Smulh, O::Umaddl, O::Umsubl, O::Umulh]
        }
        "decode_fp_int_conv" => &[O::FmovReg, O::Fcvtzs, O::Fcvtzu, O::Scvtf, O::Ucvtf],
        "decode_fp_dp_2source" => &[O::Fmul, O::Fdiv, O::Fadd, O::Fsub],
        "decode_fp_dp_1source" => &[O::FmovReg, O::Fabs, O::Fneg, O::Fsqrt, O::Fcvt],
        "decode_fp_compare" => &[O::Fcmp],
        "decode_fp_csel" => &[O::Fcsel],
        "decode_fp_imm" => &[O::FmovImm],
        // Pure-refusal nodes: reaching one with a successful decode is an
        // attribution error by construction.
        _ => &[],
    }
}
