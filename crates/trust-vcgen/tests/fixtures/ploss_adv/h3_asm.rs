// h3_asm: writes the MIR carries only as an inline-asm OUTPUT operand (or as a store the
// asm makes through a pointer it is handed), aarch64. H3 OPAQUE-ASM-OUTPUT: the extractor
// lowers `asm!` to `Terminator::Opaque { kind: "InlineAsm" }` and drops every operand.
// Every `_bug` panics on every input (`k < 4` by construction, the asm makes it >= 4;
// h3k: every input with two or more loop turns);
// every `_ctl` is panic-free on every input.
#![allow(clippy::all, unused_mut, unused_assignments, unused_variables, dead_code)]
use core::arch::asm;

pub struct St {
    pub a: usize,
    pub b: usize,
}

// H3A `out(reg)`.
pub fn h3a_out_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    unsafe { asm!("mov {0}, #4", out(reg) k) };
    t[k]
}

// H3B `lateout(reg)`.
pub fn h3b_lateout_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    unsafe { asm!("mov {0}, #4", lateout(reg) k) };
    t[k]
}

// H3C `inlateout(reg)`.
pub fn h3c_inlateout_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    unsafe { asm!("add {0}, {0}, #4", inlateout(reg) k) };
    t[k]
}

// H3D split `inout(reg) x => k`: the input is `x`, the output is `k`.
pub fn h3d_split_inout_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let x = 4usize;
    unsafe { asm!("mov {0}, {0}", inout(reg) x => k) };
    t[k]
}

// H3E `options(nomem, nostack, pure)` still writes its outputs.
pub fn h3e_nomem_pure_inout_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    unsafe { asm!("add {0}, {0}, #4", inout(reg) k, options(nomem, nostack, pure)) };
    t[k]
}

// H3F the output place is a struct FIELD.
pub fn h3f_field_inout_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut s = St { a: n & 3, b: 0 };
    unsafe { asm!("add {0}, {0}, #4", inout(reg) s.a) };
    t[s.a]
}

// H3G the output place is `*k` of a `&mut` parameter.
pub fn h3g_deref_inout_bug(k: &mut usize, t: &[u8; 4]) -> u8 {
    *k &= 3;
    unsafe { asm!("add {0}, {0}, #4", inout(reg) *k) };
    t[*k]
}

// H3H an explicit register `out("x9")`.
pub fn h3h_explicit_reg_out_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    unsafe { asm!("mov x9, #4", out("x9") k) };
    t[k]
}

// H3I memory clobber: the asm STORES 4 into `k` through a pointer it receives as an
// INPUT (no output operand names `k`).
pub fn h3i_store_through_ptr_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw mut k;
    unsafe { asm!("mov {v}, #4", "str {v}, [{p}]", p = in(reg) p, v = out(reg) _) };
    t[k]
}

// H3J memory clobber through a `&mut St` parameter's field pointer.
pub fn h3j_store_through_param_bug(s: &mut St, t: &[u8; 4]) -> u8 {
    s.a &= 3;
    let p: *mut usize = &mut s.a;
    unsafe { asm!("mov {v}, #4", "str {v}, [{p}]", p = in(reg) p, v = out(reg) _) };
    t[s.a]
}

// H3K the output is loop-carried: `k < 4` on entry, the asm adds 4 each turn, the
// index at the loop head panics on the second turn: every input with xs.len() >= 2.
pub fn h3k_loop_inout_bug(xs: &[u8], n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let mut acc = 0u8;
    for _ in xs {
        acc ^= t[k];
        unsafe { asm!("add {0}, {0}, #4", inout(reg) k) };
    }
    acc
}

// H3L two outputs; the SECOND one is the index.
pub fn h3l_second_output_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut j = 0usize;
    let mut k = n & 3;
    unsafe { asm!("mov {0}, #1", "mov {1}, #4", out(reg) j, out(reg) k) };
    t[k] ^ (j as u8)
}

// ---- controls (correct on every input) ----

// H3C1 the guard tests the asm's OUTPUT, after the asm.
pub fn h3c1_guard_after_asm_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n;
    unsafe { asm!("add {0}, {0}, #4", inout(reg) k) };
    if k >= 4 {
        return 0;
    }
    t[k]
}

// H3C2 the fact is established AFTER the asm.
pub fn h3c2_fact_after_asm_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut m = n;
    unsafe { asm!("add {0}, {0}, #4", inout(reg) m) };
    let k = m & 3;
    t[k]
}

// H3C3 a constant index into a fixed-size array: the bound is the TYPE's.
pub fn h3c3_const_index_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n;
    unsafe { asm!("add {0}, {0}, #4", inout(reg) k) };
    t[3] ^ (k as u8)
}

// H3C4 the asm only READS `k` (an `in` operand), nomem.
pub fn h3c4_input_only_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let k = n & 3;
    unsafe { asm!("/* {0} */", in(reg) k, options(nomem, nostack, preserves_flags)) };
    t[k]
}

// H3C5 the asm writes ANOTHER local `j`, nomem; `k` is never an operand.
pub fn h3c5_nomem_other_output_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let k = n & 3;
    let mut j = 0usize;
    unsafe { asm!("mov {0}, #9", out(reg) j, options(nomem, nostack, pure)) };
    t[k] ^ (j as u8)
}

// H3C6 memory-clobbering asm (no options) with no pointer to `k` anywhere.
pub fn h3c6_clobber_unescaped_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let k = n & 3;
    unsafe { asm!("nop") };
    t[k]
}

// H3M the asm output feeds an ARITHMETIC row: `k < 4` by construction, the asm writes
// 255, `k + 1` overflows `u8` on every input (-O0, and -O1 with debug assertions).
pub fn h3m_overflow_after_asm_bug(n: u8) -> u8 {
    let mut k = n & 3;
    unsafe { asm!("mov {0:w}, #255", inout(reg) k) };
    k + 1
}

// H3N the asm output is a DIVISOR: `k == 1` before the asm, the asm writes 0. Every
// input panics (division by zero).
pub fn h3n_divisor_after_asm_bug(n: usize) -> usize {
    let mut k = 1usize;
    unsafe { asm!("mov {0}, #0", inout(reg) k) };
    n / k
}

// H3O a CONSTANT index the asm overwrites: `k == 1` before the asm, the asm writes 4.
pub fn h3o_const_then_asm_index_bug(t: &[u8; 4]) -> u8 {
    let mut k = 1usize;
    unsafe { asm!("mov {0}, #4", inout(reg) k) };
    t[k]
}
