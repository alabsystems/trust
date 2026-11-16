// h1_ctl: CORRECT programs whose slice-range bound or range-loop end is read through a
// reference / pointer (the projected arm of `resolve_range_bound_formula`). Each is
// panic-free on every input: the bound is guarded, or is `min(8)` of the input, and
// nothing writes it between the range's construction and the index.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]

pub struct St {
    pub len: usize,
}

#[inline(never)]
pub fn bump(s: &mut St) {
    s.len = s.len.wrapping_mul(3);
}

// PC01: `&St` parameter field, guarded, then `..s.len`.
pub fn pc01_param_field_guarded_ctl(s: &St, buf: &[u8; 8]) -> usize {
    if s.len > 8 {
        return 0;
    }
    buf[..s.len].len()
}

// PC02: a single-assignment local read through `z = &len`.
pub fn pc02_folded_ssa_local_ctl(buf: &[u8; 8], m: usize) -> usize {
    let len = m.min(8);
    let z = &len;
    buf[..*z].len()
}

// PC03: range-loop end `s.len` of a `&St` parameter, guarded first.
pub fn pc03_yield_param_field_ctl(s: &St, buf: &[u8; 8]) -> u8 {
    if s.len > 8 {
        return 0;
    }
    let mut acc = 0;
    for i in 0..s.len {
        acc ^= buf[i];
    }
    acc
}

// PC04: range-loop end `*z` with `z = &len`, `len` single-assignment.
pub fn pc04_yield_folded_ssa_ctl(buf: &[u8; 8], m: usize) -> u8 {
    let len = m.min(8);
    let z = &len;
    let mut acc = 0;
    for i in 0..*z {
        acc ^= buf[i];
    }
    acc
}

// PC05: `&mut St` parameter, guarded, reborrowed `z = &s.len`, never written.
pub fn pc05_mut_param_field_no_write_ctl(s: &mut St, buf: &[u8; 8]) -> usize {
    if s.len > 8 {
        return 0;
    }
    let z = &s.len;
    let r = ..*z;
    buf[r].len()
}

// PC06: a callee writes `s.len` BEFORE the guard and the range; nothing after.
pub fn pc06_call_before_range_ctl(s: &mut St, buf: &[u8; 8]) -> usize {
    bump(s);
    if s.len > 8 {
        return 0;
    }
    buf[..s.len].len()
}

// PC07: a local struct field, written once (whole), read through `z = &st.len`.
pub fn pc07_local_struct_ssa_ctl(buf: &[u8; 8], m: usize) -> usize {
    let st = St { len: m.min(8) };
    let z = &st.len;
    buf[..*z].len()
}

// PC08: the yield twin of PC06: a callee writes `s.len` before the guard and the loop.
pub fn pc08_yield_call_before_loop_ctl(s: &mut St, buf: &[u8; 8]) -> u8 {
    bump(s);
    if s.len > 8 {
        return 0;
    }
    let mut acc = 0;
    for i in 0..s.len {
        acc ^= buf[i];
    }
    acc
}
