// h1_alias: H1 variants the 2026-10-08 hunt did not pin -- the pointee written by a
// CALLEE, and the pointee read through a pointer the referent fold cannot resolve (a
// laundered `&raw mut len`) and written through the pointer it was made from. Every
// `_bug` panics on the input in its comment (see drv_h1.rs).
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]

pub struct St {
    pub len: usize,
}

#[inline(never)]
pub fn set(s: &mut St, n: usize) {
    s.len = n;
}

#[inline(never)]
pub fn launder(p: *const usize) -> *const usize {
    p
}

// AL01: range from `*q`, `q` a laundered copy of `p = &raw mut len`; store through `p`;
// guard through `q`.  m=100, n=3 panics.
pub fn al01_launder_store_range_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = launder(p);
    unsafe {
        let r = ..*q;
        *p = n;
        if *q > 8 {
            return 0;
        }
        buf[r].len()
    }
}

// AL02: the ORDINARY-read twin of AL01 (no range): `x = *q; *p = n; guard *q; buf[x]`.
// m=100, n=3 panics.
pub fn al02_launder_store_read_bug(buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let p = &raw mut len;
    let q = launder(p);
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        buf[x]
    }
}

// AL03: the range-loop twin of AL01.  m=100, n=3 panics (i reaches 8).
pub fn al03_launder_store_yield_bug(buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let p = &raw mut len;
    let q = launder(p);
    let mut acc = 0;
    unsafe {
        for i in 0..*q {
            *p = n;
            if *q > 8 {
                return acc;
            }
            acc ^= buf[i];
        }
    }
    acc
}

// AL04: a CALLEE writes the field between the range and the index.
// s.len=100, n=3 panics.
pub fn al04_callee_write_range_bug(s: &mut St, buf: &[u8; 8], n: usize) -> usize {
    let r = ..s.len;
    set(s, n);
    if s.len > 8 {
        return 0;
    }
    buf[r].len()
}

// AL05: the range-loop twin of AL04.  s.len=100, n=3 panics (i reaches 8).
pub fn al05_callee_write_yield_bug(s: &mut St, buf: &[u8; 8], n: usize) -> u8 {
    let mut acc = 0;
    for i in 0..s.len {
        set(s, n);
        if s.len > 8 {
            return acc;
        }
        acc ^= buf[i];
    }
    acc
}

// AL06 control: AL04 with the guard first (correct on every input).
pub fn al06_callee_write_guard_first_ctl(s: &mut St, buf: &[u8; 8], n: usize) -> usize {
    if s.len > 8 {
        return 0;
    }
    let r = ..s.len;
    set(s, n);
    buf[r].len()
}
