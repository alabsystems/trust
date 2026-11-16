// h2_raw_const: H2 RAW-CONST-STORE variants: a `&raw const` of the body's OWN storage cast
// to `*mut` and written (Tree Borrows: allowed; Stacked Borrows: UB). Every `_bug` panics
// natively at -O0/-O1 on its comment's input; every `_ctl` never panics. H2A/H2C5 have no
// fixture: the compiler records `addr-of-field` as an unverified assumption, dumps no MIR.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]

pub struct P {
    pub a: usize,
    pub b: usize,
}

// H2A: a FIELD of a local struct, `&raw const s.a`, stored. Every n panics. (No fixture.)
pub fn h2a_field_raw_const_store_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut s = P { a: n & 3, b: 0 };
    let p = &raw const s.a;
    unsafe { *(p as *mut usize) = 4 };
    t[s.a]
}

// H2B: an ELEMENT of a local array, `&raw const a[0]`.  Every n panics.
pub fn h2b_elem_raw_const_store_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut a = [n & 3, 0];
    let p = &raw const a[0];
    unsafe { *(p as *mut usize) = 4 };
    t[a[0]]
}

// H2C: the guard is taken BEFORE the store; the store moves `k` past it.  Every m panics
// (m > 3 returns, m <= 3 indexes with m + 4).
pub fn h2c_guarded_raw_const_store_bug(m: usize, t: &[u8; 4]) -> u8 {
    let mut k = m;
    if k > 3 {
        return 0;
    }
    let p = &raw const k;
    unsafe { *(p as *mut usize) = k + 4 };
    t[k]
}

// H2D: `ptr::addr_of!(k).cast_mut()` (a CALL at -O0, inlined to a cast at -O1).
// Every n panics.
pub fn h2d_addr_of_cast_mut_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let k0 = k;
    let p = core::ptr::addr_of!(k).cast_mut();
    unsafe { *p = k0 + 4 };
    t[k]
}

// H2E: a cast to a DIFFERENT pointee (`*mut u8`): a partial write of `k` (little-endian:
// its low byte).  Every n panics (k becomes 4).
pub fn h2e_byte_store_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw const k as *mut u8;
    unsafe { *p = 4 };
    t[k]
}

// H2F: the `*const` handed to a CALLEE that casts it and writes.  Every n panics.
#[inline(never)]
pub unsafe fn poke(p: *const usize) {
    unsafe { *(p as *mut usize) += 4 };
}
pub fn h2f_callee_store_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    unsafe { poke(&raw const k) };
    t[k]
}

// H2G: the WHOLE struct borrowed `&raw const s`, a field written through the cast.
// Every n panics.
pub fn h2g_whole_struct_field_store_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut s = P { a: n & 3, b: 0 };
    let p = &raw const s;
    unsafe { (*(p as *mut P)).a = 4 };
    t[s.a]
}

// H2H: the `*const` rides in a tuple before the cast.  Every n panics.
pub fn h2h_tuple_carried_raw_const_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let h: (*const usize, u8) = (&raw const k, 0);
    unsafe { *(h.0 as *mut usize) = 4 };
    t[k]
}

// H2I: the store is in a loop that runs once per input bit (`n & 1` times), the guard
// is before the loop.  n odd panics.
pub fn h2i_loop_store_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw const k;
    let mut i = 0;
    while i < (n & 1) {
        unsafe { *(p as *mut usize) += 4 };
        i += 1;
    }
    t[k]
}

// ---------------------------------------------------------------- controls (correct)

// H2C1: a `&raw const` that is only READ.
pub fn h2c1_raw_const_read_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let k = n & 3;
    let p = &raw const k;
    t[unsafe { *p }]
}

// H2C2: the store goes through a `&raw const` of ANOTHER local; `k` is never borrowed.
pub fn h2c2_raw_const_other_store_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let k = n & 3;
    let mut h = 0usize;
    let p = &raw const h;
    unsafe { *(p as *mut usize) = 9 };
    t[k] ^ (h as u8)
}

// H2C3: read both directly and through the pointer, no store.
pub fn h2c3_raw_const_read_both_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw const k;
    let v = unsafe { *p };
    t[k] ^ t[v]
}

// H2C4: the guard is taken AFTER the store (it tests the stored value).
pub fn h2c4_guard_after_store_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw const k;
    unsafe { *(p as *mut usize) = n };
    if k > 3 {
        return 0;
    }
    t[k]
}

// H2C5: `&raw const` of a field; the OTHER field is indexed. (No fixture.)
pub fn h2c5_other_field_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut s = P { a: 0, b: n & 3 };
    let p = &raw const s.a;
    let v = unsafe { *p };
    t[s.b] ^ (v as u8)
}

// H2C6: a `&raw const` of a local, then a CALL that receives nothing pointer-like.
pub fn h2c6_raw_const_then_call_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let k = n & 3;
    let p = &raw const k;
    let x = std::hint::black_box(1u8);
    t[unsafe { *p }] ^ x
}

// H2C7: the `&raw mut` twin of H2C6 (the fix makes `&raw const` answer like this).
pub fn h2c7_raw_mut_then_call_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw mut k;
    let x = std::hint::black_box(1u8);
    t[unsafe { *p }] ^ x
}

// H2C8: the slice-index prelude's `&raw const (*s)` (a borrow BEHIND a reference).
pub fn h2c8_slice_param_ctl(s: &[u8], i: usize) -> u8 {
    if i >= s.len() {
        return 0;
    }
    s[i]
}
