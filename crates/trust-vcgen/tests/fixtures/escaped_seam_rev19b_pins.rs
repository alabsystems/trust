#![allow(unconditional_panic, unused_assignments, unused_variables, unused_mut, clippy::all, dead_code, unused_unsafe)]
// rev19b — isolating the round-A13 guard-filter widening (R-a):
//   `!local_storage_borrowed_anywhere(func, g.local)` added to the guard filter.
// v3/v4 are the soundness cases the widening defends; v1/v2/v6/v7 are correct programs
// that differ from them only in that no write channel to the guard exists at all.

#[inline(never)]
pub fn sink(p: &usize) -> usize { *p & 0 }
#[inline(never)]
pub fn launder(p: *const usize) -> *mut usize { p as *mut usize }
#[inline(never)]
pub fn nothing() {}

// v1: shared borrow of a never-written PARAMETER guard, NO call in the region.
pub fn v1_shared_param_no_call_ctl(s: &mut [u8], t: &[u8; 4], j: usize) -> u8 {
    if s.len() < 4 { return 0; }
    if j >= s.len() { return 0; }
    let q = &j;
    let r = &mut s[j];
    *r = 3;
    let _z = *q;
    t[s[j] as usize]
}

// v2: the same, with a CALL between the borrow and the use (= ra1).
pub fn v2_shared_param_call_ctl(s: &mut [u8], t: &[u8; 4], j: usize) -> u8 {
    if s.len() < 4 { return 0; }
    if j >= s.len() { return 0; }
    let q = &j;
    let r = &mut s[j];
    let _z = sink(q);
    *r = 3;
    t[s[j] as usize]
}

// v3: the SOUNDNESS case — the shared borrow of the parameter guard is laundered to
//     `*mut` and STORED through. The guard IS written; the fold must stay refused.
pub fn v3_shared_param_cast_store_bug(s: &mut [u8], t: &[u8; 4], j: usize, k: usize) -> u8 {
    if s.len() < 4 { return 0; }
    if j >= s.len() { return 0; }
    let pj = launder(&j);
    let r = &mut s[j];
    unsafe { *pj = k };
    *r = 3;
    if j >= s.len() { return 0; }
    t[s[j] as usize]
}

// v4: a MUTABLE borrow of the parameter guard, written through.
pub fn v4_mut_param_guard_bug(s: &mut [u8], t: &[u8; 4], mut j: usize, k: usize) -> u8 {
    if s.len() < 4 { return 0; }
    if j >= s.len() { return 0; }
    let r = &mut s[j];
    let q = &mut j;
    *q = k;
    *r = 3;
    if j >= s.len() { return 0; }
    t[s[j] as usize]
}

// v5: no borrow of the guard at all, with a call (the A12 shape that still proves).
pub fn v5_plain_param_call_ctl(s: &mut [u8], t: &[u8; 4], j: usize) -> u8 {
    if s.len() < 4 { return 0; }
    if j >= s.len() { return 0; }
    let r = &mut s[j];
    nothing();
    *r = 3;
    t[s[j] as usize]
}

// v6: shared borrow of the parameter guard plus a DROP in the region.
pub fn v6_shared_param_drop_ctl(s: &mut [u8], t: &[u8; 4], j: usize) -> u8 {
    if s.len() < 4 { return 0; }
    if j >= s.len() { return 0; }
    let q = &j;
    let r = &mut s[j];
    {
        let v = vec![1u8, 2, 3];
        let _n = v.len() + *q;
    }
    *r = 3;
    t[s[j] as usize]
}

// v7: shared borrow of the parameter guard, taken AFTER the whole region has ended.
pub fn v7_shared_param_borrow_after_ctl(s: &mut [u8], t: &[u8; 4], j: usize) -> u8 {
    if s.len() < 4 { return 0; }
    if j >= s.len() { return 0; }
    let r = &mut s[j];
    nothing();
    *r = 3;
    let v = t[s[j] as usize];
    let q = &j;
    let _z = sink(q);
    v
}
