//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A store through a reference that points INTO memory reached by an unresolved
//! pointer (an unsize cast of `&mut arr`, the join of two reborrows, a pointer moved
//! out of an `Option` or an array) writes memory that other names reach too. Each
//! panics on the input named beside it.
//!
//! MEASURED FALSE PROOFS, 2026-09-29 (an adversarial audit; the 2026-09-17 pack
//! proved all of them): `*z` folded to `(*s)[0 of 1]`, so the store was a precise
//! write of `s*[..]` with no havoc, and a guard on `arr*[..]` survived.
//! `store_through_a_parameter_field_borrow_stays_precise.rs` is the twin.

// arr = [0; 4] (m = [[0; 2]; 2], a = b = [0, 0], p = P { x: 0, y: 0 }, c = true,
// k = 0, pp = &mut &mut [0; 4], self.data = [0; 8]) unless named below.
pub fn coerced_store(arr: &mut [u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::coerced_store`
    let [a, ..] = *arr;
    if a < 5 {
        let s: &mut [u8] = arr;
        if let [z, ..] = s { *z = 250; }
        let [b, ..] = *arr;
        return b + 250;
    }
    0
}
pub fn coerced_store_from_end(arr: &mut [u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::coerced_store_from_end`
    let [.., a] = *arr;
    if a < 5 {
        let s: &mut [u8] = arr;
        if let [.., z] = s { *z = 250; }
        let [.., b] = *arr;
        return b + 250;
    }
    0
}
pub fn coerced_whole_elem_via_ref(arr: &mut [u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::coerced_whole_elem_via_ref`
    let [a, ..] = *arr;
    if a < 5 {
        let s: &mut [u8] = arr;
        if let [z, ..] = s { let w: &mut u8 = z; *w = 250; }
        let [b, ..] = *arr;
        return b + 250;
    }
    0
}
pub fn coerced_nested(m: &mut [[u8; 2]; 2]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::coerced_nested`
    let [[a, _], _] = *m;
    if a < 5 {
        let s: &mut [[u8; 2]] = m;
        if let [r, ..] = s { r[0] = 250; }
        let [[b, _], _] = *m;
        return b + 250;
    }
    0
}
pub fn branch_ptr_pattern(a: &mut [u8; 2], b: &mut [u8; 2], c: bool) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::branch_ptr_pattern`
    let [x, _] = *a;
    if x < 5 {
        let s: &mut [u8; 2] = if c { &mut *a } else { &mut *b };
        let [z, _] = s;
        *z = 250;
        let [y, _] = *a;
        return y + 250;
    }
    0
}
pub fn branch_ptr_field(p: &mut P, q: &mut P, c: bool) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::branch_ptr_field`
    if p.x < 5 {
        let s: &mut P = if c { &mut *p } else { &mut *q };
        let z = &mut s.x;
        *z = 250;
        return p.x + 250;
    }
    0
}
pub fn coerced_index_ref(arr: &mut [u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::coerced_index_ref`
    let [a, ..] = *arr;
    if a < 5 {
        let s: &mut [u8] = arr;
        let z = &mut s[0];
        *z = 250;
        let [b, ..] = *arr;
        return b + 250;
    }
    0
}
pub fn coerced_subslice(arr: &mut [u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::coerced_subslice`
    let [_, a, ..] = *arr;
    if a < 5 {
        let s: &mut [u8] = arr;
        if let [_, rest @ ..] = s {
            if let [r0, ..] = rest { *r0 = 250; }
        }
        let [_, b, ..] = *arr;
        return b + 250;
    }
    0
}
pub fn option_held_ptr(arr: &mut [u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::option_held_ptr`
    let [a, ..] = *arr;
    if a < 5 {
        let o = Some(&mut *arr);
        if let Some(s) = o {
            let [z, ..] = s;
            *z = 250;
        }
        let [b, ..] = *arr;
        return b + 250;
    }
    0
}
pub fn array_of_ptrs(arr: &mut [u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::array_of_ptrs`
    let [a, ..] = *arr;
    if a < 5 {
        let ps = [&mut *arr];
        let [s] = ps;
        let [z, ..] = s;
        *z = 250;
        let [b, ..] = *arr;
        return b + 250;
    }
    0
}
pub fn match_selected(arr: &mut [u8; 4], other: &mut [u8; 4], k: u8) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::match_selected`
    let [a, ..] = *arr;
    if a < 5 {
        let s: &mut [u8; 4] = match k { 0 => &mut *arr, _ => &mut *other };
        let [z, ..] = s;
        *z = 250;
        let [b, ..] = *arr;
        return b + 250;
    }
    0
}
// arr = [0;4], buf = [1,2,3,4]: the store through the coerced slice makes arr[0] = 200
pub fn stale_guard_index_oob(arr: &mut [u8; 4], buf: &[u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::stale_guard_index_oob`
    let [a, ..] = *arr;
    if a < 4 {
        let s: &mut [u8] = arr;
        if let [z, ..] = s { *z = 200; }
        let [b, ..] = *arr;
        return buf[b as usize];
    }
    0
}
pub struct Buf { pub data: [u8; 8], pub len: u8 }
impl Buf {
    // data = [0;8]: an array field viewed as a slice, element ref by match ergonomics
    pub fn header_after_touch(&mut self) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::Buf::header_after_touch`
        let [h, ..] = self.data;
        if h < 5 {
            let d: &mut [u8] = &mut self.data;
            if let [first, ..] = d { *first = 250; }
            let [h2, ..] = self.data;
            return h2 + 250;
        }
        0
    }
}
// pp = &mut &mut [0;4]: inner pointer copied out and coerced
pub fn double_ptr_coerced(pp: &mut &mut [u8; 4]) -> u8 { //~ ERROR failed for `store_through_an_unresolved_pointer_refused::double_ptr_coerced`
    let [a, ..] = **pp;
    if a < 5 {
        let s: &mut [u8] = *pp;
        if let [z, ..] = s { *z = 250; }
        let [b, ..] = **pp;
        return b + 250;
    }
    0
}
pub struct P { pub x: u8, pub y: u8 }
