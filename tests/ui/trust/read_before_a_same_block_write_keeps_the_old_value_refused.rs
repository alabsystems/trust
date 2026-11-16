//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A value read BEFORE a write in the same block keeps the OLD value, whatever
//! reads the new one afterwards. Each panics on the input named beside it.
//!
//! MEASURED FALSE PROOFS, 2026-09-29 (an adversarial audit): a read that was the
//! ENTRY value at its own statement stayed spelled bare, and the obligation's
//! use-point rename stamped it with the version AFTER the write, so `old` became
//! the new value. `by_value_parameter` and `field_store` were already proved by the
//! 2026-09-17 pack; `60888aafec1` made every whole-pointee store reach the same
//! collision. `read_before_a_same_block_write_keeps_its_own_guard.rs` is the twin.
//!
//! Not one is proved. The arithmetic rows are refuted; the index rows are left
//! runtime-checked (a warning, the bounds check stays in the binary), because their
//! model rests on the pre-write value, a symbol of its own that the refutation lane
//! does not read as an execution.

//! Re-pinned 2026-10-15 (the merge of 2026-10-14): the index rows are now REFUTED too, not
//! left runtime-checked: each `[bounds]` row is FAILED with a real execution (the read
//! value `old = 2^63`, far past the array), so the default policy reports an error rather
//! than a warning. Still not one is proved.

// x = 7.
pub fn by_value_parameter(mut x: usize, a: &[u8; 4]) -> u8 { //~ ERROR safety verification incomplete for `read_before_a_same_block_write_keeps_the_old_value_refused::by_value_parameter`
    let old = x;
    x = 0;
    a[old | x]
}

// p = (7, 0).
pub fn field_store(p: &mut (usize, usize), a: &[u8; 4]) -> u8 { //~ ERROR safety verification incomplete for `read_before_a_same_block_write_keeps_the_old_value_refused::field_store`
    let old = p.0;
    p.0 = 0;
    a[old | p.0]
}

// *p = 7.
pub fn whole_pointee_store(p: &mut usize, a: &[u8; 4]) -> u8 { //~ ERROR safety verification incomplete for `read_before_a_same_block_write_keeps_the_old_value_refused::whole_pointee_store`
    let old = *p;
    *p = 0;
    a[old | *p]
}

// **q = 7.
pub fn through_two_pointers(q: &mut &mut usize, a: &[u8; 4]) -> u8 { //~ ERROR safety verification incomplete for `read_before_a_same_block_write_keeps_the_old_value_refused::through_two_pointers`
    let old = **q;
    **q = 0;
    a[old | **q]
}

pub struct R<'a> {
    pub r: &'a mut usize,
}

// *s.r = 7.
pub fn through_a_pointer_field(s: &mut R<'_>, a: &[u8; 4]) -> u8 { //~ ERROR safety verification incomplete for `read_before_a_same_block_write_keeps_the_old_value_refused::through_a_pointer_field`
    let old = *s.r;
    *s.r = 0;
    a[old | *s.r]
}

// *p = (7, 7).
pub fn aggregate_store(p: &mut (usize, usize), a: &[u8; 4]) -> u8 { //~ ERROR safety verification incomplete for `read_before_a_same_block_write_keeps_the_old_value_refused::aggregate_store`
    let old = p.0;
    *p = (0, 0);
    a[old | p.0]
}

// *p = (usize::MAX, 0).
pub fn overflow_after_aggregate_store(p: &mut (usize, usize)) -> usize { //~ ERROR failed for `read_before_a_same_block_write_keeps_the_old_value_refused::overflow_after_aggregate_store`
    let old = p.0;
    *p = (1, 1);
    old + p.0
}

// *p = 0.
pub fn divisor_after_store(p: &mut usize) -> usize { //~ ERROR failed for `read_before_a_same_block_write_keeps_the_old_value_refused::divisor_after_store`
    let old = *p;
    *p = 1;
    (old | *p) / old
}

// *s = [], t = [1].
pub fn stale_length<'a>(s: &mut &'a [u8], t: &'a [u8]) -> usize { //~ ERROR failed for `read_before_a_same_block_write_keeps_the_old_value_refused::stale_length`
    let before = s.len();
    *s = t;
    before - s.len()
}

// *best = 0, x = 1.
pub fn underflow_after_store(best: &mut u8, x: u8) -> u8 { //~ ERROR failed for `read_before_a_same_block_write_keeps_the_old_value_refused::underflow_after_store`
    let old = *best;
    *best = x;
    old - *best
}
