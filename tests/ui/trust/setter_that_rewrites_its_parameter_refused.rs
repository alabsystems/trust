//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A helper that stores a parameter and THEN rewrites it stores the OLD value. Each
//! panics on the input named beside it.
//!
//! MEASURED FALSE PROOFS, 2026-09-30 (an adversarial audit; the 2026-09-17 pack
//! proves them too, one kernel-certified): the trivial-setter summary resolved the
//! stored operand through a copy chain built without regard to statement order, and
//! `*p = v; v = w` came out as "stores `w`". A helper that writes one of its own
//! parameters is no longer a trivial setter. The index and subtraction rows are
//! refuted; the assert keeps its runtime check (a warning).

fn set(p: &mut usize, mut v: usize, w: usize) {
    *p = v;
    v = w;
    let _ = v;
}

// a becomes 5.
pub fn index_after(buf: &[u8; 4]) -> u8 { //~ ERROR failed for `setter_that_rewrites_its_parameter_refused::index_after`
    let mut a: usize = 0;
    set(&mut a, 5, 2);
    buf[a]
}

// a becomes 5: `3 - 5`.
pub fn subtract_after() -> usize { //~ ERROR failed for `setter_that_rewrites_its_parameter_refused::subtract_after`
    let mut a: usize = 0;
    set(&mut a, 5, 2);
    3 - a
}

// x = 1, y = 2.
pub fn assert_after(x: usize, y: usize) { //~ WARN safety verification incomplete for `setter_that_rewrites_its_parameter_refused::assert_after`
    let mut a: usize = 0;
    set(&mut a, x, y);
    assert!(a == y);
}
