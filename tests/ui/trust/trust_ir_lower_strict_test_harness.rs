//@ dont-check-compiler-stderr
//@ compile-flags: --test -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust: `-Ztrust-ir-lower=strict` ratchets the direct producer over the bodies
//! the author WROTE — including a `#[test]` function's own body — and never over
//! the harness items the `#[test]` macro synthesizes for it (a `TestDescAndFn`
//! const marked `#[rustc_test_marker]` and the runner closure inside it).
//!
//! Before the scoping (`rustc_mir_build::trust_ir_strict_coverage_applies`) every
//! `#[test]` below raised two more errors at its `fn` line, from bodies no author
//! can change: `Adt(unsupported field)`/`EnumCtor(fat field seed)` on the
//! descriptor and `Call(unsupported arg)` on the closure. No strict crate could
//! build its tests at all; this file then fails with six unexpected errors.
//!
//! The negative half is `casts_a_borrow`: its OWN body carries a shape the
//! producer refuses (`Cast(borrow ptr operand)`), and that error must stay. The
//! annotation pins only that the body still refuses, not the tag — the tag moves
//! when the producer's coverage grows, which is the intended outcome.

pub fn add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

#[test]
fn adds() {
    assert_eq!(add(1, 2), 3);
}

// 2026-10-01: this body passed strict only because the wave-ER for-loop summary erased its
// loop (reported clean, lowered to `undef`). With the summary removed the array iterator's
// `next` has no lane, so the author's body is refused — the harness items around it stay
// exempt, which is what this file pins. `sums_with_a_range_loop` is the positive control: a
// `#[test]` whose loop the producer DOES lower faithfully.
#[test]
fn sums_with_a_loop() {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let mut s = 0u32;
    for i in [1u32, 2, 3] {
        s = s.wrapping_add(i);
    }
    assert_eq!(s, 6);
}

#[test]
fn sums_with_a_range_loop() {
    let mut s = 0u32;
    for i in 1u32..4 {
        s = s.wrapping_add(i);
    }
    assert_eq!(s, 6);
}

#[test]
fn casts_a_borrow() {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let v = 5u32;
    let r = &v;
    let p = r as *const u32 as *const u8;
    assert!(!p.is_null());
}
