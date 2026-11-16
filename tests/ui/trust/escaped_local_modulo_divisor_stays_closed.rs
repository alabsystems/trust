//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//~? RAW Trust
//! Trust: 2026-09-15 — A `&mut` ESCAPE MUST NOT RESOLVE A LOCAL'S VALUE.
//!
//! # The false proof this pins
//!
//! `crates/trust-vcgen/src/local_defs.rs::body_unique_value_def` is THE resolver
//! for "what is this local's one value". Its answer is INLINED into a formula,
//! so — unlike a fact keyed on the bare name — version renaming can never rebind
//! it afterwards. It admitted the `LocalWrite::Escape` channel: a `&mut local`
//! handed out anywhere in the body.
//!
//! A store through that alias names a DIFFERENT place (`(*p) = v`, whose
//! `place.local` is `p`, not `m`) and `LocalWrite::of_place` classifies a
//! `Deref`-first projection as `Untouched` BY CONSTRUCTION, so no scan keyed on
//! `m` can see the reassignment. The resolver therefore handed back the one
//! `Assign` it did see — `m = const 4` —
//! `generate::callee_summaries::stable_min_arg_formula` folded it to the literal
//! `4`, and `generate::value_facts::build_modulo_bound_facts` emitted the GLOBAL
//! fact `n % m < 4`.
//!
//! MEASURED on the pristine prebuilt stage1 driver, 2026-09-15: this file
//! compiled with **rc = 0** and "2 proved, 0 failed ... of which 2
//! kernel-certified by the clean CIC kernel", the `IndexOutOfBounds` row reading
//! `outcome = proved`, `assurance = Certified`, `validation = KernelRechecked`,
//! `axiom_closure = Empty` — while the same program run as a binary panics
//! `index out of bounds: the len is 4 but the index is 5` (rc = 101) on
//! `pesc(false, 5, &[1, 2, 3, 4])`, because `pick(false)` is `9` and `5 % 9 == 5`.
//! That is a kernel-certified FALSE PROOF reachable from plain safe Rust: no
//! `unsafe`, no contracts, no unstable features, at the default cargo dev
//! profile's optimisation level.
//!
//! # Why the flags are part of the fixture
//!
//! `-Copt-level=0` is load-bearing. At `-Copt-level=1`/`2` the borrow is
//! optimised away and the same source lowers to the `Call`-destination shape the
//! resolver's `WholeOpaque` arm already refuses — so the shape that carries the
//! channel is the UN-optimised one, which is also the one users get by default.
//!
//! `-Ztrust-policy=certify` is the strictest lane; a row that survives it is
//! being claimed at full strength. The fixture is `check-fail` because the
//! divisor is no longer resolvable, so the bounds obligation is not discharged
//! and strict policy makes that a build error — fail-CLOSED, which is the sound
//! direction for a claim the program can violate.
//!
//! # The control
//!
//! `escaped_local_control_unaliased_divisor_still_proves.rs` is the same
//! arithmetic with NO alias. It must keep proving: this change refuses the
//! ESCAPE channel, not division, not modulo, and not locals.

#[inline(never)]
pub fn pick(c: bool) -> usize {
    if c { 4 } else { 9 }
}

#[inline(never)]
pub fn pesc(c: bool, n: usize, b: &[u8; 4]) -> u8 {
    let mut m = 4usize;
    let p = &mut m;
    // The write that no scan keyed on `m` can see: this statement's place-local
    // is `p`.
    *p = pick(c);
    // `m` is 9 whenever `c` is false, so `n % m` reaches 8 — out of bounds for a
    // `[u8; 4]`. The compiler must NOT prove this index in range.
    b[n % m]
}
