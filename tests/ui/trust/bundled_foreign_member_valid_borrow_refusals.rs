//@ needs-trust-verify
//@ aux-build:bundled_borrow_provenance_dep.rs
//@ edition: 2021
//@ revisions: xclean xclean_certify xtransmuted xpass xchain unguarded
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[xclean] compile-flags: -Ztrust-bundle-foreign-crate=bpdep
//@[xclean_certify] compile-flags: -Ztrust-bundle-foreign-crate=bpdep -Ztrust-policy=certify
//@[xtransmuted] compile-flags: -Ztrust-bundle-foreign-crate=bpdep -Ztrust-policy=certify
//@[xpass] compile-flags: -Ztrust-bundle-foreign-crate=bpdep -Ztrust-policy=certify
//@[xchain] compile-flags: -Ztrust-bundle-foreign-crate=bpdep -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[xclean] check-pass
//@[xclean_certify] check-pass
//@[xtransmuted] check-fail
//@[xpass] check-pass
//@[xchain] check-fail
//@[unguarded] check-fail
//! **`ValidBorrow` in a B-lane member must be TRUE OF THE ACTUAL BORROW (D5-C,
//! 2026-09-24).** This file holds the refusals the widening must not open, plus
//! the positive twin that shows the refusals are specific.
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED WITH THE PINNED ROW. If one
//! goes green, treat it as a possible FALSE ACCEPT until shown otherwise: fix
//! the compiler, never this file.
//!
//! # Before (measured on stage-1 `trustc 0.10.0+g4e9fe36bf`, 2026-09-24)
//!
//! * `xclean`: rc=0, but `1 proved, 0 failed, 0 unknown, 0 timed out,
//!   1 runtime-checked out of 2`. The runtime-checked row was the aggregate
//!   panic-freedom row, `UnsupportedDirectCallSummary` on the call to
//!   `bpdep::load_ref`. `xclean_certify` was rc=1.
//! * `xtransmuted`, `xpass`, `xchain`: rc=1, with the same counts and the same
//!   construct.
//! * `unguarded`: rc=1, `0 proved, 1 failed, 0 unknown, 0 timed out,
//!   1 runtime-checked out of 2`, with `[precond] FAILED (ay-in-process);
//!   counterexample: d = 0`.
//!
//! Why `xtransmuted` is a DISCRIMINATING negative and not an unrelated refusal:
//! the only instruction trust-mc's call summary declines on, in both
//! `load_ref` and `load_transmuted_ref`, is the one `Load` through the `&u32`
//! (`call-summary-census`: `declined unmodeled_instruction/Load`). With
//! `ValidBorrow` patched onto that `Load` in the dumped bundle, BOTH summarize
//! (census: `summarized`, measured for each). So a fix that stamped every
//! B-lane member, or keyed the clean set without classifying the member's own
//! body, would move `xtransmuted` exactly as it moves `xclean`: to proved, over
//! a load from address `a`. The compiler must tell them apart by the member's
//! MIR, where the `transmute` to `&u32` is still visible
//! (`function_is_borrow_provenance_clean`). It must not rely on the static type
//! `&u32`, which both of them have.
//!
//! * `xclean`, `xclean_certify` — POSITIVE TWIN, check-pass. After the fix both
//!   rows prove. If these fail with the before counts, the fix did not fire. If
//!   they fail differently, adjudicate before touching the pins.
//! * `xtransmuted` — must keep the before counts under `certify`.
//! * `xpass` — POSITIVE, check-pass. A clean member (`pass_through`) hands its
//!   own parameter to a clean member (`load_ref`). trust-mc summarizes the pair
//!   through its NESTED call summary.
//! * `xchain` — the chain that conjunct (3) exists for, found by adversarial
//!   self-check before landing. `pass_transmuted` fabricates the reference and
//!   loads nothing. `load_ref`, which is clean, does the load. Measured on the
//!   before dump: with `ValidBorrow` patched onto `load_ref`'s `Load` ONLY, the
//!   census reports BOTH call sites `summarized`. So a per-function stamp would
//!   verify this caller over a load from address `a`. It must keep the before
//!   counts: because a FOREIGN body in the bundle fails the member rule, every
//!   B-lane stamp is withheld.
//!
//!   **2026-09-27: `xchain` and `xtransmuted` no longer reach conjuncts (1)-(3).**
//!   Since D4-A (2026-09-24) a non-sysroot foreign member whose source carries
//!   user `unsafe` is not bundled (`foreign-member-user-unsafe-source`), so
//!   `pass_transmuted` and `load_transmuted_ref` are absent callees and both
//!   revisions are refused by their may-panic marker. Measured with
//!   `TRUST_BORROW_CLEAN_TRACE`: both revisions record the root alone, while
//!   `xclean` and `xpass` record their `bpdep` members. They still pin the
//!   refusal, and they must keep it; they no longer discriminate the mechanism
//!   this file describes. Conjunct (3), now asked on the lowered module
//!   (`ReachScope`), is pinned by the unit tests in
//!   `compiler/rustc_mir_transform/src/trust_verify/bundled_borrow_provenance/tests.rs`,
//!   because no fixture can put a fabricator into the B-lane any more.
//! * `unguarded` — a real divide-by-zero through the SYSROOT member
//!   `<&u32 as Rem<u32>>::rem`. With the stamp, the member's summary now reaches
//!   its own `Assert` (`d != 0`), so the aggregate row can no longer be excused
//!   as an unsummarized call. The row must still not prove (the pinned
//!   `0 proved`), and the derived-precondition row must still refute with
//!   `d = 0`.
//!
//! Not pinned: a member that obtains its reference from an `unsafe fn`, from a
//! `transmute` into a type that merely CONTAINS a reference, or through a union
//! field. On today's engine all three are refused at lowering or call time,
//! before the stamp could matter. Measured: the unsafe callee is an
//! absent-callee `Assert(false)`, and the other two members fail to lower and
//! are evicted. The foreign-member conjunct
//! (`mono_member_has_no_unsafe_reference_source`) refuses them anyway. It has
//! no discriminating fixture yet, and that is stated here so nobody reads one
//! into this file.
extern crate bpdep;

#[cfg(any(xclean, xclean_certify))]
pub fn f(x: &u32, d: u32) -> u32 {
    //[xclean,xclean_certify]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    let v = bpdep::load_ref(x);
    if d == 0 { 0 } else { v % d }
}

#[cfg(xtransmuted)]
pub fn f(a: usize, d: u32) -> u32 {
    //[xtransmuted]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //[xtransmuted]~| ERROR Trust Level 0 safety verification incomplete
    //[xtransmuted]~| ERROR Trust strict verification failed
    let v = bpdep::load_transmuted_ref(a);
    if d == 0 { 0 } else { v % d }
}

#[cfg(xpass)]
pub fn f(x: &u32, d: u32) -> u32 {
    //[xpass]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    let v = bpdep::pass_through(x);
    if d == 0 { 0 } else { v % d }
}

#[cfg(xchain)]
pub fn f(a: usize, d: u32) -> u32 {
    //[xchain]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //[xchain]~| ERROR Trust Level 0 safety verification incomplete
    //[xchain]~| ERROR Trust strict verification failed
    let v = bpdep::pass_transmuted(a);
    if d == 0 { 0 } else { v % d }
}

#[cfg(unguarded)]
pub fn rem_ref_any(x: &u32, d: u32) -> u32 {
    //[unguarded]~^ NOTE Trust verification: 0 proved
    //[unguarded]~| NOTE [precond] FAILED
    //[unguarded]~| ERROR Trust strict verification failed
    x % d
}
