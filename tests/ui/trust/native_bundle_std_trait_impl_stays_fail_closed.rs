//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! The guard for the trait-impl arm of
//! `native_trust_ir_monomorphic_foreign_callees`.
//!
//! Admitting resolved std trait calls (see
//! `native_bundle_std_trait_impl_body_proved.rs`) is sound only because the
//! admission is keyed on RESOLUTION. A trait method is user-implementable, so
//! the tempting shortcut — "`AsRef::as_ref` is trivial, model it as total" —
//! becomes a lie the moment any crate writes the impl below, and it would
//! launder that lie into every caller in the graph. `Boom` is that crate,
//! written here on purpose.
//!
//! # Every probe pins its MECHANISM, and that is the point of this file
//!
//! Read the trailing `NOTE` annotations as load-bearing, not decoration. Each
//! probe below fails, but they fail for THREE different reasons, and a lone
//! `ERROR Trust strict verification failed` annotation cannot tell them apart —
//! that string is the shared header every fail-closed path prints. See "the
//! blindness this file was repaired for", below.
//!
//! (This doc deliberately never spells the annotation sigil: compiletest's
//! `parse_expected` regex matches it ANYWHERE on a line, doc comments included,
//! so writing it in prose mints a phantom expectation that fails the fixture.
//! Measured while repairing this file — it cost seven bogus expectations.)
//!
//!   * `probe_generic_as_ref` — the receiver is the bare type parameter `B`, so
//!     trait selection cannot pick an impl and `Instance::try_resolve` returns
//!     `Ok(None)`. `B = Boom` is a legal instantiation and it panics, so the
//!     R3/T5 refusal is not conservatism, it is the correct answer. This is the
//!     shape that shows up as `<B as core::convert::AsRef<[u8]>>::as_ref` in
//!     first-party memchr's generic `Finder` constructors, and it stays open
//!     until the frontier is closed by a contract, never by a blanket model.
//!     MECHANISM PINNED: the ABSENT-CALLEE arm (`call to an absent callee`).
//!   * `probe_dyn_as_ref` — a `dyn` receiver resolves to `InstanceKind::Virtual`.
//!     There is no source body behind a vtable slot, so it is the irreducible
//!     floor no amount of body-lowering reaches.
//!     MECHANISM PINNED: the ABSENT-CALLEE arm, same as above.
//!   * `probe_slice_index_range` — `&a[1..2]` on a slice of unknown length.
//!     MECHANISM PINNED: a REFUTED caller-local bounds obligation (`[slice]
//!     FAILED`), minted by the bridge's own slice-index recognizer at the call
//!     site. **This probe does NOT exercise bundling** — see the correction
//!     below; it is kept because the recognizer path is worth a fail-closed
//!     guard of its own, not because it says anything about bundled bodies.
//!   * `probe_bundled_member_div` — the probe that actually tests the bundling
//!     premise, and the one this file previously lacked. See its own comment.
//!
//! Note what is deliberately NOT probed here: a call to a LOCAL panicking impl
//! with a concrete receiver. Verification is modular, so the error lands on
//! `<Boom as AsRef<[u8]>>::as_ref` itself (below) and the caller is entitled to
//! assume a separately-verified callee. The crate still fails; the obligation is
//! just booked against the body that owns it.
//!
//! If this fixture ever compiles clean, read it as a soundness regression: some
//! trait method became total without a resolved body behind it.
//!
//! # The blindness this file was repaired for (measured 2026-08-26)
//!
//! Every probe used to carry exactly one assertion — an `ERROR Trust strict
//! verification failed` line — and there is no `.stderr` companion. That string is
//! the header `report_strict_verification_failure` prints for EVERY fail-closed
//! outcome: a refuted obligation, an unproved absent-callee assumption, and a
//! bundled member's obligation reaching the root all render it identically. So
//! the assertion could not distinguish "the thing I claim to test happened"
//! from "something else failed first", and a probe silently changing mechanism
//! stayed green.
//!
//! It had already happened. `probe_slice_index_range`'s doc used to read:
//!
//!   > a std trait call (`SliceIndex::index`) that DOES resolve, so the new arm
//!   > bundles its body. It must still fail, because the body it bundles is the
//!   > real one and the real one panics on an out-of-range index. Bundling can
//!   > only ADD a callee's obligations to the caller's verdict; if this probe
//!   > ever passes, a body-lowering path has started discarding the obligations
//!   > of the body it lowered.
//!
//! Every clause after the first is false today, and `-Ztrust-dump=native-bundle`
//! settles it in one line: the bundle for `probe_slice_index_range` contains
//! exactly ONE function, the root itself. Nothing is bundled. The collector
//! declines it twice over — once on the peeled slice/array receiver arm added by
//! `fcf90eeb9a` (whose later `AsRef` exemption rescued the sibling
//! `body_proved` fixture but does not cover `Index`), and again on the
//! `core::slice::` plumbing-family arm. What the probe actually fails on is a
//! caller-local `bounds_check` that the bridge's slice recognizer mints at the
//! call site, refuted by `ay` with `counterexample: a__slice_len = 0`. That
//! obligation exists whether or not any callee body is bundled, so the probe was
//! not merely ambiguous between two modes — it was reporting on a mechanism its
//! own doc did not mention, and it would have gone on passing while the
//! regression it named ran free. (Control, same driver: `&a[1..2]` on a
//! `&[u8; 4]` — provable bounds — verifies clean and kernel-certified, i.e. the
//! callee contributes zero obligations either way.)
//!
//! # What a future reader must not weaken
//!
//!   1. **Do not delete a `NOTE` annotation to make this file green.** Each one
//!      names the arm its probe is supposed to take. Deleting it restores exactly
//!      the blindness described above; a green `ERROR` line here has never been
//!      evidence of anything.
//!   2. **Do not replace the `NOTE` pins with a `.stderr` companion.** It
//!      was considered and it cannot work: this fixture's stderr carries
//!      `bundle_digest=sha256:…` and `elapsed_ms=…` from the native verifier
//!      detail block, so a blessed file would be unstable. `dont-check-
//!      compiler-stderr` is set for that reason. Targeted note pins are the
//!      instrument that fits.
//!   3. **A probe whose mechanism legitimately changes needs its NOTE moved, not
//!      removed.** If bundling later admits `SliceIndex::index`, the right edit
//!      is to re-measure and re-pin, and to say so here.
//!   4. **`probe_bundled_member_div` must never be softened into a `check-pass`
//!      or have its `ERROR` annotation dropped.** It is red on purpose; see below.

use std::num::Wrapping;

pub struct Boom;

impl AsRef<[u8]> for Boom {
    fn as_ref(&self) -> &[u8] { //~ ERROR Trust strict verification failed
        // Mechanism pin, RE-MEASURED 2026-08-30 on the stamped build: the row
        // is no longer rendered `[assert] FAILED` — the proof-only Assertion
        // bridge HOLDS the solver counterexample below proof authority, and
        // the held-refutation stamp is what makes it fatal. Pinning the held
        // wording keeps this a mechanism pin: if the bridge ever silently
        // drops the counterexample instead of holding it, this NOTE vanishes
        // and the fixture goes red.
        //~| NOTE [assert] UNKNOWN (trust-full-verifier): a solver counterexample for this assertion was held below proof authority
        panic!("a trait method is user code, and user code panics")
    }
}

// OD-1 phase 1 (2026-10-04), mechanism MOVED per rule 3: `b.as_ref()` on the body's
// own parameter is an ADMITTED instance-hypothesis site (open `AsRef`, unresolved,
// no unsafe, no raw pointer). The definition no longer claims panic-freedom for every
// `B`: it publishes one `assumption:instance-hypothesis` row and passes strict
// CONDITIONALLY (the WARN pin). The panicking `Boom` impl is charged where an instance
// is NAMED: `probe_generic_as_ref_at_boom` names `probe_generic_as_ref::<Boom>`, whose
// discharge row resolves to `<Boom as AsRef<[u8]>>::as_ref`, which is not proved
// panic-free, so that row is `failed` and the strict build is refused there.
pub fn probe_generic_as_ref<B: AsRef<[u8]>>(b: &B) -> usize { //~ WARN 1 instance hypothesis row(s)
    b.as_ref().len()
}

pub fn probe_generic_as_ref_at_boom(b: &Boom) -> usize { //~ ERROR Trust instance discharge not established
    probe_generic_as_ref(b)
}

pub fn probe_dyn_as_ref(b: &dyn AsRef<[u8]>) -> usize { //~ ERROR Trust strict verification failed
    //~| NOTE call to an absent callee
    b.as_ref().len()
}

// NOT a bundling probe — see the correction in the module doc. The callee is
// declined by the collector, and this fails on the caller-local slice-bounds
// obligation the bridge's recognizer mints. Pinning `[slice] FAILED` is what
// stops it from silently drifting onto the absent-callee arm (or onto a
// bundled-member arm) while still printing the same `ERROR` header.
pub fn probe_slice_index_range(a: &[u8]) -> &[u8] { //~ ERROR Trust strict verification failed
    //~| NOTE [slice] FAILED
    &a[1..2]
}

// ---------------------------------------------------------------------------
// The bundling premise itself. THIS is the probe the file's title promises, and
// until 2026-08-26 the file did not contain one.
//
// The premise, stated by every doc in this family: *bundling can only ADD a
// callee's obligations to the caller's verdict.* To test it you need a callee
// that is genuinely BUNDLED and whose body genuinely carries an obligation.
// `SliceIndex::index` is not bundled, so it cannot serve. `Div for Wrapping<u8>`
// can, and it is the exact twin of `native_bundle_std_trait_impl_body_proved`'s
// `probe_wrapping_add`: same receiver type, same operator-trait path, same
// collector arm — one body is total, this one is partial.
//
// Measured 2026-08-26 with `-Ztrust-dump=native-bundle`, stage1 driver
// `rustc 1.99.0-dev (7ac47751a 2026-08-26)`:
//
//   * the bundle for this root contains TWO functions — `["probe_bundled_member_div",
//     "<core::num::wrapping::Wrapping<u8> as core::ops::arith::Div>::div"]` — so
//     the callee body IS in the module, unlike `probe_slice_index_range`'s;
//   * that bundled body ends in `Assert { cond } proofs: ["DivNonZero"]`, a real
//     division-by-zero obligation over the callee's own parameter;
//   * the module's `proof_obligations` list nevertheless holds exactly ONE row,
//     the default `PanicFreedom` function-admission row. The member's assert is
//     not in it. No diagnostic in this fixture mentions this function at all;
//   * compiled on its own, this body verifies with ZERO obligations and exit 0 —
//     not "one obligation, proved"; no verification report is printed at all;
//   * the same division written directly in the caller (`fn f(a: u8, b: u8) -> u8
//     { a / b }`) is correctly refuted: `[divzero] FAILED (ay-in-process);
//     counterexample: _3 = true, a = 0, b = 0`;
//   * and the program built from this exact body panics at runtime:
//     `thread 'main' panicked at core/src/num/wrapping.rs:566:1: attempt to
//     divide by zero` (exit 101).
//
// So the bundled member's obligation is DISCARDED on the way to the root — the
// regression the old `probe_slice_index_range` doc named and could never have
// detected. Both halves of the channel are visible in the source:
//
//   * `reset_native_trust_ir_proof_inventory_to_public_bundle`
//     (`rustc_mir_transform/src/trust_verify.rs`) clears `module.proof_obligations`
//     outright and rebuilds the inventory root-scoped;
//   * the surviving whole-function aggregate in `trust-ir-bridge/src/lower.rs` is
//     emitted ONLY for a diverging panic `Terminator::Call`, deliberately NOT for
//     `Terminator::Assert`. Its stated reason is that "a `Terminator::Assert` site
//     is ALREADY covered by a counted per-site obligation below". That premise is
//     true for a ROOT body and false for a BUNDLED MEMBER, whose per-site row is
//     exactly what the reset just cleared. Neither channel covers the member, so
//     the assert is modeled and then required of nobody.
//
// SAME ROOT CAUSE AS `tests/ui/trust/wrapping_div_zero_false_proof.rs`, which
// already documents it ("An `Assert` inside a BUNDLED callee body mints no proof
// obligation for the caller") and was closed by DECLINING to bundle the primitive
// integer `wrapping_div`/`wrapping_rem` spellings. That fixture is green today —
// verified 2026-08-26 — so the denylist works for the spellings it names. This
// probe reaches the identical defect through a std TRAIT impl,
// `<Wrapping<u8> as Div>::div`, which no primitive-int spelling list covers. That
// is the cost of closing a mechanism defect one spelling at a time, and it is why
// the note in that file — "the better fix is a change to the native-bundle
// planner, which rebuilds `module.proof_obligations` from the compiler's
// obligation list" — is the fix this probe is waiting for.
//
// THIS ANNOTATION CURRENTLY FAILS, AND THAT IS THE CORRECT STATE. The fixture is
// red because the compiler is wrong, not because the test is. Make the planner
// mint a root obligation for a bundled member's `Assert` and this goes green on
// its own. Do not "fix" it by deleting the annotation, by moving the probe to a
// `check-pass` file, or by adding `<Wrapping<_> as Div>` to a decline list — a
// denylist closes this one program and leaves every other bundled `Assert`
// unguarded, which is how the prior false proves in this class were closed and
// why this one was still reachable.
// RE-BLESSED 2026-08-28: the refusing LANE moved. Since the bundled-member
// assert-admission boundary landed (90f22093e9c "refuse uncharged bundled
// member asserts", 48f24efa5af "bind bundled Assert charges exactly"), a
// member whose Assert population is not exactly chargeable is refused
// ADMISSION into the proof-authority bundle, so the compile now fails with
// the full-verification lowering-incomplete refusal instead of a strict-lane
// refutation. Same fail-closed property, different (earlier) chokepoint.
// RESTORED 2026-08-30: that re-bless mis-read WHY admission was refused. The
// 48f24efa5af gate compared the call site's SYNTACTIC identity (the trait
// method's `DefId` + call args, which is what `Terminator::Call` carries)
// against a ledger recording the RESOLVED impl method's identity — two
// different `DefId`s that render identically — so it refused EVERY
// Assert-bearing trait member, chargeable or not. That is not a moved
// chokepoint; it is the aggregate-shaped over-refusal
// `native_bundle_member_derived_requires_per_site.rs` exists to catch (its
// three controls were refused by the same comparison, never chargeable-vs-not).
// With the ledger recording the call-form identity the member is admitted
// again, the derived requires `rhs != 0` is minted per call site, and THIS
// unguarded site is refuted — the strict-lane refutation the annotation
// pinned before the 2026-08-28 re-bless, now with its mechanism pinned too.
// ---------------------------------------------------------------------------
pub fn probe_bundled_member_div(a: Wrapping<u8>, b: Wrapping<u8>) -> Wrapping<u8> { //~ ERROR Trust strict verification failed
    //~| NOTE [precond] FAILED
    a / b
}

fn main() {}
