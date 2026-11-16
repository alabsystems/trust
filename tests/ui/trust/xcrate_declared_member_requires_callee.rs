//@ needs-trust-verify
//@ aux-build:xcmreq_callee.rs
//@ aux-build:xcmreq_mid.rs
//@ aux-build:xcmreq_mid_o3.rs
//@ aux-build:xcmreq_dyn_o3.rs
//@ edition: 2021
//@ revisions: call call_default call_via guarded both inlined direct direct_guarded quiet
//@ revisions: dyn_inlined dyn_inlined_default dyn_quiet
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ rustc-env:TRUST_BUNDLE_TRACE=1
//@[call] compile-flags: -Ztrust-policy=certify
//@[call] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid
//@[call_default] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid
//@[call_via] compile-flags: -Ztrust-policy=certify
//@[call_via] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid
//@[guarded] compile-flags: -Ztrust-policy=certify
//@[guarded] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid
//@[both] compile-flags: -Ztrust-policy=certify
//@[both] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid
//@[inlined] compile-flags: -Ztrust-policy=certify
//@[inlined] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid_o3
//@[direct] compile-flags: -Ztrust-policy=certify
//@[direct] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid
//@[direct_guarded] compile-flags: -Ztrust-policy=certify
//@[direct_guarded] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid
//@[quiet] compile-flags: -Ztrust-policy=certify
//@[quiet] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_callee,xcmreq_mid
//@[dyn_inlined] compile-flags: -Ztrust-policy=certify
//@[dyn_inlined] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_dyn_o3
//@[dyn_inlined] rustc-env:TRUST_DYN_RELIANCE_PROBE=1
//@[dyn_inlined_default] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_dyn_o3
//@[dyn_quiet] compile-flags: -Ztrust-policy=certify
//@[dyn_quiet] compile-flags: -Ztrust-bundle-foreign-crate=xcmreq_dyn_o3
//@[dyn_quiet] rustc-env:TRUST_DYN_RELIANCE_PROBE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[call] check-fail
//@[call_default] check-fail
//@[call_via] check-fail
//@[guarded] check-fail
//@[both] check-fail
//@[inlined] check-fail
//@[direct] check-fail
//@[direct_guarded] check-fail
//@[quiet] check-pass
//@[dyn_inlined] check-fail
//@[dyn_inlined_default] check-fail
//@[dyn_quiet] check-fail
//@[direct] forbid-output: foreign-member-uncharged-requires
//@[direct_guarded] forbid-output: foreign-member-uncharged-requires
//@[quiet] forbid-output: foreign-member-uncharged-requires
//@[dyn_quiet] forbid-output: inlined into its encoded MIR
//! **A declared dependency's bundled member must not reach a function that owes
//! its caller a `requires` by an edge nothing charges (DEP-MEMBER-REQ-1).**
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED. One going green is a possible
//! FALSE ACCEPT until shown otherwise: fix the compiler, never this file. The one
//! exception is `guarded`, read its note below first.
//!
//! # The false accept (measured on a stage 1 of main plus wave 13, `stage1-w13fix`)
//!
//! Three crates; by a reading of targo (not run), the shape `targo trust` gives a
//! workspace `{a, b, c}` when only `a` and `b` are named roots, since a non-root unit
//! is built verify-off. `xcmreq_callee` (`a`) is verified under `certify`
//! and builds clean: `inc` is verified UNDER `requires x < 100`, so the kernel
//! certifies its `x + 1` overflow row under the clause and the compiler ELIDES that
//! check from the MIR it encodes. `xcmreq_mid` (`c`) is built `-Ztrust-verify=off`
//! and its `wrapper` calls `inc` with an argument nothing constrains. This crate
//! (`b`), built `-Ztrust-policy=certify -Ztrust-bundle-foreign-crate=` both,
//! calls `wrapper`.
//!
//! The B-lane bundled `wrapper` AND `inc` as members. A ROOT's direct call is
//! charged a `Precondition` row for the callee's clause, but the member-to-member
//! call `inc(x)` was charged nothing, and the member body it reached had no check
//! left. `f` built rc=0 with its one panic-freedom row proved. The call it makes
//! returns 0 for `u32::MAX` (`xcrate_declared_member_requires_callee_wrong_value_run.rs`
//! prints `xcmreq_mid::wrapper(4294967295) = 0`), where the all-verify-off build
//! panics "attempt to add with overflow". Built against verify-off builds of the
//! same crates (the check still in `inc`), the same `f` was refused, so the
//! dependency's own build mode decided the verdict.
//!
//! # The fix this pins
//!
//! `foreign_member_reaches_uncharged_requires` (trust_verify.rs) makes the B-lane
//! decline a non-local, non-sysroot member whose MIR CALLS a function that owes its
//! caller a `requires` (`def_owes_caller_precondition`, which reads a dependency's
//! exported contract set; for a trait item, also the item the call resolves to),
//! or whose encoded MIR had one INLINED (a `SourceScope` naming it). The call site
//! then takes the fail-closed absent-callee arm, as for an undeclared scope.
//! `TRUST_BUNDLE_TRACE=1` prints the decline, which the `~? RAW` lines require.
//!
//! # Amended 2026-10-05: ADVISORY-REQUIRES-CROSS-CRATE
//!
//! ADVISORY-REQUIRES-CROSS-CRATE (`02e71e93b4`, merged by `d5debba1a8`;
//! docs/DECISION_QUEUE.md) keeps every check a `requires` body's clause proved
//! when another crate can call that body, so `xcmreq_callee::inc` (a `pub fn` of a
//! library) now keeps its `x + 1` overflow `Assert` in the MIR it encodes, even
//! under `certify`, and the premise above no longer holds for `inc`. A root that
//! calls `inc` directly (`direct`, `direct_guarded`, `both`) bundles it as an
//! Assert-bearing foreign member with a contract, which the member `Assert` lane
//! refuses ("member Assert kind `Overflow(Add)` is outside the exact
//! Div/Rem/BoundsCheck lane"): the native bundle is not minted and the root is
//! refused "Trust full verification failed … native typed-TrustIr lowering did not
//! complete", with the note "refused Assert-bearing member `xcmreq_callee::inc`",
//! instead of "Trust strict verification failed … obligation(s) were not fully
//! verified". This is the refusal a verify-off build of `xcmreq_callee` already
//! drew (KNOWN_HAZARDS, DEP-MEMBER-REQ-1), so the verdict no longer depends on the
//! dependency's build mode. Every `check-fail` revision stays refused; `direct`
//! still reports `[precond] FAILED`, and `both` still prints the `wrapper` decline.
//! `call`, `call_default`, `guarded` and `inlined` never bundle `inc` (`wrapper` is
//! declined first), nor does `call_via` (`wrapper_via` is declined first); they
//! keep the strict-verification error.
//!
//! The elision survived for a body no other crate can call: `xcmreq_callee::bump`,
//! private, reached from outside only through the `pub` `inc_via`. `call_via` is
//! the revision whose verdict the decline still decides. Measured 2026-10-05, built
//! outside compiletest with this revision's flags: exit 0 on the stage 1 of
//! `76a6ea45b2` (before the fix; "1 proved … out of 1", `wrapper_via`, `inc_via`
//! and `bump` all bundled), exit 1 with the `wrapper_via` decline on the stage 1 of
//! `444376149e` and of `c1c028f41f`.
//! Since ADVISORY-REQUIRES-TRANSITIVE-1 `bump` keeps its check too (it is named by
//! `inc_via`, a `requires` body another crate can call). `call_via` never bundles
//! `bump` (`wrapper_via` is declined first), so its verdict and its `~? RAW` line are
//! unchanged (measured 2026-10-06 on the stage 1 of `0ac7a96d9f`: every revision's
//! exit code and errors as on the stage 1 of `9e11546767`, and `x.py test` passes).
//!
//! # The revisions
//!
//! * `call` — the measured witness: rc=0 under `certify` before the fix.
//! * `call_default` — the same under the default policy: rc=0 before the fix.
//! * `call_via` — `call` through `xcmreq_mid::wrapper_via` → `inc_via` → the private
//!   `bump`, whose check elided until ADVISORY-REQUIRES-TRANSITIVE-1 (see above):
//!   rc=0 under `certify` before the fix. Its run witness is
//!   `..._wrong_value_run.rs`'s `private_callee`.
//! * `both` — the root ALSO calls `inc` itself, correctly (`inc(1)`, which meets the
//!   clause), so `inc` is bundled through a charged edge, and `wrapper`'s uncharged
//!   call reaches that same member body. Declining `inc` instead of `wrapper` would
//!   leave this open; the decision is made per member body, about what the body
//!   itself calls. rc=0 before the fix. Since ADVISORY-REQUIRES-CROSS-CRATE the
//!   bundled `inc` keeps its `Assert` and is refused as an Assert-bearing member
//!   (see the amendment above); `wrapper` is still declined (the `~? RAW` line).
//! * `inlined` — `xcmreq_mid_o3`, the same `wrapper` built at `-Copt-level=3`: its
//!   MIR inliner copied `inc`'s elided body in, so there is NO CALL to ask about,
//!   only `scope 1 (inlined xcmreq_callee::inc)` over a bare `AddWithOverflow`. A
//!   fix that only read call terminators would leave it rc=0, as it was before.
//! * `guarded` — THE COST, not a hazard: `if v < 50 { wrapper(v) } else { 0 }` does
//!   establish `inc`'s clause and was rc=0 before, soundly. It is refused now
//!   (docs/DECISION_QUEUE.md, DEP-MEMBER-REQ-1). Turning it green is welcome ONLY by
//!   charging a member's call sites with `Precondition` rows inside the bundle, the
//!   recorded recovery; never by bundling `wrapper` uncharged again.
//! * `direct` — the control: the ROOT calls `inc` itself, is charged the clause and
//!   is refused `[precond] FAILED` (counterexample `v = 100`), before and after. The
//!   DEP-MEMBER-REQ-1 decline never fires here (`inc` calls and inlines nothing).
//!   Since ADVISORY-REQUIRES-CROSS-CRATE the bundled `inc` keeps its `Assert`, so the
//!   error is the member `Assert` lane's, and the `[precond] FAILED` row stands.
//! * `direct_guarded` — THE COST of ADVISORY-REQUIRES-CROSS-CRATE, not a hazard:
//!   `if v < 50 { inc(v) } else { 0 }` meets the clause and was accepted under
//!   `certify` ("2 proved … out of 2"; measured on the stage 1 of `83ba8f1181` with
//!   that gate disabled). It is refused now, see the amendment above. Turning it
//!   green is welcome ONLY by charging the member's kept `Assert` (or a certified
//!   record of it) to this root; never by eliding the check from `inc` again.
//! * `quiet` — POSITIVE CONTROL, check-pass: `pick` calls `cap`, which owes its
//!   caller nothing, so the member stays bundled. If this revision fails, the fix
//!   over-refuses.
//!
//! # The C-FLOW (`dyn`) revisions: a RE-DERIVED root, not a member
//!
//! `xcmreq_dyn_o3` (verify-off, `-Copt-level=3`) implements `Shape` for `Sq` by
//! calling `inc`, which its MIR inliner copied in. This crate declares ONLY
//! `xcmreq_dyn_o3` — the single declaration `targo` injects for a direct path
//! dependency — and calls `area` through `&dyn Shape`. The C-FLOW bar re-derives
//! `<Sq as Shape>::area` as its OWN root, so the B-lane member rule above never
//! sees it, and the re-derived body has no call for its verification to charge.
//! Measured at review of `444376149e` (2026-10-05), on that stage 1 and on the
//! stage 1 of `2a1adf641f` alike, with the probe crates
//! (`dyn_mid_o3.rs`/`dyn_cons.rs`) this revision is built from: certify rc=0,
//! `C-FLOW admitted 1 target(s)` and the site `DISCHARGED`, `f` with no row at
//! all; a verify-off `main` linked against it printed `dyn_cons::f(4294967295) = 0`
//! where the all-verify-off twin panics "attempt to add with overflow" (exit 101).
//! Against verify-off builds of the same crates the same consumer was refused, so
//! the dependency's build mode decided the verdict again.
//!
//! The fix: re-derivation's conjunct (7) (`foreign_rederivation.rs`,
//! `body_inlines_requires_owing_callee`, the one inlined-scope test the member
//! drain reads too) declines a body whose encoded MIR inlined a function that owes
//! its caller a `requires`. The C-FLOW bar then admits no target and the `dyn`
//! site keeps its fail-closed row.
//!
//! * `dyn_inlined` — certify; the probe line names conjunct (7). rc=0 before.
//! * `dyn_inlined_default` — the same under the default policy. rc=0 before.
//! * `dyn_quiet` — was the POSITIVE CONTROL of conjunct (7): `Half` inlines
//!   `halve`, which owes its caller nothing, so conjunct (7) does not fire (the
//!   `forbid-output` still holds). Since T6 (2026-10-09) it is refused by
//!   re-derivation's conjunct (8) instead: `xcmreq_dyn_o3` was built at
//!   `-Copt-level=3` outside a proof session, so its encoded MIR is the MIR
//!   inliner's, not the proof-session `-O0` pipeline's
//!   (`trust_crate_mir_is_proof_session_pipeline`), and none of its bodies is
//!   re-derived — a dependency's speed row no longer decides this site. A proof
//!   session never builds a dependency that way, and inside one only
//!   `#[rustc_force_inline]` still inlines, so conjunct (7) keeps its
//!   `dyn_inlined` pins and has no positive control on this crate.
#[cfg(not(any(dyn_inlined, dyn_inlined_default, dyn_quiet)))]
extern crate xcmreq_callee;
#[cfg(not(any(dyn_inlined, dyn_inlined_default, dyn_quiet)))]
extern crate xcmreq_mid;
#[cfg(not(any(dyn_inlined, dyn_inlined_default, dyn_quiet)))]
extern crate xcmreq_mid_o3;
#[cfg(any(dyn_inlined, dyn_inlined_default, dyn_quiet))]
extern crate xcmreq_dyn_o3;

#[cfg(any(call, call_default))]
pub fn f(v: u32) -> u32 {
    //[call,call_default]~^ ERROR Trust strict verification failed for `xcrate_declared_member_requires_callee::f`
    xcmreq_mid::wrapper(v)
}

#[cfg(call_via)]
pub fn f(v: u32) -> u32 {
    //[call_via]~^ ERROR Trust strict verification failed for `xcrate_declared_member_requires_callee::f`
    xcmreq_mid::wrapper_via(v)
}

#[cfg(guarded)]
pub fn f(v: u32) -> u32 {
    //[guarded]~^ ERROR Trust strict verification failed for `xcrate_declared_member_requires_callee::f`
    if v < 50 { xcmreq_mid::wrapper(v) } else { 0 }
}

#[cfg(both)]
pub fn f(v: u32) -> u32 {
    //[both]~^ ERROR Trust full verification failed for `xcrate_declared_member_requires_callee::f`: native typed-TrustIr lowering did not complete
    //[both]~| NOTE refused Assert-bearing member `xcmreq_callee::inc`
    let k = xcmreq_callee::inc(1);
    xcmreq_mid::wrapper(v).wrapping_add(k)
}

#[cfg(inlined)]
pub fn f(v: u32) -> u32 {
    //[inlined]~^ ERROR Trust strict verification failed for `xcrate_declared_member_requires_callee::f`
    xcmreq_mid_o3::wrapper(v)
}

#[cfg(direct)]
pub fn f(v: u32) -> u32 {
    //[direct]~^ ERROR Trust full verification failed for `xcrate_declared_member_requires_callee::f`: native typed-TrustIr lowering did not complete
    //[direct]~| NOTE refused Assert-bearing member `xcmreq_callee::inc`
    //[direct]~| NOTE [precond] FAILED
    xcmreq_callee::inc(v)
}

#[cfg(direct_guarded)]
pub fn f(v: u32) -> u32 {
    //[direct_guarded]~^ ERROR Trust full verification failed for `xcrate_declared_member_requires_callee::f`: native typed-TrustIr lowering did not complete
    //[direct_guarded]~| NOTE refused Assert-bearing member `xcmreq_callee::inc`
    if v < 50 { xcmreq_callee::inc(v) } else { 0 }
}

/// Deliberately not a bare passthrough (see `cross_crate_bundle_scope_declared.rs`):
/// the capped increment gives the caller obligations it must discharge itself, so
/// the pass is a pass WITH proofs.
#[cfg(quiet)]
pub fn f(a: u8) -> u8 {
    let _ = xcmreq_mid::pick(3);
    if a > 200 {
        return 201;
    }
    a + 1
}

#[cfg(any(dyn_inlined, dyn_inlined_default))]
pub fn f(v: u32) -> u32 {
    //[dyn_inlined,dyn_inlined_default]~^ ERROR Trust strict verification failed for `xcrate_declared_member_requires_callee::f`
    let s: &dyn xcmreq_dyn_o3::Shape = &xcmreq_dyn_o3::Sq(v);
    s.area()
}

#[cfg(dyn_quiet)]
pub fn f(v: u32) -> u32 {
    let s: &dyn xcmreq_dyn_o3::Shape = &xcmreq_dyn_o3::Half(v);
    s.area()
}

//[call,call_default,guarded,both]~? RAW [BUNDLE_DROP] reason=foreign-member-uncharged-requires callee=xcmreq_mid::wrapper
//[call_via]~? RAW [BUNDLE_DROP] reason=foreign-member-uncharged-requires callee=xcmreq_mid::wrapper_via
//[inlined]~? RAW [BUNDLE_DROP] reason=foreign-member-uncharged-requires callee=xcmreq_mid_o3::wrapper
//[dyn_inlined]~? RAW C-FLOW declined: target <xcmreq_dyn_o3::Sq as xcmreq_dyn_o3::Shape>::area had a function that owes its caller a `requires` inlined into its encoded MIR
