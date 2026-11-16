//@ needs-trust-verify
//@ revisions: bundled nobundle certify certify_nobundle
//@ compile-flags: -Ztrust-verify=on
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bundled] check-pass
//@[nobundle] rustc-env:TRUST_NO_BUNDLE_STD=1
//@[nobundle] check-pass
//@[certify] compile-flags: -Ztrust-policy=certify
//@[certify] check-fail
//@[certify_nobundle] compile-flags: -Ztrust-policy=certify
//@[certify_nobundle] rustc-env:TRUST_NO_BUNDLE_STD=1
//@[certify_nobundle] check-fail
//! TRUST_NO_SYSROOT_CENSUS (2026-09-26): this file measures the BUNDLING lane, so it
//! runs with the sysroot panic census off. The census (docs/design/trust-std-design.md,
//! amendment 2026-09-26) derives from a std callee's own MIR that it reaches no
//! panic site and discharges the call on the compiler-total channel — which every
//! probe below is (`max`, `Result::ok`, `then_some`, `Wrapping::add`, the `as_ref`s,
//! `String::capacity`, `io::empty` reach no panic), bundled or not. With it on, a
//! dead bundling lane could no longer turn a row red here. The knob is subtractive
//! (it only withholds census grants); the census has its own fixtures in
//! `tests/ui/trust/sysroot_census/`.
//!
//! REGRESSION NET for the B-lane (plan of record
//! `docs/design/2026-08-19-verified-sysroot-scoping.md`, §5 step 2a′):
//! "Add falsification fixtures whose green DEPENDS on a bundled std body. §2.5
//! measured that today's corpus has none: `TRUST_NO_BUNDLE_STD=1` takes it from
//! 124/1 to 125/0. Until such fixtures exist there is no regression net for any
//! of this, and a future refactor could silently delete the B-lane's coverage
//! without a single red row."
//!
//! §2.5's measurement was over the `tests/trust-falsification/proved/` corpus
//! and is correct there. The ui suite was in better shape than the plan
//! records, but only accidentally: of `native_bundle_std_body_proved.rs`'s six
//! probes, exactly ONE (`probe_max_i32`) goes red under `TRUST_NO_BUNDLE_STD=1`
//! — the other five are discharged by audited models, so their green never
//! touched the bundle. (`native_bundle_std_trait_impl_body_proved.rs` is a real
//! net: all five of its probes depend on the lane.) Nothing documented any of
//! that, and no fixture ran the OFF direction at all.
//!
//! This file is the deliberate version. EVERY probe below was measured to
//! prove ONLY via `native_trust_ir_monomorphic_foreign_callees`
//! (trust_verify.rs): green with the lane on, red with it off. The bundled
//! body each green rests on, read from `-Ztrust-dump=native-bundle:<dir>`:
//!
//! (READ THE `certify` SECTION BELOW BEFORE RELYING ON THAT SENTENCE. It was
//! true of the DEFAULT lane's exit code when written; under `certify`, the only
//! policy where this file can still observe anything, four of the eight probes
//! are refused with the lane ON and so discriminate nothing. The four that do
//! are named there. The table below is still accurate as a BUNDLING record —
//! which body each probe's callee resolves to — and that is what it is for.)
//!
//!   probe_max_i32          <- core::cmp::max::<i32>                 (core, free fn)
//!   probe_result_ok        <- core::result::Result::<u8, ()>::ok    (core, inherent)
//!   probe_then_some        <- core::bool::<impl bool>::then_some::<u8>
//!   probe_wrapping_add     <- <Wrapping<u8> as core::ops::arith::Add>::add   (T-IMPL arm)
//!   probe_slice_as_ref     <- <[u8] as core::convert::AsRef<[u8]>>::as_ref   (T-IMPL arm)
//!   probe_string_capacity  <- alloc::string::String::capacity       (alloc, inherent)
//!   probe_string_as_ref    <- <String as core::convert::AsRef<str>>::as_ref  (alloc, T-IMPL)
//!   probe_io_empty         <- core::io::util::empty  (spelled std::io::empty; the
//!                             body lives in core — no probe here reaches a
//!                             std-crate body, which mirrors the corpus: std
//!                             bodies bottom out in OS plumbing the lane declines)
//!
//! The two revisions are the A/B from §2.5, run on byte-identical probes:
//!
//!   * `bundled` (check-pass): the shipped default. If any probe goes red here,
//!     the lane lost coverage — the silent-deletion refactor the plan warns
//!     about now costs a red row.
//!   * `nobundle`: `TRUST_NO_BUNDLE_STD=1`. Every probe must land
//!     on the fail-closed absent-callee arm and ERROR. If any probe stays GREEN
//!     here, either the knob stopped disabling the lane (the §2.5 measurement
//!     lever is broken and every A/B number after that is a lie), or an absent
//!     callee stopped failing closed (a model quietly widened — a soundness
//!     regression, not progress). Both are exactly the "verifier ASSUMES rather
//!     than proves" direction this suite exists to refuse.
//!
//! NEITHER OF THOSE TWO BULLETS IS STILL A LIVE INSTRUMENT, and saying so is the
//! point of the `certify` re-pointing below. Both `bundled` and `nobundle` are
//! `check-pass` today: under the default policy all eight probes land in the
//! tolerated warning class, so `nobundle` cannot produce the ERROR its bullet
//! demands, and `bundled` cannot go red from the lane dying. They are kept
//! because `nobundle` still pins the policy-B disposition (see the last
//! paragraph) — but the live A/B is `[certify]` vs `[certify_nobundle]`.
//!
//! The knob is documented at its read site as strictly subtractive: "There is
//! no setting of this variable that admits anything, downgrades a policy, or
//! turns an obligation into an assumption." This fixture is what notices if
//! that sentence stops being true in either direction.
//!
//! RE-POINTED ONTO `certify` (2026-09-16). This file's A/B was read off the
//! DEFAULT lane's exit code, and policy B took that instrument away on
//! 2026-09-14: `1db02fe416` added `transport_row_is_vanilla_sysroot_absent_callee`,
//! which reclassifies an absent-SYSROOT-callee panic-freedom row from a build
//! error to a reported warning. Every probe here calls a sysroot def at
//! foundational types, so under the default policy ALL EIGHT land in the
//! tolerated class and the `nobundle` revision stopped producing a single error.
//! That commit re-pinned four other fixtures for exactly this disposition change
//! (`absent_sysroot_callee_run_pass`, `debug_of_std_container_run_pass`,
//! `parse_user_fromstr_stays_closed`, `runtime_div_by_zero_stays_closed`) and
//! missed this one and its trait-arm sibling.
//!
//! THE B-LANE ITSELF LOST NOTHING, which is the thing to check before touching a
//! regression net. Measured under `-Ztrust-policy=certify`, where an unproved row
//! is still fatal: lane ON refuses 4 of 8, `TRUST_NO_BUNDLE_STD=1` refuses all 8.
//! The three that survive the knob — `probe_max_i32`, `probe_result_ok`,
//! `probe_then_some` — are the net, and they must stay un-annotated under
//! `[certify]`: if the lane dies, they go red there. (2026-11-10: `probe_then_some`
//! has left the net and `probe_io_empty` has joined it; see RE-MEASURED below.)
//!
//! WIDENED 2026-09-19: `probe_slice_as_ref` moved from the frontier INTO the net,
//! and that is a CAPABILITY GAIN, not an expectation drift. When the `certify`
//! revisions were written (2026-09-16) it was refused by "a `FatPtr` parameter
//! trust-mc's call-summary reader does not admit". `first-party/trust-mc`
//! `e2411e09b` ("Carry opaque fat pointers through typed call summaries") closed
//! exactly that, and the superproject adopted it on 2026-09-18 (`cb117c97a3b`).
//! Measured on the resulting stage1 with compiletest's OWN command for the
//! `certify` revision: that probe emits no error at all, while
//! `[certify_nobundle]` still errors — so its green DEPENDS on the bundled body,
//! which is precisely the property this file exists to hold.
//!
//! Un-annotating it under `[certify]` is the STRONGER direction, not the
//! convenient one: the probe is now a net member, so if the bundled-std lane or
//! trust-mc's fat-pointer carrier ever regresses, this file goes red there. The
//! status quo — annotated as expected-to-fail — would have made that loss
//! invisible.
//!
//!
//! This file does NOT carry `dont-require-annotations: ERROR`, so an
//! unannotated error fails the revision automatically — that is the
//! mechanism by which a dead lane turns these rows red.
//!
//! The four that are refused even with the lane on are a PRE-EXISTING frontier,
//! catalogued by name on 2026-09-14 in
//! `reports/2026-09-14-ui-trust-repair-and-strict-lane-findings.md` as
//! "byte-identical on the sealed pack". Each stops for its own downstream reason
//! — an untrackable `String` aggregate (`string_capacity`), a public-dialect op
//! with no private producer capability (`string_as_ref`), an `Alloca` with no
//! bound extent (`io_empty`), and a solver counterexample (`wrapping_add`) —
//! none of them a bundling failure. (2026-11-10: `io_empty` proves and
//! `then_some` is refused; see RE-MEASURED below.)
//!
//! `probe_slice_as_ref` JOINED THE NET (re-blessed 2026-09-19); the net went
//! from three discriminating probes to four. It was the fifth frontier row, and
//! it now proves with the lane on.
//!
//! WHAT THAT ROW'S OLD REFUSAL REASON ACTUALLY WAS IS NOT ESTABLISHED, and the
//! reason this file used to give was never sourced. Until 2026-09-19 the list
//! above read "a `FatPtr` parameter trust-mc's call-summary reader does not
//! admit (`slice_as_ref`)", introduced by `21083a52b0d` and credited to the
//! 2026-09-14 report cited below. That report does not say it. It assigns
//! `probe_slice_as_ref` to "trust-mc: aggregate solved **without a proof**" —
//! the SAME row as `probe_wrapping_add`, reason "whole-function panic-freedom
//! aggregate: CHC/PDR transport solved obligation … without a proof:
//! counterexample evidence is not a proof" — and the string `FatPtr` appears
//! nowhere near this probe in it. It read that way at `21083a52b0d` too, so the
//! sentence was unsourced when written, not stale since. It is removed rather than
//! re-dated; the pre-flip driver that could measure it no longer exists here.
//! This matters downstream: the follow-up report's case for a specific trust-mc
//! commit reasoned FROM that `FatPtr` wording, so that inference inherits the
//! same defect. See the last bullet.
//!
//! Two reports opened the question and neither closed it:
//! `reports/2026-09-18-a-certify-fixture-went-red-on-the-clean-pin.md`
//! attributed the flip to the `first-party/clean` elaborator pin and asked
//! whether something was reporting `Certified` for a row it had not certified;
//! `reports/2026-09-18-certify-fixture-authority-followup.md` refused that
//! inference and named a trust-mc alternative. The AUTHORITY half of the live
//! check both asked for was run on 2026-09-19 and settles that half — MEASURED,
//! not inferred. The CAUSE half was not run, and the last bullet says so:
//!
//!   * THE AUTHORITY IS trust-mc, NOT THE KERNEL. `-Ztrust-verify-output=json`
//!     on the probe gives `outcome: proved`, `native_trust_ir.suite: trust-mc`,
//!     `proof_evidence.strength.reasoning: ChcSpacer`, `evidence.assurance:
//!     SmtBacked`, `route=TriviallySafe`. No Clean CIC re-check appears anywhere
//!     in the record, so the row is `Trusted`, not `Certified`. The Clean
//!     attribution in the first report is refuted by that measurement. The SAME
//!     record also carries `strength.grade.axiom_closure: Unrecorded` and
//!     `coverage: Unbounded`, quoted here because the strong fields alone read
//!     stronger than the record: this is a sound-analysis discharge with no
//!     recorded axiom closure, not a closed proof.
//!
//!     `route=TriviallySafe` is the field that should make a reader suspicious —
//!     "no Horn rule derives `error`" is the classic vacuous green — so: it is
//!     gated. `trust_mc_chc_credit_witness` (`crates/trust-bmc/src/verifier_api.rs`)
//!     credits that route ONLY for `WholeFunctionStructuralQuery`, where the
//!     rule set IS the obligation, and returns an explicit Err for any other
//!     obligation that takes it ("its solve took the trivially-safe route: no
//!     Horn rule derives the query target"). This probe's row is the counted
//!     whole-function panic-freedom aggregate — the 2026-09-14 report names it
//!     as exactly that when cataloguing the refusal — so it is that one case.
//!     Source-read plus that citation, not a measurement of the gate itself.
//!   * THERE WAS NO SOUNDNESS DEFECT TO FIND, because the first report's premise
//!     was wrong: `-Ztrust-policy=certify` does not require `Certified`. It
//!     requires every Level 0 obligation to be STATICALLY PROVED, and a trust-mc
//!     `Proved` row satisfies it — `is_static_proof_for` (trust_verify.rs)
//!     admits `FreshExactDirectChcPdr`, `DirectTrustVcLive`, `SolverRevalidated`
//!     and others alongside `KernelCertified`. So `certify` refused this probe
//!     before because its row was not statically proved, which is the only thing
//!     `certify` asks — never for want of a kernel re-check. That is a SOURCE
//!     result, not a measurement: the pre-flip driver is gone and what the row
//!     reported then is only known from the first report's transcript.
//!   * THE GREEN STILL DEPENDS ON THE BUNDLE, which is this file's whole point.
//!     `-Ztrust-dump=native-bundle:<dir>` shows the bundle CARRIES the real body
//!     of `<[u8] as core::convert::AsRef<[u8]>>::as_ref` as a second function in
//!     the same trust-ir module — one block, a `FatPtr(Slice)` param, `Copy`,
//!     `Return`, `proofs: ["Pure"]` — and the caller's `Call` targets it. With
//!     `TRUST_NO_BUNDLE_STD=1` that function is absent from the module, the row
//!     falls to the fail-closed absent-callee arm, and `certify` refuses. So the
//!     probe discriminates MORE than it used to, not less: it was red both ways,
//!     and is now green-with-lane / red-without.
//!
//!     That is a STATE, not a change, and is deliberately not offered as one:
//!     the same body is already listed in this file's own 2026-09-14 dump table
//!     above (`probe_slice_as_ref <- … (T-IMPL arm)`), read from the same flag at
//!     a time when the probe WAS refused under `certify`. The body was bundled
//!     before the flip. Whatever changed is therefore downstream of the bundle —
//!     in what CONSUMES the bundled body, not in whether it is bundled — and
//!     this file does not measure what.
//!   * THE ATTRIBUTION IS SCOPED — and it is a NECESSITY result, not a cause.
//!     `TRUST_NO_BUNDLE_STD_TRAIT_IMPL=1` alone — which subtracts ONLY the
//!     T-IMPL arm — takes `probe_slice_as_ref` red while `probe_max_i32`,
//!     `probe_result_ok` and `probe_then_some` stay green. That establishes that
//!     THIS bundled trait-impl body is necessary for today's green, rather than
//!     some global side effect of the whole-lane knob, which is what a net row
//!     has to show. It does NOT identify what changed: "trust-mc learned to read
//!     an already-bundled body" and "something else supplied the missing fact
//!     while the bundle stayed a necessary input" both predict this cell.
//!     `native_bundle_std_trait_arm_knob_scoped.rs` is where that knob is pinned.
//!   * WHAT CHANGED IS NARROWED, NOT ATTRIBUTED — and the `feat(interval)` work
//!     landed the same week is excluded by HISTORY, not by the control above.
//!     The flip was already reported at 2026-09-18 00:35:29 -0700 (`07b91f19ef0`,
//!     the first report below); `77440a33e03` was committed at 03:07:42 and
//!     `e848e0da591` at 04:05:03, and neither is an ancestor of `07b91f19ef0`
//!     (`git merge-base --is-ancestor` refuses both). They did not exist when the
//!     flip was observed. The control could not have excluded them in any case:
//!     both ARE ancestors of the driver every measurement above was taken on.
//!     What remains is the differential the FIRST report records: the same
//!     compiler sources with eight `first-party/*` pins held back vs restored, so
//!     the change is inside the submodule range. `first-party/clean` was the
//!     first report's candidate, and the reading above removes it: this row's
//!     proof is trust-mc's and nothing in the record reaches the CIC kernel.
//!     (Strictly that refutes clean as the DISCHARGING AUTHORITY, which is what
//!     the report claimed; it is not a bisect over the clean range.) The
//!     follow-up report names what is left: `first-party/trust-mc`
//!     `fde4a1b3a0..17ca7adb40`, containing `e2411e09b7` "Carry opaque fat
//!     pointers through typed call summaries". Note that its argument for THAT
//!     commit in particular was "the existing UI fixture describes its previous
//!     `slice_as_ref` limitation as an unsupported `FatPtr` call-summary
//!     parameter" — i.e. it reasoned from this file's own unsourced sentence,
//!     now removed. The pin RANGE survives that; the single commit inside it
//!     does not. So: a PLAUSIBLE cause localized to a pin RANGE, NOT an
//!     established one, and the commit-level guess is weaker than the range.
//!     Closing it means bisecting `first-party/trust-mc` over
//!     `fde4a1b3a0..17ca7adb40` with everything else
//!     at tip and running this file's `[certify]` revision at each step, looking
//!     for the step where `probe_slice_as_ref` goes red. No such build has been
//!     run, by this lane or any earlier one.
//!
//! WHICH DRIVERS THE ABOVE WAS MEASURED ON, because a cell is only as good as
//! the compiler it was read from. Twice, agreeing cell for cell: the sealed pack
//! `ddafc55ba72` (`first-party/trust-mc` `17ca7adb40`) and a stage1 built from
//! `5de63989367` (`first-party/trust-mc` `4d7fbbcd1d`) — 20 trust-mc commits
//! apart, several of them tightening the very CHC/BMC discharge gate this
//! probe's green rests on. That agreement is what licenses the four `[certify]`
//! and eight `[certify_nobundle]` probe expectations here, not just the one cell
//! that moved. `-Ztrust-verify-output=json` was read on the stage1 driver.
//!
//! `[nobundle]` becomes `check-pass`: with the lane off, the default policy
//! REPORTS all eight. That is now this file's pin on the policy-B disposition
//! itself, and it goes red if the tolerance is ever withdrawn.
//!
//! RE-MEASURED 2026-11-10 (`docs/DECISION_QUEUE.md`, NATIVE-BUNDLE-NET-REMEASURE-1).
//! The net and the frontier traded one row each. Neither move is a bundling change.
//! Measured on a stage 1 of `e66b24d03d` (trust-mc `ba679aa25c`) with compiletest's
//! own `[certify]` command, `-Ztrust-dump=native-bundle:<dir>` and
//! `-Ztrust-verify-output=json`:
//!
//!   * `probe_io_empty` PROVES with the lane on and still refuses under
//!     `[certify_nobundle]`. It joins the net. Its authority is trust-mc
//!     (`ChcSpacer`, `SoundAnalysis`), `Trusted`. Its doc comment has the body.
//!   * `probe_then_some` is REFUSED with the lane on. It leaves the net for the
//!     frontier, for the trust-mc reason its doc comment gives. The `[certify]` red
//!     it caused had been on main since at least the 2026-11-06 baseline
//!     `01127ca387`.
//!   * `probe_result_ok` still proves, but trust-mc is no longer its authority. The
//!     row carries the compiler-composed grade (`trust-assert-refute`, premises
//!     `panic-free-callee-registry` and `sibling-rows`) through the zero-obligation
//!     gate's `moved-value-nodrop` arm (R43; `TRUST_PF_REG_TRACE=1` prints
//!     `arm=moved-value-nodrop`). That arm runs only when the bridge elided the
//!     call, which needs the bundled body, so the row still depends on the lane:
//!     `[certify_nobundle]` refuses it.
//!
//! So lane ON refuses 4 of 8 again, and the net is `probe_max_i32`,
//! `probe_result_ok`, `probe_slice_as_ref` and `probe_io_empty`. CONTROL: the
//! `[certify]` command with `TRUST_NO_BUNDLE_STD=1` added reports both errors for
//! each of those four, and none is annotated under `[certify]`, so a dead lane
//! still turns that revision red.

use std::num::Wrapping;

pub fn probe_max_i32(a: i32, b: i32) -> i32 { //[certify_nobundle]~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_max_i32`
//[certify_nobundle]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_max_i32`
    std::cmp::max(a, b)
}

pub fn probe_result_ok(r: Result<u8, ()>) -> Option<u8> { //[certify_nobundle]~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_result_ok`
//[certify_nobundle]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_result_ok`
    r.ok()
}

/// Trust (2026-11-10, NATIVE-BUNDLE-NET-REMEASURE-1): a FRONTIER row now, refused
/// under `[certify]` with the lane ON for a reason downstream of the bundle. The
/// bundle still carries the real `core::bool::<impl bool>::then_some::<u8>` body and
/// the caller's `Call` targets it. trust-mc declines that call's direct summary
/// (`UnsupportedDirectCallSummary`) because the body's `None` arm builds
/// `Option<u8>` from the bridge's partial-construction seed, an aggregate `Undef`
/// overwritten only at `__tag`. trust-mc's operand-consumption gate (trust-mc
/// `5ab307b53`/`1322a5a2d`, in Trust since `8862c94337`) refuses an aggregate
/// `Undef`, which faults at its definition. The canonical seed, a
/// `Constant::Uninit`-lane constant, is refused by name at trust-mc's native input
/// gate until trust-mc's own Uninit carrier exists. When it does, this annotation
/// goes unmatched and the row moves back into the net.
pub fn probe_then_some(b: bool) -> Option<u8> { //[certify]~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_then_some`
//[certify]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_then_some`
//[certify_nobundle]~^^ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_then_some`
//[certify_nobundle]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_then_some`
    b.then_some(1)
}

pub fn probe_wrapping_add(a: Wrapping<u8>, b: Wrapping<u8>) -> Wrapping<u8> { //[certify]~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_wrapping_add`
//[certify]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_wrapping_add`
//[certify_nobundle]~^^ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_wrapping_add`
//[certify_nobundle]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_wrapping_add`
    a + b
}

/// Trust (2026-09-19): A NET ROW, not a frontier row — deliberately UN-annotated
/// under `[certify]`. It proves there, via the bundled
/// `<[u8] as AsRef<[u8]>>::as_ref` body; it refuses under `[certify_nobundle]`,
/// and under `TRUST_NO_BUNDLE_STD_TRAIT_IMPL=1` alone. If the T-IMPL bundling arm
/// regresses, the error here is unannotated and `[certify]` goes red.
///
/// THE GREEN RESTS ON TWO THINGS, and only one of them is a knob in this tree:
/// the T-IMPL bundling arm (which the knob subtracts), and a `first-party/trust-mc` at or after
/// `e2411e09b` ("Carry opaque fat pointers through typed call summaries"),
/// which the superproject adopted on 2026-09-18 in `cb117c97a3b` — the exact
/// commit, established by the other lane that measured this same flip. A trust-mc rollback across that range would take
/// this row red as an UNANNOTATED error under `[certify]` while the bundling arm
/// measures perfectly fine; look at the pin before the arm.
///
/// Do not add a `[certify]` annotation back without re-running the four-revision
/// A/B: the header records what the row's authority actually is (trust-mc
/// `ChcSpacer`, `Trusted` — not a kernel re-check).
pub fn probe_slice_as_ref(n: &[u8]) -> &[u8] { //[certify_nobundle]~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_slice_as_ref`
//[certify_nobundle]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_slice_as_ref`
    n.as_ref()
}

pub fn probe_string_capacity(s: &String) -> usize { //[certify]~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_string_capacity`
//[certify]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_string_capacity`
//[certify_nobundle]~^^ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_string_capacity`
//[certify_nobundle]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_string_capacity`
    s.capacity()
}

pub fn probe_string_as_ref(s: &String) -> &str { //[certify]~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_string_as_ref`
//[certify]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_string_as_ref`
//[certify_nobundle]~^^ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_string_as_ref`
//[certify_nobundle]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_string_as_ref`
    s.as_ref()
}

/// Trust (2026-11-10, NATIVE-BUNDLE-NET-REMEASURE-1): a NET row now, deliberately
/// UN-annotated under `[certify]`. It proves there: trust-mc `ChcSpacer`,
/// `SoundAnalysis` grade, a `Trusted` native authority, not a kernel re-check. The
/// bundled `core::io::util::empty` body is one zero-field aggregate constant and a
/// `Return`, with no `Alloca` (the 2026-09-14 refusal named an `Alloca` with no
/// bound extent). It still refuses under `[certify_nobundle]`, so its green depends
/// on the bundle. If the bundling lane regresses, the error here is unannotated and
/// `[certify]` goes red.
pub fn probe_io_empty() -> std::io::Empty { //[certify_nobundle]~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_green_depends_on_bundle::probe_io_empty`
//[certify_nobundle]~| ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_io_empty`
    std::io::empty()
}

fn main() {}
