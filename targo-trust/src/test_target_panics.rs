// targo trust: the explicit `--test-target-panics` obligation-classification
// policy.
//
// A `#[test]` signals failure BY PANICKING. `assert!` is a panic by
// construction, `assert_eq!` is a panic by construction, and a test helper that
// indexes a vector is doing the thing tests do. Holding that code to
// panic-freedom is a category error: for shipped code Trust demands a STATIC
// proof that the panic is unreachable, but inside a test target the panic IS
// the intended semantics, and Rust already emits the runtime check (bounds
// check, overflow check, panic boundary) that enforces it.
//
// `runtime-checked` is already a gate category with exactly that meaning — an
// obligation not statically discharged whose operation KEEPS the check rustc
// emits — and it already produces a CONDITIONAL pass rather than a failure.
// This module reclassifies PANIC-CLASS refutations raised inside a cargo target
// of kind `["test"]` into that existing category, and nothing else.
//
// "KEEPS the check" is NOT this module's opinion. The repo single-sources that
// question in `VcKind::site_retains_language_check_in`
// (crates/trust-types/src/formula/vc_kind.rs) — "is rustc's own dynamic check
// still at this obligation's site". This module asks THAT predicate, in this
// run's check environment, and layers a narrower policy refusal on top; see
// `is_reclassifiable_obligation`. An earlier revision carried its own
// hand-rolled panic-class list, which disagreed with the authority on
// `UnboundedAllocation` (the language bounds no bulk allocation, so no check
// exists) and admitted `HardenedBoundary { PanicBoundary }` WHOLESALE,
// including the `unwrap`/`expect`/`std::fs` boundaries that stand over no rustc
// check at all. The split between those two halves is the authority's, not this
// module's, which is exactly the point.
//
// WHY `site_retains_language_check_in` AND NOT `has_runtime_fallback_in`, which
// is the other predicate in that file and the one this module used to ask.
// `has_runtime_fallback_in` asks whether the OBLIGATION is discharged
// dynamically, and its `true` is the sole gate on the tree's other producer of
// `RuntimeChecked` (`classify_runtime_disposition_in`,
// crates/trust-types/src/result.rs), which every report goes through. For a
// hardened panic boundary the obligation is "this panic is UNREACHABLE", and
// the surviving `Assert` does not discharge that — it IS the panic. So that
// predicate answers `false` for the whole hardened family and must keep doing
// so, or every report in the tree silently relabels unproved hardened rows.
// What THIS flag needs is the narrower factual question, and it has its own
// name. The reason the two may be answered differently HERE is the flag's whole
// premise: inside a cargo `["test"]` target the panic is the INTENDED failure
// signal, so "the panic still fires" is the answer this flag wants rather than
// the answer the hardening profile refuses.
//
// Everything here is inert unless the caller passes the explicit flag. There is
// NO environment variable and NO default: `TestTargetPanicChoice::Strict` is
// what an absent flag resolves to, and `apply` is a no-op under the
// `TestTargetPanicPolicy::Strict` it resolves to.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use anyhow::{Result, bail};
use trust_types::{HardenedVcCategory, RuntimeCheckEnv, VcKind};

use crate::types::{VerificationOutcome, VerificationResult};

/// The flag this module implements. One spelling, named once.
pub(crate) const FLAG: &str = "--test-target-panics";

/// The `=`-joined spelling, so the parser never rebuilds it from parts.
pub(crate) const FLAG_EQ: &str = "--test-target-panics=";

/// Value that selects today's behaviour explicitly.
pub(crate) const STRICT_VALUE: &str = "strict";

/// Value that selects the reclassification.
pub(crate) const RUNTIME_CHECKED_VALUE: &str = "runtime-checked";

/// Exact opening of the `reason` this policy mints, and the ONLY way a row is
/// later recognized as one it reclassified. It names the flag, because the row
/// must never be readable without the reader learning which explicit choice
/// produced it. Nothing else in Targo or the compiler mints this prefix.
pub(crate) const REASON_PREFIX: &str = "--test-target-panics=runtime-checked:";

/// Ledger tag for a reclassified row in `report.assumptions`.
pub(crate) const LEDGER_TAG: &str = "test-target-panic-runtime-checked";

/// How `targo trust` classifies a PANIC-CLASS obligation raised in a cargo
/// target of kind `["test"]`, AS WRITTEN ON THE COMMAND LINE.
///
/// This is the user's choice and nothing else. It deliberately carries no
/// check environment: the environment is a property of the RUN, and binding
/// the two happens once, in [`TestTargetPanicChoice::resolve`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum TestTargetPanicChoice {
    /// Today's behaviour, and what an ABSENT flag resolves to: a refuted
    /// panic-class obligation in a test target is a refutation like any other.
    #[default]
    Strict,
    /// A refuted panic-class obligation in a test target is recorded as a
    /// runtime-checked CONDITION of the pass. Never a proof.
    RuntimeChecked,
}

impl TestTargetPanicChoice {
    /// Parse the flag value. There is no inferred value: an unrecognized
    /// spelling is an error, never a silent fallback to either behaviour.
    pub(crate) fn parse(value: &str) -> Result<Self> {
        match value {
            STRICT_VALUE => Ok(Self::Strict),
            RUNTIME_CHECKED_VALUE => Ok(Self::RuntimeChecked),
            other => {
                bail!("{FLAG} takes `{STRICT_VALUE}` or `{RUNTIME_CHECKED_VALUE}`, not `{other}`")
            }
        }
    }

    /// Bind this choice to the FALLBACK check environment of the run it will be
    /// applied to. `strict_artifact_policy` is
    /// `SubcommandArgs::strict_artifact_policy()` — the ONE bit that decides
    /// whether targo owns the safety codegen options for this run; see
    /// [`lane_inferred_check_env`].
    ///
    /// The bound value is a FALLBACK, not the answer. A row that carries the
    /// compiler's own `Session::overflow_checks()`/`Session::ub_checks()` is
    /// answered from that measurement instead; this lane inference is what is
    /// left when a row carries nothing. See [`effective_check_env`].
    pub(crate) fn resolve(self, strict_artifact_policy: bool) -> TestTargetPanicPolicy {
        match self {
            Self::Strict => TestTargetPanicPolicy::Strict,
            Self::RuntimeChecked => TestTargetPanicPolicy::RuntimeChecked {
                lane_env: lane_inferred_check_env(strict_artifact_policy),
            },
        }
    }
}

/// The RESOLVED policy: a user choice bound to the check environment of the run
/// it applies to. `RuntimeChecked` cannot be constructed without an environment,
/// because the reclassification it authorizes is a POSITIVE claim that the
/// generated program still carries a dynamic guard, and that claim is only ever
/// true relative to the compile-time check settings — see
/// [`VcKind::site_retains_language_check_in`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum TestTargetPanicPolicy {
    /// Today's behaviour, and what an ABSENT flag resolves to. `apply` is a
    /// no-op under it, so the run stays byte-identical to a build without this
    /// module. It needs no environment: it makes no claim.
    #[default]
    Strict,
    /// Reclassify. `lane_env` is the check environment to fall back to for a row
    /// that does NOT carry the compiler's own — see [`effective_check_env`].
    RuntimeChecked { lane_env: RuntimeCheckEnv },
}

impl TestTargetPanicPolicy {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Strict => STRICT_VALUE,
            Self::RuntimeChecked { .. } => RUNTIME_CHECKED_VALUE,
        }
    }

    /// The FALLBACK environment to answer
    /// [`VcKind::site_retains_language_check_in`] in for a row that carries no
    /// compiler-stated one, or `None` when this policy reclassifies nothing.
    ///
    /// Two changes met here. The authority reconcile moved the flag off
    /// `has_runtime_fallback_in` — which asks whether the property the
    /// obligation ASSERTS is enforced dynamically, and a hardened panic
    /// boundary asserting a panic is unreachable can never be discharged by
    /// the surviving panic — onto the narrower `site_retains_language_check_in`.
    /// The transport change then made the environment a statement by the
    /// compiler rather than an inference by the lane. This field is the lane's
    /// inference, used ONLY when the row carries no stated environment.
    fn reclassifying_env(self) -> Option<RuntimeCheckEnv> {
        match self {
            Self::Strict => None,
            Self::RuntimeChecked { lane_env } => Some(lane_env),
        }
    }
}

/// THE FALLBACK CHECK ENVIRONMENT: what targo can establish about this run
/// WITHOUT the compiler telling it, used only for a row that tells it nothing.
///
/// [`VcKind::site_retains_language_check_in`] answers two families from the
/// environment and the rest from the kind alone:
///
/// * `overflow_checks` (`Session::overflow_checks()`, `-C overflow-checks`)
///   gates `ArithmeticOverflow` / `ShiftOverflow` / `NegationOverflow`;
/// * `ub_checks` (`Session::ub_checks()`, defaulting to `-C debug-assertions`,
///   overridable with `-Z ub-checks`) gates ONLY the unchecked-UB family
///   (`UncheckedArithmeticOverflow`, `UncheckedIndexBounds`).
///
/// WHAT TARGO CAN ESTABLISH ON ITS OWN, MEASURED IN THIS TREE:
///
/// * `overflow_checks` — when `SubcommandArgs::strict_artifact_policy()` is
///   true (neither `--survey` nor `--allow-l0-gaps`), targo itself appends
///   `-C overflow-checks=yes -C debug-assertions=yes` to EVERY compiled unit
///   (`append_strict_safety_check_args` / `append_strict_safety_check_rustflags`,
///   targo-trust/src/pipeline/backend.rs, plus the direct-rustc lane in
///   pipeline/run.rs), `sanitize_inherited_options` strips any inherited
///   `-C overflow-checks=…` first, and `canonicalize_strict_safety_codegen_args`
///   REFUSES a passthrough that tries to own either option. The setting is
///   therefore targo's own: `overflow_checks = true`.
///
///   In every other lane targo appends nothing and, in the words of this tree's
///   own safety-bypass auditor, "advisory and survey lanes deliberately preserve
///   the Cargo profile for artifact fidelity" (`SafetyCheckBypass`,
///   targo-trust/src/main.rs). The effective value is then Cargo's per-unit
///   profile resolution plus inherited `RUSTFLAGS`, which targo neither computes
///   nor records: `detect_safety_check_bypasses` only reports profiles that
///   explicitly say `false`, and an ABSENT `overflow-checks` key proves nothing
///   (the `release` profile defaults it OFF). Targo cannot establish it, so this
///   answers with the value that claims the FEWEST runtime checks:
///   `overflow_checks = false`.
///
/// * `ub_checks` — `false`, ALWAYS, in every lane. Targo owns `-C
///   debug-assertions` in the strict lane but does NOT own `-Z ub-checks`
///   (`sanitize_inherited_z_options` strips only `targo_owned_z_option` names),
///   so an inherited `-Zub-checks=no` could still turn the guard off under a
///   targo-forced `-C debug-assertions=yes`. Answering `false` is the
///   fail-closed direction, and it costs this flag nothing: the two kinds
///   `ub_checks` gates are `get_unchecked` / `unchecked_{add,sub,mul}`, which
///   the policy layer refuses outright — violating one is undefined behaviour,
///   not a panic.
///
/// THIS IS THE FALLBACK, NOT THE ANSWER. The advisory-lane `false` above is a
/// statement about targo's knowledge, not about the compiled program: under
/// `targo trust check --allow-l0-gaps`, Cargo resolves the `dev` profile, whose
/// `overflow-checks` DEFAULTS TO TRUE, so the check is very probably emitted and
/// declining the whole overflow family is counterfactual. The compiler knows the
/// real value exactly — [`effective_check_env`] prefers it wherever a row
/// carries it, and reaches this function only when none does.
fn lane_inferred_check_env(strict_artifact_policy: bool) -> RuntimeCheckEnv {
    RuntimeCheckEnv::new(strict_artifact_policy, false)
}

/// Where the check environment used for one row came from. It is disclosed in
/// the row's `reason`, because a positive runtime-check claim that rests on a
/// measurement and one that rests on targo owning a codegen flag are different
/// claims and a reader is entitled to tell them apart.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckEnvSource {
    /// The compiler stated it: `Session::overflow_checks()` and
    /// `Session::ub_checks()`, minted on the transport envelope of the exact
    /// compilation unit that produced this obligation and carried onto the row
    /// in the authenticated structured transport evidence.
    CompilerStated,
    /// The row stated nothing, so [`lane_inferred_check_env`] answered.
    LaneInferred,
}

/// THE CHECK ENVIRONMENT FOR ONE ROW: the compiler's own measurement when the
/// row carries it, and the conservative lane inference when it does not.
///
/// WHY THE ROW WINS. `Session::overflow_checks()` and `Session::ub_checks()` are
/// exact, per-compilation-unit, and read at the moment the obligation is minted;
/// `lane_env` is an inference from which codegen options targo appended. Where
/// they can differ, the measurement is right by construction — it is the setting
/// the generated program was actually built with, which is precisely what
/// [`VcKind::site_retains_language_check_in`] is asking about. (That doc named
/// `has_runtime_fallback_in` when it was written, before the authority
/// reconcile moved this flag onto the narrower query; the environment question
/// is identical for both.)
///
/// NEITHER DIRECTION IS A NEW RISK:
///
/// * row `true` / lane `false` is the case this exists for — the advisory lane
///   compiling under Cargo's `dev` profile, where `overflow-checks` defaults to
///   TRUE and the check really is emitted. Targo could not establish it; the
///   compiler did not have to.
/// * row `false` / lane `true` moves the OTHER way, to fewer claims: it says a
///   unit was built without the check even though the strict lane appends
///   `-C overflow-checks=yes`. Taking the row is the conservative answer AND the
///   correct one — the program is what it is regardless of what targo appended.
///
/// ABSENCE IS NEVER READ AS TRUE. `None` — an older compiler, a producer that
/// does not mint the field, a row with no structured evidence, a malformed
/// payload — falls back to `lane_env`, which is exactly today's behaviour. The
/// fallback is never `RuntimeCheckEnv::new(true, ..)` unless targo itself owns
/// the flag for the run.
fn effective_check_env(
    result: &VerificationResult,
    lane_env: RuntimeCheckEnv,
) -> (RuntimeCheckEnv, CheckEnvSource) {
    match crate::types::transport_runtime_check_env(result) {
        Some(stated) => (stated, CheckEnvSource::CompilerStated),
        None => (lane_env, CheckEnvSource::LaneInferred),
    }
}

/// WHETHER THIS FLAG MAY RECLASSIFY AN OBLIGATION OF THIS KIND. Two layers, and
/// the order matters.
///
/// LAYER 1 — THE AUTHORITY — is [`VcKind::site_retains_language_check_in`]. It
/// is the repo's single-sourced answer to "does the generated program still
/// execute a rustc-inserted dynamic check at this obligation's site", and it is
/// a strict SUPERSET of [`VcKind::has_runtime_fallback_in`] (which asks the
/// stronger question of whether the check DISCHARGES the obligation — see the
/// module header for why this flag, and only this flag, may ask the weaker one).
/// A hand-rolled second list is exactly how the two drift: the list this
/// replaced admitted `UnboundedAllocation` (the language does not bound
/// bulk-allocation sizes — that absence is WHY the obligation exists), for which
/// the authority answers `false`, and the WHOLE `HardenedBoundary
/// { PanicBoundary }` family, for which the authority answers per the operation
/// the boundary stands over: `true` for the `mir_assert::*` subfamily raised
/// over a rustc-inserted `Assert`, `false` for the `unwrap` / `expect` /
/// `std::fs` call boundaries that stand over no check at all.
///
/// LAYER 2 — POLICY — is [`policy_admits_panic_class`]. It refuses obligations
/// the authority would allow, for reasons that are about what this FLAG is for
/// rather than about whether a monitor exists. It can only ever SHRINK the set.
///
/// Neither layer alone is enough and both are kept on purpose: layer 1 cannot
/// know that `division_by_zero` was left off the authorized list, and layer 2
/// must never be the thing that decides a monitor exists.
fn is_reclassifiable_obligation(kind: &VcKind, env: RuntimeCheckEnv) -> bool {
    kind.site_retains_language_check_in(env) && policy_admits_panic_class(kind)
}

/// LAYER 2. The obligations this flag is authorized to reclassify, ASSUMING
/// layer 1 has already established that a runtime check exists. Every arm is a
/// refusal or an allowance about POLICY, never about mechanism.
///
/// ALLOWED, each a Rust panic a `#[test]` legitimately uses as its failure
/// signal (the report tag it renders as is named beside it):
///
/// * `SliceBoundsCheck` / `IndexOutOfBounds` (`slice_bounds_check`,
///   `index_out_of_bounds`) — `panic_bounds_check`;
/// * `ArithmeticOverflow` / `NegationOverflow` / `ShiftOverflow`
///   (`arithmetic_overflow_*`, `negation_overflow`, `shift_overflow_*`) —
///   `mir_assert::Overflow*`. Layer 1 admits these only when `overflow_checks`
///   is on in this run's environment;
/// * `RemainderByZero` (`remainder_by_zero`) — `mir_assert::RemainderByZero`;
/// * `Assertion` whose message is a DIRECT panic call — see
///   [`assertion_is_a_direct_panic_call`].
///
/// REFUSED, and why it is policy and not mechanism:
///
/// * `DivisionByZero` — panic-class in fact, and layer 1 says `true` for it,
///   but it is not on the authorized list, so it stays a refutation. Fail
///   closed on an obligation nobody asked this flag to forgive.
/// * every unsafe-discipline finding — `HardenedBoundary { UnsafeOperation }`,
///   `UnsafeOperation`, and the separation engine's `[unsafe:sep:…]`
///   assertions, all routed by `hardened_category()`, which is the single
///   source of truth for that classification. Layer 1 already declines each of
///   them; this restates it as policy because "a test may panic" is not a
///   reason to forgive an unsafe-block discipline finding even if one of them
///   ever acquired a monitor.
/// * `Unreachable` — reaching a MIR `Terminator::Unreachable` is UNDEFINED
///   BEHAVIOUR, not a panic. Layer 1 also declines it (the unit variant cannot
///   tell a bare `Unreachable`, lowered to `llvm.unreachable` with no check at
///   all, from a panic-backed one); this restates it because the UB/panic
///   distinction is the flag's whole premise.
/// * `UnsupportedMir` — layer 1 can recover a runtime fallback through a
///   round-tripped full-lane tag, but an unsupported-MIR row is not a panic
///   obligation this flag was authorized over, and it is also the carrier
///   `report_vc_kind` uses for declared contract panics and `assumption:` rows.
///   Refused outright.
/// * every hardened boundary except the `mir_assert::*` panic subfamily named
///   in [`policy_admits_hardened_mir_assert`] — and, inside that subfamily,
///   `mir_assert::DivisionByZero`, refused for exactly the reason
///   `VcKind::DivisionByZero` is refused above.
/// * everything else — contract, temporal, ownership, FFI, binary and
///   functional families. Layer 1 declines all of them; the wildcard here
///   means a NEW `VcKind` variant is out of scope until someone adds it
///   deliberately.
fn policy_admits_panic_class(kind: &VcKind) -> bool {
    // An unsafe-discipline finding is refused whatever else it looks like, and
    // before anything else, because `hardened_category` classifies three
    // different carriers (`HardenedBoundary { UnsafeOperation }`,
    // `UnsafeOperation`, and an `Assertion` whose message opens `[unsafe…`) into
    // the one category.
    if matches!(kind.hardened_category(), Some(trust_types::HardenedVcCategory::UnsafeOperation)) {
        return false;
    }
    match kind {
        VcKind::SliceBoundsCheck
        | VcKind::IndexOutOfBounds
        | VcKind::ArithmeticOverflow { .. }
        | VcKind::NegationOverflow { .. }
        | VcKind::ShiftOverflow { .. }
        | VcKind::RemainderByZero => true,
        VcKind::Assertion { message } => assertion_is_a_direct_panic_call(message),
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary, callee, ..
        } => policy_admits_hardened_mir_assert(callee),
        _ => false,
    }
}

/// LAYER 2, hardened panic-boundary half. Whether this flag is authorized over a
/// `unix_hardened` panic boundary, ASSUMING layer 1 has already established that
/// the operation underneath it keeps its check.
///
/// A hardened boundary is a hardening-PROFILE proof requirement, and most of them
/// stand over nothing rustc checks — `unwrap`, `expect`, `std::fs::rename`,
/// `chroot`. Layer 1 declines every one of those, because their `callee` is a real
/// call path and not a `mir_assert::` marker. What is left is the subfamily raised
/// over a rustc-inserted `Assert`, and for those the boundary and the
/// per-statement obligation are the SAME runtime panic-check — which is not this
/// module's opinion either: it is what `PanicTwinFamily` /
/// `subsume_hardened_panic_twins` (targo-trust/src/types.rs) already models, and
/// why a proved per-statement sibling is already allowed to discharge an Unknown
/// twin.
///
/// ADMITTED: exactly the `mir_assert` families whose PRIMARY kind
/// [`policy_admits_panic_class`] admits above — `BoundsCheck` (<-> bounds),
/// `Overflow(..)` (<-> arithmetic and shift overflow), `OverflowNeg` (<-> negation
/// overflow), `RemainderByZero`.
///
/// REFUSED: `mir_assert::DivisionByZero`, for the SAME reason `VcKind::
/// DivisionByZero` is refused above — panic-class in fact, but not on the list
/// anyone asked this flag to forgive, and the two spellings of one obligation must
/// not answer differently. Every other marker, and every non-marker callee, is
/// refused here as well as by layer 1.
///
/// The recognizer is NOT re-implemented: the marker is stripped by
/// `trust_types::hardened_mir_assert_message`, the same single source layer 1's
/// authority reads, so this list can only ever be a SUBSET of what layer 1 admits.
fn policy_admits_hardened_mir_assert(callee: &str) -> bool {
    match trust_types::hardened_mir_assert_message(callee) {
        Some("BoundsCheck" | "OverflowNeg" | "RemainderByZero") => true,
        Some(message) if message.starts_with("Overflow(") && message.ends_with(')') => true,
        Some(_) | None => false,
    }
}

/// Whether an `Assertion` row's failure is a DIRECT panic call in this
/// function's own body — the only assertion shape this flag may reclassify.
///
/// ELIGIBLE: a message that begins exactly `panic call: `. That text has ONE
/// producer in the whole tree — `v2_panic_call_vc_message`
/// (crates/trust-vcgen/src/generate/assert_refutation.rs), described at its
/// consumer as "the ONLY minter of this text"
/// (compiler/rustc_mir_transform/src/trust_verify.rs). Every one of its three
/// call sites mints the VC for a `Terminator::Call` in THIS function's body
/// whose callee a panic-entrypoint recognizer accepted
/// (`terminator_obligations::is_assertion_panic_call` — `begin_panic`,
/// `panic_fmt`, `panic_display`, `assert_failed` — the bare `::panic`
/// intrinsic, or the `unreachable!()` sentinel), and the VC's formula is that
/// block's path FEASIBILITY condition. A refutation therefore says exactly
/// "this panic call is reachable", which in a `#[test]` is the failure signal
/// the test is written to raise, and the panic itself is the runtime check. The
/// prefix is the provenance, so no second recognizer is re-implemented here
/// that could disagree with the minter.
///
/// REFUSED, and this is the hole this reader was rewritten to close:
///
/// * `panic freedom: …` — the WHOLE-FUNCTION INTERPROCEDURAL catch-all
///   ("panic freedom: no assertion, `unreachable!`, or panic is reachable",
///   synthesized in compiler/rustc_mir_transform/src/trust_verify.rs). Its
///   claim ranges over `unreachable!` AND over CALLEE BODIES, so its refutation
///   can be caused by a bare `Terminator::Unreachable` — undefined behaviour
///   with no check emitted, which this flag must never touch — or by a panic in
///   a function belonging to a DIFFERENT, non-test cargo target that the test
///   merely calls, which this flag's target scoping is specifically designed to
///   exclude. The row's own text cannot tell those apart from an honest
///   test-local panic, so the whole family is refused.
/// * the `[trust-contract-panic] panic call: …` marker form, and any other
///   prefix: the check is ANCHORED, so a marker, a `metadata_keys=` restatement
///   or an embedded mention inside a longer message does not match. (A declared
///   contract panic never reaches here as an `Assertion` anyway —
///   `report_vc_kind` re-carries it as `UnsupportedMir` — so this is belt and
///   braces.)
/// * an `Assertion` carrying an authored, temporal or engine-minted obligation:
///   `VcKind::Assertion` is the carrier for those too, and the word "assertion"
///   is not evidence of a panic.
fn assertion_is_a_direct_panic_call(message: &str) -> bool {
    message.strip_prefix(PANIC_CALL_PREFIX).is_some_and(|callee| !callee.is_empty())
}

/// The exact opening `v2_panic_call_vc_message` renders for a panic-call VC.
const PANIC_CALL_PREFIX: &str = "panic call: ";

/// The package / kinds / target of the `cargo-target(...)::` scope prefix that
/// `CargoTargetIdentity::scope_function` puts on every merged transport row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CargoTargetScope {
    pub(crate) package: String,
    pub(crate) kinds: Vec<String>,
    pub(crate) target: String,
}

impl CargoTargetScope {
    /// Whether this is a cargo TEST target.
    ///
    /// Exact and fail-closed: every kind in the list must be `test`, which is
    /// the shape Cargo produces for a `[[test]]`/`tests/` target (`["test"]`).
    /// A `lib`, `bin`, `example`, `bench`, `custom-build` or `proc-macro`
    /// target — INCLUDING a library compiled in test mode, whose kind stays
    /// `["lib"]` — answers `false`, so a non-test target that a test target
    /// merely calls keeps every refutation it earned.
    pub(crate) fn is_test_target(&self) -> bool {
        !self.kinds.is_empty() && self.kinds.iter().all(|kind| kind == "test")
    }

    fn describe(&self) -> String {
        format!("package `{}`, target `{}`, kind {:?}", self.package, self.target, self.kinds)
    }
}

/// Read the hidden Cargo proof-unit identity off a scoped function name.
///
/// The prefix is minted by `CargoTargetIdentity::report_label`
/// (targo-trust/src/pipeline/transport.rs) as
/// `cargo-target(package_id={:?},package={:?},kind={:?},target={:?},…)::<fn>`,
/// so this walks those four fields IN ORDER through a real Rust-debug string
/// reader rather than searching for `kind=[` — a package id is a URL and
/// substring searching it is how a parser starts believing the wrong field.
/// Anything that does not match exactly returns `None`, and a `None` row is
/// never reclassified.
pub(crate) fn cargo_target_scope(scoped_function: &str) -> Option<CargoTargetScope> {
    let rest = scoped_function.strip_prefix("cargo-target(")?;
    let rest = rest.strip_prefix("package_id=")?;
    let (_package_id, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",package=")?;
    let (package, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",kind=")?;
    let (kinds, rest) = take_debug_string_list(rest)?;
    let rest = rest.strip_prefix(",target=")?;
    let (target, _rest) = take_debug_string(rest)?;
    Some(CargoTargetScope { package, kinds, target })
}

/// Trust (CB4): the Cargo compile mode of the proof unit a scoped row belongs
/// to, read off the same `cargo-target(...)::` prefix as
/// [`cargo_target_scope`].
///
/// Walks EVERY field `CargoTargetIdentity::report_label` writes before
/// `proof_unit_mode`, in order, through the same Rust-debug readers, and
/// returns the mode only when Cargo's two spellings of it agree
/// (`compile_mode == proof_unit_mode`). Anything else — an unscoped row (raw
/// single-file compile), a label of another shape, a disagreement — is `None`,
/// and a caller asking "is this a test-harness unit?" must read `None` as no.
pub(crate) fn cargo_target_unit_mode(scoped_function: &str) -> Option<String> {
    let rest = scoped_function.strip_prefix("cargo-target(")?;
    let rest = rest.strip_prefix("package_id=")?;
    let (_package_id, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",package=")?;
    let (_package, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",kind=")?;
    let (_kinds, rest) = take_debug_string_list(rest)?;
    let rest = rest.strip_prefix(",target=")?;
    let (_target, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",compile_target=")?;
    let (_compile_target, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",compile_mode=")?;
    let (compile_mode, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",compile_kind=")?;
    let (_compile_kind, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",unit_identity_sha256=")?;
    let (_unit_identity, rest) = take_debug_string(rest)?;
    let rest = rest.strip_prefix(",compile_target_spec_sha256=")?;
    let rest = match rest.strip_prefix("None") {
        Some(rest) => rest,
        None => {
            let (_spec, rest) = take_debug_string(rest.strip_prefix("Some(")?)?;
            rest.strip_prefix(')')?
        }
    };
    let rest = rest.strip_prefix(",proof_unit_index=")?;
    let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
    if digits == 0 {
        return None;
    }
    let rest = rest.get(digits..)?.strip_prefix(",proof_unit_mode=")?;
    let (proof_unit_mode, rest) = take_debug_string(rest)?;
    if !rest.starts_with(",proof_unit_role=") {
        return None;
    }
    (compile_mode == proof_unit_mode).then_some(proof_unit_mode)
}

/// Read one `{:?}`-formatted Rust string, returning it and the remaining input.
fn take_debug_string(input: &str) -> Option<(String, &str)> {
    let body = input.strip_prefix('"')?;
    let mut out = String::new();
    let mut index = 0usize;
    while index < body.len() {
        let rest = body.get(index..)?;
        let ch = rest.chars().next()?;
        match ch {
            '"' => return Some((out, body.get(index + 1..)?)),
            '\\' => {
                let escaped = rest.get(1..)?.chars().next()?;
                match escaped {
                    '"' => out.push('"'),
                    '\\' => out.push('\\'),
                    '\'' => out.push('\''),
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    '0' => out.push('\0'),
                    'u' => {
                        let braced = rest.get(2..)?.strip_prefix('{')?;
                        let end = braced.find('}')?;
                        let code = u32::from_str_radix(braced.get(..end)?, 16).ok()?;
                        out.push(char::from_u32(code)?);
                        index += 2 + 1 + end + 1;
                        continue;
                    }
                    // An escape this reader does not model means the identity is
                    // not the shape it was told to expect. Fail closed.
                    _ => return None,
                }
                index += 1 + escaped.len_utf8();
            }
            _ => {
                out.push(ch);
                index += ch.len_utf8();
            }
        }
    }
    None
}

/// Read one `{:?}`-formatted `Vec<String>`, returning it and the rest.
fn take_debug_string_list(input: &str) -> Option<(Vec<String>, &str)> {
    let mut rest = input.strip_prefix('[')?;
    let mut out = Vec::new();
    if let Some(tail) = rest.strip_prefix(']') {
        return Some((out, tail));
    }
    loop {
        let (value, tail) = take_debug_string(rest)?;
        out.push(value);
        rest = tail;
        if let Some(tail) = rest.strip_prefix(", ") {
            rest = tail;
            continue;
        }
        return rest.strip_prefix(']').map(|tail| (out, tail));
    }
}

/// Whether ONE row is in scope for the reclassification, and — when it is — the
/// target it belongs to plus the check environment the decision was taken in.
/// Pure: it mutates nothing, and it decides nothing the two eligibility layers
/// in [`is_reclassifiable_obligation`] have not decided.
///
/// `lane_env` is only a FALLBACK here: [`effective_check_env`] prefers the
/// compiler-stated environment this row carries.
fn reclassifiable(
    result: &VerificationResult,
    lane_env: RuntimeCheckEnv,
) -> Option<(CargoTargetScope, RuntimeCheckEnv, CheckEnvSource)> {
    if !matches!(result.outcome, VerificationOutcome::Failed) {
        return None;
    }
    let scope = cargo_target_scope(&result.function)?;
    if !scope.is_test_target() {
        return None;
    }
    let (env, source) = effective_check_env(result, lane_env);
    is_reclassifiable_obligation(&crate::report::report_vc_kind(result), env)
        .then_some((scope, env, source))
}

/// Apply the policy to one run's publication rows, returning how many rows it
/// reclassified.
///
/// Under [`TestTargetPanicPolicy::Strict`] — which is what an ABSENT flag
/// resolves to — this touches nothing and returns 0, so the whole run stays
/// byte-identical to a build without this code.
///
/// Under [`TestTargetPanicPolicy::RuntimeChecked`] a refuted panic-class row in
/// a `["test"]` target becomes [`VerificationOutcome::RuntimeChecked`] and
/// carries a `reason` naming the flag and the exact cargo target. Nothing
/// becomes `Proved`, no row is removed, no counterexample is discarded, and no
/// proof evidence is minted: the row keeps its kind, its message and its
/// location, and only moves between two EXISTING gate buckets.
pub(crate) fn apply(results: &mut [VerificationResult], policy: TestTargetPanicPolicy) -> usize {
    let Some(lane_env) = policy.reclassifying_env() else {
        return 0;
    };
    let mut reclassified = 0usize;
    for result in results.iter_mut() {
        let Some((scope, env, source)) = reclassifiable(result, lane_env) else {
            continue;
        };
        result.outcome = VerificationOutcome::RuntimeChecked;
        result.reason = Some(format!(
            "{REASON_PREFIX} the static proof was REFUTED, and this obligation is accepted as a \
             runtime-checked condition of the pass because it is a panic-class obligation \
             (`{}`) raised in a cargo test target ({}). A `#[test]` signals failure by \
             panicking and Rust still emits this check, so the check is the intended \
             semantics here. This is NOT a proof, and the same obligation in any non-test \
             target is still a refutation.{}",
            crate::report::report_vc_kind(result).transport_tag(),
            scope.describe(),
            check_env_disclosure(env, source),
        ));
        reclassified += 1;
    }
    reclassified
}

/// The sentence appended to a reclassified row's `reason` saying which check
/// environment the runtime-check claim was decided in, and on whose word.
///
/// A reader auditing a conditional pass needs to separate "the compiler that
/// built this unit says the check is on" from "targo appended the flag that
/// turns it on", because only the first survives a lane that does not own the
/// codegen options. The values are stated, not just their source.
fn check_env_disclosure(env: RuntimeCheckEnv, source: CheckEnvSource) -> String {
    let settings = format!("overflow_checks={}, ub_checks={}", env.overflow_checks, env.ub_checks);
    match source {
        CheckEnvSource::CompilerStated => format!(
            " The runtime-check environment is the COMPILER'S OWN, minted by the compilation \
             unit that raised this obligation and carried on its authenticated transport \
             evidence: {settings}."
        ),
        CheckEnvSource::LaneInferred => format!(
            " This row carried no compiler-stated runtime-check environment, so the \
             conservative environment targo can establish from the lane it is running was \
             used instead: {settings}."
        ),
    }
}

/// Whether a row in a finished report is one this policy reclassified. The
/// `reason` prefix is minted only by [`apply`], so this is exact.
pub(crate) fn is_reclassified_row(result: &VerificationResult) -> bool {
    matches!(result.outcome, VerificationOutcome::RuntimeChecked)
        && result.reason.as_deref().is_some_and(|reason| reason.starts_with(REASON_PREFIX))
}

/// The conditions ledger entry for one reclassified row, so a reader can see
/// exactly what was conditionally accepted and on whose say-so.
pub(crate) fn ledger_entry(result: &VerificationResult) -> Option<trust_types::AssumptionEntry> {
    if !is_reclassified_row(result) {
        return None;
    }
    Some(trust_types::AssumptionEntry {
        scope: "function".to_string(),
        subject: result.function.clone(),
        tag: LEDGER_TAG.to_string(),
        detail: result.reason.clone().unwrap_or_default(),
        location: result.location.clone(),
        source: result.backend.clone(),
    })
}

/// The terminal disclosure block. Empty when the policy reclassified nothing,
/// so an absent flag adds not one byte of output.
pub(crate) fn terminal_lines(results: &[VerificationResult]) -> Vec<String> {
    let rows = results.iter().filter(|result| is_reclassified_row(result)).collect::<Vec<_>>();
    if rows.is_empty() {
        return Vec::new();
    }
    let mut lines = vec![format!(
        "Test-target panic policy: {} refuted panic-class obligation(s) in cargo test targets \
         were recorded as RUNTIME-CHECKED conditions of this run by `{FLAG}={RUNTIME_CHECKED_VALUE}` \
         — they are counted in the Gate line's runtime-checked bucket and listed in the \
         assumptions/conditions ledger; NONE of them is proved.",
        rows.len()
    )];
    let mut by_target: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    for row in rows {
        let key = cargo_target_scope(&row.function)
            .map_or_else(|| "<unparseable cargo target>".to_string(), |scope| scope.describe());
        *by_target.entry(key).or_default() += 1;
    }
    lines.extend(
        by_target
            .into_iter()
            .map(|(target, count)| format!("  Reclassified {count} obligation(s) in {target}")),
    );
    lines
}

/// The `--help` paragraph. It says what the flag does AND what it does not do,
/// because a reader who learns only the first half will over-trust the result.
pub(crate) fn help_lines() -> Vec<&'static str> {
    vec![
        "  --test-target-panics=<strict|runtime-checked>",
        "                          How to classify a PANIC-CLASS obligation raised in a cargo",
        "                          target of kind [\"test\"]. No default: omitting this flag is",
        "                          exactly `strict`, today's behaviour. There is no environment",
        "                          variable for it.",
        "                            strict           a refuted panic-class obligation in a test",
        "                                             target is a REFUTATION, as it is anywhere",
        "                                             else.",
        "                            runtime-checked  such a row is recorded as RUNTIME-CHECKED:",
        "                                             a `#[test]` signals failure by panicking and",
        "                                             Rust still emits the bounds/overflow/panic",
        "                                             check, so in a test the runtime check is the",
        "                                             intended semantics.",
        "                          A row is eligible ONLY when the compiler's own",
        "                          `VcKind::site_retains_language_check_in` says the generated",
        "                          program still executes a rustc-inserted check at that site in",
        "                          THIS run's check environment. That predicate is the authority;",
        "                          the list below is a further, narrower policy refusal on top.",
        "                          DOES apply to: slice_bounds_check, index_out_of_bounds,",
        "                          remainder_by_zero, and an `assertion` row whose message begins",
        "                          `panic call: ` (a direct call to a panic entry point in the",
        "                          function's own body).",
        "                          DOES apply to a `hardened_panic_boundary` raised over a",
        "                          rustc-inserted MIR assert (`mir_assert::BoundsCheck`,",
        "                          `mir_assert::RemainderByZero`, and the `mir_assert::Overflow*`",
        "                          family under the same `-C overflow-checks` condition below):",
        "                          the hardening profile does not touch codegen, so that assert",
        "                          is still executing in the test binary. It does NOT apply to",
        "                          the rest of that family — see the refusals below.",
        "                          DOES apply to arithmetic_overflow_*, negation_overflow and",
        "                          shift_overflow_* ONLY where the overflow check was really",
        "                          emitted. That is read off the COMPILER: each row carries the",
        "                          `Session::overflow_checks()` / `Session::ub_checks()` of the",
        "                          unit that raised it, and the row is answered from that. A row",
        "                          that carries no such statement (an older compiler, a producer",
        "                          that does not mint it) falls back to what targo can establish",
        "                          alone — true only when targo itself owns `-C overflow-checks`,",
        "                          i.e. NOT under --allow-l0-gaps or --survey, which preserve the",
        "                          Cargo profile. Absence is never read as `on`. Each reclassified",
        "                          row\'s reason states the environment used and which of the two",
        "                          it came from.",
        "                          DOES NOT apply to: `unreachable` (reaching it is undefined",
        "                          behaviour, not a panic), `hardened_unsafe_operation` or any",
        "                          other unsafe-discipline finding, `division_by_zero`,",
        "                          `unbounded_allocation` (the language bounds no bulk allocation",
        "                          — that absence is why it is an obligation), a",
        "                          `hardened_panic_boundary` raised over a CALL such as `unwrap`,",
        "                          `expect` or `std::fs::rename` (the panic is in the callee;",
        "                          rustc inserts nothing at the site) or over",
        "                          `mir_assert::DivisionByZero` (refused by name, in lock-step",
        "                          with `division_by_zero`), an `assertion` row reading",
        "                          `panic freedom:`",
        "                          (the whole-function catch-all, which ranges over `unreachable!`",
        "                          and over callee bodies), or ANY obligation in a lib, bin,",
        "                          example, bench or build-script target — including a non-test",
        "                          target that a test merely calls.",
        "                          It NEVER proves anything: a reclassified row is counted,",
        "                          printed, written to report.json and listed in the",
        "                          assumptions/conditions ledger with the reason naming this flag",
        "                          and the target. It makes the advisory lane a CONDITIONAL PASS;",
        "                          `--certify` still folds every runtime-checked row into a",
        "                          nonzero exit, so the release gate is unaffected.",
    ]
}

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, HardenedVcCategory, Ty};

    use super::*;
    use crate::pipeline::hardened::{
        GateDecision, GateLane, evaluate_verification_gate, partition_outcome_counts,
    };
    use crate::pipeline::transport::CargoTargetIdentity;

    /// Build the exact Cargo proof-unit identity the transport mints, so every
    /// test below reads the scope prefix through the SAME producer production
    /// uses. A hand-written prefix would let the reader and the minter drift.
    fn identity(kinds: &[&str], target: &str) -> CargoTargetIdentity {
        CargoTargetIdentity {
            package_id: "path+file:///w/ay-dpll#0.27.0".to_string(),
            package_name: "ay-dpll".to_string(),
            target_name: target.to_string(),
            target_kinds: kinds.iter().map(|kind| (*kind).to_string()).collect(),
            compile_target: "aarch64-apple-darwin".to_string(),
            compile_mode: "test".to_string(),
            compile_kind: "host".to_string(),
            unit_identity_sha256: "a".repeat(64),
            compile_target_spec_sha256: None,
            proof_unit_index: 7,
            proof_unit_mode: "test".to_string(),
            proof_unit_role: "primary".to_string(),
            semantics_sha256: "b".repeat(64),
        }
    }

    fn scoped(kinds: &[&str], target: &str, function: &str) -> String {
        format!("{}::{function}", identity(kinds, target).report_label())
    }

    /// One authenticated transport row carrying the exact typed VC payload, so
    /// `report_vc_kind` recovers the same `VcKind` production would.
    fn row(kind: &VcKind, function: &str, outcome: VerificationOutcome) -> VerificationResult {
        let evidence = serde_json::json!({
            "obligation_id": "obligation-1",
            "claim_digest_sha256": "c".repeat(64),
            "typed_kind": kind,
        });
        VerificationResult {
            function: function.to_string(),
            kind: kind.transport_tag(),
            message: kind.description(),
            outcome,
            backend: "ay-in-process".to_string(),
            time_ms: Some(3),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: format!("targo-trust-structured-transport-evidence:{evidence}"),
        }
    }

    fn failed(kind: &VcKind, function: &str) -> VerificationResult {
        row(kind, function, VerificationOutcome::Failed)
    }

    /// The SAME authenticated transport row, plus the compiler-stated
    /// runtime-check environment of the unit that minted it. Built through the
    /// real producers — `TransportObligationResult` -> the envelope's
    /// `runtime_checks` -> `transport_to_verification_result` — so the reader
    /// under test and the writer cannot drift apart on the payload shape.
    fn failed_with_stated_env(
        kind: &VcKind,
        function: &str,
        env: Option<RuntimeCheckEnv>,
    ) -> VerificationResult {
        let transport = trust_types::TransportObligationResult {
            assumes: Vec::new(),
            obligation_id: Some("obligation-1".to_string()),
            claim_digest_sha256: Some("c".repeat(64)),
            original_vc_snapshot: None,
            typed_kind: Some(Box::new(kind.clone())),
            kind: kind.transport_tag(),
            description: kind.description(),
            location: None,
            outcome: trust_types::Outcome::Failed,
            solver: "ay-in-process".to_string(),
            time_ms: 3,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            gap_class: None,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        };
        crate::types::transport_to_verification_result(function, &transport, env, None)
    }

    fn int64() -> Ty {
        Ty::Int { width: 64, signed: true }
    }

    /// `VerificationResult` has no `PartialEq`; the publication projection is
    /// compared by its exact serialized bytes, which is also the comparison the
    /// live transport authority makes.
    fn bytes(results: &[VerificationResult]) -> Vec<u8> {
        serde_json::to_vec(results).expect("rows serialize")
    }

    fn overflow_add() -> VcKind {
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (int64(), int64()) }
    }

    /// The policy `--test-target-panics=runtime-checked` resolves to in the
    /// ADVISORY / survey lane — the lane this flag actually exists for. Targo
    /// preserves the Cargo profile there and so cannot establish
    /// `-C overflow-checks`; the conservative environment is the result.
    fn advisory_policy() -> TestTargetPanicPolicy {
        TestTargetPanicChoice::RuntimeChecked.resolve(false)
    }

    /// The policy the same flag resolves to in the STRICT lane, where targo
    /// appends `-C overflow-checks=yes` to every compiled unit itself.
    fn strict_lane_policy() -> TestTargetPanicPolicy {
        TestTargetPanicChoice::RuntimeChecked.resolve(true)
    }

    /// The `assertion` row shape a direct `assert!`/`panic!` failure block
    /// raises, exactly as `v2_panic_call_vc_message` mints it.
    fn panic_call(callee: &str) -> VcKind {
        VcKind::Assertion { message: format!("panic call: {callee}") }
    }

    /// The whole-function interprocedural catch-all, verbatim.
    fn panic_freedom_catchall() -> VcKind {
        VcKind::Assertion {
            message: "panic freedom: no assertion, `unreachable!`, or panic is reachable"
                .to_string(),
        }
    }

    fn unbounded_allocation() -> VcKind {
        VcKind::UnboundedAllocation {
            callee: "vec::from_elem".to_string(),
            count: "num_atoms".to_string(),
            detail: "count is symbolic".to_string(),
        }
    }

    fn hardened_panic_boundary() -> VcKind {
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: "assert_not_sat".to_string(),
            detail: "MIR arithmetic assert can panic".to_string(),
        }
    }

    /// A hardened panic boundary raised over a CALL — the `unwrap`/`expect`/
    /// `std::fs` half of the family, which stands over no rustc-inserted check.
    fn hardened_call_boundary(callee: &str) -> VcKind {
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: callee.to_string(),
            detail: "hardened boundary over a call".to_string(),
        }
    }

    /// A hardened panic boundary raised over a rustc-inserted `Assert`, spelled
    /// exactly as `trust_vcgen::hardened` mints it: `mir_assert::{msg:?}`.
    fn hardened_mir_assert_boundary(message: &str) -> VcKind {
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: format!("mir_assert::{message}"),
            detail: "MIR assert can panic; hardened code needs a proved precondition".to_string(),
        }
    }

    /// The fixture rows must actually round-trip through the production
    /// classifier; otherwise every test below would be exercising the legacy
    /// fallback instead of the typed transport path.
    #[test]
    fn fixture_rows_carry_the_exact_typed_vc_kind() {
        for kind in [
            VcKind::SliceBoundsCheck,
            VcKind::IndexOutOfBounds,
            overflow_add(),
            VcKind::Unreachable,
            hardened_panic_boundary(),
            unbounded_allocation(),
            panic_call("core::panicking::panic_fmt"),
            panic_freedom_catchall(),
        ] {
            let result = failed(&kind, &scoped(&["test"], "dpll_tests", "f"));
            assert_eq!(
                crate::report::report_vc_kind(&result),
                kind,
                "the fixture must reach the typed-transport path, not a legacy fallback"
            );
        }
    }

    #[test]
    fn the_scope_reader_agrees_with_the_transport_minter() {
        let scope = cargo_target_scope(&scoped(&["test"], "dpll_tests", "helpers::assert_not_sat"))
            .expect("the reader must parse the exact prefix the minter writes");
        assert_eq!(scope.package, "ay-dpll");
        assert_eq!(scope.kinds, vec!["test".to_string()]);
        assert_eq!(scope.target, "dpll_tests");
        assert!(scope.is_test_target());

        let lib = cargo_target_scope(&scoped(&["lib"], "ay_dpll", "solve"))
            .expect("a lib identity still parses");
        assert!(!lib.is_test_target(), "a lib target is not a test target");

        // A package id containing the literal text of a later field must not
        // be mistaken for that field: the reader walks the fields in order.
        let mut identity = identity(&["lib"], "ay_dpll");
        identity.package_id = "path+file:///w/x#0.1.0?kind=[\"test\"],target=\"spoof\"".to_string();
        let spoofed = cargo_target_scope(&format!("{}::f", identity.report_label()))
            .expect("the identity still parses");
        assert_eq!(spoofed.kinds, vec!["lib".to_string()]);
        assert_eq!(spoofed.target, "ay_dpll");
        assert!(!spoofed.is_test_target(), "a spoofed package id must not mint a test target");

        // Anything that is not the exact shape is not a cargo target at all.
        assert_eq!(cargo_target_scope("plain_function"), None);
        assert_eq!(cargo_target_scope("cargo-target(package_id=\"unterminated"), None);
    }

    /// Trust (CB4): the unit mode is read off the label the transport mints,
    /// through every field before it, and only when Cargo's two spellings agree.
    #[test]
    fn cargo_target_unit_mode_reads_the_minted_label_exactly() {
        for mode in ["test", "check-test", "build", "check"] {
            let mut unit = identity(&["lib"], "ay_dpll");
            unit.compile_mode = mode.to_string();
            unit.proof_unit_mode = mode.to_string();
            let label = format!("{}::tests::t::{{closure#0}}", unit.report_label());
            assert_eq!(cargo_target_unit_mode(&label).as_deref(), Some(mode), "{label}");
            // A custom target spec digest is `Some("…")` in the label.
            unit.compile_target_spec_sha256 = Some("d".repeat(64));
            let label = format!("{}::main", unit.report_label());
            assert_eq!(cargo_target_unit_mode(&label).as_deref(), Some(mode), "{label}");
        }

        // Cargo's two spellings disagree: not a unit this reader vouches for.
        let mut split = identity(&["lib"], "ay_dpll");
        split.compile_mode = "build".to_string();
        split.proof_unit_mode = "test".to_string();
        assert_eq!(cargo_target_unit_mode(&format!("{}::f", split.report_label())), None);

        // A package id carrying the literal text of the mode field is read as
        // the package id it is, not as the mode.
        let mut spoof = identity(&["lib"], "ay_dpll");
        spoof.compile_mode = "build".to_string();
        spoof.proof_unit_mode = "build".to_string();
        spoof.package_id = "path+file:///w/x#0.1.0?proof_unit_mode=\"test\"".to_string();
        assert_eq!(
            cargo_target_unit_mode(&format!("{}::f", spoof.report_label())).as_deref(),
            Some("build")
        );

        // An unscoped (raw single-file) row has no unit, so no mode.
        assert_eq!(cargo_target_unit_mode("unit::main"), None);
        assert_eq!(cargo_target_unit_mode("cargo-target(package_id=\"unterminated"), None);
    }

    // (a) A refuted bounds / overflow row in a `["test"]` target is
    //     reclassified as runtime-checked — with a reason naming the flag and
    //     the target, and with no proof anywhere.
    //
    //     The policy beside each kind is the LANE the kind is eligible in. The
    //     bounds/remainder/panic-call families keep their check in every
    //     environment; the overflow family is eligible only where targo owns
    //     `-C overflow-checks`, which is the strict lane.
    #[test]
    fn a_refuted_panic_class_row_in_a_test_target_becomes_runtime_checked() {
        for (kind, policy) in [
            (VcKind::SliceBoundsCheck, advisory_policy()),
            (VcKind::IndexOutOfBounds, advisory_policy()),
            (VcKind::RemainderByZero, advisory_policy()),
            (panic_call("core::panicking::panic_fmt"), advisory_policy()),
            (panic_call("core::panicking::assert_failed::<u64, u64>"), advisory_policy()),
            (overflow_add(), strict_lane_policy()),
            (VcKind::NegationOverflow { ty: int64() }, strict_lane_policy()),
            (
                VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: int64(), shift_ty: int64() },
                strict_lane_policy(),
            ),
        ] {
            let mut results =
                vec![failed(&kind, &scoped(&["test"], "dpll_tests", "assert_not_sat"))];
            let reclassified = apply(&mut results, policy);

            assert_eq!(reclassified, 1, "{kind:?} is panic-class and must be reclassified");
            assert_eq!(results[0].outcome, VerificationOutcome::RuntimeChecked);
            assert_ne!(
                results[0].outcome,
                VerificationOutcome::Proved,
                "nothing may become PROVED"
            );
            let reason = results[0].reason.as_deref().expect("a reclassified row carries a reason");
            assert!(reason.starts_with(REASON_PREFIX), "the reason must name the flag: {reason}");
            assert!(reason.contains(FLAG), "the reason must name the flag: {reason}");
            assert!(
                reason.contains("target `dpll_tests`") && reason.contains("package `ay-dpll`"),
                "the reason must name the target: {reason}"
            );
            assert!(is_reclassified_row(&results[0]));

            // The row is still an honest record of what the solver said: its
            // kind, message and identity are untouched.
            assert_eq!(results[0].kind, kind.transport_tag());
            assert_eq!(results[0].message, kind.description());

            // It is counted, and counted in the runtime-checked bucket.
            let (counts, defects) = partition_outcome_counts(&results);
            assert!(
                defects.is_empty(),
                "a reclassified row is not a transport defect: {defects:?}"
            );
            assert_eq!(counts.runtime_checked, 1);
            assert_eq!(counts.failed, 0);
            assert_eq!(counts.proved, 0);
            assert_eq!(counts.total, 1);

            // And it is in the conditions ledger, with the same reason.
            let entry = ledger_entry(&results[0]).expect("a reclassified row enters the ledger");
            assert_eq!(entry.tag, LEDGER_TAG);
            assert_eq!(entry.subject, results[0].function);
            assert_eq!(entry.detail.as_str(), reason);

            // And it is printed.
            let lines = terminal_lines(&results);
            assert!(lines[0].contains(FLAG), "the disclosure must name the flag: {lines:?}");
            assert!(lines.iter().any(|line| line.contains("dpll_tests")), "{lines:?}");
        }
    }

    // (b) The SAME row in a non-test target is still refuted — for every
    //     non-test kind Cargo can produce, and for a lib the test merely calls.
    #[test]
    fn the_same_row_in_a_non_test_target_is_still_refuted() {
        for target_kind in ["lib", "bin", "example", "bench", "custom-build", "proc-macro"] {
            let mut results = vec![
                failed(&VcKind::SliceBoundsCheck, &scoped(&[target_kind], "ay_dpll", "solve")),
                failed(&overflow_add(), &scoped(&[target_kind], "ay_dpll", "solve")),
            ];
            let before = bytes(&results);
            let reclassified = apply(&mut results, strict_lane_policy());

            assert_eq!(reclassified, 0, "`{target_kind}` is not a test target");
            assert_eq!(bytes(&results), before, "a non-test row must not be touched at all");
            let (counts, _) = partition_outcome_counts(&results);
            assert_eq!(counts.failed, 2);
            assert_eq!(counts.runtime_checked, 0);
        }
    }

    // (c) Everything outside the eligible set is still refuted IN A TEST
    //     TARGET, under the WIDEST environment this flag can ever resolve to
    //     (the strict lane), so nothing here passes merely because the
    //     conservative environment hid it.
    #[test]
    fn excluded_kinds_in_a_test_target_are_still_refuted() {
        let excluded = [
            // Refused by BOTH layers: reaching an `Unreachable` is undefined
            // behaviour, not a panic.
            VcKind::Unreachable,
            // Refused by BOTH layers: unsafe-discipline findings, in all three
            // carriers `hardened_category` routes.
            VcKind::HardenedBoundary {
                category: HardenedVcCategory::UnsafeOperation,
                callee: "raw".to_string(),
                detail: "unsafe operation".to_string(),
            },
            VcKind::UnsafeOperation { desc: "ptr::read is unchecked".to_string() },
            VcKind::Assertion { message: "[unsafe:sep:double_free] freed twice".to_string() },
            // Refused by LAYER 1, the authority: the language emits no check
            // for either — that absence is exactly why they are obligations.
            // Both were on the hand-rolled list this replaced. The hardened row
            // here is a CALL boundary (`callee` is a call path, not a
            // `mir_assert::` marker), which is the half of the panic-boundary
            // family that stands over nothing rustc checks.
            unbounded_allocation(),
            hardened_panic_boundary(),
            hardened_call_boundary("std::option::Option::<T>::unwrap"),
            hardened_call_boundary("std::result::Result::<T, E>::expect"),
            // Refused by LAYER 1 because the marker is ANCHORED: a callee that
            // merely embeds it is a call path, not a rustc-inserted assert.
            hardened_call_boundary("wrapper::mir_assert::Overflow(Add)"),
            // Refused by LAYER 2 by name, in lock-step with `VcKind::
            // DivisionByZero` three entries below.
            hardened_mir_assert_boundary("DivisionByZero"),
            // Refused by LAYER 1: the unchecked-UB family's only guard is
            // `ub_checks`-gated, which targo never owns.
            VcKind::UncheckedIndexBounds {
                callee: "get_unchecked".to_string(),
                detail: "index must be < len".to_string(),
            },
            VcKind::UncheckedArithmeticOverflow { op: BinOp::Add, operand_tys: (int64(), int64()) },
            // Refused by LAYER 2: the whole-function interprocedural catch-all
            // ranges over `unreachable!` AND over callee bodies, so its
            // refutation is not evidence that a panic in THIS test target is
            // reachable.
            panic_freedom_catchall(),
            VcKind::Assertion { message: "panic freedom: ay_dpll::solve".to_string() },
            // Refused by LAYER 2: the eligibility test is ANCHORED, so a
            // contract-panic marker or an embedded mention does not match.
            VcKind::Assertion {
                message: "[trust-contract-panic] panic call: core::panicking::panic_fmt"
                    .to_string(),
            },
            VcKind::Assertion {
                message: "assertion: panic call: core::panicking::panic_fmt".to_string(),
            },
            // An `assertion` row that does not name a panic at all.
            VcKind::Assertion { message: "contract:global-alloc-dealloc-panic-free".to_string() },
            // Refused by LAYER 2: panic-class in fact, but not on the
            // authorized list, so it fails closed.
            VcKind::DivisionByZero,
            VcKind::Postcondition,
            VcKind::Precondition { callee: "f".to_string() },
            VcKind::CastOverflow { from_ty: int64(), to_ty: Ty::Int { width: 8, signed: false } },
        ];
        for kind in excluded {
            let mut results = vec![failed(&kind, &scoped(&["test"], "dpll_tests", "helper"))];
            let before = bytes(&results);
            let reclassified = apply(&mut results, strict_lane_policy());

            assert_eq!(reclassified, 0, "{kind:?} is outside the eligible set");
            assert_eq!(bytes(&results), before, "an out-of-scope row must not be touched at all");
            let (counts, _) = partition_outcome_counts(&results);
            assert_eq!(counts.runtime_checked, 0, "{kind:?} must not become a condition");
            assert_eq!(counts.proved, 0, "{kind:?} must not become a proof");
            // The row keeps whatever non-passing bucket it already had. That is
            // `failed` for all but the declared contract panic, which the gate
            // has always counted in its own `contract_panics` bucket.
            assert_eq!(
                counts.failed + counts.contract_panics,
                1,
                "{kind:?} must stay a refutation"
            );
        }
    }

    /// Only a REFUTED row moves. An unknown, a timeout, or a proved row in a
    /// test target is left exactly as the compiler reported it — the flag
    /// forgives a refutation, it does not relabel the report.
    #[test]
    fn only_refuted_rows_move() {
        for outcome in [
            VerificationOutcome::Unknown,
            VerificationOutcome::Timeout,
            VerificationOutcome::Proved,
            VerificationOutcome::RuntimeChecked,
        ] {
            let mut results = vec![row(
                &VcKind::SliceBoundsCheck,
                &scoped(&["test"], "dpll_tests", "helper"),
                outcome,
            )];
            let before = bytes(&results);
            assert_eq!(apply(&mut results, strict_lane_policy()), 0);
            assert_eq!(bytes(&results), before);
            assert!(!is_reclassified_row(&results[0]));
        }
    }

    // (d) The flag ABSENT reproduces today's verdict byte for byte.
    #[test]
    fn an_absent_flag_is_byte_identical_to_today() {
        let mut results = vec![
            failed(&VcKind::SliceBoundsCheck, &scoped(&["test"], "dpll_tests", "assert_not_sat")),
            failed(&overflow_add(), &scoped(&["test"], "dpll_tests", "assert_not_sat")),
            failed(&VcKind::Unreachable, &scoped(&["test"], "dpll_tests", "assert_not_sat")),
            failed(&VcKind::SliceBoundsCheck, &scoped(&["lib"], "ay_dpll", "solve")),
            row(
                &VcKind::IndexOutOfBounds,
                &scoped(&["test"], "dpll_tests", "ok"),
                VerificationOutcome::Proved,
            ),
        ];
        let before = bytes(&results);
        let before_counts = partition_outcome_counts(&results).0;

        // The default IS the absent flag.
        assert_eq!(TestTargetPanicPolicy::default(), TestTargetPanicPolicy::Strict);
        assert_eq!(apply(&mut results, TestTargetPanicPolicy::default()), 0);
        assert_eq!(apply(&mut results, TestTargetPanicPolicy::Strict), 0);

        assert_eq!(
            bytes(&results),
            before,
            "under the absent/strict policy the publication rows must be byte-identical"
        );
        assert_eq!(partition_outcome_counts(&results).0, before_counts);
        assert_eq!(before_counts.failed, 4);
        assert_eq!(before_counts.runtime_checked, 0);
        assert!(terminal_lines(&results).is_empty(), "a strict run adds no disclosure output");
        assert!(results.iter().all(|result| ledger_entry(result).is_none()));
    }

    // (e) The gate line and the exit code, in both directions.
    #[test]
    fn the_gate_flips_only_when_every_refutation_is_a_test_target_panic() {
        let test_target_rows = || {
            vec![
                failed(&VcKind::SliceBoundsCheck, &scoped(&["test"], "dpll_tests", "a")),
                failed(
                    &panic_call("core::panicking::panic_fmt"),
                    &scoped(&["test"], "dpll_tests", "b"),
                ),
                row(
                    &VcKind::IndexOutOfBounds,
                    &scoped(&["test"], "dpll_tests", "c"),
                    VerificationOutcome::Proved,
                ),
            ]
        };

        // Strict (== flag absent): FAIL, exit 1.
        let mut strict_rows = test_target_rows();
        assert_eq!(apply(&mut strict_rows, TestTargetPanicPolicy::Strict), 0);
        let strict_counts = partition_outcome_counts(&strict_rows).0;
        let strict_decision = evaluate_verification_gate(GateLane::Advisory, 0, strict_counts);
        assert_eq!(strict_decision, GateDecision::Fail);
        assert_eq!(strict_decision.as_str(), "fail");
        assert!(!strict_decision.is_success());

        // runtime-checked: every refutation reclassified -> conditional-pass, exit 0.
        let mut reclassified_rows = test_target_rows();
        assert_eq!(apply(&mut reclassified_rows, advisory_policy()), 2);
        let counts = partition_outcome_counts(&reclassified_rows).0;
        assert_eq!(counts.failed, 0);
        assert_eq!(counts.runtime_checked, 2);
        assert_eq!(counts.proved, 1);
        let decision = evaluate_verification_gate(GateLane::Advisory, 0, counts);
        assert_eq!(decision.as_str(), "conditional-pass");
        assert!(decision.is_success(), "a conditional pass exits 0");
        assert!(matches!(decision, GateDecision::ConditionalPass { runtime_checked: 2, .. }));

        // ONE non-test refutation left and the gate still FAILS.
        let mut mixed = test_target_rows();
        mixed.push(failed(&VcKind::SliceBoundsCheck, &scoped(&["lib"], "ay_dpll", "solve")));
        assert_eq!(apply(&mut mixed, advisory_policy()), 2);
        let mixed_counts = partition_outcome_counts(&mixed).0;
        assert_eq!(mixed_counts.failed, 1);
        assert_eq!(mixed_counts.runtime_checked, 2);
        let mixed_decision = evaluate_verification_gate(GateLane::Advisory, 0, mixed_counts);
        assert_eq!(mixed_decision, GateDecision::Fail);
        assert!(!mixed_decision.is_success());

        // An `unreachable` row left in a TEST target also keeps the gate failing.
        let mut with_unreachable = test_target_rows();
        with_unreachable.push(failed(&VcKind::Unreachable, &scoped(&["test"], "dpll_tests", "d")));
        assert_eq!(apply(&mut with_unreachable, advisory_policy()), 2);
        let unreachable_counts = partition_outcome_counts(&with_unreachable).0;
        assert_eq!(unreachable_counts.failed, 1);
        assert_eq!(
            evaluate_verification_gate(GateLane::Advisory, 0, unreachable_counts),
            GateDecision::Fail
        );
    }

    /// Render the Gate LINE the terminal prints for one outcome partition, so
    /// the assertion is on the literal text a reader sees rather than on an
    /// internal decision value.
    fn gate_line(
        lane: GateLane,
        compiler_exit: i32,
        counts: crate::pipeline::hardened::OutcomeCounts,
    ) -> String {
        let decision = evaluate_verification_gate(lane, compiler_exit, counts);
        let mut report = trust_report::build_json_report_with_policy(
            "cargo-targets[1]",
            &[],
            trust_types::RuntimeCheckPolicy::ForceStatic,
            false,
        );
        report.verification_gate = Some(trust_types::VerificationGateReport {
            lane: lane.as_str().to_string(),
            verification_level: Some("L0".to_string()),
            decision: decision.as_str().to_string(),
            exit_code: u8::from(!decision.is_success()),
            counts: trust_types::VerificationGateCounts {
                total: counts.total,
                proved: counts.proved,
                failed: counts.failed,
                unknown: counts.unknown,
                runtime_checked: counts.runtime_checked,
                assumed: counts.assumed,
                mandated: counts.mandated,
                contract_panics: counts.contract_panics,
                excluded: 0,
            },
            conditional_on_assumption_rows: counts.assumed > 0,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: counts.runtime_checked > 0,
            conditional_on_unknown_rows: matches!(
                decision,
                GateDecision::ConditionalPass { unknown, .. } if unknown > 0
            ),
            conditional_on_visitation_entries: false,
            coverage: None,
            test_execution: None,
            exclusions: Vec::new(),
            determinism: None,
            failure_sites: None,
            project_requirements: None,
        });
        trust_report::format_json_summary(&report)
            .lines()
            .find(|line| line.trim_start().starts_with("Gate: "))
            .expect("the summary renders a Gate line")
            .to_string()
    }

    /// The literal Gate line, in both directions, on the SAME rows.
    #[test]
    fn the_gate_line_shows_the_reclassified_count_and_the_exit_code() {
        let rows = || {
            vec![
                failed(&VcKind::SliceBoundsCheck, &scoped(&["test"], "dpll_tests", "a")),
                failed(
                    &panic_call("core::panicking::panic_fmt"),
                    &scoped(&["test"], "dpll_tests", "b"),
                ),
                row(
                    &VcKind::IndexOutOfBounds,
                    &scoped(&["test"], "dpll_tests", "c"),
                    VerificationOutcome::Proved,
                ),
            ]
        };

        let mut strict_rows = rows();
        apply(&mut strict_rows, TestTargetPanicPolicy::Strict);
        assert_eq!(
            gate_line(GateLane::Advisory, 0, partition_outcome_counts(&strict_rows).0),
            "  Gate: FAIL [advisory lane, exit 1] (1 proved, 2 failed, 0 runtime-checked, \
             0 assumed, 0 mandated, 0 contract-panic, 0 unknown / 3 total)"
        );

        let mut reclassified_rows = rows();
        apply(&mut reclassified_rows, advisory_policy());
        assert_eq!(
            gate_line(GateLane::Advisory, 0, partition_outcome_counts(&reclassified_rows).0),
            "  Gate: CONDITIONAL-PASS [advisory lane, exit 0] (1 proved, 0 failed, \
             2 runtime-checked, 0 assumed, 0 mandated, 0 contract-panic, 0 unknown / 3 total)"
        );
    }

    /// The release gate is untouched: a reclassified row is runtime-checked,
    /// and `--certify` folds every runtime-checked row into a nonzero exit.
    #[test]
    fn the_certify_lane_still_refuses_a_reclassified_row() {
        let mut results =
            vec![failed(&VcKind::SliceBoundsCheck, &scoped(&["test"], "dpll_tests", "a"))];
        assert_eq!(apply(&mut results, advisory_policy()), 1);
        let counts = partition_outcome_counts(&results).0;
        assert_eq!(
            evaluate_verification_gate(GateLane::Certify, 0, counts),
            GateDecision::Inconclusive,
            "--certify must never pass on a reclassified row"
        );
        assert_eq!(
            evaluate_verification_gate(GateLane::MemorySafe, 0, counts),
            GateDecision::Inconclusive,
        );
    }

    /// A nonzero compiler exit still fails, reclassification or not.
    #[test]
    fn a_nonzero_compiler_exit_still_fails() {
        let mut results =
            vec![failed(&VcKind::SliceBoundsCheck, &scoped(&["test"], "dpll_tests", "a"))];
        assert_eq!(apply(&mut results, advisory_policy()), 1);
        let counts = partition_outcome_counts(&results).0;
        assert_eq!(evaluate_verification_gate(GateLane::Advisory, 101, counts), GateDecision::Fail);
    }

    /// THE STRUCTURAL INVARIANT, and the reason this module was rewritten:
    /// `VcKind::site_retains_language_check_in` is the GATE. No obligation this
    /// flag reclassifies may be one that predicate declines, in either lane.
    ///
    /// The same loop pins the CONVERSE for the hardened family: every hardened
    /// row this flag admits is one `has_runtime_fallback_in` still DECLINES. That
    /// is the separation a reviewer's probe caught collapsing — the flag gets its
    /// answer without the tree's report labelling moving with it.
    #[test]
    fn nothing_is_eligible_that_the_authority_predicate_declines() {
        let every_kind_we_reason_about = [
            VcKind::SliceBoundsCheck,
            VcKind::IndexOutOfBounds,
            VcKind::RemainderByZero,
            VcKind::DivisionByZero,
            overflow_add(),
            VcKind::NegationOverflow { ty: int64() },
            VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: int64(), shift_ty: int64() },
            VcKind::UncheckedIndexBounds {
                callee: "get_unchecked".to_string(),
                detail: "index must be < len".to_string(),
            },
            VcKind::UncheckedArithmeticOverflow { op: BinOp::Add, operand_tys: (int64(), int64()) },
            unbounded_allocation(),
            hardened_panic_boundary(),
            VcKind::HardenedBoundary {
                category: HardenedVcCategory::UnsafeOperation,
                callee: "raw".to_string(),
                detail: "unsafe operation".to_string(),
            },
            VcKind::UnsafeOperation { desc: "ptr::read is unchecked".to_string() },
            VcKind::Unreachable,
            panic_call("core::panicking::panic_fmt"),
            panic_freedom_catchall(),
            VcKind::Assertion { message: "[unsafe:sep:double_free] freed twice".to_string() },
            VcKind::UnsupportedMir {
                kind: "FullVerification::Assertion".to_string(),
                detail: "assertion: panic call: core::panicking::panic_fmt".to_string(),
            },
            VcKind::Postcondition,
            VcKind::Precondition { callee: "f".to_string() },
            VcKind::CastOverflow { from_ty: int64(), to_ty: Ty::Int { width: 8, signed: false } },
            VcKind::DoubleFree,
            VcKind::UseAfterFree,
        ];
        for env in [
            RuntimeCheckEnv::new(false, false),
            RuntimeCheckEnv::new(true, false),
            RuntimeCheckEnv::new(false, true),
            RuntimeCheckEnv::new(true, true),
        ] {
            for kind in &every_kind_we_reason_about {
                if is_reclassifiable_obligation(kind, env) {
                    assert!(
                        kind.site_retains_language_check_in(env),
                        "{kind:?} was reclassified in {env:?} though the AUTHORITY says the \
                         generated program keeps no runtime check at its site"
                    );
                    if matches!(kind, VcKind::HardenedBoundary { .. }) {
                        assert!(
                            !kind.has_runtime_fallback_in(env),
                            "{kind:?} must stay UNDISCHARGED for every other consumer: this \
                             flag reads the site question, not the discharge question"
                        );
                    }
                }
            }
        }
    }

    /// The hand-rolled list this replaced admitted two obligations the
    /// authority declines. Both are now refused, and this test names them so a
    /// future edit cannot quietly put them back.
    #[test]
    fn the_two_kinds_the_authority_declines_are_no_longer_eligible() {
        for kind in [unbounded_allocation(), hardened_panic_boundary()] {
            for env in [RuntimeCheckEnv::new(false, false), RuntimeCheckEnv::new(true, true)] {
                assert!(
                    !kind.site_retains_language_check_in(env),
                    "the authority must still decline {kind:?}"
                );
                assert!(!kind.has_runtime_fallback_in(env));
                assert!(
                    !is_reclassifiable_obligation(&kind, env),
                    "{kind:?} must not be eligible in {env:?}"
                );
            }
        }

        // And at row level, in a test target, under the widest policy.
        for kind in [unbounded_allocation(), hardened_panic_boundary()] {
            let mut results =
                vec![failed(&kind, &scoped(&["test"], "dpll_tests", "assert_certified_unsat"))];
            let before = bytes(&results);
            assert_eq!(apply(&mut results, strict_lane_policy()), 0, "{kind:?}");
            assert_eq!(bytes(&results), before);
        }
    }

    /// The overflow family is a positive claim about `-C overflow-checks`, so
    /// it is eligible in exactly the lane where targo owns that option.
    #[test]
    fn the_overflow_family_is_eligible_only_where_targo_owns_overflow_checks() {
        let overflow_kinds = [
            overflow_add(),
            VcKind::NegationOverflow { ty: int64() },
            VcKind::ShiftOverflow { op: BinOp::Shr, operand_ty: int64(), shift_ty: int64() },
        ];
        for kind in &overflow_kinds {
            assert!(
                !is_reclassifiable_obligation(kind, RuntimeCheckEnv::new(false, false)),
                "{kind:?} must not be claimed where the overflow check was not established"
            );
            assert!(
                is_reclassifiable_obligation(kind, RuntimeCheckEnv::new(true, false)),
                "{kind:?} is eligible once the overflow check is established"
            );
        }

        // The lane derivation itself, and the two environments it produces.
        assert_eq!(
            TestTargetPanicChoice::RuntimeChecked.resolve(false),
            TestTargetPanicPolicy::RuntimeChecked { lane_env: RuntimeCheckEnv::new(false, false) },
            "the advisory/survey lane preserves the Cargo profile, so it claims nothing"
        );
        assert_eq!(
            TestTargetPanicChoice::RuntimeChecked.resolve(true),
            TestTargetPanicPolicy::RuntimeChecked { lane_env: RuntimeCheckEnv::new(true, false) },
            "the strict lane appends `-C overflow-checks=yes` itself"
        );
        // `ub_checks` is never claimed: targo does not own `-Z ub-checks`.
        for strict in [false, true] {
            assert!(!lane_inferred_check_env(strict).ub_checks);
        }

        // Same rows, same target, both lanes — end to end.
        let rows = || {
            overflow_kinds
                .iter()
                .map(|kind| failed(kind, &scoped(&["test"], "dpll_tests", "overflows")))
                .collect::<Vec<_>>()
        };
        let mut advisory = rows();
        let before = bytes(&advisory);
        assert_eq!(apply(&mut advisory, advisory_policy()), 0);
        assert_eq!(bytes(&advisory), before, "the advisory lane must not touch them at all");

        let mut strict = rows();
        assert_eq!(apply(&mut strict, strict_lane_policy()), 3);
    }

    /// THE POINT OF THE ROW-CARRIED ENVIRONMENT. In the ADVISORY lane targo
    /// appends no codegen options and cannot establish `-C overflow-checks`, so
    /// it used to decline the whole overflow family. But the compiler that built
    /// the unit knows exactly — `targo trust check --allow-l0-gaps` resolves
    /// Cargo's `dev` profile, whose `overflow-checks` DEFAULTS TO TRUE, so the
    /// check is emitted and declining it was counterfactual. A row that carries
    /// the compiler's own answer is decided on THAT, not on the lane.
    #[test]
    fn a_compiler_stated_overflow_checks_beats_the_advisory_lane_inference() {
        let kind = overflow_add();
        let function = scoped(&["test"], "dpll_tests", "overflows");

        // Same lane, same target, same obligation: only the row's statement moves.
        let mut stated_on =
            vec![failed_with_stated_env(&kind, &function, Some(RuntimeCheckEnv::new(true, false)))];
        assert_eq!(
            apply(&mut stated_on, advisory_policy()),
            1,
            "the compiler said the overflow check is emitted; the advisory lane must believe it"
        );
        assert_eq!(stated_on[0].outcome, VerificationOutcome::RuntimeChecked);
        let reason = stated_on[0].reason.as_deref().expect("a reclassified row carries a reason");
        assert!(
            reason.contains("COMPILER'S OWN") && reason.contains("overflow_checks=true"),
            "the reason must disclose whose environment decided it: {reason}"
        );

        // And the same row carrying the OTHER value is still declined, in the
        // very same lane: the field is read, not assumed.
        let mut stated_off = vec![failed_with_stated_env(
            &kind,
            &function,
            Some(RuntimeCheckEnv::new(false, false)),
        )];
        let before = bytes(&stated_off);
        assert_eq!(apply(&mut stated_off, advisory_policy()), 0);
        assert_eq!(bytes(&stated_off), before);
    }

    /// ABSENCE IS NEVER READ AS TRUE. A row that states nothing — an older
    /// compiler, a producer that does not mint the field, a row with no
    /// structured evidence at all — keeps EXACTLY today's conservative
    /// behaviour: the lane inference, and nothing else.
    #[test]
    fn a_row_that_states_no_environment_keeps_the_conservative_lane_behaviour() {
        let kind = overflow_add();
        let function = scoped(&["test"], "dpll_tests", "overflows");

        for mut absent in [
            // No `runtime_checks` on the envelope.
            vec![failed_with_stated_env(&kind, &function, None)],
            // No structured transport evidence on the row at all.
            vec![failed(&kind, &function)],
            // Structured evidence present but the payload is unreadable.
            vec![{
                let mut row = failed(&kind, &function);
                row.raw_line = "targo-trust-structured-transport-evidence:{not json".to_string();
                row
            }],
        ] {
            assert_eq!(
                crate::types::transport_runtime_check_env(&absent[0]),
                None,
                "this row must carry no measurement"
            );
            let before = bytes(&absent);
            assert_eq!(
                apply(&mut absent, advisory_policy()),
                0,
                "absence must never be read as `checks are on`"
            );
            assert_eq!(bytes(&absent), before, "and the row must be untouched");
        }
    }

    /// The other direction, and it moves toward FEWER claims: a unit the
    /// compiler says was built WITHOUT the overflow check is declined even in
    /// the strict lane, where targo appends `-C overflow-checks=yes` itself. The
    /// generated program is what it is regardless of what targo appended, so the
    /// measurement wins there too.
    #[test]
    fn a_compiler_stated_checks_off_is_declined_even_in_the_strict_lane() {
        let kind = overflow_add();
        let function = scoped(&["test"], "dpll_tests", "overflows");

        let mut stated_off = vec![failed_with_stated_env(
            &kind,
            &function,
            Some(RuntimeCheckEnv::new(false, false)),
        )];
        let before = bytes(&stated_off);
        assert_eq!(apply(&mut stated_off, strict_lane_policy()), 0);
        assert_eq!(bytes(&stated_off), before);

        // The lane's own inference still applies to a row that states nothing.
        let mut silent = vec![failed_with_stated_env(&kind, &function, None)];
        assert_eq!(apply(&mut silent, strict_lane_policy()), 1);
    }

    /// The row-carried environment decides ONLY the families
    /// `has_runtime_fallback_in` answers from the environment. It can neither
    /// widen the policy layer nor reach outside a `["test"]` target: a stated
    /// `RuntimeCheckEnv::new(true, true)` — the most permissive environment that
    /// exists — still reclassifies nothing that layer 2 refuses, and nothing in
    /// a lib target.
    #[test]
    fn a_stated_environment_cannot_widen_the_policy_or_the_target_scope() {
        let widest = Some(RuntimeCheckEnv::new(true, true));
        for kind in [
            VcKind::Unreachable,
            VcKind::DivisionByZero,
            unbounded_allocation(),
            hardened_panic_boundary(),
            panic_freedom_catchall(),
        ] {
            let mut rows =
                vec![failed_with_stated_env(&kind, &scoped(&["test"], "dpll_tests", "t"), widest)];
            let before = bytes(&rows);
            assert_eq!(apply(&mut rows, advisory_policy()), 0, "{kind:?}");
            assert_eq!(bytes(&rows), before, "{kind:?}");
        }

        let mut lib_rows = vec![failed_with_stated_env(
            &overflow_add(),
            &scoped(&["lib"], "ay_dpll", "solve"),
            widest,
        )];
        let before = bytes(&lib_rows);
        assert_eq!(apply(&mut lib_rows, advisory_policy()), 0);
        assert_eq!(bytes(&lib_rows), before);
    }

    /// The environment travels on the row's AUTHENTICATED structured transport
    /// evidence — the payload `live_transport_row_receipt` digests — and not in
    /// a side channel. Two consequences are checked here: it survives the exact
    /// serialization the receipt covers, and an absent statement adds not one
    /// byte to the row, so a producer that does not mint it leaves the row
    /// byte-identical to today.
    #[test]
    fn the_stated_environment_rides_on_the_authenticated_row_and_absence_adds_no_bytes() {
        let kind = overflow_add();
        let function = scoped(&["test"], "dpll_tests", "overflows");

        let stated =
            failed_with_stated_env(&kind, &function, Some(RuntimeCheckEnv::new(true, false)));
        assert!(
            stated.raw_line.contains("runtime_checks"),
            "the value must be inside the row payload the receipt digests: {}",
            stated.raw_line
        );
        let round_tripped: VerificationResult =
            serde_json::from_slice(&serde_json::to_vec(&stated).expect("row serializes"))
                .expect("row round-trips");
        assert_eq!(
            crate::types::transport_runtime_check_env(&round_tripped),
            Some(RuntimeCheckEnv::new(true, false))
        );

        let absent = failed_with_stated_env(&kind, &function, None);
        assert!(!absent.raw_line.contains("runtime_checks"));
        let mut legacy = failed_with_stated_env(&kind, &function, None);
        legacy.raw_line = absent.raw_line.clone();
        assert_eq!(bytes(&[absent]), bytes(&[legacy]));
    }

    /// The assertion family: a direct `panic call: ` row is eligible, and the
    /// whole-function `panic freedom:` catch-all — which ranges over
    /// `unreachable!` and over callee bodies — is not.
    #[test]
    fn only_a_direct_panic_call_assertion_is_eligible() {
        let env = RuntimeCheckEnv::new(false, false);

        for callee in [
            "core::panicking::panic_fmt",
            "core::panicking::panic",
            "core::panicking::assert_failed::<u64, u64>",
            "std::rt::begin_panic",
        ] {
            assert!(
                is_reclassifiable_obligation(&panic_call(callee), env),
                "`panic call: {callee}` is a direct panic call in this function's body"
            );
        }

        for message in [
            "panic freedom: no assertion, `unreachable!`, or panic is reachable",
            "panic freedom: ay_dpll::solve",
            "[trust-contract-panic] panic call: core::panicking::panic_fmt",
            "assertion: panic call: core::panicking::panic_fmt",
            "panic call:",
            " panic call: core::panicking::panic_fmt",
            "the panic freedom: and panic call: words appear here",
            "[unsafe:sep:double_free] freed twice",
            "contract:global-alloc-dealloc-panic-free",
        ] {
            let kind = VcKind::Assertion { message: message.to_string() };
            assert!(!is_reclassifiable_obligation(&kind, env), "`{message}` must not be eligible");
        }

        // The authority ALLOWS the catch-all (every `Assertion` that is not a
        // separation-engine unsafe row answers `true`); it is LAYER 2 that
        // refuses it. Pinning that keeps the two layers honestly separate.
        assert!(
            panic_freedom_catchall().site_retains_language_check_in(env),
            "the authority does answer `true` for the catch-all — layer 2 is what refuses it"
        );

        // And at row level, in a test target, under the widest policy.
        let mut results = vec![failed(
            &panic_freedom_catchall(),
            &scoped(&["test"], "dpll_tests", "solve_wrapper"),
        )];
        let before = bytes(&results);
        assert_eq!(apply(&mut results, strict_lane_policy()), 0);
        assert_eq!(bytes(&results), before);
        let (counts, _) = partition_outcome_counts(&results);
        assert_eq!(counts.failed, 1, "a `panic freedom:` row keeps its refutation");
    }

    /// The resolved policy is built from the LANE, once, in `cli.rs`, so no
    /// caller can apply the reclassification against an environment nobody
    /// established.
    #[test]
    fn the_cli_binds_the_policy_to_the_lane() {
        let advisory = crate::cli::parse_subcommand_args(&[
            "--allow-l0-gaps".to_string(),
            "--test-target-panics=runtime-checked".to_string(),
        ])
        .expect("parses");
        assert_eq!(advisory.test_target_panics, TestTargetPanicChoice::RuntimeChecked);
        assert!(!advisory.strict_artifact_policy());
        assert_eq!(
            advisory.test_target_panic_policy(),
            TestTargetPanicPolicy::RuntimeChecked { lane_env: RuntimeCheckEnv::new(false, false) }
        );

        let strict =
            crate::cli::parse_subcommand_args(
                &["--test-target-panics=runtime-checked".to_string()],
            )
            .expect("parses");
        assert!(strict.strict_artifact_policy());
        assert_eq!(
            strict.test_target_panic_policy(),
            TestTargetPanicPolicy::RuntimeChecked { lane_env: RuntimeCheckEnv::new(true, false) }
        );

        // An absent flag resolves to `Strict` in EVERY lane, and `Strict`
        // carries no environment because it makes no claim.
        for args in [vec!["--allow-l0-gaps".to_string()], vec![], vec!["--survey".to_string()]] {
            let parsed = crate::cli::parse_subcommand_args(&args).expect("parses");
            assert_eq!(parsed.test_target_panic_policy(), TestTargetPanicPolicy::Strict);
        }
    }

    #[test]
    fn the_flag_value_is_explicit_and_has_no_inferred_fallback() {
        assert_eq!(
            TestTargetPanicChoice::parse(STRICT_VALUE).expect("strict parses"),
            TestTargetPanicChoice::Strict
        );
        assert_eq!(
            TestTargetPanicChoice::parse(RUNTIME_CHECKED_VALUE).expect("runtime-checked parses"),
            TestTargetPanicChoice::RuntimeChecked
        );
        for bad in ["", "true", "runtime_checked", "yes", "RUNTIME-CHECKED", "off"] {
            let error = TestTargetPanicChoice::parse(bad)
                .expect_err("an unrecognized value must be an error, never a silent fallback");
            assert!(error.to_string().contains(FLAG), "{error}");
        }
    }

    #[test]
    fn the_help_text_says_what_it_does_and_what_it_does_not_do() {
        let help = help_lines().join("\n");
        assert!(help.contains(FLAG));
        assert!(help.contains("DOES apply to"));
        assert!(help.contains("DOES NOT apply to"));
        for named in [
            "slice_bounds_check",
            "index_out_of_bounds",
            "arithmetic_overflow_*",
            "negation_overflow",
            "shift_overflow_*",
            "remainder_by_zero",
            "hardened_panic_boundary",
            "unbounded_allocation",
            "unreachable",
            "hardened_unsafe_operation",
            "panic freedom:",
            "panic call: ",
            "site_retains_language_check_in",
            "-C overflow-checks",
            "--allow-l0-gaps",
        ] {
            assert!(help.contains(named), "the help must name `{named}`");
        }
        // The two the old list wrongly admitted are named in the REFUSAL half.
        let refusals = help.split("DOES NOT apply to").nth(1).expect("the help refuses things");
        for refused in [
            "unbounded_allocation",
            "hardened_panic_boundary",
            "panic freedom:",
            // The family is SPLIT, so the help must say which half it refuses
            // rather than leaving a reader to infer the whole family is refused.
            "mir_assert::DivisionByZero",
        ] {
            assert!(refusals.contains(refused), "`{refused}` must be listed as refused");
        }
        // ...and the admitted half must be named in the POSITIVE section, or the
        // help would deny a reclassification the flag actually performs.
        let applies =
            help.split("DOES NOT apply to").next().expect("the help lists what it applies to");
        for admitted in ["mir_assert::BoundsCheck", "mir_assert::Overflow*"] {
            assert!(applies.contains(admitted), "`{admitted}` must be listed as admitted");
        }
        assert!(help.contains("No default"), "the help must say the flag has no default");
        assert!(help.contains("environment"), "the help must say there is no env var");
        assert!(help.contains("--certify"), "the help must say the release gate is unaffected");
    }

    #[test]
    fn the_cli_parses_both_spellings_and_defaults_to_strict() {
        let absent =
            crate::cli::parse_subcommand_args(&["--allow-l0-gaps".to_string()]).expect("parses");
        assert_eq!(absent.test_target_panics, TestTargetPanicChoice::Strict);

        for args in [
            vec!["--test-target-panics=runtime-checked".to_string()],
            vec!["--test-target-panics".to_string(), "runtime-checked".to_string()],
        ] {
            let parsed = crate::cli::parse_subcommand_args(&args).expect("parses");
            assert_eq!(parsed.test_target_panics, TestTargetPanicChoice::RuntimeChecked);
            assert!(
                parsed.passthrough.is_empty(),
                "the flag is consumed by targo, never forwarded to Cargo: {:?}",
                parsed.passthrough
            );
        }

        let explicit_strict =
            crate::cli::parse_subcommand_args(&["--test-target-panics=strict".to_string()])
                .expect("parses");
        assert_eq!(explicit_strict.test_target_panics, TestTargetPanicChoice::Strict);

        crate::cli::parse_subcommand_args(&["--test-target-panics=maybe".to_string()])
            .expect_err("an unrecognized value is refused at parse time");
    }

    /// THE POSITIVE HALF OF THIS CHANGE. A refuted hardened panic boundary over
    /// a rustc-inserted assert, in a cargo `["test"]` target, is reclassified as
    /// a runtime-checked CONDITION — and only in the environment where layer 1's
    /// authority says the guard is there.
    ///
    /// These are the ~517 `hardened_panic_boundary` rows ay 0.27.0's gate could
    /// not publish: the hardening profile demands a STATIC proof that the panic
    /// is unreachable, but the profile does not touch codegen (MEASURED
    /// 2026-09-18: byte-identical LLVM IR with and without
    /// `-Ztrust-verify-profile=unix_hardened`), so the `Assert` rustc emitted is
    /// still executing in the test binary.
    #[test]
    fn hardened_mir_assert_boundaries_in_a_test_target_are_reclassified() {
        // Unconditional guards: reclassified in EITHER environment.
        for message in ["BoundsCheck", "RemainderByZero"] {
            for policy in [advisory_policy(), strict_lane_policy()] {
                let mut results = vec![failed(
                    &hardened_mir_assert_boundary(message),
                    &scoped(&["test"], "dpll_tests", "f"),
                )];
                assert_eq!(apply(&mut results, policy), 1, "mir_assert::{message} in {policy:?}");
                assert!(matches!(results[0].outcome, VerificationOutcome::RuntimeChecked));
                assert!(is_reclassified_row(&results[0]));
                assert!(ledger_entry(&results[0]).is_some(), "it must reach the conditions ledger");
            }
        }
        // Overflow guards: reclassified ONLY where `-C overflow-checks` is
        // established, which is the strict lane. This is layer 1 answering, not
        // a second opinion held here.
        for message in
            ["Overflow(Add)", "Overflow(Sub)", "Overflow(Mul)", "Overflow(Shl)", "OverflowNeg"]
        {
            let mut strict = vec![failed(
                &hardened_mir_assert_boundary(message),
                &scoped(&["test"], "dpll_tests", "f"),
            )];
            assert_eq!(apply(&mut strict, strict_lane_policy()), 1, "mir_assert::{message}");

            let mut advisory = vec![failed(
                &hardened_mir_assert_boundary(message),
                &scoped(&["test"], "dpll_tests", "f"),
            )];
            let before = bytes(&advisory);
            assert_eq!(apply(&mut advisory, advisory_policy()), 0, "mir_assert::{message}");
            assert_eq!(bytes(&advisory), before, "the conservative lane touches nothing");
        }
    }

    /// The same hardened boundary in a NON-test target keeps its refutation.
    /// Target scoping is the whole premise of this flag and the hardened
    /// subfamily does not get an exemption from it.
    #[test]
    fn a_hardened_mir_assert_boundary_outside_a_test_target_is_still_refuted() {
        for kinds in [&["lib"][..], &["bin"][..], &["bench"][..], &["lib", "test"][..]] {
            let mut results = vec![failed(
                &hardened_mir_assert_boundary("Overflow(Add)"),
                &scoped(kinds, "ay-dpll", "solve"),
            )];
            let before = bytes(&results);
            assert_eq!(apply(&mut results, strict_lane_policy()), 0, "{kinds:?}");
            assert_eq!(bytes(&results), before, "a non-test row must not be touched at all");
        }
    }

    /// LAYER 2 CAN ONLY SHRINK LAYER 1. Pinned as an implication over the whole
    /// recognized marker set, so a family added to the authority cannot quietly
    /// widen what this flag forgives, and a family removed from the authority
    /// cannot leave a stale allowance behind.
    #[test]
    fn the_hardened_policy_list_is_a_strict_subset_of_the_authority() {
        let markers = [
            "BoundsCheck",
            "DivisionByZero",
            "RemainderByZero",
            "OverflowNeg",
            "Overflow(Add)",
            "Overflow(Sub)",
            "Overflow(Mul)",
            "Overflow(Div)",
            "Overflow(Rem)",
            "Overflow(Shl)",
            "Overflow(Shr)",
            "NullPointerDereference",
            "MisalignedPointerDereference",
            "InvalidEnumConstruction",
            "ResumedAfterReturn",
            "Custom(\"anything\")",
        ];
        let strict_env = RuntimeCheckEnv::new(true, true);
        for message in markers {
            let kind = hardened_mir_assert_boundary(message);
            let authority = kind.site_retains_language_check_in(strict_env);
            let policy = policy_admits_panic_class(&kind);
            assert!(
                !policy || authority,
                "layer 2 admitted `mir_assert::{message}` that layer 1 declines"
            );
            // And no marker, admitted or not, may ever claim a DISCHARGE.
            assert!(
                !kind.has_runtime_fallback_in(strict_env),
                "`mir_assert::{message}` must not read as covered to any other consumer"
            );
            // The ONE deliberate policy subtraction, stated as a fact rather
            // than left implicit: division by zero has a guard and is still
            // refused, exactly as `VcKind::DivisionByZero` is.
            if message == "DivisionByZero" {
                assert!(authority, "the zero-divisor assert is unconditional");
                assert!(!policy, "but this flag was never authorized over it");
            }
        }
    }

    /// Every hardened CATEGORY other than `PanicBoundary` is refused whatever
    /// its callee looks like, so a mis-categorized row cannot borrow the panic
    /// boundary's allowance.
    #[test]
    fn non_panic_hardened_categories_are_refused_even_over_an_assert() {
        for category in [
            HardenedVcCategory::UnsafeOperation,
            HardenedVcCategory::FfiBoundary,
            HardenedVcCategory::RawPathApi,
            HardenedVcCategory::ByteLoss,
            HardenedVcCategory::ErrorDiscard,
            HardenedVcCategory::TrustDomain,
            HardenedVcCategory::ProcessSemantics,
        ] {
            let kind = VcKind::HardenedBoundary {
                category,
                callee: "mir_assert::Overflow(Add)".to_string(),
                detail: "mis-categorized".to_string(),
            };
            assert!(!policy_admits_panic_class(&kind), "{category:?}");
            let mut results = vec![failed(&kind, &scoped(&["test"], "dpll_tests", "f"))];
            let before = bytes(&results);
            assert_eq!(apply(&mut results, strict_lane_policy()), 0, "{category:?}");
            assert_eq!(bytes(&results), before);
        }
    }

    /// THE COMPILER'S OWN ROWS, VERBATIM. Captured 2026-09-18 from
    /// `trustc -C overflow-checks=yes -Ztrust-policy=advisory
    /// -Ztrust-verify-profile=unix_hardened -Ztrust-verify-output=json` over a
    /// three-function fixture — an `a + b`, a `v[i]`, and an `Option::unwrap` —
    /// so the marker this module keys on is the marker the producer actually
    /// writes, not a spelling invented in a test. `serde` deserializing these
    /// into `VcKind` is itself the wire-shape assertion.
    const COMPILER_OVERFLOW_ADD_BOUNDARY: &str = r#"{"HardenedBoundary":{
        "category":"panic_boundary","callee":"mir_assert::Overflow(Add)",
        "detail":"MIR arithmetic assert can panic; hardened code needs proven arithmetic preconditions"}}"#;
    const COMPILER_BOUNDS_BOUNDARY: &str = r#"{"HardenedBoundary":{
        "category":"panic_boundary","callee":"mir_assert::BoundsCheck",
        "detail":"MIR bounds-check assert can panic; hardened code needs a proven index precondition"}}"#;
    const COMPILER_UNWRAP_BOUNDARY: &str = r#"{"HardenedBoundary":{
        "category":"panic_boundary","callee":"core::option::Option::<i32>::unwrap",
        "detail":"unwrap is a denial-of-service path unless the success precondition is proven"}}"#;

    fn compiler_row_kind(json: &str) -> VcKind {
        serde_json::from_str(json).expect("the compiler's own typed payload must deserialize")
    }

    /// END-TO-END ON THE PRODUCER'S BYTES: over a CHECKED operation the boundary
    /// is reclassified, over an UNCHECKED one it is not. This is the measurement
    /// the whole change rests on, run against the exact rows `trustc` emits.
    #[test]
    fn the_compilers_own_hardened_rows_split_on_whether_rustc_checks_the_operation() {
        // CHECKED: rustc emits `llvm.sadd.with.overflow` + `panic_const_add_overflow`
        // and `panic_bounds_check`, and enabling the hardening profile leaves the
        // IR byte-identical, so the guard is demonstrably still executing.
        for json in [COMPILER_OVERFLOW_ADD_BOUNDARY, COMPILER_BOUNDS_BOUNDARY] {
            let kind = compiler_row_kind(json);
            assert!(
                kind.site_retains_language_check_in(RuntimeCheckEnv::new(true, false)),
                "layer 1 must see the guard: {kind:?}"
            );
            assert!(
                !kind.has_runtime_fallback_in(RuntimeCheckEnv::new(true, false)),
                "seeing the guard is not discharging the boundary: {kind:?}"
            );
            let mut results = vec![failed(&kind, &scoped(&["test"], "dpll_tests", "f"))];
            assert_eq!(apply(&mut results, strict_lane_policy()), 1, "{kind:?}");
            assert!(matches!(results[0].outcome, VerificationOutcome::RuntimeChecked));
            assert!(is_reclassified_row(&results[0]));
        }
        // UNCHECKED: `Option::unwrap` panics inside the CALLEE. rustc inserts
        // nothing at this site, so nothing here may be called covered — in a test
        // target or anywhere else.
        let kind = compiler_row_kind(COMPILER_UNWRAP_BOUNDARY);
        for env in [RuntimeCheckEnv::new(true, true), RuntimeCheckEnv::new(false, false)] {
            assert!(!kind.site_retains_language_check_in(env), "an unwrap boundary has no guard");
            assert!(!kind.has_runtime_fallback_in(env));
        }
        let mut results = vec![failed(&kind, &scoped(&["test"], "dpll_tests", "f"))];
        let before = bytes(&results);
        assert_eq!(apply(&mut results, strict_lane_policy()), 0);
        assert_eq!(bytes(&results), before, "an unchecked boundary must not be touched at all");
    }
}
