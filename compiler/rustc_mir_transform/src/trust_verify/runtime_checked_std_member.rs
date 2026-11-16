//! Trust (2026-09-29): the RUNTIME-CHECKED disposition of a bundled std/core/alloc
//! member whose internal `Assert` the exact admission lane refused.
//!
//! ## The defect this replaces
//!
//! `trust_ir_bridge::bundled_member_assert_admission` turns a bundled member's
//! entry-prefix Div/Rem/BoundsCheck Asserts into caller-side `requires`; anything
//! else is `Refused`. The bundle gate
//! (`ensure_bundled_member_asserts_exactly_charged_with_charges`) used to return
//! `Err` at the FIRST refused member, which discarded the WHOLE native bundle —
//! every other member's panic-freedom rows and every other Assert-bearing member's
//! caller-side charge with it — and a policy-B tolerance on the lowering-FAILURE
//! path of `abort_on_full_verification_failure` then called the refused member's
//! own Assert "the only obligation it could not discharge" when the refusal text
//! matched two fragments. That was false whenever the discarded bundle held
//! anything else: a charged `wrapping_div`, a `copy_from_slice` length panic, a
//! dependency's `Debug` reached through core's formatting machinery. MEASURED
//! (m3 debug std, strict): `filter().count()` + `match` + `c.wrapping_div(d)`
//! built exit 0 with `functions_verified` 2 of 2 and the program divided by zero.
//!
//! ## The rule
//!
//! A member refused as a COMPLETENESS gap (`MemberAssertRefusalClass::
//! AssertKindOutsideLane`, `GuardedOrNonEntryPrefix` or, since 2026-10-15,
//! `UnrootedOperand` / `UnpairedOperation`), foreign to this crate,
//! whose body is an AUTHENTIC sysroot foundational crate's
//! (`BundledMemberSourceProvenance::body_crate_is_authentic_foundational`), is
//! KEPT in the bundle, and the gate records it (`RuntimeCheckedStdMember`). The
//! member's internal Asserts are rustc's own runtime checks: their panic is left to
//! vanilla Rust semantics (with `-Coverflow-checks=off` an inherited overflow check
//! is not even emitted — the row says "left to", never "retained"). Nothing charges
//! them, so the ROOT owes, per such member:
//!
//! * one `runtime_checked` row in the published set ([`rows_with_runtime_checked_std_members`],
//!   or appended to the zero-obligation base) — the function is never counted
//!   verified, and the proved `no_obligations` row is never minted beside it;
//! * no panic-free registration by any route, and no premise credit
//!   (`collect_full_verification_artifacts`, `verdict_rests_on_user_axiom`);
//! * a warning on every non-`certify` lane, and a compile error under `certify`
//!   ([`abort_on_runtime_checked_std_member`]); memory-safe refuses the row as an
//!   unauthenticated non-proved row.
//!
//! Every other member — an integrity refusal (`Other`), a local member, a body of
//! any other crate (a whole-`core` substitute included) — refuses the bundle
//! exactly as before, and a refusal there is fatal on every fail-closed lane.
//!
//! ## Soundness shape
//!
//! The bundle that is now kept is the same bundle the gate would have admitted had
//! the member no Asserts: every row it publishes is judged by the ordinary
//! success-path gates. What the disposition adds is only the debit above, and it is
//! written by one seam: rows claiming the kind (its solver label, or a reason that
//! begins with [`STD_MEMBER_RUNTIME_CHECK_REASON`]) that this seam did not mint are
//! stripped (staleness/forgery defense, as the coroutine, global-alloc,
//! entry-`Termination` and D9 seams do). Each row it mints states why its
//! obligation was left undecided as a stop token ([`std_member_stop`]).

use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;
use trust_ir_bridge::MemberAssertRefusalClass;
use trust_types::determinism::StopCause;
use trust_types::{Outcome, SourceSpan, TransportObligationResult, VcKind};

use super::{PreparedDiagnostic, PreparedDiagnosticChild, PreparedLocatedDiagnostic, RuntimeCheckedStdMember};

/// The solver label of a runtime-checked std-member row. No engine ran: the row
/// records a disposition, not a verdict.
pub(super) const STD_MEMBER_RUNTIME_CHECK_ROW_SOLVER: &str = "trust-std-member-runtime-check";

/// The reason a runtime-checked std-member row begins with; its stop token
/// ([`std_member_stop`]) follows. A reason that begins with it is one of the keys
/// the strip in [`rows_with_runtime_checked_std_members`] recognizes.
pub(super) const STD_MEMBER_RUNTIME_CHECK_REASON: &str = "bundled std/core/alloc member runtime \
     check (policy B): an internal Assert of an authentic sysroot member that no row of this \
     function discharges is left to rustc's runtime check under vanilla Rust semantics; the \
     function is not counted verified, and `-Ztrust-policy=certify` refuses it";

/// Why the admission lane could not charge the member, in words. Renders nothing
/// but a fixed string.
fn class_phrase(class: MemberAssertRefusalClass) -> &'static str {
    match class {
        MemberAssertRefusalClass::AssertKindOutsideLane => {
            "its Assert kind has no caller-side charge in the exact Div/Rem/BoundsCheck lane"
        }
        MemberAssertRefusalClass::GuardedOrNonEntryPrefix => {
            "an Assert sits off its unguarded entry prefix, so no unconditional caller-side \
             charge exists for it"
        }
        // Trust (2026-10-15): see `MemberAssertRefusalClass::UnrootedOperand`.
        MemberAssertRefusalClass::UnrootedOperand => {
            "an Assert's divisor or index is neither a formal of the member nor a constant, so \
             no caller-side charge can name it"
        }
        // Trust (2026-10-15): see `MemberAssertRefusalClass::UnpairedOperation`.
        MemberAssertRefusalClass::UnpairedOperation => {
            "an Assert pairs with no single operation the exact lane recognizes, so no \
             caller-side charge is derived for it"
        }
        // Never recorded: `Other` refuses the bundle at the gate.
        MemberAssertRefusalClass::Other => "its Asserts were refused",
    }
}

/// Trust (RUNTIME-CHECKED-NO-STOP-CAUSE-1, 2026-11-13): why a member row's
/// obligation was left undecided, written as its reason's stop token. A
/// runtime-checked row whose reason states no stop reads as `unclassified`
/// (`StopCause::of_outcome`), which is not reproducible, so a unit whose rows
/// are otherwise clean could not show a reproducible result. No engine is asked
/// to decide a member's Assert: `not-dispatched`. The one clock that reaches
/// the member set is the per-function deadline declining this run's native
/// lowering (`native_run_lowering_declined_by_deadline`): the members kept then
/// are what a construction the deadline cut recorded, so the row states
/// `wall-backstop`, as the run's gap row does
/// (`transport_native_lowering_gap_row`).
fn std_member_stop(run: Option<&trust_verifier_api::VerificationRunResult>) -> StopCause {
    if run.is_some_and(super::native_run_lowering_declined_by_deadline) {
        StopCause::WallBackstop
    } else {
        StopCause::NotDispatched
    }
}

/// One member's row. Built without a `TyCtxt` so the whole shape is unit-tested;
/// the message renders only the stored `def_path` (never a `Ty`, never a trimmed
/// path — the X2 `must_produce_diag` ICE class).
fn member_row(
    location: Option<SourceSpan>,
    member: &RuntimeCheckedStdMember,
    stop: StopCause,
) -> TransportObligationResult {
    let kind = VcKind::Assertion {
        message: format!(
            "panic freedom: bundled std member `{}` carries an internal Assert that no row of \
             this function discharges ({}); it is left to rustc's runtime check",
            member.def_path,
            class_phrase(member.class)
        ),
    };
    TransportObligationResult {
        assumes: Vec::new(),
        gap_class: None,
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: kind.transport_tag(),
        original_vc_snapshot: None,
        typed_kind: Some(Box::new(kind.clone())),
        description: kind.description(),
        location,
        outcome: Outcome::RuntimeChecked,
        solver: STD_MEMBER_RUNTIME_CHECK_ROW_SOLVER.to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some(stop.stamp(STD_MEMBER_RUNTIME_CHECK_REASON)),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        grade: None,
    }
}

/// Is `row` claiming to be a runtime-checked std-member row? By the row's solver
/// label, or by a reason that begins with [`STD_MEMBER_RUNTIME_CHECK_REASON`],
/// whatever follows it (the stop token this seam writes, or anything else): only
/// this seam writes either.
fn claims_std_member_runtime_check(row: &TransportObligationResult) -> bool {
    row.solver == STD_MEMBER_RUNTIME_CHECK_ROW_SOLVER
        || row
            .reason
            .as_deref()
            .is_some_and(|reason| reason.starts_with(STD_MEMBER_RUNTIME_CHECK_REASON))
}

/// `rows` with every pre-existing row claiming the kind
/// ([`claims_std_member_runtime_check`]) removed and one row per member of this
/// body's `artifacts` appended, each stating the stop its own native run gives
/// ([`std_member_stop`]). `None` — use `rows` unchanged — when there is no member
/// and nothing to strip, so an ordinary body allocates nothing. Both publication
/// branches read the members and the run here, from the artifacts they publish,
/// so neither can state a stop of its own (RUNTIME-CHECKED-NO-STOP-CAUSE-1).
pub(super) fn rows_with_runtime_checked_std_members(
    rows: &[TransportObligationResult],
    location: Option<SourceSpan>,
    artifacts: &super::VerificationArtifacts,
) -> Option<Vec<TransportObligationResult>> {
    rows_with_members(
        rows,
        location,
        &artifacts.runtime_checked_std_members,
        std_member_stop(artifacts.full_verification.as_ref()),
    )
}

fn rows_with_members(
    rows: &[TransportObligationResult],
    location: Option<SourceSpan>,
    members: &[RuntimeCheckedStdMember],
    stop: StopCause,
) -> Option<Vec<TransportObligationResult>> {
    if members.is_empty() && !rows.iter().any(claims_std_member_runtime_check) {
        return None;
    }
    let mut out: Vec<TransportObligationResult> =
        rows.iter().filter(|row| !claims_std_member_runtime_check(row)).cloned().collect();
    out.extend(members.iter().map(|member| member_row(location.clone(), member, stop)));
    Some(out)
}

/// The base rows of the ZERO-obligation transport branch when members are owed
/// (D9 critique H3's precedent: do not divert, append). The proved
/// `no_obligations` row is never minted beside a member row — "nothing to prove"
/// is false when a member's Assert was left to a runtime check — so a vacuously
/// clean native run publishes the verifier's own rows (usually none) and the
/// member rows; an unclean run with no rows keeps the honest gap row.
pub(super) fn zero_obligation_rows(
    native_vacuously_clean: bool,
    transport_results: &[TransportObligationResult],
    location: Option<SourceSpan>,
    artifacts: &super::VerificationArtifacts,
) -> Vec<TransportObligationResult> {
    zero_obligation_rows_with_members(
        native_vacuously_clean,
        transport_results,
        location,
        &artifacts.runtime_checked_std_members,
        std_member_stop(artifacts.full_verification.as_ref()),
    )
}

fn zero_obligation_rows_with_members(
    native_vacuously_clean: bool,
    transport_results: &[TransportObligationResult],
    location: Option<SourceSpan>,
    members: &[RuntimeCheckedStdMember],
    stop: StopCause,
) -> Vec<TransportObligationResult> {
    let base = if !native_vacuously_clean && transport_results.is_empty() {
        vec![super::transport_native_verification_gap_row()]
    } else {
        transport_results.to_vec()
    };
    rows_with_members(&base, location, members, stop).unwrap_or(base)
}

const DISCLOSURE_NOTE: &str = "published as a runtime-checked row; this function is not counted \
     verified. std/core/alloc are foundational TCB (docs/TCB.md): the member's internal Assert \
     is rustc's own runtime check, left to vanilla Rust semantics rather than an obligation Trust \
     discharged, and every other member of the bundle keeps its rows. `-Ztrust-policy=certify` \
     refuses it";

/// The human disclosure on every non-`certify` lane (targo reads the row).
pub(super) fn warn_runtime_checked_std_member(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    members: &[RuntimeCheckedStdMember],
) {
    prepare_runtime_checked_std_member_warning(tcx, body, func_path, members).emit(tcx);
}

pub(super) fn prepare_runtime_checked_std_member_warning(
    _tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    members: &[RuntimeCheckedStdMember],
) -> PreparedLocatedDiagnostic {
    let span = body.span;
    let mut diagnostic = PreparedDiagnostic {
        aborting: false,
        header: format!(
            "Trust verification advisory for `{func_path}`: a bundled std/core/alloc member's \
             internal obligation was not statically discharged"
        ),
        children: Vec::new(),
    };
    for member in members {
        diagnostic.children.push(PreparedDiagnosticChild::Note(format!(
            "bundled member `{}`: {} ({})",
            member.def_path,
            class_phrase(member.class),
            member.reason
        )));
    }
    diagnostic.children.push(PreparedDiagnosticChild::Note(DISCLOSURE_NOTE.into()));
    PreparedLocatedDiagnostic { span, diagnostic }
}

/// `certify` refuses a function that owes a runtime-checked std-member row.
/// Emitted in every output mode, like the other certify aborts.
pub(super) fn abort_on_runtime_checked_std_member(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    members: &[RuntimeCheckedStdMember],
) {
    prepare_runtime_checked_std_member_refusal(tcx, body, func_path, members).emit(tcx);
}

pub(super) fn prepare_runtime_checked_std_member_refusal(
    _tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    members: &[RuntimeCheckedStdMember],
) -> PreparedLocatedDiagnostic {
    let span = body.span;
    let mut diagnostic = PreparedDiagnostic {
        aborting: true,
        header: format!(
            "Trust certify verification failed for `{func_path}`: a bundled std/core/alloc \
             member's internal Assert is left to a runtime check, not statically discharged"
        ),
        children: Vec::new(),
    };
    for member in members {
        diagnostic.children.push(PreparedDiagnosticChild::Note(format!(
            "bundled member `{}`: {} ({})",
            member.def_path,
            class_phrase(member.class),
            member.reason
        )));
    }
    diagnostic.children.push(PreparedDiagnosticChild::Note(
        "under `-Ztrust-policy=certify` a runtime-checked row is fatal; the default lane \
         records it and passes CONDITIONALLY".into(),
    ));
    PreparedLocatedDiagnostic { span, diagnostic }
}

#[cfg(test)]
mod tests;
