//! Trust: Prepare the independent hard Level-0 refutation diagnostic as DATA.
//! The complete forced/modeling-gap/override predicate is unchanged. A calculus
//! alternative cannot discharge or hide this safety floor; the parent must
//! preserve its single original invocation and eventual aborting emission.
//! Extracted from immutable commit 28dd079df1f; this checkpoint is UNCOMPILED.

use super::*;

pub(super) fn prepare_refuted_l0_safety_counterexamples(
    _tcx: TyCtxt<'_>,
    _body: &Body<'_>,
    func_path: &str,
    artifacts: &VerificationArtifacts,
) -> Option<PreparedDiagnostic> {
    let refuted = artifacts
        .results
        .iter()
        .filter(|(vc, result)| {
            // Trust: escalate a GUARANTEED violation — one forced by the program's
            // own values regardless of ANY backend verdict. For an UnboundedAllocation
            // the criterion is the VIOLATION ATOM — the count folds to a constant >=
            // the budget ceiling — which holds whenever the site is reached,
            // independent of reaching guards (a shift's panic-freedom, a branch) that
            // may carry a vcgen-unpinned free var. For other kinds, the whole VC
            // formula must fold to forced-true. A merely POSSIBLE violation (`a + b`,
            // `s[i]` with symbolic len) does not fold and stays a warning, keeping
            // drop-in Rust green.
            //
            // SOUNDNESS — a forced UnboundedAllocation violation OVERRIDES a `Proved`:
            // a GROUND over-ceiling constant (`count` folds to a constant >= the
            // budget, no free input vars) holds on every reaching execution, so the
            // obligation is definitionally UNSAFE and no sound prover can prove it
            // safe. This override is load-bearing under strict verification: the native
            // trust-mc lane lowers only arithmetic-safety / panic-freedom obligations
            // and never the OOM ceiling, so it forges `Proved` for a constant
            // over-budget bulk allocation, and the earlier `!Proved` guard let that
            // forge through. `alloc_over_ceiling_forced` returns true ONLY for a
            // genuinely over-ceiling constant, so a legitimately-safe allocation
            // (`forced == false`) keeps deferring to its backend `Proved` and is never
            // false-failed. For other L0 kinds the `!Proved` guard is kept (conservative
            // — `violation_is_forced` is less battle-tested and a forged `Proved` on
            // those is not the demonstrated bug), so drop-in Rust stays green.
            let forced = match &vc.kind {
                VcKind::UnboundedAllocation { .. } => {
                    trust_router::alloc_over_ceiling_forced(&vc.formula)
                }
                _ => trust_router::violation_is_forced(&vc.formula),
            };
            // Trust (defense-in-depth, SOUNDNESS): NEVER escalate a bare `true`-
            // literal obligation. A vcgen MODELING-GAP fail-close — the
            // `Index<Range>` body with an unresolved receiver length or an
            // untraceable range aggregate, an FFI boundary with no summary, a
            // memory-provenance gap — emits a literal `Formula::Bool(true)`. It
            // carries NO information about the program's actual values, so the
            // indexed/called code may be provably safe (`bytes[52..56]` on a
            // `[u8; 64]` whose `&[T; N]` length was not recovered). Reporting that as
            // a GUARANTEED, every-execution Level-0 VIOLATION is a FALSE REFUTATION
            // of correct code, and `violation_is_forced(Bool(true))` is `true`, so
            // without this the fail-close marker escalates itself. A value-forced
            // violation always folds through REAL modeled atoms (`Ge(1<<28, 1<<28)`,
            // `Ge(100, 64)`), never a bare literal, so this exclusion drops only
            // false refutations. FAIL-CLOSED and strictly conservative: it can only
            // DEMOTE this escalation, never grant a proof — the obligation stays
            // FAILED, so `abort_on_full_verification_failure` (which runs BEFORE this
            // escalation on the same strict path) still hard-errors on it, and the
            // coverage/warning lane still surfaces it.
            let modeling_gap = trust_router::violation_is_modeling_gap_failclose(&vc.formula);
            let forced_overrides_proved = matches!(&vc.kind, VcKind::UnboundedAllocation { .. });
            (forced_overrides_proved || !matches!(result, VerificationResult::Proved { .. }))
                && is_refutable_l0_safety_vc_kind(&vc.kind)
                && forced
                && !modeling_gap
        })
        .count();
    if refuted == 0 {
        return None;
    }
    Some(PreparedDiagnostic {
        aborting: true,
        header: format!(
            "Trust verification found {refuted} guaranteed Level 0 safety violation(s) in `{func_path}`"
        ),
        children: vec![
            PreparedDiagnosticChild::Note(String::from(
                "the violation holds on every reaching execution (integer overflow, out-of-bounds index, divide-by-zero, or an over-budget bulk allocation forced by the program's own values); because verification was explicitly requested this is a build error, not a warning",
            )),
            PreparedDiagnosticChild::Note(String::from(
                "fix the violation, or build with `-Ztrust-verify=off` to opt into Rust-compatibility (no-verification) mode",
            )),
        ],
    })
    // Trust (scope-truncation fix): the parent emits and CONTINUES — no
    // mid-pass abort. Its `ErrorGuaranteed` still fails the build at the driver
    // checkpoint; see `report_strict_l0_verification_failure`.
}
