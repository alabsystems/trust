// Trust: prepare memory-safe policy diagnostics as ordered report DATA.
// Source-dependent predicates and queries run at the original eager callpoint.

use super::*;

pub(super) fn prepare_memory_safe_non_demotable_failure<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
    artifacts: &VerificationArtifacts,
    effective_rows: &[TransportObligationResult],
    // Trust (2026-10-10, ZERO-ROW-GATE): the publisher's verdict on a zero-
    // obligation body (`zero_obligation_native_vacuously_clean`); `None` when the
    // body has bridged obligations.
    zero_obligation_vacuously_clean: Option<bool>,
) -> Option<PreparedDiagnostic> {
    // Trust (2026-09-27): memory-safe demotes a gap on the premise that a body with no
    // `unsafe` cannot reach undefined behaviour. A MASKED source breaks it with no
    // `unsafe` token here: a verify-off dependency's call or function value, a
    // std/core/alloc routine instantiated at a dependency type, or foreign drop glue
    // runs a body no verdict covers. Measured on stage-1 436c9eb6d0:
    // `o.unwrap_or_default().0` over `Option<dep::Evil>`, whose verify-off `Default`
    // is `unreachable_unchecked()`, built rc=0 with NO error or warning (its JSON row
    // read `unknown`). Such a body is admitted only when every row it publishes is
    // proved and no foreign-reaching consumer call went uncharged
    // (`uncharged_foreign_closure_consumer_edges` — the zero-row shape above); a
    // demoted or unproved row standing beside the masked edge is refused.
    let masked_source_uncovered = function_has_masked_fail_closed_dispatch(tcx, body)
        && (effective_rows.iter().any(|row| !row.outcome.is_proved())
            || !uncharged_foreign_closure_consumer_edges(tcx, body, func_path, artifacts)
                .is_empty());
    if !masked_source_uncovered
        && !memory_safe_artifacts_have_non_demotable_failure(artifacts, effective_rows)
        && !memory_safe_zero_obligation_body_is_unclean(artifacts, zero_obligation_vacuously_clean)
    {
        // The collapse row is ADMITTED, and it is a whole function that was not
        // verified. Say so on the diagnostic surface: before this, such a body
        // printed only its proved VC rows ("1 proved … out of 1 obligation(s)"),
        // emitted no warning and exited 0.
        if effective_rows.iter().any(transport_row_is_authenticated_native_lowering_assumption) {
            let header = format!(
                "Trust memory-safe verification admitted `{func_path}` on an unverified \
                 assumption: native typed-TrustIr lowering did not complete"
            );
            let mut children = vec![PreparedDiagnosticChild::Note(
                "recorded as `assumption:native-lowering` (skipped, NOT proved): the body's own \
                 panic-freedom obligations were not discharged; every call it makes resolves to \
                 a local function that this crate verifies, refuses, or admits on its own row \
                 under this same rule, so the assumption covers no callee"
                    .into(),
            )];
            if let Some(run) = artifacts.full_verification.as_ref() {
                for diagnostic in run
                    .diagnostics
                    .iter()
                    .filter(|d| d.contains(NATIVE_TRUST_IR_LOWERING_FAILED_MARKER))
                    .take(2)
                {
                    children.push(PreparedDiagnosticChild::Note(format!(
                        "native full verifier diagnostic: {diagnostic}"
                    )));
                }
            }
            return Some(PreparedDiagnostic { aborting: false, header, children });
        }
        return None;
    }

    let has_coroutine_protocol_premise =
        effective_rows.iter().any(transport_row_is_coroutine_protocol_assumption);
    let header = if has_coroutine_protocol_premise {
        format!(
            "Trust memory-safe verification failed for `{func_path}`: coroutine \
             executor-protocol premise is unproved"
        )
    } else {
        format!(
            "Trust memory-safe verification failed for `{func_path}`: at least one result is \
             not an authenticated memory-safe assumption"
        )
    };
    let mut children = Vec::new();
    if has_coroutine_protocol_premise {
        children.push(PreparedDiagnosticChild::Note(
            "supported user data-safety obligations were still verified and reported \
             independently; memory-safe policy does not admit the compiler-generated \
             ResumedAfterReturn/Panic/Drop executor premise"
                .into(),
        ));
    }
    if masked_source_uncovered {
        children.push(PreparedDiagnosticChild::Note(
            "this body reaches code outside the verified closure and the std/core/alloc TCB \
             (a verify-off dependency's call or function value, a std/core/alloc routine \
             instantiated at a dependency type, or foreign drop glue), and either not every \
             row it publishes is proved or a closure-driving consumer call into that code is \
             charged by no row: memory-safe demotes a gap only on the premise that a body with \
             no `unsafe` cannot reach undefined behaviour, and that code can"
                .into(),
        ));
    }
    // Trust (2026-10-10, ZERO-ROW-GATE): name the empty-inventory refusal when it is
    // this conjunct that decided it (the native run itself was vacuously clean, so
    // the zero-row branch of `memory_safe_artifacts_have_non_demotable_failure`
    // would have admitted the body).
    if memory_safe_zero_obligation_body_is_unclean(artifacts, zero_obligation_vacuously_clean)
        && artifacts.full_verification.as_ref().is_some_and(native_run_is_vacuously_clean)
    {
        children.push(PreparedDiagnosticChild::Note(
            "this function has no obligation of its own, but it is not vacuously verified: a \
             call it makes is discharged by no authenticated panic-freedom registry (or a \
             consumer call reaches unverified code uncharged), so it publishes an unproved \
             row (outcome `unknown`) that is not an authenticated memory-safe assumption"
                .into(),
        ));
    }
    if artifacts.full_verification.as_ref().is_some_and(native_run_trust_ir_lowering_failed)
        && !effective_rows.iter().any(transport_row_is_authenticated_native_lowering_assumption)
    {
        let edges = memory_safe_assumption_uncharged_edges(tcx, body);
        if !edges.is_empty() {
            children.push(PreparedDiagnosticChild::Note(format!(
                "native typed-TrustIr lowering did not complete, and this body calls out of \
                 the verified closure ({}): the lowering charged none of its callees (the \
                 `[trust-absent-callee-assumption]` rows memory-safe refuses), so an \
                 `assumption:native-lowering` row cannot stand for them",
                edges.join(", "),
            )));
        }
    }
    children.push(PreparedDiagnosticChild::Note(
        "-Ztrust-policy=memory-safe conditionally admits only compiler-marked safe-code panic \
         or lowering assumptions in functions with neither source nor inlined unsafe; proofs \
         remain proofs, while UB, hardened, contract, functional, unmarked unknown, runtime-checked, \
         and other failed rows remain build errors"
            .into(),
    ));
    children.push(PreparedDiagnosticChild::Note(format!(
        "effective transport rows: {} total, {} authenticated memory-safe assumption(s)",
        effective_rows.len(),
        effective_rows
            .iter()
            .filter(|row| transport_row_is_authenticated_memory_safe_assumption(row))
            .count(),
    )));
    Some(PreparedDiagnostic { aborting: true, header, children })
}
