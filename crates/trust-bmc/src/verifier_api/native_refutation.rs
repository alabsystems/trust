//! Independent native candidate checks, deliberately without Rust source authority.

use super::*;

#[cfg(test)]
pub(super) fn check(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    consumer_rows: &[&trust_mc_trust_bmc::NativeTrustMcChcPdrObligation],
    row: &trust_mc_driver::NativeTrustIrChcPdrRefuted,
    engine: trust_mc_core::ChcPdrEngine,
) -> Result<(TrustMcNativeTypedChcPdrNormalizedInput, String), String> {
    check_with_options(
        bundle,
        obligation,
        consumer_rows,
        row,
        &trust_mc_core::ChcPdrSolveOptions::default().with_engine(engine),
    )
}

pub(super) fn check_with_options(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    consumer_rows: &[&trust_mc_trust_bmc::NativeTrustMcChcPdrObligation],
    row: &trust_mc_driver::NativeTrustIrChcPdrRefuted,
    caller_options: &trust_mc_core::ChcPdrSolveOptions,
) -> Result<(TrustMcNativeTypedChcPdrNormalizedInput, String), String> {
    let native_id = &row.translated.obligation.obligation_id;
    let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
        &row.verification.outcome.status
    else {
        return Err("refuted row carries no witness payload".to_string());
    };
    let matching: Vec<_> = consumer_rows
        .iter()
        .copied()
        .filter(|consumer| &consumer.obligation.obligation_id == native_id)
        .collect();
    let [fresh_row] = matching.as_slice() else {
        return Err(format!(
            "consumer translation of the native bundle yielded {} rows for `{native_id}`; \
             expected exactly one",
            matching.len()
        ));
    };
    validate_native_trust_mc_row_request_config(fresh_row)?;
    if !fresh_row.diagnostics.is_empty() {
        return Err(format!(
            "consumer translation of the native bundle recorded {} fail-closed lowering \
             diagnostic(s); a derivation may pass through an unconditional error rule",
            fresh_row.diagnostics.len()
        ));
    }
    let expected = trust_mc_driver::normalized_typed_chc_pdr_input(&fresh_row.obligation).map_err(
        |error| {
            format!(
                "consumer translation of the native bundle could not be normalized: {}",
                native_typed_chc_pdr_error_reason(error)
            )
        },
    )?;
    // Reconstruct the executed profile from the consumer's own retained
    // request, never from a solver-returned row or the adapter's global mode.
    let expected_options = fresh_row.request_config.solve_options(caller_options);
    let summary = validate_bound_typed_chc_pdr_refutation_witness_with_options(
        bundle,
        witness,
        obligation,
        &fresh_row.obligation,
        &row.verification,
        &expected,
        &expected_options,
    )?;
    Ok((expected, summary))
}
