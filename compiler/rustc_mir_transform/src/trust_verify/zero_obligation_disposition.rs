//! Trust (2026-10-03): the rows a ZERO-obligation body publishes when an additive
//! policy disposition charged it — the coroutine executor-protocol premise, the
//! `GlobalAlloc` contract (`contract:global-alloc-dealloc-panic-free`), or the
//! policy-B entry-`Termination::report` dispatch row.
//!
//! ## The defect this replaces
//!
//! `publish_body_verification_outcome` publishes one of two row sets. A body with
//! zero VC-level obligations publishes the ZERO-OBLIGATION rows: exactly one base —
//! the synthetic `no_obligations` row (proved), the honest `native-verification-gap`
//! row (unknown), or the transport rows — with the D9 charge and the runtime-checked
//! std-member rows appended to it (D9 critique H3: append, never divert). Every other
//! body publishes `effective_rows`, into which every additive policy row has been
//! composed. The zero-obligation branch was guarded by "no coroutine disposition and
//! no global-alloc disposition", and never read the entry-`Termination` row at all.
//! Both mistakes erased a row the verdict rests on from the JSON transport, which is
//! what `targo trust` grades. MEASURED on stage-1 `6011b74bad` (raw trustc,
//! `-Ztrust-verify=on -Ztrust-verify-output=json --error-format=human`):
//!
//! * DROPPED ENTRY ROW. `fn main() -> Result<(), Box<dyn std::error::Error>> {
//!   Ok(()) }` published `[no_obligations: proved]` and a crate summary of
//!   `functions_verified: 1, total_proved: 1, total_runtime_checked: 0` under the
//!   default and strict policies (rc 0). The runtime-checked entry row that
//!   `effective_rows` carried — the one the compiler's own human warning says "is
//!   counted CONDITIONAL" — was gone, so targo's strict lane would grade PASS where
//!   it owes CONDITIONAL-PASS.
//! * DROPPED GAP ROW. The rlib `pub fn q5(o: Option<Instant>) -> Instant {
//!   o.unwrap_or_else(AssertUnwindSafe(Instant::now)) }` is charged the discharged
//!   global-alloc premise (an rlib does not choose the final link's allocator). Its
//!   zero-obligation run is NOT vacuously clean (a call no registry discharges;
//!   `TRUST_PF_REG_TRACE` prints `all_calls_proven=false`), so the branch owed the
//!   gap row; the premise diverted the body to `effective_rows` and only the
//!   `skipped` premise row was published, under every policy. targo's strict and
//!   memory-safe lanes would grade that `assumed` row CONDITIONAL-PASS where the
//!   unknown gap row owes INCONCLUSIVE. Its whole-program twin (not charged)
//!   publishes the gap row.
//!
//! ## The rule
//!
//! When any of the three dispositions charged a zero-obligation body, the body
//! publishes `effective_rows` — every disposition's row plus the D9 charge and the
//! std-member rows, already composed in the pipeline's one fixed order, each seam
//! having stripped any stale row claiming its kind — with the gap row in FRONT of
//! it exactly when the uncharged branch would have published the gap row as its
//! base: the native run was not vacuously clean and produced no transport row
//! ([`rows_over_charged_dispositions`]). The synthetic `no_obligations` row is never
//! minted beside a charged row ("nothing to prove" is false when a premise was
//! relied on or a dispatch was left to a runtime check — the
//! `runtime_checked_std_member::zero_obligation_rows` rule); the uncharged branch
//! and its D9 and std-member arms are untouched.
//!
//! ## What does not move
//!
//! Only the PUBLISHED rows change: the JSON transport and the one tally the human
//! summary line shares with it (`PublishedRowTally`). `effective_rows` — the
//! memory-safe fatality boundary — and the VC-level artifacts the strict and
//! certify gates read are unchanged, so no lane's exit code moves. The change is
//! one-directional: it can only add a non-proved row or withhold the synthetic
//! proved one, never the reverse.

use trust_types::TransportObligationResult;

/// The rows a zero-obligation body publishes when an additive policy disposition
/// (coroutine premise, global-alloc contract, entry-`Termination` dispatch) charged
/// it. `transport_results` is the base the uncharged branch reads (the verifier's
/// own rows); `composed_rows` is `effective_rows`, which already carries every
/// disposition row, the D9 charge and the std-member rows.
///
/// The honest `native-verification-gap` row leads exactly when the native run was
/// not vacuously clean and produced no row of its own — the case in which the
/// uncharged branch publishes the gap row as its base. The synthetic proved
/// `no_obligations` row is never minted here.
pub(super) fn rows_over_charged_dispositions(
    native_vacuously_clean: bool,
    transport_results: &[TransportObligationResult],
    composed_rows: &[TransportObligationResult],
) -> Vec<TransportObligationResult> {
    let owes_gap_row = !native_vacuously_clean && transport_results.is_empty();
    let mut out = Vec::with_capacity(composed_rows.len() + usize::from(owes_gap_row));
    if owes_gap_row {
        out.push(super::transport_native_verification_gap_row());
    }
    out.extend(composed_rows.iter().cloned());
    out
}

#[cfg(test)]
mod tests;
