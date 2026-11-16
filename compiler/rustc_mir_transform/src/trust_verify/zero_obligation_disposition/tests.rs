use trust_types::Outcome;

use super::*;

fn gap() -> TransportObligationResult {
    super::super::transport_native_verification_gap_row()
}

fn row(kind: &str, outcome: Outcome, solver: &str, reason: &str) -> TransportObligationResult {
    let mut row = super::super::transport_no_obligations_row();
    row.kind = kind.to_string();
    row.description = format!("{kind} ({reason})");
    row.outcome = outcome;
    row.solver = solver.to_string();
    row.reason = Some(reason.to_string());
    row
}

/// The policy-B entry-`Termination` row's wire shape (runtime-checked).
fn entry_row() -> TransportObligationResult {
    row(
        "assert",
        Outcome::RuntimeChecked,
        "trust-classifier",
        "entry `Termination::report` dispatch: reported gap (policy B)",
    )
}

/// The discharged global-alloc premise row's wire shape (skipped).
fn premise_row() -> TransportObligationResult {
    row(
        trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND,
        Outcome::Skipped,
        trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_SOLVER,
        trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_DISCHARGED_REASON,
    )
}

fn coroutine_premise_row() -> TransportObligationResult {
    row("assumption:coroutine", Outcome::Skipped, "trust-classifier", "executor protocol")
}

fn d9_row() -> TransportObligationResult {
    row(
        "assumption:termination-unmeasured",
        Outcome::Skipped,
        "trust-termination-census",
        "termination assumption",
    )
}

fn verifier_row(outcome: Outcome) -> TransportObligationResult {
    row("assert", outcome, "trust-native", "")
}

fn mints_no_obligations(rows: &[TransportObligationResult]) -> bool {
    rows.iter().any(|row| row.kind == "no_obligations")
}

/// MEASURED shape (stage-1 `6011b74bad`): `fn main() -> Result<(), Box<dyn Error>> {
/// Ok(()) }` is a clean zero-obligation run charged only the entry row. It used to
/// publish `[no_obligations: proved]`; it publishes the runtime-checked entry row.
#[test]
fn a_clean_body_charged_the_entry_row_publishes_it_and_no_proof() {
    let rows = rows_over_charged_dispositions(true, &[], &[entry_row()]);
    assert_eq!(rows, vec![entry_row()]);
    assert!(!mints_no_obligations(&rows));
    assert!(rows.iter().all(|row| row.outcome != Outcome::Proved));
}

/// MEASURED shape: the rlib `q5` (`unwrap_or_else(AssertUnwindSafe(Instant::now))`)
/// is an UNCLEAN zero-obligation run with no row of its own, charged the discharged
/// premise. It used to publish the premise row alone; the honest gap row (unknown)
/// now leads it.
#[test]
fn an_unclean_body_charged_the_premise_keeps_the_gap_row_in_front() {
    let rows = rows_over_charged_dispositions(false, &[], &[premise_row()]);
    assert_eq!(rows, vec![gap(), premise_row()]);
    assert_eq!(rows[0].outcome, Outcome::Unknown, "the gap row is an unknown, not a proof");
}

/// A clean run charged the premise publishes the premise row alone — the shape
/// the branch published before (the rlib `pub fn bx() -> Box<u8>` control), and
/// never `no_obligations` beside it.
#[test]
fn a_clean_body_charged_the_premise_publishes_the_premise_alone() {
    let rows = rows_over_charged_dispositions(true, &[], &[premise_row()]);
    assert_eq!(rows, vec![premise_row()]);
    assert!(!mints_no_obligations(&rows));
}

/// When the verifier produced rows of its own they are the base, as in the
/// uncharged branch: no gap row is added beside them, whatever the cleanliness.
#[test]
fn the_verifiers_own_rows_stand_in_for_the_gap_row() {
    let own = verifier_row(Outcome::RuntimeChecked);
    for clean in [false, true] {
        let rows =
            rows_over_charged_dispositions(clean, &[own.clone()], &[own.clone(), entry_row()]);
        assert_eq!(rows, vec![own.clone(), entry_row()], "clean = {clean}");
    }
}

/// Every composed row survives, in the pipeline's order (dispositions, then the
/// D9 charge), behind the gap row — critique H3's "append, never divert".
#[test]
fn every_composed_row_is_kept_in_order_behind_the_gap_row() {
    let composed = [coroutine_premise_row(), premise_row(), entry_row(), d9_row()];
    let rows = rows_over_charged_dispositions(false, &[], &composed);
    let mut expected = vec![gap()];
    expected.extend(composed.iter().cloned());
    assert_eq!(rows, expected);
}

/// One-directional: no input mints proof credit. The output's proved rows are
/// exactly the composed rows' proved rows, and the synthetic row never appears.
#[test]
fn no_input_mints_proof_credit() {
    let proved = verifier_row(Outcome::Proved);
    let composed_sets: [&[TransportObligationResult]; 4] = [
        &[entry_row()],
        &[premise_row()],
        &[premise_row(), entry_row(), d9_row()],
        &[proved.clone(), premise_row()],
    ];
    for clean in [false, true] {
        for transport in [&[][..], &[proved.clone()][..]] {
            for composed in composed_sets {
                let rows = rows_over_charged_dispositions(clean, transport, composed);
                let proved_in =
                    composed.iter().filter(|row| row.outcome == Outcome::Proved).count();
                let proved_out = rows.iter().filter(|row| row.outcome == Outcome::Proved).count();
                assert_eq!(proved_out, proved_in, "clean = {clean}, transport = {transport:?}");
                assert!(!mints_no_obligations(&rows));
                assert!(rows.len() >= composed.len(), "a composed row was dropped");
            }
        }
    }
}
