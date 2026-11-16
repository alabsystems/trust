//! Descriptive continuation on the actual completed seven-target base.
//!
//! This shares production's private judgment builder and fenced kernel call.
//! It does not construct a Vf5Reference, certificate or CheckedPresentation;
//! every accepted token and the kernel are dropped before DATA returns. Both
//! production pins and ordinary compiler consumption remain independent gates.

use super::*;
use crate::calculus_row::{CalculusRowClaim, check_calculus_judgment};
use crate::calculus_row::hints::{Vf5HintMiss, decode};

/// An actual artifact/function claim and an untrusted encoded proposal. The
/// existing hint decoder checks the artifact commitment and bounded term codec.
pub struct Vf5JudgmentInput<'a> {
    pub claim: &'a CalculusRowClaim,
    pub proposal: &'a [u8],
}

/// Observations of a genuinely checked pair. These public bytes and digests
/// cannot restore its discarded token or enter production pin tables.
#[derive(Debug)]
pub struct Vf5AcceptedRowData {
    pub artifact_sha256: [u8; 32],
    pub fid: u64,
    pub symbol: Vec<u8>,
    pub environment_sha256: [u8; 32],
    pub statement_sha256: [u8; 32],
}

/// Preserve intake and typed kernel refusals; a missing or malformed proposal
/// is not a semantic counterexample. An inherited stop aborts the whole book.
#[derive(Debug)]
pub enum Vf5JudgmentObservation {
    AcceptedData(Vf5AcceptedRowData),
    Refused(Vf5HintMiss),
}

#[derive(Debug)]
pub struct Vf5JudgmentsMeasurement {
    pub base: Vf5BaseMeasurement,
    pub rows: Vec<Vf5JudgmentObservation>,
}

/// Replay the original fixed package once from EMPTY, observe its seven types,
/// then check every requested row using the SAME private judgment check as the
/// production mint. No caller-supplied digest becomes a pin. Successful DATA
/// does not bypass Vf5Reference::load_package or the ordinary hint session.
pub fn measure_package_with_judgments(
    root: &Path,
    inputs: &[Vf5JudgmentInput<'_>],
) -> Result<Vf5JudgmentsMeasurement, Vf5MeasurementMiss> {
    let (kernel, base) = replay_for_observation(root)?;
    let rows = observe_rows(&kernel, inputs)?;
    check_deadline()?;
    drop(kernel);
    check_deadline()?;
    Ok(Vf5JudgmentsMeasurement { base, rows })
}

fn observe_rows(
    kernel: &clean_kernel::ReferenceKernel,
    inputs: &[Vf5JudgmentInput<'_>],
) -> Result<Vec<Vf5JudgmentObservation>, Vf5MeasurementMiss> {
    observe_rows_checked(kernel, inputs, || check_deadline().map_err(Into::into))
}

fn observe_rows_checked(
    kernel: &clean_kernel::ReferenceKernel,
    inputs: &[Vf5JudgmentInput<'_>],
    mut checkpoint: impl FnMut() -> Result<(), Vf5MeasurementMiss>,
) -> Result<Vec<Vf5JudgmentObservation>, Vf5MeasurementMiss> {
    checkpoint()?;
    let mut rows = Vec::new();
    rows.try_reserve(inputs.len())
        .map_err(|error| Vf5BaseMiss::Io(std::io::Error::other(error)))?;
    for input in inputs {
        checkpoint()?;
        let checked = decode(&input.claim.artifact, input.proposal).and_then(|(annotation, certs)| {
            check_calculus_judgment(kernel, input.claim, &annotation, &certs)
                .map_err(Vf5HintMiss::Row)
        });
        checkpoint()?;
        let observation = match checked {
            Ok(checked) => {
                let mut artifact = Sha256::new();
                for chunk in input.claim.artifact.chunks(4096) {
                    checkpoint()?;
                    artifact.update(chunk);
                }
                let mut symbol = Vec::new();
                symbol.try_reserve(input.claim.symbol.len())
                    .map_err(|error| Vf5BaseMiss::Io(std::io::Error::other(error)))?;
                for chunk in input.claim.symbol.chunks(4096) {
                    checkpoint()?;
                    symbol.extend_from_slice(chunk);
                }
                checkpoint()?;
                let data = Vf5AcceptedRowData {
                    artifact_sha256: artifact.finalize().into(),
                    fid: input.claim.fid,
                    symbol,
                    environment_sha256: checked.accepted.env_digest().0,
                    statement_sha256: checked.accepted.decl_digest(),
                };
                // In particular, never call ReferenceCertificate::from_accepted.
                drop(checked);
                Vf5JudgmentObservation::AcceptedData(data)
            }
            Err(error) => Vf5JudgmentObservation::Refused(error),
        };
        checkpoint()?;
        rows.push(observation);
    }
    checkpoint()?;
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calculus_row::{CalculusRowMiss, Vf5Reference, hints, test_support};

    fn claim(fid: u64) -> CalculusRowClaim {
        CalculusRowClaim { artifact: b"TRUST".to_vec(), fid, symbol: b"s".to_vec() }
    }

    #[test]
    fn observing_a_real_entry_token_does_not_admit_an_unpinned_base() {
        // Existing unit-only stand-in tests the shared entry mechanism. The
        // actual fixed package and compiler artifacts are separate inputs.
        let kernel = test_support::toy_kernel(true);
        let before = kernel.env_digest();
        let claim = claim(0);
        let term = clean_kernel::Expr::nat_lit(0);
        let proposal = hints::encode(&claim.artifact, &term, &term).unwrap();
        let rows = observe_rows(&kernel, &[Vf5JudgmentInput { claim: &claim, proposal: &proposal }]).unwrap();
        let [Vf5JudgmentObservation::AcceptedData(data)] = rows.as_slice() else { panic!("{rows:?}") };
        assert_eq!(data.environment_sha256, before.0);
        assert_eq!(data.artifact_sha256, <[u8; 32]>::from(Sha256::digest(&claim.artifact)));
        assert_eq!(kernel.env_digest(), before);
        assert!(matches!(Vf5Reference::new(kernel), Err(CalculusRowMiss::UnpinnedBase(_))));
    }

    #[test]
    fn kernel_identity_refusal_is_distinct_from_stale_or_malformed_proposal_intake() {
        let kernel = test_support::toy_kernel(true);
        let wrong_fid = claim(1);
        let mut changed = claim(0);
        changed.artifact.push(0);
        let original = claim(0);
        let term = clean_kernel::Expr::nat_lit(0);
        let proposal = hints::encode(&original.artifact, &term, &term).unwrap();
        let rows = observe_rows(&kernel, &[
            Vf5JudgmentInput { claim: &wrong_fid, proposal: &proposal },
            Vf5JudgmentInput { claim: &changed, proposal: &proposal },
            Vf5JudgmentInput { claim: &original, proposal: &proposal[..proposal.len() - 1] },
        ]).unwrap();
        assert!(matches!(&rows[0], Vf5JudgmentObservation::Refused(Vf5HintMiss::Row(CalculusRowMiss::Refused(_)))));
        assert!(matches!(&rows[1], Vf5JudgmentObservation::Refused(Vf5HintMiss::Invalid(_))));
        assert!(matches!(&rows[2], Vf5JudgmentObservation::Refused(Vf5HintMiss::Envelope(_))));
    }

    #[test]
    fn spent_ambient_budget_discards_all_row_observations() {
        let kernel = test_support::toy_kernel(true);
        let claim = claim(0);
        let term = clean_kernel::Expr::nat_lit(0);
        let proposal = hints::encode(&claim.artifact, &term, &term).unwrap();
        let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(None, 0);
        assert!(matches!(observe_rows(&kernel, &[Vf5JudgmentInput { claim: &claim, proposal: &proposal }]),
            Err(Vf5MeasurementMiss::Base(Vf5BaseMiss::Stopped(StopCause::Steps)))));
    }

    #[test]
    fn a_real_stop_after_kernel_acceptance_discards_the_observation_book() {
        let kernel = test_support::toy_kernel(true);
        let claim = claim(0);
        let term = clean_kernel::Expr::nat_lit(0);
        let proposal = hints::encode(&claim.artifact, &term, &term).unwrap();
        let input = Vf5JudgmentInput { claim: &claim, proposal: &proposal };
        let mut budget = None;
        let mut checkpoints = 0;
        let result = observe_rows_checked(&kernel, &[input], || {
            checkpoints += 1;
            // The fourth boundary is the artifact hashing loop after the
            // real private entry check. Install a genuine spent Trust scope;
            // no fabricated stop value or accepted token is supplied.
            if checkpoints == 4 {
                budget = Some(trust_types::verify_budget::VerifyBudgetGuard::install(None, 0));
            }
            check_deadline().map_err(Into::into)
        });
        assert_eq!(checkpoints, 4);
        assert!(matches!(result, Err(Vf5MeasurementMiss::Base(Vf5BaseMiss::Stopped(StopCause::Steps)))));
        drop(budget);
    }
}
