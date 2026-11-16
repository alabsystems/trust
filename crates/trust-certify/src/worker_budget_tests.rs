use std::sync::atomic::{AtomicUsize, Ordering};

use trust_types::determinism::StopCause;
use trust_types::verify_budget::{VerifyBudgetGuard, budget_exhausted, exhaustion_cause};

use super::*;

#[test]
fn certify_stack_charges_the_remaining_original_count() {
    let _budget = VerifyBudgetGuard::install(None, 3);
    assert!(!budget_exhausted());
    assert_eq!(
        on_certify_stack(|| {
            assert!(!budget_exhausted());
            Some(17)
        }),
        Some(17)
    );
    assert!(!budget_exhausted());
    assert!(budget_exhausted(), "one caller and one worker poll already consumed two steps");
    assert_eq!(exhaustion_cause(), Some(StopCause::Steps));
}

#[test]
fn panicking_certify_worker_returns_spent_work_and_records_fault() {
    let _budget = VerifyBudgetGuard::install(None, 2);
    let (result, stop) = with_stop_scope(|| {
        on_certify_stack(|| {
            assert!(!budget_exhausted());
            panic!("certifier panicked after consuming a step");
            #[allow(unreachable_code)]
            Some(())
        })
    });
    assert!(result.is_none());
    assert_eq!(stop, Some(StopCause::SolverFault));
    assert!(!budget_exhausted());
    assert!(budget_exhausted(), "panic must not restore the consumed step");
}

#[test]
fn worker_budget_stop_is_classified_before_memo_insertion() {
    let violation = Formula::Var("worker_budget_memo_custody_unique".into(), Sort::Bool);
    let identity = ObligationIdentity::from_violation(&violation).unwrap();
    let key = bincode::serialize(&violation).unwrap();
    let runs = AtomicUsize::new(0);
    for _ in 0..2 {
        let _budget = VerifyBudgetGuard::install(None, 0);
        // Match production ordering: the memo producer is INSIDE the worker.
        // An outer-only stop after this returns is too late to prevent caching.
        assert!(
            on_certify_stack(|| certify_memoized(key.clone(), &identity, || {
                runs.fetch_add(1, Ordering::SeqCst);
                let (evidence, stop) = with_stop_scope(|| {
                    assert!(budget_exhausted());
                    None::<trust_ir::ProofEvidence>
                });
                assert_eq!(stop, Some(StopCause::Steps));
                CertifyOutcome::of(evidence, stop)
            }))
            .is_none()
        );
        assert!(certify_memo_lookup(&key).is_none(), "budget-shaped decline poisoned the memo");
    }
    assert_eq!(runs.load(Ordering::SeqCst), 2);
    let _healthy = VerifyBudgetGuard::install(None, 10);
    assert!(
        on_certify_stack(|| certify_memoized(key.clone(), &identity, || {
            runs.fetch_add(1, Ordering::SeqCst);
            let (evidence, stop) = with_stop_scope(|| None::<trust_ir::ProofEvidence>);
            assert_eq!(stop, None);
            CertifyOutcome::of(evidence, stop)
        }))
        .is_none()
    );
    assert!(matches!(certify_memo_lookup(&key), Some(None)));
    assert!(
        on_certify_stack(|| certify_memoized(key, &identity, || {
            panic!("healthy pure decline should be reused without another producer")
        }))
        .is_none()
    );
    assert_eq!(runs.load(Ordering::SeqCst), 3);
}
