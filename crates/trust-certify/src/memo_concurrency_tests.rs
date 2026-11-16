use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use trust_types::{SourceSpan, VcKind};

use super::*;

fn probe(label: &str) -> VerificationCondition {
    let x = || Formula::Var(format!("memo_concurrency_{label}"), Sort::Int);
    VerificationCondition {
        kind: VcKind::Assertion { message: "concurrent proof".into() },
        function: format!("memo_concurrency::{label}").into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

fn key(vc: &VerificationCondition) -> Vec<u8> {
    let mut key = certify_memo_key_prefix().to_vec();
    key.extend(bincode::serialize(&vc.formula).expect("formula key"));
    key
}

/// Holding the real per-key lock lets every worker reach its cold miss before
/// any producer runs. No timing assumption decides whether requests overlap.
fn await_waiters(flight: &MemoFlight, count: usize) {
    let deadline = Instant::now() + Duration::from_secs(30);
    while Arc::strong_count(&flight.serial) < count + 1 {
        assert!(Instant::now() < deadline, "workers did not reach the per-key lock");
        std::thread::sleep(Duration::from_millis(1));
    }
}

#[test]
fn concurrent_cold_requests_produce_one_real_proof_with_distinct_lineages() {
    let vc = probe("one_producer");
    let key = key(&vc);
    let flight = MemoFlight::acquire(&key);
    let held = flight.serial.lock().expect("gate");
    let produced = Arc::new(AtomicUsize::new(0));
    let workers: Vec<_> = (0..8)
        .map(|index| {
            let mut vc = vc.clone();
            vc.function = format!("{}::{index}", vc.function.as_str()).into();
            let key = key.clone();
            let produced = produced.clone();
            std::thread::spawn(move || {
                let evidence = on_certify_stack(|| {
                    let identity = ObligationIdentity::from_vc(&vc)?;
                    certify_memoized(key, &identity, || {
                        produced.fetch_add(1, Ordering::SeqCst);
                        certify_with_identity_uncached(&vc.formula, &identity)
                    })
                })
                .expect("real proof");
                (vc, evidence)
            })
        })
        .collect();
    await_waiters(&flight, workers.len());
    assert_eq!(produced.load(Ordering::SeqCst), 0);
    drop(held);
    for worker in workers {
        let (vc, evidence) = worker.join().expect("worker");
        assert!(reference_certificate_for(&evidence).is_some());
        assert!(replay_vc_evidence(&vc, &evidence));
        let mut other = vc;
        other.function = format!("{}::wrong", other.function.as_str()).into();
        assert!(!replay_vc_evidence(&other, &evidence));
    }
    assert_eq!(produced.load(Ordering::SeqCst), 1);
    drop(flight);
    assert!(!memo_flights().lock().expect("flights").contains_key(&key));
}

#[test]
fn a_stopped_producer_is_retried_by_the_next_waiter() {
    let vc = probe("stopped");
    let key = key(&vc);
    let flight = MemoFlight::acquire(&key);
    let held = flight.serial.lock().expect("gate");
    let produced = Arc::new(AtomicUsize::new(0));
    let workers: Vec<_> = (0..3)
        .map(|_| {
            let vc = vc.clone();
            let key = key.clone();
            let produced = produced.clone();
            std::thread::spawn(move || {
                let identity = ObligationIdentity::from_vc(&vc).expect("identity");
                certify_memoized(key, &identity, || {
                    if produced.fetch_add(1, Ordering::SeqCst) == 0 {
                        CertifyOutcome::Stopped {
                            cause: trust_types::determinism::StopCause::WallBackstop,
                            evidence: None,
                        }
                    } else {
                        CertifyOutcome::Uncertifiable
                    }
                })
            })
        })
        .collect();
    await_waiters(&flight, workers.len());
    drop(held);
    for worker in workers {
        assert!(worker.join().expect("worker").is_none());
    }
    assert_eq!(produced.load(Ordering::SeqCst), 2);
    assert!(matches!(certify_memo_lookup(&key), Some(None)));
}

#[test]
fn a_panicked_producer_releases_ownership_for_the_next_waiter() {
    let vc = probe("panicked");
    let key = key(&vc);
    let flight = MemoFlight::acquire(&key);
    let held = flight.serial.lock().expect("gate");
    let produced = Arc::new(AtomicUsize::new(0));
    let workers: Vec<_> = (0..2)
        .map(|_| {
            let vc = vc.clone();
            let key = key.clone();
            let produced = produced.clone();
            std::thread::spawn(move || {
                on_certify_stack(|| {
                    let identity = ObligationIdentity::from_vc(&vc)?;
                    certify_memoized(key, &identity, || {
                        assert_ne!(produced.fetch_add(1, Ordering::SeqCst), 0, "producer panic");
                        CertifyOutcome::Uncertifiable
                    })
                })
            })
        })
        .collect();
    await_waiters(&flight, workers.len());
    drop(held);
    for worker in workers {
        assert!(worker.join().expect("worker").is_none());
    }
    assert_eq!(produced.load(Ordering::SeqCst), 2);
    assert!(matches!(certify_memo_lookup(&key), Some(None)));
}

#[test]
fn recursive_production_across_a_stack_hop_does_not_wait_on_itself() {
    let (done, result) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let vc = probe("recursive");
        let key = key(&vc);
        let nested_calls = AtomicUsize::new(0);
        let _ = on_certify_stack(|| {
            let identity = ObligationIdentity::from_vc(&vc)?;
            certify_memoized(key.clone(), &identity, || {
                let _ = on_certify_stack(|| {
                    certify_memoized(key.clone(), &identity, || {
                        nested_calls.fetch_add(1, Ordering::SeqCst);
                        CertifyOutcome::Uncertifiable
                    })
                });
                CertifyOutcome::Uncertifiable
            })
        });
        done.send(nested_calls.load(Ordering::SeqCst)).expect("receiver");
    });
    assert_eq!(result.recv_timeout(Duration::from_secs(30)).expect("recursive search finished"), 1);
}

#[test]
fn independent_formulas_can_produce_concurrently() {
    let (entered, observed) = std::sync::mpsc::channel();
    let mut releases = Vec::new();
    let mut workers = Vec::new();
    for label in ["parallel_a", "parallel_b"] {
        let (release, wait) = std::sync::mpsc::channel();
        releases.push(release);
        let entered = entered.clone();
        workers.push(std::thread::spawn(move || {
            let vc = probe(label);
            let identity = ObligationIdentity::from_vc(&vc).expect("identity");
            certify_memoized(key(&vc), &identity, || {
                entered.send(label).expect("receiver");
                wait.recv().expect("release");
                CertifyOutcome::Uncertifiable
            })
        }));
    }
    for _ in 0..2 {
        observed.recv_timeout(Duration::from_secs(30)).expect("independent producer started");
    }
    for release in releases {
        release.send(()).expect("worker");
    }
    for worker in workers {
        assert!(worker.join().expect("worker").is_none());
    }
}
