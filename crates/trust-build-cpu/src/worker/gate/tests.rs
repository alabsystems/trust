use super::*;

#[test]
fn pause_excludes_inflight_and_offered_credits_until_backing_drops() {
    let gate = Gate::new();
    let attempt = gate.begin().unwrap().unwrap();
    assert!(gate.pause().unwrap().is_none());
    let permit = attempt.publish().unwrap();
    assert!(gate.pause().unwrap().is_none());
    let ticket = AtomicU8::new(super::super::OFFERED);
    assert!(permit.commit(&ticket));
    assert!(gate.pause().unwrap().is_none());
    drop(permit);
    let pause = gate.pause().unwrap().unwrap();
    assert!(!gate.running());
    assert!(gate.begin().unwrap().is_none());
    assert!(gate.pause().unwrap().is_none());
    pause.resume().unwrap();
    assert!(gate.running());
    drop(gate.begin().unwrap().unwrap());
    gate.pause().unwrap().unwrap().resume().unwrap();
}

#[test]
fn abandoned_pause_never_silently_resumes_admission() {
    let gate = Gate::new();
    drop(gate.pause().unwrap().unwrap());
    assert!(!gate.running());
    assert_eq!(gate.begin().err().unwrap().kind(), io::ErrorKind::PermissionDenied);
    assert_eq!(gate.pause().err().unwrap().kind(), io::ErrorKind::PermissionDenied);
}

#[test]
fn concurrent_pause_and_extra_admission_have_only_one_winner() {
    for _ in 0..16 {
        let gate = Gate::new();
        let barrier = std::sync::Barrier::new(2);
        let (pause, permit) = std::thread::scope(|scope| {
            let paused = scope.spawn(|| {
                barrier.wait();
                gate.pause().unwrap()
            });
            let acquired = scope.spawn(|| {
                barrier.wait();
                gate.begin().unwrap().map(|attempt| attempt.publish().unwrap())
            });
            (paused.join().unwrap(), acquired.join().unwrap())
        });
        match (pause, permit) {
            (Some(pause), None) => pause.resume().unwrap(),
            (None, Some(permit)) => {
                assert!(permit.commit(&AtomicU8::new(super::super::OFFERED)));
                drop(permit);
                gate.pause().unwrap().unwrap().resume().unwrap();
            }
            _ => panic!("pause and acquisition did not exclude one another"),
        }
        assert!(gate.running());
    }
}

#[test]
fn uncertain_settlement_poison_survives_original_permit_drop() {
    let gate = Gate::new();
    let permit = gate.begin().unwrap().unwrap().publish().unwrap();
    permit.poison();
    drop(permit);
    assert!(!gate.running());
    assert!(gate.begin().is_err());
    assert!(gate.pause().is_err(), "unknown worker return cannot become a primary loan");
}
