use super::*;

fn far() -> Instant {
    Instant::now() + Duration::from_secs(3600)
}

#[test]
fn worker_borrows_remaining_count_and_restores_its_previous_tls() {
    let deadline = far();
    let _caller = VerifyBudgetGuard::install(Some(deadline), 5);
    assert!(!budget_exhausted());
    with_worker_budget(|budget| {
        std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    let local_deadline = far();
                    let _local = VerifyBudgetGuard::install(Some(local_deadline), 99);
                    budget.run(|| {
                        assert_eq!(current_deadline(), Some(deadline));
                        assert_eq!(VERIFY_STEPS.with(Cell::get), 4);
                        assert!(!budget_exhausted());
                        assert!(!budget_exhausted());
                    });
                    assert_eq!(current_deadline(), Some(local_deadline));
                    assert_eq!(VERIFY_STEPS.with(Cell::get), 99);
                    assert_eq!(exhaustion_cause(), None);
                })
                .join()
                .unwrap();
        })
    });
    assert_eq!(current_deadline(), Some(deadline));
    assert_eq!(VERIFY_STEPS.with(Cell::get), 2);
    assert!(!budget_exhausted());
    assert!(!budget_exhausted());
    assert!(budget_exhausted());
    assert_eq!(exhaustion_cause(), Some(StopCause::Steps));
}

#[test]
fn worker_keeps_expired_deadline_and_first_trip_even_after_spending_steps() {
    let original = Instant::now() - Duration::from_millis(1);
    let _caller = VerifyBudgetGuard::install(Some(original), WALL_POLL_INTERVAL);
    assert_eq!(exhaustion_cause(), None);
    with_worker_budget(|budget| {
        std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    budget.run(|| {
                        assert_eq!(current_deadline(), Some(original));
                        assert!(
                            budget_exhausted(),
                            "first poll must see the original expired clock"
                        );
                        for _ in 0..WALL_POLL_INTERVAL {
                            budget_exhausted();
                        }
                        assert_eq!(VERIFY_STEPS.with(Cell::get), 0);
                        assert_eq!(exhaustion_cause(), Some(StopCause::WallBackstop));
                    })
                })
                .join()
                .unwrap();
        })
    });
    assert_eq!(current_deadline(), Some(original));
    assert_eq!(exhaustion_cause(), Some(StopCause::WallBackstop));
    // A second hop must import the existing first trip, not reset it to Steps.
    with_worker_budget(|budget| {
        std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    budget.run(|| {
                        assert!(budget_exhausted());
                        assert_eq!(exhaustion_cause(), Some(StopCause::WallBackstop));
                    })
                })
                .join()
                .unwrap();
        })
    });
    assert_eq!(exhaustion_cause(), Some(StopCause::WallBackstop));
}

#[test]
fn worker_and_dispatch_panics_return_consumption_without_renewing_budget() {
    let original = far();
    let _caller = VerifyBudgetGuard::install(Some(original), 3);
    assert!(!budget_exhausted());
    let result = std::panic::catch_unwind(|| {
        with_worker_budget(|budget| {
            std::thread::scope(|scope| {
                scope
                    .spawn(|| {
                        let local = far();
                        let _local = VerifyBudgetGuard::install(Some(local), 77);
                        let panic = std::panic::catch_unwind(|| {
                            budget.run(|| {
                                assert!(!budget_exhausted());
                                panic!("worker failed after charged work");
                            })
                        });
                        assert!(panic.is_err());
                        assert_eq!(current_deadline(), Some(local));
                        assert_eq!(VERIFY_STEPS.with(Cell::get), 77);
                    })
                    .join()
                    .unwrap();
            });
            panic!("dispatcher failed after joining the worker");
        })
    });
    assert!(result.is_err());
    assert_eq!(current_deadline(), Some(original));
    assert_eq!(VERIFY_STEPS.with(Cell::get), 1);
    assert!(!budget_exhausted());
    assert!(budget_exhausted());
}

#[test]
fn refused_spawn_leaves_original_state_and_makes_no_budget_observation() {
    let original = far();
    let _caller = VerifyBudgetGuard::install(Some(original), 2);
    assert!(!budget_exhausted());
    let mark = clock_credit_mark();
    let refused: std::io::Result<()> = with_worker_budget(|worker| {
        // A Builder::spawn_scoped error drops its unstarted closure/token.
        let _unstarted = worker;
        Err(std::io::Error::other("test spawner refused before worker start"))
    });
    assert!(refused.is_err());
    assert_eq!(current_deadline(), Some(original));
    assert_eq!(VERIFY_STEPS.with(Cell::get), 1);
    assert_eq!(exhaustion_cause(), None);
    assert_eq!(clock_credit_since(mark), Duration::ZERO);
    assert!(!budget_exhausted());
    assert!(budget_exhausted());
}

#[test]
fn only_nested_function_work_earns_clock_credit_across_the_worker() {
    let original = far();
    let _caller = VerifyBudgetGuard::install_function(Some(original), 20);
    let mark = clock_credit_mark();
    with_worker_budget(|budget| {
        std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    budget.run(|| {
                        let _nested = VerifyBudgetGuard::install_function(Some(far()), 3);
                        assert!(!budget_exhausted());
                        std::thread::sleep(Duration::from_millis(2));
                    })
                })
                .join()
                .unwrap();
        })
    });
    let credit = clock_credit_since(mark);
    assert!(credit >= Duration::from_millis(2));
    assert_eq!(current_deadline(), original.checked_add(credit));
    assert_eq!(credited(Some(original), mark), current_deadline());
    assert_eq!(VERIFY_STEPS.with(Cell::get), 20, "a nested function has its own count");
    let deadline = current_deadline();
    let mark = clock_credit_mark();
    with_worker_budget(|budget| {
        std::thread::scope(|scope| {
            scope
                .spawn(|| budget.run(|| std::thread::sleep(Duration::from_millis(2))))
                .join()
                .unwrap();
        })
    });
    assert_eq!(clock_credit_since(mark), Duration::ZERO, "a stack hop is not another function");
    assert_eq!(current_deadline(), deadline, "ordinary worker work renews no clock");
}
