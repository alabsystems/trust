use super::PendingClock;
use std::time::{Duration, Instant};
use trust_types::verify_budget::{self, VerifyBudgetGuard};

#[test]
fn pending_clock_credits_later_bodies_but_not_its_own_completed_scope() {
    let _ambient = VerifyBudgetGuard::install(None, u64::MAX);
    {
        let _own = VerifyBudgetGuard::install_function(None, u64::MAX);
    }
    let deadline = Instant::now() + Duration::from_millis(5);
    let clock = PendingClock::capture(Some(deadline)).unwrap();
    assert_eq!(clock.deadline(), Ok(Some(deadline)), "own drop precedes mark");
    {
        let _other = VerifyBudgetGuard::install_function(None, u64::MAX);
        std::thread::sleep(Duration::from_millis(10));
    }
    assert!(Instant::now() >= deadline, "original absolute deadline elapsed");
    let credited = clock.deadline().unwrap().unwrap();
    assert_eq!(credited - deadline, verify_budget::clock_credit_since(clock.credit));
    assert!(credited > deadline, "only actual later-body credit moves the bound");
}

#[test]
fn pending_clock_cannot_renew_an_earlier_inherited_wall_stop() {
    let hard = Instant::now() + Duration::from_millis(5);
    let _outer = VerifyBudgetGuard::install(Some(hard), u64::MAX);
    let clock = PendingClock::capture(Some(Instant::now() + Duration::from_secs(60))).unwrap();
    {
        let _other = VerifyBudgetGuard::install_function(None, u64::MAX);
        std::thread::sleep(Duration::from_millis(10));
    }
    assert!(Instant::now() >= hard);
    assert_eq!(clock.deadline(), Ok(Some(hard)));
}

#[test]
fn pending_clock_refuses_another_threads_credit_epoch() {
    let _ambient = VerifyBudgetGuard::install(None, u64::MAX);
    let clock = PendingClock::capture(None).unwrap();
    assert!(std::thread::spawn(move || clock.deadline()).join().unwrap().is_err());
}

#[test]
fn pending_clock_never_retains_an_already_spent_carrier() {
    let _ambient = VerifyBudgetGuard::install(None, u64::MAX);
    assert!(PendingClock::capture(Some(Instant::now() - Duration::from_secs(1))).is_none());
    let _stopped = VerifyBudgetGuard::install(None, 0);
    assert!(PendingClock::capture(None).is_none());
}
