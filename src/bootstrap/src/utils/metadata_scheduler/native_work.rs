//! Closed Rust-native graph work borrows the SAME implicit execution once.
//! This executor supplies no foreign-process launch capability. Its actual
//! lexical worker join finishes the registered local callback, never a Host
//! child, foreign ProducerBorrow, SDK or durable withholding obligation.

use std::io;
use std::sync::TryLockError;
use std::time::{Duration, Instant};

use build_helper::trust_repo_lock::management::ScopeIdentity;

pub(crate) fn run_native_worker<'env, F, T>(
    expected: &ScopeIdentity,
    deadline: Instant,
    work: F,
) -> io::Result<T>
where
    F: FnOnce(Instant) -> T + Send + 'env,
    T: Send + 'env,
{
    let scope = super::super::exec::protected_scope()?
        .ok_or_else(|| io::Error::other("native graph has no original installed scope"))?;
    if scope.identity() != expected {
        return Err(io::Error::other("native graph belongs to another original scope"));
    }
    let deadline = deadline.min(scope.deadline());
    let before = || -> io::Result<()> {
        if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
    };
    before()?;
    scope.check_current()?;
    let scheduler = super::selected()?;
    let mut original = loop {
        before()?;
        match scheduler.state.try_lock() {
            Ok(original) => break original,
            Err(TryLockError::Poisoned(_)) => {
                return Err(io::Error::other("original native scheduler is poisoned"));
            }
            Err(TryLockError::WouldBlock) => std::thread::sleep(Duration::from_millis(2)),
        }
    };
    before()?;
    scope.check_current()?;
    if !original.embedded_original || original.producer_failed || original.server.is_none() {
        return Err(io::Error::other("native graph has no resolved original embedded execution"));
    }
    // This exclusive original guard stays on the caller's thread through the
    // ACTUAL std lexical scope and join. No token is acquired or replenished.
    let result = scope
        .scoped_threads(|threads| {
            let worker = threads.spawn(move || work(deadline))?;
            worker.join().map_err(|_| io::Error::other("original native graph worker failed"))
        })
        .and_then(|value| value);
    if result.is_err() {
        original.producer_failed = true;
        return result;
    }
    scope.check_current().inspect_err(|_| original.producer_failed = true)?;
    before().inspect_err(|_| original.producer_failed = true)?;
    result
}
