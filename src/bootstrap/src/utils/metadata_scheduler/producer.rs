//! The same captured GNU owner for embedded producing commands.
//!
//! This borrows the original implicit execution, never a new pool or token.
//! The existing metadata mutex serializes the borrower with both metadata and
//! other producers. Scope registration and Host admission remain independent.

use std::io;
use std::process::Command;
use std::sync::{MutexGuard, TryLockError};
use std::time::{Duration, Instant};

use build_helper::trust_repo_lock::management::{JoinedChild, LaunchIdentity, LaunchRegistration};

use super::{State, selected};

/// Retained by the actual spawning/waiting thread through the child's original
/// readers. Deliberately not Send: another thread cannot take its implicit slot.
/// Only the exact native joined-child capability permits ordinary return.
#[must_use]
pub(crate) struct ProducerBorrow {
    state: Option<MutexGuard<'static, State>>,
    launch: LaunchIdentity,
    deadline: Instant,
}

/// Configure after all argv/environment/stdio processing, before actual spawn.
/// The deadline limits waiting; it cannot grant execution or extend the scope.
pub(crate) fn prepare_producer(
    command: &mut Command,
    registration: &LaunchRegistration,
    original_deadline: Instant,
) -> io::Result<ProducerBorrow> {
    let scheduler = selected()?;
    let state = loop {
        let remaining = original_deadline
            .checked_duration_since(Instant::now())
            .ok_or_else(|| io::Error::new(io::ErrorKind::TimedOut, "producer borrower deadline"))?;
        match scheduler.state.try_lock() {
            Ok(state) => break state,
            Err(TryLockError::Poisoned(_)) => {
                return Err(io::Error::other("original producing borrower is poisoned"));
            }
            Err(TryLockError::WouldBlock) => {
                std::thread::sleep(remaining.min(Duration::from_millis(2)));
            }
        }
    };
    if Instant::now() >= original_deadline {
        return Err(io::Error::new(io::ErrorKind::TimedOut, "producer borrower deadline"));
    }
    if !state.embedded_original || state.producer_failed {
        return Err(io::Error::other("producing command has no resolved original embedded owner"));
    }
    let server = state
        .server
        .as_ref()
        .ok_or_else(|| io::Error::other("producing command has no retained original GNU server"))?;
    // This derives every GNU variable from the SAME actual descriptors. It
    // replaces Bootstrap's earlier MAKEFLAGS removal, without ambient import,
    // pipe construction, credit acquisition or token replenishment.
    if !super::scheduler_transport_supported() {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "original producer transport requires Trust std descriptor inheritance",
        ));
    }
    super::configure_original_transport(server, command, state.sdk_present)?;
    Ok(ProducerBorrow {
        state: Some(state),
        launch: registration.identity().clone(),
        deadline: original_deadline,
    })
}

impl ProducerBorrow {
    /// Preserve a completed child's observations even if its local bookend or
    /// original deadline cannot be accepted. This never returns execution.
    pub(crate) fn unresolved_join(self, actual: io::Result<JoinedChild>) -> String {
        match actual.and_then(|actual| self.observe_join(actual)) {
            Ok(joined) => joined.unresolved(),
            Err(error) => {
                let reason = format!("original producer local completion is unresolved: {error}");
                if let Ok(Some(scope)) = super::super::exec::protected_scope() {
                    scope.record_failure(&reason);
                }
                reason
            }
        }
    }

    /// Observe only this exact child's local join. The implicit execution
    /// remains borrowed: descendants can close both streams and keep running.
    pub(crate) fn observe_join(self, actual: JoinedChild) -> io::Result<JoinedProducer> {
        if Instant::now() >= self.deadline {
            return Err(io::Error::new(io::ErrorKind::TimedOut, "producer completion deadline"));
        }
        if actual.identity() != &self.launch {
            return Err(io::Error::other("producer completion belongs to another actual launch"));
        }
        // This establishes local facts only, not descendant retirement.
        if Instant::now() >= self.deadline {
            return Err(io::Error::new(io::ErrorKind::TimedOut, "producer completion deadline"));
        }
        Ok(JoinedProducer { borrower: self, _local: actual })
    }
}

/// The SAME outstanding borrower plus its exact local child observation.
/// There is deliberately no release/return operation or constructor from a
/// status, EOF, PID, marker or decoded acknowledgement.
#[must_use]
pub(crate) struct JoinedProducer {
    borrower: ProducerBorrow,
    _local: JoinedChild,
}

impl JoinedProducer {
    pub(crate) fn unresolved(self) -> String {
        let reason = if Instant::now() >= self.borrower.deadline {
            "original producer retirement deadline expired"
        } else {
            "original Host/subgroup/foreign-work retirement is unavailable; local child exit and EOF cannot return GNU execution"
        };
        // Failure is not authority. Permanently invalidate actual installed
        // dispatch aliases; dropping this retained borrower also latches the
        // SAME scheduler against every later implicit borrower.
        if let Ok(Some(scope)) = super::super::exec::protected_scope() {
            scope.record_failure(reason);
        }
        reason.to_owned()
    }
}

impl Drop for ProducerBorrow {
    fn drop(&mut self) {
        if let Some(mut state) = self.state.take() {
            // Keep the SAME original server in the process-wide owner and
            // permanently refuse future borrowers. Unlocking this data mutex
            // does not return an unresolved implicit execution to dispatch.
            state.producer_failed = true;
        }
    }
}

#[cfg(test)]
mod tests;
