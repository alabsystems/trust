//! Admission exclusion for a cooperative owner's already-quiescent phase.

use std::io;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

use crate::invalid;

#[derive(Clone, Copy)]
enum Phase {
    Running,
    Paused(u64),
    Poisoned,
}

mod decision;

struct State {
    phase: Phase,
    acquiring: usize,
    credits: usize,
    generation: u64,
}

pub(super) struct Gate {
    state: Mutex<State>,
}

impl Gate {
    pub(super) fn new() -> Arc<Self> {
        Arc::new(Self {
            state: Mutex::new(State {
                phase: Phase::Running,
                acquiring: 0,
                credits: 0,
                generation: 0,
            }),
        })
    }

    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    pub(super) fn running(&self) -> bool {
        matches!(self.lock().phase, Phase::Running)
    }

    // Only an uncertain native-host workload settlement poisons from outside
    // this module; without that feature nothing but the unit tests calls it.
    #[cfg(any(test, all(feature = "native-host", any(target_os = "linux", target_os = "macos"))))]
    pub(super) fn poison(&self) {
        self.lock().phase = Phase::Poisoned;
    }

    pub(super) fn begin(self: &Arc<Self>) -> io::Result<Option<Attempt>> {
        let mut state = self.lock();
        match state.phase {
            Phase::Paused(_) => return Ok(None),
            Phase::Poisoned => return Err(refused()),
            Phase::Running => {}
        }
        state.acquiring = state.acquiring.checked_add(1).ok_or_else(refused)?;
        Ok(Some(Attempt { gate: Arc::clone(self), active: true }))
    }

    pub(super) fn pause(self: &Arc<Self>) -> io::Result<Option<WorkerPause>> {
        let mut state = self.lock();
        if matches!(state.phase, Phase::Poisoned) {
            return Err(refused());
        }
        if !decision::may_pause_extra_workers(
            matches!(state.phase, Phase::Running),
            state.acquiring == 0,
            state.credits == 0,
        ) {
            return Ok(None);
        }
        state.generation = state.generation.checked_add(1).ok_or_else(refused)?;
        let generation = state.generation;
        state.phase = Phase::Paused(generation);
        Ok(Some(WorkerPause { gate: Some(Arc::clone(self)), generation }))
    }
}

fn refused() -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, "worker admission gate is poisoned")
}

pub(super) struct Attempt {
    gate: Arc<Gate>,
    active: bool,
}

impl Attempt {
    pub(super) fn publish(mut self) -> io::Result<Permit> {
        let mut state = self.gate.lock();
        if state.acquiring == 0 || !matches!(state.phase, Phase::Running) {
            state.phase = Phase::Poisoned;
            return Err(refused());
        }
        state.acquiring -= 1;
        self.active = false;
        state.credits = state.credits.checked_add(1).ok_or_else(refused)?;
        Ok(Permit { gate: Arc::clone(&self.gate) })
    }
}

impl Drop for Attempt {
    fn drop(&mut self) {
        if self.active {
            let mut state = self.gate.lock();
            if state.acquiring == 0 {
                state.phase = Phase::Poisoned;
            } else {
                state.acquiring -= 1;
            }
        }
    }
}

pub(super) struct Permit {
    gate: Arc<Gate>,
}

impl std::fmt::Debug for Permit {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("WorkerAdmissionPermit")
    }
}

impl Permit {
    #[cfg(any(test, all(feature = "native-host", any(target_os = "linux", target_os = "macos"))))]
    pub(super) fn poison(&self) {
        self.gate.poison();
    }

    pub(super) fn commit(&self, ticket: &AtomicU8) -> bool {
        let state = self.gate.lock();
        matches!(state.phase, Phase::Running)
            && ticket
                .compare_exchange(
                    super::OFFERED,
                    super::COMMITTED,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                )
                .is_ok()
    }
}

impl Drop for Permit {
    fn drop(&mut self) {
        let mut state = self.gate.lock();
        if state.credits == 0 {
            state.phase = Phase::Poisoned;
        } else {
            state.credits -= 1;
        }
    }
}

/// Excludes extra worker admission until an execution owner returns its loan.
///
/// This does not release any implicit CPU descriptor, park its executing thread,
/// prove descendant closure, or create a host loan. The caller must separately
/// establish compiler quiescence and exclude implicit dispatch. Dropping this
/// value without explicit resume permanently poisons this client's extra
/// admission rather than silently returning a potentially outstanding unit.
#[must_use]
pub struct WorkerPause {
    gate: Option<Arc<Gate>>,
    generation: u64,
}

impl WorkerPause {
    /// Resume only after the execution owner positively receives its loan back.
    /// This method cannot authenticate that external receipt on its own.
    pub fn resume(mut self) -> io::Result<()> {
        let gate = self.gate.as_ref().ok_or_else(|| invalid("worker pause already consumed"))?;
        let mut state = gate.lock();
        if !matches!(state.phase, Phase::Paused(generation) if generation == self.generation)
            || state.acquiring != 0
            || state.credits != 0
        {
            state.phase = Phase::Poisoned;
            return Err(refused());
        }
        state.phase = Phase::Running;
        drop(state);
        self.gate = None;
        Ok(())
    }
}

impl Drop for WorkerPause {
    fn drop(&mut self) {
        if let Some(gate) = &self.gate {
            let mut state = gate.lock();
            if matches!(state.phase, Phase::Paused(generation) if generation == self.generation) {
                state.phase = Phase::Poisoned;
            }
        }
    }
}

#[cfg(test)]
mod tests;
