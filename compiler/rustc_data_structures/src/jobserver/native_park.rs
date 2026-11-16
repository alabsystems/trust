// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Admission serialization, never proof of joined codegen or descendant closure.
use std::io;
use std::sync::{Arc, Weak};
use std::thread::ThreadId;

use parking_lot::{Mutex, MutexGuard};
use trust_build_cpu::{Lease, WorkerPause};

use super::runtime_v3::NativeV3;
use super::{ProxyData, ProxyShared};

#[derive(Clone, Copy)]
enum Phase {
    Running,
    Parked(u64),
    Poisoned,
}
pub(super) struct State {
    phase: Phase,
    generation: u64,
    proxies: Vec<Weak<ProxyShared>>,
}
pub(super) struct Registry {
    state: Mutex<State>,
}
fn refused() -> io::Error {
    io::Error::new(
        io::ErrorKind::PermissionDenied,
        "native compiler admission is parked or poisoned",
    )
}

pub(super) fn reserved(data: &ProxyData) -> io::Result<u16> {
    let active = data.active.as_ref().ok_or_else(refused)?;
    if data.workload.as_ref().is_some_and(|assignments| !assignments.matches(active)) {
        return Err(refused());
    }
    let count =
        active.values().try_fold(0u16, |n, value| n.checked_add(*value)).ok_or_else(refused)?;
    data.used.checked_sub(count).ok_or_else(refused)
}

impl Registry {
    pub(super) fn new() -> Arc<Self> {
        Arc::new(Self {
            state: Mutex::new(State { phase: Phase::Running, generation: 0, proxies: Vec::new() }),
        })
    }
    pub(super) fn enter(&self) -> io::Result<MutexGuard<'_, State>> {
        let state = self.state.lock();
        if !matches!(state.phase, Phase::Running) {
            return Err(refused());
        }
        Ok(state)
    }
    // Asynchronous failures can arrive after their core Attempt dropped,
    // including during a legitimate park. Latch them under the same lock and
    // wake every waiter; never panic the only helper and strand its requests.
    pub(super) fn callback(&self, failed: bool) -> Option<MutexGuard<'_, State>> {
        let mut state = self.state.lock();
        if failed || !matches!(state.phase, Phase::Running) {
            Self::poison_locked(&mut state);
            return None;
        }
        Some(state)
    }
    pub(super) fn register(&self, proxy: &Arc<ProxyShared>) -> io::Result<()> {
        self.enter()?.proxies.push(Arc::downgrade(proxy));
        Ok(())
    }
    fn eligible(state: &mut State, caller: ThreadId) -> io::Result<bool> {
        state.proxies.retain(|proxy| proxy.strong_count() != 0);
        for proxy in state.proxies.iter().filter_map(Weak::upgrade) {
            let data = proxy.data.lock();
            if data.error.is_some() {
                return Err(refused());
            }
            if data.pending != 0
                || reserved(&data)? != 0
                || !data.tokens.is_empty()
                || data.active.as_ref().ok_or_else(refused)?.keys().any(|id| *id != caller)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn poison_locked(state: &mut State) {
        state.phase = Phase::Poisoned;
        for proxy in state.proxies.iter().filter_map(Weak::upgrade) {
            let mut data = proxy.data.lock();
            data.error = Some("native compiler admission is poisoned".into());
            proxy.wake_pending.notify_all();
        }
    }
    fn poison(&self) {
        Self::poison_locked(&mut self.state.lock());
    }
}

/// Exclusive logical park after the caller separately joined its codegen work.
/// This retains the original implicit CPU; it never allocates another credit.
#[must_use]
pub struct CompilerPause {
    owner: Option<Arc<NativeV3>>,
    extra: Option<WorkerPause>,
    generation: u64,
}
impl CompilerPause {
    pub(super) fn acquire(owner: &Arc<NativeV3>) -> io::Result<Option<Self>> {
        let mut state = owner.registry().enter()?;
        match Registry::eligible(&mut state, std::thread::current().id()) {
            Ok(false) => return Ok(None),
            Err(error) => {
                Registry::poison_locked(&mut state);
                return Err(error);
            }
            Ok(true) => {}
        }
        let Some(generation) = state.generation.checked_add(1) else {
            Registry::poison_locked(&mut state);
            return Err(refused());
        };
        // Registry -> proxy data (above) -> core gate. A helper's already
        // acquired but unpublished offer is still counted by this core gate.
        let extra = match owner.workers().try_pause_extras() {
            Ok(Some(extra)) => extra,
            Ok(None) => return Ok(None),
            Err(error) => {
                Registry::poison_locked(&mut state);
                return Err(error);
            }
        };
        state.generation = generation;
        state.phase = Phase::Parked(generation);
        Ok(Some(Self { owner: Some(owner.clone()), extra: Some(extra), generation }))
    }
    /// Read-only original backing, not a new grant or a join witness.
    pub fn cpu(&self) -> &Arc<Lease> {
        self.owner.as_ref().expect("consumed compiler pause").workers().implicit()
    }
    /// Call only after the owner received positive authenticated host return.
    /// This method does not itself authenticate that external receipt.
    pub fn resume(mut self) -> io::Result<()> {
        let owner = self.owner.as_ref().ok_or_else(refused)?;
        let mut state = owner.registry().state.lock();
        if !matches!(state.phase, Phase::Parked(n) if n == self.generation) {
            Registry::poison_locked(&mut state);
            return Err(refused());
        }
        let extra = self.extra.take().ok_or_else(refused)?;
        if let Err(error) = extra.resume() {
            Registry::poison_locked(&mut state);
            return Err(error);
        }
        state.phase = Phase::Running;
        drop(state);
        drop(self.owner.take());
        Ok(())
    }
}
impl Drop for CompilerPause {
    fn drop(&mut self) {
        if let Some(owner) = self.owner.take() {
            owner.registry().poison();
            // Dropping the core pause poisons extra admission. Retain original
            // native custody/lifeline through process exit on unresolved loan.
            drop(self.extra.take());
            std::mem::forget(owner);
        }
    }
}

// Trust: the private Fixed compiler owns its primary in the original native
// Root. Admission exclusion reuses this same registry plus every actual local
// GNU helper/offer barrier; there is no WorkerClient or synthetic CPU Lease.
#[must_use]
pub struct BootstrapCompilerPause {
    owner: Option<Arc<super::BootstrapFixed>>,
    extra: Option<jobserver_utils::quiescence::Pause>,
    generation: u64,
}
impl BootstrapCompilerPause {
    pub(super) fn acquire(owner: &Arc<super::BootstrapFixed>) -> io::Result<Option<Self>> {
        let mut state = owner.registry().enter()?;
        match Registry::eligible(&mut state, std::thread::current().id()) {
            Ok(false) => return Ok(None),
            Err(error) => {
                Registry::poison_locked(&mut state);
                return Err(error);
            }
            Ok(true) => {}
        }
        let Some(generation) = state.generation.checked_add(1) else {
            Registry::poison_locked(&mut state);
            return Err(refused());
        };
        let extra = match owner.extras().try_pause() {
            Ok(Some(extra)) => extra,
            Ok(None) => return Ok(None),
            Err(error) => {
                Registry::poison_locked(&mut state);
                return Err(error);
            }
        };
        state.generation = generation;
        state.phase = Phase::Parked(generation);
        Ok(Some(Self { owner: Some(Arc::clone(owner)), extra: Some(extra), generation }))
    }
    pub fn generation(&self) -> u64 {
        self.generation
    }
    pub fn compiler(&self) -> &Arc<super::BootstrapFixed> {
        self.owner.as_ref().expect("consumed Fixed pause")
    }
    pub fn resume(
        self,
        closed: trust_resource_controller::client::bootstrap_graph::ClosedLinker,
    ) -> io::Result<trust_resource_controller::Status> {
        if !closed.belongs_to(self.compiler().member(), self.generation) {
            return Err(refused());
        }
        let status = closed.status().clone();
        self.resume_local()?;
        Ok(status)
    }
    pub fn cancel_unoffered(
        self,
        unlent: trust_resource_controller::client::bootstrap_graph::UnlentLinker,
    ) -> io::Result<()> {
        if !unlent.belongs_to(self.compiler().member(), self.generation) {
            return Err(refused());
        }
        let bound = self.compiler().member().original_deadline()?;
        self.compiler().member().check_current(
            bound.min(std::time::Instant::now() + std::time::Duration::from_secs(8)),
        )?;
        self.resume_local()
    }
    fn resume_local(mut self) -> io::Result<()> {
        let owner = self.owner.as_ref().ok_or_else(refused)?;
        if std::time::Instant::now() >= owner.member().original_deadline()? {
            return Err(refused());
        }
        let mut state = owner.registry().state.lock();
        if !matches!(state.phase,Phase::Parked(generation) if generation==self.generation) {
            Registry::poison_locked(&mut state);
            return Err(refused());
        }
        if let Err(error) = self.extra.take().ok_or_else(refused)?.resume() {
            Registry::poison_locked(&mut state);
            return Err(error);
        }
        state.phase = Phase::Running;
        drop(state);
        drop(self.owner.take());
        Ok(())
    }
}
impl Drop for BootstrapCompilerPause {
    fn drop(&mut self) {
        if let Some(owner) = self.owner.take() {
            owner.registry().poison();
            drop(self.extra.take());
            std::mem::forget(owner);
        }
    }
}

#[cfg(test)]
#[path = "native_park/tests.rs"]
mod tests;
