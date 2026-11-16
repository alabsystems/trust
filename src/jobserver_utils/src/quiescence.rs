//! A restriction-only barrier around an existing GNU client. This creates no
//! pool, implicit credit, Root, CPU lease or native execution authority. Higher
//! owners must authenticate their original entitlement and actual SDK joins.
use std::collections::BTreeMap;
use std::io;
use std::sync::{Arc, Mutex, MutexGuard};

#[derive(Clone, Copy)]
enum Phase {
    Running,
    Paused(u64),
    Poisoned,
}
struct State {
    phase: Phase,
    generation: u64,
    next_helper: u64,
    helpers: BTreeMap<u64, u64>, // Actual requested-but-unpublished population.
    held: u64,
    callbacks: u64,
}
fn refused() -> io::Error {
    io::Error::other("original GNU admission is paused or poisoned")
}
fn running(state: &State) -> io::Result<()> {
    if matches!(state.phase, Phase::Running) { Ok(()) } else { Err(refused()) }
}

#[derive(Clone)]
pub struct Client {
    original: jobserver::Client,
    state: Arc<Mutex<State>>,
}
impl Client {
    /// Wrap this actual caller-owned client without creating or moving credits.
    /// This alone cannot authorize any compiler, primary or native child.
    pub fn new(original: jobserver::Client) -> Self {
        Self {
            original,
            state: Arc::new(Mutex::new(State {
                phase: Phase::Running,
                generation: 0,
                next_helper: 1,
                helpers: BTreeMap::new(),
                held: 0,
                callbacks: 0,
            })),
        }
    }
    fn lock(&self) -> io::Result<MutexGuard<'_, State>> {
        self.state.lock().map_err(|_| refused())
    }
    pub fn try_acquire(&self) -> io::Result<Option<Acquired>> {
        let mut state = self.lock()?;
        running(&state)?;
        let Some(original) = self.original.try_acquire()? else {
            return Ok(None);
        };
        state.held = state.held.checked_add(1).ok_or_else(refused)?;
        Ok(Some(Acquired { original: Some(original), state: Arc::clone(&self.state) }))
    }
    pub fn into_helper_thread(
        self,
        mut callback: impl FnMut(io::Result<Acquired>) + Send + 'static,
    ) -> io::Result<HelperThread> {
        let id = {
            let mut state = self.lock()?;
            running(&state)?;
            let id = state.next_helper;
            state.next_helper = id.checked_add(1).ok_or_else(refused)?;
            state.helpers.insert(id, 0);
            id
        };
        let owner = Arc::clone(&self.state);
        let actual = self.original.clone().into_helper_thread(move |token| {
            let result = (|| {
                let mut state = owner.lock().map_err(|_| refused())?;
                let pending = state.helpers.get_mut(&id).ok_or_else(refused)?;
                *pending = pending.checked_sub(1).ok_or_else(refused)?;
                state.callbacks = state.callbacks.checked_add(1).ok_or_else(refused)?;
                let token = match token {
                    Ok(original) if matches!(state.phase, Phase::Running) => {
                        state.held = state.held.checked_add(1).ok_or_else(refused)?;
                        Ok(Acquired { original: Some(original), state: Arc::clone(&owner) })
                    }
                    Ok(_) => {
                        state.phase = Phase::Poisoned;
                        Err(refused())
                    }
                    Err(error) => {
                        state.phase = Phase::Poisoned;
                        Err(error)
                    }
                };
                drop(state);
                Ok((Callback { state: Arc::clone(&owner) }, token))
            })();
            match result {
                Ok((_scope, token)) => callback(token),
                Err(error) => {
                    if let Ok(mut state) = owner.lock() {
                        state.phase = Phase::Poisoned;
                    }
                    callback(Err(error));
                }
            }
        });
        match actual {
            Ok(actual) => Ok(HelperThread { original: Some(actual), owner: self, id }),
            Err(error) => {
                self.lock()?.helpers.remove(&id);
                Err(error)
            }
        }
    }
    /// Restrict new acquisition only when every actual request, unpublished
    /// offer, callback and held supplemental GNU credit has settled. The caller
    /// separately proves SDK work joined and retains its real original primary.
    pub fn try_pause(&self) -> io::Result<Option<Pause>> {
        let mut state = self.lock()?;
        running(&state)?;
        if state.held != 0
            || state.callbacks != 0
            || state.helpers.values().any(|count| *count != 0)
        {
            return Ok(None);
        }
        let generation = state.generation.checked_add(1).ok_or_else(refused)?;
        state.generation = generation;
        state.phase = Phase::Paused(generation);
        Ok(Some(Pause { owner: self.clone(), generation, resumed: false }))
    }
}

pub struct Acquired {
    original: Option<jobserver::Acquired>,
    state: Arc<Mutex<State>>,
}
impl std::fmt::Debug for Acquired {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OriginalGnuCredit").finish_non_exhaustive()
    }
}
impl Acquired {
    pub fn commit(&self) -> bool {
        self.state.lock().is_ok_and(|state| matches!(state.phase, Phase::Running))
    }
}
impl Drop for Acquired {
    fn drop(&mut self) {
        let original = self.original.take();
        if let Ok(mut state) = self.state.lock() {
            // The real byte returns before the tracked held count clears.
            drop(original);
            match state.held.checked_sub(1) {
                Some(held) => state.held = held,
                None => state.phase = Phase::Poisoned,
            }
        } else {
            drop(original);
        }
    }
}
struct Callback {
    state: Arc<Mutex<State>>,
}
impl Drop for Callback {
    fn drop(&mut self) {
        if let Ok(mut state) = self.state.lock() {
            match state.callbacks.checked_sub(1) {
                Some(callbacks) => state.callbacks = callbacks,
                None => state.phase = Phase::Poisoned,
            }
            if std::thread::panicking() {
                state.phase = Phase::Poisoned;
            }
        }
    }
}

pub struct HelperThread {
    original: Option<jobserver::HelperThread>,
    owner: Client,
    id: u64,
}
impl HelperThread {
    pub fn request_token(&self) -> io::Result<()> {
        let mut state = self.owner.lock()?;
        self.request_locked(&mut state)
    }
    fn request_locked(&self, state: &mut State) -> io::Result<()> {
        running(state)?;
        let pending = state.helpers.get_mut(&self.id).ok_or_else(refused)?;
        *pending = pending.checked_add(1).ok_or_else(refused)?;
        self.original.as_ref().ok_or_else(refused)?.request_token();
        Ok(())
    }
    pub fn cancel_request(&self) -> io::Result<bool> {
        let mut state = self.owner.lock()?;
        let actual = self.original.as_ref().ok_or_else(refused)?;
        if !actual.cancel_request() {
            return Ok(false);
        }
        // Only the ACTUAL helper's cancellation acknowledgment can withdraw a
        // request. An already-reading helper keeps its pending publication.
        let pending = state.helpers.get_mut(&self.id).ok_or_else(refused)?;
        *pending = pending.checked_sub(1).ok_or_else(refused)?;
        Ok(true)
    }
    pub fn queued_requests(&self) -> usize {
        self.original.as_ref().map_or(0, jobserver::HelperThread::queued_requests)
    }
    fn join(&mut self) -> io::Result<()> {
        let Some(actual) = self.original.take() else {
            return Ok(());
        };
        // Never hold our gate during the actual join: its callback needs it.
        let result = actual.shutdown_blocking();
        let mut state = self.owner.lock()?;
        if result.is_ok() {
            // Unfetched requests may disappear only after this real join.
            state.helpers.remove(&self.id).ok_or_else(refused)?;
        } else {
            state.phase = Phase::Poisoned;
        }
        result
    }
    pub fn shutdown_blocking(mut self) -> io::Result<()> {
        self.join()
    }
}
impl Drop for HelperThread {
    fn drop(&mut self) {
        if self.join().is_err()
            && let Ok(mut state) = self.owner.lock()
        {
            state.phase = Phase::Poisoned;
        }
    }
}

#[must_use]
pub struct Pause {
    owner: Client,
    generation: u64,
    resumed: bool,
}
impl Pause {
    /// Restriction only. The higher compiler owner must FIRST consume its exact
    /// opaque native retired loan; this method cannot authenticate that closure.
    pub fn resume(mut self) -> io::Result<()> {
        let mut state = self.owner.lock()?;
        if !matches!(state.phase, Phase::Paused(generation) if generation == self.generation) {
            state.phase = Phase::Poisoned;
            return Err(refused());
        }
        state.phase = Phase::Running;
        self.resumed = true;
        Ok(())
    }
}
impl Drop for Pause {
    fn drop(&mut self) {
        if !self.resumed
            && let Ok(mut state) = self.owner.lock()
        {
            state.phase = Phase::Poisoned;
        }
    }
}
#[cfg(test)]
mod tests;
