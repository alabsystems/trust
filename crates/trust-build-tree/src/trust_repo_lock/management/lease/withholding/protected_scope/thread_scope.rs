//! The actual lexical std::thread::Scope owner for borrowed workers.
//! No caller can set its private joined state or supply a completion callback.
//! This adds no CPU/memory admission: the caller still funds actual worker work.

use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::{io, thread};

use super::{Inner, Phase, ScopeDispatch, before, pause};

pub(super) struct NativeScope {
    joined: AtomicBool,
}
impl NativeScope {
    pub(super) fn joined(&self) -> bool {
        self.joined.load(Ordering::Acquire)
    }
}

/// Holds the ACTUAL standard-library scope. Passed by value into the HRTB
/// callback; a local proxy borrow never pretends to live for the native scope.
/// No raw scope, arbitrary completion callback or release is exported.
pub struct ScopedThreads<'scope, 'env> {
    native: &'scope thread::Scope<'scope, 'env>,
    inner: Arc<Inner>,
}

pub struct ScopedThread<'scope, T> {
    native: thread::ScopedJoinHandle<'scope, T>,
    inner: Arc<Inner>,
}

impl ScopeDispatch {
    /// Register BEFORE invoking the actual std Scope. Its original lexical
    /// owner joins ALL borrowed workers on return or unwind. A local joined
    /// bookend cannot return while this actual owner is active.
    pub fn scoped_threads<'env, F, T>(&self, work: F) -> io::Result<T>
    where
        F: for<'scope> FnOnce(ScopedThreads<'scope, 'env>) -> T,
    {
        self.check_current()?;
        let region = Arc::new(NativeScope { joined: AtomicBool::new(false) });
        {
            let mut state = self.inner.state()?;
            if state.phase != Phase::Open {
                return Err(io::Error::other("native scope dispatch sealed"));
            }
            before(self.inner.deadline)?;
            state.native_scopes.push(Arc::clone(&region));
        }
        let inner = Arc::clone(&self.inner);
        let result = catch_unwind(AssertUnwindSafe(move || {
            thread::scope(move |native| work(ScopedThreads { native, inner }))
        }));
        // std Scope itself has joined, including during unwind. Panic and late
        // return remain permanently failed observations of this SAME scope.
        region.joined.store(true, Ordering::Release);
        match result {
            Ok(value) => {
                self.inner.check()?;
                Ok(value)
            }
            Err(payload) => {
                self.inner.fail("original native thread scope panicked");
                resume_unwind(payload)
            }
        }
    }
}

impl<'scope, 'env> ScopedThreads<'scope, 'env> {
    /// Same original seal gate covers actual thread delivery. This restriction
    /// and retained join owner do not acquire CPU, memory or a new scheduler.
    pub fn spawn<F, T>(&self, work: F) -> io::Result<ScopedThread<'scope, T>>
    where
        F: FnOnce() -> T + Send + 'scope,
        T: Send + 'scope,
    {
        self.inner.check()?;
        let state = self.inner.state()?;
        if state.phase != Phase::Open {
            return Err(io::Error::other("native worker dispatch sealed"));
        }
        before(self.inner.deadline)?;
        let native = self.native.spawn(work);
        drop(state);
        Ok(ScopedThread { native, inner: Arc::clone(&self.inner) })
    }
}

impl<T> ScopedThread<'_, T> {
    pub fn join(self) -> thread::Result<T> {
        while !self.native.is_finished() {
            if let Err(error) = pause(self.inner.deadline) {
                self.inner.fail(error.to_string());
                // The actual lexical Scope still owns this thread and joins
                // it. Dropping a timed-out wrapper cannot detach a borrower.
                return Err(Box::new(error));
            }
        }
        match self.native.join() {
            Ok(value) => match self.inner.check() {
                Ok(()) => Ok(value),
                Err(error) => Err(Box::new(error)),
            },
            Err(payload) => {
                self.inner.fail("original scoped worker panicked");
                Err(payload)
            }
        }
    }
}
