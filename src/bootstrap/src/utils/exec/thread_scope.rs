//! One lexical native owner for Bootstrap's borrowed workers. Standalone uses
//! its original std scope; installed protected mode cannot take that fallback.
//! Worker count and real CPU/memory funding remain the original caller's job.

use std::{io, thread};

pub(crate) enum Threads<'scope, 'env> {
    Standalone(&'scope thread::Scope<'scope, 'env>),
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    Protected(build_helper::trust_repo_lock::management::ScopedThreads<'scope, 'env>),
}

pub(crate) enum Worker<'scope, T> {
    Standalone(thread::ScopedJoinHandle<'scope, T>),
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    Protected(build_helper::trust_repo_lock::management::ScopedThread<'scope, T>),
}

pub(crate) fn scoped_threads<'env, F, T>(work: F) -> io::Result<T>
where
    F: for<'scope> FnOnce(Threads<'scope, 'env>) -> T,
{
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    if let Some(scope) = super::protected_scope()? {
        return scope.scoped_threads(|native| work(Threads::Protected(native)));
    }
    Ok(thread::scope(|native| work(Threads::Standalone(native))))
}

impl<'scope, 'env> Threads<'scope, 'env> {
    pub(crate) fn spawn<F, T>(&self, work: F) -> io::Result<Worker<'scope, T>>
    where
        F: FnOnce() -> T + Send + 'scope,
        T: Send + 'scope,
    {
        match self {
            Self::Standalone(scope) => Ok(Worker::Standalone(scope.spawn(work))),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            Self::Protected(scope) => scope.spawn(work).map(Worker::Protected),
        }
    }
}

impl<T> Worker<'_, T> {
    // Some original std scopes intentionally rely on automatic lexical joins.
    #[expect(dead_code, reason = "available to the original native scoped-worker caller")]
    pub(crate) fn join(self) -> thread::Result<T> {
        match self {
            Self::Standalone(worker) => worker.join(),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            Self::Protected(worker) => worker.join(),
        }
    }
}
