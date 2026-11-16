// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Persistent large-stack workers for Clean elaboration and kernel checks.
//!
//! The Clean lanes cache their elaborated preludes (`Temporal.lean`,
//! `FiniteModel.lean`, the EvalIR + temporal frontiers) per worker under the
//! current cache policy. Pinned Clean's FileContext and Environment are now
//! Send + Sync; global sharing remains a separate optimization. A worker-local
//! cache is only a cache if the thread
//! outlives the call: the lanes used to spawn a fresh 64 MiB thread for every
//! call, which would rebuild the finite-model prelude on each one (measured in
//! a debug test binary: ~46 s per cold build on an idle machine, ~156 s under
//! a parallel test run, against ~2-4 ms for a warm clone).
//!
//! This pool keeps those threads. A call takes an idle worker (the most
//! recently used one, whose caches are warm) or, when none is idle, spawns a
//! new one — so concurrent and nested calls never wait on each other, and the
//! number of workers is the peak concurrency, each building its caches once.
//!
//! Nothing a job computes crosses to the next job except through those caches,
//! and the caches hand out owned clones only. A job that panics retires its
//! worker instead of returning it to the pool, so a thread whose thread-local
//! state a panic may have left half-updated is never reused.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Mutex;
use std::sync::mpsc::{Receiver, Sender, channel, sync_channel};

/// Stack for every worker: the largest of the three lanes' former per-call
/// threads (all three were 64 MiB).
pub(crate) const KERNEL_WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;

type Job = Box<dyn FnOnce() + Send + 'static>;

/// Idle workers, most recently used last. Holding a worker's job sender is
/// what keeps it alive: dropping the sender ends its receive loop.
static IDLE: Mutex<Vec<Sender<Job>>> = Mutex::new(Vec::new());

/// Why a kernel-worker call produced no value.
#[derive(Debug)]
pub(crate) enum KernelWorkerError {
    /// No idle worker existed and a new one could not be started.
    Spawn(std::io::Error),
    /// The job panicked; its worker has been retired.
    Panicked,
}

fn idle_workers() -> std::sync::MutexGuard<'static, Vec<Sender<Job>>> {
    // The critical sections below only push/pop a sender; a poisoned lock
    // cannot hold a half-updated vector.
    IDLE.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn spawn_worker() -> Result<Sender<Job>, KernelWorkerError> {
    let (jobs, receiver): (Sender<Job>, Receiver<Job>) = channel();
    std::thread::Builder::new()
        .name("trust-clean-kernel-worker".to_owned())
        .stack_size(KERNEL_WORKER_STACK_BYTES)
        .spawn(move || {
            for job in receiver {
                job();
            }
        })
        .map_err(KernelWorkerError::Spawn)?;
    Ok(jobs)
}

/// Run `operation` on a persistent large-stack worker and wait for it.
pub(crate) fn run_on_kernel_worker<T, F>(operation: F) -> Result<T, KernelWorkerError>
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    let (result_sender, result) = sync_channel(1);
    let mut job: Job = Box::new(move || {
        // A send failure means the caller is gone; there is nobody to tell.
        let _ = result_sender.send(catch_unwind(AssertUnwindSafe(operation)));
    });
    let worker = loop {
        let candidate = idle_workers().pop();
        let worker = match candidate {
            Some(worker) => worker,
            None => spawn_worker()?,
        };
        match worker.send(job) {
            Ok(()) => break worker,
            // That worker's thread is gone; take the job back and try again.
            Err(returned) => job = returned.0,
        }
    };
    match result.recv() {
        Ok(Ok(value)) => {
            let mut idle = idle_workers();
            let cap = std::thread::available_parallelism().map_or(1, std::num::NonZero::get);
            if idle.len() < cap {
                idle.push(worker);
            }
            Ok(value)
        }
        // Dropping `worker` here retires the thread whose job panicked.
        Ok(Err(_)) | Err(_) => Err(KernelWorkerError::Panicked),
    }
}

/// Test probe: `true` when the calling thread has run this probe before.
///
/// A lane whose per-thread prelude cache is actually reused must report `true`
/// for some of a run of sequential jobs; a lane that spawns a thread per call
/// reports `false` every time.
#[cfg(test)]
pub(crate) fn probe_ran_on_this_thread_before() -> bool {
    thread_local! {
        static RAN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    }
    RAN.with(|ran| ran.replace(true))
}

/// Run `probe_ran_on_this_thread_before` as eight sequential jobs through
/// `lane` and report whether any of them landed on a reused thread.
#[cfg(test)]
pub(crate) fn lane_reuses_a_worker<E: std::fmt::Debug>(lane: impl Fn() -> Result<bool, E>) -> bool {
    (0..8).map(|_| lane().expect("probe job runs")).fold(false, |seen, reused| seen | reused)
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;

    thread_local! {
        static JOBS_ON_THIS_THREAD: Cell<usize> = const { Cell::new(0) };
    }

    fn count_job() -> (std::thread::ThreadId, usize) {
        JOBS_ON_THIS_THREAD.with(|jobs| jobs.set(jobs.get() + 1));
        (std::thread::current().id(), JOBS_ON_THIS_THREAD.with(Cell::get))
    }

    /// The point of the pool: sequential calls from one caller land on a
    /// thread that has already run a job, so its thread-local caches are warm.
    /// Other tests share the pool, so this asserts reuse, not a fixed thread.
    #[test]
    fn sequential_jobs_reuse_a_warm_worker_with_a_large_stack() {
        let mut reused = false;
        for _ in 0..8 {
            let (_, jobs) = run_on_kernel_worker(count_job).expect("job runs");
            reused |= jobs > 1;
        }
        assert!(reused, "eight sequential jobs never reused a worker thread");

        // A recursion that needs well over a default 2 MiB/8 MiB stack.
        fn depth(n: usize) -> usize {
            let pad = std::hint::black_box([0u8; 1024]);
            if n == 0 { usize::from(pad[0]) } else { 1 + depth(n - 1) }
        }
        let reached = run_on_kernel_worker(|| depth(16 * 1024)).expect("deep job runs");
        assert_eq!(reached, 16 * 1024);
    }

    #[test]
    fn nested_jobs_do_not_deadlock_and_panics_retire_the_worker() {
        let nested = run_on_kernel_worker(|| {
            let outer = std::thread::current().id();
            let inner = run_on_kernel_worker(|| std::thread::current().id()).expect("inner runs");
            (outer, inner)
        })
        .expect("outer runs");
        assert_ne!(nested.0, nested.1, "a nested job must get its own worker");

        let (report, reported) = std::sync::mpsc::channel();
        let panicked = run_on_kernel_worker(move || {
            report.send(std::thread::current().id()).expect("test receiver alive");
            if std::hint::black_box(true) {
                panic!("deliberate kernel-worker panic");
            }
        });
        assert!(matches!(panicked, Err(KernelWorkerError::Panicked)));
        let retired = reported.recv().expect("panicking job reported its thread");
        // The pool still serves jobs, and never again on the retired thread.
        for _ in 0..8 {
            let served = run_on_kernel_worker(|| std::thread::current().id()).expect("job runs");
            assert_ne!(served, retired, "a worker whose job panicked was reused");
        }
    }
}
