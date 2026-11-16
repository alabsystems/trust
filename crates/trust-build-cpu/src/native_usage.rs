// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::collections::BTreeMap;
use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use crate::{Owner, Pool, SlotState, process_cpu};

/// Sample only explicit kernel-lease owner identities, never a truncated
/// process listing or an assumption that each held lease is a busy core.
pub struct NativeUsage {
    shared: Arc<Shared>,
    thread: Option<JoinHandle<()>>,
}

struct Shared {
    value: Mutex<Option<(Instant, u64, Option<u64>)>>,
    stop: AtomicBool,
    wake: (Mutex<()>, Condvar),
}

#[derive(Default)]
struct State {
    previous: BTreeMap<(u32, u64), (u64, Instant)>,
    sampled: Option<Instant>,
    millicores: u64,
}

impl NativeUsage {
    /// Observe a pool without changing its capacity or ownership.
    pub fn new(pool: Pool) -> io::Result<Self> {
        let shared = Arc::new(Shared {
            value: Mutex::new(None),
            stop: AtomicBool::new(false),
            wake: (Mutex::new(()), Condvar::new()),
        });
        let worker = Arc::clone(&shared);
        let thread = thread::Builder::new().name("trust-native-cpu".into()).spawn(move || {
            let mut state = State::default();
            while !worker.stop.load(Ordering::Acquire) {
                let now = Instant::now();
                let cpu = pool.snapshot().ok().map_or(0, |slots| {
                    let owners = slots.into_iter().filter_map(|slot| match slot {
                        SlotState::Held { reported_owner: Some(owner), .. } => Some(owner),
                        _ => None,
                    });
                    sample(&mut state, owners, now, process_cpu::read)
                });
                let memory = crate::available_memory();
                *worker.value.lock().unwrap_or_else(std::sync::PoisonError::into_inner) =
                    Some((now, cpu, memory));
                let wake_lock = &worker.wake.0;
                let guard = wake_lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
                if !worker.stop.load(Ordering::Acquire) {
                    drop(worker.wake.1.wait_timeout(guard, Duration::from_millis(500)));
                }
            }
        })?;
        Ok(Self { shared, thread: Some(thread) })
    }

    /// Return recent owned CPU usage. Missing/birth-mismatched processes add
    /// zero rather than overstating native CPU and concealing external load.
    /// This is advisory telemetry; the pool's kernel leases remain authority.
    pub fn millicores(&self) -> u64 {
        self.shared
            .value
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .filter(|(when, _, _)| when.elapsed() <= Duration::from_secs(3))
            .map_or(0, |(_, cpu, _)| cpu)
    }

    /// A cached conservative kernel memory reading, for pre-monitor fallback.
    /// This performs no system query while a caller holds an admission lock.
    pub fn available_memory(&self) -> Option<u64> {
        self.shared
            .value
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .filter(|(when, _, _)| when.elapsed() <= Duration::from_secs(3))
            .and_then(|(_, _, memory)| memory)
    }
}

impl Drop for NativeUsage {
    fn drop(&mut self) {
        self.shared.stop.store(true, Ordering::Release);
        self.shared.wake.1.notify_all();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn sample(
    state: &mut State,
    owners: impl IntoIterator<Item = Owner>,
    now: Instant,
    mut read: impl FnMut(u32) -> Option<process_cpu::ProcessCpu>,
) -> u64 {
    if state
        .sampled
        .is_some_and(|last| now.saturating_duration_since(last) < Duration::from_millis(500))
    {
        return state.millicores;
    }
    let mut credits = BTreeMap::<_, u64>::new();
    for owner in owners {
        if let Some(birth) = owner.birth {
            let count = credits.entry((owner.pid, birth)).or_default();
            *count = count.saturating_add(1);
        }
    }
    let mut previous = BTreeMap::new();
    let mut total = 0u64;
    for ((pid, birth), credits) in credits {
        let Some(current) = read(pid).filter(|value| value.owner.birth == Some(birth)) else {
            continue;
        };
        if let Some(&(cpu, when)) = state.previous.get(&(pid, birth)) {
            let elapsed = now.saturating_duration_since(when);
            if elapsed <= Duration::from_secs(3)
                && !elapsed.is_zero()
                && let Some(delta) = current.total_ns.checked_sub(cpu)
            {
                let used = u128::from(delta).saturating_mul(1000) / elapsed.as_nanos();
                // Uncredited threads in an owner process remain external CPU
                // pressure. Held credits bound attribution, never imply usage.
                let owned =
                    u64::try_from(used).unwrap_or(u64::MAX).min(credits.saturating_mul(1000));
                total = total.saturating_add(owned);
            }
        }
        previous.insert((pid, birth), (current.total_ns, now));
    }
    state.previous = previous;
    state.sampled = Some(now);
    state.millicores = total;
    total
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deduplicates_workers_and_rejects_pid_reuse_or_missing_birth() {
        let start = Instant::now();
        let owner = Owner { pid: 42, birth: Some(7) };
        let mut state = State::default();
        assert_eq!(
            sample(&mut state, [owner, owner], start, |_| Some(process_cpu::ProcessCpu {
                owner,
                total_ns: 100
            })),
            0
        );
        assert_eq!(
            sample(&mut state, [owner, owner], start + Duration::from_secs(1), |_| Some(
                process_cpu::ProcessCpu { owner, total_ns: 1_000_000_100 }
            )),
            1000
        );
        assert_eq!(
            sample(&mut state, [owner], start + Duration::from_secs(2), |_| Some(
                process_cpu::ProcessCpu {
                    owner: Owner { pid: 42, birth: Some(8) },
                    total_ns: 9_000_000_000
                }
            )),
            0
        );
        assert_eq!(
            sample(
                &mut state,
                [Owner { pid: 42, birth: None }],
                start + Duration::from_secs(3),
                |_| panic!("unknown birth must not be queried")
            ),
            0
        );
    }

    #[test]
    fn attributes_only_measured_cpu_backed_by_held_credits() {
        let start = Instant::now();
        let owner = Owner { pid: 42, birth: Some(7) };
        for (credits, measured, expected) in
            [(1, 4_000, 1_000), (4, 4_000, 4_000), (4, 500, 500), (4, 0, 0)]
        {
            let mut state = State::default();
            let owners = || std::iter::repeat_n(owner, credits);
            sample(&mut state, owners(), start, |_| {
                Some(process_cpu::ProcessCpu { owner, total_ns: 0 })
            });
            assert_eq!(
                sample(&mut state, owners(), start + Duration::from_secs(1), |_| Some(
                    process_cpu::ProcessCpu { owner, total_ns: measured * 1_000_000 }
                )),
                expected
            );
        }
    }
}
