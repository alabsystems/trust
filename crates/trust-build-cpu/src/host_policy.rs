// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::num::NonZeroU64;
use std::sync::Arc;
use std::time::Instant;

use crate::{Monitor, Observation, Pool, SlotState};

/// Cached bounded reads only: implementations must not perform RPC, OS process
/// scans or recursively lock the native pool inside admission transactions.
pub trait ObservationSource: Send + Sync {
    /// Last original observation plus independent conservative claimable memory.
    fn latest(&self) -> Option<(Observation, u64)>;
    /// A previously working source going stale must pause fresh work.
    fn ever_observed(&self) -> bool;
}
impl ObservationSource for Monitor {
    fn latest(&self) -> Option<(Observation, u64)> {
        Monitor::latest(self)
    }
    fn ever_observed(&self) -> bool {
        Monitor::ever_observed(self)
    }
}

/// Connect cached live monitoring to the shared pool's admission veto.
///
/// This does not mint CPU capacity or turn observations into reservations.
/// Every admitted worker must still acquire its own actual pool lease.
pub struct HostPolicy {
    pool: Pool,
    monitor: Option<Arc<dyn ObservationSource>>,
    required: bool,
    per_worker: NonZeroU64,
    reserve: u64,
    fallback_memory: Arc<dyn Fn() -> Option<u64> + Send + Sync>,
    native_cpu: Arc<dyn Fn() -> u64 + Send + Sync>,
}

impl HostPolicy {
    /// Use a monitor when available. Before any successful observation, a
    /// kernel CPU/memory reading may permit a bounded global worker budget on
    /// machines without aterm. A previously working monitor that becomes
    /// stale/unavailable pauses new work until fresh observations recover.
    pub fn new(
        pool: Pool,
        monitor: Option<Arc<Monitor>>,
        per_worker: NonZeroU64,
        reserve: u64,
        fallback_memory: Arc<dyn Fn() -> Option<u64> + Send + Sync>,
    ) -> Self {
        Self {
            pool,
            monitor: monitor.map(|monitor| monitor as Arc<dyn ObservationSource>),
            required: false,
            per_worker,
            reserve,
            fallback_memory,
            native_cpu: Arc::new(|| 0),
        }
    }

    /// Require the actual native custodian's cached observations even before
    /// its first successful sample. Missing input pauses work; it never becomes
    /// a fabricated successful observation or a GUI-dependent fallback.
    pub fn with_observation_source(mut self, source: Arc<dyn ObservationSource>) -> Self {
        self.monitor = Some(source);
        self.required = true;
        self
    }

    /// Supply validated process CPU measurements. An absent/unknown owner
    /// contributes zero, never an invented busy core from a held lease count.
    pub fn with_native_cpu(mut self, source: Arc<dyn Fn() -> u64 + Send + Sync>) -> Self {
        self.native_cpu = source;
        self
    }

    /// The next acquisition's current observed limit; errors pause admission.
    pub fn limit(&self) -> u32 {
        let Ok(states) = self.pool.snapshot() else { return 0 };
        let held =
            states.iter().filter(|state| matches!(state, SlotState::Held { .. })).count() as u32;
        self.limit_for(held)
    }

    /// Use the count from `Pool::try_acquire_observed` inside its transaction.
    pub fn limit_for(&self, held: u32) -> u32 {
        self.limit_at(Instant::now(), held)
    }

    fn limit_at(&self, now: Instant, _held: u32) -> u32 {
        if let Some(monitor) = &self.monitor {
            if let Some((observation, claimable)) = monitor.latest() {
                return observation
                    .admission_limit(
                        now,
                        (self.native_cpu)(),
                        claimable,
                        self.per_worker,
                        self.reserve,
                    )
                    .min(self.pool.slots().get());
            }
            if self.required || monitor.ever_observed() {
                return 0;
            }
        }
        (self.fallback_memory)().map_or(0, |available| {
            (available.saturating_sub(self.reserve) / self.per_worker)
                .min(u64::from(self.pool.slots().get())) as u32
        })
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use super::*;

    #[test]
    fn absent_monitor_uses_measured_kernel_budget_without_inventing_monitor_freshness() {
        let _fixture = crate::tests::kernel_fixture();
        let dir = crate::tests::private_tempdir();
        let pool = Pool::open_in(dir.path(), NonZeroU32::new(8).unwrap()).unwrap();
        let policy = HostPolicy::new(
            pool.clone(),
            None,
            NonZeroU64::new(1000).unwrap(),
            200,
            Arc::new(|| Some(5000)),
        );
        assert_eq!(policy.limit(), 4);
        let unknown =
            HostPolicy::new(pool, None, NonZeroU64::new(1000).unwrap(), 200, Arc::new(|| None));
        assert_eq!(unknown.limit(), 0);
    }
    #[test]
    fn required_native_cache_adapts_and_never_refreshes_or_falls_back_on_loss() {
        use std::sync::Mutex;
        use std::time::Duration;

        use crate::{Measurements, MemoryPressure, ThermalPressure};
        struct Cache(Mutex<Option<(Observation, u64)>>);
        impl ObservationSource for Cache {
            fn latest(&self) -> Option<(Observation, u64)> {
                self.0.lock().unwrap().clone()
            }
            fn ever_observed(&self) -> bool {
                false
            } // required input, no invented success
        }
        let _fixture = crate::tests::kernel_fixture();
        let dir = crate::tests::private_tempdir();
        let pool = Pool::open_in(dir.path(), NonZeroU32::new(8).unwrap()).unwrap();
        let source = Arc::new(Cache(Mutex::new(None)));
        let policy =
            HostPolicy::new(pool, None, NonZeroU64::new(1000).unwrap(), 0, Arc::new(|| Some(9000)))
                .with_observation_source(source.clone());
        assert_eq!(policy.limit(), 0);
        let received = Instant::now();
        let sample = |busy, pressure| {
            Observation::from_measurements(Measurements {
                received,
                age: Duration::ZERO,
                window: Duration::from_secs(1),
                cpus: 8,
                busy_millicores: Some(busy),
                available_memory: Some(9000),
                pressure,
                thermal: ThermalPressure::Nominal,
            })
            .unwrap()
        };
        *source.0.lock().unwrap() = Some((sample(4000, MemoryPressure::Normal), 9000));
        assert_eq!(policy.limit_at(received, 0), 4);
        *source.0.lock().unwrap() = Some((sample(7000, MemoryPressure::Normal), 9000));
        assert_eq!(policy.limit_at(received, 0), 1);
        *source.0.lock().unwrap() = Some((sample(0, MemoryPressure::Normal), 9000));
        assert_eq!(policy.limit_at(received, 0), 8);
        assert_eq!(policy.limit_at(received + Duration::from_secs(4), 0), 0);
        *source.0.lock().unwrap() = Some((sample(0, MemoryPressure::Critical), 9000));
        assert_eq!(policy.limit_at(received, 0), 0);
        *source.0.lock().unwrap() = None;
        assert_eq!(policy.limit(), 0);
        assert!(
            Observation::from_measurements(Measurements {
                received,
                age: Duration::ZERO,
                window: Duration::from_secs(1),
                cpus: 8,
                busy_millicores: Some(0),
                available_memory: Some(9000),
                pressure: MemoryPressure::Unknown,
                thermal: ThermalPressure::Nominal,
            })
            .is_err()
        );
    }
}
