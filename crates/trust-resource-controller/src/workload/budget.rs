//! Checked containment plan only. It grants no deadline, root or resources;
//! the actual admitted Submission deadline remains independently authoritative.
use std::io;
use std::time::Duration;

use super::WORKLOAD_MAX_REPETITIONS;

pub const STARTUP_NS: u64 = 300_000_000_000;
pub const CHECKPOINT_NS: u64 = 300_000_000_000;
pub const SETTLEMENT_NS: u64 = 300_000_000_000;
/// Existing runtime observations use u64 nanoseconds. Keep even the rounded
/// whole-root millisecond containment within that representation.
pub const MAX_ROOT_TIMEOUT_MS: u64 = u64::MAX / 1_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Budget {
    pub phases: u32,
    pub phase_timeout_ns: u64,
    pub root_timeout_ms: u64,
}
impl Budget {
    /// One consumer compilation, both complete inventories, and every native
    /// sample each retain the original per-phase budget. Checkpoint/input
    /// revalidation and native startup/settlement have separate explicit bounds.
    /// Never silently truncate a valid requested phase to a resolver timeout.
    pub fn new(repetitions: u32, phase_timeout_ns: u64) -> io::Result<Self> {
        if !(1..=WORKLOAD_MAX_REPETITIONS).contains(&repetitions) || phase_timeout_ns == 0 {
            return Err(super::invalid());
        }
        let phases = 1 + 2 + 2 * repetitions;
        let total = u128::from(phases) * u128::from(phase_timeout_ns)
            + u128::from(phases) * u128::from(CHECKPOINT_NS)
            + u128::from(STARTUP_NS)
            + u128::from(SETTLEMENT_NS);
        let millis = total.div_ceil(1_000_000);
        if millis > u128::from(MAX_ROOT_TIMEOUT_MS) {
            return Err(super::invalid());
        }
        Ok(Self { phases, phase_timeout_ns, root_timeout_ms: millis as u64 })
    }
    pub fn root_duration(self) -> Duration {
        Duration::from_millis(self.root_timeout_ms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whole_plan_preserves_each_phase_instead_of_truncating_to_600_seconds_or_24_hours() {
        let hour = 3_600_000_000_000;
        assert_eq!(
            Budget::new(3, hour).unwrap(),
            Budget { phases: 9, phase_timeout_ns: hour, root_timeout_ms: 35_700_000 }
        );
        let complete = Budget::new(32, hour).unwrap();
        assert_eq!(complete.phases, 67);
        assert_eq!(complete.root_timeout_ms, 261_900_000);
        assert!(complete.root_duration() > Duration::from_secs(24 * 3600));
    }

    #[test]
    fn round_up_only_the_outer_milliseconds_and_refuse_unrepresentable_complete_plans() {
        let tiny = Budget::new(1, 1).unwrap();
        assert_eq!(tiny.phase_timeout_ns, 1);
        assert_eq!(tiny.root_timeout_ms, 2_100_001);
        for (repetitions, timeout) in [(0, 1), (33, 1), (1, 0), (32, u64::MAX)] {
            assert!(Budget::new(repetitions, timeout).is_err());
        }
        let overhead =
            5 * u128::from(CHECKPOINT_NS) + u128::from(STARTUP_NS) + u128::from(SETTLEMENT_NS);
        let last = ((u128::from(MAX_ROOT_TIMEOUT_MS) * 1_000_000 - overhead) / 5) as u64;
        assert_eq!(Budget::new(1, last).unwrap().root_timeout_ms, MAX_ROOT_TIMEOUT_MS);
        assert!(Budget::new(1, last + 1).is_err());
    }
}
