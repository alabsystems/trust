//! Whole-plan arithmetic, not a new deadline/resource authority. The actual
//! original host Submission deadline cannot be extended by any plan bytes.
use std::io;
use std::time::Duration;

pub use crate::workload::budget::MAX_ROOT_TIMEOUT_MS;
use crate::workload::budget::{CHECKPOINT_NS, SETTLEMENT_NS, STARTUP_NS};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Budget {
    pub phases: u32,
    pub phase_timeout_ns: u64,
    pub root_timeout_ms: u64,
}
impl Budget {
    pub fn new(repetitions: u32, phase_timeout_ns: u64) -> io::Result<Self> {
        if !(1..=crate::workload::WORKLOAD_MAX_REPETITIONS).contains(&repetitions)
            || phase_timeout_ns == 0
        {
            return Err(crate::wire::invalid());
        }
        // AY compilation, advisory, strict PLUS the unchanged consumer graph.
        let phases = 3 + 1 + 2 + 2 * repetitions;
        let total = u128::from(phases) * u128::from(phase_timeout_ns)
            + u128::from(phases) * u128::from(CHECKPOINT_NS)
            + u128::from(STARTUP_NS)
            + u128::from(SETTLEMENT_NS);
        let millis = total.div_ceil(1_000_000);
        if millis > u128::from(MAX_ROOT_TIMEOUT_MS) {
            return Err(crate::wire::invalid());
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
    fn ay_and_both_policy_budgets_are_additional_not_borrowed_from_consumer() {
        let hour = 3_600_000_000_000;
        for repetitions in [1, 3, 32] {
            let original = crate::workload::budget::Budget::new(repetitions, hour).unwrap();
            let paired = Budget::new(repetitions, hour).unwrap();
            assert_eq!(paired.phases, original.phases + 3);
            assert_eq!(
                paired.root_timeout_ms - original.root_timeout_ms,
                3 * (hour + CHECKPOINT_NS) / 1_000_000
            );
            assert_eq!(paired.phase_timeout_ns, hour);
        }
        assert_eq!(Budget::new(32, hour).unwrap().phases, 70);
    }
    #[test]
    fn complete_plan_rounds_only_outer_time_and_refuses_unrepresentable_bounds() {
        assert_eq!(Budget::new(1, 1).unwrap().root_timeout_ms, 3_000_001);
        for (r, t) in [(0, 1), (33, 1), (1, 0), (32, u64::MAX)] {
            assert!(Budget::new(r, t).is_err());
        }
        let overhead =
            8 * u128::from(CHECKPOINT_NS) + u128::from(STARTUP_NS) + u128::from(SETTLEMENT_NS);
        let last = ((u128::from(MAX_ROOT_TIMEOUT_MS) * 1_000_000 - overhead) / 8) as u64;
        assert_eq!(Budget::new(1, last).unwrap().root_timeout_ms, MAX_ROOT_TIMEOUT_MS);
        assert!(Budget::new(1, last + 1).is_err());
    }
}
