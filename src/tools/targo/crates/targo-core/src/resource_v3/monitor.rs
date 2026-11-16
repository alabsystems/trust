//! Targo and compiler workers share the canonical authenticated observation
//! cache and host liveness implementation, without GUI subprocess probes.
pub(super) use trust_build_cpu::NativeHostObservation as NativeMonitor;

pub(super) fn custodian_lost() -> ! {
    super::executor::abort_worker()
}
