//! Original cooperative workload ownership. This is not a second admission
//! domain: startup must supply the actual authenticated all-domain guards.

pub(crate) mod bank;
pub(crate) mod produced;
mod query;
pub(crate) mod startup;

pub(crate) enum ProcessPlan {
    Workload(std::sync::Arc<trust_resource_controller::workload::WorkloadInvocation>),
    NativeJob(std::sync::Arc<trust_resource_controller::native_job::Plan>),
}
impl ProcessPlan {
    pub(crate) fn header(&self) -> trust_resource_controller::native_job::RootHeader<'_> {
        match self { Self::Workload(plan) => trust_resource_controller::native_job::RootHeader::workload(plan), Self::NativeJob(plan) => plan.header() }
    }
}
pub(crate) struct ProcessInputs {
    pub(crate) invocation: ProcessPlan,
    pub(crate) compiler: std::sync::Arc<trust_resource_provenance::program::HeldProgram>,
    pub(crate) sysroot:
        std::sync::Arc<trust_resource_controller::descriptors::AdmittedTargetSysroot>,
    pub(crate) deadline: std::time::Instant,
    pub(crate) poisoned: std::sync::atomic::AtomicBool,
    /// Shared actual service stop intent. It grants nothing and never
    /// substitutes for the execution owner's final owning wait/retirement.
    pub(crate) cancelled: std::sync::Arc<std::sync::atomic::AtomicBool>,
    pub(crate) _program_reservation: Option<std::sync::Arc<trust_resource_controller::descriptors::OriginalInputPermit>>,
}

pub(super) fn install_queries(startup: std::sync::Arc<super::Startup>) -> std::io::Result<()> {
    query::install(startup)
}

pub(crate) fn abort_unknown() -> ! {
    super::executor::abort_worker()
}

#[cfg(test)]
pub(crate) fn abort_fixture() -> ! {
    // The real production abort path, exposed only to the isolated evidence
    // actor; this constructs no startup, host, target or resource authority.
    super::executor::abort_worker()
}
