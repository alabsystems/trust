//! Native workload consumer façade. Unsupported targets retain the preceding
//! pair/probe/dependency checks and refuse actual workload delivery.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) use supported::NativeWorkloadProducer;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) use supported::{artifact_identity, invocation, io, write_frame};

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub(crate) struct NativeWorkloadProducer;
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
impl NativeWorkloadProducer {
    pub(crate) fn new(_: Option<std::path::PathBuf>) -> Self {
        Self
    }
}
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
impl trust_qualification::workloads::Producer for NativeWorkloadProducer {
    fn start(
        &mut self,
        _: &trust_qualification::workloads::Request,
    ) -> trust_qualification::Result<Box<dyn trust_qualification::workloads::Run>> {
        Err(trust_qualification::Refusal(
            "native workload ownership is unsupported on this platform".into(),
        ))
    }
}
