//! An unavailable transport is a runner refusal, not a paired-stage bypass.
//! ReceiptCheckedPair still owns both preflight and final full input checks.

use std::path::PathBuf;

use trust_qualification::pair::FileIdentity;
use trust_qualification::probes::MetadataRunner;
use trust_qualification::{Refusal, Result};
use trust_resource_controller::{MetadataBatch, MetadataBatchReport};

pub(crate) struct NativeMetadataRunner;

fn unavailable() -> Refusal {
    Refusal("native metadata admission is unsupported on this Unix platform".into())
}

impl NativeMetadataRunner {
    pub(crate) fn new(_service: Option<PathBuf>, _host_store: Option<PathBuf>) -> Self {
        Self
    }
}

impl MetadataRunner for NativeMetadataRunner {
    fn service_image(&self) -> Result<FileIdentity> {
        Err(unavailable())
    }

    fn collect(&mut self, _batch: &MetadataBatch) -> Result<MetadataBatchReport> {
        Err(unavailable())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsupported_runner_refuses_without_service_or_host_discovery() {
        let mut runner = NativeMetadataRunner::new(
            Some("/nonexistent-service".into()),
            Some("/nonexistent-native-host".into()),
        );
        assert!(
            runner.service_image().unwrap_err().0.contains("unsupported on this Unix platform")
        );
        let batch = MetadataBatch {
            host_store: Some(b"/nonexistent-native-host".to_vec()),
            service_program: b"/nonexistent-service".to_vec(),
            service_sha256: [0; 32],
            probes: Vec::new(),
        };
        assert!(
            runner.collect(&batch).unwrap_err().0.contains("unsupported on this Unix platform")
        );
        assert!(runner.execution_observation().is_none());
    }
}
