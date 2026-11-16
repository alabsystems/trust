//! Closed metadata service adapter; outer native capture is shared with the
//! separately negotiated normal resolver without widening either purpose.
use std::path::PathBuf;

use serde_json::Value;
use trust_qualification::pair::{self, FileIdentity};
use trust_qualification::probes::MetadataRunner;
use trust_qualification::{Refusal, Result};
use trust_resource_controller::{MetadataBatch, MetadataBatchReport};

use crate::native_root_transport::{self as transport, RootSpec, hex, validate_statuses};

pub(crate) struct NativeMetadataRunner {
    service: std::result::Result<PathBuf, String>,
    host_store: Option<PathBuf>,
    observation: Option<Value>,
}
impl NativeMetadataRunner {
    pub(crate) fn new(service: Option<PathBuf>, host_store: Option<PathBuf>) -> Self {
        let service = (|| -> Result<PathBuf> {
            if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
                return Err(Refusal(
                    "native metadata admission currently supports macOS arm64 only".into(),
                ));
            }
            let service = match service {
                Some(path) => path,
                None => std::env::current_exe()?
                    .parent()
                    .ok_or_else(|| Refusal("paired frontend has no executable parent".into()))?
                    .join("targo"),
            };
            Ok(service.canonicalize()?)
        })()
        .map_err(|e| e.to_string());
        Self { service, host_store, observation: None }
    }
}
impl MetadataRunner for NativeMetadataRunner {
    fn service_image(&self) -> Result<FileIdentity> {
        pair::file_identity(self.service.as_ref().map_err(|e| Refusal(e.clone()))?)
    }
    fn execution_observation(&self) -> Option<Value> {
        self.observation.clone()
    }
    fn collect(&mut self, batch: &MetadataBatch) -> Result<MetadataBatchReport> {
        let service = self.service.as_ref().map_err(|e| Refusal(e.clone()))?.clone();
        let mut supplied = batch.clone();
        supplied.host_store =
            self.host_store.as_ref().map(|p| p.as_os_str().as_encoded_bytes().to_vec());
        let bytes = supplied.encode()?;
        let capture = transport::capture(
            RootSpec {
                program: &service,
                cwd: service
                    .parent()
                    .and_then(std::path::Path::parent)
                    .ok_or_else(|| Refusal("service has no SDK root".into()))?,
                entry: trust_resource_controller::METADATA_STARTUP_ARGUMENT,
                environment: &[],
                input: &bytes,
                max_output: trust_resource_controller::METADATA_REPORT_MAX_BYTES,
                max_stderr: trust_resource_controller::METADATA_REPORT_MAX_BYTES,
                job: "trust-native-paired-metadata",
            },
            &self.host_store,
        )?;
        self.observation = Some(capture.observation);
        let output = capture.output.map_err(Refusal)?;
        if !capture.image_valid {
            return Err(Refusal("native metadata CLI image was not authenticated; original output retained as failed data".into()));
        }
        let terminal = validate_statuses(&capture.statuses.map_err(Refusal)?, &output.status)?;
        let mut report = MetadataBatchReport::decode(&output.stdout, &supplied)?;
        let runner = report
            .runner
            .as_ref()
            .ok_or_else(|| Refusal("metadata report has no actual service observation".into()))?;
        let context =
            trust_resource_controller::ContextReply::decode_observation(&runner.context_frame)?
                .context;
        if runner.identity.pid != terminal.pid
            || runner.identity.birth != terminal.birth
            || context.session != terminal.session
            || hex(&context.root_attempt) != terminal.attempt
        {
            return Err(Refusal(
                "native root lifecycle does not identify actual metadata service/context".into(),
            ));
        }
        if !terminal.normal || !output.status.success() {
            report.failure.get_or_insert(
                "native metadata root failed, refused or did not retire normally".into(),
            );
        }
        Ok(report)
    }
}
