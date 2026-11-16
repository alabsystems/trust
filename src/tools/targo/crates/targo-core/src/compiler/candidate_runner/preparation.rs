//! Resolve the parent's independent selected commands from the SAME actual
//! native preparation, using normal Cargo configuration and compiler queries.
use super::*;
use crate::compiler::{
    candidate_commands::Preparation, candidate_coordinator, candidate_semantics,
};
use crate::resource_v3::workload::bank::broker::RegisteredArtifact;
use cargo_util::{Jobserver, Sha256};
use std::io::{self, Write};
use std::sync::Mutex;
use trust_resource_controller::client::ContainedProducedMember;
use trust_resource_controller::workload::host::coordinator::{Mode, SemanticSelection};

pub(super) const MAX_DIAGNOSTIC_BYTES: usize = 1024 * 1024;
#[derive(Clone)]
pub(super) struct Output(Arc<Mutex<DiagnosticOutput>>);
struct DiagnosticOutput {
    bytes: Vec<u8>,
    failed: bool,
}
impl Output {
    pub(super) fn new() -> Self {
        Self(Arc::new(Mutex::new(DiagnosticOutput {
            bytes: Vec::new(),
            failed: false,
        })))
    }
    fn check(&self) -> CargoResult<()> {
        ensure!(
            !self
                .0
                .lock()
                .map_err(|_| anyhow::anyhow!("parent preparation diagnostics poisoned"))?
                .failed,
            "parent preparation diagnostics exceeded their finite bound"
        );
        Ok(())
    }
}
impl Write for Output {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let mut output = self
            .0
            .lock()
            .map_err(|_| io::Error::other("preparation diagnostics poisoned"))?;
        if output.failed {
            return Err(io::Error::other(
                "preparation diagnostic capture already failed",
            ));
        }
        let room = MAX_DIAGNOSTIC_BYTES.saturating_sub(output.bytes.len());
        output
            .bytes
            .extend_from_slice(&bytes[..room.min(bytes.len())]);
        if bytes.len() > room {
            output.failed = true;
            return Err(io::Error::other(
                "parent preparation diagnostic limit reached",
            ));
        }
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        self.check().map_err(io::Error::other)
    }
}

impl CompilerRelay {
    pub(super) fn prepare(
        &mut self,
        member: &mut ContainedProducedMember,
        artifact: Arc<RegisteredArtifact>,
        jobserver: &Jobserver,
    ) -> CargoResult<SemanticSelection> {
        self.inputs.validate()?;
        let deadline = self.inputs.deadline;
        let actual = member
            .coordinator_prepared(deadline)?
            .context("actual original coordinator preparation is still pending")?;
        let preparation = Preparation::observe(member, artifact.clone(), deadline)?
            .context("actual original coordinator preparation disappeared")?;
        let plan = &self.inputs.plan;
        let manifest = path(&plan.manifest.path);
        let cwd = manifest
            .parent()
            .context("selected manifest has no parent")?
            .to_owned();
        ensure!(
            actual.command.cwd == cwd.as_os_str().as_bytes(),
            "prepared coordinator does not run in its selected manifest directory"
        );
        let home = path(&plan.cargo_home);
        let output_root = path(&plan.output_root);
        let sdk = path(&plan.sdk_root);
        let compiler = path(&plan.compiler.path);
        let sources = plan
            .sources
            .iter()
            .map(|source| path(&source.root))
            .collect::<Vec<_>>();
        // Native contained targets have captured, non-TTY output. Preserve the
        // parent's bounded diagnostics while sharing that same Shell policy;
        // do not substitute its ambient terminal width/color into expectations.
        let shell =
            cargo_util_terminal::Shell::from_write(Box::new(self.preparation_output.clone()));
        let mut gctx = crate::util::GlobalContext::for_coordinator_queries(
            shell,
            cwd,
            home.clone(),
            artifact.original().image().program().to_owned(),
            preparation.environment().clone(),
            jobserver.clone(),
            self.factory.clone(),
        )?;
        candidate_coordinator::configure_context(&mut gctx, plan)?;
        let workspace = candidate_coordinator::selected_workspace(&gctx, plan)?;
        let options = candidate_coordinator::compile_options(&gctx, plan)?;
        let selected = candidate_semantics::Selected {
            mode: match plan.mode {
                Mode::Build => candidate_semantics::Mode::Build,
                Mode::Check => candidate_semantics::Mode::Check,
            },
            sources: &sources,
            manifest: &manifest,
            package: &plan.package,
            binary: &plan.binary,
            output_root: &output_root,
            cargo_home: &home,
            sdk_root: &sdk,
            compiler: &compiler,
            compiler_sha256: plan.compiler.sha256,
        };
        let resolved = crate::ops::cargo_compile::candidate_configuration(
            &workspace,
            &options,
            &selected,
            preparation,
            jobserver,
        )?;
        self.preparation_output.check()?;
        self.inputs.validate()?;
        self.install_commands(member, resolved.commands)?;
        let mut prepared_hash = Sha256::new();
        prepared_hash.update(&actual.encode()?);
        let request = member.coordinator_request()?;
        Ok(SemanticSelection {
            root_attempt: request.contained.produced.key.root_attempt,
            member_attempt: request.contained.produced.member.member_attempt,
            prepared_sha256: prepared_hash.finish(),
            configuration_sha256: resolved.digests.configuration_sha256,
            coverage_sha256: resolved.digests.coverage_sha256,
        })
    }
}
