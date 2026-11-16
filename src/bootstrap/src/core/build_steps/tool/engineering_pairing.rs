//! Independently held engineering dependencies, not completed SDK authority.
//! The existing Bootstrap entry owns early GNU/fixed capture and source/output
//! leases. This owner binds only its explicitly selected initial compiler.
use std::io::{self, Read as _};
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};
use trust_resource_provenance::paired_compiler;
use trust_resource_provenance::program::{HeldProgram, HeldRustTargetSysroot, HeldSystemCommand};

use super::*;

fn separate_output(root: &Path, output: &Path) -> io::Result<()> {
    let mut existing = output;
    let mut tail = Vec::new();
    while !existing.try_exists()? {
        tail.push(
            existing
                .file_name()
                .ok_or_else(|| io::Error::other("engineering output has no existing ancestor"))?,
        );
        existing = existing
            .parent()
            .ok_or_else(|| io::Error::other("engineering output parent missing"))?;
    }
    let mut actual = existing.canonicalize()?;
    for name in tail.into_iter().rev() {
        actual.push(name);
    }
    if actual.starts_with(root) {
        return Err(io::Error::other("engineering output aliases the read-only initial sysroot"));
    }
    Ok(())
}

pub(super) struct Inputs {
    compiler: Arc<HeldProgram>,
    target: HeldRustTargetSysroot,
    linker: HeldSystemCommand,
    debug: HeldSystemCommand,
    encoded: String,
    identity: String,
}

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn digest(path: &Path, end: Instant) -> io::Result<[u8; 32]> {
    let mut file = fs::File::open(path)?;
    let mut hash = Sha256::new();
    let mut total = 0u64;
    let mut buffer = [0; 65536];
    loop {
        if Instant::now() >= end {
            return Err(io::ErrorKind::TimedOut.into());
        }
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        total = total
            .checked_add(count as u64)
            .ok_or_else(|| io::Error::other("engineering image size overflow"))?;
        if total > 1024 * 1024 * 1024 {
            return Err(io::Error::other("engineering image exceeds bound"));
        }
        hash.update(&buffer[..count]);
    }
    Ok(hash.finalize().into())
}

fn query(held: &HeldProgram, argument: &str, end: Instant) -> io::Result<Vec<u8>> {
    held.validate(end)?;
    let mut command =
        crate::utils::exec::tool_metadata_command(&held.observation().executable.path);
    command.env_clear();
    for (key, value) in held.runtime_environment()? {
        command.env(key, value);
    }
    command.arg(argument);
    command.metadata_scheduler();
    let result = command.bounded_metadata_output(end, 16 * 1024)?;
    held.validate(end)?;
    if !result.status.success() {
        return Err(io::Error::other("engineering compiler query refused"));
    }
    Ok(result.stdout)
}

impl Inputs {
    pub(super) fn capture(builder: &Builder<'_>) -> io::Result<Self> {
        let end = deadline();
        // Do not call sysroot(stage0): its Step creates a different mutable
        // output sysroot. These are the actual explicitly selected inputs.
        let root = builder.sess.initial_sysroot.canonicalize()?;
        let program = builder.initial_rustc.canonicalize()?;
        let initial = Compiler::new(0, builder.host_target);
        separate_output(
            &root,
            &crate::core::session::tools_bin_dir(&builder.out, initial, builder.host_target),
        )?;
        separate_output(
            &root,
            &builder.cargo_out_for_input(
                initial,
                Mode::ToolTarget,
                builder.host_target,
                CargoInput::Seed.for_original(builder.sess),
            ),
        )?;
        let compiler = Arc::new(HeldProgram::open(&root, &program, &digest(&program, end)?, end)?);
        let target = HeldRustTargetSysroot::capture(Arc::clone(&compiler), end)?;
        let linker = HeldSystemCommand::open(&root.join("bin/rust-lld"), end)?;
        let debug =
            HeldSystemCommand::open_absolute_system_imports(&root.join("bin/dsymutil"), end)?;
        let reply = query(&compiler, "--resource-capabilities", end)?;
        let encoded = paired_compiler::capture(&compiler, &reply, end)?;
        let identity = String::from_utf8(query(&compiler, "-vV", end)?)
            .map_err(|_| io::Error::other("engineering compiler identity is not UTF-8"))?;
        let inputs = Self { compiler, target, linker, debug, encoded, identity };
        inputs.validate(end)?;
        Ok(inputs)
    }

    fn validate(&self, end: Instant) -> io::Result<()> {
        self.compiler.validate(end)?;
        self.target.validate(end)?;
        self.linker.validate(end)?;
        self.debug.validate(end)
    }

    pub(super) fn bind(&self, cargo: &mut CargoCommand) -> io::Result<()> {
        self.validate(deadline())?;
        // Constructor-owned child input only; no user-supplied JSON, ambient
        // pairing profile, compatibility wrapper or sealed-producer override.
        cargo.env(paired_compiler::PRODUCER_INPUT, &self.encoded);
        Ok(())
    }

    pub(super) fn finish(&self, builder: &Builder<'_>, artifact: &Path) -> io::Result<()> {
        let end = deadline();
        self.validate(end)?;
        let artifact_sha256: String =
            digest(artifact, end)?.iter().map(|byte| format!("{byte:02x}")).collect();
        self.validate(end)?;
        let record = serde_json::json!({
            "kind":"engineering-frontend-dependencies-v1",
            "scope":"input custody and compiler compatibility only; not completed SDK, release, Host or proof qualification",
            "frontend_source":builder.version_info().sha(),
            "frontend_sha256":artifact_sha256,
            "compiler_identity_observed":self.identity,
            "compiler_sha256":self.compiler.observation().executable.sha256,
            "target_sysroot_files":self.target.file_observations().count(),
            "linker_sha256":self.linker.observation().executable.sha256,
            "dsymutil_sha256":self.debug.observation().executable.sha256,
        });
        let bytes = serde_json::to_vec_pretty(&record).map_err(io::Error::other)?;
        fs::write(artifact.with_extension("engineering-dependencies.json"), bytes)?;
        builder.info(&format!("Engineering native frontend: {} (independent compiler dependency; no SDK qualification)", artifact.display()));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn engineering_outputs_cannot_alias_retained_initial_inputs() {
        let context = crate::utils::tests::TestCtx::new();
        let root = context.dir().join("initial");
        fs::create_dir(&root).unwrap();
        let root = root.canonicalize().unwrap();
        assert!(separate_output(&root, &root.join("new-tools")).is_err());
        let alias = context.dir().join("alias");
        std::os::unix::fs::symlink(&root, &alias).unwrap();
        assert!(separate_output(&root, &alias.join("new-cache")).is_err());
        assert!(separate_output(&root, &context.dir().join("own-output/tools")).is_ok());
    }
}
