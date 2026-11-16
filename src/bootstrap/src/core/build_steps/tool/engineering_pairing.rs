//! Independently held engineering dependencies, not completed SDK authority.
//! The existing Bootstrap entry owns early GNU/fixed capture and source/output
//! leases. This owner binds only its explicitly selected initial compiler.
use std::io::{self, Read as _};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};
use trust_resource_controller::descriptors::{AdmittedTargetSysroot, DescriptorBudget};
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
    if actual.starts_with(root) || root.starts_with(&actual) {
        return Err(io::Error::other("engineering input and output namespaces overlap"));
    }
    Ok(())
}

pub(super) struct Inputs {
    compiler: Arc<HeldProgram>,
    target: Arc<AdmittedTargetSysroot>,
    linker: HelperInput,
    debug: HelperInput,
    encoded: String,
    identity: String,
}

/// Optional observations in this engineering-only producer. Absence is explicit
/// DATA, never helper/SDK readiness. A present malformed input still refuses.
enum HelperInput {
    Absent(PathBuf),
    Held(HeldSystemCommand),
}
impl HelperInput {
    fn capture(path: &Path, system_imports: bool, end: Instant) -> io::Result<Self> {
        match fs::symlink_metadata(path) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                Ok(Self::Absent(path.to_owned()))
            }
            Err(error) => Err(error),
            Ok(metadata) => {
                use std::os::unix::fs::PermissionsExt as _;
                if !metadata.is_file() || metadata.permissions().mode() & 0o111 == 0 {
                    return Err(io::Error::other(
                        "present engineering helper must be a regular executable, never a symlink",
                    ));
                }
                let held = if system_imports {
                    HeldSystemCommand::open_absolute_system_imports(path, end)?
                } else {
                    HeldSystemCommand::open(path, end)?
                };
                Ok(Self::Held(held))
            }
        }
    }
    fn validate(&self, end: Instant) -> io::Result<()> {
        match self {
            Self::Absent(path) => match fs::symlink_metadata(path) {
                Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
                Err(error) => Err(error),
                Ok(_) => Err(io::Error::other("absent engineering helper input appeared")),
            },
            Self::Held(held) => held.validate(end),
        }
    }
    fn record(&self) -> serde_json::Value {
        match self {
            Self::Absent(path) => serde_json::json!({
                "availability": "absent", "selected_path": path,
            }),
            Self::Held(held) => serde_json::json!({
                "availability": "held", "selected_path": held.observation().executable.path,
                "sha256": held.observation().executable.sha256,
            }),
        }
    }
}

// One bounded phase for complete multi-GiB input hashing and bookends; no
// per-file clock restart. Metadata children have a separate tighter cap below.
const INPUT_BOOKEND_BUDGET: Duration = Duration::from_secs(300);
const METADATA_QUERY_BUDGET: Duration = Duration::from_secs(30);

fn deadline() -> Instant {
    Instant::now() + INPUT_BOOKEND_BUDGET
}

fn input_stage<T>(stage: &str, result: io::Result<T>) -> io::Result<T> {
    result.map_err(|error| io::Error::new(error.kind(), format!("{stage}: {error}")))
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
    let query_end = end.min(Instant::now() + METADATA_QUERY_BUDGET);
    let result = command.bounded_metadata_output(query_end, 16 * 1024)?;
    held.validate(end)?;
    if !result.status.success() {
        return Err(io::Error::other("engineering compiler query refused"));
    }
    Ok(result.stdout)
}

impl Inputs {
    pub(super) fn capture(builder: &Builder<'_>, input: CargoInput) -> io::Result<Self> {
        let end = deadline();
        // Do not call sysroot(stage0): its Step creates a different mutable
        // output sysroot. These are the actual explicitly selected inputs.
        let root = builder.sess.initial_sysroot.canonicalize()?;
        let program = builder.initial_rustc.canonicalize()?;
        validate_output_domains(builder, &root, input)?;
        let compiler_hash = input_stage("original compiler bytes", digest(&program, end))?;
        let compiler = Arc::new(input_stage(
            "original compiler runtime",
            HeldProgram::open(&root, &program, &compiler_hash, end),
        )?);
        let target = capture_target(Arc::clone(&compiler), end)?;
        let linker = input_stage(
            "original linker input",
            HelperInput::capture(&root.join("bin/rust-lld"), true, end),
        )?;
        let debug = input_stage(
            "original debug helper input",
            HelperInput::capture(&root.join("bin/dsymutil"), true, end),
        )?;
        let reply = input_stage(
            "compiler capability query",
            query(&compiler, "--resource-capabilities", end),
        )?;
        let encoded = input_stage(
            "original compiler pairing",
            paired_compiler::capture(&compiler, &reply, end),
        )?;
        let identity = String::from_utf8(input_stage(
            "compiler identity query",
            query(&compiler, "-vV", end),
        )?)
        .map_err(|_| io::Error::other("engineering compiler identity is not UTF-8"))?;
        let inputs = Self { compiler, target, linker, debug, encoded, identity };
        inputs.validate(end)?;
        Ok(inputs)
    }

    fn validate(&self, end: Instant) -> io::Result<()> {
        input_stage("compiler runtime bookend", self.compiler.validate(end))?;
        input_stage("complete admitted target bookend", self.target.validate(end))?;
        input_stage("linker input bookend", self.linker.validate(end))?;
        input_stage("debug helper input bookend", self.debug.validate(end))
    }

    pub(super) fn bind(&self, cargo: &mut CargoCommand) -> io::Result<()> {
        self.validate(deadline())?;
        // Constructor-owned child input only; no user-supplied JSON, ambient
        // pairing profile, compatibility wrapper or sealed-producer override.
        cargo.env(paired_compiler::PRODUCER_INPUT, &self.encoded);
        Ok(())
    }

    // Trust: this metadata comes only from the actually held compiler query.
    pub(super) fn bind_frontend(&self, cargo: &mut CargoCommand, host: &str) -> io::Result<()> {
        self.validate(deadline())?;
        let identity = retained_identity(&self.identity, host)?;
        cargo.env("CFG_TRUST_ORACLE_COMPILER_HASH", &identity.commit);
        cargo.env("CFG_TRUST_ORACLE_COMPILER_RELEASE", &identity.release);
        Ok(())
    }

    pub(super) fn finish(&self, builder: &Builder<'_>, artifact: &Path) -> io::Result<()> {
        let end = deadline();
        self.validate(end)?;
        let artifact_sha256: String =
            digest(artifact, end)?.iter().map(|byte| format!("{byte:02x}")).collect();
        self.validate(end)?;
        let record = serde_json::json!({
            "kind":"engineering-frontend-dependencies-v2",
            "scope":"input custody and compiler compatibility only; not completed SDK, release, Host or proof qualification",
            "frontend_source":builder.version_info().sha(),
            "frontend_sha256":artifact_sha256,
            "compiler_identity_observed":self.identity,
            "compiler_sha256":self.compiler.observation().executable.sha256,
            "target_sysroot_files":self.target.file_observations().count(),
            "native_helpers": {
                "rust-lld": self.linker.record(),
                "dsymutil": self.debug.record(),
            },
        });
        let bytes = serde_json::to_vec_pretty(&record).map_err(io::Error::other)?;
        fs::write(artifact.with_extension("engineering-dependencies.json"), bytes)?;
        builder.info(&format!("Engineering native frontend: {} (independent compiler dependency; no SDK qualification)", artifact.display()));
        Ok(())
    }
}

// Trust: guard the actual producer cache domain before any compiler work.
fn validate_output_domains(
    builder: &Builder<'_>,
    root: &Path,
    input: CargoInput,
) -> io::Result<()> {
    let initial = Compiler::new(0, builder.host_target);
    separate_output(
        root,
        &crate::core::session::tools_bin_dir(&builder.out, initial, builder.host_target),
    )?;
    separate_output(
        root,
        &builder.cargo_out_for_input(initial, Mode::ToolTarget, builder.host_target, input),
    )
}

// Trust: parse a bounded reply already obtained from the held native image.
#[derive(Debug, PartialEq, Eq)]
struct RetainedIdentity {
    commit: String,
    release: String,
}

fn retained_identity(reply: &str, host: &str) -> io::Result<RetainedIdentity> {
    fn unique<'a>(reply: &'a str, prefix: &str) -> io::Result<&'a str> {
        let values: Vec<_> = reply.lines().filter_map(|line| line.strip_prefix(prefix)).collect();
        if values.len() != 1 {
            return Err(io::Error::other("retained compiler identity field missing or ambiguous"));
        }
        Ok(values[0])
    }
    let commit = unique(reply, "commit-hash: ")?;
    let release = unique(reply, "release: ")?;
    if unique(reply, "binary: ")? != "trustc"
        || unique(reply, "host: ")? != host
        || commit.len() != 40
        || !commit.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        || release.is_empty()
        || release.len() > 128
        || !release.bytes().all(|b| b.is_ascii_alphanumeric() || b".-+_".contains(&b))
    {
        return Err(io::Error::other(
            "retained compiler identity is not exact native Trust metadata",
        ));
    }
    Ok(RetainedIdentity { commit: commit.into(), release: release.into() })
}

fn capture_target(
    compiler: Arc<HeldProgram>,
    end: Instant,
) -> io::Result<Arc<AdmittedTargetSysroot>> {
    // The provenance plan retains originals but never raises a process limit.
    // The existing process coordinator owns checked capacity acquisition and
    // the actual charge, retained by the SAME target through final validation.
    let budget =
        input_stage("target descriptor preparation", DescriptorBudget::for_preparation(1, 0))?;
    let plan =
        input_stage("complete target namespace plan", HeldRustTargetSysroot::plan(compiler, end))?;
    input_stage("complete admitted target materialization", budget.capture_target(plan, end))
}

#[cfg(test)]
#[path = "engineering_pairing/tests.rs"]
mod tests;

#[cfg(test)]
#[path = "engineering_pairing/descriptor_tests.rs"]
mod descriptor_tests;
