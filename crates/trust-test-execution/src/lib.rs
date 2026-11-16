//! Native prepared execution, authorized only after current proof validation.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::{Deserialize, Serialize};

#[cfg(unix)]
pub mod retained;
// Unverified workload observations share no prepared/proof execution authority.
pub mod workload;

pub const PLAN_SCHEMA: &str = "targo.prepared-tests.v1";
pub const RECEIPT_SCHEMA: &str = "targo.prepared-tests-receipt.v1";
pub const EXPORT_ENV: &str = "TRUST_TARGO_PREPARED_TESTS_EXPORT";
pub const EXPORT_SESSION_ENV: &str = "TRUST_TARGO_PREPARED_TESTS_SESSION";
pub const MAX_PLAN_BYTES: u64 = 8 * 1024 * 1024;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PreparedTests {
    pub schema: String,
    pub session: String,
    pub host_os: String,
    pub host_arch: String,
    pub target_directory: String,
    pub no_fail_fast: bool,
    pub tests: Vec<PreparedTest>,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PreparedTest {
    pub target: String,
    pub executable: String,
    pub sha256: String,
    pub size: u64,
    pub cwd: String,
    pub args: Vec<String>,
    pub env: BTreeMap<String, String>,
}

impl std::fmt::Debug for PreparedTest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedTest")
            .field("target", &self.target)
            .field("executable", &self.executable)
            .field("sha256", &self.sha256)
            .field("argument_count", &self.args.len())
            .field("environment_count", &self.env.len())
            .finish_non_exhaustive()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PreparedTestsReceipt {
    pub schema: String,
    pub session: String,
    pub path: String,
    pub sha256: String,
}

/// This checks the handoff's shape and its exact current artifact population.
/// Callers must separately authenticate the producer, digest, bytes and proof
/// result. A well-formed plan is never authorization to execute it.
impl PreparedTests {
    pub fn validate(
        &self,
        session: &str,
        artifacts: &BTreeMap<String, (String, u64)>,
    ) -> Result<(), String> {
        if self.schema != PLAN_SCHEMA
            || self.session != session
            || session.is_empty()
            || self.host_os != std::env::consts::OS
            || self.host_arch != std::env::consts::ARCH
        {
            return Err("prepared tests do not match this session, schema and host".into());
        }
        if self.tests.is_empty()
            || self.tests.len() > 4096
            || self.tests.len() != artifacts.len()
            || !Path::new(&self.target_directory).is_absolute()
        {
            return Err(
                "prepared tests have an invalid artifact population or target directory".into()
            );
        }
        let mut seen = BTreeSet::new();
        for test in &self.tests {
            if test.target.is_empty()
                || !seen.insert(&test.executable)
                || !Path::new(&test.executable).is_absolute()
                || !Path::new(&test.executable).starts_with(&self.target_directory)
                || !Path::new(&test.cwd).is_absolute()
                || artifacts.get(&test.executable) != Some(&(test.sha256.clone(), test.size))
            {
                return Err("prepared test does not match its authorized artifact".into());
            }
            if test.args.len() > 4096
                || test.env.len() > 4096
                || test.args.iter().any(|value| value.contains('\0'))
                || test.env.iter().any(|(key, value)| {
                    key.is_empty()
                        || key.contains(['=', '\0'])
                        || value.contains('\0')
                        || !allowed_environment(key, value)
                })
            {
                return Err(
                    "prepared test has unsupported arguments or environment authority".into()
                );
            }
        }
        Ok(())
    }
}

/// Opaque runtime transports belong to the actual scheduler owner, never to a
/// serialized command plan. Stable job counts and ordinary scalar inputs are
/// deliberately excluded from this classifier.
pub fn is_scheduling_transport_environment(name: &str) -> bool {
    matches!(
        name,
        "TRUST_CPU_IMPLICIT_FD"
            | "TRUST_CPU_HANDOFF"
            | "BUILD_SLOT_CPU_PROTOCOL"
            | "BUILD_SLOT_CPU_MODE"
            | "BUILD_SLOT_DIR"
            | "BUILD_SLOT_LEGACY_DIR"
            | "BUILD_SLOT_V2_DIR"
            | "BUILD_SLOT_POOL_SLOTS"
            | "BUILD_SLOT_FENCE_FDS"
            | "TARGO_JOB_MEMORY_BYTES"
            | "TARGO_MEMORY_RESERVE_BYTES"
            | "CARGO_MAKEFLAGS"
            | "MAKEFLAGS"
            | "MFLAGS"
            | "CARGO_JOBSERVER_HANDOFF"
            | "ATERM_RESOURCE_JOB_V3"
    )
}

/// Match the native authenticated-test environment boundary. Fixed system
/// loader fallback values are the only permitted dynamic-loader settings.
pub fn allowed_environment(name: &str, value: &str) -> bool {
    if cfg!(target_os = "macos") && name == "DYLD_FALLBACK_LIBRARY_PATH" {
        return value == "/usr/lib:/System/Library/Frameworks";
    }
    if cfg!(target_os = "macos") && name == "DYLD_FALLBACK_FRAMEWORK_PATH" {
        return value == "/System/Library/Frameworks";
    }
    let upper = name.to_ascii_uppercase();
    !(name.starts_with("TRUST_")
        || name.starts_with("TRUSTD_")
        || is_scheduling_transport_environment(name)
        || upper.starts_with("LD_")
        || upper.starts_with("DYLD_")
        || matches!(upper.as_str(), "LIBPATH" | "SHLIB_PATH" | "LDR_PRELOAD")
        || matches!(
            name,
            "RUSTFLAGS"
                | "RUSTDOCFLAGS"
                | "CARGO_ENCODED_RUSTFLAGS"
                | "CARGO_ENCODED_RUSTDOCFLAGS"
                | "CARGO_BUILD_RUSTFLAGS"
                | "CARGO_BUILD_RUSTDOCFLAGS"
                | "RUSTC"
                | "RUSTDOC"
                | "RUSTC_WRAPPER"
                | "RUSTC_WORKSPACE_WRAPPER"
                | "CARGO_BUILD_RUSTC"
                | "CARGO_BUILD_RUSTDOC"
                | "CARGO_BUILD_RUSTC_WRAPPER"
                | "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"
        ))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn fixture() -> (PreparedTests, BTreeMap<String, (String, u64)>) {
        let test = PreparedTest {
            target: "test".into(),
            executable: "/target/test".into(),
            sha256: "a".repeat(64),
            size: 3,
            cwd: "/source".into(),
            args: vec!["--exact".into(), "example".into()],
            env: BTreeMap::new(),
        };
        let expected =
            [(test.executable.clone(), (test.sha256.clone(), test.size))].into_iter().collect();
        (
            PreparedTests {
                schema: PLAN_SCHEMA.into(),
                session: "current".into(),
                host_os: std::env::consts::OS.into(),
                host_arch: std::env::consts::ARCH.into(),
                target_directory: "/target".into(),
                no_fail_fast: false,
                tests: vec![test],
            },
            expected,
        )
    }

    #[test]
    fn current_session_and_exact_artifact_population_are_required() {
        let (mut plan, expected) = fixture();
        assert!(plan.validate("current", &expected).is_ok());
        assert!(plan.validate("other", &expected).is_err());
        plan.tests[0].sha256 = "b".repeat(64);
        assert!(plan.validate("current", &expected).is_err());
        plan.tests[0].sha256 = "a".repeat(64);
        plan.tests.push(plan.tests[0].clone());
        assert!(plan.validate("current", &expected).is_err());
    }

    #[test]
    fn execution_cannot_restore_compiler_loader_or_jobserver_authority() {
        for key in [
            "RUSTC",
            "TRUST_TARGO_VERIFY",
            "TRUSTD_DISABLE",
            "TRUSTD_RUNTIME_DIR",
            "LD_PRELOAD",
            "DYLD_INSERT_LIBRARIES",
            "CARGO_MAKEFLAGS",
            "CARGO_JOBSERVER_HANDOFF",
        ] {
            let (mut plan, expected) = fixture();
            plan.tests[0].env.insert(key.into(), "injected".into());
            assert!(plan.validate("current", &expected).is_err(), "{key}");
        }
    }

    #[test]
    fn plans_exclude_runtime_transports_but_preserve_signed_counts_and_scalars() {
        for key in [
            "TRUST_CPU_IMPLICIT_FD",
            "TRUST_CPU_HANDOFF",
            "BUILD_SLOT_CPU_PROTOCOL",
            "BUILD_SLOT_CPU_MODE",
            "BUILD_SLOT_DIR",
            "BUILD_SLOT_LEGACY_DIR",
            "BUILD_SLOT_V2_DIR",
            "BUILD_SLOT_POOL_SLOTS",
            "BUILD_SLOT_FENCE_FDS",
            "TARGO_JOB_MEMORY_BYTES",
            "TARGO_MEMORY_RESERVE_BYTES",
            "CARGO_MAKEFLAGS",
            "MAKEFLAGS",
            "MFLAGS",
            "CARGO_JOBSERVER_HANDOFF",
            "ATERM_RESOURCE_JOB_V3",
        ] {
            let (mut plan, expected) = fixture();
            plan.tests[0].env.insert(key.into(), "forged-transport".into());
            assert!(plan.validate("current", &expected).is_err(), "{key}");
        }
        let (mut plan, expected) = fixture();
        for key in [
            "NUM_JOBS",
            "CARGO_BUILD_JOBS",
            "TARGO_PLANNED_JOBS",
            "RUST_TEST_THREADS",
            "BUILD_SLOT_HELD",
            "FIXTURE_SCALAR",
        ] {
            plan.tests[0].env.insert(key.into(), "1".into());
        }
        assert!(plan.validate("current", &expected).is_ok());
    }

    #[test]
    fn relative_paths_nuls_and_foreign_hosts_refuse() {
        let (mut plan, expected) = fixture();
        plan.tests[0].cwd = "relative".into();
        assert!(plan.validate("current", &expected).is_err());
        plan.tests[0].cwd = "/source".into();
        plan.tests[0].args.push("bad\0arg".into());
        assert!(plan.validate("current", &expected).is_err());
        plan.tests[0].args.pop();
        plan.host_arch = "foreign".into();
        assert!(plan.validate("current", &expected).is_err());
    }
}
