//! Trust: explicit owned scheduling transport for authenticated test images.
//!
//! This grants no proof or execution authority. The native resource owner
//! supplies its actual jobserver and CPU/fence descriptors after qualification;
//! neither inherited environment nor a frontend grant can construct resources.

use crate::util::errors::CargoResult;
use cargo_util::ProcessBuilder;
use jobserver_utils::Jobserver;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::os::fd::{AsRawFd, OwnedFd, RawFd};
use std::sync::Arc;

const CPU_FD: &str = "TRUST_CPU_IMPLICIT_FD";
const FENCE_FDS: &str = "BUILD_SLOT_FENCE_FDS";
const RUNTIME_ENV: &[&str] = &[
    CPU_FD,
    jobserver_utils::CPU_HANDOFF_ENV,
    "BUILD_SLOT_CPU_PROTOCOL",
    "BUILD_SLOT_CPU_MODE",
    "BUILD_SLOT_DIR",
    "BUILD_SLOT_LEGACY_DIR",
    "BUILD_SLOT_V2_DIR",
    "BUILD_SLOT_POOL_SLOTS",
    FENCE_FDS,
    "TARGO_JOB_MEMORY_BYTES",
    "TARGO_MEMORY_RESERVE_BYTES",
];
const DETERMINISTIC_JOB_COUNTS: &[&str] = &["NUM_JOBS", "CARGO_BUILD_JOBS", "TARGO_PLANNED_JOBS"];
// These advertisements are capabilities, not stable inputs to a signed test
// command. Only the owned jobserver may regenerate its own GNU transport.
const OTHER_TRANSPORT_ENV: &[&str] = &[
    "CARGO_MAKEFLAGS",
    "MAKEFLAGS",
    "MFLAGS",
    jobserver_utils::DESCENDANT_HANDOFF_ENV,
    "ATERM_RESOURCE_JOB_V3",
];

pub(super) fn remove_transport_environment(command: &mut ProcessBuilder) {
    for name in RUNTIME_ENV.iter().chain(OTHER_TRANSPORT_ENV) {
        command.env_remove(name);
    }
}

/// Freeze semantic scheduling counts before the retained plan is captured.
/// Descriptor numbers, pool paths and private recovery endpoints belong to
/// the later owned transport, never to the signed semantic environment.
pub(super) fn prepare_retained_environment(command: &mut ProcessBuilder) {
    command.clear_jobserver();
    remove_transport_environment(command);
    for name in DETERMINISTIC_JOB_COUNTS {
        command.env(name, "1");
    }
    command.env("RUST_TEST_THREADS", "1");
}

/// Retains exactly one native scheduler's transport through the child wait.
/// The constructor accepts owned resources, never descriptor numbers supplied
/// by a test, a manifest or the process environment.
pub(crate) struct OwnedSchedulingHandoff {
    jobserver: Jobserver,
    descriptors: Vec<Arc<OwnedFd>>,
    environment: BTreeMap<String, OsString>,
    // Drop last, after every copied transport. In native dispatch this retains
    // the original RootContext and its borrowed-credit/descriptor permits.
    origin: Option<Arc<dyn Send + Sync>>,
}

impl OwnedSchedulingHandoff {
    /// Build from the resource owner's own `RootContext::configure` result.
    /// Only its explicit scheduling overrides are copied; ambient and proof
    /// authority variables cannot enter the capsule.
    pub(crate) fn new(
        jobserver: &Jobserver,
        descriptors: Vec<Arc<OwnedFd>>,
        configured_runtime_command: &ProcessBuilder,
    ) -> CargoResult<Self> {
        let environment = RUNTIME_ENV
            .iter()
            .filter_map(|&name| {
                configured_runtime_command
                    .get_envs()
                    .get(name)
                    .and_then(Option::as_ref)
                    .map(|value| (name.to_owned(), value.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        let handoff = Self {
            jobserver: jobserver.clone(),
            descriptors,
            environment,
            origin: None,
        };
        handoff.validate()?;
        Ok(handoff)
    }

    /// Retain the live native dispatch owner through this capsule's final use.
    /// The origin is opaque and cannot be reconstructed from report metadata.
    pub(crate) fn retain_origin<T: Send + Sync + 'static>(&mut self, origin: Arc<T>) {
        self.origin = Some(origin);
    }

    pub(crate) fn jobserver_only(jobserver: &Jobserver) -> CargoResult<Self> {
        Self::new(
            jobserver,
            Vec::new(),
            &ProcessBuilder::new("__owned_scheduler__"),
        )
    }

    fn validate(&self) -> CargoResult<()> {
        let mut inherited = BTreeSet::new();
        for fd in self.descriptors.iter().map(|fd| fd.as_raw_fd()).chain(
            self.jobserver
                .pipe_descriptors()
                .into_iter()
                .flatten()
                .map(AsRawFd::as_raw_fd),
        ) {
            if fd < 3 || !inherited.insert(fd) {
                anyhow::bail!("owned scheduling descriptors alias stdio or each other");
            }
            let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
            if flags < 0 {
                return Err(std::io::Error::last_os_error().into());
            }
            if flags & libc::FD_CLOEXEC == 0 {
                anyhow::bail!("owned scheduling descriptor is not CLOEXEC in the parent");
            }
        }
        let mut advertised = BTreeSet::new();
        let parse_fd = |value: &std::ffi::OsStr| -> CargoResult<RawFd> {
            let fd = value
                .to_str()
                .and_then(|value| value.parse::<RawFd>().ok())
                .ok_or_else(|| anyhow::format_err!("invalid owned scheduling descriptor"))?;
            if fd < 3 {
                anyhow::bail!("owned scheduling advertisement aliases stdio");
            }
            Ok(fd)
        };
        if let Some(value) = self.environment.get(CPU_FD) {
            advertised.insert(parse_fd(value)?);
        }
        if let Some(value) = self.environment.get(FENCE_FDS) {
            let value = value
                .to_str()
                .ok_or_else(|| anyhow::format_err!("invalid owned scheduling fences"))?;
            for value in value.split(',').filter(|value| !value.is_empty()) {
                if !advertised.insert(parse_fd(value.as_ref())?) {
                    anyhow::bail!("owned scheduling advertisement repeats a descriptor");
                }
            }
        }
        let owned = self
            .descriptors
            .iter()
            .map(|fd| fd.as_raw_fd())
            .collect::<BTreeSet<_>>();
        if advertised != owned {
            anyhow::bail!(
                "owned scheduling advertisements do not match CPU/fence descriptor ownership"
            );
        }
        if !owned.is_empty() && !self.environment.contains_key(CPU_FD) {
            anyhow::bail!("owned CPU/fence scheduling transport has no implicit CPU descriptor");
        }
        if owned.is_empty() && !self.environment.is_empty() {
            anyhow::bail!("runtime scheduling advertisements have no owned CPU/fence transport");
        }
        Ok(())
    }

    /// Install after the authenticated executor has removed all previous
    /// exec inheritance and authority environment. Jobserver advertisements
    /// are generated by its owned transport, never copied from the command.
    pub(super) fn apply(&self, command: &mut ProcessBuilder) -> CargoResult<()> {
        self.validate()?;
        command.inherit_jobserver(&self.jobserver);
        for descriptor in &self.descriptors {
            command.inherit_fd_for_exec(Arc::clone(descriptor))?;
        }
        for (name, value) in &self.environment {
            command.env(name, value);
        }
        Ok(())
    }

    /// macOS CLOEXEC_DEFAULT has no pre-exec callback: enumerate only this
    /// capsule's owned descriptors in explicit spawn file actions.
    pub(super) fn descriptors(&self) -> impl Iterator<Item = RawFd> + '_ {
        self.descriptors.iter().map(|fd| fd.as_raw_fd()).chain(
            self.jobserver
                .pipe_descriptors()
                .into_iter()
                .flatten()
                .map(AsRawFd::as_raw_fd),
        )
    }
}

/// Start each authenticated command with no scheduler advertisement or
/// descriptor inheritance; reapply only the actual scheduler selected above.
pub(super) fn authenticated_command(
    command: &ProcessBuilder,
    scheduling: Option<&OwnedSchedulingHandoff>,
) -> CargoResult<ProcessBuilder> {
    let mut command = command.clone();
    command.clear_exec_inheritance();
    super::strip_test_execution_authority_env(&mut command);
    remove_transport_environment(&mut command);
    if let Some(scheduling) = scheduling {
        // The retained command already signed these values. Native transport
        // and GNU-only transport must preserve the same semantic environment.
        for name in DETERMINISTIC_JOB_COUNTS {
            anyhow::ensure!(
                command.get_env(name).as_deref() == Some(std::ffi::OsStr::new("1")),
                "retained authenticated test requires signed {name}=1"
            );
        }
        scheduling.apply(&mut command)?;
    }
    Ok(command)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::MetadataExt;

    fn descriptor(path: &std::path::Path) -> Arc<OwnedFd> {
        Arc::new(std::fs::File::create(path).unwrap().into())
    }

    #[test]
    fn owned_scheduling_rejects_unbacked_and_aliased_advertisements() {
        let root = tempfile::tempdir().unwrap();
        let fd = descriptor(&root.path().join("cpu"));
        let server = Jobserver::new(1).unwrap();
        let mut configured = ProcessBuilder::new("ignored");
        configured.env(CPU_FD, fd.as_raw_fd().to_string());
        assert!(OwnedSchedulingHandoff::new(&server, Vec::new(), &configured).is_err());
        assert!(
            OwnedSchedulingHandoff::new(&server, vec![fd.clone(), fd.clone()], &configured)
                .is_err()
        );
        configured.env(FENCE_FDS, fd.as_raw_fd().to_string());
        assert!(OwnedSchedulingHandoff::new(&server, vec![fd], &configured).is_err());
    }

    #[test]
    fn scheduling_capsule_copies_only_explicit_owned_runtime_overrides() {
        let root = tempfile::tempdir().unwrap();
        let fd = descriptor(&root.path().join("cpu"));
        let server = Jobserver::new(1).unwrap();
        let mut configured = ProcessBuilder::new("ignored");
        configured
            .env(CPU_FD, fd.as_raw_fd().to_string())
            .env("TRUST_CPU_HANDOFF", "owned-runtime")
            .env("TRUST_PROOF_SESSION", "forged")
            .env("TRUST_TARGO_TEST_EXECUTION_MANIFEST", "/untrusted");
        let handoff = OwnedSchedulingHandoff::new(&server, vec![fd], &configured).unwrap();
        let mut command = ProcessBuilder::new("ignored");
        command
            .env("CARGO_MAKEFLAGS", "--jobserver-auth=0,1")
            .env("TRUST_PROOF_SESSION", "forged")
            .env("TRUST_CPU_HANDOFF", "forged-runtime");
        prepare_retained_environment(&mut command);
        command.env("ATERM_RESOURCE_JOB_V3", "unowned-private-resource-sentinel");
        let command = authenticated_command(&command, Some(&handoff)).unwrap();
        assert_eq!(
            command.get_env("TRUST_CPU_HANDOFF").unwrap(),
            "owned-runtime"
        );
        assert!(command.get_env("TRUST_PROOF_SESSION").is_none());
        assert!(command.get_env("ATERM_RESOURCE_JOB_V3").is_none());
        assert!(
            command
                .get_env("TRUST_TARGO_TEST_EXECUTION_MANIFEST")
                .is_none()
        );
        let effective = command.get_effective_envs().unwrap();
        assert!(
            !effective[std::ffi::OsStr::new("CARGO_MAKEFLAGS")]
                .to_string_lossy()
                .contains("--jobserver-auth=0,1")
        );
        let legacy = authenticated_command(&command, None).unwrap();
        assert!(!legacy.has_jobserver());
        assert!(legacy.get_env("TRUST_CPU_HANDOFF").is_none());
        for name in DETERMINISTIC_JOB_COUNTS {
            assert_eq!(legacy.get_env(name).unwrap(), "1");
        }
        let mut original_legacy = ProcessBuilder::new("ignored");
        for (name, count) in DETERMINISTIC_JOB_COUNTS.iter().zip(["3", "5", "7"]) {
            original_legacy.env(name, count);
        }
        let original_legacy = authenticated_command(&original_legacy, None).unwrap();
        for (name, count) in DETERMINISTIC_JOB_COUNTS.iter().zip(["3", "5", "7"]) {
            assert_eq!(original_legacy.get_env(name).unwrap(), count);
        }
        assert!(
            !legacy
                .get_effective_envs()
                .unwrap()
                .contains_key(std::ffi::OsStr::new("CARGO_MAKEFLAGS"))
        );
    }

    #[test]
    fn retained_execution_refuses_changed_signed_job_counts() {
        let server = Jobserver::new(1).unwrap();
        let handoff = OwnedSchedulingHandoff::jobserver_only(&server).unwrap();
        for changed in DETERMINISTIC_JOB_COUNTS {
            let mut command = ProcessBuilder::new("ignored");
            prepare_retained_environment(&mut command);
            command.env(changed, "2");
            assert!(authenticated_command(&command, Some(&handoff)).is_err());
        }
        assert!(authenticated_command(&ProcessBuilder::new("ignored"), Some(&handoff)).is_err());
    }

    #[test]
    fn retained_plan_signs_semantic_counts_and_scalar_without_resource_transport() {
        let signed_plan = |transport: &str, scalar: &str| {
            let mut command = ProcessBuilder::new("/target/retained-test");
            command.environment_snapshot(
                cargo_util::EnvironmentInputs::from_variables(std::iter::empty::<(
                    OsString,
                    OsString,
                )>())
                .unwrap(),
            );
            for name in RUNTIME_ENV.iter().chain(OTHER_TRANSPORT_ENV) {
                command.env(name, transport);
            }
            for name in DETERMINISTIC_JOB_COUNTS {
                command.env(name, "19");
            }
            command.env("TARGO_SEMANTIC_ENV_MARKER", scalar);
            prepare_retained_environment(&mut command);
            let environment = command.get_effective_envs().unwrap();
            for name in DETERMINISTIC_JOB_COUNTS
                .iter()
                .copied()
                .chain(["RUST_TEST_THREADS"])
            {
                assert_eq!(environment[std::ffi::OsStr::new(name)], "1");
            }
            assert_eq!(
                environment[std::ffi::OsStr::new("TARGO_SEMANTIC_ENV_MARKER")],
                scalar
            );
            for name in RUNTIME_ENV.iter().chain(OTHER_TRANSPORT_ENV) {
                assert!(
                    !environment.contains_key(std::ffi::OsStr::new(name)),
                    "opaque transport entered signed plan: {name}"
                );
            }
            let plan = trust_test_execution::PreparedTests {
                schema: trust_test_execution::PLAN_SCHEMA.into(),
                session: "signed-environment-regression".into(),
                host_os: std::env::consts::OS.into(),
                host_arch: std::env::consts::ARCH.into(),
                target_directory: "/target".into(),
                no_fail_fast: false,
                tests: vec![trust_test_execution::PreparedTest {
                    target: "retained-test".into(),
                    executable: "/target/retained-test".into(),
                    sha256: "a".repeat(64),
                    size: 1,
                    cwd: "/source".into(),
                    args: Vec::new(),
                    env: environment
                        .into_iter()
                        .map(|(key, value)| {
                            (key.into_string().unwrap(), value.into_string().unwrap())
                        })
                        .collect(),
                }],
            };
            plan.validate(
                &plan.session,
                &[("/target/retained-test".into(), ("a".repeat(64), 1))]
                    .into_iter()
                    .collect(),
            )
            .unwrap();
            serde_json::to_vec(&plan).unwrap()
        };
        let original = signed_plan("old-fd-and-private-recovery-endpoint", "signed-scalar-π");
        assert_eq!(
            original,
            signed_plan(
                "different-fd-and-private-recovery-endpoint",
                "signed-scalar-π"
            )
        );
        assert_ne!(
            original,
            signed_plan("old-fd-and-private-recovery-endpoint", "changed-scalar")
        );
    }

    #[cfg(all(
        any(target_os = "linux", target_os = "macos"),
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "authenticated child fixture must inspect the actual post-exec environment, not a Cargo context snapshot"
    )]
    fn authenticated_owned_scheduler_child_fixture() {
        let Some(mode) = std::env::var_os("TARGO_AUTH_SCHEDULING_FIXTURE") else {
            return;
        };
        assert!(
            std::env::var_os("PATH").is_none(),
            "authenticated exec restored ambient variables outside its closed snapshot"
        );
        assert_eq!(
            std::env::var("TARGO_SEMANTIC_ENV_MARKER").unwrap(),
            "signed-scalar-π"
        );
        assert!(
            std::env::var_os("ATERM_RESOURCE_JOB_V3").is_none(),
            "ambient resource capability leaked"
        );
        for name in [
            "TRUST_PROOF_SESSION",
            "TRUST_TARGO_PREPARED_TEST_SESSION",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
        ] {
            assert!(
                std::env::var_os(name).is_none(),
                "proof authority leaked: {name}"
            );
        }
        // File numbers may be reused by the test harness after exec; compare
        // the actual old file identity rather than assuming EBADF is stable.
        for identity in std::env::var("TARGO_AUTH_EXCLUDED_IDENTITIES")
            .unwrap()
            .split(';')
        {
            let parts = identity
                .split(',')
                .map(|part| part.parse::<u64>().unwrap())
                .collect::<Vec<_>>();
            let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
            if unsafe { libc::fstat(parts[0] as RawFd, stat.as_mut_ptr()) } == 0 {
                let stat = unsafe { stat.assume_init() };
                assert_ne!(
                    (stat.st_dev as u64, stat.st_ino as u64),
                    (parts[1], parts[2]),
                    "excluded file crossed exec"
                );
            }
        }
        if mode == "owned" || mode == "jobserver" {
            // SAFETY: the parent constructed this exact owned pipe, retained
            // it throughout authenticated exec, and supplied its real numbers.
            let server = unsafe { Jobserver::from_env() }.unwrap().unwrap();
            // The parent waits for this exact child and never reads from its
            // one-credit pipe. This is its sole consumer, so the observed
            // population makes blocking acquire safe even for an inherited
            // anonymous macOS pipe with no try_acquire implementation.
            assert_eq!(
                server.client().available().unwrap(),
                1,
                "same owned pool must supply exactly one real credit"
            );
            let credit = server.client().acquire().unwrap();
            assert_eq!(server.client().available().unwrap(), 0);
            drop(credit);
            assert_eq!(server.client().available().unwrap(), 1);
            for name in DETERMINISTIC_JOB_COUNTS {
                assert_eq!(
                    std::env::var(name).unwrap(),
                    "1",
                    "signed count changed: {name}"
                );
            }
            if mode == "owned" {
                assert_eq!(std::env::var("TRUST_CPU_HANDOFF").unwrap(), "owned-runtime");
                for name in [CPU_FD, FENCE_FDS] {
                    let fd = std::env::var(name).unwrap().parse::<RawFd>().unwrap();
                    assert_eq!(unsafe { libc::write(fd, b"native".as_ptr().cast(), 6) }, 6);
                }
            } else {
                for name in RUNTIME_ENV {
                    assert!(
                        std::env::var_os(name).is_none(),
                        "GNU-only scheduler invented native transport: {name}"
                    );
                }
            }
        } else {
            assert_eq!(mode, "legacy");
            for name in DETERMINISTIC_JOB_COUNTS {
                assert_eq!(
                    std::env::var(name).unwrap(),
                    "1",
                    "legacy signed count changed: {name}"
                );
            }
            for name in RUNTIME_ENV
                .iter()
                .copied()
                .chain(["CARGO_MAKEFLAGS", "CARGO_JOBSERVER_HANDOFF"])
            {
                assert!(
                    std::env::var_os(name).is_none(),
                    "legacy scheduler leaked: {name}"
                );
            }
        }
    }

    #[cfg(all(
        any(target_os = "linux", target_os = "macos"),
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "ambient environment is the explicit nonvacuity control for authenticated child exclusion"
    )]
    fn authenticated_launch_retains_only_owned_scheduling_transport() {
        assert!(
            std::env::var_os("PATH").is_some(),
            "ambient snapshot control must be nonvacuous"
        );
        let root = tempfile::tempdir().unwrap();
        let executable = root.path().join("authorized-test");
        std::fs::copy(std::env::current_exe().unwrap(), &executable).unwrap();
        let executable = executable.canonicalize().unwrap();
        let (sha256, size) =
            super::super::exact_regular_test_executable_identity(&executable).unwrap();
        let authority = super::super::TestExecutionAuthority {
            executables: [(
                executable.clone(),
                super::super::TestExecutionAuthorityEntry {
                    target: "owned-scheduling".into(),
                    path: executable.to_str().unwrap().into(),
                    sha256,
                    size,
                },
            )]
            .into_iter()
            .collect(),
            prepared: None,
        };
        let cpu_path = root.path().join("cpu");
        let fence_path = root.path().join("fence");
        let cpu = descriptor(&cpu_path);
        let fence = descriptor(&fence_path);
        let unrelated = descriptor(&root.path().join("unrelated"));
        let proof_guard = descriptor(&root.path().join("proof-guard"));
        let server = Jobserver::new(1).unwrap();
        let mut runtime = ProcessBuilder::new("owned-runtime");
        runtime
            .env(CPU_FD, cpu.as_raw_fd().to_string())
            .env(FENCE_FDS, fence.as_raw_fd().to_string())
            .env("TRUST_CPU_HANDOFF", "owned-runtime");
        for name in DETERMINISTIC_JOB_COUNTS {
            runtime.env(name, "19");
        }
        let scheduling = OwnedSchedulingHandoff::new(&server, vec![cpu, fence], &runtime).unwrap();
        let identities = [&unrelated, &proof_guard]
            .into_iter()
            .map(|fd| {
                // Clone only to inspect identity without changing the offset.
                let metadata = std::fs::File::from(fd.try_clone().unwrap())
                    .metadata()
                    .unwrap();
                format!("{},{},{}", fd.as_raw_fd(), metadata.dev(), metadata.ino())
            })
            .collect::<Vec<_>>()
            .join(";");
        let mut command = ProcessBuilder::new(&executable);
        command
            .environment_snapshot(cargo_util::EnvironmentInputs::from_variables(std::iter::empty::<(OsString, OsString)>()).unwrap())
            .arg("--exact")
            .arg("ops::cargo_test::auth_scheduling::tests::authenticated_owned_scheduler_child_fixture")
            .arg("--test-threads=1")
            .env("TARGO_AUTH_EXCLUDED_IDENTITIES", identities)
            .env("TARGO_SEMANTIC_ENV_MARKER", "signed-scalar-π")
            .env("ATERM_RESOURCE_JOB_V3", "unowned-private-resource-sentinel")
            .env("TRUST_PROOF_SESSION", "forged")
            .env("TRUST_TARGO_PREPARED_TEST_SESSION", "forged")
            .env("TRUST_TARGO_TEST_EXECUTION_MANIFEST", "/forged")
            .env("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256", "0".repeat(64))
            .env("CARGO_MAKEFLAGS", "--jobserver-auth=0,1")
            .env(CPU_FD, "0")
            .env("TRUST_CPU_HANDOFF", "forged-runtime");
        prepare_retained_environment(&mut command);
        command.inherit_fd_for_exec(unrelated).unwrap();
        command.hold_fd_through_exec(proof_guard).unwrap();
        command.env("TARGO_AUTH_SCHEDULING_FIXTURE", "owned");
        super::super::execute_authenticated_test_with_cancel_and_scheduling(
            &authority,
            &executable,
            &command,
            &mut || false,
            Some(&scheduling),
        )
        .unwrap();
        assert_eq!(std::fs::read(&cpu_path).unwrap(), b"native");
        assert_eq!(std::fs::read(&fence_path).unwrap(), b"native");
        command.env("TARGO_AUTH_SCHEDULING_FIXTURE", "jobserver");
        let jobserver_only = OwnedSchedulingHandoff::jobserver_only(&server).unwrap();
        super::super::execute_authenticated_test_with_cancel_and_scheduling(
            &authority,
            &executable,
            &command,
            &mut || false,
            Some(&jobserver_only),
        )
        .unwrap();
        command.env("TARGO_AUTH_SCHEDULING_FIXTURE", "legacy");
        super::super::execute_authenticated_test_with_cancel_and_scheduling(
            &authority,
            &executable,
            &command,
            &mut || false,
            None,
        )
        .unwrap();
    }
}
