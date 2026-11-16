//! Shared CLOSED compiler-query ProcessBuilder consistency checks.
//! Distinct resolver/workload owners retain their own roles, native admission,
//! actual SDK/CPU/GNU custody, lifecycle and raw observations. Profile data
//! grants nothing and cannot convert one request purpose into another.
use cargo_util::ProcessBuilder;
use std::ffi::OsString;
use std::io;
use std::os::unix::ffi::OsStrExt as _;
use trust_resource_controller::CommandSpec;
use trust_resource_controller::resolver::{ResolverInvocation, classify_resolver_query};
use trust_resource_controller::workload::WorkloadInvocation;

pub(crate) struct Profile<'a> {
    purpose: &'static str,
    program: &'a [u8],
    compiler: &'a [u8],
    cargo_home: &'a [u8],
    cwd: &'a [u8],
    paired: Option<&'a trust_resource_controller::paired_qualification::PairedInvocation>,
    native_job: Option<&'a trust_resource_controller::native_job::Plan>,
}
impl<'a> Profile<'a> {
    pub(crate) fn resolver(invocation: &'a ResolverInvocation) -> Self {
        Self {
            purpose: "resolver",
            program: &invocation.program,
            compiler: &invocation.compiler,
            cargo_home: &invocation.cargo_home,
            cwd: &invocation.cwd,
            paired: None,
            native_job: None,
        }
    }
    pub(crate) fn workload(invocation: &'a WorkloadInvocation) -> Self {
        Self {
            purpose: "workload",
            program: &invocation.program.path,
            compiler: &invocation.compiler.path,
            cargo_home: &invocation.cargo_home,
            cwd: &invocation.cwd,
            paired: None,
            native_job: None,
        }
    }
    pub(crate) fn native_job(plan: &'a trust_resource_controller::native_job::Plan) -> Self {
        Self { purpose: "native job", program: &plan.inputs.program.path,
            compiler: &plan.inputs.compiler.path, cargo_home: &plan.inputs.cargo_home,
            cwd: &plan.inputs.cwd, paired: None, native_job: Some(plan) }
    }
    pub(crate) fn paired(
        invocation: &'a trust_resource_controller::paired_qualification::PairedInvocation,
    ) -> Self {
        let mut profile = Self::workload(&invocation.consumer);
        profile.purpose = "paired qualification";
        profile.paired = Some(invocation);
        profile
    }
    pub(crate) fn paired_root(
        invocation: &'a trust_resource_controller::paired_qualification::PairedInvocation,
    ) -> Self {
        // Normal config extras are negotiated for actual compiler queries,
        // after configuration. Original root startup remains fixed env6.
        let mut profile = Self::workload(&invocation.consumer);
        profile.purpose = "paired qualification root";
        profile
    }
}
fn error(message: impl Into<String>) -> io::Error {
    io::Error::other(message.into())
}
pub(crate) fn validate_process_profile(
    invocation: &Profile<'_>,
    process: &ProcessBuilder,
    command: &CommandSpec,
) -> io::Result<()> {
    if process.has_action_sandbox()
        || process.get_stdin().is_some_and(|s| !s.is_empty())
        || command.program.as_slice() != invocation.compiler
        || (command.cwd.as_slice() != invocation.cwd
            && Some(command.cwd.as_slice())
                != invocation.paired.map(|plan| plan.ay.root.as_slice())
            && !invocation.native_job.is_some_and(|plan| plan.sources.iter().any(|source| source.root == command.cwd)))
        || command.arg0.is_some()
    {
        return Err(error(format!(
            "{} refuses custom wrappers, executable/cwd changes, sandbox or producing stdin",
            invocation.purpose
        )));
    }
    classify_resolver_query(&command.args)?;
    let mut declared = fixed_environment(invocation);
    for (name, value) in process.get_envs() {
        if let Some(value) = value {
            let expected = match name.as_str() {
                "CARGO" => Some(invocation.program),
                "RUSTC" => Some(invocation.compiler),
                "CARGO_HOME" => Some(invocation.cargo_home),
                "CARGO_CACHE_RUSTC_INFO" => Some(b"0".as_slice()),
                "LANG" | "LC_ALL" => Some(b"C".as_slice()),
                _ => None,
            };
            if let Some(expected) = expected {
                if value.as_os_str().as_bytes() != expected {
                    return Err(error(format!(
                        "{} compiler environment differs from exact closed semantics",
                        invocation.purpose
                    )));
                }
            } else if invocation.paired.is_some() {
                // Pure shared DATA validation below, no invented Request/FD.
                // Even runtime/plumbing keys cannot enter via project config.
                declared.push((
                    name.as_bytes().to_vec(),
                    value.as_os_str().as_bytes().to_vec(),
                ));
            } else {
                return Err(error(format!(
                    "{} refuses configured compiler environment {name}",
                    invocation.purpose
                )));
            }
        }
    }
    if let Some(plan) = invocation.paired {
        trust_resource_controller::paired_qualification::query::validate_environment(
            plan, &declared,
        )?;
    }
    Ok(())
}
fn fixed_environment(invocation: &Profile<'_>) -> Vec<(Vec<u8>, Vec<u8>)> {
    vec![
        (b"LANG".to_vec(), b"C".to_vec()),
        (b"LC_ALL".to_vec(), b"C".to_vec()),
        (b"CARGO".to_vec(), invocation.program.to_vec()),
        (b"RUSTC".to_vec(), invocation.compiler.to_vec()),
        (b"CARGO_HOME".to_vec(), invocation.cargo_home.to_vec()),
        (b"CARGO_CACHE_RUSTC_INFO".to_vec(), b"0".to_vec()),
    ]
}
pub(crate) fn validate_effective_environment(
    invocation: &Profile<'_>,
    environment: &[(Vec<u8>, Vec<u8>)],
    runtime: &[(OsString, OsString)],
) -> io::Result<()> {
    forwarded_environment(invocation, environment, runtime).map(|_| ())
}
pub(crate) fn forwarded_environment(
    invocation: &Profile<'_>,
    environment: &[(Vec<u8>, Vec<u8>)],
    runtime: &[(OsString, OsString)],
) -> io::Result<Vec<(Vec<u8>, Vec<u8>)>> {
    let mut forwarded = fixed_environment(invocation);
    let required = [
        (b"LANG".as_slice(), b"C".as_slice()),
        (b"LC_ALL", b"C"),
        (b"CARGO", invocation.program),
        (b"RUSTC", invocation.compiler),
        (b"CARGO_HOME", invocation.cargo_home),
        (b"CARGO_CACHE_RUSTC_INFO", b"0"),
    ];
    for (name, value) in required {
        if environment
            .iter()
            .filter(|(key, _)| key.as_slice() == name)
            .count()
            != 1
            || !environment
                .iter()
                .any(|(key, actual)| key == name && actual == value)
        {
            return Err(error(format!(
                "{} query effective environment differs at {}",
                invocation.purpose,
                String::from_utf8_lossy(name)
            )));
        }
    }
    for (name, value) in environment {
        if required.iter().any(|(key, _)| key == &name.as_slice()) {
            continue;
        }
        // Host-supplied original custody plumbing is not arbitrary managed
        // semantics. Actual SDK/GNU/CPU ownership is independently checked;
        // these strings never grant capacity or attest the child environment.
        if matches!(
            name.as_slice(),
            b"ATERM_SESSION_ID"
                | b"ATERM_PARENT_SESSION_ID"
                | b"ATERM_RESOURCE_INSPECTOR"
                | b"ATERM_SDK_LEASE_V3"
                | b"MAKEFLAGS"
                | b"MFLAGS"
                | b"CARGO_MAKEFLAGS"
        ) {
            continue;
        }
        // CoreFoundation's pre-main initializer can add this one variable
        // after env_clear. Only the same real/effective UID and the supported
        // Roman/US zero defaults are equivalent under the clean child runtime.
        // The observed bytes stay in the report; this is no origin attestation.
        #[cfg(target_os = "macos")]
        if name == b"__CF_USER_TEXT_ENCODING"
            && darwin_default_encoding(
                value,
                unsafe { libc::getuid() },
                unsafe { libc::geteuid() },
                true,
            )
        {
            continue;
        }
        if runtime.iter().any(|(key, actual)| {
            key.as_os_str().as_bytes() == name && actual.as_os_str().as_bytes() == value
        }) {
            continue;
        }
        if invocation.paired.is_some() {
            forwarded.push((name.clone(), value.clone()));
            continue;
        }
        return Err(error(format!(
            "{} refuses unsupported inherited semantic environment {}",
            invocation.purpose,
            String::from_utf8_lossy(name)
        )));
    }
    if let Some(plan) = invocation.paired {
        trust_resource_controller::paired_qualification::query::validate_environment(
            plan, &forwarded,
        )?;
    }
    Ok(forwarded)
}
pub(crate) fn darwin_default_encoding(value: &[u8], uid: u32, euid: u32, darwin: bool) -> bool {
    darwin
        && uid == euid
        && (value == format!("0x{uid:X}:0x0:0x0").as_bytes()
            || value == format!("0x{uid:X}:0:0").as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_resource_controller::workload::InputFile;

    fn invocation() -> WorkloadInvocation {
        let input = |name: &str| InputFile {
            path: name.as_bytes().to_vec(),
            sha256: [1; 32],
        };
        WorkloadInvocation {
            invocation: [1; 16],
            observed_host_store: None,
            root: b"/sdk".to_vec(),
            program: input("/sdk/bin/targo"),
            compiler: input("/sdk/bin/trustc"),
            cwd: b"/source".to_vec(),
            cargo_home: b"/cargo".to_vec(),
            output_root: b"/output".to_vec(),
            refutation_step: input("/proof/step"),
            refutation_loop: input("/proof/loop"),
            trust_spec_source: input("/spec/source"),
            repetitions: 1,
            timeout_ns: 1,
        }
    }
    fn command(process: &ProcessBuilder) -> CommandSpec {
        let actual = process.build_command();
        CommandSpec {
            program: actual.get_program().as_bytes().to_vec(),
            arg0: process.get_arg0().map(|value| value.as_bytes().to_vec()),
            args: actual
                .get_args()
                .map(|value| value.as_bytes().to_vec())
                .collect(),
            cwd: process.get_cwd().unwrap().as_os_str().as_bytes().to_vec(),
            environment: process
                .get_effective_envs()
                .unwrap()
                .into_iter()
                .map(|(name, value)| {
                    (
                        name.as_os_str().as_bytes().to_vec(),
                        value.as_os_str().as_bytes().to_vec(),
                    )
                })
                .collect(),
        }
    }
    #[test]
    fn workload_query_profile_binds_its_own_exact_inputs_and_has_no_producing_or_environment_fallback()
     {
        let invocation = invocation();
        invocation.validate().unwrap();
        let profile = Profile::workload(&invocation);
        let mut process = ProcessBuilder::new("/sdk/bin/trustc");
        process.arg("-vV").cwd("/source");
        // ProcessBuilder preserves Cargo's ordinary inherited environment;
        // remove its observed keys on this builder only, never globally.
        for name in process.get_effective_envs().unwrap().into_keys() {
            process.env_remove(name.to_str().expect("test environment key is UTF8"));
        }
        for (name, value) in [
            ("LANG", "C"),
            ("LC_ALL", "C"),
            ("CARGO", "/sdk/bin/targo"),
            ("RUSTC", "/sdk/bin/trustc"),
            ("CARGO_HOME", "/cargo"),
            ("CARGO_CACHE_RUSTC_INFO", "0"),
        ] {
            process.env(name, value);
        }
        let validate = |process: &ProcessBuilder| {
            let observed = command(process);
            validate_process_profile(&profile, process, &observed)
                .and_then(|()| validate_effective_environment(&profile, &observed.environment, &[]))
        };
        validate(&process).unwrap();
        for (name, value) in [
            ("RUSTC_WRAPPER", "/wrapper"),
            ("RUSTC_BOOTSTRAP", "1"),
            ("LD_PRELOAD", "/override"),
            ("CARGO_HOME", "/another-cache"),
        ] {
            let mut changed = process.clone();
            changed.env(name, value);
            assert!(validate(&changed).is_err(), "unsupported configured {name}");
        }
        let mut producing = process.clone();
        producing.arg("--emit=link");
        assert!(validate(&producing).is_err());
        let mut changed = process.clone();
        changed.cwd("/another-source");
        assert!(validate(&changed).is_err());
        let mut missing = process.clone();
        missing.env_remove("CARGO_HOME");
        assert!(validate(&missing).is_err());
    }
    #[test]
    fn paired_profile_accepts_only_its_two_bound_workspaces_without_expanding_v1() {
        use trust_resource_controller::paired_qualification::{AySubject, PairedInvocation};
        let input = |path: &str| trust_resource_controller::workload::InputFile {
            path: path.as_bytes().to_vec(),
            sha256: [1; 32],
        };
        let plan = PairedInvocation {
            consumer: invocation(),
            ay: AySubject {
                root: b"/ay".to_vec(),
                workspace_manifest: input("/ay/Cargo.toml"),
                crate_manifest: input("/ay/crates/ay-proof-common/Cargo.toml"),
                lockfile: input("/ay/Cargo.lock"),
                cargo_config: input("/ay/.cargo/config.toml"),
                toolchain_config: input("/ay/rust-toolchain.toml"),
                source_commit: [1; 20],
                crate_tree: [2; 20],
            },
        };
        plan.validate().unwrap();
        let paired = Profile::paired(&plan);
        let old = Profile::workload(&plan.consumer);
        let mut query = ProcessBuilder::new("/sdk/bin/trustc");
        query.arg("-vV").cwd("/ay");
        validate_process_profile(&paired, &query, &command(&query)).unwrap();
        assert!(validate_process_profile(&old, &query, &command(&query)).is_err());
        query.cwd("/source");
        validate_process_profile(&paired, &query, &command(&query)).unwrap();
        for changed in ["/ay/child", "/ay-sibling", "/source/child", "/other"] {
            query.cwd(changed);
            assert!(
                validate_process_profile(&paired, &query, &command(&query)).is_err(),
                "{changed}"
            );
        }
        query.cwd("/ay").arg("--emit=link");
        assert!(validate_process_profile(&paired, &query, &command(&query)).is_err());
        let mut query = ProcessBuilder::new("/sdk/bin/trustc");
        query.arg("-vV").cwd("/ay").env("SCCACHE_CACHE_SIZE", "50G");
        // Distinct paired50/v2 now carries normal config values unchanged.
        // The old workload50/v1 profile remains exact6 and refuses them.
        validate_process_profile(&paired, &query, &command(&query)).unwrap();
        assert!(validate_process_profile(&old, &query, &command(&query)).is_err());
        let mut semantic = fixed_environment(&paired);
        semantic.push((b"SCCACHE_CACHE_SIZE".to_vec(), b"50G".to_vec()));
        semantic.push((
            b"CC_x86_64_unknown_linux_musl".to_vec(),
            b"/ay/scripts/zig-cc-x86_64-linux-musl.sh".to_vec(),
        ));
        assert_eq!(
            forwarded_environment(&paired, &semantic, &[]).unwrap(),
            semantic
        );
        assert!(validate_effective_environment(&old, &semantic, &[]).is_err());
        assert!(
            validate_effective_environment(&Profile::paired_root(&plan), &semantic, &[]).is_err(),
            "config extras cannot silently enter original root startup"
        );
        let mut protected = query.clone();
        protected.env("MAKEFLAGS", "-j99");
        assert!(
            validate_process_profile(&paired, &protected, &command(&protected)).is_err(),
            "project config cannot impersonate inherited scheduling runtime"
        );
        let mut wrong = semantic.clone();
        wrong.last_mut().unwrap().1 = b"/foreign/script".to_vec();
        assert!(forwarded_environment(&paired, &wrong, &[]).is_err());
        query.env("LD_PRELOAD", "/unowned/override");
        assert!(validate_process_profile(&paired, &query, &command(&query)).is_err());
    }
}
