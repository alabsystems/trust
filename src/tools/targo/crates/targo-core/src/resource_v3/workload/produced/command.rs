//! ProcessBuilder consistency only. Registration, phase and native execution
//! stay with their live original owners; these projections grant nothing.
use std::ffi::OsString;
use std::io;
use std::os::unix::ffi::OsStrExt as _;

use cargo_util::ProcessBuilder;
use trust_resource_controller::{CommandSpec, workload::host::produced};

pub(crate) fn command(
    process: &ProcessBuilder,
    runtime: &[(OsString, OsString)],
) -> io::Result<(CommandSpec, CommandSpec)> {
    if process.has_action_sandbox()
        || process.get_arg0().is_some()
        || process.get_stdin().is_some_and(|bytes| !bytes.is_empty())
    {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "produced native work refuses a wrapper, sandbox or producing stdin",
        ));
    }
    let actual = process.build_command();
    let observed = CommandSpec {
        program: actual.get_program().as_bytes().to_vec(),
        arg0: None,
        args: actual
            .get_args()
            .map(|value| value.as_bytes().to_vec())
            .collect(),
        cwd: process
            .get_cwd()
            .ok_or_else(|| {
                io::Error::other("produced native command has no actual working directory")
            })?
            .as_os_str()
            .as_bytes()
            .to_vec(),
        environment: process
            .get_effective_envs()?
            .into_iter()
            .map(|(name, value)| {
                (
                    name.as_os_str().as_bytes().to_vec(),
                    value.as_os_str().as_bytes().to_vec(),
                )
            })
            .collect(),
    };
    let mut command = observed.clone();
    command
        .environment
        .retain(|(name, _)| !produced::protected_environment_name(name));
    // Cargo's normal generated loader environment is accepted only when its
    // exact value agrees with this SAME retained image's native runtime. The
    // host re-injects that held runtime; arbitrary caller overrides refuse.
    for (name, value) in &command.environment {
        if produced::loader_override_name(name)
            && !runtime.iter().any(|(key, actual)| {
                key.as_os_str().as_bytes() == name && actual.as_os_str().as_bytes() == value
            })
        {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "produced native command has an unbound loader environment override",
            ));
        }
    }
    command
        .environment
        .retain(|(name, _)| !produced::loader_override_name(name));
    Ok((command, observed))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_builder_projection_preserves_semantics_and_refuses_unbound_runtime_overrides() {
        let mut process = ProcessBuilder::new("/output/test");
        process.arg("--list").cwd("/source");
        // Clear only this builder's inherited projection, never the process.
        for name in process.get_effective_envs().unwrap().into_keys() {
            process.env_remove(name.to_str().unwrap());
        }
        process.env("NUM_JOBS", "7").env("CARGO_HOME", "/cargo");
        process.env("MAKEFLAGS", "actual-original-transport");
        process.env("ATERM_RESOURCE_JOB_V3", "private-original-root");
        let runtime = vec![(
            OsString::from("DYLD_LIBRARY_PATH"),
            OsString::from("/output:/sdk/lib"),
        )];
        process.env("DYLD_LIBRARY_PATH", "/output:/sdk/lib");
        let (semantic, observed) = command(&process, &runtime).unwrap();
        assert_eq!(semantic.args, [b"--list".to_vec()]);
        assert_eq!(
            semantic.environment,
            [
                (b"CARGO_HOME".to_vec(), b"/cargo".to_vec()),
                (b"NUM_JOBS".to_vec(), b"7".to_vec()),
            ]
        );
        assert!(
            observed
                .environment
                .iter()
                .any(|(key, _)| key == b"DYLD_LIBRARY_PATH")
        );
        assert!(
            observed
                .environment
                .iter()
                .any(|(key, _)| key == b"MAKEFLAGS")
        );
        for (name, value) in [("DYLD_LIBRARY_PATH", "/foreign"), ("LD_PRELOAD", "/inject")] {
            let mut changed = process.clone();
            changed.env(name, value);
            assert!(command(&changed, &runtime).is_err());
        }
        let mut changed = process.clone();
        changed.arg0("wrapper");
        assert!(command(&changed, &runtime).is_err());
    }
}
