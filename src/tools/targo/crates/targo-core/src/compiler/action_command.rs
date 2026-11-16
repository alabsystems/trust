//! Trust: identity of the prepared confined compiler command.
//!
//! Files and platform values have their own captures. This binds the command
//! that consumes them, without turning scheduler transport addresses into
//! compilation inputs. Observed env-dep values still use the full environment.

use std::ffi::OsStr;
use std::sync::Arc;

use anyhow::bail;
use cargo_util::{EnvironmentInputs, ProcessBuilder, Sha256};

use super::{BuildRunner, Unit};
use crate::CargoResult;

#[derive(Debug)]
pub(super) struct CommandInputs {
    digest: String,
    environment: EnvironmentInputs,
    native: bool,
}

impl CommandInputs {
    pub(super) fn capture(command: &ProcessBuilder) -> CargoResult<Self> {
        Self::capture_inner(command, false)
    }
    /// An original native command may inherit its caller's stdin. This records
    /// that fact; the selected process owner must independently refuse stdin it
    /// cannot deliver. Confined command identity keeps its strict requirement.
    pub(super) fn capture_native(command: &ProcessBuilder) -> CargoResult<Self> {
        Self::capture_inner(command, true)
    }
    fn capture_inner(command: &ProcessBuilder, native: bool) -> CargoResult<Self> {
        let environment = EnvironmentInputs::capture_effective(command)?;
        // Hash the actual OS command, including the generated sandbox policy
        // and wrapper arguments, rather than just the logical compiler argv.
        let prepared = command.build_command();
        let mut hash = Sha256::new();
        let mut field = |value: &[u8]| {
            hash.update(&(value.len() as u64).to_le_bytes());
            hash.update(value);
        };
        field(if native {
            b"targo-original-native-command-v1"
        } else {
            b"targo-confined-command-v1"
        });
        field(prepared.get_program().as_encoded_bytes());
        field(if command.get_arg0().is_some() {
            b"explicit-arg0"
        } else {
            b"default-arg0"
        });
        field(
            command
                .get_arg0()
                .map(OsStr::as_encoded_bytes)
                .unwrap_or_default(),
        );
        let args: Vec<_> = prepared.get_args().collect();
        field(&(args.len() as u64).to_le_bytes());
        let mut bytes = 0_usize;
        for argument in args {
            bytes = bytes
                .checked_add(argument.len())
                .ok_or_else(|| anyhow::anyhow!("command argument size overflow"))?;
            if bytes > 16 * 1024 * 1024 {
                bail!("confined command arguments exceed their size bound");
            }
            field(argument.as_encoded_bytes());
        }
        let cwd = command
            .get_cwd()
            .ok_or_else(|| anyhow::anyhow!("confined command has no working directory"))?;
        if !cwd.is_absolute() {
            bail!("confined command working directory must be absolute");
        }
        field(cwd.as_os_str().as_encoded_bytes());
        field(cwd.canonicalize()?.as_os_str().as_encoded_bytes());
        match command.get_stdin() {
            Some(stdin) => {
                if native {
                    field(b"explicit-stdin");
                }
                field(stdin);
            }
            None if native => field(b"inherited-stdin"),
            None => bail!("confined command cannot inherit stdin"),
        }
        // Read the complete spawn-time map. Scheduler and Targo broker
        // addresses are control transport. If Rust source observes them
        // through env!/option_env!, retained dep-info compares their full
        // actual values and refuses a hit when those values change.
        for (name, value) in environment.iter() {
            if (command.has_jobserver()
                && (name == "CARGO_MAKEFLAGS" || name == cargo_util::DESCENDANT_HANDOFF_ENV))
                || name == crate::util::process_authority::TARGO_NESTED_UNVERIFIED_BROKER_ENV
                || name == crate::util::process_authority::LEGACY_TARGO_NESTED_UNVERIFIED_BROKER_ENV
            {
                continue;
            }
            field(name.as_encoded_bytes());
            field(value.as_encoded_bytes());
        }
        Ok(Self {
            digest: hash.finish_hex(),
            environment,
            native,
        })
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    pub fn environment(&self) -> &EnvironmentInputs {
        &self.environment
    }

    pub fn ensure_matches(&self, command: &ProcessBuilder) -> CargoResult<()> {
        if Self::capture_inner(command, self.native)?.digest != self.digest {
            bail!("confined compiler command changed after input capture");
        }
        Ok(())
    }
}

pub(super) fn is_transport_environment(name: &str) -> bool {
    matches!(name, "CARGO_MAKEFLAGS")
        || name == cargo_util::DESCENDANT_HANDOFF_ENV
        || name == crate::util::process_authority::TARGO_NESTED_UNVERIFIED_BROKER_ENV
        || name == crate::util::process_authority::LEGACY_TARGO_NESTED_UNVERIFIED_BROKER_ENV
}

pub(super) fn for_unit(
    build: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    source_inputs: Option<&super::action_inputs::SourceInputs>,
) -> CargoResult<Option<Arc<CommandInputs>>> {
    if !build.bcx.confines(unit) {
        return Ok(None);
    }
    // Trust: the caller already captured/revalidated this planning boundary.
    // Share that exact input with command preparation, rather than rehashing
    // the whole source tree a second time in the same phase.
    if let Some(inputs) = source_inputs {
        inputs.ensure_bound_to(unit.pkg.root())?;
    }
    if build.bcx.shared_dependency_units.contains(unit) && source_inputs.is_none() {
        bail!("shared dependency compilation requires a separate captured source tree");
    }
    if let Some(inputs) = build.action_commands.get(unit) {
        return Ok(Some(Arc::clone(inputs)));
    }
    let (command, ..) = super::prepare_rustc(build, unit)?;
    let inputs = Arc::new(CommandInputs::capture(&command)?);
    build
        .action_commands
        .insert(unit.clone(), Arc::clone(&inputs));
    Ok(Some(inputs))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn command(root: &std::path::Path) -> ProcessBuilder {
        let empty = EnvironmentInputs::capture_for(&ProcessBuilder::new("unused"), &[]).unwrap();
        let mut command = ProcessBuilder::new(std::env::current_exe().unwrap());
        command
            .cwd(root)
            .stdin(Vec::new())
            .environment_snapshot(empty);
        command
    }

    #[test]
    fn native_stdin_observation_does_not_weaken_confined_input_identity() {
        let root = tempfile::tempdir().unwrap();
        let mut native = ProcessBuilder::new("not-executed");
        native.cwd(root.path());
        assert!(CommandInputs::capture(&native).is_err());
        let observed = CommandInputs::capture_native(&native).unwrap();
        observed.ensure_matches(&native).unwrap();
        native.stdin(Vec::new());
        assert!(observed.ensure_matches(&native).is_err());
        CommandInputs::capture(&native)
            .unwrap()
            .ensure_matches(&native)
            .unwrap();
    }

    #[test]
    fn command_identity_binds_arguments_environment_cwd_and_stdin() {
        let root = tempfile::tempdir().unwrap();
        let mut original = command(root.path());
        original.arg("input.rs").env("DECLARED", "first");
        let inputs = CommandInputs::capture(&original).unwrap();
        inputs.ensure_matches(&original).unwrap();
        let mut changed = original.clone();
        changed.arg("--cfg=changed");
        assert!(inputs.ensure_matches(&changed).is_err());
        let mut changed = original.clone();
        changed.env("DECLARED", "second");
        assert!(inputs.ensure_matches(&changed).is_err());
        let mut changed = original.clone();
        changed.stdin(b"different".to_vec());
        assert!(inputs.ensure_matches(&changed).is_err());
        let other = tempfile::tempdir().unwrap();
        let mut changed = original;
        changed.cwd(other.path());
        assert!(inputs.ensure_matches(&changed).is_err());
    }

    #[test]
    fn scheduler_transport_is_observed_but_does_not_define_compilation_identity() {
        let root = tempfile::tempdir().unwrap();
        let mut first = command(root.path());
        let mut second = first.clone();
        first.inherit_jobserver(&cargo_util::Jobserver::new(1).unwrap());
        second.inherit_jobserver(&cargo_util::Jobserver::new(2).unwrap());
        let first = CommandInputs::capture(&first).unwrap();
        let second = CommandInputs::capture(&second).unwrap();
        assert_eq!(first.digest(), second.digest());
        assert_ne!(
            first.environment().get(OsStr::new("CARGO_MAKEFLAGS")),
            second.environment().get(OsStr::new("CARGO_MAKEFLAGS"))
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn generated_sandbox_policy_is_part_of_the_command_identity() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("input");
        std::fs::write(&path, b"input").unwrap();
        let mut command = command(root.path());
        let executable = std::env::current_exe().unwrap();
        let mut initial = cargo_util::ActionSandbox::new();
        initial.executable(&executable).unwrap();
        initial.write_directory(root.path()).unwrap();
        command.action_sandbox(initial).unwrap();
        let inputs = CommandInputs::capture(&command).unwrap();
        let mut expanded = cargo_util::ActionSandbox::new();
        expanded.executable(&executable).unwrap();
        expanded.write_directory(root.path()).unwrap();
        expanded.read_file(&path).unwrap();
        command.action_sandbox(expanded).unwrap();
        assert!(inputs.ensure_matches(&command).is_err());
    }
}
