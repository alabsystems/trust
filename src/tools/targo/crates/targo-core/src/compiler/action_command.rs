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
    /// Trust (DC-18b): the paths the digest reads as tokens (a shared
    /// member's command); empty otherwise.
    relocated: Relocation,
    /// Trust (DC-18b): each library the command passes with `--extern`.
    externs: Vec<std::path::PathBuf>,
}

/// Trust (DC-18b): what the workspace directory reads as in a relocated
/// command's digest. A NUL is in no argument, path or environment value.
const WORKSPACE_TOKEN: &[u8] = b"\0targo-workspace\0";
/// Trust (DC-18b): what a shared member's own store slot reads as, so that
/// the digest, which names the slot, can choose it.
const SLOT_TOKEN: &[u8] = b"\0targo-slot\0";

/// A byte that continues a file name: a spelling followed or preceded by one
/// is part of another name (`/a/w` in `/a/w-data` or `/x/a/w`).
fn name_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || b"-_.~+@".contains(&byte) || byte >= 0x80
}

/// Trust (DC-18b): the directories a relocated digest reads as tokens, each
/// spelling with its token, longest first.
#[derive(Clone, Debug, Default)]
struct Relocation {
    spellings: Vec<(Vec<u8>, &'static [u8])>,
}

impl Relocation {
    fn new(directories: &[(&std::path::Path, &'static [u8])]) -> CargoResult<Self> {
        let mut spellings = Vec::new();
        for (directory, token) in directories {
            spellings.push((directory.as_os_str().as_encoded_bytes().to_vec(), *token));
            if let Ok(canonical) = directory.canonicalize() {
                spellings.push((canonical.as_os_str().as_encoded_bytes().to_vec(), *token));
            }
        }
        spellings.retain(|(spelling, _)| !spelling.is_empty() && spelling != b"/");
        // Longest first, so a spelling that extends another reads whole.
        spellings.sort_by(|left, right| right.0.len().cmp(&left.0.len()).then(left.cmp(right)));
        spellings.dedup();
        if !spellings.iter().any(|(_, token)| *token == WORKSPACE_TOKEN) {
            bail!("a relocated command needs its workspace directory");
        }
        Ok(Relocation { spellings })
    }

    fn is_empty(&self) -> bool {
        self.spellings.is_empty()
    }

    /// Each whole occurrence of a spelling, read as its token: one that
    /// starts and ends a file name. Two commands read alike only where they
    /// differ in nothing but where their own checkout and slot are: a path
    /// into another checkout keeps its spelling.
    fn apply<'v>(&self, value: &'v [u8]) -> std::borrow::Cow<'v, [u8]> {
        if self.spellings.is_empty() {
            return std::borrow::Cow::Borrowed(value);
        }
        let mut relocated = Vec::with_capacity(value.len());
        let mut at = 0;
        'scan: while at < value.len() {
            let starts = at == 0 || !(name_byte(value[at - 1]) || value[at - 1] == b'/');
            if starts {
                for (spelling, token) in &self.spellings {
                    if value[at..].starts_with(spelling)
                        && value
                            .get(at + spelling.len())
                            .is_none_or(|next| !name_byte(*next))
                    {
                        relocated.extend_from_slice(token);
                        at += spelling.len();
                        continue 'scan;
                    }
                }
            }
            relocated.push(value[at]);
            at += 1;
        }
        std::borrow::Cow::Owned(relocated)
    }
}

/// Trust (DC-18b): a sandbox profile's identity once relocated: its fixed
/// header (every line up to the last `(deny default)` or `(version …)`
/// line, in order), then its rule lines relocated and sorted, without the
/// rules that let the compiler read the metadata of the directories above the
/// checkout (where the checkout is, which its remapped, path-free output
/// does not name). The slot needs no such care: a planned slot and the slot
/// it names are siblings, with the same directories above them.
fn relocated_profile(profile: &[u8], relocation: &Relocation) -> Vec<u8> {
    let above: Vec<Vec<u8>> = relocation
        .spellings
        .iter()
        .filter(|(_, token)| *token == WORKSPACE_TOKEN)
        .filter_map(|(spelling, _)| std::str::from_utf8(spelling).ok())
        .flat_map(|spelling| {
            std::path::Path::new(spelling)
                .ancestors()
                .skip(1)
                .filter_map(|ancestor| ancestor.to_str())
                .map(|ancestor| {
                    format!("(allow file-read-metadata (literal {ancestor:?}))").into_bytes()
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let relocated = relocation.apply(profile);
    let lines: Vec<&[u8]> = relocated.split(|byte| *byte == b'\n').collect();
    let header = lines
        .iter()
        .rposition(|line| line.starts_with(b"(deny default)") || line.starts_with(b"(version "))
        .map_or(0, |at| at + 1);
    let mut rules: Vec<&[u8]> = lines[header..]
        .iter()
        .copied()
        .filter(|line| !above.iter().any(|rule| rule.as_slice() == *line))
        .collect();
    rules.sort_unstable();
    let mut out = Vec::with_capacity(relocated.len() + 32);
    out.extend_from_slice(b"targo-sorted-profile-v1\n");
    for line in lines[..header].iter().chain(&rules) {
        out.extend_from_slice(&(line.len() as u64).to_le_bytes());
        out.extend_from_slice(line);
    }
    out
}

impl CommandInputs {
    pub(super) fn capture(command: &ProcessBuilder) -> CargoResult<Self> {
        Self::capture_inner(command, false, Relocation::default())
    }
    /// Trust (DC-18b): a shared member's command, whose digest reads every
    /// spelling of the workspace directory as one token and of its own store
    /// `slot` as another, so that two checkouts' commands for one unit have
    /// one digest, and the digest can name the slot. The compiler remaps the
    /// workspace and refuses metadata that still names it
    /// (`-Ztrust-path-free`), so the path is no input of its bytes.
    pub(super) fn capture_relocated(
        command: &ProcessBuilder,
        workspace: &std::path::Path,
        slot: &std::path::Path,
    ) -> CargoResult<Self> {
        let relocation = Relocation::new(&[(workspace, WORKSPACE_TOKEN), (slot, SLOT_TOKEN)])?;
        Self::capture_inner(command, false, relocation)
    }
    /// An original native command may inherit its caller's stdin. This records
    /// that fact; the selected process owner must independently refuse stdin it
    /// cannot deliver. Confined command identity keeps its strict requirement.
    pub(super) fn capture_native(command: &ProcessBuilder) -> CargoResult<Self> {
        Self::capture_inner(command, true, Relocation::default())
    }
    fn capture_inner(
        command: &ProcessBuilder,
        native: bool,
        relocated: Relocation,
    ) -> CargoResult<Self> {
        let environment = EnvironmentInputs::capture_effective(command)?;
        // Hash the actual OS command, including the generated sandbox policy
        // and wrapper arguments, rather than just the logical compiler argv.
        let prepared = command.build_command();
        let mut hash = Sha256::new();
        let mut field = |value: &[u8]| {
            let value = relocated.apply(value);
            hash.update(&(value.len() as u64).to_le_bytes());
            hash.update(&value);
        };
        field(if native {
            b"targo-original-native-command-v1"
        } else if relocated.is_empty() {
            b"targo-confined-command-v1"
        } else {
            b"targo-relocated-member-command-v2"
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
        // Trust (DC-18b): the sandbox profile lists its paths sorted, so two
        // checkouts' rules come in different orders around the store's. Its
        // rules are one per line and only the header's order matters; a
        // relocated command hashes the header and its other lines sorted, once
        // relocated.
        let profile = (!relocated.is_empty()
            && prepared.get_program() == OsStr::new("/usr/bin/sandbox-exec")
            && args.first() == Some(&OsStr::new("-p")))
        .then_some(1);
        let mut bytes = 0_usize;
        for (position, argument) in args.iter().enumerate() {
            bytes = bytes
                .checked_add(argument.len())
                .ok_or_else(|| anyhow::anyhow!("command argument size overflow"))?;
            if bytes > 16 * 1024 * 1024 {
                bail!("confined command arguments exceed their size bound");
            }
            if profile == Some(position) {
                field(&relocated_profile(argument.as_encoded_bytes(), &relocated));
            } else {
                field(argument.as_encoded_bytes());
            }
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
        let mut externs = Vec::new();
        let mut arguments = command.get_args();
        while let Some(argument) = arguments.next() {
            let argument = argument.as_encoded_bytes();
            let value = if argument == b"--extern" {
                arguments.next().map(|value| value.as_encoded_bytes())
            } else {
                argument.strip_prefix(b"--extern=")
            };
            // `[modifiers:]name=path`; a bare name passes no file.
            if let Some(value) = value
                && let Some(at) = value.iter().position(|byte| *byte == b'=')
            {
                externs.push(std::path::PathBuf::from(
                    std::str::from_utf8(&value[at + 1..])
                        .map_err(|_| anyhow::anyhow!("an --extern path is not UTF-8"))?,
                ));
            }
        }
        Ok(Self {
            digest: hash.finish_hex(),
            environment,
            native,
            relocated,
            externs,
        })
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    pub fn environment(&self) -> &EnvironmentInputs {
        &self.environment
    }

    /// Trust (DC-18b): the library files the command passes with `--extern`.
    pub fn externs(&self) -> &[std::path::PathBuf] {
        &self.externs
    }

    pub fn ensure_matches(&self, command: &ProcessBuilder) -> CargoResult<()> {
        if Self::capture_inner(command, self.native, self.relocated.clone())?.digest != self.digest
        {
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
    let inputs = Arc::new(if build.bcx.shared_member(unit) {
        let slot = build
            .files()
            .member_slot(unit)
            .ok_or_else(|| anyhow::anyhow!("shared member has no planned slot"))?;
        let inputs = CommandInputs::capture_relocated(&command, build.bcx.ws.root(), &slot.dir)?;
        // Trust (DC-18b): the slot was named by this command's digest. A
        // command that moved since (it never should) is not that slot's.
        if inputs.digest() != slot.command {
            return Err(build.bcx.shared_eligibility.recorder(unit)?.refuse_for_now(
                crate::util::log_message::SharedDependencyExclusion::MemberSlotDiffers,
            ));
        }
        inputs
    } else {
        CommandInputs::capture(&command)?
    });
    build
        .action_commands
        .insert(unit.clone(), Arc::clone(&inputs));
    Ok(Some(inputs))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    /// DC-18b: a spelling reads as its token only as a whole name: never
    /// inside a longer name, or as the tail of another path.
    #[test]
    fn relocation_reads_only_whole_names() {
        let root = tempfile::tempdir().unwrap();
        let workspace = root.path().join("w");
        let slot = root.path().join("slot");
        let relocation =
            Relocation::new(&[(&workspace, WORKSPACE_TOKEN), (&slot, SLOT_TOKEN)]).unwrap();
        let read = |value: String| relocation.apply(value.as_bytes()).into_owned();
        let w = workspace.to_str().unwrap();
        let s = slot.to_str().unwrap();
        assert_eq!(
            read(format!("{w}/src")),
            [WORKSPACE_TOKEN, b"/src"].concat()
        );
        assert_eq!(
            read(format!("--remap-path-prefix={w}=.")),
            [b"--remap-path-prefix=".as_slice(), WORKSPACE_TOKEN, b"=."].concat()
        );
        assert_eq!(
            read(format!("{s}/out:{w}")),
            [SLOT_TOKEN, b"/out:", WORKSPACE_TOKEN].concat()
        );
        for kept in [
            format!("{w}-data/src"),
            format!("/x{w}"),
            format!("{w}.old"),
        ] {
            assert_eq!(read(kept.clone()), kept.as_bytes(), "{kept}");
        }
    }

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
