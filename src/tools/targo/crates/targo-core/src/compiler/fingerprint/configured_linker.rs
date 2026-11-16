//! Content and effective-access identity for one explicitly configured native linker.
//!
//! This observes the original executable path and its symlink chain through the
//! existing bounded input scanner. It does not identify subordinate tools or
//! loaded libraries, authenticate execution, or grant proof authority.
//! The access data assumes a fixed credential/security profile throughout the
//! local compiler transport; it does not establish `execve` success.
//! Linux additionally excludes overridden fsuid/fsgid profiles: the shared
//! credential record does not capture those IDs or capability/namespace state.

use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use cargo_util::ProcessBuilder;
use trust_fs_observation::effective_access;

use super::build_script_inputs::{self, Snapshot, Window};

const DOMAIN: &[u8] = b"targo-configured-linker-content-access-v2";
const COMPILER_DOMAIN: &[u8] = b"targo-compiler-with-configured-linker-v1";

#[derive(Clone, Debug, Default)]
pub(super) enum Selection {
    #[default]
    NoConfigured,
    Captured(Planned),
    Unavailable,
}

#[derive(Clone)]
pub(super) struct Planned {
    path: PathBuf,
    snapshot: Snapshot,
    access: effective_access::Snapshot,
    binding: [u8; 32],
    // Only a fresh full observation can replace this invocation's original
    // point-freshness stamps. Nothing serialized can populate this cache.
    current_window: Arc<Mutex<Option<Window>>>,
}

impl std::fmt::Debug for Planned {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Planned")
            .field("path", &self.path)
            .field("snapshot", &self.snapshot)
            .field("access", &self.access)
            .field("binding", &self.binding)
            .finish_non_exhaustive()
    }
}

struct Observed {
    snapshot: Snapshot,
    access: effective_access::Snapshot,
    window: Window,
}

/// One attempt's metadata window, consumed rather than serialized or reused.
pub(in crate::compiler) struct Execution(State);

enum State {
    NoConfigured,
    Captured { binding: [u8; 32], window: Window },
    Unavailable,
}

impl Selection {
    pub(super) fn has_configured_selection(&self) -> bool {
        matches!(self, Self::Captured(_))
    }

    pub(super) fn capture(path: Option<&Path>, caller_selects_linker: bool) -> Self {
        if caller_selects_linker {
            return Self::Unavailable;
        }
        let Some(path) = path else {
            return Self::NoConfigured;
        };
        let Some(observed) = observe(path) else {
            return Self::Unavailable;
        };
        let Observed {
            snapshot,
            access,
            window,
        } = observed;
        let Ok(encoded) = serde_json::to_vec(&snapshot) else {
            return Self::Unavailable;
        };
        let Ok(encoded_access) = serde_json::to_vec(&access) else {
            return Self::Unavailable;
        };
        let mut hash = blake3::Hasher::new();
        field(&mut hash, DOMAIN);
        field(&mut hash, path.as_os_str().as_encoded_bytes());
        field(&mut hash, &encoded);
        field(&mut hash, &encoded_access);
        Self::Captured(Planned {
            path: path.to_owned(),
            snapshot,
            access,
            binding: *hash.finalize().as_bytes(),
            current_window: Arc::new(Mutex::new(Some(window))),
        })
    }

    /// Preserve every old default key byte: absent/unavailable observations add
    /// nothing. Unavailable separately refuses a reusable compiler observation.
    pub(super) fn hash_into(&self, state: &mut impl Hasher) {
        if let Self::Captured(planned) = self {
            DOMAIN.hash(state);
            planned.binding.hash(state);
        }
    }

    pub(super) fn bind_compiler(&self, compiler: Option<[u8; 32]>) -> Option<[u8; 32]> {
        match self {
            Self::NoConfigured => compiler,
            Self::Unavailable => None,
            Self::Captured(planned) => compiler.map(|compiler| {
                let mut hash = blake3::Hasher::new();
                field(&mut hash, COMPILER_DOMAIN);
                field(&mut hash, &compiler);
                field(&mut hash, &planned.binding);
                *hash.finalize().as_bytes()
            }),
        }
    }

    pub(super) fn current(&self) -> bool {
        self.current_with(observe)
    }

    fn current_with(&self, observe: impl FnOnce(&Path) -> Option<Observed>) -> bool {
        match self {
            Self::NoConfigured => true,
            Self::Unavailable => false,
            Self::Captured(planned) => {
                let mut current = planned.current_window.lock().unwrap();
                if access(&planned.path).is_some_and(|access| access == planned.access)
                    && executable(&planned.path)
                    && current.as_ref().is_some_and(Window::is_current)
                {
                    return true;
                }
                *current = None;
                // A changed stamp can trigger a full reobservation, but never
                // replacement of the SAME planned content/access identity.
                observe(&planned.path).is_some_and(|observed| {
                    if observed.snapshot != planned.snapshot || observed.access != planned.access {
                        return false;
                    }
                    *current = Some(observed.window);
                    true
                })
            }
        }
    }

    pub(super) fn begin(&self, command: &ProcessBuilder) -> Execution {
        let selection =
            command_selection(command.get_args().map(|arg| arg.as_encoded_bytes()), true);
        let state = match (self, selection) {
            (Self::NoConfigured, CommandSelection::None) => State::NoConfigured,
            (Self::Captured(planned), CommandSelection::One(path))
                if path == planned.path.as_os_str().as_encoded_bytes() =>
            {
                window(&planned.path)
                    .filter(|window| {
                        access(&planned.path).is_some_and(|access| access == planned.access)
                            && executable(&planned.path)
                            && window.is_current()
                    })
                    .map_or(State::Unavailable, |window| State::Captured {
                        binding: planned.binding,
                        window,
                    })
            }
            _ => State::Unavailable,
        };
        Execution(state)
    }

    pub(super) fn complete(&self, execution: Execution) -> bool {
        self.complete_with(execution, observe)
    }

    fn complete_with(
        &self,
        execution: Execution,
        observe: impl FnOnce(&Path) -> Option<Observed>,
    ) -> bool {
        match (self, execution.0) {
            (Self::NoConfigured, State::NoConfigured) => true,
            (Self::Captured(planned), State::Captured { binding, window })
                if binding == planned.binding =>
            {
                observe(&planned.path).is_some_and(|observed| {
                    observed.snapshot == planned.snapshot
                        && observed.access == planned.access
                        // Keep the ORIGINAL execution window through all final
                        // content, executable and effective-access reads.
                        && window.is_current()
                })
            }
            _ => false,
        }
    }
}

fn field(hash: &mut blake3::Hasher, bytes: &[u8]) {
    hash.update(&(bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

fn executable(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        path.is_absolute()
            && std::fs::metadata(path).is_ok_and(|metadata| {
                metadata.is_file() && metadata.permissions().mode() & 0o111 != 0
            })
    }
    #[cfg(not(unix))]
    {
        let _ = path;
        false
    }
}

fn access(path: &Path) -> Option<effective_access::Snapshot> {
    let snapshot = effective_access::capture(&[path.to_owned()]).ok()?;
    (snapshot.entries().first()?.outcome() == effective_access::Outcome::Allowed)
        .then_some(snapshot)
}

fn observe(path: &Path) -> Option<Observed> {
    observe_with(path, access)
}

fn observe_with(
    path: &Path,
    capture: impl FnOnce(&Path) -> Option<effective_access::Snapshot>,
) -> Option<Observed> {
    if !executable(path) {
        return None;
    }
    let observation = build_script_inputs::observe_attempt(
        path.parent()?,
        &[PathBuf::from(path.file_name()?)],
        false,
    )
    .result
    .ok()?;
    let (snapshot, window) = observation.into_parts();
    let access = capture(path)?;
    // The full observation's original stamps cover every final access and
    // executable query; never mint a new window after those reads.
    (executable(path) && window.is_current()).then_some(Observed {
        snapshot,
        access,
        window,
    })
}

fn window(path: &Path) -> Option<Window> {
    if !executable(path) {
        return None;
    }
    build_script_inputs::window_attempt(path.parent()?, &[PathBuf::from(path.file_name()?)], false)
        .result
        .ok()
}

enum CommandSelection<'a> {
    None,
    One(&'a [u8]),
    Unavailable,
}

/// Inspect original UTF-8 caller vectors, not Cargo's later response transport.
/// Possible option-looking operand data is conservatively uncacheable.
pub(super) fn caller_selects_linker<'a>(args: impl IntoIterator<Item = &'a str>) -> bool {
    !matches!(
        command_selection(args.into_iter().map(str::as_bytes), false),
        CommandSelection::None
    )
}

fn command_selection<'a>(
    args: impl IntoIterator<Item = &'a [u8]>,
    refuse_argfiles: bool,
) -> CommandSelection<'a> {
    let mut args = args.into_iter();
    let mut selected = None;
    while let Some(arg) = args.next() {
        if refuse_argfiles && arg.starts_with(b"@") {
            return CommandSelection::Unavailable;
        }
        let Some(value) = codegen_option(arg) else {
            continue;
        };
        let Some(value) = value.or_else(|| args.next()) else {
            return CommandSelection::Unavailable;
        };
        let value = value.strip_prefix(b"=").unwrap_or(value);
        let equal = value.iter().position(|byte| *byte == b'=');
        let key = equal.map_or(value, |equal| &value[..equal]);
        if key.trim_ascii() != b"linker" {
            continue;
        }
        let Some(equal) = equal else {
            return CommandSelection::Unavailable;
        };
        let path = &value[equal + 1..];
        if path.is_empty() || selected.is_some() {
            return CommandSelection::Unavailable;
        }
        selected = Some(path);
    }
    selected.map_or(CommandSelection::None, CommandSelection::One)
}

// Outer Some means a -C/--codegen option; inner None consumes the next word.
fn codegen_option(arg: &[u8]) -> Option<Option<&[u8]>> {
    if arg == b"--codegen" {
        return Some(None);
    }
    if let Some(value) = arg.strip_prefix(b"--codegen=") {
        return Some(Some(value));
    }
    let short = arg.strip_prefix(b"-")?;
    if short.starts_with(b"-") {
        return None;
    }
    for (index, byte) in short.iter().enumerate() {
        if *byte == b'C' {
            let rest = &short[index + 1..];
            return Some((!rest.is_empty()).then_some(rest));
        }
        // Other value-taking options consume the rest of a short cluster.
        // In particular -gClink-arg=... is one C value, not an inner selector.
        if b"ADFLWZjlo".contains(byte) {
            break;
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(selection: &Selection) -> u64 {
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        b"existing fingerprint".hash(&mut hash);
        selection.hash_into(&mut hash);
        hash.finish()
    }

    #[test]
    fn default_preserves_exact_hash_and_compiler_identity() {
        let selection = Selection::capture(None, false);
        let mut original = std::collections::hash_map::DefaultHasher::new();
        b"existing fingerprint".hash(&mut original);
        assert_eq!(hash(&selection), original.finish());
        assert_eq!(selection.bind_compiler(Some([7; 32])), Some([7; 32]));
        assert_eq!(selection.bind_compiler(None), None);
        assert!(selection.current());
        let mut command = ProcessBuilder::new("rustc");
        command.args(&["-C", "opt-level=2"]);
        assert!(selection.complete(selection.begin(&command)));
        command.arg("-Clinker=/caller");
        assert!(!selection.complete(selection.begin(&command)));
    }

    #[test]
    fn caller_options_include_long_split_and_short_clusters() {
        for args in [
            vec!["-C", "linker=/other"],
            vec!["-Clinker=/other"],
            vec!["--codegen", "linker=/other"],
            vec!["--codegen=linker=/other"],
            vec!["-gClinker=/other"],
            vec!["-gC", "linker=/other"],
            vec!["-C=linker=/other"],
            vec!["--cfg", "-Clinker=/other"],
            vec!["-C", "linker="],
        ] {
            assert!(caller_selects_linker(args.iter().copied()), "{args:?}");
        }
        for args in [
            vec!["-C", "opt-level=2"],
            vec!["-gClink-arg=-Clinker=/data"],
            vec!["-L-Clinker=/data"],
            vec!["-oClinker=/data"],
            vec!["-Clinker-flavor=gnu"],
            vec!["--cfg", "literal=\"linker=/data\""],
        ] {
            assert!(!caller_selects_linker(args.iter().copied()), "{args:?}");
        }
    }

    #[cfg(unix)]
    fn tool(path: &Path, bytes: &[u8]) {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::write(path, bytes).unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
    }

    #[cfg(unix)]
    fn command(path: &Path) -> ProcessBuilder {
        let mut command = ProcessBuilder::new("rustc");
        command.arg("-C").arg(format!("linker={}", path.display()));
        command
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn preserved_mtime_content_change_alters_both_bindings() {
        build_script_inputs::settled(|world| {
            let path = world.path().canonicalize().unwrap().join("tool");
            tool(&path, b"one");
            let planned = Selection::capture(Some(&path), false);
            assert!(matches!(planned, Selection::Captured(_)));
            assert!(planned.complete(planned.begin(&command(&path))));
            let mtime =
                filetime::FileTime::from_last_modification_time(&std::fs::metadata(&path).unwrap());
            std::fs::write(&path, b"two").unwrap();
            filetime::set_file_mtime(&path, mtime).unwrap();
            assert!(!planned.current());
            let changed = Selection::capture(Some(&path), false);
            assert!(changed.current());
            assert_ne!(hash(&planned), hash(&changed));
            assert_ne!(
                planned.bind_compiler(Some([9; 32])),
                changed.bind_compiler(Some([9; 32]))
            );
        });
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn unchanged_point_checks_share_live_stamps_without_full_observation() {
        build_script_inputs::settled(|world| {
            let path = world.path().canonicalize().unwrap().join("tool");
            // Keep the existing configured-tool profile: opaque executable
            // bytes and scripts do not require a native header.
            tool(&path, b"#!/bin/sh\nexit 0\n");
            let planned = Selection::capture(Some(&path), false);
            let cloned = planned.clone();
            let (Selection::Captured(first), Selection::Captured(second)) = (&planned, &cloned)
            else {
                panic!("configured script must retain its existing supported profile");
            };
            assert!(Arc::ptr_eq(&first.current_window, &second.current_window));
            let key = hash(&planned);
            let compiler = planned.bind_compiler(Some([9; 32]));
            for _ in 0..3 {
                assert!(
                    cloned.current_with(|_| panic!("unchanged tools must not be fully reread"))
                );
            }
            tool(&path, b"different executable bytes");
            assert!(!planned.current());
            tool(&path, b"#!/bin/sh\nexit 0\n");
            let mut full_reads = 0;
            assert!(cloned.current_with(|path| {
                full_reads += 1;
                observe(path)
            }));
            assert_eq!(full_reads, 1);
            assert!(planned.current_with(|_| panic!("clones must share the fresh window")));
            assert_eq!(hash(&planned), key);
            assert_eq!(planned.bind_compiler(Some([9; 32])), compiler);
            assert!(planned.complete(planned.begin(&command(&path))));
        });
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn content_mutation_during_final_access_refuses_observation() {
        build_script_inputs::settled(|world| {
            let path = world.path().canonicalize().unwrap().join("tool");
            tool(&path, b"one");
            assert!(
                observe_with(&path, |path| {
                    let access = access(path);
                    tool(path, b"two");
                    access
                })
                .is_none()
            );
        });
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn completed_access_reads_remain_inside_original_execution_window() {
        build_script_inputs::settled(|world| {
            let path = world.path().canonicalize().unwrap().join("tool");
            tool(&path, b"one");
            let planned = Selection::capture(Some(&path), false);
            let execution = planned.begin(&command(&path));
            assert!(!planned.complete_with(execution, |path| {
                let after = observe(path);
                tool(path, b"two");
                tool(path, b"one");
                after
            }));
        });
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn final_selection_must_be_unique_and_match_original_path() {
        build_script_inputs::settled(|world| {
            let path = world.path().canonicalize().unwrap().join("tool");
            tool(&path, b"one");
            let planned = Selection::capture(Some(&path), false);
            let value = format!("linker={}", path.display());
            for args in [
                vec!["-C".to_owned(), value.clone()],
                vec![format!("-C{value}")],
                vec!["--codegen".to_owned(), value.clone()],
                vec![format!("--codegen={value}")],
                vec![format!("-gC{value}")],
                vec!["-gC".to_owned(), value.clone()],
            ] {
                let mut cmd = ProcessBuilder::new("rustc");
                cmd.args(&args);
                assert!(planned.complete(planned.begin(&cmd)), "{args:?}");
            }
            for args in [
                vec![],
                vec!["-Clinker=/other"],
                vec!["@opaque"],
                vec!["--codegen", "linker="],
            ] {
                let mut cmd = ProcessBuilder::new("rustc");
                cmd.args(&args);
                assert!(!planned.complete(planned.begin(&cmd)), "{args:?}");
            }
            for extra in [
                "-Clinker=/other",
                "--codegen=linker=/other",
                "-gClinker=/other",
            ] {
                let mut cmd = command(&path);
                cmd.arg(extra);
                assert!(!planned.complete(planned.begin(&cmd)), "{extra}");
            }
            let other = Selection::capture(Some(&path), true);
            assert!(!other.complete(planned.begin(&command(&path))));
        });
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn edit_restore_and_same_byte_rename_cannot_complete_window() {
        build_script_inputs::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let path = root.join("tool");
            tool(&path, b"one");
            let planned = Selection::capture(Some(&path), false);
            let before = planned.begin(&command(&path));
            let mtime =
                filetime::FileTime::from_last_modification_time(&std::fs::metadata(&path).unwrap());
            std::fs::write(&path, b"two").unwrap();
            std::fs::write(&path, b"one").unwrap();
            filetime::set_file_mtime(&path, mtime).unwrap();
            assert!(planned.current());
            assert!(!planned.complete(before));
            let before = planned.begin(&command(&path));
            std::fs::rename(&path, root.join("old")).unwrap();
            tool(&path, b"one");
            filetime::set_file_mtime(&path, mtime).unwrap();
            assert!(planned.current());
            assert!(!planned.complete(before));
        });
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn symlink_chain_retarget_and_restore_retains_window_evidence() {
        build_script_inputs::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            tool(&root.join("one"), b"same");
            tool(&root.join("two"), b"same");
            std::os::unix::fs::symlink("one", root.join("middle")).unwrap();
            let path = root.join("tool");
            std::os::unix::fs::symlink("middle", &path).unwrap();
            let planned = Selection::capture(Some(&path), false);
            assert!(planned.complete(planned.begin(&command(&path))));
            let before = planned.begin(&command(&path));
            std::fs::remove_file(root.join("middle")).unwrap();
            std::os::unix::fs::symlink("two", root.join("middle")).unwrap();
            assert!(!planned.current());
            std::fs::remove_file(root.join("middle")).unwrap();
            std::os::unix::fs::symlink("one", root.join("middle")).unwrap();
            assert!(planned.current());
            assert!(!planned.complete(before));
        });
    }

    #[cfg(unix)]
    #[test]
    fn unavailable_shapes_and_original_overrides_never_bind_or_seal() {
        build_script_inputs::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let path = root.join("tool");
            tool(&path, b"one");
            let noexec = root.join("noexec");
            std::fs::write(&noexec, b"data").unwrap();
            for selected in [
                Selection::capture(Some(Path::new("relative")), false),
                Selection::capture(Some(&root.join("missing")), false),
                Selection::capture(Some(&root), false),
                Selection::capture(Some(&noexec), false),
                Selection::capture(Some(&path), true),
                Selection::capture(None, true),
            ] {
                assert!(matches!(selected, Selection::Unavailable));
                assert!(!selected.current());
                assert_eq!(selected.bind_compiler(Some([7; 32])), None);
                assert_eq!(hash(&selected), hash(&Selection::default()));
                assert!(!selected.complete(selected.begin(&ProcessBuilder::new("rustc"))));
            }
        });
    }

    #[cfg(all(unix, not(any(target_os = "macos", target_os = "linux"))))]
    #[test]
    fn unsupported_execute_access_host_refuses_configured_tool_reuse() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("tool");
        tool(&path, b"one");
        let selection = Selection::capture(Some(&path), false);
        assert!(matches!(selection, Selection::Unavailable));
        assert!(!selection.current());
        assert_eq!(selection.bind_compiler(Some([7; 32])), None);
        assert!(!selection.complete(selection.begin(&command(&path))));
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn acl_denial_refuses_reuse_even_with_unchanged_mode_and_content() {
        use std::os::unix::fs::PermissionsExt as _;

        build_script_inputs::settled(|world| {
            let path = world.path().canonicalize().unwrap().join("tool");
            tool(&path, b"same");
            let planned = Selection::capture(Some(&path), false);
            assert!(planned.complete(planned.begin(&command(&path))));
            let window = planned.begin(&command(&path));
            let mode = std::fs::metadata(&path).unwrap().permissions().mode();
            let acl = "everyone deny execute";
            let chmod = |action| {
                assert!(
                    std::process::Command::new("/bin/chmod")
                        .args([action, acl])
                        .arg(&path)
                        .status()
                        .unwrap()
                        .success()
                );
            };
            chmod("+a");
            assert_eq!(std::fs::metadata(&path).unwrap().permissions().mode(), mode);
            assert_eq!(std::fs::read(&path).unwrap(), b"same");
            assert!(!planned.current());
            assert!(!planned.complete(planned.begin(&command(&path))));
            let denied = Selection::capture(Some(&path), false);
            assert!(matches!(denied, Selection::Unavailable));
            assert_eq!(denied.bind_compiler(Some([7; 32])), None);
            chmod("-a");
            assert!(planned.current());
            assert!(!planned.complete(window));
            let recovered = Selection::capture(Some(&path), false);
            assert!(recovered.complete(recovered.begin(&command(&path))));
        });
    }
}
