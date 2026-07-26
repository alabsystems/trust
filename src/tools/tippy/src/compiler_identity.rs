//! Stable identity checks for the compiler selected by branded Tippy.
//!
//! Tippy must keep the compiler pathname inside the installed toolchain bin
//! directory so rustc can discover its sibling sysroot. Consequently this
//! module cannot hand Targo an already-open compiler handle. It instead binds
//! the pathname as tightly as the portable interface allows: exact executable
//! identities, the launch and canonical directory-ancestor chains, bounded
//! bytes, checks before/open/after reading, a final check immediately around
//! the Targo child lifetime, and live handles held across that lifetime.

use std::fs;
use std::io::{Read as _, Seek as _, SeekFrom};
use std::path::{Path, PathBuf};

use crate::path_identity::{
    AuthenticatedDirectoryChain, DirectoryChainGuard, MAX_AUTHENTICATED_EXECUTABLE_BYTES, OpenedExecutable,
    PathSnapshot,
};

// A Trust compiler frontend is normally far smaller than this, including
// debug builds. Keep the ceiling generous enough for supported stage2
// toolchains while preventing a forged sibling from turning Tippy startup into
// an unbounded read.
const MAX_COMPILER_EXECUTABLE_BYTES: u64 = MAX_AUTHENTICATED_EXECUTABLE_BYTES;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompilerAliasRelationship {
    /// The public `rustc` name is another hard link to the selected `trustc`.
    SameFile,
    /// Installers may copy, rather than hard-link, the compatibility frontend.
    ByteIdenticalCopy,
}

#[derive(Debug)]
struct ToolchainBinDirectory {
    chain: AuthenticatedDirectoryChain,
}

impl ToolchainBinDirectory {
    fn authenticate(trustc: &Path, selected: &Path) -> Result<Self, String> {
        let trustc_parent = trustc
            .parent()
            .ok_or_else(|| format!("selected trustc `{}` has no toolchain bin directory", trustc.display()))?;
        if selected.parent() != Some(trustc_parent) {
            return Err(format!(
                "selected compiler `{}` is not in trustc's exact toolchain bin directory `{}`",
                selected.display(),
                trustc_parent.display()
            ));
        }
        Ok(Self {
            chain: AuthenticatedDirectoryChain::capture(trustc_parent)?,
        })
    }

    fn revalidate(&self) -> Result<DirectoryChainGuard, String> {
        self.chain.revalidate()
    }

    fn confirm_stable_with_guard(&self, guard: &DirectoryChainGuard) -> Result<(), String> {
        self.chain.confirm_stable_with_guard(guard)
    }
}

fn opened_files_have_identical_bytes(
    left: &mut fs::File,
    right: &mut fs::File,
    expected_len: u64,
) -> std::io::Result<bool> {
    left.seek(SeekFrom::Start(0))?;
    right.seek(SeekFrom::Start(0))?;
    let mut left_buf = [0_u8; 64 * 1024];
    let mut right_buf = [0_u8; 64 * 1024];
    let mut compared = 0_u64;
    loop {
        let left_read = left.read(&mut left_buf)?;
        let right_read = right.read(&mut right_buf)?;
        if left_read != right_read || left_buf[..left_read] != right_buf[..right_read] {
            return Ok(false);
        }
        compared = compared
            .checked_add(left_read as u64)
            .ok_or_else(|| std::io::Error::other("compiler byte count overflowed"))?;
        if compared > MAX_COMPILER_EXECUTABLE_BYTES {
            return Err(std::io::Error::other(format!(
                "compiler exceeds the {MAX_COMPILER_EXECUTABLE_BYTES}-byte authentication limit"
            )));
        }
        if left_read == 0 {
            return Ok(compared == expected_len);
        }
    }
}

struct CheckedCompilerPair {
    trustc: OpenedExecutable,
    alias: OpenedExecutable,
    relationship: CompilerAliasRelationship,
}

fn checked_compiler_pair(trustc: PathBuf, alias: PathBuf) -> Result<CheckedCompilerPair, String> {
    let mut trustc = OpenedExecutable::open(trustc, "compiler trustc")?;
    let mut alias = OpenedExecutable::open(alias, "compiler rustc-compatible alias")?;
    if trustc.snapshot.len != alias.snapshot.len {
        return Err(format!(
            "rustc-compatible sibling `{}` is not the selected Trust compiler `{}`; executable lengths differ",
            alias.path.display(),
            trustc.path.display()
        ));
    }
    let relationship = if trustc.snapshot.same_file(&alias.snapshot) {
        CompilerAliasRelationship::SameFile
    } else {
        let identical = opened_files_have_identical_bytes(&mut trustc.file, &mut alias.file, trustc.snapshot.len)
            .map_err(|error| {
                format!(
                    "cannot authenticate rustc-compatible sibling `{}` against selected trustc `{}`: {error}",
                    alias.path.display(),
                    trustc.path.display()
                )
            })?;
        if !identical {
            return Err(format!(
                "rustc-compatible sibling `{}` is not the selected Trust compiler `{}`; repair or reinstall the toolchain",
                alias.path.display(),
                trustc.path.display()
            ));
        }
        CompilerAliasRelationship::ByteIdenticalCopy
    };
    // This final metadata pass occurs after the complete byte comparison, so a
    // mutation during the read cannot be accepted under the initial identity.
    trustc.confirm_stable("compiler trustc")?;
    alias.confirm_stable("compiler rustc-compatible alias")?;
    Ok(CheckedCompilerPair {
        trustc,
        alias,
        relationship,
    })
}

#[derive(Debug)]
pub(crate) struct AuthenticatedCompiler {
    path: PathBuf,
    bin_directory: ToolchainBinDirectory,
    trustc_path: PathBuf,
    alias_path: Option<PathBuf>,
    trustc_snapshot: PathSnapshot,
    selected_snapshot: PathSnapshot,
    relationship: Option<CompilerAliasRelationship>,
    // On Windows these retained read-sharing handles prevent a same-length
    // rewrite/replacement from being hidden by restoring writable timestamps
    // between initial authentication and the launch-boundary revalidation.
    _selected_trustc: fs::File,
    _selected_alias: Option<fs::File>,
}

impl AuthenticatedCompiler {
    pub(crate) fn selected_trustc(path: PathBuf) -> Result<Self, String> {
        let bin_directory = ToolchainBinDirectory::authenticate(&path, &path)?;
        let trustc = OpenedExecutable::open(path.clone(), "compiler trustc")?;
        trustc.confirm_stable("compiler trustc")?;
        let _ = bin_directory.revalidate()?;
        Ok(Self {
            path: path.clone(),
            bin_directory,
            trustc_path: path,
            alias_path: None,
            trustc_snapshot: trustc.snapshot.clone(),
            selected_snapshot: trustc.snapshot,
            relationship: None,
            _selected_trustc: trustc.file,
            _selected_alias: None,
        })
    }

    pub(crate) fn alias(trustc_path: PathBuf, alias_path: PathBuf) -> Result<Self, String> {
        let bin_directory = ToolchainBinDirectory::authenticate(&trustc_path, &alias_path)?;
        let checked = checked_compiler_pair(trustc_path.clone(), alias_path.clone())?;
        let _ = bin_directory.revalidate()?;
        Ok(Self {
            path: alias_path.clone(),
            bin_directory,
            trustc_path,
            alias_path: Some(alias_path),
            trustc_snapshot: checked.trustc.snapshot,
            selected_snapshot: checked.alias.snapshot,
            relationship: Some(checked.relationship),
            _selected_trustc: checked.trustc.file,
            _selected_alias: Some(checked.alias.file),
        })
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    /// Run one operation while the latest authenticated compiler and bin
    /// directory handles remain live, then reject its result if either path no
    /// longer has the recorded identity.
    ///
    /// This is deliberately not described as stable-handle execution. The
    /// actual compiler exec occurs later in Targo/Cargo and still uses `path` to
    /// preserve rustc's toolchain-relative sysroot lookup. On Unix an attacker
    /// with write authority can rename an open path. Directory/file ctime makes
    /// ordinary swap-and-restore detectable, but a filesystem or privileged
    /// actor able to forge those identity fields remains outside this boundary.
    /// A raced executable can perform side effects before the post-check rejects
    /// its result.
    pub(crate) fn run_guarded<T>(&self, operation: impl FnOnce() -> T) -> Result<T, String> {
        let _guard = self
            .revalidate()
            .map_err(|error| format!("compiler authentication failed before Targo launch: {error}"))?;
        let result = operation();
        let _post_guard = self
            .revalidate()
            .map_err(|error| format!("compiler identity changed while Targo was running: {error}"))?;
        Ok(result)
    }

    fn revalidate(&self) -> Result<CompilerSpawnGuard, String> {
        let bin_directory = self.bin_directory.revalidate()?;
        if let Some(alias_path) = &self.alias_path {
            // Initial authentication already compared every byte for a copied
            // alias. Repeating an up-to-1 GiB comparison before and after each
            // complete Targo run is redundant: exact recorded identity,
            // metadata, and alias relationship establish that the initially
            // compared objects remain selected. Persistent read-sharing
            // handles additionally prevent Windows rewrites whose writable
            // timestamps could otherwise be restored.
            let trustc = OpenedExecutable::open(self.trustc_path.clone(), "compiler trustc")?;
            let alias = OpenedExecutable::open(alias_path.clone(), "compiler rustc-compatible alias")?;
            trustc.confirm_stable("compiler trustc")?;
            alias.confirm_stable("compiler rustc-compatible alias")?;
            self.bin_directory.confirm_stable_with_guard(&bin_directory)?;
            let relationship = if trustc.snapshot.same_file(&alias.snapshot) {
                CompilerAliasRelationship::SameFile
            } else {
                CompilerAliasRelationship::ByteIdenticalCopy
            };
            if trustc.snapshot != self.trustc_snapshot
                || alias.snapshot != self.selected_snapshot
                || Some(relationship) != self.relationship
            {
                return Err(format!(
                    "selected compiler `{}` changed identity, length, contents, or alias relationship",
                    self.path.display()
                ));
            }
            return Ok(CompilerSpawnGuard {
                _bin_directory: bin_directory,
                _trustc: trustc.file,
                _selected: Some(alias.file),
            });
        }

        let trustc = OpenedExecutable::open(self.trustc_path.clone(), "compiler trustc")?;
        trustc.confirm_stable("compiler trustc")?;
        self.bin_directory.confirm_stable_with_guard(&bin_directory)?;
        if trustc.snapshot != self.trustc_snapshot || trustc.snapshot != self.selected_snapshot {
            return Err(format!(
                "selected compiler `{}` changed identity, length, or contents",
                self.path.display()
            ));
        }
        Ok(CompilerSpawnGuard {
            _bin_directory: bin_directory,
            _trustc: trustc.file,
            _selected: None,
        })
    }
}

// The final opened handles remain alive across the guarded operation. This
// strengthens replacement resistance on platforms whose sharing rules deny
// replacement of open files, but the later Cargo compiler exec does not use
// these handles.
struct CompilerSpawnGuard {
    _bin_directory: DirectoryChainGuard,
    _trustc: fs::File,
    _selected: Option<fs::File>,
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Mutex, MutexGuard};
    use std::time::{SystemTime, UNIX_EPOCH};
    use std::{env, fs};

    use super::{AuthenticatedCompiler, CompilerAliasRelationship, MAX_COMPILER_EXECUTABLE_BYTES};
    #[cfg(windows)]
    use crate::path_identity::AuthenticatedDirectoryChain;
    use crate::path_identity::AuthenticatedExecutable;

    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
    static FIXTURE_LOCK: Mutex<()> = Mutex::new(());

    struct Fixture {
        root: PathBuf,
        _lock: MutexGuard<'static, ()>,
    }

    impl Fixture {
        fn new(label: &str) -> Self {
            // Every authenticated fixture records the writable temporary
            // directory in its ancestor chain. Serialize fixture lifecycle so
            // sibling tests cannot mutate that shared directory while a guard
            // is deliberately checking it.
            let lock = FIXTURE_LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system clock after Unix epoch")
                .as_nanos();
            let sequence = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
            let temp = env::temp_dir().canonicalize().unwrap_or_else(|_| env::temp_dir());
            let root = temp.join(format!(
                "tippy-compiler-identity-{label}-{}-{nanos}-{sequence}",
                std::process::id()
            ));
            fs::create_dir(&root).expect("create isolated compiler fixture directory");
            Self { root, _lock: lock }
        }

        fn path(&self, name: &str) -> PathBuf {
            self.root.join(name)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    fn write_executable(path: &Path, bytes: &[u8]) {
        fs::write(path, bytes).expect("write executable fixture");
        make_executable(path);
    }

    fn make_executable(path: &Path) {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            let mut permissions = fs::metadata(path).expect("executable fixture metadata").permissions();
            permissions.set_mode(0o700);
            fs::set_permissions(path, permissions).expect("mark executable fixture executable");
        }
        #[cfg(not(unix))]
        let _ = path;
    }

    #[test]
    fn byte_identical_copy_is_accepted_but_different_bytes_are_not() {
        let fixture = Fixture::new("exact-alias");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        write_executable(&trustc, b"same Trust compiler bytes");
        write_executable(&rustc, b"same Trust compiler bytes");
        let authenticated =
            AuthenticatedCompiler::alias(trustc.clone(), rustc.clone()).expect("matching compiler aliases");
        assert_eq!(authenticated.path(), rustc);
        assert_eq!(
            authenticated.relationship,
            Some(CompilerAliasRelationship::ByteIdenticalCopy)
        );
        // Windows retains non-writable selection handles for the authenticated
        // compiler lifetime, so release that authority before constructing the
        // deliberately stale second fixture.
        drop(authenticated);

        write_executable(&rustc, b"stale compiler bytes");
        let error = AuthenticatedCompiler::alias(trustc, rustc).expect_err("mixed compiler aliases must fail");
        assert!(error.contains("not the selected Trust compiler"), "{error}");
    }

    #[test]
    fn hard_linked_alias_uses_same_file_authority() {
        let fixture = Fixture::new("hard-link");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        write_executable(&trustc, b"one hard-linked Trust compiler");
        fs::hard_link(&trustc, &rustc).expect("create hard-linked compiler alias");

        let authenticated = AuthenticatedCompiler::alias(trustc, rustc).expect("hard link authenticates");
        assert_eq!(authenticated.relationship, Some(CompilerAliasRelationship::SameFile));
    }

    #[test]
    fn selected_trustc_without_compatibility_alias_is_revalidated() {
        let fixture = Fixture::new("selected-trustc");
        let trustc = fixture.path("trustc");
        write_executable(&trustc, b"selected Trust compiler without rustc alias");

        let authenticated =
            AuthenticatedCompiler::selected_trustc(trustc.clone()).expect("authenticate selected trustc");
        assert_eq!(authenticated.path(), trustc);
        assert_eq!(authenticated.run_guarded(|| 17_u8), Ok(17));
    }

    #[test]
    fn sibling_guard_rejects_in_place_tool_rewrite() {
        let fixture = Fixture::new("sibling-in-place-rewrite");
        let targo = fixture.path("targo");
        write_executable(&targo, b"authenticated targo bytes");
        let authenticated =
            AuthenticatedExecutable::capture(targo.clone(), "targo").expect("authenticate Targo sibling");

        let result = authenticated.run_guarded_for("Targo", || {
            // This mutation leaves the containing directory untouched. The
            // compiler-only directory guard therefore cannot substitute for
            // binding each executable role itself.
            fs::write(&targo, b"hostile targo replacement")
        });
        assert!(
            matches!(result, Err(_) | Ok(Err(_))),
            "an in-place Targo rewrite was neither prevented nor detected"
        );
    }

    #[test]
    fn sibling_guard_rejects_replacement_before_child_launch() {
        let fixture = Fixture::new("sibling-pre-launch-replacement");
        let driver = fixture.path("tippy-driver");
        let replacement = fixture.path("replacement");
        let sentinel = fixture.path("sentinel");
        write_executable(&driver, b"authenticated tippy driver");
        let authenticated = AuthenticatedExecutable::capture(driver.clone(), "tippy-driver")
            .expect("authenticate Tippy driver sibling");

        write_executable(&replacement, b"authenticated tippy driver");
        let replacement_attempt = fs::remove_file(&driver).and_then(|()| fs::rename(&replacement, &driver));
        if replacement_attempt.is_err() {
            // Windows selection handles deny delete sharing, preventing the
            // replacement before a child can be considered for launch.
            assert!(!sentinel.exists());
            return;
        }
        let result = authenticated.run_guarded_for("Targo", || fs::write(&sentinel, b"child launched"));
        assert!(result.is_err(), "a replacement driver reached the launch boundary");
        assert!(
            !sentinel.exists(),
            "guarded operation ran after failed driver authentication"
        );
    }

    #[cfg(windows)]
    #[test]
    fn windows_selection_handles_deny_hidden_executable_and_directory_replacement() {
        let fixture = Fixture::new("windows-sharing-locks");
        let bin = fixture.path("bin");
        fs::create_dir(&bin).expect("create selected Windows bin directory");
        let targo = bin.join("targo.exe");
        write_executable(&targo, b"selected Windows Targo executable");

        let executable =
            AuthenticatedExecutable::capture(targo.clone(), "targo").expect("authenticate selected Windows executable");
        assert!(
            fs::OpenOptions::new().write(true).open(&targo).is_err(),
            "a retained executable handle unexpectedly shared write authority"
        );

        let directories =
            AuthenticatedDirectoryChain::capture(&bin).expect("authenticate selected Windows directory chain");
        let renamed = fixture.path("bin-renamed");
        assert!(
            fs::rename(&bin, &renamed).is_err(),
            "a retained directory handle unexpectedly shared delete/rename authority"
        );

        drop(directories);
        drop(executable);
        fs::rename(&bin, &renamed).expect("selection locks are released when guards are dropped");
    }

    #[test]
    fn oversized_alias_is_rejected_before_byte_comparison() {
        let fixture = Fixture::new("oversized");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        write_executable(&trustc, b"bounded Trust compiler");
        let oversized = fs::File::create(&rustc).expect("create sparse oversized alias");
        oversized
            .set_len(MAX_COMPILER_EXECUTABLE_BYTES + 1)
            .expect("extend sparse oversized alias");
        drop(oversized);
        make_executable(&rustc);

        let error = AuthenticatedCompiler::alias(trustc, rustc)
            .expect_err("oversized compiler aliases must fail before reading");
        assert!(error.contains("byte bound"), "{error}");
    }

    #[test]
    fn non_regular_alias_is_rejected() {
        let fixture = Fixture::new("directory-alias");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        write_executable(&trustc, b"bounded Trust compiler");
        fs::create_dir(&rustc).expect("create directory in alias position");

        let error = AuthenticatedCompiler::alias(trustc, rustc).expect_err("directory alias must fail");
        assert!(error.contains("not a regular file"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn symlink_alias_is_rejected_even_when_bytes_match() {
        use std::os::unix::fs::symlink;

        let fixture = Fixture::new("symlink");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        write_executable(&trustc, b"Trust compiler behind forbidden symlink");
        symlink(&trustc, &rustc).expect("create compiler alias symlink");

        let error = AuthenticatedCompiler::alias(trustc, rustc).expect_err("compiler alias symlink must fail");
        assert!(error.contains("symlink"), "{error}");
    }

    #[test]
    fn guarded_operation_rejects_same_byte_replacement_before_it_runs() {
        let fixture = Fixture::new("pre-run-replacement");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        let replacement = fixture.path("replacement");
        let sentinel = fixture.path("sentinel");
        write_executable(&trustc, b"authenticated Trust compiler");
        write_executable(&rustc, b"authenticated Trust compiler");
        let authenticated =
            AuthenticatedCompiler::alias(trustc, rustc.clone()).expect("authenticate initial compiler alias");

        write_executable(&replacement, b"authenticated Trust compiler");
        let replacement_attempt = fs::remove_file(&rustc).and_then(|()| fs::rename(&replacement, &rustc));
        if replacement_attempt.is_err() {
            // Windows selection handles close the between-capture-and-launch
            // gap by preventing replacement, not merely detecting it later.
            assert!(!sentinel.exists());
            return;
        }

        let result = authenticated.run_guarded(|| fs::write(&sentinel, b"operation ran"));
        assert!(
            result.is_err(),
            "same-byte replacement with a new identity was accepted"
        );
        assert!(!sentinel.exists(), "guarded operation ran despite failed pre-check");
    }

    #[cfg(unix)]
    #[test]
    fn latest_spawn_boundary_recheck_prevents_replaced_alias_child_launch() {
        use std::process::Command;

        let fixture = Fixture::new("spawn-boundary-replacement");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        let replacement = fixture.path("replacement");
        let sentinel = fixture.path("sentinel");
        write_executable(&trustc, b"authenticated Trust compiler");
        write_executable(&rustc, b"authenticated Trust compiler");
        let authenticated =
            AuthenticatedCompiler::alias(trustc, rustc.clone()).expect("authenticate initial compiler alias");

        write_executable(&replacement, b"authenticated Trust compiler");
        fs::remove_file(&rustc).expect("remove authenticated alias path");
        fs::rename(&replacement, &rustc).expect("install same-byte replacement alias");

        let result = authenticated.run_guarded(|| {
            Command::new("sh")
                .args(["-c", "printf launched > \"$TIPPY_TEST_SENTINEL\""])
                .env("TIPPY_TEST_SENTINEL", &sentinel)
                .status()
        });
        assert!(
            result.is_err(),
            "same-byte replacement reached the child spawn boundary"
        );
        assert!(
            !sentinel.exists(),
            "child launched despite failed latest-boundary recheck"
        );
    }

    #[cfg(unix)]
    #[test]
    fn post_run_check_detects_same_inode_swap_and_restore() {
        let fixture = Fixture::new("post-run-swap-restore");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        let saved = fixture.path("rustc-saved");
        let hostile = fixture.path("hostile");
        let sentinel = fixture.path("sentinel");
        write_executable(&trustc, b"hard-linked authenticated Trust compiler");
        fs::hard_link(&trustc, &rustc).expect("create initial hard-linked alias");
        write_executable(&hostile, b"hostile replacement compiler bytes");
        let authenticated =
            AuthenticatedCompiler::alias(trustc, rustc.clone()).expect("authenticate hard-linked compiler alias");

        let result = authenticated.run_guarded(|| {
            fs::rename(&rustc, &saved).expect("save authenticated inode");
            fs::copy(&hostile, &rustc).expect("install hostile compiler");
            fs::remove_file(&rustc).expect("remove hostile compiler");
            fs::rename(&saved, &rustc).expect("restore exact authenticated inode");
            fs::write(&sentinel, b"operation completed").expect("record completed operation");
        });
        assert!(result.is_err(), "swap-and-restore escaped the post-run directory check");
        assert!(
            sentinel.exists(),
            "fixture operation did not complete its swap-and-restore sequence"
        );
    }

    #[cfg(unix)]
    #[test]
    fn compiler_guard_rejects_ancestor_redirect_restore_after_raced_child_runs() {
        use std::os::unix::fs::symlink;
        use std::process::Command;

        let fixture = Fixture::new("ancestor-redirect-restore");
        let selected_root = fixture.path("selected");
        let selected_bin = selected_root.join("bin");
        let attacker_root = fixture.path("attacker");
        let attacker_bin = attacker_root.join("bin");
        fs::create_dir_all(&selected_bin).expect("create selected toolchain directory");
        fs::create_dir_all(&attacker_bin).expect("create attacker toolchain directory");
        let trustc = selected_bin.join("trustc");
        write_executable(&trustc, b"#!/bin/sh\nexit 0\n");
        write_executable(&attacker_bin.join("trustc"), b"#!/bin/sh\nexit 23\n");
        let saved_root = fixture.path("selected-saved");

        let authenticated = AuthenticatedCompiler::selected_trustc(trustc.clone())
            .expect("authenticate selected compiler and its ancestor chain");
        let mut hostile_child_ran = false;
        let result = authenticated.run_guarded(|| {
            fs::rename(&selected_root, &saved_root).expect("save selected toolchain root");
            symlink(&attacker_root, &selected_root).expect("redirect selected toolchain root");
            let status = Command::new(&trustc)
                .status()
                .expect("run compiler through redirected pathname");
            hostile_child_ran = status.code() == Some(23);
            fs::remove_file(&selected_root).expect("remove attacker redirect");
            fs::rename(&saved_root, &selected_root).expect("restore exact selected toolchain root");
        });

        assert!(hostile_child_ran, "fixture did not execute the redirected compiler");
        assert!(
            result.is_err(),
            "an ancestor redirect-and-restore escaped the compiler directory-chain guard"
        );
    }
}
