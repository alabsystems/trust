//! Stable identity checks for the compiler selected by branded Tippy.
//!
//! Tippy runs `trustc` — the Trust compiler under its own name, beside Tippy in
//! the installed toolchain bin directory so rustc's sysroot discovery works. It
//! does not run a `rustc`-named sibling and does not authenticate one.
//!
//! That is a design decision, recorded here because the opposite one cost a
//! lint lane. The distribution shipped `rustc` as a second COPY of `trustc`
//! for rustup's and cargo's benefit, and Tippy preferred it for build scripts
//! that grep a `rustc` banner. Keeping two copies honest then needed a proof
//! that they were the same compiler, and the proof chosen was byte identity —
//! which macOS makes impossible: an ad-hoc code signature bakes the file's own
//! basename into itself, so two names for one image are never byte-equal.
//! Measured 2026-09-14 on an installed store: 2,428 differing bytes, every one
//! of them inside the signature blob, and 317,296 identical bytes of code in
//! front. Tippy refused a correct toolchain for that, and every lint lane on
//! the machine went with it. A check that asks the wrong question of a file
//! that should not be there is not repaired by asking a cleverer question; it
//! is repaired by not needing the file. `trustc`'s own banner begins
//! `rustc 1.99.0-dev …`, which is what the build-script argument was about, so
//! running the compiler under its own name loses nothing.
//!
//! Tippy must keep the compiler pathname inside the installed toolchain bin
//! directory so rustc can discover its sibling sysroot. Consequently this
//! module cannot hand Targo an already-open compiler handle. It instead binds
//! the pathname as tightly as the portable interface allows: an exact
//! executable identity, the launch and canonical directory-ancestor chains,
//! bounded bytes, checks before/open/after reading, a final check immediately
//! around the Targo child lifetime, and a live handle held across that
//! lifetime.

use std::fs;
use std::path::{Path, PathBuf};

use super::path_identity::{
    AuthenticatedDirectoryChain, DirectoryChainGuard, OpenedExecutable, PathSnapshot,
};

// A Trust compiler frontend is normally far smaller than this, including
// debug builds. Keep the ceiling generous enough for supported stage2
// toolchains while preventing a forged sibling from turning Tippy startup into
// an unbounded read.
#[cfg(test)]
const MAX_COMPILER_EXECUTABLE_BYTES: u64 = super::path_identity::MAX_AUTHENTICATED_EXECUTABLE_BYTES;

#[derive(Debug)]
struct ToolchainBinDirectory {
    chain: AuthenticatedDirectoryChain,
}

impl ToolchainBinDirectory {
    fn authenticate(trustc: &Path) -> Result<Self, String> {
        let trustc_parent = trustc.parent().ok_or_else(|| {
            format!(
                "selected trustc `{}` has no toolchain bin directory",
                trustc.display()
            )
        })?;
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

#[derive(Debug)]
pub(crate) struct AuthenticatedCompiler {
    path: PathBuf,
    bin_directory: ToolchainBinDirectory,
    snapshot: PathSnapshot,
    // On Windows this retained read-sharing handle prevents a same-length
    // rewrite/replacement from being hidden by restoring writable timestamps
    // between initial authentication and the launch-boundary revalidation.
    _selected: fs::File,
}

impl AuthenticatedCompiler {
    pub(crate) fn selected_trustc(path: PathBuf) -> Result<Self, String> {
        let bin_directory = ToolchainBinDirectory::authenticate(&path)?;
        let trustc = OpenedExecutable::open(path.clone(), "compiler trustc")?;
        trustc.confirm_stable("compiler trustc")?;
        let _ = bin_directory.revalidate()?;
        Ok(Self {
            path,
            bin_directory,
            snapshot: trustc.snapshot,
            _selected: trustc.file,
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
        let _guard = self.revalidate().map_err(|error| {
            format!("compiler authentication failed before Targo launch: {error}")
        })?;
        let result = operation();
        let _post_guard = self.revalidate().map_err(|error| {
            format!("compiler identity changed while Targo was running: {error}")
        })?;
        Ok(result)
    }

    fn revalidate(&self) -> Result<CompilerSpawnGuard, String> {
        let bin_directory = self.bin_directory.revalidate()?;
        let trustc = OpenedExecutable::open(self.path.clone(), "compiler trustc")?;
        trustc.confirm_stable("compiler trustc")?;
        self.bin_directory
            .confirm_stable_with_guard(&bin_directory)?;
        if trustc.snapshot != self.snapshot {
            return Err(format!(
                "selected compiler `{}` changed identity, length, or contents",
                self.path.display()
            ));
        }
        Ok(CompilerSpawnGuard {
            _bin_directory: bin_directory,
            _trustc: trustc.file,
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
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::sync::{Mutex, MutexGuard};
    use std::time::{SystemTime, UNIX_EPOCH};
    use std::{env, fs};

    #[cfg(windows)]
    use super::super::path_identity::AuthenticatedDirectoryChain;
    use super::super::path_identity::AuthenticatedExecutable;
    use super::{AuthenticatedCompiler, MAX_COMPILER_EXECUTABLE_BYTES};

    // The next fixture's sequence number, behind the lock that serializes
    // fixtures. A std `Mutex<u64>`, not an `AtomicU64` (not portable, so
    // Targo's clippy.toml disallows std's) and not `portable_atomic` (Tippy
    // compiles this file by `#[path]` and has no such dependency): the same
    // std-only portable counter as overlay.rs's filtered-directory nonce.
    static FIXTURE_LOCK: Mutex<u64> = Mutex::new(0);

    struct Fixture {
        root: PathBuf,
        _lock: MutexGuard<'static, u64>,
    }

    impl Fixture {
        fn new(label: &str) -> Self {
            // Every authenticated fixture records the writable temporary
            // directory in its ancestor chain. Serialize fixture lifecycle so
            // sibling tests cannot mutate that shared directory while a guard
            // is deliberately checking it.
            let mut lock = FIXTURE_LOCK
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system clock after Unix epoch")
                .as_nanos();
            let sequence = *lock;
            *lock = sequence
                .checked_add(1)
                .expect("compiler fixture sequence is exhausted");
            let temp = env::temp_dir()
                .canonicalize()
                .unwrap_or_else(|_| env::temp_dir());
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

            let mut permissions = fs::metadata(path)
                .expect("executable fixture metadata")
                .permissions();
            permissions.set_mode(0o700);
            fs::set_permissions(path, permissions).expect("mark executable fixture executable");
        }
        #[cfg(not(unix))]
        let _ = path;
    }

    #[test]
    fn selected_trustc_is_revalidated() {
        let fixture = Fixture::new("selected-trustc");
        let trustc = fixture.path("trustc");
        write_executable(&trustc, b"selected Trust compiler");

        let authenticated = AuthenticatedCompiler::selected_trustc(trustc.clone())
            .expect("authenticate selected trustc");
        assert_eq!(authenticated.path(), trustc);
        assert_eq!(authenticated.run_guarded(|| 17_u8), Ok(17));
    }

    /// The design pin. A `rustc` beside `trustc` — whatever it holds — is not
    /// consulted: Tippy runs the compiler under its own name, so nothing about
    /// that file can make a correct toolchain fail, and nothing in it can be
    /// lent Trust's authority.
    #[test]
    fn a_rustc_sibling_is_neither_required_nor_consulted() {
        let fixture = Fixture::new("stock-name-sibling-ignored");
        let trustc = fixture.path("trustc");
        let rustc = fixture.path("rustc");
        write_executable(&trustc, b"the Trust compiler");
        write_executable(&rustc, b"something else entirely, occupying the stock name");

        let authenticated = AuthenticatedCompiler::selected_trustc(trustc.clone())
            .expect("trustc authenticates on its own");
        assert_eq!(authenticated.path(), trustc);
        assert_eq!(authenticated.run_guarded(|| 3_u8), Ok(3));

        // What the sibling HOLDS is irrelevant to the guard: rewriting it in
        // place changes no identity Tippy recorded.
        fs::write(&rustc, b"rewritten while guarded").expect("rewrite the ignored sibling");
        assert_eq!(authenticated.run_guarded(|| 4_u8), Ok(4));

        // Removing it is refused — but by the toolchain DIRECTORY guard, which
        // watches the bin directory's contents against any entry churn, and not
        // by anything that knows what a `rustc` is. The message names the
        // directory, not the file.
        fs::remove_file(&rustc).expect("remove the ignored sibling");
        let error = authenticated
            .run_guarded(|| 5_u8)
            .expect_err("directory churn is still refused");
        assert!(
            error.contains("directory ancestor") && !error.contains("rustc"),
            "{error}"
        );
    }

    #[test]
    fn oversized_trustc_is_rejected_before_reading() {
        let fixture = Fixture::new("oversized");
        let trustc = fixture.path("trustc");
        let oversized = fs::File::create(&trustc).expect("create sparse oversized compiler");
        oversized
            .set_len(MAX_COMPILER_EXECUTABLE_BYTES + 1)
            .expect("extend sparse oversized compiler");
        drop(oversized);
        make_executable(&trustc);

        let error = AuthenticatedCompiler::selected_trustc(trustc)
            .expect_err("an oversized compiler must fail before reading");
        assert!(error.contains("byte bound"), "{error}");
    }

    #[test]
    fn non_regular_trustc_is_rejected() {
        let fixture = Fixture::new("directory-trustc");
        let trustc = fixture.path("trustc");
        fs::create_dir(&trustc).expect("create directory in the compiler's position");

        let error =
            AuthenticatedCompiler::selected_trustc(trustc).expect_err("a directory must fail");
        assert!(error.contains("not a regular file"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_trustc_is_rejected_even_when_its_target_is_genuine() {
        use std::os::unix::fs::symlink;

        let fixture = Fixture::new("symlink");
        let real = fixture.path("trustc-real");
        let trustc = fixture.path("trustc");
        write_executable(&real, b"Trust compiler behind a forbidden symlink");
        symlink(&real, &trustc).expect("create compiler symlink");

        let error = AuthenticatedCompiler::selected_trustc(trustc)
            .expect_err("a symlinked compiler must fail");
        assert!(error.contains("symlink"), "{error}");
    }

    #[test]
    fn guarded_operation_rejects_same_byte_replacement_before_it_runs() {
        let fixture = Fixture::new("pre-run-replacement");
        let trustc = fixture.path("trustc");
        let replacement = fixture.path("replacement");
        let sentinel = fixture.path("sentinel");
        write_executable(&trustc, b"authenticated Trust compiler");
        let authenticated = AuthenticatedCompiler::selected_trustc(trustc.clone())
            .expect("authenticate the initial compiler");

        write_executable(&replacement, b"authenticated Trust compiler");
        let replacement_attempt =
            fs::remove_file(&trustc).and_then(|()| fs::rename(&replacement, &trustc));
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
        assert!(
            !sentinel.exists(),
            "guarded operation ran despite failed pre-check"
        );
    }

    #[cfg(unix)]
    #[test]
    fn latest_spawn_boundary_recheck_prevents_replaced_compiler_child_launch() {
        use std::process::Command;

        let fixture = Fixture::new("spawn-boundary-replacement");
        let trustc = fixture.path("trustc");
        let replacement = fixture.path("replacement");
        let sentinel = fixture.path("sentinel");
        write_executable(&trustc, b"authenticated Trust compiler");
        let authenticated = AuthenticatedCompiler::selected_trustc(trustc.clone())
            .expect("authenticate the initial compiler");

        write_executable(&replacement, b"authenticated Trust compiler");
        fs::remove_file(&trustc).expect("remove the authenticated compiler path");
        fs::rename(&replacement, &trustc).expect("install same-byte replacement compiler");

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
        let saved = fixture.path("trustc-saved");
        let hostile = fixture.path("hostile");
        let sentinel = fixture.path("sentinel");
        write_executable(&trustc, b"authenticated Trust compiler");
        write_executable(&hostile, b"hostile replacement compiler bytes");
        let authenticated = AuthenticatedCompiler::selected_trustc(trustc.clone())
            .expect("authenticate the compiler");

        let result = authenticated.run_guarded(|| {
            fs::rename(&trustc, &saved).expect("save authenticated inode");
            fs::copy(&hostile, &trustc).expect("install hostile compiler");
            fs::remove_file(&trustc).expect("remove hostile compiler");
            fs::rename(&saved, &trustc).expect("restore exact authenticated inode");
            fs::write(&sentinel, b"operation completed").expect("record completed operation");
        });
        assert!(
            result.is_err(),
            "swap-and-restore escaped the post-run directory check"
        );
        assert!(
            sentinel.exists(),
            "fixture operation did not complete its swap-and-restore sequence"
        );
    }

    #[test]
    fn sibling_guard_rejects_in_place_tool_rewrite() {
        let fixture = Fixture::new("sibling-in-place-rewrite");
        let targo = fixture.path("targo");
        write_executable(&targo, b"authenticated targo bytes");
        let authenticated = AuthenticatedExecutable::capture(targo.clone(), "targo")
            .expect("authenticate Targo sibling");

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
        let replacement_attempt =
            fs::remove_file(&driver).and_then(|()| fs::rename(&replacement, &driver));
        if replacement_attempt.is_err() {
            // Windows selection handles deny delete sharing, preventing the
            // replacement before a child can be considered for launch.
            assert!(!sentinel.exists());
            return;
        }
        let result =
            authenticated.run_guarded_for("Targo", || fs::write(&sentinel, b"child launched"));
        assert!(
            result.is_err(),
            "a replacement driver reached the launch boundary"
        );
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

        let executable = AuthenticatedExecutable::capture(targo.clone(), "targo")
            .expect("authenticate selected Windows executable");
        assert!(
            fs::OpenOptions::new().write(true).open(&targo).is_err(),
            "a retained executable handle unexpectedly shared write authority"
        );

        let directories = AuthenticatedDirectoryChain::capture(&bin)
            .expect("authenticate selected Windows directory chain");
        let renamed = fixture.path("bin-renamed");
        assert!(
            fs::rename(&bin, &renamed).is_err(),
            "a retained directory handle unexpectedly shared delete/rename authority"
        );

        drop(directories);
        drop(executable);
        fs::rename(&bin, &renamed).expect("selection locks are released when guards are dropped");
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

        assert!(
            hostile_child_ran,
            "fixture did not execute the redirected compiler"
        );
        assert!(
            result.is_err(),
            "an ancestor redirect-and-restore escaped the compiler directory-chain guard"
        );
    }
}
