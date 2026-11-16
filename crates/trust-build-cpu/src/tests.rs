// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;

// File descriptors belong to the process, not the test thread. A concurrent
// spawn may temporarily inherit another fixture's locked description before
// exec closes it, so each kernel fixture owns the process's descriptor table
// through its final close and child reap. Child fixtures exec a fresh test
// process and therefore have their own guard. The guard excludes only tests
// that take it: every test that spawns a child takes it before the spawn and
// keeps it until the child is reaped. On macOS even a plain posix_spawn, with
// or without POSIX_SPAWN_CLOEXEC_DEFAULT, briefly keeps a dropped lease held.
// `every_spawn_site_holds_the_kernel_fixture` checks the spawner half.
#[cfg(unix)]
static KERNEL_FIXTURE: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(unix)]
thread_local! {
    static HELD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// This thread's hold on the kernel fixture. Only `kernel_fixture` makes one,
/// and it cannot leave its thread.
#[cfg(unix)]
pub(crate) struct KernelFixture {
    _guard: std::sync::MutexGuard<'static, ()>,
}

#[cfg(unix)]
impl Drop for KernelFixture {
    fn drop(&mut self) {
        HELD.set(false);
    }
}

/// Take the kernel fixture. The mutex is not reentrant: a thread that already
/// holds it would deadlock, so a second take on one thread panics instead.
#[cfg(unix)]
pub(crate) fn kernel_fixture() -> KernelFixture {
    assert!(!HELD.get(), "this thread already holds the kernel fixture");
    let guard = KERNEL_FIXTURE.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    HELD.set(true);
    KernelFixture { _guard: guard }
}

/// Whether this thread holds the kernel fixture now.
#[cfg(unix)]
pub(crate) fn kernel_fixture_held() -> bool {
    HELD.get()
}

/// A fixture root, owner-only whatever the umask. tempfile makes a TempDir
/// 0777 less the umask, and this crate refuses a capacity parent that group
/// or others can write, so under umask 002 a plain TempDir is refused before
/// the behavior under test is reached.
#[cfg(unix)]
pub(crate) fn private_tempdir() -> tempfile::TempDir {
    use std::os::unix::fs::PermissionsExt;
    let directory = tempfile::Builder::new()
        .permissions(std::fs::Permissions::from_mode(0o700))
        .tempdir()
        .unwrap();
    // mkdir applies the umask to the mode it is given: state the mode exactly.
    std::fs::set_permissions(directory.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
    directory
}

/// A new fixture directory, 0700 whatever the umask.
#[cfg(unix)]
pub(crate) fn private_dir(path: &std::path::Path) {
    use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
    std::fs::DirBuilder::new().mode(0o700).create(path).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
}

/// A new fixture file, 0600 whatever the umask.
#[cfg(unix)]
pub(crate) fn private_file(path: &std::path::Path, bytes: impl AsRef<[u8]>) {
    use std::io::Write;
    use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
    let mut file =
        std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(path).unwrap();
    file.set_permissions(std::fs::Permissions::from_mode(0o600)).unwrap();
    file.write_all(bytes.as_ref()).unwrap();
}

#[cfg(unix)]
pub(crate) mod descriptor_copy;

/// Spawn sites in this crate's own sources that are not test code, with why
/// none takes the kernel fixture: (file, enclosing function, reason).
#[cfg(unix)]
const UNFIXTURED_SPAWNS: [(&str, &str, &str); 1] = [(
    "src/monitor.rs",
    "probe",
    "production: the monitor's own probe child; tests start it only through the Monitor's \
     spawn entry points (spawn and spawn_with), and each test's call of either is itself a \
     scanned site",
)];

/// The kernel fixture's spawner rule, checked: in every source file of this
/// crate, each spawn site's enclosing function takes the kernel fixture before
/// the site, or names `KernelFixture` (a `&KernelFixture` parameter, which
/// only a holder can lend), or is listed in `UNFIXTURED_SPAWNS`. The check is
/// lexical. It does not see spawns inside other crates' APIs, nor whether the
/// hold lasts until the child is reaped, nor the tests that only drop leases.
#[cfg(unix)]
#[test]
fn every_spawn_site_holds_the_kernel_fixture() {
    // Split so that these needles are not spawn sites themselves. The last is
    // a prefix: it names every Monitor entry point that starts its sampler.
    const SITES: [&str; 5] = [
        concat!("Command", "::new("),
        concat!(".pre", "_exec("),
        concat!("fo", "rk("),
        concat!("posix", "_spawn"),
        concat!("Monitor", "::spawn"),
    ];
    let mut unfixtured = Vec::new();
    let mut listed = std::collections::BTreeSet::new();
    for site in source_sites(&SITES) {
        let (file, line) = (&site.file, site.line);
        let Some((name, body)) = &site.function else {
            unfixtured.push(format!("{file}:{line}: outside any function"));
            continue;
        };
        if let Some(entry) =
            UNFIXTURED_SPAWNS.iter().position(|&(entry_file, entry_function, _)| {
                entry_file == file && entry_function == name
            })
        {
            listed.insert(entry);
        } else if !body
            .iter()
            .any(|line| line.contains("kernel_fixture()") || line.contains("KernelFixture"))
        {
            unfixtured.push(format!("{file}:{line}: in fn {name}"));
        }
    }
    assert!(
        unfixtured.is_empty(),
        "spawn sites without the kernel fixture:\n{}",
        unfixtured.join("\n")
    );
    assert_eq!(
        listed.len(),
        UNFIXTURED_SPAWNS.len(),
        "an UNFIXTURED_SPAWNS entry names no spawn site"
    );
}

/// One code line of this crate's own sources (src/ and tests/) that contains
/// a needle: its path from the manifest directory, its 1-based line, and its
/// lexically enclosing function (the nearest `fn` line at or above it) with
/// that function's code lines through the site, or `None` outside any.
#[cfg(unix)]
struct SourceSite {
    file: String,
    line: usize,
    function: Option<(String, Vec<String>)>,
}

/// Every source line that contains one of `needles`, outside `//` comments.
#[cfg(unix)]
fn source_sites(needles: &[&str]) -> Vec<SourceSite> {
    fn sources(directory: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(directory).unwrap() {
            let entry = entry.unwrap();
            let kind = entry.file_type().unwrap();
            if kind.is_dir() {
                sources(&entry.path(), files);
            } else if kind.is_file() && entry.path().extension().is_some_and(|ext| ext == "rs") {
                files.push(entry.path());
            }
        }
    }
    fn function(line: &str) -> Option<&str> {
        let mut rest = line.trim_start();
        for qualifier in ["pub(crate) ", "pub(super) ", "pub ", "const ", "async ", "unsafe "] {
            rest = rest.strip_prefix(qualifier).unwrap_or(rest);
        }
        let rest = rest.strip_prefix("fn ")?;
        rest.find(|c: char| !(c.is_alphanumeric() || c == '_')).map(|end| &rest[..end])
    }
    fn code(line: &str) -> bool {
        !line.trim_start().starts_with("//")
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    for directory in ["src", "tests"] {
        sources(&root.join(directory), &mut files);
    }
    let mut sites = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(path).unwrap();
        let file = path.strip_prefix(root).unwrap().to_str().unwrap();
        let lines: Vec<&str> = text.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            if !code(line) || !needles.iter().any(|needle| line.contains(needle)) {
                continue;
            }
            let enclosing =
                (0..=index).rev().find(|&at| function(lines[at]).is_some()).map(|start| {
                    let body = lines[start..=index].iter().filter(|line| code(line));
                    (
                        function(lines[start]).unwrap().to_owned(),
                        body.map(|line| (*line).to_owned()).collect(),
                    )
                });
            sites.push(SourceSite { file: file.to_owned(), line: index + 1, function: enclosing });
        }
    }
    sites
}

/// Temporary directories in this crate's own sources that are not made by
/// `private_tempdir`, with why: (file, enclosing function, reason).
#[cfg(unix)]
const UNPRIVATE_ROOTS: [(&str, &str, &str); 3] = [
    ("src/tests.rs", "private_tempdir", "the helper itself, which states the mode exactly"),
    (
        "src/legacy_retirement/tests.rs",
        "created_capacity_parent_is_owner_only_under_a_group_writable_umask",
        "sets umask 002 itself, alone in a fresh process, and checks the modes of the \
         directories made inside this root, not the root's",
    ),
    (
        "src/recovery_material/tests.rs",
        "directory",
        "a separate test binary, which cannot reach this crate's test helpers; it sets 0700 \
         on the root itself",
    ),
];

/// What `every_fixture_root_is_private` flags. Split so that these needles are
/// not fixture roots themselves. An import is flagged too, since it can rename
/// any constructor.
#[cfg(unix)]
const FIXTURE_ROOT_NEEDLES: [&str; 5] = [
    concat!("tempfile::", "tempdir"),
    concat!("tempfile::", "Builder"),
    concat!("TempDir", "::new"),
    concat!("TempDir", "::with_"),
    concat!("use ", "tempfile"),
];

/// Each needle flags its own spelling of a fixture root and no other needle
/// does, so dropping or changing a needle leaves a spelling unflagged and
/// fails here.
#[cfg(unix)]
#[test]
fn every_fixture_root_needle_flags_its_own_spelling() {
    let spellings = [
        concat!("let root = tempfile::", "tempdir().unwrap();"),
        concat!("let root = tempfile::", "Builder::new().tempdir().unwrap();"),
        concat!("let root = TempDir", "::new().unwrap();"),
        concat!("let root = TempDir", "::with_prefix(\"fixture\").unwrap();"),
        concat!("use ", "tempfile as scratch;"),
    ];
    assert_eq!(spellings.len(), FIXTURE_ROOT_NEEDLES.len(), "one spelling per needle");
    for (needle, spelling) in FIXTURE_ROOT_NEEDLES.iter().zip(spellings) {
        let flagging: Vec<&str> = FIXTURE_ROOT_NEEDLES
            .iter()
            .copied()
            .filter(|candidate| spelling.contains(candidate))
            .collect();
        assert_eq!(flagging, [*needle], "{spelling:?} must be flagged by its own needle alone");
    }
}

/// Fixture roots stay owner-only whatever the umask, checked: every temporary
/// directory in this crate's sources is made by `private_tempdir`, or its
/// enclosing function is listed in `UNPRIVATE_ROOTS`. Under umask 002 a plain
/// TempDir is group writable: the capacity code refuses it as a parent, and
/// anyone in the group could replace what a test keeps or runs there. The
/// check is lexical, like the spawner rule above.
#[cfg(unix)]
#[test]
fn every_fixture_root_is_private() {
    let mut unprivate = Vec::new();
    let mut listed = std::collections::BTreeSet::new();
    for site in source_sites(&FIXTURE_ROOT_NEEDLES) {
        let (file, line) = (&site.file, site.line);
        let Some((name, _)) = &site.function else {
            unprivate.push(format!("{file}:{line}: outside any function"));
            continue;
        };
        if let Some(entry) = UNPRIVATE_ROOTS.iter().position(|&(entry_file, entry_function, _)| {
            entry_file == file && entry_function == name
        }) {
            listed.insert(entry);
        } else {
            unprivate.push(format!("{file}:{line}: in fn {name}"));
        }
    }
    assert!(
        unprivate.is_empty(),
        "fixture roots not made by private_tempdir:\n{}",
        unprivate.join("\n")
    );
    assert_eq!(
        listed.len(),
        UNPRIVATE_ROOTS.len(),
        "an UNPRIVATE_ROOTS entry names no fixture root"
    );
}

#[test]
fn records_round_trip_and_refuse_unbounded_or_ambiguous_input() {
    for birth in [None, Some(0), Some(u64::MAX)] {
        let record = Record { slot: 7, owner: Owner { pid: 42, birth } };
        assert_eq!(Record::parse(&record.encode()).unwrap(), record);
    }
    for text in [
        "trust-build-cpu-v2 slot=0 pid=1 birth=- held=1\n",
        "trust-build-cpu-v1 slot=0 pid=0 birth=- held=1\n",
        "trust-build-cpu-v1 slot=0 pid=1 birth=- held=0\n",
        "trust-build-cpu-v1 slot=+0 pid=1 birth=- held=1\n",
        "trust-build-cpu-v1 slot=00 pid=1 birth=- held=1\n",
        "trust-build-cpu-v1 slot=0 pid=1 birth=- held=1\n\n",
        "trust-build-cpu-v1 slot=0 pid=1 birth=- held=1 extra=1\n",
        "trust-build-cpu-v1 slot=0 pid=1 birth=- held=1",
    ] {
        assert!(Record::parse(text).is_err(), "accepted {text:?}");
    }
    assert!(Record::parse(&"x".repeat(MAX_RECORD_BYTES + 1)).is_err());
}

#[cfg(unix)]
mod unix {
    use std::io::{BufRead, Read, Write};
    use std::num::NonZeroU32;
    use std::os::fd::FromRawFd;
    use std::os::unix::fs::{PermissionsExt, symlink};
    use std::process::{Child, Command, Stdio};
    use std::time::{Duration, Instant};

    use super::*;

    fn width(value: u32) -> NonZeroU32 {
        NonZeroU32::new(value).unwrap()
    }
    fn owner() -> Owner {
        Owner::current(Some(123))
    }

    #[test]
    fn independent_pool_handles_share_exact_unit_capacity() {
        let fixture = kernel_fixture();
        let dir = private_tempdir();
        let first = Pool::open_in(dir.path(), width(2)).unwrap();
        let second = Pool::open_in(dir.path(), width(2)).unwrap();
        let a = first.try_acquire(owner()).unwrap().unwrap();
        let b = second.try_acquire(owner()).unwrap().unwrap();
        assert_ne!(a.slot(), b.slot());
        assert!(first.try_acquire(owner()).unwrap().is_none());
        assert!(
            second.snapshot().unwrap().iter().all(|state| matches!(state, SlotState::Held { .. }))
        );
        // An inherited duplicate still consumes a's slot even after this
        // process drops a. The independent handle cannot reuse it until the
        // child proves it started, closes the descriptor and is reaped.
        let mut child =
            start(&fixture, "inherit", dir.path(), Some(a.try_clone().unwrap().into_file()));
        drop(a);
        assert!(second.try_acquire(owner()).unwrap().is_none());
        child.0.stdin.as_mut().unwrap().write_all(b"x").unwrap();
        assert!(wait(&mut child).success());
        let c = second.try_acquire(owner()).unwrap().unwrap();
        assert_ne!(b.slot(), c.slot());
        drop((b, c));
        assert!(
            first
                .snapshot()
                .unwrap()
                .iter()
                .all(|state| matches!(state, SlotState::Available { .. }))
        );
    }

    #[test]
    fn duplicate_descriptor_keeps_lease_until_final_close() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let lease = pool.try_acquire(owner()).unwrap().unwrap();
        let duplicate = lease.try_clone().unwrap();
        drop(lease);
        assert!(pool.try_acquire(owner()).unwrap().is_none());
        drop(duplicate);
        assert!(pool.try_acquire(owner()).unwrap().is_some());
    }

    #[test]
    fn opening_an_existing_pool_refuses_an_active_initializer_without_waiting() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let held =
            std::fs::OpenOptions::new().write(true).open(pool.path().join("init.lock")).unwrap();
        held.lock().unwrap();
        assert!(Pool::open_in(dir.path(), width(1)).is_err());
        held.unlock().unwrap();
        assert!(Pool::open_in(dir.path(), width(1)).is_ok());
    }

    #[test]
    fn stale_unlocked_metadata_is_available_but_corrupt_held_metadata_is_busy() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let mut file = pool.try_acquire(owner()).unwrap().unwrap().into_file();
        file.set_len(0).unwrap();
        file.write_all(&vec![b'x'; MAX_RECORD_BYTES + 1]).unwrap();
        assert_eq!(pool.snapshot().unwrap(), [SlotState::Held { slot: 0, reported_owner: None }]);
        drop(file);
        assert_eq!(pool.snapshot().unwrap(), [SlotState::Available { slot: 0 }]);
        let lease = pool.try_acquire(owner()).unwrap().unwrap();
        assert_eq!(
            pool.snapshot().unwrap(),
            [SlotState::Held { slot: 0, reported_owner: Some(owner()) }]
        );
        drop(lease);
    }

    #[test]
    fn pool_width_cannot_change_under_existing_users() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        assert_eq!(
            Pool::open_in(dir.path(), width(2)).unwrap_err().kind(),
            std::io::ErrorKind::InvalidData
        );
        assert_eq!(pool.slots(), width(1));
    }

    #[test]
    fn observation_does_not_create_or_repair_a_pool() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let absent = dir.path().join("absent");
        assert!(Pool::open_existing(&absent).unwrap().is_none());
        assert!(!absent.exists());
        assert!(Pool::open_existing(dir.path()).unwrap().is_none());
        assert!(!dir.path().join(DIRECTORY_NAME).exists());
        let pool = Pool::open_in(dir.path(), width(2)).unwrap();
        let read = Pool::open_existing(dir.path()).unwrap().unwrap();
        assert_eq!(read.slots(), width(2));
        assert_eq!(pool.snapshot().unwrap(), read.snapshot().unwrap());
    }

    #[test]
    fn readable_capacity_parent_does_not_require_permission_rewriting() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o755)).unwrap();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        assert_eq!(std::fs::metadata(dir.path()).unwrap().permissions().mode() & 0o777, 0o755);
        assert_eq!(std::fs::metadata(pool.path()).unwrap().permissions().mode() & 0o777, 0o700);
        assert!(pool.try_acquire(owner()).unwrap().is_some());
    }

    #[test]
    fn replacing_a_leased_slot_never_creates_duplicate_capacity() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let lease = pool.try_acquire(owner()).unwrap().unwrap();
        let slot = pool.path().join("slot-00000000");
        std::fs::rename(&slot, pool.path().join("former-slot")).unwrap();
        private_file(&slot, b"");
        assert!(pool.try_acquire(owner()).is_err());
        assert!(pool.snapshot().is_err());
        assert!(Pool::open_in(dir.path(), width(1)).is_err());
        assert!(Pool::open_existing(dir.path()).is_err());
        drop(lease);
    }

    #[test]
    fn readers_report_initialization_without_waiting_for_its_lock() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let path = pool.path().join("pool");
        let before = std::fs::read(&path).unwrap();
        let initialization =
            std::fs::OpenOptions::new().write(true).open(pool.path().join("init.lock")).unwrap();
        initialization.lock().unwrap();
        let mut config = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
        config.set_len(0).unwrap();
        config.write_all(b"partial initialization").unwrap();
        let root = dir.path().to_owned();
        let (send, receive) = std::sync::mpsc::channel();
        let reader = std::thread::spawn(move || {
            let opened = Pool::open_existing(&root).unwrap_err().kind();
            let snapshot = pool.snapshot().unwrap_err().kind();
            send.send((opened, snapshot)).unwrap();
        });
        let result = receive
            .recv_timeout(Duration::from_secs(60))
            .expect("read-only pool observation must not wait on initialization");
        assert_eq!(result, (std::io::ErrorKind::WouldBlock, std::io::ErrorKind::WouldBlock));
        reader.join().unwrap();
        assert_eq!(std::fs::read(&path).unwrap(), b"partial initialization");
        config.set_len(0).unwrap();
        use std::io::{Seek, SeekFrom};
        config.seek(SeekFrom::Start(0)).unwrap();
        config.write_all(&before).unwrap();
        drop(config);
        drop(initialization);
        assert!(Pool::open_existing(dir.path()).unwrap().is_some());
    }

    #[test]
    fn interrupted_unpublished_initialization_is_not_repaired() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let path = dir.path().join(DIRECTORY_NAME);
        private_dir(&path);
        for name in ["slot-00000000", ".pool-init-dead"] {
            private_file(&path.join(name), b"incomplete unpublished data");
        }
        assert!(Pool::open_in(dir.path(), width(1)).is_err());
        assert!(!path.join("pool").exists());
    }

    #[test]
    fn existing_pool_opens_under_a_read_only_capacity_parent() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(2)).unwrap();
        std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o500)).unwrap();
        let result = Pool::open_in(dir.path(), width(2));
        let mismatch = Pool::open_in(dir.path(), width(1));
        std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
        let reopened = result.unwrap();
        assert_eq!(reopened.path(), pool.path());
        assert!(reopened.try_acquire(owner()).unwrap().is_some());
        assert!(mismatch.is_err());
    }

    #[test]
    fn unsafe_permissions_and_symlink_slots_are_refused_without_repair() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let slot = pool.path().join("slot-00000000");
        std::fs::set_permissions(&slot, std::fs::Permissions::from_mode(0o666)).unwrap();
        assert!(pool.try_acquire(owner()).is_err());
        assert_eq!(std::fs::metadata(&slot).unwrap().permissions().mode() & 0o777, 0o666);
        std::fs::remove_file(&slot).unwrap();
        let victim = dir.path().join("victim");
        private_file(&victim, b"keep this");
        symlink(&victim, &slot).unwrap();
        assert!(pool.try_acquire(owner()).is_err());
        assert_eq!(std::fs::read(&victim).unwrap(), b"keep this");
    }

    #[test]
    fn hardlinked_slot_cannot_be_truncated_by_claiming() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let slot = pool.path().join("slot-00000000");
        let alias = dir.path().join("alias");
        std::fs::hard_link(&slot, &alias).unwrap();
        assert!(pool.try_acquire(owner()).is_err());
        assert_eq!(std::fs::metadata(&alias).unwrap().len(), 0);
    }

    #[test]
    fn replaced_or_made_public_pool_is_refused() {
        let _fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        std::fs::set_permissions(pool.path(), std::fs::Permissions::from_mode(0o755)).unwrap();
        assert!(pool.snapshot().is_err());
        std::fs::set_permissions(pool.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
        std::fs::rename(pool.path(), dir.path().join("former-pool")).unwrap();
        private_dir(pool.path());
        assert!(pool.try_acquire(owner()).is_err());
    }

    const MODE: &str = "TRUST_BUILD_CPU_TEST_MODE";
    const ROOT: &str = "TRUST_BUILD_CPU_TEST_ROOT";
    const FD: &str = "TRUST_BUILD_CPU_TEST_FD";
    const HELD: &str = "TRUST_BUILD_CPU_TEST_HELD";

    #[test]
    fn subprocess_holder() {
        let _fixture = kernel_fixture();
        let Ok(mode) = std::env::var(MODE) else { return };
        let _kept;
        let _lease;
        if mode == "inherit" {
            let fd = std::env::var(FD).unwrap().parse::<i32>().unwrap();
            // SAFETY: this child fixture owns the sole startup descriptor
            // deliberately inherited by its parent. No other Rust owner exists.
            _kept = Some(unsafe { std::fs::File::from_raw_fd(fd) });
            _lease = None;
        } else {
            let pool =
                Pool::open_in(std::path::Path::new(&std::env::var_os(ROOT).unwrap()), width(1))
                    .unwrap();
            _lease = Some(pool.try_acquire(Owner::current(None)).unwrap().unwrap());
            _kept = None;
        }
        println!("\n{HELD}");
        std::io::stdout().flush().unwrap();
        let mut byte = [0];
        let _ = std::io::stdin().read(&mut byte);
    }

    struct Running(Child);
    impl Drop for Running {
        fn drop(&mut self) {
            if self.0.try_wait().ok().flatten().is_none() {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
    }

    fn start(
        _fixture: &KernelFixture,
        mode: &str,
        root: &std::path::Path,
        inherited: Option<std::fs::File>,
    ) -> Running {
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", "tests::unix::subprocess_holder", "--nocapture"])
            .env(MODE, mode)
            .env(ROOT, root)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        if let Some(file) = inherited {
            // The native stdio handoff passes this one File through std's own
            // spawn, so no unsafe pre_exec hook has to clear its close-on-exec
            // flag. Neither path keeps other descriptors out of the child
            // until its exec: posix_spawn copies them too, on macOS even with
            // POSIX_SPAWN_CLOEXEC_DEFAULT. The caller's kernel fixture, held
            // until the child is reaped, is what keeps other tests' leases
            // out of that copy. This fixture never writes stderr; stdout
            // proves that it started.
            command.env(FD, "2").stderr(Stdio::from(file));
        }
        let mut child = Running(command.spawn().unwrap());
        let output = child.0.stdout.take().unwrap();
        let (send, receive) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let mut notified = false;
            for line in std::io::BufReader::new(output).lines() {
                if !notified && line.as_deref().is_ok_and(|line| line == HELD) {
                    let _ = send.send(());
                    notified = true;
                }
            }
        });
        receive
            .recv_timeout(Duration::from_secs(60))
            .expect("child must prove that it holds the lease");
        child
    }

    fn wait(child: &mut Running) -> std::process::ExitStatus {
        let end = Instant::now() + Duration::from_secs(60);
        loop {
            if let Some(status) = child.0.try_wait().unwrap() {
                return status;
            }
            assert!(Instant::now() < end, "child did not end within its hang detector");
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    #[test]
    fn owner_death_releases_capacity_without_stale_record_cleanup() {
        let fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let mut child = start(&fixture, "acquire", dir.path(), None);
        assert!(pool.try_acquire(owner()).unwrap().is_none());
        child.0.kill().unwrap();
        assert!(!wait(&mut child).success());
        assert_eq!(pool.snapshot().unwrap(), [SlotState::Available { slot: 0 }]);
        assert!(pool.try_acquire(owner()).unwrap().is_some());
    }

    #[test]
    fn inherited_descriptor_outlives_parent_lease_and_releases_on_child_exit() {
        let fixture = kernel_fixture();
        let dir = private_tempdir();
        let pool = Pool::open_in(dir.path(), width(1)).unwrap();
        let lease = pool.try_acquire(owner()).unwrap().unwrap();
        let mut child =
            start(&fixture, "inherit", dir.path(), Some(lease.try_clone().unwrap().into_file()));
        drop(lease);
        assert!(pool.try_acquire(owner()).unwrap().is_none());
        child.0.stdin.as_mut().unwrap().write_all(b"x").unwrap();
        assert!(wait(&mut child).success());
        assert!(pool.try_acquire(owner()).unwrap().is_some());
    }

    /// Fixture-heavy modules that the umask test re-runs, each under the cfg
    /// that compiles it, so that every one is re-run whenever it exists.
    const UMASK_RERUN: &[&str] = &[
        "native_domain::tests::",
        "retained_tests::",
        "retained::candidate_tests::",
        "external_debt::tests::",
        "legacy_retirement::tests::",
        "fence::tests::",
        "unix::initialization_tests::",
        "unix::claim_tests::",
        "tests::unix::",
        "admission_tests::",
        #[cfg(feature = "observations")]
        "monitor::tests::",
        #[cfg(feature = "observations")]
        "external::tests::",
        #[cfg(feature = "observations")]
        "host_policy::tests::",
        #[cfg(feature = "jobserver")]
        "worker::tests::",
        #[cfg(all(any(target_os = "linux", target_os = "macos"), feature = "member"))]
        "member::tests::",
        #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
        "native_observation::tests::",
        #[cfg(feature = "native-host")]
        "unix::workload_original_tests::",
    ];

    #[test]
    fn fixtures_stay_private_under_a_group_writable_umask() {
        const TEST: &str = "tests::unix::fixtures_stay_private_under_a_group_writable_umask";
        const RERUN: &str = "TRUST_BUILD_CPU_UMASK_RERUN";
        if std::env::var_os(RERUN).is_some() {
            return; // A re-run never starts another.
        }
        // The umask is process-wide, so the child's shell sets it before its
        // exec and this process keeps its own. The child holds a copy of every
        // descriptor of this process, other tests' leases included, until its
        // exec.
        let fixture = kernel_fixture();
        let output = Command::new("/bin/sh")
            .args(["-c", "umask 002 && umask && exec \"$0\" \"$@\""])
            .arg(std::env::current_exe().unwrap())
            .args(UMASK_RERUN)
            .args(["--skip", TEST])
            .env(RERUN, "1")
            .stdin(Stdio::null())
            .output()
            .unwrap();
        drop(fixture);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let report = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(stdout.lines().next(), Some("0002"), "the re-run had another umask:\n{report}");
        assert!(output.status.success(), "fixtures failed under umask 002:\n{report}");
        for module in UMASK_RERUN {
            let prefix = format!("test {module}");
            assert!(
                stdout.lines().any(|line| line.starts_with(&prefix) && line.ends_with(" ok")),
                "no {module} test passed under umask 002:\n{report}"
            );
        }
    }
}
