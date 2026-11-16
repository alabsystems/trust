// Trust: the seed Cargo's named jobserver (BOOTSTRAP-JOBSERVER-PROBE-1): its
// mode, its token count, its placement and its lifetime.

use std::os::unix::fs::{FileTypeExt as _, MetadataExt as _, PermissionsExt as _};
use std::path::Path;
use std::process::{Command, Output};

use jobserver_utils::Jobserver;

use super::{DIRECTORY_PREFIX, FIFO_NAME, SeedJobserver, is_live};

fn entries(directory: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
    names.sort();
    names
}

fn mkfifo(path: &Path) {
    let name = std::ffi::CString::new(path.to_str().unwrap()).unwrap();
    // SAFETY: a new FIFO in a test's private directory.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0, "{}", path.display());
}

// Run one test of this module alone in a child of this binary, with `role`
// set: for what is process-wide (exit handlers, the umask).
fn alone(name: &str, role: &str, value: &str, parent: &Path) -> Output {
    crate::test_entry::synthetic_observer(Command::new(std::env::current_exe().unwrap()))
        .args(["--exact", &format!("utils::seed_jobserver::tests::{name}"), "--nocapture"])
        .env(role, value)
        .env("TRUST_BOOTSTRAP_SEED_JOBSERVER_PARENT", parent)
        .output()
        .unwrap()
}

#[test]
fn a_private_mode_0600_fifo_holds_jobs_minus_one_tokens() {
    let parent = tempfile::tempdir().unwrap();
    let server = SeedJobserver::create(parent.path(), 4).unwrap();

    assert_eq!(server.directory.parent(), Some(parent.path()));
    let directory_name = server.directory.file_name().unwrap().to_str().unwrap();
    assert!(directory_name.starts_with(DIRECTORY_PREFIX), "{directory_name}");
    let directory = std::fs::symlink_metadata(&server.directory).unwrap();
    assert!(directory.is_dir());
    assert_eq!(directory.permissions().mode() & 0o7777, 0o700, "directory is not private");

    assert_eq!(server.path, server.directory.join(FIFO_NAME));
    let fifo = std::fs::symlink_metadata(&server.path).unwrap();
    assert!(fifo.file_type().is_fifo(), "{:?}", fifo.file_type());
    assert_eq!(fifo.permissions().mode() & 0o7777, 0o600);
    // SAFETY: getuid has no preconditions.
    assert_eq!(fifo.uid(), unsafe { libc::getuid() });

    // Each client holds one implicit token, so -j4 is three in the FIFO.
    assert_eq!(server.server.client().available().unwrap(), 3);
    assert_eq!(
        server.makeflags(),
        format!("-j4 --jobserver-auth=fifo:{}", server.path.to_str().unwrap())
    );
    assert!(is_live(&server.directory));
}

#[test]
fn one_job_puts_no_token_in_the_fifo() {
    let parent = tempfile::tempdir().unwrap();
    let server = SeedJobserver::create(parent.path(), 1).unwrap();
    assert_eq!(server.server.client().available().unwrap(), 0);
    assert!(server.makeflags().starts_with("-j1 --jobserver-auth=fifo:"));
}

#[test]
fn tokens_survive_clients_that_come_and_go() {
    let parent = tempfile::tempdir().unwrap();
    let server = SeedJobserver::create(parent.path(), 3).unwrap();
    for _ in 0..2 {
        // A client opens the FIFO by its name, as Cargo, a build script or the
        // shim does, takes both tokens and gives them back, then closes it.
        let client = Jobserver::from_fifo(&server.path).unwrap();
        let first = client.client().acquire().unwrap();
        let second = client.client().acquire().unwrap();
        assert_eq!(server.server.client().available().unwrap(), 0);
        drop((first, second));
        drop(client);
        // A FIFO's bytes are discarded when its last descriptor closes. The
        // owner keeps it open, so the tokens are still there for the next run.
        assert_eq!(server.server.client().available().unwrap(), 2);
    }
}

#[test]
fn drop_removes_the_fifo_and_its_directory() {
    let parent = tempfile::tempdir().unwrap();
    let server = SeedJobserver::create(parent.path(), 2).unwrap();
    let (directory, path) = (server.directory.clone(), server.path.clone());
    assert!(path.exists());
    assert!(is_live(&directory));
    drop(server);
    assert!(!path.exists());
    assert!(!directory.exists());
    assert!(!is_live(&directory), "a dropped server is still registered for removal at exit");
    assert!(entries(parent.path()).is_empty());
}

#[test]
fn each_build_gets_its_own_server_for_its_own_job_count() {
    let parent = tempfile::tempdir().unwrap();
    let three = SeedJobserver::for_build(parent.path(), 3, false).unwrap();
    let five = SeedJobserver::for_build(parent.path(), 5, false).unwrap();
    assert_ne!(three.path, five.path);
    assert_eq!(three.server.client().available().unwrap(), 2);
    assert_eq!(five.server.client().available().unwrap(), 4);
    assert!(three.makeflags().starts_with("-j3 "));
    assert!(five.makeflags().starts_with("-j5 "));
    assert_eq!(entries(parent.path()).len(), 2);
}

#[test]
fn a_refused_path_leaves_nothing_behind() {
    let relative = SeedJobserver::create(Path::new("relative/tmp"), 2).err().unwrap();
    assert_eq!(relative.kind(), std::io::ErrorKind::InvalidInput);
    assert!(!Path::new("relative").exists());

    // GNU flags are split at whitespace, so such a path cannot be advertised.
    let root = tempfile::tempdir().unwrap();
    let spaced = root.path().join("build dir").join("tmp");
    let error = SeedJobserver::create(&spaced, 2).err().unwrap();
    assert!(error.to_string().contains("whitespace"), "{error}");
    assert!(!root.path().join("build dir").exists(), "a refused path was created");
}

#[test]
fn a_build_directory_gnu_flags_cannot_carry_falls_back_to_the_system_temporary_directory() {
    // Another Bootstrap's server in the shared directory, between its mkfifo
    // and its open: nobody holds it yet. The build lock does not cover this
    // directory, so a fallback never removes anything there.
    let other = tempfile::Builder::new().prefix(DIRECTORY_PREFIX).tempdir().unwrap();
    mkfifo(&other.path().join(FIFO_NAME));
    let root = tempfile::tempdir().unwrap();
    let spaced = root.path().join("build dir").join("tmp");
    let server = SeedJobserver::for_build(&spaced, 3, true).unwrap();
    assert!(!spaced.exists(), "{}", spaced.display());
    assert_eq!(server.directory.parent(), Some(std::env::temp_dir().as_path()));
    assert!(std::fs::symlink_metadata(&server.path).unwrap().file_type().is_fifo());
    assert_eq!(server.server.client().available().unwrap(), 2);
    assert!(other.path().join(FIFO_NAME).exists(), "a fallback removed another's server");
}

// Only the placement is chosen before creating anything; a failure under the
// build directory stops instead of moving the server to another directory.
#[test]
fn a_failure_under_an_advertisable_build_directory_stops() {
    let root = tempfile::tempdir().unwrap();
    // `tmp` is a file, so no directory can be made under it.
    let parent = root.path().join("tmp");
    std::fs::write(&parent, b"not a directory").unwrap();
    let error = SeedJobserver::for_build(&parent, 3, false).err().expect("the failure stopped");
    assert_ne!(error.kind(), std::io::ErrorKind::InvalidInput, "{error}");
    assert_eq!(entries(root.path()), ["tmp"]);
    // An invalid-input failure that is not about GNU flags stops too: GNU flags
    // could carry this path, but no directory can be named by it.
    let unnamable = root.path().join("a\0b");
    let error = SeedJobserver::for_build(&unnamable, 3, false).err().expect("the failure stopped");
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput, "{error}");
}

// A server a killed Bootstrap left behind: its directory and FIFO, open nowhere.
#[test]
fn a_build_that_holds_the_lock_removes_only_servers_nobody_holds() {
    let parent = tempfile::tempdir().unwrap();
    let dead = parent.path().join(format!("{DIRECTORY_PREFIX}dead"));
    std::fs::create_dir(&dead).unwrap();
    mkfifo(&dead.join(FIFO_NAME));
    let emptied = parent.path().join(format!("{DIRECTORY_PREFIX}emptied"));
    std::fs::create_dir(&emptied).unwrap();
    // A pool some process still holds: a Bootstrap that is running, or a Cargo
    // that outlived a killed one.
    let held = parent.path().join(format!("{DIRECTORY_PREFIX}held"));
    std::fs::create_dir(&held).unwrap();
    mkfifo(&held.join(FIFO_NAME));
    let holder = Jobserver::from_fifo(&held.join(FIFO_NAME)).unwrap();
    // Not a FIFO, or more than one: not this module's to judge.
    let regular = parent.path().join(format!("{DIRECTORY_PREFIX}regular"));
    std::fs::create_dir(&regular).unwrap();
    std::fs::write(regular.join(FIFO_NAME), b"").unwrap();
    let crowded = parent.path().join(format!("{DIRECTORY_PREFIX}crowded"));
    std::fs::create_dir(&crowded).unwrap();
    mkfifo(&crowded.join(FIFO_NAME));
    std::fs::write(crowded.join("other"), b"").unwrap();
    let unrelated = parent.path().join("unrelated");
    std::fs::create_dir(&unrelated).unwrap();
    mkfifo(&unrelated.join(FIFO_NAME));
    // A live server of this process.
    let live = SeedJobserver::create(parent.path(), 2).unwrap();

    // Without the lock (a dry run, or --bypass-bootstrap-lock) nothing is removed.
    let unlocked = SeedJobserver::for_build(parent.path(), 2, false).unwrap();
    assert!(dead.exists() && emptied.exists());
    drop(unlocked);

    let server = SeedJobserver::for_build(parent.path(), 2, true).unwrap();
    assert!(!dead.exists(), "a server nobody holds was kept");
    assert!(!emptied.exists());
    for kept in [&held, &regular, &crowded, &unrelated, &live.directory, &server.directory] {
        assert!(kept.exists(), "{} was removed", kept.display());
    }
    assert!(held.join(FIFO_NAME).exists());
    assert!(crowded.join(FIFO_NAME).exists());
    assert_eq!(holder.client().available().unwrap(), 0);
    assert_eq!(server.server.client().available().unwrap(), 1);
    assert_eq!(live.server.client().available().unwrap(), 1);
}

// mkdir and mkfifo modes pass through the umask; an inherited umask that clears
// owner bits still yields a usable private directory and FIFO. The umask is
// process-wide, so this runs alone in a child.
#[test]
fn an_owner_clearing_umask_still_yields_exact_modes() {
    const ROLE: &str = "TRUST_BOOTSTRAP_SEED_JOBSERVER_UMASK";
    let name = "an_owner_clearing_umask_still_yields_exact_modes";
    if std::env::var_os(ROLE).is_some() {
        let parent = std::env::var_os("TRUST_BOOTSTRAP_SEED_JOBSERVER_PARENT").unwrap();
        // SAFETY: umask has no preconditions; this child runs only this test.
        unsafe { libc::umask(0o277) };
        let server = SeedJobserver::create(Path::new(&parent), 3).unwrap();
        let directory = std::fs::symlink_metadata(&server.directory).unwrap();
        assert_eq!(directory.permissions().mode() & 0o7777, 0o700);
        let fifo = std::fs::symlink_metadata(&server.path).unwrap();
        assert_eq!(fifo.permissions().mode() & 0o7777, 0o600);
        assert_eq!(server.server.client().available().unwrap(), 2);
        println!("seed-jobserver-umask-checked");
        return;
    }
    let parent = tempfile::tempdir().unwrap();
    let output = alone(name, ROLE, "1", parent.path());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "{output:?}");
    assert!(stdout.contains("seed-jobserver-umask-checked"), "{stdout}");
    assert!(entries(parent.path()).is_empty(), "{:?}", entries(parent.path()));
}

// A server still live when Bootstrap exits without dropping it is removed by
// the exit handler, whether the process succeeds (exit 0, or a return from
// main) or fails (`exit!`, exit 1).
#[test]
fn a_live_server_is_removed_when_the_process_exits() {
    const ROLE: &str = "TRUST_BOOTSTRAP_SEED_JOBSERVER_EXIT";
    let name = "a_live_server_is_removed_when_the_process_exits";
    if let Some(code) = std::env::var_os(ROLE) {
        let parent = std::env::var_os("TRUST_BOOTSTRAP_SEED_JOBSERVER_PARENT").unwrap();
        let server = SeedJobserver::for_build(Path::new(&parent), 3, false).unwrap();
        assert!(server.path.exists());
        println!("seed-jobserver-path={}", server.path.display());
        std::process::exit(code.to_str().unwrap().parse().unwrap());
    }
    for code in [0, 1] {
        let parent = tempfile::tempdir().unwrap();
        let output = alone(name, ROLE, &code.to_string(), parent.path());
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        let path = stdout
            .lines()
            .find_map(|line| line.strip_prefix("seed-jobserver-path="))
            .unwrap_or_else(|| panic!("the child made no server: {stdout}"));
        assert!(Path::new(path).starts_with(parent.path()), "{path}");
        assert!(!Path::new(path).exists(), "exit {code} left {path}");
        assert!(entries(parent.path()).is_empty(), "exit {code} left {:?}", entries(parent.path()));
    }
}
