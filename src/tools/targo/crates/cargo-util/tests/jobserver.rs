//! Trust: real two-hop jobserver custody through ProcessBuilder and SP-1 std.
#![cfg(unix)]

use cargo_util::ProcessBuilder;
use jobserver_utils::Jobserver;
use std::env;
use std::ffi::OsStr;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::sync::Arc;

const STAGE: &str = "CARGO_UTIL_JOBSERVER_TEST_STAGE";
const CASE: &str = "CARGO_UTIL_JOBSERVER_TEST_CASE";

fn identity(fd: RawFd) -> Option<String> {
    let mut info = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe { libc::fstat(fd, info.as_mut_ptr()) } != 0 {
        return None;
    }
    let info = unsafe { info.assume_init() };
    Some(format!(
        "{}:{}:{}",
        info.st_dev,
        info.st_ino,
        info.st_mode & libc::S_IFMT
    ))
}

fn transport(flags: &str) -> &str {
    flags
        .split_whitespace()
        .find_map(|value| value.strip_prefix("--jobserver-auth="))
        .or_else(|| {
            flags
                .split_whitespace()
                .find_map(|value| value.strip_prefix("--jobserver-fds="))
        })
        .expect("actual client transport")
}

fn endpoints(flags: &str) -> Option<(RawFd, RawFd)> {
    let auth = transport(flags);
    if auth.starts_with("fifo:") {
        return None;
    }
    let (read, write) = auth.split_once(',').unwrap();
    Some((read.parse().unwrap(), write.parse().unwrap()))
}

fn child() -> Command {
    let mut command = Command::new(env::current_exe().unwrap());
    command.args([
        "--exact",
        "processbuilder_jobserver_transport",
        "--nocapture",
    ]);
    command
}

fn configured_flags(server: &Jobserver) -> std::ffi::OsString {
    // The temporary Command owns a transport clone only until this helper returns.
    let mut command = Command::new("never-executed-metadata-only");
    server.configure(&mut command);
    let flags = command
        .get_envs()
        .find_map(|(key, value)| (key == "CARGO_MAKEFLAGS").then_some(value).flatten())
        .unwrap()
        .to_owned();
    flags
}

// Trust: FIONREAD on a named FIFO reports zero on Darwin even with a
// readable token. In these serialized fixture phases, measure the real pool
// with bounded nonblocking acquisitions and return every acquired token.
// Reading one beyond the expected count still detects surplus authority.
fn token_count(server: &Jobserver, expected: usize) -> usize {
    if endpoints(configured_flags(server).to_str().unwrap()).is_some() {
        return server.client().available().unwrap();
    }
    let mut tokens = Vec::new();
    for _ in 0..=expected {
        let Some(token) = server.client().try_acquire().unwrap() else { break };
        tokens.push(token);
    }
    let count = tokens.len();
    drop(tokens);
    count
}

fn observer_process(
    server: &Jobserver,
    read: String,
    write: String,
    expected_tokens: usize,
) -> ProcessBuilder {
    let mut process = ProcessBuilder::new(env::current_exe().unwrap());
    process
        .args(&["--exact", "processbuilder_jobserver_transport", "--nocapture"])
        .env(STAGE, "observer")
        .env("CARGO_UTIL_EXPECTED_READ", read)
        .env("CARGO_UTIL_EXPECTED_WRITE", write)
        .env("CARGO_UTIL_EXPECTED_TOKENS", expected_tokens.to_string())
        .inherit_jobserver(server);
    process
}

fn run_observer(mut process: ProcessBuilder, label: &str) {
    let effective = process.get_effective_envs().unwrap();
    let flags = effective.get(OsStr::new("CARGO_MAKEFLAGS")).unwrap();
    process.env("CARGO_UTIL_EXPECTED_FLAGS", flags);
    let mut command = process.build_command();
    drop(process);
    let output = command.output().unwrap();
    assert!(output.status.success(), "second hop {label}: {output:?}");
}

fn observer() {
    let flags = env::var("CARGO_MAKEFLAGS").unwrap();
    assert_eq!(flags, env::var("CARGO_UTIL_EXPECTED_FLAGS").unwrap());
    let sentinel: RawFd = env::var("CARGO_UTIL_SENTINEL_FD").unwrap().parse().unwrap();
    assert_ne!(identity(sentinel), Some(env::var("CARGO_UTIL_SENTINEL_ID").unwrap()));
    let numeric = endpoints(&flags);
    if let Some(pair) = numeric {
        // Inspect before import creates its private Client and owned transport copies.
        for fd in 3..256 {
            assert!(
                identity(fd).is_none() || fd == pair.0 || fd == pair.1,
                "unexpected descriptor {fd} survived the jobserver handoff"
            );
        }
    }
    // SAFETY: no descriptor-opening operation precedes this import. Inherited
    // numeric originals are OS handles, not Rust-owned descriptors in this child.
    let server = unsafe { Jobserver::from_env() }.unwrap().expect("advertised server");
    let expected_tokens: usize = env::var("CARGO_UTIL_EXPECTED_TOKENS").unwrap().parse().unwrap();
    assert_eq!(token_count(&server, expected_tokens), expected_tokens);
    let fifo;
    let (read, write) = if let Some(pair) = numeric {
        pair
    } else {
        fifo = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(transport(&flags).strip_prefix("fifo:").unwrap())
            .unwrap();
        (fifo.as_raw_fd(), fifo.as_raw_fd())
    };
    assert_eq!(identity(read), Some(env::var("CARGO_UTIL_EXPECTED_READ").unwrap()));
    assert_eq!(identity(write), Some(env::var("CARGO_UTIL_EXPECTED_WRITE").unwrap()));
    let mut ready = libc::pollfd { fd: read, events: libc::POLLIN, revents: 0 };
    assert_eq!(unsafe { libc::poll(&mut ready, 1, 0) }, 1);
    let mut token = [0u8];
    assert_eq!(unsafe { libc::read(read, token.as_mut_ptr().cast(), 1) }, 1);
    assert_eq!(unsafe { libc::write(write, token.as_ptr().cast(), 1) }, 1);
    assert_eq!(token_count(&server, expected_tokens), expected_tokens, "token was not returned");
}

fn inherited_originals() -> (RawFd, RawFd) {
    let pair = endpoints(&env::var("CARGO_MAKEFLAGS").unwrap()).unwrap();
    // high_pipe in the parent installs these above all ordinary owned imports.
    // No Rust value in this child owns these raw inherited originals.
    assert!(pair.0 >= 100 && pair.1 >= 100 && pair.0 != pair.1);
    pair
}

fn close_inherited_originals(pair: (RawFd, RawFd)) {
    // SAFETY: only parent-installed, raw inherited originals enter this helper.
    // Never pass server.configure()'s numbers: Jobserver owns those via RAII.
    assert_eq!(unsafe { libc::close(pair.0) }, 0);
    assert_eq!(unsafe { libc::close(pair.1) }, 0);
}

fn first_child(case: &str) {
    if matches!(case, "absent" | "malformed" | "closed" | "nonpipe") {
        // SAFETY: import is the first descriptor-opening operation in this role.
        let imported = unsafe { Jobserver::from_env() };
        if case == "absent" {
            assert!(matches!(imported, Ok(None)), "absent parent invented a server: {imported:?}");
        } else {
            assert!(imported.is_err(), "invalid parent transport accepted: {case}: {imported:?}");
        }
        return;
    }
    let stale = matches!(
        case,
        "stale-before-capture" | "nonpipe-before-capture"
            | "warm-stale-before-capture" | "warm-nonpipe-before-capture"
    );
    if stale {
        let originals = inherited_originals();
        let expected_read = identity(originals.0).unwrap();
        let expected_write = identity(originals.1).unwrap();
        let count = || (0..256).filter(|&fd| identity(fd).is_some()).count();
        let before_warm = count();
        let warm = if case.starts_with("warm-") {
            // This earlier import owns independent copies before originals go stale.
            let server = unsafe { Jobserver::from_env() }.unwrap().unwrap();
            let pair = endpoints(configured_flags(&server).to_str().unwrap()).unwrap();
            assert!(pair.0 != originals.0 && pair.0 != originals.1);
            assert!(pair.1 != originals.0 && pair.1 != originals.1);
            let process = observer_process(&server, expected_read, expected_write, 1);
            assert!(process.get_effective_envs().is_ok());
            Some((server, process))
        } else {
            None
        };
        assert_eq!(count(), before_warm + if warm.is_some() { 4 } else { 0 });
        close_inherited_originals(originals);
        let replacement;
        if case.ends_with("nonpipe-before-capture") {
            let file = std::fs::File::open(env::var("CARGO_UTIL_REGULAR_FILE").unwrap()).unwrap();
            assert_ne!(file.as_raw_fd(), originals.0);
            assert_ne!(file.as_raw_fd(), originals.1);
            // Create and immediately own replacements at the raw inherited slots.
            // They are distinct from both the warm owner's pipe and `file`.
            assert_eq!(unsafe { libc::dup2(file.as_raw_fd(), originals.0) }, originals.0);
            assert_eq!(unsafe { libc::dup2(file.as_raw_fd(), originals.1) }, originals.1);
            replacement = Some(unsafe {
                [OwnedFd::from_raw_fd(originals.0), OwnedFd::from_raw_fd(originals.1)]
            });
        } else {
            assert!(identity(originals.0).is_none() && identity(originals.1).is_none());
            replacement = None;
        }
        let before_import = count();
        // This is the actual capture boundary of the new API. An old warm
        // owner must not allow this distinct invalid import to reuse its pipe.
        assert!(unsafe { Jobserver::from_env() }.is_err(), "invalid re-import accepted: {case}");
        assert_eq!(count(), before_import, "rejected import leaked descriptors: {case}");
        if let Some((server, process)) = warm {
            assert_eq!(server.client().available().unwrap(), 1);
            drop(server);
            run_observer(process, case);
            assert_eq!(count(), before_import - 4, "warm owner cleanup leaked descriptors: {case}");
        }
        drop(replacement);
        return;
    }

    let server = if case == "new" {
        Jobserver::new(2).unwrap()
    } else {
        // SAFETY: no files or sidecars have been opened in this child role.
        unsafe { Jobserver::from_env() }.unwrap().unwrap()
    };
    let flags = configured_flags(&server);
    let fifo;
    let (read, write) = if let Some(pair) = endpoints(flags.to_str().unwrap()) {
        pair
    } else {
        fifo = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(transport(flags.to_str().unwrap()).strip_prefix("fifo:").unwrap())
            .unwrap();
        (fifo.as_raw_fd(), fifo.as_raw_fd())
    };
    let expected_tokens = if case == "new" { 2 } else { 1 };
    assert_eq!(token_count(&server, expected_tokens), expected_tokens);
    let mut process = observer_process(
        &server, identity(read).unwrap(), identity(write).unwrap(), expected_tokens,
    );
    if case == "overlay" {
        process.env("CARGO_MAKEFLAGS", "unrelated explicit overlay");
    }
    let effective = process.get_effective_envs().unwrap();
    let effective_flags = effective.get(OsStr::new("CARGO_MAKEFLAGS")).unwrap();
    assert_eq!(effective_flags, &flags, "builder overlay replaced owned authority");
    process.env("CARGO_UTIL_EXPECTED_FLAGS", effective_flags);
    if case == "clone-drop-close" {
        let originals = inherited_originals();
        assert!(read != originals.0 && read != originals.1);
        assert!(write != originals.0 && write != originals.1);
        let retained = process.clone();
        drop(process);
        drop(server);
        close_inherited_originals(originals);
        process = retained;
        assert_eq!(
            process.get_effective_envs().unwrap().get(OsStr::new("CARGO_MAKEFLAGS")),
            Some(effective_flags)
        );
    }
    let mut command = process.build_command();
    drop(process);
    let output = command.output().unwrap();
    assert!(output.status.success(), "second hop {case}: {output:?}");
    drop(command);
    if case == "clone-drop-close" {
        assert!(identity(read).is_none() && identity(write).is_none(), "last command retained pipe");
    }
}

fn high_pipe(minimum: RawFd) -> [OwnedFd; 2] {
    let mut fds = [-1; 2];
    assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
    let originals = unsafe { [OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])] };
    std::array::from_fn(|index| {
        let copy = unsafe {
            libc::fcntl(
                originals[index].as_raw_fd(),
                libc::F_DUPFD_CLOEXEC,
                minimum + index as i32,
            )
        };
        assert!(copy >= minimum);
        unsafe { OwnedFd::from_raw_fd(copy) }
    })
}

#[test]
fn processbuilder_jobserver_transport() {
    if env::var(STAGE).as_deref() == Ok("observer") {
        observer();
        return;
    }
    if env::var(STAGE).as_deref() == Ok("first-child") {
        first_child(&env::var(CASE).unwrap());
        return;
    }
    assert!(env::var(STAGE).is_err(), "unknown child stage");
    for case in [
        "inherited",
        "legacy",
        "make",
        "mflags",
        "new",
        "fifo",
        "overlay",
        "clone-drop-close",
        "stale-before-capture",
        "nonpipe-before-capture",
        "warm-stale-before-capture",
        "warm-nonpipe-before-capture",
        "absent",
        "malformed",
        "closed",
        "nonpipe",
    ] {
        let directory = tempfile::tempdir().unwrap();
        let regular = directory.path().join("regular");
        std::fs::write(&regular, "not a jobserver pipe").unwrap();
        let pipes = high_pipe(100);
        let sentinel = high_pipe(120);
        let (read, write) = (pipes[0].as_raw_fd(), pipes[1].as_raw_fd());
        assert_eq!(unsafe { libc::write(write, b"+".as_ptr().cast(), 1) }, 1);
        let sentinel_fd = sentinel[0].as_raw_fd();
        let sentinel_id = identity(sentinel_fd).unwrap();
        let owned = Arc::new([pipes, sentinel]);
        let before: Vec<_> = owned
            .iter()
            .flatten()
            .map(|fd| {
                (identity(fd.as_raw_fd()), unsafe {
                    libc::fcntl(fd.as_raw_fd(), libc::F_GETFD)
                })
            })
            .collect();
        let mut flags =
            format!("-j --jobserver-fds={read},{write} --jobserver-auth={read},{write}");
        let mut command = child();
        // Isolate synthetic parent roles, not an actual build's jobserver.
        for name in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
            command.env_remove(name);
        }
        let fifo;
        match case {
            "legacy" => flags = format!("-j --jobserver-fds={read},{write}"),
            "malformed" => flags = "-j --jobserver-auth=invalid".into(),
            "closed" => flags = "-j --jobserver-auth=9000,9001".into(),
            "nonpipe" => {
                // Give the first child a real regular FD, not an absent one.
                let file = std::fs::File::open(&regular).unwrap();
                unsafe {
                    command.pre_exec(move || {
                        if libc::dup2(file.as_raw_fd(), 140) < 0
                            || libc::dup2(file.as_raw_fd(), 141) < 0
                        {
                            return Err(std::io::Error::last_os_error());
                        }
                        Ok(())
                    });
                }
                flags = "-j --jobserver-auth=140,141".into();
            }
            "fifo" => {
                let path = directory.path().join("private.fifo");
                let raw = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
                assert_eq!(unsafe { libc::mkfifo(raw.as_ptr(), 0o600) }, 0);
                fifo = std::fs::OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(&path)
                    .unwrap();
                assert_eq!(
                    unsafe { libc::write(fifo.as_raw_fd(), b"+".as_ptr().cast(), 1) },
                    1
                );
                flags = format!("-j --jobserver-auth=fifo:{}", path.display());
            }
            _ => {}
        }
        if case != "absent" {
            command.env(
                if case == "make" {
                    "MAKEFLAGS"
                } else if case == "mflags" {
                    "MFLAGS"
                } else {
                    "CARGO_MAKEFLAGS"
                },
                flags,
            );
        }
        command
            .env(STAGE, "first-child")
            .env(CASE, case)
            .env("CARGO_UTIL_SENTINEL_FD", sentinel_fd.to_string())
            .env("CARGO_UTIL_SENTINEL_ID", sentinel_id)
            .env("CARGO_UTIL_REGULAR_FILE", regular);
        let keep = Arc::clone(&owned);
        unsafe {
            command.pre_exec(move || {
                for fd in keep.iter().flatten() {
                    let raw = fd.as_raw_fd();
                    let flags = libc::fcntl(raw, libc::F_GETFD);
                    if flags < 0 || libc::fcntl(raw, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
        let output = command.output().unwrap();
        assert!(output.status.success(), "first hop {case}: {output:?}");
        let after: Vec<_> = owned
            .iter()
            .flatten()
            .map(|fd| {
                (identity(fd.as_raw_fd()), unsafe {
                    libc::fcntl(fd.as_raw_fd(), libc::F_GETFD)
                })
            })
            .collect();
        assert_eq!(before, after, "parent custody changed: {case}");
    }
}

#[test]
fn processbuilder_jobserver_graph_custody() {
    const RESOURCE_CHILD: &str = "CARGO_UTIL_JOBSERVER_RESOURCE_CHILD";
    if env::var(RESOURCE_CHILD).as_deref() != Ok("1") {
        let output = Command::new(env::current_exe().unwrap())
            .args([
                "--exact",
                "processbuilder_jobserver_graph_custody",
                "--nocapture",
            ])
            .env(RESOURCE_CHILD, "1")
            .output()
            .unwrap();
        assert!(output.status.success(), "resource child: {output:?}");
        return;
    }
    // Restrict only this isolated child, never the test runner or other tests.
    let mut limit = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    assert_eq!(
        unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limit.as_mut_ptr()) },
        0
    );
    let mut limit = unsafe { limit.assume_init() };
    limit.rlim_cur = 64;
    assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
    let count = || {
        (0..64)
            .filter(|&fd| unsafe { libc::fcntl(fd, libc::F_GETFD) } >= 0)
            .count()
    };
    let sentinel = std::os::unix::net::UnixStream::pair().unwrap();
    let before = count();
    let server = Jobserver::new(1).unwrap();
    // Two Client pipe descriptors plus two separately owned transport copies.
    let constructed = count();
    assert_eq!(constructed, before + 4, "unexpected Jobserver construction cost");
    let flags = configured_flags(&server);
    let (read, write) = endpoints(flags.to_str().unwrap()).unwrap();
    let mut builders = Vec::new();
    let mut shared_flags = None;
    for _ in 0..128 {
        let mut process = observer_process(&server, identity(read).unwrap(), identity(write).unwrap(), 1);
        process
            .env("CARGO_UTIL_SENTINEL_FD", sentinel.0.as_raw_fd().to_string())
            .env("CARGO_UTIL_SENTINEL_ID", identity(sentinel.0.as_raw_fd()).unwrap());
        let effective = process.get_effective_envs().unwrap();
        let flags = effective.get(OsStr::new("CARGO_MAKEFLAGS")).unwrap().clone();
        if let Some(shared) = &shared_flags {
            assert_eq!(&flags, shared);
        } else {
            shared_flags = Some(flags.clone());
        }
        process.env("CARGO_UTIL_EXPECTED_FLAGS", flags);
        builders.push(process);
    }
    assert_eq!(count(), constructed, "transport grew with the queued graph");
    assert_eq!(server.client().available().unwrap(), 1);
    let mut command = builders[0].build_command();
    let output = command.output().unwrap();
    assert!(output.status.success(), "all-retained spawn: {output:?}");
    drop(command);
    assert_eq!(count(), constructed);
    assert_eq!(server.client().available().unwrap(), 1, "child lost or minted a token");

    // An unrelated live server keeps its own pipe and token budget.
    let other = Jobserver::new(1).unwrap();
    assert_eq!(count(), constructed + 4);
    let mut other_builder = ProcessBuilder::new("never-executed-distinct-client");
    other_builder.inherit_jobserver(&other);
    let other_env = other_builder.get_effective_envs().unwrap();
    assert_ne!(other_env.get(OsStr::new("CARGO_MAKEFLAGS")), shared_flags.as_ref());
    let (other_read, other_write) = endpoints(
        other_env.get(OsStr::new("CARGO_MAKEFLAGS")).unwrap().to_str().unwrap(),
    ).unwrap();
    assert_ne!(identity(other_read), identity(read));
    assert_ne!(identity(other_write), identity(write));
    assert_eq!(other.client().available().unwrap(), 1);
    assert_eq!(count(), constructed + 4, "a second builder duplicated its server transport");
    drop(other_builder);
    drop(other);
    assert_eq!(count(), constructed, "unrelated server descriptors leaked");
    assert!(identity(other_read).is_none() && identity(other_write).is_none());

    // A final command keeps only the explicit handoff pair after every
    // Jobserver/ProcessBuilder owner drops; its last drop closes that pair too.
    let mut last_command = builders[0].build_command();
    drop(server);
    assert_eq!(count(), constructed, "builders did not retain their imported owner");
    drop(builders);
    assert_eq!(count(), before + 2, "last command should retain only the exact handoff pair");
    let output = last_command.output().unwrap();
    assert!(output.status.success(), "last-command custody: {output:?}");
    assert_eq!(count(), before + 2);
    drop(last_command);
    assert_eq!(count(), before, "final transport cleanup leaked descriptors");
    assert!(identity(read).is_none() && identity(write).is_none());
}
