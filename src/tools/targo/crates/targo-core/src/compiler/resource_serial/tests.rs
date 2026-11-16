use std::io::{Read, Seek, SeekFrom, Write};
use std::os::fd::{AsRawFd, BorrowedFd};
use std::process::Command;

const WORKER: &str = "TARGO_SERIAL_MAKE_WORKER";

// Trust: libtest omits the crate prefix, but retains the complete module path.
// A shortened --exact filter succeeds after selecting no worker at all.
fn test_name() -> String {
    let (_, module) = module_path!().split_once("::").unwrap();
    format!("{module}::system_make_preserves_one_implicit_worker")
}

#[expect(
    clippy::disallowed_methods,
    reason = "the GNU make child must observe the actual inherited worker protocol and jobserver state, without a GlobalContext"
)]
fn worker() {
    // SAFETY: this fixture imports immediately on child startup, before opening
    // unrelated files. Parent GNU make explicitly inherits the checked pair.
    let server = unsafe { jobserver::Client::from_env_ext(true) }
        .client
        .unwrap();
    assert!(
        server.available().unwrap() == 0,
        "no extra credit may be minted"
    );
    let path = std::env::var_os("TARGO_SERIAL_MAKE_STATE").unwrap();
    let mut state = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(path)
        .unwrap();
    update(&mut state, true);
    std::thread::sleep(std::time::Duration::from_millis(50));
    update(&mut state, false);
}

fn update(state: &mut std::fs::File, entering: bool) {
    // SAFETY: state is an owned regular fixture file; flock changes its lock.
    assert_eq!(unsafe { libc::flock(state.as_raw_fd(), libc::LOCK_EX) }, 0);
    let mut bytes = String::new();
    state.seek(SeekFrom::Start(0)).unwrap();
    state.read_to_string(&mut bytes).unwrap();
    let values: Vec<u32> = bytes
        .split_whitespace()
        .map(|n| n.parse().unwrap())
        .collect();
    let active = if entering {
        values[0] + 1
    } else {
        values[0] - 1
    };
    let peak = values[1].max(active);
    let done = values[2] + u32::from(!entering);
    state.seek(SeekFrom::Start(0)).unwrap();
    state.set_len(0).unwrap();
    write!(state, "{active} {peak} {done}").unwrap();
    state.flush().unwrap();
    // SAFETY: release only this fixture file's lock.
    assert_eq!(unsafe { libc::flock(state.as_raw_fd(), libc::LOCK_UN) }, 0);
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the nested GNU make fixture distinguishes its actual inherited worker tag, without a GlobalContext"
)]
fn system_make_preserves_one_implicit_worker() {
    if std::env::var_os(WORKER).is_some() {
        worker();
        return;
    }
    let version = Command::new("/usr/bin/make")
        .arg("--version")
        .output()
        .unwrap();
    assert!(version.status.success());
    let version = String::from_utf8(version.stdout).unwrap();
    assert!(
        version.contains("GNU Make"),
        "this fixture requires actual GNU make: {version}"
    );
    let dir = tempfile::tempdir().unwrap();
    let state = dir.path().join("state");
    std::fs::write(&state, "0 0 0").unwrap();
    let executable = std::env::current_exe().unwrap();
    let recipe = format!(
        ".PHONY: all a b c d\nall: a b c d\na b c d:\n\t+{}=1 '{}' --exact {} --nocapture\n",
        WORKER,
        executable.display(),
        test_name(),
    );
    let makefile = dir.path().join("Makefile");
    std::fs::write(&makefile, recipe).unwrap();
    let server = super::jobserver().unwrap();
    assert_eq!(server.client().available().unwrap(), 0);
    let mut command = Command::new("/usr/bin/make");
    command
        .arg("--no-print-directory")
        .arg("-f")
        .arg(&makefile)
        .env("TARGO_SERIAL_MAKE_STATE", &state);
    server.configure_make(&mut command);
    let flags = command
        .get_envs()
        .find_map(|(key, value)| (key == "MAKEFLAGS").then_some(value).flatten())
        .unwrap()
        .to_str()
        .unwrap();
    assert!(!flags.contains("fifo:"));
    let numbers = flags
        .split_whitespace()
        .find_map(|part| part.strip_prefix("--jobserver-fds="))
        .unwrap();
    let numbers: Vec<i32> = numbers.split(',').map(|n| n.parse().unwrap()).collect();
    assert_eq!(numbers.len(), 2);
    drop(server); // Configured Command alone must keep these advertised slots live.
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "make failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!String::from_utf8_lossy(&output.stderr).contains("jobserver unavailable"));
    assert_eq!(std::fs::read_to_string(&state).unwrap(), "0 1 4");
    // SAFETY: our still-live configured Command owns exactly these advertised
    // descriptors. from_pipe duplicates them; no advertised foreign FD is adopted.
    let observer = unsafe {
        jobserver::Client::from_pipe(
            BorrowedFd::borrow_raw(numbers[0]),
            BorrowedFd::borrow_raw(numbers[1]),
        )
    }
    .unwrap();
    assert!(
        observer.available().unwrap() == 0,
        "make must return no extra token"
    );
    drop(observer);
    drop(command);
    for number in numbers {
        // SAFETY: F_GETFD only observes a descriptor number after our owner closes.
        assert_eq!(unsafe { libc::fcntl(number, libc::F_GETFD) }, -1);
        assert_eq!(
            std::io::Error::last_os_error().raw_os_error(),
            Some(libc::EBADF)
        );
    }
    println!("qualified {}", version.lines().next().unwrap());
}
