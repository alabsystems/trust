// Test-only entry in the current native libtest image. Enter before libtest so
// the production CLI's stdout remains exactly its token/protocol response.
use std::ffi::OsString;
use std::path::Path;
use std::process::Command;

const ENTRY: &str = "--trust-native-manager-test-actor-v1";

#[used]
#[cfg_attr(target_vendor = "apple", unsafe(link_section = "__DATA,__mod_init_func"))]
#[cfg_attr(not(target_vendor = "apple"), unsafe(link_section = ".init_array"))]
static ENTRY_POINT: extern "C" fn() = enter;

extern "C" fn enter() {
    let mut args = std::env::args_os();
    let _ = args.next();
    if args.next().as_deref() != Some(std::ffi::OsStr::new(ENTRY)) {
        return;
    }
    let code = std::panic::catch_unwind(|| {
        let mode = args.next().expect("native actor mode");
        let root = args.next().expect("native actor root");
        let root = Path::new(&root);
        match mode.to_str().expect("native actor UTF-8 mode") {
            "cli" => super::manager_run(&args.collect::<Vec<OsString>>()),
            "guard-helper" => {
                use std::os::fd::{FromRawFd, OwnedFd};
                // stdin is an explicitly mapped duplicate of the controller's
                // original guard description; ambient FD inheritance is unused.
                let fd = unsafe { libc::fcntl(0, libc::F_DUPFD_CLOEXEC, 3) };
                assert!(fd >= 3);
                let held = unsafe { OwnedFd::from_raw_fd(fd) };
                super::lock_inherited(root, fd).unwrap();
                drop(held);
                0
            }
            "guard-controller" => {
                use std::io::{Read, Write};
                let held = std::fs::OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(root.join(".trust-build-lock.guard"))
                    .unwrap();
                let mut child = actor(root, "guard-helper");
                let result = child
                    .stdin(std::process::Stdio::from(held.try_clone().unwrap()))
                    .output()
                    .unwrap();
                assert!(result.status.success(), "{result:?}");
                std::fs::write(root.join("helper-exited"), b"original helper reaped").unwrap();
                std::io::stdout().flush().unwrap();
                let mut byte = [0];
                assert_eq!(std::io::stdin().read(&mut byte).unwrap(), 1);
                drop(held);
                0
            }
            "descriptors" => descriptors(root, args.next().unwrap() == "all"),
            _ => panic!("unknown native actor mode"),
        }
    })
    .unwrap_or(101);
    std::process::exit(i32::from(code));
}

pub(super) fn actor(root: &Path, mode: &str) -> Command {
    let mut child = Command::new(std::env::current_exe().unwrap());
    child.args([std::ffi::OsStr::new(ENTRY), std::ffi::OsStr::new(mode), root.as_os_str()]);
    child
}

#[cfg(not(feature = "native-cli-tests"))]
pub(super) fn command(root: &Path, args: &[&str]) -> Command {
    let mut child = actor(root, "cli");
    child
        .args(args)
        .env("TRUST_REPO", root)
        .env_remove("TRUST_BUILD_LOCK_TOKEN")
        .env_remove("TRUST_BUILD_LOCK_BREAK")
        .env_remove("TRUST_BUILD_LOCK_WAIT");
    child
}

fn descriptors(root: &Path, all: bool) -> u8 {
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
    use std::os::unix::fs::MetadataExt;
    let first = if all { 3 } else { 8 };
    let path = root.join("resources");
    let original =
        std::fs::OpenOptions::new().create_new(true).read(true).append(true).open(&path).unwrap();
    // Keep the source outside the occupied range before installing actual
    // descriptions at 3..9 in this isolated, single-threaded native actor.
    let high = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 20) };
    assert!(high >= 20);
    let high = unsafe { OwnedFd::from_raw_fd(high) };
    drop(original);
    let mut before = Vec::new();
    for fd in first..=9 {
        assert_eq!(unsafe { libc::dup2(high.as_raw_fd(), fd) }, fd);
        let duplicate = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 20) };
        assert!(duplicate >= 20);
        let file = unsafe { std::fs::File::from_raw_fd(duplicate) };
        before.push((
            fd,
            file.metadata().unwrap(),
            unsafe { libc::fcntl(fd, libc::F_GETFL) },
            unsafe { libc::fcntl(fd, libc::F_GETFD) },
            unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) },
        ));
    }
    let pid = std::process::id().to_string();
    let args =
        ["acquire", "--kind", "build", "--purpose", "native descriptor custody", "--pid", &pid];
    let args = args.map(OsString::from);
    assert_eq!(super::manager_run(&args), 0);
    for (fd, metadata, flags, fd_flags, cursor) in before {
        let dup = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 20) };
        assert!(dup >= 20);
        let file = unsafe { std::fs::File::from_raw_fd(dup) };
        let now = file.metadata().unwrap();
        assert_eq!((now.dev(), now.ino()), (metadata.dev(), metadata.ino()));
        assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFL) }, flags);
        assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFD) }, fd_flags);
        assert_eq!(unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) }, cursor);
    }
    for fd in first..=9 {
        assert_eq!(unsafe { libc::write(fd, b"x".as_ptr().cast(), 1) }, 1);
    }
    assert_eq!(std::fs::read(path).unwrap(), vec![b'x'; (10 - first) as usize]);
    0
}
