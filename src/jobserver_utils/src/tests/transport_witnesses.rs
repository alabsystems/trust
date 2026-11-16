use std::ffi::CString;
use std::os::unix::ffi::OsStrExt as _;
use std::path::Path;

use super::Jobserver;

// Darwin exposes kernel bookkeeping through F_GETFL: FMARK/FDEFER are
// changed by Unix-rights GC and FWASWRITTEN by legitimate token writes.
// Keep every other bit, including ALL access/configuration flags. In
// particular O_NONBLOCK is 0x4 on Darwin, not the observed GC mark 0x1000.
// XNU bsd/sys/fcntl.h and bsd/kern/kern_descrip.c document these encodings.
fn configuration_flags(flags: libc::c_int) -> libc::c_int {
    assert!(flags >= 0);
    #[cfg(target_os = "macos")]
    {
        flags & !(0x1000 | 0x2000 | 0x10000)
    }
    #[cfg(not(target_os = "macos"))]
    {
        flags
    }
}

fn fifo(path: &Path) {
    let name = CString::new(path.as_os_str().as_bytes()).unwrap();
    // SAFETY: create a new FIFO only inside this test's owned private directory.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
}

#[test]
fn named_transport_replacement_is_refused_without_changing_either_inventory() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("credits");
    fifo(&path);
    let original = jobserver::Client::from_fifo(&path).unwrap();
    original.release_raw().unwrap();
    std::fs::rename(&path, directory.path().join("original-credits")).unwrap();
    fifo(&path);
    let replacement = jobserver::Client::from_fifo(&path).unwrap();
    replacement.release_raw().unwrap();
    replacement.release_raw().unwrap();

    // The caller still owns one credit, but its advertised name now selects
    // a different, two-credit pool. Adoption must stop before any child can
    // import that name as if it were the original scheduling authority.
    let imported = Jobserver::with_client(original.clone());
    assert!(imported.is_err(), "a replaced named FIFO was accepted");
    assert_eq!(original.available().unwrap(), 1);
    assert_eq!(replacement.available().unwrap(), 2);
}

#[test]
fn numeric_transport_keeps_the_original_pool_after_the_source_client_drops() {
    use std::os::fd::{AsFd as _, AsRawFd as _};
    let original = jobserver::Client::new(1).unwrap();
    let jobserver::TransportWitnesses::NumericPipe { read, write } =
        original.transport_witnesses().unwrap()
    else {
        panic!("numeric owner changed its transport kind");
    };
    let observer = jobserver::Client::from_pipe(read.as_fd(), write.as_fd()).unwrap();
    let imported = Jobserver::with_client(original.clone()).unwrap();
    let descriptors = imported.pipe_descriptors().expect("actual retained numeric transport");
    let flags = descriptors
        .each_ref()
        .map(|fd| configuration_flags(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) }));
    let from_owned =
        jobserver::Client::from_pipe(descriptors[0].as_fd(), descriptors[1].as_fd()).unwrap();
    for (fd, before) in descriptors.iter().zip(flags) {
        assert_eq!(
            configuration_flags(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) }),
            before
        );
        assert_ne!(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
    }
    drop(original);
    let token = imported.client().acquire().unwrap();
    assert_eq!(observer.available().unwrap(), 0);
    assert_eq!(from_owned.available().unwrap(), 0);
    drop(token);
    assert_eq!(observer.available().unwrap(), 1);
    assert_eq!(from_owned.available().unwrap(), 1);
}

#[test]
fn unchanged_named_transport_keeps_its_kind_and_original_credit() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("credits");
    fifo(&path);
    let original = jobserver::Client::from_fifo(&path).unwrap();
    original.release_raw().unwrap();
    let imported = Jobserver::with_client(original.clone()).unwrap();
    assert!(imported.pipe.is_none(), "named owner became an anonymous pool");
    assert!(imported.pipe_descriptors().is_none(), "named owner advertised numeric transport");
    let token = imported.client().acquire().unwrap();
    assert_eq!(original.available().unwrap(), 0);
    drop(token);
    assert_eq!(original.available().unwrap(), 1);
}

fn command_env<'a>(
    command: &'a std::process::Command,
    key: &str,
) -> Option<Option<&'a std::ffi::OsStr>> {
    command.get_envs().find(|(name, _)| *name == key).map(|(_, value)| value)
}

fn advertised_pair(command: &std::process::Command) -> [i32; 2] {
    let flags = command_env(command, "CARGO_MAKEFLAGS").flatten().unwrap().to_str().unwrap();
    for key in ["MAKEFLAGS", "MFLAGS"] {
        assert_eq!(
            command_env(command, key).flatten().and_then(|value| value.to_str()),
            Some(flags)
        );
    }
    assert!(flags.contains(" --jobserver-fds="), "{flags}");
    let pair: Vec<i32> = flags
        .split_whitespace()
        .find_map(|word| word.strip_prefix("--jobserver-auth="))
        .unwrap_or_else(|| panic!("{flags}"))
        .split(',')
        .map(|number| number.parse().unwrap_or_else(|_| panic!("not a numeric pair: {flags}")))
        .collect();
    pair.try_into().unwrap()
}

// Trust (BOOTSTRAP-JOBSERVER-PROBE-1): GNU make before 4.4 stops on `fifo:`.
// The make program gets the server's own descriptions of the same FIFO as a
// numeric pair; every other child still gets the path.
#[test]
fn gnu_make_gets_a_named_fifo_as_its_own_numeric_pair() {
    use std::os::unix::fs::MetadataExt as _;
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("credits");
    fifo(&path);
    let server = Jobserver::from_fifo(&path).unwrap();
    server.client().release_raw().unwrap();

    let mut other = std::process::Command::new("unused-metadata-only");
    server.configure_make(&mut other);
    let named = command_env(&other, "MAKEFLAGS").flatten().unwrap().to_str().unwrap();
    assert!(named.contains(&format!("--jobserver-auth=fifo:{}", path.display())), "{named}");

    let mut make = std::process::Command::new("unused-metadata-only");
    make.env(super::DESCENDANT_HANDOFF_ENV, "ambient");
    server.configure_gnu_make(&mut make).unwrap();
    assert_eq!(command_env(&make, super::DESCENDANT_HANDOFF_ENV), Some(None));
    let pair = advertised_pair(&make);
    let expected = std::fs::metadata(&path).unwrap();
    for (fd, access) in pair.into_iter().zip([libc::O_RDONLY, libc::O_WRONLY]) {
        // SAFETY: observe the descriptors the command's hook retains.
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
        assert!(flags >= 0, "advertised descriptor {fd} is not open");
        assert_eq!(flags & libc::O_ACCMODE, access);
        let opened = std::fs::File::from(
            // SAFETY: borrowed only to duplicate; the command keeps ownership.
            unsafe { std::os::fd::BorrowedFd::borrow_raw(fd) }.try_clone_to_owned().unwrap(),
        )
        .metadata()
        .unwrap();
        assert_eq!((opened.dev(), opened.ino()), (expected.dev(), expected.ino()));
    }
    // The same pool: a token taken through the pair is the FIFO's one token.
    // SAFETY: borrowed for this call only; the command keeps ownership.
    let observer = unsafe {
        jobserver::Client::from_pipe(
            std::os::fd::BorrowedFd::borrow_raw(pair[0]),
            std::os::fd::BorrowedFd::borrow_raw(pair[1]),
        )
    }
    .unwrap();
    let token = observer.acquire().unwrap();
    assert_eq!(server.client().available().unwrap(), 0);
    drop(token);
    assert_eq!(server.client().available().unwrap(), 1);
    drop((observer, make));
    assert_eq!(server.client().available().unwrap(), 1);
}

#[test]
fn gnu_make_gets_a_numeric_pipe_as_configure_make_hands_it() {
    let server = Jobserver::new(1).unwrap();
    let mut make = std::process::Command::new("unused-metadata-only");
    server.configure_gnu_make(&mut make).unwrap();
    let mut other = std::process::Command::new("unused-metadata-only");
    server.configure_make(&mut other);
    assert_eq!(advertised_pair(&make), advertised_pair(&other));
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn high_pipe_owner(mut server: Jobserver) -> Jobserver {
    use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
    let original = server.pipe_descriptors().unwrap();
    // Keep the child's advertised numbers above ordinary libtest startup FDs.
    // These are real duplicates of the selected pipe, not invented transport.
    let mut limit = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    // SAFETY: local output storage for the native limit query.
    assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limit.as_mut_ptr()) }, 0);
    let limit = unsafe { limit.assume_init() };
    assert!(limit.rlim_cur >= 16);
    let floor = i32::try_from(limit.rlim_cur.saturating_sub(2).min(128)).unwrap();
    let copies = original.each_ref().map(|fd| {
        // SAFETY: duplicate an owned live pipe without replacing any descriptor.
        let number = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_DUPFD_CLOEXEC, floor) };
        assert!(number >= 0);
        // SAFETY: a successful duplication returned a fresh owned description.
        unsafe { OwnedFd::from_raw_fd(number) }
    });
    server.pipe = Some(std::sync::Arc::new(copies));
    server
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn descendant_advertisement(server: &Jobserver) -> (std::ffi::OsString, std::ffi::OsString) {
    let mut command = std::process::Command::new("unused-metadata-only");
    server.configure(&mut command);
    let value = |name: &str| {
        command
            .get_envs()
            .find(|(key, _)| *key == name)
            .and_then(|(_, value)| value)
            .unwrap()
            .to_owned()
    };
    (value(super::DESCENDANT_HANDOFF_ENV), value("CARGO_MAKEFLAGS"))
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn pipe_identity(pipe: &[std::os::fd::OwnedFd; 2]) -> String {
    use std::os::unix::fs::MetadataExt as _;
    pipe.each_ref()
        .map(|fd| {
            let file = std::fs::File::from(fd.try_clone().unwrap());
            let metadata = file.metadata().unwrap();
            format!("{}:{}", metadata.dev(), metadata.ino())
        })
        .join("/")
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn recovery_child(
    advertisement: &std::ffi::OsStr,
    flags: &std::ffi::OsStr,
    identity: &str,
    available: usize,
    refused: bool,
) {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "transport_witness_tests::recovery_child_entry",
            "--ignored",
            "--nocapture",
        ])
        .env("TRUST_JOBSERVER_TEST_RECOVERY_AD", advertisement)
        .env("TRUST_JOBSERVER_TEST_RECOVERY_FLAGS", flags)
        .env("TRUST_JOBSERVER_TEST_PIPE_IDENTITY", identity)
        .env("TRUST_JOBSERVER_TEST_AVAILABLE", available.to_string())
        .env("TRUST_JOBSERVER_TEST_REFUSED", if refused { "1" } else { "0" })
        // Deliberately do not configure explicit descriptor inheritance: this
        // models the unaware spawn. The parent retains its actual pipe owner.
        .output()
        .unwrap();
    assert!(output.status.success(), "child failed: {}", String::from_utf8_lossy(&output.stderr));
    assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed"));
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
#[ignore = "re-executed closed-descriptor transport fixture, not a standalone regression"]
fn recovery_child_entry() {
    let advertisement = std::env::var_os("TRUST_JOBSERVER_TEST_RECOVERY_AD").unwrap();
    let flags = std::env::var_os("TRUST_JOBSERVER_TEST_RECOVERY_FLAGS").unwrap();
    let pair = flags
        .to_str()
        .unwrap()
        .split_whitespace()
        .find_map(|word| word.strip_prefix("--jobserver-auth="))
        .unwrap();
    for number in pair.split(',').map(|number| number.parse::<i32>().unwrap()) {
        // SAFETY: observe only. The parent owns these descriptors in a
        // different process; this fixture's unaware spawn closed its copies.
        assert_eq!(unsafe { libc::fcntl(number, libc::F_GETFD) }, -1);
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::EBADF));
    }
    let recovered = Jobserver::from_authenticated_handoff(&advertisement, &flags);
    if std::env::var("TRUST_JOBSERVER_TEST_REFUSED").unwrap() == "1" {
        assert!(recovered.is_err());
        return;
    }
    let recovered = recovered.unwrap();
    let descriptors = recovered.pipe_descriptors().unwrap();
    assert_eq!(
        pipe_identity(descriptors),
        std::env::var("TRUST_JOBSERVER_TEST_PIPE_IDENTITY").unwrap()
    );
    let client = recovered.client();
    let available =
        std::env::var("TRUST_JOBSERVER_TEST_AVAILABLE").unwrap().parse::<usize>().unwrap();
    assert_eq!(client.available().unwrap(), available);
    if available > 0 {
        let token = client.acquire().unwrap();
        assert_eq!(client.available().unwrap(), available - 1);
        drop(token);
        assert_eq!(client.available().unwrap(), available);
    }
}

#[test]
fn owned_client_retention_preserves_the_original_pipe_and_credit() {
    let original = Jobserver::new(2).unwrap();
    let borrowed = original.client().acquire().unwrap();
    let identity = pipe_identity(original.pipe_descriptors().unwrap());
    let retained = Jobserver::from_owned_client(original.client().clone()).unwrap();
    assert_eq!(pipe_identity(retained.pipe_descriptors().unwrap()), identity);
    assert_eq!(retained.client().available().unwrap(), 1);
    drop(original);
    assert_eq!(retained.client().available().unwrap(), 1);
    drop(borrowed);
    assert_eq!(retained.client().available().unwrap(), 2);
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn descendant_owner_recovers_exact_pipe_without_replenishing_borrowed_credit() {
    use std::os::fd::AsRawFd as _;
    let original = high_pipe_owner(Jobserver::new(2).unwrap());
    let borrowed = original.client().acquire().unwrap();
    let descriptors = original.pipe_descriptors().unwrap();
    let identity = pipe_identity(descriptors);
    let flags = descriptors
        .each_ref()
        .map(|fd| configuration_flags(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) }));
    let selected = original.for_descendant().unwrap();
    assert!(original.handoff.is_none(), "the original early capture was mutated");
    let (advertisement, makeflags) = descendant_advertisement(&selected);
    recovery_child(&advertisement, &makeflags, &identity, 1, false);
    assert_eq!(original.client().available().unwrap(), 1);
    for (fd, before) in descriptors.iter().zip(flags) {
        assert_eq!(
            configuration_flags(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) }),
            before
        );
    }
    drop(borrowed);
    assert_eq!(original.client().available().unwrap(), 2);
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn descendant_clone_retains_recovery_until_last_scheduler_owner_drops() {
    let original = high_pipe_owner(Jobserver::new(0).unwrap());
    let selected = original.for_descendant().unwrap();
    let identity = pipe_identity(original.pipe_descriptors().unwrap());
    let (advertisement, makeflags) = descendant_advertisement(&selected);
    let stored = selected.clone(); // the ownership operation ProcessBuilder uses
    drop(selected);
    drop(original);
    recovery_child(&advertisement, &makeflags, &identity, 0, false);
    assert_eq!(stored.client().available().unwrap(), 0, "no implicit unit became a pipe credit");
    drop(stored);
    recovery_child(&advertisement, &makeflags, &identity, 0, true);
}

#[test]
fn configuration_oracle_still_rejects_actual_nonblocking_and_every_public_configuration_bit() {
    use std::os::fd::AsRawFd as _;
    for bit in [
        libc::O_WRONLY,
        libc::O_RDWR,
        libc::O_NONBLOCK,
        libc::O_APPEND,
        libc::O_ASYNC,
        libc::O_SYNC,
        libc::O_DSYNC,
    ] {
        assert_ne!(configuration_flags(0), configuration_flags(bit), "{bit:#x}");
    }
    #[cfg(target_os = "macos")]
    {
        assert_eq!(configuration_flags(0), configuration_flags(0x1000 | 0x2000 | 0x10000));
    }
    let server = Jobserver::new(1).unwrap();
    let descriptors = server.pipe_descriptors().unwrap();
    let descriptor = &descriptors[0];
    let before = unsafe { libc::fcntl(descriptor.as_raw_fd(), libc::F_GETFL) };
    assert!(before >= 0);
    assert_eq!(
        unsafe { libc::fcntl(descriptor.as_raw_fd(), libc::F_SETFL, before ^ libc::O_NONBLOCK) },
        0
    );
    let changed = unsafe { libc::fcntl(descriptor.as_raw_fd(), libc::F_GETFL) };
    assert_ne!(configuration_flags(before), configuration_flags(changed));
    assert_eq!(unsafe { libc::fcntl(descriptor.as_raw_fd(), libc::F_SETFL, before) }, 0);
    assert_eq!(
        configuration_flags(unsafe { libc::fcntl(descriptor.as_raw_fd(), libc::F_GETFL) }),
        configuration_flags(before)
    );
    assert_ne!(unsafe { libc::fcntl(descriptor.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
    assert_eq!(server.client().available().unwrap(), 1);
}
