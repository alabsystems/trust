// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::io::{Read, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::UnixListener;
use std::process::{Command, Stdio};
use std::time::Duration;

use super::*;
use crate::schema::Record;
#[path = "tests/control_transfer.rs"]
mod control_transfer;
#[path = "tests/lifecycle.rs"]
mod lifecycle;
use lifecycle::{
    FixtureRoot, HANG, OwnedFixtureChild, STARTED, bounded_child, prove_child_started,
};

fn write(path: &Path, bytes: &[u8]) {
    let mut file =
        fs::OpenOptions::new().create_new(true).write(true).mode(0o600).open(path).unwrap();
    file.write_all(bytes).unwrap();
}
struct Fixture {
    root: FixtureRoot,
    image: Option<PathBuf>,
}
impl Fixture {
    fn new() -> Self {
        let root = tempfile::Builder::new()
            .prefix("rp-")
            .tempdir_in(std::env::temp_dir().canonicalize().unwrap())
            .unwrap();
        fs::set_permissions(root.path(), fs::Permissions::from_mode(0o700)).unwrap();
        for name in ["images", "instances"] {
            fs::DirBuilder::new().mode(0o700).create(root.path().join(name)).unwrap();
        }
        write(&root.path().join("version.json"), b"{\"version\":1}");
        write(&root.path().join("lock"), b"");
        write(
            &root.path().join("instances/book.json"),
            &Book { version: 1, instances: vec![] }.encode().unwrap(),
        );
        Self { root: FixtureRoot::new(root), image: None }
    }
    fn cache(&mut self) -> PathBuf {
        let source = std::env::current_exe().unwrap();
        let bytes = fs::read(&source).unwrap();
        let digest = hex(&Sha256::digest(&bytes));
        let directory = self.root.path().join("images").join(&digest);
        fs::DirBuilder::new().mode(0o700).create(&directory).unwrap();
        let helper = directory.join("aterm");
        write(&helper, &bytes);
        fs::set_permissions(&helper, fs::Permissions::from_mode(0o500)).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o500)).unwrap();
        self.image = Some(directory);
        self.root.arm();
        helper
    }

    fn completed(&mut self, output: &std::process::Output) {
        assert!(output.status.success(), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout).lines().any(|line| line.ends_with(STARTED)),
            "cached native fixture supplied no execution proof: {output:?}"
        );
        self.root.ran();
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        if self.root.may_remove()
            && let Some(path) = &self.image
        {
            let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o700));
        }
    }
}

#[test]
fn existing_store_is_read_only_and_replaced_backing_refuses() {
    let fixture = Fixture::new();
    let root = fixture.root.path();
    assert!(Store::open_at(&root.join("missing")).is_err());
    assert!(!root.join("missing").exists());
    let store = Store::open_at(root).unwrap();
    assert!(store.instances().unwrap().is_empty());
    fs::rename(root.join("instances"), root.join("original")).unwrap();
    fs::DirBuilder::new().mode(0o700).create(root.join("instances")).unwrap();
    write(&root.join("instances/book.json"), b"{\"version\":1,\"instances\":[]}");
    assert!(store.instances().is_err());
}

#[test]
fn pinned_directory_comparison_refuses_a_store_opened_during_actual_path_aba() {
    use std::os::fd::AsFd as _;
    let first = Fixture::new();
    let second = Fixture::new();
    let original = private::directory(first.root.path()).unwrap();
    let expected = identity(&original.metadata().unwrap());
    let held = Store::open_at(first.root.path()).unwrap();
    assert!(held.same_original_directory(original.as_fd()).unwrap());
    let saved = first.root.path().with_extension("saved-original");
    fs::rename(first.root.path(), &saved).unwrap();
    fs::rename(second.root.path(), first.root.path()).unwrap();
    let foreign = Store::open_at(first.root.path()).unwrap();
    fs::rename(first.root.path(), second.root.path()).unwrap();
    fs::rename(&saved, first.root.path()).unwrap();
    assert_eq!(
        identity(&fs::symlink_metadata(first.root.path()).unwrap()),
        expected,
        "original path pre/post checks see A again"
    );
    assert!(
        !foreign.same_original_directory(original.as_fd()).unwrap(),
        "the reader retained B while the independently held locator retained A"
    );
    let second_original = private::directory(second.root.path()).unwrap();
    assert!(
        foreign.same_original_directory(second_original.as_fd()).unwrap(),
        "comparison uses actual held descriptions, not the reader's now-stale pathname"
    );
    assert!(foreign.validate().is_err(), "all ordinary named backing validation remains intact");
    assert!(held.same_original_directory(original.as_fd()).unwrap());
}

fn run_cached_host(tamper: bool) {
    run_cached_host_phase(tamper, Phase::Fresh);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Fresh,
    Parent,
    Accept,
    Discovery,
    OwnerRead,
    ClientRead,
    Close,
}

impl Phase {
    fn name(self) -> &'static str {
        match self {
            Self::Fresh => "fresh",
            Self::Parent => "parent",
            Self::Accept => "accept",
            Self::Discovery => "discovery",
            Self::OwnerRead => "owner-read",
            Self::ClientRead => "client-read",
            Self::Close => "close",
        }
    }

    fn received() -> Self {
        match std::env::var("PROVENANCE_FIXTURE_AGED").as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("fresh") => Self::Fresh,
            Ok("parent") => Self::Parent,
            Ok("accept") => Self::Accept,
            Ok("discovery") => Self::Discovery,
            Ok("owner-read") => Self::OwnerRead,
            Ok("client-read") => Self::ClientRead,
            Ok("close") => Self::Close,
            other => panic!("invalid fixture phase: {other:?}"),
        }
    }

    fn start(self, phase: Self) -> Instant {
        let age = if self == phase {
            match phase {
                Self::Fresh => 0,
                Self::Parent => 16,
                Self::Accept => 9,
                Self::Discovery | Self::OwnerRead | Self::Close => 5,
                Self::ClientRead => 4,
            }
        } else {
            0
        };
        Instant::now() - Duration::from_secs(age)
    }
}

fn remaining(started: Instant) -> Duration {
    HANG.checked_sub(started.elapsed())
        .filter(|left| !left.is_zero())
        .expect("required native fixture hang detector expired")
}

fn run_cached_host_phase(tamper: bool, phase: Phase) {
    let mut fixture = Fixture::new();
    let helper = fixture.cache();
    let mut command = Command::new(&helper);
    command
        .args(["--exact", "reader::tests::fixture_role", "--nocapture"])
        .env("PROVENANCE_FIXTURE_ROLE", "host")
        .env("PROVENANCE_FIXTURE_ROOT", fixture.root.path())
        .env("PROVENANCE_FIXTURE_CLIENT", std::env::current_exe().unwrap())
        .env("PROVENANCE_FIXTURE_TAMPER", if tamper { "yes" } else { "no" })
        .env("PROVENANCE_FIXTURE_AGED", phase.name())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if phase == Phase::Close {
        command.env("PROVENANCE_FIXTURE_PINNED", "1");
    } else {
        command.env_remove("PROVENANCE_FIXTURE_PINNED");
    }
    let child = OwnedFixtureChild::new(command.spawn().unwrap());
    let output = bounded_child(child, phase.start(Phase::Parent) + HANG);
    fixture.completed(&output);
}

#[test]
fn actual_cached_ancestor_connects_for_a_different_loaded_client_image() {
    run_cached_host(false);
}

#[test]
fn required_native_reader_phases_keep_original_starts_without_latency_budgets() {
    for phase in [
        Phase::Parent,
        Phase::Accept,
        Phase::Discovery,
        Phase::OwnerRead,
        Phase::ClientRead,
        Phase::Close,
    ] {
        run_cached_host_phase(false, phase);
    }
}

#[test]
fn a_cached_image_without_native_execution_proof_is_kept() {
    let mut fixture = Fixture::new();
    let helper = fixture.cache();
    let root = fixture.root.path().to_owned();
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(fixture))).is_err());
    assert!(helper.is_file());
    // No process was launched by this cleanup control. Its image was never assessed.
    fs::set_permissions(helper.parent().unwrap(), fs::Permissions::from_mode(0o700)).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn successful_status_without_child_written_execution_proof_is_refused() {
    use std::os::unix::process::ExitStatusExt as _;
    let mut fixture = Fixture::new();
    let helper = fixture.cache();
    let root = fixture.root.path().to_owned();
    let output = std::process::Output {
        status: std::process::ExitStatus::from_raw(0),
        stdout: b"status supplied no execution proof".to_vec(),
        stderr: vec![],
    };
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            fixture.completed(&output);
        }))
        .is_err()
    );
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(fixture))).is_err());
    assert!(helper.is_file());
    // This control constructed output DATA and launched no executable.
    fs::set_permissions(helper.parent().unwrap(), fs::Permissions::from_mode(0o700)).unwrap();
    fs::remove_dir_all(root).unwrap();
}
#[test]
fn post_reply_validation_refuses_a_changed_immutable_helper() {
    run_cached_host(true);
}

#[test]
fn fixture_role() {
    let Ok(role) = std::env::var("PROVENANCE_FIXTURE_ROLE") else {
        return;
    };
    println!("{STARTED}");
    std::io::stdout().flush().unwrap();
    let root = PathBuf::from(std::env::var_os("PROVENANCE_FIXTURE_ROOT").unwrap());
    let tamper = std::env::var("PROVENANCE_FIXTURE_TAMPER").unwrap() == "yes";
    if role == "helper" {
        let mut byte = [0];
        std::io::stdin().read_exact(&mut byte).unwrap();
        return;
    }
    if role == "host" {
        host_role(&root, tamper);
    } else {
        client_role(&root, tamper);
    }
}

fn host_role(root: &Path, tamper: bool) {
    let phase = Phase::received();
    let helper = std::env::current_exe().unwrap();
    let listener = UnixListener::bind(root.join("s")).unwrap();
    fs::set_permissions(root.join("s"), fs::Permissions::from_mode(0o600)).unwrap();
    let native = process::read_identity(std::process::id()).unwrap();
    let (host, boot) = process::host_boot().unwrap();
    let directory = helper.parent().unwrap();
    let record = Record {
        pid: native.pid,
        birth: native.birth,
        host,
        boot,
        digest: directory.file_name().unwrap().to_str().unwrap().to_owned(),
        image: identity(&fs::metadata(&helper).unwrap()),
        directory: identity(&fs::metadata(directory).unwrap()),
        socket_hex: hex(root.join("s").as_os_str().as_bytes()),
        socket: identity(&fs::symlink_metadata(root.join("s")).unwrap()),
    };
    fs::write(
        root.join("instances/book.json"),
        Book { version: 1, instances: vec![record] }.encode().unwrap(),
    )
    .unwrap();
    let mut child = OwnedFixtureChild::new(
        Command::new(std::env::var_os("PROVENANCE_FIXTURE_CLIENT").unwrap())
            .args(["--exact", "reader::tests::fixture_role", "--nocapture"])
            .env("PROVENANCE_FIXTURE_ROLE", "client")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    listener.set_nonblocking(true).unwrap();
    let deadline = phase.start(Phase::Accept) + HANG;
    let mut stream = loop {
        match listener.accept() {
            Ok((stream, _)) => break stream,
            Err(error)
                if error.kind() == io::ErrorKind::WouldBlock && Instant::now() < deadline =>
            {
                if child.try_wait().unwrap().is_some() {
                    let output = bounded_child(child, Instant::now() + HANG);
                    panic!("owned client exited before acceptance: {output:?}");
                }
                std::thread::sleep(Duration::from_millis(5))
            }
            result => {
                let _ = child.kill();
                let output = bounded_child(child, Instant::now() + HANG);
                panic!("owned accept: {result:?}; {output:?}");
            }
        }
    };
    if std::env::var("PROVENANCE_FIXTURE_PINNED").as_deref() == Ok("reconnect") {
        stream.set_nonblocking(true).unwrap();
        bounded_read(&mut stream, &mut [0], deadline, true);
        let mut stream = loop {
            match listener.accept() {
                Ok((stream, _)) => break stream,
                Err(error)
                    if error.kind() == io::ErrorKind::WouldBlock && Instant::now() < deadline =>
                {
                    std::thread::sleep(Duration::from_millis(1))
                }
                other => panic!("pinned reconnect failed: {other:?}"),
            }
        };
        stream.set_nonblocking(true).unwrap();
        let mut ping = [0; 4];
        bounded_read(&mut stream, &mut ping, deadline, false);
        assert_eq!(&ping, b"ping");
        stream.write_all(b"pong").unwrap();
        let mut ack = [0];
        bounded_read(&mut stream, &mut ack, deadline, false);
        assert_eq!(ack, [1]);
        let output = bounded_child(child, Instant::now() + HANG);
        assert!(output.status.success(), "{output:?}");
        return;
    }
    stream.set_nonblocking(false).unwrap();
    if std::env::var_os("PROVENANCE_FIXTURE_PINNED").is_some() {
        // Use the same nonblocking/deadline pattern as production discovery;
        // this fixture's native SO_RCVTIMEO setter refuses EINVAL here.
        stream.set_nonblocking(true).unwrap();
        let deadline = phase.start(Phase::Close) + HANG;
        loop {
            match stream.read(&mut [0]) {
                Ok(0) => break,
                Err(error)
                    if error.kind() == io::ErrorKind::WouldBlock && Instant::now() < deadline =>
                {
                    std::thread::sleep(Duration::from_millis(1));
                }
                other => panic!("discovery stream did not close before deadline: {other:?}"),
            }
        }
        let output = bounded_child(child, Instant::now() + HANG);
        assert!(output.status.success(), "{output:?}");
        return;
    }
    stream.set_nonblocking(false).unwrap();
    stream.set_read_timeout(Some(remaining(phase.start(Phase::OwnerRead)))).unwrap();
    let mut request = [0; 4];
    stream.read_exact(&mut request).unwrap();
    assert_eq!(&request, b"ping");
    if tamper {
        fs::set_permissions(&helper, fs::Permissions::from_mode(0o700)).unwrap();
    }
    stream.write_all(b"pong").unwrap();
    let mut ack = [0];
    if tamper {
        assert_eq!(stream.read(&mut ack).unwrap(), 0);
    } else {
        stream.read_exact(&mut ack).unwrap();
        assert_eq!(ack, [1]);
    }
    let output = bounded_child(child, Instant::now() + HANG);
    assert!(output.status.success(), "{output:?}");
}
fn client_role(root: &Path, tamper: bool) {
    let phase = Phase::received();
    let deadline = phase.start(Phase::Discovery) + HANG;
    let host = Store::open_at(root).unwrap().connect_ancestor(deadline).unwrap();
    if std::env::var("PROVENANCE_FIXTURE_PINNED").as_deref() == Ok("reconnect") {
        let pinned = host.into_helper(deadline).unwrap();
        let host = pinned.connect(deadline).unwrap();
        let mut stream = host.stream();
        stream.write_all(b"ping").unwrap();
        let mut pong = [0; 4];
        bounded_read(&mut stream, &mut pong, deadline, false);
        assert_eq!(&pong, b"pong");
        host.revalidate(deadline).unwrap();
        stream.write_all(&[1]).unwrap();
        return;
    }
    if std::env::var_os("PROVENANCE_FIXTURE_PINNED").is_some() {
        let pinned = host.into_helper(deadline).unwrap();
        use std::os::fd::{AsFd as _, AsRawFd as _};
        let original = pinned.duplicate_original_store(deadline).unwrap();
        let store = Store::open_at(root).unwrap();
        assert!(store.same_original_directory(original.as_fd()).unwrap());
        assert!(original.as_raw_fd() >= 6);
        assert_ne!(
            unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC,
            0
        );
        assert_eq!(
            unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) } & libc::O_ACCMODE,
            libc::O_RDONLY
        );
        assert!(pinned.duplicate_original_store(Instant::now()).is_err());
        let mut helper = OwnedFixtureChild::new(
            Command::new(pinned.helper_path())
                .args(["--exact", "reader::tests::fixture_role", "--nocapture"])
                .env("PROVENANCE_FIXTURE_ROLE", "helper")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .spawn()
                .unwrap(),
        );
        let helper_output = prove_child_started(&mut helper);
        assert_eq!(pinned.validate_child(&helper, deadline).unwrap().pid, helper.id());
        let mut unrelated = OwnedFixtureChild::new(
            Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "reader::tests::fixture_role", "--nocapture"])
                .env("PROVENANCE_FIXTURE_ROLE", "helper")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .spawn()
                .unwrap(),
        );
        let unrelated_output = prove_child_started(&mut unrelated);
        assert!(pinned.validate_child(&unrelated, deadline).is_err());
        helper.stdin.take().unwrap().write_all(&[1]).unwrap();
        unrelated.stdin.take().unwrap().write_all(&[1]).unwrap();
        assert!(helper.wait().unwrap().success());
        assert!(unrelated.wait().unwrap().success());
        helper_output.join().unwrap();
        unrelated_output.join().unwrap();
        return;
    }
    assert_ne!(std::env::current_exe().unwrap(), host.helper_path());
    let mut stream = host.stream();
    stream.set_nonblocking(false).unwrap();
    stream.set_read_timeout(Some(remaining(phase.start(Phase::ClientRead)))).unwrap();
    stream.write_all(b"ping").unwrap();
    let mut reply = [0; 4];
    stream.read_exact(&mut reply).unwrap();
    assert_eq!(&reply, b"pong");
    if tamper {
        assert!(host.revalidate(deadline).is_err());
    } else {
        host.revalidate(deadline).unwrap();
        stream.write_all(&[1]).unwrap();
    }
}

#[test]
fn pinned_helper_requires_original_loaded_image_after_idle_discovery_closes() {
    let mut fixture = Fixture::new();
    let helper = fixture.cache();
    let child = OwnedFixtureChild::new(
        Command::new(&helper)
            .args(["--exact", "reader::tests::fixture_role", "--nocapture"])
            .env("PROVENANCE_FIXTURE_ROLE", "host")
            .env("PROVENANCE_FIXTURE_ROOT", fixture.root.path())
            .env("PROVENANCE_FIXTURE_CLIENT", std::env::current_exe().unwrap())
            .env("PROVENANCE_FIXTURE_TAMPER", "no")
            .env("PROVENANCE_FIXTURE_PINNED", "1")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let output = bounded_child(child, Instant::now() + HANG);
    fixture.completed(&output);
}

fn bounded_read(stream: &mut impl Read, bytes: &mut [u8], deadline: Instant, eof: bool) {
    let mut offset = 0;
    while offset < bytes.len() {
        match stream.read(&mut bytes[offset..]) {
            Ok(0) if eof => return,
            Ok(n) if n > 0 && !eof => offset += n,
            Err(error)
                if error.kind() == io::ErrorKind::WouldBlock && Instant::now() < deadline =>
            {
                std::thread::sleep(Duration::from_millis(1))
            }
            other => panic!("bounded fixture read failed: {other:?}"),
        }
    }
    assert!(!eof);
}
#[test]
fn pinned_host_reconnect_keeps_original_image_and_native_peer_through_ack() {
    let mut fixture = Fixture::new();
    let helper = fixture.cache();
    let child = OwnedFixtureChild::new(
        Command::new(&helper)
            .args(["--exact", "reader::tests::fixture_role", "--nocapture"])
            .env("PROVENANCE_FIXTURE_ROLE", "host")
            .env("PROVENANCE_FIXTURE_ROOT", fixture.root.path())
            .env("PROVENANCE_FIXTURE_CLIENT", std::env::current_exe().unwrap())
            .env("PROVENANCE_FIXTURE_TAMPER", "no")
            .env("PROVENANCE_FIXTURE_PINNED", "reconnect")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let output = bounded_child(child, Instant::now() + HANG);
    fixture.completed(&output);
}
