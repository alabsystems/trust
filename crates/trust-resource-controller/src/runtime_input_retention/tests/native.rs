//! Mechanical SCM/RAII controls. Synthetic metadata grants no source, SDK,
//! completed producer, original Job or Host execution authority.
use std::fs::{self, File, OpenOptions};
use std::os::fd::{AsFd, AsRawFd};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use super::*;
use crate::Channel;

fn isolated(test: &str) -> bool {
    if std::env::var("TRUST_RETENTION_ISOLATED").as_deref() == Ok(test) {
        return false;
    }
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", test, "--nocapture"])
        .env("TRUST_RETENTION_ISOLATED", test)
        .output()
        .unwrap();
    assert!(out.status.success(), "real isolated actor failed: {out:?}");
    true
}
fn root() -> PathBuf {
    // Darwin's per-user TMPDIR can already consume most of sockaddr_un.
    // Create a fresh private fixture directory under the short native base;
    // never truncate a production path or change the native socket bound.
    // Parallel tests can read one clock microsecond; the sequence keeps each fixture its own.
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let path = Path::new("/tmp").join(format!(
        "retained-inputs-{}-{}-{}",
        std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
    fs::canonicalize(path).unwrap()
}
fn observed(kind: Kind, logical: &[u8], path: &Path, file: &File) -> Input {
    use std::os::unix::ffi::OsStrExt;
    let meta = file.metadata().unwrap();
    Input {
        kind,
        logical_path: logical.to_vec(),
        target: path.as_os_str().as_bytes().to_vec(),
        alias: None,
        backing: FileIdentity { device: meta.dev(), inode: meta.ino() },
        size: (kind == Kind::RuntimeFile).then_some(meta.len()),
        sha256: (kind == Kind::RuntimeFile).then_some([0; 32]),
        executable: !kind.directory() && meta.mode() & 0o111 != 0,
    }
}
fn population(root: &Path) -> (Request, Vec<File>) {
    let runtime = root.join("runtime");
    let output = root.join("output");
    fs::create_dir(&runtime).unwrap();
    fs::create_dir(&output).unwrap();
    let mut value = Request { query: query(), transfer: [4; 16], inputs: Vec::new() };
    let mut files = Vec::new();
    let lock = output.join("lock");
    let file =
        OpenOptions::new().create_new(true).read(true).write(true).mode(0o600).open(&lock).unwrap();
    file.lock().unwrap();
    value.inputs.push(observed(Kind::OutputLock, b"lock", &lock, &file));
    files.push(file);
    let file = File::open(&runtime).unwrap();
    value.inputs.push(observed(Kind::RuntimeRoot, b"", &runtime, &file));
    files.push(file);
    let file = File::open(&output).unwrap();
    value.inputs.push(observed(Kind::OutputRoot, b"", &output, &file));
    files.push(file);
    for n in 0..12 {
        let logical = format!("dir{n}");
        let path = runtime.join(&logical);
        fs::create_dir(&path).unwrap();
        let file = File::open(&path).unwrap();
        value.inputs.push(observed(Kind::RuntimeDirectory, logical.as_bytes(), &path, &file));
        files.push(file);
    }
    for n in 0..156 {
        let logical = format!("dir0/file{n}");
        let path = runtime.join(&logical);
        fs::write(&path, b"actual bytes").unwrap();
        let file = File::open(&path).unwrap();
        value.inputs.push(observed(Kind::RuntimeFile, logical.as_bytes(), &path, &file));
        files.push(file);
    }
    assert_eq!(files.len(), 171);
    value.validate().unwrap();
    (value, files)
}
fn wait_path(path: &Path) {
    let deadline = Instant::now() + Duration::from_secs(30);
    while !path.exists() {
        assert!(Instant::now() < deadline, "actor control missing {}", path.display());
        std::thread::sleep(Duration::from_millis(5));
    }
}
#[test]
fn receiver_actor() {
    let Some(root) = std::env::var_os("TRUST_RETENTION_ACTOR_ROOT") else { return };
    let root = PathBuf::from(root);
    let mode = std::env::var("TRUST_RETENTION_ACTOR_MODE").unwrap();
    let socket = UnixStream::connect(root.join("socket")).unwrap();
    let mut channel = Channel::new(socket).unwrap();
    let request =
        Request::decode(&channel.receive(Instant::now() + Duration::from_secs(30)).unwrap())
            .unwrap();
    let budget = if ["deadline", "final-deadline"].contains(&mode.as_str()) {
        Duration::from_millis(250)
    } else {
        Duration::from_secs(30)
    };
    let mut checks = 0;
    let result = transport::receive_inputs(&mut channel, &request, Instant::now() + budget, || {
        checks += 1;
        if mode == "final-deadline" && checks == 3 {
            std::thread::sleep(Duration::from_millis(350));
        }
        if mode == "peer-lost" && checks == 2 {
            Err(std::io::ErrorKind::PermissionDenied.into())
        } else {
            Ok(())
        }
    });
    if mode == "positive" {
        let actual = result.unwrap();
        assert_eq!(actual.len(), 171);
        channel.send(b"retained", Instant::now() + Duration::from_secs(30)).unwrap();
        transport::finish_reply(&mut channel).unwrap();
        wait_path(&root.join("release"));
        drop(actual);
        drop(channel);
    } else {
        assert!(result.is_err(), "malformed {mode} accepted");
        assert!(channel.poisoned());
        drop(channel);
        wait_path(&root.join("sources-dropped"));
        OpenOptions::new()
            .read(true)
            .write(true)
            .open(root.join("output/lock"))
            .unwrap()
            .try_lock()
            .unwrap();
    }
}
fn child(root: &Path, mode: &str) -> std::process::Child {
    std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "runtime_input_retention::tests::native::receiver_actor", "--nocapture"])
        .env("TRUST_RETENTION_ACTOR_ROOT", root)
        .env("TRUST_RETENTION_ACTOR_MODE", mode)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap()
}
#[test]
fn actual_171_rights_cross_chunks_preserve_original_lock_and_flags_until_final_close() {
    if isolated(
        "runtime_input_retention::tests::native::actual_171_rights_cross_chunks_preserve_original_lock_and_flags_until_final_close",
    ) {
        return;
    }
    let root = root();
    let (request, files) = population(&root);
    let listener = UnixListener::bind(root.join("socket")).unwrap();
    let worker = child(&root, "positive");
    let (mut channel, deadline) = (
        Channel::new(listener.accept().unwrap().0).unwrap(),
        Instant::now() + Duration::from_secs(30),
    );
    let flags = files
        .iter()
        .map(|f| unsafe { libc::fcntl(f.as_raw_fd(), libc::F_GETFL) })
        .collect::<Vec<_>>();
    channel.send(&request.encode().unwrap(), deadline).unwrap();
    let mut checks = 0;
    transport::send_inputs(
        &mut channel,
        &request,
        &files.iter().map(AsFd::as_fd).collect::<Vec<_>>(),
        deadline,
        || {
            checks += 1;
            Ok(())
        },
    )
    .unwrap();
    assert!(checks >= 3);
    assert_eq!(channel.receive(deadline).unwrap(), b"retained");
    transport::require_reply_eof(&mut channel, deadline).unwrap();
    for (file, old) in files.iter().zip(flags) {
        assert_eq!(
            crate::tests::caller_status_flags(unsafe {
                libc::fcntl(file.as_raw_fd(), libc::F_GETFL)
            }),
            crate::tests::caller_status_flags(old)
        );
    }
    drop(files);
    let probe = OpenOptions::new().read(true).write(true).open(root.join("output/lock")).unwrap();
    assert!(matches!(probe.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
    fs::write(root.join("release"), b"release").unwrap();
    let out = worker.wait_with_output().unwrap();
    assert!(out.status.success(), "{out:?}");
    probe.try_lock().unwrap();
    drop(probe);
    fs::remove_dir_all(root).unwrap();
}
#[test]
fn malformed_chunk_tails_close_actual_received_prefix_and_never_complete() {
    if isolated(
        "runtime_input_retention::tests::native::malformed_chunk_tails_close_actual_received_prefix_and_never_complete",
    ) {
        return;
    }
    for mode in [
        "nonce",
        "reordered",
        "duplicate",
        "count",
        "marker",
        "missing",
        "trailing",
        "trailing-rights",
        "deadline",
        "peer-lost",
        "final-deadline",
    ] {
        let root = root();
        let (request, files) = population(&root);
        let listener = UnixListener::bind(root.join("socket")).unwrap();
        let worker = child(&root, mode);
        let mut channel = Channel::new(listener.accept().unwrap().0).unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        channel.send(&request.encode().unwrap(), deadline).unwrap();
        channel
            .send(
                &Transfer::Chunk { key: request.key(), offset: 0, count: 128 }.encode().unwrap(),
                deadline,
            )
            .unwrap();
        channel
            .send_retained_inputs(
                &files[..128].iter().map(AsFd::as_fd).collect::<Vec<_>>(),
                deadline,
            )
            .unwrap();
        if mode == "deadline" {
            std::thread::sleep(Duration::from_millis(400));
        } else if !["missing", "peer-lost"].contains(&mode) {
            let mut key = request.key();
            if mode == "nonce" {
                key.transfer = [8; 16];
            }
            let offset = if mode == "reordered" {
                129
            } else if mode == "duplicate" {
                0
            } else {
                128
            };
            channel
                .send(&Transfer::Chunk { key, offset, count: 43 }.encode().unwrap(), deadline)
                .unwrap();
            if ["count", "marker", "trailing", "trailing-rights", "final-deadline"].contains(&mode)
            {
                let end = if mode == "count" { 170 } else { 171 };
                if mode == "marker" {
                    let socket = UnixStream::from(channel.as_fd().try_clone_to_owned().unwrap());
                    jobserver_utils::descriptor_transfer::send(
                        &socket,
                        &files[128..end].iter().map(AsFd::as_fd).collect::<Vec<_>>(),
                        RIGHTS_MARKER ^ 1,
                        deadline,
                    )
                    .unwrap();
                } else {
                    channel
                        .send_retained_inputs(
                            &files[128..end].iter().map(AsFd::as_fd).collect::<Vec<_>>(),
                            deadline,
                        )
                        .unwrap();
                }
                if ["trailing", "trailing-rights", "final-deadline"].contains(&mode) {
                    channel
                        .send(
                            &Transfer::End { key: request.key(), count: 171 }.encode().unwrap(),
                            deadline,
                        )
                        .unwrap();
                    if mode == "trailing" {
                        channel.send(b"trailing", deadline).unwrap();
                    } else if mode == "trailing-rights" {
                        channel.send_retained_inputs(&[files[0].as_fd()], deadline).unwrap();
                    }
                }
            }
        }
        let _ = channel.end_retained_send();
        drop(channel);
        drop(files);
        fs::write(root.join("sources-dropped"), b"closed").unwrap();
        let out = worker.wait_with_output().unwrap();
        assert!(out.status.success(), "mode {mode}: {out:?}");
        fs::remove_dir_all(root).unwrap();
    }
}
