// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
use std::io::{BufRead, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::process::{Child, Command, Stdio};
use std::time::Duration;

use super::*;
fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}
fn write(path: &Path, bytes: &[u8]) {
    fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .unwrap()
        .write_all(bytes)
        .unwrap();
}
struct Fixture {
    _root: std::mem::ManuallyDrop<tempfile::TempDir>,
    store: Store,
    path: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        // Leave cache images in place even if an exec never proves it ran.
        let root = std::mem::ManuallyDrop::new(
            tempfile::Builder::new()
                .prefix("image-pin-")
                .tempdir_in(std::env::temp_dir().canonicalize().unwrap())
                .unwrap(),
        );
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
        let bytes = fs::read(std::env::current_exe().unwrap()).unwrap();
        let dir = root.path().join("images").join(hex(&Sha256::digest(&bytes)));
        fs::DirBuilder::new().mode(0o700).create(&dir).unwrap();
        let path = dir.join("aterm");
        write(&path, &bytes);
        fs::set_permissions(&path, fs::Permissions::from_mode(0o500)).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o500)).unwrap();
        let store = Store::open_at(root.path()).unwrap();
        Self { _root: root, store, path }
    }
}
#[test]
fn cached_image_actor() {
    if std::env::var_os("PINNED_PROGRAM_FIXTURE").is_none() {
        return;
    }
    println!("pinned-image-running");
    std::io::stdout().flush().unwrap();
    let mut done = [0; 1];
    std::io::stdin().read_exact(&mut done).unwrap();
}
struct OwnedChild(Child);
impl Drop for OwnedChild {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
#[test]
fn once_hashed_pin_validates_native_cached_child_and_rejects_changed_backing() {
    let fixture = Fixture::new();
    assert!(fixture.store.pin_program(&std::env::current_exe().unwrap(), deadline()).is_err());
    let pin = fixture.store.pin_program(&fixture.path, deadline()).unwrap();
    let mut child = OwnedChild(
        Command::new(&fixture.path)
            .args(["--exact", "reader::image_pin::tests::cached_image_actor", "--nocapture"])
            .env("PINNED_PROGRAM_FIXTURE", "1")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let output = child.0.stdout.take().unwrap();
    let (sent, received) = std::sync::mpsc::sync_channel(1);
    let reader = std::thread::spawn(move || {
        let mut read = std::io::BufReader::new(output);
        let mut line = String::new();
        let mut sent = Some(sent);
        loop {
            line.clear();
            if read.read_line(&mut line).unwrap() == 0 {
                break;
            }
            if line.contains("pinned-image-running")
                && let Some(sent) = sent.take()
            {
                sent.send(()).unwrap();
            }
        }
    });
    received.recv_timeout(Duration::from_secs(30)).unwrap();
    let native = process::read_identity(child.0.id()).unwrap();
    pin.validate_cached_process(native, deadline()).unwrap();
    let mut wrong = native;
    wrong.birth += 1;
    assert!(pin.validate_cached_process(wrong, deadline()).is_err());
    assert!(pin.validate_cached_process(native, Instant::now()).is_err());
    fs::set_permissions(&fixture.path, fs::Permissions::from_mode(0o700)).unwrap();
    assert!(pin.validate_cached_process(native, deadline()).is_err());
    assert!(fixture.store.pin_program(&fixture.path, deadline()).is_err(), "mutable image refused");
    fs::set_permissions(&fixture.path, fs::Permissions::from_mode(0o500)).unwrap();
    assert!(
        pin.validate_cached_process(native, deadline()).is_err(),
        "restored mode does not restore original metadata"
    );
    child.0.stdin.take().unwrap().write_all(b"x").unwrap();
    assert!(child.0.wait().unwrap().success());
    reader.join().unwrap();
    let fresh = fixture.store.pin_program(&fixture.path, deadline()).unwrap();
    assert!(
        fresh.validate_cached_process(native, deadline()).is_err(),
        "exited original process refuses"
    );
    let parent = fixture.path.parent().unwrap();
    fs::set_permissions(parent, fs::Permissions::from_mode(0o700)).unwrap();
    fs::rename(&fixture.path, parent.join("original")).unwrap();
    fs::copy(parent.join("original"), &fixture.path).unwrap();
    fs::set_permissions(&fixture.path, fs::Permissions::from_mode(0o500)).unwrap();
    fs::set_permissions(parent, fs::Permissions::from_mode(0o500)).unwrap();
    assert!(
        fresh.reference().check(&fresh.image).is_err(),
        "replacement path cannot refresh original pin"
    );
    let mutated = fixture.store.pin_program(&fixture.path, deadline()).unwrap();
    fs::set_permissions(&fixture.path, fs::Permissions::from_mode(0o700)).unwrap();
    fs::OpenOptions::new().append(true).open(&fixture.path).unwrap().write_all(b"changed").unwrap();
    fs::set_permissions(&fixture.path, fs::Permissions::from_mode(0o500)).unwrap();
    assert!(mutated.reference().check(&mutated.image).is_err());
    assert!(
        fixture.store.pin_program(&fixture.path, deadline()).is_err(),
        "new pin verifies actual digest"
    );
}
