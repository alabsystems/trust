// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! A real cached executable publishes its own listener and exercises original
//! control transfers. No fake Host/SDK/CPU or decoded readiness is constructed.
use std::os::fd::{AsFd, AsRawFd, OwnedFd};

use super::*;

#[test]
fn native_control_originals_validate_and_preserve_original_byte_reads() {
    let mut fixture = Fixture::new();
    let helper = fixture.cache();
    let child = OwnedFixtureChild::new(
        Command::new(&helper)
            .args([
                "--exact",
                "reader::tests::control_transfer::native_control_actor",
                "--nocapture",
            ])
            .env("PROVENANCE_CONTROL_ROOT", fixture.root.path())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let output = bounded_child(child, Instant::now() + HANG);
    fixture.completed(&output);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("1 passed; 0 failed; 0 ignored"), "{output:?}");
    assert!(stdout.contains("CONTROL-ORIGINALS-POSTASSERT"), "{output:?}");
}
#[test]
fn native_control_actor() {
    let Some(root) = std::env::var_os("PROVENANCE_CONTROL_ROOT") else {
        return;
    };
    println!("{STARTED}");
    std::io::stdout().flush().unwrap();
    let root = PathBuf::from(root);
    let helper = std::env::current_exe().unwrap();
    let socket = root.join("c.sock");
    let listener = UnixListener::bind(&socket).unwrap();
    fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).unwrap();
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
        socket_hex: hex(socket.as_os_str().as_bytes()),
        socket: identity(&fs::symlink_metadata(&socket).unwrap()),
    };
    fs::write(
        root.join("instances/book.json"),
        Book { version: 1, instances: vec![record] }.encode().unwrap(),
    )
    .unwrap();
    let deadline = Instant::now() + HANG;
    let store = Store::open_at(&root).unwrap();
    let non_listener = UnixStream::pair().unwrap();
    assert!(
        store.pin_current_listener(non_listener.0.as_fd(), deadline).is_err(),
        "a socket alone is not a listener"
    );
    assert!(
        store
            .pin_current_listener(File::open(root.join("lock")).unwrap().as_fd(), deadline)
            .is_err()
    );
    let pin = Arc::new(store.pin_current_listener(listener.as_fd(), deadline).unwrap());
    let transfer = pin.control_transfer(deadline).unwrap();
    let originals = transfer.duplicate_descriptions(deadline).unwrap();
    let anchor_fd = originals[8].as_raw_fd();
    let before = unsafe { libc::lseek(originals[5].as_raw_fd(), 0, libc::SEEK_CUR) };
    let observed_image = originals[5].try_clone().unwrap();
    let imported = pin.receive_original_control(originals, deadline).unwrap();
    assert!(
        unsafe { libc::fcntl(anchor_fd, libc::F_GETFD) } >= 0,
        "import closed its actual original anchor"
    );
    let retained_connection = imported.connect(deadline).unwrap();
    assert_eq!(
        before,
        unsafe { libc::lseek(observed_image.as_raw_fd(), 0, libc::SEEK_CUR) },
        "import changed shared image offset"
    );
    imported.validate(deadline).unwrap();
    assert_eq!(imported.host_pid(), std::process::id());
    assert_eq!(imported.original_store_path(), root);
    // Named read permission can disappear without revoking the already held
    // original. Validation must read the actual retained version, not reopen it.
    fs::set_permissions(root.join("version.json"), fs::Permissions::from_mode(0o000)).unwrap();
    assert!(fs::File::open(root.join("version.json")).is_err());
    imported.validate(deadline).unwrap();
    fs::set_permissions(root.join("version.json"), fs::Permissions::from_mode(0o600)).unwrap();
    let mut wrong = transfer.duplicate_descriptions(deadline).unwrap();
    wrong.swap(0, 1);
    assert!(pin.receive_original_control(wrong, deadline).is_err());
    let mut wrong = transfer.duplicate_descriptions(deadline).unwrap();
    let pair = UnixStream::pair().unwrap();
    wrong[8] = OwnedFd::from(pair.0);
    assert!(
        pin.receive_original_control(wrong, deadline).is_err(),
        "unnamed peer substituted for original listener"
    );
    let originals = transfer.duplicate_descriptions(deadline).unwrap();
    fs::rename(root.join("version.json"), root.join("version.saved")).unwrap();
    write(&root.join("version.json"), b"{\"version\":1}");
    assert!(
        pin.receive_original_control(originals, deadline).is_err(),
        "equal-byte replacement accepted"
    );
    assert!(transfer.validate(deadline).is_err());
    fs::remove_file(root.join("version.json")).unwrap();
    fs::rename(root.join("version.saved"), root.join("version.json")).unwrap();
    assert!(
        transfer.duplicate_descriptions(deadline).is_err(),
        "late repair cleared failed transfer"
    );
    drop(observed_image);
    drop(imported);
    assert!(
        unsafe { libc::fcntl(anchor_fd, libc::F_GETFD) } >= 0,
        "reconnected Host lost the original anchor owner"
    );
    let retained_pin = retained_connection.into_helper(deadline).unwrap();
    assert!(unsafe { libc::fcntl(anchor_fd, libc::F_GETFD) } >= 0);
    drop(retained_pin);
    assert_eq!(
        unsafe { libc::fcntl(anchor_fd, libc::F_GETFD) },
        -1,
        "last original pin did not close its actual anchor"
    );
    drop(transfer);
    drop(pin);
    drop(store);
    println!("CONTROL-ORIGINALS-POSTASSERT");
}
