//! Private roots for the three live Trustd release smokes.
//!
//! A Darwin default temporary parent can consume 56 canonical path bytes.
//! Trustd also binds in a private `.td-.../s` child before publishing its socket.
//! Honor the caller's temporary directory when both names fit. An arbitrarily
//! long configured parent needs a fresh owner-private root in the short system
//! namespace; shortening only our prefix cannot make that parent fit.

#[derive(Clone, Copy, Debug)]
pub(crate) enum Purpose {
    SelfVerify,
    EvidenceCollector,
    ProductProof,
}

pub(crate) fn create(purpose: Purpose) -> std::io::Result<tempfile::TempDir> {
    let prefix = match purpose {
        Purpose::SelfVerify => "sv-",
        Purpose::EvidenceCollector => "pc-",
        Purpose::ProductProof => "pp-",
    };
    let mut builder = tempfile::Builder::new();
    builder.prefix(prefix);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        // The default tempfile directory mode is 0777 filtered by the umask.
        // Request privacy atomically, before any caller's defensive chmod.
        builder.permissions(std::fs::Permissions::from_mode(0o700));
    }
    let root = builder.tempdir()?;
    #[cfg(unix)]
    if !private_bind_paths_fit(root.path())? {
        // Allocate the configured parent first: missing, inaccessible and
        // otherwise invalid TMPDIR inputs must retain their original error.
        // Only the proven pathname-capacity failure selects a shorter parent.
        drop(root);
        let root = builder.tempdir_in("/tmp")?;
        if !private_bind_paths_fit(root.path())? {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "private Trustd smoke paths exceed the Unix socket pathname capacity",
            ));
        }
        return Ok(root);
    }
    Ok(root)
}

#[cfg(unix)]
fn private_bind_paths_fit(root: &std::path::Path) -> std::io::Result<bool> {
    let root = std::fs::canonicalize(root)?;
    Ok(canonical_private_bind_paths_fit(&root))
}

#[cfg(unix)]
fn canonical_private_bind_paths_fit(root: &std::path::Path) -> bool {
    use std::os::unix::ffi::OsStrExt as _;

    // Match the private coordinator's `.td-{pid:x}-{nonce:x}-{sequence:x}/s`
    // layout, reserving the full integer widths rather than today's small PID
    // and sequence. Its bind path and the published name must both fit, even
    // after resolving /tmp or a caller-selected symlink to its longer target.
    let staging = root.join(format!(".td-{:x}-{:x}-{:x}/s", u32::MAX, u128::MAX, usize::MAX,));
    let published = root.join("trustd.sock");
    // SAFETY: all-zero bytes are valid for this plain C address structure.
    let capacity = unsafe { std::mem::zeroed::<libc::sockaddr_un>() }.sun_path.len();
    [staging, published].iter().all(|path| path.as_os_str().as_bytes().len() < capacity)
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
mod tests {
    use std::fs;
    use std::io::{BufRead, BufReader, Write};
    use std::os::unix::ffi::OsStrExt as _;
    use std::os::unix::fs::{
        DirBuilderExt as _, FileTypeExt as _, MetadataExt as _, PermissionsExt as _,
    };
    use std::os::unix::net::UnixStream;
    use std::path::{Path, PathBuf};
    use std::process::{Child, Command, Stdio};
    use std::time::{Duration, Instant};

    use super::{Purpose, create};
    use crate::process_lifecycle::{Ownership, StopCause, spawn_owned, stop_tree};

    const CHILD_CASE: &str = "smoke_socket_root::tests::real_coordinator_child";
    const PURPOSE_ENV: &str = "TRUST_TEST_SMOKE_SOCKET_PURPOSE";
    const MARKER_ENV: &str = "TRUST_TEST_SMOKE_SOCKET_MARKER";
    // A hang detector for the fixture, not a production readiness budget.
    const HANG: Duration = Duration::from_secs(60);

    struct OwnedDaemon {
        child: Child,
        _ownership: Ownership,
        reaped: bool,
    }

    impl OwnedDaemon {
        fn finish(mut self) {
            let outcome =
                stop_tree(self.child.id(), StopCause::Released).expect("stop owned daemon");
            self.child.wait().expect("reap owned daemon");
            self.reaped = true;
            assert_eq!(outcome.left, 0, "owned daemon descendants must drain");
        }
    }

    impl Drop for OwnedDaemon {
        fn drop(&mut self) {
            if !self.reaped {
                let _ = stop_tree(self.child.id(), StopCause::Released);
                let _ = self.child.wait();
            }
        }
    }

    #[test]
    fn real_coordinator_child() {
        let Some(purpose) = std::env::var_os(PURPOSE_ENV) else { return };
        let purpose = match purpose.to_str() {
            Some("self-verify") => Purpose::SelfVerify,
            Some("collector") => Purpose::EvidenceCollector,
            Some("product-proof") => Purpose::ProductProof,
            _ => panic!("unknown smoke root fixture purpose"),
        };
        let selected_temp = PathBuf::from(std::env::var_os("TMPDIR").expect("selected child temp"));
        // This dedicated child runs only this fixture. Exercise allocation
        // under a permissive umask without mutating the parent test process.
        unsafe { libc::umask(0) };
        let root = create(purpose).expect("create production smoke root");
        assert_eq!(fs::metadata(root.path()).unwrap().permissions().mode() & 0o777, 0o700);
        // Match the unchanged production callers before entering Trustd.
        fs::set_permissions(root.path(), fs::Permissions::from_mode(0o700))
            .expect("make smoke root owner-private");
        let expected_parent = if super::canonical_private_bind_paths_fit(
            &selected_temp.join(root.path().file_name().unwrap()),
        ) {
            selected_temp.clone()
        } else {
            fs::canonicalize("/tmp").unwrap()
        };
        assert_eq!(
            fs::canonicalize(root.path()).unwrap().parent(),
            Some(expected_parent.as_path())
        );
        assert_eq!(fs::metadata(root.path()).unwrap().permissions().mode() & 0o777, 0o700);
        let socket = root.path().join("trustd.sock");
        fs::write(
            std::env::var_os(MARKER_ENV).expect("owned socket marker"),
            socket.as_os_str().as_bytes(),
        )
        .expect("publish fixture socket path");
        // Exercise the real daemon entry point, including canonical parent
        // checks, stable ownership, private staged bind/rename and DIRTY epoch.
        trust_router::coordinator::serve(&socket).expect("serve real coordinator smoke");
    }

    fn assert_real_coordinator_at_temp_length(purpose: &str, length: usize) {
        // This fixture selects a private synthetic TMPDIR in its child only.
        // Production create() still uses the caller's original temp selection.
        // Use the same short trusted sticky namespace as Trustd's own tests so
        // the synthetic canonical parent has the requested byte length.
        let fixture = tempfile::Builder::new().prefix("ts-").tempdir_in("/tmp").unwrap();
        let fixture_root = fs::canonicalize(fixture.path()).unwrap();
        let padding = length
            .checked_sub(fixture_root.as_os_str().as_bytes().len() + 1)
            .expect("short fixture parent leaves room for a Darwin-length temp base");
        let selected_temp = fixture_root.join("b".repeat(padding));
        fs::DirBuilder::new().mode(0o700).create(&selected_temp).unwrap();
        assert_eq!(selected_temp.as_os_str().as_bytes().len(), length);
        let executable = std::env::current_exe().unwrap();

        let marker = fixture_root.join(format!("{purpose}.socket"));
        let log = fixture_root.join(format!("{purpose}.log"));
        let output = fs::File::create(&log).unwrap();
        let mut command = Command::new(&executable);
        command
            .args(["--exact", CHILD_CASE, "--nocapture", "--test-threads=1"])
            .env(PURPOSE_ENV, purpose)
            .env(MARKER_ENV, &marker)
            .env("TMPDIR", &selected_temp)
            .env("TMP", &selected_temp)
            .env("TEMP", &selected_temp)
            .stdin(Stdio::null())
            .stdout(output.try_clone().unwrap())
            .stderr(output);
        let (child, ownership) = spawn_owned(&mut command).expect("start owned real coordinator");
        let mut daemon = OwnedDaemon { child, _ownership: ownership, reaped: false };
        let deadline = Instant::now() + HANG;
        let socket = loop {
            assert!(
                !crate::bounded_process::exited_without_reaping(&mut daemon.child).unwrap(),
                "{purpose} real coordinator exited: {}",
                fs::read_to_string(&log).unwrap()
            );
            if let Ok(path) = fs::read_to_string(&marker) {
                if !path.is_empty() {
                    let socket = PathBuf::from(path);
                    assert!(super::private_bind_paths_fit(socket.parent().unwrap()).unwrap());
                    if let Ok(mut stream) = UnixStream::connect(&socket) {
                        stream.set_read_timeout(Some(HANG)).unwrap();
                        stream.write_all(b"PING\n").unwrap();
                        let mut answer = String::new();
                        BufReader::new(stream).read_line(&mut answer).unwrap();
                        assert_eq!(answer, "PONG\n");
                        break socket;
                    }
                }
            }
            assert!(
                Instant::now() < deadline,
                "{purpose} real coordinator did not bind: {}",
                fs::read_to_string(&log).unwrap()
            );
            std::thread::sleep(Duration::from_millis(10));
        };
        let metadata = fs::symlink_metadata(&socket).unwrap();
        assert!(metadata.file_type().is_socket());
        assert_eq!(metadata.uid(), unsafe { libc::geteuid() });
        assert_eq!(metadata.permissions().mode() & 0o777, 0o600);
        assert_eq!(
            fs::metadata(socket.parent().unwrap()).unwrap().permissions().mode() & 0o777,
            0o700
        );
        let canonical_root = fs::canonicalize(socket.parent().unwrap()).unwrap();
        if length == 24 {
            assert_eq!(canonical_root.parent(), Some(selected_temp.as_path()));
        } else if length == 160 {
            assert_ne!(canonical_root.parent(), Some(selected_temp.as_path()));
            assert_eq!(canonical_root.parent(), Some(fs::canonicalize("/tmp").unwrap().as_path()));
        }
        assert!(Path::new(&socket).as_os_str().as_bytes().len() < 104);
        daemon.finish();
        // The fixture daemon is terminated externally, so its TempDir cannot
        // run Drop. Remove only the private root whose socket identity and
        // owner/mode were checked above, including when it used the fallback.
        match fs::remove_file(&socket) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => panic!("remove owned fixture socket: {error}"),
        }
        fs::remove_dir(socket.parent().unwrap()).expect("remove owned fixture smoke root");
    }

    #[test]
    fn self_verify_factory_binds_real_coordinator_at_macos_default_temp_length() {
        assert_real_coordinator_at_temp_length("self-verify", 56);
    }

    #[test]
    fn collector_factory_binds_real_coordinator_at_macos_default_temp_length() {
        assert_real_coordinator_at_temp_length("collector", 56);
    }

    #[test]
    fn product_proof_factory_binds_real_coordinator_at_macos_default_temp_length() {
        assert_real_coordinator_at_temp_length("product-proof", 56);
    }

    #[test]
    fn every_smoke_factory_binds_real_coordinator_with_oversized_temp_parent() {
        for purpose in ["self-verify", "collector", "product-proof"] {
            assert_real_coordinator_at_temp_length(purpose, 160);
        }
    }

    #[test]
    fn every_smoke_factory_preserves_a_short_configured_parent() {
        for purpose in ["self-verify", "collector", "product-proof"] {
            assert_real_coordinator_at_temp_length(purpose, 24);
        }
    }

    #[test]
    fn invalid_configured_parent_does_not_fall_back() {
        const CHILD_ENV: &str = "TRUST_TEST_MISSING_SMOKE_TEMP";
        if std::env::var_os(CHILD_ENV).is_some() {
            let error = create(Purpose::SelfVerify).unwrap_err();
            assert_eq!(error.kind(), std::io::ErrorKind::NotFound);
            return;
        }
        let fixture = tempfile::Builder::new().prefix("ts-").tempdir_in("/tmp").unwrap();
        let missing = fixture.path().join("missing-parent-".repeat(12));
        let output = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "smoke_socket_root::tests::invalid_configured_parent_does_not_fall_back",
                "--nocapture",
            ])
            .env(CHILD_ENV, "1")
            .env("TMPDIR", &missing)
            .env("TMP", &missing)
            .env("TEMP", &missing)
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        assert!(!missing.exists());
    }
}
