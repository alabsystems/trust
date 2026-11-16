//! Real private native lease semantics only. These fixtures create no live
//! Host/SDK member and cannot qualify an opaque controller transfer.
use std::fs::OpenOptions;
use std::time::{Duration, Instant};

use super::*;

const TEST: &str = "unix::workload_original_tests::original_continuation_is_close_only_and_failed_import_never_refunds_origin";
const ACTOR: &str = "TRUST_NATIVE_ORIGINAL_CPU_FILE_TEST";
const MARKER: &str = "NATIVE_ORIGINAL_CPU_FILE_ASSERTIONS_PASSED";

struct Actor {
    child: std::process::Child,
    readers: Vec<std::thread::JoinHandle<io::Result<Vec<u8>>>>,
}
impl Drop for Actor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        for reader in self.readers.drain(..) {
            let _ = reader.join();
        }
    }
}
fn reader(
    mut pipe: impl io::Read + Send + 'static,
) -> std::thread::JoinHandle<io::Result<Vec<u8>>> {
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        io::Read::take(&mut pipe, 1024 * 1024 + 1).read_to_end(&mut bytes)?;
        Ok(bytes)
    })
}
struct Fixture(Option<tempfile::TempDir>);
impl Drop for Fixture {
    fn drop(&mut self) {
        if std::thread::panicking()
            && let Some(root) = self.0.take()
        {
            eprintln!("retained native original CPU input={}", root.keep().display());
        }
    }
}

#[test]
fn original_continuation_is_close_only_and_failed_import_never_refunds_origin() {
    if std::env::var_os(ACTOR).is_none() {
        // Create the private pool only in this exact child. Other parallel
        // tests' spawns cannot copy its live originals and delay final close.
        // The child itself holds a copy of every descriptor of this process,
        // other tests' leases included, until its exec.
        let _fixture = crate::tests::kernel_fixture();
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", TEST, "--nocapture"])
            .env(ACTOR, "1")
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        let readers =
            vec![reader(child.stdout.take().unwrap()), reader(child.stderr.take().unwrap())];
        let mut actor = Actor { child, readers };
        let deadline = Instant::now() + Duration::from_secs(30);
        let status = loop {
            if let Some(status) = actor.child.try_wait().unwrap() {
                break status;
            }
            assert!(
                Instant::now() < deadline,
                "native original CPU actor timed out; Drop kills/reaps exact child"
            );
            std::thread::sleep(Duration::from_millis(5));
        };
        let stdout = actor.readers.remove(0).join().unwrap().unwrap();
        let stderr = actor.readers.remove(0).join().unwrap().unwrap();
        assert!(stdout.len() <= 1024 * 1024 && stderr.len() <= 1024 * 1024);
        let stdout = String::from_utf8(stdout).unwrap();
        let stderr = String::from_utf8(stderr).unwrap();
        assert!(status.success(), "stdout={stdout}; stderr={stderr}");
        assert!(
            stdout.contains("running 1 test") && stdout.contains("1 passed; 0 failed"),
            "{stdout}"
        );
        assert_eq!(stderr.matches(MARKER).count(), 1, "native postconditions missing: {stderr}");
        return;
    }
    let root = crate::tests::private_tempdir();
    let path = root.path().to_owned();
    let _fixture = Fixture(Some(root));
    let pool = Pool::open_in(&path, NonZeroU32::new(1).unwrap()).unwrap();
    let owner = Owner::current(None);
    let original = pool.try_acquire(owner).unwrap().unwrap();
    let slot = original.slot();
    assert!(pool.try_acquire(owner).unwrap().is_none());
    assert!(
        continue_original_workload_file(slot + 1, original.try_clone().unwrap().into_file())
            .is_err()
    );
    assert!(
        pool.try_acquire(owner).unwrap().is_none(),
        "failed import returned the original guard"
    );
    let readonly = OpenOptions::new().read(true).open(pool.path().join(slot_name(slot))).unwrap();
    assert!(continue_original_workload_file(slot, readonly).is_err());
    assert!(pool.try_acquire(owner).unwrap().is_none());
    let continued =
        continue_original_workload_file(slot, original.try_clone().unwrap().into_file()).unwrap();
    assert_eq!(continued.slot(), slot);
    assert_eq!(continued.owner(), original.owner());
    drop(original);
    assert!(pool.try_acquire(owner).unwrap().is_none(), "continued original unlocked early");
    let final_original = continued.try_clone().unwrap();
    drop(continued);
    assert!(
        pool.try_acquire(owner).unwrap().is_none(),
        "an actual original copy still owns the guard"
    );
    drop(final_original);
    let available = pool
        .try_acquire(owner)
        .unwrap()
        .expect("last original close releases exactly one actual native unit");
    assert_eq!(available.slot(), slot);
    drop(available);
    eprintln!("{MARKER}");
}
