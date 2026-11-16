use std::process::{Child, Command};

fn birth(value: u64) -> String {
    if cfg!(target_os = "macos") {
        format!("darwin:1:{value}")
    } else {
        format!("linux:00000000-0000-0000-0000-000000000000:{value}")
    }
}

use serde_json::json;

use super::*;
use crate::trust_repo_lock::management::process;

fn eventually_available(mut observe: impl FnMut() -> io::Result<bool>) -> bool {
    // A concurrent spawn may still own a forked registration-lock description
    // until exec closes it. Busy remains unavailable in production; these
    // positive retirement assertions require actual availability within 5s.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        if observe().unwrap() {
            return true;
        }
        if std::time::Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
}

struct Actor(Child);
impl Actor {
    fn start() -> Self {
        Self(Command::new("/bin/sleep").arg("30").spawn().unwrap())
    }
}
impl Drop for Actor {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn record(root: &Path, pid: u32, birth: &str, paths: &[PathBuf]) -> serde_json::Value {
    json!({
        "schema":1, "adopted":true, "pid":pid,
        "identity":{"pid":pid,"uid":unsafe{libc::geteuid()},"birth":birth,"executable":"/bin/sleep"},
        "pool":root,"worktree":null,"leases":paths,
    })
}
fn write(registry: &Path, value: &serde_json::Value) -> PathBuf {
    let path = registry.join("original.json");
    crate::owner_only::write(&path, &serde_json::to_vec(value).unwrap());
    path
}
fn fixture() -> (tempfile::TempDir, PathBuf, PathBuf) {
    let root = crate::owner_only::tempdir();
    let registry = root.path().join("adopted");
    crate::owner_only::create_dir(&registry);
    let path = root.path().join("slot-0");
    crate::launcher_file::write(&path, &[]);
    let path = fs::canonicalize(path).unwrap();
    (root, registry, path)
}

#[test]
fn actual_process_birth_keeps_debt_until_original_process_is_reaped() {
    let (root, registry, lease) = fixture();
    let mut actor = Actor::start();
    let birth = process::live_adoption_birth(actor.0.id()).unwrap().unwrap();
    let original =
        write(&registry, &record(root.path(), actor.0.id(), &birth, std::slice::from_ref(&lease)));
    assert!(!available(&registry, &lease).unwrap());
    assert!(original.is_file());
    actor.0.kill().unwrap();
    actor.0.wait().unwrap();
    assert!(eventually_available(|| available(&registry, &lease)));
    assert!(!original.exists());
}

#[test]
fn exec_uid_diagnostics_do_not_retire_matching_birth_and_unknown_keeps_debt() {
    let (root, registry, lease) = fixture();
    let mut value = record(root.path(), 17, &birth(2), std::slice::from_ref(&lease));
    value["identity"]["uid"] = json!(u32::MAX);
    value["identity"]["executable"] = json!("/a/previous/executable");
    let original = write(&registry, &value);
    assert!(!available_with(&registry, &lease, |_| Ok(Some(birth(2)))).unwrap());
    assert!(
        !available_with(&registry, &lease, |_| Err(io::ErrorKind::PermissionDenied.into()))
            .unwrap()
    );
    assert!(original.exists());
    assert!(eventually_available(|| available_with(&registry, &lease, |_| Ok(Some(birth(3))))));
    assert!(!original.exists());
}

#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::adopted::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            actual_process_birth_keeps_debt_until_original_process_is_reaped();
            exec_uid_diagnostics_do_not_retire_matching_birth_and_unknown_keeps_debt();
        },
    );
}

#[test]
fn invalid_unknown_and_unrelated_adoptions_preserve_the_complete_claim() {
    let (root, registry, lease) = fixture();
    let other = root.path().join("slot-1");
    crate::launcher_file::write(&other, &[]);
    let other = fs::canonicalize(other).unwrap();
    let good = record(root.path(), 17, &birth(2), &[other]);
    write(&registry, &good);
    assert!(
        available_with(&registry, &lease, |_| panic!("unrelated birth must not be queried"))
            .unwrap()
    );
    for mutate in [
        |v: &mut serde_json::Value| v["schema"] = json!(2),
        |v: &mut serde_json::Value| v["adopted"] = json!(false),
        |v: &mut serde_json::Value| v["identity"]["pid"] = json!(18),
        |v: &mut serde_json::Value| v["leases"] = json!([]),
        |v: &mut serde_json::Value| v["leases"] = json!(["relative"]),
        |v: &mut serde_json::Value| v["worktree"] = json!("/missing/whole/claim"),
        |v: &mut serde_json::Value| v["identity"]["birth"] = json!("unknown birth encoding"),
    ] {
        let mut invalid = good.clone();
        mutate(&mut invalid);
        write(&registry, &invalid);
        assert!(
            !available_with(&registry, &lease, |_| panic!("malformed record is a barrier"))
                .unwrap()
        );
    }
    fs::write(registry.join("original.json"), b"{truncated").unwrap();
    assert!(!available_with(&registry, &lease, |_| panic!("unknown is a barrier")).unwrap());
}

#[test]
fn registration_contention_never_blocks_while_holding_reverse_order_locks() {
    let (_root, registry, lease) = fixture();
    let directory = Directory::open(&registry).unwrap();
    let registration = directory.open_file("registration.lock", true).unwrap();
    assert!(try_exclusive(&registration).unwrap());
    assert!(!available(&registry, &lease).unwrap());
    drop(registration);
    assert!(eventually_available(|| available(&registry, &lease)));
}

#[test]
fn disappeared_claim_member_preserves_live_debt_and_does_not_block_known_dead_retirement() {
    let (root, registry, lease) = fixture();
    let tree = root.path().join("old-worktree");
    // The lock sits where scripts/build-slot puts it, in the checkout's Git
    // directory: `.git`, not a bare "git", which names a program to a reader.
    fs::create_dir_all(tree.join(".git")).unwrap();
    let lock = tree.join(".git/build-slot.lock");
    fs::write(&lock, []).unwrap();
    let lock = fs::canonicalize(lock).unwrap();
    let value = record(root.path(), 17, &birth(2), &[lease.clone(), lock]);
    let original = write(&registry, &value);
    fs::remove_dir_all(tree).unwrap();
    assert!(!available_with(&registry, &lease, |_| Ok(Some(birth(2)))).unwrap());
    assert!(original.exists());
    assert!(eventually_available(|| available_with(&registry, &lease, |_| Ok(None))));
    assert!(!original.exists());
}

#[test]
fn replaced_or_changed_record_is_never_deleted_as_the_dead_original() {
    for replace in [false, true] {
        let (root, registry, lease) = fixture();
        let value = record(root.path(), 17, &birth(2), std::slice::from_ref(&lease));
        let path = write(&registry, &value);
        let result = available_with(&registry, &lease, |_| {
            if replace {
                let replacement = registry.join("replacement");
                crate::owner_only::write(&replacement, b"replacement");
                fs::rename(replacement, &path).unwrap();
            } else {
                fs::write(&path, b"changed original").unwrap();
            }
            Ok(None)
        });
        assert!(result.is_err());
        assert_eq!(
            fs::read(path).unwrap(),
            if replace { b"replacement".to_vec() } else { b"changed original".to_vec() }
        );
    }
}
