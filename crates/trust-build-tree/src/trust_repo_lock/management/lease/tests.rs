use std::fs;
use std::process::Command;
use std::time::Duration;

use super::*;
use crate::trust_repo_lock::management::{Acquire, Kind};

fn request(token: Option<String>) -> Acquire {
    Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "native durable lease regression".into(),
        contract: "retain original exclusion through work".into(),
        wait: Duration::ZERO,
        inherited_token: token,
        break_reason: None,
    }
}

fn grant(root: &std::path::Path, token: Option<String>) -> Lease {
    match Manager::open(root).unwrap().acquire_lease(&request(token)).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("native test root unexpectedly busy"),
    }
}

#[test]
fn native_lease_owns_original_exclusion_and_refuses_a_forged_borrow() {
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    assert!(!lease.is_borrowed());
    lease.check_current().unwrap();
    assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    assert!(matches!(
        Manager::open(root.path()).unwrap().acquire_lease(&request(Some("forged".into()))).unwrap(),
        LeaseAcquisition::Busy(_)
    ));
    drop(lease);
    assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn native_lease_borrows_actual_live_ancestor_without_releasing_it() {
    const ROOT: &str = "TRUST_TEST_NATIVE_LEASE_ANCESTOR_ROOT";
    const TOKEN: &str = "TRUST_TEST_NATIVE_LEASE_ANCESTOR_TOKEN";
    const NAME: &str = "trust_repo_lock::management::lease::tests::native_lease_borrows_actual_live_ancestor_without_releasing_it";
    if let Some(root) = std::env::var_os(ROOT) {
        let root = std::path::Path::new(&root);
        let lease = grant(root, Some(std::env::var(TOKEN).unwrap()));
        assert!(lease.is_borrowed());
        lease.check_current().unwrap();
        drop(lease);
        assert!(!Manager::open(root).unwrap().status().unwrap().is_free());
        return;
    }
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", NAME, "--nocapture"])
        .env(ROOT, root.path())
        .env(TOKEN, &lease.token)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    lease.check_current().unwrap();
    drop(lease);
    assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn native_lease_rejects_named_external_owner() {
    let root = tempfile::tempdir().unwrap();
    let mut request = request(None);
    request.owner_pid = 2;
    assert!(Manager::open(root.path()).unwrap().acquire_lease(&request).is_err());
    assert!(!root.path().join(".trust-build-lock").exists());
}

#[test]
fn native_lease_never_releases_a_replaced_holder_even_with_the_original_token() {
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let holder = root.path().join(".trust-build-lock");
    let original = fs::read(holder.join("info")).unwrap();
    fs::rename(&holder, root.path().join("retained-original")).unwrap();
    fs::create_dir(&holder).unwrap();
    fs::write(holder.join("info"), &original).unwrap();
    assert!(lease.check_current().is_err());
    drop(lease);
    assert_eq!(fs::read(holder.join("info")).unwrap(), original);
    assert!(root.path().join("retained-original/info").is_file());
}

#[cfg(target_os = "macos")]
struct LiveNonWriter(std::process::Child);

#[cfg(target_os = "macos")]
impl LiveNonWriter {
    fn spawn() -> Self {
        Self(
            Command::new("/bin/cat")
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::null())
                .spawn()
                .unwrap(),
        )
    }
}

#[cfg(target_os = "macos")]
impl Drop for LiveNonWriter {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

#[cfg(target_os = "macos")]
#[test]
fn native_lease_recovers_transient_process_observation_only_after_actual_kernel_read() {
    use crate::trust_repo_lock::management::process;
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let child = LiveNonWriter::spawn();
    let fault = process::read_fault(child.0.id(), 2);
    let observed = Manager::open(root.path()).unwrap().status().unwrap();
    assert_eq!(observed.holder.unwrap().token, lease.token);
    assert!(process::present(child.0.id()).unwrap());
    assert_eq!(process::read(child.0.id()).unwrap().name, "cat");
    drop(fault);
    lease.check_current().unwrap();
    drop(lease);
    assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[cfg(target_os = "macos")]
#[test]
fn native_lease_persistent_process_observation_refusal_keeps_original_exclusion() {
    use crate::trust_repo_lock::management::process;
    let root = tempfile::tempdir().unwrap();
    let lease = grant(root.path(), None);
    let token = lease.token.clone();
    let original = fs::read(root.path().join(".trust-build-lock/info")).unwrap();
    let child = LiveNonWriter::spawn();
    let fault = process::read_fault(child.0.id(), usize::MAX);
    assert!(Manager::open(root.path()).unwrap().release(&token).is_err());
    drop(lease);
    assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), original);
    assert!(process::present(child.0.id()).unwrap());
    drop(fault);
    assert_eq!(Manager::open(root.path()).unwrap().release(&token).unwrap(), Release::Released);
}
