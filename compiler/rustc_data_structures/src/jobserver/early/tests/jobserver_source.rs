//! Compile the maintained compiler jobserver implementation and its original
//! unit controls. This is not a whole-compiler or authenticated host fixture.
#![feature(trust_process_inherit_fds)]

// Trust: this test root sits under tests/, as tidy's `unit_tests` check requires, so each
// #[path] below climbs one more directory to reach the same file.
#[path = "../../../jobserver.rs"]
mod jobserver;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const WORKLOAD_MEMBER_PROTOCOL_MARKER: [u8; 64] =
    trust_resource_controller::workload::WORKLOAD_MEMBER_PROTOCOL_MARKER;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "../../../../../rustc/src/workload_protocol.rs"]
mod workload_protocol;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn actual_frontend_declaration_source_is_in_the_held_readonly_member_section() {
    use std::os::unix::fs::PermissionsExt;
    use std::time::{Duration, Instant};

    use sha2::{Digest, Sha256};
    use trust_resource_provenance::program::HeldProgram;

    // This is an actual compiled declaration component, never a compiler SDK,
    // registered member, resource grant, execution or proof fixture.
    let image = std::env::current_exe().unwrap().canonicalize().unwrap();
    let directory = tempfile::Builder::new()
        .prefix("member-declaration-")
        .tempdir_in(image.parent().unwrap())
        .unwrap();
    let root = directory.path().join("inputs");
    std::fs::create_dir(&root).unwrap();
    std::fs::create_dir(root.join("bin")).unwrap();
    std::fs::create_dir(root.join("lib")).unwrap();
    let program = root.join("bin/declaration-fixture");
    std::fs::copy(&image, &program).unwrap();
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o555)).unwrap();
    let hash: [u8; 32] = Sha256::digest(std::fs::read(&program).unwrap()).into();
    let deadline = Instant::now() + Duration::from_secs(30);
    let held = HeldProgram::open(&root, &program, &hash, deadline).unwrap();
    held.require_workload_member_protocol_marker(&WORKLOAD_MEMBER_PROTOCOL_MARKER, deadline)
        .unwrap();
    assert!(
        held.require_workload_protocol_marker(
            &trust_resource_controller::workload::WORKLOAD_PROTOCOL_MARKER,
            deadline
        )
        .is_err()
    );
    let mut wrong = WORKLOAD_MEMBER_PROTOCOL_MARKER;
    wrong[63] ^= 1;
    assert!(held.require_workload_member_protocol_marker(&wrong, deadline).is_err());
}
