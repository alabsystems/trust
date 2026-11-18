use std::os::unix::fs::symlink;
// Only the tests compiled under the `native-exec` gate below use these.
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
use std::time::{Duration, Instant};

use super::super::{InheritedFixedClaim, PreparedFixedCommand};
use super::*;

fn prepare_member_fixture() -> (tempfile::TempDir, PreparedFixedCommand, PathBuf) {
    let (root, claim) = super::super::tests::fixture();
    let claim = claim.with_original_output_member().unwrap();
    let output = claim.output.as_ref().unwrap().root().unwrap().to_path_buf();
    let command = claim.prepare_command(Command::new("not-launched")).unwrap();
    (root, command, output)
}

fn retain(root: &Path, prepared: &PreparedFixedCommand) -> InheritedFixedClaim {
    InheritedFixedClaim::read(
        OsStr::new(&prepared.packet.as_raw_fd().to_string()),
        &root.join("legacy"),
        NonZeroU32::new(2).unwrap(),
    )
    .unwrap()
}

#[test]
fn original_output_member_rejects_escape_symlink_and_foreign_member() {
    let (root, prepared, output) = prepare_member_fixture();
    let original = retain(root.path(), &prepared);
    let foreign = tempfile::tempdir().unwrap();
    assert!(original.retain_original_output_directory(foreign.path()).is_err());
    assert!(original.retain_original_output_directory(&output.join("../escape")).is_err());
    symlink(foreign.path(), output.join("link")).unwrap();
    assert!(original.retain_original_output_directory(&output.join("link/target")).is_err());
    assert!(!foreign.path().join("target").exists());
    let target = original.retain_original_output_directory(&output.join("project/target")).unwrap();
    original.check_output_directory(&target).unwrap();
    let (other_root, other_prepared, other_output) = prepare_member_fixture();
    let other = retain(other_root.path(), &other_prepared);
    let other_target =
        other.retain_original_output_directory(&other_output.join("target")).unwrap();
    assert!(original.check_output_directory(&other_target).is_err());
    original.check_current().unwrap();
    other.check_current().unwrap();
}

#[test]
fn retained_target_replacement_refuses_before_another_dispatch() {
    let (root, prepared, output) = prepare_member_fixture();
    let original = retain(root.path(), &prepared);
    let path = output.join("project/target");
    let target = original.retain_original_output_directory(&path).unwrap();
    fs::rename(&path, output.join("project/retained-original")).unwrap();
    fs::create_dir(&path).unwrap();
    assert!(original.check_current().is_err());
    assert!(original.check_output_directory(&target).is_err());
}

#[test]
fn member_source_does_not_authorize_a_foreign_manifest_or_file_alias() {
    let (root, prepared, output) = prepare_member_fixture();
    let original = retain(root.path(), &prepared);
    let project = output.join("project");
    fs::create_dir(&project).unwrap();
    fs::write(project.join("Cargo.toml"), b"[workspace]\n").unwrap();
    let source = original.retain_existing_output_source_directory(&project).unwrap().unwrap();
    original.check_output_source_file(&source, OsStr::new("Cargo.toml")).unwrap();
    let foreign = tempfile::tempdir().unwrap();
    fs::create_dir(foreign.path().join(".git")).unwrap();
    fs::write(foreign.path().join("Cargo.toml"), b"[workspace]\n").unwrap();
    assert!(original.retain_existing_output_source_directory(foreign.path()).unwrap().is_none());
    assert!(
        original
            .check_nested(
                original.budget().unwrap(),
                Some(&foreign.path().join(".git/build-slot.lock")),
                false
            )
            .is_err()
    );
    fs::rename(project.join("Cargo.toml"), project.join("original-manifest")).unwrap();
    symlink(foreign.path().join("Cargo.toml"), project.join("Cargo.toml")).unwrap();
    assert!(original.check_output_source_file(&source, OsStr::new("Cargo.toml")).is_err());
    fs::remove_file(project.join("Cargo.toml")).unwrap();
    fs::hard_link(foreign.path().join("Cargo.toml"), project.join("Cargo.toml")).unwrap();
    assert!(original.check_output_source_file(&source, OsStr::new("Cargo.toml")).is_err());
    assert!(!foreign.path().join("target").exists());
    original.check_current().unwrap();
}

#[test]
fn appended_member_cannot_upgrade_an_actual_v1_record() {
    let (member_root, member_prepared, _) = prepare_member_fixture();
    let mut bytes = vec![0; member_prepared.packet.metadata().unwrap().len() as usize];
    member_prepared.packet.read_exact_at(&mut bytes, 0).unwrap();
    let (_, member) = decode_packet(&bytes).unwrap();
    let (root, claim) = super::super::tests::fixture();
    let prepared = claim.prepare_command(Command::new("not-launched")).unwrap();
    let mut v1 = vec![0; prepared.packet.metadata().unwrap().len() as usize];
    prepared.packet.read_exact_at(&mut v1, 0).unwrap();
    let original: Packet = serde_json::from_slice(&v1).unwrap();
    let bytes = serde_json::to_vec(&OutputPacket { version: 2, original, output: member.unwrap() })
        .unwrap();
    let mut packet = private_packet().unwrap();
    packet.write_all(&bytes).unwrap();
    packet.flush().unwrap();
    assert!(
        InheritedFixedClaim::read(
            OsStr::new(&packet.as_raw_fd().to_string()),
            &root.path().join("legacy"),
            NonZeroU32::new(2).unwrap()
        )
        .is_err()
    );
    // Failed membership never releases either actual original reservation.
    prepared.claim.check_current().unwrap();
    member_prepared.claim.check_current().unwrap();
    assert!(!crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
    assert!(!crate::admission::resources::tests::released(
        &member_root.path().join("legacy/slot-0")
    ));
}

#[test]
fn v2_member_binding_rejects_duplicate_record_fields_and_v1_decoder() {
    let (root, prepared, _) = prepare_member_fixture();
    let mut bytes = vec![0; prepared.packet.metadata().unwrap().len() as usize];
    prepared.packet.read_exact_at(&mut bytes, 0).unwrap();
    // V1's actual deny-unknown-fields decoder remains closed, including when
    // its ordinary fixed claim files are genuine and remain kernel-held.
    assert!(serde_json::from_slice::<Packet>(&bytes).is_err());
    let (mut packet, member) = decode_packet(&bytes).unwrap();
    let record = std::str::from_utf8(&packet.record).unwrap();
    packet.record = format!("{{\"cpu_budget\":1,{}", &record[1..]).into_bytes();
    assert!(packet_record(&packet, member.as_ref()).is_err());
    retain(root.path(), &prepared).check_current().unwrap();
}

#[test]
fn an_empty_original_worktree_population_is_not_a_v2_output_wildcard() {
    use crate::admission::{Coordinator, Requirements};
    for output_member in [false, true] {
        let root = crate::owner_only::tempdir();
        let namespace = root.path().join("legacy");
        crate::owner_only::create_dir(&namespace);
        let width = NonZeroU32::new(2).unwrap();
        let budget = NonZeroU32::new(1).unwrap();
        let pool = Pool::open_in(root.path(), width).unwrap();
        let mut coordinator = Coordinator::open(
            &namespace,
            &root.path().join("adopted"),
            Requirements::new(None, 2, 1, false, 0).unwrap(),
        )
        .unwrap();
        let claim = match coordinator.attempt_fixed_in_pool(Some(0), 1, budget, &pool).unwrap() {
            Attempt::Admitted(claim) => claim,
            _ => panic!("private actual no-worktree fixture was not admitted"),
        };
        let claim =
            if output_member { claim.with_original_output_member().unwrap() } else { claim };
        let prepared = claim.prepare_command(Command::new("not-launched")).unwrap();
        let original = retain(root.path(), &prepared);
        if output_member {
            assert!(original.check_nested(budget, None, false).is_err());
            let path =
                prepared.claim.output.as_ref().unwrap().root().unwrap().join("actual-target");
            let member = original.retain_original_output_directory(&path).unwrap();
            original.check_output_directory(&member).unwrap();
        } else {
            // Preserve V1's exact empty-set equality, without promoting it
            // into a V2 member or changing its original protocol grammar.
            original.check_nested(budget, None, false).unwrap();
        }
    }
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
const NAMESPACE: &str = "TRUST_FIXED_OUTPUT_TEST_NAMESPACE";
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
const RESULT: &str = "TRUST_FIXED_OUTPUT_TEST_RESULT";

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
fn actor_original() -> InheritedFixedClaim {
    let (packet, originals) = jobserver_utils::recover_fixed_claim(
        &std::env::var_os(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV).unwrap(),
    )
    .unwrap();
    InheritedFixedClaim::read_file(
        packet.into(),
        Path::new(&std::env::var_os(NAMESPACE).unwrap()),
        NonZeroU32::new(2).unwrap(),
        Some(originals),
    )
    .unwrap()
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub(crate) fn actor_root() {
    let mode = std::env::var_os(super::super::group::tests::MODE).unwrap();
    let refuse_cwd = mode == "native-output-cwd-refusal";
    let observed = mode == "native-output-observed-root";
    let closed = mode == "native-output-observed-closed";
    let alias = mode == "native-output-observed-alias";
    let original = actor_original();
    // SAFETY: this isolated actor imports its SAME actual inherited GNU
    // originals once, then pauses serially through the nested owning wait.
    let scheduler = unsafe { jobserver_utils::Jobserver::from_env() }.unwrap().unwrap();
    let project = PathBuf::from(std::env::var_os("TMPDIR").unwrap()).join("actual-project");
    fs::create_dir(&project).unwrap();
    // Only this isolated actor changes its process cwd; its helper endpoints
    // already use absolute original names and no parallel test body runs here.
    std::env::set_current_dir(&project).unwrap();
    let directory = original.original_output_cwd().unwrap().unwrap();
    if !refuse_cwd {
        let target = original.retain_original_output_directory(&project.join("target")).unwrap();
        original.check_output_directory(&target).unwrap();
    }
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", super::super::group::tests::ACTOR, "--nocapture", "--test-threads=1"])
        .env(super::super::group::tests::MODE, "native-output-leaf");
    if observed {
        command.env("TRUST_FIXED_OUTPUT_NOTICE_LEAF", "1");
    }
    for (name, _) in std::env::vars_os() {
        if name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_") {
            command.env_remove(name);
        }
    }
    let budget = original.budget().unwrap();
    // The refused builder is consumed/dropped. Retain the SAME server Arc so
    // these actual original descriptors remain live for the post-refusal check.
    let alias_keepalive = alias.then(|| scheduler.clone());
    let alias_writer = alias_keepalive
        .as_ref()
        .map(|scheduler| scheduler.pipe_descriptors().unwrap()[1].as_raw_fd());
    let alias_flags = alias_writer.map(|fd| {
        // SAFETY: observe only the fixture's SAME retained GNU writer.
        unsafe { (libc::fcntl(fd, libc::F_GETFL), libc::fcntl(fd, 74)) }
    });
    // SAFETY: same original fixed/GNU continuation; selected cwd is the SAME
    // descriptor-authenticated current member, console stdio is inherited,
    // and the actual outer group remains the descendant-retirement owner.
    let prepared = unsafe {
        original.prepare_nested_output_command(
            command,
            scheduler,
            budget,
            directory,
            false,
            Instant::now() + Duration::from_secs(10),
        )
    }
    .unwrap();
    if observed || closed || alias {
        use std::io::Read as _;
        let (mut reader, writer) = super::super::group::loaded_tests::pipe();
        let input = if let Some(fd) = alias_writer {
            drop(writer);
            super::super::group::ExecutionStartPipe::from_descriptor(OsStr::new(&fd.to_string()))
                .unwrap()
        } else {
            super::super::group::ExecutionStartPipe::from_owned_writer(writer).unwrap()
        };
        if alias {
            let error = prepared.with_execution_start(input).err().unwrap();
            assert!(error.to_string().contains("aliases original scheduling transport"), "{error}");
            let fd = alias_writer.unwrap();
            // SAFETY: reobserve the same original after the refused private mutation.
            assert_eq!(
                unsafe { (libc::fcntl(fd, libc::F_GETFL), libc::fcntl(fd, 74)) },
                alias_flags.unwrap()
            );
            assert!(!project.join("target/actual-body").exists());
            fs::write(std::env::var_os(RESULT).unwrap(), b"actual-notice-alias-refused").unwrap();
            return;
        }
        let prepared = prepared.with_execution_start(input).unwrap();
        if closed {
            drop(reader);
            let error = prepared.spawn().err().unwrap();
            assert_eq!(error.raw_os_error(), Some(libc::EPIPE));
            assert!(
                !project.join("target/actual-body").exists(),
                "closed observer let the body run"
            );
            let members =
                crate::trust_repo_lock::management::process::group_pids(std::process::id())
                    .unwrap();
            assert!(
                members.iter().all(|pid| *pid == std::process::id()),
                "unrun child was not retired"
            );
            fs::write(std::env::var_os(RESULT).unwrap(), b"actual-notice-closed-refused").unwrap();
            return;
        }
        assert!(prepared.spawn().unwrap().wait().unwrap().success());
        let mut frame = [0; 18];
        assert_eq!(reader.read(&mut frame).unwrap(), 17);
        assert_eq!(frame[0], b'S');
        let mut pid = [0; 8];
        pid.copy_from_slice(&frame[1..9]);
        let actual: u64 =
            fs::read_to_string(project.join("target/actual-pid")).unwrap().parse().unwrap();
        assert_eq!(u64::from_be_bytes(pid), actual);
        assert_eq!(fs::read(project.join("target/actual-body")).unwrap(), b"actual-member-body");
        fs::write(std::env::var_os(RESULT).unwrap(), b"actual-notice-complete").unwrap();
        return;
    }
    if refuse_cwd {
        let retained = project.with_file_name("retained-project");
        super::super::nested::replace_output_before_go(project.clone(), retained.clone());
        let error = prepared.spawn().err().unwrap();
        assert!(error.to_string().contains("original output member"), "{error}");
        assert!(
            !retained.join("target/actual-body").exists(),
            "replaced cwd let the stopped body run"
        );
        let members =
            crate::trust_repo_lock::management::process::group_pids(std::process::id()).unwrap();
        assert!(
            members.iter().all(|pid| *pid == std::process::id()),
            "refused native child was not retired"
        );
        fs::write(std::env::var_os(RESULT).unwrap(), b"actual-cwd-refusal-complete").unwrap();
        return;
    }
    assert!(prepared.spawn().unwrap().wait().unwrap().success());
    assert_eq!(fs::read(project.join("target/actual-body")).unwrap(), b"actual-member-body");
    fs::write(std::env::var_os(RESULT).unwrap(), b"actual-root-complete").unwrap();
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub(crate) fn actor_leaf() {
    let original = actor_original();
    let cwd = std::env::current_dir().unwrap();
    let directory = original.original_output_cwd().unwrap().unwrap();
    original.check_output_directory(&directory).unwrap();
    let target = original.retain_original_output_directory(&cwd.join("target")).unwrap();
    original.check_output_directory(&target).unwrap();
    fs::write(cwd.join("target/actual-body"), b"actual-member-body").unwrap();
    if std::env::var_os("TRUST_FIXED_OUTPUT_NOTICE_LEAF").is_some() {
        fs::write(cwd.join("target/actual-pid"), std::process::id().to_string()).unwrap();
    }
    original.check_current().unwrap();
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[test]
fn root_issued_member_crosses_real_courier_and_native_fchdir_until_group_retirement() {
    run_native_output_fixture("native-output-root", b"actual-root-complete");
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[test]
fn replaced_member_cwd_refuses_before_go_and_retires_the_stopped_child() {
    run_native_output_fixture("native-output-cwd-refusal", b"actual-cwd-refusal-complete");
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[test]
fn nested_original_notice_matches_actual_child_without_new_reservation() {
    run_native_output_fixture("native-output-observed-root", b"actual-notice-complete");
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[test]
fn nested_closed_notice_retires_stopped_child_without_running_body() {
    run_native_output_fixture("native-output-observed-closed", b"actual-notice-closed-refused");
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[test]
fn nested_notice_cannot_mutate_original_gnu_writer() {
    run_native_output_fixture("native-output-observed-alias", b"actual-notice-alias-refused");
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[test]
fn nested_v1_original_cannot_obtain_a_v2_execution_notice() {
    let (root, claim) = super::super::tests::fixture();
    let prepared = claim.prepare_command(Command::new("not-launched")).unwrap();
    let original = retain(root.path(), &prepared);
    let budget = original.budget().unwrap();
    let scheduler = jobserver_utils::Jobserver::new(1).unwrap();
    scheduler.client().acquire_raw().unwrap();
    let mut command = Command::new(std::env::current_exe().unwrap());
    for (name, _) in std::env::vars_os() {
        if name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_") {
            command.env_remove(name);
        }
    }
    // SAFETY: this isolated Root has its one original GNU server and actual
    // held worktree; no other work consumes its implicit continuation. The
    // test refuses the observer before any child is launched.
    let nested = unsafe {
        original.prepare_nested_command(
            command,
            scheduler,
            budget,
            Some(&root.path().join("worktree.lock")),
            false,
            Instant::now() + Duration::from_secs(10),
        )
    }
    .unwrap();
    let (_reader, writer) = super::super::group::loaded_tests::pipe();
    let input = super::super::group::ExecutionStartPipe::from_owned_writer(writer).unwrap();
    let error = nested.with_execution_start(input).err().unwrap();
    assert!(error.to_string().contains("original V2 output member"), "{error}");
    prepared.claim.check_current().unwrap();
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
fn run_native_output_fixture(mode: &str, expected: &[u8]) {
    use trust_resource_provenance::program::HeldSystemCommand;
    let (root, claim) = super::super::tests::fixture();
    let claim = claim.with_original_output_member().unwrap();
    let output = claim.output.as_ref().unwrap().root().unwrap().to_path_buf();
    let result = output.join("actual-root-result");
    let mut scheduler = jobserver_utils::Jobserver::new(1).unwrap();
    scheduler.client().acquire_raw().unwrap();
    if mode == "native-output-observed-alias" {
        let fd = scheduler.pipe_descriptors().unwrap()[1].as_raw_fd();
        // SAFETY: seed this fixture-owned GNU description BEFORE publication
        // or child launch, so its actual original flags are stable thereafter.
        unsafe {
            let flags = libc::fcntl(fd, libc::F_GETFL);
            assert!(flags >= 0);
            assert_eq!(libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK), 0);
        }
    }
    scheduler.enable_descendant_handoff().unwrap();
    let executable = std::env::current_exe().unwrap();
    let image =
        HeldSystemCommand::open(&executable, Instant::now() + Duration::from_secs(30)).unwrap();
    let mut command = Command::new(&executable);
    command
        .args(["--exact", super::super::group::tests::ACTOR, "--nocapture", "--test-threads=1"])
        .env(super::super::group::tests::MODE, mode)
        .env(NAMESPACE, root.path().join("legacy"))
        .env(RESULT, &result);
    for (name, _) in std::env::vars_os() {
        if name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_") {
            command.env_remove(name);
        }
    }
    scheduler.configure_make(&mut command);
    let prepared = claim.prepare_command(command).unwrap();
    // SAFETY: this exact fixture image has inherited console/cwd, no caller
    // pre_exec/env_clear/arg0 changes; the same GNU continuation stays paused.
    let mut group = unsafe {
        prepared.spawn_loaded_output_fixture(
            image,
            scheduler,
            Instant::now() + Duration::from_secs(15),
        )
    }
    .unwrap();
    assert!(super::super::group::tests::finish(&mut group).success());
    assert_eq!(fs::read(&result).unwrap(), expected);
    assert!(OutputLock::try_acquire_existing(&output).unwrap().is_none());
    drop(group);
    assert!(!output.exists(), "Root output was not retired after actual group drain");
}
