use std::io::{BufRead, BufReader};
use std::process::Stdio;
use std::time::{Duration, Instant};

use super::*;
use crate::admission::{Coordinator, Requirements, Waiting};

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[path = "nested/tests.rs"]
mod nested_tests;

fn width(n: u32) -> NonZeroU32 {
    NonZeroU32::new(n).unwrap()
}

pub(super) fn fixture() -> (tempfile::TempDir, FixedClaim) {
    fixture_with_budget(1)
}

fn fixture_with_budget(budget: u32) -> (tempfile::TempDir, FixedClaim) {
    fixture_with_mode(budget, false)
}

#[test]
fn contended_original_domain_waits_then_reads_the_same_held_claim() {
    use std::sync::mpsc;
    let (root, claim) = fixture();
    let prepared = claim.prepare_command(Command::new("never-launched")).unwrap();
    let pool = Pool::open_existing(root.path()).unwrap().unwrap();
    let other = Pool::open_existing(root.path()).unwrap().unwrap();
    // The fixture's admission just released this domain; another test's spawn
    // can still hold that description, so the hold waits boundedly for it.
    let held =
        original_transaction_before(&pool, Instant::now() + Duration::from_secs(5), || {}).unwrap();
    let descriptor = prepared.packet.as_raw_fd().to_string();
    let namespace = root.path().join("legacy");
    let record = prepared.claim.record.clone();
    let (busy_tx, busy_rx) = mpsc::sync_channel(0);
    let (resume_tx, resume_rx) = mpsc::sync_channel(0);
    std::thread::scope(|scope| {
        let worker = scope.spawn(move || {
            let mut first = Some(busy_tx);
            let transaction = original_transaction_before(
                &other,
                Instant::now() + Duration::from_secs(10),
                || {
                    if let Some(first) = first.take() {
                        first.send(()).unwrap();
                        resume_rx.recv_timeout(Duration::from_secs(10)).unwrap();
                    }
                },
            )
            .unwrap();
            let original =
                InheritedFixedClaim::read(OsStr::new(&descriptor), &namespace, width(2)).unwrap();
            assert_eq!(original.budget().unwrap(), width(1));
            assert_eq!(original.record, record);
            drop(transaction);
        });
        // This notification follows an actual failed native lock attempt,
        // not an assumed scheduling delay or a forged busy result.
        busy_rx.recv_timeout(Duration::from_secs(10)).unwrap();
        prepared.claim.check_current().unwrap();
        drop(held);
        resume_tx.send(()).unwrap();
        worker.join().unwrap();
    });
    prepared.claim.check_current().unwrap();
    assert!(!crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn original_domain_timeout_keeps_the_actual_resource_owner_unchanged() {
    let (root, claim) = fixture();
    let prepared = claim.prepare_command(Command::new("never-launched")).unwrap();
    let pool = Pool::open_existing(root.path()).unwrap().unwrap();
    let other = Pool::open_existing(root.path()).unwrap().unwrap();
    // As above: the fixture's release can still be held by another test's spawn.
    let _held =
        original_transaction_before(&pool, Instant::now() + Duration::from_secs(5), || {}).unwrap();
    let result =
        original_transaction_before(&other, Instant::now() + Duration::from_millis(10), || {});
    let error = match result {
        Err(error) => error,
        Ok(_) => panic!("busy native transaction admitted"),
    };
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    prepared.claim.check_current().unwrap();
    assert!(!crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn prelaunch_manifest_wait_retains_claim_and_releases_transaction_before_launch() {
    use std::sync::mpsc;
    let (root, claim) = fixture();
    let prepared = claim.prepare_command(Command::new("never-launched")).unwrap();
    let pool = Pool::open_existing(root.path()).unwrap().unwrap();
    let other = Pool::open_existing(root.path()).unwrap().unwrap();
    let held =
        original_transaction_before(&pool, Instant::now() + Duration::from_secs(5), || {}).unwrap();
    let (busy_tx, busy_rx) = mpsc::sync_channel(0);
    let (resume_tx, resume_rx) = mpsc::sync_channel(0);
    let prepared = std::thread::scope(|scope| {
        let worker = scope.spawn(move || {
            let mut first = Some(busy_tx);
            let room = prepared
                .claim
                .observe_in_pool_before(&other, Instant::now() + Duration::from_secs(10), || {
                    if let Some(first) = first.take() {
                        first.send(()).unwrap();
                        resume_rx.recv_timeout(Duration::from_secs(10)).unwrap();
                    }
                    Ok(())
                })
                .unwrap();
            assert!(matches!(room, LegacyFixedRoom::Fits { .. }));
            // This independent description must acquire the manifest now:
            // observation did not carry a transaction into the launch phase.
            assert!(other.try_legacy_fixed_transaction().unwrap().is_some());
            prepared
        });
        busy_rx.recv_timeout(Duration::from_secs(10)).unwrap();
        assert!(!crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
        drop(held);
        resume_tx.send(()).unwrap();
        worker.join().unwrap()
    });
    prepared.claim.check_current().unwrap();
}

#[test]
fn prelaunch_manifest_timeout_and_cancellation_do_not_start_or_release_the_claim() {
    let (root, claim) = fixture();
    let prepared = claim.prepare_command(Command::new("never-launched")).unwrap();
    let pool = Pool::open_existing(root.path()).unwrap().unwrap();
    let other = Pool::open_existing(root.path()).unwrap().unwrap();
    let _held =
        original_transaction_before(&pool, Instant::now() + Duration::from_secs(5), || {}).unwrap();
    let timeout = prepared
        .claim
        .observe_in_pool_before(&other, Instant::now() + Duration::from_millis(10), || Ok(()))
        .unwrap_err();
    assert_eq!(timeout.kind(), io::ErrorKind::TimedOut);
    let cancelled = prepared
        .claim
        .observe_in_pool_before(&other, Instant::now() + Duration::from_secs(5), || {
            Err(io::ErrorKind::Interrupted.into())
        })
        .unwrap_err();
    assert_eq!(cancelled.kind(), io::ErrorKind::Interrupted);
    prepared.claim.check_current().unwrap();
    assert!(!crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn early_fixed_snapshot_preserves_original_cursor_and_refuses_reused_packet() {
    use std::io::{Seek, SeekFrom};
    let (_root, claim) = fixture();
    let mut prepared = claim.prepare_command(Command::new("not-started")).unwrap();
    prepared.packet.seek(SeekFrom::Start(3)).unwrap();
    let fd = prepared.packet.as_raw_fd();
    let pending = EarlyFixedClaim::snapshot(OsStr::new(&fd.to_string())).unwrap();
    assert_eq!(prepared.packet.stream_position().unwrap(), 3);
    pending.check().unwrap();
    let bytes = pending.packet.clone();
    // A packet as the product makes one, so the refusal below is for its identity.
    let mut replacement = private_packet().unwrap();
    replacement.write_all(&bytes).unwrap();
    // This test replaces only its own still-owned packet slot. It does not
    // close another thread's descriptor or pretend the copy grants a claim.
    assert_eq!(unsafe { libc::dup2(replacement.as_raw_fd(), fd) }, fd);
    assert!(pending.check().is_err());
}

#[test]
fn early_fixed_snapshot_rejects_an_original_closed_at_entry() {
    use std::os::fd::IntoRawFd;
    let original = tempfile::tempfile().unwrap().into_raw_fd();
    assert_eq!(unsafe { libc::close(original) }, 0);
    assert!(EarlyFixedClaim::snapshot(OsStr::new(&original.to_string())).is_err());
}

// Trust: `check_nested` is compiled wherever the claim is, so its test is too. It sat
// in nested/tests.rs, which only Apple silicon compiles, while Targo's `repo-prune`
// called the check on Linux, where it did not exist (E0599).
#[test]
fn nested_ceiling_worktree_and_exclusive_checks_never_publish_a_new_claim() {
    let (root, claim) = fixture_with_budget(2);
    let prepared = claim.prepare_command(Command::new("unused")).unwrap();
    let original = read(&prepared, &root.path().join("legacy")).unwrap();
    let record = original.record.clone();
    let worktree = root.path().join("worktree.lock");
    original.check_nested(width(1), Some(&worktree), false).unwrap();
    original.check_nested(width(2), Some(&worktree), false).unwrap();
    assert_eq!(original.limited_budget(Some(OsStr::new("1"))).unwrap(), width(1));
    assert_eq!(original.limited_budget(Some(OsStr::new("32"))).unwrap(), width(2));
    assert!(original.limited_budget(Some(OsStr::new("0"))).is_err());
    assert!(original.check_nested(width(3), Some(&worktree), false).is_err());
    assert!(original.check_nested(width(1), None, false).is_err());
    assert!(original.check_nested(width(1), Some(&root.path().join("other.lock")), false).is_err());
    assert!(original.check_nested(width(1), Some(&worktree), true).is_err());
    assert_eq!(original.record, record);
    original.check_current().unwrap();
    assert!(!crate::admission::resources::tests::released(&worktree));
    let (exclusive_root, claim) = fixture_with_mode(2, true);
    let exclusive =
        read_exclusive_packet(&exclusive_packet(&claim), &exclusive_root.path().join("legacy"))
            .unwrap();
    exclusive
        .check_nested(width(1), Some(&exclusive_root.path().join("worktree.lock")), true)
        .unwrap();
}

fn fixture_with_mode(budget: u32, exclusive: bool) -> (tempfile::TempDir, FixedClaim) {
    let root = crate::owner_only::tempdir();
    let namespace = root.path().join("legacy");
    crate::owner_only::create_dir(&namespace);
    if exclusive {
        crate::launcher_file::write(&namespace.join("slot-3"), b"");
    }
    let pool = Pool::open_in(root.path(), width(2)).unwrap();
    let mut coordinator = Coordinator::open(
        &namespace,
        &root.path().join("adopted"),
        Requirements::new(Some(root.path().join("worktree.lock")), 2, 1, exclusive, 0).unwrap(),
    )
    .unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        match coordinator.attempt_fixed_in_pool(Some(0), budget, width(budget), &pool).unwrap() {
            Attempt::Admitted(claim) => return (root, claim),
            Attempt::Waiting(Waiting::RegistryBusy) if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(1));
            }
            Attempt::Waiting(reason) => panic!("original fixed claim refused: {reason:?}"),
        }
    }
}

fn exclusive_packet(claim: &FixedClaim) -> Packet {
    Packet {
        version: 1,
        namespace: claim.reservation.namespace.as_os_str().as_bytes().to_vec(),
        cpus: claim.cpus.get(),
        budget: claim.budget.get(),
        record: claim.record.clone(),
        files: original_entries(claim).unwrap(),
    }
}

fn read_exclusive_packet(packet: &Packet, namespace: &Path) -> io::Result<InheritedFixedClaim> {
    let mut file = private_packet()?;
    file.write_all(&serde_json::to_vec(packet).unwrap())?;
    InheritedFixedClaim::read(OsStr::new(&file.as_raw_fd().to_string()), namespace, width(2))
}

#[test]
fn exclusive_original_handoff_retains_the_fence_and_every_historical_slot() {
    let (root, claim) = fixture_with_mode(2, true);
    let namespace = root.path().join("legacy");
    let inherited = read_exclusive_packet(&exclusive_packet(&claim), &namespace).unwrap();
    drop(claim);
    for name in ["admission.lock", "slot-0", "slot-1", "slot-3"] {
        let file = OpenOptions::new().read(true).write(true).open(namespace.join(name)).unwrap();
        assert!(!try_exclusive(&file).unwrap(), "lost {name}");
    }
    inherited.check_budget(width(2)).unwrap();
    drop(inherited);
    assert!(crate::admission::resources::tests::released(&namespace.join("admission.lock")));
}

#[test]
fn self_consistent_partial_exclusive_packets_do_not_authorize_a_nested_claim() {
    for missing in ["admission.lock", "slot-3"] {
        let (root, mut claim) = fixture_with_mode(2, true);
        let mut packet = exclusive_packet(&claim);
        packet.files.retain(|entry| {
            Path::new(OsStr::from_bytes(&entry.path)).file_name() != Some(OsStr::new(missing))
        });
        let (count, digest) = fingerprint(&packet.files).unwrap();
        let mut record: serde_json::Value = serde_json::from_slice(&packet.record).unwrap();
        record["claim_file_count"] = count.into();
        record["claim_files_sha256"] = serde_json::to_value(digest).unwrap();
        packet.record = serde_json::to_vec(&record).unwrap();
        claim.record = packet.record.clone();
        // Make all actual originals match the malformed packet: a rejection
        // must establish complete exclusive membership, not just hash equality.
        for lease in claim.reservation.held.iter().chain(&claim.reservation.slots) {
            lease.file.set_len(0).unwrap();
            lease.file.write_all_at(&packet.record, 0).unwrap();
        }
        assert!(read_exclusive_packet(&packet, &root.path().join("legacy")).is_err(), "{missing}");
        claim.check_current().unwrap();
        let fence = OpenOptions::new()
            .read(true)
            .write(true)
            .open(root.path().join("legacy/admission.lock"))
            .unwrap();
        assert!(!try_exclusive(&fence).unwrap(), "refused read unlocked the original fence");
    }
}

#[test]
fn exclusive_launch_cannot_skip_quietness_or_run_after_an_expired_wait() {
    let (root, claim) = fixture_with_mode(2, true);
    let marker = root.path().join("must-not-launch");
    let mut command = Command::new("/usr/bin/touch");
    command.arg(&marker);
    let error = claim.prepare_exclusive_command(command, Duration::ZERO).err().unwrap();
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    assert!(!marker.exists());
    assert!(crate::admission::resources::tests::released(
        &root.path().join("legacy/admission.lock")
    ));

    let (_root, claim) = fixture_with_mode(2, true);
    assert!(claim.prepare_command(Command::new("must-not-launch")).is_err());
    let (_root, claim) = fixture();
    assert!(
        claim.prepare_exclusive_command(Command::new("must-not-launch"), Duration::ZERO).is_err()
    );
}

#[test]
fn smaller_command_ceiling_is_retained_by_nested_original_custody() {
    let (root, claim) = fixture_with_budget(2);
    assert_eq!(claim.budget(), width(2));
    let mut command = Command::new("unused-command");
    command.env("CARGO_BUILD_JOBS", "1");
    let prepared = claim.prepare_command(command).unwrap();
    let inherited = read(&prepared, &root.path().join("legacy")).unwrap();
    inherited.check_budget(width(1)).unwrap();
    assert!(inherited.check_budget(width(2)).is_err());
}

#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::resources::machine::handoff::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            exclusive_original_handoff_retains_the_fence_and_every_historical_slot();
            smaller_command_ceiling_is_retained_by_nested_original_custody();
        },
    );
}

fn packet(prepared: &PreparedFixedCommand) -> Packet {
    let mut bytes = vec![0; prepared.packet.metadata().unwrap().len() as usize];
    prepared.packet.read_exact_at(&mut bytes, 0).unwrap();
    serde_json::from_slice(&bytes).unwrap()
}

fn rewrite(prepared: &mut PreparedFixedCommand, packet: &Packet) {
    let bytes = serde_json::to_vec(packet).unwrap();
    prepared.packet.set_len(0).unwrap();
    prepared.packet.write_all_at(&bytes, 0).unwrap();
}

fn read(prepared: &PreparedFixedCommand, namespace: &Path) -> io::Result<InheritedFixedClaim> {
    InheritedFixedClaim::read(
        OsStr::new(&prepared.packet.as_raw_fd().to_string()),
        namespace,
        width(2),
    )
}

fn transferred_originals(prepared: &PreparedFixedCommand) -> Vec<std::os::fd::OwnedFd> {
    original_entries(&prepared.claim)
        .unwrap()
        .iter()
        .map(|entry| {
            trust_build_cpu::duplicate_descriptor(OsStr::new(&entry.descriptor.to_string()))
                .unwrap()
                .into()
        })
        .collect()
}

#[test]
fn transferred_originals_ignore_sender_fd_numbers_but_keep_full_claim_validation() {
    let (root, claim) = fixture();
    let mut prepared = claim.prepare_command(Command::new("unused-command")).unwrap();
    let originals = transferred_originals(&prepared);
    let mut description = packet(&prepared);
    for entry in &mut description.files {
        entry.descriptor = 0;
    }
    rewrite(&mut prepared, &description);
    assert!(
        read(&prepared, &root.path().join("legacy")).is_err(),
        "legacy numeric reader weakened"
    );
    let stdin_before = unsafe { libc::fcntl(0, libc::F_GETFD) };
    let inherited = InheritedFixedClaim::read_file(
        prepared.packet.try_clone().unwrap(),
        &root.path().join("legacy"),
        width(2),
        Some(originals),
    )
    .unwrap();
    assert_eq!(unsafe { libc::fcntl(0, libc::F_GETFD) }, stdin_before, "remote FD0 was touched");
    inherited.check_budget(width(1)).unwrap();
    assert!(inherited.check_budget(width(2)).is_err());
    drop(prepared);
    inherited.check_current().unwrap();
    assert!(!crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
    drop(inherited);
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn transferred_missing_or_foreign_originals_never_construct_a_fixed_claim() {
    let (root, claim) = fixture();
    let prepared = claim.prepare_command(Command::new("unused-command")).unwrap();
    for foreign in [false, true] {
        let mut originals = transferred_originals(&prepared);
        if foreign {
            originals[0] = tempfile::tempfile().unwrap().into();
        } else {
            originals.pop();
        }
        assert!(
            InheritedFixedClaim::read_file(
                prepared.packet.try_clone().unwrap(),
                &root.path().join("legacy"),
                width(2),
                Some(originals)
            )
            .is_err()
        );
        prepared.claim.check_current().unwrap();
    }
}

#[test]
fn explicit_descendant_courier_cannot_override_a_new_direct_claim() {
    let (_root, claim) = fixture();
    let mut command = Command::new("must-not-be-executed");
    command.env(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV, "not-authority");
    let error = claim.prepare_command(command).err().unwrap();
    assert!(error.to_string().contains("fixed descendant courier"), "{error}");
}

#[test]
fn new_direct_claim_clears_ambient_courier_before_actual_child_delivery() {
    const MODE: &str = "TRUST_FIXED_DIRECT_COURIER_TEST_MODE";
    const TEST: &str = "admission::resources::machine::handoff::tests::new_direct_claim_clears_ambient_courier_before_actual_child_delivery";
    if let Some(mode) = std::env::var_os(MODE) {
        if mode == "receiver" {
            assert!(std::env::var_os(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV).is_none());
            let namespace = std::env::var_os("TRUST_FIXED_DIRECT_TEST_NAMESPACE").unwrap();
            let value = std::env::var_os(FIXED_HANDOFF_ENV).unwrap();
            let claim = InheritedFixedClaim::read(&value, Path::new(&namespace), width(2)).unwrap();
            claim.check_budget(width(1)).unwrap();
            assert!(claim.check_budget(width(2)).is_err());
        } else {
            assert!(std::env::var_os(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV).is_some());
            let (root, claim) = fixture();
            let mut command = Command::new(std::env::current_exe().unwrap());
            command
                .args(["--exact", TEST, "--nocapture"])
                .env(MODE, "receiver")
                .env("TRUST_FIXED_DIRECT_TEST_NAMESPACE", root.path().join("legacy"));
            let mut child = claim.prepare_command(command).unwrap().spawn_checked().unwrap();
            assert!(child.wait().unwrap().success());
        }
        return;
    }
    let status = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", TEST, "--nocapture"])
        .env(MODE, "owner")
        .env(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV, "stale-ancestor-routing-only")
        .status()
        .unwrap();
    assert!(status.success());
}

#[test]
fn original_duplicates_retain_complete_claim_and_never_enlarge_nested_budget() {
    let (root, claim) = fixture();
    let prepared = claim.prepare_command(Command::new("unused-command")).unwrap();
    let inherited = read(&prepared, &root.path().join("legacy")).unwrap();
    assert!(inherited.check_budget(width(1)).is_ok());
    assert!(inherited.check_budget(width(2)).is_err());
    drop(prepared);
    inherited.check_current().unwrap();
    for path in [root.path().join("worktree.lock"), root.path().join("legacy/slot-0")] {
        let probe = OpenOptions::new().read(true).write(true).open(&path).unwrap();
        assert!(!try_exclusive(&probe).unwrap());
    }
    drop(inherited);
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn native_budget_observes_the_same_real_claim_and_refuses_changed_record() {
    use crate::admission::budget::{self, CpuScope, Overlap, Request, Workload};
    let (root, claim) = fixture();
    let prepared = claim.prepare_command(Command::new("never-launched")).unwrap();
    let inherited = read(&prepared, &root.path().join("legacy")).unwrap();
    let request = Request::new(Workload::RustcBuild);
    let report = budget::current(&request, Some(&inherited)).unwrap();
    assert_eq!(report.cpu_scope, CpuScope::OriginalFixed { ceiling: 1 });
    assert!(report.plan.jobs <= 1);
    assert_eq!(report.overlap, Some(Overlap::OriginalFixedRequiresSerial));
    let original = &inherited
        .held
        .iter()
        .find(|held| held.name.as_bytes().starts_with(b"slot-"))
        .unwrap()
        .file;
    let flags = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) };
    let local = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFD) };
    original.write_all_at(b"changed", 0).unwrap();
    assert!(budget::current(&request, Some(&inherited)).is_err());
    assert_eq!(unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) }, flags);
    assert_eq!(unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFD) }, local);
}

#[test]
fn partial_foreign_and_replaced_descriptors_never_become_original_custody() {
    for mode in ["partial", "foreign", "replaced", "budget", "role", "width"] {
        let (root, claim) = fixture();
        let mut prepared = claim.prepare_command(Command::new("unused-command")).unwrap();
        let mut wire = packet(&prepared);
        let mut foreign = None;
        match mode {
            "partial" => {
                wire.files.pop();
            }
            "foreign" => {
                let file = OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(PathBuf::from(OsString::from_vec(wire.files[0].path.clone())))
                    .unwrap();
                wire.files[0].descriptor = file.as_raw_fd();
                foreign = Some(file);
            }
            "replaced" => {
                let path = PathBuf::from(OsString::from_vec(wire.files[0].path.clone()));
                fs::rename(&path, path.with_extension("original")).unwrap();
                crate::owner_only::write(&path, &wire.record);
            }
            "budget" => wire.budget = 2,
            "role" => wire.files[0].slot = !wire.files[0].slot,
            "width" => wire.cpus = 3,
            _ => unreachable!(),
        }
        rewrite(&mut prepared, &wire);
        assert!(read(&prepared, &root.path().join("legacy")).is_err(), "{mode}");
        drop(foreign);
        // A refused foreign duplicate must not unlock the true original.
        if mode != "replaced" {
            prepared.claim.check_current().unwrap();
            for lease in &prepared.claim.reservation.slots {
                let probe = OpenOptions::new().read(true).write(true).open(lease.path()).unwrap();
                assert!(!try_exclusive(&probe).unwrap(), "{mode}");
            }
        }
    }
}

#[test]
fn checked_record_reads_never_move_original_shared_file_offsets() {
    let (root, claim) = fixture();
    let prepared = claim.prepare_command(Command::new("unused-command")).unwrap();
    for lease in &prepared.claim.reservation.slots {
        let mut duplicate = lease.file.try_clone().unwrap();
        duplicate.seek(SeekFrom::Start(3)).unwrap();
        prepared.claim.check_current().unwrap();
        read(&prepared, &root.path().join("legacy")).unwrap().check_current().unwrap();
        assert_eq!(duplicate.stream_position().unwrap(), 3);
    }
}

#[test]
fn inherited_claim_actor() {
    let Some(namespace) = std::env::var_os("TRUST_FIXED_TEST_NAMESPACE") else { return };
    let descriptor = std::env::var_os(FIXED_HANDOFF_ENV).unwrap();
    let inherited =
        InheritedFixedClaim::read(&descriptor, Path::new(&namespace), width(2)).unwrap();
    inherited.check_budget(width(1)).unwrap();
    assert!(inherited.check_budget(width(2)).is_err());
    assert_eq!(std::env::var("CARGO_BUILD_JOBS").unwrap(), "1");
    println!("FIXED-CLAIM-HELD");
    io::stdout().flush().unwrap();
    let mut token = [0];
    io::stdin().read_exact(&mut token).unwrap();
    assert_eq!(token, [83]);
    inherited.check_current().unwrap();
    std::process::exit(83);
}

#[test]
fn actual_exec_keeps_original_resources_after_parent_owners_close() {
    let (root, claim) = fixture();
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args([
            "--exact",
            "admission::resources::machine::handoff::tests::inherited_claim_actor",
            "--nocapture",
        ])
        .env("TRUST_FIXED_TEST_NAMESPACE", root.path().join("legacy"))
        .env("CARGO_BUILD_JOBS", "999")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped());
    let prepared = claim.prepare_command(command).unwrap();
    for entry in packet(&prepared).files {
        assert_ne!(unsafe { libc::fcntl(entry.descriptor, libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
    }
    let running = std::mem::ManuallyDrop::new(prepared.spawn_checked().unwrap());
    // This isolated custody control deliberately closes the parent copies
    // without invoking public supervisor cancellation. Move every field once.
    let (claim, _packet, child) = unsafe {
        (
            std::ptr::read(&running.claim),
            std::ptr::read(&running._packet),
            std::ptr::read(&running.child),
        )
    };
    struct Owned(Child);
    impl Drop for Owned {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let mut child = Owned(child);
    let mut reader = BufReader::new(child.0.stdout.take().unwrap());
    loop {
        let mut line = String::new();
        assert_ne!(reader.read_line(&mut line).unwrap(), 0, "original child exited before custody");
        if line.trim() == "FIXED-CLAIM-HELD" {
            break;
        }
    }
    drop(claim);
    drop(_packet);
    for path in [root.path().join("worktree.lock"), root.path().join("legacy/slot-0")] {
        let probe = OpenOptions::new().read(true).write(true).open(path).unwrap();
        assert!(!try_exclusive(&probe).unwrap());
    }
    child.0.stdin.as_mut().unwrap().write_all(&[83]).unwrap();
    assert_eq!(child.0.wait().unwrap().code(), Some(83));
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn direct_child_without_retained_claim_actor() {
    if std::env::var_os("TRUST_FIXED_DROP_ACTOR").is_none() {
        return;
    }
    let descriptor = std::env::var_os(FIXED_HANDOFF_ENV).unwrap();
    let file = trust_build_cpu::duplicate_descriptor(&descriptor).unwrap();
    let mut bytes = vec![0; file.metadata().unwrap().len() as usize];
    file.read_exact_at(&mut bytes, 0).unwrap();
    let packet: Packet = serde_json::from_slice(&bytes).unwrap();
    // An ordinary executable may close every inherited resource descriptor.
    // Its still-running supervisor must retain the original claim itself.
    for entry in packet.files {
        assert!(entry.descriptor > 2);
        // SAFETY: these are the actual descriptors explicitly inherited by
        // this isolated actor, which owns their one close in this process.
        assert_eq!(unsafe { libc::close(entry.descriptor) }, 0);
    }
    println!("FIXED-ORIGINALS-CLOSED");
    io::stdout().flush().unwrap();
    let mut byte = [0];
    if io::stdin().read_exact(&mut byte).is_ok() {
        std::process::exit(i32::from(byte[0]));
    }
}

fn closing_actor(claim: FixedClaim) -> (RunningFixedCommand, std::process::ChildStdin) {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args([
            "--exact",
            "admission::resources::machine::handoff::tests::direct_child_without_retained_claim_actor",
            "--nocapture",
        ])
        .env("TRUST_FIXED_DROP_ACTOR", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped());
    let mut running = claim.prepare_command(command).unwrap().spawn_checked().unwrap();
    let stdin = running.child.stdin.take().unwrap();
    let mut stdout = running.take_stdout().unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut line = Vec::new();
    loop {
        let timeout = deadline.saturating_duration_since(Instant::now()).as_millis();
        assert!(timeout > 0, "actor readiness timed out");
        let mut poll = libc::pollfd { fd: stdout.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: stdout owns this descriptor throughout the bounded poll.
        let ready = unsafe { libc::poll(&mut poll, 1, timeout.min(10_000) as i32) };
        if ready < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
            continue;
        }
        assert!(ready > 0, "actor stdout unavailable");
        let mut byte = [0];
        stdout.read_exact(&mut byte).expect("actor exited before readiness");
        if byte == *b"\n" {
            if line == b"FIXED-ORIGINALS-CLOSED" {
                break;
            }
            line.clear();
        } else {
            assert!(line.len() < 4096, "actor readiness line exceeded its bound");
            line.push(byte[0]);
        }
    }
    (running, stdin)
}

#[test]
fn dropping_supervisor_reaps_its_live_child_before_releasing_resources() {
    let (root, claim) = fixture();
    let (running, _stdin) = closing_actor(claim);
    let pid = running.id() as libc::pid_t;
    struct ReapOurChild(libc::pid_t);
    impl Drop for ReapOurChild {
        fn drop(&mut self) {
            // SAFETY: this PID belongs to the actual child just spawned by
            // this test; an unreaped child cannot have its PID reused.
            unsafe {
                if libc::waitpid(self.0, std::ptr::null_mut(), libc::WNOHANG) == 0 {
                    libc::kill(self.0, libc::SIGKILL);
                    while libc::waitpid(self.0, std::ptr::null_mut(), 0) < 0 {
                        if io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                            break;
                        }
                    }
                }
            }
        }
    }
    let _cleanup = ReapOurChild(pid);
    // Keep stdin open past supervisor Drop: EOF must not terminate the actor
    // on behalf of the missing product supervision.
    let probe =
        OpenOptions::new().read(true).write(true).open(root.path().join("legacy/slot-0")).unwrap();
    assert!(!try_exclusive(&probe).unwrap());
    drop(running);
    // The owner must perform the actual wait, rather than leaving a live
    // child or zombie while its original resource descriptions are released.
    let result = unsafe { libc::waitpid(pid, std::ptr::null_mut(), libc::WNOHANG) };
    assert_eq!(result, -1, "supervisor released its claim without owning child retirement");
    assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn natural_nonzero_exit_and_repeated_observations_keep_the_actual_status() {
    let (root, claim) = fixture();
    let (mut running, mut stdin) = closing_actor(claim);
    assert!(running.try_wait().unwrap().is_none());
    stdin.write_all(&[83]).unwrap();
    assert_eq!(running.wait().unwrap().code(), Some(83));
    assert_eq!(running.try_wait().unwrap().unwrap().code(), Some(83));
    assert_eq!(running.cancel().unwrap().code(), Some(83));
    drop(running);
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn explicit_cancellation_reaps_only_the_owned_child_and_retains_the_claim() {
    use std::os::unix::process::ExitStatusExt;
    let (root, claim) = fixture();
    let (mut running, _stdin) = closing_actor(claim);
    assert_eq!(running.cancel().unwrap().signal(), Some(libc::SIGKILL));
    let probe =
        OpenOptions::new().read(true).write(true).open(root.path().join("legacy/slot-0")).unwrap();
    assert!(!try_exclusive(&probe).unwrap());
    drop(running);
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn resource_validation_failure_does_not_prevent_owned_child_cancellation() {
    use std::os::unix::process::ExitStatusExt;
    let (root, claim) = fixture();
    let (mut running, _stdin) = closing_actor(claim);
    let path = root.path().join("legacy/slot-0");
    fs::rename(&path, path.with_extension("original")).unwrap();
    crate::owner_only::write(&path, b"foreign replacement");
    assert!(running.wait().is_err());
    assert_eq!(running.cancel().unwrap().signal(), Some(libc::SIGKILL));
    drop(running);
    assert!(crate::admission::resources::tests::released(&path.with_extension("original")));
}

#[test]
fn unknown_retirement_actor() {
    if std::env::var_os("TRUST_FIXED_UNKNOWN_RETIREMENT_ACTOR").is_none() {
        return;
    }
    let (root, claim) = fixture();
    let (mut running, _stdin) = closing_actor(claim);
    let pid = running.id() as libc::pid_t;
    // SAFETY: this is our actual direct child, whose PID cannot be reused
    // before this wait. Deliberately take its status away from the supervisor.
    unsafe {
        assert_eq!(libc::kill(pid, libc::SIGKILL), 0);
        loop {
            let result = libc::waitpid(pid, std::ptr::null_mut(), 0);
            if result == pid {
                break;
            }
            assert_eq!(io::Error::last_os_error().kind(), io::ErrorKind::Interrupted);
        }
    }
    assert_eq!(running.cancel().unwrap_err().raw_os_error(), Some(libc::ECHILD));
    drop(running);
    let probe =
        OpenOptions::new().read(true).write(true).open(root.path().join("legacy/slot-0")).unwrap();
    assert!(!try_exclusive(&probe).unwrap(), "unknown retirement released original custody");
    // The deliberately retained descriptions end only with this isolated actor.
}

#[test]
fn losing_the_owning_wait_never_releases_original_resources() {
    let status = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "admission::resources::machine::handoff::tests::unknown_retirement_actor",
            "--nocapture",
        ])
        .env("TRUST_FIXED_UNKNOWN_RETIREMENT_ACTOR", "1")
        .status()
        .unwrap();
    assert!(status.success());
}
