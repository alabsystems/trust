use std::collections::BTreeMap;
use std::io::{Seek, SeekFrom};
use std::num::NonZeroU32;
use std::os::unix::fs::PermissionsExt;

use super::*;

struct Fixture {
    _root: tempfile::TempDir,
    namespace: PathBuf,
    capacity: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        let root = crate::owner_only::tempdir();
        let physical = fs::canonicalize(root.path()).unwrap();
        let namespace = physical.join("legacy");
        let capacity = physical.join("capacity");
        crate::owner_only::create_dir(&namespace);
        Self { _root: root, namespace, capacity }
    }
    fn pool(&self, count: u32) -> Pool {
        Pool::open_in(&self.capacity, NonZeroU32::new(count).unwrap()).unwrap()
    }
    fn file(&self, name: &str, bytes: &[u8], held: bool) -> File {
        let path = self.namespace.join(name);
        crate::owner_only::create_dir_all(path.parent().unwrap());
        // scripts/build-slot makes its slots and its fence 0644 and its queue,
        // registry and adoption files 0600.
        if name.starts_with("slot-") || name == "admission.lock" {
            crate::launcher_file::write(&path, bytes);
        } else {
            crate::owner_only::write(&path, bytes);
        }
        let file = OpenOptions::new().read(true).write(true).open(&path).unwrap();
        if held {
            file.try_lock().unwrap();
        }
        file
    }
    fn observe(&self) -> MachineStatus {
        snapshot(&self.namespace, &self.capacity, None)
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Entry {
    inode: u64,
    device: u64,
    mode: u32,
    bytes: Vec<u8>,
}
fn contents(root: &Path) -> BTreeMap<PathBuf, Entry> {
    fn walk(root: &Path, at: &Path, rows: &mut BTreeMap<PathBuf, Entry>) {
        let metadata = fs::symlink_metadata(at).unwrap();
        let bytes = if metadata.file_type().is_symlink() {
            fs::read_link(at).unwrap().as_os_str().as_bytes().to_vec()
        } else if metadata.is_file() {
            fs::read(at).unwrap()
        } else {
            Vec::new()
        };
        rows.insert(
            at.strip_prefix(root).unwrap().to_owned(),
            Entry { inode: metadata.ino(), device: metadata.dev(), mode: metadata.mode(), bytes },
        );
        if metadata.is_dir() {
            for entry in fs::read_dir(at).unwrap() {
                walk(root, &entry.unwrap().path(), rows);
            }
        }
    }
    let mut rows = BTreeMap::new();
    walk(root, root, &mut rows);
    rows
}
fn observed<T>(value: Observation<T>) -> T {
    match value {
        Observation::Observed { value } => value,
        other => panic!(
            "expected observed, got {}",
            match other {
                Observation::Absent => "absent",
                Observation::Busy => "busy",
                _ => "unavailable",
            }
        ),
    }
}
fn unavailable<T>(value: &Observation<T>) -> bool {
    matches!(value, Observation::Unavailable { .. })
}

#[test]
fn absent_status_creates_no_namespace_pool_or_registry() {
    isolated_status_fixture(
        "admission::status::tests::absent_status_creates_no_namespace_pool_or_registry",
        || {
            let root = crate::owner_only::tempdir();
            let before = contents(root.path());
            let result = snapshot(
                &root.path().join("missing-legacy"),
                &root.path().join("missing-capacity"),
                None,
            );
            assert!(matches!(result.legacy, Observation::Absent));
            assert!(matches!(result.native, Observation::Absent));
            assert_eq!(contents(root.path()), before);
        },
    );
}

#[test]
fn actual_slots_keep_held_unknown_stale_and_missing_distinct_without_mutation() {
    isolated_status_fixture(
        "admission::status::tests::actual_slots_keep_held_unknown_stale_and_missing_distinct_without_mutation",
        || {
            let f = Fixture::new();
            let pool = f.pool(18);
            let native_lease =
                pool.try_acquire(trust_build_cpu::Owner::current(None)).unwrap().unwrap();
            let mut held = f.file("slot-0", b"not a complete owner record", true);
            held.seek(SeekFrom::Start(3)).unwrap();
            let flags = unsafe { libc::fcntl(held.as_raw_fd(), libc::F_GETFL) };
            let _stale = f.file("slot-1", br#"{"pid":1,"cpu_mode":"fixed-v1"}"#, false);
            let before = contents(f._root.path());
            let status = f.observe();
            let native = observed(status.native);
            assert_eq!(
                native.slots.iter().filter(|slot| slot.state == NativeSlotState::Held).count(),
                1
            );
            assert!(matches!(native.external, Observation::Absent));
            let legacy = observed(status.legacy);
            assert_eq!(legacy.slots.len(), 3);
            assert_eq!(legacy.slots[0].lock, Observation::observed(LockState::ExclusiveHeld));
            assert!(unavailable(&legacy.slots[0].reported));
            assert_eq!(legacy.slots[1].lock, Observation::observed(LockState::SharedCompatible));
            assert!(matches!(legacy.slots[1].reported, Observation::Absent));
            assert!(matches!(legacy.slots[2].lock, Observation::Absent));
            assert!(matches!(legacy.queue, Observation::Absent));
            assert!(matches!(legacy.adopted, Observation::Absent));
            assert_eq!(held.stream_position().unwrap(), 3);
            assert_eq!(unsafe { libc::fcntl(held.as_raw_fd(), libc::F_GETFL) }, flags);
            assert_eq!(contents(f._root.path()), before);
            assert!(!try_exclusive(&File::open(f.namespace.join("slot-0")).unwrap()).unwrap());
            drop(native_lease);
        },
    );
}

#[test]
fn actual_fifo_population_and_exclusive_drain_fence_remain_diagnostic() {
    isolated_status_fixture(
        "admission::status::tests::actual_fifo_population_and_exclusive_drain_fence_remain_diagnostic",
        || {
            let f = Fixture::new();
            let _registry = f.file("admission/registry.lock", b"", false);
            let required = Requirements::new(None, 3, 2, true, 4096).unwrap();
            let bytes = serde_json::to_vec(&NativeRecord::new(&required)).unwrap();
            let _later = f.file("admission/wait-10", &bytes, true);
            let _early = f.file("admission/wait-2", &bytes, true);
            let _bad = f.file("admission/wait-3", b"partial", true);
            let _stale = f.file("admission/wait-1", &bytes, false);
            let _exclusive = f.file(
                "admission.lock",
                br#"{"pid":123,"exclusive":true,"cmd":"original exclusive"}"#,
                true,
            );
            let before = contents(f._root.path());
            let status = observed(f.observe().legacy);
            assert_eq!(status.admission.lock, Observation::observed(LockState::ExclusiveHeld));
            assert_eq!(observed(status.admission.reported).exclusive, Some(true));
            let queue = observed(status.queue);
            assert_eq!(
                queue.tickets.iter().map(|ticket| ticket.order).collect::<Vec<_>>(),
                [1, 2, 3, 10]
            );
            assert_eq!(queue.tickets[0].lock, Observation::observed(LockState::SharedCompatible));
            assert!(matches!(queue.tickets[0].requirements, Observation::Absent));
            assert_eq!(observed_requirement(&queue.tickets[1].requirements).needed, 2);
            assert!(unavailable(&queue.tickets[2].requirements));
            assert_eq!(contents(f._root.path()), before);
        },
    );
}

// Each called test runs its body in a process of its own (`isolated_status_fixture`),
// which inherits this process's umask.
#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::status::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            actual_slots_keep_held_unknown_stale_and_missing_distinct_without_mutation();
            actual_fifo_population_and_exclusive_drain_fence_remain_diagnostic();
        },
    );
}
fn observed_requirement(value: &Observation<RequirementObservation>) -> &RequirementObservation {
    match value {
        Observation::Observed { value } => value,
        _ => panic!("missing actual requirements"),
    }
}

#[test]
fn busy_and_incomplete_registries_are_not_empty_populations() {
    isolated_status_fixture(
        "admission::status::tests::busy_and_incomplete_registries_are_not_empty_populations",
        || {
            let f = Fixture::new();
            let _queue = f.file("admission/registry.lock", b"", true);
            let _adopted = f.file("adopted/registration.lock", b"", true);
            let before = contents(f._root.path());
            let status = observed(f.observe().legacy);
            assert!(matches!(status.queue, Observation::Busy));
            assert!(matches!(status.adopted, Observation::Busy));
            assert_eq!(contents(f._root.path()), before);
            drop(_queue);
            drop(_adopted);
            fs::remove_file(f.namespace.join("admission/registry.lock")).unwrap();
            fs::remove_file(f.namespace.join("adopted/registration.lock")).unwrap();
            let before = contents(f._root.path());
            let status = observed(f.observe().legacy);
            assert!(unavailable(&status.queue));
            assert!(unavailable(&status.adopted));
            assert_eq!(contents(f._root.path()), before);
        },
    );
}

fn adoption(f: &Fixture, name: &str, pid: u32, birth: &str) {
    let record = serde_json::json!({"schema":1,"adopted":true,"pid":pid,"identity":{"pid":pid,"uid":unsafe { libc::geteuid() },"birth":birth,"executable":"/diagnostic-only"},"pool":f.namespace,"worktree":null,"leases":[f.namespace.join("slot-0")]});
    f.file(name, &serde_json::to_vec(&record).unwrap(), false);
}

#[test]
fn current_dead_and_malformed_adopted_records_stay_present_with_distinct_outcomes() {
    isolated_status_fixture(
        "admission::status::tests::current_dead_and_malformed_adopted_records_stay_present_with_distinct_outcomes",
        || {
            let f = Fixture::new();
            let _registration = f.file("adopted/registration.lock", b"", false);
            f.file("slot-0", b"", false);
            let current = std::process::id();
            let birth = crate::trust_repo_lock::management::process::live_adoption_birth(current)
                .unwrap()
                .unwrap();
            adoption(&f, "adopted/live.json", current, &birth);
            adoption(&f, "adopted/unobservable.json", u32::MAX, &birth);
            struct OwnedChild(std::process::Child);
            impl Drop for OwnedChild {
                fn drop(&mut self) {
                    let _ = self.0.kill();
                    let _ = self.0.wait();
                }
            }
            let mut child =
                OwnedChild(std::process::Command::new("/bin/sleep").arg("60").spawn().unwrap());
            let pid = child.0.id();
            let birth = crate::trust_repo_lock::management::process::live_adoption_birth(pid)
                .unwrap()
                .unwrap();
            child.0.kill().unwrap();
            child.0.wait().unwrap();
            adoption(&f, "adopted/dead.json", pid, &birth);
            f.file("adopted/unknown.json", br#"{"schema":200}"#, false);
            let before = contents(f._root.path());
            let records = observed(observed(f.observe().legacy).adopted);
            assert_eq!(records.len(), 4);
            let mut kinds = BTreeMap::new();
            for row in records {
                match row.record {
                    Observation::Observed { value } => {
                        kinds.insert(row.name_bytes, value.process);
                    }
                    Observation::Unavailable { .. } => {
                        assert_eq!(row.name_bytes, b"unknown.json");
                    }
                    _ => panic!("unexpected adoption result"),
                }
            }
            assert_eq!(
                kinds[b"live.json".as_slice()],
                Observation::observed(AdoptedProcess::SameBirth)
            );
            assert_eq!(
                kinds[b"dead.json".as_slice()],
                Observation::observed(AdoptedProcess::GoneOrReused)
            );
            assert!(unavailable(&kinds[b"unobservable.json".as_slice()]));
            assert_eq!(contents(f._root.path()), before);
        },
    );
}

#[test]
fn symlink_unreadable_or_oversized_slot_never_becomes_shared_compatible() {
    isolated_status_fixture(
        "admission::status::tests::symlink_unreadable_or_oversized_slot_never_becomes_shared_compatible",
        || {
            assert_ne!(
                unsafe { libc::geteuid() },
                0,
                "unreadability fixture requires a real non-root account"
            );
            let f = Fixture::new();
            let _pool = f.pool(18);
            let outside = f._root.path().join("outside");
            fs::write(&outside, b"preserved").unwrap();
            std::os::unix::fs::symlink(&outside, f.namespace.join("slot-0")).unwrap();
            f.file("slot-1", b"unreadable", false);
            fs::set_permissions(f.namespace.join("slot-1"), fs::Permissions::from_mode(0o0))
                .unwrap();
            let _oversized = f.file("slot-2", &vec![b'x'; MAX_RECORD as usize + 1], true);
            let status = observed(f.observe().legacy);
            assert!(unavailable(&status.slots[0].lock));
            assert!(unavailable(&status.slots[1].lock));
            assert_eq!(status.slots[2].lock, Observation::observed(LockState::ExclusiveHeld));
            assert!(unavailable(&status.slots[2].reported));
            assert_eq!(fs::read(&outside).unwrap(), b"preserved");
            assert_eq!(fs::metadata(f.namespace.join("slot-1")).unwrap().mode() & 0o777, 0);
            fs::set_permissions(f.namespace.join("slot-1"), fs::Permissions::from_mode(0o600))
                .unwrap();
        },
    );
}

#[test]
fn partial_native_external_state_is_unavailable_and_never_repaired() {
    isolated_status_fixture(
        "admission::status::tests::partial_native_external_state_is_unavailable_and_never_repaired",
        || {
            let f = Fixture::new();
            let pool = f.pool(2);
            fs::write(pool.path().join("external-debt-v1"), b"partial").unwrap();
            let before = contents(f._root.path());
            let native = observed(f.observe().native);
            assert!(unavailable(&native.external));
            assert_eq!(contents(f._root.path()), before);
        },
    );
}

#[test]
fn partial_native_pool_is_not_absent_or_reinitialized() {
    isolated_status_fixture(
        "admission::status::tests::partial_native_pool_is_not_absent_or_reinitialized",
        || {
            let f = Fixture::new();
            let pool = f.pool(2);
            fs::write(pool.path().join("pool"), b"partial").unwrap();
            let before = contents(f._root.path());
            assert!(unavailable(&f.observe().native));
            assert_eq!(contents(f._root.path()), before);
        },
    );
}

#[test]
fn status_serializes_original_non_utf8_requirement_bytes_without_opening_that_path() {
    isolated_status_fixture(
        "admission::status::tests::status_serializes_original_non_utf8_requirement_bytes_without_opening_that_path",
        || {
            let f = Fixture::new();
            let _registry = f.file("admission/registry.lock", b"", false);
            // APFS refuses invalid UTF-8 directory entries. Native queue records
            // instead carry byte paths as DATA; observing one must not open its path.
            let path =
                PathBuf::from(std::ffi::OsString::from_vec(b"/unopened/opaque-\xff/lock".to_vec()));
            let requirements = Requirements::new(Some(path.clone()), 1, 1, false, 0).unwrap();
            let _ticket = f.file(
                "admission/wait-1",
                &serde_json::to_vec(&NativeRecord::new(&requirements)).unwrap(),
                true,
            );
            let before = contents(f._root.path());
            let status = f.observe();
            let json = serde_json::to_value(&status).unwrap();
            assert_eq!(json["protocol"], "native-resource-status-v1");
            let rows = observed(observed(status.legacy).queue).tickets;
            assert_eq!(
                observed_requirement(&rows[0].requirements).worktree_bytes.as_deref(),
                Some(path.as_os_str().as_bytes())
            );
            assert_eq!(contents(f._root.path()), before);
        },
    );
}

#[test]
fn status_frontdoor_rejects_resource_and_namespace_options_before_observation() {
    let mut output = Vec::new();
    for args in [
        vec!["--dir", "/foreign"],
        vec!["--cpus", "1"],
        vec!["--json", "--json"],
        vec!["adopt", "1"],
    ] {
        let args = args.iter().map(std::ffi::OsString::from).collect::<Vec<_>>();
        assert!(command(&args, &mut output).is_err());
        assert!(output.is_empty());
    }
    command(&["--help".into()], &mut output).unwrap();
    assert!(String::from_utf8(output).unwrap().contains("no admission"));
}

#[test]
fn actual_native_status_frontdoor_ignores_scratch_home_and_refuses_foreign_namespace() {
    const ACTOR: &str = "TRUST_NATIVE_STATUS_CANONICAL_ACTOR";
    if let Some(mode) = std::env::var_os(ACTOR) {
        if mode == "foreign" {
            assert!(current().is_err());
        } else {
            let mut output = Vec::new();
            command(&["--json".into()], &mut output).unwrap();
            let value: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(value["protocol"], "native-resource-status-v1");
            let expected = resources::account_home().unwrap().join(".cache/build-slot");
            assert_eq!(
                value["legacy_namespace_bytes"],
                serde_json::json!(expected.as_os_str().as_bytes())
            );
        }
        return;
    }
    let fake = crate::owner_only::tempdir();
    let before = contents(fake.path());
    for mode in ["canonical", "foreign"] {
        let mut child = std::process::Command::new(std::env::current_exe().unwrap());
        child.args(["--exact", "admission::status::tests::actual_native_status_frontdoor_ignores_scratch_home_and_refuses_foreign_namespace", "--nocapture"])
            .env(ACTOR, mode).env("HOME", fake.path()).env_remove("BUILD_SLOT_DIR");
        if mode == "foreign" {
            child.env("BUILD_SLOT_DIR", fake.path());
        }
        let result = child.output().unwrap();
        assert!(
            result.status.success(),
            "{mode}: {}{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
    }
    assert_eq!(contents(fake.path()), before);
}

// Keep private lock/FD populations out of the parallel parent process. Each
// exact child retains the real process limit and executes every original
// assertion; no shared serialization, limit increase, or product gate changes.
fn isolated_status_fixture(name: &str, body: impl FnOnce()) {
    const ACTOR: &str = "TRUST_NATIVE_STATUS_FIXTURE_ACTOR";
    if std::env::var_os(ACTOR).as_deref() == Some(std::ffi::OsStr::new(name)) {
        body();
        println!("status fixture assertions completed: {name}");
        return;
    }
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", name, "--nocapture"])
        .env(ACTOR, name)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    while child.try_wait().unwrap().is_none() {
        if std::time::Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!("actual status fixture actor timed out: {name}");
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{name}: {output:?}");
    assert!(
        String::from_utf8_lossy(&output.stdout)
            .contains(&format!("status fixture assertions completed: {name}"))
    );
}
