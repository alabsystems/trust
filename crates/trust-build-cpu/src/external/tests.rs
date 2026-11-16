use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt, symlink};

use super::*;

fn record(dir: &Path, name: &str, text: &str, lock: bool) -> File {
    let mut file = OpenOptions::new()
        .create_new(true)
        .read(true)
        .write(true)
        .mode(0o600)
        .open(dir.join(name))
        .unwrap();
    file.write_all(text.as_bytes()).unwrap();
    if lock {
        file.lock().unwrap();
    }
    file
}

fn row(mode: &str, budget: u32, lease: char) -> String {
    serde_json::json!({"cpu_mode":mode,"cpu_budget":budget,"pool_slots":4,
        "lease_id":lease.to_string().repeat(32)})
    .to_string()
}

#[test]
fn fixed_leases_deduplicate_and_cooperating_workers_are_separate() {
    let _fixture = crate::tests::kernel_fixture();
    let dir = crate::tests::private_tempdir();
    let _first = record(dir.path(), "slot-0", &row("fixed-v1", 14, 'a'), true);
    let _second = record(dir.path(), "slot-1", &row("fixed-v1", 14, 'a'), true);
    let _worker = record(dir.path(), "slot-2", &row("workers-v1", 7, 'b'), true);
    let _stale = record(dir.path(), "slot-3", "not json", false);
    assert_eq!(reserved_cpus(dir.path(), 28, 4).unwrap(), 14);
    drop(_first);
    drop(_second);
    assert_eq!(reserved_cpus(dir.path(), 28, 4).unwrap(), 0);
}

#[test]
fn exclusive_fence_and_unknown_live_metadata_veto_new_workers() {
    let _fixture = crate::tests::kernel_fixture();
    let dir = crate::tests::private_tempdir();
    let fence = record(dir.path(), "admission.lock", "{}", true);
    assert_eq!(reserved_cpus(dir.path(), 28, 4).unwrap(), 28);
    drop(fence);
    let _unknown = record(dir.path(), "slot-0", "bad", true);
    assert_eq!(reserved_cpus(dir.path(), 28, 4).unwrap(), 28);
}

#[test]
fn inherited_duplicate_stays_reserved_and_legacy_has_a_fixed_share() {
    let _fixture = crate::tests::kernel_fixture();
    let dir = crate::tests::private_tempdir();
    let lease = record(
        dir.path(),
        "slot-0",
        r#"{"pid":4,"cmd":"legacy","cwd":"/fixture","started":0}"#,
        true,
    );
    let inherited = lease.try_clone().unwrap();
    drop(lease);
    assert_eq!(reserved_cpus(dir.path(), 28, 4).unwrap(), 7);
    drop(inherited);
    assert_eq!(reserved_cpus(dir.path(), 28, 4).unwrap(), 0);
}

#[test]
fn unsafe_files_and_symlinks_are_not_treated_as_free_capacity() {
    let _fixture = crate::tests::kernel_fixture();
    let dir = crate::tests::private_tempdir();
    let original = record(dir.path(), "original", "{}", true);
    symlink(dir.path().join("original"), dir.path().join("slot-0")).unwrap();
    assert!(reserved_cpus(dir.path(), 28, 4).is_err());
    std::fs::remove_file(dir.path().join("slot-0")).unwrap();
    drop(original);
    let _unsafe = record(dir.path(), "slot-0", "{}", false);
    std::fs::set_permissions(dir.path().join("slot-0"), std::fs::Permissions::from_mode(0o666))
        .unwrap();
    assert!(reserved_cpus(dir.path(), 28, 4).is_err());
}

fn width(value: u32) -> std::num::NonZeroU32 {
    std::num::NonZeroU32::new(value).unwrap()
}

#[test]
fn known_full_host_and_unknown_live_records_have_distinct_native_readiness() {
    use std::io::{Seek, SeekFrom};
    let _fixture = crate::tests::kernel_fixture();
    let native = crate::tests::private_tempdir();
    let pool = crate::Pool::open_in(native.path(), width(4)).unwrap();
    let external = crate::tests::private_tempdir();
    let mut fixed = record(external.path(), "slot-0", &row("fixed-v1", 4, 'a'), true);
    assert_eq!(
        pool.observe_legacy_fixed_room(external.path(), width(4), None).unwrap(),
        LegacyFixedRoom::Fits { native_held: 0, external_reserved: 4, capacity: 4 }
    );
    fixed.set_len(0).unwrap();
    fixed.seek(SeekFrom::Start(0)).unwrap();
    fixed.write_all(b"unknown live record").unwrap();
    assert_eq!(
        pool.observe_legacy_fixed_room(external.path(), width(4), None).unwrap(),
        LegacyFixedRoom::UnknownExternal
    );
    fixed.set_len(0).unwrap();
    fixed.seek(SeekFrom::Start(0)).unwrap();
    fixed.write_all(row("fixed-v1", 4, 'a').as_bytes()).unwrap();
    let _lease = pool.try_acquire(crate::Owner::current(None)).unwrap().unwrap();
    let before = pool.snapshot().unwrap();
    assert_eq!(
        pool.observe_legacy_fixed_room(external.path(), width(4), None).unwrap(),
        LegacyFixedRoom::OverCapacity { native_held: 1, external_reserved: 4, capacity: 4 }
    );
    assert_eq!(pool.snapshot().unwrap(), before, "observer acquired or released native CPU work");
}

#[test]
fn complete_fixed_totals_are_not_clamped_into_an_apparent_fit() {
    let _fixture = crate::tests::kernel_fixture();
    let native = crate::tests::private_tempdir();
    let pool = crate::Pool::open_in(native.path(), width(4)).unwrap();
    let external = crate::tests::private_tempdir();
    let _first = record(external.path(), "slot-0", &row("fixed-v1", 4, 'a'), true);
    let _second = record(external.path(), "slot-1", &row("fixed-v1", 4, 'b'), true);
    assert_eq!(
        pool.observe_legacy_fixed_room(external.path(), width(4), None).unwrap(),
        LegacyFixedRoom::OverCapacity { native_held: 0, external_reserved: 8, capacity: 4 }
    );
}

#[test]
fn only_original_exclusive_admission_description_can_continue_its_fence() {
    let _fixture = crate::tests::kernel_fixture();
    let native = crate::tests::private_tempdir();
    let pool = crate::Pool::open_in(native.path(), width(4)).unwrap();
    let external = crate::tests::private_tempdir();
    let fence = record(external.path(), "admission.lock", "{}", true);
    let _fixed = record(external.path(), "slot-0", &row("fixed-v1", 4, 'a'), true);
    let foreign = OpenOptions::new()
        .read(true)
        .write(true)
        .open(external.path().join("admission.lock"))
        .unwrap();
    for supplied in [None, Some(&foreign)] {
        assert_eq!(
            pool.observe_legacy_fixed_room(external.path(), width(4), supplied).unwrap(),
            LegacyFixedRoom::UnknownExternal
        );
    }
    let original_copy = fence.try_clone().unwrap();
    assert_eq!(
        pool.observe_legacy_fixed_room(external.path(), width(4), Some(&original_copy)).unwrap(),
        LegacyFixedRoom::Fits { native_held: 0, external_reserved: 4, capacity: 4 }
    );
    assert!(foreign.try_lock().is_err(), "original fence was downgraded or released");
}

#[test]
fn manifest_contention_and_activated_debt_never_report_legacy_readiness() {
    let _fixture = crate::tests::kernel_fixture();
    let native = crate::tests::private_tempdir();
    let pool = crate::Pool::open_in(native.path(), width(4)).unwrap();
    let external = crate::tests::private_tempdir();
    let manifest = OpenOptions::new().read(true).open(pool.path().join("pool")).unwrap();
    manifest.lock().unwrap();
    assert_eq!(
        pool.observe_legacy_fixed_room(external.path(), width(4), None).unwrap(),
        LegacyFixedRoom::Busy
    );
    drop(manifest);
    crate::tests::private_file(&pool.path().join("external-debt-v1"), "incomplete activation");
    assert!(pool.observe_legacy_fixed_room(external.path(), width(4), None).is_err());
}

#[test]
fn duplicate_fields_are_unknown_even_when_the_last_budget_would_fit() {
    let _fixture = crate::tests::kernel_fixture();
    let native = crate::tests::private_tempdir();
    let pool = crate::Pool::open_in(native.path(), width(4)).unwrap();
    let external = crate::tests::private_tempdir();
    let text = format!(
        "{{\"cpu_mode\":\"fixed-v1\",\"cpu_budget\":4,\"cpu_budget\":1,\"pool_slots\":4,\"lease_id\":\"{}\"}}",
        "a".repeat(32)
    );
    let _fixed = record(external.path(), "slot-0", &text, true);
    assert_eq!(
        pool.observe_legacy_fixed_room(external.path(), width(4), None).unwrap(),
        LegacyFixedRoom::UnknownExternal
    );
}
