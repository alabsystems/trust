use std::os::unix::fs::symlink;

use super::*;

fn fixture() -> (tempfile::TempDir, PathBuf) {
    let root = tempfile::tempdir().unwrap();
    let cache = root.path().join("crates/target.noindex/debug/incremental");
    fs::create_dir_all(&cache).unwrap();
    fs::write(cache.join("unit-cache"), b"rebuildable compiler cache").unwrap();
    (root, cache)
}

fn force() -> Thresholds {
    Thresholds { max_cache_bytes: 0, min_free_bytes: 0 }
}

fn reclaim_after_release(root: &Path, thresholds: Thresholds) -> Vec<Observation> {
    // Parallel process controls may inherit an original flock until exec.
    // Busy must retain the cache. Wait only after this test closes its owner;
    // do not force-unlock an inherited original description to obtain a pass.
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        let rows = reclaim(root, thresholds, true).unwrap();
        if rows.len() != 1 || rows[0].outcome != Outcome::Busy || Instant::now() >= deadline {
            return rows;
        }
        std::thread::sleep(Duration::from_millis(1));
    }
}

#[test]
fn report_observes_actual_volume_and_creates_no_locks_or_deletes() {
    let (root, cache) = fixture();
    let rows = reclaim(root.path(), force(), false).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].outcome, Outcome::WouldReclaim);
    assert!(rows[0].allocated_bytes.unwrap() > 0);
    assert!(rows[0].free_bytes.is_some());
    assert!(cache.join("unit-cache").is_file());
    assert!(!cache.parent().unwrap().join(LOCKS[0]).exists());
}

#[test]
fn actual_cargo_profile_locks_prevent_reclamation_and_remain_held() {
    for name in LOCKS {
        let (root, cache) = fixture();
        let path = cache.parent().unwrap().join(name);
        let holder = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(path)
            .unwrap();
        assert_eq!(unsafe { libc::flock(holder.as_raw_fd(), libc::LOCK_SH | libc::LOCK_NB) }, 0);
        for _ in 0..2 {
            let rows = reclaim(root.path(), force(), true).unwrap();
            assert_eq!(rows[0].outcome, Outcome::Busy, "{name}");
            assert!(cache.join("unit-cache").is_file());
        }
        drop(holder);
        let rows = reclaim_after_release(root.path(), force());
        assert_eq!(rows[0].outcome, Outcome::Reclaimed);
        assert!(!cache.exists());
    }
}

#[test]
fn supported_target_symlink_is_deduplicated_and_sysroots_are_untouched() {
    let (root, cache) = fixture();
    symlink("target.noindex", root.path().join("crates/target")).unwrap();
    let sysroot = root.path().join("build/stage1/bin/trustc");
    fs::create_dir_all(sysroot.parent().unwrap()).unwrap();
    fs::write(&sysroot, b"compiler image").unwrap();
    let rows = reclaim(root.path(), force(), true).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].outcome, Outcome::Reclaimed);
    assert!(!cache.exists());
    assert_eq!(fs::read(sysroot).unwrap(), b"compiler image");
}

#[test]
fn target_and_incremental_symlink_escapes_refuse_without_touching_outside() {
    for level in ["target", "incremental"] {
        let (root, cache) = fixture();
        let outside = tempfile::tempdir().unwrap();
        let external = outside.path().join("debug/incremental");
        fs::create_dir_all(&external).unwrap();
        fs::write(external.join("valuable"), b"outside").unwrap();
        if level == "target" {
            fs::remove_dir_all(root.path().join("crates/target.noindex")).unwrap();
            symlink(outside.path(), root.path().join("crates/target")).unwrap();
        } else {
            fs::remove_dir_all(&cache).unwrap();
            symlink(&external, &cache).unwrap();
        }
        let rows = reclaim(root.path(), force(), true).unwrap();
        assert_eq!(rows.len(), 1);
        assert!(matches!(rows[0].outcome, Outcome::Refused(_)));
        assert_eq!(fs::read(external.join("valuable")).unwrap(), b"outside");
    }
}

#[test]
fn threshold_keeps_warm_cache_and_interrupted_cleanup_uses_same_profile_locks() {
    crate::trust_output_lock::tests::isolated_case(
        "trust_repo_lock::incremental::tests::threshold_keeps_warm_cache_and_interrupted_cleanup_uses_same_profile_locks",
        || {
            let (root, cache) = fixture();
            let thresholds = Thresholds { max_cache_bytes: u64::MAX, min_free_bytes: 0 };
            let rows = reclaim(root.path(), thresholds, true).unwrap();
            assert_eq!(rows[0].outcome, Outcome::Kept);
            assert!(cache.join("unit-cache").exists());
            let garbage = cache.parent().unwrap().join("incremental.reclaim-previous");
            fs::rename(&cache, &garbage).unwrap();
            let holder = OpenOptions::new()
                .create(true)
                .truncate(false)
                .read(true)
                .write(true)
                .open(garbage.parent().unwrap().join(LOCKS[1]))
                .unwrap();
            assert_eq!(
                unsafe { libc::flock(holder.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) },
                0
            );
            assert_eq!(reclaim(root.path(), thresholds, true).unwrap()[0].outcome, Outcome::Busy);
            assert!(garbage.exists());
            drop(holder);
            let rows = reclaim_after_release(root.path(), thresholds);
            assert_eq!(rows[0].removed_interrupted_reclaims, 1);
            assert!(!garbage.exists());
            assert!(!cache.exists());
        },
    );
}

#[test]
fn lock_symlink_and_interrupted_symlink_refuse() {
    for name in [LOCKS[0], "incremental.reclaim-linked"] {
        let (root, cache) = fixture();
        let outside = tempfile::tempdir().unwrap();
        let valuable = outside.path().join("valuable");
        fs::write(&valuable, b"not cache").unwrap();
        symlink(&valuable, cache.parent().unwrap().join(name)).unwrap();
        let rows = reclaim(root.path(), force(), true).unwrap();
        assert!(matches!(rows[0].outcome, Outcome::Refused(_)));
        assert!(cache.exists());
        assert_eq!(fs::read(valuable).unwrap(), b"not cache");
    }
}

#[test]
fn allocated_size_deduplicates_hardlinks_and_never_follows_internal_symlinks() {
    let (root, cache) = fixture();
    let file = cache.join("unit-cache");
    let metadata = fs::symlink_metadata(&file).unwrap();
    let expected = metadata.blocks() * 512;
    fs::hard_link(&file, cache.join("same-cache-inode")).unwrap();
    assert_eq!(cache_bytes(&cache).unwrap(), expected);
    let outside = tempfile::tempdir().unwrap();
    fs::write(outside.path().join("valuable"), b"outside").unwrap();
    symlink(outside.path(), cache.join("external-link")).unwrap();
    assert_eq!(reclaim(root.path(), force(), true).unwrap()[0].outcome, Outcome::Reclaimed);
    assert_eq!(fs::read(outside.path().join("valuable")).unwrap(), b"outside");
}

#[test]
fn low_volume_rule_requires_at_least_one_gib_of_observed_cache() {
    let (root, cache) = fixture();
    let thresholds = Thresholds { max_cache_bytes: u64::MAX, min_free_bytes: u64::MAX };
    assert_eq!(reclaim(root.path(), thresholds, false).unwrap()[0].outcome, Outcome::Kept);
    // A valid zero-block sparse file is zero allocated payload, rather than a
    // GiB of actual cache allocation. No physical GiB is allocated by this test.
    File::create(cache.join("sparse-cache")).unwrap().set_len(GIB).unwrap();
    assert_eq!(fs::metadata(cache.join("sparse-cache")).unwrap().blocks(), 0);
    assert_eq!(reclaim(root.path(), thresholds, false).unwrap()[0].outcome, Outcome::Kept);
    assert!(cache.exists());
}

#[test]
fn observation_limits_refuse_incomplete_accounting_without_deleting() {
    let (_root, cache) = fixture();
    fs::create_dir_all(cache.join("deep/nested")).unwrap();
    fs::write(cache.join("deep/nested/state"), b"cache").unwrap();
    for mut budget in [
        WalkBudget { remaining: 0, ..WalkBudget::new() },
        WalkBudget { max_depth: 0, ..WalkBudget::new() },
        WalkBudget { until: Instant::now() - Duration::from_secs(1), ..WalkBudget::new() },
    ] {
        assert!(cache_bytes_with_budget(&cache, &mut budget).is_err());
        assert!(cache.join("deep/nested/state").exists());
    }
    let thresholds = Thresholds { max_cache_bytes: u64::MAX, min_free_bytes: 100 * GIB };
    assert!(!thresholds.selected(GIB - 1, 0));
    assert!(thresholds.selected(GIB, 0));
    assert!(!thresholds.selected(GIB, 100 * GIB));
}

#[test]
fn busy_writer_is_reported_before_recursive_cache_inspection() {
    let (root, cache) = fixture();
    let holder = try_lock_file(&cache.parent().unwrap().join(LOCKS[0])).unwrap().unwrap();
    // A malformed cache would refuse if recursive observation were attempted.
    // The existing live profile's exclusion must be observed first instead.
    fs::remove_dir_all(&cache).unwrap();
    fs::write(&cache, b"not a directory").unwrap();
    let rows = reclaim(root.path(), force(), true).unwrap();
    assert_eq!(rows[0].outcome, Outcome::Busy);
    assert!(rows[0].allocated_bytes.is_none());
    drop(holder);
    assert!(matches!(reclaim_after_release(root.path(), force())[0].outcome, Outcome::Refused(_)));
}

#[test]
fn one_observation_budget_covers_root_enumeration_and_all_profiles() {
    let (root, cache) = fixture();
    let second = root.path().join("crates/target-second/debug/incremental");
    fs::create_dir_all(&second).unwrap();
    fs::write(second.join("state"), b"another cache").unwrap();
    let mut cleanup = |_: &Path| -> io::Result<()> { panic!("report mode deleted a cache") };
    let mut budget = WalkBudget { remaining: 8, ..WalkBudget::new() };
    let rows =
        reclaim_with_budget_and_cleanup(root.path(), force(), false, &mut cleanup, &mut budget)
            .unwrap();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].outcome, Outcome::WouldReclaim);
    assert!(matches!(rows[1].outcome, Outcome::Refused(_)));
    assert!(rows[1].allocated_bytes.is_none());
    assert!(cache.exists() && second.exists());

    let mut no_entries = WalkBudget { remaining: 0, ..WalkBudget::new() };
    assert!(
        reclaim_with_budget_and_cleanup(root.path(), force(), true, &mut cleanup, &mut no_entries)
            .is_err()
    );
    assert!(cache.exists() && second.exists());
}

#[test]
fn final_time_check_does_not_charge_an_entry_or_accept_expiry() {
    let mut budget = WalkBudget { remaining: 0, ..WalkBudget::new() };
    assert!(budget.check_time().is_ok());
    assert_eq!(budget.remaining, 0);
    budget.until = Instant::now() - Duration::from_secs(1);
    assert!(budget.check_time().is_err());
    assert_eq!(budget.remaining, 0);
}

#[cfg(feature = "native-cli-tests")]
#[test]
fn actual_native_frontend_acquisition_reclaims_before_token_delivery_without_pipe_leaks() {
    use std::process::Command;
    let bootstrap = std::env::var_os("TRUST_BUILD_TREE_BOOTSTRAP")
        .expect("native-cli-tests requires the actual newly built Bootstrap executable");
    let targo = std::env::var_os("TRUST_BUILD_TREE_TARGO")
        .expect("native-cli-tests requires the actual newly built Targo executable");
    let protocol = Command::new(&bootstrap)
        .args(["--trust-build-tree-lock", "reclaim-incremental", "--protocol"])
        .output()
        .unwrap();
    assert!(protocol.status.success(), "{protocol:?}");
    assert_eq!(protocol.stdout, b"trust-incremental-reclamation-v1\n");
    let (root, cache) = fixture();
    // An earlier malformed target must not suppress a valid later cache.
    fs::create_dir_all(root.path().join("crates/target-a")).unwrap();
    fs::write(root.path().join("crates/target-a/debug"), b"not a directory").unwrap();
    let started = Instant::now();
    let acquired = Command::new(&targo)
        .args(["trust", "repo", "lock"])
        .args(["acquire", "--kind", "build", "--purpose", "native-reclaim-hook", "--pid"])
        .arg(std::process::id().to_string())
        .arg("--repo-root")
        .arg(root.path())
        .env("TRUST_REPO", root.path())
        .env("TRUST_INCREMENTAL_MAX_GIB", "0")
        .env("TRUST_INCREMENTAL_MIN_FREE_GIB", "0")
        .env_remove("TRUST_BUILD_LOCK_TOKEN")
        .env_remove("TRUST_BUILD_LOCK_BREAK")
        .output()
        .unwrap();
    assert!(acquired.status.success(), "{acquired:?}");
    assert!(
        started.elapsed() < Duration::from_secs(30),
        "detached output pipes delayed acquisition"
    );
    let token = String::from_utf8_lossy(&acquired.stdout);
    assert_eq!(token.lines().count(), 1);
    // Native maintenance finishes before the real owner delivers its token;
    // there is no detached helper, log poll or inherited output pipe to wait on.
    assert!(!cache.exists(), "{acquired:?}");
    assert!(String::from_utf8_lossy(&acquired.stderr).contains("Reclaimed"), "{acquired:?}");
    let released = Command::new(&targo)
        .args(["trust", "repo", "lock", "release", token.trim(), "--repo-root"])
        .arg(root.path())
        .env("TRUST_REPO", root.path())
        .output()
        .unwrap();
    assert!(released.status.success(), "{released:?}");
    assert!(!root.path().join(".trust-build-lock").exists());
}

#[cfg(feature = "native-cli-tests")]
#[test]
fn preflight_unavailable_provider_never_invokes_a_potentially_installing_targo_shim() {
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;
    let root = tempfile::tempdir().unwrap();
    let bin = root.path().join("bin");
    fs::create_dir(&bin).unwrap();
    let shim = bin.join("targo");
    // This is a noninvocation canary, not a fake SDK or capability provider.
    fs::write(&shim, b"#!/bin/sh\nprintf invoked > \"$NATIVE_SHIM_CANARY\"\nexit 99\n").unwrap();
    fs::set_permissions(&shim, fs::Permissions::from_mode(0o700)).unwrap();
    let marker = root.path().join("shim-was-invoked");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
    let script = fs::read_to_string(repository.join("scripts/machine_preflight.sh")).unwrap();
    // Execute the exact checked-in function; avoid unrelated machine-wide
    // inspection and use an owned empty root with no native provider.
    let name = "native_incremental_preflight() {";
    let body = script.split_once(name).unwrap().1.split_once("\n}\n").unwrap().0;
    let command = format!(
        "note() {{ printf '%s\\n' \"$1\"; }}\n{name}{body}\n}}\nnative_incremental_preflight\n"
    );
    let output = Command::new("/bin/sh")
        .args(["-c", &command])
        .env("ROOT", root.path())
        .env_remove("TRUST_BUILD_TREE_BOOTSTRAP")
        .env("PATH", &bin)
        .env("NATIVE_SHIM_CANARY", &marker)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(!marker.exists(), "read-only preflight invoked the SDK-installing shim");
}

#[test]
fn cleanup_releases_cargo_locks_before_deleting_detached_state_and_keeps_next_cache() {
    crate::trust_output_lock::tests::isolated_case(
        "trust_repo_lock::incremental::tests::cleanup_releases_cargo_locks_before_deleting_detached_state_and_keeps_next_cache",
        || {
            let (root, cache) = fixture();
            let profile = cache.parent().unwrap().to_owned();
            let old = profile.join("incremental.reclaim-interrupted");
            fs::rename(&cache, &old).unwrap();
            let mut cleanups = 0;
            let mut cleanup = |garbage: &Path| {
                let locks =
                    profile_locks(&profile)?.expect("deletion retained Cargo profile locks");
                fs::create_dir_all(&cache)?;
                fs::write(cache.join("next-build"), b"new compiler cache")?;
                drop(locks);
                cleanups += 1;
                fs::remove_dir_all(garbage)
            };
            let rows = reclaim_with_cleanup(root.path(), force(), true, &mut cleanup).unwrap();
            assert_eq!(cleanups, 1);
            assert_eq!(rows[0].removed_interrupted_reclaims, 1);
            assert_eq!(fs::read(cache.join("next-build")).unwrap(), b"new compiler cache");
        },
    );
}

#[test]
fn native_free_space_counts_refuse_negative_and_overflow_without_losing_zero() {
    assert!(checked_free_product(-1_i64, 4096_u32).is_err());
    assert!(checked_free_product(u64::MAX, 2_u32).is_err());
    assert_eq!(checked_free_product(0_u32, u64::MAX).unwrap(), 0);
    assert_eq!(checked_free_product(2_u32, 4096_u64).unwrap(), 8192);
}
