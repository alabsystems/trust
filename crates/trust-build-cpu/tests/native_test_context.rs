// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

// Trust: this is deliberately absent from ordinary unit-test qualification.
// Run it through native `targo --unverified test --test native_test_context`,
// so the production test-action graph must supply real resources.
#[test]
#[ignore = "requires a live protocol-2 workers-v1 native test-action graph"]
fn live_native_test_child_has_checked_serial_resources() -> anyhow::Result<()> {
    use std::ffi::OsStr;
    use std::fs::File;
    use std::os::fd::AsFd;
    use std::os::unix::fs::MetadataExt;
    use std::path::PathBuf;
    use std::time::Duration;

    use anyhow::Context as _;
    use jobserver_utils::{CPU_HANDOFF_ENV, recover_cpu_resources};
    use trust_build_cpu::{
        IMPLICIT_FD_ENV, LegacyFence, Pool, SlotState, capacity_dir, duplicate_descriptor,
        duplicate_descriptors,
    };

    let required = |name: &str| {
        std::env::var_os(name).unwrap_or_else(|| panic!("live native test child is missing {name}"))
    };
    for (name, expected) in [
        ("BUILD_SLOT_CPU_PROTOCOL", "2"),
        ("BUILD_SLOT_CPU_MODE", "workers-v1"),
        ("NUM_JOBS", "1"),
        ("CARGO_BUILD_JOBS", "1"),
        ("TARGO_PLANNED_JOBS", "1"),
        ("RUST_TEST_THREADS", "1"),
    ] {
        assert_eq!(required(name), OsStr::new(expected), "{name}");
    }

    // Duplicate advertised descriptors without taking ownership of raw
    // numbers. The validators below must establish their actual identity.
    let direct_cpu = duplicate_descriptor(&required(IMPLICIT_FD_ENV))?;
    let direct_fences = duplicate_descriptors(&required("BUILD_SLOT_FENCE_FDS"))?;
    let flags = required("CARGO_MAKEFLAGS");
    let auth = flags
        .to_str()
        .context("live serial jobserver flags are not UTF-8")?
        .split_whitespace()
        .find_map(|part| part.strip_prefix("--jobserver-auth="))
        .context("live test child has no serial jobserver advertisement")?;
    let (read, write) =
        auth.split_once(',').context("live test child must inherit the serial GNU pipe")?;
    let read = duplicate_descriptor(OsStr::new(read))?;
    let write = duplicate_descriptor(OsStr::new(write))?;
    let server = jobserver::Client::from_pipe(read.as_fd(), write.as_fd())?;
    assert_eq!(server.available()?, 0, "the owned root is the only credit");

    let legacy = PathBuf::from(required("BUILD_SLOT_LEGACY_DIR"));
    assert!(legacy.is_absolute());
    assert_eq!(PathBuf::from(required("BUILD_SLOT_DIR")), legacy);
    assert_eq!(PathBuf::from(required("BUILD_SLOT_V2_DIR")), legacy.join("runtime-v2"));
    let slots: u32 = required("BUILD_SLOT_POOL_SLOTS")
        .to_str()
        .context("live legacy fence width is not UTF-8")?
        .parse()?;
    // Open only the real account's existing pool. This test cannot create
    // a replacement namespace, acquire capacity, or repair absent grants.
    let pool = Pool::open_existing(&capacity_dir()?)?
        .context("live test child has no existing global CPU pool")?;
    let direct_lease = pool.adopt_inherited(direct_cpu)?;
    let direct_fence = LegacyFence::from_inherited(&legacy, slots, direct_fences)?;

    // Exercise the authenticated live-ancestor path even when the direct
    // descriptors survived exec. Advertisement text alone cannot pass.
    let (cpu, fences) = recover_cpu_resources(&required(CPU_HANDOFF_ENV))?;
    let recovered_lease = pool.adopt_inherited(File::from(cpu))?;
    let recovered_fence =
        LegacyFence::from_inherited(&legacy, slots, fences.into_iter().map(File::from).collect())?;
    assert_eq!(direct_lease.slot(), recovered_lease.slot());
    let identities = |fence: &LegacyFence| -> std::io::Result<Vec<_>> {
        fence
            .files()
            .iter()
            .map(|file| file.metadata().map(|metadata| (metadata.dev(), metadata.ino())))
            .collect()
    };
    assert_eq!(identities(&direct_fence)?, identities(&recovered_fence)?);
    assert!(pool.snapshot()?.iter().any(|state| {
        matches!(state, SlotState::Held { slot, .. } if *slot == direct_lease.slot())
    }));

    eprintln!(
        "live native test context validated: pid={} slot={} extra_tokens=0",
        std::process::id(),
        direct_lease.slot()
    );
    // Give the outer qualifier a bounded opportunity to observe the real
    // actor. This is not a timing or throughput assertion.
    std::thread::sleep(Duration::from_secs(2));
    assert_eq!(server.available()?, 0, "no extra GNU token may appear");
    assert!(pool.snapshot()?.iter().any(|state| {
        matches!(state, SlotState::Held { slot, .. } if *slot == recovered_lease.slot())
    }));
    Ok(())
}
