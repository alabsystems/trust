use super::*;

fn host(cpus: u32, total: u64, available: u64) -> Host {
    Host {
        platform: "fixture-data",
        cpus,
        physical_memory_bytes: total,
        available_memory_bytes: available.min(total),
        available_memory_source: "fixture-data-only",
        load_one: None,
    }
}

#[test]
fn every_workload_keeps_the_complete_memory_and_cpu_bounds() {
    for cpus in [1, 7, 32, 128] {
        for total in [2 * GIB, 24 * GIB, 128 * GIB, u64::MAX] {
            for available in [0, GIB / 4, total / 2, total] {
                for workload in [
                    Workload::RustcBuild,
                    Workload::UiTest,
                    Workload::CratesTest,
                    Workload::FastLane,
                ] {
                    let report =
                        observed(host(cpus, total, available), &Request::new(workload), None);
                    let plan = report.plan;
                    assert_eq!(plan.reserve_bytes, GIB.max(total / 8));
                    assert_eq!(plan.room_bytes, available.saturating_sub(plan.reserve_bytes));
                    if plan.outcome == Outcome::FitsMeasuredMemory {
                        assert!((1..=cpus).contains(&plan.jobs));
                        assert!(plan.cap_bytes >= plan.floor_bytes);
                        assert!(u64::from(plan.jobs) * plan.cap_bytes <= plan.room_bytes);
                        assert!(plan.room_bytes <= available);
                    } else {
                        assert_eq!((plan.jobs, plan.cap_bytes), (0, 0));
                        assert!(plan.room_bytes < plan.floor_bytes);
                    }
                }
            }
        }
    }
}

#[test]
fn reduced_original_and_caller_ceiling_never_multiply_the_same_share() {
    let mut request = Request::new(Workload::RustcBuild);
    request.maximum_jobs = NonZeroU32::new(3);
    let report = observed(host(32, 128 * GIB, 100 * GIB), &request, NonZeroU32::new(7));
    assert_eq!(report.cpu_scope, CpuScope::OriginalFixed { ceiling: 7 });
    assert_eq!(report.plan.cpu_bound, 7);
    assert_eq!(report.plan.jobs, 3);
    assert_eq!(report.overlap, Some(Overlap::OriginalFixedRequiresSerial));
    request.maximum_jobs = NonZeroU32::new(100);
    assert_eq!(observed(host(32, 128 * GIB, 100 * GIB), &request, NonZeroU32::new(7)).plan.jobs, 7);
}

#[test]
fn below_want_keeps_one_real_floor_and_unknown_is_not_a_zero_reading() {
    let request = Request::new(Workload::RustcBuild);
    let report = observed(host(8, 8 * GIB, 3 * GIB), &request, None);
    assert_eq!(report.plan.jobs, 1);
    assert_eq!(report.plan.cap_bytes, 2 * GIB);
    assert_eq!(report.plan.outcome, Outcome::FitsMeasuredMemory);
    for invalid in [
        "",
        "MemTotal: 0 kB\n",
        "MemTotal: 2 GB\n",
        "MemTotal: -1 kB\n",
        "MemTotal: 1 kB\nMemTotal: 1 kB\n",
        "MemTotal: 18446744073709551615 kB\n",
    ] {
        assert!(native::physical_from_meminfo(invalid).is_err());
    }
    assert_eq!(native::physical_from_meminfo("MemTotal: 42 kB\nOther: 1 kB\n").unwrap(), 42 * 1024);
    let json = serde_json::to_value(&report).unwrap();
    assert!(json["host"]["load_one"].is_null());
    assert_eq!(json["authority"], "policy_data_only_no_admission");
}

#[test]
fn governor_and_overlap_remain_policy_observations() {
    let request = Request::new(Workload::RustcBuild);
    let small = observed(host(14, 24 * GIB, 14 * GIB), &request, None);
    assert_eq!((small.governor.critical_gib, small.governor.resume_gib), (2, 3));
    assert_eq!(small.overlap, Some(Overlap::BelowFullCpuMemoryWant));
    let large = observed(host(20, 128 * GIB, 100 * GIB), &request, None);
    assert_eq!((large.governor.critical_gib, large.governor.resume_gib), (8, 16));
    assert_eq!(large.overlap, Some(Overlap::FitsMeasuredMemory));
    let unrelated = observed(host(20, 128 * GIB, 100 * GIB), &Request::new(Workload::UiTest), None);
    assert_eq!(unrelated.overlap, None);
}

#[test]
fn actual_native_measurement_opens_no_coordination_namespace() {
    const NAME: &str =
        "admission::budget::tests::actual_native_measurement_opens_no_coordination_namespace";
    const ROOT: &str = "TRUST_BUDGET_READONLY_ACTOR";
    if let Some(root) = std::env::var_os(ROOT) {
        let root = std::path::Path::new(&root);
        assert_eq!(std::fs::read_dir(root).unwrap().count(), 0);
        let report = current(&Request::new(Workload::FastLane), None).unwrap();
        assert!(report.host.cpus > 0 && report.host.physical_memory_bytes > 0);
        assert_eq!(report.cpu_scope, CpuScope::UnmanagedPolicy);
        assert_eq!(std::fs::read_dir(root).unwrap().count(), 0);
        println!("native-budget-observed");
        return;
    }
    let root = tempfile::tempdir().unwrap();
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", NAME, "--nocapture"])
        .env(ROOT, root.path())
        .env("HOME", root.path())
        .env("BUILD_SLOT_DIR", root.path().join("absent-namespace"))
        .output()
        .unwrap();
    assert!(output.status.success(), "native readonly observation actor failed: {output:?}");
    assert!(String::from_utf8(output.stdout).unwrap().contains("native-budget-observed"));
    assert_eq!(std::fs::read_dir(root.path()).unwrap().count(), 0);
}
