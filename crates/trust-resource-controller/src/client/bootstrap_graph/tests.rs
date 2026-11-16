use super::*;

#[test]
fn native_work_after_root_budget_expires_cannot_renew_from_receipt_time() {
    let started = Instant::now();
    let bound = original_deadline(started, 5_000_000).unwrap();
    assert_eq!(bound, started + Duration::from_millis(5));
    std::thread::sleep(Duration::from_millis(20));
    let _native = trust_resource_provenance::process::read_identity(std::process::id()).unwrap();
    assert_eq!(original_deadline(started, 5_000_000).unwrap_err().kind(), io::ErrorKind::TimedOut);
    assert_eq!(time(bound).unwrap_err().kind(), io::ErrorKind::TimedOut);
}

#[test]
fn original_graph_bound_and_rpc_deadline_remain_distinct_restrictions() {
    let started = Instant::now();
    let root = original_deadline(started, 60_000_000_000).unwrap();
    let rpc = started + Duration::from_secs(8);
    assert!(root > rpc);
    bounded(root, rpc).unwrap();
    assert_eq!(
        bounded(root, root + Duration::from_nanos(1)).unwrap_err().kind(),
        io::ErrorKind::InvalidInput
    );
    assert_eq!(original_deadline(started, 0).unwrap_err().kind(), io::ErrorKind::TimedOut);
}

#[test]
fn final_actual_native_observations_remain_under_the_unchanged_bound() {
    let until = Instant::now() + Duration::from_millis(5);
    let observed = finish(until, || {
        std::thread::sleep(Duration::from_millis(20));
        std::fs::File::open("/dev/null")?.metadata()?;
        trust_resource_provenance::process::read_identity(std::process::id())
    });
    assert_eq!(observed.unwrap_err().kind(), io::ErrorKind::TimedOut);
}
