use std::fs::File;

use super::*;

#[test]
fn exact_actual_proc_leaf_is_accepted_but_other_leaf_is_refused() {
    let statm = File::open("/proc/self/statm").unwrap();
    let same = File::open(format!("/proc/{}/statm", std::process::id())).unwrap();
    let status = File::open("/proc/self/status").unwrap();
    assert!(exact(statm.as_raw_fd(), same.as_raw_fd()).is_ok());
    assert!(exact(status.as_raw_fd(), same.as_raw_fd()).is_err());
}

#[test]
fn swapped_global_role_and_nonproc_file_are_refused() {
    let statm = File::open("/proc/self/statm").unwrap();
    let meminfo = File::open("/proc/meminfo").unwrap();
    let null = File::open("/dev/null").unwrap();
    assert!(exact(meminfo.as_raw_fd(), meminfo.as_raw_fd()).is_ok());
    assert!(exact(meminfo.as_raw_fd(), statm.as_raw_fd()).is_err());
    assert!(exact(null.as_raw_fd(), statm.as_raw_fd()).is_err());
}
