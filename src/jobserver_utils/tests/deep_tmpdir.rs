//! Trust (JOBSERVER-HANDOFF-SUN-LEN-1): a scheduler whose `TMPDIR` is too deep for a
//! Unix socket path still advertises its descendant endpoint. Before, the seed mint
//! (`TMPDIR=<checkout>/build/.mint-and-prove.*/environment-mint/tmp`, 83 bytes from a
//! 31-byte checkout path) warned "jobserver descendant handoff unavailable: path must
//! be shorter than SUN_LEN", and rust-analyzer's `proc-macro-test` build script, which
//! starts a nested Cargo with a plain spawn, died on "cannot inherit Targo jobserver".
//!
//! Its own test binary: it sets `TMPDIR` for the whole process before anything reads it.

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::process::Command;

#[test]
fn a_scheduler_under_a_deep_tmpdir_advertises_its_descendant_endpoint() {
    let mut deep = std::env::temp_dir().join(format!("tjs-deep-{}", std::process::id()));
    // 8 x 17 bytes past the system temporary directory: past every `sun_path` (104/108).
    for _ in 0..8 {
        deep.push("environment-mint");
    }
    std::fs::create_dir_all(&deep).unwrap();
    // SAFETY: this binary's only test sets it before any thread or temp_dir() reads it.
    unsafe { std::env::set_var("TMPDIR", &deep) };
    assert_eq!(std::env::temp_dir(), deep);

    let mut server = jobserver_utils::Jobserver::new(1).unwrap();
    server.enable_descendant_handoff().expect("the endpoint is created under the short base");
    let mut command = Command::new("__metadata_only__");
    server.configure(&mut command);
    let advertised = command
        .get_envs()
        .find_map(|(key, value)| (key == jobserver_utils::DESCENDANT_HANDOFF_ENV).then_some(value))
        .flatten()
        .expect("a configured child carries the recovery advertisement");
    assert!(!advertised.is_empty());

    drop(server);
    let mut top = deep.as_path();
    while top.file_name().is_some_and(|name| name == "environment-mint") {
        top = top.parent().unwrap();
    }
    std::fs::remove_dir_all(top).unwrap();
}
