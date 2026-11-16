use std::ffi::OsStr;
use std::process::Command;

use super::isolate_fixture_build;

#[test]
fn fixture_builds_run_on_the_isolated_lane() {
    let mut cargo = Command::new("cargo");
    isolate_fixture_build(&mut cargo);
    let env: Vec<_> = cargo.get_envs().collect();
    assert!(env.contains(&(OsStr::new("RUSTFLAGS"), Some(OsStr::new("-Ztrust-verify=off")))));
    assert!(env.contains(&(OsStr::new("TRUST_VANILLA_ANNOUNCED"), Some(OsStr::new("1")))));
}
