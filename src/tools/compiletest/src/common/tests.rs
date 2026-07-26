use std::ffi::OsStr;
use std::process::Command;

use super::{TRUST_VANILLA_RUSTC_FLAG, configure_trust_verification_isolation};

fn args(command: &Command) -> Vec<&OsStr> {
    command.get_args().collect()
}

#[test]
fn trust_isolation_is_capability_scoped_and_overridable() {
    let mut upstream = Command::new("rustc");
    configure_trust_verification_isolation(&mut upstream, false);
    assert!(args(&upstream).is_empty());

    let mut trust = Command::new("rustc");
    configure_trust_verification_isolation(&mut trust, true);
    trust.arg("-Ztrust-verify=on");
    assert_eq!(
        args(&trust),
        [OsStr::new(TRUST_VANILLA_RUSTC_FLAG), OsStr::new("-Ztrust-verify=on")]
    );

    // An auxiliary boundary must override a primary test's opt-in. Any
    // dedicated auxiliary flags are appended after this and can opt in
    // deliberately rather than inheriting verification accidentally.
    configure_trust_verification_isolation(&mut trust, true);
    assert_eq!(
        args(&trust),
        [
            OsStr::new(TRUST_VANILLA_RUSTC_FLAG),
            OsStr::new("-Ztrust-verify=on"),
            OsStr::new(TRUST_VANILLA_RUSTC_FLAG),
        ]
    );
}
