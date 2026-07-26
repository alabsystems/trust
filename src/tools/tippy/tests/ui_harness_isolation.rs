use std::ffi::OsString;

mod test_utils;

use test_utils::{bootstrap_dependency_builder_env, reject_trust_frontend_controls};

#[test]
fn ordinary_diagnostic_arguments_reach_the_driver_untouched() {
    reject_trust_frontend_controls(&[
        OsString::from("-Dwarnings"),
        OsString::from("--emit=metadata"),
        OsString::from("-Zui-testing"),
    ]);
}

#[test]
#[should_panic(expected = "no-evidence lint frontend rejects it")]
fn a_trust_control_in_the_driver_arguments_fails_the_harness() {
    reject_trust_frontend_controls(&[OsString::from("-Dwarnings"), OsString::from("-Ztrust-verify=off")]);
}

#[test]
fn dependency_builder_restores_supplemental_shim_context_and_isolates_all_units() {
    assert_eq!(
        bootstrap_dependency_builder_env("1", "aarch64-apple-darwin", "1"),
        [
            (OsString::from("RUSTC_STAGE"), Some(OsString::from("1"))),
            (
                OsString::from("CFG_COMPILER_BUILD_TRIPLE"),
                Some(OsString::from("aarch64-apple-darwin")),
            ),
            (
                OsString::from("RUSTC_LINK_STD_INTO_RUSTC_DRIVER"),
                Some(OsString::from("1")),
            ),
            (
                OsString::from("TRUST_BOOTSTRAP_SHIM_NO_VERIFY"),
                Some(OsString::from("1")),
            ),
            (OsString::from("TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY"), None),
        ]
    );
}
