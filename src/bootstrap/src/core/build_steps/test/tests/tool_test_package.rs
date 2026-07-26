use super::{targo_test_packages, trustfmt_test_packages};

#[test]
fn standard_targo_tests_select_every_package_with_a_unit_suite() {
    assert_eq!(
        targo_test_packages(),
        [
            "cargo",
            "build-rs-test-lib",
            "cargo-credential",
            "cargo-platform",
            "cargo-test-support",
            "cargo-util",
            "cargo-util-schemas",
            "mdman",
            "resolver-tests",
            "rustfix",
            "xtask-bump-check",
        ]
    );
}

#[test]
fn standard_trustfmt_tests_include_config_macro_contracts() {
    assert_eq!(trustfmt_test_packages(), ["rustfmt-nightly", "rustfmt-config_proc_macro"]);
}
