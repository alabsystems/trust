use super::tippy_test_packages;

#[test]
fn standard_tippy_tests_select_every_package_with_a_unit_suite() {
    assert_eq!(
        tippy_test_packages(),
        [
            "tippy",
            "clippy_config",
            "clippy_utils",
            "clippy_lints",
            "rustc_tools_util",
            "clippy_dev",
        ]
    );
}
