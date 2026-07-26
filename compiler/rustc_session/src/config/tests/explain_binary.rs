use super::explain_binary_for_invoked_name;

#[test]
fn diagnostic_hints_name_the_paired_compiler() {
    assert_eq!(explain_binary_for_invoked_name(Some("rustc")), "rustc");
    assert_eq!(explain_binary_for_invoked_name(Some("rustdoc")), "rustc");
    assert_eq!(explain_binary_for_invoked_name(Some("trustc")), "trustc");
    assert_eq!(explain_binary_for_invoked_name(Some("trustdoc")), "trustc");
    assert_eq!(explain_binary_for_invoked_name(Some("custom-trust-driver")), "trustc");
    assert_eq!(explain_binary_for_invoked_name(None), "trustc");
}
