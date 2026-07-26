use super::stable_trust_compat_z_options;

#[test]
fn stable_trust_compat_z_options_allow_only_the_verification_switch() {
    fn allowed(options: &[&str]) -> bool {
        let options = options.iter().map(|option| option.to_string()).collect::<Vec<_>>();
        stable_trust_compat_z_options(&options)
    }

    assert!(allowed(&["trust-verify"]));
    assert!(allowed(&["trust-verify=off"]));
    assert!(!allowed(&[]));
    assert!(!allowed(&["unstable-options"]));
    assert!(!allowed(&["trust-verify", "treat-err-as-bug=1"]));
}
