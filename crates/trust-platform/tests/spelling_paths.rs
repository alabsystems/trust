// Copyright 2026 Andrew Yates. License: MIT OR Apache-2.0.
// These are fixture strings only: the test does not access either directory.
#[path = "conformance_darwin/spelling_paths.rs"]
mod spelling_paths;

#[test]
fn aliases_remain_different_spellings_for_private_and_home_temp_roots() {
    for canon in ["/private/var/tmp/trust-spelling", "<home>/trust-spelling"] {
        let target = format!("{canon}/Lease.lock");
        let aliases = spelling_paths::spelling_aliases(canon);
        assert_eq!(aliases.len(), if canon.starts_with("/private") { 5 } else { 4 });
        for alias in &aliases {
            let spelling =
                if alias.starts_with('/') { alias.clone() } else { format!("{canon}/{alias}") };
            assert_ne!(spelling, target, "fixture must supply a different spelling under {canon}");
        }
        assert!(
            aliases.iter().any(|alias| alias.contains("//")),
            "the duplicate-separator case must exist under {canon}"
        );
    }
}
