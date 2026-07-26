use std::path::PathBuf;

use super::parse::{
    parse_trust_cg_output_gate, parse_trust_nonempty_path, parse_trust_verify_crate_role,
    parse_trust_verify_level, parse_trust_verify_output, parse_trust_verify_package_name,
    parse_trust_verify_profile, parse_trust_verify_session,
    parse_trust_verify_target_spec_sha256, parse_trust_verify_timeout_ms,
    parse_trust_verify_worker_threads,
};

#[test]
fn raw_trustc_defaults_match_the_canonical_frontend_policy() {
    let opts = super::Options::default();
    assert_eq!(opts.unstable_opts.trust_verify_level, 2);
    assert_eq!(opts.unstable_opts.trust_verify_timeout_ms, 5_000);
    assert_eq!(opts.unstable_opts.trust_verify_function_budget_ms, 120_000);
}

#[test]
fn trust_cg_output_gate_is_a_closed_protocol() {
    for accepted in ["allow-unknown", "strict", "off"] {
        let mut mode = String::new();
        assert!(parse_trust_cg_output_gate(&mut mode, Some(accepted)));
        assert_eq!(mode, accepted);
    }
    for rejected in [None, Some(""), Some("allow_unknown"), Some("STRICT"), Some(" strict ")] {
        let mut mode = "allow-unknown".to_string();
        assert!(!parse_trust_cg_output_gate(&mut mode, rejected));
        assert_eq!(mode, "allow-unknown");
    }
}

#[test]
fn trust_verify_level_rejects_values_outside_the_protocol() {
    for accepted in ["0", "1", "2"] {
        let mut level = usize::MAX;
        assert!(parse_trust_verify_level(&mut level, Some(accepted)));
        assert_eq!(level.to_string(), accepted);
    }

    for rejected in [None, Some(""), Some("-1"), Some("3"), Some("999"), Some("L1")] {
        let mut level = 1;
        assert!(!parse_trust_verify_level(&mut level, rejected));
        assert_eq!(level, 1);
    }
}

#[test]
fn trust_verify_output_rejects_unknown_transport_modes() {
    for accepted in ["human", "json", "both"] {
        let mut output = String::new();
        assert!(parse_trust_verify_output(&mut output, Some(accepted)));
        assert_eq!(output, accepted);
    }

    for rejected in [None, Some(""), Some("JSON"), Some("jsonl"), Some("quiet")] {
        let mut output = "human".to_string();
        assert!(!parse_trust_verify_output(&mut output, rejected));
        assert_eq!(output, "human");
    }
}

#[test]
fn trust_verify_crate_role_is_a_closed_protocol() {
    for accepted in ["unscoped", "primary", "dependency", "build-script"] {
        let mut role = String::new();
        assert!(parse_trust_verify_crate_role(&mut role, Some(accepted)));
        assert_eq!(role, accepted);
    }

    for rejected in [None, Some(""), Some("build_script"), Some("PRIMARY"), Some(" primary ")] {
        let mut role = "unscoped".to_string();
        assert!(!parse_trust_verify_crate_role(&mut role, rejected));
        assert_eq!(role, "unscoped");
    }
}

#[test]
fn trust_nonempty_paths_preserve_nonempty_cli_bytes() {
    for rejected in [None, Some(""), Some("   ")] {
        let mut path = None;
        assert!(!parse_trust_nonempty_path(&mut path, rejected));
        assert_eq!(path, None);
    }

    let mut path = None;
    assert!(parse_trust_nonempty_path(&mut path, Some(" path with spaces ")));
    assert_eq!(path, Some(PathBuf::from(" path with spaces ")));
}

#[test]
fn trust_verify_metadata_strings_are_nonempty_and_trimmed() {
    for parser in [
        parse_trust_verify_package_name as fn(&mut Option<String>, Option<&str>) -> bool,
        parse_trust_verify_profile,
    ] {
        for rejected in [None, Some(""), Some("   ")] {
            let mut value = None;
            assert!(!parser(&mut value, rejected));
            assert_eq!(value, None);
        }

        let mut value = None;
        assert!(parser(&mut value, Some(" proof-value ")));
        assert_eq!(value.as_deref(), Some("proof-value"));
    }
}

#[test]
fn trust_verify_timeout_is_positive() {
    for rejected in [None, Some(""), Some("0"), Some("-1"), Some("abc")] {
        let mut timeout = 500;
        assert!(!parse_trust_verify_timeout_ms(&mut timeout, rejected));
        assert_eq!(timeout, 500);
    }
    for accepted in ["1", "500", "18446744073709551615"] {
        let mut timeout = 500;
        assert!(parse_trust_verify_timeout_ms(&mut timeout, Some(accepted)));
        assert_eq!(timeout.to_string(), accepted);
    }
}

#[test]
fn trust_verify_worker_threads_is_bounded() {
    for accepted in ["0", "1", "256"] {
        let mut workers = usize::MAX;
        assert!(parse_trust_verify_worker_threads(&mut workers, Some(accepted)));
        assert_eq!(workers.to_string(), accepted);
    }
    for rejected in [None, Some(""), Some("-1"), Some("257"), Some("abc")] {
        let mut workers = 1;
        assert!(!parse_trust_verify_worker_threads(&mut workers, rejected));
        assert_eq!(workers, 1);
    }
}

#[test]
fn trust_verify_session_requires_a_nonempty_identity() {
    for rejected in [None, Some(""), Some("   ")] {
        let mut session = None;
        assert!(!parse_trust_verify_session(&mut session, rejected));
        assert_eq!(session, None);
    }

    let mut session = None;
    assert!(parse_trust_verify_session(&mut session, Some(" proof-run-42 ")));
    assert_eq!(session.as_deref(), Some("proof-run-42"));
}

#[test]
fn trust_target_spec_digest_requires_canonical_sha256() {
    let canonical = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let mut digest = None;
    assert!(parse_trust_verify_target_spec_sha256(&mut digest, Some(canonical)));
    assert_eq!(digest.as_deref(), Some(canonical));

    for rejected in [
        None,
        Some(""),
        Some("abc"),
        Some("0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF"),
        Some("g123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"),
        Some(" 0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"),
    ] {
        let mut value = None;
        assert!(!parse_trust_verify_target_spec_sha256(&mut value, rejected));
        assert_eq!(value, None);
    }
}
