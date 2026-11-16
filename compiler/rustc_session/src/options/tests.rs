use std::path::PathBuf;

use super::parse::{
    parse_trust_admission_target, parse_trust_cg_f1_backend, parse_trust_cg_output_gate,
    parse_trust_nonempty_path, parse_trust_platform_budget, parse_trust_platform_properties,
    parse_trust_platform_report, parse_trust_platform_unanalysed, parse_trust_verify_crate_role,
    parse_trust_verify_effort, parse_trust_verify_function_budget_steps, parse_trust_verify_level,
    parse_trust_verify_output, parse_trust_verify_package_name, parse_trust_verify_profile,
    parse_trust_verify_session, parse_trust_verify_target_spec_sha256,
    parse_trust_verify_timeout_ms, parse_trust_verify_worker_threads,
};

#[test]
fn raw_trustc_defaults_match_the_canonical_frontend_policy() {
    let opts = super::Options::default();
    assert_eq!(opts.unstable_opts.trust_verify_level, 2);
    assert_eq!(opts.unstable_opts.trust_verify_timeout_ms, 20_000);
    assert_eq!(opts.unstable_opts.trust_verify_function_budget_ms, 120_000);
    // Mirrors `trust_types::determinism::EffortScale::BUILTIN`.
    assert_eq!(opts.unstable_opts.trust_verify_effort, 384);
}

// Trust: the Option-lane representation is default-on and part of both artifact identities.
#[test]
fn option_flag_lanes_are_default_on_and_tracked_in_both_hashes() {
    let default = super::Options::default();
    assert!(default.unstable_opts.trust_option_flag_lanes);
    let option = super::Z_OPTIONS
        .iter()
        .find(|option| option.name == "trust_option_flag_lanes")
        .expect("the Option-lane selector is registered");
    for (spelling, enabled) in [("on", true), ("off", false)] {
        let mut parsed = default.clone();
        let mut collected = super::CollectedOptions::default();
        assert!((option.setter)(&mut parsed.unstable_opts, &mut collected, Some(spelling), 0,));
        assert_eq!(parsed.unstable_opts.trust_option_flag_lanes, enabled);
        for crate_hash in [false, true] {
            assert_eq!(
                parsed.dep_tracking_hash(crate_hash) == default.dep_tracking_hash(crate_hash),
                enabled,
                "{spelling}: crate_hash={crate_hash}",
            );
        }
    }
    // Numeric spellings of the retired environment control are not boolean options.
    for spelling in ["0", "1", "", "maybe"] {
        let mut parsed = default.clone();
        let mut collected = super::CollectedOptions::default();
        assert!(!(option.setter)(&mut parsed.unstable_opts, &mut collected, Some(spelling), 0,));
        assert!(parsed.unstable_opts.trust_option_flag_lanes);
    }
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

// Trust (step 2 increment 5, sub-step 5.4.2): F1's consumer is a closed domain; a typo never
// silently selects the default `lir` lane.
#[test]
fn trust_cg_f1_backend_is_a_closed_protocol() {
    for accepted in ["lir", "compiler"] {
        let mut backend = String::new();
        assert!(parse_trust_cg_f1_backend(&mut backend, Some(accepted)));
        assert_eq!(backend, accepted);
    }
    for rejected in
        [None, Some(""), Some("LIR"), Some("Compiler"), Some(" compiler"), Some("llvm"), Some("cg")]
    {
        let mut backend = "lir".to_string();
        assert!(!parse_trust_cg_f1_backend(&mut backend, rejected));
        assert_eq!(backend, "lir");
    }
    assert_eq!(super::Options::default().unstable_opts.trust_cg_f1_backend, "lir");
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

/// Trust (determinism plan §3.2a): the effort scale `k` is a count from 1
/// through 100,000 (`EffortScale::CEILING`), and nothing else: not `0`, not a
/// list, not a value past the ceiling.
#[test]
fn trust_verify_effort_is_a_bounded_positive_scale() {
    for rejected in [
        None,
        Some(""),
        Some("0"),
        Some("-1"),
        Some("abc"),
        Some("1,2"),
        Some("100001"),
        Some("18446744073709551615"),
    ] {
        let mut effort = 7;
        assert!(!parse_trust_verify_effort(&mut effort, rejected), "{rejected:?}");
        assert_eq!(effort, 7);
    }
    for accepted in ["1", "64", "100000"] {
        let mut effort = 7;
        assert!(parse_trust_verify_effort(&mut effort, Some(accepted)));
        assert_eq!(effort.to_string(), accepted);
    }
}

/// Trust (determinism plan §3.2, owner direction 2026-09-29): the step budget
/// is the deterministic bound on preprocessing, and no value switches it off —
/// the former `0 = disabled` arm left only the clock.
#[test]
fn trust_verify_function_budget_steps_is_a_positive_count_with_no_off_switch() {
    for rejected in [None, Some(""), Some("0"), Some("-1"), Some("abc")] {
        let mut steps = 7;
        assert!(!parse_trust_verify_function_budget_steps(&mut steps, rejected), "{rejected:?}");
        assert_eq!(steps, 7);
    }
    for accepted in ["1", "64000000", "18446744073709551615"] {
        let mut steps = 7;
        assert!(parse_trust_verify_function_budget_steps(&mut steps, Some(accepted)));
        assert_eq!(steps.to_string(), accepted);
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

#[test]
fn native_admission_target_preserves_exact_unicode_path_and_rejects_duplicates() {
    let path = "/owned/targets/日本語 directory/custom.json";
    let mut target = None;
    assert!(parse_trust_admission_target(&mut target, Some(path)));
    assert_eq!(target.as_deref(), Some(path));
    assert!(!parse_trust_admission_target(&mut target, Some("other")));
    assert_eq!(target.as_deref(), Some(path));
    for rejected in [None, Some("")] {
        assert!(!parse_trust_admission_target(&mut None, rejected));
    }
    assert!(!parse_trust_admission_target(&mut None, Some(&"x".repeat(4097))));
}

// Trust (platform protocols, plan L1a = design PR 8): the five `-Ztrust-platform-*` controls.
// FC-7 is the rule every test below holds: an unknown spelling is a hard error, and so is a
// property this trustc cannot check yet. A refused value never changes the slot.

use crate::config::{
    TrustPlatformProperties, TrustPlatformProperty, TrustPlatformPropertyRefusal,
    TrustPlatformReport, TrustPlatformUnanalysed,
};

fn fd_inherit() -> TrustPlatformProperties {
    [TrustPlatformProperty::FdInherit].into_iter().collect()
}

#[test]
fn trust_platform_defaults_select_no_platform_pass() {
    let opts = super::Options::default();
    let z = &opts.unstable_opts;
    assert!(z.trust_platform_properties.is_empty(), "no property is checked unless asked for");
    assert_eq!(z.trust_platform_unanalysed, TrustPlatformUnanalysed::Warn);
    // Mirrors `trust_platform_derive::DeriveOptions::default().budget`.
    assert_eq!(z.trust_platform_budget, 1_000_000);
    assert_eq!(z.trust_platform_report, TrustPlatformReport::Summary);
    assert_eq!(z.trust_platform_dump_facts, None);
}

#[test]
fn trust_platform_properties_accept_exact_spellings_only() {
    let mut set = TrustPlatformProperties::default();
    assert!(parse_trust_platform_properties(&mut set, Some("fd-inherit")));
    assert_eq!(set, fd_inherit());

    // A duplicate is harmless and kept once.
    let mut set = TrustPlatformProperties::default();
    assert!(parse_trust_platform_properties(&mut set, Some("fd-inherit,fd-inherit")));
    assert_eq!(set, fd_inherit());
    // Repeating the option adds to the set; it can never remove what was asked for.
    assert!(parse_trust_platform_properties(&mut set, Some("fd-inherit")));
    assert_eq!(set.iter().collect::<Vec<_>>(), [TrustPlatformProperty::FdInherit]);

    for rejected in [
        None,
        Some(""),
        Some(","),
        Some("fd-inherit,"),
        Some(",fd-inherit"),
        Some("fd-inherit,,fd-inherit"),
        Some("fd_inherit"),
        Some("FD-INHERIT"),
        Some("Fd-Inherit"),
        Some(" fd-inherit"),
        Some("fd-inherit "),
        Some("fd-inherit, fd-inherit"),
        Some("fdinherit"),
        Some("fd-inherrit"),
        Some("fd-inherit;fd-inherit"),
        Some("all"),
        Some("none"),
        Some("off"),
        Some("on"),
        Some("*"),
    ] {
        for start in [TrustPlatformProperties::default(), fd_inherit()] {
            let mut set = start.clone();
            assert!(!parse_trust_platform_properties(&mut set, rejected), "{rejected:?}");
            assert_eq!(set, start, "a refused value changed the set: {rejected:?}");
        }
    }
}

#[test]
fn trust_platform_properties_refuse_what_this_trustc_cannot_check() {
    for unsupported in TrustPlatformProperty::NOT_SUPPORTED {
        assert_eq!(
            TrustPlatformProperty::from_spelling(unsupported),
            Err(TrustPlatformPropertyRefusal::NotSupported),
        );
        // Never half-applied: the supported property beside it is refused with it, so a
        // policy cannot end up checking less than it says without an error.
        for value in [
            unsupported.to_string(),
            format!("fd-inherit,{unsupported}"),
            format!("{unsupported},fd-inherit"),
        ] {
            let mut set = TrustPlatformProperties::default();
            assert!(!parse_trust_platform_properties(&mut set, Some(&value)), "{value}");
            assert!(set.is_empty(), "{value}");
        }
    }
    assert_eq!(
        TrustPlatformProperty::NOT_SUPPORTED,
        ["lock-release", "fd-identity"],
        "a property leaves this list only in the landing that makes the pass check it (L4c)",
    );
    assert_eq!(
        TrustPlatformProperty::from_spelling("lock_release"),
        Err(TrustPlatformPropertyRefusal::Unknown),
    );
    assert_eq!(
        TrustPlatformProperty::from_spelling("fd-inherit"),
        Ok(TrustPlatformProperty::FdInherit),
    );

    // The parse error's text is the option's description: it must name every property this
    // trustc checks and every one it refuses, and the two lists must not overlap.
    let refusal = super::desc::parse_trust_platform_properties;
    for property in TrustPlatformProperty::ALL {
        assert_eq!(TrustPlatformProperty::from_spelling(property.spelling()), Ok(*property));
        assert!(!TrustPlatformProperty::NOT_SUPPORTED.contains(&property.spelling()));
        assert!(refusal.contains(&format!("`{}`", property.spelling())), "{refusal}");
    }
    for unsupported in TrustPlatformProperty::NOT_SUPPORTED {
        assert!(refusal.contains(&format!("`{unsupported}`")), "{refusal}");
    }
    assert!(refusal.contains("not supported by this trustc"), "{refusal}");
}

#[test]
fn trust_platform_unanalysed_is_warn_or_deny() {
    for (accepted, expected) in
        [("warn", TrustPlatformUnanalysed::Warn), ("deny", TrustPlatformUnanalysed::Deny)]
    {
        let mut mode = if expected.is_deny() {
            TrustPlatformUnanalysed::Warn
        } else {
            TrustPlatformUnanalysed::Deny
        };
        assert!(parse_trust_platform_unanalysed(&mut mode, Some(accepted)));
        assert_eq!(mode, expected);
    }
    // No `allow`: an unanalysed site is always named (FC-1).
    for rejected in [
        None,
        Some(""),
        Some("allow"),
        Some("forbid"),
        Some("error"),
        Some("Deny"),
        Some("DENY"),
        Some("denny"),
        Some(" deny"),
        Some("warn,deny"),
        Some("on"),
        Some("off"),
    ] {
        for start in [TrustPlatformUnanalysed::Warn, TrustPlatformUnanalysed::Deny] {
            let mut mode = start;
            assert!(!parse_trust_platform_unanalysed(&mut mode, rejected), "{rejected:?}");
            assert_eq!(mode, start, "{rejected:?}");
        }
    }
}

#[test]
fn trust_platform_report_is_summary_or_verbose() {
    for (accepted, expected) in
        [("summary", TrustPlatformReport::Summary), ("verbose", TrustPlatformReport::Verbose)]
    {
        let mut report = if expected.is_verbose() {
            TrustPlatformReport::Summary
        } else {
            TrustPlatformReport::Verbose
        };
        assert!(parse_trust_platform_report(&mut report, Some(accepted)));
        assert_eq!(report, expected);
    }
    for rejected in
        [None, Some(""), Some("verbos"), Some("Verbose"), Some("quiet"), Some("none"), Some("json")]
    {
        let mut report = TrustPlatformReport::Verbose;
        assert!(!parse_trust_platform_report(&mut report, rejected), "{rejected:?}");
        assert_eq!(report, TrustPlatformReport::Verbose, "{rejected:?}");
    }
}

#[test]
fn trust_platform_budget_is_a_positive_state_count() {
    for rejected in [
        None,
        Some(""),
        Some("0"),
        Some("-1"),
        Some(" 1"),
        Some("1e6"),
        Some("1_000_000"),
        Some("1.5"),
        Some("18446744073709551616"),
        Some("states"),
    ] {
        let mut budget = 7;
        assert!(!parse_trust_platform_budget(&mut budget, rejected), "{rejected:?}");
        assert_eq!(budget, 7, "{rejected:?}");
    }
    let max = usize::MAX.to_string();
    for accepted in ["1", "1000000", max.as_str()] {
        let mut budget = 7;
        assert!(parse_trust_platform_budget(&mut budget, Some(accepted)));
        assert_eq!(budget.to_string(), accepted);
    }
}

/// The table is what the command line reaches: each `-Ztrust-platform-*` name must route to its
/// own parser and field, and carry its parser's refusal text.
#[test]
fn trust_platform_options_are_wired_through_the_z_table() {
    let option = |name: &str| {
        super::Z_OPTIONS
            .iter()
            .find(|option| option.name == name)
            .unwrap_or_else(|| panic!("`-Z{}` is not in the table", name.replace('_', "-")))
    };
    let mut opts = super::UnstableOptions::default();
    let mut collected = super::CollectedOptions::default();
    for (name, value) in [
        ("trust_platform_properties", "fd-inherit"),
        ("trust_platform_unanalysed", "deny"),
        ("trust_platform_budget", "7"),
        ("trust_platform_report", "verbose"),
        ("trust_platform_dump_facts", "facts.sidecar"),
    ] {
        assert!((option(name).setter)(&mut opts, &mut collected, Some(value), 0), "{name}={value}");
    }
    assert_eq!(opts.trust_platform_properties, fd_inherit());
    assert_eq!(opts.trust_platform_unanalysed, TrustPlatformUnanalysed::Deny);
    assert_eq!(opts.trust_platform_budget, 7);
    assert_eq!(opts.trust_platform_report, TrustPlatformReport::Verbose);
    assert_eq!(opts.trust_platform_dump_facts, Some(PathBuf::from("facts.sidecar")));

    for (name, rejected, refusal) in [
        ("trust_platform_properties", "lock-release", super::desc::parse_trust_platform_properties),
        ("trust_platform_unanalysed", "allow", super::desc::parse_trust_platform_unanalysed),
        ("trust_platform_budget", "0", super::desc::parse_trust_platform_budget),
        ("trust_platform_report", "quiet", super::desc::parse_trust_platform_report),
        ("trust_platform_dump_facts", "", super::desc::parse_trust_nonempty_path),
    ] {
        let mut opts = super::UnstableOptions::default();
        assert!(!(option(name).setter)(&mut opts, &mut collected, Some(rejected), 0), "{name}");
        assert_eq!(option(name).type_desc, refusal, "{name}");
    }
}

/// TRACKED_NO_CRATE_HASH: a platform control adds (from L1d) diagnostics and changes no emitted
/// byte, so changing it must invalidate incremental reuse (a session compiled without the pass
/// cannot be replayed for one with it) and must leave the crate hash, and with it every symbol
/// and every emitted byte, where it was.
#[test]
fn trust_platform_options_invalidate_incremental_reuse_but_not_the_crate_hash() {
    let base = super::Options::default();
    let mutations: [(&str, fn(&mut super::UnstableOptions)); 5] = [
        ("properties", |z| z.trust_platform_properties = fd_inherit()),
        ("unanalysed", |z| z.trust_platform_unanalysed = TrustPlatformUnanalysed::Deny),
        ("budget", |z| z.trust_platform_budget = 1),
        ("report", |z| z.trust_platform_report = TrustPlatformReport::Verbose),
        ("dump_facts", |z| z.trust_platform_dump_facts = Some(PathBuf::from("facts.sidecar"))),
    ];
    for (name, mutate) in mutations {
        let mut changed = base.clone();
        mutate(&mut changed.unstable_opts);
        assert_eq!(
            changed.dep_tracking_hash(true),
            base.dep_tracking_hash(true),
            "-Ztrust-platform-{name} must not move the crate hash",
        );
        assert_ne!(
            changed.dep_tracking_hash(false),
            base.dep_tracking_hash(false),
            "-Ztrust-platform-{name} must invalidate incremental reuse",
        );
    }
}

// Trust (platform protocols, plan L1a; FC-7 and inertness, ADVERSARIAL): attacks on the
// `-Ztrust-platform-*` parsers and their tracking that the tests above do not try.

/// Every spelling of a property name this trustc knows (checked or refused), perturbed the ways a
/// human, an editor or a copy from a rendered document perturbs a word: case, `_` for `-`, a
/// Unicode dash that renders like `-`, an invisible character anywhere in it, whitespace of every
/// kind at either end, a dropped or doubled separator. None may parse as a property, and none of
/// the perturbations of a REFUSED name may be accepted either: a lookalike of `lock-release` must
/// not become a way to ask for it and get nothing.
#[test]
fn trust_platform_property_lookalikes_are_refused() {
    const DASHES: [char; 8] = [
        '\u{2010}', '\u{2011}', '\u{2012}', '\u{2013}', '\u{2014}', '\u{2212}', '\u{fe63}',
        '\u{ff0d}',
    ];
    const INVISIBLE: [char; 5] = ['\u{00ad}', '\u{200b}', '\u{200c}', '\u{200d}', '\u{feff}'];
    const SPACE: [&str; 6] = [" ", "\t", "\n", "\r", "\u{00a0}", "\u{3000}"];

    let known: Vec<&str> = TrustPlatformProperty::ALL
        .iter()
        .map(|property| property.spelling())
        .chain(TrustPlatformProperty::NOT_SUPPORTED.iter().copied())
        .collect();
    let mut tried = 0usize;
    for name in known {
        let mut variants = vec![
            name.to_uppercase(),
            name.replace('-', "_"),
            name.replace('-', ""),
            name.replace('-', "--"),
            name.replace('-', " "),
            name.replace('-', "."),
            {
                let mut chars = name.chars();
                let first = chars.next().unwrap().to_uppercase().collect::<String>();
                first + chars.as_str()
            },
        ];
        for dash in DASHES {
            variants.push(name.replace('-', &dash.to_string()));
        }
        for invisible in INVISIBLE {
            for at in 0..=name.len() {
                variants.push(format!("{}{invisible}{}", &name[..at], &name[at..]));
            }
        }
        for space in SPACE {
            variants.push(format!("{space}{name}"));
            variants.push(format!("{name}{space}"));
        }
        for variant in variants {
            assert_ne!(variant, name);
            assert_eq!(
                TrustPlatformProperty::from_spelling(&variant),
                Err(TrustPlatformPropertyRefusal::Unknown),
                "{variant:?} (a lookalike of `{name}`) must be an unknown spelling",
            );
            for start in [TrustPlatformProperties::default(), fd_inherit()] {
                let mut set = start.clone();
                assert!(!parse_trust_platform_properties(&mut set, Some(&variant)), "{variant:?}");
                assert_eq!(set, start, "a refused lookalike changed the set: {variant:?}");
                // Beside the real spelling it is refused too, and nothing is half-applied.
                let mut set = start.clone();
                let beside = format!("fd-inherit,{variant}");
                assert!(!parse_trust_platform_properties(&mut set, Some(&beside)), "{beside:?}");
                assert_eq!(set, start, "{beside:?}");
            }
            tried += 1;
        }
    }
    assert!(tried > 100, "the generator produced only {tried} variants");
}

/// The tracked hash is a function of the VALUE, never of the spelling: a duplicated property, the
/// option repeated, a budget with a leading zero or a `+`, and every control spelled at its
/// default all hash like the plain value. The opposite would invalidate incremental reuse for
/// nothing; a hash that ignored a real change would be the hole (pinned above and end to end in
/// `tests/run-make/trust-platform-flags-adversarial`).
#[test]
fn trust_platform_value_equal_spellings_track_alike() {
    let parsed = |values: &[(&str, &str)]| {
        let mut opts = super::Options::default();
        for (name, value) in values {
            let option = super::Z_OPTIONS
                .iter()
                .find(|option| option.name == *name)
                .unwrap_or_else(|| panic!("`{name}` is not in the table"));
            let mut collected = super::CollectedOptions::default();
            assert!(
                (option.setter)(&mut opts.unstable_opts, &mut collected, Some(value), 0),
                "{name}={value}",
            );
        }
        opts
    };
    let hash = |opts: &super::Options| opts.dep_tracking_hash(false);

    let default = super::Options::default();
    let explicit_defaults = parsed(&[
        ("trust_platform_unanalysed", "warn"),
        ("trust_platform_budget", "1000000"),
        ("trust_platform_report", "summary"),
    ]);
    assert_eq!(hash(&explicit_defaults), hash(&default), "defaults spelled out");

    let fd = parsed(&[("trust_platform_properties", "fd-inherit")]);
    assert_ne!(hash(&fd), hash(&default));
    for respelled in [
        parsed(&[("trust_platform_properties", "fd-inherit,fd-inherit")]),
        parsed(&[
            ("trust_platform_properties", "fd-inherit"),
            ("trust_platform_properties", "fd-inherit"),
        ]),
        parsed(&[
            ("trust_platform_properties", "fd-inherit"),
            ("trust_platform_budget", "01000000"),
            ("trust_platform_report", "summary"),
        ]),
        parsed(&[
            ("trust_platform_properties", "fd-inherit"),
            ("trust_platform_budget", "+1000000"),
        ]),
    ] {
        assert_eq!(respelled.unstable_opts.trust_platform_properties, fd_inherit());
        assert_eq!(hash(&respelled), hash(&fd), "a value-equal spelling moved the hash");
    }
}

/// The `trust_platform_*` rows of the `-Z` table are exactly the five controls of plan L1a's
/// table. A sixth (say an `allow` switch, or `premises` before plan L3.E gives it a checker)
/// must arrive in the landing that makes the pass honour it, with its own FC-7 tests; it cannot
/// slip in under the prefix and inherit this landing's tests by name.
#[test]
fn trust_platform_z_rows_are_exactly_the_five_controls() {
    let mut rows: Vec<&str> = super::Z_OPTIONS
        .iter()
        .map(|option| option.name)
        .filter(|name| name.starts_with("trust_platform"))
        .collect();
    rows.sort_unstable();
    assert_eq!(
        rows,
        [
            "trust_platform_budget",
            "trust_platform_dump_facts",
            "trust_platform_properties",
            "trust_platform_report",
            "trust_platform_unanalysed",
        ],
    );
}
