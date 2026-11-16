use super::*;

// `test` is redundant here (exec.rs declares this module under cfg(test)) but
// it is the landing gate's evidence that public.rs is test code: the gate reads
// a module's test-only standing from its own declaration, not its parent's.
#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod public;

fn words(values: &[&str]) -> Vec<OsString> {
    values.iter().map(OsString::from).collect()
}

#[test]
fn exact_program_and_every_child_argument_are_retained() {
    let options = parse(&words(&[
        "--kind",
        "measurement",
        "--repo-root",
        "/work",
        "--",
        "/bin/native",
        "--",
        "space value",
        "",
    ]))
    .unwrap();
    assert_eq!(options.kind, Kind::Measurement);
    assert_eq!(options.wait, Duration::ZERO);
    assert_eq!(options.purpose, "native held child");
    assert_eq!(options.root, Some(PathBuf::from("/work")));
    assert_eq!(options.command, words(&["/bin/native", "--", "space value", ""]));
}

#[test]
fn runtime_session_refuses_before_inputs_admission_or_a_child() {
    let error = run(
        &words(&[
            "--runtime-session",
            "--repo-root",
            "/does-not-exist",
            "--",
            "/does-not-exist/bootstrap",
        ]),
        None,
        None,
    )
    .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::Unsupported);
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    assert!(error.to_string().contains("no command started"));
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    assert!(error.to_string().contains("native held command profile is unavailable"));
}

#[test]
fn no_shell_path_lookup_duplicate_or_unbounded_request() {
    for args in [
        words(&["--", "bootstrap"]),
        words(&["--kind", "build", "--kind", "build", "--", "/program"]),
        words(&["--wait", "604801", "--", "/program"]),
        words(&["--kind", "arbitrary", "--", "/program"]),
        words(&["--repo-root", "--", "/program"]),
        words(&["--", ""]),
    ] {
        assert!(parse(&args).is_err(), "{args:?}");
    }
}

#[test]
fn absent_actual_originals_never_start_a_program() {
    assert!(run(&words(&["--", "/not-opened/bootstrap"]), None, None).is_err());
}

#[test]
fn only_exact_fixed_exec_coordinators_are_excluded_from_writer_discovery() {
    let management = super::super::native_management_request;
    assert!(management(
        "targo",
        &words(&[
            "targo",
            "--unverified",
            "resource",
            "repo-lock-exec",
            "--",
            "/native/bootstrap",
            "build"
        ])
    ));
    assert!(management(
        "targo",
        &words(&[
            "targo",
            "--unverified",
            "resource",
            "fixed",
            "--cpus",
            "2",
            "--",
            "repo-lock-exec",
            "--",
            "/native/bootstrap"
        ])
    ));
    for args in [
        words(&[
            "targo",
            "--unverified",
            "resource",
            "fixed",
            "--",
            "check",
            "--",
            "repo-lock-exec",
        ]),
        words(&["targo", "--unverified", "check", "repo-lock-exec"]),
        words(&["targo", "resource", "repo-lock-exec"]),
    ] {
        assert!(!management("targo", &args));
    }
}

#[test]
fn only_exact_native_prune_coordinators_are_management_requests() {
    let management = super::super::native_management_request;
    for name in ["targo", "cargo"] {
        assert!(management(
            name,
            &words(&[name, "--unverified", "resource", "repo-prune", "--dry-run"])
        ));
        assert!(management(
            name,
            &words(&[
                name,
                "--unverified",
                "resource",
                "fixed",
                "--cpus",
                "1",
                "--",
                "repo-prune",
                "--host",
                "aarch64-apple-darwin",
                "--dead-variants",
                "--dry-run"
            ])
        ));
        for args in [
            words(&[name, "--unverified", "resource", "fixed", "--", "check", "--", "repo-prune"]),
            words(&[name, "--unverified", "check", "repo-prune"]),
            words(&[name, "--unverified", "resource", "fixed", "--", "repo-prune-other"]),
            words(&[name, "--unverified", "resource", "fixed", "repo-prune"]),
            words(&[name, "resource", "repo-prune"]),
        ] {
            assert!(!management(name, &args), "{args:?}");
        }
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
#[ignore = "explicit original-image actor; requires an independently selected actual Bootstrap image/hash/expected support"]
fn actual_original_bootstrap_image_support_is_checked_without_executing_it() {
    let path = PathBuf::from(
        std::env::var_os("TRUST_NATIVE_BOOTSTRAP_IMAGE")
            .expect("select an actual original Bootstrap image"),
    );
    let digest = std::env::var("TRUST_NATIVE_BOOTSTRAP_SHA256")
        .expect("select the independent original digest");
    let supported = match std::env::var("TRUST_NATIVE_BOOTSTRAP_SUPPORT").as_deref() {
        Ok("1") => true,
        Ok("0") => false,
        _ => panic!("explicit expected support must be0 or1"),
    };
    let image = HeldSystemCommand::open(&path, input_deadline().unwrap()).unwrap();
    assert_eq!(image.observation().executable.sha256, digest);
    let observed = image.require_bootstrap_fixed_protocol(
        &crate::bootstrap_protocol::BOOTSTRAP_FIXED_PROTOCOL_MARKER,
        input_deadline().unwrap(),
    );
    assert_eq!(observed.is_ok(), supported, "{observed:?}");
    if !supported {
        let refusal = observed.unwrap_err();
        assert_eq!(refusal.kind(), io::ErrorKind::InvalidData);
        assert!(refusal.to_string().contains("does not declare"), "{refusal}");
    }
    println!(
        "actual_original_bootstrap_sha256={digest} supported={supported}; original input/support only, no executable run or runtime/SDK/custody grant"
    );
}
