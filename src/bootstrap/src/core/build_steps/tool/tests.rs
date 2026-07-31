use std::collections::HashSet;
use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};

use super::*;

#[test]
fn ay_bootstrap_uses_the_checked_in_source_closure() {
    // New-spelling manifest -> unsafe-bcp.
    assert_eq!(
        ay_bootstrap_cargo_args_for_manifest("[features]\nunsafe-bcp = []\ncli = []\n"),
        ["--locked", "--no-default-features", "--features", "cli,unsafe-bcp"]
    );
    // Old-spelling manifest (pre-rename pin) -> raw-pointer-bcp.
    assert_eq!(
        ay_bootstrap_cargo_args_for_manifest("[features]\nraw-pointer-bcp = []\ncli = []\n"),
        ["--locked", "--no-default-features", "--features", "cli,raw-pointer-bcp"]
    );
    // Unreadable/ambiguous manifest fails safe to the current spelling.
    assert_eq!(
        ay_bootstrap_cargo_args_for_manifest(""),
        ["--locked", "--no-default-features", "--features", "cli,unsafe-bcp"]
    );
    // Both spellings declared (mid-rename transition) -> the new one wins.
    assert_eq!(
        ay_bootstrap_cargo_args_for_manifest("[features]\nraw-pointer-bcp = []\nunsafe-bcp = []\n"),
        ["--locked", "--no-default-features", "--features", "cli,unsafe-bcp"]
    );
    // A same-named package/dependency key outside `[features]` cannot spoof
    // the selected bootstrap capability.
    assert_eq!(
        ay_bootstrap_cargo_args_for_manifest(
            "unsafe-bcp = \"0.1\"\n[features]\nraw-pointer-bcp = []\ncli = []\n"
        ),
        ["--locked", "--no-default-features", "--features", "cli,raw-pointer-bcp"]
    );
}

#[test]
fn ay_bootstrap_feature_probe_is_rooted_at_the_configured_source_tree() {
    let directory = tempfile::TempDir::new().unwrap();
    let manifest = directory.path().join(AY_SOURCE_MANIFEST);
    fs::create_dir_all(manifest.parent().unwrap()).unwrap();
    fs::write(&manifest, "[features]\nraw-pointer-bcp = []\ncli = []\n").unwrap();

    assert_eq!(
        ay_bootstrap_cargo_args(directory.path()),
        ["--locked", "--no-default-features", "--features", "cli,raw-pointer-bcp"]
    );
}

#[test]
fn locked_cargo_args_prepend_the_closure_gate() {
    assert_eq!(locked_cargo_args(&[]), ["--locked"]);
    assert_eq!(locked_cargo_args(&["--bin", "ty"]), ["--locked", "--bin", "ty"]);
}

#[test]
fn retired_proc_macro_alias_cleanup_is_unconditional_and_idempotent() {
    let directory = tempfile::TempDir::new().unwrap();
    let alias = directory.path().join("rust-analyzer-proc-macro-srv");

    remove_retired_proc_macro_srv_alias(&alias).unwrap();
    fs::write(&alias, b"retired alias").unwrap();
    remove_retired_proc_macro_srv_alias(&alias).unwrap();
    assert!(fs::symlink_metadata(&alias).is_err());
    remove_retired_proc_macro_srv_alias(&alias).unwrap();
}

#[cfg(unix)]
#[test]
fn retired_proc_macro_alias_cleanup_removes_dangling_symlink() {
    use std::os::unix::fs::symlink;

    let directory = tempfile::TempDir::new().unwrap();
    let alias = directory.path().join("rust-analyzer-proc-macro-srv");
    symlink(directory.path().join("missing-target"), &alias).unwrap();
    assert!(!alias.exists(), "fixture must be a dangling symlink");
    assert!(fs::symlink_metadata(&alias).is_ok(), "path entry must exist");

    remove_retired_proc_macro_srv_alias(&alias).unwrap();
    assert!(fs::symlink_metadata(&alias).is_err());
}

#[cfg(unix)]
#[test]
fn cargo_tracks_private_sysroot_search_path_across_invocations() {
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;

    let directory = tempfile::TempDir::new().unwrap();
    let crate_dir = directory.path().join("tracked-private-sysroot");
    fs::create_dir_all(crate_dir.join("src")).unwrap();
    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\n\
         name = \"tracked-private-sysroot\"\n\
         version = \"0.0.0\"\n\
         edition = \"2024\"\n\
         [workspace]\n",
    )
    .unwrap();
    fs::write(crate_dir.join("src/lib.rs"), "pub fn tracked() {}\n").unwrap();

    let wrapper = directory.path().join("record-rustc");
    fs::write(
        &wrapper,
        "#!/bin/sh\n\
         printf '%s\\n' \"$*\" >> \"$TRUST_RUSTC_INVOCATION_LOG\"\n\
         exec \"$@\"\n",
    )
    .unwrap();
    let mut permissions = fs::metadata(&wrapper).unwrap().permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&wrapper, permissions).unwrap();

    let first_search_path = directory.path().join("private-sysroot-generation-one");
    let second_search_path = directory.path().join("private-sysroot-generation-two");
    fs::create_dir_all(&first_search_path).unwrap();
    fs::create_dir_all(&second_search_path).unwrap();
    let target_dir = directory.path().join("target");
    let invocation_log = directory.path().join("rustc-invocations");
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());

    let run = |search_path: &Path| {
        let output = Command::new(&cargo)
            .current_dir(&crate_dir)
            .arg("check")
            .arg("--offline")
            .arg("--quiet")
            .arg("--target-dir")
            .arg(&target_dir)
            .env("RUSTC_WRAPPER", &wrapper)
            .env("TRUST_RUSTC_INVOCATION_LOG", &invocation_log)
            .env("RUSTFLAGS", rustc_private_search_path_flag(search_path))
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .env("CARGO_INCREMENTAL", "0")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "nested cargo check failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    };
    let compiled_library_units = || {
        fs::read_to_string(&invocation_log)
            .unwrap()
            .lines()
            .filter(|line| line.split_whitespace().any(|arg| arg.ends_with("src/lib.rs")))
            .count()
    };

    run(&first_search_path);
    let after_first = compiled_library_units();
    assert!(after_first > 0, "fixture must compile its library once");

    run(&first_search_path);
    assert_eq!(
        compiled_library_units(),
        after_first,
        "an unchanged tracked private-sysroot path should reuse the Cargo unit"
    );

    run(&second_search_path);
    assert!(
        compiled_library_units() > after_first,
        "a changed tracked private-sysroot path must force Cargo to rebuild the unit"
    );
}

#[test]
fn rustdoc_sysroot_aliases_preserve_stage_policy() {
    let bindir = Path::new("sysroot/bin");
    assert_eq!(
        rustdoc_sysroot_bins(bindir, 1, "rustdoc", "trustdoc"),
        (bindir.join("rustdoc"), vec![bindir.join("trustdoc")])
    );
    assert_eq!(
        rustdoc_sysroot_bins(bindir, 2, "rustdoc", "trustdoc"),
        (bindir.join("trustdoc"), Vec::new())
    );
}

fn tools_profile_default_tools() -> HashSet<String> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/defaults/bootstrap.tools.toml");
    let contents = fs::read_to_string(path).unwrap();
    let toml: toml::Value = toml::from_str(&contents).unwrap();

    toml.get("build")
        .and_then(|build| build.get("tools"))
        .and_then(toml::Value::as_array)
        .unwrap()
        .iter()
        .map(|tool| tool.as_str().unwrap().to_string())
        .collect()
}

#[test]
fn only_local_build_assembles_the_complete_user_toolchain() {
    // Stage1 sysroot restoration remains enabled so assembly cannot delete
    // binaries that a previous explicit build produced.
    assert!(should_restore_user_facing_tools(1));
    assert!(!should_restore_user_facing_tools(0));

    // The local build path retains the batteries-on installed surface.
    assert!(should_ensure_default_verifier_tool_bins(Kind::Build, 1));
    assert!(should_assemble_user_facing_tools(Kind::Build, 2));

    // Dist/install/test own explicit component dependency graphs. They must
    // not prebuild every configured tool while assembling a compiler sysroot;
    // that used to build Tippy at stage3 before its requested stage2 dist step.
    for kind in [Kind::Dist, Kind::Install, Kind::Test] {
        assert!(!should_ensure_default_verifier_tool_bins(kind, 1));
        assert!(!should_assemble_user_facing_tools(kind, 2));
    }

    assert!(!should_ensure_default_verifier_tool_bins(Kind::Build, 0));
    assert!(!should_assemble_user_facing_tools(Kind::Build, 1));
}

#[test]
fn tool_aliases_enable_associated_cargo_frontends() {
    // Trust-canonical user aliases. The `tool_name` RHS args remain the
    // upstream cargo source-binary names — that's what bootstrap passes to
    // `cargo --bin` to actually build the binary; only the user-facing
    // tools-settings spelling is rebranded.
    let tools = HashSet::from_iter(
        ["tippy", "trustfmt", "trust-miri"].into_iter().map(ToString::to_string),
    );

    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "clippy-driver",
        true,
    ));
    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "cargo-clippy",
        true,
    ));
    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "rustfmt",
        true,
    ));
    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "cargo-fmt",
        true,
    ));
    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "miri",
        false,
    ));
    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "cargo-miri",
        false,
    ));
}

#[test]
fn tool_aliases_do_not_enable_unrelated_tools() {
    let tools = HashSet::from_iter(["tippy".to_string()]);

    assert!(!extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "cargo-fmt",
        true,
    ));
    assert!(!extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "cargo-miri",
        false,
    ));
    assert!(!extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "rust-analyzer",
        false,
    ));
}

#[test]
fn ay_solver_is_batteries_on_by_default_when_its_source_is_present() {
    let no_tools = HashSet::new();
    // Bare checkout (no in-tree `ay` source) with nothing selected: no verifier
    // tool is scheduled, so no compiler is built solely for it.
    assert!(!default_verifier_tool_bins_enabled(false, None, false));
    assert!(!default_verifier_tool_bins_enabled(true, Some(&no_tools), false));

    // Batteries-on default: whenever the in-tree `ay` source is present, the
    // core solver installs beside `trustc` regardless of `extended`/`tools` —
    // a `trustc` without a sibling `ay` silently degrades every proof-authority
    // obligation to `unknown`, so it is a battery of the compiler, not an
    // optional user tool.
    assert!(default_verifier_tool_bins_enabled(false, None, true));
    assert!(default_verifier_tool_bins_enabled(true, Some(&no_tools), true));

    // Explicit tool selection still enables it even on a bare checkout.
    for selector in ["targo", "targo-trust", "tippy", "ay"] {
        let tools = HashSet::from_iter([selector.to_string()]);
        assert!(
            default_verifier_tool_bins_enabled(true, Some(&tools), false),
            "selector `{selector}` must enable verifier-tool restoration"
        );
    }
}

#[test]
fn l2_backends_are_batteries_whose_only_opt_out_is_the_committed_tool_list() {
    // Unconfigured means batteries-on: the standalone `ty` and `clean` binaries
    // ship, and no ambient process state can take them away.
    assert!(l2_backend_enabled(None, "ty"));
    assert!(l2_backend_enabled(None, "clean"));
    let bins = restored_sysroot_bins_for_tool_settings(false, None, false, true);
    assert!(bins.contains(&("ty", "ty")));
    assert!(bins.contains(&("clean", "clean")));

    // Naming the list is the opt-out, and it is per backend.
    let only_ty = HashSet::from_iter(["ty".to_string()]);
    assert!(l2_backend_enabled(Some(&only_ty), "ty"));
    assert!(!l2_backend_enabled(Some(&only_ty), "clean"));
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&only_ty), false, true);
    assert!(bins.contains(&("ty", "ty")));
    assert!(!bins.contains(&("clean", "clean")));

    // Dropping the trust root's checker survives only as a written decision,
    // and it never drags the solver out with it.
    let no_backends = HashSet::from_iter(["targo-trust".to_string()]);
    assert!(!l2_backend_enabled(Some(&no_backends), "clean"));
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&no_backends), false, true);
    assert!(bins.contains(&("ay", "ay")));
    assert!(!bins.contains(&("ty", "ty")));
    assert!(!bins.contains(&("clean", "clean")));
}

#[test]
fn verifier_frontend_closes_over_solver_batteries_bidirectionally() {
    let no_tools = HashSet::new();

    // Batteries-on means a usable surface, not isolated backend executables:
    // present AY source must also stage the canonical frontend and its daemon.
    for (extended, tools) in [(false, None), (true, Some(&no_tools))] {
        let bins = restored_sysroot_bins_for_tool_settings(extended, tools, false, true);
        assert!(
            bins.contains(&("cargo", "targo")),
            "extended={extended}: solver batteries must pull in Targo"
        );
        assert!(
            bins.contains(&("targo-trust", "targo-trust")),
            "extended={extended}: solver batteries must pull in targo-trust"
        );
        assert!(bins.contains(&("trustd", "trustd")));
        assert!(bins.contains(&("ay", "ay")));
    }

    // Selecting any public verifier/frontend member restores the complete
    // frontend unit. The solver remains guarded by source availability.
    for selector in ["targo", "targo-trust", "ay", "tippy"] {
        let tools = HashSet::from_iter([selector.to_string()]);
        let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
        assert!(
            bins.contains(&("cargo", "targo"))
                && bins.contains(&("targo-trust", "targo-trust"))
                && bins.contains(&("trustd", "trustd")),
            "selector `{selector}` must restore the complete verifier frontend"
        );
    }

    // A bare checkout with nothing selected stages no verifier surface.
    let bins = restored_sysroot_bins_for_tool_settings(false, None, false, false);
    assert!(!bins.contains(&("cargo", "targo")));
    assert!(!bins.contains(&("targo-trust", "targo-trust")));
    assert!(!bins.contains(&("trustd", "trustd")));
    assert!(!bins.contains(&("ay", "ay")));
}

#[test]
fn every_public_tippy_selector_builds_frontend_and_driver() {
    for selector in ["tippy", "targo-tippy", "tippy-driver"] {
        let tools = HashSet::from_iter([selector.to_string()]);
        for source_bin in ["cargo-clippy", "clippy-driver"] {
            assert!(
                extended_rustc_tool_is_default_step_for_tool_settings(
                    true,
                    Some(&tools),
                    false,
                    source_bin,
                    true,
                ),
                "selector `{selector}` should build `{source_bin}`"
            );
        }

        let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
        assert!(
            bins.contains(&("cargo", "targo")),
            "selector `{selector}` must install Tippy's required sibling Targo"
        );
    }
}

#[test]
fn every_public_trustfmt_selector_builds_formatter_and_targo_frontend() {
    for selector in ["trustfmt", "targo-fmt"] {
        let tools = HashSet::from_iter([selector.to_string()]);
        for source_bin in ["rustfmt", "cargo-fmt"] {
            assert!(
                extended_rustc_tool_is_default_step_for_tool_settings(
                    true,
                    Some(&tools),
                    false,
                    source_bin,
                    true,
                ),
                "selector `{selector}` should build `{source_bin}`"
            );
        }

        let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
        assert!(bins.contains(&("rustfmt", "trustfmt")));
        assert!(bins.contains(&("cargo-fmt", "targo-fmt")));
    }
}

#[test]
fn rust_tool_config_names_are_compatibility_selectors() {
    // Trust spellings remain canonical in docs, but source-build config accepts
    // the familiar Rust names as selectors for the same Trust tools.
    let tools = HashSet::from_iter(
        ["clippy", "rustfmt", "miri", "rust-analyzer", "rustdoc"]
            .into_iter()
            .map(ToString::to_string),
    );

    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "cargo-clippy",
        true,
    ));
    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "clippy-driver",
        true,
    ));
    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "rustfmt",
        true,
    ));
    assert!(extended_rustc_tool_is_default_step_for_tool_settings(
        true,
        Some(&tools),
        false,
        "miri",
        false,
    ));
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    assert!(bins.contains(&("rustdoc_tool_binary", "trustdoc")));
    assert!(bins.contains(&("rustfmt", "trustfmt")));
    assert!(bins.contains(&("cargo-fmt", "targo-fmt")));
    assert!(bins.contains(&("cargo-clippy", "tippy")));
    assert!(bins.contains(&("cargo-clippy", "targo-tippy")));
    assert!(bins.contains(&("clippy-driver", "tippy-driver")));
    assert!(bins.contains(&("miri", "trust-miri")));
    assert!(bins.contains(&("cargo-miri", "targo-miri")));
    assert!(restore_rust_analyzer_proc_macro_srv_for_tool_settings(true, Some(&tools)));
}

#[test]
fn restored_sysroot_bins_follow_enabled_tool_surface() {
    let tools = HashSet::from_iter(
        ["targo", "targo-trust", "trustdoc", "tippy", "trustfmt", "trust-analyzer", "trust-miri"]
            .into_iter()
            .map(ToString::to_string),
    );
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    assert!(bins.contains(&("cargo", "targo")));
    assert!(bins.contains(&("targo-trust", "targo-trust")));
    assert!(bins.contains(&("trustd", "trustd")));
    assert!(bins.contains(&("cargo-clippy", "tippy")));
    assert!(bins.contains(&("cargo-clippy", "targo-tippy")));
    assert!(bins.contains(&("clippy-driver", "tippy-driver")));
    assert!(bins.contains(&("rustfmt", "trustfmt")));
    assert!(bins.contains(&("rust-analyzer", "trust-analyzer")));
    assert!(bins.contains(&("cargo-miri", "targo-miri")));
    assert!(bins.contains(&("miri", "trust-miri")));
    assert!(bins.contains(&("rustdoc_tool_binary", "trustdoc")));
    assert!(restore_rust_analyzer_proc_macro_srv_for_tool_settings(true, Some(&tools)));
}

#[test]
fn trustup_is_staged_when_selected_and_only_when_selected() {
    // Trust: `trustup` is the Trust-native replacement for rustup. It must
    // survive a sysroot rewrite like any other user-facing tool, or the binary
    // installed by `ensure_user_facing_tools` is deleted by the next assembly.
    let tools = HashSet::from_iter(["targo".to_string(), "trustup".to_string()]);
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    assert!(bins.contains(&("trustup", "trustup")), "selected `trustup` must be restored");
    assert!(tool_enabled_for_tool_settings(true, Some(&tools), "trustup"));

    // Wiring it in is not adopting it: an unselected `trustup` stages nothing,
    // and no other tool's selection drags it in.
    let without = HashSet::from_iter(["targo".to_string(), "targo-trust".to_string()]);
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&without), false, false);
    assert!(!bins.contains(&("trustup", "trustup")));
    assert!(!tool_enabled_for_tool_settings(true, Some(&without), "trustup"));

    // `trustup` has no upstream spelling, so it can never re-emit a stock name.
    assert_eq!(upstream_compat_bin_for_tool_source("trustup"), None);
}

#[test]
fn upstream_compat_bins_are_cargo_only() {
    // Trust: the sysroot bin ships Trust-branded names ONLY. `cargo` is the sole
    // retained upstream-compat alias (rustup needs a `cargo` entrypoint; `rustc`
    // is materialized on a separate path). No other restored tool may emit a stock
    // secondary name — the invariant the former scripts/purge-stock-names.sh
    // enforced by post-build deletion, now enforced at the source.
    assert_eq!(upstream_compat_bin_for_tool_source("cargo"), Some("cargo"));
    for src in [
        "rustdoc_tool_binary",
        "targo-trust",
        "trustd",
        "cargo-clippy",
        "clippy-driver",
        "cargo-fmt",
        "rustfmt",
        "rust-analyzer",
        "cargo-miri",
        "miri",
        "ay",
        "ty",
        "clean",
    ] {
        assert_eq!(
            upstream_compat_bin_for_tool_source(src),
            None,
            "`{src}` must not emit a stock upstream-compat bin alias",
        );
    }

    // Belt-and-suspenders over the real restored-bins surface: for the default
    // tools profile, no restored bin source may map back to a purged stock name.
    let purged = [
        "cargo-clippy",
        "clippy-driver",
        "cargo-fmt",
        "cargo-miri",
        "cargo-trust",
        "rustdoc",
        "rustfmt",
        "rust-analyzer",
        "miri",
    ];
    let tools = tools_profile_default_tools();
    for (src, _dst) in restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false) {
        if let Some(compat) = upstream_compat_bin_for_tool_source(src) {
            assert!(
                !purged.contains(&compat),
                "restored bin `{src}` re-emits purged stock name `{compat}`",
            );
        }
    }
}

#[test]
fn tools_profile_default_tools_restore_daily_driver_bins() {
    let tools = tools_profile_default_tools();

    for tool in [
        "targo",
        "targo-trust",
        "trustdoc",
        "tippy",
        "trustfmt",
        "trust-analyzer",
        "trust-miri",
        "src",
        "trust-llvm-tools",
    ] {
        assert!(tools.contains(tool), "tools profile should include `{tool}`");
    }

    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    for bin in [
        ("cargo", "targo"),
        ("targo-trust", "targo-trust"),
        ("trustd", "trustd"),
        ("cargo-clippy", "tippy"),
        ("cargo-clippy", "targo-tippy"),
        ("clippy-driver", "tippy-driver"),
        ("rustfmt", "trustfmt"),
        ("rust-analyzer", "trust-analyzer"),
        ("cargo-miri", "targo-miri"),
        ("miri", "trust-miri"),
        ("rustdoc_tool_binary", "trustdoc"),
    ] {
        assert!(bins.contains(&bin), "tools profile should restore `{}`", bin.1);
    }
    assert!(restore_rust_analyzer_proc_macro_srv_for_tool_settings(true, Some(&tools)));
}

#[test]
fn targo_trust_stage2_build_enables_in_process_verifier_features() {
    assert_eq!(
        targo_trust_in_process_features(),
        vec![
            "trust-mc-in-process".to_string(),
            "trust-wp-in-process".to_string(),
            "trust-vc-in-process".to_string(),
            "ay-backend".to_string(),
            // Trust: the proof-carrying-ay promotion lane is LIVE in the shipped
            // verifier (ay UNSAT for LIA/BV-mul/BV-shift → natively kernel-certified
            // → Certified) — without it every ay verdict stays a trusted SmtBacked seam.
            "ay-certify".to_string(),
        ]
    );
    assert_eq!(
        CARGO_TRUST_ALLOW_FEATURES,
        "min_specialization,specialization,try_trait_v2,try_trait_v2_residual"
    );
    assert_eq!(trustd_cargo_args(), ["--locked", "--bin", "trustd"]);
}

#[test]
fn trustd_recipe_inherits_the_trust_runtime_feature_sandbox() {
    let target = TargetSelection::from_user("aarch64-apple-darwin");
    let recipe =
        trustd_tool_build_recipe(Compiler::new(0, target), Compiler::new(1, target), target);

    assert_eq!(recipe.mode, Mode::ToolTarget);
    assert_eq!(recipe.path, "crates/trust-router");
    assert_eq!(recipe.source_type, SourceType::InTree);
    assert_eq!(recipe.cargo_args, ["--locked", "--bin", "trustd"]);
    assert_eq!(recipe.allow_features, CARGO_TRUST_ALLOW_FEATURES);
}

#[test]
fn tippy_test_and_distribution_feature_recipe_tracks_jemalloc() {
    assert_eq!(tippy_driver_features_for_jemalloc(false), Vec::<String>::new());
    assert_eq!(tippy_driver_features_for_jemalloc(true), vec!["jemalloc".to_string()]);
    assert_eq!(CARGO_CLIPPY_CARGO_ARGS, ["--bin", "cargo-clippy"]);
    assert_eq!(CLIPPY_DRIVER_CARGO_ARGS, ["--bin", "clippy-driver"]);
}

#[test]
fn restored_sysroot_bins_skip_disabled_tools() {
    let tools = HashSet::from_iter(["targo".to_string()]);
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    assert_eq!(
        bins,
        vec![("cargo", "targo"), ("targo-trust", "targo-trust"), ("trustd", "trustd")]
    );
    assert!(!restore_rust_analyzer_proc_macro_srv_for_tool_settings(true, Some(&tools)));
}

#[test]
fn tool_build_cache_distinguishes_output_compiler() {
    let target = TargetSelection::from_user("aarch64-apple-darwin");
    let base = ToolBuild {
        build_compiler: Compiler::new(0, target),
        output_compiler: Compiler::new(1, target),
        target,
        tool: "cargo",
        path: "src/tools/targo",
        mode: Mode::ToolTarget,
        source_type: SourceType::Submodule,
        extra_features: Vec::new(),
        allow_features: "",
        cargo_args: Vec::new(),
        artifact_kind: ToolArtifactKind::Binary,
    };
    let other = ToolBuild { output_compiler: Compiler::new(2, target), ..base.clone() };

    assert_ne!(base, other);

    let mut left = DefaultHasher::new();
    base.hash(&mut left);
    let mut right = DefaultHasher::new();
    other.hash(&mut right);
    assert_ne!(left.finish(), right.finish());
}
