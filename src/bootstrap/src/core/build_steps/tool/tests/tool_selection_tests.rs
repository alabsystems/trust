use super::*;

#[test]
fn contributor_profiles_select_every_verification_backend() {
    for profile in ["compiler", "tools"] {
        let tools = default_profile_tools(profile);
        for backend in ["clean", "ty"] {
            assert!(tools.contains(backend), "{profile} profile must include `{backend}`");
        }

        let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
        for bin in [("clean", "clean"), ("ty", "ty")] {
            assert!(bins.contains(&bin), "{profile} profile must restore `{}`", bin.1);
        }
    }
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
fn partial_stage1_source_selection_is_exact_and_never_a_full_sdk() {
    let requested =
        ["compiler/rustc", "library", "src/tools/targo", "src/tools/trustdoc"].map(PathBuf::from);
    assert!(is_partial_stage1_source_build(Kind::Build, 1, 1, false, &requested));
    for path in [
        "compiler",
        "compiler/rustc",
        "library",
        "library/std",
        "src/tools/targo",
        "src/tools/trustdoc",
        "src/librustdoc",
    ] {
        assert!(is_partial_stage1_source_build(Kind::Build, 1, 1, false, &[PathBuf::from(path)]));
    }
    for unknown in [
        "targo-build-tool",
        "trustc",
        "targo-trust",
        "first-party/ay",
        "src/tools/targo/other",
        "src/tools/trustdoc/other",
        "src/librustdoc/other",
        "src/tools/./trustdoc",
        "src/tools/trustdoc/.",
        "src/./librustdoc",
        "src/librustdoc/.",
        "compiler/../compiler/rustc",
        "./compiler/rustc",
    ] {
        let mut mixed = requested.to_vec();
        mixed.push(PathBuf::from(unknown));
        assert!(!is_partial_stage1_source_build(Kind::Build, 1, 1, false, &mixed), "{unknown}");
    }
    assert!(!is_partial_stage1_source_build(Kind::Build, 1, 1, false, &[]));
    assert!(!is_partial_stage1_source_build(Kind::Build, 1, 1, true, &requested));
    for kind in [Kind::Dist, Kind::Install, Kind::Test, Kind::Check, Kind::Clippy, Kind::Doc] {
        assert!(!is_partial_stage1_source_build(kind, 1, 1, false, &requested), "{kind:?}");
    }
    for (compiler_stage, top_stage) in [(0, 1), (1, 2), (2, 2), (2, 1), (3, 3)] {
        assert!(!is_partial_stage1_source_build(
            Kind::Build,
            compiler_stage,
            top_stage,
            false,
            &requested
        ));
    }
}

/// Trust: exercise the actual native bootstrap graph, not just its selection
/// predicate. Compiler requests still build AY through Rustc::run; source Cargo
/// remains distinct from its seed-built engineering prerequisite.
#[test]
fn partial_stage1_source_graph_preserves_requested_tools_and_exact_ay() {
    for rustdoc_path in ["src/tools/trustdoc", "src/librustdoc"] {
        assert_partial_stage1_source_graph(rustdoc_path);
    }
}

// Trust: both paths select the same native Rustdoc step. Exercise its actual
// graph with each spelling rather than duplicating the selector's allowlist.
fn assert_partial_stage1_source_graph(rustdoc_path: &str) {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "build.extended=true"])
        .paths(&["compiler/rustc", "library", "src/tools/targo", rustdoc_path])
        .create_config();
    assert!(
        verifier_backend_source_present(&config.src, AY_SOURCE_MANIFEST),
        "the regression requires the real pinned AY source"
    );
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    builder.execute_cli();
    let producers = builder.step_cache().inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
        (step.tool, step.build_compiler.stage, step.output_compiler.stage)
    });
    assert!(producers.contains(&("ay", 0, 1)), "exact stage1 AY dependency: {producers:?}");
    assert!(producers.contains(&("targo", 0, 0)), "seed-built engineering Cargo: {producers:?}");
    assert!(
        producers.contains(&("targo", 0, 1)),
        "requested source-built SDK Cargo: {producers:?}"
    );
    assert!(
        !producers
            .iter()
            .any(|(tool, _, _)| matches!(*tool, "targo-trust" | "trustd" | "ty" | "clean")),
        "unrequested runtime batteries must not precede a compiler source build: {producers:?}"
    );
    assert!(
        producers.iter().any(|(tool, _, output)| *tool == "rustdoc_tool_binary" && *output == 1),
        "requested paired trustdoc: {producers:?}"
    );
    assert!(builder.step_cache().contains::<compile::Rustc>());
}

#[test]
fn partial_stage1_targo_graph_keeps_real_compiler_dependencies_without_unrequested_tools() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "build.extended=true"])
        .path("src/tools/targo")
        .create_config();
    assert!(verifier_backend_source_present(&config.src, AY_SOURCE_MANIFEST));
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    builder.execute_cli();
    let producers = builder.step_cache().inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
        (step.tool, step.build_compiler.stage, step.output_compiler.stage)
    });
    assert!(producers.contains(&("targo", 0, 0)), "{producers:?}");
    assert!(producers.contains(&("targo", 0, 1)), "{producers:?}");
    // The source-built SDK Cargo needs its stage1 std/compiler graph. Keep
    // that graph (including the compiler's exact AY) rather than treating
    // the engineering seed-built Cargo as the requested SDK artifact.
    assert!(producers.contains(&("ay", 0, 1)), "{producers:?}");
    assert!(builder.step_cache().contains::<compile::Rustc>());
    assert!(
        !producers
            .iter()
            .any(|(tool, _, _)| { matches!(*tool, "targo-trust" | "trustd" | "ty" | "clean") }),
        "unrequested runtime batteries: {producers:?}",
    );
}

#[test]
fn partial_stage1_policy_keeps_full_mixed_and_stage2_battery_graphs() {
    for (stage, paths) in [
        (1, &[][..]),
        (1, &["compiler/rustc", "targo-trust"][..]),
        (2, &["compiler/rustc", "library/std", "src/tools/targo"][..]),
    ] {
        let context = crate::utils::tests::TestCtx::new();
        let config = context
            .config("build")
            .stage(stage)
            .args(&["--set", "build.extended=true"])
            .paths(paths)
            .create_config();
        for manifest in [AY_SOURCE_MANIFEST, TY_SOURCE_MANIFEST, CLEAN_SOURCE_MANIFEST] {
            assert!(verifier_backend_source_present(&config.src, manifest), "{manifest}");
        }
        let build = crate::core::session::Session::new(config);
        let builder = Builder::new(&build);
        builder.execute_cli();
        let producers =
            builder.step_cache().inspect_all_steps_of_type::<ToolBuild, _>(|step, _| step.tool);
        for expected in ["ay", "targo-trust", "trustd", "ty", "clean"] {
            assert!(
                producers.contains(&expected),
                "stage{stage} {paths:?}: missing {expected}: {producers:?}"
            );
        }
    }
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
            bins.contains(&("targo", "targo")),
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
            bins.contains(&("targo", "targo"))
                && bins.contains(&("targo-trust", "targo-trust"))
                && bins.contains(&("trustd", "trustd")),
            "selector `{selector}` must restore the complete verifier frontend"
        );
    }

    // A bare checkout with nothing selected stages no verifier surface.
    let bins = restored_sysroot_bins_for_tool_settings(false, None, false, false);
    assert!(!bins.contains(&("targo", "targo")));
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
            bins.contains(&("targo", "targo")),
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

// Trust: assembly must preserve both names from the same documentation tool.
#[test]
fn documentation_aliases_survive_assembly_for_both_config_spellings() {
    for selected in ["trustdoc", "rustdoc"] {
        let tools = HashSet::from_iter([selected.to_string()]);
        let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
        let documentation: Vec<_> =
            bins.iter().filter(|(source, _)| *source == "rustdoc_tool_binary").copied().collect();
        assert_eq!(
            documentation,
            [("rustdoc_tool_binary", "trustdoc"), ("rustdoc_tool_binary", "rustdoc")],
        );
        let disabled = restored_sysroot_bins_for_tool_settings(false, Some(&tools), false, false);
        assert!(!disabled.iter().any(|(source, _)| *source == "rustdoc_tool_binary"));
    }
    let tools = HashSet::from_iter(["trustfmt".to_string()]);
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    assert!(!bins.iter().any(|(source, _)| *source == "rustdoc_tool_binary"));
}

#[test]
fn restored_sysroot_bins_follow_enabled_tool_surface() {
    let tools = HashSet::from_iter(
        ["targo", "targo-trust", "trustdoc", "tippy", "trustfmt", "trust-analyzer", "trust-miri"]
            .into_iter()
            .map(ToString::to_string),
    );
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    assert!(bins.contains(&("targo", "targo")));
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
    // alias returned by this helper, and only for the `targo` artifact. The
    // `rustc` alias and explicit local documentation bin list are materialized
    // separately. Other retired stock names must stay absent from both the
    // helper and restoration destinations.
    assert_eq!(upstream_compat_bin_for_tool_source("targo"), Some("cargo"));
    for src in [
        "cargo",
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
        "rustfmt",
        "rust-analyzer",
        "miri",
    ];
    let tools = tools_profile_default_tools();
    for (src, dst) in restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false) {
        assert!(!purged.contains(&dst), "restoration emits retired stock name `{dst}`");
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
        // Trust: install.rs's source-component selector; upstream 162423
        // renamed it from `src`, which now selects nothing.
        "rust-src",
        "trust-llvm-tools",
    ] {
        assert!(tools.contains(tool), "tools profile should include `{tool}`");
    }
    assert!(
        !tools.contains("src"),
        "Trust: the obsolete src spelling does not select the source installation component"
    );

    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    for bin in [
        ("targo", "targo"),
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
fn restored_sysroot_bins_skip_disabled_tools() {
    let tools = HashSet::from_iter(["targo".to_string()]);
    let bins = restored_sysroot_bins_for_tool_settings(true, Some(&tools), false, false);
    assert_eq!(
        bins,
        vec![("targo", "targo"), ("targo-trust", "targo-trust"), ("trustd", "trustd")]
    );
    assert!(!restore_rust_analyzer_proc_macro_srv_for_tool_settings(true, Some(&tools)));
}
