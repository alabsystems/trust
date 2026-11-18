use std::collections::HashSet;
use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};

use super::*;

// Trust: two cohesive groups live in child modules under tool/tests/, which keeps
// this file under tidy's length limit: which tools a configuration selects and
// restores (tool_selection_tests), and the native targo, trustup and frontend
// artifact graphs (native_artifact_tests).
mod native_artifact_tests;
// Trust (DC-16a): a stage 2 takes the batteries its change leaves alone from its
// source toolchain.
mod stage2_source_tests;
// Trust: the crate-level features of the first-party crates Targo links, against
// its sandbox (STAGE1-TARGO-AY-FEATURES-1).
mod targo_linked_features;
mod tool_selection_tests;

// Trust: the pairing cycle exists only on the native held-compiler constructor.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod sysroot_construction_tests;

#[cfg(unix)]
#[test]
fn paired_lld_reaches_native_and_rustlib_sdk_paths() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .path("compiler/rustc")
        .with_default_toml_config("profile = 'compiler'\n")
        .create_config();
    assert!(config.lld_enabled, "the compiler SDK must build its paired linker");
    let mut build = crate::core::session::Session::new(config);
    // Only exercise the production filesystem delivery below. Constructing
    // the session as a dry run keeps unrelated build steps out of this test.
    build.config.set_dry_run(crate::core::config::DryRun::Disabled);
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let compiler = Compiler::new(1, target);
    let lld_dir = context.dir().join("lld");
    fs::create_dir_all(lld_dir.join("bin")).unwrap();
    let original = lld_dir.join("bin").join(exe("lld", target));
    let bytes = b"original paired linker image";
    fs::write(&original, bytes).unwrap();
    let wrapper = context.dir().join("lld-wrapper");
    fs::write(&wrapper, b"original linker wrapper").unwrap();
    copy_lld_artifacts(
        &builder,
        BuiltLldWrapper {
            tool: ToolBuildResult {
                tool_path: wrapper,
                build_compiler: Compiler::new(0, target),
                artifacts: vec![],
            },
            lld_dir,
        },
        compiler,
    );
    let copies = [
        builder.sysroot(compiler).join("bin").join(exe("rust-lld", target)),
        builder.sysroot_target_bindir(compiler, target).join(exe("rust-lld", target)),
    ];
    for path in &copies {
        assert_eq!(fs::read(path).unwrap(), bytes);
    }
    #[cfg(target_os = "macos")]
    {
        use std::os::unix::fs::MetadataExt;
        let mut identities = HashSet::new();
        for path in [&original, &copies[0], &copies[1]] {
            let metadata = fs::metadata(path).unwrap();
            assert_eq!(metadata.nlink(), 1, "SDK executable is hard-linked: {}", path.display());
            assert!(identities.insert((metadata.dev(), metadata.ino())));
        }
    }
}

// Trust: preserve the actual snapshot files and reject a conflicting alias.
#[cfg(unix)]
#[test]
fn native_tool_sysroot_alias_keeps_the_snapshot_and_refuses_collisions() {
    let temp = tempfile::TempDir::new_in("/tmp").unwrap();
    let snapshot = temp.path().join("Application Support/seed");
    fs::create_dir_all(snapshot.join("lib")).unwrap();
    fs::write(snapshot.join("lib/identity"), "unchanged seed").unwrap();
    let out = temp.path().join("out");
    let alias = bootstrap_tool_sysroot_alias(&snapshot, &out, false).unwrap().unwrap();
    assert!(!alias.as_os_str().as_encoded_bytes().iter().any(u8::is_ascii_whitespace));
    assert_eq!(alias.canonicalize().unwrap(), snapshot.canonicalize().unwrap());
    assert_eq!(fs::read(alias.join("lib/identity")).unwrap(), b"unchanged seed");
    assert_eq!(bootstrap_tool_sysroot_alias(&snapshot, &out, false).unwrap(), Some(alias.clone()));

    fs::remove_file(&alias).unwrap();
    let other = temp.path().join("other");
    fs::create_dir(&other).unwrap();
    std::os::unix::fs::symlink(&other, &alias).unwrap();
    let error = bootstrap_tool_sysroot_alias(&snapshot, &out, false).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
    assert_eq!(fs::read_link(&alias).unwrap(), other);
    assert_eq!(fs::read(snapshot.join("lib/identity")).unwrap(), b"unchanged seed");
}

#[cfg(unix)]
#[test]
fn native_tool_sysroot_alias_has_no_filesystem_effect_for_dry_runs_or_safe_paths() {
    let temp = tempfile::TempDir::new_in("/tmp").unwrap();
    let out = temp.path().join("absent");
    assert_eq!(bootstrap_tool_sysroot_alias(&temp.path().join("seed"), &out, false).unwrap(), None);
    let snapshot = temp.path().join("Application Support/seed");
    let alias = bootstrap_tool_sysroot_alias(&snapshot, &out, true).unwrap().unwrap();
    assert!(!alias.exists());
    assert!(!out.exists());
    assert!(bootstrap_tool_sysroot_alias(&snapshot, &temp.path().join("bad out"), false).is_err());
    assert!(!temp.path().join("bad out").exists());
    assert!(bootstrap_tool_sysroot_alias(Path::new("relative seed"), &out, false).is_err());
    assert!(!out.exists());
}

// Trust: `x.py -vv` asks the Cargo it drives for the reason each unit rebuilds. The
// in-tree Targo logs them from its `targo-core` library, the pinned stage-0 seal's from its
// `targo` library, and a stock Cargo (which the stage-0 check admits) from `cargo`; a
// filter naming only a retired seal's `targo::core::…` printed none from the first two.
#[test]
fn a_very_verbose_build_asks_each_targo_for_its_fingerprint_reasons() {
    let context = crate::utils::tests::TestCtx::new();
    let mut build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    build.verbosity = 2;
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let cargo = prepare_tool_cargo(
        &builder,
        Compiler::new(0, target),
        Mode::ToolBootstrap,
        target,
        Kind::Build,
        "src/tools/tidy",
        SourceType::InTree,
        &[],
    );
    let mut command = cargo.into_cmd();
    command.mark_as_executed();
    let filter = command
        .get_envs()
        .find_map(|(name, value)| (name == "CARGO_LOG").then_some(value).flatten())
        .map(|value| value.to_string_lossy().into_owned())
        .unwrap_or_default();
    let core = builder.src.join("src/tools/targo/crates/targo-core");
    let manifest = fs::read_to_string(core.join("Cargo.toml")).unwrap();
    assert!(manifest.lines().any(|line| line == "name = \"targo-core\""));
    assert!(core.join("src/compiler/fingerprint/mod.rs").is_file());
    let directives: Vec<&str> = filter.split(',').collect();
    assert_eq!(
        directives,
        [
            "targo_core::compiler::fingerprint=info",
            "targo::compiler::fingerprint=info",
            "cargo::core::compiler::fingerprint=info",
        ]
    );
}

// Trust: exercise the actual targo recipe, whose mode is ToolTarget, rather
// than testing an alias helper that the recipe might never call.
#[cfg(unix)]
#[test]
fn stage0_targo_recipe_passes_the_sysroot_alias_and_keeps_vendoring() {
    for (local_rebuild, mode, needs_alias) in [
        (false, Mode::ToolTarget, true),
        (true, Mode::ToolTarget, false),
        (true, Mode::ToolBootstrap, true),
    ] {
        let context = crate::utils::tests::TestCtx::new();
        let setting =
            if local_rebuild { "build.local-rebuild=true" } else { "build.local-rebuild=false" };
        let mut build = crate::core::session::Session::new(
            context.config("build").stage(1).args(&["--set", setting]).create_config(),
        );
        // Trust: `Session::new` turns a local rebuild on when the stage-0 compiler has
        // the tree's own release, as the pinned seal does; each case names the one it
        // checks (a 1.100 stage 0, which `min_stage0_rustc_version` admits, makes none).
        build.config.local_rebuild = local_rebuild;
        build.initial_sysroot = PathBuf::from("/seed/Application Support/trust");
        let builder = Builder::new(&build);
        let target = builder.config.host_target;
        let recipe =
            targo_tool_build_recipe(Compiler::new(0, target), Compiler::new(1, target), target);
        let cargo = prepare_tool_cargo(
            &builder,
            recipe.build_compiler,
            mode,
            target,
            Kind::Build,
            recipe.path,
            recipe.source_type,
            &recipe.extra_features,
        );
        let alias = bootstrap_tool_sysroot_alias(&build.initial_sysroot, &builder.out, true)
            .unwrap()
            .unwrap();
        let expected_sysroot = if local_rebuild && mode == Mode::ToolTarget {
            builder.sysroot(recipe.build_compiler)
        } else {
            build.initial_sysroot.clone()
        };
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        let flags = command
            .get_envs()
            .filter_map(|(name, value)| {
                matches!(name.to_str(), Some("RUSTFLAGS" | "CARGO_ENCODED_RUSTFLAGS"))
                    .then_some(value)
                    .flatten()
                    .map(|value| value.to_string_lossy().into_owned())
            })
            .collect::<Vec<_>>()
            .join("\x1f");
        assert_eq!(
            flags.contains(alias.to_str().unwrap()),
            needs_alias,
            "wrong sysroot in recipe: {flags}"
        );
        let sysroot = command.get_envs().find_map(|(name, value)| {
            (name == "RUSTC_SYSROOT").then_some(value).flatten().map(PathBuf::from)
        });
        assert_eq!(sysroot, Some(expected_sysroot));
        let args =
            command.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>().join(" ");
        assert!(args.contains("vendored-openssl"), "OpenSSL vendoring removed: {args}");
        assert!(args.contains("vendored-libgit2"), "libgit2 vendoring removed: {args}");
    }
}

// Trust: inspect the real composed commands, rather than merely testing a mode
// predicate. A compiler/private tool retains its sysroot runtime path while a
// standalone trustd recipe has no embedded search path even with rust.rpath=true.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn trustd_uses_system_runtime_defaults_while_private_tools_keep_their_rpath() {
    // Trust: x.py gives this test binary its own compiler-private link flags.
    // Run the command comparison in an isolated child so those inherited flags
    // do not masquerade as flags generated for the standalone daemon. Avoid
    // changing the process environment while other bootstrap tests are running.
    const CHILD: &str = "TRUST_BOOTSTRAP_TEST_TRUSTD_RPATH_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let mut child = std::process::Command::new(std::env::current_exe().unwrap());
        child
            .args([
                "--exact",
                "core::build_steps::tool::tests::trustd_uses_system_runtime_defaults_while_private_tools_keep_their_rpath",
                "--nocapture",
            ])
            .env(CHILD, "1");
        for (name, _) in std::env::vars_os() {
            let name_text = name.to_string_lossy();
            if name_text.starts_with("RUSTFLAGS")
                || name_text == "CARGO_ENCODED_RUSTFLAGS"
                || (name_text.starts_with("CARGO_TARGET_") && name_text.ends_with("_RUSTFLAGS"))
            {
                child.env_remove(name);
            }
        }
        let output = crate::utils::metadata_scheduler::output(&mut child, true, true).unwrap();
        assert!(
            output.status.success(),
            "isolated runtime policy test failed:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        return;
    }
    let context = crate::utils::tests::TestCtx::new();
    // Trust: bootstrap's build state became `Session` in the 1.101 port.
    let build = crate::core::session::Session::new(
        context.config("build").stage(1).args(&["--set", "rust.rpath=true"]).create_config(),
    );
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let recipe =
        trustd_tool_build_recipe(Compiler::new(0, target), Compiler::new(1, target), target);
    // `Rustflags::propagate_rustflag_envs` folds this test process's own
    // RUSTFLAGS (set by `x.py test src/bootstrap` for the ToolBootstrap
    // build of this very test binary, rpath included) into every composed
    // cargo command. The recipe's OWN flags are what this test measures,
    // so subtract the inherited tokens (multiset difference, order kept).
    let inherited: Vec<String> = ["RUSTFLAGS", "RUSTFLAGS_BOOTSTRAP", "RUSTFLAGS_NOT_BOOTSTRAP"]
        .iter()
        .filter_map(|name| std::env::var(name).ok())
        .flat_map(|value| value.split(' ').map(str::to_string).collect::<Vec<_>>())
        .collect();
    let runtime_flags = |mode: Mode| {
        let cargo = prepare_tool_cargo(
            &builder,
            recipe.build_compiler,
            mode,
            target,
            Kind::Build,
            recipe.path,
            // Trust: each composed command owns its non-Copy source kind.
            recipe.source_type.clone(),
            &recipe.extra_features,
        );
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        let mut inherited = inherited.clone();
        command
            .get_envs()
            .filter_map(|(name, value)| {
                matches!(name.to_str(), Some("RUSTFLAGS" | "CARGO_ENCODED_RUSTFLAGS"))
                    .then_some(value)
                    .flatten()
                    .map(|value| value.to_string_lossy().into_owned())
            })
            .collect::<Vec<_>>()
            .join("\x1f")
            .split([' ', '\x1f'])
            .filter(|token| {
                if let Some(pos) = inherited.iter().position(|seen| seen == token) {
                    inherited.swap_remove(pos);
                    false
                } else {
                    true
                }
            })
            .collect::<Vec<_>>()
            .join(" ")
    };
    let standalone = runtime_flags(recipe.mode);
    assert!(
        !standalone.contains("-rpath,"),
        "standalone daemon has embedded loader authority: {standalone}"
    );
    let private = runtime_flags(Mode::ToolRustcPrivate);
    assert!(private.contains("-rpath,"), "rustc-private tool lost its sysroot runtime: {private}");
}

fn owned_cargo_args(args: &[&str]) -> Vec<String> {
    args.iter().map(|arg| (*arg).to_string()).collect()
}

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

// Trust: exercise the composed command's feature sandbox, including the
// unchanged generic baseline. Native Targo links ay-sat through trust-certify
// (STAGE1-TARGO-AY-FEATURES-1), so it carries the solver permission too. Solver
// permissions must survive composition without becoming a blanket
// unstable-feature permission.
#[test]
fn solver_allocation_feature_stays_scoped_to_solver_tools() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let compiler = Compiler::new(0, target);
    let output = Compiler::new(1, target);
    let ay = ay_tool_build_recipe(compiler, output, target, context.dir());
    let native = targo_tool_build_recipe(compiler, output, target);
    let trustd = trustd_tool_build_recipe(compiler, output, target);
    for (
        name,
        path,
        extra,
        has_allocator,
        has_allocator_api,
        has_min_specialization,
        has_specialization,
    ) in [
        ("generic", "src/tools/targo", "", false, false, false, false),
        (native.tool, native.path, native.allow_features, true, false, true, true),
        (ay.tool, ay.path, ay.allow_features, true, true, true, false),
        (trustd.tool, trustd.path, trustd.allow_features, true, false, true, true),
        (
            "ty",
            "first-party/ty/crates/tla-cli",
            VERIFIER_BACKEND_ALLOW_FEATURES,
            true,
            true,
            true,
            true,
        ),
        (
            "clean",
            "first-party/clean/crates/clean",
            VERIFIER_BACKEND_ALLOW_FEATURES,
            true,
            true,
            true,
            true,
        ),
    ] {
        let mut cargo = prepare_tool_cargo(
            &builder,
            compiler,
            Mode::ToolTarget,
            target,
            Kind::Build,
            path,
            SourceType::InTree,
            &[],
        );
        if !extra.is_empty() {
            cargo.allow_features(extra);
        }
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        let features = command
            .get_envs()
            .find(|(key, _)| *key == "RUSTC_ALLOW_FEATURES")
            .and_then(|(_, value)| value)
            .expect("ToolTarget retains an explicit feature sandbox")
            .to_str()
            .unwrap();
        let allowed: HashSet<_> = features.split(',').collect();
        assert_eq!(allowed.contains("allocator_api"), has_allocator_api, "{name}: {features}");
        assert_eq!(allowed.contains("allocator_ext"), has_allocator, "{name}: {features}");
        // Trust: ahash needs only min_specialization in AY; neither its full
        // specialization permission nor its allocator permission may leak.
        assert_eq!(
            allowed.contains("min_specialization"),
            has_min_specialization,
            "{name}: {features}"
        );
        assert_eq!(allowed.contains("specialization"), has_specialization, "{name}: {features}");
        // Trust: only the recipes that link the native controller client
        // (Targo, and the shared frontend/trustd recipe since d1ab34d273:
        // targo-trust enables `trust-resource-controller/client`) inherit
        // authenticated FDs; AY, ty and clean do not.
        assert_eq!(
            allowed.contains("trust_process_inherit_fds"),
            matches!(name, "targo" | "trustd"),
            "{name}: {features}"
        );
        assert!(allowed.contains("binary-dep-depinfo"), "{name}: {features}");
        assert!(!allowed.contains("box_patterns"), "{name}: unrelated feature was admitted");
    }
}

#[test]
fn locked_cargo_args_prepend_the_closure_gate() {
    assert_eq!(locked_cargo_args(&[]), ["--locked"]);
    assert_eq!(locked_cargo_args(&["--bin", "ty"]), ["--locked", "--bin", "ty"]);
}

#[test]
fn tool_cargo_args_compose_global_and_recipe_lock_policies() {
    for global_locked in [false, true] {
        for recipe_copies in [0, 1, 2, 4] {
            let mut recipe = vec!["--bin".to_string(), "trustd".to_string()];
            recipe.extend(std::iter::repeat_n("--locked".to_string(), recipe_copies));
            recipe.extend(["--features".to_string(), "ay-backend".to_string()]);
            let extra = tool_cargo_args(global_locked, recipe);
            let mut complete = Vec::new();
            if global_locked {
                complete.push("--locked".to_string());
            }
            complete.extend(extra);
            assert_eq!(
                complete.iter().filter(|arg| *arg == "--locked").count(),
                usize::from(global_locked || recipe_copies > 0),
                "global_locked={global_locked}, recipe_copies={recipe_copies}"
            );
            assert_eq!(
                complete
                    .iter()
                    .filter(|arg| *arg != "--locked")
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
                ["--bin", "trustd", "--features", "ay-backend"]
            );
        }
    }
}

#[test]
fn tool_cargo_args_normalize_only_exact_options_and_preserve_order() {
    let recipe = [
        "--locked",
        "--config",
        "env.RECIPE = '--locked'",
        "--features=--locked",
        "--locked",
        "--frozen",
        "--offline",
        "--bin",
        "trustd",
        "--locked",
        "--",
        "--locked",
        "--locked",
    ];
    for global_locked in [false, true] {
        let actual = tool_cargo_args(global_locked, owned_cargo_args(&recipe));
        let mut expected = Vec::new();
        if !global_locked {
            expected.push("--locked");
        }
        expected.extend([
            "--config",
            "env.RECIPE = '--locked'",
            "--features=--locked",
            "--frozen",
            "--offline",
            "--bin",
            "trustd",
            "--",
            "--locked",
            "--locked",
        ]);
        assert_eq!(actual, expected);
    }
}

#[test]
fn tool_cargo_args_preserve_hyphen_leading_jobs_values() {
    for jobs_flag in ["--jobs", "-j"] {
        for global_locked in [false, true] {
            for value in ["--locked", "--", "-2"] {
                let recipe = owned_cargo_args(&[jobs_flag, value, "--locked", "--locked"]);
                let mut expected = owned_cargo_args(&[jobs_flag, value]);
                if !global_locked {
                    expected.push("--locked".to_string());
                }
                assert_eq!(tool_cargo_args(global_locked, recipe), expected);
                // A jobs value cannot satisfy a recipe's lock requirement.
                assert_eq!(
                    tool_cargo_args(global_locked, owned_cargo_args(&[jobs_flag, value])),
                    [jobs_flag, value]
                );
            }
        }
    }
}

#[test]
fn tool_cargo_args_preserve_all_locked_tool_recipes() {
    let recipes = [
        locked_cargo_args(&[]), // targo-trust
        ay_bootstrap_cargo_args_for_manifest("[features]\nunsafe-bcp = []\n"),
        locked_cargo_args(&["--bin", "ty"]),
        locked_cargo_args(&["--bin", "clean"]),
        trustd_cargo_args(),
    ];
    for recipe in recipes {
        assert_eq!(tool_cargo_args(false, recipe.clone()), recipe);
        assert_eq!(tool_cargo_args(true, recipe.clone()), recipe[1..]);
    }
}

/// Opt-in process check, not a build: the selected Trust Cargo must reach the
/// missing-manifest diagnostic after parsing each composed command. The raw
/// duplicate command is a negative control. No compiler or dependency resolution
/// is invoked, and a missing explicit executable is an error rather than fallback.
#[test]
#[ignore = "requires TRUST_BOOTSTRAP_TEST_TARGO naming an absolute Trust Targo executable"]
fn tool_cargo_args_actual_trust_parser() {
    use std::process::Command;

    let executable = PathBuf::from(
        env::var_os("TRUST_BOOTSTRAP_TEST_TARGO")
            .expect("set TRUST_BOOTSTRAP_TEST_TARGO explicitly"),
    );
    assert!(executable.is_absolute(), "the selected executable must be absolute");
    let directory = tempfile::TempDir::new().unwrap();
    let missing = directory.path().join("missing/Cargo.toml");
    let run = |args: &[String]| {
        Command::new(&executable)
            .args(["--unverified", "build", "--manifest-path"])
            .arg(&missing)
            .args(args)
            .env("CARGO_HOME", directory.path().join("cargo-home"))
            .current_dir(directory.path())
            .output()
            .expect("run explicitly selected Trust Targo")
    };
    let raw = run(&owned_cargo_args(&["--locked", "--locked"]));
    let raw_stderr = String::from_utf8(raw.stderr).unwrap();
    assert!(!raw.status.success());
    assert!(
        raw_stderr.contains("the argument '--locked' cannot be used multiple times"),
        "{raw_stderr}"
    );
    for global_locked in [false, true] {
        for recipe_copies in [0, 1, 3] {
            let recipe = vec!["--locked".to_string(); recipe_copies];
            let mut args = Vec::new();
            if global_locked {
                args.push("--locked".to_string());
            }
            args.extend(tool_cargo_args(global_locked, recipe));
            let output = run(&args);
            let stderr = String::from_utf8(output.stderr).unwrap();
            eprintln!(
                "global_locked={global_locked} recipe_copies={recipe_copies} args={args:?}: {stderr}"
            );
            assert!(!output.status.success(), "a missing manifest must not build");
            assert!(stderr.contains("manifest path"), "{stderr}");
            assert!(stderr.contains("does not exist"), "{stderr}");
            assert!(!stderr.contains("cannot be used multiple times"), "{stderr}");
        }
    }
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

    let first_search_path = directory.path().join("private-sysroot-generation-one");
    let second_search_path = directory.path().join("private-sysroot-generation-two");
    fs::create_dir_all(&first_search_path).unwrap();
    fs::create_dir_all(&second_search_path).unwrap();
    let target_dir = directory.path().join("target");
    // Trust: a branded Targo needs an explicit lane; x.py may instead supply
    // the seed's Cargo-compatible invocation. Probe the executable we will run.
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "targo".into());
    let explicit_lane =
        Command::new(&cargo).args(["--unverified", "--version"]).output().unwrap().status.success();

    let run = |search_path: &Path| {
        // Trust: keep the fixture unverified under Targo's two-lane policy.
        let mut command = Command::new(&cargo);
        if explicit_lane {
            command.arg("--unverified");
        }
        let output = command
            .current_dir(&crate_dir)
            .arg("check")
            .arg("--offline")
            .arg("--message-format=json")
            .arg("--target-dir")
            .arg(&target_dir)
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
        // Observe real compiler artifacts without installing a compiler wrapper:
        // wrappers can make native output completion unavailable for reuse.
        let artifacts: Vec<serde_json::Value> = String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .filter(|message: &serde_json::Value| {
                message["reason"] == "compiler-artifact"
                    && message["target"]["name"] == "tracked_private_sysroot"
            })
            .collect();
        assert_eq!(artifacts.len(), 1, "fixture must report its actual library artifact");
        artifacts[0]["fresh"].as_bool().expect("artifact reports its freshness")
    };

    assert!(!run(&first_search_path), "fixture must compile its library once");
    assert!(
        run(&first_search_path),
        "an unchanged tracked private-sysroot path should reuse the Cargo unit"
    );
    assert!(
        !run(&second_search_path),
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
        // The stock alias stays: cargo doctests spawn `rustdoc` by name.
        (bindir.join("trustdoc"), vec![bindir.join("rustdoc")])
    );
}

#[test]
fn local_rustdoc_assembly_and_restoration_match_standalone_step() {
    // Trust: a default local stage2 build must have the same documentation
    // entry points as an explicit Rustdoc build, even after sysroot reassembly.
    let bindir = Path::new("sysroot/bin");
    let (primary, aliases) = rustdoc_sysroot_bins(bindir, 2, "rustdoc", "trustdoc");
    let expected: HashSet<_> = std::iter::once(primary).chain(aliases).collect();
    let assembled: HashSet<_> =
        LOCAL_RUSTDOC_BIN_NAMES.iter().map(|name| bindir.join(name)).collect();
    assert_eq!(assembled, expected);

    let canonical = HashSet::from(["trustdoc".to_owned()]);
    let compatible = HashSet::from(["rustdoc".to_owned()]);
    for tools in [None, Some(&canonical), Some(&compatible)] {
        let restored: HashSet<_> =
            restored_sysroot_bins_for_tool_settings(true, tools, false, false)
                .into_iter()
                .filter(|(source, _)| *source == "rustdoc_tool_binary")
                .map(|(_, name)| bindir.join(name))
                .collect();
        assert_eq!(restored, expected);
    }
    assert!(
        restored_sysroot_bins_for_tool_settings(false, Some(&canonical), false, false)
            .iter()
            .all(|(source, _)| *source != "rustdoc_tool_binary")
    );
}

fn default_profile_tools(profile: &str) -> HashSet<String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("defaults")
        .join(format!("bootstrap.{profile}.toml"));
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

fn tools_profile_default_tools() -> HashSet<String> {
    default_profile_tools("tools")
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
        "min_specialization,specialization,try_trait_v2,try_trait_v2_residual,allocator_ext,trust_process_inherit_fds"
    );
    assert_eq!(trustd_cargo_args(), ["--locked", "--bin", "trustd"]);
}

// Trust: the native member client deliberately uses child-only std file
// actions, never a global CLOEXEC change or a pre_exec fallback. Its actual
// Targo and frontend recipe closures must allow precisely that unstable API.
#[test]
fn native_member_clients_keep_child_only_inheritance_feature_scope() {
    let target = TargetSelection::from_user("aarch64-apple-darwin");
    let recipe =
        targo_tool_build_recipe(Compiler::new(0, target), Compiler::new(1, target), target);
    for allowed in [recipe.allow_features, CARGO_TRUST_ALLOW_FEATURES] {
        assert_eq!(
            allowed.split(',').filter(|feature| *feature == "trust_process_inherit_fds").count(),
            1
        );
    }
    for unrelated in [AY_ALLOW_FEATURES, VERIFIER_BACKEND_ALLOW_FEATURES] {
        assert!(
            !unrelated.split(',').any(|feature| feature == "trust_process_inherit_fds"),
            "unrelated solver recipes must keep their existing feature restrictions"
        );
    }
}

#[test]
fn trustd_recipe_inherits_the_trust_runtime_feature_sandbox() {
    let target = TargetSelection::from_user("aarch64-apple-darwin");
    let recipe =
        trustd_tool_build_recipe(Compiler::new(0, target), Compiler::new(1, target), target);

    assert_eq!(recipe.mode, Mode::ToolTarget);
    assert_eq!(recipe.path, "crates/trust-coordinator");
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
fn tool_build_cache_distinguishes_output_compiler() {
    let target = TargetSelection::from_user("aarch64-apple-darwin");
    let base = ToolBuild {
        build_compiler: Compiler::new(0, target),
        output_compiler: Compiler::new(1, target),
        target,
        tool: "targo",
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

// Trust (2026-10-09): a battery built for the stage-N sysroot names THAT sysroot to
// trust-cg-verify's build script, never the build compiler's (stage N-1), whose
// `bin/ay` is the battery the stage N-2 compiler built.
#[test]
fn a_battery_records_the_ay_of_the_sysroot_it_is_installed_in() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(2).create_config());
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let named = |mode: Mode, output_stage: u32| {
        let build_compiler = Compiler::new(output_stage.saturating_sub(1), target);
        let mut cargo = CargoCommand::new(
            &builder,
            build_compiler,
            mode,
            SourceType::InTree,
            target,
            Kind::Build,
        );
        name_tool_ay_record_host_sysroot(
            &builder,
            &mut cargo,
            mode,
            Compiler::new(output_stage, target),
        );
        let mut command = cargo.into_cmd();
        command.mark_as_executed(); // Inspect the command without running Cargo.
        command
            .get_envs()
            .find(|(key, _)| *key == compile::AY_RECORD_HOST_SYSROOT_ENV)
            .and_then(|(_, value)| value)
            .map(PathBuf::from)
    };
    for stage in [1, 2] {
        let installed = builder.out.join(target).join(format!("stage{stage}"));
        assert_eq!(
            named(Mode::ToolTarget, stage),
            Some(installed),
            "a battery for the stage{stage} sysroot must name the stage{stage} sysroot",
        );
    }
    // Nothing is a sysroot's battery at stage 0, and other tool modes never ship
    // beside a sysroot's `ay`.
    assert_eq!(named(Mode::ToolTarget, 0), None);
    assert_eq!(named(Mode::ToolBootstrap, 1), None);
    assert_eq!(named(Mode::ToolStd, 2), None);
}

// Trust (2026-10-14, D7 of the first seed mint): a stage2 sysroot's rustc-private tools have ONE
// producer, whatever the build selects. `ensure_user_facing_tools` built each of them with the
// stage2 compiler, while the standalone tool steps and `x.py dist` built the same tool with stage1
// into another cargo directory. Both installed it at the same `stage2/bin/<name>`, so whichever ran
// last decided its bytes (they differed in the N_OSO paths that name the cargo directory). A
// `build compiler/rustc library/std` and a full `build` left different tools in the sysroot, and
// the dist archives shipped bytes the compiler-only build never held: the mint's double compile
// compared one copy and the seal would have carried the other.
#[test]
fn a_stage2_sysroot_tool_has_one_producer_whatever_the_build_selects() {
    let shipped = [
        "cargo-clippy",
        "cargo-fmt",
        "cargo-miri",
        "clippy-driver",
        "miri",
        "rust-analyzer",
        "rust-analyzer-proc-macro-srv",
        "rustdoc_tool_binary",
        "rustfmt",
    ];
    for paths in [&["compiler/rustc", "library/std"][..], &[][..]] {
        let config = crate::utils::tests::TestCtx::new()
            .config("build")
            .stage(2)
            .args(&["--set", "build.extended=true"])
            .paths(paths)
            .create_config();
        let build = crate::core::session::Session::new(config);
        let builder = Builder::new(&build);
        builder.execute_cli();
        let producers: Vec<(&str, u32)> = builder
            .step_cache()
            .inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
                (step.mode == Mode::ToolRustcPrivate && step.output_compiler.stage == 2)
                    .then_some((step.tool, step.build_compiler.stage))
            })
            .into_iter()
            .flatten()
            .collect();
        let tools: Vec<&str> = producers.iter().map(|(tool, _)| *tool).collect();
        assert_eq!(
            tools, shipped,
            "`build {paths:?}`: every rustc-private tool of the stage2 sysroot is built exactly \
             once: {producers:?}"
        );
        assert!(
            producers.iter().all(|(_, build_stage)| *build_stage == 1),
            "`build {paths:?}`: the stage2 sysroot's tools are the ones dist ships, built by \
             stage1: {producers:?}"
        );
    }
}

/// Trust: a built tool is installed under its target's triple, where the seed
/// mint (`find_build_manifest_tool`) and recreate_bootstrap read it, and two
/// targets' builds of one tool never share a file. The 1.101 port dropped the
/// level, and the cut's mint found no build-manifest.
#[test]
fn a_built_tool_is_installed_under_its_target_triple() {
    use crate::core::session::tools_bin_dir;
    let host = TargetSelection::from_user("aarch64-apple-darwin");
    let wasm = TargetSelection::from_user("wasm32-unknown-unknown");
    let out = Path::new("/build");
    let compiler = Compiler::new(2, host);
    assert_eq!(
        tools_bin_dir(out, compiler, host),
        Path::new("/build/aarch64-apple-darwin/stage3-tools-bin/aarch64-apple-darwin")
    );
    assert_ne!(tools_bin_dir(out, compiler, host), tools_bin_dir(out, compiler, wasm));
}

// Trust: inspect actual prepared commands; only independent ToolTarget recipes
// receive their component label. Private and mixed tool graphs retain the global one.
#[test]
fn independent_component_remap_is_applied_only_to_its_prepared_tool_command() {
    use crate::utils::channel::{GitInfo, Info};
    use crate::utils::trust_source_identity::{IndependentToolComponent, Naming, component_remap};
    crate::utils::tests::git::git_test(|ctx| {
        let recipes = [
            (IndependentToolComponent::Ay, "first-party/ay/crates/ay"),
            (IndependentToolComponent::Ty, "first-party/ty/crates/tla-cli"),
            (IndependentToolComponent::Clean, "first-party/clean/crates/clean"),
        ];
        ctx.write(
            ".gitmodules",
            &recipes
                .iter()
                .map(|(c, _)| {
                    format!(
                        "[submodule \"{}\"]\npath = {}\nurl = ./{}\n",
                        c.root(),
                        c.root(),
                        c.namespace()
                    )
                })
                .collect::<String>(),
        );
        ctx.write("parent", "parent");
        ctx.commit();
        for (component, recipe) in recipes {
            let root = component.root();
            fs::create_dir_all(ctx.get_path().join(root)).unwrap();
            for args in [
                vec!["-C", root, "init"],
                vec!["-C", root, "config", "user.name", "Tester"],
                vec!["-C", root, "config", "user.email", "tester@example.invalid"],
            ] {
                ctx.run_git(&args);
            }
            ctx.write(&format!("{recipe}/src/lib.rs"), "pub fn solve() {}");
            ctx.run_git(&["-C", root, "add", "."]);
            ctx.run_git(&["-C", root, "commit", "-m", "component"]);
        }
        let context = crate::utils::tests::TestCtx::new();
        let mut build =
            crate::core::session::Session::new(context.config("build").stage(1).create_config());
        build.config.src = ctx.get_path().to_owned();
        build.config.rust_remap_debuginfo = true;
        build.config.omit_git_hash = false;
        let global = "0123456789abcdef0123456789abcdef01234567";
        let version = GitInfo::Present(Some(Info {
            sha: global.to_owned(),
            short_sha: global[..9].to_owned(),
            commit_date: "2026-11-03".to_owned(),
        }));
        assert!(build.name_for_test(Naming { version, remap: Some(global.to_owned()) }));
        let builder = Builder::new(&build);
        let target = builder.host_target;
        for (component, recipe) in recipes {
            let root = ctx.get_path().join(component.root());
            let own = GitInfo::new(false, &root, build.config.exec_ctx());
            let component_label =
                component_remap(build.config.exec_ctx(), &root, &own, component).unwrap().unwrap();
            for (mode, path, expected) in [
                (Mode::ToolTarget, recipe, component_label.as_str()),
                (
                    Mode::ToolTarget,
                    "targo-trust",
                    "/rustc/0123456789abcdef0123456789abcdef01234567",
                ),
                (Mode::ToolRustcPrivate, recipe, "/rustc/0123456789abcdef0123456789abcdef01234567"),
            ] {
                let cargo = prepare_tool_cargo_with_input(
                    &builder,
                    Compiler::new(0, target),
                    mode,
                    target,
                    Kind::Build,
                    path,
                    SourceType::InTree,
                    &[],
                    CargoInput::Seed,
                );
                let mut command = cargo.into_cmd();
                command.mark_as_executed();
                let remap = command
                    .get_envs()
                    .find(|(key, _)| *key == OsStr::new("__CARGO_RUSTC_BOOTSTRAP_WS_REMAP"))
                    .and_then(|(_, value)| value)
                    .unwrap();
                assert_eq!(remap, OsStr::new(expected), "{mode:?} {path}");
                if mode == Mode::ToolTarget && path == recipe {
                    let hash = command
                        .get_envs()
                        .find(|(key, _)| *key == OsStr::new("CFG_COMMIT_HASH"))
                        .and_then(|(_, value)| value)
                        .unwrap();
                    assert_eq!(hash, OsStr::new(own.sha().unwrap()));
                }
            }
        }
    });
}

// Trust: the backend manifests in this fixture exist independently of whether
// the developer materialized the three sibling sources. All other source reads
// still use this checkout; no compiler or tool command is executed by the graph.
#[cfg(unix)]
fn intermediate_tool_source_fixture(
    context: &crate::utils::tests::TestCtx,
    build: &mut crate::core::session::Session,
) {
    let source = context.dir().join("source");
    fs::create_dir(&source).unwrap();
    for entry in fs::read_dir(&build.config.src).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() != "first-party" && entry.file_name() != ".git" {
            std::os::unix::fs::symlink(entry.path(), source.join(entry.file_name())).unwrap();
        }
    }
    for manifest in [AY_SOURCE_MANIFEST, TY_SOURCE_MANIFEST, CLEAN_SOURCE_MANIFEST] {
        let manifest = source.join(manifest);
        fs::create_dir_all(manifest.parent().unwrap()).unwrap();
        fs::write(manifest, "[features]\ncli = []\nunsafe-bcp = []\n").unwrap();
    }
    build.config.src = source;
    // Trust: TestCtx injects external tools for identity probes. Session has
    // already bound them; model the ordinary source-built scheduling config.
    build.config.external_rustc = None;
    build.config.external_cargo = None;
    build.config.external_rustdoc = None;
    // Trust: and a stage 0 of an older release (`min_stage0_rustc_version` admits one),
    // not the local rebuild `Session::new` turns on when the stage-0 compiler has the
    // tree's own release, as the pinned seal does: then nothing is deferred, which
    // `intermediate_tool_deferral_policy_is_fail_closed` checks.
    build.config.local_rebuild = false;
}

#[cfg(unix)]
fn intermediate_tool_graph_isolated(name: &str) -> bool {
    // x.py's test runner inherits injected rpath flags. Remove that unrelated
    // test harness posture only in a child; never mutate the shared test env.
    const ISOLATED: &str = "BOOTSTRAP_INTERMEDIATE_TOOL_GRAPH_ISOLATED";
    if env::var_os(ISOLATED).is_none() {
        let mut child = std::process::Command::new(env::current_exe().unwrap());
        child.args(["--exact", name, "--nocapture"]).env(ISOLATED, "1");
        for (key, value) in env::vars_os() {
            if intermediate_tool_ambient_override(&key, &value) {
                child.env_remove(key);
            }
        }
        // Trust: the existing announced native policy of the x.py driver.
        child.env("RUSTFLAGS_BOOTSTRAP", "-Ztrust-verify=off");
        // Trust: and a Cargo home with no configuration, which the policy requires; the
        // runner's own (`$HOME/.cargo/config.toml` on a developer machine) refuses it.
        let home = env::temp_dir().join(format!("bootstrap-tool-graph-{}", std::process::id()));
        child.env("CARGO_HOME", home.join("cargo-home"));
        let output = crate::utils::metadata_scheduler::output(&mut child, true, true).unwrap();
        print!("{}", String::from_utf8_lossy(&output.stdout));
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        return true;
    }
    false
}

#[cfg(unix)]
#[test]
fn intermediate_stage1_defers_only_eager_tools_and_keeps_final_generation() {
    if intermediate_tool_graph_isolated(
        "core::build_steps::tool::tests::intermediate_stage1_defers_only_eager_tools_and_keeps_final_generation",
    ) {
        return;
    }
    assert_intermediate_stage1_tool_graph(false, false);
}

#[cfg(unix)]
#[test]
fn intermediate_apple_cross_std_keeps_ay_first_and_all_final_tools() {
    if intermediate_tool_graph_isolated(
        "core::build_steps::tool::tests::intermediate_apple_cross_std_keeps_ay_first_and_all_final_tools",
    ) {
        return;
    }
    assert_intermediate_stage1_tool_graph(true, false);
}

#[cfg(unix)]
#[test]
fn intermediate_same_line_compiler_artifacts_precede_native_clis() {
    if intermediate_tool_graph_isolated(
        "core::build_steps::tool::tests::intermediate_same_line_compiler_artifacts_precede_native_clis",
    ) {
        return;
    }
    assert_intermediate_stage1_tool_graph(false, true);
}

#[cfg(unix)]
#[test]
fn intermediate_same_line_cross_std_retains_both_complete_sdks() {
    if intermediate_tool_graph_isolated(
        "core::build_steps::tool::tests::intermediate_same_line_cross_std_retains_both_complete_sdks",
    ) {
        return;
    }
    assert_intermediate_stage1_tool_graph(true, true);
}

#[cfg(unix)]
fn assert_intermediate_stage1_tool_graph(apple_cross_std: bool, same_line: bool) {
    let context = crate::utils::tests::TestCtx::new();
    let mut build = crate::core::session::Session::new(
        context
            .config("build")
            .stage(2)
            .args(&["--set", "build.extended=true", "--set", "rust.trust-source-identity=false"])
            .paths(&["compiler/rustc", "library/std"])
            .create_config(),
    );
    let source_derived_local_rebuild = build.config.local_rebuild;
    if same_line && !source_derived_local_rebuild {
        println!(
            "same-line source/seed graph requires a compiler on the source Rust protocol line"
        );
        return;
    }
    intermediate_tool_source_fixture(&context, &mut build);
    build.config.local_rebuild = same_line && source_derived_local_rebuild;
    if apple_cross_std {
        let native = build.config.host_target;
        let cross = match &*native.triple {
            "aarch64-apple-darwin" => "x86_64-apple-darwin",
            "x86_64-apple-darwin" => "aarch64-apple-darwin",
            _ => return, // The actual native-host graph is exercised on Apple hosts.
        };
        build.config.targets.push(TargetSelection::from_user(cross));
    }
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let verifier_tools = |stage| {
        builder
            .step_cache()
            .inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
                (step.output_compiler.stage == stage
                    && ["ay", "targo", "targo-trust", "trustd", "ty", "clean"].contains(&step.tool))
                .then_some((step.tool, step.build_compiler.stage))
            })
            .into_iter()
            .flatten()
            .collect::<Vec<_>>()
    };

    // The first sysroot creation is before Rustc::run constructs compiler
    // Cargo. AY must already have a producer at precisely this boundary.
    let stage1 = Compiler::new(1, target);
    builder.sysroot(stage1);
    assert_eq!(verifier_tools(1), [("ay", 0)]);
    if same_line {
        // The actual same-line path may build cross-std with stage0. It must
        // retain its ordinary Std recipe without pulling native verifier CLIs.
        for cross in builder.config.targets.iter().filter(|cross| **cross != target) {
            builder.std(Compiler::new(0, target), *cross);
        }
        let seed = Compiler::new(0, target);
        builder.ensure(compile::Rustc::new(seed, target));
        let mut cargo = builder::Cargo::new(
            &builder,
            seed,
            Mode::Rustc,
            SourceType::InTree,
            target,
            Kind::Build,
        );
        compile::rustc_cargo(&builder, &mut cargo, target, &seed, &[]);
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        let named = command
            .get_envs()
            .find(|(key, _)| *key == compile::AY_RECORD_HOST_SYSROOT_ENV)
            .and_then(|(_, value)| value)
            .map(PathBuf::from);
        assert_eq!(named, Some(compile::local_sysroot_dir(&builder, stage1)));
        for (key, expected) in [("RUSTC_STAGE", "1"), ("TRUST_BOOTSTRAP_SHIM_NO_VERIFY", "1")] {
            assert_eq!(
                command.get_envs().find(|(name, _)| *name == key).and_then(|(_, value)| value),
                Some(OsStr::new(expected))
            );
        }
        assert_eq!(verifier_tools(1), [("ay", 0)]);
        assert_eq!(
            builder.step_cache().inspect_all_steps_of_type::<compile::Rustc, _>(|_, _| ()).len(),
            1
        );
    }
    builder.compiler(1, target);
    let complete_stage1 = if same_line {
        vec![("ay", 0), ("clean", 0), ("targo", 0), ("targo-trust", 0), ("trustd", 0), ("ty", 0)]
    } else {
        vec![("ay", 0)]
    };
    if same_line {
        // Assembly reused the same completed compiler artifact Step.
        assert_eq!(
            builder.step_cache().inspect_all_steps_of_type::<compile::Rustc, _>(|_, _| ()).len(),
            1
        );
    }
    if apple_cross_std {
        for cross in builder.config.targets.iter().filter(|cross| **cross != target) {
            builder.std(stage1, *cross);
        }
    }
    // Post-assembly restoration must not move the same five builds later.
    assert_eq!(verifier_tools(1), complete_stage1);
    builder.compiler(2, target);
    assert_eq!(verifier_tools(1), complete_stage1);
    assert_eq!(
        verifier_tools(2),
        [("ay", 1), ("clean", 1), ("targo", 1), ("targo-trust", 1), ("trustd", 1), ("ty", 1)]
    );

    // Inspect actual graph recipes and the commands they compose. Their
    // features/locks, generation and output sysroot are unchanged.
    let recipes = std::cell::RefCell::new(Vec::new());
    builder.step_cache().inspect_all_steps_of_type::<ToolBuild, _>(|recipe, _| {
        if (recipe.output_compiler.stage == 2 || (same_line && recipe.output_compiler.stage == 1))
            && ["ay", "targo", "targo-trust", "trustd", "ty", "clean"].contains(&recipe.tool)
        {
            recipes.borrow_mut().push(recipe.clone());
        }
    });
    // Drop the cache's immutable borrow before command construction consults
    // its dependencies, even when they are already cached.
    for recipe in recipes.into_inner() {
        assert_eq!(recipe.mode, Mode::ToolTarget);
        assert_eq!(recipe.artifact_kind, ToolArtifactKind::Binary);
        assert_eq!(recipe.build_compiler, Compiler::new(recipe.output_compiler.stage - 1, target));
        let (args, features) = match recipe.tool {
            "ay" => {
                (vec!["--locked", "--no-default-features", "--features", "cli,unsafe-bcp"], vec![])
            }
            "targo" => (vec![], vec![]),
            "targo-trust" => (
                vec!["--locked"],
                vec![
                    "trust-mc-in-process",
                    "trust-wp-in-process",
                    "trust-vc-in-process",
                    "ay-backend",
                    "ay-certify",
                ],
            ),
            "trustd" => (vec!["--locked", "--bin", "trustd"], vec![]),
            "ty" => (vec!["--locked", "--bin", "ty"], vec![]),
            "clean" => (vec!["--locked", "--bin", "clean"], vec!["carcara-verify"]),
            _ => unreachable!(),
        };
        assert_eq!(recipe.cargo_args, args);
        assert_eq!(recipe.extra_features, features);
        assert_eq!(
            recipe.allow_features,
            match recipe.tool {
                // Trust: 17ce2ab3e5 lets AY's ahash build script request
                // min_specialization (AY_ALLOW_FEATURES).
                "ay" => "min_specialization,allocator_api,allocator_ext",
                // The native job service and verifier tools use the same
                // proof runtime and child-only descriptor inheritance.
                "targo" | "targo-trust" | "trustd" =>
                    "min_specialization,specialization,try_trait_v2,try_trait_v2_residual,allocator_ext,trust_process_inherit_fds",
                "ty" | "clean" => "min_specialization,specialization,allocator_api,allocator_ext",
                _ => unreachable!(),
            }
        );
        let mut cargo = prepare_tool_cargo(
            &builder,
            recipe.build_compiler,
            recipe.mode,
            target,
            Kind::Build,
            recipe.path,
            recipe.source_type.clone(),
            &recipe.extra_features,
        );
        if !recipe.allow_features.is_empty() {
            cargo.allow_features(recipe.allow_features);
        }
        cargo.args(tool_cargo_args(builder.config.locked_deps, recipe.cargo_args.clone()));
        name_tool_ay_record_host_sysroot(&builder, &mut cargo, recipe.mode, recipe.output_compiler);
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        let named = command
            .get_envs()
            .find(|(key, _)| *key == compile::AY_RECORD_HOST_SYSROOT_ENV)
            .and_then(|(_, value)| value)
            .map(PathBuf::from);
        assert_eq!(named, Some(compile::local_sysroot_dir(&builder, recipe.output_compiler)));
        let arguments: Vec<_> =
            command.get_args().map(|arg| arg.to_string_lossy().into_owned()).collect();
        assert!(arguments.windows(2).any(|pair| {
            pair[0] == "--manifest-path"
                && pair[1] == builder.src.join(recipe.path).join("Cargo.toml").to_string_lossy()
        }));
        assert_eq!(
            arguments.iter().filter(|arg| *arg == "--locked").count(),
            usize::from(recipe.tool != "targo")
        );
    }
}

// Trust: policy and filesystem controls include postures that must keep the
// original graph, rather than treating an unknown backend as native LLVM.
#[test]
fn intermediate_tool_deferral_policy_is_fail_closed() {
    assert_intermediate_tool_scheduling_policy();
}

// Trust: all generations postpone final frontends until compiler assembly;
// only the retained older-line skip policy still needs conditional admission.
fn assert_intermediate_tool_scheduling_policy() {
    use crate::core::backend::CodegenBackendKind;
    let context = crate::utils::tests::TestCtx::new();
    let mut build =
        crate::core::session::Session::new(context.config("build").stage(2).create_config());
    build.config.external_rustc = None;
    build.config.external_cargo = None;
    build.config.external_rustdoc = None;
    // Trust: the policy reads every Cargo configuration above the source tree. Model a
    // tree in the temporary directory whose only one is the tracked `.cargo/config.toml`,
    // so a `$HOME/.cargo/config.toml` above the checkout does not decide the test. One
    // above the temporary directory itself would refuse deferral, as it should, so the
    // test names it rather than failing on the first `ordinary` assertion.
    let source = context.dir().join("source");
    let above = source.ancestors().skip(1).find_map(|parent| {
        ["config", "config.toml"]
            .iter()
            .map(|name| parent.join(".cargo").join(name))
            .find(|path| fs::symlink_metadata(path).is_ok())
    });
    assert!(
        above.is_none(),
        "this test needs a temporary directory with no Cargo configuration above it; \
         {} is one (set TMPDIR elsewhere)",
        above.unwrap_or_default().display()
    );
    fs::create_dir_all(source.join(".cargo")).unwrap();
    fs::write(
        source.join(".cargo/config.toml"),
        include_str!("../../../../../../.cargo/config.toml"),
    )
    .unwrap();
    build.config.src = source;
    build.config.local_rebuild = false;
    let native = helpers::get_host_target();
    let ambient = vec![
        (OsString::from("CARGO_HOME"), context.dir().join("cargo-home").into_os_string()),
        (OsString::from("RUSTFLAGS_BOOTSTRAP"), OsString::from("-Ztrust-verify=off")),
    ];
    let eligible = |build: &crate::core::session::Session,
                    kind,
                    top,
                    stage,
                    host,
                    paths: &[&str],
                    ambient: Vec<(OsString, OsString)>| {
        let mut builder = Builder::new(build);
        builder.kind = kind;
        builder.top_stage = top;
        builder.paths = paths.iter().map(PathBuf::from).collect();
        should_defer_intermediate_verifier_tool_bins(&builder, Compiler::new(stage, host), ambient)
    };
    let ordinary = |build: &crate::core::session::Session, ambient| {
        eligible(build, Kind::Build, 2, 1, native, &[], ambient)
    };
    assert!(ordinary(&build, ambient.clone()));
    assert!(eligible(
        &build,
        Kind::Build,
        2,
        1,
        native,
        &["compiler/rustc", "library/std"],
        ambient.clone()
    ));
    for kind in [Kind::Test, Kind::Check, Kind::Dist, Kind::Install, Kind::Doc] {
        assert!(!eligible(&build, kind, 2, 1, native, &[], ambient.clone()));
    }
    for (top, stage) in [(1, 1), (2, 0), (2, 2), (3, 1), (3, 2)] {
        assert!(!eligible(&build, Kind::Build, top, stage, native, &[], ambient.clone()));
    }
    for paths in [vec!["targo-trust"], vec!["src/tools/targo"], vec!["compiler"], vec!["unknown"]] {
        assert!(!eligible(&build, Kind::Build, 2, 1, native, &paths, ambient.clone()));
    }
    let foreign = TargetSelection::from_user("i686-unknown-haiku");
    assert!(!eligible(&build, Kind::Build, 2, 1, foreign, &[], ambient.clone()));
    build.config.hosts.push(foreign);
    assert!(!ordinary(&build, ambient.clone()));
    build.config.hosts = vec![native];
    build.config.targets.push(foreign);
    assert!(!ordinary(&build, ambient.clone()));
    build.config.targets = vec![native];
    if let Some(cross) = match &*native.triple {
        "aarch64-apple-darwin" => Some("x86_64-apple-darwin"),
        "x86_64-apple-darwin" => Some("aarch64-apple-darwin"),
        _ => None,
    } {
        let cross = TargetSelection::from_user(cross);
        build.config.targets.push(cross);
        assert!(ordinary(&build, ambient.clone()));
        build.config.targets.reverse();
        assert!(ordinary(&build, ambient.clone()));
        assert!(!eligible(&build, Kind::Build, 2, 2, native, &[], ambient.clone()));
        assert!(!eligible(&build, Kind::Build, 2, 1, cross, &[], ambient.clone()));
        for key in ["TRUST_BOOTSTRAP_VERIFY_LIBRARY", "RUSTFLAGS_NOT_BOOTSTRAP"] {
            let mut changed = ambient.clone();
            changed.push((key.into(), "core".into()));
            assert!(!ordinary(&build, changed));
        }
        for backends in [
            vec![],
            vec![CodegenBackendKind::TrustCg, CodegenBackendKind::Llvm],
            vec![CodegenBackendKind::Llvm, CodegenBackendKind::TrustIrCg],
        ] {
            build.config.target_config.entry(cross).or_default().codegen_backends = Some(backends);
            assert!(!ordinary(&build, ambient.clone()));
        }
        build.config.target_config.entry(cross).or_default().codegen_backends =
            Some(vec![CodegenBackendKind::Llvm]);
        assert!(ordinary(&build, ambient.clone()));
        build
            .config
            .target_config
            .entry(cross)
            .or_default()
            .rustflags
            .push("-Ztrust-verify=on".into());
        assert!(!ordinary(&build, ambient.clone()));
        build.config.target_config.remove(&cross);
        build.config.targets = vec![native, native];
        assert!(!ordinary(&build, ambient.clone()));
        let mut custom = cross;
        custom.file = Some(crate::utils::cache::INTERNER.intern_str("custom-apple.json"));
        build.config.targets = vec![native, custom];
        assert!(!ordinary(&build, ambient.clone()));
        custom = cross;
        custom.synthetic = true;
        build.config.targets = vec![native, custom];
        assert!(!ordinary(&build, ambient.clone()));
    }
    build.config.targets = vec![native];
    build.config.local_rebuild = true;
    assert!(!ordinary(&build, ambient.clone()));
    build.config.local_rebuild = false;
    for backends in [
        vec![],
        vec![CodegenBackendKind::TrustCg, CodegenBackendKind::Llvm],
        vec![CodegenBackendKind::Llvm, CodegenBackendKind::TrustIrCg],
        vec![CodegenBackendKind::Llvm, CodegenBackendKind::Custom("unknown".into())],
    ] {
        build.config.rust_codegen_backends = backends;
        assert!(!ordinary(&build, ambient.clone()));
    }
    build.config.rust_codegen_backends =
        vec![CodegenBackendKind::Llvm, CodegenBackendKind::TrustCg];
    assert!(ordinary(&build, ambient.clone()));
    build.config.rust_rustflags.push("-Zcodegen-backend=trust-cg".into());
    assert!(!ordinary(&build, ambient.clone()));
    build.config.rust_rustflags.clear();
    build.config.external_rustc = Some("custom".into());
    assert!(!ordinary(&build, ambient.clone()));
    build.config.external_rustc = None;
    build.config.full_bootstrap = true;
    assert!(!ordinary(&build, ambient.clone()));
    build.config.full_bootstrap = false;
    assert!(ordinary(&build, ambient.clone()));
    for key in [
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "RUSTFLAGS_NOT_BOOTSTRAP",
        "CARGO_TARGET_X_RUSTFLAGS",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        "CARGO_PROFILE_RELEASE_CODEGEN_BACKEND",
        "CARGO_PROFILE_DEV_BUILD_OVERRIDE_CODEGEN_BACKEND",
        "CARGO_UNSTABLE_CODEGEN_BACKEND",
        "RUSTC_WRAPPER",
        "TRUST_BOOTSTRAP_VERIFY_LIBRARY",
        "TRUST_UNKNOWN_CONTROL",
        "TCG_EXTERNAL_CLEAN_CHECKER",
        "TOOLCHAIN_AY_EXPECTED_SYSROOT",
        "LEAN_PATH",
    ] {
        let mut changed = ambient.clone();
        changed.push((key.into(), "unknown".into()));
        assert!(!ordinary(&build, changed), "{key}");
    }
    // Trust: Bootstrap hands CARGOFLAGS* to every Cargo; only lockfile and network
    // switches keep the audited posture.
    for key in ["CARGOFLAGS", "CARGOFLAGS_BOOTSTRAP", "CARGOFLAGS_NOT_BOOTSTRAP"] {
        for flags in [
            "--config env.RUSTC_WRAPPER_REAL='/x/w'",
            "--offline --config build.rustc-wrapper='w'",
            "-Zadvanced-env",
        ] {
            let mut changed = ambient.clone();
            changed.push((key.into(), flags.into()));
            assert!(!ordinary(&build, changed), "{key}={flags}");
        }
        for flags in ["", "--offline", " --offline  --locked ", "--frozen"] {
            let mut changed = ambient.clone();
            changed.push((key.into(), flags.into()));
            assert!(ordinary(&build, changed), "{key}={flags}");
        }
    }
    assert!(!ordinary(&build, vec![ambient[0].clone()]));
    assert!(ordinary(&build, vec![ambient[0].clone(), ("TRUST_NO_VERIFY".into(), "1".into())]));
    let mut opt_in = ambient.clone();
    opt_in[1].1 = "-Ztrust-verify=off -Zcodegen-backend=trust-cg".into();
    assert!(!ordinary(&build, opt_in));
}

#[test]
fn intermediate_tool_deferral_refuses_ambient_cargo_configuration() {
    let context = crate::utils::tests::TestCtx::new();
    let src = context.dir().join("source");
    let home = context.dir().join("cargo-home");
    fs::create_dir_all(src.join(".cargo")).unwrap();
    fs::create_dir_all(&home).unwrap();
    assert!(intermediate_tool_cargo_configuration_known(&src, &home));
    fs::write(
        src.join(".cargo/config.toml"),
        "[build]\njobs = 4\n[net]\ngit-fetch-with-cli = true\n",
    )
    .unwrap();
    assert!(intermediate_tool_cargo_configuration_known(&src, &home));
    // Trust: exercise the tracked config, including its overridden output
    // directory, so an ordinary workspace setting cannot disable deferral.
    fs::write(src.join(".cargo/config.toml"), include_str!("../../../../../../.cargo/config.toml"))
        .unwrap();
    assert!(intermediate_tool_cargo_configuration_known(&src, &home));
    // Trust: a thread-stack size is the one `[env]` entry that cannot reach the
    // compiler's selection or verification policy.
    for text in [
        "[env]\nRUST_MIN_STACK = '16777216'\n",
        "[env]\nRUST_MIN_STACK = { value = '16777216', force = false }\n",
        "[env]\nRUST_MIN_STACK = { value = '16777216' }\n",
    ] {
        fs::write(src.join(".cargo/config.toml"), text).unwrap();
        assert!(intermediate_tool_cargo_configuration_known(&src, &home), "{text}");
    }
    for text in [
        "[env]\nRUST_MIN_STACK = '16777216'\nTRUST_BOOTSTRAP_VERIFY_LIBRARY = 'core'\n",
        "[env]\nRUSTFLAGS = '-Ztrust-verify=off'\n",
        "[env]\nRUSTC_BOOTSTRAP = '1'\n",
        "[env]\n",
        "[env]\nTRUST_NO_VERIFY = '1'\n",
        "[env]\nRUST_MIN_STACK = '1'\nRUSTC_BOOTSTRAP = '1'\n",
        "[env]\nRUST_MIN_STACK = { value = '16777216', force = true }\n",
        "[env]\nRUST_MIN_STACK = { value = '16M' }\n",
        "[env]\nRUST_MIN_STACK = { value = 16777216, force = false }\n",
        "[env]\nRUST_MIN_STACK = 16777216\n",
        "[env]\nRUST_MIN_STACK = ''\n",
        "[env]\nRUST_MIN_STACK = '16M'\n",
        "[env]\nRUST_MIN_STACK = { value = '16777216', relative = true }\n",
        "[env]\nRUST_MIN_STACK = { value = '16777216', force = 'yes' }\n",
        "[env]\nRUST_MIN_STACK = { force = false }\n",
        "[env]\nRUST_MIN_STACK = ['16777216']\n",
        "env = 'RUST_MIN_STACK'\n",
    ] {
        fs::write(src.join(".cargo/config.toml"), text).unwrap();
        assert!(!intermediate_tool_cargo_configuration_known(&src, &home), "{text}");
    }
    for text in [
        "[build]\ntarget-dir = 7\n",
        "[build]\ntarget-dir = false\n",
        "[build]\ntarget-dir = ['target']\n",
        "[build.target-dir]\npath = 'target'\n",
        "[build]\ntarget-dir = 'target'\nrustc-wrapper = 'custom'\n",
        "[build]\ntarget-dir = 'target'\nunknown = true\n",
        "[build]\nrustflags = ['-Zcodegen-backend=trust-cg']\n",
        "[build]\nrustc-workspace-wrapper = 'custom'\n",
        "[env]\nTRUST_BOOTSTRAP_VERIFY_LIBRARY = 'core'\n",
        "not toml",
    ] {
        fs::write(src.join(".cargo/config.toml"), text).unwrap();
        assert!(!intermediate_tool_cargo_configuration_known(&src, &home));
    }
    fs::remove_file(src.join(".cargo/config.toml")).unwrap();
    for path in [
        home.join("config"),
        home.join("config.toml"),
        src.join(".cargo/config"),
        context.dir().join(".cargo/config.toml"),
    ] {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, "").unwrap();
        assert!(!intermediate_tool_cargo_configuration_known(&src, &home));
        fs::remove_file(path).unwrap();
    }
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(home.join("missing"), home.join("config.toml")).unwrap();
        assert!(!intermediate_tool_cargo_configuration_known(&src, &home));
    }
    assert!(!intermediate_tool_cargo_configuration_known(&src, Path::new("relative-home")));
}

#[cfg(unix)]
#[test]
fn intermediate_tool_deferral_keeps_requested_stage1_and_explicit_frontend() {
    if intermediate_tool_graph_isolated(
        "core::build_steps::tool::tests::intermediate_tool_deferral_keeps_requested_stage1_and_explicit_frontend",
    ) {
        return;
    }
    for stage in [1, 2] {
        let context = crate::utils::tests::TestCtx::new();
        let mut build = crate::core::session::Session::new(
            context
                .config("build")
                .stage(stage)
                .args(&[
                    "--set",
                    "build.extended=true",
                    "--set",
                    "rust.trust-source-identity=false",
                ])
                .create_config(),
        );
        intermediate_tool_source_fixture(&context, &mut build);
        let builder = Builder::new(&build);
        let target = builder.config.host_target;
        let compiler = Compiler::new(1, target);
        builder.sysroot(compiler);
        let build_compiler =
            get_tool_target_compiler(&builder, ToolTargetBuildMode::Dist(compiler));
        builder.ensure(TCargoTrust::from_build_compiler(build_compiler, target));
        let tools: Vec<_> = builder
            .step_cache()
            .inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
                (step.output_compiler.stage == 1
                    && ["ay", "clean", "targo", "targo-trust", "trustd", "ty"].contains(&step.tool))
                .then_some(step.tool)
            })
            .into_iter()
            .flatten()
            .collect();
        for tool in ["ay", "targo-trust", "trustd"] {
            assert!(tools.contains(&tool), "{stage}: {tools:?}");
        }
        if stage == 1 {
            for tool in ["clean", "targo", "ty"] {
                assert!(tools.contains(&tool), "requested Stage1: {tools:?}");
            }
        } else {
            assert_eq!(
                tools,
                ["ay", "targo-trust", "trustd"],
                "the explicit frontend retains its daemon without eagerly building unrelated CLIs"
            );
        }
        // Eager deferral never changes which existing artifacts restoration
        // considers, including the Targo compatibility alias.
        let bins = restored_sysroot_bins(&builder);
        for tool in ["ay", "clean", "targo", "targo-trust", "trustd", "ty"] {
            assert!(bins.contains(&(tool, tool)));
        }
        assert_eq!(upstream_compat_bin_for_tool_source("targo"), Some("cargo"));
    }
}

// Trust: exercise the generated build graph for the actual formatter package.
// The package also contains two development-only binaries that do not ship.
#[test]
fn formatter_steps_select_only_their_declared_public_binary() {
    let context = crate::utils::tests::TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "build.extended=true", "--set", "build.tools=['trustfmt']"])
        .path("src/tools/trustfmt")
        .create_config();
    let build = crate::core::session::Session::new(config);
    let builder = Builder::new(&build);
    builder.execute_cli();
    let producers = builder.step_cache().inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
        (
            step.tool,
            step.path,
            step.mode == Mode::ToolRustcPrivate,
            step.build_compiler.stage,
            step.output_compiler.stage,
            step.extra_features.clone(),
            step.cargo_args.clone(),
        )
    });
    let formatters: Vec<_> =
        producers.into_iter().filter(|step| step.1 == "src/tools/trustfmt").collect();
    assert_eq!(formatters.len(), 2, "{formatters:?}");
    for name in ["rustfmt", "cargo-fmt"] {
        let step = formatters.iter().find(|step| step.0 == name).unwrap();
        assert!(step.2);
        assert_eq!((step.3, step.4), (0, 1));
        assert!(step.5.is_empty());
        assert_eq!(
            step.6,
            vec!["--bin".to_string(), name.to_string()],
            "this real package otherwise builds rustfmt-format-diff and git-rustfmt too"
        );
    }
    assert!(!formatters.iter().any(|step| matches!(step.0, "rustfmt-format-diff" | "git-rustfmt")));
}

#[test]
fn compiletest_entry_features_stay_in_their_actual_tool_commands() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let compiler = Compiler::new(0, target);
    // Exercise the actual macro-generated tool constructors, including the
    // library's sole other consumer, rather than a parallel recipe table.
    builder.tool(Tool::Compiletest);
    builder.tool(Tool::RustdocGUITest);
    builder.tool(Tool::Tidy);
    let recipes = std::cell::RefCell::new(Vec::new());
    builder.step_cache().inspect_all_steps_of_type::<ToolBuild, _>(|recipe, _| {
        if ["compiletest", "rustdoc-gui-test", "tidy"].contains(&recipe.tool) {
            recipes.borrow_mut().push(recipe.clone());
        }
    });
    let mut cases = Vec::new();
    for recipe in recipes.into_inner() {
        let mut cargo = prepare_tool_cargo(
            &builder,
            recipe.build_compiler,
            recipe.mode,
            target,
            Kind::Build,
            recipe.path,
            recipe.source_type.clone(),
            &recipe.extra_features,
        );
        if !recipe.allow_features.is_empty() {
            cargo.allow_features(recipe.allow_features);
        }
        cases.push((recipe.tool, cargo));
    }
    cases.push(("unit", prepare_compiletest_test_cargo(&builder, compiler, target)));
    let mut observed = std::collections::HashMap::new();
    for (name, cargo) in cases {
        let mut command = cargo.into_cmd();
        command.mark_as_executed();
        let features = command
            .get_envs()
            .find(|(key, _)| *key == "RUSTC_ALLOW_FEATURES")
            .and_then(|(_, value)| value)
            .expect("tool sandbox remains explicit")
            .to_str()
            .unwrap()
            .split(',')
            .map(str::to_owned)
            .collect::<HashSet<_>>();
        observed.insert(name, features);
    }
    let baseline = observed.get("tidy").expect("actual unrelated tool command");
    let fd = HashSet::from(["trust_process_inherit_fds".to_owned()]);
    for name in ["compiletest", "rustdoc-gui-test"] {
        let extras = observed[name].difference(baseline).cloned().collect::<HashSet<_>>();
        assert_eq!(extras, fd, "normal tool {name} has only native transport permission");
    }
    let unit = observed["unit"].difference(baseline).cloned().collect::<HashSet<_>>();
    assert_eq!(
        unit,
        HashSet::from(
            ["trust_process_inherit_fds", "test", "custom_test_frameworks", "exitcode_exit_method"]
                .map(str::to_owned)
        )
    );
    assert!(!baseline.contains("trust_process_inherit_fds"));
    assert!(!baseline.contains("custom_test_frameworks"));
}

#[test]
fn compiletest_check_steps_allow_what_their_builds_allow() {
    // Trust (COMPILETEST-CHECK-INHERIT-FDS-1): `x.py check src/tools/compiletest` checks
    // `--all-targets`, so it compiles compiletest's library test target as the unit
    // build does; rustdoc-gui-test links only the library. A `tool_check_step!` entry is
    // built only by running it, and its sandbox is the expression the entry names.
    let check = include_str!("../check.rs");
    let entry = |name: &str| {
        let start = check.find(&format!("tool_check_step!({name} {{")).expect("a check step");
        &check[start..start + check[start..].find("});").expect("the entry closes")]
    };
    let compiletest = entry("Compiletest");
    assert!(compiletest.contains("path: \"src/tools/compiletest\""), "{compiletest}");
    assert!(
        compiletest.contains("allow_features: tool::COMPILETEST_SELF_ALLOW_FEATURES"),
        "{compiletest}"
    );
    let gui = entry("RustdocGuiTest");
    assert!(gui.contains("allow_features: tool::COMPILETEST_ALLOW_FEATURES"), "{gui}");
    let unit: HashSet<&str> = COMPILETEST_SELF_ALLOW_FEATURES.split(',').collect();
    assert_eq!(
        unit,
        HashSet::from([
            "trust_process_inherit_fds",
            "test",
            "custom_test_frameworks",
            "exitcode_exit_method"
        ])
    );
    assert_eq!(COMPILETEST_ALLOW_FEATURES, "trust_process_inherit_fds");
}

#[test]
fn targo_doc_step_allows_what_targo_builds_allow() {
    // Trust: documenting Targo compiles the graph Targo's build compiles (ay-sat's
    // `allocator_ext` among it). Cargo's fingerprint does not record the shim's
    // allow-list, so a narrower doc list passes on a warm tree and refuses a cold one;
    // only its source names it.
    let doc = include_str!("../doc.rs");
    let start =
        doc.find("tool_doc!(\n    Cargo,\n    \"src/tools/targo\",").expect("Targo's doc step");
    let entry = &doc[start..start + doc[start..].find("\n);").expect("the entry closes")];
    assert!(entry.contains("allow_features: tool::TARGO_ALLOW_FEATURES"), "{entry}");
}

// Trust: the real recipe must not select the target compiler/Std or a test feature.
#[test]
fn vf5_resource_preparer_is_the_source_built_host_snapshot_binary() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(2).create_config());
    let builder = Builder::new(&build);
    let recipe = vf5_resource_tool_recipe(&builder);
    assert_eq!(recipe.mode, Mode::ToolBootstrap);
    assert_eq!(recipe.build_compiler.stage, 0);
    assert_eq!(recipe.build_compiler.host, builder.host_target);
    assert_eq!(recipe.target, builder.host_target);
    assert_eq!(recipe.path, "crates/trust-certify");
    assert_eq!(recipe.tool, "prepare_vf5_inputs");
    assert_eq!(recipe.allow_features, VF5_RESOURCE_ALLOW_FEATURES);
    assert_eq!(recipe.cargo_args, ["--bin", "prepare_vf5_inputs"]);
    assert_eq!(recipe.artifact_kind, ToolArtifactKind::Binary);
    assert!(recipe.extra_features.is_empty());
    // Trust: exactly what ahash, ay-sat and trust-types' try-sugar declare.
    assert_eq!(
        recipe.allow_features,
        "min_specialization,allocator_ext,try_trait_v2,try_trait_v2_residual"
    );
    assert!(matches!(recipe.cargo_input(&builder), CargoInput::Seed));
}

#[test]
fn vf5_resource_preparer_retains_the_solver_feature_sandbox() {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(2).create_config());
    let builder = Builder::new(&build);
    let recipe = vf5_resource_tool_recipe(&builder);
    let mut cargo = prepare_tool_cargo(
        &builder,
        recipe.build_compiler,
        recipe.mode,
        recipe.target,
        Kind::Build,
        recipe.path,
        recipe.source_type,
        &recipe.extra_features,
    );
    cargo.allow_features(recipe.allow_features);
    let mut command = cargo.into_cmd();
    command.mark_as_executed();
    let features = command
        .get_envs()
        .find(|(key, _)| *key == "RUSTC_ALLOW_FEATURES")
        .and_then(|(_, value)| value)
        .expect("the host preparer retains an explicit feature sandbox")
        .to_str()
        .unwrap();
    let allowed: HashSet<_> = features.split(',').collect();
    for feature in [
        "binary-dep-depinfo",
        "proc_macro_span",
        "min_specialization",
        "allocator_ext",
        "try_trait_v2",
        "try_trait_v2_residual",
    ] {
        assert!(allowed.contains(feature), "missing {feature}: {features}");
    }
    for feature in ["allocator_api", "specialization", "trust_process_inherit_fds"] {
        assert!(!allowed.contains(feature), "unrelated {feature}: {features}");
    }
}

#[test]
fn vf5_resource_dry_runs_discover_the_host_tool_without_running_policy() {
    use crate::core::config::DryRun;

    // Real builds plan with SelfCheck; explicit --dry-run uses UserSelected.
    // Both must consume BootstrapCommand without executing/parsing tool output.
    for dry_run in [DryRun::SelfCheck, DryRun::UserSelected] {
        let context = crate::utils::tests::TestCtx::new();
        let mut build =
            crate::core::session::Session::new(context.config("build").stage(1).create_config());
        build.config.set_dry_run(dry_run);
        let builder = Builder::new(&build);
        assert!(builder.config.dry_run());
        let target = builder.host_target;
        let root = context.dir().join("vf5-dry-run-sysroot");
        assert!(!root.exists());
        crate::core::build_steps::vf5_resource::install_into_sysroot(
            &builder,
            Compiler::new(0, target),
            Compiler::new(1, target),
            &root,
        );
        assert!(!root.exists(), "a dry run must not stage a resource");
        let cache = builder.step_cache();
        let preparers = cache
            .inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
                (step.tool == "prepare_vf5_inputs").then_some((
                    step.build_compiler.stage,
                    step.build_compiler.host,
                    step.target,
                    step.mode == Mode::ToolBootstrap, // Trust: retain exact mode equality in the sortable projection.
                    step.cargo_args.clone(),
                ))
            })
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(
            preparers,
            [(0, target, target, true, vec!["--bin".to_owned(), "prepare_vf5_inputs".to_owned()])],
            "dry-run dependency discovery must retain the real host-tool recipe",
        );
        assert!(
            cache
                .inspect_all_steps_of_type::<compile::Assemble, _>(|step, _| {
                    step.target_compiler.stage
                })
                .into_iter()
                .all(|stage| stage == 0),
            "the snapshot host-tool route must not recurse into target assembly",
        );
    }
}
