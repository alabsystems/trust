// ignore-tidy-file-filelength
use std::panic;

use build_helper::stage0_parser::parse_stage0_file;
use llvm::get_llvm_build_status;

use super::*;
use crate::core::build_steps::llvm::LlvmKind;
use crate::core::config::Config;
use crate::utils::cache::ExecutedStep;
use crate::utils::helpers::get_host_target;
use crate::utils::tests::git::{GitCtx, git_test};
use crate::utils::tests::{ConfigBuilder, TestCtx};

static TEST_TRIPLE_1: &str = "i686-unknown-haiku";
static TEST_TRIPLE_2: &str = "i686-unknown-hurd-gnu";

fn configure(cmd: &str, host: &[&str], target: &[&str]) -> Config {
    configure_with_args(&[cmd], host, target)
}

fn configure_with_args(cmd: &[&str], host: &[&str], target: &[&str]) -> Config {
    TestCtx::new().config(cmd[0]).args(&cmd[1..]).hosts(host).targets(target).create_config()
}

fn run_build(paths: &[PathBuf], config: Config) -> Cache {
    let sess = Session::new(config);
    let builder = Builder::new(&sess);
    builder.run_step_descriptions(&Builder::get_step_descriptions(builder.kind), paths);
    builder.cache
}

// Trust: use the actual Step graph, including std dependencies of aliases and
// compiler assembly. Source selection is not reconstructed from CLI strings.
#[test]
fn selected_std_source_readiness_follows_the_native_plan() {
    for (kind, stage, paths, expected) in [
        ("build", 1, vec!["library"], true),
        ("build", 1, vec!["compiler/rustc", "library"], true),
        ("build", 1, vec!["library/std"], true),
        ("check", 1, vec!["library/core"], true),
        ("build", 1, vec!["src/tools/tidy"], false),
        ("build", 1, vec!["targo-build-tool"], false),
    ] {
        let context = TestCtx::new();
        let mut config = context.config(kind).stage(stage).paths(&paths);
        if paths.contains(&"targo-build-tool") {
            config = config.args(&["--set", "rust.omit-git-hash=false"]);
        }
        let mut session = Session::new(config.create_config());
        session.config.set_dry_run(DryRun::SelfCheck);
        let builder = Builder::new(&session);
        builder.execute_cli();
        assert_eq!(builder.selected_std_sources.get(), expected, "{kind} stage{stage} {paths:?}");
    }
}

#[test]
fn selected_tool_source_readiness_follows_the_native_plan() {
    for (paths, required, absent) in [
        (
            vec!["compiler/rustc", "library"],
            "first-party/ay/crates/ay/Cargo.toml",
            "src/tools/tidy/Cargo.toml",
        ),
        (
            vec!["src/tools/tidy"],
            "src/tools/tidy/Cargo.toml",
            "first-party/ay/crates/ay/Cargo.toml",
        ),
        (
            vec!["targo-build-tool"],
            "src/tools/targo/Cargo.toml",
            "first-party/ay/crates/ay/Cargo.toml",
        ),
    ] {
        let context = TestCtx::new();
        let config = context
            .config("build")
            .stage(1)
            .paths(&paths)
            .args(&["--set", "rust.omit-git-hash=false"])
            .create_config();
        let mut session = Session::new(config);
        session.config.set_dry_run(DryRun::SelfCheck);
        let builder = Builder::new(&session);
        builder.execute_cli();
        let manifests = builder.selected_tool_sources.borrow();
        assert!(manifests.contains(Path::new(required)), "{paths:?}: {manifests:?}");
        assert!(!manifests.contains(Path::new(absent)), "{paths:?}: {manifests:?}");
    }
}

#[test]
#[should_panic(expected = "status code: 1")]
fn selected_std_readiness_does_not_promote_unsupported_stage0_builds() {
    let context = TestCtx::new();
    let session = Session::new(context.config("build").stage(0).path("library").create_config());
    Builder::new(&session).execute_cli();
}

#[test]
fn compiler_runtime_paths_resolve_llvm_only_for_built_compilers() {
    for stage in [0, 1] {
        let context = TestCtx::new();
        let config = context
            .config("test")
            .no_override_download_ci_llvm()
            .with_default_toml_config("[llvm]\ndownload-ci-llvm = true\n")
            .create_config();
        let session = Session::new(config);
        let builder = Builder::new(&session);
        let compiler = Compiler::new(stage, builder.host_target);
        assert!(!builder.cache.contains::<llvm::LlvmFromCi>());
        let paths = builder.rustc_lib_paths(compiler);
        assert_eq!(paths.first(), Some(&builder.rustc_libdir(compiler)));
        // A seed's runtime comes from its original sysroot. Looking up its
        // loader path must not resolve the current source's LLVM provider.
        assert_eq!(builder.cache.contains::<llvm::LlvmFromCi>(), stage != 0);
    }
}

fn check_cli<const N: usize>(paths: [&str; N]) {
    run_build(
        &paths.map(PathBuf::from),
        configure_with_args(&paths, &[TEST_TRIPLE_1], &[TEST_TRIPLE_1]),
    );
}

#[test]
fn test_valid() {
    // make sure multi suite paths are accepted
    check_cli(["test", "tests/ui/bootstrap/self-test/a.rs", "tests/ui/bootstrap/self-test/b.rs"]);
}

#[test]
#[should_panic]
fn test_invalid() {
    // make sure that invalid paths are caught, even when combined with valid paths
    check_cli(["test", "library/std", "x"]);
}

#[test]
fn ci_rustc_if_unchanged_invalidate_on_compiler_changes() {
    git_test(|ctx| {
        prepare_rustc_checkout(ctx);
        ctx.create_upstream_merge(&["compiler/bar"]);
        // This change should invalidate download-ci-rustc
        ctx.create_nonupstream_merge(&["compiler/foo"]);

        let config = parse_config_download_rustc_at(ctx.get_path(), "if-unchanged", true);
        assert_eq!(config.download_rustc_commit, None);
    });
}

#[test]
fn ci_rustc_if_unchanged_do_not_invalidate_on_library_changes_outside_ci() {
    git_test(|ctx| {
        prepare_rustc_checkout(ctx);
        let sha = ctx.create_upstream_merge(&["compiler/bar"]);
        // This change should not invalidate download-ci-rustc
        ctx.create_nonupstream_merge(&["library/foo"]);

        let config = parse_config_download_rustc_at(ctx.get_path(), "if-unchanged", false);
        assert_eq!(config.download_rustc_commit, Some(sha));
    });
}

#[test]
fn ci_rustc_if_unchanged_do_not_invalidate_on_tool_changes() {
    git_test(|ctx| {
        prepare_rustc_checkout(ctx);
        let sha = ctx.create_upstream_merge(&["compiler/bar"]);
        // This change should not invalidate download-ci-rustc
        ctx.create_nonupstream_merge(&["src/tools/foo"]);

        let config = parse_config_download_rustc_at(ctx.get_path(), "if-unchanged", true);
        assert_eq!(config.download_rustc_commit, Some(sha));
    });
}

/// Prepares the given directory so that it looks like a rustc checkout.
/// Also configures `GitCtx` to use the correct merge bot e-mail for upstream merge commits.
fn prepare_rustc_checkout(ctx: &mut GitCtx) {
    ctx.merge_bot_email =
        format!("Merge bot <{}>", parse_stage0_file().config.git_merge_commit_email);
    ctx.write("src/ci/channel", "nightly");
    ctx.commit();
}

/// Parses a Config directory from `path`, with the given value of `download_rustc`.
fn parse_config_download_rustc_at(path: &Path, download_rustc: &str, ci: bool) -> Config {
    TestCtx::new()
        .config("build")
        .args(&[
            "--ci",
            if ci { "true" } else { "false" },
            format!("--set=rust.download-rustc='{download_rustc}'").as_str(),
            "--src",
            path.to_str().unwrap(),
        ])
        .no_override_download_ci_llvm()
        .create_config()
}

mod sysroot_target_dirs {
    use super::{
        Builder, Compiler, Session, TEST_TRIPLE_1, TEST_TRIPLE_2, TargetSelection, configure,
    };

    #[test]
    fn test_sysroot_target_libdir() {
        let sess = Session::new(configure("build", &[TEST_TRIPLE_1], &[TEST_TRIPLE_1]));
        let builder = Builder::new(&sess);
        let target_triple_1 = TargetSelection::from_user(TEST_TRIPLE_1);
        let compiler = Compiler::new(1, target_triple_1);
        let target_triple_2 = TargetSelection::from_user(TEST_TRIPLE_2);
        let actual = builder.sysroot_target_libdir(compiler, target_triple_2);

        assert_eq!(
            builder
                .sysroot(compiler)
                .join(builder.sysroot_libdir_relative(compiler))
                .join("rustlib")
                .join(TEST_TRIPLE_2)
                .join("lib"),
            actual
        );
    }

    #[test]
    fn test_sysroot_target_bindir() {
        let sess = Session::new(configure("build", &[TEST_TRIPLE_1], &[TEST_TRIPLE_1]));
        let builder = Builder::new(&sess);
        let target_triple_1 = TargetSelection::from_user(TEST_TRIPLE_1);
        let compiler = Compiler::new(1, target_triple_1);
        let target_triple_2 = TargetSelection::from_user(TEST_TRIPLE_2);
        let actual = builder.sysroot_target_bindir(compiler, target_triple_2);

        assert_eq!(
            builder
                .sysroot(compiler)
                .join(builder.sysroot_libdir_relative(compiler))
                .join("rustlib")
                .join(TEST_TRIPLE_2)
                .join("bin"),
            actual
        );
    }
}

/// Regression test for <https://github.com/rust-lang/rust/issues/134916>.
///
/// The command `./x test compiler` should invoke the step that runs unit tests
/// for (most) compiler crates, rather than any other step that also registers
/// a `compiler/` source path.
#[test]
fn test_test_compiler() {
    let config = configure_with_args(&["test", "compiler"], &[&host_target()], &[TEST_TRIPLE_1]);
    let cache = run_build(&config.paths.clone(), config);

    assert!(cache.contains::<test::CrateLibrustc>());
}

#[test]
fn test_test_coverage() {
    struct Case {
        cmd: &'static [&'static str],
        expected: &'static [&'static str],
    }
    let cases = &[
        Case { cmd: &["test"], expected: &["coverage-map", "coverage-run"] },
        Case { cmd: &["test", "coverage"], expected: &["coverage-map", "coverage-run"] },
        Case { cmd: &["test", "coverage-map"], expected: &["coverage-map"] },
        Case { cmd: &["test", "coverage-run"], expected: &["coverage-run"] },
        Case { cmd: &["test", "coverage", "--skip=coverage"], expected: &[] },
        Case { cmd: &["test", "coverage", "--skip=tests/coverage"], expected: &[] },
        Case { cmd: &["test", "coverage", "--skip=coverage-map"], expected: &["coverage-run"] },
        Case { cmd: &["test", "coverage", "--skip=coverage-run"], expected: &["coverage-map"] },
        Case { cmd: &["test", "--skip=coverage-map", "--skip=coverage-run"], expected: &[] },
        Case { cmd: &["test", "coverage", "--skip=tests"], expected: &[] },
    ];

    for &Case { cmd, expected } in cases {
        // Print each test case so that if one fails, the most recently printed
        // case is the one that failed.
        println!("Testing case: {cmd:?}");
        let config = configure_with_args(cmd, &[], &[TEST_TRIPLE_1]);
        let cache = run_build(&config.paths.clone(), config);

        let modes =
            cache.inspect_all_steps_of_type::<test::Coverage, _>(|step, ()| step.mode.as_str());
        assert_eq!(modes, expected);
    }
}

#[test]
fn test_prebuilt_llvm_config_path_resolution() {
    fn configure(config: &str) -> Config {
        TestCtx::new().config("build").with_default_toml_config(config).create_config()
    }

    // Removes Windows disk prefix if present
    fn drop_win_disk_prefix_if_present(path: PathBuf) -> PathBuf {
        let path_str = path.to_str().unwrap();
        if let Some((_, without_prefix)) = path_str.split_once(":/") {
            return PathBuf::from(format!("/{}", without_prefix));
        }

        path
    }

    let config = configure(
        r#"
            [llvm]
            download-ci-llvm = false

            [build]
            build = "x86_64-unknown-linux-gnu"
            host = ["arm-unknown-linux-gnueabihf"]
            target = ["arm-unknown-linux-gnueabihf"]

            [target.x86_64-unknown-linux-gnu]
            llvm-config = "/some/path/to/llvm-config"

            [target.arm-unknown-linux-gnueabihf]
            cc = "arm-linux-gnueabihf-gcc"
            cxx = "arm-linux-gnueabihf-g++"
        "#,
    );

    let sess = Session::new(config);
    let builder = Builder::new(&sess);

    let host_llvm_config = PathBuf::from("/some/path/to/llvm-config");

    let actual =
        get_llvm_build_status(&builder, TargetSelection::from_user("arm-unknown-linux-gnueabihf"))
            .llvm_output()
            .llvm_config()
            .to_path_buf();
    let actual = drop_win_disk_prefix_if_present(actual);
    assert_ne!(
        host_llvm_config, actual,
        "llvm-config should be returned for the given target, not the host"
    );

    let actual = get_llvm_build_status(&builder, builder.config.host_target)
        .llvm_output()
        .llvm_config()
        .to_path_buf();
    let actual = drop_win_disk_prefix_if_present(actual);
    assert_eq!(host_llvm_config, actual);

    let config = configure(
        r#"
            [llvm]
            download-ci-llvm = false
        "#,
    );

    let sess = Session::new(config.clone());
    let builder = Builder::new(&sess);

    let actual = get_llvm_build_status(&builder, builder.config.host_target)
        .llvm_output()
        .llvm_config()
        .to_path_buf();
    let expected = builder
        .out
        .join(builder.config.host_target)
        .join("llvm/bin")
        .join(exe("llvm-config", builder.config.host_target));
    assert_eq!(expected, actual);

    let config = configure(
        r#"
            [llvm]
            download-ci-llvm = "if-unchanged"
        "#,
    );

    let sess = Session::new(config.clone());
    let builder = Builder::new(&sess);

    let llvm = get_llvm_build_status(&builder, builder.config.host_target);
    let llvm = llvm.llvm_output();
    // CI-LLVM isn't always available; check if it's enabled before testing.
    if llvm.kind() == LlvmKind::DownloadedFromCi {
        let actual = llvm.llvm_config().to_path_buf();
        let expected = builder
            .out
            .join(builder.config.host_target)
            .join("ci-llvm/bin")
            .join(exe("llvm-config", builder.config.host_target));
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_is_builder_target() {
    let target1 = TargetSelection::from_user(TEST_TRIPLE_1);
    let target2 = TargetSelection::from_user(TEST_TRIPLE_2);

    for (target1, target2) in [(target1, target2), (target2, target1)] {
        let mut config = configure("build", &[], &[]);
        config.host_target = target1;
        let sess = Session::new(config);
        let builder = Builder::new(&sess);

        assert!(builder.config.is_host_target(target1));
        assert!(!builder.config.is_host_target(target2));
    }
}

/// When bootstrap detects a step dependency cycle (which is a bug), its panic
/// message should show the actual steps on the stack, not just several copies
/// of `Any { .. }`.
#[test]
fn step_cycle_debug() {
    let config = configure_with_args(&["run", "cyclic-step"], &[TEST_TRIPLE_1], &[TEST_TRIPLE_1]);

    let err = panic::catch_unwind(|| run_build(&config.paths.clone(), config)).unwrap_err();
    let err = err.downcast_ref::<String>().unwrap().as_str();

    assert!(!err.contains("Any"));
    assert!(err.contains("CyclicStep { n: 1 }"));
}

/// The `AnyDebug` trait should delegate to the underlying type's `Debug`, and
/// should also allow downcasting as expected.
#[test]
fn any_debug() {
    #[derive(Debug, PartialEq, Eq)]
    struct MyStruct {
        x: u32,
    }

    let x: &dyn AnyDebug = &MyStruct { x: 7 };

    // Debug-formatting should delegate to the underlying type.
    assert_eq!(format!("{x:?}"), format!("{:?}", MyStruct { x: 7 }));
    // Downcasting to the underlying type should succeed.
    assert_eq!(x.downcast_ref::<MyStruct>(), Some(&MyStruct { x: 7 }));
}

/// These tests use expect-test for snapshot testing.
/// Run `x test bootstrap --bless` to update them.
mod snapshot {
    // Trust: snapshot cases use ConfigBuilder methods rather than the outer test helpers.
    use crate::core::build_steps::{dist, install, test};
    use crate::core::builder::tests::{
        RenderConfig, TEST_TRIPLE_1, TEST_TRIPLE_2, assert_compiler_plan, host_target,
    };
    use crate::core::builder::{Builder, CommandLineStep, Kind, StepMetadata};
    use crate::core::compiler::Compiler;
    use crate::core::config::TargetSelection;
    use crate::core::config::toml::target::{
        DefaultLinuxLinkerOverride, with_default_linux_linker_overrides,
    };
    use crate::core::session::Session;
    use crate::utils::tests::{ConfigBuilder, TestCtx};

    // Trust: select the runtime frontend explicitly, including in a bare
    // checkout. Otherwise AY's availability silently selects a different
    // dependency order before Assemble reaches target LLVM.
    fn with_verifier_frontend(config: ConfigBuilder) -> ConfigBuilder {
        config.args(&["--set", "build.extended=true", "--set", "build.tools=['targo-trust']"])
    }

    #[test]
    fn build_default() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>"#]]
        .assert_eq(&ctx.config("build").render_steps());
    }

    #[test]
    fn build_cross_compile() {
        let ctx = TestCtx::new();

        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] rustc 2 <host> -> std 2 <target1>
            [build] rustdoc 2 <host>
            [build] llvm <target1>
            [build] rustc 1 <host> -> rustc 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustdoc 2 <target1>"#]]
        .assert_eq(
            &ctx.config("build")
                // Cross-compilation fails on stage 1, as we don't have a stage0 std available
                // for non-host targets.
                .stage(2)
                .hosts(&[&host_target(), TEST_TRIPLE_1])
                .targets(&[&host_target(), TEST_TRIPLE_1])
                .render_steps(),
        );
    }

    #[test]
    fn build_with_empty_host() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <target1>"#]]
        .assert_eq(&ctx.config("build").hosts(&[]).targets(&[TEST_TRIPLE_1]).render_steps());
    }

    #[test]
    fn build_compiler_no_explicit_stage() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").path("compiler").render_steps());
    }

    #[test]
    fn build_rustc_no_explicit_stage() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").path("rustc").render_steps());
    }

    #[test]
    #[should_panic]
    fn build_compiler_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("build").path("compiler").stage(0).run();
    }

    #[test]
    fn build_compiler_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").path("compiler").stage(1).render_steps());
    }

    #[test]
    fn build_compiler_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>"#]]
        .assert_eq(&ctx.config("build").path("compiler").stage(2).render_steps());
    }

    #[test]
    fn build_compiler_stage_2_full_bootstrap_installs_target_std() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>"#]]
        .assert_eq(
            &ctx.config("build")
                .path("compiler")
                .stage(2)
                .args(&["--set", "build.full-bootstrap=true"])
                .render_steps(),
        );
    }

    #[test]
    fn build_compiler_stage_3() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> rustc 3 <host>
            [build] rustc 3 <host> -> std 3 <host>"#]]
        .assert_eq(&ctx.config("build").path("compiler").stage(3).render_steps());
    }

    #[test]
    fn build_compiler_stage_3_cross() {
        // Trust: runtime tools request std before target LLVM. The repeated
        // host std rows have distinct link policies.
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] rustc 2 <host> -> std 2 <target1>
            [build] llvm <target1>
            [build] rustc 2 <host> -> rustc 3 <target1>
            [build] rustc 3 <target1> -> std 3 <target1>"#]]
        .assert_eq(
            &with_verifier_frontend(ctx.config("build"))
                .path("compiler")
                .hosts(&[TEST_TRIPLE_1])
                .stage(3)
                .render_steps(),
        );
    }

    #[test]
    fn build_compiler_stage_3_full_bootstrap() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> rustc 3 <host>
            [build] rustc 3 <host> -> std 3 <host>"#]]
        .assert_eq(
            &ctx.config("build")
                .path("compiler")
                .stage(3)
                .args(&["--set", "build.full-bootstrap=true"])
                .render_steps(),
        );
    }

    #[test]
    fn build_compiler_stage_3_cross_full_bootstrap() {
        // Trust: retain the full-bootstrap dependency order and both host std keys.
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <target1>
            [build] llvm <target1>
            [build] rustc 2 <host> -> rustc 3 <target1>
            [build] rustc 3 <target1> -> std 3 <target1>"#]]
        .assert_eq(
            &with_verifier_frontend(ctx.config("build"))
                .path("compiler")
                .stage(3)
                .hosts(&[TEST_TRIPLE_1])
                .args(&["--set", "build.full-bootstrap=true"])
                .render_steps(),
        );
    }

    #[test]
    fn targeted_trust_cg_builds_full_compiler_without_self_hosting_std_or_plugin() {
        let ctx = TestCtx::new();
        let steps = ctx
            .config("build")
            .path("compiler/rustc_codegen_trust_cg")
            .stage(1)
            // Trust-CG is builtin, but it is deliberately too narrow to
            // self-host rustc. Keep LLVM first so the complete compiler is
            // built by the supported bootstrap backend while the targeted
            // Trust-CG path still selects the builtin adapter.
            .args(&["--set", "rust.codegen-backends=['llvm', 'trust-cg']"])
            .render_steps();

        assert!(
            steps.contains("[build] rustc 0 <host> -> rustc 1 <host>"),
            "targeted trust-cg build must build the complete compiler:\n{steps}"
        );
        assert!(
            !steps.contains("[build] rustc 1 <host> -> std 1 <host>"),
            "targeted trust-cg build must not Assemble/self-host stage1 std:\n{steps}"
        );
        assert!(
            !steps.contains("-> rustc_codegen_trust_cg"),
            "trust-cg is builtin and must never be built as a standalone plugin:\n{steps}"
        );
    }

    #[test]
    fn build_compiler_tools() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 0 <host> -> LldWrapper 1 <host>
            [build] rustc 0 <host> -> LlvmBitcodeLinker 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 1 <host> -> LldWrapper 2 <host>
            [build] rustc 1 <host> -> LlvmBitcodeLinker 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustdoc 2 <host>"#]]
        .assert_eq(
            &ctx.config("build")
                .stage(2)
                .args(&["--set", "rust.lld=true", "--set", "rust.llvm-bitcode-linker=true"])
                .render_steps(),
        );
    }

    #[test]
    fn build_compiler_tools_cross() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 0 <host> -> LldWrapper 1 <host>
            [build] rustc 0 <host> -> LlvmBitcodeLinker 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 1 <host> -> LldWrapper 2 <host>
            [build] rustc 1 <host> -> LlvmBitcodeLinker 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] rustc 2 <host> -> std 2 <target1>
            [build] llvm <target1>
            [build] rustc 1 <host> -> rustc 2 <target1>
            [build] rustc 1 <host> -> LldWrapper 2 <target1>
            [build] rustc 1 <host> -> LlvmBitcodeLinker 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustdoc 2 <target1>"#]]
        .assert_eq(
            &ctx.config("build")
                .stage(2)
                .args(&["--set", "rust.lld=true", "--set", "rust.llvm-bitcode-linker=true"])
                .hosts(&[TEST_TRIPLE_1])
                .render_steps(),
        );
    }

    #[test]
    fn build_compiler_lld_opt_in() {
        with_default_linux_linker_overrides(
            [(host_target(), DefaultLinuxLinkerOverride::SelfContainedLldCc)].into(),
            || {
                let ctx = TestCtx::new();
                expect_test::expect![[r#"
                    [build] llvm <host>
                    [build] rustc 0 <host> -> rustc 1 <host>
                    [build] rustc 0 <host> -> LldWrapper 1 <host>
                    [build] rustc 1 <host> -> std 1 <host>"#]]
                .assert_eq(&ctx.config("build").path("compiler").render_steps());
            },
        );
    }

    #[test]
    fn build_compiler_lld_opt_in_lld_disabled() {
        with_default_linux_linker_overrides(
            [(host_target(), DefaultLinuxLinkerOverride::SelfContainedLldCc)].into(),
            || {
                let ctx = TestCtx::new();
                expect_test::expect![[r#"
                    [build] llvm <host>
                    [build] rustc 0 <host> -> rustc 1 <host>
                    [build] rustc 1 <host> -> std 1 <host>"#]]
                .assert_eq(
                    &ctx.config("build")
                        .path("compiler")
                        .args(&["--set", "rust.lld=false"])
                        .render_steps(),
                );
            },
        );
    }

    #[test]
    fn build_library_no_explicit_stage() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").path("library").render_steps());
    }

    #[test]
    #[should_panic]
    fn build_library_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("build").path("library").stage(0).run();
    }

    #[test]
    fn build_library_stage_0_local_rebuild() {
        let ctx = TestCtx::new();
        expect_test::expect![["[build] rustc 0 <host> -> std 0 <target1>"]].assert_eq(
            &ctx.config("build")
                .path("library")
                .stage(0)
                .targets(&[TEST_TRIPLE_1])
                .args(&["--set", "build.local-rebuild=true"])
                .render_steps(),
        );
    }

    #[test]
    fn build_library_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").path("library").stage(1).render_steps());
    }

    #[test]
    fn build_library_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>"#]]
        .assert_eq(&ctx.config("build").path("library").stage(2).render_steps());
    }

    #[test]
    fn build_miri_no_explicit_stage() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> miri 1 <host>"#]]
        .assert_eq(&ctx.config("build").path("miri").render_steps());
    }

    #[test]
    #[should_panic]
    fn build_miri_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("build").path("miri").stage(0).run();
    }

    #[test]
    fn build_miri_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> miri 1 <host>"#]]
        .assert_eq(&ctx.config("build").path("miri").stage(1).render_steps());
    }

    #[test]
    fn build_miri_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> miri 2 <host>"#]]
        .assert_eq(&ctx.config("build").path("miri").stage(2).render_steps());
    }

    #[test]
    fn build_error_index() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> error-index 1 <host>"#]]
        .assert_eq(&ctx.config("build").path("error_index_generator").render_steps());
    }

    #[test]
    fn build_bootstrap_tool_no_explicit_stage() {
        let ctx = TestCtx::new();
        expect_test::expect![["[build] rustc 0 <host> -> OptimizedDist 1 <host>"]]
            .assert_eq(&ctx.config("build").path("opt-dist").render_steps());
    }

    #[test]
    #[should_panic]
    fn build_bootstrap_tool_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("build").path("opt-dist").stage(0).run();
    }

    #[test]
    fn build_bootstrap_tool_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![["[build] rustc 0 <host> -> OptimizedDist 1 <host>"]]
            .assert_eq(&ctx.config("build").path("opt-dist").stage(1).render_steps());
    }

    #[test]
    fn build_bootstrap_tool_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![["[build] rustc 0 <host> -> OptimizedDist 1 <host>"]]
            .assert_eq(&ctx.config("build").path("opt-dist").stage(2).render_steps());
    }

    #[test]
    fn build_default_stage() {
        let ctx = TestCtx::new();
        assert_eq!(ctx.config("build").path("compiler").create_config().stage, 1);
    }

    /// Ensure that if someone passes both a single crate and `library`, all
    /// library crates get built.
    #[test]
    fn alias_and_path_for_library() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").paths(&["library", "core"]).render_steps());

        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").paths(&["std"]).render_steps());

        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").paths(&["core"]).render_steps());

        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("build").paths(&["alloc"]).render_steps());

        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]"#]].assert_eq(&ctx.config("doc")
            .paths(&["library", "core"])
            .render_steps());
    }

    #[test]
    fn build_all() {
        // Trust: include the runtime frontend's target std dependency explicitly.
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] llvm <target1>
            [build] rustc 1 <host> -> rustc 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <target1>
            [build] rustc 1 <host> -> std 1 <target2>
            [build] rustc 2 <host> -> std 2 <target2>"#]]
        .assert_eq(
            &with_verifier_frontend(ctx.config("build"))
                .stage(2)
                .paths(&["compiler/rustc", "library"])
                .hosts(&[&host_target(), TEST_TRIPLE_1])
                .targets(&[&host_target(), TEST_TRIPLE_1, TEST_TRIPLE_2])
                .render_steps(),
        );
    }

    #[test]
    fn build_targo() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> targo 1 <host>"#]]
        .assert_eq(&ctx.config("build").paths(&["targo"]).render_steps());
    }

    #[test]
    fn build_targo_cross() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] llvm <target1>
            [build] rustc 1 <host> -> rustc 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustc 1 <host> -> targo 2 <target1>"#]]
        .assert_eq(&ctx.config("build").paths(&["targo"]).hosts(&[TEST_TRIPLE_1]).render_steps());
    }

    #[test]
    fn dist_default_stage() {
        let ctx = TestCtx::new();
        assert_eq!(ctx.config("dist").path("compiler").create_config().stage, 2);
    }

    #[test]
    fn dist_baseline() {
        let ctx = TestCtx::new();
        // Note that stdlib is uplifted, that is why `[dist] rustc 1 <host> -> std <host>` is in
        // the output.
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> standalone 2 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> error-index 2 <host>
            [doc] rustc 1 <host> -> error-index 2 <host>
            [doc] rustdoc (book) <host>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] cargo (book) <host>
            [doc] tippy (book) <host>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] docs <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <host>
            [dist] mingw <host>
            [build] rustdoc 2 <host>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <host>
            [build] rustc 0 <host> -> GenerateCopyright 1 <host>
            [dist] trustc <host>
            [dist] rustc 1 <host> -> std 1 <host>
            [dist] rustc 1 <host> -> trustc-dev 2 <host>
            [dist] src <>
            [dist] reproducible-artifacts <host>"#]].assert_eq(&ctx
            .config("dist")
            .render_steps());
    }

    #[test]
    fn dist_compiler_docs() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [doc] rustc 1 <host> -> Rustdoc 2 <host>
            [doc] rustc 1 <host> -> Rustfmt 2 <host>
            [doc] rustc 1 <host> -> Clippy 2 <host>
            [doc] rustc 1 <host> -> Miri 2 <host>
            [doc] rustc 1 <host> -> Cargo 2 <host>
            [doc] rustc 1 <host> -> Tidy 2 <host>
            [doc] rustc 1 <host> -> Bootstrap 2 <host>
            [doc] rustc 1 <host> -> BuildHelper 2 <host>
            [doc] rustc 1 <host> -> Compiletest 2 <host>
            [doc] rustc 1 <host> -> RunMakeSupport 2 <host>
            [doc] rustc 1 <host> -> CompilerWithTools 2 <host>
            [build] rustc 0 <host> -> RustInstaller 1 <host>"#]]
        .assert_eq(
            &ctx.config("dist")
                .path("rustc-docs")
                .args(&["--set", "build.compiler-docs=true"])
                .render_steps(),
        );
    }

    #[test]
    fn dist_extended() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 0 <host> -> LldWrapper 1 <host>
            [build] rustc 0 <host> -> WasmComponentLd 1 <host>
            [build] rustc 0 <host> -> LlvmBitcodeLinker 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> standalone 2 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 1 <host> -> LldWrapper 2 <host>
            [build] rustc 1 <host> -> WasmComponentLd 2 <host>
            [build] rustc 1 <host> -> LlvmBitcodeLinker 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> error-index 2 <host>
            [doc] rustc 1 <host> -> error-index 2 <host>
            [doc] rustdoc (book) <host>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] cargo (book) <host>
            [doc] tippy (book) <host>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] docs <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <host>
            [dist] mingw <host>
            [build] rustdoc 2 <host>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <host>
            [build] rustc 0 <host> -> GenerateCopyright 1 <host>
            [dist] trustc <host>
            [dist] rustc 1 <host> -> std 1 <host>
            [dist] rustc 1 <host> -> trustc-dev 2 <host>
            [dist] rustc 1 <host> -> analysis 2 <host>
            [dist] src <>
            [build] rustc 1 <host> -> targo 2 <host>
            [dist] rustc 1 <host> -> targo 2 <host>
            [build] rustc 1 <host> -> trust-analyzer 2 <host>
            [dist] rustc 1 <host> -> trust-analyzer 2 <host>
            [build] rustc 1 <host> -> rustfmt 2 <host>
            [build] rustc 1 <host> -> cargo-fmt 2 <host>
            [dist] rustc 1 <host> -> trustfmt 2 <host>
            [build] rustc 1 <host> -> cargo-clippy 2 <host>
            [build] rustc 1 <host> -> clippy-driver 2 <host>
            [dist] rustc 1 <host> -> tippy 2 <host>
            [build] rustc 1 <host> -> miri 2 <host>
            [build] rustc 1 <host> -> cargo-miri 2 <host>
            [dist] rustc 1 <host> -> trust-miri 2 <host>
            [build] rustc 1 <host> -> trustd 2 <host>
            [build] rustc 1 <host> -> targo-trust 2 <host>
            [dist] rustc 1 <host> -> targo-trust 2 <host>
            [doc] rustc 2 <host> -> std 2 <host> crates=[]
            [dist] rustc 2 <host> -> json-docs 3 <host>
            [dist] rustc 1 <host> -> extended 2 <host>
            [dist] reproducible-artifacts <host>"#]].assert_eq(&ctx.config("dist")
        .args(&[
            "--set",
            "build.extended=true",
            "--set",
            "rust.llvm-bitcode-linker=true",
            "--set",
            "rust.lld=true",
        ])
        .render_steps());
    }

    #[test]
    fn dist_with_targets() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [doc] unstable-book (book) <target1>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> standalone 2 <host>
            [doc] rustc 1 <host> -> standalone 2 <target1>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [doc] rustc 1 <host> -> std 1 <target1> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> error-index 2 <host>
            [doc] rustc 1 <host> -> error-index 2 <host>
            [doc] rustdoc (book) <host>
            [doc] rustdoc (book) <target1>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] cargo (book) <host>
            [doc] cargo (book) <target1>
            [doc] tippy (book) <host>
            [doc] tippy (book) <target1>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] docs <host>
            [dist] docs <target1>
            [doc] rustc 1 <host> -> std 1 <host> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <host>
            [doc] rustc 1 <host> -> std 1 <target1> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <target1>
            [dist] mingw <host>
            [dist] mingw <target1>
            [build] rustdoc 2 <host>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <host>
            [build] rustc 0 <host> -> GenerateCopyright 1 <host>
            [dist] trustc <host>
            [dist] rustc 1 <host> -> std 1 <host>
            [dist] rustc 1 <host> -> std 1 <target1>
            [dist] rustc 1 <host> -> trustc-dev 2 <host>
            [dist] src <>
            [dist] reproducible-artifacts <host>"#]].assert_eq(&ctx
            .config("dist")
            .hosts(&[&host_target()])
            .targets(&[&host_target(), TEST_TRIPLE_1])
            .render_steps());
    }

    #[test]
    fn dist_with_hosts() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> standalone 2 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> error-index 2 <host>
            [doc] rustc 1 <host> -> error-index 2 <host>
            [build] llvm <target1>
            [build] rustc 1 <host> -> rustc 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustc 1 <host> -> error-index 2 <target1>
            [doc] rustc 1 <host> -> error-index 2 <target1>
            [doc] rustdoc (book) <host>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] rustc (book) <target1>
            [doc] cargo (book) <host>
            [doc] tippy (book) <host>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] docs <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <host>
            [dist] mingw <host>
            [build] rustdoc 2 <host>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <host>
            [build] rustc 0 <host> -> GenerateCopyright 1 <host>
            [dist] trustc <host>
            [build] rustdoc 2 <target1>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <target1>
            [dist] trustc <target1>
            [dist] rustc 1 <host> -> std 1 <host>
            [dist] rustc 1 <host> -> trustc-dev 2 <host>
            [dist] rustc 1 <host> -> trustc-dev 2 <target1>
            [dist] src <>
            [dist] reproducible-artifacts <host>
            [dist] reproducible-artifacts <target1>"#]].assert_eq(&ctx
            .config("dist")
            .hosts(&[&host_target(), TEST_TRIPLE_1])
            .targets(&[&host_target()])
            .render_steps());
    }

    #[test]
    fn dist_with_targets_and_hosts() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [doc] unstable-book (book) <target1>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> standalone 2 <host>
            [doc] rustc 1 <host> -> standalone 2 <target1>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [doc] rustc 1 <host> -> std 1 <target1> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> error-index 2 <host>
            [doc] rustc 1 <host> -> error-index 2 <host>
            [build] llvm <target1>
            [build] rustc 1 <host> -> rustc 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustc 1 <host> -> error-index 2 <target1>
            [doc] rustc 1 <host> -> error-index 2 <target1>
            [doc] rustdoc (book) <host>
            [doc] rustdoc (book) <target1>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] rustc (book) <target1>
            [doc] cargo (book) <host>
            [doc] cargo (book) <target1>
            [doc] tippy (book) <host>
            [doc] tippy (book) <target1>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] docs <host>
            [dist] docs <target1>
            [doc] rustc 1 <host> -> std 1 <host> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <host>
            [doc] rustc 1 <host> -> std 1 <target1> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <target1>
            [dist] mingw <host>
            [dist] mingw <target1>
            [build] rustdoc 2 <host>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <host>
            [build] rustc 0 <host> -> GenerateCopyright 1 <host>
            [dist] trustc <host>
            [build] rustdoc 2 <target1>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <target1>
            [dist] trustc <target1>
            [dist] rustc 1 <host> -> std 1 <host>
            [dist] rustc 1 <host> -> std 1 <target1>
            [dist] rustc 1 <host> -> trustc-dev 2 <host>
            [dist] rustc 1 <host> -> trustc-dev 2 <target1>
            [dist] src <>
            [dist] reproducible-artifacts <host>
            [dist] reproducible-artifacts <target1>"#]].assert_eq(&ctx
            .config("dist")
            .hosts(&[&host_target(), TEST_TRIPLE_1])
            .targets(&[&host_target(), TEST_TRIPLE_1])
            .render_steps());
    }

    #[test]
    fn dist_with_empty_host() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <target1>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> standalone 2 <target1>
            [doc] rustc 1 <host> -> std 1 <target1> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [doc] rustdoc (book) <target1>
            [doc] cargo (book) <target1>
            [doc] tippy (book) <target1>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] docs <target1>
            [doc] rustc 1 <host> -> std 1 <target1> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <target1>
            [dist] mingw <target1>
            [dist] rustc 1 <host> -> std 1 <target1>"#]].assert_eq(&ctx
            .config("dist")
            .hosts(&[])
            .targets(&[TEST_TRIPLE_1])
            .render_steps());
    }

    #[test]
    fn dist_all_cross_extended() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 0 <host> -> WasmComponentLd 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <target1>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> standalone 2 <target1>
            [doc] rustc 1 <host> -> std 1 <target1> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] llvm <target1>
            [build] rustc 1 <host> -> rustc 2 <target1>
            [build] rustc 1 <host> -> WasmComponentLd 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustc 1 <host> -> error-index 2 <target1>
            [doc] rustc 1 <host> -> error-index 2 <target1>
            [doc] rustdoc (book) <target1>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <target1>
            [doc] cargo (book) <target1>
            [doc] tippy (book) <target1>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] docs <target1>
            [doc] rustc 1 <host> -> std 1 <target1> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <target1>
            [dist] mingw <target1>
            [build] rustdoc 2 <target1>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <target1>
            [build] rustc 0 <host> -> GenerateCopyright 1 <host>
            [dist] trustc <target1>
            [dist] rustc 1 <host> -> std 1 <target1>
            [dist] rustc 1 <host> -> trustc-dev 2 <target1>
            [dist] rustc 1 <host> -> analysis 2 <target1>
            [dist] src <>
            [build] rustc 1 <host> -> targo 2 <target1>
            [dist] rustc 1 <host> -> targo 2 <target1>
            [build] rustc 1 <host> -> trust-analyzer 2 <target1>
            [dist] rustc 1 <host> -> trust-analyzer 2 <target1>
            [build] rustc 1 <host> -> rustfmt 2 <target1>
            [build] rustc 1 <host> -> cargo-fmt 2 <target1>
            [dist] rustc 1 <host> -> trustfmt 2 <target1>
            [build] rustc 1 <host> -> cargo-clippy 2 <target1>
            [build] rustc 1 <host> -> clippy-driver 2 <target1>
            [dist] rustc 1 <host> -> tippy 2 <target1>
            [build] rustc 1 <host> -> miri 2 <target1>
            [build] rustc 1 <host> -> cargo-miri 2 <target1>
            [dist] rustc 1 <host> -> trust-miri 2 <target1>
            [build] rustc 1 <host> -> LlvmBitcodeLinker 2 <target1>
            [build] rustc 1 <host> -> trustd 2 <target1>
            [build] rustc 1 <host> -> targo-trust 2 <target1>
            [dist] rustc 1 <host> -> targo-trust 2 <target1>
            [doc] rustc 2 <target1> -> std 2 <target1> crates=[]
            [dist] rustc 2 <target1> -> json-docs 3 <target1>
            [dist] rustc 1 <host> -> extended 2 <target1>
            [dist] reproducible-artifacts <target1>"#]].assert_eq(&ctx
            .config("dist")
            .hosts(&[TEST_TRIPLE_1])
            .targets(&[TEST_TRIPLE_1])
            .args(&["--set", "rust.channel=nightly", "--set", "build.extended=true"])
            .render_steps());
    }

    /// Simulates e.g. the powerpc64 builder, which is fully cross-compiled from x64, but it does
    /// not build docs. Crucially, it shouldn't build host stage 2 rustc.
    ///
    /// This is a regression test for <https://github.com/rust-lang/rust/issues/138123>
    /// and <https://github.com/rust-lang/rust/issues/138004>.
    #[test]
    fn dist_all_cross_extended_no_docs() {
        let ctx = TestCtx::new();
        let steps = ctx
            .config("dist")
            .hosts(&[TEST_TRIPLE_1])
            .targets(&[TEST_TRIPLE_1])
            .args(&[
                "--set",
                "rust.channel=nightly",
                "--set",
                "build.extended=true",
                "--set",
                "build.docs=false",
            ])
            .get_steps();

        // Make sure that we don't build stage2 host rustc
        steps.assert_no_match(|m| {
            m.name == "rustc"
                && m.built_by.map(|b| b.stage) == Some(1)
                && *m.target.triple == host_target()
        });

        // Independent prerequisites can be scheduled in either order. Preserve
        // the cross-target artifacts and the no-host-stage2 regression directly.
        let target = TargetSelection::from_user(TEST_TRIPLE_1);
        let host = TargetSelection::from_user(&host_target());
        steps.assert_contains(StepMetadata::build("llvm", target));
        steps
            .assert_contains(StepMetadata::build("rustc", target).built_by(Compiler::new(1, host)));
        steps
            .assert_contains(StepMetadata::build("std", target).built_by(Compiler::new(2, target)));
        steps.assert_contains(
            StepMetadata::dist("extended", target).built_by(Compiler::new(1, host)),
        );
        steps.assert_no_match(|metadata| metadata.kind == Kind::Doc);
    }

    #[test]
    fn dist_trust_cg_by_default() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> standalone 2 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> error-index 2 <host>
            [doc] rustc 1 <host> -> error-index 2 <host>
            [doc] rustdoc (book) <host>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] cargo (book) <host>
            [doc] tippy (book) <host>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] docs <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[]
            [dist] rustc 1 <host> -> json-docs 2 <host>
            [dist] mingw <host>
            [build] rustdoc 2 <host>
            [build] rustc 1 <host> -> trust-analyzer-proc-macro-srv 2 <host>
            [build] rustc 0 <host> -> GenerateCopyright 1 <host>
            [dist] trustc <host>
            [dist] rustc 1 <host> -> std 1 <host>
            [dist] rustc 1 <host> -> trustc-dev 2 <host>
            [dist] src <>
            [dist] reproducible-artifacts <host>"#]]
        .assert_eq(&ctx
                .config("dist")
                .args(&["--set", "rust.codegen-backends=['llvm', 'trust-cg']"])
                .render_steps());
    }

    #[test]
    fn dist_bootstrap() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] bootstrap <host>"#]]
        .assert_eq(&ctx.config("dist").path("bootstrap").render_steps());
    }

    #[test]
    fn dist_library_stage_0_local_rebuild() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustc 0 <host> -> std 0 <target1>
            [build] rustc 0 <host> -> RustInstaller 1 <host>
            [dist] rustc 0 <host> -> std 0 <target1>"#]]
        .assert_eq(
            &ctx.config("dist")
                .path("trust-std")
                .stage(0)
                .targets(&[TEST_TRIPLE_1])
                .args(&["--set", "build.local-rebuild=true"])
                .render_steps(),
        );
    }

    #[test]
    fn dist_rustc_docs() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [doc] rustc 1 <host> -> Rustdoc 2 <host>
            [doc] rustc 1 <host> -> Rustfmt 2 <host>
            [doc] rustc 1 <host> -> Clippy 2 <host>
            [doc] rustc 1 <host> -> Miri 2 <host>
            [doc] rustc 1 <host> -> Cargo 2 <host>
            [doc] rustc 1 <host> -> Tidy 2 <host>
            [doc] rustc 1 <host> -> Bootstrap 2 <host>
            [doc] rustc 1 <host> -> BuildHelper 2 <host>
            [doc] rustc 1 <host> -> Compiletest 2 <host>
            [doc] rustc 1 <host> -> RunMakeSupport 2 <host>
            [doc] rustc 1 <host> -> CompilerWithTools 2 <host>
            [build] rustc 0 <host> -> RustInstaller 1 <host>"#]]
        .assert_eq(&ctx.config("dist").path("rustc-docs").render_steps());
    }

    #[test]
    fn check_compiler_no_explicit_stage() {
        let ctx = TestCtx::new();
        assert_compiler_plan(
            &ctx,
            expect_test::expect!["[check] rustc 0 <host> -> rustc 1 <host> (compiler crates)"],
            &ctx.config("check").path("compiler").render_steps(),
        );
    }

    #[test]
    fn check_rustc_no_explicit_stage() {
        let ctx = TestCtx::new();
        expect_test::expect![["[check] rustc 0 <host> -> rustc 1 <host> (1 crates)"]]
            .assert_eq(&ctx.config("check").path("rustc").render_steps());
    }

    #[test]
    #[should_panic]
    fn check_compiler_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("check").path("compiler").stage(0).run();
    }

    #[test]
    fn check_compiler_stage_1() {
        let ctx = TestCtx::new();
        assert_compiler_plan(
            &ctx,
            expect_test::expect!["[check] rustc 0 <host> -> rustc 1 <host> (compiler crates)"],
            &ctx.config("check").path("compiler").stage(1).render_steps(),
        );
    }

    #[test]
    fn check_compiler_stage_2() {
        let ctx = TestCtx::new();
        assert_compiler_plan(
            &ctx,
            expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> rustc 2 <host> (compiler crates)"#]],
            &ctx.config("check").path("compiler").stage(2).render_steps(),
        );
    }

    #[test]
    fn check_cross_compile() {
        let ctx = TestCtx::new();
        assert_compiler_plan(
            &ctx,
            expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> std 1 <target1>
            [check] rustc 1 <host> -> rustc 2 <target1> (compiler crates)
            [check] rustc 1 <host> -> rustc 2 <target1>
            [check] rustc 1 <host> -> Rustdoc 2 <target1>
            [check] rustc 1 <host> -> Clippy 2 <target1>
            [check] rustc 1 <host> -> Miri 2 <target1>
            [check] rustc 1 <host> -> CargoMiri 2 <target1>
            [check] rustc 1 <host> -> Rustfmt 2 <target1>
            [check] rustc 1 <host> -> RustAnalyzer 2 <target1>
            [check] rustc 1 <host> -> TestFloatParse 2 <target1>
            [check] rustc 1 <host> -> std 1 <target1>"#]],
            &ctx.config("check").targets(&[TEST_TRIPLE_1]).hosts(&[TEST_TRIPLE_1]).render_steps(),
        );
    }

    #[test]
    fn check_library_no_explicit_stage() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("check").path("library").render_steps());
    }

    #[test]
    #[should_panic]
    fn check_library_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("check").path("library").stage(0).run();
    }

    #[test]
    fn check_library_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("check").path("library").stage(1).render_steps());
    }

    #[test]
    fn check_library_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [check] rustc 2 <host> -> std 2 <host>"#]]
        .assert_eq(&ctx.config("check").path("library").stage(2).render_steps());
    }

    #[test]
    fn check_library_cross_compile() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> std 1 <target1>
            [check] rustc 1 <host> -> std 1 <target2>"#]]
        .assert_eq(
            &ctx.config("check")
                .paths(&["core", "alloc", "std"])
                .targets(&[TEST_TRIPLE_1, TEST_TRIPLE_2])
                .render_steps(),
        );
    }

    /// Make sure that we don't check library when download-rustc is disabled
    /// when `--skip-std-check-if-no-download-rustc` was passed.
    #[test]
    fn check_library_skip_without_download_rustc() {
        let ctx = TestCtx::new();
        let args = ["--set", "rust.download-rustc=false", "--skip-std-check-if-no-download-rustc"];
        expect_test::expect![[""]]
            .assert_eq(&ctx.config("check").paths(&["library"]).args(&args).render_steps());

        assert_compiler_plan(
            &ctx,
            expect_test::expect!["[check] rustc 0 <host> -> rustc 1 <host> (compiler crates)"],
            &ctx.config("check").paths(&["library", "compiler"]).args(&args).render_steps(),
        );
    }

    #[test]
    fn check_miri_no_explicit_stage() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> rustc 2 <host>
            [check] rustc 1 <host> -> Miri 2 <host>"#]]
        .assert_eq(&ctx.config("check").path("miri").render_steps());
    }

    #[test]
    #[should_panic]
    fn check_miri_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("check").path("miri").stage(0).run();
    }

    #[test]
    fn check_miri_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> rustc 2 <host>
            [check] rustc 1 <host> -> Miri 2 <host>"#]]
        .assert_eq(&ctx.config("check").path("miri").stage(1).render_steps());
    }

    #[test]
    fn check_miri_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> rustc 2 <host>
            [check] rustc 1 <host> -> Miri 2 <host>"#]]
        .assert_eq(&ctx.config("check").path("miri").stage(2).render_steps());
    }

    // Trust: the explicit Priroda path selects its unified Miri package and stage floor.
    #[test]
    fn check_priroda_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> rustc 2 <host>
            [check] rustc 1 <host> -> Miri 2 <host>"#]]
        .assert_eq(&ctx.config("check").path("src/tools/miri/priroda").stage(1).render_steps());
    }

    #[test]
    fn check_compiletest() {
        let ctx = TestCtx::new();
        expect_test::expect![["[check] rustc 0 <host> -> Compiletest 1 <host>"]]
            .assert_eq(&ctx.config("check").path("compiletest").render_steps());
    }

    #[test]
    fn check_rust_analyzer() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [check] rustc 0 <host> -> rustc 1 <host>
            [check] rustc 0 <host> -> RustAnalyzer 1 <host>"#]]
        .assert_eq(&ctx.config("check").path("rust-analyzer").render_steps());
    }

    #[test]
    fn check_bootstrap_tool() {
        let ctx = TestCtx::new();
        expect_test::expect![["[check] rustc 0 <host> -> RunMakeSupport 1 <host>"]]
            .assert_eq(&ctx.config("check").path("run-make-support").render_steps());
    }

    fn prepare_test_config(ctx: &TestCtx) -> ConfigBuilder {
        ctx.config("test")
            // Bootstrap only runs by default on CI, so we have to emulate that also locally.
            .args(&["--ci", "true"])
            // These rustdoc tests requires nodejs to be present.
            // We can't easily opt out of it, so if it is present on the local PC, the test
            // would have different result on CI, where nodejs might be missing.
            .args(&["--skip", "rustdoc-js-std"])
            .args(&["--skip", "rustdoc-js"])
            .args(&["--skip", "rustdoc-gui"])
    }

    #[test]
    fn test_targo_trust_builds_and_runs_the_shipped_tool_recipe() {
        let ctx = TestCtx::new();
        let steps = ctx.config("test").path("targo-trust").stage(2).render_steps();

        assert!(
            steps.contains("[build] rustc 1 <host> -> targo-trust 2 <host>"),
            "the selector must build the shipped stage-2 tool before testing it:\n{steps}"
        );
        assert!(
            steps.contains("[build] rustc 1 <host> -> trustd 2 <host>"),
            "the selector must build the required same-sysroot daemon:\n{steps}"
        );
        assert!(
            steps.contains("[test] rustc 1 <host> -> targo-trust 2 <host>"),
            "the selector must execute the targo-trust cargo test step:\n{steps}"
        );
    }

    #[test]
    fn test_all_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustc 0 <host> -> Tidy 1 <host>
            [test] tidy <>
            [build] rustdoc 0 <host>
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> Compiletest 1 <host>
            [test] compiletest-ui 1 <host>
            [test] compiletest-crashes 1 <host>
            [build] rustc 0 <host> -> CoverageDump 1 <host>
            [test] compiletest-coverage 1 <host>
            [test] compiletest-coverage 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [test] compiletest-mir-opt 1 <host>
            [test] compiletest-codegen-llvm 1 <host>
            [test] compiletest-codegen-units 1 <host>
            [test] compiletest-assembly-gcc 1 <host>
            [test] compiletest-assembly-llvm 1 <host>
            [test] compiletest-incremental 1 <host>
            [test] compiletest-debuginfo 1 <host>
            [test] compiletest-ui-fulldeps 1 <host>
            [build] rustdoc 1 <host>
            [test] compiletest-rustdoc-html 1 <host>
            [test] compiletest-coverage-run-rustdoc 1 <host>
            [test] compiletest-pretty 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> std 0 <host>
            [test] rustc 0 <host> -> CrateLibrustc 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [test] crate-bootstrap <host> src/tools/coverage-dump
            [test] crate-bootstrap <host> src/tools/jsondoclint
            [test] crate-bootstrap <host> src/tools/replace-version-placeholder
            [test] crate-bootstrap <host> tidyselftest
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [doc] rustc 0 <host> -> standalone 1 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 0 <host> -> error-index 1 <host>
            [doc] rustc 0 <host> -> error-index 1 <host>
            [doc] rustdoc (book) <host>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] cargo (book) <host>
            [doc] tippy (book) <host>
            [build] rustc 0 <host> -> Linkchecker 1 <host>
            [test] link-check <host>
            [test] tier-check <host>
            [test] rustc 0 <host> -> rust-analyzer 1 <host>
            [build] rustc 0 <host> -> RustdocTheme 1 <host>
            [test] rustdoc-theme 1 <host>
            [test] compiletest-rustdoc-ui 1 <host>
            [build] rustc 0 <host> -> JsonDocCk 1 <host>
            [build] rustc 0 <host> -> JsonDocLint 1 <host>
            [test] compiletest-rustdoc-json 1 <host>
            [doc] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 0 <host> -> HtmlChecker 1 <host>
            [test] html-check <host>
            [test] test-float-parse <host>
            [build] rustc 0 <host> -> RunMakeSupport 1 <host>
            [test] compiletest-run-make 1 <host>
            [build] rustc 0 <host> -> targo 1 <host>
            [test] compiletest-run-make-cargo 1 <host>
            [test] intrinsic-test <host>"#]].assert_eq(&prepare_test_config(&ctx)
            .render_steps());
    }

    #[test]
    fn test_compiletest_self_test() {
        let ctx = TestCtx::new();
        let steps = ctx.config("test").arg("compiletest").render_steps();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 0 <host>"#]]
        .assert_eq(&steps);
    }

    #[test]
    fn test_compiletest_suites_stage1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> Compiletest 1 <host>
            [test] compiletest-ui 1 <host>
            [test] compiletest-ui-fulldeps 1 <host>
            [build] rustc 0 <host> -> RunMakeSupport 1 <host>
            [build] rustdoc 1 <host>
            [test] compiletest-run-make 1 <host>
            [test] compiletest-rustdoc-html 1 <host>
            [build] rustc 0 <host> -> RustdocGUITest 1 <host>
            [test] rustdoc-gui 1 <host>
            [test] compiletest-incremental 1 <host>"#]]
        .assert_eq(
            &ctx.config("test")
                .args(&[
                    "ui",
                    "ui-fulldeps",
                    "run-make",
                    "rustdoc-html",
                    "rustdoc-gui",
                    "incremental",
                ])
                .render_steps(),
        );
    }

    #[test]
    fn test_compiletest_suites_stage2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 0 <host> -> Compiletest 1 <host>
            [test] compiletest-ui 2 <host>
            [test] compiletest-ui-fulldeps 2 <host>
            [build] rustc 0 <host> -> RunMakeSupport 1 <host>
            [build] rustdoc 2 <host>
            [test] compiletest-run-make 2 <host>
            [test] compiletest-rustdoc-html 2 <host>
            [build] rustc 0 <host> -> RustdocGUITest 1 <host>
            [test] rustdoc-gui 2 <host>
            [test] compiletest-incremental 2 <host>"#]]
        .assert_eq(
            &ctx.config("test")
                .args(&[
                    "ui",
                    "ui-fulldeps",
                    "run-make",
                    "rustdoc-html",
                    "rustdoc-gui",
                    "incremental",
                ])
                .stage(2)
                .render_steps(),
        );
    }

    #[test]
    fn test_compiletest_suites_stage2_cross() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 0 <host> -> Compiletest 1 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] rustc 2 <host> -> std 2 <target1>
            [test] compiletest-ui 2 <target1>
            [build] llvm <target1>
            [build] rustc 1 <host> -> rustc 2 <target1>
            [test] compiletest-ui-fulldeps 2 <target1>
            [build] rustc 0 <host> -> RunMakeSupport 1 <host>
            [build] rustdoc 2 <host>
            [test] compiletest-run-make 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustc 2 <target1> -> std 2 <target1>
            [build] rustdoc 2 <target1>
            [build] rustc 0 <host> -> RustdocGUITest 1 <host>
            [test] rustdoc-gui 2 <target1>
            [test] compiletest-incremental 2 <target1>"#]]
        .assert_eq(
            &ctx.config("test")
                .hosts(&[TEST_TRIPLE_1])
                .targets(&[TEST_TRIPLE_1])
                .args(&["ui", "ui-fulldeps", "run-make", "rustdoc", "rustdoc-gui", "incremental"])
                .stage(2)
                .render_steps(),
        );
    }

    #[test]
    fn test_all_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustc 0 <host> -> Tidy 1 <host>
            [test] tidy <>
            [build] rustdoc 0 <host>
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 0 <host> -> Compiletest 1 <host>
            [test] compiletest-ui 2 <host>
            [test] compiletest-crashes 2 <host>
            [build] rustc 0 <host> -> CoverageDump 1 <host>
            [test] compiletest-coverage 2 <host>
            [test] compiletest-coverage 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [test] compiletest-mir-opt 2 <host>
            [test] compiletest-codegen-llvm 2 <host>
            [test] compiletest-codegen-units 2 <host>
            [test] compiletest-assembly-gcc 2 <host>
            [test] compiletest-assembly-llvm 2 <host>
            [test] compiletest-incremental 2 <host>
            [test] compiletest-debuginfo 2 <host>
            [test] compiletest-ui-fulldeps 2 <host>
            [build] rustdoc 2 <host>
            [test] compiletest-rustdoc-html 2 <host>
            [test] compiletest-coverage-run-rustdoc 2 <host>
            [test] compiletest-pretty 2 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [test] rustc 1 <host> -> CrateLibrustc 2 <host>
            [test] crate-bootstrap <host> src/tools/coverage-dump
            [test] crate-bootstrap <host> src/tools/jsondoclint
            [test] crate-bootstrap <host> src/tools/replace-version-placeholder
            [test] crate-bootstrap <host> tidyselftest
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [doc] rustc 1 <host> -> standalone 2 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <host> -> error-index 2 <host>
            [doc] rustc 1 <host> -> error-index 2 <host>
            [doc] rustdoc (book) <host>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] cargo (book) <host>
            [doc] tippy (book) <host>
            [build] rustc 0 <host> -> Linkchecker 1 <host>
            [test] link-check <host>
            [test] tier-check <host>
            [test] rustc 1 <host> -> rust-analyzer 2 <host>
            [doc] rustc (book) <host>
            [test] rustc 1 <host> -> lint-docs 2 <host>
            [build] rustc 0 <host> -> RustdocTheme 1 <host>
            [test] rustdoc-theme 2 <host>
            [test] compiletest-rustdoc-ui 2 <host>
            [build] rustc 0 <host> -> JsonDocCk 1 <host>
            [build] rustc 0 <host> -> JsonDocLint 1 <host>
            [test] compiletest-rustdoc-json 2 <host>
            [doc] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 0 <host> -> HtmlChecker 1 <host>
            [test] html-check <host>
            [test] test-float-parse <host>
            [build] rustc 0 <host> -> RunMakeSupport 1 <host>
            [test] compiletest-run-make 2 <host>
            [build] rustc 1 <host> -> targo 2 <host>
            [test] compiletest-run-make-cargo 2 <host>
            [test] intrinsic-test <host>"#]].assert_eq(&prepare_test_config(&ctx)
            .stage(2)
            .render_steps());
    }

    #[test]
    fn test_compiler_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustc 0 <host> -> std 0 <host>
            [build] rustdoc 0 <host>
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [test] rustc 0 <host> -> CrateLibrustc 1 <host>"#]]
        .assert_eq(&ctx.config("test").path("compiler").stage(1).render_steps());
    }

    // Trust: check the real step graph as well as the pass-selection helper.
    #[test]
    fn test_compiler_stage_1_doctests_have_current_tools_without_stage_2_compiler() {
        let ctx = TestCtx::new();
        for extra_args in [&[][..], &["--doc"][..]] {
            let steps =
                ctx.config("test").path("compiler").stage(1).args(extra_args).render_steps();
            assert!(steps.contains("[build] rustc 0 <host> -> rustc 1 <host>"), "{steps}");
            assert!(steps.contains("[build] rustdoc 1 <host>"), "{steps}");
            assert!(!steps.contains("[build] rustc 1 <host> -> rustc 2 <host>"), "{steps}");
        }
        let steps =
            ctx.config("test").path("compiler").stage(1).args(&["--all-targets"]).render_steps();
        assert!(!steps.contains("[build] rustdoc 1 <host>"), "{steps}");
    }

    // Trust: these commands have no later doctest pass that could hide a
    // missing current-driver sysroot prerequisite for in-process fixtures.
    #[test]
    fn test_compiler_stage_1_units_have_current_runtime_without_stage_2_compiler() {
        let ctx = TestCtx::new();
        for flag in ["--all-targets", "--tests"] {
            let steps = ctx.config("test").path("compiler").stage(1).args(&[flag]).render_steps();
            assert!(steps.contains("[test] rustc 0 <host> -> CrateLibrustc 1 <host>"), "{steps}");
            assert!(steps.contains("[build] rustc 0 <host> -> rustc 1 <host>"), "{steps}");
            assert!(steps.contains("[build] rustc 1 <host> -> std 1 <host>"), "{steps}");
            assert!(!steps.contains("[build] rustc 1 <host> -> rustc 2 <host>"), "{steps}");
            assert!(!steps.contains("[build] rustdoc 1 <host>"), "{steps}");
        }
    }

    #[test]
    fn test_compiler_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [test] rustc 1 <host> -> CrateLibrustc 2 <host>"#]]
        .assert_eq(&ctx.config("test").path("compiler").stage(2).render_steps());
    }

    #[test]
    fn test_exclude() {
        let ctx = TestCtx::new();
        let steps = ctx.config("test").args(&["--skip", "src/tools/tidy"]).get_steps();

        let host = TargetSelection::from_user(&host_target());
        steps.assert_contains(StepMetadata::test("compiletest-rustdoc-ui", host).stage(1));
        steps.assert_not_contains(test::Tidy);
    }

    #[test]
    fn test_exclude_kind() {
        let ctx = TestCtx::new();
        let host = TargetSelection::from_user(&host_target());

        let get_steps = |args: &[&str]| ctx.config("test").args(args).get_steps();

        let rustc_metadata =
            || StepMetadata::test("CrateLibrustc", host).built_by(Compiler::new(0, host));
        // Ensure our test is valid, and `test::Rustc` would be run without the exclude.
        get_steps(&[]).assert_contains(rustc_metadata());

        let steps = get_steps(&["--skip", "compiler/rustc_data_structures"]);

        // Ensure tests for rustc are not skipped.
        steps.assert_contains(rustc_metadata());
        steps.assert_contains_fuzzy(StepMetadata::build("rustc", host));
    }

    #[test]
    fn test_exclude_trustdoc_selectors() {
        let ctx = TestCtx::new();
        let host = TargetSelection::from_user(&host_target());

        let get_steps = |args: &[&str]| ctx.config("build").args(args).get_steps();

        for args in [
            ["--skip", "trustdoc"].as_slice(),
            ["--skip", "src/tools/trustdoc"].as_slice(),
            ["--skip", "src/librustdoc"].as_slice(),
        ] {
            let steps = get_steps(args);

            steps.assert_contains_fuzzy(StepMetadata::build("rustc", host));
            steps.assert_no_match(|metadata| {
                metadata.name == "rustdoc"
                    && metadata.kind == Kind::Build
                    && metadata.target == host
            });
        }
    }

    #[test]
    fn test_library_tests_only_does_not_build_rustdoc() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("test").args(&["--tests", "library/core"]).render_steps());
    }

    #[test]
    fn test_targo_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> targo 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [build] rustdoc 0 <host>
            [test] rustc 0 <host> -> targo 1 <host>"#]]
        .assert_eq(&ctx.config("test").path("targo").render_steps());
    }

    #[test]
    fn test_targo_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> targo 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustdoc 2 <host>
            [build] rustdoc 1 <host>
            [test] rustc 1 <host> -> targo 2 <host>"#]]
        .assert_eq(&ctx.config("test").path("targo").stage(2).render_steps());
    }

    #[test]
    fn test_cargotest() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> targo 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> CargoTest 1 <host>
            [build] rustdoc 1 <host>
            [test] cargotest 1 <host>"#]]
        .assert_eq(&ctx.config("test").path("cargotest").render_steps());
    }

    #[test]
    fn test_tier_check() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [test] tier-check <host>"#]]
        .assert_eq(&ctx.config("test").path("tier-check").render_steps());
    }

    // Differential snapshots for `./x test run-make` run `./x test run-make-cargo`: only
    // `run-make-cargo` should build an in-tree cargo, running `./x test run-make` should not.
    #[test]
    fn test_run_make_no_cargo() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> Compiletest 1 <host>
            [build] rustc 0 <host> -> RunMakeSupport 1 <host>
            [build] rustdoc 1 <host>
            [test] compiletest-run-make 1 <host>"#]]
        .assert_eq(&ctx.config("test").path("run-make").render_steps());
    }

    #[test]
    fn test_run_make_cargo_builds_cargo() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> Compiletest 1 <host>
            [build] rustc 0 <host> -> RunMakeSupport 1 <host>
            [build] rustc 0 <host> -> targo 1 <host>
            [build] rustdoc 1 <host>
            [test] compiletest-run-make-cargo 1 <host>"#]]
        .assert_eq(&ctx.config("test").path("run-make-cargo").render_steps());
    }

    #[test]
    fn doc_all() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> UnstableBookGen 1 <host>
            [build] rustc 0 <host> -> Rustbook 1 <host>
            [doc] unstable-book (book) <host>
            [build] rustdoc 0 <host>
            [doc] rustc 0 <host> -> standalone 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 0 <host> -> error-index 1 <host>
            [doc] rustc 0 <host> -> error-index 1 <host>
            [doc] rustdoc (book) <host>
            [build] rustc 0 <host> -> LintDocs 1 <host>
            [doc] rustc (book) <host>
            [doc] cargo (book) <host>
            [doc] tippy (book) <host>"#]].assert_eq(&ctx.config("doc")
            .render_steps());
    }

    #[test]
    fn doc_library() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]"#]].assert_eq(&ctx.config("doc")
            .path("library")
            .render_steps());
    }

    #[test]
    fn doc_compiler_with_tools() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustdoc 0 <host>
            [doc] rustc 0 <host> -> rustc 1 <host>
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [doc] rustc 0 <host> -> Rustdoc 1 <host>
            [doc] rustc 0 <host> -> Rustfmt 1 <host>
            [doc] rustc 0 <host> -> Clippy 1 <host>
            [doc] rustc 0 <host> -> Miri 1 <host>
            [doc] rustc 0 <host> -> Cargo 1 <host>
            [doc] rustc 0 <host> -> Tidy 1 <host>
            [doc] rustc 0 <host> -> Bootstrap 1 <host>
            [doc] rustc 0 <host> -> BuildHelper 1 <host>
            [doc] rustc 0 <host> -> Compiletest 1 <host>
            [doc] rustc 0 <host> -> RunMakeSupport 1 <host>
            [doc] rustc 0 <host> -> CompilerWithTools 1 <host>"#]]
        .assert_eq(&ctx.config("doc").arg("compiler-with-tools").render_steps());
    }

    #[test]
    fn doc_targo_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustdoc 0 <host>
            [doc] rustc 0 <host> -> Cargo 1 <host>"#]]
        .assert_eq(&ctx.config("doc").path("targo").render_steps());
    }
    #[test]
    fn doc_targo_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> Cargo 2 <host>"#]]
        .assert_eq(&ctx.config("doc").path("targo").stage(2).render_steps());
    }

    #[test]
    fn doc_core() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[core]"#]]
        .assert_eq(&ctx.config("doc").path("core").render_steps());
    }

    #[test]
    fn doc_core_no_std_target() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[core]"#]]
        .assert_eq(
            &ctx.config("doc").path("core").override_target_no_std(&host_target()).render_steps(),
        );
    }

    #[test]
    fn doc_library_no_std_target() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> std 1 <host> crates=[alloc,core]"#]]
        .assert_eq(
            &ctx.config("doc")
                .path("library")
                .override_target_no_std(&host_target())
                .render_steps(),
        );
    }

    #[test]
    fn doc_library_no_std_target_cross_compile() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> std 1 <target1> crates=[alloc,core]"#]]
        .assert_eq(
            &ctx.config("doc")
                .path("library")
                .targets(&[TEST_TRIPLE_1])
                .override_target_no_std(TEST_TRIPLE_1)
                .render_steps(),
        );
    }

    #[test]
    #[should_panic]
    fn doc_compiler_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("doc").path("compiler").stage(0).run();
    }

    #[test]
    fn doc_compiler_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustdoc 0 <host>
            [doc] rustc 0 <host> -> rustc 1 <host>"#]]
        .assert_eq(&ctx.config("doc").path("compiler").stage(1).render_steps());
    }

    #[test]
    fn doc_compiler_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> rustc 2 <host>"#]]
        .assert_eq(&ctx.config("doc").path("compiler").stage(2).render_steps());
    }

    #[test]
    #[should_panic]
    fn doc_compiletest_stage_0() {
        let ctx = TestCtx::new();
        ctx.config("doc").path("src/tools/compiletest").stage(0).run();
    }

    #[test]
    fn doc_compiletest_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustdoc 0 <host>
            [doc] rustc 0 <host> -> Compiletest 1 <host>"#]]
        .assert_eq(&ctx.config("doc").path("src/tools/compiletest").stage(1).render_steps());
    }

    #[test]
    fn doc_compiletest_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [doc] rustc 1 <host> -> Compiletest 2 <host>"#]]
        .assert_eq(&ctx.config("doc").path("src/tools/compiletest").stage(2).render_steps());
    }

    #[test]
    fn clippy_ci() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> clippy-driver 1 <host>
            [build] rustc 0 <host> -> cargo-clippy 1 <host>
            [clippy] rustc 1 <host> -> bootstrap 2 <host>
            [clippy] rustc 1 <host> -> std 1 <host>
            [clippy] rustc 1 <host> -> rustc 2 <host>"#]]
        .assert_eq(&ctx.config("clippy").path("ci").stage(2).render_steps());
    }

    #[test]
    fn clippy_compiler_stage1() {
        let ctx = TestCtx::new();
        expect_test::expect![["[clippy] rustc 0 <host> -> rustc 1 <host>"]]
            .assert_eq(&ctx.config("clippy").path("compiler").render_steps());
    }

    #[test]
    fn clippy_compiler_stage2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> clippy-driver 1 <host>
            [build] rustc 0 <host> -> cargo-clippy 1 <host>
            [clippy] rustc 1 <host> -> rustc 2 <host>"#]]
        .assert_eq(&ctx.config("clippy").path("compiler").stage(2).render_steps());
    }

    #[test]
    fn clippy_std_stage1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> clippy-driver 1 <host>
            [build] rustc 0 <host> -> cargo-clippy 1 <host>
            [clippy] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("clippy").path("std").render_steps());
    }

    #[test]
    fn clippy_std_stage2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> clippy-driver 2 <host>
            [build] rustc 1 <host> -> cargo-clippy 2 <host>
            [clippy] rustc 2 <host> -> std 2 <host>"#]]
        .assert_eq(&ctx.config("clippy").path("std").stage(2).render_steps());
    }

    #[test]
    fn clippy_miri_stage1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [check] rustc 0 <host> -> rustc 1 <host>
            [clippy] rustc 0 <host> -> miri 1 <host>"#]]
        .assert_eq(&ctx.config("clippy").path("miri").stage(1).render_steps());
    }

    #[test]
    fn clippy_miri_stage2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [check] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 0 <host> -> clippy-driver 1 <host>
            [build] rustc 0 <host> -> cargo-clippy 1 <host>
            [clippy] rustc 1 <host> -> miri 2 <host>"#]]
        .assert_eq(&ctx.config("clippy").path("miri").stage(2).render_steps());
    }

    #[test]
    fn clippy_bootstrap() {
        let ctx = TestCtx::new();
        expect_test::expect![["[clippy] rustc 0 <host> -> bootstrap 1 <host>"]]
            .assert_eq(&ctx.config("clippy").path("bootstrap").render_steps());
    }

    fn targeted_install_config(ctx: &TestCtx, path: &str) -> ConfigBuilder {
        install_into_test_dir(ctx).path(path).stage(2)
    }

    /// `x install` with every install directory inside the test's own directory.
    fn install_into_test_dir(ctx: &TestCtx) -> ConfigBuilder {
        ctx.config("install").args(&[
            "--set",
            &format!("install.prefix={}", ctx.normalized_dir()),
            "--set",
            &format!("install.bindir={}", ctx.normalized_dir()),
            "--set",
            &format!("install.libdir={}", ctx.normalized_dir()),
            "--set",
            &format!("install.datadir={}", ctx.normalized_dir()),
            "--set",
            &format!("install.mandir={}", ctx.normalized_dir()),
            "--set",
            &format!("install.sysconfdir={}", ctx.normalized_dir()),
        ])
    }

    #[test]
    fn install_tippy_closes_over_required_runtime() {
        let ctx = TestCtx::new();
        let cache = targeted_install_config(&ctx, "tippy").run();

        assert!(cache.contains::<install::Clippy>());
        assert!(cache.contains::<install::Rustc>(), "tippy installation must ensure trustc");
        assert!(cache.contains::<install::Std>(), "tippy installation must ensure trust-std");
        assert!(cache.contains::<install::Cargo>(), "tippy installation must ensure targo");
    }

    #[test]
    fn install_targo_trust_closes_over_required_runtime() {
        let ctx = TestCtx::new();
        let cache = targeted_install_config(&ctx, "targo-trust").run();

        assert!(cache.contains::<install::TCargoTrust>());
        assert!(cache.contains::<install::Rustc>(), "targo-trust installation must ensure trustc");
        assert!(cache.contains::<install::Std>(), "targo-trust installation must ensure trust-std");
        assert!(cache.contains::<install::Cargo>(), "targo-trust installation must ensure targo");
    }

    // Trust: source component names schedule sources without documentation.
    #[test]
    fn install_src_accepts_owned_and_compatibility_component_names() {
        for selector in ["trust-src", "rust-src"] {
            let ctx = TestCtx::new();
            let cache = targeted_install_config(&ctx, selector).run();
            assert!(cache.contains::<install::Src>(), "source install missing for {selector}");
            assert!(cache.contains::<dist::Src>(), "source package missing for {selector}");
            assert!(!cache.contains::<install::Docs>(), "unexpected docs install for {selector}");
            assert!(!cache.contains::<dist::Docs>(), "unexpected docs package for {selector}");
        }
    }

    // Trust: `src` is an existing directory selector for `src/doc`; a profile's
    // tools allowlist spelling must not expand that command-line selection.
    #[test]
    fn install_src_directory_keeps_existing_docs_selection() {
        let ctx = TestCtx::new();
        let cache = targeted_install_config(&ctx, "src").run();
        assert!(cache.contains::<install::Docs>());
        assert!(cache.contains::<dist::Docs>());
        assert!(!cache.contains::<install::Src>());
        assert!(!cache.contains::<dist::Src>());
    }

    // Trust: the profile's `src` allowlist must select source by default, while
    // an unrelated allowlist and a non-extended build must still exclude it.
    #[test]
    fn install_src_default_selection_respects_aliases_and_extended_gate() {
        for (extended, selector, expected) in [
            (false, None, false),
            (false, Some("trust-src"), false),
            (false, Some("rust-src"), false),
            (false, Some("src"), false),
            (true, None, true),
            (true, Some("targo"), false),
            (true, Some("trust-src"), true),
            (true, Some("rust-src"), true),
            (true, Some("src"), true),
        ] {
            let ctx = TestCtx::new();
            let mut config = ctx.config("install").create_config();
            config.extended = extended;
            config.tools = selector.map(|tool| [tool.to_owned()].into_iter().collect());
            let sess = Session::new(config);
            let builder = Builder::new(&sess);
            assert_eq!(
                install::Src::is_default_step(&builder),
                expected,
                "extended={extended}, tools={selector:?}"
            );
        }
    }

    #[test]
    fn install_plain() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> rustc 1 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> std 1 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> std 1 <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> UnstableBookGen 1 <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> Rustbook 1 <x86_64-unknown-linux-gnu>
            [doc] unstable-book (book) <x86_64-unknown-linux-gnu>
            [build] rustdoc 1 <x86_64-unknown-linux-gnu>
            [doc] rustc 1 <x86_64-unknown-linux-gnu> -> standalone 2 <x86_64-unknown-linux-gnu>
            [doc] rustc 1 <x86_64-unknown-linux-gnu> -> std 1 <x86_64-unknown-linux-gnu> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> rustc 2 <x86_64-unknown-linux-gnu>
            [build] rustc 2 <x86_64-unknown-linux-gnu> -> std 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> error-index 2 <x86_64-unknown-linux-gnu>
            [doc] rustc 1 <x86_64-unknown-linux-gnu> -> error-index 2 <x86_64-unknown-linux-gnu>
            [doc] rustdoc (book) <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> LintDocs 1 <x86_64-unknown-linux-gnu>
            [doc] rustc (book) <x86_64-unknown-linux-gnu>
            [doc] cargo (book) <x86_64-unknown-linux-gnu>
            [doc] tippy (book) <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> RustInstaller 1 <x86_64-unknown-linux-gnu>
            [dist] docs <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> std 1 <x86_64-unknown-linux-gnu>
            [build] rustdoc 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> trust-analyzer-proc-macro-srv 2 <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> GenerateCopyright 1 <x86_64-unknown-linux-gnu>
            [dist] trustc <x86_64-unknown-linux-gnu>"#]].assert_eq(&ctx.config("install")
            .args(&[
                // Using backslashes fails with `--set`
                "--set", &format!("install.prefix={}", ctx.normalized_dir()),
                "--set", &format!("install.bindir={}", ctx.normalized_dir()),
                "--set", &format!("install.libdir={}", ctx.normalized_dir()),
                "--set", &format!("install.datadir={}", ctx.normalized_dir()),
                "--set", &format!("install.mandir={}", ctx.normalized_dir()),
                "--set", &format!("install.sysconfdir={}", ctx.normalized_dir()),
                "--build", "x86_64-unknown-linux-gnu",
                "--host", "x86_64-unknown-linux-gnu",
                "--target", "x86_64-unknown-linux-gnu",
            ])
            .get_steps()
            .render_with(RenderConfig {
                normalize_host: false
            }));
    }

    // Trust: contributor profiles must select the source component by default.
    // Preserve the explicit rust-src profile spelling and all supported tools
    // allowlist aliases; the separate CLI directory selector remains unchanged.
    #[test]
    fn install_contributor_profiles_include_the_source_component() {
        for profile in ["compiler", "tools"] {
            let ctx = TestCtx::new();
            let cache = install_into_test_dir(&ctx)
                .with_default_toml_config(&format!("profile = \"{profile}\"\n"))
                .run();
            assert!(
                cache.contains::<install::Src>(),
                "`x install` under the {profile} profile must install the source component"
            );
        }
    }

    #[test]
    fn install_source_component_follows_supported_selectors() {
        for (tools, expected) in [
            (r#"build.tools=["trust-src"]"#, true),
            (r#"build.tools=["rust-src"]"#, true),
            (r#"build.tools=["src"]"#, true),
            (r#"build.tools=["targo"]"#, false),
        ] {
            let ctx = TestCtx::new();
            let cache = install_into_test_dir(&ctx)
                .args(&["--set", "build.extended=true", "--set", tools])
                .run();
            assert_eq!(cache.contains::<install::Src>(), expected, "{tools}");
        }
    }

    #[test]
    fn install_src() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> RustInstaller 1 <x86_64-unknown-linux-gnu>
            [dist] src <>"#]]
        .assert_eq(
            &ctx.config("install")
                .path("rust-src")
                .args(&[
                    // Using backslashes fails with `--set`
                    "--set",
                    &format!("install.prefix={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.bindir={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.libdir={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.datadir={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.mandir={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.sysconfdir={}", ctx.normalized_dir()),
                    "--build",
                    "x86_64-unknown-linux-gnu",
                    "--host",
                    "x86_64-unknown-linux-gnu",
                    "--target",
                    "x86_64-unknown-linux-gnu",
                ])
                .get_steps()
                .render_with(RenderConfig { normalize_host: false }),
        );
    }

    #[test]
    fn install_src_no_docs() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> RustInstaller 1 <x86_64-unknown-linux-gnu>
            [dist] src <>"#]]
        .assert_eq(
            &ctx.config("install")
                .path("rust-src")
                .args(&[
                    // Using backslashes fails with `--set`
                    "--set",
                    &format!("install.prefix={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.bindir={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.libdir={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.datadir={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.mandir={}", ctx.normalized_dir()),
                    "--set",
                    &format!("install.sysconfdir={}", ctx.normalized_dir()),
                    "--set",
                    "build.docs=false",
                    "--build",
                    "x86_64-unknown-linux-gnu",
                    "--host",
                    "x86_64-unknown-linux-gnu",
                    "--target",
                    "x86_64-unknown-linux-gnu",
                ])
                .get_steps()
                .render_with(RenderConfig { normalize_host: false }),
        );
    }

    #[test]
    fn install_extended() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> rustc 1 <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> WasmComponentLd 1 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> std 1 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> std 1 <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> UnstableBookGen 1 <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> Rustbook 1 <x86_64-unknown-linux-gnu>
            [doc] unstable-book (book) <x86_64-unknown-linux-gnu>
            [build] rustdoc 1 <x86_64-unknown-linux-gnu>
            [doc] rustc 1 <x86_64-unknown-linux-gnu> -> standalone 2 <x86_64-unknown-linux-gnu>
            [doc] rustc 1 <x86_64-unknown-linux-gnu> -> std 1 <x86_64-unknown-linux-gnu> crates=[alloc,compiler_builtins,core,panic_abort,panic_unwind,proc_macro,rustc-std-workspace-core,std,std_detect,sysroot,test,trust-bignum,unwind]
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> rustc 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> WasmComponentLd 2 <x86_64-unknown-linux-gnu>
            [build] rustc 2 <x86_64-unknown-linux-gnu> -> std 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> error-index 2 <x86_64-unknown-linux-gnu>
            [doc] rustc 1 <x86_64-unknown-linux-gnu> -> error-index 2 <x86_64-unknown-linux-gnu>
            [doc] rustdoc (book) <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> LintDocs 1 <x86_64-unknown-linux-gnu>
            [doc] rustc (book) <x86_64-unknown-linux-gnu>
            [doc] cargo (book) <x86_64-unknown-linux-gnu>
            [doc] tippy (book) <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> RustInstaller 1 <x86_64-unknown-linux-gnu>
            [dist] docs <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> std 1 <x86_64-unknown-linux-gnu>
            [build] rustdoc 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> trust-analyzer-proc-macro-srv 2 <x86_64-unknown-linux-gnu>
            [build] rustc 0 <x86_64-unknown-linux-gnu> -> GenerateCopyright 1 <x86_64-unknown-linux-gnu>
            [dist] trustc <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> trustc-dev 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> targo 2 <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> targo 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> trust-analyzer 2 <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> trust-analyzer 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> rustfmt 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> cargo-fmt 2 <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> trustfmt 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> cargo-clippy 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> clippy-driver 2 <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> tippy 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> miri 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> cargo-miri 2 <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> trust-miri 2 <x86_64-unknown-linux-gnu>
            [dist] src <>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> trustd 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> targo-trust 2 <x86_64-unknown-linux-gnu>
            [dist] rustc 1 <x86_64-unknown-linux-gnu> -> targo-trust 2 <x86_64-unknown-linux-gnu>
            [build] rustc 1 <x86_64-unknown-linux-gnu> -> LlvmBitcodeLinker 2 <x86_64-unknown-linux-gnu>"#]].assert_eq(&ctx.config("install")
            .args(&[
                // Using backslashes fails with `--set`
                "--set", &format!("install.prefix={}", ctx.normalized_dir()),
                "--set", &format!("install.bindir={}", ctx.normalized_dir()),
                "--set", &format!("install.libdir={}", ctx.normalized_dir()),
                "--set", &format!("install.datadir={}", ctx.normalized_dir()),
                "--set", &format!("install.mandir={}", ctx.normalized_dir()),
                "--set", &format!("install.sysconfdir={}", ctx.normalized_dir()),
                "--set", "build.extended=true",
                // Pinned because this snapshot renders un-normalized host triples
                "--build", "x86_64-unknown-linux-gnu",
                "--host", "x86_64-unknown-linux-gnu",
            ])
            .get_steps()
            .render_with(RenderConfig {
                normalize_host: false
            }));
    }

    #[test]
    fn cargo_miri_stage_1() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> miri 1 <host>
            [build] rustc 0 <host> -> cargo-miri 1 <host>
            [build] rustdoc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>"#]]
        .assert_eq(&ctx.config("test").args(&["cargo-miri"]).stage(1).get_steps().render());
    }

    #[test]
    fn cargo_miri_stage_2() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> rustc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 1 <host> -> miri 2 <host>
            [build] rustc 1 <host> -> cargo-miri 2 <host>
            [build] rustdoc 2 <host>
            [build] rustc 2 <host> -> std 2 <host>
            [build] rustc 0 <host> -> targo 1 <host>"#]]
        .assert_eq(&ctx.config("test").args(&["cargo-miri"]).stage(2).get_steps().render());
    }

    #[test]
    fn test_float_parse() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [test] test-float-parse <host>"#]]
        .assert_eq(&ctx.config("test").path("src/tools/test-float-parse").render_steps());
    }

    #[test]
    fn test_float_parse_cross() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 1 <host> -> std 1 <target1>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustdoc 1 <host>
            [test] test-float-parse <target1>"#]]
        .assert_eq(
            &ctx.config("test")
                .path("src/tools/test-float-parse")
                .targets(&[TEST_TRIPLE_1])
                .render_steps(),
        );
    }

    // Check that `x run miri --target FOO` actually builds miri for the host.
    #[test]
    fn run_miri() {
        let ctx = TestCtx::new();
        expect_test::expect![[r#"
            [build] llvm <host>
            [build] rustc 0 <host> -> rustc 1 <host>
            [build] rustc 1 <host> -> std 1 <host>
            [build] rustc 0 <host> -> miri 1 <host>
            [build] rustc 0 <host> -> cargo-miri 1 <host>
            [run] rustc 0 <host> -> miri 1 <target1>"#]]
        .assert_eq(
            &ctx.config("run").path("miri").stage(1).targets(&[TEST_TRIPLE_1]).render_steps(),
        );
    }

    #[test]
    fn fix_compiler() {
        let ctx = TestCtx::new();
        // Trust: T11 removed hmac from rustc-main's closure, keeping its workspace tests.
        assert_compiler_plan(
            &ctx,
            expect_test::expect!["[fix] rustc 0 <host> -> rustc 1 <host> (compiler crates)"],
            &ctx.config("fix").path("compiler").render_steps(),
        );
    }
}

// Check the selected compiler closure against native workspace metadata. Its
// size changes when an actual compiler dependency is added or removed.
fn assert_compiler_plan(ctx: &TestCtx, expected: expect_test::Expect, actual: &str) {
    let session = Session::new(ctx.config("check").create_config());
    let count = session.in_tree_crates("rustc-main", None).len();
    let expected = expected
        .data()
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
        .replace("(compiler crates)", &format!("({count} crates)"));
    assert_eq!(actual, expected);
}

struct ExecutedSteps {
    steps: Vec<ExecutedStep>,
}

impl ExecutedSteps {
    fn render(&self) -> String {
        self.render_with(RenderConfig::default())
    }

    fn render_with(&self, config: RenderConfig) -> String {
        render_steps(&self.steps, config)
    }

    #[track_caller]
    fn assert_contains<M: Into<StepMetadata>>(&self, metadata: M) {
        let metadata = metadata.into();
        if !self.contains(&metadata) {
            panic!(
                "Metadata `{}` ({metadata:?}) not found in executed steps:\n{}",
                render_metadata(&metadata, &RenderConfig::default()),
                self.render()
            );
        }
    }

    /// Try to match metadata by similarity, it does not need to match exactly.
    /// Stages (and built_by compiler) do not need to match, but name, target and
    /// kind has to match.
    #[track_caller]
    fn assert_contains_fuzzy<M: Into<StepMetadata>>(&self, metadata: M) {
        let metadata = metadata.into();
        if !self.contains_fuzzy(&metadata) {
            panic!(
                "Metadata `{}` ({metadata:?}) not found in executed steps:\n{}",
                render_metadata(&metadata, &RenderConfig::default()),
                self.render()
            );
        }
    }

    #[track_caller]
    fn assert_not_contains<M: Into<StepMetadata>>(&self, metadata: M) {
        let metadata = metadata.into();
        if self.contains(&metadata) {
            panic!(
                "Metadata `{}` ({metadata:?}) found in executed steps (it should not be there):\n{}",
                render_metadata(&metadata, &RenderConfig::default()),
                self.render()
            );
        }
    }

    /// Make sure that no metadata matches the given `func`.
    #[track_caller]
    fn assert_no_match<F>(&self, func: F)
    where
        F: Fn(StepMetadata) -> bool,
    {
        for metadata in self.steps.iter().filter_map(|s| s.metadata.clone()) {
            if func(metadata.clone()) {
                panic!(
                    "Metadata {metadata:?} was found, even though it should have not been present"
                );
            }
        }
    }

    fn contains(&self, metadata: &StepMetadata) -> bool {
        self.steps
            .iter()
            .filter_map(|s| s.metadata.as_ref())
            .any(|executed_metadata| executed_metadata == metadata)
    }

    fn contains_fuzzy(&self, metadata: &StepMetadata) -> bool {
        self.steps
            .iter()
            .filter_map(|s| s.metadata.as_ref())
            .any(|executed_metadata| fuzzy_metadata_eq(executed_metadata, metadata))
    }
}

fn fuzzy_metadata_eq(executed: &StepMetadata, to_match: &StepMetadata) -> bool {
    let StepMetadata { name, kind, target, built_by: _, stage: _, metadata: _ } = executed;
    *name == to_match.name && *kind == to_match.kind && *target == to_match.target
}

impl<S: Step> From<S> for StepMetadata {
    fn from(step: S) -> Self {
        step.metadata().expect("step has no metadata")
    }
}

impl ConfigBuilder {
    fn run(self) -> Cache {
        let config = self.create_config();

        let sess = Session::new(config);
        let builder = Builder::new(&sess);
        builder
            .run_step_descriptions(&Builder::get_step_descriptions(builder.kind), &builder.paths);
        builder.cache
    }

    fn get_steps(self) -> ExecutedSteps {
        let cache = self.run();
        ExecutedSteps { steps: cache.into_executed_steps() }
    }

    fn render_steps(self) -> String {
        self.get_steps().render()
    }
}

struct RenderConfig {
    normalize_host: bool,
}

impl Default for RenderConfig {
    fn default() -> Self {
        Self { normalize_host: true }
    }
}

/// Renders the executed bootstrap steps for usage in snapshot tests with insta.
/// Only renders certain important steps.
/// Each value in `steps` should be a tuple of (Step, step output).
///
/// The arrow in the rendered output (`X -> Y`) means `X builds Y`.
/// This is similar to the output printed by bootstrap to stdout, but here it is
/// generated purely for the purpose of tests.
fn render_steps(steps: &[ExecutedStep], config: RenderConfig) -> String {
    steps
        .iter()
        .filter_map(|step| {
            let Some(metadata) = &step.metadata else {
                return None;
            };

            Some(render_metadata(&metadata, &config))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_metadata(metadata: &StepMetadata, config: &RenderConfig) -> String {
    let mut record = format!("[{}] ", metadata.kind.as_str());
    if let Some(compiler) = metadata.built_by {
        write!(record, "{} -> ", render_compiler(compiler, config)).unwrap();
    }
    let stage = metadata.get_stage().map(|stage| format!("{stage} ")).unwrap_or_default();
    write!(record, "{} {stage}<{}>", metadata.name, normalize_target(metadata.target, config))
        .unwrap();
    if let Some(metadata) = &metadata.metadata {
        write!(record, " {metadata}").unwrap();
    }
    record
}

fn normalize_target(target: TargetSelection, config: &RenderConfig) -> String {
    let mut target = target.to_string();
    if config.normalize_host {
        target = target.replace(&host_target(), "host");
    }
    target.replace(TEST_TRIPLE_1, "target1").replace(TEST_TRIPLE_2, "target2")
}

fn render_compiler(compiler: Compiler, config: &RenderConfig) -> String {
    format!("rustc {} <{}>", compiler.stage, normalize_target(compiler.host, config))
}

fn host_target() -> String {
    get_host_target().to_string()
}

#[test]
fn flags_env_prefers_plain_form_without_spaces() {
    use super::cargo::flags_env;

    // No flag value contains a space, so use the readable, copy-pasteable plain form
    // rather than the `\x1f`-separated encoded form (rust-lang/rust#158749).
    assert_eq!(
        flags_env("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "--cfg=foo\u{1f}-Cdebuginfo=0"),
        ("RUSTFLAGS", "--cfg=foo -Cdebuginfo=0".to_string()),
    );

    // A flag value contains a space (e.g. an `-L` path), which the whitespace-split plain
    // form can't represent, so keep the encoded form.
    assert_eq!(
        flags_env(
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "-Clink-arg=-L/opt/my libs\u{1f}--cfg=foo"
        ),
        ("CARGO_ENCODED_RUSTFLAGS", "-Clink-arg=-L/opt/my libs\u{1f}--cfg=foo".to_string()),
    );
}

/// Trust: a bootstrap `--print=…` query must never be the thing that demands a
/// `dlopen`ed codegen backend the sysroot does not carry yet.
///
/// The measured failure this pins: with `codegen-backends = ["trust-ir-cg", "llvm",
/// "trust-cg"]`, `x.py build --stage 2 compiler/rustc` died on
/// `--print=deployment-target` with `failed to find a codegen-backends folder in the
/// sysroot candidates: build/<host>/stage1`, because the probe runs while `Assemble`
/// is still setting that sysroot up.
mod metadata_probe_backend {
    use crate::core::backend::CodegenBackendKind::{Custom, Llvm, TrustCg, TrustIrCg};
    use crate::core::builder::metadata_probe_backend_name;

    #[test]
    fn upstream_configurations_say_nothing() {
        // The overwhelmingly common case: LLVM is the default, it is linked into
        // rustc_driver, and the probe needs no help. Byte-for-byte upstream behaviour.
        assert_eq!(metadata_probe_backend_name(1, &Llvm, &[Llvm]), None);
        assert_eq!(metadata_probe_backend_name(2, &Llvm, &[Llvm, TrustIrCg]), None);
        // trust-cg is also linked in, so it needs no help either.
        assert_eq!(metadata_probe_backend_name(2, &TrustCg, &[TrustCg, Llvm]), None);
    }

    #[test]
    fn a_plugin_default_falls_back_to_the_first_linked_in_backend() {
        assert_eq!(
            metadata_probe_backend_name(1, &TrustIrCg, &[TrustIrCg, Llvm, TrustCg]),
            Some("llvm"),
        );
        // Order within the enabled list decides, not a hard-coded name: with llvm
        // dropped, trust-cg is the honest answer.
        assert_eq!(
            metadata_probe_backend_name(1, &TrustIrCg, &[TrustIrCg, TrustCg]),
            Some("trust-cg"),
        );
        // A custom out-of-tree backend is a plugin too.
        assert_eq!(
            metadata_probe_backend_name(
                2,
                &Custom("cranelift".into()),
                &[Custom("cranelift".into()), Llvm]
            ),
            Some("llvm"),
        );
    }

    #[test]
    fn stage0_is_never_pinned() {
        // A stage0 compiler is a snapshot built elsewhere. This build's
        // `codegen-backends` describes neither its baked default nor the options it
        // understands, so passing it `-Zcodegen-backend` is a guess, not a fix.
        assert_eq!(metadata_probe_backend_name(0, &TrustIrCg, &[TrustIrCg, Llvm]), None);
    }

    #[test]
    fn no_linked_in_backend_configured_is_a_refusal_not_a_guess() {
        // `dummy` would "work" here and is deliberately not offered: its
        // `supported_crate_types` answers `[Rlib, Executable]`, which would make the
        // `--print=file-names --crate-type=proc-macro` probe read "unsupported crate
        // type" and silently drop `-Zdual-proc-macros`. Failing loudly at the probe is
        // the honest outcome.
        assert_eq!(metadata_probe_backend_name(1, &TrustIrCg, &[TrustIrCg]), None);
        assert_eq!(
            metadata_probe_backend_name(
                1,
                &Custom("cranelift".into()),
                &[Custom("cranelift".into())]
            ),
            None,
        );
    }
}

/// Trust: on macOS `copy_link` must install an executable as a file of its own, never as
/// another hard link of the cargo output, because dyld can resolve the main executable's
/// `@loader_path` through the other link (see `FileType::may_hard_link`). A library keeps
/// the hard-link fast path, and so does an executable everywhere else.
#[test]
#[cfg(unix)]
fn copy_link_never_hard_links_an_executable_on_macos() {
    use std::os::unix::fs::MetadataExt;

    let ctx = TestCtx::new();
    let mut build = crate::core::session::Session::new(ctx.config("build").create_config());
    build.config.set_dry_run(crate::core::config::DryRun::Disabled);

    let src = ctx.dir().join("rustc-main");
    std::fs::write(&src, b"rustc-main").unwrap();
    let exe = ctx.dir().join("rustc");
    let lib = ctx.dir().join("librustc_driver.dylib");
    build.copy_link(&src, &exe, crate::core::session::FileType::Executable);
    build.copy_link(&src, &lib, crate::core::session::FileType::NativeLibrary);

    let inode = |path: &Path| std::fs::metadata(path).unwrap().ino();
    assert_eq!(std::fs::read(&exe).unwrap(), b"rustc-main");
    if cfg!(target_os = "macos") {
        assert_ne!(inode(&exe), inode(&src), "a macOS executable must not share the inode");
    } else {
        assert_eq!(inode(&exe), inode(&src));
    }
    assert_eq!(inode(&lib), inode(&src), "a library keeps the hard-link fast path");
}

// Trust: exercise the real LLVM provider installer without modifying a shared provider.
#[cfg(unix)]
mod resolved_provider_copy {
    use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};

    use super::*;

    fn identity(path: &Path) -> (u64, u64, u64, i64, i64, u64, u32, i64, i64) {
        let metadata = std::fs::metadata(path).unwrap();
        (
            metadata.dev(),
            metadata.ino(),
            metadata.nlink(),
            metadata.ctime(),
            metadata.ctime_nsec(),
            metadata.len(),
            metadata.mode(),
            metadata.mtime(),
            metadata.mtime_nsec(),
        )
    }

    fn executable(path: &Path) {
        std::fs::write(path, b"#!/bin/sh\nexit 0\n").unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    fn session(ctx: &TestCtx) -> Session {
        let mut session = Session::new(ctx.config("build").create_config());
        session.config.set_dry_run(crate::core::config::DryRun::Disabled);
        session
    }

    #[test]
    fn preserves_source_across_install_and_reassembly() {
        let ctx = TestCtx::new();
        let session = session(&ctx);
        let source = ctx.dir().join("provider-llvm-objcopy");
        let destination = ctx.dir().join("sysroot-rust-objcopy");
        executable(&source);
        let original = identity(&source);
        let bytes = std::fs::read(&source).unwrap();

        for _ in 0..2 {
            session.resolve_symlink_and_copy(&source, &destination);
            assert_eq!(identity(&source), original, "install must leave provider metadata intact");
            assert_eq!(std::fs::read(&source).unwrap(), bytes);
            assert_ne!(identity(&destination).1, original.1, "destination must have its own inode");
            assert_eq!(std::fs::read(&destination).unwrap(), bytes);
            assert_eq!(std::fs::metadata(&destination).unwrap().mode() & 0o777, 0o755);
            std::fs::write(&destination, b"owned destination edit").unwrap();
            assert_eq!(
                std::fs::read(&source).unwrap(),
                bytes,
                "destination writes must be isolated"
            );
            assert_eq!(identity(&source), original);
        }
    }

    #[test]
    fn dereferences_relative_alias_chain_without_mutating_provider() {
        let ctx = TestCtx::new();
        let session = session(&ctx);
        let source = ctx.dir().join("llvm-objcopy");
        let alias = ctx.dir().join("llvm-strip");
        let second_alias = ctx.dir().join("llvm-install-name-tool");
        let destination = ctx.dir().join("installed-llvm-strip");
        executable(&source);
        symlink("llvm-objcopy", &alias).unwrap();
        symlink("llvm-strip", &second_alias).unwrap();
        let original = identity(&source);
        let alias_metadata = std::fs::symlink_metadata(&alias).unwrap();

        for _ in 0..2 {
            session.resolve_symlink_and_copy(&second_alias, &destination);
            assert!(!std::fs::symlink_metadata(&destination).unwrap().file_type().is_symlink());
            assert_ne!(identity(&destination).1, original.1);
            assert_eq!(std::fs::read(&destination).unwrap(), std::fs::read(&source).unwrap());
            assert_eq!(std::fs::metadata(&destination).unwrap().mode() & 0o777, 0o755);
            assert_eq!(identity(&source), original);
            let actual_alias = std::fs::symlink_metadata(&alias).unwrap();
            assert_eq!(actual_alias.ino(), alias_metadata.ino());
            assert_eq!(actual_alias.nlink(), alias_metadata.nlink());
            assert_eq!(actual_alias.ctime(), alias_metadata.ctime());
            assert_eq!(actual_alias.ctime_nsec(), alias_metadata.ctime_nsec());
            assert_eq!(std::fs::read_link(&alias).unwrap(), Path::new("llvm-objcopy"));
            assert_eq!(std::fs::read_link(&second_alias).unwrap(), Path::new("llvm-strip"));
        }
    }

    #[test]
    fn detaches_legacy_destination_then_preserves_provider_on_reassembly() {
        let ctx = TestCtx::new();
        let session = session(&ctx);
        let source = ctx.dir().join("provider-opt");
        let destination = ctx.dir().join("legacy-installed-opt");
        executable(&source);
        let original = identity(&source);
        std::fs::hard_link(&source, &destination).unwrap();
        assert_eq!(identity(&source).2, original.2 + 1);

        // Trust: retiring an old shared inode necessarily changes its link metadata once.
        session.resolve_symlink_and_copy(&source, &destination);
        assert_eq!(identity(&source).1, original.1);
        assert_eq!(identity(&source).2, original.2);
        assert_ne!(identity(&destination).1, original.1);
        assert_eq!(std::fs::read(&source).unwrap(), b"#!/bin/sh\nexit 0\n");
        let detached = identity(&source);
        session.resolve_symlink_and_copy(&source, &destination);
        assert_eq!(identity(&source), detached);
        assert_ne!(identity(&destination).1, original.1);
    }

    #[test]
    fn replaces_destination_symlink_without_writing_its_target() {
        let ctx = TestCtx::new();
        let session = session(&ctx);
        let source = ctx.dir().join("provider-llc");
        let unrelated = ctx.dir().join("unrelated-target");
        let destination = ctx.dir().join("installed-llc");
        executable(&source);
        std::fs::write(&unrelated, b"untouched").unwrap();
        symlink(&unrelated, &destination).unwrap();
        let source_before = identity(&source);
        let unrelated_before = identity(&unrelated);

        session.resolve_symlink_and_copy(&source, &destination);

        assert!(!std::fs::symlink_metadata(&destination).unwrap().file_type().is_symlink());
        assert_eq!(identity(&source), source_before);
        assert_eq!(identity(&unrelated), unrelated_before);
        assert_eq!(std::fs::read(&unrelated).unwrap(), b"untouched");
        assert_ne!(identity(&destination).1, source_before.1);
        assert_eq!(std::fs::read(&destination).unwrap(), std::fs::read(&source).unwrap());
    }
}

// Trust: the explicit development component owns a real compiler1 producer,
// not development files copied from the seed-built compiler into stage1.
#[test]
fn build_development_component_uses_current_producer_and_complete_targets() {
    let host = host_target();
    for alias in ["trustc-dev", "rustc-dev"] {
        let config = configure_with_args(
            &["build", "--stage", "1", alias],
            &[&host],
            &[&host, TEST_TRIPLE_1],
        );
        let cache = run_build(&config.paths.clone(), config);
        assert_eq!(
            cache.inspect_all_steps_of_type::<compile::RustcDev, _>(|_, compiler| compiler.stage),
            vec![2],
        );
        let compilers = cache.inspect_all_steps_of_type::<compile::Rustc, _>(|step, built| {
            assert_eq!(step.build_compiler, built.build_compiler);
            built.build_compiler.stage
        });
        assert_eq!(compilers, vec![0, 1]);
        let libraries = cache.inspect_all_steps_of_type::<compile::Std, _>(|step, _| {
            (step.build_compiler.stage, step.target.to_string())
        });
        for target in [host.as_str(), TEST_TRIPLE_1] {
            assert!(libraries.contains(&(1, target.to_owned())), "{libraries:?}");
            assert!(libraries.contains(&(2, target.to_owned())), "{libraries:?}");
        }
        // The same maintained producer is used without entering Dist/Install.
        assert!(!cache.contains::<dist::RustcDev>());
        assert!(cache.executed_steps().iter().all(|step| {
            step.metadata.as_ref().is_none_or(|metadata| metadata.kind == Kind::Build)
        }));
    }
}

#[test]
fn build_development_component_is_never_a_default() {
    let host = host_target();
    let cache = run_build(&[], configure_with_args(&["build", "--stage", "1"], &[&host], &[&host]));
    assert!(!cache.contains::<compile::RustcDev>());
}

#[test]
fn build_development_component_rejects_alternate_producers_before_dispatch() {
    let host = host_target();
    // Ordinary stage0 configuration already refuses before a Builder exists.
    assert!(
        panic::catch_unwind(|| {
            configure_with_args(&["build", "--stage", "0", "trustc-dev"], &[&host], &[&host]);
        })
        .is_err()
    );
    for args in [
        // Admit ordinary source-rebuild configuration, then require this
        // component to reject stage0 before dispatching any compiler work.
        vec!["build", "--stage", "0", "trustc-dev", "--set", "build.local-rebuild=true"],
        vec!["build", "--stage", "2", "trustc-dev"],
        vec!["build", "--stage", "1", "trustc-dev", "--keep-stage", "0"],
        vec!["build", "--stage", "1", "trustc-dev", "--keep-stage-std", "1"],
        vec!["build", "--stage", "1", "trustc-dev", "--skip", "library"],
    ] {
        let sess = Session::new(configure_with_args(&args, &[&host], &[&host]));
        let builder = Builder::new(&sess);
        let rejected = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            builder.ensure(compile::RustcDev { target: builder.host_target });
        }));
        assert!(rejected.is_err(), "{args:?}");
        assert!(!builder.cache.contains::<compile::Rustc>());
        assert!(!builder.cache.contains::<compile::Assemble>());
    }
    let sess = Session::new(configure_with_args(
        &["build", "--stage", "1", "trustc-dev"],
        &[&host],
        &[&host],
    ));
    let builder = Builder::new(&sess);
    assert!(
        panic::catch_unwind(panic::AssertUnwindSafe(|| {
            builder.ensure(compile::RustcDev { target: TargetSelection::from_user(TEST_TRIPLE_1) });
        }))
        .is_err()
    );
    assert!(!builder.cache.contains::<compile::Rustc>());
    assert!(!builder.cache.contains::<compile::Assemble>());
}
