// Trust: compiler-crate unit/doctest pass selection; kept in the test-only tree.
use super::{TestTarget, compiler_crate_test_passes};
use crate::core::build_steps::tool::SourceType;
use crate::core::builder::{Builder, Cargo, Kind};
use crate::core::session::{Mode, Session};
use crate::utils::tests::TestCtx;

// Trust: only the explicitly selected native compiler unit pass changes owners.
#[test]
fn native_compiler_unit_program_selection_is_doc_free_and_host_only() {
    use crate::core::builder::CargoInput;

    for target in [TestTarget::Tests, TestTarget::Lib] {
        assert_eq!(
            super::compiler_unit_test_cargo_input(
                Mode::Rustc,
                Kind::Test,
                target,
                true,
                true,
                false,
                false,
            ),
            CargoInput::CurrentNativeUnitTests,
        );
    }
    for (mode, kind, target, native, supported, remote, runner) in [
        (Mode::Rustc, Kind::Test, TestTarget::Tests, false, true, false, false),
        (Mode::Rustc, Kind::Test, TestTarget::Tests, true, false, false, false),
        (Mode::Rustc, Kind::Test, TestTarget::Tests, true, true, true, false),
        (Mode::Rustc, Kind::Test, TestTarget::Tests, true, true, false, true),
        (Mode::Rustc, Kind::Test, TestTarget::DocOnly, true, true, false, false),
        (Mode::Rustc, Kind::Test, TestTarget::AllTargets, true, true, false, false),
        (Mode::Rustc, Kind::Build, TestTarget::Tests, true, true, false, false),
        (Mode::Rustc, Kind::Miri, TestTarget::Tests, true, true, false, false),
        (Mode::Std, Kind::Test, TestTarget::Tests, true, true, false, false),
        (Mode::ToolRustcPrivate, Kind::Test, TestTarget::Tests, true, true, false, false),
    ] {
        assert_eq!(
            super::compiler_unit_test_cargo_input(
                mode, kind, target, native, supported, remote, runner,
            ),
            CargoInput::for_mode(mode),
        );
    }
}

#[test]
fn default_keeps_seed_units_and_uses_current_doctests() {
    assert_eq!(
        compiler_crate_test_passes(0, TestTarget::Default),
        [(0, TestTarget::AllTargets), (1, TestTarget::DocOnly)],
    );
}

#[test]
fn explicit_doctests_use_current_compiler_metadata() {
    assert_eq!(compiler_crate_test_passes(0, TestTarget::DocOnly), [(1, TestTarget::DocOnly)],);
    assert_eq!(compiler_crate_test_passes(1, TestTarget::DocOnly), [(1, TestTarget::DocOnly)],);
}

#[test]
fn explicit_non_doc_and_later_stage_passes_keep_their_scope() {
    for stage in 0..=2 {
        for target in [TestTarget::Tests, TestTarget::Lib, TestTarget::AllTargets] {
            assert_eq!(compiler_crate_test_passes(stage, target), [(stage, target)]);
        }
    }
    for stage in 1..=2 {
        assert_eq!(
            compiler_crate_test_passes(stage, TestTarget::Default),
            [(stage, TestTarget::Default)],
        );
    }
}

#[test]
fn compiler_unit_commands_keep_build_inputs_and_use_matching_fixture_runtime() {
    for (build_stage, test_target) in (0..=2).flat_map(|stage| {
        [TestTarget::AllTargets, TestTarget::Tests, TestTarget::Lib, TestTarget::Default]
            .map(|target| (stage, target))
    }) {
        let ctx = TestCtx::new();
        let config = ctx.config("test").path("compiler").stage(build_stage + 1).create_config();
        let sess = Session::new(config);
        let builder = Builder::new(&sess);
        let host = builder.host_target;
        let build_compiler = builder.compiler(build_stage, host);
        let compiler_path = builder.rustc(build_compiler);
        let build_sysroot = builder.sysroot(build_compiler);
        let cargo =
            Cargo::new(&builder, build_compiler, Mode::Rustc, SourceType::InTree, host, Kind::Test);
        let mut command = super::prepare_cargo_test_for_target(
            cargo,
            &[],
            &["rustc_hir".to_owned()],
            host,
            &builder,
            test_target,
        );
        // This is a dry-run command; inspect the production preparation path.
        command.mark_as_executed();
        let env: std::collections::BTreeMap<_, _> = command
            .get_envs()
            .map(|(key, value)| (key.to_owned(), value.map(std::ffi::OsStr::to_owned)))
            .collect();
        let runtime = builder.compiler(build_stage.max(1), host);
        assert_eq!(
            env[std::ffi::OsStr::new("RUSTC_REAL")].as_deref(),
            Some(compiler_path.as_os_str())
        );
        assert_eq!(
            env[std::ffi::OsStr::new("RUSTC_SYSROOT")].as_deref(),
            Some(build_sysroot.as_os_str())
        );
        assert_eq!(
            env[std::ffi::OsStr::new("TEST_SYSROOT")].as_deref(),
            Some(builder.sysroot(runtime).as_os_str()),
        );
        assert!(!env.contains_key(std::ffi::OsStr::new("TEST_COMPILER_FIXTURE_ID")));
        let args: Vec<_> = command.get_args().collect();
        assert_eq!(
            args.contains(&std::ffi::OsStr::new("--tests")),
            matches!(test_target, TestTarget::Tests | TestTarget::AllTargets)
        );
        assert_eq!(
            args.contains(&std::ffi::OsStr::new("--examples")),
            test_target == TestTarget::AllTargets
        );
        assert!(!args.contains(&std::ffi::OsStr::new("--doc")));
        assert_eq!(args.contains(&std::ffi::OsStr::new("--lib")), test_target == TestTarget::Lib);
    }
}

// Trust: exercise the same command preparation as real compiler unit tests.
// A retained runtime skips only its fixture prerequisite; the build compiler
// and build sysroot remain the independently configured seed inputs.
#[test]
fn retained_compiler_fixture_selects_only_library_test_runtime() {
    let ctx = TestCtx::new();
    let config = ctx.config("test").path("compiler").stage(1).create_config();
    let mut sess = Session::new(config);
    let fixture_root = ctx.dir().join("retained-runtime");
    sess.compiler_test_fixture = Some(
        crate::utils::retained_compiler_fixture::RetainedCompilerTestFixture::for_command_test(
            fixture_root.clone(),
        ),
    );
    let builder = Builder::new(&sess);
    let host = builder.host_target;
    let compiler = builder.compiler(0, host);
    let compiler_path = builder.rustc(compiler);
    let build_sysroot = builder.sysroot(compiler);
    let cargo = Cargo::new(&builder, compiler, Mode::Rustc, SourceType::InTree, host, Kind::Test);
    let mut command = super::prepare_cargo_test_for_target(
        cargo,
        &[],
        &["rustc_mir_transform".into()],
        host,
        &builder,
        TestTarget::AllTargets,
    );
    command.mark_as_executed();
    let env: std::collections::BTreeMap<_, _> = command
        .get_envs()
        .map(|(key, value)| (key.to_owned(), value.map(std::ffi::OsStr::to_owned)))
        .collect();
    for (key, expected) in [
        ("RUSTC_REAL", compiler_path.as_os_str()),
        ("RUSTC_SYSROOT", build_sysroot.as_os_str()),
        ("TEST_SYSROOT", fixture_root.as_os_str()),
    ] {
        assert_eq!(env[std::ffi::OsStr::new(key)].as_deref(), Some(expected));
    }
    assert_eq!(
        env[std::ffi::OsStr::new("TEST_COMPILER")].as_deref(),
        Some(fixture_root.join("bin/trustc").as_os_str())
    );
    let args: Vec<_> = command.get_args().collect();
    assert!(args.contains(&std::ffi::OsStr::new("--lib")));
    for flag in ["--tests", "--doc", "--bins", "--examples", "--benches"] {
        assert!(!args.contains(&std::ffi::OsStr::new(flag)));
    }
    assert!(
        builder
            .step_cache()
            .inspect_all_steps_of_type::<crate::core::build_steps::compile::Assemble, _>(
                |step, _| step.target_compiler.stage
            )
            .iter()
            .all(|stage| *stage == 0),
        "retained fixture selection must not request a next-stage compiler"
    );
}

#[test]
fn doc_only_and_non_compiler_commands_do_not_get_a_fixture_sysroot() {
    for (mode, test_target) in [
        (Mode::Rustc, TestTarget::DocOnly),
        (Mode::Std, TestTarget::Tests),
        (Mode::ToolBootstrap, TestTarget::Tests),
    ] {
        let ctx = TestCtx::new();
        let config = ctx.config("test").path("compiler").stage(1).create_config();
        let sess = Session::new(config);
        let builder = Builder::new(&sess);
        let host = builder.host_target;
        let compiler = builder.compiler(0, host);
        let cargo = Cargo::new(&builder, compiler, mode, SourceType::InTree, host, Kind::Test);
        let mut command = super::prepare_cargo_test_for_target(
            cargo,
            &[],
            &["test-fixture".to_owned()],
            host,
            &builder,
            test_target,
        );
        command.mark_as_executed();
        assert!(command.get_envs().all(|(key, _)| key != std::ffi::OsStr::new("TEST_SYSROOT")));
    }
}

#[test]
fn compiler_runtime_sysroot_does_not_leak_into_doc_only_or_std_tests() {
    for compiler_stage in [0, 1] {
        for (mode, test_target) in [
            (Mode::Rustc, TestTarget::DocOnly),
            (Mode::Std, TestTarget::Tests),
            (Mode::Std, TestTarget::AllTargets),
        ] {
            let ctx = TestCtx::new();
            let config =
                ctx.config("test").path("compiler").stage(compiler_stage + 1).create_config();
            let sess = Session::new(config);
            let builder = Builder::new(&sess);
            let host = builder.host_target;
            let compiler = builder.compiler(compiler_stage, host);
            let cargo = Cargo::new(&builder, compiler, mode, SourceType::InTree, host, Kind::Test);
            let mut command = super::prepare_cargo_test_for_target(
                cargo,
                &[],
                &["rustc_hir".to_owned()],
                host,
                &builder,
                test_target,
            );
            command.mark_as_executed();
            assert!(!command.get_envs().any(|(key, _)| key == "TEST_SYSROOT"));
        }
    }
}
