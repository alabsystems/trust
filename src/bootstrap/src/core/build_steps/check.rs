//! Implementation of compiling the compiler and standard library, in "check"-based modes.

use std::fs;
use std::path::{Path, PathBuf};

// Trust: this module has no codegen-backend-kind use.
use crate::core::build_steps::compile::{
    ArtifactKeepMode, add_to_sysroot, run_cargo, rustc_cargo, std_cargo, std_crates_for_make_run,
};
use crate::core::build_steps::tool;
use crate::core::build_steps::tool::{
    SourceType, TEST_FLOAT_PARSE_ALLOW_FEATURES, ToolTargetBuildMode, get_tool_target_compiler,
    prepare_tool_cargo,
};
use crate::core::builder::{
    self, Alias, Builder, Cargo, CommandLineStep, Kind, RunConfig, ShouldRun, Step, StepMetadata,
    crate_description,
};
use crate::core::compiler::Compiler;
use crate::core::config::TargetSelection;
use crate::core::session::Mode;
use crate::utils::build_stamp::{self, BuildStamp};
use crate::utils::helpers::t;

/// Allows individual check-step instances to keep track of whether they
/// represent `cargo check` or `cargo fix`, independently of [`Builder::kind`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum CheckKind {
    Check,
    Fix,
}

impl CheckKind {
    fn to_kind(self) -> Kind {
        match self {
            CheckKind::Check => Kind::Check,
            CheckKind::Fix => Kind::Fix,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Std {
    /// Compiler that will check this std.
    pub build_compiler: Compiler,
    pub target: TargetSelection,
    /// Whether to build only a subset of crates.
    ///
    /// This shouldn't be used from other steps; see the comment on [`compile::Rustc`].
    ///
    /// [`compile::Rustc`]: crate::core::build_steps::compile::Rustc
    crates: Vec<String>,
}

impl Std {
    const CRATE_OR_DEPS: &[&str] = &["sysroot", "coretests", "alloctests"];
}

impl CommandLineStep for Std {
    type Output = BuildStamp;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        let mut run = run;
        for c in Std::CRATE_OR_DEPS {
            run = run.crate_or_deps(c);
        }

        run.path("library")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        if !run.builder.download_rustc() && run.builder.config.skip_std_check_if_no_download_rustc {
            eprintln!(
                "WARNING: `--skip-std-check-if-no-download-rustc` flag was passed and `rust.download-rustc` is not available. Skipping."
            );
            return;
        }

        if run.builder.config.compile_time_deps {
            // libstd doesn't have any important build scripts and can't have any proc macros
            return;
        }

        // Explicitly pass -p for all dependencies crates -- this will force cargo
        // to also check the tests/benches/examples for these crates, rather
        // than just the leaf crate.
        let crates = std_crates_for_make_run(&run);
        run.builder.ensure(Std {
            build_compiler: prepare_compiler_for_check(run.builder, run.target, Mode::Std)
                .build_compiler(),
            target: run.target,
            crates,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let build_compiler = self.build_compiler;
        let target = self.target;

        let mut cargo = builder::Cargo::new(
            builder,
            build_compiler,
            Mode::Std,
            SourceType::InTree,
            target,
            builder.kind,
        );

        std_cargo(builder, target, &mut cargo, &self.crates);
        if matches!(builder.kind, Kind::Fix) {
            // By default, cargo tries to fix all targets. Tell it not to fix tests until we've added `test` to the sysroot.
            cargo.arg("--lib");
        }

        let _guard = builder.msg(
            builder.kind,
            format_args!("library artifacts{}", crate_description(&self.crates)),
            Mode::Std,
            build_compiler,
            target,
        );

        let check_stamp =
            build_stamp::libstd_stamp(builder, build_compiler, target).with_prefix("check");
        run_cargo(
            builder,
            cargo,
            builder.config.free_args.clone(),
            &check_stamp,
            vec![],
            ArtifactKeepMode::OnlyRmeta,
        );

        drop(_guard);

        // don't check test dependencies if we haven't built libtest
        if !self.crates.iter().any(|krate| krate == "test") {
            return check_stamp;
        }

        // Then run cargo again, once we've put the rmeta files for the library
        // crates into the sysroot. This is needed because e.g., core's tests
        // depend on `libtest` -- Cargo presumes it will exist, but it doesn't
        // since we initialize with an empty sysroot.
        //
        // Currently only the "libtest" tree of crates does this.
        let mut cargo = builder::Cargo::new(
            builder,
            build_compiler,
            Mode::Std,
            SourceType::InTree,
            target,
            Kind::Check,
        );

        std_cargo(builder, target, &mut cargo, &self.crates);

        let stamp =
            build_stamp::libstd_stamp(builder, build_compiler, target).with_prefix("check-test");
        let _guard = builder.msg(
            Kind::Check,
            "library test/bench/example targets",
            Mode::Std,
            build_compiler,
            target,
        );
        run_cargo(
            builder,
            cargo,
            builder.config.free_args.clone(),
            &stamp,
            vec![],
            ArtifactKeepMode::OnlyRmeta,
        );
        check_stamp
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::check("std", self.target).built_by(self.build_compiler))
    }
}

/// Represents a proof that rustc was **checked**.
/// Contains directories with .rmeta files generated by checking rustc for a specific
/// target.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RmetaSysroot {
    host_dir: PathBuf,
    target_dir: PathBuf,
}

impl RmetaSysroot {
    /// Copy rmeta artifacts from the given `stamp` into a sysroot located at `directory`.
    fn from_stamp(
        builder: &Builder<'_>,
        stamp: BuildStamp,
        target: TargetSelection,
        directory: &Path,
    ) -> Self {
        let host_dir = directory.join("host");
        let target_dir = directory.join(target);
        let _ = fs::remove_dir_all(directory);
        t!(fs::create_dir_all(directory));
        add_to_sysroot(builder, &target_dir, &host_dir, &stamp);

        Self { host_dir, target_dir }
    }

    /// Configure the given cargo invocation so that the compiled crate will be able to use
    /// rustc .rmeta artifacts that were previously generated.
    fn configure_cargo(&self, cargo: &mut Cargo) {
        cargo.append_to_env(
            "RUSTC_ADDITIONAL_SYSROOT_PATHS",
            format!("{},{}", self.host_dir.to_str().unwrap(), self.target_dir.to_str().unwrap()),
            ",",
        );
        // Trust: build-script probes can invoke the compiler directly, bypassing
        // the shim's environment channel. Expose the same metadata directories
        // through Cargo's tracked rustflags, as rustc-private tool builds do.
        for search_path in [&self.host_dir, &self.target_dir] {
            cargo.rustflag(&format!("-Lall={}", search_path.to_str().unwrap()));
        }
    }
}

// Trust: exercise the check-specific Cargo configuration and flag serialization.
#[cfg(test)]
mod tests;

/// Checks rustc using the given `build_compiler` for the given `target`, and produces
/// a sysroot in the build directory that stores the generated .rmeta files.
///
/// This step exists so that we can store the generated .rmeta artifacts into a separate
/// directory, instead of copying them into the sysroot of `build_compiler`, which would
/// "pollute" it (that is especially problematic for the external stage0 rustc).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct PrepareRustcRmetaSysroot {
    build_compiler: CompilerForCheck,
    target: TargetSelection,
}

impl PrepareRustcRmetaSysroot {
    fn new(build_compiler: CompilerForCheck, target: TargetSelection) -> Self {
        Self { build_compiler, target }
    }
}

impl Step for PrepareRustcRmetaSysroot {
    type Output = RmetaSysroot;

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        // Check rustc
        let stamp = Rustc::check_rustc_for_preparing_sysroot(builder, &self);

        let build_compiler = self.build_compiler.build_compiler();

        // Copy the generated rmeta artifacts to a separate directory
        let dir = builder
            .config
            .out
            .join(build_compiler.host)
            .join(format!("stage{}-rustc-rmeta-artifacts", build_compiler.stage + 1));
        RmetaSysroot::from_stamp(builder, stamp, self.target, &dir)
    }
}

/// Checks std using the given `build_compiler` for the given `target`, and produces
/// a sysroot in the build directory that stores the generated .rmeta files.
///
/// This step exists so that we can store the generated .rmeta artifacts into a separate
/// directory, instead of copying them into the sysroot of `build_compiler`, which would
/// "pollute" it (that is especially problematic for the external stage0 rustc).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct PrepareStdRmetaSysroot {
    build_compiler: Compiler,
    target: TargetSelection,
}

impl PrepareStdRmetaSysroot {
    fn new(build_compiler: Compiler, target: TargetSelection) -> Self {
        Self { build_compiler, target }
    }
}

impl Step for PrepareStdRmetaSysroot {
    type Output = RmetaSysroot;

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        // Check std
        let stamp = builder.ensure(Std {
            build_compiler: self.build_compiler,
            target: self.target,
            crates: vec![],
        });

        // Copy the generated rmeta artifacts to a separate directory
        let dir = builder
            .config
            .out
            .join(self.build_compiler.host)
            .join(format!("stage{}-std-rmeta-artifacts", self.build_compiler.stage));

        RmetaSysroot::from_stamp(builder, stamp, self.target, &dir)
    }
}

/// Checks rustc using `build_compiler`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Rustc {
    check_kind: CheckKind,

    /// Compiler that will check this rustc.
    build_compiler: CompilerForCheck,
    target: TargetSelection,

    /// Whether to build only a subset of crates.
    ///
    /// This shouldn't be used from other steps; see the comment on [`compile::Rustc`].
    ///
    /// [`compile::Rustc`]: crate::core::build_steps::compile::Rustc
    crates: Vec<String>,
}

impl Rustc {
    // Trust: the native repository workflow checks the same complete compiler
    // crate set as `check compiler --all-targets`, within the existing graph.
    pub(crate) fn ensure_repo_check(builder: &Builder<'_>, target: TargetSelection) {
        let crates = builder
            .in_tree_crates("rustc-main", Some(target))
            .into_iter()
            .map(|krate| krate.name.to_string())
            .collect();
        builder.ensure(Self {
            check_kind: CheckKind::Check,
            build_compiler: prepare_compiler_for_check(builder, target, Mode::Rustc),
            target,
            crates,
        });
    }

    fn check_rustc_for_preparing_sysroot(
        builder: &Builder<'_>,
        prepare: &PrepareRustcRmetaSysroot,
    ) -> BuildStamp {
        builder.ensure(Rustc {
            // We specifically want `cargo check`, not the current bootstrap subcommand.
            check_kind: CheckKind::Check,
            build_compiler: prepare.build_compiler.clone(),
            target: prepare.target,
            crates: vec![],
        })
    }
}

impl CommandLineStep for Rustc {
    type Output = BuildStamp;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.crate_or_deps("rustc-main").path("compiler")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        let check_kind = match run.builder.kind {
            Kind::Check => CheckKind::Check,
            Kind::Fix => CheckKind::Fix,
            kind => panic!("unexpected kind for `check::Rustc`: {kind:?}"),
        };

        let target = run.target;
        let build_compiler = prepare_compiler_for_check(run.builder, target, Mode::Rustc);
        let crates = run.make_run_crates(Alias::Compiler);

        run.builder.ensure(Rustc { check_kind, build_compiler, target, crates });
    }

    /// Check the compiler.
    ///
    /// This will check the compiler for a particular stage of the build using
    /// the `compiler` targeting the `target` architecture. The artifacts
    /// created will also be linked into the sysroot directory.
    ///
    /// If we check a stage 2 compiler, we will have to first build a stage 1 compiler to check it.
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let build_compiler = self.build_compiler.build_compiler;
        let target = self.target;

        let mut cargo = builder::Cargo::new(
            builder,
            build_compiler,
            Mode::Rustc,
            SourceType::InTree,
            target,
            self.check_kind.to_kind(),
        );

        rustc_cargo(builder, &mut cargo, target, &build_compiler, &self.crates);
        self.build_compiler.configure_cargo(&mut cargo);

        // Explicitly pass -p for all compiler crates, so cargo checks each
        // named crate rather than just the leaf.
        for krate in &*self.crates {
            cargo.arg("-p").arg(krate);
        }
        // When we run `x check compiler --all-targets`, then the `Rustc` step is executed in
        // two "modes" - one with all in-tree rustc crates, and a second time with empty crates
        // in `PrepareRustcRmetaSysroot`, to prepare .rmeta files for RustcPrivate tools.
        // If we use `--all-targets` for both, then we will end up with a duplicated .rmeta file
        // in the sysroot, which breaks everything.
        // So we only use `--all-targets` for the default case where crates are empty.
        // This will also be used when someone does `x check compiler/<rustc-crate>`.
        if !self.crates.is_empty() && builder.sess.config.cmd.check_all_targets() {
            cargo.arg("--all-targets");
        }

        // Trust: `-p` alone does NOT reach test targets. The comment this
        // replaced claimed it did ("this will force cargo to also check the
        // tests/benches/examples"), and that claim was false: `cargo check -p
        // foo` checks foo's lib and bins, never its `#[cfg(test)]` module.
        // Measured — with a deliberate `let _: u32 = "not a u32";` planted in
        // `rustc_mir_transform`'s test module, `x.py check --stage 1
        // compiler/rustc_mir_transform` exited 0 and reported no error.
        //
        // That is why the trust_verify test target silently rotted through six
        // separate signature changes: `x.py build` compiles only the lib, and
        // `x.py check` was believed to cover the rest. `--tests` is what
        // actually reaches them. (Deliberately not `--all-targets`, which the
        // tool path uses — that also drags in benches and examples, a surface
        // this repo has never kept green.)
        cargo.arg("--tests");

        let _guard = builder.msg(
            self.check_kind.to_kind(),
            format_args!("compiler artifacts{}", crate_description(&self.crates)),
            Mode::Rustc,
            self.build_compiler.build_compiler(),
            target,
        );

        let stamp =
            build_stamp::librustc_stamp(builder, build_compiler, target).with_prefix("check");

        run_cargo(
            builder,
            cargo,
            builder.config.free_args.clone(),
            &stamp,
            vec![],
            ArtifactKeepMode::OnlyRmeta,
        );

        stamp
    }

    fn metadata(&self) -> Option<StepMetadata> {
        let mut metadata = StepMetadata::new("rustc", self.target, self.check_kind.to_kind())
            .built_by(self.build_compiler.build_compiler());
        if !self.crates.is_empty() {
            metadata = metadata.with_metadata(format!("({} crates)", self.crates.len()));
        }
        Some(metadata)
    }
}

/// Represents a compiler that can check something.
///
/// If the compiler was created for `Mode::ToolRustcPrivate` or `Mode::Codegen`, it will also contain
/// .rmeta artifacts from rustc that was already checked using `build_compiler`.
///
/// All steps that use this struct in a "general way" (i.e. they don't know exactly what kind of
/// thing is being built) should call `configure_cargo` to ensure that the rmeta artifacts are
/// properly linked, if present.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompilerForCheck {
    build_compiler: Compiler,
    rustc_rmeta_sysroot: Option<RmetaSysroot>,
    std_rmeta_sysroot: Option<RmetaSysroot>,
}

impl CompilerForCheck {
    pub fn build_compiler(&self) -> Compiler {
        self.build_compiler
    }

    /// If there are any rustc rmeta artifacts available, configure the Cargo invocation
    /// so that the artifact being built can find them.
    pub fn configure_cargo(&self, cargo: &mut Cargo) {
        if let Some(sysroot) = &self.rustc_rmeta_sysroot {
            sysroot.configure_cargo(cargo);
        }
        if let Some(sysroot) = &self.std_rmeta_sysroot {
            sysroot.configure_cargo(cargo);
        }
    }
}

/// Prepare the standard library for checking something (that requires stdlib) using
/// `build_compiler`.
fn prepare_std(
    builder: &Builder<'_>,
    build_compiler: Compiler,
    target: TargetSelection,
) -> Option<RmetaSysroot> {
    // We need to build the host stdlib even if we only check, to compile build scripts and proc
    // macros
    builder.std(build_compiler, builder.host_target);

    // If we're cross-compiling, we generate the rmeta files for the given target
    // This check has to be here, because if we generate both .so and .rmeta files, rustc will fail,
    // as it will have multiple candidates for linking.
    if builder.host_target != target {
        Some(builder.ensure(PrepareStdRmetaSysroot::new(build_compiler, target)))
    } else {
        None
    }
}

/// Prepares a compiler that will check something with the given `mode`.
pub fn prepare_compiler_for_check(
    builder: &Builder<'_>,
    target: TargetSelection,
    mode: Mode,
) -> CompilerForCheck {
    prepare_compiler_for_check_with_minimum_stage(builder, target, mode, 0)
}

// Trust: some rustc-private tools require APIs absent from the pinned bootstrap
// std. Check them with a locally built compiler and its own std/rustc metadata;
// never substitute an ambient SDK or remove targets from their Cargo check.
fn prepare_compiler_for_check_with_minimum_stage(
    builder: &Builder<'_>,
    target: TargetSelection,
    mode: Mode,
    minimum_compiler_stage: u32,
) -> CompilerForCheck {
    let host = builder.host_target;

    let mut rustc_rmeta_sysroot = None;
    let mut std_rmeta_sysroot = None;
    let build_compiler = match mode {
        Mode::ToolBootstrap => builder.compiler(0, host),
        // We could also only check std here and use `prepare_std`, but `ToolTarget` is currently
        // only used for running in-tree Clippy on bootstrap tools, so it does not seem worth it to
        // optimize it. Therefore, here we build std for the target, instead of just checking it.
        Mode::ToolTarget => get_tool_target_compiler(builder, ToolTargetBuildMode::Build(target)),
        Mode::ToolStd => {
            if builder.config.compile_time_deps {
                // When --compile-time-deps is passed, we can't use any rustc
                // other than the bootstrap compiler. Luckily build scripts and
                // proc macros for tools are unlikely to need nightly.
                builder.compiler(0, host)
            } else {
                // These tools require the local standard library to be checked
                let build_compiler = builder.compiler(builder.top_stage, host);
                std_rmeta_sysroot = prepare_std(builder, build_compiler, target);
                build_compiler
            }
        }
        Mode::ToolRustcPrivate | Mode::Codegen => {
            // Check Rustc to produce the required rmeta artifacts for rustc_private, and then
            // return the build compiler that was used to check rustc.
            // We do not need to check examples/tests/etc. of Rustc for rustc_private, so we pass
            // an empty set of crates, which will avoid using `cargo -p`.
            // Trust: the tool and every private crate must use the same compiler.
            let compiler_for_rustc = prepare_compiler_for_check_with_minimum_stage(
                builder,
                target,
                Mode::Rustc,
                minimum_compiler_stage,
            );
            rustc_rmeta_sysroot = Some(
                builder.ensure(PrepareRustcRmetaSysroot::new(compiler_for_rustc.clone(), target)),
            );
            let build_compiler = compiler_for_rustc.build_compiler();

            // To check a rustc_private tool, we also need to check std that it will link to
            std_rmeta_sysroot = prepare_std(builder, build_compiler, target);
            build_compiler
        }
        Mode::Rustc => {
            // This is a horrible hack, because we actually change the compiler stage numbering
            // here. If you do `x check --stage 1 --host FOO`, we build stage 1 host rustc,
            // and use that to check stage 1 FOO rustc (which actually makes that stage 2 FOO
            // rustc).
            //
            // FIXME: remove this and either fix cross-compilation check on stage 2 (which has a
            // myriad of other problems) or disable cross-checking on stage 1.
            // Trust: keep stage zero unsupported, including for tools with a floor.
            assert!(builder.top_stage > 0, "checking rustc requires stage >= 1");
            let stage = if host == target { builder.top_stage - 1 } else { builder.top_stage };
            // Trust: a tool can require the current std without changing other checks.
            let build_compiler = builder.compiler(stage.max(minimum_compiler_stage), host);

            // To check rustc, we need to check std that it will link to
            std_rmeta_sysroot = prepare_std(builder, build_compiler, target);
            build_compiler
        }
        Mode::Std => {
            // When checking std stage N, we want to do it with the stage N compiler
            // Note: we don't need to build the host stdlib here, because when compiling std, the
            // stage 0 stdlib is used to compile build scripts and proc macros.
            builder.compiler(builder.top_stage, host)
        }
    };
    CompilerForCheck { build_compiler, rustc_rmeta_sysroot, std_rmeta_sysroot }
}

macro_rules! tool_check_step {
    (
        $name:ident {
            // The part of this path after the final '/' is also used as a display name.
            path: $path:literal
            $(, alt_path: $alt_path:literal )*
            // `Mode` to use when checking this tool
            , mode: $mode:expr
            // Subset of nightly features that are allowed to be used when checking
            $(, allow_features: $allow_features:expr )?
            // Features that should be enabled when checking
            $(, enable_features: [$($enable_features:expr),*] )?
            $(, default_features: $default_features:expr )?
            $(, default: $default:literal )?
            // Trust: minimum compiler that can supply this tool's host std APIs.
            $(, minimum_compiler_stage: $minimum_compiler_stage:expr )?
            $( , )?
        }
    ) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub struct $name {
            compiler: CompilerForCheck,
            target: TargetSelection,
        }

        impl CommandLineStep for $name {
            type Output = ();
            const IS_HOST: bool = true;

            fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
                run.multi_path(&[$path $(, $alt_path )*])
            }

            fn is_default_step(_builder: &Builder<'_>) -> bool {
                // Most of the tool-checks using this macro are run by default.
                true $( && const { $default } )?
            }

            fn make_run(run: RunConfig<'_>) {
                let target = run.target;
                let mode: Mode = $mode;

                // Trust: keep all targets checked against one coherent local toolchain.
                let minimum_compiler_stage = 0 $(.max($minimum_compiler_stage))?;
                let compiler = prepare_compiler_for_check_with_minimum_stage(
                    run.builder, target, mode, minimum_compiler_stage,
                );

                // It doesn't make sense to cross-check bootstrap tools
                if mode == Mode::ToolBootstrap && target != run.builder.host_target {
                    println!("WARNING: not checking bootstrap tool {} for target {target} as it is a bootstrap (host-only) tool", stringify!($path));
                    return;
                };

                run.builder.ensure($name { target, compiler });
            }

            fn run(self, builder: &Builder<'_>) {
                let Self { target, compiler } = self;
                let allow_features = {
                    let mut _value = "";
                    $( _value = $allow_features; )?
                    _value
                };
                let extra_features: &[&str] = &[$($($enable_features),*)?];
                let default_features = {
                    let mut _value = true;
                    $( _value = $default_features; )?
                    _value
                };
                let mode: Mode = $mode;
                run_tool_check_step(builder, compiler, target, $path, mode, allow_features, extra_features, default_features);
            }

            fn metadata(&self) -> Option<StepMetadata> {
                Some(StepMetadata::check(stringify!($name), self.target).built_by(self.compiler.build_compiler))
            }
        }
    }
}

// Trust: a full Rustc build links its artifacts into the build compiler's
// sysroot. Check artifacts have different crate hashes, so private tool checks
// must read std from an isolated copy and rustc only from their checked rmetas.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ToolCheckSysroot {
    compiler: Compiler,
}

impl Step for ToolCheckSysroot {
    type Output = PathBuf;

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let source = builder.sysroot(self.compiler);
        let destination = builder
            .out
            .join(self.compiler.host)
            .join(format!("stage{}-tool-check-sysroot", self.compiler.stage));
        copy_tool_check_sysroot(builder, &source, &destination);
        destination
    }
}

// Trust: never mutate the build compiler's sysroot or follow its source aliases.
fn copy_tool_check_sysroot(
    session: &crate::core::session::Session,
    source: &Path,
    destination: &Path,
) {
    if session.config.dry_run() {
        return;
    }
    match fs::remove_dir_all(destination) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            panic!("failed to replace tool-check sysroot {}: {error}", destination.display())
        }
    }
    t!(fs::create_dir_all(destination.join("lib")));
    session.cp_link_filtered(&source.join("lib"), &destination.join("lib"), &|path| {
        path != Path::new("rustlib/src")
            && path != Path::new("rustlib/rustc-src")
            && !crate::core::build_steps::compile::is_rustc_private_artifact(path)
    });
}

// Trust: the explicit flag also reaches direct probes and Cargo's fingerprints.
fn configure_tool_check_sysroot(cargo: &mut Cargo, sysroot: &Path) {
    cargo.env("RUSTC_SYSROOT", sysroot);
    cargo.rustflag("--sysroot");
    cargo.rustflag(sysroot.to_str().unwrap());
}

/// Used by the implementation of `Step::run` in `tool_check_step!`.
#[allow(clippy::too_many_arguments)]
fn run_tool_check_step(
    builder: &Builder<'_>,
    compiler: CompilerForCheck,
    target: TargetSelection,
    path: &str,
    mode: Mode,
    allow_features: &str,
    extra_features: &[&str],
    default_features: bool,
) {
    let display_name = path.rsplit('/').next().unwrap();

    let build_compiler = compiler.build_compiler();

    let extra_features = extra_features.iter().map(|f| f.to_string()).collect::<Vec<String>>();
    let mut cargo = prepare_tool_cargo(
        builder,
        build_compiler,
        mode,
        target,
        builder.kind,
        path,
        // Currently, all of the tools that use this macro/function are in-tree.
        // If support for out-of-tree tools is re-added in the future, those
        // steps should probably be marked non-default, so that a tool that
        // happens to be broken cannot fail the default checks.
        SourceType::InTree,
        &extra_features,
    );
    cargo.allow_features(allow_features);
    compiler.configure_cargo(&mut cargo);
    // Trust: prevent full-build rustc metadata from competing with check metadata.
    if mode == Mode::ToolRustcPrivate {
        let sysroot = builder.ensure(ToolCheckSysroot { compiler: build_compiler });
        configure_tool_check_sysroot(&mut cargo, &sysroot);
    }

    // FIXME: check bootstrap doesn't currently work when multiple targets are checked
    // FIXME: rust-analyzer does not work with --all-targets
    if display_name == "rust-analyzer" {
        cargo.arg("--bins");
        cargo.arg("--tests");
        cargo.arg("--benches");
    } else {
        cargo.arg("--all-targets");
    }

    if !default_features {
        cargo.arg("--no-default-features");
    }

    // Trust: this must match prepare_tool_cargo's actual selected generation.
    let stamp = BuildStamp::new(&builder.cargo_out_for_input(
        build_compiler,
        mode,
        target,
        builder.cargo_input(mode),
    ))
    .with_prefix(&format!("{display_name}-check"));

    let _guard = builder.msg(builder.kind, display_name, mode, build_compiler, target);
    run_cargo(
        builder,
        cargo,
        builder.config.free_args.clone(),
        &stamp,
        vec![],
        ArtifactKeepMode::OnlyRmeta,
    );
}

tool_check_step!(Rustdoc {
    path: "src/tools/trustdoc",
    alt_path: "src/librustdoc",
    mode: Mode::ToolRustcPrivate
});
// Clippy, miri and Rustfmt are hybrids. They are external tools, but use a git subtree instead
// of a submodule. Since the SourceType only drives the deny-warnings
// behavior, treat it as in-tree so that any new warnings in clippy will be
// rejected.
tool_check_step!(Clippy { path: "src/tools/tippy", mode: Mode::ToolRustcPrivate });
// Trust: the trust-ir → trust-cg self-host backend, a sibling-repo crate
// (build_steps/trust_ir_cg.rs). Not a default check step: it is built only when
// `rust.codegen-backends` lists "trust-ir-cg", and a sibling checkout mid-sync
// must not be able to fail `x check` for everyone. Select it explicitly:
// `x check first-party/trust-cg/crates/rustc-codegen-trust-cg`.
tool_check_step!(TrustIrCgBackend {
    path: "first-party/trust-cg/crates/rustc-codegen-trust-cg",
    mode: Mode::ToolRustcPrivate,
    default: false,
});
tool_check_step!(Miri {
    path: "src/tools/miri",
    // Trust: preserve the explicit debugger path after its package joined Miri.
    alt_path: "src/tools/miri/priroda",
    mode: Mode::ToolRustcPrivate,
    enable_features: ["check_only", "priroda"],
    // Trust: Miri and its Priroda binary require host APIs absent from the seed.
    // Keep all targets checked with the locally built compiler and matching std.
    minimum_compiler_stage: 1,
});
tool_check_step!(CargoMiri { path: "src/tools/miri/cargo-miri", mode: Mode::ToolRustcPrivate });
tool_check_step!(Rustfmt { path: "src/tools/trustfmt", mode: Mode::ToolRustcPrivate });
tool_check_step!(RustAnalyzer {
    path: "src/tools/rust-analyzer",
    mode: Mode::ToolRustcPrivate,
    allow_features: tool::RustAnalyzer::ALLOW_FEATURES,
    enable_features: ["in-rust-tree"],
});
tool_check_step!(MiroptTestTools {
    path: "src/tools/miropt-test-tools",
    mode: Mode::ToolBootstrap
});
// We want to test the local std
tool_check_step!(TestFloatParse {
    path: "src/tools/test-float-parse",
    mode: Mode::ToolStd,
    allow_features: TEST_FLOAT_PARSE_ALLOW_FEATURES
});
tool_check_step!(FeaturesStatusDump {
    path: "src/tools/features-status-dump",
    mode: Mode::ToolBootstrap
});

// Trust: `--all-targets` includes Bootstrap's library test target, and Bootstrap links the
// native controller client, so this allows what its test build allows
// (test::BOOTSTRAP_SELF_ALLOW_FEATURES).
tool_check_step!(Bootstrap {
    path: "src/bootstrap",
    mode: Mode::ToolBootstrap,
    allow_features: super::test::BOOTSTRAP_SELF_ALLOW_FEATURES,
    default: false
});

// `run-make-support` will be built as part of suitable run-make compiletest test steps, but support
// check to make it easier to work on.
tool_check_step!(RunMakeSupport {
    path: "src/tools/run-make-support",
    mode: Mode::ToolBootstrap,
    default: false
});

tool_check_step!(CoverageDump {
    path: "src/tools/coverage-dump",
    mode: Mode::ToolBootstrap,
    default: false
});

// Compiletest is implicitly "checked" when it gets built in order to run tests,
// so this is mainly for people working on compiletest to run locally.
tool_check_step!(Compiletest {
    path: "src/tools/compiletest",
    mode: Mode::ToolBootstrap,
    // Trust: `--all-targets` compiles the library test target, as its test build does.
    allow_features: tool::COMPILETEST_SELF_ALLOW_FEATURES,
    default: false,
});

// As with compiletest, rustdoc-gui-test is automatically built when running
// relevant tests. So being able to check it is mainly useful for people
// working on on rustdoc-gui-test itself, or on its compiletest dependency.
tool_check_step!(RustdocGuiTest {
    path: "src/tools/rustdoc-gui-test",
    mode: Mode::ToolBootstrap,
    // Trust: it links compiletest's library, which carries the native query transport.
    allow_features: tool::COMPILETEST_ALLOW_FEATURES,
    default: false,
});

tool_check_step!(Linkchecker {
    path: "src/tools/linkchecker",
    mode: Mode::ToolBootstrap,
    default: false
});

tool_check_step!(BumpStage0 {
    path: "src/tools/bump-stage0",
    mode: Mode::ToolBootstrap,
    default: false
});

// Tidy is implicitly checked when `./x test tidy` is executed
// (if you set a pre-push hook, the command is called).
// So this is mainly for people working on tidy.
tool_check_step!(Tidy { path: "src/tools/tidy", mode: Mode::ToolBootstrap, default: false });
