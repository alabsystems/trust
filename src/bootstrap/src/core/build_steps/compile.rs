//! Implementation of compiling various phases of the compiler and standard
//! library.
//!
//! This module contains some of the real meat in the bootstrap build system
//! which is where Cargo is used to compile the standard library, libtest, and
//! the compiler. This module is also responsible for assembling the sysroot as it
//! goes along from the output of the previous stage.

use std::borrow::Cow;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::ffi::{OsStr, OsString};
use std::hash::{Hash, Hasher};
use std::io::BufReader;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::time::SystemTime;
use std::{env, fs, str};

use serde_derive::Deserialize;
use sha2::Digest;
#[cfg(feature = "tracing")]
use tracing::span;

use crate::core::build_steps::tool::{SourceType, copy_lld_artifacts};
use crate::core::build_steps::{dist, llvm};
use crate::core::builder;
use crate::core::builder::{
    Builder, Cargo, Kind, RunConfig, ShouldRun, Step, StepMetadata, crate_description,
};
use crate::core::config::toml::target::DefaultLinuxLinkerOverride;
use crate::core::config::{
    CompilerBuiltins, DebuginfoLevel, LlvmLibunwind, RustcLto, TargetSelection,
};
use crate::utils::build_stamp;
use crate::utils::build_stamp::BuildStamp;
use crate::utils::exec::command;
use crate::utils::helpers::{
    dylib_path_var, exe, get_clang_cl_resource_dir, hex_encode, is_debug_info, is_dylib,
    symlink_dir, t, up_to_date,
};
use crate::{
    CLang, CodegenBackendKind, Compiler, DependencyType, FileType, GitRepo, LLVM_TOOLS, Mode,
    debug, trace,
};

/// Build a standard library for the given `target` using the given `build_compiler`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Std {
    pub target: TargetSelection,
    /// Compiler that builds the standard library.
    pub build_compiler: Compiler,
    /// Whether to build only a subset of crates in the standard library.
    ///
    /// This shouldn't be used from other steps; see the comment on [`Rustc`].
    crates: Vec<String>,
    /// When using download-rustc, we need to use a new build of `std` for running unit tests of Std itself,
    /// but we need to use the downloaded copy of std for linking to rustdoc. Allow this to be overridden by `builder.ensure` from other steps.
    force_recompile: bool,
    is_for_mir_opt_tests: bool,
    /// Whether this build step should also link its output into the compiler
    /// sysroot. `Assemble` disables the implicit link so it can install the
    /// selected (possibly uplifted) stamp into the newly assembled sysroot
    /// exactly once.
    link_into_sysroot: bool,
}

impl Std {
    pub fn new(build_compiler: Compiler, target: TargetSelection) -> Self {
        Self {
            target,
            build_compiler,
            crates: Default::default(),
            force_recompile: false,
            is_for_mir_opt_tests: false,
            link_into_sysroot: true,
        }
    }

    pub fn force_recompile(mut self, force_recompile: bool) -> Self {
        self.force_recompile = force_recompile;
        self
    }

    #[expect(clippy::wrong_self_convention)]
    pub fn is_for_mir_opt_tests(mut self, is_for_mir_opt_tests: bool) -> Self {
        self.is_for_mir_opt_tests = is_for_mir_opt_tests;
        self
    }

    pub fn without_sysroot_link(mut self) -> Self {
        self.link_into_sysroot = false;
        self
    }

    fn copy_extra_objects(
        &self,
        builder: &Builder<'_>,
        compiler: &Compiler,
        target: TargetSelection,
    ) -> Vec<(PathBuf, DependencyType)> {
        let mut deps = Vec::new();
        if !self.is_for_mir_opt_tests {
            deps.extend(copy_third_party_objects(builder, compiler, target));
            deps.extend(copy_self_contained_objects(builder, compiler, target));
        }
        deps
    }

    /// Returns true if the standard library should be uplifted from stage 1.
    ///
    /// Uplifting is enabled if we're building a stage2+ libstd and full bootstrap is
    /// disabled.
    pub fn should_be_uplifted_from_stage_1(builder: &Builder<'_>, stage: u32) -> bool {
        stage > 1 && !builder.config.full_bootstrap
    }
}

impl Step for Std {
    /// Build stamp of std, if it was indeed built or uplifted.
    type Output = Option<BuildStamp>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.crate_or_deps("sysroot").path("library")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        let crates = std_crates_for_run_make(&run);
        let builder = run.builder;

        // Force compilation of the standard library from source if the `library` is modified. This allows
        // library team to compile the standard library without needing to compile the compiler with
        // the `rust.download-rustc=true` option.
        let force_recompile = builder.rust_info().is_managed_git_subrepository()
            && builder.download_rustc()
            && builder.config.has_changes_from_upstream(&["library"]);

        trace!("is managed git repo: {}", builder.rust_info().is_managed_git_subrepository());
        trace!("download_rustc: {}", builder.download_rustc());
        trace!(force_recompile);

        run.builder.ensure(Std {
            // Note: we don't use compiler_for_std here, so that `x build library --stage 2`
            // builds a stage2 rustc.
            build_compiler: run.builder.compiler(run.builder.top_stage, builder.host_target),
            target: run.target,
            crates,
            force_recompile,
            is_for_mir_opt_tests: false,
            link_into_sysroot: true,
        });
    }

    /// Builds the standard library.
    ///
    /// This will build the standard library for a particular stage of the build
    /// using the `compiler` targeting the `target` architecture. The artifacts
    /// created will also be linked into the sysroot directory.
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let target = self.target;

        // In most cases, we already have the std ready to be used for stage 0.
        // However, if we are doing a local rebuild (so the build compiler can compile the standard
        // library even on stage 0), and we're cross-compiling (so the stage0 standard library for
        // *target* is not available), we still allow the stdlib to be built here.
        if self.build_compiler.stage == 0
            && !(builder.local_rebuild && target != builder.host_target)
        {
            let compiler = self.build_compiler;
            if self.link_into_sysroot {
                builder.ensure(StdLink::from_std(self, compiler));
            }

            return None;
        }

        let build_compiler = if builder.download_rustc() && self.force_recompile {
            // When there are changes in the library tree with CI-rustc, we want to build
            // the stageN library and that requires using stageN-1 compiler.
            builder
                .compiler(self.build_compiler.stage.saturating_sub(1), builder.config.host_target)
        } else {
            self.build_compiler
        };

        // When using `download-rustc`, we already have artifacts for the host available. Don't
        // recompile them.
        if builder.download_rustc()
            && builder.config.is_host_target(target)
            && !self.force_recompile
        {
            let sysroot =
                builder.ensure(Sysroot { compiler: build_compiler, force_recompile: false });
            cp_rustc_component_to_ci_sysroot(
                builder,
                &sysroot,
                builder.config.ci_rust_std_contents(),
            );
            return None;
        }

        if builder.config.keep_stage.contains(&build_compiler.stage)
            || builder.config.keep_stage_std.contains(&build_compiler.stage)
        {
            trace!(keep_stage = ?builder.config.keep_stage);
            trace!(keep_stage_std = ?builder.config.keep_stage_std);

            builder.info("WARNING: Using a potentially old libstd. This may not behave well.");

            builder.ensure(StartupObjects { compiler: build_compiler, target });

            self.copy_extra_objects(builder, &build_compiler, target);

            if self.link_into_sysroot {
                builder.ensure(StdLink::from_std(self, build_compiler));
            }
            return Some(build_stamp::libstd_stamp(builder, build_compiler, target));
        }

        if !self.is_for_mir_opt_tests
            && staged_narrow_trust_cg_cannot_self_host(
                build_compiler.stage,
                builder.local_rebuild,
                builder.config.default_codegen_backend(build_compiler.host),
            )
        {
            reject_narrow_trust_cg_self_host("the standard library");
        }

        let mut target_deps = builder.ensure(StartupObjects { compiler: build_compiler, target });

        // Stage of the stdlib that we're building
        let stage = build_compiler.stage;

        if Self::should_be_uplifted_from_stage_1(builder, build_compiler.stage) {
            let build_compiler_for_std_to_uplift = builder.compiler(1, builder.host_target);
            let stage_1_stamp = builder.std(build_compiler_for_std_to_uplift, target);

            let msg = if build_compiler_for_std_to_uplift.host == target {
                format!(
                    "Uplifting library (stage{} -> stage{stage})",
                    build_compiler_for_std_to_uplift.stage
                )
            } else {
                format!(
                    "Uplifting library (stage{}:{} -> stage{stage}:{target})",
                    build_compiler_for_std_to_uplift.stage, build_compiler_for_std_to_uplift.host,
                )
            };

            builder.info(&msg);

            // Even if we're not building std this stage, the new sysroot must
            // still contain the third party objects needed by various targets.
            self.copy_extra_objects(builder, &build_compiler, target);

            if self.link_into_sysroot {
                builder.ensure(StdLink::from_std(self, build_compiler_for_std_to_uplift));
            }
            return stage_1_stamp;
        }

        target_deps.extend(self.copy_extra_objects(builder, &build_compiler, target));

        // We build a sysroot for mir-opt tests using the same trick that Miri does: A check build
        // with -Zalways-encode-mir. This frees us from the need to have a target linker, and the
        // fact that this is a check build integrates nicely with run_cargo.
        let mut cargo = if self.is_for_mir_opt_tests {
            trace!("building special sysroot for mir-opt tests");
            let mut cargo = builder::Cargo::new_for_mir_opt_tests(
                builder,
                build_compiler,
                Mode::Std,
                SourceType::InTree,
                target,
                Kind::Check,
            );
            cargo.rustflag("-Zalways-encode-mir");
            cargo.arg("--manifest-path").arg(builder.src.join("library/sysroot/Cargo.toml"));
            cargo
        } else {
            trace!("building regular sysroot");
            let mut cargo = builder::Cargo::new(
                builder,
                build_compiler,
                Mode::Std,
                SourceType::InTree,
                target,
                Kind::Build,
            );
            std_cargo(builder, target, &mut cargo, &self.crates);
            // Trust (opt-in via `TRUST_STD_ENCODE_MIR=1`): encode MIR for ALL std
            // functions (not just generic/inline ones) so the trust-ir frontend
            // can lower the FULL std dependency closure of a program
            // self-contained (e.g. hashbrown's non-inline RawTableInner::ctrl_slice),
            // instead of leaving them as MIR-unavailable link leaves. Additive
            // metadata only — the compiled std object code is byte-identical, so
            // linking/binaries are unaffected; it only enlarges the rlib metadata
            // and is therefore OFF by default (no cost to ordinary builds).
            if std::env::var_os("TRUST_STD_ENCODE_MIR").is_some() {
                cargo.rustflag("-Zalways-encode-mir");
            }
            cargo
        };

        // See src/bootstrap/synthetic_targets.rs
        if target.is_synthetic() {
            cargo.env("RUSTC_BOOTSTRAP_SYNTHETIC_TARGET", "1");
        }
        let _guard = builder.msg(
            Kind::Build,
            format_args!("library artifacts{}", crate_description(&self.crates)),
            Mode::Std,
            build_compiler,
            target,
        );

        let stamp = build_stamp::libstd_stamp(builder, build_compiler, target);
        run_cargo(
            builder,
            cargo,
            vec![],
            &stamp,
            target_deps,
            if self.is_for_mir_opt_tests {
                ArtifactKeepMode::OnlyRmeta
            } else {
                // We use -Zno-embed-metadata for the standard library
                ArtifactKeepMode::BothRlibAndRmeta
            },
        );

        if self.link_into_sysroot {
            builder.ensure(StdLink::from_std(
                self,
                builder.compiler(build_compiler.stage, builder.config.host_target),
            ));
        }
        Some(stamp)
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("std", self.target).built_by(self.build_compiler))
    }
}

fn copy_and_stamp(
    builder: &Builder<'_>,
    libdir: &Path,
    sourcedir: &Path,
    name: &str,
    target_deps: &mut Vec<(PathBuf, DependencyType)>,
    dependency_type: DependencyType,
) {
    let target = libdir.join(name);
    builder.copy_link(&sourcedir.join(name), &target, FileType::Regular);

    target_deps.push((target, dependency_type));
}

fn copy_llvm_libunwind(builder: &Builder<'_>, target: TargetSelection, libdir: &Path) -> PathBuf {
    let libunwind_path = builder.ensure(llvm::Libunwind { target });
    let libunwind_source = libunwind_path.join("libunwind.a");
    let libunwind_target = libdir.join("libunwind.a");
    builder.copy_link(&libunwind_source, &libunwind_target, FileType::NativeLibrary);
    libunwind_target
}

/// Copies third party objects needed by various targets.
fn copy_third_party_objects(
    builder: &Builder<'_>,
    compiler: &Compiler,
    target: TargetSelection,
) -> Vec<(PathBuf, DependencyType)> {
    let mut target_deps = vec![];

    if builder.config.needs_sanitizer_runtime_built(target) && compiler.stage != 0 {
        // The sanitizers are only copied in stage1 or above,
        // to avoid creating dependency on LLVM.
        target_deps.extend(
            copy_sanitizers(builder, compiler, target)
                .into_iter()
                .map(|d| (d, DependencyType::Target)),
        );
    }

    if target == "x86_64-fortanix-unknown-sgx"
        || builder.config.llvm_libunwind(target) == LlvmLibunwind::InTree
            && (target.contains("linux")
                || target.contains("fuchsia")
                || target.contains("aix")
                || target.contains("hexagon"))
    {
        let libunwind_path =
            copy_llvm_libunwind(builder, target, &builder.sysroot_target_libdir(*compiler, target));
        target_deps.push((libunwind_path, DependencyType::Target));
    }

    target_deps
}

/// Copies third party objects needed by various targets for self-contained linkage.
fn copy_self_contained_objects(
    builder: &Builder<'_>,
    compiler: &Compiler,
    target: TargetSelection,
) -> Vec<(PathBuf, DependencyType)> {
    let libdir_self_contained =
        builder.sysroot_target_libdir(*compiler, target).join("self-contained");
    t!(fs::create_dir_all(&libdir_self_contained));
    let mut target_deps = vec![];

    // Copies the libc and CRT objects.
    //
    // rustc historically provides a more self-contained installation for musl targets
    // not requiring the presence of a native musl toolchain. For example, it can fall back
    // to using gcc from a glibc-targeting toolchain for linking.
    // To do that we have to distribute musl startup objects as a part of Rust toolchain
    // and link with them manually in the self-contained mode.
    if target.needs_crt_begin_end() {
        let srcdir = builder.musl_libdir(target).unwrap_or_else(|| {
            panic!("Target {:?} does not have a \"musl-libdir\" key", target.triple)
        });
        if !target.starts_with("wasm32") {
            for &obj in &["libc.a", "crt1.o", "Scrt1.o", "rcrt1.o", "crti.o", "crtn.o"] {
                copy_and_stamp(
                    builder,
                    &libdir_self_contained,
                    &srcdir,
                    obj,
                    &mut target_deps,
                    DependencyType::TargetSelfContained,
                );
            }
            let crt_path = builder.ensure(llvm::CrtBeginEnd { target });
            for &obj in &["crtbegin.o", "crtbeginS.o", "crtend.o", "crtendS.o"] {
                let src = crt_path.join(obj);
                let target = libdir_self_contained.join(obj);
                builder.copy_link(&src, &target, FileType::NativeLibrary);
                target_deps.push((target, DependencyType::TargetSelfContained));
            }
        } else {
            // For wasm32 targets, we need to copy the libc.a and crt1-command.o files from the
            // musl-libdir, but we don't need the other files.
            for &obj in &["libc.a", "crt1-command.o"] {
                copy_and_stamp(
                    builder,
                    &libdir_self_contained,
                    &srcdir,
                    obj,
                    &mut target_deps,
                    DependencyType::TargetSelfContained,
                );
            }
        }
        if !target.starts_with("s390x") {
            let libunwind_path = copy_llvm_libunwind(builder, target, &libdir_self_contained);
            target_deps.push((libunwind_path, DependencyType::TargetSelfContained));
        }
    } else if target.contains("-wasi") {
        let srcdir = builder.wasi_libdir(target).unwrap_or_else(|| {
            panic!(
                "Target {:?} does not have a \"wasi-root\" key in bootstrap.toml \
                    or `$WASI_SDK_PATH` set",
                target.triple
            )
        });

        // wasm32-wasip3 doesn't exist in wasi-libc yet, so instead use libs
        // from the wasm32-wasip2 target. Once wasi-libc supports wasip3 this
        // should be deleted and the native objects should be used.
        let srcdir = if target == "wasm32-wasip3" {
            assert!(!srcdir.exists(), "wasip3 support is in wasi-libc, this should be updated now");
            builder.wasi_libdir(TargetSelection::from_user("wasm32-wasip2")).unwrap()
        } else {
            srcdir
        };
        for &obj in &["libc.a", "crt1-command.o", "crt1-reactor.o"] {
            copy_and_stamp(
                builder,
                &libdir_self_contained,
                &srcdir,
                obj,
                &mut target_deps,
                DependencyType::TargetSelfContained,
            );
        }
        if srcdir.join("eh").exists() {
            copy_and_stamp(
                builder,
                &libdir_self_contained,
                &srcdir.join("eh"),
                "libunwind.a",
                &mut target_deps,
                DependencyType::TargetSelfContained,
            );
        }
    } else if target.is_windows_gnu() || target.is_windows_gnullvm() {
        for obj in ["crt2.o", "dllcrt2.o"].iter() {
            let src = compiler_file(builder, &builder.cc(target), target, CLang::C, obj);
            let dst = libdir_self_contained.join(obj);
            builder.copy_link(&src, &dst, FileType::NativeLibrary);
            target_deps.push((dst, DependencyType::TargetSelfContained));
        }
    }

    target_deps
}

/// Resolves standard library crates for `Std::run_make` for any build kind (like check, doc,
/// build, clippy, etc.).
pub fn std_crates_for_run_make(run: &RunConfig<'_>) -> Vec<String> {
    let mut crates = run.make_run_crates(builder::Alias::Library);

    // For no_std targets, we only want to check core and alloc
    // Regardless of core/alloc being selected explicitly or via the "library" default alias,
    // we only want to keep these two crates.
    // The set of no_std crates should be kept in sync with what `Builder::std_cargo` does.
    // Note: an alternative design would be to return an enum from this function (Default vs Subset)
    // of crates. However, several steps currently pass `-p <package>` even if all crates are
    // selected, because Cargo behaves differently in that case. To keep that behavior without
    // making further changes, we pre-filter the no-std crates here.
    let target_is_no_std = run.builder.no_std(run.target).unwrap_or(false);
    if target_is_no_std {
        crates.retain(|c| c == "core" || c == "alloc");
    }
    crates
}

fn staged_narrow_trust_cg_cannot_self_host(
    compiler_stage: u32,
    local_rebuild: bool,
    compiler_default_backend: &CodegenBackendKind,
) -> bool {
    let effective_stage = if compiler_stage == 0 && local_rebuild { 1 } else { compiler_stage };
    effective_stage != 0 && compiler_default_backend.is_trust_cg()
}

fn narrow_trust_cg_self_host_error(component: &str) -> String {
    format!(
        "cannot build {component} with a staged compiler whose default backend is trust-cg: \
         the builtin Trust-CG adapter currently links only audited rlibs of External \
         scalar-register functions, while std and compiler self-hosting require Internal \
         linkage, statics, and additional crate types. Configure `[rust] \
         codegen-backends = [\"llvm\", \"trust-cg\"]` (LLVM first) for bootstrap, and select \
         trust-cg explicitly only for a supported rlib target"
    )
}

fn reject_narrow_trust_cg_self_host(component: &str) -> ! {
    eprintln!("ERROR: {}", narrow_trust_cg_self_host_error(component));
    crate::exit!(1)
}

/// Tries to find LLVM's `compiler-rt` source directory, for building `library/profiler_builtins`.
///
/// Normally it lives in the `src/llvm-project` submodule, but if we will be using a
/// downloaded copy of CI LLVM, then we try to use the `compiler-rt` sources from
/// there instead, which lets us avoid checking out the LLVM submodule.
fn compiler_rt_for_profiler(builder: &Builder<'_>) -> PathBuf {
    // Try to use `compiler-rt` sources from downloaded CI LLVM, if possible.
    if builder.config.llvm_from_ci {
        // CI LLVM might not have been downloaded yet, so try to download it now.
        builder.config.maybe_download_ci_llvm();
        let ci_llvm_compiler_rt = builder.config.ci_llvm_root().join("compiler-rt");
        if ci_llvm_compiler_rt.exists() {
            return ci_llvm_compiler_rt;
        }
    }

    // Otherwise, fall back to requiring the LLVM submodule.
    builder.require_submodule("src/llvm-project", {
        Some("The `build.profiler` config option requires `compiler-rt` sources from LLVM.")
    });
    builder.src.join("src/llvm-project/compiler-rt")
}

/// Configure cargo to compile the standard library, adding appropriate env vars
/// and such.
pub fn std_cargo(
    builder: &Builder<'_>,
    target: TargetSelection,
    cargo: &mut Cargo,
    crates: &[String],
) {
    // rustc already ensures that it builds with the minimum deployment
    // target, so ideally we shouldn't need to do anything here.
    //
    // However, `cc` currently defaults to a higher version for backwards
    // compatibility, which means that compiler-rt, which is built via
    // compiler-builtins' build script, gets built with a higher deployment
    // target. This in turn causes warnings while linking, and is generally
    // a compatibility hazard.
    //
    // So, at least until https://github.com/rust-lang/cc-rs/issues/1171, or
    // perhaps https://github.com/rust-lang/cargo/issues/13115 is resolved, we
    // explicitly set the deployment target environment variables to avoid
    // this issue.
    //
    // This place also serves as an extension point if we ever wanted to raise
    // rustc's default deployment target while keeping the prebuilt `std` at
    // a lower version, so it's kinda nice to have in any case.
    if target.contains("apple") && !builder.config.dry_run() {
        // Query rustc for the deployment target, and the associated env var.
        // The env var is one of the standard `*_DEPLOYMENT_TARGET` vars, i.e.
        // `MACOSX_DEPLOYMENT_TARGET`, `IPHONEOS_DEPLOYMENT_TARGET`, etc.
        let mut cmd = builder.rustc_cmd(cargo.compiler());
        cmd.arg("--target").arg(target.rustc_target_arg());
        // FIXME(#152709): -Zunstable-options is to handle JSON targets.
        // Remove when JSON targets are stabilized.
        cmd.arg("-Zunstable-options").env("RUSTC_BOOTSTRAP", "1");
        cmd.arg("--print=deployment-target");
        let output = cmd.run_capture_stdout(builder).stdout();

        let (env_var, value) = output.split_once('=').unwrap();
        // Unconditionally set the env var (if it was set in the environment
        // already, rustc should've picked that up).
        cargo.env(env_var.trim(), value.trim());

        // Allow CI to override the deployment target for `std` on macOS.
        //
        // This is useful because we might want the host tooling LLVM, `rustc`
        // and Cargo to have a different deployment target than `std` itself
        // (currently, these two versions are the same, but in the past, we
        // supported macOS 10.7 for user code and macOS 10.8 in host tooling).
        //
        // It is not necessary on the other platforms, since only macOS has
        // support for host tooling.
        if let Some(target) = env::var_os("MACOSX_STD_DEPLOYMENT_TARGET") {
            cargo.env("MACOSX_DEPLOYMENT_TARGET", target);
        }
    }

    // Paths needed by `library/profiler_builtins/build.rs`.
    if let Some(path) = builder.config.profiler_path(target) {
        cargo.env("LLVM_PROFILER_RT_LIB", path);
    } else if builder.config.profiler_enabled(target) {
        let compiler_rt = compiler_rt_for_profiler(builder);
        // Currently this is separate from the env var used by `compiler_builtins`
        // (below) so that adding support for CI LLVM here doesn't risk breaking
        // the compiler builtins. But they could be unified if desired.
        cargo.env("RUST_COMPILER_RT_FOR_PROFILER", compiler_rt);
    }

    // Determine if we're going to compile in optimized C intrinsics to
    // the `compiler-builtins` crate. These intrinsics live in LLVM's
    // `compiler-rt` repository.
    //
    // Note that this shouldn't affect the correctness of `compiler-builtins`,
    // but only its speed. Some intrinsics in C haven't been translated to Rust
    // yet but that's pretty rare. Other intrinsics have optimized
    // implementations in C which have only had slower versions ported to Rust,
    // so we favor the C version where we can, but it's not critical.
    //
    // If `compiler-rt` is available ensure that the `c` feature of the
    // `compiler-builtins` crate is enabled and it's configured to learn where
    // `compiler-rt` is located.
    let compiler_builtins_c_feature = match builder.config.optimized_compiler_builtins(target) {
        CompilerBuiltins::LinkLLVMBuiltinsLib(path) => {
            cargo.env("LLVM_COMPILER_RT_LIB", path);
            " compiler-builtins-c"
        }
        CompilerBuiltins::BuildLLVMFuncs => {
            // NOTE: this interacts strangely with `llvm-has-rust-patches`. In that case, we enforce
            // `submodules = false`, so this is a no-op. But, the user could still decide to
            //  manually use an in-tree submodule.
            //
            // NOTE: if we're using system llvm, we'll end up building a version of `compiler-rt`
            // that doesn't match the LLVM we're linking to. That's probably ok? At least, the
            // difference wasn't enforced before. There's a comment in the compiler_builtins build
            // script that makes me nervous, though:
            // https://github.com/rust-lang/compiler-builtins/blob/31ee4544dbe47903ce771270d6e3bea8654e9e50/build.rs#L575-L579
            builder.require_submodule(
                "src/llvm-project",
                Some(
                    "The `build.optimized-compiler-builtins` config option \
                     requires `compiler-rt` sources from LLVM.",
                ),
            );
            let compiler_builtins_root = builder.src.join("src/llvm-project/compiler-rt");
            if !builder.config.dry_run() {
                // This assertion would otherwise trigger during tests if `llvm-project` is not
                // checked out.
                assert!(compiler_builtins_root.exists());
            }

            // The path to `compiler-rt` is also used by `profiler_builtins` (above),
            // so if you're changing something here please also change that as appropriate.
            cargo.env("RUST_COMPILER_RT_ROOT", &compiler_builtins_root);
            " compiler-builtins-c"
        }
        CompilerBuiltins::BuildRustOnly => "",
    };

    let mut features = String::new();

    if builder.no_std(target) == Some(true) {
        for krate in crates {
            cargo.args(["-p", krate]);
        }

        features += " compiler-builtins-mem";
        if !target.starts_with("bpf") {
            features.push_str(compiler_builtins_c_feature);
        }

        // for no-std targets we only compile a few no_std crates
        if crates.is_empty() {
            cargo.args(["-p", "alloc"]);
        }
        cargo
            .arg("--manifest-path")
            .arg(builder.src.join("library/alloc/Cargo.toml"))
            .arg("--features")
            .arg(features);
    } else {
        if crates.is_empty() {
            // The sysroot manifest's dummy crate is empty, so cargo may skip
            // building proc_macro unless we request it explicitly. That leaves
            // linked stage toolchains unable to compile proc-macro crates.
            cargo.args(["-p", "sysroot"]);
            cargo.args(["-p", "proc_macro"]);
        } else {
            for krate in crates {
                cargo.args(["-p", krate]);
            }
        }

        features += &builder.std_features(target);
        features.push_str(compiler_builtins_c_feature);

        cargo
            .arg("--features")
            .arg(features)
            .arg("--manifest-path")
            .arg(builder.src.join("library/sysroot/Cargo.toml"));

        // Help the libc crate compile by assisting it in finding various
        // sysroot native libraries.
        if target.contains("musl")
            && let Some(p) = builder.musl_libdir(target)
        {
            let root = format!("native={}", p.to_str().unwrap());
            cargo.rustflag("-L").rustflag(&root);
        }

        if target.contains("-wasi")
            && let Some(dir) = builder.wasi_libdir(target)
        {
            let root = format!("native={}", dir.to_str().unwrap());
            cargo.rustflag("-L").rustflag(&root);
        }
    }

    if builder.config.rust_lto == RustcLto::Off {
        cargo.rustflag("-Clto=off");
    }

    // By default, rustc does not include unwind tables unless they are required
    // for a particular target. They are not required by RISC-V targets, but
    // compiling the standard library with them means that users can get
    // backtraces without having to recompile the standard library themselves.
    //
    // This choice was discussed in https://github.com/rust-lang/rust/pull/69890
    if target.contains("riscv") {
        cargo.rustflag("-Cforce-unwind-tables=yes");
    }

    let html_root =
        format!("-Zcrate-attr=doc(html_root_url=\"{}/\")", builder.doc_rust_lang_org_channel(),);
    cargo.rustflag(&html_root);
    cargo.rustdocflag(&html_root);

    cargo.rustdocflag("-Zcrate-attr=warn(rust_2018_idioms)");
}

/// Link all libstd rlibs/dylibs into a sysroot of `target_compiler`.
///
/// Links those artifacts generated by `compiler` to the `stage` compiler's
/// sysroot for the specified `host` and `target`.
///
/// Note that this assumes that `compiler` has already generated the libstd
/// libraries for `target`, and this method will find them in the relevant
/// output directory.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StdLink {
    pub compiler: Compiler,
    pub target_compiler: Compiler,
    pub target: TargetSelection,
    /// Not actually used; only present to make sure the cache invalidation is correct.
    crates: Vec<String>,
    /// See [`Std::force_recompile`].
    force_recompile: bool,
}

impl StdLink {
    pub fn from_std(std: Std, host_compiler: Compiler) -> Self {
        Self {
            compiler: host_compiler,
            target_compiler: std.build_compiler,
            target: std.target,
            crates: std.crates,
            force_recompile: std.force_recompile,
        }
    }
}

impl Step for StdLink {
    type Output = ();

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.never()
    }

    /// Link all libstd rlibs/dylibs into the sysroot location.
    ///
    /// Links those artifacts generated by `compiler` to the `stage` compiler's
    /// sysroot for the specified `host` and `target`.
    ///
    /// Note that this assumes that `compiler` has already generated the libstd
    /// libraries for `target`, and this method will find them in the relevant
    /// output directory.
    fn run(self, builder: &Builder<'_>) {
        let compiler = self.compiler;
        let target_compiler = self.target_compiler;
        let target = self.target;

        // NOTE: intentionally does *not* check `target == builder.build` to avoid having to add the same check in `test::Crate`.
        let (libdir, hostdir) = if !self.force_recompile && builder.download_rustc() {
            // NOTE: copies part of `sysroot_libdir` to avoid having to add a new `force_recompile` argument there too
            let lib = builder.sysroot_libdir_relative(self.compiler);
            let sysroot = builder.ensure(crate::core::build_steps::compile::Sysroot {
                compiler: self.compiler,
                force_recompile: self.force_recompile,
            });
            let libdir = sysroot.join(lib).join("rustlib").join(target).join("lib");
            let hostdir = sysroot.join(lib).join("rustlib").join(compiler.host).join("lib");
            (libdir, hostdir)
        } else {
            let libdir = builder.sysroot_target_libdir(target_compiler, target);
            let hostdir = builder.sysroot_target_libdir(target_compiler, compiler.host);
            (libdir, hostdir)
        };

        let is_downloaded_beta_stage0 = builder
            .build
            .config
            .initial_rustc
            .starts_with(builder.out.join(compiler.host).join("stage0/bin"));

        // Special case for legacy beta stage0 sysroots. We only do this if the stage0 compiler comes from beta,
        // and is not set to a custom path.
        if compiler.stage == 0 && is_downloaded_beta_stage0 {
            // Copy bin files from stage0/bin to stage0-sysroot/bin
            let sysroot = builder.out.join(compiler.host).join("stage0-sysroot");

            let host = compiler.host;
            let stage0_bin_dir = builder.out.join(host).join("stage0/bin");
            let sysroot_bin_dir = sysroot.join("bin");
            t!(fs::create_dir_all(&sysroot_bin_dir));
            builder.cp_link_r(&stage0_bin_dir, &sysroot_bin_dir);

            let stage0_lib_dir = builder.out.join(host).join("stage0/lib");
            t!(fs::create_dir_all(sysroot.join("lib")));
            builder.cp_link_r(&stage0_lib_dir, &sysroot.join("lib"));

            // Copy codegen-backends from stage0
            let sysroot_codegen_backends = builder.sysroot_codegen_backends(compiler);
            t!(fs::create_dir_all(&sysroot_codegen_backends));
            let stage0_codegen_backends = builder
                .out
                .join(host)
                .join("stage0/lib/rustlib")
                .join(host)
                .join("codegen-backends");
            if stage0_codegen_backends.exists() {
                builder.cp_link_r(&stage0_codegen_backends, &sysroot_codegen_backends);
            }
        } else if compiler.stage == 0 {
            let sysroot = builder.out.join(compiler.host.triple).join("stage0-sysroot");

            if builder.local_rebuild {
                // On local rebuilds this path might be a symlink to the project root,
                // which can be read-only (e.g., on CI). So remove it before copying
                // the stage0 lib.
                let _ = fs::remove_dir_all(sysroot.join("lib/rustlib/src/rust"));
            }

            builder.cp_link_r(&builder.initial_sysroot.join("lib"), &sysroot.join("lib"));
        } else {
            if builder.download_rustc() {
                // Ensure there are no CI-rustc std artifacts.
                let _ = fs::remove_dir_all(&libdir);
                let _ = fs::remove_dir_all(&hostdir);
            }

            add_to_sysroot(
                builder,
                &libdir,
                &hostdir,
                &build_stamp::libstd_stamp(builder, compiler, target),
            );
            if target_compiler.stage < 2 {
                let sysroot = builder.sysroot(target_compiler);
                restore_user_facing_tools(builder, target_compiler, &sysroot);
            }
        }
    }
}

/// Copies sanitizer runtime libraries into target libdir.
fn copy_sanitizers(
    builder: &Builder<'_>,
    compiler: &Compiler,
    target: TargetSelection,
) -> Vec<PathBuf> {
    let runtimes: Vec<llvm::SanitizerRuntime> = builder.ensure(llvm::Sanitizers { target });

    if builder.config.dry_run() {
        return Vec::new();
    }

    let mut target_deps = Vec::new();
    let libdir = builder.sysroot_target_libdir(*compiler, target);

    for runtime in &runtimes {
        let dst = libdir.join(&runtime.name);
        builder.copy_link(&runtime.path, &dst, FileType::NativeLibrary);

        // The `aarch64-apple-ios-macabi` and `x86_64-apple-ios-macabi` are also supported for
        // sanitizers, but they share a sanitizer runtime with `${arch}-apple-darwin`, so we do
        // not list them here to rename and sign the runtime library.
        if target == "x86_64-apple-darwin"
            || target == "aarch64-apple-darwin"
            || target == "aarch64-apple-ios"
            || target == "aarch64-apple-ios-sim"
            || target == "x86_64-apple-ios"
        {
            // Update the library’s install name to reflect that it has been renamed.
            apple_darwin_update_library_name(builder, &dst, &format!("@rpath/{}", runtime.name));
            // Upon renaming the install name, the code signature of the file will invalidate,
            // so we will sign it again.
            apple_darwin_sign_file(builder, &dst);
        }

        target_deps.push(dst);
    }

    target_deps
}

fn apple_darwin_update_library_name(builder: &Builder<'_>, library_path: &Path, new_name: &str) {
    command("install_name_tool").arg("-id").arg(new_name).arg(library_path).run(builder);
}

fn apple_darwin_sign_file(builder: &Builder<'_>, file_path: &Path) {
    command("codesign")
        .arg("-f") // Force to rewrite the existing signature
        .arg("-s")
        .arg("-")
        .arg(file_path)
        .run(builder);
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StartupObjects {
    pub compiler: Compiler,
    pub target: TargetSelection,
}

impl Step for StartupObjects {
    type Output = Vec<(PathBuf, DependencyType)>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("library/rtstartup")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(StartupObjects {
            compiler: run.builder.compiler(run.builder.top_stage, run.build_triple()),
            target: run.target,
        });
    }

    /// Builds and prepare startup objects like rsbegin.o and rsend.o
    ///
    /// These are primarily used on Windows right now for linking executables/dlls.
    /// They don't require any library support as they're just plain old object
    /// files, so we just use the nightly snapshot compiler to always build them (as
    /// no other compilers are guaranteed to be available).
    fn run(self, builder: &Builder<'_>) -> Vec<(PathBuf, DependencyType)> {
        let for_compiler = self.compiler;
        let target = self.target;
        // Even though no longer necessary on x86_64, they are kept for now to
        // avoid potential issues in downstream crates.
        if !target.is_windows_gnu() {
            return vec![];
        }

        let mut target_deps = vec![];

        let src_dir = &builder.src.join("library").join("rtstartup");
        let dst_dir = &builder.native_dir(target).join("rtstartup");
        let sysroot_dir = &builder.sysroot_target_libdir(for_compiler, target);
        t!(fs::create_dir_all(dst_dir));

        for file in &["rsbegin", "rsend"] {
            let src_file = &src_dir.join(file.to_string() + ".rs");
            let dst_file = &dst_dir.join(file.to_string() + ".o");
            if !up_to_date(src_file, dst_file) {
                let mut cmd = command(&builder.initial_rustc);
                cmd.env("RUSTC_BOOTSTRAP", "1");
                cmd.env_remove(dylib_path_var());
                if !builder.local_rebuild {
                    // a local_rebuild compiler already has stage1 features
                    cmd.arg("--cfg").arg("bootstrap");
                }
                cmd.arg("--target")
                    .arg(target.rustc_target_arg())
                    .arg("--emit=obj")
                    .arg("-o")
                    .arg(dst_file)
                    .arg(src_file)
                    .run(builder);
            }

            let obj = sysroot_dir.join((*file).to_string() + ".o");
            builder.copy_link(dst_file, &obj, FileType::NativeLibrary);
            target_deps.push((obj, DependencyType::Target));
        }

        target_deps
    }
}

fn cp_rustc_component_to_ci_sysroot(builder: &Builder<'_>, sysroot: &Path, contents: Vec<String>) {
    let ci_rustc_dir = builder.config.ci_rustc_dir();

    for file in contents {
        let src = ci_rustc_dir.join(&file);
        let dst = sysroot.join(file);
        if src.is_dir() {
            t!(fs::create_dir_all(dst));
        } else {
            builder.copy_link(&src, &dst, FileType::Regular);
        }
    }
}

/// Represents information about a built rustc.
#[derive(Clone, Debug)]
pub struct BuiltRustc {
    /// The compiler that actually built this *rustc*.
    /// This can be different from the *build_compiler* passed to the `Rustc` step because of
    /// uplifting.
    pub build_compiler: Compiler,
}

/// Build rustc using the passed `build_compiler`.
///
/// - Makes sure that `build_compiler` has a standard library prepared for its host target,
///   so that it can compile build scripts and proc macros when building this `rustc`.
/// - Makes sure that `build_compiler` has a standard library prepared for `target`,
///   so that the built `rustc` can *link to it* and use it at runtime.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Rustc {
    /// The target on which rustc will run (its host).
    pub target: TargetSelection,
    /// The **previous** compiler used to compile this rustc.
    pub build_compiler: Compiler,
    /// Whether to build a subset of crates, rather than the whole compiler.
    ///
    /// This should only be requested by the user, not used within bootstrap itself.
    /// Using it within bootstrap can lead to confusing situation where lints are replayed
    /// in two different steps.
    crates: Vec<String>,
}

impl Rustc {
    pub fn new(build_compiler: Compiler, target: TargetSelection) -> Self {
        Self { target, build_compiler, crates: Default::default() }
    }
}

impl Step for Rustc {
    type Output = BuiltRustc;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        let mut crates = run.builder.in_tree_crates("rustc-main", None);
        for (i, krate) in crates.iter().enumerate() {
            // We can't allow `build rustc` as an alias for this Step, because that's reserved by `Assemble`.
            // Ideally Assemble would use `build compiler` instead, but that seems too confusing to be worth the breaking change.
            if krate.name == "rustc-main" {
                crates.swap_remove(i);
                break;
            }
        }
        // This crate is selected by `BuiltinTrustCg`, which builds the full
        // compiler. Treating it as a partial Rustc build overwrites the shared
        // `.librustc-stamp` with a backend-only stamp and can leave stale
        // rustc/trustc binaries without librustc_driver.
        crates.retain(|krate| krate.name != "rustc_codegen_trust_cg");
        run.crates(crates)
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

    fn make_run(run: RunConfig<'_>) {
        // If only `compiler` was passed, do not run this step.
        // Instead the `Assemble` step will take care of compiling Rustc.
        if run.builder.paths == vec![PathBuf::from("compiler")] {
            return;
        }

        let crates = run.cargo_crates_in_set();
        run.builder.ensure(Rustc {
            build_compiler: run
                .builder
                .compiler(run.builder.top_stage.saturating_sub(1), run.build_triple()),
            target: run.target,
            crates,
        });
    }

    /// Builds the compiler.
    ///
    /// This will build the compiler for a particular stage of the build using
    /// the `build_compiler` targeting the `target` architecture. The artifacts
    /// created will also be linked into the sysroot directory.
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let build_compiler = self.build_compiler;
        let target = self.target;

        // NOTE: the ABI of the stage0 compiler is different from the ABI of the downloaded compiler,
        // so its artifacts can't be reused.
        if builder.download_rustc() && build_compiler.stage != 0 {
            trace!(stage = build_compiler.stage, "`download_rustc` requested");

            let sysroot =
                builder.ensure(Sysroot { compiler: build_compiler, force_recompile: false });
            cp_rustc_component_to_ci_sysroot(
                builder,
                &sysroot,
                builder.config.ci_rustc_dev_contents(),
            );
            return BuiltRustc { build_compiler };
        }

        if staged_narrow_trust_cg_cannot_self_host(
            build_compiler.stage,
            builder.local_rebuild,
            builder.config.default_codegen_backend(build_compiler.host),
        ) {
            reject_narrow_trust_cg_self_host("the next-stage compiler");
        }

        // Build a standard library for `target` using the `build_compiler`.
        // This will be the standard library that the rustc which we build *links to*.
        builder.std(build_compiler, target);

        if builder.config.keep_stage.contains(&build_compiler.stage) {
            trace!(stage = build_compiler.stage, "`keep-stage` requested");

            builder.info("WARNING: Using a potentially old librustc. This may not behave well.");
            builder.info("WARNING: Use `--keep-stage-std` if you want to rebuild the compiler when it changes");
            builder.ensure(RustcLink::from_rustc(self));

            return BuiltRustc { build_compiler };
        }

        // The stage of the compiler that we're building
        let stage = build_compiler.stage + 1;

        // If we are building a stage3+ compiler, and full bootstrap is disabled, and we have a
        // previous rustc available, we will uplift a compiler from a previous stage.
        // We do not allow cross-compilation uplifting here, because there it can be quite tricky
        // to figure out which stage actually built the rustc that should be uplifted.
        if build_compiler.stage >= 2
            && !builder.config.full_bootstrap
            && target == builder.host_target
        {
            // Here we need to determine the **build compiler** that built the stage that we will
            // be uplifting. We cannot uplift stage 1, as it has a different ABI than stage 2+,
            // so we always uplift the stage2 compiler (compiled with stage 1).
            let uplift_build_compiler = builder.compiler(1, build_compiler.host);

            let msg = format!("Uplifting rustc from stage2 to stage{stage})");
            builder.info(&msg);

            // Here the compiler that built the rlibs (`uplift_build_compiler`) can be different
            // from the compiler whose sysroot should be modified in this step. So we need to copy
            // the (previously built) rlibs into the correct sysroot.
            builder.ensure(RustcLink::from_build_compiler_and_sysroot(
                // This is the compiler that actually built the rustc rlibs
                uplift_build_compiler,
                // We copy the rlibs into the sysroot of `build_compiler`
                build_compiler,
                target,
                self.crates,
            ));

            // Here we have performed an uplift, so we return the actual build compiler that "built"
            // this rustc.
            return BuiltRustc { build_compiler: uplift_build_compiler };
        }

        // Build a standard library for the current host target using the `build_compiler`.
        // This standard library will be used when building `rustc` for compiling
        // build scripts and proc macros.
        // If we are not cross-compiling, the Std build above will be the same one as the one we
        // prepare here.
        builder.std(
            builder.compiler(self.build_compiler.stage, builder.config.host_target),
            builder.config.host_target,
        );

        let mut cargo = builder::Cargo::new(
            builder,
            build_compiler,
            Mode::Rustc,
            SourceType::InTree,
            target,
            Kind::Build,
        );

        rustc_cargo(builder, &mut cargo, target, &build_compiler, &self.crates);

        // NB: all RUSTFLAGS should be added to `rustc_cargo()` so they will be
        // consistently applied by check/doc/test modes too.

        for krate in &*self.crates {
            cargo.arg("-p").arg(krate);
        }

        if builder.build.config.enable_bolt_settings && build_compiler.stage == 1 {
            // Relocations are required for BOLT to work.
            cargo.env("RUSTC_BOLT_LINK_FLAGS", "1");
        }

        let _guard = builder.msg(
            Kind::Build,
            format_args!("compiler artifacts{}", crate_description(&self.crates)),
            Mode::Rustc,
            build_compiler,
            target,
        );
        let stamp = build_stamp::librustc_stamp(builder, build_compiler, target);

        run_cargo(
            builder,
            cargo,
            vec![],
            &stamp,
            vec![],
            ArtifactKeepMode::Custom(Box::new(|filename| {
                if filename.contains("jemalloc_sys")
                    || filename.contains("rustc_public_bridge")
                    || filename.contains("rustc_public")
                {
                    // jemalloc_sys and rustc_public_bridge are not linked into librustc_driver.so,
                    // so we need to distribute them as rlib to be able to use them.
                    filename.ends_with(".rlib")
                } else {
                    // Distribute the rest of the rustc crates as rmeta files only to reduce
                    // the tarball sizes by about 50%. The object files are linked into
                    // librustc_driver.so, so it is still possible to link against them.
                    filename.ends_with(".rmeta")
                }
            })),
        );

        let target_root_dir = stamp.path().parent().unwrap();
        // When building `librustc_driver.so` (like `libLLVM.so`) on linux, it can contain
        // unexpected debuginfo from dependencies, for example from the C++ standard library used in
        // our LLVM wrapper. Unless we're explicitly requesting `librustc_driver` to be built with
        // debuginfo (via the debuginfo level of the executables using it): strip this debuginfo
        // away after the fact.
        if builder.config.rust_debuginfo_level_rustc == DebuginfoLevel::None
            && builder.config.rust_debuginfo_level_tools == DebuginfoLevel::None
        {
            let rustc_driver = target_root_dir.join("librustc_driver.so");
            strip_debug(builder, target, &rustc_driver);
        }

        if builder.config.rust_debuginfo_level_rustc == DebuginfoLevel::None {
            // Due to LTO a lot of debug info from C++ dependencies such as jemalloc can make it into
            // our final binaries
            strip_debug(builder, target, &target_root_dir.join("rustc-main"));
        }

        let output_compiler = Compiler::new(stage, target);
        let output_sysroot = builder.sysroot(output_compiler);
        materialize_local_compiler_aliases(
            builder,
            output_compiler,
            &output_sysroot,
            build_compiler,
        );

        builder.ensure(RustcLink::from_rustc(self));
        BuiltRustc { build_compiler }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("rustc", self.target).built_by(self.build_compiler))
    }
}

pub fn rustc_cargo(
    builder: &Builder<'_>,
    cargo: &mut Cargo,
    target: TargetSelection,
    build_compiler: &Compiler,
    crates: &[String],
) {
    cargo
        .arg("--features")
        .arg(builder.rustc_features(builder.kind, target, crates))
        .arg("--manifest-path")
        .arg(builder.src.join("compiler/rustc/Cargo.toml"));

    cargo.rustdocflag("-Zcrate-attr=warn(rust_2018_idioms)");

    // If the rustc output is piped to e.g. `head -n1` we want the process to be killed, rather than
    // having an error bubble up and cause a panic.
    //
    // FIXME(jieyouxu): this flag is load-bearing for rustc to not ICE on broken pipes, because
    // rustc internally sometimes uses std `println!` -- but std `println!` by default will panic on
    // broken pipes, and uncaught panics will manifest as an ICE. The compiler *should* handle this
    // properly, but this flag is set in the meantime to paper over the I/O errors.
    //
    // See <https://github.com/rust-lang/rust/issues/131059> for details.
    //
    // Also see the discussion for properly handling I/O errors related to broken pipes, i.e. safe
    // variants of `println!` in
    // <https://rust-lang.zulipchat.com/#narrow/stream/131828-t-compiler/topic/Internal.20lint.20for.20raw.20.60print!.60.20and.20.60println!.60.3F>.
    cargo.rustflag("-Zon-broken-pipe=kill");

    // Building with protected visibility reduces the number of dynamic relocations needed, giving
    // us a faster startup time. However GNU ld < 2.40 will error if we try to link a shared object
    // with direct references to protected symbols, so for now we only use protected symbols if
    // linking with LLD is enabled.
    if builder.build.config.bootstrap_override_lld.is_used() {
        cargo.rustflag("-Zdefault-visibility=protected");
    }

    if is_lto_stage(build_compiler) {
        match builder.config.rust_lto {
            RustcLto::Thin | RustcLto::Fat => {
                // Since using LTO for optimizing dylibs is currently experimental,
                // we need to pass -Zdylib-lto.
                cargo.rustflag("-Zdylib-lto");
                // Cargo by default passes `-Cembed-bitcode=no` and doesn't pass `-Clto` when
                // compiling dylibs (and their dependencies), even when LTO is enabled for the
                // crate. Therefore, we need to override `-Clto` and `-Cembed-bitcode` here.
                let lto_type = match builder.config.rust_lto {
                    RustcLto::Thin => "thin",
                    RustcLto::Fat => "fat",
                    _ => unreachable!(),
                };
                cargo.rustflag(&format!("-Clto={lto_type}"));
                cargo.rustflag("-Cembed-bitcode=yes");
            }
            RustcLto::ThinLocal => { /* Do nothing, this is the default */ }
            RustcLto::Off => {
                cargo.rustflag("-Clto=off");
            }
        }
    } else if builder.config.rust_lto == RustcLto::Off {
        cargo.rustflag("-Clto=off");
    }

    // With LLD, we can use ICF (identical code folding) to reduce the executable size
    // of librustc_driver/rustc and to improve i-cache utilization.
    //
    // -Wl,[link options] doesn't work on MSVC. However, /OPT:ICF (technically /OPT:REF,ICF)
    // is already on by default in MSVC optimized builds, which is interpreted as --icf=all:
    // https://github.com/llvm/llvm-project/blob/3329cec2f79185bafd678f310fafadba2a8c76d2/lld/COFF/Driver.cpp#L1746
    // https://github.com/rust-lang/rust/blob/f22819bcce4abaff7d1246a56eec493418f9f4ee/compiler/rustc_codegen_ssa/src/back/linker.rs#L827
    if builder.config.bootstrap_override_lld.is_used() && !build_compiler.host.is_msvc() {
        cargo.rustflag("-Clink-args=-Wl,--icf=all");
    }

    if builder.config.rust_profile_use.is_some() && builder.config.rust_profile_generate.is_some() {
        panic!("Cannot use and generate PGO profiles at the same time");
    }
    let is_collecting = if let Some(path) = &builder.config.rust_profile_generate {
        if build_compiler.stage == 1 {
            cargo.rustflag(&format!("-Cprofile-generate={path}"));
            // Apparently necessary to avoid overflowing the counters during
            // a Cargo build profile
            cargo.rustflag("-Cllvm-args=-vp-counters-per-site=4");
            true
        } else {
            false
        }
    } else if let Some(path) = &builder.config.rust_profile_use {
        if build_compiler.stage == 1 {
            cargo.rustflag(&format!("-Cprofile-use={path}"));
            if builder.is_verbose() {
                cargo.rustflag("-Cllvm-args=-pgo-warn-missing-function");
            }
            true
        } else {
            false
        }
    } else {
        false
    };
    if is_collecting {
        // Ensure paths to Rust sources are relative, not absolute.
        cargo.rustflag(&format!(
            "-Cllvm-args=-static-func-strip-dirname-prefix={}",
            builder.config.src.components().count()
        ));
    }

    // The stage0 compiler changes infrequently and does not directly depend on code
    // in the current working directory. Therefore, caching it with sccache should be
    // useful.
    // This is only performed for non-incremental builds, as ccache cannot deal with these.
    if let Some(ref ccache) = builder.config.ccache
        && build_compiler.stage == 0
        && !builder.config.incremental
    {
        cargo.env("RUSTC_WRAPPER", ccache);
    }

    rustc_cargo_env(builder, cargo, target);
}

pub fn rustc_cargo_env(builder: &Builder<'_>, cargo: &mut Cargo, target: TargetSelection) {
    // Set some configuration variables picked up by build scripts and
    // the compiler alike
    cargo
        .env("CFG_RELEASE", builder.rust_release())
        .env("CFG_RELEASE_CHANNEL", &builder.config.channel)
        .env("CFG_VERSION", builder.rust_version())
        // Trust: the product version, distinct from the rustc-protocol one above.
        .env("CFG_TRUST_VERSION", builder.trust_version());

    // Some tools like Cargo detect their own git information in build scripts. When omit-git-hash
    // is enabled in bootstrap.toml, we pass this environment variable to tell build scripts to avoid
    // detecting git information on their own.
    if builder.config.omit_git_hash {
        cargo.env("CFG_OMIT_GIT_HASH", "1");
    }

    cargo.env("CFG_DEFAULT_CODEGEN_BACKEND", builder.config.default_codegen_backend(target).name());

    let libdir_relative = builder.config.libdir_relative().unwrap_or_else(|| Path::new("lib"));
    let target_config = builder.config.target_config.get(&target);

    cargo.env("CFG_LIBDIR_RELATIVE", libdir_relative);

    if let Some(ref ver_date) = builder.rust_info().commit_date() {
        cargo.env("CFG_VER_DATE", ver_date);
    }
    if let Some(ref ver_hash) = builder.rust_info().sha() {
        cargo.env("CFG_VER_HASH", ver_hash);
    }
    if !builder.unstable_features() {
        cargo.env("CFG_DISABLE_UNSTABLE_FEATURES", "1");
    }

    // Prefer the current target's own default_linker, else a globally
    // specified one.
    if let Some(s) = target_config.and_then(|c| c.default_linker.as_ref()) {
        cargo.env("CFG_DEFAULT_LINKER", s);
    } else if let Some(ref s) = builder.config.rustc_default_linker {
        cargo.env("CFG_DEFAULT_LINKER", s);
    }

    // Enable rustc's env var to use a linker override on Linux when requested.
    if let Some(linker) = target_config.map(|c| c.default_linker_linux_override) {
        match linker {
            DefaultLinuxLinkerOverride::Off => {}
            DefaultLinuxLinkerOverride::SelfContainedLldCc => {
                cargo.env("CFG_DEFAULT_LINKER_SELF_CONTAINED_LLD_CC", "1");
            }
        }
    }

    // The host this new compiler will *run* on.
    cargo.env("CFG_COMPILER_HOST_TRIPLE", target.triple);

    if builder.config.rust_verify_llvm_ir {
        cargo.env("RUSTC_VERIFY_LLVM_IR", "1");
    }

    // These conditionals represent a tension between three forces:
    // - For non-check builds, we need to define some LLVM-related environment
    //   variables, requiring LLVM to have been built.
    // - For check builds, we want to avoid building LLVM if possible.
    // - Check builds and non-check builds should have the same environment if
    //   possible, to avoid unnecessary rebuilds due to cache-busting.
    //
    // Therefore we try to avoid building LLVM for check builds, but only if
    // building LLVM would be expensive. If "building" LLVM is cheap
    // (i.e. it's already built or is downloadable), we prefer to maintain a
    // consistent environment between check and non-check builds.
    if builder.config.llvm_enabled(target) {
        let building_llvm_is_expensive =
            crate::core::build_steps::llvm::prebuilt_llvm_config(builder, target, false)
                .should_build();

        let skip_llvm = (builder.kind == Kind::Check) && building_llvm_is_expensive;
        if !skip_llvm {
            rustc_llvm_env(builder, cargo, target)
        }
    }

    // See also the "JEMALLOC_SYS_WITH_LG_PAGE" setting in the tool build step.
    if builder.config.jemalloc(target) && env::var_os("JEMALLOC_SYS_WITH_LG_PAGE").is_none() {
        // Build jemalloc on AArch64 with support for page sizes up to 64K
        // See: https://github.com/rust-lang/rust/pull/135081
        if target.starts_with("aarch64") {
            cargo.env("JEMALLOC_SYS_WITH_LG_PAGE", "16");
        }
        // Build jemalloc on LoongArch with support for page sizes up to 16K
        else if target.starts_with("loongarch") {
            cargo.env("JEMALLOC_SYS_WITH_LG_PAGE", "14");
        }
    }
}

/// Pass down configuration from the LLVM build into the build of
/// rustc_llvm and rustc_codegen_llvm.
///
/// Note that this has the side-effect of _building LLVM_, which is sometimes
/// unwanted (e.g. for check builds).
fn rustc_llvm_env(builder: &Builder<'_>, cargo: &mut Cargo, target: TargetSelection) {
    if builder.config.is_rust_llvm(target) {
        cargo.env("LLVM_RUSTLLVM", "1");
    }
    if builder.config.llvm_enzyme {
        cargo.env("LLVM_ENZYME", "1");
    }
    let llvm::LlvmResult { host_llvm_config, .. } = builder.ensure(llvm::Llvm { target });
    if builder.config.llvm_offload {
        builder.ensure(llvm::OmpOffload { target });
        cargo.env("LLVM_OFFLOAD", "1");
    }

    cargo.env("LLVM_CONFIG", &host_llvm_config);

    // Some LLVM linker flags (-L and -l) may be needed to link `rustc_llvm`. Its build script
    // expects these to be passed via the `LLVM_LINKER_FLAGS` env variable, separated by
    // whitespace.
    //
    // For example:
    // - on windows, when `clang-cl` is used with instrumentation, we need to manually add
    // clang's runtime library resource directory so that the profiler runtime library can be
    // found. This is to avoid the linker errors about undefined references to
    // `__llvm_profile_instrument_memop` when linking `rustc_driver`.
    let mut llvm_linker_flags = String::new();
    if builder.config.llvm_profile_generate
        && target.is_msvc()
        && let Some(ref clang_cl_path) = builder.config.llvm_clang_cl
    {
        // Add clang's runtime library directory to the search path
        let clang_rt_dir = get_clang_cl_resource_dir(builder, clang_cl_path);
        llvm_linker_flags.push_str(&format!("-L{}", clang_rt_dir.display()));
    }

    // The config can also specify its own llvm linker flags.
    if let Some(ref s) = builder.config.llvm_ldflags {
        if !llvm_linker_flags.is_empty() {
            llvm_linker_flags.push(' ');
        }
        llvm_linker_flags.push_str(s);
    }

    // Set the linker flags via the env var that `rustc_llvm`'s build script will read.
    if !llvm_linker_flags.is_empty() {
        cargo.env("LLVM_LINKER_FLAGS", llvm_linker_flags);
    }

    // Building with a static libstdc++ is only supported on Linux and windows-gnu* right now,
    // not for MSVC or macOS
    if builder.config.llvm_static_stdcpp
        && !target.contains("freebsd")
        && !target.is_msvc()
        && !target.contains("apple")
        && !target.contains("solaris")
    {
        let libstdcxx_name =
            if target.contains("windows-gnullvm") { "libc++.a" } else { "libstdc++.a" };
        let file = compiler_file(
            builder,
            &builder.cxx(target).unwrap(),
            target,
            CLang::Cxx,
            libstdcxx_name,
        );
        cargo.env("LLVM_STATIC_STDCPP", file);
    }
    if builder.llvm_link_shared() {
        cargo.env("LLVM_LINK_SHARED", "1");
    }
    if builder.config.llvm_use_libcxx {
        cargo.env("LLVM_USE_LIBCXX", "1");
    }
    if builder.config.llvm_assertions {
        cargo.env("LLVM_ASSERTIONS", "1");
    }
}

/// `RustcLink` copies compiler rlibs from a rustc build into a compiler sysroot.
/// It works with (potentially up to) three compilers:
/// - `build_compiler` is a compiler that built rustc rlibs
/// - `sysroot_compiler` is a compiler into whose sysroot we will copy the rlibs
///   - In most situations, `build_compiler` == `sysroot_compiler`
/// - `target_compiler` is the compiler whose rlibs were built. It is not represented explicitly
///   in this step, rather we just read the rlibs from a rustc build stamp of `build_compiler`.
///
/// This is necessary for tools using `rustc_private`, where the previous compiler will build
/// a tool against the next compiler.
/// To build a tool against a compiler, the rlibs of that compiler that it links against
/// must be in the sysroot of the compiler that's doing the compiling.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RustcLink {
    /// This compiler **built** some rustc, whose rlibs we will copy into a sysroot.
    build_compiler: Compiler,
    /// This is the compiler into whose sysroot we want to copy the built rlibs.
    /// In most cases, it will correspond to `build_compiler`.
    sysroot_compiler: Compiler,
    target: TargetSelection,
    /// Not actually used; only present to make sure the cache invalidation is correct.
    crates: Vec<String>,
}

impl RustcLink {
    /// Copy rlibs from the build compiler that build this `rustc` into the sysroot of that
    /// build compiler.
    fn from_rustc(rustc: Rustc) -> Self {
        Self {
            build_compiler: rustc.build_compiler,
            sysroot_compiler: rustc.build_compiler,
            target: rustc.target,
            crates: rustc.crates,
        }
    }

    /// Copy rlibs **built** by `build_compiler` into the sysroot of `sysroot_compiler`.
    fn from_build_compiler_and_sysroot(
        build_compiler: Compiler,
        sysroot_compiler: Compiler,
        target: TargetSelection,
        crates: Vec<String>,
    ) -> Self {
        Self { build_compiler, sysroot_compiler, target, crates }
    }
}

impl Step for RustcLink {
    type Output = ();

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.never()
    }

    /// Same as `StdLink`, only for librustc
    fn run(self, builder: &Builder<'_>) {
        let build_compiler = self.build_compiler;
        let sysroot_compiler = self.sysroot_compiler;
        let target = self.target;
        add_rustc_to_sysroot(
            builder,
            &builder.sysroot_target_libdir(sysroot_compiler, target),
            &builder.sysroot_target_libdir(sysroot_compiler, sysroot_compiler.host),
            &build_stamp::librustc_stamp(builder, build_compiler, target),
        );
    }
}

/// Build a compiler containing the builtin trust-cg backend.
///
/// trust-cg intentionally has no standalone codegen-plugin artifact: a plugin
/// would statically link a second copy of rustc_span and its scoped TLS. The
/// historical plugin build consequently panicked as soon as it interned a
/// symbol. Keep the familiar source path and aliases, but make them select the
/// complete, runnable compiler that owns the backend.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BuiltinTrustCg {
    pub target_compiler: Compiler,
}

fn trust_cg_builtin_enabled_for_any_host<'a>(
    backends_by_host: impl IntoIterator<Item = &'a [CodegenBackendKind]>,
) -> bool {
    backends_by_host.into_iter().any(trust_cg_builtin_enabled_for_host)
}

fn trust_cg_builtin_enabled_for_host(backends: &[CodegenBackendKind]) -> bool {
    backends.contains(&CodegenBackendKind::TrustCg)
}

impl Step for BuiltinTrustCg {
    type Output = Compiler;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        if !trust_cg_builtin_enabled_for_any_host(
            run.builder.hosts.iter().map(|host| run.builder.config.enabled_codegen_backends(*host)),
        ) {
            // This is a builtin backend, not an independently buildable
            // plugin.  Registering its source path while it is disabled makes
            // a broad `x build compiler` select a step that can only fail.
            return run.never();
        }
        run.path("compiler/rustc_codegen_trust_cg")
            .alias("rustc_codegen_trust_cg")
            .alias("rustc-codegen-trust_cg")
            .alias("cg_trust_cg")
    }

    fn make_run(run: RunConfig<'_>) {
        // `should_run` is evaluated once for the whole build, but host steps
        // are expanded over every configured host afterwards. Target-specific
        // backend lists can therefore enable trust-cg for one host and disable
        // it for another. Do not schedule an impossible builtin validation for
        // the disabled hosts merely because the selector was registered by an
        // enabled sibling.
        if !trust_cg_builtin_enabled_for_host(
            run.builder.config.enabled_codegen_backends(run.target),
        ) {
            return;
        }
        run.builder.ensure(BuiltinTrustCg {
            target_compiler: Compiler::new(run.builder.top_stage, run.target),
        });
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        if !builder
            .config
            .enabled_codegen_backends(self.target_compiler.host)
            .contains(&CodegenBackendKind::TrustCg)
        {
            panic!(
                "the trust-cg backend is builtin; enable `trust-cg` in \
                 `rust.codegen-backends` before selecting \
                 `compiler/rustc_codegen_trust_cg`"
            );
        }
        if self.target_compiler.stage == 0 {
            // Stage 0 is supplied by the configured bootstrap toolchain. There
            // is no in-tree compiler to build or validate at this stage.
            return self.target_compiler;
        }

        // Match the full `Rustc` build selected for compiler sources, but stop
        // before `Assemble`. Assemble builds std with the newly-produced
        // compiler; when trust-cg is the configured default that accidentally
        // asks the still-incomplete backend to self-host compiler_builtins.
        // Building rustc itself only needs the previous-stage compiler and its
        // std, and writes the authoritative *full* librustc stamp.
        let previous = builder.compiler(self.target_compiler.stage - 1, builder.config.host_target);
        let BuiltRustc { build_compiler } =
            builder.ensure(Rustc::new(previous, self.target_compiler.host));

        // `Rustc::run` normally materializes these aliases. Repeat the
        // idempotent operation here to cover keep-stage/uplift paths and bind
        // validation to the build compiler recorded by the full stamp.
        let sysroot = builder.sysroot(self.target_compiler);
        materialize_local_compiler_aliases(builder, self.target_compiler, &sysroot, build_compiler);
        validate_assembled_local_compiler(builder, self.target_compiler, &sysroot);
        self.target_compiler
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("builtin trust-cg compiler", self.target_compiler.host))
    }
}

pub fn compiler_file(
    builder: &Builder<'_>,
    compiler: &Path,
    target: TargetSelection,
    c: CLang,
    file: &str,
) -> PathBuf {
    if builder.config.dry_run() {
        return PathBuf::new();
    }
    let mut cmd = command(compiler);
    cmd.args(builder.cc_handled_cflags(target, c));
    cmd.args(builder.cc_unhandled_cflags(target, GitRepo::Rustc, c));
    cmd.arg(format!("-print-file-name={file}"));
    let out = cmd.run_capture_stdout(builder).stdout();
    PathBuf::from(out.trim())
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sysroot {
    pub compiler: Compiler,
    /// See [`Std::force_recompile`].
    force_recompile: bool,
}

impl Sysroot {
    pub(crate) fn new(compiler: Compiler) -> Self {
        Sysroot { compiler, force_recompile: false }
    }
}

impl Step for Sysroot {
    type Output = PathBuf;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.never()
    }

    /// Returns the sysroot that `compiler` is supposed to use.
    /// For the stage0 compiler, this is stage0-sysroot (because of the initial std build).
    /// For all other stages, it's the same stage directory that the compiler lives in.
    fn run(self, builder: &Builder<'_>) -> PathBuf {
        let compiler = self.compiler;
        let host_dir = builder.out.join(compiler.host);

        let sysroot_dir = |stage| {
            if stage == 0 {
                host_dir.join("stage0-sysroot")
            } else if self.force_recompile && stage == compiler.stage {
                host_dir.join(format!("stage{stage}-test-sysroot"))
            } else if builder.download_rustc() && compiler.stage != builder.top_stage {
                host_dir.join("ci-rustc-sysroot")
            } else {
                host_dir.join(format!("stage{stage}"))
            }
        };
        let sysroot = sysroot_dir(compiler.stage);
        trace!(stage = ?compiler.stage, ?sysroot);

        builder.do_if_verbose(|| {
            println!("Removing sysroot {} to avoid caching bugs", sysroot.display())
        });
        let _ = fs::remove_dir_all(&sysroot);
        t!(fs::create_dir_all(&sysroot));

        // In some cases(see https://github.com/rust-lang/rust/issues/109314), when the stage0
        // compiler relies on more recent version of LLVM than the stage0 compiler, it may not
        // be able to locate the correct LLVM in the sysroot. This situation typically occurs
        // when we upgrade LLVM version while the stage0 compiler continues to use an older version.
        //
        // Make sure to add the correct version of LLVM into the stage0 sysroot.
        if compiler.stage == 0 {
            dist::maybe_install_llvm_target(builder, compiler.host, &sysroot);
        }

        // If we're downloading a compiler from CI, we can use the same compiler for all stages other than 0.
        if builder.download_rustc() && compiler.stage != 0 {
            assert_eq!(
                builder.config.host_target, compiler.host,
                "Cross-compiling is not yet supported with `download-rustc`",
            );

            // #102002, cleanup old toolchain folders when using download-rustc so people don't use them by accident.
            for stage in 0..=2 {
                if stage != compiler.stage {
                    let dir = sysroot_dir(stage);
                    if !dir.ends_with("ci-rustc-sysroot") {
                        let _ = fs::remove_dir_all(dir);
                    }
                }
            }

            // Copy the compiler into the correct sysroot.
            //
            // FIXME(#156525): investigate if this is still needed.
            //
            // NOTE(#108767): We intentionally don't copy `trustc-dev` artifacts until they're
            // requested with `builder.ensure(Rustc)`. This fixes an issue where we'd have multiple
            // copies of libc in the sysroot with no way to tell which to load. There are a few
            // quirks of bootstrap that interact to make this reliable:
            // 1. The order `Step`s are run is hard-coded in `builder.rs` and not configurable. This
            //    avoids e.g. reordering `test::UiFulldeps` before `test::Ui` and causing the latter
            //    to fail because of duplicate metadata.
            // 2. The sysroot is deleted and recreated between each invocation, so running `x test
            //    ui-fulldeps && x test ui` can't cause failures.
            let mut filtered_files = Vec::new();
            let mut add_filtered_files = |suffix, contents| {
                for path in contents {
                    let path = Path::new(&path);
                    if path.parent().is_some_and(|parent| parent.ends_with(suffix)) {
                        filtered_files.push(path.file_name().unwrap().to_owned());
                    }
                }
            };
            let suffix = format!("lib/rustlib/{}/lib", compiler.host);
            add_filtered_files(suffix.as_str(), builder.config.ci_rustc_dev_contents());
            // NOTE: we can't copy std eagerly because `stage2-test-sysroot` needs to have only the
            // newly compiled std, not the downloaded std.
            add_filtered_files("lib", builder.config.ci_rust_std_contents());

            let filtered_extensions = [
                OsStr::new("rmeta"),
                OsStr::new("rlib"),
                // FIXME: this is wrong when compiler.host != build, but we don't support that today
                OsStr::new(std::env::consts::DLL_EXTENSION),
            ];
            let ci_rustc_dir = builder.config.ci_rustc_dir();
            builder.cp_link_filtered(&ci_rustc_dir, &sysroot, &|path| {
                if path.extension().is_none_or(|ext| !filtered_extensions.contains(&ext)) {
                    return true;
                }
                if !path.parent().is_none_or(|p| p.ends_with(&suffix)) {
                    return true;
                }
                filtered_files.iter().all(|f| f != path.file_name().unwrap())
            });
        }

        restore_user_facing_tools(builder, compiler, &sysroot);
        restore_local_compiler_aliases(builder, compiler, &sysroot);

        // Symlink the source root into the same location inside the sysroot,
        // where `rust-src` component would go (`$sysroot/lib/rustlib/src/rust`),
        // so that any tools relying on `rust-src` also work for local builds,
        // and also for translating the virtual `/rustc/$hash` back to the real
        // directory (for running tests with `rust.remap-debuginfo = true`).
        if compiler.stage != 0 {
            let sysroot_lib_rustlib_src = sysroot.join("lib/rustlib/src");
            t!(fs::create_dir_all(&sysroot_lib_rustlib_src));
            let sysroot_lib_rustlib_src_rust = sysroot_lib_rustlib_src.join("rust");
            if let Err(e) =
                symlink_dir(&builder.config, &builder.src, &sysroot_lib_rustlib_src_rust)
            {
                eprintln!(
                    "ERROR: creating symbolic link `{}` to `{}` failed with {}",
                    sysroot_lib_rustlib_src_rust.display(),
                    builder.src.display(),
                    e,
                );
                if builder.config.rust_remap_debuginfo {
                    eprintln!(
                        "ERROR: some `tests/ui` tests will fail when lacking `{}`",
                        sysroot_lib_rustlib_src_rust.display(),
                    );
                }
                build_helper::exit!(1);
            }
        }

        // rustc-src component is already part of CI rustc's sysroot
        if !builder.download_rustc() {
            let sysroot_lib_rustlib_rustcsrc = sysroot.join("lib/rustlib/rustc-src");
            t!(fs::create_dir_all(&sysroot_lib_rustlib_rustcsrc));
            let sysroot_lib_rustlib_rustcsrc_rust = sysroot_lib_rustlib_rustcsrc.join("rust");
            if let Err(e) =
                symlink_dir(&builder.config, &builder.src, &sysroot_lib_rustlib_rustcsrc_rust)
            {
                eprintln!(
                    "ERROR: creating symbolic link `{}` to `{}` failed with {}",
                    sysroot_lib_rustlib_rustcsrc_rust.display(),
                    builder.src.display(),
                    e,
                );
                build_helper::exit!(1);
            }
        }

        sysroot
    }
}

fn restore_user_facing_tools(builder: &Builder<'_>, compiler: Compiler, sysroot: &Path) {
    if !crate::core::build_steps::tool::should_restore_user_facing_tools(compiler.stage) {
        return;
    }

    // Restoring an existing tool is cheap and prevents sysroot assembly from
    // deleting it. Only a local build constructs the batteries-on runtime
    // here. Dist/install/test steps have explicit component graphs; eagerly
    // building the full surface would bypass their stage and selection policy.
    if crate::core::build_steps::tool::should_ensure_default_verifier_tool_bins(
        builder.kind,
        compiler.stage,
    ) {
        crate::core::build_steps::tool::ensure_default_verifier_tool_bins(
            builder, compiler, sysroot,
        );
    }

    let tools_dir = builder.tools_dir(compiler, compiler.host);

    let bindir = sysroot.join("bin");
    t!(fs::create_dir_all(&bindir));
    // A single built tool can intentionally back both its upstream-compatible
    // binary and Trust alias, for example `cargo` and `targo`.
    for (src_name, dst_name) in crate::core::build_steps::tool::restored_sysroot_bins(builder) {
        let src_exe = exe(src_name, compiler.host);
        let src = tools_dir.join(&src_exe);
        if src.exists() {
            builder.copy_link(
                &src,
                &bindir.join(exe(dst_name, compiler.host)),
                FileType::Executable,
            );
            if let Some(compat_name) =
                crate::core::build_steps::tool::upstream_compat_bin_for_tool_source(src_name)
            {
                builder.copy_link(
                    &src,
                    &bindir.join(exe(compat_name, compiler.host)),
                    FileType::Executable,
                );
            }
        }
    }

    let ra_proc_macro_srv = tools_dir.join(exe("rust-analyzer-proc-macro-srv", compiler.host));
    if crate::core::build_steps::tool::restore_rust_analyzer_proc_macro_srv(builder)
        && ra_proc_macro_srv.exists()
    {
        let libexec = sysroot.join("libexec");
        t!(fs::create_dir_all(&libexec));
        builder.copy_link(
            &ra_proc_macro_srv,
            &libexec.join(exe("trust-analyzer-proc-macro-srv", compiler.host)),
            FileType::Executable,
        );
    }

    // Trust: no stock `rust-analyzer-proc-macro-srv` alias. Purge it even when
    // the canonical server was not recopied, and detect dangling symlinks as
    // real forbidden path entries rather than relying on `Path::exists`.
    let stock_proc_macro_srv = sysroot
        .join("libexec")
        .join(exe("rust-analyzer-proc-macro-srv", compiler.host));
    t!(crate::core::build_steps::tool::remove_retired_proc_macro_srv_alias(
        &stock_proc_macro_srv
    ));
}

fn restore_local_compiler_aliases(builder: &Builder<'_>, compiler: Compiler, sysroot: &Path) {
    if compiler.stage == 0 || builder.download_rustc() {
        return;
    }

    let build_compiler = builder.compiler(compiler.stage - 1, builder.config.host_target);
    materialize_local_compiler_aliases(builder, compiler, sysroot, build_compiler);
}

fn materialize_local_compiler_aliases(
    builder: &Builder<'_>,
    compiler: Compiler,
    sysroot: &Path,
    build_compiler: Compiler,
) {
    let stamp = build_stamp::librustc_stamp(builder, build_compiler, compiler.host);
    let rustc_main = builder
        .cargo_out(build_compiler, Mode::Rustc, compiler.host)
        .join(exe("rustc-main", compiler.host));
    if !stamp.path().exists() || !rustc_main.is_file() {
        return;
    }
    restore_local_compiler_runtime_artifacts(builder, compiler, sysroot, build_compiler, &stamp);

    let bindir = sysroot.join("bin");
    t!(fs::create_dir_all(&bindir));
    let inherited_rustc = bindir.join(exe("rustc", compiler.host));
    builder.copy_link(&rustc_main, &inherited_rustc, FileType::Executable);
    builder.copy_link(
        &rustc_main,
        &bindir.join(exe("trustc", compiler.host)),
        FileType::Executable,
    );
}

fn restore_local_compiler_runtime_artifacts(
    builder: &Builder<'_>,
    compiler: Compiler,
    sysroot: &Path,
    build_compiler: Compiler,
    stamp: &BuildStamp,
) {
    let stamp_entries = builder.read_stamp_file(stamp);
    let proc_macros = stamp_entries
        .iter()
        .filter_map(|(path, dependency_type)| {
            if *dependency_type == DependencyType::Host {
                path.file_name().map(OsStr::to_owned)
            } else {
                None
            }
        })
        .collect::<HashSet<OsString>>();
    let runtime_artifacts = existing_local_compiler_runtime_artifacts(stamp_entries);

    let rustc_libdir = sysroot.join(builder.libdir_relative(compiler));
    t!(fs::create_dir_all(&rustc_libdir));
    for path in runtime_artifacts {
        let Some(filename) = path.file_name() else {
            continue;
        };
        builder.copy_link(&path, &rustc_libdir.join(filename), FileType::Regular);
    }
    let src_libdir = existing_sysroot_target_libdir(builder, build_compiler, compiler.host);
    if src_libdir.exists() {
        for entry in builder.read_dir(&src_libdir) {
            let filename = entry.file_name();
            let is_dylib_or_debug =
                is_dylib(&entry.path()) || filename.to_str().is_some_and(is_debug_info);
            if is_dylib_or_debug && !proc_macros.contains(&filename) {
                builder.copy_link(&entry.path(), &rustc_libdir.join(&filename), FileType::Regular);
            }
        }
    }
}

fn existing_local_compiler_runtime_artifacts(
    stamp_entries: Vec<(PathBuf, DependencyType)>,
) -> Vec<PathBuf> {
    stamp_entries
        .into_iter()
        .filter_map(|(path, dependency_type)| {
            (is_local_compiler_runtime_artifact(&path, dependency_type) && path.exists())
                .then_some(path)
        })
        .collect()
}

fn existing_sysroot_target_libdir(
    builder: &Builder<'_>,
    compiler: Compiler,
    target: TargetSelection,
) -> PathBuf {
    let host_dir = builder.out.join(compiler.host);
    let sysroot = if compiler.stage == 0 {
        host_dir.join("stage0-sysroot")
    } else {
        host_dir.join(format!("stage{}", compiler.stage))
    };
    sysroot.join(builder.sysroot_libdir_relative(compiler)).join("rustlib").join(target).join("lib")
}

fn is_local_compiler_runtime_artifact(path: &Path, dependency_type: DependencyType) -> bool {
    if dependency_type != DependencyType::Target {
        return false;
    }

    is_dylib(path) || path.file_name().and_then(OsStr::to_str).is_some_and(is_debug_info)
}

fn is_rustc_driver_runtime_artifact(path: &Path) -> bool {
    let Some(filename) = path.file_name().and_then(OsStr::to_str) else {
        return false;
    };
    is_dylib(path)
        && (filename.starts_with("librustc_driver-") || filename.starts_with("rustc_driver-"))
}

/// Reject a nominally assembled local compiler if its aliases cannot load the
/// driver. Native-host aliases are executed as a final smoke test so bootstrap
/// never reports success for the loader-abort state this invariant prevents.
fn validate_assembled_local_compiler(builder: &Builder<'_>, compiler: Compiler, sysroot: &Path) {
    if builder.config.dry_run() || compiler.stage == 0 || builder.download_rustc() {
        return;
    }

    let bindir = sysroot.join("bin");
    let rustc = bindir.join(exe("rustc", compiler.host));
    let trustc = bindir.join(exe("trustc", compiler.host));
    for binary in [&rustc, &trustc] {
        assert!(
            binary.is_file(),
            "assembled compiler is missing executable alias `{}`",
            binary.display()
        );
    }

    let rustc_libdir = builder.rustc_libdir(compiler);
    let has_driver = builder
        .read_dir(&rustc_libdir)
        .into_iter()
        .any(|entry| is_rustc_driver_runtime_artifact(&entry.path()));
    assert!(
        has_driver,
        "assembled stage{} compiler at `{}` has no librustc_driver runtime in `{}`",
        compiler.stage,
        sysroot.display(),
        rustc_libdir.display()
    );

    if compiler.host == builder.build.host_target {
        command(&rustc).arg("--version").run(builder);
        command(&trustc).arg("--version").run(builder);
    }
}

/// Return the stamp whose standard-library artifacts must be installed into a
/// newly assembled compiler sysroot. Non-full stage2+ builds uplift stage1
/// artifacts; stage1 and full-bootstrap builds use the target compiler's own
/// artifacts.
fn assembled_sysroot_std_stamp(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    target: TargetSelection,
) -> BuildStamp {
    let std_compiler = if Std::should_be_uplifted_from_stage_1(builder, target_compiler.stage) {
        builder.compiler(1, builder.host_target)
    } else {
        target_compiler
    };
    build_stamp::libstd_stamp(builder, std_compiler, target)
}

/// Prepare a compiler sysroot.
///
/// The sysroot may contain various things useful for running the compiler, like linkers and
/// linker wrappers (LLD, LLVM bitcode linker, etc.).
///
/// This will assemble a compiler in `build/$target/stage$stage`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assemble {
    /// The compiler which we will produce in this step. Assemble itself will
    /// take care of ensuring that the necessary prerequisites to do so exist,
    /// that is, this can be e.g. a stage2 compiler and Assemble will build
    /// the previous stages for you.
    pub target_compiler: Compiler,
}

impl Step for Assemble {
    type Output = Compiler;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("compiler/rustc").path("compiler")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Assemble {
            target_compiler: run.builder.compiler(run.builder.top_stage, run.target),
        });
    }

    fn run(self, builder: &Builder<'_>) -> Compiler {
        let target_compiler = self.target_compiler;

        if target_compiler.stage == 0 {
            trace!("stage 0 build compiler is always available, simply returning");
            assert_eq!(
                builder.config.host_target, target_compiler.host,
                "Cannot obtain compiler for non-native build triple at stage 0"
            );
            // The stage 0 compiler for the build triple is always pre-built.
            return target_compiler;
        }

        // We prepend this bin directory to the user PATH when linking Rust binaries. To
        // avoid shadowing the system LLD we rename the LLD we provide to `rust-lld`.
        let libdir = builder.sysroot_target_libdir(target_compiler, target_compiler.host);
        let libdir_bin = libdir.parent().unwrap().join("bin");
        t!(fs::create_dir_all(&libdir_bin));

        if builder.config.llvm_enabled(target_compiler.host) {
            trace!("target_compiler.host" = ?target_compiler.host, "LLVM enabled");

            let target = target_compiler.host;
            let llvm::LlvmResult { host_llvm_config, .. } = builder.ensure(llvm::Llvm { target });
            if !builder.config.dry_run() && builder.config.llvm_tools_enabled {
                trace!("LLVM tools enabled");

                let host_llvm_bin_dir = command(&host_llvm_config)
                    .arg("--bindir")
                    .cached()
                    .run_capture_stdout(builder)
                    .stdout()
                    .trim()
                    .to_string();

                let llvm_bin_dir = if target == builder.host_target {
                    PathBuf::from(host_llvm_bin_dir)
                } else {
                    // If we're cross-compiling, we cannot run the target llvm-config in order to
                    // figure out where binaries are located. We thus have to guess.
                    let external_llvm_config = builder
                        .config
                        .target_config
                        .get(&target)
                        .and_then(|t| t.llvm_config.clone());
                    if let Some(external_llvm_config) = external_llvm_config {
                        // If we have an external LLVM, just hope that the bindir is the directory
                        // where the LLVM config is located
                        external_llvm_config.parent().unwrap().to_path_buf()
                    } else {
                        // If we have built LLVM locally, then take the path of the host bindir
                        // relative to its output build directory, and then apply it to the target
                        // LLVM output build directory.
                        let host_llvm_out = builder.llvm_out(builder.host_target);
                        let target_llvm_out = builder.llvm_out(target);
                        if let Ok(relative_path) =
                            Path::new(&host_llvm_bin_dir).strip_prefix(host_llvm_out)
                        {
                            target_llvm_out.join(relative_path)
                        } else {
                            // This is the most desperate option, just replace the host target with
                            // the actual target in the directory path...
                            PathBuf::from(
                                host_llvm_bin_dir
                                    .replace(&*builder.host_target.triple, &target.triple),
                            )
                        }
                    }
                };

                // Since we've already built the LLVM tools, install them to the sysroot.
                // This installs the LLVM tools into the standalone sysroot so projects that
                // expect llvm tools to be present can find them without extra selector setup
                // (e.g. the `bootimage` crate).

                #[cfg(feature = "tracing")]
                let _llvm_tools_span =
                    span!(tracing::Level::TRACE, "installing llvm tools to sysroot", ?libdir_bin)
                        .entered();
                for tool in LLVM_TOOLS {
                    trace!("installing `{tool}`");
                    let tool_exe = exe(tool, target_compiler.host);
                    let src_path = llvm_bin_dir.join(&tool_exe);

                    // When using `download-ci-llvm`, some of the tools may not exist, so skip trying to copy them.
                    if !src_path.exists() && builder.config.llvm_from_ci {
                        eprintln!("{} does not exist; skipping copy", src_path.display());
                        continue;
                    }

                    // There is a chance that these tools are being installed from an external LLVM.
                    // Use `Builder::resolve_symlink_and_copy` instead of `Builder::copy_link` to ensure
                    // we are copying the original file not the symlinked path, which causes issues for
                    // tarball distribution.
                    //
                    // See https://github.com/rust-lang/rust/issues/135554.
                    builder.resolve_symlink_and_copy(&src_path, &libdir_bin.join(&tool_exe));
                }

                // External macOS LLVM tools (notably Homebrew's `llvm-objcopy`)
                // can be dynamically linked even when rustc itself uses LLVM
                // statically. Their install name is `@rpath/libLLVM.dylib` and
                // their copied binary retains `@loader_path/../lib`, so copying
                // only the executable creates a sysroot tool that aborts as
                // soon as rustc honors `-Cstrip`. Keep the runtime next to the
                // assembled tools; this is narrower than treating every system
                // LLVM library as a compiler runtime dependency.
                if target.contains("apple-darwin") && builder.config.is_system_llvm(target) {
                    let external_llvm_libdir = command(&host_llvm_config)
                        .arg("--libdir")
                        .cached()
                        .run_capture_stdout(builder)
                        .stdout()
                        .trim()
                        .to_string();
                    let external_llvm_dylib =
                        PathBuf::from(external_llvm_libdir).join("libLLVM.dylib");
                    if external_llvm_dylib.exists() {
                        builder.resolve_symlink_and_copy(
                            &external_llvm_dylib,
                            &libdir.join("libLLVM.dylib"),
                        );
                    }
                }
            }
        }

        let maybe_install_llvm_bitcode_linker = || {
            if builder.config.llvm_bitcode_linker_enabled {
                trace!("llvm-bitcode-linker enabled, installing");
                let llvm_bitcode_linker = builder.ensure(
                    crate::core::build_steps::tool::LlvmBitcodeLinker::from_target_compiler(
                        builder,
                        target_compiler,
                    ),
                );

                // Copy the llvm-bitcode-linker to the self-contained binary directory
                let bindir_self_contained = builder
                    .sysroot(target_compiler)
                    .join(format!("lib/rustlib/{}/bin/self-contained", target_compiler.host));
                let tool_exe = exe("llvm-bitcode-linker", target_compiler.host);

                t!(fs::create_dir_all(&bindir_self_contained));
                builder.copy_link(
                    &llvm_bitcode_linker.tool_path,
                    &bindir_self_contained.join(tool_exe),
                    FileType::Executable,
                );
            }
        };

        // If we're downloading a compiler from CI, we can use the same compiler for all stages other than 0.
        if builder.download_rustc() {
            trace!("`download-rustc` requested, reusing CI compiler for stage > 0");

            builder.std(target_compiler, target_compiler.host);
            let sysroot =
                builder.ensure(Sysroot { compiler: target_compiler, force_recompile: false });
            // Ensure that `libLLVM.so` ends up in the newly created target directory,
            // so that tools using `rustc_private` can use it.
            dist::maybe_install_llvm_target(builder, target_compiler.host, &sysroot);
            // Lower stages use `ci-rustc-sysroot`, not stageN
            if target_compiler.stage == builder.top_stage {
                builder.info(&format!(
                    "Creating standalone Trust sysroot for stage{stage} compiler at build/host/stage{stage}",
                    stage = target_compiler.stage
                ));
            }

            // FIXME: this is incomplete, we do not copy a bunch of other stuff to the downloaded
            // sysroot...
            maybe_install_llvm_bitcode_linker();

            return target_compiler;
        }

        // Get the compiler that we'll use to bootstrap ourselves.
        //
        // Note that this is where the recursive nature of the bootstrap
        // happens, as this will request the previous stage's compiler on
        // downwards to stage 0.
        //
        // Also note that we're building a compiler for the host platform. We
        // only assume that we can run `build` artifacts, which means that to
        // produce some other architecture compiler we need to start from
        // `build` to get there.
        //
        // FIXME: It may be faster if we build just a stage 1 compiler and then
        //        use that to bootstrap this compiler forward.
        debug!(
            "ensuring build compiler is available: compiler(stage = {}, host = {:?})",
            target_compiler.stage - 1,
            builder.config.host_target,
        );
        let build_compiler =
            builder.compiler(target_compiler.stage - 1, builder.config.host_target);

        // Build enzyme
        if builder.config.llvm_enzyme {
            debug!("`llvm_enzyme` requested");
            let enzyme = builder.ensure(llvm::Enzyme { target: build_compiler.host });
            let target_libdir =
                builder.sysroot_target_libdir(target_compiler, target_compiler.host);
            let target_dst_lib = target_libdir.join(enzyme.enzyme_filename());
            builder.copy_link(&enzyme.enzyme_path(), &target_dst_lib, FileType::NativeLibrary);
        }

        if builder.config.llvm_offload && !builder.config.dry_run() {
            debug!("`llvm_offload` requested");
            let offload_install = builder.ensure(llvm::OmpOffload { target: build_compiler.host });
            if let Some(_llvm_config) = builder.llvm_config(builder.config.host_target) {
                let target_libdir =
                    builder.sysroot_target_libdir(target_compiler, target_compiler.host);
                for p in offload_install.offload_paths() {
                    let libname = p.file_name().unwrap();
                    let dst_lib = target_libdir.join(libname);
                    builder.resolve_symlink_and_copy(&p, &dst_lib);
                }
                // FIXME(offload): Add amdgcn-amd-amdhsa and nvptx64-nvidia-cuda folder
                // This one is slightly more tricky, since we have the same file twice, in two
                // subfolders for amdgcn and nvptx64. We'll likely find two more in the future, once
                // Intel and Spir-V support lands in offload.
            }
        }

        // Build the libraries for this compiler to link to (i.e., the libraries
        // it uses at runtime).
        debug!(
            ?build_compiler,
            "target_compiler.host" = ?target_compiler.host,
            "building compiler libraries to link to"
        );

        // It is possible that an uplift has happened, so we override build_compiler here.
        let BuiltRustc { build_compiler } =
            builder.ensure(Rustc::new(build_compiler, target_compiler.host));

        let stage = target_compiler.stage;
        let host = target_compiler.host;
        let (host_info, dir_name) = if build_compiler.host == host {
            ("".into(), "host".into())
        } else {
            (format!(" ({host})"), host.to_string())
        };
        // NOTE: "Creating a sysroot" is somewhat inconsistent with our internal terminology, since
        // sysroots can temporarily be empty until we put the compiler inside. However,
        // `ensure(Sysroot)` isn't really something that's user facing, so there shouldn't be any
        // ambiguity.
        let msg = format!(
            "Creating standalone Trust sysroot for stage{stage} compiler{host_info} at build/{dir_name}/stage{stage}"
        );
        builder.info(&msg);

        // Link in all dylibs to the libdir
        let stamp = build_stamp::librustc_stamp(builder, build_compiler, target_compiler.host);
        let proc_macros = builder
            .read_stamp_file(&stamp)
            .into_iter()
            .filter_map(|(path, dependency_type)| {
                if dependency_type == DependencyType::Host {
                    Some(path.file_name().unwrap().to_owned().into_string().unwrap())
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();

        let sysroot = builder.sysroot(target_compiler);
        let rustc_libdir = builder.rustc_libdir(target_compiler);
        t!(fs::create_dir_all(&rustc_libdir));
        // Copy runtime dylibs from the authoritative full-rustc stamp. The
        // previous compiler's sysroot is mutable and may have been populated
        // by an unrelated partial build, so it is not a sufficient source of
        // truth for the driver required by these compiler aliases.
        restore_local_compiler_runtime_artifacts(
            builder,
            target_compiler,
            &sysroot,
            build_compiler,
            &stamp,
        );
        let src_libdir = builder.sysroot_target_libdir(build_compiler, host);
        for f in builder.read_dir(&src_libdir) {
            let filename = f.file_name().into_string().unwrap();

            let is_proc_macro = proc_macros.contains(&filename);
            let is_dylib_or_debug = is_dylib(&f.path()) || is_debug_info(&filename);

            // If we link statically to stdlib, do not copy the libstd dynamic library file
            // FIXME: Also do this for Windows once incremental post-optimization stage0 tests
            // work without std.dll (see https://github.com/rust-lang/rust/pull/131188).
            let can_be_rustc_dynamic_dep = if builder
                .link_std_into_rustc_driver(target_compiler.host)
                && !target_compiler.host.is_windows()
                && !target_compiler.host.contains("apple-darwin")
            {
                let is_std = filename.starts_with("std-") || filename.starts_with("libstd-");
                !is_std
            } else {
                true
            };

            if is_dylib_or_debug && can_be_rustc_dynamic_dep && !is_proc_macro {
                builder.copy_link(&f.path(), &rustc_libdir.join(&filename), FileType::Regular);
            }
        }

        if builder.config.lld_enabled {
            let lld_wrapper =
                builder.ensure(crate::core::build_steps::tool::LldWrapper::for_use_by_compiler(
                    builder,
                    target_compiler,
                ));
            copy_lld_artifacts(builder, lld_wrapper, target_compiler);
        }

        if builder.config.llvm_enabled(target_compiler.host) && builder.config.llvm_tools_enabled {
            debug!(
                "llvm and llvm tools enabled; copying `llvm-objcopy` as `rust-objcopy` to \
                workaround faulty homebrew `strip`s"
            );

            // `llvm-strip` is used by rustc, which is actually just a symlink to `llvm-objcopy`, so
            // copy and rename `llvm-objcopy`.
            //
            // But only do so if llvm-tools are enabled, as the bootstrap compiler
            // might not contain any LLVM tools.
            // See <https://github.com/rust-lang/rust/issues/132719>.
            let src_exe = exe("llvm-objcopy", target_compiler.host);
            let dst_exe = exe("rust-objcopy", target_compiler.host);
            builder.copy_link(
                &libdir_bin.join(src_exe),
                &libdir_bin.join(dst_exe),
                FileType::Executable,
            );
        }

        // In addition to `rust-lld` also install `wasm-component-ld` when
        // is enabled. This is used by the `wasm32-wasip2` target of Rust.
        if builder.tool_enabled("wasm-component-ld") {
            let wasm_component = builder.ensure(
                crate::core::build_steps::tool::WasmComponentLd::for_use_by_compiler(
                    builder,
                    target_compiler,
                ),
            );
            builder.copy_link(
                &wasm_component.tool_path,
                &libdir_bin.join(wasm_component.tool_path.file_name().unwrap()),
                FileType::Executable,
            );
        }

        maybe_install_llvm_bitcode_linker();

        // Ensure that `libLLVM.so` ends up in the newly build compiler directory,
        // so that it can be found when the newly built `rustc` is run.
        debug!(
            "target_compiler.host" = ?target_compiler.host,
            ?sysroot,
            "ensuring availability of `libLLVM.so` in compiler directory"
        );
        dist::maybe_install_llvm_runtime(builder, target_compiler.host, &sysroot);
        dist::maybe_install_llvm_target(builder, target_compiler.host, &sysroot);

        // Link the compiler binary itself into place
        let out_dir = builder.cargo_out(build_compiler, Mode::Rustc, host);
        let rustc = out_dir.join(exe("rustc-main", host));
        let bindir = sysroot.join("bin");
        t!(fs::create_dir_all(&bindir));
        let inherited_rustc = bindir.join(exe("rustc", host));
        debug!(src = ?rustc, dst = ?inherited_rustc, "linking Rust-compatible compiler alias");
        builder.copy_link(&rustc, &inherited_rustc, FileType::Executable);
        let trustc = bindir.join(exe("trustc", host));
        debug!(src = ?rustc, dst = ?trustc, "linking trustc compiler alias");
        builder.copy_link(&rustc, &trustc, FileType::Executable);

        // Build (or select an uplifted) std without linking it through the
        // build compiler's normal StdLink destination, then install that exact
        // stamp into the compiler sysroot being assembled. This is the single
        // Assemble-owned install path for stage1, full bootstrap, and uplifted
        // stage2+ alike.
        let std_stamp = builder
            .ensure(Std::new(target_compiler, host).without_sysroot_link())
            .unwrap_or_else(|| assembled_sysroot_std_stamp(builder, target_compiler, host));
        if std_stamp.path().exists() {
            let host_libdir = builder.sysroot_target_libdir(target_compiler, host);
            add_to_sysroot(builder, &host_libdir, &host_libdir, &std_stamp);
        }

        if target_compiler.stage < 2 {
            restore_user_facing_tools(builder, target_compiler, &sysroot);
        }

        if target_compiler.stage >= 2 && builder.config.extended {
            let host_libdir = builder.sysroot_target_libdir(target_compiler, host);
            prune_public_sysroot_compiler_artifacts(&host_libdir);
            // Trust: for a LOCAL self-host build (`x.py build`), re-populate the
            // standalone sysroot's target libdir with the rustc_private (rustc-dev)
            // rlibs/rmetas that `prune_public_sysroot_compiler_artifacts` just
            // removed, so Trust's own rustc-driver tools (trust-vc, trust-wp, and a
            // Trust-with-Trust rebuild) can link rustc_private WITHOUT a manual
            // `component add rustc-dev` step. This is the in-bootstrap replacement
            // for the former scripts/restore-rustc-dev.sh, which post-copied the
            // same stamp libs after every build.
            //
            // Gated to `Kind::Build` so this is confined to the developer's local
            // toolchain: `x.py dist`/`install` images and the `x.py test` sysroots
            // keep the clean, upstream-#108767 pruned sysroot (dist ships rustc-dev
            // as the separate `trustc-dev` component, and the shared stage2 sysroot
            // it copies from — dist.rs `Rustc` — must not double-bundle these).
            // Reuses the librustc `stamp` read above and the same routing helper
            // (`add_rustc_to_sysroot`, with its duplicate-rustc-crate guard) that
            // the rustc-private sysroot path uses; copies exactly what
            // restore-rustc-dev.sh copied (whole stamp -> target libdir).
            if builder.kind == Kind::Build {
                add_rustc_to_sysroot(builder, &host_libdir, &host_libdir, &stamp);
            }
            crate::core::build_steps::tool::ensure_user_facing_tools(
                builder,
                target_compiler,
                &sysroot,
            );
        }

        validate_assembled_local_compiler(builder, target_compiler, &sysroot);

        target_compiler
    }
}

/// Link some files into a rustc sysroot.
///
/// For a particular stage this will link the file listed in `stamp` into the
/// `sysroot_dst` provided.
#[track_caller]
pub fn add_to_sysroot(
    builder: &Builder<'_>,
    sysroot_dst: &Path,
    sysroot_host_dst: &Path,
    stamp: &BuildStamp,
) {
    add_to_sysroot_with_metadata_mode(
        builder,
        sysroot_dst,
        sysroot_host_dst,
        stamp,
        SysrootMetadataMode::Deduplicate,
    );
}

fn add_rustc_to_sysroot(
    builder: &Builder<'_>,
    sysroot_dst: &Path,
    sysroot_host_dst: &Path,
    stamp: &BuildStamp,
) {
    add_to_sysroot_with_metadata_mode(
        builder,
        sysroot_dst,
        sysroot_host_dst,
        stamp,
        SysrootMetadataMode::PreserveMetadataOnlyDeps,
    );
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SysrootMetadataMode {
    Deduplicate,
    PreserveMetadataOnlyDeps,
}

#[track_caller]
fn add_to_sysroot_with_metadata_mode(
    builder: &Builder<'_>,
    sysroot_dst: &Path,
    sysroot_host_dst: &Path,
    stamp: &BuildStamp,
    metadata_mode: SysrootMetadataMode,
) {
    let self_contained_dst = &sysroot_dst.join("self-contained");
    t!(fs::create_dir_all(sysroot_dst));
    t!(fs::create_dir_all(sysroot_host_dst));
    t!(fs::create_dir_all(self_contained_dst));

    let mut crates = HashMap::new();
    let stamp_entries = builder.read_stamp_file(stamp);
    let rlib_stems_in_stamp = stamp_entries
        .iter()
        .filter_map(|(path, dependency_type)| {
            let filename = path.file_name().unwrap().to_str().unwrap();
            let artifact = parse_hashed_rust_artifact(filename)?;
            (artifact.kind == RustArtifactKind::Rlib).then(|| {
                (
                    sysroot_destination(
                        sysroot_dst,
                        sysroot_host_dst,
                        self_contained_dst,
                        *dependency_type,
                    )
                    .to_path_buf(),
                    artifact.stem.to_owned(),
                )
            })
        })
        .collect::<HashSet<_>>();

    for (path, dependency_type) in stamp_entries {
        let filename = path.file_name().unwrap().to_str().unwrap();
        let dst = match dependency_type {
            DependencyType::Host => {
                if sysroot_dst == sysroot_host_dst {
                    // Only insert the part before the . to deduplicate different files for the same crate.
                    // For example foo-1234.dll and foo-1234.dll.lib.
                    crates.insert(filename.split_once('.').unwrap().0.to_owned(), path.clone());
                }

                sysroot_host_dst
            }
            DependencyType::Target => {
                // Only insert the part before the . to deduplicate different files for the same crate.
                // For example foo-1234.dll and foo-1234.dll.lib.
                crates.insert(filename.split_once('.').unwrap().0.to_owned(), path.clone());

                sysroot_dst
            }
            DependencyType::TargetSelfContained => self_contained_dst,
        };

        if let Some(artifact) = parse_hashed_rust_artifact(filename)
            && !prepare_sysroot_artifact_for_copy(
                &path,
                dst,
                artifact,
                metadata_mode,
                &rlib_stems_in_stamp,
            )
        {
            continue;
        }

        builder.copy_link(&path, &dst.join(filename), FileType::Regular);
    }

    // Check that none of the rustc_* crates have multiple versions. Otherwise using them from
    // the sysroot would cause ambiguity errors. We do allow rustc_hash however as it is an
    // external dependency that we build multiple copies of. It is re-exported by
    // rustc_data_structures, so not being able to use extern crate rustc_hash; is not a big
    // issue.
    let mut seen_crates = HashMap::new();
    for (filestem, path) in crates {
        let Some(crate_and_hash) = filestem.strip_prefix("lib") else { continue };
        let Some((crate_name, hash)) = crate_and_hash.rsplit_once('-') else { continue };
        if crate_name.is_empty() || hash.is_empty() || !is_rustc_private_crate(crate_name) {
            continue;
        }
        if let Some(other_path) = seen_crates.insert(crate_name.to_owned(), path.clone()) {
            panic!(
                "duplicate rustc crate {}\n-  first copy at {}\n- second copy at {}",
                crate_name,
                other_path.display(),
                path.display(),
            );
        }
    }
}

pub fn prepare_rustc_private_sysroot(
    builder: &Builder<'_>,
    rustc_build_compiler: Compiler,
    target: TargetSelection,
    label: &str,
) -> Option<(PathBuf, PathBuf)> {
    prepare_rustc_private_sysroot_with_runtime_identity(
        builder,
        rustc_build_compiler,
        target,
        label,
        None,
    )
}

/// Prepare the private sysroot used to link an installed rustc-private tool.
///
/// Unlike metadata-only consumers, an installed tool loads its owning
/// compiler's dylibs at runtime. Those dylibs can be rebuilt in place without
/// changing their paths, crate disambiguators, or the librustc stamp. Bind the
/// private sysroot path handed to Cargo to their actual bytes. Tool bootstrap
/// passes that path both through the shim compatibility channel and as a
/// Cargo-tracked `-Lall` flag, so an in-place rebuild invalidates the tool.
pub(crate) fn prepare_rustc_private_tool_sysroot(
    builder: &Builder<'_>,
    rustc_build_compiler: Compiler,
    runtime_compiler: Compiler,
    target: TargetSelection,
    label: &str,
) -> Option<(PathBuf, PathBuf)> {
    let stamp = build_stamp::librustc_stamp(builder, rustc_build_compiler, target);
    if !stamp.path().exists() || builder.config.dry_run() {
        return prepare_rustc_private_sysroot(builder, rustc_build_compiler, target, label);
    }

    let mut runtime_paths = builder.rustc_lib_paths(runtime_compiler);
    let target_runtime_libdir = builder.sysroot_target_libdir(runtime_compiler, target);
    runtime_paths.push(target_runtime_libdir);
    runtime_paths.dedup();
    let runtime_dylibs = runtime_paths
        .iter()
        .flat_map(|path| rustc_private_runtime_dylibs(path))
        .collect::<Vec<_>>();
    assert!(
        !runtime_dylibs.is_empty(),
        "cannot build a rustc-private tool for stage{} compiler ({}): \
         no runtime dylibs found in runtime search paths: {}",
        runtime_compiler.stage,
        runtime_compiler.host,
        runtime_paths.iter().map(|path| path.display().to_string()).collect::<Vec<_>>().join(", "),
    );
    let runtime_identity = rustc_private_runtime_dylib_identity(runtime_dylibs);

    prepare_rustc_private_sysroot_with_runtime_identity(
        builder,
        rustc_build_compiler,
        target,
        label,
        Some(&runtime_identity),
    )
}

fn prepare_rustc_private_sysroot_with_runtime_identity(
    builder: &Builder<'_>,
    rustc_build_compiler: Compiler,
    target: TargetSelection,
    label: &str,
    runtime_identity: Option<&str>,
) -> Option<(PathBuf, PathBuf)> {
    let stamp = build_stamp::librustc_stamp(builder, rustc_build_compiler, target);
    if !stamp.path().exists() {
        return None;
    }

    let compiler_commit_hash = if builder.config.dry_run() {
        None
    } else {
        let mut rustc_version = builder.rustc_cmd(rustc_build_compiler);
        rustc_version.arg("-vV");
        let verbose_version = rustc_version.run_capture_stdout(builder).stdout();
        Some(
            rustc_commit_hash_from_verbose_version(&verbose_version)
                .unwrap_or_else(|| panic!("rustc -vV omitted commit-hash:\n{verbose_version}"))
                .to_owned(),
        )
    };

    // The private sysroot is also a real nested-driver sysroot: below we copy
    // every regular target std artifact into it. Include those bytes in the
    // directory identity as well. Otherwise an in-place std rebuild would
    // select an old directory and the `!dst.exists()` copy guard would retain
    // stale core/std artifacts.
    let std_src = builder.sysroot_target_libdir(rustc_build_compiler, target);
    let std_files = rustc_private_copied_std_files(&std_src);
    let copied_std_identity =
        (!std_files.is_empty()).then(|| rustc_private_copied_std_identity(std_files.clone()));
    let key = rustc_private_sysroot_key(
        builder,
        &stamp,
        compiler_commit_hash.as_deref(),
        runtime_identity,
        copied_std_identity.as_deref(),
    );
    let directory_name =
        format!("{}-stage{}-{}-{}", label, rustc_build_compiler.stage, target.triple, key);
    let directory = builder
        .out
        .join(rustc_build_compiler.host.triple)
        .join("rustc-private-sysroots")
        .join(directory_name);
    let host_dir = directory.join("host");
    let target_dir = directory.join(target);
    add_rustc_to_sysroot(builder, &target_dir, &host_dir, &stamp);

    // A rustc crate hash is not a complete metadata-compatibility identity.
    // In particular, the filename of `librustc_driver` can remain unchanged
    // across source commits that do not alter that crate, while rustc still
    // rejects metadata produced by the other compiler as E0514.  Record the
    // exact compiler commit that produced this private sysroot so out-of-tree
    // rustc-driver tools can select it without guessing from filenames.
    if let Some(commit_hash) = compiler_commit_hash {
        t!(fs::write(directory.join(".rustc-commit-hash"), format!("{commit_hash}\n")));
    }

    // Trust: fulldeps rustc_public/* tests spawn INNER compilations via the
    // rustc_driver API. Those detect their sysroot from the loaded
    // librustc_driver dylib (rustc_session::filesearch::default_from_rustc_driver_dll):
    // two parents up from `<directory>/host/librustc_driver.dylib` == `<directory>`.
    // For the inner compilation to find `std`/`core`, `<directory>` must be a real
    // sysroot layout, so populate `<directory>/lib/rustlib/<target>/lib` with the
    // build compiler's target std — exactly the layout upstream's rustc-dev-over-
    // sysroot provides. The OUTER test compilation still gets std from its own
    // `--sysroot`; this is purely for the nested driver invocations.
    if !std_files.is_empty() {
        let std_dst = directory.join("lib").join("rustlib").join(target.triple).join("lib");
        t!(fs::create_dir_all(&std_dst));
        for path in std_files {
            let dst = std_dst.join(path.file_name().unwrap());
            if !dst.exists() {
                builder.copy_link(&path, &dst, FileType::Regular);
            }
        }
    }

    Some((host_dir, target_dir))
}

fn rustc_commit_hash_from_verbose_version(verbose_version: &str) -> Option<&str> {
    verbose_version
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .filter(|hash| !hash.is_empty())
}

fn rustc_private_sysroot_key(
    builder: &Builder<'_>,
    stamp: &BuildStamp,
    compiler_commit_hash: Option<&str>,
    runtime_identity: Option<&str>,
    copied_std_identity: Option<&str>,
) -> String {
    rustc_private_sysroot_key_from_entries(
        stamp.path(),
        compiler_commit_hash,
        builder.read_stamp_file(stamp),
        runtime_identity,
        copied_std_identity,
    )
}

fn rustc_private_sysroot_key_from_entries(
    stamp_path: &Path,
    compiler_commit_hash: Option<&str>,
    mut entries: Vec<(PathBuf, DependencyType)>,
    runtime_identity: Option<&str>,
    copied_std_identity: Option<&str>,
) -> String {
    entries.sort_by(|(left_path, left_kind), (right_path, right_kind)| {
        left_path.cmp(right_path).then(left_kind.cmp(right_kind))
    });

    let mut hasher = DefaultHasher::new();
    stamp_path.hash(&mut hasher);
    compiler_commit_hash.hash(&mut hasher);
    runtime_identity.hash(&mut hasher);
    copied_std_identity.hash(&mut hasher);
    for (path, dependency_type) in entries {
        path.hash(&mut hasher);
        match dependency_type {
            DependencyType::Host => 0_u8,
            DependencyType::Target => 1,
            DependencyType::TargetSelfContained => 2,
        }
        .hash(&mut hasher);
    }
    format!("{:016x}", hasher.finish())
}

fn rustc_private_runtime_dylibs(runtime_libdir: &Path) -> Vec<PathBuf> {
    let mut dylibs = fs::read_dir(runtime_libdir)
        .unwrap_or_else(|error| {
            panic!(
                "failed to enumerate rustc-private tool runtime `{}`: {error}",
                runtime_libdir.display()
            )
        })
        .map(|entry| {
            entry
                .unwrap_or_else(|error| {
                    panic!(
                        "failed to read an entry in rustc-private tool runtime `{}`: {error}",
                        runtime_libdir.display()
                    )
                })
                .path()
        })
        .filter(|path| is_dylib(path))
        .collect::<Vec<_>>();
    dylibs.sort();
    dylibs
}

fn rustc_private_runtime_dylib_identity(mut dylibs: Vec<PathBuf>) -> String {
    // Recompute the bytes at every call. A metadata-based cache would be
    // cheaper, but could reproduce the original bug if a compiler runtime is
    // replaced between two tool builds in one bootstrap invocation.
    rustc_private_files_identity(b"trust-rustc-private-runtime-dylibs-v1\0", &mut dylibs)
}

fn rustc_private_copied_std_files(std_libdir: &Path) -> Vec<PathBuf> {
    if !std_libdir.is_dir() {
        return Vec::new();
    }

    let mut files = fs::read_dir(std_libdir)
        .unwrap_or_else(|error| {
            panic!(
                "failed to enumerate rustc-private nested-driver std `{}`: {error}",
                std_libdir.display()
            )
        })
        .filter_map(|entry| {
            let entry = entry.unwrap_or_else(|error| {
                panic!(
                    "failed to read an entry in rustc-private nested-driver std `{}`: {error}",
                    std_libdir.display()
                )
            });
            entry.file_type().map(|kind| kind.is_file()).unwrap_or(false).then(|| entry.path())
        })
        .collect::<Vec<_>>();
    files.sort();
    files
}

fn rustc_private_copied_std_identity(mut files: Vec<PathBuf>) -> String {
    rustc_private_files_identity(b"trust-rustc-private-copied-std-v1\0", &mut files)
}

fn rustc_private_files_identity(domain: &[u8], files: &mut Vec<PathBuf>) -> String {
    files.sort();
    files.dedup();

    let mut identity = sha2::Sha256::new();
    identity.update(domain);
    for path in files {
        let encoded_path = path.as_os_str().as_encoded_bytes();
        identity.update((encoded_path.len() as u64).to_le_bytes());
        identity.update(encoded_path);

        let mut file = BufReader::new(fs::File::open(&path).unwrap_or_else(|error| {
            panic!("failed to open rustc-private input `{}`: {error}", path.display())
        }));
        let mut contents = sha2::Sha256::new();
        let mut buffer = [0_u8; 64 * 1024];
        loop {
            let read = file.read(&mut buffer).unwrap_or_else(|error| {
                panic!("failed to hash rustc-private input `{}`: {error}", path.display())
            });
            if read == 0 {
                break;
            }
            contents.update(&buffer[..read]);
        }
        identity.update(contents.finalize());
    }

    hex_encode(identity.finalize().as_slice())
}

fn sysroot_destination<'a>(
    sysroot_dst: &'a Path,
    sysroot_host_dst: &'a Path,
    self_contained_dst: &'a Path,
    dependency_type: DependencyType,
) -> &'a Path {
    match dependency_type {
        DependencyType::Host => sysroot_host_dst,
        DependencyType::Target => sysroot_dst,
        DependencyType::TargetSelfContained => self_contained_dst,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RustArtifactKind {
    Dylib,
    Rlib,
    Rmeta,
}

struct RustArtifact<'a> {
    crate_name: &'a str,
    stem: &'a str,
    kind: RustArtifactKind,
}

fn parse_hashed_rust_artifact(filename: &str) -> Option<RustArtifact<'_>> {
    let (stem, extension) = filename.rsplit_once('.')?;
    let kind = match extension {
        "dylib" | "dll" | "so" => RustArtifactKind::Dylib,
        "rlib" => RustArtifactKind::Rlib,
        "rmeta" => RustArtifactKind::Rmeta,
        _ => return None,
    };
    let crate_and_hash = stem.strip_prefix("lib")?;
    let (crate_name, hash) = crate_and_hash.rsplit_once('-')?;
    if crate_name.is_empty() || hash.is_empty() {
        return None;
    }
    Some(RustArtifact { crate_name, stem, kind })
}

fn is_rustc_private_crate(crate_name: &str) -> bool {
    crate_name.starts_with("rustc_")
        && crate_name != "rustc_demangle"
        && crate_name != "rustc_hash"
        && crate_name != "rustc_literal_escaper"
        && !crate_name.starts_with("rustc_std_workspace_")
}

fn should_deduplicate_sysroot_metadata(crate_name: &str) -> bool {
    // Compiler crates intentionally flow through sysroots as metadata for
    // rustc_private tools. External and standard-library crates must not keep
    // metadata-only siblings once an rlib for the same crate is present, because
    // that makes an rlib dependency resolve ambiguously.
    !is_rustc_private_crate(crate_name)
}

fn prune_stale_sysroot_metadata(dst: &Path, crate_name: &str, active_stem: &str) {
    prune_stale_sysroot_artifact_kind(dst, crate_name, active_stem, RustArtifactKind::Rmeta);
}

fn prune_stale_sysroot_artifact_kind(
    dst: &Path,
    crate_name: &str,
    active_stem: &str,
    active_kind: RustArtifactKind,
) {
    for entry in t!(fs::read_dir(dst)) {
        let entry = t!(entry);
        let filename = entry.file_name();
        let Some(filename) = filename.to_str() else { continue };
        let Some(candidate) = parse_hashed_rust_artifact(filename) else { continue };
        if candidate.kind == active_kind
            && candidate.crate_name == crate_name
            && candidate.stem != active_stem
        {
            trace!(
                path = ?entry.path(),
                crate_name,
                active_stem,
                "removing stale sysroot artifact"
            );
            t!(fs::remove_file(entry.path()));
        }
    }
}

fn sysroot_has_different_rlib_for_crate(dst: &Path, crate_name: &str, metadata_stem: &str) -> bool {
    for entry in t!(fs::read_dir(dst)) {
        let entry = t!(entry);
        let filename = entry.file_name();
        let Some(filename) = filename.to_str() else { continue };
        let Some(candidate) = parse_hashed_rust_artifact(filename) else { continue };
        if candidate.kind == RustArtifactKind::Rlib
            && candidate.crate_name == crate_name
            && candidate.stem != metadata_stem
        {
            return true;
        }
    }
    false
}

fn sysroot_has_matching_rlib(dst: &Path, stem: &str) -> bool {
    dst.join(format!("{stem}.rlib")).exists()
}

fn sysroot_has_matching_public_dylib(dst: &Path, crate_name: &str, stem: &str) -> bool {
    if !is_public_sysroot_dylib_crate(crate_name) {
        return false;
    }

    ["dylib", "dll", "so"].iter().any(|extension| dst.join(format!("{stem}.{extension}")).exists())
}

fn is_public_sysroot_dylib_crate(crate_name: &str) -> bool {
    matches!(crate_name, "std" | "test" | "proc_macro")
}

fn should_prune_public_sysroot_artifact(dst: &Path, artifact: RustArtifact<'_>) -> bool {
    if is_rustc_private_crate(artifact.crate_name) {
        return true;
    }

    match artifact.kind {
        RustArtifactKind::Rmeta => {
            !sysroot_has_matching_rlib(dst, artifact.stem)
                && !sysroot_has_matching_public_dylib(dst, artifact.crate_name, artifact.stem)
        }
        RustArtifactKind::Dylib => !is_public_sysroot_dylib_crate(artifact.crate_name),
        RustArtifactKind::Rlib => false,
    }
}

fn prune_public_sysroot_compiler_artifacts(dst: &Path) {
    if !dst.exists() {
        return;
    }

    for entry in t!(fs::read_dir(dst)) {
        let entry = t!(entry);
        let filename = entry.file_name();
        let Some(filename) = filename.to_str() else { continue };
        let Some(artifact) = parse_hashed_rust_artifact(filename) else { continue };
        if should_prune_public_sysroot_artifact(dst, artifact) {
            trace!(path = ?entry.path(), "removing private compiler artifact from public sysroot");
            t!(fs::remove_file(entry.path()));
        }
    }
}

fn prepare_sysroot_artifact_for_copy(
    _path: &Path,
    dst: &Path,
    artifact: RustArtifact<'_>,
    metadata_mode: SysrootMetadataMode,
    rlib_stems_in_stamp: &HashSet<(PathBuf, String)>,
) -> bool {
    if is_rustc_private_crate(artifact.crate_name) {
        prune_stale_sysroot_artifact_kind(dst, artifact.crate_name, artifact.stem, artifact.kind);
        return true;
    }

    if !should_deduplicate_sysroot_metadata(artifact.crate_name) {
        return true;
    }

    match artifact.kind {
        RustArtifactKind::Rlib => {
            prune_stale_sysroot_metadata(dst, artifact.crate_name, artifact.stem);
        }
        RustArtifactKind::Rmeta => {
            if metadata_mode == SysrootMetadataMode::Deduplicate
                && !rlib_stems_in_stamp.contains(&(dst.to_path_buf(), artifact.stem.to_owned()))
                && sysroot_has_different_rlib_for_crate(dst, artifact.crate_name, artifact.stem)
            {
                trace!(
                    path = ?_path,
                    ?dst,
                    "skipping metadata-only sysroot artifact with a different rlib already present"
                );
                return false;
            }
        }
        RustArtifactKind::Dylib => {}
    }

    true
}

#[cfg(test)]
mod tests;

/// Specifies which rlib/rmeta artifacts outputted by Cargo should be put into the resulting
/// build stamp, and thus be included in dist archives and copied into sysroots by default.
/// Note that some kinds of artifacts are copied automatically (e.g. native libraries).
pub enum ArtifactKeepMode {
    /// Only keep .rlib files, ignore .rmeta files
    OnlyRlib,
    /// Only keep .rmeta files, ignore .rlib files
    OnlyRmeta,
    /// Keep both .rlib and .rmeta files.
    /// This is essentially only useful when using `-Zno-embed-metadata`, in which case both the
    /// .rlib and .rmeta files are needed for compilation/linking.
    BothRlibAndRmeta,
    /// Custom logic for keeping an artifact
    /// It receives the filename of an artifact, and returns true if it should be kept.
    Custom(Box<dyn Fn(&str) -> bool>),
}

pub fn run_cargo(
    builder: &Builder<'_>,
    cargo: Cargo,
    tail_args: Vec<String>,
    stamp: &BuildStamp,
    additional_target_deps: Vec<(PathBuf, DependencyType)>,
    artifact_keep_mode: ArtifactKeepMode,
) -> Vec<PathBuf> {
    // `target_root_dir` looks like $dir/$target/release
    let target_root_dir = stamp.path().parent().unwrap();
    // `target_build_dir` looks like $dir/$target/release/build
    let target_build_dir = target_root_dir.join("build");
    // `host_root_dir` looks like $dir/release
    let host_root_dir = target_root_dir
        .parent()
        .unwrap() // chop off `release`
        .parent()
        .unwrap() // chop off `$target`
        .join(target_root_dir.file_name().unwrap());

    // Spawn Cargo slurping up its JSON output. We'll start building up the
    // `deps` array of all files it generated along with a `toplevel` array of
    // files we need to probe for later.
    let mut deps = Vec::new();
    let mut toplevel = Vec::new();
    let ok = stream_cargo(builder, cargo, tail_args, &mut |msg| {
        let (filenames_vec, crate_types) = match msg {
            CargoMessage::CompilerArtifact {
                filenames,
                target: CargoTarget { crate_types },
                ..
            } => {
                let mut f: Vec<String> = filenames.into_iter().map(|s| s.into_owned()).collect();
                f.sort(); // Sort the filenames
                (f, crate_types)
            }
            _ => return,
        };
        for filename in filenames_vec {
            // Skip files like executables
            let keep = if filename.ends_with(".lib")
                || filename.ends_with(".a")
                || is_debug_info(&filename)
                || is_dylib(Path::new(&*filename))
            {
                // Always keep native libraries, rust dylibs and debuginfo
                true
            } else {
                match &artifact_keep_mode {
                    ArtifactKeepMode::OnlyRlib => filename.ends_with(".rlib"),
                    ArtifactKeepMode::OnlyRmeta => filename.ends_with(".rmeta"),
                    ArtifactKeepMode::BothRlibAndRmeta => {
                        filename.ends_with(".rmeta") || filename.ends_with(".rlib")
                    }
                    ArtifactKeepMode::Custom(func) => func(&filename),
                }
            };

            if !keep {
                continue;
            }

            let filename = Path::new(&*filename);

            // If this was an output file in the "host dir" we don't actually
            // worry about it, it's not relevant for us
            if filename.starts_with(&host_root_dir) {
                // Unless it's a proc macro used in the compiler
                if crate_types.iter().any(|t| t == "proc-macro") {
                    // Cargo will compile proc-macros that are part of the rustc workspace twice.
                    // Once as libmacro-hash.so as build dependency and once as libmacro.so as
                    // output artifact. Only keep the former to avoid ambiguity when trying to use
                    // the proc macro from the sysroot.
                    if filename.file_name().unwrap().to_str().unwrap().contains("-") {
                        deps.push((filename.to_path_buf(), DependencyType::Host));
                    }
                }
                continue;
            }

            // If this was output in the `deps` dir then this is a precise file
            // name (hash included) so we start tracking it.
            if filename.starts_with(&target_build_dir) {
                deps.push((filename.to_path_buf(), DependencyType::Target));
                continue;
            }

            // Otherwise this was a "top level artifact" which right now doesn't
            // have a hash in the name, but there's a version of this file in
            // the `deps` folder which *does* have a hash in the name. That's
            // the one we'll want to we'll probe for it later.
            //
            // We do not use `Path::file_stem` or `Path::extension` here,
            // because some generated files may have multiple extensions e.g.
            // `std-<hash>.dll.lib` on Windows. The aforementioned methods only
            // split the file name by the last extension (`.lib`) while we need
            // to split by all extensions (`.dll.lib`).
            let top_level_path = filename.to_path_buf();
            let expected_len = t!(filename.metadata()).len();
            let filename = filename.file_name().unwrap().to_str().unwrap();
            let mut parts = filename.splitn(2, '.');
            let file_stem = parts.next().unwrap().to_owned();
            let extension = parts.next().unwrap().to_owned();

            toplevel.push((top_level_path, file_stem, extension, expected_len));
        }
    });

    if !ok {
        crate::exit!(1);
    }

    if builder.config.dry_run() {
        return Vec::new();
    }

    // Ok now we need to actually find all the files listed in `toplevel`. We've
    // got a list of prefix/extensions and we need to find the hashed copy in
    // the `build` folder corresponding to each top-level artifact.
    //
    // Cargo's build folder is structured as `build/<pkg>/<hash>/out/<artifacts>` so
    // we need to traverse multiple directory layers to get to actual files.
    let read_dir = |path: &Path| path.read_dir().ok().into_iter().flatten().filter_map(Result::ok);
    let contents = target_build_dir
        .read_dir()
        .unwrap_or_else(|e| panic!("Couldn't read {}: {}", target_build_dir.display(), e))
        .map(|e| e.unwrap())
        .flat_map(|e| read_dir(&e.path()))
        .flat_map(|e| read_dir(&e.path()))
        .flat_map(|e| read_dir(&e.path()))
        .map(|e| (e.path(), e.file_name().into_string().unwrap(), t!(e.metadata())))
        .collect::<Vec<_>>();
    for (top_level_path, prefix, extension, expected_len) in toplevel {
        let candidates = contents
            .iter()
            .filter(|&(_, filename, meta)| {
                meta.len() == expected_len
                    && filename
                        .strip_prefix(&prefix[..])
                        .map(|s| s.starts_with('-') && s.ends_with(&extension[..]))
                        .unwrap_or(false)
            })
            .collect::<Vec<_>>();
        let path_to_add = resolve_top_level_artifact(
            &top_level_path,
            &prefix,
            &extension,
            expected_len,
            &candidates,
        );
        if is_dylib(path_to_add) {
            let candidate = format!("{}.lib", path_to_add.display());
            let candidate = PathBuf::from(candidate);
            if candidate.exists() {
                deps.push((candidate, DependencyType::Target));
            }
        }
        deps.push((path_to_add.to_path_buf(), DependencyType::Target));
    }

    deps.extend(additional_target_deps);
    deps.sort();
    let mut new_contents = Vec::new();
    for (dep, dependency_type) in deps.iter() {
        new_contents.extend(match *dependency_type {
            DependencyType::Host => b"h",
            DependencyType::Target => b"t",
            DependencyType::TargetSelfContained => b"s",
        });
        new_contents.extend(dep.to_str().unwrap().as_bytes());
        new_contents.extend(b"\0");
    }
    t!(fs::write(stamp.path(), &new_contents));
    deps.into_iter().map(|(d, _)| d).collect()
}

fn resolve_top_level_artifact<'a>(
    top_level_path: &Path,
    prefix: &str,
    extension: &str,
    expected_len: u64,
    candidates: &[&'a (PathBuf, String, fs::Metadata)],
) -> &'a Path {
    if candidates.is_empty() {
        panic!("no output generated for {prefix:?} {extension:?}");
    }

    let mut byte_matches = Vec::new();
    for candidate in candidates {
        let (path, _, _) = *candidate;
        if files_are_equal(top_level_path, path).unwrap_or_else(|e| {
            panic!(
                "failed to compare top-level artifact {} with deps artifact {}: {e}",
                top_level_path.display(),
                path.display()
            )
        }) {
            byte_matches.push(*candidate);
        }
    }

    if let Some((path, _, _)) = byte_matches.into_iter().max_by_key(|(_, _, metadata)| {
        metadata.modified().expect("mtime should be available on all relevant OSes")
    }) {
        return path;
    }

    let candidates = candidates
        .iter()
        .map(|(path, _, metadata)| format!("{} ({} bytes)", path.display(), metadata.len()))
        .collect::<Vec<_>>()
        .join(", ");
    panic!(
        "no deps output matched top-level artifact bytes for {} \
         ({prefix:?} {extension:?}, {expected_len} bytes); candidates: {candidates}",
        top_level_path.display()
    );
}

fn files_are_equal(left: &Path, right: &Path) -> std::io::Result<bool> {
    let left_metadata = fs::metadata(left)?;
    let right_metadata = fs::metadata(right)?;
    if left_metadata.len() != right_metadata.len() {
        return Ok(false);
    }

    let mut left_file = BufReader::new(fs::File::open(left)?);
    let mut right_file = BufReader::new(fs::File::open(right)?);
    let mut left_buf = [0; 64 * 1024];
    let mut right_buf = [0; 64 * 1024];

    loop {
        let left_read = left_file.read(&mut left_buf)?;
        let right_read = right_file.read(&mut right_buf)?;
        if left_read != right_read {
            return Ok(false);
        }
        if left_read == 0 {
            return Ok(true);
        }
        if left_buf[..left_read] != right_buf[..right_read] {
            return Ok(false);
        }
    }
}

pub fn stream_cargo(
    builder: &Builder<'_>,
    cargo: Cargo,
    tail_args: Vec<String>,
    cb: &mut dyn FnMut(CargoMessage<'_>),
) -> bool {
    let mut cmd = cargo.into_cmd();

    // Instruct Cargo to give us json messages on stdout, critically leaving
    // stderr as piped so we can get those pretty colors.
    let mut message_format = if builder.config.json_output {
        String::from("json")
    } else {
        String::from("json-render-diagnostics")
    };
    if let Some(s) = &builder.config.rustc_error_format {
        message_format.push_str(",json-diagnostic-");
        message_format.push_str(s);
    }
    cmd.arg("--message-format").arg(message_format);

    for arg in tail_args {
        cmd.arg(arg);
    }

    builder.do_if_verbose(|| println!("running: {cmd:?}"));

    let streaming_command = cmd.stream_capture_stdout(&builder.config.exec_ctx);

    let Some(mut streaming_command) = streaming_command else {
        return true;
    };

    // Spawn Cargo slurping up its JSON output. We'll start building up the
    // `deps` array of all files it generated along with a `toplevel` array of
    // files we need to probe for later.
    let stdout = BufReader::new(streaming_command.stdout.take().unwrap());
    for line in stdout.lines() {
        let line = t!(line);
        match serde_json::from_str::<CargoMessage<'_>>(&line) {
            Ok(msg) => {
                if builder.config.json_output {
                    // Forward JSON to stdout.
                    println!("{line}");
                }
                cb(msg)
            }
            // If this was informational, just print it out and continue
            Err(_) => println!("{line}"),
        }
    }

    // Make sure Cargo actually succeeded after we read all of its stdout.
    let status = t!(streaming_command.wait(&builder.config.exec_ctx));
    if builder.is_verbose() && !status.success() {
        eprintln!(
            "command did not execute successfully: {cmd:?}\n\
                  expected success, got: {status}"
        );
    }

    status.success()
}

#[derive(Deserialize)]
pub struct CargoTarget<'a> {
    crate_types: Vec<Cow<'a, str>>,
}

#[derive(Deserialize)]
#[serde(tag = "reason", rename_all = "kebab-case")]
pub enum CargoMessage<'a> {
    CompilerArtifact { filenames: Vec<Cow<'a, str>>, target: CargoTarget<'a> },
    BuildScriptExecuted,
    BuildFinished,
}

pub fn strip_debug(builder: &Builder<'_>, target: TargetSelection, path: &Path) {
    // FIXME: to make things simpler for now, limit this to the host and target where we know
    // `strip -g` is both available and will fix the issue, i.e. on a x64 linux host that is not
    // cross-compiling. Expand this to other appropriate targets in the future.
    if target != "x86_64-unknown-linux-gnu"
        || !builder.config.is_host_target(target)
        || !path.exists()
    {
        return;
    }

    let previous_mtime = t!(t!(path.metadata()).modified());
    let stamp = BuildStamp::new(path.parent().unwrap())
        .with_prefix(path.file_name().unwrap().to_str().unwrap())
        .with_prefix("strip")
        .add_stamp(previous_mtime.duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos());

    // Running strip can be relatively expensive (~1s on librustc_driver.so), so we don't rerun it
    // if the file is unchanged.
    if !stamp.is_up_to_date() {
        command("strip").arg("--strip-debug").arg(path).run_capture(builder);
    }
    t!(stamp.write());

    let file = t!(fs::File::open(path));

    // After running `strip`, we have to set the file modification time to what it was before,
    // otherwise we risk Cargo invalidating its fingerprint and rebuilding the world next time
    // bootstrap is invoked.
    //
    // An example of this is if we run this on librustc_driver.so. In the first invocation:
    // - Cargo will build librustc_driver.so (mtime of 1)
    // - Cargo will build rustc-main (mtime of 2)
    // - Bootstrap will strip librustc_driver.so (changing the mtime to 3).
    //
    // In the second invocation of bootstrap, Cargo will see that the mtime of librustc_driver.so
    // is greater than the mtime of rustc-main, and will rebuild rustc-main. That will then cause
    // everything else (standard library, future stages...) to be rebuilt.
    t!(file.set_modified(previous_mtime));
}

/// We only use LTO for stage 2+, to speed up build time of intermediate stages.
pub fn is_lto_stage(build_compiler: &Compiler) -> bool {
    build_compiler.stage != 0
}
