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
use std::sync::{LazyLock, Mutex};
use std::time::SystemTime;
use std::{env, fs, str};

use serde_derive::Deserialize;
use sha2::Digest;
#[cfg(feature = "tracing")]
use tracing::span;

use crate::core::backend::CodegenBackendKind;
use crate::core::build_steps::llvm::{LlvmFromCi, LlvmKind, prebuilt_llvm_output};
use crate::core::build_steps::tool::{SourceType, copy_lld_artifacts};
use crate::core::build_steps::{dist, llvm};
use crate::core::builder::{
    self, Builder, Cargo, CommandLineStep, Kind, RunConfig, ShouldRun, Step, StepMetadata,
    apply_pgo, crate_description,
};
use crate::core::compiler::Compiler;
use crate::core::config::toml::target::DefaultLinuxLinkerOverride;
use crate::core::config::{
    Allocator, CompilerBuiltins, DebuginfoLevel, LlvmLibunwind, RustcLto, TargetSelection,
};
use crate::core::session::{CLang, DependencyType, FileType, Mode};
use crate::utils::build_stamp;
use crate::utils::build_stamp::BuildStamp;
use crate::utils::exec::{command, tool_metadata_command};
use crate::utils::helpers::{
    self, dylib_path_var, exe, get_clang_cl_resource_dir, hex_encode, is_debug_info, is_dylib,
    symlink_dir, t, up_to_date,
};
use crate::{debug, trace};

/// Opt-out for `-Zalways-encode-mir` on the standard library.
pub(crate) const TRUST_STD_ENCODE_MIR_ENV: &str = "TRUST_STD_ENCODE_MIR";

/// Should std be built with `-Zalways-encode-mir`? Unset means yes.
///
/// This switch decides whether std is LOWERABLE AT ALL for the trust-ir
/// frontend, which is load-bearing for the verified-library lane — so an
/// unrecognized value must not be read as "leave it on" while the person who
/// set it believes they turned it off. It used to disable on the exact string
/// `0` and silently ignore everything else, so `TRUST_STD_ENCODE_MIR=false`,
/// `=no` and `=off` all left the flag ON with no diagnostic.
///
/// Deliberately NOT a permissive boolean: this is an internal build switch, and
/// the accepted set is named in the error so a wrong value is a one-line fix.
fn trust_std_encode_mir_enabled(value: Option<&OsStr>) -> Result<bool, String> {
    match value {
        None => Ok(true),
        Some(value) if value == "1" => Ok(true),
        Some(value) if value == "0" => Ok(false),
        Some(other) => Err(format!(
            "{TRUST_STD_ENCODE_MIR_ENV}={other:?} is not a recognized value: use `1` (the \
             default — encode MIR for every std function, which is what makes std lowerable \
             for the trust-ir frontend) or `0` (opt out). Unset means `1`. Refusing rather \
             than ignoring it, because ignoring would leave -Zalways-encode-mir ON while \
             looking like it had been turned off."
        )),
    }
}

/// Trust: the flag `TRUST_STD_ENCODE_MIR` gates on every `Mode::Std` unit.
pub(crate) const TRUST_STD_ENCODE_MIR_FLAG: &str = "-Zalways-encode-mir";

/// Trust: what `rust.trust-ir-metadata = true` adds to every `Mode::Std` unit of a
/// stage >= 1 build compiler, in this order.
///
/// `-Ztrust-ir-lower=on` turns the THIR -> trust-ir producer on by itself: bootstrap
/// still passes `-Ztrust-verify=off` to these units, and the producer runs when
/// verification is on OR lowering is requested, so the entries std's metadata carries
/// do not depend on the verifier switch. `-Ztrust-ir-flip=no` keeps the producer from
/// installing derived MIR, so the bodies codegen reads are the ones a build without
/// the option reads. `-Ztrust-ir-lower-templates` also retains generic definitions;
/// lowering alone records them as `template-pending(capture off)`. These are
/// structural metadata, not a template admission or proof capability. None of
/// these flags is a verifier control: bootstrap's self-proof refusal and
/// its off-switch default do not classify them
/// (`builder::cargo::tests::the_std_producer_flags_are_not_verifier_controls`).
pub(crate) const TRUST_STD_IR_METADATA_FLAGS: [&str; 3] = [
    "-Ztrust-ir-lower=on",
    "-Ztrust-ir-flip=no",
    "-Ztrust-ir-lower-templates",
];

/// Trust: every Trust rustflag of a `Mode::Std` unit, as a pure function of the build
/// compiler's stage, `rust.trust-ir-metadata` and the `TRUST_STD_ENCODE_MIR` setting.
///
/// PURE so the list is tested without a `Builder`, and ONE list so the build lane and
/// the test lane cannot disagree ([`apply_trust_std_rustflags`] is its only caller).
///
/// The two switches are independent. `TRUST_STD_ENCODE_MIR` decides
/// `-Zalways-encode-mir` at every stage, exactly as before the option existed, and an
/// unrecognized value is still an error whatever the option says. The option adds the
/// producer flags only at effective stage >= 1 (`Cargo::build_compiler_stage`: a
/// local-rebuild stage-0 compiler counts as 1), the same `build_compiler_stage != 0`
/// condition as `builder::cargo`'s `-Ztrust-verify=off` default. A seed that is not a
/// local rebuild never gets them: its trust-ir wire version and entry schema need not
/// be this tree's.
///
/// With the option off the result is the one flag, or nothing under
/// `TRUST_STD_ENCODE_MIR=0`: what a `Mode::Std` unit received before the option existed.
pub(crate) fn trust_std_rustflags(
    build_compiler_stage: u32,
    trust_ir_metadata: bool,
    encode_mir: Option<&OsStr>,
) -> Result<Vec<&'static str>, String> {
    let mut flags = Vec::new();
    if trust_std_encode_mir_enabled(encode_mir)? {
        flags.push(TRUST_STD_ENCODE_MIR_FLAG);
    }
    if trust_ir_metadata && build_compiler_stage >= 1 {
        flags.extend(TRUST_STD_IR_METADATA_FLAGS);
    }
    Ok(flags)
}

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

impl CommandLineStep for Std {
    /// Build stamp of std, if it was indeed built or uplifted.
    type Output = Option<BuildStamp>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.crate_or_deps("sysroot").path("library")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        let crates = std_crates_for_make_run(&run);
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
            // Trust (DEFAULT ON; opt out with `TRUST_STD_ENCODE_MIR=0`): encode MIR
            // for ALL std functions (not just generic/inline ones) so the trust-ir
            // frontend can lower the FULL std dependency closure of a program
            // self-contained (e.g. hashbrown's non-inline RawTableInner::ctrl_slice),
            // instead of leaving them as MIR-unavailable link leaves. Additive
            // metadata only — the compiled std object code is byte-identical, so
            // linking and binaries are unaffected; only the rlib metadata grows.
            //
            // Why the default flipped: whether a std function was MIR-encoded is
            // decided by `cross_crate_inlinable`, which requires `checker.calls == 0`.
            // That made verifiability an accident of a body's call count —
            // `Formatter::alternate` (0 calls) bundled and PROVED while
            // `Formatter::write_str` (1 call) stayed an absent callee, so no impl of
            // `Debug` or `Display` could verify. An inlining heuristic must not decide
            // what a VERIFYING compiler is able to prove.
            //
            // Trust: the same call adds the trust-ir producer flags when
            // `rust.trust-ir-metadata` is on (default off).
            apply_trust_std_rustflags(builder, &mut cargo);
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
                // We use -Zembed-metadata=no for the standard library
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

/// Resolves standard library crates for [`Std::make_run`] for any build kind (like check, doc,
/// build, clippy, etc.).
pub fn std_crates_for_make_run(run: &RunConfig<'_>) -> Vec<String> {
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
    crate::exit!(1); // Trust: the exit macro is a diverging statement.
}

/// Tries to find LLVM's `compiler-rt` source directory, for building `library/profiler_builtins`.
///
/// Normally it lives in the `src/llvm-project` submodule, but if we will be using a
/// downloaded copy of CI LLVM, then we try to use the `compiler-rt` sources from
/// there instead, which lets us avoid checking out the LLVM submodule.
fn compiler_rt_for_profiler(builder: &Builder<'_>) -> PathBuf {
    // Try to use `compiler-rt` sources from downloaded CI LLVM, if available
    if let Some(downloaded_llvm) = builder.ensure(LlvmFromCi { target: builder.host_target }) {
        let ci_llvm_compiler_rt = downloaded_llvm.output.root_dir().join("compiler-rt");
        if !builder.config.dry_run() {
            assert!(
                ci_llvm_compiler_rt.exists(),
                "compiler-rt sources not found in LLVM downloaded from CI at {ci_llvm_compiler_rt:?}"
            );
        }
        return ci_llvm_compiler_rt;
    }

    // Otherwise, fall back to requiring the LLVM submodule.
    builder.require_submodule("src/llvm-project", {
        Some("The `build.profiler` config option requires `compiler-rt` sources from LLVM.")
    });
    builder.src.join("src/llvm-project/compiler-rt")
}

/// Configure cargo to compile the standard library, adding appropriate env vars
/// and such.
/// Trust: apply the Trust rustflags of a `Mode::Std` cargo: `-Zalways-encode-mir`
/// under its gate, and the trust-ir producer flags under `rust.trust-ir-metadata`.
///
/// EXTRACTED BECAUSE THE TWO STD LANES MUST NOT DRIFT. `compile::Std::run` and
/// `test::Crate::run` both configure a `Mode::Std` cargo with `std_cargo`, and
/// both write into the SAME target directory (`cargo.rs`'s `CARGO_TARGET_DIR` is
/// `stage_out(compiler, mode)`, which has no `Kind` term). When only the build
/// lane added this flag, cargo forked `core` into two units — because rustflags
/// are hashed into cargo's `unit_id` (the `-Cextra-filename` and the
/// `build/<pkg>/<hash>/` directory) but deliberately NOT into `c_metadata` (the
/// `-Cmetadata`).
///
/// Two `core` rlibs with the same `-Cmetadata` and different content collide:
/// `StableCrateId` is `hash(crate name, -Cmetadata, is_exe, cfg_version)`
/// (`rustc_span/src/def_id.rs`), and `extra_filename` is not an input. That is
/// exactly the failure `library/std_detect` hit — its `#[cfg(test)] extern crate
/// std;` has no cargo edge to supply `std` (std_detect is a DEPENDENCY of std),
/// so `std` resolved through the sysroot, which was linked against the BUILD
/// lane's `core`, while `--extern core` handed the test target the TEST lane's.
/// "found crates (`core` and `core`) with colliding StableCrateId values",
/// followed by a bogus-looking `E0463: can't find crate for `std``.
///
/// Upstream does not hit this: it adds `-Zalways-encode-mir` only on the
/// `is_for_mir_opt_tests` path, which uses a different sysroot, so its two lanes
/// never share a directory while disagreeing about a flag.
///
/// Call this from both lanes that build std into `stage_out(compiler, Mode::Std)`
/// with `std_cargo`: `compile::Std`'s regular sysroot and `test::Crate`'s non-Miri
/// lane. The check, clippy, doc, Miri and mir-opt lanes do not call it;
/// `compile::tests::both_std_lanes_take_their_trust_rustflags_from_the_one_helper`
/// pins exactly these two callers. A future flag that applies to one of the two
/// only re-creates this bug, and the symptom will again look like anything but a
/// missing rustflag.
///
/// The same holds for the producer flags of `rust.trust-ir-metadata`, which is
/// why they are added here and not at either call site: one helper, one flag
/// list ([`trust_std_rustflags`]), both lanes.
pub fn apply_trust_std_rustflags(builder: &Builder<'_>, cargo: &mut Cargo) {
    let flags = trust_std_rustflags(
        cargo.build_compiler_stage(),
        builder.config.trust_ir_metadata,
        std::env::var_os(TRUST_STD_ENCODE_MIR_ENV).as_deref(),
    )
    .unwrap_or_else(|message| panic!("{message}"));
    for flag in flags {
        cargo.rustflag(flag);
    }
}

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

        // Trust: an explicitly configured compiler remains an input even if its
        // executable happens to use the downloaded stage0 directory spelling.
        let is_downloaded_beta_stage0 = builder.config.external_rustc.is_none()
            && builder
                .sess
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

            // Trust (E0464, 2026-09-14): do NOT copy the initial sysroot's RUSTC-PRIVATE
            // artifacts into `stage0-sysroot`.
            //
            // Upstream's stage0 is a downloaded beta toolchain, which ships no
            // `rustc_*` rmeta at all, so this whole-tree copy was safe there. EVERY
            // Trust stage0 is a full Trust toolchain and does ship them. The result is
            // that building a rustc-private tool sees TWO generations of every rustc
            // crate — `stage0-sysroot`'s, from the snapshot, and this build's, handed
            // over as `-L` via `RUSTC_ADDITIONAL_SYSROOT_PATHS` — and rustc refuses with
            // `E0464: multiple candidates for rmeta dependency rustc_abi`, 29 of them,
            // failing `src/librustdoc` and with it the whole `scoped.compiler-check`
            // lane.
            //
            // That failure is BUILD-TREE STATE, which is why it has looked intermittent
            // and been quarantined three times and retired twice in one day: a tree
            // assembled from scratch carries one generation and is green, a long-lived
            // one carries two and is red. Same source, opposite verdicts.
            //
            // Nothing needs these rows here. `prepare_rustc_private_sysroot` builds a
            // tool's rustc-private sysroot from `librustc_stamp` — the built rustc's own
            // artifacts — and returns `None` when that stamp is absent; it reads
            // `stage0-sysroot` only for std files. So the rustc-private half of this
            // copy has no consumer, and dropping it makes Trust's stage0-sysroot the
            // shape the rest of bootstrap already assumes.
            //
            // The filter is on the CRATE ROLE, not on a name pattern, for the reason
            // this file has learned five times today: `librustc_driver-<hash>.dylib` and
            // `rustc_driver-<hash>.dll` differ by platform, and `-Cextra-filename`
            // carries a hash that changes with every commit. `is_rustc_private_artifact`
            // asks what the file IS.
            //
            // Trust (2026-09-15, merged from the parallel fix): ALSO skip the `rustlib/src`
            // and `rustlib/rustc-src` SOURCE SNAPSHOTS. `Sysroot` plants both as symlinks
            // back into `builder.src`, and a copier that follows a symlink it finds at the
            // destination writes a stage0 toolchain's `compiler/` and `library/` OVER THE
            // SOURCE TREE — measured: `x.py check` rewrote 1,002 files under compiler/ and
            // library/ six seconds in. `cp_link_filtered` skips a rejected DIRECTORY
            // without descending, so excluding the two relative paths leaves the planted
            // symlinks untouched; the filter sees paths RELATIVE to `lib/`.
            // Trust: the custom initial SDK is an external input. Import independent
            // regular-file bytes so assembly/reassembly cannot change its nlink/ctime.
            builder.cp_filtered(
                &builder.initial_sysroot.join("lib"),
                &sysroot.join("lib"),
                &|path| {
                    let is_source_snapshot =
                        path == Path::new("rustlib/src") || path == Path::new("rustlib/rustc-src");
                    !is_source_snapshot && !is_rustc_private_artifact(path)
                },
            );
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

impl CommandLineStep for StartupObjects {
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

/// Whether `channel` takes upstream's nightly compiler defaults
/// (`CFG_DEFAULT_POLONIUS_NEXT` / `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY`).
/// The `trust` channel is Trust's nightly-equivalent (PERF-SEP26-DEFAULTS);
/// omitting it here silently kept the pre-1.101 defaults on Trust builds.
fn channel_takes_nightly_defaults(channel: &str) -> bool {
    matches!(channel, "nightly" | "dev" | "trust")
}

impl CommandLineStep for Rustc {
    type Output = BuiltRustc;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.crate_or_deps_filtered("rustc-main", |krate| {
            // We can't allow `build rustc` as an alias for this Step, because that's reserved by `Assemble`.
            // Ideally Assemble would use `build compiler` instead, but that seems too confusing to be worth the breaking change.
            // `rustc_codegen_trust_cg` is selected by `BuiltinTrustCg`, which builds the full
            // compiler. Treating it as a partial Rustc build overwrites the shared
            // `.librustc-stamp` with a backend-only stamp and can leave stale
            // rustc/trustc binaries without librustc_driver.
            krate.name != "rustc-main" && krate.name != "rustc_codegen_trust_cg"
        })
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

        // Trust: the sysroot this compiler is assembled into, with the `ay` it
        // ships, BEFORE the compiler's crates are compiled: trust-cg-verify
        // records that `bin/ay` (see `rustc_cargo`). Measured 2026-10-01: with
        // the build compiler's sysroot recorded instead, a stage2 compiler
        // refused its own stage2/bin/ay (TCG-AY-IDENTITY-MISMATCH) and admitted
        // only stage1's, and its bytes changed with whatever stage0 built that.
        let output_compiler = Compiler::new(stage, target);
        let output_sysroot = builder.sysroot(output_compiler);
        assert_eq!(
            output_sysroot,
            local_sysroot_dir(builder, output_compiler),
            "the sysroot rustc_cargo names for the AY record is not the one being assembled",
        );
        crate::core::build_steps::tool::ensure_sysroot_ay(
            builder,
            output_compiler,
            &output_sysroot,
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

        if builder.sess.config.enable_bolt_settings && build_compiler.stage == 1 {
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
                    if filename.ends_with(".rlib") {
                        return true;
                    }
                }

                // Distribute the rest of the rustc crates as rmeta files only to reduce
                // the tarball sizes by about 50%. The object files are linked into
                // librustc_driver.so, so it is still possible to link against them.
                filename.ends_with(".rmeta")
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

/// Trust: an explicit BUILD component for a coherent self-host development image.
///
/// The selected stage is the producer, not the resulting compiler's stage: like
/// `dist::RustcDev`, this component always builds compiler libraries with stage1.
/// Those libraries belong to the compiler/runtime they produced (stage2), never
/// to a stage1 image whose runtime was built by the seed. Normal Assemble owns
/// that image, its std selection and configured tools; this step also installs
/// the development libraries when `build.extended` is false.
///
/// This is not a distribution/install request or a complete recipe envelope.
/// Their readiness scopes, including every top-level stage2 request, are intact.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct RustcDev {
    pub target: TargetSelection,
}

impl CommandLineStep for RustcDev {
    type Output = Compiler;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trustc-dev").alias("rustc-dev")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Self { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Compiler {
        assert!(
            builder.kind == Kind::Build
                && builder.config.explicit_stage_from_cli
                && builder.top_stage == 1
                && self.target == builder.host_target
                && builder.hosts.as_slice() == [builder.host_target]
                && !builder.download_rustc()
                && builder.config.keep_stage.is_empty()
                && builder.config.keep_stage_std.is_empty()
                && builder.config.skip.is_empty(),
            "the BUILD development component requires an explicit native stage1 producer, \
             original compiler/std builds and no downloaded, kept or skipped stages",
        );

        // Use the distribution component's maintained compiler1 producer.
        // Constructing that Step does not enter Dist or create an archive.
        let producer = dist::RustcDev::new(builder, self.target);
        let BuiltRustc { build_compiler } =
            builder.ensure(Rustc::new(producer.build_compiler, self.target));
        assert_eq!(build_compiler, producer.build_compiler);
        let compiler = builder.ensure(Assemble {
            target_compiler: Compiler::new(build_compiler.stage + 1, self.target),
        });

        // Each configured target gets the complete library population, not a
        // std-only partial stamp. Std retains its normal full-bootstrap/uplift
        // policy and the public image retains Assemble's actual runtime.
        for &target in &builder.targets {
            builder.ensure(Std::new(compiler, target));
        }
        let stamp = build_stamp::librustc_stamp(builder, build_compiler, self.target);
        let std_stamp = assembled_sysroot_std_stamp(builder, compiler, self.target);
        install_local_rustc_dev(builder, compiler, &stamp, &std_stamp);
        validate_assembled_local_compiler(builder, compiler, &builder.sysroot(compiler));
        compiler
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("trustc-dev", self.target).built_by(Compiler::new(1, self.target)))
    }
}

/// Trust: trust-cg-verify (linked into the driver) pins the `ay` its compiler
/// may start, by the bytes of `<sysroot>/bin/ay`. The compiler compiled with
/// `build_compiler` is assembled into the NEXT stage's sysroot and hosts the
/// verifier there, so that is the sysroot to record — not the build
/// compiler's, whose `bin/ay` is the previous stage's battery. `rustc_cargo`
/// sets it for every kind (check, build, doc, test) so they share one
/// build-script record instead of re-running it at each switch; `Rustc::run`
/// puts the battery in place before a compiler that ships is compiled.
pub(crate) fn name_ay_record_host_sysroot(
    builder: &Builder<'_>,
    cargo: &mut Cargo,
    target: TargetSelection,
    build_compiler: &Compiler,
) {
    cargo.env(
        AY_RECORD_HOST_SYSROOT_ENV,
        local_sysroot_dir(builder, Compiler::new(build_compiler.stage + 1, target)),
    );
}

pub fn rustc_cargo(
    builder: &Builder<'_>,
    cargo: &mut Cargo,
    target: TargetSelection,
    build_compiler: &Compiler,
    crates: &[String],
) {
    let kind = cargo.kind();
    cargo
        .arg("--features")
        .arg(builder.rustc_features(kind, target, crates))
        .arg("--manifest-path")
        .arg(builder.src.join("compiler/rustc/Cargo.toml"));

    name_ay_record_host_sysroot(builder, cargo, target, build_compiler);

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

    // /Brepro tells the MSVC linker to omit non-deterministic COFF data
    // (namely the PE timestamp) from the produced binary. Only applied when
    // building rustc itself via bootstrap. See discussion:
    // https://github.com/rust-lang/rust/pull/158873
    if target.is_msvc() {
        cargo.rustflag("-Clink-arg=/Brepro");
    }

    // Building with protected visibility reduces the number of dynamic relocations needed, giving
    // us a faster startup time. However GNU ld < 2.40 will error if we try to link a shared object
    // with direct references to protected symbols, so for now we only use protected symbols if
    // linking with LLD is enabled.
    if builder.sess.config.bootstrap_override_lld.is_used() {
        cargo.rustflag("-Zdefault-visibility=protected");
    }

    apply_dylib_lto(builder, build_compiler, cargo);

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

    apply_pgo(builder, cargo, *build_compiler, &builder.config.rust_pgo);

    // The stage0 compiler changes infrequently and does not directly depend on code
    // in the current working directory. Therefore, caching it with sccache should be
    // useful.
    // This is only performed for non-incremental builds, as ccache cannot deal with these.
    //
    // We skip this on Windows hosts for now because of command line length issues (see CI failure
    // in https://github.com/rust-lang/rust/pull/158888#issuecomment-4960306292).
    if let Some(ref ccache) = builder.config.ccache
        && build_compiler.stage == 0
        && !cfg!(windows)
        && !builder.config.incremental
    {
        cargo.env("RUSTC_WRAPPER", ccache);
    }

    rustc_cargo_env(builder, cargo, target, crates);
}

fn apply_dylib_lto(builder: &Builder<'_>, build_compiler: &Compiler, cargo: &mut Cargo) {
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
}

// Trust: only rustc_llvm consumes the native LLVM configuration. Walk raw
// local metadata conservatively: in_tree_crates prunes optional backends by
// host configuration, which may differ from the selected compiler target.
// Empty selection retains the full compiler route; unknown roots still refuse.
fn compiler_crates_need_llvm(builder: &Builder<'_>, crates: &[String]) -> bool {
    if crates.is_empty() {
        return true;
    }
    let mut pending = crates.iter().map(String::as_str).collect::<Vec<_>>();
    let mut visited = HashSet::new();
    while let Some(name) = pending.pop() {
        if !visited.insert(name) {
            continue;
        }
        let krate =
            builder.crates.get(name).unwrap_or_else(|| panic!("metadata missing for {name}"));
        if name == "rustc_llvm" || krate.deps.contains("rustc_llvm") {
            return true;
        }
        // Non-workspace path dependencies have no metadata node here. The
        // named LLVM consumer above remains required even if its node is absent.
        pending.extend(
            krate.deps.iter().filter(|dep| builder.crates.contains_key(*dep)).map(String::as_str),
        );
    }
    false
}

fn rustc_cargo_env(
    builder: &Builder<'_>,
    cargo: &mut Cargo,
    target: TargetSelection,
    crates: &[String],
) {
    // Trust: stable admission policy. Clean obtains the changing build identity from
    // its native host, without embedding it in the elaborator dependency graph.
    cargo.env(
        "CFG_TRUST_ORACLE_HOST",
        if builder.version_info().sha().is_some() { "1" } else { "0" },
    );
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

    // Trust: a dev stage-1 build's identity names its sources, not HEAD (TB1).
    if let Some(ref ver_date) = builder.version_info().commit_date() {
        cargo.env("CFG_VER_DATE", ver_date);
    }
    if let Some(ref ver_hash) = builder.version_info().sha() {
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

    // Trust: the `trust` channel is Trust's nightly-equivalent (it tracks
    // nightly pins; see tests/upstream-rust/baseline.toml), so it takes the
    // same nightly defaults. Without this, Trust builds silently kept the
    // pre-1.101 defaults (Polonius off, next solver coherence-only) that
    // upstream nightly left in Aug 2026. Ruling: PERF-SEP26-DEFAULTS in
    // docs/DECISION_QUEUE.md; per-compile opt-outs -Zpolonius=off and
    // -Znext-solver=coherence are unchanged.
    if channel_takes_nightly_defaults(&builder.config.channel) {
        // We want to enable Polonius Alpha and Next Trait Solver by default on nighty
        cargo.env("CFG_DEFAULT_POLONIUS_NEXT", "1");
        cargo.env("CFG_DEFAULT_NEXT_SOLVER_GLOBALLY", "1");
    }

    // These conditionals represent a tension between three forces:
    // - For non-check builds, we need to define some LLVM-related environment
    //   variables, requiring LLVM to have been built.
    // - For check builds, we want to avoid building LLVM if possible.
    // - Check builds and non-check builds should have the same environment if
    //   possible, to avoid unnecessary rebuilds due to cache-busting (in the same stage).
    //
    // If we have either:
    // - LLVM already locally built
    // - download-ci-llvm enabled
    // - LLVM provided externally through a llvm-config
    //
    // and we do a check-like build, we run rustc_llvm as normally, to maintain a
    // consistent environment between check and non-check builds
    //
    // However, if neither from the above three bullet points is true, and we do a check-like build,
    // we skip running rustc_llvm by setting the RUST_CHECK environment variable.
    //
    // Note that if download-ci-llvm is enabled, `prebuilt_llvm_output` will *eagerly* download
    // LLVM from CI, thus making it locally available.
    if builder.config.llvm_enabled(target) && compiler_crates_need_llvm(builder, crates) {
        let building_llvm_is_expensive = prebuilt_llvm_output(builder, target).is_none();

        let skip_llvm = cargo.kind().is_check_like() && building_llvm_is_expensive;
        if skip_llvm {
            cargo.env("RUST_CHECK", "1");
        } else {
            rustc_llvm_env(builder, cargo, target);
        }
    }

    // See also the "JEMALLOC_SYS_WITH_LG_PAGE" setting in the tool build step.
    if builder.config.allocator(target) == Allocator::Jemalloc
        && env::var_os("JEMALLOC_SYS_WITH_LG_PAGE").is_none()
    {
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

    // Plumb the `rust.wasm-panic-unwind-default` configuration option into the
    // `rustc_target` crate.
    if builder.config.wasm_panic_unwind_default {
        cargo.env("CFG_WASM_PANIC_UNWIND_DEFAULT", "1");
    }
}

/// Pass down configuration from the LLVM build into the build of
/// rustc_llvm and rustc_codegen_llvm.
///
/// Note that calling this function has the side-effect of _building LLVM_, which is sometimes
/// unwanted (e.g. for check builds).
fn rustc_llvm_env(builder: &Builder<'_>, cargo: &mut Cargo, target: TargetSelection) {
    let llvm_output = builder.ensure(llvm::Llvm { target });
    if builder.config.is_rust_llvm(&llvm_output, target) {
        cargo.env("LLVM_RUSTLLVM", "1");
    }
    if builder.config.llvm_enzyme {
        cargo.env("LLVM_ENZYME", "1");
    }
    if builder.config.llvm_offload {
        builder.ensure(llvm::OmpOffload { target });
        cargo.env("LLVM_OFFLOAD", "1");
    }

    // This always has to be the host LLVM config, because it is executed by rustc_llvm
    cargo.env("LLVM_CONFIG", builder.host_llvm_config());
    // Declared dependency input, never an ambient pkg-config search override.
    if let Some(directory) = builder
        .config
        .target_config
        .get(&builder.host_target)
        .and_then(|config| config.llvm_zstd_pkg_config_dir.as_ref())
    {
        cargo.env("LLVM_ZSTD_PC_DIR", directory);
    } else {
        cargo.env("LLVM_ZSTD_PC_DIR", "");
    }

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
    if builder.config.llvm_pgo.generate_profile.is_some()
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
    if llvm_output.link_shared() {
        cargo.env("LLVM_LINK_SHARED", "1");
    }
    if builder.config.llvm_use_libcxx {
        cargo.env("LLVM_USE_LIBCXX", "1");
    }
    if builder.config.llvm_assertions {
        cargo.env("LLVM_ASSERTIONS", "1");
    }
    if builder.cxx_tool(target).is_like_gnu() || builder.cc_tool(target).is_like_gnu() {
        cargo.env("LLVM_COMPILER_IS_GNU_LIKE", "1");
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

    /// Same as `StdLink`, only for librustc
    fn run(self, builder: &Builder<'_>) {
        let build_compiler = self.build_compiler;
        let sysroot_compiler = self.sysroot_compiler;
        let target = self.target;
        add_to_sysroot(
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

impl CommandLineStep for BuiltinTrustCg {
    type Output = Compiler;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        // Trust: upstream 1.101 asserts every step registers at least one
        // pathset (core::builder::cli_paths sanity check), so the path is
        // registered unconditionally; `make_run` gates per host, so a broad
        // `x build compiler` with trust-cg disabled selects this step and
        // skips it instead of running a step that can only fail. (Before
        // 1.101 the path was left unregistered while disabled.)
        let _ = trust_cg_builtin_enabled_for_any_host(
            run.builder.hosts.iter().map(|host| run.builder.config.enabled_codegen_backends(*host)),
        );
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
    cmd.args(builder.cc_unhandled_cflags(target, c));
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

/// The environment variable that names, to trust-cg-verify's build script,
/// the sysroot whose compiler will host it (first-party/trust-cg,
/// crates/trust-cg-verify/build.rs). Not `TRUST_`-prefixed: authenticated
/// Targo refuses that prefix as build-script authority.
pub(crate) const AY_RECORD_HOST_SYSROOT_ENV: &str = "TOOLCHAIN_AY_RECORD_HOST_SYSROOT";

/// The directory `Sysroot` assembles a locally built `compiler`'s sysroot in
/// (`build/<host>/stage<N>`, `stage0-sysroot` for stage 0) — computed without
/// assembling it, so a `check` names the same sysroot a `build` assembles.
/// Forced-recompile test sysroots and CI downloads are `Sysroot`'s own cases.
pub(crate) fn local_sysroot_dir(builder: &Builder<'_>, compiler: Compiler) -> PathBuf {
    let host_dir = builder.out.join(compiler.host);
    if compiler.stage == 0 {
        host_dir.join("stage0-sysroot")
    } else {
        host_dir.join(format!("stage{}", compiler.stage))
    }
}

/// Source aliases actually planted by `Sysroot`, shared with artifact observation.
pub(crate) fn sysroot_source_aliases(stage: u32, download_rustc: bool) -> &'static [&'static str] {
    match (stage == 0, download_rustc) {
        (true, true) => &[],
        (true, false) => &["lib/rustlib/rustc-src/rust"],
        (false, true) => &["lib/rustlib/src/rust"],
        (false, false) => &["lib/rustlib/src/rust", "lib/rustlib/rustc-src/rust"],
    }
}

impl Step for Sysroot {
    type Output = PathBuf;

    /// Returns the sysroot that `compiler` is supposed to use.
    /// For the stage0 compiler, this is stage0-sysroot (because of the initial std build).
    /// For all other stages, it's the same stage directory that the compiler lives in.
    fn run(self, builder: &Builder<'_>) -> PathBuf {
        let compiler = self.compiler;
        let host_dir = builder.out.join(compiler.host);

        let sysroot_dir = |stage| {
            if stage != 0 && self.force_recompile && stage == compiler.stage {
                host_dir.join(format!("stage{stage}-test-sysroot"))
            } else if stage != 0 && builder.download_rustc() && compiler.stage != builder.top_stage
            {
                host_dir.join("ci-rustc-sysroot")
            } else {
                local_sysroot_dir(builder, Compiler::new(stage, compiler.host))
            }
        };
        let sysroot = sysroot_dir(compiler.stage);
        trace!(stage = ?compiler.stage, ?sysroot);

        builder.do_if_verbose(|| {
            println!("Removing sysroot {} to avoid caching bugs", sysroot.display())
        });
        let _ = fs::remove_dir_all(&sysroot);
        t!(fs::create_dir_all(&sysroot));

        // Trust: StdLink imports stage0's original libraries, including its LLVM
        // runtime. Resolving this source tree's LLVM here would select a different
        // provider before that import, even for seed-built library tests.

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
        // rustc-src is already part of CI rustc's sysroot. Local stage 0 also
        // plants it, so consumers must declare BOTH kinds at their actual stages.
        for relative in sysroot_source_aliases(compiler.stage, builder.download_rustc()) {
            let source_alias = sysroot.join(relative);
            t!(fs::create_dir_all(source_alias.parent().unwrap()));
            if let Err(e) = symlink_dir(&builder.config, &builder.src, &source_alias) {
                eprintln!(
                    "ERROR: creating symbolic link `{}` to `{}` failed with {}",
                    source_alias.display(),
                    builder.src.display(),
                    e,
                );
                if *relative == "lib/rustlib/src/rust" && builder.config.rust_remap_debuginfo {
                    eprintln!(
                        "ERROR: some `tests/ui` tests will fail when lacking `{}`",
                        source_alias.display(),
                    );
                }
                helpers::exit_process(1);
            }
        }

        sysroot
    }
}

fn restore_user_facing_tools(builder: &Builder<'_>, compiler: Compiler, sysroot: &Path) {
    if !crate::core::build_steps::tool::should_restore_user_facing_tools(compiler.stage) {
        return;
    }

    // Trust: restore existing artifacts and build only compiler prerequisites
    // here. Final Targo needs the completed compiler, so selected frontend/CLI
    // construction belongs to the post-assembly finish, after Sysroot is cached.
    // Dist/install/test retain their explicit component graphs.
    let partial_source_build = crate::core::build_steps::tool::is_partial_stage1_source_build(
        builder.kind,
        compiler.stage,
        builder.top_stage,
        builder.config.include_default_paths,
        &builder.paths,
    );
    if partial_source_build {
        builder.info(
            "Partial stage1 source build: unrelated verifier tools are not rebuilt; this is not a complete SDK",
        );
    } else if crate::core::build_steps::tool::should_ensure_default_verifier_tool_bins(
        builder.kind,
        compiler.stage,
    ) {
        crate::core::build_steps::tool::ensure_sysroot_verifier_prerequisites(
            builder, compiler, sysroot,
        );
    }

    let tools_dir = builder.tools_dir(compiler, compiler.host);

    let bindir = sysroot.join("bin");
    t!(fs::create_dir_all(&bindir));
    // A single built tool can intentionally back both its Trust name and one
    // upstream-compatible alias: the `targo` artifact is installed as `targo`
    // and as the `cargo` compatibility entry point.
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
    let stock_proc_macro_srv =
        sysroot.join("libexec").join(exe("rust-analyzer-proc-macro-srv", compiler.host));
    t!(crate::core::build_steps::tool::remove_retired_proc_macro_srv_alias(&stock_proc_macro_srv));
}

fn restore_local_compiler_aliases(builder: &Builder<'_>, compiler: Compiler, sysroot: &Path) {
    if compiler.stage == 0 || builder.download_rustc() {
        return;
    }

    // Trust: restoration observes already-produced stamps and images. Selecting
    // their exact stage/host must not assemble a previous compiler merely to
    // discover that no artifact exists, or make Sysroot a compiler build root.
    let build_compiler = Compiler::new(compiler.stage - 1, builder.config.host_target);
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

/// Trust (E0464, 2026-09-14): is this sysroot file a RUSTC-PRIVATE compiler artifact —
/// one of the `rustc_*` crates a rustc-private tool links against — rather than part of
/// the standard library?
///
/// Asked of the file's CRATE NAME, taken from the artifact stem, not of a substring of
/// the whole path: a path test would also match `.../rustlib/rustc_foo/...` directories
/// and would miss the Windows `rustc_driver-<hash>.dll` spelling, which carries no `lib`
/// prefix. Both mistakes have real precedent in this file.
///
/// Deliberately NOT matched: `rustc_std_workspace_core` / `_alloc` / `_std`, which are
/// std-side shims that a rustc-private tool's std half genuinely needs, and whose names
/// merely begin with `rustc_`.
// Trust: check-only sysroots use the same artifact-role boundary.
pub(super) fn is_rustc_private_artifact(path: &Path) -> bool {
    // MUST be gated on a library extension. `cp_link_filtered` applies its predicate to
    // DIRECTORIES as well as files and skips the whole subtree when it returns true, so
    // an unextended name test would drop a directory that merely begins with `rustc_`
    // and silently truncate the copy. A crate artifact always carries one of these.
    let Some(extension) = path.extension().and_then(|e| e.to_str()) else {
        return false;
    };
    if !matches!(extension, "rlib" | "rmeta" | "dylib" | "so" | "dll" | "a") {
        return false;
    }
    let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
        return false;
    };
    let stem = stem.strip_prefix("lib").unwrap_or(stem);
    let crate_name = stem.split('-').next().unwrap_or(stem);
    if !crate_name.starts_with("rustc_") {
        return false;
    }
    // NOT every `rustc_*` crate is compiler-private. The standard library itself
    // depends on several, and dropping one of those does not produce a tidy failure —
    // it produces `E0463: can't find crate for 'rustc_demangle' which 'std' depends on`
    // multiplied across every downstream crate. Measured when this filter first shipped
    // with only the `rustc_std_workspace_` exception: 0 E0464 (the bug was fixed) and
    // 2571 NEW errors (the cure was worse).
    //
    // The list started as a DERIVATION and was then NARROWED BY MEASUREMENT, which is
    // the part worth keeping. Deriving it from the manifests —
    //
    //     grep -hoE '^rustc[-_][a-z_-]+' library/*/Cargo.toml | sort -u
    //
    // (where `rustc-dep-of-std` is a FEATURE, not a crate) — yields `rustc_demangle`,
    // `rustc_literal_escaper` and `rustc_apfloat`. That is a SUPERSET: a manifest names
    // what the library is BUILT with, while this sysroot only has to carry what the
    // PREBUILT std rlib still references. Measured by dropping all three and reading the
    // failures: the only missing crate was `rustc_demangle` (11 occurrences, plus 10
    // cascading `std`). Neither of the other two was wanted.
    //
    // SECOND MEASUREMENT, and the correction matters: a build stops at its FIRST
    // missing crate, so that probe named the first requirement, not the requirement
    // SET. It never reached `proc-macro2` — where `proc_macro` needs
    // `rustc_literal_escaper` — and re-running with `rustc_demangle` restored surfaced
    // `E0463: can't find crate for rustc_literal_escaper which proc_macro depends on`.
    //
    // `rustc_apfloat` is deliberately NOT here, and that is what keeping the whole
    // superset would have cost. It is genuinely DUAL-USE — `library/compiler-builtins`
    // declares it AND `src/tools/miri` links it as rustc-private — so exempting it left
    // miri seeing two generations and reproduced the very
    // `E0464: multiple candidates for rmeta dependency rustc_apfloat` this filter
    // exists to remove. Exempting only what is measurably needed takes the lane from
    // 30 E0464 to 0.
    const STD_SIDE_RUSTC_CRATES: &[&str] = &["rustc_demangle", "rustc_literal_escaper"];
    !crate_name.starts_with("rustc_std_workspace_") && !STD_SIDE_RUSTC_CRATES.contains(&crate_name)
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
    // Hash-named driver dylibs from a previous assembly are not replaced by a
    // copy with a new hash. Leaving both in the public compiler libdir makes
    // rustc-private wrappers unable to select the compiler's unique runtime
    // and can load a driver from the wrong compiler generation. The full
    // librustc stamp below is authoritative, so remove every prior driver
    // runtime before restoring that exact generation.
    if !builder.config.dry_run() {
        t!(prune_rustc_driver_runtime_artifacts(&rustc_libdir));
    }
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
            // Trust: finish the cheap name checks before opening any candidate.
            if proc_macros.contains(&filename) {
                continue;
            }
            let path = entry.path();
            let is_dylib_or_debug = is_dylib(&path) || filename.to_str().is_some_and(is_debug_info);
            // Trust: the name filter above CANNOT work on its own, so also test
            // what the file actually is. See `dylib_declares_proc_macro`.
            if is_dylib_or_debug && !is_proc_macro_dylib(&path) {
                builder.copy_link(&path, &rustc_libdir.join(&filename), FileType::Regular);
            }
        }
    }
}

/// Trust: does this file export a proc-macro declarations symbol?
///
/// `restore_local_compiler_runtime_artifacts` already tried to keep proc macros
/// out of the compiler's public libdir, by excluding FILE NAMES drawn from this
/// build's stamp. That filter cannot work, because the libdir it copies FROM
/// belongs to the *build compiler* — a different generation, whose `-Cmetadata`
/// and therefore whose `-Cextra-filename` differ — so the names never match.
/// Measured 2026-09-13: this build's displaydoc is
/// `libdisplaydoc-213623978e25d466.dylib` while the file that reached the libdir
/// was stage0's `libdisplaydoc-2ef9e771ac39abb5.dylib`, and all 21 of the build
/// compiler's proc-macro dylibs were copied in.
///
/// That is not cosmetic. The compiler runs with this libdir on
/// `DYLD_LIBRARY_PATH`, and dyld resolves `dlopen` of an ABSOLUTE path against
/// that variable by LEAF NAME first — so a stale proc-macro dylib sitting there
/// silently replaces the one rustc asked for. Because `CFG_VERSION` embeds the
/// git short sha, the stale copy declares a different `StableCrateId`, and the
/// load fails with `symbol not found` against a file that is perfectly good.
/// Reproduced standalone: the same file and symbol resolve with `dlsym` when
/// `DYLD_LIBRARY_PATH` is unset and miss when it names that libdir.
///
/// So test what the file IS rather than what it is called.
fn is_proc_macro_dylib(path: &Path) -> bool {
    fs::read(path).is_ok_and(|bytes| dylib_declares_proc_macro(&bytes))
}

/// The byte-level half of [`is_proc_macro_dylib`], split out so it can be tested
/// without a real dylib on disk.
///
/// A proc-macro dylib exports `__rustc_proc_macro_decls_<hex>__`, minted by
/// `rustc_session::generate_proc_macro_decls_symbol` as
/// `format!("__rustc_proc_macro_decls_{:08x}__", stable_crate_id.as_u64())`.
///
/// **`{:08x}` is a MINIMUM width of 8, not a fixed 16.** A `StableCrateId` is a
/// uniformly distributed 64-bit hash, so it renders in 16 hex digits only when its
/// top nibble is non-zero — 15/16 of the value space. The rest render in 8..=15.
/// An earlier version of this predicate demanded exactly 16 and therefore missed a
/// random ~1-in-16 of all proc-macro dylibs; measured on this tree, 58 of 1,921
/// (3.0%), `displaydoc` and `serde_derive` among them. That is the same defect
/// class this function exists to fix — an artifact identified by a rendering of a
/// hash, where the rendering's width is itself input-dependent.
///
/// The run is bounded at 16 and NOT left open-ended, and that bound is
/// load-bearing. `librustc_driver` contains this prefix once, from the format
/// string that generates the symbol — but the `{:08x}` placeholder is not stored
/// as text: the two `&str` pieces sit in the constant pool with exactly **8 bytes**
/// of non-hex filler between them (measured: `c3 20 00 00 69 08 00 02`), followed
/// by the literal `__`. So the guard's real margin is that those filler bytes are
/// not hex, a constant-pool layout accident no linker guarantees. A false positive
/// here drops `librustc_driver` from the assembled compiler's libdir and produces a
/// compiler that cannot start — strictly worse than the bug being fixed — so the
/// exact driver payload is pinned as a fixture in the tests.
///
/// Only lowercase hex is accepted: `{:08x}` never emits uppercase, so allowing
/// `A-F` would widen the false-positive surface (UUIDs, hex dumps) for nothing.
fn dylib_declares_proc_macro(bytes: &[u8]) -> bool {
    const NEEDLE: &[u8] = b"__rustc_proc_macro_decls_";
    const MIN_DIGITS: usize = 8;
    const MAX_DIGITS: usize = 16;

    // Trust: search for the first `r`, preserving every overlapping prefix. Its
    // offset avoids false candidates in underscore-dense data. The patched
    // memmem search is scalar too, so use the optimized single-byte loop.
    for anchor in memchr::memchr_iter(b'r', bytes) {
        let Some(i) = anchor.checked_sub(2) else {
            continue;
        };
        let Some(rest) = bytes[i..].strip_prefix(NEEDLE) else {
            continue;
        };
        let digits = rest
            .iter()
            .take(MAX_DIGITS + 1)
            .take_while(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
            .count();
        if (MIN_DIGITS..=MAX_DIGITS).contains(&digits) && rest[digits..].starts_with(b"__") {
            return true;
        }
    }
    false
}

fn prune_rustc_driver_runtime_artifacts(libdir: &Path) -> std::io::Result<()> {
    if !libdir.exists() {
        return Ok(());
    }
    for entry in fs::read_dir(libdir)? {
        let path = entry?.path();
        if is_rustc_driver_runtime_artifact(&path) {
            fs::remove_file(path)?;
        }
    }
    Ok(())
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
    let drivers = builder
        .read_dir(&rustc_libdir)
        .into_iter()
        .map(|entry| entry.path())
        .filter(|path| is_rustc_driver_runtime_artifact(path))
        .collect::<Vec<_>>();
    assert_eq!(
        drivers.len(),
        1,
        "assembled stage{} compiler at `{}` must contain exactly one librustc_driver runtime in `{}`; found {}: {}",
        compiler.stage,
        sysroot.display(),
        rustc_libdir.display(),
        drivers.len(),
        drivers.iter().map(|path| path.display().to_string()).collect::<Vec<_>>().join(", ")
    );

    if compiler.host == builder.sess.host_target {
        tool_metadata_command(&rustc).arg("--version").run(builder);
        tool_metadata_command(&trustc).arg("--version").run(builder);
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

impl CommandLineStep for Assemble {
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
            let llvm_output = builder.ensure(llvm::Llvm { target });
            if !builder.config.dry_run() && builder.config.llvm_tools_enabled {
                trace!("LLVM tools enabled");

                let host_llvm = builder.ensure(llvm::Llvm { target: builder.host_target });
                let host_llvm_bin_dir = command(host_llvm.llvm_config())
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
                        // If not, then take the path of the host bindir of the host LLVM,
                        // relative to its output build directory, and then apply it to the target
                        // LLVM output build directory.
                        let host_llvm_out = host_llvm.root_dir();
                        let target_llvm_out = llvm_output.root_dir();
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
                for tool in dist::LLVM_TOOLS {
                    trace!("installing `{tool}`");
                    let tool_exe = exe(tool, target_compiler.host);
                    let src_path = llvm_bin_dir.join(&tool_exe);

                    if !src_path.exists() {
                        // When using `download-ci-llvm`, some of the tools may not exist, so skip trying to copy them.
                        if llvm_output.kind() == LlvmKind::DownloadedFromCi {
                            eprintln!("{} does not exist; skipping copy", src_path.display());
                            continue;
                        }
                        // On older LLVM versions, llubi isn't in the default tools. Remove this
                        // code when LLVM 23 is the minimum version.
                        if *tool == "llubi" {
                            continue;
                        }
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
                if target.contains("apple-darwin") && llvm_output.kind() == LlvmKind::External {
                    let external_llvm_libdir = command(host_llvm.llvm_config())
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

        // Trust: establish the selected LLD provider before recursive compiler
        // work. Keep the compiler-dependent wrapper and installation below.
        if builder.config.lld_enabled {
            builder.ensure(llvm::Lld { target: target_compiler.host });
        }

        // Trust: TPDE's existing provider checks precede compiler recursion;
        // installation below retains the same option and Linux-host boundary.
        if builder.config.llvm_tpde && target_compiler.host.contains("linux") {
            builder.ensure(llvm::Tpde { target: target_compiler.host });
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
            if builder.is_llvm_enabled_for(builder.config.host_target) {
                let rust_offload =
                    builder.ensure(llvm::RustOffload { target: build_compiler.host });
                let target_libdir =
                    builder.sysroot_target_libdir(target_compiler, target_compiler.host);
                let rust_offload_dst_lib = target_libdir.join(rust_offload.rust_offload_filename());
                builder.copy_link(
                    &rust_offload.rust_offload_path(),
                    &rust_offload_dst_lib,
                    FileType::NativeLibrary,
                );

                let omp_offload = builder.ensure(llvm::OmpOffload { target: build_compiler.host });
                for p in omp_offload.artifact_paths_with_symlink_targets() {
                    let libname = p.file_name().unwrap();
                    let dst_lib = target_libdir.join(libname);
                    builder.resolve_symlink_and_copy(&p, &dst_lib);
                }
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

            // `rustc_driver` statically links to stdlib, so do not copy the libstd dynamic library file.
            // Trust keeps the apple-darwin exception from before: there the libstd
            // dynamic library is still copied.
            let can_be_rustc_dynamic_dep = target_compiler.host.contains("apple-darwin")
                || !(filename.starts_with("std-") || filename.starts_with("libstd-"));

            // Trust: reject ineligible files before reading their bytes. In
            // particular, rlib/rmeta files need no proc-macro scan at all.
            if !can_be_rustc_dynamic_dep || proc_macros.contains(&filename) {
                continue;
            }
            let path = f.path();
            let is_dylib_or_debug = is_dylib(&path) || is_debug_info(&filename);

            // Trust: the name set comes from THIS build's stamp while `src_libdir`
            // belongs to the build compiler, a different generation whose
            // `-Cextra-filename` differs — so names alone cannot exclude proc
            // macros. Check every eligible dylib/debug file's actual bytes.
            if is_dylib_or_debug && !is_proc_macro_dylib(&path) {
                builder.copy_link(&path, &rustc_libdir.join(&filename), FileType::Regular);
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
        // is enabled. This is used by targets that produce WebAssembly
        // components in Rust such as `wasm32-wasip{2,3}`.
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

        if builder.config.llvm_tpde {
            debug!("`llvm_tpde` requested");
            // The rustc TPDE integration is Linux-only for now
            if !host.contains("linux") {
                builder.info(&format!("host target `{host}` not supported by tpde. skipping"));
            } else {
                // Put TPDE next to librustc_driver.so
                let tpde_output = builder.ensure(llvm::Tpde { target: host });
                let target_libdir =
                    builder.sysroot_target_libdir(target_compiler, target_compiler.host);
                let target_dst_lib =
                    target_libdir.join(tpde_output.plugin_path().file_name().unwrap());
                builder.copy_link(
                    tpde_output.plugin_path(),
                    &target_dst_lib,
                    FileType::NativeLibrary,
                );
            }
        }

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

        // Trust: ship the trust-ir → trust-cg self-host backend into this
        // sysroot's `codegen-backends/` when it is enabled for the host.
        //
        // ORDERING, and it is load-bearing in BOTH directions:
        //
        // * not earlier — the plugin is `dlopen`ed into this compiler and must
        //   share one copy of `librustc_driver` (and `libstd`) with it, so it
        //   links against the runtime dylibs copied into `rustc_libdir` above
        //   and against the rustc rmetas of the build that produced them.
        //
        // * not later — the `Std` step immediately below compiles std USING
        //   `target_compiler`. When `target_compiler`'s default backend is
        //   trust-ir-cg (the self-host configuration) that compilation, and the
        //   `--print=deployment-target` probe that sets it up, both resolve the
        //   backend at startup and cannot start without this file. This call
        //   used to sit at the end of `Assemble`, after the std block, and the
        //   module docs' claim that a stage-N compiler "finds it before it
        //   compiles a single unit of stage N+1" was true only for N+1: stage N
        //   compiles its OWN std here, first. Measured 2026-09-14: a self-compile
        //   with `codegen-backends = ["trust-ir-cg", "llvm", "trust-cg"]` failed
        //   6:27 in, immediately after "Creating standalone Trust sysroot for
        //   stage1 compiler", with `failed to find a codegen-backends folder in
        //   the sysroot candidates: build/<host>/stage1`.
        crate::core::build_steps::trust_ir_cg::install_into_sysroot(
            builder,
            build_compiler,
            target_compiler,
        );

        // Trust: install mathematical DATA before this compiler can execute for Std.
        crate::core::build_steps::vf5_resource::install_into_sysroot(
            builder, build_compiler, target_compiler, &sysroot,
        );

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
            // (`add_to_sysroot`, with its duplicate-rustc-crate guard) that
            // the rustc-private sysroot path uses; copies exactly what
            // restore-rustc-dev.sh copied (whole stamp -> target libdir).
            //
            // SELF-HOST ONLY. The convenience above is defined for a compiler
            // being built to run on the machine building it; the librustc stamp
            // of a CROSS-HOST build carries both, and they are not
            // interchangeable. Its rustc_private proc-macro crates are built for
            // and loaded by the BUILD machine, while the rest of the stamp is
            // built for the host the assembled compiler will run on — so the
            // same crate name appears twice, once per architecture. Copying both
            // into one target libdir puts a build-machine dylib in a sysroot that
            // cannot load it, and trips `add_to_sysroot`'s
            // duplicate-rustc-crate guard besides. A cross-host build keeps the
            // clean pruned sysroot, exactly as dist images do; `trustc-dev`
            // remains the supported way to get rustc_private for such a target.
            if builder.kind == Kind::Build && build_compiler.host == host {
                install_local_rustc_dev(builder, target_compiler, &stamp, &std_stamp);
            }
            crate::core::build_steps::tool::ensure_user_facing_tools(
                builder,
                target_compiler,
                &sysroot,
            );
        }

        validate_assembled_local_compiler(builder, target_compiler, &sysroot);

        // Trust: final Targo binds the completed compiler image/runtime. Keep
        // its construction out of Sysroot's own graph, while retaining every
        // selected tool and the existing intermediate-generation policy.
        crate::core::build_steps::tool::finish_verifier_tool_bins_after_assembly(
            builder,
            target_compiler,
            &sysroot,
        );

        // Trust: that was this sysroot's last frontend install. A `targo` it
        // ships carries its `cargo` alias, or assembly stops here.
        crate::core::build_steps::tool::validate_sysroot_compat_aliases(
            builder,
            target_compiler,
            &sysroot,
        );

        // Trust: this invocation assembled the host stage-1 compiler, so a green finish
        // records the key of this build directory for other worktrees to seed from
        // (`utils::trust_stage1_seed`, EW-9).
        if target_compiler.stage == 1
            && target_compiler.host == builder.config.host_target
            && !builder.config.dry_run()
        {
            crate::utils::trust_stage1_seed::note_stage1_assembled();
        }

        target_compiler
    }
}

/// Link some files into a rustc sysroot.
///
/// For a particular stage this will link the file listed in `stamp` into the
/// `sysroot_dst` provided.
// `add_rustc_to_sysroot` used to be a separate entry point whose ONLY difference
// was passing `SysrootMetadataMode::PreserveMetadataOnlyDeps` rather than
// `Deduplicate`. That mode chose between "drop metadata-only artifacts whose
// crate name already has an rlib" and "keep them"; the dropping half was wrong
// for both populations (see `prune_superseded_sysroot_artifacts`), so the two
// modes now describe identical behaviour and the enum, the wrapper and the
// second entry point are gone with it.
#[track_caller]
pub fn add_to_sysroot(
    builder: &Builder<'_>,
    sysroot_dst: &Path,
    sysroot_host_dst: &Path,
    stamp: &BuildStamp,
) {
    let self_contained_dst = &sysroot_dst.join("self-contained");
    t!(fs::create_dir_all(sysroot_dst));
    t!(fs::create_dir_all(sysroot_host_dst));
    t!(fs::create_dir_all(self_contained_dst));

    let mut crates = HashMap::new();
    let stamp_entries = builder.read_stamp_file(stamp);
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

        if let Some(artifact) = parse_hashed_rust_artifact(filename) {
            prune_superseded_sysroot_artifacts(dst, artifact);
        }

        builder.copy_link(&path, &dst.join(filename), FileType::Regular);
        record_sysroot_install(dst, filename);
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

    let runtime_identity = rustc_private_tool_runtime_identity(builder, runtime_compiler);

    prepare_rustc_private_sysroot_with_runtime_identity(
        builder,
        rustc_build_compiler,
        target,
        label,
        Some(&runtime_identity),
    )
}

/// The identity of the runtime a rustc-private tool built for `runtime_compiler`
/// loads: every dylib in that compiler's own dylib directories
/// (`Builder::rustc_lib_paths`, where the tool's rpath points: librustc_driver
/// and libstd), by path and bytes.
///
/// Not the compiler's target libdir. `x build`'s rustc-dev top-up puts the
/// compiler's proc-macro dylibs there and `x dist`'s assembly prunes them
/// (`Assemble`), and no tool loads them when it runs. With that directory in
/// the identity, one tool had two private sysroots, so two `-L` paths in its
/// RUSTFLAGS, two cargo metadata hashes and two binaries: the dist archives
/// shipped one and the local stage2 sysroot held the other, and the seed
/// mint's `verify-archives-carry-compared` refused the cut (D8 of the first
/// mint, 2026-10-14).
fn rustc_private_tool_runtime_identity(
    builder: &Builder<'_>,
    runtime_compiler: Compiler,
) -> String {
    let runtime_dylibs = rustc_runtime_dylib_files(builder, runtime_compiler);
    assert!(
        !runtime_dylibs.is_empty(),
        "cannot build a rustc-private tool for stage{} compiler ({}): \
         no runtime dylibs found in runtime search paths: {}",
        runtime_compiler.stage,
        runtime_compiler.host,
        builder
            .rustc_lib_paths(runtime_compiler)
            .iter()
            .map(|path| path.display().to_string())
            .collect::<Vec<_>>()
            .join(", "),
    );
    rustc_private_runtime_dylib_identity(runtime_dylibs)
}

// Trust: enumerate the actual host runtime, not the target std output being built.
fn rustc_runtime_dylib_files(builder: &Builder<'_>, runtime_compiler: Compiler) -> Vec<PathBuf> {
    let mut runtime_paths = builder.rustc_lib_paths(runtime_compiler);
    runtime_paths.dedup();
    runtime_paths.iter().flat_map(|path| rustc_private_runtime_dylibs(path)).collect()
}

/// Trust: the shim's path and a thin launcher's mtime do not identify rustc.
/// Hash its real launcher and host runtime bytes before reusing std or Cargo's
/// cached version query. A static compiler legitimately has no runtime dylibs.
pub(crate) fn std_compiler_runtime_identity(builder: &Builder<'_>, compiler: Compiler) -> String {
    std_compiler_runtime_files_identity(
        builder.rustc(compiler),
        rustc_runtime_dylib_files(builder, compiler),
    )
}

fn std_compiler_runtime_files_identity(launcher: PathBuf, mut runtime: Vec<PathBuf>) -> String {
    runtime.push(launcher);
    rustc_private_files_identity(b"trust-std-compiler-runtime-v1\0", &mut runtime)
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
    add_to_sysroot(builder, &target_dir, &host_dir, &stamp);

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

/// Every (directory, filename) this bootstrap run has installed into a sysroot.
///
/// `lib/rustlib/<target>/lib` is populated TWICE from two different stamps — once
/// for std (`add_to_sysroot`, line ~2728) and once for rustc
/// (the second `add_to_sysroot` call) — and the two populations legitimately
/// contain the SAME external crates at DIFFERENT versions: std links `hashbrown`,
/// `libc`, `object`, `memchr`, `gimli` and `miniz_oxide` for backtrace, and the
/// compiler links its own copies. Neither call can see the other's stamp, so
/// without this record the second population's prune deletes the first's
/// artifacts as "stale" purely because the crate NAME matches. They are not
/// stale; they are the other half of the same build.
static SYSROOT_INSTALLED_THIS_RUN: LazyLock<Mutex<HashSet<(PathBuf, String)>>> =
    LazyLock::new(|| Mutex::new(HashSet::new()));

fn record_sysroot_install(dst: &Path, filename: &str) {
    SYSROOT_INSTALLED_THIS_RUN
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .insert((dst.to_path_buf(), filename.to_owned()));
}

fn was_installed_this_run(dst: &Path, filename: &str) -> bool {
    SYSROOT_INSTALLED_THIS_RUN
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .contains(&(dst.to_path_buf(), filename.to_owned()))
}

fn prune_stale_sysroot_metadata(dst: &Path, crate_name: &str, active_stem: &str) {
    prune_stale_sysroot_artifact_kind(
        dst,
        crate_name,
        active_stem,
        RustArtifactKind::Rmeta,
        MultiVersion::Legitimate,
    );
}

/// Whether a same-name, different-hash artifact can be a real second version of
/// this crate, or is necessarily a leftover from an earlier build.
#[derive(Clone, Copy, PartialEq, Eq)]
enum MultiVersion {
    /// External and std crates: std and rustc each bring their own copy, so a
    /// differing hash installed by THIS run must be kept.
    Legitimate,
    /// `rustc_*` crates: `add_to_sysroot`'s duplicate-crate check enforces one
    /// version, so a differing hash is always stale and pruned unconditionally.
    Impossible,
}

fn prune_stale_sysroot_artifact_kind(
    dst: &Path,
    crate_name: &str,
    active_stem: &str,
    active_kind: RustArtifactKind,
    multi_version: MultiVersion,
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
            // STALE means "left over from an earlier build", not "belongs to the
            // other population of this one". Deleting by crate NAME alone removed
            // artifacts that rustc_public and friends still reference by HASH,
            // which made every out-of-tree `rustc_private` consumer fail to load
            // with E0460 ("found possibly newer version of crate `hashbrown`
            // which `rustc_public` depends on") against a sysroot that had just
            // been built successfully. Measured 2026-08-30: 12 artifacts across
            // 9 crate names were missing from a clean stage2, and supplying them
            // by hand turned a total failure into a clean compile.
            if multi_version == MultiVersion::Legitimate && was_installed_this_run(dst, filename) {
                trace!(
                    path = ?entry.path(),
                    crate_name,
                    active_stem,
                    "keeping same-name artifact installed by this run"
                );
                continue;
            }
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

    // Trust: a dist/test assembly must not retain a previous local build's
    // compiler helper population. A local build reinstalls its current stamp.
    let private = dst.join("rustc-dependencies");
    if private.exists() {
        t!(fs::remove_dir_all(&private));
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

/// Trust: install one actual compiler producer's development closure using the
/// same routing for ordinary local Assemble and the explicit BUILD component.
fn install_local_rustc_dev(
    builder: &Builder<'_>,
    compiler: Compiler,
    compiler_stamp: &BuildStamp,
    std_stamp: &BuildStamp,
) {
    let host_libdir = builder.sysroot_target_libdir(compiler, compiler.host);
    add_to_sysroot(builder, &host_libdir, &host_libdir, compiler_stamp);
    // Preserve both closures without ambiguous bare std helper imports.
    separate_compiler_std_dependencies(
        &host_libdir,
        &builder.read_stamp_file(std_stamp),
        &builder.read_stamp_file(compiler_stamp),
    );
    dist::maybe_install_llvm_native_dev(builder, compiler.host, &builder.sysroot(compiler));
}

/// Trust: std and rustc legitimately depend on different versions of helpers
/// such as libc/hashbrown. Keep std's exact stems public and every current
/// compiler helper in a dependency-only directory; deleting the latter breaks
/// direct rustc_private consumers with E0460, while leaving both public causes
/// bare helper imports to fail with E0464.
fn separate_compiler_std_dependencies(
    dst: &Path,
    std_entries: &[(PathBuf, DependencyType)],
    compiler_entries: &[(PathBuf, DependencyType)],
) {
    let mut std_stems: HashMap<String, HashSet<String>> = HashMap::new();
    for (path, _) in std_entries {
        let Some(filename) = path.file_name().and_then(OsStr::to_str) else { continue };
        let Some(artifact) = parse_hashed_rust_artifact(filename) else { continue };
        std_stems
            .entry(artifact.crate_name.to_owned())
            .or_default()
            .insert(artifact.stem.to_owned());
    }
    let current: HashSet<_> = compiler_entries
        .iter()
        .filter_map(|(path, _)| path.file_name().map(OsStr::to_owned))
        .collect();
    let private = dst.join("rustc-dependencies");
    for entry in t!(fs::read_dir(dst)) {
        let entry = t!(entry);
        let filename = entry.file_name();
        let Some(name) = filename.to_str() else { continue };
        let Some(artifact) = parse_hashed_rust_artifact(name) else { continue };
        let Some(stems) = std_stems.get(artifact.crate_name) else { continue };
        if stems.contains(artifact.stem) {
            continue;
        }
        if current.contains(&filename) {
            t!(fs::create_dir_all(&private));
            let private_path = private.join(&filename);
            // Trust: repeated assembly can give these paths the same inode.
            // POSIX rename then does nothing, leaving the helper public too.
            // Remove the old destination so the move always removes that name.
            t!(match fs::remove_file(&private_path) {
                Ok(()) => Ok(()),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
                Err(error) => Err(error),
            });
            t!(fs::rename(entry.path(), private_path));
            record_sysroot_install(&private, name);
        } else {
            // A public helper from an earlier build is in neither active
            // population. Do not export it as part of the new private closure.
            t!(fs::remove_file(entry.path()));
        }
    }
}

/// Remove artifacts an EARLIER build left behind for the crate now being
/// installed. Everything the current stamps name is copied unconditionally.
///
/// This used to additionally SKIP metadata-only artifacts whose crate name
/// already had an rlib in the sysroot under a different hash, to stop a stray
/// `.rmeta` making `extern crate foo;` ambiguous. That rule cannot be stated in
/// terms of the crate name, and as written it discarded artifacts the build
/// genuinely needs:
///
///   * `lib/rustlib/<target>/lib` receives TWO populations from two stamps —
///     std's and rustc's — and they legitimately share crate names at different
///     versions (`hashbrown`, `libc`, `object`, `memchr`, `gimli`,
///     `miniz_oxide`, `cfg_if`, `getopts`, `rustc_demangle`).
///   * std is built with `-Zno-embed-metadata`, so it ships
///     `ArtifactKeepMode::BothRlibAndRmeta` precisely BECAUSE the separate
///     `.rmeta` is required to compile against it. A rule that drops `.rmeta`
///     files is therefore never safe here, whatever the hashes say.
///
/// Measured on a clean stage2 (2026-08-30): 12 artifacts across 9 crate names
/// were absent, and `extern crate rustc_public;` — nothing else — failed with
/// E0460 `found possibly newer version of crate hashbrown which rustc_public
/// depends on`. That is every out-of-tree `rustc_private` consumer, against a
/// sysroot the build had just reported as successful.
fn prune_superseded_sysroot_artifacts(dst: &Path, artifact: RustArtifact<'_>) {
    if is_rustc_private_crate(artifact.crate_name) {
        // The duplicate-crate check at the end of `add_to_sysroot` enforces that
        // these exist at exactly one version, so a different hash under the same
        // name is unambiguously a leftover.
        prune_stale_sysroot_artifact_kind(
            dst,
            artifact.crate_name,
            artifact.stem,
            artifact.kind,
            MultiVersion::Impossible,
        );
        return;
    }

    if artifact.kind == RustArtifactKind::Rlib {
        prune_stale_sysroot_metadata(dst, artifact.crate_name, artifact.stem);
    }
}

#[cfg(test)]
mod tests;

/// Specifies which rlib/rmeta artifacts outputted by Cargo should be put into the resulting
/// build stamp, and thus be included in dist archives and copied into sysroots by default.
/// Note that some kinds of artifacts are copied automatically (e.g. native libraries).
pub enum ArtifactKeepMode {
    // Trust: omit the unconstructed OnlyDylib mode; native libraries are retained below.
    /// Only keep .rmeta files, ignore .rlib files
    OnlyRmeta,
    /// Keep both .rlib and .rmeta files.
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
                target: CargoTarget { crate_types, .. },
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
            if is_precise_cargo_artifact(filename, target_root_dir) {
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
        helpers::exit_process(1);
    }

    if builder.config.dry_run() {
        return Vec::new();
    }

    // Ok now we need to actually find all the files listed in `toplevel`. We've
    // got a list of prefix/extensions and we need to find the hashed copy in
    // active Cargo layout corresponding to each top-level artifact. Trust:
    // accept both layouts; the stage0 compatibility lane uses shared `deps`.
    let contents = cargo_artifact_candidates(target_root_dir);
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

// Trust: Cargo reports exact dependency paths in either supported layout.
// Treating an already-hashed legacy `deps/libfoo-HASH.rmeta` as a top-level
// alias incorrectly searches for `libfoo-HASH-OTHERHASH.rmeta`.
// Upstream 1.101: example artifacts are likewise already hashed
// (`examples/libfoo-HASH.rmeta`, e.g. trust-os's `dirfd` example under
// `x.py check --all-targets`); treating one as a top-level alias searches
// for a second hash that does not exist and panics the check.
fn is_precise_cargo_artifact(path: &Path, target_root_dir: &Path) -> bool {
    path.starts_with(target_root_dir.join("deps"))
        || path.starts_with(target_root_dir.join("build"))
        || path.starts_with(target_root_dir.join("examples"))
}

// Trust: top-level aliases still require byte-for-byte matching, whether Cargo
// stores their hashed counterparts in `deps` or `build/<pkg>/<hash>/out`.
fn cargo_artifact_candidates(target_root_dir: &Path) -> Vec<(PathBuf, String, fs::Metadata)> {
    let read_dir = |path: &Path| path.read_dir().ok().into_iter().flatten().filter_map(Result::ok);
    let unit_outputs = read_dir(&target_root_dir.join("build"))
        .flat_map(|e| read_dir(&e.path()))
        .flat_map(|e| read_dir(&e.path()))
        .flat_map(|e| read_dir(&e.path()));
    read_dir(&target_root_dir.join("deps"))
        .chain(unit_outputs)
        .map(|e| (e.path(), e.file_name().into_string().unwrap(), t!(e.metadata())))
        .collect()
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
                // Trust: every unit this run's cargo reports is a root of the prune that
                // follows a successful run (`utils::trust_prune`).
                #[cfg(unix)]
                crate::utils::trust_prune::note_cargo_message(&msg);
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

#[derive(Deserialize, Debug)]
pub struct CargoTarget<'a> {
    pub crate_types: Vec<Cow<'a, str>>,
    #[serde(default)]
    pub doc: bool,
}

#[derive(Deserialize, Debug)]
#[serde(tag = "reason", rename_all = "kebab-case")]
pub enum CargoMessage<'a> {
    CompilerArtifact {
        filenames: Vec<Cow<'a, str>>,
        target: CargoTarget<'a>,
        // Trust: whether cargo found the unit up to date and compiled nothing; the prune
        // after a successful run roots the unit either way (`utils::trust_prune`).
        #[serde(default)]
        fresh: bool,
    },
    // Trust: the `OUT_DIR` of the build-script run unit, which the prune roots.
    BuildScriptExecuted {
        #[serde(default)]
        out_dir: Option<Cow<'a, str>>,
    },
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
