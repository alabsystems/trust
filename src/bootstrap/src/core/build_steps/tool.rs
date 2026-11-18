//! This module handles building and managing various tools in bootstrap
//! build system.
//!
//! **What It Does**
//! - Defines how tools are built, configured and installed.
//! - Manages tool dependencies and build steps.
//! - Copies built tool binaries to the correct locations.
//!
//! Each Rust tool **MUST** utilize `ToolBuild` inside their `Step` logic,
//! return `ToolBuildResult` and should never prepare `cargo` invocations manually.

// Trust: preserve unknown ambient compiler postures when scheduling intermediate tools.
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::{env, fs, io};

use crate::core::build_steps::compile::{CargoMessage, is_lto_stage};
use crate::core::build_steps::dist::LLD_FILE_NAMES;
use crate::core::build_steps::{compile, llvm};
use crate::core::builder::{
    self, Builder, Cargo as CargoCommand, CargoInput, CargoProgram, CommandLineStep, Kind,
    RunConfig, ShouldRun, Step, StepMetadata, apply_pgo, cargo_profile_var,
};
use crate::core::compiler::Compiler;
use crate::core::config::{Allocator, Config, DebuginfoLevel, RustcLto, TargetSelection};
use crate::core::session::{FileType, Mode};
use crate::utils::exec::{BootstrapCommand, ExecutionContext, command};
use crate::utils::helpers::{self, add_dylib_path, dylib_path_var, exe, t};
use crate::utils::trust_source_identity;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "tool/engineering_pairing.rs"]
mod engineering_pairing;
#[path = "tool/native_build_tool.rs"]
mod native_build_tool;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "tool/paired_compiler.rs"]
mod paired_compiler;
pub use native_build_tool::TargoNativeBuildTool;
// Trust: the sysroot compatibility-alias check lives in its own child module, which keeps this
// upstream file under tidy's 3000-line limit.
mod sysroot_aliases;
pub(crate) use sysroot_aliases::validate_sysroot_compat_aliases;
#[cfg(test)]
use sysroot_aliases::{inspect_sysroot_compat_aliases, sysroot_compat_alias_problems};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum SourceType {
    InTree,
    Submodule,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ToolArtifactKind {
    Binary,
    /// Explicit host/stage0 artifact with independently held compiler inputs.
    NativeEngineeringBinary,
    // Trust: artifact-only frontend with a separately held oracle compiler.
    RetainedFrontendBinary,
    // Trust: build-host mathematical DATA helper, built through the normal tool step.
    Example,
    Library,
}

// Trust: old Cargo exports its Rust sysroot source remap to native build scripts.
// OpenSSL's Configure writes those arguments into Make without preserving spaces.
// Give the snapshot a different spelling, not different files or compiler identity.
#[cfg(unix)]
fn bootstrap_tool_sysroot_alias(
    snapshot: &Path,
    build_out: &Path,
    dry_run: bool,
) -> io::Result<Option<PathBuf>> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    if !snapshot.is_absolute() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "snapshot sysroot must be absolute",
        ));
    }
    if !snapshot.as_os_str().as_encoded_bytes().iter().any(u8::is_ascii_whitespace) {
        return Ok(None);
    }
    if build_out.as_os_str().as_encoded_bytes().iter().any(u8::is_ascii_whitespace) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "the legacy seed's native tool build needs a whitespace-free build-dir",
        ));
    }
    let mut hash = DefaultHasher::new();
    snapshot.hash(&mut hash);
    let alias = build_out.join(format!("bootstrap-tool-sysroot-{:016x}", hash.finish()));
    if !dry_run {
        fs::create_dir_all(build_out)?;
        match fs::read_link(&alias) {
            Ok(target) if target == snapshot => {}
            Ok(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::AlreadyExists,
                    format!("refusing to replace a different sysroot alias: {}", alias.display()),
                ));
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                std::os::unix::fs::symlink(snapshot, &alias)?;
            }
            Err(error) => return Err(error),
        }
    }
    Ok(Some(alias))
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct ToolBuild {
    /// Compiler that will build this tool.
    build_compiler: Compiler,
    /// Compiler/sysroot that will own the built tool.
    output_compiler: Compiler,
    target: TargetSelection,
    tool: &'static str,
    path: &'static str,
    mode: Mode,
    source_type: SourceType,
    extra_features: Vec<String>,
    /// Nightly-only features that are allowed (comma-separated list).
    allow_features: &'static str,
    /// Additional arguments to pass to the `cargo` invocation.
    cargo_args: Vec<String>,
    /// Whether the tool builds a binary or a library.
    artifact_kind: ToolArtifactKind,
}

/// Result of the tool build process. Each `Step` in this module is responsible
/// for using this type as `type Output = ToolBuildResult;`
#[derive(Clone)]
pub struct ToolBuildResult {
    /// Artifact path of the corresponding tool that was built.
    pub tool_path: PathBuf,
    /// Compiler used to build the tool.
    pub build_compiler: Compiler,
    /// All Cargo artifacts produced during the compilation of this tool
    pub artifacts: Vec<PathBuf>,
}

impl Step for ToolBuild {
    type Output = ToolBuildResult;

    /// Builds a tool in `src/tools`
    ///
    /// This will build the specified tool with the specified `host` compiler in
    /// `stage` into the normal cargo output directory.
    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        let target = self.target;
        let mut tool = self.tool;
        let path = self.path;
        let input = self.cargo_input(builder);
        let retained_frontend = self.artifact_kind == ToolArtifactKind::RetainedFrontendBinary;
        let native_engineering =
            retained_frontend || self.artifact_kind == ToolArtifactKind::NativeEngineeringBinary;
        if native_engineering {
            assert_eq!(path, if retained_frontend { "targo-trust" } else { "src/tools/targo" });
            assert_eq!(self.build_compiler.stage, 0);
            assert_eq!(self.output_compiler.stage, 0);
            assert_eq!(self.target, builder.host_target);
            assert_eq!(self.build_compiler.host, builder.host_target);
            assert_eq!(self.mode, Mode::ToolTarget);
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let engineering = (native_engineering && !builder.config.dry_run())
            .then(|| engineering_pairing::Inputs::capture(builder, input))
            .transpose()
            .unwrap_or_else(|error| panic!("engineering compiler capture failed: {error}"));
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        assert!(!native_engineering, "native engineering pairing requires macOS arm64");

        // Trust: the mathematical DATA preparer is never built/executed for a foreign host.
        if self.artifact_kind == ToolArtifactKind::Example {
            assert_eq!(self.mode, Mode::ToolBootstrap);
            assert_eq!(self.target, builder.host_target);
            assert_eq!(self.build_compiler.stage, 0);
            assert_eq!(self.build_compiler.host, builder.host_target);
        }

        match self.mode {
            Mode::ToolRustcPrivate => {
                // FIXME: remove this, it's only needed for download-rustc...
                if !self.build_compiler.is_forced_compiler() && builder.download_rustc() {
                    builder.std(self.build_compiler, self.build_compiler.host);
                    builder.ensure(compile::Rustc::new(self.build_compiler, target));
                }
            }
            Mode::ToolStd => {
                // If compiler was forced, its artifacts should have been prepared earlier.
                if !self.build_compiler.is_forced_compiler() {
                    builder.std(self.build_compiler, target);
                }
            }
            Mode::ToolBootstrap | Mode::ToolTarget => {} // uses downloaded stage0 compiler libs
            _ => panic!("unexpected Mode for tool build"),
        }

        // Trust: this exact recipe is the root of the internal Cargo dependency.
        // Every other ToolTarget recipe uses the source-built engineering Cargo.
        let mut cargo = prepare_tool_cargo_with_input(
            builder,
            self.build_compiler,
            self.mode,
            target,
            Kind::Build,
            path,
            self.source_type,
            &self.extra_features,
            input,
        );
        // The private compile-time pairing input belongs solely to this SDK
        // constructor. Engineering/stage0 tools never inherit an ambient one.
        cargo.env_remove("TRUST_TARGO_PAIRED_COMPILER_PROFILE");
        // Trust: only the held constructor below may bind a distinct compiler.
        cargo.env_remove("CFG_TRUST_ORACLE_COMPILER_HASH");
        cargo.env_remove("CFG_TRUST_ORACLE_COMPILER_RELEASE");
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if let Some(inputs) = &engineering {
            if retained_frontend {
                inputs.bind_frontend(&mut cargo, &builder.host_target.triple.to_string())
            } else {
                inputs.bind(&mut cargo)
            }
            .unwrap_or_else(|error| panic!("engineering pairing failed: {error}"));
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if path == "src/tools/targo"
            && self.output_compiler.stage > 0
            && self.output_compiler.host == target
            && target == builder.config.host_target
        {
            paired_compiler::bind(builder, &mut cargo, self.output_compiler).unwrap_or_else(
                |error| panic!("cannot bind final Targo compiler pairing: {error}"),
            );
        }
        if self.mode == Mode::ToolRustcPrivate {
            add_rustc_private_tool_metadata_search_path(
                builder,
                &mut cargo,
                self.output_compiler,
                target,
            );
        }
        name_tool_ay_record_host_sysroot(builder, &mut cargo, self.mode, self.output_compiler);

        // The stage0 compiler changes infrequently and does not directly depend on code
        // in the current working directory. Therefore, caching it with sccache should be
        // useful.
        // This is only performed for non-incremental builds, as ccache cannot deal with these.
        if let Some(ref ccache) = builder.config.ccache
            && matches!(self.mode, Mode::ToolBootstrap)
            && !builder.config.incremental
        {
            cargo.env("RUSTC_WRAPPER", ccache);
        }

        // RustcPrivate tools (miri, clippy, rustfmt, rust-analyzer) and cargo
        // could use the additional optimizations.
        if is_lto_stage(&self.build_compiler)
            && (self.mode == Mode::ToolRustcPrivate || self.path == "src/tools/targo")
        {
            let lto = match builder.config.rust_lto {
                RustcLto::Off => Some("off"),
                RustcLto::Thin => Some("thin"),
                RustcLto::Fat => Some("fat"),
                RustcLto::ThinLocal => None,
            };
            if let Some(lto) = lto {
                cargo.env(cargo_profile_var("LTO", &builder.config, self.mode), lto);
            }
        }

        let pgo_config = match self.path {
            "src/tools/rustdoc" => Some(&builder.config.rustdoc_pgo),
            "src/tools/cargo" => Some(&builder.config.cargo_pgo),
            "src/tools/clippy" => Some(&builder.config.clippy_pgo),
            _ => None,
        };
        if let Some(pgo_config) = pgo_config {
            apply_pgo(builder, &mut cargo, self.build_compiler, pgo_config);
        }

        if !self.allow_features.is_empty() {
            cargo.allow_features(self.allow_features);
        }

        cargo.args(tool_cargo_args(builder.config.locked_deps, self.cargo_args));

        let _guard =
            builder.msg(Kind::Build, self.tool, self.mode, self.build_compiler, self.target);

        // we check this below
        let mut artifacts = vec![];
        let build_success = compile::stream_cargo(builder, cargo, vec![], &mut |msg| match msg {
            CargoMessage::CompilerArtifact { filenames, .. } => {
                artifacts.extend(filenames.into_iter().map(|p| PathBuf::from(p.as_ref())));
            }
            // Trust: the variant now carries the run's `OUT_DIR` (`utils::trust_prune`).
            CargoMessage::BuildScriptExecuted { .. } => {}
            CargoMessage::BuildFinished => {}
        });

        if !build_success {
            helpers::exit_process(1);
        } else {
            // HACK(#82501): on Windows, the tools directory gets added to PATH when running tests, and
            // compiletest confuses HTML tidy with the in-tree tidy. Name the in-tree tidy something
            // different so the problem doesn't come up.
            if tool == "tidy" {
                tool = "rust-tidy";
            }
            let tool_path = match self.artifact_kind {
                ToolArtifactKind::Binary
                | ToolArtifactKind::NativeEngineeringBinary
                | ToolArtifactKind::RetainedFrontendBinary => copy_link_tool_bin(
                    builder,
                    self.output_compiler,
                    self.target,
                    self.mode,
                    self.build_compiler,
                    tool,
                    input,
                ),
                ToolArtifactKind::Example => {
                    let source = builder
                        .cargo_out(self.build_compiler, input.cache_mode(self.mode), self.target)
                        .join("examples")
                        .join(exe(tool, self.target));
                    let destination = builder
                        .tools_dir(self.output_compiler, self.target)
                        .join(exe(tool, self.target));
                    builder.copy_link(&source, &destination, FileType::Executable);
                    destination
                }
                ToolArtifactKind::Library => builder
                    .cargo_out_for_input(self.build_compiler, self.mode, self.target, input)
                    .join(format!("lib{tool}.rlib")),
            };

            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            if let Some(inputs) = &engineering {
                inputs
                    .finish(builder, &tool_path)
                    .unwrap_or_else(|error| panic!("engineering input bookend failed: {error}"));
            }
            ToolBuildResult { tool_path, build_compiler: self.build_compiler, artifacts }
        }
    }
}

// Trust: only the native engineering producer's exact recipe closes the cycle
// with the pinned seed; SDK Targo recipes remain consumers of the built Cargo.
impl ToolBuild {
    fn cargo_input(&self, builder: &Builder<'_>) -> CargoInput {
        let compiler = Compiler::new(0, builder.host_target);
        if *self == targo_tool_build_recipe(compiler, compiler, builder.host_target)
            || *self == native_build_tool::recipe(compiler, builder.host_target)
        {
            CargoInput::Seed.for_original(builder.sess)
        } else if *self == trustup_tool_build_recipe(compiler, compiler, builder.host_target) {
            CargoInput::CurrentBuildToolSnapshotStd
        } else if *self == targo_trust_tool_build_recipe(compiler, compiler, builder.host_target)
            || *self == retained_frontend_tool_build_recipe(compiler, builder.host_target)
        {
            CargoInput::CurrentBuildToolSnapshotStd
        } else {
            builder.cargo_input(self.mode)
        }
    }
}

// Trust: this binary is a BUILD-host DATA tool, not a compiler/proof producer.
// Snapshot std and CargoInput::Seed avoid any Assemble -> tool -> Assemble cycle.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Vf5ResourceTool;

// The host preparer links AY and trust-types with its default try-sugar API.
// Keep their actual language requirements local to this recipe.
const VF5_RESOURCE_ALLOW_FEATURES: &str =
    "min_specialization,allocator_ext,try_trait_v2,try_trait_v2_residual";

fn vf5_resource_tool_recipe(builder: &Builder<'_>) -> ToolBuild {
    let compiler = builder.compiler(0, builder.host_target);
    ToolBuild {
        build_compiler: compiler,
        output_compiler: output_compiler_for_tool(compiler, builder.host_target),
        target: builder.host_target,
        tool: "prepare_vf5_inputs",
        path: "crates/trust-certify",
        mode: Mode::ToolBootstrap,
        source_type: SourceType::InTree,
        extra_features: Vec::new(),
        allow_features: VF5_RESOURCE_ALLOW_FEATURES,
        cargo_args: vec!["--bin".into(), "prepare_vf5_inputs".into()],
        artifact_kind: ToolArtifactKind::Binary,
    }
}

impl Step for Vf5ResourceTool {
    type Output = ToolBuildResult;

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.ensure(vf5_resource_tool_recipe(builder))
    }
}

/// Trust (2026-10-09): a battery that links trust-cg-verify -- `targo-trust`
/// from this tree, or `ty` through its own
/// trust-cg pin -- admits only the `ay` whose bytes its build script recorded,
/// and it runs from the sysroot it is installed in, beside that sysroot's
/// `bin/ay`. Name that sysroot (`TOOLCHAIN_AY_RECORD_HOST_SYSROOT`), as
/// `compile::rustc_cargo` does for the compiler crates. Left to the build
/// compiler's `--print sysroot`, the stage-N battery recorded the stage N-1
/// sysroot's `ay`, the one the stage N-2 compiler built: it refused the `ay`
/// shipped beside it, and its bytes depended on the bootstrap seed, which the
/// pack cut's double compile reports as a difference. `ensure_default_verifier_tool_bins`
/// installs the sysroot's `ay` before any battery, so the named `ay` exists when
/// a battery's build script runs. Tools that do not link trust-cg-verify never
/// read the variable.
fn name_tool_ay_record_host_sysroot(
    builder: &Builder<'_>,
    cargo: &mut CargoCommand,
    mode: Mode,
    output_compiler: Compiler,
) {
    if mode == Mode::ToolTarget && output_compiler.stage > 0 {
        cargo.env(
            compile::AY_RECORD_HOST_SYSROOT_ENV,
            compile::local_sysroot_dir(builder, output_compiler),
        );
    }
}

#[expect(clippy::too_many_arguments)] // FIXME: reduce the number of args and remove this.
pub fn prepare_tool_cargo(
    builder: &Builder<'_>,
    compiler: Compiler,
    mode: Mode,
    target: TargetSelection,
    cmd_kind: Kind,
    path: &str,
    source_type: SourceType,
    extra_features: &[String],
) -> CargoCommand {
    prepare_tool_cargo_with_input(
        builder,
        compiler,
        mode,
        target,
        cmd_kind,
        path,
        source_type,
        extra_features,
        builder.cargo_input(mode),
    )
}

// Trust: share every flag and generated identity with the explicit seed edge.
#[expect(clippy::too_many_arguments)]
fn prepare_tool_cargo_with_input(
    builder: &Builder<'_>,
    compiler: Compiler,
    mode: Mode,
    target: TargetSelection,
    cmd_kind: Kind,
    path: &str,
    source_type: SourceType,
    extra_features: &[String],
    input: CargoInput,
) -> CargoCommand {
    let mut cargo = builder::Cargo::new_with_input(
        builder,
        compiler,
        mode,
        source_type,
        target,
        cmd_kind,
        input,
    );

    let path = PathBuf::from(path);
    let dir = builder.src.join(&path);
    // Trust: check every actual standalone tool graph before any real Step;
    // root metadata --no-deps cannot establish AY/Targo workspace readiness.
    builder.record_selected_tool_sources(path.join("Cargo.toml"));
    cargo.arg("--manifest-path").arg(dir.join("Cargo.toml"));

    // Trust: an explicit sysroot also reaches Cargo's compiler-info probe. A
    // binary symlink alone is canonicalized by the shipped 1.99 compiler.
    #[cfg(unix)]
    if compiler.stage == 0
        && (mode == Mode::ToolBootstrap
            || (mode == Mode::ToolTarget
                && (!builder.local_rebuild || input.uses_snapshot_compiler())))
        && (path.ends_with("targo") || matches!(input, CargoInput::CurrentBuildToolSnapshotStd))
    {
        let alias = if input.is_original_control() {
            // Trust: this is the actual separately held private seed runtime.
            // Its native invocation guard requires the original root; ordinary
            // filesystem aliases do not issue a replacement private sysroot.
            Some(builder.rustc_snapshot_sysroot().to_owned())
        } else {
            bootstrap_tool_sysroot_alias(
                builder.rustc_snapshot_sysroot(),
                &builder.out,
                builder.config.dry_run(),
            )
            .unwrap_or_else(|error| {
                panic!("cannot prepare the snapshot's native-tool sysroot: {error}")
            })
        };
        if let Some(alias) = alias {
            cargo.rustflag("--sysroot").rustflag(alias.to_str().expect("sysroot must be UTF-8"));
        } else if matches!(input, CargoInput::CurrentBuildToolSnapshotStd) {
            // Track the selected std spelling in Cargo's actual Rustflags;
            // do not rely only on an untracked shim environment difference.
            cargo.rustflag("--sysroot").rustflag(
                builder.rustc_snapshot_sysroot().to_str().expect("sysroot must be UTF-8"),
            );
        }
    }

    let mut features = extra_features.to_vec();
    if builder.sess.config.cargo_native_static {
        if path.ends_with("targo")
            || path.ends_with("tippy")
            || path.ends_with("miri")
            || path.ends_with("trustfmt")
        {
            cargo.env("LIBZ_SYS_STATIC", "1");
        }
        if path.ends_with("targo") {
            features.push("all-static".to_string());
        }
    }
    if path.ends_with("targo") && !features.iter().any(|feature| feature == "all-static") {
        features.push("vendored-openssl".to_string());
        // Trust: VENDOR LIBGIT2 ON THIS PATH TOO (2026-07-30). Without it,
        // `libgit2-sys`'s build script takes
        // `try_to_use_system_libgit2 = !vendored && !zlib_ng_compat` (build.rs:113)
        // and pkg-config-probes the system, so targo and cargo take a RUNTIME
        // dependency on Homebrew's /opt/homebrew/opt/libgit2/lib/libgit2.1.9.dylib.
        //
        // That dylib is package-manager-owned and `brew deps rust` lists it, so
        // `brew uninstall rust && brew autoremove` deletes it and every targo on the
        // machine dies at dyld load — with targo being how everything here is built.
        // It also drifts underneath already-built binaries: measured 2026-07-30,
        // stage0/bin/targo was linked against libgit2 1.9.4 and stage1/bin/targo
        // against 1.9.6, i.e. brew upgraded it between the two.
        //
        // `all-static` (src/tools/targo/Cargo.toml:301) already implies
        // vendored-libgit2, which is why the guard above excludes that case. This
        // makes the ORDINARY path match, exactly as vendored-openssl already does —
        // OpenSSL was vendored here and libgit2 was simply missed. Vendoring needs no
        // network: the bundled C tree ships inside the crate.
        features.push("vendored-libgit2".to_string());
    }

    // build.tool.TOOL_NAME.features in bootstrap.toml allows specifying which features to enable
    // for a specific tool. `extra_features` instead is not controlled by the toml and provides
    // features that are always enabled for a specific tool (e.g. "in-rust-tree" for rust-analyzer).
    // Finally, `prepare_tool_cargo` above here might add more features to adapt the build
    // to the chosen flags (e.g. "all-static" for cargo if `cargo_native_static` is true).
    builder
        .config
        .tool
        .iter()
        .filter(|(tool_name, _)| path.file_name().and_then(OsStr::to_str) == Some(tool_name))
        .for_each(|(_, tool)| features.extend(tool.features.clone().unwrap_or_default()));

    // clippy tests need to know about the stage sysroot. Set them consistently while building to
    // avoid rebuilding when running tests.
    cargo.env("SYSROOT", builder.sysroot(compiler));

    // Make sure we explicitly add rustc_private libs to path centrally here so that
    // RustcPrivate tools can pick them up.
    if mode == Mode::ToolRustcPrivate {
        cargo.add_rustc_lib_path(builder);
    }

    // if tools are using lzma we want to force the build script to build its
    // own copy
    cargo.env("LZMA_API_STATIC", "1");

    // See also the "JEMALLOC_SYS_WITH_LG_PAGE" setting in the compile build step.
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

    // CFG_RELEASE is needed by rustfmt (and possibly other tools) which
    // import rustc-ap-rustc_attr which requires this to be set for the
    // `#[cfg(version(...))]` attribute.
    cargo.env("CFG_RELEASE", builder.rust_release());
    // Trust: see rustc_cargo_env; the identity lives in each native host entrypoint.
    cargo.env(
        "CFG_TRUST_ORACLE_HOST",
        if builder.version_info().sha().is_some() { "1" } else { "0" },
    );
    cargo.env("CFG_RELEASE_CHANNEL", &builder.config.channel);
    cargo.env("CFG_VERSION", builder.rust_version());
    // Trust: the product version, distinct from the rustc-protocol one above.
    cargo.env("CFG_TRUST_VERSION", builder.trust_version());
    cargo.env("CFG_RELEASE_NUM", &builder.version);
    cargo.env("DOC_RUST_LANG_ORG_CHANNEL", builder.doc_rust_lang_org_channel());

    // Trust: a dev stage-1 build's identity names its sources, not HEAD (TB1).
    if let Some(ref ver_date) = builder.version_info().commit_date() {
        cargo.env("CFG_VER_DATE", ver_date);
    }

    if let Some(ref ver_hash) = builder.version_info().sha() {
        cargo.env("CFG_VER_HASH", ver_hash);
    }

    if let Some(description) = &builder.config.description {
        cargo.env("CFG_VER_DESCRIPTION", description);
    }

    // Trust: the commit tuple a tool's build script reads instead of asking git (targo's
    // `build_commit_info.rs`, `rustc_tools_util::setup_version_info!` for tippy and
    // targo-miri, trust-analyzer's and its proc-macro server's `build.rs`, trustfmt's). A
    // tool built from this checkout's own sources carries the identity the compiler's
    // version carries (TB1), so that its version and `trustc -vV` name the same build and a
    // commit that keeps the identity reruns none of those scripts. A tool inside a submodule
    // keeps its own repository's commit (`trust_source_identity::tool_commit`). The
    // submodules are what `.gitmodules` lists, not `Builder::submodule_paths`, which names
    // `src/tools/targo` among the trees Trust carries in place of upstream's submodules
    // when it finds no `.gitmodules`.
    let submodules = build_helper::util::parse_gitmodules(&builder.src);
    let component = trust_source_identity::independent_tool_component(&path, &submodules);
    // GitInfo expects the repository root, not the nested executable package.
    let own_root = component
        .map(|component| builder.src.join(component.root()))
        .unwrap_or_else(|| dir.clone());
    let info =
        trust_source_identity::tool_commit(&path, &submodules, builder.version_info(), || {
            builder.config.git_info(builder.config.omit_git_hash, &own_root)
        });
    // Trust: the standalone verifier batteries do not compile the surrounding
    // Trust checkout. Its file!/diagnostic/debug paths follow its own source identity,
    // so changing Targo alone does not rebuild the solver. The applied mapping
    // stays in Cargo's fingerprint AND artifact unit_id; mixed tool and compiler
    // graphs keep the whole-build mapping prepared by Builder::cargo.
    if mode == Mode::ToolTarget && builder.config.rust_remap_debuginfo {
        if let Some(component) = component {
            let remap = trust_source_identity::component_remap(
                builder.exec_ctx(),
                &builder.src.join(component.root()),
                &info,
                component,
            )
            .unwrap_or_else(|error| {
                panic!("cannot name the independent verifier sources: {error}")
            });
            if let Some(remap) = remap {
                cargo.env("__CARGO_RUSTC_BOOTSTRAP_WS_REMAP", remap);
            }
        }
    }
    if let Some(sha) = info.sha() {
        cargo.env("CFG_COMMIT_HASH", sha);
    }

    if let Some(sha_short) = info.sha_short() {
        cargo.env("CFG_SHORT_COMMIT_HASH", sha_short);
    }

    if let Some(date) = info.commit_date() {
        cargo.env("CFG_COMMIT_DATE", date);
    }

    // Targo's build script treats presence as an explicit suppression. This
    // must accompany an omitted tuple; otherwise a direct Git diagnostic
    // fallback would silently defeat `rust.omit-git-hash = true`.
    if path == Path::new("src/tools/targo") && builder.config.omit_git_hash {
        cargo.env("CFG_OMIT_GIT_HASH", "1");
    }

    if !features.is_empty() {
        cargo.arg("--features").arg(features.join(", "));
    }

    // Enable internal lints for clippy and rustdoc
    // NOTE: this doesn't enable lints for any other tools unless they explicitly add `#![warn(rustc::internal)]`
    // See https://github.com/rust-lang/rust/pull/80573#issuecomment-754010776
    //
    // NOTE: We unconditionally set this here to avoid recompiling tools between `x check $tool`
    // and `x test $tool` executions.
    // See https://github.com/rust-lang/rust/issues/116538
    cargo.rustflag("-Zunstable-options");

    // NOTE: The root cause of needing `-Zon-broken-pipe=kill` in the first place is because `rustc`
    // and `rustdoc` doesn't gracefully handle I/O errors due to usages of raw std `println!` macros
    // which panics upon encountering broken pipes. `-Zon-broken-pipe=kill` just papers over that
    // and stops rustc/rustdoc ICEing on e.g. `rustc --print=sysroot | false`.
    //
    // cargo explicitly does not want the `-Zon-broken-pipe=kill` paper because it does actually use
    // variants of `println!` that handles I/O errors gracefully. It's also a breaking change for a
    // spawn process not written in Rust, especially if the language default handler is not
    // `SIG_IGN`. Thankfully cargo tests will break if we do set the flag.
    //
    // For the cargo discussion, see
    // <https://rust-lang.zulipchat.com/#narrow/stream/246057-t-cargo/topic/Applying.20.60-Zon-broken-pipe.3Dkill.60.20flags.20in.20bootstrap.3F>.
    //
    // For the rustc discussion, see
    // <https://rust-lang.zulipchat.com/#narrow/stream/131828-t-compiler/topic/Internal.20lint.20for.20raw.20.60print!.60.20and.20.60println!.60.3F>
    // for proper solutions.
    if !path.ends_with("targo") {
        // Use an untracked env var `FORCE_ON_BROKEN_PIPE_KILL` here instead of `RUSTFLAGS`.
        // `RUSTFLAGS` is tracked by cargo. Conditionally omitting `-Zon-broken-pipe=kill` from
        // `RUSTFLAGS` causes unnecessary tool rebuilds due to cache invalidation from building e.g.
        // cargo *without* `-Zon-broken-pipe=kill` but then rustdoc *with* `-Zon-broken-pipe=kill`.
        cargo.env("FORCE_ON_BROKEN_PIPE_KILL", "-Zon-broken-pipe=kill");
    }

    cargo
}

// Trust: pub(crate) so cargo-*test* invocations of rustc_private tools (e.g.
// `CrateRustdoc` in test.rs) can provide the same pruned-sysroot search paths
// that `ToolBuild::run` provides for the build. Trust prunes rustc_private
// from staged sysroots (upstream #108767 parity), so without these -L paths a
// `cargo test` rebuild of such a tool dies with an E0463 `extern crate
// rustc_*` cascade.
pub(crate) fn add_rustc_private_metadata_search_path(
    builder: &Builder<'_>,
    cargo: &mut CargoCommand,
    output_compiler: Compiler,
    target: TargetSelection,
) {
    add_rustc_private_metadata_search_path_impl(builder, cargo, output_compiler, target, false);
}

pub(crate) fn add_rustc_private_tool_metadata_search_path(
    builder: &Builder<'_>,
    cargo: &mut CargoCommand,
    output_compiler: Compiler,
    target: TargetSelection,
) {
    add_rustc_private_metadata_search_path_impl(builder, cargo, output_compiler, target, true);
}

fn add_rustc_private_metadata_search_path_impl(
    builder: &Builder<'_>,
    cargo: &mut CargoCommand,
    output_compiler: Compiler,
    target: TargetSelection,
    bind_to_runtime: bool,
) {
    if output_compiler.stage == 0 {
        return;
    }

    let mut rustc_build_compiler =
        RustcPrivateCompilers::build_compiler_from_stage(builder, output_compiler.stage);
    // With `full-bootstrap = false` (the default), compilers past stage 2 are
    // UPLIFTED rather than recompiled ("Uplifting rustc from stage2 to
    // stage3"), so no `stage{N}-rustc` artifacts — and thus no librustc stamp
    // — ever exist for them. An uplifted compiler's rustc-private libs ARE
    // the previous stage's, so walk down to the newest stage whose stamp
    // exists and use that stage's sysroot. (Previously this silently gave the
    // tool NO private sysroot, and e.g. a stage3 trustdoc build died with 152
    // `E0463 can't find crate for rustc_*` cascade errors.)
    let (host_dir, target_dir) = loop {
        let prepared = if bind_to_runtime {
            compile::prepare_rustc_private_tool_sysroot(
                builder,
                rustc_build_compiler,
                output_compiler,
                target,
                "rustc-private-tool",
            )
        } else {
            compile::prepare_rustc_private_sysroot(
                builder,
                rustc_build_compiler,
                target,
                "rustc-private-tool",
            )
        };
        match prepared {
            Some(dirs) => break dirs,
            None if rustc_build_compiler.stage > 1 => {
                rustc_build_compiler =
                    builder.compiler(rustc_build_compiler.stage - 1, rustc_build_compiler.host);
            }
            None => return,
        }
    };

    cargo.append_to_env(
        "RUSTC_ADDITIONAL_SYSROOT_PATHS",
        format!("{},{}", host_dir.to_str().unwrap(), target_dir.to_str().unwrap()),
        ",",
    );
    // The bootstrap rustc shim consumes RUSTC_ADDITIONAL_SYSROOT_PATHS, but
    // that custom env channel is intentionally invisible to Cargo's unit
    // fingerprint. Also pass the content-keyed paths as ordinary tracked
    // rustflags: changing either path then forces Cargo to relink the tool
    // instead of reusing a binary bound to the previous runtime ABI.
    for search_path in [&host_dir, &target_dir] {
        cargo.rustflag(&rustc_private_search_path_flag(search_path));
    }
}

fn rustc_private_search_path_flag(search_path: &Path) -> String {
    format!("-Lall={}", search_path.to_str().expect("private sysroot path must be UTF-8"))
}

/// Determines how to build a `ToolTarget`, i.e. which compiler should be used to compile it.
/// The compiler stage is automatically bumped if we need to cross-compile a stage 1 tool.
pub enum ToolTargetBuildMode {
    /// Build the tool for the given `target` using rustc that corresponds to the top CLI
    /// stage.
    Build(TargetSelection),
    /// Build the tool so that it can be attached to the sysroot of the passed compiler.
    /// Since we always dist stage 2+, the compiler that builds the tool in this case has to be
    /// stage 1+.
    Dist(Compiler),
}

/// Returns compiler that is able to compile a `ToolTarget` tool with the given `mode`.
pub(crate) fn get_tool_target_compiler(
    builder: &Builder<'_>,
    mode: ToolTargetBuildMode,
) -> Compiler {
    let (target, build_compiler_stage) = match mode {
        ToolTargetBuildMode::Build(target) => {
            assert!(builder.top_stage > 0);
            // If we want to build a stage N tool, we need to compile it with stage N-1 rustc
            (target, builder.top_stage - 1)
        }
        ToolTargetBuildMode::Dist(target_compiler) => {
            assert!(target_compiler.stage > 0);
            // If we want to dist a stage N rustc, we want to attach stage N tool to it.
            // And to build that tool, we need to compile it with stage N-1 rustc
            (target_compiler.host, target_compiler.stage - 1)
        }
    };

    let compiler = if builder.host_target == target {
        builder.compiler(build_compiler_stage, builder.host_target)
    } else {
        // If we are cross-compiling a stage 1 tool, we cannot do that with a stage 0 compiler,
        // so we auto-bump the tool's stage to 2, which means we need a stage 1 compiler.
        let build_compiler = builder.compiler(build_compiler_stage.max(1), builder.host_target);
        // We also need the host stdlib to compile host code (proc macros/build scripts)
        builder.std(build_compiler, builder.host_target);
        build_compiler
    };
    builder.std(compiler, target);
    compiler
}

// Trust: pub(crate) for the same reason as `add_rustc_private_metadata_search_path`.
pub(crate) fn output_compiler_for_tool(
    build_compiler: Compiler,
    target: TargetSelection,
) -> Compiler {
    Compiler::new(build_compiler.stage + 1, target)
}

/// Links a built tool binary with the given `name` from the build directory to the
/// tools directory.
fn copy_link_tool_bin(
    builder: &Builder<'_>,
    output_compiler: Compiler,
    target: TargetSelection,
    mode: Mode,
    build_compiler: Compiler,
    name: &str,
    input: CargoInput,
) -> PathBuf {
    let cargo_out =
        builder.cargo_out_for_input(build_compiler, mode, target, input).join(exe(name, target));
    let bin = builder.tools_dir(output_compiler, target).join(exe(name, target));
    builder.copy_link(&cargo_out, &bin, FileType::Executable);
    bin
}

fn copy_bins_to_sysroot(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    tool_path: &Path,
    bin_names: &[&str],
) -> PathBuf {
    assert!(!bin_names.is_empty(), "at least one sysroot bin name is required");
    let bindir = builder.sysroot(target_compiler).join("bin");
    t!(fs::create_dir_all(&bindir));
    let mut primary = None;
    for bin_name in bin_names {
        let dst = bindir.join(exe(bin_name, target_compiler.host));
        builder.copy_link(tool_path, &dst, FileType::Executable);
        primary.get_or_insert(dst);
    }
    primary.expect("non-empty bin_names should set primary destination")
}

fn install_rustc_private_tool_bins(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    bindir: &Path,
    tool_path: &Path,
    bin_names: &[&str],
) -> PathBuf {
    assert!(!bin_names.is_empty(), "at least one rustc-private bin name is required");
    t!(fs::create_dir_all(bindir));

    let installed = bin_names
        .iter()
        .map(|bin_name| {
            let destination = bindir.join(exe(bin_name, target_compiler.host));
            builder.copy_link(tool_path, &destination, FileType::Executable);
            destination
        })
        .collect::<Vec<_>>();

    for binary in &installed {
        validate_installed_rustc_private_tool(builder, target_compiler, binary);
    }

    installed[0].clone()
}

fn validate_installed_rustc_private_tool(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    binary: &Path,
) {
    if builder.config.dry_run() {
        return;
    }
    if target_compiler.host != builder.sess.host_target {
        // Cross-host binaries are not runnable by bootstrap. Do not probe
        // them with the build compiler's libraries: that would be a silent,
        // incoherent fallback. Their content-bound private-sysroot identity
        // still applies at build time.
        builder.info(&format!(
            "Skipping runtime coherence probe for cross-compiled rustc-private tool `{}` \
             (tool host {}, build host {})",
            binary.display(),
            target_compiler.host,
            builder.sess.host_target,
        ));
        return;
    }

    assert!(binary.is_file(), "installed rustc-private tool is missing: `{}`", binary.display());
    let mut runtime_paths = builder.rustc_lib_paths(target_compiler);
    let target_runtime_libdir =
        builder.sysroot_target_libdir(target_compiler, target_compiler.host);
    runtime_paths.push(target_runtime_libdir);
    runtime_paths.dedup();
    for runtime_dir in &runtime_paths {
        assert!(
            runtime_dir.is_dir(),
            "cannot validate installed rustc-private tool `{}`: \
             target runtime directory is missing: `{}`",
            binary.display(),
            runtime_dir.display(),
        );
    }

    let mut probe = command(binary);
    // Do not use `add_dylib_path` here: it appends ambient lookup paths, so a
    // missing current-generation dylib could fall through to a stale build
    // directory and falsely pass this coherence gate. Keep the exact desired
    // [owning rustc, optional CI LLVM, target std] order. On Windows this also
    // replaces PATH, but the owning rustc runtime is already the sysroot bin
    // directory and these probes do not spawn external programs.
    let exact_loader_path = env::join_paths(&runtime_paths).unwrap_or_else(|error| {
        panic!("cannot encode exact runtime loader path for `{}`: {error}", binary.display())
    });
    probe.env(dylib_path_var(), exact_loader_path);
    probe
        .env_remove("DYLD_FALLBACK_LIBRARY_PATH")
        .env_remove("LD_PRELOAD")
        .env_remove("DYLD_INSERT_LIBRARIES");
    let binary_stem = binary.file_stem();
    if binary_stem == Some(OsStr::new("trust-analyzer-proc-macro-srv")) {
        // The server deliberately rejects direct invocation unless callers
        // acknowledge that its protocol is an IDE implementation detail.
        probe.env("RUST_ANALYZER_INTERNALS_DO_NOT_USE", "1");
    }
    let probe_arg = if binary_stem == Some(OsStr::new("targo-fmt")) {
        // `targo-fmt --version` delegates to a sibling formatter, which may
        // not be installed yet while assembling its standalone component.
        // Help stays in-process and is sufficient to force the loader to
        // resolve this binary's runtime closure.
        "--help"
    } else {
        "--version"
    };
    probe.arg(probe_arg);
    assert!(
        probe.run(builder),
        "installed rustc-private tool `{}` failed its runtime coherence probe",
        binary.display(),
    );
}

pub(crate) fn restored_sysroot_bins(builder: &Builder<'_>) -> Vec<(&'static str, &'static str)> {
    restored_sysroot_bins_for_config(&builder.config, builder.sess.unstable_features())
}

fn default_source_solver_enabled(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
    ay_source_present: bool,
) -> bool {
    // Trust: `ay` is the core proof solver the (on-by-default) verifier calls
    // via `sibling_solver`; a `trustc` without a sibling `ay` silently degrades
    // every proof-authority obligation to `unknown`. It is therefore NOT an
    // optional user tool but a battery of the compiler itself: install it
    // whenever its in-tree source is present, independent of `extended`/`tools`.
    // (`tools` may still name it explicitly for a minimal build that vendored
    // only `ay`, and `targo-trust` closes over it as before. The closure also
    // runs the other way: solver batteries pull in the `targo`/`targo-trust`
    // frontend; see `default_verifier_tool_bins_enabled`.)
    ay_source_present
        || tool_enabled_for_tool_settings(extended, tools, "targo-trust")
        || tool_enabled_for_tool_settings(extended, tools, "ay")
}

fn targo_runtime_enabled(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
) -> bool {
    tool_enabled_for_tool_settings(extended, tools, "targo")
        // Both public Tippy frontends intentionally require a sibling Targo;
        // they reject ambient Cargo to avoid mixing toolchains. Selecting only
        // `tippy` must therefore close over this runtime dependency or
        // bootstrap constructs an installed-but-unusable frontend.
        || tool_enabled_for_tool_settings(extended, tools, "tippy")
}

fn default_verifier_tool_bins_enabled(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
    ay_source_present: bool,
) -> bool {
    targo_runtime_enabled(extended, tools)
        || tool_enabled_for_tool_settings(extended, tools, "targo-trust")
        || default_source_solver_enabled(extended, tools, ay_source_present)
}

/// Path (relative to the repo root) of the in-tree source manifest for each
/// verification backend that ships beside `trustc`. Presence of the manifest is
/// the authoritative "battery available" gate — it mirrors `require_submodule`'s
/// own existence check and degrades gracefully on a bare checkout.
const AY_SOURCE_MANIFEST: &str = "first-party/ay/crates/ay/Cargo.toml";
const TY_SOURCE_MANIFEST: &str = "first-party/ty/crates/tla-cli/Cargo.toml";
const CLEAN_SOURCE_MANIFEST: &str = "first-party/clean/crates/clean/Cargo.toml";

fn verifier_backend_source_present(src: &Path, manifest_rel: &str) -> bool {
    src.join(manifest_rel).exists()
}

fn locked_cargo_args(args: &[&str]) -> Vec<String> {
    std::iter::once("--locked").chain(args.iter().copied()).map(ToString::to_string).collect()
}

/// Compose recipe arguments with the lock policy already applied by `Builder::cargo`.
///
/// Recipes may require a checked-in lockfile even when `build.locked-deps` is false.
/// Keep that requirement, but do not repeat the global flag (Cargo rejects duplicate
/// `--locked`). Only this exact option is normalized; other arguments, including
/// attached option values and anything after `--`, retain their original spelling
/// and order. Cargo build also accepts hyphen-leading values for `--jobs`/`-j`;
/// preserve that next token even if it spells `--locked` (an invalid jobs value
/// belongs to Cargo's diagnostics, not this normalizer). This is not a general
/// Cargo argument rewriter.
fn tool_cargo_args(global_locked: bool, args: Vec<String>) -> Vec<String> {
    let mut locked = global_locked;
    let mut options = true;
    let mut jobs_value = false;
    args.into_iter()
        .filter(|arg| {
            if jobs_value {
                jobs_value = false;
                return true;
            }
            if arg == "--" {
                options = false;
            }
            if options && matches!(arg.as_str(), "--jobs" | "-j") {
                jobs_value = true;
            }
            if options && arg == "--locked" {
                let keep = !locked;
                locked = true;
                keep
            } else {
                true
            }
        })
        .collect()
}

fn ay_bootstrap_cargo_args(src: &Path) -> Vec<String> {
    let manifest_text = std::fs::read_to_string(src.join(AY_SOURCE_MANIFEST)).unwrap_or_default();
    ay_bootstrap_cargo_args_for_manifest(&manifest_text)
}

fn ay_bootstrap_cargo_args_for_manifest(manifest_text: &str) -> Vec<String> {
    // AY is part of the compiler bootstrap graph. Its checked-in lockfile
    // must describe the exact sibling-submodule closure; silently
    // re-resolving a private branch here makes fresh, credential-free
    // bootstrap non-reproducible.
    //
    // The bcp feature was RENAMED in ay (raw-pointer-bcp -> unsafe-bcp), and
    // hardcoding one spelling breaks every stage2 build whose ay pin sits on
    // the other side of the rename (2026-07-22: the deliberately-held ay pin
    // vs the updated bootstrap collided and no stage2 could build at
    // coherent pins). Probe the pinned manifest for the spelling it actually
    // declares. Fail-safe: an unreadable/ambiguous manifest keeps the
    // current spelling, so machines on the new ay never regress.
    let declares = |feature: &str| {
        let mut in_features = false;
        for line in manifest_text.lines() {
            let trimmed = line.split_once('#').map_or(line, |(code, _)| code).trim();
            if trimmed.starts_with('[') {
                in_features = trimmed == "[features]";
                continue;
            }
            if in_features
                && trimmed
                    .strip_prefix(feature)
                    .is_some_and(|rest| rest.trim_start().starts_with('='))
            {
                return true;
            }
        }
        false
    };
    let features = if declares("unsafe-bcp") || !declares("raw-pointer-bcp") {
        "cli,unsafe-bcp"
    } else {
        "cli,raw-pointer-bcp"
    };
    locked_cargo_args(&["--no-default-features", "--features", features])
}

// Trust: AY preserves allocation failure with Box::try_new. Its ahash dependency
// detects this nightly seed in build.rs and requests min_specialization. Keep
// these permissions recipe-local; AY does not need full specialization.
// The pinned alloc library labels Box::try_new allocator_ext, implied by
// allocator_api. The CLI also links veripb-formula -> smartstring, whose
// native-channel probe still enables allocator_api. Keep that permission local
// to this wider CLI graph; the shared proof-runtime census does not need it.
const AY_ALLOW_FEATURES: &str = "min_specialization,allocator_api,allocator_ext";
// Verifier CLIs retain their preexisting allocator_api permission: their wider
// registry closures are not the shared proof-runtime graph audited below.
const VERIFIER_BACKEND_ALLOW_FEATURES: &str =
    "min_specialization,specialization,allocator_api,allocator_ext";

fn ay_tool_build_recipe(
    build_compiler: Compiler,
    output_compiler: Compiler,
    target: TargetSelection,
    src: &Path,
) -> ToolBuild {
    ToolBuild {
        build_compiler,
        output_compiler,
        target,
        tool: "ay",
        mode: Mode::ToolTarget,
        path: "first-party/ay/crates/ay",
        source_type: SourceType::InTree,
        extra_features: Vec::new(),
        allow_features: AY_ALLOW_FEATURES,
        cargo_args: ay_bootstrap_cargo_args(src),
        artifact_kind: ToolArtifactKind::Binary,
    }
}

/// Build the `ay` battery of `target_compiler`'s sysroot and install it as
/// `<sysroot>/bin/ay`; `None` (and nothing built) when the tree carries no
/// in-tree AY source, or for stage 0.
///
/// The compiler's trust-cg verifier pins the bytes of exactly this file
/// (`compile::rustc_cargo`), so `Rustc::run` calls this for every kind before
/// it compiles a compiler, not only for the batteries-on local build: dist,
/// install and test must ship a compiler whose record names the AY beside
/// it. It is the same `ToolBuild` the batteries use, so it is built once.
pub(crate) fn ensure_sysroot_ay(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    sysroot: &Path,
) -> Option<PathBuf> {
    if target_compiler.stage == 0
        || !verifier_backend_source_present(&builder.src, AY_SOURCE_MANIFEST)
    {
        return None;
    }
    let target = target_compiler.host;
    let bindir = sysroot.join("bin");
    t!(fs::create_dir_all(&bindir));
    // Trust (DC-16a): a stage-2 `x.py build` whose change leaves the batteries alone
    // takes them from its source toolchain, `ay` first (`Stage2VerifierTools`).
    let (produced, sealed) = match taken_stage2_verifier_tools(builder, target_compiler) {
        Some(taken) => {
            let ay = taken.tool("ay").expect("a taken set starts with its ay");
            (ay.path.clone(), Some(ay.sha256.clone()))
        }
        None => {
            let build_compiler =
                get_tool_target_compiler(builder, ToolTargetBuildMode::Dist(target_compiler));
            let built = builder
                .ensure(ay_tool_build_recipe(build_compiler, target_compiler, target, &builder.src))
                .tool_path;
            (built, None)
        }
    };
    let tools_dir = builder.tools_dir(target_compiler, target_compiler.host);
    let ay = if builder.config.dry_run() {
        tools_dir.join(exe("ay", target_compiler.host))
    } else {
        let recorders = restored_sysroot_bins(builder)
            .into_iter()
            .filter(|(src_name, _)| AY_RECORDING_TOOLS.contains(src_name))
            .map(|(src_name, _)| {
                let bins = sysroot_bin_names_for_tool_source(src_name)
                    .into_iter()
                    .map(|name| exe(name, target_compiler.host))
                    .collect();
                (exe(src_name, target_compiler.host), bins)
            })
            .collect::<Vec<_>>();
        settle_installed_ay(
            &produced,
            sealed.as_deref(),
            &tools_dir,
            &bindir,
            &exe("ay", target_compiler.host),
            &recorders,
        )
        .unwrap_or_else(|error| panic!("cannot install {}: {error}", produced.display()))
    };
    let installed = bindir.join(exe("ay", target_compiler.host));
    builder.copy_link(&ay, &installed, FileType::Executable);
    Some(installed)
}

/// Trust (DC-16a): the tools of a stage>0 sysroot whose build can record its `bin/ay`:
/// every ToolTarget battery is told that sysroot (`name_tool_ay_record_host_sysroot`),
/// and trust-cg-verify, linked into any of them, records the `ay` it finds there.
const AY_RECORDING_TOOLS: [&str; 5] = ["targo", "targo-trust", "trustd", "ty", "clean"];

/// Trust (DC-16a): the record, in a tools directory, of the `ay` that directory installs:
/// its SHA-256. The record's modification time is when that `ay` arrived there.
pub(crate) const INSTALLED_AY_RECORD: &str = "ay.installed.sha256";

/// Trust (DC-16a): installs the `ay` at `produced` as `<tools_dir>/<ay_name>`, the file
/// the sysroot's `bin/ay` is linked from, and returns that path.
///
/// What records a sysroot's `ay` (trust-cg-verify's build script, in the compiler and in
/// each tool of [`AY_RECORDING_TOOLS`]) re-records it only when Cargo finds the file's
/// modification time newer than its last run (`rerun-if-changed`). A file installed
/// with its own time (a hard link, or a copy that keeps its times, as `copy_link`
/// makes) can carry a time older than that run: a taken `ay` keeps the pack's time, and a
/// built one Cargo did not relink keeps its old link time. Then the compiler kept
/// recording the `ay` it found before while the sysroot held another. So the installed
/// `ay` is always this directory's own copy, never a link into a pack or Cargo's output,
/// and its time is the time its bytes arrived: when they differ from the record, now,
/// and otherwise the record's, so that switching back and forth never sets it back to a
/// time before a run that recorded other bytes.
///
/// When the bytes change, a tool restored from this directory that recorded the `ay` it
/// replaces is removed, from `tools_dir` and from `bindir`, so that no sysroot restores
/// a tool beside an `ay` it does not admit: `recorders` names each tool's file here and
/// its file names in `bindir`. A tool records an `ay` by its SHA-256, in hex. Without a
/// record, the `ay` before is unknown, and each tool that does not record this one is
/// removed. A command that does not build these tools then finds them missing, never
/// mismatched; `x.py build` builds them again.
///
/// `sealed`, when given, is the SHA-256 `produced` must have (a taken `ay`'s seal).
pub(crate) fn settle_installed_ay(
    produced: &Path,
    sealed: Option<&str>,
    tools_dir: &Path,
    bindir: &Path,
    ay_name: &str,
    recorders: &[(String, Vec<String>)],
) -> io::Result<PathBuf> {
    use sha2::Digest as _;
    let bytes = fs::read(produced)?;
    let sha256 = helpers::hex_encode(sha2::Sha256::digest(&bytes).as_slice());
    if let Some(sealed) = sealed
        && sealed != sha256
    {
        return Err(io::Error::other(format!(
            "it is {sha256}, not the {sealed} bootstrap took (it changed while it was taken)"
        )));
    }
    let record = tools_dir.join(INSTALLED_AY_RECORD);
    let before = match fs::read_to_string(&record) {
        Ok(text) => Some(text.trim().to_owned()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(error) => return Err(error),
    };
    if before.as_deref() != Some(sha256.as_str()) {
        for (tool, bins) in recorders {
            let path = tools_dir.join(tool);
            let held = match fs::read(&path) {
                Ok(held) => held,
                Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                Err(error) => return Err(error),
            };
            let stale = match &before {
                Some(before) => memchr::memmem::find(&held, before.as_bytes()).is_some(),
                None => memchr::memmem::find(&held, sha256.as_bytes()).is_none(),
            };
            if stale {
                for path in std::iter::once(path).chain(bins.iter().map(|bin| bindir.join(bin))) {
                    match fs::remove_file(&path) {
                        Err(error) if error.kind() != io::ErrorKind::NotFound => {
                            return Err(error);
                        }
                        _ => {}
                    }
                }
            }
        }
        // The record moves last: a run cut short before it removes again.
        let next = tools_dir.join(format!("{INSTALLED_AY_RECORD}.next"));
        fs::write(&next, format!("{sha256}\n"))?;
        fs::rename(&next, &record)?;
    }
    let arrived = fs::metadata(&record)?.modified()?;
    let installed = tools_dir.join(ay_name);
    let next = tools_dir.join(format!("{ay_name}.installing"));
    match fs::remove_file(&next) {
        Err(error) if error.kind() != io::ErrorKind::NotFound => return Err(error),
        _ => {}
    }
    fs::write(&next, &bytes)?;
    fs::set_permissions(&next, fs::metadata(produced)?.permissions())?;
    helpers::set_file_times(
        &next,
        fs::FileTimes::new().set_accessed(arrived).set_modified(arrived),
    )?;
    fs::rename(&next, &installed)?;
    Ok(installed)
}

// Trust: Sysroot may build compiler prerequisites, never a frontend bound to itself.
pub(crate) fn ensure_sysroot_verifier_prerequisites(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    sysroot: &Path,
) {
    ensure_verifier_tool_bins(builder, target_compiler, sysroot, false);
}

// Trust: dist's explicit component graph requests the completed compiler's
// whole verifier surface. Keep that entry separate from Sysroot prerequisites;
// its caller has already ensured compiler assembly before preparing the image.
pub(crate) fn ensure_default_verifier_tool_bins(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    sysroot: &Path,
) {
    ensure_verifier_tool_bins(builder, target_compiler, sysroot, true);
}

// Trust: final Targo records this compiler's held image and runtime closure.
// Construct all selected frontends only after compiler/runtime/std assembly and
// validation. Sysroot is then complete and cached before pairing requests it.
pub(crate) fn finish_verifier_tool_bins_after_assembly(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    sysroot: &Path,
) {
    if should_ensure_default_verifier_tool_bins(builder.kind, target_compiler.stage)
        && !is_partial_stage1_source_build(
            builder.kind,
            target_compiler.stage,
            builder.top_stage,
            builder.config.include_default_paths,
            &builder.paths,
        )
    {
        ensure_default_verifier_tool_bins(builder, target_compiler, sysroot);
    }
}

fn ensure_verifier_tool_bins(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    sysroot: &Path,
    compiler_assembled: bool,
) {
    let extended = builder.config.extended;
    let tools = builder.config.tools.as_ref();
    let ay_source_present = verifier_backend_source_present(&builder.src, AY_SOURCE_MANIFEST);
    if target_compiler.stage == 0
        || !default_verifier_tool_bins_enabled(extended, tools, ay_source_present)
    {
        return;
    }

    let target = target_compiler.host;
    let bindir = sysroot.join("bin");
    t!(fs::create_dir_all(&bindir));
    let install_bin = |builder: &Builder<'_>, tool_path: &Path, bin_name: &str| {
        builder.copy_link(
            tool_path,
            &bindir.join(exe(bin_name, target_compiler.host)),
            FileType::Executable,
        );
    };
    let solvers = default_source_solver_enabled(extended, tools, ay_source_present);

    // `ay` — the core solver — installs whenever its in-tree source is present.
    // Guarding on the manifest keeps a bare checkout (no first-party sources)
    // building instead of hard-failing when the block is reached via
    // `targo-trust`/`tools` without the `ay` source.
    //
    // Trust (2026-10-09): FIRST, before any battery that links trust-cg-verify.
    // Each of them records the bytes of THIS sysroot's `bin/ay` from its build
    // script (`name_tool_ay_record_host_sysroot`), and `Rustc::run` reaches this
    // function through `builder.sysroot(..)` before its own `ensure_sysroot_ay`,
    // so `targo-trust` and `trustd`, built here before `ay` until now (a pack-cut
    // probe's log, 2026-10-09: "Building stage1 targo", "targo-trust", "trustd",
    // then "ay"), would have found no `ay` to record.
    if solvers && ay_source_present {
        ensure_sysroot_ay(builder, target_compiler, sysroot);
    }

    // Trust: AY is a compiler prerequisite, while final Targo consumes the
    // completed compiler. Asking for that Targo while Sysroot is active closes
    // a dependency cycle (and cannot capture the not-yet-installed image).
    if !compiler_assembled {
        return;
    }
    // Keep the audited older-line intermediate Stage1 deferral. Every other
    // selected generation retains its complete surface after assembly, including
    // same-line Stage1 and a non-partial top-level Stage1 build.
    if solvers
        && ay_source_present
        && should_defer_intermediate_verifier_tool_bins(builder, target_compiler, env::vars_os())
    {
        return;
    }

    // Trust: selecting a final tool's build compiler can itself assemble a
    // prior compiler. It belongs to the completed phase too; AY owns its own
    // explicit prerequisite selection above.
    let build_compiler =
        get_tool_target_compiler(builder, ToolTargetBuildMode::Dist(target_compiler));

    // Reaching this point means at least one member of the verifier surface is
    // enabled. Install both frontend binaries as a unit: staging solver
    // batteries without the canonical `targo trust` entry point strands those
    // batteries in the sysroot, while staging only one half of the frontend
    // produces a present-but-unusable command.
    {
        builder.sess.require_submodule("src/tools/targo", None);
        let targo =
            builder.ensure(targo_tool_build_recipe(build_compiler, target_compiler, target));
        // Trust: with its `cargo` alias; no later pass installs it for the top stage.
        for bin_name in sysroot_bin_names_for_tool_source("targo") {
            install_bin(builder, &targo.tool_path, bin_name);
        }
    }
    {
        let targo_trust = builder.ensure(ToolBuild {
            build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "targo-trust",
            mode: Mode::ToolTarget,
            path: "targo-trust",
            source_type: SourceType::InTree,
            extra_features: targo_trust_in_process_features(),
            allow_features: CARGO_TRUST_ALLOW_FEATURES,
            cargo_args: locked_cargo_args(&[]),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_bin(builder, &targo_trust.tool_path, "targo-trust");

        // `targo trust` starts the coordination daemon on demand.  Keep the
        // daemon in the exact same sysroot as the frontend so a canonical
        // Stage-N toolchain never falls back to an ambient executable.
        let trustd = build_trustd_tool(builder, build_compiler, target_compiler, target);
        install_bin(builder, &trustd.tool_path, "trustd");
    }
    if solvers {
        // Trust: batteries-on default — build EVERY verification backend into
        // the sysroot, not just `ay`. The two L2 backends — `ty` (temporal
        // logic / TLA+) and `clean` (higher-order theorem prover) — are each
        // their own `first-party/` submodule, wired here so `targo trust
        // doctor` reports 6/6 backends out of the box (DESIGN_PHILOSOPHY.md
        // §2/§4 — all batteries on, in-tree capability). We select the single
        // backend binary with `--bin` so the sibling CLIs are not built, and we
        // allow `min_specialization,specialization` so dependency crates that
        // gate impls on those features (e.g. `ahash`'s `specialize` path, which
        // otherwise trips an E0119 blanket/specialized impl conflict) compile.
        // Trust: both TY and Clean also reach ay-sat's fallible allocations.
        let backend_allow_features = VERIFIER_BACKEND_ALLOW_FEATURES;
        // Trust (DC-16a): the same decision `ensure_sysroot_ay` took for this sysroot.
        let taken_ty = taken_stage2_verifier_tools(builder, target_compiler)
            .filter(|taken| taken.tool("ty").is_some());
        if let Some(taken) = &taken_ty {
            let ty = install_taken_verifier_tool(builder, taken, "ty", target_compiler);
            install_bin(builder, &ty, "ty");
        } else if l2_backend_enabled(tools, "ty")
            && verifier_backend_source_present(&builder.src, TY_SOURCE_MANIFEST)
        {
            let ty = builder.ensure(ToolBuild {
                build_compiler,
                output_compiler: target_compiler,
                target,
                tool: "ty",
                mode: Mode::ToolTarget,
                path: "first-party/ty/crates/tla-cli",
                source_type: SourceType::InTree,
                extra_features: Vec::new(),
                allow_features: backend_allow_features,
                cargo_args: locked_cargo_args(&["--bin", "ty"]),
                artifact_kind: ToolArtifactKind::Binary,
            });
            install_bin(builder, &ty.tool_path, "ty");
        }

        if l2_backend_enabled(tools, "clean")
            && verifier_backend_source_present(&builder.src, CLEAN_SOURCE_MANIFEST)
        {
            // Trust: exactly ONE clean feature is enabled here: `carcara-verify`.
            //
            // Why it is on. A `clean` built without it answers EVERY Alethe
            // certificate with "carcara-verify feature required for tier 1
            // verification", whatever the proof says (measured 2026-09-14/15 on
            // trust-stage1-r2/bin/clean and on the aterm trust pack 8590/8595
            // `bin/clean`; the aterm-packaged clean 8606, built with the feature,
            // verifies the same control proof and rejects a one-premise mutant of
            // it). trust-cg's certificate lane capability-probes its checker and
            // treats such a build as NO checker, so a sysroot shipping it carries
            // no independent Alethe authority. clean's own workspace `build-args`
            // (first-party/clean/Cargo.toml) already request
            // `clean/carcara-verify`; this makes the sysroot build match them.
            //
            // Who consumes it. trust-cg-verify's default discovery tries the
            // aterm-packaged `store/clean/current/bin/clean` first
            // (aterm_toolchain.rs) and falls back to THIS binary -- the `clean`
            // in the running compiler's `<sysroot>/bin` -- only when that package
            // is absent or fails the control-proof probe
            // (`default_clean_checker_candidates`, obligation_cert_store.rs);
            // `TCG_EXTERNAL_CLEAN_CHECKER` (legacy `TCG_CLEAN_CHECKER`) can also
            // name it explicitly. Either way it is re-probed and bound by its
            // SHA-256 before any proof is credited.
            //
            // What it costs. The closure clean -> clean-cli -> clean-elab ->
            // clean-auto -> carcara (a path dependency on clean's audited vendored
            // copy, first-party/clean/third-party/carcara, with its path sibling
            // carcara-macros) adds five crates.io crates: az 1.3.0, libm 0.2.16,
            // rug 1.30.0, gmp-mpfr-sys 1.7.1 and nom 8.0.0. All five are already
            // in first-party/clean/Cargo.lock, so `--locked` still resolves, but a
            // box that has never fetched them must reach crates.io once; carcara
            // itself comes from the clean checkout and needs no fetch.
            // gmp-mpfr-sys builds GMP from bundled C source (m4, make and cc
            // required; it runs GMP's C test suite and caches the result in the
            // user cache directory), a one-time multi-minute cost, and the binary
            // grows by roughly 8 MB. A `vendor = true` bootstrap (which passes
            // `--frozen`) fails here on any box that has not already cached those
            // five crates: `default_paths_to_vendor` (vendor.rs) does not list
            // first-party/clean's workspace, and `vendor/` does not contain them.
            //
            // Why `trust-ir-backend` stays off. The Lean->TrustIr leg (`clean
            // compile --emit trustir`, and the `--emit obj` handoff to trust-cg)
            // lives behind clean's `trust-ir-backend` feature, whose closure
            // reaches the trust-ir and trust-cg siblings. Turning it on is not a
            // one-line change here — it needs `first-party/clean`'s own lockfile
            // to describe that closure at the currently pinned sibling revisions,
            // and `--locked` is not negotiable for a reproducible, credential-free
            // bootstrap.
            let clean = builder.ensure(ToolBuild {
                build_compiler,
                output_compiler: target_compiler,
                target,
                tool: "clean",
                mode: Mode::ToolTarget,
                path: "first-party/clean/crates/clean",
                source_type: SourceType::InTree,
                extra_features: vec!["carcara-verify".to_string()],
                allow_features: backend_allow_features,
                cargo_args: locked_cargo_args(&["--bin", "clean"]),
                artifact_kind: ToolArtifactKind::Binary,
            });
            install_bin(builder, &clean.tool_path, "clean");
        }
    }
}

/// Whether an L2 standalone backend binary (`ty`, `clean`) belongs in this
/// sysroot.
///
/// These are batteries, not optional user tools, so — like `ay` — they ignore
/// `extended` and install whenever their in-tree source is present. What they
/// do respect is the `[build] tools` allowlist: a build that must leave one
/// out (a sibling tree mid-sync, a deliberately minimal distribution) says so
/// in a committed, reviewable file. Removing the sole trust root's checker from
/// a sysroot is a decision that has to survive review, which ambient process
/// state cannot express.
fn l2_backend_enabled(tools: Option<&std::collections::HashSet<String>>, backend: &str) -> bool {
    match tools {
        Some(set) => set.iter().any(|entry| tool_config_entry_selects_user_tool(entry, backend)),
        None => true,
    }
}

fn restored_sysroot_bins_for_config(
    config: &Config,
    unstable_features: bool,
) -> Vec<(&'static str, &'static str)> {
    let ay_source_present = verifier_backend_source_present(&config.src, AY_SOURCE_MANIFEST);
    restored_sysroot_bins_for_tool_settings(
        config.extended,
        config.tools.as_ref(),
        unstable_features,
        ay_source_present,
    )
}

// Trust: local sysroots support both the canonical documentation command and
// rustup's compatibility entry point. Cold assembly and restoration must agree
// with the standalone Rustdoc step; distribution owns its separate name policy.
const LOCAL_RUSTDOC_BIN_NAMES: &[&str] = &["trustdoc", "rustdoc"];

// Trust: repository qualification shares the installed public tool names.
pub(crate) fn restored_sysroot_bins_for_tool_settings(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
    unstable_features: bool,
    ay_source_present: bool,
) -> Vec<(&'static str, &'static str)> {
    let mut bins = Vec::new();

    if tool_enabled_for_tool_settings(extended, tools, "trustdoc") {
        bins.extend(LOCAL_RUSTDOC_BIN_NAMES.iter().map(|&name| ("rustdoc_tool_binary", name)));
    }

    // The public frontend is one unit. Any enabled verifier-surface member
    // restores both halves (and the daemon used by `targo trust`) so a
    // batteries-on sysroot always has a usable entry point. The frontend's
    // source is the `targo` artifact (`targo_tool_build_recipe`), never a file
    // named `cargo`.
    if default_verifier_tool_bins_enabled(extended, tools, ay_source_present) {
        bins.push(("targo", "targo"));
        bins.push(("targo-trust", "targo-trust"));
        bins.push(("trustd", "trustd"));
    }
    if default_source_solver_enabled(extended, tools, ay_source_present) {
        // The copy loop that consumes this list guards each entry on the built
        // binary's existence, so listing `ay`/`ty`/`clean` here is safe even
        // when a particular backend's source was absent at build time.
        bins.push(("ay", "ay"));
        // Trust: batteries-on default — the L2 backends `ty` + `clean` ship
        // alongside `ay`. Gated on the same committed `[build] tools`
        // allowlist that decides whether they were built at all, so what a
        // sysroot contains is a function of the checked-in configuration
        // alone (see `l2_backend_enabled`).
        if l2_backend_enabled(tools, "ty") {
            bins.push(("ty", "ty"));
        }
        if l2_backend_enabled(tools, "clean") {
            bins.push(("clean", "clean"));
        }
    }
    // Trust: tool-settings call sites here pass the upstream cargo
    // source-binary name as `tool_name`, because `tool_matches_config_entry`
    // matches Trust-canonical config aliases (LHS) against upstream tool
    // names (RHS). The first element of each `bins.push((<src>, <dst>))`
    // tuple is the upstream cargo source-binary name (must stay upstream —
    // that's what cargo's `--bin` selector consumes); the second element is
    // the Trust-canonical install name.
    if extended_rustc_tool_is_default_step_for_tool_settings(
        extended,
        tools,
        unstable_features,
        "cargo-clippy",
        true,
    ) {
        bins.push(("cargo-clippy", "tippy"));
        bins.push(("cargo-clippy", "targo-tippy"));
    }
    if extended_rustc_tool_is_default_step_for_tool_settings(
        extended,
        tools,
        unstable_features,
        "clippy-driver",
        true,
    ) {
        bins.push(("clippy-driver", "tippy-driver"));
    }
    if extended_rustc_tool_is_default_step_for_tool_settings(
        extended,
        tools,
        unstable_features,
        "cargo-fmt",
        true,
    ) {
        bins.push(("cargo-fmt", "targo-fmt"));
    }
    if extended_rustc_tool_is_default_step_for_tool_settings(
        extended,
        tools,
        unstable_features,
        "rustfmt",
        true,
    ) {
        bins.push(("rustfmt", "trustfmt"));
    }
    if tool_enabled_for_tool_settings(extended, tools, "trustup") {
        // Trust: same name on both sides — `trustup` has no upstream spelling
        // to be compatible with, which is the point of it.
        bins.push(("trustup", "trustup"));
    }
    if tool_enabled_for_tool_settings(extended, tools, "trust-analyzer") {
        bins.push(("rust-analyzer", "trust-analyzer"));
    }
    if extended_rustc_tool_is_default_step_for_tool_settings(
        extended,
        tools,
        unstable_features,
        "cargo-miri",
        false,
    ) {
        bins.push(("cargo-miri", "targo-miri"));
    }
    if extended_rustc_tool_is_default_step_for_tool_settings(
        extended,
        tools,
        unstable_features,
        "miri",
        false,
    ) {
        bins.push(("miri", "trust-miri"));
    }

    bins
}

pub(crate) fn upstream_compat_bin_for_tool_source(src_name: &str) -> Option<&str> {
    // Trust: the generic compatibility alias emitted here is `cargo`: `cargo
    // +trust` must resolve, and for a linked toolchain without `bin/cargo`
    // rustup's proxy falls back to ANOTHER toolchain's (stock) Cargo. It is a
    // copy of the `targo` artifact and nothing else — the Trust Cargo's
    // package, library and binary are all `targo`, so a file in a tools
    // directory that is merely NAMED `cargo` (a stale build from before the
    // rename, say) can never be installed under either name.
    // (The matching `rustc` name is materialized on a separate path:
    // `materialize_local_compiler_aliases` / `Assemble`, and `rustdoc` through
    // the explicit local documentation bin list and the Rustdoc step's
    // `bin_rustdoc` closure.) Every other stock secondary name — cargo-trust,
    // cargo-clippy, clippy-driver, cargo-fmt, rustfmt, rust-analyzer,
    // cargo-miri, miri — is intentionally NOT materialized. This stops those
    // names at the source (the root-cause replacement for the former
    // scripts/purge-stock-names.sh, which deleted them post-build).
    match src_name {
        "targo" => Some("cargo"),
        _ => None,
    }
}

/// Trust: the file names one built tool is installed under in a sysroot `bin/`:
/// its own name, then its upstream-compatible alias when it has one (`cargo`
/// for `targo`). Every step that installs a built `targo` into a sysroot
/// installs all of these from the one artifact, in the one place.
///
/// The alias used to be left to sysroot restoration
/// (`restore_user_facing_tools`, compile.rs), which copies what already sits in
/// the stage's tools directory. That was enough while restoration built the
/// frontend first. Since 0b37a090af (2026-11-10) the frontend is built after
/// the compiler is assembled: for the top stage, restoration had already run
/// and found no `targo`, the later install wrote `bin/targo` alone, and nothing
/// restored again. `x.py build --stage 2` at 7cbb5e4327 left `stage2/bin` with
/// `targo` and no `cargo` (aarch64 Linux, 2026-11-10; stage1 kept its alias only
/// because `StdLink` restores a stage1 sysroot once more), and
/// `scripts/seed_staircase.py admit` refused that stage2 as a stage0.
pub(crate) fn sysroot_bin_names_for_tool_source(src_name: &str) -> Vec<&str> {
    let mut names = vec![src_name];
    names.extend(upstream_compat_bin_for_tool_source(src_name));
    names
}

pub(crate) fn restore_rust_analyzer_proc_macro_srv(builder: &Builder<'_>) -> bool {
    restore_rust_analyzer_proc_macro_srv_for_config(&builder.config)
}

/// Remove the retired stock proc-macro-server surface if any path entry names
/// it. `Path::exists` is insufficient here because it follows symlinks and
/// reports a dangling forbidden alias as absent. Only a genuine `NotFound` is
/// benign; permission and I/O failures must stop sysroot assembly.
pub(crate) fn remove_retired_proc_macro_srv_alias(path: &Path) -> io::Result<()> {
    match fs::symlink_metadata(path) {
        Ok(_) => fs::remove_file(path),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

// Tippy's package has two binaries with deliberately different feature
// recipes. Always select the requested binary: building the package default
// compiles both, then the second bootstrap step recompiles the driver (and can
// do so with a different jemalloc feature set).
const CARGO_CLIPPY_CARGO_ARGS: &[&str] = &["--bin", "cargo-clippy"];
const CLIPPY_DRIVER_CARGO_ARGS: &[&str] = &["--bin", "clippy-driver"];

// Trust: this package also has development-only format-diff/git helpers.
// Each public formatter step owns one binary; keep its library/features shared.
const CARGOFMT_CARGO_ARGS: &[&str] = &["--bin", "cargo-fmt"];
const RUSTFMT_CARGO_ARGS: &[&str] = &["--bin", "rustfmt"];

pub(crate) fn ensure_user_facing_tools(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    sysroot: &Path,
) {
    // Only a local `x build` promises a batteries-on, directly runnable
    // sysroot. Distribution and installation steps own explicit component
    // dependency graphs and must not assemble every configured tool here: in
    // particular, doing so built Tippy once as an unrelated stage3 sysroot
    // side effect and then again as the requested stage2 dist component. The
    // redundant stage3 build could observe an uplifted/partially assembled
    // sysroot and fail in rustc_tools_util with E0463 before the real Tippy
    // component was reached. Tests likewise own the packages they exercise.
    if !should_assemble_user_facing_tools(builder.kind, target_compiler.stage) {
        return;
    }

    let target = target_compiler.host;
    // ONE producer per installed tool. Each rustc-private tool of this sysroot
    // is the standalone step's own (`Rustdoc`, `CargoClippy`, `Clippy`, ...):
    // built by the stage N-1 compiler and linked against this sysroot's
    // compiler libraries (`RustcPrivateCompilers::from_target_compiler`), the
    // tool `x.py dist` ships and a full `x build` runs as a default step.
    // Until 2026-10-14 this function built its own copy of each with the
    // stage N compiler, into another cargo directory, and both copies were
    // installed at the same `bin/<name>`: the last step to run decided the
    // bytes (they differed in the N_OSO paths that name the cargo directory).
    // A `build compiler/rustc library/std` then left other tools in the
    // sysroot than a full build did or the dist archives shipped: the seed
    // mint's double compile compared one copy, the pack would have carried
    // the other, and its `verify-stage2-unchanged` refused the cut
    // (`scripts/mint_and_prove_seed.sh`, D7 of the first mint).
    let compilers = RustcPrivateCompilers::from_target_compiler(builder, target_compiler);
    let bindir = sysroot.join("bin");
    t!(fs::create_dir_all(&bindir));

    let install_bins = |builder: &Builder<'_>, tool_path: &Path, bin_names: &[&str]| {
        for bin_name in bin_names {
            builder.copy_link(
                tool_path,
                &bindir.join(exe(bin_name, target_compiler.host)),
                FileType::Executable,
            );
        }
    };

    if tool_enabled_for_tool_settings(
        builder.config.extended,
        builder.config.tools.as_ref(),
        "trustdoc",
    ) {
        builder.ensure(Rustdoc { target_compiler });
    }

    if targo_runtime_enabled(builder.config.extended, builder.config.tools.as_ref()) {
        builder.sess.require_submodule("src/tools/targo", None);
        let targo = builder.ensure(targo_tool_build_recipe(
            get_tool_target_compiler(builder, ToolTargetBuildMode::Dist(target_compiler)),
            target_compiler,
            target,
        ));
        // Trust: with its `cargo` alias (`sysroot_bin_names_for_tool_source`).
        install_bins(builder, &targo.tool_path, &sysroot_bin_names_for_tool_source("targo"));
    }
    if tool_enabled_for_tool_settings(
        builder.config.extended,
        builder.config.tools.as_ref(),
        "targo-trust",
    ) {
        let targo_trust = builder.ensure(ToolBuild {
            build_compiler: get_tool_target_compiler(
                builder,
                ToolTargetBuildMode::Dist(target_compiler),
            ),
            output_compiler: target_compiler,
            target,
            tool: "targo-trust",
            mode: Mode::ToolTarget,
            path: "targo-trust",
            source_type: SourceType::InTree,
            extra_features: targo_trust_in_process_features(),
            allow_features: CARGO_TRUST_ALLOW_FEATURES,
            cargo_args: locked_cargo_args(&[]),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_bins(builder, &targo_trust.tool_path, &["targo-trust"]);

        let trustd = build_trustd_tool(
            builder,
            get_tool_target_compiler(builder, ToolTargetBuildMode::Dist(target_compiler)),
            target_compiler,
            target,
        );
        install_bins(builder, &trustd.tool_path, &["trustd"]);
    }
    if tool_enabled_for_tool_settings(
        builder.config.extended,
        builder.config.tools.as_ref(),
        "trustup",
    ) {
        // Trust: `trustup` is the Trust-native toolchain selector — the
        // replacement for rustup, which this project does not depend on. It is
        // std-only and in-tree, so it builds exactly like the other
        // `Mode::ToolTarget` frontends and installs under its own name only.
        // Wiring it in is not adopting it: nothing here makes it the default
        // selector, and no existing selection path consults it.
        let trustup = builder.ensure(trustup_tool_build_recipe(
            get_tool_target_compiler(builder, ToolTargetBuildMode::Dist(target_compiler)),
            target_compiler,
            target,
        ));
        install_bins(builder, &trustup.tool_path, &["trustup"]);
    }
    if extended_rustc_tool_is_default_step(builder, "cargo-clippy", true) {
        builder.ensure(CargoClippy::from_compilers(compilers));
    }
    if extended_rustc_tool_is_default_step(builder, "clippy-driver", true) {
        builder.ensure(Clippy::from_compilers(compilers));
    }
    if extended_rustc_tool_is_default_step(builder, "cargo-fmt", true) {
        builder.ensure(Cargofmt::from_compilers(compilers));
    }
    if extended_rustc_tool_is_default_step(builder, "rustfmt", true) {
        builder.ensure(Rustfmt::from_compilers(compilers));
    }
    if tool_enabled_for_tool_settings(
        builder.config.extended,
        builder.config.tools.as_ref(),
        "trust-analyzer",
    ) {
        builder.ensure(RustAnalyzer::from_compilers(compilers));
    }
    if restore_rust_analyzer_proc_macro_srv(builder) {
        builder.ensure(RustAnalyzerProcMacroSrv::from_compilers(compilers));
    }
    if extended_rustc_tool_is_default_step(builder, "miri", false) {
        builder.ensure(Miri::from_compilers(compilers));
    }
    if extended_rustc_tool_is_default_step(builder, "cargo-miri", false) {
        builder.ensure(CargoMiri::from_compilers(compilers));
    }

    // Enforce the Trust-only public libexec surface at the very end of local
    // user-facing tool assembly. A later stage/copy step may have recreated the
    // retired stock alias; the helper also removes a dangling symlink, which
    // `Path::exists` would miss even though the doctor gate still observes it.
    let stock_proc_macro_srv =
        sysroot.join("libexec").join(exe("rust-analyzer-proc-macro-srv", target_compiler.host));
    t!(remove_retired_proc_macro_srv_alias(&stock_proc_macro_srv));
}

pub(crate) fn should_restore_user_facing_tools(compiler_stage: u32) -> bool {
    compiler_stage > 0
}

pub(crate) fn should_ensure_default_verifier_tool_bins(kind: Kind, compiler_stage: u32) -> bool {
    compiler_stage > 0 && kind == Kind::Build
}

// Trust: only the audited internal Stage1 of a native, LLVM-default Stage2
// build is eligible. Unknown configuration keeps the existing batteries-on
// graph. This is scheduling, never permission to change compiler verification.
fn should_defer_intermediate_verifier_tool_bins(
    builder: &Builder<'_>,
    compiler: Compiler,
    ambient: impl IntoIterator<Item = (OsString, OsString)>,
) -> bool {
    !builder.config.local_rebuild && verifier_tool_scheduling_known(builder, compiler, 1, ambient)
}

// Trust: the configurations whose verifier-tool scheduling is audited: a native
// `x.py build --stage 2` (top stage 2) in the announced bootstrap posture, asked of
// its `stage` compiler. The intermediate rule asks it of stage 1, the stage-2 source
// rule (`stage2_verifier_tools`, DC-16a) of stage 2. Anything else is unknown.
fn verifier_tool_scheduling_known(
    builder: &Builder<'_>,
    compiler: Compiler,
    stage: u32,
    ambient: impl IntoIterator<Item = (OsString, OsString)>,
) -> bool {
    use crate::core::backend::CodegenBackendKind::{Llvm, TrustCg};
    let config = &builder.config;
    let native = helpers::get_host_target();
    if builder.kind != Kind::Build
        || builder.top_stage != 2
        || compiler.stage != stage
        || compiler.host != native
        || config.host_target != native
        || config.hosts != [native]
        || !intermediate_tool_std_targets_known(builder, native)
        || config.full_bootstrap
        || config.download_rustc()
        || !config.keep_stage.is_empty()
        || !config.keep_stage_std.is_empty()
        || config.external_rustc.is_some()
        || config.external_cargo.is_some()
        || config.external_rustdoc.is_some()
        || !config.tool.is_empty()
        || !config.free_args.is_empty()
        || !config.skip.is_empty()
        || !config.rust_rustflags.is_empty()
        || config.target_config.values().any(|target| !target.rustflags.is_empty())
        || !matches!(config.enabled_codegen_backends(native), [Llvm] | [Llvm, TrustCg])
        || builder
            .paths
            .iter()
            .any(|path| path != Path::new("compiler/rustc") && path != Path::new("library/std"))
    {
        return false;
    }
    let ambient: Vec<_> = ambient.into_iter().collect();
    // Require the existing announced native bootstrap posture. Neither an
    // arbitrary flag string nor a per-library verification request qualifies.
    if !ambient.iter().any(|(key, value)| {
        (key == "RUSTFLAGS_BOOTSTRAP" && value == "-Ztrust-verify=off")
            || (key == "TRUST_NO_VERIFY" && value == "1")
    }) || ambient.iter().any(|(key, value)| intermediate_tool_ambient_override(key, value))
    {
        return false;
    }
    let cargo_home = ambient
        .iter()
        .find(|(key, _)| key == "CARGO_HOME")
        .map(|(_, value)| PathBuf::from(value))
        .or_else(|| {
            ambient
                .iter()
                .find(|(key, _)| key == "HOME")
                .map(|(_, value)| PathBuf::from(value).join(".cargo"))
        });
    cargo_home.is_some_and(|home| intermediate_tool_cargo_configuration_known(&config.src, &home))
}

// Trust: the compiler still has one native host. The canonical Apple SDK adds
// only the other builtin Apple architecture's std; neither target uses a verifier
// CLI under the already-required, announced LLVM bootstrap policy. Keep unknown
// target specifications/backends on the eager graph, and retain every final tool.
fn intermediate_tool_std_targets_known(builder: &Builder<'_>, native: TargetSelection) -> bool {
    use crate::core::backend::CodegenBackendKind::{Llvm, TrustCg};
    let config = &builder.config;
    if config.targets == [native] {
        return true;
    }
    config.targets.len() == 2
        && config.targets.contains(&native)
        && native.file.is_none()
        && !native.synthetic
        && matches!(&*native.triple, "aarch64-apple-darwin" | "x86_64-apple-darwin")
        && config.targets.iter().all(|target| {
            target.file.is_none()
                && !target.synthetic
                && matches!(&*target.triple, "aarch64-apple-darwin" | "x86_64-apple-darwin")
                && matches!(config.enabled_codegen_backends(*target), [Llvm] | [Llvm, TrustCg])
        })
        && config.targets[0] != config.targets[1]
}

// Trust: accept only the preexisting native transport and scheduling/diagnostic
// state; do not parse arbitrary flags or infer an effective backend from TOML
// while inherited flags, wrappers or untracked verifier controls can override it.
fn intermediate_tool_ambient_override(key: &OsStr, value: &OsStr) -> bool {
    let Some(key) = key.to_str() else {
        return true;
    };
    match key {
        "RUSTFLAGS_BOOTSTRAP" => value != "-Ztrust-verify=off",
        "TRUST_NO_VERIFY"
        | "RUSTC_BOOTSTRAP"
        | "TRUST_VANILLA_ANNOUNCED"
        | "TRUST_BOOTSTRAP_OFFLINE_CLOSURE" => value != "1",
        "TRUST_BUILD_LOCK_TOKEN" | "TRUST_BUILD_LOCK_WAIT" | "TRUST_REPO" => false,
        // Trust: Bootstrap hands each word of these to every Cargo it runs
        // (`builder/cargo.rs`), where `--config` or `-Z` can add `[env]` entries,
        // wrappers or flags that the configuration-file check never reads. Only the
        // lockfile and network switches leave the audited posture as it is.
        "CARGOFLAGS" | "CARGOFLAGS_BOOTSTRAP" | "CARGOFLAGS_NOT_BOOTSTRAP" => {
            value.to_str().is_none_or(|flags| {
                flags
                    .split_whitespace()
                    .any(|flag| !matches!(flag, "--offline" | "--locked" | "--frozen"))
            })
        }
        _ => {
            key.contains("RUSTFLAGS")
                || key.contains("RUSTDOCFLAGS")
                || key.contains("CODEGEN_BACKEND")
                || key.starts_with("CARGO_UNSTABLE_")
                || key.starts_with("RUSTC")
                || (key.starts_with("CARGO_") && key.contains("RUSTC"))
                || key.starts_with("TRUST_")
                || key == "TRUSTFLAGS"
                || key.starts_with("TCG_")
                || key.starts_with("TOOLCHAIN_AY_")
                || key.starts_with("AY_")
                || key.starts_with("CLEAN_")
                || key.starts_with("LEAN_")
                || key.starts_with("TY_")
        }
    }
}

// Trust: Cargo can inject wrappers or flags from files as well as env. Match
// the recreator's empty-home/no-ancestor-config posture. At the source root,
// accept only the current non-compiler jobs/net settings and a string target-dir.
// Bootstrap overrides target-dir through CARGO_TARGET_DIR for every tool build;
// it cannot change the selected compiler or verification policy. An `[env]`
// table can (a `TRUST_*` or `RUSTC*` variable reaches every rustc Cargo runs), so
// it is accepted only when it names `RUST_MIN_STACK` alone, with a decimal value,
// plain or as `{ value, force = false }`. That sizes the compiler's, codegen's and
// spawned threads' stacks and selects no compiler, flag or verifier control; the
// ambient check above already admits it, and without `force` an ambient value
// still wins. (`CARGOFLAGS` can carry `[env]` too; the ambient check handles it.)
// Unknown tables,
// legacy config, malformed/unreadable files and dangling links keep the old graph.
fn intermediate_tool_cargo_configuration_known(src: &Path, cargo_home: &Path) -> bool {
    let absent = |path: &Path| matches!(fs::symlink_metadata(path), Err(error) if error.kind() == io::ErrorKind::NotFound);
    if !cargo_home.is_absolute()
        || [cargo_home.join("config"), cargo_home.join("config.toml")]
            .iter()
            .any(|path| !absent(path))
        || src.ancestors().skip(1).any(|parent| {
            ["config", "config.toml"].iter().any(|name| !absent(&parent.join(".cargo").join(name)))
        })
        || !absent(&src.join(".cargo/config"))
    {
        return false;
    }
    let path = src.join(".cargo/config.toml");
    if absent(&path) {
        return true;
    }
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    let Ok(document) = text.parse::<toml::Value>() else {
        return false;
    };
    document.as_table().is_some_and(|table| {
        table.iter().all(|(key, value)| match key.as_str() {
            "net" => value.is_table(),
            "build" => value.as_table().is_some_and(|build| {
                build.iter().all(|(key, value)| match key.as_str() {
                    "jobs" => true,
                    "target-dir" => value.is_str(),
                    _ => false,
                })
            }),
            "env" => value.as_table().is_some_and(|env| {
                let decimal = |value: &toml::Value| {
                    value.as_str().is_some_and(|text| {
                        !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit())
                    })
                };
                env.len() == 1
                    && env.iter().all(|(key, value)| {
                        key == "RUST_MIN_STACK"
                            && (decimal(value)
                                || value.as_table().is_some_and(|entry| {
                                    entry.get("value").is_some_and(decimal)
                                        && entry.iter().all(|(key, value)| match key.as_str() {
                                            "value" => true,
                                            "force" => value.as_bool() == Some(false),
                                            _ => false,
                                        })
                                }))
                    })
            }),
            _ => false,
        })
    })
}

/// Trust (DC-16a): what a native `x.py build --stage 2` does with the verifier
/// batteries the toolchain it is built from already carries.
///
/// A stage-2 tool is compiled by the stage-1 compiler, which changes with every
/// compiler change, so cargo rebuilt every battery on every such change although a
/// battery's own sources had not moved: 1 h 34 min of a seeded stage 2 (Trust
/// docs/STATUS.md, Costs). Here a battery whose inputs are proven equal is installed
/// from the source toolchain instead ([`Stage2VerifierTools::Taken`]):
///
/// * The source toolchain is the installed atpkg `trust` pack, the one
///   `scripts/recreate_bootstrap.py`'s `atpkg_trust_sysroot` selects
///   ([`installed_trust_pack`]). The seed `src/stage0` pins carries no battery.
/// * Its record is the pack's `PROVENANCE` seal ([`SourceToolchainRecord`]): a
///   `BUILD-STAMPED-CLEAN` build of `reported_commit`, and the SHA-256 of each
///   `bin/` file as that build sealed it. A file that differs from its seal (a pack
///   whose batteries were replaced in place after the cut) was not built from that
///   commit, and nothing is taken.
/// * The inputs of `ay` and `ty` are their `first-party/` pins with the worktree's
///   departures under them ([`trust_source_identity::inputs_unchanged_since`]), and
///   every source Cargo can read for them stays inside the pin
///   ([`trust_source_identity::component_sources_closed`]).
/// * A battery whose build records this build's compiler is always built:
///   `targo` (bound to the completed compiler's image by `paired_compiler::bind`),
///   `targo-trust` (its oracle compiler is `CFG_VER_HASH`, `tool_identity.rs`),
///   `trustd` (`targo trust self-verify` requires its commit to be `trustc`'s) and
///   `clean` (clean-elab's `oracle_compiler` admits only the `trustc` of
///   `CFG_VER_HASH`). Each of them carries its commit as a bare string; a taken
///   battery may not ([`records_its_compiler`]).
/// * The set is taken whole or built whole. `ty` links trust-cg-verify, whose build
///   script recorded the `ay` beside it (`name_tool_ay_record_host_sysroot`), so `ty`
///   is taken only with the very `ay` its bytes record, and that `ay` is installed
///   first, before the stage-2 compiler records it in turn. The installed `ay` arrives
///   with a new time whenever its bytes change, so that what recorded the one before
///   records it again, and a restored tool that recorded the one before is removed
///   ([`settle_installed_ay`]).
/// * A battery's answers depend on which of its own checks it compiles: the build must
///   compile the batteries with debug assertions as the source toolchain's cut did
///   ([`source_toolchain_tools_debug_assertions`]).
///
/// Everything else builds: `x.py dist`, `install` and every other command (a pack
/// cut's double compile compares the tools the compilers it ships compiled), a
/// configuration [`verifier_tool_scheduling_known`] does not recognise, a pack that
/// cannot be read, a source commit this repository does not hold, an input that moved,
/// and any doubt. What is accepted: a taken battery was compiled by another compiler
/// and recipe, so a miscompilation of a battery by this tree's compiler or recipe is
/// found at dist and the pack cut, not in a dev stage 2 (docs/DECISION_QUEUE.md,
/// DC-16a).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Stage2VerifierTools {
    /// Every battery is built; why none is taken.
    Built(String),
    Taken(TakenVerifierTools),
}

/// The batteries a stage-2 build installs from its source toolchain, `ay` first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TakenVerifierTools {
    pub(crate) source: PathBuf,
    pub(crate) commit: String,
    pub(crate) tools: Vec<TakenVerifierTool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TakenVerifierTool {
    pub(crate) name: &'static str,
    /// The file in the source toolchain.
    pub(crate) path: PathBuf,
    /// Its SHA-256, which is also what its seal records.
    pub(crate) sha256: String,
}

impl TakenVerifierTools {
    fn tool(&self, name: &str) -> Option<&TakenVerifierTool> {
        self.tools.iter().find(|tool| tool.name == name)
    }
}

/// The batteries a stage-2 build may take: the independent solver repositories
/// whose builds do not record this build's compiler. `ay` comes first.
const STAGE2_TAKEABLE_VERIFIER_TOOLS: [(&str, trust_source_identity::IndependentToolComponent); 2] = [
    ("ay", trust_source_identity::IndependentToolComponent::Ay),
    ("ty", trust_source_identity::IndependentToolComponent::Ty),
];

/// What the source toolchain's seal says ([`Stage2VerifierTools`]).
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SourceToolchainRecord {
    pub(crate) commit: String,
    /// The sealed SHA-256 of each `bin/<name>` the record names.
    pub(crate) bins: std::collections::BTreeMap<String, String>,
}

/// The seal a pack carries at its root (`scripts/promote-toolchain.sh`).
pub(crate) const SOURCE_TOOLCHAIN_RECORD: &str = "PROVENANCE";

/// Reads a pack's [`SOURCE_TOOLCHAIN_RECORD`]: `key=value` lines, `#` comments. It must
/// say `provenance_class=BUILD-STAMPED-CLEAN` (the build tree was clean at the commit
/// when the build started and unchanged when it finished) and name one full
/// `reported_commit`; any `sealtime_repo_tree` and `build_stamp:tree_state` say
/// `clean`. Each `artifact_bin_<name>_sha256` is one sealed file. A key given twice,
/// or a value of another shape, refuses the record.
pub(crate) fn parse_source_toolchain_record(text: &str) -> Result<SourceToolchainRecord, String> {
    let mut fields = std::collections::BTreeMap::new();
    for line in text.lines() {
        let line = line.trim_end_matches('\r');
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            return Err(format!("{SOURCE_TOOLCHAIN_RECORD} line without `=`: {line:?}"));
        };
        if fields.insert(key, value).is_some() {
            return Err(format!("{SOURCE_TOOLCHAIN_RECORD} names `{key}` twice"));
        }
    }
    let hex = |value: &str, len: usize| {
        value.len() == len && value.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
    };
    if fields.get("provenance_class") != Some(&"BUILD-STAMPED-CLEAN") {
        return Err(format!(
            "the toolchain is not BUILD-STAMPED-CLEAN (provenance_class={:?})",
            fields.get("provenance_class")
        ));
    }
    for key in ["sealtime_repo_tree", "build_stamp:tree_state"] {
        if fields.get(key).is_some_and(|value| *value != "clean") {
            return Err(format!("{SOURCE_TOOLCHAIN_RECORD} says {key}={}", fields[key]));
        }
    }
    let commit = match fields.get("reported_commit") {
        Some(&commit) if hex(commit, 40) || hex(commit, 64) => commit.to_owned(),
        other => return Err(format!("no full reported_commit: {other:?}")),
    };
    let mut bins = std::collections::BTreeMap::new();
    for (key, value) in &fields {
        if let Some(name) =
            key.strip_prefix("artifact_bin_").and_then(|k| k.strip_suffix("_sha256"))
        {
            if !hex(*value, 64) {
                return Err(format!("{key} is no SHA-256: {value:?}"));
            }
            bins.insert(name.to_owned(), (*value).to_owned());
        }
    }
    Ok(SourceToolchainRecord { commit, bins })
}

/// The installed atpkg `trust` pack: `store/trust/current` under atpkg's per-user prefix
/// (`home` is `$HOME`) is a symlink to a numbered pack directly in `store/trust`, whose
/// `toolchain` is no symlink. atpkg keeps a pack's files in `<N>.noindex`, out of
/// Spotlight, and links `<N>` to it, so the directory `current` resolves to is `<N>` or
/// `<N>.noindex`. (`scripts/recreate_bootstrap.py`'s `_capture_atpkg_pack` reads the
/// same link but admits only `<N>`.) Never `PATH` or `ATPKG_BIN`.
pub(crate) fn installed_trust_pack(home: &Path) -> Result<PathBuf, String> {
    let prefix = if cfg!(target_os = "macos") {
        home.join("Library/Application Support/aterm/pkg")
    } else if cfg!(target_os = "linux") {
        home.join(".local/share/aterm/pkg")
    } else {
        return Err("atpkg installs no trust pack on this platform".into());
    };
    let store = prefix.join("store/trust");
    let current = store.join("current");
    let link = fs::symlink_metadata(&current)
        .map_err(|error| format!("no installed trust pack at {}: {error}", current.display()))?;
    if !link.file_type().is_symlink() {
        return Err(format!("{} does not name the active pack", current.display()));
    }
    let pack =
        fs::canonicalize(&current).map_err(|error| format!("{}: {error}", current.display()))?;
    let store =
        fs::canonicalize(&store).map_err(|error| format!("{}: {error}", store.display()))?;
    let numbered = pack.file_name().and_then(OsStr::to_str).is_some_and(|name| {
        let name = name.strip_suffix(".noindex").unwrap_or(name);
        !name.is_empty() && name.bytes().all(|b| b.is_ascii_digit()) && !name.starts_with('0')
    });
    if pack.parent() != Some(store.as_path()) || !numbered {
        return Err(format!("{} is not a numbered pack in {}", pack.display(), store.display()));
    }
    if fs::symlink_metadata(pack.join("toolchain")).is_ok_and(|meta| meta.file_type().is_symlink())
    {
        return Err(format!("{} is a wired sysroot, not a sealed pack", pack.display()));
    }
    Ok(pack)
}

/// The build record a pack carries at its root beside its seal (`tool-provenance.json`).
pub(crate) const SOURCE_TOOLCHAIN_BUILD_RECORD: &str = "tool-provenance.json";

/// Whether the source toolchain at `source` compiled its batteries with debug assertions:
/// the one profile setting that decides which of a battery's own checks run, and so what
/// it answers. (Overflow checks are always on: Trust's configuration refuses
/// `rust.overflow-checks = false`. The rest of a battery's profile changes its code, not
/// its answers, as another compiler does.)
///
/// The pack's build record names the configuration its cut parsed
/// (`bootstrap_lineage.mint_configuration.configuration_closure`); its one profile,
/// a file under `src/bootstrap/defaults/`, must be the bytes of this checkout's at `src`,
/// and its `rust.debug-assertions-tools`, else `rust.debug-assertions`, else
/// `rust.debug`, decides, as `Config` derives `tools_debug_assertions`. The cut's own
/// `bootstrap.toml`, which the record names only by digest, is the recreator's template,
/// which sets none of them. A record that names no profile, or another one's bytes,
/// decides nothing.
pub(crate) fn source_toolchain_tools_debug_assertions(
    source: &Path,
    src: &Path,
) -> Result<bool, String> {
    use sha2::Digest as _;
    let path = source.join(SOURCE_TOOLCHAIN_BUILD_RECORD);
    let record: serde_json::Value = fs::read(&path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))
        .and_then(|bytes| {
            serde_json::from_slice(&bytes)
                .map_err(|error| format!("cannot parse {}: {error}", path.display()))
        })?;
    let files = record
        .pointer("/bootstrap_lineage/mint_configuration/configuration_closure/files")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| format!("{} names no configuration its cut parsed", path.display()))?;
    let mut profiles = files.iter().filter_map(|file| {
        let relative = file.get("relative_path")?.as_str()?;
        relative.starts_with("src/bootstrap/defaults/").then_some((relative, file.get("sha256")))
    });
    let (Some((relative, sealed)), None) = (profiles.next(), profiles.next()) else {
        return Err(format!("{} names no single configuration profile", path.display()));
    };
    let sealed = sealed.and_then(serde_json::Value::as_str).unwrap_or_default();
    let bytes = fs::read(src.join(relative))
        .map_err(|error| format!("the source toolchain's profile {relative}: {error}"))?;
    if helpers::hex_encode(sha2::Sha256::digest(&bytes).as_slice()) != sealed {
        return Err(format!("the source toolchain was cut on other bytes of {relative}"));
    }
    let profile = std::str::from_utf8(&bytes)
        .ok()
        .and_then(|text| text.parse::<toml::Value>().ok())
        .ok_or_else(|| format!("cannot parse {relative}"))?;
    let rust = |key: &str| profile.get("rust").and_then(|rust| rust.get(key)?.as_bool());
    Ok(rust("debug-assertions-tools")
        .or_else(|| rust("debug-assertions"))
        .unwrap_or(rust("debug") == Some(true)))
}

/// Whether a battery's bytes carry `commit`, the commit of the build that compiled it,
/// as a record of that build: the full commit as a bare string (`CFG_VER_HASH`), or
/// its 9-digit form in a version (`(<short> ` of `CFG_VERSION`, `+g<short>` of
/// `CFG_TRUST_VERSION`). A path into the standard library's remapped sources,
/// `/rustc/<commit>/`, names where std was built, not what the battery binds.
pub(crate) fn records_its_compiler(bytes: &[u8], commit: &str) -> bool {
    let commit = commit.as_bytes();
    let short = &commit[..commit.len().min(9)];
    memchr::memmem::find_iter(bytes, commit).any(|at| !bytes[..at].ends_with(b"/rustc/"))
        || [[&b"("[..], short, &b" "[..]].concat(), [&b"+g"[..], short].concat()]
            .iter()
            .any(|marker| memchr::memmem::find(bytes, marker).is_some())
}

/// The batteries a stage-2 build would build in place of taking them: `wanted` are the
/// takeable ones, `ay` first, and `debug_assertions` is whether it compiles them with
/// debug assertions (`Config::tools_debug_assertions`).
#[derive(Clone, Copy, Debug)]
pub(crate) struct WantedVerifierTools<'a> {
    pub(crate) tools: &'a [(&'static str, trust_source_identity::IndependentToolComponent)],
    pub(crate) debug_assertions: bool,
}

/// The decision of [`Stage2VerifierTools`] for the checkout at `src` (HEAD `head`, its
/// `.gitmodules` paths `submodules`) and the source toolchain at `source`, for the
/// batteries `wanted`.
pub(crate) fn decide_stage2_verifier_tools(
    exec_ctx: &ExecutionContext,
    src: &Path,
    head: &crate::utils::channel::Info,
    submodules: &[String],
    source: &Path,
    host: TargetSelection,
    wanted: WantedVerifierTools<'_>,
) -> Stage2VerifierTools {
    match take_stage2_verifier_tools(exec_ctx, src, head, submodules, source, host, wanted) {
        Ok(taken) => Stage2VerifierTools::Taken(taken),
        Err(why) => Stage2VerifierTools::Built(why),
    }
}

fn take_stage2_verifier_tools(
    exec_ctx: &ExecutionContext,
    src: &Path,
    head: &crate::utils::channel::Info,
    submodules: &[String],
    source: &Path,
    host: TargetSelection,
    wanted: WantedVerifierTools<'_>,
) -> Result<TakenVerifierTools, String> {
    let WantedVerifierTools { tools: wanted, debug_assertions } = wanted;
    if wanted.first().map(|(name, _)| *name) != Some("ay") {
        return Err("nothing is taken without the ay every battery records".into());
    }
    let record_path = source.join(SOURCE_TOOLCHAIN_RECORD);
    let record = fs::read_to_string(&record_path)
        .map_err(|error| format!("cannot read {}: {error}", record_path.display()))
        .and_then(|text| parse_source_toolchain_record(&text))?;
    let cut = source_toolchain_tools_debug_assertions(source, src)?;
    if cut != debug_assertions {
        let on = |on: bool| if on { "on" } else { "off" };
        return Err(format!(
            "this build compiles the batteries with debug assertions {}, the source toolchain's \
             cut compiled them with debug assertions {}",
            on(debug_assertions),
            on(cut)
        ));
    }
    let mut roots = Vec::new();
    for (name, component) in wanted {
        if !submodules.iter().any(|path| path == component.root()) {
            return Err(format!("{} is not a submodule of this checkout", component.root()));
        }
        if !record.bins.contains_key(*name) {
            return Err(format!("the source toolchain's seal records no bin/{name}"));
        }
        roots.push(component.root());
    }
    trust_source_identity::inputs_unchanged_since(exec_ctx, src, &record.commit, head, &roots)?;
    for root in &roots {
        trust_source_identity::component_sources_closed(exec_ctx, src, root)?;
    }
    use sha2::Digest as _;
    let mut tools = Vec::new();
    let mut ay_sha256 = String::new();
    for (name, _) in wanted {
        let path = source.join("bin").join(exe(name, host));
        let bytes = fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))?;
        let sha256 = helpers::hex_encode(sha2::Sha256::digest(&bytes).as_slice());
        if record.bins[*name] != sha256 {
            return Err(format!(
                "{} is not the file its seal records ({sha256}, sealed {})",
                path.display(),
                record.bins[*name]
            ));
        }
        if records_its_compiler(&bytes, &record.commit) {
            return Err(format!("{} records its compiler {}", path.display(), record.commit));
        }
        if *name == "ay" {
            ay_sha256 = sha256.clone();
        } else if memchr::memmem::find(&bytes, ay_sha256.as_bytes()).is_none() {
            return Err(format!("{} does not record the ay {ay_sha256} beside it", path.display()));
        }
        tools.push(TakenVerifierTool { name, path, sha256 });
    }
    Ok(TakenVerifierTools { source: source.to_owned(), commit: record.commit, tools })
}

/// Whether a stage-2 build may take any battery: a native `x.py build --stage 2` in a
/// configuration [`verifier_tool_scheduling_known`] recognises. An error says why not.
fn stage2_verifier_tools_eligible(
    builder: &Builder<'_>,
    compiler: Compiler,
    ambient: Vec<(OsString, OsString)>,
) -> Result<(), String> {
    if builder.kind != Kind::Build {
        return Err(format!(
            "`x.py {}` compiles every battery with its compiler",
            builder.kind.as_str()
        ));
    }
    if compiler.stage != 2 || builder.top_stage != 2 {
        return Err("only a stage-2 sysroot of `x.py build --stage 2` takes batteries".into());
    }
    if !verifier_tool_scheduling_known(builder, compiler, 2, ambient) {
        return Err("the configuration is not one whose tool scheduling is audited".into());
    }
    Ok(())
}

/// The takeable batteries this build would build for its stage-2 sysroot, `ay` first.
fn stage2_wanted_verifier_tools(
    builder: &Builder<'_>,
) -> Vec<(&'static str, trust_source_identity::IndependentToolComponent)> {
    let tools = builder.config.tools.as_ref();
    let ay_present = verifier_backend_source_present(&builder.src, AY_SOURCE_MANIFEST);
    let ty = ay_present
        && default_source_solver_enabled(builder.config.extended, tools, ay_present)
        && l2_backend_enabled(tools, "ty")
        && verifier_backend_source_present(&builder.src, TY_SOURCE_MANIFEST);
    STAGE2_TAKEABLE_VERIFIER_TOOLS
        .into_iter()
        .filter(|(name, _)| match *name {
            "ay" => ay_present,
            "ty" => ty,
            _ => false,
        })
        .collect()
}

fn stage2_verifier_tools(
    builder: &Builder<'_>,
    compiler: Compiler,
    ambient: Vec<(OsString, OsString)>,
) -> Stage2VerifierTools {
    let home = ambient.iter().find(|(key, _)| key == "HOME").map(|(_, value)| PathBuf::from(value));
    if let Err(why) = stage2_verifier_tools_eligible(builder, compiler, ambient) {
        return Stage2VerifierTools::Built(why);
    }
    let source = match home.as_deref().map(installed_trust_pack) {
        Some(Ok(source)) => source,
        Some(Err(why)) => return Stage2VerifierTools::Built(why),
        None => return Stage2VerifierTools::Built("HOME is not set".into()),
    };
    let Some(head) = builder.rust_info().info() else {
        return Stage2VerifierTools::Built("git names no HEAD for this checkout".into());
    };
    decide_stage2_verifier_tools(
        builder.config.exec_ctx(),
        &builder.src,
        head,
        &build_helper::util::parse_gitmodules(&builder.src),
        &source,
        compiler.host,
        WantedVerifierTools {
            tools: &stage2_wanted_verifier_tools(builder),
            debug_assertions: builder.config.tools_debug_assertions,
        },
    )
}

// Trust: one decision per stage-2 compiler, shared by `ensure_sysroot_ay` (before the
// compiler that records the `ay` is compiled) and the post-assembly batteries.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Stage2VerifierToolSource {
    compiler: Compiler,
}

#[cfg(test)]
thread_local! {
    /// What a unit test hands [`Stage2VerifierToolSource`]; a test that hands nothing
    /// takes nothing, whatever this machine has installed.
    static STAGE2_VERIFIER_TOOLS_FOR_TEST: std::cell::RefCell<Option<Stage2VerifierTools>> =
        const { std::cell::RefCell::new(None) };
}

impl Step for Stage2VerifierToolSource {
    type Output = Stage2VerifierTools;

    fn run(self, builder: &Builder<'_>) -> Stage2VerifierTools {
        #[cfg(test)]
        let decision =
            STAGE2_VERIFIER_TOOLS_FOR_TEST.with_borrow(Clone::clone).unwrap_or_else(|| {
                Stage2VerifierTools::Built("a unit test hands no source toolchain".into())
            });
        #[cfg(not(test))]
        let decision = stage2_verifier_tools(builder, self.compiler, env::vars_os().collect());
        match &decision {
            Stage2VerifierTools::Taken(taken) => builder.info(&format!(
                "Taking stage{} verifier tools {} from {} (their inputs are unchanged since {})",
                self.compiler.stage,
                taken.tools.iter().map(|tool| tool.name).collect::<Vec<_>>().join(", "),
                taken.source.display(),
                taken.commit,
            )),
            Stage2VerifierTools::Built(why) => builder.config.do_if_verbose(|| {
                println!("Building stage{} verifier tools: {why}", self.compiler.stage)
            }),
        }
        decision
    }
}

/// The batteries the stage-2 sysroot of `compiler` takes from its source toolchain, if
/// any ([`Stage2VerifierTools`]). Only `x.py build` asks.
fn taken_stage2_verifier_tools(
    builder: &Builder<'_>,
    compiler: Compiler,
) -> Option<TakenVerifierTools> {
    if builder.kind != Kind::Build || compiler.stage != 2 {
        return None;
    }
    match builder.ensure(Stage2VerifierToolSource { compiler }) {
        Stage2VerifierTools::Taken(taken) => Some(taken),
        Stage2VerifierTools::Built(_) => None,
    }
}

/// Installs the taken battery `name` (not `ay`, which [`ensure_sysroot_ay`] installs)
/// where its build would have put it, the tools directory of `compiler`, so that sysroot
/// restoration copies the same bytes, and returns that path.
fn install_taken_verifier_tool(
    builder: &Builder<'_>,
    taken: &TakenVerifierTools,
    name: &str,
    compiler: Compiler,
) -> PathBuf {
    let tool = taken.tool(name).unwrap_or_else(|| panic!("no taken verifier tool {name}"));
    let installed = builder.tools_dir(compiler, compiler.host).join(exe(name, compiler.host));
    if !builder.config.dry_run() {
        copy_taken_verifier_tool(&tool.path, &tool.sha256, &installed).unwrap_or_else(|error| {
            panic!("cannot take {} from {}: {error}", tool.path.display(), taken.source.display())
        });
    }
    installed
}

/// Trust (DC-16a): copies a taken battery from its source toolchain to `installed`. It is
/// a copy of its own, never a link into the pack, and it must be the file the decision
/// read: `sealed` is its SHA-256.
pub(crate) fn copy_taken_verifier_tool(
    source: &Path,
    sealed: &str,
    installed: &Path,
) -> io::Result<()> {
    use sha2::Digest as _;
    let bytes = fs::read(source)?;
    let sha256 = helpers::hex_encode(sha2::Sha256::digest(&bytes).as_slice());
    if sha256 != sealed {
        return Err(io::Error::other(format!(
            "it is {sha256}, not the {sealed} bootstrap took (it changed while it was taken)"
        )));
    }
    let next = installed.with_extension("installing");
    match fs::remove_file(&next) {
        Err(error) if error.kind() != io::ErrorKind::NotFound => return Err(error),
        _ => {}
    }
    fs::write(&next, &bytes)?;
    fs::set_permissions(&next, fs::metadata(source)?.permissions())?;
    fs::rename(&next, installed)
}

// Trust: share the actual Rustdoc step's registered source aliases with the
// partial-source selector so either spelling builds the same dependency graph.
const RUSTDOC_SOURCE_PATHS: &[&str] = &["src/tools/trustdoc", "src/librustdoc"];

/// Trust: an exact stage1 source request builds only those requested targets
/// and their real dependencies. In particular Rustc::run still installs the
/// exact AY whose bytes the compiler records. This is not a complete SDK build:
/// default/full, mixed or unknown selections and every stage2+ invocation keep
/// the existing batteries-on assembly graph.
pub(crate) fn is_partial_stage1_source_build(
    kind: Kind,
    compiler_stage: u32,
    top_stage: u32,
    include_default_paths: bool,
    paths: &[PathBuf],
) -> bool {
    kind == Kind::Build
        && compiler_stage == 1
        && top_stage == 1
        && !include_default_paths
        && !paths.is_empty()
        && paths.iter().all(|path| {
            path.to_str().is_some_and(|path| {
                matches!(
                    path,
                    "compiler" | "compiler/rustc" | "library" | "library/std" | "src/tools/targo"
                ) || RUSTDOC_SOURCE_PATHS.contains(&path)
            })
        })
}

fn should_assemble_user_facing_tools(kind: Kind, compiler_stage: u32) -> bool {
    compiler_stage >= 2 && kind == Kind::Build
}

fn restore_rust_analyzer_proc_macro_srv_for_config(config: &Config) -> bool {
    restore_rust_analyzer_proc_macro_srv_for_tool_settings(config.extended, config.tools.as_ref())
}

fn restore_rust_analyzer_proc_macro_srv_for_tool_settings(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
) -> bool {
    // Trust: tool-settings spellings are Trust-canonical. The user-facing
    // `tools = [...]` list uses `trust-analyzer` and
    // `trust-analyzer-proc-macro-srv`; either one enables the proc-macro
    // server build.
    tool_enabled_for_tool_settings(extended, tools, "trust-analyzer")
        || tool_enabled_for_tool_settings(extended, tools, "trust-analyzer-proc-macro-srv")
}

macro_rules! bootstrap_tool {
    ($(
        $name:ident, $path:expr, $tool_name:expr
        $(,is_external_tool = $external:expr)*
        $(,allow_features = $allow_features:expr)?
        $(,submodules = $submodules:expr)?
        $(,artifact_kind = $artifact_kind:expr)?
        ;
    )+) => {
        #[derive(PartialEq, Eq, Clone)]
        pub(crate) enum Tool {
            $(
                #[allow(dead_code, reason = "not all bootstrap-tools need a variant")]
                $name,
            )+
        }

        impl<'a> Builder<'a> {
            /// Ensure a tool is built, then get the path to its executable.
            ///
            /// The actual building, if any, will be handled via [`ToolBuild`].
            pub(crate) fn tool_exe(&self, tool: Tool) -> PathBuf {
                self.tool(tool).tool_path
            }

            /// Ensure a tool is built, then return its build output.
            ///
            /// The actual building, if any, will be handled via [`ToolBuild`].
            pub(crate) fn tool(&self, tool: Tool) -> ToolBuildResult {
                match tool {
                    $(Tool::$name =>
                        self.ensure($name {
                            compiler: self.compiler(0, self.config.host_target),
                            target: self.config.host_target,
                        }),
                    )+
                }
            }
        }

        $(
            #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        pub struct $name {
            pub compiler: Compiler,
            pub target: TargetSelection,
        }

        impl CommandLineStep for $name {
            type Output = ToolBuildResult;

            fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
                run.path($path)
            }

            fn make_run(run: RunConfig<'_>) {
                run.builder.ensure($name {
                    // snapshot compiler
                    compiler: run.builder.compiler(0, run.builder.config.host_target),
                    target: run.target,
                });
            }

            fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
                $(
                    for submodule in $submodules {
                        builder.require_submodule(submodule, None);
                    }
                )*

                builder.ensure(ToolBuild {
                    build_compiler: self.compiler,
                    output_compiler: output_compiler_for_tool(self.compiler, self.target),
                    target: self.target,
                    tool: $tool_name,
                    mode: Mode::ToolBootstrap,
                    path: $path,
                    source_type: if false $(|| $external)* {
                        SourceType::Submodule
                    } else {
                        SourceType::InTree
                    },
                    extra_features: vec![],
                    allow_features: {
                        let mut _value = "";
                        $( _value = $allow_features; )?
                        _value
                    },
                    cargo_args: vec![],
                    artifact_kind: if false $(|| $artifact_kind == ToolArtifactKind::Library)* {
                        ToolArtifactKind::Library
                    } else {
                        ToolArtifactKind::Binary
                    }
                })
            }

            fn metadata(&self) -> Option<StepMetadata> {
                Some(
                    StepMetadata::build(stringify!($name), self.target)
                        .built_by(self.compiler)
                )
            }
        }
        )+
    }
}

// Trust: the compiletest library now carries the native query transport even when
// consumed only for rustdoc GUI properties. Keep its FD API permission scoped
// to these two consumers; the ordinary stable tool sandbox stays unchanged.
pub(super) const COMPILETEST_ALLOW_FEATURES: &str = "trust_process_inherit_fds";

// Trust: compiletest's own library test target also enables the native unit-entry
// runner (lib.rs's `#![cfg_attr(test, feature(...))]`). Its test build and its
// `--all-targets` check both compile that target, so both allow exactly this set
// (COMPILETEST-CHECK-INHERIT-FDS-1).
pub(super) const COMPILETEST_SELF_ALLOW_FEATURES: &str =
    "trust_process_inherit_fds,test,custom_test_frameworks,exitcode_exit_method";

pub(super) fn prepare_compiletest_test_cargo(
    builder: &Builder<'_>,
    compiler: Compiler,
    target: TargetSelection,
) -> CargoCommand {
    let mut cargo = prepare_tool_cargo(
        builder,
        compiler,
        Mode::ToolBootstrap,
        target,
        Kind::Test,
        "src/tools/compiletest",
        SourceType::InTree,
        &[],
    );
    // Trust: native unit entry must capture before libtest opens descriptors; its three
    // runner features preserve libtest's real ExitCode beside the transport's one.
    cargo.allow_features(COMPILETEST_SELF_ALLOW_FEATURES);
    cargo
}

bootstrap_tool!(
    // This is marked as an external tool because it includes dependencies
    // from submodules. Trying to keep the lints in sync between all the repos
    // is a bit of a pain. Unfortunately it means the rustbook source itself
    // doesn't deny warnings, but it is a relatively small piece of code.
    Rustbook, "src/tools/rustbook", "rustbook", is_external_tool = true;
    UnstableBookGen, "src/tools/unstable-book-gen", "unstable-book-gen";
    Tidy, "src/tools/tidy", "tidy";
    Linkchecker, "src/tools/linkchecker", "linkchecker";
    CargoTest, "src/tools/cargotest", "cargotest";
    Compiletest, "src/tools/compiletest", "compiletest", allow_features = COMPILETEST_ALLOW_FEATURES;
    RemoteTestClient, "src/tools/remote-test-client", "remote-test-client";
    RustInstaller, "src/tools/rust-installer", "rust-installer";
    RustdocTheme, "src/tools/rustdoc-themes", "rustdoc-themes";
    LintDocs, "src/tools/lint-docs", "lint-docs";
    JsonDocCk, "src/tools/jsondocck", "jsondocck";
    JsonDocLint, "src/tools/jsondoclint", "jsondoclint";
    HtmlChecker, "src/tools/html-checker", "html-checker";
    BumpStage0, "src/tools/bump-stage0", "bump-stage0";
    ReplaceVersionPlaceholder, "src/tools/replace-version-placeholder", "replace-version-placeholder";
    CollectLicenseMetadata, "src/tools/collect-license-metadata", "collect-license-metadata";
    GenerateCopyright, "src/tools/generate-copyright", "generate-copyright";
    GenerateWindowsSys, "src/tools/generate-windows-sys", "generate-windows-sys";
    RustdocGUITest, "src/tools/rustdoc-gui-test", "rustdoc-gui-test", allow_features = COMPILETEST_ALLOW_FEATURES;
    CoverageDump, "src/tools/coverage-dump", "coverage-dump";
    UnicodeTableGenerator, "src/tools/unicode-table-generator", "unicode-table-generator";
    FeaturesStatusDump, "src/tools/features-status-dump", "features-status-dump";
    // Trust: opt-dist declares no source dependency of its own. Its PGO training
    // stage drives an external `rustc-perf` checkout, supplied at run time with
    // `--rustc-perf-checkout-dir`; that benchmark corpus is not carried in-tree.
    OptimizedDist, "src/tools/opt-dist", "opt-dist";
    RunMakeSupport, "src/tools/run-make-support", "run_make_support", artifact_kind = ToolArtifactKind::Library;
    IntrinsicTest, "library/stdarch/crates/intrinsic-test", "intrinsic-test";
);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ErrorIndex {
    compilers: RustcPrivateCompilers,
}

impl ErrorIndex {
    pub fn command(builder: &Builder<'_>, compilers: RustcPrivateCompilers) -> BootstrapCommand {
        // Error-index-generator links with the rustdoc library, so we need to add `rustc_lib_paths`
        // for rustc_private and libLLVM.so, and `sysroot_lib` for libstd, etc.
        let mut cmd = command(builder.ensure(ErrorIndex { compilers }).tool_path);

        let target_compiler = compilers.target_compiler();
        let mut dylib_paths = builder.rustc_lib_paths(target_compiler);
        dylib_paths.push(builder.sysroot_target_libdir(target_compiler, target_compiler.host));
        add_dylib_path(dylib_paths, &mut cmd);
        cmd
    }
}

impl CommandLineStep for ErrorIndex {
    type Output = ToolBuildResult;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/error_index_generator")
    }

    fn make_run(run: RunConfig<'_>) {
        // NOTE: This `make_run` isn't used in normal situations, only if you
        // manually build the tool with `x.py build
        // src/tools/error-index-generator` which almost nobody does.
        // Normally, `x.py test` or `x.py doc` will use the
        // `ErrorIndex::command` function instead.
        run.builder.ensure(ErrorIndex {
            compilers: RustcPrivateCompilers::new(
                run.builder,
                run.builder.top_stage,
                run.builder.host_target,
            ),
        });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.ensure(ToolBuild {
            build_compiler: self.compilers.build_compiler,
            output_compiler: self.compilers.target_compiler,
            target: self.compilers.target(),
            tool: "error_index_generator",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/error_index_generator",
            source_type: SourceType::InTree,
            extra_features: Vec::new(),
            allow_features: "",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        })
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(
            StepMetadata::build("error-index", self.compilers.target())
                .built_by(self.compilers.build_compiler),
        )
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct RemoteTestServer {
    pub build_compiler: Compiler,
    pub target: TargetSelection,
}

impl CommandLineStep for RemoteTestServer {
    type Output = ToolBuildResult;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/remote-test-server")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RemoteTestServer {
            build_compiler: get_tool_target_compiler(
                run.builder,
                ToolTargetBuildMode::Build(run.target),
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.ensure(ToolBuild {
            build_compiler: self.build_compiler,
            output_compiler: output_compiler_for_tool(self.build_compiler, self.target),
            target: self.target,
            tool: "remote-test-server",
            mode: Mode::ToolTarget,
            path: "src/tools/remote-test-server",
            source_type: SourceType::InTree,
            extra_features: Vec::new(),
            allow_features: "",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        })
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("remote-test-server", self.target).built_by(self.build_compiler))
    }
}

/// Represents `Rustdoc` that either comes from the external stage0 sysroot or that is built
/// locally.
/// Rustdoc is special, because it both essentially corresponds to a `Compiler` (that can be
/// externally provided), but also to a `ToolRustcPrivate` tool.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Rustdoc {
    /// If the stage of `target_compiler` is `0`, then rustdoc is externally provided.
    /// Otherwise it is built locally.
    pub target_compiler: Compiler,
}

fn rustdoc_sysroot_bins(
    bindir: &Path,
    stage: u32,
    rustdoc_file_name: &str,
    trustdoc_file_name: &str,
) -> (PathBuf, Vec<PathBuf>) {
    let inherited_rustdoc = bindir.join(rustdoc_file_name);
    let trustdoc = bindir.join(trustdoc_file_name);
    if stage < 2 {
        // Bootstrap stage1 remains a compatibility sysroot, so retain rustdoc
        // while also materializing the branded hard-link for Trust-native tests.
        (inherited_rustdoc, vec![trustdoc])
    } else {
        // Stage2+: trustdoc is the primary name, but keep the inherited
        // `rustdoc` alias — cargo's doctest phase spawns `bin/rustdoc` and
        // rustup's proxy fails a linked toolchain without it ("'rustdoc' is
        // not installed"). Same contract that keeps `bin/rustc` in Assemble.
        (trustdoc, vec![inherited_rustdoc])
    }
}

impl CommandLineStep for Rustdoc {
    /// Path to the built rustdoc binary.
    type Output = PathBuf;

    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.multi_path(RUSTDOC_SOURCE_PATHS)
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Rustdoc {
            target_compiler: run.builder.compiler(run.builder.top_stage, run.target),
        });
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let target_compiler = self.target_compiler;
        let target = target_compiler.host;

        // If stage is 0, we use a prebuilt rustdoc from stage0
        if target_compiler.stage == 0 {
            if !target_compiler.is_snapshot(builder) {
                panic!("rustdoc in stage 0 must be snapshot rustdoc");
            }

            return builder.initial_rustdoc.clone();
        }

        // If stage is higher, we build rustdoc instead
        let bin_rustdoc = || -> (PathBuf, Vec<PathBuf>) {
            let sysroot = builder.sysroot(target_compiler);
            let bindir = sysroot.join("bin");
            t!(fs::create_dir_all(&bindir));
            // `rustdoc` is (re-)materialized as an alias at every stage;
            // copy_link removes a stale destination first, so no pre-purge.
            rustdoc_sysroot_bins(
                &bindir,
                target_compiler.stage,
                &exe("rustdoc", target_compiler.host),
                &exe("trustdoc", target_compiler.host),
            )
        };

        // If CI rustc is enabled and we haven't modified the rustdoc sources,
        // use the precompiled rustdoc from CI rustc's sysroot to speed up bootstrapping.
        if builder.download_rustc() && builder.rust_info().is_managed_git_subrepository() {
            let files_to_track =
                &["src/librustdoc", "src/tools/trustdoc", "src/rustdoc-json-types"];

            // Check if unchanged
            if !builder.config.has_changes_from_upstream(files_to_track) {
                let precompiled_rustdoc = builder
                    .config
                    .ci_rustc_dir()
                    .join("bin")
                    .join(exe("rustdoc", target_compiler.host));

                let (bin_rustdoc, alias_bins) = bin_rustdoc();
                builder.copy_link(&precompiled_rustdoc, &bin_rustdoc, FileType::Executable);
                for alias in &alias_bins {
                    builder.copy_link(&precompiled_rustdoc, &alias, FileType::Executable);
                }
                validate_installed_rustc_private_tool(builder, target_compiler, &bin_rustdoc);
                for alias in &alias_bins {
                    validate_installed_rustc_private_tool(builder, target_compiler, alias);
                }
                return bin_rustdoc;
            }
        }

        // The presence of `target_compiler` ensures that the necessary libraries (codegen backends,
        // compiler libraries, ...) are built. Rustdoc does not require the presence of any
        // libraries within sysroot_libdir (i.e., rustlib), though doctests may want it (since
        // they'll be linked to those libraries). As such, don't explicitly `ensure` any additional
        // libraries here. The intuition here is that If we've built a compiler, we should be able
        // to build rustdoc.
        let mut extra_features = Vec::new();
        if !builder.config.rust_debug_logging {
            extra_features.push("max_level_info".to_string())
        }

        let compilers = RustcPrivateCompilers::from_target_compiler(builder, target_compiler);
        let tool_path = builder
            .ensure(ToolBuild {
                build_compiler: compilers.build_compiler,
                output_compiler: target_compiler,
                target,
                // Cargo adds a number of paths to the dylib search path on windows, which results in
                // the wrong rustdoc being executed. To avoid the conflicting rustdocs, we name the "tool"
                // rustdoc a different name.
                // Trust: the trustdoc tool binary keeps its underscore name
                // (src/tools/trustdoc/Cargo.toml); upstream renamed theirs to
                // hyphens in 1.101.
                tool: "rustdoc_tool_binary",
                mode: Mode::ToolRustcPrivate,
                path: "src/tools/trustdoc",
                source_type: SourceType::InTree,
                extra_features,
                allow_features: "",
                cargo_args: Vec::new(),
                artifact_kind: ToolArtifactKind::Binary,
            })
            .tool_path;

        if builder.config.rust_debuginfo_level_tools == DebuginfoLevel::None {
            // Due to LTO a lot of debug info from C++ dependencies such as jemalloc can make it into
            // our final binaries
            compile::strip_debug(builder, target, &tool_path);
        }
        let (bin_rustdoc, alias_bins) = bin_rustdoc();
        builder.copy_link(&tool_path, &bin_rustdoc, FileType::Executable);
        for alias in &alias_bins {
            builder.copy_link(&tool_path, &alias, FileType::Executable);
        }
        validate_installed_rustc_private_tool(builder, target_compiler, &bin_rustdoc);
        for alias in &alias_bins {
            validate_installed_rustc_private_tool(builder, target_compiler, alias);
        }
        bin_rustdoc
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(
            StepMetadata::build("rustdoc", self.target_compiler.host)
                .stage(self.target_compiler.stage),
        )
    }
}

/// Trust: the one build recipe for the Trust Cargo, shared by the standalone
/// `Cargo` step, the batteries-on verifier frontend and the user-facing sysroot
/// tools so they cannot drift apart (they are the same `ToolBuild` step).
///
/// The Trust Cargo's package, library crate and only binary are all named
/// `targo` (src/tools/targo/Cargo.toml), so the build compiles `--crate-name
/// targo` and the artifact in `cargo_out` and in the stage's tools directory is
/// the file `targo`. Sysroot restoration installs exactly that artifact as
/// `bin/targo` and, as the one compatibility alias, `bin/cargo`
/// (`restored_sysroot_bins_for_tool_settings`,
/// `upstream_compat_bin_for_tool_source`). Until 2026-09-29 all three were named
/// `cargo`, and restoration copied whatever tools-directory file carried that
/// name to `bin/targo`, so a stale `cargo` file there could reach the sysroot
/// under the Trust name. The artifact name is spelled as a literal here and in
/// those two functions because `tools/preflight.py` and
/// `scripts/recreate_bootstrap.py` read it textually;
/// `trust_cargo_is_built_restored_and_aliased_under_targo` pins the three
/// spellings together.
fn targo_tool_build_recipe(
    build_compiler: Compiler,
    output_compiler: Compiler,
    target: TargetSelection,
) -> ToolBuild {
    ToolBuild {
        build_compiler,
        output_compiler,
        target,
        tool: "targo",
        mode: Mode::ToolTarget,
        path: "src/tools/targo",
        source_type: SourceType::Submodule,
        extra_features: Vec::new(),
        allow_features: TARGO_ALLOW_FEATURES,
        cargo_args: Vec::new(),
        artifact_kind: ToolArtifactKind::Binary,
    }
}

// Native Targo's job service uses the same proof-session, certification and
// discharge implementations as the verifier tools. Its build and self-test
// recipes share the verifier runtime's exact allowances.
pub(super) const TARGO_ALLOW_FEATURES: &str = CARGO_TRUST_ALLOW_FEATURES;

// Trust: build an engineering Cargo input without assembling a next-stage SDK.
// Keep the ordinary Cargo build/test steps below responsible for SDK installation.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TargoBuildTool {
    target: TargetSelection,
}

// Trust: cache capabilities with this built artifact, never the seed's answer.
#[derive(Clone)]
pub(crate) struct TargoBuildToolResult {
    // Trust: only bootstrap's assertions inspect the full artifact descriptor.
    #[cfg(test)]
    pub(crate) artifact: ToolBuildResult,
    pub(crate) cargo: CargoProgram,
    // Trust: retain the original produced spelling; probe it only if selected.
    pub(crate) native_path: PathBuf,
}

impl TargoBuildTool {
    pub(crate) fn native(builder: &Builder<'_>) -> Self {
        Self { target: builder.host_target }
    }
}

impl CommandLineStep for TargoBuildTool {
    type Output = TargoBuildToolResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("targo-build-tool")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

    fn make_run(run: RunConfig<'_>) {
        // Explicit engineering production requires identity. Internal SDK builds
        // retain their existing omit-git-hash/source-tarball policy.
        run.builder
            .version_info()
            .sha()
            .expect("targo-build-tool requires source identity; do not omit git hash");
        run.builder.ensure(Self { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> TargoBuildToolResult {
        assert_eq!(
            self.target, builder.host_target,
            "targo-build-tool only supports the native build host"
        );
        builder.sess.require_submodule("src/tools/targo", None);
        let compiler = builder.compiler(0, builder.host_target);
        // The output descriptor is also stage0: ToolBuild copies into tools-bin,
        // never the downloaded seed or a stage1 sysroot, and needs no host SDK.
        let result = builder.ensure(targo_tool_build_recipe(compiler, compiler, self.target));
        let cargo_alias =
            copy_targo_build_tool_alias(&result.tool_path, self.target, |src, dst| {
                builder.copy_link(src, dst, FileType::Executable);
            });
        let cargo = CargoProgram::probe(builder.config.exec_ctx(), cargo_alias);
        assert!(!cargo.unverified_lane, "the built cargo alias must retain Cargo compatibility");
        // Trust: compatibility-only builds need no native capability probe.
        let native_path = result.tool_path.clone();
        builder.info(&format!(
            "Engineering build-tool artifact: {} (cargo: {}; metadata: {}; compiler: stage0 {}; release: {}; source: {}). \
             This is not SDK, seed, or proof qualification.",
            result.tool_path.display(),
            cargo.path.display(),
            cargo.metadata_flag,
            builder.initial_rustc.display(),
            builder.rust_release(),
            builder.version_info().sha().unwrap_or("omitted or unavailable"),
        ));
        TargoBuildToolResult {
            #[cfg(test)]
            artifact: result,
            cargo,
            native_path,
        }
    }
}

// Trust: keep both invocation names byte-identical without installing a sysroot.
fn copy_targo_build_tool_alias(
    artifact: &Path,
    target: TargetSelection,
    copy: impl FnOnce(&Path, &Path),
) -> PathBuf {
    let alias = artifact.with_file_name(exe("cargo", target));
    copy(artifact, &alias);
    alias
}

/// Builds the Trust Cargo, `targo` (the tool historically called cargo).
/// Note that it can be built using a stable compiler.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Cargo {
    build_compiler: Compiler,
    target: TargetSelection,
}

impl Cargo {
    /// Returns `Cargo` that will be **compiled** by the passed compiler, for the given
    /// `target`.
    pub fn from_build_compiler(build_compiler: Compiler, target: TargetSelection) -> Self {
        Self { build_compiler, target }
    }
}

impl CommandLineStep for Cargo {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/targo")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.tool_enabled("targo")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Cargo {
            build_compiler: get_tool_target_compiler(
                run.builder,
                ToolTargetBuildMode::Build(run.target),
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.sess.require_submodule("src/tools/targo", None);

        builder.std(self.build_compiler, builder.host_target);
        builder.std(self.build_compiler, self.target);

        let target_compiler = builder.compiler(self.build_compiler.stage + 1, self.target);
        let tool_result = builder.ensure(targo_tool_build_recipe(
            self.build_compiler,
            target_compiler,
            self.target,
        ));

        // Trust: with its `cargo` alias (`sysroot_bin_names_for_tool_source`);
        // the returned path is still the first name, `targo`.
        let tool_path = copy_bins_to_sysroot(
            builder,
            target_compiler,
            &tool_result.tool_path,
            &sysroot_bin_names_for_tool_source("targo"),
        );

        ToolBuildResult {
            tool_path,
            build_compiler: tool_result.build_compiler,
            artifacts: tool_result.artifacts,
        }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("targo", self.target).built_by(self.build_compiler))
    }
}

/// Builds the selected toolchain frontend in a local stage1 build as well as
/// later stages. The broad sysroot assembly intentionally starts at stage2;
/// this standalone step is the stage1/default and explicit-path owner.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Trustup {
    build_compiler: Compiler,
    target: TargetSelection,
}

fn trustup_tool_build_recipe(
    build_compiler: Compiler,
    output_compiler: Compiler,
    target: TargetSelection,
) -> ToolBuild {
    ToolBuild {
        build_compiler,
        output_compiler,
        target,
        tool: "trustup",
        mode: Mode::ToolTarget,
        path: "src/tools/trustup",
        source_type: SourceType::InTree,
        extra_features: Vec::new(),
        allow_features: "",
        cargo_args: Vec::new(),
        artifact_kind: ToolArtifactKind::Binary,
    }
}

/// Produces the same native Trustup recipe without assembling or installing an SDK.
/// Engineering continuations bind the returned bytes and own any later delivery.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TrustupBuildTool {
    target: TargetSelection,
}

impl CommandLineStep for TrustupBuildTool {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trustup-build-tool")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder
            .version_info()
            .sha()
            .expect("trustup-build-tool requires source identity; do not omit git hash");
        run.builder.ensure(Self { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        assert_eq!(
            self.target, builder.host_target,
            "trustup-build-tool only supports the native build host"
        );
        let compiler = builder.compiler(0, builder.host_target);
        // ToolTarget uses the actual snapshot's native std and the current
        // source-built Cargo. output0 writes tools-bin, never stage1 or the seed.
        let result = builder.ensure(trustup_tool_build_recipe(compiler, compiler, self.target));
        builder.info(&format!(
            "Engineering Trustup artifact: {} (source: {}). This is not SDK, seed, or proof qualification.",
            result.tool_path.display(),
            builder.version_info().sha().unwrap_or("omitted or unavailable"),
        ));
        result
    }
}

impl CommandLineStep for Trustup {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/trustup")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.tool_enabled("trustup")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Trustup {
            build_compiler: get_tool_target_compiler(
                run.builder,
                ToolTargetBuildMode::Build(run.target),
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.std(self.build_compiler, builder.host_target);
        builder.std(self.build_compiler, self.target);
        let target_compiler = builder.compiler(self.build_compiler.stage + 1, self.target);
        let result = builder.ensure(trustup_tool_build_recipe(
            self.build_compiler,
            target_compiler,
            self.target,
        ));
        let tool_path =
            copy_bins_to_sysroot(builder, target_compiler, &result.tool_path, &["trustup"]);
        ToolBuildResult { tool_path, ..result }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("trustup", self.target).built_by(self.build_compiler))
    }
}

/// Builds the targo-trust tool.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TCargoTrust {
    build_compiler: Compiler,
    target: TargetSelection,
}

// Trust: share the unchanged frontend recipe between SDK and artifact producers.
fn targo_trust_tool_build_recipe(
    build_compiler: Compiler,
    output_compiler: Compiler,
    target: TargetSelection,
) -> ToolBuild {
    ToolBuild {
        build_compiler,
        output_compiler,
        target,
        tool: "targo-trust",
        mode: Mode::ToolTarget,
        path: "targo-trust",
        source_type: SourceType::InTree,
        extra_features: targo_trust_in_process_features(),
        allow_features: CARGO_TRUST_ALLOW_FEATURES,
        cargo_args: locked_cargo_args(&[]),
        artifact_kind: ToolArtifactKind::Binary,
    }
}

// Trust: this exact native artifact role retains compiler identity separately.
fn retained_frontend_tool_build_recipe(compiler: Compiler, target: TargetSelection) -> ToolBuild {
    ToolBuild {
        artifact_kind: ToolArtifactKind::RetainedFrontendBinary,
        ..targo_trust_tool_build_recipe(compiler, compiler, target)
    }
}

pub(super) fn targo_trust_in_process_features() -> Vec<String> {
    // Trust: `ay-certify` makes the SHIPPED verifier's proof-carrying-ay promotion
    // lane LIVE (ay UNSAT for LIA/BV-mul/BV-shift → natively re-derived in the Clean
    // kernel → Certified, modulo the 3 Lean-core axioms). Without it,
    // `promote_to_certified` is the identity and every ay verdict stays a trusted
    // SmtBacked seam — a dead lane undercutting the Clean kernel as the sole
    // PROOF-CHECKING trust root (docs/TRUST-BASE-AND-SCOPE.md).
    [
        "trust-mc-in-process",
        "trust-wp-in-process",
        "trust-vc-in-process",
        "ay-backend",
        "ay-certify",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

// Trust: `try_trait_v2` is required by `trust-types`' fail-closed `Discharge<T>`
// `?`-propagation (the structural prevention of the unmodeled-construct→PROVED
// false-proof class). Added alongside `min_specialization`/`specialization` so the
// shipped `targo-trust` and `trustd` tool builds (which both depend on
// trust-types) allow it.
// `try_trait_v2_residual` joined in the 1.99 migration: the newer `Try` trait
// requires `type Residual: Residual<Self::Output>`, so `Discharge` now also
// implements `std::ops::Residual`.
// Trust: `allocator_ext` is required by ay-sat's fallible Box::try_new through
// the proof-runtime closure shared by the native job service and verifier
// tools. It replaces the previous broader allocator_api permission for the
// same API; generic tool defaults keep their own restrictions.
// This list is a LIABILITY, not a convenience: every entry is an unstable
// feature the compiler's own build graph is then permitted to depend on.
// `variant_count` was briefly added here for `crates/trust-machine-sem` (which
// entered the graph via `compiler/rustc_codegen_trust_cg` and
// `crates/trust-cg-bridge`) to back a const assertion that its `Effect` name
// table named every variant. It has been REMOVED: that crate now expands the
// name table and its wildcard-free match from a single token list
// (`declare_effect_census!` in `effect.rs`), so the drift is unrepresentable
// rather than asserted — a stronger check that costs no unstable feature. Prefer
// that shape to a new entry here.
// Trust: `stdarch_x86_avx512` has been REMOVED, and this is a real TCB reduction —
// one fewer unstable feature the compiler's own build graph is permitted to use.
//
// It was here for exactly one crate: curve25519-dalek gates its AVX-512 backend
// behind it (`src/lib.rs:15-19`, under `curve25519_dalek_backend = "simd"` +
// `nightly` + x86/x86_64), and it entered every build that used this list through
//     targo-trust -> trust-proof-cert -> ed25519-dalek -> curve25519-dalek.
// Phase 1d cut that chain: `trust-proof-cert` now depends on the Trust-owned
// `trust-ed25519`, and the incumbent survives only as an acceptance-gate
// *dev*-dependency of `trust-ed25519`/`trust-rand`.
//
// Checked before removing, on the resolved graphs rather than by inspection —
// every package in BOTH closures this list applies to was scanned for the feature:
//   * targo-trust (5 of the 6 sites; `Kind::Test` at test.rs includes dev-deps):
//     curve25519-dalek is absent entirely, and NO package's Rust source gates on
//     `stdarch_x86_avx512`.
//   * the former trustd build from `crates/trust-router` (a `--bin` build, so no dev-deps):
//     curve25519-dalek is absent; the only two sources mentioning the feature are
//     `rand` (needs `feature = "simd_support"` AND `target_feature = "avx512bw"`;
//     resolved features are alloc/default/os_rng/small_rng/std/std_rng/thread_rng
//     — `simd_support` is off) and `simd-adler32` (needs its `nightly` feature;
//     resolved features are empty). Neither gate can fire.
//
// NOT verified by an actual x86_64 build — this machine is aarch64 and the feature
// is x86-only, so the evidence above is graph-measurement, not a green compile. If
// an x86_64 host ever fails on a missing `stdarch_x86_avx512`, the cause is a NEW
// edge into curve25519-dalek (or `simd_support` being switched on), and the fix is
// to remove that edge rather than to re-add the allowance.
// The frontend's native member client needs the same child-only descriptor API
// as Targo. This shared runtime recipe also governs trustd and their self-tests.
pub(super) const CARGO_TRUST_ALLOW_FEATURES: &str = "min_specialization,specialization,try_trait_v2,try_trait_v2_residual,allocator_ext,trust_process_inherit_fds";

fn trustd_cargo_args() -> Vec<String> {
    locked_cargo_args(&["--bin", "trustd"])
}

fn trustd_tool_build_recipe(
    build_compiler: Compiler,
    output_compiler: Compiler,
    target: TargetSelection,
) -> ToolBuild {
    ToolBuild {
        build_compiler,
        output_compiler,
        target,
        tool: "trustd",
        mode: Mode::ToolTarget,
        path: "crates/trust-coordinator",
        source_type: SourceType::InTree,
        extra_features: Vec::new(),
        allow_features: CARGO_TRUST_ALLOW_FEATURES,
        cargo_args: trustd_cargo_args(),
        artifact_kind: ToolArtifactKind::Binary,
    }
}

fn build_trustd_tool(
    builder: &Builder<'_>,
    build_compiler: Compiler,
    output_compiler: Compiler,
    target: TargetSelection,
) -> ToolBuildResult {
    builder.ensure(trustd_tool_build_recipe(build_compiler, output_compiler, target))
}

/// Builds the same-sysroot coordination daemon required by `targo trust`.
///
/// `Trustd` is an internal dependency step rather than a separately selectable
/// distribution component.  It is shipped inside the `targo-trust` component
/// so installing the frontend cannot produce a present-but-unusable toolchain.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Trustd {
    build_compiler: Compiler,
    target: TargetSelection,
}

impl Trustd {
    pub fn from_build_compiler(build_compiler: Compiler, target: TargetSelection) -> Self {
        Self { build_compiler, target }
    }
}

impl Step for Trustd {
    type Output = ToolBuildResult;

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.std(self.build_compiler, builder.host_target);
        builder.std(self.build_compiler, self.target);

        let target_compiler = builder.compiler(self.build_compiler.stage + 1, self.target);
        let tool_result =
            build_trustd_tool(builder, self.build_compiler, target_compiler, self.target);
        let tool_path =
            copy_bins_to_sysroot(builder, target_compiler, &tool_result.tool_path, &["trustd"]);

        ToolBuildResult {
            tool_path,
            build_compiler: tool_result.build_compiler,
            artifacts: tool_result.artifacts,
        }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("trustd", self.target).built_by(self.build_compiler))
    }
}

impl TCargoTrust {
    /// Returns `TCargoTrust` that will be **compiled** by the passed compiler, for the given
    /// `target`.
    pub fn from_build_compiler(build_compiler: Compiler, target: TargetSelection) -> Self {
        Self { build_compiler, target }
    }

    // Trust: retain the active build-compiler constructor; no caller needs a target adapter.
}

impl CommandLineStep for TCargoTrust {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("targo-trust")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.tool_enabled("targo-trust")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(TCargoTrust {
            build_compiler: get_tool_target_compiler(
                run.builder,
                ToolTargetBuildMode::Build(run.target),
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.std(self.build_compiler, builder.host_target);
        builder.std(self.build_compiler, self.target);

        let target_compiler = builder.compiler(self.build_compiler.stage + 1, self.target);
        let tool_result = builder.ensure(targo_trust_tool_build_recipe(
            self.build_compiler,
            target_compiler,
            self.target,
        ));

        // Keep the runtime daemon coupled to the public frontend at the build
        // graph boundary.  Dist/install reuse this cached step and package both
        // binaries in one component.
        builder.ensure(Trustd::from_build_compiler(self.build_compiler, self.target));

        let tool_path = copy_bins_to_sysroot(
            builder,
            target_compiler,
            &tool_result.tool_path,
            &["targo-trust"],
        );

        ToolBuildResult {
            tool_path,
            build_compiler: tool_result.build_compiler,
            artifacts: tool_result.artifacts,
        }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("targo-trust", self.target).built_by(self.build_compiler))
    }
}

/// Trust: build a native frontend artifact without assembling or changing an SDK.
/// The ordinary `TCargoTrust` step remains the owner of SDK/daemon delivery.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TCargoTrustBuildTool {
    target: TargetSelection,
}

impl CommandLineStep for TCargoTrustBuildTool {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("targo-trust-build-tool")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder
            .version_info()
            .sha()
            .expect("targo-trust-build-tool requires source identity; do not omit git hash");
        run.builder.ensure(Self { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        assert_eq!(
            self.target, builder.host_target,
            "targo-trust-build-tool only supports the native build host"
        );
        // The component origin is observed under the same normal build owner;
        // neither a version label nor this source-only key authorizes a runtime.
        let inputs = if builder.config.dry_run() {
            None
        } else {
            let fresh = ExecutionContext::new(builder.config.exec_ctx().verbosity, false);
            let head = builder.rust_info().info().expect("frontend source must be Git-backed");
            let config = trust_source_identity::config_digest(
                builder.config.config.as_deref(),
                &builder.src,
            );
            let full = trust_source_identity::of_sources(&fresh, &builder.src, &config, head)
                .unwrap_or_else(|error| panic!("cannot capture frontend source inputs: {error}"));
            let runtime = trust_source_identity::frontend_runtime_sources(
                &fresh,
                &builder.src,
                &config,
                head,
            )
            .unwrap_or_else(|error| panic!("cannot capture nonfrontend source inputs: {error}"));
            Some((full.info.sha, runtime, config))
        };
        let compiler = builder.compiler(0, builder.host_target);
        // This exact role uses the current native Cargo and actual snapshot std.
        // Output0 writes only tools-bin. No stage1 compiler, daemon or sysroot is
        // assembled, copied or relabelled, and existing runtime refusals remain.
        let recipe = if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            retained_frontend_tool_build_recipe(compiler, self.target)
        } else {
            targo_trust_tool_build_recipe(compiler, compiler, self.target)
        };
        let result = builder.ensure(recipe);
        if let Some((full, runtime, config)) = inputs {
            let fresh = ExecutionContext::new(builder.config.exec_ctx().verbosity, false);
            let head = builder.rust_info().info().unwrap();
            let after_config = trust_source_identity::config_digest(
                builder.config.config.as_deref(),
                &builder.src,
            );
            assert_eq!(config, after_config, "frontend configuration changed during construction");
            let after =
                trust_source_identity::of_sources(&fresh, &builder.src, &after_config, head)
                    .unwrap_or_else(|error| {
                        panic!("cannot recheck frontend source inputs: {error}")
                    });
            assert_eq!(full, after.info.sha, "frontend source inputs changed during construction");
            let after_runtime = trust_source_identity::frontend_runtime_sources(
                &fresh,
                &builder.src,
                &after_config,
                head,
            )
            .unwrap_or_else(|error| panic!("cannot recheck nonfrontend source inputs: {error}"));
            assert_eq!(
                runtime, after_runtime,
                "nonfrontend source inputs changed during construction"
            );
            // Diagnostic artifact provenance only. No reader can reconstruct a
            // completed/qualified SDK or a live daemon owner from these fields.
            use sha2::Digest as _;
            let mut artifact = fs::File::open(&result.tool_path).unwrap();
            let mut hash = sha2::Sha256::new();
            let artifact_bytes = io::copy(&mut artifact, &mut hash).unwrap();
            let origin = serde_json::json!({
                "schema": "trust.frontend-artifact-origin.v1",
                "scope": "engineering-artifact-only; no runtime, SDK, seed, or proof qualification",
                "build_version_commit": builder.version_info().sha(),
                "observed_source_digest": full,
                "nonfrontend_source_digest": runtime,
                "configuration_digest": config,
                "host": self.target.triple.to_string(),
                "artifact": result.tool_path,
                "artifact_bytes": artifact_bytes,
                "artifact_sha256_observation": format!("{:x}", hash.finalize()),
            });
            let path = result.tool_path.with_extension("component-origin.json");
            let bytes = serde_json::to_vec_pretty(&origin).unwrap();
            let temporary = path.with_extension(format!("json.{}.partial", std::process::id()));
            let publish = || -> io::Result<()> {
                use io::Write as _;
                let mut file =
                    fs::OpenOptions::new().write(true).create_new(true).open(&temporary)?;
                file.write_all(&bytes)?;
                file.sync_all()?;
                fs::rename(&temporary, &path)
            };
            publish().unwrap_or_else(|error| {
                panic!("cannot write frontend component origin {}: {error}", path.display())
            });
        }
        builder.info(&format!(
            "Engineering frontend artifact: {} (source: {}). This is not SDK, runtime, seed, or proof qualification.",
            result.tool_path.display(),
            builder.version_info().sha().unwrap_or("omitted or unavailable"),
        ));
        result
    }
}

/// Represents a built LldWrapper, the `lld-wrapper` tool itself, and a directory
/// containing a build of LLD.
#[derive(Clone)]
pub struct BuiltLldWrapper {
    tool: ToolBuildResult,
    lld_dir: PathBuf,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LldWrapper {
    pub build_compiler: Compiler,
    pub target: TargetSelection,
}

impl LldWrapper {
    /// Returns `LldWrapper` that should be **used** by the passed compiler.
    pub fn for_use_by_compiler(builder: &Builder<'_>, target_compiler: Compiler) -> Self {
        Self {
            build_compiler: get_tool_target_compiler(
                builder,
                ToolTargetBuildMode::Dist(target_compiler),
            ),
            target: target_compiler.host,
        }
    }
}

impl CommandLineStep for LldWrapper {
    type Output = BuiltLldWrapper;

    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/lld-wrapper")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(LldWrapper {
            build_compiler: get_tool_target_compiler(
                run.builder,
                ToolTargetBuildMode::Build(run.target),
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let lld_dir = builder.ensure(llvm::Lld { target: self.target });
        let tool = builder.ensure(ToolBuild {
            build_compiler: self.build_compiler,
            output_compiler: output_compiler_for_tool(self.build_compiler, self.target),
            target: self.target,
            tool: "lld-wrapper",
            mode: Mode::ToolTarget,
            path: "src/tools/lld-wrapper",
            source_type: SourceType::InTree,
            extra_features: Vec::new(),
            allow_features: "",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        BuiltLldWrapper { tool, lld_dir }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("LldWrapper", self.target).built_by(self.build_compiler))
    }
}

pub(crate) fn copy_lld_artifacts(
    builder: &Builder<'_>,
    lld_wrapper: BuiltLldWrapper,
    target_compiler: Compiler,
) {
    let target = target_compiler.host;

    let libdir_bin = builder.sysroot_target_bindir(target_compiler, target);
    t!(fs::create_dir_all(&libdir_bin));

    let src_exe = exe("lld", target);
    let dst_exe = exe("rust-lld", target);
    let source = lld_wrapper.lld_dir.join("bin").join(src_exe);

    builder.copy_link(&source, &libdir_bin.join(&dst_exe), FileType::Executable);
    // The closed native workload profile selects this exact SDK-relative
    // executable. Keep the usual rustlib copy for ordinary compiler callers.
    // Executable copies on Darwin use distinct inodes, so the SDK input
    // validator can retain each original image without a hard-link alias.
    let native_bin = builder.sysroot(target_compiler).join("bin");
    t!(fs::create_dir_all(&native_bin));
    builder.copy_link(&source, &native_bin.join(dst_exe), FileType::Executable);
    let self_contained_lld_dir = libdir_bin.join("gcc-ld");
    t!(fs::create_dir_all(&self_contained_lld_dir));

    for name in LLD_FILE_NAMES {
        builder.copy_link(
            &lld_wrapper.tool.tool_path,
            &self_contained_lld_dir.join(exe(name, target)),
            FileType::Executable,
        );
    }
}

/// Builds the `wasm-component-ld` linker wrapper, which is shipped with rustc to be executed on the
/// host platform where rustc runs.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct WasmComponentLd {
    build_compiler: Compiler,
    target: TargetSelection,
}

impl WasmComponentLd {
    /// Returns `WasmComponentLd` that should be **used** by the passed compiler.
    pub fn for_use_by_compiler(builder: &Builder<'_>, target_compiler: Compiler) -> Self {
        Self {
            build_compiler: get_tool_target_compiler(
                builder,
                ToolTargetBuildMode::Dist(target_compiler),
            ),
            target: target_compiler.host,
        }
    }
}

impl CommandLineStep for WasmComponentLd {
    type Output = ToolBuildResult;

    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/wasm-component-ld")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(WasmComponentLd {
            build_compiler: get_tool_target_compiler(
                run.builder,
                ToolTargetBuildMode::Build(run.target),
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.ensure(ToolBuild {
            build_compiler: self.build_compiler,
            output_compiler: output_compiler_for_tool(self.build_compiler, self.target),
            target: self.target,
            tool: "wasm-component-ld",
            mode: Mode::ToolTarget,
            path: "src/tools/wasm-component-ld",
            source_type: SourceType::InTree,
            extra_features: vec![],
            allow_features: "",
            cargo_args: vec![],
            artifact_kind: ToolArtifactKind::Binary,
        })
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("WasmComponentLd", self.target).built_by(self.build_compiler))
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct RustAnalyzer {
    compilers: RustcPrivateCompilers,
}

impl RustAnalyzer {
    pub fn from_compilers(compilers: RustcPrivateCompilers) -> Self {
        Self { compilers }
    }
}

impl RustAnalyzer {
    pub const ALLOW_FEATURES: &'static str = "rustc_private,proc_macro_internals,proc_macro_diagnostic,proc_macro_span,proc_macro_span_shrink,proc_macro_def_site,new_zeroed_alloc";
}

impl CommandLineStep for RustAnalyzer {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/rust-analyzer")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        // Trust: user-facing `tools = [...]` alias is `trust-analyzer`
        // (commit d3d70a6ab1). `tool_enabled` does a direct lookup against
        // that user-facing set, so the inherited `rust-analyzer` spelling
        // would never match.
        builder.tool_enabled("trust-analyzer")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RustAnalyzer {
            compilers: RustcPrivateCompilers::new(run.builder, run.builder.top_stage, run.target),
        });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        let build_compiler = self.compilers.build_compiler;
        let target = self.compilers.target();
        let tool_result = builder.ensure(ToolBuild {
            build_compiler,
            output_compiler: self.compilers.target_compiler,
            target,
            tool: "rust-analyzer",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/rust-analyzer",
            extra_features: vec!["in-rust-tree".to_owned()],
            source_type: SourceType::InTree,
            allow_features: RustAnalyzer::ALLOW_FEATURES,
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });

        let bindir = builder.sysroot(self.compilers.target_compiler).join("bin");
        let tool_path = install_rustc_private_tool_bins(
            builder,
            self.compilers.target_compiler,
            &bindir,
            &tool_result.tool_path,
            &["trust-analyzer"],
        );

        ToolBuildResult {
            tool_path,
            build_compiler: tool_result.build_compiler,
            artifacts: tool_result.artifacts,
        }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(
            StepMetadata::build("trust-analyzer", self.compilers.target())
                .built_by(self.compilers.build_compiler),
        )
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct RustAnalyzerProcMacroSrv {
    compilers: RustcPrivateCompilers,
}

impl RustAnalyzerProcMacroSrv {
    pub fn from_compilers(compilers: RustcPrivateCompilers) -> Self {
        Self { compilers }
    }
}

impl CommandLineStep for RustAnalyzerProcMacroSrv {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        // Allow building `rust-analyzer-proc-macro-srv` both as part of the `rust-analyzer` and as a stand-alone tool.
        // FIXME(Zalathar): Should we stop registering "src/tools/rust-analyzer" here?
        run.path("src/tools/rust-analyzer").path_with_alias(
            "src/tools/rust-analyzer/crates/proc-macro-srv-cli",
            "trust-analyzer-proc-macro-srv",
        )
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        // Trust: per commit d3d70a6ab1 the user-facing tool-settings list
        // is keyed on Trust-canonical aliases only. `trust-analyzer` (the
        // umbrella for the LSP) and `trust-analyzer-proc-macro-srv` (the
        // dedicated alias) each enable the proc-macro server build; the
        // inherited `rust-analyzer-proc-macro-srv` spelling is no longer
        // accepted in `tools = [...]`.
        builder.tool_enabled("trust-analyzer")
            || builder.tool_enabled("trust-analyzer-proc-macro-srv")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RustAnalyzerProcMacroSrv {
            compilers: RustcPrivateCompilers::new(run.builder, run.builder.top_stage, run.target),
        });
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let tool_result = builder.ensure(ToolBuild {
            build_compiler: self.compilers.build_compiler,
            output_compiler: self.compilers.target_compiler,
            target: self.compilers.target(),
            tool: "rust-analyzer-proc-macro-srv",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/rust-analyzer/crates/proc-macro-srv-cli",
            extra_features: vec!["in-rust-tree".to_owned()],
            source_type: SourceType::InTree,
            allow_features: RustAnalyzer::ALLOW_FEATURES,
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });

        // Copy the upstream-built helper under the Trust-owned public name ONLY.
        // The retired stock `rust-analyzer-proc-macro-srv` alias must not ship:
        // the daily-driver readiness surface (`FORBIDDEN_TRUST_PUBLIC_LIBEXEC_NAMES`)
        // rejects it, flipping `targo trust doctor` to `needs_attention`. This
        // step was the alias's actual producer — it runs after the per-tool and
        // final assembly cleanups, so any stock copy made here survived them.
        let libexec_path = builder.sysroot(self.compilers.target_compiler).join("libexec");
        t!(fs::create_dir_all(&libexec_path));
        let installed = libexec_path
            .join(exe("trust-analyzer-proc-macro-srv", self.compilers.target_compiler.host));
        builder.copy_link(&tool_result.tool_path, &installed, FileType::Executable);
        validate_installed_rustc_private_tool(builder, self.compilers.target_compiler, &installed);
        let stock_proc_macro_srv = libexec_path
            .join(exe("rust-analyzer-proc-macro-srv", self.compilers.target_compiler.host));
        t!(remove_retired_proc_macro_srv_alias(&stock_proc_macro_srv));

        tool_result
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(
            StepMetadata::build("trust-analyzer-proc-macro-srv", self.compilers.target())
                .built_by(self.compilers.build_compiler),
        )
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LlvmBitcodeLinker {
    build_compiler: Compiler,
    target: TargetSelection,
}

impl LlvmBitcodeLinker {
    /// Returns `LlvmBitcodeLinker` that will be **compiled** by the passed compiler, for the given
    /// `target`.
    pub fn from_build_compiler(build_compiler: Compiler, target: TargetSelection) -> Self {
        Self { build_compiler, target }
    }

    /// Returns `LlvmBitcodeLinker` that should be **used** by the passed compiler.
    pub fn from_target_compiler(builder: &Builder<'_>, target_compiler: Compiler) -> Self {
        Self {
            build_compiler: get_tool_target_compiler(
                builder,
                ToolTargetBuildMode::Dist(target_compiler),
            ),
            target: target_compiler.host,
        }
    }

    /// Return a compiler that is able to build this tool for the given `target`.
    pub fn get_build_compiler_for_target(
        builder: &Builder<'_>,
        target: TargetSelection,
    ) -> Compiler {
        get_tool_target_compiler(builder, ToolTargetBuildMode::Build(target))
    }
}

impl CommandLineStep for LlvmBitcodeLinker {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/llvm-bitcode-linker")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.tool_enabled("llvm-bitcode-linker")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(LlvmBitcodeLinker {
            build_compiler: Self::get_build_compiler_for_target(run.builder, run.target),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.ensure(ToolBuild {
            build_compiler: self.build_compiler,
            output_compiler: output_compiler_for_tool(self.build_compiler, self.target),
            target: self.target,
            tool: "llvm-bitcode-linker",
            mode: Mode::ToolTarget,
            path: "src/tools/llvm-bitcode-linker",
            source_type: SourceType::InTree,
            extra_features: vec![],
            allow_features: "",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        })
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("LlvmBitcodeLinker", self.target).built_by(self.build_compiler))
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LibcxxVersionTool {
    pub target: TargetSelection,
}

#[expect(dead_code)]
#[derive(Debug, Clone)]
pub enum LibcxxVersion {
    Gnu(usize),
    Llvm(usize),
}

impl Step for LibcxxVersionTool {
    type Output = LibcxxVersion;

    fn run(self, builder: &Builder<'_>) -> LibcxxVersion {
        let out_dir = builder.out.join(self.target.to_string()).join("libcxx-version");
        let executable = out_dir.join(exe("libcxx-version", self.target));

        // This is a sanity-check specific step, which means it is frequently called (when using
        // CI LLVM), and compiling `src/tools/libcxx-version/main.cpp` at the beginning of the bootstrap
        // invocation adds a fair amount of overhead to the process (see https://github.com/rust-lang/rust/issues/126423).
        // Therefore, we want to avoid recompiling this file unnecessarily.
        if !executable.exists() {
            if !out_dir.exists() {
                t!(fs::create_dir_all(&out_dir));
            }

            let compiler = builder.cxx(self.target).unwrap();
            let mut cmd = command(compiler);

            cmd.arg("-o")
                .arg(&executable)
                .arg(builder.src.join("src/tools/libcxx-version/main.cpp"));

            cmd.run(builder);

            if !executable.exists() {
                panic!("Something went wrong. {} is not present", executable.display());
            }
        }

        let version_output = command(executable).run_capture_stdout(builder).stdout();

        let version_str = version_output.split_once("version:").unwrap().1;
        let version = version_str.trim().parse::<usize>().unwrap();

        if version_output.starts_with("libstdc++") {
            LibcxxVersion::Gnu(version)
        } else if version_output.starts_with("libc++") {
            LibcxxVersion::Llvm(version)
        } else {
            panic!("Coudln't recognize the standard library version.");
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct BuildManifest {
    compiler: Compiler,
    target: TargetSelection,
}

impl BuildManifest {
    pub fn new(builder: &Builder<'_>, target: TargetSelection) -> Self {
        BuildManifest { compiler: builder.compiler(1, builder.config.host_target), target }
    }
}

impl CommandLineStep for BuildManifest {
    type Output = ToolBuildResult;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/build-manifest")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(BuildManifest::new(run.builder, run.target));
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        // Building with the beta compiler will produce a broken build-manifest that doesn't support
        // recently stabilized targets/hosts.
        assert!(self.compiler.stage != 0);
        builder.ensure(ToolBuild {
            build_compiler: self.compiler,
            output_compiler: output_compiler_for_tool(self.compiler, self.target),
            target: self.target,
            tool: "build-manifest",
            mode: Mode::ToolStd,
            path: "src/tools/build-manifest",
            source_type: SourceType::InTree,
            extra_features: vec![],
            allow_features: "",
            cargo_args: vec![],
            artifact_kind: ToolArtifactKind::Binary,
        })
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("build-manifest", self.target).built_by(self.compiler))
    }
}

/// Represents which compilers are involved in the compilation of a tool
/// that depends on compiler internals (`rustc_private`).
/// Their compilation looks like this:
///
/// - `build_compiler` (stage N-1) builds `target_compiler` (stage N) to produce .rlibs
///     - These .rlibs are copied into the sysroot of `build_compiler`
/// - `build_compiler` (stage N-1) builds `<tool>` (stage N)
///     - `<tool>` links to .rlibs from `target_compiler`
///
/// Eventually, this could also be used for .rmetas and check builds, but so far we only deal with
/// normal builds here.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct RustcPrivateCompilers {
    /// Compiler that builds the tool and that builds `target_compiler`.
    build_compiler: Compiler,
    /// Compiler to which .rlib artifacts the tool links to.
    /// The host target of this compiler corresponds to the target of the tool.
    target_compiler: Compiler,
}

impl RustcPrivateCompilers {
    /// Create compilers for a `rustc_private` tool with the given `stage` and for the given
    /// `target`.
    pub fn new(builder: &Builder<'_>, stage: u32, target: TargetSelection) -> Self {
        let build_compiler = Self::build_compiler_from_stage(builder, stage);

        // This is the compiler we'll link to
        // FIXME: make 100% sure that `target_compiler` was indeed built with `build_compiler`...
        let target_compiler = builder.compiler(build_compiler.stage + 1, target);

        Self { build_compiler, target_compiler }
    }

    /// Create rustc tool compilers from the build compiler.
    pub fn from_build_compiler(
        builder: &Builder<'_>,
        build_compiler: Compiler,
        target: TargetSelection,
    ) -> Self {
        let target_compiler = builder.compiler(build_compiler.stage + 1, target);
        Self { build_compiler, target_compiler }
    }

    /// Create rustc tool compilers from the target compiler.
    pub fn from_target_compiler(builder: &Builder<'_>, target_compiler: Compiler) -> Self {
        Self {
            build_compiler: Self::build_compiler_from_stage(builder, target_compiler.stage),
            target_compiler,
        }
    }

    fn build_compiler_from_stage(builder: &Builder<'_>, stage: u32) -> Compiler {
        assert!(stage > 0);

        if builder.download_rustc() && stage == 1 {
            // We shouldn't drop to stage0 compiler when using CI rustc.
            builder.compiler(1, builder.config.host_target)
        } else {
            builder.compiler(stage - 1, builder.config.host_target)
        }
    }

    pub fn build_compiler(&self) -> Compiler {
        self.build_compiler
    }

    pub fn target_compiler(&self) -> Compiler {
        self.target_compiler
    }

    /// Target of the tool being compiled
    pub fn target(&self) -> TargetSelection {
        self.target_compiler.host
    }
}

/// Creates a step that builds an extended `Mode::ToolRustcPrivate` tool
/// and installs it into the sysroot of a corresponding compiler.
macro_rules! tool_rustc_extended {
    (
        $name:ident {
            path: $path:expr,
            tool_name: $tool_name:expr,
            stable: $stable:expr
            $( , add_bins_to_sysroot: $add_bins_to_sysroot:expr )?
            $( , add_features: $add_features:expr )?
            $( , cargo_args: $cargo_args:expr )?
            $( , )?
        }
    ) => {
        #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        pub struct $name {
            compilers: RustcPrivateCompilers,
        }

        impl $name {
            #[allow(dead_code)]
            pub fn from_compilers(compilers: RustcPrivateCompilers) -> Self {
                Self {
                    compilers,
                }
            }
        }

        impl CommandLineStep for $name {
            type Output = ToolBuildResult;
            const IS_HOST: bool = true;

            fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
                should_run_extended_rustc_tool(
                    run,
                    $path,
                )
            }

            fn is_default_step(builder: &Builder<'_>) -> bool {
                extended_rustc_tool_is_default_step(
                    builder,
                    $tool_name,
                    $stable,
                )
            }

            fn make_run(run: RunConfig<'_>) {
                run.builder.ensure($name {
                    compilers: RustcPrivateCompilers::new(run.builder, run.builder.top_stage, run.target),
                });
            }

            fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
                let Self { compilers } = self;
                build_extended_rustc_tool(
                    builder,
                    compilers,
                    $tool_name,
                    $path,
                    None $( .or(Some(&$add_bins_to_sysroot)) )?,
                    None $( .or(Some($add_features)) )?,
                    None $( .or(Some($cargo_args)) )?,
                )
            }

            fn metadata(&self) -> Option<StepMetadata> {
                Some(
                    StepMetadata::build($tool_name, self.compilers.target())
                        .built_by(self.compilers.build_compiler)
                )
            }
        }
    }
}

fn should_run_extended_rustc_tool<'a>(run: ShouldRun<'a>, path: &'static str) -> ShouldRun<'a> {
    run.path(path)
}

pub(crate) fn extended_rustc_tool_is_default_step(
    builder: &Builder<'_>,
    tool_name: &'static str,
    stable: bool,
) -> bool {
    extended_rustc_tool_is_default_step_for_config(
        &builder.config,
        builder.sess.unstable_features(),
        tool_name,
        stable,
    )
}

fn extended_rustc_tool_is_default_step_for_config(
    config: &Config,
    unstable_features: bool,
    tool_name: &'static str,
    stable: bool,
) -> bool {
    extended_rustc_tool_is_default_step_for_tool_settings(
        config.extended,
        config.tools.as_ref(),
        unstable_features,
        tool_name,
        stable,
    )
}

fn extended_rustc_tool_is_default_step_for_tool_settings(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
    unstable_features: bool,
    tool_name: &'static str,
    stable: bool,
) -> bool {
    extended
        && tools.map_or(
            // By default, on nightly/dev enable all tools, else only build stable tools.
            stable || unstable_features,
            // If `tools` is set, search list for this tool.
            |tools| tools.iter().any(|tool| tool_matches_config_entry(tool, tool_name)),
        )
}

fn tool_enabled_for_tool_settings(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
    tool: &str,
) -> bool {
    if !extended {
        return false;
    }
    match tools {
        Some(set) => set.iter().any(|entry| tool_config_entry_selects_user_tool(entry, tool)),
        None => true,
    }
}

pub(crate) fn tool_config_entry_selects_user_tool(config_tool: &str, tool: &str) -> bool {
    // Trust: the left-hand spellings are `bootstrap.toml` `[build] tools`
    // entries an upstream-shaped config may still carry. They SELECT the Trust
    // tool; they never name an artifact (docs/trust-naming.md, "What is still
    // spelled `cargo`").
    match config_tool {
        "cargo" => tool == "targo",
        "cargo-trust" => tool == "targo-trust",
        "rustdoc" => tool == "trustdoc",
        "rustfmt" => tool == "trustfmt",
        "cargo-fmt" | "targo-fmt" => tool == "trustfmt" || tool == "targo-fmt",
        "clippy" | "cargo-clippy" | "clippy-driver" => tool == "tippy",
        "targo-tippy" | "tippy-driver" => tool == "tippy",
        "rust-analyzer" => tool == "trust-analyzer",
        "miri" => tool == "trust-miri",
        "cargo-miri" => tool == "targo-miri",
        "analysis" | "rust-analysis" => tool == "trust-analysis",
        "llvm-tools" => tool == "trust-llvm-tools",
        _ => config_tool == tool,
    }
}

fn tool_matches_config_entry(config_tool: &str, tool_name: &str) -> bool {
    // Trust: user-facing tool-settings aliases (LHS) are Trust-canonical. The
    // RHS `tool_name` stays as the upstream cargo source-binary name, because
    // the same identifier is passed to `cargo --bin` to select which binary
    // to build (see `build_extended_rustc_tool`); rebranding the RHS would
    // make `cargo build` look for a non-existent `--bin tippy` target.
    // Finished sysroots install only the Trust public executable names. Rust
    // spellings remain accepted as source-build compatibility selectors.
    match config_tool {
        "tippy" | "targo-tippy" | "tippy-driver" | "clippy" | "clippy-driver" | "cargo-clippy" => {
            matches!(tool_name, "clippy-driver" | "cargo-clippy")
        }
        "trust-miri" | "miri" | "cargo-miri" => matches!(tool_name, "miri" | "cargo-miri"),
        "trustfmt" | "targo-fmt" | "rustfmt" | "cargo-fmt" => {
            matches!(tool_name, "rustfmt" | "cargo-fmt")
        }
        "trust-analyzer" | "rust-analyzer" => tool_name == "rust-analyzer",
        "trust-llvm-tools" | "llvm-tools" => tool_name == "llvm-tools",
        x => tool_name == x,
    }
}

fn build_extended_rustc_tool(
    builder: &Builder<'_>,
    compilers: RustcPrivateCompilers,
    tool_name: &'static str,
    path: &'static str,
    add_bins_to_sysroot: Option<&[&str]>,
    // Trust: per-tool cargo feature hook (tippy-driver/miri jemalloc), lost
    // when upstream simplified this macro; restored by the 1.101 port.
    add_features: Option<fn(&Builder<'_>, TargetSelection, &mut Vec<String>)>,
    cargo_args: Option<&[&'static str]>,
) -> ToolBuildResult {
    let target = compilers.target();
    let mut extra_features = Vec::new();
    if let Some(func) = add_features {
        func(builder, target, &mut extra_features);
    }

    let build_compiler = compilers.build_compiler;
    let ToolBuildResult { tool_path, artifacts, .. } = builder.ensure(ToolBuild {
        build_compiler,
        output_compiler: compilers.target_compiler,
        target,
        tool: tool_name,
        mode: Mode::ToolRustcPrivate,
        path,
        extra_features,
        source_type: SourceType::InTree,
        allow_features: "",
        cargo_args: cargo_args.unwrap_or_default().iter().map(|s| String::from(*s)).collect(),
        artifact_kind: ToolArtifactKind::Binary,
    });

    let target_compiler = compilers.target_compiler;
    if let Some(add_bins_to_sysroot) = add_bins_to_sysroot
        && !add_bins_to_sysroot.is_empty()
    {
        let bindir = builder.sysroot(target_compiler).join("bin");
        let path = install_rustc_private_tool_bins(
            builder,
            target_compiler,
            &bindir,
            &tool_path,
            add_bins_to_sysroot,
        );
        ToolBuildResult { tool_path: path, build_compiler, artifacts }
    } else {
        ToolBuildResult { tool_path, build_compiler, artifacts }
    }
}

tool_rustc_extended!(Cargofmt {
    path: "src/tools/trustfmt",
    tool_name: "cargo-fmt",
    stable: true,
    add_bins_to_sysroot: ["targo-fmt"],
    cargo_args: CARGOFMT_CARGO_ARGS
});
tool_rustc_extended!(CargoClippy {
    path: "src/tools/tippy",
    tool_name: "cargo-clippy",
    stable: true,
    add_bins_to_sysroot: ["tippy", "targo-tippy"],
    cargo_args: CARGO_CLIPPY_CARGO_ARGS
});

/// Features that alter the shipped Tippy driver binary.
///
/// Keep this shared with `test::Clippy`: otherwise a configured distribution
/// can build a jemalloc-enabled public driver while CI exercises a different
/// no-feature test binary.
pub(super) fn tippy_driver_features(builder: &Builder<'_>, target: TargetSelection) -> Vec<String> {
    tippy_driver_features_for_jemalloc(builder.config.allocator(target) == Allocator::Jemalloc)
}

fn tippy_driver_features_for_jemalloc(jemalloc: bool) -> Vec<String> {
    if jemalloc { vec!["jemalloc".to_string()] } else { Vec::new() }
}

tool_rustc_extended!(Clippy {
    path: "src/tools/tippy",
    tool_name: "clippy-driver",
    stable: true,
    add_bins_to_sysroot: ["tippy-driver"],
    add_features: |builder, target, features| {
        features.extend(tippy_driver_features(builder, target));
    },
    cargo_args: CLIPPY_DRIVER_CARGO_ARGS
});
tool_rustc_extended!(Miri {
    path: "src/tools/miri",
    tool_name: "miri",
    stable: false,
    add_bins_to_sysroot: ["trust-miri"],
    add_features: |builder, target, features| {
        if builder.config.allocator(target) == Allocator::Jemalloc {
            features.push("jemalloc".to_string());
        }
    },
    // Always compile also tests when building miri. Otherwise feature unification can cause rebuilds between building and testing miri.
    cargo_args: &["--all-targets"],
});
tool_rustc_extended!(CargoMiri {
    path: "src/tools/miri/cargo-miri",
    tool_name: "cargo-miri",
    stable: false,
    add_bins_to_sysroot: ["targo-miri"]
});
tool_rustc_extended!(Rustfmt {
    path: "src/tools/trustfmt",
    tool_name: "rustfmt",
    stable: true,
    add_bins_to_sysroot: ["trustfmt"],
    cargo_args: RUSTFMT_CARGO_ARGS
});

pub const TEST_FLOAT_PARSE_ALLOW_FEATURES: &str = "f16,cfg_target_has_reliable_f16_f128";

#[cfg(test)]
mod tests;

impl Builder<'_> {
    /// Gets a `BootstrapCommand` which is ready to run `tool` in `stage` built for
    /// `host`.
    ///
    /// This also ensures that the given tool is built (using [`ToolBuild`]).
    pub(crate) fn tool_cmd(&self, tool: Tool) -> BootstrapCommand {
        self.bootstrap_tool_command(self.tool_exe(tool))
    }

    // Trust: reuse the ordinary host-tool runtime closure and ToolBuild cache.
    pub(crate) fn vf5_resource_tool_cmd(&self) -> BootstrapCommand {
        let result = self.ensure(Vf5ResourceTool);
        self.bootstrap_tool_command(result.tool_path)
    }

    fn bootstrap_tool_command(&self, tool: PathBuf) -> BootstrapCommand {
        let mut cmd = command(tool);
        let compiler = self.compiler(0, self.config.host_target);
        let host = &compiler.host;
        // Prepares the `cmd` provided to be able to run the `compiler` provided.
        //
        // Notably this munges the dynamic library lookup path to point to the
        // right location to run `compiler`.
        let mut lib_paths: Vec<PathBuf> = discover_out_dirs_with_dylibs(
            self.cargo_out_for_input(
                compiler,
                Mode::ToolBootstrap,
                *host,
                self.cargo_input(Mode::ToolBootstrap),
            )
            .join("build"),
        );

        // On MSVC a tool may invoke a C compiler (e.g., compiletest in run-make
        // mode) and that C compiler may need some extra PATH modification. Do
        // so here.
        if compiler.host.is_msvc() {
            let curpaths = env::var_os("PATH").unwrap_or_default();
            let curpaths = env::split_paths(&curpaths).collect::<Vec<_>>();
            for (k, v) in self.cc[&compiler.host].env() {
                if k != "PATH" {
                    continue;
                }
                for path in env::split_paths(v) {
                    if !curpaths.contains(&path) {
                        lib_paths.push(path);
                    }
                }
            }
        }

        add_dylib_path(lib_paths, &mut cmd);

        // Provide a RUSTC for this command to use.
        cmd.env("RUSTC", &self.initial_rustc);

        cmd
    }
}

/// Gets all of the `out` dirs in a given Cargo `build-dir/<profile>/build` dir.
fn discover_out_dirs_with_dylibs(dir: PathBuf) -> Vec<PathBuf> {
    if !dir.exists() {
        return Vec::new();
    }
    let read_dir = |path: &Path| path.read_dir().ok().into_iter().flatten().filter_map(Result::ok);
    let has_dylib = |path: &Path| {
        read_dir(path)
            .any(|e| e.path().extension().is_some_and(|ext| ext == std::env::consts::DLL_EXTENSION))
    };
    dir.read_dir()
        .unwrap_or_else(|e| panic!("Couldn't read {}: {}", dir.display(), e))
        .map(|e| e.unwrap())
        .flat_map(|e| read_dir(&e.path()))
        .flat_map(|e| read_dir(&e.path()))
        .map(|e| e.path())
        .filter(|path| path.ends_with("out") && has_dylib(path))
        .collect::<Vec<_>>()
}
