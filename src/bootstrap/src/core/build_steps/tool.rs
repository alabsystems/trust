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

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::{env, fs, io};

use crate::core::build_steps::compile::is_lto_stage;
use crate::core::build_steps::{compile, llvm};
use crate::core::builder;
use crate::core::builder::{
    Builder, Cargo as CargoCommand, RunConfig, ShouldRun, Step, StepMetadata, cargo_profile_var,
};
use crate::core::config::{Config, DebuginfoLevel, RustcLto, TargetSelection};
use crate::utils::exec::{BootstrapCommand, command};
use crate::utils::helpers::{add_dylib_path, dylib_path_var, exe, t};
use crate::{Compiler, FileType, Kind, Mode};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum SourceType {
    InTree,
    Submodule,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ToolArtifactKind {
    Binary,
    Library,
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
}

impl Step for ToolBuild {
    type Output = ToolBuildResult;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.never()
    }

    /// Builds a tool in `src/tools`
    ///
    /// This will build the specified tool with the specified `host` compiler in
    /// `stage` into the normal cargo output directory.
    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        let target = self.target;
        let mut tool = self.tool;
        let path = self.path;

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

        let mut cargo = prepare_tool_cargo(
            builder,
            self.build_compiler,
            self.mode,
            target,
            Kind::Build,
            path,
            self.source_type,
            &self.extra_features,
        );
        if self.mode == Mode::ToolRustcPrivate {
            add_rustc_private_tool_metadata_search_path(
                builder,
                &mut cargo,
                self.output_compiler,
                target,
            );
        }

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

        if !self.allow_features.is_empty() {
            cargo.allow_features(self.allow_features);
        }

        cargo.args(self.cargo_args);

        let _guard =
            builder.msg(Kind::Build, self.tool, self.mode, self.build_compiler, self.target);

        // we check this below
        let build_success = compile::stream_cargo(builder, cargo, vec![], &mut |_| {});

        if !build_success {
            crate::exit!(1);
        } else {
            // HACK(#82501): on Windows, the tools directory gets added to PATH when running tests, and
            // compiletest confuses HTML tidy with the in-tree tidy. Name the in-tree tidy something
            // different so the problem doesn't come up.
            if tool == "tidy" {
                tool = "rust-tidy";
            }
            let tool_path = match self.artifact_kind {
                ToolArtifactKind::Binary => copy_link_tool_bin(
                    builder,
                    self.output_compiler,
                    self.target,
                    self.mode,
                    self.build_compiler,
                    tool,
                ),
                ToolArtifactKind::Library => builder
                    .cargo_out(self.build_compiler, self.mode, self.target)
                    .join(format!("lib{tool}.rlib")),
            };

            ToolBuildResult { tool_path, build_compiler: self.build_compiler }
        }
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
    let mut cargo = builder::Cargo::new(builder, compiler, mode, source_type, target, cmd_kind);

    let path = PathBuf::from(path);
    let dir = builder.src.join(&path);
    cargo.arg("--manifest-path").arg(dir.join("Cargo.toml"));

    let mut features = extra_features.to_vec();
    if builder.build.config.cargo_native_static {
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

    // CFG_RELEASE is needed by rustfmt (and possibly other tools) which
    // import rustc-ap-rustc_attr which requires this to be set for the
    // `#[cfg(version(...))]` attribute.
    cargo.env("CFG_RELEASE", builder.rust_release());
    cargo.env("CFG_RELEASE_CHANNEL", &builder.config.channel);
    cargo.env("CFG_VERSION", builder.rust_version());
    // Trust: the product version, distinct from the rustc-protocol one above.
    cargo.env("CFG_TRUST_VERSION", builder.trust_version());
    cargo.env("CFG_RELEASE_NUM", &builder.version);
    cargo.env("DOC_RUST_LANG_ORG_CHANNEL", builder.doc_rust_lang_org_channel());

    if let Some(ref ver_date) = builder.rust_info().commit_date() {
        cargo.env("CFG_VER_DATE", ver_date);
    }

    if let Some(ref ver_hash) = builder.rust_info().sha() {
        cargo.env("CFG_VER_HASH", ver_hash);
    }

    if let Some(description) = &builder.config.description {
        cargo.env("CFG_VER_DESCRIPTION", description);
    }

    // Targo is vendored in the Trust monorepo, so its version tuple must come
    // from the single root identity captured during bootstrap configuration.
    // Other tools may still be independently versioned subrepositories.
    let info = if path == Path::new("src/tools/targo") {
        builder.cargo_info.clone()
    } else {
        builder.config.git_info(builder.config.omit_git_hash, &dir)
    };
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

fn add_rustc_private_tool_metadata_search_path(
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
) -> PathBuf {
    let cargo_out = builder.cargo_out(build_compiler, mode, target).join(exe(name, target));
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
    if target_compiler.host != builder.build.host_target {
        // Cross-host binaries are not runnable by bootstrap. Do not probe
        // them with the build compiler's libraries: that would be a silent,
        // incoherent fallback. Their content-bound private-sysroot identity
        // still applies at build time.
        builder.info(&format!(
            "Skipping runtime coherence probe for cross-compiled rustc-private tool `{}` \
             (tool host {}, build host {})",
            binary.display(),
            target_compiler.host,
            builder.build.host_target,
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
    restored_sysroot_bins_for_config(&builder.config, builder.build.unstable_features())
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

pub(crate) fn ensure_default_verifier_tool_bins(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    sysroot: &Path,
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
    let build_compiler =
        get_tool_target_compiler(builder, ToolTargetBuildMode::Dist(target_compiler));

    // Reaching this point means at least one member of the verifier surface is
    // enabled. Install both frontend binaries as a unit: staging solver
    // batteries without the canonical `targo trust` entry point strands those
    // batteries in the sysroot, while staging only one half of the frontend
    // produces a present-but-unusable command.
    {
        builder.build.require_submodule("src/tools/targo", None);
        let cargo = builder.ensure(ToolBuild {
            build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "cargo",
            mode: Mode::ToolTarget,
            path: "src/tools/targo",
            source_type: SourceType::Submodule,
            extra_features: Vec::new(),
            allow_features: "min_specialization,specialization",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_bin(builder, &cargo.tool_path, "targo");
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
    if default_source_solver_enabled(extended, tools, ay_source_present) {
        // `ay` — the core solver — installs whenever its in-tree source is
        // present. Guarding on the manifest keeps a bare checkout (no
        // first-party sources) building instead of hard-failing when the block
        // is reached via `targo-trust`/`tools` without the `ay` source.
        if ay_source_present {
            let ay = builder.ensure(ToolBuild {
                build_compiler,
                output_compiler: target_compiler,
                target,
                tool: "ay",
                mode: Mode::ToolTarget,
                path: "first-party/ay/crates/ay",
                source_type: SourceType::InTree,
                extra_features: Vec::new(),
                allow_features: "",
                cargo_args: ay_bootstrap_cargo_args(&builder.src),
                artifact_kind: ToolArtifactKind::Binary,
            });
            install_bin(builder, &ay.tool_path, "ay");
        }

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
        let backend_allow_features = "min_specialization,specialization";
        if l2_backend_enabled(tools, "ty")
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
            // `extra_features` stays empty deliberately: the Lean->TrustIr leg
            // (`clean compile --emit trustir`, and the `--emit obj` handoff to
            // trust-cg) lives behind clean's `trust-ir-backend` feature, whose
            // closure reaches the trust-ir and trust-cg siblings. Turning it on
            // is not a one-line change here — it needs `first-party/clean`'s
            // own lockfile to describe that closure at the currently pinned
            // sibling revisions, and `--locked` is not negotiable for a
            // reproducible, credential-free bootstrap.
            let clean = builder.ensure(ToolBuild {
                build_compiler,
                output_compiler: target_compiler,
                target,
                tool: "clean",
                mode: Mode::ToolTarget,
                path: "first-party/clean/crates/clean",
                source_type: SourceType::InTree,
                extra_features: Vec::new(),
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

fn restored_sysroot_bins_for_tool_settings(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
    unstable_features: bool,
    ay_source_present: bool,
) -> Vec<(&'static str, &'static str)> {
    let mut bins = Vec::new();

    if tool_enabled_for_tool_settings(extended, tools, "trustdoc") {
        bins.push(("rustdoc_tool_binary", "trustdoc"));
    }

    // The public frontend is one unit. Any enabled verifier-surface member
    // restores both halves (and the daemon used by `targo trust`) so a
    // batteries-on sysroot always has a usable entry point.
    if default_verifier_tool_bins_enabled(extended, tools, ay_source_present) {
        bins.push(("cargo", "targo"));
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
    // Trust: the toolchain ships Trust-branded command names ONLY. The single
    // retained upstream-compat alias emitted here is `cargo` — rustup refuses to
    // register a toolchain whose bin/ lacks a `cargo` entrypoint, and `cargo
    // +trust` must resolve. (The matching `rustc` name is materialized on a
    // separate path: `materialize_local_compiler_aliases` / `Assemble`.) Every
    // other stock secondary name — rustdoc, cargo-trust, cargo-clippy,
    // clippy-driver, cargo-fmt, rustfmt, rust-analyzer, cargo-miri, miri — is
    // intentionally NOT materialized. This stops those names at the source (the
    // root-cause replacement for the former scripts/purge-stock-names.sh, which
    // deleted them post-build). Note: `rustdoc` also had a *second* producer,
    // the Rustdoc step's `bin_rustdoc` closure, fixed in tandem.
    match src_name {
        "cargo" => Some("cargo"),
        _ => None,
    }
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

fn owned_cargo_args(args: &[&str]) -> Vec<String> {
    args.iter().map(|arg| (*arg).to_string()).collect()
}

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
    // A linked stage2 sysroot is a user-facing toolchain. Rustc-private tools
    // installed into that sysroot must link against that same sysroot's
    // compiler libraries; otherwise their rpath points at stage2/lib while the
    // binary still expects stage1 hashes.
    let compilers =
        RustcPrivateCompilers::from_build_and_target_compiler(target_compiler, target_compiler);
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
    let install_private_bins = |builder: &Builder<'_>, tool_path: &Path, bin_names: &[&str]| {
        install_rustc_private_tool_bins(builder, target_compiler, &bindir, tool_path, bin_names);
    };

    if tool_enabled_for_tool_settings(
        builder.config.extended,
        builder.config.tools.as_ref(),
        "trustdoc",
    ) {
        let mut rustdoc_features = Vec::new();
        if builder.config.jemalloc(target) {
            rustdoc_features.push("jemalloc".to_string());
        }
        let rustdoc = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "rustdoc_tool_binary",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/trustdoc",
            source_type: SourceType::InTree,
            extra_features: rustdoc_features,
            allow_features: "",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        if builder.config.rust_debuginfo_level_tools == DebuginfoLevel::None {
            compile::strip_debug(builder, target, &rustdoc.tool_path);
        }
        install_private_bins(builder, &rustdoc.tool_path, &["trustdoc"]);
    }

    if targo_runtime_enabled(builder.config.extended, builder.config.tools.as_ref()) {
        builder.build.require_submodule("src/tools/targo", None);
        let cargo = builder.ensure(ToolBuild {
            build_compiler: get_tool_target_compiler(
                builder,
                ToolTargetBuildMode::Dist(target_compiler),
            ),
            output_compiler: target_compiler,
            target,
            tool: "cargo",
            mode: Mode::ToolTarget,
            path: "src/tools/targo",
            source_type: SourceType::Submodule,
            extra_features: Vec::new(),
            allow_features: "min_specialization,specialization",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_bins(builder, &cargo.tool_path, &["targo"]);
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
    if extended_rustc_tool_is_default_step(builder, "cargo-clippy", true) {
        let tool = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "cargo-clippy",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/tippy",
            source_type: SourceType::InTree,
            extra_features: Vec::new(),
            allow_features: "",
            cargo_args: owned_cargo_args(CARGO_CLIPPY_CARGO_ARGS),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_private_bins(builder, &tool.tool_path, &["tippy", "targo-tippy"]);
    }
    if extended_rustc_tool_is_default_step(builder, "clippy-driver", true) {
        let extra_features = tippy_driver_features(builder, target);
        let tool = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "clippy-driver",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/tippy",
            source_type: SourceType::InTree,
            extra_features,
            allow_features: "",
            cargo_args: owned_cargo_args(CLIPPY_DRIVER_CARGO_ARGS),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_private_bins(builder, &tool.tool_path, &["tippy-driver"]);
    }
    if extended_rustc_tool_is_default_step(builder, "cargo-fmt", true) {
        let tool = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "cargo-fmt",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/trustfmt",
            source_type: SourceType::InTree,
            extra_features: Vec::new(),
            allow_features: "",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_private_bins(builder, &tool.tool_path, &["targo-fmt"]);
    }
    if extended_rustc_tool_is_default_step(builder, "rustfmt", true) {
        let tool = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "rustfmt",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/trustfmt",
            source_type: SourceType::InTree,
            extra_features: Vec::new(),
            allow_features: "",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_private_bins(builder, &tool.tool_path, &["trustfmt"]);
    }
    if tool_enabled_for_tool_settings(
        builder.config.extended,
        builder.config.tools.as_ref(),
        "trust-analyzer",
    ) {
        let tool = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "rust-analyzer",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/rust-analyzer",
            source_type: SourceType::InTree,
            extra_features: vec!["in-rust-tree".to_owned()],
            allow_features: RustAnalyzer::ALLOW_FEATURES,
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_private_bins(builder, &tool.tool_path, &["trust-analyzer"]);
    }
    if restore_rust_analyzer_proc_macro_srv(builder) {
        let tool = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "rust-analyzer-proc-macro-srv",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/rust-analyzer/crates/proc-macro-srv-cli",
            source_type: SourceType::InTree,
            extra_features: vec!["in-rust-tree".to_owned()],
            allow_features: RustAnalyzer::ALLOW_FEATURES,
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        let libexec = sysroot.join("libexec");
        t!(fs::create_dir_all(&libexec));
        let installed = libexec.join(exe("trust-analyzer-proc-macro-srv", target_compiler.host));
        builder.copy_link(&tool.tool_path, &installed, FileType::Executable);
        validate_installed_rustc_private_tool(builder, target_compiler, &installed);
    }
    if extended_rustc_tool_is_default_step(builder, "miri", false) {
        let mut extra_features = Vec::new();
        if builder.config.jemalloc(target) {
            extra_features.push("jemalloc".to_string());
        }
        let tool = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "miri",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/miri",
            source_type: SourceType::InTree,
            extra_features,
            allow_features: "",
            cargo_args: vec!["--all-targets".to_string()],
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_private_bins(builder, &tool.tool_path, &["trust-miri"]);
    }
    if extended_rustc_tool_is_default_step(builder, "cargo-miri", false) {
        let tool = builder.ensure(ToolBuild {
            build_compiler: compilers.build_compiler,
            output_compiler: target_compiler,
            target,
            tool: "cargo-miri",
            mode: Mode::ToolRustcPrivate,
            path: "src/tools/miri/cargo-miri",
            source_type: SourceType::InTree,
            extra_features: Vec::new(),
            allow_features: "",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });
        install_private_bins(builder, &tool.tool_path, &["targo-miri"]);
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
        pub enum Tool {
            $(
                $name,
            )+
        }

        impl<'a> Builder<'a> {
            /// Ensure a tool is built, then get the path to its executable.
            ///
            /// The actual building, if any, will be handled via [`ToolBuild`].
            pub fn tool_exe(&self, tool: Tool) -> PathBuf {
                match tool {
                    $(Tool::$name =>
                        self.ensure($name {
                            compiler: self.compiler(0, self.config.host_target),
                            target: self.config.host_target,
                        }).tool_path,
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

        impl Step for $name {
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
    Compiletest, "src/tools/compiletest", "compiletest";
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
    RustdocGUITest, "src/tools/rustdoc-gui-test", "rustdoc-gui-test";
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

impl Step for ErrorIndex {
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

impl Step for RemoteTestServer {
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
        // User-facing stage2+ sysroots install only the Trust-branded name.
        (trustdoc, Vec::new())
    }
}

impl Step for Rustdoc {
    /// Path to the built rustdoc binary.
    type Output = PathBuf;

    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.selectors(&["src/tools/trustdoc", "src/librustdoc"])
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
            let inherited_rustdoc = bindir.join(exe("rustdoc", target_compiler.host));
            if target_compiler.stage >= 2 {
                // Trust: at stage>=2 ship ONLY the `trustdoc` name; do NOT emit a
                // stock `rustdoc` bin alias (Trust-branded-names-only policy — the
                // root-cause replacement for scripts/purge-stock-names.sh, which
                // deleted `rustdoc` post-build). Remove any stale `rustdoc` a prior
                // build left so the invariant also holds on additive trees.
                let _ = fs::remove_file(&inherited_rustdoc);
            }
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
        //
        let mut extra_features = Vec::new();
        if builder.config.jemalloc(target) {
            extra_features.push("jemalloc".to_string());
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

/// Builds the cargo tool.
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

impl Step for Cargo {
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
        builder.build.require_submodule("src/tools/targo", None);

        builder.std(self.build_compiler, builder.host_target);
        builder.std(self.build_compiler, self.target);

        let target_compiler = builder.compiler(self.build_compiler.stage + 1, self.target);
        let tool_result = builder.ensure(ToolBuild {
            build_compiler: self.build_compiler,
            output_compiler: target_compiler,
            target: self.target,
            tool: "cargo",
            mode: Mode::ToolTarget,
            path: "src/tools/targo",
            source_type: SourceType::Submodule,
            extra_features: Vec::new(),
            // Cargo is compilable with a stable compiler, but since we run in bootstrap,
            // with RUSTC_BOOTSTRAP being set, some "clever" build scripts enable specialization
            // based on this, which breaks stuff. We thus have to explicitly allow these features
            // here.
            allow_features: "min_specialization,specialization",
            cargo_args: Vec::new(),
            artifact_kind: ToolArtifactKind::Binary,
        });

        let tool_path =
            copy_bins_to_sysroot(builder, target_compiler, &tool_result.tool_path, &["targo"]);

        ToolBuildResult { tool_path, build_compiler: tool_result.build_compiler }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("targo", self.target).built_by(self.build_compiler))
    }
}

/// Builds the targo-trust tool.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TCargoTrust {
    build_compiler: Compiler,
    target: TargetSelection,
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
pub(super) const CARGO_TRUST_ALLOW_FEATURES: &str =
    "min_specialization,specialization,try_trait_v2,try_trait_v2_residual";

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
        path: "crates/trust-router",
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
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.never()
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

    fn run(self, builder: &Builder<'_>) -> ToolBuildResult {
        builder.std(self.build_compiler, builder.host_target);
        builder.std(self.build_compiler, self.target);

        let target_compiler = builder.compiler(self.build_compiler.stage + 1, self.target);
        let tool_result =
            build_trustd_tool(builder, self.build_compiler, target_compiler, self.target);
        let tool_path =
            copy_bins_to_sysroot(builder, target_compiler, &tool_result.tool_path, &["trustd"]);

        ToolBuildResult { tool_path, build_compiler: tool_result.build_compiler }
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

    /// Returns `TCargoTrust` that should be **used** by the passed compiler.
    pub fn from_target_compiler(builder: &Builder<'_>, target_compiler: Compiler) -> Self {
        Self {
            build_compiler: get_tool_target_compiler(
                builder,
                ToolTargetBuildMode::Dist(target_compiler),
            ),
            target: target_compiler.host,
        }
    }
}

impl Step for TCargoTrust {
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
        let tool_result = builder.ensure(ToolBuild {
            build_compiler: self.build_compiler,
            output_compiler: target_compiler,
            target: self.target,
            tool: "targo-trust",
            mode: Mode::ToolTarget,
            path: "targo-trust",
            source_type: SourceType::InTree,
            extra_features: targo_trust_in_process_features(),
            allow_features: CARGO_TRUST_ALLOW_FEATURES,
            cargo_args: locked_cargo_args(&[]),
            artifact_kind: ToolArtifactKind::Binary,
        });

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

        ToolBuildResult { tool_path, build_compiler: tool_result.build_compiler }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("targo-trust", self.target).built_by(self.build_compiler))
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

impl Step for LldWrapper {
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

    builder.copy_link(
        &lld_wrapper.lld_dir.join("bin").join(src_exe),
        &libdir_bin.join(dst_exe),
        FileType::Executable,
    );
    let self_contained_lld_dir = libdir_bin.join("gcc-ld");
    t!(fs::create_dir_all(&self_contained_lld_dir));

    for name in crate::LLD_FILE_NAMES {
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

impl Step for WasmComponentLd {
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

impl Step for RustAnalyzer {
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

        ToolBuildResult { tool_path, build_compiler: tool_result.build_compiler }
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

impl Step for RustAnalyzerProcMacroSrv {
    type Output = ToolBuildResult;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        // Allow building `rust-analyzer-proc-macro-srv` both as part of the `rust-analyzer` and as a stand-alone tool.
        run.path("src/tools/rust-analyzer")
            .path("src/tools/rust-analyzer/crates/proc-macro-srv-cli")
            .alias("trust-analyzer-proc-macro-srv")
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

impl Step for LlvmBitcodeLinker {
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
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.never()
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

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

impl Step for BuildManifest {
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

    pub fn from_build_and_target_compiler(
        build_compiler: Compiler,
        target_compiler: Compiler,
    ) -> Self {
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

        impl Step for $name {
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
        builder.build.unstable_features(),
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
    add_features: Option<fn(&Builder<'_>, TargetSelection, &mut Vec<String>)>,
    cargo_args: Option<&[&'static str]>,
) -> ToolBuildResult {
    let target = compilers.target();
    let mut extra_features = Vec::new();
    if let Some(func) = add_features {
        func(builder, target, &mut extra_features);
    }

    let build_compiler = compilers.build_compiler;
    let ToolBuildResult { tool_path, .. } = builder.ensure(ToolBuild {
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
        ToolBuildResult { tool_path: path, build_compiler }
    } else {
        ToolBuildResult { tool_path, build_compiler }
    }
}

tool_rustc_extended!(Cargofmt {
    path: "src/tools/trustfmt",
    tool_name: "cargo-fmt",
    stable: true,
    add_bins_to_sysroot: ["targo-fmt"]
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
    tippy_driver_features_for_jemalloc(builder.config.jemalloc(target))
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
        if builder.config.jemalloc(target) {
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
    add_bins_to_sysroot: ["trustfmt"]
});

pub const TEST_FLOAT_PARSE_ALLOW_FEATURES: &str = "f16,cfg_target_has_reliable_f16_f128";

#[cfg(test)]
mod tests;

impl Builder<'_> {
    /// Gets a `BootstrapCommand` which is ready to run `tool` in `stage` built for
    /// `host`.
    ///
    /// This also ensures that the given tool is built (using [`ToolBuild`]).
    pub fn tool_cmd(&self, tool: Tool) -> BootstrapCommand {
        let mut cmd = command(self.tool_exe(tool));
        let compiler = self.compiler(0, self.config.host_target);
        let host = &compiler.host;
        // Prepares the `cmd` provided to be able to run the `compiler` provided.
        //
        // Notably this munges the dynamic library lookup path to point to the
        // right location to run `compiler`.
        let mut lib_paths: Vec<PathBuf> = discover_out_dirs_with_dylibs(
            self.cargo_out(compiler, Mode::ToolBootstrap, *host).join("build"),
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
