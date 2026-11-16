//! Compilation of native dependencies like LLVM.
//!
//! Native projects like LLVM unfortunately aren't suited just yet for
//! compilation in build scripts that Cargo has. This is because the
//! compilation takes a *very* long time but also because we don't want to
//! compile LLVM 3 times as part of a normal bootstrap (we want it cached).
//!
//! LLVM and compiler-rt are essentially just wired up to everything else to
//! ensure that they're always in place if needed.

use std::env::consts::EXE_EXTENSION;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::{env, fs};

use build_helper::git::PathFreshness;

use crate::core::build_steps::llvm;
use crate::core::builder::{
    Builder, CommandLineStep, Kind, RunConfig, ShouldRun, Step, StepMetadata,
};
use crate::core::config::{Config, LlvmCiMode, LlvmPgoGenerationMode, TargetSelection};
use crate::core::session::CLang;
use crate::trace;
use crate::utils::build_stamp::BuildStamp;
use crate::utils::exec::command;
use crate::utils::helpers::{
    self, exe, get_clang_cl_resource_dir, libdir, t, unhashed_basename, up_to_date,
};

// Trust: Trust-owned native-build reuse machinery lives in these submodules, so
// this upstream file keeps upstream's shape and stays within tidy's length limit.
mod cmake_plan;
// Trust: LLD consumes the declared whole zstd dependency, as rustc_llvm does.
mod lld_zstd;
mod reuse_evidence;
mod source_recipe;

use self::cmake_plan::{CmakeOperation, CmakePlan, prepared_cmake_request};
use self::reuse_evidence::{
    CmakeGeneration, ReusableCmakeInputs, begin_cmake_miss, bounded_native_evidence,
    cmake_generation_matches, complete_with_unchanged_cmake_source, observe_cmake_sources,
    recorded_llvm_dependency_key, reusable_cmake_inputs,
};
#[cfg(test)]
use self::reuse_evidence::{
    cmake_generation_record, own_source_unchanged, recorded_llvm_dependency_key_with_hook,
};
#[cfg(all(test, unix))]
use self::source_recipe::prepare_owned_source_build;
use self::source_recipe::{
    LlvmBuildCacheIdentity, OwnSourceGeneration, ResolvedSourceRecipe, SelectedLlvmDependency,
    SourceRecipeResolution, SourceResolutionMode, regular_source_artifact,
    validate_owned_source_build,
};
#[cfg(test)]
use self::source_recipe::{SourceRecipeKey, source_recipe_key};

/// Path where a file containing the link type (dynamic or static) is stored in the LLVM CI tarball.
pub const LLVM_CI_LINK_TYPE_PATH: &str = "link-type.txt";

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum LlvmKind {
    /// The LLVM was built from in-tree sources
    BuiltLocally,
    /// The LLVM was downloaded from the `rust-dev` CI artifact.
    DownloadedFromCi,
    /// The LLVM was provided externally through a `llvm-config` file.
    External,
}

/// Result of building or downloading LLVM artifacts.
#[derive(Clone)]
pub struct LlvmOutput {
    llvm_config: PathBuf,
    link_shared: bool,
    llvm_root_dir: PathBuf,
    kind: LlvmKind,
}

impl LlvmOutput {
    /// Directory containing the built LLVM artifacts.
    /// Contains `bin`/`lib` directories.
    pub fn root_dir(&self) -> &Path {
        &self.llvm_root_dir
    }

    /// Path to LLVM cmake directory.
    pub fn cmake_dir(&self) -> PathBuf {
        self.llvm_root_dir.join("lib").join("cmake").join("llvm")
    }

    /// Should we link dynamically to the built LLVM?
    pub fn link_shared(&self) -> bool {
        self.link_shared
    }

    /// How was the LLVM produced?
    pub fn kind(&self) -> LlvmKind {
        self.kind
    }

    /// Path to the `llvm-config` binary.
    ///
    /// Note that this binary might not be executable on the current host, if LLVM was built for a
    /// different target.
    pub fn llvm_config(&self) -> &Path {
        &self.llvm_config
    }
}

#[path = "llvm/installed_outputs.rs"]
mod installed_outputs;

#[path = "llvm/external_inputs.rs"]
mod external_inputs;

pub struct LlvmBuildInfo {
    stamp: BuildStamp,
    output: LlvmOutput,
    source_generation: OwnSourceGeneration,
    recipe: SourceRecipeResolution,
}

pub enum LlvmBuildStatus {
    AlreadyBuilt(LlvmOutput),
    ShouldBuild(LlvmBuildInfo),
}

impl LlvmBuildStatus {
    pub fn llvm_output(&self) -> &LlvmOutput {
        match self {
            LlvmBuildStatus::AlreadyBuilt(res) => res,
            LlvmBuildStatus::ShouldBuild(meta) => &meta.output,
        }
    }
}

/// Allows each step to add C/Cxx flags which are only used for a specific cmake invocation.
#[derive(Debug, Clone, Default)]
struct CcFlags {
    /// Additional values for CMAKE_CC_FLAGS, to be added before all other values.
    cflags: OsString,
    /// Additional values for CMAKE_CXX_FLAGS, to be added before all other values.
    cxxflags: OsString,
}

impl CcFlags {
    fn push_all(&mut self, s: impl AsRef<OsStr>) {
        let s = s.as_ref();
        self.cflags.push(" ");
        self.cflags.push(s);
        self.cxxflags.push(" ");
        self.cxxflags.push(s);
    }
}

/// Linker flags to pass to LLVM's CMake invocation.
#[derive(Debug, Clone, Default)]
struct LdFlags {
    /// CMAKE_EXE_LINKER_FLAGS
    exe: OsString,
    /// CMAKE_SHARED_LINKER_FLAGS
    shared: OsString,
    /// CMAKE_MODULE_LINKER_FLAGS
    module: OsString,
}

impl LdFlags {
    fn push_all(&mut self, s: impl AsRef<OsStr>) {
        let s = s.as_ref();
        self.exe.push(" ");
        self.exe.push(s);
        self.shared.push(" ");
        self.shared.push(s);
        self.module.push(" ");
        self.module.push(s);
    }
}

/// Select configured external LLVM or ensure the configured CI acquisition owner.
/// Local source lookup/build is separate; CI policy retains its existing source
/// materialization and download behavior.
fn external_or_ci_llvm_output(
    builder: &Builder<'_>,
    target: TargetSelection,
) -> Option<LlvmOutput> {
    // Use an externally provided LLVM, if available
    if let Some(config) = builder.config.target_config.get(&target)
        && let Some(ref s) = config.llvm_config
    {
        // We execute the llvm-config, and we can only do that on the host target
        if target == builder.host_target {
            check_llvm_version(builder, s);
        }
        let llvm_config = s.to_path_buf();
        let mut llvm_root_dir = llvm_config.clone();
        llvm_root_dir.pop();
        llvm_root_dir.pop();

        return Some(LlvmOutput {
            llvm_config,
            link_shared: llvm_link_shared(&builder.config),
            llvm_root_dir,
            kind: LlvmKind::External,
        });
    }

    // If external LLVM is not configured, try to download LLVM from CI, if possible
    let llvm_ci = builder.ensure(LlvmFromCi { target });
    if let Some(llvm) = llvm_ci {
        return Some(llvm.output);
    }

    None
}

/// Nonbuilding local lookup after the existing external/CI selection route.
/// An unavailable cross-HOST request is a miss, never permission to build HOST.
pub fn prebuilt_llvm_output(builder: &Builder<'_>, target: TargetSelection) -> Option<LlvmOutput> {
    if let Some(output) = external_or_ci_llvm_output(builder, target) {
        return Some(output);
    }
    match get_locally_built_llvm_build_status(builder, target) {
        LlvmBuildStatus::AlreadyBuilt(output) => Some(output),
        LlvmBuildStatus::ShouldBuild(_) => None,
    }
}

/// This returns whether we've already previously built LLVM.
///
/// This will return the llvm-config if it can get it (but it will not build it
/// if not).
///
/// Note that calling this function *might* checkout the LLVM submodule!
pub fn get_llvm_build_status(builder: &Builder<'_>, target: TargetSelection) -> LlvmBuildStatus {
    if let Some(prebuilt_output) = external_or_ci_llvm_output(builder, target) {
        return LlvmBuildStatus::AlreadyBuilt(prebuilt_output);
    }

    // In remaining cases, build it locally
    // If submodules are disabled, this does nothing.
    builder.config.update_submodule("src/llvm-project");

    get_locally_built_llvm_build_status(builder, target)
}

/// Return build status of LLVM, considering only the (possibly) locally built LLVM.
///
/// Calling this function should never attempt to checkout the LLVM submodule.
pub(crate) fn get_locally_built_llvm_build_status(
    builder: &Builder<'_>,
    target: TargetSelection,
) -> LlvmBuildStatus {
    let out_dir = llvm_output_dir(builder, target);

    let res = LlvmOutput {
        llvm_config: out_dir.join("bin").join(exe("llvm-config", target)),
        link_shared: llvm_link_shared(&builder.config),
        llvm_root_dir: out_dir.clone(),
        kind: LlvmKind::BuiltLocally,
    };

    resolve_local_llvm(builder, target, res, SourceResolutionMode::Lookup)
}

fn llvm_native_target(target: TargetSelection) -> String {
    if target.starts_with("riscv") {
        let index = target.triple.find('-').unwrap();
        format!("riscv{}{}", &target.triple[5..7], &target.triple[index..])
    } else if target.starts_with("powerpc") && target.ends_with("freebsd") {
        format!("{target}13.0")
    } else {
        target.to_string()
    }
}

fn resolve_local_llvm(
    builder: &Builder<'_>,
    target: TargetSelection,
    output: LlvmOutput,
    mode: SourceResolutionMode,
) -> LlvmBuildStatus {
    let source = builder.src.join("src/llvm-project");
    let projected = || OwnSourceGeneration {
        source: source.clone(),
        anchor: builder.out.clone(),
        output: output.root_dir().to_owned(),
        observed: None,
    };
    let source_generation = if builder.config.dry_run() {
        projected()
    } else if !source.is_dir() {
        let source_generation = projected();
        let stamp = source_generation.stamp("llvm", &target.triple, None);
        return LlvmBuildStatus::ShouldBuild(LlvmBuildInfo {
            stamp,
            output,
            source_generation,
            recipe: SourceRecipeResolution::Unavailable(
                "LLVM sources are unavailable for request observation".into(),
            ),
        });
    } else {
        OwnSourceGeneration::observe(builder, output.root_dir())
    };
    let recipe = if builder.config.dry_run() {
        SourceRecipeResolution::Dry
    } else {
        let host_tools = if builder.config.is_host_target(target) {
            Some(None)
        } else {
            resolve_cross_llvm_tools(builder, target, mode).map(Some)
        };
        match host_tools {
            None => SourceRecipeResolution::UnresolvedCross,
            Some(host_tools) => {
                let native = llvm_native_target(target);
                let recipe = llvm_cmake_config_with_tools(
                    builder,
                    target,
                    LlvmCmakeRequest {
                        source: &source.join("llvm"),
                        output: output.root_dir(),
                        target_native: &native,
                        link_shared: output.link_shared(),
                    },
                    host_tools.as_ref(),
                );
                let dependencies = host_tools.into_iter().map(|tools| tools.selected).collect();
                match recipe.and_then(|recipe| {
                    ResolvedSourceRecipe::from_config(
                        recipe.config,
                        recipe.postprocess_version_suffix,
                        dependencies,
                        output.link_shared(),
                    )
                }) {
                    Ok(recipe) => SourceRecipeResolution::Resolved(recipe),
                    Err(error) => SourceRecipeResolution::Unavailable(error),
                }
            }
        }
    };
    let key = match &recipe {
        SourceRecipeResolution::Resolved(recipe) => recipe.key.as_ref(),
        _ => None,
    };
    let stamp = source_generation.stamp("llvm", &target.triple, key);
    if key.is_some()
        && source_generation.cache_matches("llvm", &stamp, output.llvm_config())
        && matches!(&recipe, SourceRecipeResolution::Resolved(recipe)
            if recipe.dependencies.iter().all(SelectedLlvmDependency::unchanged))
    {
        return LlvmBuildStatus::AlreadyBuilt(output);
    }
    LlvmBuildStatus::ShouldBuild(LlvmBuildInfo { stamp, output, source_generation, recipe })
}

/// The suffix emitted by the actual recipe before final user definitions.
/// It participates in requested configuration; postprocessing currently retains
/// this selected value, rather than claiming to read a final user override.
fn llvm_version_suffix_to_define(builder: &Builder<'_>) -> Option<String> {
    if let Some(ref suffix) = builder.config.llvm_version_suffix {
        // Allow version-suffix="" to not define a version suffix at all.
        if !suffix.is_empty() { Some(suffix.to_string()) } else { None }
    } else if builder.config.channel == "dev" {
        // Changes to a version suffix require a complete rebuild of the LLVM.
        // To avoid rebuilds during a time of version bump, don't include rustc
        // release number on the dev channel.
        Some("-rust-dev".to_string())
    } else {
        Some(format!("-rust-{}-{}", builder.version, builder.config.channel))
    }
}

/// Output directory of *locally built* LLVM for the given `target`.
/// Should only be used within this module, when building LLVM (or related tools).
/// Otherwise, you should ensure the `Llvm` step and read its root directory.
pub(crate) fn llvm_output_dir(builder: &Builder<'_>, target: TargetSelection) -> PathBuf {
    builder.config.out.join(target).join("llvm")
}

fn try_download_ci_llvm(builder: &Builder<'_>, target: TargetSelection) -> Option<DownloadedLlvm> {
    match builder.config.llvm_ci_mode {
        LlvmCiMode::BuildLocally => return None,
        LlvmCiMode::Download => {}
        LlvmCiMode::DownloadIfUnchanged => {
            builder.config.update_submodule("src/llvm-project");

            // Check for untracked changes in `src/llvm-project` and other important places.
            let has_changes = builder.config.has_changes_from_upstream(LLVM_INVALIDATION_PATHS);
            if has_changes {
                builder.info("Warning: LLVM will not be downloaded because of local changes");
                return None;
            }
        }
    }

    if !is_ci_llvm_available_for_target(&target, builder.config.llvm_assertions) {
        builder.info(&format!(
            "Warning: LLVM not available on CI for target={target} and assertions={}",
            builder.config.llvm_assertions
        ));
        return None;
    }

    let ci_llvm = builder.config.maybe_download_ci_llvm(target)?;
    let link_shared = if !builder.config.dry_run() {
        let link_type = t!(
            std::fs::read_to_string(ci_llvm.join(LLVM_CI_LINK_TYPE_PATH)),
            format!("LLVM downloaded from CI is missing the following file: {}", ci_llvm.display())
        );
        link_type == "dynamic"
    } else {
        false
    };

    Some(DownloadedLlvm {
        output: LlvmOutput {
            llvm_config: ci_llvm.join("bin").join(exe("llvm-config", target)),
            link_shared,
            llvm_root_dir: ci_llvm,
            kind: LlvmKind::DownloadedFromCi,
        },
    })
}

/// Determine whether llvm should be linked dynamically.
/// **NOTE**: This only contains the value from the config.
/// If you need to figure out the correct value for a specific LLVM instance, use
/// `prebuilt_llvm_config` instead.
///
/// This function is not a method on Config to discourage calling it from outside this module.
fn llvm_link_shared(config: &Config) -> bool {
    // unclear how thought-through this default is, but it maintains compatibility with
    // previous behavior
    config.llvm_link_shared.unwrap_or(false)
}

/// Paths whose changes invalidate LLVM downloads.
pub const LLVM_INVALIDATION_PATHS: &[&str] = &[
    "src/llvm-project",
    "src/bootstrap/download-ci-llvm-stamp",
    // the LLVM shared object file is named `LLVM-<LLVM-version>-rust-{version}-nightly`
    "src/version",
];

/// Detect whether LLVM sources have been modified locally or not.
pub(crate) fn detect_llvm_freshness(config: &Config, is_git: bool) -> PathFreshness {
    assert!(cfg!(not(test)), "unit tests shouldn't care about LLVM freshness");

    if is_git {
        config.check_path_modifications(LLVM_INVALIDATION_PATHS)
    } else if let Some(info) = crate::utils::channel::read_commit_info_file(&config.src) {
        PathFreshness::LastModifiedUpstream { upstream: info.sha.trim().to_owned() }
    } else {
        PathFreshness::MissingUpstream
    }
}

/// Returns whether the CI-found LLVM is currently usable.
///
/// This checks the build triple platform to confirm we're usable at all, and if LLVM
/// with/without assertions is available.
pub(crate) fn is_ci_llvm_available_for_target(
    host_target: &TargetSelection,
    asserts: bool,
) -> bool {
    // This is currently all tier 1 targets and tier 2 targets with host tools
    // (since others may not have CI artifacts)
    // https://doc.rust-lang.org/rustc/platform-support.html#tier-1
    let supported_platforms = [
        // tier 1
        ("aarch64-unknown-linux-gnu", false),
        ("aarch64-apple-darwin", false),
        ("aarch64-pc-windows-msvc", false),
        ("i686-pc-windows-msvc", false),
        ("i686-unknown-linux-gnu", false),
        ("x86_64-unknown-linux-gnu", true),
        ("x86_64-apple-darwin", true),
        ("x86_64-pc-windows-gnu", false),
        ("x86_64-pc-windows-msvc", true),
        // tier 2 with host tools
        ("aarch64-unknown-linux-musl", false),
        ("aarch64-pc-windows-gnullvm", false),
        ("arm-unknown-linux-gnueabi", false),
        ("arm-unknown-linux-gnueabihf", false),
        ("armv7-unknown-linux-gnueabihf", false),
        ("i686-pc-windows-gnu", false),
        ("loongarch64-unknown-linux-gnu", false),
        ("loongarch64-unknown-linux-musl", false),
        ("powerpc-unknown-linux-gnu", false),
        ("powerpc64-unknown-linux-gnu", false),
        ("powerpc64-unknown-linux-musl", false),
        ("powerpc64le-unknown-linux-gnu", false),
        ("powerpc64le-unknown-linux-musl", false),
        ("riscv64gc-unknown-linux-gnu", false),
        ("riscv64gc-unknown-linux-musl", false),
        ("s390x-unknown-linux-gnu", false),
        ("x86_64-pc-windows-gnullvm", false),
        ("x86_64-unknown-freebsd", false),
        ("x86_64-unknown-illumos", false),
        ("x86_64-unknown-linux-musl", false),
        ("x86_64-unknown-netbsd", false),
    ];

    // Check if the host target is available with the requested assertions (true/false),
    supported_platforms.contains(&(&*host_target.triple, asserts))
        // if it is not available for the given `asserts`, check if it is available with assertions (superset).
        || supported_platforms.contains(&(&*host_target.triple, true))
}

#[derive(Clone)]
pub struct DownloadedLlvm {
    pub output: LlvmOutput,
}

/// This step explicitly represents the output of *downloaded* LLVM.
/// The step will provide an output only if all the following is true:
/// - `llvm.download-ci-llvm` is `true` or `if-unchanged`
/// - If the previous value is `if-unchanged`, the local LLVM inputs are not modified
/// - Artifacts for LLVM for the given target (and debug assertions) are available on CI
///
/// There are some places in bootstrap that explicitly want to do something special about the
/// downloaded LLVM, this step serves for them to do it in an explicit way.
/// For all other use-cases, the normal `Llvm` step should be used.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LlvmFromCi {
    pub target: TargetSelection,
}

impl Step for LlvmFromCi {
    type Output = Option<DownloadedLlvm>;

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let llvm_ci = try_download_ci_llvm(builder, self.target)?;

        // Sanity check (we execute the llvm-config, so we can only do it on the host target).
        if builder.host_target == self.target {
            check_llvm_version(builder, llvm_ci.output.llvm_config());
        }

        Some(llvm_ci)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Llvm {
    pub target: TargetSelection,
}

struct ResolvedHostLlvmTools {
    selected: SelectedLlvmDependency,
    bindir: PathBuf,
    clang_tblgen: Option<PathBuf>,
}
fn selected_host_llvm(
    builder: &Builder<'_>,
    mode: SourceResolutionMode,
) -> Option<SelectedLlvmDependency> {
    let target = builder.config.host_target;
    let output = match mode {
        SourceResolutionMode::Lookup => {
            if let Some(path) = builder
                .config
                .target_config
                .get(&target)
                .and_then(|config| config.llvm_config.as_ref())
            {
                let mut root = path.to_owned();
                root.pop();
                root.pop();
                LlvmOutput {
                    llvm_config: path.to_owned(),
                    llvm_root_dir: root,
                    link_shared: llvm_link_shared(&builder.config),
                    kind: LlvmKind::External,
                }
            } else {
                // CI policy may require acquisition. Only the actual Build route
                // may ensure that owner; unknown is not permission to guess a root.
                if !matches!(builder.config.llvm_ci_mode, LlvmCiMode::BuildLocally) {
                    return None;
                }
                match get_locally_built_llvm_build_status(builder, target) {
                    LlvmBuildStatus::AlreadyBuilt(output) => output,
                    LlvmBuildStatus::ShouldBuild(_) => return None,
                }
            }
        }
        SourceResolutionMode::Build => builder.ensure(Llvm { target }),
    };
    Some(SelectedLlvmDependency::observe(output, target))
}
fn resolve_cross_llvm_tools(
    builder: &Builder<'_>,
    target: TargetSelection,
    mode: SourceResolutionMode,
) -> Option<ResolvedHostLlvmTools> {
    let selected = selected_host_llvm(builder, mode)?;
    let output = command(selected.output.llvm_config())
        .allow_failure()
        .arg("--bindir")
        .cached()
        .run_capture_stdout(builder);
    let reported_bindir = output.stdout_if_ok()?;
    let bindir = reported_bindir.trim();
    if bindir.is_empty() {
        return None;
    }
    let bindir = PathBuf::from(bindir);
    if !bindir.is_absolute() {
        return None;
    }
    if !bindir.join("llvm-tblgen").with_extension(EXE_EXTENSION).is_file()
        || (target.is_msvc() && !bindir.join("llvm-nm").with_extension(EXE_EXTENSION).is_file())
    {
        return None;
    }
    let clang_tblgen = builder.config.llvm_clang.then(|| {
        selected.output.root_dir().join("bin").join("clang-tblgen").with_extension(EXE_EXTENSION)
    });
    if clang_tblgen.as_ref().is_some_and(|path| !path.is_file()) {
        return None;
    }
    Some(ResolvedHostLlvmTools { selected, bindir, clang_tblgen })
}

// The actual request constructor takes resolved cross-dependency paths as data.
struct LlvmCmakeRequest<'a> {
    source: &'a Path,
    output: &'a Path,
    target_native: &'a str,
    link_shared: bool,
}

struct LlvmCmakeConfig {
    config: cmake::Config,
    // Preserve the existing postprocess selection, before final user defines.
    postprocess_version_suffix: Option<String>,
}

// Host-only qualification adapter for the same production constructor below.
#[cfg(all(test, unix))]
fn llvm_cmake_config(
    builder: &Builder<'_>,
    target: TargetSelection,
    request: LlvmCmakeRequest<'_>,
) -> LlvmCmakeConfig {
    llvm_cmake_config_with_tools(builder, target, request, None)
        .expect("host recipe requires selected C/C++ data")
}

fn llvm_cmake_config_with_tools(
    builder: &Builder<'_>,
    target: TargetSelection,
    request: LlvmCmakeRequest<'_>,
    host_tools: Option<&ResolvedHostLlvmTools>,
) -> Result<LlvmCmakeConfig, String> {
    let LlvmCmakeRequest { source, output, target_native, link_shared } = request;
    // https://llvm.org/docs/CMake.html
    let mut cfg = cmake::Config::new(source);
    // Owned derived input: fixed before preparation, written only after the
    // generation reset. It is not an external cleanup-protected dependency.
    cfg.define("LLVM_BUILD_KEY_FILE", output.join(".trust-llvm-build-id"));
    let mut ldflags = LdFlags::default();

    let profile = get_llvm_profile(&builder.config);

    // NOTE: remember to also update `bootstrap.example.toml` when changing the
    // defaults!
    let llvm_targets = match &builder.config.llvm_targets {
        Some(s) => s,
        None => {
            "AArch64;AMDGPU;ARM;BPF;Hexagon;LoongArch;MSP430;Mips;NVPTX;PowerPC;RISCV;\
                 Sparc;SystemZ;WebAssembly;X86"
        }
    };

    let llvm_exp_targets = match builder.config.llvm_experimental_targets {
        Some(ref s) => s,
        None => "AVR;M68k;CSKY;Xtensa",
    };

    let assertions = if builder.config.llvm_assertions { "ON" } else { "OFF" };
    let plugins = if builder.config.llvm_plugins { "ON" } else { "OFF" };
    let enable_tests = if builder.config.llvm_tests { "ON" } else { "OFF" };
    let enable_warnings = if builder.config.llvm_enable_warnings { "ON" } else { "OFF" };

    cfg.out_dir(output)
        .profile(profile)
        .define("LLVM_ENABLE_ASSERTIONS", assertions)
        .define("LLVM_UNREACHABLE_OPTIMIZE", "OFF")
        .define("LLVM_ENABLE_PLUGINS", plugins)
        .define("LLVM_TARGETS_TO_BUILD", llvm_targets)
        .define("LLVM_EXPERIMENTAL_TARGETS_TO_BUILD", llvm_exp_targets)
        .define("LLVM_INCLUDE_EXAMPLES", "OFF")
        .define("LLVM_INCLUDE_DOCS", "OFF")
        .define("LLVM_INCLUDE_BENCHMARKS", "OFF")
        .define("LLVM_INCLUDE_TESTS", enable_tests)
        .define("LLVM_ENABLE_LIBEDIT", "OFF")
        .define("LLVM_ENABLE_BINDINGS", "OFF")
        .define("LLVM_ENABLE_Z3_SOLVER", "OFF")
        .define_execution_budget("LLVM_PARALLEL_COMPILE_JOBS", builder.jobs().to_string())
        .define("LLVM_TARGET_ARCH", target_native.split('-').next().unwrap())
        .define("LLVM_DEFAULT_TARGET_TRIPLE", target_native)
        .define("LLVM_ENABLE_WARNINGS", enable_warnings);

    // Parts of our test suite rely on the `FileCheck` tool, which is built by default in
    // `build/$TARGET/llvm/build/bin` is but *not* then installed to `build/$TARGET/llvm/bin`.
    // This flag makes sure `FileCheck` is copied in the final binaries directory.
    cfg.define("LLVM_INSTALL_UTILS", "ON");

    if let Some(mode) = builder.config.llvm_pgo.generate_profile.as_ref() {
        cfg.define("LLVM_BUILD_INSTRUMENTED", "IR");
        match mode {
            LlvmPgoGenerationMode::Implicit => {}
            LlvmPgoGenerationMode::Directory(llvm_profile_dir) => {
                cfg.define("LLVM_PROFILE_DATA_DIR", llvm_profile_dir);
            }
        }
        cfg.define("LLVM_BUILD_RUNTIME", "No");
    }
    if let Some(path) = builder.config.llvm_pgo.use_profile.as_ref() {
        cfg.define("LLVM_PROFDATA_FILE", path);
    }

    // Libraries for ELF section compression and profraw files merging.
    if !target.is_msvc() {
        cfg.define("LLVM_ENABLE_ZLIB", "ON");
    } else {
        cfg.define("LLVM_ENABLE_ZLIB", "OFF");
    }

    // Are we compiling for iOS/tvOS/watchOS/visionOS?
    if target.contains("apple-ios")
        || target.contains("apple-tvos")
        || target.contains("apple-watchos")
        || target.contains("apple-visionos")
    {
        // Prevent cmake from adding -bundle to CFLAGS automatically, which leads to a compiler error because "-bitcode_bundle" also gets added.
        cfg.define("LLVM_ENABLE_PLUGINS", "OFF");
        // Zlib fails to link properly, leading to a compiler error.
        cfg.define("LLVM_ENABLE_ZLIB", "OFF");
    }

    // This setting makes the LLVM tools link to the dynamic LLVM library,
    // which saves both memory during parallel links and overall disk space
    // for the tools. We don't do this on every platform as it doesn't work
    // equally well everywhere.
    //
    // Under normal circumstances, the dylib LINK and BUILD vars below should
    // be set to the same value. See #160597
    let llvm_dylib = if link_shared { "ON" } else { "OFF" };
    cfg.define("LLVM_LINK_LLVM_DYLIB", llvm_dylib);
    cfg.define("LLVM_BUILD_LLVM_DYLIB", llvm_dylib);
    // Keep the pre-LLVM23 behavior for now.
    cfg.define("LLVM_VERSIONED_DYLIB_NAME_ON_DARWIN", "OFF");

    if link_shared {
        // We inform LLVM tools where they can find the LLVM library
        // by adding an rpath entry to the expected parent `lib` directory,
        // e.g. `rust-objcopy` is shipped in `lib/rustlib/<host>/bin`.
        if let Some(rpath) = llvm_lib_rpath(builder, target) {
            ldflags.exe.push(" ");
            ldflags.exe.push(rpath);
        }
    }

    if (target.starts_with("csky") || target.starts_with("riscv") || target.starts_with("sparc-"))
        && !target.contains("freebsd")
        && !target.contains("openbsd")
        && !target.contains("netbsd")
    {
        // CSKY and RISC-V GCC erroneously requires linking against
        // `libatomic` when using 1-byte and 2-byte C++
        // atomics but the LLVM build system check cannot
        // detect this. Therefore it is set manually here.
        // Some BSD uses Clang as its system compiler and
        // provides no libatomic in its base system so does
        // not want this. 32-bit SPARC requires linking against
        // libatomic as well.
        ldflags.exe.push(" -latomic");
        ldflags.shared.push(" -latomic");
    }

    if target.starts_with("mips") && target.contains("netbsd") {
        // LLVM wants 64-bit atomics, while mipsel is 32-bit only, so needs -latomic
        ldflags.exe.push(" -latomic");
        ldflags.shared.push(" -latomic");
    }

    if target.starts_with("arm64ec") {
        // MSVC linker requires the -machine:arm64ec flag to be passed to
        // know it's linking as Arm64EC (vs Arm64X).
        ldflags.exe.push(" -machine:arm64ec");
        ldflags.shared.push(" -machine:arm64ec");
    }

    // cc-rs deprecated `static_flag`, which used to supply `-static` for musl
    // targets, so pass it here instead.
    if target.contains("musl") && builder.crt_static(target).unwrap_or(true) {
        ldflags.exe.push(" -static");
    }

    if target.is_msvc() {
        cfg.define("CMAKE_MSVC_RUNTIME_LIBRARY", "MultiThreaded");
        cfg.static_crt(true);
    }

    if target.starts_with("i686") {
        cfg.define("LLVM_BUILD_32_BITS", "ON");
    }

    if target.starts_with("x86_64") && target.contains("ohos") {
        cfg.define("LLVM_TOOL_LLVM_RTDYLD_BUILD", "OFF");
    }

    let mut enabled_llvm_projects = Vec::new();

    if helpers::forcing_clang_based_tests() {
        enabled_llvm_projects.push("clang");
    }

    if builder.config.llvm_polly {
        enabled_llvm_projects.push("polly");
    }

    if builder.config.llvm_clang {
        enabled_llvm_projects.push("clang");
    }

    // We want libxml to be disabled.
    // See https://github.com/rust-lang/rust/pull/50104
    cfg.define("LLVM_ENABLE_LIBXML2", "OFF");

    let mut enabled_llvm_runtimes = Vec::new();

    if helpers::forcing_clang_based_tests() {
        enabled_llvm_runtimes.push("compiler-rt");
    }

    if !enabled_llvm_projects.is_empty() {
        enabled_llvm_projects.sort();
        enabled_llvm_projects.dedup();
        cfg.define("LLVM_ENABLE_PROJECTS", enabled_llvm_projects.join(";"));
    }

    if !enabled_llvm_runtimes.is_empty() {
        enabled_llvm_runtimes.sort();
        enabled_llvm_runtimes.dedup();
        cfg.define("LLVM_ENABLE_RUNTIMES", enabled_llvm_runtimes.join(";"));
    }

    if let Some(num_linkers) = builder.config.llvm_link_jobs
        && num_linkers > 0
    {
        cfg.define_execution_budget("LLVM_PARALLEL_LINK_JOBS", num_linkers.to_string());
    }

    if !builder.config.is_host_target(target) {
        let tools =
            host_tools.ok_or("HOST LLVM tools are unavailable for cross request observation")?;
        cfg.define_input_path(
            "LLVM_TABLEGEN",
            tools.bindir.join("llvm-tblgen").with_extension(EXE_EXTENSION),
        );
        cfg.define_input_path(
            "LLVM_NM",
            tools.bindir.join("llvm-nm").with_extension(EXE_EXTENSION),
        );
        cfg.define_input_path("LLVM_CONFIG_PATH", tools.selected.output.llvm_config());
        if let Some(path) = &tools.clang_tblgen {
            cfg.define_input_path("CLANG_TABLEGEN", path);
        }
    }

    // Trust: upstream's computation, moved into `llvm_version_suffix_to_define` unchanged.
    let llvm_version_suffix = llvm_version_suffix_to_define(builder);
    if let Some(ref suffix) = llvm_version_suffix {
        cfg.define("LLVM_VERSION_SUFFIX", suffix);
    }

    resolve_cmake_plan(
        builder,
        target,
        CommonCmakeOptions { ninja: builder.selected_ninja(), use_compiler_launcher: true },
        ldflags,
        CcFlags::default(),
        &[],
        &|key| env::var_os(key),
    )
    .ok_or("selected C/C++ compiler data is unavailable")?
    .apply(&mut cfg);
    configure_llvm(builder, target, &mut cfg);

    for (key, val) in &builder.config.llvm_build_config {
        cfg.define(key, val);
    }

    Ok(LlvmCmakeConfig { config: cfg, postprocess_version_suffix: llvm_version_suffix })
}

impl CommandLineStep for Llvm {
    type Output = LlvmOutput;

    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/llvm-project").path("src/llvm-project/llvm")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Llvm { target: run.target });
    }

    /// Compile LLVM for `target`.
    fn run(self, builder: &Builder<'_>) -> LlvmOutput {
        let target = self.target;
        let mut status = get_llvm_build_status(builder, target);
        if !builder.config.dry_run()
            && let LlvmBuildStatus::ShouldBuild(info) = &status
            && matches!(info.recipe, SourceRecipeResolution::UnresolvedCross)
        {
            info.source_generation.refuse_linked_miss().unwrap_or_else(|error| panic!("{error}"));
            status = resolve_local_llvm(
                builder,
                target,
                info.output.clone(),
                SourceResolutionMode::Build,
            );
        }
        let LlvmBuildInfo { stamp, output, source_generation, recipe } = match status {
            LlvmBuildStatus::AlreadyBuilt(output) => return output,
            LlvmBuildStatus::ShouldBuild(info) => info,
        };
        if builder.config.dry_run() {
            if !builder.config.is_host_target(target) {
                builder.ensure(Llvm { target: builder.config.host_target });
            }
            return output;
        }
        source_generation.refuse_linked_miss().unwrap_or_else(|error| panic!("{error}"));
        let recipe = match recipe {
            SourceRecipeResolution::Resolved(recipe) => recipe,
            SourceRecipeResolution::Unavailable(error) => {
                panic!("unavailable LLVM request: {error}")
            }
            SourceRecipeResolution::UnresolvedCross => {
                panic!("HOST LLVM tools unavailable after genuine dependency construction")
            }
            SourceRecipeResolution::Dry => unreachable!("real LLVM build has no dry request"),
        };
        let ResolvedSourceRecipe {
            prepared,
            key,
            postprocess_version_suffix: llvm_version_suffix,
            dependencies,
        } = recipe;
        let link_shared = output.link_shared();
        if link_shared && target.is_windows() && !target.is_windows_gnullvm() {
            panic!("shared linking to LLVM is not currently supported on {}", target.triple);
        }
        let _guard = builder.msg_unstaged(Kind::Build, "LLVM", target);
        let _time = helpers::timeit(builder);
        t!(validate_owned_source_build(builder));
        for selected in &dependencies {
            t!(selected.ensure_selected(builder));
        }
        let known = key.is_some() && source_generation.observed.is_some();
        let selected_inputs = dependencies
            .iter()
            .map(|selected| selected.output.root_dir().to_owned())
            .collect::<Vec<_>>();
        t!(source_generation.begin(
            &stamp,
            &prepared,
            if known { CmakeGeneration::Known } else { CmakeGeneration::Unknown },
            &selected_inputs
        ));
        let build_identity =
            LlvmBuildCacheIdentity::derive(&source_generation, &target.triple, key.as_ref());
        t!(build_identity.write());
        prepared.build();

        // Helper to find the name of LLVM's shared library on darwin and linux.
        let find_llvm_lib_name = |extension| {
            let llvm_config = if target == builder.host_target {
                output.llvm_config().to_path_buf()
            } else {
                builder.ensure(Llvm { target: builder.host_target }).llvm_config().to_path_buf()
            };

            let major = get_llvm_version_major(builder, &llvm_config);
            match &llvm_version_suffix {
                Some(version_suffix) => format!("libLLVM-{major}{version_suffix}.{extension}"),
                None => format!("libLLVM-{major}.{extension}"),
            }
        };

        // When building LLVM with LLVM_LINK_LLVM_DYLIB for macOS, an unversioned
        // libLLVM.dylib will be built. However, llvm-config will still look
        // for a versioned path like libLLVM-14.dylib. Manually create a symbolic
        // link to make llvm-config happy.
        if link_shared && target.contains("apple-darwin") {
            let lib_name = find_llvm_lib_name("dylib");
            let lib_llvm = output.root_dir().join("build").join("lib").join(lib_name);
            if !lib_llvm.exists() {
                t!(builder.symlink_file("libLLVM.dylib", &lib_llvm));
            }
        }

        // When building LLVM as a shared library on linux, it can contain unexpected debuginfo:
        // some can come from the C++ standard library. Unless we're explicitly requesting LLVM to
        // be built with debuginfo, strip it away after the fact, to make dist artifacts smaller.
        if link_shared && builder.config.llvm_optimize && !builder.config.llvm_release_debuginfo {
            // Find the name of the LLVM shared library that we just built.
            let lib_name = find_llvm_lib_name("so");

            // If the shared library exists in LLVM's `/build/lib/` or `/lib/` folders, strip its
            // debuginfo.
            crate::core::build_steps::compile::strip_debug(
                builder,
                target,
                &output.root_dir().join("lib").join(&lib_name),
            );
            crate::core::build_steps::compile::strip_debug(
                builder,
                target,
                &output.root_dir().join("build").join("lib").join(&lib_name),
            );
        }

        if known
            && build_identity.matches()
            && dependencies.iter().all(SelectedLlvmDependency::unchanged)
            && regular_source_artifact(output.llvm_config())
        {
            t!(source_generation
                .complete(&stamp, || dependencies.iter().all(SelectedLlvmDependency::unchanged)));
        }

        output
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("llvm", self.target))
    }
}

/// This has to be called with the **host** llvm-config!
pub fn get_llvm_version(builder: &Builder<'_>, llvm_config: &Path) -> String {
    command(llvm_config)
        .arg("--version")
        .cached()
        .run_capture_stdout(builder)
        .stdout()
        .trim()
        .to_owned()
}

/// This has to be called with the **host** llvm-config!
pub fn get_llvm_version_major(builder: &Builder<'_>, llvm_config: &Path) -> u8 {
    let version = get_llvm_version(builder, llvm_config);
    let major_str = version.split_once('.').expect("Failed to parse LLVM version").0;
    major_str.parse().unwrap()
}

fn get_llvm_profile(config: &Config) -> &'static str {
    match (config.llvm_optimize, config.llvm_release_debuginfo) {
        (false, _) => "Debug",
        (true, false) => "Release",
        (true, true) => "RelWithDebInfo",
    }
}

fn check_llvm_version(builder: &Builder<'_>, llvm_config: &Path) {
    if builder.config.dry_run() {
        return;
    }

    let version = get_llvm_version(builder, llvm_config);
    let mut parts = version.split('.').take(2).filter_map(|s| s.parse::<u32>().ok());
    if let (Some(major), Some(_minor)) = (parts.next(), parts.next())
        && major >= 22
    {
        return;
    }
    panic!("\n\nbad LLVM version: {version}, need >=22\n\n")
}

/// C/C++ debug info remap flags for LLVM build.
///
/// The remap is observable when LLVM is compiled with debug info,
/// for example, with `llvm.release-debuginfo = true`.
fn debuginfo_map_cflags(builder: &Builder<'_>, target: TargetSelection) -> Vec<String> {
    if !builder.config.rust_remap_debuginfo {
        return Vec::new();
    }

    let mut flags = Vec::new();
    let map = format!("{}=/rustc/llvm", builder.src.display());
    let cc = builder.cc_tool(target);
    if cc.is_like_clang() || cc.is_like_gnu() {
        flags.push(format!("-fdebug-prefix-map={map}"));
    } else if cc.is_like_clang_cl() {
        flags.push("-Xclang".into());
        flags.push(format!("-fdebug-prefix-map={map}"));
    }
    flags
}

// Trust: share the existing dependency choice with TPDE's side-effect-free planning path.
fn in_tree_lld_requested(config: &Config, target: TargetSelection) -> bool {
    !target.contains("apple")
        && config.llvm_use_linker.is_none()
        && config.lld_enabled
        && !target.is_msvc()
}

// This is the actual downloaded-LLD shortcut, not a claim that CI is ready.
fn ci_lld_output_dir(llvm: &LlvmOutput, target: TargetSelection) -> Option<PathBuf> {
    (llvm.kind() == LlvmKind::DownloadedFromCi
        && llvm.root_dir().join("bin").join(exe("lld", target)).exists())
    .then(|| llvm.root_dir().to_owned())
}

fn requested_lld_output_dir(
    builder: &Builder<'_>,
    llvm: &LlvmOutput,
    target: TargetSelection,
) -> PathBuf {
    ci_lld_output_dir(llvm, target).unwrap_or_else(|| source_lld_output_dir(builder, target))
}

fn source_lld_output_dir(builder: &Builder<'_>, target: TargetSelection) -> PathBuf {
    builder.out.join(target).join("lld")
}

// Requested flags/environment only. The getter is intentionally lazy on Apple,
// fallback and non-shared branches; this does not construct or qualify LLD.
fn requested_lld_settings(
    config: &Config,
    target: TargetSelection,
    selected_lld: Option<&Path>,
    llvm_root: &Path,
    link_shared: bool,
    dylib_paths: impl FnOnce() -> Vec<PathBuf>,
    ldflags: &mut LdFlags,
) -> std::io::Result<Option<OsString>> {
    if target.contains("apple") {
        return Ok(None);
    }
    if !in_tree_lld_requested(config, target) {
        if config.llvm_thin_lto {
            ldflags.push_all("-fuse-ld=lld");
        }
        return Ok(None);
    }
    let root = selected_lld.ok_or_else(|| std::io::Error::other("missing requested LLD path"))?;
    ldflags.push_all(format!("'-B{}' -fuse-ld=lld", root.join("bin").display()));
    if !link_shared {
        return Ok(None);
    }
    let mut paths = dylib_paths();
    paths.insert(0, llvm_root.join("lib"));
    env::join_paths(paths).map(Some).map_err(std::io::Error::other)
}

/// Tries to reuse a locally built LLD as a linker.
/// If it is not available, uses a global LLD from PATH.
fn try_link_with_in_tree_lld(
    builder: &Builder<'_>,
    target: TargetSelection,
    llvm_output: &LlvmOutput,
    cfg: &mut cmake::Config,
    ldflags: &mut LdFlags,
) {
    // Apple has its own ld64 linker, so don't use LLD on Darwin.
    if target.contains("apple") {
        return;
    }

    let selected =
        in_tree_lld_requested(&builder.config, target).then(|| builder.ensure(Lld { target }));
    if let Some(path) = t!(requested_lld_settings(
        &builder.config,
        target,
        selected.as_deref(),
        llvm_output.root_dir(),
        llvm_output.link_shared(),
        helpers::dylib_path,
        ldflags,
    )) {
        cfg.env(helpers::dylib_path_var(), path);
    }
}

#[cfg(test)]
#[path = "llvm/tests/cmake_plan_tests.rs"]
mod cmake_plan_tests;

fn configure_cmake(
    builder: &Builder<'_>,
    target: TargetSelection,
    cfg: &mut cmake::Config,
    use_compiler_launcher: bool,
    ldflags: LdFlags,
    ccflags: CcFlags,
    suppressed_compiler_flag_prefixes: &[&str],
) {
    let ninja = builder.ninja();
    resolve_cmake_plan(
        builder,
        target,
        CommonCmakeOptions { ninja, use_compiler_launcher },
        ldflags,
        ccflags,
        suppressed_compiler_flag_prefixes,
        &|key| env::var_os(key),
    )
    .expect("selected C/C++ compiler data is unavailable")
    .apply(cfg);
}

#[derive(Clone, Copy)]
struct CommonCmakeOptions {
    ninja: bool,
    use_compiler_launcher: bool,
}

fn resolve_cmake_plan(
    builder: &Builder<'_>,
    target: TargetSelection,
    options: CommonCmakeOptions,
    mut ldflags: LdFlags,
    ccflags: CcFlags,
    suppressed_compiler_flag_prefixes: &[&str],
    environment: &dyn Fn(&str) -> Option<OsString>,
) -> Option<CmakePlan> {
    let CommonCmakeOptions { ninja, use_compiler_launcher } = options;
    let mut cfg = CmakePlan::default();
    // Do not print installation messages for up-to-date files.
    // LLVM and LLD builds can produce a lot of those and hit CI limits on log size.
    cfg.define("CMAKE_INSTALL_MESSAGE", "LAZY");

    if builder.config.quiet {
        // Only log errors and warnings from `cmake`.
        cfg.define("CMAKE_MESSAGE_LOG_LEVEL", "WARNING");

        // If we're configuring llvm to build with `ninja`, we can suppress output from it with
        // `--quiet`. Otherwise don't add anything since we don't know which build system is going
        // to use.
        if ninja {
            cfg.quiet_build();
        }
    }

    // Do not allow the user's value of DESTDIR to influence where
    // LLVM will install itself. LLVM must always be installed in our
    // own build directories.
    cfg.env("DESTDIR", "");

    if ninja {
        cfg.generator("Ninja");
    }
    cfg.target(&target.triple).host(&builder.config.host_target.triple);

    if !builder.config.is_host_target(target) {
        cfg.define("CMAKE_CROSSCOMPILING", "True");

        // NOTE: Ideally, we wouldn't have to do this, and `cmake-rs` would just handle it for us.
        // But it currently determines this based on the `CARGO_CFG_TARGET_OS` environment variable,
        // which isn't set when compiling outside `build.rs` (like bootstrap is).
        //
        // So for now, we define `CMAKE_SYSTEM_NAME` ourselves, to panicking in `cmake-rs`.
        if target.contains("netbsd") {
            cfg.define("CMAKE_SYSTEM_NAME", "NetBSD");
        } else if target.contains("dragonfly") {
            cfg.define("CMAKE_SYSTEM_NAME", "DragonFly");
        } else if target.contains("openbsd") {
            cfg.define("CMAKE_SYSTEM_NAME", "OpenBSD");
        } else if target.contains("freebsd") {
            cfg.define("CMAKE_SYSTEM_NAME", "FreeBSD");
        } else if target.is_windows() {
            cfg.define("CMAKE_SYSTEM_NAME", "Windows");
        } else if target.contains("haiku") {
            cfg.define("CMAKE_SYSTEM_NAME", "Haiku");
        } else if target.contains("solaris") || target.contains("illumos") {
            cfg.define("CMAKE_SYSTEM_NAME", "SunOS");
        } else if target.contains("linux") {
            cfg.define("CMAKE_SYSTEM_NAME", "Linux");
        } else if target.contains("darwin") {
            // macOS
            cfg.define("CMAKE_SYSTEM_NAME", "Darwin");
        } else if target.contains("ios") {
            cfg.define("CMAKE_SYSTEM_NAME", "iOS");
        } else if target.contains("tvos") {
            cfg.define("CMAKE_SYSTEM_NAME", "tvOS");
        } else if target.contains("visionos") {
            cfg.define("CMAKE_SYSTEM_NAME", "visionOS");
        } else if target.contains("watchos") {
            cfg.define("CMAKE_SYSTEM_NAME", "watchOS");
        } else if target.contains("none") {
            // "none" should be the last branch
            cfg.define("CMAKE_SYSTEM_NAME", "Generic");
        } else {
            builder.info(&format!(
                "could not determine CMAKE_SYSTEM_NAME from the target `{target}`, build may fail",
            ));
            // Fallback, set `CMAKE_SYSTEM_NAME` anyhow to avoid the logic `cmake-rs` tries, and
            // to avoid CMAKE_SYSTEM_NAME being inferred from the host.
            cfg.define("CMAKE_SYSTEM_NAME", "Generic");
        }

        // When cross-compiling we should also set CMAKE_SYSTEM_VERSION, but in
        // that case like CMake we cannot easily determine system version either.
        //
        // Since, the LLVM itself makes rather limited use of version checks in
        // CMakeFiles (and then only in tests), and so far no issues have been
        // reported, the system version is currently left unset.

        if target.contains("apple") {
            if !target.contains("darwin") {
                // FIXME(madsmtm): compiler-rt's CMake setup is kinda weird, it seems like they do
                // version testing etc. for macOS (i.e. Darwin), even while building for iOS?
                //
                // So for now we set it to "Darwin" on all Apple platforms.
                cfg.define("CMAKE_SYSTEM_NAME", "Darwin");

                // These two defines prevent CMake from automatically trying to add a MacOSX sysroot, which leads to a compiler error.
                cfg.define("CMAKE_OSX_SYSROOT", "/");
                cfg.define("CMAKE_OSX_DEPLOYMENT_TARGET", "");
            }

            // Make sure that CMake does not build universal binaries on macOS.
            // Explicitly specify the one single target architecture.
            if target.starts_with("aarch64") {
                // macOS uses a different name for building arm64
                cfg.define("CMAKE_OSX_ARCHITECTURES", "arm64");
            } else if target.starts_with("i686") {
                // macOS uses a different name for building i386
                cfg.define("CMAKE_OSX_ARCHITECTURES", "i386");
            } else {
                cfg.define("CMAKE_OSX_ARCHITECTURES", target.triple.split('-').next().unwrap());
            }
        }
    }

    let sanitize_cc = |cc: &Path| {
        if target.is_msvc() {
            Some(OsString::from(cc.to_str()?.replace('\\', "/")))
        } else {
            Some(cc.as_os_str().to_owned())
        }
    };

    // MSVC with CMake uses msbuild by default which doesn't respect these
    // vars that we'd otherwise configure. In that case we just skip this
    // entirely.
    if target.is_msvc() && !ninja {
        return Some(cfg);
    }

    if builder.config.llvm_clang_cl.is_none()
        && !builder.config.dry_run()
        && !builder.cc.contains_key(&target)
    {
        return None;
    }
    if builder.config.rust_remap_debuginfo && !builder.cc.contains_key(&target) {
        return None;
    }
    let (cc, cxx) = match builder.config.llvm_clang_cl {
        Some(ref cl) => (cl.into(), cl.into()),
        None => (builder.cc(target), builder.cxx(target).ok()?),
    };

    // If ccache is configured we inform the build a little differently how
    // to invoke ccache while also invoking our compilers.
    if use_compiler_launcher && let Some(ref ccache) = builder.config.ccache {
        cfg.define_input_program("CMAKE_C_COMPILER_LAUNCHER", ccache)
            .define_input_program("CMAKE_CXX_COMPILER_LAUNCHER", ccache);
    }
    cfg.define_input_program("CMAKE_C_COMPILER", sanitize_cc(&cc)?)
        .define_input_program("CMAKE_CXX_COMPILER", sanitize_cc(&cxx)?)
        .define_input_program("CMAKE_ASM_COMPILER", sanitize_cc(&cc)?);

    // If we are running under a FIFO jobserver, we should not pass -j to CMake; otherwise it
    // overrides the jobserver settings and can lead to oversubscription.
    let has_modern_jobserver = environment("MAKEFLAGS")
        .and_then(|flags| flags.into_string().ok())
        .map(|flags| flags.contains("--jobserver-auth=fifo:"))
        .unwrap_or(false);

    if !has_modern_jobserver {
        cfg.parallel_build(builder.jobs());
    }
    if builder.opaque_cc_operands.contains(&target) {
        cfg.operations.push(CmakeOperation::CleanupOpaque);
    }
    if !builder.config.dry_run() {
        for tool in [builder.cc.get(&target), builder.cxx.get(&target)].into_iter().flatten() {
            cfg.operations.extend(
                tool.env()
                    .iter()
                    .filter(|(key, _)| key == "SDKROOT")
                    .map(|(_, value)| CmakeOperation::InputNamespace(PathBuf::from(value))),
            );
        }
    }
    let mut cflags = ccflags.cflags.clone();
    // FIXME(madsmtm): Allow `cmake-rs` to select flags by itself by passing
    // our flags via `.cflag`/`.cxxflag` instead.
    //
    // Needs `suppressed_compiler_flag_prefixes` to be gone, and hence
    // https://github.com/llvm/llvm-project/issues/88780 to be fixed.
    for flag in builder
        .cc_handled_cflags(target, CLang::C)
        .into_iter()
        .chain(builder.cc_unhandled_cflags(target, CLang::C))
        .chain(debuginfo_map_cflags(builder, target))
        .filter(|flag| !suppressed_compiler_flag_prefixes.iter().any(|p| flag.starts_with(p)))
    {
        cflags.push(" ");
        cflags.push(flag);
    }
    if let Some(ref s) = builder.config.llvm_cflags {
        cflags.push(" ");
        cflags.push(s);
    }
    if target.contains("ohos") {
        cflags.push(" -D_LINUX_SYSINFO_H");
    }
    if builder.config.llvm_clang_cl.is_some() {
        cflags.push(format!(" --target={target}"));
    }
    // The ASM lane must mirror the C lane: cmake-rs seeds CMAKE_ASM_FLAGS from
    // its own PATH-`cc` probe, so a host whose `cc` is clang-flavored injects
    // clang-only flags (--target=…) that a configured-gcc CMAKE_ASM_COMPILER
    // rejects. Defining it here suppresses that probe; LLVM's .S files go
    // through the C compiler, so the C flag set is the right one.
    cfg.define("CMAKE_ASM_FLAGS", cflags.clone());
    cfg.define("CMAKE_C_FLAGS", cflags);
    let mut cxxflags = ccflags.cxxflags.clone();
    for flag in builder
        .cc_handled_cflags(target, CLang::Cxx)
        .into_iter()
        .chain(builder.cc_unhandled_cflags(target, CLang::Cxx))
        .chain(debuginfo_map_cflags(builder, target))
        .filter(|flag| {
            !suppressed_compiler_flag_prefixes
                .iter()
                .any(|suppressed_prefix| flag.starts_with(suppressed_prefix))
        })
    {
        cxxflags.push(" ");
        cxxflags.push(flag);
    }
    if let Some(ref s) = builder.config.llvm_cxxflags {
        cxxflags.push(" ");
        cxxflags.push(s);
    }
    if target.contains("ohos") {
        cxxflags.push(" -D_LINUX_SYSINFO_H");
    }
    if builder.config.llvm_clang_cl.is_some() {
        cxxflags.push(format!(" --target={target}"));
    }

    cfg.define("CMAKE_CXX_FLAGS", cxxflags);
    if let Some(ar) = builder.ar(target)
        && ar.is_absolute()
    {
        // LLVM build breaks if `CMAKE_AR` is a relative path, for some reason it
        // tries to resolve this path in the LLVM build directory.
        cfg.define_input_program("CMAKE_AR", sanitize_cc(&ar)?);
    }

    if let Some(ranlib) = builder.ranlib(target)
        && ranlib.is_absolute()
    {
        // LLVM build breaks if `CMAKE_RANLIB` is a relative path, for some reason it
        // tries to resolve this path in the LLVM build directory.
        cfg.define_input_program("CMAKE_RANLIB", sanitize_cc(&ranlib)?);
    }

    if let Some(ref flags) = builder.config.llvm_ldflags {
        ldflags.push_all(flags);
    }

    if let Some(flags) =
        get_var("LDFLAGS", &builder.config.host_target.triple, &target.triple, environment)
    {
        cfg.operations.push(CmakeOperation::CleanupOpaque);
        ldflags.push_all(&flags);
    }

    // For distribution we want the LLVM tools to be *statically* linked to libstdc++.
    // We also do this if the user explicitly requested static libstdc++.
    if builder.config.llvm_static_stdcpp
        && !target.is_msvc()
        && !target.contains("netbsd")
        && !target.contains("solaris")
    {
        if target.contains("apple") || target.is_windows() {
            ldflags.push_all("-static-libstdc++");
        } else {
            ldflags.push_all("-Wl,-Bsymbolic -static-libstdc++");
        }
    }

    cfg.define("CMAKE_SHARED_LINKER_FLAGS", &ldflags.shared);
    cfg.define("CMAKE_MODULE_LINKER_FLAGS", &ldflags.module);
    cfg.define("CMAKE_EXE_LINKER_FLAGS", &ldflags.exe);

    if environment("SCCACHE_ERROR_LOG").is_some() {
        cfg.env("RUSTC_LOG", "sccache=warn");
    }
    Some(cfg)
}

fn configure_llvm(builder: &Builder<'_>, target: TargetSelection, cfg: &mut cmake::Config) {
    // ThinLTO is only available when building with LLVM, enabling LLD is required.
    // Apple's linker ld64 supports ThinLTO out of the box though, so don't use LLD on Darwin.
    if builder.config.llvm_thin_lto {
        cfg.define("LLVM_ENABLE_LTO", "Thin");
        if !target.contains("apple") {
            cfg.define("LLVM_ENABLE_LLD", "ON");
        }
    }

    // Libraries for ELF section compression.
    if builder.config.llvm_libzstd {
        cfg.define("LLVM_ENABLE_ZSTD", "FORCE_ON");
        cfg.define("LLVM_USE_STATIC_ZSTD", "TRUE");
    } else {
        cfg.define("LLVM_ENABLE_ZSTD", "OFF");
    }

    if let Some(ref linker) = builder.config.llvm_use_linker {
        // Bind the exact executable as both recipe content and a protected cleanup input.
        // A spelling-only CMake definition cannot authorize replacing source outputs.
        cfg.define_input_program("LLVM_USE_LINKER", &[OsStr::new(linker)]);
    }

    if builder.config.llvm_allow_old_toolchain {
        cfg.define("LLVM_TEMPORARILY_ALLOW_OLD_TOOLCHAIN", "YES");
    }
}

// Adapted from https://github.com/alexcrichton/cc-rs/blob/fba7feded71ee4f63cfe885673ead6d7b4f2f454/src/lib.rs#L2347-L2365
fn get_var(
    var_base: &str,
    host: &str,
    target: &str,
    environment: &dyn Fn(&str) -> Option<OsString>,
) -> Option<OsString> {
    let kind = if host == target { "HOST" } else { "TARGET" };
    let target_u = target.replace('-', "_");
    environment(&format!("{var_base}_{target}"))
        .or_else(|| environment(&format!("{var_base}_{target_u}")))
        .or_else(|| environment(&format!("{kind}_{var_base}")))
        .or_else(|| environment(var_base))
}

/// Generate a RPATH entry for a binary that will link to LLVM (libLLVM.so) dynamically.
/// This will make it possible to execute the binary outside Rustup, so that it can still find the libLLVM.so file.
fn llvm_lib_rpath(builder: &Builder<'_>, target: TargetSelection) -> Option<&'static str> {
    if builder.config.rpath_enabled(target) && helpers::use_host_linker(target) {
        // Be careful when changing this path, we need to ensure it's quoted or escaped:
        // `$ORIGIN` would otherwise be expanded when the `LdFlags` are passed verbatim to
        // cmake.
        if target.contains("linux") {
            return Some("-Wl,-rpath,'$ORIGIN/../../../'");
        }
        if target.contains("apple-darwin") {
            return Some("-Wl,-rpath,'@loader_path/../../../'");
        }
    }
    None
}

#[derive(Clone)]
pub struct BuiltRustOffload {
    /// Path to the rust offload dylib
    offload: PathBuf,
}

impl BuiltRustOffload {
    pub fn rust_offload_path(&self) -> PathBuf {
        self.offload.clone()
    }

    pub fn rust_offload_filename(&self) -> String {
        self.offload.file_name().unwrap().to_str().unwrap().to_owned()
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct RustOffload {
    pub target: TargetSelection,
}

impl CommandLineStep for RustOffload {
    type Output = BuiltRustOffload;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("rust-offload")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RustOffload { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        if builder.config.dry_run() {
            return BuiltRustOffload {
                offload: builder.config.tempdir().join("rust-offload-dry-run"),
            };
        }

        let target = self.target;

        let llvm_output = builder.ensure(Llvm { target });

        let out_dir = builder.out.join(self.target.triple).join("rust-offload");

        let llvm_version_major = get_llvm_version_major(builder, &builder.host_llvm_config());
        let lib_ext = std::env::consts::DLL_EXTENSION;
        let lib_rust_offload = format!("libRustOffload-{llvm_version_major}");
        let build_dir = out_dir.join(libdir(target));
        let dylib = build_dir.join(&lib_rust_offload).with_extension(lib_ext);

        let mut cfg =
            cmake::Config::new(builder.src.join("compiler/rustc_llvm/llvm-wrapper/offload/"));

        let mut ldflags = LdFlags::default();
        try_link_with_in_tree_lld(builder, target, &llvm_output, &mut cfg, &mut ldflags);

        configure_cmake(builder, target, &mut cfg, true, ldflags, CcFlags::default(), &[]);

        let profile = get_llvm_profile(&builder.config);

        cfg.out_dir(&out_dir).profile(profile).define("LLVM_DIR", llvm_output.cmake_dir());

        cfg.build();

        if !dylib.exists() {
            eprintln!(
                "`{lib_rust_offload}` not found in `{}`. Either the build has failed or RustOffload was built with a wrong version of LLVM",
                build_dir.display()
            );
            helpers::exit_process(1);
        }

        BuiltRustOffload { offload: dylib }
    }
}

#[derive(Clone)]
pub struct BuiltOmpOffload {
    /// Path to the omp and offload dylibs.
    offload: Vec<PathBuf>,
    /// Directory the dylibs were installed into.
    lib_dir: PathBuf,
}

impl BuiltOmpOffload {
    pub fn lib_dir(&self) -> &Path {
        &self.lib_dir
    }

    pub fn artifact_paths_with_symlink_targets(&self) -> Vec<PathBuf> {
        let mut paths = self.offload.clone();

        for path in &self.offload {
            let mut current = path.clone();

            while t!(fs::symlink_metadata(&current)).file_type().is_symlink() {
                let target = t!(fs::read_link(&current));
                current = current.parent().unwrap().join(target);

                if paths.contains(&current) {
                    break;
                }

                paths.push(current.clone());
            }
        }

        paths
    }
}

// FIXME(offload): In an ideal world, we would just enable the offload runtime in our previous LLVM
// build step. For now, we still depend on the openmp runtime since we use some of it's API, so we
// build both. However, when building those runtimes as part of the LLVM step, then LLVM's cmake
// implicitly assumes that Clang has also been build and will try to use it. In the Rust CI, we
// don't always build clang (due to compile times), but instead use a slightly older external clang.
// LLVM tries to remove this build dependency of offload/openmp on Clang for LLVM-22, so in the
// future we might be able to integrate this step into the LLVM step. For now, we instead introduce
// a Clang_DIR bootstrap option, which allows us tell CMake to use an external clang for these two
// runtimes. This external clang will try to use it's own (older) include dirs when building our
// in-tree LLVM submodule, which will cause build failures. To prevent those, we now also
// explicitly set our include dirs.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct OmpOffload {
    pub target: TargetSelection,
}

#[derive(Debug)]
enum OffloadCxxQueryUnavailable {
    NoConfiguredCompiler,
    CommandFailure(Option<std::process::ExitStatus>),
}

fn decode_offload_cxx_library(
    output: &crate::utils::exec::CommandOutput,
) -> Result<Option<PathBuf>, OffloadCxxQueryUnavailable> {
    if !output.is_success() {
        return Err(OffloadCxxQueryUnavailable::CommandFailure(output.status()));
    }
    let stdout = output
        .stdout_if_present()
        .ok_or(OffloadCxxQueryUnavailable::CommandFailure(output.status()))?;
    if stdout.contains('\0') {
        return Err(OffloadCxxQueryUnavailable::CommandFailure(output.status()));
    }
    let library = PathBuf::from(stdout.trim());
    Ok(library.is_absolute().then(|| library.parent().map(Path::to_owned)).flatten())
}

fn query_offload_cxx_library(
    builder: &Builder<'_>,
    target: TargetSelection,
) -> Result<Option<PathBuf>, OffloadCxxQueryUnavailable> {
    let cxx = builder.cxx(target).map_err(|_| OffloadCxxQueryUnavailable::NoConfiguredCompiler)?;
    // Query once before admission. Failure is not a successful no-library answer;
    // its ordinary miss diagnostic is emitted before touching generated output.
    let output = command(&cxx)
        .allow_failure()
        .arg("-print-file-name=libstdc++.so")
        .cached()
        .run_capture_stdout(builder);
    decode_offload_cxx_library(&output)
}

#[derive(Debug)]
struct OffloadClang {
    clang: PathBuf,
    clangxx: PathBuf,
    cmake_dir: Option<PathBuf>,
}

fn selected_offload_clang(
    config: &Config,
    llvm: &LlvmOutput,
    target: TargetSelection,
) -> Option<OffloadClang> {
    let cmake_dir = (!config.llvm_clang).then(|| config.offload_clang_dir.clone()).flatten();
    let bin = if config.llvm_clang {
        llvm.llvm_config().parent().map(Path::to_owned)
    } else {
        // Preserve the maintained <prefix>/lib/cmake/clang selection.
        cmake_dir.as_deref().and_then(|dir| dir.ancestors().nth(3)).map(|prefix| prefix.join("bin"))
    }?;
    let clang = bin.join(exe("clang", target));
    clang.exists().then(|| OffloadClang {
        clang,
        clangxx: bin.join(exe("clang++", target)),
        cmake_dir,
    })
}

fn omp_offload_output(output: &Path) -> BuiltOmpOffload {
    BuiltOmpOffload {
        offload: ["libLLVMOffload", "libomp", "libomptarget"]
            .into_iter()
            .map(|name| {
                output.join("lib").join(name).with_extension(std::env::consts::DLL_EXTENSION)
            })
            .collect(),
        lib_dir: output.join("lib"),
    }
}

fn offload_artifacts_exist(output: &BuiltOmpOffload) -> bool {
    !output.offload.is_empty() && output.offload.iter().all(|path| path.is_file())
}

fn omp_offload_stamp(output: &Path, inputs: Option<ReusableCmakeInputs<'_>>) -> BuildStamp {
    use sha2::Digest;

    use crate::utils::trust_repo_cache::{add, finish};
    let mut hash = sha2::Sha256::new();
    add(&mut hash, b"omp-offload-source-provider-prepared:v1");
    if let Some(inputs) = inputs {
        add(&mut hash, inputs.source.as_bytes());
        add(&mut hash, inputs.dependency.as_bytes());
        add(&mut hash, inputs.request.as_bytes());
    } else {
        add(&mut hash, b"unknown");
    }
    BuildStamp::new(output).with_prefix("offload").add_stamp(finish(hash))
}

fn cached_omp_offload(
    stamp: &BuildStamp,
    output: &BuiltOmpOffload,
    inputs: Option<ReusableCmakeInputs<'_>>,
) -> bool {
    inputs.is_some()
        && cmake_generation_matches(stamp)
        && stamp.is_up_to_date()
        && offload_artifacts_exist(output)
}

fn build_omp_offload_install(
    stamp: &BuildStamp,
    generation: CmakeGeneration,
    config: &mut cmake::Config,
    prepared: Option<cmake::Prepared>,
    output: &BuiltOmpOffload,
) -> std::io::Result<()> {
    begin_cmake_miss(stamp, generation)?;
    if let Some(prepared) = prepared {
        prepared.build();
    } else {
        config.build();
    }
    if !offload_artifacts_exist(output) {
        return Err(std::io::Error::other(
            "OpenMP/Offload build returned without all expected regular library files",
        ));
    }
    Ok(())
}

fn record_omp_offload_completion(
    stamp: &BuildStamp,
    output: &BuiltOmpOffload,
    llvm: &LlvmOutput,
    target: TargetSelection,
    inputs: Option<ReusableCmakeInputs<'_>>,
) -> std::io::Result<()> {
    if offload_artifacts_exist(output)
        && let Some(inputs) = inputs
        && recorded_llvm_dependency_key(llvm, target).as_deref() == Some(inputs.dependency)
    {
        stamp.write()?;
    }
    Ok(())
}

// Selected path/mode requests for applying the plan; not LLVM completion evidence.
struct OffloadLlvmRequest<'a> {
    root: &'a Path,
    cmake: &'a Path,
    link_shared: bool,
}

fn omp_offload_cmake_plan(
    builder: &Builder<'_>,
    target: TargetSelection,
    output: &Path,
    llvm: OffloadLlvmRequest<'_>,
    clang: &OffloadClang,
    cxx_library: Option<&Path>,
    selected_lld: Option<&Path>,
    environment: &dyn Fn(&str) -> Option<OsString>,
    dylib_paths: impl FnOnce() -> Vec<PathBuf>,
) -> Option<CmakePlan> {
    let mut plan = CmakePlan::default();
    plan.source(builder.src.join("src/llvm-project/runtimes"));
    let mut cflags = CcFlags::default();
    if !builder.config.llvm_clang {
        cflags.push_all(format!(" -I {}", llvm.root.join("include").display()));
    }
    let mut ldflags = LdFlags::default();
    if let Some(path) = requested_lld_settings(
        &builder.config,
        target,
        selected_lld,
        llvm.root,
        llvm.link_shared,
        dylib_paths,
        &mut ldflags,
    )
    .ok()?
    {
        plan.env(helpers::dylib_path_var(), path);
    }
    if let Some(dir) = cxx_library {
        ldflags.push_all(format!("-L{}", dir.display()));
    }
    if llvm.link_shared
        && let Some(rpath) = llvm_lib_rpath(builder, target)
    {
        ldflags.push_all(rpath);
    }
    let common = resolve_cmake_plan(
        builder,
        target,
        CommonCmakeOptions { ninja: builder.selected_ninja(), use_compiler_launcher: true },
        ldflags,
        cflags,
        &[],
        environment,
    )?;
    plan.operations.extend(common.operations);
    // These intentionally override the shared helper's compiler definitions.
    plan.define("CMAKE_C_COMPILER", &clang.clang)
        .define("CMAKE_CXX_COMPILER", &clang.clangxx)
        .define("CMAKE_ASM_COMPILER", &clang.clang)
        .out_dir(output)
        .profile(get_llvm_profile(&builder.config))
        .define("LLVM_ENABLE_ASSERTIONS", "ON")
        .define("LLVM_INCLUDE_TESTS", "OFF")
        .define("OFFLOAD_INCLUDE_TESTS", "OFF")
        .define("LLVM_ROOT", llvm.root.join("build"))
        .define("LLVM_DIR", llvm.cmake)
        .define("LLVM_DEFAULT_TARGET_TRIPLE", &*target.triple);
    if let Some(dir) = &clang.cmake_dir {
        plan.define("Clang_DIR", dir);
    }
    plan.define("LLVM_ENABLE_RUNTIMES", "openmp;offload").build_target("install");
    Some(plan)
}

#[cfg(test)]
#[path = "llvm/tests/offload_tests.rs"]
mod offload_tests;

impl CommandLineStep for OmpOffload {
    type Output = BuiltOmpOffload;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/llvm-project/offload")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(OmpOffload { target: run.target });
    }

    /// Compile OpenMP offload runtimes for `target`.
    #[allow(unused)]
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        if builder.config.dry_run() {
            let dry_run = builder.config.tempdir().join("llvm-offload-dry-run");
            return BuiltOmpOffload { offload: vec![dry_run.clone()], lib_dir: dry_run };
        }
        let target = self.target;
        let llvm = builder.ensure(Llvm { target });
        let out_dir = builder.out.join(target.triple).join("offload");
        let output = omp_offload_output(&out_dir);
        builder.config.update_submodule("src/llvm-project");
        let source_root = builder.src.join("src/llvm-project");
        let source = t!(observe_cmake_sources(&source_root, &out_dir));
        let dependency = recorded_llvm_dependency_key(&llvm, target);
        let clang = selected_offload_clang(&builder.config, &llvm, target);
        let cxx_library = clang.as_ref().map(|_| query_offload_cxx_library(builder, target));
        let selected_lld = in_tree_lld_requested(&builder.config, target)
            .then(|| requested_lld_output_dir(builder, &llvm, target));
        let library_dir = cxx_library
            .as_ref()
            .and_then(|result| result.as_ref().ok())
            .and_then(|dir| dir.as_deref());
        let plan = clang.as_ref().and_then(|clang| {
            omp_offload_cmake_plan(
                builder,
                target,
                &out_dir,
                OffloadLlvmRequest {
                    root: llvm.root_dir(),
                    cmake: &llvm.cmake_dir(),
                    link_shared: llvm.link_shared(),
                },
                clang,
                library_dir,
                selected_lld.as_deref(),
                &|key| env::var_os(key),
                helpers::dylib_path,
            )
        });
        let mut cfg = plan.as_ref().map(CmakePlan::new_config);
        let prepared =
            if matches!(&cxx_library, Some(Err(OffloadCxxQueryUnavailable::CommandFailure(_)))) {
                None
            } else {
                cfg.as_ref().and_then(|cfg| cfg.try_prepare().ok())
            };
        let request = plan
            .as_ref()
            .zip(prepared.as_ref())
            .and_then(|(plan, prepared)| {
                prepared_cmake_request(b"omp-offload-prepared:v1", plan, prepared)
            })
            .filter(|_| cxx_library.as_ref().is_some_and(Result::is_ok));
        let reusable =
            reusable_cmake_inputs(source.as_deref(), dependency.as_deref(), request.as_deref());
        let stamp = omp_offload_stamp(&out_dir, reusable);
        if cached_omp_offload(&stamp, &output, reusable) {
            return output;
        }

        if clang.is_none() {
            eprintln!(
                "Building Offload requires a clang binary. Please either set `llvm.offload-clang-dir` or enable `llvm.clang` to build it."
            );
            helpers::exit_process(1);
        }
        if let Some(Err(OffloadCxxQueryUnavailable::CommandFailure(status))) = &cxx_library {
            eprintln!(
                "Offload C++ compiler query `-print-file-name=libstdc++.so` failed (status {status:?}); no output generation was changed"
            );
            helpers::exit_process(1);
        }
        let cfg = cfg.as_mut().expect("selected C/C++ compiler data is unavailable");
        builder.validate_ninja();
        if let Some(requested) = &selected_lld {
            let actual = builder.ensure(Lld { target });
            t!(verify_requested_lld(requested, &actual));
        }
        builder.info(&format!("Building OpenMP/Offload for {target}"));
        let _time = helpers::timeit(builder);
        t!(build_omp_offload_install(
            &stamp,
            if reusable.is_some() { CmakeGeneration::Known } else { CmakeGeneration::Unknown },
            cfg,
            prepared,
            &output
        ));
        t!(complete_with_unchanged_cmake_source(
            &source_root,
            &out_dir,
            reusable.map(|inputs| inputs.source),
            || record_omp_offload_completion(&stamp, &output, &llvm, target, reusable)
        ));
        output
    }
}

#[derive(Clone)]
pub struct BuiltEnzyme {
    /// Path to the libEnzyme dylib.
    enzyme: PathBuf,
}

impl BuiltEnzyme {
    pub fn enzyme_path(&self) -> PathBuf {
        self.enzyme.clone()
    }
    pub fn enzyme_filename(&self) -> String {
        self.enzyme.file_name().unwrap().to_str().unwrap().to_owned()
    }
}

#[cfg(test)]
#[path = "llvm/tests/cmake_generation_tests.rs"]
mod cmake_generation_tests;

// Trust: a completion stamp cannot substitute for the selected output artifact.
fn cached_enzyme(
    stamp: &BuildStamp,
    dylib: &Path,
    dependency: Option<&str>,
) -> Option<BuiltEnzyme> {
    (dependency.is_some()
        && cmake_generation_matches(stamp)
        && stamp.is_up_to_date()
        && dylib.is_file())
    .then(|| BuiltEnzyme { enzyme: dylib.to_owned() })
}

// Trust: one ordered requested configuration drives both cache comparison and application.
fn enzyme_cmake_plan(
    builder: &Builder<'_>,
    target: TargetSelection,
    out: &Path,
    llvm_cmake: &Path,
    environment: &dyn Fn(&str) -> Option<OsString>,
) -> Option<CmakePlan> {
    let mut cflags = CcFlags::default();
    // Enzyme tolerates LLVM deprecations until upstream removes them.
    cflags.push_all("-Wno-deprecated");
    let mut ldflags = LdFlags::default();
    if builder.config.llvm_thin_lto && !target.contains("apple") {
        ldflags.push_all("-fuse-ld=lld");
    }
    let ninja = builder.selected_ninja();
    let mut plan = resolve_cmake_plan(
        builder,
        target,
        CommonCmakeOptions { ninja, use_compiler_launcher: true },
        ldflags,
        cflags,
        &[],
        environment,
    )?;
    plan.source(builder.src.join("src/tools/enzyme/enzyme/"))
        .out_dir(out)
        .profile(get_llvm_profile(&builder.config))
        .define("LLVM_ENABLE_ASSERTIONS", "ON")
        .define("ENZYME_EXTERNAL_SHARED_LIB", "ON")
        .define("ENZYME_BC_LOADER", "OFF")
        .define("LLVM_DIR", llvm_cmake);
    Some(plan)
}

fn enzyme_stamp(out: &Path, source: &str, dependency: Option<&str>, request: &str) -> BuildStamp {
    BuildStamp::new(out)
        .with_prefix("enzyme")
        .add_stamp(source)
        .add_stamp("\nenzyme-cmake-request:v2:")
        .add_stamp(request)
        .add_stamp("\nllvm-dependency:")
        .add_stamp(dependency.unwrap_or("unknown"))
}

fn record_enzyme_completion(
    stamp: &BuildStamp,
    dylib: &Path,
    llvm: &LlvmOutput,
    target: TargetSelection,
    before: Option<&str>,
) -> std::io::Result<()> {
    if dylib.is_file()
        && let Some(before) = before
        && recorded_llvm_dependency_key(llvm, target).as_deref() == Some(before)
    {
        stamp.write()?;
    }
    Ok(())
}

#[cfg(test)]
#[path = "llvm/tests/enzyme_tests.rs"]
mod enzyme_tests;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Enzyme {
    pub target: TargetSelection,
}

impl CommandLineStep for Enzyme {
    type Output = BuiltEnzyme;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tools/enzyme/enzyme")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Enzyme { target: run.target });
    }

    /// Compile Enzyme for `target`.
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        builder.require_submodule(
            "src/tools/enzyme",
            Some("The Enzyme sources are required for autodiff."),
        );
        let target = self.target;

        if builder.config.dry_run() {
            return BuiltEnzyme { enzyme: builder.config.tempdir().join("enzyme-dryrun") };
        }

        let llvm_output = builder.ensure(Llvm { target });

        let out_dir = builder.out.join(self.target.triple).join("enzyme");
        let source_root = builder.config.src.join("src/tools/enzyme");
        let source = t!(observe_cmake_sources(&source_root, &out_dir));
        let dependency = recorded_llvm_dependency_key(&llvm_output, target);
        let plan = enzyme_cmake_plan(builder, target, &out_dir, &llvm_output.cmake_dir(), &|key| {
            env::var_os(key)
        });
        let mut cfg = plan.as_ref().map(CmakePlan::new_config);
        let prepared = cfg.as_ref().and_then(|cfg| cfg.try_prepare().ok());
        let request = plan.as_ref().zip(prepared.as_ref()).and_then(|(plan, prepared)| {
            prepared_cmake_request(b"enzyme-prepared-cmake:v1", plan, prepared)
        });
        let reusable =
            reusable_cmake_inputs(source.as_deref(), dependency.as_deref(), request.as_deref());
        let stamp = enzyme_stamp(
            &out_dir,
            source.as_deref().unwrap_or("unknown"),
            dependency.as_deref(),
            request.as_deref().unwrap_or("unresolved"),
        );
        let reusable_dependency = reusable.map(|inputs| inputs.dependency);

        let llvm_version_major = llvm::get_llvm_version_major(builder, &builder.host_llvm_config());
        let lib_ext = std::env::consts::DLL_EXTENSION;
        let libenzyme = format!("libEnzyme-{llvm_version_major}");
        let build_dir = out_dir.join(libdir(target));
        let dylib = build_dir.join(&libenzyme).with_extension(lib_ext);

        trace!("checking build stamp to see if we need to rebuild enzyme artifacts");
        if let Some(output) = cached_enzyme(&stamp, &dylib, reusable_dependency) {
            trace!(?out_dir, "enzyme build artifacts are up to date");
            return output;
        }

        let llvm_cmake_dir = llvm_output.cmake_dir();
        if !builder.config.dry_run() && !llvm_cmake_dir.is_dir() {
            builder.info(&format!(
                "WARNING: {:?} does not exist, Enzyme build will likely fail",
                llvm_cmake_dir
            ));
        }

        trace!(?target, "(re)building enzyme artifacts");
        builder.info(&format!("Building Enzyme for {target}"));
        let _time = helpers::timeit(builder);
        t!(begin_cmake_miss(
            &stamp,
            if reusable_dependency.is_some() {
                CmakeGeneration::Known
            } else {
                CmakeGeneration::Unknown
            }
        ));

        builder.validate_ninja(); // A cached artifact does not need a build tool; a miss does.
        if let Some(prepared) = prepared {
            prepared.build();
        } else {
            // Preparation unavailability grants no cache reuse. Keep the ordinary
            // build path and its existing diagnostics, without mutating it first.
            cfg.as_mut().expect("selected C/C++ compiler data is unavailable").build();
        }

        // At this point, `out_dir` should contain the built libEnzyme-<LLVM-version>.<dylib-ext>
        // file.
        if !dylib.is_file() {
            eprintln!(
                "`{libenzyme}` not found in `{}`. Either the build has failed or Enzyme was built with a wrong version of LLVM",
                build_dir.display()
            );
            helpers::exit_process(1);
        }

        t!(complete_with_unchanged_cmake_source(
            &source_root,
            &out_dir,
            reusable.map(|inputs| inputs.source),
            || record_enzyme_completion(&stamp, &dylib, &llvm_output, target, reusable_dependency)
        ));
        BuiltEnzyme { enzyme: dylib }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Lld {
    pub target: TargetSelection,
}

/// Bind source-built LLD to the selected LLVM provider. An absent export must
/// refuse here rather than let CMake search an ambient LLVM installation.
fn lld_cmake_inputs(llvm: &LlvmOutput) -> std::io::Result<PathBuf> {
    let directory = fs::canonicalize(llvm.cmake_dir())?;
    for name in ["LLVMConfig.cmake", "LLVMExports.cmake"] {
        if !fs::metadata(directory.join(name))?.is_file() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!(
                    "selected LLVM CMake export is not a file: {}",
                    directory.join(name).display()
                ),
            ));
        }
    }
    Ok(directory)
}

fn lld_cached_provider(out: &Path, selected: &Path) -> bool {
    use std::io::Read as _;
    const LIMIT: u64 = 4 * 1024 * 1024;
    let Ok(file) = fs::File::open(out.join("build/CMakeCache.txt")) else { return false };
    let mut bytes = String::new();
    if file.take(LIMIT + 1).read_to_string(&mut bytes).is_err() || bytes.len() as u64 > LIMIT {
        return false;
    }
    let mut providers = bytes.lines().filter_map(|line| line.strip_prefix("LLVM_DIR:PATH="));
    let Some(provider) = providers.next() else { return false };
    providers.next().is_none()
        && fs::canonicalize(provider).is_ok_and(|provider| provider == selected)
}

#[cfg(test)]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires: the file sits
// under llvm/tests/ so the module keeps its `lld_tests` path.
#[path = "llvm/tests/lld_tests.rs"]
mod lld_tests;

struct LldCmakeRequest<'a> {
    source: &'a Path,
    output: &'a Path,
    llvm_cmake: &'a Path,
    link_shared: bool,
    host_tablegen: Option<&'a Path>,
}
// The external LLVM CMake package adds its library directory to LLD's search
// path. That directory is not authority to replace the platform C++ runtime.
fn uses_darwin_platform_cxx_runtime(target: &str, static_cpp: bool) -> bool {
    target.contains("apple-darwin") && !static_cpp
}

fn darwin_cxx_runtime(sdk: &Path) -> Result<PathBuf, String> {
    if !sdk.is_absolute() {
        return Err("selected Darwin SDK must be absolute".into());
    }
    let runtime = sdk.join("usr/lib/libc++.tbd");
    if !runtime.is_file() {
        return Err(format!(
            "selected Darwin SDK C++ runtime is unavailable: {}",
            runtime.display()
        ));
    }
    Ok(runtime)
}

fn lld_cmake_config(
    builder: &Builder<'_>,
    target: TargetSelection,
    request: LldCmakeRequest<'_>,
) -> Result<cmake::Config, String> {
    let LldCmakeRequest { source, output, llvm_cmake, link_shared, host_tablegen } = request;
    let mut cfg = cmake::Config::new(source);
    let mut ldflags = LdFlags::default();

    // When building LLD as part of a build with instrumentation on windows, for example
    // when doing PGO on CI, cmake or clang-cl don't automatically link clang's
    // profiler runtime in. In that case, we need to manually ask cmake to do it, to avoid
    // linking errors, much like LLVM's cmake setup does in that situation.
    if builder.config.llvm_pgo.generate_profile.is_some()
        && target.is_msvc()
        && let Some(clang_cl_path) = builder.config.llvm_clang_cl.as_ref()
    {
        // Find clang's runtime library directory and push that as a search path to the
        // cmake linker flags.
        let clang_rt_dir = get_clang_cl_resource_dir(builder, clang_cl_path);
        ldflags.push_all(format!("/libpath:{}", clang_rt_dir.display()));
    }

    // LLD is built as an LLVM tool, but is distributed outside of the `llvm-tools` component,
    // which impacts where it expects to find LLVM's shared library. This causes #80703.
    //
    // LLD is distributed at "$root/lib/rustlib/$host/bin/rust-lld", but the `libLLVM-*.so` it
    // needs is distributed at "$root/lib". The default rpath of "$ORIGIN/../lib" points at the
    // lib path for LLVM tools, not the one for rust binaries.
    //
    // (The `llvm-tools` component copies the .so there for the other tools, and with that
    // component installed, one can successfully invoke `rust-lld` directly without rustup's
    // `LD_LIBRARY_PATH` overrides)
    //
    if link_shared {
        // So we inform LLD where it can find LLVM's libraries by adding an rpath entry to the
        // expected parent `lib` directory.
        if let Some(rpath) = llvm_lib_rpath(builder, target) {
            ldflags.push_all(rpath);
        }
    }

    resolve_cmake_plan(
        builder,
        target,
        CommonCmakeOptions { ninja: builder.selected_ninja(), use_compiler_launcher: true },
        ldflags,
        CcFlags::default(),
        &[],
        &|key| env::var_os(key),
    )
    .ok_or("selected C/C++ compiler data is unavailable")?
    .apply(&mut cfg);
    configure_llvm(builder, target, &mut cfg);

    // Trust: LLVM's CMake export otherwise discovers an unrelated installed
    // zstd even when rustc_llvm has an explicitly selected dependency. Bind the
    // same metadata, actual package tool, headers and archive in LLD's recipe.
    if !builder.config.dry_run()
        && let Some(directory) = builder
            .config
            .target_config
            .get(&target)
            .and_then(|config| config.llvm_zstd_pkg_config_dir.as_ref())
    {
        let provider = env::var_os("PKG_CONFIG").unwrap_or_else(|| "pkg-config".into());
        lld_zstd::bind_declared(&mut cfg, Path::new(&provider), &target.triple, directory)?;
    }

    if uses_darwin_platform_cxx_runtime(&target.triple, builder.config.llvm_static_stdcpp)
        && !builder.config.dry_run()
    {
        let cxx = builder.cxx_tool(target);
        let sdk = cxx
            .env()
            .iter()
            .find(|(key, _)| key == "SDKROOT")
            .map(|(_, value)| PathBuf::from(value))
            .or_else(|| env::var_os("SDKROOT").map(PathBuf::from));
        let sdk = match sdk {
            Some(sdk) => sdk,
            None if cfg!(target_os = "macos") => {
                let xcrun = Path::new("/usr/bin/xcrun");
                cfg.input_path(xcrun);
                PathBuf::from(crate::utils::trust_repo_tools::query(
                    xcrun,
                    &["--sdk", "macosx", "--show-sdk-path"],
                )?)
            }
            None => return Err("Darwin LLD requires an explicitly selected SDK".into()),
        };
        let runtime = darwin_cxx_runtime(&sdk)?;
        // CMake emits STANDARD_LIBRARIES as command fragments rather than typed
        // file operands. Quote one Unix argument, and separately bind its real path.
        let runtime_text = runtime.to_str().ok_or("Darwin C++ runtime path is not UTF-8")?;
        let quoted_runtime = shlex::try_quote(runtime_text)
            .map_err(|error| format!("Darwin C++ runtime path cannot be quoted: {error}"))?;
        // Do not let the C++ driver's implicit -lc++ select a second runtime
        // from the external LLVM library directories alongside the bound SDK.
        let runtime_operands = format!("-nostdlib++ {quoted_runtime}");
        cfg.define_input_path("CMAKE_OSX_SYSROOT", &sdk)
            .input_path(&runtime)
            .define("CMAKE_CXX_STANDARD_LIBRARIES", &runtime_operands);
    }

    // Re-use the same flags as llvm to control the level of debug information
    // generated for lld.
    let profile = get_llvm_profile(&builder.config);

    cfg.out_dir(output)
        .profile(profile)
        .define_input_path("LLVM_CMAKE_DIR", llvm_cmake)
        .define_input_path("LLVM_DIR", llvm_cmake)
        .define("LLVM_INCLUDE_TESTS", "OFF");

    if !builder.config.is_host_target(target) {
        // Use the host llvm-tblgen binary.
        cfg.define_input_path(
            "LLVM_TABLEGEN_EXE",
            host_tablegen.ok_or("HOST LLVM provider is unavailable for cross LLD request")?,
        );
    }

    Ok(cfg)
}

impl CommandLineStep for Lld {
    type Output = PathBuf;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/llvm-project/lld")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Lld { target: run.target });
    }

    /// Compile LLD for `target`.
    fn run(self, builder: &Builder<'_>) -> PathBuf {
        if builder.config.dry_run() {
            return PathBuf::from("lld-out-dir-test-gen");
        }
        let target = self.target;

        let llvm_output = builder.ensure(Llvm { target });

        // The `dist` step packages LLD next to LLVM's binaries for download-ci-llvm. The root path
        // we usually expect here is `./build/$triple/ci-llvm/`, with the binaries in its `bin`
        // subfolder. We check if that's the case, and if LLD's binary already exists there next to
        // `llvm-config`: if so, we can use it instead of building LLVM/LLD from source.
        if let Some(root) = ci_lld_output_dir(&llvm_output, target) {
            return root;
        }

        builder.config.update_submodule("src/llvm-project");
        let out_dir = source_lld_output_dir(builder, target);
        let source_generation = OwnSourceGeneration::observe(builder, &out_dir);
        let host =
            if builder.config.is_host_target(target) {
                None
            } else {
                match selected_host_llvm(builder, SourceResolutionMode::Lookup) {
                    Some(host) => Some(host),
                    None => {
                        t!(source_generation.refuse_linked_miss());
                        Some(selected_host_llvm(builder, SourceResolutionMode::Build).expect(
                            "genuine HOST LLVM construction must return a selected provider",
                        ))
                    }
                }
            };
        let llvm_cmake = t!(lld_cmake_inputs(&llvm_output));
        let host_tablegen = host.as_ref().map(|selected| {
            selected
                .output
                .llvm_config()
                .with_file_name("llvm-tblgen")
                .with_extension(EXE_EXTENSION)
        });
        let config = lld_cmake_config(
            builder,
            target,
            LldCmakeRequest {
                source: &builder.src.join("src/llvm-project/lld"),
                output: &out_dir,
                llvm_cmake: &llvm_cmake,
                link_shared: llvm_output.link_shared(),
                host_tablegen: host_tablegen.as_deref(),
            },
        )
        .unwrap_or_else(|error| panic!("unavailable LLD request: {error}"));
        let mut dependencies = vec![SelectedLlvmDependency::observe(llvm_output.clone(), target)];
        dependencies.extend(host);
        let recipe = ResolvedSourceRecipe::from_config(
            config,
            None,
            dependencies,
            llvm_output.link_shared(),
        )
        .unwrap_or_else(|error| panic!("unavailable LLD request: {error}"));
        let lld_stamp = source_generation.stamp("lld", &target.triple, recipe.key.as_ref());
        if recipe.key.is_some()
            && source_generation.cache_matches(
                "lld",
                &lld_stamp,
                &out_dir.join("bin").join(exe("lld", target)),
            )
            && lld_cached_provider(&out_dir, &llvm_cmake)
            && recipe.dependencies.iter().all(SelectedLlvmDependency::unchanged)
        {
            return out_dir;
        }
        t!(source_generation.refuse_linked_miss());
        let _guard = builder.msg_unstaged(Kind::Build, "LLD", target);
        let _time = helpers::timeit(builder);
        t!(validate_owned_source_build(builder));
        let ResolvedSourceRecipe { prepared, key, dependencies, .. } = recipe;
        for selected in &dependencies {
            t!(selected.ensure_selected(builder));
        }
        if host_tablegen.as_ref().is_some_and(|path| !path.is_file()) {
            panic!("required HOST llvm-tblgen is unavailable before LLD generation replacement");
        }
        let known = source_generation.observed.is_some() && key.is_some();
        let selected_inputs = dependencies
            .iter()
            .map(|selected| selected.output.root_dir().to_owned())
            .collect::<Vec<_>>();
        t!(source_generation.begin(
            &lld_stamp,
            &prepared,
            if known { CmakeGeneration::Known } else { CmakeGeneration::Unknown },
            &selected_inputs
        ));
        prepared.build();
        if known
            && dependencies.iter().all(SelectedLlvmDependency::unchanged)
            && regular_source_artifact(&out_dir.join("bin").join(exe("lld", target)))
        {
            t!(source_generation.complete(&lld_stamp, || dependencies
                .iter()
                .all(SelectedLlvmDependency::unchanged)));
        }

        out_dir
    }
}

// The ordered target set owns one generation. A target never clears another target's output.
struct CmakeTargetBuild {
    config: cmake::Config,
    prepared: Option<cmake::Prepared>,
    request: Option<String>,
}

fn sanitizer_cmake_plan(
    builder: &Builder<'_>,
    target: TargetSelection,
    source: &Path,
    output: &Path,
    llvm_config: &Path,
    environment: &dyn Fn(&str) -> Option<OsString>,
) -> Option<CmakePlan> {
    let mut plan = CmakePlan::default();
    plan.source(source)
        .profile("Release")
        .define("CMAKE_C_COMPILER_TARGET", target.triple)
        .define("COMPILER_RT_BUILD_BUILTINS", "OFF")
        .define("COMPILER_RT_BUILD_CRT", "OFF")
        .define("COMPILER_RT_BUILD_LIBFUZZER", "OFF")
        .define("COMPILER_RT_BUILD_PROFILE", "OFF")
        .define("COMPILER_RT_BUILD_SANITIZERS", "ON")
        .define("COMPILER_RT_BUILD_XRAY", "OFF")
        .define("COMPILER_RT_DEFAULT_TARGET_ONLY", "ON")
        .define("COMPILER_RT_USE_LIBCXX", "OFF")
        .define("LLVM_CONFIG_PATH", llvm_config);
    if target.contains("ohos") {
        plan.define("COMPILER_RT_USE_BUILTINS_LIBRARY", "ON");
    }
    // Darwin universal sanitizer builds do not support sccache; cc-rs' deployment
    // flag also interferes with Compiler-RT's own architecture detection.
    let use_compiler_launcher = !target.contains("apple-darwin");
    let suppressed: &[&str] =
        if target.contains("apple-darwin") { &["-mmacosx-version-min="] } else { &[] };
    let common = resolve_cmake_plan(
        builder,
        target,
        CommonCmakeOptions { ninja: builder.selected_ninja(), use_compiler_launcher },
        LdFlags::default(),
        CcFlags::default(),
        suppressed,
        environment,
    )?;
    plan.operations.extend(common.operations);
    plan.out_dir(output);
    Some(plan)
}

fn prepare_cmake_targets(base: &CmakePlan, runtimes: &[SanitizerRuntime]) -> Vec<CmakeTargetBuild> {
    runtimes
        .iter()
        .map(|runtime| {
            let mut plan = base.clone();
            plan.build_target(&runtime.cmake_target);
            let config = plan.new_config();
            let prepared = config.try_prepare().ok();
            let request = prepared.as_ref().and_then(|prepared| {
                prepared_cmake_request(b"sanitizer-target-prepared:v1", &plan, prepared)
            });
            CmakeTargetBuild { config, prepared, request }
        })
        .collect()
}

fn sanitizer_request_key(
    runtimes: &[SanitizerRuntime],
    targets: &[CmakeTargetBuild],
) -> Option<String> {
    use sha2::Digest;

    use crate::utils::trust_repo_cache::{add, finish};
    if runtimes.is_empty() || runtimes.len() != targets.len() {
        return None;
    }
    let mut hash = sha2::Sha256::new();
    add(&mut hash, b"sanitizers-ordered-target-requests:v1");
    add(&mut hash, (runtimes.len() as u64).to_le_bytes());
    for (runtime, target) in runtimes.iter().zip(targets) {
        add(&mut hash, runtime.cmake_target.as_bytes());
        add(&mut hash, runtime.path.as_os_str().as_encoded_bytes());
        add(&mut hash, runtime.name.as_bytes());
        add(&mut hash, target.request.as_deref()?.as_bytes());
    }
    Some(finish(hash))
}

fn sanitizer_stamp(output: &Path, inputs: Option<ReusableCmakeInputs<'_>>) -> BuildStamp {
    use sha2::Digest;

    use crate::utils::trust_repo_cache::{add, finish};
    let mut hash = sha2::Sha256::new();
    add(&mut hash, b"sanitizers-source-provider-prepared:v1");
    if let Some(inputs) = inputs {
        add(&mut hash, inputs.source.as_bytes());
        add(&mut hash, inputs.dependency.as_bytes());
        add(&mut hash, inputs.request.as_bytes());
    } else {
        add(&mut hash, b"unknown");
    }
    BuildStamp::new(output).with_prefix("sanitizers").add_stamp(finish(hash))
}

fn sanitizer_artifacts_exist(runtimes: &[SanitizerRuntime]) -> bool {
    !runtimes.is_empty() && runtimes.iter().all(|runtime| runtime.path.is_file())
}

fn cached_sanitizers(
    stamp: &BuildStamp,
    runtimes: &[SanitizerRuntime],
    inputs: Option<ReusableCmakeInputs<'_>>,
) -> bool {
    inputs.is_some()
        && cmake_generation_matches(stamp)
        && stamp.is_up_to_date()
        && sanitizer_artifacts_exist(runtimes)
}

fn build_cmake_target_set(
    stamp: &BuildStamp,
    generation: CmakeGeneration,
    targets: Vec<CmakeTargetBuild>,
) -> std::io::Result<()> {
    begin_cmake_miss(stamp, generation)?;
    for mut target in targets {
        if let Some(prepared) = target.prepared {
            prepared.build();
        } else {
            target.config.build();
        }
    }
    Ok(())
}

fn record_sanitizer_completion(
    stamp: &BuildStamp,
    runtimes: &[SanitizerRuntime],
    llvm: &LlvmOutput,
    host: TargetSelection,
    inputs: Option<ReusableCmakeInputs<'_>>,
) -> std::io::Result<()> {
    if sanitizer_artifacts_exist(runtimes)
        && let Some(inputs) = inputs
        && recorded_llvm_dependency_key(llvm, host).as_deref() == Some(inputs.dependency)
    {
        stamp.write()?;
    }
    Ok(())
}

#[cfg(test)]
#[path = "llvm/tests/sanitizer_tests.rs"]
mod sanitizer_tests;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sanitizers {
    pub target: TargetSelection,
}

impl CommandLineStep for Sanitizers {
    type Output = Vec<SanitizerRuntime>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("sanitizers")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Sanitizers { target: run.target });
    }

    /// Builds sanitizer runtime libraries.
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let compiler_rt_dir = builder.src.join("src/llvm-project/compiler-rt");
        if !compiler_rt_dir.exists() {
            return Vec::new();
        }

        let out_dir = builder.native_dir(self.target).join("sanitizers");
        let runtimes = supported_sanitizers(&out_dir, self.target, &builder.config.channel);

        if builder.config.dry_run() || runtimes.is_empty() {
            return runtimes;
        }

        let llvm_host = builder.ensure(Llvm { target: builder.config.host_target });

        // Compiler-RT consumes sibling CMake/LLVM/runtimes sources, not just its subtree.
        let source_root = builder.src.join("src/llvm-project");
        let source = t!(observe_cmake_sources(&source_root, &out_dir));
        let dependency = recorded_llvm_dependency_key(&llvm_host, builder.config.host_target);
        let plan = sanitizer_cmake_plan(
            builder,
            self.target,
            &compiler_rt_dir,
            &out_dir,
            llvm_host.llvm_config(),
            &|key| env::var_os(key),
        );
        let targets = plan.as_ref().map(|plan| prepare_cmake_targets(plan, &runtimes));
        let request =
            targets.as_ref().and_then(|targets| sanitizer_request_key(&runtimes, targets));
        let reusable =
            reusable_cmake_inputs(source.as_deref(), dependency.as_deref(), request.as_deref());
        let stamp = sanitizer_stamp(&out_dir, reusable);
        if cached_sanitizers(&stamp, &runtimes, reusable) {
            return runtimes;
        }

        let _guard = builder.msg_unstaged(Kind::Build, "sanitizers", self.target);
        let targets = targets.expect("selected C/C++ compiler data is unavailable");
        builder.validate_ninja();
        let _time = helpers::timeit(builder);
        t!(build_cmake_target_set(
            &stamp,
            if reusable.is_some() { CmakeGeneration::Known } else { CmakeGeneration::Unknown },
            targets
        ));
        assert!(
            sanitizer_artifacts_exist(&runtimes),
            "sanitizer build returned without all expected regular runtime files"
        );
        t!(complete_with_unchanged_cmake_source(
            &source_root,
            &out_dir,
            reusable.map(|inputs| inputs.source),
            || record_sanitizer_completion(
                &stamp,
                &runtimes,
                &llvm_host,
                builder.config.host_target,
                reusable
            )
        ));

        runtimes
    }
}

#[derive(Clone, Debug)]
pub struct SanitizerRuntime {
    /// CMake target used to build the runtime.
    pub cmake_target: String,
    /// Path to the built runtime library.
    pub path: PathBuf,
    /// Library filename that will be used rustc.
    pub name: String,
}

/// Returns sanitizers available on a given target.
fn supported_sanitizers(
    out_dir: &Path,
    target: TargetSelection,
    channel: &str,
) -> Vec<SanitizerRuntime> {
    let darwin_libs = |os: &str, components: &[&str]| -> Vec<SanitizerRuntime> {
        components
            .iter()
            .map(move |c| {
                let cmake_c = if *c == "ubsan" { "ubsan_standalone" } else { *c };
                SanitizerRuntime {
                    cmake_target: format!("clang_rt.{cmake_c}_{os}_dynamic"),
                    path: out_dir
                        .join(format!("build/lib/darwin/libclang_rt.{cmake_c}_{os}_dynamic.dylib")),
                    name: format!("librustc-{channel}_rt.{c}.dylib"),
                }
            })
            .collect()
    };

    let common_libs = |os: &str, arch: &str, components: &[&str]| -> Vec<SanitizerRuntime> {
        components
            .iter()
            .map(move |c| {
                let cmake_c = if *c == "ubsan" { "ubsan_standalone" } else { *c };
                SanitizerRuntime {
                    cmake_target: format!("clang_rt.{cmake_c}-{arch}"),
                    path: out_dir.join(format!("build/lib/{os}/libclang_rt.{cmake_c}-{arch}.a")),
                    name: format!("librustc-{channel}_rt.{c}.a"),
                }
            })
            .collect()
    };

    match &*target.triple {
        "aarch64-apple-darwin" => darwin_libs("osx", &["asan", "lsan", "tsan", "rtsan"]),
        "aarch64-apple-ios" => darwin_libs("ios", &["asan", "tsan", "rtsan"]),
        "aarch64-apple-ios-sim" => darwin_libs("iossim", &["asan", "tsan", "rtsan"]),
        "aarch64-apple-ios-macabi" => darwin_libs("osx", &["asan", "lsan", "tsan"]),
        "aarch64-unknown-fuchsia" => common_libs("fuchsia", "aarch64", &["asan"]),
        "aarch64-unknown-linux-gnu" => common_libs(
            "linux",
            "aarch64",
            &["asan", "lsan", "msan", "tsan", "hwasan", "rtsan", "ubsan", "ubsan_minimal"],
        ),
        "aarch64-unknown-linux-ohos" => {
            common_libs("linux", "aarch64", &["asan", "lsan", "msan", "tsan", "hwasan"])
        }
        "loongarch64-unknown-linux-gnu" | "loongarch64-unknown-linux-musl" => {
            common_libs("linux", "loongarch64", &["asan", "lsan", "msan", "tsan"])
        }
        "x86_64-apple-darwin" => darwin_libs("osx", &["asan", "lsan", "tsan", "rtsan"]),
        "x86_64-unknown-fuchsia" => common_libs("fuchsia", "x86_64", &["asan"]),
        "x86_64-apple-ios" => darwin_libs("iossim", &["asan", "tsan"]),
        "x86_64-apple-ios-macabi" => darwin_libs("osx", &["asan", "lsan", "tsan"]),
        "x86_64-unknown-freebsd" => common_libs("freebsd", "x86_64", &["asan", "msan", "tsan"]),
        "x86_64-unknown-netbsd" => {
            common_libs("netbsd", "x86_64", &["asan", "lsan", "msan", "tsan"])
        }
        "x86_64-unknown-illumos" => common_libs("illumos", "x86_64", &["asan"]),
        "x86_64-pc-solaris" => common_libs("solaris", "x86_64", &["asan"]),
        "x86_64-unknown-linux-gnu" => common_libs(
            "linux",
            "x86_64",
            &[
                "asan",
                "dfsan",
                "lsan",
                "msan",
                "safestack",
                "tsan",
                "rtsan",
                "ubsan",
                "ubsan_minimal",
            ],
        ),
        "x86_64-unknown-linux-gnuasan" => common_libs("linux", "x86_64", &["asan"]),
        "x86_64-unknown-linux-gnumsan" => common_libs("linux", "x86_64", &["msan"]),
        "x86_64-unknown-linux-gnutsan" => common_libs("linux", "x86_64", &["tsan"]),
        "x86_64-unknown-linux-musl" => {
            common_libs("linux", "x86_64", &["asan", "lsan", "msan", "tsan"])
        }
        "s390x-unknown-linux-gnu" => {
            common_libs("linux", "s390x", &["asan", "lsan", "msan", "tsan"])
        }
        "s390x-unknown-linux-musl" => {
            common_libs("linux", "s390x", &["asan", "lsan", "msan", "tsan"])
        }
        "x86_64-unknown-linux-ohos" => {
            common_libs("linux", "x86_64", &["asan", "lsan", "msan", "tsan"])
        }
        _ => Vec::new(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CrtBeginEnd {
    pub target: TargetSelection,
}

impl CommandLineStep for CrtBeginEnd {
    type Output = PathBuf;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/llvm-project/compiler-rt/lib/builtins")
    }

    fn make_run(run: RunConfig<'_>) {
        if run.target.needs_crt_begin_end() {
            run.builder.ensure(CrtBeginEnd { target: run.target });
        }
    }

    /// Build crtbegin.o/crtend.o for musl target.
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        builder.require_submodule(
            "src/llvm-project",
            Some("The LLVM sources are required for the CRT from `compiler-rt`."),
        );

        let out_dir = builder.native_dir(self.target).join("crt");

        if builder.config.dry_run() {
            return out_dir;
        }

        let crtbegin_src = builder.src.join("src/llvm-project/compiler-rt/lib/builtins/crtbegin.c");
        let crtend_src = builder.src.join("src/llvm-project/compiler-rt/lib/builtins/crtend.c");
        if up_to_date(&crtbegin_src, &out_dir.join("crtbeginS.o"))
            && up_to_date(&crtend_src, &out_dir.join("crtendS.o"))
        {
            return out_dir;
        }

        let _guard = builder.msg_unstaged(Kind::Build, "crtbegin.o and crtend.o", self.target);
        t!(fs::create_dir_all(&out_dir));

        let mut cfg = cc::Build::new();

        if let Some(ar) = builder.ar(self.target) {
            cfg.archiver(ar);
        }
        cfg.compiler(builder.cc(self.target));
        cfg.cargo_metadata(false)
            .out_dir(&out_dir)
            .target(&self.target.triple)
            .host(&builder.config.host_target.triple)
            .warnings(false)
            .debug(false)
            .opt_level(3)
            .file(crtbegin_src)
            .file(crtend_src);

        // Those flags are defined in src/llvm-project/compiler-rt/lib/builtins/CMakeLists.txt
        // Currently only consumer of those objects is musl, which use .init_array/.fini_array
        // instead of .ctors/.dtors
        cfg.flag("-std=c11")
            .define("CRT_HAS_INITFINI_ARRAY", None)
            .define("EH_USE_FRAME_REGISTRY", None);

        let objs = cfg.compile_intermediates();
        assert_eq!(objs.len(), 2);
        for obj in objs {
            let base_name = unhashed_basename(&obj);
            assert!(base_name == "crtbegin" || base_name == "crtend");
            t!(fs::copy(&obj, out_dir.join(format!("{base_name}S.o"))));
            t!(fs::rename(&obj, out_dir.join(format!("{base_name}.o"))));
        }

        out_dir
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Libunwind {
    pub target: TargetSelection,
}

impl CommandLineStep for Libunwind {
    type Output = PathBuf;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/llvm-project/libunwind")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Libunwind { target: run.target });
    }

    /// Build libunwind.a
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        builder.require_submodule(
            "src/llvm-project",
            Some("The LLVM sources are required for libunwind."),
        );

        if builder.config.dry_run() {
            return PathBuf::new();
        }

        let out_dir = builder.native_dir(self.target).join("libunwind");
        let root = builder.src.join("src/llvm-project/libunwind");

        if up_to_date(&root, &out_dir.join("libunwind.a")) {
            return out_dir;
        }

        let _guard = builder.msg_unstaged(Kind::Build, "libunwind.a", self.target);
        t!(fs::create_dir_all(&out_dir));

        let mut cc_cfg = cc::Build::new();
        let mut cpp_cfg = cc::Build::new();

        cpp_cfg.cpp(true);
        cpp_cfg.cpp_set_stdlib(None);
        cpp_cfg.flag("-nostdinc++");
        cpp_cfg.flag("-fno-exceptions");
        cpp_cfg.flag("-fno-rtti");
        cpp_cfg.flag_if_supported("-fvisibility-global-new-delete-hidden");

        for cfg in [&mut cc_cfg, &mut cpp_cfg].iter_mut() {
            if let Some(ar) = builder.ar(self.target) {
                cfg.archiver(ar);
            }
            cfg.target(&self.target.triple);
            cfg.host(&builder.config.host_target.triple);
            cfg.warnings(false);
            cfg.debug(false);
            // get_compiler() need set opt_level first.
            cfg.opt_level(3);
            cfg.flag("-fstrict-aliasing");
            cfg.flag("-funwind-tables");
            cfg.flag("-fvisibility=hidden");
            cfg.define("_LIBUNWIND_DISABLE_VISIBILITY_ANNOTATIONS", None);
            cfg.define("_LIBUNWIND_IS_NATIVE_ONLY", "1");
            cfg.include(root.join("include"));
            cfg.cargo_metadata(false);
            cfg.out_dir(&out_dir);

            if self.target.contains("x86_64-fortanix-unknown-sgx") {
                cfg.flag("-fno-stack-protector");
                cfg.flag("-ffreestanding");
                cfg.flag("-fexceptions");

                // easiest way to undefine since no API available in cc::Build to undefine
                cfg.flag("-U_FORTIFY_SOURCE");
                cfg.define("_FORTIFY_SOURCE", "0");
                cfg.define("RUST_SGX", "1");
                cfg.define("__NO_STRING_INLINES", None);
                cfg.define("__NO_MATH_INLINES", None);
                cfg.define("_LIBUNWIND_IS_BAREMETAL", None);
                cfg.define("NDEBUG", None);
            }
            if self.target.is_windows() {
                cfg.define("_LIBUNWIND_HIDE_SYMBOLS", "1");
            }
        }

        cc_cfg.compiler(builder.cc(self.target));
        if let Ok(cxx) = builder.cxx(self.target) {
            cpp_cfg.compiler(cxx);
        } else {
            cc_cfg.compiler(builder.cc(self.target));
        }

        // Don't set this for clang
        // By default, Clang builds C code in GNU C17 mode.
        // By default, Clang builds C++ code according to the C++98 standard,
        // with many C++11 features accepted as extensions.
        if cc_cfg.get_compiler().is_like_gnu() {
            cc_cfg.flag("-std=c99");
        }
        if cpp_cfg.get_compiler().is_like_gnu() {
            cpp_cfg.flag("-std=c++11");
        }

        if self.target.contains("x86_64-fortanix-unknown-sgx") || self.target.contains("musl") {
            // use the same GCC C compiler command to compile C++ code so we do not need to setup the
            // C++ compiler env variables on the builders.
            // Don't set this for clang++, as clang++ is able to compile this without libc++.
            if cpp_cfg.get_compiler().is_like_gnu() {
                cpp_cfg.cpp(false);
                cpp_cfg.compiler(builder.cc(self.target));
            }
        }

        let mut c_sources = vec![
            "Unwind-sjlj.c",
            "UnwindLevel1-gcc-ext.c",
            "UnwindLevel1.c",
            "UnwindRegistersRestore.S",
            "UnwindRegistersSave.S",
        ];

        let cpp_sources = vec!["Unwind-EHABI.cpp", "Unwind-seh.cpp", "libunwind.cpp"];
        let cpp_len = cpp_sources.len();

        if self.target.contains("x86_64-fortanix-unknown-sgx") {
            c_sources.push("UnwindRustSgx.c");
        }

        for src in c_sources {
            cc_cfg.file(root.join("src").join(src).canonicalize().unwrap());
        }

        for src in &cpp_sources {
            cpp_cfg.file(root.join("src").join(src).canonicalize().unwrap());
        }

        cpp_cfg.compile("unwind-cpp");

        // FIXME: https://github.com/alexcrichton/cc-rs/issues/545#issuecomment-679242845
        let mut count = 0;
        let mut files = fs::read_dir(&out_dir)
            .unwrap()
            .map(|entry| entry.unwrap().path().canonicalize().unwrap())
            .collect::<Vec<_>>();
        files.sort();
        for file in files {
            if file.is_file() && file.extension() == Some(OsStr::new("o")) {
                // Object file name without the hash prefix is "Unwind-EHABI", "Unwind-seh" or "libunwind".
                let base_name = unhashed_basename(&file);
                if cpp_sources.iter().any(|f| *base_name == f[..f.len() - 4]) {
                    cc_cfg.object(&file);
                    count += 1;
                }
            }
        }
        assert_eq!(cpp_len, count, "Can't get object files from {out_dir:?}");

        cc_cfg.compile("unwind");
        out_dir
    }
}

/// Returns the path to `FileCheck` LLVM binary for the specified target.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FileCheck {
    pub target: TargetSelection,
}

impl Step for FileCheck {
    type Output = PathBuf;

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let target_config = builder.config.target_config.get(&self.target);

        // The target configured filecheck, prefer it
        if let Some(s) = target_config.and_then(|c| c.llvm_filecheck.as_ref()) {
            return s.clone();
        };

        // There is a LLVM config set, take filecheck from it
        if let Some(llvm_config) = target_config.and_then(|c| c.llvm_config.as_ref()) {
            // We can only execute llvm-config if we're on the same host target
            return if builder.is_host_target(self.target) {
                let llvm_bindir =
                    command(llvm_config).arg("--bindir").run_capture_stdout(builder).stdout();
                let filecheck = Path::new(llvm_bindir.trim()).join(exe("FileCheck", self.target));

                if filecheck.exists() {
                    filecheck
                } else {
                    // On Fedora the system LLVM installs FileCheck in the
                    // llvm subdirectory of the libdir.
                    let llvm_libdir =
                        command(llvm_config).arg("--libdir").run_capture_stdout(builder).stdout();
                    let lib_filecheck = Path::new(llvm_libdir.trim())
                        .join("llvm")
                        .join(exe("FileCheck", self.target));
                    if lib_filecheck.exists() {
                        lib_filecheck
                    } else {
                        // Return the most normal file name, even though
                        // it doesn't exist, so that any error message
                        // refers to that.
                        filecheck
                    }
                }
            } else {
                // In other cases, just guess that Filecheck is available in the same directory
                // as the llvm-config
                llvm_config.parent().unwrap().join(exe("FileCheck", self.target))
            };
        }
        // Here we take the filecheck from LLVM directly
        let llvm_output = builder.ensure(Llvm { target: self.target });
        llvm_output.root_dir().join("bin").join(exe("FileCheck", self.target))
    }
}

/// Result of building TPDE artifacts.
///
/// Currently only tpde-plugin.so is consumed elsewhere.
#[derive(Clone)]
pub struct TpdeOutput {
    tpde_root_dir: PathBuf,
    tpde_plugin_path: PathBuf,
}

impl TpdeOutput {
    /// Path to tpde-plugin.so
    pub fn plugin_path(&self) -> &Path {
        &self.tpde_plugin_path
    }
}

pub struct TpdeBuildInfo {
    stamp: BuildStamp,
    output: TpdeOutput,
}

pub enum TpdeBuildStatus {
    AlreadyBuilt(TpdeOutput),
    ShouldBuild(TpdeBuildInfo),
}

// Trust: old stamps could predate actual CMake execution, even with a stale plugin present.
const TPDE_BUILD_RECIPE: &str = "\ncmake:tpde-plugin:configure-and-build:v1";

// Trust: bounded recorded evidence, not a complete LLVM artifact/proof identity.
fn completed_llvm_dependency_key(llvm: &LlvmOutput, target: TargetSelection) -> Option<String> {
    if llvm.kind() != LlvmKind::BuiltLocally || !llvm.link_shared() {
        return None;
    }
    recorded_llvm_dependency_key(llvm, target)
}

// Trust: the real owner calls this only after build and strip have returned.
// The recorded observations do not prove continuous or complete artifact identity.
fn record_tpde_completion(
    stamp: &BuildStamp,
    llvm: &LlvmOutput,
    target: TargetSelection,
    before: Option<&str>,
) -> std::io::Result<()> {
    if let Some(before) = before
        && completed_llvm_dependency_key(llvm, target).as_deref() == Some(before)
    {
        stamp.write()?;
    }
    Ok(())
}

/// Return build status of TPDE, considering only the locally built TPDE.
///
/// Calling this function should never attempt to checkout the TPDE submodule.
fn get_locally_built_tpde_build_status(
    builder: &Builder<'_>,
    target: TargetSelection,
    reusable: Option<ReusableCmakeInputs<'_>>,
    strip_requested: bool,
) -> TpdeBuildStatus {
    let res = tpde_output(builder, target);

    // Rebuild if build options change
    let mut stamp = BuildStamp::new(&res.tpde_root_dir)
        .with_prefix("tpde")
        .add_stamp(reusable.map(|inputs| inputs.source).unwrap_or("unknown"))
        .add_stamp(TPDE_BUILD_RECIPE)
        .add_stamp("\ntpde-cmake-request:")
        .add_stamp(reusable.map(|inputs| inputs.request).unwrap_or("unknown"))
        .add_stamp("\nstrip:")
        .add_stamp(strip_requested);
    if let Some(inputs) = reusable {
        stamp = stamp.add_stamp("\nllvm-dependency:").add_stamp(inputs.dependency);
    }

    if reusable.is_some()
        && cmake_generation_matches(&stamp)
        && stamp.is_up_to_date()
        && fs::symlink_metadata(res.plugin_path()).is_ok_and(|metadata| metadata.is_file())
    {
        return TpdeBuildStatus::AlreadyBuilt(res);
    }

    TpdeBuildStatus::ShouldBuild(TpdeBuildInfo { stamp, output: res })
}

/// Output directory of *locally built* TPDE for the given `target`.
/// Should only be used within this module, when building TPDE.
/// Otherwise, you should ensure the `Tpde` step and read its root directory.
fn tpde_output_dir(builder: &Builder<'_>, target: TargetSelection) -> PathBuf {
    builder.config.out.join(target).join("tpde")
}

// Trust: use the same paths for a planned result and actual local cache/build output.
fn tpde_output(builder: &Builder<'_>, target: TargetSelection) -> TpdeOutput {
    let out_dir = tpde_output_dir(builder, target);
    TpdeOutput {
        tpde_plugin_path: out_dir.join("build").join("tpde-llvm").join("tpde-plugin.so"),
        tpde_root_dir: out_dir,
    }
}

fn tpde_cmake_plan(
    builder: &Builder<'_>,
    target: TargetSelection,
    out: &Path,
    llvm_cmake: &Path,
    llvm_root: &Path,
    selected_lld: Option<&Path>,
    lookup: &dyn Fn(&str) -> Option<OsString>,
    dylib_paths: impl FnOnce() -> Vec<PathBuf>,
) -> Option<CmakePlan> {
    let mut plan = CmakePlan::default();
    plan.source(builder.src.join("src/tpde"))
        .out_dir(out)
        .profile(get_llvm_profile(&builder.config))
        .define("TPDE_ENABLE_ASSERTIONS", if builder.config.llvm_assertions { "ON" } else { "OFF" })
        .define("TPDE_ENABLE_LLVM", "ON")
        .define("TPDE_ENABLE_ENCODEGEN", "ON")
        .define("TPDE_INCLUDE_TESTS", "OFF")
        .define("TPDE_ENABLE_ASAN", "OFF")
        .define("TPDE_LOGGING", "OFF")
        .define("TPDE_ENABLE_COVERAGE", "OFF")
        .define("TPDE_BUILD_DOCS", "OFF")
        .define("TPDE_ENABLE_EH", "OFF")
        .define("LLVM_DIR", llvm_cmake);
    let mut ldflags = LdFlags::default();
    if let Some(paths) = requested_lld_settings(
        &builder.config,
        target,
        selected_lld,
        llvm_root,
        true,
        dylib_paths,
        &mut ldflags,
    )
    .ok()?
    {
        plan.env(helpers::dylib_path_var(), paths);
    }
    let ninja = builder.selected_ninja();
    let common = resolve_cmake_plan(
        builder,
        target,
        CommonCmakeOptions { ninja, use_compiler_launcher: true },
        ldflags,
        CcFlags::default(),
        &[],
        lookup,
    )?;
    // Preserve TPDE's old own-definitions/linker-env-before-common ordering.
    plan.operations.extend(common.operations);
    plan.build_target("tpde-plugin");
    Some(plan)
}

fn verify_requested_lld(requested: &Path, actual: &Path) -> std::io::Result<()> {
    if requested == actual {
        Ok(())
    } else {
        Err(std::io::Error::other(format!(
            "selected LLD output changed from {} to {}",
            requested.display(),
            actual.display()
        )))
    }
}

#[cfg(test)]
#[path = "llvm/tests/tpde_tests.rs"]
mod tpde_tests;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Tpde {
    pub target: TargetSelection,
}

impl CommandLineStep for Tpde {
    type Output = TpdeOutput;

    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src/tpde").alias("tpde")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Tpde { target: run.target });
    }

    /// Compile TPDE for `target`.
    fn run(self, builder: &Builder<'_>) -> TpdeOutput {
        let target = self.target;
        if !target.contains("linux") {
            builder.info(&format!("WARNING: host target {target} not supported by TPDE"));
        }
        let llvm = builder.ensure(Llvm { target });
        if llvm.kind() != LlvmKind::BuiltLocally || !llvm.link_shared() {
            // Due to current limitations with the way LLVM configures CMake exports, it is not possible to use CI LLVM.
            // FIXME: experiment with LLVM_OMIT_EXPORTS_FROM_CONFIG=OFF and changing library search paths as described in https://github.com/rust-lang/rust/pull/163731#discussion_r4286684608,
            // or (preferred) wait until upstream LLVM patches have landed to decouple static exports from dynamic exports in the CMake config
            panic!(
                "TPDE currently requires building with a locally built LLVM and `llvm.link-shared = true` in bootstrap"
            );
        }
        // Trust: validate the selected provider above, but do not mutate TPDE
        // inputs, stamps or output directories while planning its graph.
        if builder.config.dry_run() {
            if in_tree_lld_requested(&builder.config, target) {
                builder.ensure(Lld { target });
            }
            return tpde_output(builder, target);
        }
        let llvm_dependency = completed_llvm_dependency_key(&llvm, target);
        builder.config.update_submodule("src/tpde");
        let output = tpde_output(builder, target);
        let source_root = builder.config.src.join("src/tpde");
        let source = t!(observe_cmake_sources(&source_root, &output.tpde_root_dir));
        let selected_lld = in_tree_lld_requested(&builder.config, target)
            .then(|| source_lld_output_dir(builder, target));
        let plan = tpde_cmake_plan(
            builder,
            target,
            &output.tpde_root_dir,
            &llvm.cmake_dir(),
            llvm.root_dir(),
            selected_lld.as_deref(),
            &|key| env::var_os(key),
            helpers::dylib_path,
        );
        let mut cfg = plan.as_ref().map(CmakePlan::new_config);
        let prepared = cfg.as_ref().and_then(|cfg| cfg.try_prepare().ok());
        let request = plan.as_ref().zip(prepared.as_ref()).and_then(|(plan, prepared)| {
            prepared_cmake_request(b"tpde-prepared-cmake:v1", plan, prepared)
        });
        let reusable = reusable_cmake_inputs(
            source.as_deref(),
            llvm_dependency.as_deref(),
            request.as_deref(),
        );
        let strip_requested =
            builder.config.llvm_optimize && !builder.config.llvm_release_debuginfo;
        let TpdeBuildInfo { stamp, output } =
            match get_locally_built_tpde_build_status(builder, target, reusable, strip_requested) {
                TpdeBuildStatus::AlreadyBuilt(p) => return p,
                TpdeBuildStatus::ShouldBuild(m) => m,
            };
        let _guard = builder.msg_unstaged(Kind::Build, "TPDE", target);
        let cfg = cfg.as_mut().expect("selected C/C++ compiler data is unavailable");
        builder.validate_ninja();
        if let Some(requested) = &selected_lld {
            let actual = builder.ensure(Lld { target });
            t!(verify_requested_lld(requested, &actual));
        }
        let _time = helpers::timeit(builder);
        t!(begin_cmake_miss(
            &stamp,
            if reusable.is_some() { CmakeGeneration::Known } else { CmakeGeneration::Unknown }
        ));
        if let Some(prepared) = prepared {
            prepared.build();
        } else {
            cfg.build();
        }

        // When building TPDE as a shared library on linux, it can contain unexpected debuginfo:
        // some can come from the C++ standard library. Unless we're explicitly requesting TPDE to
        // be built with debuginfo, strip it away after the fact, to make dist artifacts smaller.
        if strip_requested {
            // If the shared library exists in TPDE's `/build/tpde-llvm` folder, strip its
            // debuginfo.
            crate::core::build_steps::compile::strip_debug(builder, target, output.plugin_path());
        }

        // Trust: unknown or changed completed evidence permits this build, but
        // cannot authorize reusable dependent completion.
        t!(complete_with_unchanged_cmake_source(
            &source_root,
            &output.tpde_root_dir,
            reusable.map(|inputs| inputs.source),
            || record_tpde_completion(
                &stamp,
                &llvm,
                target,
                reusable.map(|inputs| inputs.dependency)
            )
        ));

        output
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("tpde", self.target))
    }
}

#[cfg(all(test, unix))]
#[path = "llvm/tests/vcs_constructor_tests.rs"]
mod vcs_constructor_tests;

#[cfg(all(test, unix))]
#[path = "llvm/tests/llvm_recipe_tests.rs"]
mod llvm_recipe_tests;

#[cfg(test)]
#[path = "llvm/tests/llvm_source_guard_tests.rs"]
mod llvm_source_guard_tests;

#[cfg(test)]
#[path = "llvm/tests/llvm_build_identity_tests.rs"]
mod llvm_build_identity_tests;
#[cfg(test)]
#[path = "llvm/tests/llvm_recipe_guard_tests.rs"]
mod llvm_recipe_guard_tests;

#[cfg(test)]
fn fixture_install_manifest(root: &Path, members: &[&Path]) {
    fs::create_dir_all(root.join("build")).unwrap();
    let rows = members
        .iter()
        .map(|path| fs::canonicalize(path).unwrap().to_str().unwrap().to_owned())
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(root.join("build/install_manifest.txt"), format!("{rows}\n")).unwrap();
}
