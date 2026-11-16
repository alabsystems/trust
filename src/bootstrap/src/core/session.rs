use std::cell::Cell;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Display;
use std::ops::Deref;
use std::path::{Path, PathBuf};
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use std::sync::Arc;
use std::sync::OnceLock;
use std::time::{Instant, SystemTime};
use std::{env, fs, io, str};

use build_helper::ci::gha;
use termcolor::{ColorChoice, StandardStream, WriteColor};
#[cfg(feature = "tracing")]
use tracing::{instrument, span};

use crate::core::backend::CodegenBackendKind;
use crate::core::build_steps::format::InternalRustfmt;
use crate::core::build_steps::test::TestTarget;
use crate::core::build_steps::vendor::VENDOR_DIR;
use crate::core::builder::{Builder, Kind};
use crate::core::compiler::Compiler;
use crate::core::config::flags::{self, Subcommand};
// Trust: the Session defaults must use the same seed identities as Config and x.py.
use crate::core::config::{
    BootstrapOverrideLld, Config, DryRun, LlvmLibunwind, TargetSelection,
    default_initial_cargo_path, default_initial_rustc_path, default_initial_rustdoc_path,
};
use crate::core::download::{DownloadContext, download_beta_toolchain};
use crate::core::metadata::Crate;
#[cfg(feature = "tracing")]
use crate::trace_io;
use crate::utils::build_stamp::BuildStamp;
use crate::utils::channel::GitInfo;
use crate::utils::exec::{BootstrapCommand, ExecutionContext, tool_metadata_command};
use crate::utils::helpers::{
    self, dir_is_empty, exe, is_symlink_dir, libdir, set_file_times, split_debuginfo, symlink_dir,
    t,
};
// Trust: TB1.
use crate::utils::trust_source_identity;
use crate::{debug, exit, trace};

/// Global configuration for the build system.
///
/// This structure transitively contains all configuration for the build system.
/// All filesystem-encoded configuration is in `config`, all flags are in
/// `flags`, and then parsed or probed information is listed in the keys below.
pub(crate) struct Session {
    /// User-specified configuration from command-line flags and `bootstrap.toml`.
    pub(crate) config: Config,
    pub(crate) completed_runtime: std::cell::RefCell<
        Option<std::sync::Arc<crate::core::build_steps::frontend_runtime::CompletedRuntime>>,
    >,
    /// Trust: a retained test runtime is owned independently of every build compiler.
    pub(crate) compiler_test_fixture:
        Option<crate::utils::retained_compiler_fixture::RetainedCompilerTestFixture>,
    // Trust: share the actual original guards with completed runtime owners.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    pub(crate) runtime_build_ownership:
        Option<std::sync::Arc<crate::core::build_steps::frontend_runtime::BuildOwnership>>,
    // Trust: actual original Full guards outlive every normal Step. This is
    // not an independently constructed runtime, shim, SDK or release witness.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    _original_compilation: Option<Arc<crate::engine::OriginalBootstrapCompilation>>,

    // Version information
    pub(crate) version: String,
    // Trust: the Rust-line version this tree is aligned to
    // (`src/rust-compat-version`); it, not Trust's own `version`, is what
    // `rust_release`/`rust_version` report and what build scripts parse.
    pub(crate) rust_compat_version: String,

    // Properties derived from the above configuration
    pub(crate) bootstrap_out: PathBuf,
    pub(crate) fail_fast: bool,
    pub(crate) test_target: TestTarget,
    pub(crate) verbosity: usize,

    pub(crate) initial_rustc: PathBuf,
    pub(crate) initial_rustdoc: PathBuf,
    pub(crate) initial_cargo: PathBuf,
    pub(crate) initial_lld: PathBuf,
    pub(crate) initial_relative_libdir: PathBuf,
    pub(crate) initial_sysroot: PathBuf,

    // Runtime state filled in later on
    // C/C++ compilers and archiver for all targets
    pub(crate) cc: HashMap<TargetSelection, cc::Tool>,
    pub(crate) cxx: HashMap<TargetSelection, cc::Tool>,
    pub(crate) opaque_cc_operands: HashSet<TargetSelection>,
    pub(crate) ar: HashMap<TargetSelection, PathBuf>,
    pub(crate) ranlib: HashMap<TargetSelection, PathBuf>,
    pub(crate) wasi_sdk_path: Option<PathBuf>,

    // Miscellaneous
    // allow bidirectional lookups: both name -> path and path -> name
    pub(crate) crates: HashMap<String, Crate>,
    pub(crate) crate_paths: HashMap<PathBuf, String>,
    pub(crate) prerelease_version: Cell<Option<u32>>,
    // Trust: what this invocation's version names (`Build::naming`).
    naming: OnceLock<trust_source_identity::Naming>,

    #[cfg(feature = "build-metrics")]
    pub(crate) metrics: crate::utils::metrics::BuildMetrics,

    #[cfg(feature = "tracing")]
    pub(crate) step_graph: std::cell::RefCell<crate::utils::step_graph::StepGraph>,
}

impl Deref for Session {
    type Target = Config;

    fn deref(&self) -> &Self::Target {
        &self.config
    }
}

/// When building Rust various objects are handled differently.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum DependencyType {
    /// Libraries originating from proc-macros.
    Host,
    /// Typical Rust libraries.
    Target,
    /// Non Rust libraries and objects shipped to ease usage of certain targets.
    TargetSelfContained,
}

/// The various "modes" of invoking Cargo.
///
/// These entries currently correspond to the various output directories of the
/// build system, with each mod generating output in a different directory.
#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    /// Build the standard library, placing output in the "stageN-std" directory.
    Std,

    /// Build librustc, and compiler libraries, placing output in the "stageN-rustc" directory.
    Rustc,

    /// Build a codegen backend for rustc, placing the output in the "stageN-codegen" directory.
    Codegen,

    /// Build a tool, placing output in the "bootstrap-seed-tools"
    /// directory. This is for miscellaneous sets of tools that extend
    /// bootstrap.
    ///
    /// These tools are intended to be only executed on the host system that
    /// invokes bootstrap, and they thus cannot be cross-compiled.
    ///
    /// They are always built using the stage0 compiler, and they
    /// can be compiled with stable Rust.
    ///
    /// These tools also essentially do not participate in staging.
    ToolBootstrap,

    /// Build a cross-compilable helper tool. These tools do not depend on unstable features or
    /// compiler internals, but they might be cross-compilable (so we cannot build them using the
    /// stage0 compiler, unlike `ToolBootstrap`).
    ///
    /// Some of these tools are also shipped in our `dist` archives.
    /// While we could compile them using the stage0 compiler when not cross-compiling, we instead
    /// use the in-tree compiler (and std) to build them, so that we can ship e.g. std security
    /// fixes and avoid depending fully on stage0 for the artifacts that we ship.
    ///
    /// This mode is used e.g. for linkers and linker tools invoked by rustc on its host target.
    ToolTarget,

    /// Build a tool which uses the locally built std, placing output in the
    /// "stageN-tools" directory. Its usage is quite rare; historically it was
    /// needed by compiletest, but now it is mainly used by `test-float-parse`.
    ToolStd,

    /// Build a tool which uses the `rustc_private` mechanism, and thus
    /// the locally built rustc rlib artifacts,
    /// placing the output in the "stageN-tools" directory. This is used for
    /// everything that links to rustc as a library, such as rustdoc, clippy,
    /// rustfmt, miri, etc.
    ToolRustcPrivate,
}

impl Mode {
    pub(crate) fn must_support_dlopen(&self) -> bool {
        match self {
            Mode::Std | Mode::Codegen => true,
            Mode::ToolBootstrap
            | Mode::ToolRustcPrivate
            | Mode::ToolStd
            | Mode::ToolTarget
            | Mode::Rustc => false,
        }
    }
}

/// When `rust.rust_remap_debuginfo` is requested, the compiler needs to know how to
/// opportunistically unremap compiler vs non-compiler sources. We use two schemes,
/// [`RemapScheme::Compiler`] and [`RemapScheme::NonCompiler`].
pub(crate) enum RemapScheme {
    /// The [`RemapScheme::Compiler`] scheme will remap to `/rustc-dev/{hash}`.
    Compiler,
    /// The [`RemapScheme::NonCompiler`] scheme will remap to `/rustc/{hash}`.
    NonCompiler,
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CLang {
    C,
    Cxx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FileType {
    /// An executable binary file (like a `.exe`).
    Executable,
    /// A native, binary library file (like a `.so`, `.dll`, `.a`, `.lib` or `.o`).
    NativeLibrary,
    /// An executable (non-binary) script file (like a `.py` or `.sh`).
    Script,
    /// Any other regular file that is non-executable.
    Regular,
}

impl FileType {
    /// Whether `copy_link` may install a file of this type as a hard link.
    ///
    /// Trust: not an executable when bootstrap runs on macOS. dyld can resolve the main
    /// executable to ANOTHER hard link of the same file and computes `@loader_path` from
    /// that path. A sysroot's `bin/rustc` shares its inode with the cargo target-dir
    /// original, so it then looks for `librustc_driver` in `<target-dir>/release/../lib`
    /// and aborts before `main`. Measured 2026-09-28 on Darwin 25.6: `x.py test --stage 2`
    /// failed its assembled-compiler smoke test with dyld's "Referenced from:
    /// .../stage2-rustc/aarch64-apple-darwin/release/rustc-main", and a freshly linked
    /// `rustc-main` aborted that way in 45 of 60 runs while a copy aborted in none of 30.
    /// Every sysroot tool that loads `librustc_driver` is exposed, not just `rustc`.
    ///
    /// The fallback is `fs::copy`, which clones on APFS, so the copy shares data blocks
    /// and the sysroot still owns an independent file (the property `scripts/slim_build.py`
    /// relies on).
    pub(crate) fn may_hard_link(self) -> bool {
        !(cfg!(target_os = "macos") && self == FileType::Executable)
    }

    /// Get Unix permissions appropriate for this file type.
    pub(crate) fn perms(self) -> u32 {
        match self {
            FileType::Executable | FileType::Script => 0o755,
            FileType::Regular | FileType::NativeLibrary => 0o644,
        }
    }

    pub(crate) fn could_have_split_debuginfo(self) -> bool {
        match self {
            FileType::Executable | FileType::NativeLibrary => true,
            FileType::Script | FileType::Regular => false,
        }
    }
}

macro_rules! forward {
    ($( $fn:ident( $($param:ident: $ty:ty),* ) $( -> $ret:ty)? ),+ $(,)? ) => {
        impl Session {
            $(
                pub(crate) fn $fn(&self, $($param: $ty),* ) $( -> $ret)? {
                    self.config.$fn( $($param),* )
                }
            )+
        }
    }
}

forward! {
    do_if_verbose(f: impl Fn()),
    is_verbose() -> bool,
    create(path: &Path, s: &str),
    remove(f: &Path),
    tempdir() -> PathBuf,
    download_rustc() -> bool,
}

/// An alternative way of specifying what target and stage is involved in some bootstrap activity.
/// Ideally using a `Compiler` directly should be preferred.
pub(crate) struct TargetAndStage {
    target: TargetSelection,
    stage: u32,
}

impl From<(TargetSelection, u32)> for TargetAndStage {
    fn from((target, stage): (TargetSelection, u32)) -> Self {
        Self { target, stage }
    }
}

impl From<Compiler> for TargetAndStage {
    fn from(compiler: Compiler) -> Self {
        Self { target: compiler.host, stage: compiler.stage }
    }
}

// Trust: only an opaque original configuration can select the qualified
// private seed. Ordinary Session construction retains its existing readiness.
enum InitialRuntime {
    Ordinary,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    Original {
        owner: Arc<crate::engine::OriginalBootstrapCompilation>,
        stage0: crate::utils::metadata_scheduler::host_graph::Stage0Selection,
    },
}

impl Session {
    /// Creates a new set of build configuration from the `flags` on the command
    /// line and the filesystem `config`.
    ///
    /// By default all build output will be placed in the current directory.
    pub(crate) fn new(config: Config) -> Session {
        Self::new_with_shims(config, None)
    }

    pub(crate) fn new_with_shims(config: Config, supplied_shims: Option<PathBuf>) -> Session {
        Self::new_with_runtime(config, supplied_shims, InitialRuntime::Ordinary)
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn new_with_original(
        configured: crate::utils::metadata_scheduler::host_graph::OriginalBootstrapConfiguration,
        supplied_shims: PathBuf,
    ) -> Result<Session, String> {
        let (config, owner, stage0) = configured.into_parts();
        let ownership = owner.build_ownership().map_err(|error| error.to_string())?;
        let mut session = Self::new_with_runtime(
            config,
            Some(supplied_shims),
            InitialRuntime::Original { owner, stage0 },
        );
        session.runtime_build_ownership = Some(ownership);
        Ok(session)
    }

    // Trust: selection through the SAME actual original Full producer. The
    // seed paths continue to describe the private seed, never this driver.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn original_compilation(
        &self,
    ) -> Option<&Arc<crate::engine::OriginalBootstrapCompilation>> {
        self._original_compilation.as_ref()
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn original_control_targo(&self) -> io::Result<PathBuf> {
        let owner = self.original_compilation().ok_or_else(|| {
            io::Error::other("control Cargo driver requires the actual original Full owner")
        })?;
        owner.check_current()?;
        owner.control_targo()
    }

    fn new_with_runtime(
        mut config: Config,
        supplied_shims: Option<PathBuf>,
        initial: InitialRuntime,
    ) -> Session {
        // Trust: reject incompatible selectors before skipping any ordinary
        // prerequisite, including before downloading/preparing the seed.
        crate::core::build_steps::test::compiler_fixture::validate_request(&config).unwrap_or_else(
            |error| {
                eprintln!("Compiler test fixture selection refused: {error}");
                helpers::exit_process(2)
            },
        );
        let compiler_test_fixture = config.compiler_test_fixture.as_ref().map(|source| {
            crate::utils::retained_compiler_fixture::RetainedCompilerTestFixture::capture(
                source,
                &config.out.join("compiler-test-fixtures"),
                &config.host_target.triple,
            )
            .unwrap_or_else(|error| {
                eprintln!("Retained compiler test fixture refused: {error}");
                helpers::exit_process(2)
            })
        });
        if let Some(fixture) = &compiler_test_fixture {
            eprintln!(
                "Retained compiler library-test fixture: {} (product source {}; identity {}; receipt {}; this is a runtime input, not the test build compiler or a current-source SDK)",
                fixture.sysroot().display(),
                fixture.source_commit(),
                fixture.identity(),
                fixture.receipt_path().display()
            );
        }
        // Trust: dependency producers are always frozen; sudo detection no
        // longer selects a different source/lockfile policy.
        let dwn_ctx = DownloadContext::from(&config);

        // Trust: the stage0 driver is the seed's `trustc`, the name bootstrap used before
        // the 1.101 port (`default_stage0_rustc_path` in config.rs, which a direct
        // `cargo test` run also uses). The port's upstream default,
        // `bin/rustc`, is the same binary under its compatibility name, but two decisions
        // read the driver's NAME:
        //  * the stage0 rustdoc (`default_initial_rustdoc_path`): the seed ships `trustdoc`
        //    and the stage0 surface check refuses a `bin/rustdoc` (download.rs
        //    `stage0_forbidden_bins`), so under `bin/rustc` every doctest of a crate
        //    stage0 compiles died in the rustdoc shim;
        //  * the rustc shim's off-switch for HOST units, build scripts and proc macros
        //    (`rustc_driver_supports_trust_no_verify`, a `trustc` stem). Under `bin/rustc`
        //    stage0 compiled them with no off-switch at all. The 1.99.0-trust seed hid it:
        //    its `-Z help` lists only the retired `no-trust-verify`, so x.py exported
        //    `TRUST_NO_VERIFY=1` to the whole run. The 0.11.0-trust seed lists
        //    `trust-verify`, x.py exports nothing, and the seed verified every host unit
        //    under its strict default: `x.py check --stage 1` stopped at 62 crates
        //    (2026-10-20).
        // A configured `build.rustc` is classified by its own name, as before.
        let initial_rustc = match &initial {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            InitialRuntime::Original { stage0, .. } => stage0.compiler.clone(),
            InitialRuntime::Ordinary => config.external_rustc.clone().unwrap_or_else(|| {
                download_beta_toolchain(&dwn_ctx, &config.out);
                // Trust: host units lose target rustflags, so the shim must see the
                // declared Trust driver and apply the existing native seed policy.
                default_initial_rustc_path(&config.out, config.host_target)
            }),
        };

        let initial_rustdoc = match &initial {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            InitialRuntime::Original { stage0, .. } => stage0.rustdoc.clone(),
            InitialRuntime::Ordinary => config.external_rustdoc.clone().unwrap_or_else(|| {
                default_initial_rustdoc_path(
                    &initial_rustc,
                    config.host_target,
                    config.external_rustc.is_none(),
                )
            }),
        };

        // Gather both the sysroot and the target libdir to avoid an unnecessary rustc execution
        // and speed up bootstrap slightly.
        // Remove LD_LIBRARY_PATH/DYLD_LIBRARY_PATH so bootstrap's own libdir doesn't
        // leak into the stage0 compiler and cause ABI mismatches.
        // Trust: preserve captured scheduler custody for compiler metadata.
        let (initial_sysroot, initial_target_libdir) = match &initial {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            InitialRuntime::Original { stage0, .. } => {
                // Native-issued selection DATA stays beside its actual live
                // owner; no output for a different compiler query is invented.
                (stage0.root.clone(), stage0.target_libdir.clone())
            }
            InitialRuntime::Ordinary => {
                let rustc_paths = {
                    let mut query = tool_metadata_command(&initial_rustc);
                    query.metadata_scheduler();
                    query
                        .env_remove(helpers::dylib_path_var())
                        .args(["--print", "sysroot", "--print", "target-libdir"])
                        .run_in_dry_run()
                        .run_capture_stdout(&config)
                        .stdout()
                };
                let mut rustc_paths = rustc_paths.lines();
                let initial_sysroot = rustc_paths
                    .next()
                    .map(PathBuf::from)
                    .expect("Missing sysroot from initial rustc");
                let initial_target_libdir = rustc_paths
                    .next()
                    .map(PathBuf::from)
                    .expect("Missing target libdir from initial rustc");
                assert!(rustc_paths.next().is_none());
                (initial_sysroot, initial_target_libdir)
            }
        };

        let initial_cargo = match &initial {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            InitialRuntime::Original { stage0, .. } => stage0.targo.clone(),
            InitialRuntime::Ordinary => config.external_cargo.clone().unwrap_or_else(|| {
                download_beta_toolchain(&dwn_ctx, &config.out);
                default_initial_cargo_path(&initial_sysroot, config.host_target)
            }),
        };

        // Trust: every location a held capture walks is known now: the checkout,
        // the build directory, the seed sysroot and the Cargo home. Refuse one the
        // held-input rule refuses before any build work, rather than when the
        // final Targo pairing holds the stage-1 sysroot an hour in.
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        crate::utils::trust_held_location::ensure(&config, &initial_sysroot).unwrap_or_else(
            |error| {
                eprintln!("{error}");
                helpers::exit_process(2);
            },
        );

        // Trust: the canonical parsed request decides readiness after the
        // frozen metatool/tool selection, before metadata or stage-1 seeding.
        // Refusal is unconditional, including under --no-fail-fast.
        let readiness = match &initial {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            InitialRuntime::Original { owner, .. } => {
                owner.check_current().map_err(|error| error.to_string())
            }
            InitialRuntime::Ordinary => {
                crate::utils::trust_preparation::ensure(&config, &initial_rustc, &initial_cargo)
            }
        };
        readiness.unwrap_or_else(|error| {
            eprintln!("Trust source readiness refused: {error}");
            helpers::exit_process(2);
        });

        // NOTE: it's important this comes *after* we potentially download the binaries above,
        // in order to not redownload them into a temporary directory.
        if config.exec_ctx.dry_run() {
            config.out = config.out.join("tmp-dry-run");
            fs::create_dir_all(&config.out).expect("Failed to create dry-run directory");
        }

        let initial_target_dir = initial_target_libdir
            .parent()
            .unwrap_or_else(|| panic!("{initial_target_libdir:?} has no parent"));

        let initial_lld = initial_target_dir.join("bin").join("rust-lld");

        let initial_relative_libdir = if cfg!(test) {
            // On tests, bootstrap uses the shim rustc, not the one from the stage0 toolchain.
            PathBuf::default()
        } else {
            let ancestor = initial_target_dir.ancestors().nth(2).unwrap_or_else(|| {
                panic!("Not enough ancestors for {}", initial_target_dir.display())
            });

            ancestor
                .strip_prefix(&initial_sysroot)
                .unwrap_or_else(|_| {
                    panic!(
                        "Couldn’t resolve the initial relative libdir from {}",
                        initial_target_dir.display()
                    )
                })
                .to_path_buf()
        };

        let version = std::fs::read_to_string(config.src.join("src").join("version"))
            .expect("failed to read src/version");
        let version = version.trim();
        // Trust: `src/version` mirrors the ONE version authority (the root
        // Cargo.toml `[workspace.package] version`); refuse to build on drift.
        crate::utils::trust_version_authority::check_version_mirrors(&config.src, version);

        // Trust: the Rust-line alignment of this tree (release/trust-version.toml).
        let rust_compat_version =
            std::fs::read_to_string(config.src.join("src").join("rust-compat-version"))
                .expect("failed to read src/rust-compat-version");
        let rust_compat_version = rust_compat_version.trim().to_string();

        let mut bootstrap_out = supplied_shims.unwrap_or_else(|| {
            std::env::current_exe()
                .expect("could not determine path to running process")
                .parent()
                .unwrap()
                .to_path_buf()
        });
        // Since bootstrap is hardlink to deps/bootstrap-*, Solaris can sometimes give
        // path with deps/ which is bad and needs to be avoided.
        if bootstrap_out.ends_with("deps") {
            bootstrap_out.pop();
        }
        if !bootstrap_out.join(exe("rustc", config.host_target)).exists() && !cfg!(test) {
            // this restriction can be lifted whenever https://github.com/rust-lang/rfcs/pull/3028 is implemented
            panic!(
                "`rustc` not found in {}, run `cargo build --bins` before `cargo run`",
                bootstrap_out.display()
            )
        }

        if config.rust_info.is_from_tarball() && config.description.is_none() {
            config.description = Some("built from a source tarball".to_owned());
        }

        // Trust: consume the actual retained -vV result as version DATA, not
        // as a fabricated answer for the ordinary different-argv query.
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let original_version = match &initial {
            InitialRuntime::Ordinary => None,
            InitialRuntime::Original { stage0, .. } => Some(stage0.compiler_verbose.clone()),
        };
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        let original_version: Option<String> = None;

        let mut sess = Session {
            compiler_test_fixture,
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            runtime_build_ownership: None,
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            _original_compilation: match initial {
                InitialRuntime::Ordinary => None,
                InitialRuntime::Original { owner, .. } => Some(owner),
            },
            completed_runtime: std::cell::RefCell::new(None),
            initial_lld,
            initial_relative_libdir,
            initial_rustc,
            initial_rustdoc,
            initial_cargo,
            initial_sysroot,
            fail_fast: config.cmd.fail_fast(),
            test_target: config.cmd.test_target(),
            verbosity: config.exec_ctx.verbosity as usize,
            config,
            version: version.to_string(),
            rust_compat_version,
            bootstrap_out,

            cc: HashMap::new(),
            cxx: HashMap::new(),
            opaque_cc_operands: HashSet::new(),
            ar: HashMap::new(),
            ranlib: HashMap::new(),
            wasi_sdk_path: env::var_os("WASI_SDK_PATH").map(PathBuf::from),
            crates: HashMap::new(),
            crate_paths: HashMap::new(),
            prerelease_version: Cell::new(None),
            naming: OnceLock::new(),

            #[cfg(feature = "build-metrics")]
            metrics: crate::utils::metrics::BuildMetrics::init(),

            #[cfg(feature = "tracing")]
            step_graph: std::cell::RefCell::new(crate::utils::step_graph::StepGraph::default()),
        };

        // If local-rust is the same major.minor as the current version, then force a
        // local-rebuild
        // Trust: "the current version" is the Rust line, `src/rust-compat-version`; see
        // `helpers::stage0_release_is_local_rebuild`.
        // Trust: preserve captured scheduler custody for compiler metadata.
        let local_version_verbose = original_version.unwrap_or_else(|| {
            let mut query = tool_metadata_command(&sess.initial_rustc);
            query.metadata_scheduler();
            query
                .run_in_dry_run()
                .args(["--version", "--verbose"])
                .run_capture_stdout(&sess)
                .stdout()
        });
        let local_release = local_version_verbose
            .lines()
            .filter_map(|x| x.strip_prefix("release:"))
            .next()
            .unwrap()
            .trim();
        if helpers::stage0_release_is_local_rebuild(local_release, &sess.rust_compat_version) {
            sess.do_if_verbose(|| println!("auto-detected local-rebuild {local_release}"));
            sess.config.local_rebuild = true;
        }

        sess.do_if_verbose(|| println!("finding compilers"));
        crate::utils::cc_detect::fill_compilers(&mut sess);
        // When running `setup`, the profile is about to change, so any requirements we have now may
        // be different on the next invocation. Don't check for them until the next time x.py is
        // run. This is ok because `setup` never runs any build commands, so it won't fail if commands are missing.
        //
        // Similarly, for `setup` we don't actually need submodules or cargo metadata.
        if !matches!(sess.config.cmd, Subcommand::Setup { .. }) {
            sess.do_if_verbose(|| println!("running sanity check"));
            crate::core::sanity::check(&mut sess);

            // Make sure we update these before gathering metadata so we don't get an error about missing
            // Cargo.toml files.
            let rust_submodules = ["library/backtrace"];
            for s in rust_submodules {
                sess.require_submodule(
                    s,
                    Some(
                        "The submodule is required for the standard library \
                         and the main Cargo workspace.",
                    ),
                );
            }
            // Now, update all existing submodules.
            sess.update_existing_submodules();

            sess.do_if_verbose(|| println!("learning about cargo"));
            crate::core::metadata::build(&mut sess);
        }

        // Create symbolic link to use host sysroot from a consistent path (e.g., in the rust-analyzer config file).
        let build_triple = sess.out.join(sess.host_target);
        t!(fs::create_dir_all(&build_triple));
        let host = sess.out.join("host");
        if host.is_symlink() {
            // Left over from a previous build; overwrite it.
            // This matters if `sess.host_target` has changed between invocations.
            #[cfg(windows)]
            t!(fs::remove_dir(&host));
            #[cfg(not(windows))]
            t!(fs::remove_file(&host));
        }
        t!(
            symlink_dir(&sess.config, &build_triple, &host),
            format!("symlink_dir({} => {}) failed", host.display(), build_triple.display())
        );

        sess
    }

    /// Updates a submodule, and exits with a failure if submodule management
    /// is disabled and the submodule does not exist.
    ///
    /// The given submodule name should be its path relative to the root of
    /// the main repository.
    ///
    /// The given `err_hint` will be shown to the user if the submodule is not
    /// checked out and submodule management is disabled.
    #[cfg_attr(
        feature = "tracing",
        instrument(
            level = "trace",
            name = "Session::require_submodule",
            skip_all,
            fields(submodule = submodule),
        )
    )]
    pub(crate) fn require_submodule(&self, submodule: &str, err_hint: Option<&str>) {
        if self.rust_info().is_from_tarball() {
            return;
        }

        if self.config.dry_run() {
            return;
        }

        // When testing bootstrap itself, it is much faster to ignore
        // submodules. Almost all Steps work fine without their submodules.
        if cfg!(test) && !self.config.submodules() {
            return;
        }
        self.config.update_submodule(submodule);
        let absolute_path = self.config.src.join(submodule);
        if !absolute_path.exists() || dir_is_empty(&absolute_path) {
            let maybe_enable = if !self.config.submodules()
                && self.config.rust_info.is_managed_git_subrepository()
            {
                "\nConsider setting `build.submodules = true` or manually initializing the submodules."
            } else {
                ""
            };
            let err_hint = err_hint.map_or_else(String::new, |e| format!("\n{e}"));
            eprintln!(
                "submodule {submodule} does not appear to be checked out, \
                 but it is required for this step{maybe_enable}{err_hint}"
            );
            helpers::exit_process(1);
        }
    }

    /// If any submodule has been initialized already, sync it unconditionally.
    /// This avoids contributors checking in a submodule change by accident.
    pub(crate) fn update_existing_submodules(&self) {
        // Avoid running git when there isn't a git checkout, or the user has
        // explicitly disabled submodules in `bootstrap.toml`.
        if !self.config.submodules() {
            return;
        }
        let output = helpers::git(Some(&self.src))
            .args(["config", "--file"])
            .arg(".gitmodules")
            .args(["--get-regexp", "path"])
            .run_capture(self)
            .stdout();
        // Trust: preserve the actual lexical worker owner in protected mode.
        crate::utils::exec::scoped_threads(|s| {
            // Look for `submodule.$name.path = $path`
            // Sample output: `submodule.src/rust-installer.path src/tools/rust-installer`
            for line in output.lines() {
                let submodule = line.split_once(' ').unwrap().1;
                let config = self.config.clone();
                s.spawn(move || {
                    Self::update_existing_submodule(&config, submodule);
                })
                .expect("native submodule worker dispatch refused");
            }
        })
        .expect("native submodule worker scope did not close");
    }

    /// Updates the given submodule only if it's initialized already; nothing happens otherwise.
    pub(crate) fn update_existing_submodule(config: &Config, submodule: &str) {
        // Avoid running git when there isn't a git checkout.
        if !config.submodules() {
            return;
        }

        if config.git_info(false, Path::new(submodule)).is_managed_git_subrepository() {
            config.update_submodule(submodule);
        }
    }

    /// Executes the entire build, as configured by the flags and configuration.
    #[cfg_attr(feature = "tracing", instrument(level = "debug", name = "Session::build", skip_all))]
    pub(crate) fn build(&mut self) {
        trace!("setting up job management");
        unsafe {
            crate::utils::job::setup(self);
        }

        // Handle hard-coded subcommands.
        {
            #[cfg(feature = "tracing")]
            let _hardcoded_span =
                span!(tracing::Level::DEBUG, "handling hardcoded subcommands (Format, Perf)")
                    .entered();

            match &self.config.cmd {
                Subcommand::Format { check, all } => {
                    let builder = Builder::new(self);
                    let rustfmt_path = builder.ensure(InternalRustfmt).unwrap_or_else(|| {
                        eprintln!("fmt error: `x fmt` is not supported on this channel");
                        helpers::exit_process(1);
                    });
                    return crate::core::build_steps::format::format(
                        &builder,
                        rustfmt_path,
                        *check,
                        *all,
                        &self.config.paths,
                    );
                }
                // Trust: no `x perf` subcommand — Trust does not carry the
                // rustc-perf step/submodule (deleted before 1.99; performance
                // measurement runs through Trust's own benchmark lanes).
                _cmd => {
                    debug!(cmd = ?_cmd, "not a hardcoded subcommand; returning to normal handling");
                }
            }

            debug!("handling subcommand normally");
        }

        if !self.config.dry_run() {
            #[cfg(feature = "tracing")]
            let _real_run_span = span!(tracing::Level::DEBUG, "executing real run").entered();

            // We first do a dry-run. This is a sanity-check to ensure that
            // steps don't do anything expensive in the dry-run.
            {
                #[cfg(feature = "tracing")]
                let _sanity_check_span =
                    span!(tracing::Level::DEBUG, "(1) executing dry-run sanity-check").entered();
                self.config.set_dry_run(DryRun::SelfCheck);
                let builder = Builder::new(self);
                builder.execute_cli();
            }

            // Actual run.
            {
                #[cfg(feature = "tracing")]
                let _actual_run_span =
                    span!(tracing::Level::DEBUG, "(2) executing actual run").entered();
                self.config.set_dry_run(DryRun::Disabled);
                let builder = Builder::new(self);
                builder.execute_cli();
            }
        } else {
            #[cfg(feature = "tracing")]
            let _dry_run_span = span!(tracing::Level::DEBUG, "executing dry run").entered();

            let builder = Builder::new(self);
            builder.execute_cli();
        }

        #[cfg(feature = "tracing")]
        debug!("checking for postponed test failures from `test  --no-fail-fast`");

        // Check for postponed failures from `test --no-fail-fast`.
        self.config.exec_ctx().report_failures_and_exit();

        #[cfg(feature = "build-metrics")]
        self.metrics.persist(self);
    }

    pub(crate) fn rust_info(&self) -> &GitInfo {
        &self.config.rust_info
    }

    /// Gets the space-separated set of activated features for the standard library.
    /// This can be configured with the `std-features` key in bootstrap.toml.
    /// Trust: what this build is named (`utils::trust_source_identity`). A dev stage-1
    /// build names its sources and every other build its commit. It is chosen once per
    /// invocation, so that every compiler, library and tool of one build carry the same
    /// name (a compiler refuses crates built by a differently named one), and so that
    /// bootstrap's dry-run pass and the run after it agree. When git cannot name the
    /// sources of a build that names them, the build is refused: naming HEAD instead
    /// would give an edited tree the name of HEAD's own.
    fn naming(&self) -> &trust_source_identity::Naming {
        self.naming.get_or_init(|| {
            let named =
                trust_source_identity::select_for_build(&self.config, self.rust_info(), |head| {
                    let exec_ctx = self.config.exec_ctx();
                    let config = self.config.config.as_deref();
                    trust_source_identity::of_build(exec_ctx, &self.src, &self.out, config, head)
                });
            named.unwrap_or_else(|reason| {
                eprintln!(
                    "ERROR: bootstrap cannot name the sources of this dev stage-1 build: {reason}"
                );
                eprintln!(
                    "HELP: repair the checkout, or set `rust.trust-source-identity = false` to \
                     name the build by HEAD, as a stage-2 build is named, knowing that an edited \
                     tree then carries HEAD's own name (docs/DECISION_QUEUE.md, \
                     TB1-SOURCE-IDENTITY-1)"
                );
                exit!(1);
            })
        })
    }

    /// Trust: the identity this build's version carries: `CFG_VER_HASH`, `CFG_VER_DATE`,
    /// the hash and date in `CFG_VERSION`, `CFG_TRUST_VERSION`'s build metadata and
    /// the commit tuple of every tool built from the checkout's own sources
    /// (`trust_source_identity::tool_commit`; [`Session::naming`]).
    pub(crate) fn version_info(&self) -> &GitInfo {
        &self.naming().version
    }

    /// Trust: names this build `naming` before anything has asked its name, for a test
    /// that hands tool steps a naming of its own (`utils::trust_source_identity`'s
    /// `every_tool_step_is_handed_the_name_the_compiler_carries`). False when the build
    /// was already named.
    #[cfg(test)]
    pub(crate) fn name_for_test(&self, naming: trust_source_identity::Naming) -> bool {
        self.naming.set(naming).is_ok()
    }

    pub(crate) fn std_features(&self, target: TargetSelection) -> String {
        let mut features: BTreeSet<&str> =
            self.config.rust_std_features.iter().map(|s| s.as_str()).collect();

        match self.config.llvm_libunwind(target) {
            LlvmLibunwind::InTree => features.insert("llvm-libunwind"),
            LlvmLibunwind::System => features.insert("system-llvm-libunwind"),
            LlvmLibunwind::No => false,
        };

        if self.config.backtrace {
            features.insert("backtrace");
        }

        if self.config.profiler_enabled(target) {
            features.insert("profiler");
        }

        // If zkvm target, generate memcpy, etc.
        if target.contains("zkvm") {
            features.insert("compiler-builtins-mem");
        }

        features.into_iter().collect::<Vec<_>>().join(" ")
    }

    /// Gets the space-separated set of activated features for the compiler.
    pub(crate) fn rustc_features(
        &self,
        kind: Kind,
        target: TargetSelection,
        crates: &[String],
    ) -> String {
        let possible_features_by_crates: HashSet<_> = crates
            .iter()
            .flat_map(|krate| &self.crates[krate].features)
            .map(std::ops::Deref::deref)
            .collect();
        let check = |feature: &str| -> bool {
            crates.is_empty() || possible_features_by_crates.contains(feature)
        };
        let mut features = vec![];

        if let Some(allocator_feature_name) = self.config.allocator(target).feature_name()
            && check(allocator_feature_name)
        {
            features.push(allocator_feature_name);
        }
        if self.config.llvm_enabled(target) && check("llvm") {
            features.push("llvm");
        }
        // Trust: Activate trust-cg feature when trust-cg backend is enabled (#956).
        // (Restored in the 1.101 port: upstream moved this fn from `lib.rs` to
        // `core/session.rs`, and the hunk did not follow — stage1 silently built
        // without the builtin backend and every `needs-trust-cg-backend` fixture
        // was ignored.)
        if self.config.enabled_codegen_backends(target).contains(&CodegenBackendKind::TrustCg)
            && check("trust-cg")
        {
            features.push("trust-cg");
        }
        if self.config.llvm_offload {
            features.push("llvm_offload");
        }
        // keep in sync with `bootstrap/compile.rs:rustc_cargo_env`
        if self.config.rust_randomize_layout && check("rustc_randomized_layouts") {
            features.push("rustc_randomized_layouts");
        }
        if self.config.compile_time_deps && kind.is_check_like() {
            features.push("check_only");
        }

        if crates.iter().any(|c| c == "rustc_transmute") {
            // for `x test rustc_transmute`, this feature isn't enabled automatically by a
            // dependent crate.
            features.push("rustc");
        }

        // If debug logging is on, then we want the default for tracing:
        // https://github.com/tokio-rs/tracing/blob/3dd5c03d907afdf2c39444a29931833335171554/tracing/src/level_filters.rs#L26
        // which is everything (including debug/trace/etc.)
        // if its unset, if debug_assertions is on, then debug_logging will also be on
        // as well as tracing *ignoring* this feature when debug_assertions is on
        if !self.config.rust_debug_logging && check("max_level_info") {
            features.push("max_level_info");
        }

        features.join(" ")
    }

    /// Component directory that Cargo will produce output into (e.g.
    /// release/debug)
    pub(crate) fn cargo_dir(&self, mode: Mode) -> &'static str {
        match (mode, self.config.rust_optimize.is_release()) {
            (Mode::Std, _) => "dist",
            (_, true) => "release",
            (_, false) => "debug",
        }
    }

    pub(crate) fn tools_dir(&self, build_compiler: Compiler, target: TargetSelection) -> PathBuf {
        let out = tools_bin_dir(&self.out, build_compiler, target);
        t!(fs::create_dir_all(&out));
        out
    }

    /// Returns the root directory for all output generated in a particular
    /// stage when being built with a particular build compiler.
    ///
    /// The mode indicates what the root directory is for.
    pub(crate) fn stage_out(&self, build_compiler: Compiler, mode: Mode) -> PathBuf {
        use std::fmt::Write;

        fn bootstrap_tool() -> (Option<u32>, &'static str) {
            (None, "bootstrap-tools")
        }
        fn staged_tool(build_compiler: Compiler) -> (Option<u32>, &'static str) {
            (Some(build_compiler.stage + 1), "tools")
        }

        let (stage, suffix) = match mode {
            // Std is special, stage N std is built with stage N rustc
            Mode::Std => (Some(build_compiler.stage), "std"),
            // The rest of things are built with stage N-1 rustc
            Mode::Rustc => (Some(build_compiler.stage + 1), "rustc"),
            Mode::Codegen => (Some(build_compiler.stage + 1), "codegen"),
            // Trust: the immutable seed can predate the current Cargo's
            // fingerprint encoding. Never let current-Cargo tools write records
            // into its prerequisites' domain. This stable generation split keeps
            // warm reuse within each domain without salting by executable hash.
            Mode::ToolBootstrap => (None, "bootstrap-seed-tools"),
            Mode::ToolStd | Mode::ToolRustcPrivate => (Some(build_compiler.stage + 1), "tools"),
            Mode::ToolTarget => {
                // Stage0-compiler consumers of the current Cargo retain their
                // existing cache. Seed-driven ToolTarget recipes project to
                // ToolBootstrap only when selecting their cache paths.
                if build_compiler.stage == 0 {
                    bootstrap_tool()
                } else {
                    staged_tool(build_compiler)
                }
            }
        };
        let path = self.out.join(build_compiler.host);
        let mut dir_name = String::new();
        if let Some(stage) = stage {
            write!(dir_name, "stage{stage}-").unwrap();
        }
        dir_name.push_str(suffix);
        path.join(dir_name)
    }

    /// Returns the root output directory for all Cargo output in a given stage,
    /// running a particular compiler, whether or not we're building the
    /// standard library, and targeting the specified architecture.
    pub(crate) fn cargo_out(
        &self,
        build_compiler: Compiler,
        mode: Mode,
        target: TargetSelection,
    ) -> PathBuf {
        self.stage_out(build_compiler, mode).join(target).join(self.cargo_dir(mode))
    }

    /// Output directory for all documentation for a target
    pub(crate) fn doc_out(&self, target: TargetSelection) -> PathBuf {
        self.out.join(target).join("doc")
    }

    /// Output directory for all JSON-formatted documentation for a target
    pub(crate) fn json_doc_out(&self, target: TargetSelection) -> PathBuf {
        self.out.join(target).join("json-doc")
    }

    /// Output directory for combined compiler + tools docs.
    pub(crate) fn compiler_doc_out(&self, target: TargetSelection) -> PathBuf {
        self.out.join(target).join("compiler-doc")
    }

    /// Path to the vendored Rust crates.
    pub(crate) fn vendored_crates_path(&self) -> Option<PathBuf> {
        if self.config.vendor { Some(self.src.join(VENDOR_DIR)) } else { None }
    }

    /// Directory for libraries built from C/C++ code and shared between stages.
    pub(crate) fn native_dir(&self, target: TargetSelection) -> PathBuf {
        self.out.join(target).join("native")
    }

    /// Adds the `RUST_TEST_THREADS` env var if necessary
    pub(crate) fn add_rust_test_threads(&self, cmd: &mut BootstrapCommand) {
        if env::var_os("RUST_TEST_THREADS").is_none() {
            cmd.env("RUST_TEST_THREADS", self.jobs().to_string());
        }
    }

    /// Returns the libdir of the snapshot compiler.
    pub(crate) fn rustc_snapshot_libdir(&self) -> PathBuf {
        self.rustc_snapshot_sysroot().join(libdir(self.config.host_target))
    }

    /// Returns the sysroot of the snapshot compiler.
    pub(crate) fn rustc_snapshot_sysroot(&self) -> &Path {
        &self.initial_sysroot
    }

    pub(crate) fn info(&self, msg: &str) {
        match self.config.get_dry_run() {
            DryRun::SelfCheck => (),
            DryRun::Disabled | DryRun::UserSelected => {
                println!("{msg}");
            }
        }
    }

    /// Return a `Group` guard for a [`Step`] that:
    /// - Performs `action`
    ///   - If the action is `Kind::Test`, use [`Session::msg_test`] instead.
    /// - On `what`
    ///   - Where `what` possibly corresponds to a `mode`
    /// - `action` is performed with/on the given compiler (`target_and_stage`).
    ///   - Since for some steps it is not possible to pass a single compiler here, it is also
    ///     possible to pass the host and stage explicitly.
    /// - With a given `target`.
    ///
    /// [`Step`]: crate::core::builder::Step
    #[must_use = "Groups should not be dropped until the Step finishes running"]
    #[track_caller]
    pub(crate) fn msg(
        &self,
        action: impl Into<Kind>,
        what: impl Display,
        mode: impl Into<Option<Mode>>,
        target_and_stage: impl Into<TargetAndStage>,
        target: impl Into<Option<TargetSelection>>,
    ) -> Option<gha::Group> {
        let target_and_stage = target_and_stage.into();
        let action = action.into();
        assert!(
            action != Kind::Test,
            "Please use `Session::msg_test` instead of `Session::msg(Kind::Test)`"
        );

        let actual_stage = match mode.into() {
            // Std has the same stage as the compiler that builds it
            Some(Mode::Std) => target_and_stage.stage,
            // Other things have stage corresponding to their build compiler + 1
            Some(
                Mode::Rustc
                | Mode::Codegen
                | Mode::ToolBootstrap
                | Mode::ToolTarget
                | Mode::ToolStd
                | Mode::ToolRustcPrivate,
            )
            | None => target_and_stage.stage + 1,
        };

        let action = action.description();
        let what = what.to_string();
        let msg = |fmt| {
            let space = if !what.is_empty() { " " } else { "" };
            format!("{action} stage{actual_stage} {what}{space}{fmt}")
        };
        let msg = if let Some(target) = target.into() {
            let build_stage = target_and_stage.stage;
            let host = target_and_stage.target;
            if host == target {
                msg(format_args!("(stage{build_stage} -> stage{actual_stage}, {target})"))
            } else {
                msg(format_args!("(stage{build_stage}:{host} -> stage{actual_stage}:{target})"))
            }
        } else {
            msg(format_args!(""))
        };
        self.group(&msg)
    }

    /// Return a `Group` guard for a [`Step`] that tests `what` with the given `stage` and `target`.
    /// Use this instead of [`Session::msg`] for test steps, because for them it is not always clear
    /// what exactly is a build compiler.
    ///
    /// [`Step`]: crate::core::builder::Step
    #[must_use = "Groups should not be dropped until the Step finishes running"]
    #[track_caller]
    pub(crate) fn msg_test(
        &self,
        what: impl Display,
        target: TargetSelection,
        stage: u32,
    ) -> Option<gha::Group> {
        let action = Kind::Test.description();
        let msg = format!("{action} stage{stage} {what} ({target})");
        self.group(&msg)
    }

    /// Return a `Group` guard for a [`Step`] that is only built once and isn't affected by `--stage`.
    ///
    /// [`Step`]: crate::core::builder::Step
    #[must_use = "Groups should not be dropped until the Step finishes running"]
    #[track_caller]
    pub(crate) fn msg_unstaged(
        &self,
        action: impl Into<Kind>,
        what: impl Display,
        target: TargetSelection,
    ) -> Option<gha::Group> {
        let action = action.into().description();
        let msg = format!("{action} {what} for {target}");
        self.group(&msg)
    }

    #[track_caller]
    pub(crate) fn group(&self, msg: &str) -> Option<gha::Group> {
        match self.config.get_dry_run() {
            DryRun::SelfCheck => None,
            DryRun::Disabled | DryRun::UserSelected => Some(gha::group(msg)),
        }
    }

    /// Returns the number of parallel jobs that have been configured for this
    /// build.
    pub(crate) fn jobs(&self) -> u32 {
        self.config.jobs.unwrap_or_else(|| {
            std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get) as u32
        })
    }

    pub(crate) fn debuginfo_map_to(&self, remap_scheme: RemapScheme) -> Option<String> {
        if !self.config.rust_remap_debuginfo {
            return None;
        }

        // Trust: development paths use a stable namespace, while version_info
        // still names the selected source identity or HEAD. Changing the version
        // must not change every otherwise unchanged crate's path flags.
        // Sealed/stage2/install builds have no separate remap label.
        let sha =
            self.naming().remap.as_deref().or_else(|| self.rust_sha()).unwrap_or(&self.version);

        match remap_scheme {
            RemapScheme::Compiler => {
                // For compiler sources, remap via `/rustc-dev/{sha}` to allow
                // distinguishing between compiler sources vs library sources, since
                // `rustc-dev` dist component places them under
                // `$sysroot/lib/rustlib/rustc-src/rust` as opposed to `rust-src`'s
                // `$sysroot/lib/rustlib/src/rust`.
                //
                // Keep this scheme in sync with `rustc_metadata::rmeta::decoder`'s
                // `try_to_translate_virtual_to_real`.
                Some(format!("/rustc-dev/{sha}"))
            }
            RemapScheme::NonCompiler => {
                // For non-compiler sources, use `/rustc/{sha}` remapping scheme.
                Some(format!("/rustc/{sha}"))
            }
        }
    }

    /// Returns the path to the C compiler for the target specified.
    pub(crate) fn cc(&self, target: TargetSelection) -> PathBuf {
        if self.config.dry_run() {
            return PathBuf::new();
        }
        self.cc[&target].path().into()
    }

    /// Returns the internal `cc::Tool` for the C compiler.
    pub(crate) fn cc_tool(&self, target: TargetSelection) -> cc::Tool {
        self.cc[&target].clone()
    }

    /// Returns the internal `cc::Tool` for the C++ compiler.
    pub(crate) fn cxx_tool(&self, target: TargetSelection) -> cc::Tool {
        self.cxx[&target].clone()
    }

    /// Returns C flags that `cc-rs` thinks should be enabled for the
    /// specified target by default.
    pub(crate) fn cc_handled_cflags(&self, target: TargetSelection, c: CLang) -> Vec<String> {
        if self.config.dry_run() {
            return Vec::new();
        }
        let base = match c {
            CLang::C => self.cc[&target].clone(),
            CLang::Cxx => self.cxx[&target].clone(),
        };

        // Filter out -O and /O (the optimization flags) that we picked up
        // from cc-rs, that's up to the caller to figure out.
        base.args()
            .iter()
            .map(|s| s.to_string_lossy().into_owned())
            .filter(|s| !s.starts_with("-O") && !s.starts_with("/O"))
            .collect::<Vec<String>>()
    }

    /// Returns extra C flags that `cc-rs` doesn't handle.
    pub(crate) fn cc_unhandled_cflags(&self, target: TargetSelection, c: CLang) -> Vec<String> {
        let mut base = Vec::new();

        // If we're compiling C++ on macOS then we add a flag indicating that
        // we want libc++ (more filled out than libstdc++), ensuring that
        // LLVM/etc are all properly compiled.
        if matches!(c, CLang::Cxx) && target.contains("apple-darwin") {
            base.push("-stdlib=libc++".into());
        }

        // Work around an apparently bad MinGW / GCC optimization,
        // See: https://lists.llvm.org/pipermail/cfe-dev/2016-December/051980.html
        // See: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=78936
        if &*target.triple == "i686-pc-windows-gnu" {
            base.push("-fno-omit-frame-pointer".into());
        }

        base
    }

    /// Returns the path to the `ar` archive utility for the target specified.
    pub(crate) fn ar(&self, target: TargetSelection) -> Option<PathBuf> {
        if self.config.dry_run() {
            return None;
        }
        self.ar.get(&target).cloned()
    }

    /// Returns the path to the `ranlib` utility for the target specified.
    pub(crate) fn ranlib(&self, target: TargetSelection) -> Option<PathBuf> {
        if self.config.dry_run() {
            return None;
        }
        self.ranlib.get(&target).cloned()
    }

    /// Returns the path to the C++ compiler for the target specified.
    pub(crate) fn cxx(&self, target: TargetSelection) -> Result<PathBuf, String> {
        if self.config.dry_run() {
            return Ok(PathBuf::new());
        }
        match self.cxx.get(&target) {
            Some(p) => Ok(p.path().into()),
            None => Err(format!("target `{target}` is not configured as a host, only as a target")),
        }
    }

    /// Returns the path to the linker for the given target if it needs to be overridden.
    pub(crate) fn linker(&self, target: TargetSelection) -> Option<PathBuf> {
        if self.config.dry_run() {
            return Some(PathBuf::new());
        }
        if let Some(linker) = self.config.target_config.get(&target).and_then(|c| c.linker.clone())
        {
            Some(linker)
        } else if target.contains("vxworks") {
            // need to use CXX compiler as linker to resolve the exception functions
            // that are only existed in CXX libraries
            Some(self.cxx[&target].path().into())
        } else if !self.config.is_host_target(target)
            && helpers::use_host_linker(target)
            && !target.is_msvc()
        {
            Some(self.cc(target))
        } else if self.config.bootstrap_override_lld.is_used()
            && self.is_lld_direct_linker(target)
            && self.host_target == target
        {
            match self.config.bootstrap_override_lld {
                BootstrapOverrideLld::SelfContained => Some(self.initial_lld.clone()),
                BootstrapOverrideLld::External => Some("lld".into()),
                BootstrapOverrideLld::None => None,
            }
        } else {
            None
        }
    }

    // Is LLD configured directly through `-Clinker`?
    // Only MSVC targets use LLD directly at the moment.
    pub(crate) fn is_lld_direct_linker(&self, target: TargetSelection) -> bool {
        target.is_msvc()
    }

    /// Returns if this target should statically link the C runtime, if specified
    pub(crate) fn crt_static(&self, target: TargetSelection) -> Option<bool> {
        if target.contains("pc-windows-msvc") {
            Some(true)
        } else {
            self.config.target_config.get(&target).and_then(|t| t.crt_static)
        }
    }

    /// Returns the "musl root" for this `target`, if defined.
    ///
    /// If this is a native target (host is also musl) and no musl-root is given,
    /// it falls back to the system toolchain in /usr.
    pub(crate) fn musl_root(&self, target: TargetSelection) -> Option<&Path> {
        let configured_root = self
            .config
            .target_config
            .get(&target)
            .and_then(|t| t.musl_root.as_ref())
            .or(self.config.musl_root.as_ref())
            .map(|p| &**p);

        if self.config.is_host_target(target) && configured_root.is_none() {
            Some(Path::new("/usr"))
        } else {
            configured_root
        }
    }

    /// Returns the "musl libdir" for this `target`.
    pub(crate) fn musl_libdir(&self, target: TargetSelection) -> Option<PathBuf> {
        self.config
            .target_config
            .get(&target)
            .and_then(|t| t.musl_libdir.clone())
            .or_else(|| self.musl_root(target).map(|root| root.join("lib")))
    }

    /// Returns the `lib` directory for the WASI target specified, if
    /// configured.
    ///
    /// This first consults `wasi-root` as configured in per-target
    /// configuration, and failing that it assumes that `$WASI_SDK_PATH` is
    /// set in the environment, and failing that `None` is returned.
    pub(crate) fn wasi_libdir(&self, target: TargetSelection) -> Option<PathBuf> {
        let configured =
            self.config.target_config.get(&target).and_then(|t| t.wasi_root.as_ref()).map(|p| &**p);
        if let Some(path) = configured {
            return Some(path.join("lib").join(target.to_string()));
        }
        let mut env_root = self.wasi_sdk_path.clone()?;
        env_root.push("share");
        env_root.push("wasi-sysroot");
        env_root.push("lib");
        env_root.push(target.to_string());
        Some(env_root)
    }

    /// Returns `true` if this is a no-std `target`, if defined
    pub(crate) fn no_std(&self, target: TargetSelection) -> Option<bool> {
        self.config.target_config.get(&target).map(|t| t.no_std)
    }

    /// Returns `true` if the target will be tested using the `remote-test-client`
    /// and `remote-test-server` binaries.
    pub(crate) fn remote_tested(&self, target: TargetSelection) -> bool {
        self.qemu_rootfs(target).is_some()
            || target.contains("android")
            || env::var_os("TEST_DEVICE_ADDR").is_some()
    }

    /// Returns an optional "runner" to pass to `compiletest` when executing
    /// test binaries.
    ///
    /// An example of this would be a WebAssembly runtime when testing the wasm
    /// targets.
    pub(crate) fn runner(&self, target: TargetSelection) -> Option<String> {
        let configured_runner =
            self.config.target_config.get(&target).and_then(|t| t.runner.as_ref()).map(|p| &**p);
        if let Some(runner) = configured_runner {
            return Some(runner.to_owned());
        }

        if target.starts_with("wasm") && target.contains("wasi") {
            self.default_wasi_runner()
        } else {
            None
        }
    }

    /// When a `runner` configuration is not provided and a WASI-looking target
    /// is being tested this is consulted to prove the environment to see if
    /// there's a runtime already lying around that seems reasonable to use.
    fn default_wasi_runner(&self) -> Option<String> {
        let mut finder = crate::core::sanity::Finder::new();

        // Look for Wasmtime, and for its default options be sure to disable
        // its caching system since we're executing quite a lot of tests and
        // ideally shouldn't pollute the cache too much.
        if let Some(path) = finder.maybe_have("wasmtime")
            && let Ok(mut path) = path.into_os_string().into_string()
        {
            path.push_str(
                " run -C cache=n --dir . \
                 --wasi inherit-env,inherit-network,allow-ip-name-lookup",
            );
            return Some(path);
        }

        None
    }

    /// Returns whether the specified tool is configured as part of this build.
    ///
    /// This requires that both the `extended` key is set and the `tools` key is
    /// either unset or specifically contains the specified tool.
    pub(crate) fn tool_enabled(&self, tool: &str) -> bool {
        if !self.config.extended {
            return false;
        }
        match &self.config.tools {
            Some(set) => set.contains(tool),
            None => true,
        }
    }

    /// Returns the root of the "rootfs" image that this target will be using,
    /// if one was configured.
    ///
    /// If `Some` is returned then that means that tests for this target are
    /// emulated with QEMU and binaries will need to be shipped to the emulator.
    pub(crate) fn qemu_rootfs(&self, target: TargetSelection) -> Option<&Path> {
        self.config.target_config.get(&target).and_then(|t| t.qemu_rootfs.as_ref()).map(|p| &**p)
    }

    /// Tests whether the `compiler` compiling for `target` should be forced to
    /// use a stage1 compiler instead.
    ///
    /// Currently, by default, the build system does not perform a "full
    /// bootstrap" by default where we compile the compiler three times.
    /// Instead, we compile the compiler two times. The final stage (stage2)
    /// just copies the libraries from the previous stage, which is what this
    /// method detects.
    ///
    /// Here we return `true` if:
    ///
    /// * The build isn't performing a full bootstrap
    /// * The `compiler` is in the final stage, 2
    /// * We're not cross-compiling, so the artifacts are already available in
    ///   stage1
    ///
    /// When all of these conditions are met the build will lift artifacts from
    /// the previous stage forward.
    pub(crate) fn force_use_stage1(&self, stage: u32, target: TargetSelection) -> bool {
        !self.config.full_bootstrap
            && !self.config.download_rustc()
            && stage >= 2
            && (self.hosts.contains(&target) || target == self.host_target)
    }

    /// Checks whether the `compiler` compiling for `target` should be forced to
    /// use a stage2 compiler instead.
    ///
    /// When we download the pre-compiled version of rustc and compiler stage is >= 2,
    /// it should be forced to use a stage2 compiler.
    pub(crate) fn force_use_stage2(&self, stage: u32) -> bool {
        self.config.download_rustc() && stage >= 2
    }

    /// Given `num` in the form "a.b.c" return a "release string" which
    /// describes the release version number.
    ///
    /// For example on nightly this returns "a.b.c-nightly", on beta it returns
    /// "a.b.c-beta.1" and on stable it just returns "a.b.c".
    pub(crate) fn release(&self, num: &str) -> String {
        match &self.config.channel[..] {
            "stable" => num.to_string(),
            "beta" => {
                if !self.config.omit_git_hash {
                    format!("{}-beta.{}", num, self.beta_prerelease_version())
                } else {
                    format!("{num}-beta")
                }
            }
            "nightly" => format!("{num}-nightly"),
            _ => format!("{num}-dev"),
        }
    }

    fn beta_prerelease_version(&self) -> u32 {
        fn extract_beta_rev_from_file<P: AsRef<Path>>(version_file: P) -> Option<String> {
            let version = fs::read_to_string(version_file).ok()?;

            helpers::extract_beta_rev(&version)
        }

        if let Some(s) = self.prerelease_version.get() {
            return s;
        }

        // First check if there is a version file available.
        // If available, we read the beta revision from that file.
        // This only happens when building from a source tarball when Git should not be used.
        let count = extract_beta_rev_from_file(self.src.join("version")).unwrap_or_else(|| {
            // Figure out how many merge commits happened since we branched off main.
            // That's our beta number!
            // (Note that we use a `..` range, not the `...` symmetric difference.)
            helpers::git(Some(&self.src))
                .arg("rev-list")
                .arg("--count")
                .arg("--merges")
                .arg(format!(
                    "refs/remotes/origin/{}..HEAD",
                    self.config.stage0_metadata.config.nightly_branch
                ))
                .run_in_dry_run()
                .run_capture(self)
                .stdout()
        });
        let n = count.trim().parse().unwrap();
        self.prerelease_version.set(Some(n));
        n
    }

    /// Returns the value of `release` above for Rust itself.
    pub(crate) fn rust_release(&self) -> String {
        // Trust: the compiler's release string is the Rust-line alignment,
        // not Trust's own product version (docs/VERSIONING.md).
        self.release(&self.rust_compat_version)
    }

    /// Trust's own product version (`CFG_TRUST_VERSION`): the checked-in
    /// `MAJOR.MINOR.0` on a `stable` build, and `MAJOR.MINOR.0+g<sha>` on every
    /// other channel.
    ///
    /// Trust: docs/VERSIONING.md (the owner's publication policy) reserves a bare
    /// `X.Y.0` for the release itself; a dev build carries its commit in SemVer
    /// BUILD METADATA, which identifies the artifact and is ignored when versions
    /// are compared. A checkout without git information has no identity to add and
    /// reports the bare line.
    pub(crate) fn trust_version(&self) -> String {
        // Trust: a dev stage-1 build's identity names its sources (`version_info`).
        match (&self.config.channel[..], self.version_info().sha_short()) {
            ("stable", _) | (_, None) => self.version.clone(),
            (_, Some(sha)) => format!("{}+g{sha}", self.version),
        }
    }

    /// Returns the "package version" for a component.
    ///
    /// The package version is typically what shows up in the names of tarballs.
    /// For channels like beta/nightly it's just the channel name, otherwise it's the release
    /// version.
    pub(crate) fn rust_package_vers(&self) -> String {
        package_vers(&self.config.channel, &self.version)
    }

    /// Returns the `version` string associated with this compiler for Rust
    /// itself.
    ///
    /// Note that this is a descriptive string which includes the commit date,
    /// sha, version, etc.
    pub(crate) fn rust_version(&self) -> String {
        let mut version = self.version_info().version(self, &self.rust_compat_version);
        if let Some(ref s) = self.config.description
            && !s.is_empty()
        {
            version.push_str(" (");
            version.push_str(s);
            version.push(')');
        }
        version
    }

    /// Returns the full commit hash.
    pub(crate) fn rust_sha(&self) -> Option<&str> {
        self.version_info().sha()
    }

    /// Returns the `a.b.c` version that the given package is at.
    pub(crate) fn release_num(&self, package: &str) -> String {
        if self.config.dry_run() {
            return "0.0.0 (dry-run)".into();
        }
        let toml_file_name = self.src.join(format!("src/tools/{package}/Cargo.toml"));
        let toml = t!(fs::read_to_string(toml_file_name));
        for line in toml.lines() {
            if let Some(stripped) =
                line.strip_prefix("version = \"").and_then(|s| s.strip_suffix('"'))
            {
                return stripped.to_owned();
            }
        }

        panic!("failed to find version in {package}'s Cargo.toml")
    }

    /// Returns `true` if unstable features should be enabled for the compiler
    /// we're building.
    pub(crate) fn unstable_features(&self) -> bool {
        !matches!(&self.config.channel[..], "stable" | "beta")
    }

    /// Returns a Vec of all the dependencies of the given root crate,
    /// including transitive dependencies and the root itself. Only includes
    /// "local" crates (those in the local source tree, not from a registry).
    pub(crate) fn in_tree_crates(
        &self,
        root: &str,
        target: Option<TargetSelection>,
    ) -> Vec<&Crate> {
        let mut ret = Vec::new();
        let mut list = vec![root.to_owned()];
        let mut visited = HashSet::new();
        while let Some(krate) = list.pop() {
            let krate = self
                .crates
                .get(&krate)
                .unwrap_or_else(|| panic!("metadata missing for {krate}: {:?}", self.crates));
            ret.push(krate);
            for dep in &krate.deps {
                if !self.crates.contains_key(dep) {
                    // Ignore non-workspace members.
                    continue;
                }
                // Don't include optional deps if their features are not
                // enabled. Ideally this would be computed from `cargo
                // metadata --features …`, but that is somewhat slow. In
                // the future, we may want to consider just filtering all
                // build and dev dependencies in metadata::build.
                if visited.insert(dep)
                    && (dep != "profiler_builtins"
                        || target
                            .map(|t| self.config.profiler_enabled(t))
                            .unwrap_or_else(|| self.config.any_profiler_enabled()))
                    && (dep != "rustc_codegen_llvm"
                        || self.config.hosts.iter().any(|host| self.config.llvm_enabled(*host)))
                {
                    list.push(dep.clone());
                }
            }
        }

        // Sort the crates so that bootstrap unit tests can assume a deterministic order.
        ret.sort_unstable_by(|a, b| Ord::cmp(&a.name, &b.name));
        ret
    }

    pub(crate) fn read_stamp_file(&self, stamp: &BuildStamp) -> Vec<(PathBuf, DependencyType)> {
        if self.config.dry_run() {
            return Vec::new();
        }

        if !stamp.path().exists() {
            eprintln!(
                "ERROR: Unable to find the stamp file {}, did you try to keep a nonexistent build stage?",
                stamp.path().display()
            );
            helpers::exit_process(1);
        }

        let mut paths = Vec::new();
        let contents = t!(fs::read(stamp.path()), stamp.path());
        // This is the method we use for extracting paths from the stamp file passed to us. See
        // run_cargo for more information (in compile.rs).
        for part in contents.split(|b| *b == 0) {
            if part.is_empty() {
                continue;
            }
            let dependency_type = match part[0] as char {
                'h' => DependencyType::Host,
                's' => DependencyType::TargetSelfContained,
                't' => DependencyType::Target,
                _ => unreachable!(),
            };
            let path = PathBuf::from(t!(str::from_utf8(&part[1..])));
            paths.push((path, dependency_type));
        }
        paths
    }

    /// Copies a file from `src` to `dst`.
    ///
    /// If `src` is a symlink, `src` will be resolved to the actual path
    /// and copied to `dst` instead of the symlink itself.
    #[track_caller]
    pub(crate) fn resolve_symlink_and_copy(&self, src: &Path, dst: &Path) {
        // Trust: LLVM providers can be shared inputs. Dereference aliases, but copy their
        // bytes so sysroot installation never adds a hard link to a provider inode.
        self.copy_link_internal(src, dst, true, false);
    }

    /// Links a file from `src` to `dst`.
    /// Attempts to use hard links if possible, falling back to copying.
    /// You can neither rely on this being a copy nor it being a link,
    /// so do not write to dst.
    #[track_caller]
    pub(crate) fn copy_link(&self, src: &Path, dst: &Path, file_type: FileType) {
        // Trust: an executable is always copied on macOS; see `FileType::may_hard_link`.
        self.copy_link_internal(src, dst, false, file_type.may_hard_link());

        if file_type.could_have_split_debuginfo()
            && let Some(dbg_file) = split_debuginfo(src)
        {
            self.copy_link_internal(
                &dbg_file,
                &dst.with_extension(dbg_file.extension().unwrap()),
                false,
                true,
            );
        }
    }

    #[track_caller]
    fn copy_link_internal(
        &self,
        src: &Path,
        dst: &Path,
        dereference_symlinks: bool,
        allow_hard_link: bool,
    ) {
        if self.config.dry_run() {
            return;
        }
        if src == dst {
            return;
        }

        #[cfg(feature = "tracing")]
        let _span = trace_io!("file-copy-link", ?src, ?dst);

        if let Err(e) = fs::remove_file(dst)
            && cfg!(windows)
            && e.kind() != io::ErrorKind::NotFound
        {
            // workaround for https://github.com/rust-lang/rust/issues/127126
            // if removing the file fails, attempt to rename it instead.
            let now = t!(SystemTime::now().duration_since(SystemTime::UNIX_EPOCH));
            let _ = fs::rename(dst, format!("{}-{}", dst.display(), now.as_nanos()));
        }
        let mut metadata = t!(src.symlink_metadata(), format!("src = {}", src.display()));
        let mut src = src.to_path_buf();
        if metadata.file_type().is_symlink() {
            if dereference_symlinks {
                src = t!(fs::canonicalize(src));
                metadata = t!(fs::metadata(&src), format!("target = {}", src.display()));
            } else {
                let link = t!(fs::read_link(src));
                if is_symlink_dir(&metadata) {
                    t!(symlink_dir(&self.config, &link, dst));
                } else {
                    t!(self.symlink_file(link, dst));
                }
                return;
            }
        }
        if allow_hard_link && let Ok(()) = fs::hard_link(&src, dst) {
            // Attempt to "easy copy" by creating a hard link (symlinks are privileged on windows),
            // but if that fails just fall back to a slow `copy` operation.
        } else {
            if let Err(e) = fs::copy(&src, dst) {
                panic!("failed to copy `{}` to `{}`: {}", src.display(), dst.display(), e)
            }
            t!(fs::set_permissions(dst, metadata.permissions()));

            // Restore file times because changing permissions on e.g. Linux using `chmod` can cause
            // file access time to change.
            let file_times = fs::FileTimes::new()
                .set_accessed(t!(metadata.accessed()))
                .set_modified(t!(metadata.modified()));
            t!(set_file_times(dst, file_times));
        }
    }

    /// Links the `src` directory recursively to `dst`. Both are assumed to exist
    /// when this function is called.
    /// Will attempt to use hard links if possible and fall back to copying.
    #[track_caller]
    pub(crate) fn cp_link_r(&self, src: &Path, dst: &Path) {
        if self.config.dry_run() {
            return;
        }
        for f in self.read_dir(src) {
            let path = f.path();
            let name = path.file_name().unwrap();
            let dst = dst.join(name);
            if t!(f.file_type()).is_dir() {
                t!(fs::create_dir_all(&dst));
                self.cp_link_r(&path, &dst);
            } else {
                self.copy_link(&path, &dst, FileType::Regular);
            }
        }
    }

    /// Copies the `src` directory recursively to `dst`. Both are assumed to exist
    /// when this function is called.
    /// Will attempt to use hard links if possible and fall back to copying.
    /// Unwanted files or directories can be skipped
    /// by returning `false` from the filter function.
    #[track_caller]
    pub(crate) fn cp_link_filtered(&self, src: &Path, dst: &Path, filter: &dyn Fn(&Path) -> bool) {
        // Immediately recurse with an empty relative path
        self.cp_link_filtered_recurse(src, dst, Path::new(""), filter, true)
    }

    /// Trust: import an input tree without hard-linking its regular files.
    /// Uses the same filtering, alias and destination-replacement semantics as
    /// `cp_link_filtered`; only build-owned artifacts may use its hard-link fast path.
    #[track_caller]
    pub(crate) fn cp_filtered(&self, src: &Path, dst: &Path, filter: &dyn Fn(&Path) -> bool) {
        self.cp_link_filtered_recurse(src, dst, Path::new(""), filter, false)
    }

    // Inner function does the actual work
    #[track_caller]
    fn cp_link_filtered_recurse(
        &self,
        src: &Path,
        dst: &Path,
        relative: &Path,
        filter: &dyn Fn(&Path) -> bool,
        allow_hard_link: bool,
    ) {
        for f in self.read_dir(src) {
            let path = f.path();
            let name = path.file_name().unwrap();
            let dst = dst.join(name);
            let relative = relative.join(name);
            // Only copy file or directory if the filter function returns true
            if filter(&relative) {
                if t!(f.file_type()).is_dir() {
                    let _ = fs::remove_dir_all(&dst);
                    self.create_dir(&dst);
                    self.cp_link_filtered_recurse(&path, &dst, &relative, filter, allow_hard_link);
                } else if allow_hard_link {
                    self.copy_link(&path, &dst, FileType::Regular);
                } else {
                    self.copy_link_internal(&path, &dst, false, false);
                }
            }
        }
    }

    pub(crate) fn copy_link_to_folder(&self, src: &Path, dest_folder: &Path) {
        let file_name = src.file_name().unwrap();
        let dest = dest_folder.join(file_name);
        self.copy_link(src, &dest, FileType::Regular);
    }

    pub(crate) fn install(&self, src: &Path, dstdir: &Path, file_type: FileType) {
        if self.config.dry_run() {
            return;
        }
        let dst = dstdir.join(src.file_name().unwrap());

        #[cfg(feature = "tracing")]
        let _span = trace_io!("install", ?src, ?dst);

        t!(fs::create_dir_all(dstdir));
        if !src.exists() {
            panic!("ERROR: File \"{}\" not found!", src.display());
        }

        self.copy_link_internal(src, &dst, true, file_type.may_hard_link());
        chmod(&dst, file_type.perms());

        // If this file can have debuginfo, look for split debuginfo and install it too.
        if file_type.could_have_split_debuginfo()
            && let Some(dbg_file) = split_debuginfo(src)
        {
            self.install(&dbg_file, dstdir, FileType::Regular);
        }
    }

    pub(crate) fn read(&self, path: &Path) -> String {
        if self.config.dry_run() {
            return String::new();
        }
        t!(fs::read_to_string(path))
    }

    #[track_caller]
    pub(crate) fn create_dir(&self, dir: &Path) {
        if self.config.dry_run() {
            return;
        }

        #[cfg(feature = "tracing")]
        let _span = trace_io!("dir-create", ?dir);

        t!(fs::create_dir_all(dir))
    }

    pub(crate) fn remove_dir(&self, dir: &Path) {
        if self.config.dry_run() {
            return;
        }

        #[cfg(feature = "tracing")]
        let _span = trace_io!("dir-remove", ?dir);

        t!(fs::remove_dir_all(dir))
    }

    /// Make sure that `dir` will be an empty existing directory after this function ends.
    /// If it existed before, it will be first deleted.
    pub(crate) fn clear_dir(&self, dir: &Path) {
        if self.config.dry_run() {
            return;
        }

        #[cfg(feature = "tracing")]
        let _span = trace_io!("dir-clear", ?dir);

        let _ = std::fs::remove_dir_all(dir);
        self.create_dir(dir);
    }

    pub(crate) fn read_dir(&self, dir: &Path) -> impl Iterator<Item = fs::DirEntry> {
        let iter = match fs::read_dir(dir) {
            Ok(v) => v,
            Err(_) if self.config.dry_run() => return vec![].into_iter(),
            Err(err) => panic!("could not read dir {dir:?}: {err:?}"),
        };
        iter.map(|e| t!(e)).collect::<Vec<_>>().into_iter()
    }

    pub(crate) fn symlink_file<P: AsRef<Path>, Q: AsRef<Path>>(
        &self,
        src: P,
        link: Q,
    ) -> io::Result<()> {
        #[cfg(unix)]
        use std::os::unix::fs::symlink as symlink_file;
        #[cfg(windows)]
        use std::os::windows::fs::symlink_file;
        if !self.config.dry_run() { symlink_file(src.as_ref(), link.as_ref()) } else { Ok(()) }
    }

    /// Returns if config.ninja is enabled, and checks for ninja existence,
    /// exiting with a nicer error message if not.
    pub(crate) fn ninja(&self) -> bool {
        self.validate_ninja();
        self.selected_ninja()
    }

    pub(crate) fn validate_ninja(&self) {
        let mut cmd_finder = crate::core::sanity::Finder::new();

        // Trust: a dry run plans the configured generator without executing
        // it. Missing build tools remain a refusal before any real build.
        if self.config.ninja_in_file && !self.config.dry_run() {
            // Some Linux distros rename `ninja` to `ninja-build`.
            // CMake can work with either binary name.
            if cmd_finder.maybe_have("ninja-build").is_none()
                && cmd_finder.maybe_have("ninja").is_none()
            {
                eprintln!(
                    "
Couldn't find required command: ninja (or ninja-build)

You should install ninja as described at
<https://github.com/ninja-build/ninja/wiki/Pre-built-Ninja-packages>,
or set `ninja = false` in the `[llvm]` section of `bootstrap.toml`.
Alternatively, set `download-ci-llvm = true` in that `[llvm]` section
to download LLVM rather than building it.
"
                );
                helpers::exit_process(1);
            }
        }
    }

    /// Resolve the configured generator choice without requiring a build tool.
    /// MSVC keeps its existing availability-based auto-selection.
    pub(crate) fn selected_ninja(&self) -> bool {
        self.selected_ninja_with(|| {
            crate::core::sanity::Finder::new().maybe_have("ninja").is_some()
        })
    }

    pub(crate) fn selected_ninja_with(&self, available: impl FnOnce() -> bool) -> bool {
        // If ninja isn't enabled but we're building for MSVC then we try
        // doubly hard to enable it. It was realized in #43767 that the msbuild
        // CMake generator for MSVC doesn't respect configuration options like
        // disabling LLVM assertions, which can often be quite important!
        //
        // In these cases we automatically enable Ninja if we find it in the
        // environment.
        if !self.config.ninja_in_file && self.config.host_target.is_msvc() && available() {
            return true;
        }

        self.config.ninja_in_file
    }

    pub(crate) fn colored_stdout<R, F: FnOnce(&mut dyn WriteColor) -> R>(&self, f: F) -> R {
        self.colored_stream_inner(StandardStream::stdout, self.config.stdout_is_tty, f)
    }

    #[expect(dead_code, reason = "symmetric with `colored_stdout`")]
    pub(crate) fn colored_stderr<R, F: FnOnce(&mut dyn WriteColor) -> R>(&self, f: F) -> R {
        self.colored_stream_inner(StandardStream::stderr, self.config.stderr_is_tty, f)
    }

    fn colored_stream_inner<R, F, C>(&self, constructor: C, is_tty: bool, f: F) -> R
    where
        C: Fn(ColorChoice) -> StandardStream,
        F: FnOnce(&mut dyn WriteColor) -> R,
    {
        let choice = match self.config.color {
            flags::Color::Always => ColorChoice::Always,
            flags::Color::Never => ColorChoice::Never,
            flags::Color::Auto if !is_tty => ColorChoice::Never,
            flags::Color::Auto => ColorChoice::Auto,
        };
        let mut stream = constructor(choice);
        let result = f(&mut stream);
        stream.reset().unwrap();
        result
    }

    #[cfg_attr(not(feature = "tracing"), expect(dead_code))]
    pub(crate) fn report_summary(&self, path: &Path, start_time: Instant) {
        self.config.exec_ctx.profiler().report_summary(path, start_time);
    }

    #[cfg(feature = "tracing")]
    pub(crate) fn report_step_graph(self, directory: &Path) {
        self.step_graph.into_inner().store_to_dot_files(directory);
    }
}

impl AsRef<ExecutionContext> for Session {
    fn as_ref(&self) -> &ExecutionContext {
        &self.config.exec_ctx
    }
}

#[cfg(unix)]
fn chmod(path: &Path, perms: u32) {
    use std::os::unix::fs::*;
    t!(fs::set_permissions(path, fs::Permissions::from_mode(perms)));
}
#[cfg(windows)]
fn chmod(_path: &Path, _perms: u32) {}

/// The "package version" a component's tarball is named by on `channel`.
///
/// Trust: the `trust` channel names its archives `<version>-trust`
/// (`trustc-0.11.0-trust-<host>.tar.xz`), the names src/stage0 pins and the pack
/// cut admits (scripts/mint_and_prove_seed.sh). The 1.101 port (60669f9fc2) moved
/// this from lib.rs and dropped the arm, so a `trust` dist named them `-dev` and
/// the cut of 2ff339c653 (2026-10-22) produced `trustc-0.11.0-dev-*` archives.
pub(crate) fn package_vers(channel: &str, version: &str) -> String {
    match channel {
        "stable" => version.to_string(),
        "beta" => "beta".to_string(),
        "nightly" => "nightly".to_string(),
        "trust" => format!("{version}-trust"),
        _ => format!("{version}-dev"),
    }
}

/// Trust: where a tool `build_compiler` built for `target` is installed:
/// `<out>/<build host>/stage<N+1>-tools-bin/<target>/`. The target level keeps two
/// targets' builds of one tool apart, and the cut reads tools there
/// (`scripts/mint_seed_support.py` `find_build_manifest_tool`,
/// `scripts/recreate_bootstrap.py`, `scripts/seed_producer_contract.py`). The 1.101
/// port took upstream's level-less `tools_dir`, and the seed mint then found no
/// build-manifest.
pub(crate) fn tools_bin_dir(
    out: &Path,
    build_compiler: Compiler,
    target: TargetSelection,
) -> PathBuf {
    out.join(build_compiler.host)
        .join(format!("stage{}-tools-bin", build_compiler.stage + 1))
        .join(target.triple)
}
