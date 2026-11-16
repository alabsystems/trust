use crate::util::data_structures::HashMap;
use std::env;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use anyhow::Context as _;
use cargo_util::{Jobserver, ProcessBuilder, ProcessError, paths};
use filetime::FileTime;
use serde::{Deserialize, Serialize};
use tracing::{debug, info, warn};

use crate::compiler::{TRUST_TARGO_LANE_RUSTFLAGS_ENV, apply_env_config};
use crate::util::interning::InternedString;
use crate::util::process_authority::{
    LEGACY_TARGO_NESTED_UNVERIFIED_BROKER_ENV, TARGO_NESTED_UNVERIFIED_BROKER_ENV,
    configure_verified_tool_loader_environment, verified_tool_runtime_library_paths,
};
use crate::util::{CargoResult, GlobalContext, StableHasher};

// Trust: Targo's private protocol travels in the environment, and every
// `ProcessBuilder` built here inherits it. None of these are inputs the
// compiler should read ambiently — the per-unit values are routed as arguments
// by `compiler::prepare_rustc` — so they are stripped at construction rather
// than at each spawn site.
const TRUST_TARGO_INTERNAL_ENV: &[&str] = &[
    trust_test_execution::EXPORT_ENV,
    trust_test_execution::EXPORT_SESSION_ENV,
    TARGO_NESTED_UNVERIFIED_BROKER_ENV,
    LEGACY_TARGO_NESTED_UNVERIFIED_BROKER_ENV,
    TRUST_TARGO_LANE_RUSTFLAGS_ENV,
    "TRUST_TARGO_PREPARED_TEST_SESSION",
    "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
    "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
    "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
    "TRUST_TARGO_TEST_MONITOR_SESSION",
    "TRUST_TARGO_VERIFY",
    "TRUST_TARGO_FRONTEND",
];

pub(crate) fn scrub_trust_targo_internal_env(cmd: &mut ProcessBuilder) {
    for name in TRUST_TARGO_INTERNAL_ENV {
        cmd.env_remove(name);
    }
}

/// Information on the `rustc` executable
#[derive(Debug)]
pub struct Rustc {
    /// The location of the exe
    pub path: PathBuf,
    /// An optional program that will be passed the path of the rust exe as its first argument, and
    /// rustc args following this.
    pub wrapper: Option<PathBuf>,
    /// An optional wrapper to be used in addition to `rustc.wrapper` for workspace crates
    pub workspace_wrapper: Option<PathBuf>,
    /// Verbose version information (the output of `rustc -vV`)
    pub verbose_version: String,
    /// The rustc version (`1.23.4-beta.2`), this comes from `verbose_version`.
    pub version: semver::Version,
    /// The host tuple (arch-platform-OS), this comes from `verbose_version`.
    pub host: InternedString,
    /// The rustc full commit hash, this comes from `verbose_version`.
    pub commit_hash: Option<String>,
    // Trust: version/capability probes precede BuildRunner. Keep the same
    // checked imported transport on every compiler command, not only units.
    jobserver: Option<Jobserver>,
    // Only the prepared coordinator's parent planning context supplies this.
    // Each query keeps its real native owner instead of the parked Root's
    // process-global ordinary query executor.
    query_scope: Option<crate::context::compiler_query::Scoped>,
    cache: Mutex<Cache>,
    // Trust: the public version metadata keeps its workspace-facing semantics.
    // Only global units need the observation without the workspace wrapper;
    // preparing its command must not require that compiler to answer yet.
    global_version_command: Option<ProcessBuilder>,
    global_version_observation:
        OnceLock<Result<ObservedCompilerVersion, GlobalCompilerVersionError>>,
    // A native compiler's display version is not its executable identity.
    content_identity: Option<CompilerContentIdentity>,
    compiler_inputs: Option<CompilerInputs>,
    compiler_inputs_error: Option<String>,
}

/// Version fields observed from the compiler command selected for one unit's scope.
#[derive(Clone, Copy)]
pub(crate) struct CompilerVersion<'a> {
    pub verbose_version: &'a str,
    pub version: &'a semver::Version,
    pub host: InternedString,
}

#[derive(Debug)]
struct ObservedCompilerVersion {
    verbose_version: String,
    version: semver::Version,
    host: InternedString,
}

impl ObservedCompilerVersion {
    fn parse(verbose_version: String) -> CargoResult<Self> {
        let host = compiler_version_field(&verbose_version, "host: ")?.into();
        let version =
            semver::Version::parse(compiler_version_field(&verbose_version, "release: ")?)
                .with_context(|| {
                    format!(
                        "rustc version does not appear to be a valid semver version, from:\n{}",
                        verbose_version
                    )
                })?;
        Ok(Self {
            verbose_version,
            version,
            host,
        })
    }

    fn borrowed(&self) -> CompilerVersion<'_> {
        CompilerVersion {
            verbose_version: &self.verbose_version,
            version: &self.version,
            host: self.host,
        }
    }
}

fn compiler_version_field<'a>(verbose_version: &'a str, field: &str) -> CargoResult<&'a str> {
    verbose_version
        .lines()
        .find_map(|line| line.strip_prefix(field))
        .ok_or_else(|| {
            anyhow::format_err!(
                "`rustc -vV` didn't have a line for `{}`, got:\n{}",
                field.trim(),
                verbose_version
            )
        })
}

#[derive(Clone, Debug)]
struct GlobalCompilerVersionError(Arc<anyhow::Error>);

impl std::fmt::Display for GlobalCompilerVersionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("failed to query global compiler version")
    }
}

impl std::error::Error for GlobalCompilerVersionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(self.0.as_ref().as_ref())
    }
}

impl Rustc {
    /// Runs the compiler at `path` to learn various pieces of information about
    /// it, with an optional wrapper.
    ///
    /// If successful this function returns a description of the compiler along
    /// with a list of its capabilities.
    #[tracing::instrument(skip(gctx))]
    pub fn new(
        path: PathBuf,
        wrapper: Option<PathBuf>,
        workspace_wrapper: Option<PathBuf>,
        rustup_rustc: &Path,
        cache_location: Option<PathBuf>,
        gctx: &GlobalContext,
    ) -> CargoResult<Rustc> {
        let jobserver = gctx.jobserver_from_env()?.cloned();
        let mut compiler_inputs = CompilerInputs::default();
        let content_identity = crate::is_targo_invocation().then(|| {
            let launch = CompilerLaunch {
                path: path.clone(),
                wrapper: wrapper.clone(),
                workspace_wrapper: workspace_wrapper.clone(),
                rustup_rustc: rustup_rustc.to_path_buf(),
            };
            gctx.compiler_content_captures().capture(
                launch,
                &mut compiler_inputs,
                |compiler_inputs| {
                    let global_sysroot = compiler_sysroot(&path, wrapper.as_deref(), None, gctx)
                        .context("failed to query the compiler sysroot")?;
                    let workspace_sysroot = if workspace_wrapper.is_some() {
                        compiler_sysroot(
                            &path,
                            wrapper.as_deref(),
                            workspace_wrapper.as_deref(),
                            gctx,
                        )?
                    } else {
                        global_sysroot.clone()
                    };
                    compiler_content_identity_with_inputs(
                        &path,
                        wrapper.as_deref(),
                        workspace_wrapper.as_deref(),
                        rustup_rustc,
                        Some((&global_sysroot, &workspace_sysroot)),
                        gctx,
                        compiler_inputs,
                    )
                    .context("failed to capture compiler content")
                },
            )
        });
        let artifact_identity = content_identity.as_ref().map(|identity| {
            identity
                .as_ref()
                .copied()
                .unwrap_or_else(|_| CompilerContentIdentity::uncacheable())
        });
        let mut compiler_inputs_error = content_identity
            .as_ref()
            .and_then(|identity| identity.as_ref().err())
            .map(|error| format!("{error:#}"));
        let compiler_inputs = content_identity
            .as_ref()
            .is_some_and(|identity| identity.is_ok())
            .then_some(compiler_inputs)
            .filter(|inputs| match inputs.ensure_directories_current() {
                Ok(()) => true,
                Err(error) => {
                    compiler_inputs_error = Some(format!("{error:#}"));
                    false
                }
            });
        let mut cache = Cache::load(
            wrapper.as_deref(),
            workspace_wrapper.as_deref(),
            &path,
            rustup_rustc,
            cache_location,
            gctx,
            content_identity.as_ref(),
        );

        let version_command = |workspace_wrapper: Option<&Path>| -> CargoResult<ProcessBuilder> {
            let mut cmd = ProcessBuilder::new(&path)
                .wrapped(workspace_wrapper)
                .wrapped(wrapper.as_deref());
            if let Some(server) = &jobserver {
                cmd.inherit_jobserver(server);
            }
            apply_env_config(gctx, &mut cmd)?;
            scrub_trust_targo_internal_env(&mut cmd);
            if crate::is_targo_invocation() && crate::trust_verified_targo() {
                configure_verified_tool_loader_environment(&mut cmd, &path)?;
            }
            cmd.env(crate::CARGO_ENV, gctx.cargo_exe()?);
            cmd.arg("-vV");
            gctx.configure_compiler_query(&mut cmd);
            Ok(cmd)
        };
        let cmd = version_command(workspace_wrapper.as_deref())?;
        let ObservedCompilerVersion {
            verbose_version,
            version,
            host,
        } = ObservedCompilerVersion::parse(cache.cached_output(&cmd, 0)?.0)?;
        let global_version_command = workspace_wrapper
            .as_ref()
            .map(|_| version_command(None))
            .transpose()?;

        let commit_hash = compiler_version_field(&verbose_version, "commit-hash: ").ok().map(|hash| {
            // Possible commit-hash values from rustc are SHA hex string and "unknown". See:
            // * https://github.com/rust-lang/rust/blob/531cb83fc/src/bootstrap/src/utils/channel.rs#L73
            // * https://github.com/rust-lang/rust/blob/531cb83fc/compiler/rustc_driver_impl/src/lib.rs#L911-L913
            #[cfg(debug_assertions)]
            if hash != "unknown" {
                debug_assert!(
                    hash.chars().all(|ch| ch.is_ascii_hexdigit()),
                    "commit hash must be a hex string, got: {hash:?}"
                );
                debug_assert!(
                    hash.len() == 40 || hash.len() == 64,
                    "hex string must be generated from sha1 or sha256 (i.e., it must be 40 or 64 characters long)\ngot: {hash:?}"
                );
            }
            hash.to_string()
        });

        Ok(Rustc {
            path,
            wrapper,
            workspace_wrapper,
            verbose_version,
            version,
            host,
            commit_hash,
            jobserver,
            query_scope: gctx.compiler_query_scope(),
            cache: Mutex::new(cache),
            global_version_command,
            global_version_observation: OnceLock::new(),
            content_identity: artifact_identity,
            compiler_inputs,
            compiler_inputs_error,
        })
    }

    /// Observe every version field through the wrappers actually used by this
    /// scope. A failed global query refuses global layout/key requests without
    /// preventing workspace-only builds or borrowing the workspace observation.
    pub(crate) fn version_observation(&self, workspace: bool) -> CargoResult<CompilerVersion<'_>> {
        match (workspace, self.global_version_command.as_ref()) {
            (false, Some(command)) => self
                .global_version_observation
                .get_or_init(|| {
                    self.cache
                        .lock()
                        .unwrap()
                        .cached_output(command, 0)
                        .and_then(|(stdout, _)| ObservedCompilerVersion::parse(stdout))
                        .map_err(|error| GlobalCompilerVersionError(Arc::new(error)))
                })
                .as_ref()
                .map(ObservedCompilerVersion::borrowed)
                .map_err(|error| anyhow::Error::new(error.clone())),
            _ => Ok(CompilerVersion {
                verbose_version: &self.verbose_version,
                version: &self.version,
                host: self.host,
            }),
        }
    }

    /// Native artifact identity includes the compiler and the wrappers actually
    /// used for this unit. Installation paths remain inputs until relocation is
    /// established; version labels alone never establish equal compiler bytes.
    pub(crate) fn artifact_fingerprint(&self, workspace: bool) -> CargoResult<u64> {
        let verbose_version = self.version_observation(workspace)?.verbose_version;
        Ok(match self.content_identity {
            Some(identity) => crate::util::hash_u64((
                verbose_version,
                if workspace {
                    identity.workspace
                } else {
                    identity.global
                },
            )),
            None => crate::util::hash_u64(verbose_version),
        })
    }

    /// Stable native compiler variant for artifact layout. A failed identity
    /// may force rebuilding, but must not allocate a fresh cache directory on
    /// every invocation.
    pub(crate) fn content_variant(&self, workspace: bool) -> Option<u64> {
        self.content_identity
            .filter(|identity| identity.cacheable)
            .map(|identity| {
                if workspace {
                    identity.workspace
                } else {
                    identity.global
                }
            })
    }

    pub(crate) fn full_content_identity(&self, workspace: bool) -> Option<[u8; 32]> {
        self.content_identity
            .filter(|identity| identity.cacheable)
            .map(|identity| {
                if workspace {
                    identity.workspace_full
                } else {
                    identity.global_full
                }
            })
    }

    pub(crate) fn compiler_inputs(&self) -> CargoResult<&CompilerInputs> {
        self.compiler_inputs.as_ref().ok_or_else(|| {
            anyhow::anyhow!(
                "confined compilation requires a captured compiler input inventory: {}",
                self.compiler_inputs_error
                    .as_deref()
                    .unwrap_or("no native compiler capture")
            )
        })
    }

    /// Probe both source checksums and used-binary dependency tracking rather
    /// than assuming either option from a version label. Native content reuse
    /// needs both: an explicit `--extern` can change without a Cargo graph edge.
    /// This parsing-only query is cached with the other compiler capabilities.
    pub(crate) fn supports_checksum_depinfo(&self, gctx: &GlobalContext) -> CargoResult<bool> {
        // A workspace wrapper can select a different effective compiler from
        // the one used for registry dependencies. Both must support the flag.
        // Without a workspace wrapper the second query is an in-memory hit.
        for mut command in [self.process(), self.workspace_process()] {
            apply_env_config(gctx, &mut command)?;
            command.args(&[
                "-Zchecksum-hash-algorithm=blake3",
                "-Zbinary-dep-depinfo",
                "--print=cfg",
            ]);
            if self.cached_output(&command, 0).is_err() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Only probe static flag support here. Actual tool lookup facts depend on
    /// the final compiler command and filesystem, so this query cache must
    /// never supply them. Both effective compilers must accept the data flag.
    pub(crate) fn supports_tool_input_depinfo(&self, gctx: &GlobalContext) -> CargoResult<bool> {
        for mut command in [self.process(), self.workspace_process()] {
            apply_env_config(gctx, &mut command)?;
            command.args(&["-Ztrust-tool-inputs", "--print=cfg"]);
            if self.cached_output(&command, 0).is_err() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Gets a process builder set up to use the found rustc version, with a wrapper if `Some`.
    pub fn process(&self) -> ProcessBuilder {
        let mut cmd = ProcessBuilder::new(self.path.as_path()).wrapped(self.wrapper.as_ref());
        self.configure_jobserver(&mut cmd);
        // Trust: the certified-monitor selector is a per-compilation-unit
        // channel routed by `compiler::prepare_rustc`, never ambient rustc
        // state. This also keeps target-info probes from observing a test
        // marker and answering differently than they will for real units.
        scrub_trust_targo_internal_env(&mut cmd);
        cmd.retry_with_argfile(true);
        if let Some(scope) = &self.query_scope {
            scope.configure(&mut cmd);
        }
        cmd
    }

    /// Gets a process builder set up to use the found rustc version, with a wrapper if `Some`.
    pub fn workspace_process(&self) -> ProcessBuilder {
        let mut cmd = ProcessBuilder::new(self.path.as_path())
            .wrapped(self.workspace_wrapper.as_ref())
            .wrapped(self.wrapper.as_ref());
        self.configure_jobserver(&mut cmd);
        scrub_trust_targo_internal_env(&mut cmd);
        cmd.retry_with_argfile(true);
        if let Some(scope) = &self.query_scope {
            scope.configure(&mut cmd);
        }
        cmd
    }

    pub fn process_no_wrapper(&self) -> ProcessBuilder {
        let mut cmd = ProcessBuilder::new(&self.path);
        self.configure_jobserver(&mut cmd);
        scrub_trust_targo_internal_env(&mut cmd);
        cmd.retry_with_argfile(true);
        if let Some(scope) = &self.query_scope {
            scope.configure(&mut cmd);
        }
        cmd
    }

    fn configure_jobserver(&self, cmd: &mut ProcessBuilder) {
        if let Some(server) = &self.jobserver {
            cmd.inherit_jobserver(server);
        }
    }

    /// Trust: close ambient and overlaid dynamic-loader authority before
    /// executing an authenticated rustc probe. Probes are spawned outside
    /// `Compilation::fill_env`, so they would otherwise be the one compiler
    /// execution path with no loader closure at all.
    pub fn configure_verified_loader_environment(
        &self,
        cmd: &mut ProcessBuilder,
    ) -> CargoResult<()> {
        if crate::is_targo_invocation() && crate::trust_verified_targo() {
            configure_verified_tool_loader_environment(cmd, &self.path)?;
        }
        Ok(())
    }

    /// Gets the output for the given command.
    ///
    /// This will return the cached value if available, otherwise it will run
    /// the command and cache the output.
    ///
    /// `extra_fingerprint` is extra data to include in the cache fingerprint.
    /// Use this if there is other information about the environment that may
    /// affect the output that is not part of `cmd`.
    ///
    /// Returns a tuple of strings `(stdout, stderr)`.
    pub fn cached_output(
        &self,
        cmd: &ProcessBuilder,
        extra_fingerprint: u64,
    ) -> CargoResult<(String, String)> {
        let mut cmd = cmd.clone();
        self.configure_verified_loader_environment(&mut cmd)?;
        self.cache
            .lock()
            .unwrap()
            .cached_output(&cmd, extra_fingerprint)
    }
}

/// It is a well known fact that `rustc` is not the fastest compiler in the
/// world.  What is less known is that even `rustc --version --verbose` takes
/// about a hundred milliseconds! Because we need compiler version info even
/// for no-op builds, we cache it here, based on compiler's mtime and rustup's
/// current toolchain.
///
/// <https://github.com/rust-lang/cargo/issues/5315>
/// <https://github.com/rust-lang/rust/issues/49761>
#[derive(Debug)]
struct Cache {
    cache_location: Option<PathBuf>,
    dirty: bool,
    data: CacheData,
}

#[derive(Serialize, Deserialize, Debug, Default)]
struct CacheData {
    rustc_fingerprint: u64,
    outputs: HashMap<u64, Output>,
    successes: HashMap<u64, bool>,
}

#[derive(Serialize, Deserialize, Debug)]
struct Output {
    success: bool,
    status: String,
    code: Option<i32>,
    stdout: String,
    stderr: String,
}

impl Cache {
    fn load(
        wrapper: Option<&Path>,
        workspace_wrapper: Option<&Path>,
        rustc: &Path,
        rustup_rustc: &Path,
        cache_location: Option<PathBuf>,
        gctx: &GlobalContext,
        native_identity: Option<&CargoResult<CompilerContentIdentity>>,
    ) -> Cache {
        let fingerprint = match native_identity {
            Some(Ok(identity)) => Ok(identity.workspace),
            Some(Err(error)) => Err(anyhow::anyhow!(
                "cannot identify compiler inputs: {error:#}"
            )),
            None => rustc_fingerprint(wrapper, workspace_wrapper, rustc, rustup_rustc, gctx),
        };
        match (cache_location, fingerprint) {
            (Some(cache_location), Ok(rustc_fingerprint)) => {
                let empty = CacheData {
                    rustc_fingerprint,
                    outputs: HashMap::default(),
                    successes: HashMap::default(),
                };
                let mut dirty = true;
                let data = match read(&cache_location) {
                    Ok(data) => {
                        if data.rustc_fingerprint == rustc_fingerprint {
                            debug!("reusing existing rustc info cache");
                            dirty = false;
                            data
                        } else {
                            debug!("different compiler, creating new rustc info cache");
                            empty
                        }
                    }
                    Err(e) => {
                        debug!("failed to read rustc info cache: {}", e);
                        empty
                    }
                };
                return Cache {
                    cache_location: Some(cache_location),
                    dirty,
                    data,
                };

                fn read(path: &Path) -> CargoResult<CacheData> {
                    let json = paths::read(path)?;
                    Ok(serde_json::from_str(&json)?)
                }
            }
            (_, fingerprint) => {
                if let Err(e) = fingerprint {
                    warn!("failed to calculate rustc fingerprint: {}", e);
                }
                debug!("rustc info cache disabled");
                Cache {
                    cache_location: None,
                    dirty: false,
                    data: CacheData::default(),
                }
            }
        }
    }

    fn cached_output(
        &mut self,
        cmd: &ProcessBuilder,
        extra_fingerprint: u64,
    ) -> CargoResult<(String, String)> {
        let key = process_fingerprint(cmd, extra_fingerprint)?;
        let fresh_output;
        let output = if cmd
            .get_args()
            .any(|arg| arg.as_encoded_bytes().starts_with(b"@"))
        {
            // Trust: the process key names the response file, not its contents.
            // Never read or publish that query as a stable fact, including a
            // legacy success which could mask the command's current failure.
            self.dirty |= self.data.outputs.remove(&key).is_some();
            debug!("rustc query has an untracked argument file; bypassing output cache");
            fresh_output = Self::query_output(cmd)?;
            &fresh_output
        } else {
            if let std::collections::hash_map::Entry::Vacant(e) = self.data.outputs.entry(key) {
                debug!("rustc info cache miss");
                e.insert(Self::query_output(cmd)?);
                self.dirty = true;
            } else {
                debug!("rustc info cache hit");
            }
            &self.data.outputs[&key]
        };
        if output.success {
            Ok((output.stdout.clone(), output.stderr.clone()))
        } else {
            Err(ProcessError::new_raw(
                &format!("process didn't exit successfully: {}", cmd),
                output.code,
                &output.status,
                Some(output.stdout.as_ref()),
                Some(output.stderr.as_ref()),
            )
            .into())
        }
    }

    fn query_output(cmd: &ProcessBuilder) -> CargoResult<Output> {
        debug!("running {}", cmd);
        let output = crate::context::compiler_query::output(cmd)?;
        let stdout = String::from_utf8(output.stdout)
            .map_err(|e| anyhow::anyhow!("{}: {:?}", e, e.as_bytes()))
            .with_context(|| format!("`{}` didn't return utf8 output", cmd))?;
        let stderr = String::from_utf8(output.stderr)
            .map_err(|e| anyhow::anyhow!("{}: {:?}", e, e.as_bytes()))
            .with_context(|| format!("`{}` didn't return utf8 output", cmd))?;
        Ok(Output {
            success: output.status.success(),
            status: if output.status.success() {
                String::new()
            } else {
                cargo_util::exit_status_to_string(output.status)
            },
            code: output.status.code(),
            stdout,
            stderr,
        })
    }
}

impl Drop for Cache {
    fn drop(&mut self) {
        if !self.dirty {
            return;
        }
        if let Some(ref path) = self.cache_location {
            let json = serde_json::to_string(&self.data).unwrap();
            match paths::write(path, json.as_bytes()) {
                Ok(()) => info!("updated rustc info cache"),
                Err(e) => warn!("failed to update rustc info cache: {}", e),
            }
        }
    }
}

/// Content supplied by the launcher, known runtime libraries, wrappers and
/// reported sysroot libraries. This does not establish complete loader
/// authority, arbitrary wrapper reads or flag-selected sysroot inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompilerContentIdentity {
    global: u64,
    workspace: u64,
    global_full: [u8; 32],
    workspace_full: [u8; 32],
    cacheable: bool,
}

// Keep the existing short layout hash while retaining a full cryptographic
// digest of the same input stream. File bytes are still read only once.
struct CompilerIdentityHasher {
    short: StableHasher,
    full: blake3::Hasher,
}

impl CompilerIdentityHasher {
    fn new() -> Self {
        Self {
            short: StableHasher::new(),
            full: blake3::Hasher::new(),
        }
    }
    fn full(&self) -> [u8; 32] {
        *self.full.finalize().as_bytes()
    }
}

macro_rules! compiler_identity_integer {
    ($($method:ident: $type:ty),* $(,)?) => {
        $(fn $method(&mut self, value: $type) {
            self.short.$method(value);
            self.full.update(&value.to_le_bytes());
        })*
    };
}

impl Hasher for CompilerIdentityHasher {
    fn finish(&self) -> u64 {
        Hasher::finish(&self.short)
    }
    fn write(&mut self, bytes: &[u8]) {
        self.short.write(bytes);
        self.full.update(bytes);
    }
    fn write_usize(&mut self, value: usize) {
        self.short.write_usize(value);
        self.full.update(&(value as u64).to_le_bytes());
    }
    fn write_isize(&mut self, value: isize) {
        self.short.write_isize(value);
        self.full.update(&(value as i64).to_le_bytes());
    }
    compiler_identity_integer! {
        write_u8: u8, write_u16: u16, write_u32: u32, write_u64: u64, write_u128: u128,
        write_i8: i8, write_i16: i16, write_i32: i32, write_i64: i64, write_i128: i128,
    }
}

/// The compiler launch a content capture describes.
#[derive(Debug, PartialEq, Eq)]
struct CompilerLaunch {
    path: PathBuf,
    wrapper: Option<PathBuf>,
    workspace_wrapper: Option<PathBuf>,
    rustup_rustc: PathBuf,
}

/// One command's compiler-content consistency records, kept by `GlobalContext`.
/// Every construction captures current compiler/sysroot bytes and selection
/// again. A previous observation is only a consistency guard, never a digest
/// cache or an immutable-input owner. Same-launch content or inventory drift
/// refuses the capture; the caller cannot attach its prior identity to it.
/// Nothing is persisted or shared between commands. A failed capture is not kept.
#[derive(Debug, Default)]
pub(crate) struct CompilerContentCaptures(
    std::sync::Mutex<Vec<(CompilerLaunch, CompilerContentIdentity, CompilerInputs)>>,
);

impl CompilerContentCaptures {
    fn capture(
        &self,
        launch: CompilerLaunch,
        inputs: &mut CompilerInputs,
        capture: impl FnOnce(&mut CompilerInputs) -> CargoResult<CompilerContentIdentity>,
    ) -> CargoResult<CompilerContentIdentity> {
        let mut captures = self
            .0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let identity = capture(inputs)?;
        if let Some((_, previous, recorded)) = captures.iter().find(|(kept, ..)| *kept == launch) {
            if identity != *previous || inputs != recorded {
                anyhow::bail!("compiler input content or inventory changed within one command");
            }
        } else {
            captures.push((launch, identity, inputs.clone()));
        }
        Ok(identity)
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .len()
    }
}

/// The paths whose contents formed the compiler identity. Confinement must
/// grant these exact inputs, not the entire SDK containing them.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CompilerInputs {
    pub files: std::collections::BTreeSet<PathBuf>,
    pub executables: std::collections::BTreeSet<PathBuf>,
    directories: std::collections::BTreeMap<PathBuf, Vec<(std::ffi::OsString, u8)>>,
}

impl CompilerInputs {
    fn record_directory(&mut self, path: &Path) -> CargoResult<()> {
        let mut entries = Vec::new();
        for (index, entry) in std::fs::read_dir(path)
            .with_context(|| format!("failed to inventory compiler directory {}", path.display()))?
            .enumerate()
        {
            if index >= 100_000 {
                anyhow::bail!("compiler directory inventory exceeded its limit");
            }
            let entry = entry?;
            let kind = entry.file_type()?;
            entries.push((
                entry.file_name(),
                if kind.is_dir() {
                    1
                } else if kind.is_file() {
                    2
                } else if kind.is_symlink() {
                    3
                } else {
                    4
                },
            ));
        }
        entries.sort();
        self.directories.insert(path.to_path_buf(), entries);
        Ok(())
    }

    pub fn directories(&self) -> impl Iterator<Item = &PathBuf> {
        self.directories.keys()
    }

    pub fn directory_fingerprint(&self) -> u64 {
        crate::util::hash_u64(("targo-compiler-directory-membership-v1", &self.directories))
    }

    pub fn full_directory_fingerprint(&self) -> [u8; 32] {
        let mut hash = CompilerIdentityHasher::new();
        ("targo-compiler-directory-membership-v1", &self.directories).hash(&mut hash);
        hash.full()
    }

    fn ensure_directories_current(&self) -> CargoResult<()> {
        let mut current = Self::default();
        for path in self.directories.keys() {
            current.record_directory(path)?;
        }
        if current.directories != self.directories {
            anyhow::bail!("compiler directory membership changed during input capture");
        }
        Ok(())
    }
}

/// Ask the selected executable (including its wrappers), rather than guessing
/// a sysroot from the launcher installation. This query must precede accepting
/// a cached compiler probe: unchanged launcher bytes can select a new sysroot.
fn compiler_sysroot(
    compiler: &Path,
    wrapper: Option<&Path>,
    workspace_wrapper: Option<&Path>,
    gctx: &GlobalContext,
) -> CargoResult<PathBuf> {
    let mut command = ProcessBuilder::new(compiler)
        .wrapped(workspace_wrapper)
        .wrapped(wrapper);
    if let Some(server) = gctx.jobserver_from_env()? {
        command.inherit_jobserver(server);
    }
    apply_env_config(gctx, &mut command)?;
    scrub_trust_targo_internal_env(&mut command);
    if crate::trust_verified_targo() {
        configure_verified_tool_loader_environment(&mut command, compiler)?;
    }
    command.env(crate::CARGO_ENV, gctx.cargo_exe()?);
    // Trust: a scoped issued query selects its complete environment using the
    // final argv. Preserve the ordinary spelling and configure after appending it.
    command.arg("--print=sysroot");
    gctx.configure_compiler_query(&mut command);
    let output = crate::context::compiler_query::exec(&command)?;
    compiler_sysroot_output(&output.stdout)
}

/// Decode one reported path without normalizing a Unix filename's trailing CR
/// into a different tree. Windows forbids CR in filenames and retains its native
/// CRLF terminator; other platforms remove only the final LF.
fn compiler_sysroot_output(stdout: &[u8]) -> CargoResult<PathBuf> {
    let value = std::str::from_utf8(stdout)?;
    #[cfg(windows)]
    let value = value
        .strip_suffix("\r\n")
        .or_else(|| value.strip_suffix('\n'))
        .unwrap_or(value);
    #[cfg(not(windows))]
    let value = value.strip_suffix('\n').unwrap_or(value);
    let path = Path::new(value);
    if !path.is_absolute() || value.contains(['\r', '\n']) {
        anyhow::bail!("compiler did not report one absolute sysroot path");
    }
    Ok(path.canonicalize()?)
}

/// Static libraries are compiler inputs too. Inventory target library trees,
/// including self-contained linker objects, but not bundled source or tools.
/// Both directory membership and every file's path/content enter the identity.
fn sysroot_library_paths(root: &Path) -> CargoResult<std::collections::BTreeSet<PathBuf>> {
    let rustlib = root.join("lib/rustlib");
    let mut pending = Vec::new();
    for entry in std::fs::read_dir(&rustlib)? {
        let entry = entry?;
        if entry.file_type()?.is_symlink() {
            anyhow::bail!("sysroot target directory is a symlink");
        }
        if entry.file_type()?.is_dir() {
            let lib = entry.path().join("lib");
            match std::fs::symlink_metadata(&lib) {
                Ok(metadata) if metadata.is_dir() => pending.push(lib),
                Ok(_) => anyhow::bail!("sysroot target library root is not a plain directory"),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
        }
    }
    let mut paths = std::collections::BTreeSet::new();
    let mut count = 0;
    while let Some(directory) = pending.pop() {
        paths.insert(directory.clone());
        for entry in std::fs::read_dir(&directory)? {
            let entry = entry?;
            count += 1;
            if count > 100_000 {
                anyhow::bail!("sysroot library inventory exceeded its limit");
            }
            if entry.file_type()?.is_dir() {
                pending.push(entry.path());
            } else {
                paths.insert(entry.path());
            }
        }
    }
    Ok(paths)
}

#[cfg(test)]
fn hash_sysroot_libraries(
    root: &Path,
    hasher: &mut StableHasher,
    contents: &mut Vec<CapturedCompilerContent>,
) -> CargoResult<()> {
    hash_sysroot_libraries_with_inputs(root, hasher, contents, &mut CompilerInputs::default())
}

fn hash_sysroot_libraries_with_inputs(
    root: &Path,
    hasher: &mut impl Hasher,
    contents: &mut Vec<CapturedCompilerContent>,
    inputs: &mut CompilerInputs,
) -> CargoResult<()> {
    "targo-sysroot-library-content-v1".hash(hasher);
    root.hash(hasher);
    let paths = sysroot_library_paths(root)?;
    paths.len().hash(hasher);
    let mut directories = std::collections::BTreeSet::new();
    for path in &paths {
        if std::fs::symlink_metadata(&path)?.is_dir() {
            directories.insert(path);
        }
    }
    let files: Vec<PathBuf> = paths
        .iter()
        .filter(|path| !directories.contains(path))
        .cloned()
        .collect();
    let mut captured = capture_executable_contents(&files, contents, "sysroot input")?.into_iter();
    for path in &paths {
        if directories.contains(path) {
            inputs.record_directory(path)?;
            "directory".hash(hasher);
            path.hash(hasher);
        } else {
            "file".hash(hasher);
            captured
                .next()
                .context("sysroot capture lost an input")?
                .hash_into(hasher);
            inputs.files.insert(path.clone());
        }
    }
    if paths != sysroot_library_paths(root)? {
        anyhow::bail!("sysroot library inventory changed while hashing");
    }
    Ok(())
}

impl CompilerContentIdentity {
    fn uncacheable() -> Self {
        // Preserve valid compilation with an unreadable executable, but never
        // accept a persisted hit without an identity. One value per Rustc
        // object keeps units within this build coherent.
        static NEXT: portable_atomic::AtomicU64 = portable_atomic::AtomicU64::new(0);
        let value = crate::util::hash_u64((
            "uncacheable compiler",
            std::process::id(),
            std::time::SystemTime::now(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        ));
        Self {
            global: value,
            workspace: value,
            global_full: [0; 32],
            workspace_full: [0; 32],
            cacheable: false,
        }
    }
}

#[cfg(test)]
fn compiler_content_identity(
    rustc: &Path,
    wrapper: Option<&Path>,
    workspace_wrapper: Option<&Path>,
    rustup_rustc: &Path,
    sysroots: Option<(&Path, &Path)>,
    gctx: &GlobalContext,
) -> CargoResult<CompilerContentIdentity> {
    compiler_content_identity_with_inputs(
        rustc,
        wrapper,
        workspace_wrapper,
        rustup_rustc,
        sysroots,
        gctx,
        &mut CompilerInputs::default(),
    )
}

fn compiler_content_identity_with_inputs(
    rustc: &Path,
    wrapper: Option<&Path>,
    workspace_wrapper: Option<&Path>,
    rustup_rustc: &Path,
    sysroots: Option<(&Path, &Path)>,
    gctx: &GlobalContext,
    inputs: &mut CompilerInputs,
) -> CargoResult<CompilerContentIdentity> {
    let mut hasher = CompilerIdentityHasher::new();
    "targo-compiler-executable-content-v1".hash(&mut hasher);
    // Trust: the branded compiler's physical installation is authoritative;
    // a directory symlink spelling is not a different compiler. Preserve the
    // final basename and leave arbitrary wrapper launch spelling untouched.
    let identity_path = branded_compiler_identity_path(rustc, crate::is_targo_invocation())?;
    let selected = hash_executable_content(&identity_path, &mut hasher)?;
    inputs.files.insert(selected.clone());
    inputs.executables.insert(selected.clone());
    inputs.executables.insert(paths::resolve_executable(rustc)?);
    let mut runtime_roots = vec![selected];
    if rustc == rustup_rustc {
        // A rustup proxy's own bytes do not identify its selected compiler.
        let toolchain = gctx.get_env("RUSTUP_TOOLCHAIN")?;
        let root = if Path::new(&toolchain).is_absolute() {
            PathBuf::from(toolchain)
        } else {
            PathBuf::from(gctx.get_env("RUSTUP_HOME")?)
                .join("toolchains")
                .join(toolchain)
        };
        let selected = hash_executable_content(
            &root
                .join("bin")
                .join(format!("rustc{}", env::consts::EXE_SUFFIX)),
            &mut hasher,
        )?;
        inputs.files.insert(selected.clone());
        inputs.executables.insert(selected.clone());
        runtime_roots.push(selected);
    }
    let mut search_dirs = std::collections::BTreeSet::new();
    for tool in runtime_roots {
        for root in verified_tool_runtime_library_paths(&tool)
            .with_context(|| format!("failed to locate compiler runtime for {}", tool.display()))?
        {
            // Codegen backends are loaded explicitly rather than through the
            // ordinary runtime search path.
            if root.file_name().is_some_and(|name| name == "lib") {
                let backends = root.with_file_name("codegen-backends");
                match std::fs::metadata(&backends) {
                    Ok(metadata) if metadata.is_dir() => {
                        search_dirs.insert(backends);
                    }
                    Ok(_) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error.into()),
                }
            }
            search_dirs.insert(root);
        }
    }
    let mut libraries = std::collections::BTreeSet::new();
    for root in search_dirs {
        inputs.record_directory(&root)?;
        // Loader directories are flat namespaces. Recursing into lib/rustlib
        // would scan bundled source trees and unrelated tools, not just code
        // the compiler can load from these search directories.
        for (index, entry) in std::fs::read_dir(root)?.enumerate() {
            if index >= 100_000 {
                anyhow::bail!("compiler runtime library inventory exceeded its limit");
            }
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().to_ascii_lowercase();
            if name.ends_with(".dylib")
                || name.ends_with(".dll")
                || name.ends_with(".so")
                || name.contains(".so.")
            {
                libraries.insert(entry.path());
            }
        }
    }
    "runtime libraries".hash(&mut hasher);
    libraries.len().hash(&mut hasher);
    let mut contents = Vec::new();
    let libraries: Vec<PathBuf> = libraries.into_iter().collect();
    for captured in capture_executable_contents(&libraries, &mut contents, "compiler library")? {
        captured.hash_into(&mut hasher);
    }
    inputs.files.extend(libraries);
    if let Some(wrapper) = wrapper {
        let path = hash_executable_content(wrapper, &mut hasher)?;
        inputs.files.insert(path.clone());
        inputs.executables.insert(path);
    }
    if let Some((global, _)) = sysroots {
        hash_sysroot_libraries_with_inputs(global, &mut hasher, &mut contents, inputs)
            .with_context(|| format!("failed to inventory sysroot {}", global.display()))?;
    }
    let global = Hasher::finish(&hasher);
    let global_full = hasher.full();
    if let Some(wrapper) = workspace_wrapper {
        let path = hash_executable_content(wrapper, &mut hasher)?;
        inputs.files.insert(path.clone());
        inputs.executables.insert(path);
    }
    if let Some((global, workspace)) = sysroots {
        if global != workspace {
            hash_sysroot_libraries_with_inputs(workspace, &mut hasher, &mut contents, inputs)?;
        }
    }
    Ok(CompilerContentIdentity {
        global,
        workspace: Hasher::finish(&hasher),
        global_full,
        workspace_full: hasher.full(),
        cacheable: true,
    })
}

// Scoped to one identity capture, never persisted or shared between builds.
// Retaining the opened identity prevents inode reuse during alias detection.
struct CapturedCompilerContent {
    identity: crate::util::file_identity::OpenedFileIdentity,
    metadata: std::fs::Metadata,
    digest: [u8; 32],
}

fn matching_content_metadata(left: &std::fs::Metadata, right: &std::fs::Metadata) -> bool {
    if left.len() != right.len()
        || !left
            .modified()
            .ok()
            .zip(right.modified().ok())
            .is_some_and(|(l, r)| l == r)
    {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if (left.ctime(), left.ctime_nsec()) != (right.ctime(), right.ctime_nsec()) {
            return false;
        }
    }
    true
}

fn branded_compiler_identity_path(path: &Path, native: bool) -> CargoResult<PathBuf> {
    let expected = if cfg!(windows) {
        "trustc.exe"
    } else {
        "trustc"
    };
    if !native || path.file_name() != Some(std::ffi::OsStr::new(expected)) {
        return Ok(path.to_path_buf());
    }
    let resolved = paths::resolve_executable(path)?;
    let parent = resolved
        .parent()
        .context("compiler has no installation directory")?;
    let name = resolved
        .file_name()
        .context("compiler has no executable name")?;
    Ok(parent.canonicalize()?.join(name))
}

fn hash_executable_content(path: &Path, hasher: &mut impl Hasher) -> CargoResult<PathBuf> {
    hash_executable_content_with_cache(path, hasher, &mut Vec::new())
}

fn hash_executable_content_with_cache(
    path: &Path,
    hasher: &mut impl Hasher,
    contents: &mut Vec<CapturedCompilerContent>,
) -> CargoResult<PathBuf> {
    let retain = std::sync::atomic::AtomicUsize::new(64usize.saturating_sub(contents.len()));
    let (captured, retained) = capture_executable_content(path, contents, &retain)?;
    captured.hash_into(hasher);
    contents.extend(retained);
    Ok(captured.canonical)
}

/// What one compiler input contributes to the identity.
struct CapturedInput {
    resolved: PathBuf,
    canonical: PathBuf,
    digest: [u8; 32],
}

impl CapturedInput {
    // Preserve launch spelling and resolved location: relative runtime-library
    // lookup is not a demonstrated relocation axis yet. Ignore mere timestamps.
    fn hash_into(&self, hasher: &mut impl Hasher) {
        self.resolved.hash(hasher);
        self.canonical.hash(hasher);
        self.digest.hash(hasher);
    }
}

/// Capture `paths` on a bounded pool and return them in `paths` order, so the
/// identity hashes exactly what a serial capture hashes. Every file still gets
/// the whole open, read and recheck protocol and every byte is read:
/// parallelism changes when bytes are read, never which. Digests are reused
/// only for an opened object already captured by an earlier batch of the same
/// capture (COMPILER-CONTENT-ONCE-1), never across captures.
fn capture_executable_contents(
    paths: &[PathBuf],
    contents: &mut Vec<CapturedCompilerContent>,
    what: &str,
) -> CargoResult<Vec<CapturedInput>> {
    use rayon::prelude::*;
    // OpenedFileIdentity retains a handle on Unix: at most 64 are retained
    // across the capture, so concurrent workers hold a bounded descriptor set.
    let retain = std::sync::atomic::AtomicUsize::new(64usize.saturating_sub(contents.len()));
    let prior: &[CapturedCompilerContent] = contents;
    let capture = |path: &PathBuf| {
        capture_executable_content(path, prior, &retain)
            .with_context(|| format!("failed to capture {what} {}", path.display()))
    };
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    let pool = (threads > 1 && paths.len() > 1)
        .then(|| {
            rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .thread_name(|index| format!("targo-compiler-capture-{index}"))
                .build()
                .ok()
        })
        .flatten();
    let started = std::time::Instant::now();
    let captured: Vec<_> = match pool {
        Some(pool) => pool.install(|| paths.par_iter().map(capture).collect()),
        None => paths.iter().map(capture).collect(),
    };
    tracing::debug!(
        files = paths.len(),
        threads,
        elapsed_ms = started.elapsed().as_millis() as u64,
        "captured {what} content"
    );
    let mut inputs = Vec::with_capacity(captured.len());
    let mut retained = Vec::new();
    for result in captured {
        let (input, entry) = result?;
        inputs.push(input);
        retained.extend(entry);
    }
    contents.extend(retained);
    Ok(inputs)
}

/// A file longer than this is read and digested as BLAKE3 subtrees on the
/// capture pool's threads, each subtree read at its own offset, so the largest
/// compiler library (the 625 MB driver) is not one thread's serial read.
const PARALLEL_DIGEST_FILE: u64 = 8 << 20;
/// The subtree a capture worker reads and digests in one piece.
const PARALLEL_DIGEST_LEAF: u64 = 4 << 20;

fn digest_regular_file(file: &mut std::fs::File, len: u64) -> CargoResult<[u8; 32]> {
    // Only a capture pool's worker splits a file: a serial capture must not
    // start rayon's global pool.
    #[cfg(unix)]
    {
        if len > PARALLEL_DIGEST_FILE && rayon::current_thread_index().is_some() {
            return digest_file_subtrees(file, len, PARALLEL_DIGEST_LEAF);
        }
    }
    use std::io::Read as _;
    let mut digest = blake3::Hasher::new();
    let mut bytes = vec![0; len.clamp(64 * 1024, 4 << 20) as usize];
    let mut total = 0;
    loop {
        let n = file.read(&mut bytes)?;
        if n == 0 {
            break;
        }
        total += n as u64;
        if total > len {
            anyhow::bail!("compiler input grew while hashing");
        }
        digest.update(&bytes[..n]);
    }
    if total != len {
        anyhow::bail!("compiler input shrank while hashing");
    }
    Ok(*digest.finalize().as_bytes())
}

/// The BLAKE3 hash of the first `len` bytes of `file`, computed as the tree
/// BLAKE3 defines: every subtree is split where `left_subtree_len` says, each
/// leaf is read with `pread` at its offset, and children join on the current
/// rayon pool. The result equals `blake3::hash` of the same bytes. A file that
/// shrinks fails a read; one that grows or changes is refused by the caller's
/// metadata recheck, exactly as for a serial read.
#[cfg(unix)]
fn digest_file_subtrees(file: &std::fs::File, len: u64, leaf: u64) -> CargoResult<[u8; 32]> {
    use blake3::hazmat::{
        ChainingValue, HasherExt as _, Mode, left_subtree_len, merge_subtrees_non_root,
        merge_subtrees_root,
    };
    use std::os::unix::fs::FileExt as _;
    fn subtree(
        file: &std::fs::File,
        offset: u64,
        len: u64,
        leaf: u64,
    ) -> CargoResult<ChainingValue> {
        if len <= leaf {
            let mut bytes = vec![0; len as usize];
            file.read_exact_at(&mut bytes, offset)
                .context("compiler input shrank while hashing")?;
            return Ok(blake3::Hasher::new()
                .set_input_offset(offset)
                .update(&bytes)
                .finalize_non_root());
        }
        let left = left_subtree_len(len);
        let (l, r) = rayon::join(
            || subtree(file, offset, left, leaf),
            || subtree(file, offset + left, len - left, leaf),
        );
        Ok(merge_subtrees_non_root(&l?, &r?, Mode::Hash))
    }
    assert!(leaf >= blake3::CHUNK_LEN as u64 && leaf % blake3::CHUNK_LEN as u64 == 0);
    if len <= leaf {
        let mut bytes = vec![0; len as usize];
        file.read_exact_at(&mut bytes, 0)
            .context("compiler input shrank while hashing")?;
        return Ok(*blake3::hash(&bytes).as_bytes());
    }
    let left = left_subtree_len(len);
    let (l, r) = rayon::join(
        || subtree(file, 0, left, leaf),
        || subtree(file, left, len - left, leaf),
    );
    Ok(*merge_subtrees_root(&l?, &r?, Mode::Hash).as_bytes())
}

fn capture_executable_content(
    path: &Path,
    contents: &[CapturedCompilerContent],
    retain: &std::sync::atomic::AtomicUsize,
) -> CargoResult<(CapturedInput, Option<CapturedCompilerContent>)> {
    let resolved = paths::resolve_executable(path)
        .with_context(|| format!("failed to resolve compiler input {}", path.display()))?;
    let canonical = resolved
        .canonicalize()
        .with_context(|| format!("failed to resolve compiler input {}", resolved.display()))?;
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let mut file = options
        .open(&canonical)
        .with_context(|| format!("failed to open compiler input {}", canonical.display()))?;
    let before = file.metadata()?;
    if !before.is_file() || before.len() > 8 * 1024 * 1024 * 1024 {
        anyhow::bail!(
            "compiler input is not a bounded regular file: {}",
            resolved.display()
        );
    }
    let opened = crate::util::file_identity::opened_file_identity(&file)?;
    let previous = contents.iter().find(|entry| {
        entry.identity == opened && matching_content_metadata(&entry.metadata, &before)
    });
    let digest = if let Some(entry) = previous {
        entry.digest
    } else {
        digest_regular_file(&mut file, before.len())?
    };
    let after = file.metadata()?;
    let rebound = options
        .open(&canonical)
        .with_context(|| format!("failed to recheck compiler input {}", canonical.display()))?;
    if !matching_content_metadata(&before, &after)
        || opened != crate::util::file_identity::opened_file_identity(&rebound)?
        || resolved.canonicalize()? != canonical
    {
        anyhow::bail!(
            "compiler input changed while hashing: {}",
            resolved.display()
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if (before.ctime(), before.ctime_nsec()) != (after.ctime(), after.ctime_nsec()) {
            anyhow::bail!(
                "compiler input changed while hashing: {}",
                resolved.display()
            );
        }
    }
    // OpenedFileIdentity retains a handle on Unix. Bound descriptor use;
    // additional files are still hashed and validated, simply without reuse.
    let take_slot = || {
        use std::sync::atomic::Ordering::Relaxed;
        let mut left = retain.load(Relaxed);
        while left > 0 {
            match retain.compare_exchange_weak(left, left - 1, Relaxed, Relaxed) {
                Ok(_) => return true,
                Err(now) => left = now,
            }
        }
        false
    };
    let retained = (previous.is_none() && take_slot()).then_some(CapturedCompilerContent {
        identity: opened,
        metadata: after,
        digest,
    });
    Ok((
        CapturedInput {
            resolved,
            canonical,
            digest,
        },
        retained,
    ))
}

fn rustc_fingerprint(
    wrapper: Option<&Path>,
    workspace_wrapper: Option<&Path>,
    rustc: &Path,
    rustup_rustc: &Path,
    gctx: &GlobalContext,
) -> CargoResult<u64> {
    let mut hasher = StableHasher::new();

    let hash_exe = |hasher: &mut _, path| -> CargoResult<()> {
        let path = paths::resolve_executable(path)?;
        path.hash(hasher);

        let meta = paths::metadata(&path)?;
        meta.len().hash(hasher);

        // Often created and modified are the same, but not all filesystems support the former,
        // and distro reproducible builds may clamp the latter, so we try to use both.
        FileTime::from_creation_time(&meta).hash(hasher);
        FileTime::from_last_modification_time(&meta).hash(hasher);
        Ok(())
    };

    hash_exe(&mut hasher, rustc)?;
    if let Some(wrapper) = wrapper {
        hash_exe(&mut hasher, wrapper)?;
    }
    if let Some(workspace_wrapper) = workspace_wrapper {
        hash_exe(&mut hasher, workspace_wrapper)?;
    }

    // Rustup can change the effective compiler without touching
    // the `rustc` binary, so we try to account for this here.
    // If we see rustup's env vars, we mix them into the fingerprint,
    // but we also mix in the mtime of the actual compiler (and not
    // the rustup shim at `~/.cargo/bin/rustup`), because `RUSTUP_TOOLCHAIN`
    // could be just `stable-x86_64-unknown-linux-gnu`, i.e, it could
    // not mention the version of Rust at all, which changes after
    // `rustup update`.
    //
    // If we don't see rustup env vars, but it looks like the compiler
    // is managed by rustup, we conservatively bail out.
    let maybe_rustup = rustup_rustc == rustc;
    match (
        maybe_rustup,
        gctx.get_env("RUSTUP_HOME"),
        gctx.get_env("RUSTUP_TOOLCHAIN"),
    ) {
        (_, Ok(rustup_home), Ok(rustup_toolchain)) => {
            debug!("adding rustup info to rustc fingerprint");
            rustup_toolchain.hash(&mut hasher);
            rustup_home.hash(&mut hasher);
            let real_rustc = Path::new(&rustup_home)
                .join("toolchains")
                .join(rustup_toolchain)
                .join("bin")
                .join("rustc")
                .with_extension(env::consts::EXE_EXTENSION);
            paths::mtime(&real_rustc)?.hash(&mut hasher);
        }
        (true, _, _) => anyhow::bail!("probably rustup rustc, but without rustup's env vars"),
        _ => (),
    }

    Ok(Hasher::finish(&hasher))
}

fn process_fingerprint(cmd: &ProcessBuilder, extra_fingerprint: u64) -> CargoResult<u64> {
    let mut hasher = StableHasher::new();
    // Trust: cached failures from the former transport are not current facts.
    crate::context::compiler_query::TRANSPORT_POLICY.hash(&mut hasher);
    cmd.has_jobserver().hash(&mut hasher);
    cmd.get_program().hash(&mut hasher);
    match cmd.get_cwd() {
        Some(cwd) => cwd.to_owned(),
        None => std::env::current_dir()?,
    }
    .hash(&mut hasher);
    // A selected native snapshot can differ while every explicit override is
    // equal. Include all actual raw environment bytes rather than serving an
    // old query from another prepared coordinator's context. Values stay in
    // memory; only their bounded digest enters the cache key.
    #[cfg(unix)]
    cargo_util::EnvironmentInputs::capture_effective(cmd)?
        .digest()
        .hash(&mut hasher);
    extra_fingerprint.hash(&mut hasher);
    cmd.get_args().for_each(|arg| arg.hash(&mut hasher));
    let mut env = cmd.get_envs().iter().collect::<Vec<_>>();
    env.sort_unstable();
    env.hash(&mut hasher);
    Ok(Hasher::finish(&hasher))
}

#[cfg(test)]
mod compiler_content_tests {
    use super::*;

    #[test]
    fn complete_version_observation_keeps_raw_release_and_host() {
        let raw = "rustc display banner\nhost: global-host\nrelease: 1.101.0-beta.3\n";
        let observed = ObservedCompilerVersion::parse(raw.into()).unwrap();
        let version = observed.borrowed();
        assert_eq!(version.verbose_version, raw);
        assert_eq!(version.version.pre.as_str(), "beta.3");
        assert_eq!(version.host.as_str(), "global-host");
        for raw in [
            "host: global-host\nrelease: invalid\n",
            "host: global-host\n",
            "release: 1.101.0-dev\n",
        ] {
            assert!(ObservedCompilerVersion::parse(raw.into()).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn global_version_failure_is_lazy_retained_and_scoped_to_global_artifact_keys() {
        let compiler = Rustc {
            path: PathBuf::from("unused-compiler"),
            wrapper: None,
            workspace_wrapper: Some(PathBuf::from("workspace-wrapper")),
            verbose_version: "workspace compiler observation".into(),
            version: semver::Version::new(1, 101, 0),
            host: "native".into(),
            commit_hash: None,
            jobserver: None,
            query_scope: None,
            cache: Mutex::new(Cache {
                cache_location: None,
                dirty: false,
                data: CacheData::default(),
            }),
            global_version_command: Some(ProcessBuilder::new("/usr/bin/false")),
            global_version_observation: OnceLock::new(),
            content_identity: Some(CompilerContentIdentity {
                global: 1,
                workspace: 2,
                global_full: [1; 32],
                workspace_full: [2; 32],
                cacheable: true,
            }),
            compiler_inputs: None,
            compiler_inputs_error: None,
        };
        let workspace = compiler.artifact_fingerprint(true).unwrap();
        assert!(compiler.global_version_observation.get().is_none());
        let first = compiler.artifact_fingerprint(false).unwrap_err();
        assert!(
            first.chain().any(|cause| cause.is::<ProcessError>()),
            "retain the typed query failure: {first:#}"
        );
        let retained = compiler
            .global_version_observation
            .get()
            .unwrap()
            .as_ref()
            .unwrap_err()
            .clone();
        let second = compiler.artifact_fingerprint(false).unwrap_err();
        assert!(second.chain().any(|cause| cause.is::<ProcessError>()));
        assert!(Arc::ptr_eq(
            &retained.0,
            &compiler
                .global_version_observation
                .get()
                .unwrap()
                .as_ref()
                .unwrap_err()
                .0
        ));
        assert_eq!(workspace, compiler.artifact_fingerprint(true).unwrap());
    }

    #[test]
    fn compiler_sysroot_output_accepts_one_native_absolute_path() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().canonicalize().unwrap();
        for output in [
            expected.display().to_string(),
            format!("{}\n", expected.display()),
        ] {
            assert_eq!(
                compiler_sysroot_output(output.as_bytes()).unwrap(),
                expected
            );
        }
    }

    #[test]
    fn compiler_sysroot_output_rejects_multiline_relative_and_non_utf8_values() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().canonicalize().unwrap();
        for output in [
            format!("{}\n{}\n", path.display(), path.display()),
            format!("{}\n\n", path.display()),
            "relative\n".into(),
            "\n".into(),
        ] {
            assert!(
                compiler_sysroot_output(output.as_bytes()).is_err(),
                "{output:?}"
            );
        }
        assert!(compiler_sysroot_output(b"\xff\n").is_err());
    }

    #[cfg(unix)]
    #[test]
    fn compiler_sysroot_output_never_normalizes_carriage_return_into_a_sibling() {
        let root = tempfile::tempdir().unwrap();
        let sibling = root.path().join("sysroot");
        let selected = root.path().join("sysroot\r");
        std::fs::create_dir(&sibling).unwrap();
        std::fs::create_dir(&selected).unwrap();
        let ordinary = format!("{}\n", sibling.display());
        assert_eq!(
            compiler_sysroot_output(ordinary.as_bytes()).unwrap(),
            sibling.canonicalize().unwrap()
        );
        let reported = format!("{}\n", selected.display());
        assert!(selected.is_dir());
        assert!(
            compiler_sysroot_output(reported.as_bytes()).is_err(),
            "the real CR-ending root must not silently select its existing sibling"
        );
        assert!(compiler_sysroot_output(selected.as_os_str().as_encoded_bytes()).is_err());
    }

    #[cfg(windows)]
    #[test]
    fn compiler_sysroot_output_accepts_the_windows_crlf_terminator() {
        let root = tempfile::tempdir().unwrap();
        let expected = root.path().canonicalize().unwrap();
        let output = format!("{}\r\n", expected.display());
        assert_eq!(
            compiler_sysroot_output(output.as_bytes()).unwrap(),
            expected
        );
    }

    #[test]
    fn full_compiler_digest_preserves_the_existing_lookup_hash() {
        let input = (
            "compiler",
            Path::new("/sdk/lib"),
            vec![1_u8, 2, 3],
            129_u64,
            Some(7_usize),
        );
        let mut short = StableHasher::new();
        input.hash(&mut short);
        let mut full = CompilerIdentityHasher::new();
        input.hash(&mut full);
        assert_eq!(Hasher::finish(&short), full.finish());
        let mut changed = CompilerIdentityHasher::new();
        (
            "compiler",
            Path::new("/sdk/lib"),
            vec![1_u8, 2, 4],
            129_u64,
            Some(7_usize),
        )
            .hash(&mut changed);
        assert_ne!(full.full(), changed.full());
    }

    #[test]
    fn captured_compiler_files_exclude_unhashed_sdk_contents() {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        std::fs::create_dir(root.join("bin")).unwrap();
        std::fs::create_dir_all(root.join("lib/rustlib/native/lib")).unwrap();
        let compiler = root.join("bin/compiler");
        let driver = root.join("lib/driver.dylib");
        let core = root.join("lib/rustlib/native/lib/libcore.rlib");
        let other_tool = root.join("bin/documentation-tool");
        std::fs::write(&compiler, b"compiler").unwrap();
        std::fs::write(&driver, b"driver").unwrap();
        std::fs::write(&core, b"core").unwrap();
        std::fs::write(&other_tool, b"not a compiler input").unwrap();
        let gctx = GlobalContext::default().unwrap();
        let capture = || {
            let mut inputs = CompilerInputs::default();
            let identity = compiler_content_identity_with_inputs(
                &compiler,
                None,
                None,
                Path::new("unused-rustup"),
                Some((&root, &root)),
                &gctx,
                &mut inputs,
            )
            .unwrap();
            (identity, inputs)
        };
        let (before, inputs) = capture();
        assert!(inputs.files.contains(&compiler));
        assert!(inputs.files.contains(&driver));
        assert!(inputs.files.contains(&core));
        assert!(!inputs.files.contains(&other_tool));
        let membership = inputs.directory_fingerprint();
        let unrecorded = root.join("lib/unrelated.txt");
        std::fs::write(&unrecorded, b"directory membership").unwrap();
        assert!(inputs.ensure_directories_current().is_err());
        let (after, inputs) = capture();
        assert_eq!(
            before.global, after.global,
            "ordinary compiler-byte identity is unchanged"
        );
        assert_ne!(membership, inputs.directory_fingerprint());
        assert!(!inputs.files.contains(&unrecorded));
    }

    #[test]
    fn sysroot_libraries_track_bytes_membership_and_nested_objects() {
        let root = tempfile::tempdir().unwrap();
        let lib = root.path().join("lib/rustlib/native/lib");
        std::fs::create_dir_all(lib.join("self-contained")).unwrap();
        let core = lib.join("libcore.rlib");
        std::fs::write(&core, b"core one").unwrap();
        let capture = || {
            let mut hash = StableHasher::new();
            hash_sysroot_libraries(root.path(), &mut hash, &mut Vec::new()).unwrap();
            Hasher::finish(&hash)
        };
        let first = capture();
        let stamp = FileTime::from_last_modification_time(&std::fs::metadata(&core).unwrap());
        filetime::set_file_mtime(&core, FileTime::from_unix_time(1, 0)).unwrap();
        assert_eq!(first, capture());
        std::fs::write(&core, b"core two").unwrap();
        filetime::set_file_mtime(&core, stamp).unwrap();
        assert_ne!(first, capture());
        std::fs::write(&core, b"core one").unwrap();
        assert_eq!(first, capture());
        let object = lib.join("self-contained/crtbegin.o");
        std::fs::write(&object, b"linker input").unwrap();
        assert_ne!(first, capture());
        std::fs::remove_file(&object).unwrap();
        assert_eq!(first, capture());
        std::fs::create_dir_all(root.path().join("lib/rustlib/src")).unwrap();
        std::fs::write(root.path().join("lib/rustlib/src/file.rs"), "source").unwrap();
        assert_eq!(
            first,
            capture(),
            "bundled sources are not compiler libraries"
        );
    }

    #[cfg(unix)]
    #[test]
    fn sysroot_directory_redirection_is_not_a_cache_identity() {
        let root = tempfile::tempdir().unwrap();
        let lib = root.path().join("lib/rustlib/native/lib");
        std::fs::create_dir_all(lib.parent().unwrap()).unwrap();
        let other = root.path().join("elsewhere");
        std::fs::create_dir(&other).unwrap();
        std::os::unix::fs::symlink(other, lib).unwrap();
        assert!(
            hash_sysroot_libraries(root.path(), &mut StableHasher::new(), &mut Vec::new()).is_err()
        );
    }

    fn identity(path: &Path) -> u64 {
        let mut hash = StableHasher::new();
        hash_executable_content(path, &mut hash).unwrap();
        Hasher::finish(&hash)
    }

    #[cfg(unix)]
    #[test]
    fn branded_compiler_directory_aliases_share_identity_without_relocating_tools() {
        let root = tempfile::tempdir().unwrap();
        let real = root.path().join("16387.noindex");
        let relocated = root.path().join("other-sdk");
        for path in [&real, &relocated] {
            std::fs::create_dir_all(path.join("bin")).unwrap();
            std::fs::write(path.join("bin/trustc"), b"same compiler bytes").unwrap();
        }
        let alias = root.path().join("16387");
        std::os::unix::fs::symlink(&real, &alias).unwrap();
        let canonical = real.join("bin/trustc");
        let via_alias = alias.join("bin/trustc");
        let hash = |path: &Path| identity(&branded_compiler_identity_path(path, true).unwrap());
        assert_eq!(hash(&canonical), hash(&via_alias));
        assert_ne!(hash(&canonical), hash(&relocated.join("bin/trustc")));
        assert_eq!(
            branded_compiler_identity_path(&via_alias, false).unwrap(),
            via_alias
        );
        let wrapper = alias.join("bin/wrapper");
        assert_eq!(
            branded_compiler_identity_path(&wrapper, true).unwrap(),
            wrapper
        );
        std::fs::remove_file(&alias).unwrap();
        std::os::unix::fs::symlink(&relocated, &alias).unwrap();
        assert_ne!(hash(&canonical), hash(&via_alias));
    }

    #[test]
    fn content_identity_ignores_timestamps_but_observes_equal_size_edits() {
        let root = tempfile::tempdir().unwrap();
        let executable = root.path().join("compiler");
        std::fs::write(&executable, b"version one").unwrap();
        let timestamp =
            FileTime::from_last_modification_time(&std::fs::metadata(&executable).unwrap());
        let before = identity(&executable);
        filetime::set_file_mtime(&executable, FileTime::from_unix_time(1, 0)).unwrap();
        assert_eq!(before, identity(&executable));
        std::fs::write(&executable, b"version two").unwrap();
        filetime::set_file_mtime(&executable, timestamp).unwrap();
        assert_ne!(before, identity(&executable));
    }

    #[test]
    fn compiler_runtime_library_content_is_an_input() {
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join("bin")).unwrap();
        std::fs::create_dir(root.path().join("lib")).unwrap();
        let compiler = root.path().join("bin/compiler");
        let library = root.path().join("lib/libcompiler.dylib");
        std::fs::write(&compiler, b"launcher").unwrap();
        std::fs::write(&library, b"driver one").unwrap();
        let gctx = GlobalContext::default().unwrap();
        let capture = || {
            compiler_content_identity(
                &compiler,
                None,
                None,
                Path::new("unused-rustup"),
                None,
                &gctx,
            )
            .unwrap()
        };
        let before = capture();
        let sources = root.path().join("lib/rustlib/src");
        std::fs::create_dir_all(&sources).unwrap();
        std::fs::write(sources.join("unrelated.so"), b"source fixture").unwrap();
        assert_eq!(
            before.global,
            capture().global,
            "source trees are not loader directories"
        );
        let timestamp =
            FileTime::from_last_modification_time(&std::fs::metadata(&library).unwrap());
        std::fs::write(&library, b"driver two").unwrap();
        filetime::set_file_mtime(&library, timestamp).unwrap();
        let after = capture();
        assert_ne!(before.global, after.global);
        filetime::set_file_mtime(&library, FileTime::from_unix_time(1, 0)).unwrap();
        assert_eq!(after.global, capture().global);
    }

    #[test]
    fn same_launch_must_not_reuse_content_after_compiler_input_mutation() {
        let mut stale = Vec::new();
        for changed in [
            "bin/compiler",
            "lib/driver.dylib",
            "lib/rustlib/native/lib/libcore.rlib",
            "bin/workspace-wrapper",
            "directory-membership",
        ] {
            let temporary = tempfile::tempdir().unwrap();
            let root = temporary.path().canonicalize().unwrap();
            std::fs::create_dir_all(root.join("bin")).unwrap();
            std::fs::create_dir_all(root.join("lib/rustlib/native/lib")).unwrap();
            for name in [
                "bin/compiler",
                "lib/driver.dylib",
                "lib/rustlib/native/lib/libcore.rlib",
                "bin/workspace-wrapper",
            ] {
                std::fs::write(root.join(name), b"original bytes").unwrap();
            }
            let compiler = root.join("bin/compiler");
            let workspace_wrapper = root.join("bin/workspace-wrapper");
            let gctx = GlobalContext::default().unwrap();
            let launch = || CompilerLaunch {
                path: compiler.clone(),
                wrapper: None,
                workspace_wrapper: Some(workspace_wrapper.clone()),
                rustup_rustc: PathBuf::from("unused-rustup"),
            };
            let capture = |inputs: &mut CompilerInputs| {
                compiler_content_identity_with_inputs(
                    &compiler,
                    None,
                    Some(&workspace_wrapper),
                    Path::new("unused-rustup"),
                    Some((&root, &root)),
                    &gctx,
                    inputs,
                )
            };
            let captures = CompilerContentCaptures::default();
            let first = captures
                .capture(launch(), &mut CompilerInputs::default(), capture)
                .unwrap();
            if changed == "directory-membership" {
                std::fs::write(root.join("lib/unrelated.txt"), b"new unrecorded member").unwrap();
            } else {
                let path = root.join(changed);
                let stamp =
                    FileTime::from_last_modification_time(&std::fs::metadata(&path).unwrap());
                std::fs::write(&path, b"mutated! bytes").unwrap();
                filetime::set_file_mtime(&path, stamp).unwrap();
            }
            let mut fresh_inputs = CompilerInputs::default();
            let fresh = capture(&mut fresh_inputs).unwrap();
            if changed == "directory-membership" {
                assert_eq!(
                    first, fresh,
                    "an unrelated member changes inventory, not compiler bytes"
                );
            } else {
                assert!(
                    first.global_full != fresh.global_full
                        || first.workspace_full != fresh.workspace_full,
                    "physical mutation was not detected: {changed}"
                );
                if changed == "bin/workspace-wrapper" {
                    assert_eq!(
                        first.global_full, fresh.global_full,
                        "isolate workspace-only identity drift"
                    );
                }
            }
            let mut inputs = CompilerInputs::default();
            match captures.capture(launch(), &mut inputs, capture) {
                Err(_) => {} // A refusal is safe too.
                Ok(identity) => {
                    if inputs.ensure_directories_current().is_err() {
                        continue; // The caller also refuses an outdated inventory.
                    }
                    if identity != fresh || inputs != fresh_inputs {
                        stale.push(changed);
                    }
                }
            }
        }
        assert!(
            stale.is_empty(),
            "same launch accepted stale compiler content after mutation: {stale:?}"
        );
    }

    #[test]
    fn one_command_recaptures_each_compiler_launch_and_checks_consistency() {
        let captures = CompilerContentCaptures::default();
        let launch = |path: &str| CompilerLaunch {
            path: PathBuf::from(path),
            wrapper: None,
            workspace_wrapper: None,
            rustup_rustc: PathBuf::from("rustup-rustc"),
        };
        let identity = |value| CompilerContentIdentity {
            global: value,
            workspace: value,
            global_full: [0; 32],
            workspace_full: [0; 32],
            cacheable: true,
        };
        let runs = std::cell::Cell::new(0);
        let capture = |value, inputs: &mut CompilerInputs| {
            runs.set(runs.get() + 1);
            inputs.files.insert(PathBuf::from("libstd.rlib"));
            Ok(identity(value))
        };
        let mut first = CompilerInputs::default();
        let a = captures
            .capture(launch("trustc"), &mut first, |inputs| capture(1, inputs))
            .unwrap();
        let mut second = CompilerInputs::default();
        let b = captures
            .capture(launch("trustc"), &mut second, |inputs| capture(1, inputs))
            .unwrap();
        assert_eq!(
            runs.get(),
            2,
            "the second construction captures current inputs again"
        );
        assert_eq!((a.global, b.global), (1, 1));
        assert_eq!(second.files, first.files);
        let drift = captures
            .capture(launch("trustc"), &mut CompilerInputs::default(), |inputs| {
                capture(2, inputs)
            })
            .unwrap_err();
        assert!(
            drift
                .to_string()
                .contains("compiler input content or inventory changed within one command")
        );
        captures
            .capture(launch("other"), &mut CompilerInputs::default(), |inputs| {
                capture(3, inputs)
            })
            .unwrap();
        assert_eq!(
            runs.get(),
            4,
            "a refused drift and another compiler are both captured"
        );
        assert!(
            captures
                .capture(launch("failing"), &mut CompilerInputs::default(), |_| {
                    anyhow::bail!("unreadable")
                })
                .is_err()
        );
        assert_eq!(captures.len(), 2, "a failed capture is not kept");
    }

    #[test]
    fn parallel_capture_hashes_what_a_serial_capture_hashes() {
        let root = tempfile::tempdir().unwrap();
        let mut paths = Vec::new();
        for index in 0..12 {
            let path = root.path().join(format!("lib{index}.rlib"));
            std::fs::write(&path, format!("library {index}").repeat(index * 97 + 1)).unwrap();
            paths.push(path);
        }
        // Larger than one read block and than the parallel digest threshold.
        let large: Vec<u8> = (0..(9 << 20) + 7)
            .map(|i: usize| (i * 31 % 251) as u8)
            .collect();
        let driver = root.path().join("librustc_driver.dylib");
        std::fs::write(&driver, &large).unwrap();
        let alias = root.path().join("alias.dylib");
        std::fs::hard_link(&driver, &alias).unwrap();
        paths.extend([driver.clone(), alias]);

        let mut serial = StableHasher::new();
        let mut serial_contents = Vec::new();
        for path in &paths {
            hash_executable_content_with_cache(path, &mut serial, &mut serial_contents).unwrap();
        }
        let mut parallel = StableHasher::new();
        let mut parallel_contents = Vec::new();
        let captured =
            capture_executable_contents(&paths, &mut parallel_contents, "test input").unwrap();
        for input in &captured {
            input.hash_into(&mut parallel);
        }
        assert_eq!(Hasher::finish(&serial), Hasher::finish(&parallel));
        let driver_digest = captured
            .iter()
            .find(|input| input.resolved == driver)
            .unwrap()
            .digest;
        assert_eq!(driver_digest, *blake3::hash(&large).as_bytes());

        // A later batch reuses an earlier batch's opened object, and a byte
        // change behind an unchanged length and timestamp is still seen.
        let timestamp = FileTime::from_last_modification_time(&std::fs::metadata(&driver).unwrap());
        let mut changed = large.clone();
        changed[5 << 20] ^= 1;
        std::fs::write(&driver, &changed).unwrap();
        filetime::set_file_mtime(&driver, timestamp).unwrap();
        let recaptured =
            capture_executable_contents(&[driver.clone()], &mut Vec::new(), "test input").unwrap();
        assert_eq!(recaptured[0].digest, *blake3::hash(&changed).as_bytes());
    }

    #[cfg(unix)]
    #[test]
    fn subtree_digest_is_the_blake3_hash_at_every_shape() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("input");
        let chunk = blake3::CHUNK_LEN as u64;
        let lengths = [
            0,
            1,
            chunk - 1,
            chunk,
            chunk + 1,
            2 * chunk,
            3 * chunk + 17,
            7 * chunk,
            8 * chunk,
            9 * chunk - 1,
            64 * chunk + 1,
            1000 * chunk + 333,
        ];
        for len in lengths {
            let bytes: Vec<u8> = (0..len).map(|i| (i * 131 % 251) as u8).collect();
            std::fs::write(&path, &bytes).unwrap();
            let file = std::fs::File::open(&path).unwrap();
            for leaf in [chunk, 2 * chunk, 3 * chunk, 16 * chunk] {
                assert_eq!(
                    digest_file_subtrees(&file, len, leaf).unwrap(),
                    *blake3::hash(&bytes).as_bytes(),
                    "length {len}, leaf {leaf}"
                );
            }
            if len > 0 {
                assert!(
                    digest_file_subtrees(&file, len + chunk, chunk).is_err(),
                    "a file shorter than its recorded length is refused"
                );
            }
        }
    }

    #[test]
    fn hardlinked_runtime_inputs_share_one_capture_but_still_detect_mutation() {
        let root = tempfile::tempdir().unwrap();
        let first = root.path().join("first.dylib");
        let alias = root.path().join("alias.dylib");
        std::fs::write(&first, b"driver one").unwrap();
        std::fs::hard_link(&first, &alias).unwrap();
        let timestamp = FileTime::from_last_modification_time(&std::fs::metadata(&first).unwrap());
        let mut contents = Vec::new();
        hash_executable_content_with_cache(&first, &mut StableHasher::new(), &mut contents)
            .unwrap();
        let mut old = StableHasher::new();
        hash_executable_content_with_cache(&alias, &mut old, &mut contents).unwrap();
        assert_eq!(
            contents.len(),
            1,
            "one opened object needs one content capture"
        );
        std::fs::write(&first, b"driver two").unwrap();
        filetime::set_file_mtime(&first, timestamp).unwrap();
        let mut changed = StableHasher::new();
        hash_executable_content_with_cache(&alias, &mut changed, &mut contents).unwrap();
        assert_ne!(Hasher::finish(&old), Hasher::finish(&changed));
    }

    #[test]
    fn workspace_wrapper_does_not_invalidate_registry_compilations() {
        let root = tempfile::tempdir().unwrap();
        let compiler = root.path().join("compiler");
        let wrapper = root.path().join("workspace-wrapper");
        std::fs::write(&compiler, b"compiler").unwrap();
        std::fs::write(&wrapper, b"wrapper one").unwrap();
        let gctx = GlobalContext::default().unwrap();
        let before = compiler_content_identity(
            &compiler,
            None,
            Some(&wrapper),
            Path::new("unused-rustup"),
            None,
            &gctx,
        )
        .unwrap();
        std::fs::write(&wrapper, b"wrapper two").unwrap();
        let after = compiler_content_identity(
            &compiler,
            None,
            Some(&wrapper),
            Path::new("unused-rustup"),
            None,
            &gctx,
        )
        .unwrap();
        assert_eq!(before.global, after.global);
        assert_ne!(before.workspace, after.workspace);

        let global_root = root.path().join("global");
        let workspace_root = root.path().join("workspace");
        for sysroot in [&global_root, &workspace_root] {
            let libraries = sysroot.join("lib/rustlib/native/lib");
            std::fs::create_dir_all(&libraries).unwrap();
            std::fs::write(libraries.join("libcore.rlib"), b"core one").unwrap();
        }
        let capture = || {
            compiler_content_identity(
                &compiler,
                None,
                Some(&wrapper),
                Path::new("unused-rustup"),
                Some((&global_root, &workspace_root)),
                &gctx,
            )
            .unwrap()
        };
        let before = capture();
        std::fs::write(
            workspace_root.join("lib/rustlib/native/lib/libcore.rlib"),
            b"core two",
        )
        .unwrap();
        let after = capture();
        assert_eq!(before.global, after.global);
        assert_ne!(before.workspace, after.workspace);
    }
}

#[cfg(test)]
mod trust_internal_env_tests {
    use cargo_util::ProcessBuilder;

    use super::{TRUST_TARGO_INTERNAL_ENV, scrub_trust_targo_internal_env};

    // Trust (T14a): the lane targo trust hands Cargo reaches no compiler,
    // probe or wrapper; every `Rustc` process builder starts without it.
    #[test]
    fn compiler_processes_never_see_the_lane_or_the_other_private_controls() {
        let mut command = ProcessBuilder::new("trustc");
        for name in TRUST_TARGO_INTERNAL_ENV {
            command.env(name, "private");
        }
        command.env("FIXTURE_MODE", "kept");
        scrub_trust_targo_internal_env(&mut command);
        assert!(TRUST_TARGO_INTERNAL_ENV.contains(&"TRUST_TARGO_LANE_RUSTFLAGS"));
        for name in TRUST_TARGO_INTERNAL_ENV {
            assert_eq!(command.get_env(name), None, "{name}");
        }
        assert!(command.get_env("FIXTURE_MODE").is_some());
    }
}

// Trust: exercise the actual cache with a retained former-policy failure.
#[cfg(all(test, unix))]
mod compiler_query_cache_tests {
    use super::*;

    fn response_query(file: &Path) -> ProcessBuilder {
        let mut argument = std::ffi::OsString::from("@");
        argument.push(file.as_os_str());
        let mut command = ProcessBuilder::new("/bin/sh");
        command
            .args(&["-c", "cat \"${1#@}\"", "query"])
            .arg(argument);
        command
    }

    fn empty_cache() -> Cache {
        Cache {
            cache_location: None,
            dirty: false,
            data: CacheData::default(),
        }
    }

    #[test]
    fn selected_environment_and_working_directory_do_not_share_stale_query_outputs() {
        let root = tempfile::tempdir().unwrap();
        let first_dir = root.path().join("first");
        let second_dir = root.path().join("second");
        for dir in [&first_dir, &second_dir] {
            std::fs::create_dir(dir).unwrap();
        }
        // Darwin's temporary root may be spelled /var while pwd reports its
        // /private/var physical directory. Compare actual working directories.
        let first_dir = first_dir.canonicalize().unwrap();
        let second_dir = second_dir.canonicalize().unwrap();
        let mut command = ProcessBuilder::new("/bin/sh");
        command
            .args(&["-c", "printf '%s:' \"$QUERY_CONTEXT\"; pwd"])
            .cwd(&first_dir);
        let snapshot = |value: &str| {
            cargo_util::EnvironmentInputs::from_variables([("QUERY_CONTEXT".into(), value.into())])
                .unwrap()
        };
        command.environment_snapshot(snapshot("first"));
        let explicit = command.get_envs().clone();
        let mut cache = empty_cache();
        assert_eq!(
            cache.cached_output(&command, 0).unwrap().0,
            format!("first:{}\n", first_dir.display())
        );
        command.environment_snapshot(snapshot("second"));
        assert_eq!(
            command.get_envs(),
            &explicit,
            "explicit overrides alone cannot identify the snapshot"
        );
        assert_eq!(
            cache.cached_output(&command, 0).unwrap().0,
            format!("second:{}\n", first_dir.display())
        );
        command.cwd(&second_dir);
        assert_eq!(
            cache.cached_output(&command, 0).unwrap().0,
            format!("second:{}\n", second_dir.display())
        );
        assert_eq!(cache.data.outputs.len(), 3);
    }

    #[test]
    fn selected_non_unicode_environment_participates_in_query_identity() {
        use std::os::unix::ffi::OsStringExt as _;
        let mut command = ProcessBuilder::new("/bin/sh");
        let key = std::ffi::OsString::from_vec(b"QUERY_\xff".to_vec());
        command.environment_snapshot(
            cargo_util::EnvironmentInputs::from_variables([(
                key.clone(),
                std::ffi::OsString::from_vec(b"one_\xfe".to_vec()),
            )])
            .unwrap(),
        );
        let before = process_fingerprint(&command, 0).unwrap();
        command.environment_snapshot(
            cargo_util::EnvironmentInputs::from_variables([(
                key,
                std::ffi::OsString::from_vec(b"two_\xfe".to_vec()),
            )])
            .unwrap(),
        );
        assert_ne!(before, process_fingerprint(&command, 0).unwrap());
    }

    #[test]
    fn response_query_observes_changed_file_contents() {
        let root = tempfile::tempdir().unwrap();
        let file = root.path().join("compiler.args");
        std::fs::write(&file, "first query").unwrap();
        let command = response_query(&file);
        let key = process_fingerprint(&command, 0).unwrap();
        let mut cache = empty_cache();
        assert_eq!(cache.cached_output(&command, 0).unwrap().0, "first query");
        std::fs::write(&file, "second query").unwrap();
        assert_eq!(cache.cached_output(&command, 0).unwrap().0, "second query");
        assert!(!cache.data.outputs.contains_key(&key));
    }

    #[test]
    fn response_query_retires_old_success_before_actual_failure() {
        let root = tempfile::tempdir().unwrap();
        let command = response_query(&root.path().join("missing.args"));
        let key = process_fingerprint(&command, 0).unwrap();
        let mut cache = empty_cache();
        cache.data.outputs.insert(
            key,
            Output {
                success: true,
                status: String::new(),
                code: Some(0),
                stdout: "stale success".into(),
                stderr: String::new(),
            },
        );
        let error = cache
            .cached_output(&command, 0)
            .err()
            .expect("cached success must not mask an unreadable response file");
        assert!(
            error
                .to_string()
                .contains("process didn't exit successfully"),
            "{error:#}"
        );
        assert!(!cache.data.outputs.contains_key(&key));
        assert!(cache.dirty, "the old persisted fact must be removed");
    }

    #[test]
    fn response_free_query_keeps_ordinary_cache_behavior() {
        let root = tempfile::tempdir().unwrap();
        let counter = root.path().join("calls");
        std::fs::write(&counter, "").unwrap();
        let mut command = ProcessBuilder::new("/bin/sh");
        command
            .args(&["-c", "printf 1 >> \"$1\"; printf normal", "query"])
            .arg(&counter);
        let mut cache = empty_cache();
        assert_eq!(cache.cached_output(&command, 0).unwrap().0, "normal");
        assert_eq!(cache.cached_output(&command, 0).unwrap().0, "normal");
        assert_eq!(std::fs::read_to_string(&counter).unwrap(), "1");
        assert!(cache.data.outputs[&process_fingerprint(&command, 0).unwrap()].success);
    }

    #[test]
    fn former_policy_cached_75_does_not_answer_a_new_query() {
        let mut command = ProcessBuilder::new("/bin/sh");
        command.args(&["-c", "printf fresh-query"]);
        // Exact predecessor process key: extra fingerprint, argv, sorted env.
        let mut legacy = StableHasher::new();
        0_u64.hash(&mut legacy);
        command.get_args().for_each(|arg| arg.hash(&mut legacy));
        let mut env = command.get_envs().iter().collect::<Vec<_>>();
        env.sort_unstable();
        env.hash(&mut legacy);
        let old = Hasher::finish(&legacy);
        let current = process_fingerprint(&command, 0).unwrap();
        assert_ne!(old, current);
        let mut cache = Cache {
            cache_location: None,
            dirty: false,
            data: CacheData::default(),
        };
        cache.data.outputs.insert(
            old,
            Output {
                success: false,
                status: "exit status: 75".into(),
                code: Some(75),
                stdout: String::new(),
                stderr: "no GNU transport".into(),
            },
        );
        assert_eq!(cache.cached_output(&command, 0).unwrap().0, "fresh-query");
        assert_eq!(cache.data.outputs[&old].code, Some(75));
        assert!(cache.data.outputs[&current].success);
    }
}
