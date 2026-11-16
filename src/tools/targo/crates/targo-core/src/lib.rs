//! # Cargo as a library
//!
//! This is the reusable `targo_core` engine, exposed to callers through the
//! `targo` facade (docs/trust-naming.md). The rest of this page is upstream's
//! description of cargo-the-library, whose design it shares.
//!
//! There are two places you can find API documentation of cargo-the-library,
//!
//! - <https://docs.rs/cargo>: targeted at external tool developers using cargo-the-library
//!   - Released with every rustc release
//! - <https://doc.rust-lang.org/nightly/nightly-rustc/cargo>: targeted at cargo contributors
//!   - Updated on each update of the `cargo` submodule in `rust-lang/rust`
//!
//! <div class="warning">
//!
//! This library is maintained by the Cargo team, primarily for use by Cargo
//! and not intended for external use.
//! This crate may make major changes to its APIs or assumptions about how it is invoked (e.g.
//! when it is safe to call [git2::transport::register]).
//!
//! See [The Cargo Book: External tools] for alternatives to using this library.
//!
//! </div>
//!
//! ## Overview
//!
//! Major components of cargo include:
//!
//! - [`ops`]:
//!   Every major operation is implemented here. Each command is a thin wrapper around ops.
//!   - [`ops::cargo_compile`]:
//!     This is the entry point for all the compilation commands. This is a
//!     good place to start if you want to follow how compilation starts and
//!     flows to completion.
//! - [`ops::resolve`]:
//!   Top-level API for dependency and feature resolver (e.g. [`ops::resolve_ws`])
//!   - [`resolver`]: The core algorithm
//! - [`compiler`]:
//!   This is the code responsible for running `rustc` and `rustdoc`.
//!   - [`compiler::build_context`]:
//!     The [`BuildContext`][compiler::BuildContext] is the result of the "front end" of the
//!     build process. This contains the graph of work to perform and any settings necessary for
//!     `rustc`. After this is built, the next stage of building is handled in
//!     [`BuildRunner`][compiler::BuildRunner].
//!   - [`compiler::build_runner`]:
//!     The `Context` is the mutable state used during the build process. This
//!     is the core of the build process, and everything is coordinated through
//!     this.
//!   - [`compiler::fingerprint`]:
//!     The `fingerprint` module contains all the code that handles detecting
//!     if a crate needs to be recompiled.
//! - [`sources::source`]:
//!   The [`sources::source::Source`] trait is an abstraction over different sources of packages.
//!   Sources are uniquely identified by a [`workspace::SourceId`]. Sources are implemented in the [`sources`]
//!   directory.
//! - [`diagnostics`]: Home of diagnostic [passes][diagnostics::passes] and their
//!   [rules][diagnostics::rules].
//! - [`util`]:
//!   This directory contains generally-useful utility modules.
//! - [`context`]:
//!   This directory contains the global application context.
//!   This includes the config parser which makes heavy use of
//!   [serde](https://serde.rs/) to merge and translate config values.
//!   The [`util::GlobalContext`] is usually accessed from the
//!   [`workspace::Workspace`]
//!   though references to it are scattered around for more convenient access.
//! - [`workspace::parser`]:
//!   This directory contains the code for parsing `Cargo.toml` files.
//!   - [`ops::lockfile`]:
//!     This is where `Cargo.lock` files are loaded and saved.
//!
//! Related crates:
//! - [`cargo-platform`](https://crates.io/crates/cargo-platform)
//!   ([nightly docs](https://doc.rust-lang.org/nightly/nightly-rustc/cargo_platform)):
//!   This library handles parsing `cfg` expressions.
//! - [`cargo-util`](https://crates.io/crates/cargo-util)
//!   ([nightly docs](https://doc.rust-lang.org/nightly/nightly-rustc/cargo_util)):
//!   This contains general utility code that is shared between cargo and the testsuite
//! - [`cargo-util-schemas`](https://crates.io/crates/cargo-util-schemas)
//!   ([nightly docs](https://doc.rust-lang.org/nightly/nightly-rustc/cargo_util_schemas)):
//!   This contains the serde schemas for cargo
//! - [`crates-io`](https://crates.io/crates/crates-io)
//!   ([nightly docs](https://doc.rust-lang.org/nightly/nightly-rustc/crates_io)):
//!   This contains code for accessing the crates.io API.
//! - [`home`](https://crates.io/crates/home):
//!   This library is shared between cargo and rustup and is used for finding their home directories.
//!   This is not directly depended upon with a `path` dependency; cargo uses the version from crates.io.
//!   It is intended to be versioned and published independently of Rust's release system.
//!   Whenever a change needs to be made, bump the version in Cargo.toml and `cargo publish` it manually, and then update cargo's `Cargo.toml` to depend on the new version.
//! - [`rustfix`](https://crates.io/crates/rustfix)
//!   ([nightly docs](https://doc.rust-lang.org/nightly/nightly-rustc/rustfix)):
//!   This defines structures that represent fix suggestions from rustc,
//!   as well as generates "fixed" code from suggestions.
//!   Operations in `rustfix` are all in memory and won't write to disks.
//! - [`cargo-test-support`](https://github.com/rust-lang/cargo/tree/master/crates/cargo-test-support)
//!   ([nightly docs](https://doc.rust-lang.org/nightly/nightly-rustc/cargo_test_support/index.html)):
//!   This contains a variety of code to support writing tests
//! - [`cargo-test-macro`](https://github.com/rust-lang/cargo/tree/master/crates/cargo-test-macro)
//!   ([nightly docs](https://doc.rust-lang.org/nightly/nightly-rustc/cargo_test_macro/index.html)):
//!   This is the `#[cargo_test]` proc-macro used by the test suite to define tests.
//! - [`credential`](https://github.com/rust-lang/cargo/tree/master/credential)
//!   This subdirectory contains several packages for implementing the
//!   [credential providers](https://doc.rust-lang.org/nightly/cargo/reference/registry-authentication.html).
//! - [`mdman`](https://github.com/rust-lang/cargo/tree/master/crates/mdman)
//!   ([nightly docs](https://doc.rust-lang.org/nightly/nightly-rustc/mdman/index.html)):
//!   This is a utility for generating cargo's man pages. See [Building the man
//!   pages](https://github.com/rust-lang/cargo/tree/master/doc#building-the-man-pages)
//!   for more information.
//! - [`resolver-tests`](https://github.com/rust-lang/cargo/tree/master/crates/resolver-tests)
//!   This is a dedicated package that defines tests for the [dependency
//!   resolver][resolver].
//!
//! ### File Overview
//!
//! Files that interact with cargo include
//!
//! - Package
//!   - `Cargo.toml`: User-written project manifest, loaded with [`workspace::parser::read_manifest`] and then
//!     translated to [`workspace::manifest::Manifest`] which maybe stored in a [`workspace::Package`].
//!     - This is editable with [`workspace::editor::manifest::LocalManifest`]
//!   - `Cargo.lock`: Generally loaded with [`ops::resolve_ws`] or a variant of it into a [`resolver::Resolve`]
//!     - At the lowest level, [`ops::load_pkg_lockfile`] and [`ops::write_pkg_lockfile`] are used
//!     - See [`resolver::encode`] for versioning of `Cargo.lock`
//!   - `target/`: Used for build artifacts and abstracted with [`compiler::layout`]. `Layout` handles locking the target directory and providing paths to parts inside. There is a separate `Layout` for each build `target`.
//!     - `target/debug/.fingerprint`: Tracker whether nor not a crate needs to be rebuilt.  See [`compiler::fingerprint`]
//! - `$CARGO_HOME/`:
//!   - `registry/`: Package registry cache which is managed in [`sources::registry`].  Be careful
//!     as the lock [`util::GlobalContext::acquire_package_cache_lock`] must be manually acquired.
//!     - `index`/: Fast-to-access crate metadata (no need to download / extract `*.crate` files)
//!     - `cache/*/*.crate`: Local cache of published crates
//!     - `src/*/*`: Extracted from `*.crate` by [`sources::registry::RegistrySource`]
//!   - `git/`: Git source cache.  See [`sources::git`].
//! - `**/.cargo/config.toml`: Environment dependent (env variables, files) configuration.  See
//!   [`context`]
//!
//! ## Contribute to Cargo documentations
//!
//! The Cargo team always continues improving all external and internal documentations.
//! If you spot anything could be better, don't hesitate to discuss with the team on
//! Zulip [`t-cargo` stream], or [submit an issue] right on GitHub.
//! There is also an issue label [`A-documenting-cargo-itself`],
//! which is generally for documenting user-facing [The Cargo Book],
//! but the Cargo team is welcome any form of enhancement for the [Cargo Contributor Guide]
//! and this API documentation as well.
//!
//! [The Cargo Book: External tools]: https://doc.rust-lang.org/stable/cargo/reference/external-tools.html
//! [Cargo Architecture Overview]: https://doc.crates.io/contrib/architecture
//! [`t-cargo` stream]: https://rust-lang.zulipchat.com/#narrow/stream/246057-t-cargo
//! [submit an issue]: https://github.com/rust-lang/cargo/issues/new/choose
//! [`A-documenting-cargo-itself`]: https://github.com/rust-lang/cargo/labels/A-documenting-cargo-itself
//! [The Cargo Book]: https://doc.rust-lang.org/cargo/
//! [Cargo Contributor Guide]: https://doc.crates.io/contrib/

use anyhow::Error;
use cargo_util_terminal::Shell;
use cargo_util_terminal::Verbosity;
use cargo_util_terminal::Verbosity::Verbose;
use tracing::debug;

pub use crate::util::errors::{AlreadyPrintedError, InternalError, VerboseError};
pub use crate::util::{CargoResult, CliError, CliResult, GlobalContext, indented_lines};
pub use crate::version::{CommitInfo, VersionInfo, bind_build_commit, version};

pub const CARGO_ENV: &str = "CARGO";

// Trust: from here to `mod macros` is Trust-authored — frontend identity.
// Upstream has no equivalent because upstream ships one binary under one name.
// This one is installed as `targo` and as a `cargo` compat symlink with
// different authority, and `argv[0]` is caller-controlled, so identity is taken
// from the OS-reported executable and `argv[0]` is only ever allowed to *narrow*
// it. Resolved once into a `OnceLock` so no later code can observe two answers.

/// Shared whole-name executable identity used by the Cargo binary and the
/// library's launch paths. This is public only because `src/bin/cargo` is a
/// separate crate in the same package.
#[doc(hidden)]
pub fn trust_executable_path_matches(path: &std::path::Path, expected: &str) -> bool {
    crate::util::tippy_arg_protocol::executable_path_matches(path, expected)
}

/// Authenticated identity of a direct Cargo/Targo frontend invocation.
///
/// Only Targo needs a protected sibling-tool authority. Plain Cargo retains its
/// upstream behavior for symlink entrypoints and platforms where
/// `current_exe()` is unavailable. Raw `argv[0]` can never promote a process to
/// Targo; the OS-reported regular `targo` executable is the positive authority.
/// Once that authority exists, a `cargo` spelling is admitted only when its
/// resolved path names the same loaded file (the intentionally shipped
/// compatibility alias); it enters Cargo semantics without receiving any
/// protected Targo path. Every other conflicting spelling fails closed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FrontendBrand {
    Cargo,
    Targo,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AuthenticatedFrontendInvocation {
    brand: FrontendBrand,
    /// The OS-reported regular Targo path whose directory alone owns protected
    /// Trust sibling tools.
    protected_targo_path: Option<std::path::PathBuf>,
    /// A resolved `cargo` argv alias proven to name the same loaded file as an
    /// OS-reported `targo`. This is only recursive Cargo identity; it never
    /// grants Targo branding or protected sibling authority.
    cargo_compat_alias_path: Option<std::path::PathBuf>,
}

static AUTHENTICATED_FRONTEND_INVOCATION: std::sync::OnceLock<
    Result<AuthenticatedFrontendInvocation, String>,
> = std::sync::OnceLock::new();

fn frontend_brand(path: &std::path::Path) -> Option<FrontendBrand> {
    frontend_brand_from_path(path, cfg!(windows))
}

fn frontend_brand_from_path(
    path: &std::path::Path,
    windows_semantics: bool,
) -> Option<FrontendBrand> {
    let matches = |expected| {
        crate::util::tippy_arg_protocol::executable_path_matches_with_windows_semantics(
            path,
            expected,
            windows_semantics,
        )
    };
    if matches("cargo") {
        Some(FrontendBrand::Cargo)
    } else if matches("targo") {
        Some(FrontendBrand::Targo)
    } else {
        None
    }
}

/// Trust (plan T13d): the executable the OS reports, with a symlink resolved ONCE to
/// the file it names, and that file bound to the image that is actually running.
///
/// macOS reports the path the process was executed by (`_NSGetExecutablePath`), so a
/// `targo` reached through a symlink (a `~/.local/bin/targo` link into a toolchain, a
/// link farm, a package manager's shim directory) is reported as the LINK; Linux's
/// `/proc/self/exe` is already the real file. Identity is then taken from the real
/// file and never from the link: its name decides the brand, and its directory is the
/// only one that owns protected sibling tools, so a link placed in a directory full
/// of other tools grants that directory nothing. The real file must be one plain
/// regular file (a link to a directory, a fifo or a device is refused).
///
/// THE BINDING. The link is read after exec, so what it names now need not be what
/// was executed: a link repointed in between would otherwise move the directory that
/// owns the siblings to wherever its writer chose. So the file it resolves to must be
/// the running image itself, by the kernel's answer (`running_image`: `/proc/self/exe`
/// on Linux, `proc_pidpath` of this process on macOS), compared as one file
/// (device and inode). A link that names any other file is refused, and so is every
/// symlinked frontend where the platform cannot name its running image (Windows,
/// where a symlinked `targo.exe` stays refused as it was before T13d). The binding is
/// to the FILE: a second hard link of the running image is the same file, and it
/// grants its directory exactly what running that hard link directly would.
fn resolve_reported_executable(
    reported: std::path::PathBuf,
    running_image: &dyn Fn() -> Result<std::path::PathBuf, String>,
) -> Result<std::path::PathBuf, String> {
    let metadata = match std::fs::symlink_metadata(&reported) {
        Ok(metadata) => metadata,
        // Not inspectable as named: the brand rules below decide what that costs.
        Err(_) => return Ok(reported),
    };
    if !metadata.file_type().is_symlink() {
        return Ok(reported);
    }
    let real = std::fs::canonicalize(&reported).map_err(|error| {
        format!(
            "OS-reported executable `{}` is a symlink that does not resolve: {error}",
            reported.display()
        )
    })?;
    let real_metadata = std::fs::symlink_metadata(&real).map_err(|error| {
        format!(
            "could not inspect `{}`, the file OS-reported executable `{}` resolves to: {error}",
            real.display(),
            reported.display()
        )
    })?;
    if !util::file_identity::metadata_is_plain_file(&real_metadata) {
        return Err(format!(
            "OS-reported executable `{}` is a symlink to `{}`, which is not a plain regular file; a frontend link must resolve to one regular executable",
            reported.display(),
            real.display()
        ));
    }
    let image = running_image().map_err(|error| {
        format!(
            "OS-reported executable `{}` is a symlink to `{}`, and the running executable image cannot be identified to bind it to ({error}); a symlinked frontend is admitted only where the file it resolves to is proved to be the one running",
            reported.display(),
            real.display()
        )
    })?;
    if !util::file_identity::paths_refer_to_same_file(&real, &image).unwrap_or(false) {
        return Err(format!(
            "OS-reported executable `{}` resolves to `{}`, which is not the running executable image (`{}`): the link names a file other than the one that was executed",
            reported.display(),
            real.display(),
            image.display()
        ));
    }
    Ok(real)
}

/// Trust (T13d): the kernel's path for this process's running image, the binding
/// `resolve_reported_executable` checks a resolved symlink against.
fn running_executable_image() -> Result<std::path::PathBuf, String> {
    util::file_identity::running_executable_image().map_err(|error| error.to_string())
}

fn classify_frontend_invocation_paths(
    argv0: &std::path::Path,
    current_exe: Option<std::path::PathBuf>,
    resolved_argv0: Option<std::path::PathBuf>,
    running_image: &dyn Fn() -> Result<std::path::PathBuf, String>,
) -> Result<AuthenticatedFrontendInvocation, String> {
    let argv_brand = frontend_brand(argv0);
    // Trust (T13d): a symlinked executable is resolved once, bound to the running
    // image, and the real file is what is authenticated. A link that cannot be
    // resolved and bound is fatal where Targo authority is asked for (the argv or the
    // link says `targo`); any other invocation is treated as one whose executable is
    // unknown, which grants no Targo authority and keeps upstream Cargo's tolerance.
    //
    // So a SYMLINK is classified by the file it resolves to on every platform, which
    // is what Linux's `/proc/self/exe` always reported: a link named `frontend` (or
    // `cargo`) to `targo`, run under an argv[0] that is not a Cargo spelling, runs
    // Targo, anchored at the real file's directory. A HARD link has no other name to
    // resolve to: it is classified by the name it was run under, on every platform,
    // so a hard link named `frontend` runs with no Targo authority. The two differ on
    // purpose; neither grants authority anywhere but the real file's directory.
    let reported_exe = current_exe;
    let current_exe = match reported_exe
        .clone()
        .map(|reported| resolve_reported_executable(reported, running_image))
    {
        None => None,
        Some(Ok(real)) => Some(real),
        Some(Err(error)) => {
            if argv_brand == Some(FrontendBrand::Targo)
                || reported_exe.as_deref().and_then(frontend_brand) == Some(FrontendBrand::Targo)
            {
                return Err(error);
            }
            None
        }
    };
    let current_brand = current_exe.as_deref().and_then(frontend_brand);
    let resolved_from = reported_exe
        .as_deref()
        .zip(current_exe.as_deref())
        .filter(|(reported, real)| reported != real)
        .map(|(reported, _)| reported);

    match current_brand {
        Some(FrontendBrand::Targo) => {
            let current_exe = current_exe.expect("recognized current executable has a path");
            let metadata = std::fs::symlink_metadata(&current_exe).map_err(|error| {
                format!(
                    "could not inspect OS-reported Targo executable `{}`: {error}",
                    current_exe.display()
                )
            })?;
            if !util::file_identity::metadata_is_plain_file(&metadata) {
                return Err(format!(
                    "OS-reported Targo executable `{}` is not a plain regular file; a Targo frontend must be one regular file (a symlink to one is resolved; a reparse point is refused)",
                    current_exe.display()
                ));
            }
            // A `cargo` name of the real `targo` keeps Cargo semantics only when argv[0]
            // resolves (through PATH when it is bare) to this same file. Since T13d a
            // `cargo` SYMLINK to targo (`scripts/rustup-link-trust.sh --repair-aliases`
            // lays one) reaches this branch on macOS as it always did on Linux: rustup's
            // proxy execs it with its full path as argv[0] (measured 2026-10-11), which
            // resolves; a bare `cargo` whose PATH lookup finds another cargo is refused.
            if argv_brand == Some(FrontendBrand::Cargo) {
                let resolved_argv0 = resolved_argv0.filter(|path| path.is_absolute()).ok_or_else(
                    || {
                        format!(
                            "Cargo argv[0] `{}` could not be resolved to an absolute compatibility alias",
                            argv0.display()
                        )
                    },
                )?;
                if !util::file_identity::paths_refer_to_same_file(&resolved_argv0, &current_exe)
                    .unwrap_or(false)
                {
                    return Err(format!(
                        "Cargo argv[0] `{}` does not resolve to the loaded Targo executable",
                        argv0.display()
                    ));
                }
                return Ok(AuthenticatedFrontendInvocation {
                    brand: FrontendBrand::Cargo,
                    protected_targo_path: None,
                    cargo_compat_alias_path: Some(resolved_argv0),
                });
            }
            Ok(AuthenticatedFrontendInvocation {
                brand: FrontendBrand::Targo,
                protected_targo_path: Some(current_exe),
                cargo_compat_alias_path: None,
            })
        }
        // Cargo is the compatibility/default domain, but a recognized `targo`
        // spelling must never silently demote to Cargo semantics: that would
        // dispatch `cargo-trust` from PATH/CARGO_HOME instead of the protected
        // sibling `targo-trust`. Ordinary Cargo spellings and unrecognized
        // argv aliases retain upstream compatibility.
        Some(FrontendBrand::Cargo) => {
            if argv_brand == Some(FrontendBrand::Targo) {
                return Err(format!(
                    "Targo argv[0] `{}` resolves to a Cargo executable, not the authenticated Targo frontend",
                    argv0.display()
                ));
            }
            if let Some(link) =
                resolved_from.filter(|link| frontend_brand(link) == Some(FrontendBrand::Targo))
            {
                return Err(format!(
                    "the running executable `{}` is a symlink to `{}`, which is a Cargo executable, not the authenticated Targo frontend; Targo is authenticated by the file a link resolves to, never by the link's name",
                    link.display(),
                    current_exe.as_deref().unwrap_or(link).display()
                ));
            }
            Ok(AuthenticatedFrontendInvocation {
                brand: FrontendBrand::Cargo,
                protected_targo_path: None,
                cargo_compat_alias_path: None,
            })
        }
        Some(FrontendBrand::Other) | None => {
            if argv_brand == Some(FrontendBrand::Targo)
                || resolved_from.and_then(frontend_brand) == Some(FrontendBrand::Targo)
            {
                if let (Some(link), Some(real)) = (resolved_from, current_exe.as_deref()) {
                    return Err(format!(
                        "the running executable `{}` is a symlink to `{}`, which is not a `targo` executable; Targo is authenticated by the file a link resolves to, never by the link's name",
                        link.display(),
                        real.display()
                    ));
                }
                return Err(format!(
                    "could not authenticate Targo argv[0] `{}` against the running executable",
                    argv0.display()
                ));
            }
            Ok(AuthenticatedFrontendInvocation {
                brand: argv_brand.unwrap_or(FrontendBrand::Other),
                protected_targo_path: None,
                cargo_compat_alias_path: None,
            })
        }
    }
}

fn detect_frontend_invocation() -> Result<AuthenticatedFrontendInvocation, String> {
    let argv0 = std::env::args_os()
        .next()
        .map(std::path::PathBuf::from)
        // POSIX permits an empty argv vector. Branding still has the
        // OS-reported executable as authority, and plain Cargo must not grow a
        // startup failure for this upstream-compatible edge case.
        .unwrap_or_default();
    let current_exe = std::env::current_exe().ok();
    let resolved_argv0 = cargo_util::paths::resolve_executable(&argv0)
        .ok()
        .and_then(|path| {
            if path.is_absolute() {
                Some(path)
            } else {
                std::env::current_dir().ok().map(|cwd| cwd.join(path))
            }
        });
    classify_frontend_invocation_paths(
        &argv0,
        current_exe,
        resolved_argv0,
        &running_executable_image,
    )
}

fn authenticated_frontend_invocation()
-> Result<&'static AuthenticatedFrontendInvocation, &'static str> {
    match AUTHENTICATED_FRONTEND_INVOCATION.get_or_init(detect_frontend_invocation) {
        Ok(invocation) => Ok(invocation),
        Err(error) => Err(error.as_str()),
    }
}

/// Validate direct frontend identity before configuration or command dispatch.
pub fn validate_frontend_invocation() -> Result<(), String> {
    authenticated_frontend_invocation()
        .map(|_| ())
        .map_err(str::to_string)
}

/// Exact OS-reported Targo path that owns protected Trust sibling tools.
pub fn authenticated_targo_path() -> Result<Option<&'static std::path::Path>, String> {
    authenticated_frontend_invocation()
        .map(|invocation| invocation.protected_targo_path.as_deref())
        .map_err(str::to_string)
}

/// Exact resolved Cargo compatibility alias proven to be the loaded Targo
/// artifact. This path is only for recursive Cargo identity.
pub fn authenticated_cargo_compat_alias_path() -> Result<Option<&'static std::path::Path>, String> {
    authenticated_frontend_invocation()
        .map(|invocation| invocation.cargo_compat_alias_path.as_deref())
        .map_err(str::to_string)
}

/// Whether the running, authenticated frontend is Trust's `targo` entrypoint.
pub fn is_targo_invocation() -> bool {
    authenticated_frontend_invocation()
        .unwrap_or_else(|error| panic!("unauthenticated Cargo/Targo frontend invocation: {error}"))
        .brand
        == FrontendBrand::Targo
}

/// Whether this process is in ordinary Cargo's compatibility domain.
pub fn is_cargo_invocation() -> bool {
    authenticated_frontend_invocation()
        .unwrap_or_else(|error| panic!("unauthenticated Cargo/Targo frontend invocation: {error}"))
        .brand
        == FrontendBrand::Cargo
}

#[macro_use]
mod macros;

pub mod compiler;
// Trust: report the internal read-set codec used by both frontends.
pub use compiler::fingerprint::encoded_dep_info_version;
pub mod context;
pub mod diagnostics;
// Trust: separate finite metadata service under original native custody.
#[cfg(unix)]
pub mod metadata_service;
pub mod native_job_service;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod native_query_profile;
#[cfg(unix)]
pub mod offline_preparation;
pub mod ops;
pub mod paired_service;
pub mod resolver;
#[cfg(unix)]
pub mod resolver_service;
mod resource_platform;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_v3;
pub mod sources;
pub mod util;
mod version;
#[cfg(unix)]
pub mod workload_service;
pub mod workspace;

/// Trust: when set by an explicitly authorized unverified or internal bootstrap
/// lane, native build/lint passes append `-Ztrust-verify=off` to the resolved
/// rustc flags so they skip the direct TrustIR proof pipeline. Branded Targo
/// refuses to set this state implicitly. The verified
/// workflow (`targo trust …`) sets `TRUST_TARGO_VERIFY=1` alongside a
/// proof-session nonce and tracked verifier policy. The frontend
/// (`src/bin/cargo`) decides per subcommand; the flag is appended in `extra_args`
/// (build_context), so it preserves config rustflags and is TRACKED in the
/// fingerprint (verified and unverified artifacts never alias). Rustdoc is the
/// one exception: trustdoc's embedded frontend refuses every other `-Ztrust-*`,
/// so this lane drops the config/env ones from rustdoc's flags
/// (`unverified_lane_rustdoc_flags`). The marker alone
/// never enables compiler verification; the compiler is batteries-on unless
/// explicitly disabled.
static TRUST_NO_VERIFY_FAST: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Trust: true only inside a verifier invocation accepted by the branded
/// `targo` frontend. This is deliberately process-local rather than an
/// environment variable: an ambient verifier marker must not change ordinary
/// Cargo's host-artifact rustflag isolation, and a child process must not
/// inherit an authority its parent was granted.
static TRUST_VERIFIED_TARGO: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

// Trust: set only by the mandatory native-epoch CLI handshake, never by env.
static RESOURCE_WORKER_V2: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Select the native worker protocol after parsing its mandatory CLI flag.
pub fn set_resource_worker_v2(enabled: bool) -> CargoResult<()> {
    if enabled && !resource_platform::native_worker_host(std::env::consts::OS) {
        anyhow::bail!("native CPU worker protocol is unsupported on this host");
    }
    RESOURCE_WORKER_V2.store(enabled, std::sync::atomic::Ordering::Relaxed);
    Ok(())
}

/// Whether this invocation selected the native worker protocol.
pub fn resource_worker_v2() -> bool {
    RESOURCE_WORKER_V2.load(std::sync::atomic::Ordering::Relaxed)
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use trust_resource_controller::client::sdk::{capture_sdk_lease, snapshot_sdk_lease};

static RESOURCE_WORKER_V3: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Mandatory paired protocol markers select a route; environment is no grant.
pub fn set_resource_worker_v3(worker: bool, subgroups: bool) -> CargoResult<()> {
    if worker != subgroups {
        anyhow::bail!("native v3 requires both worker and subgroup protocol markers");
    }
    if worker
        && (resource_worker_v2() || !resource_platform::native_worker_host(std::env::consts::OS))
    {
        anyhow::bail!("native v3 cannot mix epoch protocols or use this unsupported host");
    }
    RESOURCE_WORKER_V3.store(worker, std::sync::atomic::Ordering::Relaxed);
    Ok(())
}
/// Whether the current invocation selected the host-owned native protocol.
pub fn resource_worker_v3() -> bool {
    RESOURCE_WORKER_V3.load(std::sync::atomic::Ordering::Relaxed)
}

/// Validate live context and its actual shared domain before CPU admission.
/// The unadvertised staging route refuses before project/config work until
/// its host-owned child executor is installed; no local execution fallback.
pub fn initialize_resource_worker_v3(gctx: &util::GlobalContext, command: &str) -> CargoResult<()> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    resource_v3::initialize(gctx, command)?;
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    let _ = (gctx, command);
    if resource_worker_v3() {
        anyhow::bail!(
            "native v3 child execution adapter is not yet qualified; no build work dispatched"
        );
    }
    Ok(())
}

/// Enable/disable the explicit native unverified path (skip the proof pipeline). See
/// [`TRUST_NO_VERIFY_FAST`].
pub fn set_trust_no_verify_fast(enabled: bool) {
    TRUST_NO_VERIFY_FAST.store(enabled, std::sync::atomic::Ordering::Relaxed);
}

/// Whether the native fast-lint path is active (verifier skipped).
pub fn trust_no_verify_fast() -> bool {
    TRUST_NO_VERIFY_FAST.load(std::sync::atomic::Ordering::Relaxed)
}

/// Mark this frontend process as the internal verified-Targo lane.
pub fn set_trust_verified_targo(enabled: bool) {
    TRUST_VERIFIED_TARGO.store(enabled, std::sync::atomic::Ordering::Relaxed);
}

/// Whether the branded frontend accepted the internal verifier marker.
pub fn trust_verified_targo() -> bool {
    TRUST_VERIFIED_TARGO.load(std::sync::atomic::Ordering::Relaxed)
}

/// Trust: validate the dynamic-loader environment that existed when verified
/// Targo entered this process. This is necessarily an early fail-closed check:
/// child environment scrubbing cannot retroactively authenticate Targo's own
/// startup, because by then the untrusted library is already mapped in.
pub fn validate_verified_targo_startup_loader_environment() -> Result<(), String> {
    let frontend = authenticated_targo_path()?
        .ok_or_else(|| "verified Targo has no authenticated frontend path".to_owned())?;
    util::process_authority::validate_verified_targo_startup_loader_environment(frontend)
        .map_err(|error| error.to_string())
}

/// Trust: authenticate explicit-unverified authority inherited from a live
/// Targo ancestor before Cargo configuration is constructed.
#[doc(hidden)]
pub fn prepare_nested_unverified_targo_handoff() -> Result<(), String> {
    util::process_authority::prepare_nested_unverified_targo_handoff()
        .map_err(|error| error.to_string())
}

/// Whether this Targo process inherited live explicit-unverified authority.
#[doc(hidden)]
pub fn nested_unverified_targo_handoff_active() -> bool {
    util::process_authority::nested_unverified_targo_handoff_active()
}

/// Trust (T14c): why an inherited nested-unverified endpoint granted nothing,
/// when one was inherited and startup did not authenticate it.
#[doc(hidden)]
pub fn withheld_nested_unverified_targo_authority() -> Option<&'static str> {
    util::process_authority::withheld_nested_unverified_targo_authority()
}

/// Trust (T14c): keep an inherited endpoint that did not authenticate from a
/// child this process starts itself (an external subcommand).
#[doc(hidden)]
pub fn withhold_unauthenticated_nested_unverified_endpoint(
    command: &mut cargo_util::ProcessBuilder,
) {
    util::process_authority::withhold_unauthenticated_nested_unverified_endpoint(command)
}

/// Trust: start nested authority only for the exact explicit CLI lane.
#[doc(hidden)]
pub fn start_explicit_unverified_targo_broker() -> Result<(), String> {
    util::process_authority::start_explicit_unverified_targo_broker()
        .map_err(|error| error.to_string())
}

pub fn exit_with_error(err: CliError, shell: &mut Shell) -> ! {
    std::process::exit(report_cli_error(err, shell))
}

/// Report the canonical CLI error before an owner performs final cleanup.
/// Returning a code does not create a process status; the CLI must still exit.
pub fn report_cli_error(err: CliError, shell: &mut Shell) -> i32 {
    debug!("exit_with_error; err={:?}", err);

    if let Some(ref err) = err.error {
        if let Some(clap_err) = err.downcast_ref::<clap::Error>() {
            let exit_code = if clap_err.use_stderr() { 1 } else { 0 };
            let _ = clap_err.print();
            return exit_code;
        }
    }

    let CliError { error, exit_code } = err;
    if let Some(error) = error {
        display_error(&error, shell);
    }

    exit_code
}

/// Displays an error, and all its causes, to stderr.
pub fn display_error(err: &Error, shell: &mut Shell) {
    debug!("display_error; err={:?}", err);
    _display_error(err, shell, true);
    if err
        .chain()
        .any(|e| e.downcast_ref::<InternalError>().is_some())
    {
        drop(shell.note("this is an unexpected cargo internal error"));
        drop(
            shell.note(
                "we would appreciate a bug report: https://github.com/rust-lang/cargo/issues/",
            ),
        );
        drop(shell.note(format!("cargo {}", version())));
        // Once backtraces are stabilized, this should print out a backtrace
        // if it is available.
    }
}

/// Displays a warning, with an error object providing detailed information
/// and context.
pub fn display_warning_with_error(warning: &str, err: &Error, shell: &mut Shell) {
    drop(shell.warn(warning));
    drop(writeln!(shell.err()));
    _display_error(err, shell, false);
}

fn error_chain(err: &Error, verbosity: Verbosity) -> impl Iterator<Item = &dyn std::fmt::Display> {
    err.chain()
        .take_while(move |err| {
            // If we're not in verbose mode then only print cause chain until one
            // marked as `VerboseError` appears.
            //
            // Generally the top error shouldn't be verbose, but check it anyways.
            verbosity == Verbose || !err.is::<VerboseError>()
        })
        .take_while(|err| !err.is::<AlreadyPrintedError>())
        .map(|err| err as &dyn std::fmt::Display)
}

fn _display_error(err: &Error, shell: &mut Shell, as_err: bool) {
    for (i, err) in error_chain(err, shell.verbosity()).enumerate() {
        if i == 0 {
            if as_err {
                drop(shell.error(&err));
            } else {
                drop(writeln!(shell.err(), "{}", err));
            }
        } else {
            drop(writeln!(shell.err(), "\nCaused by:"));
            drop(write!(shell.err(), "{}", indented_lines(&err.to_string())));
        }
    }
}

// Trust: pins the frontend-identity classifier against the spellings that would
// otherwise promote a process — a renamed executable, a case-variant name on
// Windows, and a symlink placed to impersonate `targo`.
#[cfg(test)]
mod trust_frontend_identity_tests {
    use super::{
        AuthenticatedFrontendInvocation, FrontendBrand, classify_frontend_invocation_paths,
        frontend_brand_from_path,
    };
    use portable_atomic::AtomicU64;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::atomic::Ordering;

    static FIXTURE_SEQUENCE: AtomicU64 = AtomicU64::new(0);

    /// The classifier with no running image to bind a symlink to: a plain file is
    /// never resolved, so these fixtures never ask, and a symlink is refused (fatal
    /// where Targo is claimed, unknown otherwise).
    fn classify(
        argv0: &Path,
        current_exe: Option<PathBuf>,
        resolved_argv0: Option<PathBuf>,
    ) -> Result<AuthenticatedFrontendInvocation, String> {
        classify_frontend_invocation_paths(argv0, current_exe, resolved_argv0, &|| {
            Err("this fixture names no running image".to_string())
        })
    }

    /// The classifier in a process whose running image is the file `image`.
    fn classify_running(
        argv0: &Path,
        current_exe: Option<PathBuf>,
        resolved_argv0: Option<PathBuf>,
        image: &Path,
    ) -> Result<AuthenticatedFrontendInvocation, String> {
        let image = image.to_path_buf();
        classify_frontend_invocation_paths(argv0, current_exe, resolved_argv0, &move || {
            Ok(image.clone())
        })
    }

    #[test]
    fn frontend_names_require_complete_platform_valid_names() {
        assert_eq!(
            frontend_brand_from_path(Path::new("TARGO.EXE"), true),
            Some(FrontendBrand::Targo)
        );
        assert_eq!(
            frontend_brand_from_path(Path::new("CaRgO.ExE"), true),
            Some(FrontendBrand::Cargo)
        );
        assert_eq!(frontend_brand_from_path(Path::new("TARGO"), false), None);
        assert_eq!(
            frontend_brand_from_path(Path::new("targo.backup"), false),
            None
        );
        assert_eq!(frontend_brand_from_path(Path::new("targo.com"), true), None);
        assert!(
            classify(
                Path::new("targo"),
                Some(Path::new("/toolchain/bin/targo.backup").to_path_buf()),
                None,
            )
            .is_err(),
            "a suffix-renamed executable must not authenticate a Targo argv spelling"
        );
    }

    fn fixture_root() -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "targo-frontend-identity-{}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos(),
            FIXTURE_SEQUENCE.fetch_add(1, Ordering::Relaxed),
        ))
    }

    #[test]
    fn same_file_cargo_alias_is_compatibility_only_and_forged_argv_cannot_change_brand() {
        let root = fixture_root();
        fs::create_dir_all(&root).expect("create identity fixture");
        let targo = root.join("targo");
        let cargo = root.join("cargo");
        fs::write(&targo, b"shared frontend").expect("write frontend fixture");
        fs::hard_link(&targo, &cargo).expect("create Cargo compatibility hardlink");

        let compatibility = classify(&cargo, Some(targo.clone()), Some(cargo.clone()))
            .expect("a resolved same-file cargo alias must retain Cargo semantics");
        assert_eq!(compatibility.brand, FrontendBrand::Cargo);
        assert_eq!(compatibility.protected_targo_path, None);
        assert_eq!(
            compatibility.cargo_compat_alias_path.as_deref(),
            Some(cargo.as_path())
        );

        assert!(
            classify(Path::new("cargo"), Some(targo.clone()), None,).is_err(),
            "an unresolved forged Cargo argv0 must not demote Targo"
        );
        assert!(
            classify(Path::new("targo"), Some(cargo.clone()), Some(targo.clone()),).is_err(),
            "a Targo spelling resolving to Cargo must fail instead of dispatching ambient cargo-trust"
        );

        let direct = classify(&targo, Some(targo.clone()), Some(targo.clone()))
            .expect("matching loaded Targo path is authenticated");
        assert_eq!(direct.brand, FrontendBrand::Targo);
        assert_eq!(
            direct.protected_targo_path.as_deref(),
            Some(targo.as_path())
        );
        assert_eq!(direct.cargo_compat_alias_path, None);

        let argvless_targo = classify(Path::new(""), Some(targo.clone()), None)
            .expect("OS-reported Targo remains authoritative with an empty argv");
        assert_eq!(argvless_targo.brand, FrontendBrand::Targo);
        let argvless_cargo = classify(Path::new(""), Some(cargo.clone()), None)
            .expect("plain Cargo accepts an empty argv like upstream");
        assert_eq!(argvless_cargo.brand, FrontendBrand::Cargo);

        let attacker_dir = root.join("attacker");
        fs::create_dir_all(&attacker_dir).expect("create attacker directory");
        let relocated = attacker_dir.join("targo");
        fs::hard_link(&targo, &relocated).expect("create relocated same-inode frontend");
        let classified = classify(&relocated, Some(targo.clone()), Some(relocated.clone()))
            .expect("running frontend path remains available");
        assert_eq!(classified.brand, FrontendBrand::Targo);
        assert_eq!(
            classified.protected_targo_path.as_deref(),
            Some(targo.as_path())
        );

        let stock = root.join("stock-tool");
        fs::write(&stock, b"unrelated executable").expect("write unrelated executable");
        assert!(
            classify(Path::new("targo"), Some(stock), None).is_err(),
            "an unrelated executable cannot become Targo from argv spelling alone"
        );

        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn plain_cargo_keeps_symlink_and_missing_current_exe_compatibility() {
        let root = fixture_root();
        fs::create_dir_all(&root).expect("create Cargo compatibility fixture");
        let implementation = root.join("cargo-implementation");
        let cargo = root.join("cargo");
        fs::write(&implementation, b"plain cargo frontend").expect("write Cargo fixture");
        std::os::unix::fs::symlink(&implementation, &cargo).expect("create ordinary Cargo symlink");

        let symlinked = classify(&cargo, Some(cargo.clone()), Some(cargo.clone()))
            .expect("ordinary Cargo symlink invocation must remain supported");
        assert_eq!(symlinked.brand, FrontendBrand::Cargo);
        assert_eq!(symlinked.protected_targo_path, None);
        assert_eq!(symlinked.cargo_compat_alias_path, None);

        let unavailable = classify(Path::new("cargo"), None, Some(cargo.clone()))
            .expect("Cargo must tolerate unavailable current_exe");
        assert_eq!(unavailable.brand, FrontendBrand::Cargo);
        assert_eq!(unavailable.protected_targo_path, None);
        assert_eq!(unavailable.cargo_compat_alias_path, None);

        let unrelated = classify(Path::new("custom-wrapper"), None, None)
            .expect("library consumers must tolerate unrelated argv0");
        assert_eq!(unrelated.brand, FrontendBrand::Other);
        assert_eq!(unrelated.protected_targo_path, None);
        assert_eq!(unrelated.cargo_compat_alias_path, None);
        assert!(
            classify(Path::new("targo"), None, None).is_err(),
            "raw Targo argv0 cannot promote an unauthenticated process"
        );

        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn forged_symlink_argv_cannot_relocate_the_protected_toolchain_root() {
        let root = fixture_root();
        let attacker = root.join("attacker/bin");
        let implementation = root.join("implementation/bin");
        fs::create_dir_all(&attacker).expect("create attacker fixture");
        fs::create_dir_all(&implementation).expect("create implementation fixture");
        let running = implementation.join("cargo");
        fs::write(&running, b"shared frontend").expect("write frontend implementation");
        let forged_targo = attacker.join("targo");
        std::os::unix::fs::symlink(&running, &forged_targo).expect("create forged Targo symlink");

        assert!(
            classify_running(
                &forged_targo,
                Some(running.clone()),
                Some(forged_targo.clone()),
                &running,
            )
            .is_err(),
            "a loaded Cargo executable must reject a forged Targo argv symlink instead of dispatching ambient cargo-trust"
        );
        assert!(
            classify_running(
                &forged_targo,
                Some(forged_targo.clone()),
                Some(forged_targo.clone()),
                &running,
            )
            .is_err(),
            "a platform that preserves the attacker symlink in current_exe must still reject it"
        );

        let _ = fs::remove_dir_all(root);
    }

    // T13d: macOS reports a symlinked executable by the link's path. A `targo` reached
    // through links is authenticated as the real file the links resolve to, when that
    // file is the running image, and only that file's directory owns protected siblings.
    #[cfg(unix)]
    #[test]
    fn a_symlinked_targo_is_resolved_once_and_the_real_file_authenticated() {
        let root = fixture_root();
        let toolchain = root.join("toolchain/bin");
        let links = root.join("links/bin");
        let chained = root.join("chained");
        fs::create_dir_all(&toolchain).expect("create toolchain fixture");
        fs::create_dir_all(&links).expect("create link directory");
        fs::create_dir_all(&chained).expect("create chained link directory");
        let targo = toolchain.join("targo");
        fs::write(&targo, b"the real frontend").expect("write frontend fixture");
        // Decoys beside the link: the link's directory must gain no authority.
        fs::write(links.join("trustc"), b"a decoy compiler").expect("write decoy");
        fs::write(links.join("targo-trust"), b"a decoy targo-trust").expect("write decoy");
        let real = fs::canonicalize(&targo).expect("canonical frontend");

        let link = links.join("targo");
        std::os::unix::fs::symlink(&targo, &link).expect("link targo");
        let relative = links.join("targo-relative");
        std::os::unix::fs::symlink("../../toolchain/bin/targo", &relative).expect("relative link");
        let chain = chained.join("targo");
        std::os::unix::fs::symlink(&link, &chain).expect("link to the link");
        let renamed = links.join("frontend");
        std::os::unix::fs::symlink(&targo, &renamed).expect("link under another name");

        for (argv0, reported) in [
            (Path::new("targo"), &link),
            (link.as_path(), &link),
            (Path::new("targo-relative"), &relative),
            (Path::new("targo"), &chain),
            // A symlink is classified by the file it resolves to, as Linux's
            // /proc/self/exe always reported it: a link named `frontend` to `targo`
            // runs Targo. (A HARD link named `frontend` is classified by its own name
            // and runs with no Targo authority; see `classify_frontend_invocation_paths`.)
            (Path::new("frontend"), &renamed),
        ] {
            let classified = classify_running(argv0, Some(reported.clone()), None, &targo)
                .unwrap_or_else(|error| {
                    panic!("{} must authenticate: {error}", reported.display())
                });
            assert_eq!(
                classified.brand,
                FrontendBrand::Targo,
                "{}",
                reported.display()
            );
            assert_eq!(
                classified.protected_targo_path.as_deref(),
                Some(real.as_path()),
                "{} must authenticate the real file, not the link",
                reported.display()
            );
            assert_eq!(classified.cargo_compat_alias_path, None);
        }

        // A hard link named `frontend` is a name of its own: no Targo authority.
        let hard = links.join("hard-frontend");
        fs::hard_link(&targo, &hard).expect("hard link under another name");
        let classified =
            classify_running(Path::new("hard-frontend"), Some(hard.clone()), None, &targo)
                .expect("an unrelated plain name is tolerated");
        assert_eq!(classified.brand, FrontendBrand::Other);
        assert_eq!(classified.protected_targo_path, None);

        let _ = fs::remove_dir_all(root);
    }

    // T13d: a `cargo` symlink to targo (rustup-link-trust.sh --repair-aliases lays one)
    // is classified by the real file, as on Linux: Cargo semantics only when argv[0]
    // resolves to that same file, Targo under any other argv[0].
    #[cfg(unix)]
    #[test]
    fn a_cargo_symlink_to_targo_is_classified_as_on_linux() {
        let root = fixture_root();
        let toolchain = root.join("toolchain/bin");
        let elsewhere = root.join("elsewhere/bin");
        fs::create_dir_all(&toolchain).expect("create toolchain fixture");
        fs::create_dir_all(&elsewhere).expect("create other PATH entry");
        let targo = toolchain.join("targo");
        fs::write(&targo, b"the real frontend").expect("write frontend fixture");
        let real = fs::canonicalize(&targo).expect("canonical frontend");
        let cargo = toolchain.join("cargo");
        std::os::unix::fs::symlink("targo", &cargo).expect("cargo alias link");

        // rustup's proxy execs the toolchain path itself: argv[0] resolves to targo.
        let compatibility =
            classify_running(&cargo, Some(cargo.clone()), Some(cargo.clone()), &targo)
                .expect("a cargo link to targo run by its path keeps Cargo semantics");
        assert_eq!(compatibility.brand, FrontendBrand::Cargo);
        assert_eq!(compatibility.protected_targo_path, None);
        assert_eq!(
            compatibility.cargo_compat_alias_path.as_deref(),
            Some(cargo.as_path())
        );

        // A bare `cargo` whose PATH lookup finds a different cargo is refused: the
        // compatibility alias must be the file that is running.
        let other_cargo = elsewhere.join("cargo");
        fs::write(&other_cargo, b"some other cargo").expect("write other cargo");
        let error = classify_running(
            Path::new("cargo"),
            Some(cargo.clone()),
            Some(other_cargo),
            &targo,
        )
        .expect_err("a bare cargo resolving elsewhere must be refused");
        assert!(
            error.contains("does not resolve to the loaded Targo executable"),
            "{error}"
        );

        // Under an argv[0] that is not a Cargo spelling it runs Targo, at the real file.
        let classified = classify_running(Path::new("frontend"), Some(cargo.clone()), None, &targo)
            .expect("a cargo link run under another name runs the real targo");
        assert_eq!(classified.brand, FrontendBrand::Targo);
        assert_eq!(
            classified.protected_targo_path.as_deref(),
            Some(real.as_path())
        );

        let _ = fs::remove_dir_all(root);
    }

    // T13d: the file a link resolves to must be the running image. A link repointed
    // between exec and the resolution names another file, and is refused, so its writer
    // cannot move the directory that owns the protected siblings.
    #[cfg(unix)]
    #[test]
    fn a_symlinked_targo_must_resolve_to_the_running_image() {
        let root = fixture_root();
        let executed = root.join("executed/bin");
        let repointed = root.join("repointed/bin");
        let links = root.join("links");
        fs::create_dir_all(&executed).expect("create executed toolchain");
        fs::create_dir_all(&repointed).expect("create repointed toolchain");
        fs::create_dir_all(&links).expect("create link directory");
        // Two files with the same bytes and the same name: only the inode tells them apart.
        let running = executed.join("targo");
        fs::write(&running, b"the frontend").expect("write running frontend");
        let other = repointed.join("targo");
        fs::write(&other, b"the frontend").expect("write repointed frontend");
        let link = links.join("targo");
        std::os::unix::fs::symlink(&other, &link).expect("link repointed after exec");

        for argv0 in [Path::new("targo"), link.as_path(), Path::new("")] {
            let error = classify_running(argv0, Some(link.clone()), None, &running)
                .expect_err("a link naming a file other than the running image must be refused");
            assert!(
                error.contains("which is not the running executable image"),
                "{}: {error}",
                argv0.display()
            );
        }

        // The same link, run where the image is the file it names, authenticates it.
        let bound = classify_running(Path::new("targo"), Some(link.clone()), None, &other)
            .expect("a link naming the running image authenticates");
        assert_eq!(
            bound.protected_targo_path.as_deref(),
            Some(fs::canonicalize(&other).expect("canonical").as_path())
        );

        // Where the platform cannot name its running image, a symlinked frontend is
        // refused rather than trusted on the link's word.
        let error = classify(Path::new("targo"), Some(link.clone()), None)
            .expect_err("an unbindable symlinked targo must be refused");
        assert!(
            error.contains("the running executable image cannot be identified"),
            "{error}"
        );

        // A Cargo invocation keeps upstream's tolerance: an unbound link is an
        // unknown executable, with no Targo authority.
        let cargo = links.join("cargo");
        std::os::unix::fs::symlink(&other, &cargo).expect("cargo link");
        let tolerated = classify_running(Path::new("cargo"), Some(cargo), None, &running)
            .expect("plain Cargo tolerates a link it cannot bind");
        assert_eq!(tolerated.brand, FrontendBrand::Cargo);
        assert_eq!(tolerated.protected_targo_path, None);
        assert_eq!(tolerated.cargo_compat_alias_path, None);

        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn a_symlinked_targo_to_a_non_regular_or_unauthorised_target_is_refused() {
        let root = fixture_root();
        let bin = root.join("bin");
        let elsewhere = root.join("elsewhere");
        fs::create_dir_all(&bin).expect("create link directory");
        fs::create_dir_all(&elsewhere).expect("create target directory");

        // The running image is the link's own target, so every refusal below is the
        // target's kind or name, never the binding.
        let refusal = |name: &str, target: &Path, argv0: &str| -> String {
            let link = bin.join(name);
            let _ = fs::remove_file(&link);
            std::os::unix::fs::symlink(target, &link).expect("create link");
            classify_running(Path::new(argv0), Some(link.clone()), None, target)
                .expect_err(&format!("{name} -> {} must be refused", target.display()))
        };

        // Non-regular targets.
        let directory = elsewhere.join("targo");
        fs::create_dir_all(&directory).expect("create directory target");
        let error = refusal("targo", &directory, "targo");
        assert!(error.contains("is not a plain regular file"), "{error}");
        let fifo = elsewhere.join("fifo");
        let fifo_name = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes())
            .expect("fixture path has no NUL");
        assert_eq!(
            unsafe { libc::mkfifo(fifo_name.as_ptr(), 0o600) },
            0,
            "mkfifo"
        );
        let error = refusal("targo", &fifo, "targo");
        assert!(error.contains("is not a plain regular file"), "{error}");
        let error = refusal("targo", &elsewhere.join("missing"), "targo");
        assert!(error.contains("does not resolve"), "{error}");

        // Unauthorised targets: a regular file that is not a `targo` executable
        // gains nothing from a link named `targo`, whatever argv[0] says.
        let stranger = elsewhere.join("stock-tool");
        fs::write(&stranger, b"an unrelated executable").expect("write stranger");
        for argv0 in ["targo", "stock-tool", ""] {
            let error = refusal("targo", &stranger, argv0);
            assert!(
                error.contains("never by the link's name"),
                "{argv0}: {error}"
            );
        }
        let cargo = elsewhere.join("cargo");
        fs::write(&cargo, b"a cargo executable").expect("write cargo");
        let error = refusal("targo", &cargo, "targo");
        assert!(error.contains("resolves to a Cargo executable"), "{error}");
        let error = refusal("targo", &cargo, "cargo");
        assert!(error.contains("never by the link's name"), "{error}");

        // Plain Cargo keeps upstream's tolerance of an executable it cannot read:
        // a dangling `cargo` link is an unknown executable, with no Targo authority.
        let link = bin.join("cargo");
        std::os::unix::fs::symlink(elsewhere.join("gone"), &link).expect("dangling cargo link");
        let tolerated = classify(Path::new("cargo"), Some(link), None)
            .expect("plain Cargo tolerates an unreadable executable");
        assert_eq!(tolerated.brand, FrontendBrand::Cargo);
        assert_eq!(tolerated.protected_targo_path, None);

        let _ = fs::remove_dir_all(root);
    }
}
