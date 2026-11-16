//! Tracks changes to determine if something needs to be recompiled.
//!
//! This module implements change-tracking so that Cargo can know whether or
//! not something needs to be recompiled. A Cargo [`Unit`] can be either "dirty"
//! (needs to be recompiled) or "fresh" (it does not need to be recompiled).
//!
//! ## Mechanisms affecting freshness
//!
//! There are several mechanisms that influence a Unit's freshness:
//!
//! - The [`Fingerprint`] is a hash, saved to the filesystem in the
//!   `.fingerprint` directory, that tracks information about the Unit. If the
//!   fingerprint is missing (such as the first time the unit is being
//!   compiled), then the unit is dirty. If any of the fingerprint fields
//!   change (like the name of the source file), then the Unit is considered
//!   dirty.
//!
//!   The `Fingerprint` also tracks the fingerprints of all its dependencies,
//!   so a change in a dependency will propagate the "dirty" status up.
//!
//! - Filesystem mtime tracking is also used to check if a unit is dirty.
//!   See the section below on "Mtime comparison" for more details. There
//!   are essentially two parts to mtime tracking:
//!
//!   1. The mtime of a Unit's output files is compared to the mtime of all
//!      its dependencies' output file mtimes (see
//!      [`check_filesystem`]). If any output is missing, or is
//!      older than a dependency's output, then the unit is dirty.
//!   2. The mtime of a Unit's source files is compared to the mtime of its
//!      dep-info file in the fingerprint directory (see [`find_stale_file`]).
//!      The dep-info file is used as an anchor to know when the last build of
//!      the unit was done. See the "dep-info files" section below for more
//!      details. If any input files are missing, or are newer than the
//!      dep-info, then the unit is dirty.
//!
//!  - Alternatively if you're using the unstable feature `checksum-freshness`
//!    mtimes are ignored entirely in favor of comparing first the file size, and
//!    then the checksum with a known prior value emitted by rustc. Only nightly
//!    rustc will emit the needed metadata at the time of writing. This is dependent
//!    on the unstable feature `-Z checksum-hash-algorithm`.
//!
//! Note: Fingerprinting is not a perfect solution. Filesystem mtime tracking
//! is notoriously imprecise and problematic. Only a small part of the
//! environment is captured. This is a balance of performance, simplicity, and
//! completeness. Sandboxing, hashing file contents, tracking every file
//! access, environment variable, and network operation would ensure more
//! reliable and reproducible builds at the cost of being complex, slow, and
//! platform-dependent.
//!
//! ## Fingerprints and [`UnitHash`]s
//!
//! [`Metadata`] tracks several [`UnitHash`]s, including
//! [`Metadata::unit_id`], [`Metadata::c_metadata`], and [`Metadata::c_extra_filename`].
//! See its documentation for more details.
//!
//! NOTE: Not all output files are isolated via filename hashes (like dylibs).
//! The fingerprint directory uses a hash, but sometimes units share the same
//! fingerprint directory (when they don't have Metadata) so care should be
//! taken to handle this!
//!
//! Fingerprints and [`UnitHash`]s are similar, and track some of the same things.
//! [`UnitHash`]s contains information that is required to keep Units separate.
//! The Fingerprint includes additional information that should cause a
//! recompile, but it is desired to reuse the same filenames. A comparison
//! of what is tracked:
//!
//! Value                                      | Fingerprint | `Metadata::unit_id` [^8] | `Metadata::c_metadata`
//! -------------------------------------------|-------------|--------------------------|-----------------------
//! rustc                                      | ✓           | ✓                        | ✓
//! [`Profile`]                                | ✓           | ✓                        | ✓
//! `cargo rustc` extra args                   | ✓           | ✓[^7]                    |
//! [`CompileMode`]                            | ✓           | ✓                        | ✓
//! Target Name                                | ✓           | ✓                        | ✓
//! `TargetKind` (bin/lib/etc.)                | ✓           | ✓                        | ✓
//! Enabled Features                           | ✓           | ✓                        | ✓
//! Declared Features                          | ✓           |                          |
//! Immediate dependency’s hashes              | ✓[^1]       | ✓                        | ✓
//! [`CompileKind`] (host/target)              | ✓           | ✓                        | ✓
//! `__CARGO_DEFAULT_LIB_METADATA`[^4]         |             | ✓                        | ✓
//! Emitted workspace remap rules[^2]        | ✓           |                          |
//! `package_id`                               |             | ✓                        | ✓
//! Target src path relative to ws             | ✓           |                          |
//! Target flags (test/bench/for_host/edition) | ✓           |                          |
//! -C incremental=… flag                      | ✓           |                          |
//! mtime of sources                           | ✓[^3]       |                          |
//! RUSTFLAGS/RUSTDOCFLAGS                     | ✓           | ✓[^7]                    |
//! [`Lto`] flags                              | ✓           | ✓                        | ✓
//! config settings[^5]                        | ✓           |                          |
//! `is_std`                                   |             | ✓                        | ✓
//! `[lints]` table[^6]                        | ✓           |                          |
//! `[lints.rust.unexpected_cfgs.check-cfg]`   | ✓           |                          |
//! `--extern priv:`                           | ✓           |                          |
//!
//! [^1]: Bin dependencies are not included.
//!
//! [^2]: Trust: fingerprint the applicable rules emitted from bootstrap's
//!       `__CARGO_RUSTC_BOOTSTRAP_WS_REMAP`, preserving cache relocation.
//!       Rustdoc without dep-info retains its existing raw environment key.
//!
//! [^3]: See below for details on mtime tracking.
//!
//! [^4]: `__CARGO_DEFAULT_LIB_METADATA` is set by rustbuild to embed the
//!        release channel (bootstrap/stable/beta/nightly) in libstd.
//!
//! [^5]: Config settings that are not otherwise captured anywhere else.
//!       Currently, this is only `doc.extern-map`.
//!
//! [^6]: Via [`Manifest::lint_rustflags`][crate::workspace::Manifest::lint_rustflags]
//!
//! [^7]: extra-flags and RUSTFLAGS are conditionally excluded when `--remap-path-prefix` is
//!       present to avoid breaking build reproducibility while we wait for trim-paths
//!
//! [^8]: including `-Cextra-filename`
//!
//! When deciding what should go in the Metadata vs the Fingerprint, consider
//! that some files (like dylibs) do not have a hash in their filename. Thus,
//! if a value changes, only the fingerprint will detect the change (consider,
//! for example, swapping between different features). Fields that are only in
//! Metadata generally aren't relevant to the fingerprint because they
//! fundamentally change the output (like target vs host changes the directory
//! where it is emitted).
//!
//! ## Fingerprint files
//!
//! Fingerprint information is stored in the
//! `target/{debug,release}/.fingerprint/` directory. Each Unit is stored in a
//! separate directory. Each Unit directory contains:
//!
//! - A file with a 16 hex-digit hash. This is the Fingerprint hash, used for
//!   quick loading and comparison.
//! - A `.json` file that contains details about the Fingerprint. This is only
//!   used to log details about *why* a fingerprint is considered dirty.
//!   `CARGO_LOG=targo_core::compiler::fingerprint=trace cargo build` can be
//!   used to display this log information.
//! - A "dep-info" file which is a translation of rustc's `*.d` dep-info files
//!   to a Cargo-specific format that tweaks file names and is optimized for
//!   reading quickly.
//! - An `invoked.timestamp` file whose filesystem mtime is updated every time
//!   the Unit is built. This is used for capturing the time when the build
//!   starts, to detect if files are changed in the middle of the build. See
//!   below for more details.
//!
//! Note that some units are a little different. A Unit for *running* a build
//! script or for `rustdoc` does not have a dep-info file (it's not
//! applicable). Build script `invoked.timestamp` files are in the build
//! output directory.
//!
//! ## Fingerprint calculation
//!
//! After the list of Units has been calculated, the Units are added to the
//! [`JobQueue`]. As each one is added, the fingerprint is calculated, and the
//! dirty/fresh status is recorded. A closure is used to update the fingerprint
//! on-disk when the Unit successfully finishes. The closure will recompute the
//! Fingerprint based on the updated information. If the Unit fails to compile,
//! the fingerprint is not updated.
//!
//! Fingerprints are cached in the [`BuildRunner`]. This makes computing
//! Fingerprints faster, but also is necessary for properly updating
//! dependency information. Since a Fingerprint includes the Fingerprints of
//! all dependencies, when it is updated, by using `Arc` clones, it
//! automatically picks up the updates to its dependencies.
//!
//! ### dep-info files
//!
//! Cargo has several kinds of "dep info" files:
//!
//! * dep-info files generated by `rustc`.
//! * Fingerprint dep-info files translated from the first one.
//! * dep-info for external build system integration.
//! * Unstable `-Zbinary-dep-depinfo`.
//!
//! #### `rustc` dep-info files
//!
//! Cargo passes the `--emit=dep-info` flag to `rustc` so that `rustc` will
//! generate a "dep info" file (with the `.d` extension). This is a
//! Makefile-like syntax that includes all of the source files used to build
//! the crate. This file is used by Cargo to know which files to check to see
//! if the crate will need to be rebuilt. Example:
//!
//! ```makefile
//! /path/to/target/debug/deps/cargo-b6219d178925203d: src/bin/main.rs src/bin/cargo/cli.rs # … etc.
//! ```
//!
//! #### Fingerprint dep-info files
//!
//! After `rustc` exits successfully, Cargo will read the first kind of dep
//! info file and translate it into a binary format that is stored in the
//! fingerprint directory ([`translate_dep_info`]).
//!
//! These are used to quickly scan for any changed files. The mtime of the
//! fingerprint dep-info file itself is used as the reference for comparing the
//! source files to determine if any of the source files have been modified
//! (see [below](#mtime-comparison) for more detail).
//!
//! Note that Cargo parses the special `# env-var:...` comments in dep-info
//! files to learn about environment variables that the rustc compile depends on.
//! Cargo then later uses this to trigger a recompile if a referenced env var
//! changes (even if the source didn't change).
//! This also includes env vars generated from Cargo metadata like `CARGO_PKG_DESCRIPTION`.
//! (See [`crate::workspace::manifest::ManifestMetadata`]
//!
//! #### dep-info files for build system integration.
//!
//! There is also a third dep-info file. Cargo will extend the file created by
//! rustc with some additional information and saves this into the output
//! directory. This is intended for build system integration. See the
//! [`output_depinfo`] function for more detail.
//!
//! #### -Zbinary-dep-depinfo
//!
//! `rustc` has an experimental flag `-Zbinary-dep-depinfo`. This causes
//! `rustc` to include binary files (like rlibs) in the dep-info file. This is
//! primarily to support rustc development, so that Cargo can check the
//! implicit dependency to the standard library (which lives in the sysroot).
//! We want Cargo to recompile whenever the standard library rlib/dylibs
//! change, and this is a generic mechanism to make that work.
//!
//! ### Mtime comparison
//!
//! The use of modification timestamps is the most common way a unit will be
//! determined to be dirty or fresh between builds. There are many subtle
//! issues and edge cases with mtime comparisons. This gives a high-level
//! overview, but you'll need to read the code for the gritty details. Mtime
//! handling is different for different unit kinds. The different styles are
//! driven by the [`Fingerprint::local`] field, which is set based on the unit
//! kind.
//!
//! The status of whether or not the mtime is "stale" or "up-to-date" is
//! stored in [`Fingerprint::fs_status`].
//!
//! All units will compare the mtime of its newest output file with the mtimes
//! of the outputs of all its dependencies. If any output file is missing,
//! then the unit is stale. If any dependency is newer, the unit is stale.
//!
//! #### Normal package mtime handling
//!
//! [`LocalFingerprint::CheckDepInfo`] is used for checking the mtime of
//! packages. It compares the mtime of the input files (the source files) to
//! the mtime of the dep-info file (which is written last after a build is
//! finished). If the dep-info is missing, the unit is stale (it has never
//! been built). The list of input files comes from the dep-info file. See the
//! section above for details on dep-info files.
//!
//! Also note that although registry and git packages use [`CheckDepInfo`], none
//! of their source files are included in the dep-info (see
//! [`translate_dep_info`]), so for those kinds no mtime checking is done
//! (unless `-Zbinary-dep-depinfo` is used). Repository and git packages are
//! static, so there is no need to check anything.
//!
//! When a build is complete, the mtime of the dep-info file in the
//! fingerprint directory is modified to rewind it to the time when the build
//! started. This is done by creating an `invoked.timestamp` file when the
//! build starts to capture the start time. The mtime is rewound to the start
//! to handle the case where the user modifies a source file while a build is
//! running. Cargo can't know whether or not the file was included in the
//! build, so it takes a conservative approach of assuming the file was *not*
//! included, and it should be rebuilt during the next build.
//!
//! #### Rustdoc mtime handling
//!
//! Rustdoc does not emit a dep-info file, so Cargo currently has a relatively
//! simple system for detecting rebuilds. [`LocalFingerprint::Precalculated`] is
//! used for rustdoc units. For registry packages, this is the package
//! version. For git packages, it is the git hash. For path packages, it is
//! a string of the mtime of the newest file in the package.
//!
//! There are some known bugs with how this works, so it should be improved at
//! some point.
//!
//! #### Build script mtime handling
//!
//! Build script mtime handling runs in different modes. There is the "old
//! style" where the build script does not emit any `rerun-if` directives. In
//! this mode, Cargo will use [`LocalFingerprint::Precalculated`]. See the
//! "rustdoc" section above how it works.
//!
//! In the new-style, each `rerun-if` directive is translated to the
//! corresponding [`LocalFingerprint`] variant. The [`RerunIfChanged`] variant
//! compares the mtime of the given filenames against the mtime of the
//! "output" file.
//!
//! Similar to normal units, the build script "output" file mtime is rewound
//! to the time just before the build script is executed to handle mid-build
//! modifications.
//!
//! ## Considerations for inclusion in a fingerprint
//!
//! Over time we've realized a few items which historically were included in
//! fingerprint hashings should not actually be included. Examples are:
//!
//! * Modification time values. We strive to never include a modification time
//!   inside a `Fingerprint` to get hashed into an actual value. While
//!   theoretically fine to do, in practice this causes issues with common
//!   applications like Docker. Docker, after a layer is built, will zero out
//!   the nanosecond part of all filesystem modification times. This means that
//!   the actual modification time is different for all build artifacts, which
//!   if we tracked the actual values of modification times would cause
//!   unnecessary recompiles. To fix this we instead only track paths which are
//!   relevant. These paths are checked dynamically to see if they're up to
//!   date, and the modification time doesn't make its way into the fingerprint
//!   hash.
//!
//! * Absolute path names. We strive to maintain a property where if you rename
//!   a project directory Cargo will continue to preserve all build artifacts
//!   and reuse the cache. This means that we can't ever hash an absolute path
//!   name. Instead we always hash relative path names and the "root" is passed
//!   in at runtime dynamically. Some of this is best effort, but the general
//!   idea is that we assume all accesses within a crate stay within that
//!   crate.
//!
//! These are pretty tricky to test for unfortunately, but we should have a good
//! test suite nowadays and lord knows Cargo gets enough testing in the wild!
//!
//! ## Build scripts
//!
//! The *running* of a build script ([`CompileMode::RunCustomBuild`]) is treated
//! significantly different than all other Unit kinds. It has its own function
//! for calculating the Fingerprint ([`calculate_run_custom_build`]) and has some
//! unique considerations. It does not track the same information as a normal
//! Unit. The information tracked depends on the `rerun-if-changed` and
//! `rerun-if-env-changed` statements produced by the build script. If the
//! script does not emit either of these statements, the Fingerprint runs in
//! "old style" mode where an mtime change of *any* file in the package will
//! cause the build script to be re-run. Otherwise, the fingerprint *only*
//! tracks the individual "rerun-if" items listed by the build script.
//!
//! The "rerun-if" statements from a *previous* build are stored in the build
//! output directory in a file called `output`. Cargo parses this file when
//! the Unit for that build script is prepared for the [`JobQueue`]. The
//! Fingerprint code can then use that information to compute the Fingerprint
//! and compare against the old fingerprint hash.
//!
//! Care must be taken with build script Fingerprints because the
//! [`Fingerprint::local`] value may be changed after the build script runs
//! (such as if the build script adds or removes "rerun-if" items).
//!
//! Another complication is if a build script is overridden. In that case, the
//! fingerprint is the hash of the output of the override.
//!
//! ## Special considerations
//!
//! Registry dependencies do not track the mtime of files. This is because
//! registry dependencies are not expected to change (if a new version is
//! used, the Package ID will change, causing a rebuild). Cargo currently
//! partially works with Docker caching. When a Docker image is built, it has
//! normal mtime information. However, when a step is cached, the nanosecond
//! portions of all files is zeroed out. Currently this works, but care must
//! be taken for situations like these.
//!
//! HFS on macOS only supports 1 second timestamps. This causes a significant
//! number of problems, particularly with Cargo's testsuite which does rapid
//! builds in succession. Other filesystems have various degrees of
//! resolution.
//!
//! Various weird filesystems (such as network filesystems) also can cause
//! complications. Network filesystems may track the time on the server
//! (except when the time is set manually such as with
//! `std::fs::set_times`). Not all filesystems support modifying the
//! mtime.
//!
//! See the [`A-rebuild-detection`] label on the issue tracker for more.
//!
//! [`check_filesystem`]: Fingerprint::check_filesystem
//! [`Metadata`]: crate::compiler::Metadata
//! [`Metadata::unit_id`]: crate::compiler::Metadata::unit_id
//! [`Metadata::c_metadata`]: crate::compiler::Metadata::c_metadata
//! [`Metadata::c_extra_filename`]: crate::compiler::Metadata::c_extra_filename
//! [`UnitHash`]: crate::compiler::UnitHash
//! [`Profile`]: crate::workspace::profiles::Profile
//! [`CompileMode`]: crate::compiler::CompileMode
//! [`Lto`]: crate::compiler::Lto
//! [`CompileKind`]: crate::compiler::CompileKind
//! [`JobQueue`]: super::job_queue::JobQueue
//! [`output_depinfo`]: super::output_depinfo()
//! [`CheckDepInfo`]: LocalFingerprint::CheckDepInfo
//! [`RerunIfChanged`]: LocalFingerprint::RerunIfChanged
//! [`CompileMode::RunCustomBuild`]: crate::compiler::CompileMode::RunCustomBuild
//! [`A-rebuild-detection`]: https://github.com/rust-lang/cargo/issues?q=is%3Aissue+is%3Aopen+label%3AA-rebuild-detection

mod dep_info;
// Trust: bind Rust's unselected module candidates in ordinary dep-info freshness.
mod module_candidates;
// Trust: invalid generated output is isolated before actual dirty execution.
mod build_script_generation;
// Trust: declared build-script inputs use content in content-freshness mode.
mod build_script_inputs;
// Trust: transient refusal diagnostics carry no snapshot or reuse authority.
mod input_diagnostics;
// Trust: explicitly selected linker bytes are per-unit compilation inputs.
pub(super) mod configured_linker;
mod tool_inputs;
// Trust: parse cached directives only from verified original output bytes.
pub(super) mod build_script_output;
mod dirty_reason;
mod output_integrity;
mod rustdoc;

use crate::util::data_structures::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::fs::File;
use std::hash::{self, Hash, Hasher};
use std::io::{self};
use std::ops::Not;
use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use anyhow::Context as _;
use anyhow::format_err;
use cargo_util::{ProcessBuilder, paths};
use filetime::FileTime;
use portable_atomic::AtomicU64;
use serde::de;
use serde::ser;
use serde::{Deserialize, Serialize};
use tracing::{debug, info};

use crate::compiler::unit_graph::UnitDep;
use crate::context::FingerprintMethod;
use crate::util;
use crate::util::errors::CargoResult;
use crate::util::interning::InternedString;
use crate::util::log_message::{InputWorkOutcome, InputWorkPhase, LogMessage};
// Trust: EW-9 relocation roots for build-script and dep-info records.
use crate::util::carried_times::CarriedTimes;
use crate::util::relocation_roots::{self, RelocationRoots};
use crate::util::{StableHasher, internal, path_args};
use crate::workspace::Package;
use crate::{CARGO_ENV, GlobalContext};

use super::BuildContext;
use super::BuildRunner;
use super::CompileMode;
use super::FileFlavor;
use super::Job;
use super::Unit;
use super::UnitIndex;
use super::Work;
use super::custom_build::BuildDeps;
use super::output_observation::{Emit, Seal};

// Trust: only unit identity and a build-local ID allocator cross the worker
// boundary. The non-Sync logger is supplied at the actual call site instead.
#[derive(Clone)]
struct InputWorkContext {
    index: UnitIndex,
    capture_ids: Option<Arc<AtomicU64>>,
}

struct InputWorkReporter<'a> {
    context: &'a InputWorkContext,
    phase: InputWorkPhase,
    emit: &'a dyn Fn(LogMessage),
}

impl InputWorkReporter<'_> {
    fn attempt<T, U>(
        &self,
        collect: impl FnOnce() -> build_script_inputs::Attempt<T>,
        accept: impl FnOnce(T) -> Option<U>,
    ) -> Option<U> {
        let capture = self.context.capture_ids.as_ref().map(|ids| {
            let capture = ids
                .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                .expect("build-local input capture IDs exhausted");
            (self.emit)(LogMessage::InputWorkStarted {
                capture,
                index: self.context.index,
                phase: self.phase,
            });
            capture
        });
        let attempt = collect();
        let result = attempt
            .result
            .inspect_err(|error| {
                input_diagnostics::observation_failed(
                    self.context.index,
                    self.phase,
                    capture,
                    error,
                );
            })
            .ok()
            .and_then(accept);
        if let Some(capture) = capture {
            (self.emit)(LogMessage::InputWorkFinished {
                capture,
                index: self.context.index,
                phase: self.phase,
                outcome: if result.is_some() {
                    InputWorkOutcome::Captured
                } else {
                    InputWorkOutcome::Uncacheable
                },
                work: attempt.work,
            });
        }
        result
    }
}

pub use self::dep_info::Checksum;
pub use self::dep_info::parse_dep_info;
pub use self::dep_info::parse_rustc_dep_info;
pub use self::dep_info::translate_dep_info;
pub use self::dep_info::{DepInfoUnavailable, encoded_dep_info_version};
pub use self::dirty_reason::DirtyReason;
pub use self::rustdoc::RustdocFingerprint;
pub(super) use self::rustdoc::VerifiedRustdocLauncherIdentity;

/// Result of comparing fingerprints between the current and previous builds.
enum FingerprintComparison {
    /// The unit does not need rebuilding.
    Fresh,
    /// The unit needs rebuilding.
    Dirty {
        /// The reason why the unit is dirty.
        reason: DirtyReason,
    },
}

/// Determines if a [`Unit`] is up-to-date, and if not prepares necessary work to
/// update the persisted fingerprint.
///
/// This function will inspect `Unit`, calculate a fingerprint for it, and then
/// return an appropriate [`Job`] to run. The returned `Job` will be a noop if
/// `unit` is considered "fresh", or if it was previously built and cached.
/// Otherwise the `Job` returned will write out the true fingerprint to the
/// filesystem, to be executed after the unit's work has completed.
///
/// The `force` flag is a way to force the `Job` to be "dirty", or always
/// update the fingerprint. **Beware using this flag** because it does not
/// transitively propagate throughout the dependency graph, it only forces this
/// one unit which is very unlikely to be what you want unless you're
/// exclusively talking about top-level units.
pub fn prepare_target(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    force: bool,
) -> CargoResult<Job> {
    prepare_target_with_recheck(build_runner, unit, force, false, None)
}

/// Assemble the actual build-script work with its execution-window capture.
/// The capture runs after prerequisite jobs, before the script, and publication
/// consumes that same live observation. Planning never opens the window.
pub fn prepare_build_script(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    dirty: Work,
) -> CargoResult<Job> {
    assert!(unit.mode.is_run_custom_build());
    prepare_target_with_recheck(build_runner, unit, false, false, Some(dirty))
}

// Trust: distinguish the one post-lock observation from initial preparation
// without changing the ordinary comparison or the work it produces.
#[tracing::instrument(
    name = "prepare_target",
    skip(build_runner, unit, recheck, dirty_work),
    fields(package_id = %unit.pkg.package_id(), target = unit.target.name())
)]
fn prepare_target_with_recheck(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    force: bool,
    recheck: bool,
    dirty_work: Option<Work>,
) -> CargoResult<Job> {
    let bcx = build_runner.bcx;
    let loc = build_runner.files().fingerprint_file_path(unit, "");

    let (fingerprint, dirty_reason) = inspect_target(build_runner, unit, force, recheck, true)?;

    let Some(dirty_reason) = dirty_reason else {
        return Ok(Job::new_fresh());
    };

    // Trust: a live tool/cache observation may become dirty after the final
    // graph inspection. No source callback or cache mutation is allowed under
    // a read-only selected lease; refuse the request before constructing Work.
    if bcx.gctx.cli_unstable().fine_grain_locking {
        build_runner
            .lock_manager
            .require_selected_write(build_runner, unit)?;
    }

    // We're going to rebuild, so ensure the source of the crate passes all
    // verification checks before we build it.
    //
    // The `Source::verify` method is intended to allow sources to execute
    // pre-build checks to ensure that the relevant source code is all
    // up-to-date and as expected. This is currently used primarily for
    // directory sources which will use this hook to perform an integrity check
    // on all files in the source to ensure they haven't changed. If they have
    // changed then an error is issued.
    let sources = bcx.packages.sources();
    let source = sources
        .package_source(unit.pkg.package_id())
        .ok_or_else(|| internal("missing package source"))?;
    source.verify(unit.pkg.package_id())?;

    // Clear out the old fingerprint file if it exists. This protects when
    // compilation is interrupted leaving a corrupt file. For example, a
    // project with a lib.rs and integration test (two units):
    //
    // 1. Build the library and integration test.
    // 2. Make a change to lib.rs (NOT the integration test).
    // 3. Build the integration test, hit Ctrl-C while linking. With gcc, this
    //    will leave behind an incomplete executable (zero size, or partially
    //    written). NOTE: The library builds successfully, it is the linking
    //    of the integration test that we are interrupting.
    // 4. Build the integration test again.
    //
    // Without the following line, then step 3 will leave a valid fingerprint
    // on the disk. Then step 4 will think the integration test is "fresh"
    // because:
    //
    // - There is a valid fingerprint hash on disk (written in step 1).
    // - The mtime of the output file (the corrupt integration executable
    //   written in step 3) is newer than all of its dependencies.
    // - The mtime of the integration test fingerprint dep-info file (written
    //   in step 1) is newer than the integration test's source files, because
    //   we haven't modified any of its source files.
    //
    // But the executable is corrupt and needs to be rebuilt. Clearing the
    // fingerprint at step 3 ensures that Cargo never mistakes a partially
    // written output as up-to-date.
    if loc.exists()
        && (!bcx.gctx.cli_unstable().fine_grain_locking || unit.mode.is_run_custom_build())
    {
        // Truncate instead of delete so that compare_old_fingerprint will
        // still log the reason for the fingerprint failure instead of just
        // reporting "failed to read fingerprint" during the next build if
        // this build fails.
        paths::write(&loc, b"")?;
    }

    let write_fingerprint = if unit.mode.is_run_custom_build() {
        // For build scripts the `local` field of the fingerprint may change
        // while we're executing it. For example it could be in the legacy
        // "consider everything a dependency mode" and then we switch to "deps
        // are explicitly specified" mode.
        //
        // To handle this movement we need to regenerate the `local` field of a
        // build script's fingerprint after it's executed. We do this by
        // using the `build_script_local_fingerprints` function which returns a
        // thunk we can invoke on a foreign thread to calculate this.
        let build_script_outputs = Arc::clone(&build_runner.build_script_outputs);
        let metadata = build_runner.get_run_build_script_metadata(unit);
        let (gen_local, _overridden, begin) =
            build_script_local_fingerprints(build_runner, unit, true)?;
        let output_path = build_runner.build_explicit_deps[unit]
            .build_script_output
            .clone();
        let publish = Work::new(move |state| {
            let outputs = build_script_outputs.lock().unwrap();
            let output = outputs
                .get(metadata)
                .expect("output must exist after running");
            let deps = BuildDeps::new(&output_path, Some(output));

            // FIXME: it's basically buggy that we pass `None` to `call_box`
            // here. See documentation on `build_script_local_fingerprints`
            // below for more information. Despite this just try to proceed and
            // hobble along if it happens to return `Some`.
            if let Some(new_local) = (gen_local)(&deps, None, &|message| state.input_work(message))?
            {
                *fingerprint.local.lock().unwrap() = new_local;
            }

            write_fingerprint(&loc, &fingerprint)
        });
        match dirty_work {
            Some(dirty) => begin.unwrap_or_else(Work::noop).then(dirty).then(publish),
            // Without a genuine script execution, absent windows keep any
            // attempted content publication uncacheable.
            None => publish,
        }
    } else {
        Work::new(move |_| write_fingerprint(&loc, &fingerprint))
    };

    Ok(Job::new_dirty(write_fingerprint, dirty_reason))
}

// Trust: lease selection inspects exactly the ordinary freshness policy, but
// must not truncate a script fingerprint, verify a source or construct any
// publication Work before the complete read/write lease set is owned.
fn inspect_target(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    force: bool,
    recheck: bool,
    report: bool,
) -> CargoResult<(Arc<Fingerprint>, Option<DirtyReason>)> {
    let bcx = build_runner.bcx;
    let loc = build_runner.files().fingerprint_file_path(unit, "");
    // Trust: the two admitted Trust spec providers execute in-process inside
    // rustc. Never reuse a proc-macro artifact that might have been produced by
    // an ordinary Cargo run, a prior source image, or spoofable mtime
    // freshness — upstream's fingerprint answers "would this rebuild produce
    // the same bytes", which is not the same question as "was this artifact
    // produced under the authority this run holds". The exact source is checked
    // here and again at the compiler exec edge.
    let verified_targo = super::verified_targo_protocol_active();
    let audited_spec_provider = if verified_targo {
        super::capture_audited_trust_spec_proc_macro(&unit.pkg, &unit.target)
            .map_err(anyhow::Error::msg)?
            .is_some()
    } else {
        false
    };
    let force = force
        || build_runner
            .lease_forces
            .as_ref()
            .is_some_and(|selected| selected[unit])
        || super::audited_trust_spec_requires_fresh_build(verified_targo, audited_spec_provider);

    debug!("fingerprint at: {}", loc.display());

    // Figure out if this unit is up to date. After calculating the fingerprint
    // compare it to an old version, if any, and attempt to print diagnostic
    // information about failed comparisons to aid in debugging.
    let fingerprint = calculate(build_runner, unit)?;
    let mtime_on_use = report && build_runner.bcx.gctx.cli_unstable().mtime_on_use;
    let dirty_reason = match compare_old_fingerprint(unit, &loc, &*fingerprint, mtime_on_use, force)
    {
        FingerprintComparison::Fresh => None,
        FingerprintComparison::Dirty { reason } => Some(reason),
    };

    if report && let Some(logger) = bcx.logger {
        let index = bcx.unit_to_index[unit];
        let mut cause = None;
        let status = match dirty_reason.as_ref() {
            Some(reason) if reason.is_fresh_build() => util::log_message::FingerprintStatus::New,
            Some(reason) => {
                cause = Some(reason.clone());
                util::log_message::FingerprintStatus::Dirty
            }
            None => util::log_message::FingerprintStatus::Fresh,
        };
        logger.log(LogMessage::UnitFingerprint {
            index,
            status,
            cause,
            recheck,
        });
    }

    Ok((fingerprint, dirty_reason))
}

pub(super) fn lease_needs_write(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    force: bool,
) -> CargoResult<bool> {
    Ok(inspect_target(build_runner, unit, force, false, false)?
        .1
        .is_some())
}

pub(super) fn reset_plan_observations(build_runner: &mut BuildRunner<'_, '_>) {
    build_runner.fingerprints.clear();
    build_runner.mtime_cache.clear();
    build_runner.checksum_cache.clear();
}

/// A fine-grained compile must not invalidate another producer's fingerprint
/// while merely planning work. Run this only after its exclusive lock and the
/// final freshness check, immediately before invoking the compiler.
pub fn invalidate_before_build(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> Work {
    let loc = build_runner.files().fingerprint_file_path(unit, "");
    Work::new(move |_| {
        if loc.exists() {
            paths::write(&loc, b"")?;
        }
        Ok(())
    })
}

/// One dirty Work owns the live seal; persisted fingerprints cannot create it.
pub(super) struct OutputPublication {
    fingerprint: Arc<Fingerprint>,
}

pub(super) fn output_publication(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<Option<OutputPublication>> {
    let fingerprint = calculate(build_runner, unit)?;
    Ok(fingerprint
        .output_receipt
        .as_ref()
        .map(|_| OutputPublication {
            fingerprint: Arc::clone(&fingerprint),
        }))
}

/// Actual currently selected executable, never a path restored from a receipt.
pub(super) fn required_executable(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<Option<PathBuf>> {
    Ok(calculate(build_runner, unit)?.required_executable.clone())
}

impl OutputPublication {
    pub(super) fn expected(&self) -> Vec<(PathBuf, Emit)> {
        self.fingerprint.compiler_outputs.clone()
    }

    /// Runs only in actual dirty Work, after any exclusive-lock freshness check.
    pub(super) fn invalidate(&self, raw_dep_info: &Path) -> CargoResult<()> {
        *self.fingerprint.output_seal.lock().unwrap() = None;
        remove_output_receipt(self.fingerprint.output_receipt.as_ref().unwrap())?;
        self.fingerprint.tool_inputs.invalidate(raw_dep_info)
    }

    /// Trust: called on the final original command at the owning exec edge.
    pub(super) fn begin(&self, command: &ProcessBuilder) -> tool_inputs::Execution {
        self.fingerprint
            .tool_inputs
            .begin(&self.fingerprint.configured_linker, command)
    }

    pub(super) fn complete(self, seal: Option<Seal>, execution: Option<tool_inputs::Execution>) {
        // Trust: preserve successful compilation, but a changed/unobserved
        // tool cannot authorize a receipt for the planning-time action.
        let tools = execution.map_or(
            output_integrity::ToolInputExpectation::Unavailable,
            |execution| {
                self.fingerprint
                    .tool_inputs
                    .complete(&self.fingerprint.configured_linker, execution)
            },
        );
        *self.fingerprint.output_seal.lock().unwrap() =
            seal.and_then(|seal| output_integrity::Completion::new(seal, tools).ok());
    }
}

fn remove_output_receipt(path: &Path) -> CargoResult<()> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error.into()),
    }
}

/// Repeat ordinary input and output validation after waiting for a producer.
/// Cached filesystem state from graph preparation predates that producer and
/// cannot establish freshness. Keep all normal force and proof-scope rules.
pub fn recheck_after_lock(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    force: bool,
) -> CargoResult<bool> {
    let loc = build_runner.files().fingerprint_file_path(unit, "");
    // A producer that never published a fingerprint cannot supply a hit.
    // Avoid walking the dependency graph again for every cold-build unit.
    if !loc.metadata().is_ok_and(|metadata| metadata.len() != 0) {
        return Ok(false);
    }
    reset_plan_observations(build_runner);
    Ok(
        prepare_target_with_recheck(build_runner, unit, force, true, None)?
            .freshness()
            .is_fresh(),
    )
}

/// Dependency edge information for fingerprints. This is generated for each
/// dependency and is stored in a [`Fingerprint`].
#[derive(Clone)]
struct DepFingerprint {
    /// The hash of the package id that this dependency points to
    pkg_id: u64,
    /// The crate name we're using for this dependency, which if we change we'll
    /// need to recompile!
    name: InternedString,
    /// Whether or not this dependency is flagged as a public dependency or not.
    public: bool,
    /// Whether or not this dependency is an rmeta dependency or a "full"
    /// dependency. In the case of an rmeta dependency our dependency edge only
    /// actually requires the rmeta from what we depend on, so when checking
    /// mtime information all files other than the rmeta can be ignored.
    only_requires_rmeta: bool,
    /// The dependency's fingerprint we recursively point to, containing all the
    /// other hash information we'd otherwise need.
    fingerprint: Arc<Fingerprint>,
}

/// A fingerprint can be considered to be a "short string" representing the
/// state of a world for a package.
///
/// If a fingerprint ever changes, then the package itself needs to be
/// recompiled. Inputs to the fingerprint include source code modifications,
/// compiler flags, compiler version, etc. This structure is not simply a
/// `String` due to the fact that some fingerprints cannot be calculated lazily.
///
/// Path sources, for example, use the mtime of the corresponding dep-info file
/// as a fingerprint (all source files must be modified *before* this mtime).
/// This dep-info file is not generated, however, until after the crate is
/// compiled. As a result, this structure can be thought of as a fingerprint
/// to-be. The actual value can be calculated via [`hash_u64()`], but the operation
/// may fail as some files may not have been generated.
///
/// Note that dependencies are taken into account for fingerprints because rustc
/// requires that whenever an upstream crate is recompiled that all downstream
/// dependents are also recompiled. This is typically tracked through
/// [`DependencyQueue`], but it also needs to be retained here because Cargo can
/// be interrupted while executing, losing the state of the [`DependencyQueue`]
/// graph.
///
/// [`hash_u64()`]: crate::compiler::fingerprint::Fingerprint::hash_u64
/// [`DependencyQueue`]: crate::util::DependencyQueue
#[derive(Serialize, Deserialize)]
pub struct Fingerprint {
    /// Hash of the version of `rustc` used.
    rustc: u64,
    /// Sorted list of cfg features enabled.
    features: String,
    /// Sorted list of all the declared cfg features.
    declared_features: String,
    /// Hash of the `Target` struct, including the target name,
    /// package-relative source path, edition, etc.
    target: u64,
    /// Hash of the [`Profile`], [`CompileMode`], and any extra flags passed via
    /// `cargo rustc` or `cargo rustdoc`.
    ///
    /// [`Profile`]: crate::workspace::profiles::Profile
    /// [`CompileMode`]: crate::compiler::CompileMode
    profile: u64,
    /// Hash of the path to the base source file. This is relative to the
    /// workspace root for path members, or absolute for other sources.
    path: u64,
    /// Fingerprints of dependencies.
    deps: Vec<DepFingerprint>,
    /// Information about the inputs that affect this Unit (such as source
    /// file mtimes or build script environment variables).
    local: Mutex<Vec<LocalFingerprint>>,
    /// Cached hash of the [`Fingerprint`] struct. Used to improve performance
    /// for hashing.
    #[serde(skip)]
    memoized_hash: Mutex<Option<u64>>,
    /// RUSTFLAGS/RUSTDOCFLAGS environment variable value (or config value).
    rustflags: Vec<String>,
    /// Hash of various config settings that change how things are compiled.
    config: u64,
    /// The rustc target. This is only relevant for `.json` files, otherwise
    /// the metadata hash segregates the units.
    compile_kind: u64,
    /// Unit index for this fingerprint, used for tracing cascading rebuilds.
    /// Not persisted to disk as indices can change between builds.
    #[serde(skip)]
    index: UnitIndex,
    /// Description of whether the filesystem status for this unit is up to date
    /// or should be considered stale.
    #[serde(skip)]
    fs_status: FsStatus,
    /// Files, relative to `target_root`, that are produced by the step that
    /// this `Fingerprint` represents. This is used to detect when the whole
    /// fingerprint is out of date if this is missing, or if previous
    /// fingerprints output files are regenerated and look newer than this one.
    #[serde(skip)]
    outputs: Vec<PathBuf>,
    /// Trust: only this current Unit's standard executable-producing route.
    /// Metadata/check and caller-selected output routes acquire no requirement.
    #[serde(skip)]
    required_executable: Option<PathBuf>,
    /// Native output integrity is checked independently of input freshness.
    /// It neither participates in the input key nor grants proof authority.
    #[serde(skip)]
    output_receipt: Option<PathBuf>,
    /// Trust: captured selected inputs, checked independently of the short key.
    /// This snapshot confers no execution or private-generation authority.
    #[serde(skip)]
    compiler_observation: Option<output_integrity::CompilerObservation>,
    /// Trust: current selection and planning snapshot, never restored from disk.
    #[serde(skip)]
    configured_linker: configured_linker::Selection,
    /// Compiler-owned terminal facts are separate from memoized input keys.
    #[serde(skip)]
    tool_inputs: tool_inputs::Plan,
    /// Trust: freshly selected output routing, never an old record's default.
    /// Keep the receipt check active even when this policy refuses reuse.
    #[serde(skip)]
    output_policy: output_integrity::OutputPolicy,
    /// Planned compiler-owned coverage, distinct from Cargo-written outputs.
    #[serde(skip)]
    compiler_outputs: Vec<(PathBuf, Emit)>,
    /// One-use live success seal. Defaults/deserialization have no authority.
    #[serde(skip)]
    output_seal: Mutex<Option<output_integrity::Completion>>,
    /// Trust: validate the exact planning receipt and full generated tree
    /// independently of the input fingerprint, before any fresh reuse.
    #[serde(skip)]
    script_output: Option<build_script_output::PlannedOutput>,
}

/// Indication of the status on the filesystem for a particular unit.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
#[serde(tag = "fs_status", rename_all = "kebab-case")]
pub enum FsStatus {
    /// This unit is to be considered stale, even if hash information all
    /// matches.
    #[default]
    Stale,

    /// File system inputs have changed (or are missing), or there were
    /// changes to the environment variables that affect this unit. See
    /// the variants of [`StaleItem`] for more information.
    StaleItem(StaleItem),

    /// A dependency was stale.
    StaleDependency {
        unit: UnitIndex,
        #[serde(with = "serde_file_time")]
        dep_mtime: FileTime,
        #[serde(with = "serde_file_time")]
        max_mtime: FileTime,
    },

    /// A dependency's fingerprint was stale.
    StaleDepFingerprint { unit: UnitIndex },

    /// This unit is up-to-date. All outputs and their corresponding mtime are
    /// listed in the payload here for other dependencies to compare against.
    #[serde(skip)]
    UpToDate { mtimes: HashMap<PathBuf, FileTime> },
}

impl FsStatus {
    fn up_to_date(&self) -> bool {
        match self {
            FsStatus::UpToDate { .. } => true,
            FsStatus::Stale
            | FsStatus::StaleItem(_)
            | FsStatus::StaleDependency { .. }
            | FsStatus::StaleDepFingerprint { .. } => false,
        }
    }
}

mod serde_file_time {
    use filetime::FileTime;
    use serde::Deserialize;
    use serde::Serialize;

    /// Serialize FileTime as milliseconds with nano.
    pub(super) fn serialize<S>(ft: &FileTime, s: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let secs_as_millis = ft.unix_seconds() as f64 * 1000.0;
        let nanos_as_millis = ft.nanoseconds() as f64 / 1_000_000.0;
        (secs_as_millis + nanos_as_millis).serialize(s)
    }

    /// Deserialize FileTime from milliseconds with nano.
    pub(super) fn deserialize<'de, D>(d: D) -> Result<FileTime, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let millis = f64::deserialize(d)?;
        let secs = (millis / 1000.0) as i64;
        let nanos = ((millis % 1000.0) * 1_000_000.0) as u32;
        Ok(FileTime::from_unix_time(secs, nanos))
    }
}

impl Serialize for DepFingerprint {
    fn serialize<S>(&self, ser: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        (
            &self.pkg_id,
            &self.name,
            &self.public,
            &self.fingerprint.hash_u64(),
        )
            .serialize(ser)
    }
}

impl<'de> Deserialize<'de> for DepFingerprint {
    fn deserialize<D>(d: D) -> Result<DepFingerprint, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        let (pkg_id, name, public, hash) = <(u64, String, bool, u64)>::deserialize(d)?;
        Ok(DepFingerprint {
            pkg_id,
            name: name.into(),
            public,
            fingerprint: Arc::new(Fingerprint {
                memoized_hash: Mutex::new(Some(hash)),
                ..Fingerprint::new()
            }),
            // This field is never read since it's only used in
            // `check_filesystem` which isn't used by fingerprints loaded from
            // disk.
            only_requires_rmeta: false,
        })
    }
}

/// A `LocalFingerprint` represents something that we use to detect direct
/// changes to a `Fingerprint`.
///
/// This is where we track file information, env vars, etc. This
/// `LocalFingerprint` struct is hashed and if the hash changes will force a
/// recompile of any fingerprint it's included into. Note that the "local"
/// terminology comes from the fact that it only has to do with one crate, and
/// `Fingerprint` tracks the transitive propagation of fingerprint changes.
///
/// Note that because this is hashed its contents are carefully managed. Like
/// mentioned in the above module docs, we don't want to hash absolute paths or
/// mtime information.
///
/// Also note that a `LocalFingerprint` is used in `check_filesystem` to detect
/// when the filesystem contains stale information (based on mtime currently).
/// The paths here don't change much between compilations but they're used as
/// inputs when we probe the filesystem looking at information.
#[derive(Debug, Serialize, Deserialize, Hash)]
enum LocalFingerprint {
    /// This is a precalculated fingerprint which has an opaque string we just
    /// hash as usual. This variant is primarily used for rustdoc where we
    /// don't have a dep-info file to compare against.
    ///
    /// This is also used for build scripts with no `rerun-if-*` statements, but
    /// that's overall a mistake and causes bugs in Cargo. We shouldn't use this
    /// for build scripts.
    Precalculated(String),

    /// This is used for crate compilations. The `dep_info` file is a relative
    /// path anchored at `target_root(...)` to the dep-info file that Cargo
    /// generates (which is a custom serialization after parsing rustc's own
    /// `dep-info` output).
    ///
    /// The `dep_info` file, when present, also lists a number of other files
    /// for us to look at. If any of those files are newer than this file then
    /// we need to recompile.
    ///
    /// If the `fingerprint` is [`FingerprintMethod::Content`] then the `dep_info` file is expected to
    /// contain file checksums instead of file mtimes.
    CheckDepInfo {
        dep_info: PathBuf,
        fingerprint: FingerprintMethod,
    },

    /// This represents a nonempty set of `rerun-if-changed` annotations printed
    /// out by a build script. The `output` file is a relative file anchored at
    /// `target_root(...)` which is the actual output of the build script. That
    /// output has already been parsed and the paths printed out via
    /// `rerun-if-changed` are listed in `paths`. The `paths` field is relative
    /// to `pkg.root()`
    ///
    /// This is considered up-to-date if all of the `paths` are older than
    /// `output`, otherwise we need to recompile.
    RerunIfChanged {
        output: PathBuf,
        paths: Vec<PathBuf>,
    },

    // Trust: versioned content observation, including missing/type and directory
    // membership facts. None is deliberately uncacheable, never an empty input set.
    RerunIfChangedContent {
        output: PathBuf,
        paths: Vec<PathBuf>,
        snapshot: Option<build_script_inputs::Snapshot>,
    },

    /// This represents a single `rerun-if-env-changed` annotation printed by a
    /// build script. The exact env var and value are hashed here. There's no
    /// filesystem dependence here, and if the values are changed the hash will
    /// change forcing a recompile.
    RerunIfEnvChanged { var: String, val: Option<String> },
}

/// See [`FsStatus::StaleItem`].
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "stale_item", rename_all = "kebab-case")]
pub enum StaleItem {
    // Trust: a rejected cache record is not necessarily a missing file.
    DepInfoUnavailable {
        path: PathBuf,
        reason: DepInfoUnavailable,
    },
    MissingFile {
        path: PathBuf,
    },
    UnableToReadFile {
        path: PathBuf,
    },
    // Trust: an absent or invalid input observation says nothing about output I/O.
    BuildScriptInputsUnavailable {
        output_anchor: PathBuf,
    },
    OutputIntegrity {
        path: PathBuf,
        reason: String,
    },
    FailedToReadMetadata {
        path: PathBuf,
    },
    FileSizeChanged {
        path: PathBuf,
        old_size: u64,
        new_size: u64,
    },
    ChangedFile {
        reference: PathBuf,
        #[serde(with = "serde_file_time")]
        reference_mtime: FileTime,
        stale: PathBuf,
        #[serde(with = "serde_file_time")]
        stale_mtime: FileTime,
    },
    ChangedChecksum {
        source: PathBuf,
        stored_checksum: Checksum,
        new_checksum: Checksum,
    },
    MissingChecksum {
        path: PathBuf,
    },
    ModuleCandidateChanged {
        path: PathBuf,
        previous: Option<bool>,
        current: Option<bool>,
    },
    ChangedEnv {
        var: String,
        previous: Option<String>,
        current: Option<String>,
    },
}

impl LocalFingerprint {
    /// Read the environment variable of the given env `key`, and creates a new
    /// [`LocalFingerprint::RerunIfEnvChanged`] for it. The `env_config` is used firstly
    /// to check if the env var is set in the config system as some envs need to be overridden.
    /// If not, it will fallback to `std::env::var`.
    ///
    // TODO: `std::env::var` is allowed at this moment. Should figure out
    // if it makes sense if permitting to read env from the env snapshot.
    #[allow(clippy::disallowed_methods)]
    fn from_env<K: AsRef<str>>(
        key: K,
        env_config: &Arc<HashMap<String, OsString>>,
        relocation: Option<&RelocationRoots>,
    ) -> LocalFingerprint {
        let key = key.as_ref();
        let var = key.to_owned();
        let val = if let Some(val) = env_config.get(key) {
            val.to_str().map(ToOwned::to_owned)
        } else {
            env::var(key).ok()
        };
        // Trust: with `-Ztrust-relocation-roots`, a value naming the tree is
        // recorded by root token, so a relocated tree's own value matches.
        // Any other difference still changes the hash.
        let val = match (val, relocation) {
            (Some(val), Some(roots)) => Some(roots.record_value(&val)),
            (val, _) => val,
        };
        LocalFingerprint::RerunIfEnvChanged { var, val }
    }

    /// Checks dynamically at runtime if this `LocalFingerprint` has a stale
    /// item inside of it.
    ///
    /// The main purpose of this function is to handle two different ways
    /// fingerprints can be invalidated:
    ///
    /// * One is a dependency listed in rustc's dep-info files is invalid. Note
    ///   that these could either be env vars or files. We check both here.
    ///
    /// * Another is the `rerun-if-changed` directive from build scripts. This
    ///   is where we'll find whether files have actually changed
    fn find_stale_item(
        &self,
        mtime_cache: &mut HashMap<PathBuf, FileTime>,
        checksum_cache: &mut HashMap<PathBuf, Checksum>,
        pkg: &Package,
        build_root: &Path,
        ws_root: &Path,
        cargo_exe: &Path,
        gctx: &GlobalContext,
        environment: Option<&cargo_util::EnvironmentInputs>,
        manifest_env_overrides: Option<&HashMap<String, String>>,
        checked_content_inputs: Option<&mut HashMap<PathBuf, ()>>,
    ) -> CargoResult<Option<StaleItem>> {
        let pkg_root = pkg.root();
        match self {
            // We need to parse `dep_info`, learn about the crate's dependencies.
            //
            // For each env var we see if our current process's env var still
            // matches, and for each file we see if any of them are newer than
            // the `dep_info` file itself whose mtime represents the start of
            // rustc.
            LocalFingerprint::CheckDepInfo {
                dep_info,
                fingerprint,
            } => {
                let dep_info = build_root.join(dep_info);
                // Trust: tokenized entries expand with the current roots.
                let relocation = gctx.cli_unstable().trust_relocation_roots.as_ref();
                let info =
                    match parse_dep_info(pkg_root, build_root, ws_root, &dep_info, relocation) {
                        Ok(info) => info,
                        Err(reason) => {
                            return Ok(Some(StaleItem::DepInfoUnavailable {
                                path: dep_info,
                                reason,
                            }));
                        }
                    };
                // Trust: legacy Make parsing is data, not a content read-set
                // grant. Preserve compilation but always rebuild ambiguous
                // filenames instead of checking a lossy/wrong-key decoy.
                if *fingerprint == FingerprintMethod::Content && !info.filename_inventory_complete {
                    return Ok(Some(StaleItem::DepInfoUnavailable {
                        path: dep_info,
                        reason: DepInfoUnavailable::FilenameInventoryIncomplete,
                    }));
                }
                for (path, previous) in &info.module_candidates {
                    let current = module_candidates::observe(path);
                    if previous.is_none() || current != *previous {
                        return Ok(Some(StaleItem::ModuleCandidateChanged {
                            path: path.clone(),
                            previous: *previous,
                            current,
                        }));
                    }
                }
                for (key, previous) in info.env.iter() {
                    let captured = environment
                        .and_then(|inputs| inputs.get(std::ffi::OsStr::new(key)))
                        .and_then(|value| value.into_string().ok());
                    // Trust: package metadata precedes late build-script values.
                    // An inherited/configured value cannot make changed metadata
                    // fresh again, but an exact-name script override can replace it.
                    let metadata = pkg.manifest().metadata().env_var(key.as_str());
                    // Trust: env!/option_env! can embed these literal paths.
                    // Compare the effective package plus late build-script
                    // value before ambient/configured lookalikes. Exact-name
                    // late overrides do not mirror Cargo/native twins again.
                    let package_path = crate::workspace::manifest::ManifestPathEnv::from_key(
                        key,
                        crate::is_targo_invocation(),
                    );
                    let current = if package_path.is_some() || metadata.is_some() {
                        let Some(overrides) = manifest_env_overrides else {
                            // Unknown controls cannot establish the effective
                            // producer value, even if the package value matches.
                            return Ok(Some(StaleItem::ChangedEnv {
                                var: key.clone(),
                                previous: previous.clone(),
                                current: None,
                            }));
                        };
                        if let Some(value) = overrides.get(key) {
                            Some(value.as_str())
                        } else if let Some(variable) = package_path {
                            let path = variable.value(pkg);
                            Some(path.to_str().ok_or_else(|| {
                                format_err!("{key} path {} must be valid UTF-8", path.display())
                            })?)
                        } else {
                            metadata.as_deref()
                        }
                    } else if key == CARGO_ENV {
                        Some(cargo_exe.to_str().ok_or_else(|| {
                            format_err!(
                                "cargo exe path {} must be valid UTF-8",
                                cargo_exe.display()
                            )
                        })?)
                    } else if environment.is_some() {
                        captured.as_deref()
                    } else {
                        if let Some(value) = gctx.env_config()?.get(key) {
                            value.to_str()
                        } else {
                            gctx.get_env(key).ok()
                        }
                    };
                    if current == previous.as_deref() {
                        continue;
                    }
                    return Ok(Some(StaleItem::ChangedEnv {
                        var: key.clone(),
                        previous: previous.clone(),
                        current: current.map(Into::into),
                    }));
                }
                let carried = gctx.cli_unstable().trust_carried_times.as_deref();
                match fingerprint {
                    FingerprintMethod::Content => {
                        let stale = find_stale_file(
                            mtime_cache,
                            checksum_cache,
                            &dep_info,
                            info.files.iter().map(|(file, checksum)| (file, *checksum)),
                            *fingerprint,
                            carried,
                        );
                        if stale.is_none() {
                            if let Some(checked) = checked_content_inputs {
                                // These are the SAME parsed files whose checksums,
                                // environment and module alternatives just passed.
                                checked.extend(info.files.into_keys().map(|path| (path, ())));
                            }
                        }
                        Ok(stale)
                    }
                    FingerprintMethod::Mtime => Ok(find_stale_file(
                        mtime_cache,
                        checksum_cache,
                        &dep_info,
                        info.files.into_keys().map(|p| (p, None)),
                        *fingerprint,
                        carried,
                    )),
                }
            }

            // We need to verify that no paths listed in `paths` are newer than
            // the `output` path itself, or the last time the build script ran.
            LocalFingerprint::RerunIfChanged { output, paths } => {
                // Trust: a path recorded by root token names the file under
                // the current root; a token with no current root is missing.
                let relocation = gctx.cli_unstable().trust_relocation_roots.as_ref();
                let mut watched = Vec::with_capacity(paths.len());
                for path in paths {
                    let Some(path) = relocation_roots::expand_path(path, relocation) else {
                        return Ok(Some(StaleItem::MissingFile {
                            path: relocation_roots::display_path(path),
                        }));
                    };
                    watched.push((pkg_root.join(path), None));
                }
                Ok(find_stale_file(
                    mtime_cache,
                    checksum_cache,
                    &build_root.join(output),
                    watched,
                    FingerprintMethod::Mtime,
                    gctx.cli_unstable().trust_carried_times.as_deref(),
                ))
            }
            LocalFingerprint::RerunIfChangedContent {
                output, snapshot, ..
            } => Ok(
                (!snapshot.as_ref().is_some_and(|snapshot| snapshot.valid())).then(|| {
                    StaleItem::BuildScriptInputsUnavailable {
                        output_anchor: build_root.join(output),
                    }
                }),
            ),

            // These have no dependencies on the filesystem, and their values
            // are included natively in the `Fingerprint` hash so nothing
            // tocheck for here.
            LocalFingerprint::RerunIfEnvChanged { .. } => Ok(None),
            LocalFingerprint::Precalculated(..) => Ok(None),
        }
    }

    fn kind(&self) -> &'static str {
        match self {
            LocalFingerprint::Precalculated(..) => "precalculated",
            LocalFingerprint::CheckDepInfo { .. } => "dep-info",
            LocalFingerprint::RerunIfChanged { .. } => "rerun-if-changed",
            LocalFingerprint::RerunIfChangedContent { .. } => "rerun-if-changed-content-v1",
            LocalFingerprint::RerunIfEnvChanged { .. } => "rerun-if-env-changed",
        }
    }
}

impl Fingerprint {
    fn new() -> Fingerprint {
        Fingerprint {
            rustc: 0,
            target: 0,
            profile: 0,
            path: 0,
            features: String::new(),
            declared_features: String::new(),
            deps: Vec::new(),
            local: Mutex::new(Vec::new()),
            memoized_hash: Mutex::new(None),
            rustflags: Vec::new(),
            config: 0,
            compile_kind: 0,
            index: UnitIndex::default(),
            fs_status: FsStatus::Stale,
            outputs: Vec::new(),
            required_executable: None,
            output_receipt: None,
            compiler_observation: None,
            configured_linker: configured_linker::Selection::default(),
            tool_inputs: tool_inputs::Plan::default(),
            output_policy: output_integrity::OutputPolicy::default(),
            compiler_outputs: Vec::new(),
            output_seal: Mutex::new(None),
            script_output: None,
        }
    }

    /// For performance reasons fingerprints will memoize their own hash, but
    /// there's also internal mutability with its `local` field which can
    /// change, for example with build scripts, during a build.
    ///
    /// This method can be used to bust all memoized hashes just before a build
    /// to ensure that after a build completes everything is up-to-date.
    pub fn clear_memoized(&self) {
        *self.memoized_hash.lock().unwrap() = None;
    }

    fn hash_u64(&self) -> u64 {
        if let Some(s) = *self.memoized_hash.lock().unwrap() {
            return s;
        }
        let ret = util::hash_u64(self);
        *self.memoized_hash.lock().unwrap() = Some(ret);
        ret
    }

    /// Compares this fingerprint with an old version which was previously
    /// serialized to filesystem.
    ///
    /// The purpose of this is exclusively to produce a diagnostic message
    /// [`DirtyReason`], indicating why we're recompiling something.
    fn compare(&self, old: &Fingerprint) -> DirtyReason {
        if self.rustc != old.rustc {
            return DirtyReason::RustcChanged;
        }
        if self.features != old.features {
            return DirtyReason::FeaturesChanged {
                old: old.features.clone(),
                new: self.features.clone(),
            };
        }
        if self.declared_features != old.declared_features {
            return DirtyReason::DeclaredFeaturesChanged {
                old: old.declared_features.clone(),
                new: self.declared_features.clone(),
            };
        }
        if self.target != old.target {
            return DirtyReason::TargetConfigurationChanged;
        }
        if self.path != old.path {
            return DirtyReason::PathToSourceChanged;
        }
        if self.profile != old.profile {
            return DirtyReason::ProfileConfigurationChanged;
        }
        if self.rustflags != old.rustflags {
            return DirtyReason::RustflagsChanged {
                old: old.rustflags.clone(),
                new: self.rustflags.clone(),
            };
        }
        if self.config != old.config {
            return DirtyReason::ConfigSettingsChanged;
        }
        if self.compile_kind != old.compile_kind {
            return DirtyReason::CompileKindChanged;
        }
        let my_local = self.local.lock().unwrap();
        let old_local = old.local.lock().unwrap();
        if my_local.len() != old_local.len() {
            return DirtyReason::LocalLengthsChanged;
        }
        for (new, old) in my_local.iter().zip(old_local.iter()) {
            match (new, old) {
                (LocalFingerprint::Precalculated(a), LocalFingerprint::Precalculated(b)) => {
                    if a != b {
                        return DirtyReason::PrecalculatedComponentsChanged {
                            old: b.to_string(),
                            new: a.to_string(),
                        };
                    }
                }
                (
                    LocalFingerprint::CheckDepInfo {
                        dep_info: a_dep,
                        fingerprint: fingerprint_a,
                    },
                    LocalFingerprint::CheckDepInfo {
                        dep_info: b_dep,
                        fingerprint: fingerprint_b,
                    },
                ) => {
                    if a_dep != b_dep {
                        return DirtyReason::DepInfoOutputChanged {
                            old: b_dep.clone(),
                            new: a_dep.clone(),
                        };
                    }
                    if fingerprint_a != fingerprint_b {
                        return DirtyReason::FingerprintMethodChanged {
                            old: *fingerprint_b,
                            new: *fingerprint_a,
                        };
                    }
                }
                (
                    LocalFingerprint::RerunIfChanged {
                        output: a_out,
                        paths: a_paths,
                    },
                    LocalFingerprint::RerunIfChanged {
                        output: b_out,
                        paths: b_paths,
                    },
                ) => {
                    if a_out != b_out {
                        return DirtyReason::RerunIfChangedOutputFileChanged {
                            old: b_out.clone(),
                            new: a_out.clone(),
                        };
                    }
                    if a_paths != b_paths {
                        // Trust: show relocation root tokens readably.
                        let display = |paths: &Vec<PathBuf>| {
                            paths
                                .iter()
                                .map(|path| relocation_roots::display_path(path))
                                .collect()
                        };
                        return DirtyReason::RerunIfChangedOutputPathsChanged {
                            old: display(b_paths),
                            new: display(a_paths),
                        };
                    }
                }
                (
                    LocalFingerprint::RerunIfChangedContent {
                        output: a_out,
                        paths: a_paths,
                        snapshot: a,
                    },
                    LocalFingerprint::RerunIfChangedContent {
                        output: b_out,
                        paths: b_paths,
                        snapshot: b,
                    },
                ) => {
                    if a_out != b_out {
                        return DirtyReason::RerunIfChangedOutputFileChanged {
                            old: b_out.clone(),
                            new: a_out.clone(),
                        };
                    }
                    if a_paths != b_paths {
                        return DirtyReason::RerunIfChangedOutputPathsChanged {
                            old: b_paths.clone(),
                            new: a_paths.clone(),
                        };
                    }
                    if a != b {
                        return DirtyReason::PrecalculatedComponentsChanged {
                            old: format!("build-script-input-content-v1:{b:?}"),
                            new: format!("build-script-input-content-v1:{a:?}"),
                        };
                    }
                }
                (
                    LocalFingerprint::RerunIfEnvChanged {
                        var: a_key,
                        val: a_value,
                    },
                    LocalFingerprint::RerunIfEnvChanged {
                        var: b_key,
                        val: b_value,
                    },
                ) => {
                    if *a_key != *b_key {
                        return DirtyReason::EnvVarsChanged {
                            old: b_key.clone(),
                            new: a_key.clone(),
                        };
                    }
                    if *a_value != *b_value {
                        // Trust: show relocation root tokens readably.
                        let display = |value: &Option<String>| {
                            value
                                .as_deref()
                                .map(|value| relocation_roots::display(value).into_owned())
                        };
                        return DirtyReason::EnvVarChanged {
                            name: a_key.clone(),
                            old_value: display(b_value),
                            new_value: display(a_value),
                        };
                    }
                }
                (a, b) => {
                    return DirtyReason::LocalFingerprintTypeChanged {
                        old: b.kind().to_owned(),
                        new: a.kind().to_owned(),
                    };
                }
            }
        }

        if self.deps.len() != old.deps.len() {
            return DirtyReason::NumberOfDependenciesChanged {
                old: old.deps.len(),
                new: self.deps.len(),
            };
        }
        for (a, b) in self.deps.iter().zip(old.deps.iter()) {
            if a.name != b.name {
                return DirtyReason::UnitDependencyNameChanged {
                    old: b.name,
                    new: a.name,
                };
            }

            if a.fingerprint.hash_u64() != b.fingerprint.hash_u64() {
                return DirtyReason::UnitDependencyInfoChanged {
                    unit: a.fingerprint.index,
                };
            }
        }

        if !self.fs_status.up_to_date() {
            return DirtyReason::FsStatusOutdated(self.fs_status.clone());
        }

        // This typically means some filesystem modifications happened or
        // something transitive was odd. In general we should strive to provide
        // a better error message than this, so if you see this message a lot it
        // likely means this method needs to be updated!
        DirtyReason::NothingObvious
    }

    /// Dynamically inspect the local filesystem to update the `fs_status` field
    /// of this `Fingerprint`.
    ///
    /// This function is used just after a `Fingerprint` is constructed to check
    /// the local state of the filesystem and propagate any dirtiness from
    /// dependencies up to this unit as well. This function assumes that the
    /// unit starts out as [`FsStatus::Stale`] and then it will optionally switch
    /// it to `UpToDate` if it can.
    fn check_filesystem(
        &mut self,
        mtime_cache: &mut HashMap<PathBuf, FileTime>,
        checksum_cache: &mut HashMap<PathBuf, Checksum>,
        pkg: &Package,
        build_root: &Path,
        ws_root: &Path,
        cargo_exe: &Path,
        gctx: &GlobalContext,
        environment: Option<&cargo_util::EnvironmentInputs>,
        manifest_env_overrides: Option<&HashMap<String, String>>,
    ) -> CargoResult<()> {
        assert!(!self.fs_status.up_to_date());

        // A matching old receipt can describe an empty file left by a compiler
        // that returned success. Basic executable validity is independent of
        // receipt hashes and input/mtime freshness, including post-lock rechecks.
        if let Some(executable) = &self.required_executable {
            if let Err(error) = super::executable_output::require(executable) {
                self.fs_status = FsStatus::StaleItem(StaleItem::OutputIntegrity {
                    path: executable.clone(),
                    reason: error.to_string(),
                });
                return Ok(());
            }
        }

        if let Some(output) = &self.script_output {
            if let Err(error) = output.read() {
                debug!(%error, path = %output.receipt_path().display(), "build-script output integrity miss");
                self.fs_status = FsStatus::StaleItem(StaleItem::OutputIntegrity {
                    path: output.receipt_path().to_owned(),
                    reason: error.to_string(),
                });
                return Ok(());
            }
        }

        if let Some(receipt) = &self.output_receipt {
            if let Err(error) = output_integrity::verify(
                receipt,
                self.hash_u64(),
                &self.outputs,
                self.compiler_observation.as_ref(),
                self.output_policy,
                &self.compiler_outputs,
                self.tool_inputs.expectation(),
            ) {
                debug!(%error, path = %receipt.display(), "native compilation output integrity miss");
                self.fs_status = FsStatus::StaleItem(StaleItem::OutputIntegrity {
                    path: receipt.clone(),
                    reason: error.to_string(),
                });
                return Ok(());
            }
        }

        let pkg_root = pkg.root();
        let mut mtimes = HashMap::default();

        // Get the `mtime` of all outputs. Optionally update their mtime
        // afterwards based on the `mtime_on_use` flag. Afterwards we want the
        // minimum mtime as it's the one we'll be comparing to inputs and
        // dependencies.
        for output in self.outputs.iter() {
            let Ok(mtime) = paths::mtime(output) else {
                // This path failed to report its `mtime`. It probably doesn't
                // exists, so leave ourselves as stale and bail out.
                let item = StaleItem::FailedToReadMetadata {
                    path: output.clone(),
                };
                self.fs_status = FsStatus::StaleItem(item);
                return Ok(());
            };
            assert!(mtimes.insert(output.clone(), mtime).is_none());
        }

        let opt_max = mtimes.iter().max_by_key(|kv| kv.1);
        let Some((max_path, max_mtime)) = opt_max else {
            // We had no output files. This means we're an overridden build
            // script and we're just always up to date because we aren't
            // watching the filesystem.
            self.fs_status = FsStatus::UpToDate { mtimes };
            return Ok(());
        };
        debug!(
            "max output mtime for {:?} is {:?} {}",
            pkg_root, max_path, max_mtime
        );

        // Validate locals ONCE. Only the same parsed+checked native content
        // record may supply coverage for a later dependency timestamp decision.
        // Do not independently parse it for coverage and then validate a possibly
        // replaced record that no longer names the required dependency outputs.
        let locals = self.local.get_mut().unwrap();
        let mut records = locals.iter().filter_map(|local| match local {
            LocalFingerprint::CheckDepInfo { fingerprint, .. } => Some(fingerprint),
            _ => None,
        });
        let content = crate::is_targo_invocation()
            && self.output_receipt.is_some()
            && records.next() == Some(&FingerprintMethod::Content)
            && records.next().is_none();
        let mut content_inputs = content.then(HashMap::default);
        if content {
            // Reject stale children before examining this unit's read-set.
            for dep in &self.deps {
                if !dep.fingerprint.fs_status.up_to_date() {
                    self.fs_status = FsStatus::StaleDepFingerprint {
                        unit: dep.fingerprint.index,
                    };
                    return Ok(());
                }
            }

            for local in locals.iter() {
                if let Some(item) = local.find_stale_item(
                    mtime_cache,
                    checksum_cache,
                    pkg,
                    build_root,
                    ws_root,
                    cargo_exe,
                    gctx,
                    environment,
                    manifest_env_overrides,
                    content_inputs.as_mut(),
                )? {
                    item.log();
                    self.fs_status = FsStatus::StaleItem(item);
                    return Ok(());
                }
            }
        }

        // Newer timestamps alone do not invalidate a dependency edge whose
        // EVERY required output was just checked by content. Missing coverage
        // and legacy/mtime records retain the existing conservative fallback.
        for dep in self.deps.iter() {
            let dep_mtimes = match &dep.fingerprint.fs_status {
                FsStatus::UpToDate { mtimes } => mtimes,
                // If our dependency is stale, so are we, so bail out.
                FsStatus::Stale
                | FsStatus::StaleItem(_)
                | FsStatus::StaleDependency { .. }
                | FsStatus::StaleDepFingerprint { .. } => {
                    self.fs_status = FsStatus::StaleDepFingerprint {
                        unit: dep.fingerprint.index,
                    };
                    return Ok(());
                }
            };

            // If our dependency edge only requires the rmeta file to be present
            // then we only need to look at that one output file, otherwise we
            // need to consider all output files to see if we're out of date.
            let (dep_path, dep_mtime) = if dep.only_requires_rmeta {
                dep_mtimes
                    .iter()
                    .find(|(path, _mtime)| {
                        path.extension().and_then(|s| s.to_str()) == Some("rmeta")
                    })
                    .expect("failed to find rmeta")
            } else {
                match dep_mtimes.iter().max_by_key(|kv| kv.1) {
                    Some(dep_mtime) => dep_mtime,
                    // If our dependencies is up to date and has no filesystem
                    // interactions, then we can move on to the next dependency.
                    None => continue,
                }
            };
            debug!(
                "max dep mtime for {:?} is {:?} {}",
                pkg_root, dep_path, dep_mtime
            );

            // If the dependency is newer than our own output then it was
            // recompiled previously. We transitively become stale ourselves in
            // that case, so bail out.
            //
            // Note that this comparison should probably be `>=`, not `>`, but
            // for a discussion of why it's `>` see the discussion about #5918
            // below in `find_stale`.
            if dep_mtime > max_mtime {
                let required = dep_mtimes.keys().filter(|path| {
                    !dep.only_requires_rmeta || path.extension().is_some_and(|ext| ext == "rmeta")
                });
                if content_inputs.as_ref().is_some_and(|inputs| {
                    let mut observed = false;
                    for path in required {
                        observed = true;
                        if !inputs.contains_key(path) {
                            return false;
                        }
                    }
                    observed
                }) {
                    // The original complete local checks already passed. All
                    // fingerprint, compiler, output and proof gates still apply.
                    debug!(
                        "deferring dependency timestamp to recorded content: {}",
                        dep.name
                    );
                    continue;
                }
                info!(
                    "dependency on `{}` is newer than we are {} > {} {:?}",
                    dep.name, dep_mtime, max_mtime, pkg_root
                );

                self.fs_status = FsStatus::StaleDependency {
                    unit: dep.fingerprint.index,
                    dep_mtime: *dep_mtime,
                    max_mtime: *max_mtime,
                };

                return Ok(());
            }
        }

        // Legacy/mtime modes retain their original local-check ordering.
        if !content {
            for local in self.local.get_mut().unwrap().iter() {
                if let Some(item) = local.find_stale_item(
                    mtime_cache,
                    checksum_cache,
                    pkg,
                    build_root,
                    ws_root,
                    cargo_exe,
                    gctx,
                    environment,
                    manifest_env_overrides,
                    None,
                )? {
                    item.log();
                    self.fs_status = FsStatus::StaleItem(item);
                    return Ok(());
                }
            }
        }

        // Everything was up to date! Record such.
        self.fs_status = FsStatus::UpToDate { mtimes };
        debug!("filesystem up-to-date {:?}", pkg_root);

        Ok(())
    }
}

impl hash::Hash for Fingerprint {
    fn hash<H: Hasher>(&self, h: &mut H) {
        let Fingerprint {
            rustc,
            ref features,
            ref declared_features,
            target,
            path,
            profile,
            ref deps,
            ref local,
            config,
            compile_kind,
            ref rustflags,
            ..
        } = *self;
        let local = local.lock().unwrap();
        (
            rustc,
            features,
            declared_features,
            target,
            path,
            profile,
            &*local,
            config,
            compile_kind,
            rustflags,
        )
            .hash(h);

        h.write_usize(deps.len());
        for DepFingerprint {
            pkg_id,
            name,
            public,
            fingerprint,
            only_requires_rmeta: _, // static property, no need to hash
        } in deps
        {
            pkg_id.hash(h);
            name.hash(h);
            public.hash(h);
            // use memoized dep hashes to avoid exponential blowup
            h.write_u64(fingerprint.hash_u64());
        }
    }
}

impl DepFingerprint {
    fn new(
        build_runner: &mut BuildRunner<'_, '_>,
        parent: &Unit,
        dep: &UnitDep,
    ) -> CargoResult<DepFingerprint> {
        let fingerprint = calculate(build_runner, &dep.unit)?;
        // We need to be careful about what we hash here. We have a goal of
        // supporting renaming a project directory and not rebuilding
        // everything. To do that, however, we need to make sure that the cwd
        // doesn't make its way into any hashes, and one source of that is the
        // `SourceId` for `path` packages.
        //
        // We already have a requirement that `path` packages all have unique
        // names (sort of for this same reason), so if the package source is a
        // `path` then we just hash the name, but otherwise we hash the full
        // id as it won't change when the directory is renamed.
        let pkg_id = if dep.unit.pkg.package_id().source_id().is_path() {
            util::hash_u64(dep.unit.pkg.package_id().name())
        } else {
            util::hash_u64(dep.unit.pkg.package_id())
        };

        Ok(DepFingerprint {
            pkg_id,
            name: dep.extern_crate_name,
            public: dep.public,
            fingerprint,
            only_requires_rmeta: build_runner.only_requires_rmeta(parent, &dep.unit),
        })
    }
}

impl StaleItem {
    /// Use the `log` crate to log a hopefully helpful message in diagnosing
    /// what file is considered stale and why. This is intended to be used in
    /// conjunction with `CARGO_LOG` to determine why Cargo is recompiling
    /// something. Currently there's no user-facing usage of this other than
    /// that.
    fn log(&self) {
        match self {
            StaleItem::DepInfoUnavailable { path, reason } => {
                info!("stale: dependency cache {:?}: {}", path, reason);
            }
            StaleItem::MissingFile { path } => {
                info!("stale: missing {:?}", path);
            }
            StaleItem::UnableToReadFile { path } => {
                info!("stale: unable to read {:?}", path);
            }
            // Trust: this anchor identifies the script; it is not a failed file read.
            StaleItem::BuildScriptInputsUnavailable { output_anchor } => {
                info!(
                    "stale: build-script input observation unavailable or invalid (output anchor {:?})",
                    output_anchor
                );
            }
            StaleItem::OutputIntegrity { path, reason } => {
                info!("stale: cached output integrity at {:?}: {}", path, reason);
            }
            StaleItem::FailedToReadMetadata { path } => {
                info!("stale: couldn't read metadata {:?}", path);
            }
            StaleItem::ChangedFile {
                reference,
                reference_mtime,
                stale,
                stale_mtime,
            } => {
                info!("stale: changed {:?}", stale);
                info!("          (vs) {:?}", reference);
                info!("               {:?} < {:?}", reference_mtime, stale_mtime);
            }
            StaleItem::FileSizeChanged {
                path,
                new_size,
                old_size,
            } => {
                info!("stale: changed {:?}", path);
                info!("prior file size {old_size}");
                info!("  new file size {new_size}");
            }
            StaleItem::ChangedChecksum {
                source,
                stored_checksum,
                new_checksum,
            } => {
                info!("stale: changed {:?}", source);
                info!("prior checksum {stored_checksum}");
                info!("  new checksum {new_checksum}");
            }
            StaleItem::MissingChecksum { path } => {
                info!("stale: no prior checksum {:?}", path);
            }
            StaleItem::ModuleCandidateChanged {
                path,
                previous,
                current,
            } => {
                info!(
                    "stale: Rust module candidate {:?} changed {:?} -> {:?}",
                    path, previous, current
                );
            }
            StaleItem::ChangedEnv {
                var,
                previous,
                current,
            } => {
                info!("stale: changed env {:?}", var);
                info!("       {:?} != {:?}", previous, current);
            }
        }
    }
}

/// Calculates the fingerprint for a [`Unit`].
///
/// This fingerprint is used by Cargo to learn about when information such as:
///
/// * A non-path package changes (changes version, changes revision, etc).
/// * Any dependency changes
/// * The compiler changes
/// * The set of features a package is built with changes
/// * The profile a target is compiled with changes (e.g., opt-level changes)
/// * Any other compiler flags change that will affect the result
///
/// Information like file modification time is only calculated for path
/// dependencies.
#[tracing::instrument(skip_all)]
fn calculate(build_runner: &mut BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<Arc<Fingerprint>> {
    // This function is slammed quite a lot, so the result is memoized.
    if let Some(s) = build_runner.fingerprints.get(unit) {
        return Ok(Arc::clone(s));
    }
    let (mut fingerprint, command_inputs) = if unit.mode.is_run_custom_build() {
        // These units are not currently admitted to confinement. Keep their
        // command/environment preparation if that admission changes later.
        let source_inputs = super::action_inputs::for_unit(build_runner, unit)?;
        let command_inputs =
            super::action_command::for_unit(build_runner, unit, source_inputs.as_deref())?;
        (
            calculate_run_custom_build(build_runner, unit)?,
            command_inputs,
        )
    } else if unit.mode.is_doc_test() {
        panic!("doc tests do not fingerprint");
    } else {
        calculate_normal(build_runner, unit)?
    };

    // After we built the initial `Fingerprint` be sure to update the
    // `fs_status` field of it.
    let build_root = build_root(build_runner, unit);
    let ws_root = build_runner.bcx.ws.root();
    let cargo_exe = build_runner.bcx.gctx.cargo_exe()?;
    let manifest_env_overrides = manifest_env_overrides(build_runner, unit);
    fingerprint.check_filesystem(
        &mut build_runner.mtime_cache,
        &mut build_runner.checksum_cache,
        &unit.pkg,
        &build_root,
        ws_root,
        cargo_exe,
        build_runner.bcx.gctx,
        command_inputs.as_ref().map(|inputs| inputs.environment()),
        manifest_env_overrides.as_ref(),
    )?;

    let fingerprint = Arc::new(fingerprint);
    build_runner
        .fingerprints
        .insert(unit.clone(), Arc::clone(&fingerprint));
    Ok(fingerprint)
}

// Trust: ordinary build-script Work has not executed during planning. Use the
// already parsed original controls bound by the script's planning receipt,
// never a second unchecked stdout read. Dependency dirtiness and final receipt
// validation precede local env comparisons and still force rebuild/refusal.
fn manifest_env_overrides(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> Option<HashMap<String, String>> {
    let mut values = HashMap::default();
    // A build script's output is not an input to its own compilation.
    if unit.target.is_custom_build() {
        return Some(values);
    }
    let Some(scripts) = build_runner.find_build_script_units(unit) else {
        return Some(values);
    };
    let outputs = build_runner.build_script_outputs.lock().unwrap();
    for script in scripts {
        let metadata = build_runner.get_run_build_script_metadata(&script);
        let env = if let Some(output) = outputs.get(metadata) {
            &output.env
        } else {
            let deps = build_runner.build_explicit_deps.get(&script)?;
            if deps.relocation_refused
                || (crate::is_targo_invocation() && deps.cached_receipt.is_none())
            {
                return None;
            }
            deps.manifest_env_overrides.as_ref()?
        };
        // Same script order and exact-name, last-write-wins overlay as the
        // producer's find_build_script_metadatas/add_custom_flags path.
        for (key, value) in env {
            if crate::workspace::manifest::is_tracked_manifest_env(key) {
                values.insert(key.clone(), value.clone());
            }
        }
    }
    Some(values)
}

// Trust: cfg operands are original argv tokens too: rustc expands an @ operand
// before parsing its preceding --cfg/--check-cfg. Inspect only current overrides
// or the same receipt-bound cached controls used for dependency planning.
fn build_script_has_argfile(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> bool {
    // A script's output is not an input to its own compilation.
    if unit.target.is_custom_build() {
        return false;
    }
    let Some(scripts) = build_runner.find_build_script_units(unit) else {
        return false;
    };
    let outputs = build_runner.build_script_outputs.lock().unwrap();
    for script in scripts {
        let metadata = build_runner.get_run_build_script_metadata(&script);
        let has_argfile = if let Some(output) = outputs.get(metadata) {
            output
                .cfgs
                .iter()
                .chain(&output.check_cfgs)
                .any(|arg| arg.starts_with('@'))
        } else {
            build_runner
                .build_explicit_deps
                .get(&script)
                .and_then(BuildDeps::receipt_bound_cfg_args)
                .is_some_and(|args| args.iter().any(|arg| arg.starts_with('@')))
        };
        if has_argfile {
            return true;
        }
    }
    false
}

// Trust: one definition for compiler-fingerprint edges and write-lease closure.
// Runtime-only binaries do not force recompilation; artifact binaries do.
pub(super) fn compilation_dependency_rebuilds(dep: &UnitDep) -> bool {
    !dep.unit.target.is_bin() || dep.unit.artifact.is_true()
}

/// Calculate a fingerprint for a "normal" unit, or anything that's not a build
/// script execution. This includes compiling `build.rs` itself. This is an
/// internal helper of [`calculate`], don't call directly.
fn calculate_normal(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<(
    Fingerprint,
    Option<Arc<super::action_command::CommandInputs>>,
)> {
    let deps = {
        // Recursively calculate the fingerprint for all of our dependencies.
        //
        // Skip fingerprints of binaries because they don't actually induce a
        // recompile, they're just dependencies in the sense that they need to be
        // built. The only exception here are artifact dependencies,
        // which is an actual dependency that needs a recompile.
        //
        // Create Vec since mutable build_runner is needed in closure.
        let deps = Vec::from(build_runner.unit_deps(unit));
        let mut deps = deps
            .into_iter()
            .filter(compilation_dependency_rebuilds)
            .map(|dep| DepFingerprint::new(build_runner, unit, &dep))
            .collect::<CargoResult<Vec<_>>>()?;
        deps.sort_by(|a, b| a.pkg_id.cmp(&b.pkg_id));
        deps
    };

    // Afterwards calculate our own fingerprint information.
    let build_root = build_root(build_runner, unit);
    let is_any_doc_gen = unit.mode.is_doc() || unit.mode.is_doc_scrape();
    let rustdoc_depinfo_enabled = build_runner.bcx.gctx.cli_unstable().rustdoc_depinfo;
    let mut local = if is_any_doc_gen && !rustdoc_depinfo_enabled {
        // rustdoc does not have dep-info files.
        let fingerprint = pkg_fingerprint(build_runner.bcx, &unit.pkg).with_context(|| {
            format!(
                "failed to determine package fingerprint for documenting {}",
                unit.pkg
            )
        })?;
        vec![LocalFingerprint::Precalculated(fingerprint)]
    } else {
        let dep_info = dep_info_loc(build_runner, unit);
        let dep_info = dep_info.strip_prefix(&build_root).unwrap().to_path_buf();
        // rustdoc's independent opt-in remains unchanged: a rustc probe does
        // not establish that a rustdoc launcher supports checksum dep-info.
        let fingerprint = if !is_any_doc_gen {
            build_runner.bcx.source_fingerprint
        } else if build_runner.bcx.gctx.cli_unstable().checksum_freshness {
            build_runner
                .bcx
                .gctx
                .build_config()?
                .fingerprint
                .unwrap_or_default()
        } else {
            FingerprintMethod::Mtime
        };
        vec![LocalFingerprint::CheckDepInfo {
            dep_info,
            fingerprint,
        }]
    };

    // Trust: capture once after dependency planning. Command identity and
    // env-dep validation must consume this same preparation, not independently
    // rescan the source. Lock rechecks and exec boundaries still recapture it.
    let source_inputs = super::action_inputs::for_unit(build_runner, unit)?;
    let command_inputs =
        super::action_command::for_unit(build_runner, unit, source_inputs.as_deref())?;
    if let Some(inputs) = &source_inputs {
        local.push(LocalFingerprint::Precalculated(format!(
            "confined-source-v1:{}",
            inputs.digest()
        )));
    }
    if let Some(inputs) = &command_inputs {
        local.push(LocalFingerprint::Precalculated(format!(
            "confined-command-v1:{}",
            inputs.digest()
        )));
    }
    if build_runner.bcx.shared_dependency_units.contains(unit) {
        let source = unit.pkg.package_id().source_id();
        if source.is_git() {
            let identity =
                super::shared_dependencies::git_source_identity(source).ok_or_else(|| {
                    anyhow::anyhow!("shared Git dependency has no full resolved commit")
                })?;
            local.push(LocalFingerprint::Precalculated(format!(
                "shared-git-source-v1:{identity}"
            )));
        }
        let compiler = build_runner
            .bcx
            .rustc()
            .full_content_identity(false)
            .ok_or_else(|| anyhow::anyhow!("shared dependency has no compiler content identity"))?;
        let directories = build_runner
            .bcx
            .rustc()
            .compiler_inputs()?
            .full_directory_fingerprint();
        let encode = |bytes: [u8; 32]| {
            bytes
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>()
        };
        let platform = build_runner
            .bcx
            .action_platform
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("shared dependency has no platform identity"))?;
        local.push(LocalFingerprint::Precalculated(format!(
            "shared-dependency-v1:{}:{}:{}",
            encode(compiler),
            encode(directories),
            platform.digest()
        )));
    }

    // Figure out what the outputs of our unit is, and we'll be storing them
    // into the fingerprint as well.
    let outputs = build_runner
        .outputs(unit)?
        .iter()
        .filter(|output| !matches!(output.flavor, FileFlavor::DebugInfo | FileFlavor::Auxiliary))
        .map(|output| output.path.clone())
        .collect();

    // Fill out a bunch more information that we'll be tracking typically
    // hashed to take up less space on disk as we just need to know when things
    // change.
    let extra_flags = if unit.mode.is_doc() || unit.mode.is_doc_scrape() {
        &unit.rustdocflags
    } else {
        &unit.rustflags
    };
    // Trust: this vector answers "would recompiling produce a different
    // artifact?". Targo-trust's per-run session nonce and private proof-artifact
    // directory are a transport channel, not compilation semantics: they change
    // on every invocation while the compiler output is byte-identical, so
    // hashing them verbatim marks the entire resolved graph dirty every run and
    // no unit in a verified workspace can ever be reused. Project them out with
    // the same authority that already decides what belongs to a unit's semantic
    // identity (`trust_semantic_compiler_args`, which feeds the `semantics_sha256`
    // Cargo publishes for every proof unit), so freshness and published identity
    // cannot drift apart. Evidence liveness is re-established below, keyed to the
    // units that actually verify. Outside the verified protocol this is the
    // identity function, and `resolve_trust_verification_protocol` below has
    // already rejected a malformed flag vector inside it, so no new failure
    // mode reaches ordinary Cargo.
    let extra_flags = if super::verified_targo_protocol_active() {
        super::trust_semantic_compiler_args(extra_flags).map_err(anyhow::Error::msg)?
    } else {
        extra_flags.to_vec()
    };

    let profile_hash = util::hash_u64((
        &unit.profile,
        unit.mode,
        build_runner.bcx.extra_args_for(unit),
        build_runner.lto[unit],
        unit.pkg.manifest().lint_rustflags(),
        // Trust: use the command's package/scope semantics, not a process-wide
        // workspace label that registry/git dependency commands never receive.
        super::trim_paths::workspace_remap_fingerprint(build_runner, unit),
        // Trust: unlike ordinary compiler units, these doc units have no
        // env-dep records. Keep the existing conservative environment key:
        // their documentation can observe the value even without remap args.
        if is_any_doc_gen && !rustdoc_depinfo_enabled && !unit.profile.trim_paths.is_none() {
            Some(
                build_runner
                    .bcx
                    .gctx
                    .get_env(super::trim_paths::WS_REMAP_ENV)
                    .ok()
                    .filter(|prefix| !prefix.is_empty()),
            )
        } else {
            None
        },
    ));
    // Trust: the proof protocol is resolved here, before the hasher runs,
    // because it decides *whether* the extra scope below participates in the
    // fingerprint at all. Doc units never carry proof authority, so they must
    // keep upstream's fingerprint exactly and stay cacheable across protocols.
    let trust_proof_session = if is_any_doc_gen || !super::verified_targo_protocol_active() {
        None
    } else {
        super::resolve_trust_verification_protocol(
            &unit.rustflags,
            build_runner
                .bcx
                .extra_args_for(unit)
                .map(Vec::as_slice)
                .unwrap_or_default(),
        )
        .map_err(anyhow::Error::msg)?
    };
    let mut config = StableHasher::new();
    if build_runner.bcx.confines(unit) {
        "targo-confined-action-v1".hash(&mut config);
        let platform = build_runner
            .bcx
            .action_platform
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("confined action has no platform identity"))?;
        platform.ensure_current()?;
        platform.digest().hash(&mut config);
        let environment = build_runner
            .bcx
            .action_environment
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("confined action has no captured environment"))?;
        environment.digest().hash(&mut config);
        build_runner
            .bcx
            .rustc()
            .compiler_inputs()?
            .directory_fingerprint()
            .hash(&mut config);
    }
    if crate::is_targo_invocation()
        && !is_any_doc_gen
        && build_runner.bcx.source_fingerprint == FingerprintMethod::Content
    {
        // Trust: v2 also requires producer-reported used-binary checksums.
        // A v1 record can omit a same-path --extern input entirely, so checking
        // its retained files cannot establish this policy. Regenerate it once;
        // unchanged v2 inputs remain reusable.
        "targo-native-content-inputs-v2".hash(&mut config);
    }
    let linker = super::configured_linker(
        &build_runner.compilation,
        unit,
        build_runner.bcx.gctx.target_applies_to_host()?,
    );
    if let Some(linker) = linker {
        linker.hash(&mut config);
    }
    // Trust: preserve the default/legacy identity exactly. Absolute configured
    // tools acquire a full byte snapshot; ambiguous overrides remain valid
    // compiler inputs but cannot publish or reuse native output receipts.
    let configured_linker = if crate::is_targo_invocation() && !is_any_doc_gen {
        let caller_selects_linker = configured_linker::caller_selects_linker(
            unit.profile.rustflags.iter().map(|arg| arg.as_str()).chain(
                build_runner
                    .bcx
                    .extra_args_for(unit)
                    .into_iter()
                    .flatten()
                    .chain(unit.rustflags.iter())
                    .map(String::as_str),
            ),
        );
        configured_linker::Selection::capture(linker, caller_selects_linker)
    } else {
        configured_linker::Selection::default()
    };
    configured_linker.hash_into(&mut config);
    if unit.mode.is_doc() && build_runner.bcx.gctx.cli_unstable().rustdoc_map {
        if let Ok(map) = build_runner.bcx.gctx.doc_extern_map() {
            map.hash(&mut config);
        }
    }
    if let Some(allow_features) = &build_runner.bcx.gctx.cli_unstable().allow_features {
        allow_features.hash(&mut config);
    }
    // -Zpublic-dependency changes how library units pass dependency privacy
    // to rustc via `--extern`.
    (unit.target.is_lib()
        && build_runner.unit_deps(unit).iter().any(|dep| !dep.public)
        && super::is_public_dependency_enabled(build_runner, unit))
    .hash(&mut config);
    // -Zembed-metadata changes how all units are compiled, and it also changes how we tell
    // rustc to link to deps using `--extern`. If it changes, we should rebuild everything.
    build_runner
        .bcx
        .target_data
        .info(unit.kind)
        .should_embed_metadata()
        .not()
        .hash(&mut config);
    if trust_proof_session.is_some() {
        let include_dependencies = super::resolve_trust_include_dependencies(
            &unit.rustflags,
            build_runner
                .bcx
                .extra_args_for(unit)
                .map(Vec::as_slice)
                .unwrap_or_default(),
        )
        .map_err(anyhow::Error::msg)?;
        let is_custom_build = unit.target.is_custom_build();
        let is_primary = super::is_resolved_root_unit(unit, &build_runner.bcx.roots);
        let is_test_execution_subject =
            super::trust_unit_test_execution_subject(build_runner, unit);
        let is_certified_monitor_subject = super::trust_unit_certified_monitor_subject(
            build_runner,
            unit,
            is_test_execution_subject,
        );
        // Trust: match the actual proof frontier, including its non-compiler
        // mode exclusions. RunCustomBuild is not a compiler proof subject.
        let verification_enabled =
            super::trust_proof_unit_role_for_policy(build_runner, unit, include_dependencies)
                .is_some();
        // Trust: reporting metadata, the derived explicit off-switch, and the
        // test-graph verification/monitor decisions are appended after caller
        // rustflags, so upstream's rustflags hash cannot see them; record every
        // decision here instead. The v6 tag includes build-script compilation
        // and all host support units in dependency coverage. It also prevents
        // an uninstrumented harness-free root or cfg(not(test)) execution unit from aliasing the
        // stronger protocol, and must be bumped whenever the tuple changes.
        //
        // The trailing session entry is the evidence-liveness key, and it is the
        // reason the nonce may leave the rustflags hash above. Targo-trust
        // refuses a proof unit whose Cargo artifact reports `fresh=true`: a warm
        // artifact carries no observation that the verifier ran under this
        // session's authority, and replaying a stored verdict for it would be a
        // proof-authority claim nothing here is entitled to make. That
        // requirement is a property of the units that verify, not of the whole
        // graph, so it is recorded on exactly those units. What keeps this
        // correct is that the tuple hashes `verification_enabled` itself. A
        // unit newly included in dependency coverage must rerun and emit this
        // session's evidence; a previous unverified artifact cannot satisfy it.
        (
            "targo-trust-unit-scope-v6",
            super::trust_unit_role(is_custom_build, is_primary),
            unit.pkg.name().as_str(),
            is_test_execution_subject,
            is_certified_monitor_subject,
            verification_enabled,
            verification_enabled
                .then(|| trust_proof_session.as_deref())
                .flatten(),
        )
            .hash(&mut config);
    }

    let compile_kind = unit.kind.fingerprint_hash();
    let mut declared_features = unit.pkg.summary().features().keys().collect::<Vec<_>>();
    declared_features.sort(); // to avoid useless rebuild if the user orders it's features
    // differently
    // Trust: upstream keys on `rustc -vV` alone, which cannot distinguish two
    // trustdoc launchers that report the same version. Documentation units are
    // spawned through a sysroot shim, so the shim's own identity has to be part
    // of the key or a swapped launcher replays as fresh.
    let workspace_compiler = build_runner.bcx.ws.is_member(&unit.pkg);
    let compiler = build_runner
        .bcx
        .rustc()
        .artifact_fingerprint(workspace_compiler)?;
    let rustc = if is_any_doc_gen {
        build_runner
            .verified_rustdoc_launcher
            .as_ref()
            .map_or(compiler, |identity| {
                util::hash_u64((compiler, identity.fingerprint()))
            })
    } else {
        compiler
    };
    let selected_compiler = build_runner.bcx.rustc();
    let compiler_observation = selected_compiler.compiler_inputs().ok().and_then(|_| {
        output_integrity::CompilerObservation::selected(
            rustc,
            configured_linker
                .bind_compiler(selected_compiler.full_content_identity(workspace_compiler)),
            workspace_compiler,
            unit.mode,
            unit.target.is_custom_build(),
        )
    });
    // Trust: compiling a custom-build target produces an executable, just
    // like another binary. Do not confuse that compile unit with the
    // separately handled RunCustomBuild execution and its control output.
    let output_receipt = (crate::is_targo_invocation()
        && matches!(
            unit.mode,
            CompileMode::Build | CompileMode::Check { .. } | CompileMode::Test
        ))
    .then(|| {
        build_runner
            .files()
            .fingerprint_file_path(unit, "outputs-")
            .with_extension("json")
    });
    let output_policy = if output_receipt.is_some() {
        // Trust: match the caller vectors actually appended after Cargo's
        // --emit: profile flags in build_base_args, then extra args and unit
        // flags in prepare_rustc. The verified lane removes its assertion.
        // Documentation and legacy Cargo do not acquire this native policy.
        let compiler_unit_rustflags = if super::verified_targo_protocol_active() {
            super::compiler_flags_without_verification_assertion(&unit.rustflags)
                .map_err(anyhow::Error::msg)?
        } else {
            unit.rustflags.to_vec()
        };
        let selected = output_integrity::OutputPolicy::selected(
            &unit.profile.rustflags,
            build_runner
                .bcx
                .extra_args_for(unit)
                .map(Vec::as_slice)
                .unwrap_or_default(),
            &compiler_unit_rustflags,
        );
        if selected == output_integrity::OutputPolicy::Standard
            && build_script_has_argfile(build_runner, unit)
        {
            output_integrity::OutputPolicy::CallerArgfile
        } else {
            selected
        }
    } else {
        output_integrity::OutputPolicy::Unselected
    };
    // Reuse the public executable selector for binaries/tests; custom-build
    // compilation also produces an executable, while RunCustomBuild does not.
    // Keep the compiler-owned source path, not its subsequently published alias.
    // Caller query/output overrides may intentionally omit the planned output.
    let required_executable = if output_policy == output_integrity::OutputPolicy::Standard
        && (build_runner.get_executable(unit)?.is_some()
            || (unit.target.is_custom_build() && unit.mode.generates_executable()))
    {
        build_runner
            .outputs(unit)?
            .iter()
            .find(|output| output.flavor == FileFlavor::Normal)
            .map(|output| output.path.clone())
    } else {
        None
    };
    let compiler_outputs = if output_receipt.is_some() {
        super::output_observation::expected_outputs(&build_runner.outputs(unit)?)
    } else {
        Vec::new()
    };
    let tool_inputs = tool_inputs::Plan::select(
        build_runner,
        unit,
        &configured_linker,
        output_receipt.is_some(),
    )?;
    let fingerprint = Fingerprint {
        rustc,
        target: util::hash_u64(&unit.target),
        profile: profile_hash,
        // Note that .0 is hashed here, not .1 which is the cwd. That doesn't
        // actually affect the output artifact so there's no need to hash it.
        path: util::hash_u64(path_args(build_runner.bcx.ws, unit).0),
        features: format!("{:?}", unit.features),
        declared_features: format!("{declared_features:?}"),
        deps,
        local: Mutex::new(local),
        memoized_hash: Mutex::new(None),
        config: Hasher::finish(&config),
        compile_kind,
        index: build_runner.bcx.unit_to_index[unit],
        rustflags: extra_flags,
        fs_status: FsStatus::Stale,
        outputs,
        required_executable,
        compiler_observation,
        configured_linker,
        tool_inputs,
        output_policy,
        compiler_outputs,
        output_seal: Mutex::new(None),
        output_receipt,
        script_output: None,
    };
    Ok((fingerprint, command_inputs))
}

/// Calculate a fingerprint for an "execute a build script" unit.  This is an
/// internal helper of [`calculate`], don't call directly.
fn calculate_run_custom_build(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<Fingerprint> {
    assert!(unit.mode.is_run_custom_build());
    // Using the `BuildDeps` information we'll have previously parsed and
    // inserted into `build_explicit_deps` built an initial snapshot of the
    // `LocalFingerprint` list for this build script. If we previously executed
    // the build script this means we'll be watching files and env vars.
    // Otherwise if we haven't previously executed it we'll just start watching
    // the whole crate.
    let (gen_local, overridden, _begin) =
        build_script_local_fingerprints(build_runner, unit, false)?;
    let deps = &build_runner.build_explicit_deps[unit];
    let local = (gen_local)(
        deps,
        Some(&|| {
            const IO_ERR_MESSAGE: &str = "\
An I/O error happened. Please make sure you can access the file.

By default, if your project contains a build script, cargo scans all files in
it to determine whether a rebuild is needed. If you don't expect to access the
file, specify `rerun-if-changed` in your build script.
See https://doc.rust-lang.org/cargo/reference/build-scripts.html#rerun-if-changed for more information.";
            pkg_fingerprint(build_runner.bcx, &unit.pkg).map_err(|err| {
                let mut message = format!("failed to determine package fingerprint for build script for {}", unit.pkg);
                if err.root_cause().is::<io::Error>() {
                    message = format!("{}\n{}", message, IO_ERR_MESSAGE)
                }
                err.context(message)
            })
        }),
        &|message| {
            if let Some(logger) = build_runner.bcx.logger {
                logger.log(message);
            }
        },
    )?
    .unwrap();
    let output = deps.build_script_output.clone();
    let planned_receipt = deps.cached_receipt.clone();

    // Include any dependencies of our execution, which is typically just the
    // compilation of the build script itself. (if the build script changes we
    // should be rerun!). Note though that if we're an overridden build script
    // we have no dependencies so no need to recurse in that case.
    let deps = if overridden {
        // Overridden build scripts don't need to track deps.
        vec![]
    } else {
        // Create Vec since mutable build_runner is needed in closure.
        let deps = Vec::from(build_runner.unit_deps(unit));
        deps.into_iter()
            .map(|dep| DepFingerprint::new(build_runner, unit, &dep))
            .collect::<CargoResult<Vec<_>>>()?
    };

    // Trust: same projection as the compile-unit fingerprint. A build script
    // *execution* is never a proof unit — Targo declares it excluded and strips
    // the whole trust-verify family out of the environment the script sees, so
    // the per-run session and artifact root can have no effect on its output.
    // Left in the hash they would re-run every build script on every verified
    // invocation for a result that cannot differ.
    let rustflags = if super::verified_targo_protocol_active() {
        super::trust_semantic_compiler_args(&unit.rustflags).map_err(anyhow::Error::msg)?
    } else {
        unit.rustflags.to_vec()
    };

    // Trust: mirror the compiler context exposed by custom_build::prepare:
    // only workspace packages receive RUSTC_WORKSPACE_WRAPPER. A workspace
    // wrapper's version must not invalidate an unchanged external script run.
    // Keep the complete scoped observation and propagate unavailable probes.
    let workspace_compiler = build_runner.bcx.ws.is_member(&unit.pkg);
    let rustc = util::hash_u64(
        build_runner
            .bcx
            .rustc()
            .version_observation(workspace_compiler)?
            .verbose_version,
    );

    Ok(Fingerprint {
        local: Mutex::new(local),
        rustc,
        deps,
        outputs: if overridden { Vec::new() } else { vec![output] },
        script_output: (crate::is_targo_invocation() && !overridden).then(|| {
            super::custom_build::cached_output(build_runner, unit).planned(planned_receipt)
        }),
        rustflags,
        index: build_runner.bcx.unit_to_index[unit],

        // Most of the other info is blank here as we don't really include it
        // in the execution of the build script, but... this may be a latent
        // bug in Cargo.
        ..Fingerprint::new()
    })
}

/// Get ready to compute the [`LocalFingerprint`] values
/// for a [`RunCustomBuild`] unit.
///
/// This function has, what's on the surface, a seriously wonky interface.
/// You'll call this function and it'll return a closure and a boolean. The
/// boolean is pretty simple in that it indicates whether the `unit` has been
/// overridden via `.cargo/config.toml`. The closure is much more complicated.
///
/// This closure is intended to capture any local state necessary to compute
/// the `LocalFingerprint` values for this unit. It is `Send` and `'static` to
/// be sent to other threads as well (such as when we're executing build
/// scripts). That deduplication is the rationale for the closure at least.
///
/// The arguments to the closure are a bit weirder, though, and I'll apologize
/// in advance for the weirdness too. The first argument to the closure is a
/// `&BuildDeps`. This is the parsed version of a build script, and when Cargo
/// starts up this is cached from previous runs of a build script.  After a
/// build script executes the output file is reparsed and passed in here.
///
/// The second argument is the weirdest, it's *optionally* a closure to
/// call [`pkg_fingerprint`]. The `pkg_fingerprint` requires access to
/// "source map" located in `Context`. That's very non-`'static` and
/// non-`Send`, so it can't be used on other threads, such as when we invoke
/// this after a build script has finished. The `Option` allows us to for sure
/// calculate it on the main thread at the beginning, and then swallow the bug
/// for now where a worker thread after a build script has finished doesn't
/// have access. Ideally there would be no second argument or it would be more
/// "first class" and not an `Option` but something that can be sent between
/// threads. In any case, it's a bug for now.
///
/// This isn't the greatest of interfaces, and if there's suggestions to
/// improve please do so!
///
/// FIXME(#6779) - see all the words above
///
/// [`RunCustomBuild`]: crate::compiler::CompileMode::RunCustomBuild
fn build_script_local_fingerprints(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    observe_execution: bool,
) -> CargoResult<(
    Box<
        dyn FnOnce(
                &BuildDeps,
                Option<&dyn Fn() -> CargoResult<String>>,
                &dyn Fn(LogMessage),
            ) -> CargoResult<Option<Vec<LocalFingerprint>>>
            + Send,
    >,
    bool,
    Option<Work>,
)> {
    assert!(unit.mode.is_run_custom_build());
    // First up, if this build script is entirely overridden, then we just
    // return the hash of what we overrode it with. This is the easy case!
    if let Some(fingerprint) = build_script_override_fingerprint(build_runner, unit) {
        debug!("override local fingerprints deps {}", unit.pkg);
        return Ok((
            Box::new(
                move |_: &BuildDeps,
                      _: Option<&dyn Fn() -> CargoResult<String>>,
                      _: &dyn Fn(LogMessage)| { Ok(Some(vec![fingerprint])) },
            ),
            true, // this is an overridden build script
            None,
        ));
    }

    // ... Otherwise this is a "real" build script and we need to return a real
    // closure. Our returned closure classifies the build script based on
    // whether it prints `rerun-if-*`. If it *doesn't* print this it's where the
    // magical second argument comes into play, which fingerprints a whole
    // package. Remember that the fact that this is an `Option` is a bug, but a
    // longstanding bug, in Cargo. Recent refactorings just made it painfully
    // obvious.
    let pkg_root = unit.pkg.root().to_path_buf();
    let build_dir = build_root(build_runner, unit);
    let env_config = Arc::clone(build_runner.bcx.gctx.env_config()?);
    // Trust: EW-9 relocation roots, captured for the post-run recomputation.
    let relocation = build_runner
        .bcx
        .gctx
        .cli_unstable()
        .trust_relocation_roots
        .clone();
    let input_work = InputWorkContext {
        index: build_runner.bcx.unit_to_index[unit],
        capture_ids: build_runner
            .bcx
            .logger
            .map(|_| Arc::clone(&build_runner.bcx.input_work_capture_ids)),
    };
    // Trust: preserve Cargo's package include/exclude inventory for old-style
    // scripts; capture it while the source context is available on this thread.
    let content = build_runner.bcx.source_fingerprint == FingerprintMethod::Content;
    let old_deps = &build_runner.build_explicit_deps[unit];
    let old_paths = old_deps
        .rerun_if_changed
        .iter()
        .map(|path| path.strip_prefix(&pkg_root).unwrap_or(path).to_owned())
        .collect::<Vec<_>>();
    let implicit_paths =
        if content && old_paths.is_empty() && old_deps.rerun_if_env_changed.is_empty() {
            crate::sources::path::list_files(&unit.pkg, build_runner.bcx.gctx)
                .ok()
                .map(|entries| {
                    let mut paths = entries
                        .into_iter()
                        .map(|entry| {
                            let path = entry.into_path_buf();
                            path.strip_prefix(&pkg_root).unwrap_or(&path).to_owned()
                        })
                        .collect::<Vec<_>>();
                    paths.sort_unstable();
                    paths.dedup();
                    paths
                })
        } else {
            None
        };
    // Only the admitted script job opens this window. Queued prerequisites
    // can change unrelated ancestors before execution without invalidating it.
    // All original node/change stamps remain checked across the actual action.
    let execution_windows = Arc::new(Mutex::new([None, None]));
    let begin = (observe_execution && content).then(|| {
        let windows = Arc::clone(&execution_windows);
        let root = pkg_root.clone();
        let implicit = implicit_paths.clone();
        let context = input_work.clone();
        Work::new(move |state| {
            let emit = |message| state.input_work(message);
            let report = InputWorkReporter {
                context: &context,
                phase: InputWorkPhase::ExecutionWindow,
                emit: &emit,
            };
            *windows.lock().unwrap() = [
                (!old_paths.is_empty())
                    .then(|| {
                        report.attempt(
                            || build_script_inputs::window_attempt(&root, &old_paths, true),
                            Some,
                        )
                    })
                    .flatten(),
                implicit.as_ref().and_then(|paths| {
                    report.attempt(
                        || build_script_inputs::window_attempt(&root, paths, false),
                        Some,
                    )
                }),
            ];
            Ok(())
        })
    });
    let calculate = move |deps: &BuildDeps,
                          pkg_fingerprint: Option<&dyn Fn() -> CargoResult<String>>,
                          emit: &dyn Fn(LogMessage)| {
        let windows = execution_windows.lock().unwrap();
        let execution_windows = pkg_fingerprint.is_none().then_some(&*windows);
        let report = InputWorkReporter {
            context: &input_work,
            phase: if pkg_fingerprint.is_some() {
                InputWorkPhase::Freshness
            } else {
                InputWorkPhase::Publication
            },
            emit,
        };
        // Trust: EW-9. Output recorded under other relocation roots that cannot
        // be re-rooted is never replayed. No recorded fingerprint is computed
        // from refused output, so this forces the script to run again.
        if deps.relocation_refused {
            return Ok(Some(vec![LocalFingerprint::Precalculated(
                "trust-relocation-roots: cached build-script output cannot be re-rooted".to_owned(),
            )]));
        }
        if deps.rerun_if_changed.is_empty() && deps.rerun_if_env_changed.is_empty() {
            if content {
                let output = deps
                    .build_script_output
                    .strip_prefix(&build_dir)
                    .unwrap()
                    .to_owned();
                let snapshot = implicit_paths.as_ref().and_then(|paths| {
                    content_input_snapshot(&pkg_root, paths, false, execution_windows, &report)
                });
                return Ok(Some(vec![LocalFingerprint::RerunIfChangedContent {
                    output,
                    paths: implicit_paths.clone().unwrap_or_default(),
                    snapshot,
                }]));
            }
            match pkg_fingerprint {
                // FIXME: this is somewhat buggy with respect to docker and
                // weird filesystems. The `Precalculated` variant
                // constructed below will, for `path` dependencies, contain
                // a stringified version of the mtime for the local crate.
                // This violates one of the things we describe in this
                // module's doc comment, never hashing mtimes. We should
                // figure out a better scheme where a package fingerprint
                // may be a string (like for a registry) or a list of files
                // (like for a path dependency). Those list of files would
                // be stored here rather than the mtime of them.
                Some(f) => {
                    let s = f()?;
                    debug!(
                        "old local fingerprints deps {:?} precalculated={:?}",
                        pkg_root, s
                    );
                    return Ok(Some(vec![LocalFingerprint::Precalculated(s)]));
                }
                None => return Ok(None),
            }
        }

        // Ok so now we're in "new mode" where we can have files listed as
        // dependencies as well as env vars listed as dependencies. Process
        // them all here.
        Ok(Some(local_fingerprints_deps(
            deps,
            &build_dir,
            &pkg_root,
            &env_config,
            content,
            execution_windows,
            &report,
            relocation.as_ref(),
        )))
    };

    // Note that `false` == "not overridden"
    Ok((Box::new(calculate), false, begin))
}

/// Create a [`LocalFingerprint`] for an overridden build script.
/// Returns None if it is not overridden.
fn build_script_override_fingerprint(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
) -> Option<LocalFingerprint> {
    // Build script output is only populated at this stage when it is
    // overridden.
    let build_script_outputs = build_runner.build_script_outputs.lock().unwrap();
    let metadata = build_runner.get_run_build_script_metadata(unit);
    // Returns None if it is not overridden.
    let output = build_script_outputs.get(metadata)?;
    let s = format!(
        "overridden build state with hash: {}",
        util::hash_u64(output)
    );
    Some(LocalFingerprint::Precalculated(s))
}

/// Compute the [`LocalFingerprint`] values for a [`RunCustomBuild`] unit for
/// non-overridden new-style build scripts only. This is only used when `deps`
/// is already known to have a nonempty `rerun-if-*` somewhere.
///
/// [`RunCustomBuild`]: crate::compiler::CompileMode::RunCustomBuild
fn local_fingerprints_deps(
    deps: &BuildDeps,
    build_root: &Path,
    pkg_root: &Path,
    env_config: &Arc<HashMap<String, OsString>>,
    content: bool,
    execution_windows: Option<&[Option<build_script_inputs::Window>; 2]>,
    report: &InputWorkReporter<'_>,
    relocation: Option<&RelocationRoots>,
) -> Vec<LocalFingerprint> {
    debug!("new local fingerprints deps {:?}", pkg_root);
    let mut local = Vec::new();

    if !deps.rerun_if_changed.is_empty() {
        // Note that like the module comment above says we are careful to never
        // store an absolute path in `LocalFingerprint`, so ensure that we strip
        // absolute prefixes from them.
        let output = deps
            .build_script_output
            .strip_prefix(build_root)
            .unwrap()
            .to_path_buf();
        let paths: Vec<_> = deps
            .rerun_if_changed
            .iter()
            .map(|p| p.strip_prefix(pkg_root).unwrap_or(p).to_path_buf())
            .collect();
        if content {
            let snapshot =
                content_input_snapshot(pkg_root, &paths, true, execution_windows, report);
            local.push(LocalFingerprint::RerunIfChangedContent {
                output,
                paths,
                snapshot,
            });
        } else {
            // Trust: with `-Ztrust-relocation-roots`, an absolute path outside
            // the package but inside a relocation root is recorded by root
            // token (expanded with the current roots when checked), so a
            // relocated tree watches its own files with an unchanged hash.
            // Content mode keeps its snapshot paths as they are.
            let paths = match relocation {
                Some(roots) => paths
                    .into_iter()
                    .map(|path| roots.record_path(path))
                    .collect(),
                None => paths,
            };
            local.push(LocalFingerprint::RerunIfChanged { output, paths });
        }
    }

    local.extend(
        deps.rerun_if_env_changed
            .iter()
            .map(|s| LocalFingerprint::from_env(s, env_config, relocation)),
    );

    local
}

fn content_input_snapshot(
    root: &Path,
    paths: &[PathBuf],
    recursive: bool,
    execution_windows: Option<&[Option<build_script_inputs::Window>; 2]>,
    report: &InputWorkReporter<'_>,
) -> Option<build_script_inputs::Snapshot> {
    report.attempt(
        || build_script_inputs::observe_attempt(root, paths, recursive),
        |after| {
            if execution_windows.is_some_and(|windows| {
                !windows.iter().flatten().any(|before| before.covers(&after))
            }) {
                input_diagnostics::window_not_covered(
                    report.context.index,
                    report.phase,
                    execution_windows.map_or(0, |windows| windows.iter().flatten().count()),
                );
                return None;
            }
            Some(after.into_snapshot())
        },
    )
}

#[cfg(test)]
mod input_work_producer_tests {
    use super::*;
    use std::cell::RefCell;

    #[test]
    fn input_work_start_precedes_scan_and_finish_follows_coverage() {
        build_script_inputs::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            fs::write(root.join("value"), b"111").unwrap();
            let paths = [PathBuf::from("value")];
            let context = InputWorkContext {
                index: UnitIndex(7),
                capture_ids: Some(Arc::new(AtomicU64::new(0))),
            };
            let messages = RefCell::new(Vec::new());
            let emit = |message| messages.borrow_mut().push(message);
            let report = InputWorkReporter {
                context: &context,
                phase: InputWorkPhase::Freshness,
                emit: &emit,
            };
            assert!(
                report
                    .attempt(
                        || {
                            assert!(matches!(
                                messages.borrow().as_slice(),
                                [LogMessage::InputWorkStarted {
                                    capture: 0,
                                    index: UnitIndex(7),
                                    phase: InputWorkPhase::Freshness,
                                }]
                            ));
                            build_script_inputs::observe_attempt(&root, &paths, true)
                        },
                        Some,
                    )
                    .is_some()
            );
            let before = build_script_inputs::window(&root, &paths, true).unwrap();
            fs::write(root.join("value"), b"222").unwrap();
            let report = InputWorkReporter {
                context: &context,
                phase: InputWorkPhase::Publication,
                emit: &emit,
            };
            assert!(
                content_input_snapshot(&root, &paths, true, Some(&[Some(before), None]), &report)
                    .is_none()
            );
            let messages = messages.borrow();
            assert_eq!(messages.len(), 4);
            assert!(matches!(
                &messages[1],
                LogMessage::InputWorkFinished {
                    capture: 0,
                    index: UnitIndex(7),
                    phase: InputWorkPhase::Freshness,
                    outcome: InputWorkOutcome::Captured,
                    work,
                } if work.bytes_hashed == 3 && work.metadata_reads > 0
            ));
            assert!(matches!(
                &messages[3],
                LogMessage::InputWorkFinished {
                    capture: 1,
                    index: UnitIndex(7),
                    phase: InputWorkPhase::Publication,
                    outcome: InputWorkOutcome::Uncacheable,
                    work,
                } if work.bytes_hashed == 3 && work.metadata_reads > 0
            ));
        })
    }

    #[test]
    fn preflight_refusal_still_has_a_complete_zero_work_pair() {
        build_script_inputs::settled(|world| {
            let context = InputWorkContext {
                index: UnitIndex(3),
                capture_ids: Some(Arc::new(AtomicU64::new(0))),
            };
            let messages = RefCell::new(Vec::new());
            let emit = |message| messages.borrow_mut().push(message);
            let report = InputWorkReporter {
                context: &context,
                phase: InputWorkPhase::ExecutionWindow,
                emit: &emit,
            };
            let paths = vec![PathBuf::from("value"); 16_385];
            assert!(
                report
                    .attempt(
                        || build_script_inputs::window_attempt(world.path(), &paths, true),
                        Some,
                    )
                    .is_none()
            );
            assert!(matches!(
                messages.borrow().as_slice(),
                [
                    LogMessage::InputWorkStarted {
                        capture: 0,
                        index: UnitIndex(3),
                        phase: InputWorkPhase::ExecutionWindow,
                    },
                    LogMessage::InputWorkFinished {
                        capture: 0,
                        index: UnitIndex(3),
                        phase: InputWorkPhase::ExecutionWindow,
                        outcome: InputWorkOutcome::Uncacheable,
                        work,
                    },
                ] if *work == crate::util::log_message::InputWork::default()
            ));
        })
    }

    #[cfg(unix)]
    #[test]
    fn failed_capture_reports_work_completed_before_the_refusal() {
        build_script_inputs::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            fs::write(root.join("value"), b"111").unwrap();
            std::os::unix::fs::symlink("cycle", root.join("cycle")).unwrap();
            let context = InputWorkContext {
                index: UnitIndex(9),
                capture_ids: Some(Arc::new(AtomicU64::new(0))),
            };
            let messages = RefCell::new(Vec::new());
            let emit = |message| messages.borrow_mut().push(message);
            let report = InputWorkReporter {
                context: &context,
                phase: InputWorkPhase::Freshness,
                emit: &emit,
            };
            assert!(
                content_input_snapshot(
                    &root,
                    &[PathBuf::from("value"), PathBuf::from("cycle")],
                    true,
                    None,
                    &report,
                )
                .is_none()
            );
            assert!(matches!(
                &messages.borrow()[1],
                LogMessage::InputWorkFinished {
                    capture: 0,
                    index: UnitIndex(9),
                    phase: InputWorkPhase::Freshness,
                    outcome: InputWorkOutcome::Uncacheable,
                    work,
                } if work.entries == 2 && work.bytes_hashed == 3
                    && work.link_reads == 40 && work.observations > 0
            ));
        })
    }

    #[test]
    fn worker_contexts_share_build_local_ids_without_sharing_the_logger() {
        let ids = Arc::new(AtomicU64::new(0));
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::scope(|scope| {
            for unit in 0..4 {
                let context = InputWorkContext {
                    index: UnitIndex(unit),
                    capture_ids: Some(Arc::clone(&ids)),
                };
                let sender = sender.clone();
                scope.spawn(move || {
                    let emit = |message| sender.send(message).unwrap();
                    let report = InputWorkReporter {
                        context: &context,
                        phase: InputWorkPhase::Publication,
                        emit: &emit,
                    };
                    for _ in 0..16 {
                        assert!(
                            report
                                .attempt(
                                    || build_script_inputs::Attempt {
                                        result: Ok(()),
                                        work: crate::util::log_message::InputWork::default(),
                                    },
                                    Some,
                                )
                                .is_some()
                        );
                    }
                });
            }
        });
        drop(sender);
        let mut pending = std::collections::BTreeMap::new();
        let mut finished = std::collections::BTreeSet::new();
        for message in receiver {
            match message {
                LogMessage::InputWorkStarted { capture, index, .. } => {
                    assert!(pending.insert(capture, index).is_none());
                }
                LogMessage::InputWorkFinished { capture, index, .. } => {
                    assert_eq!(pending.remove(&capture), Some(index));
                    assert!(finished.insert(capture));
                }
                _ => panic!("unexpected input-work message"),
            }
        }
        assert!(pending.is_empty());
        assert_eq!(
            finished.into_iter().collect::<Vec<_>>(),
            (0..64).collect::<Vec<_>>()
        );
    }
}

/// Writes the short fingerprint hash value to `<loc>`
/// and logs detailed JSON information to `<loc>.json`.
fn write_fingerprint(loc: &Path, fingerprint: &Fingerprint) -> CargoResult<()> {
    debug_assert_ne!(fingerprint.rustc, 0);
    // fingerprint::new().rustc == 0, make sure it doesn't make it to the file system.
    // This is mostly so outside tools can reliably find out what rust version this file is for,
    // as we can use the full hash.
    let hash = fingerprint.hash_u64();
    debug!("write fingerprint ({:x}) : {}", hash, loc.display());
    if let Some(executable) = &fingerprint.required_executable {
        super::executable_output::require(executable)?;
    }
    if let Some(receipt) = &fingerprint.output_receipt {
        if let Err(error) = output_integrity::publish(
            receipt,
            hash,
            &fingerprint.outputs,
            fingerprint.compiler_observation.as_ref(),
            fingerprint.output_policy,
            &fingerprint.compiler_outputs,
            fingerprint.output_seal.lock().unwrap().take(),
        ) {
            // Custom --emit modes can intentionally omit Cargo's ordinary
            // outputs. Keep the successful compile, but never manufacture a
            // receipt for outputs we could not capture. A later run is dirty.
            debug!(%error, path = %receipt.display(), "native outputs are not cacheable");
            remove_output_receipt(receipt)?;
        }
    }
    paths::write(loc, util::to_hex(hash).as_bytes())?;

    let json = serde_json::to_string(fingerprint).unwrap();
    if cfg!(debug_assertions) {
        let f: Fingerprint = serde_json::from_str(&json).unwrap();
        assert_eq!(f.hash_u64(), hash);
    }
    paths::write(&loc.with_extension("json"), json.as_bytes())?;
    Ok(())
}

/// Prepare for work when a package starts to build
pub fn prepare_init(build_runner: &mut BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<()> {
    let new1 = build_runner.files().fingerprint_dir(unit);

    // Doc tests have no output, thus no fingerprint.
    if !new1.exists() && !unit.mode.is_doc_test() {
        paths::create_dir_all(&new1)?;
    }

    Ok(())
}

/// Returns the location that the dep-info file will show up at
/// for the [`Unit`] specified.
pub fn dep_info_loc(build_runner: &mut BuildRunner<'_, '_>, unit: &Unit) -> PathBuf {
    build_runner.files().fingerprint_file_path(unit, "dep-")
}

/// Returns an absolute path that build directory.
/// All paths are rewritten to be relative to this.
fn build_root(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> PathBuf {
    build_runner.files().build_root(unit)
}

#[cfg(test)]
mod shared_acceptance_tests {
    use super::*;

    #[test]
    fn matching_short_hash_cannot_replace_the_full_shared_identity() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("fingerprint");
        let mut current = Fingerprint::new();
        current.local = Mutex::new(vec![LocalFingerprint::Precalculated(
            "shared-dependency-v1:current".into(),
        )]);
        current.fs_status = FsStatus::UpToDate {
            mtimes: HashMap::default(),
        };
        let mut other = Fingerprint::new();
        other.local = Mutex::new(vec![LocalFingerprint::Precalculated(
            "shared-dependency-v1:other".into(),
        )]);
        std::fs::write(&path, util::to_hex(current.hash_u64())).unwrap();
        std::fs::write(
            path.with_extension("json"),
            serde_json::to_vec(&other).unwrap(),
        )
        .unwrap();
        assert!(matches!(
            _compare_old_fingerprint(&path, &current).unwrap(),
            FingerprintComparison::Dirty { .. }
        ));
        std::fs::write(
            path.with_extension("json"),
            serde_json::to_vec(&current).unwrap(),
        )
        .unwrap();
        assert!(matches!(
            _compare_old_fingerprint(&path, &current).unwrap(),
            FingerprintComparison::Fresh
        ));
    }
}

/// Reads the value from the old fingerprint hash file and compare.
///
/// If dirty, it then restores the detailed information
/// from the fingerprint JSON file, and provides an rich dirty reason.
fn compare_old_fingerprint(
    unit: &Unit,
    old_hash_path: &Path,
    new_fingerprint: &Fingerprint,
    mtime_on_use: bool,
    forced: bool,
) -> FingerprintComparison {
    if mtime_on_use {
        // update the mtime so other cleaners know we used it
        let t = FileTime::from_system_time(SystemTime::now());
        debug!("mtime-on-use forcing {:?} to {}", old_hash_path, t);
        paths::set_file_time_no_err(old_hash_path, t);
    }

    let compare = _compare_old_fingerprint(old_hash_path, new_fingerprint);

    match compare.as_ref() {
        Ok(FingerprintComparison::Fresh) => {}
        Ok(FingerprintComparison::Dirty { reason }) => {
            info!(
                "fingerprint dirty for {}/{:?}/{:?}",
                unit.pkg, unit.mode, unit.target,
            );
            info!("    dirty: {reason:?}");
        }
        Err(e) => {
            info!(
                "fingerprint error for {}/{:?}/{:?}",
                unit.pkg, unit.mode, unit.target,
            );
            info!("    err: {e:?}");
        }
    }

    match compare {
        Ok(FingerprintComparison::Fresh) if forced => FingerprintComparison::Dirty {
            reason: DirtyReason::Forced,
        },
        Ok(cmp) => cmp,
        Err(_) => FingerprintComparison::Dirty {
            reason: DirtyReason::FreshBuild,
        },
    }
}

/// Graph planning memoizes child filesystem states. Recheck tool facts across
/// that DAG before announcing a parent Fresh; the child may be prepared later.
/// Every current full binding must still match that unit's published receipt,
/// even when a different producer replaced its outputs after graph planning.
/// Shared live handles make repeated checks metadata/access reads, not repeated
/// hashing of every linker through every ancestor.
fn tool_inputs_current(fingerprint: &Fingerprint) -> bool {
    let mut pending = vec![fingerprint];
    let mut seen = HashSet::default();
    while let Some(fingerprint) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(fingerprint)) {
            continue;
        }
        if !fingerprint.configured_linker.current() {
            return false;
        }
        if let Some(receipt) = &fingerprint.output_receipt
            && output_integrity::verify_tool_inputs(
                receipt,
                fingerprint.hash_u64(),
                fingerprint.tool_inputs.expectation(),
            )
            .is_err()
        {
            return false;
        }
        pending.extend(fingerprint.deps.iter().map(|dep| dep.fingerprint.as_ref()));
    }
    true
}

fn _compare_old_fingerprint(
    old_hash_path: &Path,
    new_fingerprint: &Fingerprint,
) -> CargoResult<FingerprintComparison> {
    let new_hash = new_fingerprint.hash_u64();
    let content = new_fingerprint
        .local
        .lock()
        .unwrap()
        .iter()
        .any(|input| matches!(input, LocalFingerprint::RerunIfChangedContent { .. }));
    let old_fingerprint_short = if content {
        match build_script_inputs::read_record(old_hash_path) {
            Ok(record) => record,
            // Trust: preserve first enrollment when the key is actually absent.
            Err(error)
                if error
                    .downcast_ref::<io::Error>()
                    .is_some_and(|error| error.kind() == io::ErrorKind::NotFound) =>
            {
                return Err(error);
            }
            Err(_) => {
                return Ok(FingerprintComparison::Dirty {
                    reason: DirtyReason::ContentFingerprintUnavailable,
                });
            }
        }
    } else {
        paths::read(old_hash_path)?
    };

    if util::to_hex(new_hash) == old_fingerprint_short && new_fingerprint.fs_status.up_to_date() {
        // Trust: calculate() memoizes a planning snapshot across graph work.
        // Re-observe just before Fresh, including the post-producer-lock route.
        if !tool_inputs_current(new_fingerprint) {
            return Ok(FingerprintComparison::Dirty {
                reason: DirtyReason::ContentFingerprintUnavailable,
            });
        }
        let shared = new_fingerprint.local.lock().unwrap().iter().any(|input| {
            matches!(input, LocalFingerprint::Precalculated(value) if value.starts_with("shared-dependency-v1:"))
        });
        if shared {
            // Shared acceptance must compare the full recorded identities,
            // not accept a collision in the legacy 64-bit lookup accelerator.
            let recorded = paths::read(&old_hash_path.with_extension("json"))?;
            if recorded != serde_json::to_string(new_fingerprint)? {
                return Ok(FingerprintComparison::Dirty {
                    reason: DirtyReason::FreshBuild,
                });
            }
        }
        // Trust: the legacy short hash is only an accelerator. Content inputs
        // require the complete bounded persisted representation; old, missing,
        // noncanonical or damaged data is a miss, never a fresh action.
        if content {
            let recorded =
                match build_script_inputs::read_record(&old_hash_path.with_extension("json")) {
                    Ok(recorded) => recorded,
                    Err(_) => {
                        return Ok(FingerprintComparison::Dirty {
                            reason: DirtyReason::ContentFingerprintUnavailable,
                        });
                    }
                };
            if recorded != serde_json::to_string(new_fingerprint)? {
                return Ok(FingerprintComparison::Dirty {
                    reason: DirtyReason::ContentFingerprintChanged,
                });
            }
        }
        return Ok(FingerprintComparison::Fresh);
    }

    // Trust: a mismatched or stale content key is already dirty. Do not parse
    // arbitrary legacy JSON, or assert that damaged persisted bytes match its
    // short hash, merely to improve that miss's diagnostic.
    if content {
        return Ok(FingerprintComparison::Dirty {
            reason: if old_fingerprint_short.is_empty() {
                DirtyReason::FreshBuild
            } else if !new_fingerprint.fs_status.up_to_date() {
                // Trust: report the known current reason without decoding a
                // damaged old JSON record or weakening the cache miss.
                DirtyReason::FsStatusOutdated(new_fingerprint.fs_status.clone())
            } else {
                DirtyReason::ContentFingerprintChanged
            },
        });
    }

    let old_fingerprint_json = paths::read(&old_hash_path.with_extension("json"))?;
    let old_fingerprint: Fingerprint = serde_json::from_str(&old_fingerprint_json)
        .with_context(|| internal("failed to deserialize json"))?;
    // Fingerprint can be empty after a failed rebuild (see comment in prepare_target).
    if !old_fingerprint_short.is_empty()
        && util::to_hex(old_fingerprint.hash_u64()) != old_fingerprint_short
    {
        // Trust: this is persisted input, not an invariant of this process.
        // Another Targo revision can hash the same serialized enum differently;
        // interrupted writes can also leave the two files inconsistent. Neither
        // case licenses reuse or a panic while explaining a cache miss.
        return Ok(FingerprintComparison::Dirty {
            reason: DirtyReason::FingerprintRecordMismatch,
        });
    }

    let reason = new_fingerprint.compare(&old_fingerprint);
    Ok(FingerprintComparison::Dirty { reason })
}

#[cfg(test)]
mod legacy_record_tests {
    use super::*;

    fn current() -> Fingerprint {
        let mut fingerprint = Fingerprint::new();
        fingerprint.rustc = 1;
        fingerprint.local = Mutex::new(vec![LocalFingerprint::RerunIfEnvChanged {
            var: "TRUST_FINGERPRINT_TEST".into(),
            val: None,
        }]);
        fingerprint.fs_status = FsStatus::UpToDate {
            mtimes: HashMap::default(),
        };
        fingerprint
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn configured_linker_is_rechecked_after_fingerprint_memoization() {
        use std::os::unix::fs::PermissionsExt as _;

        build_script_inputs::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let linker = root.join("linker");
            let loc = root.join("fingerprint");
            fs::write(&linker, b"one").unwrap();
            fs::set_permissions(&linker, fs::Permissions::from_mode(0o755)).unwrap();
            assert_eq!(fs::read(&linker).unwrap(), b"one");
            let mut fingerprint = current();
            fingerprint.configured_linker =
                configured_linker::Selection::capture(Some(&linker), false);
            assert!(matches!(
                fingerprint.configured_linker,
                configured_linker::Selection::Captured(_)
            ));
            let key = util::to_hex(fingerprint.hash_u64());
            paths::write(&loc, key.as_bytes()).unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Fresh
            ));
            // The planning key and fs_status remain cached and appear fresh. The
            // final observation must independently reject the changed tool bytes.
            fs::write(&linker, b"two").unwrap();
            assert_eq!(fs::read(&linker).unwrap(), b"two");
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Dirty {
                    reason: DirtyReason::ContentFingerprintUnavailable,
                }
            ));
            let stored = serde_json::to_vec(&fingerprint).unwrap();
            let restored: Fingerprint = serde_json::from_slice(&stored).unwrap();
            // Deserialization cannot recreate this run's selected tool observation.
            assert_eq!(
                restored.configured_linker.bind_compiler(Some([7; 32])),
                Some([7; 32])
            );
        });
    }

    #[test]
    fn stored_fingerprints_cannot_select_an_output_policy() {
        let mut fingerprint = current();
        fingerprint.output_policy = output_integrity::OutputPolicy::Standard;
        let key = fingerprint.hash_u64();
        let standard = serde_json::to_vec(&fingerprint).unwrap();
        let restored: Fingerprint = serde_json::from_slice(&standard).unwrap();
        assert_eq!(
            restored.output_policy,
            output_integrity::OutputPolicy::Unselected
        );
        fingerprint.output_policy = output_integrity::OutputPolicy::CallerEmit;
        assert_eq!(fingerprint.hash_u64(), key);
        assert_eq!(serde_json::to_vec(&fingerprint).unwrap(), standard);
    }

    #[test]
    fn live_output_publication_is_invalidated_then_consumed_once_and_never_serialized() {
        let root = tempfile::tempdir().unwrap();
        let artifact = root.path().join("lib.rmeta");
        let receipt = root.path().join("outputs.json");
        let loc = root.path().join("fingerprint");
        fs::write(&artifact, b"current metadata").unwrap();
        fs::write(&receipt, b"old receipt").unwrap();
        let mut fingerprint = current();
        fingerprint.outputs = vec![artifact.clone()];
        fingerprint.compiler_outputs = vec![(artifact.clone(), Emit::Metadata)];
        fingerprint.output_receipt = Some(receipt.clone());
        fingerprint.output_policy = output_integrity::OutputPolicy::Standard;
        fingerprint.tool_inputs = tool_inputs::Plan::NotRequired;
        fingerprint.compiler_observation = output_integrity::CompilerObservation::selected(
            1,
            Some([7; 32]),
            true,
            CompileMode::Build,
            false,
        );
        let fingerprint = Arc::new(fingerprint);
        let publication = OutputPublication {
            fingerprint: Arc::clone(&fingerprint),
        };
        publication
            .invalidate(&root.path().join("compiler.d"))
            .unwrap();
        assert!(!receipt.exists());
        let mut observer = super::super::output_observation::Observer::new(
            publication.expected(),
            root.path().into(),
        );
        observer.observe(
            &serde_json::json!({
                "$message_type":"artifact", "emit":"metadata", "artifact":artifact,
            })
            .to_string(),
        );
        let execution = publication.begin(&ProcessBuilder::new("trustc"));
        publication.complete(observer.finish(), Some(execution));
        let restored: Fingerprint =
            serde_json::from_slice(&serde_json::to_vec(&*fingerprint).unwrap()).unwrap();
        assert!(restored.output_seal.lock().unwrap().is_none());
        assert!(restored.compiler_outputs.is_empty());
        assert_eq!(
            restored.tool_inputs.expectation(),
            output_integrity::ToolInputExpectation::Unavailable
        );
        write_fingerprint(&loc, &fingerprint).unwrap();
        assert!(receipt.exists());
        assert!(fingerprint.output_seal.lock().unwrap().is_none());
        write_fingerprint(&loc, &fingerprint).unwrap();
        assert!(
            !receipt.exists(),
            "the same live attempt cannot publish twice"
        );
    }

    #[test]
    fn incompatible_or_interrupted_record_is_a_cache_miss() {
        build_script_inputs::settled(|world| {
            let path = world.path().join("fingerprint");
            let fingerprint = current();
            fs::write(
                path.with_extension("json"),
                serde_json::to_vec(&fingerprint).unwrap(),
            )
            .unwrap();
            // Reproduce the seed/current-Targo mismatch without depending on a
            // particular Hash implementation or enum ordinal in the test itself.
            fs::write(&path, util::to_hex(fingerprint.hash_u64() ^ 1)).unwrap();
            let FingerprintComparison::Dirty { reason } =
                _compare_old_fingerprint(&path, &fingerprint).unwrap()
            else {
                panic!("inconsistent persisted record must not be reused")
            };
            assert!(matches!(reason, DirtyReason::FingerprintRecordMismatch));
            assert!(!reason.is_fresh_build());
        })
    }

    #[test]
    fn compatible_records_keep_fresh_reuse_and_precise_changes() {
        build_script_inputs::settled(|world| {
            let path = world.path().join("fingerprint");
            let fingerprint = current();
            fs::write(&path, util::to_hex(fingerprint.hash_u64())).unwrap();
            fs::write(
                path.with_extension("json"),
                serde_json::to_vec(&fingerprint).unwrap(),
            )
            .unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&path, &fingerprint).unwrap(),
                FingerprintComparison::Fresh
            ));
            let mut changed = current();
            changed.rustc = 2;
            assert!(matches!(
                _compare_old_fingerprint(&path, &changed).unwrap(),
                FingerprintComparison::Dirty {
                    reason: DirtyReason::RustcChanged
                }
            ));
        })
    }
}

#[cfg(test)]
mod build_script_content_record_tests {
    use super::*;

    // Trust: exercise the actual freshness branch with a real readable output,
    // and retain invalid/absent observation refusal independently of that file.
    #[test]
    fn unavailable_input_observation_does_not_report_readable_stdout_as_unreadable() {
        build_script_inputs::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            fs::write(root.join("input.rs"), "pub fn input() {}\n").unwrap();
            fs::write(
                root.join("Cargo.toml"),
                "[package]\nname='input-observation-fixture'\nversion='0.1.0'\n[lib]\npath='input.rs'\n[workspace]\n",
            )
            .unwrap();
            fs::create_dir(root.join("run")).unwrap();
            let output = PathBuf::from("run/stdout");
            let output_anchor = root.join(&output);
            fs::write(&output_anchor, "cargo:rerun-if-changed=input.rs\n").unwrap();
            let snapshot =
                build_script_inputs::capture(&root, &[PathBuf::from("input.rs")], true).unwrap();
            let mut invalid = serde_json::to_value(&snapshot).unwrap();
            invalid["version"] = serde_json::json!(0);
            let invalid = serde_json::from_value(invalid).unwrap();
            let mut context = GlobalContext::new(
                cargo_util_terminal::Shell::from_write(Box::new(Vec::<u8>::new())),
                root.clone(),
                root.join("cargo-home"),
            );
            context.set_env(Default::default());
            context.set_search_stop_path(&root);
            context
                .configure(0, false, None, false, false, true, &None, &[], &[])
                .unwrap();
            let workspace =
                crate::workspace::Workspace::new(&root.join("Cargo.toml"), &context).unwrap();
            let package = workspace.current().unwrap();
            let cargo_exe = Path::new(env!("CARGO"));
            for observation in [None, Some(invalid), Some(snapshot)] {
                let available = observation
                    .as_ref()
                    .is_some_and(|snapshot| snapshot.valid());
                let local = LocalFingerprint::RerunIfChangedContent {
                    output: output.clone(),
                    paths: vec![PathBuf::from("input.rs")],
                    snapshot: observation,
                };
                let stale = local
                    .find_stale_item(
                        &mut HashMap::default(),
                        &mut HashMap::default(),
                        package,
                        &root,
                        &root,
                        cargo_exe,
                        &context,
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                if available {
                    assert!(stale.is_none());
                } else {
                    assert!(matches!(
                        stale,
                        Some(StaleItem::BuildScriptInputsUnavailable { output_anchor: actual })
                            if actual == output_anchor
                    ));
                }
                assert_eq!(
                    fs::read_to_string(&output_anchor).unwrap(),
                    "cargo:rerun-if-changed=input.rs\n"
                );
            }
        });
    }

    fn current_content(root: &Path) -> Fingerprint {
        fs::write(root.join("schema"), b"value").unwrap();
        let snapshot =
            build_script_inputs::capture(root, &[PathBuf::from("schema")], true).unwrap();
        let mut fingerprint = Fingerprint::new();
        fingerprint.rustc = 1;
        fingerprint.fs_status = FsStatus::UpToDate {
            mtimes: HashMap::default(),
        };
        fingerprint.local = Mutex::new(vec![LocalFingerprint::RerunIfChangedContent {
            output: PathBuf::from("output"),
            paths: vec![PathBuf::from("schema")],
            snapshot: Some(snapshot),
        }]);
        fingerprint
    }

    #[test]
    fn known_stale_content_retains_its_current_reason_without_decoding_old_json() {
        build_script_inputs::settled(|world| {
            let loc = world.path().join("fingerprint");
            let mut fingerprint = current_content(world.path());
            if let LocalFingerprint::RerunIfChangedContent { snapshot, .. } =
                &mut fingerprint.local.get_mut().unwrap()[0]
            {
                *snapshot = None;
            }
            fingerprint.fs_status = FsStatus::StaleItem(StaleItem::BuildScriptInputsUnavailable {
                output_anchor: PathBuf::from("output"),
            });
            fs::write(&loc, util::to_hex(fingerprint.hash_u64())).unwrap();
            fs::write(loc.with_extension("json"), b"not JSON").unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Dirty {
                    reason: DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
                        StaleItem::BuildScriptInputsUnavailable { output_anchor }
                    )),
                } if output_anchor == Path::new("output")
            ));
        })
    }

    #[test]
    fn existing_content_misses_are_distinct_from_missing_or_empty_enrollment() {
        build_script_inputs::settled(|world| {
            let loc = world.path().join("fingerprint");
            let fingerprint = current_content(world.path());
            // No mismatched-key diagnostic may parse this damaged legacy record.
            fs::write(&loc, "malformed nonempty key").unwrap();
            fs::write(loc.with_extension("json"), b"not JSON").unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Dirty {
                    reason: DirtyReason::ContentFingerprintChanged
                }
            ));
            fs::write(&loc, util::to_hex(fingerprint.hash_u64())).unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Dirty {
                    reason: DirtyReason::ContentFingerprintChanged
                }
            ));
            fs::remove_file(loc.with_extension("json")).unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Dirty {
                    reason: DirtyReason::ContentFingerprintUnavailable
                }
            ));
            fs::write(&loc, b"").unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Dirty {
                    reason: DirtyReason::FreshBuild
                }
            ));
            fs::remove_file(&loc).unwrap();
            assert!(_compare_old_fingerprint(&loc, &fingerprint).is_err());
            fs::create_dir(&loc).unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Dirty {
                    reason: DirtyReason::ContentFingerprintUnavailable
                }
            ));
        })
    }

    #[test]
    fn malformed_or_old_content_record_cannot_use_a_matching_short_hash() {
        build_script_inputs::settled(|world| {
            let loc = world.path().join("fingerprint");
            fs::write(world.path().join("schema"), b"value").unwrap();
            let snapshot =
                build_script_inputs::capture(world.path(), &[PathBuf::from("schema")], true)
                    .unwrap();
            let mut fingerprint = Fingerprint::new();
            fingerprint.rustc = 1;
            fingerprint.fs_status = FsStatus::UpToDate {
                mtimes: HashMap::default(),
            };
            fingerprint.local = Mutex::new(vec![LocalFingerprint::RerunIfChangedContent {
                output: PathBuf::from("output"),
                paths: vec![PathBuf::from("schema")],
                snapshot: Some(snapshot),
            }]);
            fs::write(&loc, util::to_hex(fingerprint.hash_u64())).unwrap();
            let json = serde_json::to_vec(&fingerprint).unwrap();
            fs::write(loc.with_extension("json"), &json).unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Fresh
            ));
            for damaged in [b"{}".as_slice(), b"not JSON".as_slice(), b"".as_slice()] {
                fs::write(loc.with_extension("json"), damaged).unwrap();
                assert!(!matches!(
                    _compare_old_fingerprint(&loc, &fingerprint),
                    Ok(FingerprintComparison::Fresh)
                ));
            }
            let old = String::from_utf8(json)
                .unwrap()
                .replace("\"version\":1", "\"version\":0");
            fs::write(loc.with_extension("json"), old).unwrap();
            assert!(!matches!(
                _compare_old_fingerprint(&loc, &fingerprint),
                Ok(FingerprintComparison::Fresh)
            ));
            fs::write(&loc, "mismatched short hash").unwrap();
            fs::write(loc.with_extension("json"), "not JSON").unwrap();
            assert!(matches!(
                _compare_old_fingerprint(&loc, &fingerprint).unwrap(),
                FingerprintComparison::Dirty { .. }
            ));
        })
    }
}

/// Calculates the fingerprint of a unit thats contains no dep-info files.
fn pkg_fingerprint(bcx: &BuildContext<'_, '_>, pkg: &Package) -> CargoResult<String> {
    let sources = bcx.packages.sources();

    let source = sources
        .package_source(pkg.package_id())
        .ok_or_else(|| internal("missing package source"))?;
    source.fingerprint(pkg)
}

/// The `reference` file is considered as "stale" if any file from `paths` has a newer mtime.
///
/// Trust: `carried` is a seeded build directory's table of carried times
/// (`-Ztrust-carried-times`, EW-9); it changes only the times of inputs, never
/// the reference's.
fn find_stale_file<I, P>(
    mtime_cache: &mut HashMap<PathBuf, FileTime>,
    checksum_cache: &mut HashMap<PathBuf, Checksum>,
    reference: &Path,
    paths: I,
    fingerprint: FingerprintMethod,
    carried: Option<&CarriedTimes>,
) -> Option<StaleItem>
where
    I: IntoIterator<Item = (P, Option<(u64, Checksum)>)>,
    P: AsRef<Path>,
{
    let reference_mtime = match paths::mtime(reference) {
        Ok(mtime) => mtime,
        Err(..) => {
            return Some(StaleItem::MissingFile {
                path: reference.to_path_buf(),
            });
        }
    };

    let skippable_dirs =
        if fingerprint == FingerprintMethod::Content && crate::is_targo_invocation() {
            // Native content validation must cover dependency sources as well as
            // workspace sources. Restore/mtime shortcuts cannot establish bytes.
            None
        } else if let Ok(cargo_home) = home::cargo_home() {
            let skippable_dirs: Vec<_> = ["git", "registry"]
                .into_iter()
                .map(|subfolder| cargo_home.join(subfolder))
                .collect();
            Some(skippable_dirs)
        } else {
            None
        };
    for (path, prior_checksum) in paths {
        let path = path.as_ref();

        // Assuming anything in cargo_home/{git, registry} is immutable
        // (see also #9455 about marking the src directory readonly) which avoids rebuilds when CI
        // caches $CARGO_HOME/registry/{index, cache} and $CARGO_HOME/git/db across runs, keeping
        // the content the same but changing the mtime.
        if let Some(ref skippable_dirs) = skippable_dirs {
            if skippable_dirs.iter().any(|dir| path.starts_with(dir)) {
                continue;
            }
        }
        match fingerprint {
            FingerprintMethod::Content => {
                let Some((file_len, prior_checksum)) = prior_checksum else {
                    return Some(StaleItem::MissingChecksum {
                        path: path.to_path_buf(),
                    });
                };
                let path_buf = path.to_path_buf();

                let path_checksum = match checksum_cache.entry(path_buf) {
                    Entry::Occupied(o) => *o.get(),
                    Entry::Vacant(v) => {
                        let Ok(current_file_len) = fs::metadata(&path).map(|m| m.len()) else {
                            return Some(StaleItem::FailedToReadMetadata {
                                path: path.to_path_buf(),
                            });
                        };
                        if current_file_len != file_len {
                            return Some(StaleItem::FileSizeChanged {
                                path: path.to_path_buf(),
                                new_size: current_file_len,
                                old_size: file_len,
                            });
                        }
                        let Ok(file) = File::open(path) else {
                            return Some(StaleItem::MissingFile {
                                path: path.to_path_buf(),
                            });
                        };
                        let Ok(checksum) = Checksum::compute(prior_checksum.algo(), file) else {
                            return Some(StaleItem::UnableToReadFile {
                                path: path.to_path_buf(),
                            });
                        };
                        *v.insert(checksum)
                    }
                };
                if path_checksum == prior_checksum {
                    continue;
                }
                return Some(StaleItem::ChangedChecksum {
                    source: path.to_path_buf(),
                    stored_checksum: prior_checksum,
                    new_checksum: path_checksum,
                });
            }
            FingerprintMethod::Mtime => {
                let path_mtime = match mtime_cache.entry(path.to_path_buf()) {
                    Entry::Occupied(o) => *o.get(),
                    Entry::Vacant(v) => {
                        let mtime = match carried {
                            Some(carried) => {
                                paths::mtime_recursive_by(path, |meta| carried.mtime(meta))
                            }
                            None => paths::mtime_recursive(path),
                        };
                        let Ok(mtime) = mtime else {
                            return Some(StaleItem::MissingFile {
                                path: path.to_path_buf(),
                            });
                        };
                        *v.insert(mtime)
                    }
                };

                // TODO: fix #5918.
                // Note that equal mtimes should be considered "stale". For filesystems with
                // not much timestamp precision like 1s this is would be a conservative approximation
                // to handle the case where a file is modified within the same second after
                // a build starts. We want to make sure that incremental rebuilds pick that up!
                //
                // For filesystems with nanosecond precision it's been seen in the wild that
                // its "nanosecond precision" isn't really nanosecond-accurate. It turns out that
                // kernels may cache the current time so files created at different times actually
                // list the same nanosecond precision. Some digging on #5919 picked up that the
                // kernel caches the current time between timer ticks, which could mean that if
                // a file is updated at most 10ms after a build starts then Cargo may not
                // pick up the build changes.
                //
                // All in all, an equality check here would be a conservative assumption that,
                // if equal, files were changed just after a previous build finished.
                // Unfortunately this became problematic when (in #6484) cargo switch to more accurately
                // measuring the start time of builds.
                if path_mtime <= reference_mtime {
                    continue;
                }

                return Some(StaleItem::ChangedFile {
                    reference: reference.to_path_buf(),
                    reference_mtime,
                    stale: path.to_path_buf(),
                    stale_mtime: path_mtime,
                });
            }
        }
    }

    debug!(
        "all paths up-to-date relative to {:?} mtime={}",
        reference, reference_mtime
    );
    None
}
