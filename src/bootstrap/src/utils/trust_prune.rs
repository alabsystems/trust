//! Trust: bootstrap prunes the superseded cargo units and the duplicate objects of its own
//! build trees after every successful run (the Continuum's native prune, 2026-11-06).
//!
//! **Why.** A change to a unit's compiler, flags or dependencies gives it a new unit id and
//! leaves its old *variant* in bootstrap's cargo target trees for good. On 2026-11-05
//! `scripts/slim_build.py --dead-variants --rlib-objects --dry-run` found 162.8 GiB of dead
//! variants and 80.8 GiB of loose `.rcgu.o` objects in m8's main checkout, and that script
//! reclaims only when a person runs it. Bootstrap owns these trees, holds `build/lock` for
//! the whole run and writes the stamps that are the prune's roots, so it prunes them
//! itself once a run has succeeded ([`after_success`], one call in `cli_main.rs`).
//!
//! **The rules** are EW18-PRUNE-1's, ported exactly from `slim_build.py`'s "Pruning a warm
//! tree" (its docstring and `docs/DECISION_QUEUE.md`, EW18-PRUNE-1, have the measurements):
//! * *Roots* ([`find_roots`]): every unit a bootstrap stamp names, every unit an uplifted
//!   dep-info names, and the unit an uplifted artifact is (a hard link of its output, or,
//!   since cargo clones on macOS, its output of the same name and the same bytes). Here,
//!   also every unit this run's cargo reported ([`note_cargo_message`]: each artifact of a
//!   `stream_cargo` run, fresh or compiled, and the unit of each build script it ran), as a
//!   root written the moment it reported it. A reported path that names no unit id (an
//!   uplift) names the unit it is when the prune runs, so a variant that another cargo of
//!   the same run uplifted over it loses that root, as slim's uplift rule treats it: it is
//!   rebuilt when next wanted. `cargo test` runs (`test.rs`) do not stream, so their units
//!   keep only the protection of the ported rules.
//! * *Edges*: a live unit's own dep-info and its fingerprint's `deps` hashes.
//! * *Built against*: a unit no variant of which is live, all of whose fingerprint
//!   dependencies are live, is live, with its own build time as its only evidence.
//! * *Variants* ([`judge_units`]): one target (package and hash-file kind) in one mode
//!   (check or build) in one profile directory with one fingerprint identity (its JSON's
//!   `path`, `target`, `features`, `profile`, `compile_kind`). A unit whose identity cannot
//!   be read is a variant of nothing; a build-script run dies only with its build script.
//! * *Death only on evidence*: a unit nothing reaches is dead when it never finished, or
//!   a live variant is named by a root written after it was built, or a kept variant was
//!   built after it. The newest finished variant of a target built after every root that
//!   names another is kept, with what it uses.
//! * *Fingerprint first* ([`remove_units`]): each dead unit loses its fingerprint before
//!   anything else, and keeps the rest when its fingerprint does not go.
//! * *Duplicate objects* ([`duplicate_objects`]), on Darwin only: a loose Mach-O object
//!   that its unit's rlib holds as a member of the same name and size. Bootstrap passes
//!   `-Ztrust-drop-rlib-objects` to no compiler (EW18-DROPIN-1), so every unit compiled
//!   with debuginfo keeps writing them, in every tree.
//!
//! Every tree slim's `target_trees` names is judged ([`target_trees`]), not only the trees
//! this run built in, and each tree on its own ([`prune`]).
//!
//! **What is refused** (the tree is left as it is, with a warning): a cargo lock in any of
//! its profile directories that is held, is a link or not a regular file, or cannot be
//! taken (every lock is held while the tree is judged and pruned, so a cargo that starts
//! meanwhile waits); a stamp that cannot be read or is not a regular file, a directory of
//! the tree that cannot be listed or a fingerprint file that cannot be read; a tree that
//! resolves outside the build directory; a plan that would delete a path any stamp of any
//! tree names, compared by device and inode with every record and each directory above
//! it ([`stamped_in_plan`]), so a stamp that cannot be read in any tree refuses every
//! tree with something to delete; a plan path outside its tree; and a sysroot or
//! installed-tool link into a planned path.
//!
//! **What replaces slim's machine-wide process scan.** The prune runs inside bootstrap
//! after `Session::build` returned, holding `build/lock` (every other bootstrap of this
//! build directory waits) under its original native build-tree lease. The caller lends
//! the actual command/repository lease and output guard, checked before and after pruning.
//! A token or holder record never constructs ownership. Withheld or failed command
//! ownership refuses cleanup because native consumers may still be alive. This run's own
//! cargo and test runs are over. The residual, recorded in
//! `docs/DECISION_QUEUE.md` (NATIVE-PRUNE-1): a cargo or a test binary run *outside* x.py
//! against a bootstrap tree. A cargo that builds holds its lock and the tree is skipped,
//! but cargo drops its locks while `cargo test` runs what it built, and a test binary run
//! by hand holds none.
//!
//! **Cost.** After judging a tree the prune writes one stamp in it ([`STAMP`]): a digest
//! of its profile directories' `.fingerprint`, `deps`, `build` and `examples` directories,
//! the bytes of its stamps and uplifted dep-info, and the size and time of its other
//! uplifted files ([`tree_digest`]). A tree whose digest is unchanged, and in which this
//! run compiled nothing, costs that digest: a few stats and those files' bytes. The first
//! run on a tree clears its backlog. Skipping is never a deletion: what a later root would
//! supersede in an unchanged tree waits for its next change. Each run prints the units,
//! GiB and seconds; a failure warns and leaves the tree, and the build's result never
//! changes. `rust.trust-prune-superseded = false` turns it off.
//!
//! **The interface** is bootstrap-free: [`target_trees`] and [`profile_dirs`] take paths,
//! [`plan_tree`] takes a tree, its profile directories and the extra roots and returns a
//! [`Plan`], so Targo's target cleaning (targo-core `workspace/gc.rs`) can later reuse the
//! judge rather than duplicate it. Only [`after_success`] and [`note_cargo_message`] know
//! bootstrap.
//!
//! Decisions and what remains: `docs/DECISION_QUEUE.md`, NATIVE-PRUNE-1.

#![cfg(unix)]

use std::collections::{BTreeSet, HashMap, HashSet};
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{self, Read, Seek, SeekFrom};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::panic::AssertUnwindSafe;
use std::path::{Component, Path, PathBuf};
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use sha2::Digest;

use crate::core::build_steps::compile::CargoMessage;
use crate::core::builder::Kind;
use crate::core::config::Config;

pub(crate) mod space;

/// The stamp a judged tree carries at its root: [`STAMP_SCHEMA`], then the digest of what
/// the judgment read ([`tree_digest`]). It names no path, so a seed's audit of a cloned
/// tree (`utils::trust_stage1_seed`) finds nothing in it, and its inode numbers never
/// match in a clone, which is judged afresh.
pub(crate) const STAMP: &str = ".trust-prune";
const STAMP_SCHEMA: &str = "trust-prune/v1";
/// What a cargo running in a profile directory holds, in every layout cargo has used.
pub(crate) const CARGO_LOCKS: [&str; 3] =
    [".cargo-lock", ".cargo-build-lock", ".cargo-artifact-lock"];
/// Installed tool binaries beside the sysroots: kept, and checked for links into a plan.
const INSTALLED_TOOLS: [&str; 3] = ["stage1-tools-bin", "stage2-tools-bin", "stage3-tools-bin"];
/// Never pruned: these are not cargo target trees (sysroots, the seed, LLVM, installed
/// tools). Every other directory that carries cargo's target-directory marker is one.
const PRUNE_NEVER: [&str; 8] = [
    "stage0",
    "stage0-sysroot",
    "stage1",
    "stage2",
    "llvm",
    "stage1-tools-bin",
    "stage2-tools-bin",
    "stage3-tools-bin",
];
/// A tree `slim_build.py` renamed aside for deletion.
const RECLAIM_TAG: &str = ".slim-reclaim-";
const LINKED_OUTPUTS: [&str; 6] = [".dylib", ".so", ".dll", ".a", ".lib", ".wasm"];
/// A thin Mach-O object's first four bytes, in either byte order and word size.
const MACHO_MAGIC: [[u8; 4]; 4] = [
    [0xcf, 0xfa, 0xed, 0xfe],
    [0xce, 0xfa, 0xed, 0xfe],
    [0xfe, 0xed, 0xfa, 0xcf],
    [0xfe, 0xed, 0xfa, 0xce],
];

// --------------------------------------------------------------------------------------
// Bootstrap: this run's cargo reports, and the call after a successful run.
// --------------------------------------------------------------------------------------

/// What this run's cargo reported: an artifact path (`compiled` when cargo did not find
/// its unit fresh), or the `OUT_DIR` of a build script it ran, and when (ns since the
/// epoch). Each roots the unit it names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Streamed {
    pub(crate) path: PathBuf,
    pub(crate) when: i128,
    pub(crate) compiled: bool,
    pub(crate) ran: bool,
}

static STREAMED: Mutex<Vec<Streamed>> = Mutex::new(Vec::new());

/// Records what one cargo JSON message of this run names (`compile::stream_cargo`).
pub(crate) fn note_cargo_message(message: &CargoMessage<'_>) {
    let when = now();
    let found: Vec<Streamed> = match message {
        CargoMessage::CompilerArtifact { filenames, fresh, .. } => filenames
            .iter()
            .map(|name| Streamed {
                path: PathBuf::from(name.as_ref()),
                when,
                compiled: !fresh,
                ran: false,
            })
            .collect(),
        CargoMessage::BuildScriptExecuted { out_dir: Some(dir) } => {
            vec![Streamed { path: PathBuf::from(dir.as_ref()), when, compiled: false, ran: true }]
        }
        _ => return,
    };
    if let Ok(mut streamed) = STREAMED.lock() {
        streamed.extend(found);
    }
}

fn take_streamed() -> Vec<Streamed> {
    STREAMED.lock().map(|mut streamed| std::mem::take(&mut *streamed)).unwrap_or_default()
}

/// Prunes after successful protected work; cleanup failures never change the build result.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn after_success(config: &Config, ownership: Option<Ownership<'_>>) {
    if gate(
        config.trust_prune_superseded,
        config.dry_run(),
        config.bypass_bootstrap_lock,
        config.cmd.kind(),
    ) == Gate::Off
    {
        return;
    }
    let streamed = take_streamed();
    let host_dir = config.out.join(&*config.host_target.triple);
    let options = Options { objects: cfg!(target_os = "macos"), observe: None };
    let verbose = config.exec_ctx().is_verbose();
    match std::panic::catch_unwind(AssertUnwindSafe(|| {
        prune_owned(&config.src, &config.out, &host_dir, &streamed, &options, ownership)
    })) {
        Ok(Ok(summary)) => summary.print(verbose),
        Ok(Err(error)) => eprintln!("WARNING: prune: {error}; the build's result stands"),
        Err(_) => eprintln!(
            "WARNING: prune: it panicked; completed removals stand and the build's result stands"
        ),
    }
}

/// Configuration selects cleanup; only actual ownership permits execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Gate {
    Off,
    Prune,
}

pub(crate) fn gate(enabled: bool, dry_run: bool, bypass_bootstrap_lock: bool, kind: Kind) -> Gate {
    if !enabled
        || dry_run
        || bypass_bootstrap_lock
        || matches!(kind, Kind::Clean | Kind::Setup | Kind::Format | Kind::Vendor)
    {
        Gate::Off
    } else {
        Gate::Prune
    }
}

/// Borrows the invocation's actual guards. No token, PID or saved record can
/// construct one, and neither guard can be released while this borrow lives.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) struct Ownership<'a> {
    output: &'a build_helper::trust_output_lock::OutputLock,
    tree: TreeLease<'a>,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
enum TreeLease<'a> {
    Repository(&'a crate::utils::trust_repo_lock::BuildLease),
    Command(&'a crate::core::build_steps::frontend_runtime::CommandOwnership),
    Native(&'a build_helper::trust_repo_lock::management::Lease),
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
impl<'a> Ownership<'a> {
    pub(crate) fn native(
        output: &'a build_helper::trust_output_lock::OutputLock,
        tree: &'a build_helper::trust_repo_lock::management::Lease,
    ) -> Self {
        Self { output, tree: TreeLease::Native(tree) }
    }

    pub(crate) fn repository(
        output: &'a build_helper::trust_output_lock::OutputLock,
        tree: &'a crate::utils::trust_repo_lock::BuildLease,
    ) -> Self {
        Self { output, tree: TreeLease::Repository(tree) }
    }

    pub(crate) fn command(
        output: &'a build_helper::trust_output_lock::OutputLock,
        tree: &'a crate::core::build_steps::frontend_runtime::CommandOwnership,
    ) -> Self {
        Self { output, tree: TreeLease::Command(tree) }
    }

    pub(crate) fn with_current<T>(
        &self,
        root: &Path,
        output: &Path,
        prune: impl FnOnce() -> T,
    ) -> Result<T, String> {
        let prune = || {
            self.output.check_root(output).map_err(|error| error.to_string())?;
            let result = prune();
            self.output.check_root(output).map_err(|error| error.to_string())?;
            Ok(result)
        };
        match self.tree {
            TreeLease::Repository(lease) => {
                lease.check_root(root)?;
                let result = prune()?;
                lease.check_root(root)?;
                Ok(result)
            }
            TreeLease::Command(command) => command.with_pruning_lease(root, prune),
            TreeLease::Native(lease) => {
                if lease.is_borrowed() {
                    return Err("manual pruning requires its original independent lease".into());
                }
                lease.check_root(root).map_err(|error| error.to_string())?;
                let result = prune()?;
                lease.check_root(root).map_err(|error| error.to_string())?;
                Ok(result)
            }
        }
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn prune_owned(
    root: &Path,
    build: &Path,
    host_dir: &Path,
    streamed: &[Streamed],
    options: &Options,
    ownership: Option<Ownership<'_>>,
) -> Result<Summary, String> {
    ownership.ok_or("this invocation has no original native build/output ownership")?.with_current(
        root,
        build,
        || prune(build, host_dir, streamed, options),
    )
}

// --------------------------------------------------------------------------------------
// The driver: every tree, each judged on its own under its cargo locks.
// --------------------------------------------------------------------------------------

/// How to prune.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Options {
    /// Remove loose Mach-O objects their rlib holds (Darwin).
    pub(crate) objects: bool,
    /// Called with a tree and the [`Stage`] its prune reached; `None` outside the tests,
    /// which use it to change a tree between judging and deleting and to see the locks.
    pub(crate) observe: Option<fn(&Path, Stage)>,
}

/// Where a tree's prune is when [`Options::observe`] is called.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Stage {
    /// Judged, before the refusals that read the tree again.
    Judged,
    /// The refusals passed; deletion is next.
    Deleting,
}

/// What one prune did, for one line of output.
#[derive(Debug, Default)]
pub(crate) struct Summary {
    pub(crate) trees: usize,
    pub(crate) judged: usize,
    pub(crate) unchanged: usize,
    /// `(tree, why)` for each tree left unjudged or unpruned.
    pub(crate) skipped: Vec<(PathBuf, String)>,
    pub(crate) units: usize,
    pub(crate) objects: usize,
    pub(crate) planned_units: usize,
    pub(crate) planned_objects: usize,
    pub(crate) space_estimate: Option<space::Estimate>,
    pub(crate) space_observation_errors: Vec<String>,
    pub(crate) bytes: u64,
    pub(crate) failures: Vec<String>,
    /// Each removed unit and object entry, with why.
    pub(crate) listing: Vec<String>,
    pub(crate) reported: usize,
    pub(crate) compiled: usize,
    pub(crate) elapsed: Duration,
}

impl Summary {
    fn print(&self, verbose: bool) {
        if verbose {
            for line in &self.listing {
                println!("prune: {line}");
            }
        }
        for (tree, why) in &self.skipped {
            eprintln!("WARNING: prune: left {} as it is: {why}", tree.display());
        }
        for failure in &self.failures {
            eprintln!("WARNING: prune: {failure}");
        }
        println!("{}", self.line());
    }

    /// The one line every prune prints: units, GiB and seconds.
    pub(crate) fn line(&self) -> String {
        format!(
            "Prune: removed {} superseded units and {} duplicate objects, {:.2} GiB, in {:.2} s \
             ({} target trees: {} judged, {} unchanged since their last prune, {} left as they \
             are; this run's cargo reported {} artifacts, {} compiled)",
            self.units,
            self.objects,
            self.bytes as f64 / (1u64 << 30) as f64,
            self.elapsed.as_secs_f64(),
            self.trees,
            self.judged,
            self.unchanged,
            self.skipped.len(),
            self.reported,
            self.compiled,
        )
    }
}

/// Prunes every cargo target tree under `build` (the build directory) and `host_dir`
/// (`build/<host>`). Each tree is judged on its own, holding every cargo lock of its
/// profile directories, and is left as it is on any refusal.
pub(crate) fn prune(
    build: &Path,
    host_dir: &Path,
    streamed: &[Streamed],
    options: &Options,
) -> Summary {
    prune_selected(build, host_dir, streamed, options, true, false)
}

/// The manual and automatic entry use the same judge and deletion refusals.
/// A preview always judges afresh and never removes anything or writes a stamp.
pub(crate) fn prune_selected(
    build: &Path,
    host_dir: &Path,
    streamed: &[Streamed],
    options: &Options,
    variants: bool,
    dry_run: bool,
) -> Summary {
    prune_selected_inner(build, host_dir, streamed, options, variants, dry_run, None)
}

/// Manual maintenance observes the same approved paths without changing the
/// judge, deletion guards, automatic cleanup policy or cleanup stamp.
pub(crate) struct ManualObservation<'a> {
    pub(crate) directory: std::os::fd::BorrowedFd<'a>,
    pub(crate) revalidate: Option<&'a dyn Fn() -> Result<(), String>>,
}

pub(crate) fn prune_selected_measured(
    build: &Path,
    host_dir: &Path,
    streamed: &[Streamed],
    options: &Options,
    variants: bool,
    dry_run: bool,
    observation: ManualObservation<'_>,
) -> Summary {
    prune_selected_inner(build, host_dir, streamed, options, variants, dry_run, Some(observation))
}

fn prune_selected_inner(
    build: &Path,
    host_dir: &Path,
    streamed: &[Streamed],
    options: &Options,
    variants: bool,
    dry_run: bool,
    observation: Option<ManualObservation<'_>>,
) -> Summary {
    let start = Instant::now();
    // Only manual observations retain all prepared plans and their ORIGINAL
    // Cargo locks. Automatic pruning keeps its existing per-tree cost/policy.
    let mut prepared = Vec::new();
    let mut summary = Summary {
        reported: streamed.iter().filter(|s| !s.ran).count(),
        compiled: streamed.iter().filter(|s| s.compiled).count(),
        ..Summary::default()
    };
    if let Some(why) = outside(build, host_dir) {
        summary.skipped.push((host_dir.to_owned(), why));
        summary.elapsed = start.elapsed();
        return summary;
    }
    // Every potential tree/profile must be discovered before any deletion:
    // a missing census can hide a stamp protecting another readable tree.
    let discovered = target_trees(build, host_dir).and_then(|trees| {
        trees
            .into_iter()
            .map(|tree| profile_dirs(&tree).map(|profiles| (tree, profiles)))
            .collect::<Result<Vec<_>, _>>()
    });
    let trees = match discovered {
        Ok(trees) => trees,
        Err(error) => {
            summary.skipped.push((host_dir.to_owned(), error));
            summary.elapsed = start.elapsed();
            return summary;
        }
    };
    summary.trees = trees.len();
    let every_profile: Vec<PathBuf> = trees.iter().flat_map(|(_, p)| p.iter().cloned()).collect();
    let mut links: Option<Vec<PathBuf>> = None;
    for (tree, profiles) in &trees {
        if let Some(why) = outside(build, tree) {
            summary.skipped.push((tree.clone(), why));
            continue;
        }
        let locks = match CargoLocks::acquire(profiles) {
            Ok(locks) => locks,
            Err(busy) => {
                summary.skipped.push((tree.clone(), busy.join("; ")));
                continue;
            }
        };
        let compiled_here = {
            let real = fs::canonicalize(tree).ok();
            streamed.iter().any(|s| {
                s.compiled
                    && (s.path.starts_with(tree)
                        || real.as_ref().is_some_and(|real| s.path.starts_with(real)))
            })
        };
        let digest = selected_digest(tree, profiles, variants, options.objects);
        if !dry_run && !compiled_here && digest.is_some() && read_stamp(tree) == digest {
            summary.unchanged += 1;
            drop(locks);
            continue;
        }
        let planned = if variants {
            plan_tree(tree, profiles, streamed, options.objects)
        } else {
            plan_tree_selected(tree, profiles, streamed, false, options.objects)
        };
        let plan = match planned {
            Ok(plan) => plan,
            Err(unreadable) => {
                summary.skipped.push((tree.clone(), unreadable.join("; ")));
                continue;
            }
        };
        summary.judged += 1;
        let doomed = plan.paths();
        if !doomed.is_empty() {
            if let Some(observe) = options.observe {
                observe(tree, Stage::Judged);
            }
            let mut refusals = outside_trees(&plan);
            if refusals.is_empty() {
                let links = links.get_or_insert_with(|| kept_links(host_dir));
                refusals = unsafe_links(links, &doomed);
            }
            if refusals.is_empty() {
                refusals = stamped_in_plan(&doomed, &every_profile);
            }
            if !refusals.is_empty() {
                refusals.truncate(20);
                summary.skipped.push((tree.clone(), format!("refused: {}", refusals.join("; "))));
                continue;
            }
            summary.listing.extend(plan.listing(build));
            let paths = plan.unit_paths();
            summary.planned_units += paths.iter().filter(|(_, _, unit)| *unit).count();
            summary.planned_objects += paths
                .iter()
                .filter(|(_, _, unit)| !*unit)
                .map(|(_, paths, _)| paths.len())
                .sum::<usize>();
            if observation.is_some() {
                prepared.push((tree, profiles, plan, locks));
                continue;
            }
            if dry_run {
                continue;
            }
            if let Some(observe) = options.observe {
                observe(tree, Stage::Deleting);
            }
            let removal = remove_units(&plan.unit_paths());
            summary.units += removal.units;
            summary.objects += removal.objects;
            summary.bytes += removal.bytes;
            if !removal.failures.is_empty() {
                summary.failures.extend(removal.failures);
                continue; // judged again next time
            }
        }
        if observation.is_some() {
            prepared.push((tree, profiles, plan, locks));
            continue;
        }
        // The stamp binds the selected cleanup policy as well as the inputs.
        if !dry_run
            && let Some(digest) = selected_digest(tree, profiles, variants, options.objects)
            && let Err(error) = write_stamp(tree, &digest)
        {
            summary.failures.push(format!("{}: {STAMP} not written: {error}", tree.display()));
        }
        drop(locks);
    }
    if let Some(observation) = observation {
        let directory = observation.directory;
        // Measure the COMPLETE approved selection before any selected unlink
        // or cleanup stamp. Never mix pre- and post-deletion link counts.
        let estimate = (|| -> io::Result<space::Estimate> {
            let mut accounting = space::Accounting::new(build, directory)?;
            for (_, _, plan, _) in &prepared {
                accounting.collect(&plan.paths())?;
            }
            accounting.finish()
        })();
        match estimate {
            Ok(estimate) => summary.space_estimate = Some(estimate),
            Err(error) => summary.space_observation_errors.push(error.to_string()),
        }
        // Keep every original Cargo lock through the whole mutation phase;
        // the measurement above supplies no deletion authority.
        for (tree, profiles, plan, _locks) in &prepared {
            if let Some(check) = observation.revalidate
                && let Err(error) = check()
            {
                summary.failures.push(error);
                break;
            }
            if dry_run {
                continue;
            }
            let doomed = plan.paths();
            if !doomed.is_empty() {
                // Earlier plans waited while other trees were judged. Apply
                // the existing guards again rather than reuse a stale look.
                let mut refusals = outside_trees(plan);
                if let Some(why) = outside(build, tree) {
                    refusals.push(why);
                }
                if refusals.is_empty() {
                    refusals =
                        unsafe_links(links.get_or_insert_with(|| kept_links(host_dir)), &doomed);
                }
                if refusals.is_empty() {
                    refusals = stamped_in_plan(&doomed, &every_profile);
                }
                if !refusals.is_empty() {
                    refusals.truncate(20);
                    summary
                        .skipped
                        .push(((*tree).clone(), format!("refused: {}", refusals.join("; "))));
                    continue;
                }
                if let Some(observe) = options.observe {
                    observe(tree, Stage::Deleting);
                }
                if let Some(check) = observation.revalidate
                    && let Err(error) = check()
                {
                    summary.failures.push(error);
                    break;
                }
                let removal = remove_units(&plan.unit_paths());
                summary.units += removal.units;
                summary.objects += removal.objects;
                summary.bytes += removal.bytes;
                if !removal.failures.is_empty() {
                    summary.failures.extend(removal.failures);
                    continue;
                }
            }
            if let Some(check) = observation.revalidate
                && let Err(error) = check()
            {
                summary.failures.push(error);
                break;
            }
            if let Some(digest) = selected_digest(tree, profiles, variants, options.objects)
                && let Err(error) = write_stamp(tree, &digest)
            {
                summary.failures.push(format!("{}: {STAMP} not written: {error}", tree.display()));
            }
        }
    }
    summary.elapsed = start.elapsed();
    summary
}

/// Why `path` is not inside the build directory `build` once links are resolved, if it
/// is not: this run takes only this build directory's locks.
fn outside(build: &Path, path: &Path) -> Option<String> {
    let real_build = match fs::canonicalize(build) {
        Ok(real) => real,
        Err(error) => return Some(format!("{} cannot be resolved ({error})", build.display())),
    };
    match fs::canonicalize(path) {
        Ok(real) if real == real_build || real.starts_with(&real_build) => None,
        Ok(real) => Some(format!(
            "{} resolves to {}, outside {}",
            path.display(),
            real.display(),
            real_build.display()
        )),
        Err(error) => Some(format!("{} cannot be resolved ({error})", path.display())),
    }
}

// --------------------------------------------------------------------------------------
// Trees, profile directories and units.
// --------------------------------------------------------------------------------------

/// The directories directly in `path` that are not links, sorted. An
/// unreadable directory/entry is unknown, never evidence of an empty census.
fn subdirs(path: &Path) -> Result<Vec<PathBuf>, String> {
    let entries = fs::read_dir(path)
        .map_err(|error| format!("{} cannot be listed ({error})", path.display()))?;
    let mut found = Vec::new();
    for entry in entries {
        let entry =
            entry.map_err(|error| format!("{} cannot be listed ({error})", path.display()))?;
        let kind = entry
            .file_type()
            .map_err(|error| format!("{} cannot be judged ({error})", entry.path().display()))?;
        if kind.is_dir() {
            found.push(entry.path());
        }
    }
    found.sort();
    Ok(found)
}

/// Cargo target directories under the original build/host roots. Marker
/// lookup failure is unknown, never evidence that a candidate has no stamps.
pub(crate) fn target_trees(build: &Path, host_dir: &Path) -> Result<Vec<PathBuf>, String> {
    fn marker(path: &Path) -> Result<bool, String> {
        match fs::symlink_metadata(path) {
            Ok(metadata) if metadata.is_file() => Ok(true),
            Ok(_) => Err(format!("{} is not a regular Cargo marker", path.display())),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
            Err(error) => Err(format!("{} cannot be judged ({error})", path.display())),
        }
    }
    let mut trees = Vec::new();
    for parent in [host_dir, build] {
        for path in subdirs(parent)? {
            let name =
                path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
            if name.contains(RECLAIM_TAG) || PRUNE_NEVER.contains(&name.as_str()) {
                continue;
            }
            if marker(&path.join("CACHEDIR.TAG"))? || marker(&path.join(".rustc_info.json"))? {
                trees.push(path);
            }
        }
    }
    Ok(trees)
}

/// Whether `candidate` holds a cargo lock; `None` when that cannot be told.
fn lock_presence(candidate: &Path) -> Option<bool> {
    for lock in CARGO_LOCKS {
        match fs::symlink_metadata(candidate.join(lock)) {
            Ok(_) => return Some(true),
            Err(error)
                if error.kind() == io::ErrorKind::NotFound
                    || error.kind() == io::ErrorKind::NotADirectory =>
            {
                continue;
            }
            Err(_) => return None,
        }
    }
    Some(false)
}

/// Every Cargo profile directory of a target tree. Discovery failures refuse
/// the whole census before cleanup, because their stamps may protect another
/// tree. A missing lock is absence; an unreadable lock is unknown.
pub(crate) fn profile_dirs(tree: &Path) -> Result<Vec<PathBuf>, String> {
    fn listed(path: &Path) -> Result<Vec<PathBuf>, String> {
        subdirs(path).map_err(|error| {
            if lock_presence(path).is_none() {
                format!("{} cannot be judged; {error}", path.join(CARGO_LOCKS[0]).display())
            } else {
                error
            }
        })
    }
    let mut found: Vec<PathBuf> = Vec::new();
    for depth1 in listed(tree)? {
        let mut candidates = vec![depth1.clone()];
        candidates.extend(listed(&depth1)?);
        for candidate in candidates {
            if found.contains(&candidate) {
                continue;
            }
            match lock_presence(&candidate) {
                None => {
                    return Err(format!(
                        "{} cannot be judged",
                        candidate.join(CARGO_LOCKS[0]).display()
                    ));
                }
                Some(true)
                    if [".fingerprint", "deps", "build"]
                        .iter()
                        .any(|d| candidate.join(d).is_dir()) =>
                {
                    found.push(candidate);
                }
                _ => {}
            }
        }
    }
    Ok(found)
}

/// What a unit is a build *of*: its fingerprint's `path`, `target`, `features`, `profile`
/// and `compile_kind`, or nothing a variant can be judged by.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Identity {
    Of {
        path: i128,
        target: i128,
        features: String,
        profile: i128,
        compile_kind: i128,
    },
    /// No identity could be read: a variant of nothing but itself.
    Unknown(String),
}

/// What a fingerprint built from `Fingerprint::new()` carries: a build-script run.
fn no_own_identity() -> Identity {
    Identity::Of { path: 0, target: 0, features: String::new(), profile: 0, compile_kind: 0 }
}

/// One cargo unit of a profile directory, in either layout.
#[derive(Clone, Debug, Default)]
pub(crate) struct Unit {
    pub(crate) profile: PathBuf,
    pub(crate) pkg: String,
    pub(crate) unit_id: String,
    /// What deleting it removes.
    pub(crate) paths: Vec<PathBuf>,
    /// Its fingerprint hash(es), and its hash files' names.
    pub(crate) hashes: BTreeSet<String>,
    pub(crate) kinds: BTreeSet<String>,
    /// Its dependencies' fingerprint hashes.
    pub(crate) dep_hashes: BTreeSet<String>,
    pub(crate) depinfo: Vec<PathBuf>,
    /// Its rlib, rmeta, dylib or executable.
    pub(crate) outputs: Vec<PathBuf>,
    /// Its loose `.rcgu.o` files.
    pub(crate) objects: Vec<PathBuf>,
    /// The newest hash file's modification time (ns since the epoch), 0 when none.
    pub(crate) built: i128,
    pub(crate) identities: BTreeSet<Identity>,
}

impl Unit {
    /// What it is a build of, from its fingerprint; `None` when not exactly one.
    pub(crate) fn identity(&self) -> Option<&Identity> {
        if self.identities.len() == 1 { self.identities.iter().next() } else { None }
    }

    fn is_run(&self) -> bool {
        self.identity() == Some(&no_own_identity())
    }

    pub(crate) fn label(&self) -> String {
        format!("{}-{}", self.pkg, self.unit_id)
    }
}

fn is_hex16(text: &str) -> bool {
    text.len() == 16 && text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// Python's `str.isspace` (and so a regular expression's `\s`): Unicode white space and
/// the information separators `\x1c`-`\x1f`.
fn is_space(c: char) -> bool {
    c.is_whitespace() || ('\x1c'..='\x1f').contains(&c)
}

/// `(pkg, id)` of a `<pkg>-<id>` unit directory name.
fn unit_dir_name(name: &str) -> Option<(&str, &str)> {
    let at = name.len().checked_sub(17)?;
    if at == 0 || !name.is_char_boundary(at) || name.as_bytes()[at] != b'-' {
        return None;
    }
    let (pkg, id) = (&name[..at], &name[at + 1..]);
    (is_hex16(id) && !pkg.contains('\n')).then_some((pkg, id))
}

/// `(crate, id)` of a cargo artifact named by its unit id: `lib<crate>-<id>.rlib`,
/// `<crate>-<id>.d`, `<crate>-<id>` (an executable), `<crate>-<id>.<...>.rcgu.o`.
fn artifact_name(name: &str) -> Option<(&str, &str)> {
    let bytes = name.as_bytes();
    let word = bytes.iter().take_while(|b| b.is_ascii_alphanumeric() || **b == b'_').count();
    if word == 0 || bytes.get(word) != Some(&b'-') {
        return None;
    }
    let id = name.get(word + 1..word + 17)?;
    if !is_hex16(id) {
        return None;
    }
    let rest = &name[word + 17..];
    if !rest.is_empty() && (!rest.starts_with('.') || rest.contains('\n')) {
        return None;
    }
    let krate = if word > 3 && name.starts_with("lib") { &name[3..word] } else { &name[..word] };
    Some((krate, id))
}

/// Every unit id a path in `text` names, in either layout:
/// `<profile>/deps/<artifact>`, `<profile>/examples/<artifact>`,
/// `<profile>/.fingerprint/<pkg>-<id>/...`, `<profile>/build/<pkg>-<id>/...` (legacy),
/// `<profile>/build/<pkg>/<id>/...` (new). The same matches, in the same order, as
/// `slim_build.py`'s `_UNIT_REF` under `finditer`.
pub(crate) fn unit_refs(text: &str) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    let bytes = text.as_bytes();
    let mut at = 0;
    while let Some(offset) = memchr::memchr(b'/', &bytes[at..]) {
        let slash = at + offset;
        match unit_ref_at(text, slash) {
            Some((id, end)) => {
                found.insert(id.to_owned());
                at = end;
            }
            None => at = slash + 1,
        }
    }
    found
}

/// Whether what follows a matched id ends it: the end of the text, or (`ends`) a char.
fn ends_at(text: &str, at: usize, ends: impl Fn(char) -> bool) -> bool {
    text[at..].chars().next().is_none_or(ends)
}

/// The end of the run of chars from `start` that are neither `/` nor white space.
fn path_component_end(text: &str, start: usize) -> usize {
    text[start..]
        .char_indices()
        .find(|&(_, c)| c == '/' || is_space(c))
        .map_or(text.len(), |(i, _)| start + i)
}

fn hex16_at(text: &str, at: usize) -> Option<&str> {
    text.get(at..at + 16).filter(|id| is_hex16(id))
}

/// The unit id a path names at the `/` at `slash`, and where the match ends.
fn unit_ref_at(text: &str, slash: usize) -> Option<(&str, usize)> {
    let rest = &text[slash..];
    for prefix in ["/deps/", "/examples/"] {
        if let Some(after) = rest.strip_prefix(prefix) {
            let start = slash + prefix.len();
            let word =
                after.bytes().take_while(|b| b.is_ascii_alphanumeric() || *b == b'_').count();
            let dash = start + word;
            if word == 0 || text.as_bytes().get(dash) != Some(&b'-') {
                return None;
            }
            let id = hex16_at(text, dash + 1)?;
            let end = dash + 17;
            return ends_at(text, end, |c| c == '.' || c == ':' || is_space(c))
                .then_some((id, end));
        }
    }
    let legacy = ["/build/", "/.fingerprint/"].into_iter().find(|p| rest.starts_with(p));
    if let Some(prefix) = legacy {
        // `[^/\s]+-<id>`, the rightmost `-<id>` of the run that ends the run or meets `:`.
        let start = slash + prefix.len();
        let run_end = path_component_end(text, start);
        let mut dash = run_end.checked_sub(17).filter(|d| *d > start);
        while let Some(at) = dash {
            if text.as_bytes()[at] == b'-'
                && let Some(id) = hex16_at(text, at + 1)
                && (at + 17 == run_end || text.as_bytes()[at + 17] == b':')
            {
                return Some((id, at + 17));
            }
            dash = at.checked_sub(1).filter(|d| *d > start);
        }
        if prefix == "/build/" {
            // `build/<pkg>/<id>`, the new layout.
            if run_end > start && text.as_bytes().get(run_end) == Some(&b'/') {
                let id = hex16_at(text, run_end + 1)?;
                let end = run_end + 17;
                return ends_at(text, end, |c| c == '/' || c == ':' || is_space(c))
                    .then_some((id, end));
            }
        }
    }
    None
}

/// A fingerprint hash as cargo writes it into a unit's hash file.
pub(crate) fn le_hex(value: u64) -> String {
    value.to_le_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

/// An integer as Python reads one from JSON: any integral number (a bool is one too).
fn json_int(value: &serde_json::Value) -> Option<i128> {
    match value {
        serde_json::Value::Number(n) => {
            n.as_i64().map(i128::from).or_else(|| n.as_u64().map(i128::from))
        }
        _ => None,
    }
}

/// The identity a fingerprint's JSON gives, when every field is there with its type.
fn fingerprint_identity(data: &serde_json::Value) -> Option<Identity> {
    let object = data.as_object()?;
    let int = |name: &str| object.get(name).and_then(json_int);
    Some(Identity::Of {
        path: int("path")?,
        target: int("target")?,
        features: object.get("features")?.as_str()?.to_owned(),
        profile: int("profile")?,
        compile_kind: int("compile_kind")?,
    })
}

fn mtime_ns(meta: &fs::Metadata) -> i128 {
    i128::from(meta.mtime()) * 1_000_000_000 + i128::from(meta.mtime_nsec())
}

fn now() -> i128 {
    SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_nanos() as i128)
}

/// Sorted entries of `path`: none when it does not exist or is a link (never followed).
/// A directory that cannot be listed whole is an error, which leaves its tree as it is:
/// read as empty, its units would lose their fingerprints or roots to the judge.
fn entries(path: &Path) -> Result<Vec<fs::DirEntry>, String> {
    match fs::symlink_metadata(path) {
        Ok(meta) if meta.file_type().is_symlink() => return Ok(Vec::new()),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(format!("{} cannot be judged ({error})", path.display())),
    }
    let cannot = |error: io::Error| format!("{} cannot be listed ({error})", path.display());
    let mut found: Vec<fs::DirEntry> =
        fs::read_dir(path).map_err(cannot)?.collect::<io::Result<_>>().map_err(cannot)?;
    found.sort_by_key(|entry| entry.file_name());
    Ok(found)
}

fn name_of(entry: &fs::DirEntry) -> String {
    entry.file_name().to_string_lossy().into_owned()
}

fn is_dir_entry(entry: &fs::DirEntry) -> bool {
    entry.file_type().is_ok_and(|kind| kind.is_dir())
}

fn is_file_entry(entry: &fs::DirEntry) -> bool {
    entry.file_type().is_ok_and(|kind| kind.is_file())
}

fn read_fingerprint(unit: &mut Unit, dir: &Path) -> Result<(), String> {
    for entry in entries(dir)? {
        if !is_file_entry(&entry) {
            continue;
        }
        let name = name_of(&entry);
        if name.ends_with(".json") {
            let parsed = fs::read(entry.path()).ok().and_then(|bytes| {
                serde_json::from_str::<serde_json::Value>(&String::from_utf8_lossy(&bytes)).ok()
            });
            let Some(data) = parsed.filter(|data| data.is_object()) else {
                // Unreadable: no identity, so the unit is a variant of nothing.
                unit.identities.insert(Identity::Unknown(unit.unit_id.clone()));
                continue;
            };
            unit.identities.insert(
                fingerprint_identity(&data)
                    .unwrap_or_else(|| Identity::Unknown(unit.unit_id.clone())),
            );
            if let Some(deps) = data.get("deps").and_then(|deps| deps.as_array()) {
                for dep in deps {
                    let last = dep.as_array().and_then(|dep| dep.last());
                    let hash = match last {
                        Some(serde_json::Value::Bool(b)) => Some(i128::from(*b)),
                        Some(value) => json_int(value),
                        None => None,
                    };
                    if let Some(hash) = hash {
                        unit.dep_hashes.insert(le_hex(hash as u64));
                    }
                }
            }
            continue;
        }
        if name.starts_with("dep-") || name.starts_with("output-") || name == "invoked.timestamp" {
            continue;
        }
        // A hash file names the unit's kind and says when it was built; unread, the unit
        // could look older than it is.
        let bytes = fs::read(entry.path())
            .map_err(|error| format!("{} cannot be read ({error})", entry.path().display()))?;
        let content = String::from_utf8_lossy(&bytes);
        let content = content.trim_matches(is_space);
        if is_hex16(content) {
            unit.hashes.insert(content.to_owned());
            unit.kinds.insert(name);
            if let Ok(meta) = fs::symlink_metadata(entry.path()) {
                unit.built = unit.built.max(mtime_ns(&meta));
            }
        }
    }
    Ok(())
}

fn is_executable(path: &Path) -> bool {
    let Ok(c_path) = std::ffi::CString::new(path.as_os_str().as_bytes()) else { return false };
    // SAFETY: `c_path` is a valid NUL-terminated string for the duration of the call.
    unsafe { libc::access(c_path.as_ptr(), libc::X_OK) == 0 }
}

fn classify_artifact(unit: &mut Unit, path: PathBuf) {
    let name = path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
    if name.ends_with(".rcgu.o") {
        unit.objects.push(path);
    } else if name.ends_with(".d") {
        unit.depinfo.push(path);
    } else if name.ends_with(".rlib")
        || name.ends_with(".rmeta")
        || LINKED_OUTPUTS.iter().any(|ext| name.ends_with(ext))
    {
        unit.outputs.push(path);
    } else if !name.contains('.') && path.is_file() && is_executable(&path) {
        unit.outputs.push(path); // an executable: a binary, a test, a build script
    }
}

/// The units of one cargo profile directory (`<tree>[/<target>]/<profile>`). It follows
/// no link: a linked `deps/`, `.fingerprint/`, `build/`, `examples/`, unit directory or
/// `out/` is not read, so nothing behind one is planned. A directory in it that cannot
/// be listed, or a fingerprint file that cannot be read, is an error: the tree is left.
pub(crate) fn scan_profile(profile: &Path) -> Result<Vec<Unit>, String> {
    let mut units: Vec<Unit> = Vec::new();
    let mut index: HashMap<String, usize> = HashMap::new();
    let mut unit = |units: &mut Vec<Unit>, pkg: &str, id: &str| -> usize {
        *index.entry(id.to_owned()).or_insert_with(|| {
            units.push(Unit {
                profile: profile.to_owned(),
                pkg: pkg.to_owned(),
                unit_id: id.to_owned(),
                ..Unit::default()
            });
            units.len() - 1
        })
    };
    for entry in entries(&profile.join(".fingerprint"))? {
        let name = name_of(&entry);
        if let Some((pkg, id)) = unit_dir_name(&name)
            && is_dir_entry(&entry)
        {
            let at = unit(&mut units, pkg, id);
            units[at].paths.push(entry.path());
            read_fingerprint(&mut units[at], &entry.path())?;
        }
    }
    for entry in entries(&profile.join("build"))? {
        if !is_dir_entry(&entry) {
            continue;
        }
        let name = name_of(&entry);
        if let Some((pkg, id)) = unit_dir_name(&name) {
            // Legacy: a build script's compile or run directory.
            let at = unit(&mut units, pkg, id);
            units[at].paths.push(entry.path());
            continue;
        }
        for sub in entries(&entry.path())? {
            let sub_name = name_of(&sub);
            if !(is_hex16(&sub_name) && is_dir_entry(&sub)) {
                continue;
            }
            // New layout: build/<pkg>/<id>/.
            let at = unit(&mut units, &name, &sub_name);
            units[at].paths.push(sub.path());
            read_fingerprint(&mut units[at], &sub.path().join("fingerprint"))?;
            // A build-script RUN unit's `out/` is its OUT_DIR: what the script wrote, not
            // rustc's outputs, so nothing in it is an rlib's duplicate object.
            if units[at].kinds.iter().any(|kind| kind.starts_with("run-")) {
                continue;
            }
            for out in entries(&sub.path().join("out"))? {
                if is_file_entry(&out) {
                    classify_artifact(&mut units[at], out.path());
                }
            }
        }
    }
    for directory in ["deps", "examples"] {
        for entry in entries(&profile.join(directory))? {
            let name = name_of(&entry);
            let Some((krate, id)) = artifact_name(&name) else { continue };
            if entry.file_type().is_ok_and(|kind| kind.is_symlink()) {
                continue;
            }
            let at = unit(&mut units, krate, id);
            units[at].paths.push(entry.path());
            if is_file_entry(&entry) {
                classify_artifact(&mut units[at], entry.path());
            }
        }
    }
    Ok(units)
}

/// `(stamp, path)` for every record of every bootstrap stamp in `profile`, and each stamp
/// (or the profile directory itself) that cannot be read. An unreadable stamp is never
/// skipped: what it names would lose its root and its refusal.
pub(crate) fn stamp_records(profile: &Path) -> (Vec<(PathBuf, PathBuf)>, Vec<String>) {
    let mut records = Vec::new();
    let names = match fs::read_dir(profile).and_then(|read| read.collect::<io::Result<Vec<_>>>()) {
        Ok(read) => {
            let mut names: Vec<_> = read.iter().map(|entry| entry.file_name()).collect();
            names.sort();
            names
        }
        Err(error) => {
            return (
                records,
                vec![format!(
                    "{} cannot be listed ({error}), so its stamps cannot be read",
                    profile.display()
                )],
            );
        }
    };
    let mut unreadable = Vec::new();
    for name in names {
        let bytes = name.as_bytes();
        if !(bytes.starts_with(b".") && bytes.ends_with(b"stamp")) {
            continue;
        }
        let stamp = profile.join(&name);
        // Never open what is not a regular file: reading a FIFO would hang the prune
        // while it holds every lock.
        let data = fs::symlink_metadata(&stamp).and_then(|meta| {
            if meta.file_type().is_file() {
                fs::read(&stamp)
            } else {
                Err(io::Error::new(io::ErrorKind::InvalidInput, "not a regular file"))
            }
        });
        match data {
            Ok(data) => {
                for record in data.split(|b| *b == 0) {
                    let record = match record {
                        [kind, b'/', ..] if b"hts".contains(kind) => &record[1..],
                        _ => record,
                    };
                    if !record.is_empty() {
                        records.push((stamp.clone(), PathBuf::from(OsStr::from_bytes(record))));
                    }
                }
            }
            Err(error) => unreadable.push(format!(
                "{} cannot be read ({error}), so what it names cannot be protected",
                stamp.display()
            )),
        }
    }
    (records, unreadable)
}

/// The uplifted dep-info files of a profile directory: `<profile>/<name>.d`.
fn uplifted_depinfo(profile: &Path) -> Vec<PathBuf> {
    let Ok(read) = fs::read_dir(profile) else { return Vec::new() };
    let mut found: Vec<PathBuf> = read
        .flatten()
        .filter(|entry| {
            let name = name_of(entry);
            // Python's `Path.suffix`: a leading dot alone is no suffix.
            let suffixed = name.rfind('.').is_some_and(|i| i > 0 && i < name.len() - 1)
                && name.ends_with(".d");
            suffixed
                && !entry.file_type().is_ok_and(|kind| kind.is_symlink())
                && entry.path().is_file()
        })
        .map(|entry| entry.path())
        .collect();
    found.sort();
    found
}

/// The name cargo uplifts a unit's output to, `-` read as `_` (a binary's uplifted name
/// keeps its hyphens, its unit's output has underscores): `libfoo-<id>.rlib` is
/// `libfoo.rlib`, `foo_bar-<id>` is `foo-bar`. The new layout names a binary without its
/// unit id (`build/<pkg>/<id>/out/foo`), so there the name is the output's own.
fn uplifted_name(output: &Path, unit_id: &str) -> Option<String> {
    let name = output.file_name()?.to_string_lossy().into_owned();
    let marker = format!("-{unit_id}");
    let uplifted = if let Some(at) = name.find(&marker) {
        format!("{}{}", &name[..at], &name[at + marker.len()..])
    } else if output.parent().and_then(|p| p.file_name()) == Some(OsStr::new("out"))
        && output.parent().and_then(|p| p.parent()).and_then(|p| p.file_name())
            == Some(OsStr::new(unit_id))
    {
        name
    } else {
        return None;
    };
    Some(uplifted.replace('-', "_"))
}

/// Whether two regular files hold the same bytes.
fn same_bytes(a: &Path, b: &Path) -> bool {
    let (Ok(meta_a), Ok(meta_b)) = (fs::metadata(a), fs::metadata(b)) else { return false };
    if !meta_a.is_file() || !meta_b.is_file() || meta_a.len() != meta_b.len() {
        return false;
    }
    let (Ok(mut file_a), Ok(mut file_b)) = (File::open(a), File::open(b)) else { return false };
    let mut buf_a = vec![0u8; 1 << 16];
    let mut buf_b = vec![0u8; 1 << 16];
    loop {
        let Ok(read) = file_a.read(&mut buf_a) else { return false };
        if read == 0 {
            return file_b.read(&mut buf_b[..1]).is_ok_and(|n| n == 0);
        }
        if file_b.read_exact(&mut buf_b[..read]).is_err() || buf_a[..read] != buf_b[..read] {
            return false;
        }
    }
}

/// What names each live unit: unit id to the first thing found naming it, and to the
/// time (ns since the epoch) of the newest root that does.
#[derive(Clone, Debug, Default)]
pub(crate) struct Roots {
    pub(crate) what: HashMap<String, String>,
    /// Insertion order of `what`, for a stable listing.
    pub(crate) order: Vec<String>,
    pub(crate) times: HashMap<String, i128>,
}

impl Roots {
    fn note(&mut self, unit_id: &str, what: impl FnOnce() -> String, when: Option<i128>) {
        if !self.what.contains_key(unit_id) {
            self.what.insert(unit_id.to_owned(), what());
            self.order.push(unit_id.to_owned());
        }
        if let Some(when) = when {
            let time = self.times.entry(unit_id.to_owned()).or_insert(0);
            *time = (*time).max(when);
        }
    }

    fn note_file(&mut self, unit_id: &str, what: impl FnOnce() -> String, root: &Path) {
        let when = fs::symlink_metadata(root).ok().map(|meta| mtime_ns(&meta));
        self.note(unit_id, what, when);
    }
}

/// The roots over `profiles`: what names the units the last builds of each profile
/// directory used. Its stamps, its uplifted dep-info and its uplifted artifacts (cargo
/// copies `deps/<name>-<id>` to `<profile>/<name>` after every build of that target, as
/// a hard link or, on macOS, a clone: such a file names the unit whose output is the same
/// file, or has the same name less `-<id>` and the same bytes). Then everything in
/// `streamed` (this run's cargo reports): the unit each reported path names, or, for an
/// uplifted path, the unit it is, at the moment cargo reported it.
pub(crate) fn find_roots(
    profiles: &[PathBuf],
    units: &[Unit],
    streamed: &[Streamed],
) -> Result<Roots, String> {
    let mut roots = Roots::default();
    let mut uplifts = Uplifts::default();
    for unit in units {
        for output in &unit.outputs {
            let Ok(meta) = fs::symlink_metadata(output) else { continue };
            uplifts
                .by_inode
                .entry((meta.dev(), meta.ino()))
                .or_insert_with(|| unit.unit_id.clone());
            if let Some(name) = uplifted_name(output, &unit.unit_id) {
                uplifts.by_name.entry((unit.profile.clone(), name)).or_default().push((
                    unit.unit_id.clone(),
                    output.clone(),
                    meta.len(),
                ));
            }
        }
    }
    for profile in profiles {
        let (stamped, _) = stamp_records(profile); // unreadable ones refuse in plan_tree
        for (stamp, path) in &stamped {
            let stamp_name = stamp.file_name().unwrap_or_default().to_string_lossy();
            for id in unit_refs(&path.to_string_lossy()) {
                roots.note_file(&id, || format!("stamp {stamp_name}"), stamp);
            }
        }
        for depinfo in uplifted_depinfo(profile) {
            let Ok(bytes) = fs::read(&depinfo) else { continue };
            let name = depinfo.file_name().unwrap_or_default().to_string_lossy().into_owned();
            for id in unit_refs(&String::from_utf8_lossy(&bytes)) {
                roots.note_file(&id, || format!("uplifted dep-info {name}"), &depinfo);
            }
        }
        let mut uplifted: Vec<fs::DirEntry> = Vec::new();
        for directory in [profile.clone(), profile.join("examples")] {
            uplifted.extend(entries(&directory)?); // none behind a link
        }
        for entry in uplifted {
            // `examples/` holds the units' own `<name>-<id>` outputs beside the uplifted
            // `<name>`: an output does not name itself.
            let name = name_of(&entry);
            if name.ends_with(".d") || artifact_name(&name).is_some() || !is_file_entry(&entry) {
                continue;
            }
            for (unit_id, what) in uplifts.units_of(profile, &entry.path(), &name) {
                roots.note_file(&unit_id, || what, &entry.path());
            }
        }
    }
    // This run's cargo reports (bootstrap's `stream_cargo`), at the time each arrived.
    let canonical: Vec<(PathBuf, &PathBuf)> = profiles
        .iter()
        .filter_map(|profile| Some((fs::canonicalize(profile).ok()?, profile)))
        .collect();
    for report in streamed {
        let what =
            if report.ran { "this run's cargo ran it" } else { "this run's cargo reported it" };
        let ids = unit_refs(&report.path.to_string_lossy());
        if !ids.is_empty() {
            for id in ids {
                roots.note(&id, || what.to_owned(), Some(report.when));
            }
            continue;
        }
        // An uplifted path: `<profile>/<name>` or `<profile>/examples/<name>`.
        let Some(name) = report.path.file_name().map(|n| n.to_string_lossy().into_owned()) else {
            continue;
        };
        let Some(parent) = report.path.parent().and_then(|p| fs::canonicalize(p).ok()) else {
            continue;
        };
        let profile = canonical.iter().find_map(|(real, profile)| {
            (parent == *real || parent == real.join("examples")).then_some(*profile)
        });
        if let Some(profile) = profile
            && artifact_name(&name).is_none()
        {
            for (unit_id, _) in uplifts.units_of(profile, &report.path, &name) {
                roots.note(&unit_id, || what.to_owned(), Some(report.when));
            }
        }
    }
    Ok(roots)
}

/// A unit's output that an uplift may be: `(unit id, path, size)`.
type Output = (String, PathBuf, u64);

/// Each unit's outputs by file identity, and by the name cargo uplifts them to.
#[derive(Default)]
struct Uplifts {
    by_inode: HashMap<(u64, u64), String>,
    /// `(profile, uplifted name)` to `(unit id, output, size)`.
    by_name: HashMap<(PathBuf, String), Vec<Output>>,
}

impl Uplifts {
    /// The units an uplifted file at `path` (in `profile` or its `examples/`) is, and how:
    /// the one whose output it is a link of, else each whose output of its name has its
    /// bytes.
    fn units_of(&self, profile: &Path, path: &Path, name: &str) -> Vec<(String, String)> {
        let Some(meta) = fs::symlink_metadata(path).ok().filter(|m| m.file_type().is_file()) else {
            return Vec::new();
        };
        if let Some(unit_id) = self.by_inode.get(&(meta.dev(), meta.ino())) {
            return vec![(unit_id.clone(), format!("uplifted {name} is a link of its output"))];
        }
        let key = (profile.to_owned(), name.replace('-', "_"));
        self.by_name
            .get(&key)
            .into_iter()
            .flatten()
            .filter(|(_, output, size)| *size == meta.len() && same_bytes(path, output))
            .map(|(unit_id, _, _)| {
                (unit_id.clone(), format!("uplifted {name} has its output's bytes"))
            })
            .collect()
    }
}

// --------------------------------------------------------------------------------------
// The judge.
// --------------------------------------------------------------------------------------

/// Whether a unit dies, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Verdict {
    pub(crate) unit: usize,
    pub(crate) dead: bool,
    pub(crate) reason: String,
}

/// A variant: the same target of the same package, built in the same mode, in the same
/// profile directory, with the same fingerprint identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct VariantKey {
    profile: PathBuf,
    pkg: String,
    kinds: BTreeSet<String>,
    checked: bool,
    identity: Identity,
}

struct Graph<'a> {
    units: &'a [Unit],
    by_id: HashMap<&'a str, Vec<usize>>,
    by_hash: HashMap<&'a str, Vec<usize>>,
    edges: Vec<Option<Vec<usize>>>,
}

impl<'a> Graph<'a> {
    fn new(units: &'a [Unit]) -> Self {
        let mut by_id: HashMap<&str, Vec<usize>> = HashMap::new();
        let mut by_hash: HashMap<&str, Vec<usize>> = HashMap::new();
        for (i, unit) in units.iter().enumerate() {
            by_id.entry(&unit.unit_id).or_default().push(i);
            for digest in &unit.hashes {
                by_hash.entry(digest).or_default().push(i);
            }
        }
        Graph { units, by_id, by_hash, edges: vec![None; units.len()] }
    }

    /// What `unit` read: the units its own dep-info names, and those its fingerprint's
    /// `deps` hashes are.
    fn edges(&mut self, unit: usize) -> &[usize] {
        if self.edges[unit].is_none() {
            let mut found = Vec::new();
            for depinfo in &self.units[unit].depinfo {
                let Ok(bytes) = fs::read(depinfo) else { continue };
                for id in unit_refs(&String::from_utf8_lossy(&bytes)) {
                    found.extend(self.by_id.get(id.as_str()).into_iter().flatten());
                }
            }
            for digest in &self.units[unit].dep_hashes {
                found.extend(self.by_hash.get(digest.as_str()).into_iter().flatten());
            }
            self.edges[unit] = Some(found);
        }
        self.edges[unit].as_deref().unwrap_or_default()
    }

    fn closure(&mut self, start: &[usize], into: &mut [bool]) {
        let mut work = start.to_vec();
        while let Some(unit) = work.pop() {
            if into[unit] {
                continue;
            }
            into[unit] = true;
            work.extend(self.edges(unit).iter().filter(|e| !into[**e]));
        }
    }

    /// Spreads each start's root time to everything it reaches, keeping the newest.
    fn spread(&mut self, start: Vec<(usize, i128)>, root_time: &mut [Option<i128>]) {
        let mut work = start;
        while let Some((unit, when)) = work.pop() {
            if root_time[unit].unwrap_or(-1) >= when {
                continue;
            }
            root_time[unit] = Some(when);
            let next: Vec<usize> = self
                .edges(unit)
                .iter()
                .copied()
                .filter(|e| root_time[*e].unwrap_or(-1) < when)
                .collect();
            work.extend(next.into_iter().map(|e| (e, when)));
        }
    }
}

/// Which units are dead, and why: `slim_build.py`'s `judge_units`, rule for rule.
///
/// LIVE is what the roots reach, and then, until nothing changes, every unit no variant
/// of which is live that has fingerprint dependencies and ALL of them live: it was built
/// against the live graph. A unit nothing reaches is DEAD only on evidence: it never
/// finished (no fingerprint hash), or a variant of the same target superseded it. A LIVE
/// variant supersedes it when the root that names the live one was written after this
/// unit was built; a KEPT variant supersedes it when that variant was built after it.
/// The newest finished variant of a target, built after every root that names another,
/// is KEPT UNJUDGED with everything it reaches. A build-script RUN unit is a variant of
/// nothing and dies only when every build script it ran is dead.
pub(crate) fn judge_units(units: &[Unit], roots: &Roots) -> Vec<Verdict> {
    let count = units.len();
    let mut graph = Graph::new(units);

    let rooted: Vec<usize> = roots
        .order
        .iter()
        .flat_map(|id| graph.by_id.get(id.as_str()).cloned().unwrap_or_default())
        .collect();
    let mut live = vec![false; count];
    graph.closure(&rooted, &mut live);
    let mut root_time: Vec<Option<i128>> = vec![None; count];
    let start: Vec<(usize, i128)> = rooted
        .iter()
        .map(|&u| (u, roots.times.get(&units[u].unit_id).copied().unwrap_or(0)))
        .collect();
    graph.spread(start, &mut root_time);

    let variant_key = |unit: &Unit| {
        let checked = !unit.outputs.is_empty()
            && unit.outputs.iter().all(|p| p.as_os_str().as_bytes().ends_with(b".rmeta"));
        let identity = if unit.is_run() { None } else { unit.identity().cloned() };
        VariantKey {
            profile: unit.profile.clone(),
            pkg: unit.pkg.clone(),
            kinds: unit.kinds.clone(),
            checked,
            identity: identity.unwrap_or_else(|| Identity::Unknown(unit.unit_id.clone())),
        }
    };
    let mut group_of: HashMap<VariantKey, usize> = HashMap::new();
    let mut groups: Vec<Vec<usize>> = Vec::new();
    let mut key_of = Vec::with_capacity(count);
    for (i, unit) in units.iter().enumerate() {
        let next = groups.len();
        let group = *group_of.entry(variant_key(unit)).or_insert(next);
        if group == next {
            groups.push(Vec::new());
        }
        groups[group].push(i);
        key_of.push(group);
    }

    let mut consistent = vec![false; count];
    loop {
        let live_hashes: HashSet<&str> = (0..count)
            .filter(|&i| live[i])
            .flat_map(|i| units[i].hashes.iter().map(String::as_str))
            .collect();
        let fresh: Vec<usize> = (0..count)
            .filter(|&i| {
                let unit = &units[i];
                !unit.hashes.is_empty()
                    && !live[i]
                    && !unit.dep_hashes.is_empty()
                    && unit.dep_hashes.iter().all(|d| live_hashes.contains(d.as_str()))
                    && !groups[key_of[i]].iter().any(|&v| live[v])
            })
            .collect();
        if fresh.is_empty() {
            break;
        }
        for &i in &fresh {
            consistent[i] = true;
        }
        // No root names it, so it has no root time: its evidence is its own build time.
        graph.closure(&fresh, &mut live);
    }

    // When the last completed command chose `unit`, or built it.
    let evidence = |i: usize| root_time[i].unwrap_or(0).max(units[i].built);

    let mut unjudged: Vec<usize> = Vec::new();
    for members in &groups {
        let Some(&best) =
            members.iter().filter(|&&u| !units[u].hashes.is_empty()).max_by(|&&a, &&b| {
                (units[a].built, &units[a].unit_id).cmp(&(units[b].built, &units[b].unit_id))
            })
        else {
            continue;
        };
        if units[best].is_run() {
            continue; // judged by its build script, below
        }
        if !live[best] && !members.iter().any(|&v| live[v] && evidence(v) > units[best].built) {
            unjudged.push(best);
        }
    }
    let mut kept = live.clone();
    graph.closure(&unjudged, &mut kept);
    let is_unjudged: HashSet<usize> = unjudged.iter().copied().collect();

    let mut verdicts: Vec<Verdict> = Vec::with_capacity(count);
    let mut runs: Vec<usize> = Vec::new();
    for (i, unit) in units.iter().enumerate() {
        let verdict = |dead: bool, reason: String| Verdict { unit: i, dead, reason };
        let later = groups[key_of[i]]
            .iter()
            .copied()
            .filter(|&v| {
                v != i
                    && kept[v]
                    && (if live[v] { evidence(v) } else { units[v].built }) > unit.built
            })
            .min_by(|&a, &b| units[a].unit_id.cmp(&units[b].unit_id));
        verdicts.push(if consistent[i] {
            verdict(false, "live: built against live units only".into())
        } else if live[i] {
            let why =
                roots.what.get(&unit.unit_id).map_or("reached from a live unit", String::as_str);
            verdict(false, format!("live: {why}"))
        } else if is_unjudged.contains(&i) {
            verdict(
                false,
                "kept unjudged: the newest finished variant of its target, built after every \
                 root that names another (a test, doc, check or unfinished build writes no \
                 stamp)"
                    .into(),
            )
        } else if kept[i] {
            verdict(false, "kept: a unit kept unjudged uses it".into())
        } else if unit.hashes.is_empty() {
            verdict(
                true,
                "never finished: it has no fingerprint hash, and nothing kept names it".into(),
            )
        } else if unit.is_run() {
            runs.push(i);
            verdict(false, String::new()) // judged below
        } else if let Some(by) = later {
            let how = if root_time[by].unwrap_or(0) > unit.built {
                format!(
                    "live variant {} is named by a root written after it was built",
                    units[by].unit_id
                )
            } else {
                let state = if live[by] { "live" } else { "kept" };
                format!("{state} variant {} was built after it", units[by].unit_id)
            };
            verdict(
                true,
                format!("superseded: no stamp, dep-info or kept fingerprint names it, and {how}"),
            )
        } else {
            verdict(false, "kept: nothing names it, and no variant superseded it".into())
        });
    }
    let dead: Vec<bool> = verdicts.iter().map(|v| v.dead).collect();
    for i in runs {
        let mut scripts: Vec<usize> = Vec::new();
        for digest in &units[i].dep_hashes {
            for &d in graph.by_hash.get(digest.as_str()).into_iter().flatten() {
                if units[d].identity().is_some() && !units[d].is_run() {
                    scripts.push(d);
                }
            }
        }
        verdicts[i] = if !scripts.is_empty() && scripts.iter().all(|&s| dead[s]) {
            let mut ids: Vec<&str> = scripts.iter().map(|&s| units[s].unit_id.as_str()).collect();
            ids.sort();
            Verdict {
                unit: i,
                dead: true,
                reason: format!(
                    "superseded: nothing kept names it, and the build script it ran ({}) is dead",
                    ids.join(", ")
                ),
            }
        } else if !scripts.is_empty() {
            Verdict {
                unit: i,
                dead: false,
                reason: "kept: the build script it ran is kept (each library profile has its \
                         own run of it)"
                    .into(),
            }
        } else {
            Verdict {
                unit: i,
                dead: false,
                reason: "kept: no build script it ran is found, so nothing supersedes it".into(),
            }
        };
    }
    verdicts
}

// --------------------------------------------------------------------------------------
// Duplicate objects.
// --------------------------------------------------------------------------------------

/// Member name to data size of a Unix archive (BSD or GNU names), or `None`.
pub(crate) fn ar_members(path: &Path) -> Option<HashMap<String, i64>> {
    let mut file = File::open(path).ok()?;
    let mut magic = [0u8; 8];
    if file.read_exact(&mut magic).is_err() || &magic != b"!<arch>\n" {
        return None;
    }
    let mut members = HashMap::new();
    let mut long_names: Vec<u8> = Vec::new();
    loop {
        let mut header = [0u8; 60];
        let mut got = 0;
        while got < 60 {
            match file.read(&mut header[got..]) {
                Ok(0) => break,
                Ok(n) => got += n,
                Err(_) => return None,
            }
        }
        if got < 60 {
            break;
        }
        let raw = trim_end(&header[..16], b' ');
        let size_field = std::str::from_utf8(&header[48..58]).ok()?.trim();
        let size: i64 = if size_field.is_empty() { 0 } else { size_field.parse().ok()? };
        if size < 0 {
            return None; // malformed: a negative size would seek backwards for ever
        }
        let start = file.stream_position().ok()?;
        let mut data = size;
        let name: Option<Vec<u8>> = if raw.starts_with(b"#1/")
            && raw.len() > 3
            && raw[3..].iter().all(u8::is_ascii_digit)
        {
            let length: usize = std::str::from_utf8(&raw[3..]).ok()?.parse().ok()?;
            let mut name = vec![0u8; length];
            let read = read_up_to(&mut file, &mut name).ok()?;
            name.truncate(read);
            data = size - length as i64;
            Some(trim_end(&name, 0).to_vec())
        } else if raw == b"//" {
            long_names = vec![0u8; size as usize];
            let read = read_up_to(&mut file, &mut long_names).ok()?;
            long_names.truncate(read);
            None
        } else if raw.len() > 1
            && raw[0] == b'/'
            && raw[1..].iter().all(u8::is_ascii_digit)
            && !long_names.is_empty()
        {
            let offset: usize = std::str::from_utf8(&raw[1..]).ok()?.parse().ok()?;
            let end =
                find(&long_names, b"/\n", offset).unwrap_or(long_names.len().saturating_sub(1));
            Some(long_names.get(offset..end).unwrap_or_default().to_vec())
        } else if raw == b"/" || raw == b"/SYM64/" {
            None
        } else {
            Some(raw.strip_suffix(b"/").unwrap_or(raw).to_vec())
        };
        if let Some(name) = name.filter(|name| !name.is_empty()) {
            members.insert(String::from_utf8_lossy(&name).into_owned(), data);
        }
        file.seek(SeekFrom::Start(start + size as u64 + (size as u64 & 1))).ok()?;
    }
    Some(members)
}

fn trim_end(bytes: &[u8], byte: u8) -> &[u8] {
    let end = bytes.iter().rposition(|b| *b != byte).map_or(0, |i| i + 1);
    &bytes[..end]
}

fn find(haystack: &[u8], needle: &[u8], from: usize) -> Option<usize> {
    haystack.get(from..)?.windows(needle.len()).position(|w| w == needle).map(|i| i + from)
}

fn read_up_to(file: &mut File, buf: &mut [u8]) -> io::Result<usize> {
    let mut got = 0;
    while got < buf.len() {
        match file.read(&mut buf[got..])? {
            0 => break,
            n => got += n,
        }
    }
    Ok(got)
}

fn is_macho(path: &Path) -> bool {
    let mut magic = [0u8; 4];
    File::open(path).and_then(|mut f| f.read_exact(&mut magic)).is_ok()
        && MACHO_MAGIC.contains(&magic)
}

/// `(loose Mach-O objects of unit that its rlib holds as members, why)`.
pub(crate) fn duplicate_objects(unit: &Unit) -> (Vec<PathBuf>, String) {
    if unit.objects.is_empty() {
        return (Vec::new(), String::new());
    }
    let ends = |path: &Path, ext: &str| path.as_os_str().as_bytes().ends_with(ext.as_bytes());
    let rlibs: Vec<&PathBuf> = unit.outputs.iter().filter(|p| ends(p, ".rlib")).collect();
    let linked: Vec<&PathBuf> =
        unit.outputs.iter().filter(|p| !ends(p, ".rlib") && !ends(p, ".rmeta")).collect();
    if let Some(linked) = linked.first() {
        let name = linked.file_name().unwrap_or_default().to_string_lossy();
        return (
            Vec::new(),
            format!("kept: {name} is not an rlib, and only an rlib-only unit's objects go"),
        );
    }
    if rlibs.len() != 1 {
        return (Vec::new(), format!("kept: {} rlibs beside them", rlibs.len()));
    }
    let rlib_name = rlibs[0].file_name().unwrap_or_default().to_string_lossy().into_owned();
    let Some(members) = ar_members(rlibs[0]) else {
        return (Vec::new(), format!("kept: {rlib_name} is not a readable archive"));
    };
    let mut doomed = Vec::new();
    let mut foreign = 0;
    for object in &unit.objects {
        // Only a Darwin debug map names the archive member; an ELF link with unpacked
        // split DWARF names the loose object itself.
        if !is_macho(object) {
            foreign += 1;
            continue;
        }
        let Ok(meta) = fs::symlink_metadata(object) else { continue };
        let name = object.file_name().unwrap_or_default().to_string_lossy();
        // A Darwin archive pads each member to 8 bytes inside its size field.
        if let Some(&member) = members.get(name.as_ref())
            && (0..8).contains(&(member - meta.len() as i64))
        {
            doomed.push(object.clone());
        }
    }
    if doomed.is_empty() {
        if foreign == unit.objects.len() {
            return (
                Vec::new(),
                "kept: not Mach-O objects, and off Darwin the debug info names them".into(),
            );
        }
        return (Vec::new(), format!("kept: none is a member of {rlib_name}"));
    }
    (doomed, format!("members of {rlib_name}"))
}

// --------------------------------------------------------------------------------------
// The plan, and what refuses it.
// --------------------------------------------------------------------------------------

/// A tree's judgment: every unit, its verdict, and the duplicate objects of the units that
/// stay. Nothing is deleted by making one.
#[derive(Debug)]
pub(crate) struct Plan {
    /// The target tree judged: nothing outside it is ever deleted ([`outside_trees`]).
    pub(crate) tree: PathBuf,
    pub(crate) units: Vec<Unit>,
    pub(crate) verdicts: Vec<Verdict>,
    /// `(unit, its duplicate objects, why)`.
    pub(crate) objects: Vec<(usize, Vec<PathBuf>, String)>,
}

impl Plan {
    /// `(unit, what the plan deletes of it, is it a dead unit)`: dead units, then objects.
    pub(crate) fn unit_paths(&self) -> Vec<(&Unit, Vec<PathBuf>, bool)> {
        let mut out: Vec<(&Unit, Vec<PathBuf>, bool)> = self
            .verdicts
            .iter()
            .filter(|v| v.dead)
            .map(|v| (&self.units[v.unit], self.units[v.unit].paths.clone(), true))
            .collect();
        out.extend(
            self.objects
                .iter()
                .map(|(unit, objects, _)| (&self.units[*unit], objects.clone(), false)),
        );
        out
    }

    pub(crate) fn paths(&self) -> Vec<PathBuf> {
        self.unit_paths().into_iter().flat_map(|(_, paths, _)| paths).collect()
    }

    /// One line per unit and object entry the plan removes, with why.
    pub(crate) fn listing(&self, base: &Path) -> Vec<String> {
        let rel = |path: &Path| path.strip_prefix(base).unwrap_or(path).display().to_string();
        let mut lines: Vec<String> = self
            .verdicts
            .iter()
            .filter(|v| v.dead)
            .map(|v| {
                let unit = &self.units[v.unit];
                format!("dead    {}/{}  {}", rel(&unit.profile), unit.label(), v.reason)
            })
            .collect();
        for (unit, objects, why) in &self.objects {
            let unit = &self.units[*unit];
            lines.push(format!(
                "objects {}/{} ({} .rcgu.o)  {why}",
                rel(&unit.profile),
                unit.label(),
                objects.len()
            ));
        }
        lines
    }
}

/// Judges one tree: paths in, a plan out. `profiles` are the tree's profile directories
/// ([`profile_dirs`]); `streamed` are extra roots (bootstrap: this run's cargo reports).
/// A stamp that cannot be read, or a profile directory that cannot be listed, refuses.
pub(crate) fn plan_tree(
    tree: &Path,
    profiles: &[PathBuf],
    streamed: &[Streamed],
    objects: bool,
) -> Result<Plan, Vec<String>> {
    plan_tree_selected(tree, profiles, streamed, true, objects)
}

fn plan_tree_selected(
    tree: &Path,
    profiles: &[PathBuf],
    streamed: &[Streamed],
    variants: bool,
    objects: bool,
) -> Result<Plan, Vec<String>> {
    let unreadable: Vec<String> = profiles.iter().flat_map(|p| stamp_records(p).1).collect();
    if !unreadable.is_empty() {
        return Err(unreadable);
    }
    let mut units: Vec<Unit> = Vec::new();
    for profile in profiles {
        units.extend(scan_profile(profile).map_err(|error| vec![error])?);
    }
    let roots = find_roots(profiles, &units, streamed).map_err(|error| vec![error])?;
    let mut verdicts = judge_units(&units, &roots);
    if !variants {
        for verdict in &mut verdicts {
            verdict.dead = false;
        }
    }
    let mut planned = Vec::new();
    if objects {
        for verdict in verdicts.iter().filter(|v| !v.dead) {
            let (doomed, why) = duplicate_objects(&units[verdict.unit]);
            if !doomed.is_empty() {
                planned.push((verdict.unit, doomed, why));
            }
        }
    }
    Ok(Plan { tree: tree.to_owned(), units, verdicts, objects: planned })
}

/// `os.path.abspath`: absolute, with `.` and `..` resolved by spelling alone.
fn abspath(path: &Path) -> PathBuf {
    let joined = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir().unwrap_or_default().join(path)
    };
    let mut out = PathBuf::from("/");
    for component in joined.components() {
        match component {
            Component::ParentDir => {
                out.pop();
            }
            Component::Normal(part) => out.push(part),
            _ => {}
        }
    }
    out
}

/// `os.path.realpath`: every link resolved as far as the path exists, the rest appended.
fn realpath(path: &Path) -> PathBuf {
    let absolute = abspath(path);
    let mut tail: Vec<&OsStr> = Vec::new();
    let mut head = absolute.as_path();
    loop {
        if let Ok(real) = fs::canonicalize(head) {
            let mut real = real;
            for part in tail.iter().rev() {
                real.push(part);
            }
            return real;
        }
        match (head.parent(), head.file_name()) {
            (Some(parent), Some(name)) => {
                tail.push(name);
                head = parent;
            }
            _ => return absolute,
        }
    }
}

/// Which of a set of paths a path is or lies under, judged by file identity (device,
/// inode) rather than by spelling.
struct Identities {
    paths: HashMap<(u64, u64), PathBuf>,
    seen: HashMap<PathBuf, Option<(u64, u64)>>,
}

impl Identities {
    fn new(paths: &[PathBuf]) -> Self {
        let mut found = HashMap::new();
        for path in paths {
            if let Ok(meta) = fs::symlink_metadata(path) {
                found.entry((meta.dev(), meta.ino())).or_insert_with(|| path.clone());
            }
        }
        Identities { paths: found, seen: HashMap::new() }
    }

    fn identity(&mut self, path: &Path) -> Option<(u64, u64)> {
        *self
            .seen
            .entry(path.to_owned())
            .or_insert_with(|| fs::metadata(path).ok().map(|m| (m.dev(), m.ino())))
    }

    /// The path of the set that `path` is or lies under, read both as written and with
    /// every link resolved.
    fn enclosing(&mut self, path: &Path) -> Option<PathBuf> {
        let written = abspath(path);
        let real = realpath(path);
        for start in [&written, &real] {
            for candidate in start.ancestors() {
                if let Some(identity) = self.identity(candidate)
                    && let Some(hit) = self.paths.get(&identity)
                {
                    return Some(hit.clone());
                }
            }
        }
        None
    }
}

/// Every stamp record the plan would delete, from every profile directory of every tree:
/// a refusal, independent of how units were judged. The stamps are read again, and each
/// record and every directory above it is compared with the planned paths by device and
/// inode. A stamp that cannot be read refuses too.
pub(crate) fn stamped_in_plan(doomed: &[PathBuf], profiles: &[PathBuf]) -> Vec<String> {
    let mut identities = Identities::new(doomed);
    let mut hits = Vec::new();
    for profile in profiles {
        let (records, unreadable) = stamp_records(profile);
        hits.extend(unreadable);
        for (stamp, record) in records {
            if identities.enclosing(&record).is_some() {
                hits.push(format!("{} names {}", stamp.display(), record.display()));
            }
        }
    }
    hits
}

/// Each planned path that, once every link above it is resolved, does not lie inside its
/// own unit's target tree.
pub(crate) fn outside_trees(plan: &Plan) -> Vec<String> {
    let mut lines = Vec::new();
    let tree = realpath(&plan.tree);
    for (_, paths, _) in plan.unit_paths() {
        for path in paths {
            let parent = realpath(path.parent().unwrap_or(Path::new("/")));
            if parent != tree && !parent.starts_with(&tree) {
                lines.push(format!("{} is outside {}", path.display(), plan.tree.display()));
            }
        }
    }
    lines
}

/// The symlinks inside the sysroots and installed-tool directories of `host_dir`.
fn kept_links(host_dir: &Path) -> Vec<PathBuf> {
    let mut kept: Vec<PathBuf> = ["stage1", "stage2"]
        .iter()
        .map(|name| host_dir.join(name))
        .filter(|path| fs::symlink_metadata(path).is_ok())
        .collect();
    kept.extend(
        INSTALLED_TOOLS
            .iter()
            .map(|name| host_dir.join(name))
            .filter(|path| fs::symlink_metadata(path).is_ok_and(|m| m.is_dir())),
    );
    let mut links = Vec::new();
    let mut stack = kept;
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(&dir).into_iter().flatten().flatten() {
            match entry.file_type() {
                Ok(kind) if kind.is_symlink() => links.push(entry.path()),
                Ok(kind) if kind.is_dir() => stack.push(entry.path()),
                _ => {}
            }
        }
    }
    links
}

/// Each kept link whose target is or lies inside a planned path, by file identity.
fn unsafe_links(links: &[PathBuf], doomed: &[PathBuf]) -> Vec<String> {
    let mut identities = Identities::new(doomed);
    links
        .iter()
        .filter_map(|link| {
            let hit = identities.enclosing(link)?;
            Some(format!("{} links into {}", link.display(), hit.display()))
        })
        .collect()
}

/// The cargo locks of every profile directory of one tree, held while it is judged and
/// pruned, so a cargo started meanwhile waits instead of building into it. Released when
/// dropped.
pub(crate) struct CargoLocks {
    _held: Vec<File>,
}

impl CargoLocks {
    /// Whole-tree maintenance discovers the same at-most-two-level Cargo
    /// layouts relative to the actual held selected directory. It does not
    /// reopen a profile by pathname or follow a replacement parent/symlink.
    /// Every existing named lock is held even in a partial profile layout.
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn acquire_anchored(tree: std::os::fd::BorrowedFd<'_>) -> io::Result<Self> {
        use std::os::fd::AsFd as _;
        fn visit(
            parent: std::os::fd::BorrowedFd<'_>,
            depth: u8,
            held: &mut Vec<File>,
        ) -> io::Result<()> {
            for name in CARGO_LOCKS {
                let before = match space::metadata_at(parent, OsStr::new(name)) {
                    Ok(meta) => meta,
                    Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                    Err(error) => return Err(error),
                };
                if !before.regular() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "Cargo lock is not an original regular file",
                    ));
                }
                let lock = space::open_at(parent, OsStr::new(name), false)?;
                if space::Snapshot::metadata(&lock.metadata()?) != before {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "Cargo lock changed before acquisition",
                    ));
                }
                lock.try_lock().map_err(|error| {
                    io::Error::other(format!("original Cargo lock {name} unavailable: {error}"))
                })?;
                if space::metadata_at(parent, OsStr::new(name))? != before {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "Cargo lock name changed during acquisition",
                    ));
                }
                held.push(lock);
            }
            if depth == 2 {
                return Ok(());
            }
            for name in space::entries(parent)? {
                let before = space::metadata_at(parent, &name)?;
                if before.directory() {
                    let directory = space::open_at(parent, &name, true)?;
                    if space::Snapshot::metadata(&directory.metadata()?) != before {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "Cargo profile directory changed",
                        ));
                    }
                    visit(directory.as_fd(), depth + 1, held)?;
                    if space::metadata_at(parent, &name)? != before
                        || space::Snapshot::metadata(&directory.metadata()?) != before
                    {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "Cargo profile census changed",
                        ));
                    }
                }
            }
            Ok(())
        }
        let mut held = Vec::new();
        visit(tree, 0, &mut held)?;
        Ok(Self { _held: held })
    }

    /// Every lock taken, or each one another process holds or that cannot be judged; none
    /// is kept when any is refused.
    pub(crate) fn acquire(profiles: &[PathBuf]) -> Result<Self, Vec<String>> {
        let mut held = Vec::new();
        let mut busy = Vec::new();
        for profile in profiles {
            for name in CARGO_LOCKS {
                let lock = profile.join(name);
                let meta = match fs::symlink_metadata(&lock) {
                    Ok(meta) => meta,
                    Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                    Err(error) => {
                        busy.push(format!("{} cannot be judged ({error})", lock.display()));
                        continue;
                    }
                };
                // A link or a non-file is not skipped: cargo follows a link and locks what
                // it names, which this would then never probe or hold.
                if !meta.file_type().is_file() {
                    busy.push(format!(
                        "{} is not a regular file, so its holder cannot be judged",
                        lock.display()
                    ));
                    continue;
                }
                let file = match File::open(&lock) {
                    Ok(file) => file,
                    Err(error) => {
                        busy.push(format!(
                            "{} cannot be opened ({error}), so its holder cannot be judged",
                            lock.display()
                        ));
                        continue;
                    }
                };
                match file.try_lock() {
                    Ok(()) => held.push(file),
                    Err(fs::TryLockError::WouldBlock) => busy.push(format!(
                        "{} is locked: a cargo is building in this tree",
                        lock.display()
                    )),
                    Err(fs::TryLockError::Error(error)) => busy.push(format!(
                        "{} cannot be locked ({error}), so its holder cannot be judged",
                        lock.display()
                    )),
                }
            }
        }
        if busy.is_empty() { Ok(CargoLocks { _held: held }) } else { Err(busy) }
    }
}

// --------------------------------------------------------------------------------------
// Deleting.
// --------------------------------------------------------------------------------------

/// What [`remove_units`] removed and freed, and what it could not remove.
#[derive(Debug, Default)]
pub(crate) struct Removal {
    pub(crate) units: usize,
    pub(crate) objects: usize,
    /// Allocated bytes of every file whose last link went.
    pub(crate) bytes: u64,
    pub(crate) failures: Vec<String>,
}

#[cfg(test)]
thread_local! {
    /// Test-only: runs in `remove_path` between its `symlink_metadata` and the removal,
    /// where a walk that opened the path again would follow a link put there, so a test
    /// can swap the path for a link at exactly that point.
    pub(crate) static AFTER_LSTAT: std::cell::Cell<Option<fn(&Path)>> =
        const { std::cell::Cell::new(None) };
}

/// Removes `path` (a file, or a directory and all it holds, following no link), adding
/// the allocated bytes of every file whose last link it removes. A directory goes by
/// `fs::remove_dir_all`, which follows no link even when one replaces a directory while
/// it runs. Its bytes are counted first and kept only when `path` is then still the
/// directory that was judged (same device and inode), so a link put in its place adds
/// nothing; a link that comes and goes while the count runs can still add what it
/// reached, to the reported bytes only. Whether `path` is gone; a failure is listed.
fn remove_path(path: &Path, bytes: &mut u64, failures: &mut Vec<String>) -> bool {
    let Ok(meta) = fs::symlink_metadata(path) else { return true };
    #[cfg(test)]
    if let Some(hook) = AFTER_LSTAT.get() {
        hook(path);
    }
    if meta.file_type().is_dir() {
        let mut held = 0;
        allocated(path, &mut held);
        let judged = fs::symlink_metadata(path).is_ok_and(|now| {
            now.file_type().is_dir() && now.dev() == meta.dev() && now.ino() == meta.ino()
        });
        return match fs::remove_dir_all(path) {
            Ok(()) => {
                if judged {
                    *bytes += held;
                }
                true
            }
            Err(error) => {
                failures.push(format!("{}: {error}", path.display()));
                false
            }
        };
    }
    match fs::remove_file(path) {
        Ok(()) => {
            if meta.nlink() == 1 {
                *bytes += freed(&meta);
            }
            true
        }
        Err(error) => {
            failures.push(format!("{}: {error}", path.display()));
            false
        }
    }
}

/// The allocated bytes of the files under the directory `path` whose only link is there:
/// what removing it frees. It follows no link it lists, but `read_dir` opens a path again,
/// so a link swapped in for a directory it is about to list is followed; `remove_path`
/// therefore keeps the count only while the path is still the directory it judged.
fn allocated(path: &Path, bytes: &mut u64) {
    let Ok(read) = fs::read_dir(path) else { return };
    for entry in read.flatten() {
        let Ok(meta) = fs::symlink_metadata(entry.path()) else { continue };
        if meta.file_type().is_dir() {
            allocated(&entry.path(), bytes);
        } else if meta.nlink() == 1 {
            *bytes += freed(&meta);
        }
    }
}

/// The bytes a file holds on disk (its blocks, else its size).
fn freed(meta: &fs::Metadata) -> u64 {
    match meta.blocks() * 512 {
        0 => meta.len(),
        bytes => bytes,
    }
}

/// The fingerprint directories among a unit's paths: `.fingerprint/<pkg>-<id>` (legacy),
/// or `fingerprint/` inside a new-layout `build/<pkg>/<id>/`.
fn fingerprint_paths(paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut found = Vec::new();
    for path in paths {
        if path.parent().and_then(|p| p.file_name()) == Some(OsStr::new(".fingerprint")) {
            found.push(path.clone());
        } else if fs::symlink_metadata(path.join("fingerprint")).is_ok_and(|m| m.is_dir()) {
            found.push(path.join("fingerprint"));
        }
    }
    found
}

/// The legacy fingerprint directories (`<profile>/.fingerprint/<pkg>-<id>`) of `profile`
/// as they are on disk now, by unit id.
fn legacy_fingerprints(profile: &Path) -> Result<HashMap<String, PathBuf>, String> {
    Ok(entries(&profile.join(".fingerprint"))?
        .into_iter()
        .filter_map(|entry| {
            let name = name_of(&entry);
            let (_, id) = unit_dir_name(&name)?;
            Some((id.to_owned(), entry.path()))
        })
        .collect())
}

/// Deletes each unit's fingerprint first, then the rest of it; a unit whose fingerprint
/// does not go keeps everything else. Cargo trusts a build-script run unit whose
/// fingerprint is intact without looking at its `OUT_DIR`, so a run unit that lost `out/`
/// but kept its fingerprint would fail the dependent build instead of rerunning. The
/// fingerprint is looked for again here, so one the judge did not see goes first too, and
/// a unit whose fingerprint directory cannot be listed keeps everything. A unit is
/// counted only when all of it went, an object only when it went.
pub(crate) fn remove_units(unit_paths: &[(&Unit, Vec<PathBuf>, bool)]) -> Removal {
    let mut removal = Removal::default();
    let mut fingerprints: HashMap<PathBuf, Result<HashMap<String, PathBuf>, String>> =
        HashMap::new();
    for (unit, paths, is_unit) in unit_paths {
        if !*is_unit {
            for path in paths {
                if remove_path(path, &mut removal.bytes, &mut removal.failures) {
                    removal.objects += 1;
                }
            }
            continue;
        }
        let mut first = fingerprint_paths(paths);
        let mut failed = Vec::new();
        let listed = fingerprints
            .entry(unit.profile.clone())
            .or_insert_with(|| legacy_fingerprints(&unit.profile));
        match listed {
            Ok(listed) => {
                if let Some(found) = listed.get(&unit.unit_id)
                    && !first.contains(found)
                {
                    first.push(found.clone());
                }
            }
            Err(error) => failed.push(error.clone()),
        }
        if failed.is_empty() {
            for path in &first {
                remove_path(path, &mut removal.bytes, &mut failed);
                if fs::symlink_metadata(path).is_ok() && failed.is_empty() {
                    failed.push(format!("{}: not fully deleted", path.display()));
                }
            }
        }
        if !failed.is_empty() {
            removal.failures.extend(failed);
            removal
                .failures
                .push(format!("{}: kept the rest, its fingerprint did not go", unit.label()));
            continue;
        }
        let mut whole = true;
        for path in paths.iter().filter(|p| !first.contains(p)) {
            whole &= remove_path(path, &mut removal.bytes, &mut removal.failures);
        }
        if whole {
            removal.units += 1;
        }
    }
    removal
}

// --------------------------------------------------------------------------------------
// The stamp: what a tree was when it was last judged.
// --------------------------------------------------------------------------------------

fn selected_digest(
    tree: &Path,
    profiles: &[PathBuf],
    variants: bool,
    objects: bool,
) -> Option<String> {
    let inputs = tree_digest(tree, profiles)?;
    let mut digest = sha2::Sha256::new();
    digest.update(b"trust-prune-selection/v1");
    digest.update([u8::from(variants), u8::from(objects)]);
    digest.update(inputs.as_bytes());
    Some(format!("{:x}", digest.finalize()))
}

/// A digest of what judging `tree` reads that a build changes: for each profile
/// directory, the identity and modification time of its `.fingerprint`, `deps`, `build`
/// and `examples` directories (a unit made or removed changes one; a new-layout package
/// directory under `build/` is listed too), the bytes of its stamps and uplifted dep-info,
/// and the size and time of its other files and of `examples/`'s uplifted ones. A no-op
/// build rewrites every stamp and dep-info with the same bytes and clones every uplift
/// again with a new inode, so neither time nor inode is read there (measured on m116,
/// 2026-11-06). Missing a change is never a deletion, only a later one: a tree whose
/// digest matches is not judged. `None` when something in it cannot be read: the tree is
/// judged.
pub(crate) fn tree_digest(tree: &Path, profiles: &[PathBuf]) -> Option<String> {
    let mut hasher = sha2::Sha256::new();
    let mut line = |text: String| {
        hasher.update(text.as_bytes());
        hasher.update(b"\n");
    };
    let tree_meta = fs::symlink_metadata(tree).ok()?;
    line(format!("{STAMP_SCHEMA} {} {}", tree_meta.dev(), tree_meta.ino()));
    let stat = |path: &Path| match fs::symlink_metadata(path) {
        Ok(meta) => format!("{} {} {}", file_kind(&meta), meta.ino(), mtime_ns(&meta)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => "absent".to_owned(),
        Err(error) => format!("error {error}"),
    };
    for profile in profiles {
        let rel = profile.strip_prefix(tree).unwrap_or(profile);
        line(format!("profile {}", rel.display()));
        for sub in [".fingerprint", "deps", "build", "examples"] {
            line(format!("dir {sub} {}", stat(&profile.join(sub))));
        }
        let mut listing: Vec<fs::DirEntry> = fs::read_dir(profile).ok()?.flatten().collect();
        listing.sort_by_key(|entry| entry.file_name());
        for entry in listing {
            let name = entry.file_name();
            let bytes = name.as_bytes();
            let meta = fs::symlink_metadata(entry.path()).ok()?;
            if meta.file_type().is_dir() {
                continue;
            }
            let roots =
                (bytes.starts_with(b".") && bytes.ends_with(b"stamp")) || bytes.ends_with(b".d");
            if roots && meta.file_type().is_file() {
                // A stamp or an uplifted dep-info: bootstrap and cargo rewrite both on every
                // run, so their time always moves; their bytes say which units they name.
                let content = fs::read(entry.path()).ok()?;
                line(format!(
                    "roots {} {:x}",
                    name.to_string_lossy(),
                    sha2::Sha256::digest(&content)
                ));
            } else {
                // An uplift: cargo clones it again on every run (a new inode, the same size
                // and time), so its inode says nothing.
                line(format!(
                    "file {} {} {} {}",
                    name.to_string_lossy(),
                    file_kind(&meta),
                    meta.len(),
                    mtime_ns(&meta)
                ));
            }
        }
        for entry in entries(&profile.join("examples")).ok()? {
            let name = name_of(&entry);
            if artifact_name(&name).is_some() {
                continue;
            }
            let meta = fs::symlink_metadata(entry.path()).ok()?;
            line(format!("example {name} {} {}", meta.len(), mtime_ns(&meta)));
        }
        for entry in entries(&profile.join("build")).ok()? {
            let name = name_of(&entry);
            if unit_dir_name(&name).is_some() || !is_dir_entry(&entry) {
                continue;
            }
            let meta = fs::symlink_metadata(entry.path()).ok()?;
            line(format!("package {name} {} {}", meta.ino(), mtime_ns(&meta)));
        }
    }
    Some(format!("{:x}", hasher.finalize()))
}

fn file_kind(meta: &fs::Metadata) -> &'static str {
    let kind = meta.file_type();
    if kind.is_dir() {
        "dir"
    } else if kind.is_file() {
        "file"
    } else if kind.is_symlink() {
        "link"
    } else if kind.is_fifo() {
        "fifo"
    } else {
        "other"
    }
}

/// The digest `tree`'s stamp records, when it is one this prune wrote.
pub(crate) fn read_stamp(tree: &Path) -> Option<String> {
    let path = tree.join(STAMP);
    let meta = fs::symlink_metadata(&path).ok()?;
    if !meta.file_type().is_file() || meta.len() > 4096 {
        return None;
    }
    let text = fs::read_to_string(path).ok()?;
    let mut lines = text.lines();
    (lines.next() == Some(STAMP_SCHEMA)).then(|| lines.next().map(str::to_owned)).flatten()
}

fn write_stamp(tree: &Path, digest: &str) -> io::Result<()> {
    let partial = tree.join(format!("{STAMP}.partial-{}", std::process::id()));
    fs::write(&partial, format!("{STAMP_SCHEMA}\n{digest}\n"))?;
    fs::rename(&partial, tree.join(STAMP)).inspect_err(|_| {
        let _ = fs::remove_file(&partial);
    })
}

#[cfg(test)]
mod tests;
