//! Trust: manual cache maintenance uses the production Bootstrap prune engine.
//!
//! Paths and previews are observations. Mutation requires the actual independent
//! repository lease and original output lock throughout judging and deletion.

use std::path::{Component, Path, PathBuf};

use build_helper::trust_output_lock::OutputLock;
use build_helper::trust_repo_lock::management::Lease;
use serde_derive::Serialize;

pub use crate::utils::trust_prune::space::{Estimate as SpaceEstimate, VolumeChange};
use crate::utils::trust_prune::{self, Options, Ownership};

mod output;
pub use output::SelectedOutput;

#[cfg(any(all(feature = "native-cache-exec", target_os = "macos", target_arch = "aarch64"), test))]
mod whole;
#[cfg(all(feature = "native-cache-exec", target_os = "macos", target_arch = "aarch64"))]
pub use whole::reclaim;
#[cfg(any(
    all(feature = "native-cache-exec", target_os = "macos", target_arch = "aarch64"),
    test
))]
pub use whole::{WholeProfile, WholeReport, WholeRequest};

/// A selected operation, never ownership or an installed-SDK assertion.
pub struct Request {
    selection: SelectedOutput,
    root: PathBuf,
    build: PathBuf,
    host: PathBuf,
    variants: bool,
    objects: bool,
    dry_run: bool,
}

impl Request {
    pub fn new(
        root: &Path,
        host: &Path,
        variants: bool,
        objects: bool,
        dry_run: bool,
    ) -> Result<Self, String> {
        Self::from_selection(SelectedOutput::capture(root)?, host, variants, objects, dry_run)
    }

    pub fn from_selection(
        selection: SelectedOutput,
        host: &Path,
        variants: bool,
        objects: bool,
        dry_run: bool,
    ) -> Result<Self, String> {
        if !variants && !objects {
            return Err("cache pruning requires superseded variants or duplicate objects".into());
        }
        let (root, build, host) = location(&selection, host)?;
        Ok(Self { selection, root, build, host, variants, objects, dry_run })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn output(&self) -> &Path {
        &self.build
    }
}

fn location(
    selection: &SelectedOutput,
    host: &Path,
) -> Result<(PathBuf, PathBuf, PathBuf), String> {
    if host.components().count() != 1
        || !matches!(host.components().next(), Some(Component::Normal(_)))
    {
        return Err("cache host must be one target name, never a path".into());
    }
    selection.check_current()?;
    let root = selection.root().to_owned();
    let build = selection.output().to_owned();
    let host = build.join(host);
    if !host.is_dir() {
        return Err(format!("cache host directory is unavailable: {}", host.display()));
    }
    Ok((root, build, host))
}

/// Structured observations of planning and actual removal, kept separate.
#[derive(Debug, Serialize)]
pub struct Report {
    pub dry_run: bool,
    pub target_trees: usize,
    pub judged: usize,
    pub unchanged: usize,
    pub skipped: Vec<(PathBuf, String)>,
    pub planned_units: usize,
    pub planned_objects: usize,
    pub removed_units: usize,
    pub removed_objects: usize,
    /// Allocated blocks whose last directory link was removed. APFS clone
    /// sharing means this is not a measurement of volume space gained.
    pub removed_allocated_bytes: u64,
    /// Snapshot of the approved plan; clone sharing and outside hard links
    /// are accounted separately from observed volume availability.
    pub planned_file_space: Option<SpaceEstimate>,
    pub volume_space: Option<VolumeChange>,
    /// Missing observations never become zero or authorize deletion.
    pub space_observation_errors: Vec<String>,
    pub listing: Vec<String>,
    pub failures: Vec<String>,
}

impl Report {
    pub fn is_complete(&self) -> bool {
        self.skipped.is_empty() && self.failures.is_empty()
    }
}

/// Retain the same real guards through the production judge and cleanup.
/// Preview takes the same exclusion and all the same deletion refusals; it
/// deletes nothing and never stamps a tree as cleaned.
pub fn prune(request: &Request, lease: &Lease, output: &OutputLock) -> Result<Report, String> {
    request.selection.check_current()?;
    let directory = output.original_directory().map_err(|error| error.to_string())?;
    let (mut summary, volume_space, volume_error) =
        Ownership::native(output, lease).with_current(&request.root, &request.build, || {
            let volume = trust_prune::space::VolumeBefore::capture(directory);
            let revalidate = || request.selection.check_current();
            let summary = trust_prune::prune_selected_measured(
                &request.build,
                &request.host,
                &[],
                &Options { objects: request.objects, observe: None },
                request.variants,
                request.dry_run,
                trust_prune::ManualObservation { directory, revalidate: Some(&revalidate) },
            );
            let (volume_space, volume_error) = match volume.and_then(|before| before.finish()) {
                Ok(observation) => (Some(observation), None),
                Err(error) => (None, Some(error.to_string())),
            };
            (summary, volume_space, volume_error)
        })?;
    if let Some(error) = volume_error {
        summary.space_observation_errors.push(error);
    }
    finish_selection(&request.selection, &mut summary.failures);
    Ok(Report {
        dry_run: request.dry_run,
        target_trees: summary.trees,
        judged: summary.judged,
        unchanged: summary.unchanged,
        skipped: summary.skipped,
        planned_units: summary.planned_units,
        planned_objects: summary.planned_objects,
        removed_units: summary.units,
        removed_objects: summary.objects,
        removed_allocated_bytes: summary.bytes,
        planned_file_space: summary.space_estimate,
        volume_space,
        space_observation_errors: summary.space_observation_errors,
        listing: summary.listing,
        failures: summary.failures,
    })
}

fn finish_selection(selection: &SelectedOutput, failures: &mut Vec<String>) {
    if let Err(error) = selection.check_current() {
        // Mutation already happened: refuse success while preserving every
        // actual/planned outcome. A postcheck never erases removal evidence.
        failures.push(error);
    }
}
