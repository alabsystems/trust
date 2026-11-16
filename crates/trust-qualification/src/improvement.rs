//! Source observations for a native repair iteration. Agent output is a proposal:
//! only independently observed Git objects and working bytes make a candidate.
//! These owners grant no compiler, SDK, proof, execution or publication rights.

use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Component, Path, PathBuf};

use crate::source::{self, SourceIdentity};
use crate::{Git, Result, canonical_hex, refusal, tree};

mod measurement;
pub use measurement::{MeasuredBottleneck, Measurements, RunningWork};
pub mod comparison;
pub mod workload;

const MAX_FILES: usize = 128;
const MAX_BYTES: u64 = 16 * 1024 * 1024;

struct Root {
    path: PathBuf,
    descriptor: File,
    identity: (u64, u64),
}
impl Root {
    fn open(path: &Path) -> Result<Self> {
        if !path.is_absolute() || fs::canonicalize(path)? != path {
            return Err(refusal("repair root must be an exact canonical directory"));
        }
        let descriptor = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path)?;
        let metadata = descriptor.metadata()?;
        let root =
            Self { path: path.into(), descriptor, identity: (metadata.dev(), metadata.ino()) };
        root.check()?;
        Ok(root)
    }
    fn check(&self) -> Result<()> {
        let original = self.descriptor.metadata()?;
        let current = fs::symlink_metadata(&self.path)?;
        if !current.is_dir()
            || fs::canonicalize(&self.path)? != self.path
            || (original.dev(), original.ino()) != self.identity
            || (current.dev(), current.ino()) != self.identity
        {
            return Err(refusal("original repair root directory changed"));
        }
        Ok(())
    }
}

/// Pins one original clean control checkout and a distinct candidate checkout.
/// The agent may change only the preselected regular files in the candidate.
/// No command, prompt, saved report or agent completion flag creates this owner.
/// These readonly pins do NOT exclude writers or freeze source during a build.
/// Execution additionally needs the real independent repository lease/protected
/// scope and output exclusion, or an immutable owned build-input snapshot.
pub struct RepairCheckout {
    baseline: Root,
    candidate: Root,
    original: SourceIdentity,
    initial_candidate: SourceIdentity,
    selected: BTreeSet<PathBuf>,
}

/// A failed submission retains the actual original directories. Failure never
/// becomes a successfully repaired/qualified iteration or automatic rollback.
pub struct RejectedRepair {
    pub reason: crate::Refusal,
    pub checkout: RepairCheckout,
}

/// Independently observed proposed source. It is deliberately non-Clone and
/// has no deserializer, successful-build flag, proof grade or landing method.
pub struct ProposedRepair {
    checkout: RepairCheckout,
    source: SourceIdentity,
    changed: Vec<PathBuf>,
}

/// A consumed measured selection and the retained original source observations
/// awaiting proposed source from an authenticated native agent connection.
/// It has no method that interprets agent text as a command or a passed gate.
pub struct AwaitingRepair {
    bottleneck: MeasuredBottleneck,
    checkout: RepairCheckout,
}
pub struct MeasuredRepair {
    bottleneck: MeasuredBottleneck,
    proposal: ProposedRepair,
}
impl AwaitingRepair {
    pub fn new(bottleneck: MeasuredBottleneck, checkout: RepairCheckout) -> Self {
        Self { bottleneck, checkout }
    }
    pub fn bottleneck(&self) -> &MeasuredBottleneck {
        &self.bottleneck
    }
    pub fn checkout(&self) -> &RepairCheckout {
        &self.checkout
    }
    /// The reply remains untrusted data; the same independent source checks
    /// apply whether it came from an agent, a file or a human.
    pub fn observe_proposed_commit(
        self,
        git: &impl Git,
        commit: &str,
    ) -> std::result::Result<MeasuredRepair, (MeasuredBottleneck, Box<RejectedRepair>)> {
        match self.checkout.submit(git, commit) {
            Ok(proposal) => Ok(MeasuredRepair { bottleneck: self.bottleneck, proposal }),
            Err(rejected) => Err((self.bottleneck, rejected)),
        }
    }
}
impl MeasuredRepair {
    pub fn bottleneck(&self) -> &MeasuredBottleneck {
        &self.bottleneck
    }
    pub fn proposal(&self) -> &ProposedRepair {
        &self.proposal
    }
    // No build/verify/test/compare/land transition exists until a genuine
    // protected graph/SDK owner can consume this SAME source. In particular,
    // there is no setter taking a Boolean, status report or claimed proof grade.
}

impl RepairCheckout {
    pub fn open(
        git: &impl Git,
        baseline: &Path,
        candidate: &Path,
        selected: &[PathBuf],
    ) -> Result<Self> {
        let baseline = Root::open(baseline)?;
        let candidate = Root::open(candidate)?;
        if baseline.identity == candidate.identity
            || baseline.path.starts_with(&candidate.path)
            || candidate.path.starts_with(&baseline.path)
        {
            return Err(refusal("repair control and candidate directories must be disjoint"));
        }
        if selected.is_empty() || selected.len() > MAX_FILES {
            return Err(refusal("repair must select between one and 128 original files"));
        }
        let mut paths = BTreeSet::new();
        for relative in selected {
            if relative.as_os_str().is_empty()
                || relative.components().any(|c| !matches!(c, Component::Normal(_)))
                || !paths.insert(relative.clone())
            {
                return Err(refusal("repair selection has duplicate or noncanonical paths"));
            }
            for root in [&baseline, &candidate] {
                let path = tree::no_link_ancestors(&root.path, relative)?;
                if !fs::symlink_metadata(path)?.is_file() {
                    return Err(refusal("repair selection must name original regular files"));
                }
            }
        }
        let original = source::identity(git, &baseline.path, false, false)?;
        let initial_candidate = source::identity(git, &candidate.path, false, false)?;
        if original.commit != initial_candidate.commit
            || original.tree != initial_candidate.tree
            || original.working_sha256 != initial_candidate.working_sha256
        {
            return Err(refusal(
                "repair candidate does not start with the complete original source",
            ));
        }
        let checkout = Self { baseline, candidate, original, initial_candidate, selected: paths };
        checkout.check_initial(git)?;
        Ok(checkout)
    }

    pub fn baseline(&self) -> &SourceIdentity {
        &self.original
    }
    pub fn candidate_root(&self) -> &Path {
        &self.candidate.path
    }
    pub fn selected_paths(&self) -> impl Iterator<Item = &Path> {
        self.selected.iter().map(PathBuf::as_path)
    }
    fn check_control(&self, git: &impl Git) -> Result<()> {
        self.baseline.check()?;
        self.candidate.check()?;
        if source::identity(git, &self.baseline.path, false, false)? != self.original {
            return Err(refusal("original control source changed during repair"));
        }
        Ok(())
    }
    pub fn check_initial(&self, git: &impl Git) -> Result<()> {
        self.check_control(git)?;
        if source::identity(git, &self.candidate.path, false, false)? != self.initial_candidate {
            return Err(refusal("candidate changed before native repair submission"));
        }
        Ok(())
    }

    /// The agent supplies only the proposed commit name. Independently bind the
    /// complete clean source, sole original parent and exact bounded change set.
    /// This method never runs agent text, applies a patch, or mutates either tree.
    pub fn submit(
        self,
        git: &impl Git,
        proposed_commit: &str,
    ) -> std::result::Result<ProposedRepair, Box<RejectedRepair>> {
        let observed = self.observe_proposal(git, proposed_commit);
        match observed {
            Ok((source, changed)) => Ok(ProposedRepair { checkout: self, source, changed }),
            Err(reason) => Err(Box::new(RejectedRepair { reason, checkout: self })),
        }
    }
    fn observe_proposal(
        &self,
        git: &impl Git,
        proposed_commit: &str,
    ) -> Result<(SourceIdentity, Vec<PathBuf>)> {
        if !canonical_hex(proposed_commit, 40) {
            return Err(refusal("agent proposal is not a canonical commit identity"));
        }
        self.check_control(git)?;
        let parents =
            git.probe(&self.candidate.path, &["rev-list", "--parents", "-n", "1", "HEAD"])?;
        let expected = format!("{} {}\n", proposed_commit, self.original.commit);
        if parents != expected.as_bytes() {
            return Err(refusal("repair must be one commit with the sole original source parent"));
        }
        let diff = git.probe(
            &self.candidate.path,
            &[
                "diff-tree",
                "--no-commit-id",
                "--name-only",
                "--no-renames",
                "-r",
                "-z",
                &self.original.commit,
                proposed_commit,
            ],
        )?;
        let body =
            diff.strip_suffix(&[0]).ok_or_else(|| refusal("repair diff has no terminal NUL"))?;
        let mut changed = BTreeSet::new();
        let mut bytes = 0u64;
        for row in body.split(|b| *b == 0) {
            use std::os::unix::ffi::OsStrExt;
            let relative = PathBuf::from(std::ffi::OsStr::from_bytes(row));
            if !self.selected.contains(&relative) || !changed.insert(relative.clone()) {
                return Err(refusal("repair changes an unselected or duplicate source path"));
            }
            let path = tree::no_link_ancestors(&self.candidate.path, &relative)?;
            let metadata = fs::symlink_metadata(&path)?;
            if !metadata.is_file() {
                return Err(refusal("repair removes or replaces an original regular file"));
            }
            bytes =
                bytes.checked_add(metadata.len()).ok_or_else(|| refusal("repair size overflow"))?;
            if bytes > MAX_BYTES {
                return Err(refusal("repair proposed source exceeds 16 MiB"));
            }
        }
        if changed.is_empty() {
            return Err(refusal("repair contains no selected source changes"));
        }
        let source = source::identity(git, &self.candidate.path, false, false)?;
        if source.commit != proposed_commit || source.tree == self.original.tree {
            return Err(refusal(
                "agent proposal differs from actual candidate or changes no source",
            ));
        }
        self.check_control(git)?;
        if source::identity(git, &self.candidate.path, false, false)? != source {
            return Err(refusal("candidate source changed during proposal inspection"));
        }
        Ok((source, changed.into_iter().collect()))
    }
}
impl ProposedRepair {
    pub fn source(&self) -> &SourceIdentity {
        &self.source
    }
    pub fn baseline(&self) -> &SourceIdentity {
        self.checkout.baseline()
    }
    pub fn changed_paths(&self) -> &[PathBuf] {
        &self.changed
    }
    pub fn check_unchanged(&self, git: &impl Git) -> Result<()> {
        self.checkout.check_control(git)?;
        if source::identity(git, &self.checkout.candidate.path, false, false)? != self.source {
            return Err(refusal("proposed repair source changed before qualification"));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
