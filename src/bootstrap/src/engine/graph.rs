//! Closed native leaves borrowing ONE still-open engine Outcome.
//! These observations grant no CPU, foreign retirement, SDK, proof or release.

use std::path::PathBuf;
use std::time::Instant;
use std::{fmt, io};

use super::Outcome;

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod native;
mod task;
pub use task::{CompletedTask, TaskCompletion, TaskError, TaskFailure, TaskInputs};

#[derive(Debug)]
pub enum GraphError {
    InvalidReadSet(&'static str),
    InvalidDependencies(&'static str),
    WrongOwner,
    WrongDependencyOwner,
    InputChanged(PathBuf),
    OriginalOwner(String),
    Io(io::Error),
}
impl fmt::Display for GraphError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidReadSet(reason) => write!(f, "native read set refused: {reason}"),
            Self::InvalidDependencies(reason) => {
                write!(f, "native task dependencies refused: {reason}")
            }
            Self::WrongOwner => f.write_str("native inputs belong to another original Outcome"),
            Self::WrongDependencyOwner => {
                f.write_str("native task predecessor belongs to another original Outcome")
            }
            Self::InputChanged(path) => {
                write!(f, "original selected input changed: {}", path.display())
            }
            Self::OriginalOwner(reason) => write!(f, "original graph custody refused: {reason}"),
            Self::Io(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for GraphError {}
impl From<io::Error> for GraphError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// Exact selected-file observations, not a whole source/SDK/ABI judgment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputObservation {
    pub path: PathBuf,
    pub bytes: u64,
    pub sha256: [u8; 32],
}

/// Retains real readonly descriptions AND a borrow of their original Outcome.
/// No path, record, digest, observation or deserializer constructs this type.
pub struct CapturedInputs<'owner> {
    owner: &'owner Outcome,
    observations: Vec<InputObservation>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    native: native::Inputs,
}
impl CapturedInputs<'_> {
    pub fn observations(&self) -> &[InputObservation] {
        &self.observations
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputPair {
    pub left: InputObservation,
    pub right: InputObservation,
    pub same_digest: bool,
}

/// Data from actual captures, reads and revalidation. This is not completion
/// of producing/foreign work and cannot settle the still-open owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comparison {
    pub pairs: Vec<InputPair>,
    pub all_digests_match: bool,
}

/// A non-Clone borrow: it never exports the underlying scope/dispatcher/guard.
pub struct OpenGraph<'owner> {
    owner: &'owner Outcome,
}

impl Outcome {
    pub fn open_native_graph(&self) -> Result<OpenGraph<'_>, GraphError> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            native::check_owner(self)?;
            Ok(OpenGraph { owner: self })
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        Err(unavailable())
    }

    /// An actual native comparison caller, not a textual plan. Three native
    /// worker regions use this SAME open owner and original serialization.
    /// Paths are relative selected inputs in the original source root; paired
    /// positions are explicit comparison data, never artifact admission.
    pub fn compare_source_inputs(
        &self,
        left: &[PathBuf],
        right: &[PathBuf],
        deadline: Instant,
    ) -> Result<Comparison, GraphError> {
        let graph = self.open_native_graph()?;
        let left = graph.capture_inputs(left, deadline)?;
        let right = graph.capture_inputs(right, deadline)?;
        graph.compare_inputs(&left, &right, deadline)
    }
}

impl<'owner> OpenGraph<'owner> {
    /// Trust: retain the complete bounded namespace of ONE selected package
    /// subtree beneath the original source, including empty directories. No
    /// target/cache/hidden entries are excluded. Symlinks and special entries
    /// refuse, as do overlapping original outputs or descriptor/depth bounds.
    /// This is not arbitrary Rust dependency closure or a source/SDK freeze.
    /// The returned SAME inputs enter run_source_task and its recursive native
    /// predecessor bookends; directory membership remains a live restriction.
    pub fn capture_source_tree(
        &self,
        subtree: &std::path::Path,
        deadline: Instant,
    ) -> Result<CapturedInputs<'owner>, GraphError> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            native::tree::capture(self.owner, subtree, deadline)
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = (subtree, deadline);
            Err(unavailable())
        }
    }

    /// Capture a nonempty, bounded selection; never infer whole-root coverage.
    pub fn capture_inputs(
        &self,
        paths: &[PathBuf],
        deadline: Instant,
    ) -> Result<CapturedInputs<'owner>, GraphError> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            native::capture(self.owner, paths, deadline)
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = (paths, deadline);
            Err(unavailable())
        }
    }

    pub fn revalidate(
        &self,
        inputs: &CapturedInputs<'_>,
        deadline: Instant,
    ) -> Result<(), GraphError> {
        if !std::ptr::eq(self.owner, inputs.owner) {
            return Err(GraphError::WrongOwner);
        }
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            native::revalidate(self.owner, inputs, deadline)
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = deadline;
            Err(unavailable())
        }
    }

    pub fn compare_inputs(
        &self,
        left: &CapturedInputs<'_>,
        right: &CapturedInputs<'_>,
        deadline: Instant,
    ) -> Result<Comparison, GraphError> {
        if !std::ptr::eq(self.owner, left.owner) || !std::ptr::eq(self.owner, right.owner) {
            return Err(GraphError::WrongOwner);
        }
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            native::compare(self.owner, left, right, deadline)
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = deadline;
            Err(unavailable())
        }
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn unavailable() -> GraphError {
    io::Error::new(io::ErrorKind::Unsupported, "native graph input work is unavailable").into()
}
