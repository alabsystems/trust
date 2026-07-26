// The rewrite loop's undo path.
//
// Every iteration that writes to the user's source leaves behind exactly one
// generation of edits that no compiler has looked at yet. That generation is
// held here, together with the pre-apply content of every file it touched,
// until a later prove pass either accepts it or this module puts the files
// back. A repair tool that can edit source but cannot re-judge or undo the
// edit is the one failure mode that costs the user more than it gives them.

use trust_backprop::{RewriteCheckpoint, rollback};

use super::convergence::LoopDecision;

/// Source edits that are on disk but have not been judged by a compiler run.
pub(crate) struct UnverifiedRewrites {
    /// One-based iteration that wrote these edits, for operator messages.
    iteration: usize,
    /// Pre-apply content of every file the iteration wrote.
    checkpoint: RewriteCheckpoint,
    /// How many rewrites the iteration applied.
    rewrites: usize,
}

impl UnverifiedRewrites {
    pub(crate) fn new(
        iteration: usize,
        checkpoint: RewriteCheckpoint,
        rewrites: usize,
    ) -> Option<Self> {
        // A checkpoint with no files describes no edit to take back.
        if checkpoint.is_empty() {
            return None;
        }
        Some(Self { iteration, checkpoint, rewrites })
    }

    pub(crate) fn iteration(&self) -> usize {
        self.iteration
    }

    pub(crate) fn rewrites(&self) -> usize {
        self.rewrites
    }

    pub(crate) fn file_count(&self) -> usize {
        self.checkpoint.file_count()
    }

    /// Put every file back to the content it had before this generation was
    /// written, verifying each restored file against its recorded digest.
    pub(crate) fn restore(self) -> Result<usize, String> {
        let files = self.checkpoint.file_count();
        rollback(&self.checkpoint).map(|()| files).map_err(|error| error.to_string())
    }
}

/// Why a generation of applied rewrites must not survive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RewriteRejection {
    /// The rewritten source produced no verifiable artifact at all.
    BrokenBuild,
    /// The rewritten source still builds, but proves strictly less.
    RegressedFrontier(&'static str),
}

impl RewriteRejection {
    pub(crate) fn reason(self) -> &'static str {
        match self {
            Self::BrokenBuild => "rewritten source produced no verification obligations",
            Self::RegressedFrontier(reason) => reason,
        }
    }
}

/// Judge the generation of rewrites that the run being reported here compiled.
///
/// The build check is not a courtesy: a rewrite that stops the crate from
/// compiling reports *zero* obligations, and zero failing obligations reads to
/// any frontier comparison as an improvement. Without this test the loop would
/// treat a broken build as its best result yet.
pub(crate) fn rewrite_rejection(
    compiler_exit: i32,
    obligations: usize,
    decision: &LoopDecision,
) -> Option<RewriteRejection> {
    if compiler_exit != 0 && obligations == 0 {
        return Some(RewriteRejection::BrokenBuild);
    }
    match decision {
        LoopDecision::Regressed { reason } => Some(RewriteRejection::RegressedFrontier(reason)),
        LoopDecision::Continue { .. }
        | LoopDecision::Converged { .. }
        | LoopDecision::IterationLimitReached => None,
    }
}

/// Operator-facing line describing an undo.
pub(crate) fn describe_restore(
    pending: &UnverifiedRewrites,
    rejection: RewriteRejection,
) -> String {
    format!(
        "  Reverting iteration {}'s {} rewrite(s) across {} file(s): {}",
        pending.iteration(),
        pending.rewrites(),
        pending.file_count(),
        rejection.reason(),
    )
}
