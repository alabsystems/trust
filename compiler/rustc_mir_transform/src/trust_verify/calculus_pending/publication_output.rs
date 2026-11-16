//! Trust: ordered, already-prepared presentation DATA only. Original live
//! spans stay in the caller's private table; borrowed text is streamed into
//! the spool before the caller releases its original prepared actions.
//!
//! This leaf neither emits output nor chooses an alternative. The enclosing
//! private Saved/pair handle must check its original-write commitment and the
//! actual body/owed-row identity before decoding/restoring any record. A DATA
//! failure preserves that caller's fallback and full debt; it is never success.

use std::io;

use super::super::{PreparedLocatedDiagnostic, PreparedLocatedNote};
use super::diagnostic_data::{
    IndexedDiagnostic, IndexedDiagnosticRef, IndexedNote, IndexedNoteRef, LiveSpans,
};

/// Already-prepared live presentation actions. Real Spans are deliberately
/// not serializable here. This enum contains no private proof/grade selector
/// and offers no emitter; the parent prepares the original effects once.
pub(in crate::trust_verify) enum PreparedAction {
    Diagnostic(PreparedLocatedDiagnostic),
    // The original private cause is live only through paired preparation.
    // Saved DATA has the same ordinary Diagnostic wire variant; decoding
    // cannot restore this cause or make another candidate-eligibility fact.
    FullFailure {
        span: rustc_span::Span,
        failure: super::super::publication_failure::PreparedFullFailure,
    },
    // Tagged at the original sole L0-row publisher. It is never decoded as a
    // waivable fact; a proposed delta additionally needs complete private
    // original native/member coverage and the untouched independent floors.
    LevelZeroRowFailure(PreparedLocatedDiagnostic),
    Note(PreparedLocatedNote),
    Stderr(String),
}

/// Serialize a view of the original action sequence without copying its bulk
/// strings. All reservations and actual span capture can refuse while the
/// caller still owns every original action for its ordinary fallback.
pub(super) fn capture<'a>(
    actual: &mut LiveSpans,
    original: &'a [PreparedAction],
) -> io::Result<PreparedEmissionRef<'a>> {
    capture_refs(actual, original.iter())
}

/// Overlay an alternative with borrowed original actions. The owner supplies
/// the exact ordered references after its live cause/debt checks; no bulk text
/// clone and no serializer/grade authority is introduced by this adapter.
pub(super) fn capture_refs<'a>(
    actual: &mut LiveSpans,
    original: impl ExactSizeIterator<Item = &'a PreparedAction>,
) -> io::Result<PreparedEmissionRef<'a>> {
    let mut actions = Vec::new();
    actions.try_reserve(original.len()).map_err(io::Error::other)?;
    for action in original {
        actions.push(match action {
            PreparedAction::Diagnostic(diagnostic) => {
                IndexedActionRef::Diagnostic(actual.capture(diagnostic)?)
            }
            PreparedAction::LevelZeroRowFailure(diagnostic) => {
                IndexedActionRef::Diagnostic(actual.capture(diagnostic)?)
            }
            PreparedAction::FullFailure { span, failure } => {
                IndexedActionRef::Diagnostic(actual.capture_diagnostic_parts(
                    *span, failure.diagnostic(),
                )?)
            }
            PreparedAction::Note(note) => IndexedActionRef::Note(actual.capture_note(note)?),
            PreparedAction::Stderr(text) => IndexedActionRef::Stderr(text),
        });
    }
    Ok(PreparedEmissionRef { actions })
}

#[derive(serde::Serialize)]
pub(super) struct PreparedEmissionRef<'a> {
    actions: Vec<IndexedActionRef<'a>>,
}

// Variant spelling and shape match the owned DATA enum below exactly. In
// particular a primary NOTE stays distinct from an Error/Warning diagnostic.
#[derive(serde::Serialize)]
enum IndexedActionRef<'a> {
    Diagnostic(IndexedDiagnosticRef<'a>),
    Note(IndexedNoteRef<'a>),
    Stderr(&'a str),
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct PreparedEmission {
    actions: Vec<IndexedAction>,
}

#[derive(serde::Deserialize)]
enum IndexedAction {
    Diagnostic(IndexedDiagnostic),
    Note(IndexedNote),
    Stderr(String),
}

impl PreparedEmission {
    /// Resolve the ENTIRE sequence against the same actual private table
    /// before returning any actions. On a late refusal the private partial
    /// vector is dropped; no emitter or callback has observed a prefix.
    pub(super) fn restore(self, actual: &LiveSpans) -> io::Result<Vec<PreparedAction>> {
        let mut actions = Vec::new();
        actions.try_reserve(self.actions.len()).map_err(io::Error::other)?;
        for action in self.actions {
            actions.push(match action {
                IndexedAction::Diagnostic(diagnostic) => {
                    PreparedAction::Diagnostic(diagnostic.restore(actual)?)
                }
                IndexedAction::Note(note) => PreparedAction::Note(note.restore(actual)?),
                IndexedAction::Stderr(text) => PreparedAction::Stderr(text),
            });
        }
        Ok(actions)
    }
}


// Authored source controls only. No execution/qualification is implied by
// their presence, and none constructs verification or policy authority.
#[cfg(test)]
mod tests;
