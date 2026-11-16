//! Bulk diagnostic text is DATA. Actual source spans stay in a private live
//! table; stored indices cannot reconstruct a Span or any proof authority.
//! The enclosing committed body/pair handle still owns selection and debt.

use super::*;
use std::io;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TABLE: AtomicU64 = AtomicU64::new(0);

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// Small typed presentation provenance only: no VC, native run, proof, source
/// function or verification context is retained. A table cannot be cloned,
/// deserialized or supplied by a report/hint producer.
pub(super) struct LiveSpans {
    id: u64,
    indices: FxHashMap<rustc_span::Span, usize>,
    values: Vec<rustc_span::Span>,
}

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct IndexedSpan {
    table: u64,
    span: usize,
}

impl LiveSpans {
    pub(super) fn new() -> io::Result<Self> {
        let id = NEXT_TABLE.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map_err(|_| invalid("diagnostic span table identity exhausted"))?;
        Ok(Self { id, indices: FxHashMap::default(), values: Vec::new() })
    }

    fn intern(&mut self, span: rustc_span::Span) -> io::Result<usize> {
        if let Some(index) = self.indices.get(&span) {
            return Ok(*index);
        }
        self.values.try_reserve(1).map_err(io::Error::other)?;
        self.indices.try_reserve(1).map_err(io::Error::other)?;
        let index = self.values.len();
        self.values.push(span);
        self.indices.insert(span, index);
        Ok(index)
    }

    pub(super) fn capture_span(&mut self, span: rustc_span::Span) -> io::Result<IndexedSpan> {
        Ok(IndexedSpan { table: self.id, span: self.intern(span)? })
    }

    pub(super) fn restore_span(&self, saved: &IndexedSpan) -> io::Result<rustc_span::Span> {
        if saved.table != self.id {
            return Err(invalid("presentation span belongs to another live table"));
        }
        self.values.get(saved.span).copied()
            .ok_or_else(|| invalid("presentation span is outside its live table"))
    }

    /// Borrow text directly from the original prepared diagnostic. Failure
    /// leaves that original value available for immediate ordinary fallback;
    /// there is no second bulk-string copy before the paired spool write.
    pub(super) fn capture<'a>(
        &mut self,
        original: &'a PreparedLocatedDiagnostic,
    ) -> io::Result<IndexedDiagnosticRef<'a>> {
        self.capture_diagnostic_parts(original.span, &original.diagnostic)
    }

    /// The live full-failure wrapper keeps its private original cause through
    /// paired sealing. Capture borrows ONLY its already-prepared diagnostic;
    /// no cause, validator result or proof capability is serialized.
    pub(super) fn capture_diagnostic_parts<'a>(
        &mut self,
        span: rustc_span::Span,
        original: &'a PreparedDiagnostic,
    ) -> io::Result<IndexedDiagnosticRef<'a>> {
        let span = self.intern(span)?;
        let mut children = Vec::new();
        children.try_reserve(original.children.len()).map_err(io::Error::other)?;
        for child in &original.children {
            children.push(match child {
                PreparedDiagnosticChild::Note(note) => DiagnosticChildRef::Note(note),
                PreparedDiagnosticChild::Help(help) => DiagnosticChildRef::Help(help),
                PreparedDiagnosticChild::SpanNote(actual, note) => {
                    DiagnosticChildRef::SpanNote(self.intern(*actual)?, note)
                }
            });
        }
        Ok(IndexedDiagnosticRef {
            table: self.id,
            span,
            diagnostic: DiagnosticRef {
                aborting: original.aborting,
                header: &original.header,
                children,
            },
        })
    }

    pub(super) fn capture_note<'a>(
        &mut self,
        original: &'a PreparedLocatedNote,
    ) -> io::Result<IndexedNoteRef<'a>> {
        Ok(IndexedNoteRef {
            table: self.id,
            span: self.intern(original.span)?,
            report: &original.report,
        })
    }
}

/// Primary NOTE severity is distinct from Warning/Error. The same borrowed
/// report shape also carries an already-prepared ordinary human summary.
#[derive(serde::Serialize)]
pub(super) struct IndexedNoteRef<'a> {
    table: u64,
    span: usize,
    report: &'a PreparedHumanReport,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct IndexedNote {
    table: u64,
    span: usize,
    report: PreparedHumanReport,
}

impl IndexedNote {
    pub(super) fn restore(self, actual: &LiveSpans) -> io::Result<PreparedLocatedNote> {
        if self.table != actual.id {
            return Err(invalid("note belongs to another live span table"));
        }
        let span = *actual.values.get(self.span)
            .ok_or_else(|| invalid("note primary span is outside its live table"))?;
        Ok(PreparedLocatedNote { span, report: self.report })
    }
}

#[derive(serde::Serialize)]
pub(super) struct IndexedDiagnosticRef<'a> {
    table: u64,
    span: usize,
    diagnostic: DiagnosticRef<'a>,
}

#[derive(serde::Serialize)]
struct DiagnosticRef<'a> {
    aborting: bool,
    header: &'a str,
    children: Vec<DiagnosticChildRef<'a>>,
}

// Serde shape is exactly the owned PreparedDiagnosticChild<usize>, preserving
// arbitrary original Note/Help/SpanNote order without serializing a Span.
#[derive(serde::Serialize)]
enum DiagnosticChildRef<'a> {
    Note(&'a str),
    Help(&'a str),
    SpanNote(usize, &'a str),
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct IndexedDiagnostic {
    table: u64,
    span: usize,
    diagnostic: PreparedDiagnostic<usize>,
}

impl IndexedDiagnostic {
    /// Validate every slot before returning any emit-capable diagnostic.
    /// These are presentation spans from the same live original table, never
    /// private proof/grade restoration. No diagnostic is emitted on refusal.
    pub(super) fn restore(self, actual: &LiveSpans) -> io::Result<PreparedLocatedDiagnostic> {
        if self.table != actual.id {
            return Err(invalid("diagnostic belongs to another live span table"));
        }
        let span = *actual.values.get(self.span)
            .ok_or_else(|| invalid("diagnostic primary span is outside its live table"))?;
        let mut children = Vec::new();
        children.try_reserve(self.diagnostic.children.len()).map_err(io::Error::other)?;
        for child in self.diagnostic.children {
            children.push(match child {
                PreparedDiagnosticChild::Note(note) => PreparedDiagnosticChild::Note(note),
                PreparedDiagnosticChild::Help(help) => PreparedDiagnosticChild::Help(help),
                PreparedDiagnosticChild::SpanNote(index, note) => {
                    let actual = *actual.values.get(index)
                        .ok_or_else(|| invalid("diagnostic child span is outside its live table"))?;
                    PreparedDiagnosticChild::SpanNote(actual, note)
                }
            });
        }
        Ok(PreparedLocatedDiagnostic {
            span,
            diagnostic: PreparedDiagnostic {
                aborting: self.diagnostic.aborting,
                header: self.diagnostic.header,
                children,
            },
        })
    }
}

#[cfg(test)]
mod tests;
