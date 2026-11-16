//! Private saved publication roles. Stored values are committed presentation
//! DATA only; no private proof, original failure cause or live Span is decoded.
//! Role/body/complete owed-row checks precede all restoration and emission.

use super::*;
use std::io;

use diagnostic_data::{IndexedSpan, LiveSpans};
use prepared::{PreparedCollection, PreparedTransport};
use publication_identity::OwedInventory;
use publication_output::{PreparedEmission, PreparedEmissionRef};
use super::super::publication_transport::PreparedTransportData;
use super::super::publication_human::HumanFacts;
use proposal::{PreparedProposal, RowOverlay, SourceApproval};

#[derive(serde::Serialize, serde::Deserialize)]
enum OriginalRole {
    #[serde(rename = "original-publication-v1")]
    Original,
}

#[derive(serde::Serialize, serde::Deserialize)]
enum ProposedRole {
    #[serde(rename = "proposed-publication-delta-v1")]
    Proposed,
}

#[derive(serde::Serialize)]
struct ProposedRef<'a> {
    role: ProposedRole,
    owed: &'a OwedInventory,
    overlays: &'a [RowOverlay],
    drop_actions: &'a [usize],
    action_count: usize,
    human: Option<HumanRef<'a>>,
}

#[derive(serde::Serialize)]
struct HumanRef<'a> {
    action: usize,
    span: IndexedSpan,
    facts: &'a HumanFacts,
    tally: PublishedRowTally,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ProposedRecord {
    role: ProposedRole,
    owed: OwedInventory,
    pub(super) overlays: Vec<RowOverlay>,
    pub(super) drop_actions: Vec<usize>,
    action_count: usize,
    human: Option<HumanRecord>,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct HumanRecord {
    action: usize,
    span: IndexedSpan,
    facts: HumanFacts,
    tally: PublishedRowTally,
}

#[derive(serde::Serialize)]
struct OriginalRef<'a> {
    role: OriginalRole,
    owed: &'a OwedInventory,
    actions: PreparedEmissionRef<'a>,
    transport: Option<TransportRef<'a>>,
}

#[derive(serde::Serialize)]
struct TransportRef<'a> {
    action: usize,
    span: IndexedSpan,
    data: &'a PreparedTransportData,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct OriginalRecord {
    role: OriginalRole,
    owed: OwedInventory,
    actions: PreparedEmission,
    transport: Option<TransportRecord>,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TransportRecord {
    action: usize,
    span: IndexedSpan,
    data: PreparedTransportData,
}

/// Only the owned writer can construct this handle. The live complete original
/// inventory and span table are distinct from the saved DATA. A successful
/// decode cannot construct a new native/proof/debt eligibility marker.
pub(super) struct StoredOriginal {
    saved: spool::Saved<OriginalRecord>,
    spans: LiveSpans,
    owed: OwedInventory,
}

/// The two roles are separate DATA types and separate live handles. A delta
/// cannot stand in for the complete Original record or render on its own.
pub(super) struct StoredPair {
    original: StoredOriginal,
    proposed: spool::Saved<ProposedRecord>,
    approval: SourceApproval,
}

pub(super) enum StoredPublication {
    Original(StoredOriginal),
    Pair(StoredPair),
}

pub(super) struct RestoredHuman {
    pub(super) action: usize,
    pub(super) span: rustc_span::Span,
    pub(super) facts: HumanFacts,
    pub(super) tally: PublishedRowTally,
}

/// Constructed only after both stored roles and their live source approval
/// validated. This still grants NO proof/selected outcome by itself.
pub(super) struct RestoredDelta {
    pub(super) overlays: Vec<RowOverlay>,
    pub(super) drop_actions: Vec<usize>,
    pub(super) human: Option<RestoredHuman>,
    _approval: SourceApproval,
}

pub(super) struct RestoredPublication {
    pub(super) original: PreparedCollection,
    pub(super) proposed: Option<RestoredDelta>,
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

pub(super) fn save_original(
    storage: &Arc<spool::PublicationSpool>,
    body: &str,
    mut original: PreparedCollection,
) -> Result<StoredOriginal, (io::Error, PreparedCollection)> {
    let captured = (|| {
        let owed = original.owed.as_ref()
            .ok_or_else(|| invalid("original publication has no complete owed-row inventory"))?;
        let mut spans = LiveSpans::new()?;
        let actions = publication_output::capture(&mut spans, &original.actions)?;
        let transport = original.transport.as_ref().map(|transport| {
            if transport.action > original.actions.len() {
                return Err(invalid("original transport position is outside its action stream"));
            }
            Ok(TransportRef {
                action: transport.action,
                span: spans.capture_span(transport.span)?,
                data: &transport.data,
            })
        }).transpose()?;
        let saved = storage.save_as::<_, OriginalRecord>(body, owed.total(), &OriginalRef {
            role: OriginalRole::Original, owed, actions, transport,
        })?;
        Ok::<_, io::Error>((saved, spans))
    })();
    match captured {
        Ok((saved, spans)) => Ok(StoredOriginal {
            saved, spans,
            owed: original.owed.take().expect("successful original capture retained its inventory"),
        }),
        Err(error) => Err((error, original)),
    }
}

/// The caller retains the actual original artifacts/rows/clock and this
/// collection in the SAME original stop scope throughout both accepted-write
/// seals. No handle/approval escapes a refused second write or expired check.
pub(super) fn save_pair<'native, 'prepared>(
    storage: &Arc<spool::PublicationSpool>,
    body: &str,
    original: &'prepared PreparedCollection,
    proposal: PreparedProposal<'native, 'prepared>,
) -> io::Result<(spool::Saved<OriginalRecord>, Option<(spool::Saved<ProposedRecord>, SourceApproval)>, LiveSpans)> {
    if !proposal.still_current() {
        return Err(invalid("original proposed-delta preparation already stopped"));
    }
    let owed = original.owed.as_ref()
        .ok_or_else(|| invalid("paired publication has no complete original inventory"))?;
    let mut spans = LiveSpans::new()?;
    let actions = publication_output::capture(&mut spans, &original.actions)?;
    let transport = original.transport.as_ref().map(|transport| {
        if transport.action > original.actions.len() {
            return Err(invalid("paired transport position is outside its original stream"));
        }
        Ok(TransportRef {
            action: transport.action, span: spans.capture_span(transport.span)?, data: &transport.data,
        })
    }).transpose()?;
    let human = match (&original.human, proposal.human_tally) {
        (Some(human), Some(tally)) => Some(HumanRef {
            action: human.action, span: spans.capture_span(human.span)?, facts: &human.facts, tally,
        }),
        (None, None) => None,
        _ => return Err(invalid("proposed human record does not match original preparation")),
    };
    let (original, proposed) = storage.save_pair_as::<_, OriginalRecord, _, ProposedRecord>(
        body, owed.total(),
        &OriginalRef { role: OriginalRole::Original, owed, actions, transport },
        &ProposedRef {
            role: ProposedRole::Proposed, owed, overlays: &proposal.overlays,
            drop_actions: &proposal.drop_actions, action_count: original.actions.len(), human,
        },
    )?;
    // Formatting/storage time earns no function credit. Expiration may keep
    // the already committed ORIGINAL output, never a proposed approval.
    let proposed = if proposal.still_current() {
        Some((proposed, proposal.into_source_approval()))
    } else {
        None
    };
    Ok((original, proposed, spans))
}

pub(super) fn finish_saved_pair(
    saved: spool::Saved<OriginalRecord>,
    proposed: Option<(spool::Saved<ProposedRecord>, SourceApproval)>,
    spans: LiveSpans,
    owed: OwedInventory,
) -> StoredPublication {
    let original = StoredOriginal { saved, spans, owed };
    match proposed {
        Some((proposed, approval)) => StoredPublication::Pair(StoredPair { original, proposed, approval }),
        None => StoredPublication::Original(original),
    }
}

impl StoredOriginal {
    fn restore_data(&mut self, body: &str) -> io::Result<PreparedCollection> {
        let record = self.saved.consume(body, self.owed.total())?;
        if record.owed != self.owed {
            return Err(invalid("saved publication differs from its live complete original inventory"));
        }
        let OriginalRole::Original = record.role;
        let actions = record.actions.restore(&self.spans)?;
        let transport = record.transport.map(|transport| {
            if transport.action > actions.len() {
                return Err(invalid("saved transport position is outside its action stream"));
            }
            Ok(PreparedTransport {
                action: transport.action,
                span: self.spans.restore_span(&transport.span)?,
                data: transport.data,
            })
        }).transpose()?;
        Ok(PreparedCollection { actions, transport, human: None, owed: Some(record.owed) })
    }

    /// The spool verifies original emitted bytes/body/count/extent BEFORE
    /// deserializing. Typed role and exact live inventory then refuse any
    /// mismatched record, and every action/span validates before any output.
    /// No read refusal is retried or presented as a successful empty report.
    pub(super) fn restore(
        mut self,
        body: &str,
    ) -> Result<PreparedCollection, (io::Error, OwedInventory)> {
        let restored = self.restore_data(body);
        restored.map_err(|error| (error, self.owed))
    }
}

impl StoredPublication {
    pub(super) fn has_proposal(&self) -> bool { matches!(self, Self::Pair(_)) }

    pub(super) fn restore(
        self,
        body: &str,
        mut may_propose: impl FnMut() -> bool,
    ) -> Result<RestoredPublication, (io::Error, OwedInventory)> {
        match self {
            Self::Original(original) => original.restore(body).map(|original| {
                RestoredPublication { original, proposed: None }
            }),
            Self::Pair(mut pair) => {
                let original = match pair.original.restore_data(body) {
                    Ok(original) => original,
                    Err(error) => return Err((error, pair.original.owed)),
                };
                let proposed = (|| {
                    if !may_propose() {
                        return Err(io::Error::new(io::ErrorKind::Interrupted, "proposed publication stopped before decode"));
                    }
                    let record = pair.proposed.consume(body, pair.original.owed.total())?;
                    if !may_propose() {
                        return Err(io::Error::new(io::ErrorKind::Interrupted, "proposed publication stopped after decode"));
                    }
                    let ProposedRole::Proposed = record.role;
                    if record.owed != pair.original.owed || record.action_count != original.actions.len() {
                        return Err(invalid("proposed delta does not match its complete original record"));
                    }
                    if !pair.approval.matches(
                        &record.overlays, &record.drop_actions,
                        record.human.as_ref().map(|human| human.tally), &record.owed,
                    ) {
                        return Err(invalid("proposed delta differs from its live original source approval"));
                    }
                    let mut seen_rows = FxHashSet::default();
                    seen_rows.try_reserve(record.overlays.len()).map_err(io::Error::other)?;
                    let row_index = record.owed.row_index(&mut may_propose)?;
                    for overlay in &record.overlays {
                        if !may_propose() || !seen_rows.insert(overlay.published)
                            || row_index.unique_row(&overlay.identity) != Some(overlay.published)
                        {
                            return Err(invalid("proposed row correspondence is not exact and unique"));
                        }
                    }
                    let mut seen_actions = FxHashSet::default();
                    seen_actions.try_reserve(record.drop_actions.len()).map_err(io::Error::other)?;
                    for &index in &record.drop_actions {
                        if !may_propose() || index >= original.actions.len() || !seen_actions.insert(index)
                            || original.transport.as_ref().is_some_and(|transport| index < transport.action)
                            || !matches!(&original.actions[index], PreparedAction::Diagnostic(_))
                        {
                            return Err(invalid("proposed diagnostic patch is outside its exact original floor"));
                        }
                    }
                    let human = record.human.map(|human| {
                        let span = pair.original.spans.restore_span(&human.span)?;
                        if human.action >= original.actions.len()
                            || !matches!(&original.actions[human.action], PreparedAction::Note(note) if note.span == span)
                            || seen_actions.contains(&human.action)
                            || human.tally.total() != record.owed.total()
                        {
                            return Err(invalid("proposed human patch does not match its original NOTE/denominator"));
                        }
                        Ok(RestoredHuman {
                            action: human.action, span, facts: human.facts, tally: human.tally,
                        })
                    }).transpose()?;
                    if !may_propose() {
                        return Err(io::Error::new(io::ErrorKind::Interrupted, "proposed publication stopped during preflight"));
                    }
                    Ok::<_, io::Error>(RestoredDelta {
                        overlays: record.overlays, drop_actions: record.drop_actions,
                        human, _approval: pair.approval,
                    })
                })();
                let proposed = proposed.map_err(|error| {
                    debug!("VF5 proposed DATA refused: {error}; complete original output remains");
                    error
                }).ok();
                Ok(RestoredPublication { original, proposed })
            }
        }
    }
}

#[cfg(test)]
#[path = "stored/tests.rs"]
mod tests;
