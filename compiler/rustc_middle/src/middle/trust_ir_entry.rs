// Trust: step 2 increment 6, step 6.2 — trust-ir in metadata, the CARRIER.
//
//! What rmeta carries of a crate's trust-ir (design
//! `docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md` §2.6).
//!
//! # Opaque on purpose
//!
//! An entry is the producer's bytes (`trust_thir_lower::rmeta_entry`): a self-contained
//! trust-ir module in trust-ir's own binary format plus the evidence a consumer needs to
//! re-derive effect conservation. rustc_metadata never names a trust-ir type and never reads
//! inside an entry, exactly as it treats `trust_clean_verdict_digest`: versioning lives in ONE
//! place (the entry's own magic and schema, and trust-ir's wire version inside it), so a format
//! skew is the entry decoder's named refusal, never an rmeta shape error.
//!
//! # What the header is for
//!
//! An ABSENT entry must say why. The header records the producing compiler's trust-ir wire
//! version, the entry schema, how many entries were written, and one row per definition the
//! encoder refused (`DefIndex`, reason). It is `None` for a crate compiled without the producer,
//! which is itself the reason a consumer reports. Nothing here is authority: a consumer
//! re-derives every verdict over the decoded bytes (D4, D39 (ii)).

use rustc_macros::{Decodable, Encodable, StableHash};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};

/// Trust: one definition's encoded trust-ir entry, as opaque bytes.
///
/// Encoded as its length plus the raw bytes (`emit_raw_bytes`), and decoded with one
/// `read_raw_bytes` copy, rather than through the element-by-element `Vec<u8>` path the generic
/// `[T]` impl takes: an entry is kilobytes, not a handful of digest bytes.
#[derive(StableHash)]
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct TrustIrEntryBlob(pub Vec<u8>);

impl<E: Encoder> Encodable<E> for TrustIrEntryBlob {
    fn encode(&self, e: &mut E) {
        e.emit_usize(self.0.len());
        e.emit_raw_bytes(&self.0);
    }
}

impl<D: Decoder> Decodable<D> for TrustIrEntryBlob {
    fn decode(d: &mut D) -> Self {
        let len = d.read_usize();
        TrustIrEntryBlob(d.read_raw_bytes(len).to_vec())
    }
}

/// Trust: one definition rustc encodes `optimized_mir` for that carries NO trust-ir entry, and
/// why (the encoder's refusal, verbatim).
#[derive(StableHash)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Encodable, Decodable)]
pub struct TrustIrUnencoded {
    /// The definition's `DefIndex` in the producing crate.
    pub def_index: u32,
    pub reason: String,
}

/// Trust: the crate-level header of a crate's trust-ir entries. `None` in rmeta when the
/// producer did not run in the compilation that wrote it.
#[derive(StableHash)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, Encodable, Decodable)]
pub struct TrustIrCrateHeader {
    /// `trust_ir::binary::VERSION` of the PRODUCING compiler. A consumer requires its own to be
    /// equal: a blob's own header may carry a lower, minimum-lossless version, so the blob's
    /// header alone cannot say which reader wrote it.
    pub trust_ir_version: u32,
    /// The entry schema (`trust_thir_lower::rmeta_entry::ENTRY_SCHEMA`).
    pub entry_schema: u32,
    /// Definitions that carry an entry.
    pub encoded: u32,
    /// Retained producer definitions and the legacy optimized-MIR inventory
    /// that carry no entry, sorted by `def_index`.
    pub unencoded: Vec<TrustIrUnencoded>,
    /// A reason that applies to the WHOLE crate (no entry was attempted although the producer
    /// ran), as `<class>(<why>)`: `incremental(..)` (the producer's per-body records do not
    /// survive a cache replay), `metadata-only(..)` (the session encodes no MIR) or
    /// `proc-macro(..)` (a proc-macro crate's metadata carries no bodies). `None` when entries
    /// were attempted definition by definition.
    pub crate_refusal: Option<String>,
}

impl TrustIrCrateHeader {
    /// The recorded reason `def_index` carries no entry, if the encoder recorded one.
    pub fn unencoded_reason(&self, def_index: u32) -> Option<&str> {
        if let Some(reason) = &self.crate_refusal {
            return Some(reason);
        }
        self.unencoded
            .binary_search_by_key(&def_index, |row| row.def_index)
            .ok()
            .map(|i| self.unencoded[i].reason.as_str())
    }
}

/// Trust: the LOCAL crate's entries, built once after analysis by the producer
/// (`trust_thir_lower::rmeta_entry::local_entries`) for every body it recorded.
///
/// `producer_ran` is false when the producer did not run in this session (then `entries` is
/// empty and rmeta carries no header). Otherwise each recorded definition maps to its encoded
/// bytes or to the encoder's refusal. A definition with no row was never recorded by the
/// producer; the metadata encoder reports that as its own reason.
///
/// `StableHash`, because the metadata dep-node task reads the query that returns this: a result
/// with no fingerprint is red on every re-execution, and an `eval_always` query is re-executed
/// in every incremental session, so an unhashed result would keep metadata from ever being
/// reused (measured: every session re-encoded rmeta). Under incremental compilation the value is
/// the crate-wide refusal and no entries, the same in every session, so it hashes green.
#[derive(StableHash)]
#[derive(Debug, Default)]
pub struct TrustIrLocalEntries {
    pub producer_ran: bool,
    pub trust_ir_version: u32,
    pub entry_schema: u32,
    pub crate_refusal: Option<String>,
    pub entries: std::collections::BTreeMap<u32, Result<TrustIrEntryBlob, String>>,
    /// Trust (step 2 increment 6, step 6.5.1): the definitions whose row the producer routed to
    /// its level-S template builder (a generic definition: `requires_monomorphization`). Their
    /// `entries` row is that builder's outcome. The metadata encoder reads this set, never a
    /// blob, to keep its two level-R `-Zmeta-stats` lines counting what they counted before
    /// (every routed row as `template-pending`) and to print the routed rows on a line of their
    /// own (`trust-ir templates:`).
    pub templates: std::collections::BTreeSet<u32>,
}

/// Trust: the reason recorded for a definition rustc encodes `optimized_mir` for that the
/// producer never recorded a body for (a body it did not lower in this session).
pub const UNRECORDED_REASON: &str =
    "not-lowered(the producer recorded no body for this definition)";
