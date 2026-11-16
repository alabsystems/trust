//! The per-declaration rows of a crate's `clean { … }` islands, as the
//! compiler publishes them to the frontend
//! ([`crate::TransportMessage::CleanIslandRows`], `"type":"clean_island_rows"`).
//!
//! One message per compilation unit the compiler reaches its islands in,
//! `islands: 0` when it has none: absence is never "no island". A unit that
//! publishes no message stopped before its islands were read (a Rust parse or
//! macro error, an abnormal end) or was compiled by something that does not
//! publish them, so a consumer reads its islands as NOT MEASURED, never as
//! deleted (`targo-trust`'s `crate::obligations`, CLEAN ISLANDS). Each row is
//! one declaration Clean parsed from an island, keyed exactly as a standalone
//! `.lean` file's declaration is ([`crate::lean_declaration_identity`]), with
//! the crate name in front of Clean's canonical name: `<crate>::<name>#<16 hex>`.
//!
//! A row is DISCLOSURE. It is the island analogue of a `.lean` record row, and
//! it never claims more than that lane does:
//!
//! * `proved`, stopped `solved`, only in a payload whose `phase` is `verified`
//!   and which is `complete` — the producer
//!   (`trust_certify::clean_island_rows`) states the remaining conditions:
//!   the declaration's batch committed under the reference recheck, the
//!   session was not tainted, nothing refused it, no import was served by a
//!   stand-in, and its own model, binding and seal checks passed;
//! * `failed`, stopped `solver-incomplete`, basis `unproved_fail_closed`: its
//!   proof was refused, and nothing refuted its statement;
//! * `unknown`, stopped `unsupported`: checked only relative to a stand-in, or
//!   its model check decided nothing;
//! * `unknown`, stopped `not-dispatched`: every other case.
//!
//! [`CleanIslandRowsTransport::validate`] refuses any other combination, so a
//! consumer that admits a message after validating it can never read a row as
//! more than its producer could state. No consumer counts a row in a verdict,
//! a proof total, a baseline or a coverage denominator.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::obligation_identity::split_obligation_key;

/// The schema every [`CleanIslandRowsTransport`] names.
pub const CLEAN_ISLAND_ROWS_SCHEMA_V1: &str = "trust.clean-island-rows.v1";

/// Which compiler path published the rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum CleanIslandPhase {
    /// The verification pass ran over the front-end-clean crate.
    Verified,
    /// A Rust front-end error stopped the crate before the verification pass:
    /// the rows are the resolver's batch, and no model, binding or seal check
    /// ran. Nothing in such a payload is `proved`.
    FrontEndError,
}

impl CleanIslandPhase {
    /// The wire spelling.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::FrontEndError => "front-end-error",
        }
    }

    /// The phase a wire spelling names.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        [Self::Verified, Self::FrontEndError].into_iter().find(|phase| phase.as_str() == text)
    }
}

/// What a row states: the only four status/stop/basis combinations an island
/// row may carry (module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CleanIslandRowVerdict {
    /// `proved`, stopped `solved`.
    Proved,
    /// `failed`, stopped `solver-incomplete`, basis `unproved_fail_closed`.
    ProofRefused,
    /// `unknown`, stopped `unsupported`.
    Unsupported,
    /// `unknown`, stopped `not-dispatched`.
    NotDispatched,
}

impl CleanIslandRowVerdict {
    const ALL: [Self; 4] =
        [Self::Proved, Self::ProofRefused, Self::Unsupported, Self::NotDispatched];

    /// The published status.
    #[must_use]
    pub fn status(self) -> &'static str {
        match self {
            Self::Proved => crate::Outcome::Proved.as_str(),
            Self::ProofRefused => crate::Outcome::Failed.as_str(),
            Self::Unsupported | Self::NotDispatched => crate::Outcome::Unknown.as_str(),
        }
    }

    /// What ended the search.
    #[must_use]
    pub fn stop(self) -> &'static str {
        match self {
            Self::Proved => "solved",
            Self::ProofRefused => "solver-incomplete",
            Self::Unsupported => "unsupported",
            Self::NotDispatched => "not-dispatched",
        }
    }

    /// The failure basis a `failed` row states; `None` on every other row.
    #[must_use]
    pub fn basis(self) -> Option<&'static str> {
        (self == Self::ProofRefused).then(|| crate::FailureBasis::UnprovedFailClosed.as_str())
    }

    /// The verdict a row's three fields name, or `None` for any other
    /// combination.
    #[must_use]
    pub fn of_fields(status: &str, stop: &str, basis: Option<&str>) -> Option<Self> {
        Self::ALL.into_iter().find(|verdict| {
            verdict.status() == status && verdict.stop() == stop && verdict.basis() == basis
        })
    }

    /// The worse of two verdicts for one key: `failed` before `unknown`
    /// (`not-dispatched` before `unsupported`) before `proved`. Merging two
    /// units' rows keeps the worse, so a key is proved only where every unit
    /// proved it.
    #[must_use]
    pub fn worse(self, other: Self) -> Self {
        let rank = |verdict: Self| match verdict {
            Self::ProofRefused => 0,
            Self::NotDispatched => 1,
            Self::Unsupported => 2,
            Self::Proved => 3,
        };
        if rank(other) < rank(self) { other } else { self }
    }
}

/// One island declaration's row.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CleanIslandRow {
    /// `<crate>::<Clean canonical name>#<16 hex>`
    /// ([`crate::lean_declaration_identity`]).
    pub key: String,
    /// `lean:<keyword>`, spaces as `-` (`lean:theorem`, `lean:class-inductive`).
    pub kind: String,
    pub status: String,
    pub stop: String,
    /// `unproved_fail_closed` on a `failed` row, absent on every other row.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub basis: Option<String>,
    /// Where the declaration's keyword is: the file as the compiler names it,
    /// one-based line and column.
    pub file: String,
    pub line: u32,
    pub col: u32,
    /// The declaration's source digest (64 hex) when its def path is unique
    /// among the crate's island declarations, otherwise `None` (`example`).
    #[serde(default)]
    pub source: Option<String>,
}

impl CleanIslandRow {
    /// The verdict this row's fields name, if they name one.
    #[must_use]
    pub fn verdict(&self) -> Option<CleanIslandRowVerdict> {
        CleanIslandRowVerdict::of_fields(&self.status, &self.stop, self.basis.as_deref())
    }
}

/// The rows of one compilation unit's islands.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CleanIslandRowsTransport {
    /// [`CLEAN_ISLAND_ROWS_SCHEMA_V1`].
    pub schema: String,
    /// The same scope claims every proof transport message carries.
    pub crate_name: String,
    pub package_name: String,
    pub verification_session: String,
    pub primary_package: bool,
    pub phase: CleanIslandPhase,
    /// How many islands the unit has; 0 states that it has none, and then
    /// there is no row.
    pub islands: u32,
    /// Whether every island's declarations were enumerated and keyed. Exactly
    /// when `problems` is empty.
    pub complete: bool,
    /// Why the rows are not the whole set, one sentence each.
    pub problems: Vec<String>,
    /// One row per declaration, in key order, each key once.
    pub rows: Vec<CleanIslandRow>,
}

fn is_lower_hex(text: &str, len: usize) -> bool {
    text.len() == len && text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

impl CleanIslandRowsTransport {
    /// Refuse a message no honest producer writes (module docs): another
    /// schema, a row of a unit with no island, `complete` that disagrees with
    /// `problems`, a row
    /// whose status, stop and basis are not one of the four island verdicts,
    /// a `proved` row in a payload that is not `verified` and complete, a key
    /// that is not `<crate_name>::<name>#<16 hex>`, keys out of order or
    /// repeated, a kind that is not `lean:<keyword>`, a source that is not 64
    /// hex digits, or a location with no file or a zero line or column.
    pub fn validate(&self) -> Result<(), String> {
        if self.schema != CLEAN_ISLAND_ROWS_SCHEMA_V1 {
            return Err(format!(
                "island rows name schema `{}`, not `{CLEAN_ISLAND_ROWS_SCHEMA_V1}`",
                self.schema
            ));
        }
        if self.crate_name.is_empty() {
            return Err("island rows name no crate".to_string());
        }
        if self.islands == 0 && !self.rows.is_empty() {
            return Err("island rows of a unit with no island".to_string());
        }
        if self.complete != self.problems.is_empty() {
            return Err(format!(
                "island rows say complete={} with {} problem(s)",
                self.complete,
                self.problems.len()
            ));
        }
        let prefix = format!("{}::", self.crate_name);
        let mut previous: Option<&str> = None;
        for row in &self.rows {
            let verdict = row.verdict().ok_or_else(|| {
                format!(
                    "island row `{}` states status `{}`, stop `{}` and basis {:?}, which no \
                     island row can",
                    row.key, row.status, row.stop, row.basis
                )
            })?;
            if verdict == CleanIslandRowVerdict::Proved
                && !(self.phase == CleanIslandPhase::Verified && self.complete)
            {
                return Err(format!(
                    "island row `{}` is proved in a payload that is {} and {}",
                    row.key,
                    self.phase.as_str(),
                    if self.complete { "complete" } else { "incomplete" }
                ));
            }
            let (def_path, _) = split_obligation_key(&row.key)
                .ok_or_else(|| format!("island row key `{}` is not `<name>#<16 hex>`", row.key))?;
            if def_path.len() <= prefix.len() || !def_path.starts_with(&prefix) {
                return Err(format!(
                    "island row key `{}` does not name a declaration of crate `{}`",
                    row.key, self.crate_name
                ));
            }
            if previous.is_some_and(|previous| previous >= row.key.as_str()) {
                return Err(format!("island row `{}` is out of key order or repeated", row.key));
            }
            previous = Some(&row.key);
            let keyword = row.kind.strip_prefix("lean:").unwrap_or_default();
            if keyword.is_empty() || keyword.chars().any(|c| c.is_whitespace()) {
                return Err(format!("island row `{}` has kind `{}`", row.key, row.kind));
            }
            if row.source.as_deref().is_some_and(|source| !is_lower_hex(source, 64)) {
                return Err(format!("island row `{}` has a malformed source digest", row.key));
            }
            if row.file.is_empty() || row.line == 0 || row.col == 0 {
                return Err(format!("island row `{}` has no location", row.key));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "clean_island_rows_tests.rs"]
mod tests;
