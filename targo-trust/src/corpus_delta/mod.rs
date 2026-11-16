//! `targo trust gate corpus-delta`: what a new compiler won and lost on the
//! daily-driver corpora (docs/PLAN.md PKG-S1 SE16).
//!
//! A cut compares proof rows (PKG-V4) and consumer checks (`gate compare-seal`).
//! This compares ordinary programs, file by file: the 2026-10-28 seal (pack
//! 16387) shipped refusing two programs the 2026-10-19 seal verified, and
//! nothing compared the two before it went out.
//!
//! The corpora are rows of `tests/corpora.toml` ([`table`]). The verb compiles
//! every case once with each of two compilers ([`run`]) and ranks each verdict
//! against the case's pin ([`rank`]):
//!
//! * `2`: the verdict the case is pinned to, or `verifies` where nothing is
//!   pinned;
//! * `1`: a clean miss;
//! * `0`: a crash, below a clean miss;
//! * `-1`: `verifies` where the pin says `refuses`, a possible false proof and
//!   worse than a crash.
//!
//! A case whose rank fell is a LOSS, and so is one the old compiler had as
//! pinned and the new compiler did not record. A rank that rose is a GAIN. A
//! case with no verdict inside its bound is not judged: it has no rank, and a
//! run that holds one compares nothing.
//!
//! A verdict here is a compiler's exit status. It is a release-gate input,
//! never a proof, and it grants nothing by itself.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Serialize};

mod cli;
mod gate_args;
mod identity;
mod run;
mod table;

#[cfg(test)]
mod tests;

pub(crate) use cli::run_subcommand;

/// `--fail-on-loss` with a LOSS.
pub(crate) const EXIT_LOSS: u8 = 1;
/// A usage error, or a table that does not load.
pub(crate) const EXIT_USAGE: u8 = 2;
/// COULD NOT RUN: nothing was compared.
pub(crate) const EXIT_COULD_NOT_RUN: u8 = 3;

/// The rank of a verdict that is the one its case is pinned to.
const AS_PINNED: i8 = 2;
/// The rank of `verifies` where the pin says `refuses`.
const FALSE_PROOF: i8 = -1;

/// What a corpus requires of one compile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Pin {
    Verifies,
    Refuses,
}

impl Pin {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Verifies => "verifies",
            Self::Refuses => "refuses",
        }
    }
}

/// What one compiler did with one case: its own exit status.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "String", into = "String")]
pub(crate) enum Verdict {
    /// Exit 0.
    Verifies,
    /// Exit 1: rustc's status for an error, a verification refusal included.
    Refuses,
    /// Any other exit status (an ICE's 101, a program that could not load), or
    /// 128 plus the signal that ended the compiler.
    Crash(i32),
    /// No verdict inside the case's bound. Never ranked.
    NotJudged,
}

impl Verdict {
    pub(crate) fn of_exit(code: i32) -> Self {
        match code {
            0 => Self::Verifies,
            1 => Self::Refuses,
            other => Self::Crash(other),
        }
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Verifies => formatter.write_str("verifies"),
            Self::Refuses => formatter.write_str("refuses"),
            Self::Crash(status) => write!(formatter, "crash:{status}"),
            Self::NotJudged => formatter.write_str("not-judged"),
        }
    }
}

impl From<Verdict> for String {
    fn from(verdict: Verdict) -> Self {
        verdict.to_string()
    }
}

impl TryFrom<String> for Verdict {
    type Error = String;

    fn try_from(text: String) -> Result<Self, Self::Error> {
        match text.as_str() {
            "verifies" => Ok(Self::Verifies),
            "refuses" => Ok(Self::Refuses),
            "not-judged" => Ok(Self::NotJudged),
            other => other
                .strip_prefix("crash:")
                .and_then(|status| status.parse::<i32>().ok())
                .filter(|status| !matches!(status, 0 | 1))
                .map(Self::Crash)
                .ok_or_else(|| format!("{other:?} is not a verdict")),
        }
    }
}

/// One line of a side's `record.ndjson` (schema `trust.corpus-record.v1`):
/// exactly these five fields.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CaseRecord {
    pub(crate) corpus: String,
    pub(crate) case: String,
    pub(crate) verdict: Verdict,
    /// The first `error` line of the compiler's output, where it did not
    /// verify; why there is no verdict, where it was not judged.
    pub(crate) cause: String,
    pub(crate) pin: Option<Pin>,
}

/// A rank for a verdict against a pin; `None` for a verdict that has none.
pub(crate) type RankFn = fn(Verdict, Option<Pin>) -> Option<i8>;

/// The rank of `verdict` against `pin` (the module comment has the scale).
pub(crate) fn rank(verdict: Verdict, pin: Option<Pin>) -> Option<i8> {
    Some(match (verdict, pin) {
        (Verdict::NotJudged, _) => return None,
        (Verdict::Crash(_), _) => 0,
        (Verdict::Verifies, None | Some(Pin::Verifies)) => AS_PINNED,
        (Verdict::Refuses, Some(Pin::Refuses)) => AS_PINNED,
        (Verdict::Verifies, Some(Pin::Refuses)) => FALSE_PROOF,
        (Verdict::Refuses, None | Some(Pin::Verifies)) => 1,
    })
}

/// A verdict as a flip line shows it, with the pin it was ranked against.
fn shown(verdict: Verdict, pin: Option<Pin>) -> String {
    match pin {
        Some(pin) => format!("{verdict} (pinned {})", pin.label()),
        None => verdict.to_string(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FlipKind {
    Loss,
    Gain,
    /// Only the old side recorded the case, and not as pinned. Not counted.
    Gone,
    /// Only the new side recorded the case. Not counted.
    New,
}

impl FlipKind {
    fn label(self) -> &'static str {
        match self {
            Self::Loss => "LOSS",
            Self::Gain => "GAIN",
            Self::Gone => "GONE",
            Self::New => "NEW",
        }
    }
}

/// One case that did not come out the same on both sides.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Flip {
    pub(crate) kind: FlipKind,
    pub(crate) corpus: String,
    pub(crate) case: String,
    /// What moved, and why.
    pub(crate) what: String,
}

impl Flip {
    pub(crate) fn line(&self) -> String {
        format!("{:<5} {}/{}: {}", self.kind.label(), self.corpus, self.case, self.what)
    }
}

/// One corpus's counts: cases recorded, and cases recorded as pinned.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Tally {
    pub(crate) old_as_pinned: usize,
    pub(crate) old_total: usize,
    pub(crate) new_as_pinned: usize,
    pub(crate) new_total: usize,
}

/// Two sides' records, compared case by case.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Comparison {
    pub(crate) flips: Vec<Flip>,
    pub(crate) losses: usize,
    pub(crate) gains: usize,
    /// Cases the new compiler crashed on, whatever the old one did.
    pub(crate) crashes: usize,
    pub(crate) tallies: BTreeMap<String, Tally>,
}

impl Comparison {
    /// The flips as the report prints them: one line each, sorted.
    pub(crate) fn flip_lines(&self) -> Vec<String> {
        let mut lines: Vec<String> = self.flips.iter().map(Flip::line).collect();
        lines.sort();
        lines
    }
}

type Key<'a> = (&'a str, &'a str);

/// A side's records by (corpus, case). A case recorded twice has no one
/// verdict, so the side has none.
fn by_case<'a>(
    side: &str,
    records: &'a [CaseRecord],
) -> Result<BTreeMap<Key<'a>, &'a CaseRecord>, String> {
    let mut cases = BTreeMap::new();
    for record in records {
        if cases.insert((record.corpus.as_str(), record.case.as_str()), record).is_some() {
            return Err(format!(
                "{side}: {}/{} was recorded twice, so its verdict is ambiguous",
                record.corpus, record.case
            ));
        }
    }
    Ok(cases)
}

/// Compare two sides' records under `rank`. For a case both sides recorded,
/// both ranks use the new side's pin: the pin is the corpus's, and the new
/// side is the one a cut is about to ship.
pub(crate) fn compare_with(
    old: &[CaseRecord],
    new: &[CaseRecord],
    rank: RankFn,
) -> Result<Comparison, String> {
    let old = by_case("old", old)?;
    let new = by_case("new", new)?;
    let mut comparison = Comparison::default();
    for (key, was) in &old {
        let own = rank(was.verdict, was.pin);
        let tally = comparison.tallies.entry(was.corpus.clone()).or_default();
        tally.old_total += 1;
        if own == Some(AS_PINNED) {
            tally.old_as_pinned += 1;
        }
        let flip =
            |kind, what| Flip { kind, corpus: was.corpus.clone(), case: was.case.clone(), what };
        let Some(now) = new.get(key) else {
            let kind = if own == Some(AS_PINNED) { FlipKind::Loss } else { FlipKind::Gone };
            if kind == FlipKind::Loss {
                comparison.losses += 1;
            }
            comparison.flips.push(flip(
                kind,
                format!("{} -> not recorded by the new side", shown(was.verdict, was.pin)),
            ));
            continue;
        };
        let pin = now.pin;
        let (Some(before), Some(after)) = (rank(was.verdict, pin), rank(now.verdict, pin)) else {
            continue;
        };
        if after < before {
            let why = if after == FALSE_PROOF {
                "a case pinned refuses now verifies"
            } else if now.cause.is_empty() {
                "no `error` line in its output"
            } else {
                now.cause.as_str()
            };
            comparison.losses += 1;
            comparison.flips.push(flip(
                FlipKind::Loss,
                format!("{} -> {}: {why}", was.verdict, shown(now.verdict, pin)),
            ));
        } else if after > before {
            // What the old compiler said, where it said anything (a case that
            // verified against a `refuses` pin printed no error).
            let was_cause = match was.cause.as_str() {
                "" => String::new(),
                cause => format!(" (was: {cause})"),
            };
            comparison.gains += 1;
            comparison.flips.push(flip(
                FlipKind::Gain,
                format!("{} -> {}{was_cause}", was.verdict, shown(now.verdict, pin)),
            ));
        }
    }
    for (key, now) in &new {
        let tally = comparison.tallies.entry(now.corpus.clone()).or_default();
        tally.new_total += 1;
        if rank(now.verdict, now.pin) == Some(AS_PINNED) {
            tally.new_as_pinned += 1;
        }
        if matches!(now.verdict, Verdict::Crash(_)) {
            comparison.crashes += 1;
        }
        if !old.contains_key(key) {
            comparison.flips.push(Flip {
                kind: FlipKind::New,
                corpus: now.corpus.clone(),
                case: now.case.clone(),
                what: format!("{} (not recorded by the old side)", shown(now.verdict, now.pin)),
            });
        }
    }
    Ok(comparison)
}
