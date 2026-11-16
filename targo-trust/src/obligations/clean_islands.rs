// targo-trust/obligations/clean_islands.rs: the CLEAN ISLANDS section of a
// `trust.obligations.v1` record (module docs of `crate::obligations`): one
// line counting the package's compilation units that published island rows,
// one line per crate that published island rows, then one line per island
// declaration, keyed as a `.lean` declaration is.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::Deserialize;
use trust_types::clean_island_rows::{
    CleanIslandPhase, CleanIslandRowVerdict, CleanIslandRowsTransport,
};

use super::{ObligationRecord, UNGRADED, push_json_line};

/// One island declaration's row: an ungraded [`ObligationRecord`], so the
/// listing's label (`PROVED`, `FAILED: unproved, no counterexample; failed
/// closed`, `UNKNOWN`) and the changed-only view's comparison are the ones
/// every other row gets, and its source digest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CleanDeclRecord {
    pub(crate) record: ObligationRecord,
    /// The declaration's source digest, when its def path is unique.
    pub(crate) source: Option<String>,
}

/// One crate's island rows, merged over the package's units.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CleanIslandSection {
    /// `front-end-error` when any unit's was.
    pub(crate) phase: CleanIslandPhase,
    /// The most islands any unit had.
    pub(crate) islands: u32,
    /// Whether every unit's rows were complete.
    pub(crate) complete: bool,
    /// Every unit's problems, sorted, each once.
    pub(crate) problems: Vec<String>,
    /// Rows by key; a key two units published keeps its worse row.
    pub(crate) rows: BTreeMap<String, CleanDeclRecord>,
}

impl CleanIslandSection {
    /// Whether this section is a measurement of every island declaration: the
    /// verification pass ran and every declaration was enumerated.
    pub(crate) fn measured(&self) -> bool {
        self.phase == CleanIslandPhase::Verified && self.complete
    }

    fn of_unit(rows: &CleanIslandRowsTransport) -> Self {
        Self {
            phase: rows.phase,
            islands: rows.islands,
            complete: rows.complete,
            problems: rows.problems.iter().cloned().collect::<BTreeSet<_>>().into_iter().collect(),
            rows: rows
                .rows
                .iter()
                .map(|row| {
                    let record = ObligationRecord {
                        key: row.key.clone(),
                        kind: row.kind.clone(),
                        status: row.status.clone(),
                        stop: row.stop.clone(),
                        file: Some(row.file.clone()),
                        line: Some(row.line),
                        col: Some(row.col),
                        encoding: UNGRADED.to_string(),
                        discharge: UNGRADED.to_string(),
                        premises: Vec::new(),
                        basis: row.basis.clone(),
                    };
                    (row.key.clone(), CleanDeclRecord { record, source: row.source.clone() })
                })
                .collect(),
        }
    }

    /// Fold another unit's section of the same crate into this one.
    fn merge(&mut self, other: Self) {
        if other.phase == CleanIslandPhase::FrontEndError {
            self.phase = CleanIslandPhase::FrontEndError;
        }
        self.islands = self.islands.max(other.islands);
        self.complete &= other.complete;
        let problems: BTreeSet<String> = self.problems.drain(..).chain(other.problems).collect();
        self.problems = problems.into_iter().collect();
        for (key, row) in other.rows {
            match self.rows.get_mut(&key) {
                Some(held) => {
                    if held.source != row.source {
                        held.source = None;
                    }
                    if row.record.worst_first() < held.record.worst_first() {
                        held.record = row.record;
                    }
                }
                None => {
                    self.rows.insert(key, row);
                }
            }
        }
        // Merging never makes a proved row out of an incomplete or
        // front-end-error unit: a unit that could not prove a key states it
        // unproved, and the worse row is kept. A key only one unit published
        // in a section that is no longer a measurement is demoted here.
        if !self.measured() {
            self.demote();
        }
    }

    /// State every proved row `not-dispatched`: the section is not a
    /// measurement of every unit that could carry its keys.
    fn demote(&mut self) {
        for row in self.rows.values_mut() {
            if row.record.is_proved() {
                let demoted = CleanIslandRowVerdict::NotDispatched;
                row.record.status = demoted.status().to_string();
                row.record.stop = demoted.stop().to_string();
                row.record.basis = None;
            }
        }
    }
}

/// How many of a package's compilation units published island rows, of how
/// many it has.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CleanIslandUnits {
    /// The units that published a message (`islands: 0` included).
    pub(crate) published: u32,
    /// The package's proof units in the run's declared proof inventory;
    /// `None` when the run declared none.
    pub(crate) proof_units: Option<u32>,
}

/// A package's island rows: how many of its units published them, and its
/// sections by crate.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PackageCleanIslands {
    /// `None` when no unit of the package published island rows.
    pub(crate) units: Option<CleanIslandUnits>,
    /// The sections, by crate name.
    pub(crate) sections: BTreeMap<String, CleanIslandSection>,
}

impl PackageCleanIslands {
    /// Whether the package has no island line at all.
    pub(crate) fn is_empty(&self) -> bool {
        self.units.is_none() && self.sections.is_empty()
    }

    /// Whether every proof unit of the package published its island rows, so
    /// a key no unit published is one no unit has (module docs of
    /// `crate::obligations`, CLEAN ISLANDS).
    pub(crate) fn units_whole(&self) -> bool {
        self.units.is_some_and(|units| units.proof_units == Some(units.published))
    }

    /// Whether these rows measured every island declaration of the package:
    /// every proof unit published, and every section is `verified` and
    /// complete. Only such a record is an islands base.
    pub(crate) fn measured(&self) -> bool {
        self.units_whole() && self.sections.values().all(CleanIslandSection::measured)
    }

    /// Why the package's units are not whole, or `None` when they are.
    pub(crate) fn units_problem(&self) -> Option<String> {
        match self.units {
            _ if self.units_whole() => None,
            None => Some("no compilation unit of the package published island rows".to_string()),
            Some(CleanIslandUnits { proof_units: None, .. }) => {
                Some("the run declared no proof units for the package".to_string())
            }
            Some(CleanIslandUnits { published, proof_units: Some(units) }) => Some(format!(
                "{} of {units} compilation unit(s) of the package published no island rows",
                units.saturating_sub(published)
            )),
        }
    }
}

/// Merge every unit's admitted island rows into sections by package and
/// crate: the units of one package that share a crate name (a library and its
/// own test unit, or a library and a binary of the package's name) are one
/// section. `proof_units` names the package of each proof unit the run
/// declared (`None` when it declared none): a package whose units did not all
/// publish states no proved row, as a section that is not a measurement
/// states none. A verified, complete unit with no island adds no section.
pub(crate) fn sections_of_units<'a>(
    proof_units: Option<&[&str]>,
    units: impl IntoIterator<Item = (&'a str, &'a CleanIslandRowsTransport)>,
) -> BTreeMap<String, PackageCleanIslands> {
    let mut packages: BTreeMap<String, PackageCleanIslands> = BTreeMap::new();
    for (package, rows) in units {
        let islands = packages.entry(package.to_string()).or_default();
        let declared = proof_units.map(|units| {
            u32::try_from(units.iter().filter(|unit| **unit == package).count()).unwrap_or(u32::MAX)
        });
        let counted =
            islands.units.get_or_insert(CleanIslandUnits { published: 0, proof_units: declared });
        counted.published = counted.published.saturating_add(1);
        if rows.islands == 0 && rows.phase == CleanIslandPhase::Verified && rows.complete {
            continue;
        }
        let section = CleanIslandSection::of_unit(rows);
        match islands.sections.get_mut(&rows.crate_name) {
            Some(held) => held.merge(section),
            None => {
                islands.sections.insert(rows.crate_name.clone(), section);
            }
        }
    }
    for islands in packages.values_mut() {
        if !islands.units_whole() {
            islands.sections.values_mut().for_each(CleanIslandSection::demote);
        }
    }
    packages
}

/// Write the section: the units line, then per crate in name order, its
/// line, then its rows in key order.
pub(crate) fn render(out: &mut String, islands: &PackageCleanIslands) {
    if let Some(units) = islands.units {
        push_json_line(
            out,
            &serde_json::json!({
                "clean_island_units": units.published,
                "proof_units": units.proof_units,
            }),
        );
    }
    for (crate_name, section) in &islands.sections {
        push_json_line(
            out,
            &serde_json::json!({
                "clean_islands": crate_name,
                "phase": section.phase.as_str(),
                "islands": section.islands,
                "complete": section.complete,
                "problems": section.problems,
            }),
        );
        for row in section.rows.values() {
            let record = &row.record;
            let mut line = serde_json::json!({
                "clean_decl": record.key,
                "kind": record.kind,
                "status": record.status,
                "stop": record.stop,
                "file": record.file,
                "line": record.line,
                "col": record.col,
                "source": row.source,
            });
            if let Some(basis) = &record.basis {
                line["basis"] = serde_json::Value::String(basis.clone());
            }
            push_json_line(out, &line);
        }
    }
}

/// The package's units line.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct UnitsLine {
    clean_island_units: u32,
    proof_units: Option<u32>,
}

/// A crate's island line.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SectionLine {
    clean_islands: String,
    phase: String,
    islands: u32,
    complete: bool,
    problems: Vec<String>,
}

/// An island declaration line.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DeclLine {
    clean_decl: String,
    kind: String,
    status: String,
    stop: String,
    file: String,
    line: u32,
    col: u32,
    source: Option<String>,
    #[serde(default)]
    basis: Option<String>,
}

/// Read the units line (`clean_island_units`), one section line
/// (`clean_islands`) or row line (`clean_decl`) into `islands`, refusing what
/// no writer writes: a units line that is not the first island line, that
/// counts no unit or more units than the package has, a section line before
/// it, crates out of order or repeated, `complete` that disagrees with
/// `problems`, a row before any crate line or of another crate than the last
/// one, rows out of key order, a status, stop and basis that are not one of
/// the four island verdicts, a `proved` row in a section that is not
/// `verified` and complete or in a package whose units did not all publish.
pub(crate) fn parse_line(
    islands: &mut PackageCleanIslands,
    last: &mut Option<String>,
    value: serde_json::Value,
) -> Result<(), String> {
    if value.get("clean_island_units").is_some() {
        let line = serde_json::from_value::<UnitsLine>(value)
            .map_err(|error| format!("is not an island-units line: {error}"))?;
        if islands.units.is_some() || !islands.sections.is_empty() {
            return Err("is an island-units line that is not the first island line".into());
        }
        if line.clean_island_units == 0
            || line.proof_units.is_some_and(|units| units < line.clean_island_units)
        {
            return Err(format!(
                "is an island-units line counting {} published unit(s) of {:?}",
                line.clean_island_units, line.proof_units
            ));
        }
        islands.units = Some(CleanIslandUnits {
            published: line.clean_island_units,
            proof_units: line.proof_units,
        });
        return Ok(());
    }
    if islands.units.is_none() {
        return Err("is an island line before the island-units line".into());
    }
    let units_whole = islands.units_whole();
    let sections = &mut islands.sections;
    if value.get("clean_islands").is_some() {
        let line = serde_json::from_value::<SectionLine>(value)
            .map_err(|error| format!("is not an island-section line: {error}"))?;
        let phase = CleanIslandPhase::parse(&line.phase)
            .ok_or_else(|| format!("names island phase `{}`", line.phase))?;
        if line.complete != line.problems.is_empty() {
            return Err("is an island-section line whose problems do not match `complete`".into());
        }
        if last.as_ref().is_some_and(|last| *last >= line.clean_islands) {
            return Err("is an island-section line out of crate order or repeated".into());
        }
        *last = Some(line.clean_islands.clone());
        sections.insert(
            line.clean_islands,
            CleanIslandSection {
                phase,
                islands: line.islands,
                complete: line.complete,
                problems: line.problems,
                rows: BTreeMap::new(),
            },
        );
        return Ok(());
    }
    let line = serde_json::from_value::<DeclLine>(value)
        .map_err(|error| format!("is not an island-declaration line: {error}"))?;
    let Some(crate_name) = last.as_ref() else {
        return Err("is an island-declaration line before any island-section line".into());
    };
    let section = sections.get_mut(crate_name).expect("the last section line was inserted");
    let in_crate = trust_types::obligation_identity::split_obligation_key(&line.clean_decl)
        .and_then(|(def_path, _)| def_path.strip_prefix(crate_name.as_str()))
        .and_then(|rest| rest.strip_prefix("::"))
        .is_some_and(|name| !name.is_empty());
    if !in_crate {
        return Err(format!(
            "is island declaration `{}`, which names no declaration of crate `{crate_name}`",
            line.clean_decl
        ));
    }
    if section.rows.last_key_value().is_some_and(|(key, _)| *key >= line.clean_decl) {
        return Err("is an island-declaration line out of key order or repeated".into());
    }
    let Some(verdict) =
        CleanIslandRowVerdict::of_fields(&line.status, &line.stop, line.basis.as_deref())
    else {
        return Err(format!(
            "is island declaration `{}` with status `{}`, stop `{}` and basis {:?}, which no \
             island row can state",
            line.clean_decl, line.status, line.stop, line.basis
        ));
    };
    if verdict == CleanIslandRowVerdict::Proved && !section.measured() {
        return Err(format!(
            "is a proved island declaration in a section that is {} and {}",
            section.phase.as_str(),
            if section.complete { "complete" } else { "incomplete" }
        ));
    }
    if verdict == CleanIslandRowVerdict::Proved && !units_whole {
        return Err(
            "is a proved island declaration in a package whose units did not all publish island \
             rows"
                .into(),
        );
    }
    if line.source.as_deref().is_some_and(|source| {
        source.len() != 64
            || !source.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    }) {
        return Err(format!("is island declaration `{}` with a malformed source", line.clean_decl));
    }
    let key = line.clean_decl.clone();
    section.rows.insert(
        key,
        CleanDeclRecord {
            record: ObligationRecord {
                key: line.clean_decl,
                kind: line.kind,
                status: line.status,
                stop: line.stop,
                file: Some(line.file),
                line: Some(line.line),
                col: Some(line.col),
                encoding: UNGRADED.to_string(),
                discharge: UNGRADED.to_string(),
                premises: Vec::new(),
                basis: line.basis,
            },
            source: line.source,
        },
    );
    Ok(())
}
