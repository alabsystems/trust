//! One row per declaration of a crate's `clean { … }` islands (PKG-LIVE-2),
//! keyed as a standalone `.lean` file's declaration is
//! (`trust_types::lean_declaration_identity`) with the crate name in front:
//! `<crate>::<Clean canonical name>#<16 hex>`.
//!
//! Pure code: no rustc type and no I/O. The compiler hands it each island's
//! text and Clean's outcome, in authored order (the pre-walk batch, then the
//! deferred import suffix), with what only the compiler knows: whether the
//! island's batch committed, whether each binding and seal was checked
//! against the code, whether the session was tainted, and what it could not
//! enumerate. It returns rows with island-relative offsets; the compiler maps
//! them onto file, line and column and publishes them
//! (`trust_types::clean_island_rows`).
//!
//! # Keys
//!
//! Every command Clean listed is sliced with the one shared slicer
//! (`trust_types::lean_declaration_identity::lean_command_texts`) and the
//! whole crate is named by ONE `lean_declarations` call, so `nth` and the
//! ordinals of `example`s are crate-wide, as the crate's single Clean
//! environment is. A key depends on the name, keyword, statement tokens and
//! `nth` only: inserting Rust lines above an island, moving a declaration to
//! another island, a comment or a reformat moves no key.
//!
//! # Status
//!
//! The first rule that matches decides a declaration's row. It never claims
//! more than the `.lean` lane does (`targo-trust`'s `lean_cli::records`):
//!
//! 1. REFUSED → `failed`, stopped `solver-incomplete`, basis
//!    `unproved_fail_closed`: Clean's own flag
//!    (`CleanIslandDeclaration::refused`), OR an error that is not a
//!    whole-batch refusal starting in the declaration's region, OR a model
//!    check of the declaration that found it unsafe or livelocked. Recomputed
//!    here from the FINAL outcome: errors added after Clean set its flag (a
//!    served import refused, a model found unsafe) never set it. An error or
//!    model check that lies before every command's region, or in the region
//!    of the island's header (its leading `import` commands), counts against
//!    every declaration of its island: Clean places a refused served import
//!    at its `import` command, so it refuses every declaration of the island
//!    that imports it.
//! 2. Not `verified` (the resolver's batch on a Rust front-end error: no
//!    model, binding or seal check ran), or the session did not check models
//!    and read bindings and seals (`models_and_bindings_read`: without it the
//!    outcome lists none of them, whatever the islands declare) →
//!    `unknown` / `not-dispatched`.
//! 3. Any island of the crate had an `import` served by Clean's prelude
//!    stand-in → `unknown` / `unsupported`. Crate-wide on purpose: one crate
//!    has one environment, and header-first checking lets a stand-in reach
//!    every island.
//! 4. The rows are not complete (a problem below, a tainted session among
//!    them) → `unknown` / `not-dispatched`.
//! 5. A binding or seal of the declaration that the compiler did not check
//!    against the code → `unknown` / `not-dispatched`; a model of it whose
//!    check decided nothing (`Undecided`) or that an untrusted search alone
//!    found no counterexample to (`Searched`) → `unknown` / `unsupported`.
//!    One that lies before every region, or in the header's, counts against
//!    every declaration of its island.
//! 6. The island's batch committed (`accepted`) and the island has no error
//!    and its declarations are listed → `proved`, stopped `solved`.
//! 7. Otherwise → `unknown` / `not-dispatched`.
//!
//! A declaration's REGION runs from the start of the line its keyword is on
//! (where an attribute or a model's first line is) to the start of the next
//! listed command's line (the next command's start when both are on one line;
//! the end of the text for the last).
//!
//! # Complete
//!
//! The rows are complete exactly when [`IslandRows::problems`] is empty. A
//! problem is named when the compiler's inventory was not whole (its
//! `inventory_problems`: an ambiguous island order, an island whose text could
//! not be recovered, a deferred suffix never checked, an island missing from
//! the resolver's batch), when the session was tainted, when an island's
//! declarations were not listed (it did not parse, or its unit was refused
//! before elaboration), when a listed command's span lies outside its text, or
//! when a listed command that Clean named, or that something refused, gets no
//! row (the shared slicer names no declaration for its keyword: `coinductive`,
//! say): its declaration, or its refusal, would otherwise be missing from rows
//! that claim to be the whole set. The `.lean` lane's keys stay as they are;
//! such a command makes the island rows incomplete instead.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::clean_island_rows::{
    CLEAN_ISLAND_ROWS_SCHEMA_V1, CleanIslandPhase, CleanIslandRow, CleanIslandRowVerdict,
    CleanIslandRowsTransport,
};
use trust_types::lean_declaration_identity::{lean_command_texts, lean_declarations};
use trust_types::obligation_identity::obligation_key;

use crate::clean_island::{CleanIslandDeclaration, CleanIslandModelVerdict, CleanIslandOutcome};

/// One island of the crate, in authored order.
#[derive(Debug, Clone, Copy)]
pub struct IslandRowInput<'a> {
    /// The island's text, which Clean's offsets index.
    pub text: &'a str,
    /// Clean's final outcome for it.
    pub outcome: &'a CleanIslandOutcome,
    /// Whether the island's batch committed: in the pre-walk batch, that the
    /// batch was not rejected (`CleanIslandBatch::is_rejected`); in the
    /// deferred suffix, that the surviving batch committed
    /// (`CleanImportBatch::committed`) and this unit is not among its
    /// `refused_islands`.
    pub accepted: bool,
    /// For each of `outcome.bindings`, by index, whether the compiler checked
    /// it against the crate's code and it held. A missing entry is unchecked.
    pub bindings_checked: &'a [bool],
    /// The same for `outcome.seals`.
    pub seals_checked: &'a [bool],
}

/// What the compiler knows about the whole crate's islands.
#[derive(Debug, Clone, Default)]
pub struct CrateIslandFacts {
    /// The verification pass ran (`false` on a Rust front-end error: the
    /// rows are the resolver's batch).
    pub verified: bool,
    /// The session checked the finite models its islands declare and read
    /// their bindings and seals
    /// ([`crate::clean_island::CleanIslandSession::models_and_bindings_read`]).
    /// Without it `model_checks`, `bindings` and `seals` are empty whatever
    /// the islands declare, so no row is proved (module docs, rule 2).
    pub models_and_bindings_read: bool,
    /// The crate's Clean session was tainted after the islands were checked
    /// (`CleanIslandSession::is_tainted`), read after the deferred suffix and
    /// the citation sweep.
    pub tainted: bool,
    /// Why the compiler's inventory of the islands is not whole, one sentence
    /// each.
    pub inventory_problems: Vec<String>,
}

/// One declaration's row, before the compiler places it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IslandRow {
    /// Index of the island in the input.
    pub island: usize,
    /// Island-relative byte offset of the declaration's keyword.
    pub offset: usize,
    /// `<crate>::<name>#<16 hex>`.
    pub key: String,
    /// `lean:<keyword>`, spaces as `-`.
    pub kind: String,
    pub verdict: CleanIslandRowVerdict,
    /// The declaration's source digest when its def path is unique among the
    /// crate's island declarations.
    pub source: Option<String>,
}

/// Every island declaration's row, in authored order, and why they are not
/// the whole set.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct IslandRows {
    pub rows: Vec<IslandRow>,
    /// Empty exactly when the rows are complete (module docs).
    pub problems: Vec<String>,
}

impl IslandRows {
    /// Whether every declaration of every island has a row.
    #[must_use]
    pub fn complete(&self) -> bool {
        self.problems.is_empty()
    }

    /// The transport message of these rows. `locate` maps an island index and
    /// an island-relative offset onto `(file, line, column)`, one-based. Rows
    /// are put in key order; a key twice (which one naming call cannot mint)
    /// keeps its worse verdict.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn transport(
        &self,
        crate_name: &str,
        package_name: &str,
        verification_session: &str,
        primary_package: bool,
        phase: CleanIslandPhase,
        islands: u32,
        mut locate: impl FnMut(usize, usize) -> (String, u32, u32),
    ) -> CleanIslandRowsTransport {
        let mut rows: BTreeMap<&str, (CleanIslandRowVerdict, &IslandRow)> = BTreeMap::new();
        for row in &self.rows {
            rows.entry(&row.key)
                .and_modify(|(verdict, _)| *verdict = verdict.worse(row.verdict))
                .or_insert((row.verdict, row));
        }
        CleanIslandRowsTransport {
            schema: CLEAN_ISLAND_ROWS_SCHEMA_V1.to_string(),
            crate_name: crate_name.to_string(),
            package_name: package_name.to_string(),
            verification_session: verification_session.to_string(),
            primary_package,
            phase,
            islands,
            complete: self.complete(),
            problems: self.problems.clone(),
            rows: rows
                .into_values()
                .map(|(verdict, row)| {
                    let (file, line, col) = locate(row.island, row.offset);
                    CleanIslandRow {
                        key: row.key.clone(),
                        kind: row.kind.clone(),
                        status: verdict.status().to_string(),
                        stop: verdict.stop().to_string(),
                        basis: verdict.basis().map(str::to_string),
                        file,
                        line,
                        col,
                        source: row.source.clone(),
                    }
                })
                .collect(),
        }
    }
}

/// The start of the line `at` is on.
fn line_start(text: &str, at: usize) -> usize {
    text.get(..at).and_then(|before| before.rfind('\n')).map_or(0, |newline| newline + 1)
}

/// Each listed command's region start (module docs): its keyword's line, or
/// its keyword when the command before it is on the same line.
fn command_regions(text: &str, listed: &[CleanIslandDeclaration]) -> Vec<usize> {
    listed
        .iter()
        .enumerate()
        .map(|(at, d)| {
            let line = line_start(text, d.start);
            match at.checked_sub(1).map(|before| listed[before].start) {
                Some(before) if before >= line => d.start,
                _ => line,
            }
        })
        .collect()
}

/// The command whose region holds `at` (module docs), or `None` before every
/// region.
fn owner(regions: &[usize], at: usize) -> Option<usize> {
    regions.iter().rposition(|start| *start <= at)
}

/// What an island's final outcome says about one listed command (module
/// docs, rules 1 and 5).
#[derive(Clone, Copy)]
struct CommandFacts {
    /// Rule 1: something refused it.
    refused: bool,
    /// Rule 5: a binding or seal of it the compiler did not check.
    unchecked_data: bool,
    /// Rule 5: a model of it whose check decided nothing.
    undecided_model: bool,
}

fn command_facts(island: &IslandRowInput<'_>, regions: &[usize], command: usize) -> CommandFacts {
    let outcome = island.outcome;
    let this = &outcome.declarations.as_deref().unwrap_or_default()[command];
    let listed = outcome.declarations.as_deref().unwrap_or_default();
    // The island's header: its leading `import` commands. Clean places a
    // refused served import at its `import`, so a fact there is the whole
    // island's, as one before every region is.
    let header = listed
        .iter()
        .take_while(|command| {
            island.text.get(command.start..).is_some_and(|text| {
                text.strip_prefix("import")
                    .is_some_and(|rest| rest.starts_with(char::is_whitespace))
            })
        })
        .count();
    let own = |at: usize| owner(regions, at) == Some(command);
    // Clean's own reading of "in this declaration".
    let inside = |at: usize| at >= this.start && (at < this.end || at == this.start);
    // A fact before every region, or in the header's, counts against every
    // command of its island.
    let counts =
        |at: usize| own(at) || inside(at) || owner(regions, at).is_none_or(|at| at < header);
    let refused = this.refused
        || outcome.errors.iter().any(|error| !error.is_whole_batch() && counts(error.start))
        || outcome.model_checks.iter().any(|check| {
            counts(check.start)
                && matches!(
                    check.verdict,
                    CleanIslandModelVerdict::Unsafe { .. }
                        | CleanIslandModelVerdict::Livelock { .. }
                )
        });
    let unchecked_data = outcome.bindings.iter().enumerate().any(|(at, binding)| {
        counts(binding.start) && !island.bindings_checked.get(at).copied().unwrap_or(false)
    }) || outcome.seals.iter().enumerate().any(|(at, seal)| {
        counts(seal.start) && !island.seals_checked.get(at).copied().unwrap_or(false)
    });
    let undecided_model = outcome.model_checks.iter().any(|check| {
        counts(check.start)
            && !matches!(
                check.verdict,
                CleanIslandModelVerdict::Safe { .. } | CleanIslandModelVerdict::Live { .. }
            )
    });
    CommandFacts { refused, unchecked_data, undecided_model }
}

/// The rows of a crate's islands (module docs).
#[must_use]
pub fn clean_island_rows(
    crate_name: &str,
    islands: &[IslandRowInput<'_>],
    facts: &CrateIslandFacts,
) -> IslandRows {
    let mut problems = facts.inventory_problems.clone();
    if facts.tainted {
        problems.push(
            "the crate's Clean session was tainted: a refusal or an integrity failure reached \
             the shared environment, so no declaration of it is accepted"
                .to_string(),
        );
    }
    let standin = islands.iter().any(|island| !island.outcome.standin_imports.is_empty());
    // Every readable command of the crate, in authored order:
    // (island, command index, its text); and each island's regions.
    let mut commands: Vec<(usize, usize, &str)> = Vec::new();
    let mut regions: Vec<Vec<usize>> = Vec::with_capacity(islands.len());
    for (index, island) in islands.iter().enumerate() {
        let Some(listed) = island.outcome.declarations.as_deref() else {
            problems.push(format!(
                "island {} was not enumerated: it did not parse, or its unit was refused before \
                 elaboration",
                index + 1
            ));
            regions.push(Vec::new());
            continue;
        };
        regions.push(command_regions(island.text, listed));
        let spans: Vec<(usize, usize)> = listed.iter().map(|d| (d.start, d.end)).collect();
        let texts = lean_command_texts(island.text, &spans);
        if texts.iter().any(Option::is_none) {
            problems.push(format!(
                "island {}: a command's span lies outside the island's text",
                index + 1
            ));
        }
        for (command, text) in texts.into_iter().enumerate() {
            if let Some(text) = text {
                commands.push((index, command, text));
            }
        }
    }
    let listed = |index: usize| islands[index].outcome.declarations.as_deref().unwrap_or_default();
    let named = lean_declarations(
        commands
            .iter()
            .map(|&(island, command, text)| (listed(island)[command].name.as_deref(), text)),
    );
    let mut per_name: BTreeMap<&str, usize> = BTreeMap::new();
    for declaration in named.iter().flatten() {
        *per_name.entry(declaration.name.as_str()).or_default() += 1;
    }
    let facts_of: Vec<CommandFacts> = commands
        .iter()
        .map(|&(index, command, _)| command_facts(&islands[index], &regions[index], command))
        .collect();
    // A command Clean named, or that something refused, with no row: its
    // declaration or its refusal would be missing from rows that say they
    // are the whole set (module docs, Complete).
    for ((&(index, command, _), declaration), command_facts) in
        commands.iter().zip(&named).zip(&facts_of)
    {
        let this = &listed(index)[command];
        if declaration.is_none() && (this.name.is_some() || command_facts.refused) {
            let what = this.name.as_deref().map_or_else(
                || format!("the command at byte {}", this.start),
                |name| format!("declaration `{name}`"),
            );
            problems.push(format!(
                "island {}: {what} has no row{}",
                index + 1,
                if command_facts.refused { ", and something refused it" } else { "" }
            ));
        }
    }
    let complete = problems.is_empty();
    let mut rows = Vec::new();
    for ((&(index, command, _), declaration), command_facts) in
        commands.iter().zip(&named).zip(&facts_of)
    {
        let Some(declaration) = declaration else { continue };
        let island = &islands[index];
        let this = &listed(index)[command];
        let CommandFacts { refused, unchecked_data, undecided_model } = *command_facts;
        let verdict = if refused {
            CleanIslandRowVerdict::ProofRefused
        } else if !facts.verified || !facts.models_and_bindings_read {
            CleanIslandRowVerdict::NotDispatched
        } else if standin {
            CleanIslandRowVerdict::Unsupported
        } else if !complete || unchecked_data {
            CleanIslandRowVerdict::NotDispatched
        } else if undecided_model {
            CleanIslandRowVerdict::Unsupported
        } else if island.accepted && island.outcome.errors.is_empty() {
            CleanIslandRowVerdict::Proved
        } else {
            CleanIslandRowVerdict::NotDispatched
        };
        rows.push(IslandRow {
            island: index,
            offset: this.start,
            key: obligation_key(
                &format!("{crate_name}::{}", declaration.name),
                &declaration.local_id,
            ),
            kind: format!("lean:{}", declaration.keyword.replace(' ', "-")),
            verdict,
            source: (per_name[declaration.name.as_str()] == 1)
                .then(|| declaration.source_digest.clone()),
        });
    }
    IslandRows { rows, problems }
}

#[cfg(test)]
#[path = "clean_island_rows_tests.rs"]
mod tests;
