// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! The obligation-birth cutover SCORECARD — the machine-readable, per-class
//! promotion of the [`crate::NativeGenOutcome`] counters that
//! `docs/design/2026-08-27-two-language-direct-to-trust-ir.md` §6 step 2 names
//! as required entry work: *"the `NativeGenOutcome` counters exist today only
//! as `debug!` lines — promoting them into a measured scorecard artifact is
//! part of this step's entry work, or the gate is uncheckable."*
//!
//! The Stage C/D cutover gate this makes checkable, per obligation class:
//! **`NativeGenerated` fraction at 100% for the class on the measurement
//! corpus with zero `Disagreed`.** This module renders exactly that question,
//! and nothing stronger:
//!
//! * a class row's `cutover_entry_gate.eligible` is CORPUS-LOCAL evidence for
//!   the class-by-class flip's entry condition — it is never a G4/G6 verdict,
//!   never verdict parity, and never a product-completion claim
//!   (`docs/TWO_LANGUAGE_100_PERCENT_GOAL.md` §1: a corpus-local pass "does
//!   not establish" the product gates);
//! * the scorecard CHANGES NOTHING it measures: the aggregation consumes the
//!   outcomes the production entry point
//!   ([`crate::generate_native_or_flip_safety_vcs_with_discharged`]) already
//!   returns, so the dispatched VC set is byte-identical with or without a
//!   measurement run.
//!
//! # Division of labor (why the corpus walk is NOT in this module)
//!
//! Deriving an outcome for a dump requires trust-vcgen (to reproduce the VC
//! set the flip compares against), and trust-vcgen is deliberately a
//! DEV-dependency of this crate — the production link closure must not grow a
//! second producer (`Cargo.toml`'s own note). So the corpus walk lives in
//! `examples/native_gen_scorecard.rs` (examples resolve dev-dependencies) and
//! in `#[cfg(test)]` harnesses; this module owns the part worth unit-testing:
//! per-function rows in, deterministic artifact out.
//!
//! # Accounting rules, stated once
//!
//! * A function COUNTS FOR a class when its dispatched L0 safety set contains
//!   a VC of that class. A `Disagreed` function additionally TOUCHES every
//!   class in its producer diff — including a `native_only` class that is in
//!   no dispatched set at all (that is the alarm direction: an obligation
//!   nothing checks cannot be invisible to the gate for its own class).
//! * `spine_declined` is probed DIRECTLY (`generate_native_safety_vcs(..) ==
//!   None`), never inferred from `FlippedFallback` — the ratchet's measured
//!   lesson: fallback conflates "spine declined" with "spine agreed on the
//!   enumeration but not byte-for-byte on a formula", and only the first is
//!   the laundering hazard.
//! * A corpus file that fails to read or parse is COUNTED AND NAMED, never
//!   silently skipped: a scorecard whose denominator quietly shrank is the
//!   exact defect the completion goal's G3 language exists to refuse.

use std::collections::{BTreeMap, BTreeSet};

/// The artifact schema tag. Bump only with a rendering change a consumer could
/// misread across versions.
pub const NATIVE_GEN_SCORECARD_SCHEMA: &str = "trust.native-gen-scorecard/v1";

/// The three per-function outcomes of the production entry point, plus nothing:
/// this is a projection of [`crate::NativeGenOutcome`], carried without its
/// payloads so measurement rows stay cheap to build and impossible to
/// misaggregate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutcomeClass {
    /// The spine generated the dispatched L0 safety set (validated ==
    /// trust-vcgen).
    NativeGenerated,
    /// The verdict-flip ran over trust-vcgen's VCs (spine declined, or the
    /// enumeration matched without byte-equal formulas). Nothing unchecked.
    FlippedFallback,
    /// The two producers disagree about WHICH obligations exist. Dispatch is
    /// unchanged, and the diff rows are the finding.
    Disagreed,
}

/// One measured function: what the producer harness derived by running the
/// production entry point over one dump instance.
#[derive(Debug, Clone)]
pub struct FunctionOutcomeRow {
    pub def_path: String,
    /// First 16 hex digits of `VerifiableFunction::content_hash` — the corpus
    /// identity key the decline census established (survives renames,
    /// separates same-def_path instances).
    pub content_hash16: String,
    pub outcome: OutcomeClass,
    /// Direct probe: `generate_native_safety_vcs(func).is_none()`.
    pub spine_declined: bool,
    /// Obligation class -> count over the DISPATCHED L0 safety VCs
    /// (class strings from [`crate::ObligationKey::class_of`], so scorecard
    /// rows and `ObligationKey.class` findings can never drift apart).
    pub dispatched_l0_classes: BTreeMap<String, usize>,
    /// Classes of the `native_only` diff rows (Disagreed only; else empty).
    pub native_only_classes: Vec<String>,
    /// Classes of the `vcgen_only` diff rows (Disagreed only; else empty).
    pub vcgen_only_classes: Vec<String>,
}

/// One corpus file the harness could not turn into a row. Disclosed, never
/// dropped.
#[derive(Debug, Clone)]
pub struct CorpusLoss {
    pub path: String,
    pub reason: String,
}

/// The aggregated scorecard.
#[derive(Debug)]
pub struct NativeGenScorecard {
    functions: usize,
    native_generated: usize,
    flipped_fallback: usize,
    disagreed: usize,
    spine_declined: usize,
    corpus_digest: String,
    losses: Vec<CorpusLoss>,
    files_scanned: usize,
    classes: BTreeMap<String, ClassRow>,
}

/// Per-class aggregation. All counts are over functions/VCs as defined in the
/// module docs' accounting rules.
#[derive(Debug, Default)]
struct ClassRow {
    functions_dispatching: usize,
    functions_native: usize,
    functions_fallback: usize,
    functions_disagreed_dispatching: usize,
    /// Disagreed functions touching the class via dispatched set OR either
    /// diff direction. `>= functions_disagreed_dispatching`.
    functions_disagreed_touching: usize,
    vcs_total: usize,
    vcs_native_generated: usize,
    native_only_rows: usize,
    vcgen_only_rows: usize,
}

impl ClassRow {
    /// The Stage C/D per-class entry condition, corpus-locally: every function
    /// dispatching the class is NativeGenerated and no Disagreed function
    /// touches it. An empty class is NOT eligible — an entry gate over nothing
    /// is vacuous, and vacuous green is one of the five lies the strict
    /// fragment file enumerates.
    fn eligible(&self) -> bool {
        self.functions_dispatching > 0
            && self.functions_native == self.functions_dispatching
            && self.functions_disagreed_touching == 0
    }
}

impl NativeGenScorecard {
    /// Aggregate measured rows into the scorecard. Deterministic in the
    /// mathematical sense: any permutation of `rows`/`losses` renders the
    /// identical artifact (BTree containers throughout; the corpus digest
    /// sorts its material).
    #[must_use]
    pub fn measure(
        rows: &[FunctionOutcomeRow],
        losses: Vec<CorpusLoss>,
        files_scanned: usize,
    ) -> Self {
        let mut card = NativeGenScorecard {
            functions: rows.len(),
            native_generated: 0,
            flipped_fallback: 0,
            disagreed: 0,
            spine_declined: 0,
            corpus_digest: corpus_digest(rows),
            losses,
            files_scanned,
            classes: BTreeMap::new(),
        };
        for row in rows {
            match row.outcome {
                OutcomeClass::NativeGenerated => card.native_generated += 1,
                OutcomeClass::FlippedFallback => card.flipped_fallback += 1,
                OutcomeClass::Disagreed => card.disagreed += 1,
            }
            if row.spine_declined {
                card.spine_declined += 1;
            }
            for (class, count) in &row.dispatched_l0_classes {
                let entry = card.classes.entry(class.clone()).or_default();
                entry.functions_dispatching += 1;
                entry.vcs_total += count;
                match row.outcome {
                    OutcomeClass::NativeGenerated => {
                        entry.functions_native += 1;
                        entry.vcs_native_generated += count;
                    }
                    OutcomeClass::FlippedFallback => entry.functions_fallback += 1,
                    OutcomeClass::Disagreed => entry.functions_disagreed_dispatching += 1,
                }
            }
            for class in &row.native_only_classes {
                card.classes.entry(class.clone()).or_default().native_only_rows += 1;
            }
            for class in &row.vcgen_only_classes {
                card.classes.entry(class.clone()).or_default().vcgen_only_rows += 1;
            }
            if row.outcome == OutcomeClass::Disagreed {
                let touched: BTreeSet<&String> = row
                    .dispatched_l0_classes
                    .keys()
                    .chain(&row.native_only_classes)
                    .chain(&row.vcgen_only_classes)
                    .collect();
                for class in touched {
                    card.classes.entry(class.clone()).or_default().functions_disagreed_touching +=
                        1;
                }
            }
        }
        card
    }

    /// The number of classes whose corpus-local entry condition holds.
    #[must_use]
    pub fn eligible_classes(&self) -> usize {
        self.classes.values().filter(|row| row.eligible()).count()
    }

    /// Render the artifact. The schema is versioned and every honesty banner is
    /// IN the artifact, because artifacts outlive the prose around them.
    #[must_use]
    pub fn to_json(&self) -> serde_json::Value {
        let classes: Vec<serde_json::Value> = self
            .classes
            .iter()
            .map(|(class, row)| {
                serde_json::json!({
                    "class": class,
                    "functions_dispatching": row.functions_dispatching,
                    "functions_native": row.functions_native,
                    "functions_fallback": row.functions_fallback,
                    "functions_disagreed_dispatching": row.functions_disagreed_dispatching,
                    "functions_disagreed_touching": row.functions_disagreed_touching,
                    "vcs_total": row.vcs_total,
                    "vcs_native_generated": row.vcs_native_generated,
                    "native_only_rows": row.native_only_rows,
                    "vcgen_only_rows": row.vcgen_only_rows,
                    "cutover_entry_gate": {
                        "native_fraction_100": row.functions_dispatching > 0
                            && row.functions_native == row.functions_dispatching,
                        "zero_disagreed": row.functions_disagreed_touching == 0
                            && row.native_only_rows == 0
                            && row.vcgen_only_rows == 0,
                        "eligible": row.eligible()
                            && row.native_only_rows == 0
                            && row.vcgen_only_rows == 0,
                    },
                })
            })
            .collect();
        let losses: Vec<serde_json::Value> = self
            .losses
            .iter()
            .map(|loss| serde_json::json!({ "path": loss.path, "reason": loss.reason }))
            .collect();
        serde_json::json!({
            "schema": NATIVE_GEN_SCORECARD_SCHEMA,
            "claim": "corpus-local Stage C/D cutover entry evidence ONLY; never a \
                      G4/G6 verdict, never verdict parity, never product completion",
            "corpus": {
                "files_scanned": self.files_scanned,
                "functions": self.functions,
                "losses": losses,
                "corpus_digest": self.corpus_digest,
            },
            "outcomes": {
                "native_generated": self.native_generated,
                "flipped_fallback": self.flipped_fallback,
                "disagreed": self.disagreed,
                "spine_declined": self.spine_declined,
            },
            "classes": classes,
            "eligible_classes": self.eligible_classes(),
        })
    }
}

/// The corpus content identity: SHA-256 over the sorted `def_path\thash16\n`
/// lines. Two scorecards are comparable only when this matches — the same rule
/// the completion goal applies to every population claim.
fn corpus_digest(rows: &[FunctionOutcomeRow]) -> String {
    let mut lines: Vec<String> =
        rows.iter().map(|row| format!("{}\t{}\n", row.def_path, row.content_hash16)).collect();
    lines.sort();
    let material: String = lines.concat();
    format!("sha256:{}", trust_types::digest::stable_sha256_hex(material.as_bytes()))
}

/// Build one measurement row from a dump's derived pieces. Kept here (not in
/// the example) so the classification logic is unit-tested where the
/// aggregation is.
#[must_use]
pub fn classify_function(
    def_path: String,
    content_hash16: String,
    spine_declined: bool,
    dispatched: &[trust_types::VerificationCondition],
    outcome: &crate::NativeGenOutcome,
) -> FunctionOutcomeRow {
    let mut dispatched_l0_classes: BTreeMap<String, usize> = BTreeMap::new();
    for vc in dispatched {
        if vc.kind.proof_level() == trust_types::ProofLevel::L0Safety {
            *dispatched_l0_classes.entry(crate::ObligationKey::class_of(&vc.kind)).or_insert(0) +=
                1;
        }
    }
    let (outcome_class, native_only_classes, vcgen_only_classes) = match outcome {
        crate::NativeGenOutcome::NativeGenerated(_) => {
            (OutcomeClass::NativeGenerated, Vec::new(), Vec::new())
        }
        crate::NativeGenOutcome::FlippedFallback(_) => {
            (OutcomeClass::FlippedFallback, Vec::new(), Vec::new())
        }
        crate::NativeGenOutcome::Disagreed { diff, .. } => (
            OutcomeClass::Disagreed,
            diff.native_only.iter().map(|key| key.class.clone()).collect(),
            diff.vcgen_only.iter().map(|key| key.class.clone()).collect(),
        ),
    };
    FunctionOutcomeRow {
        def_path,
        content_hash16,
        outcome: outcome_class,
        spine_declined,
        dispatched_l0_classes,
        native_only_classes,
        vcgen_only_classes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(
        def_path: &str,
        outcome: OutcomeClass,
        dispatched: &[(&str, usize)],
    ) -> FunctionOutcomeRow {
        FunctionOutcomeRow {
            def_path: def_path.to_string(),
            content_hash16: format!("{:016x}", def_path.len() as u64),
            outcome,
            spine_declined: false,
            dispatched_l0_classes: dispatched
                .iter()
                .map(|(class, count)| ((*class).to_string(), *count))
                .collect(),
            native_only_classes: Vec::new(),
            vcgen_only_classes: Vec::new(),
        }
    }

    #[test]
    fn per_class_rows_partition_functions_and_vcs() {
        let rows = vec![
            row("a", OutcomeClass::NativeGenerated, &[("BoundsCheck", 2)]),
            row("b", OutcomeClass::FlippedFallback, &[("BoundsCheck", 1)]),
            row("c", OutcomeClass::NativeGenerated, &[("DivisionByZero", 1)]),
        ];
        let card = NativeGenScorecard::measure(&rows, Vec::new(), 3);
        let json = card.to_json();
        let classes = json["classes"].as_array().expect("classes");
        let bounds = classes.iter().find(|c| c["class"] == "BoundsCheck").expect("BoundsCheck");
        assert_eq!(bounds["functions_dispatching"], 2);
        assert_eq!(bounds["functions_native"], 1);
        assert_eq!(bounds["functions_fallback"], 1);
        assert_eq!(bounds["vcs_total"], 3);
        assert_eq!(bounds["vcs_native_generated"], 2);
        assert_eq!(bounds["cutover_entry_gate"]["eligible"], false);
        let div = classes.iter().find(|c| c["class"] == "DivisionByZero").expect("div");
        assert_eq!(div["cutover_entry_gate"]["eligible"], true);
        assert_eq!(json["eligible_classes"], 1);
        assert_eq!(json["outcomes"]["native_generated"], 2);
        assert_eq!(json["outcomes"]["flipped_fallback"], 1);
    }

    #[test]
    fn a_disagreed_function_makes_every_touched_class_ineligible() {
        // The alarm direction: the native_only class is in NO dispatched set,
        // and it must still be ineligible — an obligation nothing checks cannot
        // be invisible to the gate for its own class.
        let mut disagreed = row("d", OutcomeClass::Disagreed, &[("BoundsCheck", 1)]);
        disagreed.native_only_classes = vec!["ArithmeticOverflow(Add)".to_string()];
        let clean = row("a", OutcomeClass::NativeGenerated, &[("ArithmeticOverflow(Add)", 1)]);
        let card = NativeGenScorecard::measure(&[clean.clone(), disagreed], Vec::new(), 2);
        let json = card.to_json();
        let classes = json["classes"].as_array().expect("classes");
        let add =
            classes.iter().find(|c| c["class"] == "ArithmeticOverflow(Add)").expect("Add row");
        assert_eq!(add["functions_disagreed_touching"], 1);
        assert_eq!(add["native_only_rows"], 1);
        assert_eq!(add["cutover_entry_gate"]["eligible"], false);
        let bounds = classes.iter().find(|c| c["class"] == "BoundsCheck").expect("BoundsCheck");
        assert_eq!(bounds["cutover_entry_gate"]["eligible"], false);

        // MUTATION CONTROL: clearing the disagreement flips Add to eligible —
        // the gate can fail AND can pass, so it is a gate.
        let repaired = row("d", OutcomeClass::NativeGenerated, &[("BoundsCheck", 1)]);
        let card = NativeGenScorecard::measure(&[clean, repaired], Vec::new(), 2);
        let json = card.to_json();
        let classes = json["classes"].as_array().expect("classes");
        let add =
            classes.iter().find(|c| c["class"] == "ArithmeticOverflow(Add)").expect("Add row");
        assert_eq!(add["cutover_entry_gate"]["eligible"], true);
        let bounds = classes.iter().find(|c| c["class"] == "BoundsCheck").expect("BoundsCheck");
        assert_eq!(bounds["cutover_entry_gate"]["eligible"], true);
    }

    #[test]
    fn an_empty_class_population_is_not_eligible() {
        // A class that only appears via diff rows has functions_dispatching == 0
        // and must read ineligible: vacuous green is not green.
        let mut disagreed = row("d", OutcomeClass::Disagreed, &[]);
        disagreed.vcgen_only_classes = vec!["Unreachable".to_string()];
        let card = NativeGenScorecard::measure(&[disagreed], Vec::new(), 1);
        let json = card.to_json();
        let unreachable = json["classes"]
            .as_array()
            .expect("classes")
            .iter()
            .find(|c| c["class"] == "Unreachable")
            .cloned()
            .expect("Unreachable row");
        assert_eq!(unreachable["functions_dispatching"], 0);
        assert_eq!(unreachable["cutover_entry_gate"]["eligible"], false);
    }

    #[test]
    fn rendering_is_order_independent_and_digest_binds_content() {
        let a = row("a", OutcomeClass::NativeGenerated, &[("BoundsCheck", 1)]);
        let b = row("b", OutcomeClass::FlippedFallback, &[("DivisionByZero", 2)]);
        let forward = NativeGenScorecard::measure(&[a.clone(), b.clone()], Vec::new(), 2);
        let backward = NativeGenScorecard::measure(&[b, a.clone()], Vec::new(), 2);
        assert_eq!(forward.to_json(), backward.to_json());

        // A content change moves the digest.
        let mut mutated = a;
        mutated.content_hash16 = "ffffffffffffffff".to_string();
        let changed = NativeGenScorecard::measure(&[mutated], Vec::new(), 1);
        assert_ne!(
            forward.to_json()["corpus"]["corpus_digest"],
            changed.to_json()["corpus"]["corpus_digest"]
        );
    }

    #[test]
    fn losses_are_disclosed_in_the_artifact() {
        let card = NativeGenScorecard::measure(
            &[],
            vec![CorpusLoss { path: "x/bad.json".to_string(), reason: "parse: EOF".to_string() }],
            1,
        );
        let json = card.to_json();
        assert_eq!(json["corpus"]["losses"][0]["path"], "x/bad.json");
        assert_eq!(json["corpus"]["functions"], 0);
        assert_eq!(json["corpus"]["files_scanned"], 1);
    }
}
