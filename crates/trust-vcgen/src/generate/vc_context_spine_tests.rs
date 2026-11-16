//! T3 L4 (C06): the per-function VC context's spine against this crate's own block-def
//! rule, on the in-tree fixtures and the generated families.
//!
//! `trust_types::vc_context` reads the block-def relevance rule as a closure over its DAG
//! (`vc_context::spine`), with the per-function relevance names supplied as data. These
//! tests pin both halves against the functions they mirror:
//!
//! * the names its walk collects equal [`collect_formula_var_names`] on every row formula,
//!   record formula and candidate fact the fixtures produce;
//! * a Spine row over a function's candidate facts materializes as
//!   [`combine_relevant_block_defs_recorded`] combines them, kept order included, and
//!   records its kept facts as the eager recorder does (none when nothing is kept).
//!
//! The relevance names are the data vcgen supplies: each raw name's spelling after
//! [`collect_relevance_var_names`]'s collapse.
//!
//! From C08 the generation supplies them itself, and joins its block-def rows as Spine
//! rows (`super::recipes`): on the fixtures, a generation into a context returns the rows
//! `generate_vcs` returns, the row oracle sees no disagreement, every Spine row's node
//! count and digest are its materialized formula's (I4, I5), and the Spine attempts
//! charge no work meter.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use trust_types::determinism::query_size;
use trust_types::formula_merkle::formula_digest;
use trust_types::fx::FxHashSet;
use trust_types::vc_context::{
    Oracle, RecordRef, RelevanceRule, RowFormula, RowId, Spine, SpineRow, VcContext, VcRow,
    WrapperRef, same_row,
};
use trust_types::{
    Formula, ObligationWrapper, PathGuardTerm, Sort, VerifiableFunction, VerificationCondition,
};

use super::recipes::Spines;
use super::{
    KeepOrigins, collect_formula_var_names, collect_relevance_var_names,
    combine_relevant_block_defs_recorded, generate_vcs_impl_with_origins,
};

/// How many fixtures a test reads: the sorted prefix, enough to cover every family of
/// fixture directory while keeping the unit suite fast. `vc_context_parity_probe` reads
/// them all.
const FIXTURE_SAMPLE: usize = 400;

/// How many of those the work-meter test generates twice more.
const METER_SAMPLE: usize = 60;

fn json_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else { return };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            json_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "json") {
            out.push(path);
        }
    }
}

/// The fixture functions and their rows (a fixture that does not parse or whose
/// generation panics is skipped, as the row-parity probe prints it), generated once for
/// the tests of this module.
fn fixture_functions() -> &'static [(VerifiableFunction, Vec<VerificationCondition>)] {
    static FIXTURES: OnceLock<Vec<(VerifiableFunction, Vec<VerificationCondition>)>> =
        OnceLock::new();
    FIXTURES.get_or_init(generate_fixture_functions)
}

fn generate_fixture_functions() -> Vec<(VerifiableFunction, Vec<VerificationCondition>)> {
    let mut files = Vec::new();
    json_files(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests"), &mut files);
    files.sort();
    let mut out = Vec::new();
    for path in files.into_iter().take(FIXTURE_SAMPLE) {
        let Some(func) = std::fs::read_to_string(&path)
            .ok()
            .and_then(|text| serde_json::from_str::<VerifiableFunction>(&text).ok())
        else {
            continue;
        };
        let Ok(vcs) = catch_unwind(AssertUnwindSafe(|| crate::generate_vcs(&func))) else {
            continue;
        };
        out.push((func, vcs));
    }
    out
}

/// Every formula a row carries: its formula and its record's.
fn row_formulas(vc: &VerificationCondition) -> Vec<&Formula> {
    let mut formulas = vec![&vc.formula];
    if let Some(record) = &vc.obligation {
        formulas.push(&record.body);
        formulas.extend(record.subject.as_ref());
        for wrapper in &record.wrappers {
            match wrapper {
                ObligationWrapper::ConjoinFactsLast { facts } => formulas.extend(facts),
                ObligationWrapper::PathGuardOr { paths } => {
                    for path in paths {
                        if let PathGuardTerm::Guarded { guards } = path {
                            formulas.extend(guards);
                        }
                    }
                }
            }
        }
    }
    formulas
}

fn raw_names(formula: &Formula) -> BTreeSet<String> {
    let mut names = FxHashSet::default();
    collect_formula_var_names(formula, &mut names);
    names.into_iter().collect()
}

/// The relevance names of `formulas`' variables in `func`: the data vcgen supplies.
fn supply_relevance(context: &mut VcContext, func: &VerifiableFunction, formulas: &[&Formula]) {
    for formula in formulas {
        for name in raw_names(formula) {
            let mut collapsed = FxHashSet::default();
            collect_relevance_var_names(
                func,
                &Formula::Var(name.clone(), Sort::Int),
                &mut collapsed,
            );
            if let [relevance] = collapsed.into_iter().collect::<Vec<_>>().as_slice() {
                if *relevance != name {
                    context.vars_mut().insert(name.clone(), relevance.clone());
                }
            }
        }
    }
}

#[test]
fn the_context_collects_the_names_this_crate_collects() {
    let functions = fixture_functions();
    assert!(!functions.is_empty(), "no fixture parsed");
    let mut checked = 0usize;
    for (_, vcs) in functions {
        let mut context = VcContext::new();
        for vc in vcs {
            for formula in row_formulas(vc) {
                let node = context.intern(formula);
                assert_eq!(
                    context.formula_var_names(node).ok(),
                    Some(raw_names(formula)),
                    "{formula:?}"
                );
                checked += 1;
            }
        }
    }
    // Measured 2026-10-11: 32,917 formulas over the 400-fixture sample.
    assert!(checked > 10_000, "only {checked} formulas: the sample stopped exercising the walk");
}

/// One spine over `candidates` and `body` in `func`, against the eager combination.
fn assert_spine_is_the_eager_combination(
    func: &VerifiableFunction,
    candidates: &[Formula],
    body: &Formula,
) -> bool {
    let (combined, kept) =
        combine_relevant_block_defs_recorded(func, candidates.to_vec(), body.clone());
    let mut context = VcContext::new();
    let mut all: Vec<&Formula> = candidates.iter().collect();
    all.push(body);
    supply_relevance(&mut context, func, &all);
    let nodes: Vec<_> = candidates.iter().map(|fact| context.intern(fact)).collect();
    let seq = context.seq(&nodes).expect("nodes of this context");
    let body_node = context.intern(body);
    let row = context
        .push_spine_row(SpineRow {
            kind: trust_types::VcKind::DivisionByZero,
            function: trust_types::Symbol::intern(&func.def_path),
            location: trust_types::SourceSpan::default(),
            spine: Spine { candidates: seq, body: body_node, rule: RelevanceRule::BlockDefs },
            contract_metadata: None,
            obligation: Some(RecordRef {
                body: body_node,
                wrappers: vec![WrapperRef::SpineKept],
                subject: None,
                width: None,
            }),
        })
        .expect("a spine of this context");
    let materialized = context.materialize(row).expect("a row of this context");
    assert_eq!(materialized.vc().formula, combined, "{} over {candidates:?}", func.def_path);
    let wrappers = &materialized.vc().obligation.as_ref().expect("a record").wrappers;
    if kept.is_empty() {
        assert!(wrappers.is_empty());
    } else {
        assert_eq!(wrappers, &vec![ObligationWrapper::ConjoinFactsLast { facts: kept.clone() }]);
    }
    !kept.is_empty() && kept.len() < candidates.len()
}

#[test]
fn a_spine_is_the_block_def_combination_on_the_fixtures() {
    let (mut spines, mut filtered) = (0usize, 0usize);
    for (func, vcs) in fixture_functions() {
        let func = func.clone();
        // Every fact any row of the function recorded, in row order: a block's real
        // candidates are among them, and the others are candidates the rule must drop.
        let pool: Vec<Formula> = vcs
            .iter()
            .filter_map(|vc| vc.obligation.as_ref())
            .flat_map(|record| record.wrappers.iter())
            .filter_map(|wrapper| match wrapper {
                ObligationWrapper::ConjoinFactsLast { facts } => Some(facts.iter().cloned()),
                ObligationWrapper::PathGuardOr { .. } => None,
            })
            .flatten()
            .take(64)
            .collect();
        for vc in vcs.iter().take(16) {
            let body = vc.obligation.as_ref().map_or(&vc.formula, |record| &record.body);
            filtered += usize::from(assert_spine_is_the_eager_combination(&func, &pool, body));
            assert_spine_is_the_eager_combination(&func, &[], body);
            spines += 1;
        }
    }
    // Measured 2026-10-11 over the 400-fixture sample: 900 spines, 602 of them keeping
    // some candidates and dropping others. The floors keep the test from passing vacuously.
    assert!(spines > 500, "only {spines} spines");
    assert!(filtered > 300, "only {filtered} spines kept some candidates and dropped others");
}

#[test]
fn context_counters_over_a_family_account_for_every_row() {
    let func = super::version_ssa_families::locals_chain(16);
    let vcs = super::legacy_version_oracle::without_differential(|| crate::generate_vcs(&func));
    let mut context = VcContext::new();
    let ids: Vec<_> = vcs.iter().map(|vc| context.push_node_row(vc).unwrap()).collect();
    for (id, vc) in ids.iter().zip(&vcs) {
        let materialized = context.materialize(*id).expect("a row of this context");
        assert_eq!(materialized.vc().formula, vc.formula);
        assert_eq!(materialized.vc().obligation, vc.obligation);
        assert_eq!(
            context.row_node_count(*id).ok(),
            Some(trust_types::determinism::query_size(&[&vc.formula]))
        );
    }
    let stats = context.stats();
    assert_eq!(stats.rows, vcs.len() as u64);
    assert_eq!(stats.materialization.rows, vcs.len() as u64);
    assert_eq!((stats.trees_alive, stats.trees_alive_max), (0, 1));
    let union: Vec<&Formula> = vcs.iter().map(|vc| &vc.formula).collect();
    assert!(stats.dag_nodes >= trust_types::determinism::query_size(&union));
}

/// T3 C08: a generation into a context over the fixture sample. Its rows are the rows
/// `generate_vcs` returned, the row oracle saw no disagreement, the Spine rows the counts
/// name are the context's, and each Spine row's node count and digest are its materialized
/// formula's. The block-def rows' Spine share and each decline are printed (`SPINES`).
#[test]
fn the_fixtures_block_def_rows_join_as_spines_that_read_back_as_their_rows() {
    let mut total = crate::RecipeCounts::default();
    let (mut functions, mut spine_rows) = (0usize, 0u64);
    for (func, vcs) in fixture_functions() {
        let mut context = VcContext::new();
        let generated =
            catch_unwind(AssertUnwindSafe(|| crate::generate_vcs_rows(func, &mut context)));
        let Ok(rows) = generated else { continue };
        functions += 1;
        assert_eq!(rows.len(), vcs.len(), "{}", func.def_path);
        for (row, vc) in rows.iter().zip(vcs) {
            assert!(same_row(row, vc), "{}: a context changed a row", func.def_path);
        }
        assert_eq!(context.parity(Oracle::Row).mismatches, 0, "{}", func.def_path);
        let ids: Vec<RowId> = context.row_ids().collect();
        for id in ids {
            if !matches!(context.row(id).map(VcRow::formula), Ok(RowFormula::Spine(_))) {
                continue;
            }
            spine_rows += 1;
            let materialized = context.materialize(id).expect("a row of this context");
            let formula = materialized.vc().formula.clone();
            drop(materialized);
            assert_eq!(
                context.row_node_count(id).ok(),
                Some(query_size(&[&formula])),
                "{}: a Spine row's node count (I4)",
                func.def_path
            );
            assert_eq!(
                context.digest(id).ok(),
                formula_digest(&formula).ok(),
                "{}: a Spine row's digest (I5)",
                func.def_path
            );
        }
        total.absorb(&crate::recipe_counts(&context));
    }
    let declines: Vec<String> = crate::SpineDecline::ALL
        .iter()
        .map(|reason| format!("{}={}", reason.name(), total.declined(*reason)))
        .collect();
    println!(
        "SPINES fixtures={functions} recorded={} block_def_rows={} spine_rows={} {}",
        total.recorded,
        total.block_def_rows,
        total.spine_rows,
        declines.join(" ")
    );
    assert_eq!(spine_rows, total.spine_rows, "the Spine rows counted are the context's");
    // The floors are the counts the L4 merge's build printed over the 400 fixtures (2026-10-22):
    // a fixture that stops joining as a block-def combination or a Spine lowers them.
    assert!(total.block_def_rows >= 32, "block-def rows fell below the measured 32");
    assert!(total.spine_rows >= 21, "Spine rows fell below the measured 21");
}

/// T3 C08 (L4-METER-1, L4-C08s-3): the Spine attempts charge no work meter. The sink
/// normalizes each recipe's candidates and lists their relevance names inside the
/// generation's meter scope, so over the first fixtures a generation into a context that
/// joins its block-def rows as Spines must leave the meter where one that joins none
/// leaves it.
#[test]
fn the_spine_attempts_charge_no_work_meter() {
    let metered = |func: &VerifiableFunction, spines: Spines| {
        let none = FxHashSet::default();
        let frame = crate::VcgenContext::for_function_inheriting_regeneration_facts(&func.def_path);
        let mut rows = VcContext::new();
        let _meter = crate::gen_work_scope();
        crate::with_function_vcgen_context(&func.def_path, &frame, || {
            generate_vcs_impl_with_origins(
                func,
                None,
                false,
                &none,
                KeepOrigins::No,
                Some(&mut rows),
                spines,
            )
        });
        (crate::gen_work_used(), crate::recipe_counts(&rows).spine_rows)
    };
    let (mut functions, mut spine_rows) = (0usize, 0u64);
    for (func, _) in fixture_functions().iter().take(METER_SAMPLE) {
        let Ok((joined, spines)) = catch_unwind(AssertUnwindSafe(|| metered(func, Spines::Join)))
        else {
            continue;
        };
        let Ok((skipped, none)) = catch_unwind(AssertUnwindSafe(|| metered(func, Spines::Skip)))
        else {
            continue;
        };
        assert_eq!(none, 0, "{}: a generation that skips Spines joined one", func.def_path);
        assert_eq!(joined, skipped, "{}: the Spine attempts charged the work meter", func.def_path);
        functions += 1;
        spine_rows += spines;
    }
    println!("SPINE-METER fixtures={functions} spine_rows={spine_rows}");
    assert!(functions > 0, "no fixture generated");
}
