//! T3 L4 (C08): block-def recipes (`super::recipes`), their keys, and the rows the row
//! sink joins as Spine rows.
//!
//! * a shape key sees through SSA version tokens and through nothing else, and a recipe
//!   is recorded only while a generation that writes into a context runs, each nested
//!   generation into its own log;
//! * a block-def row joins as a Spine row that reads back as the row, its record naming
//!   the spine's kept facts, and its root never interned; one that keeps nothing is a
//!   Spine over its body; rows over one candidate list share its sequence; and rows whose
//!   candidates extend one another share one list in the log and one chain of sequence
//!   cells in the context;
//! * a row a pass rewrote (term `Ite`), a row a wrapper rewrote, and a row over a name the
//!   context lists as another stay Node, each counted, and no context changes a row; a row
//!   whose fact is no normalized candidate is a normalization decline, not a closure one.
//!
//! The rows are built over names without version tokens, so normalization and the
//! relevance collapse are the identity on them; the fixtures' and the families' real rows
//! are in `vc_context_spine_tests` and `version_ssa_scaling_tests`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::vc_context::{
    Oracle, ParityCount, RowFormula, RowId, Spine, VcContext, VcRow, WrapperRef, same_row,
};

use super::recipes::{self, RecipeScope, SpineDecline};
use super::*;

fn var(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}

fn row(line: u32, formula: Formula, obligation: Option<ObligationRecord>) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: Symbol::intern("recipes::f"),
        location: SourceSpan {
            file: "recipes.rs".into(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 9,
        },
        formula,
        contract_metadata: None,
        obligation,
    }
}

/// A block-def row as the builders make one: `body` combined with `defs`, recorded as a
/// recipe while a log is open, with its record.
fn block_def_row(
    func: &VerifiableFunction,
    line: u32,
    defs: Vec<Formula>,
    body: Formula,
) -> VerificationCondition {
    let (formula, kept) = combine_block_defs_as_recipe(func, defs, body.clone());
    let wrappers = if kept.is_empty() {
        Vec::new()
    } else {
        vec![ObligationWrapper::ConjoinFactsLast { facts: kept }]
    };
    row(line, formula, Some(ObligationRecord { body, wrappers, subject: None, width: None }))
}

/// The rows `make` builds, joined through one sink that writes into `context`, as one
/// generation does: inside a recording recipe log.
fn into_context(
    func: &VerifiableFunction,
    context: &mut VcContext,
    make: impl FnOnce() -> Vec<VerificationCondition>,
) -> SinkOutput {
    let _scope = RecipeScope::open(true);
    let rows = make();
    let mut sink = RowSink::new(func, Some(context));
    sink.lane(rows);
    sink.sort_by_location();
    sink.finish()
}

/// The same rows through a sink with no context.
fn bare(
    func: &VerifiableFunction,
    make: impl FnOnce() -> Vec<VerificationCondition>,
) -> Vec<VerificationCondition> {
    let _scope = RecipeScope::open(false);
    let rows = make();
    let mut sink = RowSink::new(func, None);
    sink.lane(rows);
    sink.sort_by_location();
    sink.finish().vcs
}

/// The spine row `id` is, or a panic.
fn spine_of(context: &VcContext, id: Option<RowId>) -> Spine {
    let id = id.expect("a row of an unfull context has an id");
    match context.row(id).map(VcRow::formula) {
        Ok(RowFormula::Spine(spine)) => *context.spine(spine).expect("a spine of this context"),
        other => panic!("not a Spine row: {other:?}"),
    }
}

fn chain_defs() -> Vec<Formula> {
    vec![
        eq(var("z"), Formula::Int(1)),
        eq(var("y"), var("z")),
        eq(var("w"), Formula::Int(5)),
        eq(var("x"), var("y")),
    ]
}

#[test]
fn late_body_facts_reuse_only_the_recorded_candidates_and_keep_every_occurrence() {
    let func = super::version_ssa_families::locals_chain(2);
    let bound = lt(Formula::Int(-1), var("x"));
    let make = || {
        let mut vc = block_def_row(&func, 1, chain_defs(), lt(var("x"), Formula::Int(0)));
        // This producer constructs its obligation record only after the late
        // facts. Do not leave the synthetic helper's earlier record attached.
        vc.obligation = None;
        let original = vc.formula.clone();
        vc.formula =
            recipes::conjoin_body_facts(original.clone(), vec![bound.clone(), bound.clone()]);
        let Formula::And(original) = original else { panic!("block-def prefix") };
        let Formula::And(combined) = &vc.formula else { panic!("same conjunction prefix") };
        assert_eq!(&combined[..combined.len() - 1], &original[..original.len() - 1]);
        assert_eq!(
            combined.last(),
            Some(&Formula::And(vec![
                bound.clone(),
                bound.clone(),
                original.last().unwrap().clone()
            ])),
            "neither repeated carrier occurrence can be dropped"
        );
        vec![vc]
    };
    let mut context = VcContext::new();
    let output = into_context(&func, &mut context, make);
    let eager = bare(&func, make);
    assert!(same_row(&output.vcs[0], &eager[0]), "layout must not depend on recording");
    let spine = spine_of(&context, output.ids[0]);
    assert_eq!(context.seq_nodes(spine.candidates).unwrap().len(), chain_defs().len());
    assert_eq!(context.kept(&spine).unwrap().len(), 3, "the original block-def closure");
    let counts = recipes::recipe_counts(&context);
    assert_eq!((counts.recorded, counts.block_def_rows, counts.spine_rows), (1, 1, 1));
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 1, mismatches: 0 });
}

#[test]
fn a_late_wrapper_cannot_lend_its_recipe_to_a_changed_prefix_or_body() {
    let func = super::version_ssa_families::locals_chain(2);
    let mut context = VcContext::new();
    let output = into_context(&func, &mut context, || {
        let mut vc = block_def_row(&func, 1, chain_defs(), lt(var("x"), Formula::Int(0)));
        vc.obligation = None;
        vc.formula = recipes::conjoin_body_facts(vc.formula, vec![lt(Formula::Int(-1), var("x"))]);
        let mut moved_prefix = vc.clone();
        moved_prefix.location.line_start = 2;
        let Formula::And(parts) = &mut moved_prefix.formula else { panic!("a conjunction") };
        let last = parts.len() - 1;
        parts.swap(0, last);
        let mut changed_body = vc.clone();
        changed_body.location.line_start = 3;
        let Formula::And(parts) = &mut changed_body.formula else { panic!("a conjunction") };
        *parts.last_mut().unwrap() = Formula::Bool(false);
        vec![vc, moved_prefix, changed_body]
    });
    spine_of(&context, output.ids[0]);
    for id in &output.ids[1..] {
        assert!(matches!(context.row(id.unwrap()).map(VcRow::formula), Ok(RowFormula::Node(_))));
    }
    let counts = recipes::recipe_counts(&context);
    assert_eq!((counts.recorded, counts.block_def_rows, counts.spine_rows), (1, 1, 1));
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 3, mismatches: 0 });
}

#[test]
fn the_actual_byvalue_field_postcondition_keeps_its_carriers_and_spine() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("../../tests/data/byvalue_param_field_write/ok.json"))
            .unwrap();
    let eager = crate::generate_vcs(&func);
    let mut context = VcContext::new();
    let rows = crate::generate_vcs_rows(&func, &mut context);
    assert_eq!((eager.len(), rows.len()), (1, 1));
    assert!(same_row(&rows[0], &eager[0]));
    let ids: Vec<_> = context.row_ids().collect();
    assert_eq!(ids.len(), 1, "no unreturned rows can satisfy the representation floor");
    let spine = spine_of(&context, Some(ids[0]));
    assert_eq!(context.seq_nodes(spine.candidates).unwrap().len(), 1);
    assert_eq!(context.kept(&spine).unwrap().len(), 1);
    assert_eq!(context.row_node_count(ids[0]).unwrap(), 11, "all carrier bounds remain");
    let counts = recipes::recipe_counts(&context);
    assert_eq!((counts.recorded, counts.block_def_rows, counts.spine_rows), (1, 1, 1));
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 1, mismatches: 0 });
}

#[test]
fn a_shape_key_sees_through_version_tokens_and_nothing_else() {
    let versioned =
        Formula::And(vec![eq(var("x#s1_0"), var("y")), lt(var("x#s1_0"), Formula::Int(0))]);
    let plain = Formula::And(vec![eq(var("x"), var("y")), lt(var("x"), Formula::Int(0))]);
    assert_eq!(recipes::shape_hash(&versioned), recipes::shape_hash(&plain));
    assert_eq!(recipes::shape_key(&versioned, 1), recipes::shape_key(&plain, 1));
    let others = [
        Formula::And(vec![eq(var("w"), var("y")), lt(var("x"), Formula::Int(0))]),
        Formula::And(vec![eq(var("x"), var("y")), lt(var("x"), Formula::Int(1))]),
        Formula::And(vec![lt(var("x"), Formula::Int(0)), eq(var("x"), var("y"))]),
        Formula::And(vec![
            eq(var("x"), var("y")),
            Formula::Le(Box::new(var("x")), Box::new(Formula::Int(0))),
        ]),
    ];
    for other in &others {
        assert_ne!(recipes::shape_hash(other), recipes::shape_hash(&plain), "{other:?}");
    }
    // A key says how many facts the combination keeps, and a formula that cannot keep
    // that many has none.
    assert_ne!(recipes::shape_key(&plain, 0), recipes::shape_key(&plain, 1));
    assert_eq!(recipes::shape_key(&plain, 2), None);
}

#[test]
fn recipes_are_recorded_only_while_a_recording_generation_runs() {
    let combined =
        Formula::And(vec![eq(var("x#s1_0"), var("y")), lt(var("x#s1_0"), Formula::Int(0))]);
    let normalized = Formula::And(vec![eq(var("x"), var("y")), lt(var("x"), Formula::Int(0))]);
    let candidates = vec![eq(var("w"), Formula::Int(5)), eq(var("x#s1_0"), var("y"))];
    assert!(!recipes::recording());
    recipes::record(candidates.clone(), 1, &combined);
    assert!(recipes::recipes_for(&combined).is_empty(), "no log is open");
    {
        let _outer = RecipeScope::open(true);
        assert!(recipes::recording());
        recipes::record(candidates.clone(), 1, &combined);
        recipes::record(candidates.clone(), 1, &combined);
        assert_eq!(recipes::recorded(), 2);
        assert_eq!(
            recipes::recipes_for(&normalized).len(),
            1,
            "found under normalization, and the second shares the first's candidates"
        );
        {
            let _inner = RecipeScope::open(false);
            assert!(!recipes::recording());
            assert!(recipes::recipes_for(&normalized).is_empty(), "a nested generation's own");
        }
        assert_eq!(recipes::recipes_for(&normalized).len(), 1, "the outer log is restored");
    }
    assert!(!recipes::recording());
}

#[test]
fn a_block_def_row_joins_as_a_spine_that_reads_back_as_the_row() {
    let func = super::version_ssa_families::locals_chain(2);
    let body = || lt(var("x"), Formula::Int(0));
    let make = || vec![block_def_row(&func, 1, chain_defs(), body())];
    let mut context = VcContext::new();
    let output = into_context(&func, &mut context, make);
    let [vc] = output.vcs.as_slice() else { panic!("one row") };
    let unchanged = bare(&func, make);
    assert!(unchanged.len() == 1 && same_row(vc, &unchanged[0]), "a context changed a row");
    let spine = spine_of(&context, output.ids[0]);
    assert_eq!(context.kept(&spine).map(|kept| kept.len()).ok(), Some(3), "w is not kept");
    let id = output.ids[0].expect("an id");
    {
        let read_back = context.materialize(id).expect("a row of this context");
        assert!(same_row(read_back.vc(), vc));
    }
    let wrappers = context.row(id).ok().and_then(VcRow::obligation).map(|r| r.wrappers.clone());
    assert_eq!(wrappers, Some(vec![WrapperRef::SpineKept]), "the record names the kept facts");
    let counts = recipes::recipe_counts(&context);
    assert_eq!((counts.recorded, counts.block_def_rows, counts.spine_rows), (1, 1, 1));
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 1, mismatches: 0 });
    let stats = context.stats();
    assert_eq!((stats.rows, stats.spines, stats.sum_cone_blocks, stats.cone_rows), (1, 1, 1, 1));
    // The spine's root is never interned: interning the row's formula adds it, and only it.
    let nodes = stats.dag_nodes;
    context.intern(&vc.formula);
    assert_eq!(context.stats().dag_nodes, nodes + 1);
}

#[test]
fn a_block_def_row_that_keeps_nothing_is_a_spine_over_its_body() {
    let func = super::version_ssa_families::locals_chain(2);
    let body = lt(var("x"), Formula::Int(0));
    let mut context = VcContext::new();
    let output = into_context(&func, &mut context, || {
        vec![block_def_row(&func, 1, vec![eq(var("w"), Formula::Int(5))], body.clone())]
    });
    assert_eq!(output.vcs[0].formula, body, "the eager rule kept nothing");
    let spine = spine_of(&context, output.ids[0]);
    assert_eq!(context.kept(&spine).ok(), Some(Vec::new()));
    let id = output.ids[0].expect("an id");
    let wrappers = context.row(id).ok().and_then(VcRow::obligation).map(|r| r.wrappers.clone());
    assert_eq!(wrappers, Some(Vec::new()), "an empty kept list records no wrapper");
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 1, mismatches: 0 });
}

#[test]
fn rows_over_one_candidate_list_share_its_sequence() {
    let func = super::version_ssa_families::locals_chain(2);
    let mut context = VcContext::new();
    let output = into_context(&func, &mut context, || {
        vec![
            block_def_row(&func, 1, chain_defs(), lt(var("x"), Formula::Int(0))),
            block_def_row(&func, 2, chain_defs(), lt(var("y"), Formula::Int(7))),
        ]
    });
    let (first, second) = (spine_of(&context, output.ids[0]), spine_of(&context, output.ids[1]));
    assert_eq!(first.candidates, second.candidates, "one sequence for the block's candidates");
    assert_ne!(first.body, second.body);
    let counts = recipes::recipe_counts(&context);
    assert_eq!((counts.block_def_rows, counts.spine_rows), (2, 2));
    assert_eq!(context.stats().spines, 2);
}

#[test]
fn rows_a_pass_or_a_wrapper_rewrote_and_rows_over_a_relisted_name_stay_node() {
    let func = super::version_ssa_families::locals_chain(2);
    let make = || {
        // A term `Ite` in the body, which the sink's second pass eliminates.
        let choice = Formula::Ite(
            Box::new(Formula::Var("c".into(), Sort::Bool)),
            Box::new(var("x")),
            Box::new(var("y")),
        );
        let ite =
            block_def_row(&func, 1, vec![eq(var("x"), var("y"))], lt(choice, Formula::Int(0)));
        // A combination a later step conjoined a fact around: no recipe is its.
        let mut wrapped =
            block_def_row(&func, 2, vec![eq(var("x"), var("y"))], lt(var("x"), Formula::Int(0)));
        wrapped.formula = Formula::And(vec![eq(var("g"), Formula::Int(1)), wrapped.formula]);
        // A combination over `q`, which the context already compares as another name.
        let relisted =
            block_def_row(&func, 3, vec![eq(var("q"), var("y"))], lt(var("q"), Formula::Int(0)));
        vec![ite, wrapped, relisted]
    };
    let mut context = VcContext::new();
    context.vars_mut().insert("q", "elsewhere");
    let output = into_context(&func, &mut context, make);
    let unchanged = bare(&func, make);
    assert_eq!(output.vcs.len(), unchanged.len());
    for (vc, eager) in output.vcs.iter().zip(&unchanged) {
        assert!(same_row(vc, eager), "a context changed a row");
    }
    for id in &output.ids {
        let id = id.expect("an id");
        assert!(matches!(context.row(id).map(VcRow::formula), Ok(RowFormula::Node(_))));
    }
    let counts = recipes::recipe_counts(&context);
    assert_eq!((counts.recorded, counts.block_def_rows, counts.spine_rows), (3, 2, 0));
    assert_eq!(counts.declined(SpineDecline::Ite), 1);
    assert_eq!(counts.declined(SpineDecline::Relevance), 1);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 3, mismatches: 0 });
    assert_eq!(context.stats().cone_rows, 0);
}

/// A block's rows at later points, whose candidates extend the earlier rows' statement by
/// statement, share one candidate list: the log holds the block's candidates once, not once
/// per row (L4-C08-2), each row still finds its own recipe and joins as a Spine, and the
/// rows' candidate sequences are one chain of cells.
#[test]
fn extending_candidate_lists_are_held_once() {
    let func = super::version_ssa_families::locals_chain(2);
    let defs = chain_defs();
    // Row k reads the subject of the k-th def, over the block's first k defs.
    let subjects = ["z", "y", "w", "x"];
    let mut held = 0;
    let mut context = VcContext::new();
    let output = into_context(&func, &mut context, || {
        let rows: Vec<VerificationCondition> = subjects
            .iter()
            .enumerate()
            .map(|(k, subject)| {
                let line = u32::try_from(k + 1).expect("a small line");
                block_def_row(&func, line, defs[..=k].to_vec(), lt(var(subject), Formula::Int(0)))
            })
            .collect();
        held = recipes::held_facts();
        rows
    });
    assert_eq!(held, defs.len(), "the log holds one list of the block's candidates");
    let counts = recipes::recipe_counts(&context);
    assert_eq!((counts.recorded, counts.block_def_rows, counts.spine_rows), (4, 4, 4));
    let sequences: Vec<Vec<_>> = output
        .ids
        .iter()
        .map(|id| {
            let spine = spine_of(&context, *id);
            context.seq_nodes(spine.candidates).expect("a sequence of this context")
        })
        .collect();
    for (k, pair) in sequences.windows(2).enumerate() {
        let [shorter, longer] = pair else { continue };
        assert_eq!(longer.len(), k + 2);
        assert!(longer.starts_with(shorter), "row {k}'s candidates are a prefix of the next row's");
    }
    assert_eq!(context.stats().seq_cells, defs.len() as u64, "one chain of sequence cells");
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 4, mismatches: 0 });
}

/// A block-def row whose conjoined fact is no normalized candidate (spelled at another
/// version than its candidate, over a name the function cannot collapse) is declined as a
/// normalization that is not a renaming, not as a closure mismatch, and stays Node.
#[test]
fn a_row_whose_fact_is_no_normalized_candidate_is_a_normalization_decline() {
    let func = super::version_ssa_families::locals_chain(2);
    let candidate = eq(var("zz#s1_0"), var("y"));
    let fact = eq(var("zz#s9_9"), var("y"));
    let body = lt(var("zz#s9_9"), Formula::Int(0));
    let make = || {
        // The recipe the builders would have recorded for the candidate's own spelling.
        let recorded = Formula::And(vec![candidate.clone(), lt(var("zz#s1_0"), Formula::Int(0))]);
        recipes::record(vec![candidate.clone()], 1, &recorded);
        let wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: vec![fact.clone()] }];
        let record = ObligationRecord { body: body.clone(), wrappers, subject: None, width: None };
        vec![row(1, Formula::And(vec![fact.clone(), body.clone()]), Some(record))]
    };
    let mut context = VcContext::new();
    let output = into_context(&func, &mut context, make);
    let id = output.ids[0].expect("an id");
    assert!(matches!(context.row(id).map(VcRow::formula), Ok(RowFormula::Node(_))));
    let counts = recipes::recipe_counts(&context);
    assert_eq!((counts.block_def_rows, counts.spine_rows), (1, 0));
    assert_eq!(counts.declined(SpineDecline::Normalization), 1);
    assert_eq!(counts.declined(SpineDecline::Closure), 0);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 1, mismatches: 0 });
}

#[test]
fn fast_shape_hash_and_record_slice_match_iterative_and_owned_oracles() {
    // Wide (> 16 children) + deep (> 64 depth) AST parity between `shape_hash` and `shape_hash_iterative`.
    let mut deep = var("leaf#s0_1");
    for k in 0..80 {
        deep = Formula::Add(Box::new(deep), Box::new(Formula::Int(k)));
    }
    let wide = Formula::And(
        (0..24)
            .map(|i| eq(var(&format!("v{i}#s1_0")), Formula::Int(i)))
            .chain([deep.clone()])
            .collect(),
    );
    for probe in [&deep, &wide, &Formula::And(Vec::new()), &Formula::Bool(true)] {
        assert_eq!(
            recipes::shape_hash(probe),
            recipes::shape_hash_iterative(probe),
            "shape_hash vs shape_hash_iterative mismatch"
        );
    }

    // `record_slice` shares prefix candidates without duplicating list storage.
    let defs = chain_defs();
    let _scope = RecipeScope::open(true);
    let c1 = Formula::And(vec![defs[0].clone(), lt(var("z"), Formula::Int(0))]);
    let c2 = Formula::And(vec![defs[0].clone(), defs[1].clone(), lt(var("y"), Formula::Int(0))]);
    recipes::record_slice(&defs[..2], 1, &c1);
    recipes::record_slice(&defs[..2], 1, &c1);
    recipes::record_slice(&defs, 2, &c2);
    assert_eq!(recipes::recorded(), 3);
    assert_eq!(recipes::held_facts(), defs.len(), "record_slice must share one CandidateList");
    assert_eq!(recipes::recipes_for(&c1).len(), 1);
    assert_eq!(recipes::recipes_for(&c2).len(), 1);
}
