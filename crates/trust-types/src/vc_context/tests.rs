// Tests for crate::vc_context (T3 L4, C06): every field round-trips (I1), spines
// materialize, identify, digest (I5) and count (I4) as their trees do, the identity cases
// of L4-SPINE-ID-1 and ROW-IDENTITY-1, and the ownership rules.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::*;
use crate::determinism::query_size;
use crate::formula_merkle::formula_digest;
use crate::{
    BinOp, ContractMetadata, Formula, ObligationRecord, ObligationWrapper, PathGuardTerm, Sort,
    SourceSpan, StateMachineMetadata, Symbol, Ty, VcKind, VerificationCondition,
};

fn var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}

fn span(line: u32) -> SourceSpan {
    SourceSpan {
        file: "t.rs".to_string(),
        line_start: line,
        col_start: 1,
        line_end: line,
        col_end: 9,
    }
}

fn vc(kind: VcKind, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: Symbol::intern("demo::f"),
        location: span(1),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// Every field of `a` and `b` is equal, and so is their canonical JSON.
fn assert_same_vc(a: &VerificationCondition, b: &VerificationCondition) {
    assert_eq!(a.kind, b.kind);
    assert_eq!(a.function, b.function);
    assert_eq!(a.location, b.location);
    assert_eq!(a.formula, b.formula);
    assert_eq!(a.contract_metadata, b.contract_metadata);
    assert_eq!(a.obligation, b.obligation);
    assert_eq!(
        crate::canonical_digest_json_value(a).ok(),
        crate::canonical_digest_json_value(b).ok()
    );
}

/// Rows covering every VerificationCondition field: 128-bit literals, a temporal kind
/// with a label map, a constant array, quantifiers, both wrapper kinds, contract metadata,
/// a subject and a width.
fn varied_rows() -> Vec<VerificationCondition> {
    let wide = Formula::And(vec![
        eq(var("a"), Formula::Int(i128::MAX)),
        eq(var("b"), Formula::Int(i128::MIN)),
        eq(var("c"), Formula::UInt(u128::MAX)),
    ]);
    let temporal = VcKind::Temporal {
        property: "AG(request -> AF response)".to_string(),
        machine: Some(StateMachineMetadata {
            states: vec!["idle".to_string(), "pending".to_string()],
            init_states: vec![0],
            transitions: vec![(0, "request".to_string(), 1), (1, "response".to_string(), 0)],
            labels: [(0, vec!["idle".to_string()]), (1, vec!["pending".to_string()])]
                .into_iter()
                .collect(),
        }),
    };
    let array = Formula::const_array(Sort::Int, Sort::Int, Formula::Int(7));
    let quantified = Formula::Forall(
        vec![(Symbol::intern("i"), Sort::Int)],
        Box::new(Formula::Exists(
            vec![(Symbol::intern("j"), Sort::Int)],
            Box::new(lt(var("i"), var("j"))),
        )),
    );
    let body = lt(var("x"), Formula::Int(0));
    let fact = eq(var("x"), var("y"));
    let guard = lt(var("y"), Formula::Int(3));
    let wrapped = ObligationRecord {
        body: body.clone(),
        wrappers: vec![
            ObligationWrapper::ConjoinFactsLast { facts: vec![fact.clone()] },
            ObligationWrapper::PathGuardOr {
                paths: vec![PathGuardTerm::Raw, PathGuardTerm::Guarded { guards: vec![guard] }],
            },
        ],
        subject: Some(var("x")),
        width: Some(32),
    };
    let mut recorded = vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        wrapped.reconstruct().unwrap_or(body.clone()),
    );
    recorded.obligation = Some(wrapped);
    recorded.contract_metadata = Some(ContractMetadata::default());
    vec![
        vc(VcKind::Assertion { message: "wide".to_string() }, wide),
        vc(temporal, Formula::Bool(true)),
        vc(VcKind::Assertion { message: "array".to_string() }, eq(var("arr"), array)),
        vc(VcKind::Assertion { message: "quantified".to_string() }, quantified),
        recorded,
    ]
}

#[test]
fn every_field_round_trips() {
    let rows = varied_rows();
    let mut context = VcContext::new();
    let ids: Vec<RowId> = rows.iter().map(|row| context.push_node_row(row).unwrap()).collect();
    for (id, row) in ids.iter().zip(&rows) {
        let materialized = context.materialize(*id).expect("a row of this context");
        assert_same_vc(materialized.vc(), row);
    }
    // A row of another context is refused, never read.
    let other = VcContext::new().push_node_row(&rows[0]).unwrap();
    assert!(matches!(context.materialize(other), Err(VcContextError::UnknownRow(_))));
}

/// A context whose relevance names collapse `x#1` and `x#2` onto `x`.
fn relevance_context() -> VcContext {
    let mut context = VcContext::new();
    context.vars_mut().insert("x#1", "x");
    context.vars_mut().insert("x#2", "x");
    context
}

/// The eager rule (trust-vcgen's `combine_relevant_block_defs_recorded`), over trees and
/// the same relevance names, as the reference the spine must reproduce.
fn eager_combine(context: &VcContext, defs: &[Formula], body: &Formula) -> (Formula, Vec<Formula>) {
    let names = |f: &Formula| -> std::collections::BTreeSet<String> {
        let mut scratch = VcContext::new();
        let node = scratch.intern(f);
        scratch
            .formula_var_names(node)
            .unwrap_or_default()
            .into_iter()
            .map(|name| context.vars().relevance(&name).to_string())
            .collect()
    };
    if defs.is_empty() {
        return (body.clone(), Vec::new());
    }
    let mut needed = names(body);
    let mut keep_rev = Vec::new();
    for def in defs.iter().rev() {
        let def_names = names(def);
        if def_names.iter().any(|name| needed.contains(name)) {
            needed.extend(def_names);
            keep_rev.push(def.clone());
        }
    }
    if keep_rev.is_empty() {
        return (body.clone(), Vec::new());
    }
    let kept: Vec<Formula> = keep_rev.into_iter().rev().collect();
    let mut conjuncts = kept.clone();
    conjuncts.push(body.clone());
    (Formula::And(conjuncts), kept)
}

fn spine_row(context: &mut VcContext, defs: &[Formula], body: &Formula, record: bool) -> RowId {
    let nodes: Vec<_> = defs.iter().map(|def| context.intern(def)).collect();
    let candidates = context.seq(&nodes).expect("nodes of this context");
    let body_node = context.intern(body);
    let obligation = record.then(|| RecordRef {
        body: body_node,
        wrappers: vec![WrapperRef::SpineKept],
        subject: None,
        width: None,
    });
    context
        .push_spine_row(SpineRow {
            kind: VcKind::DivisionByZero,
            function: Symbol::intern("demo::f"),
            location: span(4),
            spine: Spine { candidates, body: body_node, rule: RelevanceRule::BlockDefs },
            contract_metadata: None,
            obligation,
        })
        .expect("a spine of this context")
}

#[test]
fn a_spine_materializes_as_the_eager_combination_in_kept_order() {
    let body = lt(var("x#2"), Formula::Int(0));
    let cases: Vec<Vec<Formula>> = vec![
        // The chain x#1 <- y <- z is kept in order; w is not.
        vec![
            eq(var("z"), Formula::Int(1)),
            eq(var("y"), var("z")),
            eq(var("w"), Formula::Int(5)),
            eq(var("x#1"), var("y")),
        ],
        // Nothing relevant: the empty kept list, the formula is the body.
        vec![eq(var("w"), Formula::Int(5))],
        // No candidates at all.
        vec![],
        // A bound name does not make a fact relevant; an opaque node hides its names.
        vec![
            Formula::Forall(
                vec![(Symbol::intern("x"), Sort::Int)],
                Box::new(eq(var("x"), var("q"))),
            ),
            Formula::Pred(Symbol::intern("dir_open"), vec![var("x")]),
            eq(var("x"), var("p")),
        ],
        // A duplicate fact is kept twice, as the eager rule keeps it.
        vec![eq(var("x#1"), var("y")), eq(var("x#1"), var("y"))],
    ];
    for defs in cases {
        let mut context = relevance_context();
        let row = spine_row(&mut context, &defs, &body, true);
        let (eager, kept) = eager_combine(&context, &defs, &body);
        let materialized = context.materialize(row).expect("a row of this context");
        assert_eq!(materialized.vc().formula, eager, "defs {defs:?}");
        let record = materialized.vc().obligation.as_ref().expect("a record");
        if kept.is_empty() {
            assert!(record.wrappers.is_empty(), "an empty kept list records no wrapper");
        } else {
            assert_eq!(record.wrappers, vec![ObligationWrapper::ConjoinFactsLast { facts: kept }]);
        }
        assert_eq!(record.reconstruct(), Some(eager.clone()));
    }
}

#[test]
fn formula_identity_cases() {
    let mut context = relevance_context();
    let body = lt(var("x#2"), Formula::Int(0));
    let def = eq(var("x#1"), var("y"));
    let noise = eq(var("w"), Formula::Int(5));
    let spine = spine_row(&mut context, &[def.clone()], &body, false);
    // A spine equals an `And` Node row with the same children.
    let and_row = context
        .push_node_row(&vc(VcKind::DivisionByZero, Formula::And(vec![def.clone(), body.clone()])))
        .unwrap();
    assert!(context.formula_eq(spine, and_row));
    assert!(context.formula_eq(and_row, spine));
    // Two spines with different candidates and the same kept list are equal.
    let other = spine_row(&mut context, &[noise.clone(), def.clone()], &body, false);
    assert_ne!(
        context.row(spine).map(VcRow::formula).ok(),
        context.row(other).map(VcRow::formula).ok()
    );
    assert!(context.formula_eq(spine, other));
    // A spine that keeps nothing equals its body's Node row (the eager rule).
    let bare = spine_row(&mut context, &[noise.clone()], &body, false);
    let body_row = context.push_node_row(&vc(VcKind::DivisionByZero, body.clone())).unwrap();
    assert!(context.formula_eq(bare, body_row));
    assert!(!context.formula_eq(bare, spine));
    // The same row; and nothing of another context.
    assert!(context.formula_eq(spine, spine));
    let foreign =
        VcContext::new().push_node_row(&vc(VcKind::DivisionByZero, body.clone())).unwrap();
    assert!(!context.formula_eq(foreign, body_row));
}

/// T3 C08: two block-def rows whose spines differ only in an irrelevant candidate are the
/// same row: the same identity and the same canonical JSON once materialized, so the exact
/// dedupe, which keys a row by its canonical JSON until C11, merges them as it merges their
/// eager rows.
#[test]
fn block_def_rows_with_one_formula_and_two_candidate_lists_are_one_row() {
    let mut context = relevance_context();
    let body = lt(var("x#2"), Formula::Int(0));
    let def = eq(var("x#1"), var("y"));
    let noise = eq(var("w"), Formula::Int(5));
    let lean = spine_row(&mut context, std::slice::from_ref(&def), &body, true);
    let noisy = spine_row(&mut context, &[noise, def], &body, true);
    assert_ne!(
        context.row(lean).map(VcRow::formula).ok(),
        context.row(noisy).map(VcRow::formula).ok(),
        "control: two spines"
    );
    let a = context.identity(lean).expect("identity");
    let b = context.identity(noisy).expect("identity");
    assert!(context.same_identity(&a, &b));
    let (a, b) = (context.materialize(lean).unwrap(), context.materialize(noisy).unwrap());
    assert_same_vc(a.vc(), b.vc());
}

/// T3 C08: a supplier reads whether a name is listed before it lists one, so an entry that
/// maps a name to itself is listed, and an unlisted name is its own relevance name.
#[test]
fn a_listed_name_is_told_apart_from_an_unlisted_one() {
    let mut context = relevance_context();
    context.vars_mut().insert("y", "y");
    assert_eq!(context.vars().listed("x#1"), Some("x"));
    assert_eq!(context.vars().listed("y"), Some("y"));
    assert_eq!(context.vars().listed("z"), None);
    assert_eq!(context.vars().relevance("z"), "z");
}

/// T3 C08: `sum_cone_blocks` sums the cones vcgen knows, and `cone_rows` counts them.
#[test]
fn cone_blocks_are_summed_over_the_rows_they_are_known_for() {
    let context = VcContext::new();
    assert_eq!((context.stats().sum_cone_blocks, context.stats().cone_rows), (0, 0));
    context.record_cone_blocks(1);
    context.record_cone_blocks(3);
    assert_eq!((context.stats().sum_cone_blocks, context.stats().cone_rows), (4, 2));
}

#[test]
fn rows_that_differ_only_outside_the_formula_are_different_rows() {
    let mut context = VcContext::new();
    let base = vc(VcKind::DivisionByZero, lt(var("d"), Formula::Int(1)));
    let mut moved = base.clone();
    moved.location = span(2);
    let mut rekinded = base.clone();
    rekinded.kind = VcKind::RemainderByZero;
    let mut with_metadata = base.clone();
    with_metadata.contract_metadata = Some(ContractMetadata::default());
    let mut with_record = base.clone();
    with_record.obligation = Some(ObligationRecord {
        body: base.formula.clone(),
        wrappers: Vec::new(),
        subject: None,
        width: None,
    });
    let base_id = context.push_node_row(&base).unwrap();
    let twin = context.push_node_row(&base.clone()).unwrap();
    let base_identity = context.identity(base_id).expect("identity");
    let twin_identity = context.identity(twin).expect("identity");
    assert!(context.same_identity(&base_identity, &twin_identity));
    for other in [moved, rekinded, with_metadata, with_record] {
        let id = context.push_node_row(&other).unwrap();
        assert!(context.formula_eq(base_id, id), "the formula is the same");
        let identity = context.identity(id).expect("identity");
        assert_eq!(identity.digest, base_identity.digest, "the digest only selects");
        assert!(!context.same_identity(&base_identity, &identity), "{other:?}");
    }
}

/// T3 L4 C09: a VC identified with no row ([`VcContext::identity_of`]) has the identity of
/// the Node row pushed from it, and no row is pushed; a VC that differs only outside the
/// formula is another row (ROW-IDENTITY-1); and an identity is held only by the context it
/// was computed in.
#[test]
fn a_vc_identified_without_a_row_is_the_row_it_would_be() {
    let mut context = VcContext::new();
    let rows = varied_rows();
    let ids: Vec<RowId> = rows.iter().map(|row| context.push_node_row(row).unwrap()).collect();
    let len = context.len();
    for (row, id) in rows.iter().zip(&ids) {
        let pushed = context.identity(*id).expect("identity");
        let free = context.identity_of(row).expect("identity of a VC");
        assert!(context.same_identity(&pushed, &free), "{row:?}");
        assert_eq!(pushed.digest, free.digest);
        assert!(context.holds_identity(&free));
    }
    assert_eq!(context.len(), len, "no row was pushed");
    let base = vc(VcKind::DivisionByZero, lt(var("d"), Formula::Int(1)));
    let mut moved = base.clone();
    moved.location = span(2);
    let a = context.identity_of(&base).unwrap();
    let b = context.identity_of(&moved).unwrap();
    assert!(!context.same_identity(&a, &b), "the span is part of the identity");
    assert_eq!(a.digest, b.digest, "the digest only selects");
    let mut other = VcContext::new();
    let foreign = other.identity_of(&base).unwrap();
    assert!(other.holds_identity(&foreign));
    assert!(!context.holds_identity(&foreign), "an identity of another context");
}

#[test]
fn spine_digests_and_counts_are_the_materialized_trees() {
    let body = lt(var("x#2"), Formula::Int(0));
    let shared = Formula::Add(Box::new(var("y")), Box::new(var("y")));
    let defs = vec![
        eq(var("z"), shared.clone()),
        eq(var("y"), var("z")),
        eq(var("x#1"), Formula::Add(Box::new(var("y")), Box::new(shared))),
        eq(var("w"), Formula::Int(5)),
    ];
    for take in 0..=defs.len() {
        let mut context = relevance_context();
        let row = spine_row(&mut context, &defs[..take], &body, true);
        let tree = context.materialize(row).expect("a row of this context").vc().formula.clone();
        assert_eq!(context.digest(row).ok(), formula_digest(&tree).ok(), "take {take}");
        assert_eq!(context.row_node_count(row).ok(), Some(query_size(&[&tree])), "take {take}");
        // The digest does not depend on what else the context holds or in what order.
        let mut reversed = relevance_context();
        for def in defs.iter().rev() {
            reversed.intern(def);
        }
        let again = spine_row(&mut reversed, &defs[..take], &body, true);
        assert_eq!(context.digest(row).ok(), reversed.digest(again).ok());
    }
    // A spine root is never interned.
    let mut context = relevance_context();
    let before = {
        let row = spine_row(&mut context, &defs, &body, true);
        let nodes = context.dag().len();
        let _ = context.identity(row);
        let _ = context.row_node_count(row);
        let _ = context.materialize(row);
        assert_eq!(context.dag().len(), nodes);
        nodes
    };
    assert!(before > 0);
}

#[test]
fn node_rows_digest_and_count_as_their_trees() {
    let mut context = VcContext::new();
    for row in varied_rows() {
        let id = context.push_node_row(&row).unwrap();
        assert_eq!(context.digest(id).ok(), formula_digest(&row.formula).ok());
        assert_eq!(context.row_node_count(id).ok(), Some(query_size(&[&row.formula])));
    }
}

#[test]
fn trees_alive_counts_the_materialized_trees() {
    let mut context = VcContext::new();
    let id =
        context.push_node_row(&vc(VcKind::DivisionByZero, lt(var("d"), Formula::Int(1)))).unwrap();
    let first = context.materialize(id).expect("row");
    let second = context.materialize(id).expect("row");
    assert_eq!((context.stats().trees_alive, context.stats().trees_alive_max), (2, 2));
    drop(first);
    assert_eq!(context.stats().trees_alive, 1);
    drop(second);
    let stats = context.stats();
    assert_eq!((stats.trees_alive, stats.trees_alive_max), (0, 2));
    assert_eq!(stats.materialization.rows, 2);
    assert_eq!(stats.rows, 1);
    assert!(stats.dag_nodes >= 3 && stats.retained_row_bytes > 0);
}

#[test]
fn a_context_is_send_and_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<VcContext>();
    assert_send_sync::<MaterializedVc>();
}

/// A memo value that counts its drops.
#[derive(Default)]
struct DropProbe(Option<Arc<AtomicUsize>>);

impl Drop for DropProbe {
    fn drop(&mut self) {
        if let Some(count) = &self.0 {
            count.fetch_add(1, Ordering::SeqCst);
        }
    }
}

#[test]
fn memo_slots_drop_with_the_context() {
    let drops = Arc::new(AtomicUsize::new(0));
    let context = VcContext::new();
    let set = context.memo().with(MemoSlot::Certify, |probe: &mut DropProbe| {
        probe.0 = Some(Arc::clone(&drops));
    });
    assert_eq!(set, Some(()));
    assert!(context.memo().contains(MemoSlot::Certify));
    assert!(!context.memo().contains(MemoSlot::Lowering));
    assert!(!context.memo().contains(MemoSlot::Recipes));
    // A slot holding another type is not handed out as this one.
    assert_eq!(context.memo().with(MemoSlot::Certify, |_: &mut u64| ()), None);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    drop(context);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn sequences_share_their_prefixes() {
    let mut context = VcContext::new();
    let (a, b, c) =
        (context.intern(&var("a")), context.intern(&var("b")), context.intern(&var("c")));
    let ab = context.seq(&[a, b]).expect("seq");
    let abc = context.seq_push(ab, c).expect("seq");
    let cells = context.stats().seq_cells;
    assert_eq!(context.seq(&[a, b, c]).ok(), Some(abc));
    assert_eq!(context.stats().seq_cells, cells, "an equal sequence adds no cell");
    assert_eq!(context.seq_nodes(abc).ok(), Some(vec![a, b, c]));
    let foreign = VcContext::new().intern(&var("a"));
    assert!(matches!(context.seq(&[foreign]), Err(VcContextError::UnknownNode(_))));
}

#[test]
fn the_relevance_walk_is_linear_in_a_deep_chain_and_cached() {
    // `x0 == 0 && (x1 == 1 && (x2 == 2 && ...))`, 300 deep (the trees' own recursive drop
    // and equality bound the depth a test thread can hold): every level adds a name, so a
    // per-node name set would copy O(n^2) names; the walk visits each node once.
    let depth = 300;
    let mut chain = eq(var("x0"), Formula::Int(0));
    for level in 1..depth {
        chain = Formula::And(vec![eq(var(&format!("x{level}")), Formula::Int(level)), chain]);
    }
    let mut context = VcContext::new();
    let named = eq(var("x7"), Formula::Int(7));
    let renamed = eq(var("y"), var("x7#1"));
    let row = spine_row(&mut context, &[named.clone(), renamed.clone()], &chain, false);
    let spine = match context.row(row).expect("a row").formula() {
        RowFormula::Spine(spine) => *context.spine(spine).expect("a spine"),
        RowFormula::Node(_) => unreachable!("a spine row"),
    };
    let kept = context.kept(&spine).expect("kept");
    assert_eq!(kept, vec![context.intern(&named)]);
    let work = context.stats().relevance;
    assert_eq!(work.rows, 1);
    let nodes = context.dag().len() as u64;
    let depth = depth as u64;
    assert!(work.work <= 2 * nodes + depth + 8, "{work:?} over {nodes} nodes");
    // A second read is the cached list; materializing reads it without walking again.
    assert_eq!(context.kept(&spine).expect("kept"), kept);
    let materialized = context.materialize(row).expect("materialized");
    assert_eq!(materialized.vc().formula, Formula::And(vec![named.clone(), chain]));
    assert_eq!(context.stats().relevance, work);
    // New relevance names forget the kept list; the names themselves stay cached.
    context.vars_mut().insert("x7#1", "x7");
    let kept = context.kept(&spine).expect("kept");
    assert_eq!(kept, vec![context.intern(&named), context.intern(&renamed)]);
    let again = context.stats().relevance;
    assert_eq!(again.rows, 2);
    assert!(again.work - work.work <= depth + 8, "{again:?} after {work:?}");
}

#[test]
fn quantified_names_leave_only_the_quantifier() {
    // `forall x. x == q` names `q`; the same `x == q` outside a quantifier names both.
    let inner = eq(var("x"), var("q"));
    let quantified =
        Formula::Forall(vec![(Symbol::intern("x"), Sort::Int)], Box::new(inner.clone()));
    let mut context = VcContext::new();
    let both = context.intern(&Formula::And(vec![quantified.clone(), inner.clone()]));
    let only = context.intern(&quantified);
    let names = |set: Result<std::collections::BTreeSet<String>, VcContextError>| {
        set.expect("a node of this context").into_iter().collect::<Vec<_>>()
    };
    assert_eq!(names(context.formula_var_names(only)), vec!["q"]);
    assert_eq!(names(context.formula_var_names(both)), vec!["q", "x"]);
    // Nested quantifiers each remove their own names.
    let nested = context.intern(&Formula::Exists(
        vec![(Symbol::intern("q"), Sort::Int)],
        Box::new(Formula::And(vec![quantified, var("r")])),
    ));
    assert_eq!(names(context.formula_var_names(nested)), vec!["r"]);
}

#[test]
fn a_full_table_is_refused_never_aliased() {
    assert_eq!(next_index(7, "row"), Ok(7));
    assert_eq!(next_index(u32::MAX as usize, "row"), Ok(u32::MAX));
    assert_eq!(next_index(u32::MAX as usize + 1, "span"), Err(VcContextError::Full("span")));
    assert_eq!(
        VcContextError::Full("spine").to_string(),
        "this context's spine table is full (2^32 entries)"
    );
}

#[test]
fn the_row_oracle_keeps_an_agreeing_row_and_counts_it() {
    let rows = varied_rows();
    let mut context = VcContext::new();
    for row in &rows {
        let id = context.push_node_row(row).unwrap();
        assert_eq!(context.check_row(id, row), Ok(id));
        assert_same_vc(context.materialize(id).unwrap().vc(), row);
    }
    let count = context.parity(Oracle::Row);
    assert_eq!(count, ParityCount { rows: rows.len() as u64, mismatches: 0 });
    // The other oracles are not touched by the row oracle.
    assert_eq!(context.parity(Oracle::Identity), ParityCount::default());
    assert_eq!(context.stats().parity[0], (Oracle::Row, count));
}

#[test]
fn the_row_oracle_substitutes_the_eager_row_on_a_mismatch() {
    // Negative control: a row checked against a VC it was not made from disagrees, is
    // counted, and the eager VC is what the returned id reads back as.
    let rows = varied_rows();
    let mut context = VcContext::new();
    let first = context.push_node_row(&rows[0]).unwrap();
    let substitute = context.check_row(first, &rows[1]).unwrap();
    assert_ne!(substitute, first);
    assert_same_vc(context.materialize(substitute).unwrap().vc(), &rows[1]);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 1, mismatches: 1 });
    // A row of another context cannot be read here: also a mismatch, also substituted.
    let foreign = VcContext::new().push_node_row(&rows[2]).unwrap();
    let substitute = context.check_row(foreign, &rows[2]).unwrap();
    assert_same_vc(context.materialize(substitute).unwrap().vc(), &rows[2]);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 2, mismatches: 2 });
    // `push_checked_row` is the agreeing path.
    let checked = context.push_checked_row(&rows[3]).unwrap();
    assert_same_vc(context.materialize(checked).unwrap().vc(), &rows[3]);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 3, mismatches: 2 });
    assert!(same_row(&rows[3], &rows[3]) && !same_row(&rows[0], &rows[1]));
}

#[test]
fn a_parity_tally_sums_the_contexts_it_folds() {
    // T3 L4 C07p: a crate phase's tally of the contexts it ran and dropped (each R1
    // harvest's) is the per-oracle sum of their counts, and starts at zero.
    let rows = varied_rows();
    let mut tally = ParityTally::default();
    for oracle in Oracle::ALL {
        assert_eq!(tally.get(oracle), ParityCount::default());
    }
    let mut agreeing = VcContext::new();
    for row in &rows {
        agreeing.push_checked_row(row).unwrap();
    }
    tally.fold(&agreeing);
    let mut disagreeing = VcContext::new();
    let first = disagreeing.push_node_row(&rows[0]).unwrap();
    disagreeing.check_row(first, &rows[1]).unwrap();
    disagreeing.record_parity(Oracle::Size, false);
    tally.fold(&disagreeing);
    drop((agreeing, disagreeing));
    let total = rows.len() as u64 + 1;
    assert_eq!(tally.get(Oracle::Row), ParityCount { rows: total, mismatches: 1 });
    assert_eq!(tally.get(Oracle::Size), ParityCount { rows: 1, mismatches: 0 });
    assert_eq!(tally.get(Oracle::Identity), ParityCount::default());
}

#[test]
fn wave500_kept_arc_and_cached_and_shell_preserve_exact_spine_digest_and_materialization() {
    let mut context = VcContext::new();
    let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(1)));
    let f2 = Formula::Eq(Box::new(var("y")), Box::new(Formula::Add(Box::new(var("x")), Box::new(Formula::Int(2)))));
    let f3 = Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(99)));
    let body = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)));
    let defs = [f1.clone(), f2.clone(), f3];
    let nodes: Vec<_> = defs.iter().map(|def| context.intern(def)).collect();
    let seq = context.seq(&nodes).unwrap();
    let body_node = context.intern(&body);
    let spine = Spine { candidates: seq, body: body_node, rule: RelevanceRule::BlockDefs };
    let kept_first = context.kept_arc(&spine).unwrap();
    let kept_second = context.kept_arc(&spine).unwrap();
    assert!(Arc::ptr_eq(&kept_first, &kept_second));
    assert_eq!(kept_first.as_ref(), context.kept(&spine).unwrap().as_slice());

    let row = spine_row(&mut context, &defs, &body, true);
    let expected_formula = Formula::And(vec![f1, f2, body]);
    let mat = context.materialize(row).unwrap();
    assert_eq!(mat.vc().formula, expected_formula);
    assert_eq!(context.digest(row).unwrap(), formula_digest(&expected_formula).unwrap());
}
