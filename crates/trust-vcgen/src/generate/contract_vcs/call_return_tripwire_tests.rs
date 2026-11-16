//! INTRINSIC-RESIDUAL-1 — a return slot written directly by a call that no conjunct
//! constrains is a refutable query over havoc, and the postcondition lane fails it
//! closed to the visible `SpecUnverifiable` row (`return_slot_only_in_negated_clause`).

use trust_types::{Formula, Sort, VcKind, VerifiableFunction};

use super::return_slot_only_in_negated_clause;

fn capture(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture must deserialize")
}

fn ret() -> Formula {
    Formula::Var("_0".into(), Sort::Int)
}

fn x() -> Formula {
    Formula::Var("x".into(), Sort::Int)
}

fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}

fn not(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}

fn is_spec_unverifiable(kind: &VcKind) -> bool {
    matches!(kind, VcKind::UnsupportedMir { kind, .. } if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND)
        || matches!(
            kind.declined_contract_body(),
            Some(d) if d.cause == trust_types::ContractBodyDeclineCause::UnconstrainedReturnCall
        )
}

#[test]
fn the_return_slot_is_free_only_when_the_clause_alone_mentions_it() {
    let clause = not(le(ret(), Formula::Int(5)));
    let range = le(Formula::Int(0), x());
    assert!(return_slot_only_in_negated_clause(&Formula::And(vec![range.clone(), clause.clone()])));
    // A pin, a guarded model equality or any other conjunct over `_0` constrains it.
    let pin = Formula::Eq(Box::new(ret()), Box::new(x()));
    assert!(!return_slot_only_in_negated_clause(&Formula::And(vec![pin, clause.clone()])));
    let guarded = Formula::Implies(
        Box::new(range.clone()),
        Box::new(Formula::Eq(Box::new(ret()), Box::new(x()))),
    );
    assert!(!return_slot_only_in_negated_clause(&Formula::And(vec![guarded, clause.clone()])));
    // A second negation over `_0` is a constraint too, not a second copy of the clause.
    let other = not(le(ret(), Formula::Int(1)));
    assert!(!return_slot_only_in_negated_clause(&Formula::And(vec![other, clause.clone()])));
    // The path-guard wrap: every arm must leave `_0` free.
    let arm_free = Formula::And(vec![range.clone(), clause.clone()]);
    let arm_pinned =
        Formula::And(vec![Formula::Eq(Box::new(ret()), Box::new(x())), clause.clone()]);
    assert!(return_slot_only_in_negated_clause(&Formula::Or(vec![
        arm_free.clone(),
        arm_free.clone()
    ])));
    assert!(!return_slot_only_in_negated_clause(&Formula::Or(vec![arm_free, arm_pinned])));
    // A clause that never mentions `_0` is not this tripwire's business.
    assert!(!return_slot_only_in_negated_clause(&Formula::And(vec![range, not(le(x(), x()))])));
}

fn unsigned_abs_capture() -> VerifiableFunction {
    capture(include_str!(
        "../../../tests/fixtures/range_adversarial/wide_ok_f23_u32_unsigned_abs_o0.json"
    ))
}

fn rows_of(func: &VerifiableFunction) -> (bool, bool) {
    let vcs = crate::generate_vcs(func);
    (
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        vcs.iter().any(|vc| is_spec_unverifiable(&vc.kind)),
    )
}

/// The measured row: `fn f(x: i32) -> u32 ensures result <= 2147483648 { x.unsigned_abs() }`
/// (stage-2 capture). `unsigned_abs` is an unmarked sysroot method no model pins, so
/// `_0` is free: the row was `Failed { _0 = 2147483649 }`. It is now the visible
/// unverifiable row.
#[test]
fn an_unmodeled_sysroot_call_return_is_failed_closed() {
    assert_eq!(rows_of(&unsigned_abs_capture()), (false, true));
}

/// The SAME body, with the callee no longer an unmarked sysroot item, keeps its
/// Postcondition row: a user callee (it may be composed through its own certified
/// contract), a callee with no `callee_key` (no evidence either way), and an
/// extractor-stamped `@trust-…` path (some lane models it).
#[test]
fn only_an_unmarked_sysroot_callee_fires() {
    let retarget = |edit: &dyn Fn(&mut String, &mut Option<trust_types::CalleeKey>)| {
        let mut func = unsigned_abs_capture();
        let trust_types::Terminator::Call { func: callee, callee_key, .. } =
            &mut func.body.blocks[0].terminator
        else {
            panic!("the capture's entry block ends in the call");
        };
        edit(callee, callee_key);
        func
    };
    let user = retarget(&|_, key| {
        if let Some(key) = key {
            key.krate_is_real_sysroot = false;
        }
    });
    assert_eq!(rows_of(&user), (true, false), "a user callee keeps its row");
    let keyless = retarget(&|_, key| *key = None);
    assert_eq!(rows_of(&keyless), (true, false), "a keyless call keeps its row");
    let marked = retarget(&|callee, _| {
        *callee =
            format!("{}{callee}", trust_types::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX);
    });
    assert_eq!(rows_of(&marked), (true, false), "a marked callee keeps its row");
    // Trust (std-call-summaries P2 review): the panic-freedom-only intrinsic stamp
    // is modeled by no lane (its result is a fresh havoc), so it FIRES like an
    // unmarked sysroot callee: `_0` stays free and a refutation would be over havoc.
    let panic_free = retarget(&|callee, _| {
        *callee = format!(
            "{}core::intrinsics::minimumf64",
            trust_types::TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX
        );
    });
    assert_eq!(rows_of(&panic_free), (false, true), "the panic-free stamp fires");
}

/// A MODELED call keeps its row: the saturating model pins `_0` (guarded
/// equalities), so the clause is a real obligation and still proves.
#[test]
fn a_modeled_call_return_keeps_its_postcondition_row() {
    let func = capture(include_str!("../../../tests/fixtures/sat_add_ge.json"));
    assert_eq!(rows_of(&func), (true, false));
}

#[test]
fn contract_vcs_dedupes_typed_and_text_ensures_and_preserves_ambiguous_index_refusal() {
    assert!(!return_slot_only_in_negated_clause(&Formula::Or(Vec::new())));
    let nested = Formula::And(vec![
        le(Formula::Int(0), x()),
        Formula::And(vec![not(le(ret(), Formula::Int(5))), Formula::Eq(Box::new(ret()), Box::new(x()))]),
    ]);
    assert!(!return_slot_only_in_negated_clause(&nested));

    // Fast-exit path: stripping all postconditions and `Ensures` contracts emits zero Postcondition rows.
    let mut no_ensures = capture(include_str!("../../../tests/fixtures/sat_add_ge.json"));
    no_ensures.postconditions.clear();
    no_ensures.contracts.retain(|c| !matches!(c.kind, trust_types::ContractKind::Ensures));
    no_ensures.spec.ensures.clear();
    assert!(
        !crate::generate_vcs(&no_ensures).iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        "postcondition-free function must emit no Postcondition VCs"
    );

    // Unique vs duplicate `Ensures` contract index resolution without re-parsing drift.
    let mut dup_ensures = capture(include_str!("../../../tests/fixtures/sat_add_ge.json"));
    let Some(ensures_idx) = dup_ensures
        .contracts
        .iter()
        .position(|c| matches!(c.kind, trust_types::ContractKind::Ensures))
    else {
        panic!("sat_add_ge fixture must carry an Ensures contract");
    };
    let single_vcs = crate::generate_vcs(&dup_ensures);
    let single_post_vcs: Vec<_> =
        single_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
    assert!(!single_post_vcs.is_empty());
    assert!(
        single_post_vcs.iter().all(|vc| {
            vc.contract_metadata.as_ref().and_then(|m| m.source_contract_index)
                == Some(ensures_idx)
        }),
        "unique Ensures clause must bind source_contract_index"
    );

    let cloned_clause = dup_ensures.contracts[ensures_idx].clone();
    dup_ensures.contracts.push(cloned_clause);
    let dup_vcs = crate::generate_vcs(&dup_ensures);
    let dup_post_vcs: Vec<_> =
        dup_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
    assert_eq!(
        dup_post_vcs.len(),
        single_post_vcs.len(),
        "duplicate identical Ensures text must still deduplicate to one body postcondition set"
    );
    assert!(
        dup_post_vcs.iter().all(|vc| {
            vc.contract_metadata.as_ref().and_then(|m| m.source_contract_index).is_none()
        }),
        "ambiguous duplicate Ensures clauses must leave source_contract_index as None"
    );
}
