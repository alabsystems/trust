//! REAL-ARTIFACT regression guard for the FALSE REFUTATION of a correct
//! `async fn` — and for the two properties the fix must keep: the premise is a
//! WHOLE-BODY fact (so it survives path-map saturation), and it blesses nothing.
//!
//! All three fixtures are the compiler's OWN extracted verification input,
//! captured verbatim with `-Ztrust-dump=mir:<dir>`, so these are the MIR, not a
//! hand-built approximation of it:
//!
//! ```rust,ignore
//! pub async fn f(x: u8) -> u16 { (x as u16) + 1 }                       // dedicated
//! pub async fn f(x: Option<u8>) -> u16 {                                // MERGED
//!     match x { Some(v) => (v as u16) + 1, None => 0 }
//! }
//! pub async fn f(a0: Option<u8>, .., a6: Option<u8>) -> u16 {           // SATURATED
//!     let mut t: u16 = 0;
//!     t = t | match a0 { Some(v) => v as u16, None => 0 };  // .. seven times
//!     t
//! }
//! ```
//!
//! None of the three can fault: `(x as u16) + 1` maxes at 256 for a `u8` `x`,
//! every match is exhaustive, and `|` on `u16` cannot overflow.
//!
//! # What went wrong
//!
//! rustc lowers a resume body to an entry dispatch
//! `SwitchInt(sel) -> [0: .., 1: <ResumedAfterReturn>, .., otherwise: <Unreachable>]`
//! where `sel` is the resume state read out of the coroutine frame. Two
//! obligation families therefore carry a reachability condition that is nothing
//! but a claim ABOUT `sel`:
//!
//! ```text
//! [assert]  sentinel arm      sel == RETURNED
//! [unreach] `otherwise` arm   sel != 0 && sel != 1 && ..
//! ```
//!
//! Both are trivially satisfiable on their own, and on the refutation
//! convention a satisfiable violation formula is a REFUTATION, so a correct
//! program failed its build on resume states the executor protocol cannot
//! produce.
//!
//! Emitting the obligations is RIGHT: neither the `ResumedAfter*` message
//! spelling nor the serialized `exhaustive_enum_unreachable` bit is proof
//! authority in a public TrustIR input, so neither may erase a row. Deciding
//! them without the executor-protocol premise is what was wrong.
//!
//! # Why the premise is GLOBAL
//!
//! `coroutine_resume_state_contract` requires the selector to be written exactly
//! once in the whole body, so `sel ∈ live_states` is a fact about one value at
//! every program point — and a whole-body fact keeps working where a per-path
//! one stops: `v2_build_path_guard_map` caps a block at `MAX_PATHS_PER_BLOCK`
//! paths and, past that, drops the reachability condition entirely. The
//! saturated fixture sits past that cliff — `path_guard_collapse_tests` counts
//! the routes into its merged `Unreachable` — and it is in the corpus precisely
//! so a per-path regression cannot pass this file.

use trust_types::{
    Formula, Statement, Terminator, Ty, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/data/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("coroutine MIR fixture {path} must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("coroutine MIR fixture {path} must deserialize: {e}"))
}

fn dedicated() -> VerifiableFunction {
    load("coroutine_resume_zero_await_widen")
}

fn merged() -> VerifiableFunction {
    load("coroutine_resume_merged_unreachable")
}

/// The k = 7 body whose merged `Unreachable` block overflows
/// `MAX_PATHS_PER_BLOCK`.
fn saturated() -> VerifiableFunction {
    load("coroutine_resume_saturated_unreachable")
}

fn refuted(vcs: &[VerificationCondition]) -> Vec<String> {
    let router = trust_router::Router::deterministic_in_process_ay(60_000);
    router
        .verify_all(vcs)
        .into_iter()
        .filter(|(_, result)| matches!(result, VerificationResult::Failed { .. }))
        .map(|(vc, _)| format!("{:?}", vc.kind))
        .collect()
}

fn block_mut(func: &mut VerifiableFunction, id: usize) -> &mut trust_types::BasicBlock {
    func.body
        .blocks
        .iter_mut()
        .find(|b| b.id.0 == id)
        .unwrap_or_else(|| panic!("fixture must have bb{id}"))
}

/// The blocks whose `SwitchInt` reads a `Discriminant` — the inner `Option`
/// matches, located structurally rather than by pinned ids.
fn enum_switch_blocks(func: &VerifiableFunction) -> Vec<usize> {
    func.body
        .blocks
        .iter()
        .filter(|b| {
            matches!(b.terminator, Terminator::SwitchInt { .. })
                && b.stmts.iter().any(|s| {
                    matches!(
                        s,
                        Statement::Assign { rvalue: trust_types::Rvalue::Discriminant(_), .. }
                    )
                })
                && b.id.0 != 0
        })
        .map(|b| b.id.0)
        .collect()
}

/// Strip the recognizer's authority WITHOUT touching the panic surface: clear
/// the entry dispatch's exhaustiveness certificate. `coroutine_resume_state_contract`
/// declines, so no resume premise is available — the pre-fix formulas, exactly.
fn without_recognized_contract(mut func: VerifiableFunction) -> VerifiableFunction {
    let entry = func.body.blocks.first_mut().expect("fixture has an entry block");
    let Terminator::SwitchInt { exhaustive_enum_unreachable, .. } = &mut entry.terminator else {
        panic!("fixture entry must be the resume dispatch");
    };
    assert!(*exhaustive_enum_unreachable, "fixture must carry the certificate to begin with");
    *exhaustive_enum_unreachable = false;
    assert!(
        trust_types::coroutine_resume_state_contract(&func.body).is_none(),
        "control must make the recognizer decline"
    );
    func
}

/// Drop the extractor-supplied preconditions, so a surviving proof is
/// attributable to facts this crate derives rather than to a hypothesis that
/// arrived in the serialized input.
fn without_extractor_preconditions(mut func: VerifiableFunction) -> VerifiableFunction {
    func.preconditions.clear();
    func
}

/// THE REGRESSION, dedicated-unreachable shape. `pub async fn f(x: u8) -> u16 {
/// (x as u16) + 1 }` cannot fault, so no obligation of it may be REFUTED.
#[test]
fn correct_zero_await_async_body_is_never_refuted() {
    let vcs = trust_vcgen::generate_vcs(&dedicated());
    assert!(!vcs.is_empty(), "fixture must still emit obligations");
    assert_eq!(refuted(&vcs), Vec::<String>::new());
}

/// THE REGRESSION, MERGED-unreachable shape. The single `Unreachable` block is
/// the `otherwise` of both the resume dispatch and the inner `Option` match.
#[test]
fn correct_matching_async_body_is_never_refuted() {
    let func = merged();
    let mut otherwise_targets = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::SwitchInt { otherwise, .. } => Some(otherwise.0),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(otherwise_targets.len() >= 2, "the fixture must have two switches");
    otherwise_targets.sort_unstable();
    otherwise_targets.dedup();
    assert_eq!(
        otherwise_targets.len(),
        1,
        "the fixture's value is that rustc MERGED the unreachable blocks; if this \
         drifts to a dedicated block per switch the test no longer covers the \
         merged shape and must be re-captured"
    );
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(!vcs.is_empty(), "fixture must still emit obligations");
    assert_eq!(refuted(&vcs), Vec::<String>::new());
}

/// THE REGRESSION PAST THE PATH CAP — the property a per-path premise cannot
/// have. The body's sequential `Option` matches route more paths into one merged
/// `Unreachable` than `MAX_PATHS_PER_BLOCK` allows (counted in
/// `path_guard_collapse_tests`); the body is still correct and still may not be
/// refuted.
#[test]
fn correct_async_body_past_the_path_cap_is_never_refuted() {
    let func = saturated();
    assert!(
        enum_switch_blocks(&func).len() >= 7,
        "the fixture's value is that its merged `Unreachable` is reached by more \
         than `MAX_PATHS_PER_BLOCK` routes; if the shape drifts it must be re-captured"
    );
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(!vcs.is_empty(), "fixture must still emit obligations");
    assert_eq!(refuted(&vcs), Vec::<String>::new());
}

/// ATTRIBUTION. The bodies stay unrefuted with the extractor's preconditions
/// removed, so the proof rides on facts derived here, not on a serialized
/// hypothesis.
#[test]
fn the_premise_is_derived_not_inherited() {
    for fixture in [merged(), saturated()] {
        let vcs = trust_vcgen::generate_vcs(&without_extractor_preconditions(fixture));
        assert_eq!(refuted(&vcs), Vec::<String>::new());
    }
}

/// NEGATIVE CONTROL 1 — the premise is not free. With the recognizer declining,
/// the sentinel and `otherwise` rows are decided bare and REFUTE again, so the
/// tests above cannot be passing for some unrelated reason.
#[test]
fn without_the_contract_the_protocol_rows_refute_again() {
    for fixture in [dedicated(), merged(), saturated()] {
        let func = without_recognized_contract(fixture);
        let vcs = trust_vcgen::generate_vcs(&func);
        let refuted = refuted(&vcs);
        assert!(
            refuted.iter().any(|kind| kind.contains("ResumedAfterReturn")),
            "an unrecognized body keeps the bare, refutable public sentinel row: {refuted:?}"
        );
    }
}

/// NEGATIVE CONTROL 2 — a PARTIAL match into the merged block is real UB and
/// must stay REFUTED, on the saturated shape as well as the small one. Dropping
/// the `Some` arm from an inner switch routes `d == 1` — a value the `Option`
/// type permits — straight into `Unreachable`.
///
/// On the saturated fixture this is also the guard on the in-edge summary that
/// restores a reachability condition past the path cap: the summary is a
/// disjunction of the in-edges' own branch conditions, so an in-edge that a live
/// value can actually take leaves the row satisfiable, exactly as it must.
#[test]
fn a_partial_match_into_the_merged_block_still_refutes() {
    for fixture in [merged(), saturated()] {
        let mut func = without_extractor_preconditions(fixture);
        let switch = *enum_switch_blocks(&func).first().expect("fixture matches on an enum");
        let Terminator::SwitchInt { targets, .. } = &mut block_mut(&mut func, switch).terminator
        else {
            panic!("located block must be the enum switch");
        };
        let before = targets.len();
        targets.retain(|(value, _)| *value != 1);
        assert_eq!(targets.len(), before - 1, "the mutation must actually drop an arm");
        let refuted = refuted(&trust_vcgen::generate_vcs(&func));
        assert!(
            refuted.iter().any(|kind| kind.contains("Unreachable")),
            "a reachable `Unreachable` is real UB and must never be blessed: {refuted:?}"
        );
    }
}

/// NEGATIVE CONTROL 3 — the enum outgrows the switch. A third declared variant
/// with the switch still covering `{0, 1}` makes `d == 2` reach the merged
/// block; no fact here closes that, and none must.
#[test]
fn an_enum_wider_than_the_switch_cases_still_refutes() {
    for fixture in [merged(), saturated()] {
        let mut func = without_extractor_preconditions(fixture);
        let switch = *enum_switch_blocks(&func).first().expect("fixture matches on an enum");
        // The local the `Discriminant` statement of that block reads.
        let source = block_mut(&mut func, switch)
            .stmts
            .iter()
            .find_map(|s| match s {
                Statement::Assign { rvalue: trust_types::Rvalue::Discriminant(src), .. } => {
                    Some(src.local)
                }
                _ => None,
            })
            .expect("the enum switch reads a discriminant");
        let local = func
            .body
            .locals
            .iter_mut()
            .find(|l| l.index == source)
            .expect("the discriminant source is a declared local");
        let Ty::Adt { variants, .. } = &mut local.ty else {
            panic!("the discriminant source must be an enum")
        };
        let grown = variants.iter().map(|v| v.discriminant).max().unwrap_or(0) + 1;
        variants.push(trust_types::VariantDef {
            name: "GrownByTheTest".to_string(),
            discriminant: grown,
            fields: Vec::new(),
        });
        let refuted = refuted(&trust_vcgen::generate_vcs(&func));
        assert!(
            refuted.iter().any(|kind| kind.contains("Unreachable")),
            "a variant the switch does not cover reaches the block, so it stays \
             refutable: {refuted:?}"
        );
    }
}

/// NEGATIVE CONTROL 4 — an UNGUARDED in-edge defeats the saturation summary, as
/// it must. Retargeting one block's `Goto` at the merged `Unreachable` makes it
/// reachable unconditionally; the disjunction of in-edge conditions then
/// contains `true` and carries no information, so the row stays REFUTED.
#[test]
fn an_unguarded_edge_into_the_unreachable_block_still_refutes() {
    let mut func = without_extractor_preconditions(saturated());
    let target = func
        .body
        .blocks
        .iter()
        .find(|b| matches!(b.terminator, Terminator::Unreachable))
        .map(|b| b.id)
        .expect("the fixture has a merged unreachable block");
    let goto = func
        .body
        .blocks
        .iter()
        .find(|b| matches!(b.terminator, Terminator::Goto(_)))
        .map(|b| b.id.0)
        .expect("the fixture has a Goto block");
    block_mut(&mut func, goto).terminator = Terminator::Goto(target);
    let refuted = refuted(&trust_vcgen::generate_vcs(&func));
    assert!(
        refuted.iter().any(|kind| kind.contains("Unreachable")),
        "an unconditional edge into the block leaves it genuinely reachable: {refuted:?}"
    );
}

/// THE LOAD-BEARING SOUNDNESS GATE. The whole-body fact is only true because the
/// selector is single-VALUED, and "written exactly once" (the recognizer's gate
/// 4, which counts destination PLACES) only means that while no write channel
/// escapes place accounting. Splice in the cheapest such escape — `&raw mut
/// selector`, the precondition of every pointer write — and the fact must
/// DECLINE, restoring the bare, refutable rows.
///
/// If this test ever passes vacuously (the rows stay proved), the premise is
/// being published for a body whose selector could have been overwritten, which
/// is a false PROOF, not a false refutation.
#[test]
fn an_escaping_selector_address_withdraws_the_premise() {
    let mut func = dedicated();
    let contract = trust_types::coroutine_resume_state_contract(&func.body)
        .expect("fixture must be a recognized resume body");
    // A DECLARED local to hold the pointer, so the body stays well-formed and the
    // only thing the mutation changes is the escape itself.
    let sink = func.body.locals.iter().map(|l| l.index).max().expect("fixture declares locals");
    func.body.locals.push(trust_types::LocalDecl {
        index: sink + 1,
        ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::Int { width: 32, signed: false }) },
        name: None,
    });
    let entry = func.body.blocks.first_mut().expect("entry block");
    let span = match &entry.terminator {
        Terminator::SwitchInt { span, .. } => span.clone(),
        _ => panic!("entry must be the resume dispatch"),
    };
    // A raw pointer to the selector: the recognizer's write counter still reads
    // 1, but a pointer write could now reach it, so the fact must not be minted.
    entry.stmts.push(Statement::Assign {
        place: trust_types::Place::local(sink + 1),
        rvalue: trust_types::Rvalue::AddressOf(
            true,
            trust_types::Place::local(contract.discr_local),
        ),
        span,
    });
    assert!(
        trust_types::coroutine_resume_state_contract(&func.body).is_some(),
        "the mutation must leave the RECOGNIZER satisfied — the point is that the \
         belt, not the recognizer, is what refuses"
    );
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(!vcs.is_empty(), "the mutated body must still emit obligations");
    let refuted = refuted(&vcs);
    assert!(
        refuted.iter().any(|kind| kind.contains("ResumedAfterReturn")),
        "an escaping selector address must withdraw the whole-body premise: {refuted:?}"
    );
}

/// NEGATIVE CONTROL 5 — the premise CANNOT erase a row. Recognized and
/// unrecognized bodies emit the same obligations in the same order; only the
/// hypothesis each is decided under differs. This is the anti-silence property
/// `4ca0cb0eac` established, and this change must not walk it back.
#[test]
fn the_premise_never_adds_or_removes_an_obligation() {
    for fixture in [dedicated as fn() -> VerifiableFunction, merged, saturated] {
        let kinds = |vcs: &[VerificationCondition]| {
            vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect::<Vec<_>>()
        };
        let with = trust_vcgen::generate_vcs(&fixture());
        let without = trust_vcgen::generate_vcs(&without_recognized_contract(fixture()));
        assert_eq!(
            kinds(&with),
            kinds(&without),
            "the executor-protocol premise conditions rows, it never prunes them"
        );
    }
}

/// The premise reaches the rows it is aimed at, and is spelled so it can
/// actually unify: it must mention the SAME selector symbol the entry
/// dispatch's own path guard carries. A hand-rolled `Eq(Var, Int)` that differed
/// in sort or version token would be name-disjoint, inert, and would leave every
/// row exactly as refutable as before while looking fixed.
///
/// Run on the DEDICATED fixture on purpose. In the merged one every path into
/// the block that is not the entry `otherwise` carries `selector == 0` as its
/// own path GUARD, so "a positive `selector == live` occurrence" cannot tell the
/// premise from a guard there; on the dedicated fixture the only path is the
/// entry `otherwise`, whose guard mentions the selector exclusively under `Not`.
#[test]
fn the_premise_shares_the_guards_selector_symbol() {
    let func = dedicated();
    let contract = trust_types::coroutine_resume_state_contract(&func.body)
        .expect("fixture must be a recognized resume body");
    let live = contract.live_states.clone();
    assert!(!live.is_empty(), "the contract must name a live state");

    let unreachable_formula = |f: &VerifiableFunction| {
        trust_vcgen::generate_vcs(f)
            .into_iter()
            .find(|vc| matches!(vc.kind, VcKind::Unreachable))
            .expect("the dispatch's `otherwise` arm must keep its own obligation")
            .formula
    };
    // The selector's SMT symbol, taken from the row the CONTROL emits rather
    // than guessed: the bare `otherwise` obligation is a claim about exactly
    // that local, so its free variables must contain the symbol.
    let control = unreachable_formula(&without_recognized_contract(func.clone()));
    let control_symbols = control.free_variables();
    let selector: Vec<String> = control_symbols
        .iter()
        .filter(|s| s.as_str() == format!("_{}", contract.discr_local))
        .cloned()
        .collect();
    assert_eq!(
        selector.len(),
        1,
        "the bare row must mention the resume selector `_{}`: {control_symbols:?}",
        contract.discr_local
    );

    /// A POSITIVE `symbol == value` occurrence. Deliberately does NOT descend
    /// into `Not`: the `otherwise` guard is `¬(sel == 0) ∧ ¬(sel == 1) ∧ …`, so
    /// counting negated occurrences would make the control look as if it already
    /// carried the premise and this test would pass vacuously.
    fn positive_membership(f: &Formula, symbols: &[String], values: &[u128]) -> bool {
        match f {
            Formula::Eq(a, b) => match (a.as_ref(), b.as_ref()) {
                (Formula::Var(v, _), Formula::Int(k)) | (Formula::Int(k), Formula::Var(v, _)) => {
                    symbols.iter().any(|s| s == v)
                        && values.iter().any(|value| i128::try_from(*value) == Ok(*k))
                }
                _ => false,
            },
            Formula::And(parts) | Formula::Or(parts) => {
                parts.iter().any(|p| positive_membership(p, symbols, values))
            }
            _ => false,
        }
    }
    assert!(
        !positive_membership(&control, &selector, &live),
        "control must NOT already carry the premise: {control:#?}"
    );
    let fixed = unreachable_formula(&func);
    assert!(
        positive_membership(&fixed, &selector, &live),
        "the premise must appear as a positive `selector == live state` conjunct \
         over a symbol the row already mentions: {fixed:#?}"
    );
}

/// The premise is a WHOLE-BODY fact, so it must be present on rows that have
/// nothing to do with the entry dispatch too — that is what makes it survive the
/// path cap. Pinned on the saturated fixture's sentinel row, whose block is many
/// edges away from the merged `Unreachable`.
#[test]
fn the_premise_is_global_not_attached_to_one_block() {
    let func = saturated();
    let contract = trust_types::coroutine_resume_state_contract(&func.body)
        .expect("fixture must be a recognized resume body");
    let selector = format!("_{}", contract.discr_local);
    let facts = trust_vcgen::generate_vcs(&func);
    let mentioning = facts
        .iter()
        .filter(|vc| {
            vc.formula
                .free_variables()
                .iter()
                .any(|v| *v == selector || v.starts_with(&format!("{selector}#")))
        })
        .count();
    assert_eq!(
        mentioning,
        facts.len(),
        "every obligation of a recognized resume body is decided under the same \
         whole-body selector fact"
    );
}

/// THE SOUNDNESS GATE, SECOND CHANNEL — the alias the belt used to let through.
///
/// `selector_write_channel_is_unaccountable`'s alias arm was an ALLOWLIST of
/// `Rvalue::{Ref, AddressOf, CopyForDeref}`. `Rvalue::Unsupported` carries place
/// operands too, and it is what `trust-mir-extract` mints for
/// `mir::Rvalue::Reborrow` — a handle out of the reborrowed place whose aliasing
/// semantics the extractor explicitly declines to model. Splice exactly that
/// form in over the selector: the fact must DECLINE, restoring the bare,
/// refutable rows, for the same reason `&raw mut selector` makes it decline.
///
/// If this ever passes vacuously (the rows stay proved), the premise is being
/// published for a body holding an unmodeled handle to its own selector — a
/// false PROOF.
#[test]
fn an_unmodeled_reborrow_of_the_selector_withdraws_the_premise() {
    let mut func = dedicated();
    let contract = trust_types::coroutine_resume_state_contract(&func.body)
        .expect("fixture must be a recognized resume body");
    let sink = func.body.locals.iter().map(|l| l.index).max().expect("fixture declares locals");
    func.body.locals.push(trust_types::LocalDecl {
        index: sink + 1,
        ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::Int { width: 32, signed: false }) },
        name: None,
    });
    let entry = func.body.blocks.first_mut().expect("entry block");
    let span = match &entry.terminator {
        Terminator::SwitchInt { span, .. } => span.clone(),
        _ => panic!("entry must be the resume dispatch"),
    };
    // Byte-for-byte the shape `convert.rs`'s `mir::Rvalue::Reborrow` arm mints.
    entry.stmts.push(Statement::Assign {
        place: trust_types::Place::local(sink + 1),
        rvalue: trust_types::Rvalue::Unsupported {
            kind: "Rvalue::Reborrow".to_string(),
            detail: "Mut reborrow of a user ADT via the Reborrow/CoerceShared trait \
                     needs reborrow-aliasing semantics"
                .to_string(),
            operands: vec![trust_types::Operand::Copy(trust_types::Place::local(
                contract.discr_local,
            ))],
        },
        span,
    });
    assert!(
        trust_types::coroutine_resume_state_contract(&func.body).is_some(),
        "the mutation must leave the RECOGNIZER satisfied — the point is that the \
         belt, not the recognizer, is what refuses"
    );
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(!vcs.is_empty(), "the mutated body must still emit obligations");
    let refuted = refuted(&vcs);
    assert!(
        refuted.iter().any(|kind| kind.contains("ResumedAfterReturn")),
        "an unmodeled handle out of the selector must withdraw the whole-body \
         premise: {refuted:?}"
    );
}

/// The belt's arms are about the SELECTOR, not about the marker. An
/// `Rvalue::Unsupported` that names some OTHER local is ordinary unmodeled code
/// and must not cost the body its premise — otherwise the fix above would be a
/// blanket withdrawal dressed up as a targeted one, and every async body with an
/// unmodeled rvalue anywhere in it would go back to being falsely refuted.
#[test]
fn an_unmodeled_rvalue_over_an_unrelated_local_keeps_the_premise() {
    let mut func = dedicated();
    let contract = trust_types::coroutine_resume_state_contract(&func.body)
        .expect("fixture must be a recognized resume body");
    let sink = func.body.locals.iter().map(|l| l.index).max().expect("fixture declares locals");
    for index in [sink + 1, sink + 2] {
        func.body.locals.push(trust_types::LocalDecl {
            index,
            ty: Ty::Int { width: 32, signed: false },
            name: None,
        });
    }
    assert_ne!(sink + 2, contract.discr_local, "the decoy must not be the selector");
    let entry = func.body.blocks.first_mut().expect("entry block");
    let span = match &entry.terminator {
        Terminator::SwitchInt { span, .. } => span.clone(),
        _ => panic!("entry must be the resume dispatch"),
    };
    entry.stmts.push(Statement::Assign {
        place: trust_types::Place::local(sink + 1),
        rvalue: trust_types::Rvalue::Unsupported {
            kind: "Rvalue::Reborrow".to_string(),
            detail: "over an unrelated local".to_string(),
            operands: vec![trust_types::Operand::Copy(trust_types::Place::local(sink + 2))],
        },
        span,
    });
    let vcs = trust_vcgen::generate_vcs(&func);
    assert_eq!(refuted(&vcs), Vec::<String>::new());
}
