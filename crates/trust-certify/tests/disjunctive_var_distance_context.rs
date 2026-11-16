// A disjunction whose refuting guard sits two variable steps away, behind an
// alias with many siblings, certifies through the bounded-distance context lane
// (`certify_disjunctive_contradiction_in_distance_balls`), and only when the guard
// is really there.
//
// THE MEASURED CASE (TRUST-KI-1014-1, 2026-10-14). aterm-codec `zlib_decompress`
// (`inflate.rs:911`) computes `input.len() - 4` after `if input.len() < 6 { return }`.
// Its hardened `Overflow(Sub)` twin was kernel-certified on seal trust-6606d3bd and
// is not from trust-1b185739 on: the solver still proves it, but no Clean
// certificate is attached, so the publication boundary withholds the proof
// ("compiler transport claimed a favorable outcome without attachable native or
// clean-kernel proof evidence"). The twin's hypothesis set grew in between (the
// type-range battery `aebf15b1ed` gave the twin), and the variable-connected
// component of
// `Or([_48 - 4 < 0, _48 - 4 > MAX])` went from 41 to 49 augmented chain edges, over
// `refute_via_chain_edges`' 48-edge cap: `_48 = len` reaches the guard
// `¬(len < 6)`, but also `_4 = len`, `_8 = len`, `_12 = len`, `_33 = len`, …, each
// with its own type-range pair. The 1-hop set (`_48`'s own bounds) cannot close it.
// The ball of radius 1 (`vars ⊆ {_48, len}`) can.
//
// The real formula is pinned below as the compiler generates it today; the
// synthetic shape isolates the mechanism; the controls drop or weaken the guard,
// which must leave both uncertified.

use trust_certify::{certify_vc, recheck_vc_cleancic};
use trust_ir::ProofEvidence;
use trust_types::{Formula, HardenedVcCategory, Sort, SourceSpan, VcKind, VerificationCondition};

#[path = "disjunctive_var_distance_context/inflate911_twin.rs"]
mod inflate911_twin;
#[path = "disjunctive_var_distance_context/min_twin.rs"]
mod min_twin;

const U64_MAX: i128 = u64::MAX as i128;
const ISIZE_MAX: i128 = isize::MAX as i128;

fn int(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn lit(value: i128) -> Formula {
    Formula::Int(value)
}

fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}

fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}

fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}

fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

fn sub(a: Formula, b: Formula) -> Formula {
    Formula::Sub(Box::new(a), Box::new(b))
}

fn not(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}

/// The twin's row identity as the compiler mints it for `zlib_decompress`.
fn twin_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: "mir_assert::Overflow(Sub)".to_string(),
            detail: "MIR arithmetic assert can panic; hardened code needs proven arithmetic \
                     preconditions"
                .to_string(),
        },
        function: "zlib_decompress".into(),
        location: SourceSpan {
            file: "src/lib.rs".into(),
            line_start: 1836,
            col_start: 25,
            line_end: 1836,
            col_end: 40,
        },
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// Certify, then require the consumer's canonical regeneration to reproduce and
/// Clean-recheck the exact payload (and refuse it under another identity).
fn certifies_and_rechecks(vc: &VerificationCondition) -> bool {
    let Some(evidence) = certify_vc(vc) else {
        return false;
    };
    let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        panic!("expected CleanCic evidence");
    };
    assert!(
        recheck_vc_cleancic(&term, &context, &lineage, vc),
        "canonical regeneration must reproduce and Clean-recheck the exact payload"
    );
    let mut other = vc.clone();
    other.function = "some_other_function".into();
    assert!(
        !recheck_vc_cleancic(&term, &context, &lineage, &other),
        "the certificate is bound to its own obligation identity"
    );
    true
}

/// `x = len ∧ guard ∧ x, len in range ∧ (a_k = len ∧ a_k in range for k < aliases)
///  ∧ Or([x - 4 < 0, x - 4 > u64::MAX])` — the aterm shape reduced to its mechanism.
fn aliased_guard_shape(guard: Option<Formula>, aliases: usize) -> Formula {
    let mut cs = vec![
        le(lit(0), int("x")),
        le(int("x"), lit(U64_MAX)),
        le(lit(0), int("len")),
        le(int("len"), lit(ISIZE_MAX)),
        eq(int("x"), int("len")),
    ];
    if let Some(guard) = guard {
        cs.push(guard);
    }
    for k in 0..aliases {
        let a = int(&format!("a{k}"));
        cs.push(eq(a.clone(), int("len")));
        cs.push(le(lit(0), a.clone()));
        cs.push(le(a, lit(U64_MAX)));
    }
    cs.push(Formula::Or(vec![
        lt(sub(int("x"), lit(4)), lit(0)),
        gt(sub(int("x"), lit(4)), lit(U64_MAX)),
    ]));
    Formula::And(cs)
}

/// `¬(len < bound)`, the guard's own spelling in the compiler's formula.
fn len_at_least(bound: i128) -> Formula {
    not(lt(int("len"), lit(bound)))
}

#[test]
fn the_aterm_codec_inflate911_twin_certifies() {
    assert!(
        certifies_and_rechecks(&twin_vc(inflate911_twin::twin())),
        "the hardened Overflow(Sub) twin of `input.len() - 4` (aterm-codec inflate.rs:911) \
         must kernel-certify: its guard `!(input.len() < 6)` is one alias step from the \
         operand"
    );
}

#[test]
fn the_inflate911_twin_without_its_length_facts_does_not_certify() {
    // Drop every conjunct that bounds `input.len()` from below: the `< 6` guard and
    // the facts the earlier `input.len() - 4` (inflate.rs:906) left behind (its
    // passed overflow check `0 <= _33 - 4` and its result `_34.0 = _33 - 4`). With
    // them gone `input.len() = 2` satisfies the rest, so nothing may certify.
    let mentions_33_minus_4 = |f: &Formula| format!("{f:?}").contains("Sub(Var(\"_33\"");
    let guard_on_input = not(lt(int("input__slice_len"), lit(6)));
    let kept: Vec<Formula> = inflate911_twin::twin_conjuncts()
        .into_iter()
        .filter(|c| *c != guard_on_input && !mentions_33_minus_4(c))
        .collect();
    assert!(
        kept.len() < inflate911_twin::twin_conjuncts().len(),
        "the control must actually remove the length facts"
    );
    assert!(
        certify_vc(&twin_vc(Formula::And(kept))).is_none(),
        "without a lower bound on input.len() the subtraction can underflow: no certificate"
    );
}

#[test]
fn the_nine_line_reproducer_twin_certifies() {
    let mut vc = twin_vc(min_twin::twin());
    vc.location = SourceSpan {
        file: "src/lib.rs".into(),
        line_start: 9,
        col_start: 25,
        line_end: 9,
        col_end: 40,
    };
    assert!(certifies_and_rechecks(&vc));
}

#[test]
fn the_nine_line_reproducer_twin_without_its_length_facts_does_not_certify() {
    // As for the aterm row: without `!(input.len() < 6)` and the facts of the first
    // `input.len() - 4` (`0 <= _15 - 4`, `_16.0 = _15 - 4`), `input.len() = 2` is a
    // model (the two byte reads leave `input.len() >= 2`).
    let mentions_15_minus_4 = |f: &Formula| format!("{f:?}").contains("Sub(Var(\"_15\"");
    let guard_on_input = not(lt(int("input__slice_len"), lit(6)));
    let all = min_twin::twin_conjuncts();
    let kept: Vec<Formula> =
        all.iter().filter(|c| **c != guard_on_input && !mentions_15_minus_4(c)).cloned().collect();
    assert!(kept.len() < all.len(), "the control must actually remove the length facts");
    assert!(certify_vc(&twin_vc(Formula::And(kept))).is_none());
}

#[test]
fn a_guard_one_alias_step_away_certifies_past_a_component_over_the_edge_cap() {
    // 16 siblings of `len` put the connected component well over 48 edges, and the
    // 1-hop set `{x}` lacks the guard: only the radius-1 ball `{x, len}` closes it.
    assert!(certifies_and_rechecks(&twin_vc(aliased_guard_shape(Some(len_at_least(6)), 16))));
}

#[test]
fn a_weakened_guard_does_not_certify() {
    // `len >= 3` admits `len = x = 3`, where `x - 4 < 0`: satisfiable.
    assert!(certify_vc(&twin_vc(aliased_guard_shape(Some(len_at_least(3)), 16))).is_none());
    assert!(certify_vc(&twin_vc(aliased_guard_shape(Some(len_at_least(3)), 0))).is_none());
}

#[test]
fn no_guard_does_not_certify() {
    assert!(certify_vc(&twin_vc(aliased_guard_shape(None, 16))).is_none());
    assert!(certify_vc(&twin_vc(aliased_guard_shape(None, 0))).is_none());
}

#[test]
fn a_guard_on_an_unrelated_variable_does_not_certify() {
    // The guard bounds a variable no conjunct ties to `x`: the ball never reaches a
    // fact about `x`, and the system is satisfiable at `x = len = 0`.
    let guard = not(lt(int("unrelated"), lit(6)));
    assert!(certify_vc(&twin_vc(aliased_guard_shape(Some(guard), 16))).is_none());
}

#[test]
fn the_small_shape_still_certifies_through_the_component() {
    // Control on ordering: with no siblings the component is small, and the
    // earlier attempts certify it as before.
    assert!(certifies_and_rechecks(&twin_vc(aliased_guard_shape(Some(len_at_least(6)), 0))));
}
