// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Trust (2026-09-23, D3/W1a): the literal-zero range-start fold in the
//! `UnboundedAllocation` atoms (`fold_sub_literal_zero`).
//!
//! `(0..n.min(8) as u32).collect()` (ordinary-Rust sweep s20) counted
//! `Sub(end, Int(0))`, and the Clean kernel's scaled-chain recognizer needs a
//! bare variable under the byte atom's `Mul(stride, _)`, so the row could only
//! reach `SolverRevalidated` (and `UNKNOWN (interval)` whenever `ay` was
//! starved). Folding `end - 0` to `end` IN THE OBLIGATION is exact over the
//! integers and makes the stored formula kernel-certifiable (measured with
//! `trust_certify::certify_vc` on the formula the stage-1 compiler dumped for
//! s20: unfolded `None`, folded `Some`).
//!
//! The hazard is the fold reaching a NON-zero start: `(-268435456..end)` counts
//! `end + 268435456`, and dropping the literal turns a reachable ceiling into
//! `end <= 8` — a false proof. Every test here drives the production entry point
//! `generate_unbounded_allocation_vcs`, except the direct unit tests of the fold.

use trust_types::{BasicBlock, LocalDecl, UnwindEdge, VerifiableBody};

use super::*;

const COLLECT_U32_STRIDE_8: &str = "<core::ops::range::Range<u32> as \
     core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<u32>>::<__trust_elem_bytes@8>";

/// `fn f(n: u32[, m: u32]) -> Vec<u32> { (start..n).collect() }` — the range is
/// a BODY temp (parameters are `1..=arg_count`, see
/// `a_symbolic_inclusive_range_adds_one_to_the_span`).
fn range_collect(start: Operand, second_param: bool) -> VerifiableFunction {
    let arg_count = if second_param { 2 } else { 1 };
    let range_local = arg_count + 1;
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::adt("alloc::vec::Vec<u32>", vec![]), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
    ];
    if second_param {
        locals.push(LocalDecl { index: 2, ty: Ty::u32(), name: Some("m".into()) });
    }
    locals.push(LocalDecl {
        index: range_local,
        ty: Ty::adt("core::ops::range::Range<u32>", vec![]),
        name: Some("r".into()),
    });
    VerifiableFunction {
        name: "fold_probe".to_string(),
        def_path: "user::fold_probe".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(range_local),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "core::ops::range::Range<u32>".to_string(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        vec![start, Operand::Copy(Place::local(1))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: COLLECT_U32_STRIDE_8.to_string(),
                    args: vec![Operand::Move(Place::local(range_local))],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(COLLECT_U32_STRIDE_8),
                    is_foreign: false,
                },
            }],
            arg_count,
            return_ty: Ty::adt("alloc::vec::Vec<u32>", vec![]),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn int(n: i128) -> Operand {
    Operand::Constant(ConstValue::Int(n))
}

/// The single `UnboundedAllocation` VC, its `count` payload, and the atoms of
/// its failure disjunction (the `Or` the alloc lane builds).
fn alloc_vc(func: &VerifiableFunction) -> (String, Vec<Formula>) {
    let vcs: Vec<_> = generate_unbounded_allocation_vcs_on_64_bit(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::UnboundedAllocation { .. }))
        .collect();
    assert_eq!(vcs.len(), 1, "exactly one allocation obligation: {vcs:#?}");
    let VcKind::UnboundedAllocation { count, .. } = &vcs[0].kind else { unreachable!() };
    let mut ors = Vec::new();
    find_ors(&vcs[0].formula, &mut ors);
    assert_eq!(ors.len(), 1, "exactly one failure disjunction: {:?}", vcs[0].formula);
    (count.clone(), ors.remove(0))
}

fn find_ors(f: &Formula, out: &mut Vec<Vec<Formula>>) {
    match f {
        Formula::Or(xs) => out.push(xs.clone()),
        Formula::And(xs) => xs.iter().for_each(|x| find_ors(x, out)),
        _ => {}
    }
}

fn contains_sub_by(f: &Formula, rhs_pred: &dyn Fn(&Formula) -> bool) -> bool {
    match f {
        Formula::Sub(a, b) => {
            rhs_pred(b) || contains_sub_by(a, rhs_pred) || contains_sub_by(b, rhs_pred)
        }
        Formula::Ge(a, b) | Formula::Mul(a, b) | Formula::Add(a, b) => {
            contains_sub_by(a, rhs_pred) || contains_sub_by(b, rhs_pred)
        }
        _ => false,
    }
}

fn is_zero(f: &Formula) -> bool {
    matches!(f, Formula::Int(0) | Formula::UInt(0))
}

/// The s20 shape: every atom (count ceiling, availability bytes, capacity
/// overflow bytes) carries the BARE end, the byte atoms as `Mul(Int(8), end)` —
/// the spelling `trust_certify::certify_vc` certifies — while the `VcKind`
/// payload keeps the unfolded `(- end 0)` so diagnostics and claim display do
/// not move.
#[test]
fn zero_start_count_is_folded_in_every_atom_but_not_in_the_payload() {
    let (count, atoms) = alloc_vc(&range_collect(int(0), false));
    assert!(
        count.starts_with("(- ") && count.ends_with(" 0)"),
        "the payload keeps the unfolded count: {count}"
    );
    // Count ceiling + capacity bytes. The 256 MiB availability byte atom that stood
    // between them was deleted with trust-ir's `ALLOC_BYTE_BUDGET`; the only byte line
    // is the object limit.
    assert_eq!(atoms.len(), 2, "count ceiling + capacity bytes: {atoms:?}");
    for atom in &atoms {
        assert!(!contains_sub_by(atom, &is_zero), "a `- 0` survived in {atom:?}");
    }
    let Formula::Ge(ceiling_lhs, ceiling_rhs) = &atoms[0] else { panic!("{:?}", atoms[0]) };
    assert!(matches!(**ceiling_lhs, Formula::Var(..)), "bare end in the ceiling: {:?}", atoms[0]);
    assert_eq!(**ceiling_rhs, Formula::Int(UNBOUNDED_ALLOC_ELEM_CEILING));
    for byte_atom in &atoms[1..] {
        let Formula::Ge(lhs, rhs) = byte_atom else { panic!("{byte_atom:?}") };
        let Formula::Mul(stride, operand) = &**lhs else { panic!("{byte_atom:?}") };
        assert_eq!(**stride, Formula::Int(8));
        assert!(matches!(**operand, Formula::Var(..)), "bare end under Mul: {byte_atom:?}");
        assert_eq!(
            **rhs,
            Formula::Int(ALLOC_CAPACITY_OVERFLOW_BYTES),
            "the object limit: {byte_atom:?}"
        );
    }
}

/// FALSE-PROOF RAIL. A non-zero LITERAL start stays in every atom: folding
/// `-268435456` away would certify `(-268435456i64..n.min(8) as i64)` — a
/// genuinely reachable 2^28-element allocation — and folding `5` away would
/// change the obligation (harmlessly larger, but still not the count).
#[test]
fn a_nonzero_literal_start_is_never_folded() {
    for start in [-268_435_456i128, -5, -1, 1, 5] {
        let (count, atoms) = alloc_vc(&range_collect(int(start), false));
        assert!(
            count.contains(&start.unsigned_abs().to_string()),
            "payload keeps {start}: {count}"
        );
        for atom in &atoms {
            assert!(
                contains_sub_by(atom, &|rhs| *rhs == Formula::Int(start)),
                "start {start} vanished from {atom:?}"
            );
        }
    }
}

/// A SYMBOLIC start (`m..n`) is the general-range residual: it stays a `Sub`
/// (not certifiable today; `ChainNode::ScaledDiff` is the follow-up).
#[test]
fn a_symbolic_start_is_never_folded() {
    let (_, atoms) = alloc_vc(&range_collect(Operand::Copy(Place::local(2)), true));
    for atom in &atoms {
        assert!(
            contains_sub_by(atom, &|rhs| matches!(rhs, Formula::Var(..))),
            "the symbolic start vanished from {atom:?}"
        );
    }
}

/// The fold itself: literal zero on the RIGHT of a TOP-LEVEL `Sub` only.
#[test]
fn fold_is_literal_zero_top_level_only() {
    let x = || Formula::Var("x".into(), trust_types::Sort::Int);
    let sub = |a: Formula, b: Formula| Formula::Sub(Box::new(a), Box::new(b));
    assert_eq!(fold_sub_literal_zero(&sub(x(), Formula::Int(0))), x());
    assert_eq!(fold_sub_literal_zero(&sub(x(), Formula::UInt(0))), x());
    for keep in [
        sub(x(), Formula::Int(-1)),
        sub(x(), Formula::Int(1)),
        sub(x(), Formula::UInt(1)),
        sub(x(), x()),
        // `0 - x` is NOT `x`.
        sub(Formula::Int(0), x()),
        // Non-recursive: the inclusive count `(end - 0) + 1` is left alone.
        Formula::Add(Box::new(sub(x(), Formula::Int(0))), Box::new(Formula::Int(1))),
        x(),
        Formula::Int(0),
    ] {
        assert_eq!(fold_sub_literal_zero(&keep), keep);
    }
    // One level only.
    let nested = sub(sub(x(), Formula::Int(0)), Formula::Int(0));
    assert_eq!(fold_sub_literal_zero(&nested), sub(x(), Formula::Int(0)));
}
