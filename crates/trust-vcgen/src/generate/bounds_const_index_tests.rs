//! Every `BoundsCheck` assert mints an obligation — including the one whose
//! index and length are both compile-time constants in range.
//!
//! Trust (#57 follow-up): this module used to pin the OPPOSITE contract. A
//! literal in-range element access was suppressed at emission on the grounds
//! that it provably cannot fire. It provably cannot fire, and that is precisely
//! why it must be published: an obligation that is never emitted is SILENT, and
//! silence is indistinguishable from success everywhere downstream — including
//! the Clean kernel, which can only re-check propositions it is handed. The
//! trust-ir spine derives the obligation from the same assert, so the
//! suppression also manufactured a producer disagreement, which is the
//! fail-closed `[spine:unchecked-obligation]` alarm.
//!
//! The tests below therefore pin: (1) the in-range literal index MINTS its VC;
//! (2) the minted violation is ARITHMETIC, not a `Bool` literal, so the phase-A
//! vacuity gate (which folds only the Boolean-literal skeleton) leaves its proof
//! authority intact — the exact failure mode the old suppression was written to
//! avoid; and (3) the three soundness twins that must keep their VC regardless.

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition,
};

use super::generate_v2_safety_vcs;

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// `fn read(arr: [f64; 4], i: usize) -> f64` whose bb0 performs the MIR
/// bounds-assert shape rustc emits for `arr[<index>]`:
///   _4 = <index def>; _5 = Len(_1); _6 = Lt(copy _4, copy _5);
///   Assert(move _6, expected: true, BoundsCheck) -> bb1
///   bb1: _0 = copy _1[_4]; return
/// `index_def`: None = the symbolic param `i` is the index; Some(k) = a
/// constant-assigned temp.
fn array_read_fn(index_def: Option<u128>) -> VerifiableFunction {
    let index_local = if index_def.is_some() { 4 } else { 2 };
    let mut bb0_stmts = Vec::new();
    if let Some(k) = index_def {
        bb0_stmts
            .push(assign(Place::local(4), Rvalue::Use(Operand::Constant(ConstValue::Uint(k, 64)))));
    }
    bb0_stmts.push(assign(Place::local(5), Rvalue::Len(Place::local(1))));
    bb0_stmts.push(assign(
        Place::local(6),
        Rvalue::BinaryOp(
            BinOp::Lt,
            Operand::Copy(Place::local(index_local)),
            Operand::Copy(Place::local(5)),
        ),
    ));
    let read_place = Place { local: 1, projections: vec![Projection::Index(index_local)] };
    VerifiableFunction {
        name: "read".to_string(),
        def_path: "test::read".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::f64_ty()), len: 4 },
                    name: Some("arr".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("i".into()),
                },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: Ty::Int { width: 64, signed: false }, name: None },
                LocalDecl { index: 5, ty: Ty::Int { width: 64, signed: false }, name: None },
                LocalDecl { index: 6, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: bb0_stmts,
                    terminator: Terminator::Assert {
                        unwind: trust_types::UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(6)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(read_place)))],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::f64_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn bounds_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_v2_safety_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .collect()
}

fn bounds_kind_count(func: &VerifiableFunction) -> usize {
    bounds_vcs(func).len()
}

/// The phase-A vacuity gate's evaluator, reproduced here so this crate can pin
/// its own emission against it without depending on `trust-router` (which
/// depends on THIS crate). It folds `Bool`/`Not`/`And`/`Or` over Boolean
/// literals ONLY; every arithmetic atom is opaque. `Some(false)` is the verdict
/// `trust_router::constant_folder::violation_formula_is_vacuously_unsat` acts
/// on — it rewrites such a row's `Proved` to `Unknown`, which under fail-closed
/// policy is a build error.
fn boolean_skeleton(formula: &Formula) -> Option<bool> {
    match formula {
        Formula::Bool(b) => Some(*b),
        Formula::Not(inner) => boolean_skeleton(inner).map(|b| !b),
        Formula::And(terms) => {
            let mut unknown = false;
            for t in terms {
                match boolean_skeleton(t) {
                    Some(false) => return Some(false),
                    None => unknown = true,
                    Some(true) => {}
                }
            }
            if unknown { None } else { Some(true) }
        }
        Formula::Or(terms) => {
            let mut unknown = false;
            for t in terms {
                match boolean_skeleton(t) {
                    Some(true) => return Some(true),
                    None => unknown = true,
                    Some(false) => {}
                }
            }
            if unknown { None } else { Some(false) }
        }
        _ => None,
    }
}

#[test]
fn literal_in_range_index_mints_the_bounds_vc() {
    // `arr[0]` on `[f64; 4]`: index 0 and Len-resolved length 4 are both
    // compile-time constants with 0 < 4. The access provably cannot panic —
    // and the obligation saying so is EMITTED, so something actually verifies
    // it. Suppressing it left the spine deriving an obligation trust-vcgen
    // never emitted, which is the `[spine:unchecked-obligation]` alarm.
    let func = array_read_fn(Some(0));
    assert_eq!(bounds_kind_count(&func), 1, "in-range literal index must MINT its bounds VC");
}

#[test]
fn the_minted_in_range_violation_survives_the_vacuity_gate() {
    // The old suppression's stated cost, pinned as a NON-event. The violation
    // built for a literal in-range index is the arithmetic core `_i >= LEN`
    // conjoined with the index def `_i = k` — an obligation that is statically
    // decidable but carries real program content, exactly like the constant
    // shift-amount check `Or([1 < 0, 1 >= 8])`. The vacuity gate folds only the
    // Boolean-literal skeleton, so it must read this formula as opaque and
    // leave the row's proof authority alone. If emission ever degenerates to a
    // bare `Bool(false)`, this fails instead of silently downgrading a3d's
    // literal-index bounds proofs to Unknown at the far end of the pipeline.
    let func = array_read_fn(Some(0));
    let vcs = bounds_vcs(&func);
    let vc = vcs.first().expect("in-range literal index mints a bounds VC");
    assert_eq!(
        boolean_skeleton(&vc.formula),
        None,
        "the in-range bounds violation must be ARITHMETIC, not a Boolean-literal skeleton \
         the vacuity gate would strip authority from: {:?}",
        vc.formula
    );
    assert!(
        vc.obligation.is_some(),
        "the minted VC must carry an authenticated ObligationRecord — without one it can \
         acquire no row-bound proof authority and would be demoted to runtime-checked"
    );
}

#[test]
fn literal_out_of_range_index_keeps_the_bounds_vc() {
    // SOUNDNESS twin: `arr[7]` on `[f64; 4]` genuinely panics — the
    // refutation must surface, never be suppressed.
    let func = array_read_fn(Some(7));
    assert_eq!(
        bounds_kind_count(&func),
        1,
        "an out-of-range literal index must KEEP its bounds VC"
    );
}

#[test]
fn symbolic_index_keeps_the_bounds_vc() {
    // SOUNDNESS twin: `arr[i]` with an unconstrained parameter index stays
    // refutable.
    let func = array_read_fn(None);
    assert_eq!(bounds_kind_count(&func), 1, "a symbolic index must KEEP its bounds VC");
}

#[test]
fn call_written_index_local_keeps_the_bounds_vc() {
    // SOUNDNESS twin: the index temp is ALSO a call destination, so its value
    // is not the scanned constant on every path. Nothing about emission may
    // depend on a whole-function constant scan agreeing — the VC is minted here
    // for the same reason it is minted everywhere else, and (unlike the
    // in-range literal above) it stays genuinely REFUTABLE, since the callee's
    // return value is unconstrained.
    let mut func = array_read_fn(Some(0));
    // Prepend a block whose call writes the index temp (_4).
    for block in &mut func.body.blocks {
        block.id = BlockId(block.id.0 + 1);
    }
    if let Terminator::Assert { target, .. } = &mut func.body.blocks[0].terminator {
        *target = BlockId(target.0 + 1);
    }
    func.body.blocks.insert(
        0,
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: trust_types::UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                callee_identity: None,
                is_foreign: false,
                func: "test::pick".to_string(),
                args: vec![],
                dest: Place::local(4),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
            },
        },
    );
    assert_eq!(bounds_kind_count(&func), 1, "a call-written index local must KEEP its bounds VC");
}
