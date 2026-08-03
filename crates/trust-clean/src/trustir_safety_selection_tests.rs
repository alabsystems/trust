// Trust: EMITTER-ANCHORED VIOLATION SELECTION (2026-07-29) — the trust-ir safety
// tier must certify THIS VC's OWN emitted violation, not the first hypothesis
// conjunct that happens to be shaped like one.
//
// This is the trust-ir relocation of `mirsem::shift_core_selection_tests` (commit
// f1e45ccb0fe), widened to every kind the tier certifies. It matters MORE here than
// there: trust-ir is the lane the cutover makes the sole proving path.
//
// The pre-fix `find_violation_leaf(&vc.formula, pred)` walked the WHOLE VC formula
// pre-order and descended into `Not` and into `Implies` hypotheses before
// conclusions. `vc.formula` is the violation WRAPPED in block-definitions, dominating
// guards, the function's `#[requires]` and parameter/local/field/slice-len type
// bounds — all of them comparisons of the same syntactic family — so the scan
// certified a hypothesis. MEASURED over the 2326 committed fixture functions,
// comparing the old first match against the emitter's own violation BY VALUE. The
// corpus emits 772 safety VCs; the 85 `ArithmeticOverflow` VCs whose op/signedness
// combination this tier does not model decline before the locator and are excluded
// from the table, so its denominator is 687:
//
//   kind    VCs   old == emitted   old DIFFERS   no emitted violation, old supplied one
//   bounds   68        13              20                  34
//   divrem   65        40               8                   0
//   neg      12        12               0                   0
//   shift   133        27             106                   0
//   signed  100        93               0                   0
//   uadd    120        89              25                   2
//   usub    189       189               0                   0
//   TOTAL   687       463             159                  36
//
// 195 of the 687 MODELED safety VCs (28% of them; 25% of the 772 the corpus emits)
// had their kernel-checked adequacy certificate read off a proposition the VC does
// not contain.
//
// Each test below FAILS on the tree it was written against and passes after, verified
// by actually reverting `trustir_safety.rs` and re-running:
//   * the first eight against f1e45ccb0fe (the pre-audit tree);
//   * the six added for the review findings against the FIRST version of the audit
//     fix — the loose scan was already gone there, so these pin the four residual
//     defects it left (a fixed sibling arity that withdrew a legitimate row, a
//     whole-formula scan still inside the condition-local definition lane, a certified
//     width with no cross-check against the VC's own kind, and two half-a-violation
//     certificates).
// `the_real_assert_lane_definition_still_resolves` is deliberately NOT in that set:
// it is the positive control that passes on both trees and would catch the definition
// lane being tightened into uselessness.

use super::*;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnOp, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition,
};

const CENSUS: &str = "fixtures/census-2026-07-06";
const LADDER_ROOT: &str = "fixtures/census-rung2-2026-07-07";
const BIT_FIELD: &str = "fixtures/census-rung2-2026-07-07/bit_field";

fn load(dir: &str, name: &str) -> VerifiableFunction {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(dir).join(name);
    // NO `Err(_) => continue`: a fixture rename must FAIL this test, not silence it.
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("fixture missing — {}: {e}", path.display()));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {name}: {e}"))
}

fn var(n: &str) -> Box<Formula> {
    Box::new(Formula::Var(n.into(), Sort::Int))
}
fn int(k: i128) -> Box<Formula> {
    Box::new(Formula::Int(k))
}

/// Trust: test-local mixed-`Or` detector — replaces the deleted production `contains_mixed_or`
/// peel (which existed only to let the arithmetic lane decline on this shape). Does `f`
/// contain an `Or` with BOTH an `And` disjunct and a non-`And` one? That is the shape
/// `v2_formula_with_path_guards` emits for a block reached by one GUARDED and one UNGUARDED
/// path. Used only to assert a fixture PREMISE (the emitter really builds a mixed `Or`), never
/// to drive the live certifier, which now authenticates a recorded obligation.
fn contains_mixed_or(f: &Formula) -> bool {
    let here = matches!(f, Formula::Or(v)
        if v.iter().any(|d| matches!(d, Formula::And(_)))
            && v.iter().any(|d| !matches!(d, Formula::And(_))));
    here
        || match f {
            Formula::And(v) | Formula::Or(v) => v.iter().any(contains_mixed_or),
            Formula::Not(a) => contains_mixed_or(a),
            Formula::Implies(a, b) => contains_mixed_or(a) || contains_mixed_or(b),
            _ => false,
        }
}

/// Every `(kind, verdict)` this tier mints for the safety VCs of `func` that match
/// `pick`, driving the REAL emitter — the same empirical grounding the tier's own
/// function-level gate rests on.
fn minted(
    func: &VerifiableFunction,
    pick: impl Fn(&VcKind) -> bool,
) -> Vec<(Option<IrSafetyVcKind>, bool)> {
    trust_vcgen::generate_vcs(func)
        .iter()
        .filter(|vc| pick(&vc.kind))
        .map(|vc| {
            let (kind, verdict) = trustir_safety_vc_adequate_kind(func, vc);
            (kind, matches!(verdict, RefinementVerdict::ProvenModulo3))
        })
        .collect()
}

fn with_pre(func: &VerifiableFunction, pre: Vec<Formula>) -> VerifiableFunction {
    let mut g = func.clone();
    g.preconditions = pre;
    g
}

/// `fn f(x: iW) -> iW { k + x }` with `k` an UNTYPED integer constant — the real MIR
/// shape behind the mixed-width kind. `operand_ty` fabricates `i64` for
/// `ConstValue::Int` (trust-vcgen/src/lib.rs:1237-1241), so the emitted kind is
/// `operand_tys = (i64, iW)` while `int_op_type` takes the thresholds from the
/// NON-constant operand — and `operand_to_formula` puts `F::Int(k)` in the wider
/// position, which is what justifies certifying at the narrower width.
fn const_add_func(k: i128, width: u32) -> VerifiableFunction {
    let t = Ty::Int { width, signed: true };
    VerifiableFunction {
        name: "f".into(),
        def_path: "crate::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: t.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: t.clone(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Constant(ConstValue::Int(k)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: t,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// A function with NO `Assert` terminator at all. Every hand-built VC below whose
/// subject is a DIRECT-position lane is checked against this: the condition-local route
/// (`violation_candidates_resolved`) needs the MIR to define an asserted condition
/// local, and there is none here, so the route contributes nothing and the test
/// measures the lane it is named for.
fn no_assert_func() -> VerifiableFunction {
    let t = Ty::Int { width: 32, signed: false };
    VerifiableFunction {
        name: "f".into(),
        def_path: "crate::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: t.clone(), name: Some("_0".into()) }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: t,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The SMT name of [`assert_cond_func`]'s condition local. A source name shaped like
/// `_<k>` is demoted to the unique per-local fallback `_<index>`
/// (`place_to_var_name`, trust-vcgen/src/lib.rs:4325-4340), so a condition local at
/// index 2 is spelled `_2` in the emitted formula whatever it is called — the same
/// spelling the real emitter uses.
const COND: &str = "_2";

/// A function whose MIR really does carry the `expected == false` assert lowering —
/// `bb0 { _2 = (<lhs> == <rhs>); assert(!_2) -> bb1 }` — so the condition-local route is
/// OPEN against it. Used by the tests whose subject is a rule INSIDE that route (the
/// sibling-definition rule, the negation width cross-check): without a real MIR binding
/// the route would decline first and the test would measure nothing.
fn assert_cond_func(lhs: &str, rhs: i128, msg: AssertMessage, ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "crate::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: ty.clone(), name: Some(lhs.into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some(COND.into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(rhs)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: Default::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// SHIFT — a precondition may not supply the certified shift width.
// ---------------------------------------------------------------------------

/// `<u8 as BitField>::get_bit` shifts by `bit` and its only shift violation is
/// `bit >= 8`. A `#[requires]`-style `Ge(_, 64)` / `Ge(_, 32)` hypothesis must never
/// mint a `ShiftOob(W64)` / `ShiftOob(W32)` adequacy certificate: that is a
/// kernel-checked claim about a width the VC does not contain, over a variable the
/// body never shifts by.
///
/// PRE-FIX (MEASURED, this exact tier): `Ge(bit,64)` -> `ShiftOob(W64) ProvenModulo3`
/// and the whole-function gate flips from `false` to `true`; `Ge(other,32)` ->
/// `ShiftOob(W32) ProvenModulo3`, likewise.
#[test]
fn a_precondition_can_never_supply_the_certified_shift_width() {
    let base = load(BIT_FIELD, "<u8 as lib__BitField>__get_bit.json");
    let want = IrSafetyVcKind::ShiftOob(IrShiftWidth::W8, false);
    for (tag, pre) in [
        ("Ge(bit,64) — the right variable, the wrong width", Formula::Ge(var("bit"), int(64))),
        ("Ge(other,32) — a variable the body never shifts by", Formula::Ge(var("other"), int(32))),
    ] {
        let hostile = with_pre(&base, vec![pre]);
        for (kind, proven) in minted(&hostile, |k| matches!(k, VcKind::ShiftOverflow { .. })) {
            assert!(
                !proven || kind == Some(want),
                "{tag}: minted {kind:?} — a hypothesis conjunct was certified in place of \
                 the emitted violation core `Ge(bit, 8)`"
            );
        }
    }
}

/// The mirror direction: with the extractor's own `Ge`-spelled parameter-domain
/// precondition sitting AHEAD of the real core in the same formula, each width must
/// still certify ITS OWN emitted shift width.
#[test]
fn bit_field_get_bit_certifies_its_own_shift_width_under_a_ge_spelled_precondition() {
    const WIDTHS: [(&str, IrShiftWidth); 12] = [
        ("i8", IrShiftWidth::W8),
        ("i16", IrShiftWidth::W16),
        ("i32", IrShiftWidth::W32),
        ("i64", IrShiftWidth::W64),
        ("i128", IrShiftWidth::W128),
        ("isize", IrShiftWidth::W64),
        ("u8", IrShiftWidth::W8),
        ("u16", IrShiftWidth::W16),
        ("u32", IrShiftWidth::W32),
        ("u64", IrShiftWidth::W64),
        ("u128", IrShiftWidth::W128),
        ("usize", IrShiftWidth::W64),
    ];
    for (ty, expected) in WIDTHS {
        let func = load(BIT_FIELD, &format!("<{ty} as lib__BitField>__get_bit.json"));
        // The fixture really does carry the `Ge`-first synthesized domain precondition
        // — if the extractor stops emitting it this test measures nothing and must say
        // so rather than pass. (`Le(0, p)`-spelled bounds never collided; the whole
        // point is that this one does.)
        assert!(
            func.preconditions.iter().any(|p| matches!(p, Formula::And(cs)
                if matches!(cs.as_slice(), [Formula::Ge(..), Formula::Le(..)]))),
            "{ty}: fixture no longer carries the `And([Ge(p,lo), Le(p,hi)])` \
             parameter-domain precondition this test exists to pin"
        );
        let got = minted(&func, |k| matches!(k, VcKind::ShiftOverflow { .. }));
        assert_eq!(
            got,
            vec![(Some(IrSafetyVcKind::ShiftOob(expected, false)), true)],
            "{ty}: the certified shift width must be this body's own emitted threshold, \
             not one read off the hypothesis side of the VC formula"
        );
    }
}

// ---------------------------------------------------------------------------
// ARITHMETIC — a DOMINATING GUARD may not supply the certified add.
// ---------------------------------------------------------------------------

/// This one needs no hostile input at all. `itoa`'s `<i16 as Sealed>::write` contains
/// several checked adds; a dominating `Assert{Overflow(Add)}` is threaded in as the
/// guard `Not(Gt(Add(_43, 2), u64::MAX))`, and the pre-order scan descended into that
/// `Not` and returned its `Gt` — a `u64` add — as the violation of a VC whose own
/// obligation is the `u8` add `Gt(Add(_63, 48), 255)`.
///
/// PRE-FIX (MEASURED): `UAddOverflow(W64) ProvenModulo3`. The certified width and BOTH
/// operands are wrong, on unmodified real-crate code.
#[test]
fn a_dominating_overflow_guard_can_never_supply_the_certified_add() {
    for ty in ["u8", "u32", "u64", "i32"] {
        let func = load(
            &format!("{CENSUS}/itoa"),
            &format!("lib__<impl lib__private__Sealed for {ty}>__write.json"),
        );
        let widths: Vec<IrUWidth> = minted(&func, |k| {
            matches!(k, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, .. })
        })
        .into_iter()
        .filter(|(_, proven)| *proven)
        .filter_map(|(k, _)| match k {
            Some(IrSafetyVcKind::UAddOverflow(w)) => Some(w),
            _ => None,
        })
        .collect();
        // MEASURED, `{ty}::write`, the 5th emitted arithmetic VC:
        //   pre-fix  -> UAddOverflow(W64)   the dominating guard's `usize` add
        //   post-fix -> UAddOverflow(W8)    this VC's OWN `digit + b'0'` add
        // The other add in the body genuinely IS 64-bit, so W64 must still appear —
        // what may not happen is the u8 obligation being certified as a u64 one.
        assert!(
            widths.contains(&IrUWidth::W8),
            "{ty}::write: no uadd VC certified UAddOverflow(W8), but the body's \
             `digit + b\'0\'` add is 8-bit — its certificate was read off the dominating \
             `Not(Gt(a+b, u64::MAX))` overflow guard instead (got {widths:?})"
        );
    }
}

// ---------------------------------------------------------------------------
// NEGATION — a constant-assignment block-def may not supply the certified width.
// ---------------------------------------------------------------------------

/// `fn neg(x: i32) -> i32 { -x }` has exactly one negation violation, `Eq(x, i32::MIN)`.
/// The pre-fix certifier used the `Eq`-DESCENDING scan, whose predicate
/// `Eq(Var, Int)` is the shape of EVERY constant-assignment block-def and of any
/// `#[requires] k == C`. `Eq(k, -128)` therefore minted `NegOverflow(W8)` and
/// `Eq(k, i64::MIN)` minted `NegOverflow(W64)` — both MEASURED — for an `i32` body.
#[test]
fn a_precondition_can_never_supply_the_certified_negation_width() {
    let i32_ty = Ty::Int { width: 32, signed: true };
    let base = VerifiableFunction {
        name: "neg".into(),
        def_path: "crate::neg".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32_ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: i32_ty.clone(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: i32_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let want = IrSafetyVcKind::NegOverflow(IrSWidth::W32);
    assert_eq!(
        minted(&base, |k| matches!(k, VcKind::NegationOverflow { .. })),
        vec![(Some(want), true)],
        "the unhostile i32 negation must certify its own width"
    );
    for (tag, pre) in [
        ("Eq(k, i8::MIN)", Formula::Eq(var("k"), int(-128))),
        ("Eq(k, i64::MIN)", Formula::Eq(var("k"), int(-9_223_372_036_854_775_808))),
    ] {
        let hostile = with_pre(&base, vec![pre]);
        for (kind, proven) in minted(&hostile, |k| matches!(k, VcKind::NegationOverflow { .. })) {
            assert!(
                !proven || kind == Some(want),
                "{tag}: minted {kind:?} for an i32 negation — a hypothesis supplied the \
                 certified width"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// BOUNDS / DIV-REM — the emitter emits these violations BARE, so a hypothesis of the
// SAME SHAPE is indistinguishable by shape and only POSITION can tell them apart.
// ---------------------------------------------------------------------------

/// Authenticated-path adapter (2026-08-01, FIELD-REQUIRED): the record's `body` IS the
/// given formula (empty wrapper list), so the arm reads it directly. A formula that is not
/// this kind's `Ge(i, len)` core declines. Tests pinning a WRAPPED body (a hypothesis fact
/// or a path-guard split) build their records explicitly.
fn bounds_vc(formula: Formula) -> VerificationCondition {
    let obligation = Some(trust_types::ObligationRecord {
        body: formula.clone(),
        wrappers: vec![],
        subject: None,
        width: None,
    });
    VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation,
    }
}

/// Authenticated bounds VC with an explicit `body`/`wrappers` split — for the tests that
/// pin a wrapped body (a signed `Or` core behind a `Ge(len,0)` hypothesis fact, or a
/// path-guard split over a shared `Ge(i,len)` core).
fn bounds_vc_recorded(rec: trust_types::ObligationRecord) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: reconstruct_obligation(&rec),
        contract_metadata: None,
        obligation: Some(rec),
    }
}

/// A SLICE-RANGE bounds VC states `start > end ∨ end > len` — a `Gt`-shaped violation
/// this tier does not model, so the honest verdict is a decline. The pre-fix scan
/// instead returned the first `Ge(var, var|int)` anywhere in the formula, which for
/// every real slice-range VC is the `conjoin_slice_len_bounds` fact `Ge(len, 0)` or the
/// extractor's parameter-domain `Ge(start, 0)`, and certified `idxOob(0, len)`.
///
/// PRE-FIX (MEASURED): `ProvenModulo3`. 34 of the corpus's 68 bounds VCs were
/// certified exactly this way.
#[test]
fn a_type_bound_can_never_supply_the_certified_bounds_check() {
    let vc = bounds_vc(Formula::And(vec![
        // `conjoin_slice_len_bounds`' own fact — a hypothesis, `Ge`-shaped.
        Formula::Ge(var("len"), int(0)),
        // the real violation: a slice-RANGE check, unmodeled by `idxOob`.
        Formula::Or(vec![
            Formula::Gt(var("start"), var("end")),
            Formula::Gt(var("end"), var("len")),
        ]),
    ]));
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &vc),
            RefinementVerdict::KernelRejected(_)
        ),
        "a slice-range bounds VC has no modeled `Ge(index, len)` violation; certifying the \
         `Ge(len, 0)` slice-length HYPOTHESIS in its place is a false certificate"
    );
}

/// The same defect in its REAL form, with no hand-built formula: `byteorder`'s
/// `read_u128` raises a slice-range bounds VC, and the pre-fix tier certified it off
/// the `Ge(buf__slice_len, 0)` hypothesis (MEASURED).
#[test]
fn real_byteorder_slice_range_bounds_vc_is_not_certified_from_a_slice_len_bound() {
    for name in [
        "<lib__BigEndian as lib__ByteOrder>__read_u128.json",
        "<lib__LittleEndian as lib__ByteOrder>__read_u128.json",
    ] {
        let func = load(&format!("{CENSUS}/byteorder"), name);
        let got = minted(&func, |k| {
            matches!(k, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
        });
        assert!(!got.is_empty(), "{name}: expected a bounds VC");
        assert!(
            got.iter().all(|(_, proven)| !proven),
            "{name}: a slice-range bounds VC was certified — its violation is \
             `start > end ∨ end > len`, which this tier does not model, so the \
             certificate can only have come from a hypothesis"
        );
    }
}

/// A precondition `z == 0` on a variable that is not the divisor must not supply the
/// certified divisor. Built as a VC whose OWN violation is outside the modeled shape,
/// so the only `Eq(var, 0)` in the formula is the hypothesis.
///
/// PRE-FIX (MEASURED): `ProvenModulo3`, certifying `divByZero(z)` for a VC about `d`.
#[test]
fn a_precondition_can_never_supply_the_certified_divisor() {
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        // `Eq(z,0)` is the `#[requires]`; the body is the opaque-divisor form
        // `v2_divisor_is_zero_formula` emits for a const-generic `N` (`Eq(N, UInt 0)`),
        // which the tier does not model.
        formula: Formula::And(vec![
            Formula::Eq(var("z"), int(0)),
            Formula::Eq(var("N"), Box::new(Formula::UInt(0))),
        ]),
        contract_metadata: None,
        obligation: None,
    };
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &vc),
            RefinementVerdict::KernelRejected(_)
        ),
        "the `Eq(z, 0)` PRECONDITION was certified as this VC's divisor-is-zero violation"
    );
}

// ---------------------------------------------------------------------------
// [REMOVED 2026-08-01] `the_emitter_pair_is_total_on_the_ladder_shift_corpus` was a PURE
// PEEL-MECHANISM coverage census: it asserted the deleted `emitted_shift_violation` locator
// yields a singleton pair for every shift VC in the ladder corpora. That locator is gone
// (production authenticates a recorded obligation), so there is no coverage left to census.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// THE SHAPE CHECK MAY NOT FIX AN ARITY — a legitimate row was being withdrawn.
// ---------------------------------------------------------------------------

/// `v2_formula_with_path_guards` FLATTENS the VC body's `And` into the guard
/// conjunction (`Formula::And(inner) => conj.extend(inner)`, safety.rs:1110-1115), so
/// on a guarded block the emitter's own `And([range(a), range(b), out_of_range])`
/// group arrives as `[guard…, range(a), range(b), out_of_range]`. Requiring the
/// siblings to be EXACTLY a 3-element `And` therefore declined a violation that IS at
/// the body position — a real capability loss, not a forgery being closed.
///
/// MEASURED over the 2326-function fixture corpus: 2 rows, both here. Both were
/// certified `UAddOverflow(W64)` PRE-EVERYTHING off exactly this node (the emitter's
/// own `Or([Lt(g+1,0), Gt(g+1,u64::MAX)])`), and the first tightening dropped them;
/// arith located 453 -> 455, certified 582 -> 584, function gate 237 -> 238.
#[test]
fn a_flattened_path_guard_may_not_cost_the_emitters_own_violation() {
    let func = load(
        &format!("{CENSUS}/arrayvec"),
        "lib__arrayvec__ArrayVec__<T, CAP>__retain__process_one.json",
    );
    // The fixture must really exercise the FLATTENED case — otherwise this test
    // measures nothing and must say so rather than pass. At least one arithmetic
    // violation has to sit at the LAST position of a conjunction WIDER than the
    // emitter's own `And([range(a), range(b), out_of_range])` triple: that is the
    // path-guard flatten, and a fixed-arity matcher misses exactly it. Checked
    // against the raw emitter output, with no help from the locator under test.
    fn widened_groups(f: &Formula, out: &mut usize) {
        if let Formula::And(v) = f
            && v.len() > 3
            && let Some(Formula::Or(d)) = v.last()
            && matches!(
                d.as_slice(),
                [Formula::Lt(l, _), Formula::Gt(r, _)]
                    if matches!(&**l, Formula::Add(..)) && l == r
            )
        {
            *out += 1;
        }
        match f {
            Formula::And(v) | Formula::Or(v) => v.iter().for_each(|x| widened_groups(x, out)),
            Formula::Not(a) => widened_groups(a, out),
            _ => {}
        }
    }
    let mut widened = 0usize;
    for vc in trust_vcgen::generate_vcs(&func) {
        if matches!(vc.kind, VcKind::ArithmeticOverflow { .. }) {
            widened_groups(&vc.formula, &mut widened);
        }
    }
    assert!(
        widened >= 2,
        "process_one no longer carries an arithmetic violation whose emitter group was \
         flattened together with a dominating guard ({widened} found); this test's \
         subject is gone"
    );
    let certified_w64 = minted(&func, |k| {
        matches!(k, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, .. })
    })
    .into_iter()
    .filter(|(k, proven)| *proven && *k == Some(IrSafetyVcKind::UAddOverflow(IrUWidth::W64)))
    .count();
    assert!(
        certified_w64 >= 2,
        "the two `Or([Lt(g+1,0), Gt(g+1,u64::MAX)])` rows must certify their OWN emitted \
         violation; a fixed sibling arity withdraws a legitimate certificate ({certified_w64} \
         certified)"
    );
    assert!(
        function_safety_vcs_faithful_via_trustir(&func),
        "process_one's function-level certificate must hold: every one of its safety VCs \
         certifies from its own emitted violation"
    );
}

// ---------------------------------------------------------------------------
// THE CONDITION-LOCAL DEFINITION LANE — residual of the same defect class.
// ---------------------------------------------------------------------------

fn bvar(n: &str) -> Box<Formula> {
    Box::new(Formula::Var(n.into(), Sort::Bool))
}

/// The assert lane makes the VC body a bare condition local `Var(_c)` and takes the
/// violation from that local's DEFINITION. The definition must be a positive, direct
/// `Eq(Var(_c), core)` CONJUNCT of the same `And` the body sits in — the shape
/// `combine_relevant_block_defs` builds (block_defs.rs:696). The scan this replaces
/// walked the WHOLE formula and descended into `Not`, into every `Or` disjunct and
/// into both sides of `Implies`, accepting any occurrence at all.
///
/// PRE-FIX (MEASURED on the tree this test lands against): each formula below returns
/// `(Some(DivByZero), ProvenModulo3)`. Neither occurrence is a definition of `_2`:
/// under a `Not` it says `_2` is NOT `z == 0`, and under an `Or` it holds on one
/// branch only. Certifying `divByZero(z)` off either is a certificate about a
/// proposition the VC does not state.
#[test]
fn only_a_direct_positive_sibling_conjunct_can_define_the_certified_core() {
    // The MIR really does bind `_2 := (z == 0)` under an `expected == false` assert, so
    // the condition-local route is open and what is on trial below is the SIBLING rule:
    // a `Not`-wrapped, an `Or`-wrapped and a non-`Bool` occurrence must each fail to
    // define `_2`, even though the honest definition exists in the MIR.
    let func =
        assert_cond_func("z", 0, AssertMessage::DivisionByZero, Ty::Int { width: 32, signed: false });
    let core = || Box::new(Formula::Eq(var("z"), int(0)));
    for (tag, formula) in [
        (
            "NEGATED equation — `_2` is defined as the COMPLEMENT of the core",
            Formula::And(vec![
                Formula::Not(Box::new(Formula::Eq(bvar(COND), core()))),
                Formula::Var(COND.into(), Sort::Bool),
            ]),
        ),
        (
            "DISJOINED equation — holds on one branch, so it defines nothing",
            Formula::And(vec![
                Formula::Or(vec![
                    Formula::Eq(bvar(COND), core()),
                    Formula::Bool(true),
                ]),
                Formula::Var(COND.into(), Sort::Bool),
            ]),
        ),
        (
            "NON-BOOLEAN body local — an integer `Var` body is not a condition \
             indirection",
            Formula::And(vec![
                Formula::Eq(var(COND), core()),
                Formula::Var(COND.into(), Sort::Int),
            ]),
        ),
    ] {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "crate::f".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        };
        assert!(
            matches!(
                trustir_safety_vc_adequate(&func, &vc),
                RefinementVerdict::KernelRejected(_)
            ),
            "{tag}: the located core came from something that is not a definition of the \
             condition local the VC body names"
        );
    }
}

/// The positive control for the tightening above: the REAL assert-lane shape — the
/// definition as a direct sibling conjunct — must still resolve, or the fix would be
/// buying its strictness with the whole lane. Driven through the real emitter on the
/// corpus function whose div-by-zero VC uses it.
#[test]
fn the_real_assert_lane_definition_still_resolves() {
    let func = load(&format!("{LADDER_ROOT}/bit_field"), "<[T] as lib__BitArray<T>>__get_bit.json");
    let got = minted(&func, |k| matches!(k, VcKind::DivisionByZero | VcKind::RemainderByZero));
    assert!(!got.is_empty(), "the fixture must still raise a div/rem VC through the assert lane");
    assert!(
        got.iter().any(|(k, proven)| *proven && *k == Some(IrSafetyVcKind::DivByZero)),
        "the assert lane's own block-def `Eq(_4, Eq(divisor, 0))` must still supply the \
         certified core (got {got:?})"
    );
}

// ---------------------------------------------------------------------------
// WIDTH CROSS-CHECKS — the emitted threshold must not be the only witness.
// ---------------------------------------------------------------------------

/// The certified width is read from the EMITTED THRESHOLD, which is right (`operand_ty`
/// fabricates `i64` for a signed constant operand) but makes the threshold a single
/// point of failure. Both headline forgeries would have been killed independently by
/// checking it against the VC's own kind. Negation is the exact case: both emitters
/// take the `INT_MIN` literal from `ty.int_width()` itself, so an `Eq(x, -128)` core
/// under `NegationOverflow { ty: i32 }` cannot be this VC's violation.
///
/// PRE-FIX (MEASURED): `(Some(NegOverflow(W8)), ProvenModulo3)` — the condition-local
/// definition lane reaches a lone `Eq(k, -128)` and the tier mints an `i8` certificate
/// for an `i32` negation.
#[test]
fn the_negation_width_must_agree_with_the_vcs_own_negated_type() {
    // The MIR binds `_2 := (k == -128)` under an `expected == false` `OverflowNeg`
    // assert, so the condition-local route RESOLVES and the decline below is the width
    // cross-check firing, not the MIR confirmation declining first.
    let func =
        assert_cond_func("k", -128, AssertMessage::OverflowNeg, Ty::Int { width: 32, signed: true });
    let vc = VerificationCondition {
        kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Eq(bvar(COND), Box::new(Formula::Eq(var("k"), int(-128)))),
            Formula::Var(COND.into(), Sort::Bool),
        ]),
        contract_metadata: None,
        obligation: None,
    };
    assert!(
        matches!(
            trustir_safety_vc_adequate(&func, &vc),
            RefinementVerdict::KernelRejected(_)
        ),
        "an `i8` INT_MIN threshold cannot be the violation of an `i32` negation VC"
    );
}

fn urange(name: &str, lo: i128, hi: i128) -> Formula {
    Formula::And(vec![
        Formula::Le(int(lo), var(name)),
        Formula::Le(var(name), int(hi)),
    ])
}

fn uadd_or(lo_bound: i128, max: i128) -> Formula {
    Formula::Or(vec![
        Formula::Lt(Box::new(Formula::Add(var("a"), var("b"))), int(lo_bound)),
        Formula::Gt(Box::new(Formula::Add(var("a"), var("b"))), int(max)),
    ])
}

fn uadd_vc(a_lo: i128, max: i128, tys: (Ty, Ty)) -> VerificationCondition {
    // Authenticated-path conversion (2026-08-01, FIELD-REQUIRED): the record's `body` is the
    // `Or` out-of-range core; the operand ranges are demoted to a `ConjoinFactsLast` wrapper,
    // exactly as the emitter records them. `reconstruct_obligation == And([range(a),
    // range(b), oor])`, so the formula is unchanged and the vacuity side condition is read off
    // the record's own facts.
    let rec = trust_types::ObligationRecord {
        body: uadd_or(0, max),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![urange("a", a_lo, max), urange("b", 0, max)],
        }],
        subject: None,
        width: None,
    };
    VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, operand_tys: tys },
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: reconstruct_obligation(&rec),
        contract_metadata: None,
        obligation: Some(rec),
    }
}

/// The arithmetic analogue of the negation cross-check. This is the itoa forgery in
/// hand-built form: a `u64`-threshold add group under `operand_tys = (u8, u8)`.
///
/// PRE-FIX (MEASURED): `(Some(UAddOverflow(W64)), ProvenModulo3)` — a kernel-checked
/// 64-bit claim on an 8-bit obligation. The check is "the recovered width is a width
/// the kind MENTIONS", not "both operand types equal it", because `int_op_type`
/// (type_ranges.rs:540) legitimately takes the width from the non-constant operand:
/// the `100i8 + x` row (the third case below) must keep certifying.
#[test]
fn the_arithmetic_width_must_be_one_the_vcs_own_operand_types_mention() {
    let u8t = Ty::Int { width: 8, signed: false };
    let u64t = Ty::Int { width: 64, signed: false };
    let forged = uadd_vc(0, u64::MAX as i128, (u8t.clone(), u8t));
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &forged),
            RefinementVerdict::KernelRejected(_)
        ),
        "a `u64` threshold cannot be the violation of an `ArithmeticOverflow {{ operand_tys: \
         (u8, u8) }}` VC"
    );
    // POSITIVE CONTROL 1: the same shape with an honest (u64, u64) kind still certifies.
    let honest = uadd_vc(0, u64::MAX as i128, (u64t.clone(), u64t));
    assert_eq!(
        trustir_safety_vc_adequate_kind(&no_assert_func(), &honest).0,
        Some(IrSafetyVcKind::UAddOverflow(IrUWidth::W64)),
        "the honest u64 row must be unaffected"
    );

    // The SIGNED lane is where the fabricated-`i64` constant actually lands (a mixed
    // signed/unsigned pair is not a Rust binop and routes to `not modeled`).
    let signed_vc = |tys: (Ty, Ty), min: i128, max: i128| {
        // Authenticated-path conversion: body = the `Or` core, operand ranges demoted to a
        // `ConjoinFactsLast` wrapper; `reconstruct_obligation` reproduces the And formula.
        let rec = trust_types::ObligationRecord {
            body: Formula::Or(vec![
                Formula::Lt(Box::new(Formula::Add(var("a"), var("b"))), int(min)),
                Formula::Gt(Box::new(Formula::Add(var("a"), var("b"))), int(max)),
            ]),
            wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
                facts: vec![urange("a", min, max), urange("b", min, max)],
            }],
            subject: None,
            width: None,
        };
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, operand_tys: tys },
            function: "crate::f".into(),
            location: SourceSpan::default(),
            formula: reconstruct_obligation(&rec),
            contract_metadata: None,
            obligation: Some(rec),
        }
    };
    let i8t = Ty::Int { width: 8, signed: true };
    let i64t = Ty::Int { width: 64, signed: true };
    // FORGED: an `i64` (MIN,MAX) pair under an `(i8, i8)` kind.
    assert!(
        matches!(
            trustir_safety_vc_adequate(
                &no_assert_func(),
                &signed_vc((i8t.clone(), i8t.clone()), i64::MIN as i128, i64::MAX as i128)
            ),
            RefinementVerdict::KernelRejected(_)
        ),
        "an `i64` (MIN,MAX) pair cannot be the violation of an `(i8, i8)` overflow VC"
    );
    // POSITIVE CONTROL 2: `100i8 + x` — `operand_ty` fabricates `i64` for the signed
    // constant, so only the SECOND operand type carries the emitted `i8` width. A
    // "both must equal" check would withdraw this legitimate row.
    //
    // Trust: THIS CONTROL IS NOW DRIVEN THROUGH THE REAL EMITTER (2026-07-31, round-5
    // defect [2]). It used to hand-build `signed_vc((i64, i8), -128, 127)`, whose
    // computed sum is `Add(Var a, Var b)` — TWO BARE VARIABLES. That is not the shape
    // `100i8 + x` emits and never was: `operand_to_formula` renders `ConstValue::Int(n)`
    // as `F::Int(n)`, so the real row's wider (i64) position holds `Int(100)`. The
    // fiction mattered, because the constant in the wider position is the ONLY thing
    // that justifies certifying at the NARROWER width — and a control that omitted it
    // was being read as evidence that a mixed-width kind may certify at either width
    // with nothing narrowing anything (`the_mixed_width_signed_kind_may_not_pick_a_width`
    // is the forgery that lets through). Verified by printing the emitted VC on this
    // tree: `operand_tys = (Int{64,signed}, Int{8,signed})` with body
    // `Or([Lt(Add(Int(100), Var x), Int(-128)), Gt(Add(Int(100), Var x), Int(127))])`.
    let real = const_add_func(100, 8);
    assert_eq!(
        minted(&real, |k| matches!(k, VcKind::ArithmeticOverflow { .. })),
        vec![(Some(IrSafetyVcKind::SignedOverflow(IrSignedOp::Add, IrSWidth::W8)), true)],
        "the `100i8 + x` spelling (a constant operand whose type was fabricated as i64) \
         must keep certifying its own emitted width"
    );
    // …and the hand-built two-bare-`Var` shape, which is what the mixed-width kind can
    // certify at EITHER width if nothing checks the narrowing, must now decline.
    assert!(
        matches!(
            trustir_safety_vc_adequate(
                &no_assert_func(),
                &signed_vc((i64t, i8t), -128, 127)
            ),
            RefinementVerdict::KernelRejected(_)
        ),
        "a mixed-width `(i64, i8)` kind over TWO BARE `Var` operands has no constant \
         justifying the narrowing to `i8`, so it may not certify at `i8`"
    );
}

// ---------------------------------------------------------------------------
// PARTIAL ADEQUACY — a certificate may not cover HALF the located violation.
// ---------------------------------------------------------------------------

/// The uadd certificate grounds only the `Gt(a+b, MAX)` disjunct of the emitted
/// `Or([Lt(a+b,0), Gt(a+b,MAX)])`. That is sound exactly when the discarded disjunct is
/// unsatisfiable under the conjoined ranges — which holds because the UNSIGNED operand
/// ranges pin both operands to `≥ 0`. Nothing checked that; it was argued in a comment.
///
/// PRE-FIX (MEASURED): the formula below, whose `a` range starts at `-128`, is
/// certified `(Some(UAddOverflow(W8)), ProvenModulo3)` — but `a = -128, b = 0` makes
/// the VC's own `Lt(a+b, 0)` disjunct TRUE while `uaddOverflows a b` is false, so the
/// certificate covers strictly less than the violation it claims to be about.
#[test]
fn the_discarded_uadd_disjunct_must_be_provably_vacuous() {
    let u8t = Ty::Int { width: 8, signed: false };
    let leaky = uadd_vc(-128, 255, (u8t.clone(), u8t.clone()));
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &leaky),
            RefinementVerdict::KernelRejected(_)
        ),
        "with `a` ranged from -128 the `Lt(a+b, 0)` disjunct is satisfiable, so a \
         `Gt`-only certificate is a claim about half the emitted violation"
    );
    // POSITIVE CONTROL: the real unsigned spelling (`0 <= a`) still certifies.
    let sound = uadd_vc(0, 255, (u8t.clone(), u8t.clone()));
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &sound),
            RefinementVerdict::ProvenModulo3
        ),
        "the genuine unsigned row must be unaffected"
    );

    // AND IT MUST HOLD ACROSS EVERY PATH. Under the authenticated design the operand ranges
    // are the INNERMOST `ConjoinFactsLast` wrapper, SHARED by every `PathGuardOr` disjunct —
    // so per-path range divergence (the peel-era hazard, path 1 pinning `0 <= a` and path 2
    // not) is not even RECORDABLE: one shared fact set governs all paths. The property is
    // therefore stated over the shared facts: a multi-path record whose shared operand range
    // does NOT pin `a ≥ 0` declines on every path, and the sound one certifies.
    let split_vc = |a_lo: i128| {
        let rec = trust_types::ObligationRecord {
            body: uadd_or(0, 255),
            wrappers: vec![
                trust_types::ObligationWrapper::ConjoinFactsLast {
                    facts: vec![urange("a", a_lo, 255), urange("b", 0, 255)],
                },
                trust_types::ObligationWrapper::PathGuardOr {
                    paths: vec![
                        trust_types::PathGuardTerm::Guarded {
                            guards: vec![Formula::Var("g1".into(), Sort::Bool)],
                        },
                        trust_types::PathGuardTerm::Guarded {
                            guards: vec![Formula::Var("g2".into(), Sort::Bool)],
                        },
                    ],
                },
            ],
            subject: None,
            width: None,
        };
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: trust_types::BinOp::Add,
                operand_tys: (u8t.clone(), u8t.clone()),
            },
            function: "crate::f".into(),
            location: SourceSpan::default(),
            formula: reconstruct_obligation(&rec),
            contract_metadata: None,
            obligation: Some(rec),
        }
    };
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &split_vc(-128)),
            RefinementVerdict::KernelRejected(_)
        ),
        "a multi-path record whose SHARED operand range does not pin `a ≥ 0` must decline on \
         every path — the vacuity is read off the record's own facts"
    );
    // ...and the all-paths-sound version of the same split still certifies.
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &split_vc(0)),
            RefinementVerdict::ProvenModulo3
        ),
        "the multi-path split over sound shared ranges must still certify"
    );
    let _ = u8t;
}

/// The other member of the same pattern, closed the other way. A SIGNED index makes
/// `v2_build_bounds_assert_vc` (checked_vcs.rs:257-262) emit
/// `Or([Lt(i,0), Ge(i,len)])`, and `idxOob` models `i >= len` only — there is no
/// vacuity argument for the `Lt(i,0)` half, so the honest verdict is a decline.
///
/// PRE-FIX (MEASURED): `ProvenModulo3` — the tier descended into the `Or` and
/// certified `idxOob(len, i)`, a kernel certificate silent about the half of the
/// violation that says the index is negative.
#[test]
fn a_signed_index_bounds_violation_is_declined_not_half_certified() {
    // Authenticated: body = the SIGNED `Or([Lt(i,0), Ge(i,len)])` core, the `Ge(len,0)`
    // hypothesis demoted to a `ConjoinFactsLast` fact. It declines because the recorded body
    // is the signed form, which `idxOob` does not model — not because it is not a bounds
    // shape at all.
    let vc = bounds_vc_recorded(trust_types::ObligationRecord {
        body: Formula::Or(vec![
            Formula::Lt(var("i"), int(0)),
            Formula::Ge(var("i"), var("len")),
        ]),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![Formula::Ge(var("len"), int(0))],
        }],
        subject: None,
        width: None,
    });
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &vc),
            RefinementVerdict::KernelRejected(_)
        ),
        "certifying `idxOob(len, i)` for `i < 0 OR i >= len` covers half the violation"
    );
    // POSITIVE CONTROL: a multi-path guard split over the SAME shared `Ge(i,len)` core (a
    // `PathGuardOr` wrapper) must still certify — the body is the recorded unsigned core.
    let split = bounds_vc_recorded(trust_types::ObligationRecord {
        body: Formula::Ge(var("i"), var("len")),
        wrappers: vec![trust_types::ObligationWrapper::PathGuardOr {
            paths: vec![
                trust_types::PathGuardTerm::Guarded {
                    guards: vec![Formula::Var("g1".into(), Sort::Bool)],
                },
                trust_types::PathGuardTerm::Guarded {
                    guards: vec![Formula::Var("g2".into(), Sort::Bool)],
                },
            ],
        }],
        subject: None,
        width: None,
    });
    assert!(
        matches!(
            trustir_safety_vc_adequate(&no_assert_func(), &split),
            RefinementVerdict::ProvenModulo3
        ),
        "the multi-path guard `Or` (every disjunct an `And`, the body last in each) must \
         still locate the repeated violation"
    );
}

// ---------------------------------------------------------------------------
// A DIRECT SIBLING IS NOT A BLOCK-DEF — a `#[requires]` may not define the
// assert's condition local.
// ---------------------------------------------------------------------------

/// `fn f(ok: bool, k: i32, other: i32) -> i32 { assert!(!ok); -k }`, driven through the
/// REAL `trust_vcgen::generate_vcs`. `ok` is a PARAMETER: no statement defines it, so
/// `combine_relevant_block_defs` returns the assert body BARE
/// (`if keep_rev.is_empty() { return formula; }`, block_defs.rs:693-695) and
/// `versioned::conjoin` (versioned.rs:62-68) makes the `#[requires]` a DIRECT SIBLING
/// of the `Var(ok, Bool)` body — structurally indistinguishable from the block
/// definition the condition-local route is looking for.
///
/// PRE-FIX (MEASURED through the real emitter on this tree): emitted formula
/// `And([Eq(ok, Eq(other, -2147483648)), Var(ok, Bool)])`, verdict
/// `(Some(NegOverflow(W32)), ProvenModulo3)` and
/// `function_safety_vcs_faithful_via_trustir == true` — a kernel-checked certificate
/// about `other`, which the body never negates. The width cross-check is no defense:
/// the forger picks the threshold that matches. The div and rem twins forge the same
/// way off `Eq(z, 0)`.
///
/// The MIR confirmation closes it: `mir_assert_condition_core` requires the assert's own
/// block to CONTAIN the defining statement, and a contract cannot manufacture one.
#[test]
fn a_precondition_can_never_define_the_assert_condition_local_the_mir_does_not_define() {
    let i32_ty = Ty::Int { width: 32, signed: true };
    // `bb0 { assert(!ok) -> bb1 }  bb1 { _0 = -k }` — `ok` is a bool PARAMETER.
    let base = |msg: AssertMessage, body: Rvalue| VerifiableFunction {
        name: "f".into(),
        def_path: "crate::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32_ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("ok".into()) },
                LocalDecl { index: 2, ty: i32_ty.clone(), name: Some("k".into()) },
                LocalDecl { index: 3, ty: i32_ty.clone(), name: Some("other".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(1)),
                        expected: false,
                        msg,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: Default::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: body,
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: i32_ty.clone(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let binds = |rhs: Formula| Formula::Eq(bvar("ok"), Box::new(rhs));
    // The VC on trial is the ASSERT's own obligation, whose body is the bare condition
    // local. The body statement in bb1 raises its own, HONEST obligation alongside it —
    // that one must keep certifying, so the test is about the forged VC specifically.
    let is_forged = |vc: &VerificationCondition| {
        matches!(&vc.formula, Formula::And(v)
            if matches!(v.last(), Some(Formula::Var(n, Sort::Bool)) if n == "ok"))
    };
    let check = |f: &VerifiableFunction, pick: &dyn Fn(&VcKind) -> bool, tag: &str| {
        let vcs = trust_vcgen::generate_vcs(f);
        // The forgery's own precondition must really reach a VC as a direct sibling of
        // the bare `Var(ok)` body — otherwise this test measures nothing and must say so.
        let forged: Vec<_> = vcs
            .iter()
            .filter(|vc| pick(&vc.kind) && is_forged(vc))
            .filter(|vc| matches!(&vc.formula, Formula::And(v)
                if v.iter().any(|c| matches!(c, Formula::Eq(l, _)
                    if matches!(&**l, Formula::Var(n, _) if n == "ok")))))
            .collect();
        assert!(
            !forged.is_empty(),
            "{tag}: the emitter no longer puts the precondition beside a bare `Var(ok)` \
             assert body; this test's subject is gone"
        );
        for vc in forged {
            let (kind, verdict) = trustir_safety_vc_adequate_kind(f, vc);
            assert!(
                matches!(verdict, RefinementVerdict::KernelRejected(_)),
                "{tag}: a `#[requires]` bound the assert's condition local and minted \
                 {kind:?} off it — the certified core is over a variable this obligation \
                 is not about"
            );
        }
    };

    // (a) NEGATION — `#[requires] ok == (other == i32::MIN)` over a variable the body
    //     never negates.
    let neg = with_pre(
        &base(
            AssertMessage::OverflowNeg,
            Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(2))),
        ),
        vec![binds(Formula::Eq(var("other"), int(-2_147_483_648)))],
    );
    check(&neg, &|k| matches!(k, VcKind::NegationOverflow { .. }), "neg");
    assert!(
        !function_safety_vcs_faithful_via_trustir(&neg),
        "the function-level gate must not pass on a certificate read off a precondition"
    );

    // (b) DIV / REM — the same construction off `Eq(z, 0)`, over a variable that is not
    //     the divisor.
    for (msg, op, tag) in [
        (AssertMessage::DivisionByZero, BinOp::Div, "div"),
        (AssertMessage::RemainderByZero, BinOp::Rem, "rem"),
    ] {
        let f = with_pre(
            &base(
                msg,
                Rvalue::BinaryOp(
                    op,
                    Operand::Copy(Place::local(2)),
                    Operand::Copy(Place::local(3)),
                ),
            ),
            vec![binds(Formula::Eq(var("z"), int(0)))],
        );
        check(&f, &|k| matches!(k, VcKind::DivisionByZero | VcKind::RemainderByZero), tag);
    }
}

/// The positive control the fix must not break, stated over the ROUTE rather than one
/// fixture: a function whose MIR genuinely binds the assert's condition local still
/// resolves its core through it. (`the_real_assert_lane_definition_still_resolves` is
/// the same property on real extracted MIR.)
#[test]
fn a_mir_bound_assert_condition_local_still_supplies_the_certified_core() {
    let func =
        assert_cond_func("d", 0, AssertMessage::DivisionByZero, Ty::Int { width: 32, signed: false });
    // Authenticated: the body is the bare assert-condition local `Var(COND)`; the block
    // definition `Eq(COND, Eq(d, 0))` is a demoted `ConjoinFactsLast` fact. The arm reads
    // the body, sees it is not the core, and resolves it through the MIR-confirmed binding.
    let rec = trust_types::ObligationRecord {
        body: Formula::Var(COND.into(), Sort::Bool),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![Formula::Eq(bvar(COND), Box::new(Formula::Eq(var("d"), int(0))))],
        }],
        subject: None,
        width: None,
    };
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: reconstruct_obligation(&rec),
        contract_metadata: None,
        obligation: Some(rec),
    };
    assert_eq!(
        trustir_safety_vc_adequate_kind(&func, &vc).0,
        Some(IrSafetyVcKind::DivByZero),
        "the MIR-confirmed condition-local route must still certify its own core"
    );
}

// ---------------------------------------------------------------------------
// [REMOVED 2026-08-01] Two PURE PEEL-MECHANISM tests exercised the deleted candidate
// producer directly and are gone with it:
//   * `a_side_condition_over_zero_sibling_sets_must_not_pass` pinned
//     `LocatedViolation::all_siblings`' fail-closed-on-empty behaviour;
//   * `the_body_position_discriminator_is_enforced_where_it_is_documented` pinned
//     `candidate_at_body_position` / `violation_candidates`' body-position invariant.
// Production authenticates a recorded obligation (`record_pins_nonneg` reads the record's
// own `ConjoinFactsLast` facts) instead of reading a side condition off guessed siblings, so
// these types and the invariants they pinned no longer exist. The surviving vacuity property
// is pinned against the LIVE certifier by
// `a_path_with_no_operand_ranges_must_fail_the_uadd_vacuity_check_not_drop_out` and
// `a_mixed_or_hides_an_occurrence_from_the_uadd_universal_and_must_decline`.
// ---------------------------------------------------------------------------

// ===========================================================================
// ROUND 4 (2026-07-30) — the three defects the round-4 adversarial verify minted
// against the round-3 repair. Each test below was falsified by reverting its fix in
// place and observing the mint; the observed pre-fix verdict is recorded per test.
// `a_mixed_path_guard_or_is_emitter_reachable_through_an_unwind_edge` is the exception
// and says so: it pins a FACT that a retracted comment declared impossible, so there is
// no "pre-fix" verdict for it — only a claim it refutes.
// ===========================================================================

// ---------------------------------------------------------------------------
// NEGATION — the certified variable must be the one the emitter negated.
// ---------------------------------------------------------------------------

/// `bb0 { <cond> = (<subject> == <threshold>); assert(!<cond>) -> bb1 }`,
/// `bb1 { _0 = -<negated> }` — the real `OverflowNeg` assert lowering
/// (`safety.rs:177-178`), with the compared variable and the negated variable chosen
/// independently. `subject_local` and `neg_local` are local indices into the fixed
/// table `[_0: i32, x: subject_ty, y: i32]`.
fn neg_assert_func(subject_local: usize, subject_ty: Ty, neg_local: usize) -> VerifiableFunction {
    let i32t = Ty::Int { width: 32, signed: true };
    VerifiableFunction {
        name: "f".into(),
        def_path: "crate::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32t.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: subject_ty, name: Some("x".into()) },
                LocalDecl { index: 2, ty: i32t.clone(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(subject_local)),
                            Operand::Constant(ConstValue::Int(-2_147_483_648)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: false,
                        msg: AssertMessage::OverflowNeg,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: Default::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(neg_local))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: i32t,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// ROUND-4 DEFECT [2]. A dominating `assert!(!(x == i32::MIN))` over a negation of an
/// UNRELATED `y` mints a negation-overflow certificate ABOUT `x`. Nothing is hostile
/// here — no contract, no hand-built formula; the whole thing is driven through
/// `trust_vcgen::generate_vcs`, and the comparison the certificate is read off is a
/// genuine, MIR-confirmed defining statement of the assert's own condition local. It is
/// simply a statement about a variable the obligation is not about: `y`, the operand
/// actually negated, appears NOWHERE in the VC formula or in the certified proposition.
///
/// PRE-FIX (MEASURED, by reverting the `via_condition_local` block in place and running
/// each subject type on its own): `Some(NegOverflow(W32))` with `ProvenModulo3` for the
/// i32 subject, and the SAME `Some(NegOverflow(W32))` with `ProvenModulo3` for the i8
/// subject — a kernel-checked 32-bit negation-overflow claim about an `i8`, a type that
/// cannot hold −2³¹.
#[test]
fn a_dominating_assert_over_an_unrelated_variable_can_never_certify_a_negation() {
    let i32t = Ty::Int { width: 32, signed: true };
    let i8t = Ty::Int { width: 8, signed: true };
    for (tag, subject_ty) in
        [("i32 subject", i32t.clone()), ("i8 subject — a 32-bit claim about an i8", i8t)]
    {
        // `x` (local 1) is compared; `y` (local 2) is negated.
        let func = neg_assert_func(1, subject_ty, 2);
        let got = minted(&func, |k| matches!(k, VcKind::NegationOverflow { .. }));
        assert!(
            !got.is_empty(),
            "{tag}: the emitter no longer raises a `NegationOverflow` VC for the \
             `OverflowNeg` assert lowering; this test's subject is gone"
        );
        for (kind, proven) in &got {
            assert!(
                !proven,
                "{tag}: minted {kind:?} for a negation of `y` off a comparison of `x` — the \
                 certified proposition is about a variable the obligation never negates"
            );
        }
        assert!(
            !function_safety_vcs_faithful_via_trustir(&func),
            "{tag}: the function-level gate must not pass either"
        );
    }
}

/// The positive control the fix must not buy its strictness with: when the assert
/// compares THE NEGATED OPERAND — the honest `if x == i32::MIN { panic } ; -x` lowering
/// — the assert-condition route must still certify. Without this, the fix could have
/// closed the hole by disabling the lane.
#[test]
fn the_honest_assert_negation_lowering_still_certifies_its_own_subject() {
    let i32t = Ty::Int { width: 32, signed: true };
    // `y` (local 2) is both compared and negated.
    let func = neg_assert_func(2, i32t, 2);
    let got = minted(&func, |k| matches!(k, VcKind::NegationOverflow { .. }));
    assert!(
        got.contains(&(Some(IrSafetyVcKind::NegOverflow(IrSWidth::W32)), true)),
        "the honest assert-negation lowering must still certify `negOverflowsI32` for its \
         own negated operand (got {got:?})"
    );
}

/// The `abs` producer is the THIRD `NegationOverflow` emitter and has no negation in its
/// MIR at all (`signed_abs_panic_body`, unwrap_panic.rs:138-151). Its rows are what a
/// blanket "the certified variable must be a negated operand" rule withdrew — MEASURED:
/// 5 of the corpus's 12 certified negation rows, all `abs`. This pins them.
#[test]
fn the_signed_abs_negation_lane_still_certifies() {
    let func = load(
        "fixtures/mass-harvest-2026-07-17/int-preds/dumps",
        "trust-mir-63bc8917efe430b4-27aa733b96bd85eb.json",
    );
    let got = minted(&func, |k| matches!(k, VcKind::NegationOverflow { .. }));
    assert!(
        got.contains(&(Some(IrSafetyVcKind::NegOverflow(IrSWidth::W8)), true)),
        "`w_i8_abs`'s `core::num::<impl i8>::abs` panic obligation must still certify \
         `negOverflowsI8` (got {got:?}) — it has no `Rvalue::UnaryOp(Neg, ..)` anywhere"
    );
}

// ---------------------------------------------------------------------------
// UADD VACUITY — the universal must range over EVERY occurrence.
// ---------------------------------------------------------------------------

/// A two-path guard split in which only the FIRST path carries the emitter's unsigned
/// operand ranges. The `Gt`-only certificate is sound exactly when `Lt(a+b, 0)` is
/// unsatisfiable beside it, and on the second path it is not: `a = −1, b = 0` satisfies
/// the emitted obligation's second disjunct while the certificate says nothing about it.
///
/// ROUND-4 DEFECT [3]. The occurrence with no ranges did not FAIL the vacuity universal
/// — it was excluded from the set the universal ranged over, because
/// `emitted_arith_violation_located` pre-filtered on the very predicate being checked.
///
/// PRE-FIX (MEASURED, by restoring the range pair to the locator's `filter`):
///   `Some(UAddOverflow(W8))` / `ProvenModulo3`.
#[test]
fn a_path_with_no_operand_ranges_must_fail_the_uadd_vacuity_check_not_drop_out() {
    let u8t = Ty::Int { width: 8, signed: false };
    let guard = |g: &str| Formula::Var(g.into(), Sort::Bool);
    let vc = |rec: trust_types::ObligationRecord| VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (u8t.clone(), u8t.clone()),
        },
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: reconstruct_obligation(&rec),
        contract_metadata: None,
        obligation: Some(rec),
    };
    // Trust: AUTHENTICATED-PATH CONVERSION (2026-08-01). The formula is byte-IDENTICAL to
    // the peel-era `Or([And([g1, range(a), range(b), oor]), And([g2, oor])])`, but now it is
    // a faithful `reconstruct_obligation`: the ranges are recorded INSIDE the first path's
    // guards, NOT in a shared `ConjoinFactsLast`. `record_pins_nonneg` reads only the
    // `ConjoinFactsLast` wrappers (where the emitter demotes the shared ranges), so ranges
    // smuggled into a single path's guards do NOT satisfy the vacuity — the split declines.
    let forged = vc(trust_types::ObligationRecord {
        body: uadd_or(0, 255),
        wrappers: vec![trust_types::ObligationWrapper::PathGuardOr {
            paths: vec![
                trust_types::PathGuardTerm::Guarded {
                    guards: vec![guard("g1"), urange("a", 0, 255), urange("b", 0, 255)],
                },
                trust_types::PathGuardTerm::Guarded { guards: vec![guard("g2")] },
            ],
        }],
        subject: None,
        width: None,
    });
    let got = trustir_safety_vc_adequate_kind(&no_assert_func(), &forged);
    assert!(
        matches!(got.1, RefinementVerdict::KernelRejected(_)),
        "operand ranges recorded in ONE path's guards, not the shared `ConjoinFactsLast`, \
         must FAIL the vacuity side condition — minted {:?}",
        got.0
    );
    // POSITIVE CONTROL: the ranges recorded in the SHARED `ConjoinFactsLast` (the emitter's
    // own placement), a `PathGuardOr` outside them, still certifies.
    let honest = vc(trust_types::ObligationRecord {
        body: uadd_or(0, 255),
        wrappers: vec![
            trust_types::ObligationWrapper::ConjoinFactsLast {
                facts: vec![urange("a", 0, 255), urange("b", 0, 255)],
            },
            trust_types::ObligationWrapper::PathGuardOr {
                paths: vec![
                    trust_types::PathGuardTerm::Guarded { guards: vec![guard("g1")] },
                    trust_types::PathGuardTerm::Guarded { guards: vec![guard("g2")] },
                ],
            },
        ],
        subject: None,
        width: None,
    });
    assert_eq!(
        trustir_safety_vc_adequate_kind(&no_assert_func(), &honest).0,
        Some(IrSafetyVcKind::UAddOverflow(IrUWidth::W8)),
        "the honest two-path split with SHARED recorded ranges must be unaffected"
    );
}

/// The other half of the same defect, migrated to the AUTHENTICATED path (2026-08-01). A
/// mixed path-guard `Or` for a block reached by one GUARDED and one UNGUARDED (empty-guard)
/// path — `Or([And([g1, range(a), range(b), oor]), oor])` — is recorded FAITHFULLY as a
/// `PathGuardOr` with a `Guarded` first path carrying the operand ranges and a `Raw` (bare)
/// second path; `reconstruct_obligation` reproduces it bit-for-bit, so the record
/// authenticates. The ranges live in a PATH GUARD, not the shared `ConjoinFactsLast` the
/// vacuity check reads (`record_pins_nonneg`), so the discarded `Lt(a+b,0)` half is not
/// provably vacuous and the lane must decline: `a = −1, b = 0` satisfies the bare disjunct's
/// obligation while the `Gt`-half certificate says nothing about it.
///
/// PRE-FIX (peel era, MEASURED by removing the `contains_mixed_or` decline):
///   `Some(UAddOverflow(W8))` / `ProvenModulo3`.
#[test]
fn a_mixed_or_hides_an_occurrence_from_the_uadd_universal_and_must_decline() {
    let u8t = Ty::Int { width: 8, signed: false };
    let guard = |g: &str| Formula::Var(g.into(), Sort::Bool);
    let forged = {
        let rec = trust_types::ObligationRecord {
            body: uadd_or(0, 255),
            wrappers: vec![trust_types::ObligationWrapper::PathGuardOr {
                paths: vec![
                    trust_types::PathGuardTerm::Guarded {
                        guards: vec![guard("g1"), urange("a", 0, 255), urange("b", 0, 255)],
                    },
                    trust_types::PathGuardTerm::Raw,
                ],
            }],
            subject: None,
            width: None,
        };
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (u8t.clone(), u8t.clone()),
            },
            function: "crate::f".into(),
            location: SourceSpan::default(),
            formula: reconstruct_obligation(&rec),
            contract_metadata: None,
            obligation: Some(rec),
        }
    };
    assert!(contains_mixed_or(&forged.formula), "the test subject must BE a mixed `Or`");
    let got = trustir_safety_vc_adequate_kind(&no_assert_func(), &forged);
    assert!(
        matches!(got.1, RefinementVerdict::KernelRejected(_)),
        "a mixed `Or` whose bare disjunct carries the operand ranges only inside one path's \
         guards hides them from the vacuity check, so the arithmetic lane must decline — \
         minted {:?}",
        got.0
    );
    // POSITIVE CONTROL: the emitter's own recorded shape (the SAME `oor` body, ranges demoted
    // to the SHARED `ConjoinFactsLast`) certifies — so the decline above is the hidden-range
    // vacuity failure, not an unrecognized body or a failed authentication.
    assert_eq!(
        trustir_safety_vc_adequate_kind(&no_assert_func(), &uadd_vc(0, 255, (u8t.clone(), u8t)))
            .0,
        Some(IrSafetyVcKind::UAddOverflow(IrUWidth::W8)),
        "the honest recorded shape with SHARED operand ranges must still certify"
    );
}

// ---------------------------------------------------------------------------
// THE RETRACTED CLAIM — a mixed path-guard `Or` IS emitter-reachable.
// ---------------------------------------------------------------------------

/// ROUND-4 DEFECT [8]. `violation_candidates`' doc block used to argue that a mixed `Or`
/// cannot be emitted, because `v2_build_path_guard_map` "pushes a guard on EVERY edge it
/// follows (safety.rs:1047), so only `bb0` can receive an empty path". This is the
/// counterexample, driven through the real emitter: `safety.rs:1051-1053` threads the
/// guard list UNCHANGED along `Terminator::unguarded_successors`, which for a `Drop`
/// returns BOTH its target and its `unwind_cleanup_target` (model.rs:6882-6900 with
/// :6872-6879). So `bb2` below inherits `bb0`'s EMPTY guard list, and `bb3` is reached
/// by one GUARDED path (`bb1`'s `SwitchInt` edge, a `discovered_clauses` edge that
/// pushes a `SwitchIntMatch` guard) and one UNGUARDED one (`bb2`'s bare `Goto`) — so its
/// VC body, a bare `Not(Var(_3))` with no block definition to conjoin, is spliced into
/// an `Or` with one `And([g, body])` disjunct and one bare `body` disjunct.
///
/// This test pins the FACT, not a verdict: no impossibility argument may be re-derived
/// at that site. It is also the reachability evidence for
/// [`a_mixed_or_hides_an_occurrence_from_the_uadd_universal_and_must_decline`]'s decline
/// being a real guard rather than a shape that cannot occur.
#[test]
fn a_mixed_path_guard_or_is_emitter_reachable_through_an_unwind_edge() {
    let u64t = Ty::Int { width: 64, signed: false };
    let func = VerifiableFunction {
        name: "f".into(),
        def_path: "crate::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u64t.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: u64t.clone(), name: Some("i".into()) },
                LocalDecl { index: 2, ty: u64t.clone(), name: Some("dr".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("_4".into()) },
            ],
            blocks: vec![
                // bb0: a `Drop` — an UNGUARDED target edge to bb1 and an equally
                // UNGUARDED `Cleanup` edge to bb2 (`unguarded_successors` returns both,
                // model.rs:6882-6900), so bb2's path list is the EMPTY one.
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        place: Place::local(2),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Cleanup(BlockId(2)),
                        span: SourceSpan::default(),
                    },
                },
                // bb1: the GUARD — `if i >= 8`, whose `SwitchIntMatch` edge to bb3 is a
                // `discovered_clauses` edge and therefore pushes a guard.
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(8, 64)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(1, BlockId(3))],
                        otherwise: BlockId(5),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                // bb3: a `BoundsCheck` assert whose condition local is NOT defined here,
                // so `combine_relevant_block_defs` returns the body BARE (a non-`And`)
                // and the empty-guard path pushes it unwrapped.
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(4),
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: u64t,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = trust_vcgen::generate_vcs(&func);
    let mixed: Vec<_> = vcs.iter().filter(|vc| contains_mixed_or(&vc.formula)).collect();
    assert!(
        !mixed.is_empty(),
        "a MIXED path-guard `Or` must be reachable from the real emitter through an \
         unwind edge — if this CFG no longer produces one, re-derive the shape before \
         weakening anything that rests on it; emitted formulas were {:?}",
        vcs.iter().map(|vc| (&vc.kind, &vc.formula)).collect::<Vec<_>>()
    );
    // And the DIRECTION claim `violation_candidates`' doc block makes, checked rather
    // than asserted: in the mixed `Or` this emitter really builds, each BARE disjunct —
    // the one the candidate producer skips — is the RAW body, and is therefore also the
    // LAST conjunct of some `And` disjunct, i.e. a DUPLICATE of a candidate that
    // survives. That is what makes the skip harmless for the lanes that read the node
    // and not harmless for the one that reads a side condition off the siblings.
    fn ors(f: &Formula, out: &mut Vec<Vec<Formula>>) {
        match f {
            Formula::Or(v) => {
                out.push(v.clone());
                for d in v {
                    ors(d, out);
                }
            }
            Formula::And(v) => {
                for d in v {
                    ors(d, out);
                }
            }
            Formula::Not(a) => ors(a, out),
            Formula::Implies(a, b) => {
                ors(a, out);
                ors(b, out);
            }
            _ => {}
        }
    }
    let mut seen_mixed = 0usize;
    for vc in &mixed {
        let mut all_ors = Vec::new();
        ors(&vc.formula, &mut all_ors);
        for disjuncts in &all_ors {
            let bare: Vec<&Formula> =
                disjuncts.iter().filter(|d| !matches!(d, Formula::And(_))).collect();
            if bare.is_empty() || bare.len() == disjuncts.len() {
                continue; // not a MIXED `Or`
            }
            seen_mixed += 1;
            let lasts: Vec<&Formula> = disjuncts
                .iter()
                .filter_map(|d| match d {
                    Formula::And(v) => v.last(),
                    _ => None,
                })
                .collect();
            for b in bare {
                assert!(
                    lasts.contains(&b),
                    "the bare disjunct the candidate producer skips is NOT a duplicate \
                     of a surviving candidate — the `DIRECTION` paragraph of \
                     `violation_candidates` no longer holds on the shape the emitter \
                     builds: bare {b:?} vs body-position conjuncts {lasts:?}"
                );
            }
        }
    }
    assert!(seen_mixed > 0, "the mixed `Or` must have been found by this walk too");
}

// ---------------------------------------------------------------------------
// [REMOVED 2026-08-01] `trustir_corpus_census` (and its `kind_label` helper) was the
// `#[ignore]`d measurement harness. It tallied the tier's per-shape census with the deleted
// `emitted_shift_violation` / `emitted_arith_violation` / `contains_mixed_or` peels, so it
// cannot compile once the peels are gone. It never ran in the suite (`#[ignore]`), and its
// figures were peel-mechanism census numbers, not live-certifier soundness assertions.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// ROUND 5 — the five survivors and the three holes round 4 opened.
// Each of these FAILS on the tree it was written against (dd78924a1cf + the claim
// corrections 505b46f7a65), verified by reverting `trustir_safety.rs` in place and
// re-running; the observed pre-fix failure is quoted on each.
// ---------------------------------------------------------------------------

/// D2 — SIGNED MIXED-WIDTH. `arith_width_agrees_with_kind` accepts a width EITHER of
/// the VC's operand types mentions. With DIFFERENT widths that is a free choice: the
/// same two-bare-`Var` body certifies at `W8` under kind `(i8, i64)` and at `W64` under
/// `(i64, i8)`, and nothing in the VC narrows anything. The constant that justifies a
/// narrowing is the whole reason `operand_ty`'s fabricated `i64` is tolerated, so when
/// the widths differ the WIDER position must hold that constant — and the certified
/// width must be the NARROWER one.
///
/// PRE-FIX (observed, by removing both `mixed_width_narrowing_is_justified` call
/// sites): `(Some(SignedOverflow(Add, W8)), ProvenModulo3)` for the `(i8, i64)` kind —
/// the certified width follows whichever threshold the body carries, with two bare
/// `Var` operands and nothing narrowing anything. (The `(i64, i8)` mirror image is
/// asserted immediately after it and is the same defect at the other width; the first
/// assertion is the one that aborts the pre-fix run.)
#[test]
fn a_mixed_width_signed_kind_may_not_pick_its_own_width() {
    let i8t = Ty::Int { width: 8, signed: true };
    let i64t = Ty::Int { width: 64, signed: true };
    let body = |min: i128, max: i128| {
        Formula::And(vec![
            urange("a", min, max),
            urange("b", min, max),
            Formula::Or(vec![
                Formula::Lt(Box::new(Formula::Add(var("a"), var("b"))), int(min)),
                Formula::Gt(Box::new(Formula::Add(var("a"), var("b"))), int(max)),
            ]),
        ])
    };
    let vc = |tys: (Ty, Ty), min: i128, max: i128| VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, operand_tys: tys },
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: body(min, max),
        contract_metadata: None,
        obligation: None,
    };
    let f = no_assert_func();
    // An `i8`-thresholded body under `(i8, i64)`: the `i64` position is a bare `Var`,
    // so nothing narrows the obligation to 8 bits.
    let got = trustir_safety_vc_adequate_kind(&f, &vc((i8t.clone(), i64t.clone()), -128, 127));
    assert!(
        matches!(got.1, RefinementVerdict::KernelRejected(_)),
        "a mixed-width kind may not certify at the narrower width with no constant in \
         the wider position — got {got:?}"
    );
    // The mirror image: an `i64`-thresholded body under `(i64, i8)` may not certify at
    // 64 either — the certified width has to be the narrower one when they differ.
    let got = trustir_safety_vc_adequate_kind(
        &f,
        &vc((i64t.clone(), i8t.clone()), i64::MIN as i128, i64::MAX as i128),
    );
    assert!(
        matches!(got.1, RefinementVerdict::KernelRejected(_)),
        "a mixed-width kind may not certify at the WIDER width: `int_op_type` takes the \
         emitted thresholds from the non-constant operand, so the wider width is exactly \
         the one no operand justifies — got {got:?}"
    );
    // POSITIVE CONTROL, through the REAL emitter: `100i8 + x` is the row `min(wa, wb)`
    // exists for, and it must survive at its own emitted width.
    assert_eq!(
        minted(&const_add_func(100, 8), |k| matches!(k, VcKind::ArithmeticOverflow { .. })),
        vec![(Some(IrSafetyVcKind::SignedOverflow(IrSignedOp::Add, IrSWidth::W8)), true)],
        "the emitter's own mixed-width row must keep its certificate"
    );
    // …and the same at another width, so this is not an `i8` special case.
    assert_eq!(
        minted(&const_add_func(100, 16), |k| matches!(k, VcKind::ArithmeticOverflow { .. })),
        vec![(Some(IrSafetyVcKind::SignedOverflow(IrSignedOp::Add, IrSWidth::W16)), true)],
    );
}

/// D1/D8 — THE NEGATION SUBJECT, ON EVERY ROUTE. Round 4 recovered the negated subject
/// from the MIR but ran the check only when the core was reached through the
/// assert-condition indirection (`via_condition_local`). The DIRECT route — the shape
/// `v2_build_negation_raw_vc` and `signed_abs_panic_body` both build, an
/// `And([input_range_constraint(v, W, true), Eq(v, MIN)])` pair — was left
/// unauthenticated, on the argument that the body position authenticates it. That
/// argument is about the emitter, and this API takes a VC from anywhere.
///
/// PRE-FIX (observed): `(Some(NegOverflow(W32)), ProvenModulo3)` for a formula about
/// `x` in a function whose only negation is of `y` — `x` appears nowhere in any
/// negation the emitter could have been called about.
/// `fn f(y: i32, x: i8) -> i32 { -y }` — the MIR negates `y`, and `x` is a narrower
/// local the negation emitter never looks at.
fn neg_subject_func() -> VerifiableFunction {
    let i32t = Ty::Int { width: 32, signed: true };
    let i8t = Ty::Int { width: 8, signed: true };
    VerifiableFunction {
        name: "f".into(),
        def_path: "crate::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32t.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: i32t.clone(), name: Some("y".into()) },
                LocalDecl { index: 2, ty: i8t, name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: i32t,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The negation emitter's OWN `And([input_range_constraint(v, W, true), Eq(v, MIN)])`
/// pair shape, over any subject and any width — i.e. a VC that takes the DIRECT route.
fn neg_subject_vc(subject: &str, width: u32, min: i128) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::NegationOverflow { ty: Ty::Int { width, signed: true } },
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            urange(subject, min, -min - 1),
            Formula::Eq(var(subject), int(min)),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

#[test]
fn the_negation_subject_is_checked_on_the_direct_route_too() {
    let func = neg_subject_func();
    let got = trustir_safety_vc_adequate_kind(&func, &neg_subject_vc("x", 32, i32::MIN as i128));
    assert!(
        matches!(got.1, RefinementVerdict::KernelRejected(_)),
        "the DIRECT route must authenticate the subject too: `x` is negated nowhere in \
         this function, so no negation certificate can be about it — got {got:?}"
    );
    // The width half is [`the_negation_width_comes_from_the_certified_variables_own_type`],
    // split out so each half fails on its own rather than hiding behind the first.
    // POSITIVE CONTROL: the honest row still certifies, through the REAL emitter.
    let (kind, verdict) = {
        let vcs = trust_vcgen::generate_vcs(&func);
        let vc = vcs
            .iter()
            .find(|v| matches!(v.kind, VcKind::NegationOverflow { .. }))
            .expect("the emitter must still raise a negation VC for `-y`");
        trustir_safety_vc_adequate_kind(&func, vc)
    };
    assert_eq!(kind, Some(IrSafetyVcKind::NegOverflow(IrSWidth::W32)));
    assert!(matches!(verdict, RefinementVerdict::ProvenModulo3));
}

/// D1/D8, the width half — the certified width must be the CERTIFIED VARIABLE's own,
/// not `vc.kind`'s `ty` (which describes whatever local the emitter was called about)
/// and not the emitted threshold alone (which a forger writes). `y` is `i32` in
/// [`neg_subject_func`], so an 8-bit claim about it is refused even though the kind's
/// `ty` and the threshold agree with each other.
///
/// PRE-FIX (observed): `(Some(NegOverflow(W8)), ProvenModulo3)` — an 8-bit negation
/// certificate about an `i32` variable, with both existing cross-checks satisfied.
#[test]
fn the_negation_width_comes_from_the_certified_variables_own_type() {
    let func = neg_subject_func();
    let vc = neg_subject_vc("y", 8, -128);
    let got = trustir_safety_vc_adequate_kind(&func, &vc);
    assert!(
        matches!(got.1, RefinementVerdict::KernelRejected(_)),
        "an 8-bit negation certificate about an `i32` subject must be refused — got {got:?}"
    );
}

/// D5/D6 — THE DOMAIN OF THE UADD VACUITY UNIVERSAL. The side condition ("the discarded
/// `Lt(a+b, 0)` disjunct is vacuous because both operands are pinned `≥ 0`") is a claim
/// about EVERY body position the violation occupies. Round 4 moved the range pair out of
/// the filter that builds the located set, but the filter itself survived: it still
/// required `siblings.is_some()` and `computed(node).is_some()`, so a second body
/// position the lane could not READ — here an assert-condition local whose sibling
/// binding is NOT the MIR's own definition, so the indirection does not resolve —
/// dropped out of the domain rather than failing it, and the universal ranged over the
/// one path that happened to carry the evidence.
///
/// PRE-FIX (observed, by restoring the round-4 filter + collapse in
/// `emitted_arith_violation_located`): the assertion below fails —
/// `(Some(UAddOverflow(W8)), ProvenModulo3)`, a certificate read off the first path's
/// ranges while a body position with no range evidence at all sits in the same formula.
///
/// The unit-level half of the same defect — an occurrence with NO sibling list being
/// `filter_map`ped out of `all_siblings` instead of failing it — is pinned by
/// [`a_side_condition_over_zero_sibling_sets_must_not_pass`].
#[test]
fn a_rangeless_occurrence_must_fail_the_vacuity_universal_not_drop_out_of_it() {
    // The assert-condition route: `bb0 { _2 = (a == 0); assert(!_2) -> bb1 }`, so the
    // MIR really does define `_2` and the resolved core is admissible…
    let u8t = Ty::Int { width: 8, signed: false };
    let func = assert_cond_func("a", 0, AssertMessage::Overflow(trust_types::BinOp::Add), u8t);
    let oor = uadd_or(0, 255);
    // …and the same violation occurs TWICE: once with the emitter's unsigned ranges
    // beside it, once as the resolved definition of the condition local, which carries
    // no ranges at all.
    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: trust_types::BinOp::Add,
            operand_tys: (Ty::Int { width: 8, signed: false }, Ty::Int { width: 8, signed: false }),
        },
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: Formula::Or(vec![
            Formula::And(vec![urange("a", 0, 255), urange("b", 0, 255), oor.clone()]),
            Formula::And(vec![
                Formula::Eq(Box::new(Formula::Var(COND.into(), Sort::Bool)), Box::new(oor)),
                Formula::Var(COND.into(), Sort::Bool),
            ]),
        ]),
        contract_metadata: None,
        obligation: None,
    };
    let got = trustir_safety_vc_adequate_kind(&func, &vc);
    assert!(
        matches!(got.1, RefinementVerdict::KernelRejected(_)),
        "a body position carrying NO range evidence must FAIL the vacuity universal, not \
         be excluded from the set it quantifies over — got {got:?}"
    );
}

/// D7 — THE BARE `Or` DISJUNCT, AT THE LANES ROUND 4 DID NOT COVER. `violation_candidates`
/// descends only the `And` disjuncts of an `Or`, so the bare disjunct an empty-guard path
/// pushes is never examined. Round 4 declined on it in the arithmetic lane only; bounds,
/// shift and div/rem read their certified proposition from the same candidate set and
/// kept certifying off the guarded twin.
///
/// PRE-FIX (observed, by moving the `contains_mixed_or` decline back into the
/// arithmetic lane and restoring the round-4 per-lane filter + collapse), all three
/// minting at once:
/// `[("bounds", (Some(Bounds { signed: false }), ProvenModulo3)),
///   ("div/rem", (Some(DivByZero), ProvenModulo3)),
///   ("shift", (Some(ShiftOob(W32, false)), ProvenModulo3))]`
/// — three kernel-checked certificates, each about one half of a formula whose other
/// body position states a different obligation.
#[test]
fn a_mixed_path_guard_or_declines_at_every_lane_not_only_the_arithmetic_one() {
    let f = no_assert_func();
    let mixed = |body: Formula, other: Formula| {
        Formula::Or(vec![
            Formula::And(vec![Formula::Gt(var("g"), int(0)), body]),
            other, // the BARE disjunct — the empty-guard path, never descended
        ])
    };
    let bounds = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: mixed(
            Formula::Ge(var("i"), var("len")),
            Formula::Ge(var("j"), var("other_len")),
        ),
        contract_metadata: None,
        obligation: None,
    };
    let bounds_got = trustir_safety_vc_adequate_kind(&f, &bounds);
    let divzero = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: mixed(
            Formula::Eq(var("b"), int(0)),
            Formula::Eq(var("c"), int(0)),
        ),
        contract_metadata: None,
        obligation: None,
    };
    let divzero_got = trustir_safety_vc_adequate_kind(&f, &divzero);
    let shift = VerificationCondition {
        kind: VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: Ty::Int { width: 32, signed: false },
            shift_ty: Ty::Int { width: 32, signed: false },
        },
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: mixed(
            Formula::And(vec![urange("n", 0, 255), Formula::Ge(var("n"), int(32))]),
            Formula::Ge(var("m"), int(64)),
        ),
        contract_metadata: None,
        obligation: None,
    };
    let shift_got = trustir_safety_vc_adequate_kind(&f, &shift);
    // Reported TOGETHER: each lane is a separate instance of the same defect, and a
    // single failing assertion would hide the other two behind the first.
    let lanes = [("bounds", bounds_got), ("div/rem", divzero_got), ("shift", shift_got)];
    let minting: Vec<_> =
        lanes.iter().filter(|(_, g)| !matches!(g.1, RefinementVerdict::KernelRejected(_))).collect();
    assert!(
        minting.is_empty(),
        "no lane may certify its own half of a MIXED `Or` while a body position it never \
         examined states something else — these did: {minting:?}"
    );
}

/// D6 — AN UNRECOGNIZED BODY POSITION IS AN OBLIGATION THIS TIER CANNOT READ. The
/// per-lane `filter` used to drop every candidate its own shape predicate rejected and
/// then collapse what remained to a singleton, so a second, DIFFERENT body position
/// vanished from the set the ambiguity rule ranged over.
///
/// PRE-FIX (observed): `(Some(DivByZero), ProvenModulo3)` — the `Eq(b, 0)` path
/// certified while the other guarded path's body, a bounds violation, was dropped by
/// the div/rem lane's `is_core` filter before the collapse could see it.
#[test]
fn two_different_body_positions_are_ambiguous_not_a_singleton() {
    let f = no_assert_func();
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: Formula::Or(vec![
            Formula::And(vec![Formula::Gt(var("g"), int(0)), Formula::Eq(var("b"), int(0))]),
            Formula::And(vec![
                Formula::Le(var("g"), int(0)),
                Formula::Ge(var("i"), var("len")),
            ]),
        ]),
        contract_metadata: None,
        obligation: None,
    };
    let got = trustir_safety_vc_adequate_kind(&f, &vc);
    assert!(
        matches!(got.1, RefinementVerdict::KernelRejected(_)),
        "two DIFFERENT propositions at body positions is an ambiguous obligation; a lane \
         may not filter the one it does not recognize out of the set it collapses — got \
         {got:?}"
    );
}

/// D4 — THE SIGNED-INDEX BOUNDS FORM IS A NAMED GAP, NOT A SHAPE MISMATCH. `idxOob`
/// models `len ≤ i` alone, so `Or([Lt(i,0), Ge(i,len)])` must decline — it always did,
/// but by failing a `Ge`-only matcher, which is the same verdict for the wrong reason
/// and is indistinguishable from "not a bounds violation". The shape is now recognized
/// WITH its signedness ([`bounds_violation_shape`]) and declined by name.
#[test]
fn the_signed_index_bounds_form_is_recognized_and_declined_by_name() {
    let signed = Formula::Or(vec![
        Formula::Lt(var("i"), int(0)),
        Formula::Ge(var("i"), var("len")),
    ]);
    assert_eq!(
        bounds_violation_shape(&signed).map(|(_, _, s)| s),
        Some(true),
        "the signed index form must be RECOGNIZED (and then declined), not mistaken for \
         a non-violation"
    );
    assert_eq!(
        bounds_violation_shape(&Formula::Ge(var("i"), var("len"))).map(|(_, _, s)| s),
        Some(false)
    );
    // Authenticated: body = the signed `Or` core (empty wrappers), so the arm recognizes
    // and declines it BY NAME rather than for want of a record.
    let vc = bounds_vc(signed);
    match trustir_safety_vc_adequate(&no_assert_func(), &vc) {
        RefinementVerdict::KernelRejected(msg) => assert!(
            msg.contains("SIGNED"),
            "the decline must name the gap it is (an `idxOobSigned` spec is missing), not \
             read as a selection failure: {msg}"
        ),
        other => panic!("the signed index form must decline, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// ROUND 6 — the empty `And` disjunct.
// ---------------------------------------------------------------------------

/// F4 — AN EMPTY `And` DISJUNCT IS A BODY POSITION ASSERTING `True`, AND IT WAS
/// DROPPED. `violation_candidates`'s `F::And` arm descended `v.last()` behind an
/// `if let Some(last)`, so an EMPTY `And` contributed no occurrence at all. In
/// `Or([And([core]), And([])])` that leaves exactly one occurrence — the lane's own
/// core — which then agrees with itself, sits at a body position, and matches
/// `is_core`. But `clean_ground::ground_prop` folds an empty `And` to `True`
/// (`F::And(v) => fold_prop(v, "And", "True", params)`, clean_ground.rs:8526), so the
/// obligation the VC actually states is `core ∨ True` — identically true, a
/// proposition about nothing. The certificate says `core`. That is a forgery by this
/// file's own definition.
///
/// Round 5's `is_path_guard_splice` pre-filter is what made it invisible at the top:
/// `Or([And(_), And(_)])` is a splice by that predicate, so the parent `Or` — the only
/// node that still MENTIONS the vacuous disjunct — is removed from the agreement rule's
/// domain, and nothing downstream ever sees a body position asserting `True`. Fixing it
/// by widening the pre-filter would recreate the same drop-vs-fail hazard one level up,
/// so the producer EMITS a candidate for the empty `And` instead and the agreement rule
/// fails on it.
///
/// PRE-FIX (observed 2026-07-31, by restoring `if let Some(last) = v.last()` in
/// `violation_candidates`), all three minting at once:
/// `[("bounds", (Some(Bounds { signed: false }), ProvenModulo3)),
///   ("div/rem", (Some(DivByZero), ProvenModulo3)),
///   ("shift", (Some(ShiftOob(W32, false)), ProvenModulo3))]`
#[test]
fn an_empty_and_disjunct_is_a_body_position_stating_true_not_a_droppable_one() {
    let f = no_assert_func();
    let vacuous = |body: Formula| {
        Formula::Or(vec![Formula::And(vec![body]), Formula::And(Vec::new())])
    };
    let bounds = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: vacuous(Formula::Ge(var("i"), var("len"))),
        contract_metadata: None,
        obligation: None,
    };
    let bounds_got = trustir_safety_vc_adequate_kind(&f, &bounds);
    let divzero = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: vacuous(Formula::Eq(var("b"), int(0))),
        contract_metadata: None,
        obligation: None,
    };
    let divzero_got = trustir_safety_vc_adequate_kind(&f, &divzero);
    let shift = VerificationCondition {
        kind: VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: Ty::Int { width: 32, signed: false },
            shift_ty: Ty::Int { width: 32, signed: false },
        },
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: vacuous(Formula::And(vec![
            urange("n", 0, 255),
            Formula::Ge(var("n"), int(32)),
        ])),
        contract_metadata: None,
        obligation: None,
    };
    let shift_got = trustir_safety_vc_adequate_kind(&f, &shift);
    // Reported TOGETHER, as the D7 test above does: one failing assertion would hide
    // the other two lanes behind the first.
    let lanes = [("bounds", bounds_got), ("div/rem", divzero_got), ("shift", shift_got)];
    let minting: Vec<_> =
        lanes.iter().filter(|(_, g)| !matches!(g.1, RefinementVerdict::KernelRejected(_))).collect();
    assert!(
        minting.is_empty(),
        "an empty `And` disjunct folds to `True`, so the obligation is identically true \
         and no lane may certify its own disjunct off it — these did: {minting:?}"
    );
}

// [REMOVED 2026-08-01] `an_empty_and_still_yields_a_candidate` was the PRODUCER half of F4,
// stated directly against the deleted `violation_candidates_resolved` / `is_path_guard_splice`
// peel (that an empty `And` yields a candidate rather than vanishing). The candidate producer
// is deleted — production authenticates a recorded obligation — so this tests behaviour that
// no longer exists. The LANE-level F4 property (an empty-`And` disjunct folding to `True` may
// not be certified) is still pinned by `an_empty_and_disjunct_is_a_body_position_stating_true_
// not_a_droppable_one` above, which drives the live certifier.

// ---------------------------------------------------------------------------
// THE AUTHENTICATED-OBLIGATION FIELD — trust-ir twin of
// `mirsem::obligation_region_tests::a_truthful_recorded_obligation_certifies_and_a_
// hostile_one_is_declined`. The recorded `vc.obligation` REPLACES the peel for the
// div/rem and negation lanes, but only after `reconstruct_obligation(rec) == vc.formula`
// authenticates it; a hostile record (field claims one core, formula asserts a different
// violable one) is DECLINED, never certified and never silently ignored. Both lanes MUST
// agree (the parity checker pins them), which is why this mirrors the mirsem test.
// ---------------------------------------------------------------------------

/// A function whose MIR negates the operand named `name` at width `w` (signed), so
/// `negation_subjects` finds it for the body-route negation lane. The trust-ir twin of
/// mirsem's `named_neg_func`.
fn raw_neg_func(name: &str, w: u32) -> VerifiableFunction {
    let t = Ty::Int { width: w, signed: true };
    VerifiableFunction {
        name: "neg".into(),
        def_path: "crate::neg".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: t.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: t.clone(), name: Some(name.into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: t,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// TRUTHFUL RECORD CERTIFIES, HOSTILE RECORD DECLINES, on both sliced lanes.
///
/// FALSIFICATION (constraint 4), verified by reverting IN PLACE: relax
/// `select_obligation`'s equate (make it `if true`, or route its `Decline` arm to the
/// peel) and the hostile div VC mints `(Some(DivByZero), ProvenModulo3)` off the field's
/// `Eq(w,0)` body while the hostile negation VC mints `(Some(NegOverflow(W32)), …)` off the
/// peel's real `Eq(y, i32::MIN)`.
#[test]
fn a_truthful_recorded_obligation_certifies_and_a_hostile_one_is_declined_ir() {
    let proven = |(k, v): (Option<IrSafetyVcKind>, RefinementVerdict)| {
        (k, matches!(v, RefinementVerdict::ProvenModulo3))
    };

    // ---- ARM 1: div-by-zero (body-only) --------------------------------------------
    let div_hyp = Formula::Ge(var("p"), int(0));
    let div_core = Formula::Eq(var("z"), int(0));
    let div_formula = Formula::And(vec![div_hyp.clone(), div_core.clone()]);
    let div_vc = |obligation: Option<trust_types::ObligationRecord>| VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: div_formula.clone(),
        contract_metadata: None,
        obligation,
    };
    let conjoin = |facts: Vec<Formula>| {
        vec![trust_types::ObligationWrapper::ConjoinFactsLast { facts }]
    };
    let div_truthful = trust_types::ObligationRecord {
        body: div_core.clone(),
        wrappers: conjoin(vec![div_hyp.clone()]),
        subject: None,
        width: None,
    };
    let div_hostile = trust_types::ObligationRecord {
        body: Formula::Eq(var("w"), int(0)),
        wrappers: conjoin(vec![div_hyp.clone()]),
        subject: None,
        width: None,
    };

    // FIELD-REQUIRED (2026-08-01): the peel is deleted, so a TRUTHFUL record is the ONLY
    // thing that certifies, and it certifies to this kind's own `IrSafetyVcKind`.
    assert_eq!(
        proven(trustir_safety_vc_adequate_kind(&no_assert_func(), &div_vc(Some(div_truthful)))),
        (Some(IrSafetyVcKind::DivByZero), true),
        "a TRUTHFUL recorded obligation (reconstruct == formula) must certify DivByZero"
    );
    assert_eq!(
        trustir_safety_vc_adequate_kind(&no_assert_func(), &div_vc(Some(div_hostile))).0,
        None,
        "a HOSTILE recorded obligation (field says `Eq(w,0)`, formula asserts the violable \
         `Eq(z,0)`) reconstructs to a DIFFERENT formula, so the authentication must DECLINE"
    );

    // ---- ARM 2: negation overflow (body + subject + width) -------------------------
    // The emitter's raw-neg pair: `And([range(y), Eq(y, i32::MIN)])`, so the peel's range
    // sibling is present and the None baseline certifies too.
    let neg_range = Formula::And(vec![
        Formula::Le(int(-2147483648), var("y")),
        Formula::Le(var("y"), int(2147483647)),
    ]);
    let neg_core = Formula::Eq(var("y"), int(-2147483648));
    let neg_formula = Formula::And(vec![neg_range.clone(), neg_core.clone()]);
    let neg_vc = |obligation: Option<trust_types::ObligationRecord>| VerificationCondition {
        kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
        function: "crate::neg".into(),
        location: SourceSpan::default(),
        formula: neg_formula.clone(),
        contract_metadata: None,
        obligation,
    };
    let neg_truthful = trust_types::ObligationRecord {
        body: neg_core.clone(),
        wrappers: conjoin(vec![neg_range.clone()]),
        subject: Some(*var("y")),
        width: Some(32),
    };
    // The [10]-class WIDTH forgery: the field's body claims the i8 MIN threshold.
    let neg_hostile = trust_types::ObligationRecord {
        body: Formula::Eq(var("y"), int(-128)),
        wrappers: conjoin(vec![neg_range.clone()]),
        subject: Some(*var("y")),
        width: Some(8),
    };

    assert_eq!(
        proven(trustir_safety_vc_adequate_kind(&raw_neg_func("y", 32), &neg_vc(Some(neg_truthful)))),
        (Some(IrSafetyVcKind::NegOverflow(IrSWidth::W32)), true),
        "a TRUTHFUL recorded negation obligation must certify NegOverflow(W32)"
    );
    assert_eq!(
        trustir_safety_vc_adequate_kind(&raw_neg_func("y", 32), &neg_vc(Some(neg_hostile))).0,
        None,
        "a HOSTILE recorded negation obligation (field says the width-8 `Eq(y,-128)`, formula \
         asserts the width-32 `Eq(y,-2147483648)`) reconstructs to a DIFFERENT formula, so the \
         authentication must DECLINE"
    );
}

/// A recorded obligation that FAILS to authenticate DECLINES; it never falls back to the
/// peel (constraint 3). The peel WOULD certify this formula, yet a `Some(obligation)` whose
/// wrappers do not reproduce `formula` fails closed. Falsified by routing
/// `ObligationSelection::Decline` to the peel.
#[test]
fn an_unfaithful_recorded_obligation_declines_it_does_not_fall_back_to_the_peel_ir() {
    let hyp = Formula::Ge(var("p"), int(0));
    let core = Formula::Eq(var("z"), int(0));
    let formula = Formula::And(vec![hyp.clone(), core.clone()]);
    let vc = |obligation: Option<trust_types::ObligationRecord>| VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::f".into(),
        location: SourceSpan::default(),
        formula: formula.clone(),
        contract_metadata: None,
        obligation,
    };
    // Control (field-required): a TRUTHFUL record (reconstruct == formula) certifies the same
    // formula, so the decline below is the authentication rejecting the unfaithful record.
    let truthful = trust_types::ObligationRecord {
        body: core.clone(),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![hyp.clone()],
        }],
        subject: None,
        width: None,
    };
    assert_eq!(
        trustir_safety_vc_adequate_kind(&no_assert_func(), &vc(Some(truthful))).0,
        Some(IrSafetyVcKind::DivByZero),
        "control: a TRUTHFUL record must certify this formula, else the test proves nothing"
    );
    // A record whose wrappers carry an EXTRA fact not present in `formula`.
    let unfaithful = trust_types::ObligationRecord {
        body: core.clone(),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![hyp, Formula::Ge(var("q"), int(0))],
        }],
        subject: None,
        width: None,
    };
    assert_eq!(
        trustir_safety_vc_adequate_kind(&no_assert_func(), &vc(Some(unfaithful))).0,
        None,
        "a recorded-but-unfaithful obligation must DECLINE, not fall back to the peel"
    );
}
