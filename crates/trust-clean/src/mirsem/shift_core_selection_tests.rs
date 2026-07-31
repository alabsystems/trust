// Trust: SHIFT-CORE SELECTION (2026-07-29) — the safety-VC adequacy certifier must
// read the shift VC's OWN emitted violation, not the first hypothesis conjunct that
// happens to be shaped like one.
//
// `v2_build_shift_overflow_vc` wraps the violation `And([range, invalid])` in block
// definitions, dominating guards, the function's `preconditions`, and its parameters'
// type bounds. The old selection took the FIRST `Ge(var|int, Int)` in a pre-order walk
// of that whole wrapped formula, which is a hypothesis far more often than it is the
// violation — measured over the committed ladder, 68 of 77 emitted `ShiftOverflow` VCs.
// Both directions of the mis-selection were real, and both are pinned here:
//
//   * FAIL-CLOSED (the bit_field −12): the extractor's synthesized parameter-domain
//     precondition `And([Ge(bit,0), Le(bit,u64::MAX)])` puts `Ge(bit,0)` ahead of the
//     real core `Ge(bit,W)`, `ShiftWidth::from_bits(0)` declines, and the FUNCTION
//     loses its certificate. Note the mirror spelling `Le(0,bit)` — the SAME
//     proposition, and the one `augment_with_type_bounds` emits into the very same
//     formula — never matched the `F::Ge` probe and so never declined: the gap was a
//     spelling collision, not a missing arm.
//   * FALSE CERTIFICATE: a precondition naming a modeled shift width mints a
//     kernel-checked `ShiftOob(W)` adequacy certificate for a width the VC does not
//     contain, over a variable the body never shifts by.
//
// `mirsem::tests::real_bit_field_get_bit_fixtures_are_fully_faithful` already pins the
// resulting FULLY_FAITHFUL verdict for these twelve rows. These tests deliberately do
// NOT restate that: they pin the two things the verdict cannot show — that the
// certified WIDTH is the body's own, and that a hypothesis can never supply it.
// Both FAIL on the pre-fix tree (nothing is minted at all / `ShiftOob(W32)` is).

use super::*;
use trust_types::{Formula, Sort, VerifiableFunction};

/// The committed re-frozen ladder's `bit_field` 0.10.2 corpus.
const BIT_FIELD_DIR: &str = "fixtures/census-rung2-2026-07-07/bit_field";

/// The twelve `BitField::get_bit` widths, each with the shift-amount OOB threshold
/// its own body emits. `<T as BitField>::get_bit` is
/// `assert!(bit < T::BIT_LENGTH); (*self & (1 << bit)) != 0`, so the emitted
/// violation is `Ge(bit, W)` where `W` is the SHIFTED VALUE's width — 64 for both
/// `isize` and `usize`. The shift AMOUNT is a `usize`, always unsigned.
const GET_BIT_WIDTHS: [(&str, ShiftWidth); 12] = [
    ("i8", ShiftWidth::W8),
    ("i16", ShiftWidth::W16),
    ("i32", ShiftWidth::W32),
    ("i64", ShiftWidth::W64),
    ("i128", ShiftWidth::W128),
    ("isize", ShiftWidth::W64),
    ("u8", ShiftWidth::W8),
    ("u16", ShiftWidth::W16),
    ("u32", ShiftWidth::W32),
    ("u64", ShiftWidth::W64),
    ("u128", ShiftWidth::W128),
    ("usize", ShiftWidth::W64),
];

fn load_bit_field(ty: &str) -> VerifiableFunction {
    let rel = format!("{BIT_FIELD_DIR}/<{ty} as lib__BitField>__get_bit.json");
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(&rel);
    // NO `Err(_) => continue`: a fixture rename must FAIL this test, not silence it.
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("bit_field fixture missing — {}: {e}", path.display()));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {rel}: {e}"))
}

fn shift_kinds(func: &VerifiableFunction) -> Vec<SafetyVcKind> {
    function_safety_vcs_faithful(func)
        .map(|c| c.shift.iter().map(|s| s.kind.clone()).collect())
        .unwrap_or_default()
}

/// The certified shift width must be the one THIS body emits, while the `Ge`-spelled
/// parameter-domain precondition sits in the same formula ahead of it.
#[test]
fn bit_field_get_bit_certifies_its_own_shift_width_under_a_ge_spelled_precondition() {
    for (ty, expected) in GET_BIT_WIDTHS {
        let func = load_bit_field(ty);

        // The fixture really does carry the `Ge`-first synthesized precondition — if
        // the extractor stops emitting it, this test measures nothing and must say so
        // rather than pass. (`Le(0, p)`-spelled bounds never collided; the whole point
        // is that this one does.)
        let ge_first_domain_pre = func.preconditions.iter().any(|p| {
            matches!(p, Formula::And(cs)
                if matches!(cs.as_slice(), [Formula::Ge(..), Formula::Le(..)]))
        });
        assert!(
            ge_first_domain_pre,
            "{ty}: fixture no longer carries the `And([Ge(p,lo), Le(p,hi)])` \
             parameter-domain precondition this test exists to pin — re-derive the \
             collision before weakening the assertion"
        );

        assert_eq!(
            shift_kinds(&func),
            vec![SafetyVcKind::ShiftOob(expected, false)],
            "{ty}: the certified shift width must be this body's own emitted \
             threshold, not one read off the hypothesis side of the VC formula"
        );
    }
}

/// A precondition may not supply the certified shift width. The `u8` body's only shift
/// violation is `bit >= 8`; a `Ge(_, 32)` hypothesis must never mint a `ShiftOob(W32)`
/// adequacy certificate — that is a kernel-checked claim about a proposition the VC
/// does not contain.
#[test]
fn a_precondition_can_never_supply_the_certified_shift_width() {
    let base = load_bit_field("u8");
    let want = vec![SafetyVcKind::ShiftOob(ShiftWidth::W8, false)];

    for (tag, pre) in [
        (
            "Ge(bit,64) — the right variable, the wrong width",
            Formula::Ge(Box::new(Formula::Var("bit".into(), Sort::Int)), Box::new(Formula::Int(64))),
        ),
        (
            "Ge(other,32) — a variable the body never shifts by",
            Formula::Ge(
                Box::new(Formula::Var("other".into(), Sort::Int)),
                Box::new(Formula::Int(32)),
            ),
        ),
    ] {
        let mut hostile = base.clone();
        hostile.preconditions = vec![pre];
        let minted = shift_kinds(&hostile);
        assert!(
            minted.is_empty() || minted == want,
            "{tag}: minted {minted:?} — a hypothesis conjunct was certified in place \
             of the emitted violation core"
        );
    }
}

// ---------------------------------------------------------------------------------
// Trust: lane A round-3 findings [1] and [2] (2026-07-29) — SHAPE without POSITION.
//
// `f1e45ccb0fe` replaced the loose `Ge(var|int, Int)` scan with a match on
// `v2_shift_violation_formula`'s VERBATIM emitted pair, which is the right SHAPE test —
// but it ran that match over the WHOLE `vc.formula`, descending `Not` and `Implies`. The
// other seven sites were subsequently anchored to `emitted_obligation_body`; this one was
// not, and it was the last locator in the file reading a hypothesis. Both directions of
// that were real, and both are pinned below.
// ---------------------------------------------------------------------------------

use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VcKind, VerifiableBody, VerificationCondition,
};

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

/// The emitter's verbatim shift-violation pair for a `u32` value shifted by `n: u32`:
/// `And([input_range_constraint(n, u32), Ge(n, 32)])`.
fn emitter_pair() -> Formula {
    Formula::And(vec![
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("n".into(), Sort::Int))),
            Formula::Le(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(4294967295)),
            ),
        ]),
        Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(32))),
    ])
}

fn shift_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: u32_ty(),
            shift_ty: u32_ty(),
        },
        function: "crate::probe".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

/// A `VerifiableFunction` with no body — the hand-built VCs below are certified against
/// it, and an empty body is the honest answer for a VC this MIR did not produce.
fn probe_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "probe".into(),
        def_path: "crate::probe".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![],
            blocks: vec![],
            arg_count: 0,
            return_ty: u32_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// FINDING [1] — THE FORGERY. The shift site's locator matched the emitter's pair
/// ANYWHERE in the tree, so a formula that merely CONTAINS the pair certified, whatever
/// the obligation's own body was. All four wrappings were MEASURED on the pre-fix tree
/// and every one returned `Some(ShiftOob(W32, false))`:
///
/// ```text
/// Not(pair)                    -> Some(ShiftOob(W32, false))
/// Implies(pair, Bool(true))    -> Some(ShiftOob(W32, false))
/// And([pair, Bool(true)])      -> Some(ShiftOob(W32, false))
/// And([Not(pair), Bool(true)]) -> Some(ShiftOob(W32, false))
/// ```
///
/// The third needs no polarity trick: `Bool(true)` is the emitter's own fail-closed
/// obligation marker (`lib__check_ascii_printable`'s bounds obligation really is
/// `Bool(true)`), and the pair sits where a `#[requires]` sits — a hypothesis conjunct.
/// So this is the same statement as
/// `obligation_region_tests::no_site_certifies_an_obligation_whose_own_body_has_no_modeled_core`,
/// at the site that table was missing.
///
/// The HONEST control is asserted in the same test: the bare pair — the obligation
/// unwrapped — must still certify at W32, so the fix removes the hypothesis lane and not
/// the arm.
#[test]
fn a_shift_hypothesis_conjunct_can_never_supply_the_certified_core() {
    let pair = emitter_pair();
    let forgeries: [(&str, Formula); 4] = [
        ("Not(pair)", Formula::Not(Box::new(pair.clone()))),
        (
            "Implies(pair, Bool(true))",
            Formula::Implies(Box::new(pair.clone()), Box::new(Formula::Bool(true))),
        ),
        ("And([pair, Bool(true)])", Formula::And(vec![pair.clone(), Formula::Bool(true)])),
        (
            "And([Not(pair), Bool(true)])",
            Formula::And(vec![Formula::Not(Box::new(pair.clone())), Formula::Bool(true)]),
        ),
    ];
    let mut forged: Vec<String> = Vec::new();
    for (tag, formula) in forgeries {
        // Not vacuous: the emitter's pair really IS somewhere in each of these trees —
        // that is precisely what the old whole-formula matcher found.
        assert!(
            emitted_shift_violation_pair_probe(&formula).is_some(),
            "{tag}: the emitter pair is no longer present in this tree, so the test \
             measures nothing — re-derive the shape before weakening it"
        );
        if let Some((k, _)) =
            safety_vc_is_faithful_formula_aware(&probe_func(), &shift_vc(formula))
        {
            forged.push(format!("{tag} -> {k:?}"));
        }
    }
    assert!(
        forged.is_empty(),
        "a kernel-checked `ShiftOob` adequacy certificate was minted from a HYPOTHESIS \
         conjunct (or from a negated / implied position): {forged:#?}"
    );

    // HONEST CONTROL: the obligation itself, unwrapped.
    assert_eq!(
        safety_vc_is_faithful_formula_aware(&probe_func(), &shift_vc(emitter_pair()))
            .map(|(k, _)| k),
        Some(SafetyVcKind::ShiftOob(ShiftWidth::W32, false)),
        "the emitter's own violation must still certify — the fix is a POSITION \
         restriction, not a narrower shape"
    );
}

/// `fn f(v: u32, n: u32, c: bool) -> u32 { if c { v << n } else { 0 } }`, straight
/// through the real emitter.
fn guarded_shl() -> VerifiableFunction {
    let shift = Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::BinaryOp(
            BinOp::Shl,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
        span: Default::default(),
    };
    VerifiableFunction {
        name: "guarded_shl".into(),
        def_path: "crate::guarded_shl".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u32_ty(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: u32_ty(), name: Some("v".into()) },
                LocalDecl { index: 2, ty: u32_ty(), name: Some("n".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: Default::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![shift], terminator: Terminator::Return },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: u32_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// FINDING [2] — THE LEGITIMATE ROW THE SAME DEFECT WAS COSTING. The pair matcher needs
/// the emitter's 2-element `And([And(range), invalid])` to survive into `vc.formula`, and
/// under a DOMINATING GUARD it does not: `v2_formula_with_path_guards` FLATTENS an
/// `And`-shaped body into the guarded term (`generate/safety.rs:1112-1116`), so the range
/// constraint and the violation become flat SIBLINGS of the guard —
/// `And([Var(c,Bool), And([Le(0,n), Le(n,u32::MAX)]), Ge(n,32)])` — and the pair is gone.
///
/// Nothing here is hostile: an `if` around a shift is enough. PRE-FIX the row silently
/// failed closed; POST-FIX the wrapper-inverse peels the same `Ge(n,32)` the unguarded
/// twin emits and it certifies. 0 rows on the 486-dump census move (every corpus shift VC
/// carries block defs or preconditions that re-nest the pair), so this recovers a
/// capability off-corpus rather than changing a committed number.
#[test]
fn a_path_guarded_shift_certifies_its_own_core() {
    let func = guarded_shl();
    let mut seen = 0usize;
    for vc in &trust_vcgen::generate_vcs(&func) {
        if !matches!(vc.kind, VcKind::ShiftOverflow { .. }) {
            continue;
        }
        seen += 1;
        // The pair really is destroyed — otherwise this test measures nothing.
        assert!(
            emitted_shift_violation_pair_probe(&vc.formula).is_none(),
            "the guard splice no longer flattens the emitter pair, so the drop this test \
             exists to pin is gone — re-derive it before weakening the assertion: {:?}",
            vc.formula
        );
        // … and the range constraint and the violation really are flat siblings.
        assert!(
            matches!(&vc.formula, Formula::And(cs)
                if cs.len() >= 3
                    && matches!(cs.last(), Some(Formula::Ge(..)))
                    && cs.iter().any(|c| matches!(c, Formula::And(r)
                        if matches!(r.as_slice(), [Formula::Le(..), Formula::Le(..)])))),
            "expected the FLATTENED guarded shape `And([guard, And([Le,Le]), Ge(n,W)])`, \
             got {:?}",
            vc.formula
        );
        assert_eq!(
            safety_vc_is_faithful_formula_aware(&func, vc).map(|(k, _)| k),
            Some(SafetyVcKind::ShiftOob(ShiftWidth::W32, false)),
            "a shift under a dominating guard emits the same `Ge(n,32)` violation as the \
             unguarded twin and must certify at the same width"
        );
    }
    assert_eq!(seen, 1, "the CFG must raise exactly one shift VC");
}

// ---------------------------------------------------------------------------------
// THE ITE CASE-SPLIT PEEL, at the shift arm (2026-07-30, round-4 defect [3]).
// ---------------------------------------------------------------------------------

/// The emitter's shift violation for the amount named `n`, thresholded at `w`:
/// `Ge(Var n, Int w)` — `v2_shift_violation_formula`'s unsigned form.
fn shift_arm(n: &str, w: i128) -> Formula {
    Formula::Ge(Box::new(Formula::Var(n.into(), Sort::Int)), Box::new(Formula::Int(w)))
}

/// A guarded case-split conjunct, exactly as `generate/ite.rs`'s `guarded` (`:43-47`)
/// spells one: `Implies(guard, arm)`.
fn case(guard: Formula, arm: Formula) -> Formula {
    Formula::Implies(Box::new(guard), Box::new(arm))
}

/// Trust: THE ITE CASE-SPLIT PEEL — SELECTION WAS POSITIONAL, NOT SEMANTIC
/// (2026-07-30, round-4 defect [3]).
///
/// `eliminate_term_ites` (`trust-vcgen/src/generate/entry.rs:603-604`) rewrites EVERY
/// generated VC whose formula contains an `Ite`, safety VCs included. A shift AMOUNT that
/// is an `Ite` turns the violation `Ge(n, W)` into the case split
/// `And([Implies(c, Ge(n1, W)), Implies(¬c, Ge(n2, W))])` — `lift_relation_ites`
/// (`ite.rs:136-143`) over `guarded` (`ite.rs:43-47`).
///
/// PRE-FIX, `emitted_obligation_body`'s `And`-last rule fed its `Implies`-consequent rule
/// and the peel returned the LAST arm's consequent WITH THE CASE GUARD STRIPPED — so the
/// certificate described one branch of a proposition that states both, and the `c` arm
/// was never read.
///
/// THE ARMS BELOW CARRY DIFFERENT WIDTHS (32 and 64), AND THAT IS AN API-LEVEL
/// CONSTRUCTION, NOT AN EMITTED ONE. `v2_shift_violation_formula` builds the threshold as
/// a `Formula::Int(width)` on the far side of the `Ge`, so lifting an `Ite` AMOUNT gives
/// both arms the SAME `W`; a two-width split is only constructible through the hand-built
/// `VerificationCondition` API. It is used anyway because it is the sharpest available
/// statement of the defect, and it is the round-4 verdict's own recipe: **swap the two
/// arms and the certificate changes width**, though `∧` is commutative and the
/// proposition is identical. Both orderings are asserted, so a repair that merely
/// reverses the selection order cannot pass.
///
/// POST-FIX both decline: the `And` is refused as a case split (all conjuncts are
/// `Implies`), and the `Implies` arm no longer fires at an inner position.
#[test]
fn a_shift_case_split_certifies_no_arms_width_in_either_order() {
    let c = || Formula::Var("c".into(), Sort::Bool);
    let not_c = || Formula::Not(Box::new(c()));
    let arm32 = || shift_arm("n1", 32);
    let arm64 = || shift_arm("n2", 64);

    // The two orderings of the SAME case split.
    let split_32_then_64 = Formula::And(vec![case(c(), arm32()), case(not_c(), arm64())]);
    let split_64_then_32 = Formula::And(vec![case(c(), arm64()), case(not_c(), arm32())]);

    // NOT VACUOUS: each arm, on its own, is a shape this arm certifies — so the only
    // thing standing between the case split and a certificate is the peel.
    assert_eq!(
        safety_vc_is_faithful_formula_aware(&probe_func(), &shift_vc(arm32())).map(|(k, _)| k),
        Some(SafetyVcKind::ShiftOob(ShiftWidth::W32, false)),
        "the W32 arm must certify in isolation, or this test measures nothing"
    );
    assert_eq!(
        safety_vc_is_faithful_formula_aware(&probe_func(), &shift_vc(arm64())).map(|(k, _)| k),
        Some(SafetyVcKind::ShiftOob(ShiftWidth::W64, false)),
        "the W64 arm must certify in isolation, or this test measures nothing"
    );

    let a = safety_vc_is_faithful_formula_aware(&probe_func(), &shift_vc(split_32_then_64.clone()))
        .map(|(k, _)| k);
    let b = safety_vc_is_faithful_formula_aware(&probe_func(), &shift_vc(split_64_then_32.clone()))
        .map(|(k, _)| k);

    // The load-bearing statement: a case split is not an obligation this arm can read.
    assert_eq!(
        (a.clone(), b.clone()),
        (None, None),
        "a `ShiftOob` certificate was minted for a CASE SPLIT \
         `(c -> n1>=W1) AND (!c -> n2>=W2)` by taking one arm's consequent and dropping \
         its guard; the other arm was never read"
    );

    // …and, redundantly but deliberately, the positional statement itself: the answer
    // may not depend on conjunct ORDER. This assertion survives any future widening.
    assert_eq!(
        a, b,
        "the certified width flips with conjunct order — selection is POSITIONAL, not \
         semantic ({a:?} vs {b:?} for the same proposition)"
    );
}

/// The same defect one level down: a case split that is not the whole formula but sits
/// where the obligation body sits, under the ordinary conjoining wrappers
/// (`And([hypothesis.., body])`). The peel must not walk into it.
///
/// The hypothesis conjunct is `Ge(other, 128)` — a legitimate `#[requires]`-shaped
/// proposition and a shape this site's probe accepts — so a repair that only refused the
/// TOP-LEVEL case split would still mint here off the wrapper.
#[test]
fn a_wrapped_shift_case_split_certifies_neither_its_arms_nor_its_wrapper() {
    let c = Formula::Var("c".into(), Sort::Bool);
    let split = Formula::And(vec![
        case(c.clone(), shift_arm("n1", 32)),
        case(Formula::Not(Box::new(c)), shift_arm("n2", 64)),
    ]);
    let hypothesis = shift_arm("other", 128);
    let wrapped = Formula::And(vec![hypothesis, split]);

    assert_eq!(
        safety_vc_is_faithful_formula_aware(&probe_func(), &shift_vc(wrapped)).map(|(k, _)| k),
        None,
        "a wrapped case split minted a `ShiftOob` certificate — either from an arm's \
         stripped consequent or from the hypothesis conjunct"
    );
}
