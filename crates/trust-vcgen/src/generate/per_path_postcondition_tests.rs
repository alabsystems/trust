//! ONE POSTCONDITION ROW PER ENUMERATED RETURN PATH — two-language battery
//! blocker a7.
//!
//! # The defect these pin, measured end to end
//!
//! `fn pick(a: u32, b: u32) -> u32 ensures a <= 1000000 ==> result >= a`
//! `{ if a >= 1000000 { 1000000 } else if b >= a { b } else { a } }`
//!
//! compiles (managed `trustc d75f13f97`, `--emit=mir`) to a Return block with
//! TWO predecessors:
//!
//! ```text
//! bb0: _5 = Ge(a, 1000000);  switchInt(_5) -> [0: bb1, otherwise: bb4]
//! bb1: _6 = Ge(b, a);        switchInt(_6) -> [0: bb3, otherwise: bb2]
//! bb2: _3 = b;  goto -> bb5
//! bb3: _3 = a;  goto -> bb5
//! bb4: _4 = 1000000;  goto -> bb6
//! bb5: _4 = _3;       goto -> bb6      <- the JOIN of the inner `if`
//! bb6: _0 = _4;  return
//! ```
//!
//! `bb4` is reached by ONE guard path and `bb5` by TWO, so before this lane the
//! two emitted rows had different SHAPES: `bb4`'s row is a flat `And`, `bb5`'s is
//! `Or([And([guards_1, body]), And([guards_2, body])])`. Measured verdicts on
//! that toolchain (`-Ztrust-verify-output=both`):
//!
//! ```text
//! vc:pick:postcondition:0  proved   trust-full-verifier   (flat row, trust-mc PDR receipt)
//! vc:pick:postcondition:1  proved   ay-in-process         (Or row, NO PDR receipt)
//! obligation:pick:postcondition:0  UNKNOWN  trust-exact-source-clause-discharge
//!   "source-clause catalog marker awaits sealed private body authorities"
//! ```
//!
//! The source clause is refused although BOTH body rows read `Proved`, because
//! the `Or`-shaped row carries only the fallback solver's revalidated authority
//! and the catalog composes from `KernelCertified | FreshExactDirectChcPdr`.
//!
//! THE SAME FUNCTION written with early `return`s — where rustc gives each path
//! its own `Return` block, hence one FLAT row per path — measures
//! `4 proved, 0 failed, 0 unknown out of 4` with the marker DISCHARGED. So the
//! axis is the row SHAPE, not the clause, the arithmetic, or the path count: an
//! author who writes the value-producing `if` expression was charged a
//! disjunctive query that the `return` spelling of the same program is not.
//!
//! # What the split is
//!
//! `Or(t_1..t_n)` is UNSAT exactly when every `t_i` is UNSAT, so emitting one row
//! per `t_i` DISTRIBUTES the path-guard conjunct: the split itself adds no fact,
//! drops none and changes none, and the CONJUNCTION of the emitted rows is
//! logically identical to the single row it replaces.
//!
//! It is NOT, however, "pure distribution" of the whole pipeline. The shared
//! tail is spine-sensitive in two places (`dedup_identical_return_slot_pin` and
//! `formula_has_return_slot_pin` in one tripwire), and a per-path row has a
//! positive `And` spine where the merged `Or` row had none — so a per-path row
//! can be STRICTLY more provable than the corresponding disjunct of the merged
//! row. The direction is fail-open-to-verdict, never credit-a-violation; the
//! argument is in `contract_vcs.rs`'s `finish_row` header, and
//! `one_path_false_twin_still_pins_the_genuine_value` plus
//! `early_return_postcondition_tests::one_of_three_paths_false_is_refuted_on_exactly_that_path`
//! are the standing guards on the second half of that sentence.
//!
//! # What these tests do NOT claim
//!
//! They are formula-shape tests. They measure what vcgen EMITS; the engine
//! verdict on the emitted rows is the integrator's measurement (`x.py build`
//! then the two-language battery), and the evidence that a flat per-path row of
//! this shape is admitted is the early-return measurement quoted above, not
//! anything asserted here. The one SATISFIABILITY assertion about the split
//! lives in `early_return_postcondition_tests`, which owns the exhaustive
//! propositional oracle.

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Contract, ContractKind, Formula, LocalDecl, Operand,
    Place, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::generate_v2_contract_vcs_impl;

// ───────────────────────────── MIR builders ─────────────────────────────

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: span() }
}

fn decl(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
    LocalDecl { index, ty, name: name.map(Into::into) }
}

fn u32_const(value: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(value, 32))
}

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn switch(discr: usize, zero_target: usize, otherwise: usize) -> Terminator {
    Terminator::SwitchInt {
        discr: Operand::Move(Place::local(discr)),
        targets: vec![(0, BlockId(zero_target))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: span(),
    }
}

fn make(
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
    postconditions: Vec<Formula>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "fixture".into(),
        def_path: "test::fixture".into(),
        span: span(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions,
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `ensures a <= 1000000 ==> result >= a` — the battery's a7 clause, verbatim.
fn conditional_clause() -> Formula {
    Formula::Implies(
        Box::new(Formula::Le(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Int(1_000_000)),
        )),
        Box::new(Formula::Ge(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("a".into(), Sort::Int)),
        )),
    )
}

/// The MIR above. `last_arm` is what the `else` arm stores into the shared
/// return temp `_3`: `Operand::Copy(_1)` is the TRUE program, `0u32` is the
/// one-path-false twin.
fn pick(last_arm: Operand) -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::u32(), None),
            decl(1, Ty::u32(), Some("a")),
            decl(2, Ty::u32(), Some("b")),
            decl(3, Ty::u32(), None),
            decl(4, Ty::u32(), None),
            decl(5, Ty::Bool, None),
            decl(6, Ty::Bool, None),
        ],
        vec![
            block(
                0,
                vec![assign(
                    Place::local(5),
                    Rvalue::BinaryOp(BinOp::Ge, copy(1), u32_const(1_000_000)),
                )],
                switch(5, 1, 4),
            ),
            block(
                1,
                vec![assign(Place::local(6), Rvalue::BinaryOp(BinOp::Ge, copy(2), copy(1)))],
                switch(6, 3, 2),
            ),
            block(
                2,
                vec![assign(Place::local(3), Rvalue::Use(copy(2)))],
                Terminator::Goto(BlockId(5)),
            ),
            block(
                3,
                vec![assign(Place::local(3), Rvalue::Use(last_arm))],
                Terminator::Goto(BlockId(5)),
            ),
            block(4, vec![assign(Place::local(4), Rvalue::Use(u32_const(1_000_000)))], {
                Terminator::Goto(BlockId(6))
            }),
            block(
                5,
                vec![assign(Place::local(4), Rvalue::Use(copy(3)))],
                Terminator::Goto(BlockId(6)),
            ),
            block(6, vec![assign(Place::local(0), Rvalue::Use(copy(4)))], Terminator::Return),
        ],
        2,
        vec![conditional_clause()],
    )
}

/// The TWO-path control: `if a >= 1000000 { 1000000 } else { a }`, whose every
/// Return-block predecessor is reached by exactly ONE guard path. Nothing here
/// may change.
fn clamp() -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::u32(), None),
            decl(1, Ty::u32(), Some("a")),
            decl(2, Ty::u32(), None),
            decl(3, Ty::Bool, None),
        ],
        vec![
            block(
                0,
                vec![assign(
                    Place::local(3),
                    Rvalue::BinaryOp(BinOp::Ge, copy(1), u32_const(1_000_000)),
                )],
                switch(3, 2, 1),
            ),
            block(1, vec![assign(Place::local(2), Rvalue::Use(u32_const(1_000_000)))], {
                Terminator::Goto(BlockId(3))
            }),
            block(
                2,
                vec![assign(Place::local(2), Rvalue::Use(copy(1)))],
                Terminator::Goto(BlockId(3)),
            ),
            block(3, vec![assign(Place::local(0), Rvalue::Use(copy(2)))], Terminator::Return),
        ],
        1,
        vec![conditional_clause()],
    )
}

/// An `arms`-way `SwitchInt` whose arms all `goto` one join, which forwards to
/// the Return block. The join is reached by exactly `arms` guard paths, so this
/// is the dial the cap is read off.
fn fan(arms: usize) -> VerifiableFunction {
    assert!(arms >= 2, "a join needs at least two arms");
    let join = arms + 1;
    let ret = arms + 2;
    let mut locals = vec![decl(0, Ty::u32(), None), decl(1, Ty::u32(), Some("a"))];
    locals.push(decl(2, Ty::u32(), None));
    locals.push(decl(3, Ty::u32(), None));

    let targets: Vec<(u128, BlockId)> =
        (0..arms - 1).map(|k| (k as u128, BlockId(k + 1))).collect();
    let mut blocks = vec![block(
        0,
        vec![],
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(1)),
            targets,
            otherwise: BlockId(arms),
            exhaustive_enum_unreachable: false,
            span: span(),
        },
    )];
    for k in 0..arms {
        blocks.push(block(
            k + 1,
            vec![assign(Place::local(2), Rvalue::Use(u32_const(k as u128)))],
            Terminator::Goto(BlockId(join)),
        ));
    }
    blocks.push(block(join, vec![assign(Place::local(3), Rvalue::Use(copy(2)))], {
        Terminator::Goto(BlockId(ret))
    }));
    blocks.push(block(ret, vec![assign(Place::local(0), Rvalue::Use(copy(3)))], {
        Terminator::Return
    }));

    make(
        locals,
        blocks,
        1,
        vec![Formula::Ge(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )],
    )
}

// ───────────────────────────── assertions ─────────────────────────────

fn postcondition_formulas(f: &VerifiableFunction) -> Vec<Formula> {
    generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| vc.formula)
        .collect()
}

fn rendered(formulas: &[Formula]) -> Vec<String> {
    formulas.iter().map(|f| format!("{f:?}")).collect()
}

/// The arity of the first `Or` reachable from the root through `And` children
/// only — i.e. an `Or` the SOLVER meets as a top-level case split rather than
/// inside some conjunct's own subterm. `None` when the row is flat.
///
/// This is the exact property the split exists to remove, and the exact property
/// the spine-walking helpers (`formula_has_return_slot_pin`,
/// `dedup_identical_return_slot_pin`) are blind
/// through.
fn spine_or_arity(formula: &Formula) -> Option<usize> {
    match formula {
        Formula::And(conjuncts) => conjuncts.iter().find_map(spine_or_arity),
        Formula::Or(terms) => Some(terms.len()),
        _ => None,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// The fix.
// ═══════════════════════════════════════════════════════════════════════════

/// A three-arm `if`/`else if`/`else` EXPRESSION now emits one row per return
/// path — three, not two — and every one of them is FLAT.
#[test]
fn three_arm_expression_emits_one_flat_row_per_path() {
    let formulas = postcondition_formulas(&pick(copy(1)));
    assert_eq!(
        formulas.len(),
        3,
        "one row per enumerated return path: bb4 (1 path) + bb5 (2 paths). \
         Before this lane there were 2, the second of them disjunctive: {:?}",
        rendered(&formulas)
    );
    for (index, formula) in formulas.iter().enumerate() {
        assert_eq!(
            spine_or_arity(formula),
            None,
            "row {index} must be flat — a top-level `Or` is the shape that got no \
             trust-mc PDR receipt and sent the clause to the fallback solver: {formula:?}"
        );
    }
}

/// COVERAGE. Splitting may never lose a path: the inner branch's TRUE and FALSE
/// guards must both still be asserted by some emitted row, and the outer guard
/// by its own.
///
/// Losing a path would be the one way this change could be unsound — an
/// execution no row quantifies over is an execution nothing checks — so it is
/// asserted directly rather than inferred from the row count.
#[test]
fn the_split_loses_no_path() {
    let formulas = rendered(&postcondition_formulas(&pick(copy(1))));
    let joined = formulas.join("\n");
    assert!(
        joined.contains(r#"Ge(Var("a", Int), Int(1000000))"#),
        "the outer TRUE guard must survive: {joined}"
    );
    assert!(
        joined.contains(r#"Not(Ge(Var("a", Int), Int(1000000)))"#),
        "the outer FALSE guard must survive: {joined}"
    );
    assert!(
        joined.contains(r#"Ge(Var("b", Int), Var("a", Int))"#),
        "the inner TRUE guard (`b >= a`) must survive: {joined}"
    );
    assert!(
        joined.contains(r#"Not(Ge(Var("b", Int), Var("a", Int)))"#),
        "the inner FALSE guard (`b < a`) must survive: {joined}"
    );
    let under_the_outer_false_guard =
        formulas.iter().filter(|f| f.contains(r#"Not(Ge(Var("a", Int), Int(1000000)))"#)).count();
    assert_eq!(
        under_the_outer_false_guard, 2,
        "the JOIN predecessor contributes exactly its two paths — both of them \
         under the OUTER false guard — and the flat sibling predecessor (reached \
         only under the outer TRUE guard) contributes neither: {formulas:?}"
    );
}

/// THE CLOSE NEGATIVE TWIN. The same clause and the same body except that the
/// `else` arm returns `0` — false on exactly that one path.
///
/// What is pinned is that the split does not credit a value the body never
/// wrote: the violating path's row still pins the return slot to the constant
/// `0`, so the negated clause stays satisfiable there and the row fails closed.
/// A split that "proved" this would be a green light with no information in it.
#[test]
fn one_path_false_twin_still_pins_the_genuine_value() {
    let truthy = rendered(&postcondition_formulas(&pick(copy(1))));
    let falsy = rendered(&postcondition_formulas(&pick(u32_const(0))));
    assert_eq!(truthy.len(), 3);
    assert_eq!(falsy.len(), 3, "the twin emits the same rows: {falsy:?}");

    let false_rows = falsy
        .iter()
        .filter(|f| f.contains(r#"Not(Ge(Var("b", Int), Var("a", Int)))"#))
        .collect::<Vec<_>>();
    assert_eq!(false_rows.len(), 1, "exactly one row covers the `b < a` path: {falsy:?}");
    assert!(
        false_rows[0].contains(r#"Eq(Var("_3"#) && false_rows[0].contains("Int(0)"),
        "the violating path's row must pin the shared return temp to the body's \
         GENUINE stored value `0` — the clause is then refutable on it: {}",
        false_rows[0]
    );

    let true_rows = truthy
        .iter()
        .filter(|f| f.contains(r#"Not(Ge(Var("b", Int), Var("a", Int)))"#))
        .collect::<Vec<_>>();
    assert_eq!(true_rows.len(), 1);
    assert_ne!(
        true_rows[0], false_rows[0],
        "the true program and its one-path-false twin must not assemble the SAME \
         row — a verifier that answers identically for both is not reading the body"
    );
}

/// THE TWO-PATH REGRESSION CONTROL. Every predecessor of this Return block is
/// reached by ONE guard path, so the split must not fire and the rows must stay
/// exactly what they were: two, both flat.
///
/// This is the guard against the split widening into shapes that already worked.
#[test]
fn two_path_body_is_untouched() {
    let formulas = postcondition_formulas(&clamp());
    assert_eq!(formulas.len(), 2, "unchanged: one row per predecessor: {:?}", rendered(&formulas));
    for formula in &formulas {
        assert_eq!(spine_or_arity(formula), None, "already flat before the split: {formula:?}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// The dropped-`requires` carve-out.
// ═══════════════════════════════════════════════════════════════════════════

/// A function whose authored `requires` the assumable-fragment gate DROPPED
/// declines the split entirely, and keeps HEAD's single merged `Or` row.
///
/// WHY THIS CARVE-OUT EXISTS. Three of the four `spec_unverifiable_vc` decisions
/// in this lane are shape tests that on an `Or`-rooted row are at least as eager
/// as they would be on any one path, so deciding them on the merged row can only
/// SUPPRESS rows a per-path decision would have emitted. The 2026-08-06
/// dropped-`requires` tripwire runs the other way: `only_excluded_counterexamples`
/// is a PER-MODEL test and `models(Or(t_1..t_n))` is the UNION of the
/// `models(t_i)`, so "every model of this row is an entry state the dropped
/// `requires` excludes" is STRICTLY STRONGER for the merged row than for any one
/// path. A merged row that declines can therefore contain a path whose own models
/// are all excluded — and shipping that path as its own row is exactly the
/// false-refutation-against-correct-code that P0 guard exists to stop.
///
/// The condition is per-FUNCTION (`dropped_requires_clauses`), so it is decided
/// identically for every clause and every predecessor of such a function.
#[test]
fn a_dropped_requires_declines_the_split_and_keeps_the_merged_row() {
    let mut f = pick(copy(1));
    // A `requires` in `func.contracts` with NOTHING matching in
    // `func.preconditions` is precisely what `dropped_requires_clauses` reports:
    // the gate refused to carry it, so it is not an entry hypothesis.
    f.contracts.push(Contract {
        kind: ContractKind::Requires,
        span: span(),
        body: "a >= 0".to_string(),
    });
    assert!(
        f.preconditions.is_empty(),
        "the fixture must model a DROPPED precondition — one the gate did not carry"
    );

    let formulas = postcondition_formulas(&f);
    assert_eq!(
        formulas.len(),
        2,
        "with a dropped `requires` the split declines: one row per PREDECESSOR, \
         exactly as before this lane: {:?}",
        rendered(&formulas)
    );
    assert_eq!(
        formulas.iter().filter_map(spine_or_arity).collect::<Vec<_>>(),
        vec![2],
        "and the JOIN predecessor's row keeps its two-way disjunction — the shape \
         the dropped-`requires` tripwire was written to read: {:?}",
        rendered(&formulas)
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// The cap — the path-count mutation control.
// ═══════════════════════════════════════════════════════════════════════════

/// The dial, read at three points. `arms` is the number of guard paths reaching
/// the join, and the join is the Return block's only predecessor, so the emitted
/// row count IS the split's behaviour as a function of path count.
///
/// This is also the only test that exhibits the PRE-FIX shape: past the cap the
/// row keeps the `Or([per-path term, ..])` spelling every row had before, which
/// is what makes the comparison a mutation control rather than an assertion
/// about one hand-picked number.
#[test]
fn row_count_tracks_path_count_up_to_the_cap() {
    for arms in [2usize, 3, super::contract_vcs::POSTCONDITION_PATH_SPLIT_CAP] {
        let formulas = postcondition_formulas(&fan(arms));
        assert_eq!(
            formulas.len(),
            arms,
            "{arms} paths must give {arms} rows: {:?}",
            rendered(&formulas)
        );
        for formula in &formulas {
            assert_eq!(spine_or_arity(formula), None, "row must be flat: {formula:?}");
        }
    }
}

/// PAST the cap the row falls back to the single disjunctive spelling — the
/// behaviour every multi-path row had before this lane. Fail-open by
/// construction: the cap can cost capability, never soundness.
#[test]
fn past_the_cap_the_row_keeps_its_disjunction() {
    let arms = super::contract_vcs::POSTCONDITION_PATH_SPLIT_CAP + 1;
    let formulas = postcondition_formulas(&fan(arms));
    assert_eq!(
        formulas.len(),
        1,
        "past the cap: one merged row, exactly as before this lane: {:?}",
        rendered(&formulas)
    );
    assert_eq!(
        spine_or_arity(&formulas[0]),
        Some(arms),
        "and that merged row IS the `Or` over every path — the shape the split \
         removes: {:?}",
        formulas[0]
    );
}
