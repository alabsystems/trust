// Tests for the bool-guard definition walk (`guards::latest_same_block_bool_definition`
// and `guards::BoolDefinitionWalk`): termination on every shape, and the exactness of
// what it resolves, since the guard is used on BOTH edges of a switch.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{LocalDecl, Place, SourceSpan, VerifiableBody};

use super::*;

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn binop(op: BinOp, lhs: Operand, rhs: Operand) -> Rvalue {
    Rvalue::BinaryOp(op, lhs, rhs)
}

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn uint(value: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(value, 32))
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn switch_on(local: usize) -> Terminator {
    Terminator::SwitchInt {
        discr: copy(local),
        targets: vec![(0, BlockId(0))],
        otherwise: BlockId(0),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

/// `_1: u32` and `_2: bool` are parameters; `_3 ..= _last` are bool temps.
fn bool_func(last: usize, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::Bool, name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
        LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
    ];
    locals.extend((3..=last).map(|index| LocalDecl { index, ty: Ty::Bool, name: None }));
    VerifiableFunction {
        name: "walk".to_string(),
        def_path: "test::walk".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 2,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn fixture(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

/// THE CRASH, on real MIR of the ay-dpll shape (`nelson_oppen_check`'s
/// `has_new_eqs |= ..; if !has_new_eqs`; `tests/self_update_bool_guard_realmir.rs` has
/// the reduced source):
/// `bb7: _8 = BitOr(copy _8, move _10); switchInt(move _8)` — `changed |= ..;
/// if !changed { break; }`. The old walk resolved the `BitOr`'s own `_8` operand to
/// the `BitOr` and never returned. The operand is read AT that statement, so nothing
/// before it defines it in-block and it stays the opaque `changed` — exact, because
/// `c' | t == c'`. `_10` is the second call's result (a single `Call` destination),
/// so its own name is exact too.
#[test]
fn self_updated_bool_resolves_its_operand_before_the_update() {
    let func = fixture(include_str!("../tests/fixtures/self_update_bool_switch_guard_mir.json"));
    let switch_block = &func.body.blocks[7];
    assert!(matches!(switch_block.terminator, Terminator::SwitchInt { .. }));

    let resolved = latest_same_block_bool_definition(&func, switch_block, 8)
        .expect("the self-update resolves: opaque old value OR the call result");
    assert_eq!(
        resolved,
        Formula::Or(vec![
            operand_to_formula(&func, &copy(8)),
            operand_to_formula(&func, &copy(10))
        ]),
        "`changed |= reconcile(..)` must resolve to `changed | _10`: neither operand has an \
         in-block definition BEFORE the update, so each is spelled by its own name"
    );

    // Both edges of the real switch lower, and the false edge is the exact negation.
    let true_edge =
        guard_to_formula(&func, &GuardCondition::SwitchIntMatch { discr: copy(8), value: 1 });
    let false_edge =
        guard_to_formula(&func, &GuardCondition::SwitchIntMatch { discr: copy(8), value: 0 });
    assert_eq!(true_edge, resolved);
    assert_eq!(false_edge, Formula::Not(Box::new(resolved)));

    // The join-inlining gate asks the same reaching-definition question and refuses:
    // the old `changed` is not defined in the switch block.
    assert!(!bool_definition_is_switch_block_local(&func, switch_block, 8, 8));
}

/// The same self-update with an IN-BLOCK right operand (`c |= v > 3; if !c { .. }`):
/// the comparison still unfolds while the self-referential operand stays opaque.
#[test]
fn self_update_keeps_unfolding_its_other_operand() {
    let gt3 = assign(3, binop(BinOp::Gt, copy(1), uint(3)));
    let update = assign(4, binop(BinOp::BitOr, copy(4), copy(3)));
    let init = block(0, vec![assign(4, Rvalue::Use(copy(2)))], Terminator::Goto(BlockId(1)));
    let func = bool_func(4, vec![init, block(1, vec![gt3.clone(), update], switch_on(4))]);

    let control = bool_func(4, vec![block(0, vec![gt3], switch_on(3))]);
    let comparison = latest_same_block_bool_definition(&control, &control.body.blocks[0], 3)
        .expect("control: the comparison resolves");

    assert_eq!(
        latest_same_block_bool_definition(&func, &func.body.blocks[1], 4),
        Some(Formula::Or(vec![operand_to_formula(&func, &copy(4)), comparison]))
    );
}

/// Positive control on real MIR: `ok = (x >= 2) & (x <= 9); match ok { .. }` still
/// unfolds to both comparisons, with no opaque bool temp left in it.
#[test]
fn ordinary_single_block_bitand_still_resolves_to_its_comparisons() {
    let func = fixture(include_str!("../tests/fixtures/range_bitand_match_guard_mir.json"));
    let switch_block = &func.body.blocks[0];
    let resolved = latest_same_block_bool_definition(&func, switch_block, 2)
        .expect("a same-block BitAnd of two comparisons resolves");
    let Formula::And(conjuncts) = &resolved else {
        panic!("expected And(Ge, Le), got {resolved:?}");
    };
    assert!(
        matches!(conjuncts.as_slice(), [Formula::Ge(..), Formula::Le(..)]),
        "expected And(Ge, Le), got {resolved:?}"
    );
    let x = operand_to_formula(&func, &copy(1));
    let free = resolved.free_variables();
    assert_eq!(free.len(), 1, "only `x` may remain free, got {free:?}");
    assert!(x.free_variables().is_subset(&free));
    assert!(bool_definition_is_switch_block_local(&func, switch_block, 2, 8));
}

/// The same misreading, as a wrong answer instead of a crash: a leaf REDEFINED later
/// in the block was answered with the later value. `b = a & flag` was resolved as
/// `x > 10 && flag` while the switch tests `x < 5 && flag`.
#[test]
fn a_leaf_resolves_to_the_definition_reaching_its_read_not_the_latest_one() {
    let lt5 = assign(3, binop(BinOp::Lt, copy(1), uint(5)));
    let and = assign(4, binop(BinOp::BitAnd, copy(3), copy(2)));
    let gt10 = assign(3, binop(BinOp::Gt, copy(1), uint(10)));

    let control = bool_func(4, vec![block(0, vec![lt5.clone(), and.clone()], switch_on(4))]);
    let expected = latest_same_block_bool_definition(&control, &control.body.blocks[0], 4)
        .expect("control resolves");

    let func = bool_func(4, vec![block(0, vec![lt5, and, gt10], switch_on(4))]);
    let resolved = latest_same_block_bool_definition(&func, &func.body.blocks[0], 4)
        .expect("the reaching definition resolves");
    assert_eq!(
        resolved, expected,
        "the later `_3 = x > 10` does not reach the BitAnd's read of `_3`"
    );
}

/// An UNRESOLVED leaf keeps its own name only while that name still denotes the value
/// read. Rewritten later in the switch block, `Var(_3)` would name the NEW value on
/// both edges, so the whole definition declines to the opaque discriminant.
#[test]
fn an_unresolved_leaf_rewritten_after_its_read_declines_the_definition() {
    let entry = block(0, vec![assign(3, Rvalue::Use(copy(2)))], Terminator::Goto(BlockId(1)));
    let and = assign(4, binop(BinOp::BitAnd, copy(3), copy(2)));
    let rewrite = assign(3, binop(BinOp::Gt, copy(1), uint(10)));

    let func =
        bool_func(4, vec![entry.clone(), block(1, vec![and.clone(), rewrite], switch_on(4))]);
    assert_eq!(
        latest_same_block_bool_definition(&func, &func.body.blocks[1], 4),
        None,
        "a stale opaque leaf must decline, never be read as the rewritten value"
    );

    // Control: nothing rewrites `_3` after the read — it is then a single static
    // assignment, and its own name is exact.
    let func = bool_func(4, vec![entry, block(1, vec![and], switch_on(4))]);
    let resolved = latest_same_block_bool_definition(&func, &func.body.blocks[1], 4)
        .expect("an unrewritten opaque leaf is exact");
    assert_eq!(
        resolved,
        Formula::And(vec![
            operand_to_formula(&func, &copy(3)),
            operand_to_formula(&func, &copy(2))
        ])
    );
}

/// Termination does not rest on the MIR being well formed. Two blocks whose unique
/// definitions read each other (unreachable in valid MIR, where a unique definition
/// dominates its uses) made the cross-block hop cycle: bb2 -> bb0 -> bb1 -> bb0 -> ...
#[test]
fn a_cross_block_definition_cycle_terminates() {
    let func = bool_func(
        5,
        vec![
            block(
                0,
                vec![assign(4, binop(BinOp::BitAnd, copy(5), copy(2)))],
                Terminator::Goto(BlockId(1)),
            ),
            block(
                1,
                vec![assign(5, binop(BinOp::BitAnd, copy(4), copy(2)))],
                Terminator::Goto(BlockId(2)),
            ),
            block(2, vec![], switch_on(4)),
        ],
    );
    // Any answer is acceptable here; returning at all is the property.
    let _ = latest_same_block_bool_definition(&func, &func.body.blocks[2], 4);
}

/// Shared leaves: `_k = _{k-1} & _{k-1}` forty times is a 2^40-leaf tree to a walk
/// with no budget. Fuel bounds the work; the leaves it does not unfold are
/// single-static-assignment temps, so the answer stays exact.
#[test]
fn shared_leaves_are_bounded_by_fuel() {
    let last = 43;
    let mut stmts = vec![assign(3, binop(BinOp::Lt, copy(1), uint(5)))];
    stmts.extend((4..=last).map(|k| assign(k, binop(BinOp::BitAnd, copy(k - 1), copy(k - 1)))));
    let func = bool_func(last, vec![block(0, stmts, switch_on(last))]);
    let resolved = latest_same_block_bool_definition(&func, &func.body.blocks[0], last);
    assert!(resolved.is_some(), "every leaf is exact (resolved or an SSA temp)");
}
