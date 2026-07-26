//! Recognition of the simplest E6 kernel-import body SHAPES from an extracted
//! [`VerifiableFunction`] — the soundness-critical trust boundary of the
//! compiler-side minting hook.
//!
//! Once a function is certified `Pure ∧ Total ∧ Deterministic ∧ NoPanic`, the
//! kernel-import step must turn its BODY into a defining equation the kernel
//! re-checks (see `trust_spec_elab::admit_constant_function` /
//! `admit_projection_function` and `docs/design-notes/2026-07-15-e6-kernel-import-spec.md`).
//! The correspondence between the minted definition and the function's actual
//! computation rests entirely on this recognition being FAITHFUL: a body that is
//! reported `ConstantUint { value }` must genuinely return exactly that constant.
//! So the recognizer is deliberately CONSERVATIVE — it matches only the two
//! simplest, unambiguous shapes and returns `None` (fail closed → no admission →
//! the call keeps failing closed) for anything else. Widening it (arithmetic,
//! select, `SwitchInt`) is future work, each shape added only when its
//! recognition is provably exact.
//!
//! A pure IR analysis with no `rustc` dependency, unit-testable in isolation.

use crate::{
    BasicBlock, BinOp, BlockId, ConstValue, Operand, Rvalue, Statement, Terminator,
    VerifiableFunction,
};

/// A body shape the kernel-import elaborator can turn into a defining equation.
/// Deliberately minimal; see the module docs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissibleBody {
    /// The body returns exactly a machine-integer literal — `fn f() -> uN { V }`.
    ConstantUint {
        /// The returned value.
        value: u128,
        /// The width of the machine integer, in bits.
        width_bits: u32,
    },
    /// The body returns one of its parameters verbatim — `fn f(.., x, ..) { x }`.
    /// `param` is the 0-based source parameter index.
    Projection {
        /// 0-based index of the returned parameter.
        param: usize,
    },
    /// The body is a single WRAPPING binary arithmetic operation over two
    /// operands, each a parameter or a literal — `fn winc(x) { x.wrapping_add(1) }`,
    /// `fn wsum(x, y) { x.wrapping_add(y) }`. `wrapping_add`/`wrapping_sub`/
    /// `wrapping_mul` are recognized: the Machine-domain elaboration resolves
    /// `+`/`-`/`*` to the fixed-width WRAPPING carrier ops (`<Carrier>.add`/
    /// `.sub`/`.mul` — the `UInt64.sub` wrap is kernel-oracle-tested in
    /// trust-spec-elab), exactly the primitives' unsigned semantics. (An
    /// earlier note here claimed a truncating `-` under an
    /// `ofNat(Nat.op(toNat..))` encoding; that described a superseded
    /// encoding — corrected 2026-07-22 with the evidence cited above.)
    Arithmetic {
        /// The operation.
        op: ArithBinOp,
        /// Left operand.
        left: ArithOperand,
        /// Right operand.
        right: ArithOperand,
    },
    /// The body is a LINEAR CHAIN of wrapping-primitive calls composing one
    /// arithmetic expression over parameters and literals (E6 widening
    /// increment 3) — `fn f(x) { x.wrapping_add(1).wrapping_mul(2) }` as MIR
    /// lowers it: strictly consecutive call blocks, each feeding a fresh
    /// temporary, the last writing the return place. The composed tree is
    /// elaborated fully parenthesized over the SAME Machine-domain wrapping
    /// ops as [`AdmissibleBody::Arithmetic`], so faithfulness composes
    /// node-for-node from the single-op case.
    Composed {
        /// The composed expression tree.
        expr: ArithExpr,
    },
    /// The body compares two parameters and returns one of them — the
    /// `if <cmp> { p_then } else { p_else }` shape, of which `min`/`max` are
    /// canonical (`fn min2(a, b) { if a < b { a } else { b } }`). All indices are
    /// 0-based source parameters.
    Select {
        /// The comparison the branch tests.
        cmp: SelectCmp,
        /// Left operand parameter of the comparison.
        cmp_left: usize,
        /// Right operand parameter of the comparison.
        cmp_right: usize,
        /// Parameter returned when the comparison holds.
        then_param: usize,
        /// Parameter returned otherwise.
        else_param: usize,
    },
}

/// The comparison a [`AdmissibleBody::Select`] branch tests. Only the comparisons
/// the select elaborator supports; `!=`, `>` and `>=` are not recognized (fail
/// closed) — `>`/`>=` could be normalized to `<`/`<=` with swapped operands, a
/// future refinement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectCmp {
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `==`
    Eq,
}

/// A wrapping binary arithmetic operation in an [`AdmissibleBody::Arithmetic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithBinOp {
    /// `wrapping_add`
    Add,
    /// `wrapping_sub` — admitted 2026-07-22 (E6 widening increment 1): the
    /// Machine-domain `-` elaboration is the fixed-width wrapping carrier
    /// sub, matching this primitive's unsigned semantics exactly.
    Sub,
    /// `wrapping_mul`
    Mul,
}

/// An operand of an [`AdmissibleBody::Arithmetic`] body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithOperand {
    /// A 0-based source parameter.
    Param(usize),
    /// A machine-integer literal.
    Const(u128),
}

/// Whether a statement has NO effect on any value — pure bookkeeping the
/// recognizer may skip. Anything NOT on this whitelist is treated as effectful,
/// so a body carrying it fails to match (fail closed); the list only ever grows
/// with statements that are provably value-neutral.
fn is_value_neutral(stmt: &Statement) -> bool {
    matches!(
        stmt,
        Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::PlaceMention(_)
            | Statement::Retag { .. }
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop
    )
}

/// Recognize a [`VerifiableFunction`] whose body is one of the [`AdmissibleBody`]
/// shapes, or `None` (fail closed). CONSERVATIVE: requires a single basic block
/// that `Return`s after exactly one value-carrying statement — an assignment of
/// a constant or a bare parameter to the return place (`_0`). See the module
/// docs for why faithfulness here is soundness-critical.
#[must_use]
pub fn recognize_admissible_body(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    recognize_single_block(func)
        .or_else(|| recognize_arithmetic(func))
        .or_else(|| recognize_select(func))
        .or_else(|| recognize_use_chain(func))
        .or_else(|| recognize_call_chain(func))
}

/// Linear wrapping-call chain (E6 widening increment 3, 2026-07-22): N ≥ 2
/// consecutive call blocks — each a `core::num` wrapping primitive whose
/// operands are literals, parameters, or PRIOR chain temporaries, whose
/// destination is a fresh bare temporary (never rewritten), and whose target
/// is exactly the next block — with the LAST call writing the bare return
/// place and targeting a bookkeeping-only `Return` block.
///
/// FAITHFULNESS: each node is the recognized primitive (the same
/// [`arith_op`] gate as the single-call shape), operands resolve to the
/// values the temporaries carry by construction (single assignment, linear
/// control flow, value-neutral statements only), so the composed tree IS the
/// body's dataflow; the elaborator renders it fully parenthesized over the
/// same Machine-domain wrapping ops. Fail-closed on: any non-primitive
/// callee, any branching/diverging/reordered target, any projected place,
/// any temporary rewrite, any read of an unresolved local, and fewer than
/// two calls (the single-call shape stays with [`recognize_arithmetic`]).
fn recognize_call_chain(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let blocks = &func.body.blocks;
    if blocks.len() < 3 {
        return None;
    }
    let (ret_blk, call_blks) = blocks.split_last()?;
    if !matches!(ret_blk.terminator, Terminator::Return)
        || ret_blk.stmts.iter().any(|s| !is_value_neutral(s))
    {
        return None;
    }
    if call_blks.len() < 2 {
        return None;
    }
    let mut env: std::collections::BTreeMap<usize, ArithExpr> = (1..=func.body.arg_count)
        .map(|i| (i, ArithExpr::Operand(ArithOperand::Param(i - 1))))
        .collect();
    let mut result: Option<ArithExpr> = None;
    for (index, blk) in call_blks.iter().enumerate() {
        if blk.stmts.iter().any(|s| !is_value_neutral(s)) {
            return None;
        }
        let Terminator::Call { func: callee, args, dest, target, .. } = &blk.terminator else {
            return None;
        };
        let next = blocks.get(index + 1)?;
        if *target != Some(next.id) || !dest.projections.is_empty() {
            return None;
        }
        let op = arith_op(callee)?;
        let resolve = |operand: &Operand| -> Option<ArithExpr> {
            match operand {
                Operand::Constant(ConstValue::Uint(value, _)) => {
                    u128::try_from(*value).ok().map(|v| ArithExpr::Operand(ArithOperand::Const(v)))
                }
                Operand::Copy(p) | Operand::Move(p) => {
                    if !p.projections.is_empty() {
                        return None;
                    }
                    env.get(&p.local).cloned()
                }
                _ => None,
            }
        };
        let [a, b] = &args[..] else {
            return None;
        };
        let node = ArithExpr::Bin {
            op,
            left: Box::new(resolve(a)?),
            right: Box::new(resolve(b)?),
        };
        let is_last = index == call_blks.len() - 1;
        if dest.local == 0 {
            if !is_last {
                return None; // the return place is written only by the LAST call
            }
            result = Some(node);
        } else {
            if is_last {
                return None; // the last call must produce the return value
            }
            if env.insert(dest.local, node).is_some() {
                return None; // temporary rewrite — single assignment only
            }
        }
    }
    Some(AdmissibleBody::Composed { expr: result? })
}

/// Multi-statement straight-line `Use`-chain (E6 widening increment 2,
/// 2026-07-22): a single returning block whose every value statement assigns
/// a constant or an already-resolved bare local (`Copy`/`Move`) to a bare
/// local — value-identity copies through temporaries, resolved by
/// substitution to the SAME `ConstantUint`/`Projection` shapes the
/// single-statement recognizer emits (no new admission vocabulary, no
/// elaborator change).
///
/// FAITHFULNESS: `Rvalue::Use` is value identity, so `_0`'s final value is
/// exactly the resolution of its LAST write through the chain, and every
/// non-bookkeeping statement is such a copy — no other effect exists to
/// misrepresent. Fail-closed on: any projection (read or write side), any
/// non-`Use` rvalue, any read of a local without a resolved value (including
/// reads of `_0` itself — untracked by construction), and a body that never
/// writes `_0`. Requires at least TWO value statements so the
/// single-statement shape stays owned by [`recognize_single_block`] and
/// previously-admitted bodies keep their recognizer unchanged.
fn recognize_use_chain(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let [block] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    #[derive(Clone, Copy)]
    enum Resolved {
        Const { value: u128, width_bits: u32 },
        Param(usize),
    }
    let mut env: std::collections::BTreeMap<usize, Resolved> =
        (1..=func.body.arg_count).map(|i| (i, Resolved::Param(i - 1))).collect();
    let mut ret: Option<Resolved> = None;
    let mut value_stmts = 0usize;
    for stmt in &block.stmts {
        if is_value_neutral(stmt) {
            continue;
        }
        value_stmts += 1;
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };
        if !place.projections.is_empty() {
            return None;
        }
        let value = match rvalue {
            Rvalue::Use(Operand::Constant(ConstValue::Uint(value, width_bits))) => {
                Resolved::Const { value: *value, width_bits: *width_bits }
            }
            Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
                if !p.projections.is_empty() {
                    return None;
                }
                *env.get(&p.local)?
            }
            _ => return None,
        };
        if place.local == 0 {
            ret = Some(value);
        } else {
            env.insert(place.local, value);
        }
    }
    if value_stmts < 2 {
        return None;
    }
    match ret? {
        Resolved::Const { value, width_bits } => {
            Some(AdmissibleBody::ConstantUint { value, width_bits })
        }
        Resolved::Param(param) => Some(AdmissibleBody::Projection { param }),
    }
}

/// The single wrapping-arithmetic shape: a two-block body whose entry is a
/// `Call` to a primitive `wrapping_add`/`wrapping_mul` on two operands (each a
/// parameter or a literal), assigned to the return place, returning in the next
/// block. Fail-closed on anything else, including `wrapping_sub` (whose encoding
/// differs) and any callee not under the `core::num` primitive path (so a user
/// function merely NAMED `wrapping_add` is never mistaken for the primitive).
fn recognize_arithmetic(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let [call_blk, ret_blk] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(ret_blk.terminator, Terminator::Return)
        || ret_blk.stmts.iter().any(|s| !is_value_neutral(s))
        || call_blk.stmts.iter().any(|s| !is_value_neutral(s))
    {
        return None;
    }
    let Terminator::Call { func: callee, args, dest, target, .. } = &call_blk.terminator else {
        return None;
    };
    if dest.local != 0 || !dest.projections.is_empty() || *target != Some(ret_blk.id) {
        return None;
    }
    let [op1, op2] = &args[..] else {
        return None;
    };
    let op = arith_op(callee)?;
    Some(AdmissibleBody::Arithmetic {
        op,
        left: arith_operand(op1, func.body.arg_count)?,
        right: arith_operand(op2, func.body.arg_count)?,
    })
}

/// The wrapping arithmetic op a callee path denotes, requiring the `core::num`
/// primitive path so a same-named user function is not matched.
///
/// `wrapping_sub` ADMITTED (E6 widening increment 1, 2026-07-22): the former
/// exclusion note ("its encoding does not match the machine `-` elaboration")
/// predated trust-spec-elab's machine-subtraction landing. Today the Machine
/// domain elaborates `-` as the fixed-width WRAPPING carrier sub
/// (trust-spec-elab lib.rs "`-` denotes the DOMAIN's subtraction: … wrapping
/// `<Carrier>.sub` over a machine domain"), which is exactly
/// `u{8,16,32,64}::wrapping_sub`'s semantics — and `ty_to_domain` already
/// restricts admission to UNSIGNED carriers, so the signed case never
/// reaches this recognizer's consumers. Faithfulness pinned by
/// `widening_battery_census_targets_currently_refuse`'s flipped first pin.
fn arith_op(callee: &str) -> Option<ArithBinOp> {
    if !callee.contains("core::num") {
        return None;
    }
    if callee.contains("wrapping_add") {
        Some(ArithBinOp::Add)
    } else if callee.contains("wrapping_sub") {
        Some(ArithBinOp::Sub)
    } else if callee.contains("wrapping_mul") {
        Some(ArithBinOp::Mul)
    } else {
        None
    }
}

/// A composed wrapping-arithmetic expression tree (see
/// [`AdmissibleBody::Composed`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArithExpr {
    /// A leaf operand.
    Operand(ArithOperand),
    /// A wrapping binary node.
    Bin {
        /// The operation.
        op: ArithBinOp,
        /// Left subtree.
        left: Box<ArithExpr>,
        /// Right subtree.
        right: Box<ArithExpr>,
    },
}

/// An arithmetic operand: a bare parameter (`1..=arg_count`) or a machine-integer
/// literal.
fn arith_operand(op: &Operand, arg_count: usize) -> Option<ArithOperand> {
    match op {
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty() && p.local >= 1 && p.local <= arg_count =>
        {
            Some(ArithOperand::Param(p.local - 1))
        }
        Operand::Constant(ConstValue::Uint(v, _)) => Some(ArithOperand::Const(*v)),
        _ => None,
    }
}

/// The single-block shapes: a constant return or a bare-parameter projection.
fn recognize_single_block(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    // Exactly one basic block, returning.
    let [block] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    // Exactly one non-bookkeeping statement.
    let mut effectful = block.stmts.iter().filter(|s| !is_value_neutral(s));
    let assign = effectful.next()?;
    if effectful.next().is_some() {
        return None;
    }
    // …an assignment to the return place `_0` (a bare local, no projections).
    let Statement::Assign { place, rvalue, .. } = assign else {
        return None;
    };
    if place.local != 0 || !place.projections.is_empty() {
        return None;
    }
    match rvalue {
        // `_0 = const V` — a machine-integer literal return.
        Rvalue::Use(Operand::Constant(ConstValue::Uint(value, width_bits))) => {
            Some(AdmissibleBody::ConstantUint { value: *value, width_bits: *width_bits })
        }
        // `_0 = _i` (copy/move a bare parameter local) — a projection. Parameters
        // are locals `1..=arg_count` (local `0` is the return place), so a
        // returned local `i` in that range is 0-based source parameter `i-1`.
        Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
            if p.projections.is_empty() && p.local >= 1 && p.local <= func.body.arg_count {
                Some(AdmissibleBody::Projection { param: p.local - 1 })
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The select shape — `if <cmp of two parameters> { p_then } else { p_else }` — as
/// rustc lowers it: a four-block diamond
/// - entry: `_c = <cmp>(param, param); switchInt(_c) -> [0: bb_false, otherwise: bb_true]`
/// - true / false: `_t = <param>; goto bb_join`  (the SAME temp `_t`, the SAME join)
/// - join: `_0 = _t; return`
///
/// Every deviation fails closed. The `switchInt` sends `0` (the comparison being
/// FALSE) to the false branch and everything else (TRUE) to `otherwise`, so the
/// `otherwise` branch is `then` and the `0` branch is `else`.
fn recognize_select(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let blocks = &func.body.blocks;
    if blocks.len() != 4 {
        return None;
    }
    let n = func.body.arg_count;
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);

    // Entry: one comparison of two parameters, then a two-way switch on it.
    let entry = &blocks[0];
    let cmp_stmt = sole_effectful(&entry.stmts)?;
    let Statement::Assign { place: cmp_place, rvalue: Rvalue::BinaryOp(binop, opl, opr), .. } =
        cmp_stmt
    else {
        return None;
    };
    if !cmp_place.projections.is_empty() {
        return None;
    }
    let cmp = select_cmp(binop)?;
    let cmp_left = param_of_operand(opl, n)?;
    let cmp_right = param_of_operand(opr, n)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if bare_local(discr)? != cmp_place.local {
        return None;
    }
    if targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    let false_blk = by_id(targets[0].1)?;
    let true_blk = by_id(*otherwise)?;

    // Each branch assigns one temp from a parameter, then jumps to the join.
    let (then_param, then_temp, then_join) = branch_arm(true_blk, n)?;
    let (else_param, else_temp, else_join) = branch_arm(false_blk, n)?;
    if then_temp != else_temp || then_join != else_join {
        return None;
    }

    // Join: return the selected value. Two equivalent spellings:
    //  - O0: the branches assigned a TEMP and the join copies it to the return
    //    place (`_0 = _temp; return`);
    //  - -O: the branches assigned the RETURN PLACE `_0` directly and the join
    //    is a bare `return` (only value-neutral bookkeeping).
    let join = by_id(then_join)?;
    if !matches!(join.terminator, Terminator::Return) {
        return None;
    }
    if then_temp == 0 {
        // Direct-to-return form: the join must carry NO effectful statement.
        if join.stmts.iter().any(|s| !is_value_neutral(s)) {
            return None;
        }
    } else {
        let Statement::Assign { place: ret_place, rvalue: Rvalue::Use(ret_op), .. } =
            sole_effectful(&join.stmts)?
        else {
            return None;
        };
        if ret_place.local != 0
            || !ret_place.projections.is_empty()
            || bare_local(ret_op)? != then_temp
        {
            return None;
        }
    }
    Some(AdmissibleBody::Select { cmp, cmp_left, cmp_right, then_param, else_param })
}

/// The sole non-bookkeeping statement, or `None` if there is not exactly one.
fn sole_effectful(stmts: &[Statement]) -> Option<&Statement> {
    let mut it = stmts.iter().filter(|s| !is_value_neutral(s));
    let first = it.next()?;
    if it.next().is_some() {
        return None;
    }
    Some(first)
}

/// The bare local a `Copy`/`Move` operand names (no projections), else `None`.
fn bare_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// The 0-based source parameter a `Copy`/`Move` operand names — a bare local in
/// `1..=arg_count` (local 0 is the return place) — else `None`.
fn param_of_operand(op: &Operand, arg_count: usize) -> Option<usize> {
    let local = bare_local(op)?;
    (local >= 1 && local <= arg_count).then_some(local - 1)
}

/// The select comparison a `BinOp` denotes, or `None` if unsupported.
fn select_cmp(binop: &BinOp) -> Option<SelectCmp> {
    Some(match binop {
        BinOp::Lt => SelectCmp::Lt,
        BinOp::Le => SelectCmp::Le,
        BinOp::Eq => SelectCmp::Eq,
        _ => return None,
    })
}

/// A select branch block: `_temp = <param>; goto <join>`. Returns
/// `(param_index, temp_local, join_block)`, else `None`.
fn branch_arm(block: &BasicBlock, arg_count: usize) -> Option<(usize, usize, BlockId)> {
    let Terminator::Goto(join) = &block.terminator else {
        return None;
    };
    let Statement::Assign { place, rvalue: Rvalue::Use(op), .. } = sole_effectful(&block.stmts)?
    else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let param = param_of_operand(op, arg_count)?;
    Some((param, place.local, *join))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BasicBlock, BlockId, Place, Projection, SourceSpan, Ty, VerifiableBody, VerifiableFunction,
    };

    fn func(arg_count: usize, stmts: Vec<Statement>, term: Terminator) -> VerifiableFunction {
        VerifiableFunction {
            name: "f".into(),
            def_path: "crate::f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: Vec::new(),
                blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: term }],
                arg_count,
                return_ty: Ty::Unit,
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    fn func_blocks(arg_count: usize, blocks: Vec<BasicBlock>) -> VerifiableFunction {
        let mut f = func(arg_count, Vec::new(), Terminator::Return);
        f.body.blocks = blocks;
        f
    }

    fn two_block_call(callee: &str, args: Vec<Operand>, dest: Place) -> VerifiableFunction {
        func_blocks(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: callee.into(),
                        args,
                        dest,
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: crate::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        )
    }

    /// R4 §1-executor FALSIFICATION BATTERY, part 1 (2026-07-22, written
    /// BEFORE any E6 recognizer widening): the census-motivated widening
    /// TARGETS, pinned refused at the current boundary. Each pin may flip
    /// only in a commit that lands that ONE shape with its faithfulness
    /// argument and elaborator arm — a widening that flips a pin as a side
    /// effect of something else is a red flag, not progress.
    #[test]
    fn widening_battery_census_targets_currently_refuse() {
        // (1) wrapping_sub: FLIPPED 2026-07-22 (E6 widening increment 1).
        // The historical exclusion predated trust-spec-elab's machine
        // subtraction; the Machine domain now elaborates `-` as the wrapping
        // carrier sub — exactly this primitive's unsigned semantics — and
        // admission is already restricted to unsigned carriers. The pin flips
        // POSITIVE with the shape it recognizes.
        let sub = two_block_call(
            "core::num::<impl u64>::wrapping_sub",
            vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(1, 64))],
            Place::local(0),
        );
        assert!(
            matches!(
                recognize_admissible_body(&sub),
                Some(AdmissibleBody::Arithmetic {
                    op: ArithBinOp::Sub,
                    left: ArithOperand::Param(0),
                    right: ArithOperand::Const(1),
                })
            ),
            "wrapping_sub now admits as machine wrapping subtraction"
        );

        // (2) FLIPPED 2026-07-22 (E6 widening increment 2): the two-write
        // straight-line body resolves by Use-chain substitution to its FINAL
        // dataflow — the last `_0` write wins, exactly the param projection.
        let two_writes = func(
            1,
            vec![
                assign(Place::local(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64)))),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1)))),
            ],
            Terminator::Return,
        );
        assert!(
            matches!(
                recognize_admissible_body(&two_writes),
                Some(AdmissibleBody::Projection { param: 0 })
            ),
            "the final dataflow, not the first write"
        );
        // Temp-chain form: `t = p0; _0 = t` resolves through the temporary.
        let via_temp = func(
            1,
            vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(2)))),
            ],
            Terminator::Return,
        );
        assert!(matches!(
            recognize_admissible_body(&via_temp),
            Some(AdmissibleBody::Projection { param: 0 })
        ));
    }

    /// E6 widening increment 3 TARGET (written red, 2026-07-22): a linear
    /// multi-block chain of wrapping-primitive calls composing an arithmetic
    /// expression. Flips only in the commit landing the composed-expression
    /// vocabulary with its faithfulness argument.
    #[test]
    fn widening_battery_call_chain_target_currently_refuses() {
        // b0: _2 = wrapping_add(p0, 1) -> b1: _0 = wrapping_mul(_2, 2) -> b2: return
        let chain = func_blocks(
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: "core::num::<impl u64>::wrapping_add".into(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: crate::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: "core::num::<impl u64>::wrapping_mul".into(),
                        args: vec![
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(2, 64)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: crate::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        );
        // FLIPPED 2026-07-22 (E6 widening increment 3): the chain composes to
        // the exact expression tree, node-for-node.
        assert_eq!(
            recognize_admissible_body(&chain),
            Some(AdmissibleBody::Composed {
                expr: ArithExpr::Bin {
                    op: ArithBinOp::Mul,
                    left: Box::new(ArithExpr::Bin {
                        op: ArithBinOp::Add,
                        left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                        right: Box::new(ArithExpr::Operand(ArithOperand::Const(1))),
                    }),
                    right: Box::new(ArithExpr::Operand(ArithOperand::Const(2))),
                },
            })
        );
    }

    /// E6 widening increment 3's forgery pins (pre-landed): call-chain shapes
    /// no composed-expression widening may ever admit.
    #[test]
    fn widening_battery_call_chain_forgeries_never_admit() {
        let prim_call = |callee: &str, args: Vec<Operand>, dest: Place, target: Option<BlockId>| {
            Terminator::Call {
                func: callee.into(),
                args,
                dest,
                target,
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: crate::UnwindEdge::Unreachable,
            }
        };
        // (1) a NON-primitive call in the middle of the chain: arbitrary user
        // semantics must never compose into an admitted expression.
        let user_middle = func_blocks(
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: prim_call(
                        "my_crate::helper",
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(2),
                        Some(BlockId(1)),
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: Vec::new(),
                    terminator: prim_call(
                        "core::num::<impl u64>::wrapping_add",
                        vec![
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        Place::local(0),
                        Some(BlockId(2)),
                    ),
                },
                BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        );
        assert!(recognize_admissible_body(&user_middle).is_none(), "user call in chain");

        // (2) a BRANCHING chain (a call target that is not the next linear
        // block): control flow the composed expression would erase.
        let branching = func_blocks(
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: prim_call(
                        "core::num::<impl u64>::wrapping_add",
                        vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        Place::local(0),
                        Some(BlockId(2)),
                    ),
                },
                BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(2),
                    stmts: Vec::new(),
                    terminator: Terminator::Goto(BlockId(1)),
                },
            ],
        );
        assert!(recognize_admissible_body(&branching).is_none(), "non-linear chain");
    }

    /// E6 widening increment 2's OWN forgery pins: chain shapes the Use-chain
    /// recognizer must refuse forever.
    #[test]
    fn widening_battery_chain_forgeries_never_admit() {
        // (1) a chain containing a NON-Use rvalue (any computation) — the
        // chain's faithfulness argument is value identity only.
        let computes = func(
            1,
            vec![
                assign(
                    Place::local(2),
                    Rvalue::BinaryOp(
                        crate::BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    ),
                ),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2)))),
            ],
            Terminator::Return,
        );
        assert!(recognize_admissible_body(&computes).is_none(), "computation in a Use-chain");

        // (2) a read of an UNRESOLVED local (uninitialized temp).
        let uninit = func(
            1,
            vec![
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3)))),
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
            ],
            Terminator::Return,
        );
        assert!(recognize_admissible_body(&uninit).is_none(), "uninitialized read");

        // (3) a projected WRITE mid-chain (partial state the resolution
        // would erase).
        let mut proj_place = Place::local(2);
        proj_place.projections.push(Projection::Field(0));
        let projected = func(
            1,
            vec![
                assign(proj_place, Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1)))),
            ],
            Terminator::Return,
        );
        assert!(recognize_admissible_body(&projected).is_none(), "projected write");
    }

    /// R4 §1-executor FALSIFICATION BATTERY, part 2: shapes NO widening may
    /// EVER admit. If any of these pins goes green, a false definitional
    /// import has been armed — treat as a soundness incident, not a test
    /// update.
    #[test]
    fn widening_battery_shapes_no_widening_may_ever_admit() {
        let operands =
            || vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(1, 64))];

        // (1) a USER function merely named wrapping_add, outside the
        // core::num primitive path: admitting it imports arbitrary user
        // semantics as the primitive.
        let user = two_block_call("my_crate::wrapping_add", operands(), Place::local(0));
        assert!(recognize_admissible_body(&user).is_none(), "user-named primitive forgery");

        // (2) the genuine primitive but the destination writes a PROJECTION
        // of the return place — a partial-return the imported constant would
        // misrepresent as the whole value.
        let mut projected_dest = Place::local(0);
        projected_dest.projections.push(Projection::Field(0));
        let partial = two_block_call(
            "core::num::<impl u64>::wrapping_add",
            operands(),
            projected_dest,
        );
        assert!(recognize_admissible_body(&partial).is_none(), "projected-return forgery");

        // (3) the genuine primitive with an EFFECTFUL statement beside the
        // recognized value flow — hidden state change the import would erase.
        let mut effectful = two_block_call(
            "core::num::<impl u64>::wrapping_add",
            operands(),
            Place::local(0),
        );
        effectful.body.blocks[0].stmts.push(assign(
            Place::local(2),
            Rvalue::Use(Operand::Constant(ConstValue::Uint(9, 64))),
        ));
        assert!(recognize_admissible_body(&effectful).is_none(), "effectful-sibling forgery");

        // (4) a DIVERGING call (no return target): there is no returned value
        // for a definitional import to be faithful to.
        let mut diverging = two_block_call(
            "core::num::<impl u64>::wrapping_add",
            operands(),
            Place::local(0),
        );
        if let Terminator::Call { target, .. } = &mut diverging.body.blocks[0].terminator {
            *target = None;
        }
        assert!(recognize_admissible_body(&diverging).is_none(), "diverging-call forgery");
    }

    #[test]
    fn recognizes_the_optimized_select_form() {
        use crate::BinOp;
        // The SAME min2 under -O: the branches write the RETURN PLACE `_0`
        // directly and the join is a bare `return` (only bookkeeping) — the
        // form compiletest's run-pass `-O` produces. Semantically identical
        // select; must recognize.
        let f = func_blocks(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1))))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2))))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            })
        );
        // An EFFECTFUL join statement in the direct-to-return form fails closed
        // (it could overwrite the selected value).
        let mut g = f.clone();
        g.body.blocks[3]
            .stmts
            .push(assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2)))));
        assert_eq!(recognize_admissible_body(&g), None);
    }

    #[test]
    fn recognizes_a_select_min2() {
        use crate::BinOp;
        // fn min2(a, b) -> u64 { if a < b { a } else { b } } — the exact 4-block
        // rustc lowering: compare into _4, switch, each branch writes temp _3,
        // join returns _3.
        let f = func_blocks(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1), // otherwise / true branch: a < b ⇒ return a
                    stmts: vec![assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(1))))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2), // 0 / false branch ⇒ return b
                    stmts: vec![assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(2))))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3))))],
                    terminator: Terminator::Return,
                },
            ],
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0, // a < b true ⇒ a (param 0)
                else_param: 1, // else ⇒ b (param 1)
            })
        );

        // max2: same shape, branches swapped (then=b, else=a).
        let mut g = f.clone();
        g.body.blocks[1].stmts =
            vec![assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(2))))];
        g.body.blocks[2].stmts =
            vec![assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(1))))];
        assert_eq!(
            recognize_admissible_body(&g),
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 1,
                else_param: 0,
            })
        );

        // Fail closed if the two branches write DIFFERENT temps (not a clean
        // select diamond).
        let mut bad = f.clone();
        bad.body.blocks[2].stmts =
            vec![assign(Place::local(5), Rvalue::Use(Operand::Copy(Place::local(2))))];
        assert_eq!(recognize_admissible_body(&bad), None);
    }

    #[test]
    fn recognizes_wrapping_arithmetic() {
        // fn winc(x: u64) -> u64 { x.wrapping_add(1) } — the two-block Call shape.
        let call = |callee: &str, a: Operand, b: Operand| Terminator::Call {
            func: callee.into(),
            args: vec![a, b],
            dest: Place::local(0),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
    unwind: crate::UnwindEdge::Unreachable,
        };
        let winc = |t: Terminator, argc: usize| {
            func_blocks(
                argc,
                vec![
                    BasicBlock { id: BlockId(0), stmts: Vec::new(), terminator: t },
                    BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
                ],
            )
        };
        let f = winc(
            call(
                "core::num::<impl u64>::wrapping_add",
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(1, 64)),
            ),
            1,
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::Arithmetic {
                op: ArithBinOp::Add,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(1),
            })
        );
        // wsum(x, y) = x.wrapping_add(y).
        let g = winc(
            call(
                "core::num::<impl u64>::wrapping_add",
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            2,
        );
        assert_eq!(
            recognize_admissible_body(&g),
            Some(AdmissibleBody::Arithmetic {
                op: ArithBinOp::Add,
                left: ArithOperand::Param(0),
                right: ArithOperand::Param(1),
            })
        );
        // A user function merely NAMED wrapping_add (not under core::num) fails
        // closed; wrapping_sub (encoding differs) fails closed.
        let bad = winc(
            call("crate::wrapping_add", Operand::Copy(Place::local(1)), Operand::Copy(Place::local(1))),
            1,
        );
        assert_eq!(recognize_admissible_body(&bad), None);
        // wrapping_sub: recognized since the 2026-07-22 E6 widening
        // increment 1 (the Machine-domain `-` elaboration is the wrapping
        // carrier sub — see arith_op's doc; the widening battery carries the
        // authoritative pins).
        let sub = winc(
            call(
                "core::num::<impl u64>::wrapping_sub",
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(1, 64)),
            ),
            1,
        );
        assert_eq!(
            recognize_admissible_body(&sub),
            Some(AdmissibleBody::Arithmetic {
                op: ArithBinOp::Sub,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(1),
            })
        );
    }

    #[test]
    fn recognizes_a_constant_return() {
        // `fn answer() -> u64 { 42 }` with bookkeeping around it.
        let f = func(
            0,
            vec![
                Statement::StorageLive(0),
                assign(Place::local(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64)))),
                Statement::Nop,
            ],
            Terminator::Return,
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::ConstantUint { value: 42, width_bits: 64 })
        );
    }

    #[test]
    fn recognizes_a_projection() {
        // `fn fst(x, y) -> u64 { x }` — returns param 0 (local 1).
        let f = func(
            2,
            vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1))))],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&f), Some(AdmissibleBody::Projection { param: 0 }));
        // `{ y }` returns param 1 (local 2).
        let g = func(
            2,
            vec![assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(2))))],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&g), Some(AdmissibleBody::Projection { param: 1 }));
    }

    #[test]
    fn fails_closed_outside_the_recognized_shapes() {
        // A non-Return terminator.
        assert_eq!(
            recognize_admissible_body(&func(0, Vec::new(), Terminator::Unreachable)),
            None
        );
        // Two value-carrying statements: recognized since the 2026-07-22
        // Use-chain widening (increment 2) — the FINAL dataflow wins, and
        // this body genuinely returns the constant. The chain's own forgery
        // pins live in widening_battery_chain_forgeries_never_admit.
        let two = func(
            1,
            vec![
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64)))),
            ],
            Terminator::Return,
        );
        assert_eq!(
            recognize_admissible_body(&two),
            Some(AdmissibleBody::ConstantUint { value: 1, width_bits: 64 })
        );
        // Assigning THROUGH a reference (a Deref projection), not the bare return.
        let deref = func(
            1,
            vec![assign(
                Place { local: 0, projections: vec![Projection::Deref] },
                Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))),
            )],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&deref), None);
        // Returning a NON-parameter local (out of `1..=arg_count`).
        let non_param = func(
            1,
            vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(7))))],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&non_param), None);
        // Returning a projection OF a parameter (`x.0`), not the parameter itself.
        let field = func(
            1,
            vec![assign(
                Place::local(0),
                Rvalue::Use(Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] })),
            )],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&field), None);
        // Multiple blocks (not a straight-line return).
        assert_eq!(
            recognize_admissible_body(&VerifiableFunction {
                body: VerifiableBody {
                    blocks: vec![
                        BasicBlock {
                            id: BlockId(0),
                            stmts: Vec::new(),
                            terminator: Terminator::Goto(BlockId(1)),
                        },
                        BasicBlock {
                            id: BlockId(1),
                            stmts: Vec::new(),
                            terminator: Terminator::Return,
                        },
                    ],
                    ..func(0, Vec::new(), Terminator::Return).body
                },
                ..func(0, Vec::new(), Terminator::Return)
            }),
            None
        );
    }
}
