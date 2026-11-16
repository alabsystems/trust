// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Plan step 3.1 (docs/design/2026-10-02-step3-lean-through-trust-ir.md §9, family (a)): the
//! carrier gate's SELECT, COMPARISON-VALUE and BOOLEAN-VALUE families.
//!
//! # What is read, and from where
//!
//! The reader decides a [`FamilyReading`] from the ACTUAL emitted [`Function`] alone, in either
//! of the two spellings a producer emits today:
//!
//! * the sealed-plan emitter (`trust-clean-ir`) spells `if c then t else e` as ONE block —
//!   `icmp` then `select` then `ret` — and the Bool operations in TrustIR's boolean vocabulary
//!   (WS5.13): `BinOp::{BAnd,BOr}` at `bool` for the connectives and `bxor %b, true` (the
//!   parameter LEFT, the constant `true` RIGHT) for `not`. The pre-WS5.13 spellings
//!   (`UnOp::Not`, which the trust-ir validator refuses at scalar `bool`, and the integer
//!   `BinOp::{And,Or}`) are no producer's any more and are refused at stage `instruction`;
//! * Clean's compiler at the Rust ABI (Clean `520ba9b3e`, plan step 3.2, recorded in
//!   docs/first-party-pin-ledger.md entry (j); NOT pinned by Trust yet) spells the same `if` as an
//!   `icmp` + `condbr` diamond with one `ret` per arm, the Bool operations as `select`, and `==`
//!   as `icmp eq`.
//!
//! The reader admits exactly those spellings, every instruction accounted for (no dead
//! constant, no second branch, no block argument, no join block), at one exact
//! `UInt8/16/32/64` carrier or at `Bool`.
//!
//! # Where the term comes from
//!
//! NOT from a new rendering in this crate. The reading's operands are handed to the SAME side-B
//! producers the MIR lane's `admit_lowering` reflects through (`trust_spec_elab::
//! admit_select_function`, `admit_select_literal_function`, `admit_select_operands_function`,
//! `admit_select_beq_function`, `admit_comparison_function`, `admit_bool_value_function`), which
//! mint the reflected definition through the elaborator into a SCRATCH clone of the environment;
//! the minted value is then put to `trust_clean_origin::check_faithful_for_name` against the
//! kernel declaration at the carrier. Those producers were written for the opposite (Rust →
//! Clean) direction and already carry their own `docs/TCB.md` rows; reusing them keeps this
//! family from co-authoring a second spelling of `ite`/`decide`/`and` that would have to agree
//! with the elaborator's intensionally (the kernel compares a stuck `ite` argument-wise).
//!
//! # What the plan may and may not decide
//!
//! The body decides the family, the comparison and every operand. The sealed plan must then
//! agree field for field (stage `plan-shape`). Exactly one choice is the plan's, and it is a
//! choice between producers the body admits EQUALLY: an `icmp eq` select is both
//! `if a = b` (`CleanOriginShape::Select { cmp: Eq }`, propositional equality) and `if a == b`
//! (`SelectBeq`, `BEq` lifted to `true`), two kernel terms that are not definitionally equal
//! (`landing5_selection_probes::l5_p3`) and that the TrustIR body cannot tell apart, because
//! both compute equality of the two operands. The plan names which spelling the declaration
//! uses; the term is still built from the BODY's operands, so a plan can only pick which of two
//! equal-valued renderings the kernel compares against, never what the body computes. A plan
//! that picks the wrong one is refused by the kernel, not admitted.
//!
//! # Not targeted at the join (yet), and why
//!
//! [`crate::gate_targets`] is unchanged: these families are NOT carrier-gate targets of the
//! rustc mixed-link join. The frozen join (`crates/trust-thir-lower/src/clean_origin_join.rs`)
//! makes a targeted row fatal unless it also carries an independent kernel-TV companion, and
//! neither pinned denotation copy (clean-reflect at Clean `89aa4c92`, trust-ir-build's
//! `clean_backend_tv` mirror at trust-ir `1814992a`) has a rule for `Inst::Select`, an
//! `ICmp`-valued `Bool` or a `Bool` connective, while the source side has no `ite` rule. So a
//! row of these families still publishes at its historical tier; this module is the gate's
//! coverage, kernel-probed, waiting on that companion (or on the join's re-scoping under a
//! waiver).
//!
//! Zero authority by itself: only [`crate::admit_clean_origin_family`] mints a token.

use clean_kernel::env::Environment;
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use trust_clean_carrier::CleanType;
use trust_clean_origin::{CleanOriginPlan, CleanOriginShape, FaithfulnessMethod};
use trust_ir::inst::ICmpOp;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, ValueId};
use trust_ir::{BinOp, Constant, Function, Inst};
use trust_spec_elab::{BoolValueKind, CmpOperand, Domain, MachineUIntWidth, SelectOperand};
use trust_types::admissible_body::{ArithOperand, BoolBinOp, SelectCmp};

use crate::{GateRefusal, TokenCarrier, UIntCarrier};

/// How a branch was spelled.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BranchSpelling {
    /// One block: `icmp`, `select`, `ret` (the sealed-plan emitter).
    SelectInst,
    /// Three blocks: `icmp` + `condbr` into two parameter-free arms, each ending in its own
    /// single-value `ret` (Clean's compiler at the Rust ABI).
    Diamond,
}

/// How a Bool operation was spelled.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BoolSpelling {
    /// `bxor %b, true` / `BinOp::{BAnd,BOr}` at `bool` (the sealed-plan emitter, WS5.13).
    Operator,
    /// `select` over `bool` constants (Clean's compiler at the Rust ABI).
    Select,
}

/// One resolved operand: an entry parameter or an in-range literal of the carrier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Leaf {
    /// 0-based source parameter.
    Param(usize),
    /// An in-range unsigned literal.
    Literal(u128),
}

/// What the body-only reader saw. Zero authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FamilyReading {
    /// `if lhs <pred> rhs then then_arm else else_arm` at one UInt carrier.
    Select {
        spelling: BranchSpelling,
        pred: ICmpOp,
        lhs: Leaf,
        rhs: Leaf,
        then_arm: Leaf,
        else_arm: Leaf,
        carrier: UIntCarrier,
    },
    /// `lhs <pred> rhs` over two UInt parameters, returned as `Bool`.
    Comparison { pred: ICmpOp, lhs: usize, rhs: usize, operand_carrier: UIntCarrier },
    /// A negation or strict connective over `Bool` parameters, returned as `Bool`.
    BoolValue { spelling: BoolSpelling, kind: BoolValueKind },
}

/// The coverage-row tags this family reflects (the collector's `shape_tag` spellings).
pub const FAMILY_SHAPE_TAGS: &[&str] = &[
    "select",
    "select-literal",
    "select-operands",
    "select-beq",
    "comparison-value",
    "bool-not",
    "bool-connective",
];

/// Does the reflector cover this sealed plan's shape at its carriers? Coverage, not targeting:
/// see the module docs for why these families are not [`crate::gate_targets`].
#[must_use]
pub fn gate_reflects_family(plan: &CleanOriginPlan) -> bool {
    matches!(
        plan.shape(),
        CleanOriginShape::Select { .. }
            | CleanOriginShape::SelectLiteral { .. }
            | CleanOriginShape::SelectOperands { .. }
            | CleanOriginShape::SelectBeq { .. }
            | CleanOriginShape::DecideComparison { .. }
            | CleanOriginShape::BoolNot { .. }
            | CleanOriginShape::BoolConnective { .. }
    ) && family_source_carriers(plan).is_ok()
}

/// The source signature's carriers for a family plan: `(argument, result)`. Every argument is
/// the one argument carrier; no erased hypothesis or precondition.
pub(crate) fn family_source_carriers(
    plan: &CleanOriginPlan,
) -> Result<(TokenCarrier, TokenCarrier), GateRefusal> {
    let signature = plan.signature();
    if !signature.hypotheses().is_empty() || !signature.preconditions().is_empty() {
        return Err(GateRefusal::new(
            "source-preconditions",
            "the family gate requires zero erased hypotheses/preconditions",
        ));
    }
    let result = carrier_of_clean(signature.result().clean())?;
    let argument = match plan.shape() {
        CleanOriginShape::DecideComparison { .. } => {
            if result != TokenCarrier::Bool {
                return Err(GateRefusal::new("source-carrier", "a comparison value returns Bool"));
            }
            let first = signature
                .arguments()
                .first()
                .ok_or_else(|| GateRefusal::new("source-carrier", "a comparison has operands"))?;
            let argument = carrier_of_clean(first.clean())?;
            if argument == TokenCarrier::Bool {
                return Err(GateRefusal::new(
                    "source-carrier",
                    "a comparison value compares UInt operands (a Bool comparison is outside \
                     this family)",
                ));
            }
            argument
        }
        CleanOriginShape::BoolNot { .. } | CleanOriginShape::BoolConnective { .. } => {
            if result != TokenCarrier::Bool {
                return Err(GateRefusal::new("source-carrier", "a Bool operation returns Bool"));
            }
            TokenCarrier::Bool
        }
        _ => {
            if result == TokenCarrier::Bool {
                return Err(GateRefusal::new(
                    "source-carrier",
                    "the select family is gated at an exact UInt carrier only (a Bool select is \
                     outside this family)",
                ));
            }
            result
        }
    };
    for (index, carried) in signature.arguments().iter().enumerate() {
        if carrier_of_clean(carried.clean()).ok() != Some(argument) {
            return Err(GateRefusal::new(
                "source-carrier",
                format!(
                    "argument {index} is {}, expected {}",
                    carried.clean().name(),
                    argument.clean_name()
                ),
            ));
        }
        if carried.rust() != &argument.rust_ty() {
            return Err(GateRefusal::new(
                "source-rust-carrier",
                format!("sealed argument {index} Rust carrier is {:?}", carried.rust()),
            ));
        }
    }
    if signature.result().rust() != &result.rust_ty() {
        return Err(GateRefusal::new(
            "source-rust-carrier",
            format!("sealed result Rust carrier is {:?}", signature.result().rust()),
        ));
    }
    Ok((argument, result))
}

fn carrier_of_clean(clean: CleanType) -> Result<TokenCarrier, GateRefusal> {
    match clean {
        CleanType::Bool => Ok(TokenCarrier::Bool),
        other => UIntCarrier::from_clean(other).map(TokenCarrier::UInt).ok_or_else(|| {
            GateRefusal::new(
                "source-carrier",
                format!("{} is not Bool or an exact UInt8/16/32/64", other.name()),
            )
        }),
    }
}

fn carrier_of_ir(ty: &Ty) -> Option<TokenCarrier> {
    match ty {
        Ty::Bool => Some(TokenCarrier::Bool),
        other => UIntCarrier::from_ir(other).map(TokenCarrier::UInt),
    }
}

/// `(argument carrier, result carrier)` of the TrustIR signature: non-vararg, one result, every
/// parameter at one carrier.
fn ir_carriers(signature: &FuncTy) -> Result<(Option<TokenCarrier>, TokenCarrier), GateRefusal> {
    if signature.is_vararg || signature.returns.len() != 1 {
        return Err(GateRefusal::new(
            "signature",
            "expected a non-vararg signature with one result",
        ));
    }
    let result = carrier_of_ir(&signature.returns[0]).ok_or_else(|| {
        GateRefusal::new(
            "ir-carrier",
            format!("unsupported result type {:?}", signature.returns[0]),
        )
    })?;
    let mut argument = None;
    for (index, parameter) in signature.params.iter().enumerate() {
        let carrier = carrier_of_ir(parameter).ok_or_else(|| {
            GateRefusal::new("ir-carrier", format!("parameter {index} is {parameter:?}"))
        })?;
        match argument {
            None => argument = Some(carrier),
            Some(seen) if seen == carrier => {}
            Some(seen) => {
                return Err(GateRefusal::new(
                    "ir-carrier",
                    format!(
                        "parameter {index} is {}, earlier parameters are {}",
                        carrier.clean_name(),
                        seen.clean_name()
                    ),
                ));
            }
        }
    }
    Ok((argument, result))
}

/// The value environment of the reader: what each SSA value is.
#[derive(Clone, Copy, Debug)]
enum Value {
    Param(usize),
    Literal(u128),
    True,
    False,
    Computed,
}

struct Reader<'a> {
    function: &'a Function,
    values: std::collections::HashMap<ValueId, Value>,
    /// Literal-defining values not yet consumed: every one must be used exactly once.
    unused: std::collections::HashSet<ValueId>,
}

impl<'a> Reader<'a> {
    fn new(signature: &FuncTy, function: &'a Function) -> Result<Self, GateRefusal> {
        let entry = function
            .blocks
            .iter()
            .find(|block| block.id == function.entry)
            .ok_or_else(|| GateRefusal::new("control-flow", "entry block is missing"))?;
        if entry.params.len() != signature.params.len() {
            return Err(GateRefusal::new(
                "entry-parameters",
                format!(
                    "entry has {} parameters but signature has {}",
                    entry.params.len(),
                    signature.params.len()
                ),
            ));
        }
        let mut values = std::collections::HashMap::new();
        for (index, ((id, actual), expected)) in
            entry.params.iter().zip(&signature.params).enumerate()
        {
            if actual != expected {
                return Err(GateRefusal::new(
                    "entry-parameters",
                    format!("parameter {index} has type {actual:?}, expected {expected:?}"),
                ));
            }
            if values.insert(*id, Value::Param(index)).is_some() {
                return Err(GateRefusal::new("ssa", format!("value {id:?} is defined twice")));
            }
        }
        Ok(Self { function, values, unused: std::collections::HashSet::new() })
    }

    fn define(&mut self, results: &[ValueId], value: Value) -> Result<ValueId, GateRefusal> {
        let [id] = results else {
            return Err(GateRefusal::new(
                "result-arity",
                format!("instruction defines {} values, expected one", results.len()),
            ));
        };
        if self.values.insert(*id, value).is_some() {
            return Err(GateRefusal::new("ssa", format!("value {id:?} is defined twice")));
        }
        Ok(*id)
    }

    /// A `Const` of `carrier`: an in-range UInt literal, or `true`/`false` at `Bool`.
    fn constant(
        &mut self,
        results: &[ValueId],
        ty: &Ty,
        value: &Constant,
        carrier: TokenCarrier,
    ) -> Result<(), GateRefusal> {
        if carrier_of_ir(ty) != Some(carrier) {
            return Err(GateRefusal::new(
                "instruction-type",
                format!("Const has type {ty:?}, expected {}", carrier.clean_name()),
            ));
        }
        let read = match (carrier, value) {
            (TokenCarrier::Bool, Constant::Bool(true)) => Value::True,
            (TokenCarrier::Bool, Constant::Bool(false)) => Value::False,
            (TokenCarrier::UInt(c), Constant::Int(v)) if *v >= 0 && (*v as u128) < c.modulus() => {
                Value::Literal(*v as u128)
            }
            _ => {
                return Err(GateRefusal::new(
                    "constant",
                    format!(
                        "{value:?} is not a canonical in-range {} constant",
                        carrier.clean_name()
                    ),
                ));
            }
        };
        let id = self.define(results, read)?;
        self.unused.insert(id);
        Ok(())
    }

    /// Consume `id` as an operand. A literal may feed exactly one use.
    fn use_value(&mut self, id: ValueId) -> Result<Value, GateRefusal> {
        let value = *self
            .values
            .get(&id)
            .ok_or_else(|| GateRefusal::new("ssa", format!("operand {id:?} is undefined")))?;
        if matches!(value, Value::Literal(_) | Value::True | Value::False)
            && !self.unused.remove(&id)
        {
            return Err(GateRefusal::new(
                "shape",
                format!("constant {id:?} feeds more than one use"),
            ));
        }
        Ok(value)
    }

    fn leaf(&mut self, id: ValueId) -> Result<Leaf, GateRefusal> {
        match self.use_value(id)? {
            Value::Param(index) => Ok(Leaf::Param(index)),
            Value::Literal(value) => Ok(Leaf::Literal(value)),
            other => Err(GateRefusal::new(
                "shape",
                format!("operand {id:?} is {other:?}, expected a parameter or a literal"),
            )),
        }
    }

    fn param(&mut self, id: ValueId) -> Result<usize, GateRefusal> {
        match self.use_value(id)? {
            Value::Param(index) => Ok(index),
            other => Err(GateRefusal::new(
                "shape",
                format!("operand {id:?} is {other:?}, expected a parameter"),
            )),
        }
    }

    fn finish(&self) -> Result<(), GateRefusal> {
        if self.unused.is_empty() {
            Ok(())
        } else {
            Err(GateRefusal::new("shape", "a Const instruction feeds nothing"))
        }
    }

    /// The block with id `id`.
    fn block(&self, id: BlockId) -> Result<&'a trust_ir::Block, GateRefusal> {
        self.function
            .blocks
            .iter()
            .find(|block| block.id == id)
            .ok_or_else(|| GateRefusal::new("control-flow", format!("block {id:?} is missing")))
    }
}

/// Read the emitted body as one of the three families, deciding the family, the comparison and
/// every operand from the body alone. Zero authority.
pub fn read_family(signature: &FuncTy, function: &Function) -> Result<FamilyReading, GateRefusal> {
    let (argument, result) = ir_carriers(signature)?;
    let mut reader = Reader::new(signature, function)?;
    let entry = reader.block(function.entry)?;
    match (argument, result) {
        // The Bool operations: `not`/`and`/`or` at `bool`, or their `select` spelling.
        (Some(TokenCarrier::Bool), TokenCarrier::Bool) => {
            one_block(function)?;
            let mut returned = None;
            let mut kind = None;
            let mut spelling = None;
            for (position, node) in entry.body.iter().enumerate() {
                if returned.is_some() {
                    return Err(GateRefusal::new(
                        "control-flow",
                        format!("instruction {position} follows Return"),
                    ));
                }
                match &node.inst {
                    Inst::Const { ty, value } if kind.is_none() => {
                        reader.constant(&node.results, ty, value, TokenCarrier::Bool)?;
                    }
                    // `not b` is `bxor %b, true`: the parameter on the LEFT, the constant
                    // `true` on the RIGHT, exactly as the emitter spells it. `bxor %b, false` is
                    // the identity, and a reversed or two-parameter `bxor` is no producer's.
                    Inst::BinOp { op: BinOp::BXor, ty: Ty::Bool, lhs, rhs } if kind.is_none() => {
                        let param = reader.param(*lhs)?;
                        match reader.use_value(*rhs)? {
                            Value::True => {}
                            other => {
                                return Err(GateRefusal::new(
                                    "shape",
                                    format!(
                                        "a Bool `bxor` with right operand {other:?} is not `not` \
                                         (`bxor %b, true`)"
                                    ),
                                ));
                            }
                        }
                        kind = Some(BoolValueKind::Not(param));
                        spelling = Some(BoolSpelling::Operator);
                        reader.define(&node.results, Value::Computed)?;
                    }
                    Inst::BinOp { op: op @ (BinOp::BAnd | BinOp::BOr), ty: Ty::Bool, lhs, rhs }
                        if kind.is_none() =>
                    {
                        let (l, r) = (reader.param(*lhs)?, reader.param(*rhs)?);
                        kind = Some(if *op == BinOp::BAnd {
                            BoolValueKind::And(l, r)
                        } else {
                            BoolValueKind::Or(l, r)
                        });
                        spelling = Some(BoolSpelling::Operator);
                        reader.define(&node.results, Value::Computed)?;
                    }
                    Inst::Select { ty: Ty::Bool, cond, then_val, else_val } if kind.is_none() => {
                        let cond = reader.param(*cond)?;
                        let then_val = reader.use_value(*then_val)?;
                        let else_val = reader.use_value(*else_val)?;
                        // `select c, x, false` is `c && x`; `select c, true, x` is `c || x`;
                        // `select c, false, true` is `!c`. Operand order is kept: the
                        // condition is the connective's LEFT operand.
                        kind = Some(match (then_val, else_val) {
                            (Value::Param(x), Value::False) => BoolValueKind::And(cond, x),
                            (Value::True, Value::Param(x)) => BoolValueKind::Or(cond, x),
                            (Value::False, Value::True) => BoolValueKind::Not(cond),
                            other => {
                                return Err(GateRefusal::new(
                                    "shape",
                                    format!(
                                        "a Bool select of {other:?} is not `and`, `or` or `not`"
                                    ),
                                ));
                            }
                        });
                        spelling = Some(BoolSpelling::Select);
                        reader.define(&node.results, Value::Computed)?;
                    }
                    Inst::Return { values } => {
                        returned = Some(single_return(values, &node.results)?);
                    }
                    other => {
                        return Err(GateRefusal::new(
                            "instruction",
                            format!("unsupported instruction {other:?} in a Bool operation"),
                        ));
                    }
                }
            }
            let (Some(kind), Some(spelling), Some(returned)) = (kind, spelling, returned) else {
                return Err(GateRefusal::new("shape", "not a Bool operation ending in Return"));
            };
            if !matches!(reader.values.get(&returned), Some(Value::Computed)) {
                return Err(GateRefusal::new("return", "Return does not return the operation"));
            }
            reader.finish()?;
            Ok(FamilyReading::BoolValue { spelling, kind })
        }
        // The comparison value: one `icmp` over two UInt parameters, returned as `Bool`.
        (Some(TokenCarrier::UInt(operand_carrier)), TokenCarrier::Bool) => {
            one_block(function)?;
            let [icmp, ret] = entry.body.as_slice() else {
                return Err(GateRefusal::new(
                    "shape",
                    format!(
                        "a comparison value is exactly `icmp` + `ret`, got {} instructions",
                        entry.body.len()
                    ),
                ));
            };
            let Inst::ICmp { op, ty, lhs, rhs } = &icmp.inst else {
                return Err(GateRefusal::new("instruction", "expected one ICmp"));
            };
            if UIntCarrier::from_ir(ty) != Some(operand_carrier) {
                return Err(GateRefusal::new(
                    "instruction-type",
                    format!(
                        "ICmp compares {ty:?}, the parameters are {}",
                        operand_carrier.clean_name()
                    ),
                ));
            }
            let (l, r) = (reader.param(*lhs)?, reader.param(*rhs)?);
            let cmp = reader.define(&icmp.results, Value::Computed)?;
            let Inst::Return { values } = &ret.inst else {
                return Err(GateRefusal::new("control-flow", "block does not end in Return"));
            };
            if single_return(values, &ret.results)? != cmp {
                return Err(GateRefusal::new("return", "Return does not return the ICmp"));
            }
            Ok(FamilyReading::Comparison { pred: *op, lhs: l, rhs: r, operand_carrier })
        }
        // The select family at one UInt carrier.
        (Some(TokenCarrier::UInt(carrier)), TokenCarrier::UInt(result)) if carrier == result => {
            read_select(&mut reader, carrier)
        }
        (None, _) => Err(GateRefusal::new(
            "ir-carrier",
            "a nullary body is outside the select, comparison and Bool families",
        )),
        (Some(a), r) => Err(GateRefusal::new(
            "ir-carrier",
            format!(
                "parameters at {} and result at {} are not a select, comparison or Bool family \
                 signature",
                a.clean_name(),
                r.clean_name()
            ),
        )),
    }
}

fn one_block(function: &Function) -> Result<(), GateRefusal> {
    if function.blocks.len() == 1 {
        Ok(())
    } else {
        Err(GateRefusal::new(
            "control-flow",
            format!("expected exactly one block, got {}", function.blocks.len()),
        ))
    }
}

fn single_return(values: &[ValueId], results: &[ValueId]) -> Result<ValueId, GateRefusal> {
    if !results.is_empty() {
        return Err(GateRefusal::new("return", "Return unexpectedly defines values"));
    }
    match values {
        [value] => Ok(*value),
        _ => Err(GateRefusal::new(
            "return",
            format!("expected one return value, got {}", values.len()),
        )),
    }
}

/// The entry of a select, in either spelling: `Const*` then one `ICmp` at the carrier, then
/// (SelectInst) `Const*`, one `Select`, `Return` — or (Diamond) one `CondBr` with no branch
/// arguments into two parameter-free arms, each `Const?` then a single-value `Return`.
fn read_select(
    reader: &mut Reader<'_>,
    carrier: UIntCarrier,
) -> Result<FamilyReading, GateRefusal> {
    let function = reader.function;
    let entry = reader.block(function.entry)?;
    let constant_carrier = TokenCarrier::UInt(carrier);
    let mut cmp: Option<(usize, ICmpOp, Leaf, Leaf, ValueId)> = None;
    for (idx, node) in entry.body.iter().enumerate() {
        match &node.inst {
            Inst::Const { ty, value } => {
                reader.constant(&node.results, ty, value, constant_carrier)?;
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                if UIntCarrier::from_ir(ty) != Some(carrier) {
                    return Err(GateRefusal::new(
                        "instruction-type",
                        format!("ICmp compares {ty:?}, expected {}", carrier.clean_name()),
                    ));
                }
                let (l, r) = (reader.leaf(*lhs)?, reader.leaf(*rhs)?);
                let id = reader.define(&node.results, Value::Computed)?;
                cmp = Some((idx, *op, l, r, id));
                break;
            }
            other => {
                return Err(GateRefusal::new(
                    "instruction",
                    format!("unsupported instruction {other:?} before the comparison"),
                ));
            }
        }
    }
    let Some((cmp_idx, pred, lhs, rhs, cond_id)) = cmp else {
        return Err(GateRefusal::new("shape", "a select needs one ICmp"));
    };
    // The rest of the entry block decides the spelling.
    let rest = &entry.body[cmp_idx + 1..];
    let (spelling, then_arm, else_arm) = match rest.split_last() {
        Some((ret, body)) if matches!(&ret.inst, Inst::Return { .. }) => {
            one_block(function)?;
            let mut select: Option<(Leaf, Leaf, ValueId)> = None;
            for node in body {
                match &node.inst {
                    Inst::Const { ty, value } if select.is_none() => {
                        reader.constant(&node.results, ty, value, constant_carrier)?;
                    }
                    Inst::Select { ty, cond, then_val, else_val } if select.is_none() => {
                        if UIntCarrier::from_ir(ty) != Some(carrier) {
                            return Err(GateRefusal::new(
                                "instruction-type",
                                format!(
                                    "Select has type {ty:?}, expected {}",
                                    carrier.clean_name()
                                ),
                            ));
                        }
                        if *cond != cond_id {
                            return Err(GateRefusal::new(
                                "shape",
                                "the Select condition is not the comparison",
                            ));
                        }
                        let (t, e) = (reader.leaf(*then_val)?, reader.leaf(*else_val)?);
                        let id = reader.define(&node.results, Value::Computed)?;
                        select = Some((t, e, id));
                    }
                    other => {
                        return Err(GateRefusal::new(
                            "instruction",
                            format!("unsupported instruction {other:?} in a select body"),
                        ));
                    }
                }
            }
            let Some((t, e, selected)) = select else {
                return Err(GateRefusal::new("shape", "a one-block select needs one Select"));
            };
            let Inst::Return { values } = &ret.inst else {
                return Err(GateRefusal::new(
                    "control-flow",
                    "a select ends in Return (one block) or CondBr (a diamond)",
                ));
            };
            if single_return(values, &ret.results)? != selected {
                return Err(GateRefusal::new("return", "Return does not return the Select"));
            }
            (BranchSpelling::SelectInst, t, e)
        }
        Some((ret, body)) if matches!(&ret.inst, Inst::CondBr { .. }) => {
            let Inst::CondBr { cond, then_target, then_args, else_target, else_args } = &ret.inst
            else {
                return Err(GateRefusal::new(
                    "control-flow",
                    "a select ends in Return (one block) or CondBr (a diamond)",
                ));
            };
            if !body.is_empty() {
                return Err(GateRefusal::new(
                    "shape",
                    "the comparison must be the last instruction before the CondBr",
                ));
            }
            if *cond != cond_id {
                return Err(GateRefusal::new(
                    "shape",
                    "the CondBr condition is not the comparison",
                ));
            }
            if !then_args.is_empty() || !else_args.is_empty() {
                return Err(GateRefusal::new("control-flow", "a diamond arm takes no arguments"));
            }
            if function.blocks.len() != 3
                || then_target == else_target
                || *then_target == function.entry
                || *else_target == function.entry
            {
                return Err(GateRefusal::new(
                    "control-flow",
                    "a diamond is exactly an entry block and two distinct arms",
                ));
            }
            let t = read_arm(reader, *then_target, constant_carrier)?;
            let e = read_arm(reader, *else_target, constant_carrier)?;
            (BranchSpelling::Diamond, t, e)
        }
        _ => {
            return Err(GateRefusal::new(
                "control-flow",
                "a select ends in Return (one block) or CondBr (a diamond)",
            ));
        }
    };
    reader.finish()?;
    Ok(FamilyReading::Select { spelling, pred, lhs, rhs, then_arm, else_arm, carrier })
}

/// One diamond arm: no parameters, `Const?`, then a single-value `Return` of a parameter or of
/// that constant.
fn read_arm(
    reader: &mut Reader<'_>,
    id: BlockId,
    carrier: TokenCarrier,
) -> Result<Leaf, GateRefusal> {
    let block = reader.block(id)?;
    if !block.params.is_empty() {
        return Err(GateRefusal::new("control-flow", "a diamond arm takes no parameters"));
    }
    match block.body.as_slice() {
        [ret] => match &ret.inst {
            Inst::Return { values } => {
                let value = single_return(values, &ret.results)?;
                reader.leaf(value)
            }
            _ => Err(GateRefusal::new("control-flow", "a diamond arm ends in its own Return")),
        },
        [constant, ret] => {
            let Inst::Const { ty, value } = &constant.inst else {
                return Err(GateRefusal::new(
                    "instruction",
                    "a diamond arm is a Return, or one Const and a Return",
                ));
            };
            reader.constant(&constant.results, ty, value, carrier)?;
            let Inst::Return { values } = &ret.inst else {
                return Err(GateRefusal::new(
                    "control-flow",
                    "a diamond arm ends in its own Return",
                ));
            };
            let value = single_return(values, &ret.results)?;
            if !constant.results.contains(&value) {
                return Err(GateRefusal::new("return", "the arm does not return its constant"));
            }
            reader.leaf(value)
        }
        _ => Err(GateRefusal::new(
            "control-flow",
            "a diamond arm is a Return, or one Const and a Return",
        )),
    }
}

/// The source comparison an emitted predicate spells, or a refusal: `<`, `<=` and `=`/`==` are
/// the comparisons the elaborated select and comparison terms carry; `>`/`>=` are spelled by
/// swapping the operands at the source (`b < a`), so a `ugt`/`uge`/`ne`/signed predicate is
/// outside the family.
fn select_cmp(pred: ICmpOp) -> Result<SelectCmp, GateRefusal> {
    match pred {
        ICmpOp::Ult => Ok(SelectCmp::Lt),
        ICmpOp::Ule => Ok(SelectCmp::Le),
        ICmpOp::Eq => Ok(SelectCmp::Eq),
        other => Err(GateRefusal::new(
            "comparison",
            format!("{other:?} is outside the family (only ult, ule and eq)"),
        )),
    }
}

fn elab_cmp(cmp: SelectCmp) -> trust_spec_elab::SelectCmp {
    match cmp {
        SelectCmp::Lt => trust_spec_elab::SelectCmp::Lt,
        SelectCmp::Le => trust_spec_elab::SelectCmp::Le,
        SelectCmp::Eq => trust_spec_elab::SelectCmp::Eq,
    }
}

fn leaf_of(operand: ArithOperand) -> Leaf {
    match operand {
        ArithOperand::Param(index) => Leaf::Param(index),
        ArithOperand::Const(value) => Leaf::Literal(value),
    }
}

fn select_operand(leaf: Leaf) -> SelectOperand {
    match leaf {
        Leaf::Param(index) => SelectOperand::Param(index),
        Leaf::Literal(value) => SelectOperand::Literal(value),
    }
}

/// Which side-B producer reflects an agreed reading, with the reading's own operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ProducerCall {
    Select {
        cmp: SelectCmp,
        left: usize,
        right: usize,
        then_param: usize,
        else_param: usize,
    },
    SelectLiteral {
        cmp: SelectCmp,
        param: usize,
        literal: u128,
        then_param: usize,
        else_param: usize,
    },
    SelectOperands {
        cmp: SelectCmp,
        left: usize,
        right: Leaf,
        then_arm: Leaf,
        else_arm: Leaf,
    },
    SelectBeq {
        left: usize,
        right: Leaf,
        then_arm: Leaf,
        else_arm: Leaf,
    },
    Comparison {
        cmp: SelectCmp,
        left: usize,
        right: usize,
    },
    BoolValue(BoolValueKind),
}

/// Stage `plan-shape`: the sealed plan must agree with the body's reading field for field; the
/// producer call is built from the READING.
pub(crate) fn agree(
    plan: &CleanOriginPlan,
    reading: &FamilyReading,
) -> Result<ProducerCall, GateRefusal> {
    let disagree = || {
        GateRefusal::new(
            "plan-shape",
            format!("sealed plan is {:?} but the emitted body reads as {reading:?}", plan.shape()),
        )
    };
    match (plan.shape(), reading) {
        (shape, FamilyReading::Select { pred, lhs, rhs, then_arm, else_arm, .. }) => {
            let cmp = select_cmp(*pred)?;
            let Leaf::Param(left) = *lhs else {
                return Err(GateRefusal::new(
                    "comparison",
                    "a literal on the comparison's left does not elaborate (l3_p6)",
                ));
            };
            match shape {
                CleanOriginShape::Select {
                    cmp: c,
                    cmp_left,
                    cmp_right,
                    then_param,
                    else_param,
                } if *c == cmp
                    && *cmp_left == left
                    && *rhs == Leaf::Param(*cmp_right)
                    && *then_arm == Leaf::Param(*then_param)
                    && *else_arm == Leaf::Param(*else_param) =>
                {
                    Ok(ProducerCall::Select {
                        cmp,
                        left,
                        right: *cmp_right,
                        then_param: *then_param,
                        else_param: *else_param,
                    })
                }
                CleanOriginShape::SelectLiteral {
                    cmp: c,
                    cmp_param,
                    literal,
                    then_param,
                    else_param,
                } if *c == cmp
                    && *cmp_param == left
                    && *rhs == Leaf::Literal(*literal)
                    && *then_arm == Leaf::Param(*then_param)
                    && *else_arm == Leaf::Param(*else_param) =>
                {
                    Ok(ProducerCall::SelectLiteral {
                        cmp,
                        param: left,
                        literal: *literal,
                        then_param: *then_param,
                        else_param: *else_param,
                    })
                }
                CleanOriginShape::SelectOperands {
                    cmp: c,
                    cmp_left,
                    cmp_right,
                    then_arm: t,
                    else_arm: e,
                } if *c == cmp
                    && *cmp_left == left
                    && *rhs == leaf_of(*cmp_right)
                    && *then_arm == leaf_of(*t)
                    && *else_arm == leaf_of(*e) =>
                {
                    Ok(ProducerCall::SelectOperands {
                        cmp,
                        left,
                        right: *rhs,
                        then_arm: *then_arm,
                        else_arm: *else_arm,
                    })
                }
                CleanOriginShape::SelectBeq { cmp_left, cmp_right, then_arm: t, else_arm: e }
                    if cmp == SelectCmp::Eq
                        && *cmp_left == left
                        && *rhs == leaf_of(*cmp_right)
                        && *then_arm == leaf_of(*t)
                        && *else_arm == leaf_of(*e) =>
                {
                    Ok(ProducerCall::SelectBeq {
                        left,
                        right: *rhs,
                        then_arm: *then_arm,
                        else_arm: *else_arm,
                    })
                }
                _ => Err(disagree()),
            }
        }
        (
            CleanOriginShape::DecideComparison { cmp, cmp_left, cmp_right },
            FamilyReading::Comparison { pred, lhs, rhs, .. },
        ) if select_cmp(*pred)? == *cmp && cmp_left == lhs && cmp_right == rhs => {
            Ok(ProducerCall::Comparison { cmp: *cmp, left: *lhs, right: *rhs })
        }
        (CleanOriginShape::BoolNot { param }, FamilyReading::BoolValue { kind, .. })
            if *kind == BoolValueKind::Not(*param) =>
        {
            Ok(ProducerCall::BoolValue(*kind))
        }
        (
            CleanOriginShape::BoolConnective { op, left, right },
            FamilyReading::BoolValue { kind, .. },
        ) if *kind
            == match op {
                BoolBinOp::And => BoolValueKind::And(*left, *right),
                BoolBinOp::Or => BoolValueKind::Or(*left, *right),
            } =>
        {
            Ok(ProducerCall::BoolValue(*kind))
        }
        _ => Err(disagree()),
    }
}

fn domain_of(ty: &Ty) -> Option<Domain> {
    match ty {
        Ty::Bool => Some(Domain::Bool),
        Ty::U8 => Some(Domain::Machine(MachineUIntWidth::U8)),
        Ty::U16 => Some(Domain::Machine(MachineUIntWidth::U16)),
        Ty::U32 => Some(Domain::Machine(MachineUIntWidth::U32)),
        Ty::U64 => Some(Domain::Machine(MachineUIntWidth::U64)),
        _ => None,
    }
}

/// The scratch constant a producer mints into the environment clone.
const REFLECTED_SUFFIX: &str = "_trust_clean_ir_gate_family_reflection";

/// Mint the side-B term for `call` through its producer, into a CLONE of `env`. The parameter
/// domains are read off the TrustIR signature, never off the plan.
pub(crate) fn side_b(
    env: &Environment,
    name: &str,
    signature: &FuncTy,
    call: &ProducerCall,
) -> Result<Expr, GateRefusal> {
    let domains: Vec<Domain> = signature
        .params
        .iter()
        .map(|ty| {
            domain_of(ty).ok_or_else(|| {
                GateRefusal::new("ir-carrier", format!("parameter type {ty:?} has no domain"))
            })
        })
        .collect::<Result<_, _>>()?;
    let mut scratch = env.clone();
    let reflected = format!("{name}{REFLECTED_SUFFIX}");
    let minted = match call {
        ProducerCall::Select { cmp, left, right, then_param, else_param } => {
            trust_spec_elab::admit_select_function(
                &mut scratch,
                &reflected,
                &domains,
                elab_cmp(*cmp),
                *left,
                *right,
                *then_param,
                *else_param,
            )
        }
        ProducerCall::SelectLiteral { cmp, param, literal, then_param, else_param } => {
            trust_spec_elab::admit_select_literal_function(
                &mut scratch,
                &reflected,
                &domains,
                elab_cmp(*cmp),
                *param,
                *literal,
                *then_param,
                *else_param,
            )
        }
        ProducerCall::SelectOperands { cmp, left, right, then_arm, else_arm } => {
            trust_spec_elab::admit_select_operands_function(
                &mut scratch,
                &reflected,
                &domains,
                elab_cmp(*cmp),
                *left,
                select_operand(*right),
                select_operand(*then_arm),
                select_operand(*else_arm),
            )
        }
        ProducerCall::SelectBeq { left, right, then_arm, else_arm } => {
            trust_spec_elab::admit_select_beq_function(
                &mut scratch,
                &reflected,
                &domains,
                *left,
                select_operand(*right),
                select_operand(*then_arm),
                select_operand(*else_arm),
            )
        }
        ProducerCall::Comparison { cmp, left, right } => {
            trust_spec_elab::admit_comparison_function(
                &mut scratch,
                &reflected,
                &domains,
                elab_cmp(*cmp),
                CmpOperand::Param(*left),
                CmpOperand::Param(*right),
            )
        }
        ProducerCall::BoolValue(kind) => {
            trust_spec_elab::admit_bool_value_function(&mut scratch, &reflected, &domains, *kind)
        }
    };
    if let Err(detail) = minted {
        return Err(GateRefusal::new("reflection", detail));
    }
    scratch
        .get_const(&Name::from_string(&reflected))
        .and_then(|constant| constant.value.clone())
        .ok_or_else(|| GateRefusal::new("reflection", "the reflected definition carries no value"))
}

/// The whole family check: carriers, reading, plan agreement, side B, and the kernel's
/// definitional equality at the result carrier. Returns the verdict, the result carrier and the
/// gated shape.
pub(crate) fn check_family(
    env: &Environment,
    plan: &CleanOriginPlan,
    signature: &FuncTy,
    function: &Function,
) -> Result<(trust_clean_origin::Faithful, TokenCarrier, crate::GatedShape), GateRefusal> {
    if !gate_reflects_family(plan) {
        return Err(GateRefusal::new(
            "target-shape",
            format!(
                "`{}` is not a select / comparison-value / Bool-value plan at Bool or an exact \
                 UInt8/16/32/64 carrier with no erased hypothesis",
                plan.name()
            ),
        ));
    }
    let (argument, result) = family_source_carriers(plan)?;
    if plan.signature().arguments().len() != signature.params.len() {
        return Err(GateRefusal::new(
            "source-ir-arity",
            format!(
                "sealed source has {} carried arguments but TrustIR signature has {} parameters",
                plan.signature().arguments().len(),
                signature.params.len()
            ),
        ));
    }
    let (ir_argument, ir_result) = ir_carriers(signature)?;
    if ir_result != result || (ir_argument.is_some() && ir_argument != Some(argument)) {
        return Err(GateRefusal::new(
            "source-ir-carrier",
            "the sealed source carriers and the TrustIR signature disagree",
        ));
    }
    let reading = read_family(signature, function)?;
    let call = agree(plan, &reading)?;
    let term = side_b(env, plan.name(), signature, &call)?;
    let faithful = trust_clean_origin::gate::check_faithful_for_name(
        env,
        plan.declaration(),
        &term,
        plan.result_carrier(),
    )
    .map_err(|refusal| GateRefusal::new("kernel-disagreement", refusal.note()))?;
    if faithful.method() != FaithfulnessMethod::DefinitionalEquality {
        return Err(GateRefusal::new(
            "kernel-method",
            "the family gate requires whole-term definitional equality",
        ));
    }
    if faithful.admitted_at() != &result.rust_ty() {
        return Err(GateRefusal::new(
            "kernel-carrier",
            format!(
                "kernel verdict was admitted at {:?}, expected {:?}",
                faithful.admitted_at(),
                result.rust_ty()
            ),
        ));
    }
    Ok((faithful, result, crate::GatedShape::of_family_reading(&reading)))
}

/// KERNEL-LAYER CONTROLS. The integration tests refuse mutations at the plan agreement; these
/// bypass it, handing the kernel a term built from a mutated reading against the ORIGINAL
/// declaration, so the kernel's own refusal is measured, not assumed.
#[cfg(test)]
mod kernel_controls {
    use trust_certify::clean_island::CleanIslandSession;
    use trust_clean_origin::plan_clean_origin_body;

    use super::*;

    fn env() -> Environment {
        let mut session = CleanIslandSession::new();
        for source in [
            "def sel64 (a b : UInt64) : UInt64 := if a < b then a else b",
            "def seq64 (a b : UInt64) : UInt64 := if a = b then a else b",
            "def sbeq64 (a b : UInt64) : UInt64 := if a == b then a else b",
            "def clt64 (a b : UInt64) : Bool := a < b",
            "def band (a : Bool) (b : Bool) : Bool := a && b",
        ] {
            let outcome = session.check(source);
            assert!(!outcome.is_rejected(), "`{source}`: {outcome:?}");
        }
        session.environment().expect("untainted").clone()
    }

    /// `Ok` when the kernel admits; `Err(Ok(note))` when the KERNEL refuses a term the producer
    /// minted; `Err(Err(note))` when the producer itself refused (not a kernel verdict).
    fn verdict(
        env: &Environment,
        name: &str,
        call: &ProducerCall,
    ) -> Result<(), Result<String, String>> {
        let plan = plan_clean_origin_body(env, name).expect("plans");
        let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).expect("lowers");
        let term = side_b(env, name, &signature, call).map_err(|r| Err(r.note()))?;
        trust_clean_origin::gate::check_faithful_for_name(
            env,
            plan.declaration(),
            &term,
            plan.result_carrier(),
        )
        .map(|_| ())
        .map_err(|r| Ok(r.note()))
    }

    fn kernel_refuses(env: &Environment, name: &str, call: &ProducerCall, what: &str) {
        match verdict(env, name, call) {
            Err(Ok(_)) => {}
            Ok(()) => panic!("{what}: the kernel ADMITTED a mutated term for `{name}`"),
            Err(Err(note)) => panic!("{what}: refused before the kernel ({note})"),
        }
    }

    #[test]
    fn the_kernel_refuses_every_mutated_term_and_admits_each_control() {
        let env = env();
        let select = |cmp, then_param, else_param| ProducerCall::Select {
            cmp,
            left: 0,
            right: 1,
            then_param,
            else_param,
        };
        // Controls: the faithful term admits.
        verdict(&env, "sel64", &select(SelectCmp::Lt, 0, 1)).expect("sel64 control");
        verdict(&env, "seq64", &select(SelectCmp::Eq, 0, 1)).expect("seq64 control (`=`)");
        let beq = ProducerCall::SelectBeq {
            left: 0,
            right: Leaf::Param(1),
            then_arm: Leaf::Param(0),
            else_arm: Leaf::Param(1),
        };
        verdict(&env, "sbeq64", &beq).expect("sbeq64 control");
        let lt = ProducerCall::Comparison { cmp: SelectCmp::Lt, left: 0, right: 1 };
        verdict(&env, "clt64", &lt).expect("clt64 control");
        verdict(&env, "band", &ProducerCall::BoolValue(BoolValueKind::And(0, 1)))
            .expect("band control");
        // Mutations: each refused by the KERNEL.
        kernel_refuses(&env, "sel64", &select(SelectCmp::Le, 0, 1), "Le for Lt");
        kernel_refuses(&env, "sel64", &select(SelectCmp::Lt, 1, 0), "swapped arms");
        kernel_refuses(&env, "sel64", &select(SelectCmp::Eq, 0, 1), "Eq for Lt");
        // The `=` / `==` spelling choice the plan makes for an `icmp eq` body is decided by the
        // kernel: the wrong spelling is refused in both directions.
        kernel_refuses(&env, "sbeq64", &select(SelectCmp::Eq, 0, 1), "= for ==");
        kernel_refuses(&env, "seq64", &beq, "== for =");
        let le = ProducerCall::Comparison { cmp: SelectCmp::Le, left: 0, right: 1 };
        kernel_refuses(&env, "clt64", &le, "Le for Lt (comparison)");
        let swapped = ProducerCall::Comparison { cmp: SelectCmp::Lt, left: 1, right: 0 };
        kernel_refuses(&env, "clt64", &swapped, "swapped operands");
        kernel_refuses(
            &env,
            "band",
            &ProducerCall::BoolValue(BoolValueKind::Or(0, 1)),
            "or for and",
        );
        kernel_refuses(
            &env,
            "band",
            &ProducerCall::BoolValue(BoolValueKind::And(1, 0)),
            "commuted and",
        );
    }
}
