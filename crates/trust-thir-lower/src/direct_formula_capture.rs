//! Step 6, increment 1 (docs/design/DIRECT-LANE-PROOF-AUTHORITY.md, design of
//! record 2026-08-31): capture the TYPED shape each direct assert site holds
//! and mint its L0 safety formula ONCE, at emission, through the single source
//! of truth `trust_ir_bridge::safety_formulas::mint_direct_safety_formula` —
//! which itself delegates to the bridge's MIR-lane `reconstruct_*` builders,
//! so a byte-identical formula is the two lanes executing the SAME
//! constructor over the same operand identities, never a re-implementation.
//!
//! A NEW FILE by design (fleet discipline): `lib.rs` keeps exactly one
//! touchpoint per assert arm (`record_direct_assert_typed(...)` with a
//! [`DirectAssertShape`]) plus the module line; everything else lives here.
//!
//! WHAT THE CAPTURE KNOWS (the production knowledge rule): parameter names —
//! the `value_names` ledger is params-only ("ValueId(i) IS entry param i by
//! construction") — and literals whose defining `Inst::Const` sits in the
//! OPEN block. Everything else is [`DirectFormulaOperand`]-unrepresentable
//! and the outcome is `Withheld { reason: "opaque-operand" }`: an enumerated
//! decline, never a guess. The obligation ROW is untouched either way — the
//! formula outcome is session state beside the record, counted by the
//! installer's disclosure counters and shipped by nothing
//! (`DirectObligationTier`'s "carries a formula" violation stays the live
//! gate).
//!
//! GENERICS TRIPWIRE, BY TYPES: `direct_formula_width` yields a concrete
//! `(width, signed)` only for the mapped integer variants;
//! placeholder-mapped types (`Ty::Unit` for an uninstantiated generic) fail
//! `direct_int_width` with `non-concrete-width` — a Withheld outcome, pinned
//! on the bridge side by `mint_guards_fail_closed_with_named_reasons`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use rustc_middle::mir::BinOp as MirBinOp;
use trust_ir::inst::Inst;
use trust_ir::value::ValueId;
use trust_ir::{Constant, Ty};
use trust_ir_bridge::safety_formulas::{
    AddSubOp, DirectFormulaClass, DirectFormulaOperand, direct_int_width,
    mint_direct_safety_formula,
};

use crate::LowerCx;
use crate::direct_obligations::DirectFormulaOutcome;

/// Exactly what each of the six `record_direct_assert` sites holds at the
/// moment it pushes its `Inst::Assert` — no more (the mint must not know
/// things the site does not), no less.
#[derive(Debug, Clone)]
pub(crate) enum DirectAssertShape {
    /// Site A — `AssertKind::OverflowNeg`: the negated operand and its type.
    Neg { ty: Ty, operand: ValueId },
    /// Site B — `AssertKind::Overflow(Add|Sub|Mul)`: the checked binop.
    Binop { op: MirBinOp, ty: Ty, lhs: ValueId, rhs: ValueId },
    /// Site C — `DivisionByZero` / `RemainderByZero`: the divisor.
    DivRemZero { ty: Ty, divisor: ValueId, is_rem: bool },
    /// Site D — the signed `INT_MIN / -1` overflow pair.
    DivRemMinOverflow { ty: Ty, lhs: ValueId, rhs: ValueId },
    /// Site E — `Overflow(Shl|Shr)`: the ORIGINAL (pre-reinterpretation)
    /// amount with its own type, and the shifted value's type.
    Shift { value_ty: Ty, amount_ty: Ty, amount: ValueId },
    /// Site F — `BoundsCheck` against a compile-time array length.
    Bounds { index: ValueId, len: u64 },
    /// Slice bounds use the current fat pointer's metadata, not a compile-time length.
    /// The exact SSA predicate remains on the recorded Assert node; the present formula
    /// encoder cannot bind that metadata/state identity and must not invent a source name.
    SliceBounds,
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// Record the proof-guard `Inst::Assert` the caller JUST pushed — the
    /// Step-2 positional/identity capture, unchanged — AND mint the Step-6
    /// typed formula outcome for it, exactly once, storing the pair in the
    /// same session record. Call IMMEDIATELY after the Assert push, exactly
    /// like `record_direct_assert` (which this wraps).
    pub(crate) fn record_direct_assert_typed(
        &mut self,
        slug: &'static str,
        annotation: trust_ir::proof::ProofAnnotation,
        at: rustc_span::Span,
        shape: &DirectAssertShape,
    ) {
        // Mint BEFORE the record push (pure reads of the open block and the
        // value ledger), then attach to the record the push just created —
        // one mint, one record, one assignment; nothing recomputes it.
        let outcome = self.direct_formula_outcome(shape);
        self.record_direct_assert(slug, annotation, at);
        if let Some(record) = self.direct_obligations.last_mut() {
            record.formula = outcome;
        }
    }

    /// The formula outcome for one shape: resolve operands under the
    /// production knowledge rule, then delegate to the bridge mint. Every
    /// failure path is a named `Withheld`, never a panic and never a guess.
    fn direct_formula_outcome(&self, shape: &DirectAssertShape) -> DirectFormulaOutcome {
        let (class, width, signed, operands) = match self.direct_formula_case(shape) {
            Ok(case) => case,
            Err(reason) => return DirectFormulaOutcome::Withheld { reason },
        };
        match mint_direct_safety_formula(&class, width, signed, &operands) {
            Ok(minted) => DirectFormulaOutcome::Minted(minted),
            Err(decline) => DirectFormulaOutcome::Withheld { reason: decline.code() },
        }
    }

    /// Shape -> (class, width, signed, operands), or the withhold reason.
    fn direct_formula_case(
        &self,
        shape: &DirectAssertShape,
    ) -> Result<(DirectFormulaClass, u32, bool, Vec<DirectFormulaOperand>), &'static str> {
        match shape {
            DirectAssertShape::Neg { ty, operand } => {
                let (width, signed) = self.direct_formula_width(ty)?;
                let operand = self.direct_formula_operand(*operand)?;
                Ok((DirectFormulaClass::OverflowNeg, width, signed, vec![operand]))
            }
            DirectAssertShape::Binop { op, ty, lhs, rhs } => {
                let (width, signed) = self.direct_formula_width(ty)?;
                let class = match op {
                    MirBinOp::Add => DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
                    MirBinOp::Sub => DirectFormulaClass::OverflowAddSub { op: AddSubOp::Sub },
                    MirBinOp::Mul => DirectFormulaClass::OverflowMul,
                    // Site B is gated by `map_overflow_op` (Add/Sub/Mul only);
                    // anything else here is a wiring defect — withhold, do
                    // not guess a class.
                    _ => return Err("unsupported-binop-shape"),
                };
                let lhs = self.direct_formula_operand(*lhs)?;
                let rhs = self.direct_formula_operand(*rhs)?;
                Ok((class, width, signed, vec![lhs, rhs]))
            }
            DirectAssertShape::DivRemZero { ty, divisor, is_rem } => {
                let (width, signed) = self.direct_formula_width(ty)?;
                let class = if *is_rem {
                    DirectFormulaClass::RemByZero
                } else {
                    DirectFormulaClass::DivByZero
                };
                let divisor = self.direct_formula_operand(*divisor)?;
                Ok((class, width, signed, vec![divisor]))
            }
            DirectAssertShape::DivRemMinOverflow { ty, lhs, rhs } => {
                let (width, signed) = self.direct_formula_width(ty)?;
                let lhs = self.direct_formula_operand(*lhs)?;
                let rhs = self.direct_formula_operand(*rhs)?;
                Ok((DirectFormulaClass::DivRemMinOverflow, width, signed, vec![lhs, rhs]))
            }
            DirectAssertShape::Shift { value_ty, amount_ty, amount } => {
                let (value_bits, _) = self.direct_formula_width(value_ty)?;
                let (amount_width, amount_signed) = self.direct_formula_width(amount_ty)?;
                let amount = self.direct_formula_operand(*amount)?;
                Ok((
                    DirectFormulaClass::ShiftInRange { amount_width, amount_signed, value_bits },
                    amount_width,
                    amount_signed,
                    vec![amount],
                ))
            }
            DirectAssertShape::Bounds { index, len } => {
                // Site F's index is usize by typeck + the site's own guard:
                // the pinned 64-bit unsigned carrier.
                let index = self.direct_formula_operand(*index)?;
                Ok((DirectFormulaClass::BoundsCheck { len: *len }, 64, false, vec![index]))
            }
            // Next step: bind dynamic metadata operands to the same function/SSA/state
            // identity in the canonical formula encoder. Do not substitute an allocation
            // size, a zero constant, or an invented named parameter in the meantime.
            DirectAssertShape::SliceBounds => Err("dynamic-slice-length-operand"),
        }
    }

    /// Concrete `(width, signed)` of a mapped type, by types — the generics
    /// tripwire. Delegates to the bridge's exhaustive 13-variant helper.
    fn direct_formula_width(&self, ty: &Ty) -> Result<(u32, bool), &'static str> {
        direct_int_width(ty).map_err(|decline| decline.code())
    }

    /// One operand under the production knowledge rule:
    /// * depth-1 (leaf) resolution first — [`Self::direct_formula_leaf_operand`];
    /// * increment 3: on the ANONYMOUS band only (`unnamed-temp-operand` —
    ///   the naming-hazard declines `ambiguous-operand-name` /
    ///   `shadowed-operand-name` keep their reasons, never papered over by a
    ///   chase), the depth-2 CHECKED-TRIO chase
    ///   (`direct_operand_widening.rs::nested_checked_operand`): the value of
    ///   an open-block `Inst::Overflow` whose own operands resolve at depth 1
    ///   becomes `DirectFormulaOperand::Nested`; every failure keeps the
    ///   enumerated `unnamed-temp-operand` withhold, never a guess.
    fn direct_formula_operand(&self, value: ValueId) -> Result<DirectFormulaOperand, &'static str> {
        match self.direct_formula_leaf_operand(value) {
            Err("unnamed-temp-operand") => self.nested_checked_operand(value),
            resolved => resolved,
        }
    }

    /// The depth-1 (LEAF) resolution — increment 2's rule, verbatim:
    /// * a `value_names` hit -> `Named` (the params fast path — kept AHEAD of
    ///   the widened resolver so a shadowed param stays the pinned
    ///   KnownMismatch class, exactly increment 1's disclosed divergence);
    /// * a value whose defining `Inst::Const` sits in the OPEN block ->
    ///   `Lit`/`ULit`;
    /// * anything else -> the increment-2 NAMED-VALUE RESOLUTION
    ///   (`direct_operand_widening.rs`): a value the lowering currently knows
    ///   under exactly one census-unique source name resolves `Named`; every
    ///   other miss is a NAMED enumerated withhold
    ///   (`unnamed-temp-operand` / `ambiguous-operand-name` /
    ///   `shadowed-operand-name`), never a guess.
    ///
    /// Also the resolver for a NESTED operand's own leaves (increment 3) —
    /// calling THIS method rather than `direct_formula_operand` is what makes
    /// the one-nesting-level cap structural on the capture carrier.
    pub(crate) fn direct_formula_leaf_operand(
        &self,
        value: ValueId,
    ) -> Result<DirectFormulaOperand, &'static str> {
        if let Some((_, name)) = self.value_names.iter().find(|(vid, _)| *vid == value) {
            return Ok(DirectFormulaOperand::Named { name: name.clone() });
        }
        if let Some(node) = self.cur.iter().rev().find(|node| node.results.contains(&value)) {
            match &node.inst {
                Inst::Const { value: Constant::Int(n), .. } => {
                    return Ok(DirectFormulaOperand::Lit(*n));
                }
                Inst::Const { value: Constant::U128(n), .. } => {
                    return Ok(DirectFormulaOperand::ULit(*n));
                }
                _ => {}
            }
        }
        self.widened_named_operand(value)
    }
}
