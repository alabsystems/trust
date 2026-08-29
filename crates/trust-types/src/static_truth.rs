//! Trust (#57, 2026-08-17) — THE SHARED STATIC-TRUTH FOLD.
//!
//! Whether an `Assert`'s failure branch is STATICALLY KNOWN FALSE decides whether
//! an obligation exists at all: `n % 2` carries no division-by-zero obligation,
//! because the divisor is a literal `2`. A producer that folds it emits nothing; a
//! producer that does not emits a trivially-true VC.
//!
//! This lived in `trust-vcgen` and had no counterpart in the trust-ir spine, which
//! is why the spine over-generated 31 divisor obligations across the corpus — the
//! entire surviving population of the missing-obligation alarm
//! (`trust_ir_bridge::flip::missing_obligation_ratchet`).
//!
//! **It lives HERE, once, rather than being reimplemented on the spine side, and
//! that is the whole point.** The alarm compares the two producers' obligation
//! enumerations against each other; if each producer carried its own copy of the
//! fold, any drift between the copies would surface as a phantom disagreement — an
//! alarm about a difference in the checkers rather than a hole in the checking.
//! One definition, two callers, nothing to drift.
//!
//! SOUNDNESS DIRECTION: every `None` here means UNKNOWN and makes the caller keep
//! the obligation. Only a definite `Some(truth)` matching `expected` folds one
//! away. The `ConstValue` arms below are written with that asymmetry in mind — an
//! opaque, const-generic, or callable constant answers `None`, never
//! "definitely unequal", because pruning a genuinely-taken branch would drop its
//! safety obligations, which is a false PROVE.

use crate::{BinOp, ConstValue, Operand, Rvalue, Statement};

pub fn assert_failure_is_known_false(
    block: &crate::BasicBlock,
    cond: &Operand,
    expected: bool,
) -> bool {
    condition_truth_until(block, cond, block.stmts.len()).is_some_and(|truth| truth == expected)
}

pub fn condition_truth_until(
    block: &crate::BasicBlock,
    cond: &Operand,
    end_stmt_exclusive: usize,
) -> Option<bool> {
    match cond {
        Operand::Constant(ConstValue::Bool(value)) => Some(*value),
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            local_condition_truth_until(block, place.local, end_stmt_exclusive)
        }
        _ => None,
    }
}

pub fn local_condition_truth_until(
    block: &crate::BasicBlock,
    local: usize,
    end_stmt_exclusive: usize,
) -> Option<bool> {
    for (idx, stmt) in block.stmts.iter().take(end_stmt_exclusive).enumerate().rev() {
        match stmt {
            Statement::Assign { place, rvalue, .. }
                if place.local == local && place.projections.is_empty() =>
            {
                return match rvalue {
                    Rvalue::Use(operand) => condition_truth_until(block, operand, idx),
                    Rvalue::BinaryOp(BinOp::Eq, lhs, rhs) => constant_eq_truth(lhs, rhs),
                    Rvalue::BinaryOp(BinOp::Ne, lhs, rhs) => {
                        constant_eq_truth(lhs, rhs).map(|truth| !truth)
                    }
                    _ => None,
                };
            }
            // The shared fold intentionally has no function-wide alias oracle.
            // A projected write can therefore overlap `local` through a separately
            // named `&mut` pointer.  Likewise, opaque pointer-writing statements
            // and lifetime-ending statements can invalidate a previously computed
            // condition.  Decline the fold conservatively instead of treating a
            // stale direct assignment as the value observed by the Assert.
            Statement::Assign { place, .. } if !place.projections.is_empty() => return None,
            Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                if place.local == local || !place.projections.is_empty() =>
            {
                return None;
            }
            Statement::StorageDead(dead) if *dead == local => return None,
            Statement::Intrinsic { .. }
            | Statement::CopyNonOverlapping { .. }
            | Statement::Unsupported { .. } => return None,
            _ => {}
        }
    }

    None
}

pub fn constant_eq_truth(lhs: &Operand, rhs: &Operand) -> Option<bool> {
    match (lhs, rhs) {
        (Operand::Constant(lhs), Operand::Constant(rhs)) => const_eq_truth(lhs, rhs),
        _ => None,
    }
}

pub fn const_eq_truth(lhs: &ConstValue, rhs: &ConstValue) -> Option<bool> {
    match (lhs, rhs) {
        (ConstValue::Bool(lhs), ConstValue::Bool(rhs)) => Some(lhs == rhs),
        (ConstValue::Int(lhs), ConstValue::Int(rhs)) => Some(lhs == rhs),
        (ConstValue::Uint(lhs, _), ConstValue::Uint(rhs, _)) => Some(lhs == rhs),
        (ConstValue::Int(lhs), ConstValue::Uint(rhs, _)) => {
            (*lhs >= 0).then_some(*lhs as u128 == *rhs)
        }
        (ConstValue::Uint(lhs, _), ConstValue::Int(rhs)) => {
            (*rhs >= 0).then_some(*lhs == *rhs as u128)
        }
        (ConstValue::Float(lhs), ConstValue::Float(rhs)) => Some(lhs == rhs),
        // `FloatBits` preserves the exact IEEE payload/width, while the legacy
        // `Float(f64)` spelling does not.  Until this fold has one typed IEEE
        // equality implementation for both spellings, any FloatBits involvement
        // is UNKNOWN.  Falling through to `Some(false)` would call two identical
        // bit-pattern constants definitely unequal and could delete a genuinely
        // failing assertion.
        (ConstValue::FloatBits { .. }, _) | (_, ConstValue::FloatBits { .. }) => None,
        (ConstValue::Unit, ConstValue::Unit) => Some(true),
        // Callable identity is extraction evidence for syntactic recognizers,
        // never a solver-level equality fact. Historical dumps encoded these
        // values as Unit; returning unknown is strictly more conservative.
        (ConstValue::CallableItem { .. }, _) | (_, ConstValue::CallableItem { .. }) => None,
        // two `&str` literals are equal iff their bytes match. This is
        // exact (the bytes come straight from the literal's allocation), so it is
        // sound to let it decide a constant branch. Without this arm the catch-all
        // would answer `Some(false)` for *equal* strings and could prune the
        // genuinely-taken branch, dropping its safety obligations.
        (ConstValue::Str { bytes: lhs }, ConstValue::Str { bytes: rhs }) => Some(lhs == rhs),
        // An `OpaqueConst` (fresh-symbolic aggregate/opaque constant — empty
        // collections, `Cell`, alloc handles, `&[&str]` tables) or an
        // `OpaqueScalar` (a const-generic / associated / `size_of` integer with no
        // evaluated value) carries no decidable value, so its equality is UNKNOWN.
        // Return `None` so the caller verifies BOTH branches rather than pruning
        // one. This MUST precede the `_ => Some(false)` catch-all: answering
        // "definitely unequal" for two opaque consts that are in fact equal would
        // prune the genuinely-taken branch and silently drop its safety obligations
        // — a false PROVE. (Same hazard the `Str` arm above guards against for equal
        // string literals.)
        (ConstValue::OpaqueConst, _) | (_, ConstValue::OpaqueConst) => None,
        // A `UnitVariantRef` (promoted `&Option<T>::None`-style reference constant)
        // value-lowers exactly like `OpaqueConst` — a fresh symbolic ref with no
        // decidable value — so its equality is UNKNOWN. Return `None` (verify BOTH
        // branches), never `Some(false)`, for the same false-PROVE hazard as above.
        (ConstValue::UnitVariantRef { .. }, _) | (_, ConstValue::UnitVariantRef { .. }) => None,
        (ConstValue::OpaqueScalar { .. }, _) | (_, ConstValue::OpaqueScalar { .. }) => None,
        // Trust: piece #7a — a const-generic PARAM value carries no decidable
        // value, so its equality is UNKNOWN. Return `None` (verify BOTH branches),
        // NEVER `Some(false)` — answering "definitely unequal" for a const-param
        // that is in fact equal (`N == N`) would prune the taken branch and drop
        // its safety obligations (a false PROVE). This MUST precede the
        // `_ => Some(false)` catch-all, exactly like the `OpaqueScalar` arm. It is
        // sound EVEN for two SYNTACTICALLY-distinct params `M`, `N`: `None`
        // over-approximates (checks both sides), never merges them.
        (ConstValue::ConstParam { .. }, _) | (_, ConstValue::ConstParam { .. }) => None,
        _ => Some(false),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BasicBlock, Place, Terminator};

    fn block_with(stmts: Vec<Statement>) -> BasicBlock {
        BasicBlock { id: crate::BlockId(0), stmts, terminator: Terminator::Return }
    }

    fn assign_eq(local: usize, lhs: ConstValue, rhs: ConstValue) -> Statement {
        Statement::Assign {
            place: Place { local, projections: vec![] },
            rvalue: Rvalue::BinaryOp(BinOp::Eq, Operand::Constant(lhs), Operand::Constant(rhs)),
            span: Default::default(),
        }
    }

    /// THE FOLD. `n % 2` lowers to `_c = (2 == 0); Assert(!_c, RemainderByZero)`.
    /// The failure branch is statically false, so the obligation does not exist.
    #[test]
    fn constant_nonzero_divisor_folds() {
        let block =
            block_with(vec![assign_eq(3, ConstValue::Uint(2, 32), ConstValue::Uint(0, 32))]);
        let cond = Operand::Move(Place { local: 3, projections: vec![] });
        assert!(
            assert_failure_is_known_false(&block, &cond, false),
            "a literal nonzero divisor carries no division obligation"
        );
    }

    /// NEGATIVE CONTROL — and the load-bearing one. A divisor the fold cannot
    /// decide must answer UNKNOWN so the caller KEEPS the obligation. If this ever
    /// returns true, both producers stop emitting a real division-by-zero check
    /// and nothing downstream can tell, because an obligation that is never
    /// emitted produces silence.
    #[test]
    fn unknown_divisor_does_not_fold() {
        // `_3 = (m == 0)` where `m` is a runtime local, not a constant.
        let block = block_with(vec![Statement::Assign {
            place: Place { local: 3, projections: vec![] },
            rvalue: Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place { local: 1, projections: vec![] }),
                Operand::Constant(ConstValue::Uint(0, 32)),
            ),
            span: Default::default(),
        }]);
        let cond = Operand::Move(Place { local: 3, projections: vec![] });
        assert!(
            !assert_failure_is_known_false(&block, &cond, false),
            "a runtime divisor MUST keep its obligation"
        );
    }

    /// NEGATIVE CONTROL — a literal ZERO divisor must NOT fold either. The failure
    /// branch is statically TRUE there, not false; folding on "statically decided"
    /// rather than "decided the safe way" would delete the obligation from the one
    /// program that definitely violates it.
    #[test]
    fn constant_zero_divisor_does_not_fold() {
        let block =
            block_with(vec![assign_eq(3, ConstValue::Uint(0, 32), ConstValue::Uint(0, 32))]);
        let cond = Operand::Move(Place { local: 3, projections: vec![] });
        assert!(
            !assert_failure_is_known_false(&block, &cond, false),
            "`n / 0` must keep its obligation — the assert FAILS, it is not vacuous"
        );
    }

    /// A direct constant definition is not authority after an intervening write
    /// through a differently named mutable alias.  The shared helper has no
    /// function-wide points-to oracle, so every projected write conservatively
    /// defeats the fold.  Both trust-vcgen and the TrustIR spine call this exact
    /// helper and therefore keep the assertion obligation together.
    #[test]
    fn projected_alias_write_defeats_a_stale_constant_fold() {
        let mut block =
            block_with(vec![assign_eq(3, ConstValue::Uint(2, 32), ConstValue::Uint(0, 32))]);
        block.stmts.push(Statement::Assign {
            place: Place { local: 8, projections: vec![crate::Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
            span: Default::default(),
        });
        let cond = Operand::Move(Place { local: 3, projections: vec![] });
        assert!(
            !assert_failure_is_known_false(&block, &cond, false),
            "an intervening projected write must keep the assertion obligation"
        );
    }

    /// An opaque constant answers UNKNOWN, never "definitely unequal". Answering
    /// the latter would let a caller prune a genuinely-taken branch and drop its
    /// safety obligations.
    #[test]
    fn opaque_constants_are_unknown_not_unequal() {
        assert_eq!(const_eq_truth(&ConstValue::OpaqueConst, &ConstValue::OpaqueConst), None);
        assert_eq!(const_eq_truth(&ConstValue::OpaqueConst, &ConstValue::Int(0)), None);
    }

    #[test]
    fn float_bits_constants_are_unknown_not_definitely_unequal() {
        let zero = ConstValue::FloatBits { bits: 0, width: 32 };
        assert_eq!(const_eq_truth(&zero, &zero), None);
        assert_eq!(const_eq_truth(&zero, &ConstValue::Float(0.0)), None);

        let block = block_with(vec![assign_eq(
            3,
            ConstValue::FloatBits { bits: 0, width: 32 },
            ConstValue::FloatBits { bits: 0, width: 32 },
        )]);
        let cond = Operand::Move(Place::local(3));
        assert!(
            !assert_failure_is_known_false(&block, &cond, false),
            "an unimplemented FloatBits equality must retain the assertion"
        );
    }
}
