//! The ONE spelling rule for trust-ir v50 uniform arrays, shared by both producers of trust-ir
//! from Rust: the THIR producer (`trust-thir-lower`) and this crate's MIR-oracle bridge.
//!
//! trust-ir v50 has two constant-size spellings of `[x; N]` (`docs/SPEC_RATIFICATIONS.md` §3.1):
//! `Const { Constant::Splat }` when `x` is a constant, and `Inst::ArraySplat` when `x` is a
//! register. Both denote the same value, so the interpretation differential already agrees on
//! either. But the differential's promoted-slot fold and its observation walk read INSTRUCTIONS,
//! and a producer pair that picks different spellings for the same source holds bodies the two
//! could have paired. So both producers call the functions below, with the same inputs: the
//! element's value and the nodes that the element's OWN lowering appended. Neither producer
//! scans anything else, which also keeps each decision proportional to the element's own text.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir::node::InstrNode;
use trust_ir::{Constant, Inst, Ty, ValueId};

/// What every lane of a uniform array is. A producer records it for the arrays it emits through
/// [`uniform_array`], so a later sub-array of one ([`uniform_sub_array`]) is spelled directly
/// rather than read back through memory.
#[derive(Clone, Debug, PartialEq)]
pub enum UniformLane {
    /// Every lane is this scalar constant (`Const { Constant::Splat }`).
    Const(Constant),
    /// Every lane is this register (`Inst::ArraySplat`).
    Value(ValueId),
}

/// The scalar constant `elem` is, when one of `pushed` defines it as `Const { ty: elem_ty, .. }`
/// holding an `Int`, `U128`, `Bool` or `Float`.
///
/// `pushed` must be exactly the nodes the element's own lowering appended, and nothing earlier.
/// That is what makes the rule the same in both producers. A literal or an evaluated named
/// const pushes its `Const`, so it folds. A variable read pushes nothing, because the value
/// already exists, so it does not fold, even when an earlier statement bound it to a constant.
/// Nothing else folds either:
///   * the THIR producer's deferred-local-const sentinel (`Constant::PhantomData` at a scalar
///     type, patched once at finalize by its node) must not be COPIED into a constant;
///   * an identity-bearing constant (`FnDef`, a symbol address) stays a register the splice
///     remaps, rather than a constant it would have to refuse.
pub fn scalar_const_element(pushed: &[InstrNode], elem: ValueId, elem_ty: &Ty) -> Option<Constant> {
    pushed.iter().rev().find_map(|node| {
        if node.results.as_slice() != [elem] {
            return None;
        }
        match &node.inst {
            Inst::Const {
                ty,
                value:
                    c @ (Constant::Int(_) | Constant::U128(_) | Constant::Bool(_) | Constant::Float(_)),
            } if ty == elem_ty => Some(c.clone()),
            _ => None,
        }
    })
}

/// `[elem; n]` as ONE instruction of type `array_ty` (`Ty::Array(_, n)`), with the lane it
/// repeats (`None` for `n == 0`, which has no lanes):
///   * `n == 0`: the empty-array constant;
///   * `elem_const` is `Some(c)`, from [`scalar_const_element`]: `Const { Constant::splat(c, n) }`;
///   * otherwise: `ArraySplat { array_ty, elem }`.
///
/// Every case is one element plus one length, whatever `n` is.
pub fn uniform_array(
    array_ty: Ty,
    n: u64,
    elem: ValueId,
    elem_const: Option<Constant>,
) -> (Inst, Option<UniformLane>) {
    if n == 0 {
        return (Inst::Const { ty: array_ty, value: Constant::Array(Vec::new()) }, None);
    }
    match elem_const {
        Some(c) => (
            Inst::Const { ty: array_ty, value: Constant::splat(c.clone(), n) },
            Some(UniformLane::Const(c)),
        ),
        None => (Inst::ArraySplat { ty: array_ty, value: elem }, Some(UniformLane::Value(elem))),
    }
}

/// A sub-array of `len` lanes (typed `sub_ty`, `Ty::Array(_, len)`) of a uniform array whose
/// lanes are `lane`: every lane of it is `lane` too. The empty sub-array is the empty constant,
/// the sole inhabitant of its type, whatever the source is.
pub fn uniform_sub_array(sub_ty: Ty, len: u64, lane: &UniformLane) -> Inst {
    match (len, lane) {
        (0, _) => empty_array(sub_ty),
        (_, UniformLane::Const(c)) => {
            Inst::Const { ty: sub_ty, value: Constant::splat(c.clone(), len) }
        }
        (_, UniformLane::Value(v)) => Inst::ArraySplat { ty: sub_ty, value: *v },
    }
}

/// The empty array constant at `ty` (`Ty::Array(_, 0)`), the sole inhabitant of that type.
pub fn empty_array(ty: Ty) -> Inst {
    Inst::Const { ty, value: Constant::Array(Vec::new()) }
}

/// The initializer of a byte-array global holding `bytes`, in trust-ir v50's canonical spelling
/// (`Constant::array`'s answer, bit for bit). A uniform payload of two or more bytes is ONE
/// `Constant::Splat`, decided on the byte slice itself, so it never builds one `Constant` per
/// byte. Any other payload is its list of bytes.
pub fn byte_array_constant(bytes: &[u8]) -> Constant {
    match bytes {
        [first, rest @ ..] if !rest.is_empty() && rest.iter().all(|b| b == first) => {
            Constant::splat(Constant::Int(i128::from(*first)), bytes.len() as u64)
        }
        _ => Constant::Array(bytes.iter().map(|b| Constant::Int(i128::from(*b))).collect()),
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::value::TyId;

    use super::*;

    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }

    fn node(inst: Inst, result: ValueId) -> InstrNode {
        InstrNode::new(inst).with_result(result)
    }

    #[test]
    fn only_a_scalar_const_the_element_itself_pushed_folds() {
        let lit = node(Inst::Const { ty: Ty::U8, value: Constant::Int(5) }, v(3));
        // The element's own lowering pushed its defining `Const`: it folds.
        assert_eq!(
            scalar_const_element(std::slice::from_ref(&lit), v(3), &Ty::U8),
            Some(Constant::Int(5))
        );
        // The same `Const` pushed BEFORE the element's lowering began (`let x = 5; [x; N]`):
        // the element pushed nothing, so nothing folds.
        assert_eq!(scalar_const_element(&[], v(3), &Ty::U8), None);
        // A `Const` of another type, or one defining another value, never folds.
        assert_eq!(scalar_const_element(std::slice::from_ref(&lit), v(3), &Ty::U16), None);
        assert_eq!(scalar_const_element(std::slice::from_ref(&lit), v(4), &Ty::U8), None);
        // The deferred-const sentinel and identity-bearing constants stay registers.
        for c in [Constant::PhantomData, Constant::FnDef(trust_ir::value::FuncId::new(0))] {
            let n = node(Inst::Const { ty: Ty::U8, value: c }, v(3));
            assert_eq!(scalar_const_element(std::slice::from_ref(&n), v(3), &Ty::U8), None);
        }
    }

    #[test]
    fn a_uniform_array_is_one_instruction_whatever_its_length() {
        let arr = |n| Ty::Array(TyId::new(0), n);
        for n in [1u64, 2, 3, 1024, u64::MAX] {
            let (inst, lane) = uniform_array(arr(n), n, v(7), Some(Constant::Int(0)));
            assert_eq!(
                inst,
                Inst::Const { ty: arr(n), value: Constant::splat(Constant::Int(0), n) }
            );
            assert_eq!(lane, Some(UniformLane::Const(Constant::Int(0))));
            let (inst, lane) = uniform_array(arr(n), n, v(7), None);
            assert_eq!(inst, Inst::ArraySplat { ty: arr(n), value: v(7) });
            assert_eq!(lane, Some(UniformLane::Value(v(7))));
        }
        let (inst, lane) = uniform_array(arr(0), 0, v(7), None);
        assert_eq!(inst, empty_array(arr(0)));
        assert_eq!(lane, None);
    }

    #[test]
    fn a_sub_array_of_a_uniform_array_is_its_lane_and_the_empty_one_is_the_constant() {
        let arr = |n| Ty::Array(TyId::new(0), n);
        let c = UniformLane::Const(Constant::Bool(true));
        let r = UniformLane::Value(v(2));
        for len in [1u64, 2, u64::MAX] {
            assert_eq!(
                uniform_sub_array(arr(len), len, &c),
                Inst::Const { ty: arr(len), value: Constant::splat(Constant::Bool(true), len) }
            );
            assert_eq!(
                uniform_sub_array(arr(len), len, &r),
                Inst::ArraySplat { ty: arr(len), value: v(2) }
            );
        }
        assert_eq!(uniform_sub_array(arr(0), 0, &c), empty_array(arr(0)));
        assert_eq!(uniform_sub_array(arr(0), 0, &r), empty_array(arr(0)));
    }

    #[test]
    fn byte_array_constant_is_the_canonical_constructor_without_a_constant_per_byte() {
        for bytes in [
            &b""[..],
            &b"a"[..],
            &b"aa"[..],
            &b"ab"[..],
            &b"aaab"[..],
            &[0u8; 64][..],
            &b"hello"[..],
        ] {
            assert_eq!(
                byte_array_constant(bytes),
                Constant::array(bytes.iter().map(|b| Constant::Int(i128::from(*b))).collect()),
                "{bytes:?}"
            );
        }
        assert_eq!(
            byte_array_constant(&[7u8; 64]),
            Constant::Splat { elem: Box::new(Constant::Int(7)), len: 64 }
        );
    }
}
