// trust-vcgen/check_null_zst.rs: rustc's `CheckNull` ZST test as an exact fact.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust: the pointee-ZST test of rustc's null-dereference check, decided
//! from the pointee's type when the type alone decides it.
//!
//! `compiler/rustc_mir_transform/src/check_null.rs` guards every non-borrow
//! use of `*p` (`p: *mut P`, `P: Sized`) with
//!
//! ```text
//! t = copy p as *const () (PtrToPtr)
//! a = copy t as usize (Transmute)
//! z = Ne(const size_of::<P>(), const 0_usize)
//! e = Eq(copy a, const 0_usize)
//! b = BitAnd(copy e, copy z)
//! n = Not(copy b)
//! assert(copy n, NullPointerDereference)
//! ```
//!
//! because a null pointer to a ZST may be dereferenced. In a generic body
//! `size_of::<P>()` is unevaluated, and the extractor lowers it to an
//! `OpaqueScalar` with no modeled value (since OPAQUE-SCALAR-ID-1 its own
//! symbol: its MIR site, or the extractor's key — the item and its normalized
//! generic arguments; until then one symbol per WIDTH, shared with every other
//! opaque `u64` of the function). So `z` was a free boolean and the check that
//! PASSED said only "`p` is non-null OR `P` is a ZST": a later
//! `&mut (*p).field` ("null reference produced", which has no ZST escape) could
//! not use it, and the typed-CHC query refuted that row with
//! `size_of::<P>() == 0, p == null` — a state no execution of
//! `IvarSlot<T> { initialized: bool, .. }` can reach (aterm-objc
//! `IvarSlot::dispose`, the proof-loss class "CHC refutes its own encoding").
//!
//! When `P` provably has a non-zero size for EVERY instantiation of its
//! generic parameters ([`ty_is_provably_non_zst`]), `z` IS `true`, so its
//! definition is emitted as the literal `true` INSTEAD of
//! `z == !(opaque == 0)`. The opaque symbol itself is left unconstrained:
//! nothing here asserts `size_of::<P>() != 0` about the symbol, so no other
//! occurrence that shares it (the same key) learns anything from this check.
//!
//! NAMING (merged 2026-10-08 onto OPAQUE-SCALAR-ID-1). This module once also
//! renamed the checks' `align_of::<P>()` / `size_of::<P>()` operands per
//! checked pointer LOCAL (`ub_check_opaque_symbol`), to split them off the
//! width-interned symbol the user's `size_of::<T>()` shared (a latent false
//! proof: `ivar_slot_dispose_opaque_leak`). OPAQUE-SCALAR-ID-1 names every
//! such constant by its site or its (item, generic arguments) key, which is
//! the split, value for value; the per-local key was DROPPED because it is
//! coarser than the value: rustc's `CheckAlignment` runs with
//! `FollowProjections`, so one pointer local is checked against
//! `align_of::<T>()` AND `align_of::<S<T>>()` (`field_vs_whole`), two values
//! the per-local key named alike (B'). One scheme remains, the trust-types one.
//!
//! SOUNDNESS. The fact holds when (1) the opaque operand is `size_of::<P>()`
//! for `P` = the pointee of `p`'s declared type, and (2) `size_of::<P>() > 0`
//! for every instantiation.
//! (1): `AssertKind::NullPointerDereference` has exactly one producer in
//! rustc, `check_null.rs::insert_null_check`; its `pointee_ty` is the pointee
//! of the BASE LOCAL's raw-pointer type (`check_pointers.rs`, run with
//! `NoFollowProjections` for this pass), and the statement sequence above is
//! matched EXACTLY, contiguously, ending at that assert, with every local a
//! whole local. Any other shape (a GVN-merged cast, a reordered block, a
//! projection) declines and keeps the old def.
//! (2): see [`ty_is_provably_non_zst`] — a struct, tuple or union is at least
//! as large as each of its fields, and a field whose own type is non-ZST
//! makes it non-ZST; nothing else is assumed. An unknown type declines.

use trust_types::{
    AdtKind, AssertMessage, BasicBlock, BinOp, ConstValue, Operand, Place, Rvalue, Statement,
    Terminator, Ty, UnOp, VerifiableFunction,
};

/// Recursion bound for [`ty_is_provably_non_zst`]; running out declines.
const NON_ZST_FUEL: u32 = 8;

/// True iff the size of `ty` is non-zero for every instantiation of the generic
/// parameters it mentions. `false` means "not shown", never "is a ZST".
///
/// * a scalar (`bool`, `char`, an integer, a float) and every pointer,
///   reference or fn pointer (thin or fat) occupies at least one byte;
/// * an ADT whose CONCRETE layout the extractor recorded has that size;
/// * a struct or a union is at least as large as each of its fields (a
///   struct stores every field at a distinct offset, even an uninhabited one,
///   because a partially initialized value must have room for the rest; a
///   union is at least as large as its largest field);
/// * a tuple, likewise;
/// * a non-empty array of a non-ZST element.
///
/// An enum is NOT admitted (rustc may drop uninhabited variants from its
/// layout), and neither is anything opaque: a type parameter, an
/// `Unsupported` leaf, a compacted `Datatype` reference, `()`, `!`, `str`.
pub(crate) fn ty_is_provably_non_zst(ty: &Ty) -> bool {
    non_zst_fueled(ty, NON_ZST_FUEL)
}

fn non_zst_fueled(ty: &Ty, fuel: u32) -> bool {
    let Some(fuel) = fuel.checked_sub(1) else {
        return false;
    };
    match ty {
        Ty::Bool | Ty::Char | Ty::PtrSizedInt { .. } => true,
        Ty::Int { width, .. } | Ty::Float { width } => *width > 0,
        Ty::Ref { .. } | Ty::RawPtr { .. } | Ty::FnPtr { .. } => true,
        Ty::Adt { layout: Some(layout), .. } if layout.size > 0 => true,
        Ty::Adt { fields, adt_kind: Some(AdtKind::Struct | AdtKind::Union), .. } => {
            fields.iter().any(|(_, field)| non_zst_fueled(field, fuel))
        }
        Ty::Tuple(fields) => fields.iter().any(|field| non_zst_fueled(field, fuel)),
        Ty::Array { elem, len } => *len > 0 && non_zst_fueled(elem, fuel),
        _ => false,
    }
}

/// `Some(local)` for a whole-local `Copy`/`Move` operand.
fn whole_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// `Some((dest, rvalue))` for an assignment to a whole local.
fn whole_assign(stmt: &Statement) -> Option<(usize, &Rvalue)> {
    match stmt {
        Statement::Assign { place: Place { local, projections }, rvalue, .. }
            if projections.is_empty() =>
        {
            Some((*local, rvalue))
        }
        _ => None,
    }
}

fn is_zero_usize(op: &Operand) -> bool {
    matches!(op, Operand::Constant(ConstValue::Uint(0, _) | ConstValue::Int(0)))
}

/// True iff `block.stmts[stmt_idx]` is the ZST test `z = Ne(size_of::<P>(), 0)`
/// of a `CheckNull` sequence (module docs) whose pointee `P` is provably
/// non-ZST, so `z` is `true` in every execution.
pub(crate) fn check_null_zst_test_is_true(
    func: &VerifiableFunction,
    block: &BasicBlock,
    stmt_idx: usize,
) -> bool {
    check_null_pointee(func, block, stmt_idx).is_some_and(ty_is_provably_non_zst)
}

/// The pointee type `P` of the `CheckNull` sequence whose ZST test is
/// `block.stmts[stmt_idx]`, or `None` when the block is not that exact shape.
fn check_null_pointee<'a>(
    func: &'a VerifiableFunction,
    block: &BasicBlock,
    stmt_idx: usize,
) -> Option<&'a Ty> {
    // The sequence is six contiguous statements, the ZST test third, and the
    // block ends right after them in the null-dereference assert.
    let first = stmt_idx.checked_sub(2)?;
    if block.stmts.len() != stmt_idx + 4 {
        return None;
    }
    let Terminator::Assert {
        cond, expected: true, msg: AssertMessage::NullPointerDereference, ..
    } = &block.terminator
    else {
        return None;
    };
    let seq = &block.stmts[first..];
    let (t, t_rv) = whole_assign(&seq[0])?;
    let (a, a_rv) = whole_assign(&seq[1])?;
    let (z, z_rv) = whole_assign(&seq[2])?;
    let (e, e_rv) = whole_assign(&seq[3])?;
    let (b, b_rv) = whole_assign(&seq[4])?;
    let (n, n_rv) = whole_assign(&seq[5])?;
    if whole_local(cond)? != n {
        return None;
    }
    // n = Not(b)
    let Rvalue::UnaryOp(UnOp::Not, n_op) = n_rv else { return None };
    if whole_local(n_op)? != b {
        return None;
    }
    // b = BitAnd(e, z)
    let Rvalue::BinaryOp(BinOp::BitAnd, b_l, b_r) = b_rv else { return None };
    if whole_local(b_l)? != e || whole_local(b_r)? != z {
        return None;
    }
    // e = Eq(a, 0)
    let Rvalue::BinaryOp(BinOp::Eq, e_l, e_r) = e_rv else { return None };
    if whole_local(e_l)? != a || !is_zero_usize(e_r) {
        return None;
    }
    // z = Ne(<opaque size_of::<P>()>, 0). Only the unevaluated form: a concrete
    // size is a literal the def already renders exactly.
    let Rvalue::BinaryOp(BinOp::Ne, Operand::Constant(ConstValue::OpaqueScalar { .. }), z_r) = z_rv
    else {
        return None;
    };
    if !is_zero_usize(z_r) {
        return None;
    }
    // a = t as usize
    let Rvalue::Cast(a_op, Ty::Int { signed: false, .. } | Ty::PtrSizedInt { signed: false }) =
        a_rv
    else {
        return None;
    };
    if whole_local(a_op)? != t {
        return None;
    }
    // t = p as *const ()
    let Rvalue::Cast(t_op, Ty::RawPtr { mutable: false, pointee }) = t_rv else { return None };
    if !matches!(pointee.as_ref(), Ty::Unit) {
        return None;
    }
    let p = whole_local(t_op)?;
    // Six distinct temporaries and a pointer that is none of them.
    let mut locals = [t, a, z, e, b, n, p];
    locals.sort_unstable();
    if locals.windows(2).any(|w| w[0] == w[1]) {
        return None;
    }
    match crate::local_ty_ref(func, p)? {
        Ty::RawPtr { pointee, .. } => Some(pointee.as_ref()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn adt(kind: Option<AdtKind>, fields: Vec<(&str, Ty)>) -> Ty {
        let Ty::Adt { name, fields, variants, .. } =
            Ty::adt("T", fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect())
        else {
            unreachable!()
        };
        Ty::Adt {
            name,
            fields,
            variants,
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: kind,
            arbitrary_precision: None,
            validity_wrapper: None,
        }
    }

    fn param() -> Ty {
        Ty::Unsupported {
            kind: "TyKind::Param".to_string(),
            detail: "generic parameter T/#0 needs monomorphization".to_string(),
        }
    }

    /// `MaybeUninit<T>` as the extractor lowers it: a union over `()` and a
    /// `ManuallyDrop<T>` whose leaf is the unmonomorphized parameter.
    fn maybe_uninit_of_param() -> Ty {
        adt(
            Some(AdtKind::Union),
            vec![
                ("uninit", Ty::Unit),
                ("value", adt(Some(AdtKind::Struct), vec![("value", param())])),
            ],
        )
    }

    #[test]
    fn a_bool_field_makes_a_generic_struct_non_zst() {
        // aterm-objc `IvarSlot<T> { initialized: bool, value: MaybeUninit<T> }`.
        let ivar_slot = adt(
            Some(AdtKind::Struct),
            vec![("initialized", Ty::Bool), ("value", maybe_uninit_of_param())],
        );
        assert!(ty_is_provably_non_zst(&ivar_slot));
    }

    #[test]
    fn a_generic_payload_alone_is_not_shown_non_zst() {
        // `T = ()` makes each of these a ZST.
        assert!(!ty_is_provably_non_zst(&param()));
        assert!(!ty_is_provably_non_zst(&maybe_uninit_of_param()));
        let phantom = adt(Some(AdtKind::Struct), vec![]);
        let twin =
            adt(Some(AdtKind::Struct), vec![("tag", phantom), ("value", maybe_uninit_of_param())]);
        assert!(!ty_is_provably_non_zst(&twin));
        assert!(!ty_is_provably_non_zst(&Ty::Unit));
        assert!(!ty_is_provably_non_zst(&Ty::Never));
        assert!(!ty_is_provably_non_zst(&Ty::Array { elem: Box::new(Ty::Bool), len: 0 }));
        assert!(!ty_is_provably_non_zst(&Ty::Tuple(vec![])));
    }

    #[test]
    fn only_stamped_structs_and_unions_are_walked() {
        // An enum may lose uninhabited variants from its layout, and an
        // unstamped (synthetic) ADT has no rustc kind behind it: both decline
        // even with a scalar field.
        assert!(!ty_is_provably_non_zst(&adt(Some(AdtKind::Enum), vec![("0", Ty::Bool)])));
        assert!(!ty_is_provably_non_zst(&adt(None, vec![("0", Ty::Bool)])));
        assert!(ty_is_provably_non_zst(&adt(
            Some(AdtKind::Union),
            vec![("a", Ty::Unit), ("b", Ty::Int { width: 8, signed: false })]
        )));
        assert!(ty_is_provably_non_zst(&Ty::Tuple(vec![Ty::Unit, Ty::Char])));
        assert!(ty_is_provably_non_zst(&Ty::Array {
            elem: Box::new(Ty::Float { width: 32 }),
            len: 1
        }));
        assert!(ty_is_provably_non_zst(&Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::Unit)
        }));
    }

    #[test]
    fn a_union_tailed_pointer_is_thin_and_a_param_tail_is_not() {
        let ivar_slot = adt(
            Some(AdtKind::Struct),
            vec![("initialized", Ty::Bool), ("value", maybe_uninit_of_param())],
        );
        let ptr = |pointee: Ty| Ty::RawPtr { mutable: true, pointee: Box::new(pointee) };
        let unit_ptr = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Unit) };
        assert!(crate::is_thin_pointer_identity_cast(&ptr(ivar_slot), &unit_ptr));
        // A struct whose TAIL is the parameter itself may be unsized
        // (`T: ?Sized`), and nothing in the lowered type says otherwise.
        let param_tail = adt(Some(AdtKind::Struct), vec![("len", Ty::Bool), ("tail", param())]);
        assert!(!crate::is_thin_pointer_identity_cast(&ptr(param_tail), &unit_ptr));
        // An UNSTAMPED union-shaped ADT keeps the tail walk.
        let unstamped = adt(None, vec![("uninit", Ty::Unit), ("value", param())]);
        assert!(!crate::is_thin_pointer_identity_cast(&ptr(unstamped), &unit_ptr));
    }
}
