//! Conservative E6 facet inference over a validated, closed MIR fragment.
//!
//! Facet booleans are potential proof inputs, so this lane must not infer trust
//! from diagnostic strings or malformed serialized MIR.
//!
//! FACETS CLOSE OVER CALLEES (ruled 2026-07-25,
//! `docs/design/2026-07-25-e6-call-admission-ruling-request.md`). A `Call` no
//! longer fails all four facets outright; it is valid exactly when the callee is
//! itself certified, reached by LEAST FIXPOINT over the call graph. The
//! precondition this lane used to wait on is met: the call IR carries an exact
//! identity, because `func_operand_name` builds the callee string from
//! `safe_def_path_str_with_args(tcx, def_id, generic_args)` — the DefId path
//! plus the exact call-site instantiation
//! (`crates/trust-mir-extract/src/convert.rs:5334-5349`).
//!
//! Three properties hold by construction, each pinned by a test:
//! - matching is EXACT def-path equality, never a suffix and never a bare name,
//!   so a same-suffix impostor (`mod evil { fn leaf(..) }`) is refused;
//! - an unknown or uncertified callee still fails closed;
//! - a recursive cycle never certifies, because no member can enter the set
//!   before the others — the correct direction for `Total`.
//!
//! A callee must satisfy ALL FOUR facets to be usable, not merely be structurally
//! valid: a caller inherits its callee's behaviour, so a callee that can panic
//! makes the caller panicking too. The external authority allowlist remains
//! empty and name-blind. Composition remains available as graph utilities in
//! [`crate::facet_propagation`].
//!
//! A function is considered only after a shared validator establishes the
//! closed v1 fragment: canonical block/local identities, complete successor
//! targets, scalar/drop-free local types, well-formed places and a small typed
//! statement/rvalue subset.  `Drop`, `Opaque`, `Unreachable` and `Resume` are
//! rejected even in unreachable blocks; calls are admitted only under the
//! closure described above.  This is intentionally more
//! conservative than the individual structural analyses; it prevents their
//! differing assumptions from combining into a false all-four result.

use std::collections::{HashMap, HashSet};

use crate::structural_determinism::{
    statement_is_nondeterministic, terminator_is_nondeterministic,
};
use crate::structural_panic_freedom::is_own_panic_site;
use crate::structural_purity::{statement_is_effectful, terminator_is_effectful};
use crate::structural_termination::{for_each_terminator_successor, is_control_flow_loop_free};
use crate::{
    BinOp, ConstValue, Operand, Place, Projection, Rvalue, Statement, Terminator, Ty,
    VerifiableFunction,
};

/// Which of the four E6 facets a function is structurally known to have.
///
/// A `true` is emitted only for a unique def-path whose body passes the shared
/// closed-fragment validator.  A `false` remains conservative: a deeper,
/// context-bound lane may establish the property later.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FacetSet {
    pub total: bool,
    pub no_panic: bool,
    pub pure: bool,
    pub deterministic: bool,
}

impl FacetSet {
    /// All four facets hold — the condition an eventual sealed E6 admission
    /// gate will require.
    #[must_use]
    pub fn all(self) -> bool {
        self.total && self.no_panic && self.pure && self.deterministic
    }
}

fn ty_in_closed_fragment(ty: &Ty) -> bool {
    match ty {
        Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char | Ty::Unit => true,
        Ty::Tuple(fields) => fields.iter().all(ty_in_closed_fragment),
        // DELIBERATELY NOT recursive into `Ty::Adt`. This predicate governs
        // EVERY local, so admitting a struct here would put one at an arbitrary
        // temporary -- which is what `the_struct_widening_reaches_parameters_
        // only_and_scalars_only` pins against, and which it caught when this
        // arm briefly existed. Struct nesting is allowed by
        // `ty_is_scalar_struct` instead, which is consulted only at the
        // positions that explicitly permit a struct.
        _ => false,
    }
}

/// Whether `ty` is an ALL-SCALAR STRUCT: an `Adt` with NO enum variants whose
/// every declared field is itself in the closed scalar fragment.
///
/// This is the ONE aggregate shape the closed fragment admits, and only at a
/// PARAMETER position (see [`local_ty_in_closed_fragment`]). Three things make
/// it safe to read a field of one:
///
///   * **No destructor, no drop glue.** Every field is a scalar and the struct
///     has no enum variants, so `needs_drop` is false and rustc emits no `Drop`
///     terminator — which the validator refuses outright anyway.
///   * **No hidden mutation channel — because the parameter is BY VALUE, not
///     because this test excludes `UnsafeCell`.** The function owns its own
///     copy of the struct, so no alias can change it during the call, and that
///     is the whole argument. It is NOT the argument the parenthetical here
///     used to make ("an interior-mutable field would be an `Adt`, and a nested
///     `Adt` is not in the closed fragment"): that stopped being true when the
///     recursion below admitted nested structs. `struct W { x: u32, c:
///     Cell<u32> }` answers `true` here — `Cell<u32>` is `UnsafeCell<u32>` is
///     `u32` all the way down — and it is admissible by value for the ownership
///     reason, not for a `Freeze` reason this function never checks. **A
///     `Freeze` claim needs `Ty::is_freeze`, and this is not it**, so do not
///     reuse this predicate to justify reading a field through a SHARED BORROW:
///     there the entry == exit property is exactly what an `UnsafeCell` on the
///     path would break. See `docs/KNOWN_HAZARDS.md`.
///   * **Nothing else opens up.** A field READ is admitted by `place_ty`, but
///     comparison still requires a comparable scalar, `SwitchInt` still
///     requires a scalar discriminant, and a NON-parameter local of struct type
///     is still refused — so a struct can be projected and nothing more.
///
/// ENUMS are excluded deliberately: an enum's `fields` list is the union view
/// across variants, so field `i` is variant-relative and is reached through a
/// `Downcast` the validator does not admit. Reading it as a struct field would
/// name a different value than the program does.
#[must_use]
pub fn ty_is_scalar_struct(ty: &Ty) -> bool {
    match ty {
        Ty::Adt { fields, variants, .. } => {
            // A field may be a scalar, or ITSELF an all-scalar struct:
            // `Term { coeff: i64, lit: Lit }` is a bundle of scalars however
            // deep the nesting goes, and the properties that make a flat one
            // safe hold verbatim -- no destructor or drop glue (no field needs
            // drop, no enum variants anywhere in the tree), no hidden mutation
            // channel (a `u32` field IS the `u32`), and no reference or float.
            // Before this, `Term` was refused for its `lit` field alone.
            //
            // The recursion terminates because Rust forbids a struct containing
            // itself by value: such a type is infinitely sized and never
            // reaches extraction.
            variants.is_empty()
                && fields
                    .iter()
                    .all(|(_, field)| ty_in_closed_fragment(field) || ty_is_scalar_struct(field))
        }
        _ => false,
    }
}

/// The signed payload width when `ty` is EXACTLY the std `Option<iN>` shape the
/// overflow-checked arithmetic lane admits, and `None` for every other type.
///
/// Pinned, fail-closed conditions (checked-arith spec §2/§5.3):
///   * the ADT is the std `core::option::Option` by extracted def-path name;
///   * it has EXACTLY the two std variants, in declaration order: `None`
///     (discriminant 0, no fields) and `Some` (discriminant 1, ONE field);
///   * the `Some` payload is a PLAIN SIGNED machine integer of a supported
///     width (8/16/32/64/128) — no reference, no `NonZero*`, no nested ADT;
///   * `disc_index_safe` is `true`: the rustc-layout-aware extractor confirmed
///     a fieldless/Direct TAG encoding, so variant indices 0/1 mean what they
///     say. Every NICHE-encoded `Option` (`Option<&T>`, `Option<NonZeroU8>`)
///     has `disc_index_safe == false` and is REFUSED here — a discriminant or
///     variant index read on a niche layout does not recover a dense tag, and
///     admitting one could silently swap the `Some`/`None` arms. `Option<iN>`
///     for a plain integer payload always has the Direct encoding (integers
///     leave `Option` no niche to steal).
///
/// This is the ONE definition of "the admissible Option shape": the E6 body
/// recognizer (`admissible_body::recognize_checked_arithmetic`) and the
/// diagnostic facet scan both call it, so the two lanes cannot drift.
#[must_use]
pub fn ty_is_std_option_of_signed(ty: &Ty) -> Option<u32> {
    let Ty::Adt { name, variants, disc_index_safe, .. } = ty else {
        return None;
    };
    if name != "core::option::Option" || !disc_index_safe {
        return None;
    }
    let [none_v, some_v] = variants.as_slice() else {
        return None;
    };
    if none_v.name != "None" || none_v.discriminant != 0 || !none_v.fields.is_empty() {
        return None;
    }
    if some_v.name != "Some" || some_v.discriminant != 1 {
        return None;
    }
    let [(_, payload)] = some_v.fields.as_slice() else {
        return None;
    };
    match payload {
        Ty::Int { width, signed: true } if matches!(width, 8 | 16 | 32 | 64 | 128) => Some(*width),
        _ => None,
    }
}

/// Whether `ty` is a local the CONTRACT lowering injected rather than a step of
/// the body's own computation.
///
/// An `ensures` written in CLOSURE form is materialised by
/// `contract_check_ensures` as an `Option<{closure}>` local of the very
/// function being contracted. Letting that local decide the function's facets
/// makes "does this body carry a specification" change "is this body pure" --
/// which is backwards, and self-defeating: attaching a contract removed the
/// admissibility the contract needs in order to be kernel-cited. Measured on
/// `veripb_core_proved::sat_term`, where ALL FOUR facets reported the same
/// single cause, `local _4 has type Adt { name: "core::option::Option", …
/// Closure { name: "lib::sat_term::{closure#0}" … } }`, and the same function
/// with a signature-form clause was admissible.
///
/// NARROW ON PURPOSE. Only a closure belonging to THIS function (`<def_path>::
/// {closure#N}`), bare or as an `Option` payload — the exact shape the lowering
/// mints. A closure from anywhere else, and any USE of one, is untouched:
/// this exempts a local from the TYPE gate only, and every statement and
/// terminator is still validated, so a body that actually calls a closure is
/// refused exactly as before.
#[must_use]
pub fn is_contract_injected_ty(ty: &Ty, def_path: &str) -> bool {
    fn own_closure(ty: &Ty, def_path: &str) -> bool {
        matches!(ty, Ty::Closure { name, .. }
            if name.strip_prefix(def_path).is_some_and(|rest| rest.starts_with("::{closure#")))
    }
    match ty {
        Ty::Closure { .. } => own_closure(ty, def_path),
        Ty::Adt { name, fields, .. } if name == "core::option::Option" => {
            fields.iter().any(|(_, field)| own_closure(field, def_path))
        }
        _ => false,
    }
}

/// Whether local `index` of a function with `arg_count` value parameters may
/// carry type `ty` inside the closed fragment.
///
/// Identical to the scalar rule for every local EXCEPT a source parameter
/// (`1..=arg_count`), which may additionally be an all-scalar struct
/// ([`ty_is_scalar_struct`]), and the RETURN SLOT (`index == 0`), which may
/// additionally be the std `Option<iN>` shape
/// ([`ty_is_std_option_of_signed`], checked-arithmetic widening). Restricting
/// the Option widening to the return slot is what keeps it to CONSTRUCTION:
/// no temporary and no parameter carries an `Option`, so one can be built and
/// returned but never read back, projected, or matched in this fragment.
#[must_use]
pub fn local_ty_in_closed_fragment(ty: &Ty, index: usize, arg_count: usize) -> bool {
    ty_in_closed_fragment(ty)
        || ((1..=arg_count).contains(&index) && ty_is_scalar_struct(ty))
        || (index == 0 && ty_is_std_option_of_signed(ty).is_some())
        // The RETURN SLOT may also be an all-scalar struct. A body that
        // CONSTRUCTS one is admitted by `rvalue_matches_ty`, which type-checks
        // every operand against the field it initialises; without this the
        // constructed value could never be returned, so that admission was
        // unreachable for its motivating case (`sat_term`).
        || (index == 0 && ty_is_scalar_struct(ty))
        || (index > arg_count && crate::e6_expr::tree::option_payload(ty).is_some())
}

/// The bit width of an integer type, `None` for anything else (including
/// pointer-sized integers, whose width is target-relative and therefore not a
/// disclosed narrowing boundary).
fn int_bit_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::Int { width, .. } => Some(*width),
        _ => None,
    }
}

fn ty_is_integer(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { .. } | Ty::PtrSizedInt { .. })
}

fn ty_is_comparable_scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char | Ty::Unit)
}

fn place_ty<'a>(func: &'a VerifiableFunction, place: &Place) -> Option<&'a Ty> {
    if matches!(place.projections.as_slice(), [Projection::Downcast(1), Projection::Field(0)]) {
        return crate::e6_expr::tree::option_payload(&func.body.locals.get(place.local)?.ty);
    }
    let mut ty = &func.body.locals.get(place.local)?.ty;
    for projection in &place.projections {
        match (projection, ty) {
            (Projection::Field(field), Ty::Tuple(fields)) => ty = fields.get(*field)?,
            // One declared field of an all-scalar STRUCT. `variants.is_empty()`
            // is the struct test: an enum's field is variant-relative and is
            // reached through a `Downcast`, which this loop refuses.
            (Projection::Field(field), Ty::Adt { fields, variants, .. }) if variants.is_empty() => {
                ty = &fields.get(*field)?.1;
            }
            _ => return None,
        }
    }
    Some(ty)
}

fn unsigned_fits_width(value: u128, width: u32) -> bool {
    (1..=128).contains(&width) && (width == 128 || value < (1u128 << width))
}

fn signed_fits_width(value: i128, width: u32) -> bool {
    if width == 128 {
        return true;
    }
    if !(1..128).contains(&width) {
        return false;
    }
    let bound = 1i128 << (width - 1);
    (-bound..bound).contains(&value)
}

fn constant_matches_ty(value: &ConstValue, expected: &Ty) -> bool {
    match (value, expected) {
        (ConstValue::Bool(_), Ty::Bool) | (ConstValue::Unit, Ty::Unit) => true,
        (ConstValue::Int(value), Ty::Int { width, signed: true }) => {
            signed_fits_width(*value, *width)
        }
        (ConstValue::Uint(value, encoded_width), Ty::Int { width, signed: false }) => {
            encoded_width == width && unsigned_fits_width(*value, *width)
        }
        // Pointer-sized constants need the target width in the certificate
        // context.  This rustc-free lane has no such context, so it fails closed.
        _ => false,
    }
}

fn operand_matches_ty(func: &VerifiableFunction, operand: &Operand, expected: &Ty) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place_ty(func, place).is_some_and(|actual| actual == expected)
        }
        Operand::Constant(value) => constant_matches_ty(value, expected),
        _ => false,
    }
}

fn operand_place_ty<'a>(func: &'a VerifiableFunction, operand: &Operand) -> Option<&'a Ty> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_ty(func, place),
        _ => None,
    }
}

fn operands_have_same_comparable_ty(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    match (operand_place_ty(func, lhs), operand_place_ty(func, rhs)) {
        (Some(lhs_ty), Some(rhs_ty)) => lhs_ty == rhs_ty && ty_is_comparable_scalar(lhs_ty),
        (Some(lhs_ty), None) => {
            ty_is_comparable_scalar(lhs_ty) && operand_matches_ty(func, rhs, lhs_ty)
        }
        (None, Some(rhs_ty)) => {
            ty_is_comparable_scalar(rhs_ty) && operand_matches_ty(func, lhs, rhs_ty)
        }
        // With two untyped constants there is no closed carrier to bind the
        // operation to, so do not guess from literal spelling.
        (None, None) => false,
    }
}

fn rvalue_matches_ty(func: &VerifiableFunction, rvalue: &Rvalue, destination: &Ty) -> bool {
    match rvalue {
        Rvalue::Use(operand) => operand_matches_ty(func, operand, destination),
        Rvalue::UnaryOp(crate::UnOp::Not, operand)
            if matches!(destination, Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. }) =>
        {
            operand_matches_ty(func, operand, destination)
        }
        Rvalue::BinaryOp(op, lhs, rhs) => match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                *destination == Ty::Bool && operands_have_same_comparable_ty(func, lhs, rhs)
            }
            // Trust (E6 expansion I3′): the non-short-circuit connectives over
            // `bool` — `s & i & n`, `acc ^ c`. Over `bool` they are the total,
            // effect-free `Bool.and`/`Bool.or`/`Bool.xor` (they cannot panic,
            // and none is in `has_undischarged_panic_operation`'s list), so
            // they close exactly when both operands and the destination are
            // `bool`. A MIXED `bool`/integer operand pair falls through to
            // the integer arm below, which the `bool` destination refuses.
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor if *destination == Ty::Bool => {
                operand_matches_ty(func, lhs, &Ty::Bool) && operand_matches_ty(func, rhs, &Ty::Bool)
            }
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::Shl
            | BinOp::Shr
                if ty_is_integer(destination) =>
            {
                operand_matches_ty(func, lhs, destination)
                    && operand_matches_ty(func, rhs, destination)
            }
            _ => false,
        },
        // Integer WIDTH-CHANGING casts only, and the boundary is disclosed
        // rather than inherited. A width-changing integer cast has exactly one
        // canonical semantics, and the kernel models both directions: a
        // STRICTLY narrower destination is truncation (`BitVec.ofNat n
        // (toNat v)`, the guarded-narrow model), and a STRICTLY wider one is
        // the extension the SOURCE type's signedness determines (sext for
        // signed -- `sextWide`, the `eq_ok` model -- zext for unsigned; Rust
        // `as` widening follows source signedness, so nothing here is a
        // choice). A SAME-WIDTH cast is refused: it is a value
        // REINTERPRETATION (signed<->unsigned over the same bits) that the
        // validated fragment does not model, and it is precisely the shape
        // the adversarial audit caught when this arm briefly admitted every
        // scalar cast (`cast_is_declined_by_the_compiler_visible_firewall`).
        Rvalue::Cast(operand, cast_ty) => {
            let dest_w = int_bit_width(destination);
            let src_w = operand_place_ty(func, operand).and_then(|t| int_bit_width(&t));
            cast_ty == destination && matches!((dest_w, src_w), (Some(d), Some(s)) if d != s)
        }
        Rvalue::CheckedBinaryOp(BinOp::Add | BinOp::Sub | BinOp::Mul, lhs, rhs) => {
            let Ty::Tuple(fields) = destination else { return false };
            let [value_ty, overflow_ty] = fields.as_slice() else { return false };
            ty_is_integer(value_ty)
                && *overflow_ty == Ty::Bool
                && operand_matches_ty(func, lhs, value_ty)
                && operand_matches_ty(func, rhs, value_ty)
        }
        // Constructing the std `Option<iN>` return value (checked-arithmetic
        // widening): value-total and effect-free — an `Aggregate` writes only
        // its destination place. Valid ONLY when the destination is the pinned
        // std Option shape ([`ty_is_std_option_of_signed`]), the aggregate
        // names the SAME ADT, and the variant/operand pairing is exactly
        // `None`/no operands (variant 0) or `Some`/one payload of the exact
        // signed width (variant 1). The variant indices are trustworthy
        // because the shape gate requires the Direct tag encoding
        // (`disc_index_safe`); a niche-encoded Option never gets here. Every
        // other aggregate kind (tuples, arrays, closures, other ADTs) remains
        // outside the closed fragment.
        Rvalue::Aggregate(crate::AggregateKind::Adt { name, variant, active_field, .. }, ops) => {
            let Ty::Adt { name: dest_name, fields, variants, .. } = destination else {
                return false;
            };
            // A union field-write aliases its siblings, so it is never a
            // value-total construction of the whole destination.
            if name != dest_name || active_field.is_some() {
                return false;
            }
            if let Some(width) = ty_is_std_option_of_signed(destination) {
                return match (variant, ops.as_slice()) {
                    (0, []) => true,
                    (1, [payload]) => {
                        operand_matches_ty(func, payload, &Ty::Int { width, signed: true })
                    }
                    _ => false,
                };
            }
            // A PLAIN STRUCT construction — `Term { coeff, lit }`, the shape
            // every mapping rule's per-term step builds. `variants` is empty
            // exactly for a struct, so an enum (where a field is
            // variant-relative and the tag encoding would have to be trusted)
            // still falls out here.
            //
            // FAITHFULNESS: the aggregate writes only its destination place,
            // and every operand is matched against the DECLARED type of the
            // field it initialises, by position, with the operand count
            // required to equal the field count -- so a construction that
            // omits, reorders past the end, or mistypes a field is refused.
            // That makes it value-total, effect-free, deterministic and
            // panic-free, which is exactly what the four facets assert.
            if !variants.is_empty() || *variant != 0 || ops.len() != fields.len() {
                return false;
            }
            ops.iter()
                .zip(fields.iter())
                .all(|(op, (_, field_ty))| operand_matches_ty(func, op, field_ty))
        }
        Rvalue::Discriminant(place) => {
            ty_is_integer(destination)
                && place_ty(func, place).and_then(crate::e6_expr::tree::option_payload).is_some()
        }
        _ => false,
    }
}

fn statement_is_valid(func: &VerifiableFunction, statement: &Statement) -> bool {
    match statement {
        // A write to a CONTRACT-INJECTED local is specification machinery, not
        // a step of the body -- the same reason the type gate exempts the local
        // itself (`is_contract_injected_ty`). Exempting the local alone was not
        // enough: the lowering also STORES the closure into it, and that store
        // is an `Option<{closure}>` destination no rvalue rule admits, so the
        // firewall declined the body for the contract's own bookkeeping.
        //
        // Still narrow: only a write whose DESTINATION is that local. Reads of
        // it, and every other statement, go through the normal rules.
        Statement::Assign { place, .. }
            if place_ty(func, place)
                .is_some_and(|ty| is_contract_injected_ty(ty, &func.def_path)) =>
        {
            true
        }
        Statement::Assign { place, rvalue, .. } => place_ty(func, place)
            .is_some_and(|destination| rvalue_matches_ty(func, rvalue, destination)),
        Statement::StorageLive(local) | Statement::StorageDead(local) => {
            *local < func.body.locals.len()
        }
        Statement::PlaceMention(place) => place_ty(func, place).is_some(),
        Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => true,
        // These constructs need effect, initializedness, borrow, intrinsic, or
        // unsupported-MIR semantics that the closed leaf lane does not carry.
        _ => false,
    }
}

fn target_exists(func: &VerifiableFunction, target: crate::BlockId) -> bool {
    target.0 < func.body.blocks.len()
        && func.body.blocks.get(target.0).is_some_and(|block| block.id == target)
}

fn switch_operand_is_valid(func: &VerifiableFunction, operand: &Operand) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_ty(func, place).is_some_and(|ty| {
            matches!(ty, Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char)
        }),
        Operand::Constant(ConstValue::Bool(_) | ConstValue::Int(_) | ConstValue::Uint(_, _)) => {
            true
        }
        _ => false,
    }
}

fn total_primitive_call_is_valid(
    func: &VerifiableFunction,
    method: crate::RustcTotalPrimitiveMethod,
    args: &[Operand],
    dest: &Place,
    target: Option<crate::BlockId>,
    is_atomic: bool,
    is_foreign: bool,
    is_unsafe_sig: bool,
) -> bool {
    let expected = Ty::Int { width: method.width(), signed: false };
    !is_atomic
        && !is_foreign
        && !is_unsafe_sig
        && args.len() == 2
        && args.iter().all(|arg| operand_matches_ty(func, arg, &expected))
        && place_ty(func, dest).is_some_and(|actual| actual == &expected)
        && target.is_some_and(|normal| target_exists(func, normal))
}

fn terminator_is_valid(
    func: &VerifiableFunction,
    terminator: &Terminator,
    certified_callees: &crate::fx::FxHashSet<&str>,
) -> bool {
    match terminator {
        Terminator::Goto(target) => target_exists(func, *target),
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            if !switch_operand_is_valid(func, discr) || !target_exists(func, *otherwise) {
                return false;
            }
            if targets.len() <= 16 {
                targets.iter().enumerate().all(|(idx, (value, target))| {
                    !targets[..idx].iter().any(|(prev, _)| prev == value)
                        && target_exists(func, *target)
                })
            } else {
                let mut values = crate::fx::FxHashSet::with_capacity_and_hasher(
                    targets.len(),
                    Default::default(),
                );
                targets
                    .iter()
                    .all(|(value, target)| values.insert(*value) && target_exists(func, *target))
            }
        }
        Terminator::Return => true,
        Terminator::Assert { cond, target, .. } => {
            operand_matches_ty(func, cond, &Ty::Bool) && target_exists(func, *target)
        }
        // A call is valid exactly when the callee is ITSELF certified. The
        // precondition this arm used to wait on — "exact instance/signature
        // extraction" — is met: `func_operand_name` builds the callee string
        // from `safe_def_path_str_with_args(tcx, def_id, generic_args)`, the
        // DefId path plus the exact call-site instantiation
        // (crates/trust-mir-extract/src/convert.rs:5334-5349). Matching is
        // EXACT equality against a certified function's own `def_path`; never a
        // suffix and never a bare name, so a same-suffix impostor is refused.
        //
        // `infer_facets` reaches the certified set by least fixpoint, so a
        // recursive cycle never certifies: no member can enter the set before
        // the others. That refusal is the correct direction for Total.
        Terminator::Call {
            func: callee,
            args,
            dest,
            target,
            atomic,
            is_foreign,
            is_unsafe_sig,
            ..
        } => {
            // A callee is usable when it is certified in THIS unit, or when it
            // is one of Trust's modeled compiler intrinsics. The latter is why
            // functions using `saturating_add`/`ctpop`/`bswap` can be admitted
            // at all: those bodies live in `core` and are never present in the
            // unit, so the fixpoint alone can never reach them.
            //
            // The intrinsic marker is forgery-resistant BY CONSTRUCTION rather
            // than by convention: `@` cannot occur in a Rust identifier, so
            // authored source cannot manufacture the namespace by declaring a
            // lookalike `mod intrinsics { fn ctpop(..) }`, and the prefix is
            // stamped only after TyCtxt confirms the exact DefId is one of the
            // modeled intrinsics (crates/trust-mir-extract/src/convert.rs:5447).
            // Every intrinsic on that list is pure, total, deterministic and
            // panic-free, which is what makes inheriting them sound.
            if let Some(method) = crate::RustcTotalPrimitiveMethod::classify(callee) {
                return total_primitive_call_is_valid(
                    func,
                    method,
                    args,
                    dest,
                    *target,
                    atomic.is_some(),
                    *is_foreign,
                    *is_unsafe_sig,
                );
            }
            // TG14: signed wrapping primitives are total at their exact
            // compiler-authenticated scalar signature. Frozen E6 recognition
            // remains unsigned; only the separate tree reader consumes these.
            if let Some((_, expected)) = crate::e6_expr::tree::wrapping_primitive(callee) {
                return atomic.is_none()
                    && !is_foreign
                    && !is_unsafe_sig
                    && args.len() == 2
                    && args.iter().all(|arg| operand_matches_ty(func, arg, &expected))
                    && place_ty(func, dest) == Some(&expected)
                    && (*target).is_some_and(|normal| target_exists(func, normal));
            }
            // An overflow-CHECKED signed primitive method (Shape A of the
            // checked-arithmetic lane): compiler-marked identity, exactly two
            // operands of the SIGNED width, destination typed at the pinned
            // std `Option<iN>` shape of the SAME width. Pure, total,
            // deterministic, and panic-free as a function into `Option` —
            // rustc lowers it to an overflow-FLAG branch with no `Assert`.
            if let Some(method) = crate::RustcCheckedPrimitiveMethod::classify(callee) {
                let expected = Ty::Int { width: method.width(), signed: true };
                return atomic.is_none()
                    && !is_foreign
                    && !is_unsafe_sig
                    && args.len() == 2
                    && args.iter().all(|arg| operand_matches_ty(func, arg, &expected))
                    && place_ty(func, dest)
                        .and_then(ty_is_std_option_of_signed)
                        .is_some_and(|w| w == method.width())
                    && (*target).is_some_and(|normal| target_exists(func, normal));
            }
            if let Some((_, expected)) = crate::e6_expr::tree::checked_primitive(callee) {
                return atomic.is_none()
                    && !is_foreign
                    && !is_unsafe_sig
                    && args.len() == 2
                    && args.iter().all(|arg| operand_matches_ty(func, arg, &expected))
                    && place_ty(func, dest).and_then(crate::e6_expr::tree::option_payload)
                        == Some(&expected)
                    && (*target).is_some_and(|normal| target_exists(func, normal));
            }
            // This namespace is closed: a malformed or excluded marker must
            // not fall through to same-unit call authority even if a hostile
            // serialized bundle also supplies the same impossible def-path.
            // The `ToString::to_string` totality stamp belongs here too: it is
            // a panic-freedom fact about ONE std call, not an E6 facet grammar
            // (the call allocates), so it grants no facet at all.
            if callee.starts_with(crate::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX)
                || callee.starts_with(crate::TRUST_RUSTC_WRAPPING_REFUTATION_METHOD_PATH_PREFIX)
                || callee.starts_with(crate::TRUST_RUSTC_CHECKED_PRIMITIVE_METHOD_PATH_PREFIX)
                || callee.starts_with(crate::TRUST_TOTAL_TO_STRING_PATH_PREFIX)
                // Trust (std-call-summaries P2): the panic-freedom-only intrinsic
                // stamp grants NO facet. Its callees (the transcendentals, the
                // `nsz` selections) are nondeterministic, so a Deterministic facet
                // read off it would be false; it is closed here like the others.
                || callee.starts_with(crate::TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX)
            {
                return false;
            }
            certified_callees.contains(callee.as_str())
                || callee.starts_with(crate::TRUST_RUSTC_INTRINSIC_PATH_PREFIX)
        }
        Terminator::TailCall { func: callee, atomic, is_foreign, is_unsafe_sig, .. } => {
            // No destination/continuation exists to validate for a tail call.
            // Its facets are inherited only from the exact certified callee
            // (the least fixpoint still rejects recursive cycles), or from the
            // closed compiler-intrinsic namespace.
            atomic.is_none()
                && !is_foreign
                && !is_unsafe_sig
                // Trust (std-call-summaries P2): never via the panic-freedom-only
                // stamp, even if a hostile unit supplies its spelling as a path.
                && !callee.starts_with(crate::TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX)
                && (certified_callees.contains(callee.as_str())
                    || callee.starts_with(crate::TRUST_RUSTC_INTRINSIC_PATH_PREFIX))
        }
        Terminator::Drop { .. }
        | Terminator::Opaque { .. }
        | Terminator::Unreachable
        | Terminator::Resume => false,
    }
}

fn is_valid_closed_leaf_intrinsic(
    func: &VerifiableFunction,
) -> Option<HashSet<crate::BlockId>> {
    if func.def_path.trim().is_empty()
        || func.body.blocks.is_empty()
        || func.body.locals.is_empty()
        || func.body.arg_count >= func.body.locals.len()
        // The return type must be a closed scalar, the std `Option<iN>` shape
        // (checked-arithmetic widening), or an ALL-SCALAR STRUCT — the same
        // three the local-0 gate below admits through
        // `local_ty_in_closed_fragment`. The two rules have to agree: local 0's
        // type is required to EQUAL the return type on the next line, so a
        // return type this check refuses makes that gate unreachable, which is
        // what kept a constructed `Term { coeff, lit }` out even after
        // `rvalue_matches_ty` learned to admit building one.
        || !(ty_in_closed_fragment(&func.body.return_ty)
            || ty_is_std_option_of_signed(&func.body.return_ty).is_some()
            || ty_is_scalar_struct(&func.body.return_ty))
        || func.body.locals[0].ty != func.body.return_ty
    {
        return None;
    }

    // Require the serialized identities to agree with their canonical vector
    // positions.  This simultaneously rejects duplicates, sparse IDs, a missing
    // bb0/return slot, and the map-overwrite/index-confusion class of bugs.
    if func.body.locals.iter().enumerate().any(|(index, local)| {
        local.index != index
            || !(local_ty_in_closed_fragment(&local.ty, index, func.body.arg_count)
                || is_contract_injected_ty(&local.ty, &func.def_path))
    }) || func.body.blocks.iter().enumerate().any(|(index, block)| block.id.0 != index)
    {
        return None;
    }

    if !func
        .body
        .blocks
        .iter()
        .all(|block| block.stmts.iter().all(|statement| statement_is_valid(func, statement)))
    {
        return None;
    }

    Some(crate::e6_expr::tree::checked_option_impossible_defaults(func))
}

fn terminators_are_valid(
    func: &VerifiableFunction,
    impossible: &HashSet<crate::BlockId>,
    certified_callees: &crate::fx::FxHashSet<&str>,
) -> bool {
    func.body.blocks.iter().all(|block| {
        terminator_is_valid(func, &block.terminator, certified_callees)
            || (matches!(block.terminator, Terminator::Unreachable)
                && impossible.contains(&block.id))
    })
}

fn has_undischarged_panic_operation(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|block| {
        block.stmts.iter().any(|statement| {
            matches!(
                statement,
                Statement::Assign {
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add
                            | BinOp::Sub
                            | BinOp::Mul
                            | BinOp::Div
                            | BinOp::Rem
                            | BinOp::Shl
                            | BinOp::Shr,
                        _,
                        _,
                    ),
                    ..
                }
            )
        })
    })
}

/// Single-pass reachability evaluation of `(no_panic, pure, deterministic)` over
/// a canonical block slice (`block.id.0 == index`), reusing caller-supplied
/// `seen` and `stack` buffers across functions.
fn reachable_structural_facets(
    blocks: &[crate::BasicBlock],
    seen: &mut Vec<bool>,
    stack: &mut Vec<usize>,
) -> (bool, bool, bool) {
    if blocks.is_empty() {
        return (false, false, false);
    }
    seen.clear();
    seen.resize(blocks.len(), false);
    seen[0] = true;
    stack.clear();
    stack.push(0);
    let mut no_panic = true;
    let mut pure = true;
    let mut deterministic = true;
    while let Some(idx) = stack.pop() {
        let Some(block) = blocks.get(idx) else {
            continue;
        };
        if no_panic && is_own_panic_site(&block.terminator) {
            no_panic = false;
        }
        if pure
            && (terminator_is_effectful(&block.terminator)
                || block.stmts.iter().any(statement_is_effectful))
        {
            pure = false;
        }
        if deterministic
            && (terminator_is_nondeterministic(&block.terminator)
                || block.stmts.iter().any(statement_is_nondeterministic))
        {
            deterministic = false;
        }
        if !no_panic && !pure && !deterministic {
            break;
        }
        for_each_terminator_successor(&block.terminator, |s| {
            if let Some(slot) = seen.get_mut(s.0)
                && !*slot
            {
                *slot = true;
                stack.push(s.0);
            }
        });
    }
    (no_panic, pure, deterministic)
}

/// Infer the conservative E6 structural facets for every function.
///
/// Duplicate def-paths are rejected as a group: the result contains the path
/// once with no positive facets.  This avoids `HashMap` collection collapsing a
/// good and bad body onto one apparently certified identity.
#[must_use]
pub fn infer_facets(functions: &[VerifiableFunction]) -> HashMap<String, FacetSet> {
    let mut occurrences: crate::fx::FxHashMap<&str, usize> =
        crate::fx::FxHashMap::with_capacity_and_hasher(functions.len(), Default::default());
    for func in functions {
        *occurrences.entry(func.def_path.as_str()).or_default() += 1;
    }

    enum FuncCandidate<'a> {
        Invalid,
        CertifiedOdt,
        ClosedLeaf {
            func: &'a VerifiableFunction,
            impossible: HashSet<crate::BlockId>,
            intrinsic_facets: FacetSet,
        },
    }

    // Precompute all call-independent structural checks and intrinsic facets once
    // per function before the fixpoint loop.
    let mut candidates = Vec::with_capacity(functions.len());
    let mut certified: crate::fx::FxHashSet<&str> =
        crate::fx::FxHashSet::with_capacity_and_hasher(functions.len(), Default::default());
    let mut pending: Vec<usize> = Vec::with_capacity(functions.len());
    let mut reach_seen: Vec<bool> = Vec::new();
    let mut reach_stack: Vec<usize> = Vec::new();

    for (idx, func) in functions.iter().enumerate() {
        let unique = occurrences.get(func.def_path.as_str()) == Some(&1);
        if !unique {
            candidates.push(FuncCandidate::Invalid);
            continue;
        }
        // TG11: a separate closed reader checks every constructor path,
        // including that the default Unreachable is impossible. This is
        // not a general enum/Unreachable addition to the v1 whitelist.
        if crate::e6_odt::read(func).is_some() {
            certified.insert(func.def_path.as_str());
            candidates.push(FuncCandidate::CertifiedOdt);
            continue;
        }
        let Some(impossible) = is_valid_closed_leaf_intrinsic(func) else {
            candidates.push(FuncCandidate::Invalid);
            continue;
        };
        let (reach_no_panic, reach_pure, reach_deterministic) =
            reachable_structural_facets(&func.body.blocks, &mut reach_seen, &mut reach_stack);
        let intrinsic_facets = FacetSet {
            total: is_control_flow_loop_free(func),
            no_panic: reach_no_panic && !has_undischarged_panic_operation(func),
            pure: reach_pure,
            deterministic: reach_deterministic,
        };
        if intrinsic_facets.all() {
            pending.push(idx);
        }
        candidates.push(FuncCandidate::ClosedLeaf { func, impossible, intrinsic_facets });
    }

    // Facets are closed over callees by LEAST FIXPOINT. Round 0 certifies
    // nothing (besides call-free ODT bodies), so only call-free bodies qualify;
    // each round then admits callers whose callees are all already certified.
    // The predicate is monotone in the certified set and the set is bounded by
    // the function count, so this terminates — and a recursive cycle NEVER
    // certifies, because no member can enter the set before the others.
    let mut newly_certified: Vec<&str> = Vec::new();
    loop {
        pending.retain(|&idx| {
            let FuncCandidate::ClosedLeaf { func, impossible, .. } = &candidates[idx] else {
                return false;
            };
            if terminators_are_valid(func, impossible, &certified) {
                newly_certified.push(func.def_path.as_str());
                false
            } else {
                true
            }
        });
        if newly_certified.is_empty() {
            break;
        }
        certified.extend(newly_certified.drain(..));
    }

    let all_true = FacetSet { total: true, no_panic: true, pure: true, deterministic: true };
    let mut inferred = HashMap::with_capacity(functions.len());
    for (func, candidate) in functions.iter().zip(candidates.iter()) {
        let facets = match candidate {
            FuncCandidate::Invalid => FacetSet::default(),
            FuncCandidate::CertifiedOdt => all_true,
            FuncCandidate::ClosedLeaf { func, impossible, intrinsic_facets } => {
                if certified.contains(func.def_path.as_str())
                    || (*intrinsic_facets != FacetSet::default()
                        && terminators_are_valid(func, impossible, &certified))
                {
                    *intrinsic_facets
                } else {
                    FacetSet::default()
                }
            }
        };
        inferred.insert(func.def_path.clone(), facets);
    }
    inferred
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AssertMessage, BasicBlock, BlockId, LocalDecl, SourceSpan, UnwindEdge, VerifiableBody,
    };

    fn func_with(
        def_path: &str,
        locals: Vec<LocalDecl>,
        blocks: Vec<BasicBlock>,
        arg_count: usize,
        return_ty: Ty,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: def_path.rsplit("::").next().unwrap_or(def_path).to_string(),
            def_path: def_path.to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks,
                arg_count,
                return_ty,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// `fn <path>(x: u64) -> u64 { x }` — a certifiable call-free leaf.
    fn identity_leaf(def_path: &str) -> VerifiableFunction {
        func_with(
            def_path,
            vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            1,
            Ty::u64(),
        )
    }

    /// `fn <path>(x: u64) -> u64 { <callee>(x) }` — one call, nothing else.
    fn caller_of(def_path: &str, callee: &str) -> VerifiableFunction {
        func_with(
            def_path,
            vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: None,
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
            ],
            1,
            Ty::u64(),
        )
    }

    fn binary_caller_of(def_path: &str, callee: &str) -> VerifiableFunction {
        let mut caller = caller_of(def_path, callee);
        let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator else {
            unreachable!("caller_of always builds one call")
        };
        args.push(Operand::Copy(Place::local(1)));
        caller
    }

    /// RULED 2026-07-25: facets close over callees, so a function that calls a
    /// CERTIFIED function is itself certifiable. Before this, any call poisoned
    /// all four facets and nothing that called anything could ever be admitted
    /// — which excluded essentially all real Rust.
    #[test]
    fn a_call_to_a_certified_callee_is_certified() {
        let facets = infer_facets(&[
            identity_leaf("crate::leaf"),
            caller_of("crate::caller", "crate::leaf"),
        ]);
        let leaf = facets.get("crate::leaf").copied().unwrap_or_default();
        assert!(leaf.pure && leaf.total && leaf.no_panic && leaf.deterministic, "leaf: {leaf:?}");
        let caller = facets.get("crate::caller").copied().unwrap_or_default();
        assert!(
            caller.pure && caller.total && caller.no_panic && caller.deterministic,
            "a caller of a certified callee must certify: {caller:?}"
        );
    }

    /// THE IDENTITY TRAP, and the reason the old allowlist was hardcoded off.
    /// Callees are matched by EXACT def-path equality — the string carries the
    /// DefId path plus call-site instantiation — so a same-suffix impostor
    /// (`mod evil { fn leaf(..) }`) must NOT be mistaken for the real callee.
    #[test]
    fn a_same_suffix_impostor_callee_is_refused() {
        // The compilation unit contains `crate::leaf`, but the caller invokes
        // `evil::leaf`. Same last segment, different item.
        let facets =
            infer_facets(&[identity_leaf("crate::leaf"), caller_of("crate::caller", "evil::leaf")]);
        let caller = facets.get("crate::caller").copied().unwrap_or_default();
        assert!(
            !(caller.pure && caller.total && caller.no_panic && caller.deterministic),
            "a same-suffix impostor must not certify the caller: {caller:?}"
        );
    }

    /// A modeled compiler intrinsic is usable as a callee even though its body
    /// lives in `core` and is never present in the unit — the fixpoint alone
    /// could never reach it, so without this arm every function using
    /// `saturating_add`/`ctpop`/`bswap` stays unadmittable.
    ///
    /// Soundness rests on the marker being forgery-resistant BY CONSTRUCTION:
    /// `@` cannot appear in a Rust identifier, so authored source cannot
    /// manufacture the namespace with a lookalike `mod intrinsics { fn ctpop }`,
    /// and the prefix is stamped only after TyCtxt confirms the exact DefId.
    /// The second half of this test is that guarantee, exercised.
    #[test]
    fn a_marked_compiler_intrinsic_callee_is_usable_but_a_lookalike_is_not() {
        let marked = format!("{}core::intrinsics::ctpop", crate::TRUST_RUSTC_INTRINSIC_PATH_PREFIX);
        let facets = infer_facets(&[caller_of("crate::popcount", &marked)]);
        let f = facets.get("crate::popcount").copied().unwrap_or_default();
        assert!(
            f.pure && f.total && f.no_panic && f.deterministic,
            "a TyCtxt-confirmed intrinsic must be usable as a callee: {f:?}"
        );

        // The same path WITHOUT the marker is source-spellable, so it must not
        // be trusted: this is the `mod intrinsics { fn ctpop(..) }` impostor.
        let bare = infer_facets(&[caller_of("crate::popcount", "core::intrinsics::ctpop")]);
        let g = bare.get("crate::popcount").copied().unwrap_or_default();
        assert!(
            !(g.pure && g.total && g.no_panic && g.deterministic),
            "an unmarked, source-spellable intrinsic lookalike must be refused: {g:?}"
        );
    }

    /// Trust (std-call-summaries P2): the panic-freedom-only intrinsic stamp is NOT
    /// a facet marker. `maximum_number_nsz_f64` may return either signed zero and
    /// `sinf64`'s precision varies by platform, so a caller must not be certified
    /// Deterministic through it, not even when a hostile unit also supplies a
    /// function whose path IS the stamped spelling.
    #[test]
    fn a_panic_free_only_intrinsic_stamp_grants_no_facet() {
        for name in ["maximum_number_nsz_f64", "minimumf64", "sinf64"] {
            let stamped = format!(
                "{}core::intrinsics::{name}",
                crate::TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX
            );
            let facets = infer_facets(&[caller_of("crate::uses", &stamped)]);
            let f = facets.get("crate::uses").copied().unwrap_or_default();
            assert!(!f.deterministic, "{name}: no Deterministic facet via the stamp: {f:?}");
            assert!(!f.all(), "{name}: no facet set via the stamp: {f:?}");
            let hostile =
                infer_facets(&[identity_leaf(&stamped), caller_of("crate::uses", &stamped)]);
            let g = hostile.get("crate::uses").copied().unwrap_or_default();
            assert!(!g.deterministic && !g.all(), "{name}: hostile same-unit spelling: {g:?}");
        }
    }

    #[test]
    fn a_marked_total_primitive_method_is_usable_but_a_lookalike_is_not() {
        let marked = format!(
            "{}core::num::<impl u64>::wrapping_add",
            crate::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX
        );
        let facets = infer_facets(&[binary_caller_of("crate::winc", &marked)]);
        let f = facets.get("crate::winc").copied().unwrap_or_default();
        assert!(
            f.pure && f.total && f.no_panic && f.deterministic,
            "a TyCtxt-confirmed total primitive method must be usable as a callee: {f:?}"
        );

        let bare =
            infer_facets(&[binary_caller_of("crate::winc", "core::num::<impl u64>::wrapping_add")]);
        let g = bare.get("crate::winc").copied().unwrap_or_default();
        assert!(
            !(g.pure && g.total && g.no_panic && g.deterministic),
            "an unmarked, source-spellable primitive-method lookalike must be refused: {g:?}"
        );

        for malformed in [
            "@trust-rustc-total-primitive-method::core::num::<impl u128>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add::suffix",
            "@trust-rustc-total-primitive-method::evil::num::<impl u64>::wrapping_add",
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_add",
        ] {
            // Include a same-unit function carrying the hostile serialized
            // identity: the reserved namespace must never inherit ordinary
            // fixpoint authority when its closed grammar rejects it.
            let bad = infer_facets(&[
                identity_leaf(malformed),
                binary_caller_of("crate::bad_marker_caller", malformed),
            ]);
            assert!(
                !bad.get("crate::bad_marker_caller").copied().unwrap_or_default().all(),
                "malformed/excluded marker must fail closed even if present in the certified set: {malformed}"
            );
        }

        for mutation in ["wrong-arity", "wrong-width", "foreign", "unsafe"] {
            let mut bad = binary_caller_of("crate::bad_shape", &marked);
            let Terminator::Call { args, is_foreign, is_unsafe_sig, .. } =
                &mut bad.body.blocks[0].terminator
            else {
                unreachable!("binary_caller_of always builds one call")
            };
            match mutation {
                "wrong-arity" => {
                    args.pop();
                }
                "wrong-width" => {
                    bad.body.locals[1].ty = Ty::u32();
                }
                "foreign" => *is_foreign = true,
                "unsafe" => *is_unsafe_sig = true,
                _ => unreachable!(),
            }
            let inferred = infer_facets(&[bad]);
            assert!(
                !inferred.get("crate::bad_shape").copied().unwrap_or_default().all(),
                "invalid marked-call shape must fail closed: {mutation}"
            );
        }
    }

    /// The `@trust-total-to-string::` stamp says one std call cannot panic; it is
    /// not an E6 facet grammar, so a stamped callee grants no facet — not even
    /// when a hostile serialized bundle also supplies a same-unit function
    /// carrying the stamped identity (which the ordinary fixpoint would certify).
    #[test]
    fn a_to_string_stamped_callee_is_a_closed_namespace() {
        let stamped = format!(
            "{}<str as alloc::string::ToString>::to_string",
            crate::TRUST_TOTAL_TO_STRING_PATH_PREFIX
        );
        let facets =
            infer_facets(&[identity_leaf(&stamped), caller_of("crate::stamped_caller", &stamped)]);
        assert!(
            !facets.get("crate::stamped_caller").copied().unwrap_or_default().all(),
            "a to_string totality stamp must never inherit same-unit facet authority"
        );
    }

    /// An unknown callee still fails closed — the closure widens admission only
    /// to callees actually present and certified in this unit.
    #[test]
    fn a_call_to_an_uncertified_callee_stays_refused() {
        let facets = infer_facets(&[caller_of("crate::caller", "crate::absent")]);
        let caller = facets.get("crate::caller").copied().unwrap_or_default();
        assert!(
            !(caller.pure && caller.total && caller.no_panic && caller.deterministic),
            "an unknown callee must fail closed: {caller:?}"
        );
    }

    /// Recursion never certifies. The fixpoint starts from the empty set, so no
    /// member of a cycle can enter before the others. This is the direction that
    /// matters: `Total` must never be assumed of a body that may not terminate.
    #[test]
    fn recursion_never_certifies() {
        let direct = infer_facets(&[caller_of("crate::loop_me", "crate::loop_me")]);
        let f = direct.get("crate::loop_me").copied().unwrap_or_default();
        assert!(!(f.pure && f.total && f.no_panic && f.deterministic), "self-recursion: {f:?}");

        let mutual = infer_facets(&[
            caller_of("crate::ping", "crate::pong"),
            caller_of("crate::pong", "crate::ping"),
        ]);
        for name in ["crate::ping", "crate::pong"] {
            let g = mutual.get(name).copied().unwrap_or_default();
            assert!(
                !(g.pure && g.total && g.no_panic && g.deterministic),
                "mutual recursion must not certify {name}: {g:?}"
            );
        }
    }

    fn unit_func(def_path: &str, blocks: Vec<BasicBlock>) -> VerifiableFunction {
        func_with(
            def_path,
            vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks,
            0,
            Ty::Unit,
        )
    }

    fn block(id: usize, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts: Vec::new(), terminator }
    }

    fn call(callee: &str, target: Option<usize>) -> Terminator {
        Terminator::Call {
            func: callee.to_string(),
            args: Vec::new(),
            dest: Place::local(0),
            target: target.map(BlockId),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
            unwind: UnwindEdge::Unreachable,
        }
    }

    fn inferred(func: VerifiableFunction) -> FacetSet {
        let path = func.def_path.clone();
        infer_facets(&[func])[&path]
    }

    #[test]
    fn validated_call_free_leaf_has_all_four_facets() {
        assert!(inferred(unit_func("crate::leaf", vec![block(0, Terminator::Return)])).all());
    }

    #[test]
    fn every_call_fails_all_facets_closed() {
        for callee in
            ["core::num::<impl u64>::wrapping_add", "evil::wrapping_add", "crate::internal"]
        {
            let f = unit_func(
                "crate::caller",
                vec![block(0, call(callee, Some(1))), block(1, Terminator::Return)],
            );
            assert_eq!(inferred(f), FacetSet::default(), "call to {callee}");
        }

        let no_target = unit_func("crate::caller", vec![block(0, call("crate::never", None))]);
        assert_eq!(inferred(no_target), FacetSet::default());
    }

    #[test]
    fn ambiguous_bare_callee_never_falls_through_as_external() {
        let left = unit_func("crate::left::helper", vec![block(0, Terminator::Return)]);
        let right = unit_func("crate::right::helper", vec![block(0, Terminator::Return)]);
        let caller = unit_func(
            "crate::caller",
            vec![block(0, call("helper", Some(1))), block(1, Terminator::Return)],
        );
        let facets = infer_facets(&[left, right, caller]);
        assert!(facets["crate::left::helper"].all());
        assert!(facets["crate::right::helper"].all());
        assert_eq!(facets["crate::caller"], FacetSet::default());
    }

    #[test]
    fn duplicate_def_path_rejects_every_body_under_that_identity() {
        let good = unit_func("crate::same", vec![block(0, Terminator::Return)]);
        let bad = unit_func("crate::same", vec![block(0, Terminator::Resume)]);
        let facets = infer_facets(&[good, bad]);
        assert_eq!(facets.len(), 1);
        assert_eq!(facets["crate::same"], FacetSet::default());
    }

    #[test]
    fn malformed_block_identity_or_target_fails_closed() {
        let missing_bb0 = unit_func("crate::missing", vec![block(1, Terminator::Return)]);
        assert_eq!(inferred(missing_bb0), FacetSet::default());

        let duplicate = unit_func(
            "crate::duplicate",
            vec![block(0, Terminator::Goto(BlockId(1))), block(0, Terminator::Return)],
        );
        assert_eq!(inferred(duplicate), FacetSet::default());

        let dangling = unit_func("crate::dangling", vec![block(0, Terminator::Goto(BlockId(9)))]);
        assert_eq!(inferred(dangling), FacetSet::default());

        let dangling_switch = unit_func(
            "crate::switch",
            vec![block(
                0,
                Terminator::SwitchInt {
                    discr: Operand::Constant(ConstValue::Bool(true)),
                    targets: vec![(1, BlockId(9))],
                    otherwise: BlockId(0),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            )],
        );
        assert_eq!(inferred(dangling_switch), FacetSet::default());

        let dangling_assert = unit_func(
            "crate::assert",
            vec![block(
                0,
                Terminator::Assert {
                    cond: Operand::Constant(ConstValue::Bool(true)),
                    expected: true,
                    msg: AssertMessage::BoundsCheck,
                    target: BlockId(4),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                },
            )],
        );
        assert_eq!(inferred(dangling_assert), FacetSet::default());
    }

    #[test]
    fn malformed_local_identity_or_place_fails_closed() {
        let bad_local = func_with(
            "crate::bad_local",
            vec![LocalDecl { index: 1, ty: Ty::Unit, name: None }],
            vec![block(0, Terminator::Return)],
            0,
            Ty::Unit,
        );
        assert_eq!(inferred(bad_local), FacetSet::default());

        let mut bad_place = unit_func("crate::bad_place", vec![block(0, Terminator::Return)]);
        bad_place.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Unit)),
            span: SourceSpan::default(),
        });
        assert_eq!(inferred(bad_place), FacetSet::default());
    }

    #[test]
    fn exceptional_drop_and_opaque_terminators_fail_all_facets_closed() {
        let forbidden = [
            Terminator::Drop {
                place: Place::local(0),
                target: BlockId(0),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Unreachable,
            },
            Terminator::Opaque {
                kind: "InlineAsm".into(),
                targets: vec![BlockId(0)],
                span: SourceSpan::default(),
            },
            Terminator::Unreachable,
            Terminator::Resume,
        ];
        for (index, terminator) in forbidden.into_iter().enumerate() {
            let path = format!("crate::forbidden_{index}");
            assert_eq!(inferred(unit_func(&path, vec![block(0, terminator)])), FacetSet::default());
        }
    }

    #[test]
    fn raw_division_never_claims_no_panic_without_a_discharge() {
        let u64_ty = Ty::Int { width: 64, signed: false };
        let mut f = func_with(
            "crate::div",
            vec![
                LocalDecl { index: 0, ty: u64_ty.clone(), name: None },
                LocalDecl { index: 1, ty: u64_ty.clone(), name: Some("x".into()) },
            ],
            vec![block(0, Terminator::Return)],
            1,
            u64_ty,
        );
        f.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(0, 64)),
            ),
            span: SourceSpan::default(),
        });
        let facets = inferred(f);
        assert!(facets.total && facets.pure && facets.deterministic);
        assert!(!facets.no_panic);
        assert!(!facets.all());
    }

    #[test]
    fn checked_arithmetic_in_the_closed_fragment_remains_certifiable() {
        let u64_ty = Ty::Int { width: 64, signed: false };
        let checked_ty = Ty::Tuple(vec![u64_ty.clone(), Ty::Bool]);
        let mut f = func_with(
            "crate::checked",
            vec![
                LocalDecl { index: 0, ty: u64_ty.clone(), name: None },
                LocalDecl { index: 1, ty: u64_ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: checked_ty, name: None },
            ],
            vec![block(0, Terminator::Return)],
            1,
            u64_ty,
        );
        f.body.blocks[0].stmts.extend([
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(1, 64)),
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 2,
                    projections: vec![Projection::Field(0)],
                })),
                span: SourceSpan::default(),
            },
        ]);
        assert!(inferred(f).all());
    }

    /// E6 expansion I3′ (design note §6): `&`/`|`/`^` over `bool` are in the
    /// closed fragment — ay's `self_ind & init_valid & entry_ind` and
    /// `acc ^ contribution` get all four facets — and a bit operation whose
    /// operand is an integer, or whose destination is not `bool`, gets none
    /// from this arm.
    #[test]
    fn bool_bitwise_is_closed() {
        let bool_fn = |path: &str, op: BinOp, operand_ty: Ty, dest: Ty| {
            func_with(
                path,
                vec![
                    LocalDecl { index: 0, ty: dest.clone(), name: None },
                    LocalDecl { index: 1, ty: operand_ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: operand_ty, name: Some("b".into()) },
                ],
                vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                2,
                dest,
            )
        };
        for op in [BinOp::BitAnd, BinOp::BitOr, BinOp::BitXor] {
            let path = format!("crate::bool_{op:?}");
            let facets = infer_facets(&[bool_fn(&path, op, Ty::Bool, Ty::Bool)]);
            assert!(facets[&path].all(), "{op:?} over bool: {:?}", facets[&path]);
            // An integer operand into a `bool` destination is not this arm.
            let mixed = format!("crate::mixed_{op:?}");
            let facets = infer_facets(&[bool_fn(&mixed, op, Ty::u64(), Ty::Bool)]);
            assert!(!facets[&mixed].pure, "{op:?} over u64 into bool: {:?}", facets[&mixed]);
        }
    }

    /// The GUARDED-NARROW lane's one new statement form: an integer-to-integer
    /// cast is pure, total, deterministic and panic-free, so the whole
    /// `if fits { Some(x as i64) } else { None }` body stays certifiable. This
    /// is what makes `veripb_core_proved::guard::narrow` facet-admissible at
    /// all — before the `Rvalue::Cast` arm the body failed EVERY facet on the
    /// cast statement alone (measured: probe c2, `admissible=false`).
    #[test]
    fn an_integer_cast_stays_in_the_closed_fragment() {
        let i64_ty = Ty::Int { width: 64, signed: true };
        let i128_ty = Ty::Int { width: 128, signed: true };
        let option = Ty::adt_enum_with_disc_safety(
            "core::option::Option",
            vec![
                crate::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                crate::VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), i64_ty.clone())],
                },
            ],
            true,
        );
        let agg = |variant: usize| crate::AggregateKind::Adt {
            name: "core::option::Option".into(),
            variant,
            active_field: None,
            args: Some("core::option::Option<i64>".into()),
        };
        let cmp = |place: usize, op: BinOp, bound: i128| Statement::Assign {
            place: Place::local(place),
            rvalue: Rvalue::BinaryOp(
                op,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(bound)),
            ),
            span: SourceSpan::default(),
        };
        let switch = |flag: usize, zero: usize, other: usize| Terminator::SwitchInt {
            discr: Operand::Move(Place::local(flag)),
            targets: vec![(0, BlockId(zero))],
            otherwise: BlockId(other),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        let f = func_with(
            "crate::narrow",
            vec![
                LocalDecl { index: 0, ty: option.clone(), name: None },
                LocalDecl { index: 1, ty: i128_ty, name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: i64_ty.clone(), name: None },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![cmp(2, BinOp::Ge, -9_223_372_036_854_775_808)],
                    terminator: switch(2, 3, 1),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![cmp(3, BinOp::Le, 9_223_372_036_854_775_807)],
                    terminator: switch(3, 3, 2),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Aggregate(agg(1), vec![Operand::Move(Place::local(4))]),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(agg(0), vec![]),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            1,
            option,
        );
        assert!(inferred(f.clone()).all(), "the guarded-narrow body must certify all four facets");

        // Fail-closed edges of the new arm: the cast's recorded TARGET type
        // must be the destination's own declared type (a mismatch is a
        // malformed body, not a cast this lane models), and a NON-integer end
        // is refused outright.
        let mut mistyped = f.clone();
        mistyped.body.blocks[2].stmts[0] = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Cast(
                Operand::Copy(Place::local(1)),
                Ty::Int { width: 32, signed: true },
            ),
            span: SourceSpan::default(),
        };
        assert_eq!(inferred(mistyped), FacetSet::default(), "cast target/destination mismatch");

        let mut const_source = f;
        const_source.body.blocks[2].stmts[0] = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Cast(
                Operand::Constant(ConstValue::Int(1)),
                Ty::Int { width: 64, signed: true },
            ),
            span: SourceSpan::default(),
        };
        assert_eq!(inferred(const_source), FacetSet::default(), "a constant cast source");
    }

    #[test]
    fn assert_poisons_only_no_panic_after_validation() {
        let f = unit_func(
            "crate::asserted",
            vec![
                block(
                    0,
                    Terminator::Assert {
                        cond: Operand::Constant(ConstValue::Bool(true)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                ),
                block(1, Terminator::Return),
            ],
        );
        let facets = inferred(f);
        assert!(facets.total && facets.pure && facets.deterministic);
        assert!(!facets.no_panic);
    }

    #[test]
    fn control_flow_cycle_poisons_only_total_after_validation() {
        let f = unit_func("crate::cycle", vec![block(0, Terminator::Goto(BlockId(0)))]);
        let facets = inferred(f);
        assert!(!facets.total);
        assert!(facets.no_panic && facets.pure && facets.deterministic);
    }

    #[test]
    fn non_closed_type_fails_every_facet() {
        let float = Ty::Float { width: 64 };
        let f = func_with(
            "crate::float",
            vec![LocalDecl { index: 0, ty: float.clone(), name: None }],
            vec![block(0, Terminator::Return)],
            0,
            float,
        );
        assert_eq!(inferred(f), FacetSet::default());
    }

    // -----------------------------------------------------------------------
    // E6/E9 widening increment 7 — an all-scalar STRUCT is in the closed
    // fragment, at a PARAMETER position only.
    // -----------------------------------------------------------------------

    fn scalar_cst() -> Ty {
        Ty::adt("crate::Cst", vec![("degree".into(), Ty::u64()), ("coeff".into(), Ty::u64())])
    }

    /// `fn deg(c: Cst) -> u64 { c.degree }` with local 1 declared at `param_ty`
    /// and the body reading `projections` off it.
    fn field_leaf(param_ty: Ty, projections: Vec<Projection>) -> VerifiableFunction {
        func_with(
            "crate::deg",
            vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: param_ty, name: Some("c".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place { local: 1, projections })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            1,
            Ty::u64(),
        )
    }

    #[test]
    fn an_all_scalar_struct_parameter_certifies_and_its_field_read_is_typed() {
        let facets = infer_facets(std::slice::from_ref(&field_leaf(
            scalar_cst(),
            vec![Projection::Field(0)],
        )));
        assert!(
            facets["crate::deg"].all(),
            "reading a scalar field of a by-value struct parameter is pure, total, \
             deterministic and panic-free: {:?}",
            facets["crate::deg"]
        );
    }

    /// `Cst { degree, coeff }` built from two parameters, returned by value.
    fn constructs(
        ret_ty: Ty,
        adt_name: &str,
        ops: Vec<Operand>,
        locals: Vec<LocalDecl>,
        argc: usize,
    ) -> VerifiableFunction {
        func_with(
            "crate::mk",
            locals,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        crate::AggregateKind::Adt {
                            name: adt_name.into(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        ops,
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            argc,
            ret_ty,
        )
    }

    /// The motivating case: a body that CONSTRUCTS an all-scalar struct and
    /// returns it is pure, total, deterministic and panic-free. Without this,
    /// `rvalue_matches_ty`'s struct admission was unreachable — the constructed
    /// value could never live in the return slot.
    #[test]
    fn a_constructed_scalar_struct_return_certifies() {
        let f = constructs(
            scalar_cst(),
            "crate::Cst",
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            vec![
                LocalDecl { index: 0, ty: scalar_cst(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("d".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("c".into()) },
            ],
            2,
        );
        assert!(infer_facets(std::slice::from_ref(&f))["crate::mk"].all());
    }

    /// A NESTED all-scalar struct — `Term { coeff: u64, lit: Lit }`, the shape
    /// a per-term rule step returns. `Lit` is a struct, which is exactly why
    /// `Term` was refused before the field check learned to recurse.
    #[test]
    fn a_constructed_nested_scalar_struct_return_certifies() {
        let lit = Ty::adt("crate::Lit", vec![("var".into(), Ty::u64()), ("neg".into(), Ty::Bool)]);
        let term =
            Ty::adt("crate::Term", vec![("coeff".into(), Ty::u64()), ("lit".into(), lit.clone())]);
        let f = constructs(
            term.clone(),
            "crate::Term",
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            vec![
                LocalDecl { index: 0, ty: term, name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("coeff".into()) },
                LocalDecl { index: 2, ty: lit, name: Some("lit".into()) },
            ],
            2,
        );
        assert!(infer_facets(std::slice::from_ref(&f))["crate::mk"].all());
    }

    /// `Option<{closure}>` as the contract lowering mints it, for `owner`.
    fn contract_local(owner: &str) -> Ty {
        Ty::adt(
            "core::option::Option",
            vec![
                ("__tag".into(), Ty::Int { width: 64, signed: true }),
                (
                    "__v1_0".into(),
                    Ty::Closure {
                        name: format!("{owner}::{{closure#0}}"),
                        upvars: vec![Ty::u64()],
                        call: None,
                    },
                ),
            ],
        )
    }

    /// Writing a closure-form `ensures` must not remove the function's own
    /// admissibility. The predicate is materialised as an `Option<{closure}>`
    /// local of the contracted function; it is specification machinery, not a
    /// step of the body, and it exists only under the contract cfg.
    #[test]
    fn a_contract_injected_closure_local_does_not_poison_the_facets() {
        let mut f = constructs(
            scalar_cst(),
            "crate::Cst",
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            vec![
                LocalDecl { index: 0, ty: scalar_cst(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("d".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("c".into()) },
            ],
            2,
        );
        f.body.locals.push(LocalDecl { index: 3, ty: contract_local("crate::mk"), name: None });
        assert!(
            infer_facets(std::slice::from_ref(&f))["crate::mk"].all(),
            "the contract's own closure local must not decide the body's facets"
        );
    }

    /// The FULL shape the lowering leaves behind: the contract local AND the
    /// store into it. Exempting the local alone was not enough -- the store is
    /// an `Option<{closure}>` destination that no rvalue rule admits, so the
    /// firewall still declined the body for the contract's own bookkeeping.
    #[test]
    fn a_contract_injected_store_does_not_poison_the_facets() {
        let mut f = constructs(
            scalar_cst(),
            "crate::Cst",
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            vec![
                LocalDecl { index: 0, ty: scalar_cst(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("d".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("c".into()) },
            ],
            2,
        );
        f.body.locals.push(LocalDecl { index: 3, ty: contract_local("crate::mk"), name: None });
        // …and the lowering's own store into it, ahead of the body's return.
        f.body.blocks[0].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                span: SourceSpan::default(),
            },
        );
        assert!(
            infer_facets(std::slice::from_ref(&f))["crate::mk"].all(),
            "the contract's own store must not decide the body's facets"
        );
    }

    /// The exemption is keyed to THIS function. A closure belonging to anything
    /// else is an ordinary non-scalar local and still takes the body out.
    #[test]
    fn a_foreign_closure_local_still_poisons_the_facets() {
        let mut f = constructs(
            scalar_cst(),
            "crate::Cst",
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            vec![
                LocalDecl { index: 0, ty: scalar_cst(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("d".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("c".into()) },
            ],
            2,
        );
        f.body.locals.push(LocalDecl {
            index: 3,
            ty: contract_local("crate::somewhere_else"),
            name: None,
        });
        assert!(
            !infer_facets(std::slice::from_ref(&f))["crate::mk"].all(),
            "only THIS function's contract closure is exempt"
        );
    }

    /// A field built from an operand of the WRONG type is refused: the
    /// admission type-checks each operand against the field it initialises.
    #[test]
    fn a_mistyped_struct_field_operand_is_refused() {
        let f = constructs(
            scalar_cst(),
            "crate::Cst",
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            vec![
                LocalDecl { index: 0, ty: scalar_cst(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("d".into()) },
                // `coeff` is declared `u64`; this operand is a bool.
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) },
            ],
            2,
        );
        assert!(!infer_facets(std::slice::from_ref(&f))["crate::mk"].all());
    }

    #[test]
    fn the_struct_widening_reaches_parameters_only_and_scalars_only() {
        // A NON-SCALAR field takes the whole struct back out of the fragment.
        let with_slice = Ty::adt(
            "crate::Cst",
            vec![
                ("degree".into(), Ty::u64()),
                ("terms".into(), Ty::Slice { elem: Box::new(Ty::u64()) }),
            ],
        );
        assert!(
            !infer_facets(std::slice::from_ref(&field_leaf(
                with_slice,
                vec![Projection::Field(0)]
            )))["crate::deg"]
                .all()
        );

        // An ENUM is refused: `fields` is the union view, so field 0 is
        // variant-relative and does not name one value of the parameter.
        let enum_ty = Ty::adt_enum(
            "crate::E",
            vec![crate::VariantDef {
                name: "A".into(),
                discriminant: 0,
                fields: vec![("degree".into(), Ty::u64())],
            }],
        );
        assert!(!infer_facets(std::slice::from_ref(&field_leaf(
            enum_ty,
            vec![Projection::Field(0)]
        )))["crate::deg"]
            .all());

        // A struct at a NON-PARAMETER local stays out: the widening admits a
        // field READ of an input, not aggregates in general.
        let mut temp = field_leaf(scalar_cst(), vec![Projection::Field(0)]);
        temp.body.locals.push(LocalDecl { index: 2, ty: scalar_cst(), name: None });
        assert!(!infer_facets(std::slice::from_ref(&temp))["crate::deg"].all());

        // A struct RETURN slot whose body does not CONSTRUCT it is still
        // refused -- here the body still assigns a `u64` field read into a
        // struct-typed `_0`, which `rvalue_matches_ty` rejects outright. (The
        // slot itself may now be an all-scalar struct; what makes a body
        // admissible is that it builds one, which
        // `a_constructed_scalar_struct_return_certifies` covers.)
        let mut ret = field_leaf(scalar_cst(), vec![Projection::Field(0)]);
        ret.body.locals[0] = LocalDecl { index: 0, ty: scalar_cst(), name: None };
        ret.body.return_ty = scalar_cst();
        assert!(!infer_facets(std::slice::from_ref(&ret))["crate::deg"].all());

        // A DEREF projection is still outside `place_ty`, so a `&Cst`-shaped
        // read never types.
        assert!(
            !infer_facets(std::slice::from_ref(&field_leaf(
                scalar_cst(),
                vec![Projection::Deref, Projection::Field(0)]
            )))["crate::deg"]
                .all()
        );
    }

    // -----------------------------------------------------------------------
    // Checked-arithmetic widening: the std `Option<iN>` return, the Option
    // aggregates, and the marked checked/cold_path callees inside the closed
    // fragment.
    // -----------------------------------------------------------------------

    fn option_of_signed(width: u32) -> Ty {
        Ty::adt_enum_with_disc_safety(
            "core::option::Option",
            vec![
                crate::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                crate::VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), Ty::Int { width, signed: true })],
                },
            ],
            true,
        )
    }

    fn option_agg(width: u32, variant: usize) -> crate::AggregateKind {
        crate::AggregateKind::Adt {
            name: "core::option::Option".into(),
            variant,
            active_field: None,
            args: Some(format!("core::option::Option<i{width}>")),
        }
    }

    /// The measured `-O` Shape-B body of `fn c(a: i64, b: i64) -> Option<i64>
    /// { a.checked_add(b) }`, with the cold-hint callee spelled `cold_callee`.
    fn checked_diamond(cold_callee: &str) -> VerifiableFunction {
        let int = Ty::Int { width: 64, signed: true };
        let assign = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        func_with(
            "crate::cadd",
            vec![
                LocalDecl { index: 0, ty: option_of_signed(64), name: None },
                LocalDecl { index: 1, ty: int.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: int.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: int.clone(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
                LocalDecl { index: 5, ty: Ty::Tuple(vec![int, Ty::Bool]), name: None },
                LocalDecl { index: 6, ty: Ty::Unit, name: None },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign(
                            Place::local(5),
                            Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                        ),
                        assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::field(5, 0)))),
                        assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::field(5, 1)))),
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: cold_callee.to_string(),
                        callee_identity: None,
                        callee_key: None,
                        args: vec![],
                        dest: Place::local(6),
                        target: Some(BlockId(3)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Aggregate(option_agg(64, 0), vec![]),
                    )],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Aggregate(option_agg(64, 1), vec![Operand::Copy(Place::local(3))]),
                    )],
                    terminator: Terminator::Goto(BlockId(1)),
                },
            ],
            2,
            option_of_signed(64),
        )
    }

    /// The pinned Option-shape gate itself, positive and fail-closed.
    #[test]
    fn std_option_of_signed_shape_gate_is_exact() {
        for width in [8u32, 16, 32, 64, 128] {
            assert_eq!(ty_is_std_option_of_signed(&option_of_signed(width)), Some(width));
        }
        // Niche layout (disc_index_safe = false) refuses.
        let mut niche = option_of_signed(64);
        let Ty::Adt { disc_index_safe, .. } = &mut niche else { unreachable!() };
        *disc_index_safe = false;
        assert_eq!(ty_is_std_option_of_signed(&niche), None, "niche layout");
        // Unsigned payload refuses.
        let mut unsigned = option_of_signed(64);
        let Ty::Adt { variants, .. } = &mut unsigned else { unreachable!() };
        variants.make_mut()[1].fields[0].1 = Ty::Int { width: 64, signed: false };
        assert_eq!(ty_is_std_option_of_signed(&unsigned), None, "unsigned payload");
        // A same-shape lookalike under a different name refuses.
        let mut lookalike = option_of_signed(64);
        let Ty::Adt { name, .. } = &mut lookalike else { unreachable!() };
        *name = "my_crate::MyOption".into();
        assert_eq!(ty_is_std_option_of_signed(&lookalike), None, "lookalike name");
        // A reference payload (the classic niche carrier) refuses even when a
        // hostile bundle also claims disc_index_safe.
        let mut ref_payload = option_of_signed(64);
        let Ty::Adt { variants, .. } = &mut ref_payload else { unreachable!() };
        variants.make_mut()[1].fields[0].1 =
            Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 64, signed: true }) };
        assert_eq!(ty_is_std_option_of_signed(&ref_payload), None, "reference payload");
        // Scalars and structs refuse.
        assert_eq!(ty_is_std_option_of_signed(&Ty::u64()), None);
        assert_eq!(ty_is_std_option_of_signed(&scalar_cst()), None);
    }

    /// The measured Shape-B checked body certifies all four facets ONLY when
    /// the cold-hint callee carries the compiler intrinsic marker; the bare,
    /// source-spellable spelling stays refused (the callee is not in the unit
    /// and has no authenticated identity).
    #[test]
    fn checked_diamond_certifies_with_marked_cold_path_only() {
        let marked = checked_diamond("@trust-rustc-intrinsic::core::intrinsics::cold_path");
        let facets = inferred(marked);
        assert!(
            facets.all(),
            "the checked diamond with a marked cold_path must certify: {facets:?}"
        );

        let bare = checked_diamond("core::intrinsics::cold_path");
        assert!(
            !inferred(bare).all(),
            "an unmarked cold_path callee has no authenticated identity and must refuse"
        );
    }

    /// Fail-closed mutations of the certifying Shape-B body.
    #[test]
    fn checked_diamond_mutations_fail_closed() {
        let base = || checked_diamond("@trust-rustc-intrinsic::core::intrinsics::cold_path");
        // A niche-encoded return type takes the whole body out.
        let mut niche = base();
        let Ty::Adt { disc_index_safe, .. } = &mut niche.body.return_ty else { unreachable!() };
        *disc_index_safe = false;
        niche.body.locals[0].ty = niche.body.return_ty.clone();
        assert!(!inferred(niche).all(), "niche Option return");

        // A Some aggregate with the wrong operand count refuses.
        let mut bad_some = base();
        bad_some.body.blocks[4].stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Aggregate(option_agg(64, 1), vec![]),
            span: SourceSpan::default(),
        }];
        assert!(!inferred(bad_some).all(), "payload-less Some aggregate");

        // A None aggregate carrying a payload refuses.
        let mut bad_none = base();
        bad_none.body.blocks[3].stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Aggregate(option_agg(64, 0), vec![Operand::Copy(Place::local(3))]),
            span: SourceSpan::default(),
        }];
        assert!(!inferred(bad_none).all(), "None aggregate with a payload");

        // An Option-typed TEMPORARY (not the return slot) is admitted only as
        // the std `Option<iN>` TG14 reads (35b06b86eb: a `checked_*` result is
        // stored in a temporary before its match, `local_ty_in_closed_fragment`
        // via `e6_expr::tree::option_payload`). An unused one changes nothing
        // about the body, so it keeps every facet.
        let mut opt_temp = base();
        opt_temp.body.locals.push(LocalDecl { index: 7, ty: option_of_signed(64), name: None });
        assert!(inferred(opt_temp).all(), "a std Option<i64> temporary is in the fragment");
        // Every other Option temporary refuses: a niche-encoded one, and one
        // whose payload is not a fixed-width integer.
        let mut niche_temp = base();
        let mut niche_ty = option_of_signed(64);
        let Ty::Adt { disc_index_safe, .. } = &mut niche_ty else { unreachable!() };
        *disc_index_safe = false;
        niche_temp.body.locals.push(LocalDecl { index: 7, ty: niche_ty, name: None });
        assert!(!inferred(niche_temp).all(), "niche-encoded Option temporary");
        let mut bool_temp = base();
        let bool_ty = Ty::adt_enum_with_disc_safety(
            "core::option::Option",
            vec![
                crate::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                crate::VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), Ty::Bool)],
                },
            ],
            true,
        );
        bool_temp.body.locals.push(LocalDecl { index: 7, ty: bool_ty, name: None });
        assert!(!inferred(bool_temp).all(), "Option<bool> temporary");

        // A wrong-typed payload operand (the Bool flag where the i64 result
        // belongs) refuses. (The generic-ARGS rendering of the aggregate is
        // deliberately NOT this validator's concern — the destination type
        // gives the typing; the E6 recognizer separately pins the rendering.)
        let mut wrong_payload = base();
        wrong_payload.body.blocks[4].stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Aggregate(option_agg(64, 1), vec![Operand::Copy(Place::local(4))]),
            span: SourceSpan::default(),
        }];
        assert!(!inferred(wrong_payload).all(), "Bool payload in the Some aggregate");
    }

    /// Shape A: a marked checked call certifies; the unmarked spelling and a
    /// malformed reserved-namespace marker fail closed.
    #[test]
    fn a_marked_checked_primitive_method_is_usable_but_lookalikes_are_not() {
        let int = Ty::Int { width: 64, signed: true };
        let call_body = |callee: &str| {
            func_with(
                "crate::cadd",
                vec![
                    LocalDecl { index: 0, ty: option_of_signed(64), name: None },
                    LocalDecl { index: 1, ty: int.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: int.clone(), name: Some("b".into()) },
                ],
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: callee.to_string(),
                            callee_identity: None,
                            callee_key: None,
                            args: vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            is_foreign: false,
                            is_unsafe_sig: false,
                            unwind: UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                2,
                option_of_signed(64),
            )
        };
        let marked = "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_add";
        assert!(
            inferred(call_body(marked)).all(),
            "a TyCtxt-confirmed checked primitive method must be usable as a callee"
        );
        assert!(
            !inferred(call_body("core::num::<impl i64>::checked_add")).all(),
            "an unmarked, source-spellable checked-method lookalike must be refused"
        );
        for malformed in [
            "@trust-rustc-checked-primitive-method::core::num::<impl u64>::checked_add",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_div",
            "@trust-rustc-checked-primitive-method::evil::num::<impl i64>::checked_add",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_add::sfx",
        ] {
            assert!(
                !inferred(call_body(malformed)).all(),
                "malformed/excluded checked marker must fail closed: {malformed}"
            );
        }
        // A WIDTH-mismatched marked call (i32 method into an Option<i64>
        // destination) refuses.
        let mismatch = "@trust-rustc-checked-primitive-method::core::num::<impl i32>::checked_add";
        assert!(!inferred(call_body(mismatch)).all(), "width mismatch must fail closed");
    }
}
