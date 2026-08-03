// trust_vcgen/guards.rs: Guard condition extraction and VC assumption threading
//
// Converts GuardCondition (from MIR control flow) into Formula assumptions.
// When a VC is generated inside a guarded block, the guard conditions on
// the path to that block become assumptions: guard => vc_formula.
//
// Part of #21: Guard condition extraction and clause discovery from MIR.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Known limitation: path_map() in trust-types uses first-predecessor-wins
// for guard accumulation at join points. A block reachable from multiple
// branches may only have one branch's guards, which is not a proof-grade
// encoding of join reachability. Ambiguous joins need disjunctive path
// conditions that cover all incoming guarded paths; until then, callers
// must conservatively use true/unknown instead of assuming one predecessor's
// guard is the complete path condition.
// See trust-types/src/model.rs path_map() for details.

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AggregateKind, BasicBlock, BinOp, BlockId, ConstValue, Formula, GuardCondition, Operand,
    RoundingMode, Rvalue, Sort, Statement, Terminator, Ty, VerifiableFunction,
};
#[cfg(test)]
use trust_types::{AssertMessage, LocalDecl, Place, SourceSpan, VerifiableBody};

use crate::range::{type_max_formula, type_min_formula};
use crate::{
    ArrayReadCtx, ArrayVersionCtx, operand_to_formula, operand_to_formula_with_array_ctx,
    operand_ty, slice_len_formula, u128_to_formula,
};

// ─────────────────────────────────────────────────────────────────────────────
// Crate-origin anchors for the callee-name-keyed fact producers in this file
// (round-5 false-proof close). A GENUINE primitive/std callee renders CRATE-ROOTED
// — `core::slice::<impl [T]>::…`, `std::vec::Vec::<T>::…`, `core::str::<impl str>::…`,
// `core::num::<impl iN>::…`, `<T as core::ops::…>::m` — none of which a user free fn
// (`mycrate::…`) nor a user-trait impl (`<T as mycrate::…>::m`, carrying ` as mycrate`)
// can spell. These MIRROR the generate.rs round-4 helpers
// (`callee_is_std_slice_inherent`, `callee_is_std_vec_inherent`, `is_std_num_intrinsic`)
// and the shared `trust_types::total_call_summaries` doctrine, kept local so this file's
// forgery-rejection is self-contained. Fail-closed on a miss: a missed anchor just
// leaves the honest runtime-checked obligation (a missed proof, never a wrong one).
// `alloc`/`std`/`core` are foreign crates a user cannot shadow (the `--crate-name`
// literal attack is the accepted doctrine boundary, same as the mirrored helpers).

/// MIRROR of `generate::callee_is_std_vec_inherent`: an INHERENT method on the
/// std/alloc `Vec` type (`alloc::vec::Vec::<T>::…`, `std::vec::Vec::<T, A>::…`, the
/// UFCS `<alloc::vec::Vec<T>>::…`). Rejects a user free fn (no `alloc`/`std` root,
/// e.g. `userlib::Vec::<u32>::as_mut_slice`) and a user-trait impl on `Vec` (` as `).
fn callee_is_std_vec_inherent(callee: &str) -> bool {
    if callee.contains(" as ") {
        return false;
    }
    let c = callee.strip_prefix('<').unwrap_or(callee);
    c.starts_with("alloc::vec::Vec") || c.starts_with("std::vec::Vec")
}

/// MIRROR of `generate::callee_is_std_slice_inherent`: an INHERENT primitive-slice
/// method whose def-path ends in one of `suffixes` — `core::slice::<impl [T]>::…`
/// (crate root) or the bare inherent UFCS `<[T]>::…`. Rejects the free fn and the
/// ` as `-qualified user-trait impl on `[T]`.
fn callee_is_std_slice_inherent(callee: &str, suffixes: &[&str]) -> bool {
    if !suffixes.iter().any(|s| callee.ends_with(s)) {
        return false;
    }
    if callee.contains(" as ") {
        return false;
    }
    callee.starts_with("core::slice::")
        || callee.starts_with("std::slice::")
        || callee.starts_with("<[")
}

/// Companion for the INHERENT `str`/`String` methods (`is_empty`, `as_bytes`) whose
/// crate roots the slice/Vec mirrors do not cover. Genuine renderings:
/// `core::str::<impl str>::as_bytes`, `<str>::is_empty`,
/// `alloc::string::String::as_bytes`, `std::string::String::is_empty`. Rejects the
/// free fn (`mycrate::as_bytes`) and the ` as `-qualified user-trait UFCS.
fn callee_is_std_str_inherent(callee: &str, suffixes: &[&str]) -> bool {
    if !suffixes.iter().any(|s| callee.ends_with(s)) {
        return false;
    }
    if callee.contains(" as ") {
        return false;
    }
    callee.starts_with("core::str::")
        || callee.starts_with("std::str::")
        || callee.starts_with("alloc::str::")
        || callee.starts_with("<str")
        || callee.starts_with("alloc::string::String")
        || callee.starts_with("std::string::String")
}

/// MIRROR of `generate::is_std_num_intrinsic`: a `core::num::<impl iN>::…` /
/// `std::num::…` inherent — the un-forgeable `::num::` std segment under a core/std
/// crate root. A user `fn checked_add(..)->Option<..>` renders `mycrate::checked_add`
/// (no `::num::` under a std root) and is DECLINED.
fn is_std_num_intrinsic(callee: &str) -> bool {
    (callee.starts_with("core::") || callee.starts_with("std::")) && callee.contains("::num::")
}

/// A GENUINE `core::ops::`/`std::ops::` operator-trait method — `Index::index`,
/// `IndexMut::index_mut`, `Deref::deref`, `DerefMut::deref_mut`, `Try::branch` — in
/// EITHER the unqualified (`core::ops::index::Index::index`) or the `<T as core::ops::…>::m`
/// qualified form. CRATE-ROOT anchored (round-5 fix): a bare `contains("core::ops::")`
/// was forgeable by a NESTED USER MODULE (`mycrate::core::ops::mymod::index_mut`, or a
/// user-trait impl `<T as mycrate::core::ops::Deref>::deref`) — a strictly lower bar
/// than the accepted `--crate-name`-literal boundary. We strip one leading `<` and
/// require the `core::ops::`/`std::ops::` segment to be at the callee ROOT (unqualified)
/// or immediately after ` as ` (qualified). The nested forgery carries
/// ` as mycrate::core::ops::` — NOT ` as core::ops::` — so it is DECLINED. A user free fn
/// (`mycrate::index`) and `<T as mycrate::ops::Index>::index` are likewise DECLINED. (A
/// genuine std trait impl on a USER type — `<MyWrap as core::ops::deref::Deref>::deref` —
/// is admitted but inert here: its base is not a coll_len-modeled container.)
fn callee_is_std_ops_method(callee: &str) -> bool {
    let c = callee.strip_prefix('<').unwrap_or(callee);
    c.starts_with("core::ops::")
        || c.starts_with("std::ops::")
        || c.contains(" as core::ops::")
        || c.contains(" as std::ops::")
}

/// A GENUINE length-PRESERVING deref/view hop for the base-collection tracer
/// ([`base_collection_step`]): `Deref::deref`/`DerefMut::deref_mut` (the `*v` of a
/// `Vec`/`String`) or the inherent `Vec::as_slice`/`as_mut_slice`. The result and the
/// receiver denote the SAME sequence with IDENTICAL length, so tracing the result's
/// length to the receiver's base is sound. The bare `method_tail` match this backs
/// admitted a user `fn as_slice(v:&Vec<T>)->&[T]` (renders `userlib::…::as_slice` /
/// `mycrate::as_slice`) that returns a DIFFERENT-length view → the tie then discharges
/// an OOB index on the view. Fail-closed on a miss.
fn callee_is_length_preserving_deref(callee: &str) -> bool {
    match crate::generate::method_tail(callee) {
        "deref" | "deref_mut" => callee_is_std_ops_method(callee),
        "as_slice" | "as_mut_slice" => {
            callee_is_std_vec_inherent(callee)
                || callee_is_std_slice_inherent(callee, &["::as_slice", "::as_mut_slice"])
        }
        _ => false,
    }
}

/// Convert a single GuardCondition into an SMT Formula.
///
/// SwitchIntMatch: discr == value
/// SwitchIntOtherwise: discr != v1 AND discr != v2 AND ...
/// AssertHolds: cond == expected
/// AssertFails: cond != expected (negation of the assert condition)
pub(crate) fn guard_to_formula(func: &VerifiableFunction, guard: &GuardCondition) -> Formula {
    match guard {
        GuardCondition::SwitchIntMatch { discr, value } => {
            if matches!(crate::operand_ty_cow(func, discr).as_deref(), Some(Ty::Bool))
                && let Some(formula) = bool_switch_semantics(func, discr, *value != 0)
            {
                return formula;
            }
            let discr_f = operand_to_formula(func, discr);
            if matches!(crate::operand_ty_cow(func, discr).as_deref(), Some(Ty::Bool)) {
                if *value == 0 { Formula::Not(Box::new(discr_f)) } else { discr_f }
            } else {
                let value_f = u128_to_formula(*value);
                Formula::Eq(Box::new(discr_f), Box::new(value_f))
            }
        }
        GuardCondition::SwitchIntOtherwise { discr, excluded_values } => {
            if matches!(crate::operand_ty_cow(func, discr).as_deref(), Some(Ty::Bool)) {
                let excludes_false = excluded_values.contains(&0);
                let excludes_true = excluded_values.iter().any(|value| *value != 0);
                if let Some(truth_value) = match (excludes_false, excludes_true) {
                    (true, false) => Some(true),
                    (false, true) => Some(false),
                    _ => None,
                } && let Some(formula) = bool_switch_semantics(func, discr, truth_value)
                {
                    return formula;
                }
                let discr_f = operand_to_formula(func, discr);
                return match (excludes_false, excludes_true) {
                    (false, false) => Formula::Bool(true),
                    (true, false) => discr_f,
                    (false, true) => Formula::Not(Box::new(discr_f)),
                    (true, true) => Formula::Bool(false),
                };
            }
            let discr_f = operand_to_formula(func, discr);
            if excluded_values.is_empty() {
                return Formula::Bool(true);
            }
            let not_eqs: Vec<Formula> = excluded_values
                .iter()
                .map(|v| {
                    Formula::Not(Box::new(Formula::Eq(
                        Box::new(discr_f.clone()),
                        Box::new(u128_to_formula(*v)),
                    )))
                })
                .collect();
            if not_eqs.len() == 1 {
                // SAFETY: len == 1 guarantees .next() returns Some.
                not_eqs
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
            } else {
                Formula::And(not_eqs)
            }
        }
        GuardCondition::AssertHolds { cond, expected } => {
            let cond_f = operand_to_formula(func, cond);
            if *expected {
                // Assert expects true: cond == true
                cond_f
            } else {
                // Assert expects false: cond == false, i.e., NOT cond
                Formula::Not(Box::new(cond_f))
            }
        }
        GuardCondition::AssertFails { cond, expected, .. } => {
            // The assert failed, so cond != expected
            let cond_f = operand_to_formula(func, cond);
            if *expected {
                // Expected true but got false
                Formula::Not(Box::new(cond_f))
            } else {
                // Expected false but got true
                cond_f
            }
        }
        _ => Formula::Bool(true), /* unknown guard condition: do not hide bad states */
    }
}

fn bool_switch_semantics(
    func: &VerifiableFunction,
    discr: &Operand,
    truth_value: bool,
) -> Option<Formula> {
    if let Some(formula) = bool_condition_definition(func, discr) {
        return Some(if truth_value { formula } else { Formula::Not(Box::new(formula)) });
    }

    // An ascii predicate being TRUE implies `arg <= 127`. SOUNDNESS: only the
    // TRUE branch gets the bound; the FALSE branch yields the no-fact value
    // (`Bool(true)`), never the `>= 128` complement (which could hide a real
    // out-of-range shift). This is additive/monotone — one true conjunct under
    // the guard — exactly like the `is_empty` ⇒ `len == 0` channel below.
    if let Some(bound) = ascii_predicate_bound(func, discr) {
        return Some(if truth_value { bound } else { Formula::Bool(true) });
    }

    let len = is_empty_result_len(func, discr)?;
    Some(if truth_value {
        Formula::Eq(Box::new(len), Box::new(Formula::Int(0)))
    } else {
        Formula::Gt(Box::new(len), Box::new(Formula::Int(0)))
    })
}

fn bool_condition_definition(func: &VerifiableFunction, discr: &Operand) -> Option<Formula> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };

    let mut candidate = None;
    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr: switch_discr, .. } = &block.terminator else {
            continue;
        };
        if !same_plain_local_operand(discr, switch_discr, local) {
            continue;
        }

        let formula = latest_same_block_bool_definition(func, block, local)?;
        match &candidate {
            Some(existing) if existing != &formula => return None,
            Some(_) => {}
            None => candidate = Some(formula),
        }
    }

    candidate
}

fn same_plain_local_operand(lhs: &Operand, rhs: &Operand, local: usize) -> bool {
    matches!(
        (lhs, rhs),
        (
            Operand::Copy(lhs_place) | Operand::Move(lhs_place),
            Operand::Copy(rhs_place) | Operand::Move(rhs_place),
        ) if lhs_place.local == local
            && rhs_place.local == local
            && lhs_place.projections.is_empty()
            && rhs_place.projections.is_empty()
    )
}

fn latest_same_block_bool_definition(
    func: &VerifiableFunction,
    block: &BasicBlock,
    local: usize,
) -> Option<Formula> {
    for (cmp_index, stmt) in block.stmts.iter().enumerate().rev() {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != local || !place.projections.is_empty() {
            continue;
        }
        let Rvalue::BinaryOp(op, lhs, rhs) = rvalue else {
            return None;
        };
        // Logical AND/OR of bools, e.g. the `(L..=U).contains(&x)` rewrite's
        // `dest = (x>=L) & (x<=U)`. Recurse so the guard resolves to the conjoined
        // comparison facts (`And(Ge,Le)`) instead of an opaque bool temp — without
        // this, downstream lanes (BV mul dominating-guard) lose both bounds and a
        // range-validated `x * <const>` false-FAILs. A short-circuit `&&` is NOT
        // this shape (it splits into two switches); only an explicit single-block
        // BitAnd/BitOr of bools reaches here. Semantically faithful: `dest==true`
        // iff `lhs && rhs`.
        if matches!(op, BinOp::BitAnd | BinOp::BitOr)
            && crate::operand_ty_cow(func, lhs).as_deref().is_some_and(|ty| matches!(ty, Ty::Bool))
        {
            let lf = resolve_same_block_bool_operand(func, block, lhs);
            let rf = resolve_same_block_bool_operand(func, block, rhs);
            return Some(match op {
                BinOp::BitAnd => Formula::And(vec![lf, rf]),
                _ => Formula::Or(vec![lf, rf]),
            });
        }
        if !matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) {
            return None;
        }
        // Trust #soundness: a resolved comparison guard `hi <= K` is STALE if `hi`
        // is reassigned between the comparison (which `c` captured) and the guard's
        // consumer — conjoined onto a guarded VC it contradicts the live `hi == big`
        // and vacuously discharges a real obligation (confirmed false-PROVEs of
        // `hi + hi` non-overflow and of a `(L..=U).contains(&x)`-guarded `x * x`).
        // Two channels:
        //   (1) SAME-block: `hi` reassigned LATER in this block, between the
        //       comparison and the SwitchInt that consumes `c`.
        //   (2) CROSS-block: `hi` reassigned in ANOTHER block on the way to the
        //       consumer — e.g. a BitAnd-range leaf resolved here in bb0 while a
        //       later block reassigns `hi` before switching. This is NOT caught by
        //       the path-guard map's inherited-redef kill, because the freshly-added
        //       switch guard is appended AFTER that block's kill.
        // Withhold resolution in either case — block-local reassign OR whole-
        // function instability of a compared operand — so the guard falls back to
        // the opaque bool `c` (an SSA temp, never reassigned). Monotone-sound (drops
        // a hypothesis: PROVE -> FAIL only); a non-reassigned operand still resolves
        // (control tests), so no over-conservatism for the legitimate guarded case.
        if compared_operand_reassigned_after(block, cmp_index, lhs, rhs)
            || [lhs, rhs].iter().any(|op| match op {
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    value_local_is_unstable(func, p.local)
                }
                _ => false,
            })
        {
            return None;
        }

        let lhs_ty = crate::operand_ty_cow(func, lhs);
        if let Some(Ty::Float { width }) = lhs_ty.as_deref() {
            return float_binop_to_formula(func, *op, lhs, rhs, *width);
        }

        let lhs_f = same_block_inlined_operand_formula(func, block, lhs)
            .unwrap_or_else(|| operand_to_formula(func, lhs));
        let rhs_f = same_block_inlined_operand_formula(func, block, rhs)
            .unwrap_or_else(|| operand_to_formula(func, rhs));
        let width = lhs_ty.as_ref().and_then(|ty| ty.int_width());
        let signed = lhs_ty.as_ref().is_some_and(|ty| ty.is_signed());
        // Trust #integrity: fail closed on an unlowerable binop — return no
        // guard (a dropped HYPOTHESIS only makes proofs harder), never panic.
        return crate::chc::try_binop_to_formula(*op, lhs_f, rhs_f, width, signed).ok();
    }

    // No definition in this block. The `(L..=U).contains(&x)` rewrite leaves
    // `dest = BitAnd(..)` in the CALL block and unconditionally `Goto`s to the
    // SwitchInt block that consumes it, so the bool def is one block back. A local
    // with a single static definition dominates all its uses (MIR never reads an
    // uninitialized local), so resolve the UNIQUE defining block when it flows
    // forward unconditionally (`Goto`). Fail-closed on 0 or >1 defining blocks: a
    // multiply-assigned local's reaching def is path-dependent and may not
    // dominate. Bounded recursion: the unique block is necessarily not `block`
    // (which has no def for `local`), and resolves the def directly there.
    let mut defining: Option<&BasicBlock> = None;
    for candidate in &func.body.blocks {
        let defines_here = candidate.stmts.iter().any(|stmt| {
            matches!(stmt, Statement::Assign { place, .. }
                if place.local == local && place.projections.is_empty())
        });
        if defines_here {
            if defining.is_some() {
                return None;
            }
            defining = Some(candidate);
        }
    }
    match defining {
        Some(b) if matches!(b.terminator, Terminator::Goto(_)) => {
            latest_same_block_bool_definition(func, b, local)
        }
        _ => None,
    }
}

/// True if either comparison operand (a plain local) is reassigned by a statement
/// AFTER `cmp_index` in `block` — making a guard resolved from that comparison
/// stale for the block's guarded successors (see the call site).
fn compared_operand_reassigned_after(
    block: &BasicBlock,
    cmp_index: usize,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    let operand_local = |op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    };
    let locals: Vec<usize> =
        [operand_local(lhs), operand_local(rhs)].into_iter().flatten().collect();
    if locals.is_empty() {
        return false;
    }
    block.stmts.iter().skip(cmp_index + 1).any(|stmt| {
        matches!(stmt, Statement::Assign { place, .. }
            if place.projections.is_empty() && locals.contains(&place.local))
    })
}

/// Resolve a bool operand to a formula, recursing through a same-block temp
/// definition (`_t = x >= L`) so a `BitAnd`/`BitOr` of bools unfolds to its leaf
/// comparisons. Falls back to the operand's own formula (an opaque bool var or
/// a bool constant) when there is no same-block comparison/logical definition —
/// fail-soft: a less precise hypothesis only makes proofs harder, never unsound.
fn resolve_same_block_bool_operand(
    func: &VerifiableFunction,
    block: &BasicBlock,
    operand: &Operand,
) -> Formula {
    if let Operand::Copy(place) | Operand::Move(place) = operand
        && place.projections.is_empty()
        && let Some(formula) = latest_same_block_bool_definition(func, block, place.local)
    {
        return formula;
    }
    operand_to_formula(func, operand)
}

/// Resolve a plain-local comparison operand through its latest SAME-BLOCK
/// definition when that definition has a stable, place-keyed formula —
/// currently `PtrMetadata` (slice length).
///
/// Each `s.len()` produces a fresh MIR temp (`_4 = PtrMetadata(s)` in the
/// guard block, `_5 = PtrMetadata(s)` at the bounds assert). The resolved
/// guard `i < _4` would otherwise reference a temp nothing in the VC equates
/// to the assert block's `_5`, leaving the violation satisfiable and the
/// guarded slice index unprovable. Inlining the def maps both sides to the
/// same `{place}__slice_len` symbol. Sound: the substitution is exactly the
/// def equation, and the def dominates the comparison within its block (MIR
/// temps are not reassigned between their definition and use).
fn same_block_inlined_operand_formula(
    func: &VerifiableFunction,
    block: &BasicBlock,
    operand: &Operand,
) -> Option<Formula> {
    let local = match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    for stmt in block.stmts.iter().rev() {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != local || !place.projections.is_empty() {
            continue;
        }
        return match rvalue {
            Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner) => {
                crate::slice_len_formula(func, inner)
            }
            // Trust (Imp3): a `slice.len()` in a guard can lower to `Rvalue::Len(place)`
            // (the array/slice `len` rvalue) rather than `PtrMetadata`. Inline it to the
            // SAME `{place}__slice_len` symbol the index-bounds VC uses, so a guard
            // `if buf.len() < HEADER_SIZE { return }` discharges the later `buf[i]`
            // (i < HEADER_SIZE) reads. `Rvalue::Len(place)` IS the slice length, so this is
            // monotone-sound (adds a true def equation; never removes a fact). Closes
            // astream `frame.rs` Frame::decode's header-index `[slice]` obligations.
            Rvalue::Len(place) => crate::slice_len_formula(func, &Operand::Copy(place.clone())),
            _ => None,
        };
    }
    None
}

fn is_empty_result_len(func: &VerifiableFunction, discr: &Operand) -> Option<Formula> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    let (callee, arg) = call_defining_local(func, local)?;
    // CRATE-ANCHOR (round-5 false-proof close): only the GENUINE std `[T]`/`Vec`/`str`/
    // `String` inherent `is_empty`. A user free fn `fn is_empty(s:&[i32])->bool{false}`
    // renders `mycrate::is_empty` and a user-trait UFCS `<T as mycrate::Trait>::is_empty`
    // carries ` as mycrate`; both are DECLINED — else `!is_empty ⇒ len>0` forges the
    // `v[0]` bound (OOB). The bare `contains("is_empty")` this replaces matched either
    // forgery (any path merely mentioning the substring).
    let is_genuine_is_empty = callee_is_std_slice_inherent(callee, &["::is_empty"])
        || (callee_is_std_vec_inherent(callee)
            && crate::generate::method_tail(callee) == "is_empty")
        || callee_is_std_str_inherent(callee, &["::is_empty"]);
    if !is_genuine_is_empty {
        return None;
    }
    // Slice / array / slice-ref receiver: its type-based length var (existing path).
    if let Some(len) = slice_len_formula(func, arg) {
        return Some(len);
    }
    // Trust: OWNED-CONTAINER receiver (`Vec`/`String`, a `Ty::Adt` — not slice-typed,
    // so `slice_len_formula` is `None`). Its abstract length is `coll_len_var(base)`,
    // the SAME symbolic var the container's `<Vec as Index>::index(v,i)` bound
    // references (see `coll_len_var`'s doc), so `!v.is_empty()` (→ `coll_len_var>0`)
    // discharges a `v[0]` bound — the common `if !v.is_empty(){ v[0] }` idiom.
    owned_container_len_var(func, arg)
}

/// Trust: the abstract length var of an OWNED slice-container (`Vec`/`String`)
/// receiver operand, or `None` if the receiver is not such a container (or its
/// length is not a stable bound here). Used by [`is_empty_result_len`] so a
/// `!v.is_empty()` guard on a `Vec`/`String` yields `coll_len_var(base) > 0` — the
/// SAME var the container's index bound uses.
///
/// SOUNDNESS (0 false-PROVE): gated on (a) a SHARED-reference (`&Vec`/`&String`,
/// NOT `&mut`) receiver whose pointee is an owned-slice-container TYPE
/// ([`crate::generate::is_owned_slice_container_name`]); and (b) the unique-base
/// trace [`base_collection_local_unique`] (fail-closed on ambiguity — a merged
/// receiver declines). The SHARED-ref gate is what makes `coll_len_var(base)` a
/// STABLE bound: a `&Vec` cannot be resized for the guard→index span (no `&mut`
/// alias can coexist under the borrow checker), so the RESIZE hazard
/// (`fn f(v:&mut Vec){ if !v.is_empty(){ v.clear(); v[0] } }` — `clear` empties `v`,
/// making `v[0]` a genuine OOB) is excluded at the TYPE level. A `&mut` receiver
/// (whose length CAN change between guard and index) declines here — the
/// length-mutation analysis does NOT model `clear`, so a type-level gate is the
/// sound choice. An UNguarded `v[0]` still REFUTES: without the guard `coll_len_var`
/// is unconstrained, so `0 < len` stays unprovable.
pub(crate) fn owned_container_len_var(func: &VerifiableFunction, arg: &Operand) -> Option<Formula> {
    let (Operand::Copy(p) | Operand::Move(p)) = arg else {
        return None;
    };
    if !p.projections.is_empty() {
        return None;
    }
    // Trust (struct-field Vec length identity, 2026-07-08): PLACE-keyed resolution.
    // When the receiver temp is a gated shared-field reborrow
    // (`_t = &((*self).history)` under a `&self` root — every gate lives in
    // [`base_collection_place_unique`]), the length identity is the canonical FIELD
    // PLACE, shared with the index-bound recovery
    // (`generate::collection_abstract_len_with_base_opts`) and the `.len()` tie
    // (`slice_last_some_nonempty_definitions`) — so `!self.history.is_empty()`
    // discharges a `self.history[..]` bound across DISTINCT reborrow temps. The key
    // distinguishes FIELDS (`self.a` and `self.b` mint different vars, so a guard
    // on one can never discharge the other) and FAILS CLOSED to the per-temp
    // whole-local behavior below — whose vars never unify across temps — for
    // `&mut self` roots and every other ungated shape.
    let base_place = base_collection_place_unique(func, p.local)?;
    if !base_place.projections.is_empty() {
        return match crate::place_ty_cow(func, &base_place)?.as_ref() {
            // Same container gate as the whole-local arm below (`Vec` via
            // `is_owned_slice_container_name`, or `String` — byte length). The
            // FIELD itself is the OWNED container: there is no ref layer to peel,
            // and the SHARED-ref immutability that makes the length a stable bound
            // lives on the ROOT, already enforced by the place trace.
            Ty::Adt { name, .. }
                if crate::generate::is_owned_slice_container_name(name)
                    || name.rsplit("::").next().map_or(false, |t| t.trim() == "String") =>
            {
                Some(coll_len_var_place(func, &base_place))
            }
            _ => None,
        };
    }
    let base = base_place.local;
    let base_ty = crate::place_ty_cow(func, &trust_types::Place::local(base))?;
    // ONLY a SHARED `&Container` (immutable for the guard→index span) qualifies.
    let Ty::Ref { mutable: false, inner } = base_ty.as_ref() else {
        return None;
    };
    match inner.as_ref() {
        // `Vec<T>` (via `is_owned_slice_container_name`) OR `String`. `String`'s
        // abstract length is its BYTE length — `String::len`/`is_empty`/
        // `as_bytes().len()` are ALL byte length — so it shares `Vec`'s
        // `coll_len_var` semantics exactly. Recognised locally (NOT by widening
        // `is_owned_slice_container_name`, whose many coll_len-machinery callers
        // stay unchanged); this helper is already SHARED-ref-gated, so `&mut String`
        // + `clear()` still refutes.
        Ty::Adt { name, .. }
            if crate::generate::is_owned_slice_container_name(name)
                || name.rsplit("::").next().map_or(false, |t| t.trim() == "String") =>
        {
            Some(coll_len_var(func, base))
        }
        _ => None,
    }
}

/// When `discr` is the boolean result of a `char`/`u8` ascii predicate call
/// (`ch.is_ascii()`, `ch.is_ascii_digit()`, …), the predicate being TRUE implies
/// the tested value is an ASCII codepoint, i.e. `arg <= 127` (= `0x7F`). Returns
/// that bound as `Le(<arg-term>, Int(127))`.
///
/// Mirrors [`is_empty_result_len`] (a guard predicate whose truth implies a
/// numeric fact): we find the `Call` that defines the switched-on boolean, match
/// the callee against the ascii predicate family, and build the implied bound on
/// the call ARGUMENT (the char/byte under test), lowered exactly as the
/// surrounding VC code lowers an operand.
///
/// SOUNDNESS: the caller emits this ONLY on the predicate-TRUE branch. The whole
/// ascii family shares the TRUE-set `[0, 127]`, so `arg <= 127` is an
/// unconditional truth there — a single true conjunct that can only shrink the
/// model (turn a false-FAIL into a PROVE), never manufacture a false-PROVE (same
/// monotone argument as the `is_empty` ⇒ `len == 0` channel). The FALSE branch is
/// deliberately NOT given a bound here: `!is_ascii` means `>= 128`, and emitting
/// that complement could hide a genuinely out-of-range shift, so the caller
/// returns the no-fact value `Bool(true)` on the FALSE branch.
fn ascii_predicate_bound(func: &VerifiableFunction, discr: &Operand) -> Option<Formula> {
    /// `char`/`u8` predicate methods whose TRUE-set is bounded by `[0, 127]`.
    /// Matched as the EXACT method LEAF (`method_tail`) of a crate-anchored std
    /// callee (round-5): membership of the leaf in this set, never a substring of
    /// the whole path (which admitted a same-named user free fn / nested module).
    const ASCII_PREDICATES: &[&str] = &[
        "is_ascii_alphanumeric",
        "is_ascii_alphabetic",
        "is_ascii_hexdigit",
        "is_ascii_punctuation",
        "is_ascii_whitespace",
        "is_ascii_uppercase",
        "is_ascii_lowercase",
        "is_ascii_graphic",
        "is_ascii_control",
        "is_ascii_digit",
        "is_ascii",
    ];

    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    let (callee, arg) = call_defining_local(func, local)?;
    // (a) CRATE-ANCHOR (round-5 false-proof close): the GENUINE std `char`/`u8` ascii
    // predicate renders `core::num::<impl u8>::is_ascii*` or
    // `core::char::methods::<impl char>::is_ascii*`. Require a core/std crate root, the
    // un-forgeable `::num::`/`::char::` std segment, AND the method LEAF (not a substring
    // anywhere in the path) to be an ascii predicate. The bare `lc.contains(name)` this
    // replaces matched a user `fn is_ascii_digit(x:u64)->bool` (renders
    // `mycrate::…::is_ascii_digit`, substring hit) → a false `x <= 127` that discharges a
    // bounds/shift on a WIDE int (OOB/overflow).
    let tail = crate::generate::method_tail(callee);
    let name_is_genuine = (callee.starts_with("core::") || callee.starts_with("std::"))
        && (callee.contains("::num::") || callee.contains("::char::"))
        && ASCII_PREDICATES.contains(&tail);
    if !name_is_genuine {
        return None;
    }
    // The char/byte under test is bounded by 0x7F = 127. A method receiver
    // `b.is_ascii()` lowers to `_r = &b; is_ascii(move _r)`, so the call argument
    // is a REFERENCE to the value, not the value itself — bound the referent
    // (`*_r`, i.e. `b`), which the downstream cast/comparison defs connect to the
    // checked quantity. Bounding the reference local itself would be inert. A
    // by-value argument (no `&` indirection) is bound directly.
    let bounded = deref_through_ref(func, arg).unwrap_or_else(|| arg.clone());
    // (b) TYPE GATE (round-5 false-proof close): apply the `<= 127` bound ONLY when the
    // tested value is a `char`/`u8` — the ONLY types the std ascii predicates receive.
    // The real extractor spells `char` as `Ty::Char`; the older extractor / this file's
    // `ascii_guarded_shift_func` test lower it to `u32`, and `u8` is width 8 — so a
    // genuinely WIDE (u64/u128) arg is NOT a std ascii receiver and is DECLINED. This is
    // defense in depth behind (a): together they close the "forged is_ascii* on a wide
    // int" witness even if a name somehow slipped the anchor.
    let ty_is_char_or_byte = match operand_ty(func, &bounded) {
        Some(Ty::Char) => true,
        Some(Ty::Int { width, .. }) => width == 8 || width == 32,
        _ => false,
    };
    if !ty_is_char_or_byte {
        return None;
    }
    // SOUNDNESS (P0 false proof, 2026-06-17 hunt-8): the `x <= 127` bound describes x AT THE
    // GUARD point. If x's local is REASSIGNED (`x = 200`) or mutably borrowed in the guarded
    // region — `if x.is_ascii() { x = 200; arr[x as usize] }` — the symbol `x` is reused for a
    // different value, and the semantic guard `x <= 127` conjoined with the block-def `x == 200`
    // is a CONTRADICTION that vacuously discharges the `arr[x]` bounds (or `1<<x` shift) obligation
    // (OOB/overflow at runtime; proved in BOTH default and kernel-certified -full). Withhold the
    // bound when the tested value is unstable. Fail-closed: only turns PROVE -> not-proved.
    // NB: do NOT require `p.projections.is_empty()` — a PROJECTED tested value (`t.0.is_ascii()`)
    // is just as stale when its base aggregate is mutated (`t.0 = 200`); checking the BASE local
    // covers both bare and field/element values (hunt-9: the projection-field gap in the hunt-8 fix).
    if let Operand::Copy(p) | Operand::Move(p) = &bounded
        && value_local_is_unstable(func, p.local)
    {
        return None;
    }
    let arg_f = operand_to_formula(func, &bounded);
    Some(Formula::Le(Box::new(arg_f), Box::new(Formula::Int(127))))
}

/// True when `local`'s symbolic value is NOT stable — it is REASSIGNED (a parameter with any store
/// to it, or a non-parameter with 2+ stores; counting WHOLE-local AND projected/field stores
/// `t.0 = ..`, plus Call-terminator dests) or mutably borrowed (`Ref{mutable:true}`/`AddressOf`).
/// A guard-narrowing fact (e.g. `is_ascii` => x<=127, or about a field `t.0<=127`) is STALE in any
/// region where the value was reassigned, so it must not be emitted (hunt-8 + hunt-9 P0 fix). Field
/// stores are counted on the BASE local — conservative (a write to ANY field disqualifies the whole
/// aggregate's facts), which is the sound direction.
pub(crate) fn value_local_is_unstable(func: &VerifiableFunction, local: usize) -> bool {
    let is_param = local >= 1 && local <= func.body.arg_count;
    let mut assigns = 0u32;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if let Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp) = rvalue
                    && bp.local == local
                {
                    return true;
                }
                if place.local == local {
                    assigns += 1;
                }
            }
        }
        // Trust (P0 call-arg &mut staleness): a `&mut local` / `&raw mut local`
        // materialized as a borrow temp and passed as a Call ARGUMENT mutates
        // `local` through the callee (`mem::swap`/`replace`/`take`, a user setter
        // `set(&mut local, ..)`). The `Ref{mutable:true}`/`AddressOf` borrow itself
        // is the `Statement::Assign` scanned above, so this is already caught for
        // the materialized-temp shape; this explicit terminator scan also catches a
        // borrow temp whose value still escapes when a future extractor emits the
        // borrow more directly. Marking the local unstable only WIDENS the staleness
        // kill — it can never create a false proof; a by-VALUE or shared `&` arg
        // does not match (only a temp tracing to a MUTABLE borrow of `local`).
        if let Terminator::Call { args, dest, .. } = &block.terminator {
            if dest.local == local {
                assigns += 1;
            }
            for arg in args {
                if let Operand::Copy(p) | Operand::Move(p) = arg
                    && p.projections.is_empty()
                    && operand_local_is_mut_borrow_of(func, p.local, local)
                {
                    return true;
                }
            }
        }
    }
    if is_param { assigns >= 1 } else { assigns >= 2 }
}

/// True iff a MUTABLE borrow of `local` exists anywhere in `func` — either
/// materialized as a borrow temp (`_t = &mut local` / `&raw mut local`) or such
/// a temp passed as a Call argument. Writes through that pointer are invisible
/// to direct-def scans, so NO derived value bound — traced (`unsigned_upper_bound`)
/// or structural (`clamp_upper_bound`) — may be trusted for a mut-borrowed local.
/// This is the borrow-escape slice of [`value_local_is_unstable`]; plain
/// reassignment (multiple direct defs) deliberately does NOT match, because a
/// whole-body def scan can still reason soundly about every direct def.
pub(crate) fn value_local_is_mut_borrowed(func: &VerifiableFunction, local: usize) -> bool {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt
                && let Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp) = rvalue
                && bp.local == local
            {
                return true;
            }
        }
        if let Terminator::Call { args, .. } = &block.terminator {
            for arg in args {
                if let Operand::Copy(p) | Operand::Move(p) = arg
                    && p.projections.is_empty()
                    && operand_local_is_mut_borrow_of(func, p.local, local)
                {
                    return true;
                }
            }
        }
    }
    false
}

/// True iff `borrow_temp`'s defining rvalue is a MUTABLE borrow (`&mut target` /
/// `&raw mut target`) of `target`. Used to recognize `&mut target` passed as a
/// call argument (materialized into `borrow_temp` by MIR). A SHARED borrow
/// (`Ref{mutable:false}`, i.e. `&target`) and a by-value copy are deliberately NOT
/// matched: they cannot drive a mutation of `target`.
fn operand_local_is_mut_borrow_of(
    func: &VerifiableFunction,
    borrow_temp: usize,
    target: usize,
) -> bool {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == borrow_temp
                && place.projections.is_empty()
            {
                return matches!(
                    rvalue,
                    Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(true, bp)
                        if bp.local == target
                );
            }
        }
    }
    false
}

/// If `operand` is `Copy/Move(_r)` where `_r` is defined by a borrow
/// `_r = &referent` (the auto-ref a method call inserts for its `&self`
/// receiver), return `Copy(referent)` so a fact meant for the referent value is
/// stated about the value, not the (inert) reference local. Returns `None` for a
/// by-value operand, leaving it unchanged.
fn deref_through_ref(func: &VerifiableFunction, operand: &Operand) -> Option<Operand> {
    let local = match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
        _ => return None,
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                place: dest, rvalue: Rvalue::Ref { place: referent, .. }, ..
            } = stmt
            else {
                continue;
            };
            if dest.local == local && dest.projections.is_empty() {
                return Some(Operand::Copy(referent.clone()));
            }
        }
    }
    None
}

fn call_defining_local(func: &VerifiableFunction, local: usize) -> Option<(&str, &Operand)> {
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if dest.local == local && dest.projections.is_empty() {
            return args.first().map(|arg| (callee.as_str(), arg));
        }
    }
    None
}

/// Trust: if `local` is the result of an `as_bytes()` call (`b = recv.as_bytes()`),
/// return the receiver operand `recv`. `as_bytes` is BYTE-LENGTH-PRESERVING
/// (`str::as_bytes().len() == str.len()`; `str` is modeled as `[u8]`), so
/// [`crate::slice_len_formula`] resolves `b`'s length to `recv`'s OWN length var —
/// unifying an `!recv.is_empty()` guard (length on `recv`) with a
/// `recv.as_bytes()[i]` index bound (length on `b`), letting guarded string
/// indexing PROVE (the slice-only recogniser already handles `!s.is_empty()` +
/// `s[i]` on a `&[u8]`; this closes the `str`→`&[u8]` conversion).
///
/// SOUNDNESS (0 false-PROVE): the length transfers ONLY when `recv` itself resolves
/// to a slice length (`slice_len_formula(recv)` is `Some`) — true for the `str`/
/// `&[u8]` receiver of the real `str::as_bytes`, and FAIL-CLOSED (`None`) for any
/// other receiver (e.g. a user `Foo::as_bytes` whose `&Foo` has no slice length),
/// so a non-length-preserving impostor cannot borrow a bogus length. Uses the
/// unique-def `call_defining_local` (fail-closed on ambiguity). An UNguarded
/// `recv.as_bytes()[i]` still REFUTES: `recv`'s length var is unconstrained without
/// the guard, so `0 < len` stays unprovable.
pub(crate) fn as_bytes_length_receiver(
    func: &VerifiableFunction,
    local: usize,
) -> Option<&Operand> {
    let (callee, arg) = call_defining_local(func, local)?;
    // CRATE-ANCHOR (round-5 false-proof close): only the GENUINE byte-length-preserving
    // `str::as_bytes` (`core::str::<impl str>::as_bytes`, `<str>::as_bytes`) /
    // `String::as_bytes` (`alloc::string::String::as_bytes`). A user
    // `fn as_bytes(&Foo)->&[u8]` renders `mycrate::…::as_bytes` (or a ` as mycrate`
    // UFCS) and is DECLINED. The bare `method_tail == "as_bytes"` this replaces admitted
    // a length-CHANGING impostor: when its receiver is itself slice-typed (so
    // `slice_len_formula(recv)` is `Some`), a shorter/longer forged result borrows the
    // receiver's length var → discharges an OOB index on the fresh `as_bytes` result.
    if callee_is_std_str_inherent(callee, &["::as_bytes"]) {
        return Some(arg);
    }
    None
}

/// Convert a sequence of guard conditions into a single conjunction Formula.
///
/// An empty guard list yields `true` (no assumptions).
#[cfg(test)]
pub(crate) fn guards_to_assumption(
    func: &VerifiableFunction,
    guards: &[GuardCondition],
) -> Formula {
    if guards.is_empty() {
        return Formula::Bool(true);
    }
    let formulas: Vec<Formula> = guards.iter().map(|g| guard_to_formula(func, g)).collect();
    if formulas.len() == 1 {
        // SAFETY: len == 1 guarantees .next() returns Some.
        formulas.into_iter().next().unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
    } else {
        Formula::And(formulas)
    }
}

/// Wrap a VC formula with path guard assumptions.
///
/// Returns: guards => vc_formula
/// If guards is empty (or trivially true), returns the vc_formula unchanged.
#[must_use]
#[cfg(test)]
pub(crate) fn guarded_formula(
    func: &VerifiableFunction,
    guards: &[GuardCondition],
    vc_formula: Formula,
) -> Formula {
    if guards.is_empty() {
        return vc_formula;
    }
    let assumption = guards_to_assumption(func, guards);
    // VC convention: formula is SAT iff violation exists.
    // With guards: we only want violations reachable under the guard.
    // So: guard_assumption AND vc_violation_formula
    Formula::And(vec![assumption, vc_formula])
}

/// The single, well-typed checked integer operation whose overflow flag an
/// `Assert(expected = false)` consumes.
///
/// This is a proof-authority boundary, not just a MIR convenience recognizer.
/// Synthetic/imported TrustIR can violate rustc's ordinary SSA and typing
/// invariants, so fail closed unless all of them are explicit here:
///
/// - the condition is exactly the asserted tuple's `.1` field;
/// - that tuple has one and only one write in the block, a whole-local
///   `CheckedBinaryOp(Add|Sub|Mul)`;
/// - both operands and the tuple result have one identical integer type;
/// - the checked operation does not read its own pre-write tuple; and
/// - no value-affecting statement follows the snapshot before the Assert.
///
/// The last two conditions prevent an unversioned formula such as
/// `checked.0 == a + b` from silently referring to a different value at the
/// block exit than the one the checked operation actually read.
fn checked_operand_matches_type(
    func: &VerifiableFunction,
    operand: &Operand,
    expected: &Ty,
) -> bool {
    match operand {
        // Signed MIR constants deliberately lose their source width in the
        // portable VF (`ConstValue::Int`). Recover it only from the checked
        // tuple's authenticated value type, and only when the value is exactly
        // representable there. This admits genuine `i32 + 1` without allowing
        // a forged `i8 + 128` to mint impossible success-edge facts.
        Operand::Constant(ConstValue::Int(value)) => match expected {
            Ty::Int { width: 8, signed: true } => i8::try_from(*value).is_ok(),
            Ty::Int { width: 16, signed: true } => i16::try_from(*value).is_ok(),
            Ty::Int { width: 32, signed: true } => i32::try_from(*value).is_ok(),
            Ty::Int { width: 64, signed: true } | Ty::PtrSizedInt { signed: true } => {
                i64::try_from(*value).is_ok()
            }
            Ty::Int { width: 128, signed: true } => true,
            _ => false,
        },
        // Unsigned constants retain their compiler-extracted width. Require it
        // to agree exactly with the checked tuple carrier (including the
        // faithful pointer-sized spelling) and independently validate the
        // serialized value's range.
        Operand::Constant(ConstValue::Uint(value, source_width)) => {
            let expected_width = match expected {
                Ty::Int { width, signed: false } => *width,
                Ty::PtrSizedInt { signed: false } => 64,
                _ => return false,
            };
            if *source_width != expected_width {
                return false;
            }
            match expected_width {
                8 => u8::try_from(*value).is_ok(),
                16 => u16::try_from(*value).is_ok(),
                32 => u32::try_from(*value).is_ok(),
                64 => u64::try_from(*value).is_ok(),
                128 => true,
                _ => false,
            }
        }
        _ => crate::operand_ty_cow(func, operand).as_deref() == Some(expected),
    }
}

fn exact_asserted_checked_binary_op<'a>(
    func: &VerifiableFunction,
    block: &'a BasicBlock,
) -> Option<(usize, BinOp, &'a Operand, &'a Operand, Ty)> {
    let Terminator::Assert { cond, expected: false, .. } = &block.terminator else {
        return None;
    };
    let cond_place = match cond {
        Operand::Copy(place) | Operand::Move(place)
            if matches!(place.projections.as_slice(), [trust_types::Projection::Field(1)]) =>
        {
            place
        }
        _ => return None,
    };
    let tuple_local = cond_place.local;

    let mut checked = None;
    for (idx, stmt) in block.stmts.iter().enumerate() {
        match stmt {
            Statement::Assign { place, rvalue, .. } if place.local == tuple_local => {
                // A projection write or second whole-local write makes the
                // asserted tuple's reaching definition ambiguous.
                if !place.projections.is_empty() || checked.is_some() {
                    return None;
                }
                let Rvalue::CheckedBinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), lhs, rhs) =
                    rvalue
                else {
                    return None;
                };
                checked = Some((idx, *op, lhs, rhs));
            }
            Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                if place.local == tuple_local =>
            {
                return None;
            }
            _ => {}
        }
    }
    let (checked_idx, op, lhs, rhs) = checked?;

    if block.stmts.iter().skip(checked_idx + 1).any(|stmt| {
        !matches!(
            stmt,
            Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop
        )
    }) {
        return None;
    }
    if [lhs, rhs].iter().any(|operand| {
        matches!(operand, Operand::Copy(place) | Operand::Move(place) if place.local == tuple_local)
    }) {
        return None;
    }

    let Ty::Tuple(fields) = &func.body.locals.get(tuple_local)?.ty else {
        return None;
    };
    let [value_ty, Ty::Bool] = fields.as_slice() else {
        return None;
    };
    if !matches!(value_ty, Ty::Int { .. } | Ty::PtrSizedInt { .. })
        || !checked_operand_matches_type(func, lhs, value_ty)
        || !checked_operand_matches_type(func, rhs, value_ty)
    {
        return None;
    }

    Some((tuple_local, op, lhs, rhs, value_ty.clone()))
}

/// Extract semantic assert-passed guards from a block.
///
/// When a block contains a CheckedBinaryOp assignment followed by an Assert
/// terminator on the overflow flag, the assert passing implies:
/// 1. A range constraint: the result is in [min, max] for the type
/// 2. A result definition: `_N.0 = lhs op rhs` (the `.0` field equals the
///    mathematical result), which connects the tuple result to its operands
///
/// Returns a (possibly empty) Vec of formulas. The range constraint ensures
/// the solver knows the assert-passed semantics (e.g., hi >= lo for unsigned
/// CheckedSub), while the result definition enables dataflow tracking through
/// subsequent blocks.
///
/// This is different from the syntactic guard (`NOT _flag`) that path_map
/// already propagates: the syntactic guard refers to an unconstrained boolean
/// variable, while the semantic guard encodes the actual arithmetic meaning.
pub(crate) fn extract_assert_passed_semantics(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<Formula> {
    let Some((tuple_local, op, lhs, rhs, value_ty)) = exact_asserted_checked_binary_op(func, block)
    else {
        return Vec::new();
    };

    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let Some(width) = value_ty.int_width() else {
        return Vec::new();
    };
    let signed = value_ty.is_signed();

    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        _ => return Vec::new(),
    };

    // No-overflow means result is in [min, max] for the type.
    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);

    let in_range = Formula::And(vec![
        Formula::Le(Box::new(min_f), Box::new(result.clone())),
        Formula::Le(Box::new(result.clone()), Box::new(max_f)),
    ]);

    // Also define _N.0 = result_formula. This connects the
    // tuple's result field to the actual arithmetic expression, enabling
    // dataflow tracking when _N.0 is read in subsequent blocks.
    let tuple_name = func
        .body
        .locals
        .get(tuple_local)
        .and_then(|d| d.name.as_deref())
        .map_or_else(|| format!("_{tuple_local}"), |n| n.to_string());
    let result_field_name = format!("{tuple_name}.0");
    let result_def =
        Formula::Eq(Box::new(Formula::Var(result_field_name, Sort::Int)), Box::new(result));

    // Include input range constraints for the operands of the
    // CheckedBinaryOp. Without these, variables like `hi` that appear in the
    // semantic guard but not in the downstream VC formula would be unconstrained,
    // allowing the solver to pick out-of-range values (e.g., hi > u64::MAX)
    // that satisfy the guard while still causing a false overflow violation.
    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);

    let mut facts = vec![in_range, result_def, lhs_range, rhs_range];
    // Tighten a WIDENED operand (`_4 = a as u16`) to its SOURCE type's range
    // (`0 <= _4 <= 255` for a u8 source), not the wider ADD-operand range
    // (`0 <= _4 <= 65535`). Without this the solver picks an out-of-source-range
    // value for the widened operand and fabricates a false overflow — the
    // hardened panic_boundary OVER-REFUTATION of a provably-safe
    // `a as u16 + b as u16` (the operand range above, keyed on the wider add
    // type, admits `_4 = _5 = 65535`). Sound: the source-width range is an
    // unconditional truth about a value-preserving widening cast (monotone — a
    // true conjunct can only discharge a false-FAIL, never manufacture a
    // false-PROVE). A non-widened operand (e.g. plain `u32 + u32`) yields None,
    // so a genuinely-overflowing add still refutes.
    if let Some(range) = widening_operand_source_range(func, lhs) {
        facts.push(range);
    }
    if let Some(range) = widening_operand_source_range(func, rhs) {
        facts.push(range);
    }
    facts
}

/// If `operand` is `Copy/Move(_n)` where `_n` is defined by a value-preserving
/// widening integer cast `_n = src as wider`, return the SOURCE type's range
/// constraint on `_n` (e.g. `0 <= _n <= 255` for a `u8` source widened to `u16`).
///
/// This bounds a widened arithmetic operand by the type it actually came from,
/// not by the wider operation type — which the integer model otherwise treats as
/// an unconstrained value of the wider type. Sound by construction: a
/// value-preserving widening cast result unconditionally lies within the source
/// type's range (see [`widening_cast_result_range`]), so the returned fact is a
/// true conjunct.
fn widening_operand_source_range(func: &VerifiableFunction, operand: &Operand) -> Option<Formula> {
    let place = match operand {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    if !place.projections.is_empty() {
        return None;
    }
    let local = place.local;
    // The whole-function cast scan below is only an exact reaching definition
    // when this operand local is SSA-stable. A reassigned/mutably-borrowed local
    // can carry a later value outside the cast's source range; injecting the
    // stale narrow bound would contradict that value and vacuously prove a real
    // overflow. Withhold the optional precision fact on any instability.
    if value_local_is_unstable(func, local) {
        return None;
    }
    let dest_name = func
        .body
        .locals
        .get(local)
        .and_then(|d| d.name.as_deref())
        .map_or_else(|| format!("_{local}"), |n| n.to_string());
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue: Rvalue::Cast(src, to_ty), .. } = stmt
            else {
                continue;
            };
            if dest.local != local || !dest.projections.is_empty() {
                continue;
            }
            // Value-preserving widening keeps its tighter source-width range; a
            // narrowing / reinterpreting cast (defined, no CastOverflow VC) is
            // type-tracked by its target-type range so a widened use of the wrapped
            // value (`(x as u8) as u32 + 1`) proves rather than reading as a free int.
            return widening_cast_result_range(func, src, to_ty, &dest_name)
                .or_else(|| narrowing_cast_result_range(func, src, to_ty, &dest_name));
        }
    }
    None
}

/// Define the checked-arithmetic OVERFLOW FLAG `_N.1` in terms of the operands,
/// for consumers that model both the success and failure edges. Returns
/// `[_N.1 <=> (result < min ∨ result > max), lhs_range, rhs_range]`, or empty
/// when the block is not a `CheckedBinaryOp` + overflow `Assert`.
///
/// Without this the assert-failure condition `_N.1` is a FREE boolean, so every
/// arithmetic panic boundary fails spuriously even when a dominating guard makes
/// overflow impossible. Unlike `extract_assert_passed_semantics` this does NOT
/// emit the `in_range` fact (which assumes no overflow and would vacuously
/// discharge the failure — a false PROVE). It emits only the EXACT flag
/// biconditional (`_N.1` is true iff the unbounded result leaves the type
/// range), a true fact at the assert: under a guard that forces the result in
/// range the failure is UNSAT (proves); with no guard the overflow stays
/// reachable (fails closed).
///
/// Deliberately do NOT define `_N.0` here. MIR's value field wraps when overflow
/// is true, so `_N.0 ==` the unbounded mathematical result holds only on the
/// Assert success edge. [`extract_assert_passed_semantics`] owns that
/// success-only equation and the path-definition fixpoint transports it only
/// along the normal edge.
pub(crate) fn extract_overflow_flag_semantics(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<Formula> {
    let Some((tuple_local, op, lhs, rhs, value_ty)) = exact_asserted_checked_binary_op(func, block)
    else {
        return Vec::new();
    };

    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let Some(width) = value_ty.int_width() else {
        return Vec::new();
    };
    let signed = value_ty.is_signed();

    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        _ => return Vec::new(),
    };

    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);

    let tuple_name = func
        .body
        .locals
        .get(tuple_local)
        .and_then(|d| d.name.as_deref())
        .map_or_else(|| format!("_{tuple_local}"), |n| n.to_string());

    // `_N.1` is true exactly when the unbounded result leaves the type range.
    let overflowed = Formula::Or(vec![
        Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
        Formula::Gt(Box::new(result), Box::new(max_f)),
    ]);
    let flag_def = Formula::Eq(
        Box::new(Formula::Var(format!("{tuple_name}.1"), Sort::Bool)),
        Box::new(overflowed),
    );
    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);

    vec![flag_def, lhs_range, rhs_range]
}

/// Extract dataflow definitions from a block's assignment statements.
///
/// Each `Assign { place, rvalue }` is converted to `Eq(Var(place_name), rvalue_formula)`.
/// This allows the solver to know that intermediate locals (e.g., `_5 = _4 / 2`)
/// are constrained by their definitions, not free variables.
///
/// CheckedBinaryOp assignments are skipped (handled by `extract_assert_passed_semantics`).
/// Whole-function facts from `let v = a.checked_add(b)?` (and `checked_sub`): on
/// the success path the unwrapped value equals `a + b` (resp. `a - b`), because
/// `checked_*` returns `Some(a OP b)` exactly when it does not overflow. The
/// LIBRARY `checked_add` lowers to a CALL (not a `CheckedBinaryOp` intrinsic),
/// followed by `Try::branch` and a `ControlFlow::Continue(.0)` / `Some(.0)`
/// payload read — which the per-block `CheckedBinaryOp` semantics miss. This
/// recovers `payload == a OP b` so a guard `payload <= self.len` connects to an
/// obligation over `a + b` (aterm's `slice` offset case).
///
/// SOUND on two counts: the equality is emitted ONLY for the value-bearing
/// variant (`Some` / `Continue`, by matching the downcast's variant index), and
/// it is true wherever the payload local is defined — so conjoining it can only
/// help prove a genuinely-unsatisfiable violation, never erase a real one.
pub(crate) fn build_checked_arith_facts(func: &VerifiableFunction) -> Vec<Formula> {
    fn operand_local(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(p) | Operand::Move(p) => Some(p.local),
            _ => None,
        }
    }
    // Soundness gate (issue 4): every fact produced here is conjoined onto EVERY
    // sep VC in the function (see generate.rs), so each must be a function-wide
    // invariant — not a value a later reassignment can falsify. Count how many
    // times each local is assigned (unprojected statement-assigns + call dests);
    // a fact `payload == a OP b` is emitted only when the payload and each
    // operand base-local is assigned at most once (SSA-stable). A multiply-
    // assigned local could hold a different value at the VC site than at the
    // checked-arith site, which would make the global conjunction unsound.
    let mut assign_count: FxHashMap<usize, usize> = FxHashMap::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place.projections.is_empty()
            {
                *assign_count.entry(place.local).or_insert(0) += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.projections.is_empty()
        {
            *assign_count.entry(dest.local).or_insert(0) += 1;
        }
    }
    let stable_local = |l: usize| assign_count.get(&l).copied().unwrap_or(0) <= 1;
    let stable_operand = |op: &Operand| match op {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) => stable_local(p.local),
        // Unknown operand shape: fail closed — don't treat it as stable.
        _ => false,
    };
    // local -> (value `a OP b`, variant index that CARRIES the value).
    // `checked_*` yields `Option` (value in `Some`, variant 1); `Try::branch`
    // re-wraps it as `ControlFlow` (value in `Continue`, variant 0).
    let mut value_of: FxHashMap<usize, (Formula, usize)> = FxHashMap::default();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        // CRATE-ANCHOR (round-5 false-proof close): only the GENUINE
        // `core::num::<impl iN>::checked_add`/`checked_sub` inherent mints the
        // `Some-payload == a OP b` value. A user `fn checked_add(a:u32,b:u32)->Option<u32>{Some(BIG)}`
        // renders `mycrate::checked_add` (no `::num::` under a core/std root) and is
        // DECLINED — the bare `lc.contains("checked_add")` this replaces would conjoin a
        // FALSE `payload == a+b` globally (its `Some(BIG) != a+b`) → discharges a bounds
        // check. Method LEAF exact-match (not substring).
        if args.len() >= 2 && is_std_num_intrinsic(callee) {
            let val = match crate::generate::method_tail(callee) {
                "checked_add" => Some(Formula::Add(
                    Box::new(operand_to_formula(func, &args[0])),
                    Box::new(operand_to_formula(func, &args[1])),
                )),
                "checked_sub" => Some(Formula::Sub(
                    Box::new(operand_to_formula(func, &args[0])),
                    Box::new(operand_to_formula(func, &args[1])),
                )),
                _ => None,
            };
            if let Some(val) = val {
                // Only record the value when both operands are SSA-stable, so the
                // resulting fact stays a function-wide invariant (see gate above).
                if stable_operand(&args[0]) && stable_operand(&args[1]) {
                    value_of.insert(dest.local, (val, 1)); // Option::Some
                }
                continue;
            }
        }
        // `Try::branch(opt)` re-wraps the value into `ControlFlow::Continue`.
        // CRATE-ANCHOR (round-5): only the GENUINE `Try::branch`
        // (`core::ops::try_trait::Try::branch`, `<Option<T> as core::ops::try_trait::Try>::branch`,
        // the `std::ops::Try::branch` shorthand). The bare `lc.contains("branch")` this
        // replaces admitted a user `fn branch(o:Option<u32>)->ControlFlow<_,u32>{Continue(BIG)}`
        // (renders `mycrate::branch`) that re-wraps a DIFFERENT payload than the source's
        // `a OP b` → a FALSE `payload == a OP b` fact. The value it hops (`val`) is only
        // present for a source already anchored to a genuine `checked_*` above, but the
        // re-wrap must itself be the genuine total-hop to keep the payload identity true.
        if callee_is_std_ops_method(callee)
            && crate::generate::method_tail(callee) == "branch"
            && let Some(src) = args.first().and_then(operand_local)
            && let Some((val, _)) = value_of.get(&src).cloned()
        {
            value_of.insert(dest.local, (val, 0)); // ControlFlow::Continue
        }
    }

    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
                continue;
            };
            if let [trust_types::Projection::Downcast(v), trust_types::Projection::Field(0)] =
                src.projections.as_slice()
                && let Some((val, expect_v)) = value_of.get(&src.local)
                && v == expect_v
                // The payload local must itself be SSA-stable, else a later
                // reassignment of it would falsify the globally-conjoined fact.
                && stable_local(place.local)
            {
                let payload = operand_to_formula(func, &Operand::Copy(place.clone()));
                facts.push(Formula::Eq(Box::new(payload), Box::new(val.clone())));
            }
        }
    }
    facts
}

/// Emit `{dest}__slice_len == <referent slice length>` when `referent` is a slice
/// place borrowed (`&`) or raw-pointed (`&raw const/mut`) by `dest`. A pointer
/// preserves the slice's LENGTH metadata — a borrow cannot change a slice's
/// length, not even `&mut [T]` — so the equality is SOUND. It lets a slice length
/// read through the pointer (`PtrMetadata`) — notably the `dst.len()` of a guarded
/// `&mut [T]` index `if i < dst.len() { dst[i] = .. }`, which lowers via a
/// `FakeForPtrMetadata` raw pointer — tie back to the underlying slice's length
/// var. Borrowing `*ref` (deref of a slice reference) resolves through the trailing
/// `Deref` to the underlying reference's STABLE length var (a parameter's), so the
/// guard's and the index's reads share one var. Without this the read is a fresh
/// unconstrained var and a SAFE guarded `&mut` index false-refutes.
fn push_borrow_slice_len(
    func: &VerifiableFunction,
    dest_name: &str,
    referent: &trust_types::Place,
    defs: &mut Vec<Formula>,
    seen_dests: &mut FxHashSet<String>,
) {
    let target = match referent.projections.last() {
        Some(trust_types::Projection::Deref) => {
            let mut base = referent.clone();
            base.projections.pop();
            base
        }
        _ => referent.clone(),
    };
    if let Some(referent_len) = crate::slice_len_formula(func, &Operand::Copy(target)) {
        let name = format!("{dest_name}__slice_len");
        if seen_dests.insert(name.clone()) {
            defs.push(Formula::Eq(
                Box::new(Formula::var_owned(name, Sort::Int)),
                Box::new(referent_len),
            ));
        }
    }
}

pub(crate) fn extract_block_definitions(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<Formula> {
    extract_block_definitions_until(func, block, block.stmts.len())
}

pub(crate) fn extract_block_definitions_until(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end_stmt_exclusive: usize,
) -> Vec<Formula> {
    extract_block_definitions_until_impl(func, block, end_stmt_exclusive, false)
}

/// Variant for the ESTABLISH-POINT-VERSIONED consumer
/// (`v2_formula_with_block_defs_at_point`), which stamps every def's reads at its
/// own statement (`version_block_def_at_establish`) before conjoining. On that
/// path, PURE PLACE-READ defs (`_t == place` from `_t = Copy/Move(place)`) are
/// KEPT even when a later statement clobbers the read place: the establish-point
/// token pins the def to the PRE-write value, and a post-write read of the same
/// place mints a DIFFERENT token (the same name-disjointness that let the
/// deref-store-havoc kill be deleted on this path, proven 0-residual by
/// `block_def_establish_subsumes_kill` + the 65-mutant falsification gate).
/// Without this, a closure's `&mut`-upvar guard (`_2 = (*(_1.0)); if _2 < K {
/// (*(_1.0)) += 1 }`) loses its read-def to the write-back and `_2`/`_4` stay
/// free — the last unified over-refutation instance. COMPUTED defs
/// (`c == (m < 1000)`) keep the staleness kill unchanged, belt-and-suspenders.
/// UNversioned consumers (hardened profile, arm recovery, semantic-guard
/// threading) MUST keep using [`extract_block_definitions_until`] — without the
/// establish stamp, a kept read-def against a later-clobbered place is exactly
/// the `c = m < 1000; m = BIG` false-PROVE the kill exists to stop.
pub(crate) fn extract_block_definitions_until_versioned(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end_stmt_exclusive: usize,
) -> Vec<Formula> {
    extract_block_definitions_until_impl(func, block, end_stmt_exclusive, true)
}

fn extract_block_definitions_until_impl(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end_stmt_exclusive: usize,
    keep_versionable_read_defs: bool,
) -> Vec<Formula> {
    let mut defs = Vec::new();
    let mut seen_dests = FxHashSet::default();

    // Trust: McCarthy array-theory version context. Computed once per call from
    // `func` alone (a deterministic forward prepass over the no-join CFG), so the
    // store side and the read side share one oracle. For non-array / join-bearing
    // functions this is empty and every read/store stays on the scalar path.
    let array_ctx: ArrayVersionCtx = crate::v2_array_version_prepass(func);

    for (stmt_idx, stmt) in block.stmts.iter().take(end_stmt_exclusive).enumerate().rev() {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };

        // Read context for element reads in THIS statement: the live array
        // version just before `stmt_idx` (the single store-count oracle).
        let read_ctx = ArrayReadCtx::new(&array_ctx, block.id, stmt_idx);

        // ---- Array-theory STORE: `a[Index(idx)] = w` into an eligible local.
        // Emit `v{n+1} == Store(v{n}, idx, w)` and SKIP the scalar `seen_dests`
        // handling entirely (each variable-index store must survive — they share
        // the `a[_i]` name and would otherwise dedup to one). NEVER emit the
        // scalar `Eq(Var(a[_i]), w)`.
        if crate::is_array_theory_element_store(func, place.local, stmt) {
            if let Some(model) = crate::array_theory_local(func, place.local) {
                let elem = model.elem_sort;
                let n = array_ctx.live_version(func, place.local, block.id, stmt_idx);
                let idx_proj = &place.projections[0];
                let value = match rvalue {
                    Rvalue::Use(operand) => {
                        operand_to_formula_with_array_ctx(func, operand, Some(&read_ctx))
                    }
                    // A non-`Use` store value (rare) is modeled by its scalar
                    // formula; fall back to the dest place name when unsupported.
                    _ => operand_to_formula(func, &Operand::Copy(place.clone())),
                };
                defs.push(Formula::Eq(
                    Box::new(crate::array_term_var(place.local, n + 1, elem.clone())),
                    Box::new(Formula::Store(
                        Box::new(crate::array_term_var(place.local, n, elem)),
                        Box::new(crate::array_index_formula(func, idx_proj)),
                        Box::new(value),
                    )),
                ));
                // Skip the scalar `seen_dests` handling ONLY when the array store
                // was actually emitted. If the array is NOT eligible
                // (`array_theory_local` is None) the store must fall through to
                // the scalar `[c;min=len]` path -- otherwise the fact vanishes and
                // a same-slot read goes stale (regresses the #54 const-index case,
                // which is an Index store to a NON-eligible array).
                continue;
            }
        }

        let dest_name = crate::place_to_var_name(func, place);
        if !seen_dests.insert(dest_name.clone()) {
            continue;
        }

        // Skip CheckedBinaryOp — its result definition is handled by semantic guards.
        if matches!(rvalue, Rvalue::CheckedBinaryOp(..)) {
            continue;
        }

        let dest_sort = crate::place_sort(func, place).unwrap_or(Sort::Int);
        let rvalue_formula = match rvalue {
            Rvalue::Use(operand) => {
                // SOUNDNESS (P0 false proof, 2026-06-17 hunt-15): a read of an ENUM
                // PAYLOAD projection `(o as Variant).field` of a mutably-borrowed local
                // `o` must NOT be tied to the shared payload symbol. `o.as_mut()` /
                // `o.insert(b)` / `o.get_or_insert_with(|| b)` can REASSIGN the payload
                // BETWEEN two such reads, e.g.
                //   if let Some(v) = o { if v < 5 { o.as_mut().map(|r| *r = b);
                //                                    match o { Some(i) => arr[i], .. } } }
                // Both `v` and the later `i` lower to `copy ((o as Some).0)`, so they share
                // one var name; the guard bound `v < 5` then transfers to `i` and vacuously
                // discharges `arr[i]` even though `i` became the unbounded `b` (OOB at
                // runtime). hunt-7 gated only the CONSTRUCTION-time field fact
                // (`o@k.field == op`) and the demux re-injection; this is the READ-ALIASING
                // sibling — the `*r = b` Deref-store through the `&mut o` is not tracked as a
                // write to `o`, so the payload symbol stays stale. Emit a FRESH dest (skip
                // the equality) so the two reads are independent. Fail-closed: dropping the
                // equality only turns PROVE -> not-proved, never a false-FAIL; the safe
                // non-mutated form (no `&mut o`) is unaffected and still proves.
                if let Operand::Copy(p) | Operand::Move(p) = operand
                    && p.projections
                        .iter()
                        .any(|pr| matches!(pr, trust_types::Projection::Downcast(_)))
                    && local_is_mutably_borrowed(func, p.local)
                {
                    continue;
                }
                operand_to_formula_with_array_ctx(func, operand, Some(&read_ctx))
            }
            Rvalue::BinaryOp(op, lhs, rhs) => {
                // an unsigned right-shift by a constant tightens its result
                // below the type max; push that bound BEFORE the `dest == lhs >> rhs`
                // equality (mirroring #52) so it survives the operand-clobber dedup, and
                // so `(x >> k) + …` proves even when `x` is an unconstrained payload.
                if let Some(range) = shift_result_range(func, op, lhs, rhs, &dest_name) {
                    defs.push(range);
                }
                let lhs_ty = crate::operand_ty_cow(func, lhs);
                if lhs_ty.as_deref().is_some_and(|ty| matches!(ty, Ty::Bool)) {
                    let l = operand_to_formula_with_array_ctx(func, lhs, Some(&read_ctx));
                    let r = operand_to_formula_with_array_ctx(func, rhs, Some(&read_ctx));
                    match op {
                        BinOp::BitAnd => Formula::And(vec![l, r]),
                        BinOp::BitOr => Formula::Or(vec![l, r]),
                        BinOp::BitXor => {
                            Formula::Not(Box::new(Formula::Eq(Box::new(l), Box::new(r))))
                        }
                        _ => {
                            // Pass signedness for correct right-shift selection.
                            let width = lhs_ty.as_deref().and_then(|ty| ty.int_width());
                            let signed = lhs_ty.as_deref().is_some_and(|ty| ty.is_signed());
                            // Trust #integrity: fail closed — skip the def
                            // (a dropped hypothesis), never panic mid-verification.
                            match crate::chc::try_binop_to_formula(*op, l, r, width, signed) {
                                Ok(formula) => formula,
                                Err(_) => continue,
                            }
                        }
                    }
                } else if let Some(Ty::Float { width }) = lhs_ty.as_deref() {
                    // Float ARITHMETIC (Add/Sub/Mul/Div): the dest is a
                    // BitVec(width) bit pattern, so the value-definition is a
                    // COMPLETE structural Eq lifting both sides into FP space
                    // (Eq(FpFromBits(dest), fp.op(RNE, ..))). Push it directly and
                    // `continue` — the generic emitter at the bottom would build
                    // Eq(Var(dest, BitVec), <FP term>), which is ill-sorted.
                    if let Some(def) = fp_arith_value_def(func, *op, lhs, rhs, &dest_name, *width) {
                        defs.push(def);
                        continue;
                    }
                    // Comparisons return a Bool result for the generic
                    // `dest_bool == fp.cmp(..)` definition.
                    match float_binop_to_formula(func, *op, lhs, rhs, *width) {
                        Some(formula) => formula,
                        None => continue,
                    }
                } else {
                    let l = operand_to_formula_with_array_ctx(func, lhs, Some(&read_ctx));
                    let r = operand_to_formula_with_array_ctx(func, rhs, Some(&read_ctx));
                    // Pass signedness for correct right-shift selection.
                    let width = lhs_ty.as_ref().and_then(|ty| ty.int_width());
                    let signed = lhs_ty.as_ref().is_some_and(|ty| ty.is_signed());
                    // Trust (2026-07-06, modulo-index): an UNSIGNED `dest = a % b`
                    // with a NON-CONSTANT divisor (`i % s.len()`, the common
                    // ring-buffer idiom) produces a nonlinear `%` TERM that ay's
                    // linear-arith lane REJECTS (`ay_lra … has_unsupported`,
                    // re-parse FAILED), fail-closing the safe index `s[i%s.len()]`
                    // to UNKNOWN. The LINEAR bound `(b==0) ∨ (dest < b)` from the
                    // GLOBAL `build_modulo_bound_facts` is SUFFICIENT to discharge
                    // the index (with the `len>0` guard), so DROP this nonlinear
                    // scalar def rather than emit a term no linear backend can
                    // parse. DROP-ONLY: removing a hypothesis can only WEAKEN a
                    // PROVE, never manufacture a false-PROVE; the bound fact
                    // compensates for the common bound/comparison uses. A CONSTANT
                    // divisor keeps its def (`% k` is a smaller, often-handled term
                    // whose exact value may matter).
                    if matches!(op, trust_types::BinOp::Rem)
                        && !signed
                        && !matches!(rhs, Operand::Constant(_))
                    {
                        continue;
                    }
                    // Trust #integrity: fail closed — skip the def
                    // (a dropped hypothesis), never panic mid-verification.
                    match crate::chc::try_binop_to_formula(*op, l, r, width, signed) {
                        Ok(formula) => formula,
                        Err(_) => continue,
                    }
                }
            }
            Rvalue::UnaryOp(trust_types::UnOp::Neg, op) => {
                // Float negation is EXACT (a sign-bit flip): define
                // FpFromBits(dest) = fp.neg(FpFromBits(op)) and `continue`
                // (the dest is BitVec; integer `Formula::Neg` would be ill-sorted
                // on a float bit pattern). Fail-closed on non-IEEE widths.
                if let Some(Ty::Float { width }) = crate::operand_ty_cow(func, op).as_deref() {
                    if let Some(def) = fp_neg_value_def(func, op, &dest_name, *width) {
                        defs.push(def);
                    }
                    continue;
                }
                Formula::Neg(Box::new(operand_to_formula_with_array_ctx(func, op, Some(&read_ctx))))
            }
            Rvalue::UnaryOp(trust_types::UnOp::Not, op) => {
                Formula::Not(Box::new(operand_to_formula_with_array_ctx(func, op, Some(&read_ctx))))
            }
            Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, op) => {
                match slice_len_formula(func, op) {
                    Some(formula) => formula,
                    None => continue,
                }
            }
            // Trust: `_N = Len(s)` ties the length temp `_N` to the slice's
            // `<s>__slice_len` symbol — the SAME symbol the index/bounds obligation
            // uses (rvalue_safety::collection_len_formula). Without this fact, a
            // dominating guard `index < s.len()` (resolved to `Lt(index, _N)`) is
            // name-disjoint from the obligation `Ge(index, s__slice_len)` and cannot
            // discharge it — a false-positive `index_out_of_bounds`. Mirrors the
            // `PtrMetadata` arm above (and `Rvalue::Len` is already treated this way
            // in generate.rs). `Len` IS the slice length, so the emitted
            // `Eq(Var(_N), s__slice_len)` is a model tautology (sound, monotone).
            Rvalue::Len(place) => match slice_len_formula(func, &Operand::Copy(place.clone())) {
                Some(formula) => formula,
                None => continue,
            },
            Rvalue::Cast(op, to_ty) => {
                // push the source-width range on the result FIRST, so the
                // clobber-dedup below (which keys staleness on each `Eq` lhs) sees the
                // range before this cast's own `dest == source` equality inserts `dest`
                // into the clobbered set — otherwise the range would be dropped as
                // "stale against its own dest". The range is a value-preserving-widening
                // tautology, so at worst its omission costs precision, never soundness.
                if let Some(range) = widening_cast_result_range(func, op, to_ty, &dest_name) {
                    defs.push(range);
                }
                // Trust (drop-in cast type-tracking): a narrowing / reinterpreting
                // int->int cast carries no CastOverflow VC (defined behavior); track
                // the type change so downstream stays sound + precise by bounding the
                // dest to its TARGET-type range. Push BEFORE the `dest == source`
                // equality (same clobber-dedup ordering rationale as the widening
                // range above).
                if let Some(range) = narrowing_cast_result_range(func, op, to_ty, &dest_name) {
                    defs.push(range);
                }
                match cast_definition_formula(func, place, op, to_ty) {
                    Some(formula) => formula,
                    None => continue,
                }
            }
            Rvalue::Aggregate(kind, operands) => {
                // Trust: whole-array CONSTRUCTION of an eligible array-theory local
                // — seed `v0 == Store(Store(.. Store(FREE_base, 0, e0) ..), N-1,
                // eN-1))` so element reads via `Select(v0, c)` resolve. This bypasses
                // the scalar aggregate_field_definitions / `[c;min=len]` path.
                if matches!(kind, AggregateKind::Array)
                    && place.projections.is_empty()
                    && let Some(model) = crate::array_theory_local(func, place.local)
                {
                    if let Some(seed) = array_construction_seed(
                        func,
                        place.local,
                        &model.elem_sort,
                        operands,
                        &read_ctx,
                    ) {
                        defs.push(seed);
                    }
                    continue;
                }
                let mut field_defs = aggregate_field_definitions(func, place, kind, operands);
                // SOUNDNESS (P0 false proof, 2026-06-17 hunt-7): suppress the construction field
                // facts `place@k.i == op_i` when `place` is mutably borrowed anywhere — `&mut place`
                // or `place.as_mut()` (any call taking `&mut place`) can REASSIGN the payload AFTER
                // construction (`let mut o=Some(a.min(3)); if let Some(r)=o.as_mut(){*r=b;} match o {
                // Some(i)=>arr[i] }`), so a propagated `o@1.0 == _5` is STALE and vacuously discharges
                // the `arr[i]` bounds obligation on the mutated payload `i==b` (OOB). The downstream
                // kill machinery does not remove it (the demux re-injects, and the `*r=b` Deref-store
                // through the returned `&mut` is not tracked as a write to `o`), so drop it at the
                // SOURCE. Fail-closed: losing a construction fact only turns PROVE -> not-proved.
                if !(place.projections.is_empty() && local_is_mutably_borrowed(func, place.local)) {
                    for (field_name, field_def) in field_defs.drain(..).rev() {
                        if seen_dests.insert(field_name) {
                            defs.push(field_def);
                        }
                    }
                }
                continue;
            }
            // Trust: `[op; count]` construction of an eligible array-theory local.
            // For a small `count` build a finite Store chain; otherwise leave `v0`
            // as the FREE base (sound — reads then resolve to an unconstrained
            // element, a false-FAIL, never a false-PROVE).
            Rvalue::Repeat(op, count)
                if place.projections.is_empty()
                    && crate::array_theory_local(func, place.local).is_some() =>
            {
                if let Some(model) = crate::array_theory_local(func, place.local)
                    && let Some(seed) = array_repeat_seed(
                        func,
                        place.local,
                        &model.elem_sort,
                        op,
                        *count,
                        &read_ctx,
                    )
                {
                    defs.push(seed);
                }
                continue;
            }
            // A shared borrow `r = &P` implies `*r == P`. The compiler lowers a
            // match-guard binding by reference (`_4 = &payload; guard tests
            // *_4`) while the arm body reads the payload by value, so without
            // this the guard constrains a free `*r` variable disconnected from
            // the value the arm uses — and a guarded binding like
            // `Some(v) if v < K => v + 1` false-fails. Connecting the deref name
            // to the referent fixes it. Sound for shared refs (P cannot be
            // mutated through an immutable borrow). `&mut` is deliberately
            // skipped: a later `*r = ..` could invalidate the equality.
            //
            // `place_to_var_name` renders a trailing `Deref` projection as a
            // `*` suffix, so the deref place's name is exactly `dest_name + "*"`.
            Rvalue::Ref { place: referent, mutable: false } => {
                let deref_name = format!("{dest_name}*");
                if seen_dests.insert(deref_name.clone()) {
                    let sort = crate::place_sort(func, referent).unwrap_or(Sort::Int);
                    defs.push(Formula::Eq(
                        Box::new(Formula::Var(deref_name, sort.clone())),
                        Box::new(Formula::Var(crate::place_to_var_name(func, referent), sort)),
                    ));
                }
                push_borrow_slice_len(func, &dest_name, referent, &mut defs, &mut seen_dests);
                continue;
            }
            // A MUTABLE borrow `r = &mut P` cannot change the referent slice's
            // LENGTH — a slice's length metadata is immutable through `&mut [T]`
            // (only its ELEMENTS are mutable) — so, exactly like `AddressOf` below
            // and `push_borrow_slice_len`'s own contract, tie the length. We do NOT
            // tie the deref-VALUE equality here (that IS unsound for `&mut`, since a
            // later `*r = ..` could invalidate it — the shared arm above owns it).
            // This lets a guarded `&mut [T]` op — `if i < s.len() { *s.get_unchecked_mut(i) = v }`
            // — discharge: the guard's `s.len()` and the `&mut (*s)` receiver
            // reborrow resolve to the same `{param}__slice_len`. SOUND: the emitted
            // `{dest}__slice_len == referent_len` is a TRUE fact (a reborrow
            // preserves length), so conjoining it removes no real model.
            Rvalue::Ref { place: referent, mutable: true } => {
                push_borrow_slice_len(func, &dest_name, referent, &mut defs, &mut seen_dests);
                continue;
            }
            // `r = &raw const/mut P` (e.g. the `FakeForPtrMetadata` pointer that
            // `<[T]>::len()` reads on a `&mut [T]`). Tie the pointer's slice length
            // to the referent slice's so a `PtrMetadata(r)` read recovers it.
            Rvalue::AddressOf(_mutable, referent) => {
                push_borrow_slice_len(func, &dest_name, referent, &mut defs, &mut seen_dests);
                continue;
            }
            // Skip complex rvalues — not needed for basic dataflow tracking.
            _ => continue,
        };

        defs.push(Formula::Eq(
            Box::new(Formula::Var(dest_name, dest_sort)),
            Box::new(rvalue_formula),
        ));
    }

    // Trust: drop any def whose rvalue mentions a local a *later* statement in
    // this block overwrites. `defs` is in reverse program order here (the last
    // statement's defs first), so a front-to-back walk meets later statements
    // before earlier ones; a fact is stale exactly when one of its operands is
    // the destination of an already-visited (later) statement. Retaining such a
    // fact is unsound: `c = m < 1000; m = BIG;` would otherwise emit
    // `c == (m < 1000)` against the post-`m = BIG` value of `m`, and inside a
    // later `if c { m + 1 }` the contradictory hypotheses vacuously discharge the
    // overflow VC — a false-PROVE of a real overflow. The same-block last-write
    // dedup above only catches a redefined *destination*; this catches a
    // redefined *operand*. Dropping a fact only removes a hypothesis, so it can
    // introduce a false-FAIL but never a false-PROVE.
    let mut clobbered: FxHashSet<String> = FxHashSet::default();
    defs.retain(|d| {
        let lhs = match d {
            Formula::Eq(l, _) => l.var_name().map(str::to_string),
            _ => None,
        };
        // Trust (ARM-B, versioned-consumer relax): a PURE PLACE-READ def
        // (`Eq(Var(_t), Var(place))` from `_t = Copy/Move(place)`) survives the
        // staleness kill on the establish-point-versioned path — the consumer
        // stamps the RHS read at the def's own statement, so a later clobber of
        // the read place mints a DIFFERENT token and cannot unify (see
        // `extract_block_definitions_until_versioned`). Computed defs keep the
        // kill: their hazard example (`c = m < 1000; m = BIG`) stays dropped.
        let versionable_read_def = keep_versionable_read_defs
            && matches!(d, Formula::Eq(l, r)
                if l.var_name().is_some() && r.var_name().is_some());
        // Prefix-aware (soundness round-11): a fact is stale if a free
        // variable OVERLAPS a clobbered place (e.g. clobbering `x` invalidates a
        // fact mentioning `x.0`), not only on exact-name equality.
        let stale = !versionable_read_def
            && d.free_variables().iter().any(|v| {
                Some(v) != lhs.as_ref()
                    && clobbered.iter().any(|c| crate::generate::place_names_overlap(v, c))
            });
        if let Some(l) = lhs {
            clobbered.insert(l);
        }
        !stale
    });

    defs.reverse();
    defs
}

/// Every name a block may write while a proof snapshot is being transported,
/// or `None` when the statement surface is not known to be value-transparent.
///
/// `generate::block_written_names` supplies the canonical alias-aware set
/// (including opaque dereference havoc and terminator destinations). Add every
/// explicit place destination as a belt-and-suspenders gate because ordinary
/// definition extraction intentionally declines some rvalues. Unknown/future
/// statements fail closed: a newly added write-capable variant must never
/// silently preserve a stale branch or checked-arithmetic snapshot.
fn conservative_snapshot_writes(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Option<FxHashSet<String>> {
    let mut writes = crate::generate::block_written_names(func, block);
    for stmt in &block.stmts {
        match stmt {
            Statement::Assign { place, .. }
            | Statement::SetDiscriminant { place, .. }
            | Statement::Deinit { place } => {
                writes.insert(crate::place_to_var_name(func, place));
            }
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Retag { .. }
            | Statement::PlaceMention(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => {}
            Statement::Intrinsic { .. } | Statement::Unsupported { .. } => return None,
            _ => return None,
        }
    }
    Some(writes)
}

/// Recover the merged-local invariant at an n-arm `SwitchInt` join.
///
/// The path-definition BFS weakens to `true` at any join reached with differing
/// accumulated defs, which turns a branch-merged local (`let x = match e { A =>
/// a, B => b, C => c }`) into a free variable that a solver then false-refutes.
/// When every predecessor of `join` is a single-predecessor `Goto(join)` arm and
/// all those arms descend from the *same* `SwitchInt`, the arms partition every
/// execution reaching `join`: a switch takes exactly one successor, so the arm
/// guards are mutually exclusive and — restricted to paths that actually reach
/// `join` — exhaustive. The equality
/// `x == Ite(g_0, x_0, Ite(g_1, x_1, … x_last))` therefore holds on every
/// incoming path, so emitting it is sound and lets bounded-overflow VCs over `x`
/// discharge. (The two-arm diamond `if c { a } else { b }` is the n=2 instance
/// and is encoded byte-identically to before.)
///
/// Soundness of the catch-all `else`: the last arm's guard is dropped, so the
/// `else` value is claimed whenever no earlier guard fires. On any execution
/// that *reaches* `join` the discriminant equals one arm's value, so the `else`
/// is only reached when the last arm was genuinely taken. The phantom region
/// (discriminant values that route to a divergent/unreachable `otherwise` and so
/// never reach `join`) is unconstrained, but those paths are exactly the ones
/// excluded from `join`, so no reachable join-path is misconstrained.
///
/// The `if`-without-`else` shape is the same partition with one arm elided: the
/// switch jumps *directly* to `join` on the skip edge, so the switch block itself
/// is one of `join`'s predecessors. That edge is the `else` arm whose merged value
/// is the local's value at the switch's own exit (no statement runs between the
/// switch and the join). Modelling it this way is what lets a safe
/// `let mut s = 0; if c { s = K; } s + 1` prove while an unguarded
/// `if c { s = K; } s + b` correctly fails — without it the join keeps a stale,
/// unsound `s == 0` that vacuously discharges the overflow VC.
///
/// Returns one `Eq(Var(local), Ite(..))` per local defined in *every* arm.
/// Any deviation from the strict partition shape yields an empty vec.
///
/// `incoming` is the converged (pre-merge) path-definition map — each block's
/// entry-fact intersection across every path that reaches it. It supplies the
/// skip-edge value of a local the switch block does not itself assign (see the
/// augmentation block below). Pass an empty map to disable that augmentation;
/// clean diamonds and same-block-init shapes are unaffected by it.
pub(crate) fn branch_merge_definitions(
    func: &VerifiableFunction,
    join: BlockId,
    incoming: &FxHashMap<BlockId, Vec<Formula>>,
) -> Vec<Formula> {
    let blocks = &func.body.blocks;
    if join.0 >= blocks.len() {
        return Vec::new();
    }
    let preds = block_predecessors(func);
    let join_preds = &preds[join.0];
    // A merge needs at least two incoming arms.
    if join_preds.len() < 2 {
        return Vec::new();
    }
    // Classify each join predecessor. A *Goto arm* is a single-predecessor
    // `Goto(join)` block — the body of one switch branch. A *direct* predecessor
    // is the switch block itself flowing straight into the join: the skip edge of
    // an `if` without an `else` (`if c { s = .. } use(s)` lowers the false case to
    // a direct switch→join edge). A clean diamond has only Goto arms; an
    // if-without-else has exactly one direct predecessor (the switch).
    let is_goto_arm = |p: BlockId| {
        matches!(&blocks[p.0].terminator, Terminator::Goto(t) if *t == join)
            && preds[p.0].len() == 1
    };
    let goto_arms: Vec<BlockId> = join_preds.iter().copied().filter(|p| is_goto_arm(*p)).collect();
    let direct: Vec<BlockId> = join_preds.iter().copied().filter(|p| !is_goto_arm(*p)).collect();

    // The nearest switch predecessor of a join arm. In addition to the direct
    // `SwitchInt -> arm -> Goto(join)` diamond, accept exactly one intervening
    // successful `Assert`:
    //
    //   SwitchInt -> checked-op/Assert -> value arm -> Goto(join)
    //
    // rustc emits this shape when one branch computes a checked integer value.
    // The Assert's failure edge does not reach `join`; therefore every execution
    // that does reach the join through this branch took the authenticated success
    // edge, and the original switch still partitions the join's incoming paths.
    // Ordinary Goto/Call/Drop hops remain rejected: unlike an Assert success edge,
    // they are not this narrowly authenticated branch extension.
    let branch_switch_predecessor = |arm: BlockId| -> Option<BlockId> {
        let [parent] = preds[arm.0].as_slice() else {
            return None;
        };
        if matches!(blocks[parent.0].terminator, Terminator::SwitchInt { .. }) {
            return Some(*parent);
        }
        let Terminator::Assert { target, unwind, .. } = &blocks[parent.0].terminator else {
            return None;
        };
        if *target != arm || unwind.cleanup_target() == Some(arm) {
            return None;
        }
        let [switch] = preds[parent.0].as_slice() else {
            return None;
        };
        matches!(blocks[switch.0].terminator, Terminator::SwitchInt { .. }).then_some(*switch)
    };

    // Identify the single `SwitchInt` every arm descends from.
    let switch_id = match direct.as_slice() {
        // Clean diamond: every join predecessor is a Goto arm; all must share one
        // switch predecessor, possibly through the exact Assert-success extension
        // above.
        [] => {
            let Some(s) = goto_arms.first().and_then(|a| branch_switch_predecessor(*a)) else {
                return Vec::new();
            };
            if !goto_arms.iter().all(|a| branch_switch_predecessor(*a) == Some(s)) {
                return Vec::new();
            }
            s
        }
        // if-without-else: the lone direct predecessor is the switch, and every
        // Goto arm must descend from it (again allowing the exact Assert-success
        // extension).
        [s] => {
            let s = *s;
            if !matches!(blocks[s.0].terminator, Terminator::SwitchInt { .. })
                || !goto_arms.iter().all(|a| branch_switch_predecessor(*a) == Some(s))
            {
                return Vec::new();
            }
            s
        }
        // More than one non-Goto predecessor is not a switch partition we model.
        _ => return Vec::new(),
    };

    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &blocks[switch_id.0].terminator
    else {
        return Vec::new();
    };

    // A merge equality needs the switch guard's exact characteristic function,
    // not the precision-oriented guard assumption used by ordinary VCs (that
    // API may deliberately weaken a predicate's false arm to `true`). Validate
    // every raw table value now, including values that may later become the
    // catch-all arm, and reject duplicate values even when malformed TrustIR
    // routes them to different destinations.
    let mut seen_values = FxHashSet::default();
    if targets.iter().any(|(value, _)| {
        !seen_values.insert(*value) || exact_switch_value_guard(func, discr, *value).is_none()
    }) {
        return Vec::new();
    }

    // The raw discriminator denotes its value at the switch. Because formulas
    // here are intentionally unversioned, any write to that place (or an
    // alias/ancestor/descendant) before the join would make an Ite guard read a
    // different value and assert a false merge equality. Check every admitted
    // post-switch block: the direct value arm, plus its unique Assert parent
    // when present. Unknown statement effects fail closed.
    let discr_names = operand_to_formula(func, discr).free_variables();
    for arm in &goto_arms {
        let [parent] = preds[arm.0].as_slice() else {
            return Vec::new();
        };
        for path_block in
            [Some(*arm), (*parent != switch_id).then_some(*parent)].into_iter().flatten()
        {
            let Some(writes) = conservative_snapshot_writes(func, &blocks[path_block.0]) else {
                return Vec::new();
            };
            if discr_names.iter().any(|name| {
                writes.iter().any(|written| crate::generate::place_names_overlap(name, written))
            }) {
                return Vec::new();
            }
        }
    }

    // The block whose *exit* state supplies an arm's merged value, given a switch
    // destination `tb`: the join reached directly (the skip edge) takes the
    // switch's own exit; a Goto arm takes that arm block's exit; anything else
    // diverges, never reaches the join, and contributes no arm. Modelling the
    // skip edge as `switch_id`'s exit is sound — no statement runs between the
    // switch and the join on that edge, so the local holds its switch-exit value.
    let arm_source = |tb: BlockId| -> Option<BlockId> {
        if tb == join {
            Some(switch_id)
        } else if goto_arms.contains(&tb) {
            Some(tb)
        } else if let Terminator::Assert { target, unwind, .. } = &blocks[tb.0].terminator
            && goto_arms.contains(target)
            && preds[target.0] == [tb]
            && preds[tb.0] == [switch_id]
            && unwind.cleanup_target() != Some(*target)
        {
            Some(*target)
        } else {
            None
        }
    };

    // A `otherwise` that also appears as an explicit target tangles the partition
    // (one block reached by a value *and* the complement) — decline it.
    if targets.iter().any(|(_, t)| t == otherwise) {
        return Vec::new();
    }

    // Group explicit targets by their def-source, preserving first-seen order and
    // accumulating every routing value (an or-pattern sends several values to one
    // arm). Targets that never reach `join` are dropped.
    let mut explicit: Vec<(BlockId, Vec<u128>)> = Vec::new();
    for (value, target) in targets {
        let Some(src) = arm_source(*target) else {
            continue;
        };
        if let Some((_, values)) = explicit.iter_mut().find(|(b, _)| *b == src) {
            values.push(*value);
        } else {
            explicit.push((src, vec![*value]));
        }
    }

    // Choose the catch-all (`else`) arm's def-source. If `otherwise` reaches the
    // join it is the natural else (its guard is the negation of every target
    // value); otherwise the last explicit arm serves as the else under switch
    // totality.
    let else_source = match arm_source(*otherwise) {
        Some(src) => src,
        None => match explicit.pop() {
            Some((b, _)) => b,
            None => return Vec::new(),
        },
    };

    // Need at least one guarded arm besides the else to constrain anything.
    if explicit.is_empty() {
        return Vec::new();
    }

    // Every join predecessor must be accounted for. A Goto-arm predecessor maps to
    // its own block; the direct (switch) predecessor maps to `switch_id`. The set
    // of def-sources we built must match exactly, or the merge isn't this switch's
    // partition.
    let expected: FxHashSet<BlockId> =
        join_preds.iter().map(|p| if is_goto_arm(*p) { *p } else { switch_id }).collect();
    let mut covered: FxHashSet<BlockId> = explicit.iter().map(|(b, _)| *b).collect();
    covered.insert(else_source);
    if covered != expected {
        return Vec::new();
    }

    // Per-arm `(name, sort, value)` maps; the else arm sits last. For the exact
    // Assert-success extension, the value arm commonly copies the checked
    // tuple's `.0` field:
    //
    //   checked = CheckedAdd(a, b); Assert(!checked.1) -> arm
    //   arm: merged = checked.0; Goto(join)
    //
    // `checked.0` is not defined on the sibling arm, so the ordinary
    // intersection correctly drops its definition and would leave the merged
    // value free. Inline only the semantic equalities authenticated by that
    // unique Assert-success edge (`checked.0 == a + b`, etc.) into that arm's
    // values. This is not a general predecessor walk: it requires the exact
    // parent/target/switch identity already admitted above, and
    // `extract_assert_passed_semantics` itself requires the checked-op tuple
    // and overflow-flag projection shape.
    let arm_definition_map_with_checked_assert = |arm: BlockId| {
        let mut defs = arm_definition_map(func, arm);
        let [parent] = preds[arm.0].as_slice() else {
            return defs;
        };
        let Terminator::Assert { target, unwind, .. } = &blocks[parent.0].terminator else {
            return defs;
        };
        if *target != arm
            || unwind.cleanup_target() == Some(arm)
            || preds[parent.0] != [switch_id]
        {
            return defs;
        }

        let Some((tuple_local, _, _, _, _)) =
            exact_asserted_checked_binary_op(func, &blocks[parent.0])
        else {
            return defs;
        };
        let tuple_name = func
            .body
            .locals
            .get(tuple_local)
            .and_then(|decl| decl.name.as_deref())
            .map_or_else(|| format!("_{tuple_local}"), str::to_string);
        let result_name = format!("{tuple_name}.0");
        let Some(result_rhs) = extract_assert_passed_semantics(func, &blocks[parent.0])
            .into_iter()
            .find_map(|semantic| match semantic {
                Formula::Eq(lhs, rhs) if lhs.var_name() == Some(result_name.as_str()) => Some(*rhs),
                _ => None,
            })
        else {
            return defs;
        };

        // Substitution must preserve the value snapshot taken by CheckedBinaryOp.
        // If the success arm writes either the checked field or any operand used
        // by its mathematical RHS, replacing `checked.0` with the arm-exit name
        // would read the *new* value and could manufacture a false proof. Use the
        // canonical alias-aware write set, plus every explicit place destination
        // (including rvalues the definition extractor intentionally declines).
        let Some(arm_writes) = conservative_snapshot_writes(func, &blocks[arm.0]) else {
            return defs;
        };
        let snapshot_names =
            result_rhs.free_variables().into_iter().chain(std::iter::once(result_name.clone()));
        if snapshot_names.into_iter().any(|name| {
            arm_writes.iter().any(|written| crate::generate::place_names_overlap(&name, written))
        }) {
            return defs;
        }

        for (_, _, value) in &mut defs {
            *value = crate::quantifier_tiers::substitute(value, &result_name, &result_rhs);
        }
        defs
    };
    let mut arm_defs: Vec<Vec<(String, Sort, Formula)>> =
        explicit.iter().map(|(b, _)| arm_definition_map_with_checked_assert(*b)).collect();
    arm_defs.push(arm_definition_map_with_checked_assert(else_source));

    // if-without-else skip edge. The arm whose def-source is the switch
    // block runs no statement between the switch and the join, so a local it does
    // not itself assign keeps the value it held on entry to the switch. Without
    // this, a local assigned only on the *other* arm (`if c { lo = 0 }`) is absent
    // from the skip arm, never merges, and stays a free variable that false-FAILs a
    // safe `hi - lo`. (The pre-existing path covers only the shape where the switch
    // block ITSELF initialises the local — `s = 0; cmp = ..; switch cmp` — but real
    // MIR routinely splits the initialiser into an ancestor block, e.g. when an
    // earlier checked-arith assert ends the init block.) Fill each missing local
    // with its incoming dominating value from `incoming[switch_id]` — the
    // INTERSECTION of every path reaching the switch, hence a fact true on every
    // such path and not stale (the dataflow kills a fact when any variable it
    // mentions is reassigned). Soundness: this adds a genuinely-true equality, which
    // by monotonicity can only turn a FAIL into a PROVE, never a real overflow into
    // a false-PROVE. Only locals the switch block does not assign are filled, and
    // only when the incoming value is unambiguous (exactly one defining equality);
    // an absent or ambiguous value leaves the local free (a sound false-FAIL, no
    // worse than before this fix).
    let skip_idx = explicit
        .iter()
        .position(|(b, _)| *b == switch_id)
        .or_else(|| (else_source == switch_id).then(|| arm_defs.len() - 1));
    if let Some(skip_idx) = skip_idx
        && let Some(incoming_defs) = incoming.get(&switch_id)
    {
        let skip_present: FxHashSet<String> =
            arm_defs[skip_idx].iter().map(|(n, _, _)| n.clone()).collect();
        // Locals defined on some *other* arm but not on the skip arm, with sort.
        let mut others: Vec<(String, Sort)> = Vec::new();
        for (i, arm) in arm_defs.iter().enumerate() {
            if i == skip_idx {
                continue;
            }
            for (n, s, _) in arm {
                if !skip_present.contains(n) && !others.iter().any(|(on, _)| on == n) {
                    others.push((n.clone(), s.clone()));
                }
            }
        }
        for (name, sort) in others {
            // Sole defining equality `name == rhs` in the switch's entry state.
            let mut vals = incoming_defs.iter().filter_map(|f| match f {
                Formula::Eq(lhs, rhs) => match lhs.as_ref() {
                    Formula::Var(n, _) if *n == name => Some(rhs.as_ref()),
                    _ => None,
                },
                _ => None,
            });
            if let Some(rhs) = vals.next()
                && vals.next().is_none()
            {
                arm_defs[skip_idx].push((name, sort, rhs.clone()));
            }
        }
    }

    let else_defs = &arm_defs[arm_defs.len() - 1];

    // Only locals defined in *every* arm (including the else) merge into a total
    // Ite; iterate the first arm's locals and require presence in all the rest.
    let mut out = Vec::new();
    for (name, sort, _) in &arm_defs[0] {
        let Some(else_value) =
            else_defs.iter().find(|(n, _, _)| n == name).map(|(_, _, v)| v.clone())
        else {
            continue;
        };
        let mut per_arm: Vec<Formula> = Vec::with_capacity(explicit.len());
        let mut complete = true;
        for arm in arm_defs.iter().take(explicit.len()) {
            match arm.iter().find(|(n, _, _)| n == name) {
                Some((_, _, v)) => per_arm.push(v.clone()),
                None => {
                    complete = false;
                    break;
                }
            }
        }
        if !complete {
            continue;
        }
        // Fold innermost-last: Ite(g_0, v_0, Ite(g_1, v_1, … else_value)).
        let mut acc = else_value;
        for idx in (0..explicit.len()).rev() {
            let mut guards = Vec::with_capacity(explicit[idx].1.len());
            for value in &explicit[idx].1 {
                let Some(guard) = exact_switch_value_guard(func, discr, *value) else {
                    return Vec::new();
                };
                guards.push(guard);
            }
            let guard = match guards.len() {
                0 => return Vec::new(),
                1 => guards.pop().unwrap_or_else(|| unreachable!("one exact switch guard")),
                _ => Formula::Or(guards),
            };
            acc = Formula::Ite(Box::new(guard), Box::new(per_arm[idx].clone()), Box::new(acc));
        }
        out.push(Formula::Eq(Box::new(Formula::Var(name.clone(), sort.clone())), Box::new(acc)));
    }
    out
}

/// Exact raw route guard for one `SwitchInt` table value.
///
/// Do not call [`guard_to_formula`] here: it is an assumption-strengthening API
/// and deliberately returns one-way facts for some boolean predicates. An Ite
/// selector requires equality with the raw discriminator value. Signed MIR
/// targets need sign-extension before comparison; this narrow merge lane
/// currently fails closed on signed discriminators rather than risk interpreting
/// (for example) i8 `-1`'s raw `0xff` as mathematical `255`.
fn exact_switch_value_guard(
    func: &VerifiableFunction,
    discr: &Operand,
    value: u128,
) -> Option<Formula> {
    let ty = crate::operand_ty_cow(func, discr)?;
    let raw = operand_to_formula(func, discr);
    match ty.as_ref() {
        Ty::Bool if value <= 1 => Some(if value == 0 { Formula::Not(Box::new(raw)) } else { raw }),
        Ty::Int { width, signed: false } if *width > 0 && *width <= 128 => {
            if *width < 128 && value >= (1u128 << *width) {
                return None;
            }
            Some(Formula::Eq(Box::new(raw), Box::new(u128_to_formula(value))))
        }
        Ty::PtrSizedInt { signed: false } if value <= u64::MAX as u128 => {
            Some(Formula::Eq(Box::new(raw), Box::new(u128_to_formula(value))))
        }
        Ty::Char if value <= char::MAX as u128 && !(0xD800..=0xDFFF).contains(&(value as u32)) => {
            Some(Formula::Eq(Box::new(raw), Box::new(u128_to_formula(value))))
        }
        _ => None,
    }
}

/// Predecessor lists for every block, covering both guarded
/// (`SwitchInt`/`Assert`) and unguarded (`Goto`/`Call`/`Drop`/`Opaque`) edges.
fn block_predecessors(func: &VerifiableFunction) -> Vec<Vec<BlockId>> {
    let n = func.body.blocks.len();
    let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); n];
    for block in &func.body.blocks {
        let mut targets = block.terminator.unguarded_successors();
        for clause in block.terminator.discovered_clauses(block.id) {
            if let trust_types::ClauseTarget::Block(t) = clause.target {
                targets.push(t);
            }
        }
        for t in targets {
            if t.0 < n && !preds[t.0].contains(&block.id) {
                preds[t.0].push(block.id);
            }
        }
    }
    preds
}

/// Per-local `(name, sort, value)` defined by an arm's assignments.
fn arm_definition_map(func: &VerifiableFunction, arm: BlockId) -> Vec<(String, Sort, Formula)> {
    extract_block_definitions(func, &func.body.blocks[arm.0])
        .into_iter()
        .filter_map(|f| match f {
            Formula::Eq(lhs, rhs) => match *lhs {
                Formula::Var(name, sort) => Some((name, sort, *rhs)),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// Route enum-payload facts across a construction join into the
/// matching discriminant-switch arm — a "de-mux" of the join.
///
/// `match` on a freshly-constructed enum lowers to:
/// ```text
///   bbA: place = Aggregate(Adt variant kA, [payloadsA]); Goto J
///   bbB: place = Aggregate(Adt variant kB, [payloadsB]); Goto J
///   J:   d = Discriminant(place); SwitchInt(d) -> [.. -> arm] otherwise ow
///   arm: .. reads place.downcast(k).field(i) ..        // k = the arm's variant
/// ```
/// Each construction block emits payload field facts `place@k.i == payload_i`
/// (`aggregate_field_definitions`), but a fact established on one arm is absent
/// on the others, so the intersection at `J` drops it; the consuming arm then
/// reads an unconstrained payload and a safe `payload + 1` false-FAILs
/// (`flag_result`, `flag_some`). `const_some` proves only because its single
/// straight-line construction has no join to intersect across.
///
/// The discriminant switch DE-MUXes the join: an arm that downcasts `place` to
/// variant `k` is reachable only when `discr(place)` selects variant `k`, i.e.
/// only when `place` was constructed as variant `k`. With EXACTLY ONE predecessor
/// constructing variant `k`, that predecessor ran on every path reaching the arm,
/// so its payload facts hold there. We route each construction's `place@k.*`
/// facts to the arm that downcasts variant `k`, bypassing the lossy join, and
/// return them per-ARM for the seed machinery (seeded into the arm's
/// outflow so a same-arm operand reassignment kills them via
/// `extend_killing_redefs`, and re-attached to the arm's entry so the arm's own
/// VCs see them).
///
/// Soundness — any deviation yields no facts for the join:
///  * `place@k.i` is read ONLY in the variant-`k` arm, reached ONLY when `place`
///    is variant `k`; the routed equality is therefore true wherever it can be
///    read, and an inert dangling variable anywhere it cannot.
///  * `J` must define the switch discriminant as `d = Discriminant(place)` and
///    assign nothing else, so neither `place` nor a payload operand is clobbered
///    between construction and the switch.
///  * every predecessor of `J` must be a `Goto(J)` block whose whole-`place`
///    assignment is an ADT `Aggregate`, with no variant built by two predecessors
///    (a non-unique payload could vacuously discharge a real overflow — see the
///    `demux_two_constructions_same_variant` probe test). The constructor's OWN
///    predecessor count is irrelevant to payload soundness (the payload is the
///    constructor's own aggregate, valid whenever it runs), so a variant whose
///    constructor is reached by several paths still routes — this is what lets
///    `flag_some`, whose None constructor is shared, de-mux at all.
///  * each routed-to arm must have `J` as its sole predecessor (so `place` cannot
///    arrive via another path) and must not itself reassign `place`.
///
/// Guard routing (follow-on): when a variant-`k` constructor `P_k` has a
/// UNIQUE predecessor `Q`, every path reaching the arm traverses the `Q→P_k` edge,
/// so that edge's guard (resolved through `guard_to_formula`, e.g. `v < 100`) is
/// true at the arm. It is routed alongside the payload, gated on `P_k` being
/// single-pred and on the guard's free variables not being reassigned by `P_k` or
/// `J`. The path-guard enumerator cannot supply this: it weakens the guard under a
/// disjunction with the (infeasible) other-variant→arm path.
///
/// Adding a genuinely-true equality or guard is monotone: it can turn a false-FAIL
/// into a PROVE for safe code, never make a real overflow PROVE.
/// True iff `local` is mutably borrowed anywhere in the function — a `Rvalue::Ref{mutable:true}`
/// or a raw `Rvalue::AddressOf(_, ..)` of `local`. NB: `o.as_mut()` (and any call taking `&mut o`)
/// materializes a `&mut o` borrow statement, so this catches the indirect mutation vector too.
/// Used to fail-close enum-payload routing whose construction-time value such a borrow can
/// reassign (`if let Some(r) = o.as_mut() { *r = b; }`).
pub(crate) fn local_is_mutably_borrowed(func: &VerifiableFunction, local: usize) -> bool {
    func.body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| {
            matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place),
                    ..
                } if place.local == local
            )
        })
    })
}

/// LENGTH-stability refinement of [`local_is_mutably_borrowed`]: true iff a mutable
/// borrow of `local` may RESIZE the container it points at. `Vec`/`String` `Index`/
/// `IndexMut` never change the length (std contract — the same semantic knowledge
/// `is_owned_slice_container_name` already encodes), so a `&mut` reborrow consumed
/// SOLELY as the receiver of `index`/`index_mut` is length-benign. This is what lets
/// the dominant WRITE idiom `v[i] = x` (whose `IndexMut::index_mut` call reborrows
/// `&mut (*v)`, tripping the coarse gate and formerly VANISHING the bounds
/// obligation — a silent false-accept) recover the abstract length: the guarded
/// write PROVES, the unguarded write REFUTES.
///
/// SOUNDNESS (fail-closed direction):
/// - a raw `&raw`/`AddressOf` borrow escapes all tracking → may-resize;
/// - a borrow stored through a projection (`s.f = &mut v`) escapes → may-resize;
/// - the borrow temp's uses are counted with the EXHAUSTIVE place walk
///   (`for_each_stmt/terminator_copy_move_place` — every operand AND place-valued
///   position); any mention beyond its definition and recognized benign call
///   receivers (a resize like `Vec::push`, a reborrow chain, an escape as a non-
///   receiver argument) → may-resize. Over-counting is conservative: it can only
///   DECLINE a recovery, never mint a stale length.
///
/// Callers: use this (not the coarse gate) ONLY where the fact at stake is the
/// container's LENGTH. Element-VALUE stability (enum-payload routing, demux) must
/// keep [`local_is_mutably_borrowed`]: `index_mut` hands out `&mut` to an element,
/// so values ARE reassignable through a length-benign borrow.
pub(crate) fn local_mut_borrows_may_resize(func: &VerifiableFunction, local: usize) -> bool {
    let mut temps: Vec<usize> = Vec::new();
    for b in &func.body.blocks {
        for s in &b.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = s else { continue };
            match rvalue {
                Rvalue::Ref { mutable: true, place } if place.local == local => {
                    if !dest.projections.is_empty() {
                        return true;
                    }
                    temps.push(dest.local);
                }
                Rvalue::AddressOf(_, place) if place.local == local => return true,
                _ => {}
            }
        }
    }
    for t in temps {
        // Total mentions of the temp anywhere in the body (exhaustive walk).
        let mut mentions = 0usize;
        let mut record = |p: &trust_types::Place| {
            if p.local == t {
                mentions += 1;
            }
        };
        for b in &func.body.blocks {
            for s in &b.stmts {
                crate::generate::for_each_stmt_copy_move_place(s, &mut record);
            }
            crate::generate::for_each_terminator_copy_move_place(&b.terminator, &mut record);
        }
        // Accounted-for mentions: the defining assign's dest, plus each use as the
        // projection-free RECEIVER (arg 0) of a length-preserving container call.
        let mut benign = 1usize;
        for b in &func.body.blocks {
            if let Terminator::Call { func: callee, args, .. } = &b.terminator
                && matches!(crate::generate::method_tail(callee), "index" | "index_mut")
                // CRATE-ANCHOR (round-5 audit): a `&mut` reborrow is length-benign ONLY
                // when consumed by the GENUINE `Index`/`IndexMut` trait method (which
                // never resizes — std contract). A user free fn `fn index_mut(v:&mut Vec,..)`
                // that DOES resize renders `mycrate::index_mut`; counting it "benign" would
                // suppress the resize hazard and ADMIT a stale length tie → OOB. Genuine
                // renderings carry `core::ops::`/`std::ops::` (unqualified
                // `core::ops::index::IndexMut::index_mut` or `<Vec as core::ops::index::…>`).
                && callee_is_std_ops_method(callee)
                && let Some(Operand::Copy(p) | Operand::Move(p)) = args.first()
                && p.local == t
                && p.projections.is_empty()
            {
                benign += 1;
            }
        }
        if mentions > benign {
            return true;
        }
    }
    false
}

/// One step of the base-collection trace: the whole-local `cur` defined from a
/// projection-free `Use`/`&x`/`&raw x`/`CopyForDeref`, or a length-preserving deref
/// call (`Deref::deref`/`as_slice`). `None` when `cur` is a leaf (the base itself).
fn base_collection_step(func: &VerifiableFunction, cur: usize) -> Option<usize> {
    for b in &func.body.blocks {
        for s in &b.stmts {
            let Statement::Assign { place, rvalue, .. } = s else { continue };
            if place.local != cur || !place.projections.is_empty() {
                continue;
            }
            let next = match rvalue {
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                | Rvalue::CopyForDeref(p)
                | Rvalue::Ref { place: p, .. }
                | Rvalue::AddressOf(_, p)
                    if p.projections.is_empty() =>
                {
                    Some(p.local)
                }
                // Trust (2026-07-06, `&mut Vec` length unification): a reborrow of a
                // DEREF — `_dst = &(*_src)` / `&mut (*_src)` / `&raw (*_src)` — where
                // `_src` is a REFERENCE to the container. `*_dst` and `*_src` denote the
                // SAME container, so its length is identical; trace through to `_src`.
                // This makes a `&mut Vec` receiver's `.len()` (auto-reborrowed to
                // `&(*v)` since `Vec::len` takes `&self`) and its `v[i]` resolve to the
                // SAME base local (the param `v`), so both tie to one `coll_len(v)`. SOUND:
                // a resize still reborrows `&mut (*v)`, which `local_is_mutably_borrowed`
                // (checked by the tie/recovery sites on the traced base) detects → they
                // decline → a resized Vec's guarded index stays refutable (no false-PROVE).
                Rvalue::Ref { place: p, .. } | Rvalue::AddressOf(_, p)
                    if p.projections.as_slice() == [trust_types::Projection::Deref] =>
                {
                    Some(p.local)
                }
                _ => None,
            };
            if next.is_some() {
                return next;
            }
        }
        if let Terminator::Call { func: callee, args, dest, .. } = &b.terminator
            && dest.local == cur
            && dest.projections.is_empty()
            && callee_is_length_preserving_deref(callee)
            && let Some(Operand::Copy(p) | Operand::Move(p)) = args.first()
            && p.projections.is_empty()
        {
            return Some(p.local);
        }
    }
    None
}

/// Number of WHOLE-local definitions of `local` (a projection-free `Statement::Assign`
/// or a `Call` dest) across all blocks. `> 1` means the local is conditionally merged
/// or reassigned, so its base collection — and hence its length — is AMBIGUOUS.
pub(crate) fn whole_local_def_count(func: &VerifiableFunction, local: usize) -> usize {
    let mut n = 0;
    for b in &func.body.blocks {
        for s in &b.stmts {
            if let Statement::Assign { place, .. } = s
                && place.local == local
                && place.projections.is_empty()
            {
                n += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &b.terminator
            && dest.local == local
            && dest.projections.is_empty()
        {
            n += 1;
        }
    }
    n
}

/// Trace to the base collection local, returning `None` if ANY local on the trace
/// chain (start..base inclusive) has more than one whole-local definition — i.e. is a
/// conditional merge `let v = if c { a } else { b }`. Tying a length to such a local
/// could resolve to the WRONG collection on the other branch — a false-PROVE. Used at
/// BOTH the len-tie mint site and the slice-bound length recovery so they stay in sync
/// (resolve to the same base, or both fail closed).
pub(crate) fn base_collection_local_unique(
    func: &VerifiableFunction,
    start: usize,
) -> Option<usize> {
    let mut cur = start;
    if whole_local_def_count(func, cur) > 1 {
        return None;
    }
    for _ in 0..(func.body.locals.len() + 4) {
        match base_collection_step(func, cur) {
            Some(n) if n != cur => {
                if whole_local_def_count(func, n) > 1 {
                    return None;
                }
                cur = n;
            }
            _ => return Some(cur),
        }
    }
    Some(cur)
}

/// The canonical length var for a base collection local. Trust abstracts a
/// `Vec`/`String` to an integer (its length) under the local's OWN name — the slice
/// index bound `i <= units` and the slice-ref length carriers all reference it — so
/// we tie into THAT existing var (versioned at the use site), not a fresh synthetic
/// one. (A `__coll_len` synthetic would connect `Vec::len`'s result but leave the
/// index bound's length disconnected, the exact gap that left `[slice]` unproved.)
pub(crate) fn coll_len_var(func: &VerifiableFunction, base: usize) -> Formula {
    coll_len_var_place(func, &trust_types::Place { local: base, projections: vec![] })
}

/// Trust (struct-field Vec length identity, 2026-07-08): PLACE-keyed twin of
/// [`coll_len_var`] — mints the container's abstract length var from the canonical
/// place's `place_to_var_name`. For `Place::local(l)` this is byte-identical to
/// `coll_len_var(func, l)` (same name-minting code path), so the whole-local
/// vocabulary is unchanged; a FIELD place (`(*self).history` → `self*.0`) gives
/// every fresh reborrow temp of the SAME field ONE shared length identity, which is
/// what lets a length guard through one temp discharge an index bound built through
/// another. Field-place names already participate in the overlap-union havoc
/// (`place_names_overlap`), so a Call/Drop that could touch the root versions the
/// field length var exactly like any other place fact — no staleness channel is
/// opened that whole-local names do not already have.
pub(crate) fn coll_len_var_place(func: &VerifiableFunction, base: &trust_types::Place) -> Formula {
    Formula::var_owned(crate::place_to_var_name(func, base), Sort::Int)
}

/// Trust (struct-field Vec length identity, 2026-07-08): PLACE-keyed sibling of
/// [`base_collection_local_unique`]. A whole-local trace result embeds unchanged as
/// `Place::local(leaf)`; additionally, when the traced leaf temp is a gated SHARED
/// reborrow of a struct FIELD (`_t = &((*root).f0.f1…)` with a `&root` SHARED-ref
/// root — see [`shared_stable_field_reborrow_place`] for every gate), the canonical
/// FIELD PLACE is returned instead, so `self.history.is_empty()` (one reborrow
/// temp) and `self.history[..]` (another) resolve to ONE length identity instead of
/// two disconnected per-temp vars (the pre-fix FALSE-REFUTE).
///
/// SOUNDNESS (0 false-PROVE — the key must never name two different collections,
/// and the named collection's length must be stable for the whole body):
///  * FIELDS STAY DISTINCT BY CONSTRUCTION: the key is the full projected place
///    (`(*self).0` vs `(*self).1` mint different `place_to_var_name`s), so a guard
///    on `self.a` can never discharge an index on `self.b`. The rejected "key field
///    shapes by the struct local" design — under which `if !self.a.is_empty() {
///    self.b[0] }` would falsely PROVE — is structurally impossible here.
///  * hop uniqueness: the underlying local trace already fails closed on any hop
///    with more than one whole-local definition (conditional merge / reassignment,
///    call dests included via `whole_local_def_count`).
///  * hop reseat exclusion: NO local on the trace chain may be mutably or raw
///    borrowed ([`local_is_mutably_borrowed`] — covers a `*p = other_ref` reseat
///    through a `&mut`-to-the-temp that leaves the whole-local def count at 1) nor
///    written through a projection ([`local_has_projected_write`] — covers `*t = v`
///    / projected call dests that `whole_local_def_count` does not count).
///  * root immutability & stability: the field-reborrow gates (root is a SHARED
///    reference, root storage is stable, the path is `[Deref, Field+]` only, and no
///    interior-mutability wrapper is crossed) guarantee the field place denotes ONE
///    collection whose length cannot change between guard and index. A `&mut self`
///    root — under which the field could be resized in the span — FAILS CLOSED to
///    the per-temp identity by construction (the shared-ref match declines it).
/// Every ungated shape falls back to `Place::local(leaf)` — byte-identical to the
/// existing whole-local behavior — so this helper is a strict additive extension:
/// existing callers of the LOCAL trace are untouched, and the two sides of the new
/// key (guard fact mint and index-bound recovery) share these gates by calling this
/// ONE function, which is what keeps them symmetric.
pub(crate) fn base_collection_place_unique(
    func: &VerifiableFunction,
    start: usize,
) -> Option<trust_types::Place> {
    let leaf = base_collection_local_unique(func, start)?;
    // Re-walk the deterministic step chain to collect every hop local (mirrors
    // the local-only trace exactly, so it terminates at `leaf`).
    let mut chain = vec![start];
    let mut cur = start;
    for _ in 0..(func.body.locals.len() + 4) {
        match base_collection_step(func, cur) {
            Some(n) if n != cur => {
                cur = n;
                chain.push(n);
            }
            _ => break,
        }
    }
    if cur == leaf
        && chain
            .iter()
            .all(|&l| !local_is_mutably_borrowed(func, l) && !local_has_projected_write(func, l))
        && let Some(field_place) = shared_stable_field_reborrow_place(func, leaf)
    {
        return Some(field_place);
    }
    Some(trust_types::Place::local(leaf))
}

/// The gated field-place extraction behind [`base_collection_place_unique`]:
/// `leaf`'s unique whole-local def must be a SHARED (`&`, never `&mut`/`&raw`)
/// reborrow of `(*root).f0.f1…` — a leading `Deref` followed by one or more
/// `Field`s and NOTHING else (an `Index` hop varies at runtime; a `Downcast`
/// re-views enum memory under a switchable tag; either would let one key name two
/// collections) — where the ROOT is:
///  * a SHARED reference (`Ty::Ref { mutable: false }`, the `&self` shape): the
///    borrow checker guarantees the whole pointee — the field `Vec` included — is
///    immutable while the ref is live, so the field's LENGTH is a stable bound for
///    the whole body. This is the same type-level argument
///    [`owned_container_len_var`] documents for whole-local `&Vec` receivers. A
///    `&mut self` root (resizable between guard and index) returns `None` — FAIL
///    CLOSED. (A `&mut` root that is provably never written through could be
///    admitted later; it is deliberately out of scope here.)
///  * stable storage ([`crate::place_source_is_stable`]): never reseated, never
///    projected-into, never mutably/raw-mut borrowed — so the SAME place name
///    always denotes the SAME collection. A defense-in-depth scan additionally
///    declines on ANY `&raw` of the root (`place_source_is_stable` admits the
///    `&raw const` form, and a raw pointer launders past all later checks).
///  * free of interior mutability along the field path: a shared ref does NOT
///    freeze an `UnsafeCell`-family field, so any hop whose aggregate is such a
///    wrapper declines (only reachable via privacy-bypassing/std-internal MIR, but
///    the exclusion is cheap and closes the hole outright).
fn shared_stable_field_reborrow_place(
    func: &VerifiableFunction,
    leaf: usize,
) -> Option<trust_types::Place> {
    let Rvalue::Ref { mutable: false, place } = crate::unique_whole_local_def(func, leaf)? else {
        return None;
    };
    let (first, fields) = place.projections.split_first()?;
    if !matches!(first, trust_types::Projection::Deref)
        || fields.is_empty()
        || !fields.iter().all(|pr| matches!(pr, trust_types::Projection::Field(_)))
    {
        return None;
    }
    let root = place.local;
    let root_ty = crate::place_ty_cow(func, &trust_types::Place::local(root))?;
    if !matches!(root_ty.as_ref(), Ty::Ref { mutable: false, .. }) {
        return None;
    }
    if !crate::place_source_is_stable(func, root) {
        return None;
    }
    // `place_source_is_stable` rejects `&mut root`/`&raw mut root` but admits
    // `&raw const root`; decline on any raw borrow of the root (fail closed).
    for b in &func.body.blocks {
        for s in &b.stmts {
            if let Statement::Assign { rvalue: Rvalue::AddressOf(_, ap), .. } = s
                && ap.local == root
            {
                return None;
            }
        }
    }
    // Interior-mutability walk: every aggregate a `Field` hop steps INTO must be a
    // plain immutable ADT (the leading `Deref` steps to the root pointee first).
    let mut cur = crate::step_place_ty_cow(root_ty, first)?;
    for pr in fields {
        if ty_is_interior_mut_wrapper(cur.as_ref()) {
            return None;
        }
        cur = crate::step_place_ty_cow(cur, pr)?;
    }
    Some(place.clone())
}

/// ADT name-tail of an interior-mutability wrapper — a shared `&` does NOT make its
/// contents immutable, so the field-place key's stability argument does not survive
/// crossing one. Matched on the generic-stripped path tail, consistent with
/// `is_owned_slice_container_name`.
fn ty_is_interior_mut_wrapper(ty: &Ty) -> bool {
    let Ty::Adt { name, .. } = ty else { return false };
    let base = name.split('<').next().unwrap_or(name);
    let tail = base.rsplit("::").next().unwrap_or(base).trim();
    matches!(
        tail,
        "UnsafeCell"
            | "SyncUnsafeCell"
            | "Cell"
            | "RefCell"
            | "OnceCell"
            | "LazyCell"
            | "Mutex"
            | "RwLock"
            | "OnceLock"
            | "LazyLock"
    )
}

/// Any store through a PROJECTION of `local` (`(*l).f = v`, `l.f = v`, a projected
/// call dest, `SetDiscriminant`/`Deinit`) — writes `whole_local_def_count` does NOT
/// count, but which can change what a place rooted at (or reborrowed from) `local`
/// denotes. Used by [`base_collection_place_unique`] to fail closed on
/// reseat-through-deref of a trace-chain temp.
fn local_has_projected_write(func: &VerifiableFunction, local: usize) -> bool {
    for b in &func.body.blocks {
        for s in &b.stmts {
            match s {
                Statement::Assign { place, .. }
                | Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place } => {
                    if place.local == local && !place.projections.is_empty() {
                        return true;
                    }
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &b.terminator
            && dest.local == local
            && !dest.projections.is_empty()
        {
            return true;
        }
    }
    false
}

/// Trust: `slice.last()/.first()` (and `_mut`) returns `Some` IFF the collection is
/// NON-EMPTY. In the `Some`-discriminant arm of `match coll.last() { Some(..) => .. }`
/// the collection has `len >= 1`, which discharges the ubiquitous `coll.len() - 1`
/// (underflow) the verifier otherwise FALSE-REFUTES (it never connects the Some-arm
/// to the length, and Trust has no unified Vec length model). We mint a canonical
/// `{base}__coll_len`: (a) define EVERY `_len = Y.len()` as `_len == coll_len(base(Y))`
/// (always true), and (b) seed `coll_len(base) >= 1` at the Some-target block (true
/// only there), which the path-def fixpoint propagates forward to the `len()` site.
/// Sound: receivers are traced to the SAME base collection (a `.len()` on a DIFFERENT
/// collection ties to its own var), and a mutably-borrowed (resizable) base is
/// skipped (its length could change between the `last()` and the use).
pub(crate) fn slice_last_some_nonempty_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let blocks = &func.body.blocks;

    let mut last_opt_base: FxHashMap<usize, trust_types::Place> = FxHashMap::default();
    for b in blocks {
        let Terminator::Call { func: callee, args, dest, target, .. } = &b.terminator else {
            continue;
        };
        if !dest.projections.is_empty() {
            continue;
        }
        let Some(Operand::Copy(p) | Operand::Move(p)) = args.first() else { continue };
        if !p.projections.is_empty() {
            continue;
        }
        // Unique-definition trace: a conditionally-merged receiver (`v = if c {a} else
        // {b}`) has an ambiguous base, so tying its length to one branch's collection
        // would be unsound — decline (no coll_len minted). Must match the slice-bound
        // recovery's tracer (`collection_abstract_len_with_base`) so they stay synced.
        // Trust (struct-field Vec length identity, 2026-07-08): the trace is
        // PLACE-keyed — a whole-local receiver keys byte-identically to before
        // (`Place::local(leaf)`), while a gated shared-field reborrow receiver
        // (`_len = self.history.len()` under a `&self` root) ties to the canonical
        // FIELD place's var: the SAME var the guard fact (`owned_container_len_var`)
        // and the index bound (`collection_abstract_len_with_base_opts`) mint —
        // closing the `self.history[self.history.len() - 1]` false-refute (the
        // `_len - 1` underflow and the index bound both need `_len == coll_len`).
        let Some(base) = base_collection_place_unique(func, p.local) else { continue };
        match crate::generate::method_tail(callee) {
            // CRATE-ANCHOR (round-5 false-proof close): `first`/`last`(`_mut`) are
            // INHERENT `[T]` methods (a `Vec`/array receiver derefs to the slice, so the
            // genuine callee is `core::slice::<impl [T]>::first` etc.). A user free fn
            // `fn first(v:&Vec<i32>)->Option<i32>{Some(0)}` renders `mycrate::first` and is
            // DECLINED — else its `Some` in the match arm seeds `coll_len >= 1` and
            // discharges `v[0]` on an actually-empty collection (OOB).
            "last" | "first" | "last_mut" | "first_mut"
                if callee_is_std_slice_inherent(
                    callee,
                    &["::last", "::first", "::last_mut", "::first_mut"],
                ) =>
            {
                last_opt_base.insert(dest.local, base);
            }
            // `_len = Y.len()` is a Call whose result is live in the RETURN target;
            // tie it there (NOT in this block, where `_len` is not yet defined and the
            // var would version-mismatch the eventual `_len - 1` use site). SOUND only
            // when the base's LENGTH is stable — otherwise two `.len()` calls
            // straddling a resize (`a=v.len(); v.push(x); b=v.len()`) would both tie to
            // one `coll_len` and falsely force `a == b`. Length-benign `&mut` reborrows
            // (`index_mut` receivers — the `v[i] = x` write idiom) never resize, so
            // they keep the tie; MUST stay synced with the recovery gate
            // (`collection_abstract_len_with_base_opts`), else a guarded write would
            // emit its bounds VC without the `_len == coll_len` fact and false-refute.
            // CRATE-ANCHOR (round-5 false-proof close): only a GENUINE std container
            // `len` mints the `_len == coll_len(base)` tie. A user free fn
            // `fn len(v:&Vec<i32>)->usize{1_000_000}` renders `mycrate::len` and is
            // DECLINED by the shared `total_summary_len_bound` matcher — else the tie ties
            // the container's abstract length var to a forged huge value → discharges
            // `v[k]` for a large `k` (OOB). `total_summary_len_bound` is the same
            // doctrine matcher the VC len-bound producer uses (generate.rs), so mint and
            // recovery cannot drift; it rejects the same-prefixed impostors
            // (`std::vec::VecEvil::len`, `core::slice::Iter::len`) too.
            "len"
                if trust_types::total_call_summaries::total_summary_len_bound(callee)
                    && coll_base_len_stable(func, &base) =>
            {
                let Some(tgt) = target else { continue };
                let dest_var = Formula::var_owned(
                    crate::place_to_var_name(
                        func,
                        &trust_types::Place { local: dest.local, projections: vec![] },
                    ),
                    Sort::Int,
                );
                out.entry(*tgt).or_default().push(Formula::Eq(
                    Box::new(dest_var),
                    Box::new(coll_len_var_place(func, &base)),
                ));
            }
            _ => {}
        }
    }
    // UNGATE: keep the accumulated `_len == coll_len(base)` ties even when there is no
    // last()/first() — they connect a `k <= v.len()` guard to the slice-bound recovery
    // so guarded owned-Vec indexing PROVES. The non-emptiness `Ge(coll_len,1)` loop
    // below is a structural no-op when `last_opt_base` is empty, so this leaks no
    // non-emptiness fact. (The ties are true facts — `v.len()` IS the abstract length
    // for a uniquely-traced, non-mut-borrowed base — so they cannot cause a false-PROVE.)
    if last_opt_base.is_empty() {
        return out;
    }

    for b in blocks {
        let Terminator::SwitchInt { discr, targets, .. } = &b.terminator else { continue };
        let Some(d_local) = operand_bare_local(discr) else { continue };
        let mut opt_local = None;
        for s in &b.stmts {
            if let Statement::Assign { place: p, rvalue: Rvalue::Discriminant(src), .. } = s
                && p.local == d_local
                && p.projections.is_empty()
                && src.projections.is_empty()
            {
                opt_local = Some(src.local);
            }
        }
        let Some(opt_local) = opt_local else { continue };
        let Some(base) = last_opt_base.get(&opt_local) else { continue };
        // Length-stability gate (same refinement as the len-tie arm above): a
        // non-emptiness fact `coll_len >= 1` survives length-benign `index`/
        // `index_mut` reborrows; a genuine resize still declines it.
        if !coll_base_len_stable(func, base) {
            continue;
        }
        let Some(some_bb) = targets.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t) else {
            continue;
        };
        out.entry(some_bb)
            .or_default()
            .push(Formula::Ge(Box::new(coll_len_var_place(func, base)), Box::new(Formula::Int(1))));
    }
    out
}

/// Length-stability gate for a traced base KEY. A WHOLE-LOCAL key keeps the exact
/// [`local_mut_borrows_may_resize`] refinement it had before the place-keying (a
/// length-benign `index`/`index_mut` reborrow keeps the tie; a genuine resize
/// declines) — byte-identical behavior. A FIELD-PLACE key was already proven
/// length-stable BY CONSTRUCTION when it was minted: [`base_collection_place_unique`]
/// only returns a projected place under a SHARED, stable root, and while a `&self`
/// is live no `&mut` to the field (hence no resize) can coexist — so it passes
/// unconditionally. Keeping the gate derived from the KEY (not re-derived ad hoc at
/// each site) keeps the mint sites and the recovery sites in sync — the same
/// stay-synced requirement the local gate documents.
fn coll_base_len_stable(func: &VerifiableFunction, base: &trust_types::Place) -> bool {
    if base.projections.is_empty() { !local_mut_borrows_may_resize(func, base.local) } else { true }
}

/// Trust (R2 corpus family 2 — get-Some index bound): `slice.get(idx) == Some(..)`
/// implies `idx < slice.len()` — the `<[T]>::get` CONTRACT. In the `Some`-arm of
/// `while let Some(x) = flags.get(idx) { idx += 1; … }` (bitflags `IterNames::next`,
/// semver `numeric_identifier`) the increment `idx + 1` cannot overflow: the seeded
/// `idx < {recv}__slice_len` plus the allocation-size axiom
/// (`conjoin_slice_len_bounds`: `len <= isize::MAX` for non-ZST elements) bound it
/// away from `usize::MAX`. Without this fact the verifier FALSE-REFUTES the most
/// common get-guarded scan loops in battle-tested crates.
///
/// SOUNDNESS (each gate prevents a concrete false proof):
///  * callee anchored to `core::slice::`/`std::slice::` + tail `get` — a user
///    `MyColl::get` with different semantics never matches;
///  * the receiver arg must be a SHARED `&[T]`/`&[T; N]` (`Ref { mutable: false }`)
///    and the index a by-value unsigned integer — so the CALLEE provably cannot
///    mutate the index source or the collection (the call-arg `&mut`-staleness
///    channel, hunt-5/7/w0z class);
///  * the fact is seeded ONLY at the `Some`-discriminant target of a switch in the
///    call's DIRECT target block, which must contain no assignment other than the
///    discriminant read of the call dest — no path from the call to the seed block
///    can rewrite the index;
///  * downstream staleness (`idx += 1`, `self.flags = shorter`) is handled by the
///    consumers: `v2_live_path_defs` drops the fact in any block that redefines one
///    of its variables, and the path-def fixpoint kills it across redefining paths
///    (the S2c version rename makes a surviving stale copy name-disjoint);
///  * a traced copy source (`_t = Copy((*self).idx)` feeding `get(.., _t)`) is only
///    credited when that copy is IN the call block with no later same-block write
///    overlapping the source base — the fact then names the value the call actually
///    read (in reality unchanged across the call: the callee has no mutable access,
///    see the shared-receiver gate).
///
/// The facts are TRUE point-invariants of the Some arm; a dropped/killed fact only
/// costs precision (a false-FAIL at worst), never soundness.
pub(crate) fn slice_get_some_index_bound_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let blocks = &func.body.blocks;

    for b in blocks {
        // `_opt = <[T]>::get(recv, idx)` terminating this block.
        let Terminator::Call { func: callee, args, dest, target: Some(target), .. } = &b.terminator
        else {
            continue;
        };
        if !dest.projections.is_empty() || args.len() != 2 {
            continue;
        }
        if crate::generate::method_tail(callee) != "get"
            || !(callee.starts_with("core::slice::") || callee.starts_with("std::slice::"))
        {
            continue;
        }
        // Receiver: a SHARED reference to a slice / fixed array. This is both the
        // length-model gate and the no-mutable-access gate (see the doc comment).
        let recv = &args[0];
        let recv_shared_slice = matches!(
            operand_ty(func, recv).as_ref(),
            Some(Ty::Ref { mutable: false, inner })
                if matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. })
        );
        if !recv_shared_slice {
            continue;
        }
        let Some(len_f) = slice_len_formula(func, recv) else { continue };
        // Index: a by-value UNSIGNED integer (`usize`). A range-typed `get(a..b)` or
        // any non-integer index is skipped — its "value" has no Int-sorted meaning.
        let idx = &args[1];
        let idx_is_unsigned_int =
            matches!(operand_ty(func, idx).as_ref(), Some(Ty::Int { signed: false, .. }));

        // The call's DIRECT target must read the discriminant of `dest` and switch on
        // it, with no other assignment in between (mirror the demux `j_clean` gate).
        let Some(tb) = blocks.get(target.0).filter(|tb| tb.id == *target) else { continue };
        let mut disc_local: Option<usize> = None;
        let mut clean = true;
        for s in &tb.stmts {
            match s {
                Statement::Assign { place, rvalue, .. } if place.projections.is_empty() => {
                    if let Rvalue::Discriminant(src) = rvalue
                        && src.projections.is_empty()
                        && src.local == dest.local
                    {
                        disc_local = Some(place.local);
                    } else {
                        clean = false;
                        break;
                    }
                }
                _ => {
                    clean = false;
                    break;
                }
            }
        }
        if !clean {
            continue;
        }
        let Some(disc_local) = disc_local else { continue };
        let Terminator::SwitchInt { discr, targets, .. } = &tb.terminator else { continue };
        if operand_bare_local(discr) != Some(disc_local) {
            continue;
        }
        // `Option::Some` is variant 1.
        let Some(some_bb) = targets.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t) else {
            continue;
        };

        let mut facts: Vec<Formula> = Vec::new();
        match idx {
            Operand::Constant(ConstValue::Uint(v, _)) => {
                facts
                    .push(Formula::Lt(Box::new(Formula::Int(*v as i128)), Box::new(len_f.clone())));
            }
            Operand::Copy(p) | Operand::Move(p) if idx_is_unsigned_int => {
                // Only Deref/Field projections keep a stable, version-renameable
                // place name (an Index projection embeds another local's value).
                let stable_place = p.projections.iter().all(|pr| {
                    matches!(pr, trust_types::Projection::Deref | trust_types::Projection::Field(_))
                });
                if stable_place {
                    facts.push(Formula::Lt(
                        Box::new(Formula::var_owned(crate::place_to_var_name(func, p), Sort::Int)),
                        Box::new(len_f.clone()),
                    ));
                }
                // Trace one Use-copy: `_t = Copy(src); … get(recv, _t)` — credit the
                // SOURCE place too (the overflowing `self.idx + 1` reads the FIELD,
                // not the arg temp). Gated: the copy must be in the CALL block with
                // no later same-block write overlapping the source base.
                if p.projections.is_empty()
                    && whole_local_def_count(func, p.local) == 1
                    && let Some((src_stmt_idx, src)) =
                        b.stmts.iter().enumerate().find_map(|(i, s)| match s {
                            Statement::Assign {
                                place,
                                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                                ..
                            } if place.local == p.local && place.projections.is_empty() => {
                                Some((i, src))
                            }
                            _ => None,
                        })
                    && src.projections.iter().all(|pr| {
                        matches!(
                            pr,
                            trust_types::Projection::Deref | trust_types::Projection::Field(_)
                        )
                    })
                    && !b.stmts.iter().skip(src_stmt_idx + 1).any(|s| {
                        matches!(
                            s,
                            Statement::Assign { place, .. } if place.local == src.local
                        )
                    })
                {
                    facts.push(Formula::Lt(
                        Box::new(Formula::var_owned(
                            crate::place_to_var_name(func, src),
                            Sort::Int,
                        )),
                        Box::new(len_f.clone()),
                    ));
                }
            }
            _ => {}
        }
        if !facts.is_empty() {
            out.entry(some_bb).or_default().extend(facts);
        }
    }
    out
}

pub(crate) fn enum_construction_demux_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let blocks = &func.body.blocks;
    let preds = block_predecessors(func);

    for (j_idx, j_block) in blocks.iter().enumerate() {
        let j = BlockId(j_idx);
        // J ends in a SwitchInt on a discriminant temp defined within J itself.
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &j_block.terminator else {
            continue;
        };
        let Some(d_local) = operand_bare_local(discr) else {
            continue;
        };
        // Locate `d = Discriminant(place)` and require J assigns ONLY `d` (no
        // statement may clobber `place` or a payload operand before the switch).
        let mut place_local: Option<usize> = None;
        let mut j_clean = true;
        for stmt in &j_block.stmts {
            match stmt {
                Statement::Assign { place: p, rvalue, .. } => {
                    if p.local != d_local || !p.projections.is_empty() {
                        j_clean = false;
                        break;
                    }
                    if let Rvalue::Discriminant(src) = rvalue
                        && src.projections.is_empty()
                    {
                        place_local = Some(src.local);
                    }
                }
                Statement::SetDiscriminant { .. } | Statement::Deinit { .. } => {
                    j_clean = false;
                    break;
                }
                _ => {}
            }
        }
        if !j_clean {
            continue;
        }
        let Some(place_local) = place_local else {
            continue;
        };

        // SOUNDNESS (P0 false proof, 2026-06-17 hunt-7): if the enum local is mutably borrowed
        // anywhere — `&mut o` / `&raw mut o`, OR a call taking `&mut o` such as `o.as_mut()` —
        // its payload can be REASSIGNED after construction (`if let Some(r) = o.as_mut() { *r = b; }`
        // then `match o { Some(i) => arr[i] }`), so routing the CONSTRUCTION-time payload fact
        // `o@field == V` into the match arm is STALE and vacuously discharges a bounds/overflow
        // obligation on the mutated payload (`arr[i]` PROVED in-bounds while `i` became `b`). The
        // demux re-injects the fact past the normal mutable-borrow kill, so guard it HERE. (The
        // mutating `&mut o` materializes as a `Ref{mutable:true}` statement even for `o.as_mut()`.)
        if local_is_mutably_borrowed(func, place_local) {
            continue;
        }

        // Every predecessor of J must be a single-pred `Goto(J)` block whose
        // whole-`place` assignment is an ADT aggregate. Collect payload facts per
        // variant; bail on any non-conforming predecessor, and disable any variant
        // built by more than one predecessor (its payload is not unique).
        let j_preds = &preds[j_idx];
        if j_preds.len() < 2 {
            continue;
        }
        let mut by_variant: FxHashMap<usize, Vec<Formula>> = FxHashMap::default();
        let mut duplicate_variants: FxHashSet<usize> = FxHashSet::default();
        let mut all_conform = true;
        for &p in j_preds {
            let pb = &blocks[p.0];
            // Payload routing needs every J-predecessor to be a `Goto(J)` block that
            // overwrites `place` wholesale (the construction check below). P_k's OWN
            // predecessor count is irrelevant to payload soundness: the payload fact
            // is P_k's own aggregate, valid whenever P_k runs, and reaching the arm
            // implies P_k ran (variant uniqueness). Guard routing, which DOES need a
            // unique incoming edge, gates on `preds[p.0].len() == 1` separately below.
            // Requiring single-pred here would wrongly bail whole joins like `flag_some`
            // whose None constructor is shared by the flag-false and guard-false paths.
            let is_construction_arm = matches!(&pb.terminator, Terminator::Goto(t) if *t == j);
            if !is_construction_arm {
                all_conform = false;
                break;
            }
            // Last whole-`place` ADT aggregate assignment in the block.
            let mut construction: Option<(usize, AggregateKind, usize)> = None;
            for stmt in &pb.stmts {
                if let Statement::Assign { place: p2, rvalue: Rvalue::Aggregate(kind, ops), .. } =
                    stmt
                    && p2.local == place_local
                    && p2.projections.is_empty()
                    && let AggregateKind::Adt { variant, active_field: None, .. } = kind
                {
                    construction = Some((*variant, kind.clone(), ops.len()));
                }
            }
            let Some((variant, kind, arity)) = construction else {
                all_conform = false;
                break;
            };
            // The variant-downcast payload field names this construction defines.
            let synth = trust_types::Place { local: place_local, projections: vec![] };
            let expected: FxHashSet<String> = (0..arity)
                .filter_map(|i| crate::aggregate_variant_field_place(&synth, &kind, i))
                .map(|fp| crate::place_to_var_name(func, &fp))
                .collect();
            // Source the equalities from the block's own definitions so the
            // existing last-write / operand-clobber discipline already applies.
            let block_defs = extract_block_definitions(func, pb);
            let top_facts: Vec<Formula> = block_defs
                .iter()
                .filter(|f| match f {
                    Formula::Eq(lhs, _) => lhs.var_name().is_some_and(|n| expected.contains(n)),
                    _ => false,
                })
                .cloned()
                .collect();
            // (nested aggregate payloads): a tuple/struct-valued payload
            // field — `Some((a, b))` builds `_t = (a, b); place = Some(_t)` — routes
            // only the whole-aggregate equality `place@1.0 == _t`, but a destructuring
            // arm `Some((x, _))` reads the nested leaf `place@1.0.0`. Rewrite each
            // aggregate-valued payload equality into its leaf equalities by renaming
            // the temp's own field defs (`_t.0 == a` ⇒ `place@1.0.0 == a`). The
            // children come from `block_defs`, which already dropped any stale-operand
            // fact, so the leaves inherit that discipline; the rewrite is purely
            // additive (the whole-aggregate equality is kept) and each leaf is a
            // genuinely-true congruence consequence, hence monotone-safe.
            let facts = expand_nested_payload_facts(top_facts, &block_defs);
            // (guard routing): when P_k has a UNIQUE predecessor Q, every
            // path reaching this arm traverses the Q→P_k edge (the de-mux proves the
            // arm is reachable only via this unique variant-k constructor, and P_k is
            // entered only from Q), so that edge's guard is TRUE at the arm. Route the
            // resolved guard (e.g. `v < 100`) alongside the payload. The path-guard
            // enumerator instead weakens this guard under a disjunction with the
            // infeasible other-variant→arm path, which is exactly why it must be routed
            // here as an unconditional arm fact. Soundness: a genuinely-true fact, and
            // the clobber check drops it if P_k or J reassigns any of its free
            // variables (the arm's own reassignments are dropped later by
            // v2_live_path_defs) — so it can only turn a false-FAIL into a PROVE for
            // safe code, never make a real overflow PROVE.
            let mut guard_facts: Vec<Formula> = Vec::new();
            if let [q] = preds[p.0].as_slice() {
                let q_block = &blocks[q.0];
                let mut matching: Vec<Formula> = q_block
                    .terminator
                    .discovered_clauses(*q)
                    .into_iter()
                    .filter(|c| c.target == trust_types::ClauseTarget::Block(p))
                    .map(|c| guard_to_formula(func, &c.guard))
                    .filter(|gf| !matches!(gf, Formula::Bool(true)))
                    .collect();
                // Exactly one routable edge guard, else fail-closed: multiple clauses
                // (e.g. `0 | 1 => P_k`) would conjoin to a contradiction.
                if matching.len() == 1 {
                    let gf = matching.remove(0);
                    let clobbered = guard_edge_clobbered_names(func, pb, j_block);
                    if gf.free_variables().iter().all(|fv| !name_clobbered(fv, &clobbered)) {
                        guard_facts.push(gf);
                    }
                }
            }
            if by_variant.contains_key(&variant) {
                duplicate_variants.insert(variant);
            }
            let entry = by_variant.entry(variant).or_default();
            entry.extend(facts);
            entry.extend(guard_facts);
        }
        if !all_conform {
            continue;
        }
        for v in &duplicate_variants {
            by_variant.remove(v);
        }
        if by_variant.is_empty() {
            continue;
        }

        // Route each variant's payload facts to the arm that downcasts `place` to
        // that variant. Eligible arms have J as sole predecessor and do not
        // themselves reassign `place`.
        let mut arm_targets: Vec<BlockId> =
            targets.iter().map(|(_, t)| *t).chain(std::iter::once(*otherwise)).collect();
        arm_targets.sort_by_key(|b| b.0);
        arm_targets.dedup();
        for arm in arm_targets {
            if arm.0 >= blocks.len() || preds[arm.0].as_slice() != [j] {
                continue;
            }
            let arm_block = &blocks[arm.0];
            if block_assigns_local(arm_block, place_local) {
                continue;
            }
            for variant in arm_downcast_variants(arm_block, place_local) {
                if let Some(facts) = by_variant.get(&variant) {
                    out.entry(arm).or_default().extend(facts.iter().cloned());
                }
            }
        }
    }
    out
}

/// The bare local of a projection-less `Copy`/`Move` operand, else `None`.
fn operand_bare_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// True if any statement writes a place rooted at `local` (whole-local or any
/// field/discriminant of it) — a write that would invalidate a routed payload
/// fact about that local.
fn block_assigns_local(block: &BasicBlock, local: usize) -> bool {
    block.stmts.iter().any(|s| match s {
        Statement::Assign { place, .. }
        | Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place } => place.local == local,
        _ => false,
    })
}

/// Whole-local var-names written (assignments, set-discriminant, deinit, call
/// destinations) by `pk` or `j`. A routed edge guard whose free variables touch
/// any of these is stale by the time control reaches the arm. Every written place
/// is reduced to its WHOLE-local name so a field write (`opt.0 = …`) still records
/// the base local — `name_clobbered` then catches field/whole-local aliasing.
fn guard_edge_clobbered_names(
    func: &VerifiableFunction,
    pk: &BasicBlock,
    j: &BasicBlock,
) -> FxHashSet<String> {
    let mut locals: FxHashSet<usize> = FxHashSet::default();
    for block in [pk, j] {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, .. }
                | Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place } => {
                    locals.insert(place.local);
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator {
            locals.insert(dest.local);
        }
    }
    locals
        .into_iter()
        .map(|l| {
            crate::place_to_var_name(func, &trust_types::Place { local: l, projections: vec![] })
        })
        .collect()
}

/// True if free-variable name `fv` aliases any written whole-local name in
/// `clobbered`: either an exact match, or `fv` is a field/projection of a written
/// local (`w` followed by a projection char). Written names are clean base locals
/// (source identifier or `_N`, no projection chars), so prefix matching is exact.
fn name_clobbered(fv: &str, clobbered: &FxHashSet<String>) -> bool {
    clobbered.iter().any(|w| {
        fv == w
            || (fv.len() > w.len()
                && fv.starts_with(w.as_str())
                && matches!(fv.as_bytes()[w.len()], b'.' | b'@' | b'[' | b'*'))
    })
}

/// True if var-name `child` is a strict field/projection of `parent` — `parent`
/// followed by a projection separator (`.`, `@`, `[`, `*`). `_t.0` is a child of
/// `_t`; `_t0` is not (`0` is not a separator).
fn is_strict_field_child(child: &str, parent: &str) -> bool {
    child.len() > parent.len()
        && child.starts_with(parent)
        && matches!(child.as_bytes()[parent.len()], b'.' | b'@' | b'[' | b'*')
}

/// Expand aggregate-valued payload equalities into their leaf equalities so a
/// nested `match`-arm read of a constructed tuple/struct payload is constrained.
///
/// `Some((a, b))` lowers to `_t = (a, b); place = Some(_t)`, so the routed payload
/// fact is the whole-aggregate `place@1.0 == _t` while the arm `Some((x, _))` reads
/// the leaf `place@1.0.0`. A fact's RHS is an aggregate exactly when `block_defs`
/// holds field children `_t.J == …` for its RHS name; rename the `_t` prefix to the
/// payload-field name (`place@1.0`) to obtain `place@1.0.J == …`, and re-queue each
/// leaf so nested aggregates expand fully.
///
/// Purely additive: every input fact is kept and leaves are appended. Each leaf is
/// a genuinely-true congruence consequence of the kept whole-aggregate equality and
/// the temp's field def — and the field def already passed `block_defs`'
/// stale-operand discipline, so a leaf whose source was dropped as stale is never
/// produced. Monotone-safe: it can turn a false-FAIL into a PROVE for safe code but
/// can never make a real overflow PROVE.
fn expand_nested_payload_facts(top_facts: Vec<Formula>, block_defs: &[Formula]) -> Vec<Formula> {
    let mut out: Vec<Formula> = Vec::new();
    let mut work: Vec<(Formula, usize)> = top_facts.into_iter().map(|f| (f, 0usize)).collect();
    while let Some((f, depth)) = work.pop() {
        // Depth cap is a belt-and-braces guard; the def chain is acyclic (each temp
        // is built before use within the block), so expansion terminates anyway.
        if depth < 8
            && let Formula::Eq(lhs, rhs) = &f
            && let Some(lhs_name) = lhs.var_name()
            && let Some(rhs_name) = rhs.var_name()
        {
            for d in block_defs {
                let Formula::Eq(cl, cr) = d else { continue };
                let Some(cname) = cl.var_name() else { continue };
                if is_strict_field_child(cname, rhs_name) {
                    let suffix = &cname[rhs_name.len()..];
                    let sort = cl.var_sort().cloned().unwrap_or(Sort::Int);
                    work.push((
                        Formula::Eq(
                            Box::new(Formula::Var(format!("{lhs_name}{suffix}"), sort)),
                            cr.clone(),
                        ),
                        depth + 1,
                    ));
                }
            }
        }
        out.push(f);
    }
    out
}

/// Variant indices that `block` downcasts `target_local` to (across every place
/// read or written by its assignments).
fn arm_downcast_variants(block: &BasicBlock, target_local: usize) -> FxHashSet<usize> {
    let mut out = FxHashSet::default();
    for stmt in &block.stmts {
        if let Statement::Assign { place, rvalue, .. } = stmt {
            push_place_downcasts(place, target_local, &mut out);
            rvalue_place_downcasts(rvalue, target_local, &mut out);
        }
    }
    out
}

fn push_place_downcasts(
    place: &trust_types::Place,
    target_local: usize,
    out: &mut FxHashSet<usize>,
) {
    if place.local != target_local {
        return;
    }
    for proj in &place.projections {
        if let trust_types::Projection::Downcast(v) = proj {
            out.insert(*v);
        }
    }
}

fn rvalue_place_downcasts(rvalue: &Rvalue, target_local: usize, out: &mut FxHashSet<usize>) {
    fn vop(op: &Operand, target_local: usize, out: &mut FxHashSet<usize>) {
        if let Operand::Copy(p) | Operand::Move(p) = op {
            push_place_downcasts(p, target_local, out);
        }
    }
    match rvalue {
        Rvalue::Use(o) | Rvalue::UnaryOp(_, o) | Rvalue::Cast(o, _) | Rvalue::Repeat(o, _) => {
            vop(o, target_local, out)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            vop(a, target_local, out);
            vop(b, target_local, out);
        }
        Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
            for o in ops {
                vop(o, target_local, out);
            }
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => push_place_downcasts(place, target_local, out),
        _ => {}
    }
}

/// Trust: the FREE base array term for the McCarthy array-theory channel —
/// `arr$local$base`, an unconstrained `(Array Int elem)`. Element positions not
/// pinned by a construction store read as unconstrained from it (sound).
fn array_free_base(local: usize, elem: &Sort) -> Formula {
    Formula::Var(
        format!("arr${local}$base"),
        Sort::Array(Box::new(Sort::Int), Box::new(elem.clone())),
    )
}

/// Trust: seed equality for `[e0, e1, .., eN-1]` construction of array-theory
/// local `local`: `v0 == Store(.. Store(FREE_base, 0, e0) .., N-1, eN-1)`.
fn array_construction_seed(
    func: &VerifiableFunction,
    local: usize,
    elem: &Sort,
    operands: &[Operand],
    read_ctx: &ArrayReadCtx<'_>,
) -> Option<Formula> {
    let mut acc = array_free_base(local, elem);
    for (i, op) in operands.iter().enumerate() {
        let value = operand_to_formula_with_array_ctx(func, op, Some(read_ctx));
        acc = Formula::Store(Box::new(acc), Box::new(Formula::Int(i as i128)), Box::new(value));
    }
    Some(Formula::Eq(Box::new(crate::array_term_var(local, 0, elem.clone())), Box::new(acc)))
}

/// Trust: seed equality for `[op; count]` construction. For `count <= 64` build a
/// finite Store chain pinning every position to `op`; for larger `count` leave
/// `v0` as the FREE base (sound — reads are then unconstrained, a false-FAIL).
fn array_repeat_seed(
    func: &VerifiableFunction,
    local: usize,
    elem: &Sort,
    op: &Operand,
    count: usize,
    read_ctx: &ArrayReadCtx<'_>,
) -> Option<Formula> {
    let base = array_free_base(local, elem);
    if count > 64 {
        return Some(Formula::Eq(
            Box::new(crate::array_term_var(local, 0, elem.clone())),
            Box::new(base),
        ));
    }
    let value = operand_to_formula_with_array_ctx(func, op, Some(read_ctx));
    let mut acc = base;
    for i in 0..count {
        acc = Formula::Store(
            Box::new(acc),
            Box::new(Formula::Int(i as i128)),
            Box::new(value.clone()),
        );
    }
    Some(Formula::Eq(Box::new(crate::array_term_var(local, 0, elem.clone())), Box::new(acc)))
}

fn aggregate_field_definitions(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    kind: &AggregateKind,
    operands: &[Operand],
) -> Vec<(String, Formula)> {
    operands
        .iter()
        .enumerate()
        .flat_map(|(index, operand)| {
            let value_formula = operand_to_formula(func, operand);
            // Trust: a field write produces up to two equalities under different
            // naming conventions. The struct-style place `o.<i>` matches a struct
            // field read; the variant-downcast place `o@<v>.<i>` matches an enum
            // `match`-arm payload read (`(o as Some).0`). `AggregateKind::Adt`
            // cannot distinguish struct from enum, so emit whichever apply — a
            // local has a single type, so exactly one name is ever read; the
            // other is a dangling equality on a fresh variable that appears in no
            // obligation (sound: it can neither false-prove nor false-fail; the
            // discriminant lives in the separate `discr_` namespace). Fixes the
            // previously unconstrained enum payload that let the solver pick an
            // overflowing value for `let o = Some(7); match o { Some(v) => v + 1 }`.
            let mut defs = Vec::with_capacity(2);
            if let Some(field_place) =
                crate::aggregate_field_place(place, kind, index, operands.len())
            {
                let field_name = crate::place_to_var_name(func, &field_place);
                let field_formula = operand_to_formula(func, &Operand::Copy(field_place));
                defs.push((
                    field_name,
                    Formula::Eq(Box::new(field_formula), Box::new(value_formula.clone())),
                ));
            }
            if let Some(field_place) = crate::aggregate_variant_field_place(place, kind, index) {
                let field_name = crate::place_to_var_name(func, &field_place);
                let field_formula = operand_to_formula(func, &Operand::Copy(field_place));
                defs.push((
                    field_name,
                    Formula::Eq(Box::new(field_formula), Box::new(value_formula)),
                ));
            }
            defs
        })
        .collect()
}

fn cast_definition_formula(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    op: &Operand,
    to_ty: &Ty,
) -> Option<Formula> {
    let from_ty = operand_ty(func, op)?;
    if matches!(&from_ty, Ty::Bool) && to_ty.is_integer() {
        return Some(bool_to_int_formula(func, op));
    }

    if crate::is_callable_reification_cast(&from_ty, to_ty) {
        return Some(callable_reification_formula(func, dest, to_ty));
    }

    if crate::is_modeled_identity_cast(&from_ty, to_ty) {
        return Some(operand_to_formula(func, op));
    }

    // Constant value-preserving int->int cast: `dest = (k as T)` where the OPERAND is a
    // concrete integer constant `k` representable in T equals k EXACTLY (no truncation,
    // no signed/unsigned wrap), so `dest == k` is an unconditional theorem of this
    // statement. Rust lowers a literal shift amount as `_t = (const K_i32 as u32)` — a
    // same-width signed->unsigned reinterpret that `is_modeled_identity_cast` SOUNDLY
    // declines for a symbolic source (negatives wrap) — so without this fact `_t` is a
    // free var and the provably-in-range shift-overflow boundary (`_t < W`) FALSE-refutes
    // a safe constant shift (`x << 16`, `n >> 18`, `high << 4`). We return the VALUE; the
    // caller wraps it in `Eq(dest, value)` like every other branch.
    //
    // SOUND: gated on a CONSTANT operand whose exact value is representable in the
    // destination integer type. A symbolic source, a non-integer dest, or a truncating
    // constant (`300_i32 as u8`, `-5_i32 as u32`) declines and the def is dropped —
    // fail-closed: a missing hypothesis can only cause a false-FAIL, never a false-PROVE.
    if from_ty.is_integer() {
        if let Ty::Int { width, signed } = to_ty {
            let w = *width;
            let k = match op {
                Operand::Constant(ConstValue::Int(v)) => Some(*v),
                Operand::Constant(ConstValue::Uint(v, _)) if *v <= i128::MAX as u128 => {
                    Some(*v as i128)
                }
                _ => None,
            };
            if let Some(k) = k {
                let (to_min, to_max) = if *signed {
                    if w >= 128 {
                        (i128::MIN, i128::MAX)
                    } else {
                        (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1)
                    }
                } else if w < 128 {
                    (0i128, (1i128 << w) - 1)
                } else {
                    (0i128, i128::MAX)
                };
                if k >= to_min && k <= to_max {
                    return Some(Formula::Int(k));
                }
            }
        }
    }

    // Trust: enum-disc-index cast `_d = (e_disc as usize)` — re-emit the dropped
    // `index == disc-cast` equality. When the source is the `Discriminant` read of a
    // layout-`disc_index_safe` enum whose declared discriminants are ALL non-negative
    // (`min_disc >= 0`) and the destination integer is at least as wide as the repr,
    // the value lies in `[0, max_disc]` and the signed->unsigned cast is
    // VALUE-PRESERVING, so `_d == e_disc` is an unconditional theorem of this statement
    // (the index IS the disc cast). Mirrors the `-full` native bridge's GATE-NONNEG.
    // Without it the index `e as usize` is a free var and `arr[e as usize]` over a
    // `[T; len > max_disc]` false-FAILs (proved/enumdf_i8_nonneg). SOUND: a negative-disc
    // enum (where `e as usize` reinterprets the sign bit) has `min_disc < 0`, declines
    // here, and the def is dropped — never a false equality, never a false-PROVE.
    if let (Some(from_w), Ty::Int { width: to_w, .. }) = (from_ty.int_width(), to_ty)
        && *to_w >= from_w
        && let Operand::Copy(p) | Operand::Move(p) = op
        && p.projections.is_empty()
        && let Some(Rvalue::Discriminant(disc_place)) = crate::unique_whole_local_def(func, p.local)
        && let Some(enum_ty) = crate::operand_ty(func, &Operand::Copy(disc_place.clone()))
        && let Ty::Adt { variants, disc_index_safe: true, .. } = &enum_ty
        && !variants.is_empty()
        && variants.iter().map(|v| v.discriminant).min().is_some_and(|m| m >= 0)
    {
        // Caller wraps this in `Eq(Var(dest), value)`, i.e. `_d == e_disc`.
        return Some(operand_to_formula(func, op));
    }

    None
}

fn callable_reification_formula(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    to_ty: &Ty,
) -> Formula {
    let dest_name = crate::place_to_var_name(func, dest);
    let sort = crate::place_sort(func, dest).unwrap_or_else(|| crate::sort_for_ty(to_ty));
    crate::callable_reification_token(&dest_name, sort)
}

/// A widening integer cast result is bounded by the *source* type's
/// range. Zero-/sign-extension preserves the value, so `(x as u64)` for `x: u32`
/// lies in `[0, 2^32-1]` however wide the destination is. `extract_block_definitions`
/// already emits `dest == source`, but that only bounds `dest` when the *source*
/// variable is itself range-constrained (e.g. a u32 parameter, via `infer_from_types`).
/// When the source is a #51-extracted struct-payload field — `(p.x as u64)` over a
/// moved enum-variant payload — nothing else constrains it, so the widened value
/// reads as a free u64 and a genuinely safe `(p.x as u64) + (p.y as u64)` false-FAILs.
/// Emitting the source-width range on the cast result restores the bound at its origin.
///
/// Soundness: the returned range is an unconditional truth about the cast, so it can
/// only ever help discharge a real obligation — never manufacture a false-PROVE.
/// It is gated to value-preserving widenings:
///   * unsigned source → any strictly wider integer: result ∈ [0, 2^sw-1];
///   * signed source → strictly wider *signed*:       result ∈ [-2^(sw-1), 2^(sw-1)-1].
/// Signed→unsigned is skipped (a negative source wraps to a huge unsigned value, so the
/// source-width range would be *false*). Same-or-narrowing casts are skipped
/// (reinterpretation/truncation, not value-preserving; narrowing is covered by the
/// CastOverflow VC).
fn widening_cast_result_range(
    func: &VerifiableFunction,
    op: &Operand,
    to_ty: &Ty,
    dest_name: &str,
) -> Option<Formula> {
    let src_ty = crate::operand_ty_cow(func, op);
    // A `bool as <int>` cast is a value-preserving widening into {0,1}: the
    // boolean's runtime value is exactly 0 or 1, so the widened result lies in
    // [0, 1] for EVERY integer destination (any width, signed or unsigned — 0
    // and 1 fit `i8` as readily as `u64`). Model the source as an unsigned
    // width-1 value and emit that range. Without this a hardened panic_boundary
    // over a bool-sum (`(a != b) as u32 + …`, a3d-kernel `face_active_edge_count`)
    // leaves the cast operand unconstrained and the provably-safe add
    // OVER-REFUTES — the same {0,1} gap the per-statement arithmetic-safety lane
    // and trust-mc's typed-CHC cast encoding already close, here in the hardened
    // operand-range lane. Sound: {0,1} is the EXACT image of a bool cast, so this
    // is an unconditional true conjunct (monotone — only discharges a false-FAIL,
    // never manufactures a false-PROVE; a genuine non-bool overflow still refutes).
    if matches!(src_ty.as_deref(), Some(Ty::Bool)) {
        if !matches!(to_ty, Ty::Int { .. }) {
            return None;
        }
        return Some(crate::range::input_range_constraint(
            &Formula::Var(dest_name.to_string(), Sort::Int),
            1,
            false,
        ));
    }
    let Some(Ty::Int { width: sw, signed: ss }) = src_ty.as_deref() else {
        return None;
    };
    let Ty::Int { width: dw, signed: ds } = to_ty else {
        return None;
    };
    // Strict widening only, and only value-preserving signedness transitions.
    if *dw <= *sw || (*ss && !ds) {
        return None;
    }
    Some(crate::range::input_range_constraint(
        &Formula::Var(dest_name.to_string(), Sort::Int),
        *sw,
        *ss,
    ))
}

/// Trust (drop-in cast type-tracking, owner decision 2026-07-06): a NARROWING or
/// signedness-REINTERPRETING integer `as` cast is DEFINED in Rust (it truncates /
/// reinterprets the bit pattern, never UB), so it carries NO `CastOverflow`
/// obligation (see `generate::v2_build_cast_vc`) — Trust does not restrict the
/// programmer. To keep downstream reasoning sound AND precise we instead TYPE-TRACK
/// the result: the cast dest holds a value of the TARGET type, so it lies in the
/// target-type range `type_min(to_ty) <= dest <= type_max(to_ty)`. This is an
/// unconditional truth about the wrapped value (monotone — a conjoined true fact can
/// only discharge a false-FAIL, never manufacture a false-PROVE), and it is exactly
/// what lets `(x as u8) as u32 + 1` prove (result <= 255) while a genuinely OOB
/// `arr[(x as u8) as usize]` over a len-8 array is still CAUGHT (the index can reach
/// 255). Complements [`widening_cast_result_range`], which carries the tighter
/// SOURCE-width range for value-preserving widenings; this fires for exactly the
/// int->int casts widening does NOT cover (narrowing `dw <= sw`, or a value-changing
/// signed->unsigned reinterpret), so each cast contributes one range fact.
fn narrowing_cast_result_range(
    func: &VerifiableFunction,
    op: &Operand,
    to_ty: &Ty,
    dest_name: &str,
) -> Option<Formula> {
    let src_ty = crate::operand_ty_cow(func, op);
    let Some(Ty::Int { width: sw, signed: _ }) = src_ty.as_deref() else {
        return None;
    };
    let Ty::Int { width: dw, signed: ds } = to_ty else {
        return None;
    };
    // Fire for NARROWING (`dw < sw`) and SAME-WIDTH signedness reinterprets
    // (`dw == sw`): the result is a genuine value of the target type whose range
    // meaningfully constrains it (`u32 as u8` -> [0,255]). A strictly-WIDENING cast
    // is left to `widening_cast_result_range` (value-preserving widenings keep their
    // tighter source-width range; a signed->unsigned widening's only sound bound is
    // the trivially-true target range, so it stays free as before).
    if *dw > *sw {
        return None;
    }
    Some(crate::range::input_range_constraint(
        &Formula::Var(dest_name.to_string(), Sort::Int),
        *dw,
        *ds,
    ))
}

/// An unsigned right-shift by a constant `k` bounds its result above by
/// `(2^w - 1) >> k`, where `w` is the operand's width. This is a value-preserving
/// truth: the shifted operand is a width-`w` unsigned value, so `x <= 2^w-1` implies
/// `x >> k <= (2^w-1) >> k`. Like the #52 widening-cast range, it restores a bound the
/// integer model otherwise loses when the shifted operand is itself unconstrained — a
/// moved enum-variant payload field, or a widened value. `(x >> 1) + 1` then false-FAILs
/// because `x >> 1` reads as a free integer with no upper bound; emitting the
/// width-derived bound on the result discharges it.
///
/// Soundness: the bound is an unconditional truth about every real execution, so as a
/// conjoined hypothesis it can only turn a false-FAIL into a PROVE, never an overflow
/// into a false-PROVE (monotonicity — adding a true fact only shrinks the model). It is
/// gated tightly:
///   * `Shr` only — `Shl` can overflow, so its result has no tautological sub-type-max bound;
///   * unsigned operand only — a signed `>>` sign-extends, a different (still-bounded but
///     two-sided) range we do not model here;
///   * constant shift only — a variable shift's tightest sound upper bound is just the type
///     max (`k` could be 0), which is useless; and `k >= w` is a checked shift-overflow
///     (the op may panic and never produce a value), so we must not pre-bound it.
/// The largest value the shift's LHS can hold, when that is structurally bounded BELOW the
/// shift type's max: a widening cast `(x as W)` of an UNSIGNED `ELEM` is `<= MAX(ELEM)`
/// (`2^width(ELEM) - 1`), and a non-negative integer constant bounds itself. None when the LHS
/// is an unconstrained value of the full shift type (no tighter bound than the type max).
fn shift_lhs_unsigned_max(func: &VerifiableFunction, lhs: &Operand) -> Option<u128> {
    match lhs {
        Operand::Constant(ConstValue::Uint(v, _)) => Some(*v),
        Operand::Constant(ConstValue::Int(v)) if *v >= 0 => Some(*v as u128),
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            let Rvalue::Cast(src, _) = crate::unique_whole_local_def(func, p.local)? else {
                return None;
            };
            let src_ty = crate::operand_ty_cow(func, src)?;
            let Ty::Int { width: ew, signed: false } = src_ty.as_ref() else {
                return None;
            };
            Some(crate::range::unsigned_max(*ew))
        }
        _ => None,
    }
}

fn shift_result_range(
    func: &VerifiableFunction,
    op: &BinOp,
    lhs: &Operand,
    rhs: &Operand,
    dest_name: &str,
) -> Option<Formula> {
    // Trust #50: an unsigned LEFT-shift by a constant `(x as W) << k`, where the LHS is
    // structurally bounded by `B = MAX(ELEM) <= MAX(W)`, tightens its result BELOW the type
    // max: if `B << k <= MAX(W)` the shift provably cannot overflow `W`, so for every value
    // `0 <= x <= B` the result `x << k = x * 2^k <= B << k` (no modular wrap). Emit
    // `dest <= B << k`. SOUNDNESS: a loaded element is some value in `[0, B]`, and under the
    // no-overflow check `B << k <= MAX(W)` the W-bit shift equals the true product, so the
    // bound is an unconditional upper bound on `dest` (monotone-safe — only turns a false-FAIL
    // into a PROVE, never an overflow into a false-PROVE; a shift that COULD overflow W has
    // `B << k > MAX(W)` and emits nothing). This is the addend-side companion to
    // `build_accumulator_bound_facts`' case (c): together they discharge `t += (x as W) << k`.
    if matches!(op, BinOp::Shl) {
        let lhs_ty = crate::operand_ty_cow(func, lhs);
        let Some(Ty::Int { width, signed: false }) = lhs_ty.as_deref() else {
            return None;
        };
        let width = *width;
        let k = match rhs {
            Operand::Constant(ConstValue::Uint(v, _)) => *v,
            Operand::Constant(ConstValue::Int(v)) if *v >= 0 => *v as u128,
            _ => return None,
        };
        if k >= u128::from(width) {
            return None;
        }
        let base = shift_lhs_unsigned_max(func, lhs)?;
        // `base * 2^k` with a TRUE value-overflow check. NB: `u128::checked_shl` only checks
        // the shift AMOUNT (`k < 128`), not value overflow, so it would silently WRAP for a
        // large `base` (e.g. a u64 element) and emit an unsound too-small bound; `checked_mul`
        // detects the overflow and declines instead. `1u128 << k` is safe (`k < width <= 128`).
        let scaled = base.checked_mul(1u128 << k)?;
        if scaled > crate::range::unsigned_max(width) {
            return None; // the shift could overflow W — no tight linear bound
        }
        let dest = Formula::Var(dest_name.to_string(), Sort::Int);
        return Some(Formula::Le(Box::new(dest), Box::new(u128_to_formula(scaled))));
    }
    if !matches!(op, BinOp::Shr) {
        return None;
    }
    let lhs_ty = crate::operand_ty_cow(func, lhs);
    let Some(Ty::Int { width, signed }) = lhs_ty.as_deref() else {
        return None;
    };
    let (width, signed) = (*width, *signed);
    let k = match rhs {
        Operand::Constant(ConstValue::Uint(v, _)) => *v,
        Operand::Constant(ConstValue::Int(v)) if *v >= 0 => *v as u128,
        _ => return None,
    };
    if k >= u128::from(width) {
        return None;
    }
    let k = k as u32; // safe: k < width <= 128
    let dest = Formula::Var(dest_name.to_string(), Sort::Int);
    if !signed {
        // Unsigned logical shift: `x: u_w => x >> k <= (2^w - 1) >> k`
        // (lower bound 0 is implicit in the unsigned range).
        let max_val = crate::range::unsigned_max(width) >> k;
        return Some(Formula::Le(Box::new(dest), Box::new(u128_to_formula(max_val))));
    }
    // soundness-signed-shift: a SIGNED arithmetic right shift now bounds
    // its result TWO-sidedly: `-(2^(w-1) >> k) <= dest <= (2^(w-1)-1) >> k`. This
    // was UNSOUND while the shift def bridged via the unsigned bv2nat
    // (BvToInt signed=false) -- the signed-domain endpoints contradicted the
    // bridged unsigned value and vacuously proved overflows. Now that chc.rs
    // bridges signed shifts via bv2int_signed, `dest` lives in this same signed
    // value-space, so the bound is an unconditional truth (monotone-safe: it can
    // only turn a false-FAIL into a PROVE, never an overflow into a false-PROVE).
    // `>>` on i128 is arithmetic, matching Rust's signed `>>` floor-toward-(-inf)
    // endpoints exactly.
    let (smin, smax): (i128, i128) = if width >= 128 {
        (i128::MIN, i128::MAX)
    } else {
        let half = 1i128 << (width - 1);
        (-half, half - 1)
    };
    let lower = smin >> k;
    let upper = smax >> k;
    Some(Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(lower)), Box::new(dest.clone())),
        Formula::Le(Box::new(dest), Box::new(Formula::Int(upper))),
    ]))
}

fn bool_to_int_formula(func: &VerifiableFunction, op: &Operand) -> Formula {
    if let Operand::Constant(ConstValue::Bool(value)) = op {
        return Formula::Int(if *value { 1 } else { 0 });
    }

    Formula::Ite(
        Box::new(operand_to_formula(func, op)),
        Box::new(Formula::Int(1)),
        Box::new(Formula::Int(0)),
    )
}

fn float_binop_to_formula(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> Option<Formula> {
    // soundness: float comparisons are modeled with the IEEE-754 FloatingPoint
    // theory (`fp.eq`/`fp.lt`/`fp.leq`/`fp.gt`/`fp.geq`), which matches Rust's
    // `PartialEq`/`PartialOrd` on floats EXACTLY — NaN is unordered and
    // `NaN != NaN`, and `+0.0 == -0.0`. Each operand's bit pattern (the existing
    // bitvector modelling of float locals) is reinterpreted as a float via
    // `FpFromBits`, so this composes with the rest of the encoding.
    //
    // History (round-8): before the FP theory existed these were left UNMODELED
    // (fail-closed) because the bitvector stand-ins were false-PROVEs — ordering
    // compared sign-dropped magnitudes (wrong for negatives) and general `==`
    // used full-bit `Eq` (made `NaN == NaN`). The `fp.*` encoding fixes both at
    // the source, validated end-to-end against the ay solver, so they are now
    // soundly modeled rather than skipped.
    //
    // The div-by-zero–critical `x == 0.0` / `x != 0.0` keeps its proven
    // magnitude-`== 0` encoding (equivalent to `fp.eq(x, +0.0)`, on the
    // battle-tested path).
    let has_zero = float_is_zero_operand(lhs) || float_is_zero_operand(rhs);
    match op {
        BinOp::Eq if has_zero => Some(float_zero_magnitude_eq(func, lhs, rhs, width)),
        BinOp::Ne if has_zero => {
            Some(Formula::Not(Box::new(float_zero_magnitude_eq(func, lhs, rhs, width))))
        }
        BinOp::Eq => fp_compare(func, lhs, rhs, width, FpCmp::Eq),
        BinOp::Ne => fp_compare(func, lhs, rhs, width, FpCmp::Ne),
        BinOp::Lt => fp_compare(func, lhs, rhs, width, FpCmp::Lt),
        BinOp::Le => fp_compare(func, lhs, rhs, width, FpCmp::Le),
        BinOp::Gt => fp_compare(func, lhs, rhs, width, FpCmp::Gt),
        BinOp::Ge => fp_compare(func, lhs, rhs, width, FpCmp::Ge),
        _ => None,
    }
}

/// IEEE-754 comparison operators we model from Rust `PartialOrd`/`PartialEq`.
#[derive(Clone, Copy)]
enum FpCmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Reinterpret a float operand's bit pattern as an IEEE-754 float term. `None`
/// for non-IEEE widths (fail-closed: an unmodeled comparison leaves the
/// discriminant unconstrained rather than risking an unsound encoding).
fn fp_operand(func: &VerifiableFunction, operand: &Operand, width: u32) -> Option<Formula> {
    let (eb, sb) = match Sort::float_for_width(width) {
        Some(Sort::Float { eb, sb }) => (eb, sb),
        _ => return None,
    };
    Some(Formula::FpFromBits {
        bits: Box::new(float_operand_formula(func, operand, width)),
        eb,
        sb,
    })
}

/// Sound IEEE-754 encoding of a float comparison; matches Rust float
/// `PartialOrd`/`PartialEq` (NaN unordered, `NaN != NaN`, `+0.0 == -0.0`).
fn fp_compare(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
    cmp: FpCmp,
) -> Option<Formula> {
    let l = Box::new(fp_operand(func, lhs, width)?);
    let r = Box::new(fp_operand(func, rhs, width)?);
    Some(match cmp {
        FpCmp::Eq => Formula::FpEq(l, r),
        FpCmp::Ne => Formula::Not(Box::new(Formula::FpEq(l, r))),
        FpCmp::Lt => Formula::FpLt(l, r),
        FpCmp::Le => Formula::FpLe(l, r),
        FpCmp::Gt => Formula::FpGt(l, r),
        FpCmp::Ge => Formula::FpGe(l, r),
    })
}

/// The destination of a float assignment, lifted into FP space. The dest local
/// is modeled as `Sort::BitVec(width)` (its IEEE bit pattern) everywhere, so a
/// value-definition must reinterpret it via `FpFromBits` to compare against an
/// FP-theory result. `None` for non-IEEE widths (fail-closed).
///
/// NOTE: the inner var is kept BARE (`Var(dest, BitVec)`) so
/// `generate::block_def_subject` / `rebind_block_def_subject` can recover and
/// re-version the subject through the `FpFromBits` wrapper.
fn fp_dest_term(dest_name: &str, width: u32) -> Option<Formula> {
    let (eb, sb) = match Sort::float_for_width(width) {
        Some(Sort::Float { eb, sb }) => (eb, sb),
        _ => return None,
    };
    Some(Formula::FpFromBits {
        bits: Box::new(Formula::Var(dest_name.to_string(), Sort::BitVec(width))),
        eb,
        sb,
    })
}

/// Sound value-definition for a float ARITHMETIC assignment `dest = lhs OP rhs`
/// (`OP` ∈ Add/Sub/Mul/Div). Returns the complete top-level **structural** `Eq`
///
///   `Eq( FpFromBits(dest), fp.OP(RNE, FpFromBits(lhs), FpFromBits(rhs)) )`
///
/// Structural `Eq` (NOT `FpEq`) is the only sound choice for a *definition*:
/// it is reflexive on NaN and distinguishes ±0, so `dest` is pinned to exactly
/// the IEEE result value (a NaN result merely leaves the dest bit pattern free
/// over all NaN encodings — sound underconstraint matching unspecified Rust NaN
/// payloads). Rust `f32/f64` `+ - * /` round to nearest-ties-even (RNE) with no
/// dynamic mode, so RNE matches hardware exactly. `None` for non-arith ops or
/// non-IEEE widths (fail-closed: dest stays free → at worst a missed proof).
fn fp_arith_value_def(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    dest_name: &str,
    width: u32,
) -> Option<Formula> {
    let l = Box::new(fp_operand(func, lhs, width)?);
    let r = Box::new(fp_operand(func, rhs, width)?);
    let rne = || Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
    let fp_result = match op {
        BinOp::Add => Formula::FpAdd(rne(), l, r),
        BinOp::Sub => Formula::FpSub(rne(), l, r),
        BinOp::Mul => Formula::FpMul(rne(), l, r),
        BinOp::Div => Formula::FpDiv(rne(), l, r),
        _ => return None,
    };
    let dest = Box::new(fp_dest_term(dest_name, width)?);
    Some(Formula::Eq(dest, Box::new(fp_result)))
}

/// Sound value-definition for a float `dest = -operand` (`Rvalue::UnaryOp(Neg)`).
/// Negation is EXACT in IEEE-754 (a sign-bit flip, no rounding), so no rounding
/// mode is needed: `Eq( FpFromBits(dest), fp.neg(FpFromBits(operand)) )`.
fn fp_neg_value_def(
    func: &VerifiableFunction,
    operand: &Operand,
    dest_name: &str,
    width: u32,
) -> Option<Formula> {
    let a = Box::new(fp_operand(func, operand, width)?);
    let dest = Box::new(fp_dest_term(dest_name, width)?);
    Some(Formula::Eq(dest, Box::new(Formula::FpNeg(a))))
}

/// Sound value-definition for a float `dest = operand.abs()` (a `f32::abs` /
/// `f64::abs` Call). Like negation, abs is EXACT in IEEE-754 (a sign-bit clear,
/// no rounding), so no rounding mode is needed:
/// `Eq( FpFromBits(dest), fp.abs(FpFromBits(operand)) )`. Used by
/// `generate::build_fp_abs_facts` (abs arrives as a Call terminator, not an
/// Rvalue, so it is emitted as a global SSA-gated fact rather than a per-block
/// definition). `None` for non-IEEE widths (fail-closed).
pub(crate) fn fp_abs_value_def(
    func: &VerifiableFunction,
    operand: &Operand,
    dest_name: &str,
    width: u32,
) -> Option<Formula> {
    let a = Box::new(fp_operand(func, operand, width)?);
    let dest = Box::new(fp_dest_term(dest_name, width)?);
    Some(Formula::Eq(dest, Box::new(Formula::FpAbs(a))))
}

/// Sound encoding of `x == 0.0` (and, negated, `x != 0.0`): the magnitude (all
/// bits except the sign) is zero. True for +0.0 and -0.0; false for NaN (nonzero
/// magnitude) and every other value.
fn float_zero_magnitude_eq(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> Formula {
    let nonzero_side = if float_is_zero_operand(lhs) { rhs } else { lhs };
    Formula::Eq(
        Box::new(float_magnitude_formula(func, nonzero_side, width)),
        Box::new(Formula::BitVec { value: 0, width: width - 1 }),
    )
}

fn float_magnitude_formula(func: &VerifiableFunction, operand: &Operand, width: u32) -> Formula {
    Formula::BvExtract {
        inner: Box::new(float_operand_formula(func, operand, width)),
        high: width - 2,
        low: 0,
    }
}

fn float_operand_formula(func: &VerifiableFunction, operand: &Operand, width: u32) -> Formula {
    match operand {
        Operand::Constant(ConstValue::Float(value)) => Formula::BitVec {
            value: match width {
                32 => i128::from(((*value) as f32).to_bits()),
                64 => i128::from(value.to_bits()),
                _ => i128::from(value.to_bits()),
            },
            width,
        },
        Operand::Constant(ConstValue::FloatBits { bits, width: const_width })
            if *const_width == width =>
        {
            match i128::try_from(*bits) {
                Ok(value) => Formula::BitVec { value, width },
                Err(_) => operand_to_formula(func, operand),
            }
        }
        _ => operand_to_formula(func, operand),
    }
}

fn float_is_zero_operand(operand: &Operand) -> bool {
    match operand {
        Operand::Constant(ConstValue::Float(value)) => *value == 0.0,
        Operand::Constant(ConstValue::FloatBits { bits, width }) => {
            crate::float_bits_magnitude_is_zero(*bits, *width)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use super::*;

    fn test_func() -> VerifiableFunction {
        VerifiableFunction {
            name: "test".to_string(),
            def_path: "test::test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: Some("ret".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
                ],
                blocks: vec![],
                arg_count: 2,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn checked_literal_func(value_ty: Ty, lhs: Operand, rhs: Operand) -> VerifiableFunction {
        VerifiableFunction {
            name: "checked_literal".into(),
            def_path: "test::checked_literal".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: value_ty.clone(), name: Some("ret".into()) },
                    LocalDecl { index: 1, ty: value_ty.clone(), name: Some("x".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Tuple(vec![value_ty.clone(), Ty::Bool]),
                        name: Some("checked".into()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, lhs, rhs),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Move(Place {
                                local: 2,
                                projections: vec![trust_types::Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                            unwind: UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: value_ty,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn checked_assert_semantics_contextualize_signed_narrow_literals_exactly() {
        let x = Operand::Copy(Place::local(1));
        for (lhs, rhs) in [
            (x.clone(), Operand::Constant(ConstValue::Int(1))),
            (Operand::Constant(ConstValue::Int(1)), x.clone()),
        ] {
            let func = checked_literal_func(Ty::i32(), lhs, rhs);
            let success = extract_assert_passed_semantics(&func, &func.body.blocks[0]);
            let failure = extract_overflow_flag_semantics(&func, &func.body.blocks[0]);
            assert!(!success.is_empty(), "representable i32 literal must retain success facts");
            assert!(!failure.is_empty(), "representable i32 literal must retain overflow facts");

            let success_smt = Formula::And(success).to_smtlib();
            assert!(
                success_smt.contains("(= checked.0 (+"),
                "success facts must define the checked value: {success_smt}"
            );
            assert!(
                success_smt.contains("2147483648")
                    && success_smt.contains("2147483647")
                    && !success_smt.contains("9223372036854775808"),
                "the tuple's authenticated i32 domain—not the literal fallback i64—must drive the facts: {success_smt}"
            );
        }

        let out_of_range = checked_literal_func(
            Ty::i8(),
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Int(128)),
        );
        assert!(
            extract_assert_passed_semantics(&out_of_range, &out_of_range.body.blocks[0]).is_empty(),
            "an out-of-range i8 literal must not mint success-edge arithmetic facts"
        );
        assert!(
            extract_overflow_flag_semantics(&out_of_range, &out_of_range.body.blocks[0]).is_empty(),
            "an out-of-range i8 literal must not mint overflow-flag arithmetic facts"
        );
    }

    #[test]
    fn enum_aggregate_write_constrains_downcast_payload_place() {
        // Trust: `let o: Option<u32> = Some(7)` lowers to an ADT aggregate whose
        // payload is read in the match arm as `(o as Some).0` → `o@1.0`. The
        // write must constrain that downcast-named place; otherwise the payload
        // is a free variable and the arm's `v + 1` overflow check false-fails
        // (the solver picks `o@1.0 = u32::MAX`). Regression for the enum-payload
        // aggregate-naming mismatch — must NOT depend on telling struct from enum.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl {
                index: 1,
                ty: Ty::Adt { adt_kind: None, layout: None, 
                    variants: Vec::new(),
                    name: "Option".into(),
                    // Enum layout per `lower_enum_adt`: `__tag` then per-variant
                    // flattened payload fields (`__v1_0` for `Some`'s field 0).
                    fields: vec![("__tag".into(), Ty::i32()), ("__v1_0".into(), Ty::u32())],
                    disc_index_safe: false,
                    faithful_enum_repr: None, enum_layout: None, },
                name: Some("o".into()),
            },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Adt { name: "Option".into(), variant: 1, active_field: None, args: None },
                    vec![Operand::Constant(ConstValue::Int(7))],
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        let constrains_downcast_payload = defs.iter().any(|f| {
            matches!(f, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("o@1.0")
                && matches!(rhs.as_ref(), Formula::Int(7)))
        });
        assert!(
            constrains_downcast_payload,
            "enum payload write must constrain `o@1.0 == 7`, got: {defs:?}"
        );
    }

    #[test]
    fn shift_result_range_bounds_const_shr() {
        // `x >> k` for unsigned `x: uW` and constant `k < W` is bounded
        // above by `(2^W - 1) >> k`. soundness-signed-shift: a SIGNED `x >> k`
        // gets the two-sided `-(2^(W-1) >> k) <= dest <= (2^(W-1)-1) >> k`. Both are
        // gated to a constant `k < W`; `Shl`, a variable shift, and `k >= W` decline.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("sx".into()) },
        ];
        func.body.arg_count = 2;

        let x = Operand::Copy(Place::local(1));
        let sx = Operand::Copy(Place::local(2));
        let k = Operand::Constant(ConstValue::Uint(2, 32));

        // Unsigned Shr by const 2 → `dest <= (2^32-1) >> 2`.
        let bound = shift_result_range(&func, &BinOp::Shr, &x, &k, "dest")
            .expect("unsigned const Shr should emit a bound");
        let expected = (u128::from(u32::MAX) >> 2) as i128; // 1_073_741_823
        assert!(
            matches!(&bound, Formula::Le(l, r)
                if l.var_name() == Some("dest")
                && matches!(r.as_ref(), Formula::Int(n) if *n == expected)),
            "got {bound:?}"
        );

        // Shl of a BARE full-width value (`x: u32`, no structural bound below the type max)
        // declines: the result could wrap, so there is no tight linear bound.
        assert!(shift_result_range(&func, &BinOp::Shl, &x, &k, "dest").is_none());
        // Shl of a structurally-bounded LHS (here a non-negative constant `3`) by const `2`
        // CANNOT overflow u32, so it tightens to `dest <= 3 << 2 = 12` (#50 addend-side bound).
        let cbound = shift_result_range(
            &func,
            &BinOp::Shl,
            &Operand::Constant(ConstValue::Uint(3, 32)),
            &k,
            "dest",
        )
        .expect("Shl of a bounded LHS by a safe constant should emit a bound");
        assert!(
            matches!(&cbound, Formula::Le(l, r)
                if l.var_name() == Some("dest")
                && matches!(r.as_ref(), Formula::Int(n) if *n == 12)),
            "got {cbound:?}"
        );
        // Signed `>>` by const 2 → two-sided `-(2^31>>2) <= dest <= (2^31-1)>>2`,
        // i.e. `-536_870_912 <= dest <= 536_870_911` (sound now that signed shifts
        // bridge via bv2int_signed).
        let signed_bound = shift_result_range(&func, &BinOp::Shr, &sx, &k, "dest")
            .expect("signed const Shr should emit a two-sided bound");
        match &signed_bound {
            Formula::And(parts) if parts.len() == 2 => {
                assert!(
                    matches!(&parts[0], Formula::Le(l, r)
                        if matches!(l.as_ref(), Formula::Int(n) if *n == -536_870_912)
                        && r.var_name() == Some("dest")),
                    "lower bound wrong: {:?}",
                    parts[0]
                );
                assert!(
                    matches!(&parts[1], Formula::Le(l, r)
                        if l.var_name() == Some("dest")
                        && matches!(r.as_ref(), Formula::Int(n) if *n == 536_870_911)),
                    "upper bound wrong: {:?}",
                    parts[1]
                );
            }
            other => panic!("expected two-sided And bound, got {other:?}"),
        }
        // Variable shift → tightest sound bound is just the type max (useless).
        let var_k = Operand::Copy(Place::local(1));
        assert!(shift_result_range(&func, &BinOp::Shr, &x, &var_k, "dest").is_none());
        // Shift amount >= width → a checked shift-overflow, must not pre-bound.
        let big_k = Operand::Constant(ConstValue::Uint(32, 32));
        assert!(shift_result_range(&func, &BinOp::Shr, &x, &big_k, "dest").is_none());

        // Shl SOUNDNESS: a structurally-bounded LHS whose `base << k` would OVERFLOW the shift
        // type `W` must DECLINE (no bound) — emitting `dest <= base << k` would be unsound when
        // the W-bit shift modularly wraps. Here const `base = 2^30` shifted by `k = 5` gives
        // `2^35 > u32::MAX`, so the result could wrap; the bound is withheld.
        let big_base = Operand::Constant(ConstValue::Uint(1u128 << 30, 32));
        let k5 = Operand::Constant(ConstValue::Uint(5, 32));
        assert!(
            shift_result_range(&func, &BinOp::Shl, &big_base, &k5, "dest").is_none(),
            "Shl whose base<<k overflows the shift width must not emit a bound"
        );
    }

    #[test]
    fn shared_ref_connects_deref_to_referent() {
        // a match-guard binding lowers by reference (`r = &payload`;
        // the guard tests `*r`) while the arm reads the payload by value. The
        // shared borrow must emit `*r == payload` (`r* == p`) so the guard
        // constrains the same value the arm uses — otherwise `*r` is a free
        // variable and a guarded binding (`Some(v) if v < K => v + 1`)
        // false-fails.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("p".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                name: Some("r".into()),
            },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        let connects = defs.iter().any(|f| {
            matches!(f, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("r*") && rhs.var_name() == Some("p"))
        });
        assert!(connects, "shared ref must emit `r* == p`, got: {defs:?}");
    }

    #[test]
    fn mut_ref_does_not_emit_deref_equality() {
        // `&mut` is deliberately skipped: a later `*r = ..` could invalidate
        // `*r == referent`, so emitting the equality would be unsound.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("p".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                name: Some("r".into()),
            },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            !defs.iter().any(|f| matches!(f, Formula::Eq(lhs, _) if lhs.var_name() == Some("r*"))),
            "&mut must not emit a deref equality, got: {defs:?}"
        );
    }

    #[test]
    fn mut_ref_slice_reborrow_ties_length() {
        // `r = &mut (*s)` for `s: &mut [u8]` — the shape a guarded
        // `if i < s.len() { *s.get_unchecked_mut(i) = v }` lowers to (the receiver
        // is a fresh `&mut (*s)` reborrow) — must tie the reborrow's `__slice_len`
        // to the source's, so the guard's `s.len()` discharges the bounds
        // obligation. SOUND: a slice's LENGTH is immutable through `&mut [T]`
        // (only its elements are). Regression lock for the get_unchecked_mut fix.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: true,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                },
                name: Some("s".into()),
            },
            LocalDecl {
                index: 2,
                ty: Ty::Ref {
                    mutable: true,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                },
                name: Some("r".into()),
            },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref {
                    mutable: true,
                    place: Place { local: 1, projections: vec![trust_types::Projection::Deref] },
                },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        // The length tie `r__slice_len == s__slice_len` must now be present.
        assert!(
            defs.iter().any(|f| matches!(f, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("r__slice_len") && rhs.var_name() == Some("s__slice_len"))),
            "&mut slice reborrow must tie length `r__slice_len == s__slice_len`, got: {defs:?}"
        );
        // ...but it must STILL NOT emit the deref-VALUE equality (unsound for &mut).
        assert!(
            !defs.iter().any(|f| matches!(f, Formula::Eq(lhs, _) if lhs.var_name() == Some("r*"))),
            "&mut must not emit a deref-value equality even while tying length, got: {defs:?}"
        );
    }

    /// True when `defs` contains an `input_range_constraint`-shaped fact bounding
    /// `var` from both sides (a lower `Le(_, var)` and an upper `Le(var, _)`).
    fn has_range_bound_on(defs: &[Formula], var: &str) -> bool {
        defs.iter().any(|f| {
            matches!(f, Formula::And(cs)
                if cs.iter().any(|c| matches!(c, Formula::Le(_, v) if v.var_name() == Some(var)))
                && cs.iter().any(|c| matches!(c, Formula::Le(v, _) if v.var_name() == Some(var))))
        })
    }

    fn single_cast_func(src_ty: Ty, dst_ty: Ty) -> VerifiableFunction {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: dst_ty.clone(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: src_ty, name: Some("x".into()) },
            LocalDecl { index: 2, ty: dst_ty.clone(), name: None },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = dst_ty.clone();
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), dst_ty),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];
        func
    }

    #[test]
    fn widening_unsigned_cast_bounds_result_by_source_width() {
        // `(x as u64)` for `x: u32` must emit `0 <= dest <= 2^32-1` on the
        // cast result, not merely `dest == x`. Without this, when the cast source has
        // no independent range bound (a #51-extracted struct-payload field), the
        // widened u64 reads as a free variable and a safe `(p.x as u64)+(p.y as u64)`
        // false-FAILs. The bound is a value-preserving-widening tautology, so sound.
        let func = single_cast_func(Ty::u32(), Ty::u64());
        let dest = crate::place_to_var_name(&func, &Place::local(2));
        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        let upper = (1i128 << 32) - 1;
        let bounded = defs.iter().any(|f| {
            matches!(f, Formula::And(cs)
                if cs.iter().any(|c| matches!(c, Formula::Le(_, v) if v.var_name() == Some(dest.as_str())))
                && cs.iter().any(|c| matches!(c,
                    Formula::Le(v, hi) if v.var_name() == Some(dest.as_str())
                        && matches!(hi.as_ref(), Formula::Int(n) if *n == upper))))
        });
        assert!(
            bounded,
            "widening u32->u64 cast must bound result `{dest}` to [0, 2^32-1], got: {defs:?}"
        );
    }

    #[test]
    fn widened_operand_source_range_rejects_reassigned_cast_local() {
        // The first definition says `w` came from a u8, but the second gives it
        // a legal u16 value far outside the u8 range. A whole-function first-cast
        // scan must not inject the stale `w <= 255` fact into a later checked op.
        let mut func = single_cast_func(Ty::u8(), Ty::u16());
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(60_000, 16))),
            span: SourceSpan::default(),
        });
        assert!(
            widening_operand_source_range(&func, &Operand::Copy(Place::local(2))).is_none(),
            "a reassigned widened local must not retain its first cast's source range"
        );
    }

    #[test]
    fn narrowing_cast_emits_target_type_range_not_source_width() {
        // u64 -> u32 is a truncating (defined) cast — no CastOverflow VC. It is
        // type-tracked: the result is a u32, so `0 <= dest <= u32::MAX` is emitted
        // (the TARGET-type range), NOT the meaningless source-width (u64) range.
        let func = single_cast_func(Ty::u64(), Ty::u32());
        let dest = crate::place_to_var_name(&func, &Place::local(2));
        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            has_range_bound_on(&defs, &dest),
            "narrowing cast must type-track its result with the target-type range on \
             `{dest}`, got: {defs:?}"
        );
        // The upper bound must be the TARGET max (u32::MAX = 4_294_967_295), proving
        // it is the sound target-type range and not the source-width (u64) range.
        let has_u32_max = defs.iter().any(|f| {
            matches!(f, Formula::And(cs) if cs.iter().any(|c| matches!(c,
                Formula::Le(v, hi)
                    if v.var_name() == Some(dest.as_str())
                    && matches!(hi.as_ref(), Formula::Int(n) if *n == u32::MAX as i128))))
        });
        assert!(
            has_u32_max,
            "narrowing cast result must be bounded by the TARGET max (u32::MAX), not the \
             source-width max: {defs:?}"
        );
    }

    #[test]
    fn signed_to_unsigned_widening_cast_does_not_emit_source_range() {
        // SOUNDNESS: i32 -> u64 sign-extends then reinterprets, so a negative source
        // wraps to a huge unsigned value — the signed source-width range would be
        // FALSE and could false-PROVE a real overflow. Must be skipped.
        let func = single_cast_func(Ty::i32(), Ty::u64());
        let dest = crate::place_to_var_name(&func, &Place::local(2));
        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            !has_range_bound_on(&defs, &dest),
            "signed->unsigned widening must not emit a source range on `{dest}`, got: {defs:?}"
        );
    }

    #[test]
    fn def_with_operand_overwritten_later_in_block_is_dropped() {
        // SOUNDNESS: `c = m < 1000; m = BIG;` must NOT leave `c == (m < 1000)` in
        // the block's defs — that fact describes the *post*-`m = BIG` value of `m`,
        // which is wrong. A later `if c { m + 1 }` would then carry the
        // contradictory hypotheses {c == true, c == (m < 1000), m == BIG} and
        // vacuously prove the overflow safe (a false-PROVE of a real overflow).
        // Same-destination last-write dedup does not catch this: the stale fact's
        // destination is `c`, but its *operand* `m` is what gets overwritten.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("m".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("big".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1000)),
                    ),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        // The live reassignment of `m` survives.
        assert!(
            defs.iter().any(|f| matches!(f, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("m") && rhs.var_name() == Some("big"))),
            "live `m == big` must survive, got: {defs:?}"
        );
        // The stale comparison over the overwritten `m` must be gone.
        assert!(
            !defs.iter().any(|f| matches!(f, Formula::Eq(lhs, _) if lhs.var_name() == Some("c"))),
            "stale `c == (m < 1000)` must be dropped once `m` is overwritten, got: {defs:?}"
        );
    }

    #[test]
    fn def_with_operand_not_overwritten_survives() {
        // Precision guard: when the operand is NOT reassigned later, the
        // comparison def must survive (otherwise every guard would be dropped).
        // `c = m < 1000;` with no later write to `m` keeps `c == (m < 1000)`.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("m".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(1000)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            defs.iter().any(|f| matches!(f, Formula::Eq(lhs, _) if lhs.var_name() == Some("c"))),
            "live `c == (m < 1000)` must survive when `m` is not overwritten, got: {defs:?}"
        );
    }

    #[test]
    fn test_guard_switch_int_match_to_formula() {
        let func = test_func();
        let guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(1)), value: 42 };
        let formula = guard_to_formula(&func, &guard);
        // Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("x")
                && matches!(rhs.as_ref(), Formula::Int(42))
            ),
            "SwitchIntMatch should produce discr == value, got: {formula:?}"
        );
    }

    #[test]
    fn test_guard_switch_int_otherwise_to_formula() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![0, 7],
        };
        let formula = guard_to_formula(&func, &guard);
        match &formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                assert!(matches!(&clauses[0], Formula::Not(inner)
                    if matches!(inner.as_ref(), Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::Int(0)))
                ));
                assert!(matches!(&clauses[1], Formula::Not(inner)
                    if matches!(inner.as_ref(), Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::Int(7)))
                ));
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_guard_switch_int_otherwise_single_excluded() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![5],
        };
        let formula = guard_to_formula(&func, &guard);
        // Single excluded value should produce just Not(Eq(..)), not And([...])
        assert!(matches!(&formula, Formula::Not(_)), "single excluded: {formula:?}");
    }

    #[test]
    fn test_guard_switch_int_otherwise_empty_excluded() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![],
        };
        let formula = guard_to_formula(&func, &guard);
        assert_eq!(formula, Formula::Bool(true));
    }

    #[test]
    fn test_bool_switch_rewrite_ignores_nondominating_definition() {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
        ];
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(1, trust_types::BlockId(1))],
                    otherwise: trust_types::BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(0)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];

        let guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(2)), value: 1 };
        let formula = guard_to_formula(&func, &guard);

        assert!(
            formula.var_name() == Some("cond"),
            "nondominating bool definitions must not rewrite the switch guard, got {formula:?}"
        );
    }

    #[test]
    fn test_branch_merge_definitions_encodes_diamond_as_ite() {
        // `let x = if flag { 10 } else { 20 };`
        //   bb0: SwitchInt(flag) -> [0: bb2, otherwise: bb1]
        //   bb1 (flag true):  x = 10; goto bb3
        //   bb2 (flag false): x = 20; goto bb3
        //   bb3 (join):       return
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
        ];
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, trust_types::BlockId(2))],
                    otherwise: trust_types::BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(3)),
            },
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(3)),
            },
            BasicBlock {
                id: trust_types::BlockId(3),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];

        let merged = branch_merge_definitions(&func, trust_types::BlockId(3), &Default::default());
        assert_eq!(merged.len(), 1, "expected one merged-local invariant, got {merged:?}");
        match &merged[0] {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(lhs.var_name(), Some("x"), "lhs must be the merged local x: {lhs:?}");
                match rhs.as_ref() {
                    Formula::Ite(cond, then_v, else_v) => {
                        // value 0 selects the match arm (bb2, x=20) when flag is
                        // false, so the guard is Not(flag) and the then-branch is 20.
                        assert!(
                            matches!(cond.as_ref(), Formula::Not(inner) if inner.var_name() == Some("flag")),
                            "guard must be Not(flag): {cond:?}"
                        );
                        assert_eq!(**then_v, Formula::Int(20), "match arm (flag false) is x=20");
                        assert_eq!(**else_v, Formula::Int(10), "otherwise arm (flag true) is x=10");
                    }
                    other => panic!("rhs must be an Ite, got: {other:?}"),
                }
            }
            other => panic!("merged invariant must be an Eq, got: {other:?}"),
        }
    }

    #[test]
    fn test_branch_merge_keeps_switch_identity_across_checked_assert_success() {
        // `let x = if flag { checked_add_value } else { 10 };`
        //
        // rustc splits the checked arm through an overflow Assert:
        //
        //   bb0: SwitchInt(flag) -> [0: bb2, otherwise: bb1]
        //   bb1: x = 10; goto bb4
        //   bb2: checked = AddWithOverflow(..);
        //        Assert(!checked.1) -> bb3
        //   bb3: x = checked.0; goto bb4
        //   bb4: return
        //
        // The Assert failure edge never reaches bb4, so bb0 still partitions
        // every execution that reaches the join. Losing that identity leaves x
        // free and falsely refutes valid postconditions over guarded arithmetic.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                name: Some("checked".into()),
            },
            LocalDecl { index: 4, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 5, ty: Ty::u32(), name: Some("b".into()) },
        ];
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, trust_types::BlockId(2))],
                    otherwise: trust_types::BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(4)),
            },
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(4)),
                        Operand::Copy(Place::local(5)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert {
                    cond: Operand::Move(Place {
                        local: 3,
                        projections: vec![trust_types::Projection::Field(1)],
                    }),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: trust_types::BlockId(3),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Continue,
                },
            },
            BasicBlock {
                id: trust_types::BlockId(3),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 3,
                        projections: vec![trust_types::Projection::Field(0)],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(4)),
            },
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        let pristine = func.clone();

        let merged = branch_merge_definitions(&func, trust_types::BlockId(4), &Default::default());
        assert_eq!(merged.len(), 1, "expected one exact checked-arm merge, got {merged:?}");
        let Formula::Eq(lhs, rhs) = &merged[0] else {
            panic!("merged invariant must be an Eq, got: {:?}", merged[0]);
        };
        assert_eq!(lhs.var_name(), Some("x"));
        let Formula::Ite(cond, checked, fallback) = rhs.as_ref() else {
            panic!("merged rhs must be an Ite, got: {rhs:?}");
        };
        assert!(
            matches!(cond.as_ref(), Formula::Not(inner) if inner.var_name() == Some("flag")),
            "value 0 must select the checked arm under Not(flag): {cond:?}"
        );
        assert_eq!(
            **checked,
            Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            ),
            "the uniquely dominated checked result must be inlined before the join"
        );
        assert_eq!(**fallback, Formula::Int(10));

        // A write in the value arm changes the meaning of the unversioned name
        // `a` but not the snapshot already stored in `checked.0`. Inlining to
        // the arm-exit `a + b` here would be a false fact and could false-PROVE.
        // Keep the exact control-flow merge, but leave the checked field opaque.
        func.body.blocks[3].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(99))),
                span: SourceSpan::default(),
            },
        );
        let stale = branch_merge_definitions(&func, trust_types::BlockId(4), &Default::default());
        let Formula::Eq(_, stale_rhs) = &stale[0] else {
            panic!("stale-arm merge must remain an Eq, got: {:?}", stale[0]);
        };
        let Formula::Ite(_, stale_checked, _) = stale_rhs.as_ref() else {
            panic!("stale-arm merge rhs must remain an Ite, got: {stale_rhs:?}");
        };
        assert_eq!(
            stale_checked.var_name(),
            Some("checked.0"),
            "a clobbered checked operand must block snapshot substitution"
        );

        // The Ite selector is the raw switch discriminator. Reassigning it on an
        // incoming arm makes the unversioned name stale, so the entire merge
        // must be withheld (not merely the checked-result substitution).
        func.body.blocks[3].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
            span: SourceSpan::default(),
        });
        assert!(
            branch_merge_definitions(&func, trust_types::BlockId(4), &Default::default())
                .is_empty(),
            "a post-switch discriminant write must fail closed"
        );

        let false_route = exact_switch_value_guard(&pristine, &Operand::Copy(Place::local(2)), 0);
        assert!(
            matches!(false_route, Some(Formula::Not(inner)) if inner.var_name() == Some("flag")),
            "a branch selector needs exact raw Bool polarity, never a weakened `true` guard"
        );
        let mut signed = pristine.clone();
        signed.body.locals[2].ty = Ty::Int { width: 8, signed: true };
        assert!(
            exact_switch_value_guard(&signed, &Operand::Copy(Place::local(2)), 0xff).is_none(),
            "raw signed SwitchInt targets must fail closed until sign-extension is modeled"
        );

        let mut duplicate = pristine.clone();
        let Terminator::SwitchInt { targets, .. } = &mut duplicate.body.blocks[0].terminator else {
            unreachable!("fixture root is a SwitchInt");
        };
        targets.push((0, trust_types::BlockId(1)));
        assert!(
            branch_merge_definitions(&duplicate, trust_types::BlockId(4), &Default::default())
                .is_empty(),
            "duplicate raw switch values must not mint overlapping Ite arms"
        );

        let mut failure_reaches_value_arm = pristine.clone();
        let Terminator::Assert { unwind, .. } =
            &mut failure_reaches_value_arm.body.blocks[2].terminator
        else {
            unreachable!("fixture checked block is an Assert");
        };
        *unwind = UnwindEdge::Cleanup(trust_types::BlockId(3));
        assert!(
            branch_merge_definitions(
                &failure_reaches_value_arm,
                trust_types::BlockId(4),
                &Default::default(),
            )
            .is_empty(),
            "an Assert failure edge reaching its value arm is not success-authenticated"
        );

        // The shared checked-Assert recognizer is itself proof authority for
        // semantic/path maps. Multiple reaching tuple definitions or a write
        // after the checked snapshot must yield no facts in either direction.
        let mut multiple_checked = pristine.clone();
        multiple_checked.body.blocks[2].stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(4)),
                Operand::Copy(Place::local(5)),
            ),
            span: SourceSpan::default(),
        });
        assert!(
            extract_assert_passed_semantics(&multiple_checked, &multiple_checked.body.blocks[2])
                .is_empty()
        );
        assert!(
            extract_overflow_flag_semantics(&multiple_checked, &multiple_checked.body.blocks[2])
                .is_empty()
        );

        let mut post_snapshot_write = pristine;
        post_snapshot_write.body.blocks[2].stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
            span: SourceSpan::default(),
        });
        assert!(
            extract_assert_passed_semantics(
                &post_snapshot_write,
                &post_snapshot_write.body.blocks[2]
            )
            .is_empty()
        );
        assert!(
            extract_overflow_flag_semantics(
                &post_snapshot_write,
                &post_snapshot_write.body.blocks[2]
            )
            .is_empty()
        );
    }

    // Helpers shared by the n-arm merge tests below.
    fn arm_assign(id: usize, value: i128, goto: usize) -> BasicBlock {
        BasicBlock {
            id: trust_types::BlockId(id),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Goto(trust_types::BlockId(goto)),
        }
    }

    // Asserts `f` is `Eq(Var("d"), Int(value))` — the guard for switch arm `value`.
    fn assert_discr_guard(f: &Formula, value: i128) {
        match f {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(lhs.var_name(), Some("d"), "guard lhs must be discr d: {f:?}");
                assert_eq!(**rhs, Formula::Int(value), "guard rhs must be Int({value}): {f:?}");
            }
            other => panic!("expected Eq(d, Int({value})), got: {other:?}"),
        }
    }

    // Three-arm enum `let base = match e { A => 10, B => 20, C => 30 }` where the
    // exhaustive lowering routes the last variant through `otherwise` (which still
    // reaches the join). Expect base == Ite(d==0,10,Ite(d==1,20,30)).
    fn assert_three_arm_merge(merged: &[Formula]) {
        assert_eq!(merged.len(), 1, "expected one merged-local invariant, got {merged:?}");
        let Formula::Eq(lhs, rhs) = &merged[0] else {
            panic!("merged invariant must be an Eq, got: {:?}", merged[0]);
        };
        assert_eq!(lhs.var_name(), Some("base"), "lhs must be the merged local base: {lhs:?}");
        // Outer: Ite(d==0, 10, <inner>)
        let Formula::Ite(g0, v0, inner) = rhs.as_ref() else {
            panic!("rhs must be an Ite, got: {rhs:?}");
        };
        assert_discr_guard(g0, 0);
        assert_eq!(**v0, Formula::Int(10), "arm d==0 is base=10");
        // Inner: Ite(d==1, 20, 30)   (30 is the else / catch-all arm)
        let Formula::Ite(g1, v1, else_v) = inner.as_ref() else {
            panic!("inner must be an Ite, got: {inner:?}");
        };
        assert_discr_guard(g1, 1);
        assert_eq!(**v1, Formula::Int(20), "arm d==1 is base=20");
        assert_eq!(**else_v, Formula::Int(30), "catch-all arm is base=30");
    }

    fn three_arm_func() -> VerifiableFunction {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("base".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) },
        ];
        func
    }

    #[test]
    fn test_branch_merge_three_arm_otherwise_is_last_variant() {
        // bb0: SwitchInt(d) -> [0: bb1, 1: bb2, otherwise: bb3]
        // bb1: base=10; goto bb4   bb2: base=20; goto bb4   bb3: base=30; goto bb4
        // bb4 (join): return
        let mut func = three_arm_func();
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, trust_types::BlockId(1)), (1, trust_types::BlockId(2))],
                    otherwise: trust_types::BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            arm_assign(1, 10, 4),
            arm_assign(2, 20, 4),
            arm_assign(3, 30, 4),
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        assert_three_arm_merge(&branch_merge_definitions(
            &func,
            trust_types::BlockId(4),
            &Default::default(),
        ));
    }

    #[test]
    fn test_branch_merge_three_arm_separate_unreachable_otherwise() {
        // bb0: SwitchInt(d) -> [0: bb1, 1: bb2, 2: bb3, otherwise: bb5]
        // bb1/2/3: base=10/20/30; goto bb4    bb4 (join): return    bb5: unreachable
        // The unreachable otherwise never reaches the join, so the last explicit
        // target (bb3) is promoted to the catch-all; same Ite as above.
        let mut func = three_arm_func();
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![
                        (0, trust_types::BlockId(1)),
                        (1, trust_types::BlockId(2)),
                        (2, trust_types::BlockId(3)),
                    ],
                    otherwise: trust_types::BlockId(5),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            arm_assign(1, 10, 4),
            arm_assign(2, 20, 4),
            arm_assign(3, 30, 4),
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: trust_types::BlockId(5),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            },
        ];
        assert_three_arm_merge(&branch_merge_definitions(
            &func,
            trust_types::BlockId(4),
            &Default::default(),
        ));
    }

    #[test]
    fn test_branch_merge_bails_when_arm_not_from_switch() {
        // bb3 reaches the join but descends from bb2 (an extra hop), not the
        // switch bb0 — the arms do not share one conditional predecessor, so no
        // partition claim is sound and the result must be empty.
        // bb0: SwitchInt(d) -> [0: bb1, otherwise: bb2]
        // bb1: base=10; goto bb4    bb2: goto bb3    bb3: base=20; goto bb4
        // bb4 (join): return
        let mut func = three_arm_func();
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, trust_types::BlockId(1))],
                    otherwise: trust_types::BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            arm_assign(1, 10, 4),
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![],
                terminator: Terminator::Goto(trust_types::BlockId(3)),
            },
            arm_assign(3, 20, 4),
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        let merged = branch_merge_definitions(&func, trust_types::BlockId(4), &Default::default());
        assert!(merged.is_empty(), "non-partition join must yield no claim, got {merged:?}");
    }

    #[test]
    fn test_guard_assert_holds_expected_true() {
        let func = test_func();
        let guard =
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: true };
        let formula = guard_to_formula(&func, &guard);
        // expected=true: cond holds, so formula is just the condition var
        // Formula::var() now creates SymVar; match both Var and SymVar.
        assert!(formula.var_name() == Some("flag"), "expected flag var, got: {formula:?}");
    }

    #[test]
    fn test_guard_assert_holds_expected_false() {
        let func = test_func();
        let guard =
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: false };
        let formula = guard_to_formula(&func, &guard);
        // expected=false: assert passes when cond is false, so NOT(cond)
        // Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Not(inner) if inner.var_name() == Some("flag")),
            "expected Not(flag), got: {formula:?}"
        );
    }

    #[test]
    fn test_guard_assert_fails_expected_true() {
        let func = test_func();
        let guard = GuardCondition::AssertFails {
            cond: Operand::Copy(Place::local(2)),
            expected: true,
            msg: AssertMessage::Custom("test".into()),
        };
        let formula = guard_to_formula(&func, &guard);
        // Assert failed: expected true but got false => NOT(cond)
        // Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Not(inner) if inner.var_name() == Some("flag")),
            "expected Not(flag), got: {formula:?}"
        );
    }

    #[test]
    fn test_guards_to_assumption_empty() {
        let func = test_func();
        let assumption = guards_to_assumption(&func, &[]);
        assert_eq!(assumption, Formula::Bool(true));
    }

    #[test]
    fn test_guards_to_assumption_single() {
        let func = test_func();
        let guards = vec![GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: 1,
        }];
        let assumption = guards_to_assumption(&func, &guards);
        // Single guard should not wrap in And
        assert!(matches!(&assumption, Formula::Eq(_, _)), "single guard: {assumption:?}");
    }

    #[test]
    fn test_guards_to_assumption_multiple() {
        let func = test_func();
        let guards = vec![
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(1)), value: 1 },
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: true },
        ];
        let assumption = guards_to_assumption(&func, &guards);
        match &assumption {
            Formula::And(clauses) => assert_eq!(clauses.len(), 2),
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_guarded_formula_empty_guards() {
        let func = test_func();
        let vc = Formula::Not(Box::new(Formula::Bool(true)));
        let result = guarded_formula(&func, &[], vc.clone());
        assert_eq!(result, vc, "empty guards should return formula unchanged");
    }

    #[test]
    fn test_guarded_formula_with_guards() {
        let func = test_func();
        let guards = vec![GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: 1,
        }];
        let vc = Formula::Not(Box::new(Formula::Bool(true)));
        let result = guarded_formula(&func, &guards, vc);
        // Should be And([guard_assumption, vc_formula])
        assert!(matches!(&result, Formula::And(clauses) if clauses.len() == 2));
    }

    #[test]
    fn test_guard_switch_int_match_u128_above_i128_max() {
        let func = test_func();
        // Value above i128::MAX must not be silently truncated
        let large_value: u128 = (i128::MAX as u128) + 1;
        let guard = GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: large_value,
        };
        let formula = guard_to_formula(&func, &guard);
        assert!(
            matches!(&formula, Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::UInt(v) if *v == large_value)),
            "u128 value above i128::MAX should use Formula::UInt, got: {formula:?}"
        );
    }

    #[test]
    fn test_guard_switch_int_otherwise_u128_above_i128_max() {
        let func = test_func();
        let large_value: u128 = u128::MAX;
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![large_value],
        };
        let formula = guard_to_formula(&func, &guard);
        // Should produce Not(Eq(discr, UInt(u128::MAX)))
        assert!(
            matches!(&formula, Formula::Not(inner)
                if matches!(inner.as_ref(), Formula::Eq(_, rhs)
                    if matches!(rhs.as_ref(), Formula::UInt(v) if *v == u128::MAX))),
            "u128::MAX excluded value should use Formula::UInt, got: {formula:?}"
        );
    }

    #[test]
    fn float_comparisons_use_sound_fp_encoding() {
        // Float ordering and general `==`/`!=` are modeled with the IEEE-754
        // FloatingPoint theory (was UNMODELED/fail-closed before the FP theory
        // existed). `fp.*` matches Rust PartialOrd/PartialEq exactly.
        let f = test_func();
        let one = Operand::Constant(ConstValue::Float(1.0));
        let two = Operand::Constant(ConstValue::Float(2.0));

        let lt = super::float_binop_to_formula(&f, BinOp::Lt, &one, &two, 64)
            .expect("float `<` is now modeled");
        assert!(matches!(lt, Formula::FpLt(..)), "expected FpLt, got {lt:?}");
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Le, &one, &two, 64),
            Some(Formula::FpLe(..))
        ));
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Gt, &one, &two, 64),
            Some(Formula::FpGt(..))
        ));
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Ge, &one, &two, 64),
            Some(Formula::FpGe(..))
        ));
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Eq, &one, &two, 64),
            Some(Formula::FpEq(..))
        ));
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Ne, &one, &two, 64),
            Some(Formula::Not(_))
        ));
        // Operands are reinterpreted from their bit patterns via FpFromBits.
        if let Formula::FpLt(l, r) = lt {
            assert!(matches!(*l, Formula::FpFromBits { eb: 11, sb: 53, .. }));
            assert!(matches!(*r, Formula::FpFromBits { eb: 11, sb: 53, .. }));
        }

        // `x == 0.0` keeps its proven magnitude encoding (Eq over a bit-extract).
        let zero = Operand::Constant(ConstValue::Float(0.0));
        let eq0 = super::float_binop_to_formula(&f, BinOp::Eq, &one, &zero, 64)
            .expect("`x == 0.0` stays soundly modeled");
        assert!(matches!(eq0, Formula::Eq(..)), "x==0.0 keeps magnitude encoding, got {eq0:?}");
        assert!(super::float_binop_to_formula(&f, BinOp::Ne, &one, &zero, 64).is_some());

        // Unsupported float widths fail closed.
        assert!(
            super::float_binop_to_formula(&f, BinOp::Lt, &one, &two, 80).is_none(),
            "non-IEEE width must fail closed"
        );
    }

    #[test]
    fn modeled_identity_cast_only_value_preserving() {
        use crate::is_modeled_identity_cast as id;
        // Value-preserving (no-op or non-signed->unsigned widening): identity OK.
        assert!(id(&Ty::u32(), &Ty::u32()));
        assert!(id(&Ty::i32(), &Ty::i32()));
        assert!(id(&Ty::u8(), &Ty::u32()), "unsigned widening (zero-extend) preserves value");
        assert!(id(&Ty::i8(), &Ty::i32()), "signed->signed widening (sign-extend) preserves value");
        assert!(id(&Ty::u8(), &Ty::i32()), "unsigned->wider signed: value fits");
        // Value-changing casts: must NOT be identity (fail-closed).
        assert!(!id(&Ty::u32(), &Ty::u8()), "narrowing truncates");
        assert!(!id(&Ty::i32(), &Ty::u32()), "same-width signedness reinterpret changes value");
        assert!(!id(&Ty::i8(), &Ty::u32()), "signed->unsigned widening wraps negatives");
        assert!(!id(&Ty::i32(), &Ty::i8()), "signed narrowing truncates");
    }

    /// Build a 2-block function: bb0 calls an ascii predicate `callee(ch)` into a
    /// bool local `_b` and switches on it; bb1 is the predicate-TRUE shift block
    /// `_k = ch as u128; r = 1u128 << _k`. `char` lowers to `u32`, so `ch` is a
    /// plain unsigned local. Locals: 0 ret(u128), 1 ch(u32 ≡ char), 2 _b(bool),
    /// 3 _k(u128), 4 r(u128).
    fn ascii_guarded_shift_func(callee: &str) -> VerifiableFunction {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("ch".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("_b".into()) },
            LocalDecl { index: 3, ty: Ty::u128(), name: Some("_k".into()) },
            LocalDecl { index: 4, ty: Ty::u128(), name: Some("r".into()) },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = Ty::u128();
        func.body.blocks = vec![
            // bb0: _b = callee(ch); switch _b -> [0: bb2 (else), otherwise: bb1 (true)]
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
            },
            // bb1 (is_ascii TRUE): _k = ch as u128; r = 1u128 << _k
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u128()),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Shl,
                            Operand::Constant(ConstValue::Uint(1, 128)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            },
            // bb2 (else): return 0
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];
        func
    }

    #[test]
    fn ascii_guard_bounds_shift_amount() {
        // `if ch.is_ascii() { 1u128 << (ch as u128) }`: the is_ascii-TRUE guard
        // must imply `ch <= 127`, which bounds the shift amount below 128 and lets
        // the shift-overflow VC PROVE. The TRUE branch is reached via the switch's
        // `otherwise` edge (the `is_ascii() == true` case), so the guard is
        // `SwitchIntMatch { discr: _b, value: 1 }`.
        let func = ascii_guarded_shift_func("core::char::methods::<impl char>::is_ascii");
        let guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(2)), value: 1 };
        let formula = guard_to_formula(&func, &guard);
        assert!(
            matches!(&formula, Formula::Le(lhs, rhs)
                if lhs.var_name() == Some("ch")
                && matches!(rhs.as_ref(), Formula::Int(127))),
            "is_ascii-TRUE guard must imply `ch <= 127`, got: {formula:?}"
        );

        // The whole ascii predicate family shares the same [0,127] TRUE-set.
        for callee in [
            "core::char::methods::<impl char>::is_ascii_digit",
            "core::char::methods::<impl char>::is_ascii_alphanumeric",
            "core::char::methods::<impl char>::is_ascii_uppercase",
            "core::num::<impl u8>::is_ascii_hexdigit",
        ] {
            let func = ascii_guarded_shift_func(callee);
            let guard =
                GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(2)), value: 1 };
            let formula = guard_to_formula(&func, &guard);
            assert!(
                matches!(&formula, Formula::Le(lhs, rhs)
                    if lhs.var_name() == Some("ch")
                    && matches!(rhs.as_ref(), Formula::Int(127))),
                "{callee} TRUE guard must imply `ch <= 127`, got: {formula:?}"
            );
        }
    }

    #[test]
    fn ascii_guard_does_not_hide_unbounded_shift() {
        // ADVERSARIAL: the predicate-FALSE branch must yield NO `<= 127` bound.
        // `!is_ascii` means `>= 128`; emitting that complement could hide a real
        // out-of-range shift, so the FALSE branch returns the no-fact value.
        // The FALSE case is the explicit `value: 0` target of the switch.
        let func = ascii_guarded_shift_func("core::char::methods::<impl char>::is_ascii");
        let false_guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(2)), value: 0 };
        let false_formula = guard_to_formula(&func, &false_guard);
        assert_eq!(
            false_formula,
            Formula::Bool(true),
            "is_ascii-FALSE branch must yield NO bound (the no-fact value), got: {false_formula:?}"
        );
        // And it must never produce a `<= 127` Le anywhere in the formula.
        assert!(
            !formula_mentions_le_127_on(&false_formula, "ch"),
            "FALSE branch must not emit `ch <= 127`, got: {false_formula:?}"
        );

        // A genuinely-unbounded shift with NO ascii guard at all gets no `<= 127`
        // fact, so its shift-overflow VC still (correctly) refutes:
        // `fn g(n: u32) -> u128 { 1u128 << n }`.
        let mut g = test_func();
        g.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
        ];
        g.body.arg_count = 1;
        g.body.return_ty = Ty::u128();
        // No call, no switch — just an unguarded shift block. `bool_switch_semantics`
        // never fires, and there is no ascii fact in scope.
        assert!(
            ascii_predicate_bound(&g, &Operand::Copy(Place::local(1))).is_none(),
            "an operand with no ascii-predicate call defining it must yield no bound"
        );
    }

    /// True iff `formula` contains an `Le(Var(var), Int(127))` anywhere.
    fn formula_mentions_le_127_on(formula: &Formula, var: &str) -> bool {
        match formula {
            Formula::Le(l, r) => {
                l.var_name() == Some(var) && matches!(r.as_ref(), Formula::Int(127))
            }
            Formula::And(cs) | Formula::Or(cs) => {
                cs.iter().any(|c| formula_mentions_le_127_on(c, var))
            }
            Formula::Not(inner) => formula_mentions_le_127_on(inner, var),
            _ => false,
        }
    }

    #[test]
    fn ascii_guard_bounds_referent_through_autoref_receiver() {
        // Real MIR: a method receiver `b.is_ascii()` lowers to `_5 = &b;
        // is_ascii(move _5)`, so the call argument is a REFERENCE. The bound must
        // land on the referent `b` (_1), NOT the inert reference local `_5` —
        // otherwise the fact never connects to the shift amount and the hardened
        // panic_boundary VC false-refutes a provably-safe ascii-guarded shift.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::Int { width: 8, signed: false }, name: Some("b".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("_b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: Some("_k".into()) },
            LocalDecl { index: 4, ty: Ty::u128(), name: Some("r".into()) },
            LocalDecl { index: 5, ty: Ty::Bool, name: Some("_ref".into()) },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = Ty::u128();
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            // _5 = &b; then is_ascii(move _5) -> _b
            stmts: vec![Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Ref { place: Place::local(1), mutable: false },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func: "core::num::<impl u8>::is_ascii".to_string(),
                args: vec![Operand::Move(Place::local(5))],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                is_foreign: false,
            },
        }];

        let bound = ascii_predicate_bound(&func, &Operand::Copy(Place::local(2)))
            .expect("is_ascii(&b) must still yield a bound");
        assert!(
            matches!(&bound, Formula::Le(lhs, rhs)
                if lhs.var_name() == Some("b")
                && matches!(rhs.as_ref(), Formula::Int(127))),
            "auto-ref receiver bound must be on the referent `b`, not the reference, got: {bound:?}"
        );
    }
}
