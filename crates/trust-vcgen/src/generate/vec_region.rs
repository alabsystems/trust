// Trust (VEC-INSERT, 2026-09-25): the PRE-MUTATION REGION of a `Vec` base, and
// the index precondition of `Vec::{remove, swap_remove, insert}` stated over it.
//
// WHY A REGION AND NOT `coll_len`. The owned-container length `coll_len(base)` is
// ONE symbol for the whole body, and it is only ever tied (`.len()`, `is_empty`,
// the scalar-index recovery) when the base's length is stable for the WHOLE body
// (`local_mut_borrows_may_resize`). An index mutator is a resize by definition, so
// that discipline can never speak about it — which is why the mutator row was an
// unconditional `UnsupportedMir` (`vec-panic-method-index-unmodeled`) that no guard
// could discharge (t22: `if !v.is_empty() { v.remove(0) }` was refused).
//
// THE REGION. For a base `b` — a `Vec` by value (a parameter, or a local with ONE
// whole definition that is not on a cycle) or a `&mut Vec` PARAMETER — let
// `Mut(b)` be every block that could change what `b` denotes or its length: every
// write of `b` (whole, through a projection or `Deref`, or as a call destination),
// every `&mut`/raw borrow of `b` (any projection), every MOVE of `b`, every `Drop`
// of `b`. The region is every block that no path reaches from the successors of a
// `Mut(b)` block (the unique definition exempt). On every path from entry to a
// region block the length of `b` is therefore unchanged: it is `L0`, the length at
// entry (a parameter) or right after the definition (a local). The exemption covers
// the DEFINITION only: a `&mut`/raw borrow the definition's block takes and a LATER
// block uses — a two-phase autoref reservation, `v.truncate({ ..; v.len(); 0 })` — ends
// the definition at that one later block, and every block between is outside the
// region (W4 fix round 3, 2026-09-29; `def_block_borrows`). `L0` is a FRESH
// symbol (`__trust_vec_region_len_<b>`), related to nothing but the facts below —
// so no fact minted anywhere else (`coll_len`, a slice length) can conflate it.
//
// THE FACTS (all TRUE forever once minted, because `L0` is a constant):
//   * `_n = Vec::len(&b)` in a region block      =>  `_n == L0`
//   * `_e = Vec::is_empty(&b)` in a region block =>  `_e <=> L0 == 0`
//   * `_s = <Vec as Deref>::deref(&b)` (and `as_slice`) in a region block
//                                                =>  `_s__slice_len == L0`
// Each needs its receiver to be a DIRECT shared borrow of `b` itself (`&b` /
// `&(*b)`) defined in the call's own block — never a value traced through another
// local, so an alias (`let w = v; w.clear()`) cannot stand in for `b` (and `b` is
// dead after such a move anyway).
//
// WHERE THEY ARE MINTED (MUTREF-VEC-LEN-GUARD-REFUTE-1, 2026-10-12). At EVERY such
// call in the region of a region-eligible base, whether or not an index mutator uses
// the base. The argument above never mentions a mutator: `L0` is a constant, and on
// every path to a fact site nothing in `Mut(b)` ran. Minting them only for a base a
// charged mutator used ("no base, no facts: they would constrain a symbol nothing
// reads") was a precision loss, not a soundness gate — two facts over ONE `L0` are
// exactly what relates a guard's `len`/`is_empty` to a later `len`. On a `&mut Vec`
// parameter nothing else does: the `&mut`-parameter havoc at the second `len` call
// severs every other tie, so `if !v.is_empty() { v.len() - 1 }` was `[overflow:sub]
// FAILED` with a counterexample that broke its own guard, until a later `v.remove(r)`
// switched these facts on.
//
// THE FACT IS STATED ON THE CALL'S RETURN EDGE (VEC-REGION-JOIN-SEED-1, 2026-10-12).
// The facts are seeded as ENTRY facts of the call's return target, and an entry fact
// holds on every edge into that block. rustc's `SimplifyCfg` collapses the
// `goto` after an `if`-arm call, so `let n = if c { v.len() } else { 100 }` returns
// from `len` straight into the JOIN, which the `else` arm also enters with `n == 100`:
// `n == L0` was seeded there, and `v.len() - n` was proved (it panics for `c == false`
// and `v.len() < 100`). A fact is minted only when the call's block is the target's
// SOLE predecessor (`call_facts::sole_predecessor_is`, unwind edges counted, `bb0`
// refused), as VEC-LEN-LOOP-1's ties already require.
//
// THE OBLIGATION. `b.remove(i)` / `b.swap_remove(i)` panics iff `i >= len`,
// `b.insert(i, x)` iff `i > len`. At a mutator call `B` whose receiver is a DIRECT
// `&mut` borrow of `b` defined in `B`'s block, with `B` in the region (so `B` is not
// on a cycle through any mutation of `b`, itself included) and no write of `b` in
// `B`'s statements, the length at the call is `L0`, and the violation is
// `i >= L0` / `i > L0`. Anything else keeps the fail-honest `UnsupportedMir` row.
//
// This is a premise about std (the three panic conditions, and that `len`/
// `is_empty`/`deref` report and view the current length) recorded in docs/TCB.md;
// the region itself is a structural CFG argument checked here.
//
// THE CALLEE PREMISE (VEC-REGION-DEF-BLOCK-STASH-1, 2026-10-13). The definition block
// of a local base is exempt from the taint starts, and a `&mut b` it takes is followed
// to its uses (`def_block_borrows`). That is sound only if a callee handed such a
// borrow keeps no alias of `b` past its return: a stash in a `static` followed by a
// resize from a later call that names neither `b` nor the borrow is invisible here. The
// premise is now "a SYSROOT INHERENT callee, handed only references to `b` and
// otherwise pointer-free data, keeps no alias past its return"
// (`call_cannot_retain_borrow`, `call_args_admit_no_alias`); every other callee handed
// the borrow leaves NO region for `b`. The absent-callee row of a dependency callee is
// therefore no longer what stands between a stash and a certified row: it refused the
// strict build only, and the advisory build elided the overflow check the false fact
// proved.
//
// FIELD BASES (VEC-INSERT-FIELD, 2026-10-07). The `Vec` may also be a FIELD path
// under its root — `m.rows` for `m: M` held by value, `(*m).rows` for an `&mut M`
// PARAMETER (`m.rows.insert(0, x)`, trust-ir-conformance `refuse.rs:619`). The base is
// then the place `root.f1.….fn` (a [`VecBase`]), and its region is the ROOT's: every
// write, move, drop or `&mut`/raw borrow of ANY part of the root ends it. That is a
// superset of the mutations of the field (a sibling-field write ends it too — a
// precision loss, never a soundness one), so every argument above holds with `b`
// read as the root. Each field path names its OWN length symbol, so two fields of one
// root (`m.a.len()` guarding `m.b.insert(i, x)`) never share an `L0`. A path through a
// `core::cell` type is refused: a shared borrow of the root could then resize the
// `Vec`, and the region does not count shared borrows.
//
// RESERVED RECEIVERS (VEC-INSERT-FIELD-2, 2026-10-07). When a later argument is itself
// computed by a call (`m.rows.insert(0, mk(k))`, the real `refuse.rs:619` shape), the
// two-phase receiver borrow `_t = &mut root.f` sits in an EARLIER block `D` than the
// call `B`. `D` is then in `Mut(root)`, so `B` is never in the region, and the
// own-block rule above does not see the base. [`reserved_borrow_base`] accepts it when
// `_t` is mentioned nowhere but its definition and `B`'s receiver and `D` touches the
// root through nothing else; the call is then judged in the region of the body with
// the borrow moved to `B` (`Mut - {D} + {B}`, [`VecRegion::clean_with_reservation`]).

use super::*;

/// A region base: the `Vec` at `root` (`fields` empty) or at the field path
/// `root.f1.….fn` (through the one leading `Deref` when `root` is an `&mut`
/// parameter). The region is built over `root`; the length symbol is per path.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct VecBase {
    pub(crate) root: usize,
    pub(crate) fields: Vec<usize>,
}

/// The fresh symbol naming a `Vec` base's length throughout its pre-mutation region.
/// A whole-local base keeps its historical name `__trust_vec_region_len_<root>`; a
/// field base appends `_f<i>` per field, so no two distinct places share a symbol.
pub(crate) fn vec_region_len_var(base: &VecBase) -> Formula {
    use std::fmt::Write;
    let mut name = format!("__trust_vec_region_len_{}", base.root);
    for field in &base.fields {
        let _ = write!(name, "_f{field}");
    }
    Formula::var_owned(name, Sort::Int)
}

/// A std `Vec` type (`Seq` is the modeled spelling of one).
fn is_std_vec(ty: &Ty) -> bool {
    matches!(ty, Ty::Seq { .. })
        || matches!(ty, Ty::Adt { name, .. }
            if matches!(name.split('<').next(), Some("alloc::vec::Vec" | "std::vec::Vec")))
}

/// Is `root` a region-eligible ROOT? A local held by value, or an `&mut` PARAMETER (a
/// `&mut` LOCAL is itself a borrow of something else, whose mutations this analysis
/// would not see). Whether the base place under it is a `Vec` is [`vec_base_of_place`]'s
/// question.
///
/// Trust (2026-10-15, DECISION_QUEUE D101): an `&mut` PARAMETER root is eligible only
/// when no OTHER parameter could reach its pointee
/// ([`super::param_is_sole_channel_to_its_pointee`]). `Mut(b)` counts the writes,
/// borrows, moves and drops that NAME `b`; a second argument that aliased `*b` could
/// resize it without naming it, so a region over an `&mut` root silently assumed the
/// two arguments disjoint — D96's `noalias` premise, which ruling R1 admits only
/// disclosed and demoted. Measured on the stage 1 of the 2026-10-14 merge
/// (`tests/ui/trust/vec_param_length_invariant_loop_refused.rs`): `for i in
/// 0..v.len() { w.clear(); v[i] = 0 }` over `v, w: &mut Vec<u32>` was PROVED with both
/// rows kernel-certified and no premise disclosed, through `_n == L0` at the `len` call.
/// A by-value root cannot be reached through another argument, so it is unaffected.
fn region_root_eligible(func: &VerifiableFunction, root: usize) -> bool {
    let Some(ty) = crate::local_ty_ref(func, root) else { return false };
    match ty {
        Ty::Ref { mutable: true, .. } => {
            root >= 1
                && root <= func.body.arg_count
                && super::param_is_sole_channel_to_its_pointee(func, root)
        }
        Ty::Ref { .. } | Ty::RawPtr { .. } => false,
        _ => true,
    }
}

/// The base a borrowed place names, when it is one: `root` / `*root` (the `&mut`
/// parameter) followed by plain `Field`s only, every step typed, no step through a
/// `core::cell` type (or anything but a struct/tuple), and the place itself a std
/// `Vec`. A `Downcast`, an `Index`, or a second `Deref` is refused.
fn vec_base_of_place(func: &VerifiableFunction, place: &Place) -> Option<VecBase> {
    let mut holder = crate::place_prefix_ty_cow(func, place.local, &[])?;
    let mut pending_variant = None;
    let rest = if matches!(holder.as_ref(), Ty::Ref { .. }) {
        match place.projections.split_first() {
            Some((proj @ trust_types::Projection::Deref, rest)) => {
                holder =
                    crate::place_ty_step(&func.body.datatype_defs, holder, proj, &mut pending_variant)?;
                rest
            }
            _ => return None,
        }
    } else {
        place.projections.as_slice()
    };
    let mut fields = Vec::with_capacity(rest.len());
    for proj in rest {
        let trust_types::Projection::Field(idx) = proj else { return None };
        let plain = match holder.as_ref() {
            Ty::Tuple(_) => true,
            Ty::Adt { name, .. } => {
                !(name.starts_with("core::cell::") || name.starts_with("std::cell::"))
            }
            _ => false,
        };
        if !plain {
            return None;
        }
        holder =
            crate::place_ty_step(&func.body.datatype_defs, holder, proj, &mut pending_variant)?;
        fields.push(*idx);
    }
    is_std_vec(holder.as_ref()).then_some(VecBase { root: place.local, fields })
}

/// `Mut(b)`: every block that could change what `b` denotes or its length.
fn region_mutation_blocks(func: &VerifiableFunction, base: usize) -> FxHashSet<usize> {
    // Writes (whole / projected / call destination) and `&mut`/raw borrows.
    let mut out = local_mutation_blocks(func, base);
    for block in &func.body.blocks {
        if block_mutates_root(block, base, None) {
            out.insert(block.id.0);
        }
    }
    out
}

/// Does `block` put itself in `Mut(base)`, ignoring statement `skip` (the one
/// reservation borrow [`reserved_borrow_base`] moves to its activating call)?
///
/// A superset of [`local_mutation_blocks`]'s per-block test (writes: whole, projected,
/// call destination; `&mut`/raw borrows), plus ANY operand mention of the base, copy
/// or move, any projection. For a `&mut Vec` parameter the extractor hands the
/// reference itself to a `&mut self` callee (`Vec::pop(copy _1)`, no reborrow
/// statement at all), so a mention IS a potential resize; for a `Vec` by value it is a
/// move. The shared reborrows the facts read (`&(*b)` / `&b`) are `Ref` rvalues, not
/// operands, and stay out. An unknown statement or rvalue shape counts as a mutation.
fn block_mutates_root(block: &trust_types::BasicBlock, base: usize, skip: Option<usize>) -> bool {
    let moves = |op: &Operand| matches!(op, Operand::Move(p) | Operand::Copy(p) if p.local == base);
    for (i, stmt) in block.stmts.iter().enumerate() {
        if Some(i) == skip {
            continue;
        }
        let hit = match stmt {
            Statement::Assign { place, rvalue, .. } => {
                let borrows = matches!(rvalue,
                    Rvalue::Ref { mutable: true, place: b } | Rvalue::AddressOf(_, b)
                        if b.local == base);
                let mut moved = false;
                let complete = for_each_rvalue_operand(rvalue, &mut |op| moved |= moves(op));
                place.local == base || borrows || moved || !complete
            }
            Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                place.local == base
            }
            Statement::Intrinsic { args, .. } | Statement::Unsupported { operands: args, .. } => {
                args.iter().any(moves)
            }
            Statement::CopyNonOverlapping { src, dst, count, .. } => {
                [src, dst, count].into_iter().any(moves)
            }
            _ => false,
        };
        if hit {
            return true;
        }
    }
    match &block.terminator {
        Terminator::Call { args, dest, .. } => dest.local == base || args.iter().any(moves),
        Terminator::TailCall { args, .. } => args.iter().any(moves),
        Terminator::Drop { place, .. } => place.local == base,
        _ => false,
    }
}

/// Every rvalue operand, reporting whether the walk was complete (an unknown rvalue
/// shape is `false`, and the caller treats it as a possible move).
fn for_each_rvalue_operand(rvalue: &Rvalue, f: &mut impl FnMut(&Operand)) -> bool {
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            f(op);
            true
        }
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => {
            f(a);
            f(b);
            true
        }
        Rvalue::PtrOffset { ptr, count } => {
            f(ptr);
            f(count);
            true
        }
        Rvalue::Aggregate(_, operands) | Rvalue::Unsupported { operands, .. } => {
            operands.iter().for_each(|op| f(op));
            true
        }
        Rvalue::Ref { .. }
        | Rvalue::AddressOf(..)
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::CopyForDeref(_) => true,
        _ => false,
    }
}

/// What the `&mut`/raw borrows of the base taken in its DEFINITION block leave open
/// (W4 fix round 3, 2026-09-29).
///
/// THE HOLE THIS CLOSES. The definition block is exempt from the taint starts so that
/// the definition starts the region instead of ending it. But the same block can also
/// hold a `&mut b` that is USED only in a later block — a two-phase autoref reservation
/// (`v.truncate({ black_box(0); k = v.len(); 0 })`: `_t = &mut v` in the definition
/// block, `truncate(move _t, 0)` two blocks on). The activating call mentions only
/// `_t`, never `v`, so `region_mutation_blocks` did not see it; the `v.len()` read in
/// between minted `k == L0` at the PRE-truncate length, and a later guarded
/// `v.remove(i)` was charged against that stale `L0` — measured as fourteen
/// kernel-certified false proofs (round-r2 probes v2p01..x14,
/// `tests/ui/trust/vec_index_mutator_region.rs`).
///
/// THE RULE. Seed with every `&mut`/raw borrow of `b` (any projection) in the
/// definition block; close forward over every statement that reads a member (a copy, a
/// reborrow `&mut (*t)`, a cast, an aggregate) and every call handed one (its
/// destination joins, unless it is a pointer-free scalar and every member it was handed
/// is a reference — a `usize` returned from `&mut Vec` carries no borrow of it). Then:
///   * no block but the definition's uses a member: `Closed`, the definition block's
///     own terminator being the last thing that can use them (`let mut v = w;
///     v.push(1)`), exactly as before;
///   * exactly one other block `a` uses them and `a` is on no cycle: `Activation(a)`.
///     Every block reachable from the definition's successors without passing `a` sees
///     the length BEFORE `a` changes it, so none of them is in the region (no fact is
///     minted there and no mutator charged); after `a` the length is the one every
///     later region block sees. This keeps `v.push(v.len())`, then a guarded
///     `v.remove(i)` (probe v2p17);
///   * several blocks use them, or `a` is on a cycle: `Open`, each an ordinary
///     mutation block (its successors leave the region);
///   * a member is a raw pointer, a member is stored through a pointer or handed to an
///     intrinsic copy, or a statement shape is unknown: `Opaque`, no region at all;
///   * a member is handed to a callee that could keep it (VEC-REGION-DEF-BLOCK-STASH-1,
///     2026-10-13): any call [`call_cannot_retain_borrow`] does not credit, a credited
///     call whose arguments [`call_args_admit_no_alias`] refuses, a tail call, or the
///     drop glue of a member that is not a plain reference: `Opaque`, no region at all.
///
/// THE PREMISE (narrowed 2026-10-13, VEC-REGION-DEF-BLOCK-STASH-1). A SYSROOT INHERENT
/// callee handed a borrow of `b` — resident in a real sysroot crate, not a trait method,
/// unstamped, handed only references to `b` and otherwise pointer-free data — keeps no
/// alias of it past its return except through its return value (tracked above). Every
/// other callee leaves no region. The premise used to be "any callee": a dependency
/// that stashed the pointer in a `static` and cleared the `Vec` from a later call made
/// both `len` reads share one `L0`, `v.len() - 1` was kernel-certified, and the advisory
/// build elided its overflow check (the binary returned `usize::MAX`). The callee's own
/// `[trust-absent-callee-assumption]` row refused the strict build, but it refused
/// nothing in the advisory one, and the same callee in the same crate has no such row.
/// Recorded in docs/TCB.md (VEC-INSERT).
enum DefBlockBorrows {
    Closed,
    Activation(usize),
    Open(FxHashSet<usize>),
    Opaque,
}

fn def_block_borrows(
    func: &VerifiableFunction,
    base: usize,
    def_block: &trust_types::BasicBlock,
) -> DefBlockBorrows {
    let mut chain: FxHashSet<usize> = FxHashSet::default();
    for stmt in &def_block.stmts {
        let Statement::Assign { place, rvalue, .. } = stmt else { continue };
        let (Rvalue::Ref { mutable: true, place: borrowed } | Rvalue::AddressOf(_, borrowed)) =
            rvalue
        else {
            continue;
        };
        if borrowed.local != base {
            continue;
        }
        if place_goes_through_pointer(place) {
            return DefBlockBorrows::Opaque;
        }
        chain.insert(place.local);
    }
    if chain.is_empty() {
        return DefBlockBorrows::Closed;
    }
    if !close_borrow_chain(func, &mut chain) {
        return DefBlockBorrows::Opaque;
    }
    // A raw pointer is `Copy` and outlives every borrow check: no region reasons past one.
    let raw_or_unknown = chain.iter().any(|&member| {
        !matches!(
            crate::local_ty_ref(func, member),
            Some(ty) if !matches!(ty, Ty::RawPtr { .. })
        )
    });
    if raw_or_unknown {
        return DefBlockBorrows::Opaque;
    }
    let Some(uses) = borrow_chain_uses(func, &chain, def_block.id.0) else {
        return DefBlockBorrows::Opaque;
    };
    let mut only = uses.iter().copied();
    match (only.next(), only.next()) {
        (None, _) => DefBlockBorrows::Closed,
        (Some(a), None) if !reach_after(func, a).contains(&a) => DefBlockBorrows::Activation(a),
        _ => DefBlockBorrows::Open(uses),
    }
}

/// Does writing `place` store into memory some pointer names (a `Deref` projection)?
fn place_goes_through_pointer(place: &Place) -> bool {
    place.projections.iter().any(|p| matches!(p, trust_types::Projection::Deref))
}

/// Does `op` read a member of `set` (any projection)?
fn operand_reads(op: &Operand, set: &FxHashSet<usize>) -> bool {
    matches!(op, Operand::Copy(p) | Operand::Move(p) if set.contains(&p.local))
}

/// Does `rvalue` read a member of `set`, as an operand or as a borrowed/inspected place?
/// `None`: a shape the operand walk does not know.
fn rvalue_reads(rvalue: &Rvalue, set: &FxHashSet<usize>) -> Option<bool> {
    match rvalue {
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place) => Some(set.contains(&place.local)),
        _ => {
            let mut hit = false;
            let complete = for_each_rvalue_operand(rvalue, &mut |op| hit |= operand_reads(op, set));
            complete.then_some(hit)
        }
    }
}

/// Does `stmt` mention a member of `set` (written, read, borrowed, handed to an
/// intrinsic)? Storage markers, retags and no-ops do not. `None`: an unknown shape.
fn stmt_mentions(stmt: &Statement, set: &FxHashSet<usize>) -> Option<bool> {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            Some(set.contains(&place.local) || rvalue_reads(rvalue, set)?)
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::PlaceMention(place) => Some(set.contains(&place.local)),
        Statement::Intrinsic { args, .. } | Statement::Unsupported { operands: args, .. } => {
            Some(args.iter().any(|op| operand_reads(op, set)))
        }
        Statement::CopyNonOverlapping { src, dst, count, .. } => {
            Some([src, dst, count].into_iter().any(|op| operand_reads(op, set)))
        }
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::Retag { .. }
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => Some(false),
        _ => None,
    }
}

/// Does `terminator` mention a member of `set`?
fn terminator_mentions(terminator: &Terminator, set: &FxHashSet<usize>) -> bool {
    match terminator {
        Terminator::Call { args, dest, .. } => {
            set.contains(&dest.local) || args.iter().any(|op| operand_reads(op, set))
        }
        Terminator::TailCall { args, .. } => args.iter().any(|op| operand_reads(op, set)),
        Terminator::SwitchInt { discr: op, .. } | Terminator::Assert { cond: op, .. } => {
            operand_reads(op, set)
        }
        Terminator::Drop { place, .. } => set.contains(&place.local),
        _ => false,
    }
}

/// Close a borrow chain forward over the whole body (see [`DefBlockBorrows`]). `false`
/// when a member escapes where this walk cannot follow it: stored through a pointer,
/// handed to an intrinsic copy or an unmodeled statement, read by an unknown rvalue,
/// or handed to code that could keep it past its return (VEC-REGION-DEF-BLOCK-STASH-1:
/// a call [`call_cannot_retain_borrow`] does not credit, or one whose arguments
/// [`call_args_admit_no_alias`] refuses; a tail call; the drop glue of a member that is
/// not a plain reference).
fn close_borrow_chain(func: &VerifiableFunction, chain: &mut FxHashSet<usize>) -> bool {
    // An `Opaque` terminator (an indirect call through `dyn Fn`, inline asm, a non-panic
    // diverging call) records no operands, so nothing here could say it is not handed a
    // member. It never reaches this walk: it is an `Unlocatable` write of every local,
    // so `VecRegion::build`'s `has_one_explicit_def` already refuses every local base of
    // such a body (pinned by `vec_region_twophase_tests`).
    loop {
        let before = chain.len();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Statement::Assign { place, rvalue, .. } => match rvalue_reads(rvalue, chain) {
                        None => return false,
                        Some(false) => {}
                        Some(true) => {
                            if place_goes_through_pointer(place) {
                                return false;
                            }
                            chain.insert(place.local);
                        }
                    },
                    Statement::Intrinsic { .. }
                    | Statement::CopyNonOverlapping { .. }
                    | Statement::Unsupported { .. }
                        if stmt_mentions(stmt, chain) != Some(false) =>
                    {
                        return false;
                    }
                    _ => {}
                }
            }
            let (callee, callee_key, args, dest) = match &block.terminator {
                Terminator::Call { func: callee, callee_key, args, dest, .. } => {
                    (callee, callee_key, args, dest)
                }
                // VEC-REGION-DEF-BLOCK-STASH-1: a tail call handed a member is a callee
                // this walk cannot credit (and `become` hands it past this body's end).
                Terminator::TailCall { args, .. } => {
                    if args.iter().any(|op| operand_reads(op, chain)) {
                        return false;
                    }
                    continue;
                }
                // VEC-REGION-DEF-BLOCK-STASH-1: dropping a member that is not a plain
                // reference runs its drop glue, which can be a user `Drop` impl holding
                // the borrow (`struct W<'a>(&'a mut Vec<u8>)` whose `drop` stashes
                // `self.0`). A reference has no glue.
                Terminator::Drop { place, .. } => {
                    if chain.contains(&place.local)
                        && !matches!(
                            crate::place_ty_cow(func, place).as_deref(),
                            Some(Ty::Ref { .. })
                        )
                    {
                        return false;
                    }
                    continue;
                }
                _ => continue,
            };
            if !args.iter().any(|op| operand_reads(op, chain)) {
                continue;
            }
            // VEC-REGION-DEF-BLOCK-STASH-1: the callee must be one whose body is std's,
            // and it must be handed nothing it could keep the borrow in or hand it to.
            // Otherwise no region: a stash here and a resize through it after a later
            // call that names neither the base nor a member would both be invisible.
            if !call_cannot_retain_borrow(callee, callee_key.as_ref())
                || !call_args_admit_no_alias(func, args, chain)
            {
                return false;
            }
            if chain.contains(&dest.local) {
                continue;
            }
            let carries_no_borrow = crate::place_ty_cow(func, dest)
                .is_some_and(|ty| scalar_holds_no_pointer(ty.as_ref()))
                && args.iter().filter(|op| operand_reads(op, chain)).all(|op| {
                    matches!(crate::operand_ty_cow(func, op).as_deref(), Some(Ty::Ref { .. }))
                });
            if carries_no_borrow {
                continue;
            }
            if place_goes_through_pointer(dest) {
                return false;
            }
            chain.insert(dest.local);
        }
        if chain.len() == before {
            return true;
        }
    }
}

/// Can a callee handed a member of a definition-block borrow chain keep no alias of it
/// past its return, other than through its return value (VEC-REGION-DEF-BLOCK-STASH-1,
/// 2026-10-13)?
///
/// THE HOLE THIS CLOSES. `let mut v = w; dep::stash(&mut v); if v.len() == 0 { return 0 }
/// dep::clear_it(); v.len() - 1`, with `stash` storing the pointer in a `static mut` (or
/// an `AtomicPtr`) and `clear_it` clearing the `Vec` through it. The definition block's
/// `&mut v` was `Closed` (its own terminator the only use, a `()` result), so the region
/// started after it; `clear_it` names neither `v` nor a member, so both `len` reads got
/// `_n == L0`, and `v.len() - 1` was PROVED, clean-kernel Certified under every policy,
/// and its overflow check ELIDED by the advisory build: the binary returned
/// `usize::MAX` where rustc panics (no UB under Stacked or Tree Borrows, by the scout's
/// argument; not run under Miri). The same
/// premise let a later ACTIVATION block's callee stash (`DefBlockBorrows::Activation`).
///
/// THE RULE. True only when ALL of these hold:
///   * the callee's `DefId` is in a REAL sysroot crate
///     ([`trust_types::CalleeKey::opt_is_real_sysroot`]: the extractor's
///     artifact-residency verdict, never a name test; no key, as for an indirect call,
///     is false);
///   * the rendering is not trait-qualified (no ` as `): a trait method is keyed on the
///     trait's `DefId` in core while a user impl's body runs (NAME-ANCHOR-2), and the
///     orphan rules admit `impl AddAssign<Local> for Vec<u8>` and
///     `impl IndexMut<Local> for Vec<u8>`;
///   * the rendering carries no unauthenticated-crate stamp
///     ([`trust_types::path_has_unauthenticated_crate_stamp`]).
///
/// Every other callee (user, dependency, foreign, trait method, indirect) leaves no
/// region for the base. What remains is a premise about std, recorded in docs/TCB.md:
/// a sysroot inherent callee handed only references to the base (and, beside them,
/// nothing [`call_args_admit_no_alias`] refuses) keeps no alias of the base past its
/// return except through its return value, which the chain follows.
fn call_cannot_retain_borrow(callee: &str, callee_key: Option<&trust_types::CalleeKey>) -> bool {
    trust_types::CalleeKey::opt_is_real_sysroot(callee_key)
        && !callee.contains(" as ")
        && !trust_types::path_has_unauthenticated_crate_stamp(callee)
}

/// The arguments of a credited call that is handed a borrow-chain member: may the callee
/// neither keep the member in memory reachable from another argument nor hand it to
/// code this walk cannot see (VEC-REGION-DEF-BLOCK-STASH-1)?
///
/// * Every member handed must be a plain reference. A member of any other type (an
///   aggregate holding the borrow, `Some(&mut v)`, a closure capturing it, a call result
///   like `Drain`) can reach user code through a std callee: `Option::map(Some(r), f)`
///   hands `r` to `f`, `core::mem::drop(W(r))` runs `W`'s `Drop`.
/// * Every OTHER argument must be unable to receive an alias or to run code: a scalar
///   constant, or a value or reference whose whole content is pointer-free
///   ([`holds_no_pointer_deep`]). `vv.push(&mut v)` stores the alias in `vv`, and a later
///   dependency call handed `&mut vv` can stash it; a closure or fn item can be handed
///   the member by its std caller. Each is refused, not followed.
fn call_args_admit_no_alias(
    func: &VerifiableFunction,
    args: &[Operand],
    chain: &FxHashSet<usize>,
) -> bool {
    args.iter().all(|op| {
        if operand_reads(op, chain) {
            return matches!(crate::operand_ty_cow(func, op).as_deref(), Some(Ty::Ref { .. }));
        }
        match op {
            // A callable item (`ConstValue::CallableItem`, typed `Unit`), an opaque
            // constant, or anything unrecognized is refused.
            Operand::Constant(cv) => matches!(
                cv,
                ConstValue::Bool(_)
                    | ConstValue::Int(_)
                    | ConstValue::Uint(..)
                    | ConstValue::Float(_)
                    | ConstValue::FloatBits { .. }
                    | ConstValue::Unit
                    | ConstValue::Str { .. }
                    | ConstValue::OpaqueScalar { .. }
                    | ConstValue::ConstParam { .. }
            ),
            Operand::Copy(_) | Operand::Move(_) => {
                crate::operand_ty_cow(func, op).is_some_and(|ty| match ty.as_ref() {
                    Ty::Ref { inner, .. } => holds_no_pointer_deep(inner),
                    other => holds_no_pointer_deep(other),
                })
            }
            _ => false,
        }
    })
}

/// A value of this type holds no pointer anywhere in its content, so nothing can be
/// stored in it but plain data and no user code is reachable from it: a pointer-free
/// scalar ([`scalar_holds_no_pointer`]), `str`, or a slice, array or std `Vec` of
/// pointer-free scalars. Anything else (an ADT, a closure, a reference, a raw pointer, a
/// collection of them) is refused.
fn holds_no_pointer_deep(ty: &Ty) -> bool {
    match ty {
        Ty::Str => true,
        Ty::Slice { elem }
        | Ty::Array { elem, .. }
        | Ty::SymArray { elem, .. }
        | Ty::Seq { elem, .. } => scalar_holds_no_pointer(elem),
        other => scalar_holds_no_pointer(other),
    }
}

/// A pointer-free scalar (or a tuple of them): a value of this type returned by a
/// callee handed a REFERENCE carries no borrow of its referent.
fn scalar_holds_no_pointer(ty: &Ty) -> bool {
    match ty {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Bv(_)
        | Ty::Unit
        | Ty::Never => true,
        Ty::Tuple(elems) => elems.iter().all(scalar_holds_no_pointer),
        _ => false,
    }
}

/// Every block other than `def` that mentions a member of `chain` (`None`: an unknown
/// statement shape).
fn borrow_chain_uses(
    func: &VerifiableFunction,
    chain: &FxHashSet<usize>,
    def: usize,
) -> Option<FxHashSet<usize>> {
    let mut uses = FxHashSet::default();
    for block in &func.body.blocks {
        if block.id.0 == def {
            continue;
        }
        let mut hit = terminator_mentions(&block.terminator, chain);
        for stmt in &block.stmts {
            hit |= stmt_mentions(stmt, chain)?;
        }
        if hit {
            uses.insert(block.id.0);
        }
    }
    Some(uses)
}

/// Every block reachable from `starts` without passing through `stop` (`stop` itself
/// included when reached, its successors not walked from it).
fn reachable_until(
    func: &VerifiableFunction,
    starts: impl IntoIterator<Item = usize>,
    stop: usize,
) -> FxHashSet<usize> {
    let mut seen = FxHashSet::default();
    let mut stack: Vec<usize> = starts.into_iter().collect();
    while let Some(b) = stack.pop() {
        if b >= func.body.blocks.len() || !seen.insert(b) || b == stop {
            continue;
        }
        for_each_v2_terminator_target(&func.body.blocks[b].terminator, |t| stack.push(t.0));
    }
    seen
}

/// The pre-mutation region of one base.
pub(crate) struct VecRegion {
    clean: FxHashSet<usize>,
    mutation: FxHashSet<usize>,
    /// The unique definition block of a local root, exempt from the taint starts.
    exempt: Option<usize>,
    /// The activation of a two-phase borrow the definition block opened.
    activation: Option<usize>,
    /// The blocks between the definition and `activation` (always outside the region).
    window: FxHashSet<usize>,
}

impl VecRegion {
    /// The region of the ROOT local `base` (see FIELD BASES in the header): every
    /// base place under it shares it.
    pub(crate) fn build(func: &VerifiableFunction, base: usize) -> Option<Self> {
        if !region_root_eligible(func, base) {
            return None;
        }
        let mut mutation = region_mutation_blocks(func, base);
        let is_param = base >= 1 && base <= func.body.arg_count;
        // A local's unique whole definition starts the region rather than ending it —
        // unless it is on a cycle, where it would mint a fresh length per iteration.
        let mut exempt: Option<usize> = None;
        // The one block that completes a two-phase borrow the definition block opened,
        // and the blocks between the two (`DefBlockBorrows::Activation`).
        let mut activation: Option<usize> = None;
        let mut window: FxHashSet<usize> = FxHashSet::default();
        if !is_param {
            if !crate::local_defs::has_one_explicit_def(func, base) {
                return None;
            }
            let def_block = crate::find_local_write_candidate(
                func,
                &func.body.blocks,
                base,
                |block, item| {
                    let hit = match item {
                        Some(stmt) => matches!(stmt, Statement::Assign { place, .. }
                            if place.local == base && place.projections.is_empty()),
                        None => matches!(&block.terminator, Terminator::Call { dest, .. }
                            if dest.local == base && dest.projections.is_empty()),
                    };
                    hit.then_some(block)
                },
            )?;
            let d = def_block.id.0;
            // The definition block must write `base` ONLY as that whole definition.
            let projected_write = def_block.stmts.iter().any(|stmt| {
                matches!(stmt, Statement::Assign { place, .. }
                    if place.local == base && !place.projections.is_empty())
            });
            if projected_write || reach_after(func, d).contains(&d) {
                return None;
            }
            exempt = Some(d);
            // The exemption covers the DEFINITION, not every borrow its block takes
            // (W4 fix round 3, 2026-09-29): see `def_block_borrows`.
            match def_block_borrows(func, base, def_block) {
                DefBlockBorrows::Closed => {}
                DefBlockBorrows::Opaque => return None,
                DefBlockBorrows::Open(uses) => mutation.extend(uses),
                DefBlockBorrows::Activation(a) => {
                    // Every block between the definition and `a` sees the length
                    // BEFORE `a` changes it: none of them is in the region. `a`'s own
                    // successors are, unless `a` is a mutation block on its own account.
                    let mut succ_d = Vec::new();
                    for_each_v2_terminator_target(&def_block.terminator, |t| succ_d.push(t.0));
                    window = reachable_until(func, succ_d, a);
                    if !mutation.contains(&a) {
                        activation = Some(a);
                    }
                    mutation.insert(a);
                }
            }
        }
        // Every block reachable from the SUCCESSORS of a non-exempt mutation block —
        // the union of `reach_after(m)` over them, computed as ONE multi-source walk
        // (W4 fix round 2, 2026-09-26). One walk per mutation block made a body of n
        // guarded removes cost O(n * blocks) per region, and a region is built per
        // base per pass: measured 382 s at n = 600 against 188 s on the base compiler.
        let mut starts = Vec::new();
        for &m in &mutation {
            if Some(m) != exempt
                && Some(m) != activation
                && let Some(b) = func.body.blocks.get(m)
            {
                for_each_v2_terminator_target(&b.terminator, |succ| starts.push(succ.0));
            }
        }
        let mut tainted = reachable_from_all(func, starts);
        tainted.extend(window.iter().copied());
        let clean =
            (0..func.body.blocks.len()).filter(|b| !tainted.contains(b)).collect::<FxHashSet<_>>();
        Some(Self { clean, mutation, exempt, activation, window })
    }

    /// Is the call block `call` in the region of the body in which the reservation
    /// borrow of block `reserve` is taken at `call` instead (see
    /// [`reserved_borrow_base`])? `reserve` must be in `Mut` on that borrow's account
    /// ONLY (the caller checks), so the modified `Mut` is `Mut - {reserve} + {call}`:
    /// one walk from the successors of every other mutation block and of `call`
    /// itself (so `call` on a cycle through itself is out), plus the definition window.
    fn clean_with_reservation(
        &self,
        func: &VerifiableFunction,
        reserve: usize,
        call: usize,
    ) -> bool {
        // The definition block and the activation of its own two-phase borrow are
        // exempt from the taint starts already; a reservation there is not this shape.
        if !self.mutation.contains(&reserve)
            || Some(reserve) == self.exempt
            || Some(reserve) == self.activation
            || Some(call) == self.exempt
            || self.window.contains(&call)
        {
            return false;
        }
        let mut starts: Vec<usize> = Vec::new();
        for &m in &self.mutation {
            if m != reserve
                && Some(m) != self.exempt
                && Some(m) != self.activation
                && let Some(b) = func.body.blocks.get(m)
            {
                for_each_v2_terminator_target(&b.terminator, |succ| starts.push(succ.0));
            }
        }
        // `call` is the mutation now, whatever its role before (an `activation` included).
        let Some(call_block) = func.body.blocks.get(call) else { return false };
        for_each_v2_terminator_target(&call_block.terminator, |t| starts.push(t.0));
        !reachable_from_all(func, starts).contains(&call)
    }

    fn fact_site_ok(&self, block: usize) -> bool {
        self.clean.contains(&block) && !self.mutation.contains(&block)
    }

    #[cfg(test)]
    pub(crate) fn is_clean(&self, block: usize) -> bool {
        self.clean.contains(&block)
    }
}

/// Every block reachable from any of `starts` (each start included).
fn reachable_from_all(
    func: &VerifiableFunction,
    starts: impl IntoIterator<Item = usize>,
) -> FxHashSet<usize> {
    let mut seen = FxHashSet::default();
    let mut stack: Vec<usize> = starts.into_iter().collect();
    while let Some(b) = stack.pop() {
        if b >= func.body.blocks.len() || !seen.insert(b) {
            continue;
        }
        for_each_v2_terminator_target(&func.body.blocks[b].terminator, |t| stack.push(t.0));
    }
    seen
}

/// Blocks reachable from the SUCCESSORS of `block` (so `block` itself only through a
/// cycle).
fn reach_after(func: &VerifiableFunction, block: usize) -> FxHashSet<usize> {
    let Some(b) = func.body.blocks.get(block) else { return FxHashSet::default() };
    let mut starts = Vec::new();
    for_each_v2_terminator_target(&b.terminator, |t| starts.push(t.0));
    reachable_from_all(func, starts)
}

/// If `op` is a temp whose ONLY definition, inside `block`, is a direct borrow of a
/// region base (`&b`/`&mut b` for a `Vec` by value, `&(*b)`/`&mut (*b)` for a `&mut
/// Vec` parameter, or the same through a field path, `&mut (*m).rows`), that base.
fn direct_borrow_base(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: &Operand,
    mutable: bool,
) -> Option<VecBase> {
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    // A `&mut Vec` PARAMETER handed to a `&mut self` callee as itself (the
    // extractor's spelling of the implicit reborrow): the receiver IS the base.
    if mutable
        && p.local >= 1
        && p.local <= func.body.arg_count
        && matches!(
            crate::local_ty_ref(func, p.local),
            Some(Ty::Ref { mutable: true, inner }) if is_std_vec(inner)
        )
    {
        return Some(VecBase { root: p.local, fields: Vec::new() });
    }
    if crate::local_defs::is_parameter(func, p.local)
        || !crate::local_defs::has_one_explicit_def(func, p.local)
    {
        return None;
    }
    let place = block.stmts.iter().find_map(|stmt| match stmt {
        Statement::Assign { place: dest, rvalue: Rvalue::Ref { mutable: m, place }, .. }
            if dest.local == p.local && dest.projections.is_empty() && *m == mutable =>
        {
            Some(place)
        }
        _ => None,
    })?;
    vec_base_of_place(func, place)
}

/// A mutator receiver whose `&mut` borrow was RESERVED in an earlier block: the
/// two-phase autoref of a call whose later argument is itself computed by a call
/// (`m.rows.insert(0, mk(k))`, `v.insert(0, mk(k))`, trust-ir-conformance
/// `refuse.rs:619`), which MIR spells
///
/// ```text
/// bbD: { _t = &mut ((*_1).0); _e = mk(copy _k) -> bbB }
/// bbB: { _r = Vec::insert(move _t, const 0, move _e) -> .. }
/// ```
///
/// (VEC-INSERT-FIELD-2, 2026-10-07). The borrow puts `bbD` in `Mut(root)`, so the
/// call is never in the root's region, and [`direct_borrow_base`] (borrow in the call's
/// own block) does not see it. The base, and the block `D` holding the reservation, when:
///   * `_t` is a plain `&mut` local with ONE explicit definition, `_t = &mut <place>`,
///     in a block `D` other than the call's, and `<place>` is a [`vec_base_of_place`];
///   * `_t` is mentioned NOWHERE else in the body but as the call's receiver — not
///     copied, reborrowed, written through, dropped, or handed to `D`'s terminator, and
///     not in any statement of the call's block — so between `D` and the call nothing
///     can use the borrow, and the length it reaches is the one `D` borrowed;
///   * `D` is in `Mut(root)` on THAT borrow's account only (no other write, move, drop,
///     borrow or mention of the root in `D`: [`block_mutates_root`] with it skipped).
///
/// Then moving the borrow statement from `D` to the head of the call block changes no
/// length anywhere, and the caller asks the region of THAT body
/// ([`VecRegion::clean_with_reservation`]): `Mut - {D} + {call}`.
fn reserved_borrow_base(
    func: &VerifiableFunction,
    call_block: &trust_types::BasicBlock,
    recv: &Operand,
) -> Option<(VecBase, usize)> {
    let Operand::Move(p) = recv else { return None };
    if !p.projections.is_empty()
        || crate::local_defs::is_parameter(func, p.local)
        || !crate::local_defs::has_one_explicit_def(func, p.local)
    {
        return None;
    }
    let t = p.local;
    if !matches!(
        crate::local_ty_ref(func, t),
        Some(Ty::Ref { mutable: true, .. })
    ) {
        return None;
    }
    let mut reservation: Option<(usize, usize, &Place)> = None;
    crate::visit_local_write_indexed_stmts(func, &func.body.blocks, t, |block, i, stmt| {
        if reservation.is_none()
            && block.id != call_block.id
            && let Statement::Assign {
                place: dest,
                rvalue: Rvalue::Ref { mutable: true, place },
                ..
            } = stmt
            && dest.local == t
            && dest.projections.is_empty()
        {
            reservation = Some((block.id.0, i, place));
        }
    });
    let (d, stmt_index, place) = reservation?;
    let base = vec_base_of_place(func, place)?;
    let d_block = func.body.blocks.get(d).filter(|b| b.id.0 == d)?;
    if block_mutates_root(d_block, base.root, Some(stmt_index)) {
        return None;
    }
    let only_t: FxHashSet<usize> = std::iter::once(t).collect();
    // The receiver, and nothing else of the call, names `_t`.
    let Terminator::Call { args, dest, .. } = &call_block.terminator else { return None };
    if dest.local == t || args.iter().skip(1).any(|op| operand_reads(op, &only_t)) {
        return None;
    }
    for block in &func.body.blocks {
        let is_call = block.id == call_block.id;
        for (i, stmt) in block.stmts.iter().enumerate() {
            if block.id.0 == d && i == stmt_index {
                continue;
            }
            if stmt_mentions(stmt, &only_t) != Some(false) {
                return None;
            }
        }
        if !is_call && terminator_mentions(&block.terminator, &only_t) {
            return None;
        }
    }
    Some((base, d))
}

/// Is `callee` the genuine std `Vec` inherent method `name`?
fn callee_is_std_vec_method(callee: &str, name: &str) -> bool {
    method_tail(callee) == name && !callee.contains(" as ") && {
        let c = callee.strip_prefix('<').unwrap_or(callee);
        c.starts_with("alloc::vec::Vec") || c.starts_with("std::vec::Vec")
    }
}

/// The violation of `Vec::{remove, swap_remove, insert}`'s index precondition at the
/// mutator call terminating `block`, over the base's region length — or `None` when
/// the call is not one or the region does not reach it (the caller then keeps the
/// fail-honest `UnsupportedMir` row).
pub(crate) fn vec_mutator_index_violation(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<Formula> {
    vec_mutator_index_violation_in(func, block, &mut FxHashMap::default())
}

/// Each base's region, built at most once per pass over a body (`None`: the base is
/// not region-eligible). A region is a pure function of `(func, base)`.
/// Keyed by the ROOT local: every base under one root shares its region.
type RegionMemo = FxHashMap<usize, Option<VecRegion>>;

/// [`vec_mutator_index_violation`], reusing the regions already built in `regions`.
fn vec_mutator_index_violation_in(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    regions: &mut RegionMemo,
) -> Option<Formula> {
    charged_mutator(func, block, regions).map(|(_, violation)| violation)
}

/// The base a charged index mutator terminating `block` is charged against, and the
/// violation of its index precondition (see [`vec_mutator_index_violation`]).
fn charged_mutator(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    regions: &mut RegionMemo,
) -> Option<(VecBase, Formula)> {
    let Terminator::Call { func: callee, args, .. } = &block.terminator else { return None };
    let insert = if ["remove", "swap_remove"].iter().any(|m| callee_is_std_vec_method(callee, m)) {
        false
    } else if callee_is_std_vec_method(callee, "insert") {
        true
    } else {
        return None;
    };
    let (recv, idx) = (args.first()?, args.get(1)?);
    if !matches!(crate::operand_ty_cow(func, idx).as_deref(), Some(Ty::Int { signed: false, .. })) {
        return None;
    }
    let (base, reserved_in) = match direct_borrow_base(func, block, recv, true) {
        Some(base) => (base, None),
        None => {
            let (base, d) = reserved_borrow_base(func, block, recv)?;
            (base, Some(d))
        }
    };
    let root = base.root;
    let region = regions.entry(root).or_insert_with(|| VecRegion::build(func, root)).as_ref()?;
    let in_region = match reserved_in {
        None => region.clean.contains(&block.id.0),
        Some(d) => region.clean_with_reservation(func, d, block.id.0),
    };
    if !in_region {
        return None;
    }
    // No statement of the call's own block may write the root before the call.
    if block.stmts.iter().any(|stmt| {
        matches!(stmt, Statement::Assign { place, .. } if place.local == root)
            || matches!(stmt, Statement::Assign { rvalue: Rvalue::AddressOf(_, place), .. }
                if place.local == root)
    }) {
        return None;
    }
    let len = vec_region_len_var(&base);
    let idx_f = crate::operand_to_formula(func, idx);
    let violated = if insert {
        Formula::Gt(Box::new(idx_f), Box::new(len.clone()))
    } else {
        Formula::Ge(Box::new(idx_f), Box::new(len.clone()))
    };
    // `L0` is a length: conjoining `0 <= L0` onto the violation is a true fact.
    let violation =
        Formula::And(vec![Formula::Ge(Box::new(len), Box::new(Formula::Int(0))), violated]);
    Some((base, violation))
}

/// Which region fact a call could mint, decided from the callee alone in
/// [`vec_region_definitions`] (the anchors are the ones the facts always had).
#[derive(Clone, Copy)]
enum RegionFactCall {
    /// `Vec::len`, by the inherent method and the shared total-`len` matcher.
    Len,
    /// `Vec::is_empty`.
    IsEmpty,
    /// `<Vec as Deref>::deref` / `Vec::as_slice` (std's own view impl).
    View,
}

/// The region facts, per block, at every `len` / `is_empty` / `deref` / `as_slice`
/// call that reads a region-eligible base through a DIRECT shared borrow in the call's
/// own block, inside that base's region (see THE FACTS and WHERE THEY ARE MINTED in the
/// header). Each fact is seeded at the call's return target, so it is minted only when
/// the call is that target's sole predecessor (VEC-REGION-JOIN-SEED-1). A root's region
/// is built at most once, and only for a root some such call reads.
pub(crate) fn vec_region_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return out;
    }
    let mut regions = RegionMemo::default();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, target: Some(target), .. } =
            &block.terminator
        else {
            continue;
        };
        if !dest.projections.is_empty() {
            continue;
        }
        // The callee first, so a region is built only for a root a fact site reads.
        let kind = if callee_is_std_vec_method(callee, "len")
            && trust_types::total_call_summaries::total_summary_len_call(callee)
        {
            RegionFactCall::Len
        } else if callee_is_std_vec_method(callee, "is_empty") {
            RegionFactCall::IsEmpty
        } else if guards::callee_is_std_vec_slice_view(callee)
            && matches!(method_tail(callee), "deref" | "as_slice")
        {
            RegionFactCall::View
        } else {
            continue;
        };
        let Some(recv) = args.first() else { continue };
        let Some(base) = direct_borrow_base(func, block, recv, false) else { continue };
        // The fact holds on the call's RETURN EDGE only; seeded at a target another
        // edge also enters, it would be read on that edge too (VEC-REGION-JOIN-SEED-1).
        if !super::call_facts::sole_predecessor_is(func, *target, block.id) {
            continue;
        }
        let root = base.root;
        let Some(region) =
            regions.entry(root).or_insert_with(|| VecRegion::build(func, root)).as_ref()
        else {
            continue;
        };
        if !region.fact_site_ok(block.id.0) {
            continue;
        }
        let len = vec_region_len_var(&base);
        let dest_place = Place::local(dest.local);
        let fact = match kind {
            RegionFactCall::Len => Formula::Eq(
                Box::new(crate::operand_to_formula(func, &Operand::Copy(dest_place))),
                Box::new(len),
            ),
            RegionFactCall::IsEmpty => {
                let empty = crate::operand_to_formula(func, &Operand::Copy(dest_place));
                if !matches!(empty, Formula::Var(_, Sort::Bool)) {
                    continue;
                }
                let zero = Formula::Eq(Box::new(len), Box::new(Formula::Int(0)));
                Formula::Or(vec![
                    Formula::And(vec![empty.clone(), zero.clone()]),
                    Formula::And(vec![Formula::Not(Box::new(empty)), Formula::Not(Box::new(zero))]),
                ])
            }
            RegionFactCall::View => {
                // SLICE-VIEW-ANCHOR-1: the trait-method text cannot authenticate the
                // impl, so the receiver must be std's `Vec` by its own MIR type, as at the
                // other view-equation site (`slice_last_some_nonempty_definitions`). For a
                // direct borrow of the base that type is the base's; asking keeps the
                // two sites one rule.
                let (Operand::Copy(recv_place) | Operand::Move(recv_place)) = recv else {
                    continue;
                };
                if !guards::receiver_is_std_vec(func, recv_place) {
                    continue;
                }
                let Some(view_len) = crate::slice_len_formula(func, &Operand::Copy(dest_place))
                else {
                    continue;
                };
                Formula::Eq(Box::new(view_len), Box::new(len))
            }
        };
        out.entry(*target).or_default().push(fact);
    }
    out
}

/// Trust (VEC-INSERT, 2026-09-25): `<[T]>::binary_search{,_by,_by_key}` returns
/// `Ok(i)` with `i < len` or `Err(i)` with `i <= len` (the insertion point) — the std
/// contract, recorded in docs/TCB.md. Seeded ONLY at the arm targets of a switch on
/// the result's discriminant in the call's DIRECT target block, which must hold
/// nothing but that discriminant read (the `slice.get` Some-arm discipline), over a
/// SHARED slice receiver whose length is modeled.
///
/// THE RESULT LOCAL MUST HOLD THIS CALL'S VALUE AT EVERY READ (W4 fix round 1,
/// 2026-09-25). The fact is stated over the payload NAME `r@v.0`, and nothing
/// versions or kills that name across a later write of `r` unless the place-name
/// algebra relates the two — which it did not (`@`, the `Downcast` spelling, was no
/// projection separator; closed separately in `path_defs::place_names_overlap`). So
/// the fact is minted only when the call is `r`'s ONE definition in the whole body
/// (`local_defs::body_unique_defining_block`: no second whole write, no field or
/// discriminant store, no `&mut`/raw escape, not a parameter) and `r` is
/// `place_source_is_stable` — the gate `base_value_alias` already asks of an enum
/// payload it rebases onto. MEASURED without it, on `0.10.0+g0a25d1c42`, four
/// kernel-certified false proofs: `r = Err(big); if let Err(p) = r { v.insert(p, x) }`
/// inside the `Err` arm (r12), `r = Ok(big); if let Ok(j) = r { v[j] }` (r12b),
/// `r = w.binary_search_by(..)` over a LONGER `w` then `v.insert(p, x)` (r12c), and
/// `r = Ok(big); if let Ok(j) = r { j + 1 }` on a plain slice, whose verified build
/// dropped the overflow check and returned a wrapped value (r12d). Pinned by
/// `tests/ui/trust/vec_bsearch_result_stale_fact.rs`.
pub(crate) fn slice_binary_search_result_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let tp = super::terminator_presence_for(func);
    if !tp.has_bare_dest_call || !tp.has_switch_int {
        return out;
    }
    let blocks = &func.body.blocks;
    for (block_index, b) in blocks.iter().enumerate() {
        let Terminator::Call { func: callee, args, dest, target: Some(target), .. } = &b.terminator
        else {
            continue;
        };
        if !dest.projections.is_empty()
            || !matches!(
                method_tail(callee),
                "binary_search" | "binary_search_by" | "binary_search_by_key"
            )
            || callee.contains(" as ")
            || !(callee.starts_with("core::slice::")
                || callee.starts_with("std::slice::")
                || callee.starts_with("<["))
        {
            continue;
        }
        // The call is the result local's ONLY value, and nothing can change it in
        // place (see the doc above).
        if crate::local_defs::body_unique_defining_block(&func.body, dest.local)
            != Some(block_index)
            || !crate::place_source_is_stable(func, dest.local)
        {
            continue;
        }
        let Some(recv) = args.first() else { continue };
        let recv_shared_slice = matches!(
            crate::operand_ty_cow(func, recv).as_deref(),
            Some(Ty::Ref { mutable: false, inner }) if matches!(inner.as_ref(), Ty::Slice { .. })
        );
        if !recv_shared_slice {
            continue;
        }
        let Some(len_f) = crate::slice_len_formula(func, recv) else { continue };
        // The result must be a `Result<usize, usize>`.
        let Some(Ty::Adt { name, .. }) = crate::local_ty_ref(func, dest.local) else {
            continue;
        };
        if name.split('<').next() != Some("core::result::Result") {
            continue;
        }
        let Some(tb) = blocks.get(target.0).filter(|tb| tb.id == *target) else { continue };
        let mut disc_local = None;
        let mut clean = true;
        for s in &tb.stmts {
            match s {
                Statement::Assign { place, rvalue: Rvalue::Discriminant(src), .. }
                    if place.projections.is_empty()
                        && src.projections.is_empty()
                        && src.local == dest.local =>
                {
                    disc_local = Some(place.local);
                }
                _ => {
                    clean = false;
                    break;
                }
            }
        }
        let (true, Some(disc_local)) = (clean, disc_local) else { continue };
        let Terminator::SwitchInt { discr, targets, .. } = &tb.terminator else { continue };
        if !matches!(discr, Operand::Copy(p) | Operand::Move(p)
            if p.local == disc_local && p.projections.is_empty())
        {
            continue;
        }
        // `Result::Ok` is variant 0, `Result::Err` variant 1.
        for (variant, strict) in [(0u128, true), (1u128, false)] {
            let Some(arm) = targets.iter().find(|(v, _)| *v == variant).map(|(_, t)| *t) else {
                continue;
            };
            let payload = Place {
                local: dest.local,
                projections: vec![
                    trust_types::Projection::Downcast(variant as usize),
                    trust_types::Projection::Field(0),
                ],
            };
            let value = Formula::var_owned(crate::place_to_var_name(func, &payload), Sort::Int);
            let fact = if strict {
                Formula::Lt(Box::new(value), Box::new(len_f.clone()))
            } else {
                Formula::Le(Box::new(value), Box::new(len_f.clone()))
            };
            out.entry(arm).or_default().push(fact);
        }
    }
    out
}

/// Trust (VEC-INSERT, 2026-09-25): the call blocks at which a `Vec` index mutator is
/// charged its REAL index precondition by [`vec_mutator_index_violation`] — the
/// compiler reads this to decide, per call site, that the mutator's one
/// caller-value panic (the index check) is demanded of this body, so the call is
/// no longer a "panics on a caller-supplied value" callee THERE.
pub fn vec_mutator_charged_blocks(func: &VerifiableFunction) -> Vec<BlockId> {
    if super::cached_terminator_presence_for_body(&func.body).is_some_and(|tp| !tp.has_call) {
        return Vec::new();
    }
    // Asked by the compiler outside vcgen's generation scope, like the rows below.
    let _entry_scope = super::EntryScope::enter(func);
    if !super::terminator_presence_for(func).has_call {
        return Vec::new();
    }
    let mut regions = RegionMemo::default();
    func.body
        .blocks
        .iter()
        .filter(|block| vec_mutator_index_violation_in(func, block, &mut regions).is_some())
        .map(|block| block.id)
        .collect()
}

/// Trust (VEC-INSERT, 2026-09-25): the exact identity of each charged mutator row —
/// `(call block, call span, recorded obligation body)`, the body normalized exactly
/// as the pipeline's final pass normalizes a `SliceBoundsCheck` row. The compiler
/// keeps a charged block only when a row with THIS identity is present in the
/// root's generated inventory, so a row a later stage dropped never licenses the
/// call's vanilla verdict.
pub fn vec_mutator_charge_rows(func: &VerifiableFunction) -> Vec<(BlockId, SourceSpan, Formula)> {
    if super::cached_terminator_presence_for_body(&func.body).is_some_and(|tp| !tp.has_call) {
        return Vec::new();
    }
    // The compiler calls this OUTSIDE vcgen's generation scope, so without its own
    // scope every charged block rebuilt the statement-version oracle (two whole-CFG
    // fixpoints) — the second hot frame of the n = 600 profile. A miss only costs
    // time: the memoized value is the same pure function of `func`. `EntryScope`: the
    // analysis frame and the work memos (place names, havoc lists) both.
    let _entry_scope = super::EntryScope::enter(func);
    if !super::terminator_presence_for(func).has_call {
        return Vec::new();
    }
    let mut regions = RegionMemo::default();
    func.body
        .blocks
        .iter()
        .filter_map(|block| {
            let violation = vec_mutator_index_violation_in(func, block, &mut regions)?;
            let Terminator::Call { span, .. } = &block.terminator else { return None };
            let sv = super::stmt_versions_for(func);
            let body = version_rename_owned_at(violation, &sv, func, block.id, block.stmts.len());
            Some((block.id, span.clone(), normalize_ssa_version_tokens_owned(func, body)))
        })
        .collect()
}
