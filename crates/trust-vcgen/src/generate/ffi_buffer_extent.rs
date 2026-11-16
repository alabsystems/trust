//! Must-facts for the byte extent of an FFI buffer, at its actual call site.
//!
//! This is deliberately independent of non-nullness: a nonzero address says
//! nothing about its allocation. No extent is inferred from a raw pointer's
//! pointee type, a rendered callee name, a SAFETY comment, or a Vec's capacity.
//! Only live, initialized fixed storage and valid fixed-size reference arguments
//! seed facts. Unknown calls, writes through aliases and lifetime boundaries kill
//! facts; CFG joins retain only identical facts. Unsupported shapes stay unknown.
//!
//! A `become` is a lifetime boundary too (REVIEW-A4C4-MINORS-1 fix-forward,
//! 2026-11-07): the frame ends before the callee runs, so a tail call's facts keep
//! no extent of this frame's storage ([`BufferFacts::across_frame_end`]).

use std::collections::{HashMap, VecDeque};

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Extent {
    owner: usize,
    bytes: u64,
    elements: Option<u64>,
}

#[derive(Clone, Default, PartialEq, Eq)]
pub(super) struct BufferFacts {
    storage: FxHashMap<usize, u64>,
    pointers: FxHashMap<usize, Extent>,
    constants: FxHashMap<usize, u64>,
}

impl BufferFacts {
    fn forget(&mut self, local: usize) {
        self.storage.remove(&local);
        self.pointers.retain(|slot, extent| *slot != local && extent.owner != local);
        self.constants.remove(&local);
    }

    fn meet(&mut self, other: &Self) {
        self.storage.retain(|key, value| other.storage.get(key) == Some(value));
        self.pointers.retain(|key, value| other.pointers.get(key) == Some(value));
        self.constants.retain(|key, value| other.constants.get(key) == Some(value));
    }

    fn pointer(&self, op: &Operand) -> Option<Extent> {
        self.pointers.get(&whole_local(op)?).copied()
    }

    fn constant(&self, op: &Operand) -> Option<u64> {
        match op {
            Operand::Constant(ConstValue::Uint(n, _)) => u64::try_from(*n).ok(),
            Operand::Constant(ConstValue::Int(n)) => u64::try_from(*n).ok(),
            _ => self.constants.get(&whole_local(op)?).copied(),
        }
    }

    pub(super) fn byte_extents(&self, args: &[Operand]) -> HashMap<usize, u64> {
        args.iter().enumerate().filter_map(|(i, op)| Some((i, self.pointer(op)?.bytes))).collect()
    }

    pub(super) fn count(&self, op: &Operand) -> Option<Formula> {
        Some(Formula::Int(i128::from(self.constant(op)?)))
    }

    /// The facts a TAIL call's callee can rely on (REVIEW-A4C4-MINORS-1 fix-forward,
    /// 2026-11-07). `become f(..)` ends this frame before `f` runs: every local's
    /// storage, a parameter's included, is gone, so no extent of it survives, and
    /// neither does the storage map. What survives is what this frame never owned:
    /// the pointee of a reference PARAMETER, which its caller holds borrowed until
    /// the call it made returns (the [`call_facts`] entry seed; LD-2 parameter
    /// validity), and the values of integer constants, which the callee receives by
    /// value. An extent's `owner` tells them apart: the storage map never holds a
    /// reference-typed local ([`byte_size`] has no reference arm), so an extent owned
    /// by a reference parameter can only be that parameter's entry seed or a
    /// reborrow, cast or `as_ptr` of it.
    ///
    /// Without this, `become write(fd, b.as_ptr().cast(), 4)` (`b: [u8; 4]` a local)
    /// and `become write(fd, (&raw const fd).cast(), 4)` (`fd` a parameter) DISCHARGED
    /// "byte count must fit parameter 1 available byte extent (4)": the tail-call
    /// projection reads the call as if this frame outlived it (measured on a stage 1
    /// of the first cut: both rows `proved`).
    fn across_frame_end(&self, func: &VerifiableFunction) -> Self {
        let outlives_frame = |owner: usize| {
            crate::local_defs::body_is_parameter(&func.body, owner)
                && matches!(local_ty(func, owner), Some(Ty::Ref { .. }))
        };
        Self {
            storage: FxHashMap::default(),
            pointers: self
                .pointers
                .iter()
                .filter(|(_, extent)| outlives_frame(extent.owner))
                .map(|(&slot, &extent)| (slot, extent))
                .collect(),
            constants: self.constants.clone(),
        }
    }
}

fn whole_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

fn local_ty(func: &VerifiableFunction, local: usize) -> Option<&Ty> {
    func.body
        .locals
        .get(local)
        .filter(|decl| decl.index == local)
        .or_else(|| func.body.locals.iter().find(|decl| decl.index == local))
        .map(|decl| &decl.ty)
}

/// Exact Rust byte sizes only; unknown layout is never replaced with stride one.
fn byte_size(ty: &Ty) -> Option<u64> {
    byte_size_with_fuel(ty, 64)
}

fn byte_size_with_fuel(ty: &Ty, fuel: u32) -> Option<u64> {
    if fuel == 0 {
        return None;
    }
    match ty {
        Ty::Unit => Some(0),
        Ty::Bool => Some(1),
        Ty::Int { width, .. } if matches!(width, 8 | 16 | 32 | 64 | 128) => {
            Some(u64::from(*width) / 8)
        }
        Ty::Array { elem, len } => byte_size_with_fuel(elem, fuel - 1)?.checked_mul(*len),
        _ => None,
    }
}

fn elements(ty: &Ty) -> Option<u64> {
    match ty {
        Ty::Array { len, .. } => Some(*len),
        _ => None,
    }
}

fn reference_sequence(ty: &Ty) -> bool {
    matches!(ty, Ty::Ref { inner, .. } if matches!(inner.as_ref(), Ty::Array { .. } | Ty::Slice { .. }))
}

fn pointer_cast(from: &Ty, to: &Ty) -> bool {
    match (from, to) {
        (Ty::Ref { .. } | Ty::RawPtr { .. }, Ty::RawPtr { .. }) => true,
        (Ty::Ref { inner: from, .. }, Ty::Ref { inner: to, .. }) => {
            from == to
                || matches!((from.as_ref(), to.as_ref()),
                    (Ty::Array { elem: a, .. }, Ty::Slice { elem: b }) if a == b)
        }
        _ => false,
    }
}

fn borrow(func: &VerifiableFunction, state: &BufferFacts, place: &Place) -> Option<Extent> {
    if place.projections.is_empty() {
        Some(Extent {
            owner: place.local,
            bytes: *state.storage.get(&place.local)?,
            elements: elements(local_ty(func, place.local)?),
        })
    } else if place.projections.as_slice() == [trust_types::Projection::Deref]
        && matches!(local_ty(func, place.local), Some(Ty::Ref { .. }))
    {
        state.pointers.get(&place.local).copied()
    } else {
        None
    }
}

fn stable_pointer_slot(func: &VerifiableFunction, local: usize) -> bool {
    if matches!(local_ty(func, local), Some(Ty::Ref { .. })) {
        // A reborrow through `*r` aliases the pointee, not r's pointer metadata.
        // This existing all-write question still refuses an alias of r itself,
        // every reseating/partial write and every unlocatable write channel.
        crate::local_defs::is_single_static_assignment_modulo_pointee_borrows(func, local)
    } else {
        crate::local_defs::is_single_static_assignment(func, local)
    }
}

fn statement(
    func: &VerifiableFunction,
    slots: &FxHashSet<usize>,
    state: &mut BufferFacts,
    stmt: &Statement,
) {
    match stmt {
        Statement::Assign { place, rvalue, .. } if place.projections.is_empty() => {
            let local = place.local;
            let pointer = match rvalue {
                Rvalue::Ref { mutable, place }
                    if matches!(local_ty(func, local), Some(Ty::Ref { mutable: m, inner })
                    if m == mutable && crate::place_ty_cow(func, place).is_some_and(|ty| ty.as_ref() == inner.as_ref())) =>
                {
                    borrow(func, state, place)
                }
                Rvalue::AddressOf(mutable, place)
                    if matches!(local_ty(func, local), Some(Ty::RawPtr { mutable: m, pointee })
                    if m == mutable && crate::place_ty_cow(func, place).is_some_and(|ty| ty.as_ref() == pointee.as_ref())) =>
                {
                    borrow(func, state, place)
                }
                Rvalue::Use(op)
                    if crate::operand_ty_cow(func, op).as_deref() == local_ty(func, local) =>
                {
                    state.pointer(op)
                }
                Rvalue::Cast(op, to)
                    if Some(to) == local_ty(func, local)
                        && crate::operand_ty_cow(func, op)
                            .is_some_and(|from| pointer_cast(&from, to)) =>
                {
                    state.pointer(op).map(|mut extent| {
                        if matches!(to, Ty::RawPtr { .. }) {
                            extent.elements = None;
                        }
                        extent
                    })
                }
                _ => None,
            };
            let constant = match rvalue {
                Rvalue::Use(op)
                    if crate::operand_ty_cow(func, op).as_deref() == local_ty(func, local) =>
                {
                    state.constant(op)
                }
                Rvalue::Len(place) => borrow(func, state, place).and_then(|extent| extent.elements),
                Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, op)
                    if crate::operand_ty_cow(func, op)
                        .is_some_and(|ty| reference_sequence(&ty)) =>
                {
                    state.pointer(op).and_then(|extent| extent.elements)
                }
                _ => None,
            };
            let initialized = match rvalue {
                Rvalue::Repeat(op, count) => {
                    matches!(local_ty(func, local), Some(Ty::Array { elem, len }) if u64::try_from(*count) == Ok(*len)
                        && crate::operand_ty_cow(func, op).as_deref() == Some(elem.as_ref()))
                }
                Rvalue::Aggregate(trust_types::AggregateKind::Array, ops) => {
                    matches!(local_ty(func, local), Some(Ty::Array { elem, len }) if u64::try_from(ops.len()) == Ok(*len)
                        && ops.iter().all(|op| crate::operand_ty_cow(func, op).as_deref() == Some(elem.as_ref())))
                }
                Rvalue::Use(op) => {
                    crate::operand_ty_cow(func, op).as_deref() == local_ty(func, local)
                        && (whole_local(op).is_some_and(|src| state.storage.contains_key(&src))
                            || matches!(op, Operand::Constant(_)))
                }
                _ => false,
            };
            // A borrow of a pointer/container's metadata can mutate every alias.
            // Unsupported operations likewise never preserve an earlier extent.
            if matches!(rvalue, Rvalue::Unsupported { .. })
                || matches!(rvalue, Rvalue::Ref { .. } | Rvalue::AddressOf(..)) && pointer.is_none()
            {
                *state = BufferFacts::default();
            }
            // Moving a storage value ends the source value's initializedness;
            // copied raw aliases cannot keep its old storage license.
            if let Rvalue::Use(Operand::Move(source)) = rvalue
                && source.projections.is_empty()
                && state.storage.contains_key(&source.local)
            {
                state.forget(source.local);
            }
            state.forget(local);
            if initialized && let Some(bytes) = local_ty(func, local).and_then(byte_size) {
                state.storage.insert(local, bytes);
            }
            if slots.contains(&local)
                && let Some(extent) = pointer
            {
                state.pointers.insert(local, extent);
            }
            if let Some(value) = constant {
                let fits = match local_ty(func, local) {
                    Some(Ty::Int { width, signed }) => {
                        let bits = width.saturating_sub(u32::from(*signed));
                        bits >= 64 || bits > 0 && value < (1u64 << bits)
                    }
                    Some(Ty::PtrSizedInt { signed: false }) => true,
                    _ => false,
                };
                if fits {
                    state.constants.insert(local, value);
                }
            }
        }
        Statement::StorageLive(local) | Statement::StorageDead(local) => state.forget(*local),
        Statement::PlaceMention(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => {}
        // Projected stores, deinit, retag, intrinsics and future variants refuse.
        _ => *state = BufferFacts::default(),
    }
}

/// The facts on a terminator's normal successor edge (`call_facts` gives a call's other
/// edges no facts): [`after_modeled_call`], plus the call's own destination.
///
/// FFI-CALL-DEST-STORAGE-1 (2026-11-01): a call that returns writes its WHOLE
/// destination with the returned value, so on the return edge a whole-local destination
/// of an exactly sized type ([`byte_size`]) is initialized storage of that many bytes,
/// whatever the callee is. Every other fact the callee could invalidate is still killed
/// by [`after_modeled_call`] (an unmodeled call keeps nothing), and the destination's
/// earlier facts are dropped first, so the only fact added is the one the return itself
/// establishes. The extent of a later `&raw const dest` follows from it as from any
/// initialized local (the `let byte = u8::try_from(sig).unwrap_or(0); write(fd, (&raw
/// const byte).cast(), 1)` self-pipe shape of the agy-alab and claude-code-alab signal
/// handlers).
fn after_call(
    func: &VerifiableFunction,
    slots: &FxHashSet<usize>,
    state: &BufferFacts,
    term: &Terminator,
) -> BufferFacts {
    let mut out = after_modeled_call(func, slots, state, term);
    if let Terminator::Call { dest, target: Some(_), .. } = term
        && dest.projections.is_empty()
        && let Some(bytes) = local_ty(func, dest.local).and_then(byte_size)
    {
        out.forget(dest.local);
        out.storage.insert(dest.local, bytes);
    }
    out
}

fn after_modeled_call(
    func: &VerifiableFunction,
    slots: &FxHashSet<usize>,
    state: &BufferFacts,
    term: &Terminator,
) -> BufferFacts {
    let Terminator::Call { dest, args, callee_key, is_foreign: false, .. } = term else {
        return match term {
            Terminator::Goto(_) | Terminator::SwitchInt { .. } | Terminator::Assert { .. } => {
                state.clone()
            }
            _ => BufferFacts::default(),
        };
    };
    let mut out = state.clone();
    let [receiver] = args.as_slice() else { return BufferFacts::default() };
    let key = callee_key.as_ref();
    // Modeled item tags are minted only for real sysroot crates. A carrier
    // contradicting that invariant cannot license extent or length facts.
    if !trust_types::CalleeKey::opt_is_real_sysroot(key) {
        return BufferFacts::default();
    }
    let recv_ty = crate::operand_ty_cow(func, receiver);
    let is_slice = recv_ty.as_ref().is_some_and(|ty| reference_sequence(ty));
    let extent = state.pointer(receiver);
    let accessor = is_slice
        && trust_types::CalleeKey::opt_is_one_of(
            key,
            &[trust_types::SysrootItem::SliceAsPtr, trust_types::SysrootItem::SliceAsMutPtr],
        );
    let cast = matches!(recv_ty.as_deref(), Some(Ty::RawPtr { .. }))
        && trust_types::CalleeKey::opt_is_one_of(key, crate::sep_engine::PTR_CAST_ITEMS);
    let len = is_slice
        && trust_types::CalleeKey::opt_is_one_of(key, &[trust_types::SysrootItem::SliceLen]);
    if !dest.projections.is_empty() || !(accessor || cast || len) {
        return BufferFacts::default();
    }
    out.forget(dest.local);
    if accessor || cast {
        if matches!(local_ty(func, dest.local), Some(Ty::RawPtr { .. }))
            && slots.contains(&dest.local)
            && let Some(mut extent) = extent
        {
            extent.elements = None;
            out.pointers.insert(dest.local, extent);
        }
    } else if let Some(n) = extent.and_then(|extent| extent.elements) {
        out.constants.insert(dest.local, n);
    }
    out
}

/// A bounded least fixed point. Starting empty cannot invent a loop-carried
/// value; every predecessor participates in the intersection, including back
/// edges. On malformed CFG or non-convergence return no facts for any call.
///
/// `tail_call_blocks` is `sep_engine::tail_call_blocks` of the SOURCE model when
/// `func` is its `with_tail_calls_expanded` projection (the generation entry), where
/// a `become` reads as an ordinary call; a block whose terminator ends the frame
/// (`sep_engine::terminator_ends_frame`) records [`BufferFacts::across_frame_end`].
pub(super) fn call_facts(
    func: &VerifiableFunction,
    tail_call_blocks: &trust_types::fx::FxHashSet<BlockId>,
) -> FxHashMap<BlockId, BufferFacts> {
    let blocks = &func.body.blocks;
    if blocks.len() > MAX_SEMANTIC_GUARD_BLOCKS
        || blocks.iter().map(|block| block.stmts.len()).sum::<usize>() > MAX_SEMANTIC_GUARD_STMTS
    {
        return FxHashMap::default();
    }
    let indices: FxHashMap<_, _> =
        blocks.iter().enumerate().map(|(i, block)| (block.id, i)).collect();
    let locals: FxHashSet<_> = func.body.locals.iter().map(|decl| decl.index).collect();
    if indices.len() != blocks.len()
        || !indices.contains_key(&BlockId(0))
        || locals.len() != func.body.locals.len()
    {
        return FxHashMap::default();
    }
    let mut entry = BufferFacts::default();
    // Each slot question enumerates all write channels once, never per iteration.
    let slots: FxHashSet<_> = func
        .body
        .locals
        .iter()
        .filter(|decl| {
            matches!(decl.ty, Ty::Ref { .. } | Ty::RawPtr { .. })
                && stable_pointer_slot(func, decl.index)
        })
        .map(|decl| decl.index)
        .collect();
    for decl in &func.body.locals {
        if crate::local_defs::body_is_parameter(&func.body, decl.index) {
            if let Some(bytes) = byte_size(&decl.ty) {
                entry.storage.insert(decl.index, bytes);
            }
            if let Ty::Ref { inner, .. } = &decl.ty
                && slots.contains(&decl.index)
                && let Some(bytes) = byte_size(inner)
            {
                entry.pointers.insert(
                    decl.index,
                    Extent { owner: decl.index, bytes, elements: elements(inner) },
                );
            }
        }
    }
    let mut predecessors = vec![Vec::new(); blocks.len()];
    let mut successors = vec![Vec::new(); blocks.len()];
    for (i, block) in blocks.iter().enumerate() {
        let mut ok = true;
        let mut add_edge = |successor: BlockId| {
            let Some(&next) = indices.get(&successor) else {
                ok = false;
                return;
            };
            if !predecessors[next].contains(&i) {
                predecessors[next].push(i);
                successors[i].push(next);
            }
        };
        block.terminator.for_each_unguarded_successor(&mut add_edge);
        block.terminator.for_each_exit_block_target(&mut add_edge);
        if !ok {
            return FxHashMap::default();
        }
    }
    let mut outputs = vec![BufferFacts::default(); blocks.len()];
    let mut at_calls = FxHashMap::default();
    let limit = blocks
        .len()
        .saturating_mul(func.body.locals.len().saturating_mul(3).saturating_add(1))
        .saturating_add(1);
    let mut work: VecDeque<_> = (0..blocks.len()).collect();
    let mut queued = vec![true; blocks.len()];
    for _ in 0..limit {
        let Some(i) = work.pop_front() else { return at_calls };
        queued[i] = false;
        let block = &blocks[i];
        let mut state = if block.id == BlockId(0) {
            let mut s = entry.clone();
            for &pred in &predecessors[i] {
                if matches!(&blocks[pred].terminator, Terminator::Call { target, .. } if *target != Some(block.id))
                {
                    s = BufferFacts::default();
                    break;
                }
                s.meet(&outputs[pred]);
            }
            s
        } else if let Some((&first_pred, rest_preds)) = predecessors[i].split_first() {
            if matches!(&blocks[first_pred].terminator, Terminator::Call { target, .. } if *target != Some(block.id))
            {
                BufferFacts::default()
            } else {
                let mut s = outputs[first_pred].clone();
                for &pred in rest_preds {
                    if matches!(&blocks[pred].terminator, Terminator::Call { target, .. } if *target != Some(block.id))
                    {
                        s = BufferFacts::default();
                        break;
                    }
                    s.meet(&outputs[pred]);
                }
                s
            }
        } else {
            BufferFacts::default()
        };
        for stmt in &block.stmts {
            statement(func, &slots, &mut state, stmt);
        }
        let next = after_call(func, &slots, &state, &block.terminator);
        if crate::sep_engine::terminator_ends_frame(&block.terminator, block.id, tail_call_blocks) {
            at_calls.insert(block.id, state.across_frame_end(func));
        } else {
            at_calls.insert(block.id, state);
        }
        if outputs[i] != next {
            outputs[i] = next;
            for &successor in &successors[i] {
                if !queued[successor] {
                    queued[successor] = true;
                    work.push_back(successor);
                }
            }
        }
    }
    FxHashMap::default()
}

#[cfg(test)]
#[path = "ffi_buffer_extent_tests.rs"]
mod tests;
