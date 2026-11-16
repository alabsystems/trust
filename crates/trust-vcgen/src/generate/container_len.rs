// Length reasoning for owned containers: a `Vec` created empty and only ever
// pushed to under the same dominating guard has a provable length bound, and a
// struct field holding such a `Vec` keys a per-field length map. Also the
// windowed/chunked slice iterators, whose yields inherit the base slice's
// length, and the non-null locals an FFI boundary establishes.

use super::*;

/// The std container accessors whose result is NON-NULL for every receiver, the
/// only calls [`is_std_container_as_ptr`] admits. Each takes its receiver BY
/// REFERENCE (`&self` / `&mut self` on `[T]`, `str`, `Vec<T>` or `CStr`), so the
/// pointer it returns is derived from a valid reference, or is `Vec`'s
/// `NonNull::dangling()` buffer for an unallocated vector: never null.
///
/// Deliberately ABSENT (Trust, 2026-10-04, ASPTR-KEY-1):
///  * [`trust_types::SysrootItem::RawSlicePtrAsPtr`] /
///    [`trust_types::SysrootItem::RawSlicePtrAsMutPtr`] —
///    `<*const [T]>::as_ptr` returns `self as *const T`, which is null exactly
///    when the raw slice pointer is (`slice_from_raw_parts(null(), 0).as_ptr()`
///    prints `0x0`). The string recognizer this replaces admitted it whenever the
///    generic argument spelled a container path (`<impl *const [VecDeque<u8>]>`
///    contains `vec_deque`).
///  * `StringAsPtr` — declared for an older sysroot and unreachable here; a
///    `String` receiver reaches `StrAsPtr` through `Deref`.
///  * the other declared `as_ptr` items (`NonNull`, `Box`, `Cell`, `Rc`, …): the
///    string recognizer never admitted them, and widening the fact is not this
///    change's business.
pub(super) const STD_NONNULL_AS_PTR_ITEMS: &[trust_types::SysrootItem] = &[
    trust_types::SysrootItem::SliceAsPtr,
    trust_types::SysrootItem::SliceAsMutPtr,
    trust_types::SysrootItem::VecAsPtr,
    trust_types::SysrootItem::VecAsMutPtr,
    trust_types::SysrootItem::StrAsPtr,
    trust_types::SysrootItem::StrAsMutPtr,
    trust_types::SysrootItem::CStrAsPtr,
];

/// Whether the call keyed `callee_key` is a std container's inherent raw-pointer
/// accessor whose result is never null ([`STD_NONNULL_AS_PTR_ITEMS`]). This
/// licenses a non-null fact for FFI arguments.
///
/// Trust (2026-10-04, ASPTR-KEY-1): decided on the compiler-minted key, never on
/// the rendered path. The string test this replaces wanted an `as_ptr` leaf, a
/// `core`/`std`/`alloc` root and a container substring ANYWHERE in the path, so
/// `core::ptr::const_ptr::<impl *const [alloc::collections::vec_deque::VecDeque<u8>]>::as_ptr`
/// — the raw-slice `as_ptr`, null for a null receiver — took its `vec_deque` from
/// the generic argument and deleted the `strlen: parameter 0 must be non-null` row
/// under every policy (measured on `scratchpad/stage1-w11fix`; the program
/// segfaults). `None` (an indirect call, a pre-carrier producer) is false.
pub(super) fn is_std_container_as_ptr(callee_key: Option<&trust_types::CalleeKey>) -> bool {
    trust_types::CalleeKey::opt_is_one_of(callee_key, STD_NONNULL_AS_PTR_ITEMS)
}

/// True iff the single whole-local def of `local` is an EMPTY `Vec` constructor
/// (`Vec::new` / `Vec::with_capacity`). A non-empty / unknown creation (`vec![..]`,
/// `to_vec`, `collect`, `Vec::from`, or a plain `Assign`) declines: only an empty
/// start makes EVERY later element a guarded push. Caller ensures the def is unique.
pub(super) fn vec_created_empty(func: &VerifiableFunction, local: usize) -> bool {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return false;
    }
    crate::find_local_write_term(func, &func.body.blocks, local, |_block, term| {
        if let Terminator::Call { func: callee, dest, .. } = term
            && dest.local == local
            && dest.projections.is_empty()
        {
            return Some(
                vc_callee_is_std_vec_inherent(callee)
                    && matches!(method_tail(callee), "new" | "with_capacity"),
            );
        }
        None
    })
    .unwrap_or(false)
}

/// True iff EVERY `&mut local` / `&raw local` borrow's dest is single-def and used
/// SOLELY as the receiver (arg 0) of a `Vec::push` call — the push-only mutation
/// discipline. A projected `&mut local[..]`, a projected/reused borrow-dest, or a
/// borrow reaching pop/truncate/clear/remove/insert/extend/swap or any escape → false.
/// Modeled on [`iter_mut_borrows_only_feed_next`].
pub(super) fn vec_mut_borrows_only_feed_push(func: &VerifiableFunction, local: usize) -> bool {
    let mut conduits: Vec<usize> = Vec::new();
    if crate::any_local_write_stmt(func, &func.body.blocks, local, |_block, stmt| {
        if let Statement::Assign { place: dst, rvalue, .. } = stmt
            && let Rvalue::Ref { mutable: true, place: b } | Rvalue::AddressOf(_, b) = rvalue
            && b.local == local
        {
            // A projected `&mut m[..]` / `&mut m.f`, or a projected borrow-dest, is
            // not the whole-Vec push receiver — fail closed.
            if !b.projections.is_empty() || !dst.projections.is_empty() {
                return true;
            }
            conduits.push(dst.local);
        }
        false
    }) {
        return false;
    }
    if conduits.is_empty() {
        return true;
    }
    if !conduits.iter().all(|&t| crate::local_defs::has_one_explicit_def(func, t)) {
        return false;
    }
    let is_conduit = |l: usize| conduits.contains(&l);
    for block in &func.body.blocks {
        for s in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = s {
                // A write THROUGH the conduit (`*t = other_vec`, which REPLACES m)
                // voids the discipline; the sole whole-local def (the `&mut m`
                // borrow) is admitted (a second one is caught by the def-count).
                if is_conduit(place.local) && !place.projections.is_empty() {
                    return false;
                }
                let mut used = false;
                let complete = for_each_rvalue_operand_place(rvalue, &mut |pl| {
                    if is_conduit(pl.local) {
                        used = true;
                    }
                });
                // An rvalue the walker cannot enumerate is a read it cannot rule
                // out — refuse, like a read.
                if used || !complete {
                    return false;
                }
            }
            // A `SetDiscriminant`/`Deinit` through the conduit likewise mutates m.
            if matches!(s,
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if is_conduit(place.local))
            {
                return false;
            }
        }
        match &block.terminator {
            Terminator::Call { func: callee, args, dest, .. } => {
                if is_conduit(dest.local) {
                    return false;
                }
                for (i, a) in args.iter().enumerate() {
                    if let Operand::Copy(pl) | Operand::Move(pl) = a
                        && is_conduit(pl.local)
                        && !(i == 0
                            && method_tail(callee) == "push"
                            && vc_callee_is_std_vec_inherent(callee))
                    {
                        return false;
                    }
                }
            }
            Terminator::SwitchInt { discr, .. } => {
                if matches!(discr, Operand::Copy(pl) | Operand::Move(pl) if is_conduit(pl.local)) {
                    return false;
                }
            }
            Terminator::Assert { cond, .. } => {
                if matches!(cond, Operand::Copy(pl) | Operand::Move(pl) if is_conduit(pl.local)) {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

/// Blocks that WRITE `local` (whole/projected/call-dest store) OR take a `&mut`/raw
/// borrow of it — the sites at which its value (a `Vec`'s length) can change.
pub(super) fn local_mutation_blocks(func: &VerifiableFunction, local: usize) -> FxHashSet<usize> {
    let mut out = local_write_blocks(func, local);
    crate::visit_local_write_stmts(func, &func.body.blocks, local, |block, s| {
        if let Statement::Assign { rvalue, .. } = s
            && let Rvalue::Ref { mutable: true, place: b } | Rvalue::AddressOf(_, b) = rvalue
            && b.local == local
        {
            out.insert(block.id.0);
        }
    });
    out
}

/// The block that DEFINES the length operand `len_op` reads (a `X.len()` call, a
/// `Len(X)`, or a `PtrMetadata(&X)`), traced through whole-local `Use`-copies to the
/// defining site. `None` if not found. Used to bound "the snapshot point" for the
/// row-stability check.
pub(super) fn len_def_block(
    func: &VerifiableFunction,
    len_op: &Operand,
    fuel: u32,
) -> Option<usize> {
    let root = operand_root_local(func, len_op, fuel)?;
    // The scan below returns the FIRST defining block; it is an answer only when the
    // root has ONE explicit definition (`local_defs::has_one_explicit_def` counts the
    // `Call` dest and the `Assign` channels alike). The caller ALSO requires the block
    // to dominate the push, which a two-definition root cannot satisfy — this gate
    // makes the first-block read honest on its own rather than by that accident.
    if !crate::local_defs::has_one_explicit_def(func, root) {
        return None;
    }
    crate::find_local_write_candidate(func, &func.body.blocks, root, |block, item| match item {
        Some(s) => {
            if let Statement::Assign { place, rvalue, .. } = s
                && place.local == root
                && place.projections.is_empty()
                && matches!(
                    rvalue,
                    Rvalue::Len(_) | Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, _)
                )
            {
                Some(block.id.0)
            } else {
                None
            }
        }
        None => {
            // Trust (2026-10-03, NAME-ANCHOR-1): std's length, not a method named `len`.
            // Trust (2026-10-06, LEN-KEY-1): or its DefId key, which a duplicate-crate-name
            // graph's `::<__trust_args@…>` tag does not hide.
            if let Terminator::Call { func: callee, dest, callee_key, .. } = &block.terminator
                && dest.local == root
                && dest.projections.is_empty()
                && is_std_inherent_len_call_or_key(callee, callee_key.as_ref())
            {
                Some(block.id.0)
            } else {
                None
            }
        }
    })
}

/// True iff `rowbase` is mutated (resized/reseated/`&mut`-borrowed) on some path
/// STRICTLY BETWEEN the length-snapshot block `lblk` and the `push_block`, within
/// one loop iteration (paths that re-enter `lblk` are cut). When true, the guard's
/// `len(row) > n` snapshot may not equal the pushed length — fail closed.
pub(super) fn row_resized_between(
    func: &VerifiableFunction,
    lblk: usize,
    push_block: usize,
    rowbase: usize,
) -> bool {
    let mutations = local_mutation_blocks(func, rowbase);
    if mutations.is_empty() || (mutations.len() == 1 && mutations.contains(&lblk)) {
        return false;
    }
    let avoid = one_block_set(lblk);
    let mut post: FxHashSet<usize> = FxHashSet::default();
    if let Some(b) = func.body.blocks.get(lblk) {
        for_each_v2_terminator_target(&b.terminator, |succ| {
            post.extend(reachable_avoiding(func, succ.0, &avoid));
        });
    }
    for m in mutations {
        if m == lblk {
            continue;
        }
        if post.contains(&m)
            && (m == push_block
                || reachable_avoiding_one_contains(func, m, Some(lblk), push_block))
        {
            return true;
        }
    }
    false
}

/// The `(true_target, false_target)` of a boolean `SwitchInt`.
pub(super) fn bool_switch_branch_targets(
    targets: &[(u128, BlockId)],
    otherwise: BlockId,
) -> Option<(BlockId, BlockId)> {
    let t1 = targets.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t);
    let t0 = targets.iter().find(|(v, _)| *v == 0).map(|(_, t)| *t);
    match (t1, t0) {
        (Some(a), Some(b)) => Some((a, b)),
        (Some(a), None) => Some((a, otherwise)),
        (None, Some(b)) => Some((otherwise, b)),
        (None, None) => None,
    }
}

/// A STABLE bound operand for the push guard — one whose modeled value is IDENTICAL at
/// the guard and at the element read (else the fact `coll_len(m[k]) > n` would use a
/// different `n` than the push guard proved): a constant, or a projection-free local
/// that is [`place_source_is_stable`] (defined at most once, never in-place mutated) AND
/// — if a by-value PARAMETER — never reassigned at all (a param reassigned once passes
/// `place_source_is_stable`'s `<= 1` count yet carries TWO values: the incoming arg and
/// the reassignment, which the SSA versioning splits — so it is NOT a stable bound).
pub(super) fn operand_is_stable_bound(func: &VerifiableFunction, op: &Operand) -> bool {
    match op {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            crate::place_source_is_stable(func, p.local)
                && crate::local_defs::never_explicitly_reseated(func, p.local)
        }
        _ => false,
    }
}

/// If the `Vec::push` in `push_block` (pushing `rowbase`) is DOMINATED by a guard
/// that proves `len(rowbase) > bound` on the push edge, return that stable `bound`.
///
/// A guard is a `SwitchInt` on `_c = BinaryOp(cmp, l, r)` with one side the length of
/// `rowbase` ([`operand_is_len_of_base`]) and the other a stable bound. The four
/// strictly-`>`-yielding shapes are accepted (`len<=n` false-edge, `len>n` true-edge,
/// `n<len` true-edge, `n>=len` false-edge). Dominance is checked structurally: the
/// guard block dominates the push, the "too-short" edge cannot reach the push, the
/// length-snapshot block dominates the push, and `rowbase` is unresized between snapshot
/// and push — so the snapshot length equals the pushed length. Fail-closed on anything else.
pub(super) fn push_guarded_bound(
    func: &VerifiableFunction,
    push_block: usize,
    rowbase: usize,
    fuel: u32,
) -> Option<Operand> {
    for gblock in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &gblock.terminator else {
            continue;
        };
        let Some(c) = operand_root_local(func, discr, fuel) else { continue };
        let Some(Rvalue::BinaryOp(cmp, opl, opr)) = crate::local_defs::unique_value_def(func, c)
        else {
            continue;
        };
        // Identify the length side and the (stable) bound side, and which edge proves
        // `len > bound`. Only strict-`>` shapes are admitted.
        let (bound_op, len_op, good_is_true) = if operand_is_len_of_base(func, opl, rowbase, fuel) {
            match cmp {
                BinOp::Le => (opr, opl, false),
                BinOp::Gt => (opr, opl, true),
                _ => continue,
            }
        } else if operand_is_len_of_base(func, opr, rowbase, fuel) {
            match cmp {
                BinOp::Lt => (opl, opr, true),
                BinOp::Ge => (opl, opr, false),
                _ => continue,
            }
        } else {
            continue;
        };
        if !operand_is_stable_bound(func, bound_op) {
            continue;
        }
        let Some((true_t, false_t)) = bool_switch_branch_targets(targets, *otherwise) else {
            continue;
        };
        let (good_t, bad_t) = if good_is_true { (true_t, false_t) } else { (false_t, true_t) };
        let Some(lblk) = len_def_block(func, len_op, fuel) else { continue };
        let g = gblock.id.0;
        // The guard dominates the push (every path to the push passes through it),
        // the "too-short" edge does NOT reach the push, and the "long-enough" edge does.
        if reachable_avoiding_one_contains(func, 0, Some(g), push_block)
            || reachable_avoiding_one_contains(func, bad_t.0, Some(g), push_block)
            || !reachable_avoiding_one_contains(func, good_t.0, Some(g), push_block)
        {
            continue;
        }
        // The length snapshot dominates the push, and `rowbase` is not resized between
        // the snapshot and the push (else the snapshot length != the pushed length).
        if reachable_avoiding_one_contains(func, 0, Some(lblk), push_block)
            || row_resized_between(func, lblk, push_block, rowbase)
        {
            continue;
        }
        return Some(bound_op.clone());
    }
    None
}

/// Operand equality by modeled value (same constant, or same place) — used to require
/// ALL pushes into `m` share ONE guard bound `n`. Compared via `operand_to_formula`
/// so a stable local and a constant each map to their canonical SMT term; distinct
/// locals (even same-named) get distinct terms (the `place_to_var_name` collision
/// guard), so this can only conflate genuinely-equal bounds.
pub(super) fn operand_bounds_equal(func: &VerifiableFunction, a: &Operand, b: &Operand) -> bool {
    operand_to_formula(func, a) == operand_to_formula(func, b)
}

/// The single stable bound `n` such that EVERY `Vec::push(&mut m, row)` is dominated
/// by a guard proving `len(row) > n`, or `None` if m has no pushes, a push is
/// unguarded, or the pushes disagree on `n`.
pub(super) fn pushes_all_guarded_same_bound(
    func: &VerifiableFunction,
    mi: usize,
    fuel: u32,
) -> Option<Operand> {
    let mut bound: Option<Operand> = None;
    let mut saw_push = false;
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, .. } = &block.terminator else { continue };
        if args.len() < 2
            || method_tail(callee) != "push"
            || !vc_callee_is_std_vec_inherent(callee)
        {
            continue;
        }
        let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else { continue };
        if !recv.projections.is_empty()
            || guards::base_collection_local_unique(func, recv.local) != Some(mi)
        {
            continue;
        }
        saw_push = true;
        let row_op = args.get(1)?;
        let (Operand::Copy(rp) | Operand::Move(rp)) = row_op else { return None };
        if !rp.projections.is_empty() {
            return None;
        }
        let row_local = operand_root_local(func, row_op, fuel)?;
        let rowbase = guards::base_collection_local_unique(func, row_local)?;
        let b = push_guarded_bound(func, block.id.0, rowbase, fuel)?;
        match &bound {
            None => bound = Some(b),
            Some(prev) => {
                if !operand_bounds_equal(func, prev, &b) {
                    return None;
                }
            }
        }
    }
    if saw_push { bound } else { None }
}

/// True iff `local`'s type — after peeling at most one `&`/`&mut` — is an owned
/// `Vec` (the nested element whose `coll_len` the inner bound reads).
pub(super) fn local_peeled_is_vec(func: &VerifiableFunction, local: usize) -> bool {
    let Some(ty) = crate::local_ty_ref(func, local) else { return false };
    let inner = match ty {
        Ty::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    ty_is_owned_vec(inner)
}

/// Per-block push-guarded element-length facts (`coll_len(m[k]) > n`). See the
/// section banner for the recognizer, the fact shape, and every soundness gate.
pub(super) fn build_push_guard_elem_len_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const FUEL: u32 = 16;
    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let presence = super::terminator_presence_for(func);
    if !presence.has_std_scalar_index_call || !presence.has_switch_int {
        return map;
    }

    for decl in &func.body.locals {
        let mi = decl.index;
        // (A) m is an owned Vec, created EMPTY, single-def, never in-place mutated, and
        // mutated ONLY by `Vec::push` (no shrink / element overwrite / &mut escape).
        // Trust (IDX-TIE-1, 2026-10-03): std's `Vec` by exact path. The last-segment
        // test (`is_owned_slice_container_name`) also admitted a user type named `Vec`,
        // whose element reads need not be any of the rows pushed. `ty_is_owned_vec`
        // asks `Ty::Seq` (the extractor's std `Vec`) or an ADT that passes
        // `is_std_vec_adt_name`, so the `Seq` migration does not blind this gate.
        if crate::local_defs::is_parameter(func, mi)
            || !ty_is_owned_vec(&decl.ty)
            || !crate::local_defs::has_one_explicit_def(func, mi)
            || !vec_created_empty(func, mi)
            || local_has_projected_write(func, mi)
            || !vec_mut_borrows_only_feed_push(func, mi)
        {
            continue;
        }
        // (B) every push is dominated by a guard proving `len(row) > n` for one stable n.
        let Some(bound) = pushes_all_guarded_same_bound(func, mi, FUEL) else { continue };
        let bound_f = operand_to_formula(func, &bound);

        // (C) for every element read `_e = <Vec<Vec<T>> as Index>::index(&m, k)`, emit
        // `coll_len(base(_e)) > n` — the SAME var the inner bound `col < m[k].len()` reads.
        for block in &func.body.blocks {
            let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
                continue;
            };
            // Trust (IDX-TIE-1, 2026-10-03): std's OWN `Index<usize>::index`. The fact
            // below says the element read is one of the pushed rows, which only std's
            // impl guarantees; a user method named `index` returns what its body does.
            if !dest.projections.is_empty()
                || args.len() < 2
                || !super::unwrap_panic::is_std_scalar_index_call(callee)
            {
                continue;
            }
            let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else { continue };
            if !recv.projections.is_empty()
                || guards::base_collection_local_unique(func, recv.local) != Some(mi)
            {
                continue;
            }
            let d = dest.local;
            // Only a nested `Vec` element carries a `coll_len` the inner bound reads; a
            // scalar element (`Vec<i64>`) has no inner index and must not be over-claimed.
            if !local_peeled_is_vec(func, d) {
                continue;
            }
            let Some(base) = guards::base_collection_local_unique(func, d) else { continue };
            let fact =
                Formula::Gt(Box::new(guards::coll_len_var(func, base)), Box::new(bound_f.clone()));
            for b2 in &func.body.blocks {
                if block_mentions_local(b2, d) {
                    map.entry(b2.id).or_default().push(fact.clone());
                }
            }
        }
    }
    map
}

// ======================================================================
// Dominating length-guard facts for a PROJECTED-place (struct-field) Vec index
//   `let m = self.g.len();
//    if self.p_lo.len() != m { return Err(..) }      // or `< m` / `<= m` / `== m`
//    for j in 0..m { ... self.p_lo[j] ... }`          // j < m == len(self.p_lo)
// ======================================================================
//
// The scalar index `self.p_lo[j]` lowers to `<Vec<T> as Index>::index(&self.p_lo, j)`
// and rides the #7c owned-Vec scalar-index arm, whose bounds obligation is
// `j >= coll_len(_recv)` where `_recv = &(*self).p_lo` is the index call's receiver
// temp (`collection_abstract_len_with_base_opts` mints `coll_len_var(_recv)` — the
// base-tracer CANNOT follow a borrow of a PROJECTED place, so the base stays the temp
// itself). That var is FREE, so the solver refutes with `coll_len(_recv) == 0, j == 0`.
//
// The dominating guard `if self.p_lo.len() != m { return }` DOES pin the length, but
// through a DIFFERENT temp: its `.len()` receiver `_lenrecv = &(*self).p_lo` is a
// SEPARATE local, so the existing `.len()` tie seeds `_len == coll_len(_lenrecv)` and
// the continue edge gives `_len == m` — i.e. `coll_len(_lenrecv) == m` — but the read
// carries `coll_len(_recv)`, a distinct var the guard never reaches. (A WHOLE-local
// `&Vec` receiver has NO such split: both temps trace to the one param base, so the
// existing tie already unifies them — hence this recognizer fires ONLY for a projected
// receiver, where the gap lives.)
//
// The missing fact is `coll_len(_recv) >= m` — the SAME var the bound reads — which is
// SOUND because both `_recv` and `_lenrecv` borrow the identical field place
// `(*self).p_lo`, the field is immutable across the function (so its length is stable),
// and the guard returns on every too-short edge. With the loop range `j < m` (supplied
// by the range machinery) this discharges `j < m <= coll_len(_recv)`.
//
// SOUNDNESS (a false slice-bounds PROVE is a memory-safety false-proof):
//  * the emitted var is EXACTLY the VC's `coll_len` (`collection_abstract_len_with_base_opts`
//    with `peel_shared_ref = true` — identical to the arm that builds the obligation), so
//    the fact cannot land on a different length than the bound reads;
//  * the read receiver must borrow a PROJECTED place (a struct FIELD) via a SHARED ref;
//  * that PLACE must hold one value across the whole function (`place_is_body_stable`:
//    its root's slot is stable, and a place behind the root's `Deref` is additionally
//    reached through a reference root with no second `Deref`, no pointer that can write
//    under the root — `&mut`, `&raw mut` or `&raw const` of any place rooted at it — and
//    no interior-mutability hop), so the field's length is invariant between guard and
//    read. Until 2026-09-30 this asked `place_source_is_stable` (the root's SLOT) alone,
//    which leaves `&raw const (*self)` off by design, and a callee handed `&raw const
//    *self as *mut _` cleared the `Vec` between a guard and a kernel-certified index;
//  * a dominating guard must compare `len(place)` (a `.len()` result over a borrow of the
//    SAME place, or a `Len(place)`/`PtrMetadata`) against a STABLE bound `C`
//    (`operand_is_stable_bound`), on a shape whose GOOD (non-return) edge implies a lower
//    bound `len(place) >= C` / `> C` (decoded per operator — `!=`/`==`/`</<=/>/>=`; any
//    shape that does not soundly reduce to a lower bound emits NOTHING);
//  * dominance is structural (F1-style `reachable_avoiding`): the guard dominates the
//    read, the too-short edge CANNOT reach it, the long-enough edge does. Fail closed on
//    anything else — an unrecoverable receiver, a mutated field, an unstable `C`, a
//    guard on a DIFFERENT place, or an edge polarity that yields no lower bound.
/// The place a reference temp borrows: if `local`'s unique whole-local def is
/// `_local = &PLACE` / `&mut PLACE` / `&raw [const|mut] PLACE`, return
/// `(PLACE, mutable_of_the_borrow)`. None when `local` has no unique whole def or
/// its def is not a borrow.
pub(super) fn ref_target_of_local(
    func: &VerifiableFunction,
    local: usize,
) -> Option<(&Place, bool)> {
    if crate::local_defs::is_parameter(func, local) {
        return None;
    }
    match crate::local_defs::unique_value_def(func, local)? {
        Rvalue::Ref { mutable, place } => Some((place, *mutable)),
        Rvalue::AddressOf(mutable, place) => Some((place, *mutable)),
        _ => None,
    }
}

/// True iff `op` is the length of EXACTLY the place `place`: a projection-free local
/// `_len`, UNIQUELY whole-defined (so it stably names `len(place)`), whose def is
///   (a) a std `.len()` Call ([`is_std_inherent_len_call`]) whose sole receiver
///       borrows exactly `place`, or
///   (b) a `Len(place)` / `PtrMetadata(&place)` rvalue.
/// Matches by the borrowed PLACE (not a base local), so it recognizes a projected
/// field's length where `operand_is_len_of_base` (base-local keyed) cannot.
///
/// Trust (2026-10-03, NAME-ANCHOR-1): arm (a) keyed on `method_tail(callee) ==
/// "len"` alone, so a user trait method NAMED `len` on the field was read as its
/// length, and `build_len_guard_field_map` turned `if j < L::len(&w.v)` into
/// `coll_len(w.v) > j`: `slice proved`, kernel-certified, on an index that panics
/// (`tests/ui/trust/len_guard_field_user_trait_len.rs`).
pub(super) fn operand_is_len_of_place(
    func: &VerifiableFunction,
    op: &Operand,
    place: &Place,
) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return false };
    if !p.projections.is_empty() || !crate::local_defs::has_one_explicit_def(func, p.local) {
        return false;
    }
    // (a) `_len = <std>::len(&place)`.
    if let Some(hit) = crate::find_local_write_term(func, &func.body.blocks, p.local, |_block, term| {
        // Trust (2026-10-06, LEN-KEY-1): or its DefId key (see
        // `is_std_inherent_len_call_or_key`).
        if let Terminator::Call { func: callee, args, dest, callee_key, .. } = term
            && dest.local == p.local
            && dest.projections.is_empty()
            && is_std_inherent_len_call_or_key(callee, callee_key.as_ref())
        {
            let Some(Operand::Copy(rp) | Operand::Move(rp)) = args.first() else {
                return Some(false);
            };
            if !rp.projections.is_empty() {
                return Some(false);
            }
            return Some(
                matches!(ref_target_of_local(func, rp.local), Some((tp, _)) if tp == place),
            );
        }
        None
    }) {
        return hit;
    }
    // (b) `_len = Len(place)` / `PtrMetadata(&place)`.
    match crate::local_defs::unique_value_def(func, p.local) {
        Some(Rvalue::Len(lp)) => lp == place,
        Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => matches!(
            inner,
            Operand::Copy(ip) | Operand::Move(ip)
                if ip.projections.is_empty()
                    && matches!(ref_target_of_local(func, ip.local), Some((tp, _)) if tp == place)
        ),
        _ => false,
    }
}

/// Decode a length guard `len <cmp> C` (or `C <cmp> len`, with `len_on_left` telling
/// which operand is the length) into `(good_is_true, strict)`: whether a LOWER bound
/// `len >= C` (`strict = false`) / `len > C` (`strict = true`) holds on the guard's
/// TRUE (`good_is_true`) or FALSE edge — the OTHER (bad) edge being the one that
/// returns. None for any shape that does not soundly reduce to a lower bound (e.g.
/// `if len < C { access }`, whose reached edge is an UPPER bound).
pub(super) fn len_guard_lower_bound_edge(cmp: BinOp, len_on_left: bool) -> Option<(bool, bool)> {
    // Normalize to `len <c> C`.
    let c = if len_on_left {
        cmp
    } else {
        match cmp {
            BinOp::Lt => BinOp::Gt,
            BinOp::Le => BinOp::Ge,
            BinOp::Gt => BinOp::Lt,
            BinOp::Ge => BinOp::Le,
            BinOp::Eq => BinOp::Eq,
            BinOp::Ne => BinOp::Ne,
            _ => return None,
        }
    };
    match c {
        // `len != C` → FALSE edge: `len == C` ⟹ `len >= C`.
        BinOp::Ne => Some((false, false)),
        // `len == C` → TRUE  edge: `len == C` ⟹ `len >= C`.
        BinOp::Eq => Some((true, false)),
        // `len <  C` → FALSE edge: `len >= C`.
        BinOp::Lt => Some((false, false)),
        // `len <= C` → FALSE edge: `len >  C`.
        BinOp::Le => Some((false, true)),
        // `len >  C` → TRUE  edge: `len >  C`.
        BinOp::Gt => Some((true, true)),
        // `len >= C` → TRUE  edge: `len >= C`.
        BinOp::Ge => Some((true, false)),
        _ => None,
    }
}

/// Per-block dominating length-guard facts (`coll_len(_recv) >= C`) for a projected
/// (struct-field) Vec scalar index. See the section banner for the recognizer, the
/// fact shape, and every soundness gate.
pub(super) fn build_len_guard_field_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const FUEL: u32 = 16;
    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let tp = super::terminator_presence_for(func);
    if !tp.has_std_scalar_index_call || !tp.has_switch_int {
        return map;
    }

    for block in &func.body.blocks {
        // (1) A scalar `place[j]` index whose #7c owned-Vec bounds VC reads
        // `coll_len(_recv)`. Mirror BOTH gates the obligation-builder uses (a scalar
        // usize index AND a recoverable owned-container receiver), so the fact lands on
        // a VC that actually exists.
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else { continue };
        // Trust (IDX-TIE-1, 2026-10-03): std's OWN `Index<usize>::index`, for
        // uniformity with the value tie. Defense in depth: the fact here bounds the
        // RECEIVER's length from a dominating guard, which holds whatever the callee,
        // but it is only meant for the std scalar index whose bounds VC reads it.
        if !dest.projections.is_empty()
            || args.len() < 2
            || !super::unwrap_panic::is_std_scalar_index_call(callee)
        {
            continue;
        }
        let Some(recv_op) = args.first() else { continue };
        // The receiver must borrow a PROJECTED place (a struct FIELD) through a SHARED
        // ref. The whole-local `&Vec` case already unifies via the existing coll_len tie
        // (both temps trace to one base), so it is not the gap and is left untouched.
        let (Operand::Copy(rp) | Operand::Move(rp)) = recv_op else { continue };
        if !rp.projections.is_empty() {
            continue;
        }
        let Some((place, recv_mut)) = ref_target_of_local(func, rp.local) else { continue };
        // Require a genuine struct-FIELD projection (`self.p_lo`), not a bare `(*v)`
        // deref of a whole-local `&Vec` param — that case's two temps already unify
        // through `base_collection_step`'s Deref-reborrow arm, so the existing coll_len
        // tie handles it and this fact would be redundant. A SHARED borrow only.
        if recv_mut
            || !place.projections.iter().any(|p| matches!(p, trust_types::Projection::Field(_)))
        {
            continue;
        }
        if !args.iter().any(|a| operand_is_scalar_usize_index(func, a)) {
            continue;
        }
        // PERF-COMPILER-VCGEN-635: defer `collection_abstract_len_with_base_opts` and
        // `place_is_body_stable` until a `SwitchInt` block actually compares `len(place)`
        // against a stable bound on a valid lower-bound edge.
        let mut verified_coll_len: Option<Option<Formula>> = None;
        // (3) A dominating guard establishing `len(place) >= C` (or `> C`) for a stable
        // `C`, returning on the too-short edge.
        let access = block.id.0;
        let mut emitted: Option<Formula> = None;
        for gblock in &func.body.blocks {
            let Terminator::SwitchInt { discr, targets, otherwise, .. } = &gblock.terminator else {
                continue;
            };
            let Some(c_local) = operand_root_local(func, discr, FUEL) else { continue };
            let Some(Rvalue::BinaryOp(cmp, opl, opr)) =
                crate::local_defs::unique_value_def(func, c_local)
            else {
                continue;
            };
            if !matches!(cmp, BinOp::Ne | BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
            {
                continue;
            }
            let len_on_left = operand_is_len_of_place(func, opl, place);
            let len_on_right = operand_is_len_of_place(func, opr, place);
            // Exactly one side must be `len(place)` (a `==` here means neither side is,
            // or — defensively — both, an ambiguous comparison): fail closed otherwise.
            if len_on_left == len_on_right {
                continue;
            }
            let bound_op = if len_on_left { opr } else { opl };
            if !operand_is_stable_bound(func, bound_op) {
                continue;
            }
            let Some((good_is_true, strict)) = len_guard_lower_bound_edge(*cmp, len_on_left) else {
                continue;
            };
            let Some((true_t, false_t)) = bool_switch_branch_targets(targets, *otherwise) else {
                continue;
            };
            // (2) The field PLACE must hold one value across the whole function, so its
            // length cannot change between the guard and the read: `place_is_body_stable`,
            // which asks the root's slot AND, for a place behind the root's `Deref`, every
            // pointer that can write under the root (`&mut`, `&raw mut`, `&raw const` of any
            // place rooted at it). The slot question alone missed `&raw const *self`
            // (the r8c union review's F1).
            let Some(coll_len) = verified_coll_len
                .get_or_insert_with(|| {
                    let (_base, coll_len) =
                        collection_abstract_len_with_base_opts(func, recv_op, true)?;
                    crate::place_is_body_stable(func, place).then_some(coll_len)
                })
                .as_ref()
            else {
                break;
            };
            let (good_t, bad_t) = if good_is_true { (true_t, false_t) } else { (false_t, true_t) };
            let g = gblock.id.0;
            // The guard DOMINATES the read (no path to the read avoids it), the too-short
            // edge CANNOT reach the read, and the long-enough edge DOES.
            if reachable_avoiding_one_contains(func, 0, Some(g), access)
                || reachable_avoiding_one_contains(func, bad_t.0, Some(g), access)
                || !reachable_avoiding_one_contains(func, good_t.0, Some(g), access)
            {
                continue;
            }
            let bound_f = operand_to_formula(func, bound_op);
            emitted = Some(if strict {
                Formula::Gt(Box::new(coll_len.clone()), Box::new(bound_f))
            } else {
                Formula::Ge(Box::new(coll_len.clone()), Box::new(bound_f))
            });
            break;
        }
        if let Some(f) = emitted {
            map.entry(BlockId(access)).or_default().push(f);
        }
    }
    map
}

// Trust (2026-10-04, SLICE-INHERENT-1): the four `<[T]>` recognizers below take
// the call's compiler-minted `callee_key`; `vc_callee_is_slice_inherent` refuses a
// callee not defined in a real sysroot crate, so a user `W::<[T]>::windows` (whose
// rendering carries `[T]`) mints no yield length.
pub(super) fn callee_is_slice_windows(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
) -> bool {
    vc_callee_is_slice_inherent(callee, callee_key, "windows")
}

/// Trust (2026-09-19): `<[T]>::iter` — the plain element iterator.
///
/// Unlike its `windows`/`chunks` siblings this says nothing about the LENGTH of
/// what is yielded (elements have no length); it exists so the trip-count tracer
/// can hop THROUGH `v.iter()` to the slice `v` itself. `slice::Iter` yields
/// exactly `v.len()` items, which is the same count `into_iter(v)` gives, so the
/// hop preserves the trip count exactly. `iter_mut` is deliberately absent:
/// narrow is cheap here, and nothing yet needs it.
pub(super) fn callee_is_slice_iter(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
) -> bool {
    vc_callee_is_slice_inherent(callee, callee_key, "iter")
}

pub(super) fn callee_is_slice_chunks(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
) -> bool {
    // Plain `chunks`/`rchunks` only (length in [1, n]). The `*_exact` variants are
    // handled by `callee_is_slice_chunks_exact` (length exactly n); `*_mut` share
    // the same length guarantee but a different callee name — included here.
    let m = method_tail(callee);
    matches!(m, "chunks" | "chunks_mut" | "rchunks" | "rchunks_mut")
        && vc_callee_is_slice_inherent(callee, callee_key, m)
}

pub(super) fn callee_is_slice_chunks_exact(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
) -> bool {
    // `chunks_exact(n)`/`rchunks_exact(n)` (and their `_mut` forms) yield sub-slices
    // of length EXACTLY `n`; a final under-length remainder is dropped (`.remainder()`
    // is a separate, non-yielded slice). So every yielded chunk has length `== n`.
    let m = method_tail(callee);
    matches!(m, "chunks_exact" | "chunks_exact_mut" | "rchunks_exact" | "rchunks_exact_mut")
        && vc_callee_is_slice_inherent(callee, callee_key, m)
}

/// Iterator adapters whose items are a SUBSET of their receiver's items, each
/// UNCHANGED, so a `windows(n)`/`chunks*(n)` item keeps its length through them.
/// `rev` reads from the back (`next_back`), `skip`/`step_by` through `nth`, and
/// `peekable` hands back an item it already took from the receiver; every one of
/// those is an item of the same `windows`/`chunks*` iterator. `enumerate` and
/// `zip` pair the item with another value and are followed by field path in
/// [`trace_slice_iter_item`].
const ITEM_PRESERVING_ADAPTERS: &[&str] = &[
    "filter",
    "fuse",
    "inspect",
    "peekable",
    "rev",
    "skip",
    "skip_while",
    "step_by",
    "take",
    "take_while",
];

/// Trace the iterator built from `local` to the `windows(n)` / `chunks(n)` call
/// that produced the sub-slice at field `path` of each item it yields, returning
/// the call's kind and size operand. `path` is empty for the item itself; each
/// `enumerate` (`(index, item)`) and `zip` (`(left, right)`) between the call and
/// `local` consumes one step of it.
///
/// Trust (2026-09-29): this used to walk Ref/Use copies and `into_iter` only, so
/// `for (_, w) in v.windows(2).enumerate()`, `for w in v.windows(2).rev()`,
/// `v.windows(2).skip(1)` and `a.chunks_exact(2).zip(b.chunks_exact(2))` had no
/// length fact and `w[1]` was refuted with `w__slice_len = 0` (eight programs of the
/// 659-program ordinary-Rust sweep). Every adapter hop is an `Iterator` method of
/// core authenticated by `vc_callee_is_std_iter_trait_method`, taken through the
/// same gated `call_dest_hop` as the constructor itself.
pub(super) fn trace_slice_iter_item<'f>(
    func: &'f VerifiableFunction,
    local: usize,
    path: &[usize],
    fuel: u32,
) -> Option<(SliceIterKind, &'f Operand)> {
    if fuel == 0 {
        return None;
    }
    // The seam's VALUE resolver first; when it declines, the ORIGIN hop
    // (`iterator_yield::iterator_origin_def`), licensed here because the result is the
    // `windows`/`chunks*` CALL the iterator was built from, read for its size operand:
    // `next` on those iterators consumes and never reseats, so every sub-slice it
    // yields has the length that call fixes, whatever its position.
    let def = crate::local_defs::unique_value_def(func, local)
        .or_else(|| super::iterator_yield::iterator_origin_def(func, local));
    if let Some(rvalue) = def {
        return match rvalue {
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_slice_iter_item(func, place.local, path, fuel - 1)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_slice_iter_item(func, p.local, path, fuel - 1)
            }
            _ => None,
        };
    }
    // The call-destination hop, GATED on the call being the local's only write channel
    // (`iterator_yield::call_dest_hop`). Ungated, `let mut w = a.windows(2); let p =
    // &mut w; *p = b.windows(3); for win in w { win[2] }` traced to the FIRST
    // constructor and REFUTED a correct program with `win__slice_len = 2` (pristine
    // driver: 1 proved, 2 failed), and its twin with the sizes swapped PROVED a
    // program that panics. Both are pinned on real MIR (`windows_reseat`,
    // `windows_reseat_bug` in `tests/escaped_local_seam_realmir.rs`).
    let (callee, args, callee_key) = super::iterator_yield::call_dest_hop_keyed(func, local)?;
    let whole_local = |op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    };
    if callee_is_into_iter(callee) && args.len() == 1 {
        return trace_slice_iter_item(func, whole_local(&args[0])?, path, fuel - 1);
    }
    if !path.is_empty() {
        let (&field, rest) = path.split_first()?;
        if field == 1
            && super::iterator_yield::vc_callee_is_std_iter_trait_method(
                callee,
                "Iterator",
                "enumerate",
            )
        {
            return trace_slice_iter_item(func, whole_local(args.first()?)?, rest, fuel - 1);
        }
        if field <= 1
            && args.len() == 2
            && super::iterator_yield::vc_callee_is_std_iter_trait_method(callee, "Iterator", "zip")
        {
            return trace_slice_iter_item(func, whole_local(&args[field])?, rest, fuel - 1);
        }
    }
    let m = method_tail(callee);
    if ITEM_PRESERVING_ADAPTERS.contains(&m)
        && super::iterator_yield::vc_callee_is_std_iter_trait_method(callee, "Iterator", m)
    {
        return trace_slice_iter_item(func, whole_local(args.first()?)?, path, fuel - 1);
    }
    if !path.is_empty() || args.len() != 2 {
        return None;
    }
    if callee_is_slice_windows(callee, callee_key)
        || callee_is_slice_chunks_exact(callee, callee_key)
    {
        return Some((SliceIterKind::ExactLen, &args[1]));
    }
    if callee_is_slice_chunks(callee, callee_key) {
        return Some((SliceIterKind::Chunks, &args[1]));
    }
    None
}

/// The `windows`/`chunks*` constructor of EVERY `Iterator::next` call writing
/// `next_result_local`, traced from each call's receiver. The entrance is the JOINED
/// one, `iterator_yield::next_call_receivers` — the `next` calls must be the Option
/// local's ONLY write channels, and every receiver must trace (`None` otherwise); the
/// consumer disjoins the per-constructor length facts. Ungated, `let o = if c {
/// w1.next() } else { w2.next() }` with `w1 = a.windows(3)`, `w2 = b.windows(2)` took
/// the first call in block order and PROVED both `SliceBoundsCheck` rows of `w[2]`
/// (kernel-certified, pristine driver) while the `w2` branch panics (`two_next_win`,
/// pinned on real MIR); joined, it gets `len == 3 ∨ len == 2` and stays refuted on a
/// witness the program realises.
pub(super) fn slice_iter_next_kinds<'f>(
    func: &'f VerifiableFunction,
    next_result_local: usize,
    path: &[usize],
    fuel: u32,
) -> Option<Vec<(SliceIterKind, &'f Operand)>> {
    super::iterator_yield::next_call_receivers(func, next_result_local)?
        .into_iter()
        .map(|receiver| trace_slice_iter_item(func, receiver, path, fuel))
        .collect()
}

/// The field path under `(o as Some).0` that `projections` reads: `Some([])` for
/// the payload itself, `Some([1])` for `((o as Some).0).1`; `None` unless the place
/// is the `Some` payload followed by tuple/struct FIELD projections only.
fn some_payload_field_path(projections: &[trust_types::Projection]) -> Option<Vec<usize>> {
    let (head, tail) = projections.split_at_checked(2)?;
    if !is_some_payload_projection(head) {
        return None;
    }
    tail.iter()
        .map(|p| match p {
            trust_types::Projection::Field(i) => Some(*i),
            _ => None,
        })
        .collect()
}

/// Build the per-block map of slice-chunking yield facts: for each payload
/// `_p = (next(&mut windows/chunks(s, n)) as Some).0`, constrain `_p`'s modeled
/// slice length (`windows ⇒ == n`, `chunks ⇒ in [1, n]`). See the banner above.
///
/// Trust: 2026-09-16 (round A5) — the payload is GATED: `for mut w in a.windows(3) { w
/// = s; t = w[2] }` reseats the yielded sub-slice and the bounds `Assert` row PROVED on
/// the pristine driver with `Eq(w__slice_len#s6_1, 3)` minted on the post-reseat
/// version; the payload now has two whole writes and gets no fact. Since 2026-10-12
/// (CHUNKS-MUT-PAYLOAD-1) the gate is the `{s}__slice_len` name licence
/// (`slice_len_licence::licensed_slice_len_formula`) rather than
/// `iterator_yield::payload_carries_global_fact`, so a `_mut` chunk's own length read
/// (`&raw const (*w)`) no longer withholds the fact; see the gate below. The entrance
/// is the JOINED one: `let o = if c { w1.next() } else { w2.next() }` gets `len == 3 ∨
/// len == 2`.
pub(crate) fn build_slice_iter_yield_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    let mut payloads: Vec<(usize, Vec<Formula>)> = Vec::new();
    if super::iterator_yield::body_has_iterator_next(func) {
        for block in &func.body.blocks {
            for (stmt_index, stmt) in block.stmts.iter().enumerate() {
                let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
                if !dest.projections.is_empty() {
                    continue;
                }
                let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue
                else {
                    continue;
                };
                // `(o as Some).0`, or a FIELD of it: `enumerate`/`zip` items are tuples,
                // and rustc reads `for (_, w) in ..`'s `w` as `((o as Some).0).1`.
                let Some(path) = some_payload_field_path(&src.projections) else {
                    continue;
                };
                // PERF-COMPILER-VCGEN-636: `licensed_slice_len_formula_place` requires
                // `place_slice_len_formula(func, &Place::local(dest.local)).is_some()`;
                // check that O(1) local-type gate before tracing `Iterator::next` origins.
                let dest_place = Place::local(dest.local);
                if crate::place_slice_len_formula(func, &dest_place).is_none() {
                    continue;
                }
                let Some(kinds) = slice_iter_next_kinds(func, src.local, &path, TRACE_FUEL) else {
                    continue;
                };
                // Trust (2026-10-10, review round 101): the size `n` must still be the one the
                // yielding `next` used: a window from the previous iteration's `a.windows(n)`
                // got `len(w) == n` for the CURRENT `n` (`w[n - 1]` PROVED, indexed past it).
                if super::iterator_yield::bound_rewritten_between_yield_and_extraction(
                    func,
                    src.local,
                    block.id,
                    stmt_index,
                    dest.local,
                    kinds.iter().map(|(_, n_op)| *n_op),
                ) {
                    continue;
                }
                // The yielded sub-slice's length term, under THE `{s}__slice_len` NAME
                // LICENCE (`slice_len_licence::licensed_slice_len_formula`), which is also
                // this lane's payload gate: `None` (no fact) unless the payload is a
                // modeled slice/ref bound exactly once, never mutably aliased at or above
                // itself, and every place its length name can be tied to is the same.
                //
                // Trust: 2026-10-12 (CHUNKS-MUT-PAYLOAD-1) — the gate was
                // `iterator_yield::payload_carries_global_fact`, plain
                // `is_single_static_assignment(w)`, which counts EVERY `&raw`/`&mut` of `w` as
                // an escape. Indexing a `&mut [T]` payload makes rustc read its length through
                // its own `_k = &raw const (*w); PtrMetadata(move _k)`, so `for w in
                // a.chunks_exact_mut(4) { w[3] = 1 }` (and `chunks_mut`, `rchunks*_mut`, the
                // `while let Some(w) = it.next()` spelling) got no `len(w) == 4` fact and was
                // refuted at `w__slice_len = 0`, a length these iterators never yield, while
                // the `chunks_exact` twin proved. The fact is the fat pointer's own
                // metadata: a borrow of `*w` or an element store `(*w)[i] = v` is strictly
                // inside `w` and cannot change it, which is the line the licence draws
                // (`local_defs::path_is_single_static_assignment`). It refuses exactly what
                // the old gate refused at or above `w`: a second whole definition (a reseat,
                // `w = &mut other[..]`), `&mut w` / `&raw const w` / `&raw mut w` (a store
                // through them can reseat `w`), a destruction, an unlocatable write, and a
                // parameter (its entry definition is a second value). The same licence
                // already admits a guarded `&mut [u8]` parameter's length
                // (`if w.len() == 4 { w[3] = 1 }`).
                let Some(len_f) = super::slice_len_licence::licensed_slice_len_formula_place(
                    func,
                    &dest_place,
                    TRACE_FUEL,
                ) else {
                    continue;
                };
                // The size operand `n` is INLINED into a fact keyed on the payload's length,
                // so it must resolve to a single-valued name (a constant, a never-written
                // parameter, a single-def temp) — the same licence as a range bound
                // (`iterator_yield::resolve_range_bound_formula`); otherwise no fact.
                let groups: Option<Vec<Vec<Formula>>> = kinds
                    .iter()
                    .map(|(kind, n_op)| {
                        let n_f = super::iterator_yield::resolve_range_bound_formula(
                            func, n_op, TRACE_FUEL,
                        )?;
                        Some(match kind {
                            SliceIterKind::ExactLen => {
                                vec![Formula::Eq(Box::new(len_f.clone()), Box::new(n_f))]
                            }
                            SliceIterKind::Chunks => vec![
                                Formula::Ge(Box::new(len_f.clone()), Box::new(Formula::Int(1))),
                                Formula::Le(Box::new(len_f.clone()), Box::new(n_f)),
                            ],
                        })
                    })
                    .collect();
                let Some(groups) = groups else { continue };
                payloads.push((dest.local, super::iterator_yield::join_yield_fact_groups(groups)));
            }
        }
    }
    let mut map = super::iterator_yield::attach_payload_facts(func, payloads);
    // Trust (D2 tier 1, 2026-09-24): a closure's `ADAPTER_YIELD` slice-length
    // premise (`windows`/`chunks_exact`/`chunks` item under a core adapter),
    // installed by the compiler and re-gated on this body. No premise — every
    // body but an admitted closure — leaves the map byte-identical.
    super::extend_with_adapter_premise_facts(func, &mut map, super::AdapterPremiseFamily::SliceLen);
    map
}

/// Generate all verification conditions for a function.
///
/// Guard conditions from MIR control flow (SwitchInt, Assert) are
/// extracted via `path_map()` and threaded into each VC as path assumptions.
/// Local variable names carrying a proven NON-NULL provenance, for FFI
/// null-check discharge:
///
/// - the DEST of a STD-container `as_ptr`/`as_mut_ptr` call, by its
///   compiler-minted key ([`STD_NONNULL_AS_PTR_ITEMS`]: `[T]`, `Vec`, `str`,
///   `CStr`) — slice/container pointers are dangling-but-NONZERO even for empty
///   containers; a same-named USER method, and std's raw-slice
///   `<*const [T]>::as_ptr` (null for a null receiver), never match and stay
///   unconstrained (ASPTR-KEY-1),
/// - a `Rvalue::Ref` (`&`/`&mut` — non-null by the reference validity
///   invariant, however formed; a null reference is UB owned by the separate
///   unsafe lane, not a value this lane may see),
/// - a `Rvalue::AddressOf` (`&raw`) of a place with NO `Deref` projection (a
///   direct local/field/index place — its address comes from live storage;
///   `&raw mut *ptr` of a possibly-null `ptr` is EXCLUDED: that raw borrow
///   inherits the pointer's nullness),
///
/// propagated through nullness-preserving single steps of an already-non-null
/// whole local: `Rvalue::Use` moves/copies, `Rvalue::Cast` from a pointer or
/// reference to a pointer or reference, and std's raw-pointer pointee casts
/// `<*const T>::cast` / `cast_mut`, `<*mut T>::cast` / `cast_const` by their
/// compiler-minted key ([`crate::sep_engine::PTR_CAST_ITEMS`]: each is
/// `self as _`, address preserved).
///
/// A local whose DECLARED type is a reference is non-null outright (the same
/// validity invariant as `Rvalue::Ref`). Any other local is non-null only when
/// EVERY value it can hold is: it is not a
/// parameter, every write to it is one of the steps above, and no alias of it
/// is handed out (`crate::local_defs::value_defs` / `value_calls`, which refuse
/// an escape, a partial or unlocatable write, and a parameter's entry value).
/// Chains are followed through a memo with cycle cut-off (a cycle has no
/// non-null base, so its members stay unconstrained) and a depth fuel; anything
/// unresolved stays unconstrained (fail-closed, never a false discharge).
///
/// Trust: 2026-10-25 (FFI-NONNULL-CAST-1) — two changes, one per direction.
///
/// GAINED: the `cast` hop. `unsafe { libc::write(fd, (&raw const byte).cast(), 1) }`
/// and `libc::read(fd, buf.as_mut_ptr().cast(), buf.len())` — the claude-code-alab
/// `sys.rs` self-pipe — kept `FFI write/read: parameter 1 must be non-null` as an
/// `unknown` row, because rustc lowers `.cast()` to a CALL whose destination this
/// scan never derived, while the `as *const c_void` twin of the same argument
/// was discharged. The call is identified by its key (a real-sysroot `core` item,
/// never a same-named user method), its one argument must itself be non-null, and
/// the result is that argument's address: a non-null result follows.
///
/// CLOSED: the old scan inserted a local on ANY non-null write and never removed
/// it, so `let mut p = &raw const x; if c { p = ptr::null(); } write(fd, p as _, 1)`
/// and `let r = &mut p; *r = ptr::null();` both discharged the `write`
/// non-null row with `p` null on a reachable path (measured on atpkg Trust
/// 15698: the row was absent from both functions' results; docs/KNOWN_HAZARDS.md
/// FFI-NONNULL-CAST-1 has the runtime witness). And a `Cast` of any
/// kind propagated, so the fact could ride through an integer, where a
/// truncation (`addr as u8 as usize as *const _`) can make it zero; that half
/// was NOT observed end to end (the extractor rendered the probe's
/// pointer-to-integer cast as an opaque constant), and is closed on the rule,
/// not on a witness. Both are refused now; the first was masked end to end only
/// because every FFI call also carries an unproved `[unsafe]` row, which a
/// verdict must never rely on.
pub(super) fn ffi_nonnull_locals(func: &VerifiableFunction) -> std::collections::HashSet<String> {
    let mut memo: FxHashMap<usize, bool> = FxHashMap::with_capacity_and_hasher(
        func.body.locals.len(),
        Default::default(),
    );
    let mut nonnull: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut visiting: FxHashSet<usize> = FxHashSet::default();
    for decl in &func.body.locals {
        visiting.clear();
        if ffi_local_is_nonnull(func, decl.index, &mut memo, &mut visiting, FFI_NONNULL_FUEL) {
            nonnull.insert(place_to_var_name(func, &Place::local(decl.index)));
        }
    }
    nonnull
}

/// Depth bound for [`ffi_local_is_nonnull`]'s chain walk. Real chains are two or
/// three hops (`&raw` → `cast` → `as`); a longer one stays unconstrained.
const FFI_NONNULL_FUEL: u32 = 32;

/// Whether every value `local` can hold is a non-null pointer, by
/// [`ffi_nonnull_locals`]'s rules. A local on the current walk (`visiting`)
/// answers `false`: the conditions are conjunctive, so a cycle has no non-null
/// base, and memoizing a member computed under that cut is the least fixpoint.
fn ffi_local_is_nonnull(
    func: &VerifiableFunction,
    local: usize,
    memo: &mut FxHashMap<usize, bool>,
    visiting: &mut FxHashSet<usize>,
    fuel: u32,
) -> bool {
    if let Some(&known) = memo.get(&local) {
        return known;
    }
    // A REFERENCE-typed local is non-null at every read, however it was written:
    // the validity invariant `Rvalue::Ref` and the `&raw (*r)` reborrow below rest
    // on (a null reference is UB owned by the unsafe lane, not a value this lane
    // may see). Answered from the declared type, so a reborrow `&mut (*r)` — which
    // the local-defs seam counts as an alias of `r` — does not cost the fact.
    if matches!(crate::local_ty_ref(func, local), Some(trust_types::Ty::Ref { .. })) {
        memo.insert(local, true);
        return true;
    }
    if fuel == 0 || !visiting.insert(local) {
        return false;
    }
    let operand_nonnull = |op: &Operand,
                           memo: &mut FxHashMap<usize, bool>,
                           visiting: &mut FxHashSet<usize>|
     -> bool {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                ffi_local_is_nonnull(func, p.local, memo, visiting, fuel - 1)
            }
            _ => false,
        }
    };
    let pointer_like = |ty: &trust_types::Ty| {
        matches!(ty, trust_types::Ty::RawPtr { .. } | trust_types::Ty::Ref { .. })
    };
    let answer = if let Some(defs) = crate::local_defs::value_defs(func, local) {
        !defs.is_empty()
            && defs.iter().all(|(_, rvalue)| match rvalue {
                Rvalue::Ref { .. } => true,
                Rvalue::AddressOf(_, src) => {
                    let no_deref = !src
                        .projections
                        .iter()
                        .any(|p| matches!(p, trust_types::Projection::Deref));
                    // `&raw` through EXACTLY one Deref of a REFERENCE-typed local —
                    // the reborrow shape `_p = &raw mut (*_r)` with `_r: &mut T` —
                    // takes the reference's VALUE, non-null by the validity
                    // invariant. A Deref of a RAW-pointer-typed local stays
                    // excluded: the raw borrow inherits that pointer's possible
                    // nullness.
                    let deref_of_ref = src.projections.as_slice()
                        == [trust_types::Projection::Deref]
                        && matches!(
                            crate::local_ty_ref(func, src.local),
                            Some(trust_types::Ty::Ref { .. })
                        );
                    no_deref || deref_of_ref
                }
                Rvalue::Use(op) => operand_nonnull(op, memo, visiting),
                // Pointer-to-pointer only (`PtrToPtr`, unsize, `&T as *const T`):
                // an integer source can be a truncation of the address, and an
                // integer target is not a pointer argument.
                Rvalue::Cast(op, target) => {
                    pointer_like(target)
                        && crate::operand_ty_cow(func, op).is_some_and(|ty| pointer_like(&ty))
                        && operand_nonnull(op, memo, visiting)
                }
                _ => false,
            })
    } else if let Some(calls) = crate::local_defs::value_calls(func, local) {
        calls.iter().all(|call| {
            let Terminator::Call { callee_key, args, .. } = call else { return false };
            // The receiver must not be a RAW pointer: an `as_ptr` taking one
            // inherits its nullness. Every admitted item takes `&self` (its
            // signature, which the key names), so this only refuses an
            // extraction that disagrees with the key (ASPTR-KEY-1). A receiver
            // with no extracted type (a `"lit".as_ptr()` constant) is left to
            // the key; a missing receiver is refused.
            let receiver_is_raw = args.first().is_none_or(|recv| {
                crate::operand_ty_cow(func, recv)
                    .is_some_and(|ty| matches!(ty.as_ref(), trust_types::Ty::RawPtr { .. }))
            });
            let as_ptr = is_std_container_as_ptr(callee_key.as_ref()) && !receiver_is_raw;
            let cast = trust_types::CalleeKey::opt_is_one_of(
                callee_key.as_ref(),
                crate::sep_engine::PTR_CAST_ITEMS,
            ) && matches!(args.as_slice(), [recv] if operand_nonnull(recv, memo, visiting));
            as_ptr || cast
        })
    } else {
        false
    };
    visiting.remove(&local);
    memo.insert(local, answer);
    answer
}

/// Whether `callee` is the std `Iterator::position`/`rposition` of a slice's own
/// element iterator (`core::slice::iter::Iter`/`IterMut`). Both return the index of
/// an element counted from the FRONT of what the iterator has not yet yielded, so a
/// `Some` index is below the length of the slice it was built over. The trait half is
/// anchored by [`super::iterator_yield::vc_callee_is_std_iter_trait_method`] and the
/// self half by its path head, each against its std root, and an unauthenticated crate
/// stamp refuses.
pub(super) fn callee_is_slice_iter_position(callee: &str) -> bool {
    let method = super::method_tail(callee);
    if !matches!(method, "position" | "rposition")
        || trust_types::path_has_unauthenticated_crate_stamp(callee)
        || !super::iterator_yield::vc_callee_is_std_iter_trait_method(callee, "Iterator", method)
    {
        return false;
    }
    let Some(self_ty) = super::iterator_yield::vc_qualified_self_ty(callee) else {
        return false;
    };
    let self_ty = super::iterator_yield::vc_peel_reference_prefixes(self_ty);
    let head = self_ty.split('<').next().unwrap_or(self_ty);
    matches!(head, "core::slice::iter::Iter" | "core::slice::iter::IterMut")
}

/// The slice a `position` receiver iterates: `&mut it` (or `it`) where `it`'s one
/// value is `<[T]>::iter(s)` / `<[T]>::iter_mut(s)`, reached through whole-local
/// copies and borrows. Each hop is the seam's single-value answer or the gated
/// call-destination hop, as in [`trace_slice_iter_item`].
fn trace_to_iterated_slice<'a>(
    func: &'a VerifiableFunction,
    op: &'a Operand,
    fuel: u32,
) -> Option<&'a Operand> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if let Some(rvalue) = crate::local_defs::unique_value_def(func, p.local) {
        return match rvalue {
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_local_slice_iter_origin(func, place.local, fuel - 1)
            }
            Rvalue::Use(inner) => trace_to_iterated_slice(func, inner, fuel - 1),
            _ => None,
        };
    }
    trace_local_slice_iter_origin(func, p.local, fuel - 1)
}

fn trace_local_slice_iter_origin(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<&Operand> {
    if fuel == 0 {
        return None;
    }
    if let Some(Rvalue::Use(inner)) = crate::local_defs::unique_value_def(func, local) {
        return trace_to_iterated_slice(func, inner, fuel - 1);
    }
    // The call-destination hop, as `iterator_yield::call_dest_hop` gates it, except that
    // the iterator's `&mut` conduit may also feed the `position` being traced (it only
    // consumes; see `iterator_yield::iter_mut_borrows_only_feed`).
    let consuming = |_: usize, term: &Terminator, arg_ix: usize| {
        arg_ix == 0
            && matches!(term, Terminator::Call { func: callee, .. }
                if super::iterator_yield::callee_is_iterator_next(callee)
                    || callee_is_slice_iter_position(callee))
    };
    let terminator = crate::local_defs::unique_value_call(func, local).or_else(|| {
        super::iterator_yield::iter_mut_borrows_only_feed(func, local, consuming)
            .then(|| crate::local_defs::unique_initializing_call(func, local))
            .flatten()
    })?;
    let Terminator::Call { func: callee, args, dest, callee_key, .. } = terminator else {
        return None;
    };
    if !dest.projections.is_empty() {
        return None;
    }
    let [slice] = args.as_slice() else { return None };
    // Trust (SLICE-INHERENT-1): the `<[T]>` recognizer takes the compiler-minted key.
    let m = method_tail(callee);
    (matches!(m, "iter" | "iter_mut") && vc_callee_is_slice_inherent(callee, callee_key.as_ref(), m))
        .then_some(slice)
}

/// Build the per-block map of `position` facts: for each payload
/// `_p = (<[T]>::iter(s).position(f) as Some).0` (or `rposition`, or over `iter_mut`),
/// `0 <= _p < s.len()`.
///
/// Trust (2026-09-29). `if let Some(i) = v.iter().position(|&x| x == t) { v[i] }` was
/// refuted with `i = 0`, `v.len() = 0` (the ordinary-Rust completeness sweep): nothing
/// related the index to the slice. The length term is the root's canonical
/// `{root}__slice_len`, under the same licence a range bound's is
/// ([`super::callee_summaries::param_slice_len`], then the temp-keyed licence), so a
/// slice that is reseated after the search gets no fact; the payload must carry a
/// global fact ([`super::iterator_yield::payload_carries_global_fact`]); and the call
/// must be the `Option`'s only write ([`super::iterator_yield::call_dest_hop`]).
pub(crate) fn build_position_yield_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    if !super::terminator_presence_for(func).has_position_call {
        return FxHashMap::default();
    }
    let mut payloads: Vec<(usize, Vec<Formula>)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
                continue;
            };
            if !is_some_payload_projection(&src.projections) {
                continue;
            }
            let Some((callee, args)) = super::iterator_yield::call_dest_hop(func, src.local) else {
                continue;
            };
            if !callee_is_slice_iter_position(callee)
                || !super::iterator_yield::payload_carries_global_fact(func, dest.local)
            {
                continue;
            }
            let Some(slice) =
                args.first().and_then(|recv| trace_to_iterated_slice(func, recv, TRACE_FUEL))
            else {
                continue;
            };
            let Some(len) = super::callee_summaries::param_slice_len(func, slice, TRACE_FUEL)
                .or_else(|| {
                    super::slice_len_licence::licensed_slice_len_formula(func, slice, TRACE_FUEL)
                })
            else {
                continue;
            };
            let index =
                Formula::var_owned(place_to_var_name(func, &Place::local(dest.local)), Sort::Int);
            // Trust (2026-09-29): the same bound on the `Some` payload PLACE the index was
            // copied from. A range index resolves its end through the copy to that place
            // (`&v[..i]` reads `(o as Some).0`), and the copy's own definition does not
            // reach its row, so `match v.iter().position(p) { Some(i) => &v[..i], .. }`
            // was refuted with the payload above the length (m11 of the ordinary-Rust
            // sweep). `call_dest_hop` has already required the `position` call to be the
            // Option's only write, so the payload holds that call's index wherever the
            // copy is named.
            let payload = Formula::var_owned(place_to_var_name(func, src), Sort::Int);
            payloads.push((
                dest.local,
                vec![
                    Formula::Ge(Box::new(index.clone()), Box::new(Formula::Int(0))),
                    Formula::Lt(Box::new(index), Box::new(len.clone())),
                    Formula::Ge(Box::new(payload.clone()), Box::new(Formula::Int(0))),
                    Formula::Lt(Box::new(payload), Box::new(len)),
                ],
            ));
        }
        // Trust (2026-09-29): `v.iter().position(p).unwrap_or(d)` is the payload or `d`:
        // `0 <= r < len` or `r == d`. `&v[v.iter().position(p).unwrap_or(v.len())..]`
        // was refuted with `r = 1`, `len = 0` (z03 of the ordinary-Rust sweep).
        if let Terminator::Call { func: term_callee, args: term_args, dest, .. } = &block.terminator
            && dest.projections.is_empty()
            && term_args.len() == 2
            && term_callee.contains("::option::Option")
            && let Some((o, default)) =
                super::iterator_yield::option_unwrap_or_parts(func, dest.local)
            && let Some((callee, args)) = super::iterator_yield::call_dest_hop(func, o)
            && callee_is_slice_iter_position(callee)
            && super::iterator_yield::payload_carries_global_fact(func, dest.local)
            && let Some(slice) =
                args.first().and_then(|recv| trace_to_iterated_slice(func, recv, TRACE_FUEL))
            && let Some(len) = super::callee_summaries::param_slice_len(func, slice, TRACE_FUEL)
                .or_else(|| {
                    super::slice_len_licence::licensed_slice_len_formula(func, slice, TRACE_FUEL)
                })
            && let Some(d) = super::iterator_yield::resolve_range_bound_formula(func, default, 8)
        {
            let r =
                Formula::var_owned(place_to_var_name(func, &Place::local(dest.local)), Sort::Int);
            payloads.push((dest.local, vec![unwrap_or_bound(r, &len, false, d)]));
        }
    }
    super::iterator_yield::attach_payload_facts(func, payloads)
}

/// `0 <= r < len` (`<= len` unless `strict`), or `r == d`: the value of
/// `unwrap_or(o, d)` when `o`'s payload is bounded by `len`.
fn unwrap_or_bound(r: Formula, len: &Formula, strict: bool, d: Formula) -> Formula {
    let upper = if strict {
        Formula::Lt(Box::new(r.clone()), Box::new(len.clone()))
    } else {
        Formula::Le(Box::new(r.clone()), Box::new(len.clone()))
    };
    Formula::Or(vec![
        Formula::And(vec![Formula::Ge(Box::new(r.clone()), Box::new(Formula::Int(0))), upper]),
        Formula::Eq(Box::new(r), Box::new(d)),
    ])
}

/// Build the per-block map of `str::find` / `str::rfind` facts: for each payload
/// `_i = (s.find(p) as Some).0`, `0 <= _i <= s.len()`, and `_i < s.len()` when the
/// pattern is a `char` (a match of one occupies at least one byte at `_i`). An empty
/// `&str` pattern can match at the end, so `<=` is the general bound.
///
/// Trust (2026-09-29). `s.get(i + 1..)` after `let i = s.rfind('.')?` was refuted with
/// `i = usize::MAX` (p28 of the ordinary-Rust sweep), and `&s[..i]` under `Some(i) =
/// s.find('=')` with the payload above the length (p08). These facts are the bounds
/// half; the char-boundary half of a str slice at the payload is the structural credit
/// [`super::iterator_yield::operand_is_str_find_payload_of`]. The receiver root,
/// the length licence and the payload gates are the `position` map's
/// ([`build_position_yield_guard_map`]).
pub(crate) fn build_str_find_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    if !super::terminator_presence_for(func).has_str_find_call {
        return FxHashMap::default();
    }
    let mut payloads: Vec<(usize, Vec<Formula>)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
                continue;
            };
            if !matches!(
                src.projections.as_slice(),
                [trust_types::Projection::Downcast(0 | 1), trust_types::Projection::Field(0)]
            ) {
                continue;
            }
            if !super::iterator_yield::payload_carries_global_fact(func, dest.local) {
                continue;
            }
            let Some(root) = super::iterator_yield::str_find_payload_receiver_root(func, src)
            else {
                continue;
            };
            let Some((callee, _)) = super::iterator_yield::call_dest_hop(func, src.local) else {
                continue;
            };
            let Some(len) = str_root_len(func, root, TRACE_FUEL) else { continue };
            let char_pattern = callee.ends_with("::<char>");
            let bounded = |x: Formula| {
                let upper = if char_pattern {
                    Formula::Lt(Box::new(x.clone()), Box::new(len.clone()))
                } else {
                    Formula::Le(Box::new(x.clone()), Box::new(len.clone()))
                };
                [Formula::Ge(Box::new(x), Box::new(Formula::Int(0))), upper]
            };
            let index =
                Formula::var_owned(place_to_var_name(func, &Place::local(dest.local)), Sort::Int);
            let payload = Formula::var_owned(place_to_var_name(func, src), Sort::Int);
            let [i0, i1] = bounded(index);
            let [p0, p1] = bounded(payload);
            payloads.push((dest.local, vec![i0, i1, p0, p1]));
        }
        // `s.find(p).unwrap_or(d)`: the payload or `d` (`&s[..s.find(',').unwrap_or(s.len())]`).
        if let Terminator::Call { func: term_callee, args: term_args, dest, .. } = &block.terminator
            && dest.projections.is_empty()
            && term_args.len() == 2
            && term_callee.contains("::option::Option")
            && super::iterator_yield::payload_carries_global_fact(func, dest.local)
            && let Some((o, default)) =
                super::iterator_yield::option_unwrap_or_parts(func, dest.local)
            && let Some((root, strict)) = super::iterator_yield::str_find_call(func, o)
            && let Some(len) = str_root_len(func, root, TRACE_FUEL)
            && let Some(d) = super::iterator_yield::resolve_range_bound_formula(func, default, 8)
        {
            let r =
                Formula::var_owned(place_to_var_name(func, &Place::local(dest.local)), Sort::Int);
            payloads.push((dest.local, vec![unwrap_or_bound(r, &len, strict, d)]));
        }
    }
    super::iterator_yield::attach_payload_facts(func, payloads)
}

/// The licensed length term of the string rooted at the `&str` local `root`, under
/// the licence a range bound's length takes ([`build_position_yield_guard_map`]).
fn str_root_len(func: &VerifiableFunction, root: usize, fuel: u32) -> Option<Formula> {
    let recv = Place::local(root);
    super::callee_summaries::param_slice_len_place(func, &recv, fuel)
        .or_else(|| super::slice_len_licence::licensed_slice_len_formula_place(func, &recv, fuel))
}

/// Build the per-block map of `count` facts: for each `_c = <I as Iterator>::count(it)`
/// whose iterator is built from a slice `s`, or authenticated `str::bytes(s)`,
/// through length-non-increasing adapters ([`super::loop_bounds::iterated_slice_of`]),
/// `0 <= _c <= s.len()`. The byte producer yields one item per byte; other string
/// views, including `split`'s `len + 2` case, do not enter this numeric bound.
///
/// Trust (2026-09-29). `v.len() - v.iter().filter(p).count()` was refuted with
/// `count = 1`, `v.len() = 0` (the ordinary-Rust completeness sweep). Each hop of the
/// walk is authenticated as std's and every intermediate `Self` is a std adapter over a
/// std slice iterator, so the `count` called is std's for that type, and it counts
/// what the iterator yields. The length term is licensed as for a range bound, and the
/// result must carry a global fact.
pub(crate) fn build_count_bound_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    if !super::terminator_presence_for(func).has_count_call {
        return FxHashMap::default();
    }
    let mut counts: Vec<(usize, Vec<Formula>)> = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
        else {
            continue;
        };
        if !dest.projections.is_empty()
            || super::method_tail(callee) != "count"
            || trust_types::path_has_unauthenticated_crate_stamp(callee)
            || !super::iterator_yield::vc_callee_is_std_iter_trait_method(
                callee, "Iterator", "count",
            )
        {
            continue;
        }
        let Some(slice) =
            args.first().and_then(|it| super::loop_bounds::iterated_slice_of(func, it, TRACE_FUEL))
        else {
            continue;
        };
        if !super::iterator_yield::payload_carries_global_fact(func, dest.local) {
            continue;
        }
        let Some(len) =
            super::callee_summaries::param_slice_len(func, slice, TRACE_FUEL).or_else(|| {
                super::slice_len_licence::licensed_slice_len_formula(func, slice, TRACE_FUEL)
            })
        else {
            continue;
        };
        let count =
            Formula::var_owned(place_to_var_name(func, &Place::local(dest.local)), Sort::Int);
        counts.push((
            dest.local,
            vec![
                Formula::Ge(Box::new(count.clone()), Box::new(Formula::Int(0))),
                Formula::Le(Box::new(count), Box::new(len)),
            ],
        ));
    }
    super::iterator_yield::attach_payload_facts(func, counts)
}

// Trust (2026-10-04, wave 13): test modules sit at the END of the file, so the
// `local_defs_seam_lint` test-module mask (which runs from a braceless `mod x;` to
// the next closing brace) cannot swallow a production function.
#[cfg(test)]
#[path = "asptr_nonnull_key_tests.rs"]
mod asptr_nonnull_key_tests;

#[cfg(test)]
#[path = "slice_inherent_key_tests.rs"]
mod slice_inherent_key_tests;
