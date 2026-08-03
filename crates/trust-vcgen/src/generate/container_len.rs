// Length reasoning for owned containers: a `Vec` created empty and only ever
// pushed to under the same dominating guard has a provable length bound, and a
// struct field holding such a `Vec` keys a per-field length map. Also the
// windowed/chunked slice iterators, whose yields inherit the base slice's
// length, and the non-null locals an FFI boundary establishes.

use super::*;

/// Whether `callee` is a canonical std container's inherent raw-pointer
/// accessor. This licenses a non-null fact for FFI arguments, so both the
/// method tail and the crate root are load-bearing.
pub(super) fn is_std_container_as_ptr(callee: &str) -> bool {
    let lower = callee.to_lowercase();
    (lower.ends_with("::as_ptr") || lower.ends_with("::as_mut_ptr"))
        && (callee.starts_with("core::")
            || callee.starts_with("std::")
            || callee.starts_with("alloc::"))
        && (lower.contains("core::slice")
            || lower.contains("std::slice")
            || lower.contains("alloc::vec")
            || lower.contains("std::vec")
            || lower.contains("core::str")
            || lower.contains("std::str")
            || lower.contains("core::array")
            || lower.contains("vec_deque")
            || lower.contains("::c_str::")
            || lower.contains("::ffi::cstr")
            || lower.contains("::ffi::cstring"))
}

/// True iff the single whole-local def of `local` is an EMPTY `Vec` constructor
/// (`Vec::new` / `Vec::with_capacity`). A non-empty / unknown creation (`vec![..]`,
/// `to_vec`, `collect`, `Vec::from`, or a plain `Assign`) declines: only an empty
/// start makes EVERY later element a guarded push. Caller ensures the def is unique.
pub(super) fn vec_created_empty(func: &VerifiableFunction, local: usize) -> bool {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
        {
            return vc_callee_is_std_vec_inherent(callee)
                && matches!(method_tail(callee), "new" | "with_capacity");
        }
    }
    false
}

/// True iff EVERY `&mut local` / `&raw local` borrow's dest is single-def and used
/// SOLELY as the receiver (arg 0) of a `Vec::push` call — the push-only mutation
/// discipline. A projected `&mut local[..]`, a projected/reused borrow-dest, or a
/// borrow reaching pop/truncate/clear/remove/insert/extend/swap or any escape → false.
/// Modeled on [`iter_mut_borrows_only_feed_next`].
pub(super) fn vec_mut_borrows_only_feed_push(func: &VerifiableFunction, local: usize) -> bool {
    let mut conduits: Vec<usize> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place: dst, rvalue, .. } = stmt
                && let Rvalue::Ref { mutable: true, place: b } | Rvalue::AddressOf(_, b) = rvalue
                && b.local == local
            {
                // A projected `&mut m[..]` / `&mut m.f`, or a projected borrow-dest, is
                // not the whole-Vec push receiver — fail closed.
                if !b.projections.is_empty() || !dst.projections.is_empty() {
                    return false;
                }
                conduits.push(dst.local);
            }
        }
    }
    for t in conduits {
        if guards::whole_local_def_count(func, t) != 1 {
            return false;
        }
        for block in &func.body.blocks {
            for s in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = s {
                    // A write THROUGH the conduit (`*t = other_vec`, which REPLACES m)
                    // voids the discipline; the sole whole-local def (the `&mut m`
                    // borrow) is admitted (a second one is caught by the def-count).
                    if place.local == t && !place.projections.is_empty() {
                        return false;
                    }
                    let mut used = false;
                    for_each_rvalue_operand_place(rvalue, &mut |pl| {
                        if pl.local == t {
                            used = true;
                        }
                    });
                    if used {
                        return false;
                    }
                }
                // A `SetDiscriminant`/`Deinit` through the conduit likewise mutates m.
                if matches!(s,
                    Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                        if place.local == t)
                {
                    return false;
                }
            }
            match &block.terminator {
                Terminator::Call { func: callee, args, dest, .. } => {
                    if dest.local == t {
                        return false;
                    }
                    for (i, a) in args.iter().enumerate() {
                        if let Operand::Copy(pl) | Operand::Move(pl) = a
                            && pl.local == t
                            && !(i == 0
                                && method_tail(callee) == "push"
                                && vc_callee_is_std_vec_inherent(callee))
                        {
                            return false;
                        }
                    }
                }
                Terminator::SwitchInt { discr, .. } => {
                    if matches!(discr, Operand::Copy(pl) | Operand::Move(pl) if pl.local == t) {
                        return false;
                    }
                }
                Terminator::Assert { cond, .. } => {
                    if matches!(cond, Operand::Copy(pl) | Operand::Move(pl) if pl.local == t) {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }
    true
}

/// Blocks that WRITE `local` (whole/projected/call-dest store) OR take a `&mut`/raw
/// borrow of it — the sites at which its value (a `Vec`'s length) can change.
pub(super) fn local_mutation_blocks(func: &VerifiableFunction, local: usize) -> FxHashSet<usize> {
    let mut out = local_write_blocks(func, local);
    for block in &func.body.blocks {
        for s in &block.stmts {
            if let Statement::Assign { rvalue, .. } = s
                && let Rvalue::Ref { mutable: true, place: b } | Rvalue::AddressOf(_, b) = rvalue
                && b.local == local
            {
                out.insert(block.id.0);
            }
        }
    }
    out
}

/// The block that DEFINES the length operand `len_op` reads (a `X.len()` call, a
/// `Len(X)`, or a `PtrMetadata(&X)`), traced through whole-local `Use`-copies to the
/// defining site. `None` if not found. Used to bound "the snapshot point" for the
/// row-stability check.
pub(super) fn len_def_block(func: &VerifiableFunction, len_op: &Operand, fuel: u32) -> Option<usize> {
    let root = operand_root_local(func, len_op, fuel)?;
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, dest, .. } = &block.terminator
            && dest.local == root
            && dest.projections.is_empty()
            && method_tail(callee) == "len"
        {
            return Some(block.id.0);
        }
        for s in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = s
                && place.local == root
                && place.projections.is_empty()
                && matches!(
                    rvalue,
                    Rvalue::Len(_) | Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, _)
                )
            {
                return Some(block.id.0);
            }
        }
    }
    None
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
    let avoid = one_block_set(lblk);
    let mut post: FxHashSet<usize> = FxHashSet::default();
    if let Some(b) = func.body.blocks.get(lblk) {
        for succ in v2_terminator_targets(&b.terminator) {
            post.extend(reachable_avoiding(func, succ.0, &avoid));
        }
    }
    for m in local_mutation_blocks(func, rowbase) {
        if m == lblk {
            continue;
        }
        if post.contains(&m) && reachable_avoiding(func, m, &avoid).contains(&push_block) {
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
                && !(is_parameter(func, p.local)
                    && guards::whole_local_def_count(func, p.local) >= 1)
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
        let Some(Rvalue::BinaryOp(cmp, opl, opr)) = crate::unique_whole_local_def(func, c) else {
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
        let g = gblock.id.0;
        // The guard dominates the push (every path to the push passes through it).
        if reachable_avoiding(func, 0, &one_block_set(g)).contains(&push_block) {
            continue;
        }
        // The "too-short" edge does NOT reach the push; the "long-enough" edge does.
        let avoid_g = one_block_set(g);
        if reachable_avoiding(func, bad_t.0, &avoid_g).contains(&push_block)
            || !reachable_avoiding(func, good_t.0, &avoid_g).contains(&push_block)
        {
            continue;
        }
        // The length snapshot dominates the push, and `rowbase` is not resized between
        // the snapshot and the push (else the snapshot length != the pushed length).
        let Some(lblk) = len_def_block(func, len_op, fuel) else { continue };
        if reachable_avoiding(func, 0, &one_block_set(lblk)).contains(&push_block)
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
        if method_tail(callee) != "push" || !vc_callee_is_std_vec_inherent(callee) {
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
    let Some(ty) = func.body.locals.get(local).map(|d| &d.ty) else { return false };
    let inner = match ty {
        Ty::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    matches!(inner, Ty::Adt { name, .. } if is_owned_slice_container_name(name))
}

/// Per-block push-guarded element-length facts (`coll_len(m[k]) > n`). See the
/// section banner for the recognizer, the fact shape, and every soundness gate.
pub(super) fn build_push_guard_elem_len_map(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    const FUEL: u32 = 16;
    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();

    for decl in &func.body.locals {
        let mi = decl.index;
        // (A) m is an owned Vec, created EMPTY, single-def, never in-place mutated, and
        // mutated ONLY by `Vec::push` (no shrink / element overwrite / &mut escape).
        let Ty::Adt { name, .. } = &decl.ty else { continue };
        if !is_owned_slice_container_name(name)
            || guards::whole_local_def_count(func, mi) != 1
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
            if method_tail(callee) != "index" || !dest.projections.is_empty() || args.len() < 2 {
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
//  * that place's ROOT local must be immutable across the whole function
//    (`place_source_is_stable` — false on ANY `&mut`/`&raw mut` of its tree, any projected
//    write, any reseat), so the field's length is invariant between guard and read;
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
pub(super) fn ref_target_of_local(func: &VerifiableFunction, local: usize) -> Option<(Place, bool)> {
    match crate::unique_whole_local_def(func, local)? {
        Rvalue::Ref { mutable, place } => Some((place.clone(), *mutable)),
        Rvalue::AddressOf(mutable, place) => Some((place.clone(), *mutable)),
        _ => None,
    }
}

/// True iff `op` is the length of EXACTLY the place `place`: a projection-free local
/// `_len`, UNIQUELY whole-defined (so it stably names `len(place)`), whose def is
///   (a) a `.len()` Call whose sole receiver borrows exactly `place`, or
///   (b) a `Len(place)` / `PtrMetadata(&place)` rvalue.
/// Matches by the borrowed PLACE (not a base local), so it recognizes a projected
/// field's length where `operand_is_len_of_base` (base-local keyed) cannot.
pub(super) fn operand_is_len_of_place(func: &VerifiableFunction, op: &Operand, place: &Place) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return false };
    if !p.projections.is_empty() || guards::whole_local_def_count(func, p.local) != 1 {
        return false;
    }
    // (a) `_len = <..>::len(&place)`.
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == p.local
            && dest.projections.is_empty()
            && method_tail(callee) == "len"
        {
            let Some(Operand::Copy(rp) | Operand::Move(rp)) = args.first() else { return false };
            if !rp.projections.is_empty() {
                return false;
            }
            return matches!(ref_target_of_local(func, rp.local), Some((tp, _)) if &tp == place);
        }
    }
    // (b) `_len = Len(place)` / `PtrMetadata(&place)`.
    match crate::unique_whole_local_def(func, p.local) {
        Some(Rvalue::Len(lp)) => lp == place,
        Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => matches!(
            inner,
            Operand::Copy(ip) | Operand::Move(ip)
                if ip.projections.is_empty()
                    && matches!(ref_target_of_local(func, ip.local), Some((tp, _)) if &tp == place)
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
pub(super) fn build_len_guard_field_map(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    const FUEL: u32 = 16;
    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();

    for block in &func.body.blocks {
        // (1) A scalar `place[j]` index whose #7c owned-Vec bounds VC reads
        // `coll_len(_recv)`. Mirror BOTH gates the obligation-builder uses (a scalar
        // usize index AND a recoverable owned-container receiver), so the fact lands on
        // a VC that actually exists.
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else { continue };
        if method_tail(callee) != "index" || !dest.projections.is_empty() || args.len() < 2 {
            continue;
        }
        if !args.iter().any(|a| operand_is_scalar_usize_index(func, a)) {
            continue;
        }
        let Some(recv_op) = args.first() else { continue };
        let Some((_base, coll_len)) = collection_abstract_len_with_base_opts(func, recv_op, true)
        else {
            continue;
        };
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
        // (2) The field's ROOT local must be immutable across the whole function, so the
        // field's length cannot change between the guard and the read. `place_source_is_stable`
        // is false on ANY `&mut`/`&raw mut` of the root's tree, any projected write, any reseat.
        if !crate::place_source_is_stable(func, place.local) {
            continue;
        }
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
                crate::unique_whole_local_def(func, c_local)
            else {
                continue;
            };
            let len_on_left = operand_is_len_of_place(func, opl, &place);
            let len_on_right = operand_is_len_of_place(func, opr, &place);
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
            let (good_t, bad_t) = if good_is_true { (true_t, false_t) } else { (false_t, true_t) };
            let g = gblock.id.0;
            let avoid_g = one_block_set(g);
            // The guard DOMINATES the read (no path to the read avoids it), the too-short
            // edge CANNOT reach the read, and the long-enough edge DOES.
            if reachable_avoiding(func, 0, &avoid_g).contains(&access)
                || reachable_avoiding(func, bad_t.0, &avoid_g).contains(&access)
                || !reachable_avoiding(func, good_t.0, &avoid_g).contains(&access)
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

pub(super) fn callee_is_slice_windows(callee: &str) -> bool {
    vc_callee_is_slice_inherent(callee, "windows")
}

pub(super) fn callee_is_slice_chunks(callee: &str) -> bool {
    // Plain `chunks`/`rchunks` only (length in [1, n]). The `*_exact` variants are
    // handled by `callee_is_slice_chunks_exact` (length exactly n); `*_mut` share
    // the same length guarantee but a different callee name — included here.
    ["chunks", "chunks_mut", "rchunks", "rchunks_mut"]
        .iter()
        .any(|m| vc_callee_is_slice_inherent(callee, m))
}

pub(super) fn callee_is_slice_chunks_exact(callee: &str) -> bool {
    // `chunks_exact(n)`/`rchunks_exact(n)` (and their `_mut` forms) yield sub-slices
    // of length EXACTLY `n`; a final under-length remainder is dropped (`.remainder()`
    // is a separate, non-yielded slice). So every yielded chunk has length `== n`.
    ["chunks_exact", "chunks_exact_mut", "rchunks_exact", "rchunks_exact_mut"]
        .iter()
        .any(|m| vc_callee_is_slice_inherent(callee, m))
}

/// Trace the receiver of an `Iterator::next` to the originating `windows(n)` /
/// `chunks(n)` call, returning its kind and size operand. Walks Ref/Use copies
/// and the transparent `into_iter` (identity), with bounded fuel.
pub(super) fn trace_local_to_slice_iter_call(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<(SliceIterKind, &Operand)> {
    if fuel == 0 {
        return None;
    }
    if let Some(rvalue) = crate::unique_whole_local_def(func, local) {
        return match rvalue {
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_local_to_slice_iter_call(func, place.local, fuel - 1)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_local_to_slice_iter_call(func, p.local, fuel - 1)
            }
            _ => None,
        };
    }
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
        {
            if callee_is_into_iter(callee) && args.len() == 1 {
                if let Operand::Copy(p) | Operand::Move(p) = &args[0]
                    && p.projections.is_empty()
                {
                    return trace_local_to_slice_iter_call(func, p.local, fuel - 1);
                }
                return None;
            }
            if callee_is_slice_windows(callee) && args.len() == 2 {
                return Some((SliceIterKind::ExactLen, &args[1]));
            }
            if callee_is_slice_chunks_exact(callee) && args.len() == 2 {
                return Some((SliceIterKind::ExactLen, &args[1]));
            }
            if callee_is_slice_chunks(callee) && args.len() == 2 {
                return Some((SliceIterKind::Chunks, &args[1]));
            }
            return None;
        }
    }
    None
}

/// Find the `Iterator::next` call whose dest is `next_result_local` and trace its
/// receiver to a `windows`/`chunks` call.
pub(super) fn slice_iter_next_kind(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<(SliceIterKind, &Operand)> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == next_result_local
            && dest.projections.is_empty()
            && callee_is_iterator_next(callee)
            && args.len() == 1
        {
            if let Operand::Copy(p) | Operand::Move(p) = &args[0]
                && p.projections.is_empty()
            {
                return trace_local_to_slice_iter_call(func, p.local, fuel);
            }
            return None;
        }
    }
    None
}

/// Build the per-block map of slice-chunking yield facts: for each payload
/// `_p = (next(&mut windows/chunks(s, n)) as Some).0`, constrain `_p`'s modeled
/// slice length (`windows ⇒ == n`, `chunks ⇒ in [1, n]`). See the banner above.
pub(crate) fn build_slice_iter_yield_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    let mut payloads: Vec<(usize, SliceIterKind, Formula)> = Vec::new();
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
            let Some((kind, n_op)) = slice_iter_next_kind(func, src.local, TRACE_FUEL) else {
                continue;
            };
            payloads.push((dest.local, kind, operand_to_formula(func, n_op)));
        }
    }

    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if payloads.is_empty() {
        return map;
    }
    for block in &func.body.blocks {
        for (payload_local, kind, n_f) in &payloads {
            if !block_mentions_local(block, *payload_local) {
                continue;
            }
            // The yielded sub-slice's place-keyed length term (None if the payload
            // is not a modeled slice/ref — then no fact, sound).
            let Some(len_f) =
                crate::slice_len_formula(func, &Operand::Copy(Place::local(*payload_local)))
            else {
                continue;
            };
            let entry = map.entry(block.id).or_default();
            match kind {
                SliceIterKind::ExactLen => {
                    entry.push(Formula::Eq(Box::new(len_f), Box::new(n_f.clone())));
                }
                SliceIterKind::Chunks => {
                    entry.push(Formula::Ge(Box::new(len_f.clone()), Box::new(Formula::Int(1))));
                    entry.push(Formula::Le(Box::new(len_f), Box::new(n_f.clone())));
                }
            }
        }
    }
    map
}

/// Generate all verification conditions for a function.
///
/// Guard conditions from MIR control flow (SwitchInt, Assert) are
/// extracted via `path_map()` and threaded into each VC as path assumptions.
/// Local variable names carrying a proven NON-NULL provenance, for FFI
/// null-check discharge:
///
/// - the DEST of a STD-container `as_ptr`/`as_mut_ptr` call (anchored to the
///   canonical `core::slice`/`alloc::vec`/`core::str`/`core::array`/
///   `vec_deque` module paths — slice/container pointers are
///   dangling-but-NONZERO even for empty containers; a same-named USER method
///   never matches and stays unconstrained),
/// - a `Rvalue::Ref` (`&`/`&mut` — non-null by the reference validity
///   invariant, however formed; a null reference is UB owned by the separate
///   unsafe lane, not a value this lane may see),
/// - a `Rvalue::AddressOf` (`&raw`) of a place with NO `Deref` projection (a
///   direct local/field/index place — its address comes from live storage;
///   `&raw mut *ptr` of a possibly-null `ptr` is EXCLUDED: that raw borrow
///   inherits the pointer's nullness),
///
/// propagated through nullness-preserving single steps (`Rvalue::Use` moves/
/// copies and `Rvalue::Cast` pointer casts of an already-non-null whole
/// local). Two passes reach the ubiquitous `_p = as_ptr(&buf); _q = _p as
/// *const c_void` chain in either block order; deeper chains simply stay
/// unconstrained (fail-closed, never a false discharge).
pub(super) fn ffi_nonnull_locals(func: &VerifiableFunction) -> std::collections::HashSet<String> {
    let mut nonnull: std::collections::HashSet<String> = std::collections::HashSet::new();
    let whole_local = |op: &Operand| -> Option<String> {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                Some(place_to_var_name(func, p))
            }
            _ => None,
        }
    };
    for _ in 0..2 {
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { place, rvalue, .. } = stmt else { continue };
                if !place.projections.is_empty() {
                    continue;
                }
                let derived_nonnull = match rvalue {
                    Rvalue::Ref { .. } => true,
                    Rvalue::AddressOf(_, src) => {
                        let no_deref = !src
                            .projections
                            .iter()
                            .any(|p| matches!(p, trust_types::Projection::Deref));
                        // `&raw` through EXACTLY one Deref of a
                        // REFERENCE-typed local — the reborrow shape
                        // `_p = &raw mut (*_r)` with `_r: &mut T` — takes the
                        // reference's VALUE, non-null by the validity
                        // invariant. A Deref of a RAW-pointer-typed local
                        // stays excluded: the raw borrow inherits that
                        // pointer's possible nullness.
                        let deref_of_ref = src.projections.as_slice()
                            == [trust_types::Projection::Deref]
                            && func.body.locals.iter().any(|l| {
                                l.index == src.local
                                    && matches!(l.ty, trust_types::Ty::Ref { .. })
                            });
                        no_deref || deref_of_ref
                    }
                    Rvalue::Use(op) | Rvalue::Cast(op, _) => {
                        whole_local(op).is_some_and(|n| nonnull.contains(&n))
                    }
                    _ => false,
                };
                if derived_nonnull {
                    nonnull.insert(place_to_var_name(func, place));
                }
            }
            if let Terminator::Call { func: callee, dest, .. } = &block.terminator {
                if is_std_container_as_ptr(callee) && dest.projections.is_empty() {
                    nonnull.insert(place_to_var_name(func, dest));
                }
            }
        }
    }
    nonnull
}
