// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-10-17; do not grow casually
// The path definition map -- which definition of each name reaches each
// program point -- and the kill/redefinition analysis behind it. Deref stores
// through a mutable pointer havoc every name the pointer could alias, which is
// why pointer laundering has to be detected before any definition survives.

use super::*;
#[cfg(test)]
use trust_types::interior_mutability::shared_borrow_of_local_covers_cell;

#[path = "path_fact_membership.rs"]
mod path_fact_membership;

/// The variable a dataflow fact defines: the lhs of a top-level `Eq(Var(name), _)`.
// `build_semantic_guard_map` relies on this to compute its kill set.
pub(super) fn formula_def_name(f: &Formula) -> Option<&str> {
    match f {
        Formula::Eq(lhs, _) => match &**lhs {
            Formula::Var(name, _) => Some(name.as_str()),
            _ => None,
        },
        _ => None,
    }
}

/// True if place names `a` and `b` OVERLAP in the place tree: equal, or one is a
/// projection (`.field` / `[idx]` / `*`-deref / `@variant`-downcast) descendant of
/// the other. Writing a whole value invalidates facts about its fields/elements and
/// vice-versa; siblings (`x.0` vs `x.1`) are independent. (Place names are produced
/// by `place_to_var_name`, which spells projections `.0` / `[i]` / `*` / `@v`.)
///
/// Trust (W4 fix round 1, 2026-09-25): `@` joined the separator set here (see
/// [`crate::is_projection_segment_lead`]). Before it, a write of `r` did not
/// overlap `r@1.0`, so no whole write of an enum local — assignment, call
/// destination, `SetDiscriminant` — killed a fact over its payload.
pub(crate) fn place_names_overlap(a: &str, b: &str) -> bool {
    if a == b {
        return true;
    }
    fn proj_descendant(longer: &str, ancestor: &str) -> bool {
        longer.len() > ancestor.len()
            && longer.starts_with(ancestor)
            && crate::is_projection_segment_lead(longer.as_bytes()[ancestor.len()])
    }
    if proj_descendant(a, b) || proj_descendant(b, a) {
        return true;
    }
    // Symbolic array-index aliasing (Trust #soundness round-12/13): two
    // index-projections of the SAME array base may denote the same element when
    // ANY index — at ANY nesting depth — is symbolic (a runtime value, rendered
    // `[_..]` by `place_to_var_name`). A write to one must then havoc facts about
    // the other. Conservatively overlap them when they share the array base (the
    // prefix before the first `[`) and either contains a symbolic index segment;
    // distinct all-LITERAL index paths stay precise (distinct constant slots,
    // preserving const-index tracking). Round-12 only inspected the OUTER index
    // segment, missing a symbolic INNER index in a nested array `a[0][_k]`.
    if let (Some(open_a), Some(open_b)) = (a.find('['), b.find('['))
        && a[..open_a] == b[..open_b]
        && (a.contains("[_") || b.contains("[_"))
    {
        return true;
    }
    // Trust (2026-09-29): LITERAL index spellings are not canonical either. A constant
    // pattern index carries the PATTERN's minimum length (`v*[0;min=1]` for `[a, ..]`,
    // `v*[0;min=2]` for `[z, _]`), a shape-B constant read of a shared slice spells
    // `[c;slice]`, a from-end index counts from a length the name does not carry
    // (`[-1;min=1]`), and a subslice rebases what follows it (`v*[1..-0][0;min=1]` is
    // `v*[1;min=2]`). Two such spellings at the point where the names first diverge
    // may name ONE element, and the rule above saw two places: a store through
    // `[z, _]` left a guard through `[a, ..]` alive, and an adversarial audit found
    // nine programs PROVED and kernel-certified that overflow or index out of bounds
    // (`tests/ui/trust/slice_pattern_spellings_alias_refused.rs`; the 2026-09-17 pack
    // proved them too). They now overlap unless they are provably different elements:
    // two from-start constants, or two from-end ones, with different offsets.
    if literal_index_segments_may_alias(a, b) {
        return true;
    }
    // Trust: 2026-09-16 (round A9, corrected round A10) — the INDEX LOCAL INSIDE A
    // PROJECTION is deliberately NOT a clause of this predicate. `s*[_3]` embeds local
    // 3 by number, and a write to local 3 rebinds that name — but the relation is
    // DIRECTIONAL (a write of `_3` rebinds `s*[_3]`; a store to `s*[_3]` never rebinds
    // `_3`), and this predicate is SYMMETRIC by contract: its call sites pass
    // (written, read) in both orders. A symmetric clause here made an ELEMENT STORE
    // `(*a)[_11] = 1` count as a write of its own index local `_11`, which killed the
    // entry defs of `_11` at the store's block and refuted three correct programs
    // (`ctl_shadow_store_loop` and its twins, `tests/escaped_local_seam_realmir.rs`).
    // The directional relation lives in [`write_rebinds`], which every "does this
    // WRITE affect this READ" site calls with the written name first.
    false
}

/// True iff `a` and `b` first diverge inside an INDEX segment on both sides (the
/// segments start at the same byte with `[`) and those two segments may name the same
/// element: a symbolic or subslice segment may name any element; two constant
/// segments name the same one iff they count from the same end and their offsets
/// are equal, whatever minimum length they carry. See [`place_names_overlap`].
///
/// Trust (merge 2026-10-14): `pub(super)` for the rebinder index
/// (`rebind_index`, its LITERAL-INDEX ALIAS channel), which finds the candidates by
/// lookup and asks this predicate for the answer.
pub(super) fn literal_index_segments_may_alias(a: &str, b: &str) -> bool {
    if !a.contains('[') || !b.contains('[') {
        return false;
    }
    let (ab, bb) = (a.as_bytes(), b.as_bytes());
    // Walk the common prefix, remembering where the current TOP-LEVEL segment began
    // (a subslice `[1..4]` contains `.`, which is a segment lead only outside `[]`).
    let (mut seg_start, mut depth, mut i) = (0usize, 0usize, 0usize);
    while i < ab.len() && i < bb.len() && ab[i] == bb[i] {
        if depth == 0 && crate::is_projection_segment_lead(ab[i]) {
            seg_start = i;
        }
        match ab[i] {
            b'[' => depth += 1,
            b']' => depth = depth.saturating_sub(1),
            _ => {}
        }
        i += 1;
    }
    if depth == 0 {
        // Diverged BETWEEN segments: both must open a new index segment right here.
        seg_start = i;
    }
    fn segment(s: &str, seg_start: usize) -> Option<&str> {
        let rest = s.get(seg_start..)?.strip_prefix('[')?;
        Some(&rest[..rest.find(']')?])
    }
    let (Some(sa), Some(sb)) = (segment(a, seg_start), segment(b, seg_start)) else {
        return false;
    };
    match (literal_index_segment_constant(sa), literal_index_segment_constant(sb)) {
        (Some((end_a, off_a)), Some((end_b, off_b))) if end_a == end_b => off_a == off_b,
        _ => true,
    }
}

/// `(from_end, offset)` of a CONSTANT index segment's inner text (`0`, `0;min=2`,
/// `-1;min=1`, `3;slice`); `None` for any other spelling (a symbolic `_k`, a subslice
/// `1..-0`, anything that does not parse). The one classification
/// [`literal_index_segments_may_alias`] and the rebinder index's literal channel share.
pub(super) fn literal_index_segment_constant(inner: &str) -> Option<(bool, u128)> {
    if inner.contains("..") || inner.starts_with('_') {
        return None;
    }
    let head = inner.split(';').next()?;
    match head.strip_prefix('-') {
        Some(k) => Some((true, k.parse().ok()?)),
        None => Some((false, head.parse().ok()?)),
    }
}

/// THE DIRECTIONAL WRITE/READ RELATION over place names: true iff a write (or havoc)
/// of the name `written` rebinds what the name `read` denotes. It is
/// [`place_names_overlap`] (equal, prefix ancestor / descendant, symbolic-index alias
/// — symmetric) plus the one channel that is NOT symmetric and holds for EVERY kind
/// of written name, a direct destination or a havoc-list base name alike:
///
///  * `write_covers_index_segment(written, read)` — a whole write of local `l`,
///    spelled by its fallback `_l`, rebinds every name carrying the segment `[_l]`
///    (`s*[_l]`, `s*[_l]__slice_len`, anything projected below); a store INTO
///    `s*[_l]` rebinds no index local.
///
/// Trust: 2026-09-16 (round A10). The gen-sets carry the fallback `_l` beside the
/// canonical name for every whole-local write of an index local
/// (`extend_with_assigned_place_dests`, `terminator_def_names`,
/// `mutably_borrowed_local_names`, gated by [`local_is_index_operand`]), so the
/// version-token gate, the inter-block entry map, the kill (`formula_mentions_redef`),
/// the per-statement search (`stmt_writes_name`) and the MID-BLOCK prefix kill
/// ([`v2_live_path_defs_at_point`], whose `prefix_kill` is `writes_until` — the same
/// fallback mint, restricted to `stmts[..point]`) all see a reseat of `j` through
/// this one relation, called with the WRITTEN name first. MEASURED without it: `let
/// mut j = 0; let n = s[j].len().min(100); j = k; s[j][..n]` — `_12 = copy (*_1)[_3]`
/// before the reseat and `_13 = copy (*_1)[_3]` after it both read
/// `s*[_3]__slice_len`, ONE unversioned name, the two copy ties equated the two
/// slices' lengths, and the `RangeTo` row PROVED kernel-certified on a panicking
/// program (`index_local_min_bug`).
///
/// The derived-length channel (`write_covers_derived_slice_len`) is deliberately NOT
/// part of this relation: see [`dest_write_rebinds`].
pub(crate) fn write_rebinds(written: &str, read: &str) -> bool {
    place_names_overlap(written, read) || write_covers_index_segment(written, read)
}

/// [`write_rebinds`] for an explicit DESTINATION name — a statement / terminator
/// destination, a `Deinit`, a def's lhs — which additionally rebinds the derived
/// length metadata of what it writes (`write_covers_derived_slice_len`): a whole
/// write of `s` (or of an ancestor of `s`) reseats the fat pointer and so its
/// `s__slice_len`; an element store below `s` does not.
///
/// Only a DESTINATION carries that channel. A HAVOC-list base name does not: the
/// opaque deref-store havoc and the call havoc kill every mutable-pointer local's BASE
/// name (`s` for `s: &mut [u8]`), and treating that as a write of `s__slice_len` is the
/// false REFUTATION `extend_with_derived_slice_len`'s contract names — the `&mut [T]`
/// parameter's live length tie would be severed at every element store through it.
/// MEASURED (round A10, `rev9_pins::ctl_store_read_computed` at `-O0`, `if i + 1 <
/// s.len() { s[i + 1] = 1; s[i + 1] }`): with the derived channel applied to the
/// entry-map's tracked names, the store `(*_1)[_8] = 1` (unconfined, so the havoc
/// carries `s`) minted `s__slice_len#s4_0` for the read's borrow tie, disconnecting it
/// from the guard's `s__slice_len`, and four correct programs refuted. The direct-write
/// channel needs no base-name derivation there: every destination's own
/// `{dest}__slice_len` twin is minted into the gen-sets by `extend_with_derived_slice_len`
/// / `mutably_borrowed_havoc_names`, so the entry map tracks it by its own name.
pub(crate) fn dest_write_rebinds(written: &str, read: &str) -> bool {
    write_rebinds(written, read) || write_covers_derived_slice_len(written, read)
}

/// Trust: 2026-10-12 (UNION-SIBLING-WRITE-1, the wave-24 review) — THE UNION COVER of a
/// written place: the name of the value whose field the write projects through FIRST,
/// when that value may be a union ([`field_base_may_overlap_siblings`]), else `None`.
/// Every write oracle that names a statement or terminator DESTINATION adds this name
/// beside the destination's own, with the destination's channel: the gen-sets
/// ([`extend_with_assigned_place_dests`], [`stmt_direct_write_names`],
/// `block_writes::BlockWrites::build`), the per-statement search ([`stmt_writes_name`]),
/// a call destination ([`dest_term_extras`]) and the interval lane's statement transfer.
///
/// WHY. The place-name algebra ([`place_names_overlap`]) treats sibling fields `x.0` and
/// `x.1` as disjoint storage, which is false inside a union: its fields overlap at
/// offset 0. So `u.a = x as u8; u.b = -56; if x < 0x80 { u.a + 0x7f }` (with
/// `union V { a: u8, b: i8 }`) kept the fact `u.0 == x` (VC-NARROW-CAST-FALSE-REFUTE-1's
/// identity) across the write of `u.1`, the transport re-stated it on `u.0`'s version
/// after that write, and on the stage 1 of `51eac007f3` the `overflow:add` row was
/// kernel-certified and the advisory lane elided its check (the binary printed 71, rustc
/// panics). The widening twins (`u.a = x as u64; u.b = -1`) did the same BEFORE that
/// lane, through the widening cast's `dest == src` (review `udw.rs`, `w_udst_add`). The
/// name of the union value is a projection ANCESTOR of every one of its fields, so adding
/// it to the written names rebinds every sibling through the existing relation, with no
/// change to the relation or to its index.
///
/// The FIRST union on the projection chain: a union nested in a union field
/// (`u.0.1`) overlaps the outer union's other fields too, and a union field selected
/// before a `Deref` (`(*u.0).f`) aliases whatever its overlapping siblings point at.
/// Wider is the fail-closed direction (more names rebound). A whole write of the union
/// itself needs no cover (its own name is the ancestor).
///
/// Trust: 2026-10-12 (UNION-SIBLING-WRITE-2, the review of INTERVAL-WRITE-LOCKSTEP-2) —
/// the cover is taken on the place the write's NAME is minted from
/// ([`crate::canonical_place`], the referent fold [`place_to_var_name`] applies), not on
/// the syntactic place. A store through a reference into a union field
/// (`let r = &mut u.b; *r = n`, MIR `(*_4) = copy _2`) is NAMED `u.1`, but its
/// syntactic place `(*_4)` has no `Field` projection, so the walk answered `None`: no
/// oracle rebound `u.0`, and on the stage 1 of `0f03df468d` the `overflow:add` row of
/// `u.a = 5; *r = n; u.a + (usize::MAX - 5)` was PROVED and the advisory lane elided its
/// check (the binary printed 1 where rustc panics; also `&mut s.u.b`, and the narrowing
/// fixture's `narrow_dst` with the store through `&mut v.b`, which printed 71). On the
/// folded place the walk sees the union the referent crosses. An UNFOLDED deref keeps
/// its own spelling (`(*p).b` of a `p: &mut U` covers `p*`); the havoc lists carry the
/// cover of every place a pointer is taken to ([`mutably_borrowed_local_names`]).
pub(crate) fn union_write_cover_name(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> Option<String> {
    // A whole local has no cover, and is its own canonical place (the fold rewrites a
    // leading `Deref`; the value-alias rebase never rebases an unprojected place).
    if place.projections.is_empty() {
        return None;
    }
    let canonical = crate::canonical_place(func, place);
    let cut = union_write_cover_len(func, &canonical)?;
    Some(place_to_var_name(
        func,
        &trust_types::Place {
            local: canonical.local,
            projections: canonical.projections[..cut].to_vec(),
        },
    ))
}

/// Trust: 2026-10-12 (INTERVAL-WRITE-LOCKSTEP-2) — the names a write to `place` ITSELF
/// rebinds under: the place's own name and its union cover ([`union_write_cover_name`]).
/// The one spelling of "a destination and its cover" that the per-statement write oracle
/// ([`stmt_writes_name`]: `Assign`, `SetDiscriminant`, `Deinit`) and the interval lane's
/// statement transfer (`abstract_interp::transfer`: `transfer_function`'s destination and
/// `StmtWrite`'s `SetDiscriminant` / `Deinit`) both test, so the two lanes cannot
/// disagree about which names such a write reaches.
///
/// WHY. UNION-SIBLING-WRITE-1 added the cover to all three arms of the oracle but to
/// only the `Assign` arm of the interval lane; the lane's `SetDiscriminant` / `Deinit`
/// transfer kept forgetting the names under the place alone: after `u.b = 5`, a
/// `Deinit(u.a)` or a `discriminant(u.a) = 0` (`u: union { a: Option<u8>, b: u32 }`)
/// left `u.b ∈ [5, 5]` although each rewrites bytes `u.b` reads, and the lockstep check
/// of `transfer::transfer_statements` failed on it (`stmt_write_tests`).
pub(crate) struct WrittenPlace {
    name: String,
    cover: Option<String>,
}

impl WrittenPlace {
    pub(crate) fn of(func: &VerifiableFunction, place: &trust_types::Place) -> Self {
        WrittenPlace {
            name: place_to_var_name(func, place),
            cover: union_write_cover_name(func, place),
        }
    }

    /// `SetDiscriminant`'s channel: [`write_rebinds`] from the place or from its cover.
    pub(crate) fn rebinds(&self, read: &str) -> bool {
        write_rebinds(&self.name, read)
            || self.cover.as_deref().is_some_and(|c| write_rebinds(c, read))
    }

    /// A DESTINATION's channel (`Assign`, `Deinit`): [`dest_write_rebinds`] from the
    /// place or from its cover.
    pub(crate) fn dest_rebinds(&self, read: &str) -> bool {
        dest_write_rebinds(&self.name, read)
            || self.cover.as_deref().is_some_and(|c| dest_write_rebinds(c, read))
    }
}

/// The number of leading projections of `place` that name its union cover (see
/// [`union_write_cover_name`]): the index of the first `Field` projection whose base
/// value may be a union. FAIL-CLOSED: when the type walk cannot resolve a step, the
/// first `Field` at or after that step is the cut. `Some` is also the answer to "does
/// the place pass a possible union" (`local_defs::deref_read_unwritten_at`).
pub(crate) fn union_write_cover_len(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> Option<usize> {
    union_cover_len(&func.body.datatype_defs, crate::local_ty_ref(func, place.local), place)
}

/// Whether the fields of a value of type `ty` may OVERLAP one another — a union, or a
/// type this walk cannot classify. A stamped struct or enum (`adt_kind`), a tuple, a
/// closure or coroutine (its upvars) and a datatype with variants answer `false`. An
/// ADT the extractor did not stamp (`adt_kind: None` with no variants: every
/// synthetic `Ty::adt`) is read as a possible union, the G-STRUCT-KIND posture of
/// [`opaque_store_confined_to_written_place`]; a by-name marker resolves through the
/// body's table first, and an undefined one answers `true`.
pub(crate) use trust_types::interior_mutability::field_base_may_overlap_siblings;
/// [`union_write_cover_len`] over the root's type in hand (`base`, `None` when the root
/// is not declared): the one walk, for a caller that holds only a body
/// ([`shared_borrow_cell_places`]).
pub(crate) use trust_types::interior_mutability::union_cover_len;

/// True iff local `local` occurs as a `Projection::Index(local)` operand SOMEWHERE in
/// `func`'s body — i.e. some rendered place name may carry the segment `[_<local>]`.
/// Only such a local needs the fallback name `_<local>` minted beside its canonical
/// name in the write gen-sets (a fallback for any other local reaches nothing, and
/// doubling every gen-set measured as a 2.3x slowdown of the reaching-version
/// fixpoint on index-free bodies). Computed once per function (`fn_memo`), and
/// FAIL-CLOSED: a body containing a statement / rvalue / terminator shape the walk
/// cannot enumerate marks EVERY local, which is the unconditional mint.
pub(crate) fn local_is_index_operand(func: &VerifiableFunction, local: usize) -> bool {
    IndexLocals::of(func).contains(local)
}

/// [`local_is_index_operand`]'s per-function table, held by a caller that asks about
/// many locals: fetched ONCE instead of once per question (outside a `gen_work` scope
/// the memo is inert, and every [`local_is_index_operand`] call is a whole-body walk).
pub(crate) struct IndexLocals(std::rc::Rc<Vec<bool>>);

impl IndexLocals {
    pub(crate) fn of(func: &VerifiableFunction) -> IndexLocals {
        if !crate::gen_work::scope_active()
            && let Some(rc) = super::index_locals_for(func)
        {
            return IndexLocals(rc);
        }
        IndexLocals(crate::fn_memo::index_locals(func, || {
            super::index_locals_for(func).map_or_else(
                || index_locals_uncached(func),
                |rc| std::rc::Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone()),
            )
        }))
    }

    /// [`local_is_index_operand`]`(func, local)` — out-of-table locals answer `true`
    /// (fail-closed: the unconditional mint).
    pub(crate) fn contains(&self, local: usize) -> bool {
        self.0.get(local).copied().unwrap_or(true)
    }
}

pub(super) fn index_locals_uncached(func: &VerifiableFunction) -> Vec<bool> {
    /// Mark every `Index(l)` segment of `place`; an index local outside the locals
    /// table cannot be represented and fails the walk closed.
    fn mark(place: &trust_types::Place, set: &mut [bool], complete: &mut bool) {
        for proj in &place.projections {
            if let trust_types::Projection::Index(l) = proj {
                match set.get_mut(*l) {
                    Some(slot) => *slot = true,
                    None => *complete = false,
                }
            }
        }
    }
    fn mark_op(op: &Operand, set: &mut [bool], complete: &mut bool) {
        match op {
            Operand::Copy(p) | Operand::Move(p) => mark(p, set, complete),
            Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => {}
            // `#[non_exhaustive]` in `trust-types`: an operand shape this crate has
            // never seen may carry a place; fail closed.
            #[allow(unreachable_patterns)]
            _ => *complete = false,
        }
    }
    let n = func.body.locals.len();
    let mut set = vec![false; n];
    let mut complete = true;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    mark(place, &mut set, &mut complete);
                    let mut c = true;
                    let all =
                        super::iterator_yield::for_each_rvalue_operand_place(rvalue, &mut |p| {
                            mark(p, &mut set, &mut c)
                        });
                    complete &= all && c;
                }
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place }
                | Statement::PlaceMention(place) => mark(place, &mut set, &mut complete),
                Statement::Intrinsic { args, .. }
                | Statement::Unsupported { operands: args, .. } => {
                    for op in args {
                        mark_op(op, &mut set, &mut complete);
                    }
                }
                Statement::CopyNonOverlapping { src, dst, count, .. } => {
                    for op in [src, dst, count] {
                        mark_op(op, &mut set, &mut complete);
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                #[allow(unreachable_patterns)]
                _ => complete = false,
            }
        }
        match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                for op in args {
                    mark_op(op, &mut set, &mut complete);
                }
                mark(dest, &mut set, &mut complete);
            }
            Terminator::TailCall { args, .. } => {
                for op in args {
                    mark_op(op, &mut set, &mut complete);
                }
            }
            Terminator::SwitchInt { discr: op, .. } | Terminator::Assert { cond: op, .. } => {
                mark_op(op, &mut set, &mut complete);
            }
            Terminator::Drop { place, .. } => mark(place, &mut set, &mut complete),
            Terminator::Goto(_)
            | Terminator::Return
            | Terminator::Opaque { .. }
            | Terminator::Unreachable
            | Terminator::Resume => {}
            #[allow(unreachable_patterns)]
            _ => complete = false,
        }
    }
    if !complete {
        return vec![true; n];
    }
    set
}

/// The fallback spelling of local `local` — `_<local>` — the ONE name that denotes
/// that local and no other (see `place_to_var_name`'s fallback-collision demotion).
/// Minted beside the canonical (source) name into every write gen-set so a write to
/// an index local reaches the names that embed it by number (`[_<local>]`).
pub(crate) fn local_fallback_name(local: usize) -> String {
    format!("_{local}")
}

/// True iff `written` is a fallback spelling `_<l>` and `name` carries the index
/// segment `[_<l>]` — a name that embeds local `l` by number as an array/slice index.
/// The segment is matched whole (`[_3]` never matches `[_30]`), and a name that IS
/// the fallback (`_3` written, `_3` read) is the plain equality the caller already
/// tests. An already-versioned name (`s*[_3]#s0_0`) matches on its segment exactly as
/// the prefix and symbolic-index clauses above match a versioned descendant (`s*[_3]#t`
/// is a descendant of `s`): the kill may drop a pinned fact its token already keeps
/// name-disjoint, which is the monotone direction. Alloc-free: this sits on the
/// version oracle's hot path.
pub(crate) fn write_covers_index_segment(written: &str, name: &str) -> bool {
    let Some(digits) = written.strip_prefix('_') else { return false };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    let bytes = name.as_bytes();
    let mut from = 0usize;
    while let Some(off) = name[from..].find('[') {
        let start = from + off + 1;
        if name[start..].starts_with(written) && bytes.get(start + written.len()) == Some(&b']') {
            return true;
        }
        from = start;
    }
    false
}

/// True if fact `f` SURVIVES redefinition of the place names in `redefined`: none
/// of `f`'s free variables overlaps any redefined name. Prefix-aware (Trust
/// #soundness round-11), so redefining a whole value `x` also invalidates facts
/// about `x.0` / `x[i]` / `*x` — keying staleness on exact names alone let a
/// stale `x.0 == a` survive `x = move y` and vacuously discharge a VC over the
/// new value's field. Dropping more facts is monotone-sound (PROVE -> FAIL only).
///
/// This scan is the REFERENCE form. Production tests go through [`KillSet`] (the same
/// decision, answered by an index over the set) or a per-read probe
/// ([`formula_survives_redefs_by`]); both are cross-checked against this one under
/// `cfg(test)`.
#[cfg(any(test, feature = "version-oracle-differential"))]
pub(crate) fn formula_survives_redefs(f: &Formula, redefined: &FxHashSet<String>) -> bool {
    // Trust (lane-A CSE): alloc-free equivalent of
    // `f.free_variables().iter().all(|v| !redefined.iter().any(|n| overlap(v, n)))`.
    // The old form materialized an `FxHashSet<String>` of cloned free-var names
    // (plus per-node child `Vec`s) per fact per block-dequeue; the predicate below
    // early-exits on the first overlapping free mention and walks the tree without
    // allocating. Same binder exclusion as `free_variables_inner` (a Forall/Exists
    // bound var is never a free mention), so the verdict is byte-identical.
    redefined.is_empty() || !formula_mentions_redef(f, redefined, &[])
}

/// [`formula_survives_redefs`] for a HAVOC set — the call, opaque-store and drop
/// lists of `v2_path_def_fixpoint`. The overlap and index-segment relation
/// ([`write_rebinds`]) applies to every name; the derived slice-length channel
/// ([`write_covers_derived_slice_len`]) applies to every PROJECTED name and to no
/// BARE one ([`havoc_rebinds`]).
///
/// A bare local in these lists is either a pointer whose POINTEE may change
/// ([`mutable_pointer_local_names`]: `w` of a `&mut [T]` parameter, whose length
/// lives in the pointer and does not move when an element is stored), or a name
/// whose own length twin is minted beside it: a mutably borrowed root's
/// `s__slice_len` ([`mutably_borrowed_havoc_names`]) and a call destination's
/// (`push_derived_slice_len`). A projected name is a written PLACE, and when that
/// place holds a fat pointer its length moves with it: a user callee's refined
/// write path `s*` (`callee_write_set::refine_call_havoc_delta`) reseats `*s` of an
/// `s: &mut &[u8]`. The refinement mints `s*__slice_len` beside it since the audit
/// below (the version gen-sets need the name itself); the channel here keeps the
/// kill right for any projected name a list carries without its twin.
///
/// Trust (2026-09-29): the fixpoint applied the destination relation to these
/// lists, so every element store through a `&mut [T]` parameter severed its
/// length tie at the loop header: `if v.len() == w.len() { for i in 0..v.len() {
/// w[i] = 0 } }` was refuted with `w__slice_len = 0` (u02, u03, t01, r29 of the
/// ordinary-Rust sweep). `3b4293d06cb` then withheld the channel from EVERY havoc
/// name, and an audit the same day measured the refined-path hole as proofs of
/// programs that panic: `fn sset(s: &mut &[u8], t: &[u8]) { *s = t }` and
/// `if i <= s.len() { sset(s, t); &s[..i] }` (and `t.len() - 1` after the same
/// reseat, and its `&str` and struct-field twins). The channel is back for projected
/// names, and the refinement mints the twin.
/// `tests/ui/trust/callee_reseat_kills_the_length_refused.rs` pins the reseats, and
/// `tests/opaque_deref_store_reseat.rs` holds both directions for opaque stores.
///
/// Merge 2026-10-14: upstream judges the opaque-store havoc with [`KillSet::havoc`]
/// (the plain relation for EVERY name). The fixpoint's store kill asks both: the
/// plain kill over the whole list, and this relation over its PROJECTED names (a
/// stored-reference pointee `X*.f*` whose own fat pointer an opaque store may
/// reseat), so a fact survives only when both admit it.
pub(crate) fn formula_survives_havoc(f: &Formula, havoc: &FxHashSet<String>) -> bool {
    havoc.is_empty() || !formula_mentions_written(f, havoc, &[], havoc_rebinds)
}

/// The write/read relation of a HAVOC name (written first): [`write_rebinds`], plus
/// the derived slice-length channel when `written` is a projected place. See
/// [`formula_survives_havoc`] for why a bare name is spared that channel.
fn havoc_rebinds(written: &str, read: &str) -> bool {
    write_rebinds(written, read)
        || (written.bytes().any(crate::is_projection_segment_lead)
            && write_covers_derived_slice_len(written, read))
}

/// A kill set prepared for many [`formula_survives_redefs`] tests: its names are
/// indexed by place structure (`rebind_index::RebindIndex`, `Dest` mode — exactly
/// `dest_write_rebinds`), so each free mention of a tested fact is answered by
/// lookups keyed on the mention instead of a scan of the whole set.
///
/// THE COST THIS REMOVES. `formula_survives_redefs(f, set)` tests every free
/// mention of `f` against EVERY name of `set`. The path-definition fixpoint kills its
/// threaded facts with a terminator's write set — the whole-function havoc list at
/// every call — so each block paid facts × mentions × havoc names; on
/// `ever-init-many-locals` (every `Box` local a pointer local, every
/// `Box::new`/`drop` a call) that was the dominant cost of VC generation.
///
/// Same decision, fact by fact: `survives(f)` is `formula_survives_redefs(f, set)`
/// with the per-mention `set.iter().any(|n| dest_write_rebinds(n, mention))`
/// answered by the index, which visits exactly the members that relation relates
/// (see `rebind_index`). Under `cfg(test)` every answer is cross-checked against the
/// scan.
pub(crate) struct KillSet {
    empty: bool,
    table: super::rebind_index::NameTable,
    index: super::rebind_index::RebindIndex,
    /// The relation the members carry: `Dest` for WRITTEN names (a destination
    /// also rebinds its derived `__slice_len`), `Plain` for HAVOC base names
    /// ([`KillSet::havoc`]).
    mode: super::rebind_index::RebindMode,
    /// PERF-COMPILER-VCGEN-807: `kills(name)` answers, memoized. The set is
    /// immutable after construction, so a name's answer never changes; the
    /// path-definition fixpoint asks the SAME names (every free variable of every
    /// fact, each iteration) of the same per-block sets over and over, and each
    /// uncached answer is several hash lookups plus a sorted-range search.
    memo: std::cell::RefCell<FxHashMap<Box<str>, bool>>,
    #[cfg(any(test, feature = "version-oracle-differential"))]
    reference: FxHashSet<String>,
}

impl KillSet {
    pub(crate) fn new<'a>(names: impl IntoIterator<Item = &'a String>) -> KillSet {
        Self::with_mode(names, super::rebind_index::RebindMode::Dest)
    }

    /// A kill set of HAVOC BASE names — the opaque deref-store havoc
    /// (`deref_store_havoc_names`) — judged with the PLAIN relation
    /// (`write_rebinds`), never the destination relation.
    ///
    /// Trust (2026-09-29). A havoc base `s` (for `s: &mut [u8]`, a
    /// `mutable_pointer_local_names` member) stands for the memory REACHABLE THROUGH
    /// `s` that an opaque store may write; `s`'s own value — the fat pointer and its
    /// length metadata `s__slice_len` — lives in `s`'s slot, which only a pointer TO
    /// that slot can write.
    ///
    /// THE PREMISE, and the whole of it: every pointer that can write a local's slot
    /// is minted by one of the three SLOT-WRITE CHANNELS — `&mut s`, `&raw mut s`, or
    /// `&raw const s` of an owned place ([`own_storage_write_borrow`], the one
    /// statement of the rule) — and each makes `s` a `mutably_borrowed_havoc_names`
    /// member whose `__slice_len` twin is minted into the list EXPLICITLY. A write
    /// through a pointer derived from a SHARED reference is UB under Stacked Borrows
    /// and Tree Borrows alike and is not a channel. Until 2026-09-30 the list named
    /// `&mut` / `&raw mut` only; a write through `&raw const s as *mut _` (defined
    /// under Tree Borrows for a `let mut s`) then left `s__slice_len` live across
    /// the reseat, and the fixpoint-outflow kill below turned the `&mut [u8]` loop
    /// reseat into a kernel-certified false proof (the destination relation's
    /// over-kill of a mutable-pointer base had covered it by accident; the
    /// straight-line, call and shared-slice shapes were false proofs before this
    /// relation landed). Pinned by tests/opaque_deref_store_reseat.rs
    /// (`a_raw_const_slot_reseat_*` and the rest of its `&raw const` section).
    ///
    /// So the destination relation's derived channel (`write_covers_derived_slice_len`)
    /// must not be applied to a havoc base name; `dest_write_rebinds`' own contract
    /// says exactly that, and the version oracle already follows it. Three kill sites
    /// did not, and each is now built with this: the path-definition fixpoint's
    /// outflow kill (`v2_path_def_fixpoint`), the hardened twin's entry-fact kill
    /// (`block_entry_fact_kill`), and — through the write index's `havoc_rebinds`,
    /// the same relation — the conservative whole-block arm of the per-point prefix
    /// kill (`StmtVersionCtx::prefix_kill_rebinds`). Each severed
    /// `_6__slice_len == digits__slice_len` at an element store through `digits`:
    /// the store half of `digits[i] -= 1` and the hardened twin of a bounds assert
    /// after `s[i] = 1` were refuted at a length of 0 beside a length of 1, and an
    /// element store in a loop dropped `s__slice_len == 8`
    /// (tests/false_refutation_shapes_realmir.rs, tests/opaque_deref_store_reseat.rs).
    /// NOT changed, and still the destination relation: a store that PRECEDES the
    /// row's point in its own block (`WriteIndex::gate`) and the terminator-row kill
    /// (`v2_live_path_defs`) — no fixture here distinguishes them, so they keep their
    /// measured behaviour. Everything reachable through the pointer still dies under
    /// the plain relation: `s*`, `s*[_i]`, `s*.f__slice_len` all overlap `s`. What
    /// keeps it SOUND is the explicit twin over the complete channel list: drop
    /// `push_derived_slice_len` from `mutably_borrowed_havoc_names` and the three
    /// reseat canaries of tests/opaque_deref_store_reseat.rs fail (measured
    /// 2026-09-29); drop the `&raw const` arm of [`own_storage_write_borrow`] and the
    /// `&raw const` canaries of the same file fail (measured 2026-09-30).
    pub(crate) fn havoc<'a>(names: impl IntoIterator<Item = &'a String>) -> KillSet {
        Self::with_mode(names, super::rebind_index::RebindMode::Plain)
    }

    fn with_mode<'a>(
        names: impl IntoIterator<Item = &'a String>,
        mode: super::rebind_index::RebindMode,
    ) -> KillSet {
        let mut table = super::rebind_index::NameTable::default();
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let diff_enabled = super::differential_enabled();
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let mut reference: FxHashSet<String> = FxHashSet::default();
        let mut ids = Vec::new();
        for n in names {
            ids.push(table.intern(n));
            #[cfg(any(test, feature = "version-oracle-differential"))]
            if diff_enabled {
                reference.insert(n.clone());
            }
        }
        let index = super::rebind_index::RebindIndex::build(&table, ids.iter().copied());
        KillSet {
            empty: ids.is_empty(),
            table,
            index,
            mode,
            memo: std::cell::RefCell::new(FxHashMap::default()),
            #[cfg(any(test, feature = "version-oracle-differential"))]
            reference,
        }
    }

    /// Some name of the set rebinds `read` — `dest_write_rebinds` for a set built
    /// by [`KillSet::new`], `write_rebinds` for one built by [`KillSet::havoc`].
    pub(crate) fn kills(&self, read: &str) -> bool {
        let _ = &self.table;
        if self.empty {
            return false;
        }
        if let Some(&hit) = self.memo.borrow().get(read) {
            return hit;
        }
        let answer = self.index.any_rebinder(read, self.mode);
        self.memo.borrow_mut().insert(Box::from(read), answer);
        answer
    }

    /// `formula_survives_redefs(f, set)` (or its plain-relation twin for a havoc set).
    pub(crate) fn survives(&self, f: &Formula) -> bool {
        let survives = self.empty || formula_survives_redefs_by(f, &mut |n| self.kills(n));
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if super::differential_enabled() {
            let reference = match self.mode {
                super::rebind_index::RebindMode::Dest => {
                    formula_survives_redefs(f, &self.reference)
                }
                super::rebind_index::RebindMode::Plain => formula_survives_redefs_by(f, &mut |n| {
                    self.reference.iter().any(|w| write_rebinds(w, n))
                }),
            };
            assert_eq!(survives, reference, "KillSet differential on {f:?}");
        }
        survives
    }
}

/// [`formula_survives_redefs`] against a kill set given as a PROBE instead of a
/// materialised set: `kills(name)` answers "some name of the set
/// `dest_write_rebinds` `name`", which is exactly what the set form tests at every
/// free mention (`redefined.iter().any(|n| dest_write_rebinds(n, name))`). Same binder
/// exclusion, same early exit — so the same decision over the same set, without the
/// set.
pub(crate) fn formula_survives_redefs_by(f: &Formula, kills: &mut dyn FnMut(&str) -> bool) -> bool {
    !formula_mentions_redef_by(f, kills, &[])
}

fn formula_mentions_redef_by(
    f: &Formula,
    kills: &mut dyn FnMut(&str) -> bool,
    bound: &[&str],
) -> bool {
    match f {
        Formula::Var(name, _) => !bound.contains(&name.as_str()) && kills(name),
        Formula::SymVar(sym, _) => {
            let name = sym.as_str();
            !bound.contains(&name) && kills(name)
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let mut extended: Vec<&str> = bound.to_vec();
            extended.extend(bindings.iter().map(|(sym, _)| sym.as_str()));
            formula_mentions_redef_by(body, kills, &extended)
        }
        _ => !trust_types::all_formula_children(f, |c| !formula_mentions_redef_by(c, kills, bound)),
    }
}

/// True iff some FREE variable of `f` overlaps a name in `redefined` (i.e. the fact
/// does NOT survive). Alloc-free, early-exiting twin of the `free_variables`-based
/// check in [`formula_survives_redefs`]. `bound` carries the quantifier-bound names
/// in scope; a `Var`/`SymVar` whose name EXACTLY equals a bound name is excluded
/// from the mention test — mirroring `Formula::free_variables_inner`'s
/// `!bound.contains(name)` binder handling exactly (the overlap test only ever runs
/// on genuinely-free names).
#[cfg(any(test, feature = "version-oracle-differential"))]
pub(super) fn formula_mentions_redef(
    f: &Formula,
    redefined: &FxHashSet<String>,
    bound: &[&str],
) -> bool {
    formula_mentions_written(f, redefined, bound, dest_write_rebinds)
}

/// [`formula_mentions_redef`] under an explicit write/read relation `rebinds`
/// (called WRITTEN name first): [`dest_write_rebinds`] for a destination kill set,
/// [`write_rebinds`] for a havoc set ([`formula_survives_havoc`]).
fn formula_mentions_written(
    f: &Formula,
    redefined: &FxHashSet<String>,
    bound: &[&str],
    rebinds: fn(&str, &str) -> bool,
) -> bool {
    match f {
        // Trust #soundness (2026-08-25): a redefinition of `p` also kills the DERIVED
        // `p__slice_len`. `place_names_overlap` alone cannot see that — `_` is not a
        // projection separator, so `place_names_overlap("p__slice_len", "p")` is FALSE
        // — and `write_covers_derived_slice_len` is the predicate that closes exactly
        // that gap everywhere else in this file.
        //
        // MEASURED, the shape that exposed it (`/tmp/r6/r6.rs`, extracted MIR):
        //     bb0[3]: _6 = AddressOf(_2.Deref)   // p = &raw const *sa
        //             -> ties `_6__slice_len == _2__slice_len` (len 3)
        //     bb1[1]: _6 = Use(Move(_7))         // p = &raw const *sb (len 1)
        //     bb3[1]: _11 = PtrMetadata(Copy(_6))
        // The reassignment is an `Rvalue::Use`, and `push_borrow_slice_len` is called
        // ONLY from the `Ref`/`AddressOf` arms — never `Use` — so bb1 emits a def named
        // `_6` and NO `_6__slice_len` def. Without the bridge the bb0 tie was not killed
        // on that path, survived the join, and discharged `2 < _2__slice_len` = `2 < 3`:
        // a `proved`, kernel-certified bounds row on a program that panics with
        // "index out of bounds: the len is 1 but the index is 2".
        //
        // KILLING is the correct direction, and PROPAGATING through `Use` would be
        // wrong: emitting a fresh tie there would put `== sa__slice_len` and
        // `== sb__slice_len` on the SAME join variable — a contradiction, i.e. a
        // vacuous proof of everything. Dropping the fact can only turn a PROVE into a
        // FAIL, never the reverse.
        // Trust (round A10): `n` is the WRITTEN name and `name` the fact's free read —
        // the relation is directional and must be called in that order (a store to
        // `a*[_11]` in `redefined` must not read as a write of `_11`). The derived
        // channel is kept here as it always was (`redefined` is a kill set; dropping
        // more is the monotone direction).
        Formula::Var(name, _) => {
            !bound.contains(&name.as_str()) && redefined.iter().any(|n| rebinds(n, name))
        }
        // SymVar carries a `Symbol`; resolve to its `&str` for the same name check.
        Formula::SymVar(sym, _) => {
            let name = sym.as_str();
            !bound.contains(&name) && redefined.iter().any(|n| rebinds(n, name))
        }
        // Quantifiers extend the bound set with their binding names; only the body
        // is a sub-formula (the bindings are not). Matches `children()` + the
        // `bound ∪ bindings` recursion in `free_variables_inner`.
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let mut extended: Vec<&str> = bound.to_vec();
            extended.extend(bindings.iter().map(|(sym, _)| sym.as_str()));
            formula_mentions_written(body, redefined, &extended, rebinds)
        }
        // Every other node: recurse into its sub-formulas with the same bound set.
        _ => !trust_types::all_formula_children(f, |c| {
            !formula_mentions_written(c, redefined, bound, rebinds)
        }),
    }
}

/// Names of locals written by a block's TERMINATOR (currently a `Call` dest).
// Trust: `extract_block_definitions` scans only `block.stmts`, so it misses a
// value the terminator reassigns. rustc usually lowers `lo = call()` as a call
// into a temp plus a follow-up statement `lo = <temp>` (which the statement kill
// catches), but a direct `Call { dest: lo }` lowering would otherwise strand a
// stale fact (e.g. `hi >= lo`) in the successor block. Used to harden the fact
// THREADING in `build_semantic_guard_map`.
/// True iff `ty` is a PURE VALUE — a scalar or an aggregate of scalars with NO
/// reference / raw pointer / opaque component anywhere. A callee receiving only
/// such values (by Copy or as constants) has NO path to any caller local.
/// FAIL-CLOSED by construction: `Adt` is rejected even when its `fields` list
/// looks pointer-free, because extraction ERASES fields for opaque std types
/// (`Vec<u32>` carries `fields: []` yet holds a raw pointer); `Slice` is a fat
/// pointer; `Closure`/`Coroutine` hide captures; anything unrecognized is false.
pub(super) fn ty_is_pure_value(ty: &Ty) -> bool {
    match ty {
        Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Unit => true,
        Ty::Tuple(ts) => ts.iter().all(ty_is_pure_value),
        Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => ty_is_pure_value(elem),
        _ => false,
    }
}

/// Trust (2026-10-15, DECISION_QUEUE D101): is the reference PARAMETER `param` the only
/// channel this body has to its pointee? Every OTHER parameter is a pure value, or a
/// shared reference to a pure value, a slice of pure values or a `str` (none of which
/// can write anything), and the body launders no address through a raw pointer
/// ([`func_has_pointer_laundering`]).
///
/// A fact about `*param` that survives a call or store through ANOTHER argument (a
/// second `&mut Vec`, a raw pointer, a `&RefCell`, a struct holding one) rests on the
/// two arguments not aliasing: Rust's `noalias`, which `docs/DECISION_QUEUE.md` D96
/// adopts only DISCLOSED and DEMOTED (R1: no `Certified` row on an
/// unproved aliasing assumption), through the compiler-installed `NOALIAS_MUT_ARGS`
/// premise, never silently. A lane that keeps such a fact without that premise asks
/// this first. One predicate for every such lane (the length-invariant tie
/// `value_facts::vec_length_is_invariant`, the `Vec` pre-mutation region
/// `vec_region::region_root_eligible`, and the abstract-length stability gate
/// `guards::local_mut_borrows_may_resize` behind main's `coll_len` ties and scalar-index
/// recovery), so they cannot drift apart.
pub(crate) fn param_is_sole_channel_to_its_pointee(
    func: &VerifiableFunction,
    param: usize,
) -> bool {
    let reaches_nothing = |ty: &Ty| {
        ty_is_pure_value(ty)
            || matches!(ty, Ty::Ref { mutable: false, inner } if match inner.as_ref() {
                Ty::Slice { elem } => ty_is_pure_value(elem),
                Ty::Str => true,
                other => ty_is_pure_value(other),
            })
    };
    (1..=func.body.arg_count)
        .filter(|&local| local != param)
        .all(|local| crate::local_ty_ref(func, local).is_some_and(reaches_nothing))
        && !func_has_pointer_laundering(func)
}

/// A call argument that hands the callee NO pointer: a constant, or a `Copy`/`Move`
/// of a place whose type is a pure pointer-free value ([`ty_is_pure_value`]).
/// Trust (ENC-DEFECTS 13b): `Move` is admitted beside `Copy` — see the call arm of
/// [`terminator_def_names`].
fn arg_is_pure_value(func: &VerifiableFunction, arg: &Operand) -> bool {
    match arg {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) => matches!(
            crate::place_ty_cow(func, p).as_deref(),
            Some(ty) if ty_is_pure_value(ty)
        ),
        _ => false,
    }
}

/// [`arg_is_pure_value`] for the call arm of [`terminator_def_names_structured`]: a
/// CONSTANT is admitted only when its value is pointer-free ([`const_is_pure_value`]).
///
/// Trust (TINV-18 correction, 2026-10-06): `arg_is_pure_value` admits every constant,
/// but a constant `&'static` to a static with interior mutability (`A.store(..)`'s
/// `const {alloc}: &AtomicU8`, extracted as an opaque constant) or a constant raw
/// pointer hands the callee a write channel. The 13b narrowing keeps the older
/// predicate: its premise is the protector on the reborrowed root, which no constant
/// can bypass.
fn arg_hands_no_pointer(func: &VerifiableFunction, arg: &Operand) -> bool {
    match arg {
        Operand::Constant(c) => const_is_pure_value(c),
        _ => arg_is_pure_value(func, arg),
    }
}

/// Whether a constant operand's value holds no pointer through which a callee could
/// write: a scalar, unit, a zero-sized callable item, or a shared reference to
/// read-only promoted bytes (a `&str` / byte-string literal, a promoted payload-less
/// `&Enum::Variant`, a valtree-built `&` to an all-scalar struct, which the
/// extractor never builds for a static, an `UnsafeCell` or a raw pointer). An opaque
/// reference constant, a memory image (it can hold pointers) and every later kind
/// answer `false`.
pub(super) fn const_is_pure_value(c: &trust_types::ConstValue) -> bool {
    use trust_types::ConstValue as C;
    matches!(
        c,
        C::Bool(_)
            | C::Int(_)
            | C::Uint(..)
            | C::Float(_)
            | C::FloatBits { .. }
            | C::Unit
            | C::OpaqueScalar { .. }
            | C::ConstParam { .. }
            | C::CallableItem { .. }
            | C::Str { .. }
            | C::UnitVariantRef { .. }
            | C::EmptyClosureRef { .. }
            | C::StructScalarFieldsRef { .. }
    )
}

/// Trust (TINV P1 on real MIR, 2026-10-06): a call argument through which the callee
/// can WRITE nothing — see the call arm of [`terminator_def_names_structured`]. One of:
///  * a `Copy`/`Move` of a by-value [`ty_is_recorded_pure_frozen_value`]: the callee
///    receives bits, as for [`arg_is_pure_value`], which this widens from scalars to
///    ADTs the extractor stamped and recorded;
///  * when `fenced` (the callee is not foreign, has no `unsafe` signature and is not an
///    atomic intrinsic: the TRUST-10 / 13b fences), a `Copy`/`Move` of a whole local
///    SHARED reference whose pointee is [`pointee_is_read_only`] and which is not a
///    reborrow through a `&mut` or raw pointer ([`shared_ref_avoids_mutable_roots`]):
///    every byte the callee can reach through it is `Freeze` and behind shared
///    references only, so any write through it is UB (docs/TCB.md, "Calls whose
///    arguments grant no write").
///
/// A reborrow of memory under a `&mut`/raw pointer (`&*self` in a `&mut self` method)
/// is deliberately NOT admitted here, although the same premise covers it: those calls
/// stay with the TRUST-10 and 13b refinements and their own gates, so this widening
/// never decides a call either of them was built to decide. A `&mut`, a raw pointer, a
/// `Box`, a closure, a `dyn`, an `UnsafeCell` anywhere, an unstamped or field-less ADT,
/// a by-name `Datatype` marker and every other shape are refused.
fn arg_grants_no_write(func: &VerifiableFunction, arg: &Operand, fenced: bool) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = arg else { return false };
    let Some(ty) = crate::place_ty_cow(func, p) else { return false };
    if ty_is_recorded_pure_frozen_value(&ty) {
        return true;
    }
    match ty.as_ref() {
        Ty::Ref { mutable: false, inner } => {
            fenced
                && p.projections.is_empty()
                && if pointee_is_read_only(inner, 8) {
                    shared_ref_avoids_mutable_roots(func, p.local)
                } else {
                    borrows_a_retagged_ref_local(func, p.local)
                }
        }
        _ => false,
    }
}

/// A `&&U` argument `r` that grants no write (CALL-HAVOC-ESCAPE-2): `r`'s one value is
/// a shared borrow `&l` of a WHOLE local `l: &U` with `U` [`pointee_is_read_only`] that
/// is retagged where it gets its value ([`ref_local_is_retagged`]). The callee can write
/// neither `l`'s slot (`Freeze` bytes behind a shared reference) nor `*l` (`l`'s own
/// tag is a fresh `SharedReadOnly`/`Frozen` one). A `&&U` whose inner reference is
/// stored in memory (`&p.b`) or is a parameter's pointee is refused: that inner value
/// was never retagged and may carry raw-pointer bits with write permission. This is the
/// `PartialEq::eq` receiver of a slice comparison (`&self.b[a..b] == w` in P1).
fn borrows_a_retagged_ref_local(func: &VerifiableFunction, r: usize) -> bool {
    if crate::local_defs::is_parameter(func, r) {
        return false;
    }
    let Some(Rvalue::Ref { mutable: false, place }) = crate::local_defs::unique_value_def(func, r)
    else {
        return false;
    };
    place.projections.is_empty()
        && matches!(
            crate::local_ty_ref(func, place.local),
            Some(Ty::Ref { mutable: false, inner }) if pointee_is_read_only(inner, 8)
        )
        && ref_local_is_retagged(func, place.local)
}

#[cfg(test)]
pub(super) fn arg_grants_no_write_for_tests(func: &VerifiableFunction, arg: &Operand) -> bool {
    arg_grants_no_write(func, arg, true)
}

/// Whether the shared-reference local `r` is a parameter, or holds ONE value
/// (`local_defs::unique_value_def`) that is a shared borrow `&q` of a place `q` reached
/// through SHARED references only: every `Deref` along `q` dereferences a
/// `&T`, never a `&mut T`, a raw pointer or a `Box`. A `Use` copy of another such local
/// is followed (bounded). Anything else — a call destination, a second value, a reborrow
/// through `*self` of a `&mut self` — answers `false`.
fn shared_ref_avoids_mutable_roots(func: &VerifiableFunction, r: usize) -> bool {
    let mut local = r;
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, local) {
            return true;
        }
        match crate::local_defs::unique_value_def(func, local) {
            Some(Rvalue::Ref { mutable: false, place }) => {
                return place_derefs_only_shared(func, place);
            }
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                local = q.local;
            }
            _ => return false,
        }
    }
    false
}

/// Every `Deref` in `place` dereferences a shared `&T` (the place's type walked from its
/// local); a place whose type cannot be walked answers `false`.
fn place_derefs_only_shared(func: &VerifiableFunction, place: &trust_types::Place) -> bool {
    let Some(mut ty) = crate::local_ty_ref(func, place.local) else { return false };
    for proj in &place.projections {
        match proj {
            trust_types::Projection::Deref => match ty {
                Ty::Ref { mutable: false, inner } => ty = inner,
                _ => return false,
            },
            trust_types::Projection::Field(i) => {
                let next = match ty {
                    Ty::Adt { fields, .. } => fields.get(*i).map(|(_, t)| t),
                    Ty::Tuple(ts) => ts.get(*i),
                    _ => None,
                };
                let Some(next) = next else { return false };
                ty = next;
            }
            _ => return false,
        }
    }
    true
}

/// [`ty_is_pure_frozen_value`], and additionally every ADT in it has at least one
/// RECORDED field (an enum's tag counts): a struct the extractor recorded no fields for
/// may hide an `UnsafeCell` or a pointer (the TRUST-10 row's refusal of a field-less
/// struct, kept here). A unit struct or `PhantomData` is refused too: precision only.
fn ty_is_recorded_pure_frozen_value(ty: &Ty) -> bool {
    ty_is_pure_frozen_value_with(ty, true)
}

/// The pointee of a shared reference grants no write when it is a
/// [`ty_is_recorded_pure_frozen_value`], a slice of one, or `str`: no reference, raw
/// pointer or interior mutability anywhere in it.
///
/// Trust (CALL-HAVOC-ESCAPE-2, 2026-10-06): ONE level only. A shared reference to a
/// SHARED reference (`&&[u8]`, the receiver of `PartialEq::eq` on slices) used to pass:
/// the inner reference is stored in memory, is never retagged, and can carry raw-pointer
/// bits with write permission, so `peek(&p.b)` could write `*p.b` through it.
fn pointee_is_read_only(ty: &Ty, fuel: u32) -> bool {
    if fuel == 0 {
        return false;
    }
    match ty {
        Ty::Str => true,
        Ty::Slice { elem } => ty_is_recorded_pure_frozen_value(elem),
        _ => ty_is_recorded_pure_frozen_value(ty),
    }
}

/// Whether an ADT's NAME is an `UnsafeCell` or a std wrapper built on one (`Cell`,
/// `RefCell`, `OnceCell`, `Mutex`, `RwLock`, `Atomic*`, ...): refused by name as well
/// as by field walk, so a wrapper rendered without its private fields cannot pass.
///
/// Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1) — THE ONE interior-mutability NAME list.
/// `guards::ty_is_interior_mut_wrapper`, `sep_engine`'s cell refusal and
/// `callee_write_set`'s frozen-struct descent each carried a list of their own (ten exact
/// tails; `contains("Cell")` without `Condvar`/`Once`; `contains("UnsafeCell")`); they ask
/// this one now. It is a LOOSE test and may only REFUSE (a user type merely named like a
/// cell is treated as one): every grant comes from [`ty_may_hold_inline_unsafe_cell`]'s
/// structural walk finding no `UnsafeCell`, never from a name failing to match.
pub(crate) use trust_types::interior_mutability::type_name_is_interior_mutable;

/// Is `ty` a pure pointer-free value that is also `Freeze` — a finite tree of
/// scalars, tuples, arrays, and structs/enums the extractor stamped with their real
/// kind, with NO pointer of any kind (`&`, `&mut`, raw, `Box`, fn pointer, `dyn`),
/// NO union, and NO interior-mutability cell anywhere inline?
///
/// Trust (ENC-DEFECTS 13b, 2026-09-26). This is `Freeze` re-derived STRUCTURALLY
/// and made stricter by refusing every pointer: the bytes of such a value are the
/// whole of what a `&T` to it lets a callee reach, so the protected-shared-borrow
/// argument in [`frozen_shared_reborrow_roots`] covers everything the argument can
/// touch. Fail-closed on every shape it does not classify:
///  * `Ty::Adt` with `adt_kind: None` (hand-built / pre-W19) or `Some(Union)`;
///  * an ADT whose name tail is `UnsafeCell`/`SyncUnsafeCell` or any std wrapper
///    built on one (`Cell`, `RefCell`, `OnceCell`, `Mutex`, `RwLock`, `Atomic*`,
///    ...) — refused by NAME as well as by field walk, so a wrapper the extractor
///    rendered without its private fields cannot pass as an empty struct;
///  * a by-name `Ty::Datatype` marker (a compacted oversized field) — its structure
///    is not in hand;
///  * a nesting deeper than the fuel.
pub(crate) fn ty_is_pure_frozen_value(ty: &Ty) -> bool {
    ty_is_pure_frozen_value_with(ty, false)
}

fn ty_is_pure_frozen_value_with(ty: &Ty, require_recorded_fields: bool) -> bool {
    fn interior_mutable_name(name: &str) -> bool {
        type_name_is_interior_mutable(name)
    }
    fn walk(ty: &Ty, require_recorded_fields: bool, fuel: u32) -> bool {
        let Some(fuel) = fuel.checked_sub(1) else { return false };
        match ty {
            // Trust (upstream 1.101): `!` is stable and std now spells residual
            // payloads with it (`Option<!>` for `Try` on `Option`, where 1.99
            // extracted `Option<Infallible>`). The never type is `Freeze`,
            // holds no pointer and has no inhabitants, so a field of that type
            // carries no write channel — admitting it restores the dest-only
            // havoc arm at `from_residual` calls (measured: TINV P1's `bump`
            // lost its frame there and `i <= len(b)` stopped certifying).
            Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Unit | Ty::Never => true,
            Ty::Tuple(elems) => elems.iter().all(|t| walk(t, require_recorded_fields, fuel)),
            Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
                walk(elem, require_recorded_fields, fuel)
            }
            Ty::Adt {
                name,
                fields,
                variants,
                adt_kind: Some(trust_types::AdtKind::Struct | trust_types::AdtKind::Enum),
                ..
            } => {
                (!require_recorded_fields || !fields.is_empty())
                    && !interior_mutable_name(name)
                    && fields.iter().all(|(_, t)| walk(t, require_recorded_fields, fuel))
                    && variants.iter().all(|v| {
                        v.fields.iter().all(|(_, t)| walk(t, require_recorded_fields, fuel))
                    })
            }
            _ => false,
        }
    }
    walk(ty, require_recorded_fields, 24)
}

/// Trust (ENC-DEFECTS 13b, 2026-09-26): the havoc-list ROOT names a call cannot
/// write because it receives their WHOLE pointee only as a protected shared
/// reborrow of a pure `Freeze` type — or `None` when the call is not of that
/// shape (then nothing is narrowed).
///
/// THE PREMISE (docs/TCB.md, "Shared-reborrow immutability across a call"). A
/// `&T` passed DIRECTLY as a function argument is protected for the whole call
/// (the language's own aliasing contract; Stacked Borrows and Tree Borrows both
/// enforce it with a protector), and while it is live the `Freeze` bytes of `*T`
/// are immutable: ANY write to them during the call — by the callee through the
/// reference, through a pointer it derives or finds, or through any other alias
/// — is undefined behavior. `self.remaining()` on `&mut self` therefore leaves
/// `*self` exactly as it found it, and the `&mut self` field facts the body
/// established before the call hold after it. The old havoc killed `self` (and so
/// every `self*.f`) at every such call: `if n > self.remaining() { .. }
/// self.used += n` refuted on `self*.0#e_s2_t = u32::MAX`.
///
/// Every argument must be one of:
///  * a pure value ([`arg_is_pure_value`]) — hands the callee no pointer; or
///  * a `Copy`/`Move` of a whole local `r: &T` (SHARED) whose one value is
///    `&(*root)` — a reborrow of `root`'s ENTIRE pointee, nothing more, nothing
///    less (a field reborrow protects only that field and is not narrowed here),
///    where `T` is [`ty_is_pure_frozen_value`] and `root` is a reference.
///
/// and, for each such `root`, all of:
///  * `root` holds ONE value in the body (`local_defs::holds_one_value`), so
///    `*root` names one referent throughout;
///  * `root`'s pointee never escapes by any channel this narrowing could miss —
///    no `&mut`/`&raw` borrow of any place rooted at `root` (a stashed `&mut` or
///    raw child could be written through between calls), no copy/move/borrow of
///    the `root` SLOT itself, and no cast of it ([`local_pointee_may_escape`]);
///  * the body has no pointer-laundering site ([`func_has_pointer_laundering`]).
///
/// The returned names are each `root`'s base name exactly as the havoc list
/// spells it. Any argument outside the two forms — a `&mut`, a raw pointer, a
/// pointer-carrying aggregate, a shared reference to anything impure or
/// non-`Freeze`, a projected reborrow — returns `None`.
pub(super) fn frozen_shared_reborrow_roots(
    func: &VerifiableFunction,
    args: &[Operand],
) -> Option<trust_types::fx::FxHashSet<String>> {
    if args.is_empty() {
        return None;
    }
    let mut checked_laundering = false;
    let mut roots = trust_types::fx::FxHashSet::default();
    for arg in args {
        if arg_is_pure_value(func, arg) {
            continue;
        }
        let (Operand::Copy(r) | Operand::Move(r)) = arg else { return None };
        if !r.projections.is_empty() || crate::local_defs::is_parameter(func, r.local) {
            return None;
        }
        let r_ty = crate::local_ty_ref(func, r.local)?;
        let Ty::Ref { mutable: false, inner } = r_ty else { return None };
        if !ty_is_pure_frozen_value(inner) {
            return None;
        }
        let Rvalue::Ref { mutable: false, place } =
            crate::local_defs::unique_value_def(func, r.local)?
        else {
            return None;
        };
        if !matches!(place.projections.as_slice(), [trust_types::Projection::Deref]) {
            return None;
        }
        let root = place.local;
        let Some(Ty::Ref { inner: root_inner, .. }) = crate::local_ty_ref(func, root) else {
            return None;
        };
        if root_inner.as_ref() != inner.as_ref()
            || !crate::local_defs::holds_one_value(func, root)
        {
            return None;
        }
        if !checked_laundering {
            if func_has_pointer_laundering(func) {
                return None;
            }
            checked_laundering = true;
        }
        if local_pointee_may_escape(func, root) {
            return None;
        }
        roots.insert(place_to_var_name(func, &trust_types::Place::local(root)));
    }
    (!roots.is_empty()).then_some(roots)
}

/// Can the reference local `root`, or anything derived from it, escape past the
/// shared-reborrow narrowing? True on ANY of:
///  * a `&mut` or `&raw` (const or mut) borrow of a place rooted at `root` — a
///    mutable or raw CHILD of the pointee that a callee could stash and write
///    through between calls;
///  * a borrow of the `root` SLOT itself (`&root`, `&mut root`);
///  * a whole-value copy/move of `root` into anything (another local, an
///    aggregate, a cast, a call or tail-call argument) — the pointer then lives
///    on under a name this analysis does not follow;
///  * a `Drop` of a place rooted at `root` — drop glue is user code handed a
///    `&mut` to that place, the same channel as a `&mut` borrow of it;
///  * an `Unsupported` statement or rvalue, or an `Opaque` terminator, anywhere
///    (unaccountable).
///
/// Salvage reconciliation (2026-09-28): the terminator arm names every
/// `LocalWrite` channel construct (`local_defs_seam_lint`'s proper-subset ratchet
/// flagged it for omitting the tail call and drop glue); both additions only
/// widen what counts as an escape, i.e. fail closed.
///
/// Reads and shared borrows of places BELOW `(*root)` do not escape a writable
/// alias: a shared reference cannot be used to write `Freeze` bytes.
///
/// The rule is stated once, in [`for_each_pointee_escape`], which also names WHERE
/// each escape happens (the flow-sensitive half of [`escape_havoc_at`]); this is
/// "is there any".
pub(crate) fn local_pointee_may_escape(func: &VerifiableFunction, root: usize) -> bool {
    let mut found = false;
    let walk = for_each_pointee_escape(func, root, &mut |_| {
        found = true;
        std::ops::ControlFlow::Break(())
    });
    found || matches!(walk, PointeeEscapeWalk::Unaccountable)
}

/// One place where [`local_pointee_may_escape`]'s rule fires: the POSITION of the block
/// in `func.body.blocks` and whether it is the block's terminator (`false`: one of its
/// statements, which all run before the terminator).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PointeeEscapeSite {
    pub(crate) block_pos: usize,
    pub(crate) at_terminator: bool,
}

/// How [`for_each_pointee_escape`] ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PointeeEscapeWalk {
    /// Every statement and terminator was classified and every escape site reported.
    Complete,
    /// The visitor broke off.
    Stopped,
    /// An `Unsupported` (or unclassified) statement or rvalue, or an `Opaque`
    /// terminator: nothing about `root` can be said, anywhere.
    Unaccountable,
}

/// [`local_pointee_may_escape`]'s rule, reporting each escape SITE to `visit` in body
/// order. See there for what counts as an escape.
pub(crate) fn for_each_pointee_escape(
    func: &VerifiableFunction,
    root: usize,
    visit: &mut dyn FnMut(PointeeEscapeSite) -> std::ops::ControlFlow<()>,
) -> PointeeEscapeWalk {
    fn op_is_root_value(op: &Operand, root: usize) -> bool {
        matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == root && p.projections.is_empty())
    }
    let mut site = |block_pos: usize, at_terminator: bool| -> bool {
        visit(PointeeEscapeSite { block_pos, at_terminator }).is_break()
    };
    for (block_pos, block) in func.body.blocks.iter().enumerate() {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { rvalue, .. } => {
                    let escapes = match rvalue {
                        Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place) => {
                            place.local == root
                        }
                        Rvalue::Ref { mutable: false, place } => {
                            place.local == root && place.projections.is_empty()
                        }
                        Rvalue::Use(op) | Rvalue::Cast(op, _) | Rvalue::UnaryOp(_, op) => {
                            op_is_root_value(op, root)
                        }
                        Rvalue::Repeat(op, _) => op_is_root_value(op, root),
                        Rvalue::BinaryOp(_, a, b)
                        | Rvalue::CheckedBinaryOp(_, a, b)
                        | Rvalue::UncheckedBinaryOp(_, a, b) => {
                            op_is_root_value(a, root) || op_is_root_value(b, root)
                        }
                        Rvalue::Aggregate(_, ops) => ops.iter().any(|o| op_is_root_value(o, root)),
                        Rvalue::CopyForDeref(p) => p.local == root && p.projections.is_empty(),
                        Rvalue::PtrOffset { ptr, count } => {
                            op_is_root_value(ptr, root) || op_is_root_value(count, root)
                        }
                        Rvalue::Discriminant(_) | Rvalue::Len(_) => false,
                        // Unmodeled semantics (and any variant added later):
                        // unaccountable, whatever it mentions.
                        _ => return PointeeEscapeWalk::Unaccountable,
                    };
                    if escapes && site(block_pos, false) {
                        return PointeeEscapeWalk::Stopped;
                    }
                }
                Statement::Intrinsic { args, .. } => {
                    if args.iter().any(|a| op_is_root_value(a, root)) && site(block_pos, false) {
                        return PointeeEscapeWalk::Stopped;
                    }
                }
                Statement::CopyNonOverlapping { src, dst, count, .. } => {
                    if [src, dst, count].into_iter().any(|a| op_is_root_value(a, root))
                        && site(block_pos, false)
                    {
                        return PointeeEscapeWalk::Stopped;
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. } => {}
                // `Unsupported` and any statement kind added later.
                _ => return PointeeEscapeWalk::Unaccountable,
            }
        }
        match &block.terminator {
            // A tail call hands its arguments on exactly like a call.
            Terminator::Call { args, .. } | Terminator::TailCall { args, .. } => {
                if args.iter().any(|a| op_is_root_value(a, root)) && site(block_pos, true) {
                    return PointeeEscapeWalk::Stopped;
                }
            }
            // Drop glue receives `&mut` to the dropped place: a place rooted at
            // `root` is a mutable CHILD of the pointee handed to user code.
            Terminator::Drop { place, .. } => {
                if place.local == root && site(block_pos, true) {
                    return PointeeEscapeWalk::Stopped;
                }
            }
            Terminator::Opaque { .. } => return PointeeEscapeWalk::Unaccountable,
            _ => {}
        }
    }
    PointeeEscapeWalk::Complete
}

/// True iff the function contains ANY raw-pointer laundering site — an
/// `AddressOf` (`&raw`), a cast whose TARGET is a raw pointer, or an
/// `Unsupported` rvalue (unknown provenance). Such a site can smuggle a local's
/// address through a "pure scalar" (`&mut x as *mut u32 as usize`) into an
/// earlier callee's storage, from which a LATER no-pointer-arg callee could
/// write the local — so the per-argument havoc skip must fail closed for the
/// WHOLE function whenever one exists. (The raw write itself is also
/// independently fail-closed at the callee, but this gate keeps the skip sound
/// without relying on that separate lane.)
pub(super) fn func_has_pointer_laundering(func: &VerifiableFunction) -> bool {
    // Asked once per call terminator whose arguments are pure values: a whole-body
    // walk per call was quadratic in the body, so it is computed once per function.
    crate::fn_memo::pointer_laundering(func, || super::func_has_pointer_laundering_for(func))
}

pub(super) fn func_has_writable_pointer_laundering_uncached(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| match s {
            Statement::Assign { rvalue: Rvalue::AddressOf(false, place), .. } => {
                !addr_of_is_read_only(func, place)
            }
            Statement::Assign { rvalue: Rvalue::AddressOf(..), .. }
            | Statement::Assign { rvalue: Rvalue::Cast(_, Ty::RawPtr { .. }), .. }
            | Statement::Assign { rvalue: Rvalue::Unsupported { .. }, .. } => true,
            _ => false,
        })
    })
}

/// [`func_has_pointer_laundering`] minus the `&raw const` sites that can carry no WRITE
/// permission ([`addr_of_is_read_only`]): the gate of the dest-only call arm of
/// [`terminator_def_names_structured`] ONLY. The TRUST-10 / 13b refinements and the
/// callee write-set derivation keep the full gate.
///
/// Trust (P1 precision, 2026-10-06). Every slice index `b[i]` lowers to
/// `_p = &raw const (*_r); _n = PtrMetadata(move _p)` for its bounds check, so the full
/// gate closed the dest-only arm in every body that indexes a slice, and a `&mut self`
/// over P1's `Parser` lost `self.i < self.b.len()` at a nullary call before
/// `self.b[self.i]`. A `*const` taken as `&raw const (*r)` (or a struct/tuple field
/// below it) through a shared-reference LOCAL `r` to `Freeze` data gets no tag of its
/// own: it carries `r`'s tag. Two cases:
///  * `r` is retagged where it got its value ([`ref_local_is_retagged`]: a pinned
///    parameter, a borrow, a call return): the tag is `SharedReadOnly` (Stacked Borrows)
///    / `Frozen` over the `Freeze` pointee (Tree Borrows), so a write through the
///    pointer, or through one a callee rebuilds from its address, is UB (R1);
///  * `r` is NOT retagged — a deref temp `_t = copy (*p).0` (AddRetag skips deref
///    temps), whose value is a reference loaded from memory that may carry raw-pointer
///    bits with write permission; the slice-index prelude's `FakeForPtrMetadata` raw
///    pointer is the same. The pointer can then write only what that stored reference
///    reaches, and every name for those bytes is either behind a reference loaded from
///    memory (`_t*`, `p*.0*`: havocked at every call, [`stored_ref_pointee_names`]),
///    behind a retagged reference (a foreign write makes its later use UB), or a local
///    of this body, whose address can be in such bits only through a `&mut`/`&raw`
///    borrow this body takes (on the havoc list, or this gate) or a shared borrow (no
///    write permission; an interior-mutable local is the list's pre-existing residual).
/// So it launders no write channel that leaves a kept fact stale. The raw local itself
/// still carries a pointer and stays on the whole-function havoc list. (The admission was
/// NOT restricted to retagged `r`: the slice-index prelude is through a deref temp, and
/// the restriction loses `self.b[self.i]` after a call; CALL-HAVOC-ESCAPE-2.)
pub(super) fn func_has_writable_pointer_laundering(func: &VerifiableFunction) -> bool {
    if !func_has_pointer_laundering(func) {
        return false;
    }
    crate::fn_memo::writable_pointer_laundering(func, || {
        super::func_has_writable_pointer_laundering_for(func)
    })
}

/// A `&raw const place` that launders no write channel a kept fact depends on (see
/// [`func_has_writable_pointer_laundering`]): `place` is `(*r)` or `(*r).f.g..` for a
/// LOCAL `r` of SHARED reference type (exactly one `Deref`, first; then only
/// struct/tuple `Field`s), the WHOLE target `*r` is [`pointee_is_read_only`]
/// (pointer-free `Freeze` data, a slice of it or `str`: no `UnsafeCell` anywhere in it,
/// no union), and so is the addressed type. A `&raw const x` of a local is refused (it
/// carries the local's own write permission), as is a deref of a `&mut`, a raw pointer,
/// a `Box` or a reference stored in memory.
fn addr_of_is_read_only(func: &VerifiableFunction, place: &trust_types::Place) -> bool {
    // Exactly ONE `Deref`, first: through the LOCAL itself (a second `Deref` is of a
    // reference stored in memory and is refused outright). See
    // [`func_has_writable_pointer_laundering`] for why that is enough whether or not the
    // local was retagged.
    if !matches!(place.projections.first(), Some(trust_types::Projection::Deref))
        || place.projections[1..].iter().any(|p| matches!(p, trust_types::Projection::Deref))
    {
        return false;
    }
    let Some(mut ty) = crate::local_ty_ref(func, place.local) else { return false };
    for proj in &place.projections {
        match proj {
            // Every Deref target AS A WHOLE must be read-only: under Tree Borrows a raw
            // pointer gets no tag of its own and keeps the reference's tag, which is
            // `Frozen` only over the `Freeze` bytes of the WHOLE pointee — a `Cell`
            // sibling or a union around the addressed field stays writable through it.
            trust_types::Projection::Deref => match ty {
                Ty::Ref { mutable: false, inner } if pointee_is_read_only(inner, 8) => ty = inner,
                _ => return false,
            },
            // Inside a read-only target every field is read-only too; a field of
            // anything but a stamped struct or a tuple is refused all the same.
            trust_types::Projection::Field(i) => {
                let next = match ty {
                    Ty::Adt { fields, adt_kind: Some(trust_types::AdtKind::Struct), .. } => {
                        fields.get(*i).map(|(_, t)| t)
                    }
                    Ty::Tuple(ts) => ts.get(*i),
                    _ => None,
                };
                let Some(next) = next else { return false };
                ty = next;
            }
            _ => return false,
        }
    }
    pointee_is_read_only(ty, 8)
}

/// Trust: 2026-10-08 (RAW-CONST-STORE, H2 of the ploss adversarial pass, FALSE PROOF) —
/// THE write-channel question for a borrow: the place `rvalue` hands WRITE permission
/// to, if it hands out any.
///
/// `&mut P` and `&raw mut P` do. So does `&raw const P`: a raw pointer carries the
/// permission of the place it is taken from (Tree Borrows gives it no tag of its own),
/// and `p as *mut T` (or `p.cast_mut()`, or a callee handed `p`) writes `P` through it
/// in a defined execution. The crate's other answers to this question already say so —
/// `trust_types::PlaceWriteChannel::RawBorrow` ("a raw pointer may write it either
/// way"), `Statement::escapes_local`, `guards::value_local_is_unstable`, the referent
/// fold's `AliasKind::WriteCapable`, and [`func_has_writable_pointer_laundering`]. The
/// one `&raw const` that hands out NO write permission is [`addr_of_is_read_only`]'s:
/// through a shared reference local to pointer-free `Freeze` data (a write is UB).
///
/// The write-channel scans that matched `&mut` / `&raw mut` only missed it: `let p =
/// &raw const k; *(p as *mut usize) = k0 + 4; t[k]` — the store through the cast is
/// opaque, the deref-store havoc list ([`mutably_borrowed_local_names`]) had no `k`, so
/// `k`'s pre-store definition stayed live and `t[k]` was kernel-certified at -O0 and
/// PROVED at -O1 while every input panics (`fd08`, `ce06`, `fd05`, `h2c`..`h2i` in
/// `tests/ploss_adv_false_proofs_realmir.rs`). Every scan that asks "can a borrow write
/// this place" asks it here (or [`own_storage_write_borrow`]).
///
/// The two models. A `&raw const` pointer cast to `*mut` and written through is
/// accepted by Tree Borrows and rejected by Stacked Borrows (which makes it read-only);
/// Trust assumes about aliasing only what BOTH models validate, so it is a channel. For
/// the write to be defined the memory must also be mutable — the Rust Reference makes
/// mutating bytes owned by an IMMUTABLE binding UB — but binding mutability does not
/// reach `trust_types`, so `let s` and `let mut s` are both counted (sound for both).
/// `let mut s: &[u8] = a; let p = &raw const s as *mut &[u8]; unsafe { *p = b }`
/// RESEATS `s`, and a later `s[i]` panics for `i >= b.len()`. A scan of what a local
/// POINTS TO (a parameter's entry-stable field `(*self).x`, a backing field behind
/// `&mut self`, an element read through a reference) asks this rule; a scan of a
/// local's OWN value asks [`own_storage_write_borrow`].
///
/// The same rule was also found and fixed on the r8c soundness-union lane (2026-09-30,
/// `pointer_write_channel` / `slot_write_channel` there); the lanes were merged into
/// these two functions on 2026-10-08. The match is spelled in its wide form
/// (`AddressOf(_, ..)`), which `tests/write_channel_rule_is_not_restated.rs` accepts.
pub(crate) fn borrow_write_target<'a>(
    func: &VerifiableFunction,
    rvalue: &'a Rvalue,
) -> Option<&'a trust_types::Place> {
    match rvalue {
        Rvalue::AddressOf(false, place) if addr_of_is_read_only(func, place) => None,
        Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place) => Some(place),
        _ => None,
    }
}

/// [`borrow_write_target`] for the scans whose question is about a place's OWN storage
/// — a local, a field or an element of one: a `&raw const` counts only when its place has
/// no `Deref` (`&raw const k`, `&raw const s.f`, `&raw const a[i]`). (`&mut` / `&raw mut`
/// count whatever they borrow, as they always did.)
///
/// A `&raw const` of a place BEHIND a pointer (`&raw const (*s)` — every slice index's
/// bounds prelude takes one) writes only the POINTEE, which the pointer's own channel
/// already covers: a `&mut` / raw / `Box` local is on [`mutable_pointer_local_names`] (its
/// base name kills every `p*…` by prefix), a reference loaded from memory is on
/// [`stored_ref_pointee_names`], a shared reference to `Freeze` data is frozen (a write is
/// UB), and the borrow that made a FOLDED pointer (`r = &raw const k`, then `&raw const
/// (*r)`) is itself an own-storage borrow this function answers. Counting it again would
/// add the pointee's name beside its pointer's on the call-havoc list, where the per-call
/// refinements that drop a pointer's base name would leave it behind. That base-name
/// coverage is a property of the HAVOC list: a scan asking whether a POINTEE is
/// unchanged must ask [`borrow_write_target`] instead.
///
/// The opaque-store havoc judges its base names with the PLAIN relation
/// ([`KillSet::havoc`]), which is sound only because the havoc list mints every
/// own-storage channel's `__slice_len` twin ([`mutably_borrowed_havoc_names`]): before
/// `&raw const` counted here, a slice reseated through `&raw const s as *mut &[u8]`
/// kept its stale length live (kernel-certified false proofs on the straight-line,
/// call and shared-slice-loop reseats, and on a `&mut [u8]` loop reseat once the
/// fixpoint outflow kill moved to the plain relation, `aebf15b1ed`). Pinned by
/// `tests/opaque_deref_store_reseat.rs` (`a_raw_const_*`, the parameter rows) and
/// `generate/slot_write_channel_tests.rs` (the rule arm by arm, one pin per consumer).
pub(crate) fn own_storage_write_borrow<'a>(
    func: &VerifiableFunction,
    rvalue: &'a Rvalue,
) -> Option<&'a trust_types::Place> {
    match rvalue {
        Rvalue::AddressOf(false, place)
            if place.projections.iter().any(|p| matches!(p, Projection::Deref)) =>
        {
            None
        }
        _ => borrow_write_target(func, rvalue),
    }
}

pub(super) fn func_has_pointer_laundering_uncached(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| {
            matches!(
                s,
                Statement::Assign { rvalue: Rvalue::AddressOf(..), .. }
                    | Statement::Assign { rvalue: Rvalue::Cast(_, Ty::RawPtr { .. }), .. }
                    | Statement::Assign { rvalue: Rvalue::Unsupported { .. }, .. }
            )
        })
    })
}

/// The flow-INSENSITIVE form of [`escape_havoc_at`]: rule (b) exempting only a parameter
/// with no escape site anywhere ([`protected_private_mut_param`]), the arm's rule from
/// TINV-18 until ESCAPE-HAVOC-FLOW-1. Kept for the unit tests that pin it; every call
/// site asks [`escape_havoc_at`].
#[cfg(test)]
pub(super) fn escape_havoc(func: &VerifiableFunction) -> TermHavoc {
    let exempt: Vec<usize> = (0..func.body.locals.len())
        .filter(|&local| protected_private_mut_param(func, local))
        .collect();
    escape_term_havoc(crate::fn_memo::escape_havoc_exempting(func, &exempt, || {
        escape_havoc_exempting(func, &exempt)
    }))
}

/// The [`TermHavoc`] of an escape-arm split: `None` when nothing is kept, `Function`
/// when nothing is dropped.
fn escape_term_havoc(e: std::rc::Rc<EscapeHavoc>) -> TermHavoc {
    if e.kept.is_empty() {
        TermHavoc::None
    } else if e.dropped.is_empty() {
        TermHavoc::Function
    } else {
        TermHavoc::Escape(e)
    }
}

/// The havoc of a call whose arguments hand the callee no write channel (the dest-only
/// arm of [`terminator_def_names_structured`]): the whole-function list
/// [`function_havoc_names`] minus the names rooted at a parameter rule (b) exempts AT
/// THIS CALL — `None` when nothing is left, `Function` when nothing is dropped. The
/// exempt sets are computed once per function ([`ParamEscapeReach`]), and every call
/// with the same set shares one split.
///
/// Trust (TINV-18 correction, 2026-10-06; coarse rule after the second review). A
/// callee that receives no pointer into caller memory can still write caller memory it
/// reaches WITHOUT an argument: through a raw pointer the caller also holds (a callee
/// returned `&raw mut G`, a later one writes `G`), through a `&mut` held in memory
/// whose creator stashed a raw child of it, and through a raw child of any `&mut` a
/// callee received EARLIER in the body (parked in a global inside a safe-signatured
/// callee's `unsafe`). A fine-grained exposure analysis of those channels was tried and
/// three review rounds each found a channel it missed (a pointer stored THROUGH a `&mut`
/// to another local, a `&mut T` parameter with `T: !Unpin`, a fail-open walk over
/// by-name `Datatype` markers). So the rule is now coarse, and these are the ONLY roots
/// the arm exempts:
///
///  (a) A stack local that is never the place or projection root of a mutable or raw
///      borrow and whose type holds no pointer. NO CODE: such a local contributes no
///      name to the whole-function list at all (that list is the `&mut`/`&raw mut`
///      borrow targets plus the pointer-carrying locals), so it was never havocked by
///      any call. Its address exists only inside its own direct place uses, so no
///      callee can name its memory. (A SHARED borrow of an interior-mutable local is a
///      write channel to its `UnsafeCell` bytes; since 2026-10-14 those bytes are named
///      at every call, this arm's included, by [`stored_ref_pointee_names`]'
///      INTERIOR-MUT-CHANNEL-1 half, [`shared_borrowed_cell_places`].)
///  (b) A `&mut T` PARAMETER, [`protected_mut_param_shape`]: `T` is `Freeze`, fully
///      recorded, structurally `Unpin` and holds no pointer except SHARED references
///      to pointer-free `Freeze` data ([`ty_is_protected_plain_pointee`]; P1 precision,
///      2026-10-06), never reseated, and whose pointer has not left the body on any
///      path to this call: no escape site of [`local_pointee_may_escape`]'s rule (a
///      copy or move of it, a `&mut`/`&raw` reborrow of anything under it, a borrow of
///      the slot itself, a `Drop` under it) reaches the call (until ESCAPE-HAVOC-FLOW-1,
///      2026-10-15, none anywhere in the body; see below). Such a parameter
///      is retagged with a PROTECTOR on function entry that lasts for the whole call
///      (Stacked Borrows and Tree Borrows alike; `noalias` in codegen), so while this
///      body runs any write to `*param` through a pointer not derived from `param` is
///      undefined behaviour. The only pointers derived from it are this body's own
///      places and shared reborrows of `Freeze` bytes (through which a write is UB);
///      none can reach the callee except as an argument, which the arm's argument rules
///      exclude. The names kept are those of `*param`'s own bytes (protected,
///      including a shared-reference field's address and length); the names BEHIND
///      such a field (`param*.f*`) are havocked at every call, like every name behind
///      a reference loaded from memory ([`stored_ref_pointee_names`]; why on
///      [`ty_is_protected_plain_pointee`]).
///
/// Every other root is havocked exactly as the full call arm havocs it (the
/// whole-function list, unrefined). The in-body derivation of a raw pointer
/// ([`func_has_pointer_laundering`]), a non-pointer-free constant argument
/// ([`const_is_pure_value`]) and a foreign / `unsafe`-signature / atomic callee still
/// close the whole arm at the call site.
///
/// Trust: 2026-10-15 (TRUST-KI-1015-1, the aterm-digest top-up; ESCAPE-HAVOC-FLOW-1). Rule
/// (b)'s "never leaves the body" is the flow-INSENSITIVE form of the question its premise
/// asks, which is about the call: "can anyone but this body's own places hold a pointer
/// derived from `param` WHILE THE CALL RUNS?". A pointer derived from `param` exists only
/// after an escape site of [`local_pointee_may_escape`]'s rule has executed in THIS
/// invocation of the body: the parameter is retagged with a protector on entry, so no
/// pointer created before the call to the body, and none created by another invocation,
/// may write `*param` while it runs (the same premise as rule (b), docs/TCB.md). So at a
/// call that no escape site of `param` can reach — on no CFG path from the entry to the
/// call, unwind edges included, does an escape site run first — the call's argument rules
/// leave the callee exactly rule (b)'s position: no pointer it may write through reaches
/// `*param`. `usize::min(64 - self.buf_len, data.len())` before the body's first
/// `&mut self.buf` is that call: the two reads of `self.buf_len` around it name one value.
///
/// A parameter whose escape sites reach the call (an earlier call parked a raw child of a
/// reborrow, or one round of a loop parks it before the next round's call:
/// `tests/digest_update_topup_realmir.rs`, `top_up_stashed` and `mark_rounds_stashed`) is
/// havocked exactly as before, and so is every parameter at a call whose block this
/// cannot place (repeated block ids, an unknown successor, a block not in
/// `func.body.blocks`): it falls back to the flow-insensitive rule. The argument rules,
/// the laundering gate and the foreign / `unsafe`-signature / atomic fences of the arm
/// are unchanged.
///
/// The premise's boundary is pinned in the same test file. The `premise_*` programs panic
/// in a debug build only through a pointer that ANOTHER invocation created: an earlier
/// call, the outer frame of a recursion, or the caller before the entry. That pointer
/// writes `*self` while this invocation's protected `self` is live, so the execution is UB,
/// and a release build folds the reload and does not panic. Their rows are PROVED by the
/// premise. On main, the pre-entry row already was (KNOWN_HAZARDS TRUST-KI-1015-1). The
/// `reach_*` programs are defined executions whose escape reaches the call through a join,
/// a loop's `break`, an inner loop, a recursive call's reborrow, or a sibling field. Their
/// rows stay FAILED.
pub(super) fn escape_havoc_at(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> TermHavoc {
    let reach = crate::fn_memo::param_escape_reach(func, || param_escape_reach_uncached(func));
    if reach.params.is_empty() {
        return if function_havoc_names(func).is_empty() {
            TermHavoc::None
        } else {
            TermHavoc::Function
        };
    }
    let pos = reach.position_of(func, block);
    let exempt: Vec<usize> = reach
        .params
        .iter()
        .filter(|p| match (&p.reached, pos) {
            (None, _) => false,
            (Some(_), _) if !p.has_sites => true,
            (Some(reached), Some(pos)) => !reached.get(pos).copied().unwrap_or(true),
            (Some(_), None) => false,
        })
        .map(|p| p.local)
        .collect();
    if exempt.is_empty() {
        return if function_havoc_names(func).is_empty() {
            TermHavoc::None
        } else {
            TermHavoc::Function
        };
    }
    let e = crate::fn_memo::escape_havoc_exempting(func, &exempt, || {
        escape_havoc_exempting(func, &exempt)
    });
    escape_term_havoc(e)
}

/// One parameter of [`ParamEscapeReach`].
#[derive(Debug)]
pub(crate) struct ParamReach {
    pub(crate) local: usize,
    /// Whether [`for_each_pointee_escape`] reported any site.
    pub(crate) has_sites: bool,
    /// Per block POSITION: does an escape site of `local` run before that block's
    /// terminator on some path from the entry? `None`: the walk was unaccountable
    /// (or the CFG could not be indexed and there are sites); exempt nowhere.
    pub(crate) reached: Option<Vec<bool>>,
}

/// [`escape_havoc_at`]'s per-function table: every parameter with rule (b)'s SHAPE
/// ([`protected_mut_param_shape`]) and where its escape sites reach.
#[derive(Debug)]
pub(crate) struct ParamEscapeReach {
    /// Block id -> position; `None` when ids repeat or a terminator's successors are
    /// not known (the flow-insensitive fallback).
    positions: Option<FxHashMap<trust_types::BlockId, usize>>,
    pub(crate) params: Vec<ParamReach>,
}

impl ParamEscapeReach {
    /// The position of `block` in `func.body.blocks`: by id, and only when it is that
    /// very block (a copy of a block is not placed).
    fn position_of(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
    ) -> Option<usize> {
        let pos = *self.positions.as_ref()?.get(&block.id)?;
        std::ptr::eq(func.body.blocks.get(pos)?, block).then_some(pos)
    }
}

/// Every successor of `term`, the cleanup block of an unwind edge included; `None` for
/// a terminator kind this does not know or an unmapped target block id.
fn push_terminator_successors_with_cleanup(
    term: &Terminator,
    positions: &FxHashMap<trust_types::BlockId, usize>,
    out: &mut Vec<usize>,
) -> Option<()> {
    let cleanup = |u: &trust_types::UnwindEdge| u.cleanup_target();
    match term {
        Terminator::Goto(target) => out.push(*positions.get(target)?),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            out.reserve(targets.len() + 1);
            for (_, b) in targets {
                out.push(*positions.get(b)?);
            }
            out.push(*positions.get(otherwise)?);
        }
        Terminator::Call { target, unwind, .. } => {
            if let Some(t) = target {
                out.push(*positions.get(t)?);
            }
            if let Some(c) = cleanup(unwind) {
                out.push(*positions.get(&c)?);
            }
        }
        Terminator::Assert { target, unwind, .. } | Terminator::Drop { target, unwind, .. } => {
            out.push(*positions.get(target)?);
            if let Some(c) = cleanup(unwind) {
                out.push(*positions.get(&c)?);
            }
        }
        Terminator::Opaque { targets, .. } => {
            out.reserve(targets.len());
            for b in targets {
                out.push(*positions.get(b)?);
            }
        }
        Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | Terminator::Resume => {}
        _ => return None,
    }
    Some(())
}

fn param_escape_reach_uncached(func: &VerifiableFunction) -> ParamEscapeReach {
    let protected_params: Vec<usize> = (0..func.body.locals.len())
        .filter(|&local| protected_mut_param_shape(func, local))
        .collect();
    if protected_params.is_empty() {
        return ParamEscapeReach { positions: None, params: Vec::new() };
    }
    let blocks = &func.body.blocks;
    // The CFG by position, or `None` (flow-insensitive fallback), with the blocks the
    // entry (`bb0`) reaches.
    type Graph = (FxHashMap<trust_types::BlockId, usize>, Vec<Vec<usize>>, Vec<bool>);
    let graph: Option<Graph> = (|| {
        let mut positions: FxHashMap<trust_types::BlockId, usize> =
            FxHashMap::with_capacity_and_hasher(blocks.len(), Default::default());
        for (pos, b) in blocks.iter().enumerate() {
            if positions.insert(b.id, pos).is_some() {
                return None;
            }
        }
        let mut succ = Vec::with_capacity(blocks.len());
        for b in blocks {
            let mut out = Vec::new();
            push_terminator_successors_with_cleanup(&b.terminator, &positions, &mut out)?;
            succ.push(out);
        }
        let mut from_entry = vec![false; blocks.len()];
        let mut work = vec![*positions.get(&trust_types::BlockId(0))?];
        while let Some(b) = work.pop() {
            if !from_entry[b] {
                from_entry[b] = true;
                work.extend(succ[b].iter().copied());
            }
        }
        Some((positions, succ, from_entry))
    })();
    let mut params = Vec::with_capacity(protected_params.len());
    for local in protected_params {
        let mut sites: Vec<PointeeEscapeSite> = Vec::new();
        let walk = for_each_pointee_escape(func, local, &mut |s| {
            sites.push(s);
            std::ops::ControlFlow::Continue(())
        });
        let has_sites = !sites.is_empty();
        let reached = match (walk, &graph) {
            (PointeeEscapeWalk::Complete, _) if !has_sites => Some(vec![false; blocks.len()]),
            (PointeeEscapeWalk::Complete, Some((_, succ, from_entry))) => {
                // A block the entry does not reach has a predecessor this graph does
                // not show (or none): counted as reached.
                let mut reached: Vec<bool> = from_entry.iter().map(|r| !r).collect();
                let mut work: Vec<usize> = Vec::new();
                for site in &sites {
                    // A statement runs before its block's own terminator.
                    if !site.at_terminator {
                        reached[site.block_pos] = true;
                    }
                    work.extend(succ[site.block_pos].iter().copied());
                }
                let mut seen = vec![false; blocks.len()];
                while let Some(b) = work.pop() {
                    if !seen[b] {
                        seen[b] = true;
                        reached[b] = true;
                        work.extend(succ[b].iter().copied());
                    }
                }
                Some(reached)
            }
            _ => None,
        };
        params.push(ParamReach { local, has_sites, reached });
    }
    ParamEscapeReach { positions: graph.map(|(positions, _, _)| positions), params }
}

/// The escape-arm split of the whole-function list with the names rooted at the
/// `exempt` locals dropped (rule (b)'s parameters, flow-insensitively for
/// [`escape_havoc`], at one call for [`escape_havoc_at`]).
fn escape_havoc_exempting(func: &VerifiableFunction, exempt: &[usize]) -> EscapeHavoc {
    let h = function_havoc_names(func);
    if exempt.is_empty() || h.is_empty() {
        return EscapeHavoc { kept: h.as_ref().clone(), dropped: Vec::new() };
    }
    let keep = |local: usize| !exempt.contains(&local);
    let mut kept_names =
        mutably_borrowed_havoc_names_from(func, mutably_borrowed_local_names_where(func, &keep));
    kept_names.extend(mutable_pointer_local_names_where(func, &keep));
    // A name some kept root also builds stays kept: only names EVERY builder of which
    // is an exempt root are dropped.
    let kept_set: FxHashSet<String> = kept_names.into_iter().collect();
    let mut kept: Vec<String> = Vec::with_capacity(h.len());
    let mut dropped: Vec<String> = Vec::new();
    for n in h.iter() {
        if kept_set.contains(n) {
            kept.push(n.clone());
        } else {
            dropped.push(n.clone());
        }
    }
    dropped.sort_unstable();
    dropped.dedup();
    EscapeHavoc { kept, dropped }
}

/// Trust (CALL-HAVOC-ESCAPE-2, 2026-10-06): the names a call (or drop glue, or an opaque
/// terminator) havocs beside its ordinary list — the memory behind every reference
/// LOADED FROM MEMORY, for every root local, parameter or not, shared or `&mut`.
///
/// A reference that is a FIELD (or element, or payload) of something is never retagged:
/// a struct field is not a function argument and is not loaded into a local, so its
/// value can carry raw-pointer bits with write permission (`ptr::write` of a
/// `*const [u8]` into `p.b`). A callee — through a static, or through a `&&[u8]` handed
/// to it — can then write the bytes behind it in a defined execution, and the next read
/// through a fresh load sees the new bytes. So every name that dereferences such a
/// reference (`p*.0*`, `p.0*`, `_t*` for a deref temp `_t = copy (*p).0`) is havocked.
///
/// KEPT: the names behind a reference LOCAL that is retagged where it gets its value
/// ([`ref_local_is_retagged`]: a pinned parameter — protected for the whole call —, a
/// single-valued local whose value is a borrow `&place`/`&mut place` or a call's return
/// value, or a copy of such a local). Its tag is a fresh `SharedReadOnly`/`Unique`
/// (Stacked Borrows) or child (Tree Borrows) for the whole pointee, so a foreign write to
/// `Freeze` bytes behind a shared one makes its later use UB (R1), and a `&mut` one is in
/// the ordinary list already. A reference INSIDE that pointee is again loaded from
/// memory: `self*.0*` for `self: &mut P { b: &[u8] }` is havocked.
///
/// Spelling: the name of the dereferenced position (`X*.f*`); a reference inside an enum
/// variant, an array, a slice, a closure or an unresolved type is covered by the name of
/// the containing place. The kill relation also rebinds every ANCESTOR of a name
/// (`X*.f`, `X*`, `X`): a sibling field and a slice length (`X*.f__slice_len`) survive.
///
/// AND THE INTERIOR-MUTABLE WRITE CHANNEL (INTERIOR-MUT-CHANNEL-1, 2026-10-14). The KEPT
/// argument above is about `Freeze` bytes: a foreign write to the `UnsafeCell` bytes
/// behind a retagged shared reference is DEFINED, and so is a write to the cell bytes of
/// an owned local through a shared borrow of it. Both are named here, at the finest
/// place [`unsafe_cell_places`] can split: the POINTEE half, the cell bytes behind every
/// retagged shared reference local (`c*` for `c: &Cell<usize>`, `a*` for
/// `a: &[Cell<usize>]`, `w*.1` for `w: &W { n, c: Cell }`), and the SLOT half, the cell
/// bytes of every local's own storage a shared borrow covers
/// ([`shared_borrowed_cell_places`]: `c` for `poke(&c)`, `st.1` for `poke_s(&st)`).
/// Until then nothing named either: on the compiler's vcgen entry, an index guarded on
/// a cell's value stayed kernel-certified PROVED across a call handed `&c`, `c` or
/// `&a[k]` for bodies that read the cell as a place (`tests/interior_mut_channel_realmir.rs`).
///
/// AND THE RETAGGED RETURN PAYLOAD (RETURN-PAYLOAD-RETAG-1, 2026-10-18). An ENUM local
/// whose one value is a call's return value (`_n = Iterator::next(..)`, an
/// `Option<&T>`) is retagged where the call returns, references inside it included
/// ([`call_return_enum_root`]). A shared reference in its payload, and a reference local
/// copied out of it (`t = copy (_n as Some).0`, the `t` of `for t in &v`), is then the
/// retagged reference the KEPT rule keeps: the enum is walked variant by variant, not
/// named whole, and `(_n as Some).0*` keeps its `Freeze` bytes across a call. A `&mut`
/// payload, an enum loaded from memory, or one with a second definition or an escaping
/// borrow of its slot is named whole as before.
///
/// AND THE FRESH CLOSURE CAPTURE (FRESH-CAPTURE-1, 2026-10-18). A closure body's capture
/// `(*_1).k: &T` is loaded from memory, so the walk above names `_1*` whole. Where the
/// COMPILER certified that every value of the closure type holds, at field `k`, the tag
/// of a fresh shared borrow made at its one construction site
/// ([`premised_capture_fields`]), that capture is exactly the retagged borrow the KEPT
/// rule keeps — its producer is `&place`, it only travelled through the closure value —
/// so `(*_1).k*` is kept: the environment is walked field by field
/// ([`premised_env_positions`]), every other capture still named as before, and a
/// reference local or borrow whose deref folds onto `(*_1).k*` is fresh too
/// ([`borrowed_place_is_unstored`]). The premise is a fact about THIS body that the
/// compiler installs for its whole generation scope, so a list memoized under it is
/// valid for every frame of the body; a frame without it (a vcgen regeneration) can
/// only compute the longer, pre-premise list.
#[inline]
fn push_unique_pointee_name(
    out: &mut Vec<String>,
    seen: &mut FxHashSet<String>,
    name: String,
) {
    if seen.insert(name.clone()) {
        out.push(name);
    }
}

pub(crate) fn stored_ref_pointee_names(func: &VerifiableFunction) -> std::rc::Rc<Vec<String>> {
    crate::fn_memo::stored_ref_pointee_names(func, || {
        let mut out: Vec<String> = Vec::new();
        let mut seen: FxHashSet<String> = FxHashSet::default();
        let skip_std: std::cell::OnceCell<bool> = std::cell::OnceCell::new();
        let premised = premised_capture_fields(func);
        let mut place = trust_types::Place::local(0);
        for (local, decl) in func.body.locals.iter().enumerate() {
            place.local = local;
            place.projections.clear();
            let fresh = matches!(decl.ty, Ty::Ref { .. })
                && (ref_local_is_retagged(func, local)
                    || ref_local_folds_to_unstored_place_with(func, local, &premised));
            if local == CLOSURE_ENV_LOCAL && !premised.is_empty() {
                premised_env_positions(func, &decl.ty, &premised, &skip_std, &mut out, &mut seen);
            } else {
                stored_ref_positions(
                    func,
                    &mut place,
                    &decl.ty,
                    fresh,
                    &skip_std,
                    &mut out,
                    &mut seen,
                    24,
                );
            }
            // THE FOLD INVARIANT. Facts about a retagged borrow `l = &place` are minted
            // under `place`'s own name when the deref folds (`referent_of_source`), so
            // `l`'s retag protects nothing about that name: a raw re-read of `place`
            // through another path is defined. A kept name must therefore root at `l*`
            // itself, at a place with no `Deref`, or at `(*r)..` — exactly one leading
            // `Deref` of a retagged reference local, no stored pointer after it. Any other borrowed place is
            // killed too (`borrowed_place_is_unstored`).
            if !crate::local_defs::is_parameter(func, local)
                && let Some(Rvalue::Ref { place, .. }) =
                    crate::local_defs::unique_value_def(func, local)
                && !borrowed_place_is_unstored_with(func, place, &premised)
            {
                let name = place_to_var_name(func, place);
                push_unique_pointee_name(&mut out, &mut seen, name);
            }
            // Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1, the SLOT half) — the
            // `UnsafeCell` bytes of this local's OWN storage that a shared borrow
            // covers (`poke(&c)` for an owned `c: Cell<usize>`, `poke_s(&st)` for
            // `st: S { n, c: Cell }` names `st.1`): whoever holds that borrow, or a
            // pointer derived from it, writes them with defined behaviour.
            for cell in shared_borrowed_cell_places(func, local).iter() {
                let name = place_to_var_name(func, cell);
                push_unique_pointee_name(&mut out, &mut seen, name);
            }
        }
        // The discriminant carrier of every killed place (and, by prefix, of every place
        // below it): `__trust_mir__discr_<place>` is a separate spelling no projection
        // relation reaches.
        let base_len = out.len();
        out.reserve(base_len);
        for i in 0..base_len {
            let c = crate::discriminant_formula_var_name(&out[i]);
            push_unique_pointee_name(&mut out, &mut seen, c);
        }
        out
    })
}

/// Whether a path names a std crate item (`core::`, `alloc::`, `std::`).
pub(crate) use trust_types::interior_mutability::type_name_is_std;

/// The std structs whose fields are PUBLIC (user code can project them): the range
/// types. Every other std struct is walked only when `skip_std` is off.
fn type_name_has_public_fields(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name).trim();
    let tail = base.rsplit("::").next().unwrap_or(base);
    base.contains("::ops::")
        && matches!(tail, "Range" | "RangeFrom" | "RangeTo" | "RangeToInclusive")
}

/// Whether any place in `func`'s body projects a FIELD of a std struct (an inlined std
/// body does). Fail-closed: an unclassified statement, rvalue or terminator answers
/// `true`, as does a place whose type walk is lost.
fn body_projects_into_std_adt(func: &VerifiableFunction) -> bool {
    fn place_hits(func: &VerifiableFunction, p: &trust_types::Place) -> bool {
        if !p.projections.iter().any(|q| matches!(q, trust_types::Projection::Field(_))) {
            return false;
        }
        let Some(mut ty) = crate::local_ty_ref(func, p.local) else { return true };
        for proj in &p.projections {
            match proj {
                trust_types::Projection::Deref => {
                    ty = match ty {
                        Ty::Ref { inner, .. } => inner,
                        Ty::RawPtr { pointee, .. } => pointee,
                        // A `Box` deref, or anything else: the type walk is lost.
                        _ => return true,
                    };
                }
                trust_types::Projection::Field(i) => {
                    let next = match ty {
                        Ty::Adt { name, fields, .. } => {
                            if type_name_is_std(name) && !type_name_has_public_fields(name) {
                                return true;
                            }
                            fields.get(*i).map(|(_, t)| t)
                        }
                        Ty::Tuple(ts) => ts.get(*i),
                        _ => None,
                    };
                    let Some(next) = next else { return true };
                    ty = next;
                }
                trust_types::Projection::Index(_)
                | trust_types::Projection::ConstantIndex { .. }
                | trust_types::Projection::Subslice { .. } => {
                    ty = match ty {
                        Ty::Array { elem, .. } | Ty::SymArray { elem, .. } | Ty::Slice { elem } => {
                            elem
                        }
                        _ => return true,
                    };
                }
                // A downcast keeps the enum type; a variant field is then indexed into
                // the variant, which this walk does not track: lost.
                _ => return true,
            }
        }
        false
    }
    let op_hits = |op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) => place_hits(func, p),
        _ => false,
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let hit = match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    let mut hit = place_hits(func, place);
                    let all =
                        super::iterator_yield::for_each_rvalue_operand_place(rvalue, &mut |p| {
                            hit |= place_hits(func, p)
                        });
                    hit || !all
                }
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place }
                | Statement::PlaceMention(place) => place_hits(func, place),
                Statement::Intrinsic { args, .. } => args.iter().any(op_hits),
                Statement::CopyNonOverlapping { src, dst, count, .. } => {
                    op_hits(src) || op_hits(dst) || op_hits(count)
                }
                Statement::StorageLive(_) | Statement::StorageDead(_) => false,
                _ => true,
            };
            if hit {
                return true;
            }
        }
        let hit = match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                args.iter().any(op_hits) || place_hits(func, dest)
            }
            Terminator::TailCall { args, .. } => args.iter().any(op_hits),
            Terminator::SwitchInt { discr, .. } => op_hits(discr),
            Terminator::Assert { cond, .. } => op_hits(cond),
            Terminator::Drop { place, .. } => place_hits(func, place),
            Terminator::Goto(_)
            | Terminator::Return
            | Terminator::Unreachable
            | Terminator::Resume => false,
            // `Opaque` and anything added later: unaccountable.
            _ => true,
        };
        if hit {
            return true;
        }
    }
    false
}

/// [`stored_ref_pointee_names`]' fold invariant: a borrowed place whose name a retagged
/// borrow may fold to without any stored pointer on the way: a place with no `Deref`,
/// or `(*r)..` with exactly one leading `Deref` of a retagged reference local `r` and
/// no `Deref` after it.
pub(super) fn borrowed_place_is_unstored(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> bool {
    borrowed_place_is_unstored_with(func, place, &premised_capture_fields(func))
}

/// [`borrowed_place_is_unstored`] with the body's [`premised_capture_fields`] in hand:
/// also `(*_1).k*` and places under it with no further `Deref`, for a premised field
/// `k` (FRESH-CAPTURE-1) — the pointee of a capture whose every value is a fresh shared
/// borrow, no stored pointer after it.
fn borrowed_place_is_unstored_with(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    premised: &[usize],
) -> bool {
    use trust_types::Projection;
    if place.local == CLOSURE_ENV_LOCAL
        && let [Projection::Deref, Projection::Field(k), Projection::Deref, rest @ ..] =
            place.projections.as_slice()
        && premised.contains(k)
        && !rest.iter().any(|p| matches!(p, Projection::Deref))
    {
        return true;
    }
    // RETURN-PAYLOAD-RETAG-1: `(*(b as V).i)..` (or a tuple payload's element) for a
    // shared reference the call-return retag of `b` covers, no stored pointer after it.
    if let Some(at) = place.projections.iter().position(|p| matches!(p, Projection::Deref))
        && retagged_return_payload_ref(func, place.local, &place.projections[..at])
        && !place.projections[at + 1..].iter().any(|p| matches!(p, Projection::Deref))
    {
        return true;
    }
    match place.projections.split_first() {
        None => true,
        Some((Projection::Deref, rest)) => {
            matches!(crate::local_ty_ref(func, place.local), Some(Ty::Ref { .. }))
                && ref_local_is_retagged(func, place.local)
                && !rest.iter().any(|p| matches!(p, Projection::Deref))
        }
        Some(_) => !place.projections.iter().any(|p| matches!(p, Projection::Deref)),
    }
}

/// A closure body's environment parameter.
const CLOSURE_ENV_LOCAL: usize = 1;

/// Trust (2026-10-18, FRESH-CAPTURE-1; gate RCA precision T1): the capture fields of
/// THIS closure body whose pointee [`stored_ref_pointee_names`] keeps across a call —
/// the fields the COMPILER installed ([`crate::fresh_shared_capture_fields_for`]: in
/// every value of the closure type, field `k` holds the tag of a fresh shared borrow
/// made at the closure's one construction site, and no code can forge a value of the
/// type), re-gated on the body verified:
///
/// * `_1` is a PARAMETER of type `&C` (shared) with `C` a closure type, never
///   reseated or aliased (`local_defs::pointer_is_pinned`): every `(*_1).k` read
///   reads the environment the caller passed;
/// * upvar `k` is a SHARED reference whose pointee grants no write
///   ([`pointee_is_read_only`]: pointer-free `Freeze` data, a slice of it, or `str`),
///   so the borrow's tag freezes every byte the capture reaches;
/// * no statement or terminator writes a place rooted at `_1` or an unlocatable place
///   (`Statement::place_writes` / `Terminator::place_writes`).
///
/// Empty for every body the compiler certified nothing for — the CALL-HAVOC-ESCAPE-2
/// behaviour.
pub(crate) fn premised_capture_fields(func: &VerifiableFunction) -> Vec<usize> {
    let installed = crate::fresh_shared_capture_fields_for(&func.def_path);
    if installed.is_empty()
        || !crate::local_defs::is_parameter(func, CLOSURE_ENV_LOCAL)
        || !crate::local_defs::pointer_is_pinned(func, CLOSURE_ENV_LOCAL)
    {
        return Vec::new();
    }
    let Some(Ty::Ref { mutable: false, inner }) = crate::local_ty_ref(func, CLOSURE_ENV_LOCAL)
    else {
        return Vec::new();
    };
    let Ty::Closure { upvars, .. } = &**inner else {
        return Vec::new();
    };
    if body_writes_under_local_or_unlocatable(func, CLOSURE_ENV_LOCAL) {
        return Vec::new();
    }
    let mut fields: Vec<usize> = installed
        .into_iter()
        .filter(|k| {
            matches!(upvars.get(*k), Some(Ty::Ref { mutable: false, inner })
                if pointee_is_read_only(inner, 2))
        })
        .collect();
    fields.sort_unstable();
    fields.dedup();
    fields
}

/// Whether any statement or terminator of `func` writes a place rooted at `local`, or
/// writes a place no name locates (fail-closed).
fn body_writes_under_local_or_unlocatable(func: &VerifiableFunction, local: usize) -> bool {
    let hits = |writes: trust_types::PlaceWrites<'_>| match writes {
        trust_types::PlaceWrites::None => false,
        trust_types::PlaceWrites::Places(places) => places.iter().any(|(p, _)| p.local == local),
        trust_types::PlaceWrites::Unlocatable => true,
    };
    func.body.blocks.iter().any(|block| {
        block.stmts.iter().any(|stmt| hits(stmt.place_writes()))
            || hits(block.terminator.place_writes())
    })
}

/// [`stored_ref_pointee_names`]' walk of a closure body's environment `_1: &C` when
/// [`premised_capture_fields`] is non-empty: the `ty` arm of [`stored_ref_positions`]
/// for a retagged shared reference (the `UnsafeCell` bytes of the pointee are named),
/// then the closure's upvars FIELD BY FIELD instead of the whole `_1*`: a premised
/// field names nothing, every other upvar is walked as a stored position (`&U` names
/// `_1*.j*`, a by-value capture names what a stored pointer inside it reaches).
fn premised_env_positions(
    func: &VerifiableFunction,
    ty: &Ty,
    premised: &[usize],
    skip_std: &std::cell::OnceCell<bool>,
    out: &mut Vec<String>,
    seen: &mut FxHashSet<String>,
) {
    let Ty::Ref { mutable: false, inner } = ty else {
        return;
    };
    let Ty::Closure { upvars, .. } = &**inner else {
        return;
    };
    let mut deref = trust_types::Place {
        local: CLOSURE_ENV_LOCAL,
        projections: vec![trust_types::Projection::Deref],
    };
    let mut cells = Vec::new();
    unsafe_cell_places(&func.body.datatype_defs, &deref, inner, &mut cells);
    for cell in &cells {
        let name = place_to_var_name(func, cell);
        push_unique_pointee_name(out, seen, name);
    }
    for (j, upvar) in upvars.iter().enumerate() {
        if premised.contains(&j) {
            continue;
        }
        deref.projections.push(trust_types::Projection::Field(j));
        stored_ref_positions(func, &mut deref, upvar, false, skip_std, out, seen, 23);
        deref.projections.pop();
    }
}

/// Trust (R3 GUARD-CALL-HAVOC-FOLD, 2026-10-10): whether the reference local `local`,
/// although NOT retagged where it gets its value (it is loaded out of memory — a tuple
/// or struct field, `_21 = copy (_11.0)`), has a deref `*local` that the name mint
/// FOLDS to a concrete referent `R` which [`borrowed_place_is_unstored`] accepts: `R`
/// has no `Deref`, or exactly one leading `Deref` of a retagged reference local.
///
/// Why the walk may then keep `local*` (treat `local` as fresh). Every read through
/// `*local` is spelled by `R`'s name — the fold (`referent_fold::is_stable`, walked
/// over every hop that carried the address) is the alias fact `*local ≡ R` — so
/// havocking `local*` at a call means havocking `R`'s own name. That is exactly the
/// question THE FOLD INVARIANT below answers for a retagged borrow `l = &R`: `R`'s
/// name is killed unless `R` is unstored. The pointer's value having travelled
/// through a field of a local (`format!` packs `&c.groups` into `(&usize,)` and
/// reads it back) changes neither which storage `R` is nor who can write it, so the
/// two spellings of the same alias must get the same answer. Before this, a
/// `format!("{}", c.groups)` on an early-return branch havocked `c*.1` at EVERY call
/// in the body — including `c.heads.is_multiple_of(c.groups)` BEFORE the format —
/// and `if c.groups == 0 { return .. }` no longer guarded `c.heads / c.groups`
/// (nn-glm5/nn-qwen3 `num_kv_groups`, preview3 R3: false DivisionByZero refutation).
///
/// FAIL-CLOSED by construction: a fold the stability walk refuses leaves `*local`
/// unfolded (`local*`), whose root is not retagged, so `borrowed_place_is_unstored`
/// answers `false` and the name stays havocked; a definitional fold through a
/// stored reference (`(*M).f*`, `**M`) carries a second `Deref` and is refused the
/// same way; and a fold onto a place reached through a stored raw pointer
/// (`stored_raw_body`'s `p*.0*`) is refused by the same predicate that refuses the
/// retagged borrow of it.
fn ref_local_folds_to_unstored_place_with(
    func: &VerifiableFunction,
    local: usize,
    premised: &[usize],
) -> bool {
    let deref = trust_types::Place { local, projections: vec![trust_types::Projection::Deref] };
    let canonical = crate::canonical_place(func, &deref);
    canonical != deref && borrowed_place_is_unstored_with(func, &canonical, premised)
}

/// Whether the reference local `local` is retagged where it gets its value (see
/// [`stored_ref_pointee_names`]): a parameter whose pointer is never reseated
/// (`local_defs::pointer_is_pinned`), or a single-valued local whose one value is a
/// borrow (`Rvalue::Ref`), a call's return value, a whole-local copy of such a local
/// (followed, bounded), or (RETURN-PAYLOAD-RETAG-1) a copy of a shared reference out of
/// the payload of a single-valued enum call return ([`retagged_return_payload_ref`]:
/// `t = copy (_n as Some).0` after `_n = Iterator::next(..)`). A deref temp
/// `_t = copy (*p).0` is NOT.
fn ref_local_is_retagged(func: &VerifiableFunction, local: usize) -> bool {
    let mut local = local;
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, local) {
            return crate::local_defs::pointer_is_pinned(func, local);
        }
        if let Some(Terminator::Call { func: callee, .. }) =
            crate::local_defs::unique_value_call(func, local)
        {
            // VEC-INDEX-TIE-HEAP-1: an indexed reference's retag is an identity
            // of that returned reference, not a whole-body frame for the buffer.
            // A copied element value can outlive the temporary borrow; another
            // call can then write the buffer through a previously stashed pointer.
            // Include this pointee (and copies tracing here) in the unconditional
            // call/drop/opaque and opaque-store dependency lists. Recognizing a
            // spelling here only REMOVES preservation credit; it grants no frame.
            return !super::unwrap_panic::is_std_scalar_index_call(callee);
        }
        match crate::local_defs::unique_value_def(func, local) {
            Some(Rvalue::Ref { .. }) => return true,
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                local = q.local;
            }
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q)))
                if retagged_return_payload_ref(func, q.local, &q.projections) =>
            {
                return true;
            }
            _ => return false,
        }
    }
    false
}

/// Trust (2026-10-18, RETURN-PAYLOAD-RETAG-1; candidate-gate RCA precision D2): whether
/// `local` is an ENUM local whose one value is a call's return value
/// (`local_defs::unique_value_call`: one whole definition, the call's destination, and no
/// `&mut`/`&raw` borrow of the slot, no partial or unlocatable write), with its variants
/// recorded. `Iterator::next`'s `Option<&T>` in every `for t in &v` is one.
///
/// The return place of a call is retagged where the call returns (AddRetag puts a
/// `Retag` on every call destination whose type may contain a reference), and the retag
/// reaches the references INSIDE the value (Miri's default `-Zmiri-retag-fields=all`;
/// for a `Scalar`/`ScalarPair` value such as `Option<&T>` or `Option<(usize, &T)>`, also
/// the narrower `scalar` mode, the one rustc's own `noalias`/`dereferenceable`
/// annotations rely on). So a shared reference in its payload holds a fresh
/// `SharedReadOnly` (Stacked Borrows) / frozen child (Tree Borrows) tag, and every copy
/// read out of the never-rewritten local carries that tag: exactly what the KEPT rule of
/// [`stored_ref_pointee_names`] relies on for a call-return reference LOCAL `t = f()`.
fn call_return_enum_root(func: &VerifiableFunction, local: usize) -> bool {
    !crate::local_defs::is_parameter(func, local)
        && super::terminator_presence_for(func).has_bare_dest_call
        && matches!(
            crate::local_ty_ref(func, local),
            Some(Ty::Adt { adt_kind: Some(trust_types::AdtKind::Enum), variants, .. })
                if !variants.is_empty()
        )
        && crate::local_defs::unique_value_call(func, local).is_some()
}

/// [`call_return_enum_root`]'s payload positions that the call-return retag covers: the
/// projections `[Downcast(v), Field(i)]` naming a SHARED reference payload field of
/// `local`, or `[Downcast(v), Field(i), Field(j)]` naming a shared reference element of a
/// tuple payload field (`enumerate`'s `Option<(usize, &T)>`). A `&mut` payload is not one:
/// its pointee is the ordinary list's question.
fn retagged_return_payload_ref(
    func: &VerifiableFunction,
    local: usize,
    projections: &[trust_types::Projection],
) -> bool {
    use trust_types::Projection;
    let [Projection::Downcast(v), Projection::Field(i), rest @ ..] = projections else {
        return false;
    };
    if !call_return_enum_root(func, local) {
        return false;
    }
    let Some(Ty::Adt { variants, .. }) = crate::local_ty_ref(func, local) else {
        return false;
    };
    let Some((_, field)) = variants.get(*v).and_then(|var| var.fields.get(*i)) else {
        return false;
    };
    let at = match (rest, field) {
        ([], t) => t,
        ([Projection::Field(j)], Ty::Tuple(elems)) => match elems.get(*j) {
            Some(t) => t,
            None => return false,
        },
        _ => return false,
    };
    matches!(at, Ty::Ref { mutable: false, .. })
}

/// [`stored_ref_positions`] over one payload position of a [`call_return_enum_root`]:
/// a shared reference (or a tuple's shared reference element) is walked as the retagged
/// reference it is (its pointee's `UnsafeCell` bytes and the stored pointers inside it are
/// named, its `Freeze` bytes are kept); everything else exactly as a stored position.
fn retagged_payload_positions(
    func: &VerifiableFunction,
    at: &mut trust_types::Place,
    ty: &Ty,
    skip_std: &std::cell::OnceCell<bool>,
    out: &mut Vec<String>,
    seen: &mut FxHashSet<String>,
    fuel: u32,
) {
    match ty {
        Ty::Tuple(elems) => {
            for (j, elem) in elems.iter().enumerate() {
                at.projections.push(trust_types::Projection::Field(j));
                let fresh = matches!(elem, Ty::Ref { mutable: false, .. });
                stored_ref_positions(func, at, elem, fresh, skip_std, out, seen, fuel);
                at.projections.pop();
            }
        }
        _ => {
            let fresh = matches!(ty, Ty::Ref { mutable: false, .. });
            stored_ref_positions(func, at, ty, fresh, skip_std, out, seen, fuel);
        }
    }
}

/// [`stored_ref_pointee_names`]' walk: the names under `place` (of type `ty`) that
/// dereference a reference loaded from memory. `deref_ok` is true only for a retagged
/// reference LOCAL itself.
#[allow(clippy::too_many_arguments)]
fn stored_ref_positions(
    func: &VerifiableFunction,
    place: &mut trust_types::Place,
    ty: &Ty,
    deref_ok: bool,
    skip_std: &std::cell::OnceCell<bool>,
    out: &mut Vec<String>,
    seen: &mut FxHashSet<String>,
    fuel: u32,
) {
    let emit = |p: &trust_types::Place, out: &mut Vec<String>, seen: &mut FxHashSet<String>| {
        let name = place_to_var_name(func, p);
        push_unique_pointee_name(out, seen, name);
    };
    let Some(fuel) = fuel.checked_sub(1) else {
        emit(place, out, seen);
        return;
    };
    match ty {
        Ty::Ref { inner, mutable } => {
            place.projections.push(trust_types::Projection::Deref);
            if deref_ok {
                // Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1, the POINTEE half) — a
                // retagged SHARED reference freezes only the `Freeze` bytes of its
                // pointee: its `UnsafeCell` bytes are written, in a defined execution,
                // through any copy of it a callee holds (`poke(c)` for `c: &Cell<usize>`,
                // a `&'static Cell` a zero-argument callee reaches through a
                // `thread_local!`). Name exactly those bytes; a frozen sibling keeps its
                // facts. (A `&mut` local's pointee is under its base name on the
                // ordinary list.)
                if !*mutable {
                    let mut cells = Vec::new();
                    unsafe_cell_places(&func.body.datatype_defs, place, inner, &mut cells);
                    for cell in &cells {
                        emit(cell, out, seen);
                    }
                }
                stored_ref_positions(func, place, inner, false, skip_std, out, seen, fuel);
            } else {
                emit(place, out, seen);
            }
            place.projections.pop();
        }
        // Trust (CALL-HAVOC-ESCAPE-2 review, 2026-10-06): a raw pointer stored BELOW a
        // root carries whatever permission its bits have, whatever its pointee type: a
        // `static mut` may hold a copy of it, so a callee can write `*p.q` and a later
        // re-read sees it. A raw-pointer ROOT local is on the ordinary list already.
        Ty::RawPtr { .. } => {
            if !place.projections.is_empty() {
                place.projections.push(trust_types::Projection::Deref);
                emit(place, out, seen);
                place.projections.pop();
            }
        }
        Ty::Tuple(elems) => {
            for (i, t) in elems.iter().enumerate() {
                place.projections.push(trust_types::Projection::Field(i));
                stored_ref_positions(func, place, t, false, skip_std, out, seen, fuel);
                place.projections.pop();
            }
        }
        // A `Box` below a root likewise: its pointee is reached by a `Deref` of the box
        // itself, and the box's bits are as good as a raw pointer's. A `Box` ROOT local is
        // pointer-carrying, on the ordinary list already. (`Vec`/`String`/`Rc`/`Arc`
        // contents have no header place name: indexed call-result contents have
        // their own dependency names, independent of the header. Other structs
        // are walked like any other, and a `Vec` is `Seq`.)
        Ty::Adt { name, fields, .. } if type_name_is_box(name) => {
            // A ROOT `Box` local is on the ordinary list (`ty_contains_mut_pointer` answers
            // `true` for any std `Box`), which havocs it whole at every call.
            if place.projections.is_empty() {
                return;
            }
            place.projections.push(trust_types::Projection::Deref);
            emit(place, out, seen);
            place.projections.pop();
            // Belt and braces: walk the recorded fields too (they hold the raw pointer).
            for (i, (_, t)) in fields.iter().enumerate() {
                place.projections.push(trust_types::Projection::Field(i));
                stored_ref_positions(func, place, t, false, skip_std, out, seen, fuel);
                place.projections.pop();
            }
        }
        // A std struct's private fields (`VecDeque`'s `RawVec` buffer pointer, ...) have no
        // place name in a NON-std body that never projects into a std ADT
        // (`skip_std`): user code cannot name them, and a spec cannot either. Walking
        // them would emit names that rebind only their ANCESTORS — the collection-length
        // abstraction keyed on the reference itself (`d` for `d: &VecDeque<u32>`), which
        // lives in the protected bytes. A std body, or a user body into which a std body
        // was inlined, walks them like any struct.
        Ty::Adt { name, adt_kind: Some(trust_types::AdtKind::Struct), .. }
            if type_name_is_std(name)
                && !type_name_has_public_fields(name)
                && *skip_std.get_or_init(|| {
                    !type_name_is_std(&func.def_path) && !body_projects_into_std_adt(func)
                }) => {}
        Ty::Adt { fields, adt_kind: Some(trust_types::AdtKind::Struct), .. } => {
            // A field-less rendering may hide a pointer (fail-closed, std markers aside).
            if fields.is_empty() && ty_may_hold_pointer(ty, 24) {
                emit(place, out, seen);
            }
            for (i, (_, t)) in fields.iter().enumerate() {
                place.projections.push(trust_types::Projection::Field(i));
                stored_ref_positions(func, place, t, false, skip_std, out, seen, fuel);
                place.projections.pop();
            }
        }
        // RETURN-PAYLOAD-RETAG-1: an enum ROOT whose one value is a call's return value
        // ([`call_return_enum_root`]) is walked variant by variant instead of named
        // whole: a shared reference in its payload carries the call-return retag. The
        // union view (`__tag`, `__v<v>_<i>`, the same bytes as variant `v`'s field `i`)
        // is walked the same way, so either spelling of a payload gets one answer.
        Ty::Adt { adt_kind: Some(trust_types::AdtKind::Enum), variants, fields, .. }
            if place.projections.is_empty() && call_return_enum_root(func, place.local) =>
        {
            for (v, variant) in variants.iter().enumerate() {
                place.projections.push(trust_types::Projection::Downcast(v));
                for (i, (_, t)) in variant.fields.iter().enumerate() {
                    place.projections.push(trust_types::Projection::Field(i));
                    retagged_payload_positions(func, place, t, skip_std, out, seen, fuel);
                    place.projections.pop();
                }
                place.projections.pop();
            }
            for (k, (name, t)) in fields.iter().enumerate() {
                place.projections.push(trust_types::Projection::Field(k));
                let is_payload_view = name.strip_prefix("__v").is_some_and(|vi| {
                    vi.split_once('_').is_some_and(|(v, i)| {
                        v.parse::<usize>().ok().zip(i.parse::<usize>().ok()).is_some_and(
                            |(v, i)| {
                                variants
                                    .get(v)
                                    .and_then(|var| var.fields.get(i))
                                    .is_some_and(|(_, vt)| vt == t)
                            },
                        )
                    })
                });
                if is_payload_view {
                    retagged_payload_positions(func, place, t, skip_std, out, seen, fuel);
                } else {
                    stored_ref_positions(func, place, t, false, skip_std, out, seen, fuel);
                }
                place.projections.pop();
            }
        }
        _ => {
            if ty_may_hold_pointer(ty, 24) {
                emit(place, out, seen);
            }
        }
    }
}

/// Whether `ty` may hold a POINTER anywhere — a reference, a raw pointer or an owning
/// pointer — through fields, variants, elements and captures. Fail-closed: an
/// unresolved type (`Datatype`
/// marker, `Unsupported`, a type parameter, `dyn`, a field-less ADT, exhausted fuel)
/// answers `true`.
fn ty_may_hold_pointer(ty: &Ty, fuel: u32) -> bool {
    let Some(fuel) = fuel.checked_sub(1) else { return true };
    match ty {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Bv(_)
        | Ty::Unit
        | Ty::Never
        | Ty::Str
        | Ty::FnDef { .. }
        | Ty::FnPtr { .. } => false,
        Ty::Ref { .. } | Ty::RawPtr { .. } => true,
        // An owned `Vec`'s elements have no place name (they are reached only through
        // call results, which are retagged): the `Vec` itself never needs havocking.
        Ty::Seq { .. } => false,
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            ty_may_hold_pointer(elem, fuel)
        }
        Ty::Tuple(elems) => elems.iter().any(|t| ty_may_hold_pointer(t, fuel)),
        // An ADT with neither a recorded field nor a recorded variant (a field-less
        // rendering may hide anything) answers `true`; otherwise its recorded fields and
        // variant payloads decide, stamped or not (a C-like enum's variants are listed).
        Ty::Adt { name, .. } if type_name_is_box(name) => true,
        Ty::Adt { name, fields, variants, .. } => {
            // Zero-sized std markers hold no value at all, whatever their type arguments
            // (full paths only: a user type named `PhantomData` is not exempt).
            if fields.is_empty() && type_name_is_zero_sized_std_marker(name) {
                return false;
            }
            (fields.is_empty() && variants.is_empty())
                || fields.iter().any(|(_, t)| ty_may_hold_pointer(t, fuel))
                || variants
                    .iter()
                    .any(|v| v.fields.iter().any(|(_, t)| ty_may_hold_pointer(t, fuel)))
        }
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            upvars.iter().any(|t| ty_may_hold_pointer(t, fuel))
        }
        _ => true,
    }
}

/// Rule (b) of [`escape_havoc`]: `local` is a PARAMETER of type `&mut T` where `T` is
/// [`ty_is_protected_plain_pointee`], whose pointer is fixed for the whole body
/// (`local_defs::pointer_is_pinned`: never written, no alias of the slot) and never
/// leaves it (`!local_pointee_may_escape`: no copy or move of the pointer into any
/// rvalue, call, tail call or intrinsic argument; no `&mut`/`&raw` borrow of any place
/// under it; no shared borrow of the slot; no `Drop` of a place under it; refused on an
/// `Opaque` terminator and on any statement or rvalue it does not classify).
/// Flow-insensitive over the whole body: since ESCAPE-HAVOC-FLOW-1 the arm asks
/// [`protected_mut_param_shape`] and the escape reach at each call
/// ([`escape_havoc_at`]); this is kept for the unit tests that pin the old rule.
#[cfg(test)]
pub(super) fn protected_private_mut_param(func: &VerifiableFunction, local: usize) -> bool {
    protected_mut_param_shape(func, local) && !local_pointee_may_escape(func, local)
}

/// [`protected_private_mut_param`] without its escape clause: a `&mut T` PARAMETER, `T`
/// [`ty_is_protected_plain_pointee`], whose pointer is pinned. Where its pointee escapes
/// is [`escape_havoc_at`]'s question.
fn protected_mut_param_shape(func: &VerifiableFunction, local: usize) -> bool {
    crate::local_defs::is_parameter(func, local)
        && matches!(
            crate::local_ty_ref(func, local),
            Some(Ty::Ref { mutable: true, inner }) if ty_is_protected_plain_pointee(inner)
        )
        && crate::local_defs::pointer_is_pinned(func, local)
}

/// The pointee a [`protected_private_mut_param`] may have: a finite tree of scalars,
/// tuples, arrays and stamped struct/enum ADTs with recorded fields (as
/// [`ty_is_recorded_pure_frozen_value`]: no union, no `UnsafeCell`-based type by name or
/// field, no `Datatype` marker, no `Unsupported` leaf, no type parameter, no closure or
/// coroutine) whose ONLY pointers are SHARED references to frozen data
/// ([`shared_ref_target_is_frozen_data`]: `&U`, `&[U]` or `&str` with `U` a
/// [`ty_is_recorded_pure_frozen_value`] — pointer-free, `Freeze`, fully resolved), and
/// with no ADT named as a pinning marker (`PhantomPinned`, `UnsafePinned`, `Pin`).
/// Refused: a `&mut`, a raw pointer, an owning pointer (`Box`, `Vec`/`Seq`, `String`,
/// `Rc`, ... — their heap is not under the parameter's protector), a fn pointer, a
/// `dyn`, a shared reference to anything holding a pointer or interior mutability, and
/// every unclassified shape.
///
/// Trust (P1 precision, 2026-10-06): the shared-reference fields are the widening of
/// rule (b) that recovers TINV P1's `struct Parser<'a> { b: &'a [u8], i: usize }`. Only
/// the bytes of `*param` ITSELF are kept: the scalar fields and each shared-reference
/// field's VALUE — its address and, for `&[U]`/`&str`, its length metadata
/// `param*.f__slice_len`. The protector covers every byte of `*param`, whatever type
/// those bytes have, so no write not derived from `param` can change them during the
/// call. P1's `i <= len(b)` needs nothing more.
///
/// The memory BEHIND such a field (`param*.f*`, `param*.f*[k]`) is NOT kept: the arm
/// havocs `param*.f*` at every call ([`stored_ref_pointee_names`]). The tempting
/// argument "a foreign write to `Freeze` bytes behind a live shared reference
/// invalidates it, so any later read through it is UB" fails for a reference STORED IN
/// MEMORY: a field is never retagged (it is not a function argument and is not loaded
/// into a local), so its value can carry a tag that never became `SharedReadOnly` /
/// `Frozen` — `ptr::write` of a `*const [u8]` into the field puts raw-pointer bits
/// there. A nullary `poke()` writing the same buffer through a `static mut` pointer is
/// then defined under Stacked and Tree Borrows, and the post-call `copy (*p).b` retags
/// a fresh child that reads the NEW bytes (adversarial review, 2026-10-06:
/// `if p.b[0] < 4 { poke(); a[p.b[0] as usize] }` kept, in the kill list, the pointee
/// facts its bounds row needs while the execution, reported Miri-clean, indexed 9; end
/// to end the row is not proved today only because each read uses a fresh deref temp). The same holds for a reference
/// loaded into a deref temp (not retagged) and for every root kind, not only this
/// parameter: [`stored_ref_pointee_names`] (CALL-HAVOC-ESCAPE-2) havocs all of them at
/// every call.
///
/// `Unpin` is decided STRUCTURALLY: the extracted types do not record it. Every type
/// admitted here is built from scalars and shared references by tuples, arrays and
/// ADTs, which are `Unpin` unless a field is `!Unpin` or the ADT carries a user
/// `impl !Unpin` (nightly `negative_impls`); a reference is `Unpin` whatever it points
/// at. `PhantomPinned` is a field-less struct, refused both by the recorded-field rule
/// and by name. The user negative impl is the disclosed residual
/// (docs/KNOWN_HAZARDS.md, CALL-HAVOC-ESCAPE-1).
fn ty_is_protected_plain_pointee(ty: &Ty) -> bool {
    fn adt_name_is_pin_marker(name: &str) -> bool {
        let base = name.split('<').next().unwrap_or(name);
        let tail = base.rsplit("::").next().unwrap_or(base).trim();
        tail.contains("Pinned") || tail == "Pin"
    }
    /// [`ty_is_recorded_pure_frozen_value`]'s walk with one more admitted leaf: a
    /// shared reference whose target is [`shared_ref_target_is_frozen_data`], admitted
    /// only through struct and tuple fields (`ref_ok`), never inside an enum variant or
    /// an array element (precision only since [`stored_ref_pointee_names`] covers those
    /// too; kept as the reviewed shape).
    fn walk(ty: &Ty, ref_ok: bool, fuel: u32) -> bool {
        let Some(fuel) = fuel.checked_sub(1) else { return false };
        match ty {
            // `Ty::Never`: see `ty_is_pure_frozen_value` (upstream 1.101).
            Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Unit | Ty::Never => true,
            Ty::Tuple(elems) => elems.iter().all(|t| walk(t, ref_ok, fuel)),
            Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => walk(elem, false, fuel),
            Ty::Adt { name, fields, variants, adt_kind: Some(kind), .. }
                if matches!(kind, trust_types::AdtKind::Struct | trust_types::AdtKind::Enum) =>
            {
                let ref_ok = ref_ok && matches!(kind, trust_types::AdtKind::Struct);
                !adt_name_is_pin_marker(name)
                    && !type_name_is_interior_mutable(name)
                    && !type_name_is_owning_pointer(name)
                    && !fields.is_empty()
                    && fields.iter().all(|(_, t)| walk(t, ref_ok, fuel))
                    && variants.iter().all(|v| v.fields.iter().all(|(_, t)| walk(t, false, fuel)))
            }
            Ty::Ref { mutable: false, inner } => ref_ok && shared_ref_target_is_frozen_data(inner),
            _ => false,
        }
    }
    walk(ty, true, 24)
}

/// Whether an ADT's NAME is a std owning or raw-wrapping pointer (`Box`, `Rc`, `Arc`,
/// `Weak`, `Vec`, `String`, `NonNull`, `Unique`): refused by name as well as by the field
/// walk (which finds their raw pointer), so a compacted rendering cannot pass. Their heap
/// is not under the `&mut` parameter's protector.
fn type_name_is_owning_pointer(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name);
    let tail = base.rsplit("::").next().unwrap_or(base).trim();
    matches!(tail, "Box" | "Rc" | "Arc" | "Weak" | "Vec" | "String" | "NonNull" | "Unique")
}

/// Whether an ADT's NAME is `alloc::boxed::Box` (the one owning pointer with a built-in
/// `Deref` projection).
///
/// FULL path only (review of `2628c2a847`): a user `m::Box` is an ordinary struct, and
/// matching the last segment let the arm below skip its fields.
fn type_name_is_box(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name).trim();
    matches!(base, "alloc::boxed::Box" | "std::boxed::Box")
}

/// Whether an ADT with no recorded field is a zero-sized std marker (`PhantomData`,
/// `PhantomPinned`, the `Global` allocator), by FULL path in either the `core`/`alloc`
/// or the `std` spelling the extractor mostly renders.
pub(crate) use trust_types::interior_mutability::type_name_is_zero_sized_std_marker;

/// The target of a shared reference a [`ty_is_protected_plain_pointee`] may hold: `str`,
/// a slice `[U]`, or a sized `U`, where `U` is a [`ty_is_recorded_pure_frozen_value`]
/// (pointer-free, `Freeze`, every ADT stamped with recorded fields). Deliberately ONE
/// level: a `&&U` or `&[&U]` is refused (precision only).
fn shared_ref_target_is_frozen_data(target: &Ty) -> bool {
    match target {
        Ty::Str => true,
        Ty::Slice { elem } => ty_is_recorded_pure_frozen_value(elem),
        _ => ty_is_recorded_pure_frozen_value(target),
    }
}

pub(crate) fn terminator_def_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<String> {
    terminator_def_names_structured(func, block).flatten(func)
}

/// The havoc half of a terminator's write set (see [`TermDefs`]).
#[derive(Clone, Debug)]
pub(crate) enum TermHavoc {
    /// The terminator havocs no alias list.
    None,
    /// The terminator havocs the WHOLE-FUNCTION list [`function_havoc_names`],
    /// unrefined. Kept symbolic so a consumer that indexes writes (the statement
    /// write index behind the version oracle) holds ONE shared list for every such
    /// terminator instead of a copy per block — the copies are what made the
    /// oracle's gen-sets `O(calls x pointer locals)`.
    Function,
    /// A per-call REFINATION of the whole-function list (`callee_write_set`), kept as
    /// a DELTA over it — a few names dropped, a few appended — rather than as the
    /// refined list. A copy per call is `O(calls x pointer locals)` again, which is
    /// what `Function` exists to avoid; the delta is `O(arguments)`.
    Refined(std::rc::Rc<HavocDelta>),
    /// The whole-function list restricted to the names a callee can reach without
    /// an argument ([`escape_havoc`]): one shared value per function, like
    /// `Function`, for the call arm whose arguments hand the callee no write
    /// channel. Built only when it is a strict, non-empty part of the list (an
    /// empty part is `None`, the whole list `Function`).
    Escape(std::rc::Rc<EscapeHavoc>),
}

/// [`TermHavoc::Escape`]'s payload: the whole-function list `h` split by
/// [`escape_havoc`]'s exemption ([`protected_private_mut_param`]).
#[derive(Debug)]
pub(crate) struct EscapeHavoc {
    /// The names of `h` still havocked, in `h`'s order and with its repeats (so the
    /// flattened list is the one a filter of `h` would build).
    pub(crate) kept: Vec<String>,
    /// The distinct names of `h` that are not, sorted.
    pub(crate) dropped: Vec<String>,
}

/// A per-call refinement of the whole-function havoc list `h`, as the two steps
/// `callee_write_set` takes: the call-write-set step (drop the replaceable roots'
/// base names, deduplicating the list on the way, then append the callee's written
/// paths) and, in order, the shared-reborrow steps (drop one base name, append its
/// replacement names). [`HavocDelta::flatten`] rebuilds the refined `Vec` exactly as
/// the refinement used to build it; [`HavocDelta::contains`] answers membership of
/// the refined SET without building it.
#[derive(Clone, Debug)]
pub(crate) struct HavocDelta {
    pub(crate) call: Option<callee_write_set::CallHavocDelta>,
    pub(crate) reborrow: Vec<callee_write_set::ReborrowStep>,
}

impl HavocDelta {
    /// The refined list, byte-identical to what the in-place refinement produced.
    pub(crate) fn flatten(&self, h: &[String]) -> Vec<String> {
        let mut v: Vec<String> = match &self.call {
            Some(call) => call.apply(h),
            None => h.to_vec(),
        };
        for (base, replacement) in &self.reborrow {
            v.retain(|n| n != base);
            if replacement.is_empty() {
                continue;
            }
            if replacement.len() <= 4 {
                for name in replacement {
                    if !v.contains(name) {
                        v.push(name.clone());
                    }
                }
            } else {
                let mut seen: FxHashSet<&str> = FxHashSet::with_capacity_and_hasher(
                    v.len() + replacement.len(),
                    Default::default(),
                );
                for existing in &v {
                    seen.insert(existing.as_str());
                }
                let to_add: Vec<&String> =
                    replacement.iter().filter(|name| seen.insert(name.as_str())).collect();
                v.extend(to_add.into_iter().cloned());
            }
        }
        v
    }

    /// Whether `name` is in the refined list, given membership in `h`. Each step
    /// maps `S` to `(S \ dropped) ∪ appended`, so the last step that mentions `name`
    /// decides, and `h` decides when none does.
    pub(crate) fn contains(&self, name: &str, in_h: &dyn Fn(&str) -> bool) -> bool {
        refined_list_contains(name, in_h, self.call.as_ref(), &self.reborrow)
    }

    /// The names of `h` the refined list no longer holds.
    pub(crate) fn removed(&self, in_h: &dyn Fn(&str) -> bool) -> Vec<String> {
        let mut out: Vec<String> = self
            .call
            .iter()
            .flat_map(|c| c.roots.iter())
            .chain(self.reborrow.iter().map(|(b, _)| b))
            .filter(|n| in_h(n) && !self.contains(n, in_h))
            .cloned()
            .collect();
        out.sort_unstable();
        out.dedup();
        out
    }

    /// The names the refined list holds that `h` does not.
    pub(crate) fn added(&self, in_h: &dyn Fn(&str) -> bool) -> Vec<String> {
        let mut out: Vec<String> = self
            .call
            .iter()
            .flat_map(|c| c.paths.iter())
            .chain(self.reborrow.iter().flat_map(|(_, r)| r.iter()))
            .filter(|n| !in_h(n) && self.contains(n, in_h))
            .cloned()
            .collect();
        out.sort_unstable();
        out.dedup();
        out
    }
}

/// Membership of `name` in `h` refined by `call` and then by the shared-reborrow
/// `steps` (see [`HavocDelta::contains`]).
fn refined_list_contains(
    name: &str,
    in_h: &dyn Fn(&str) -> bool,
    call: Option<&callee_write_set::CallHavocDelta>,
    steps: &[callee_write_set::ReborrowStep],
) -> bool {
    for (base, replacement) in steps.iter().rev() {
        if replacement.iter().any(|r| r == name) {
            return true;
        }
        if base == name {
            return false;
        }
    }
    if let Some(call) = call {
        if call.paths.iter().any(|p| p == name) {
            return true;
        }
        if call.roots.iter().any(|r| r == name) {
            return false;
        }
    }
    in_h(name)
}

/// One name a terminator appends after its havoc list.
#[derive(Clone, Debug)]
pub(crate) enum TermExtra {
    Push(String),
    /// Appended only when not already present — `push_index_fallback_name`'s dedupe.
    PushIfAbsent(String),
}

/// [`terminator_def_names`] with the havoc list kept symbolic. `flatten` rebuilds the
/// legacy `Vec` exactly (same names, same order, same dedupe), and
/// `terminator_def_names` IS that flatten, so the two can never disagree.
#[derive(Clone, Debug)]
pub(crate) struct TermDefs {
    pub(crate) havoc: TermHavoc,
    pub(crate) extra: Vec<TermExtra>,
}

impl TermDefs {
    pub(crate) fn flatten(self, func: &VerifiableFunction) -> Vec<String> {
        let mut names: Vec<String> = match self.havoc {
            TermHavoc::None => Vec::new(),
            TermHavoc::Function => function_havoc_names(func).as_ref().clone(),
            TermHavoc::Refined(delta) => delta.flatten(&function_havoc_names(func)),
            TermHavoc::Escape(e) => e.kept.clone(),
        };
        for e in self.extra {
            match e {
                TermExtra::Push(n) => names.push(n),
                TermExtra::PushIfAbsent(n) => {
                    if !names.contains(&n) {
                        names.push(n);
                    }
                }
            }
        }
        names
    }
}

/// The extras `push_derived_slice_len` + `push_index_fallback_name` append for a
/// whole write of `dest` (spelled `dest_name`), in their order.
fn dest_term_extras(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    dest_name: String,
    extra: &mut Vec<TermExtra>,
) {
    let slice =
        (!dest_name.ends_with(SLICE_LEN_SUFFIX)).then(|| format!("{dest_name}{SLICE_LEN_SUFFIX}"));
    extra.push(TermExtra::Push(dest_name));
    if let Some(s) = slice {
        extra.push(TermExtra::Push(s));
    }
    if dest.projections.is_empty() && local_is_index_operand(func, dest.local) {
        extra.push(TermExtra::PushIfAbsent(local_fallback_name(dest.local)));
    }
    // Trust: 2026-10-12 (UNION-SIBLING-WRITE-1) — a call writing a union field writes
    // every overlapping sibling ([`union_write_cover_name`]).
    if let Some(cover) = union_write_cover_name(func, dest) {
        extra.push(TermExtra::Push(format!("{cover}{SLICE_LEN_SUFFIX}")));
        extra.push(TermExtra::Push(cover));
    }
}

pub(crate) fn terminator_def_names_structured(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> TermDefs {
    let mut defs = terminator_def_names_structured_inner(func, block);
    // Trust (CALL-HAVOC-ESCAPE-2, 2026-10-06): every terminator that runs code the body
    // does not see (a call, drop glue, an opaque terminator) havocs the memory behind
    // every reference LOADED FROM MEMORY, whatever the root ([`stored_ref_pointee_names`]).
    if matches!(
        block.terminator,
        Terminator::Call { .. }
            | Terminator::TailCall { .. }
            | Terminator::Drop { .. }
            | Terminator::Opaque { .. }
    ) {
        defs.extra.extend(stored_ref_pointee_names(func).iter().cloned().map(TermExtra::Push));
    }
    // Trust: 2026-10-08 (H3 OPAQUE-ASM-OUTPUT) — a terminator whose writes the
    // extraction could not LOCATE writes every local, as far as this oracle can tell.
    // `trust_types::Terminator::place_writes` is the wildcard-free classifier that
    // says which terminators those are (today: `Opaque`), and it says
    // `PlaceWrites::Unlocatable` precisely because the extractor kept the successors
    // but dropped the destination: an `asm!` `out` / `lateout` / `inout` /
    // `inlateout` place, a `Yield` resume place, the `dest` of a call it could not
    // lower (`Call(indirect)`, a malformed atomic, a pre-unwind-modelling
    // `Call::..::UnsupportedUnwind`). The `Opaque` arm's `TermHavoc::Function` is the
    // MEMORY half (what unseen code can reach through a pointer — an asm that is not
    // `nomem`/`readonly` clobbers it); it never names a local that is only ever an
    // asm OUTPUT, so `let mut k = n & 3; asm!("add {0}, {0}, #4", inout(reg) k);
    // t[k]` read `k`'s pre-asm definition at the index and PROVED + certified a
    // bounds check that panics on every input (`tests/ploss_adv_false_proofs_
    // realmir.rs`, `h3_*`). Every local's write name is the answer
    // `extend_with_copy_nonoverlapping_writes` already gives the other write with no
    // place: a version bump with no definition, never a claim the local changed.
    if matches!(block.terminator.place_writes(), trust_types::PlaceWrites::Unlocatable) {
        push_every_local_write_name(func, &mut defs.extra);
    }
    defs
}

/// [`extend_with_every_local_write_name`] for a terminator's `Vec`-shaped extras, in
/// local order (deterministic): every local's canonical name, its derived
/// `__slice_len` twin, and its index fallback — what [`dest_term_extras`] mints for a
/// call that writes the WHOLE local.
fn push_every_local_write_name(func: &VerifiableFunction, extra: &mut Vec<TermExtra>) {
    for local in 0..func.body.locals.len() {
        let place = trust_types::Place::local(local);
        dest_term_extras(func, &place, place_to_var_name(func, &place), extra);
    }
}

fn terminator_def_names_structured_inner(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> TermDefs {
    match &block.terminator {
        Terminator::Call {
            func: callee, args, dest, is_foreign, is_unsafe_sig, atomic, ..
        } => {
            // Trust (per-argument havoc refinement — the scheduled precision
            // follow-up behind the verify.precision.2026-07-08 ledger entry): a
            // callee can mutate caller-visible memory ONLY through its
            // arguments. Caller LOCALS have no other channel: statics are not
            // caller-local names; a non-'static `&mut` cannot be stashed into
            // global state by safe code (lifetime bounds); and the one laundering
            // channel — a local's address smuggled through an integer — requires
            // an in-function `AddressOf`/raw-cast site, which fail-closes the
            // skip for the whole function (`func_has_pointer_laundering`). So
            // when EVERY argument is a Constant or a Copy of a pure pointer-free
            // VALUE, the callee cannot reach any local: skip the mut-borrow /
            // mut-pointer havoc and kill only the dest (which the callee
            // genuinely writes). Anything else — Move (escape), Symbolic /
            // Unsupported operands, any Ref/RawPtr/Slice/Adt/closure anywhere in
            // an arg type — keeps the FULL havoc. Restores the guard-across-
            // unrelated-call idioms (`if *r < 1000 { log(); t = *r + 1 }`)
            // without reopening the callee-write false-accept class: every
            // pointer-carrying call (p00-p10, method receivers, closures,
            // mem::replace/swap) still havocs in full.
            //
            // Trust (ENC-DEFECTS 13b, 2026-09-26): a MOVE of a pure pointer-free
            // value is the same bits as a Copy of it — `saturating_sub(move _5,
            // move _6)` over two `u32` temporaries hands the callee nothing a Copy
            // would not — so it joins the Copy arm. The "Move (escape)" exclusion
            // is about a moved POINTER (or a pointer-carrying aggregate), which
            // `ty_is_pure_value` already refuses by TYPE; the laundering gate is
            // unchanged. Before this, every std call over moved scalar temps
            // havocked every `&mut self` field the body had established
            // (`self.used += n` refuted at `self*.0#e_s2_t = u32::MAX` after
            // `self.limit.saturating_sub(self.used)`).
            //
            // Trust (TINV P1 on real MIR, 2026-10-06): an argument that hands the
            // callee no WRITE channel joins the arm ([`arg_grants_no_write`]): a
            // by-value pure `Freeze` ADT (`Option<u8>` into `Try::branch`,
            // `Range<usize>` into `Index::index`), or — for a callee that is not
            // foreign, has no `unsafe` signature and is not atomic — a SHARED
            // reference whose whole reachable memory is pointer-free `Freeze` bytes
            // and which is not a reborrow through a `&mut`/raw pointer (`&[u8]` into
            // `<[u8]>::len`, `&&[u8]` into `PartialEq::eq`; `&*self` stays with the
            // TRUST-10 / 13b refinements below). The premise
            // is the one above (a callee writes caller-visible memory only through
            // what its arguments reach) plus the shared-reference rule of the
            // "Shared-reborrow immutability across a call" TCB row: a write through a
            // `&T` to `Freeze` bytes is UB. Before this every such call havocked every
            // `&mut self` field, so a `self.i += w.len()` guarded by
            // `self.b.len() >= self.i + w.len()` was refuted across the `len` calls.
            //
            // Trust (TINV-18 correction, 2026-10-06): "a callee writes caller memory
            // only through its arguments" is FALSE for memory the caller reaches
            // through a raw pointer (a callee handed it `&raw mut G` and a later one
            // writes `G`), and for a local whose `&mut` an EARLIER call received (a
            // safe-signatured callee may stash it in a global inside an `unsafe`
            // block; nothing ends that stash's validity before a later call writes
            // through it). Both held for nullary and scalar-argument calls long before
            // TINV-18, which widened them to every lane. So the arm no longer havocs
            // NOTHING: it havocs [`escape_havoc`] — the whole-function list except
            // the names rooted at a protected, pointer-free, `Unpin` `&mut` PARAMETER
            // that never leaves the body (the coarse rule that replaced a
            // fine-grained exposure analysis after three review rounds each found a
            // channel it missed). A constant argument must be a pointer-free value
            // ([`const_is_pure_value`]), and the foreign / `unsafe`-signature / atomic
            // fences now close the WHOLE arm, not only its shared-reference half.
            let fenced = !*is_foreign && !*is_unsafe_sig && atomic.is_none();
            let args_cannot_reach_locals = fenced
                && args
                    .iter()
                    .all(|a| arg_hands_no_pointer(func, a) || arg_grants_no_write(func, a, fenced))
                && !func_has_writable_pointer_laundering(func);
            if args_cannot_reach_locals {
                let mut extra = Vec::new();
                dest_term_extras(func, dest, place_to_var_name(func, dest), &mut extra);
                return TermDefs { havoc: escape_havoc_at(func, block), extra };
            }
            // The callee may write its destination AND mutate any local whose
            // mutable reference escapes into it (`f(&mut x)` / `f(&raw mut x)`).
            // soundness (round-11): havocing only the dest left a stale
            // pre-call fact (`x == 5`) live across `f(&mut x)`, vacuously
            // discharging a real overflow on the post-call value. Conservatively
            // havoc every mutably-borrowed local at each Call (dropping a fact only
            // turns PROVE -> FAIL, so it is sound; per-argument PLACE-level
            // points-to (disjoint `&mut` args) is a further completeness
            // refinement. The `UnsafeCell` bytes a SHARED reference or borrow
            // reaches are named beside this list at every call
            // (`stored_ref_pointee_names`, INTERIOR-MUT-CHANNEL-1, 2026-10-14).
            // Trust #soundness (round-12/13): the list also havocs every local whose
            // type TRANSITIVELY contains a mutable reference / raw pointer — a `&mut`/
            // `*mut` PARAMETER, a pointer RETURNED from a call, or one NESTED in an
            // aggregate (`struct Wrapper { p: &mut u32 }`, a tuple/array/closure
            // capture, …). None have a syntactic `&mut x` statement, and the nested
            // case is not even a pointer at the local's top level, so
            // mutably_borrowed_local_names misses them. The callee can mutate the
            // pointee, so we havoc the local's BASE name — its prefix-overlap kills
            // the pointer, its pointee `s*`, and any nested pointee `s.f*`.
            // The refinements below are computed as a DELTA over that list
            // (`HavocDelta`), so a call costs O(its arguments), not O(the list).
            let havoc_set = function_havoc_set(func);
            let in_h = |n: &str| havoc_set.contains(n);
            // Trust (BLOCKER 2 — opaque callee effect summaries): the alias list
            // above is a WHOLE-FUNCTION over-approximation by BASE LOCAL name, so
            // for a `&mut self` method it is the single name `self` — a projection
            // ANCESTOR of every field spelling. One call to ANY helper therefore
            // erased every field fact the body established, which is why no method
            // that calls anything could discharge a `&mut self` postcondition (the
            // visible `SpecUnverifiable` row). When the callee's OWN extracted MIR
            // is available and falls inside the modeled fragment, replace this
            // call's argument roots with the precise caller-side spellings of the
            // paths the callee actually writes; every other alias name is retained
            // verbatim. `None` (no body, outside the fragment, unresolvable
            // argument shape, caller admits raw-pointer aliasing) keeps the
            // conservative list unchanged. See `callee_write_set` for the full
            // soundness discipline — the write-set is DERIVED from MIR, never
            // declared, and is total-and-fail-closed over statements/terminators.
            let call = callee_write_set::refine_call_havoc_delta(func, callee, args, &in_h);
            // Trust (2026-09-24, TRUST-10): a `&mut` local whose SHARED reborrow is
            // this call's argument (`self.check()` in a `&mut self` method) keeps the
            // facts about its frozen scalar fields — the argument's protection makes
            // any write to them undefined behaviour. Every other name under it, and
            // every other conservative name, is still havoced. See
            // `callee_write_set::refine_shared_reborrow_havoc`.
            let reborrow = callee_write_set::refine_shared_reborrow_havoc(
                func,
                args,
                *is_foreign,
                *is_unsafe_sig,
                atomic.is_some(),
                &|name: &str, steps: &[callee_write_set::ReborrowStep]| {
                    refined_list_contains(name, &in_h, call.as_ref(), steps)
                },
            );
            // Trust (ENC-DEFECTS 13b, 2026-09-26): a `&mut` root whose WHOLE
            // pointee this call receives only as a protected SHARED reborrow of a
            // pure, `Freeze` type cannot be written during the call — see
            // [`frozen_shared_reborrow_roots`] for the aliasing premise and every
            // gate (docs/TCB.md, "Shared-reborrow immutability across a call").
            // Every OTHER name stays: this narrows exactly the named roots and
            // nothing else, and only when every argument is either a pure value or
            // such a reborrow. A FOREIGN callee is excluded: code on the far side of
            // an FFI boundary is outside the aliasing model the premise rests on.
            //
            // Salvage reconciliation (2026-09-28): this runs AFTER the TRUST-10
            // sibling above, which rests on the same protector premise but spares
            // only the scalar leaves it reaches through struct fields and replaces
            // the root's base name with the names of everything else under it.
            // Where the sibling has fired the base name is gone and this removal
            // (exact names only) is a no-op, so the sibling's finer answer stands;
            // this narrowing only acts where the sibling declined — a pure,
            // `Freeze` pointee with no scalar leaf on a struct-field path (an enum,
            // an array, a tuple, a float). The `unsafe`-signature and atomic-callee
            // fences are the sibling's, taken over fail-closed so the two agree on
            // which calls the premise may be applied to at all.
            //
            // In the DELTA representation (rebased onto WS-E, 2026-09-28) each
            // protected root is one more trailing step `(root, [])`: drop that exact
            // name, append nothing — `HavocDelta::flatten`'s `retain` and
            // `refined_list_contains`'s last-step-decides rule both give exactly
            // the `names.retain(|n| !protected.contains(n))` this used to apply to
            // the refined list. Sorted, so the delta is deterministic.
            let mut frozen: Vec<callee_write_set::ReborrowStep> = Vec::new();
            if !*is_foreign
                && !*is_unsafe_sig
                && atomic.is_none()
                && let Some(protected) = frozen_shared_reborrow_roots(func, args)
            {
                let mut protected: Vec<String> = protected.into_iter().collect();
                protected.sort_unstable();
                frozen.extend(protected.into_iter().map(|root| (root, Vec::new())));
            }
            // Trust #soundness (LANE): the callee writes `dest` whether or not it
            // is a projection. A WHOLE-local dest (`lo = make()`) and a PROJECTED
            // dest (`s.0 = make()`, `s.field = make()`) both invalidate any
            // pre-call fact about that place. Pushing the dest's name
            // unconditionally lets `place_names_overlap` kill the matching child
            // fact (`s.0 == V`) AND — via prefix-overlap — any ancestor/descendant
            // fact (`s == V`, `s.0.1 == V`). Restricting the kill to whole-local
            // dests stranded a stale `s.0 == V` across `s.0 = make()`, which then
            // vacuously discharged a real overflow/assert on the post-call `s.0`
            // (a false-PROVE). Killing the dest name is monotone-sound (drops a
            // hypothesis: PROVE -> FAIL only, never the reverse).
            // Trust (P0 false proof — STALE LENGTH TIE): the callee writes a whole
            // new value into `dest`, so a slice-typed `dest` gets new length
            // metadata. See `extend_with_derived_slice_len`.
            // Trust: 2026-09-16 (round A9) — and a whole-local dest that is used as
            // an INDEX elsewhere rebinds every `..[_dest]..` name (see
            // `write_covers_index_segment`).
            let mut extra = Vec::new();
            dest_term_extras(func, dest, place_to_var_name(func, dest), &mut extra);
            let havoc = if call.is_none() && reborrow.is_none() && frozen.is_empty() {
                TermHavoc::Function
            } else {
                let mut steps = reborrow.unwrap_or_default();
                steps.extend(frozen);
                TermHavoc::Refined(std::rc::Rc::new(HavocDelta { call, reborrow: steps }))
            };
            TermDefs { havoc, extra }
        }
        // Trust #soundness (callee-write false-accept sweep): DROP GLUE RUNS
        // ARBITRARY USER CODE with `&mut` access to the dropped place and to
        // anything mut-reachable from it (`impl Drop { fn drop(&mut self) }` — a
        // stored `&mut u32` field can be written through). Confirmed live false
        // proof: a `Drop` impl setting `*self.r = u32::MAX` between a guard read
        // and an arithmetic use was PROVED (lane-level) because this registry
        // returned `Vec::new()` for `Drop`, so no fact was killed / no version
        // minted. Havoc exactly like a Call: every mutably-borrowed local, every
        // mut-pointer-carrying local, the dropped place itself, and its
        // deref-extension (the pointee spelling a `Box`/ref drop mutates).
        Terminator::Drop { place, .. } => {
            let mut dp = place.clone();
            dp.projections.push(trust_types::Projection::Deref);
            TermDefs {
                havoc: TermHavoc::Function,
                extra: vec![
                    TermExtra::Push(place_to_var_name(func, place)),
                    TermExtra::Push(place_to_var_name(func, &dp)),
                ],
            }
        }
        // Trust #soundness (same sweep): an `Opaque` terminator (Yield /
        // InlineAsm / unlowered constructs that preserve successors) can run
        // arbitrary code — the same conservative MEMORY havoc as a Call. Its
        // destinations (asm outputs, a resume place, a dropped call `dest`) are
        // not here: the extraction did not keep them, so
        // `terminator_def_names_structured` adds every local (H3, 2026-10-08).
        // Dropping facts is monotone-sound.
        Terminator::Opaque { .. } => TermDefs { havoc: TermHavoc::Function, extra: Vec::new() },
        _ => TermDefs { havoc: TermHavoc::None, extra: Vec::new() },
    }
}

/// [`mutably_borrowed_local_names`] plus, for each root, the DERIVED slice-length
/// name that reseating it invalidates.
///
/// Trust (P0 false proof — STALE LENGTH TIE). Code that receives `&mut s` may store
/// a whole new fat pointer into `s`, not merely write through the old one, which
/// changes `s__slice_len`. That derived name is not reached by `place_names_overlap`
/// from the base name (`_` is not a projection separator), so an array→slice tie
/// minted earlier in the function survived the call and certified-PROVED an
/// out-of-bounds index (`q6_mut_reseat` in `tests/array_unsize_slice_len.rs`).
///
/// All three arbitrary-code terminators (`Call`, `Drop`, `Opaque`) share this one
/// helper so the reseat channel cannot be closed on one and left open on another.
/// `refine_call_havoc_delta` drops only names EQUAL to a replaceable root's base
/// name, so the derived names survive the refinement unchanged.
///
/// Scoped to the roots a SLOT-WRITE CHANNEL reaches ([`own_storage_write_borrow`]:
/// `&mut`, `&raw mut`, and `&raw const` of an owned place) —
/// `mutable_pointer_local_names` is deliberately NOT extended, for the reason
/// [`extend_with_derived_slice_len`] documents.
fn mutably_borrowed_havoc_names(func: &VerifiableFunction) -> Vec<String> {
    mutably_borrowed_havoc_names_from(func, mutably_borrowed_local_names(func))
}

/// [`mutably_borrowed_havoc_names`] over a given list of borrow-target names (the
/// whole [`mutably_borrowed_local_names`], or the part of it [`escape_havoc`] keeps).
fn mutably_borrowed_havoc_names_from(
    func: &VerifiableFunction,
    mut names: Vec<String>,
) -> Vec<String> {
    // Trust (VEC-AS-SLICE, 2026-09-25): an owned std `Vec` local (`Ty::Seq`, held BY
    // VALUE) is abstracted to ONE integer under its own name — its LENGTH (see
    // `guards::coll_len_var`); its elements are reached only through call results
    // (`index`/`index_mut`/`deref_mut` return fresh references) and never through a
    // name derived from it. When EVERY `&mut` borrow of it, over its whole alias
    // closure, is consumed solely as the receiver of std's `Index::index`/
    // `IndexMut::index_mut` or of `Vec`'s OWN `deref_mut`/`as_mut_slice`
    // (`!guards::local_mut_borrows_may_resize`), no call can change that length,
    // so havocing it at every call only killed true length facts — the
    // `to_vec`-then-`sort` idiom lost `v.len() == xs.len()` at the sort. A raw
    // borrow, a borrow handed to any other callee, a reborrow stored anywhere, or
    // an exhausted budget keeps the havoc. A `&mut Vec` REFERENCE is `Ty::Ref`, not
    // `Ty::Seq`, and is never exempted: a callee can resize through it.
    if !names.is_empty() {
        for decl in &func.body.locals {
            if matches!(decl.ty, Ty::Seq { .. }) {
                let seq_name = crate::local_var_name(func, decl);
                if names.iter().any(|n| n == &seq_name)
                    && !guards::local_mut_borrows_may_resize(func, decl.index)
                {
                    names.retain(|n| n != &seq_name);
                }
            }
        }
    }
    for i in 0..names.len() {
        let base = names[i].clone();
        push_derived_slice_len(&mut names, &base);
    }
    names
}

/// True if `ty` TRANSITIVELY contains a mutable reference or ANY raw pointer
/// (`&mut`/`*mut`/`*const`) — directly, or nested in a struct/tuple/array/slice
/// field or a closure/coroutine capture — that is NOT behind a shared reference.
/// A callee that receives a value of such a type can mutate the pointee through
/// that nested pointer, so the local's BASE name goes on the havoc list.
///
/// Shared `&` is not recursed into HERE, and that is a statement about the bytes
/// the reference covers, not about everything it reaches: those bytes are frozen
/// outside an `UnsafeCell` (the `UnsafeCell` bytes behind a shared reference are named
/// at their own places by [`stored_ref_pointee_names`], INTERIOR-MUT-CHANNEL-1),
/// and the callee handed the `&` cannot write through a `&mut` stored in them
/// (`& &mut T` yields `&T`). A pointer stored in them that this function never
/// retagged is another matter: a raw pointer is `Copy` (safe code reads it out of
/// `w.p`), and any code holding a copy of it — or a raw child of a stored `&mut` or
/// `Box`, derived before the call — writes its target with defined behaviour. So what
/// a shared reference reaches through such a pointer is havoced too, by the precise
/// names [`stored_ref_pointee_names`] mints (`w*.0*`; CALL-HAVOC-ESCAPE-2, at a call
/// and, on [`function_havoc_names`], at an opaque store) — never by the shared
/// reference's base name, which would also kill every frozen field fact. Until
/// 2026-09-30 nothing named it (the r8c union review's F2): `s[*w.p]` under
/// `*w.p < s.len()` stayed PROVED across `poke(w.p)`, kernel-rechecked on the
/// installed lane, for `w: &PW { p: *mut usize }`.
///
/// Trust #soundness (callee-write false-accept sweep): `*const` IS included — a
/// `*const T` with write provenance is a legal, defined mutation channel (cast to
/// `*mut` in the callee, or `UnsafeCell`-backed). Today raw-pointer derefs are
/// independently blanket-refuted, but the Box-deref precision work is actively
/// narrowing that lane; registering `*const` here means that work cannot silently
/// reopen the "callee writes through the pointer, guard transfers across the
/// call" hole. Cost is ~zero today (the blanket refutation already dominates).
pub(super) fn ty_contains_mut_pointer(ty: &Ty) -> bool {
    match ty {
        Ty::Ref { mutable: true, .. } | Ty::RawPtr { .. } => true,
        // Trust: piece #7a — descend into a const-generic array's element exactly
        // like a concrete `[T; N]`. SOUNDNESS-CRITICAL (same reason as
        // `ty_contains_raw_ptr`): drives conservative mut-pointer havoc.
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            ty_contains_mut_pointer(elem)
        }
        Ty::Tuple(elems) => elems.iter().any(ty_contains_mut_pointer),
        // Trust (review of `2628c2a847`, fail-closed): a std `Box` is a pointer whatever
        // its rendering; an ADT with neither a recorded field nor a recorded variant
        // (std zero-sized markers aside) may hide one; and an enum's variant payloads
        // count like fields.
        Ty::Adt { name, .. } if type_name_is_box(name) => true,
        Ty::Adt { name, fields, variants, .. } => {
            (fields.is_empty() && variants.is_empty() && !type_name_is_zero_sized_std_marker(name))
                || fields.iter().any(|(_, t)| ty_contains_mut_pointer(t))
                || variants.iter().any(|v| v.fields.iter().any(|(_, t)| ty_contains_mut_pointer(t)))
        }
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            upvars.iter().any(ty_contains_mut_pointer)
        }
        _ => false,
    }
}

/// Base names of all locals whose type TRANSITIVELY contains a mutable reference
/// or raw pointer (directly, or nested in an aggregate / capture). A callee that
/// receives such a local can mutate the pointee, so its facts must be havoced at
/// a Call. Returning the BASE local name kills — via prefix-overlap — the pointer
/// itself, its pointee `s*`, and any nested pointee `s.f*`. This covers a `&mut`/
/// `*mut` PARAMETER, a pointer RETURNED from a call, and a pointer nested in a
/// non-reference aggregate parameter (the case top-level-type inspection missed).
pub(crate) fn mutable_pointer_local_names(func: &VerifiableFunction) -> Vec<String> {
    // verifier-perf: a whole-locals walk minting every pointer-carrying local's
    // name, re-run for every Call terminator by `terminator_def_names` (once per
    // gen'd name per block inside `block_entry_versions`) and by every
    // `deref_store_havoc_names` probe. Pure function of `func.body`; computed
    // once per function per scope (`fn_memo`) and cloned out — callers extend
    // and refine the list, so they keep receiving an owned `Vec`.
    crate::fn_memo::mut_pointer_names(func, || mutable_pointer_local_names_uncached(func))
        .as_ref()
        .clone()
}

fn mutable_pointer_local_names_uncached(func: &VerifiableFunction) -> Vec<String> {
    mutable_pointer_local_names_where(func, &|_| true)
}

/// [`mutable_pointer_local_names`] restricted to the locals `keep` admits.
fn mutable_pointer_local_names_where(
    func: &VerifiableFunction,
    keep: &dyn Fn(usize) -> bool,
) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    let mut seen: FxHashSet<String> = FxHashSet::default();
    for (local, decl) in func.body.locals.iter().enumerate() {
        if keep(local) && ty_contains_mut_pointer(&decl.ty) {
            let name = place_to_var_name(func, &trust_types::Place::local(local));
            if seen.insert(name.clone()) {
                names.push(name);
            }
        }
    }
    names
}

/// Whether a value of type `ty`, met at a place that is (`behind_deref`) or is not
/// behind a `Deref`, holds a pointer this function never RETAGGED: a raw pointer
/// anywhere, or a `&mut` / `Box` stored behind a reference (reached through a
/// `Deref`). A raw pointer is never retagged, and a `&mut` or `Box` STORED in memory
/// is not retagged when this function reads through it either (a retag happens at
/// function entry to the arguments themselves, at a call's return, and at a reborrow;
/// never to a pointer that sits in a pointee). Any code holding a copy of such a
/// pointer, or a raw child derived from it, can write its target with defined
/// behaviour under Stacked Borrows and Tree Borrows alike. A SHARED reference stored
/// in memory is not on the list (a write through it to `Freeze` bytes is UB; its
/// `UnsafeCell` bytes are named by [`stored_ref_pointee_names`]), and neither is a reference or
/// `Box` a local holds DIRECTLY (retagged, and protected at entry for an argument).
///
/// Asked by `callee_write_set`'s two refusals (the callee-formal check and the
/// replaceable-root check): a receiver whose pointee stores such a pointer keeps its
/// base-name havoc at a call. The names such a pointer can write are havocked at
/// every call, drop and opaque terminator, and at every opaque store, by
/// [`stored_ref_pointee_names`] (CALL-HAVOC-ESCAPE-2, on [`function_havoc_names`]), the
/// one statement of that rule.
///
/// Trust (2026-09-30, the r8c union review's F2). Until then
/// [`ty_contains_mut_pointer`], which does not recurse through `&` (right for the
/// bytes the reference covers), was the refusals' question, so a receiver
/// `x: &mut S { r: &PW }` with `PW { p: *mut usize }` was a replaceable root.
pub(crate) fn ty_reaches_unretagged_pointer(ty: &Ty, behind_deref: bool) -> bool {
    match ty {
        Ty::RawPtr { .. } => true,
        Ty::Ref { mutable: true, .. } if behind_deref => true,
        Ty::Ref { inner, .. } => ty_reaches_unretagged_pointer(inner, true),
        Ty::Adt { name, .. } if type_name_is_box(name) => {
            behind_deref || box_pointee(ty).is_none_or(|t| ty_reaches_unretagged_pointer(t, true))
        }
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            ty_reaches_unretagged_pointer(elem, behind_deref)
        }
        Ty::Tuple(elems) => elems.iter().any(|t| ty_reaches_unretagged_pointer(t, behind_deref)),
        Ty::Adt { fields, variants, .. } => {
            fields.iter().any(|(_, t)| ty_reaches_unretagged_pointer(t, behind_deref))
                || variants.iter().any(|v| {
                    v.fields.iter().any(|(_, t)| ty_reaches_unretagged_pointer(t, behind_deref))
                })
        }
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            upvars.iter().any(|t| ty_reaches_unretagged_pointer(t, behind_deref))
        }
        _ => false,
    }
}

/// The pointee type of a `Box` the extractor rendered with its fields
/// (`Box { 0: Unique { pointer: NonNull { pointer: *const T } }, 1: A }`): the target
/// of the first raw pointer on its field-0 chain. `None` when that chain is not
/// there (a `Box` rendered without fields), which every caller reads fail-closed.
fn box_pointee(ty: &Ty) -> Option<&Ty> {
    let mut cur = ty;
    for _ in 0..8 {
        match cur {
            Ty::RawPtr { pointee, .. } => return Some(pointee),
            Ty::Adt { fields, .. } => cur = &fields.first()?.1,
            _ => return None,
        }
    }
    None
}

/// Every local whose MUTABLE reference (`&mut x`, `&raw mut x`, or a `&raw const x` of
/// its own storage — [`own_storage_write_borrow`]) is taken anywhere in `func`. Such a
/// local may be mutated through that reference by a callee, so its accumulated
/// equality/value facts must be havoced across any `Call`.
pub(crate) fn mutably_borrowed_local_names(func: &VerifiableFunction) -> Vec<String> {
    // verifier-perf: same treatment as `mutable_pointer_local_names` — a
    // whole-body walk re-run per Call terminator and per havoc probe, memoized
    // per function per scope (`fn_memo`) and cloned out.
    crate::fn_memo::mut_borrowed_names(func, || mutably_borrowed_local_names_uncached(func))
        .as_ref()
        .clone()
}

fn mutably_borrowed_local_names_uncached(func: &VerifiableFunction) -> Vec<String> {
    mutably_borrowed_local_names_where(func, &|_| true)
}

/// [`mutably_borrowed_local_names`] restricted to borrows whose target is rooted at a
/// local `keep` admits.
fn mutably_borrowed_local_names_where(
    func: &VerifiableFunction,
    keep: &dyn Fn(usize) -> bool,
) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    let mut seen: FxHashSet<String> = FxHashSet::default();
    let mut index_locals: Option<IndexLocals> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            // Trust: 2026-10-08 (H2 RAW-CONST-STORE) — `&raw const k` of the body's own
            // storage is a write channel too ([`own_storage_write_borrow`]): a store
            // through it cast to `*mut` is opaque, and this list is that store's havoc.
            let Some(target) = own_storage_write_borrow(func, rvalue) else { continue };
            if !keep(target.local) {
                continue;
            }
            let name = place_to_var_name(func, target);
            if seen.insert(name.clone()) {
                names.push(name);
            }
            // Trust: 2026-10-12 (UNION-SIBLING-WRITE-2) — a pointer into a union field
            // writes every overlapping sibling: `&mut u.b` handed to `set(r, v)`, or
            // stored through after it reached a pointer the fold cannot resolve (a
            // two-referent `&mut`), rewrites `u.a`'s bytes. The borrowed place's name
            // `u.1` rebinds no sibling; its union cover `u` rebinds them all
            // ([`union_write_cover_name`], the cover every destination already carries).
            // MEASURED on the stage 1 of `0f03df468d` without it:
            // `u.a = 5; set(&mut u.b, n); u.a + (usize::MAX - 5)` elided its overflow
            // check (the binary printed 1 where rustc panics), and the two-referent
            // store's `overflow:add` row was PROVED.
            if let Some(cover) = union_write_cover_name(func, target)
                && seen.insert(cover.clone())
            {
                names.push(cover);
            }
            // Trust: 2026-09-16 (round A9) — a callee holding `&mut j` can reseat an
            // INDEX local; the names that embed `j` by number (`s*[_j]`) are havoced
            // through the fallback exactly as `j` itself is.
            if target.projections.is_empty()
                && index_locals.get_or_insert_with(|| IndexLocals::of(func)).contains(target.local)
            {
                let fallback = local_fallback_name(target.local);
                if seen.insert(fallback.clone()) {
                    names.push(fallback);
                }
            }
        }
    }
    names
}

/// Trust: 2026-10-11 (LAUNDERED-ALIAS-STORE, LAUNDERED-ALIAS-ELIDE-1) — THE ONE
/// QUESTION every gen-set and kill oracle asks of an `Assign` to `place`: does the write
/// havoc the whole-function list ([`function_havoc_names`])? Two kinds of write do.
///
///  * An OPAQUE deref store (`*p = v` whose `p` the referent fold cannot resolve,
///    `crate::deref_store_is_opaque`): it is spelled `p*`, a name no read of the real
///    referent gets, so the havoc versions every possible referent (the escaped locals
///    by name, every pointer-carrying local's pointee by its base name). Unchanged.
///  * ITS SYMMETRIC HALF: a write whose own, folded name lands in storage whose
///    address was taken ([`laundered_alias_roots`]) in a body that holds a pointer the
///    fold cannot resolve and through which a read after that write is defined. The
///    write is spelled by the storage's own name (`len`), a read through the
///    unresolved copy by `q*`, and nothing in the name algebra relates the two: until
///    this arm, `*q` read before and after the write shared one version. Measured
///    2026-10-11 on the stage 1 of `1213387e6d`: `let p = &raw mut len; let q = p as
///    *const usize; let x = *q; *p = n; if *q > 7 { return 0 } x + 1` proved the `x + 1`
///    row, kernel-certified, and the advisory lane elided its overflow check (the
///    binary returned 0 where rustc panics); so did `cast_const()`, `wrapping_add(0)`,
///    an opaque `launder(p)` and a DIRECT `len = n` in place of `*p = n`. Havocking the
///    whole list at the write versions `q` (a pointer-carrying local, which rebinds
///    `q*` by prefix), exactly as an opaque store through `q` versions `len`.
///
/// ONE predicate, so the retired per-statement oracle (`stmt_writes_name`,
/// `writes_until`, `block_written_names`, the kills) and the indexed one
/// (`block_writes::BlockWrites::build`) agree by construction. MONOTONE: every write
/// the previous test (a leading `Deref` and `deref_store_is_opaque`) accepted is still
/// accepted; the new arm only ADDS havoc, which drops hypotheses (it can cost a proof,
/// never grant one). Its cost is the whole list, not only the unresolved pointers'
/// names: a write into one escaped local also re-versions the others. That is the
/// indexed oracle's one symbolic havoc shape (`HMode`); a narrower list is a precision
/// follow-up, not a soundness one. `SetDiscriminant` / `Deinit` of escaped storage
/// are not routed here (their arms never carried the opaque-store havoc either).
pub(crate) fn write_havocs_function_list(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> bool {
    if matches!(place.projections.first(), Some(trust_types::Projection::Deref))
        && crate::deref_store_is_opaque(func, place)
    {
        return true;
    }
    let roots = laundered_alias_roots(func);
    if roots.is_empty() {
        return false;
    }
    let written = place_to_var_name(func, place);
    roots.iter().any(|root| place_names_overlap(root, &written))
}

/// The whole-local names of every local whose storage a pointer may reach — the ROOT
/// of every place a write-capable borrow takes ([`borrow_write_target`]: `&mut`,
/// `&raw mut`, `&raw const` short of a read-only one; a borrow behind a `Deref` counts
/// for the pointer it goes through, `(*s)` for `s`) — or NOTHING when no read through
/// an unresolved pointer can observe a write to them
/// ([`body_has_unresolved_unretagged_pointer`]). Computed once per function.
///
/// The root, not the borrowed place: `&raw mut s.0` hands out a pointer whose
/// provenance under Tree Borrows is the whole local, so a write to `s.1` is a write
/// the pointer can see. Wider is the fail-closed direction here (more writes havoc).
///
/// Trust: 2026-10-12 (LAUNDERED-ALIAS-CELL-1, the wave-24 review) — AND the root of
/// every SHARED borrow of interior-mutable storage ([`interior_mutable_shared_borrow`]).
/// `Cell::as_ptr(&c)` (and `UnsafeCell::get`, `AtomicUsize::as_ptr`, `RefCell::as_ptr`)
/// takes `&c`, a `Rvalue::Ref { mutable: false }` that [`borrow_write_target`] rightly
/// does not count as a write channel, and hands back a raw pointer to `c`'s bytes. So
/// `let q = c.as_ptr(); let x = *q; c = nc; if *q > 7 { return 0 } x + 1` rooted
/// nothing, the direct write `c = nc` havocked nothing, both reads of `*q` shared one
/// version, and on the stage 1 of `51eac007f3` the `x + 1` row was kernel-certified and
/// the advisory lane elided its overflow check (`elided 1`; the binary printed `0`
/// where rustc panics; `tests/ui/trust/laundered_alias_overflow_elide_run.rs`
/// `cell_direct`). The read through `q` after the direct write is defined under Tree
/// Borrows (a foreign write to a `Cell`-permission tag), the validity class of `al12`.
/// A shared borrow of `Freeze` data is not rooted: a write to it while a pointer
/// derived from the borrow is read is UB under both models.
pub(crate) fn laundered_alias_roots(func: &VerifiableFunction) -> std::rc::Rc<Vec<String>> {
    crate::fn_memo::laundered_alias_roots(func, || {
        let mut roots: Vec<usize> = Vec::new();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { rvalue, .. } = stmt else { continue };
                if let Some(target) = borrow_write_target(func, rvalue)
                    .or_else(|| interior_mutable_shared_borrow(func, rvalue))
                    && !roots.contains(&target.local)
                {
                    roots.push(target.local);
                }
            }
        }
        if roots.is_empty() || !body_has_unresolved_unretagged_pointer(func) {
            return Vec::new();
        }
        let mut names: Vec<String> = Vec::new();
        for local in roots {
            let name = place_to_var_name(func, &trust_types::Place::local(local));
            if !names.contains(&name) {
                names.push(name);
            }
        }
        names
    })
}

/// Trust: 2026-10-12 (LAUNDERED-ALIAS-CELL-1) — the place a SHARED borrow
/// (`Rvalue::Ref { mutable: false }`) takes, when that place's type may hold an
/// `UnsafeCell` at an inline position ([`ty_may_hold_inline_unsafe_cell`]): the bytes a
/// pointer derived from the borrow may write, so a write to the borrowed storage is
/// visible through it. `None` for every other rvalue, and for a shared borrow of
/// `Freeze` data. A place whose type cannot be resolved answers `Some` (fail-closed).
///
/// Only [`laundered_alias_roots`] asks this. A `&raw const` is not asked: every one
/// that is not [`addr_of_is_read_only`] (pointer-free `Freeze` data behind a shared
/// reference) already counts through [`borrow_write_target`].
fn interior_mutable_shared_borrow<'a>(
    func: &VerifiableFunction,
    rvalue: &'a Rvalue,
) -> Option<&'a trust_types::Place> {
    let Rvalue::Ref { mutable: false, place } = rvalue else { return None };
    let may_hold = crate::place_ty_cow(func, place).is_none_or(|ty| {
        ty_may_hold_inline_unsafe_cell(
            &func.body.datatype_defs,
            &ty,
            &mut Vec::new(),
            UNRETAGGED_POINTER_TY_FUEL,
        )
    });
    may_hold.then_some(place)
}

#[cfg(test)]
pub(crate) use trust_types::interior_mutability::ty_may_hold_named_unsafe_cell;
pub(crate) use trust_types::interior_mutability::{
    shared_borrow_cell_places, ty_may_hold_inline_unsafe_cell, ty_may_hold_unsafe_cell,
    unsafe_cell_places,
};

/// Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1) — every `UnsafeCell` sub-place of `local`'s
/// OWN storage that a shared borrow in `func` covers ([`shared_borrow_cell_places`], over
/// every statement). Empty for a local no shared borrow of a cell reaches — every local
/// of a body without interior mutability. Computed once per function.
///
/// THE ONE STATEMENT of the slot half, asked by the havoc list
/// ([`stored_ref_pointee_names`]: these places are havocked at every call, drop and opaque
/// terminator, and at every opaque store) and by the stability scans of a local's own
/// storage (`crate::place_source_is_stable`, `crate::place_is_body_stable`,
/// `local_versions_collapse_to_bare`, `crate::stmt_escapes_local`).
pub(crate) fn shared_borrowed_cell_places(
    func: &VerifiableFunction,
    local: usize,
) -> std::rc::Rc<Vec<trust_types::Place>> {
    let map = crate::fn_memo::shared_cell_borrows(func, || {
        let mut map: FxHashMap<usize, std::rc::Rc<Vec<trust_types::Place>>> = FxHashMap::default();
        let mut acc: FxHashMap<usize, Vec<trust_types::Place>> = FxHashMap::default();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                if let Some((root, cells)) = shared_borrow_cell_places(&func.body, stmt) {
                    let entry = acc.entry(root).or_default();
                    for cell in cells {
                        if !entry.contains(&cell) {
                            entry.push(cell);
                        }
                    }
                }
            }
        }
        for (root, cells) in acc {
            map.insert(root, std::rc::Rc::new(cells));
        }
        map
    });
    map.get(&local).cloned().unwrap_or_default()
}

/// Whether some local of `func` may hold a pointer that is NOT retagged where the body
/// reads through it ([`ty_may_reach_unretagged_pointer`]: a raw pointer anywhere in its
/// value, a `&mut` or `Box` stored behind a reference, or a part whose layout is not
/// recorded) AND whose deref the referent fold does not resolve
/// (`crate::deref_pointer_is_opaque`; always true for an aggregate local, which has no
/// referent of its own).
///
/// Why only such pointers: a read through a RETAGGED reference (`&T`, `&mut T` held
/// directly, a `Box`) after a write to its referent through any other pointer is
/// undefined behaviour under Stacked Borrows and Tree Borrows alike (the foreign write
/// pops / disables the reference), so its stale version describes no execution. A raw
/// pointer is never retagged: `q = p as *const usize`, `p.cast_const()`,
/// `p.wrapping_add(0)` and `launder(p)` all carry `p`'s tag, and a read through `q`
/// after a write through `p` (or to `len` itself, under Tree Borrows) is defined.
fn body_has_unresolved_unretagged_pointer(func: &VerifiableFunction) -> bool {
    func.body.locals.iter().any(|decl| {
        ty_may_reach_unretagged_pointer(
            &func.body.datatype_defs,
            &decl.ty,
            false,
            &mut Vec::new(),
            UNRETAGGED_POINTER_TY_FUEL,
        ) && crate::deref_pointer_is_opaque(func, decl.index)
    })
}

/// Depth bound of [`ty_may_reach_unretagged_pointer`]; running out answers `true`.
const UNRETAGGED_POINTER_TY_FUEL: u32 = 64;

/// [`ty_reaches_unretagged_pointer`], FAIL-CLOSED on every part whose layout is not
/// recorded: an ADT with neither a recorded field nor a recorded variant (a std
/// zero-sized marker aside, the clause [`ty_contains_mut_pointer`] carries), a by-name
/// datatype marker the body's table does not define, an unsupported type, and a type
/// deeper than the fuel. A marker already being walked (in the same `behind_deref`
/// position) answers `false` for the cycle, which adds no new part.
fn ty_may_reach_unretagged_pointer<'a>(
    defs: &'a trust_types::DatatypeDefs,
    ty: &'a Ty,
    behind_deref: bool,
    seen: &mut Vec<(&'a str, bool)>,
    fuel: u32,
) -> bool {
    let Some(fuel) = fuel.checked_sub(1) else {
        return true;
    };
    match ty {
        Ty::RawPtr { .. } => true,
        Ty::Ref { mutable: true, .. } if behind_deref => true,
        Ty::Ref { inner, .. } => ty_may_reach_unretagged_pointer(defs, inner, true, seen, fuel),
        Ty::Adt { name, .. } if type_name_is_box(name) => {
            behind_deref
                || box_pointee(ty)
                    .is_none_or(|t| ty_may_reach_unretagged_pointer(defs, t, true, seen, fuel))
        }
        Ty::Adt { name, fields, variants, .. } => {
            (fields.is_empty() && variants.is_empty() && !type_name_is_zero_sized_std_marker(name))
                || fields.iter().any(|(_, t)| {
                    ty_may_reach_unretagged_pointer(defs, t, behind_deref, seen, fuel)
                })
                || variants.iter().any(|v| {
                    v.fields.iter().any(|(_, t)| {
                        ty_may_reach_unretagged_pointer(defs, t, behind_deref, seen, fuel)
                    })
                })
        }
        Ty::Datatype { name, variants } if variants.is_empty() => {
            let key = (name.as_str(), behind_deref);
            if seen.contains(&key) {
                return false;
            }
            seen.push(key);
            match trust_types::datatype_marker_definition(defs, ty) {
                Some(definition) => {
                    ty_may_reach_unretagged_pointer(defs, definition, behind_deref, seen, fuel)
                }
                None => true,
            }
        }
        Ty::Datatype { variants, .. } => variants.iter().any(|(_, fields)| {
            fields
                .iter()
                .any(|(_, t)| ty_may_reach_unretagged_pointer(defs, t, behind_deref, seen, fuel))
        }),
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            ty_may_reach_unretagged_pointer(defs, elem, behind_deref, seen, fuel)
        }
        Ty::Tuple(elems) => {
            elems.iter().any(|t| ty_may_reach_unretagged_pointer(defs, t, behind_deref, seen, fuel))
        }
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => upvars
            .iter()
            .any(|t| ty_may_reach_unretagged_pointer(defs, t, behind_deref, seen, fuel)),
        Ty::Unsupported { .. } => true,
        _ => false,
    }
}

/// Extra SMT names a block REDEFINES that the statement-def scan cannot see: the
/// referent of a non-canonicalizable deref-store `*p = v`.
///
/// Trust #soundness: a store through a pointer `p` that does NOT resolve to a
/// unique referent — reseated / multiply-`&mut`-borrowed (`p = &mut x` more than
/// once), a pointer PARAMETER, or a call-returned pointer — leaves `canonicalize_deref`
/// unable to fold `*p -> x`, so `place_to_var_name(*p)` is the opaque `p*`. The
/// store then emits a def about `p*`, which `place_names_overlap` never matches
/// against the real referent `x`, so the mutation is INVISIBLE to the name-based
/// redef-kill and a fact about `x` (a guard `x <= K`, a block-def `x == v`, a
/// precondition) survives STALE — vacuously discharging a real obligation over the
/// post-store value (a confirmed false-PROVE: a reseated `*r = 4e9` left `x == 5`
/// live and proved `x + x` non-overflowing). The single-borrow case is already
/// folded (round-12, `unique_value_def` skips deref-stores), so this fires
/// ONLY for the genuinely-opaque case and keeps full precision otherwise.
///
/// Conservatively havoc every mutably-borrowed / mutable-pointer local — the exact
/// over-approximation `terminator_def_names` already applies at a `Call` (a callee
/// can mutate any `&mut` pointee) — so any fact about a possible referent is
/// dropped. Monotone-sound: dropping a hypothesis can only turn a PROVE into a
/// FAIL, never the reverse. Empty unless such a store exists.
///
/// Trust (P0 false proof — STALE LENGTH TIE through the DEREF-STORE channel). The
/// `&mut`-borrowed roots carry their DERIVED slice-length names here for the same
/// reason they do at a `Call` ([`mutably_borrowed_havoc_names`]): a store through a
/// pointer whose POINTEE IS THE SLICE REFERENCE ITSELF (`p: &mut &[T]`, `*p = t`)
/// RESEATS it and changes its length, which the base name alone does not reach
/// (`_` is not a projection separator). Without this the array→slice tie minted
/// before the store stayed live and certified-PROVED an out-of-bounds index on
/// bodies that panic at runtime — measured on the reborrow-reseat, int-to-ptr
/// reseat, struct-carried-pointer reseat, field-reseat and reseat-in-loop shapes.
///
/// A store through a pointer to an ELEMENT (`e: &mut T`, `*e = x`) preserves the
/// length, and havocing there is the false REFUTATION
/// `write_covers_derived_slice_len` exists to prevent. The two are separated here
/// by the SCOPE of the extension, not by the store's pointee type: only the roots
/// a slot-write channel reaches are extended ([`own_storage_write_borrow`]: `&mut`,
/// `&raw mut`, `&raw const` of an owned place), and a slice reference's SLOT cannot
/// be written through a pointer that none of those three minted — a write through a
/// pointer derived from a shared reference is UB under Stacked Borrows and Tree
/// Borrows alike. (`&raw const` joined the list on 2026-09-30; until then this
/// sentence said "`&mut`/`&raw mut`", and a reseat through `&raw const s as *mut _`
/// was a kernel-certified false proof.) `mutable_pointer_local_names` stays
/// unextended — those entries are
/// base locals whose own length metadata lives one projection down
/// (`p*__slice_len`, already an overlap of `p`), so extending them would only havoc
/// a `&mut [T]` local's live tie at every element store through an unrelated
/// opaque pointer. Measured: the element-store controls (`&mut T` through a
/// two-branch borrow, `v[i] = x`, a `&mut` element write in a loop, a raw-pointer
/// element store) all keep their proofs under this scoping. It holds only if the
/// KILL does not re-extend the list: `v2_path_def_fixpoint` retains against it with
/// [`formula_survives_havoc`], never the destination relation, whose derived-length
/// disjunct performed exactly that extension from 2026-08-26 to 2026-09-29.
///
/// verifier-perf: the returned list is a pure function of `func` ALONE — the
/// `block` argument only selects whether the (block-gated) havoc is in effect at
/// all. Both halves are therefore memoized per function by `havoc_memo`: the
/// list itself once per `func`, and the block gate once per block (keyed by the
/// block's statement-buffer address — see `havoc_memo::block_key`). Sharing the
/// list behind an `Rc` also keeps the hot `writes_until` path from cloning
/// O(locals) strings at every program point. See `havoc_memo`'s header for the
/// staleness argument; the values are byte-identical to the unmemoized ones.
pub(super) fn deref_store_havoc_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> std::rc::Rc<Vec<String>> {
    let has_opaque_deref_store = crate::havoc_memo::block_has_opaque_store(
        func,
        crate::havoc_memo::block_key(block),
        || {
            block.stmts.iter().any(|stmt| {
                let Statement::Assign { place, .. } = stmt else { return false };
                // Opaque ⟺ the pointer does not fold to a concrete referent — covers the
                // reseated/multi-borrow/param case AND a cast-laundered pointer
                // (`&mut x as *mut`, IntToPtr) whose def `resolve_referent` cannot fold.
                // `deref_store_is_opaque` is the strict, name-mint-consistent superset of
                // the old `crate::local_defs::unique_value_def(..).is_none()` check.
                // Asked on the WRITTEN PLACE (2026-09-18): the mint is a function of the
                // place, so a store with projections past the leading `Deref` must be
                // decided on its own spelling and not on the bare `*local`.
                // Trust: 2026-10-11 (LAUNDERED-ALIAS-STORE) — and a write into escaped
                // storage in a body that reads through an unresolved copy of a pointer
                // havocs the list too: the one predicate, `write_havocs_function_list`.
                write_havocs_function_list(func, place)
            })
        },
    );
    if !has_opaque_deref_store {
        return std::rc::Rc::new(Vec::new());
    }
    let full = function_havoc_names(func);
    // Trust (2026-10-08, D15 NOALIAS_MUT_ARGS): two `&mut` ARGUMENTS live for the
    // whole call never overlap (Rust's `noalias`), so a store through `*a` cannot
    // reach `*n`. Without this, `fn bump(a: &mut u32, n: &mut usize) { if *n < 8 {
    // *a = 1; *n += 1 } }` lost the guard on `*n` at `*a = 1` and false-refuted the
    // `*n += 1` overflow (ordinary-Rust sweep m04/m06/m07/m08/p26). It is a PREMISE
    // nothing here proves, so it applies only where the COMPILER installed it
    // (`noalias_mut_params_for`), which also demotes to `Trusted` every row whose VC
    // the premise-free generation does not reproduce byte-identically (per row since
    // 2026-10-17) and discloses it; any other caller of vcgen gets the full list.
    let installed = crate::noalias_mut_params_for(&func.def_path);
    if installed.is_empty() {
        return full;
    }
    let params = premise_params(func, &installed);
    match block_noalias_excluded_bases(func, block, &params) {
        Some(bases) => std::rc::Rc::new(
            full.iter()
                .filter(|h| !bases.iter().any(|b| place_names_overlap(h, b)))
                .cloned()
                .collect(),
        ),
        None => full,
    }
}

/// The installed premise parameters that also pass the structural gate.
fn premise_params(func: &VerifiableFunction, installed: &[usize]) -> Vec<usize> {
    noalias_mut_params(func).iter().copied().filter(|l| installed.contains(l)).collect()
}

/// The base names a store in `block` cannot reach under the premise over
/// `params`: the trees of the OTHER premise parameters, when EVERY opaque store in
/// the block goes through one of them (exactly one leading `Deref`). `None` when
/// any opaque store is outside the premise, or nothing would be excluded.
fn block_noalias_excluded_bases(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    params: &[usize],
) -> Option<Vec<String>> {
    let mut excluded: Option<Vec<String>> = None;
    for stmt in &block.stmts {
        let Statement::Assign { place, .. } = stmt else { continue };
        if !matches!(place.projections.first(), Some(trust_types::Projection::Deref))
            || !crate::deref_store_is_opaque(func, place)
        {
            continue;
        }
        let here = noalias_param_store_excludes(func, place, params);
        let next: Vec<String> = match excluded {
            None => here,
            Some(prev) => prev.into_iter().filter(|n| here.contains(n)).collect(),
        };
        if next.is_empty() {
            return None;
        }
        excluded = Some(next);
    }
    excluded
}

/// Would the D15 premise over the candidate `params` change any havoc list of
/// `func`? The compiler installs the premise (and demotes the body) only when it
/// would, so a body that cannot use it keeps its proofs byte-identical.
#[must_use]
pub fn noalias_premise_would_fire(func: &VerifiableFunction, candidates: &[usize]) -> bool {
    let params = premise_params(func, candidates);
    if params.len() < 2 {
        return false;
    }
    let full = function_havoc_names(func);
    func.body.blocks.iter().any(|block| {
        block_noalias_excluded_bases(func, block, &params).is_some_and(|bases| {
            full.iter().any(|h| bases.iter().any(|b| place_names_overlap(h, b)))
        })
    })
}

/// The `&mut` parameters the body never reseats (see [`is_noalias_mut_ref_param`]),
/// computed once per function. STRUCTURAL only: the premise also needs the
/// compiler's installation, intersected at each use.
fn noalias_mut_params(func: &VerifiableFunction) -> std::rc::Rc<Vec<usize>> {
    crate::fn_memo::noalias_mut_params(func, || {
        func.body
            .locals
            .iter()
            .map(|d| d.index)
            .filter(|&l| is_noalias_mut_ref_param(func, l))
            .collect()
    })
}

/// A `&mut` PARAMETER the body never reseats: not assigned as a whole, not the
/// destination of a call, and never borrowed as a whole local (so no `&mut a`
/// can rewrite it). Its pointee is a protected unique borrow for the whole call.
fn is_noalias_mut_ref_param(func: &VerifiableFunction, local: usize) -> bool {
    if !crate::local_defs::is_parameter(func, local) {
        return false;
    }
    if !matches!(crate::local_ty_ref(func, local), Some(Ty::Ref { mutable: true, .. })) {
        return false;
    }
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if place.local == local && place.projections.is_empty() {
                        return false;
                    }
                    if let Rvalue::Ref { place: target, .. } | Rvalue::AddressOf(_, target) = rvalue
                        && target.local == local
                        && target.projections.is_empty()
                    {
                        return false;
                    }
                }
                Statement::Deinit { place } if place.local == local => return false,
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == local
        {
            return false;
        }
    }
    true
}

/// For a store through `*a` (exactly ONE `Deref`, the leading one) where `a` is a
/// noalias `&mut` parameter: the base names of every OTHER noalias `&mut`
/// parameter, whose trees the store cannot reach. Empty otherwise.
fn noalias_param_store_excludes(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    params: &[usize],
) -> Vec<String> {
    let derefs =
        place.projections.iter().filter(|p| matches!(p, trust_types::Projection::Deref)).count();
    if derefs != 1 || !params.contains(&place.local) {
        return Vec::new();
    }
    params
        .iter()
        .copied()
        .filter(|&l| l != place.local)
        .map(|l| crate::place_to_var_name(func, &trust_types::Place::local(l)))
        .collect()
}

/// The whole-function conservative havoc list —
/// `mutably_borrowed_havoc_names(func) ++ mutable_pointer_local_names(func)`, plus
/// `stored_ref_pointee_names(func)` in a function with an opaque deref store — shared
/// behind an `Rc` and computed once per function. It is the havoc of a call, a `Drop`,
/// an opaque terminator AND an opaque deref store.
///
/// The third part is the memory behind every reference or pointer stored IN memory
/// (CALL-HAVOC-ESCAPE-2), which `terminator_def_names_structured` adds explicitly at
/// every call-like terminator (so a refined or escape-split call keeps it). On this
/// list it reaches the opaque store too; it is on the list only when the function HAS
/// an opaque deref store, so a function without one keeps the list (and every call's
/// havoc shape: an empty list is `TermHavoc::None`) the first two parts make it.
///
/// Trust (2026-10-08, the r8c union review's F2 on a store): a pointer read out of
/// memory this function reaches through a reference — `w.p` for
/// `w: &PW { p: *mut usize }` — was never retagged, so a store through anything derived
/// from it (`*(&raw const *w.p as *mut usize) = v`) is defined under both aliasing
/// models and writes `w*.0*`; an opaque store took only the first two parts, which
/// never name it. `let i = *w.p; if i < s.len() { *q = usize::MAX; s[*w.p] }` (`q`
/// that cast) kept `w*.0* < s.len()` across the store, and its `[slice]` row and
/// hardened twin were kernel-certified PROVED on the compiler's vcgen entry for a body
/// that panics (tests/data/shared_reach_pointer_havoc.rs
/// `shared_struct_raw_const_pointee`). The union first closed it with a second walk
/// of its own (`shared_reach_pointer_names`); one rule names that memory now. It is
/// on THIS list, not added beside it at the store, because the indexed version
/// oracle (`block_writes::FnWrites`) represents every opaque store's havoc as this
/// list `h`.
///
/// This is the SINGLE spelling of that union. It was previously open-coded at
/// four sites (`Call`, `Drop`, `Opaque` and the opaque-deref-store gate), which
/// made it four independently-forkable copies of one rule as well as four
/// whole-function rescans; routing them all through here keeps them equal by
/// construction.
///
/// `pub(crate)` (2026-10-02, trust-fixpoint-deadline) for the interval fixpoint's
/// call havoc (`abstract_interp::transfer::CallHavoc`), which indexes this list ONCE
/// per run and shares it among every terminator whose havoc is
/// [`TermHavoc::Function`].
pub(crate) fn function_havoc_names(func: &VerifiableFunction) -> std::rc::Rc<Vec<String>> {
    crate::havoc_memo::havoc_list(func, || {
        let mut names = mutably_borrowed_havoc_names(func);
        names.extend(mutable_pointer_local_names(func));
        // A stored-pointer name already under a listed name (`p*` beside a listed `p`)
        // adds no kill: the listed ancestor rebinds everything it does. Leaving it
        // off keeps the list (and the version oracle's rebinder trees) what the first
        // two parts make it wherever they already cover the memory.
        let covered = |n: &str, names: &[String]| {
            names.iter().any(|m| {
                n == m
                    || (n.len() > m.len()
                        && n.starts_with(m.as_str())
                        && crate::is_projection_segment_lead(n.as_bytes()[m.len()]))
            })
        };
        if func_has_opaque_deref_store(func) {
            for n in stored_ref_pointee_names(func).iter() {
                if !covered(n, &names) {
                    names.push(n.clone());
                }
            }
        }
        names
    })
}

/// Whether any statement of `func` is a write that havocs the whole-function list — an
/// OPAQUE deref store (`*p = v` through a pointer that does not fold to a concrete
/// referent) or, since 2026-10-11, a write into escaped storage that a laundered copy
/// of a pointer can read ([`write_havocs_function_list`]; [`deref_store_havoc_names`]'
/// per-block test, asked of every block).
fn func_has_opaque_deref_store(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().flat_map(|b| b.stmts.iter()).any(|stmt| {
        let Statement::Assign { place, .. } = stmt else { return false };
        write_havocs_function_list(func, place)
    })
}

/// [`function_havoc_names`] as a SET, for the membership questions the per-call
/// refinements ask (computed once per function, like the list).
pub(super) fn function_havoc_set(func: &VerifiableFunction) -> std::rc::Rc<FxHashSet<String>> {
    crate::havoc_memo::havoc_set(func, || function_havoc_names(func).iter().cloned().collect())
}

/// Append `new_defs` onto `defs`, first dropping any existing fact that *mentions*
/// a variable `new_defs` redefines. A path's accumulated facts must reflect each
/// variable's *live* value, and a fact is invalidated when any variable it
/// references is reassigned — not only when its own left-hand side is. Two ways
/// this matters:
///   * `x == v_old`, kept past a reassignment of `x`, survives the join
///     intersection in `v2_build_path_definition_map` and vacuously discharges a
///     VC over `x` — e.g. `s == 0`, established before `if c { s = 50; }`, masked
///     the merged value and false-PROVED an unguarded `s + b`.
///   * `c == (m < 1000)`, kept past a reassignment of `m` in a *later* block, lets
///     a downstream `if c { m + 1 }` carry the contradictory hypotheses
///     {c == true, c == (m < 1000), m == BIG} that vacuously discharge the
///     overflow — a false-PROVE of a real overflow. Keying the kill on the def's
///     left-hand side alone misses this, because the stale fact's lhs is `c`, not
///     the reassigned `m`.
/// Dropping a fact only ever removes a hypothesis, so it can introduce a
/// false-FAIL but never a false-PROVE.
pub(super) fn extend_killing_redefs(defs: &mut Vec<Formula>, new_defs: Vec<Formula>) {
    if new_defs.is_empty() {
        return;
    }
    if !defs.is_empty() {
        let mut redefined: FxHashSet<String> =
            new_defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
        extend_with_derived_slice_len(&mut redefined);
        if !redefined.is_empty() {
            let kill = KillSet::new(&redefined);
            defs.retain(|f| {
                // CHARGE the ambient budget per fact, but NEVER change the verdict:
                // this retain is a KILL, and keeping a fact the block invalidated is
                // the unsound direction (a stale hypothesis can vacuously discharge a
                // real violation — see `v2_live_path_defs`' doc). Charging is enough:
                // this runs inside `v2_path_def_fixpoint`'s loop, whose top-of-loop
                // poll then sees the exhausted budget and returns the sound empty
                // map, discarding this result. Measured 2026-09-09 as a co-leaf with
                // the fixpoint in the tla-cli hang (`formula_survives_redefs` walks
                // each fact's tree against every redefined name).
                let _ = trust_types::verify_budget::budget_exhausted();
                kill.survives(f)
            });
        }
    }
    defs.extend(new_defs);
}

/// Drop block-ENTRY facts that `block`'s own statements invalidate by reassigning
/// one of their free variables. `v2_build_path_definition_map` stores each block's
/// *entry* fact set; conjoining it verbatim onto a VC that sits *after* an
/// intra-block reassignment is unsound. A CheckedSub `hi - lo` leaves the entry
/// fact `lo == hi`; a block that then does `lo = big` and a second `hi - lo`
/// carries both `lo == hi` (entry) and the live in-block `lo == big`, which are
/// contradictory and vacuously discharge the real underflow. The VC formula
/// already embeds the block's live intra-block defs (via
/// `extract_block_definitions_until`), so the live value is never lost — dropping
/// the stale entry fact only removes a hypothesis, which is sound (it can turn a
/// PROVE into a FAIL, never the reverse). Safety obligations here are Assert
/// *terminator* VCs at block end, so every intra-block reassignment precedes
/// them and this whole-block kill is exact for that case.
pub(super) fn v2_live_path_defs(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    entry_defs: &[Formula],
) -> Vec<Formula> {
    if entry_defs.is_empty() {
        return Vec::new();
    }
    let sv = super::stmt_versions_for(func);
    // Trust (2026-11-08, MAIN-REDS-4): the writes table's kill
    // (`block_entry_kill_rebinds`) havocs the WHOLE-function list at an opaque store;
    // `deref_store_havoc_names`, which the uncached path reads, spares the other
    // `&mut` arguments when the compiler installed the D15 noalias premise. With the
    // premise installed the two differ, so take the uncached path: 03c7b3c1c7 took the
    // table's answer there and killed the guard on `*n` at `*a = 1`, so the premise
    // stopped shaping any row (`noalias_premise_shapes_only_the_row_that_reads_the_
    // spared_name`, ui `noalias_args/two_mut_args_guarded_update.rs`).
    if !sv.ssa.writes().built_after_trip()
        && !crate::noalias_premise_installed_for(&func.def_path)
        && func.body.blocks.get(block.id.0).is_some_and(|b| {
            b.id == block.id
                && std::ptr::eq(b.stmts.as_ptr(), block.stmts.as_ptr())
                && b.stmts.len() == block.stmts.len()
        })
    {
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if sv.has_legacy() && super::legacy_version_oracle::legacy_answers() {
            return v2_live_path_defs_uncached(func, block, entry_defs);
        }
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let expected = super::differential_enabled()
            .then(|| v2_live_path_defs_uncached(func, block, entry_defs));
        let out: Vec<Formula> = entry_defs
            .iter()
            .filter(|f| {
                formula_survives_redefs_by(f, &mut |name| {
                    sv.block_entry_kill_rebinds(block.id.0, name)
                })
            })
            .cloned()
            .collect();
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if let Some(expected) = expected {
            assert_eq!(out, expected, "v2_live_path_defs differential at {:?}", block.id);
        }
        return out;
    }
    v2_live_path_defs_uncached(func, block, entry_defs)
}

fn v2_live_path_defs_uncached(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    entry_defs: &[Formula],
) -> Vec<Formula> {
    let mut redefined = collect_block_extracted_def_names(func, block);
    // Extraction-declined destinations still invalidate entry facts — the write
    // must stay in the kill even where the def was refused (the unified write
    // oracle, see `extend_with_assigned_place_dests`).
    extend_with_assigned_place_dests(func, &block.stmts, &mut redefined);
    extend_with_derived_slice_len(&mut redefined);
    redefined.extend(deref_store_havoc_names(func, block).iter().cloned());
    if redefined.is_empty() {
        return entry_defs.to_vec();
    }
    let kill = KillSet::new(&redefined);
    entry_defs.iter().filter(|f| kill.survives(f)).cloned().collect()
}

/// [`v2_live_path_defs`] for a row whose use point is the MID-BLOCK statement
/// `point` (a per-statement `BinaryOp` / cast / negation row), not the block
/// terminal.
///
/// THE DEFECT THIS CLOSES (false refutation of valid Rust). `v2_live_path_defs`
/// kills an entry fact when ANY statement of the block writes one of its names —
/// exact for a terminator row, but a statement row reads its operands BEFORE the
/// later writes. The loop body of `while b != 0 { let t = b; b = a % b; a = t; }`
/// is `bb4: _8 = Rem(_4, _3); _5 = _3; _3 = _8; _4 = _5`, so the write `_3 = _8`
/// AFTER the remainder killed the entry facts `_6 == (_3 != 0)` (the loop guard)
/// and `_7 == (_3 == 0)` (the assert cond). The path guards `_6` / `!_7` are
/// conjoined later, exempt from the kill, so the row shipped them as FREE
/// booleans with no definition, and ay refuted `_3 == 0` with the infeasible
/// model `_6 = true, _3 = 0` (`nat_gcd`, clean-kernel). A dropped path condition
/// is not only a false refutation: it is the same loss that could hide a guard's
/// ABSENCE, so the repair restores the guard rather than dropping the row.
///
/// THE RULE. An entry fact is a statement about block-ENTRY values.
///  1. Kill it if it mentions a name written in `stmts[..point]` (plus every
///     opaque-deref-store havoc of the block, conservatively): there the live
///     value differs from the entry value. Kill-only, as in `v2_live_path_defs`.
///  2. Version the survivor AT `point` — for every name it still mentions the
///     value at `point` IS the entry value, so this is the same spelling the
///     row's own body read got from `v2_formula_with_block_defs_at_point_recorded`.
///  3. Belt and braces: kill a survivor carrying a WITHIN-block token
///     `s{block}_{j}`; such a spelling names a value this block writes.
///
/// A name still BARE after step 2 is SAFE to keep even when the block writes it
/// at or after `point`: the whole-row version rename
/// (`conjoin_preconditions_versioned_at_point_recorded`) runs at this SAME
/// `point` for the row, so the bare name stays bare and denotes the value read at
/// `point` — the pre-write value the fact is about — in the body and in the fact
/// alike. (Before 2026-09-17 that rename ran at the block TERMINAL for every row,
/// moved such a bare name to its POST-write token in the body, and this function
/// had to DROP the fact to stay sound, falsely refuting the row.) The rename and
/// this function MUST use the same point; `generate_v2_safety_vcs_impl_with_origins_checked`
/// passes both the one `row_points` entry.
///
/// Each kept fact is therefore a true equation over the version oracle's names
/// for the entry values, and a name-disjoint neighbour of every post-write read.
/// A `point` at or past the terminal is exactly `v2_live_path_defs`.
pub(super) fn v2_live_path_defs_at_point(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    entry_defs: &[Formula],
    point: usize,
) -> Vec<Formula> {
    if entry_defs.is_empty() {
        return Vec::new();
    }
    let terminal = block.stmts.len();
    if point >= terminal {
        return v2_live_path_defs(func, block, entry_defs);
    }
    // Step 1: the prefix kill, consistent with the version oracle at `point`.
    //
    // Trust: 2026-09-18 (merge) — this kill MUST be tested with the DIRECTIONAL
    // relation, WRITTEN name FIRST. `formula_survives_redefs` below supplies that
    // (`formula_mentions_redef` calls `dest_write_rebinds(written, read)`), and
    // `writes_until` supplies the other half: `extend_with_assigned_place_dests`
    // mints the index FALLBACK `_l` beside the canonical name for every whole-local
    // write of an index operand. The two together are what makes a prefix reseat of
    // an index local `_l` kill an entry fact about `s*[_l]`. Drop either — the
    // fallback mint, or the written-first argument order — and the prefix kill goes
    // silently blind to the reseat: the canonical name never reaches `s*[_l]`, and
    // the symmetric `place_names_overlap` alone does not carry the segment channel.
    // See `write_rebinds` for the relation and the measured false-PROVE behind it.
    //
    // The kill set is `writes_until(block, point)` plus the block's opaque-store havoc
    // list, PROBED per free variable through the statement write index
    // (`StmtVersionCtx::prefix_kill_rebinds`) instead of materialised: the prefix
    // set is a statement-PREFIX definition extraction, which the retired memo
    // recomputed per `(block, point)` up to a 400k-name cap.
    let block_havoc = !deref_store_havoc_names(func, block).is_empty();
    let within_block_prefix = format!("s{}_", block.id.0);
    let names_within_block_value = |f: &Formula| {
        trust_types::any_free_variable_name(f, &mut |v| {
            v.split_once('#').is_some_and(|(_, token)| {
                token
                    .strip_prefix(&within_block_prefix)
                    .is_some_and(|j| !j.is_empty() && j.bytes().all(|c| c.is_ascii_digit()))
            })
        })
    };
    let sv = super::stmt_versions_for(func);
    let mut kills = |name: &str| sv.prefix_kill_rebinds(func, block.id, point, name, block_havoc);
    // The reference: the PREFIX's writes (its destinations and the havoc of an opaque
    // store that precedes `point`) under the destination relation, as before; the
    // conservative WHOLE-BLOCK havoc (stores at or after `point`, which cannot change
    // the value read at `point`) under the plain relation its base names carry
    // (`KillSet::havoc`) — the rule `prefix_kill_rebinds` implements.
    #[cfg(any(test, feature = "version-oracle-differential"))]
    let diff = super::differential_enabled().then(|| {
        let prefix_kill: FxHashSet<String> = writes_until_uncached(func, block, point);
        let havoc_names = block_havoc.then(|| deref_store_havoc_names(func, block));
        let havoc_kill = match &havoc_names {
            Some(names) => KillSet::havoc(names.iter()),
            None => KillSet::havoc(std::iter::empty()),
        };
        (prefix_kill, havoc_kill)
    });
    entry_defs
        .iter()
        .filter(|f| {
            let survives = formula_survives_redefs_by(f, &mut kills);
            #[cfg(any(test, feature = "version-oracle-differential"))]
            if let Some((prefix_kill, havoc_kill)) = &diff {
                assert_eq!(
                    survives,
                    formula_survives_redefs(f, prefix_kill) && havoc_kill.survives(f),
                    "prefix-kill differential at {:?}[{point}] for {f:?}",
                    block.id
                );
            }
            survives
        })
        .map(|f| version_rename_at(f, &sv, func, block.id, point))
        .filter(|f| !names_within_block_value(f))
        .collect()
}

/// Per-block set of variables that MAY have been reassigned on some path from the
/// entry block up to (and including) that block's own statements.
///
/// A function's declared `preconditions` are *entry* facts: they describe the
/// argument values on the way in, not invariants. Conjoining a precondition like
/// `lo <= hi` onto a VC in a block that has already reassigned `hi` is unsound —
/// the entry relation no longer constrains the live `hi`, yet it vacuously
/// discharges a real `hi - lo` underflow (a false-PROVE of a real overflow). The
/// per-block path-def kill (`v2_live_path_defs`) only sees a block's OWN
/// statements, so it misses a reassignment in an *ancestor* block; this is a
/// proper forward MAY-dataflow that also accounts for ancestors.
///
/// Forward union fixpoint: `out[B] = in[B] ∪ gen_stmt[B] ∪ gen_term[B]`, where
/// `gen_stmt`/`gen_term` are the names a block redefines via its statements /
/// terminator (`Call` dest); `in[B]` is the union of predecessors' `out`. The
/// set returned for `B` is `in[B] ∪ gen_stmt[B]` — the terminator is excluded
/// because B's own safety obligations are Assert *terminator* VCs that sit at the
/// block end, before any `Call`-dest reassignment takes effect (the terminator's
/// redefinition is still propagated to successors via `out`). A precondition is
/// dropped at `B` iff it mentions any variable in this set. Dropping a hypothesis
/// is monotone-sound: it can turn a PROVE into a FAIL, never the reverse.
// =========================================================================
// STALENESS-CLASS S2 — canonical reaching-def versioning + shadow audit
//
// The version oracle (proven in S1: freshness + kill-parity, including loops)
// is the unconditional production semantics. The shadow-parity audit remains a
// diagnostic backstop against divergence from the retired overlap-based kill.
// =========================================================================
/// SMT names a block writes — the kill's gen-set channels (statement defs +
/// set-discriminant + pointer-copy write havoc + opaque-deref-store havoc +
/// terminator defs). NOTE this
/// INCLUDES terminator defs; `v2_may_reassigned_per_block`'s *returned* set
/// excludes them at the defining block (the terminator runs after that block's
/// own VCs), so the shadow audit exempts a block's own terminator def.
fn collect_block_extracted_def_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> FxHashSet<String> {
    let mut names: FxHashSet<String> = FxHashSet::default();
    if let Some(sv) = super::stmt_versions_if_cached(func)
        && let Some(prepared) = sv.prepared_block_outflow(func, block)
    {
        prepared.extend_raw_def_names(func, block, &mut names);
    } else {
        let mut block_defs = guards::extract_block_definitions(func, block);
        block_defs.extend(extract_set_discriminant_definitions(func, block));
        names.extend(block_defs.iter().filter_map(formula_def_name).map(str::to_string));
    }
    names
}

pub(crate) fn block_written_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> FxHashSet<String> {
    let mut names = collect_block_extracted_def_names(func, block);
    extend_with_assigned_place_dests(func, &block.stmts, &mut names);
    extend_with_derived_slice_len(&mut names);
    names.extend(block_deref_store_havoc_names(func, block));
    names.extend(terminator_def_names(func, block));
    names
}

/// THE UNIFIED WRITE ORACLE: the name of every EXPLICIT place destination in
/// `stmts` (`Assign` / `SetDiscriminant` / `Deinit`), plus the storage that a
/// `CopyNonOverlapping` may write, spelled by
/// `place_to_var_name` — the same fail-closed enumeration
/// `conservative_snapshot_writes` uses for the proof-snapshot lane, generalized
/// to every gen-set the version map and the kills are built from.
///
/// Definition extraction (`extract_block_definitions_until_impl`) intentionally
/// DECLINES a def for several rvalues — bare wrapping `Mul` / unknown widths,
/// unsigned non-constant `Rem`, unsupported casts, FP shapes whose lhs is not a
/// `Var`, `&mut` borrows, the generic catch-all. Each refusal is sound as a
/// dropped HYPOTHESIS, but the gen-sets used to be derived from
/// `formula_def_name` over the extracted defs alone, so each such `continue`
/// also deleted the WRITE from write visibility: downstream reads of the
/// assigned place rendered BARE and every rename-exempt bare fact
/// (preconditions, path guards, semantic guards, arg type ranges) unified
/// straight across the invisible write — a measured false PROOF
/// (`tests/dropped_def_write_visibility.rs`). Unioning the raw destinations in
/// makes the write domain a superset of what `stmt_writes_name` recognizes, so
/// the version-token gate and the per-statement token search agree by
/// construction (`mod.rs`'s `version_token_at` invariant), and widening is the
/// monotone-sound direction: an extra gen-set name only versions MORE reads,
/// and a versioned read with no defining equation is a FREE symbol — it can
/// weaken a proof or widen a refutation, never manufacture a proof.
///
/// Union-only: never replaces `formula_def_name` entries (synthetic lhs names
/// like `r*`, `r__slice_len`, `arr$L$vN` keep their own spellings alongside).
/// Call BEFORE `extend_with_derived_slice_len` so each added dest gets its
/// `__slice_len` twin, matching `conservative_snapshot_writes`' own derivation.
pub(crate) fn extend_with_assigned_place_dests(
    func: &VerifiableFunction,
    stmts: &[Statement],
    names: &mut FxHashSet<String>,
) {
    let mut index_locals: Option<IndexLocals> = None;
    for stmt in stmts {
        let place = match stmt {
            Statement::Assign { place, .. }
            | Statement::SetDiscriminant { place, .. }
            | Statement::Deinit { place } => place,
            Statement::CopyNonOverlapping { .. } => {
                extend_with_copy_nonoverlapping_writes(func, stmt, names);
                continue;
            }
            // Fail-closed contract for every OTHER variant:
            // `Statement::write_effect` is EXHAUSTIVE in trust-types (a new
            // variant fails to compile until classified there). `NoValueWrite`
            // variants write no place; `FailClosedOrBackstopped` variants with
            // no destination place (`Intrinsic`, `Unsupported`) cannot be
            // captured by a place-keyed gen-set and are refused by their own
            // gates. The tripwire
            // below fires if a place-writing variant is ever added without
            // being enumerated here.
            _ => {
                debug_assert!(
                    !matches!(stmt.write_effect(), trust_types::WriteEffect::Captured),
                    "place-destination statement not enumerated in the write oracle: {stmt:?}"
                );
                continue;
            }
        };
        names.insert(crate::place_to_var_name(func, place));
        // Trust: 2026-10-12 (UNION-SIBLING-WRITE-1) — a write through a union field
        // writes every overlapping sibling: the union value's own name rebinds them.
        if let Some(cover) = union_write_cover_name(func, place) {
            names.insert(cover);
        }
        // Trust (triage ticket 216): a `SetDiscriminant` also writes the synthetic
        // `discr_<place>` and tag-field names, including when its definitions
        // were refused (`set_discriminant_synthetic_write_names`).
        if matches!(stmt, Statement::SetDiscriminant { .. }) {
            names.extend(set_discriminant_synthetic_write_names(func, place).into_iter().flatten());
        }
        // Trust: 2026-09-16 (round A9/A10) — a whole-local write also rebinds every
        // name that embeds the local BY NUMBER as an index (`s*[_<local>]`); the
        // fallback spelling is what `write_rebinds` reaches those names through.
        // Minted only for a local that IS an index operand somewhere in the body
        // (`local_is_index_operand`): for any other local the fallback reaches
        // nothing and only doubles the gen-set.
        if place.projections.is_empty()
            && index_locals.get_or_insert_with(|| IndexLocals::of(func)).contains(place.local)
        {
            names.insert(local_fallback_name(place.local));
        }
    }
}

/// A pointer copy can modify storage without an explicit MIR place destination.
/// Even a `*const` destination cast to `*mut` may have write provenance, and an
/// integer-derived pointer may not reveal its referent here. Until a complete
/// destination/alias analysis is available, every local is a possible write.
/// This is a kill and version bump, not a claim that every local actually changes.
/// A literal zero count is the one case with no memory write.
fn extend_with_copy_nonoverlapping_writes(
    func: &VerifiableFunction,
    stmt: &Statement,
    names: &mut FxHashSet<String>,
) {
    if !copy_nonoverlapping_writes_memory(stmt) {
        return;
    }
    extend_with_every_local_write_name(func, names);
}

/// True iff `stmt` is a `CopyNonOverlapping` whose count is not the literal zero —
/// the statements [`extend_with_copy_nonoverlapping_writes`] treats as writing
/// every local. (`pub(crate)`, 2026-10-08: the interval lane's statement transfer
/// forgets every tracked name at one.)
pub(crate) fn copy_nonoverlapping_writes_memory(stmt: &Statement) -> bool {
    let Statement::CopyNonOverlapping { count, .. } = stmt else { return false };
    !matches!(
        count,
        Operand::Constant(trust_types::ConstValue::Int(0) | trust_types::ConstValue::Uint(0, _))
    )
}

/// The names a memory-writing `CopyNonOverlapping` may write: every local's
/// canonical name, its derived `__slice_len` twin, and its index fallback.
pub(super) fn extend_with_every_local_write_name(
    func: &VerifiableFunction,
    names: &mut FxHashSet<String>,
) {
    let index_locals = IndexLocals::of(func);
    for local in 0..func.body.locals.len() {
        let name = place_to_var_name(func, &trust_types::Place::local(local));
        if !name.ends_with(SLICE_LEN_SUFFIX) {
            names.insert(format!("{name}{SLICE_LEN_SUFFIX}"));
        }
        names.insert(name);
        if index_locals.contains(local) {
            names.insert(local_fallback_name(local));
        }
    }
}

/// The write names of ONE statement, as a per-statement kill set: what
/// [`extend_with_assigned_place_dests`] contributes for `stmt` plus derived
/// `__slice_len` names. Trust: 2026-09-16 (round A11) — the statement-
/// granular form of the unified write oracle, for the two consumers that walk a
/// block's own definitions in STATEMENT ORDER: the extraction's clobber cursor
/// (`guards::extract_block_definitions_until_impl`) and the path-def fixpoint's
/// own-def threading (`v2_path_def_fixpoint`). Both previously keyed their intra-
/// block kill on the lhs of EMITTED defs alone, so a declined destination (a bare
/// `Mul`, a `&mut` borrow, a `CheckedBinaryOp`) between a def and its use was not
/// a write there at all. Adding to a kill set is the monotone direction.
///
/// Opaque deref-store havoc is deliberately NOT part of this; the fixpoint adds
/// it per statement from
/// `deref_store_havoc_names_over`, the same union `writes_until` uses.
/// Pointer-copy havoc IS included: it has no place destination and its effect
/// must still kill earlier definitions at this statement.
pub(crate) fn stmt_direct_write_names(
    func: &VerifiableFunction,
    stmt: &Statement,
    names: &mut FxHashSet<String>,
) {
    if matches!(stmt, Statement::CopyNonOverlapping { .. }) {
        extend_with_copy_nonoverlapping_writes(func, stmt, names);
        return;
    }
    let place = match stmt {
        Statement::Assign { place, .. }
        | Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place } => place,
        // Same fail-closed contract as `extend_with_assigned_place_dests`: every
        // other variant either writes no place or is refused by its own gate.
        _ => {
            debug_assert!(
                !matches!(stmt.write_effect(), trust_types::WriteEffect::Captured),
                "place-destination statement not enumerated in the write oracle: {stmt:?}"
            );
            return;
        }
    };
    let dest = crate::place_to_var_name(func, place);
    if !dest.ends_with(SLICE_LEN_SUFFIX) {
        names.insert(format!("{dest}{SLICE_LEN_SUFFIX}"));
    }
    if place.projections.is_empty() && local_is_index_operand(func, place.local) {
        names.insert(local_fallback_name(place.local));
    }
    names.insert(dest);
    // Trust: 2026-10-12 (UNION-SIBLING-WRITE-1) — the union cover, with its derived
    // twin, exactly as `extend_with_assigned_place_dests` and the gen-sets carry it.
    if let Some(cover) = union_write_cover_name(func, place) {
        names.insert(format!("{cover}{SLICE_LEN_SUFFIX}"));
        names.insert(cover);
    }
    // Same synthetic names as `extend_with_assigned_place_dests`, with the derived
    // `__slice_len` twin the block-level sets give every name.
    if matches!(stmt, Statement::SetDiscriminant { .. }) {
        for name in set_discriminant_synthetic_write_names(func, place).into_iter().flatten() {
            if !name.ends_with(SLICE_LEN_SUFFIX) {
                names.insert(format!("{name}{SLICE_LEN_SUFFIX}"));
            }
            names.insert(name);
        }
    }
}

/// [`stmt_direct_write_names`] inserting directly into a [`super::rebind_index::RebindSet`]
/// via [`super::rebind_index::RebindSet::insert_with_derived_slice_len`], avoiding a
/// scratch `FxHashSet<String>` and avoiding `format!("{dest}__slice_len")` heap allocations.
pub(crate) fn stmt_direct_write_rebind_set(
    func: &VerifiableFunction,
    stmt: &Statement,
    clobbered: &mut super::rebind_index::RebindSet,
) {
    if matches!(stmt, Statement::CopyNonOverlapping { .. }) {
        let mut names = FxHashSet::default();
        extend_with_copy_nonoverlapping_writes(func, stmt, &mut names);
        for w in &names {
            clobbered.insert(w);
        }
        return;
    }
    let place = match stmt {
        Statement::Assign { place, .. }
        | Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place } => place,
        _ => {
            debug_assert!(
                !matches!(stmt.write_effect(), trust_types::WriteEffect::Captured),
                "place-destination statement not enumerated in the write oracle: {stmt:?}"
            );
            return;
        }
    };
    let dest = crate::place_to_var_name(func, place);
    clobbered.insert_with_derived_slice_len(&dest);
    if place.projections.is_empty() && local_is_index_operand(func, place.local) {
        clobbered.insert(&local_fallback_name(place.local));
    }
    if let Some(cover) = union_write_cover_name(func, place) {
        clobbered.insert_with_derived_slice_len(&cover);
    }
    if matches!(stmt, Statement::SetDiscriminant { .. }) {
        for name in set_discriminant_synthetic_write_names(func, place).into_iter().flatten() {
            clobbered.insert_with_derived_slice_len(&name);
        }
    }
}

/// The kill a block's OWN statements impose on facts that were true at its
/// ENTRY: extracted def names + every raw statement destination
/// (`extend_with_assigned_place_dests`) + derived `__slice_len` twins + the
/// opaque-deref-store havoc. Terminator defs are deliberately EXCLUDED — a
/// block's own safety obligations sit at its terminator, before any `Call`-dest
/// write takes effect (the same exclusion `v2_may_reassigned_per_block` applies
/// at the defining block). This is the exact intra-block half of the staleness
/// kill for consumers whose threaded facts already received the flow-sensitive
/// inter-block kills in `v2_path_def_fixpoint` (see `hardened.rs`).
/// [`block_entry_fact_kill_names`] as a KILL, with the opaque-store havoc judged by
/// the relation its base names carry (`KillSet::havoc`) instead of folded into the
/// destination set. `survives(f)` holds iff neither half rebinds a free name of `f`.
pub(crate) struct BlockEntryFactKill {
    written: KillSet,
    havoc: KillSet,
}

impl BlockEntryFactKill {
    pub(crate) fn survives(&self, f: &Formula) -> bool {
        self.written.survives(f) && self.havoc.survives(f)
    }

    /// Some name of either half rebinds `read`.
    fn kills(&self, read: &str) -> bool {
        (!self.written.empty && self.written.kills(read))
            || (!self.havoc.empty && self.havoc.kills(read))
    }

    /// Trust (2026-10-10, KILLED-ENTRY-EXISTS-1): the entry fact `f` of `block` as
    /// a hypothesis the block's own writes leave TRUE. A fact that survives the kill
    /// is returned as is. A killed one is returned with every free name the kill
    /// rebinds renamed to a FRESH name ([`killed_entry_exists_name`]), so it states
    /// "there is a value the place held at block entry such that `f` held", and it
    /// no longer mentions the place the block writes. `None` (the old drop) when the
    /// rename cannot be made safely.
    ///
    /// THE DEFECT THIS CLOSES (false refutation of valid Rust). `*count += 1;
    /// *count - 1` is `bb0: _2 = CheckedAdd(*_1, 1); assert(!_2.1)` then `bb1: *_1
    /// = move _2.0; _3 = *_1; _4 = CheckedSub(_3, 1); assert(!_4.1)`. The entry
    /// fact of bb1, `_2.0 == count* + 1` with `0 <= count* <= MAX`, mentions
    /// `count*`, which bb1 writes, so the hardened twin of the `Overflow(Sub)`
    /// assert dropped it whole, and `_2.0` (the value bb1 stores and reloads)
    /// floated free: refuted at `_2.0 = 0` while the per-statement row PROVED.
    /// Measured on trust-ir-conformance `CharCarriers::of` (preview3, row C1) and
    /// any `&mut` counter bumped and reread.
    ///
    /// SOUNDNESS. Every entry fact of `block` was true at block entry, jointly, in
    /// every execution reaching it. Renaming a set of free names consistently to
    /// names that occur NOWHERE else in the VC is existential quantification: the
    /// renamed conjunction is satisfied by giving each fresh name the entry value
    /// of the place it replaces, whatever the rest of the VC says, so it can only
    /// delete models no execution produces. It never re-ties a fact to the value
    /// the block wrote: the written place is no longer named by it. Names the kill
    /// does NOT rebind stay as they were, on the same premise as the facts that
    /// survive whole. The fresh names carry no `#`, so no version rename,
    /// `#`-token collapse (`normalize_ssa_version_tokens`) or seal touches them,
    /// and they are block-keyed and namespaced; a body that declares a local in
    /// that namespace gets the old drop. A fact with a binder also gets the old
    /// drop (a rename under `Forall`/`Exists` would have to respect the binding),
    /// and so does one whose killed mention is not a plain `Var` or already
    /// carries a version token: the renamed fact must SURVIVE the kill, or it is
    /// dropped.
    pub(crate) fn survive_or_quantify(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        f: &Formula,
    ) -> Option<Formula> {
        if self.survives(f) {
            return Some(f.clone());
        }
        if killed_entry_namespace_is_declared(func)
            || trust_types::any_formula_node(f, &mut |node| {
                matches!(node, Formula::Forall(..) | Formula::Exists(..))
                    || matches!(node, Formula::Var(name, _) if name.contains('#') && self.kills(name))
            })
        {
            return None;
        }
        let renamed = f.clone().map(&mut |node| match node {
            Formula::Var(name, sort) if !name.contains('#') && self.kills(&name) => {
                Formula::Var(killed_entry_exists_name(block, &name), sort)
            }
            other => other,
        });
        self.survives(&renamed).then_some(renamed)
    }
}

/// The namespace of the fresh names [`BlockEntryFactKill::survive_or_quantify`]
/// mints. No `#`: these are not version tokens of a place, and nothing that reads
/// `#` tokens may treat them as one.
pub(crate) const KILLED_ENTRY_EXISTS_PREFIX: &str = "__trust_kx";

/// The fresh name standing for the BLOCK-ENTRY value of `name` in a killed entry
/// fact of `block`. Injective in `(block, name)`: the block number is the digit
/// run before the first `_` after the prefix.
pub(crate) fn killed_entry_exists_name(block: BlockId, name: &str) -> String {
    format!("{KILLED_ENTRY_EXISTS_PREFIX}{}_{name}", block.0)
}

/// A local of `func` whose source name is in the fresh namespace: its place names
/// could collide with a fresh name, so the rename is refused for the whole body.
fn killed_entry_namespace_is_declared(func: &VerifiableFunction) -> bool {
    func.body
        .locals
        .iter()
        .any(|l| l.name.as_deref().is_some_and(|n| n.starts_with(KILLED_ENTRY_EXISTS_PREFIX)))
}

/// Trust (2026-09-29): the entry-fact kill of `block` for a consumer that KILLS with
/// it (the hardened twin's cross-block reaching defs). Same names as
/// [`block_entry_fact_kill_names`]; the difference is only the relation the havoc
/// half is judged with — see [`KillSet::havoc`] for why the destination relation
/// was wrong there (the bounds-assert twin after `s[i] = 1` lost its length tie).
pub(crate) fn block_entry_fact_kill(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> BlockEntryFactKill {
    let mut names = collect_block_extracted_def_names(func, block);
    extend_with_assigned_place_dests(func, &block.stmts, &mut names);
    extend_with_derived_slice_len(&mut names);
    BlockEntryFactKill {
        written: KillSet::new(&names),
        havoc: KillSet::havoc(deref_store_havoc_names(func, block).iter()),
    }
}

pub(crate) fn block_entry_fact_kill_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> FxHashSet<String> {
    let mut names = collect_block_extracted_def_names(func, block);
    extend_with_assigned_place_dests(func, &block.stmts, &mut names);
    extend_with_derived_slice_len(&mut names);
    names.extend(deref_store_havoc_names(func, block).iter().cloned());
    names
}

/// The opaque-deref-store havoc contribution to a BLOCK's gen-set, as the union
/// over the block's statements of what [`stmt_writes_name`] reports for each.
///
/// WHY THIS EXISTS. `deref_store_havoc_names` is deliberately whole-block and
/// whole-function: one opaque store anywhere in the block havocs EVERY mutably
/// borrowed / mutable-pointer local's BASE name. Feeding that raw into the
/// gen-set makes the inter-block reaching-def map believe a store to
/// `self*.0.1` redefines its own SIBLING `self*.0.0` — because the base name
/// `self` is a projection ANCESTOR of both, so `place_names_overlap` unions
/// their version sets. `stmt_writes_name` already refuses exactly this
/// (`opaque_store_confined_to_written_place`, the P0 multi-write fix), but that
/// refinement lives only at STATEMENT granularity; `block_written_names` fed the
/// unrefined list into `block_entry_versions`, so the BLOCK-level map kept the
/// over-merge.
///
/// The consequence was a postcondition over `&mut self` on ANY body that writes
/// two different fields: the flag's reaching-def token at the exit block became
/// the join of every sibling store (`self*.0.0#e_s1_0_s4_0`), a name no pin
/// could spell, so a TRUE clause and its exact NEGATION were both refuted from a
/// free variable. This is the block-granularity twin of the statement-level fix,
/// and computing it as the per-statement union makes the two oracles agree BY
/// CONSTRUCTION rather than by a second, forkable rule.
///
/// SOUNDNESS. Shrinking a gen-set is the dangerous direction — a name that stops
/// being re-versioned lets a STALE fact survive and vacuously discharge a real
/// obligation. Three things keep this safe:
///
///   * a name is dropped ONLY under `opaque_store_confined_to_written_place`,
///     which certifies from the TYPE that the pointer addresses a plain `struct`
///     (no variants, `AdtKind::Struct`) through `Field` projections alone — so
///     the written place is disjointly addressable and provably cannot alias a
///     sibling field;
///   * the union is over statements, so ONE unconfined opaque store anywhere in
///     the block restores the full havoc for the whole block;
///   * the exact written place is added explicitly, so the store still kills its
///     own place, its ancestors and its descendants even when the block-def
///     extraction produced no fact for an unlowerable rvalue.
///
/// Every OTHER local in the havoc list is retained for every store, so
/// cross-pointer aliasing (`q*` havoced by a store through `p`) is untouched.
fn block_deref_store_havoc_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> FxHashSet<String> {
    deref_store_havoc_names_over(func, block, &block.stmts)
}

/// [`block_deref_store_havoc_names`] over an arbitrary STATEMENT SLICE of
/// `block`, so the point-in-block oracle (`writes_until`) and the whole-block
/// one compute the same union over the statements each can see. `block` still
/// selects the havoc LIST (`deref_store_havoc_names` is block-gated by design —
/// a store anywhere in the block puts its referent-havoc in effect); `stmts`
/// selects which stores contribute.
pub(crate) fn deref_store_havoc_names_over(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmts: &[Statement],
) -> FxHashSet<String> {
    if stmts.is_empty() || !stmts.iter().any(|s| matches!(s, Statement::Assign { .. })) {
        return FxHashSet::default();
    }
    let havoc = deref_store_havoc_names(func, block);
    let mut out: FxHashSet<String> = FxHashSet::default();
    if havoc.is_empty() {
        return out;
    }
    for stmt in stmts {
        let Statement::Assign { place, .. } = stmt else { continue };
        // Trust: 2026-10-11 (LAUNDERED-ALIAS-STORE) — the one havoc predicate. A write
        // with no leading `Deref` (a direct write into escaped storage) is never
        // confined, so it takes the whole list.
        if !write_havocs_function_list(func, place) {
            continue;
        }
        if !opaque_store_confined_to_written_place(func, place) {
            // Unconfined: this statement alone havocs the whole list, so the
            // union is the whole list and nothing further can shrink it.
            return havoc.iter().cloned().collect();
        }
        // Minted with the SAME construction `mutable_pointer_local_names` uses,
        // so the exclusion is name-consistent with the list by construction.
        let store_base =
            crate::place_to_var_name(func, &trust_types::Place::local(place.local));
        // The store's own tree is answered precisely by the written place name.
        out.insert(crate::place_to_var_name(func, place));
        out.extend(havoc.iter().filter(|h| !place_names_overlap(h, &store_base)).cloned());
    }
    out
}

/// Forward reaching-definition may-dataflow over names. Per-block OUT-sets
/// (version AFTER the block's own writes), matching `may_reassigned[B] = in[B] ∪
/// gen[B]`. A name's version at a block = the set of writer ids that may reach it
/// (`-1` = entry/parameter value, `b` = block `b`). Reuses the kill's exact
/// gen-set (`block_written_names`) so the two analyses are directly comparable.
#[cfg(test)]
pub(crate) fn reaching_def_versions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, FxHashMap<String, std::collections::BTreeSet<i64>>> {
    use std::collections::BTreeSet;
    let n = func.body.blocks.len();
    let gen_sets: Vec<FxHashSet<String>> =
        func.body.blocks.iter().map(|b| block_written_names(func, b)).collect();
    let all_names: FxHashSet<String> = gen_sets.iter().flatten().cloned().collect();

    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, b) in func.body.blocks.iter().enumerate() {
        for t in v2_terminator_targets(&b.terminator) {
            if t.0 < n {
                preds[t.0].push(i);
            }
        }
    }

    let entry_in: FxHashMap<String, BTreeSet<i64>> =
        all_names.iter().map(|nm| (nm.clone(), BTreeSet::from([-1i64]))).collect();
    let mut in_sets: Vec<FxHashMap<String, BTreeSet<i64>>> = vec![FxHashMap::default(); n];
    if n > 0 {
        in_sets[0] = entry_in.clone();
    }

    let out_of = |b: usize, in_b: &FxHashMap<String, BTreeSet<i64>>| {
        let mut out: FxHashMap<String, BTreeSet<i64>> = FxHashMap::default();
        for nm in &all_names {
            if gen_sets[b].contains(nm) {
                out.insert(nm.clone(), BTreeSet::from([b as i64]));
            } else if let Some(s) = in_b.get(nm) {
                out.insert(nm.clone(), s.clone());
            }
        }
        out
    };

    // Round-robin to the LEAST fixpoint: every in-set starts empty (bb0 at the entry
    // seed) and the transfer is monotone, so the sets only grow and the loop stops
    // after at most one round per (block, name, writer) triple added — no cap needed.
    let mut changed = true;
    while changed {
        changed = false;
        for b in 0..n {
            let mut new_in: FxHashMap<String, BTreeSet<i64>> =
                if b == 0 { entry_in.clone() } else { FxHashMap::default() };
            for &p in &preds[b] {
                let out_p = out_of(p, &in_sets[p]);
                for (nm, s) in out_p {
                    new_in.entry(nm).or_default().extend(s);
                }
            }
            if new_in != in_sets[b] {
                in_sets[b] = new_in;
                changed = true;
            }
        }
    }

    func.body.blocks.iter().enumerate().map(|(i, b)| (b.id, out_of(i, &in_sets[i]))).collect()
}

/// Shadow-parity audit: for every (block, tracked-name), does VERSIONING mark the
/// name stale (version ≠ {-1}) iff the KILL would drop a fact about it? The kill's
/// drop decision runs through the DIRECTIONAL write/read relation
/// ([`formula_survives_redefs`] → `formula_mentions_redef` → [`dest_write_rebinds`],
/// called with the WRITTEN name first): a write to whole `x` drops a fact about
/// `x.0`/`x[i]`/`*x` (the [`place_names_overlap`] core), a write of an index local
/// `_l` drops a fact about `s*[_l]` (`write_covers_index_segment`), and a write of
/// `s` drops a fact about the derived `s__slice_len`
/// (`write_covers_derived_slice_len`). So the audit probes with the kill's own
/// predicate — not exact membership. Returns the number of UNEXPECTED divergences
/// (a block's own terminator def is exempt: the kill excludes it at the defining
/// block by design). Zero ⟹ versioning is drop-equivalent to the kill on this
/// function over its tracked-name domain.
///
/// The audit is only meaningful while the QUERY side tests the SAME directional
/// relation, in the same argument order, as the kill side does: a divergence in the
/// PREDICATES shows up here as a parity break that no production renaming has, and a
/// silent agreement here means nothing once the two predicates differ. The two must
/// therefore move together — see the amendment on `VersionCtx::is_versioned_query`,
/// which records the gap this merge opened (the query tests `write_rebinds`, the kill
/// the wider `dest_write_rebinds`) and why it is an audit question rather than a
/// production one.
#[cfg(test)]
pub(crate) fn shadow_parity_disagreements(func: &VerifiableFunction) -> usize {
    use std::collections::BTreeSet;
    let kill = v2_may_reassigned_per_block(func);
    let vctx = VersionCtx::build(func);
    let entry_only = BTreeSet::from([-1i64]);
    let empty = FxHashSet::default();
    let mut disagreements = 0usize;
    for block in &func.body.blocks {
        let killed = kill.get(&block.id).unwrap_or(&empty);
        let Some(vers) = vctx.per_block.get(&block.id) else { continue };
        let term_defs = terminator_def_names(func, block);
        for (name, vset) in vers {
            let versioned = *vset != entry_only;
            let probe = Formula::Var(name.clone(), trust_types::Sort::Int);
            let kill_drops = !formula_survives_redefs(&probe, killed);
            // Exempt a block's OWN terminator def: version is {B} but the kill's
            // returned set excludes the terminator at B (it runs after B's VCs).
            let is_own_term_def =
                *vset == BTreeSet::from([block.id.0 as i64]) && term_defs.iter().any(|d| d == name);
            if is_own_term_def {
                continue;
            }
            if kill_drops != versioned {
                disagreements += 1;
            }
        }
    }
    disagreements
}

/// S2b overlap-aware shadow audit: extends `shadow_parity_disagreements` to also
/// probe PROJECTED queries (each tracked name's projection-parent and a `.0`
/// child), asserting the OVERLAP-AWARE version verdict (`is_versioned_query`)
/// equals the kill's overlap-based drop verdict. Zero ⟹ versioning is
/// drop-equivalent to the kill for projected facts too — closing the gap the
/// tracked-name audit could not see.
#[cfg(test)]
pub(crate) fn shadow_parity_disagreements_overlap(func: &VerifiableFunction) -> usize {
    let kill = v2_may_reassigned_per_block(func);
    let vctx = VersionCtx::build(func);
    let empty = FxHashSet::default();
    let mut disagreements = 0usize;
    for block in &func.body.blocks {
        let killed = kill.get(&block.id).unwrap_or(&empty);
        let term_defs = terminator_def_names(func, block);
        let Some(vers) = vctx.per_block.get(&block.id) else { continue };
        // Probe domain: each tracked name + its projection-parent + a `.0` child,
        // so a write to whole `s` is checked against a fact about `s.0`, and a
        // write to `s.0` against a fact about whole `s`.
        let mut probes: Vec<String> = Vec::new();
        for name in vers.keys() {
            probes.push(name.clone());
            if let Some(dot) = name.rfind('.') {
                probes.push(name[..dot].to_string()); // projection-parent
            }
            probes.push(format!("{name}.0")); // synthetic descendant
        }
        for q in probes {
            // A block's own terminator def is excluded from the kill's returned set
            // (runs after the block's VCs); skip a probe that is exactly such a def.
            if term_defs.iter().any(|d| *d == q) {
                continue;
            }
            let versioned = vctx.is_versioned_query(block.id, &q);
            let kill_drops =
                !formula_survives_redefs(&Formula::Var(q.clone(), trust_types::Sort::Int), killed);
            if versioned != kill_drops {
                disagreements += 1;
            }
        }
    }
    disagreements
}

// =========================================================================
// STALENESS-CLASS S2c Stage 0 — STATEMENT-GRANULAR version oracle
//
// The block-level oracle (`VersionCtx`) is INSUFFICIENT for the naming flip: VC
// bodies are statement-granular (built via `extract_block_definitions_until`),
// but `version_token(block, name)` is keyed by BlockId only. A name written
// LATER in the same block (e.g. `y = x + 5; x = big`) makes the block-level token
// non-entry, which would rename an EARLIER read of `x` apart from an entry fact —
// a false-FAIL the block-level parity audits (`shadow_parity_disagreements*`)
// cannot even witness (they compare whole-block vs whole-block).
//
// This statement-granular oracle keys the version on `(block, stmt_idx)`,
// mirroring the array path's `ArrayVersionCtx::live_version` (lib.rs:1909, which
// counts element stores in `stmts[..stmt_idx]`). It is the load-bearing
// prerequisite for the flip; nothing consumes it yet (pure addition).
// =========================================================================
/// Names written by statements `stmts[..stmt_idx]` of `block` — the SAME view the
/// VC body sees at a mid-block VC (`extract_block_definitions_until`), so a
/// statement-granular version derived from this is drop-equivalent to the kill at
/// the correct granularity. Includes set-discriminant defs and the opaque-deref
/// havoc (attributed conservatively when a deref-store occurs in the prefix).
///
/// Production code no longer materialises this set: the version oracle's per-block
/// write index (`block_writes::FnWrites::gate`) answers "does some name of it rebind
/// `name`" by lookup, falling back to [`writes_until_uncached`] only when a
/// statement-prefix definition extraction may carry a synthetic name. This form is
/// the reference the index is checked against.
#[cfg(any(test, feature = "version-oracle-differential"))]
pub(crate) fn writes_until(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_idx: usize,
) -> std::rc::Rc<FxHashSet<String>> {
    std::rc::Rc::new(writes_until_uncached(func, block, stmt_idx))
}

pub(super) fn writes_until_uncached(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_idx: usize,
) -> FxHashSet<String> {
    let mut defs = guards::extract_block_definitions_until(func, block, stmt_idx);
    defs.extend(extract_set_discriminant_definitions_until(func, block, stmt_idx));
    let mut names: FxHashSet<String> =
        defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
    // Same per-statement destination union as `block_written_names`,
    // prefix-restricted — the two oracles must agree (the unified write oracle).
    extend_with_assigned_place_dests(
        func,
        &block.stmts[..stmt_idx.min(block.stmts.len())],
        &mut names,
    );
    extend_with_derived_slice_len(&mut names);
    // Opaque deref-store havoc: if any opaque `*p = v` appears in stmts[..stmt_idx],
    // its referent-havoc is in effect from that point. `deref_store_havoc_names` is
    // block-level; gate it on a prefix occurrence so it does not leak BACKWARD to
    // reads before the store.
    //
    // Trust: the CONTRIBUTION is the per-statement union, identical to
    // `block_deref_store_havoc_names` but restricted to the prefix. Taking the
    // raw block-level list here contradicts `stmt_writes_name`, which subtracts
    // a certified disjoint store's own tree: `writes_until` would report a write
    // overlapping `self*.0.0` for a block that only stores `self*.0.1`, then the
    // per-statement search would find NO statement writing it, and
    // `version_token_at` would fall through to the phantom `s{b}_pre`
    // entry-havoc token — a name nothing can ever pin. The two oracles must
    // agree, so this is the same union, prefix-restricted.
    names.extend(deref_store_havoc_names_over(
        func,
        block,
        &block.stmts[..stmt_idx.min(block.stmts.len())],
    ));
    names
}

/// Every successor edge `v2_path_def_fixpoint` can transport a fact across:
/// `unguarded_successors` (which includes the unwind/cleanup successor) plus the
/// in-CFG `discovered_clauses` targets — the same union
/// `entry_sentinel_tie_subsumption_tests::fixpoint_enqueue_targets` pins as the
/// fixpoint's enqueue set for every `Terminator` variant, present and future.
/// `v2_terminator_targets` is unioned in as belt-and-braces so a future divergence
/// between the two successor functions fails toward MORE predecessor edges — i.e.
/// fewer `#e` mints — never fewer.
pub(crate) fn full_graph_terminator_targets(
    terminator: &Terminator,
    _source: BlockId,
) -> Vec<BlockId> {
    let mut targets: Vec<BlockId> = Vec::new();
    for_each_full_graph_terminator_target(terminator, |target| targets.push(target));
    targets.sort_unstable_by_key(|t| t.0);
    targets.dedup();
    targets
}

pub(super) fn for_each_full_graph_terminator_target(
    terminator: &Terminator,
    mut f: impl FnMut(BlockId),
) {
    terminator.for_each_in_cfg_successor(&mut f);
    super::for_each_v2_terminator_target(terminator, &mut f);
}

pub(crate) fn full_graph_terminator_has_target(terminator: &Terminator, needle: BlockId) -> bool {
    terminator.has_in_cfg_successor(needle) || super::v2_terminator_has_target(terminator, needle)
}

pub(crate) fn any_full_graph_terminator_target(
    terminator: &Terminator,
    mut f: impl FnMut(BlockId) -> bool,
) -> bool {
    let mut matched = false;
    terminator.for_each_in_cfg_successor(|target| {
        if !matched && f(target) {
            matched = true;
        }
    });
    if !matched {
        super::for_each_v2_terminator_target(terminator, |target| {
            if !matched && f(target) {
                matched = true;
            }
        });
    }
    matched
}

/// True iff an opaque deref-store to `place` provably CONFINES its effect —
/// *within the storing pointer's OWN pointee tree* — to the exact place written,
/// so a SIBLING field path under that same pointer cannot be disturbed by it.
///
/// Trust (P0 multi-write postcondition false-refutation, 2026-08-01). This exists
/// solely to let [`stmt_writes_name`] subtract the storing pointer's own tree from
/// the block-level [`deref_store_havoc_names`] over-approximation. That list is a
/// *whole-function* set of BASE LOCAL names (`mutable_pointer_local_names` walks
/// locals, so a `&mut` parameter contributes the bare name `self`), and
/// `place_names_overlap` treats `*` as a projection separator — so
/// `place_names_overlap("self", "self*.0")` is TRUE and the store `(*self).1 = v`
/// was reported as a write of its own SIBLING `self*.0`. For the fact KILL that is
/// merely conservative, but `stmt_writes_name` ALSO chooses WHICH statement stamps
/// a name's version token, and moving `self*.0`'s token onto a statement that never
/// wrote it severs the token from the exact-token out-parameter pin in
/// `with_out_param_pins` — leaving the postcondition's read of `self*.0` a FREE
/// variable that the solver "refutes" with a *verified counterexample* against a
/// body that plainly establishes it. Every `&mut self` method that writes two
/// fields was affected.
///
/// FAIL-CLOSED. Returns `false` — keeping today's whole-pointee havoc verbatim —
/// unless every step is positively certified:
///   * a leading `Deref` with a NON-EMPTY path after it of constant `Field`s and
///     (since 2026-09-29) `Index` steps into ARRAY-typed places — a whole-pointee
///     store `*p = v` has no sibling to spare; an index into an array stays in
///     that array's inline storage, and which element it hits is the written
///     name's business, not this predicate's; an index into a SLICE, a
///     `ConstantIndex`/`Subslice` (a spelling that need not match the element's
///     other spellings), a nested `Deref` (re-opens aliasing) and a `Downcast`
///     (the field's location is variant-dependent) refuse,
///   * an unambiguous declared pointer type for the storing local, and
///   * every ADT traversed along that path positively confirmed
///     `Some(AdtKind::Struct)`. A `union`'s fields OVERLAP at byte offset 0, so
///     sibling independence is OPERATIONALLY FALSE for one; an `enum` (non-empty
///     `variants`) is variant-dependent; and `None` means the ADT was never lowered
///     from a rustc `AdtDef` and its kind is simply unknown. This is the same
///     G-STRUCT-KIND posture `clean_ground::sem_field_set_shape_of` already applies
///     to the field-setter frame surface, for the identical reason.
///
/// Note this certifies ONLY intra-pointer sibling disjointness. CROSS-pointer
/// aliasing is deliberately untouched by the caller: a store through `q` still
/// havocs every name under `p`, which is what the out-param pin's soundness
/// argument (contract_vcs.rs, "ALIASING IS NOT ASSUMED AWAY") relies on.
pub(super) fn opaque_store_confined_to_written_place(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> bool {
    let Some((trust_types::Projection::Deref, rest)) = place.projections.split_first() else {
        return false;
    };
    if rest.is_empty() {
        return false;
    }
    // An ambiguous (duplicated) declaration index makes the type unusable; refuse,
    // matching `is_out_param_place`. (By lookup: this runs once per opaque store.)
    let Some(decl) = crate::unique_local_decl(func, place.local) else { return false };
    let mut ty: &trust_types::Ty = match &decl.ty {
        trust_types::Ty::Ref { inner, .. } => inner,
        trust_types::Ty::RawPtr { pointee, .. } => pointee,
        _ => return false,
    };
    for proj in rest {
        // Trust (2026-09-29): an `Index` step into an ARRAY-typed place stays inside
        // that array's inline storage (MIR bounds-checks it), so a store
        // `(*s).items[i] = x` cannot reach the sibling field `(*s).len`. Which
        // ELEMENT it hits is left to the written name: behind a `&mut` root even a
        // constant index spells `[_l]` (`constant_array_index_segment` shape B
        // refuses a mutable root), and `s*.0[_l]` overlaps every element of `s*.0`
        // by the symbolic-index rule of `place_names_overlap` — so this certifies
        // nothing about the elements, only that the store stays in `s*.0`.
        // `ConstantIndex` stays refused: its `from_end`/`min_length` spelling need
        // not equal another spelling of the same element (the bail list above
        // `array_local_index_naming_stable`), so name overlap could miss it. A
        // SLICE step is not inline storage of the pointee and stays refused.
        // Measured on the ordinary-Rust sweep: `if s.len < 8 { s.items[0] = x;
        // s.len += 1 }` was refuted with the guarded `s.len` re-versioned to
        // `usize::MAX` by the element store (m01, m01b, m18, p01).
        if let trust_types::Projection::Index(_) = proj {
            let trust_types::Ty::Array { elem, .. } = ty else { return false };
            ty = elem;
            continue;
        }
        let trust_types::Projection::Field(idx) = proj else { return false };
        let trust_types::Ty::Adt { fields, variants, adt_kind, .. } = ty else { return false };
        // G-STRUCT-KIND: a positively-confirmed `struct` with no variant structure.
        if !variants.is_empty() || *adt_kind != Some(trust_types::AdtKind::Struct) {
            return false;
        }
        let Some((_, field_ty)) = fields.get(*idx) else { return false };
        ty = field_ty;
    }
    true
}

/// True iff statement `bb.stmts[k]` ITSELF writes a place overlapping `name` — a
/// direct `Assign`/`SetDiscriminant` dest, a pointer copy, or an opaque
/// deref-store (`*p = v` with `p` non-canonicalizable) that havocs `name`.
/// The single-statement test the
/// version token needs (vs the cumulative `writes_until`, which collapses two
/// same-block writes to one token).
///
/// `pub(crate)` (2026-10-08, trust-interval-drop-havoc) for the interval lane's
/// statement transfer (`abstract_interp::transfer::transfer_statements`), which
/// must forget at least every tracked name this predicate says a statement writes
/// and re-checks exactly that against it under `cfg(test)`.
pub(crate) fn stmt_writes_name(
    func: &VerifiableFunction,
    bb: &trust_types::BasicBlock,
    k: usize,
    name: &str,
) -> bool {
    let Some(stmt) = bb.stmts.get(k) else { return false };
    match stmt {
        Statement::Assign { place, .. } => {
            // Trust: 2026-10-12 (UNION-SIBLING-WRITE-1) — the destination and its union
            // cover, on the destination's channel (`extend_with_assigned_place_dests`
            // carries both); [`WrittenPlace`] is the interval lane's spelling too.
            if WrittenPlace::of(func, place).dest_rebinds(name) {
                return true;
            }
            // Trust: 2026-09-16 (round A9/A10) — a whole-local write of `l` writes
            // every name that embeds `l` by number as an index (`s*[_l]`,
            // `s*[_l]__slice_len`) and the fallback name `_l` the gen-sets carry for
            // it (`extend_with_assigned_place_dests`, same gate). The gate in
            // `version_token_at` admits these through `write_rebinds(_l, name)`; this
            // is the matching per-statement search, so the phantom `s{b}_pre` arm
            // stays unreachable for them.
            if place.projections.is_empty() && local_is_index_operand(func, place.local) {
                let fallback = local_fallback_name(place.local);
                if name == fallback || write_covers_index_segment(&fallback, name) {
                    return true;
                }
            }
            // Trust: 2026-10-11 (LAUNDERED-ALIAS-STORE) — the statement havocs the list
            // when `write_havocs_function_list` says so: an opaque deref store, or a
            // write into escaped storage a laundered pointer copy can read.
            if !write_havocs_function_list(func, place) {
                return false;
            }
            let havoc = deref_store_havoc_names(func, bb);
            // Trust (P0 multi-write postcondition false-refutation): when the store's
            // own field path is certified disjointly-addressable, the exact written
            // place `dest` (tested above) ALREADY is the precise answer inside the
            // storing pointer's own tree — ancestors (`p*`, `p`) and descendants of
            // `dest` still report true through that branch. Subtract only that tree
            // from the alias havoc, which exists for the OTHER locals the store might
            // reach. Every other name in the list is retained, so cross-pointer
            // aliasing (`q*` havoced by a store through `p`) is fully preserved.
            if opaque_store_confined_to_written_place(func, place) {
                // Minted with the SAME construction `mutable_pointer_local_names` uses,
                // so the exclusion is name-consistent with the list by construction.
                let store_base = crate::place_to_var_name(
                    func,
                    &trust_types::Place { local: place.local, projections: Vec::new() },
                );
                return havoc
                    .iter()
                    .filter(|h| !place_names_overlap(h, &store_base))
                    .any(|h| write_rebinds(h, name));
            }
            havoc.iter().any(|h| write_rebinds(h, name))
        }
        Statement::SetDiscriminant { place, .. } => WrittenPlace::of(func, place).rebinds(name),
        // `Deinit` invalidates its place. With Deinit dests in the gen-sets
        // (`extend_with_assigned_place_dests`), the token search must find the
        // statement — gate/search parity, keeping the `s{b}_pre` phantom arm of
        // `version_token_at` unreachable for union-admitted names. Deliberately
        // NOT an establish point (`block_def_establish_stmt` unchanged — a
        // deinit defines nothing).
        Statement::Deinit { place } => WrittenPlace::of(func, place).dest_rebinds(name),
        Statement::CopyNonOverlapping { .. } => {
            let mut written = FxHashSet::default();
            extend_with_copy_nonoverlapping_writes(func, stmt, &mut written);
            written.iter().any(|w| write_rebinds(w, name))
        }
        _ => false,
    }
}

/// Trust (P0 false-refutation, 2026-07-02 — the `__slice_len` version-oracle
/// mismatch): a write to the WHOLE place `dest` (or an ancestor of it) also
/// writes the SYNTHETIC metadata name `{dest}__slice_len` — reassigning a
/// slice pointer/reference changes which slice it points at, hence its length
/// var. `writes_until` already counts these names as written (the block-def
/// extraction emits `Eq({dest}__slice_len, referent_len)` for `&`/`&mut`/`&raw`
/// borrows, and `formula_def_name` reports that lhs), but `stmt_writes_name`
/// and `block_def_establish_stmt` tested only the RAW place-name algebra, in
/// which `_6` does NOT overlap `_6__slice_len` (`_` is not a projection
/// separator). The mismatch minted the phantom entry-havoc token `s{b}_pre`
/// for every in-block `__slice_len` read while the defining tie fact stayed
/// bare/unpinnable — name-disjoint — so the metadata slice-length tie of a
/// guarded `&mut [T]` index (`_6 = &raw const *dst; _7 = PtrMetadata(_6)`) was
/// pruned from the bounds VC and provably-safe code FALSE-REFUTED
/// (superiority fixtures bounded_copy / guarded_mut_slice_bound /
/// two_pointer_reverse).
///
/// Deliberately ANCESTOR-ONLY (`dest == base` or `base` a projection
/// descendant of `dest`): an ELEMENT/pointee store (`dst*[i] = v`, a
/// DESCENDANT of `dst`) preserves the length metadata and must NOT count as a
/// write of `dst__slice_len` — a phantom write there would re-version
/// later reads away from the live tie and reintroduce the disconnect.
pub(super) fn write_covers_derived_slice_len(dest: &str, name: &str) -> bool {
    name.strip_suffix(SLICE_LEN_SUFFIX).is_some_and(|base| {
        base == dest
            || (base.len() > dest.len()
                && base.starts_with(dest)
                && crate::is_projection_segment_lead(base.as_bytes()[dest.len()]))
    })
}

/// Suffix `guards::push_borrow_slice_len` / `push_unsize_slice_len` /
/// `crate::slice_len_formula` append to a place name to spell its slice-length
/// metadata symbol.
pub(crate) const SLICE_LEN_SUFFIX: &str = "__slice_len";

/// GEN-SET form of [`write_covers_derived_slice_len`], for the analyses that hold
/// a set of written NAMES and test it with [`place_names_overlap`] rather than
/// asking the predicate per (dest, name) pair.
///
/// Trust (P0 false proof — STALE LENGTH TIE, 2026-08-25). `write_covers_derived_slice_len`
/// is applied at STATEMENT granularity (`stmt_writes_name`, `block_def_establish_stmt`),
/// but every gen-set here is built from `formula_def_name` over
/// `extract_block_definitions`. A block whose only write to a slice local is an
/// `Rvalue::Use` — `s = <call dest>`, `s = t` — contributes the def `Eq(Var("s"), ..)`
/// and hence the name `s`, never `s__slice_len`; a BORROW or an array→slice CAST
/// contributes `Eq(Var("s__slice_len"), N)` and so mints the name by itself. The
/// non-cast reassignment therefore left `s__slice_len` ungen'd, the cast block's
/// token stayed the only one reaching the join, and `s__slice_len#<cast> == N` was
/// conjoined onto a path where `s` had been reseated to a different length —
/// certified-PROVED bodies that fault at runtime (measured on `q1_call_dest`,
/// `q2_slice_to_slice`, `q3_loop`, `q4_merge`, `q6_mut_reseat`, `q7_after_len_read`,
/// `q9_store_call`; see `tests/array_unsize_slice_len.rs`).
///
/// Only the `base == dest` branch of the predicate needs a new NAME: the
/// projection-descendant branch is already answered by `place_names_overlap`,
/// because `{dest}.0__slice_len` starts with `dest` followed by the `.` separator.
///
/// Apply to the DIRECT-WRITE channel only — statement/terminator destinations and
/// the slot-write-channel roots ([`own_storage_write_borrow`]) a callee can RESEAT.
/// NOT to
/// `mutable_pointer_local_names`, whose entries are base locals reached at every
/// call in the function and whose own length metadata lives one projection down
/// (`p*__slice_len`, already an overlap of `p`): extending those would havoc a
/// `&mut [T]` parameter's live tie at every call, which is the false REFUTATION
/// `write_covers_derived_slice_len` exists to prevent.
pub(crate) fn extend_with_derived_slice_len(names: &mut FxHashSet<String>) {
    if names.is_empty() {
        return;
    }
    let mut derived: Vec<String> = Vec::with_capacity(names.len());
    for n in names.iter() {
        if !n.ends_with(SLICE_LEN_SUFFIX) {
            derived.push(format!("{n}{SLICE_LEN_SUFFIX}"));
        }
    }
    names.extend(derived);
}

/// [`extend_with_derived_slice_len`] for the `Vec`-shaped havoc/def name lists.
pub(crate) fn push_derived_slice_len(names: &mut Vec<String>, dest: &str) {
    if dest.ends_with(SLICE_LEN_SUFFIX) {
        return;
    }
    names.push(format!("{dest}{SLICE_LEN_SUFFIX}"));
}

/// Trust: 2026-09-16 (round A9/A10) — the `Vec`-shaped twin of the fallback mint in
/// [`extend_with_assigned_place_dests`]: a WHOLE-local write/havoc of `place` also
/// carries the fallback name `_<local>`, through which [`write_rebinds`] reaches every
/// name embedding that local by number as an index (`write_covers_index_segment`). A
/// projected place rebinds no index local, and a local that is never an index operand
/// (`local_is_index_operand`) has no such name to reach: neither mints anything here.
pub(crate) fn push_index_fallback_name(
    func: &VerifiableFunction,
    names: &mut Vec<String>,
    place: &trust_types::Place,
) {
    if !place.projections.is_empty() || !local_is_index_operand(func, place.local) {
        return;
    }
    let fallback = local_fallback_name(place.local);
    if !names.contains(&fallback) {
        names.push(fallback);
    }
}

// =========================================================================
// STALENESS-CLASS S2c Stage 1+2 — THE FLIP rename + the equivalence WITNESS
//
// The flip replaces the kill's "drop a stale fact" with "rename every place
// variable to its versioned form at its program point", so a stale fact and a VC
// name DIFFERENT SMT variables and cannot unify — the kill's effect, achieved by
// name-disjointness instead of per-site discipline.
//
// `version_rename_at` is the rename. `flip_matches_kill_*` is the SOUNDNESS
// WITNESS: it proves, at STATEMENT granularity, that the flip's "does fact φ about
// name n apply at (B, i)?" verdict equals the kill's drop verdict — which AUTHORIZES
// replacing (and ultimately deleting) the kill. The block-level audits could not
// witness this (they are block-blind); this one is statement-exact.
// =========================================================================
/// Rename every place-variable in `formula` to its versioned form at `(block,
/// stmt_idx)`: `Var(n, s)` → `Var("n#token", s)` when `version_token_at` is `Some`,
/// else unchanged (byte-identical for entry/unwritten names). Constants and
/// already-versioned names pass through. This is the mint applied as a formula
/// rewrite at the conjoin boundary — equivalent to threading the version into every
/// operand read, but localized.
pub(crate) fn version_rename_needs_rewrite(
    formula: &Formula,
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: BlockId,
    stmt_idx: usize,
) -> bool {
    trust_types::any_formula_node(formula, &mut |node| match node {
        Formula::Var(name, _) => {
            !name.contains('#') && sv.version_token_at(func, block, stmt_idx, name).is_some()
        }
        _ => false,
    })
}

pub(crate) fn version_rename_at(
    formula: &Formula,
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: BlockId,
    stmt_idx: usize,
) -> Formula {
    version_rename_owned_at(formula.clone(), sv, func, block, stmt_idx)
}

pub(crate) fn version_rename_owned_at(
    formula: Formula,
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: BlockId,
    stmt_idx: usize,
) -> Formula {
    if !version_rename_needs_rewrite(&formula, sv, func, block, stmt_idx) {
        return formula;
    }
    formula.map(&mut |node| match node {
        // Only rename PLACE names (a versioned read); leave synthetic/internal vars
        // (already containing '#', or solver temporaries) alone.
        Formula::Var(name, sort) if !name.contains('#') => {
            match sv.version_token_at(func, block, stmt_idx, &name) {
                Some(tok) => Formula::Var(format!("{name}#{tok}"), sort),
                None => Formula::Var(name, sort),
            }
        }
        other => other,
    })
}

/// SOUNDNESS WITNESS for the flip, at statement granularity. For every block `B`,
/// every program point `stmt_idx`, and every place name `n` written or
/// entry-versioned in scope, assert the flip verdict equals the kill verdict:
///
///   flip says "a fact about `n` from BLOCK ENTRY does NOT apply at (B, i)"
///     ⟺  the statement-granular kill (extract_block_definitions_until) drops it.
///
/// The flip verdict = `is_versioned_stale_at(B, i, n)` (the renamed read differs
/// from the entry-version name). The kill verdict = a write to an overlap of `n`
/// is visible in `stmts[..i]` OR `n` is may-reassigned reaching `B`. Returns the
/// count of disagreements; 0 ⟹ the flip is drop-equivalent to the kill at the
/// CORRECT (statement) granularity — the witness the block-level audit cannot give.
#[cfg(test)]
pub(crate) fn flip_matches_kill_stmt(func: &VerifiableFunction) -> usize {
    let sv = super::stmt_versions_for(func);
    let may = v2_may_reassigned_per_block(func);
    let empty = FxHashSet::default();
    let mut disagreements = 0usize;
    for block in &func.body.blocks {
        let may_b = may.get(&block.id).unwrap_or(&empty);
        // Probe domain at each point: names written so far + entry-may-reassigned +
        // projection probes (parent + `.0` child) so projected facts are checked.
        for stmt_idx in 0..=block.stmts.len() {
            let writes = writes_until(func, block, stmt_idx);
            let mut probes: Vec<String> = writes.iter().cloned().collect();
            probes.extend(may_b.iter().cloned());
            let extra: Vec<String> = probes
                .iter()
                .flat_map(|n| {
                    // Trust (callee-write false-accept sweep): probe the DEREF
                    // spelling too — `r*` is exactly what a pointee read of a
                    // `&mut`/`*mut` param mints, and the confirmed false-accept
                    // was a stale=yes/token=None disagreement ON that spelling
                    // (invisible to the parent/child-field probes alone).
                    let mut v = vec![format!("{n}.0"), format!("{n}*")];
                    if let Some(dot) = n.rfind('.') {
                        v.push(n[..dot].to_string());
                    }
                    v
                })
                .collect();
            probes.extend(extra);
            // The deref spelling of every mut-pointer-carrying / mut-borrowed
            // local — the exact names opaque pointee reads mint — even when the
            // local is not (yet) in the written/may-reassigned sets at this point.
            for base in mutable_pointer_local_names(func)
                .into_iter()
                .chain(mutably_borrowed_local_names(func))
            {
                probes.push(format!("{base}*"));
            }
            for q in &probes {
                let flip_stale = sv.is_versioned_stale_at(func, block.id, stmt_idx, q);
                // Statement-granular kill: a write to an overlap of q in stmts[..i],
                // OR q reachable-reassigned at block entry (the inherited-hypothesis
                // side, which is block-granular by construction in the real kill).
                let writes_overlap = writes.iter().any(|w| write_rebinds(w, q));
                let entry_overlap = !formula_survives_redefs(
                    &Formula::Var(q.clone(), trust_types::Sort::Int),
                    &block_entry_may_reassigned(func, block.id),
                );
                let kill_stale = writes_overlap || entry_overlap;
                if flip_stale != kill_stale {
                    disagreements += 1;
                }
                // Trust (callee-write false-accept sweep) — MINT-CONSISTENCY: a
                // point where the staleness oracle says "a fact about q does not
                // apply here" but the version mint returns `None` (a BARE read)
                // is exactly the bug class that let the guard bound transfer
                // across `bump(r)`: the rename left the stale-scoped read
                // byte-identical to the fact's var. Post-fix this holds by
                // construction (both sides consult `place_names_overlap` over
                // the same write/entry sets); pre-fix it witnesses the p00
                // false-accept (stale=yes, token=None on "r*" after the call).
                if flip_stale && sv.version_token_at(func, block.id, stmt_idx, q).is_none() {
                    disagreements += 1;
                }
            }
        }
    }
    disagreements
}

/// P-C — the WITNESS clause `flip_matches_kill_stmt` was missing: the property the
/// flip's rename ACTUALLY relies on is that two read points straddling a write to
/// `name` get DISTINCT tokens (so a fact at the earlier point cannot unify with the
/// VC body at the later point). `flip_matches_kill_stmt` only checked an
/// overlap-staleness yes/no predicate, so it reported 0 even when the oracle
/// collapsed two writes to one token (the P-A bug). This counts violations of the
/// distinctness property: for every name written by statement `k`, the token just
/// BEFORE `k` must differ from the token just AFTER `k`. 0 ⟹ the oracle actually
/// distinguishes the values the rename must keep apart.
#[cfg(test)]
pub(crate) fn flip_token_distinctness_violations(func: &VerifiableFunction) -> usize {
    let sv = super::stmt_versions_for(func);
    let mut violations = 0usize;
    for block in &func.body.blocks {
        for k in 0..block.stmts.len() {
            // names this statement writes (probe its own dest + havoc).
            let after = writes_until(func, block, k + 1);
            let before = writes_until(func, block, k);
            for name in after.difference(&*before) {
                // `name` newly written at k: token before k vs after k must differ.
                let t_before = sv.version_token_at(func, block.id, k, name);
                let t_after = sv.version_token_at(func, block.id, k + 1, name);
                if t_after == t_before {
                    violations += 1;
                }
            }
        }
    }
    violations
}

/// Names that are may-reassigned at `block`'s ENTRY (the inherited-hypothesis side
/// of the statement-granular kill): a name whose reaching-def version at block
/// entry is non-entry.
#[cfg(test)]
pub(super) fn block_entry_may_reassigned(
    func: &VerifiableFunction,
    block: BlockId,
) -> FxHashSet<String> {
    let entry_only = std::collections::BTreeSet::from([ENTRY_VERSION_SENTINEL.to_string()]);
    super::legacy_version_oracle::block_entry_versions(func)
        .get(&block)
        .map(|m| m.iter().filter(|(_, v)| **v != entry_only).map(|(k, _)| k.clone()).collect())
        .unwrap_or_default()
}

// The RETIRED materialised form of the may-reassigned kill (a Θ(blocks × names)
// forward fixpoint). Its one production consumer — the hardened profile's
// semantic-guard filter — now probes `StmtVersionCtx::may_reassigned_rebinds` (the
// same set, resolved per read over the dominator tree); every other former caller
// passed it to a conjoin that ignores it. Kept as the reference the probe is checked
// against.
//
// The production form carried a step cap with a kill-everything overflow fallback.
// This reference has neither: a reference that could answer with its fallback would
// make the differential compare the probe against something other than the least
// fixpoint (a loud false alarm on a large body, never a silent pass). The iteration
// terminates without one: `incoming` only grows, and a block is re-queued only when
// its `incoming` grew, so there are at most `blocks x names` productive steps.
#[cfg(any(test, feature = "version-oracle-differential"))]
pub(crate) fn v2_may_reassigned_per_block(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, FxHashSet<String>> {
    use std::collections::VecDeque;

    let n = func.body.blocks.len();
    let mut gen_stmt: Vec<FxHashSet<String>> = Vec::with_capacity(n);
    let mut gen_term: Vec<FxHashSet<String>> = Vec::with_capacity(n);
    for block in &func.body.blocks {
        // Extracted def names + raw statement destinations + derived twins +
        // deref-store havoc — the unified write oracle, so the kill and the
        // version map agree by construction (the parity audits demand it).
        let stmt = block_entry_fact_kill_names(func, block);
        let term: FxHashSet<String> = terminator_def_names(func, block).into_iter().collect();
        gen_stmt.push(stmt);
        gen_term.push(term);
    }

    let mut incoming: Vec<FxHashSet<String>> = vec![FxHashSet::default(); n];
    // Seed every block so each propagates its own `gen` set to successors at least
    // once (a reassign-free ancestor never grows a successor's `in`, so seeding
    // only the entry would strand a later block's reassignment).
    let mut queue: VecDeque<usize> = (0..n).collect();
    let mut queued = vec![true; n];

    while let Some(i) = queue.pop_front() {
        queued[i] = false;
        let mut out = incoming[i].clone();
        out.extend(gen_stmt[i].iter().cloned());
        out.extend(gen_term[i].iter().cloned());

        // Propagate across the FULL fact-transport graph (incl. unwind/cleanup
        // edges), matching `v2_path_def_fixpoint`'s enqueue set and the
        // unwind-inclusive entry-version map — a write on the normal path is a
        // reassignment on the cleanup path too. More kill edges is drop-only.
        for succ in
            full_graph_terminator_targets(&func.body.blocks[i].terminator, func.body.blocks[i].id)
        {
            let si = succ.0;
            if si >= n {
                continue;
            }
            let before = incoming[si].len();
            for v in &out {
                incoming[si].insert(v.clone());
            }
            if incoming[si].len() != before && !queued[si] {
                queued[si] = true;
                queue.push_back(si);
            }
        }
    }

    let mut result: FxHashMap<BlockId, FxHashSet<String>> = FxHashMap::default();
    for i in 0..n {
        let mut set = incoming[i].clone();
        set.extend(gen_stmt[i].iter().cloned());
        if !set.is_empty() {
            result.insert(BlockId(i), set);
        }
    }
    result
}

/// Conjoin only those `preconditions` still live at a block onto `formula`,
/// dropping any whose free variables appear in `killed` (the block's
/// may-reassigned set from [`v2_may_reassigned_per_block`]).
/// THE FLIP, wired unconditionally at the precondition-conjoin boundary. It
/// replaces the retired overlap kill: instead of dropping a stale precondition,
/// it renames every place variable in the VC formula to its versioned form at
/// `(block, terminal)`, then conjoins all entry/bare-name preconditions. A
/// precondition about a reassigned place therefore names a different SMT variable
/// from the renamed VC body and cannot constrain it (= the kill's drop, by
/// name-disjointness). Verdict equivalence is guarded by
/// `flip_matches_kill_stmt`, the statement-granular witness.
pub(crate) fn conjoin_preconditions_versioned(
    func: &VerifiableFunction,
    block: BlockId,
    preconditions: &[Formula],
    killed: &FxHashSet<String>,
    formula: Formula,
) -> Formula {
    let _ = killed;
    let sv = super::stmt_versions_for(func);
    conjoin_preconditions_versioned_at_point_inner(
        func,
        &sv,
        block,
        usize::MAX,
        preconditions,
        formula,
        false,
        false,
    )
    .0
}

/// As [`conjoin_preconditions_versioned`], but also returns the exact facts it
/// conjoined onto the (renamed) body — the filtered preconditions. Trust: the
/// obligation recorder mirrors the whole-formula rename onto its stored body/facts,
/// then records a `ConjoinFactsLast { facts }` from THIS return so reconstruction
/// reproduces `And([facts.., renamed_body])` exactly.
pub(crate) fn conjoin_preconditions_versioned_recorded(
    func: &VerifiableFunction,
    block: BlockId,
    preconditions: &[Formula],
    killed: &FxHashSet<String>,
    formula: Formula,
) -> (Formula, Vec<Formula>) {
    conjoin_preconditions_versioned_at_point_recorded(
        func,
        block,
        usize::MAX,
        preconditions,
        killed,
        formula,
    )
}

/// The rename point a row with use point `point` is versioned at in `block`: the
/// statement index itself for a mid-block row, the block terminal otherwise
/// (`usize::MAX` is the terminal-row sentinel). A block id that does not index
/// its own block falls back to `0`, the historical `map_or(0, ..)` of the find.
pub(crate) fn row_rename_point(func: &VerifiableFunction, block: BlockId, point: usize) -> usize {
    // Trust (lane-A CSE): id==index invariant → O(1) indexed lookup; the
    // `.filter` preserves the exact `map_or(0, ..)` fallback of the find.
    let terminal =
        func.body.blocks.get(block.0).filter(|b| b.id == block).map_or(0, |b| b.stmts.len());
    point.min(terminal)
}

/// As [`conjoin_preconditions_versioned_recorded`], but the whole-row rename runs
/// at the row's own USE POINT `point` (clamped to the block terminal; pass
/// `usize::MAX` for a terminator row).
///
/// THE DEFECT THIS CLOSES (false refutation of valid Rust). A per-statement row
/// (`_7 = Rem(x, d)` at `bb[k]`) has its body read versioned at `k`, where a name
/// the block writes only LATER (`d = 0` at `bb[k+1]`) is still BARE (its entry
/// value). Renaming the whole row again at the TERMINAL stamped that bare read
/// with the POST-write token, so the row asked about the value AFTER the write,
/// and every entry fact about the pre-write value (`_5 == (d != 0)`) had to be
/// dropped (`v2_live_path_defs_at_point`) to stay sound — leaving the guard free
/// and the row falsely refuted. Renaming at `k` keeps the read and its facts on
/// the same value. For a terminator row this is byte-identical to before.
pub(crate) fn conjoin_preconditions_versioned_at_point_recorded(
    func: &VerifiableFunction,
    block: BlockId,
    point: usize,
    preconditions: &[Formula],
    killed: &FxHashSet<String>,
    formula: Formula,
) -> (Formula, Vec<Formula>) {
    let _ = killed; // the kill is REPLACED by the version rename (item 3: deleted)
    let sv = super::stmt_versions_for(func);
    conjoin_preconditions_versioned_at_point_inner(
        func,
        &sv,
        block,
        point,
        preconditions,
        formula,
        true,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn conjoin_preconditions_versioned_at_point_inner(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: BlockId,
    point: usize,
    preconditions: &[Formula],
    formula: Formula,
    record: bool,
    prefiltered: bool,
) -> (Formula, Vec<Formula>) {
    use crate::versioned::{Fact, Vc, conjoin_owned};
    let rename_point = row_rename_point(func, block, point);
    // The VC body, renamed to its versioned form at this point; the preconditions
    // carry entry/bare names. They meet ONLY through the typed version-aware
    // boundary `conjoin` (the type-gate, item 2). A precondition about a reassigned
    // place names a different variable than the renamed body and cannot constrain
    // it — the kill's drop, by name-disjointness. Verdict-equivalence proven by
    // `flip_matches_kill_stmt`.
    let renamed = version_rename_owned_at(formula, sv, func, block, rename_point);
    // Read the ties off the SHIPPED spelling, and conjoin them in the SAME bucket as
    // the preconditions — the bucket whose bare place names ARE the entry value.
    // Emitted into the path-def fact stream instead, they would be stamped by this
    // very rename into `pre == post`, the forbidden re-unification.
    let ties = entry_sentinel_ties(func, sv, block, rename_point, &renamed);
    let vc = Vc::versioned(renamed, block);
    // Defense in depth for callers that invoke a lower-level generator without
    // passing through `generate_vcs_impl`'s sanitized function view.
    if record {
        let mut kept: Vec<Formula> = Vec::with_capacity(preconditions.len() + ties.len());
        if prefiltered {
            kept.extend_from_slice(preconditions);
        } else {
            kept.extend(
                preconditions
                    .iter()
                    .filter(|pre| {
                        !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre)
                    })
                    .cloned(),
            );
        }
        // Ties ride the SAME vector so `ob_record_conjoin` mirrors them and obligation
        // reconstruction still reproduces `And([facts.., renamed_body])` exactly.
        kept.extend(ties);
        let mut facts: Vec<Fact> = Vec::with_capacity(kept.len());
        facts.extend(kept.iter().cloned().map(Fact::entry));
        (conjoin_owned(facts, vc), kept)
    } else {
        let mut facts: Vec<Fact> = Vec::with_capacity(preconditions.len() + ties.len());
        if prefiltered {
            facts.extend(preconditions.iter().cloned().map(Fact::entry));
        } else {
            facts.extend(
                preconditions
                    .iter()
                    .filter(|pre| {
                        !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre)
                    })
                    .cloned()
                    .map(Fact::entry),
            );
        }
        facts.extend(ties.into_iter().map(Fact::entry));
        (conjoin_owned(facts, vc), Vec::new())
    }
}

/// Tie each ENTRY-SENTINEL read the in-place-update pin left behind (`n#e`) to the
/// BARE name that denotes the same value in this conjoin bucket: `Eq(n#e, n)`.
///
/// `#e` is minted as a NAME SUFFIX at exactly two sites, both behind the same mint
/// gate (`full_graph_union_is_entry_only` at the minting block): the in-place-update
/// pin (`stamp_entry_valued_recurrent_read`) and, since 2026-09-30, the stale-read
/// seal (`seal_bare_reads`, which spells a read that a point-stamped fact left bare so
/// no later whole-formula rename can re-stamp it). Each mints one only where the read
/// rendered bare, i.e. where `version_token_at` said the value is the function-ENTRY
/// one. A bare place name conjoined HERE is the entry value too (the `Fact::entry`
/// contract). So the tie is an identity between two spellings of one value, not a new
/// hypothesis: it cannot exclude a real execution, and it restores the
/// precondition/type-range connection that a free `#e` costs.
///
/// It is NOT cosmetic. MEASURED on a safe `#[requires(n < 30)] n /= 3; … a[n]` whose
/// use sits past a diamond join: the semantic-guard BFS weakens the establish-
/// versioned sibling `n#s0_0 == n / 3` away, the pinned `n#s0_0 == n#e / 3` is the
/// only carrier, `n#e` occurs once, and the bounds row is FALSELY REFUTED
/// (`n#e = 300`).
///
/// The COLLISION check below and [`entry_sentinel_tie_is_sound`] enumerate every way
/// a tie could be a FALSE equation; each is refused rather than reasoned about.
/// `tests/entry_sentinel_tie_guards.rs` plants the violations and watches them fail.
fn entry_sentinel_ties(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: BlockId,
    terminal: usize,
    renamed: &Formula,
) -> Vec<Formula> {
    entry_sentinel_ties_in_slice(func, sv, block, terminal, std::slice::from_ref(renamed))
}

fn entry_sentinel_ties_in_slice(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: BlockId,
    terminal: usize,
    formulas: &[Formula],
) -> Vec<Formula> {
    let mut seen: FxHashSet<&str> = FxHashSet::default();
    let mut ties: Vec<Formula> = Vec::new();
    for f in formulas {
        trust_types::visit_formula_nodes(f, &mut |node| {
            let Formula::Var(name, sort) = node else { return };
            // EXACT token match: a MIXED join renders `n#e_s1_t` — a partially-entry
            // read, whose tie would be a false cross-path equality.
            let Some((base, tok)) = name.split_once('#') else { return };
            if tok != ENTRY_VERSION_SENTINEL || !seen.insert(name.as_str()) {
                return;
            }
            // COLLISION, the pin's own backstop repeated at this second minting site.
            // `validate_function` does not reserve `#` and `place_to_var_name` permits
            // it, so a caller-built IR may hold a local literally named `n#e`; tying it
            // to `n` would assert a relationship the program does not have.
            if sv.has_hash_local_named(name.as_str()) {
                return;
            }
            if !entry_sentinel_tie_is_sound(func, sv, block, terminal, base) {
                return;
            }
            ties.push(Formula::Eq(
                Box::new(Formula::Var(name.clone(), sort.clone())),
                Box::new(Formula::Var(base.to_string(), sort.clone())),
            ));
        });
    }
    ties
}

/// Trust (2026-09-30, vac Phase 1.1 follow-up): the entry-sentinel ties for `#e`
/// names that reach a row through a RENAME-EXEMPT fact (a semantic assert-passed
/// guard, stamped at its own point and conjoined after the row's rename), minus the
/// ties `formula` already carries.
///
/// [`entry_sentinel_ties`] runs inside the precondition conjoin and reads only the
/// renamed BODY, so a sealed `n#e` that arrives later stayed disconnected from the
/// bare `n` of the precondition bucket. Measured on `-O`
/// `fn r6(mut x: u32) -> u32 requires x < 100 { let t = x; opaque(t); x = 0;
/// opaque(x); t + 100 }` (true): the overflow row carried `t == x#e` and `x < 100`
/// with nothing between them and fell to runtime-checked.
///
/// SOUNDNESS is the existing tie's, unchanged: `n#e` denotes the entry value by the
/// mint gate wherever it was minted, and the tie is admitted only under the same
/// consumer clause [`entry_sentinel_tie_is_sound`] at the row's own rename point —
/// so the bare side it meets is exactly the population the body's ties already meet.
pub(crate) fn entry_sentinel_ties_for_exempt_facts(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: BlockId,
    point: usize,
    facts: &[Formula],
    formula: &Formula,
) -> Vec<Formula> {
    if facts.is_empty() {
        return Vec::new();
    }
    let rename_point = row_rename_point(func, block, point);
    let mut ties = entry_sentinel_ties_in_slice(func, sv, block, rename_point, facts);
    if ties.is_empty() {
        return ties;
    }
    let _ = trust_types::any_formula_node(formula, &mut |node| {
        ties.retain(|t| t != node);
        ties.is_empty()
    });
    ties
}

/// May `Eq(base#e, base)` be asserted at `(block, terminal)`? Two clauses, each
/// closing one way the equation could be FALSE rather than merely uninformative.
/// The division of labor (re-derived 2026-08-29, when the whole-function
/// quantifier was retired):
///
///  * THE MINT GATE OWNS "`base#e` DENOTES THE ENTRY VALUE". `#e` has TWO mint
///    sites — `stamp_entry_valued_recurrent_read`, called only from
///    `pin_in_place_update_reads`, and `seal_bare_reads` (2026-09-30) — and both
///    stamp `#e` only where
///    `full_graph_union_is_entry_only` holds at the MINTING block: the
///    UNWIND-INCLUSIVE reaching union is exactly `{e}`, i.e. no path (normal or
///    unwind) into the mint block writes the base. Everywhere else it stamps the
///    never-tieable `#pre_s{b}_{k}`. So by the time this function sees a `#e`,
///    the symbol denotes the function-entry value BY CONSTRUCTION, no matter
///    which block minted it — which is exactly why the whole-function
///    `entry_map_covers` quantifier this function used to open with could go.
///    That quantifier was BOTH too strong (one droppable `String`'s cleanup
///    cluster vetoed the tie at every consumer of the function) and too weak
///    (a mixed shape where an unwind edge delivers a write into a v2-`{e}`
///    block passed it while `#e` named a post-write value — the measured false
///    proof `no_entry_sentinel_when_an_unwind_path_can_deliver_a_write` pins).
///  * CONSUMER SIDE — the clause owns "BARE MEANS ENTRY WHERE THE TIE LANDS".
///    Tie only where this consumer VERSIONS the base: `version_token_at` Some
///    means the terminal rename (`version_rename_at` stamps every '#'-free var)
///    left NO bare occurrence of the base anywhere in the renamed formula — in
///    particular the pinned def's subject is stamped `base#tok` and cannot
///    coincide with the tie's bare side. The tie's bare side then meets ONLY the
///    `Fact::entry` bucket (preconditions, param ranges), whose contract is that
///    bare names denote entry values. HISTORY: a cleanup consumer used to have
///    an EMPTY v2 entry map (`v2_terminator_targets` had no unwind arm), bare
///    there was the pinned def's POST-write subject, and this clause was the
///    ONLY refusal on that shape. Since 2026-08-30 `block_entry_versions` is
///    unwind-inclusive, a consumer holding a threaded `#e` fact is downstream
///    of the mint block's own write and therefore versions the base, so the
///    clause ADMITS there — the tie is the true identity `entry == entry`
///    (adjudicated in `the_tie_at_a_cleanup_consumer_is_sound_and_no_stale_sibling_is_minted`).
///    WIDENED 2026-09-30 (vac Phase 1.1): a consumer with NO token for the base
///    admits too, when `full_graph_union_is_entry_only(block, base)` holds there.
///    With no token at the point AND an unwind-inclusive reaching union of exactly
///    `{e}` at the consumer block, every bare `base` the rename left is the entry
///    value, so the tie is again `entry == entry`. The two things that could make
///    a bare `base` mean something else are gone: an UNSTAMPED bare def (every
///    point-stamped fact is sealed by `seal_bare_reads` since Phase 0, and the P3
///    whole-deref establish search stamps `(*x) = v` defs), and an in-place-update
///    pin's bare SUBJECT (its write is on every path into the consumer, so the
///    union there is not entry-only). WHY IT IS NEEDED: since Phase 0 seals a
///    guard's entry read (`_2 == self*.0.0#e`) while the consumer — an early-return
///    predecessor that never writes the flag — spells the flag bare, refusing the
///    tie left the two spellings independent and correct `abort_fixed`-shaped
///    code was refuted (`tests/ui/trust/chc-entry-inputs/wedge_refutation_attests.rs`).
///    The refusal is KEPT for the corners where a base can still render bare with
///    `#e` in scope and no entry guarantee: a block the fixpoint never reached, a
///    write index built after a budget trip, and any consumer whose union carries a
///    non-`e` token — `full_graph_union_is_entry_only` fails closed on each.
///  * COLLAPSE. If the base's version tokens all normalize back to the bare name,
///    the tie degenerates to the tautology `x == x`, which the recurrence scanners
///    report as an offending self-referential definition. Nothing is lost: both
///    sides of the tie collapse together, so the connection exists anyway.
///
/// (The COLLISION refusal — a caller-declared local literally named `base#e` —
/// lives in `entry_sentinel_ties` and at the mint site, unchanged.)
fn entry_sentinel_tie_is_sound(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: BlockId,
    terminal: usize,
    base: &str,
) -> bool {
    // Consumer side: a token at the point, or (widened, vac Phase 1.1) no token AND an
    // entry-only reaching union at the consumer block. Nothing else.
    if sv.version_token_at(func, block, terminal, base).is_none()
        && !sv.full_graph_union_is_entry_only(block, base)
    {
        return false;
    }
    let base_local = crate::fn_memo::whole_local_index_by_base(func, base, |l| {
        crate::place_to_var_name(func, &Place::local(l))
    });
    !base_local.is_some_and(|l| discharge::local_versions_collapse_to_bare(func, l))
}

// DELETED (S2c item 3): `conjoin_live_preconditions` — the precondition KILL
// (`preconditions.filter(formula_survives_redefs)`). Replaced everywhere
// (the v2 VC sites AND the hardened lane) by `conjoin_preconditions_versioned`,
// which renames the VC body to its versioned form so a precondition about a
// reassigned place names a different SMT variable and cannot constrain it — the
// kill's drop, by name-disjointness. Verdict-equivalence proven by
// `flip_matches_kill_stmt` (statement-granular, 125 functions, 0 disagreements)
// and validated by the full trust-vcgen suite passing with the flip live.
/// Pin the READS of an IN-PLACE UPDATE (`x = f(x)`) to their pre-write values.
///
/// `extract_block_definitions` renders a def bare, which is correct only while the
/// subject and its reads denote the same value. For an in-place update they do NOT:
/// the lhs `x` is the value AFTER the write, every rhs `x` the value BEFORE it. Bare,
/// they are ONE symbol, and the consuming block's terminal rename stamps both with
/// that block's single live token — minting the recurrence `x#t == f(x#t)`. That is
/// never a statement about the program: it is a tautology (`x == x`) or, for any real
/// update, unsatisfiable/over-constraining (`remain == remain / 10_000` pins `remain`
/// to 0), and one such hypothesis vacuously discharges EVERY obligation it reaches.
/// Measured on `sr_countdown_full[u32;N=10;exact]` — genuinely safe code — where bb3's
/// `remain /= 10_000` flowed bare into the `buf[offset + 1/2/3]` blocks and collapsed
/// to `Eq(remain#s3_6, Div(remain#s3_6, 10000))`.
///
/// So rename the reads at the establishing statement's read-point `k` (their values
/// just BEFORE the write), then put the SUBJECT BACK TO BARE. Leaving the subject bare
/// is what keeps this a pure narrowing rather than a re-wiring:
///   * the consumer's terminal rename still stamps it, so the def connects to the body
///     exactly as it does today (facts are renamed TOGETHER with the body, the
///     connection property the pre-rename conjoin position exists to provide); and
///   * every kill keyed on the def's name — `extend_killing_redefs`/`formula_def_name`
///     here, `v2_live_path_defs` at the consumer — still sees the bare subject and
///     fires unchanged. (`place_names_overlap` cannot match `x#tok` against a bare
///     gen-set name, so versioning the subject would silently render those kills
///     inert; the S2c rule is to add versioning WITHOUT retiring a kill.)
///
/// Only the rhs reads move, and only for a def that reads its own subject. Every other
/// def passes through byte-identical.
///
/// `own_stmt` is the index of the statement that EMITTED `def` (from
/// `guards::extract_block_definitions_indexed`): the establish search is bounded by
/// it, so the read-point is the def's own write, never a later reseat of the subject's
/// ancestor (round A11 — the same bound `version_block_def_at_establish` now takes).
fn pin_in_place_update_reads(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    own_stmt: usize,
    def: Formula,
) -> Formula {
    let Some(subj) = block_def_subject(&def) else { return def };
    // Array term defs (`arr$L$vN`) carry their own version scheme.
    if subj.starts_with("arr$") {
        return def;
    }
    // GEN-KEY == SUBJECT, the invariant this whole repair rests on. The repair
    // rebinds the subject to BARE `subj`, while every kill and version token keyed
    // on this def uses `formula_def_name` — the WHOLE lhs name. `block_def_subject`
    // SPLITS that name at '#' (block_defs.rs:688), so the two disagree exactly when
    // the lhs name contains '#', and then the shipped bare subject names a place the
    // entry-version dataflow never saw written. Repair only where they AGREE.
    //
    // Subsumes the FLOAT case: an `FpFromBits` lhs is not a `Var` at all, so
    // `formula_def_name` is `None` (the kills never watched that subject either —
    // `writes_until` at :787 does not unwrap it). And it closes the '#'-in-a-local-
    // name case: a def of a local literally named `n#x` gens the token for `n#x` yet
    // ships a fact whose subject is `n`. The COLLISION check below refuses only the
    // exact spelling `subj#e`, so that near-miss walked straight past it and left
    // the consumer-side clause of `entry_sentinel_tie_is_sound` as the only refusal
    // standing — see `no_pin_when_the_defs_gen_key_is_not_its_subject`.
    if formula_def_name(&def) != Some(subj) {
        return def;
    }
    let Formula::Eq(_, rhs) = &def else { return def };
    // Only an in-place update needs this: the rhs must READ the subject.
    if !trust_types::any_free_variable_name(rhs, &mut |v| v.split('#').next().unwrap_or(v) == subj)
    {
        return def;
    }
    // The `#e` symbol must be FRESH. `validate_function` does not reserve `#` in
    // local names (lib.rs:492) and `place_to_var_name` permits it (lib.rs:5310),
    // so a caller-constructed `VerifiableFunction` may already hold a local
    // literally named `n#e`. Minting it would then ALIAS a real local and assert
    // a relationship the program does not have — a false proof, not merely a
    // weakening, because `version_rename_at` treats any `#` name as already
    // versioned (:1102) and the collision survives. Fail closed: no repair.
    let has_hash_local = sv.has_any_hash_local();
    if has_hash_local {
        let entry_symbol = format!("{subj}#{ENTRY_VERSION_SENTINEL}");
        if sv.has_hash_local_named(entry_symbol.as_str()) {
            return def;
        }
    }
    // A deref subject `x*` is established here ONLY by the borrow `x = &..` of its
    // base — deliberately not by `def_subject_establish_stmt`, which also finds the
    // store through `x` that this in-place update IS. Pinning `*x = *x + 1` would mint
    // entry-sentinel tokens for a POINTEE, which widens the audited entry-sentinel tie
    // (docs/KNOWN_HAZARDS.md, the OPEN entry on field reads before writes: filed for
    // decision). Unpinned, the def ships the bare recurrence the scanners degrade —
    // fail-closed, never a proof — and `version_block_def_at_establish` still pins it
    // in the threading lane. Pinned by `tests/entry_sentinel_tie_guards.rs`
    // (`a_pointee_in_place_update_mints_no_entry_sentinel`).
    let base = subj.strip_suffix('*').unwrap_or(subj);
    let Some(k) =
        block_def_establish_stmt(func, block, base, (own_stmt + 1).min(block.stmts.len()))
    else {
        return def;
    };
    // THE MINT GATE (entry-denotation guarantee). A read that renders bare at
    // `(block, k)` proves only that the v2 reaching union is empty-or-`{e}`.
    // The v2 map is unwind-inclusive since 2026-08-30, but "empty" still covers
    // a block the fixpoint never reached, and the v2 caller keeps a PARTIAL map
    // when the fixpoint hits its step cap. Stamp `#e` only where the fail-closed
    // full-graph oracle proves the reaching union is exactly `{e}` (converged,
    // reachable, no non-`e` token); then every `#e` in existence denotes the
    // function-entry value BY CONSTRUCTION, which is what licenses
    // `entry_sentinel_tie_is_sound` to run without its whole-function
    // quantifier. Everywhere else stamp the per-point token `#pre_s{block}_{k}`:
    // a FRESH spelling, never the bare def — bare would re-mint the
    // `x#t == f(x#t)` recurrence this pin exists to prevent — and never `#e`.
    // A fresh unconstrained read-symbol is a pure havoc-weakening (the actual
    // pre-write value satisfies it on every trace), and `entry_sentinel_ties`
    // matches the token `e` EXACTLY, so `#pre_…` can never be tied to bare.
    // Guarded by `no_entry_sentinel_when_an_unwind_path_can_deliver_a_write` and
    // `a_cleanup_block_mint_is_stamped_pre_not_entry` (tie_guards).
    let token = if sv.full_graph_union_is_entry_only(block.id, subj) {
        ENTRY_VERSION_SENTINEL.to_string()
    } else {
        format!("{PRE_WRITE_SENTINEL_PREFIX}_s{}_{k}", block.id.0)
    };
    // The chosen spelling must be FRESH — the `#e` collision refusal above,
    // repeated verbatim for the fallback spelling. Fail closed: no repair (the
    // bare recurrence then collapses at the consumer and the scanners DEGRADE
    // the obligation — never a false proof).
    if has_hash_local {
        let minted_symbol = format!("{subj}#{token}");
        if sv.has_hash_local_named(minted_symbol.as_str()) {
            return def;
        }
    }
    let subj = subj.to_owned();
    let read_versioned = version_rename_owned_at(def, sv, func, block.id, k);
    let read_versioned = stamp_entry_valued_recurrent_read(read_versioned, &subj, &token);
    rebind_block_def_subject(read_versioned, &subj, None)
}

/// Give a recurrent read that renders BARE an explicit pre-write token — the entry
/// sentinel `n#e` where the mint gate proved entry-denotation, else `n#pre_s{b}_{k}`.
///
/// `version_token_at` returns `None` — i.e. the bare name — when the value read is
/// the function-ENTRY one, deliberately, so never-havoced parameter reads stay
/// byte-identical across lanes. For an in-place update in the FIRST block that
/// writes the place, that lands the read right back where it started: `n /= 3` at
/// bb1[0] renames its read at point 0, gets `None` (bb1's entry value of `n` IS the
/// parameter), and ships `Eq(n, Div(n, 3))` — whereupon the consumer, whose entry
/// token for `n` is `s1_0`, stamps BOTH occurrences and re-mints
/// `Eq(n#s1_0, Div(n#s1_0, 3))`. Pinning the read at its establish point is
/// therefore only half the fix; MEASURED on
/// `fn f(mut n: u32, a: &[u8; 10]) -> u8 { n /= 3; if n < 10 { a[n as usize] } else { 0 } }`
/// (safe), where it demotes 1 of 1 obligations — fixture
/// `tests/data/entry_block_in_place_update.json`.
///
/// `token` is chosen by the caller's mint gate: `e` (`ENTRY_VERSION_SENTINEL`) only
/// where the unwind-inclusive reaching union proves the pre-write value IS the entry
/// value, else the never-tieable `pre_s{b}_{k}`. Either way the read now names the
/// pre-write value and only that. It is WEAKER than the bare read: bare, it would
/// have unified with any other entry-valued read of the subject; the stamped symbol
/// unifies with nothing else (`#e` only through the guarded tie). That cost is
/// confined to the update's own subject — every OTHER read in the def keeps its bare
/// entry spelling and stays connected — and it buys nothing away, because every
/// block this def flows to is dominated by the write and so reads the subject
/// POST-write anyway.
fn stamp_entry_valued_recurrent_read(def: Formula, subj: &str, token: &str) -> Formula {
    let stamp = |f: Formula| {
        f.map(&mut |node| match node {
            Formula::Var(name, sort) if name == subj => {
                Formula::Var(format!("{name}#{token}"), sort)
            }
            other => other,
        })
    };
    // Read side only: the subject is rebound to BARE immediately after this, and it
    // is the consumer's rename of that bare subject that connects the def to the body.
    match def {
        Formula::Eq(l, r) => Formula::Eq(l, Box::new(stamp(*r))),
        other => other,
    }
}

/// Trust (2026-09-30, stale-read seal — P1 of the `vac` root cause): give every
/// read that `version_rename_at(.., at_block, at_point)` left BARE an explicit
/// spelling, so NO later whole-formula rename can re-stamp it.
///
/// PRECONDITION: `f` came out of `version_rename_at(.., at_block, at_point)`, so a
/// name still bare had no token AT THAT POINT — it denotes the value there (the
/// entry value, or a value the full-graph oracle cannot certify as entry). A bare
/// name is exactly what every LATER rename stamps, with the token of ITS point: a
/// def pinned at its own statement then silently reads the POST-write value. On
/// `s.f = !s.f; s.f` the establish-stamped def `s.f#s0_0 == !s.f` became
/// `s.f#s0_0 == !s.f#s0_0` at the Return-block rename — UNSAT, and every
/// obligation it reached was vacuously proved (`vac`, `vac_ref`, overflow,
/// division and bounds twins).
///
/// Each bare `Var(n)` is spelled:
///  * unchanged when `n` is never versioned anywhere (`ever_versioned` false — no
///    rename can ever stamp it), when it is the return slot (`_0` / `__ret`, whose
///    explicit return pins are stamped by the postcondition lane), or when its whole local's
///    versions all collapse to bare (`local_versions_collapse_to_bare`: every
///    spelling denotes one value, so a re-stamp is an identity);
///  * `n#e` where the SAME mint gate `pin_in_place_update_reads` uses proves the
///    reaching union at `at_block` is exactly `{e}` — it then IS the entry value,
///    and `entry_sentinel_ties` may reconnect it to the preconditions;
///  * else `n#pre_s{at_block}_{at_point}` — fresh, never tieable: a pure
///    weakening, never a false identity.
///
/// `None` (the caller must DROP the fact — fail closed) when the chosen spelling
/// collides with a local literally named so (the `#e` collision refusal of
/// `pin_in_place_update_reads`, repeated).
pub(crate) fn seal_bare_reads(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    at_block: BlockId,
    at_point: usize,
    f: Formula,
) -> Option<Formula> {
    let ret_name = func.body.locals.first().and_then(|l| l.name.as_deref());
    let needs_seal = |name: &str| -> bool {
        if name.contains('#')
            || name == "_0"
            || name == "__ret"
            || ret_name == Some(name)
            || !sv.ever_versioned(func, name)
        {
            return false;
        }
        let whole_local = crate::fn_memo::whole_local_index_by_base(func, name, |l| {
            crate::place_to_var_name(func, &Place::local(l))
        });
        !whole_local.is_some_and(|l| discharge::local_versions_collapse_to_bare(func, l))
    };
    if !trust_types::any_free_variable_name(&f, &mut |name| needs_seal(name)) {
        return Some(f);
    }
    let mut collided = false;
    let sealed = f.map(&mut |node| match node {
        Formula::Var(name, sort) if needs_seal(&name) => {
            let sealed_name = if sv.full_graph_union_is_entry_only(at_block, &name) {
                format!("{name}#{ENTRY_VERSION_SENTINEL}")
            } else {
                format!("{name}#{PRE_WRITE_SENTINEL_PREFIX}_s{}_{at_point}", at_block.0)
            };
            if sv.has_hash_local_named(sealed_name.as_str()) {
                collided = true;
            }
            Formula::Var(sealed_name, sort)
        }
        other => other,
    });
    (!collided).then_some(sealed)
}

/// Thread a block's OWN statement definitions onto `defs` (the block's already-
/// killed entry facts) in STATEMENT ORDER, killing each accumulated own def by every
/// LATER statement's writes before the next def joins — then append them through
/// `extend_killing_redefs` exactly as the one-batch form did for the entry facts.
///
/// Trust: 2026-09-16 (round A11). The batch form `extend_killing_redefs(next_defs,
/// extract_block_definitions(block))` kills only the INCOMING facts: `redefined` is
/// the batch's own `formula_def_name` set, tested against `defs`, and the batch is
/// then appended whole. A def emitted at statement `k` therefore outflowed even when
/// a statement `> k` had rebound its subject through a channel the extraction's
/// clobber walk did not test — and the canonical `j` that set carried never reaches
/// `s*[_4]` (only the fallback `_4` does, via `write_rebinds`). MEASURED: `s[j] = 3;
/// j = k; t[s[j] as usize]` at `-O1` — bb1 `(*_1)[_4] = 3; _4 = copy _3` — outflowed
/// `Eq(s*[_4], 3)` bare to bb2, where the whole-row version rename re-spelled it
/// `s*[_4]#s1_0_s1_1`, the successor-entry UNION token the post-reseat read
/// `_8 = copy (*_1)[_4]` carries too; `_7 == 3 < 4`, UNSAT, PROVED kernel-certified
/// on a program that panics (`store_reseat_read_bug`, with local-array,
/// interval-lane and pointer-reseat twins).
///
/// The rename is performed by [`conjoin_preconditions_versioned_at_point_recorded`];
/// `conjoin_preconditions_versioned_recorded` is now the thin wrapper that calls it
/// with the terminator-row sentinel `point = usize::MAX`. The measurement above is a
/// TERMINATOR row (the bounds `Assert` on `t[s[j] as usize]`), so the token quoted is
/// the one produced by renaming at the block TERMINAL. A mid-block row renames at its
/// own statement index instead ([`row_rename_point`]) and, wherever the row's own
/// block rebinds the name between that index and the terminal, carries a DIFFERENT
/// token for it — so read the spelling as this row kind's instance of the defect, not
/// as the only spelling it has.
///
/// The extraction now drops that def itself (its subject is no longer exempt from
/// the clobber test), so this walk is the SECOND, independent line: for every
/// statement `k` in order, the own defs accumulated so far are killed by `k`'s direct
/// write names (`stmt_direct_write_names`: dest, derived `__slice_len`, index
/// fallback `_l`), by `k`'s opaque deref-store havoc (the per-statement union
/// `writes_until` uses), and by the names the defs of `k` define; only then do `k`'s
/// defs join. Whatever the extraction may one day emit, no own def can cross this
/// block's boundary if any later statement of the block rebinds a name inside or
/// above its subject — which is what makes the union token `version_token_at` mints
/// at the successor a FRESH read symbol (see its inter-block arm).
///
/// The entry facts in `defs` need no per-statement pass: they were already killed
/// by the whole-block `assigned` set (a superset of every per-statement set here)
/// and the whole-block deref-store havoc, before this is called. Cost is therefore
/// `|own defs so far| x |one statement's writes|` per statement — the own-def set is
/// small — and the incoming set is walked once, in the final `extend_killing_redefs`.
/// Drop-only over the batch form, hence monotone: PROVE -> FAIL only.
struct PreparedDefStep {
    defs: Vec<Formula>,
    kill: Option<KillSet>,
}

impl PreparedDefStep {
    fn from_defs(defs: Vec<Formula>) -> Self {
        if defs.is_empty() {
            return Self { defs, kill: None };
        }
        let mut redefined: FxHashSet<String> =
            defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
        extend_with_derived_slice_len(&mut redefined);
        let kill = (!redefined.is_empty()).then(|| KillSet::new(&redefined));
        Self { defs, kill }
    }

    fn apply_to(&self, defs: &mut Vec<Formula>) {
        if self.defs.is_empty() {
            return;
        }
        if !defs.is_empty()
            && let Some(kill) = &self.kill
        {
            defs.retain(|f| {
                let _ = trust_types::verify_budget::budget_exhausted();
                kill.survives(f)
            });
        }
        defs.extend_from_slice(&self.defs);
    }
}

struct StoreHavocKill {
    kill: KillSet,
    projected: FxHashSet<String>,
}

#[derive(Default)]
pub(super) struct PreparedBlockOutflow {
    store_havoc_kill: std::cell::OnceCell<Option<StoreHavocKill>>,
    assigned_kill: std::cell::OnceCell<Option<KillSet>>,
    raw_indexed_defs: std::cell::OnceCell<Vec<(usize, Formula)>>,
    raw_set_discr_defs: std::cell::OnceCell<Vec<Formula>>,
    raw_assert_semantics: std::cell::OnceCell<Vec<Formula>>,
    stmt_and_assert_semantic_facts: std::cell::OnceCell<Vec<Formula>>,
    own_defs: std::cell::OnceCell<PreparedDefStep>,
    set_discr_defs: std::cell::OnceCell<PreparedDefStep>,
    post_term_steps: std::cell::OnceCell<Vec<PreparedDefStep>>,
}

fn compute_threaded_own_defs_from_raw(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: &trust_types::BasicBlock,
    raw_indexed: Vec<(usize, Formula)>,
) -> Vec<Formula> {
    let mut own = raw_indexed.into_iter().peekable();
    if own.peek().is_none() {
        return Vec::new();
    }
    let mut havoc_in_effect: Option<bool> = None;
    let mut acc: Vec<Formula> = Vec::new();
    for (k, stmt) in block.stmts.iter().enumerate() {
        // The defs statement `k` emitted (indices are non-decreasing).
        let mut emitted: Vec<Formula> = Vec::new();
        while let Some((_, d)) = own.next_if(|(i, _)| *i == k) {
            emitted.push(pin_in_place_update_reads(sv, func, block, k, d));
        }
        if !acc.is_empty() {
            let mut redefined: FxHashSet<String> = FxHashSet::default();
            stmt_direct_write_names(func, stmt, &mut redefined);
            if *havoc_in_effect
                .get_or_insert_with(|| !deref_store_havoc_names(func, block).is_empty())
            {
                redefined.extend(deref_store_havoc_names_over(
                    func,
                    block,
                    std::slice::from_ref(stmt),
                ));
            }
            // The names `k`'s own defs define (synthetic lhs like `r*` included),
            // with their derived twins — what `extend_killing_redefs` keyed on.
            for name in emitted.iter().filter_map(formula_def_name) {
                if !name.ends_with(SLICE_LEN_SUFFIX) {
                    redefined.insert(format!("{name}{SLICE_LEN_SUFFIX}"));
                }
                redefined.insert(name.to_string());
            }
            if !redefined.is_empty() {
                // Same per-fact charge as `extend_killing_redefs`: a kill never
                // changes the verdict, the fixpoint's top-of-loop poll does.
                let _ = trust_types::verify_budget::budget_exhausted();
                let kill = KillSet::new(&redefined);
                acc.retain(|f| kill.survives(f));
            }
        }
        acc.extend(emitted);
    }
    // An index at or past `stmts.len()` cannot be emitted; drain defensively so a
    // def is never silently lost (it is still pinned at its own statement).
    for (k, d) in own {
        acc.push(pin_in_place_update_reads(sv, func, block, k, d));
    }
    acc
}

fn thread_own_defs_in_statement_order(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: &trust_types::BasicBlock,
    defs: &mut Vec<Formula>,
) {
    let raw = guards::extract_block_definitions_indexed(func, block);
    let acc = compute_threaded_own_defs_from_raw(func, sv, block, raw);
    extend_killing_redefs(defs, acc);
}

impl PreparedBlockOutflow {
    pub(super) fn extend_raw_def_names(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        names: &mut FxHashSet<String>,
    ) {
        if let Some(cached) = self.raw_indexed_defs.get() {
            names.extend(
                cached.iter().filter_map(|(_, f)| formula_def_name(f)).map(str::to_string),
            );
        } else {
            let defs = self.raw_indexed_defs(func, block);
            names.extend(defs.iter().filter_map(|(_, f)| formula_def_name(f)).map(str::to_string));
        }
        if let Some(cached) = self.raw_set_discr_defs.get() {
            names.extend(cached.iter().filter_map(formula_def_name).map(str::to_string));
        } else {
            let defs = self.raw_set_discr_defs(func, block);
            names.extend(defs.iter().filter_map(formula_def_name).map(str::to_string));
        }
    }

    pub(super) fn raw_indexed_defs(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
    ) -> Vec<(usize, Formula)> {
        if let Some(cached) = self.raw_indexed_defs.get() {
            return cached.clone();
        }
        let defs = guards::extract_block_definitions_indexed(func, block);
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.raw_indexed_defs.set(defs.clone());
        }
        defs
    }

    pub(super) fn raw_set_discr_defs(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
    ) -> Vec<Formula> {
        if let Some(cached) = self.raw_set_discr_defs.get() {
            return cached.clone();
        }
        let defs = extract_set_discriminant_definitions(func, block);
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.raw_set_discr_defs.set(defs.clone());
        }
        defs
    }

    pub(super) fn raw_assert_semantics(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
    ) -> Vec<Formula> {
        if let Some(cached) = self.raw_assert_semantics.get() {
            return cached.clone();
        }
        let defs = guards::extract_assert_passed_semantics(func, block);
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.raw_assert_semantics.set(defs.clone());
        }
        defs
    }

    pub(super) fn stmt_and_assert_semantic_facts(
        &self,
        func: &VerifiableFunction,
        sv: &StmtVersionCtx,
        block: &trust_types::BasicBlock,
    ) -> Vec<Formula> {
        if let Some(cached) = self.stmt_and_assert_semantic_facts.get() {
            return cached.clone();
        }
        let mut block_defs = self.raw_indexed_defs(func, block);
        block_defs.extend(
            self.raw_set_discr_defs(func, block)
                .into_iter()
                .map(|d| (block.stmts.len(), d)),
        );
        let assert_facts = self.raw_assert_semantics(func, block);
        let mut own_guards = Vec::with_capacity(assert_facts.len() + block_defs.len());
        if !assert_facts.is_empty() {
            let assert_k = assert_passed_establish_stmt(func, block).unwrap_or(0);
            for f in assert_facts {
                own_guards.push(version_assert_passed_fact(sv, func, block, assert_k, f));
            }
        }
        for (k, d) in block_defs {
            own_guards.push(version_block_def_at_establish(
                sv,
                func,
                block,
                (k + 1).min(block.stmts.len()),
                d,
            ));
        }
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.stmt_and_assert_semantic_facts.set(own_guards.clone());
        }
        own_guards
    }

    pub(super) fn stmt_and_assert_semantic_facts_uncached(
        func: &VerifiableFunction,
        sv: &StmtVersionCtx,
        block: &trust_types::BasicBlock,
    ) -> Vec<Formula> {
        Self::default().stmt_and_assert_semantic_facts(func, sv, block)
    }

    pub(super) fn compute_post_term_steps_uncached(
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
    ) -> Vec<PreparedDefStep> {
        Self::default().compute_post_term_steps(func, block)
    }

    fn compute_post_term_steps(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
    ) -> Vec<PreparedDefStep> {
        let mut steps = Vec::new();
        let mut push = |defs: Vec<Formula>| {
            if !defs.is_empty() {
                steps.push(PreparedDefStep::from_defs(defs));
            }
        };
        match &block.terminator {
            Terminator::Assert { .. } => {
                push(self.raw_assert_semantics(func, block));
            }
            Terminator::Call { target: Some(_), .. } => {
                if let Some(defs) = super::as_chunks_len::as_chunks_result_len_facts(func, block) {
                    push(defs);
                }
                push(probe_call_definitions(func, block));
                push(eq_unit_call_definitions(func, block));
                push(inferred_pred_call_definitions(func, block));
                push(super::range_index_len::block_range_index_result_len_definitions(func, block));
            }
            _ => {}
        }
        steps
    }

    fn retain_store_havoc(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        next_defs: &mut Vec<Formula>,
    ) {
        if next_defs.is_empty() {
            return;
        }
        if let Some(cached) = self.store_havoc_kill.get() {
            if let Some(sh) = cached {
                next_defs
                    .retain(|f| sh.kill.survives(f) && formula_survives_havoc(f, &sh.projected));
            }
            return;
        }
        let store_havoc = deref_store_havoc_names(func, block);
        let built = (!store_havoc.is_empty()).then(|| {
            let kill = KillSet::havoc(store_havoc.iter());
            let projected: FxHashSet<String> = store_havoc
                .iter()
                .filter(|n| n.bytes().any(crate::is_projection_segment_lead))
                .cloned()
                .collect();
            StoreHavocKill { kill, projected }
        });
        if let Some(sh) = &built {
            next_defs.retain(|f| sh.kill.survives(f) && formula_survives_havoc(f, &sh.projected));
        }
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.store_havoc_kill.set(built);
        }
    }

    fn retain_assigned(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        next_defs: &mut Vec<Formula>,
    ) {
        if next_defs.is_empty() {
            return;
        }
        if let Some(cached) = self.assigned_kill.get() {
            if let Some(kill) = cached {
                next_defs.retain(|f| kill.survives(f));
            }
            return;
        }
        let mut assigned: FxHashSet<String> = FxHashSet::default();
        extend_with_assigned_place_dests(func, &block.stmts, &mut assigned);
        extend_with_derived_slice_len(&mut assigned);
        let built = (!assigned.is_empty()).then(|| KillSet::new(&assigned));
        if let Some(kill) = &built {
            next_defs.retain(|f| kill.survives(f));
        }
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.assigned_kill.set(built);
        }
    }

    fn apply_own_defs(
        &self,
        func: &VerifiableFunction,
        sv: &StmtVersionCtx,
        block: &trust_types::BasicBlock,
        next_defs: &mut Vec<Formula>,
    ) {
        if let Some(step) = self.own_defs.get() {
            step.apply_to(next_defs);
            return;
        }
        let raw = self.raw_indexed_defs(func, block);
        let step =
            PreparedDefStep::from_defs(compute_threaded_own_defs_from_raw(func, sv, block, raw));
        step.apply_to(next_defs);
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.own_defs.set(step);
        }
    }

    fn apply_set_discr_defs(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        next_defs: &mut Vec<Formula>,
    ) {
        if let Some(step) = self.set_discr_defs.get() {
            step.apply_to(next_defs);
            return;
        }
        let step = PreparedDefStep::from_defs(self.raw_set_discr_defs(func, block));
        step.apply_to(next_defs);
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.set_discr_defs.set(step);
        }
    }

    fn apply_post_term_steps(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        normal_outflow: &mut Vec<Formula>,
    ) {
        if let Some(steps) = self.post_term_steps.get() {
            for step in steps {
                step.apply_to(normal_outflow);
            }
            return;
        }
        let steps = self.compute_post_term_steps(func, block);
        for step in &steps {
            step.apply_to(normal_outflow);
        }
        if !trust_types::verify_budget::exhausted_readonly() {
            let _ = self.post_term_steps.set(steps);
        }
    }
}

/// ONE STEP of [`v2_path_def_fixpoint`]: the facts `block` sends along EVERY edge out of
/// it (its BASE outflow), given the facts `next_defs` true on entry to it and the merge
/// facts `seeded` there. The success-only facts of an `Assert` or a `Call` return are not
/// among them; the fixpoint adds those to the edge that carries them.
///
/// Trust (2026-10-15, TRUST-KI-1015-1): split out of the fixpoint unchanged, so that a
/// consumer can read the facts a block sends into a join through the very kills the
/// fixpoint applies, and the two cannot drift.
fn block_base_outflow(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: &trust_types::BasicBlock,
    prepared: Option<&PreparedBlockOutflow>,
    mut next_defs: Vec<Formula>,
    seeded: Option<&[Formula]>,
) -> Vec<Formula> {
    // seed this block's branch-merge Ite as an ENTRY fact — injected
    // before the block's own defs so that a same-block redefinition of one of its
    // free variables kills it. The Ite then flows to successors and is killed /
    // intersected exactly like any other entry fact.
    if let Some(seeded) = seeded {
        extend_killing_redefs(&mut next_defs, seeded.to_vec());
    }
    // Trust (P0 false proof — the OPAQUE DEREF STORE never reached the
    // OUTFLOW). `v2_live_path_defs` drops a block's ENTRY facts that an opaque
    // `*p = v` in that block invalidates, so VCs INSIDE the storing block are
    // sound; this fixpoint applied only the statement-def and terminator kills,
    // so those same facts flowed on to the SUCCESSORS untouched. `block_written_names`
    // (which mints the version tokens) DOES include the deref-store havoc, so the
    // stale fact was renamed to the post-store token by `version_rename_at` and
    // unified with the live read.
    //
    // The straight-line shape hid it — rustc puts the two-branch `&mut` join, the
    // store and the use in ONE block, where the entry kill already applies. Put the
    // use in a LATER block and the fact leaks: `let p = if c { &mut x } else { &mut y };
    // while i < n { *p = 4_000_000_000; i += 1 } x + x` is kernel-certified PROVED
    // while it panics at runtime (`a_scalar_reseat_in_a_loop_still_refutes` in `tests/opaque_deref_store_reseat.rs`).
    //
    // Kills incoming + seeded entry facts only; the block's OWN statement defs are
    // added after and stay. Monotone-sound: dropping a hypothesis turns PROVE into
    // FAIL, never the reverse.
    if let Some(prepared) = prepared {
        prepared.retain_store_havoc(func, block, &mut next_defs);
        prepared.retain_assigned(func, block, &mut next_defs);
        prepared.apply_own_defs(func, sv, block, &mut next_defs);
        prepared.apply_set_discr_defs(func, block, &mut next_defs);
    } else {
        if !next_defs.is_empty() {
            let store_havoc = deref_store_havoc_names(func, block);
            if !store_havoc.is_empty() {
                let kill = KillSet::havoc(store_havoc.iter());
                let projected: FxHashSet<String> = store_havoc
                    .iter()
                    .filter(|n| n.bytes().any(crate::is_projection_segment_lead))
                    .cloned()
                    .collect();
                next_defs.retain(|f| kill.survives(f) && formula_survives_havoc(f, &projected));
            }
        }
        if !next_defs.is_empty() {
            let mut assigned: FxHashSet<String> = FxHashSet::default();
            extend_with_assigned_place_dests(func, &block.stmts, &mut assigned);
            extend_with_derived_slice_len(&mut assigned);
            if !assigned.is_empty() {
                let kill = KillSet::new(&assigned);
                next_defs.retain(|f| kill.survives(f));
            }
        }
        thread_own_defs_in_statement_order(func, sv, block, &mut next_defs);
        extend_killing_redefs(&mut next_defs, extract_set_discriminant_definitions(func, block));
    }
    // loop-backedge: a value the block's TERMINATOR reassigns (a direct
    // `Call { dest: i }` to a user var) is invisible to the statement-based
    // `extract_block_definitions` above, so no killing def is generated. On a
    // back-edge that re-enters a loop header, this strands the pre-loop fact
    // (`i == 0`): the back-edge outflow still carries it, the header
    // intersection does not shrink, and the stale fact survives into the loop
    // body where it vacuously discharges a real overflow on `i`. Mirror the
    // terminator-kill already done in `build_semantic_guard_map` and
    // `v2_may_reassigned_per_block`: drop any outflow fact mentioning a
    // terminator-redefined name before propagating to successors. Dropping a
    // hypothesis is monotone-sound (PROVE -> FAIL only). The terminator runs
    // after this block's own VCs, so recording `result[b]` above stays precise.
    //
    // Trust (2026-10-10, SLICE-LEN-CALL-HAVOC-1): the terminator's havoc LIST is
    // judged under the plain relation, as the deref-store havoc above already is
    // (`TerminatorKill::survives_havoc_plain`); its destination and every other
    // explicitly written name keep the destination relation.
    if !next_defs.is_empty() {
        let kill = sv.terminator_kill(func, block);
        if !kill.is_empty() {
            next_defs.retain(|f| kill.survives_havoc_plain(f));
        }
    }
    next_defs
}

/// Trust (2026-10-15, TRUST-KI-1015-1): what the path-definition fixpoint carries along
/// every edge out of `block` when `entry` holds on entry and nothing is seeded there: the
/// skip edge's facts of an `if` without `else`, as pass 1 of
/// [`v2_build_path_definition_map`] sends them into the join
/// (`guards::skip_edge_join_definitions`). Empty for a block id the body does not have.
pub(crate) fn path_def_base_outflow(
    func: &VerifiableFunction,
    block: BlockId,
    entry: &[Formula],
) -> Vec<Formula> {
    let Some(b) = func.body.blocks.get(block.0).filter(|b| b.id == block) else {
        return Vec::new();
    };
    let sv = super::stmt_versions_for(func);
    let prepared = sv.prepared_block_outflow(func, b);
    block_base_outflow(func, &sv, b, prepared.as_deref(), entry.to_vec(), None)
}

/// Monotone dataflow fixpoint over path-definition facts. `result[b]` converges to
/// the INTERSECTION of every incoming path's accumulated defs — i.e. the facts that
/// hold on *every* execution reaching `b`. Intersection is sound: a fact retained here
/// was present on (hence true along) every path to `b`, so assuming it as a VC
/// hypothesis cannot mask a real violation.
///
/// `seed` injects extra per-block facts (branch-merge Ites) into a block's
/// OUTFLOW at the entry-fact position — *before* the block's own statement defs, so a
/// same-block redefinition of a seeded fact's variable kills it via
/// `extend_killing_redefs`. Seeded facts thereby propagate to descendants under the
/// identical kill+intersection discipline as ordinary block defs: dropped at any block
/// that reassigns one of their free variables, and intersected away at any block the
/// originating block does not dominate.
///
/// This replaced an older "weaken the join to `true` on the second differing path"
/// scheme. That scheme was correct only for VCs *inside* the join block; any block
/// *downstream* of the join had its predecessor defs nuked to `[true]`, dropping
/// dominating facts such as `cmp == (m < 1000)`. A guard like `if m < 1000 { m + 1 }`
/// then carried `cmp == true` with nothing tying `cmp` back to `m`, so the overflow VC
/// false-FAILED with `m = u32::MAX`. The intersection keeps `cmp == (m < 1000)`
/// (established at the join, identical on both arms) so the guard constrains `m` again.
pub(super) fn v2_path_def_fixpoint(
    func: &VerifiableFunction,
    seed: &FxHashMap<BlockId, Vec<Formula>>,
) -> FxHashMap<BlockId, Vec<Formula>> {
    use std::collections::VecDeque;

    let sv = super::stmt_versions_for(func);
    let n = func.body.blocks.len();
    let mut result: FxHashMap<BlockId, Vec<Formula>> =
        FxHashMap::with_capacity_and_hasher(n, Default::default());
    let mut queue: VecDeque<(BlockId, Vec<Formula>)> = VecDeque::from([(BlockId(0), Vec::new())]);

    // The fixpoint terminates on its own — a block's fact set only ever shrinks
    // (intersection) and is re-propagated only when it does — but cap total steps
    // as defence against an unforeseen CFG shape. On overflow fall back to the
    // sound, less precise empty map (VCs then rely on guards/preconditions alone).
    let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(8).saturating_add(4096);
    let mut steps = 0usize;

    while let Some((block_id, incoming)) = queue.pop_front() {
        steps += 1;
        // Trust (2026-09-09): the STEP CAP ABOVE IS NOT A TIME BOUND, and this
        // loop is where that stopped being academic. `cap` is `8n² + 8n + 4096`
        // dequeues. Before adaptive membership indexing, ONE dequeue performed
        // `|existing| × |incoming|` deep structural `Formula` comparisons, so
        // wide fact sets made that cap worth hours. MEASURED on `first-party/ty`'s
        // `tla-cli` (seal trust-9e08c848): two `trustc` processes sat at 99% CPU
        // for 2 h 52 min inside this fixpoint — 172 minutes of CPU each — having
        // emitted nothing since the crate's first minutes, with the ambient
        // per-function budget installed above (`collect_verification_artifacts_
        // inner_with_policy`) and DEAD, because nothing here polled it. That is
        // exactly the defect `trust_types::verify_budget`'s own module doc warns
        // about: "a poll bounds nothing unless a guard is installed above it",
        // and its converse — a guard bounds nothing unless something polls.
        //
        // With an ambient guard installed, both bounds apply, and both degrade
        // the SAME way the step cap
        // already did: the sound, less precise empty map (VCs then rely on
        // guards/preconditions alone). Fewer hypotheses can turn a PROVE into a
        // FAIL, never a FAIL into a PROVE.
        if steps > cap || trust_types::verify_budget::budget_exhausted() {
            return FxHashMap::default();
        }
        if block_id.0 >= n {
            continue;
        }

        let new_defs = match result.get(&block_id) {
            None => incoming,
            Some(existing) => {
                // Keep only facts also present on this newly-arriving path.
                //
                // Trust (2026-10-26): index the incoming facts by borrowed,
                // structural Eq+Hash instead of scanning them for every existing
                // fact. The helper retains order, duplicates and the same budget
                // poll per existing fact; hash collisions still require full Eq.
                let Some(merged) = path_fact_membership::intersect(existing, &incoming) else {
                    return FxHashMap::default();
                };
                if merged.len() == existing.len() {
                    // No shrink ⇒ no new information ⇒ this block has converged.
                    continue;
                }
                merged.into_owned()
            }
        };
        let block = &func.body.blocks[block_id.0];
        // PERF-COMPILER-VCGEN-810: a block with no successor edge sends its outflow
        // nowhere (no arm below enqueues anything for it), so its base outflow was
        // computed and dropped, and its incoming facts were deep-cloned only to keep
        // a copy for that discarded computation. Store them by move and stop.
        if matches!(
            &block.terminator,
            Terminator::Return | Terminator::Unreachable | Terminator::Resume
        ) {
            result.insert(block_id, new_defs);
            continue;
        }
        // `result[b]` stores only the pure incoming intersection (never the seed), so
        // the convergence test above remains a clean monotone shrink and terminates.
        result.insert(block_id, new_defs.clone());

        let prepared = sv.prepared_block_outflow(func, block);
        let next_defs = block_base_outflow(
            func,
            &sv,
            block,
            prepared.as_deref(),
            new_defs,
            seed.get(&block_id).map(Vec::as_slice),
        );

        // `next_defs` is the BASE outflow: facts true after the block and
        // terminator write-kill, regardless of whether a panicking terminator
        // returns normally or transfers to cleanup. Success-only facts must
        // never enter this set.
        let mut base_outflow = next_defs;
        // Only Assert and Call read a separate success-only outflow below.
        // Every other terminator transports base_outflow directly, so cloning
        // and then dropping its whole fact vector does no semantic work.
        // Furthermore, when Assert or Call has no cleanup target (and no
        // non-success discovered clause), base_outflow is not read again, so
        // move it directly into normal_outflow without cloning.
        let mut normal_outflow = match &block.terminator {
            Terminator::Assert { unwind, .. } => {
                if unwind.cleanup_target().is_some() {
                    base_outflow.clone()
                } else {
                    std::mem::take(&mut base_outflow)
                }
            }
            Terminator::Call { target, unwind, .. } => {
                if target.is_none() {
                    Vec::new()
                } else if unwind.cleanup_target().is_some() {
                    base_outflow.clone()
                } else {
                    std::mem::take(&mut base_outflow)
                }
            }
            _ => Vec::new(),
        };
        if matches!(
            &block.terminator,
            Terminator::Assert { .. } | Terminator::Call { target: Some(_), .. }
        ) {
            if let Some(prepared) = prepared.as_deref() {
                prepared.apply_post_term_steps(func, block, &mut normal_outflow);
            } else {
                for step in PreparedBlockOutflow::compute_post_term_steps_uncached(func, block) {
                    step.apply_to(&mut normal_outflow);
                }
            }
        }

        if !matches!(
            &block.terminator,
            Terminator::Goto(_)
                | Terminator::Return
                | Terminator::Unreachable
                | Terminator::Resume
                | Terminator::Drop { .. }
                | Terminator::Call { .. }
        ) {
            // PERF-COMPILER-VCGEN-810: a `SwitchInt`'s arms all carry `base_outflow`
            // and nothing reads it after them (its arm below enqueues nothing), so
            // the LAST arm takes it by move instead of a deep clone. Same targets,
            // same queue order, same facts.
            let block_targets: Vec<BlockId> = block
                .terminator
                .discovered_clauses(block_id)
                .into_iter()
                .filter_map(|guarded| match guarded.target {
                    trust_types::ClauseTarget::Block(target) => Some(target),
                    _ => None,
                })
                .collect();
            let switch = matches!(&block.terminator, Terminator::SwitchInt { .. });
            let last = block_targets.len().saturating_sub(1);
            for (index, target) in block_targets.into_iter().enumerate() {
                // Assert's sole in-CFG discovered clause is its normal-success
                // edge. Switch clauses are ordinary base outflow. A future
                // conditional terminator fails closed to base facts.
                let outflow = match &block.terminator {
                    Terminator::Assert { target: success, .. } if target == *success => {
                        &mut normal_outflow
                    }
                    _ => &mut base_outflow,
                };
                if matches!(&block.terminator, Terminator::Assert { .. })
                    || (switch && index == last)
                {
                    queue.push_back((target, std::mem::take(outflow)));
                } else {
                    queue.push_back((target, outflow.clone()));
                }
            }
        }

        // Faithful unwind transport. Normal Call return receives post-return
        // facts; every cleanup edge receives BASE facts only. Enqueue both when
        // normal and cleanup target the same block: the incoming intersection
        // then deliberately removes success-only facts from that join.
        match &block.terminator {
            Terminator::Call { target, unwind, .. } => {
                if let Some(target) = target {
                    queue.push_back((*target, normal_outflow));
                }
                if let Some(cleanup) = unwind.cleanup_target() {
                    queue.push_back((cleanup, base_outflow));
                }
            }
            Terminator::Assert { unwind, .. } => {
                // The normal target was enqueued through discovered_clauses.
                if let Some(cleanup) = unwind.cleanup_target() {
                    queue.push_back((cleanup, base_outflow));
                }
            }
            Terminator::Goto(target) => {
                // Goto has one edge and no discovered clauses. Transfer its
                // owned facts instead of cloning and then dropping the original.
                queue.push_back((*target, base_outflow));
            }
            Terminator::Drop { target, unwind, .. } => {
                if let Some(cleanup) = unwind.cleanup_target() {
                    queue.push_back((*target, base_outflow.clone()));
                    queue.push_back((cleanup, base_outflow));
                } else {
                    queue.push_back((*target, base_outflow));
                }
            }
            Terminator::Opaque { targets, .. } => {
                if let Some((last, prefix)) = targets.split_last() {
                    for target in prefix {
                        queue.push_back((*target, base_outflow.clone()));
                    }
                    queue.push_back((*last, base_outflow));
                }
            }
            Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Unreachable
            | Terminator::Resume => {}
            // `Terminator` is non-exhaustive across crate boundaries. Unknown
            // future successors receive only base facts, never success facts.
            _ => {
                for target in block.terminator.unguarded_successors() {
                    queue.push_back((target, base_outflow.clone()));
                }
            }
        }
    }

    result
}

#[cfg(test)]
pub(crate) fn v2_build_path_definition_map_pub(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    v2_build_path_definition_map(func)
}

/// Pass 1 of [`v2_build_path_definition_map`] (the converged intersection, nothing
/// seeded): the `incoming` map `guards::branch_merge_definitions` reads.
#[cfg(test)]
pub(crate) fn v2_path_def_pass1_pub(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    v2_path_def_fixpoint(func, &FxHashMap::default())
}

/// Public accessor for the hardened panic-boundary path (`hardened.rs`), which
/// threads cross-block assert-passed result defs (`_N.0 == lhs OP rhs` on the
/// no-overflow success edge) into MIR-assert boundary VCs. Gated under
/// the canonical pipeline like the underlying fixpoint.
pub(crate) fn v2_build_path_definition_map_for_hardened(
    func: &VerifiableFunction,
) -> std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> {
    super::path_definition_map_for(func)
}

/// Conjoin the FULL dominating path-condition onto a hardened panic-boundary VC's
/// `formula` for `block`, using the SAME guard-gathering the per-statement
/// arithmetic/bounds-safety VC uses (`v2_build_path_guard_map` +
/// `v2_formula_with_path_guards`). This carries EVERY branch condition that must
/// hold to reach the assert's block — including NESTED/inner guards (`len >= 8`
/// inside `if len <= 16 { if len >= 8 { … } }`) — in ASSERTED form (the guard's
/// controlling comparison, source-versioned exactly as the body), rather than the
/// `path_map()` first-predecessor accumulation the hardened lane previously used
/// (which surfaced only the OUTER branch guard and dropped the inner one, leaving
/// `bytes[len-8..]`'s `len - 8` unprovable).
///
/// MUST be called AFTER the body has been versioned (the hardened lane's
/// `conjoin_preconditions_versioned`), matching the per-statement ordering — the
/// guards are conjoined EXEMPT from the rename so an entry-derived read (`len`)
/// stays bare and unifies with the renamed body, while an in-block guard read is
/// versioned at the guard's source block.
///
/// SOUNDNESS: `v2_build_path_guard_map` accumulates guards strictly along CFG
/// edges (`discovered_clauses`), so a block receives ONLY the conditions that
/// dominate it — the `len >= 8` arm's assert gets `len >= 8`, while the sibling
/// `else`/`len < 8` arm's assert never does. A saturated / unreachable-by-the-walk
/// block falls back to the unguarded `[Vec::new()]` path (no fabricated fact). The
/// per-block walk enumerates ALL incoming paths disjunctively (`Or` of paths), so
/// an unguarded operand carries no bound and a real overflow/underflow stays
/// SAT/refutable. This is the EXACT machinery the per-statement VC discharges
/// with, so the two lanes carry identical hypotheses.
pub(crate) fn v2_conjoin_path_guards_for_hardened(
    func: &VerifiableFunction,
    block: BlockId,
    formula: Formula,
) -> Formula {
    let guard_paths_map = super::guard_map_for(func);
    match guard_paths_map.get(&block) {
        Some(block_guard_paths) => v2_formula_with_path_guards(
            func,
            &super::stmt_versions_for(func),
            block,
            block_guard_paths,
            formula,
        ),
        None => formula,
    }
}

pub(super) fn v2_build_path_definition_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    // Pass 1: converge the pure path-definition intersection (no seed). `base[b]`
    // holds the facts true on EVERY path reaching `b`.
    let base = v2_path_def_fixpoint(func, &FxHashMap::default());

    // recover the sound branch-merge invariant `x == Ite(..)` for
    // each genuine SwitchInt join. `branch_merge_definitions` reads each switch's
    // incoming dominating values from the converged pass-1 intersection (`base`) to
    // fill if-without-else skip edges, and returns empty for any non-join block. These
    // are computed ONCE from `base` so they are independent of iteration order and free
    // of the merge facts themselves.
    let n = func.body.blocks.len();
    let mut merge_facts: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if n >= 2 {
        let preds = super::block_predecessors_rc_for(func);
        for block_id in (0..n).map(BlockId) {
            if preds[block_id.0].len() < 2 {
                continue;
            }
            let merge = guards::branch_merge_definitions_with_preds(func, block_id, &base, &preds);
            if !merge.is_empty() {
                merge_facts.insert(block_id, merge);
            }
        }
    }

    // route enum-payload facts across a construction join into the
    // matching discriminant-switch arm (the join intersection drops a fact present
    // on only one arm). Keyed by ARM block, so it composes with the join-keyed
    // branch-merge facts above under the same seed+re-attach machinery below.
    for (arm, facts) in guards::enum_construction_demux_definitions(func) {
        merge_facts.entry(arm).or_default().extend(facts);
    }

    // Trust (2026-10-07, MATCH-ARM-CALL-CHAIN): at each variant arm of a
    // discriminant switch on a branch-merged enum, the merge arms that may have
    // built that variant (`sel == 0 || sel == 1` at the `Some` arm). Keyed by arm
    // like the demux facts; see `guards::switch_join_variant_arm_definitions`.
    for (arm, facts) in guards::switch_join_variant_arm_definitions(func) {
        merge_facts.entry(arm).or_default().extend(facts);
    }

    // `coll.last()/.first() == Some` arm ⟹ `len(coll) >= 1`, plus the `_len ==
    // coll_len` ties for each `.len()` call. Seeded like the demux facts so the
    // non-emptiness propagates from the Some-arm to a later `coll.len() - 1`.
    for (block, facts) in guards::slice_last_some_nonempty_definitions(func) {
        merge_facts.entry(block).or_default().extend(facts);
    }

    // Trust (R2 family 2): `slice.get(idx) == Some` arm ⟹ `idx < slice.len()` (the
    // `<[T]>::get` contract). Same seed+kill discipline as the facts above; with the
    // allocation-size axiom this discharges the get-guarded `idx += 1` overflow
    // (bitflags `IterNames::next`, semver `numeric_identifier`).
    for (block, facts) in guards::slice_get_some_index_bound_definitions(func) {
        merge_facts.entry(block).or_default().extend(facts);
    }

    // Trust (VEC-INSERT, 2026-09-25): the pre-mutation region facts of every
    // region-eligible `Vec` base read by `len`/`is_empty`/`deref`/`as_slice` inside its
    // region (`_n == L0`, `_e <=> L0 == 0`, `view_len == L0`; minted with or without an
    // index mutator since MUTREF-VEC-LEN-GUARD-REFUTE-1, 2026-10-12, and only at a return
    // target the call solely enters) and the `binary_search` result bounds (`Ok(i) => i
    // < len`, `Err(i) => i <= len`). Every one is a TRUE point-invariant under the same
    // seed+kill discipline.
    for (block, facts) in super::vec_region_definitions(func) {
        merge_facts.entry(block).or_default().extend(facts);
    }
    for (block, facts) in super::slice_binary_search_result_definitions(func) {
        merge_facts.entry(block).or_default().extend(facts);
    }

    if merge_facts.is_empty() {
        return if trust_types::verify_budget::exhausted_readonly() {
            FxHashMap::default()
        } else {
            base
        };
    }

    // Pass 2: re-run the intersection fixpoint, this time SEEDING each join's Ite into
    // that block's outflow so it propagates to descendants (downstream
    // propagation — e.g. chained `if c1 {x=..} if c2 {y=..}; x+y`, where the join-local
    // Ite for `x` must reach the later block that adds `x + y`). Soundness: the Ite is a
    // genuinely-true fact at the join; propagating a true fact forward under the same
    // kill+intersection discipline as ordinary defs can only turn a false-FAIL into a
    // PROVE for safe code — it can never make a real overflow PROVE, because a true fact
    // cannot contradict a real violation. `extend_killing_redefs` drops the Ite at any
    // block that reassigns one of its free variables (including the guard variables —
    // `Formula::free_variables` recurses into the Ite condition), and the intersection
    // drops it at any block the join does not dominate.
    let mut result = v2_path_def_fixpoint(func, &merge_facts);

    // The seed flows to SUCCESSORS, not into `result[join]` itself (pass 2 stores the
    // pure incoming intersection there). Re-attach each join's own Ite so VCs *inside*
    // the join block still see it — matching the pre-propagation behavior exactly.
    for (block_id, merge) in merge_facts {
        result.entry(block_id).or_default().extend(merge);
    }

    result
}

// LAUNDERED-ALIAS-STORE / LAUNDERED-ALIAS-ELIDE-1 (2026-10-11): synthetic rows for
// `write_havocs_function_list` and the referent fold's raw-pointer `Cast` arm.
#[cfg(test)]
#[path = "laundered_alias_tests.rs"]
mod laundered_alias_tests;

// INTERIOR-MUT-CHANNEL-1 (2026-10-14): the `UnsafeCell` bytes a shared reference or
// borrow reaches — the walk, both halves of the havoc, and the stability scans.
#[cfg(test)]
#[path = "interior_mut_channel_tests.rs"]
mod interior_mut_channel_tests;

#[cfg(test)]
#[path = "union_sibling_write_tests.rs"]
mod union_sibling_write_tests;
