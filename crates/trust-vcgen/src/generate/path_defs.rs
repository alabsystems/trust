// The path definition map -- which definition of each name reaches each
// program point -- and the kill/redefinition analysis behind it. Deref stores
// through a mutable pointer havoc every name the pointer could alias, which is
// why pointer laundering has to be detected before any definition survives.

use super::*;

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
/// projection (`.field` / `[idx]` / `*`-deref) descendant of the other. Writing a
/// whole value invalidates facts about its fields/elements and vice-versa;
/// siblings (`x.0` vs `x.1`) are independent. (Place names are produced by
/// `place_to_var_name`, which spells projections `.0` / `[i]` / `*`.)
pub(crate) fn place_names_overlap(a: &str, b: &str) -> bool {
    if a == b {
        return true;
    }
    fn proj_descendant(longer: &str, ancestor: &str) -> bool {
        longer.len() > ancestor.len()
            && longer.starts_with(ancestor)
            && matches!(longer.as_bytes()[ancestor.len()], b'.' | b'[' | b'*')
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
    false
}

/// True if fact `f` SURVIVES redefinition of the place names in `redefined`: none
/// of `f`'s free variables overlaps any redefined name. Prefix-aware (Trust
/// #soundness round-11), so redefining a whole value `x` also invalidates facts
/// about `x.0` / `x[i]` / `*x` — keying staleness on exact names alone let a
/// stale `x.0 == a` survive `x = move y` and vacuously discharge a VC over the
/// new value's field. Dropping more facts is monotone-sound (PROVE -> FAIL only).
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

/// True iff some FREE variable of `f` overlaps a name in `redefined` (i.e. the fact
/// does NOT survive). Alloc-free, early-exiting twin of the `free_variables`-based
/// check in [`formula_survives_redefs`]. `bound` carries the quantifier-bound names
/// in scope; a `Var`/`SymVar` whose name EXACTLY equals a bound name is excluded
/// from the mention test — mirroring `Formula::free_variables_inner`'s
/// `!bound.contains(name)` binder handling exactly (the overlap test only ever runs
/// on genuinely-free names).
pub(super) fn formula_mentions_redef(
    f: &Formula,
    redefined: &FxHashSet<String>,
    bound: &[&str],
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
        Formula::Var(name, _) => {
            !bound.contains(&name.as_str())
                && redefined.iter().any(|n| {
                    place_names_overlap(name, n) || write_covers_derived_slice_len(n, name)
                })
        }
        // SymVar carries a `Symbol`; resolve to its `&str` for the same name check.
        Formula::SymVar(sym, _) => {
            let name = sym.as_str();
            !bound.contains(&name)
                && redefined.iter().any(|n| {
                    place_names_overlap(name, n) || write_covers_derived_slice_len(n, name)
                })
        }
        // Quantifiers extend the bound set with their binding names; only the body
        // is a sub-formula (the bindings are not). Matches `children()` + the
        // `bound ∪ bindings` recursion in `free_variables_inner`.
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let mut extended: Vec<&str> = bound.to_vec();
            extended.extend(bindings.iter().map(|(sym, _)| sym.as_str()));
            formula_mentions_redef(body, redefined, &extended)
        }
        // Every other node: recurse into its sub-formulas with the same bound set.
        _ => f.children().iter().any(|c| formula_mentions_redef(c, redefined, bound)),
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

pub(crate) fn terminator_def_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<String> {
    match &block.terminator {
        Terminator::Call { func: callee, args, dest, .. } => {
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
            let args_cannot_reach_locals = args.iter().all(|a| match a {
                Operand::Constant(_) => true,
                Operand::Copy(p) => matches!(
                    crate::place_ty_cow(func, p).as_deref(),
                    Some(ty) if ty_is_pure_value(ty)
                ),
                _ => false,
            }) && !func_has_pointer_laundering(func);
            if args_cannot_reach_locals {
                let dest_name = place_to_var_name(func, dest);
                let mut names = vec![dest_name.clone()];
                push_derived_slice_len(&mut names, &dest_name);
                return names;
            }
            // The callee may write its destination AND mutate any local whose
            // mutable reference escapes into it (`f(&mut x)` / `f(&raw mut x)`).
            // soundness (round-11): havocing only the dest left a stale
            // pre-call fact (`x == 5`) live across `f(&mut x)`, vacuously
            // discharging a real overflow on the post-call value. Conservatively
            // havoc every mutably-borrowed local at each Call (dropping a fact only
            // turns PROVE -> FAIL, so it is sound; per-argument PLACE-level
            // points-to (disjoint `&mut` args) is a further completeness
            // refinement. Shared-ref interior mutability
            // is a separate, narrower residual.
            // Trust #soundness (round-12/13): the list also havocs every local whose
            // type TRANSITIVELY contains a mutable reference / raw pointer — a `&mut`/
            // `*mut` PARAMETER, a pointer RETURNED from a call, or one NESTED in an
            // aggregate (`struct Wrapper { p: &mut u32 }`, a tuple/array/closure
            // capture, …). None have a syntactic `&mut x` statement, and the nested
            // case is not even a pointer at the local's top level, so
            // mutably_borrowed_local_names misses them. The callee can mutate the
            // pointee, so we havoc the local's BASE name — its prefix-overlap kills
            // the pointer, its pointee `s*`, and any nested pointee `s.f*`.
            let mut names = function_havoc_names(func).as_ref().clone();
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
            if let Some(refined) =
                callee_write_set::refine_call_havoc_names(func, callee, args, &names)
            {
                names = refined;
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
            let dest_name = place_to_var_name(func, dest);
            names.push(dest_name.clone());
            // Trust (P0 false proof — STALE LENGTH TIE): the callee writes a whole
            // new value into `dest`, so a slice-typed `dest` gets new length
            // metadata. See `extend_with_derived_slice_len`.
            push_derived_slice_len(&mut names, &dest_name);
            names
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
            let mut names = function_havoc_names(func).as_ref().clone();
            names.push(place_to_var_name(func, place));
            let mut dp = place.clone();
            dp.projections.push(trust_types::Projection::Deref);
            names.push(place_to_var_name(func, &dp));
            names
        }
        // Trust #soundness (same sweep): an `Opaque` terminator (Yield /
        // InlineAsm / unlowered constructs that preserve successors) can run
        // arbitrary code — same conservative havoc as a Call (minus a dest,
        // which Opaque does not model). Dropping facts is monotone-sound.
        Terminator::Opaque { .. } => function_havoc_names(func).as_ref().clone(),
        _ => Vec::new(),
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
/// `refine_call_havoc_names` drops only names EQUAL to a replaceable root's base
/// name, so the derived names survive the refinement unchanged.
///
/// Scoped to the EXPLICITLY `&mut`-borrowed roots — `mutable_pointer_local_names`
/// is deliberately NOT extended, for the reason [`extend_with_derived_slice_len`]
/// documents.
fn mutably_borrowed_havoc_names(func: &VerifiableFunction) -> Vec<String> {
    let mut names = mutably_borrowed_local_names(func);
    for i in 0..names.len() {
        let base = names[i].clone();
        push_derived_slice_len(&mut names, &base);
    }
    names
}

/// True if `ty` TRANSITIVELY contains a mutable reference or ANY raw pointer
/// (`&mut`/`*mut`/`*const`) — directly, or nested in a struct/tuple/array/slice
/// field or a closure/coroutine capture. A callee that receives a value of such a
/// type can mutate the pointee through that nested pointer. Shared `&` is NOT
/// recursed into: you cannot obtain a `&mut` through a shared reference, so it
/// cannot drive a mutation (`&UnsafeCell` interior mutability is a separate,
/// noted residual, pinned by fail-closure tests).
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
        Ty::Adt { fields, .. } => fields.iter().any(|(_, t)| ty_contains_mut_pointer(t)),
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
    let mut names: Vec<String> = Vec::new();
    for (local, decl) in func.body.locals.iter().enumerate() {
        if ty_contains_mut_pointer(&decl.ty) {
            let name = place_to_var_name(func, &trust_types::Place { local, projections: vec![] });
            if !names.contains(&name) {
                names.push(name);
            }
        }
    }
    names
}

/// Every local whose MUTABLE reference (`&mut x`, `&raw mut x`) is taken anywhere
/// in `func`. Such a local may be mutated through that reference by a callee, so
/// its accumulated equality/value facts must be havoced across any `Call`.
pub(crate) fn mutably_borrowed_local_names(func: &VerifiableFunction) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            let target = match rvalue {
                Rvalue::Ref { mutable: true, place } => place,
                Rvalue::AddressOf(true, place) => place,
                _ => continue,
            };
            let name = place_to_var_name(func, target);
            if !names.contains(&name) {
                names.push(name);
            }
        }
    }
    names
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
/// by the SCOPE of the extension, not by the store's pointee type: only the
/// EXPLICITLY `&mut`-borrowed roots are extended, and a slice reference cannot be
/// reseated through a pointer that was never derived from `&mut`/`&raw mut` of
/// that place. `mutable_pointer_local_names` stays unextended — those entries are
/// base locals whose own length metadata lives one projection down
/// (`p*__slice_len`, already an overlap of `p`), so extending them would only havoc
/// a `&mut [T]` local's live tie at every element store through an unrelated
/// opaque pointer. Measured: the element-store controls (`&mut T` through a
/// two-branch borrow, `v[i] = x`, a `&mut` element write in a loop, a raw-pointer
/// element store) all keep their proofs under this scoping.
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
    let has_opaque_deref_store =
        crate::havoc_memo::block_has_opaque_store(func, crate::havoc_memo::block_key(block), || {
            block.stmts.iter().any(|stmt| {
                let Statement::Assign { place, .. } = stmt else { return false };
                // Opaque ⟺ the pointer does not fold to a concrete referent — covers the
                // reseated/multi-borrow/param case AND a cast-laundered pointer
                // (`&mut x as *mut`, IntToPtr) whose def `resolve_referent` cannot fold.
                // `deref_pointer_is_opaque` is the strict, name-mint-consistent superset of
                // the old `crate::local_defs::unique_value_def(..).is_none()` check.
                matches!(place.projections.first(), Some(trust_types::Projection::Deref))
                    && crate::deref_pointer_is_opaque(func, place.local)
            })
        });
    if !has_opaque_deref_store {
        return std::rc::Rc::new(Vec::new());
    }
    function_havoc_names(func)
}

/// The whole-function conservative havoc list —
/// `mutably_borrowed_havoc_names(func) ++ mutable_pointer_local_names(func)` —
/// shared behind an `Rc` and computed once per function.
///
/// This is the SINGLE spelling of that union. It was previously open-coded at
/// four sites (`Call`, `Drop`, `Opaque` and the opaque-deref-store gate), which
/// made it four independently-forkable copies of one rule as well as four
/// whole-function rescans; routing them all through here keeps them equal by
/// construction.
pub(super) fn function_havoc_names(func: &VerifiableFunction) -> std::rc::Rc<Vec<String>> {
    crate::havoc_memo::havoc_list(func, || {
        let mut names = mutably_borrowed_havoc_names(func);
        names.extend(mutable_pointer_local_names(func));
        names
    })
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
    let mut redefined: FxHashSet<String> =
        new_defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
    extend_with_derived_slice_len(&mut redefined);
    if !redefined.is_empty() {
        defs.retain(|f| formula_survives_redefs(f, &redefined));
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
    let mut block_defs = guards::extract_block_definitions(func, block);
    block_defs.extend(extract_set_discriminant_definitions(func, block));
    let mut redefined: FxHashSet<String> =
        block_defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
    // Extraction-declined destinations still invalidate entry facts — the write
    // must stay in the kill even where the def was refused (the unified write
    // oracle, see `extend_with_assigned_place_dests`).
    extend_with_assigned_place_dests(func, &block.stmts, &mut redefined);
    extend_with_derived_slice_len(&mut redefined);
    redefined.extend(deref_store_havoc_names(func, block).iter().cloned());
    if redefined.is_empty() {
        return entry_defs.to_vec();
    }
    entry_defs.iter().filter(|f| formula_survives_redefs(f, &redefined)).cloned().collect()
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
/// set-discriminant + opaque-deref-store havoc + terminator defs). NOTE this
/// INCLUDES terminator defs; `v2_may_reassigned_per_block`'s *returned* set
/// excludes them at the defining block (the terminator runs after that block's
/// own VCs), so the shadow audit exempts a block's own terminator def.
pub(crate) fn block_written_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> FxHashSet<String> {
    let mut defs = guards::extract_block_definitions(func, block);
    defs.extend(extract_set_discriminant_definitions(func, block));
    let mut names: FxHashSet<String> =
        defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
    extend_with_assigned_place_dests(func, &block.stmts, &mut names);
    extend_with_derived_slice_len(&mut names);
    names.extend(block_deref_store_havoc_names(func, block));
    names.extend(terminator_def_names(func, block));
    names
}

/// THE UNIFIED WRITE ORACLE: the name of every EXPLICIT place destination in
/// `stmts` (`Assign` / `SetDiscriminant` / `Deinit`), spelled by
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
    for stmt in stmts {
        let place = match stmt {
            Statement::Assign { place, .. }
            | Statement::SetDiscriminant { place, .. }
            | Statement::Deinit { place } => place,
            // Fail-closed contract for every OTHER variant:
            // `Statement::write_effect` is EXHAUSTIVE in trust-types (a new
            // variant fails to compile until classified there). `NoValueWrite`
            // variants write no place; `FailClosedOrBackstopped` variants with
            // no destination place (`Intrinsic`, `CopyNonOverlapping`,
            // `Unsupported`) cannot be captured by ANY place-keyed gen-set and
            // are refused by their own gates (UnsupportedMir degradation, the
            // sep-engine copy rows, the mutable-borrow havoc). The tripwire
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
pub(crate) fn block_entry_fact_kill_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> FxHashSet<String> {
    let mut block_defs = guards::extract_block_definitions(func, block);
    block_defs.extend(extract_set_discriminant_definitions(func, block));
    let mut names: FxHashSet<String> =
        block_defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
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
fn deref_store_havoc_names_over(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmts: &[Statement],
) -> FxHashSet<String> {
    let havoc = deref_store_havoc_names(func, block);
    let mut out: FxHashSet<String> = FxHashSet::default();
    if havoc.is_empty() {
        return out;
    }
    for stmt in stmts {
        let Statement::Assign { place, .. } = stmt else { continue };
        if !matches!(place.projections.first(), Some(trust_types::Projection::Deref))
            || !crate::deref_pointer_is_opaque(func, place.local)
        {
            continue;
        }
        if !opaque_store_confined_to_written_place(func, place) {
            // Unconfined: this statement alone havocs the whole list, so the
            // union is the whole list and nothing further can shrink it.
            return havoc.iter().cloned().collect();
        }
        // Minted with the SAME construction `mutable_pointer_local_names` uses,
        // so the exclusion is name-consistent with the list by construction.
        let store_base = crate::place_to_var_name(
            func,
            &trust_types::Place { local: place.local, projections: Vec::new() },
        );
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

    let mut changed = true;
    let mut guard = 0usize;
    let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(8).saturating_add(4096);
    while changed && guard < cap {
        changed = false;
        guard += 1;
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
/// drop decision is OVERLAP-based (`formula_survives_redefs` → `place_names_overlap`,
/// so a write to whole `x` drops a fact about `x.0`/`x[i]`/`*x`), so the audit
/// probes with the kill's own predicate — not exact membership. Returns the number
/// of UNEXPECTED divergences (a block's own terminator def is exempt: the kill
/// excludes it at the defining block by design). Zero ⟹ versioning is
/// drop-equivalent to the kill on this function over its tracked-name domain.
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
/// verifier-perf: this is a pure function of `(func, block, stmt_idx)` — it does
/// NOT depend on the name being queried — yet `version_token_at` calls it once
/// per (program point x name), so the raw form recomputed the whole prefix
/// analysis O(names) times at every point. Memoized per `(BlockId, stmt_idx)`
/// and shared behind an `Rc`; see `havoc_memo` for why an entry cannot outlive
/// or cross the function it was computed for.
pub(crate) fn writes_until(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_idx: usize,
) -> std::rc::Rc<FxHashSet<String>> {
    crate::havoc_memo::writes_until(func, crate::havoc_memo::block_key(block), stmt_idx, || {
        writes_until_uncached(func, block, stmt_idx)
    })
}

fn writes_until_uncached(
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

/// Inter-block reaching-version oracle. Maps each block to `{name -> set of
/// STATEMENT-GRANULAR OUT tokens}` reaching its entry. An OUT token is
/// `s{pred}_{k}` — the predecessor block and the LAST statement that wrote (or
/// opaque-deref-store HAVOCED) the name — matching the within-block token format
/// in `version_token_at`. This is what lets a fact threaded from a predecessor and
/// versioned at its establish point connect to a LIVE successor read (same token)
/// yet stay name-disjoint from a HAVOCED one (the havoc's later statement gives a
/// distinct token). A block-id-only token (the old encoding) collapsed a
/// predecessor's establishing write and its havoc to one token, which is why the
/// inter-block threading kill could not be replaced by versioning before.
pub(crate) fn block_entry_versions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, FxHashMap<String, std::collections::BTreeSet<String>>> {
    let n = func.body.blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, b) in func.body.blocks.iter().enumerate() {
        // UNWIND-INCLUSIVE predecessor edges, matching the fact-transport graph
        // (`v2_path_def_fixpoint` transports facts across cleanup edges): a
        // cleanup-only-reachable block must NOT render its reads bare when a
        // normal-path write precedes the unwind — bare is exactly what let a
        // rename-exempt entry precondition unify across a dropped-def write on
        // the unwind shape (`tests/dropped_def_write_visibility.rs`). Extra
        // predecessor edges only ADD reaching tokens, moving reads AWAY from
        // the bare/entry rendering — rename-exempt bare facts can only LOSE
        // unification points (monotone-sound).
        for t in full_graph_terminator_targets(&b.terminator, b.id) {
            if t.0 < n {
                preds[t.0].push(i);
            }
        }
    }
    entry_versions_fixpoint(func, &preds).0
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
    source: BlockId,
) -> Vec<BlockId> {
    let mut targets: Vec<BlockId> = terminator.unguarded_successors();
    for clause in terminator.discovered_clauses(source) {
        if let trust_types::ClauseTarget::Block(target) = clause.target {
            targets.push(target);
        }
    }
    targets.extend(v2_terminator_targets(terminator));
    targets.sort_unstable_by_key(|t| t.0);
    targets.dedup();
    targets
}

/// FAIL-CLOSED sibling of [`block_entry_versions`]: the same reaching-version
/// fixpoint over the same unwind-inclusive predecessor relation (since
/// 2026-08-30 both build their edges from `full_graph_terminator_targets`; this
/// one predates that adoption). Under this map, a name whose reaching union at a
/// block is exactly `{e}` has NO writer on ANY runtime path into the block, normal
/// or unwind — the entry-denotation guarantee the `#e` mint gate in
/// `pin_in_place_update_reads` requires. The remaining difference is convergence
/// semantics: `None` when the fixpoint hit its step cap without converging; the
/// sole consumer fails closed on `None` (no `#e` minted), while the v2 caller
/// keeps its historical partial-map behavior.
pub(crate) fn block_entry_versions_full_graph(
    func: &VerifiableFunction,
) -> Option<FxHashMap<BlockId, FxHashMap<String, std::collections::BTreeSet<String>>>> {
    let n = func.body.blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, b) in func.body.blocks.iter().enumerate() {
        for t in full_graph_terminator_targets(&b.terminator, b.id) {
            if t.0 < n {
                preds[t.0].push(i);
            }
        }
    }
    let (map, converged) = entry_versions_fixpoint(func, &preds);
    converged.then_some(map)
}

/// The shared fixpoint of [`block_entry_versions`] and
/// [`block_entry_versions_full_graph`]; only the predecessor relation differs.
/// The second return is CONVERGENCE: `false` iff the step cap was hit while the
/// in-sets were still changing, OR the ambient verify budget tripped and the
/// walk was abandoned (the v2 caller keeps its historical behavior of using the
/// partial map; the full-graph caller fails closed). On a budget trip the
/// caller's own post-generation checkpoint discards the function's whole
/// inventory, so no row built on a partial map can be kept — see the poll.
fn entry_versions_fixpoint(
    func: &VerifiableFunction,
    preds: &[Vec<usize>],
) -> (FxHashMap<BlockId, FxHashMap<String, std::collections::BTreeSet<String>>>, bool) {
    use std::collections::BTreeSet;
    let n = func.body.blocks.len();
    // The gen-sets, the name universe and the per-block OUT tokens are a pure
    // function of `func` (see `EntryVersionGenSets`), so both callers share one
    // build. `None` = the ambient budget tripped mid-precompute; the whole
    // fixpoint is abandoned rather than run against a short gen-set.
    let Some(precomputed) = entry_version_gen_sets(func) else {
        return (FxHashMap::default(), false);
    };
    let EntryVersionGenSets { gen_sets, all_names, gen_out } = precomputed.as_ref();
    let sentinel = || BTreeSet::from([ENTRY_VERSION_SENTINEL.to_string()]);
    let entry_in: FxHashMap<String, BTreeSet<String>> =
        all_names.iter().map(|nm| (nm.clone(), sentinel())).collect();
    let mut in_sets: Vec<FxHashMap<String, BTreeSet<String>>> = vec![FxHashMap::default(); n];
    if n > 0 {
        in_sets[0] = entry_in.clone();
    }
    let mut changed = true;
    let mut guard = 0usize;
    let mut budget_tripped = false;
    let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(8).saturating_add(4096);
    while changed && guard < cap {
        changed = false;
        guard += 1;
        for b in 0..n {
            // BUDGET POLL (`-Ztrust-verify-function-budget-{ms,steps}`). This
            // loop had none, and `cap` alone is `8n^2 + 8n + 4096` ROUNDS over
            // `n` blocks x predecessor edges x live names — measured, a budgeted
            // run of `nn-core` sat 10+ minutes here with the budget LIVE and
            // correctly reporting 'timed out' elsewhere, because the checkpoint
            // that reports an overrun sits AFTER generation returns and
            // generation never returned.
            //
            // Per BLOCK, not merely per round: one round of a large CFG is
            // itself long enough to be the whole overrun.
            //
            // Breaking out is the ONLY sound degradation. A reaching-version
            // oracle may not hand back a truncated answer — a SHORT reaching
            // set is a short kill set, which lets a stale fact survive and
            // vacuously discharge a real obligation (a false PROVE) — so the
            // in-sets are left exactly as computed and the result is reported
            // NOT CONVERGED. `block_entry_versions_full_graph` already fails
            // closed on that (no `#e` is minted anywhere in the function), and
            // the caller in `rustc_mir_transform::trust_verify` observes the
            // spent budget at its existing checkpoint and applies the
            // discipline `d9d9d675e3` landed: advisory warns and substitutes
            // one COUNTED `Unknown` with the partial VCs discarded wholesale,
            // strict/certify/memory-safe keep the located hard error. This adds
            // a poll to an existing mechanism; it does not introduce a second.
            if trust_types::verify_budget::budget_exhausted() {
                budget_tripped = true;
                break;
            }
            // verifier-perf: ACCUMULATE into `in_sets[b]` instead of rebuilding
            // it. This was `let mut new_in = ...; for p { for (nm, s) in
            // out_of(p, &in_sets[p]) { new_in.entry(nm).or_default().extend(s) }
            // }; if new_in != in_sets[b] { in_sets[b] = new_in }` — which, for
            // EVERY (round x block x predecessor edge), materialized a whole
            // intermediate `FxHashMap<String, BTreeSet<String>>` (`out_of`),
            // deep-cloned every name and every token into a second one
            // (`new_in`), and then compared two full maps. That churn was the
            // #1 self-time leaf of a stack sample of the wedged `nn-core`
            // generator, with `HashMap<String, BTreeSet<String>>`'s
            // `reserve_rehash` and `insert` the #2 and #3.
            //
            // WHY ACCUMULATING IS EXACTLY THE SAME COMPUTATION. The transfer is
            // MONOTONE and the in-sets only ever GROW, so `new_in` was always a
            // SUPERSET of the `in_sets[b]` it replaced. Induction: every in-set
            // starts empty (block 0 starts at `entry_in`); block `b`'s stored
            // value is `F_b` applied to an EARLIER, componentwise-smaller state,
            // and `F_b` is monotone, so re-applying it to the current state can
            // only add. Hence `new_in == in_sets[b] union contributions`, and
            // `new_in != in_sets[b]` holds exactly when some contribution was
            // absent — which is what `additions` records. Block 0's `entry_in`
            // seed is already contained in `in_sets[0]` (it is its initial
            // value, and it only grows), so dropping the per-visit reseed drops
            // nothing.
            //
            // The two contribution families are `out_of`'s two arms verbatim:
            // for each name in `all_names`, the singleton `{gen_out[p][nm]}`
            // when `p` gens it, else `in_sets[p][nm]` when present. `gen_sets[p]`
            // is a subset of `all_names` by construction (`all_names` is their
            // union) and every in-set key is an `all_names` key by the same
            // induction, so iterating the two families visits exactly the pairs
            // `out_of` emitted and nothing else.
            //
            // The read phase borrows `in_sets` immutably throughout, so a
            // SELF-LOOP (`p == b`) reads block `b`'s pre-visit value — exactly
            // what `out_of(b, &in_sets[b])` did.
            let mut additions: Vec<(String, String)> = Vec::new();
            for &p in &preds[b] {
                for nm in &gen_sets[p] {
                    let tok = &gen_out[p][nm];
                    if !in_sets[b].get(nm).is_some_and(|have| have.contains(tok)) {
                        additions.push((nm.clone(), tok.clone()));
                    }
                }
                for (nm, s) in &in_sets[p] {
                    if gen_sets[p].contains(nm) {
                        continue;
                    }
                    let have = in_sets[b].get(nm);
                    for tok in s {
                        if !have.is_some_and(|h| h.contains(tok)) {
                            additions.push((nm.clone(), tok.clone()));
                        }
                    }
                }
            }
            if !additions.is_empty() {
                for (nm, tok) in additions {
                    in_sets[b].entry(nm).or_default().insert(tok);
                }
                changed = true;
            }
        }
        if budget_tripped {
            break;
        }
    }
    let map = func.body.blocks.iter().enumerate().map(|(i, b)| (b.id, in_sets[i].clone())).collect();
    // A budget trip is NOT convergence even when the interrupted round happened
    // to change nothing: the remaining blocks of that round were never visited.
    (map, !changed && !budget_tripped)
}

/// The predecessor-INDEPENDENT half of [`entry_versions_fixpoint`].
///
/// `preds` is consulted nowhere in building these three, yet the fixpoint runs
/// TWICE per function — once from [`block_entry_versions`] and once from
/// [`block_entry_versions_full_graph`], differing ONLY in the predecessor
/// relation — so they were built identically twice. The second build is the
/// expensive one to repeat: `gen_out` is an O(blocks x names x statements)
/// `stmt_writes_name` scan.
struct EntryVersionGenSets {
    /// The names each block writes (`block_written_names`), by block index.
    gen_sets: Vec<FxHashSet<String>>,
    /// Their union — the fixpoint's whole name universe.
    all_names: FxHashSet<String>,
    /// Each block's OUT token per gen'd name, constant across the fixpoint.
    gen_out: Vec<FxHashMap<String, String>>,
}

/// Build (or reuse) the precompute above. `None` iff the ambient verify budget
/// tripped part-way, in which case NOTHING is memoized — see
/// `crate::havoc_memo::entry_gen_sets` for why a truncated one may never be
/// stored or returned.
fn entry_version_gen_sets(func: &VerifiableFunction) -> Option<std::rc::Rc<EntryVersionGenSets>> {
    crate::havoc_memo::entry_gen_sets(func, || {
        let gen_sets: Vec<FxHashSet<String>> =
            func.body.blocks.iter().map(|b| block_written_names(func, b)).collect();
        let all_names: FxHashSet<String> = gen_sets.iter().flatten().cloned().collect();
        // Precompute each block's OUT token per gen'd name (constant across the
        // fixpoint): the last statement writing/havocing the name, else a terminator
        // marker `s{b}_t` for a name the block's TERMINATOR defines (Call dest).
        let mut gen_out: Vec<FxHashMap<String, String>> = Vec::with_capacity(func.body.blocks.len());
        for (bi, b) in func.body.blocks.iter().enumerate() {
            // BUDGET POLL: this walk is O(names x statements) per block with a
            // whole-block `stmt_writes_name` scan inside, so it is its own
            // overrun channel. Abandoning it returns `None` all the way out —
            // a PARTIAL `gen_out` is not a cheaper answer, it is a WRONG one
            // (a missing OUT token is a missing kill), so it is never built,
            // never cached, and never handed to the fixpoint.
            if trust_types::verify_budget::budget_exhausted() {
                return None;
            }
            // The block's TERMINATOR writes (a `Call` dest + escaping `&mut`s) run
            // AFTER every statement, so a name it reassigns has its OUT token pinned
            // to the terminator marker `s{b}_t` — DISTINCT from any statement
            // establish token, so a fact established at a statement and threaded to a
            // successor is name-disjoint from the post-terminator value. Without this
            // the OUT token would be the last STATEMENT write (`stmt_writes_name`
            // cannot see the terminator), and a stale pre-call fact would re-unify
            // with the post-call read (the case `terminator_def_names` defends).
            let term_defs = terminator_def_names(func, b);
            gen_out.push(
                gen_sets[bi]
                    .iter()
                    .map(|nm| {
                        let tok = if term_defs.iter().any(|t| place_names_overlap(t, nm)) {
                            format!("s{}_t", b.id.0)
                        } else {
                            match (0..b.stmts.len())
                                .rev()
                                .find(|&k| stmt_writes_name(func, b, k, nm))
                            {
                                Some(k) => format!("s{}_{k}", b.id.0),
                                None => format!("s{}_t", b.id.0),
                            }
                        };
                        (nm.clone(), tok)
                    })
                    .collect(),
            );
        }
        Some(EntryVersionGenSets { gen_sets, all_names, gen_out })
    })
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
///   * a leading `Deref` with a NON-EMPTY, all-constant-`Field` path after it (a
///     whole-pointee store `*p = v` has no sibling to spare; a symbolic `Index`
///     may hit any slot; a nested `Deref` re-opens aliasing; a `Downcast` makes
///     the field's location variant-dependent),
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
    // matching `is_out_param_place`.
    let mut decls = func.body.locals.iter().filter(|d| d.index == place.local);
    let Some(decl) = decls.next() else { return false };
    if decls.next().is_some() {
        return false;
    }
    let mut ty: &trust_types::Ty = match &decl.ty {
        trust_types::Ty::Ref { inner, .. } => inner,
        trust_types::Ty::RawPtr { pointee, .. } => pointee,
        _ => return false,
    };
    for proj in rest {
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
/// direct `Assign`/`SetDiscriminant` dest, or an opaque deref-store (`*p = v` with
/// `p` non-canonicalizable) that havocs `name`. The single-statement test the
/// version token needs (vs the cumulative `writes_until`, which collapses two
/// same-block writes to one token).
pub(super) fn stmt_writes_name(
    func: &VerifiableFunction,
    bb: &trust_types::BasicBlock,
    k: usize,
    name: &str,
) -> bool {
    let Some(stmt) = bb.stmts.get(k) else { return false };
    match stmt {
        Statement::Assign { place, .. } => {
            let dest = crate::place_to_var_name(func, place);
            if place_names_overlap(&dest, name) || write_covers_derived_slice_len(&dest, name) {
                return true;
            }
            if !matches!(place.projections.first(), Some(trust_types::Projection::Deref))
                || !crate::deref_pointer_is_opaque(func, place.local)
            {
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
                    .any(|h| place_names_overlap(h, name));
            }
            havoc.iter().any(|h| place_names_overlap(h, name))
        }
        Statement::SetDiscriminant { place, .. } => {
            place_names_overlap(&crate::place_to_var_name(func, place), name)
        }
        // `Deinit` invalidates its place. With Deinit dests in the gen-sets
        // (`extend_with_assigned_place_dests`), the token search must find the
        // statement — gate/search parity, keeping the `s{b}_pre` phantom arm of
        // `version_token_at` unreachable for union-admitted names. Deliberately
        // NOT an establish point (`block_def_establish_stmt` unchanged — a
        // deinit defines nothing).
        Statement::Deinit { place } => {
            let dest = crate::place_to_var_name(func, place);
            place_names_overlap(&dest, name) || write_covers_derived_slice_len(&dest, name)
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
                && matches!(base.as_bytes()[dest.len()], b'.' | b'[' | b'*'))
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
/// the explicitly `&mut`-borrowed roots a callee can RESEAT. NOT to
/// `mutable_pointer_local_names`, whose entries are base locals reached at every
/// call in the function and whose own length metadata lives one projection down
/// (`p*__slice_len`, already an overlap of `p`): extending those would havoc a
/// `&mut [T]` parameter's live tie at every call, which is the false REFUTATION
/// `write_covers_derived_slice_len` exists to prevent.
pub(crate) fn extend_with_derived_slice_len(names: &mut FxHashSet<String>) {
    let derived: Vec<String> = names
        .iter()
        .filter(|n| !n.ends_with(SLICE_LEN_SUFFIX))
        .map(|n| format!("{n}{SLICE_LEN_SUFFIX}"))
        .collect();
    names.extend(derived);
}

/// [`extend_with_derived_slice_len`] for the `Vec`-shaped havoc/def name lists.
pub(crate) fn push_derived_slice_len(names: &mut Vec<String>, dest: &str) {
    if dest.ends_with(SLICE_LEN_SUFFIX) {
        return;
    }
    names.push(format!("{dest}{SLICE_LEN_SUFFIX}"));
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
pub(crate) fn version_rename_at(
    formula: &Formula,
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: BlockId,
    stmt_idx: usize,
) -> Formula {
    formula.clone().map(&mut |node| match node {
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
                let writes_overlap = writes.iter().any(|w| place_names_overlap(w, q));
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
            for name in after.difference(&before) {
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
    block_entry_versions(func)
        .get(&block)
        .map(|m| m.iter().filter(|(_, v)| **v != entry_only).map(|(k, _)| k.clone()).collect())
        .unwrap_or_default()
}

// Trust: ungated — both the v2 VC sites and the hardened profile conjoin
// preconditions and need this kill to avoid threading a stale entry contract.
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

    // Monotone (sets only grow) so the fixpoint terminates; cap total steps as
    // defence against an unforeseen CFG shape. On overflow fall back below to the
    // maximal kill (every variable reassigned anywhere) — sound, less precise.
    let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(8).saturating_add(4096);
    let mut steps = 0usize;
    let mut overflowed = false;

    while let Some(i) = queue.pop_front() {
        queued[i] = false;
        steps += 1;
        if steps > cap {
            overflowed = true;
            break;
        }
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
    if overflowed {
        // Sound fallback: kill any precondition mentioning ANY variable reassigned
        // anywhere in the function, at every block. Over-approximates the live set
        // (may introduce false-FAILs) but never threads a stale precondition.
        let mut all: FxHashSet<String> = FxHashSet::default();
        for s in gen_stmt.iter().chain(gen_term.iter()) {
            all.extend(s.iter().cloned());
        }
        if !all.is_empty() {
            for i in 0..n {
                result.insert(BlockId(i), all.clone());
            }
        }
        return result;
    }

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
    conjoin_preconditions_versioned_recorded(func, block, preconditions, killed, formula).0
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
    use crate::versioned::{Fact, Vc, conjoin};
    let _ = killed; // the kill is REPLACED by the version rename (item 3: deleted)
    let sv = super::stmt_versions_for(func);
    // Trust (lane-A CSE): id==index invariant → O(1) indexed lookup; the
    // `.filter` preserves the exact `map_or(0, ..)` fallback of the find.
    let terminal =
        func.body.blocks.get(block.0).filter(|b| b.id == block).map_or(0, |b| b.stmts.len());
    // The VC body, renamed to its versioned form at this point; the preconditions
    // carry entry/bare names. They meet ONLY through the typed version-aware
    // boundary `conjoin` (the type-gate, item 2). A precondition about a reassigned
    // place names a different variable than the renamed body and cannot constrain
    // it — the kill's drop, by name-disjointness. Verdict-equivalence proven by
    // `flip_matches_kill_stmt`.
    let renamed = version_rename_at(&formula, &sv, func, block, terminal);
    // Read the ties off the SHIPPED spelling, and conjoin them in the SAME bucket as
    // the preconditions — the bucket whose bare place names ARE the entry value.
    // Emitted into the path-def fact stream instead, they would be stamped by this
    // very rename into `pre == post`, the forbidden re-unification.
    let ties = entry_sentinel_ties(func, &sv, block, terminal, &renamed);
    let vc = Vc::versioned(renamed, block);
    // Defense in depth for callers that invoke a lower-level generator without
    // passing through `generate_vcs_impl`'s sanitized function view.
    let mut kept: Vec<Formula> = preconditions
        .iter()
        .filter(|pre| !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre))
        .cloned()
        .collect();
    // Ties ride the SAME vector so `ob_record_conjoin` mirrors them and obligation
    // reconstruction still reproduces `And([facts.., renamed_body])` exactly.
    kept.extend(ties);
    let facts: Vec<Fact> = kept.iter().cloned().map(Fact::entry).collect();
    (conjoin(&facts, vc), kept)
}

/// Tie each ENTRY-SENTINEL read the in-place-update pin left behind (`n#e`) to the
/// BARE name that denotes the same value in this conjoin bucket: `Eq(n#e, n)`.
///
/// `stamp_entry_valued_recurrent_read` is the only site in the crate that mints `#e`
/// as a NAME SUFFIX, and it mints one only where the read rendered bare, i.e. where
/// `version_token_at` said the value is the function-ENTRY one. A bare place name
/// conjoined HERE is the entry value too (the `Fact::entry` contract). So the tie is
/// an identity between two spellings of one value, not a new hypothesis: it cannot
/// exclude a real execution, and it restores the precondition/type-range connection
/// that a free `#e` costs.
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
    let mut seen: FxHashSet<String> = FxHashSet::default();
    let mut ties: Vec<Formula> = Vec::new();
    renamed.visit(&mut |node| {
        let Formula::Var(name, sort) = node else { return };
        // EXACT token match: a MIXED join renders `n#e_s1_t` — a partially-entry
        // read, whose tie would be a false cross-path equality.
        let Some((base, tok)) = name.split_once('#') else { return };
        if tok != ENTRY_VERSION_SENTINEL || !seen.insert(name.clone()) {
            return;
        }
        // COLLISION, the pin's own backstop repeated at this second minting site.
        // `validate_function` does not reserve `#` and `place_to_var_name` permits
        // it, so a caller-built IR may hold a local literally named `n#e`; tying it
        // to `n` would assert a relationship the program does not have.
        if func.body.locals.iter().any(|l| l.name.as_deref() == Some(name.as_str())) {
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
    ties
}

/// May `Eq(base#e, base)` be asserted at `(block, terminal)`? Two clauses, each
/// closing one way the equation could be FALSE rather than merely uninformative.
/// The division of labor (re-derived 2026-08-29, when the whole-function
/// quantifier was retired):
///
///  * THE MINT GATE OWNS "`base#e` DENOTES THE ENTRY VALUE". `#e` has ONE mint
///    site — `stamp_entry_valued_recurrent_read`, called only from
///    `pin_in_place_update_reads` — and that site now stamps `#e` only where
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
///    (adjudicated in `the_tie_at_a_cleanup_consumer_is_sound_and_the_stale_sibling_degrades`).
///    The clause is KEPT as the fail-closed refusal for the corners where a
///    base can still render bare with `#e` in scope: a step-cap partial map
///    and a block the fixpoint never reached.
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
    if sv.version_token_at(func, block, terminal, base).is_none() {
        return false;
    }
    let base_local = (0..func.body.locals.len()).find(|&l| {
        crate::place_to_var_name(func, &Place { local: l, projections: Vec::new() }) == base
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
fn pin_in_place_update_reads(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
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
    if formula_def_name(&def) != Some(subj.as_str()) {
        return def;
    }
    // The `#e` symbol must be FRESH. `validate_function` does not reserve `#` in
    // local names (lib.rs:492) and `place_to_var_name` permits it (lib.rs:5310),
    // so a caller-constructed `VerifiableFunction` may already hold a local
    // literally named `n#e`. Minting it would then ALIAS a real local and assert
    // a relationship the program does not have — a false proof, not merely a
    // weakening, because `version_rename_at` treats any `#` name as already
    // versioned (:1102) and the collision survives. Fail closed: no repair.
    let entry_symbol = format!("{subj}#{ENTRY_VERSION_SENTINEL}");
    if func.body.locals.iter().any(|l| l.name.as_deref() == Some(entry_symbol.as_str())) {
        return def;
    }
    let Formula::Eq(_, rhs) = &def else { return def };
    // Only an in-place update needs this: the rhs must READ the subject.
    if !rhs.free_variables().iter().any(|v| v.split('#').next().unwrap_or(v) == subj) {
        return def;
    }
    // A deref subject `x*` is established by the borrow `x = &..` of its base.
    let base = subj.strip_suffix('*').unwrap_or(&subj);
    let Some(k) = block_def_establish_stmt(func, block, base, block.stmts.len()) else {
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
    let token = if sv.full_graph_union_is_entry_only(block.id, &subj) {
        ENTRY_VERSION_SENTINEL.to_string()
    } else {
        format!("{PRE_WRITE_SENTINEL_PREFIX}_s{}_{k}", block.id.0)
    };
    // The chosen spelling must be FRESH — the `#e` collision refusal above,
    // repeated verbatim for the fallback spelling. Fail closed: no repair (the
    // bare recurrence then collapses at the consumer and the scanners DEGRADE
    // the obligation — never a false proof).
    let minted_symbol = format!("{subj}#{token}");
    if func.body.locals.iter().any(|l| l.name.as_deref() == Some(minted_symbol.as_str())) {
        return def;
    }
    let read_versioned = version_rename_at(&def, sv, func, block.id, k);
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
    let stamp = |f: &Formula| {
        f.clone().map(&mut |node| match node {
            Formula::Var(name, sort) if name == subj => {
                Formula::Var(format!("{name}#{token}"), sort)
            }
            other => other,
        })
    };
    // Read side only: the subject is rebound to BARE immediately after this, and it
    // is the consumer's rename of that bare subject that connects the def to the body.
    match def {
        Formula::Eq(l, r) => Formula::Eq(l, Box::new(stamp(&r))),
        other => other,
    }
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
    let mut result: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let mut queue: VecDeque<(BlockId, Vec<Formula>)> = VecDeque::from([(BlockId(0), Vec::new())]);

    // The fixpoint terminates on its own — a block's fact set only ever shrinks
    // (intersection) and is re-propagated only when it does — but cap total steps
    // as defence against an unforeseen CFG shape. On overflow fall back to the
    // sound, less precise empty map (VCs then rely on guards/preconditions alone).
    let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(8).saturating_add(4096);
    let mut steps = 0usize;

    while let Some((block_id, incoming)) = queue.pop_front() {
        steps += 1;
        if steps > cap {
            return FxHashMap::default();
        }
        if block_id.0 >= n {
            continue;
        }

        let new_defs = match result.get(&block_id) {
            None => incoming,
            Some(existing) => {
                // Keep only facts also present on this newly-arriving path.
                let merged: Vec<Formula> =
                    existing.iter().filter(|f| incoming.contains(f)).cloned().collect();
                if merged.len() == existing.len() {
                    // No shrink ⇒ no new information ⇒ this block has converged.
                    continue;
                }
                merged
            }
        };
        // `result[b]` stores only the pure incoming intersection (never the seed), so
        // the convergence test above remains a clean monotone shrink and terminates.
        result.insert(block_id, new_defs.clone());

        let block = &func.body.blocks[block_id.0];
        let mut next_defs = new_defs;
        // seed this block's branch-merge Ite as an ENTRY fact — injected
        // before the block's own defs so that a same-block redefinition of one of its
        // free variables kills it. The Ite then flows to successors and is killed /
        // intersected exactly like any other entry fact.
        if let Some(seeded) = seed.get(&block_id) {
            extend_killing_redefs(&mut next_defs, seeded.clone());
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
        let store_havoc = deref_store_havoc_names(func, block);
        if !store_havoc.is_empty() {
            let store_set: FxHashSet<String> = store_havoc.iter().cloned().collect();
            next_defs.retain(|f| formula_survives_redefs(f, &store_set));
        }
        // Extraction-declined destinations kill incoming/seeded facts too. The
        // facts in this channel are conjoined PRE-rename (renamed WITH the
        // body), so the use-point rename UNIFIES a stale survivor with the live
        // read — for this channel the KILL, not the rename, is load-bearing
        // (the same reason the deref-store havoc above must kill here). Applied
        // BEFORE the block's own extracted defs are re-added, so a fact this
        // block itself establishes still flows out. Drop-only, hence monotone.
        {
            let mut assigned: FxHashSet<String> = FxHashSet::default();
            extend_with_assigned_place_dests(func, &block.stmts, &mut assigned);
            extend_with_derived_slice_len(&mut assigned);
            if !assigned.is_empty() {
                next_defs.retain(|f| formula_survives_redefs(f, &assigned));
            }
        }
        // Reads of an in-place update are pinned to their pre-write values BEFORE the
        // defs cross a block boundary; the subject stays bare, so the kill computed
        // inside `extend_killing_redefs` is byte-identical to the unversioned form.
        // Orthogonal to the deref-store havoc kill above: that DROPS incoming facts a
        // `*p = v` invalidates, this NARROWS the block's own defs. Both are monotone.
        extend_killing_redefs(
            &mut next_defs,
            guards::extract_block_definitions(func, block)
                .into_iter()
                .map(|d| pin_in_place_update_reads(&sv, func, block, d))
                .collect(),
        );
        extend_killing_redefs(&mut next_defs, extract_set_discriminant_definitions(func, block));
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
        let term_defs = terminator_def_names(func, block);
        if !term_defs.is_empty() {
            let term_set: FxHashSet<String> = term_defs.into_iter().collect();
            next_defs.retain(|f| formula_survives_redefs(f, &term_set));
        }

        // `next_defs` is the BASE outflow: facts true after the block and
        // terminator write-kill, regardless of whether a panicking terminator
        // returns normally or transfers to cleanup. Success-only facts must
        // never enter this set.
        let base_outflow = next_defs;
        let mut normal_outflow = base_outflow.clone();
        match &block.terminator {
            Terminator::Assert { .. } => {
                // A checked operation's result equation and no-overflow range
                // hold only after its Assert succeeds. This is what connects a
                // chained `x + y + z` across rustc's checked-op blocks, but it
                // is false on the panic/unwind edge.
                extend_killing_redefs(
                    &mut normal_outflow,
                    guards::extract_assert_passed_semantics(func, block),
                );
            }
            Terminator::Call { .. } => {
                // These are post-RETURN definitions of the call destination.
                // Add them after the terminator kill, and only to the normal
                // return edge. A cleanup edge observes no returned value.
                extend_killing_redefs(&mut normal_outflow, probe_call_definitions(func, block));
                extend_killing_redefs(&mut normal_outflow, eq_unit_call_definitions(func, block));
                extend_killing_redefs(
                    &mut normal_outflow,
                    inferred_pred_call_definitions(func, block),
                );
            }
            _ => {}
        }

        for guarded in block.terminator.discovered_clauses(block_id) {
            if let trust_types::ClauseTarget::Block(target) = guarded.target {
                // Assert's sole in-CFG discovered clause is its normal-success
                // edge. Switch clauses are ordinary base outflow. A future
                // conditional terminator fails closed to base facts.
                let outflow = match &block.terminator {
                    Terminator::Assert { target: success, .. } if target == *success => {
                        &normal_outflow
                    }
                    _ => &base_outflow,
                };
                queue.push_back((target, outflow.clone()));
            }
        }

        // Faithful unwind transport. Normal Call return receives post-return
        // facts; every cleanup edge receives BASE facts only. Enqueue both when
        // normal and cleanup target the same block: the incoming intersection
        // then deliberately removes success-only facts from that join.
        match &block.terminator {
            Terminator::Call { target, unwind, .. } => {
                if let Some(target) = target {
                    queue.push_back((*target, normal_outflow.clone()));
                }
                if let Some(cleanup) = unwind.cleanup_target() {
                    queue.push_back((cleanup, base_outflow.clone()));
                }
            }
            Terminator::Assert { unwind, .. } => {
                // The normal target was enqueued through discovered_clauses.
                if let Some(cleanup) = unwind.cleanup_target() {
                    queue.push_back((cleanup, base_outflow.clone()));
                }
            }
            Terminator::Goto(target) => {
                queue.push_back((*target, base_outflow.clone()));
            }
            Terminator::Drop { target, unwind, .. } => {
                queue.push_back((*target, base_outflow.clone()));
                if let Some(cleanup) = unwind.cleanup_target() {
                    queue.push_back((cleanup, base_outflow.clone()));
                }
            }
            Terminator::Opaque { targets, .. } => {
                for target in targets {
                    queue.push_back((*target, base_outflow.clone()));
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

/// Public accessor for the hardened panic-boundary path (`hardened.rs`), which
/// threads cross-block assert-passed result defs (`_N.0 == lhs OP rhs` on the
/// no-overflow success edge) into MIR-assert boundary VCs. Gated under
/// the canonical pipeline like the underlying fixpoint.
pub(crate) fn v2_build_path_definition_map_for_hardened(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    v2_build_path_definition_map(func)
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
        Some(block_guard_paths) => {
            v2_formula_with_path_guards(func, &super::stmt_versions_for(func), block_guard_paths, formula)
        }
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
    for block_id in (0..n).map(BlockId) {
        let merge = guards::branch_merge_definitions(func, block_id, &base);
        if !merge.is_empty() {
            merge_facts.insert(block_id, merge);
        }
    }

    // route enum-payload facts across a construction join into the
    // matching discriminant-switch arm (the join intersection drops a fact present
    // on only one arm). Keyed by ARM block, so it composes with the join-keyed
    // branch-merge facts above under the same seed+re-attach machinery below.
    for (arm, facts) in guards::enum_construction_demux_definitions(func) {
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
    for (block_id, merge) in &merge_facts {
        result.entry(*block_id).or_default().extend(merge.iter().cloned());
    }

    result
}
