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
pub(super) fn formula_mentions_redef(f: &Formula, redefined: &FxHashSet<String>, bound: &[&str]) -> bool {
    match f {
        Formula::Var(name, _) => {
            !bound.contains(&name.as_str())
                && redefined.iter().any(|n| place_names_overlap(name, n))
        }
        // SymVar carries a `Symbol`; resolve to its `&str` for the same name check.
        Formula::SymVar(sym, _) => {
            let name = sym.as_str();
            !bound.contains(&name) && redefined.iter().any(|n| place_names_overlap(name, n))
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
        Terminator::Call { args, dest, .. } => {
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
                return vec![place_to_var_name(func, dest)];
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
            let mut names = mutably_borrowed_local_names(func);
            // Trust #soundness (round-12/13): also havoc every local whose type
            // TRANSITIVELY contains a mutable reference / raw pointer — a `&mut`/
            // `*mut` PARAMETER, a pointer RETURNED from a call, or one NESTED in an
            // aggregate (`struct Wrapper { p: &mut u32 }`, a tuple/array/closure
            // capture, …). None have a syntactic `&mut x` statement, and the nested
            // case is not even a pointer at the local's top level, so
            // mutably_borrowed_local_names misses them. The callee can mutate the
            // pointee, so we havoc the local's BASE name — its prefix-overlap kills
            // the pointer, its pointee `s*`, and any nested pointee `s.f*`.
            names.extend(mutable_pointer_local_names(func));
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
            names.push(place_to_var_name(func, dest));
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
            let mut names = mutably_borrowed_local_names(func);
            names.extend(mutable_pointer_local_names(func));
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
        Terminator::Opaque { .. } => {
            let mut names = mutably_borrowed_local_names(func);
            names.extend(mutable_pointer_local_names(func));
            names
        }
        _ => Vec::new(),
    }
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
/// folded (round-12, `unique_whole_local_def` skips deref-stores), so this fires
/// ONLY for the genuinely-opaque case and keeps full precision otherwise.
///
/// Conservatively havoc every mutably-borrowed / mutable-pointer local — the exact
/// over-approximation `terminator_def_names` already applies at a `Call` (a callee
/// can mutate any `&mut` pointee) — so any fact about a possible referent is
/// dropped. Monotone-sound: dropping a hypothesis can only turn a PROVE into a
/// FAIL, never the reverse. Empty unless such a store exists.
pub(super) fn deref_store_havoc_names(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<String> {
    let has_opaque_deref_store = block.stmts.iter().any(|stmt| {
        let Statement::Assign { place, .. } = stmt else { return false };
        // Opaque ⟺ the pointer does not fold to a concrete referent — covers the
        // reseated/multi-borrow/param case AND a cast-laundered pointer
        // (`&mut x as *mut`, IntToPtr) whose def `resolve_referent` cannot fold.
        // `deref_pointer_is_opaque` is the strict, name-mint-consistent superset of
        // the old `unique_whole_local_def(..).is_none()` check.
        matches!(place.projections.first(), Some(trust_types::Projection::Deref))
            && crate::deref_pointer_is_opaque(func, place.local)
    });
    if !has_opaque_deref_store {
        return Vec::new();
    }
    let mut names = mutably_borrowed_local_names(func);
    names.extend(mutable_pointer_local_names(func));
    names
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
    let redefined: FxHashSet<String> =
        new_defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
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
    redefined.extend(deref_store_havoc_names(func, block));
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
    names.extend(deref_store_havoc_names(func, block));
    names.extend(terminator_def_names(func, block));
    names
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
pub(crate) fn writes_until(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_idx: usize,
) -> FxHashSet<String> {
    let mut defs = guards::extract_block_definitions_until(func, block, stmt_idx);
    defs.extend(extract_set_discriminant_definitions_until(func, block, stmt_idx));
    let mut names: FxHashSet<String> =
        defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
    // Opaque deref-store havoc: if any opaque `*p = v` appears in stmts[..stmt_idx],
    // its referent-havoc is in effect from that point. `deref_store_havoc_names` is
    // block-level; gate it on a prefix occurrence so it does not leak BACKWARD to
    // reads before the store.
    let has_opaque_prefix = block.stmts[..stmt_idx.min(block.stmts.len())].iter().any(|stmt| {
        let trust_types::Statement::Assign { place, .. } = stmt else { return false };
        matches!(place.projections.first(), Some(trust_types::Projection::Deref))
            && crate::deref_pointer_is_opaque(func, place.local)
    });
    if has_opaque_prefix {
        names.extend(deref_store_havoc_names(func, block));
    }
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
    use std::collections::BTreeSet;
    let n = func.body.blocks.len();
    let gen_sets: Vec<FxHashSet<String>> =
        func.body.blocks.iter().map(|b| block_written_names(func, b)).collect();
    let all_names: FxHashSet<String> = gen_sets.iter().flatten().cloned().collect();
    // Precompute each block's OUT token per gen'd name (constant across the
    // fixpoint): the last statement writing/havocing the name, else a terminator
    // marker `s{b}_t` for a name the block's TERMINATOR defines (Call dest).
    let gen_out: Vec<FxHashMap<String, String>> = func
        .body
        .blocks
        .iter()
        .enumerate()
        .map(|(bi, b)| {
            // The block's TERMINATOR writes (a `Call` dest + escaping `&mut`s) run
            // AFTER every statement, so a name it reassigns has its OUT token pinned
            // to the terminator marker `s{b}_t` — DISTINCT from any statement
            // establish token, so a fact established at a statement and threaded to a
            // successor is name-disjoint from the post-terminator value. Without this
            // the OUT token would be the last STATEMENT write (`stmt_writes_name`
            // cannot see the terminator), and a stale pre-call fact would re-unify
            // with the post-call read (the case `terminator_def_names` defends).
            let term_defs = terminator_def_names(func, b);
            gen_sets[bi]
                .iter()
                .map(|nm| {
                    let tok = if term_defs.iter().any(|t| place_names_overlap(t, nm)) {
                        format!("s{}_t", b.id.0)
                    } else {
                        match (0..b.stmts.len()).rev().find(|&k| stmt_writes_name(func, b, k, nm)) {
                            Some(k) => format!("s{}_{k}", b.id.0),
                            None => format!("s{}_t", b.id.0),
                        }
                    };
                    (nm.clone(), tok)
                })
                .collect()
        })
        .collect();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, b) in func.body.blocks.iter().enumerate() {
        for t in v2_terminator_targets(&b.terminator) {
            if t.0 < n {
                preds[t.0].push(i);
            }
        }
    }
    let sentinel = || BTreeSet::from([ENTRY_VERSION_SENTINEL.to_string()]);
    let entry_in: FxHashMap<String, BTreeSet<String>> =
        all_names.iter().map(|nm| (nm.clone(), sentinel())).collect();
    let mut in_sets: Vec<FxHashMap<String, BTreeSet<String>>> = vec![FxHashMap::default(); n];
    if n > 0 {
        in_sets[0] = entry_in.clone();
    }
    let out_of = |b: usize, in_b: &FxHashMap<String, BTreeSet<String>>| {
        let mut out: FxHashMap<String, BTreeSet<String>> = FxHashMap::default();
        for nm in &all_names {
            if gen_sets[b].contains(nm) {
                out.insert(nm.clone(), BTreeSet::from([gen_out[b][nm].clone()]));
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
            let mut new_in: FxHashMap<String, BTreeSet<String>> =
                if b == 0 { entry_in.clone() } else { FxHashMap::default() };
            for &p in &preds[b] {
                for (nm, s) in out_of(p, &in_sets[p]) {
                    new_in.entry(nm).or_default().extend(s);
                }
            }
            if new_in != in_sets[b] {
                in_sets[b] = new_in;
                changed = true;
            }
        }
    }
    func.body.blocks.iter().enumerate().map(|(i, b)| (b.id, in_sets[i].clone())).collect()
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
    name.strip_suffix("__slice_len").is_some_and(|base| {
        base == dest
            || (base.len() > dest.len()
                && base.starts_with(dest)
                && matches!(base.as_bytes()[dest.len()], b'.' | b'[' | b'*'))
    })
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
    let sv = StmtVersionCtx::build(func);
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
    let sv = StmtVersionCtx::build(func);
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
pub(super) fn block_entry_may_reassigned(func: &VerifiableFunction, block: BlockId) -> FxHashSet<String> {
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
        let mut block_defs = guards::extract_block_definitions(func, block);
        block_defs.extend(extract_set_discriminant_definitions(func, block));
        let mut stmt: FxHashSet<String> =
            block_defs.iter().filter_map(formula_def_name).map(str::to_string).collect();
        stmt.extend(deref_store_havoc_names(func, block));
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

        for succ in v2_terminator_targets(&func.body.blocks[i].terminator) {
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
    let sv = StmtVersionCtx::build(func);
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
    let vc = Vc::versioned(version_rename_at(&formula, &sv, func, block, terminal), block);
    // Defense in depth for callers that invoke a lower-level generator without
    // passing through `generate_vcs_impl`'s sanitized function view.
    let kept: Vec<Formula> = preconditions
        .iter()
        .filter(|pre| !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre))
        .cloned()
        .collect();
    let facts: Vec<Fact> = kept.iter().cloned().map(Fact::entry).collect();
    (conjoin(&facts, vc), kept)
}

// DELETED (S2c item 3): `conjoin_live_preconditions` — the precondition KILL
// (`preconditions.filter(formula_survives_redefs)`). Replaced everywhere
// (the v2 VC sites AND the hardened lane) by `conjoin_preconditions_versioned`,
// which renames the VC body to its versioned form so a precondition about a
// reassigned place names a different SMT variable and cannot constrain it — the
// kill's drop, by name-disjointness. Verdict-equivalence proven by
// `flip_matches_kill_stmt` (statement-granular, 125 functions, 0 disagreements)
// and validated by the full trust-vcgen suite passing with the flip live.
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
        extend_killing_redefs(&mut next_defs, guards::extract_block_definitions(func, block));
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
    let guard_paths_map = v2_build_path_guard_map(func);
    match guard_paths_map.get(&block) {
        Some(block_guard_paths) => {
            // Trust (lane-A CSE): `v2_formula_with_path_guards` now takes the
            // statement-version oracle by reference; build it here for this one call.
            let sv = StmtVersionCtx::build(func);
            v2_formula_with_path_guards(func, &sv, block_guard_paths, formula)
        }
        None => formula,
    }
}

pub(super) fn v2_build_path_definition_map(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
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
