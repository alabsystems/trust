// Recognizers for std calls that can panic on their own arguments -- checked
// arithmetic, division and remainder, and the slice/collection methods whose
// index or range argument is unchecked -- together with the abstract-length
// reasoning used to decide whether the argument is provably in range.

use super::*;

/// Division/remainder-by-zero hidden inside a library `Terminator::Call`. The
/// `Rvalue::BinaryOp(Div|Rem)` arms of `generate_v2_safety_vcs` only see a
/// caller-visible `/`/`%`; a dynamic divisor passed to a method that panics (or
/// is UB) on a zero divisor lowers to a `Terminator::Call` with no BinaryOp, so
/// the op was reported vacuously safe — a false PROVE for `a.div_euclid(b)` /
/// `Iterator::step_by(0)` with a runtime-zero argument. This recognizer maps
/// such a call to the SAME `DivisionByZero` / `RemainderByZero` obligation the
/// BinaryOp path builds (`divisor != 0`), so a dominating `if b != 0 { … }`
/// guard or `#[requires(b != 0)]` precondition DISCHARGES it while an unguarded
/// one FAILS with a counterexample.
///
///   * `a.checked_div(b)` / `a.checked_rem(b)`: TOTAL — they RETURN `None` on a
///     zero divisor (or the `MIN / -1` overflow) instead of panicking, so they have
///     NO panic condition AT ALL and emit NO obligation (returning `None` here).
///     This is the WHOLE point of the `checked_*` family vs `a / b`: modeling a
///     `divisor != 0` obligation for them is a FALSE REFUTATION — an unguarded
///     `n.checked_div(&x).unwrap_or_else(BigUint::zero)` handles the `None` and
///     never panics. (The `<T as num_traits::CheckedDiv>::checked_div` trait form
///     shares the `checked_div` tail and is likewise total. The Some/None RESULT
///     modeling is a SEPARATE concern: a caller `.unwrap()` on the result emits its
///     OWN obligation — so suppressing the divzero VC opens no hole.)
///   * `a.div_euclid(b)` / `a.rem_euclid(b)`: PANIC on a zero divisor, exactly
///     like `a / b` / `a % b`.
///   * `Iterator::step_by(n)`: PANICS when `n == 0` (`assert!(step != 0)` in the
///     stdlib). The step is the divisor-analogue: the obligation is `n != 0`.
///
/// Returns the **0-based index of the divisor argument** in the MIR `args` (the
/// receiver lowers to arg 0, so the divisor is arg 1 for the `a.op(b)` methods;
/// `step_by`'s step is likewise arg 1 after the iterator receiver) and the
/// `VcKind` to tag the obligation with (`Div` family vs `Rem` family). Any
/// unrecognized call returns `None` — the recognizer must NOT broadly fail-close
/// on every Call, which would break drop-in Rust.
pub(super) fn divzero_call(callee: &str) -> Option<(usize, VcKind)> {
    let tail = callee.rsplit("::").next().unwrap_or(callee);
    let tail = tail.split('<').next().unwrap_or(tail).trim();
    match tail {
        // `a.div_euclid(b)`: PANICS on a zero divisor exactly like `a / b`. Divisor
        // is arg 1. (`checked_div` is DELIBERATELY ABSENT: it returns `None` on a
        // zero divisor and NEVER panics — see the doc above; emitting a divzero VC
        // for it was a FALSE REFUTATION.)
        "div_euclid" => Some((1, VcKind::DivisionByZero)),
        // `a.div_ceil(b)`: ceiling division — PANICS on a zero divisor exactly like
        // `a / b`, and (for the common UNSIGNED case) has NO other panic path (the
        // ceiling result is <= self, so it cannot overflow), so `b != 0` FULLY models
        // its panic-freedom. Divisor is arg 1. (Signed `iN::div_ceil` also panics on
        // the `MIN.div_ceil(-1)` overflow — the same residual as `div_euclid` above,
        // handled identically; NOT a regression.) Closes the `x.div_ceil(0)`
        // false-accept: it was reported vacuously proved despite the div-by-zero panic.
        "div_ceil" => Some((1, VcKind::DivisionByZero)),
        // `a.rem_euclid(b)`: PANICS on a zero divisor exactly like `a % b`. Divisor
        // is arg 1. (`checked_rem` is DELIBERATELY ABSENT — total, returns `None`.)
        "rem_euclid" => Some((1, VcKind::RemainderByZero)),
        // `iter.step_by(n)`: the step `n` is arg 1; `n == 0` panics. The "divisor"
        // is `n`; tag it `DivisionByZero` (the `!= 0` obligation is identical).
        "step_by" => Some((1, VcKind::DivisionByZero)),
        _ => None,
    }
}

/// Recognize a slice method whose runtime panic is an out-of-bounds / zero-size
/// argument with no caller-visible `Projection::Index`. Mirrors [`divzero_call`]:
/// returns `None` for any unrecognized call so the recognizer NEVER broadly
/// fail-closes on every `Call` (that would break drop-in Rust). The callee path
/// is matched on its final segment so it works regardless of the `<impl [T]>` /
/// `core::slice::<impl [T]>::` qualification the MIR carries.
pub(super) fn slice_method_panic(callee: &str) -> Option<SliceMethodPanic> {
    // Route through `method_tail` (not an inline `rsplit`) so a TRAILING turbofish
    // token — e.g. the `::<__trust_str_index>` str-index marker `func_operand_name`
    // appends — is stripped and the `index`/`split_at`/… tail still recognizes. An
    // inline `rsplit("::")` would read the token itself as the tail and MISS the
    // method (a silent skip => a str range-index emits no obligation at all).
    let tail = method_tail(callee);
    match tail {
        // `s.split_at(mid)` / `split_at_mut(mid)`: `mid` is arg 1, panic `mid > len`.
        "split_at" | "split_at_mut" => Some(SliceMethodPanic::SplitAt { mid_idx: 1 }),
        // Zero-size-argument panics: the size/window `n` is arg 1, panic `n == 0`.
        "chunks" | "chunks_mut" | "chunks_exact" | "chunks_exact_mut" | "rchunks"
        | "rchunks_mut" | "rchunks_exact" | "rchunks_exact_mut" | "windows" => {
            Some(SliceMethodPanic::NonZeroArg { n_idx: 1 })
        }
        // `s.swap(i, j)`: indices are args 1 and 2, panic `i >= len || j >= len`.
        "swap" => Some(SliceMethodPanic::SwapIndices { i_idx: 1, j_idx: 2 }),
        // `v.remove(i)`/`v.swap_remove(i)` (panic `i >= len`) and `v.insert(i, x)`
        // (panic `i > len`) on an owned `Vec`. The index is arg 1. Vec-vs-non-Vec
        // (HashMap/BTreeMap/VecDeque/HashSet/String never-panic or unmodeled) is
        // discriminated in the body via `operand_is_owned_container_receiver`.
        "remove" | "swap_remove" => {
            Some(SliceMethodPanic::VecPanicMethod { index_idx: 1, insert: false })
        }
        "insert" => Some(SliceMethodPanic::VecPanicMethod { index_idx: 1, insert: true }),
        // `s[range]`: the `Index`/`IndexMut` trait method, lowered to
        // `Index::index(slice, range)`. The callee is rendered as the GENERIC trait
        // method path (`core::ops::index::Index::index`), so the concrete range type
        // is NOT visible here — `slice_method_panic_body` discriminates by scanning
        // the call operands for a slice receiver (modeled len) and a panicking-range
        // argument (`operand_ty` is `Range`/`RangeTo`/`RangeFrom`/`RangeInclusive`).
        // A non-range `index` (scalar `Vec`/`HashMap` indexing) or a non-slice
        // receiver yields `None` from the body — sound, non-breaking.
        "index" | "index_mut" => Some(SliceMethodPanic::RangeIndex),
        _ => None,
    }
}

/// True iff `op`'s type is a PANICKING slice-index range — exclusive `Range`,
/// `RangeTo`, `RangeFrom`, or `RangeInclusive`. `RangeFull` (`s[..]`, never panics)
/// and scalar `usize` (`Vec`/`HashMap` index) are excluded. Authoritative
/// discrimination for `RangeIndex`, robust to the erased generic callee path.
pub(super) fn operand_is_panicking_range(func: &VerifiableFunction, op: &Operand) -> bool {
    matches!(
        crate::operand_ty_cow(func, op).as_deref(),
        Some(Ty::Adt { name, .. }) if matches!(
            range_family_adt_name(name),
            Some("Range" | "RangeTo" | "RangeFrom" | "RangeInclusive")
        )
    )
}

/// Trust (#7c owned-Vec scalar index): true iff `op` is a SCALAR unsigned-integer
/// index — the `usize` argument of `v[i]` (`<Vec<T> as Index<usize>>::index(&v, i)`).
/// A range argument (an ADT) and a signed integer are excluded. This is the SCALAR
/// sibling of `operand_is_panicking_range`: for `Vec::index`, the callee renders as
/// the GENERIC `Index::index` path, so the SCALAR-vs-range discrimination is by the
/// index arg's `operand_ty` here (a `usize` is `Ty::Int { signed: false }`).
pub(super) fn operand_is_scalar_usize_index(func: &VerifiableFunction, op: &Operand) -> bool {
    matches!(crate::operand_ty_cow(func, op).as_deref(), Some(Ty::Int { signed: false, .. }))
}

/// Build the *failure* body for a recognized [`SliceMethodPanic`] over the call's
/// `args`, or `None` when the receiver carries no modeled length (a non-slice
/// `swap`, e.g. `(a, b).swap()` on a tuple struct, or an argument that is not a
/// modeled integer) — in which case no obligation is emitted, mirroring how the
/// bounds path skips a collection whose `len` it cannot model. The returned
/// formula is the *unguarded* failure (`mid > len`, `n == 0`, `i >= len OR
/// j >= len`); the caller conjoins block-defs / path-guards / preconditions so a
/// dominating `if mid <= s.len()` / `if n != 0` DISCHARGES it.
/// True iff `name` is `Vec` — the only owned deref-to-slice container for which range
/// length-recovery is SOUND. The call-site receiver is `&Vec` and `slice_len_formula`
/// returns `None` (the deref happens inside the `Index` impl), so the length must come
/// from the container's own abstract var. `String` is DELIBERATELY EXCLUDED: a
/// `String` range index `&s[..k]` carries an unmodeled `byte_index_not_char_boundary`
/// panic (e.g. `s="é"` is 2 bytes, so a `k <= s.len()` guard with `k==1` proves the
/// byte bound yet `&s[..1]` still panics) — recovering its byte length would
/// false-PROVE that panic. `VecDeque` is non-contiguous and has no range-`Index` impl,
/// so it never reaches this path. `Vec<T>` range index panics only on OOB / start>end,
/// both modeled — so its length recovery is sound.
pub(crate) fn is_owned_slice_container_name(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name);
    let tail = base.rsplit("::").next().unwrap_or(base).trim();
    tail == "Vec"
}

/// The abstract length of an OWNED deref-to-slice container receiver (`&Vec`/`&String`),
/// or `None` when the operand does not trace to such a container. Reuses the same
/// `coll_len_var` (the container's own abstract var) the non-emptiness recognizer ties
/// `Vec::len`/`last()` to, so the bound `end <= len` connects to those facts.
///
/// SOUNDNESS: the returned var is UNCONSTRAINED unless the code establishes a length
/// relationship, so substituting it for an unmodeled `len` keeps `end > len`
/// satisfiable (the obligation still FAILS — no false PROVE) and only discharges when a
/// real guard / `last()==Some => len>=1` fact constrains it. Strictly more precise than
/// the always-violated fail-close, never less sound. Gated to genuine containers so a
/// scalar's value is never misread as a length.
/// Return an owned container's abstract length together with the BASE collection
/// local it is minted under. The base is needed to decide, STRUCTURALLY, whether a
/// slice range bound reduces to that same length (see
/// `range_bounds_within_abstract_len`).
pub(super) fn collection_abstract_len_with_base(
    func: &VerifiableFunction,
    operand: &Operand,
) -> Option<(usize, Formula)> {
    collection_abstract_len_with_base_opts(func, operand, false)
}

/// TYPE-level half of the #7c owned-container recognition, with NONE of the
/// recovery gates (base uniqueness, borrow/length stability): true iff `operand`
/// is — after peeling at most one `&`/`&mut` — an ADT whose NAME is a recognized
/// owned slice container (`Vec`, `String`, …). Used to decide fail-honest
/// VISIBILITY at the scalar-index site: when this is true but the length recovery
/// declined, the access must surface as `UnsupportedMir` (Unknown), never vanish.
/// Deliberately trace-free: the call receiver is the (re)borrow temp itself, whose
/// declared type already names the container.
pub(super) fn operand_is_owned_container_receiver(func: &VerifiableFunction, operand: &Operand) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    let ty = crate::place_ty_cow(func, &Place::local(p.local));
    let adt_ty = match ty.as_deref() {
        Some(Ty::Ref { inner, .. }) => Some(inner.as_ref()),
        other => other,
    };
    matches!(adt_ty, Some(Ty::Adt { name, .. }) if is_owned_slice_container_name(name))
}

/// True iff the ADT NAME is a std map/associative container whose `Index` impl
/// PANICS on an absent key: `HashMap`, `BTreeMap` (`self.get(key).expect("no
/// entry found for key")`). Unlike a `Vec`/slice scalar index — whose panic is a
/// length OOB with a modelable `i < len` obligation — a map index's panic is
/// key-PRESENCE, which needs a map theory to model. So a map index is surfaced as
/// a visible `UnsupportedMir` (Unknown → fail-closed under `-full`), never a
/// length obligation and never a silent skip. (`HashSet`/`BTreeSet` are not
/// `Index`-indexable; `VecDeque` indexes by `usize` like a slice.)
pub(super) fn is_panicking_map_container_name(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name);
    let tail = base.rsplit("::").next().unwrap_or(base).trim();
    matches!(tail, "HashMap" | "BTreeMap")
}

/// True iff `operand` (after peeling one `&`/`&mut`) is a receiver whose type is a
/// panicking std map container — see [`is_panicking_map_container_name`]. Used at
/// the index site to surface `m[&k]` as a visible key-presence obligation rather
/// than the former silent None-skip (a panic-freedom false-accept).
pub(super) fn operand_is_map_container_receiver(func: &VerifiableFunction, operand: &Operand) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    let ty = crate::place_ty_cow(func, &Place::local(p.local));
    let adt_ty = match ty.as_deref() {
        Some(Ty::Ref { inner, .. }) => Some(inner.as_ref()),
        other => other,
    };
    matches!(adt_ty, Some(Ty::Adt { name, .. }) if is_panicking_map_container_name(name))
}

/// Like [`collection_abstract_len_with_base`], but `peel_shared_ref` optionally accepts a
/// borrowed `&Vec` receiver (peeling one SHARED, immutable ref to the `Vec` ADT).
///
/// The RANGE-index path calls with `peel_shared_ref = false` (its behavior is UNCHANGED — a
/// `&Vec` param range slice keeps failing closed / refuting, never regressed). The #7c
/// SCALAR-index path calls with `true`: the dominant scalar shape `fn f(v: &Vec<T>, i) {
/// v[i] }` needs the borrowed receiver's length. SOUNDNESS of the peel: a SHARED `&Vec`
/// cannot be resized (no `&mut` access), so its abstract length is a STABLE bound; a `&mut
/// Vec` is NEVER peeled (the `Ty::Ref { mutable: false }` match excludes it), so a resizable
/// receiver stays declining/fail-closed. The base LOCAL is unchanged by the peel, so the
/// `.len()`/`last()` ties (keyed on the same base local) still connect to the SAME
/// `coll_len_var(base)`.
pub(super) fn collection_abstract_len_with_base_opts(
    func: &VerifiableFunction,
    operand: &Operand,
    peel_shared_ref: bool,
) -> Option<(usize, Formula)> {
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    // Unique-definition trace (must match the len-tie mint site in guards.rs): a
    // conditionally-merged receiver (`v = if c {a} else {b}`) has an ambiguous base, so
    // recovering one branch's length would let a `k <= a.len()` guard discharge an index
    // on the shorter `b` — a false-PROVE. Fail closed on an ambiguous trace.
    let Some(base) = guards::base_collection_local_unique(func, p.local) else {
        return None;
    };
    // Trust (struct-field Vec length identity, 2026-07-08): PLACE-keyed extension of
    // the recovery. The reborrow-temp receiver of a struct-field Vec
    // (`_recv = &((*self).history)`) resolves its abstract length to the canonical
    // FIELD place's var (`coll_len(self*.0)`) — the SAME var the guard side
    // (`guards::owned_container_len_var`) and the `.len()` tie
    // (`guards::slice_last_some_nonempty_definitions`) mint — so a length guard on
    // the field discharges the index bound across DISTINCT reborrow temps (each
    // access reborrows afresh, so the per-temp vars below can never unify).
    // SOUNDNESS: every gate (shared `&self` root — a `&mut self` root FAILS CLOSED
    // to the per-temp var; stable root storage; per-hop uniqueness + reseat
    // exclusion; fields kept distinct by the full-place key) lives in
    // `base_collection_place_unique`, the ONE function both sides call — which is
    // what keeps guard and bound symmetric. The root's shared-ref immutability
    // subsumes the `local_mut_borrows_may_resize` gate below (no `&mut` to the
    // field can coexist with the live `&self`, so no resize channel exists).
    // Gated to `peel_shared_ref` (the SCALAR-index side) so the RANGE path
    // (`peel_shared_ref = false`) keeps its exact fail-closed behavior. The
    // returned BASE stays the traced leaf LOCAL, so base-keyed structural checks
    // (`range_bounds_within_abstract_len`, `operand_is_len_of_base`) are unchanged
    // and can only DECLINE for a field receiver (fail closed), never mis-tie.
    if peel_shared_ref
        && let Some(base_place) = guards::base_collection_place_unique(func, p.local)
        && !base_place.projections.is_empty()
        && matches!(
            crate::place_ty_cow(func, &base_place).as_deref(),
            Some(Ty::Adt { name, .. }) if is_owned_slice_container_name(name)
        )
    {
        return Some((base, guards::coll_len_var_place(func, &base_place)));
    }
    let base_ty = crate::place_ty_cow(func, &Place::local(base));
    let adt_ty = match base_ty.as_deref() {
        Some(Ty::Ref { mutable: false, inner }) if peel_shared_ref => Some(inner.as_ref()),
        // Trust (2026-07-06): a `&mut Vec` receiver (the base-tracer now resolves a
        // `&mut Vec` param through its `&(*v)` reborrow temps) is admitted for scalar-
        // index abstract-length recovery too — its length-stability is enforced by the
        // `local_is_mutably_borrowed` gate below (every resize reborrows `&mut *v`, which
        // trips it → declines). So the common read idiom `if i < v.len() { v[i] }` over a
        // `&mut Vec` recovers `coll_len(v)` on BOTH the guard and the index and PROVES,
        // while `let n=v.len(); v.push(x); v[n]` stays REFUTABLE (the push trips the gate).
        Some(Ty::Ref { mutable: true, inner }) if peel_shared_ref => Some(inner.as_ref()),
        other => other,
    };
    let Some(Ty::Adt { name, .. }) = adt_ty else {
        return None;
    };
    if !is_owned_slice_container_name(name) {
        return None;
    }
    // Self-contained soundness (defense-in-depth, matching the non-emptiness/len-tie
    // recognizers): a `&mut`-borrowed base can be RESIZED between the length-defining
    // op and the index, so its abstract len is not a stable bound — decline (fail
    // closed). Refined to the LENGTH-stability gate: a `&mut` reborrow consumed solely
    // as an `index`/`index_mut` receiver is length-benign (Vec/String Index[Mut] never
    // resize), so the dominant WRITE idiom `v[i] = x` — whose `index_mut` call
    // reborrows `&mut (*v)` — recovers the length instead of VANISHING its bounds
    // obligation (the former silent false-accept). A resize (`push`/`extend`/raw ptr/
    // escaping borrow) still trips the gate → declines here.
    if guards::local_mut_borrows_may_resize(func, base) {
        return None;
    }
    Some((base, guards::coll_len_var(func, base)))
}

/// True iff `operand` names the abstract length of `base` — the result of a
/// `base'.len()` call, a `Len(base')`, or a `PtrMetadata(&base')` — where
/// `base_collection_local_unique(base') == Some(base)`. Whole-local `Use` copies are
/// followed (fuel-bounded). Mirrors the `.len()`/`Len` recognition the len-tie mint site
/// (`slice_last_some_nonempty_definitions`) uses, so a bound recognized here is exactly
/// one those seeded `_len == coll_len(base)` facts constrain. (`base` was already proven
/// non-mut-borrowed by `collection_abstract_len_with_base`, matching that site's gate.)
pub(super) fn operand_is_len_of_base(
    func: &VerifiableFunction,
    operand: &Operand,
    base: usize,
    fuel: u32,
) -> bool {
    if fuel == 0 {
        return false;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    // `_len = X.len()` is a Call (not a Statement::Assign), so `unique_whole_local_def`
    // returns None for it — scan the Call terminators directly, reusing the same
    // `method_tail == "len"` + unique-base trace the tie site keys on. CRUCIAL: the len
    // dest itself must be UNIQUELY whole-local defined (`base_collection_local_unique ==
    // itself`), else a REASSIGNED length carrier — the b7 `let mut end = chars.len();`
    // decremented in a loop — would be misread as a stable `chars.len()`, and the seeded
    // `end == coll_len` tie (versioned at the len call) would NOT hold at the later slice
    // use, false-REFUTEing a safe slice.
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == p.local
            && dest.projections.is_empty()
            && method_tail(callee) == "len"
        {
            if guards::base_collection_local_unique(func, p.local) != Some(p.local) {
                return false;
            }
            let Some(Operand::Copy(rp) | Operand::Move(rp)) = args.first() else {
                return false;
            };
            if !rp.projections.is_empty() {
                return false;
            }
            return guards::base_collection_local_unique(func, rp.local) == Some(base);
        }
    }
    // A slice-view length carrier: `Len(place)` / `PtrMetadata(&place)` over the base.
    match crate::unique_whole_local_def(func, p.local) {
        Some(Rvalue::Len(place)) if place.projections.is_empty() => {
            guards::base_collection_local_unique(func, place.local) == Some(base)
        }
        Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => {
            matches!(inner, Operand::Copy(ip) | Operand::Move(ip)
                if ip.projections.is_empty()
                    && guards::base_collection_local_unique(func, ip.local) == Some(base))
        }
        Some(Rvalue::Use(inner)) => operand_is_len_of_base(func, inner, base, fuel - 1),
        _ => false,
    }
}

/// A non-negative integer constant operand (a valid `_len - c` decrement amount).
pub(super) fn operand_is_nonneg_const(op: &Operand) -> bool {
    match op {
        Operand::Constant(trust_types::ConstValue::Uint(_, _)) => true,
        Operand::Constant(trust_types::ConstValue::Int(v)) => *v >= 0,
        _ => false,
    }
}

/// True iff `operand` provably evaluates to `<= coll_len(base)` by STRUCTURE alone: it is
/// the abstract length of `base` (offset 0) or that length minus a non-negative constant
/// (`_len - c`, including the `CheckedSub(_len, c).0` overflow-check lowering — the exact
/// shape `checked_self_decrement_const` recognizes). Fuel-bounded whole-local trace.
///
/// SOUNDNESS: `_len - c <= _len == L` for any `c >= 0`, so a bound recognized here can
/// NEVER exceed `L` at runtime — the `bound > L` obligation is UNSAT under the seeded
/// `_len == coll_len(base)` tie, so backing the VC with `L` only turns a false-Unknown
/// into a PROVE. It cannot mask an OOB: a would-be underflow (`c > _len`) is caught by the
/// subtraction's OWN `[overflow:sub]` obligation, an independent VC. A bound NOT of this
/// shape (a loop variable, a `.len()` over a different/ambiguous base) returns false and
/// stays the honest Unknown — never a refutable VC — so no safe slice is false-REFUTED.
pub(super) fn operand_within_abstract_len(
    func: &VerifiableFunction,
    operand: &Operand,
    base: usize,
    fuel: u32,
) -> bool {
    if fuel == 0 {
        return false;
    }
    // Offset 0: the bound IS the length of `base`.
    if operand_is_len_of_base(func, operand, base, fuel) {
        return true;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return false };
    // `_t.0` where `_t = CheckedSub(lhs, c)` — the overflow-checked `_len - c` lowering
    // (`c` a non-negative constant, `lhs` the length of `base`). Generalizes
    // `checked_self_decrement_const`'s `lhs == l` to any length-of-base operand.
    if p.projections == [trust_types::Projection::Field(0)] {
        if let Some(Rvalue::CheckedBinaryOp(trust_types::BinOp::Sub, lhs, rhs)) =
            crate::unique_whole_local_def(func, p.local)
        {
            return operand_is_nonneg_const(rhs)
                && operand_within_abstract_len(func, lhs, base, fuel - 1);
        }
        return false;
    }
    if !p.projections.is_empty() {
        return false;
    }
    if let Some(Rvalue::Use(inner)) = crate::unique_whole_local_def(func, p.local) {
        return operand_within_abstract_len(func, inner, base, fuel - 1);
    }
    false
}

/// Decide, STRUCTURALLY (never via the solver), whether every panicking upper bound of
/// `range_operand` reduces to `<= coll_len(base)` — so the soft owned-Vec abstract len may
/// safely back the real bounds VC (turning a false-Unknown into a PROVE the seeded
/// `_len == coll_len(base)` facts discharge). Only `RangeTo`/`RangeFrom` qualify: their
/// SOLE obligation is the single `bound > len` comparison. `Range` (`a..b`) additionally
/// carries the `start > end` ORDERING obligation, which is NOT structurally tied to the
/// length, so it stays the honest Unknown rather than risk a false-REFUTE.
pub(super) fn range_bounds_within_abstract_len(
    func: &VerifiableFunction,
    range_operand: &Operand,
    base: usize,
) -> bool {
    let range_local = match range_operand {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
        _ => return false,
    };
    match trace_local_to_range_family(func, range_local, 8) {
        Some(RangeFamilyOperands::To(end)) => operand_within_abstract_len(func, end, base, 8),
        Some(RangeFamilyOperands::From(start)) => operand_within_abstract_len(func, start, base, 8),
        _ => false,
    }
}

pub(super) fn slice_method_panic_body(
    func: &VerifiableFunction,
    panic: &SliceMethodPanic,
    args: &[Operand],
    // Trust (str char-boundary soundness): true iff the receiver is a `str`
    // (the `::<__trust_str_index>` marker from `func_operand_name`). A str
    // range-index carries an UNMODELED UTF-8 char-boundary panic on top of the
    // byte-bounds check, so the RangeIndex arm fails closed unless every endpoint
    // is provably a char boundary. `[u8]`/`[T]` slices pass `false` and are
    // byte-identical to before.
    receiver_is_str: bool,
) -> Option<(Formula, VcKind)> {
    // The receiver slice is arg 0; its modeled `__slice_len` (or a constant array
    // length) is the bound. `slice_len_formula` returns `None` for anything whose
    // length Trust does not model (non-slice receivers), so a `swap` on a tuple or
    // a method on an unmodeled type yields no obligation.
    let receiver = args.first()?;
    match panic {
        SliceMethodPanic::SplitAt { mid_idx } => {
            let len = crate::slice_len_formula(func, receiver)?;
            let mid = args.get(*mid_idx)?;
            // `mid` is a `usize` (>= 0 by type), so the only failure is `mid > len`.
            let mid_f = crate::operand_to_formula(func, mid);
            let violation = Formula::Gt(Box::new(mid_f), Box::new(len));
            Some((violation, VcKind::SliceBoundsCheck))
        }
        SliceMethodPanic::NonZeroArg { n_idx } => {
            // A literal nonzero size is trivially safe — emit nothing, mirroring
            // the `v2_divisor_is_nonzero_constant` skip the divzero path uses.
            let n = args.get(*n_idx)?;
            if v2_divisor_is_nonzero_constant(n) {
                return None;
            }
            // Failure is `n == 0`; reuse the exact divisor-is-zero body so a
            // dominating `if n != 0` guard discharges it identically to `step_by`.
            let violation = v2_divisor_is_zero_formula(func, n);
            Some((violation, VcKind::DivisionByZero))
        }
        SliceMethodPanic::SwapIndices { i_idx, j_idx } => {
            let len = crate::slice_len_formula(func, receiver)?;
            let i = args.get(*i_idx)?;
            let j = args.get(*j_idx)?;
            let i_f = crate::operand_to_formula(func, i);
            let j_f = crate::operand_to_formula(func, j);
            // Indices are `usize` (>= 0 by type); failure is `i >= len OR j >= len`.
            let violation = Formula::Or(vec![
                Formula::Ge(Box::new(i_f), Box::new(len.clone())),
                Formula::Ge(Box::new(j_f), Box::new(len)),
            ]);
            Some((violation, VcKind::SliceBoundsCheck))
        }
        SliceMethodPanic::VecPanicMethod { index_idx, insert } => {
            // Vec-ONLY receiver gate. A non-Vec `.remove()/.insert()/.swap_remove()` —
            // HashMap/BTreeMap/VecDeque/HashSet (Option/bool return, never panic),
            // String (byte-boundary panic, unmodeled) — yields None: NO obligation,
            // keeps compiling clean (drop-in). Only a genuine owned `Vec` proceeds.
            if !operand_is_owned_container_receiver(func, receiver) {
                return None;
            }
            let _ = index_idx; // index is not referenced in the fail-honest obligation
            let _ = insert;
            // SOUNDNESS (empirically established, 2026-07-07): DO NOT recover
            // `coll_len(base)` for the obligation. `collection_abstract_len_with_base_opts`
            // SUCCEEDS on a `&mut Vec` receiver here, and the recovered `coll_len(v)` can
            // carry a `.len()` tie that SURVIVES an intervening Vec resize the tie-killer
            // does not yet recognize (`remove`/`insert`/`swap_remove` were UNMODELED, so
            // the block-def staleness machinery does not drop the tie across them). Using
            // that `coll_len` FALSE-PROVES a genuinely-OOB program, e.g.
            //   `let n=v.len(); v.remove(0); v.remove(n-1);`   // 2nd remove is OOB
            // where `n == coll_len(v)` survives the first `remove` and makes the obligation
            // `(n-1) >= coll_len(v)` UNSAT (`-1 >= 0`) -> "proved" -> a FALSE-ACCEPT.
            // (`truncate`/`clear` ARE recognized resizes, so a tie is correctly dropped
            // across them; `remove`/`insert` are not, hence this is unsafe.)
            //
            // Until the tie-killer / `coll_len` versioning recognizes these methods
            // (completeness follow-up), we FAIL HONEST: emit an always-SAT violation
            // tagged UnsupportedMir (preclassified Unknown) so the call is NEVER silently
            // verified — closing the pre-existing false-accept (unguarded `v.remove(i)`
            // was reported vacuously safe) WITHOUT ever staking the core invariant on an
            // exploitable stale tie. Sound by construction: `Bool(true)` is never UNSAT,
            // so this obligation is never PROVED; it degrades to a runtime-checked access
            // in the default lane and a hard error under `-full`.
            Some((
                Formula::Bool(true),
                VcKind::UnsupportedMir {
                    kind: "vec-panic-method-index-unmodeled".into(),
                    detail: "Vec::remove/swap_remove/insert index bound: a sound proof \
                             requires resize-aware length tracking (the method's index \
                             precondition `i < len` / `i <= len` cannot be discharged \
                             without recognizing remove/insert/swap_remove as resizes) — \
                             reported Unknown, never silently verified (was a false-accept)"
                        .into(),
                },
            ))
        }
        SliceMethodPanic::RangeIndex => {
            // Scan the call operands for the slice receiver (a modeled `len`, traced
            // through `&(*param)` reborrows to the canonical `param__slice_len` so a
            // `b <= s.len()` guard discharges) and the panicking-range argument
            // (`operand_ty` is `Range`/`RangeTo`/`RangeFrom`/`RangeInclusive`).
            // `None` on either => not a slice range index (scalar `Vec`/`HashMap`
            // index, `RangeFull`, or a non-slice receiver) => sound skip.
            let mut len = None;
            let mut range_operand: Option<&Operand> = None;
            for arg in args {
                if len.is_none() {
                    len = param_slice_len(func, arg, 8)
                        .or_else(|| crate::slice_len_formula(func, arg));
                }
                if range_operand.is_none() && operand_is_panicking_range(func, arg) {
                    range_operand = Some(arg);
                }
            }
            // Trust (#7c owned-Vec SCALAR index `v[i]`): a scalar `usize` index over an
            // OWNED `Vec` receiver — `<Vec<T> as Index<usize>>::index(&v, i)`. Unlike a
            // slice `s[i]` (whose bounds check rustc bakes into a MIR `Assert(Lt(i, Len))`,
            // handled by the rvalue-safety path), the `Vec` index bounds check lives INSIDE
            // the opaque stdlib `index` impl, so no obligation is emitted anywhere today and
            // a panicking `v[2]` is reported vacuously safe (a headline-honesty + soundness
            // gap). Emit the real `i >= len` OOB obligation against the container's ABSTRACT
            // length (`coll_len_var` — the SAME symbol `Vec::len`/`last()` are tied to), so
            // a dominating `if i < v.len()` guard DISCHARGES it and an unguarded `v[i]` FAILS.
            //
            // SOUNDNESS: `collection_abstract_len_with_base` returns `None` (declines) when
            // the base's length is UNRECOVERABLE — a mutably-borrowed / conditionally-merged
            // base (the resize-staleness channels, §4 of the blueprint) — in which case the
            // index is left INVISIBLE (no VC, sound skip: the abstract len would be a stale
            // bound). When it DOES recover a len, that var is UNCONSTRAINED unless the code
            // ties it down (a `.len()` guard), so a bare `i >= len` over it is vacuously
            // SATISFIABLE (still FAILS — never a vacuous PROVE). Gated to a genuine `Vec`
            // receiver by `is_owned_slice_container_name` inside the recovery helper, so a
            // `HashMap`/`BTreeMap`/user-ADT scalar `index` (whose panic semantics differ)
            // never matches — it falls through to the `range_operand?` None-skip below.
            // Only fires when NO panicking range arg is present (a genuine scalar index).
            if range_operand.is_none()
                && let Some(scalar) = args.iter().find(|a| operand_is_scalar_usize_index(func, a))
            {
                if let Some((_base, coll_len)) = args
                    .iter()
                    .filter(|a| !operand_is_scalar_usize_index(func, a))
                    // Peel a SHARED `&Vec` (the `fn f(v: &Vec<T>, i)` param shape); the
                    // RANGE path below keeps `peel_shared_ref = false` so its exclusive-range
                    // refutation on a `&Vec` param is NOT regressed to Unknown.
                    .find_map(|a| collection_abstract_len_with_base_opts(func, a, true))
                {
                    let idx_f = crate::operand_to_formula(func, scalar);
                    // `usize` index is `>= 0` by type, so the ONLY failure is `i >= len`.
                    let violation = Formula::Ge(Box::new(idx_f), Box::new(coll_len));
                    return Some((violation, VcKind::SliceBoundsCheck));
                }
                // FAIL-HONEST backstop: the receiver IS a recognized owned container
                // (`Vec`/`String` by ADT name — the same knowledge the recovery keys
                // on) but its abstract length could not be recovered (resized base,
                // escaping `&mut`, ambiguous conditional merge). The former behavior
                // was a SILENT None-skip — `v[i]`/`v[i] = x` on a resized Vec was
                // reported vacuously safe (the write-path twin of the #7c read gap).
                // A non-recoverable container length is a COVERAGE GAP, not a proof:
                // surface it as `UnsupportedMir` (preclassified Unknown — runtime-
                // checked demotion in the default lane, hard error under `-full`),
                // NEVER silence. HashMap/BTreeMap/user-ADT receivers do not reach
                // here (name gate) — their panic semantics are not a length OOB.
                if args.iter().any(|a| {
                    !operand_is_scalar_usize_index(func, a)
                        && operand_is_owned_container_receiver(func, a)
                }) {
                    return Some((
                        Formula::Bool(true),
                        VcKind::UnsupportedMir {
                            kind: "container-index-unstable-len".into(),
                            detail: "scalar index over an owned Vec/String whose length \
                                     is not recoverable at the access (resized or \
                                     ambiguously-merged receiver) — reported Unknown, \
                                     never silently verified"
                                .into(),
                        },
                    ));
                }
            }
            // FAIL-HONEST backstop for a MAP index `m[&k]` (`HashMap`/`BTreeMap`):
            // the key argument is neither a scalar `usize` (so the Vec-scalar path
            // above did not fire) nor a panicking range (so `range_operand` is
            // None) — the former behavior fell straight through to a SILENT
            // None-skip, reporting a `map[absent_key]` panic as vacuously safe (a
            // panic-freedom false-accept flagged by the vcgen audit). A map index
            // PANICS on an absent key (`get(key).expect(...)`); key-presence needs a
            // map theory to model, so surface it as a visible `UnsupportedMir`
            // (Unknown → runtime-checked in the default lane, hard error under
            // `-full`) — exactly like an unmodeled `Option::unwrap`, never silent.
            if range_operand.is_none()
                && args.iter().any(|a| operand_is_map_container_receiver(func, a))
            {
                return Some((
                    Formula::Bool(true),
                    VcKind::UnsupportedMir {
                        kind: "map-index-key-presence".into(),
                        detail: "index into a HashMap/BTreeMap panics if the key is \
                                 absent; key-presence is not modeled — reported \
                                 Unknown, never silently verified"
                            .into(),
                    },
                ));
            }
            // A panicking range argument is the load-bearing precondition: without
            // one this is not a slice range index (scalar `Vec`/`HashMap` index,
            // `RangeFull`, non-slice receiver) — a sound skip.
            let range_operand = range_operand?;
            // SOUNDNESS (HOLE-6A): `range_operand` is now a CONFIRMED panicking range.
            // If the receiver's `len` could not be modeled — e.g. an OWNED `Vec`/
            // `String` receiver, where the deref-to-slice happens INSIDE the
            // container's `Index` impl so the call-site receiver is `&Vec`/`&String`,
            // never `&[T]` — then `len?` would short-circuit the whole body to `None`
            // and the OOB bounds obligation would VANISH → a vacuous PROVE of a
            // genuinely panicking `v[a..b]`. FAIL CLOSED instead (always-violated;
            // refused unless a guard discharges it, which it cannot without a modeled
            // len), mirroring the aggregate-untraceable fail-close at the `None =>`
            // arm below. Soundness over precision; the precise fix is to model the
            // length of deref-to-slice containers (`Vec`/`String`/`VecDeque`/`Box<[T]>`)
            // in `slice_len_formula`.
            //
            // Trust (Vec-length precision): before failing closed, recover the length
            // from the OWNED container's ABSTRACT var (`coll_len_var` — the same symbol
            // `Vec::len`/`last()` are tied to). An unconstrained abstract len keeps the
            // `end > len` violation SATISFIABLE (still FAILS — no vacuous PROVE), so this
            // only discharges a genuinely-guarded index (`b <= v.len()` or the
            // `last()==Some => len>=1` fact). Strictly more precise, never less sound.
            // `len` here is the HARD, refutable slice length (`slice_len_formula`:
            // `&[T]`/array/`&mut [T]`). When it is absent, the ONLY remaining length is
            // the SOFT abstract placeholder recovered from an OWNED `Vec`'s abstract var
            // (`collection_abstract_len_with_base`). That var is UNCONSTRAINED unless
            // the code ties it down, so a plain `end > len` violation over it is
            // vacuously satisfiable
            // — emitting a REFUTABLE VC there produces a FALSE `REFUTED` on a
            // provably-safe slice (the b7 `chars[..end]` over
            // `value.chars().collect::<Vec<char>>()`: `end <= chars.len()` is a real
            // loop invariant the verifier cannot yet tie back to the non-derivable
            // `chars.len()`). FAIL-HONEST: a non-derivable slice length is a COVERAGE
            // GAP, not a violation, so emit `UnsupportedMir` (→ Unknown), NEVER `failed`.
            // A None soft-len (e.g. the ambiguous conditional-merge `cond_merge_mistie`,
            // whose base is untraceable) is a genuinely-unbounded access that stays the
            // always-violated `Bool(true)` fail-close (refuted), so real OOBs are still
            // caught.
            let len = match len {
                Some(hard) => hard,
                None => {
                    // Recover the OWNED container's abstract len AND its base local (the
                    // base is needed to decide, STRUCTURALLY, whether the range bound is
                    // tied to that length).
                    let soft = args
                        .iter()
                        .filter(|a| !operand_is_panicking_range(func, a))
                        .find_map(|a| collection_abstract_len_with_base(func, a));
                    match soft {
                        // Trust (structural bound tie): back the real bounds VC with the
                        // soft abstract len ONLY when every panicking upper bound provably
                        // reduces to `<= coll_len(base)` by STRUCTURE (a `base'.len() - c`,
                        // c >= 0, over the SAME base). Then the seeded `_len == coll_len(base)`
                        // tie discharges `end > L` (a structural `L - c <= L`), turning a
                        // false-Unknown into a SOUND prove — decided HERE at VC-gen, never
                        // left to the solver. Falls through to the normal emission below
                        // with `len = L`.
                        Some((base, soft_len))
                            if range_bounds_within_abstract_len(func, range_operand, base) =>
                        {
                            soft_len
                        }
                        // A soft len whose bound is NOT structurally tied to it (the b7
                        // `chars[..loop_end]`, bounded only by a semantic loop invariant)
                        // is a COVERAGE GAP, not a violation: emit `UnsupportedMir`
                        // (→ Unknown), NEVER a refutable `failed` that would false-REFUTE a
                        // provably-safe slice.
                        Some(_) => {
                            return Some((
                                Formula::Bool(false),
                                VcKind::UnsupportedMir {
                                    kind: "SliceBoundsCheck".to_string(),
                                    detail: "slice length is a non-derivable owned-Vec \
                                             abstract placeholder; fail-honest to Unknown \
                                             rather than false-REFUTE a provably-safe slice"
                                        .to_string(),
                                },
                            ));
                        }
                        // A None soft-len (ambiguous conditional-merge base) is a genuinely
                        // unbounded access — keep the always-violated fail-close (refuted) so
                        // real OOBs are still caught.
                        None => return Some((Formula::Bool(true), VcKind::SliceBoundsCheck)),
                    }
                }
            };
            // Trace the range aggregate to its bound operands. Bounds are `usize`
            // (>= 0 by type), so the only failures are the upper-bound `end > len` /
            // `start > len` and the exclusive-range ordering `start > end`.
            let range_local = match range_operand {
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
                _ => None,
            };
            // Trust (R2 family 1 — CharIndices yields): a bound that IS a traced
            // `char_indices()` yield of the SLICED string satisfies `0 <= i` and
            // `i <= len - 1` AND is a char boundary, by the iterator contract (see
            // the module banner at `operand_is_charindices_yield_of` for the
            // theorem + the gates). Conjoin those two linear facts VC-LOCALLY onto
            // the violation — ay's strict Farkas lane then proves the bounds
            // disjunct UNSAT and the proof kernel-certifies through the normal
            // lane. VC-local scoping is the soundness design: the facts can
            // discharge ONLY this slice's own obligation (which the boundary
            // theorem covers exactly), never a DERIVED index's bounds VC — a
            // global `i < len` fact would bounds-prove `&s[i-1..]`, which panics
            // mid-char on the unmodeled str char-boundary check (a false proof).
            // The facts attach only when EVERY explicit endpoint is boundary-safe
            // (a traced yield, or the constant 0): with a non-boundary-safe
            // endpoint anywhere in the range, its char-boundary panic is not in
            // the formula and NOTHING may make this VC provable (e.g. a
            // len-guarded non-boundary `&s[1..i]` must stay refutable). The
            // `start > end` ordering disjunct is NEVER discharged by the facts
            // alone (two yields are not structurally ordered) — only a user guard
            // or a constant-0 start (`0 <= end` from the yield fact) refutes it.
            let charindices_roots: FxHashSet<usize> = args
                .iter()
                .filter(|a| !operand_is_panicking_range(func, a))
                .filter_map(|a| charindices_shared_slice_root(func, a))
                .collect();
            let bound_is_yield =
                |op: &Operand| operand_is_charindices_yield_of(func, op, &charindices_roots);
            let bound_is_zero =
                |op: &Operand| matches!(op, Operand::Constant(ConstValue::Uint(0, _)));
            let yield_facts = |op: &Operand, len: &Formula| -> Vec<Formula> {
                let x = resolve_range_bound_formula(func, op, 8);
                vec![
                    Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(0))),
                    Formula::Le(
                        Box::new(x),
                        Box::new(Formula::Sub(Box::new(len.clone()), Box::new(Formula::Int(1)))),
                    ),
                ]
            };
            // Resolve each bound with `resolve_range_bound_formula` (NOT plain
            // `operand_to_formula`): it traces the `Range { start: _t, .. }` field
            // operand through its `_t = a` Use-copy to the underlying param symbol
            // and canonicalizes a `PtrMetadata`/`Len` bound to the same
            // `slice_len_formula` term — so a `b <= s.len()` guard discharges the
            // `b > len` violation (exactly how the range-iterator yield facts connect).
            let violation = match range_local.and_then(|l| trace_local_to_range_family(func, l, 8))
            {
                Some(RangeFamilyOperands::Exclusive(start, end)) => {
                    let s = resolve_range_bound_formula(func, start, 8);
                    let e = resolve_range_bound_formula(func, end, 8);
                    let base = Formula::Or(vec![
                        Formula::Gt(Box::new(s), Box::new(e.clone())),
                        Formula::Gt(Box::new(e), Box::new(len.clone())),
                    ]);
                    let start_safe = bound_is_zero(start) || bound_is_yield(start);
                    let end_safe = bound_is_zero(end) || bound_is_yield(end);
                    if start_safe && end_safe {
                        let mut conjuncts = Vec::new();
                        if bound_is_yield(start) {
                            conjuncts.extend(yield_facts(start, &len));
                        }
                        if bound_is_yield(end) {
                            conjuncts.extend(yield_facts(end, &len));
                        }
                        if conjuncts.is_empty() {
                            base
                        } else {
                            conjuncts.push(base);
                            Formula::And(conjuncts)
                        }
                    } else {
                        base
                    }
                }
                Some(RangeFamilyOperands::To(end)) => {
                    // `&s[..i]` at a yielded `i`: `i <= len - 1` refutes `i > len`;
                    // start 0 is always a boundary — panic-free by the contract.
                    let e = resolve_range_bound_formula(func, end, 8);
                    let base = Formula::Gt(Box::new(e), Box::new(len.clone()));
                    if bound_is_yield(end) {
                        let mut conjuncts = yield_facts(end, &len);
                        conjuncts.push(base);
                        Formula::And(conjuncts)
                    } else {
                        base
                    }
                }
                Some(RangeFamilyOperands::From(start)) => {
                    // `&s[i..]` at a yielded `i`: `i <= len - 1` refutes `i > len`;
                    // the implicit end `len` is trivially valid — panic-free (the
                    // heck `capitalize` idiom).
                    let s = resolve_range_bound_formula(func, start, 8);
                    let base = Formula::Gt(Box::new(s), Box::new(len.clone()));
                    if bound_is_yield(start) {
                        let mut conjuncts = yield_facts(start, &len);
                        conjuncts.push(base);
                        Formula::And(conjuncts)
                    } else {
                        base
                    }
                }
                // `range_operand` is CONFIRMED a panicking range
                // (`operand_is_panicking_range`), but its aggregate could not be
                // traced to bounds — a `RangeInclusive` (the `+1` is not modeled),
                // a by-param `Range<usize>`, or a cross-block construction. A missing
                // bound is a MISSING OOB obligation, so FAIL CLOSED (always-violated)
                // rather than silently skip — soundness over precision. (`RangeFull`
                // is excluded by `operand_is_panicking_range`, so a genuinely-total
                // `s[..]` never reaches here.)
                None => Formula::Bool(true),
            };
            // Trust (str char-boundary SOUNDNESS): the `violation` above models
            // ONLY the byte-bounds panic (`end > len` / `start > len` / `start >
            // end`). A `str` range-slice ALSO panics on the UTF-8 char-boundary
            // check (`&s[cut..]` with `cut` mid-multibyte-char), which is not a
            // formula term (`str` is extracted as `[u8]`). So a byte-bounds PROOF
            // does not establish panic-freedom for a str receiver — e.g. a
            // `s.as_bytes()` scan under `while i < bytes.len()` proves `i + 1 <=
            // len` yet `&s[i + 1..]` panics mid-char. Fail closed unless EVERY
            // explicit endpoint is PROVABLY a char boundary: a `char_indices()`
            // yield (the existing structural credit, which also makes the bounds
            // disjunct provable) or the constant 0. The implicit endpoints are
            // boundaries by construction — `..e` starts at 0, `s..` ends at `len`
            // (a string's byte length is always a boundary) — so only the EXPLICIT
            // endpoint(s) are checked. `[u8]`/`[T]` slices (`receiver_is_str ==
            // false`) are untouched: they carry no char-boundary panic. This is a
            // fail-closed OVER-refutation of a str slice at a non-yield computed
            // offset (sound; a genuinely boundary-safe computed offset that is not
            // a traced yield is conservatively rejected), never a false PROVE.
            let violation = if receiver_is_str {
                let endpoint_boundary_safe = |op: &Operand| bound_is_zero(op) || bound_is_yield(op);
                let endpoints_safe =
                    match range_local.and_then(|l| trace_local_to_range_family(func, l, 8)) {
                        Some(RangeFamilyOperands::Exclusive(start, end)) => {
                            endpoint_boundary_safe(start) && endpoint_boundary_safe(end)
                        }
                        Some(RangeFamilyOperands::To(end)) => endpoint_boundary_safe(end),
                        Some(RangeFamilyOperands::From(start)) => endpoint_boundary_safe(start),
                        // Untraceable range — already the `Bool(true)` fail-close.
                        None => false,
                    };
                if endpoints_safe { violation } else { Formula::Bool(true) }
            } else {
                violation
            };
            Some((violation, VcKind::SliceBoundsCheck))
        }
    }
}

/// Build the overflow *failure* body for a recognized arithmetic call. Returns
/// `None` (no obligation) when the call is provably non-overflowing from its
/// argument constants alone, mirroring how the BinaryOp path skips trivially
/// safe ops. The returned body is the un-guarded failure condition; the caller
/// (`generate_v2_safety_vcs`) conjoins block-defs, path/semantic guards,
/// preconditions and parameter type-ranges, so a dominating bound DISCHARGES it.
pub(super) fn v2_overflow_call_body(
    func: &VerifiableFunction,
    kind: OverflowCall,
    args: &[Operand],
    dest: &Place,
) -> Option<(Formula, BinOp, Ty, Ty, u32)> {
    match kind {
        OverflowCall::Unchecked(op) => {
            // `unchecked_{add,sub,mul}(a, b)`: identical obligation to the inner
            // `a op b`. The args are evaluated before the call, so there are no
            // in-block defs to take "before the statement" — pass the operands to
            // the same builder the direct-BinaryOp path uses and reuse its body.
            let lhs = args.first()?;
            let rhs = args.get(1)?;
            let lhs_ty = crate::operand_ty(func, lhs)?;
            let rhs_ty = crate::operand_ty(func, rhs)?;
            let (width, signed) = int_op_type(func, lhs, rhs)?;
            let lhs_f = operand_to_formula(func, lhs);
            let rhs_f = operand_to_formula(func, rhs);
            let result = match op {
                BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
                BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
                BinOp::Mul => Formula::Mul(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
                _ => return None,
            };
            let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
            let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);
            let min_f = crate::range::type_min_formula(width, signed);
            let max_f = crate::range::type_max_formula(width, signed);
            let out_of_range = Formula::Or(vec![
                Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
                Formula::Gt(Box::new(result), Box::new(max_f)),
            ]);
            let body = Formula::And(vec![lhs_range, rhs_range, out_of_range]);
            // `width` is the REAL operand width (`int_op_type`, non-constant operand);
            // the call arm records it on the authenticated obligation.
            Some((body, op, lhs_ty, rhs_ty, width))
        }
        OverflowCall::Pow => {
            // `base.pow(exp)` — the receiver is the first arg, the exponent the
            // second. The result type == receiver type for `pow`; take the width
            // from the destination place (falling back to the base operand).
            let base = args.first()?;
            let exp = args.get(1)?;
            let result_ty =
                crate::place_ty(func, dest).or_else(|| crate::operand_ty(func, base))?;
            let width = result_ty.int_width()?;
            let signed = result_ty.is_signed();
            let max_f = crate::range::type_max_formula(width, signed);
            let min_f = crate::range::type_min_formula(width, signed);

            let base_f = operand_to_formula(func, base);

            // A literal base `0` or `1` makes `base^exp` `0`/`1`: never overflows.
            // Skip (mirrors the BinaryOp path skipping a provably-safe op).
            if let Some(b) = const_int_value(base)
                && (b == 0 || b == 1)
            {
                return None;
            }

            // BOTH operands literal: decide overflow concretely and skip the
            // obligation entirely when `base^exp` provably fits (e.g. `2u32.pow(3)`
            // == 8). Mirrors the const-size allocation skip — a trivially-safe
            // constant must produce no obligation at all, not a vacuous one.
            if let (Some(b), Some(e)) = (const_int_value(base), const_int_value(exp))
                && b >= 0
                && e >= 0
            {
                let max = if signed {
                    crate::range::signed_max(width).max(0) as u128
                } else {
                    crate::range::unsigned_max(width)
                };
                let mut acc: u128 = 1;
                let mut fits = true;
                for _ in 0..e {
                    match acc.checked_mul(b as u128) {
                        Some(v) if v <= max => acc = v,
                        _ => {
                            fits = false;
                            break;
                        }
                    }
                }
                if fits {
                    return None;
                }
                // Provably-overflowing constant pow: emit a fail-closed obligation.
                return Some((Formula::Bool(true), BinOp::Mul, result_ty.clone(), result_ty, width));
            }

            // CONSTANT exponent (the dominant case: `.pow(2)`, `.pow(3)`). Unroll
            // `base^e` into `e - 1` multiplications and build the LIA overflow
            // failure body `base^e > max OR base^e < min` over the REAL operand
            // name. This is the same `result > max | result < min` shape the Mul
            // path uses, kept on the Int/LIA path so the caller's conjoined
            // operand ranges + any dominating `#[requires(base < K)]` precondition
            // DISCHARGE it (`n.pow(2)` with `n < 100` proves: `100*100` fits),
            // while an unbounded base FAILS. `e == 0`/`e == 1` never overflow.
            if let Some(e) = const_int_value(exp) {
                if e < 0 {
                    return None; // not a valid unsigned exponent; nothing to model
                }
                if e <= 1 {
                    return None; // base^0 == 1, base^1 == base: cannot overflow
                }
                // Cap the unroll so a pathological constant exponent cannot blow up
                // the formula; beyond the bit width even base 2 overflows, so a
                // large constant exponent always fails — fall through to the
                // symbolic threshold model for those.
                if e <= i128::from(width) {
                    let mut product = base_f.clone();
                    for _ in 1..e {
                        product = Formula::Mul(Box::new(product), Box::new(base_f.clone()));
                    }
                    let out_of_range = Formula::Or(vec![
                        Formula::Gt(Box::new(product.clone()), Box::new(max_f)),
                        Formula::Lt(Box::new(product), Box::new(min_f)),
                    ]);
                    let base_range = crate::range::input_range_constraint(&base_f, width, signed);
                    let body = Formula::And(vec![base_range, out_of_range]);
                    return Some((body, BinOp::Mul, result_ty.clone(), result_ty, width));
                }
            }

            // SYMBOLIC (or huge-constant) exponent. `base^exp` is undecidable to
            // model exactly in LIA; use the sound linear over-approximation: for
            // `base >= 2`, `base^exp >= 2^exp`, which already exceeds the max once
            // `exp >= bit_width` (unsigned) / `exp >= bit_width - 1` (signed). So
            // the failure body is `base >= 2 AND exp >= threshold` — conjoined
            // later with type-ranges + a dominating `#[requires(exp < W)]` guard,
            // which discharges it; an unbounded exponent fails.
            let exp_f = operand_to_formula(func, exp);
            let exp_threshold: i128 =
                if signed { i128::from(width) - 1 } else { i128::from(width) };
            let base_big = Formula::Ge(Box::new(base_f), Box::new(Formula::Int(2)));
            let exp_big = Formula::Ge(Box::new(exp_f), Box::new(Formula::Int(exp_threshold)));
            let body = Formula::And(vec![base_big, exp_big]);
            Some((body, BinOp::Mul, result_ty.clone(), result_ty, width))
        }
    }
}

/// The signed integer value of a literal operand, if it is one.
pub(super) fn const_int_value(op: &Operand) -> Option<i128> {
    match op {
        Operand::Constant(ConstValue::Int(v)) => Some(*v),
        Operand::Constant(ConstValue::Uint(v, _)) => i128::try_from(*v).ok(),
        _ => None,
    }
}
