// Slice-to-array conversions and the range arithmetic behind them. A
// conversion is infallible exactly when the slice's static length matches the
// target array, so the range bounds have to be resolved affinely before the
// panic edge can be ruled out.

use super::*;

pub(super) fn unwrap_is_infallible_slice_to_array(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    dest: &Place,
) -> bool {
    // Only `Result::unwrap` — the receiver's sole failure path is `Err`. Be
    // conservative for `expect`/`unwrap_err`/`Option::unwrap` (kept as Unknown).
    if method_tail(callee) != "unwrap"
        || !((callee.starts_with("core::") || callee.starts_with("std::"))
            && callee.contains("::result::Result"))
    {
        return false;
    }
    // The unwrap output type must itself be the array `[T; N]` (the `Ok` payload).
    let Some(n_out) = array_len_of(func, dest) else {
        return false;
    };
    // The receiver `_r` must be a bare-local value (no projections).
    let [recv] = args else {
        return false;
    };
    let (Operand::Copy(recv_place) | Operand::Move(recv_place)) = recv else {
        return false;
    };
    if !recv_place.projections.is_empty() {
        return false;
    }
    // `_r` must be defined by EXACTLY ONE slice->array conversion `Call`.
    let Some((conv_args, conv_dest)) = unique_whole_local_conversion_call(func, recv_place.local)
    else {
        return false;
    };
    // The array length `N` taken from the conversion RESULT type
    // (`Result<[T; N], _>`) — when the extractor preserves it — must AGREE with the
    // unwrap output array length. The unwrap's own output type (`n_out`) is the
    // AUTHORITATIVE `N` (it is exactly the `Ok` payload `[T; N]`), so a Result whose
    // enum payload the extractor flattens away (no array field) does NOT block the
    // proof; it only adds a cross-check when present. A PRESENT-but-DIFFERENT `N`
    // means we mis-traced the def chain — fail closed.
    if let Some(n_res) = array_len_of_result(func, conv_dest)
        && n_res != n_out
    {
        return false;
    }
    // The conversion's slice ARGUMENT must have a STATICALLY-KNOWN length == N.
    let [slice_arg] = conv_args.as_slice() else {
        return false;
    };
    let (Operand::Copy(slice_place) | Operand::Move(slice_place)) = slice_arg else {
        return false;
    };
    slice_arg_static_len(func, slice_place, 8) == Some(n_out)
}

/// The unique `Call` terminator that defines whole-local `local`, when its callee
/// is a slice->array `TryInto::try_into` / `TryFrom::try_from` conversion. Returns
/// the conversion's `(args, dest)`. `None` on no def, a non-conversion callee, a
/// projected/duplicate def (ambiguous), or any `dest` projection.
pub(super) fn unique_whole_local_conversion_call<'a>(
    func: &'a VerifiableFunction,
    local: usize,
) -> Option<(&'a Vec<Operand>, &'a Place)> {
    let mut found: Option<(&'a Vec<Operand>, &'a Place)> = None;
    for block in &func.body.blocks {
        // A statement-level whole-local re-def makes `_r` ambiguous: bail.
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place.local == local
            {
                return None;
            }
        }
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
        {
            if !dest.projections.is_empty() {
                return None;
            }
            if !is_slice_to_array_conversion(callee) {
                return None;
            }
            if found.is_some() {
                return None; // more than one def — ambiguous
            }
            found = Some((args, dest));
        }
    }
    found
}

/// `true` for the slice->array `TryInto`/`TryFrom` conversion methods. The result
/// is `Ok` IFF the slice length equals the target array length, so a statically
/// length-`N` slice into `[T; N]` is infallible. The trait path is anchored at
/// `core`/`std` (or a qualified canonical `TryFrom`/`TryInto` spelling); a
/// same-named user conversion keeps the unwrap obligation.
pub(super) fn is_slice_to_array_conversion(callee: &str) -> bool {
    matches!(method_tail(callee), "try_into" | "try_from")
        && (((callee.starts_with("core::") || callee.starts_with("std::"))
            && callee.contains("::convert::"))
            || callee.contains("as core::convert::TryFrom<")
            || callee.contains("as std::convert::TryFrom<")
            || callee.contains("as core::convert::TryInto<")
            || callee.contains("as std::convert::TryInto<")
            || callee.contains("as TryFrom<")
            || callee.contains("as TryInto<"))
}

/// Array length `N` of a place whose type is `[T; N]` (`Ty::Array`). `None` for any
/// other type — including a SLICE `[T]` (no static length), so a slice receiver can
/// never be mistaken for a fixed-length array.
pub(super) fn array_len_of(func: &VerifiableFunction, place: &Place) -> Option<u64> {
    if !place.projections.is_empty() {
        return None;
    }
    match &func.body.locals.get(place.local)?.ty {
        Ty::Array { len, .. } => Some(*len),
        _ => None,
    }
}

/// Array length `N` of a place whose type is `Result<[T; N], _>` — the success
/// payload of a slice->array conversion. `None` unless the first ADT field is an
/// `[T; N]` array (a slice/other payload yields no static length, so no proof).
pub(super) fn array_len_of_result(func: &VerifiableFunction, place: &Place) -> Option<u64> {
    if !place.projections.is_empty() {
        return None;
    }
    let Ty::Adt { name, fields, .. } = &func.body.locals.get(place.local)?.ty else {
        return None;
    };
    if !name.contains("Result") {
        return None;
    }
    // The `Ok` payload type is the array length source; find an array field.
    fields.iter().find_map(|(_, ty)| match ty {
        Ty::Array { len, .. } => Some(*len),
        _ => None,
    })
}

/// STATICALLY-KNOWN length of the `&[T]` value handed to a slice->array
/// conversion, or `None` when the length is not a compile-time constant (in which
/// case the caller KEEPS the unwrap obligation — never assumes the length).
///
/// Real MIR for `bytes[0..8]` is NOT a `Subslice` projection: a CONSTANT range
/// index on a slice lowers to `<[T] as Index<Range<usize>>>::index(bytes, 0..8)`,
/// returning a fresh `&[T]` whose length is `end - start`. So the static length is
/// recovered by tracing the slice-value local back to that `index` call and
/// reading its `Range` aggregate's CONSTANT `start`/`end`. The two channels:
///   (a) a CONSTANT `Subslice { from, to, from_end: false }` projection (slice
///       PATTERN binding `let [.., a @ ..]`): length `to - from`;
///   (b) the result of a `slice::index`-family `Call` whose range argument is a
///       `Range` aggregate with a CONSTANT length `end - start` — either both
///       bounds constant (`s[2..10]`) OR a CONSTANT-DIFFERENCE affine pair
///       (`s[off..off+8]`, `s[off+8..off+16]`: bounds non-constant but linear in a
///       common base with constant difference). See [`range_aggregate_const_len`].
///   (d) the result of a `slice::index`-family `Call` whose range argument is a
///       `RangeFrom` aggregate `s[start..]` with `start` PROVABLY `Len(s) - K` for a
///       constant `K >= 0` — length `K` (`s.len() - start == K`). The indexed
///       receiver must be the SAME built-in slice/array whose length defines
///       `start`. See [`range_from_const_len`].
/// A `from_end` subslice, a `RangeTo`/`RangeInclusive`/`RangeFull`, a `RangeFrom`
/// whose `start` is NOT provably `Len(receiver) - K`, or a non-constant-DIFFERENCE
/// range yields `None`: the length then depends on a runtime value, so the
/// conversion is NOT provably infallible and the obligation is kept.
///
/// `fuel` bounds the whole-local `Use`/`Ref`/`CopyForDeref` hop chain so a
/// pathological MIR cannot loop.
pub(super) fn slice_arg_static_len(func: &VerifiableFunction, place: &Place, fuel: u32) -> Option<u64> {
    if fuel == 0 {
        return None;
    }
    // (a) A constant subslice PATTERN projection carries the length directly.
    if let Some(trust_types::Projection::Subslice { from, to, from_end: false }) =
        place.projections.last()
        && to >= from
    {
        return Some((*to - *from) as u64);
    }
    // Only follow BARE-LOCAL value flow; a projected place is not a transparent
    // copy of a slice value we can trace.
    if !place.projections.is_empty() {
        return None;
    }
    let local = place.local;
    // (b) The local is the dest of a `slice::index`-family conversion `Call`:
    // recover the length from its constant `Range` argument.
    //
    // SOUNDNESS: the `end - start == result length` contract holds ONLY for the
    // library `<[T] as Index<Range>>::index` impl. A USER `impl Index<Range,
    // Output = [T]>` renders as the SAME trait method path
    // (`core::ops::index::Index::index`) yet may return a slice of ANY length, so
    // `s[0..8].try_into::<[u8; 8]>().unwrap()` could panic. We therefore REQUIRE
    // the indexed receiver `args[0]` to be a built-in slice/array (or a reference
    // to one); on any other receiver type — or an unknown type — we decline
    // (return `None`) and KEEP the unwrap obligation. (`index_mut` likewise.)
    //
    // The index-call def of `local` must be UNIQUE: a local that is the dest of
    // more than one `Call` has a path-dependent value (a length valid on one path
    // can be wrong on another), so a duplicate index def declines (fail-closed).
    // A separate `Statement::Assign` to `local` (the transparent-copy channel
    // below) is allowed only when there is NO index def for this local; if BOTH an
    // index def and a statement def exist, the value is ambiguous and we bail.
    let mut idx_def: Option<&Vec<Operand>> = None;
    let mut stmt_def_seen = false;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place.local == local
                && place.projections.first() != Some(&trust_types::Projection::Deref)
            {
                stmt_def_seen = true;
            }
        }
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
            && is_slice_index_call(callee)
        {
            if idx_def.is_some() {
                return None; // more than one index def — ambiguous
            }
            idx_def = Some(args);
        }
    }
    if let Some(args) = idx_def {
        if stmt_def_seen {
            return None; // index def co-exists with a statement def — ambiguous
        }
        let recv = args.first()?;
        if !operand_is_builtin_slice_or_array(func, recv) {
            return None;
        }
        // (c) constant / constant-difference `Range` length; then (d) a `RangeFrom`
        // `s[L-K..]` whose `start` is provably `Len(receiver) - K` (length `K`).
        return args.iter().find_map(|a| {
            range_aggregate_const_len(func, a).or_else(|| range_from_const_len(func, recv, a))
        });
    }
    // Transparent whole-local copies: `_s = Use(_t)` / `_s = &_t` / deref-copy.
    match crate::unique_whole_local_def(func, local)? {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) | Rvalue::CopyForDeref(p) => {
            slice_arg_static_len(func, p, fuel - 1)
        }
        Rvalue::Ref { place: p, .. } => slice_arg_static_len(func, p, fuel - 1),
        _ => None,
    }
}

/// `true` for the slice `Index`/`IndexMut` trait method (`s[range]` ->
/// `<[T] as Index<R>>::index(s, range)`), matched on the method tail so the erased
/// generic callee path is handled. A non-match yields no static length (sound).
pub(super) fn is_slice_index_call(callee: &str) -> bool {
    matches!(method_tail(callee), "index" | "index_mut")
}

/// `true` IFF `op`'s type is a BUILT-IN slice `[T]` or array `[T; N]`, possibly
/// behind a single reference (`&[T]`, `&[T; N]`). This is the receiver-type guard
/// for the `Index::index` length contract: the `result.len() == end - start`
/// equality is guaranteed ONLY by the standard-library `<[T] as Index<Range>>`
/// impl, NOT by a user `impl Index<Range, Output = [T]>` (which shares the trait
/// method path). An unknown type (`operand_ty` -> `None`), a non-slice ADT, a
/// `str`, or any other receiver yields `false` -> the caller declines and keeps
/// the unwrap obligation (fail-closed).
pub(super) fn operand_is_builtin_slice_or_array(func: &VerifiableFunction, op: &Operand) -> bool {
    let Some(ty) = crate::operand_ty_cow(func, op) else {
        return false;
    };
    let ty = match ty.as_ref() {
        Ty::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    matches!(ty, Ty::Slice { .. } | Ty::Array { .. })
}

/// If `op` is (or whole-local-traces to) a `Range { start, end }` aggregate whose
/// length `end - start` is a compile-time CONSTANT `N`, return `N` — the length of
/// `s[start..end]`. Two SOUND length sources:
///   (b) BOTH bounds compile-time constants (`s[2..10]`): length `end - start`.
///   (c) CONSTANT-DIFFERENCE bounds (`s[off..off+8]`, `s[off+8..off+16]`): `start`
///       and `end` are non-constant but AFFINE in a COMMON base local with a
///       constant difference — `end - start` const-folds to `N` independent of the
///       (runtime) base value, so `s[start..end]` always has length `N`. See
///       [`range_bound_affine`] for the affine recovery and its soundness.
/// `None` for any other range family (`RangeFrom`/`RangeTo`/`RangeInclusive`/
/// `RangeFull`), a non-affine bound, distinct base locals in the two bounds, or a
/// negative difference, so a runtime-variable range never yields a (false) static
/// length.
pub(super) fn range_aggregate_const_len(func: &VerifiableFunction, op: &Operand) -> Option<u64> {
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return None;
    };
    if !p.projections.is_empty() {
        return None;
    }
    let Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, operands) =
        crate::unique_whole_local_def(func, p.local)?
    else {
        return None;
    };
    if !aggregate_is_exclusive_range(name) {
        return None;
    }
    let [start, end] = operands.as_slice() else {
        return None;
    };
    // (c) CONSTANT-DIFFERENCE: resolve each bound to `base*1 + offset` affine form.
    // The slice length is `end - start`; when both bounds share the SAME base local
    // (or both are pure constants — base `None`), the base term cancels and the
    // length is the constant `end.offset - start.offset`, valid for EVERY runtime
    // value of the base. (Case (b) is the all-constant special case: base `None` on
    // both, handled uniformly here.) Distinct base locals, a non-affine bound, or a
    // negative difference -> `None` (decline; the unwrap obligation is kept).
    let (start_base, start_off) = range_bound_affine(func, start, 8)?;
    let (end_base, end_off) = range_bound_affine(func, end, 8)?;
    if start_base != end_base {
        return None;
    }
    let diff = end_off.checked_sub(start_off)?;
    u64::try_from(diff).ok()
}

/// (d) RANGEFROM length recovery. If `op` is (or whole-local-traces to) a
/// `RangeFrom { start }` aggregate whose `start` is provably `Len(receiver) - K`
/// for a CONSTANT `K >= 0`, return `K` — the length of `receiver[start..]` (which
/// is exactly `receiver.len() - start == receiver.len() - (receiver.len() - K) ==
/// K`). `receiver` is the SAME operand the `slice::index` Call indexes (`args[0]`,
/// already proven a built-in slice/array by the caller), so the
/// `len == receiver.len() - start` contract is the library `<[T] as
/// Index<RangeFrom>>::index` guarantee — not a user impl.
///
/// SOUNDNESS — every gate is a HARD requirement; ANY ambiguity returns `None`
/// (keep the unwrap obligation):
///   * `op` whole-local-traces to a `RangeFrom` aggregate with exactly one bound.
///   * `start` resolves (via [`range_bound_affine`]) to AFFINE form `(Some(L), off)`
///     — a SINGLE symbolic base local `L` with constant offset `off`. The recovered
///     length is `-off` (i.e. `start = L - K` with `K = -off`); `off` must be `<= 0`
///     and `K = -off` must be a non-negative `u64`. A pure-constant `start`
///     (`base None`) is REJECTED here (no length-relative recovery — that is the
///     `RangeTo`/`RangeFull` realm and not provably `len - K`).
///   * The base local `L` is provably `Len(receiver)`: `L`'s UNIQUE whole-local def
///     is `UnaryOp(PtrMetadata, p)` (the fat-pointer-metadata lowering of
///     `slice.len()`) or `Len(p)`, where `p` refers to the SAME place as `receiver`.
///     A different base, a `start` not of the `len - K` shape, or a `RangeFrom` on a
///     length var belonging to ANOTHER slice all decline (the place-equality check
///     below pins `L = Len(receiver)`, never `Len(other)`).
pub(super) fn range_from_const_len(
    func: &VerifiableFunction,
    receiver: &Operand,
    op: &Operand,
) -> Option<u64> {
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return None;
    };
    if !p.projections.is_empty() {
        return None;
    }
    let Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, operands) =
        crate::unique_whole_local_def(func, p.local)?
    else {
        return None;
    };
    if range_family_adt_name(name) != Some("RangeFrom") {
        return None;
    }
    let [start] = operands.as_slice() else {
        return None;
    };
    // `start` must be `L - K` (`K >= 0`) with `L` a single symbolic base local.
    let (Some(base), off) = range_bound_affine(func, start, 8)? else {
        return None; // pure-constant start: not a `len - K` form, decline.
    };
    let k = u64::try_from(off.checked_neg()?).ok()?; // off <= 0, K = -off >= 0
    // `base` (the local `L`) must provably be `Len(receiver)`.
    if !local_is_len_of(func, base, receiver) {
        return None;
    }
    Some(k)
}

/// `true` IFF whole-local `len_local` is provably the LENGTH of `receiver`: its
/// unique whole-local def is `UnaryOp(PtrMetadata, q)` (the `&[T]`/`&str` fat-pointer
/// `.len()` lowering) or `Len(q)`, where `q`'s underlying place EQUALS `receiver`'s
/// place. A bare-local `receiver` whose place matches the length-source place pins
/// `len_local == receiver.len()` exactly; any other def, a projected place, or a
/// place mismatch (a length var of a DIFFERENT slice) returns `false` (decline).
pub(super) fn local_is_len_of(func: &VerifiableFunction, len_local: usize, receiver: &Operand) -> bool {
    let (Operand::Copy(recv_place) | Operand::Move(recv_place)) = receiver else {
        return false;
    };
    let inner_place = match crate::unique_whole_local_def(func, len_local) {
        Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => match inner {
            Operand::Copy(q) | Operand::Move(q) => q,
            _ => return false,
        },
        Some(Rvalue::Len(q)) => q,
        _ => return false,
    };
    inner_place == recv_place
}

/// Resolve a `Range`/index bound operand to AFFINE form `base * 1 + offset`,
/// returning `(base_local, offset)` where `base_local: Option<usize>` is the single
/// symbolic local the bound is linear in (`None` for a pure constant) and `offset`
/// is the constant addend (`i128`, may be negative through `Sub`). The COEFFICIENT
/// on `base` is implicitly `1`: only `base +/- const`, `const +/- base`, and chains
/// thereof are recovered — never `2*base`, `base + other_base`, or a scaled term —
/// so `end - start` cancels the base IFF the two bounds carry the SAME base local
/// (the only way `range_aggregate_const_len` consumes this).
///
/// SOUNDNESS: every recovered shape preserves the EXACT integer value
/// `base + offset` (mod nothing — these are the in-bounds `usize` index values the
/// `BoundsCheck`/`<[T] as Index>::index` obligation separately constrains to not
/// wrap). A bound we cannot prove affine in a single base returns `None` (decline),
/// so a length is never recovered from an unmodeled bound. MIR shapes handled:
///   - `Constant(usize)`                              -> `(None, c)`
///   - bare local with NO def (a fn param / argument) -> `(Some(local), 0)` (base)
///   - `_t = Use(Copy/Move(src))` (transparent copy)  -> recurse on `src`
///   - `_t = (_c.0)` field-0 of a `CheckedBinaryOp`   -> resolve that checked op
///   - `(Checked)BinaryOp(Add, a, b)`                 -> affine-sum (at most one base)
///   - `(Checked)BinaryOp(Sub, a, b)`                 -> `a - b`, `b` must be const
///   - any other def                                  -> `(Some(local), 0)` (opaque
///     base: SOUND — naming the local as the base is exact; it only fails to CANCEL
///     against a differently-shaped bound, which then declines).
/// `fuel` bounds the def-chain hops so pathological MIR cannot loop.
pub(super) fn range_bound_affine(
    func: &VerifiableFunction,
    op: &Operand,
    fuel: u32,
) -> Option<(Option<usize>, i128)> {
    if fuel == 0 {
        return None;
    }
    let p = match op {
        Operand::Constant(_) => return Some((None, i128::from(const_usize_operand(op)?))),
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    // `_t = (_c.0)`: field-0 read of a `CheckedBinaryOp` result tuple `(value, did_overflow)`.
    // The VALUE is field 0; resolve the underlying checked op as if it produced it.
    if let [trust_types::Projection::Field(0)] = p.projections.as_slice() {
        return range_bound_from_binop_def(func, p.local, fuel);
    }
    if !p.projections.is_empty() {
        return None;
    }
    // Bare local: a fn param/arg has no in-body def -> it IS the base (offset 0).
    let Some(def) = crate::unique_whole_local_def(func, p.local) else {
        return Some((Some(p.local), 0));
    };
    match def {
        Rvalue::Use(inner) => range_bound_affine(func, inner, fuel - 1),
        Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub), a, b)
        | Rvalue::CheckedBinaryOp(op @ (BinOp::Add | BinOp::Sub), a, b) => {
            range_bound_combine(func, *op, a, b, fuel)
        }
        // Any other def: name this local as the (opaque) base. Exact for `base+0`;
        // it cancels only against a bound carrying the same local.
        _ => Some((Some(p.local), 0)),
    }
}

/// Resolve the affine form of the VALUE field of `CheckedBinaryOp`-defined local
/// `t` (i.e. the `_t = (_c.0)` indirection where `_c = AddWithOverflow(..)`). Only
/// `Add`/`Sub` checked ops are affine; anything else declines.
pub(super) fn range_bound_from_binop_def(
    func: &VerifiableFunction,
    t: usize,
    fuel: u32,
) -> Option<(Option<usize>, i128)> {
    match crate::unique_whole_local_def(func, t)? {
        Rvalue::CheckedBinaryOp(op @ (BinOp::Add | BinOp::Sub), a, b)
        | Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub), a, b) => {
            range_bound_combine(func, *op, a, b, fuel)
        }
        _ => None,
    }
}

/// Combine the affine forms of `a` and `b` under `Add`/`Sub`. At most ONE operand
/// may carry a base local (the coefficient on `base` stays `1`); a `Sub` requires
/// the SUBTRAHEND `b` to be a pure constant (subtracting a symbolic base would
/// negate its coefficient, which the single-base model cannot represent). Two
/// distinct bases, or a base in the subtrahend, decline.
pub(super) fn range_bound_combine(
    func: &VerifiableFunction,
    op: BinOp,
    a: &Operand,
    b: &Operand,
    fuel: u32,
) -> Option<(Option<usize>, i128)> {
    let (a_base, a_off) = range_bound_affine(func, a, fuel - 1)?;
    let (b_base, b_off) = range_bound_affine(func, b, fuel - 1)?;
    match op {
        BinOp::Add => {
            let base = match (a_base, b_base) {
                (None, None) => None,
                (Some(l), None) | (None, Some(l)) => Some(l),
                (Some(_), Some(_)) => return None, // base + base: not single-base affine
            };
            Some((base, a_off.checked_add(b_off)?))
        }
        BinOp::Sub => {
            if b_base.is_some() {
                return None; // x - base: would negate base coefficient
            }
            Some((a_base, a_off.checked_sub(b_off)?))
        }
        _ => None,
    }
}

/// Read an operand as a NON-NEGATIVE integer constant (a `usize` range bound),
/// returned as `u64`. `None` for any non-constant or negative value.
pub(super) fn const_usize_operand(op: &Operand) -> Option<u64> {
    match op {
        Operand::Constant(ConstValue::Uint(v, _)) => u64::try_from(*v).ok(),
        Operand::Constant(ConstValue::Int(v)) if *v >= 0 => u64::try_from(*v).ok(),
        _ => None,
    }
}

// Trust: recognize calls to the panic intrinsic family. Mirrors
// `trust_ir_bridge`'s `is_panic_call`; kept in sync so the VC generator and the
// TrustIr lowering agree on which calls are panic sites.
pub(super) fn is_panic_intrinsic_call(callee: &str) -> bool {
    callee.contains("::panicking::")
        || callee.contains("begin_panic")
        || callee.ends_with("::panic")
        || callee.ends_with("::panic_fmt")
        || callee.ends_with("::panic_nounwind")
        || callee.contains("panic_bounds_check")
        || callee.contains("panic_misaligned_pointer_dereference")
        || callee.contains("panic_cannot_unwind")
}

pub(super) fn collect_aggregate_field_sort_unsupported(
    func: &VerifiableFunction,
    context: String,
    span: &SourceSpan,
    place: &trust_types::Place,
    kind: &trust_types::AggregateKind,
    operands: &[Operand],
    vcs: &mut Vec<VerificationCondition>,
) {
    for (index, _) in operands.iter().enumerate() {
        let Some(field_place) = crate::aggregate_field_place(place, kind, index, operands.len())
        else {
            continue;
        };
        if crate::place_sort(func, &field_place).is_none() {
            vcs.push(unsupported_mir_vc(
                func,
                "TrustSymbolicAggregateFieldSortMissing".to_string(),
                format!(
                    "{context} {index}: field `{}` has missing aggregate/field sort metadata; schema-aware proof consumers require a concrete SMT sort declaration",
                    crate::place_to_var_name(func, &field_place)
                ),
                span.clone(),
            ));
        }
    }
}

pub(super) fn thread_local_ref_thin_address_ty(ty: &Ty) -> bool {
    let pointee = match ty {
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => inner.as_ref(),
        _ => return false,
    };

    // `SymArray` is sized in Rust and remains thin in the general pointer-layout
    // classifier. The native TrustIr bridge currently preserves its symbolic
    // length with the slice-fat-pointer representation, however, so this sealed
    // TLS lane must decline it until that representation converges.
    !matches!(
        pointee,
        Ty::Slice { .. }
            | Ty::Str
            | Ty::SymArray { .. }
            | Ty::Dynamic { .. }
            | Ty::Unsupported { .. }
    )
}

pub(super) fn collect_rvalue_unsupported(
    func: &VerifiableFunction,
    context: String,
    span: &SourceSpan,
    dest: &trust_types::Place,
    rvalue: &Rvalue,
    vcs: &mut Vec<VerificationCondition>,
) {
    match rvalue {
        Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, op) => {
            collect_operand_unsupported(func, context.clone(), span, op, vcs);
            // Trust: `PtrMetadata` over a slice/str/array fat pointer is just its
            // length, which `slice_len_formula` models as a deterministic symbolic
            // `len` (keyed on the operand place, so the same slice always yields the
            // same term) or a concrete array length. When that succeeds the value is
            // fully modeled — both the `s.len()` guard (guards.rs) and the `s[i]`
            // bounds check (rvalue_safety.rs) route through `slice_len_formula` — so
            // emitting a spurious UnsupportedMir obligation here wedged the ubiquitous
            // `if i < s.len() { s[i] }` bounds-checked-indexing idiom. Fail closed only
            // for genuinely unmodelable metadata: raw-pointer provenance, `dyn` vtable.
            if crate::slice_len_formula(func, op).is_none() {
                vcs.push(unsupported_mir_vc(
                    func,
                    "Rvalue::UnaryOp(PtrMetadata)".to_string(),
                    format!(
                        "{context}: pointer metadata extraction requires fat-pointer metadata/provenance semantics; symbolic slice lengths are diagnostic-only until the metadata lane is modeled"
                    ),
                    span.clone(),
                ));
            }
        }
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => {
            collect_operand_unsupported(func, context.clone(), span, op, vcs);
        }
        Rvalue::Cast(op, target_ty) => {
            collect_operand_unsupported(func, context.clone(), span, op, vcs);
            collect_type_unsupported(
                func,
                format!("{context} cast target type"),
                target_ty,
                span,
                vcs,
            );
            collect_cast_relation_unsupported(func, context, span, op, target_ty, vcs);
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            collect_operand_unsupported(func, format!("{context} lhs"), span, lhs, vcs);
            collect_operand_unsupported(func, format!("{context} rhs"), span, rhs, vcs);
        }
        Rvalue::Aggregate(kind, operands) => {
            if let Some((kind, detail)) = unsupported_aggregate_kind(func, kind, operands) {
                vcs.push(unsupported_mir_vc(
                    func,
                    kind,
                    format!("{context}: {detail}"),
                    span.clone(),
                ));
            }
            if let trust_types::AggregateKind::RawPtr { pointee_ty, .. } = kind {
                collect_type_unsupported(
                    func,
                    format!("{context} raw pointer aggregate pointee"),
                    pointee_ty,
                    span,
                    vcs,
                );
            }
            collect_operands_unsupported(func, context, span, operands, vcs);
        }
        Rvalue::Repeat(operand, _) => {
            collect_operand_unsupported(func, context, span, operand, vcs)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => {
            collect_place_type_unsupported(func, context, span, place, vcs);
        }
        Rvalue::Unsupported { kind, detail, operands } => {
            // rustc's `ThreadLocalRef` produces a thread-local address. Depending
            // on the referenced static it can be an immutable reference or a raw
            // pointer; Trust does not model the address's storage identity. The
            // direct VC lane therefore leaves the converter's exact,
            // operand-free marker unconstrained and adds no assumptions.
            // Reference validity is established separately by the
            // borrow-validity lane; raw-pointer dereferences remain fail-closed.
            // Seal the marker shape here so a forged marker with operands or a
            // scalar destination cannot suppress an `UnsupportedMir` obligation.
            let exact_tls_marker = kind == "Rvalue::ThreadLocalRef";
            let compiler_shaped_detail = detail
                .strip_prefix("thread-local reference to ")
                .is_some_and(|symbol| !symbol.is_empty());
            let thin_address_destination = crate::place_ty_cow(func, dest)
                .as_deref()
                .is_some_and(thread_local_ref_thin_address_ty);
            let modeled_tls_address = exact_tls_marker
                && compiler_shaped_detail
                && operands.is_empty()
                && thin_address_destination;
            if !modeled_tls_address {
                let unsupported_detail = if exact_tls_marker {
                    format!(
                        "{context}: malformed ThreadLocalRef marker; expected a compiler-shaped symbol, zero operands, and a thin reference/raw-pointer destination"
                    )
                } else {
                    format!("{context}: {detail}")
                };
                vcs.push(unsupported_mir_vc(func, kind.clone(), unsupported_detail, span.clone()));
            }
            collect_operands_unsupported(
                func,
                format!("{context} unsupported operands"),
                span,
                operands,
                vcs,
            );
        }
        // Trust: W2 inc-0 — `Rvalue::PtrOffset` is pointer arithmetic
        // (`ptr + count * size_of::<T>()`), UB when out-of-bounds. Its faithful
        // in-bounds obligation is the intrinsic lane's `ptr_offset_bounds_vc`
        // (`0 ≤ index ∧ index ≤ len`), which lives over the reflected
        // `(base slice, index)` `PtrModel` in `trust-clean`, NOT here. Until this
        // lane resolves the pointer to its slice-relative index, the direct VC
        // path fails CLOSED: emit an `UnsupportedMir`-class obligation so no
        // function containing an un-discharged offset can certify (never modeled
        // as a total/opaque pointer without the bounds obligation), and walk both
        // operands for their own unsupported sub-obligations.
        Rvalue::PtrOffset { ptr, count } => {
            vcs.push(unsupported_mir_vc(
                func,
                "Rvalue::PtrOffset".to_string(),
                format!(
                    "{context}: pointer offset arithmetic requires a slice-relative in-bounds obligation (0 <= index && index <= len); the (base slice, index) pointer model and its ptr_offset_bounds_vc are not yet resolved on the direct VC lane"
                ),
                span.clone(),
            ));
            collect_operand_unsupported(func, format!("{context} ptr"), span, ptr, vcs);
            collect_operand_unsupported(func, format!("{context} count"), span, count, vcs);
        }
        _ => {}
    }
}

pub(super) fn collect_cast_relation_unsupported(
    func: &VerifiableFunction,
    context: String,
    span: &SourceSpan,
    operand: &Operand,
    target_ty: &Ty,
    vcs: &mut Vec<VerificationCondition>,
) {
    let Some(source_ty) = crate::operand_ty(func, operand) else {
        vcs.push(unsupported_mir_vc(
            func,
            "Rvalue::Cast".to_string(),
            format!("{context}: unsupported cast: source operand type is unavailable"),
            span.clone(),
        ));
        return;
    };

    if matches!(&source_ty, Ty::Bool) && target_ty.is_integer() {
        return;
    }

    if crate::is_thin_pointer_identity_cast(&source_ty, target_ty)
        || crate::is_fn_pointer_identity_cast(&source_ty, target_ty)
        || crate::is_callable_reification_cast(&source_ty, target_ty)
        || crate::is_array_to_slice_ref_cast(&source_ty, target_ty)
        // An array→slice unsize whose source lost its `&[T;N]` type — a promoted
        // array constant (`let t: &[T] = &[a,b,c]`, lowered to OpaqueConst) or a
        // fat-pointer-element array. Metadata-only, no obligation; the slice length
        // stays opaque, so accepting it by target is sound (and stops it from
        // poisoning the function's other obligations into Unsupported).
        || crate::cast_target_is_slice_ref(target_ty)
        || (source_ty.is_integer() && target_ty.is_integer())
        // float `as` casts are infallible (no panic obligation); the dest is left
        // unconstrained (no value-fact), so this is sound and stops one float cast
        // from poisoning the whole function's obligations into Unsupported.
        || crate::is_float_numeric_cast(&source_ty, target_ty)
        // A pointer→integer cast (the `*const _ -> usize` address leg of the `vec!`/
        // box-machinery alignment & null checks; `convert.rs` already lowers it to
        // `Rvalue::Cast` and the bridge emits `CastOp::PtrToInt`). Exposing a pointer's
        // address yields an arbitrary integer: the dest is left UNCONSTRAINED (no
        // value-fact), so a derived null/alignment assert stays soundly caught and
        // nothing is falsely proved. Accepting it here stops this one cast from
        // poisoning the whole function's obligations (e.g. its arithmetic-overflow
        // safety VCs) into Unsupported.
        || (source_ty.is_pointer_like() && target_ty.is_integer())
    {
        return;
    }

    vcs.push(unsupported_mir_vc(
        func,
        "Rvalue::Cast".to_string(),
        format!(
            "{context}: unsupported cast {source_ty:?} -> {target_ty:?}: {}",
            crate::unsupported_cast_reason(&source_ty, target_ty)
        ),
        span.clone(),
    ));
}

pub(super) fn unsupported_aggregate_kind(
    func: &VerifiableFunction,
    kind: &trust_types::AggregateKind,
    operands: &[Operand],
) -> Option<(String, String)> {
    match kind {
        trust_types::AggregateKind::Adt { name, variant, active_field: Some(active_field), .. } => {
            Some((
                "AggregateKind::Adt(active_field)".to_string(),
                format!(
                    "union-like aggregate {name} variant {variant} active_field {active_field}"
                ),
            ))
        }
        trust_types::AggregateKind::Closure { name, captures, .. } => {
            closure_aggregate_support_error(func, name, captures, operands)
                .map(|detail| ("AggregateKind::Closure".to_string(), detail))
        }
        // Trust: piece #13 (safe-async data-safety) — the OUTER async fn body
        // builds the coroutine frame with `Rvalue::Aggregate(Coroutine)` to
        // return the `impl Future`. Model it as an obligation-free OPAQUE
        // aggregate build (like a closure whose captures matched): the frame is
        // `Ty::Coroutine` with no modeled fields, so constructing it carries no
        // safety obligation, and every later read of a frame field is havoc'd
        // (`project_ty_ref` returns `None` for `Ty::Coroutine`). This is what
        // lets the resume body verify — without it the aggregate build alone
        // would stamp an `UnsupportedMir`→Unknown obligation on the outer body.
        // `CoroutineClosure` (`async ||`) stays fail-closed — a later increment.
        trust_types::AggregateKind::Coroutine { .. } => None,
        trust_types::AggregateKind::CoroutineClosure { name } => Some((
            "AggregateKind::CoroutineClosure".to_string(),
            format!("coroutine-closure aggregate {name} requires async closure semantics"),
        )),
        trust_types::AggregateKind::RawPtr { pointee_ty, mutable } => {
            crate::raw_ptr_aggregate_support_error(func, pointee_ty, *mutable, operands)
                .map(|detail| ("AggregateKind::RawPtr".to_string(), detail))
        }
        trust_types::AggregateKind::Tuple
        | trust_types::AggregateKind::Array
        | trust_types::AggregateKind::Adt { active_field: None, .. } => None,
        _ => Some((
            "AggregateKind::<unknown>".to_string(),
            "non-exhaustive aggregate kind is not modeled".to_string(),
        )),
    }
}

pub(super) fn closure_aggregate_support_error(
    func: &VerifiableFunction,
    name: &str,
    captures: &[Ty],
    operands: &[Operand],
) -> Option<String> {
    if captures.len() != operands.len() {
        return Some(format!(
            "closure aggregate {name} capture count {} does not match operand count {}",
            captures.len(),
            operands.len()
        ));
    }

    for (index, (capture_ty, operand)) in captures.iter().zip(operands).enumerate() {
        let Some(operand_ty) = crate::operand_ty_cow(func, operand) else {
            continue;
        };
        if operand_ty.as_ref() != capture_ty {
            return Some(format!(
                "closure aggregate {name} capture {index} type {capture_ty:?} does not match operand type {:?}",
                operand_ty.as_ref()
            ));
        }
    }

    None
}

pub(super) fn collect_operands_unsupported(
    func: &VerifiableFunction,
    context: String,
    span: &SourceSpan,
    operands: &[Operand],
    vcs: &mut Vec<VerificationCondition>,
) {
    for (index, operand) in operands.iter().enumerate() {
        collect_operand_unsupported(func, format!("{context}[{index}]"), span, operand, vcs);
    }
}

pub(super) fn collect_operand_unsupported(
    func: &VerifiableFunction,
    context: String,
    span: &SourceSpan,
    operand: &Operand,
    vcs: &mut Vec<VerificationCondition>,
) {
    if let Operand::Unsupported { kind, detail } = operand {
        vcs.push(unsupported_mir_vc(
            func,
            kind.clone(),
            format!("{context}: {detail}"),
            span.clone(),
        ));
    }
    if let Operand::Symbolic(formula) = operand
        && let Err(rejection) = crate::symbolic_formula::consume_symbolic_formula(formula)
    {
        vcs.push(unsupported_mir_vc(
            func,
            rejection.unsupported_vc_kind().to_string(),
            rejection.diagnostic(&context),
            span.clone(),
        ));
    }
}
