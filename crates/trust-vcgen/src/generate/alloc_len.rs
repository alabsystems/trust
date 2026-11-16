// W4 ALLOC-LEN (2026-09-25): a direct-size allocation whose element count IS the
// length of a live sequence — `Vec::with_capacity(s.len())`,
// `String::with_capacity(a.len() + b.len())`, `vec![0; s.len()]` — is not an
// unbounded allocation.
//
// TWO QUESTIONS, and the lane keeps them apart because only one is a panic.
//
//  1. AVAILABILITY (the #nia-oom element/byte ceiling). Not a panic and not UB:
//     a policy that no allocation's size be an opaque input. A len-derived
//     count leaves the ceiling ONLY when the allocation is at most the bytes the
//     counted sequences already occupy: every term `l_i` has a KNOWN source
//     stride `S_i >= 1` with `S_i >= T` (the target stride), so
//     `T * Σ l_i <= Σ S_i * l_i` — the counted memory, once per term (at most
//     twice what is held when both terms name one sequence). Then the OOM
//     obligation, if any, lives at the source allocation — the argument the
//     `collect` sibling rests on (`collect_source_is_bounded_std_collection`),
//     made exact. Every other len-derived count keeps the availability
//     disjuncts exactly as an opaque count does.
//
//     The first statement of this premise — "a count that is the length of an
//     existing allocation is bounded by memory the program already holds, so
//     the allocation is at most a constant factor of that one" — was REFUTED by
//     adversarial round 1 (2026-09-25), twice, each a measured abort from a
//     build that verified:
//       * a ZERO-SIZED source holds no memory: `Vec::<u8>::with_capacity(
//         z.len())` over `&[()]` under `z.len() < 2^60` asked for 2^55 bytes
//         (probe a02);
//       * a WIDER target makes the "constant factor" `T / S` unbounded:
//         `Vec::<[u8; 1 << 14]>::with_capacity(s.len())` over bytes under
//         `s.len() < 2^40` asked for 2^50 bytes of a 64 GiB source (a11), and
//         `[u8; 1 << 30]` 2^50 bytes of 1 MiB (a01).
//     The `collect` sibling shared the ZST half of that refutation (the
//     HASHMAP battery's `fa_zst_src_vec_control`); main's F3 (`0fba79c888`)
//     closed it there with `producer_leaf_count_is_memory_bounded` — a
//     sequence source must have a definitely non-zero-sized element.
//
//     WHAT THE SKIP BOUNDS, and what it does not (adversarial round 2, probe
//     n02, 2026-09-29): it bounds the OUTER buffer only — `n * T` bytes for
//     the `n` element slots. `vec![x; n]` (`from_elem`) also CLONES `x` n-1
//     times, and for a heap-owning element (`String`, `Vec<_>`, `Box<_>`)
//     each clone allocates `x`'s own payload again, so `vec![big_string;
//     s.len()]` can ask for `n * big_string.len()` bytes that no counted
//     sequence holds. Clone amplification is unmodeled on main as well: base
//     `296873da69` accepts the GUARDED twin (n02b, `if s.len() < 1024 {
//     vec![x; s.len()] }` with `x: String`), because a guarded count passes
//     the #nia-oom ceiling and nothing charges the clones. Disclosed, not
//     closed here (`docs/TCB.md`, "Live-length capacity").
//
//  2. CAPACITY OVERFLOW (`count * size_of::<T>() > isize::MAX` panics with
//     "capacity overflow" inside `RawVec`). A real panic, never dropped. It is
//     either PROVED here structurally or kept as the obligation's only disjunct:
//
//       * a live `&[T]`/`&str`/`&String`/`&Vec<T>` of a NON-zero-sized element
//         with stride `S` has `len * S <= isize::MAX` — Rust's slice/allocation
//         size invariant; `String`/`Vec` add `len <= capacity` and RawVec's own
//         `capacity * S <= isize::MAX`;
//       * so for a target stride `T` and ONE source term,
//         `T * len <= S * len <= isize::MAX` whenever `T <= S`; for TWO terms,
//         `T * (l1 + l2) <= T * (M/S1 + M/S2) <= M` whenever
//         `T * (S1 + S2) <= S1 * S2`.
//
//     When availability is bounded (half 1) but this theorem is not, the row
//     keeps ONLY the capacity-overflow disjunct; when availability is not
//     bounded, the row is the ordinary one (element ceiling plus capacity term). In
//     particular the SUM of two same-stride lengths is availability-bounded
//     but does NOT pass this theorem (`T = S1 = S2` gives `2T^2 > T^2`):
//     `String::with_capacity(a.len() + b.len())` over two `&str`s can ask for
//     up to `2 * isize::MAX - 2` bytes in the type model — two live allocations
//     each within `isize::MAX` can together exceed it — so its capacity
//     overflow is reachable there and the row stays refused, now with a
//     counterexample at the real `isize::MAX` boundary instead of the 256 MiB
//     availability witness (`tests/ordinary-rust-sweep` t23; its README calls
//     the old witness "a diagnostic gap, not a verdict gap"). That 256 MiB
//     byte budget no longer exists anywhere (deleted with trust-ir's
//     `ALLOC_BYTE_BUDGET`; see `generate/mod.rs`).
//
// WHAT COUNTS AS A LENGTH, and every gate is a refusal on a miss:
//  * `PtrMetadata(r)` with `r: &[T]` / `&mut [T]` / `&str` — a REFERENCE. A raw
//    slice pointer's metadata is excluded: `ptr::slice_from_raw_parts(p,
//    usize::MAX)` is safe to build and bounds nothing.
//  * a call whose callee KEY is `str::len`, `<[T]>::len`, `String::len` or
//    `Vec::len` in the compiler's own sysroot (DefId-minted, never a rendered
//    path), on a receiver whose type authenticates
//    (`producer_receiver_value_is_authenticated_sysroot`, or the extractor's
//    `Ty::Seq`, which only `is_std_vec`'s DefId check mints).
//  * each hop's local is the UNIQUE value of its definition
//    (`local_defs::unique_value_def` / `unique_value_call`): a parameter, a
//    second write, a `&mut` alias or a projected store refuses.
//  * the source stride is a LOWER bound (`element_stride_lower_bound`): exact
//    for a primitive, the sum of the fields for a tuple, `N` times the element
//    for an array; for an extractor-minted ADT rustc's recorded layout size, else
//    the field sum of a struct, the largest field of a union, the largest variant
//    payload of an enum (ALLOC-STRIDE-ADT-1); at every node, the larger of that
//    and the COMPILER's element-size table row (ALLOC-STRIDE-ADT-2: rustc's
//    `layout_of` over every preimage of the key, min-merged, poisoned by any it
//    could not size; on `VcgenContext` only, never on the function, so absent on
//    every decoded function and every non-compiler caller — KNOWN_HAZARDS-style
//    residual: a key minted OUTSIDE the extractor's recorded lowering exits that
//    equals a recorded key would read that key's row — the first 2026-10-07 audit
//    MISSED one, Lever A's field compaction, whose erased-name marker collides
//    with a same-named cut point of another crate or another instantiation; its
//    call sites now record the preimage (`elem_sizes::record_compacted`), see
//    DECISION_QUEUE ALLOC-STRIDE-ADT-2);
//    a leaf it cannot size (a pointer,
//    a generic, a by-name datatype, a hand-built ADT) contributes 0, and a bound
//    of 0 — every ZST among them — leaves
//    the stride unknown, which keeps BOTH rows (a ZST slice's length is NOT
//    bounded by `isize::MAX`, and it holds no memory). Both theorems are
//    monotone in the stride once it reaches `T`, so a lower bound is enough.
//  * the target stride is the extractor's `tcx.layout_of` token on a
//    DefId-keyed `Vec` constructor, or `1` for `String::with_capacity` (a
//    `String` IS a `Vec<u8>`). `reserve`/`reserve_exact` are NOT admitted: their
//    count is the ADDITIONAL capacity, and `len + additional` — which this row
//    does not model — is what overflows. `resize`/`resize_with` are NOT admitted
//    either, for a subtler reason: they grow through `RawVec::grow_amortized`,
//    which asks for `max(2 * capacity, new_len)`, so an existing capacity above
//    `isize::MAX / 2` bytes panics "capacity overflow" even when
//    `new_len * size_of::<T>()` fits (`library/alloc/src/raw_vec/mod.rs`,
//    `grow_amortized`). Only the FRESH exact-capacity constructors — whose
//    `RawVec::try_allocate_in(n)` lays out exactly `n` elements — are
//    total-count.

use super::*;

/// A direct-size allocation whose count is a sum of live-sequence lengths.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LenDerivedAllocation {
    /// `size_of::<T>()` of the allocated element, exact.
    pub(crate) target_stride: i128,
    /// `true` when `target_stride * count <= isize::MAX` is a theorem.
    pub(crate) capacity_safe: bool,
    /// `true` when the allocation is at most the bytes the counted sequences
    /// occupy: every term's source stride is known, non-zero and at least
    /// `target_stride`. The ONLY case that leaves the availability ceiling
    /// (module banner, half 1). `capacity_safe` implies it.
    pub(crate) availability_bounded: bool,
    /// The TARGET's `isize::MAX`, from the width the extractor gave the count's
    /// own `usize` — the capacity-overflow threshold the kept row compares
    /// against. Never the 64-bit constant: on a 32-bit target that threshold
    /// would be unreachable and the kept row vacuous.
    pub(crate) isize_max: i128,
}

/// A LOWER bound on `size_of` of an element type, as a stride: `Some(s)` with
/// `s >= 1`, or `None` when the bound this lane can establish is `0` (every
/// zero-sized type, and every type it cannot size — a pointer, a generic, a
/// by-name datatype, an ADT the extractor did not mint).
///
/// Exact for a primitive. A tuple is at least the sum of its fields (fields never
/// overlap; padding only adds) and an array exactly `N` times its element, so the
/// recursion is a lower bound whenever its leaves are; an unsized-here leaf
/// contributes `0`, which is always a lower bound. Both theorems that read a
/// stride are MONOTONE in it once it is at least the target stride — `T <= S` for
/// one term; `T * (S1 + S2) <= S1 * S2` for two, whose `S1 * S2 - T * (S1 + S2)`
/// grows with each `S_i >= T` — so a lower bound that satisfies one proves it for
/// the true stride. (Adversarial round 1, probe a09: a `&[(u8, u8)]` source was
/// refused because only primitive elements were sized.)
///
/// ALLOC-STRIDE-ADT-1 (2026-10-07): an extractor-minted `Ty::Adt` is sized too
/// (see `adt_bound` below for the per-kind argument). Its exact `layout` is
/// filled on the faithful lane only; the verifier lane — where every
/// `Vec::with_capacity` row is decided — falls back to the field-level bound,
/// which is never above it and is near 0 for a pointer-heavy element: a `Vec`
/// field is `Ty::Seq`, a `String` is a `Vec`, an `Arc`/`Box`/`&` reduces to a
/// pointer, a recursive type is a by-name `Ty::Datatype`, and each sizes 0. So
/// this helps only a source whose recorded fields hold enough primitive or
/// array bytes. It does NOT discharge clean-ck0's six
/// `Vec::with_capacity(src.len())` rows (sources `CtorInfo`, `BlockCtorInfo`,
/// `InductiveDecl`, `Occurrence`, `(Name, Term)`: field-level bounds 0..17
/// against targets 24..72); those need rustc's element size on the verifier
/// lane — see below.
///
/// ALLOC-STRIDE-ADT-2 (2026-10-07): that carrier is the COMPILER's element-size
/// table on the function's `VcgenContext` (`crate::ElemSizeTable`, read through
/// [`crate::compiler_elem_size_lower_bound`]): rustc's `layout_of` size of every
/// preimage the extractor lowered to a key, merged by minimum, poisoned by any
/// preimage it could not size. At EVERY node of the recursion the answer is
/// `max(structural, table)` — both are lower bounds of `size_of`, so their maximum
/// is one too. The table is consulted only for the four key shapes a source
/// element can have here (an extractor-minted `Ty::Adt`, a `Ty::Tuple`, a
/// `Ty::Array`, a `Ty::Datatype`) and only reaches this function through
/// `len_derived_allocation`, i.e. a sysroot `Vec::with_capacity`/
/// `with_capacity_in`/`from_elem` whose count is a live length. Absent (a decoded
/// or hand-built function, any caller that is not the compiler's TrustVerify
/// site, another instance of the def path, a generic/unsized/ZST element): the
/// structural bound alone, exactly as before.
fn element_stride_lower_bound(func: &VerifiableFunction, ty: &Ty) -> Option<i128> {
    fn table(func: &VerifiableFunction, ty: &Ty) -> i128 {
        let consulted = match ty {
            Ty::Adt { adt_kind, .. } => adt_kind.is_some(),
            Ty::Tuple(_) | Ty::Array { .. } | Ty::Datatype { .. } => true,
            _ => false,
        };
        if !consulted {
            return 0;
        }
        crate::compiler_elem_size_lower_bound(func, ty).map_or(0, i128::from)
    }
    fn bound(func: &VerifiableFunction, ty: &Ty, fuel: u32) -> i128 {
        let Some(fuel) = fuel.checked_sub(1) else { return 0 };
        structural(func, ty, fuel).max(table(func, ty))
    }
    fn structural(func: &VerifiableFunction, ty: &Ty, fuel: u32) -> i128 {
        match ty {
            Ty::Bool => 1,
            Ty::Char => 4,
            Ty::Int { width, .. } | Ty::Float { width } if *width >= 8 && width % 8 == 0 => {
                i128::from(*width / 8)
            }
            // An overflowing sum or product is not a real type's size (every
            // Rust type is at most `isize::MAX` bytes); answer the always-true 0.
            Ty::Tuple(fields) => fields
                .iter()
                .try_fold(0i128, |acc, field| acc.checked_add(bound(func, field, fuel)))
                .unwrap_or(0),
            Ty::Array { elem, len } => {
                i128::from(*len).checked_mul(bound(func, elem, fuel)).unwrap_or(0)
            }
            Ty::Adt { fields, variants, layout, adt_kind, .. } => {
                adt_bound(func, fields, variants, layout.as_deref(), *adt_kind, fuel)
            }
            _ => 0,
        }
    }
    // ALLOC-STRIDE-ADT-1 (2026-10-07). A user ADT is sized only when the
    // EXTRACTOR minted it from a rustc `AdtDef` (`adt_kind: Some`); a hand-built
    // or decoded pre-W19 `Ty::Adt` (`None`) may carry a synthetic field list, so
    // it contributes 0. Each arm is a lower bound of `size_of`:
    //  * rustc's own `layout_of` size, when the extractor recorded it — exact;
    //  * a STRUCT: the sum of its fields. Its fields occupy disjoint bytes
    //    (padding only adds; `repr(packed)` removes padding, never overlap);
    //  * a UNION: the largest field. Union fields overlap at offset 0, so a sum
    //    would over-ask; the union is at least as large as each field;
    //  * an ENUM: the largest per-variant field sum. Every variant's fields are
    //    laid out disjointly inside the enum (the tag or niche is extra or
    //    shares a field's invalid bit patterns, never shrinks a field), and a
    //    variant rustc omits from the layout has only 1-ZST fields, whose sum is
    //    0 anyway. The flattened `fields` view (`__tag` + every variant's
    //    `__v{v}_…`) is NOT read: it sums ALL variants. A zero-variant enum is 0.
    // A leaf the recursion cannot size (a generic, a pointer, a compacted or
    // by-name datatype, an unsupported type) contributes 0, so a truncated or
    // compacted field list only lowers the bound.
    fn adt_bound(
        func: &VerifiableFunction,
        fields: &[(String, Ty)],
        variants: &[trust_types::VariantDef],
        layout: Option<&trust_types::AdtLayoutInfo>,
        kind: Option<trust_types::AdtKind>,
        fuel: u32,
    ) -> i128 {
        use trust_types::AdtKind as K;
        let Some(kind) = kind else { return 0 };
        if let Some(layout) = layout {
            return i128::from(layout.size);
        }
        let sum = |fields: &[(String, Ty)]| {
            fields
                .iter()
                .try_fold(0i128, |acc, (_, field)| acc.checked_add(bound(func, field, fuel)))
                .unwrap_or(0)
        };
        match kind {
            K::Struct if variants.is_empty() => sum(fields),
            K::Union if variants.is_empty() => {
                fields.iter().map(|(_, field)| bound(func, field, fuel)).max().unwrap_or(0)
            }
            K::Enum => variants.iter().map(|v| sum(&v.fields)).max().unwrap_or(0),
            _ => 0,
        }
    }
    Some(bound(func, ty, 8)).filter(|&stride| stride >= 1)
}

/// The element stride of the sequence a `&[T]`/`&str` fat reference points at:
/// `Some(Some(s))` a known stride, `Some(None)` a genuine slice reference whose
/// element stride is unknown, `None` not a slice reference at all.
fn slice_ref_stride(func: &VerifiableFunction, ty: &Ty) -> Option<Option<i128>> {
    let Ty::Ref { inner, .. } = ty else { return None };
    match inner.as_ref() {
        Ty::Slice { elem } => Some(element_stride_lower_bound(func, elem)),
        Ty::Str => Some(Some(1)),
        _ => None,
    }
}

/// The source-stride list of a count operand that is a sum of at most two
/// live-sequence lengths; `None` when it is not one.
fn len_terms(func: &VerifiableFunction, op: &Operand, fuel: u32) -> Option<Vec<Option<i128>>> {
    use trust_types::SysrootItem as S;
    let fuel = fuel.checked_sub(1)?;
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if let Some(rvalue) = crate::local_defs::unique_value_def(func, p.local) {
        return match rvalue {
            Rvalue::Use(inner @ (Operand::Copy(q) | Operand::Move(q)))
                if q.projections.is_empty() =>
            {
                len_terms(func, inner, fuel)
            }
            Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, r) => {
                let ty = crate::operand_ty_cow(func, r)?;
                slice_ref_stride(func, ty.as_ref()).map(|s| vec![s])
            }
            // `(a + b).0` of an overflow-checked add, or a wrapping add (whose
            // value is at most `a + b` either way).
            Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
                if q.projections.as_slice() == [trust_types::Projection::Field(0)] =>
            {
                let Rvalue::CheckedBinaryOp(BinOp::Add, a, b) =
                    crate::local_defs::unique_value_def(func, q.local)?
                else {
                    return None;
                };
                sum_terms(func, a, b, fuel)
            }
            Rvalue::BinaryOp(BinOp::Add, a, b) => sum_terms(func, a, b, fuel),
            _ => None,
        };
    }
    let Terminator::Call { callee_key: Some(key), args, .. } =
        crate::local_defs::unique_value_call(func, p.local)?
    else {
        return None;
    };
    if !key.krate_is_real_sysroot || args.len() != 1 {
        return None;
    }
    let recv_ty = crate::operand_ty_cow(func, &args[0])?;
    let pointee = match recv_ty.as_ref() {
        Ty::Ref { inner, .. } => inner.as_ref(),
        _ => return None,
    };
    let stride = match key.sysroot_item? {
        S::StrLen | S::SliceLen => {
            if !producer_receiver_value_is_authenticated_sysroot(func, args) {
                return None;
            }
            match pointee {
                Ty::Slice { elem } => element_stride_lower_bound(func, elem),
                Ty::Str => Some(1),
                _ => return None,
            }
        }
        S::StringLen => {
            if !producer_receiver_value_is_authenticated_sysroot(func, args)
                || !matches!(pointee, Ty::Adt { .. })
            {
                return None;
            }
            Some(1)
        }
        S::VecLen => match pointee {
            Ty::Seq { elem, .. } => element_stride_lower_bound(func, elem),
            _ => return None,
        },
        _ => return None,
    };
    Some(vec![stride])
}

fn sum_terms(
    func: &VerifiableFunction,
    a: &Operand,
    b: &Operand,
    fuel: u32,
) -> Option<Vec<Option<i128>>> {
    let mut terms = len_terms(func, a, fuel)?;
    terms.extend(len_terms(func, b, fuel)?);
    (terms.len() <= 2).then_some(terms)
}

/// `T * Σ_j Π_{i≠j} S_i <= Π S_i` — the capacity theorem of the module banner,
/// for one or two terms with every stride known and nonzero.
fn capacity_theorem_holds(target_stride: i128, strides: &[Option<i128>]) -> bool {
    if target_stride < 1 {
        return false;
    }
    match strides {
        [Some(s)] if *s >= 1 => target_stride <= *s,
        [Some(s1), Some(s2)] if *s1 >= 1 && *s2 >= 1 => s1
            .checked_add(*s2)
            .and_then(|sum| target_stride.checked_mul(sum))
            .zip(s1.checked_mul(*s2))
            .is_some_and(|(lhs, rhs)| lhs <= rhs),
        _ => false,
    }
}

/// `T <= S_i` for every term with every stride known and nonzero: the
/// allocation `T * Σ l_i` is at most `Σ S_i * l_i`, the bytes the counted
/// sequences occupy — the availability half of the module banner.
fn availability_theorem_holds(target_stride: i128, strides: &[Option<i128>]) -> bool {
    target_stride >= 1
        && !strides.is_empty()
        && strides.iter().all(|s| s.is_some_and(|s| s >= 1 && target_stride <= s))
}

/// Classify a direct-size allocation's count. `None` — the obligation is
/// unchanged — unless the callee is a DefId-keyed total-count constructor and
/// the count is a sum of at most two live-sequence lengths.
pub(crate) fn len_derived_allocation(
    func: &VerifiableFunction,
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
    size_op: &Operand,
) -> Option<LenDerivedAllocation> {
    use trust_types::SysrootItem as S;
    let key = callee_key?;
    if !key.krate_is_real_sysroot {
        return None;
    }
    let target_stride = match key.sysroot_item? {
        // Fresh exact-capacity constructors: the count IS the whole capacity
        // (`try_allocate_in(n)`), with no existing buffer to double.
        S::VecWithCapacity | S::VecWithCapacityIn | S::VecFromElem => {
            parse_elem_bytes_token(callee).filter(|&s| s >= 1)?
        }
        S::StringWithCapacity => 1,
        _ => return None,
    };
    let isize_max = match crate::operand_ty_cow(func, size_op)?.as_ref() {
        Ty::Int { width: width @ (32 | 64), signed: false } => (1i128 << (width - 1)) - 1,
        _ => return None,
    };
    let terms = len_terms(func, size_op, 16)?;
    Some(LenDerivedAllocation {
        target_stride,
        capacity_safe: capacity_theorem_holds(target_stride, &terms),
        availability_bounded: availability_theorem_holds(target_stride, &terms),
        isize_max,
    })
}

#[cfg(test)]
mod tests {
    use trust_types::Ty;

    use super::{availability_theorem_holds, capacity_theorem_holds};

    /// The structural bound alone: a function with no compiler element-size
    /// table (no context is active in a unit test), as every caller that is not
    /// the compiler's TrustVerify site sees it.
    fn element_stride_lower_bound(ty: &Ty) -> Option<i128> {
        let func = trust_types::VerifiableFunction {
            name: "t".into(),
            def_path: "test::t".into(),
            span: Default::default(),
            body: trust_types::VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        super::element_stride_lower_bound(&func, ty)
    }

    #[test]
    fn availability_needs_every_source_at_least_as_wide_as_the_target() {
        // Adversarial round 1: a02 (ZST source, stride unknown), a11/a01 (a
        // 2^14 / 2^30 target over bytes) — each kept the capacity row, lost the
        // availability ceiling, and aborted on a 2^50-byte request.
        assert!(!availability_theorem_holds(1, &[None]));
        assert!(!availability_theorem_holds(1 << 14, &[Some(1)]));
        assert!(!availability_theorem_holds(8, &[Some(1)]));
        assert!(!availability_theorem_holds(1, &[Some(0)]));
        assert!(!availability_theorem_holds(1, &[]));
        assert!(availability_theorem_holds(1, &[Some(1)]));
        // t23: availability-bounded, NOT capacity-safe — the capacity row alone.
        assert!(availability_theorem_holds(1, &[Some(1), Some(1)]));
        assert!(!capacity_theorem_holds(1, &[Some(1), Some(1)]));
        assert!(!availability_theorem_holds(2, &[Some(2), Some(1)]));
    }

    #[test]
    fn the_capacity_theorem_implies_availability() {
        // `alloc_vcs` skips the row outright on `capacity_safe`; that is sound
        // only because it also bounds availability. Exhaustive over small strides.
        let strides: Vec<Option<i128>> = std::iter::once(None).chain((0..=9).map(Some)).collect();
        for t in 0..=9 {
            for &a in &strides {
                assert!(
                    !capacity_theorem_holds(t, &[a]) || availability_theorem_holds(t, &[a]),
                    "one term t={t} s={a:?}"
                );
                for &b in &strides {
                    assert!(
                        !capacity_theorem_holds(t, &[a, b])
                            || availability_theorem_holds(t, &[a, b]),
                        "two terms t={t} s1={a:?} s2={b:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn stride_lower_bounds_size_tuples_and_arrays_and_no_opaque_leaf() {
        let u8_ = Ty::Int { width: 8, signed: false };
        let u32_ = Ty::Int { width: 32, signed: false };
        assert_eq!(element_stride_lower_bound(&u8_), Some(1));
        // a09: `(u8, u8)`.
        assert_eq!(element_stride_lower_bound(&Ty::Tuple(vec![u8_.clone(), u8_.clone()])), Some(2));
        // `(u8, u32)` is 8 bytes with padding; 5 is a lower bound.
        assert_eq!(
            element_stride_lower_bound(&Ty::Tuple(vec![u8_.clone(), u32_.clone()])),
            Some(5)
        );
        let arr = Ty::Array { elem: Box::new(Ty::Int { width: 16, signed: false }), len: 4 };
        assert_eq!(element_stride_lower_bound(&arr), Some(8));
        // Zero-sized: `()`, `((), ())`, `[u8; 0]` — the stride stays unknown.
        assert_eq!(element_stride_lower_bound(&Ty::Tuple(vec![])), None);
        assert_eq!(
            element_stride_lower_bound(&Ty::Tuple(vec![Ty::Tuple(vec![]), Ty::Tuple(vec![])])),
            None
        );
        assert_eq!(
            element_stride_lower_bound(&Ty::Array { elem: Box::new(u8_.clone()), len: 0 }),
            None
        );
        // A leaf this lane cannot size contributes 0, never a guess.
        let opaque = Ty::Ref { mutable: false, inner: Box::new(u8_.clone()) };
        assert_eq!(element_stride_lower_bound(&opaque), None);
        assert_eq!(element_stride_lower_bound(&Ty::Tuple(vec![opaque, u8_])), Some(1));
    }

    fn extracted_adt(
        kind: trust_types::AdtKind,
        fields: Vec<(&str, Ty)>,
        variants: Vec<trust_types::VariantDef>,
    ) -> Ty {
        Ty::Adt {
            name: "user::T".into(),
            fields: fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect::<Vec<_>>().into(),
            variants: variants.into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            arbitrary_precision: None,
            validity_wrapper: None,
            layout: None,
            enum_layout: None,
            adt_kind: Some(kind),
        }
    }

    fn variant(name: &str, fields: Vec<Ty>) -> trust_types::VariantDef {
        trust_types::VariantDef {
            name: name.into(),
            discriminant: 0,
            fields: fields.into_iter().enumerate().map(|(i, t)| (i.to_string(), t)).collect(),
        }
    }

    fn generic() -> Ty {
        Ty::Unsupported { kind: "TyKind::Param".into(), detail: "T".into() }
    }

    /// ALLOC-STRIDE-ADT-1 (2026-10-07): a user struct/enum/union source is sized
    /// by a LOWER bound of its layout, never above it. Before, every ADT
    /// element sized 0.
    #[test]
    fn stride_lower_bounds_size_extracted_adts_from_below() {
        use trust_types::AdtKind as K;
        let u8_ = Ty::Int { width: 8, signed: false };
        let u64_ = Ty::Int { width: 64, signed: false };
        let arr10 = Ty::Array { elem: Box::new(u64_.clone()), len: 10 };
        // `struct Plain { a: [u64; 10] }` — a struct with an array field: 80.
        let plain = extracted_adt(K::Struct, vec![("a", arr10.clone())], vec![]);
        assert_eq!(element_stride_lower_bound(&plain), Some(80));
        // Field sum, padding ignored: `struct { a: u8, b: u64 }` is 16; 9 bounds it.
        let padded =
            extracted_adt(K::Struct, vec![("a", u8_.clone()), ("b", u64_.clone())], vec![]);
        assert_eq!(element_stride_lower_bound(&padded), Some(9));
        // Nested: `struct Outer { p: Plain, x: u8 }` — 81.
        let outer =
            extracted_adt(K::Struct, vec![("p", plain.clone()), ("x", u8_.clone())], vec![]);
        assert_eq!(element_stride_lower_bound(&outer), Some(81));
        // A generic / unsized-here field contributes 0, never a guess.
        let with_generic =
            extracted_adt(K::Struct, vec![("t", generic()), ("x", u64_.clone())], vec![]);
        assert_eq!(element_stride_lower_bound(&with_generic), Some(8));
        // rustc's own size when the extractor recorded it — exact.
        let mut with_layout = plain.clone();
        if let Ty::Adt { layout, .. } = &mut with_layout {
            *layout = Some(Box::new(trust_types::AdtLayoutInfo {
                size: 104,
                align: 8,
                field_offsets: vec![0],
                repr: "rust".into(),
            }));
        }
        assert_eq!(element_stride_lower_bound(&with_layout), Some(104));
        // A union is its LARGEST field (fields overlap), never their sum.
        let union_ =
            extracted_adt(K::Union, vec![("a", u64_.clone()), ("b", arr10.clone())], vec![]);
        assert_eq!(element_stride_lower_bound(&union_), Some(80));
        // An enum is its largest VARIANT payload, read from `variants`; the
        // flattened view (`__tag` + every variant's fields) would sum them all.
        let enum_ = extracted_adt(
            K::Enum,
            vec![
                ("__tag", Ty::Int { width: 64, signed: true }),
                ("__v0_0", arr10.clone()),
                ("__v1_0", u8_.clone()),
                ("__v1_1", u8_.clone()),
            ],
            vec![
                variant("A", vec![arr10.clone()]),
                variant("B", vec![u8_.clone(), u8_.clone()]),
                variant("C", vec![]),
            ],
        );
        assert_eq!(element_stride_lower_bound(&enum_), Some(80));
        // `Option<T>`-shaped over a generic: `None` sizes 0 and `Some(T)` sizes 0.
        let generic_enum = extracted_adt(
            K::Enum,
            vec![],
            vec![variant("None", vec![]), variant("Some", vec![generic()])],
        );
        assert_eq!(element_stride_lower_bound(&generic_enum), None);
        // A fieldless enum is sized 0 here (its tag is not counted): stays unknown.
        let fieldless =
            extracted_adt(K::Enum, vec![], vec![variant("A", vec![]), variant("B", vec![])]);
        assert_eq!(element_stride_lower_bound(&fieldless), None);
        // Zero-variant enum and zero-sized structs: unknown.
        assert_eq!(element_stride_lower_bound(&extracted_adt(K::Enum, vec![], vec![])), None);
        assert_eq!(element_stride_lower_bound(&extracted_adt(K::Struct, vec![], vec![])), None);
        let zst = extracted_adt(
            K::Struct,
            vec![("u", Ty::Unit), ("e", Ty::Array { elem: Box::new(u64_.clone()), len: 0 })],
            vec![],
        );
        assert_eq!(element_stride_lower_bound(&zst), None);
        // A struct of only a generic: unknown.
        let generic_struct = extracted_adt(K::Struct, vec![("t", generic())], vec![]);
        assert_eq!(element_stride_lower_bound(&generic_struct), None);
        // A hand-built `Ty::Adt` the extractor did not mint (`adt_kind: None`)
        // may carry a synthetic field list: 0.
        let synthetic = Ty::adt("user::T", vec![("a".into(), arr10.clone())]);
        assert_eq!(element_stride_lower_bound(&synthetic), None);
        // Malformed: a struct carrying variants, a union carrying variants.
        let odd = extracted_adt(K::Struct, vec![("a", arr10.clone())], vec![variant("A", vec![])]);
        assert_eq!(element_stride_lower_bound(&odd), None);
    }

    /// clean-ck0's element types, spelled the way the VERIFIER lane lowers them
    /// (`layout: None`; `Vec<T>` is `Ty::Seq`; `String` wraps a `Vec<u8>`;
    /// `Arc<T>` reduces to a raw pointer; a recursive `Term` is a by-name
    /// `Ty::Datatype`). Their field-level bounds are far below the real sizes
    /// (measured with `-Ztrust-verify=off`: Term 24, CtorInfo 88), so the
    /// field-level rule does NOT size them and their rows stay refused
    /// (ALLOC-STRIDE-ADT-2 is the missing carrier).
    #[test]
    fn stride_lower_bounds_of_pointer_heavy_elements_stay_near_zero_on_the_verifier_lane() {
        use trust_types::AdtKind as K;
        let u8_ = Ty::Int { width: 8, signed: false };
        let u32_ = Ty::Int { width: 32, signed: false };
        let term = Ty::Datatype { name: "clean_ck0::Term".into(), variants: vec![] };
        let seq = |elem: Ty| Ty::Seq { elem: Box::new(elem), drop_auth: None };
        let arc = |pointee: Ty| {
            extracted_adt(
                K::Struct,
                vec![("ptr", Ty::RawPtr { mutable: false, pointee: Box::new(pointee) })],
                vec![],
            )
        };
        let string = extracted_adt(K::Struct, vec![("vec", seq(u8_))], vec![]);
        assert_eq!(element_stride_lower_bound(&seq(u32_.clone())), None);
        assert_eq!(element_stride_lower_bound(&string), None);
        assert_eq!(element_stride_lower_bound(&arc(u32_.clone())), None);
        // `Name(NameRepr { Anonymous, Node(Arc<..>) })`.
        let name_repr = extracted_adt(
            K::Enum,
            vec![],
            vec![variant("Anonymous", vec![]), variant("Node", vec![arc(term.clone())])],
        );
        let name = extracted_adt(K::Struct, vec![("0", name_repr)], vec![]);
        assert_eq!(element_stride_lower_bound(&name), None);
        // `CtorInfo`-shaped: a name, a `u32`, a `Vec<Term>`, a `String` — only
        // the `u32` is counted: 4, against the 24-byte `Term` target of
        // recursor_build.rs:106.
        let ctor_info = extracted_adt(
            K::Struct,
            vec![("name", name.clone()), ("n", u32_), ("args", seq(term.clone())), ("s", string)],
            vec![],
        );
        assert_eq!(element_stride_lower_bound(&ctor_info), Some(4));
        assert!(!availability_theorem_holds(24, &[element_stride_lower_bound(&ctor_info)]));
        // nested.rs:417's `(Name, Term)`: unknown.
        assert_eq!(element_stride_lower_bound(&Ty::Tuple(vec![name, term])), None);
        // On the FAITHFUL lane the same type carries rustc's size, which would
        // decide it — the carrier the verifier lane lacks.
        let mut faithful = ctor_info;
        if let Ty::Adt { layout, .. } = &mut faithful {
            *layout = Some(Box::new(trust_types::AdtLayoutInfo {
                size: 88,
                align: 8,
                field_offsets: vec![0, 80, 8, 32],
                repr: "rust".into(),
            }));
        }
        assert!(capacity_theorem_holds(24, &[element_stride_lower_bound(&faithful)]));
    }

    #[test]
    fn one_term_needs_target_stride_at_most_source_stride() {
        assert!(capacity_theorem_holds(1, &[Some(1)]));
        assert!(capacity_theorem_holds(2, &[Some(2)]));
        assert!(capacity_theorem_holds(1, &[Some(4)]));
        assert!(!capacity_theorem_holds(8, &[Some(1)]));
        assert!(!capacity_theorem_holds(1, &[None]));
        assert!(!capacity_theorem_holds(1, &[Some(0)]));
    }

    #[test]
    fn two_same_stride_terms_never_pass() {
        // `String::with_capacity(a.len() + b.len())` — t23.
        assert!(!capacity_theorem_holds(1, &[Some(1), Some(1)]));
        assert!(!capacity_theorem_holds(4, &[Some(4), Some(4)]));
        // Halving the target stride is exactly enough.
        assert!(capacity_theorem_holds(1, &[Some(2), Some(2)]));
        assert!(!capacity_theorem_holds(1, &[Some(2), Some(1)]));
        assert!(!capacity_theorem_holds(1, &[Some(2), None]));
    }
}
