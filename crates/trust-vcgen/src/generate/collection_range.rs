// Trust (2026-09-25, std-range-family): the std collection methods that PANIC on a
// caller-supplied index, range or count argument and that no call-site recognizer
// charged. Each built rc=0 on the default lane (stage-1 `6606d3bdf`) and panicked
// at runtime on an out-of-range argument:
//
//   Vec::splice(r, _)  Vec::extract_if(r, _)  Vec::insert_mut(i, _)
//   VecDeque::range(r)  VecDeque::range_mut(r)  VecDeque::swap(i, j)
//   VecDeque::insert_mut(i, _)  deque[i]  deque[i] = x
//   String::drain(r)  String::replace_range(r, _)  String::extend_from_within(r)
//   String::split_off(at)  String::truncate(n)  <[T]>::repeat(n)
//   s[..=b] / s[(Bound, Bound)] on a slice, `str` or `Vec`
//
// Their panics live INSIDE the library (`slice::range`, a char-boundary `assert!`,
// `checked_mul(..).expect("capacity overflow")`, `get(i).expect(..)`), where the
// native bundle reads them as std's own defined behaviour, and the call carries no
// caller-visible `Assert` — so without a call-site row the caller's argument was
// never charged. The rows here follow `SliceMethodPanic::RangeIndex`/`BTreeRange`:
//
//   * PRECISE where a stable length is available: a `VecDeque` receiver whose
//     length the body cannot change (`deque_receiver_len`) gets the exact
//     `slice::range` failure condition, so `if a <= b && b <= d.len()` PROVES;
//   * FAIL-HONEST otherwise — a RESIZING receiver (`Vec::splice` takes `&mut self`
//     and no length tie survives a resize, the argument `VecPanicMethod` records)
//     or an unmodeled condition (a `String` char boundary; a capacity product) is
//     an `UnsupportedMir` row: refused under the default policy, never verified;
//   * NOTHING for an argument that provably cannot panic (`..`, `0..`, `..0`,
//     `0..0`, index/`at`/`n` = `0`, `repeat(0)`/`repeat(1)`).
//
// IDENTITY. An inherent method is recognized by its leaf (`method_tail`, which is
// arrow-aware) under an owner prefix anchored at an AUTHENTICATED sysroot root
// (`path_root_is_authenticated_sysroot_crate`: a stamped impersonator crate and a
// qualified `<T as Trait>::m` user-trait spelling are both refused). The
// `VecDeque` index and swap rows additionally discriminate on the RECEIVER's type,
// as the existing variants do.

use super::*;

const VEC_OWNERS: &[&str] = &["alloc::vec::Vec", "std::vec::Vec"];
const VECDEQUE_OWNERS: &[&str] = &[
    "alloc::collections::vec_deque::VecDeque",
    "std::collections::vec_deque::VecDeque",
    "std::collections::VecDeque",
];
/// std's own `String` by its exact path: the owner a std `String` inherent method names,
/// and the self type that `guards::std_container_deref_self` and
/// `unwrap_panic::is_std_container_index_call` accept, so the wave-12 anchors and
/// [`is_std_string_adt_name`] read one list.
pub(crate) const STRING_OWNERS: &[&str] = &["alloc::string::String", "std::string::String"];
/// `Vec::extract_if` is `#[inline]`; at `-O` the caller's MIR calls its body's
/// constructor `ExtractIf::new(vec, pred, range)` instead, which runs the same
/// `slice::range(range, ..len)` check (measured on the `-O` dump).
const VEC_EXTRACT_IF_OWNERS: &[&str] = &["alloc::vec::extract_if::ExtractIf"];

/// Which std range-taking method a [`SliceMethodPanic::CollectionRange`] row
/// charges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RangeMethodOwner {
    /// `Vec::splice` / `Vec::extract_if`: `slice::range(r, ..len)` on a receiver
    /// the call itself RESIZES — fail-honest unless trivially in bounds.
    VecResize,
    /// `VecDeque::range` / `range_mut`: `slice::range(r, ..len)`, length-preserving
    /// — precise over a stable deque length.
    DequeView,
    /// `String::drain` / `replace_range` / `extend_from_within`: `slice::range` and
    /// then `assert!(is_char_boundary(start))`, `assert!(is_char_boundary(end))`.
    /// Char boundaries are not modeled — fail-honest unless every explicit
    /// endpoint is `0`.
    StringRange,
}

/// True iff `callee` starts with `<owner>::` for one of `owners` under an
/// authenticated sysroot crate root.
fn has_std_owner_prefix(callee: &str, owners: &[&str]) -> bool {
    owners.iter().any(|o| callee.strip_prefix(o).is_some_and(|rest| rest.starts_with("::")))
        && trust_types::path_root_is_authenticated_sysroot_crate(callee)
}

/// A std `VecDeque` inherent method whose leaf is one of `leaves`. Shared with the
/// length-tie and resize gates in `guards.rs`, so the recognizer that MINTS the
/// `_len == coll_len(base)` tie and the one that RECOVERS `coll_len(base)` for a
/// bound agree on what a `VecDeque` call is.
pub(crate) fn is_std_vecdeque_method(callee: &str, leaves: &[&str]) -> bool {
    has_std_owner_prefix(callee, VECDEQUE_OWNERS) && leaves.contains(&method_tail(callee))
}

/// `alloc::slice::<impl [T]>::…` — the primitive-slice inherent impl in `alloc`.
fn is_alloc_slice_inherent(callee: &str) -> bool {
    (callee.starts_with("alloc::slice::<impl [") || callee.starts_with("std::slice::<impl ["))
        && trust_types::path_root_is_authenticated_sysroot_crate(callee)
}

/// The inner text of the method's OWN generic arguments — the last top-level
/// `::<…>` group of the rendered callee. Arrow-aware (the `>` of `->` is not a
/// bracket), like `method_tail`. `None` when the callee has no trailing turbofish.
///
/// Trust (ARGS-FINGERPRINT-READ-1, 2026-10-07): the duplicate-crate-name argument
/// fingerprint `::<__trust_args@HEX>` is NOT the method's turbofish, though it is
/// spelled as one; it is removed first (`trust_types::strip_trailing_args_fingerprint`,
/// exact grammar only), so a VALUE read (`const_generic_is_nonzero`'s literal) sees
/// the real arguments. A TYPE-PATH read must also decline on a tagged callee — the
/// tag says an argument may name a same-named crate — which `range_generic_is_full`
/// does itself (round 2).
fn method_generic_args_inner(callee: &str) -> Option<&str> {
    let s = trust_types::strip_trailing_args_fingerprint(callee.trim_end());
    if !s.ends_with('>') {
        return None;
    }
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    let mut open = None;
    for i in (0..bytes.len()).rev() {
        match bytes[i] {
            b'>' if i > 0 && bytes[i - 1] == b'-' => {}
            b'>' => depth += 1,
            b'<' => {
                depth -= 1;
                if depth == 0 {
                    open = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let open = open?;
    if open < 2 || &s[open - 2..open] != "::" {
        return None;
    }
    Some(&s[open + 1..s.len() - 1])
}

/// The `pos`-th top-level generic argument of the method's trailing turbofish,
/// without allocating a `Vec<&str>`.
fn nth_method_generic_arg(callee: &str, pos: usize) -> Option<&str> {
    let inner = method_generic_args_inner(callee)?;
    let ib = inner.as_bytes();
    let (mut idx, mut depth, mut start) = (0usize, 0i32, 0usize);
    for i in 0..ib.len() {
        match ib[i] {
            b'>' if i > 0 && ib[i - 1] == b'-' => {}
            b'<' | b'(' | b'[' | b'{' => depth += 1,
            b'>' | b')' | b']' | b'}' => depth -= 1,
            b',' if depth == 0 => {
                if idx == pos {
                    return Some(inner[start..i].trim());
                }
                idx += 1;
                start = i + 1;
            }
            _ => {}
        }
    }
    (idx == pos).then(|| inner[start..].trim())
}

/// The single top-level generic argument of the method's trailing turbofish, or
/// `None` if there is no trailing turbofish or more than one top-level argument.
fn single_method_generic_arg(callee: &str) -> Option<&str> {
    let inner = method_generic_args_inner(callee)?;
    let ib = inner.as_bytes();
    let mut depth = 0i32;
    for i in 0..ib.len() {
        match ib[i] {
            b'>' if i > 0 && ib[i - 1] == b'-' => {}
            b'<' | b'(' | b'[' | b'{' => depth += 1,
            b'>' | b')' | b']' | b'}' => depth -= 1,
            b',' if depth == 0 => return None,
            _ => {}
        }
    }
    Some(inner.trim())
}

/// Is the method's range type parameter (generic position `pos`) exactly
/// `core::ops::range::RangeFull`? `..` is a zero-sized value, so MIR passes it as a
/// bare constant whose operand carries no type — the instantiation is the only
/// place its type is written. A user zero-sized `RangeBounds` type renders under
/// its own crate's name; the one crate that can spell this path is a crate NAMED
/// `core`, and the producer then tags the call (below).
///
/// Trust (ARGS-FINGERPRINT-READ-1 round 2, 2026-10-07): a callee carrying the
/// argument fingerprint ANYWHERE declines. The display printer does not stamp
/// crate identity inside generic arguments, and the producer writes the tag
/// exactly when some argument def lives in a crate whose name does not identify
/// it — so in that case `core::ops::range::RangeFull` may be a crate built
/// `--crate-name core` (MEASURED by the round-1 review: such a `RangeFull` with
/// `start_bound = Included(&1000)` read through a stripped tag lost the
/// `drain` refutation; the binary panics "range start index 1000 out of range").
/// The real `RangeFull` in a graph that duplicates some OTHER name is untagged.
fn range_generic_is_full(callee: &str, pos: usize) -> bool {
    !trust_types::args_display_may_name_a_same_named_crate(callee)
        && nth_method_generic_arg(callee, pos) == Some("core::ops::range::RangeFull")
}

/// `core::slice::<impl [T]>::…` — the primitive-slice inherent impl in `core`.
/// Also the identity gate of `as_chunks_len`'s result-length facts.
pub(super) fn is_core_slice_inherent(callee: &str) -> bool {
    (callee.starts_with("core::slice::<impl [") || callee.starts_with("std::slice::<impl ["))
        && trust_types::path_root_is_authenticated_sysroot_crate(callee)
}

/// The method's single const generic renders a NONZERO integer literal
/// (`as_chunks::<4>`). A `0`, a symbolic `N` (a generic body) or anything that does
/// not parse answers `false`, and the call is charged.
fn const_generic_is_nonzero(callee: &str) -> bool {
    const_generic_literal(callee).is_some_and(|v| v != 0)
}

/// The method's single const generic as the integer literal it renders
/// (`as_chunks::<4>` → `4`), or `None` for a symbolic `N` (a generic body), several
/// generic arguments, or anything that does not parse. The reader behind
/// [`const_generic_is_nonzero`] and `as_chunks_len`'s chunk size.
pub(super) fn const_generic_literal(callee: &str) -> Option<u128> {
    let n = single_method_generic_arg(callee)?;
    let digits = n.strip_suffix("_usize").unwrap_or(n);
    digits.parse::<u128>().ok()
}

impl SliceMethodPanic {
    pub(super) fn classify_collection_with_tail(callee: &str, tail: &str) -> Option<Self> {
        use RangeMethodOwner::*;
        match tail {
            // `Vec::splice::<R, I>`, `Vec::extract_if::<F, R>`.
            "splice" | "extract_if" if has_std_owner_prefix(callee, VEC_OWNERS) => {
                Some(SliceMethodPanic::CollectionRange {
                    range_idx: 1,
                    owner: VecResize,
                    range_is_full: range_generic_is_full(callee, usize::from(tail == "extract_if")),
                })
            }
            // `ExtractIf::<'_, T, F>::new::<R>(vec, pred, range)` — the inlined form
            // (`library/alloc/src/vec/extract_if.rs`); the range is arg 2.
            "new" if has_std_owner_prefix(callee, VEC_EXTRACT_IF_OWNERS) => {
                Some(SliceMethodPanic::CollectionRange {
                    range_idx: 2,
                    owner: VecResize,
                    range_is_full: range_generic_is_full(callee, 0),
                })
            }
            "range" | "range_mut" if has_std_owner_prefix(callee, VECDEQUE_OWNERS) => {
                Some(SliceMethodPanic::CollectionRange {
                    range_idx: 1,
                    owner: DequeView,
                    range_is_full: range_generic_is_full(callee, 0),
                })
            }
            "drain" | "replace_range" | "extend_from_within"
                if has_std_owner_prefix(callee, STRING_OWNERS) =>
            {
                Some(SliceMethodPanic::CollectionRange {
                    range_idx: 1,
                    owner: StringRange,
                    range_is_full: range_generic_is_full(callee, 0),
                })
            }
            "swap" if has_std_owner_prefix(callee, VECDEQUE_OWNERS) => {
                Some(SliceMethodPanic::DequeSwap { i_idx: 1, j_idx: 2 })
            }
            "insert_mut"
                if has_std_owner_prefix(callee, VEC_OWNERS)
                    || has_std_owner_prefix(callee, VECDEQUE_OWNERS) =>
            {
                Some(SliceMethodPanic::ResizingIndexArg { idx: 1 })
            }
            "split_off" | "truncate" if has_std_owner_prefix(callee, STRING_OWNERS) => {
                Some(SliceMethodPanic::CharBoundaryArg { idx: 1, truncate: tail == "truncate" })
            }
            "repeat" if is_alloc_slice_inherent(callee) => {
                Some(SliceMethodPanic::SliceRepeat { n_idx: 1 })
            }
            "as_chunks" | "as_chunks_mut" | "as_rchunks" | "as_rchunks_mut" | "array_windows"
                if is_core_slice_inherent(callee) =>
            {
                Some(SliceMethodPanic::ConstChunkSize { nonzero: const_generic_is_nonzero(callee) })
            }
            "into_flattened" if has_std_owner_prefix(callee, VEC_OWNERS) => {
                Some(SliceMethodPanic::VecIntoFlattened)
            }
            _ => None,
        }
    }
}

/// The recognizer half: the [`SliceMethodPanic`] a std collection call belongs to,
/// or `None`. Consulted FIRST by `slice_method_panic`, so a `VecDeque::swap` is
/// charged against the deque rather than falling to the slice `swap` arm (whose
/// body finds no slice length on a deque receiver and emits nothing).
pub(super) fn collection_method_panic(callee: &str) -> Option<SliceMethodPanic> {
    SliceMethodPanic::classify_collection_with_tail(callee, method_tail(callee))
}

// ---------------------------------------------------------------------------------
// The deque length.
// ---------------------------------------------------------------------------------

/// True iff `name` is std's `VecDeque` ADT (generic arguments ignored). An
/// impersonating crate's ADT carries the unauthenticated-crate stamp in front, so
/// the equality fails for it.
pub(crate) fn is_vecdeque_adt_name(name: &str) -> bool {
    let name = name.trim();
    if !(name.starts_with("alloc::") || name.starts_with("std::")) {
        return false;
    }
    let head = name.split('<').next().unwrap_or(name).trim_end();
    VECDEQUE_OWNERS.contains(&head)
}

/// Trust (OWNED-VEC-NAME-1, 2026-10-04): true iff `name` is std's `String` ADT by its
/// exact path (generic arguments ignored), the `String` twin of
/// [`is_vecdeque_adt_name`]. The extractor spells std's `String` `alloc::string::String`
/// (measured with `-Ztrust-dump`); a user type named `String` renders crate-qualified
/// (`mycrate::String`), and an impersonating crate's carries the unauthenticated-crate
/// stamp in front, so the equality fails for both.
pub(crate) fn is_std_string_adt_name(name: &str) -> bool {
    let name = name.trim();
    if !(name.starts_with("alloc::") || name.starts_with("std::")) {
        return false;
    }
    let head = name.split('<').next().unwrap_or(name).trim_end();
    STRING_OWNERS.contains(&head)
}

/// True iff `ty` is a `VecDeque` or a reference to one.
pub(crate) fn ty_is_vecdeque_or_ref(ty: &Ty) -> bool {
    let inner = match ty {
        Ty::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    matches!(inner, Ty::Adt { name, .. } if is_vecdeque_adt_name(name))
}

/// The length a `VecDeque` receiver has at a call, as far as it can be named.
pub(crate) enum DequeLen {
    /// The receiver is not a `VecDeque` (or a reference to one).
    NotDeque,
    /// It is a deque, but its length is not a stable, nameable quantity here: an
    /// ambiguous (conditionally merged) receiver, or a base the body may RESIZE
    /// (`push_back`, `clear`, an escaping `&mut`, …). The caller fails honest.
    Unrecovered,
    /// The deque's abstract length `coll_len(base)` — the SAME var every genuine
    /// `VecDeque::len()` call on that base is tied to
    /// (`guards::slice_last_some_nonempty_definitions`) and that a `!is_empty()`
    /// guard bounds (`guards::owned_container_len_var`).
    Len(Formula),
}

/// Recover the abstract length of a `VecDeque` receiver operand.
///
/// SOUNDNESS. `coll_len(base)` is ONE unversioned name per base for the whole body,
/// so it may only stand for the length where that length cannot change: the gate is
/// `guards::local_mut_borrows_may_resize` — every `&mut` borrow of the base must be
/// consumed as the receiver of a length-PRESERVING std call (`index_mut`, and the
/// `VecDeque` length-preserving `&mut self` methods admitted in that gate). It is the
/// SAME gate the tie site asks (`coll_base_len_stable`), so the two agree: either
/// both the `d.len()` result and the bound read `coll_len(base)`, or neither does.
/// A struct-FIELD deque under a shared `&self` root resolves to the canonical field
/// place (`guards::base_collection_place_unique`), whose stability that function
/// establishes by construction. Everything else is `Unrecovered`.
pub(crate) fn deque_receiver_len(func: &VerifiableFunction, receiver: &Operand) -> DequeLen {
    let (Operand::Copy(p) | Operand::Move(p)) = receiver else { return DequeLen::NotDeque };
    if p.projections.is_empty() {
        let Some(ty) = crate::local_ty_ref(func, p.local) else { return DequeLen::NotDeque };
        if !ty_is_vecdeque_or_ref(ty) {
            return DequeLen::NotDeque;
        }
    } else {
        let Some(ty) = crate::operand_ty_cow(func, receiver) else { return DequeLen::NotDeque };
        if !ty_is_vecdeque_or_ref(ty.as_ref()) {
            return DequeLen::NotDeque;
        }
        return DequeLen::Unrecovered;
    }
    if let Some(base_place) = crate::guards::base_collection_place_unique(func, p.local)
        && !base_place.projections.is_empty()
    {
        return match crate::place_ty_cow(func, &base_place).as_deref() {
            Some(t) if ty_is_vecdeque_or_ref(t) => {
                DequeLen::Len(crate::guards::coll_len_var_place(func, &base_place))
            }
            _ => DequeLen::Unrecovered,
        };
    }
    let Some(base) = crate::guards::base_collection_local_unique(func, p.local) else {
        return DequeLen::Unrecovered;
    };
    match crate::local_ty_ref(func, base) {
        Some(t) if ty_is_vecdeque_or_ref(t) => {}
        _ => return DequeLen::Unrecovered,
    }
    if crate::guards::local_mut_borrows_may_resize(func, base) {
        return DequeLen::Unrecovered;
    }
    DequeLen::Len(crate::guards::coll_len_var(func, base))
}

// ---------------------------------------------------------------------------------
// The range argument, normalized to its half-open bounds.
// ---------------------------------------------------------------------------------

/// A `RangeBounds<usize>` argument normalized the way `slice::range` reads it:
/// the half-open start (`None` = unbounded, i.e. `0`) and end (`None` = unbounded,
/// i.e. `len`). Each explicit bound is an operand plus whether `slice::range` adds
/// one to it (an `Excluded` start, an `Included` end — the `+ 1` overflowing at
/// `usize::MAX` is exactly std's "attempted to index slice up to maximum usize"
/// panic, and the unbounded-integer formula below reports it as `> len`).
pub(crate) struct NormRange<'a> {
    start: Option<(&'a Operand, bool)>,
    end: Option<(&'a Operand, bool)>,
}

impl NormRange<'_> {
    /// `..`, `0..`, `..0`, `0..0`: in bounds for every length.
    fn is_trivially_in_bounds(&self) -> bool {
        let zero = |b: &Option<(&Operand, bool)>| matches!(b, Some((op, false)) if super::const_int_value(op) == Some(0));
        match (&self.start, &self.end) {
            (None, None) => true,
            (s, None) => zero(s),
            (None, e) => zero(e),
            (s, e) => zero(s) && zero(e),
        }
    }
}

/// An unsigned-integer bound operand (the only payload `RangeBounds<usize>` has
/// for the aggregate shapes traced here; `Range<&usize>` also implements it and is
/// refused, because a reference's formula is not its value).
fn is_usize_bound(func: &VerifiableFunction, op: &Operand) -> bool {
    matches!(
        crate::operand_ty_cow(func, op).as_deref(),
        Some(Ty::Int { signed: false, .. } | Ty::PtrSizedInt { signed: false, .. })
    )
}

/// Normalize `op` (a `RangeBounds<usize>` argument) to a [`NormRange`], or `None`
/// when its bounds cannot be read off the MIR — a range handed in whole, a user
/// `RangeBounds` type, a reference payload, a local with more than one value (a
/// range held in a variable and mutated before use), a `RangeInclusive` whose
/// `exhausted` flag is not the constant `false`. Every caller fails closed on
/// `None`.
pub(crate) fn norm_usize_range<'a>(
    func: &'a VerifiableFunction,
    op: &'a Operand,
) -> Option<NormRange<'a>> {
    // The TYPE settles `..` first, so an untraceable `RangeFull` is not refused.
    if let Some(ty) = crate::operand_ty_cow(func, op)
        && let Ty::Adt { name, .. } = ty.as_ref()
        && range_family_adt_name(name) == Some("RangeFull")
    {
        return Some(NormRange { start: None, end: None });
    }
    let mut local = operand_local(op)?;
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, local) {
            return None;
        }
        let Some(rvalue) = crate::local_defs::unique_value_def(func, local) else {
            // `a..=b` spelled as the constructor call (optimized MIR at `-O`).
            if super::terminator_presence_for(func).has_bare_dest_call
                && let Some(LocalDef::Call { callee, args }) = local_def(func, local)
                && args.len() == 2
                && is_range_inclusive_new_call(callee)
            {
                let (s, e) = (&args[0], &args[1]);
                return (is_usize_bound(func, s) && is_usize_bound(func, e))
                    .then_some(NormRange { start: Some((s, false)), end: Some((e, true)) });
            }
            return None;
        };
        match rvalue {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) | Rvalue::Ref { place: p, .. }
                if p.projections.is_empty() =>
            {
                local = p.local;
            }
            Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops) => {
                let bound = |i: usize| ops.get(i).filter(|o| is_usize_bound(func, o));
                return match (range_family_adt_name(name), ops.len()) {
                    (Some("Range"), 2) => Some(NormRange {
                        start: Some((bound(0)?, false)),
                        end: Some((bound(1)?, false)),
                    }),
                    (Some("RangeTo"), 1) => {
                        Some(NormRange { start: None, end: Some((bound(0)?, false)) })
                    }
                    (Some("RangeFrom"), 1) => {
                        Some(NormRange { start: Some((bound(0)?, false)), end: None })
                    }
                    (Some("RangeToInclusive"), 1) => {
                        Some(NormRange { start: None, end: Some((bound(0)?, true)) })
                    }
                    (Some("RangeInclusive"), 3)
                        if matches!(ops[2], Operand::Constant(ConstValue::Bool(false))) =>
                    {
                        Some(NormRange {
                            start: Some((bound(0)?, false)),
                            end: Some((bound(1)?, true)),
                        })
                    }
                    (Some("RangeFull"), 0) => Some(NormRange { start: None, end: None }),
                    _ => None,
                };
            }
            Rvalue::Aggregate(AggregateKind::Tuple, ops) if ops.len() == 2 => {
                // `(Bound, Bound)`: `Included(x) = 0`, `Excluded(x) = 1`,
                // `Unbounded = 2`. Start: Included(x) -> x, Excluded(x) -> x + 1.
                // End: Included(x) -> x + 1, Excluded(x) -> x.
                let side = |op: &'a Operand, start: bool| -> Option<Option<(&'a Operand, bool)>> {
                    let l = operand_local(op)?;
                    if crate::local_defs::is_parameter(func, l) {
                        return None;
                    }
                    match crate::local_defs::unique_value_def(func, l)? {
                        Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, payload)
                            if name.split('<').next().is_some_and(|h| {
                                matches!(h, "core::ops::range::Bound" | "std::ops::Bound")
                            }) =>
                        {
                            match (*variant, payload.first()) {
                                (2, _) => Some(None),
                                (0, Some(x)) if is_usize_bound(func, x) => Some(Some((x, !start))),
                                (1, Some(x)) if is_usize_bound(func, x) => Some(Some((x, start))),
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                };
                return Some(NormRange { start: side(&ops[0], true)?, end: side(&ops[1], false)? });
            }
            _ => return None,
        }
    }
    None
}

/// The `slice::range(r, ..len)` failure condition for a normalized range: the
/// half-open start exceeds the end, or the end exceeds `len`. `Some(Bool(false))`
/// for a range with no explicit bound; `None` when a bound does not resolve
/// (`resolve_bound`), which every caller turns into a fail-closed row.
///
/// Trust: 2026-10-14 — `resolve_bound` is the CALLER's resolution of a bound at the
/// call the range is passed to (`panic_calls::range_bound_at_call_formula`, through
/// the slice lane's `resolve_bound` or [`collection_method_panic_body`]). This body
/// asked `resolve_range_bound_formula`, whose joined-copy fallback names a copy temp
/// of a multiply-written local by its own bare name: a variable the call's row meets
/// only where the copy's definition reaches it. The slice lane does not conjoin its
/// own call block's definitions, where `_10 = copy k` sits, and `if k >= 8 { return }
/// b[..=k]` was refuted at `_10 = 8`; a `VecDeque::range` in a loop body ahead of a
/// write of the bound was refuted on a free copy too
/// (`tests/range_bound_joined_copy_realmir.rs`).
///
/// Arithmetic is over unbounded integers, so an `Excluded(usize::MAX)` start or an
/// `Included(usize::MAX)` end — std's overflow panics — become `usize::MAX + 1`,
/// which exceeds any length and is reported.
pub(crate) fn norm_range_violation(
    range: &NormRange<'_>,
    len: &Formula,
    resolve_bound: &dyn Fn(&Operand) -> Option<Formula>,
) -> Option<Formula> {
    let resolve = |b: &(&Operand, bool)| -> Option<Formula> {
        let x = resolve_bound(b.0)?;
        Some(if b.1 { Formula::Add(Box::new(x), Box::new(Formula::Int(1))) } else { x })
    };
    let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));
    Some(match (&range.start, &range.end) {
        (None, None) => Formula::Bool(false),
        (Some(s), None) => gt(resolve(s)?, len.clone()),
        (None, Some(e)) => gt(resolve(e)?, len.clone()),
        (Some(s), Some(e)) => {
            let e = resolve(e)?;
            Formula::Or(vec![gt(resolve(s)?, e.clone()), gt(e, len.clone())])
        }
    })
}

/// The `RangeIndex` lane's fallback for a slice/`str` index whose range the
/// original `Range`/`RangeTo`/`RangeFrom` tracer does not read — `a..=b`, `..=b`,
/// `(Bound, Bound)` — over the receiver's modeled length, each bound read by the
/// lane's own `resolve_bound`. `None` = fail closed.
pub(crate) fn index_range_violation(
    func: &VerifiableFunction,
    range: &Operand,
    len: &Formula,
    resolve_bound: &dyn Fn(&Operand) -> Option<Formula>,
) -> Option<Formula> {
    norm_range_violation(&norm_usize_range(func, range)?, len, resolve_bound)
}

/// Trust (cap vec-drain, 2026-10-03): a call to std's own `Vec::drain` /
/// `VecDeque::drain` whose range argument provably cannot panic — `..`, `0..`,
/// `..0`, `0..0`, the same [`NormRange::is_trivially_in_bounds`] shapes the
/// `CollectionRange` rows already mint nothing for.
///
/// WHY. Both drains check their argument exactly once, on entry:
/// `slice::range(range, ..self.len())` (`library/alloc/src/vec/mod.rs`,
/// `library/alloc/src/collections/vec_deque/mod.rs`), which panics only when the
/// half-open start exceeds the end or the end exceeds `len`. With start `0` and end
/// `len` (or `0`) neither can hold for any length, so the
/// `Call::drain::panic-freedom-unverified` row the unmodeled fallback
/// (`is_bounds_panicking_slice_mutator`, `is_caller_value_panicking_deque_method`)
/// mints for the call has nothing to refute: the semantics already discharge it.
/// MEASURED on stage 1 `5424ce87e`: `q.drain(..).collect()` (clean's
/// `DeclDepGraph::topological_batches`) failed L0 on exactly that row.
///
/// SCOPE. Only the range bounds check is in question here; the element reads,
/// the `Drain` iterator, the element drops and the call's other rows are charged
/// as before. Every other range shape keeps the fallback's fail-closed refutation
/// row: a drain RESIZES its receiver, so a guard's length tie does not survive it
/// (the `VecResize` argument), and precise modeling is not attempted.
///
/// IDENTITY. The owner is anchored at an authenticated sysroot root
/// (`is_std_inherent_method`), so a user `drain` — or a stamped impersonator
/// crate's `Vec` — keeps the fallback's row.
pub(crate) fn std_vec_drain_range_cannot_panic(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> bool {
    let [_receiver, range] = args else { return false };
    if method_tail(callee) != "drain"
        || !(has_std_owner_prefix(callee, VEC_OWNERS)
            || has_std_owner_prefix(callee, VECDEQUE_OWNERS))
    {
        return false;
    }
    // `..` passes as a bare zero-sized constant whose type lives only in the
    // instantiation (see `range_generic_is_full`).
    if range_generic_is_full(callee, 0) && matches!(range, Operand::Constant(_)) {
        return true;
    }
    norm_usize_range(func, range).is_some_and(|n| n.is_trivially_in_bounds())
}

// ---------------------------------------------------------------------------------
// The bodies.
// ---------------------------------------------------------------------------------

fn unmodeled(kind: &str, detail: &str) -> Option<(Formula, VcKind)> {
    Some((
        super::unsupported::unsupported_mir_fail_closed_formula(),
        VcKind::UnsupportedMir { kind: kind.into(), detail: detail.into() },
    ))
}

/// The deque bound `len >= 0 ∧ violation`: a deque's length is never negative, and
/// saying so keeps a model with a negative abstract length from refuting a
/// `..0`-shaped bound.
fn with_nonneg_len(len: &Formula, violation: Formula) -> Formula {
    Formula::And(vec![Formula::Ge(Box::new(len.clone()), Box::new(Formula::Int(0))), violation])
}

const DEQUE_LEN_UNRECOVERED: &str = "the deque's length is not a stable quantity at this call \
     (the body may resize it — `push_back`, `clear`, an escaping `&mut` — or the receiver is \
     conditionally merged), so the argument's bound cannot be established — refused, never \
     silently verified";

/// Build the failure body for the `collection_range` variants of
/// [`SliceMethodPanic`]. `None` = the argument provably cannot panic.
pub(super) fn collection_method_panic_body(
    func: &VerifiableFunction,
    panic: &SliceMethodPanic,
    args: &[Operand],
    // Trust: 2026-10-14 — the block whose `Call` terminator this is: a range bound is
    // named at THIS call (`panic_calls::range_bound_at_call_formula`).
    call_block: &trust_types::BasicBlock,
) -> Option<(Formula, VcKind)> {
    let receiver = args.first()?;
    match panic {
        SliceMethodPanic::CollectionRange { range_idx, owner, range_is_full } => {
            let range = args.get(*range_idx)?;
            // `..`: a zero-sized constant operand whose instantiated type is
            // `RangeFull` (see `range_generic_is_full`). Never panics.
            if *range_is_full && matches!(range, Operand::Constant(_)) {
                return None;
            }
            let norm = norm_usize_range(func, range);
            if norm.as_ref().is_some_and(NormRange::is_trivially_in_bounds) {
                return None;
            }
            match owner {
                RangeMethodOwner::DequeView => {
                    let len = match deque_receiver_len(func, receiver) {
                        DequeLen::Len(len) => len,
                        _ => {
                            return unmodeled(
                                "vecdeque-range-bounds-unmodeled",
                                &format!(
                                    "VecDeque::range/range_mut panics when the range start \
                                     exceeds its end or the end exceeds the length; \
                                     {DEQUE_LEN_UNRECOVERED}"
                                ),
                            );
                        }
                    };
                    let resolve_bound = |op: &Operand| {
                        super::panic_calls::range_bound_at_call_formula(func, range, op, call_block)
                    };
                    match norm.and_then(|n| norm_range_violation(&n, &len, &resolve_bound)) {
                        Some(v) => Some((with_nonneg_len(&len, v), VcKind::SliceBoundsCheck)),
                        None => unmodeled(
                            "vecdeque-range-bounds-unmodeled",
                            "VecDeque::range/range_mut panics when the range start exceeds \
                             its end or the end exceeds the length; the bounds of this range \
                             argument are not values this verifier can read (a range passed \
                             in whole, a user `RangeBounds`, a range reassigned before use) — \
                             refused, never silently verified",
                        ),
                    }
                }
                RangeMethodOwner::VecResize => unmodeled(
                    "vec-range-method-bounds-unmodeled",
                    "Vec::splice/extract_if panics when the range start exceeds its end or \
                     the end exceeds the length; the call RESIZES the Vec, and a length tie \
                     does not survive a resize this verifier does not track, so the bound \
                     is not established — refused unless the range is `..`, `0..` or `..0`",
                ),
                RangeMethodOwner::StringRange => unmodeled(
                    "string-range-char-boundary-unmodeled",
                    "String::drain/replace_range/extend_from_within panics when the range \
                     is out of order or out of bounds, or when either end is not a char \
                     boundary; char boundaries are not modeled — refused unless every \
                     explicit endpoint is `0` (`..`, `0..`, `..0`)",
                ),
            }
        }
        SliceMethodPanic::ResizingIndexArg { idx } => {
            if super::const_int_value(args.get(*idx)?) == Some(0) {
                return None;
            }
            unmodeled(
                "container-insert-mut-index-unmodeled",
                "Vec/VecDeque::insert_mut panics when the index exceeds the length; the \
                 call RESIZES the container, so no stable length discharges the index — \
                 refused, never silently verified (the same fail-honest row as \
                 Vec::insert)",
            )
        }
        SliceMethodPanic::CharBoundaryArg { idx, truncate } => {
            if super::const_int_value(args.get(*idx)?) == Some(0) {
                return None;
            }
            unmodeled(
                "string-char-boundary-unmodeled",
                if *truncate {
                    "String::truncate panics when the new length is within the string and \
                     not a char boundary; char boundaries are not modeled — refused unless \
                     the length is `0`"
                } else {
                    "String::split_off panics when `at` exceeds the length or is not a char \
                     boundary; char boundaries are not modeled — refused unless `at` is `0`"
                },
            )
        }
        SliceMethodPanic::SliceRepeat { n_idx } => {
            if matches!(super::const_int_value(args.get(*n_idx)?), Some(0 | 1)) {
                return None;
            }
            unmodeled(
                "slice-repeat-capacity-overflow",
                "<[T]>::repeat computes its result capacity (len * n) inside the library \
                 and panics (\"capacity overflow\") when it overflows; not statically \
                 modeled — refused, never silently verified (the sibling of \
                 str-repeat-capacity-overflow)",
            )
        }
        SliceMethodPanic::ConstChunkSize { nonzero } => {
            if *nonzero {
                return None;
            }
            unmodeled(
                "slice-const-chunk-size-zero",
                "<[T]>::as_chunks/as_rchunks/array_windows::<N> panics when the chunk size N \
                 is zero; this instantiation's N is not a nonzero literal — refused, never \
                 silently verified",
            )
        }
        SliceMethodPanic::VecIntoFlattened => {
            // `Vec<[T; N]>` is `Seq { elem: Array { elem: T, len: N } }`. `len * N`
            // overflows only for a zero-sized `T` (a sized `T` is bounded by the
            // allocation) and only when `N > 1`.
            if let Some(ty) = crate::operand_ty_cow(func, receiver)
                && let Ty::Seq { elem, .. } = ty.as_ref()
                && let Ty::Array { elem: inner, len } = elem.as_ref()
                && (*len <= 1 || trust_types::alloc_model::ty_is_definitely_nonzero_sized(inner))
            {
                return None;
            }
            unmodeled(
                "vec-into-flattened-len-overflow",
                "Vec<[T; N]>::into_flattened panics (\"vec len overflow\") when T is \
                 zero-sized and len * N overflows; the element is not provably sized here — \
                 refused, never silently verified",
            )
        }
        SliceMethodPanic::DequeSwap { i_idx, j_idx } => {
            let (i, j) = (args.get(*i_idx)?, args.get(*j_idx)?);
            match deque_receiver_len(func, receiver) {
                DequeLen::Len(len) => {
                    let i_f = crate::operand_to_formula(func, i);
                    let j_f = crate::operand_to_formula(func, j);
                    let violation = Formula::Or(vec![
                        Formula::Ge(Box::new(i_f), Box::new(len.clone())),
                        Formula::Ge(Box::new(j_f), Box::new(len.clone())),
                    ]);
                    Some((with_nonneg_len(&len, violation), VcKind::SliceBoundsCheck))
                }
                _ => unmodeled(
                    "vecdeque-index-unmodeled",
                    &format!(
                        "VecDeque::swap panics when either index is not below the length; \
                         {DEQUE_LEN_UNRECOVERED}"
                    ),
                ),
            }
        }
        _ => None,
    }
}

/// The `RangeIndex` lane's `VecDeque` arm: `<VecDeque<T> as Index<usize>>::index(&d,
/// i)` / `IndexMut::index_mut` panics ("Out of bounds access") when `i >= len`.
/// `None` when the call is not a scalar index into a `VecDeque`.
pub(crate) fn deque_scalar_index_body(
    func: &VerifiableFunction,
    args: &[Operand],
) -> Option<(Formula, VcKind)> {
    let [receiver, index] = args else { return None };
    let (Operand::Copy(rp) | Operand::Move(rp)) = receiver else { return None };
    if rp.projections.is_empty()
        && !crate::local_ty_ref(func, rp.local).is_some_and(ty_is_vecdeque_or_ref)
    {
        return None;
    }
    if !operand_is_scalar_usize_index(func, index) {
        return None;
    }
    match deque_receiver_len(func, receiver) {
        DequeLen::NotDeque => None,
        DequeLen::Len(len) => {
            let i = crate::operand_to_formula(func, index);
            Some((
                with_nonneg_len(&len, Formula::Ge(Box::new(i), Box::new(len.clone()))),
                VcKind::SliceBoundsCheck,
            ))
        }
        DequeLen::Unrecovered => unmodeled(
            "vecdeque-index-unmodeled",
            &format!(
                "indexing a VecDeque panics (\"Out of bounds access\") when the index is \
                 not below the length; {DEQUE_LEN_UNRECOVERED}"
            ),
        ),
    }
}
