// trust-types/alloc_model: allocation-identity/offset model for pointer values
//
// DESIGN OF RECORD for §5 step 3 of
// docs/design/2026-08-19-verified-sysroot-scoping.md ("A pointer-provenance
// model for core's slice/str internals"). The design lives HERE, as this
// module's documentation, rather than as a docs/design addendum: every
// consumer of the model must import this module to spell its symbols, so the
// spelling and the design cannot drift apart.
//
// ── The model ──────────────────────────────────────────────────────────────
//
// A pointer value is semantically a pair (allocation identity, byte offset):
//
//     p  =  (A, o)     with  0 <= o <= size(A)
//
// and its ADDRESS is the sum  addr(p) = base(A) + o,  where `base` and `size`
// are per-allocation constants the program cannot forge. Today's verifier
// pipeline COLLAPSES this pair: `Sort::from_ty` maps `Ty::Ref`/`Ty::RawPtr`
// to `Sort::Int`, i.e. the model value of a pointer-typed place IS the single
// mathematical integer `base(A) + o`, with no way to name `A`, `o`, or
// `size(A)` separately. That collapse is why:
//
//   * `is_modeled_identity_cast` (trust-vcgen/src/lib.rs) could accept only
//     thin pointer-to-pointer identity — no other pointer fact was statable;
//   * `ptr::add`'s in-bounds precondition (`o + count*size_of::<T>() <=
//     size(A)`, no address wrap) could not be STATED, only refused;
//   * the fat-pointer refusal ("changes or depends on fat-pointer
//     metadata/provenance") had no model to defer to.
//
// The model enters at the VALUE/FORMULA level, NOT as a new `Ty` variant and
// NOT as a new `Sort`:
//
//   * a new `Ty` variant would perturb every fail-closed `match` and the
//     bincode variant indices (`Ty::BignumNat` is "deliberately placed LAST"
//     for exactly this reason) for zero semantic gain — the TYPE of a pointer
//     is not what was missing, the VALUE vocabulary was;
//   * a new SMT sort would force every existing pointer-carrying formula and
//     every solver frontend to re-sort; the existing `Sort::Int` address
//     reading stays VALID under the pair model (it is `base(A) + o`), so
//     compatibility with the existing Int/BV sorts is free if we keep it;
//   * value-level symbols (this module) are additive: an allocation's
//     identity, base and size become ordinary `Sort::Int` constants with
//     RESERVED NAMES, exactly the `__trust_constparam_{i}_{n}` /
//     `<s>__slice_len` precedent. A consumer that never mints them loses
//     nothing; a consumer that does can state `0 <= o <= size(A)`.
//
// Symbol identity is keyed on an `AllocId` minted per allocation SITE by the
// lane that owns the function body (allocation identity is per-function-
// analysis, like block-def versioning — it is NOT serialized into `Ty` and
// carries no cross-function meaning). Distinct ids MUST render distinct
// symbols: an id collision would let two different allocations share a
// base/size constant, which is the "M==N collision" false-proof channel
// `const_param_symbol` documents. The falsifying test below goes red on any
// such collision.
//
// ── First slice (implemented) ──────────────────────────────────────────────
//
// The provenance-EXPOSE direction. Under the collapsed representation the
// model value of a thin pointer IS its address, so the cast
//
//     thin pointer  ->  pinned-width unsigned address word (u64/usize)
//
// (`p.addr()`'s `*const () -> usize` transmute, `p as usize`) is VALUE-
// PRESERVING: `dest == source` is a theorem of the model, not an assumption.
// `is_thin_pointer_address_expose_cast` (trust-vcgen) admits exactly this
// shape into `is_modeled_identity_cast`, guarded by
// [`ptr_expose_target_is_address_word`] on the target side and the audited
// `is_thin_pointer_ty` classifier on the source side. Everything else stays
// refused, fail-closed:
//
//   * the RECOVER direction (integer -> pointer) manufactures provenance the
//     integer does not carry — never identity, never modeled here;
//   * a NARROWING target (`*const T as u32`) or a SIGNED target (`as i64`)
//     changes the mathematical value — refused;
//   * a FAT pointer's model value is not a single address — refused.
//
// This is what makes `*mut T::add::precondition_check`'s obligations
// STATABLE: `this.addr()` now denotes the pointer's own model value, so the
// body's overflow checks become real arithmetic over that value instead of
// arithmetic over a fresh unconstrained integer.
//
// ── Second slice (implemented) ─────────────────────────────────────────────
//
// The PROVABLE half for allocation ROOTS. When the expose cast's source
// pointer provably denotes `(A, 0)` — `&x`/`&raw x` of a whole local whose
// sort has a statically known byte size ([`known_alloc_byte_size`]) —
// the minted address carries the model's two axioms
// ([`alloc_root_address_bounds`]):
//
//     A1: 1 <= addr                       (allocations never contain null)
//     A2: addr <= usize::MAX - size(A)    (one-past-end is representable)
//
// which is the address-arithmetic image of [`same_alloc_in_bounds`]
// `(0, size, size)`. Consumer: `trust_vcgen::guards::
// alloc_model_expose_root_bounds` (root chase through unique whole-local
// defs and thin-identity casts, fail-closed everywhere else). This makes the
// `*mut T::add::precondition_check` overflow legs PROVABLE on covered
// shapes — one-past-end proves, one element further refutes, an unrooted
// pointer mints nothing, and no fact ever relates two distinct roots.
//
// ── Remaining slices (NOT implemented; recorded so the map is honest) ──────
//
//   1. ENGINEERING — mint `alloc_base_symbol`/`alloc_size_symbol` facts for
//      DERIVED pointers (nonzero offset: `&x.f`, `&a[i..]`, `Box`/`Vec`
//      allocations, slice borrows of symbolic length) and the pair-view fact
//      `addr(p) == base(A) + o`, widening [`same_alloc_in_bounds`]
//      provability past offset-0 roots.
//   2. ENGINEERING — spell `ptr::add`/`offset`'s precondition with
//      [`same_alloc_in_bounds`] at `BinOp::Offset` sites.
//   3. RESEARCH — `ptr_offset_from_unsigned` (slice `len!`) needs the
//      same-allocation PREMISE as an obligation-bearing axiom, not a model
//      fact; that is the first place two DIFFERENT `AllocId`s meet in one
//      formula.
//   4. RESEARCH — the fat-pointer data/metadata pair (slice len, vtable)
//      as a second value lane; the `trust_verify.rs` 28-loop-fixture
//      regression comment is the specification for why this must not be
//      bundled naively.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::formula::Formula;
use crate::model::Ty;

/// Identity of one allocation within one function-local analysis. Minted by
/// the lane that owns the body (per allocation SITE); NEVER serialized into
/// `Ty` and carrying no cross-function meaning. Two distinct ids denote two
/// (possibly) distinct allocations — their base/size symbols must never
/// alias.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AllocId(pub u64);

/// The reserved `Sort::Int` symbol naming `base(A)` — the address of
/// allocation `A`'s first byte. Reserved prefix: `__trust_alloc_base_`.
#[must_use]
pub fn alloc_base_symbol(id: AllocId) -> String {
    format!("__trust_alloc_base_{}", id.0)
}

/// The reserved `Sort::Int` symbol naming `size(A)` — allocation `A`'s size
/// in bytes. Reserved prefix: `__trust_alloc_size_`.
#[must_use]
pub fn alloc_size_symbol(id: AllocId) -> String {
    format!("__trust_alloc_size_{}", id.0)
}

/// Target-side guard of the provenance-EXPOSE cast: is `ty` the pinned
/// 64-bit target's unsigned address word (`usize`/`u64`, spelled
/// `Ty::Int { width: 64, signed: false }` on the verifier lane)?
///
/// Deliberately EXCLUDED, fail-closed:
///   * any narrower unsigned integer (`u32`, …) — truncates the address,
///     value-changing;
///   * any signed integer (`i64`, `isize`) — reinterprets addresses above
///     `2^63`, value-changing;
///   * `Ty::PtrSizedInt` — the faithful-extraction lane's spelling, which the
///     verifier lanes that consume this guard never receive; admitting it
///     untested would be a silent widening.
#[must_use]
pub fn ptr_expose_target_is_address_word(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { width: 64, signed: false })
}

/// The canonical same-allocation in-bounds statement for a byte range
/// `[offset, offset + byte_len]` inside an allocation of `alloc_size` bytes:
/// `0 <= offset && offset + byte_len <= alloc_size`.
///
/// This is `ptr::add`'s in-bounds precondition shape (with `byte_len =
/// count * size_of::<T>()`): the ONE-PAST-END offset (`offset + byte_len ==
/// alloc_size`) is deliberately IN bounds — Rust guarantees it for `add` —
/// while one byte further is out. All three operands are `Sort::Int` terms;
/// the caller supplies them (typically `alloc_size` is
/// [`alloc_size_symbol`]'s variable). Constructing the obligation asserts
/// NOTHING by itself: an unprovable instance stays an honest red/unknown.
#[must_use]
pub fn same_alloc_in_bounds(offset: Formula, byte_len: Formula, alloc_size: Formula) -> Formula {
    Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(0)), Box::new(offset.clone())),
        Formula::Le(
            Box::new(Formula::Add(Box::new(offset), Box::new(byte_len))),
            Box::new(alloc_size),
        ),
    ])
}

/// The exact byte size of `ty` on the pinned 64-bit target, for exactly the
/// sorts the allocation model COVERS in its second slice — fail-closed `None`
/// for everything else.
///
/// Covered (size is a layout theorem, no padding involved):
///   * `Ty::Int { width }` / `Ty::Float { width }` — `width / 8` bytes;
///   * `Ty::Bool` — 1 byte; `Ty::Char` — 4 bytes;
///   * `Ty::Array { elem, len }` over a covered element — `len * size(elem)`
///     exactly, because Rust guarantees `size_of::<T>()` is a multiple of
///     `align_of::<T>()`, so an array's stride IS its element size.
///
/// Deliberately DECLINED, fail-closed (each is a false-proof channel if
/// guessed): ADTs and tuples (rustc owns field ordering and padding),
/// slices/str/dyn (no static size), pointers and references (the model's
/// second slice covers allocation ROOTS of scalar/array sort only; widening
/// to pointer-typed roots is a separate audited step), `SymArray` (symbolic
/// length), and every other sort. Overflow in `len * size` declines too.
#[must_use]
pub fn known_alloc_byte_size(ty: &Ty) -> Option<u128> {
    match ty {
        Ty::Int { width, .. } | Ty::Float { width } if width % 8 == 0 && *width > 0 => {
            Some(u128::from(*width) / 8)
        }
        Ty::Bool => Some(1),
        Ty::Char => Some(4),
        Ty::Array { elem, len } => {
            let elem_size = known_alloc_byte_size(elem)?;
            elem_size.checked_mul(u128::from(*len))
        }
        _ => None,
    }
}

/// TCB AXIOM `MAX_LIVE_ALLOC_BYTES` (`docs/TCB.md`, "Modeled-fact axioms"): on a
/// 64-bit target every LIVE allocation is smaller than `isize::MAX / 2` bytes. The
/// bridge's constant of the same name (`trust-ir-bridge`) is this value.
pub const MAX_LIVE_ALLOC_BYTES: u128 = (i64::MAX / 2) as u128;

/// `isize::MAX` on a 64-bit target: the largest allocation `Layout` admits, above
/// which a reservation panics "capacity overflow".
pub const ISIZE_MAX_64: u128 = i64::MAX as u128;

/// Trust (2026-10-06, `docs/DECISION_QUEUE.md` D12 option (a)): may a `collect` or
/// `extend` whose source is an EXISTING collection skip its capacity-overflow
/// charge?
///
/// `max_source_items` bounds how many items the destination can reserve for UPFRONT
/// on the axiom above — the source's item count (a slice of `T` holds at most
/// `MAX_LIVE_ALLOC_BYTES / size_of::<T>()`), or for a str view the larger of its
/// `size_hint().0` ([`str_view_max_reserved_items`]) — and
/// `dest_item_max_bytes` bounds what the destination reserves per item. The skip is
/// sound exactly when even the largest possible upfront reservation fits:
/// `max_source_items * dest_item_max_bytes` within `isize::MAX`, or, for an
/// `extend`, within `isize::MAX - MAX_LIVE_ALLOC_BYTES`, because the receiver's own
/// live bytes are added to it. Growth that doubles a live buffer needs no check: the
/// buffer is itself a live allocation.
///
/// Before this the grant asked only that the source be bounded, so a destination
/// element of any size passed: `v.chunks(1).map(|_| MaybeUninit::<[u8; 1 << 40]>
/// ::uninit()).collect::<Vec<_>>()` panicked "capacity overflow" on an 8 MiB input
/// and was reported proved (review round 52). The arithmetic is checked, so any
/// overflow refuses.
#[must_use]
pub fn bounded_source_reservation_fits(
    max_source_items: u128,
    dest_item_max_bytes: u128,
    dest_fixed_bytes: u128,
    into_live_receiver: bool,
) -> bool {
    let budget =
        if into_live_receiver { ISIZE_MAX_64 - MAX_LIVE_ALLOC_BYTES } else { ISIZE_MAX_64 };
    max_source_items
        .checked_mul(dest_item_max_bytes)
        .and_then(|bytes| bytes.checked_add(dest_fixed_bytes))
        .is_some_and(|bytes| bytes <= budget)
}

/// The bytes a hash table reserves beyond its per-item charge, whatever its size:
/// hashbrown's `calculate_layout_for` rounds the bucket array up to `ctrl_align`
/// (at most `2^29`, Rust's largest alignment) and then requires the whole length to
/// stay below `isize::MAX - (ctrl_align - 1)`, plus one 16-byte control group. A
/// per-item term cannot absorb that for a one-item table, so it is charged once
/// (review round 55).
pub const HASH_TABLE_FIXED_BYTES: u128 = 1 << 31;

/// `BTreeSet`/`BTreeMap::from_iter` collect into a `Vec` and then stable-sort it,
/// and driftsort's scratch buffer is at least `SMALL_SORT_GENERAL_SCRATCH_LEN = 48`
/// elements once there are more than 20. So a BTree destination reserves as if for
/// at least this many items (review round 55: 21 items of `2e17` bytes each fit the
/// axiom, and the 48-element scratch overflowed).
pub const BTREE_FROM_ITER_MIN_RESERVED_ITEMS: u128 = 48;

/// The bytes a FRESH hashbrown (0.17) table reserves per item, for a table of `n`
/// items whose entry is `entry_bytes`. `capacity_to_buckets` raises a small capacity
/// to a floor (14 items for a one-byte entry, 7 for two or three bytes, 3 otherwise),
/// then takes 4 buckets below 4, 8 below 8, 16 below 15, and `next_power_of_two(n * 8
/// / 7) < 16n / 7` above. So for an entry of four bytes or more the table has at most
/// `4n` buckets at every count, and for a smaller entry at most `max(16, 4n)`, whose
/// excess over `4n` is a few dozen bytes that cannot overflow anything. The layout is
/// `buckets * entry` plus a control byte per bucket and one 16-byte group, so
/// `4 * (entry + 1) + 32` per item, with the alignment term charged once as
/// [`HASH_TABLE_FIXED_BYTES`]. It also keeps `n * 8` (which `capacity_to_buckets`
/// checks) far from overflow whenever the product fits `isize::MAX`. Review round 53:
/// the earlier `3 * (entry + 1)` undercounts the 4-bucket floor of a one-item table.
/// NOT valid for an `extend` into a live table, which re-lays-out every existing
/// entry too; that is never granted.
#[must_use]
pub fn hash_table_reserved_bytes_per_item(entry_bytes: u128) -> Option<u128> {
    entry_bytes.checked_add(1)?.checked_mul(4)?.checked_add(32)
}

/// A str view's UPFRONT reservation is its `size_hint().0`, not its item count, and
/// after that a `Vec`/`String`/hash table grows by doubling a live buffer, which needs
/// no check. So for a str view the reservation bound is the largest `size_hint().0`
/// on the `MAX_LIVE_ALLOC_BYTES` axiom: `chars`/`char_indices` report
/// `(bytes + 3) / 4`; `encode_utf16` `ceil(bytes / 3)` (`"utf16"`); `bytes` one per
/// byte; the split family
/// (`split`, `split_whitespace`, `lines`, `matches`, …) reports `0`, bounded here by
/// one. `kind` is `"chars"`, `"utf16"`, `"bytes"` or anything else for the split
/// family. Review
/// round 53 measured the item-count bound refusing `s.split(',').collect::<Vec<&str>>()`.
#[must_use]
pub fn str_view_max_reserved_items(kind: &str) -> u128 {
    // Each bound is `size_hint().0` PLUS ONE: `Vec`'s non-`TrustedLen` paths
    // (`extend_desugared`, `SpecFromIterNested`) take an item and then reserve
    // `lower + 1`, and taking one char can leave `ceil(remaining / 4)` unchanged
    // (review round 54: `v.extend(s.chars())` into a `Vec<char>` landed exactly on the
    // budget). `MIN_NON_ZERO_CAP` needs nothing: it is one item for an element over
    // 1 KiB, and a few KiB below that. A `TrustedLen` source reserves its exact length,
    // which the item-count bounds already are.
    match kind {
        "chars" => MAX_LIVE_ALLOC_BYTES / 4 + 2,
        // `EncodeUtf16` reports `ceil(bytes / 3)`, plus one while a surrogate is
        // pending.
        "utf16" => MAX_LIVE_ALLOC_BYTES / 3 + 3,
        // `Bytes` is `TrustedLen`: exact.
        "bytes" => MAX_LIVE_ALLOC_BYTES,
        _ => 2,
    }
}

/// The most items a sequence of `elem_bytes`-byte elements can hold on the
/// `MAX_LIVE_ALLOC_BYTES` axiom; `None` for a zero-sized element, which bounds
/// nothing (`vec![(); 1 << 61]` costs no memory).
#[must_use]
pub fn max_items_of_live_sequence(elem_bytes: u128) -> Option<u128> {
    (elem_bytes > 0).then(|| MAX_LIVE_ALLOC_BYTES / elem_bytes)
}

/// A LOWER bound on `size_of::<ty>()` on a 64-bit target, `0` when nothing better
/// is known. Used only to bound how many items an existing collection holds, where
/// a smaller answer is always the safe one.
#[must_use]
pub fn item_min_bytes_64(ty: &Ty) -> u128 {
    item_min_bytes_rec(ty, 0)
}

fn item_min_bytes_rec(ty: &Ty, depth: usize) -> u128 {
    if depth > 16 {
        return 0;
    }
    match ty {
        Ty::Bool => 1,
        Ty::Char => 4,
        Ty::Int { width, .. } | Ty::Float { width } => u128::from(*width / 8),
        // A pointer to an unsized type carries its length or vtable: 16 bytes
        // (review round 56: `&[&str]` was sized as 8-byte items).
        Ty::Ref { inner: pointee, .. } | Ty::RawPtr { pointee, .. }
            if matches!(**pointee, Ty::Str | Ty::Slice { .. } | Ty::Dynamic { .. }) =>
        {
            16
        }
        Ty::PtrSizedInt { .. } | Ty::Ref { .. } | Ty::RawPtr { .. } => 8,
        // A `Vec<T, A>` is at least its pointer, capacity and length.
        Ty::Seq { .. } => 24,
        Ty::Array { elem, len } => {
            item_min_bytes_rec(elem, depth + 1).saturating_mul(u128::from(*len))
        }
        Ty::Tuple(fields) => {
            fields.iter().fold(0u128, |acc, f| acc.saturating_add(item_min_bytes_rec(f, depth + 1)))
        }
        Ty::Adt { layout: Some(layout), .. } => u128::from(layout.size),
        // A STRUCT's fields do not overlap, so their sizes add; a union's do, and an
        // ADT of unknown kind is read as one (its largest field).
        Ty::Adt { fields, variants, adt_kind, .. } if variants.is_empty() => {
            let sizes = fields
                .iter()
                .filter(|(name, _)| name != "__tag")
                .map(|(_, f)| item_min_bytes_rec(f, depth + 1));
            if *adt_kind == Some(crate::model::AdtKind::Struct) {
                sizes.fold(0u128, u128::saturating_add)
            } else {
                sizes.max().unwrap_or(0).max(u128::from(ty_is_definitely_nonzero_sized(ty)))
            }
        }
        _ => u128::from(ty_is_definitely_nonzero_sized(ty)),
    }
}

/// An UPPER bound on `size_of::<ty>()` on a 64-bit target, `None` when it is not
/// known. Covers the exact scalar/array sizes, pointers (at most a fat pointer's 16
/// bytes) and an ADT whose rustc layout the extractor recorded.
#[must_use]
pub fn item_max_bytes_64(ty: &Ty) -> Option<u128> {
    match ty {
        Ty::Unit => Some(0),
        Ty::PtrSizedInt { .. } => Some(8),
        Ty::Ref { .. } | Ty::RawPtr { .. } => Some(16),
        Ty::Adt { layout: Some(layout), .. } => Some(u128::from(layout.size)),
        Ty::Array { elem, len } => item_max_bytes_64(elem)?.checked_mul(u128::from(*len)),
        _ => known_alloc_byte_size(ty),
    }
}

/// `ty` is DEFINITELY at least one byte, so a slice, array or `Vec` of it holds at most
/// `isize::MAX` elements (an allocation never exceeds `isize::MAX` bytes). GRANTING:
/// every caller uses a `true` to bound a length, so a shape this cannot settle — a
/// type parameter, a compacted type, a closure, an unsized type — answers `false`.
///
/// An ADT whose layout the extractor read from rustc answers from it. Otherwise an
/// ENUM is at least one byte when a variant carries an at-least-one-byte field
/// (rustc lays out every variant with such a field in full, inhabited or not), or
/// when at least two variants are definitely INHABITED (a tag then needs a byte). A
/// variant that is uninhabited and has only zero-sized fields is ABSENT from rustc's
/// layout, which is why `Result<(), Infallible>` is zero-sized, so such variants do not
/// count towards the two. A STRUCT is at least one byte when a field is, and the
/// extractor's synthetic enum `__tag` is never one of them: `enum E { A }` is zero-sized.
///
/// ONE definition (2026-09-29). vcgen had two, and the bridge a third "faithful port"
/// of one of them, and they had drifted. The slice-length lane counted the synthetic
/// `__tag` as a byte, so `&[E]` for `enum E { A }` took `len <= isize::MAX` and a
/// counter over `usize::MAX` elements was proved; that lane was then corrected to
/// ignore the tag but not to count variants, so every fieldless enum (`Ordering`,
/// `enum { A, B }`, `Option<()>`) lost a bound its one-byte layout guarantees (the
/// trip-count lane's precondition audit). This is the variant-aware rule the
/// allocation lane already used, with the `__tag` exclusion and an explicit enum test
/// (a zero-variant enum such as `Infallible` is uninhabited, never a struct with no
/// fields).
#[must_use]
pub fn ty_is_definitely_nonzero_sized(ty: &Ty) -> bool {
    nonzero_sized(ty, 0)
}

fn adt_is_enum(
    variants: &[crate::model::VariantDef],
    adt_kind: Option<crate::model::AdtKind>,
) -> bool {
    !variants.is_empty() || adt_kind == Some(crate::model::AdtKind::Enum)
}

/// A field named `__tag` is the extractor's SYNTHETIC enum discriminant unless the
/// extractor stamped the ADT a `Struct` from rustc's `AdtDef`: then it is a real user
/// field (`struct Tagged { __tag: u8 }`), laid out like any other. Merge 2026-10-14:
/// origin/main's vcgen rule (`alloc_vcs::adt_is_variantless_enum_rendering`) reads the
/// stamp the same way, and the merged gate asks both rules, so without this a stamped
/// struct whose only sized field is `__tag` lost its grant
/// (`iter_hof_collect_count_tests::a_variantless_enum_payload_is_not_a_bounded_source`).
/// An unstamped or `Union`-stamped ADT keeps the exclusion.
fn is_synthetic_enum_tag(name: &str, adt_kind: Option<crate::model::AdtKind>) -> bool {
    name == "__tag" && adt_kind != Some(crate::model::AdtKind::Struct)
}

fn nonzero_sized(ty: &Ty, depth: usize) -> bool {
    if depth > 16 {
        return false;
    }
    match ty {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::FnPtr { .. }
        | Ty::Seq { .. } => true,
        Ty::Bv(width) => *width > 0,
        Ty::Array { elem, len } => *len > 0 && nonzero_sized(elem, depth + 1),
        Ty::Tuple(elems) => elems.iter().any(|e| nonzero_sized(e, depth + 1)),
        Ty::Adt { layout: Some(layout), .. } => layout.size > 0,
        Ty::Adt { variants, adt_kind, .. } if adt_is_enum(variants, *adt_kind) => {
            variants.iter().any(|v| v.fields.iter().any(|(_, f)| nonzero_sized(f, depth + 1)))
                || variants
                    .iter()
                    .filter(|v| v.fields.iter().all(|(_, f)| definitely_inhabited(f, depth + 1)))
                    .count()
                    >= 2
        }
        Ty::Adt { fields, adt_kind, .. } => fields.iter().any(|(name, f)| {
            !is_synthetic_enum_tag(name, *adt_kind) && nonzero_sized(f, depth + 1)
        }),
        _ => false,
    }
}

/// `ty` definitely has at least one value. `false` when unsure, which only ever
/// counts FEWER enum variants towards [`ty_is_definitely_nonzero_sized`]'s two.
fn definitely_inhabited(ty: &Ty, depth: usize) -> bool {
    if depth > 16 {
        return false;
    }
    match ty {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Bv(_)
        | Ty::Unit
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::FnPtr { .. }
        | Ty::Seq { .. } => true,
        Ty::Array { elem, len } => *len == 0 || definitely_inhabited(elem, depth + 1),
        Ty::Tuple(elems) => elems.iter().all(|e| definitely_inhabited(e, depth + 1)),
        Ty::Adt { variants, adt_kind, .. } if adt_is_enum(variants, *adt_kind) => variants
            .iter()
            .any(|v| v.fields.iter().all(|(_, f)| definitely_inhabited(f, depth + 1))),
        Ty::Adt { adt_kind: Some(crate::model::AdtKind::Union), .. } => false,
        // A stamped struct's real `__tag` field must be inhabited like any other (a
        // `false` here only counts fewer variants towards the two).
        Ty::Adt { fields, adt_kind, .. } => fields.iter().all(|(name, f)| {
            is_synthetic_enum_tag(name, *adt_kind) || definitely_inhabited(f, depth + 1)
        }),
        _ => false,
    }
}

/// The pinned 64-bit target's address-word maximum (`usize::MAX`), as the
/// model's integer sort. One symbol, so the axiom below and every consumer
/// spell the same constant.
pub const ADDRESS_WORD_MAX: u128 = u64::MAX as u128;

/// Bounds on the exposed ADDRESS of an allocation ROOT — a pointer created by
/// `&x` / `&raw x` of a whole local of covered sort, i.e. `(A, 0)` in the pair
/// model — as a conjunction over the address term the expose cast minted:
///
/// ```text
/// 1 <= addr  &&  addr <= usize::MAX - byte_size
/// ```
///
/// Both conjuncts are THEOREMS of the allocation model, not assumptions:
///
///   * A1 (never null): no allocated object contains address 0, and a Rust
///     reference/raw-borrow of a live local is non-null. So `base(A) >= 1`.
///   * A2 (one-past-end is representable): an allocated object never wraps
///     the address space and its one-past-end address `base(A) + size(A)` is
///     a representable address word — the exact property `ptr::add`'s
///     in-bounds contract relies on. So `base(A) <= usize::MAX - size(A)`.
///
/// For a ROOT the offset is 0, so `addr == base(A)` and these bounds are the
/// address-arithmetic image of [`same_alloc_in_bounds`]`(0, size, size)`. They
/// hold for EVERY concrete address the allocation takes (a loop-local re-lived
/// per iteration may move; the bounds are per-value, never cross-iteration
/// equalities), so conjoining them can only discharge a false-FAIL, never
/// manufacture a false-PROVE. Returns `None` (fail-closed, no fact) when
/// `byte_size` exceeds the address word — no such allocation can exist, and a
/// wrong bound is worse than none.
#[must_use]
pub fn alloc_root_address_bounds(addr: Formula, byte_size: u128) -> Option<Formula> {
    if byte_size > ADDRESS_WORD_MAX {
        return None;
    }
    let upper = ADDRESS_WORD_MAX - byte_size;
    let upper = i128::try_from(upper).ok()?;
    Some(Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(1)), Box::new(addr.clone())),
        Formula::Le(Box::new(addr), Box::new(Formula::Int(upper))),
    ]))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal concrete evaluator over the {And, Le, Add, Int} fragment
    /// [`same_alloc_in_bounds`] emits. Any node outside the fragment panics:
    /// the falsifying tests below must fail loudly, not vacuously, if the
    /// constructor's shape changes.
    fn eval_closed(f: &Formula) -> bool {
        fn int(f: &Formula) -> i128 {
            match f {
                Formula::Int(v) => *v,
                Formula::Add(a, b) => int(a) + int(b),
                other => panic!("non-integer node in closed in-bounds formula: {other:?}"),
            }
        }
        match f {
            Formula::And(cs) => cs.iter().all(eval_closed),
            Formula::Le(a, b) => int(a) <= int(b),
            other => panic!("non-boolean node in closed in-bounds formula: {other:?}"),
        }
    }

    fn in_bounds(offset: i128, byte_len: i128, alloc_size: i128) -> bool {
        eval_closed(&same_alloc_in_bounds(
            Formula::Int(offset),
            Formula::Int(byte_len),
            Formula::Int(alloc_size),
        ))
    }

    /// FALSIFYING: red if two distinct allocation ids ever share a base or
    /// size symbol (the "M==N collision" aliasing false-proof channel), or if
    /// the base and size namespaces overlap.
    #[test]
    fn alloc_symbols_are_injective_and_disjoint() {
        assert_ne!(alloc_base_symbol(AllocId(1)), alloc_base_symbol(AllocId(2)));
        assert_ne!(alloc_size_symbol(AllocId(1)), alloc_size_symbol(AllocId(2)));
        assert_ne!(alloc_base_symbol(AllocId(7)), alloc_size_symbol(AllocId(7)));
        // The exact reserved spellings are load-bearing (future freshen/deny
        // lists key on them); a silent rename must show up here.
        assert_eq!(alloc_base_symbol(AllocId(3)), "__trust_alloc_base_3");
        assert_eq!(alloc_size_symbol(AllocId(3)), "__trust_alloc_size_3");
    }

    /// FALSIFYING: red if the in-bounds statement's SEMANTICS are wrong — a
    /// flipped inequality, a dropped non-negativity conjunct, or an
    /// off-by-one at the one-past-end boundary all flip one of these.
    #[test]
    fn same_alloc_in_bounds_semantics() {
        // In bounds: interior, empty range, and the one-past-end boundary
        // Rust guarantees for `ptr::add`.
        assert!(in_bounds(0, 8, 8), "whole allocation is in bounds");
        assert!(in_bounds(3, 2, 8), "interior range is in bounds");
        assert!(in_bounds(8, 0, 8), "one-past-end with empty length is in bounds");
        // Out of bounds: each violated conjunct separately.
        assert!(!in_bounds(1, 8, 8), "range past the end must refute");
        assert!(!in_bounds(9, 0, 8), "offset beyond one-past-end must refute");
        assert!(!in_bounds(-1, 2, 8), "negative offset must refute (nonneg conjunct)");
        // A wrong-direction rewrite (`<` for `<=`) would break the boundary
        // cases above; a dropped `0 <= offset` breaks the negative case.
    }

    /// FALSIFYING: red if the covered byte-size table drifts from the pinned
    /// target's layout (each constant is a layout theorem), or if the
    /// fail-closed declines are widened to a padded/symbolic/unsized sort
    /// whose size would have to be guessed.
    #[test]
    fn known_alloc_byte_size_is_exact_and_fail_closed() {
        assert_eq!(known_alloc_byte_size(&Ty::u8()), Some(1));
        assert_eq!(known_alloc_byte_size(&Ty::u32()), Some(4));
        assert_eq!(known_alloc_byte_size(&Ty::i64()), Some(8));
        assert_eq!(known_alloc_byte_size(&Ty::u128()), Some(16));
        assert_eq!(known_alloc_byte_size(&Ty::Bool), Some(1));
        assert_eq!(known_alloc_byte_size(&Ty::Char), Some(4));
        assert_eq!(known_alloc_byte_size(&Ty::Float { width: 64 }), Some(8));
        assert_eq!(
            known_alloc_byte_size(&Ty::Array { elem: Box::new(Ty::u32()), len: 8 }),
            Some(32),
            "array stride is its element size (size_of is a multiple of align_of)"
        );
        assert_eq!(
            known_alloc_byte_size(&Ty::Array {
                elem: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 3 }),
                len: 2
            }),
            Some(6),
            "nested arrays multiply exactly"
        );
        assert_eq!(known_alloc_byte_size(&Ty::Array { elem: Box::new(Ty::u8()), len: 0 }), Some(0));
        // Fail-closed declines — red if any is widened to a guessed size.
        assert_eq!(
            known_alloc_byte_size(&Ty::Tuple(vec![Ty::u8(), Ty::u32()])),
            None,
            "tuple padding is rustc's, not ours"
        );
        assert_eq!(
            known_alloc_byte_size(&Ty::adt("m::S", vec![("f".to_string(), Ty::u8())])),
            None,
            "ADT layout is rustc's, not ours"
        );
        assert_eq!(known_alloc_byte_size(&Ty::Slice { elem: Box::new(Ty::u8()) }), None);
        assert_eq!(known_alloc_byte_size(&Ty::Str), None);
        assert_eq!(
            known_alloc_byte_size(&Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) }),
            None,
            "pointer-typed roots are a later audited widening, not a default"
        );
        assert_eq!(
            known_alloc_byte_size(&Ty::Ref { mutable: false, inner: Box::new(Ty::u8()) }),
            None
        );
        assert_eq!(known_alloc_byte_size(&Ty::Unit), None);
    }

    /// FALSIFYING for [`alloc_root_address_bounds`]: the two axioms' exact
    /// boundary values, via the closed evaluator. Red if A1 admits address 0,
    /// if A2 admits an address whose one-past-end wraps, or if either boundary
    /// is off by one.
    #[test]
    fn alloc_root_address_bounds_semantics() {
        let umax = i128::try_from(ADDRESS_WORD_MAX).unwrap();
        let holds = |addr: i128, size: u128| {
            eval_closed(
                &alloc_root_address_bounds(Formula::Int(addr), size)
                    .expect("covered size must yield bounds"),
            )
        };
        assert!(holds(1, 8), "the lowest non-null address is admissible");
        assert!(holds(umax - 8, 8), "one-past-end == usize::MAX exactly is representable");
        assert!(!holds(0, 8), "A1: address 0 is never inside an allocation");
        assert!(!holds(umax - 7, 8), "A2: one-past-end past usize::MAX must refute");
        assert!(holds(umax, 0), "a zero-sized root may sit at the top of the address space");
        assert!(!holds(0, 0), "A1 binds even for zero-sized roots (references are non-null)");
        // Fail-closed: an impossible size yields NO fact rather than a wrong one.
        assert!(alloc_root_address_bounds(Formula::Int(1), ADDRESS_WORD_MAX + 1).is_none());
    }

    /// FALSIFYING: red if the expose-target guard is widened to a
    /// value-changing target (narrower, signed, or the untested faithful-lane
    /// spelling) or narrowed to reject the address word itself.
    #[test]
    fn expose_target_guard_is_exactly_the_address_word() {
        assert!(ptr_expose_target_is_address_word(&Ty::usize()));
        assert!(ptr_expose_target_is_address_word(&Ty::u64()), "u64 == usize on the pinned target");
        assert!(!ptr_expose_target_is_address_word(&Ty::u32()), "narrowing truncates the address");
        assert!(!ptr_expose_target_is_address_word(&Ty::i64()), "signed reinterpret changes value");
        assert!(!ptr_expose_target_is_address_word(&Ty::isize()));
        assert!(
            !ptr_expose_target_is_address_word(&Ty::u128()),
            "widening past the word is not the addr() shape"
        );
        assert!(
            !ptr_expose_target_is_address_word(&Ty::PtrSizedInt { signed: false }),
            "faithful-lane spelling stays fail-closed until its own migration"
        );
        assert!(!ptr_expose_target_is_address_word(&Ty::Bool));
        assert!(!ptr_expose_target_is_address_word(&Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::u8())
        }));
    }
}

#[cfg(test)]
mod nonzero_sized_tests {
    use super::ty_is_definitely_nonzero_sized as nonzero;
    use crate::model::{AdtKind, AdtLayoutInfo, Ty, VariantDef};

    fn variant(name: &str, fields: Vec<Ty>) -> VariantDef {
        VariantDef {
            name: name.into(),
            discriminant: 0,
            fields: fields.into_iter().enumerate().map(|(i, t)| (i.to_string(), t)).collect(),
        }
    }

    fn enum_of(variants: Vec<VariantDef>) -> Ty {
        let mut ty = Ty::adt_enum("E", variants);
        if let Ty::Adt { adt_kind, .. } = &mut ty {
            *adt_kind = Some(AdtKind::Enum);
        }
        ty
    }

    #[test]
    fn a_fieldless_enum_is_one_byte_once_it_has_two_variants() {
        // `enum E { A }` is zero-sized; `enum E { A, B }`, `Ordering`, `Option<()>` are
        // one byte (the trip-count lane's precondition audit, `d01_completeness`).
        assert!(!nonzero(&enum_of(vec![variant("A", vec![])])));
        assert!(nonzero(&enum_of(vec![variant("A", vec![]), variant("B", vec![])])));
        assert!(nonzero(&enum_of(vec![
            variant("Less", vec![]),
            variant("Equal", vec![]),
            variant("Greater", vec![]),
        ])));
        assert!(nonzero(&enum_of(vec![variant("None", vec![]), variant("Some", vec![Ty::Unit])])));
    }

    #[test]
    fn an_uninhabited_zero_sized_variant_is_absent() {
        // `Infallible` is a zero-variant ENUM, not a field-less struct.
        let infallible = enum_of(vec![]);
        assert!(!nonzero(&infallible));
        // `Result<(), Infallible>` and `Option<Infallible>` are zero-sized.
        let ok_or_never =
            enum_of(vec![variant("Ok", vec![Ty::Unit]), variant("Err", vec![infallible.clone()])]);
        assert!(!nonzero(&ok_or_never));
        assert!(!nonzero(&enum_of(vec![
            variant("None", vec![]),
            variant("Some", vec![infallible.clone()]),
        ])));
        // A variant with a four-byte field is laid out even when uninhabited.
        assert!(nonzero(&enum_of(vec![
            variant("A", vec![]),
            variant("B", vec![infallible, Ty::u32()]),
        ])));
    }

    #[test]
    fn a_stamped_struct_field_named_tag_is_a_real_field() {
        // Merge 2026-10-14: the extractor stamps `Struct` from rustc's `AdtDef`, so a
        // `__tag` field there is the user's own; unstamped, it stays the synthetic tag.
        let tagged = |adt_kind: Option<AdtKind>, field: Ty| {
            let mut ty = Ty::adt("user::Tagged", vec![("__tag".to_string(), field)]);
            if let Ty::Adt { adt_kind: kind, .. } = &mut ty {
                *kind = adt_kind;
            }
            ty
        };
        assert!(nonzero(&tagged(Some(AdtKind::Struct), Ty::u8())));
        assert!(!nonzero(&tagged(None, Ty::u8())));
        assert!(!nonzero(&tagged(Some(AdtKind::Union), Ty::u8())));
        // ...and its inhabitedness counts: two variants each holding a struct whose
        // only field is the uninhabited `Infallible` are both absent, so no tag byte.
        let never = tagged(Some(AdtKind::Struct), enum_of(vec![]));
        assert!(!nonzero(&never));
        assert!(!nonzero(&enum_of(vec![
            variant("A", vec![never.clone()]),
            variant("B", vec![never]),
        ])));
    }

    #[test]
    fn the_synthetic_tag_is_not_a_byte() {
        // The flattened struct view of `enum E { A }` carries only the extractor's tag.
        let tag = ("__tag".to_string(), Ty::Int { width: 64, signed: true });
        assert!(!nonzero(&Ty::adt("E", vec![tag.clone()])));
        assert!(!nonzero(&Ty::adt("E", vec![tag.clone(), ("0".into(), Ty::Unit)])));
        assert!(nonzero(&Ty::adt("E", vec![tag, ("0".into(), Ty::u32())])));
    }

    #[test]
    fn a_read_layout_decides() {
        // `#[repr(u8)] enum E { A }` is one byte although it has one variant.
        let mut ty = enum_of(vec![variant("A", vec![])]);
        if let Ty::Adt { layout, .. } = &mut ty {
            *layout = Some(Box::new(AdtLayoutInfo {
                size: 1,
                align: 1,
                field_offsets: vec![],
                repr: "rust".into(),
            }));
        }
        assert!(nonzero(&ty));
    }

    #[test]
    fn zero_sized_and_unknown_shapes_are_not_granted() {
        assert!(!nonzero(&Ty::Unit));
        assert!(!nonzero(&Ty::Tuple(vec![Ty::Unit, Ty::Unit])));
        assert!(!nonzero(&Ty::Array { elem: Box::new(Ty::u32()), len: 0 }));
        assert!(!nonzero(&Ty::Adt {
            arbitrary_precision: None,
            validity_wrapper: None,
            adt_kind: None,
            layout: None,
            variants: Vec::new().into(),
            name: "Z".into(),
            fields: vec![].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        }));
        assert!(nonzero(&Ty::Tuple(vec![Ty::Unit, Ty::Bool])));
    }
}
