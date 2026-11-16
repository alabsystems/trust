//! trust-types: the COMPILER-MINTED callee key — identity without a rendering.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! # Why this module exists
//!
//! Rounds 3–6 of the unsafe-mint campaign each closed a real defect in ONE
//! decision procedure and each exposed the next, always in the same place: a
//! safety contract was being selected by PARSING A RENDERED STRING.
//!
//!   * round 3–4: the recognizers matched callee identity by SUBSTRING.
//!   * round 5:   the anchor's UFCS reject ran BEFORE turbofish stripping, so an
//!                associated-type argument killed genuine sysroot rows.
//!   * round 6:   `strip_turbofish_args` treated the `>` of `->` as a closing
//!                bracket, so `ptr::read::<fn() -> u8>` lost its contract.
//!   * round 6 review: a `char` CONST GENERIC whose value is `'>'` or `'<'`
//!                renders those bytes RAW and desynchronizes the same scan —
//!                `core::ptr::read::<chargen::Tok<'_('_, '_>'_>>`, from REAL
//!                extracted MIR.
//!
//! The pattern is not a sequence of scanner bugs; it is the DOMAIN. A type
//! argument is attacker-chosen content, a rendering puts that content inside the
//! delimiters a canonicalizer scans for, and so patching the scanner terminates
//! only when Rust stops growing type syntax.
//!
//! [`CalleeKey`] retires the domain instead of the bug. It is minted by the
//! extractor from `(TyCtxt, DefId)` ALONE — never from `generic_args`, never
//! from a rendered path — so for a fixed `def_id` it is byte-identical for
//! `f::<u8>`, `f::<fn() -> u8>`, `f::<Tok<'>', '<'>>`, and for any instantiation
//! written in any Rust that does not yet exist. There is no scanner to
//! desynchronize because there is no scan.
//!
//! # The fail-closed rule, which may never be weakened
//!
//! `Option<CalleeKey>` absent, or [`CalleeKey::sysroot_item`] `None`, means
//! "this call is not one of the items the unsafe mint recognizes". The consumer
//! MUST answer that by keeping the call's fail-closed stand-in / its
//! `[unsafe:unmodeled-call]` row. It must NEVER answer it by comparing the
//! rendered path — that is precisely the decision procedure this type exists to
//! retire, and a key that is consulted "when present" with a string fallback is
//! the old code with one more branch.

use serde::{Deserialize, Serialize};

/// The head of a `Self` type, as a CLOSED vocabulary. Enough to separate the
/// inherent impls the mint cares about, and deliberately not enough to
//  re-render a type.
///
/// `Adt` carries the type's OWN item name (`tcx.item_name` of the ADT's
/// `DefId`), not a rendering of the type: `Vec<Tok<'>', '<'>>` and `Vec<u8>`
/// both yield `Adt("Vec")`, which is the whole point — the generic argument is
/// not in the domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SelfTyHead<'a> {
    /// A nominal type, by its own item name.
    Adt(&'a str),
    /// The primitive slice `[T]`.
    Slice,
    /// The primitive `str`.
    Str,
    /// The primitive `char`.
    Char,
    /// `*const T`.
    ConstPtr,
    /// `*mut T`.
    MutPtr,
    /// Anything else — a tuple, a closure, a fn pointer, an array, a reference.
    /// Never matches a declaration; fails closed.
    Other,
}

/// WHO owns the callee item, as typed facts read off `tcx`.
///
/// This is the third component the `DefPath` segment list alone cannot supply:
/// Rust's `DefPath` for an inherent method does NOT contain the type.
/// `Vec::set_len` is `[Mod("vec"), Impl(#N), ValueNs("set_len")]` — `Vec`
/// appears only because the PRINTER resolves the impl's self type — and the
/// `Impl` disambiguator is not stable across sysroot builds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CalleeOwner<'a> {
    /// A free function; the payload is its FULL OWNER PATH — every module from
    /// the defining crate's root down to its immediate parent, joined with
    /// `::`, and never the crate root itself (the crate is
    /// [`CalleeKey::krate_name`], matched separately).
    ///
    /// `ptr` for `core::ptr::read`, `slice::raw` for
    /// `core::slice::raw::from_raw_parts`, `str::converts` for
    /// `core::str::converts::from_utf8_unchecked`.
    ///
    /// THE IMMEDIATE PARENT ALONE WAS NOT AN IDENTITY (fixed 2026-09-20). With
    /// only the last segment, the exact three-segment `core::ptr::read` became
    /// "a fn named `read` whose parent module is named `ptr`, ANYWHERE in
    /// `core`" — a `core::…::something::ptr::read` would have matched the
    /// `PtrRead` declaration and received `ptr::read`'s deref-validity contract.
    /// The structured key was LESS specific than the string it replaced, which
    /// is the one thing it may never be. Every segment here is a `Symbol` the
    /// compiler enumerated off the DEF PATH of a crate `is_real_sysroot_crate`
    /// already authenticated; a generic argument is not a module child and
    /// cannot appear in any of them.
    Module(&'a str),
    /// An inherent impl, by the impl's self-type head.
    Inherent(SelfTyHead<'a>),
    /// A trait impl, by the trait's own item name and the impl's self-type head.
    TraitImpl { trait_name: &'a str, self_ty: SelfTyHead<'a> },
    /// A method declared on a TRAIT itself (its default body or its required
    /// signature), by the trait's FULL path from the crate root, crate root
    /// excluded: `ops::try_trait::Try` for `core::ops::try_trait::Try::branch`.
    ///
    /// THIS NAMES NO IMPLEMENTATION, and a declaration keyed on it must say so.
    /// rustc's MIR names a trait method call by the TRAIT's `DefId` with `Self`
    /// in the generic arguments (`<Result<u8, E> as Try>::branch` is
    /// `FnDef(Try::branch, [Result<u8, E>])`), and the key deliberately never
    /// reads generic arguments. So a tag minted through this owner means only
    /// "the call reaches SOME impl of this sysroot trait's method"; a consumer
    /// that needs a particular impl must establish `Self` from something the key
    /// does not carry — for `TryBranch` (W4, 2026-09-25) that is the DefId of the
    /// call that PRODUCED the receiver (`str::find` returns `Option<usize>`,
    /// `Option::ok_or` returns `Result<T, E>`, and coherence lets only `core`
    /// implement `core::ops::Try` for either).
    ///
    /// The full path, not the trait's name, for the reason
    /// [`CalleeOwner::Module`] carries one: a structured key may never be less
    /// specific than the spelling it retires.
    TraitDecl(&'a str),
    /// Any owner shape the resolver did not recognize. Never matches a
    /// declaration; fails closed.
    Other,
}

/// The CLOSED vocabulary of sysroot items the unsafe mint recognizes.
///
/// A tag is minted by the extractor ONLY for a `DefId` whose defining crate
/// passed `is_real_sysroot_crate` — the artifact-residency IDENTITY verdict, not
/// the crate-NAME gate — so a crate compiled `--crate-name core` mints
/// `sysroot_item: None` and every minting recognizer answers false on it,
/// structurally rather than by discipline.
///
/// `#[non_exhaustive]` so a consumer outside this crate cannot write a `match`
/// that silently acquires a new variant's behaviour; inside the crate the
/// totality test below requires every variant to be declared.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SysrootItem {
    // ── the free `ptr::read*` / `ptr::write*` fns ──────────────────────────
    PtrRead,
    PtrReadVolatile,
    PtrReadUnaligned,
    PtrWrite,
    PtrWriteVolatile,
    PtrWriteUnaligned,
    // ── the intrinsic memmove pair ────────────────────────────────────────
    PtrCopy,
    PtrCopyNonOverlapping,
    // ── frees ─────────────────────────────────────────────────────────────
    PtrDropInPlace,
    RawPtrDropInPlace,
    AllocDealloc,
    AllocRealloc,
    AllocAlloc,
    AllocAllocZeroed,
    GlobalAllocatorAllocate,
    GlobalAllocatorDeallocate,
    // ── unchecked indexing ────────────────────────────────────────────────
    SliceGetUnchecked,
    SliceGetUncheckedMut,
    StrGetUnchecked,
    StrGetUncheckedMut,
    // ── raw-parts constructors ────────────────────────────────────────────
    SliceFromRawParts,
    SliceFromRawPartsMut,
    StrFromRawParts,
    StrFromRawPartsMut,
    VecFromRawParts,
    StringFromRawParts,
    // ── the capacity contract ─────────────────────────────────────────────
    VecSetLen,
    // Vec backing-storage operations; zero-sized elements allocate no storage.
    VecWithCapacity,
    VecWithCapacityIn,
    VecReserve,
    VecReserveExact,
    VecResize,
    VecResizeWith,
    VecFromElem,
    // ── niches ────────────────────────────────────────────────────────────
    NonZeroNewUnchecked,
    NonNullNewUnchecked,
    UniqueNewUnchecked,
    // ── type invariants ───────────────────────────────────────────────────
    CharFromU32Unchecked,
    CharMethodsFromU32Unchecked,
    StrFromUtf8Unchecked,
    StrFromUtf8UncheckedMut,
    StringFromUtf8Unchecked,
    CStrFromBytesWithNulUnchecked,
    MaybeUninitAssumeInit,
    MaybeUninitAssumeInitRef,
    MaybeUninitAssumeInitMut,
    MaybeUninitAssumeInitRead,
    MaybeUninitAssumeInitDrop,
    BoxAssumeInit,
    BoxAssumeInitIntoVecUnsafe,
    // ── the receiver-is-Some/Ok contract ──────────────────────────────────
    OptionUnwrapUnchecked,
    ResultUnwrapUnchecked,
    // ── Layout size relocation (the six exact passthroughs) ───────────────
    OptionUnwrap,
    OptionExpect,
    ResultUnwrap,
    ResultExpect,
    // ── transmute ─────────────────────────────────────────────────────────
    MemTransmute,
    MemTransmuteCopy,
    // ── the blanket-only ops ──────────────────────────────────────────────
    MemZeroed,
    MemUninitialized,
    HintUnreachableUnchecked,
    // ── Layout construction (the size DISCHARGE) ──────────────────────────
    LayoutFromSizeAlign,
    LayoutFromSizeAlignUnchecked,
    // ── raw-pointer offset methods (provenance propagation) ───────────────
    ConstPtrAdd,
    ConstPtrOffset,
    ConstPtrWrappingAdd,
    ConstPtrWrappingOffset,
    MutPtrAdd,
    MutPtrOffset,
    MutPtrWrappingAdd,
    MutPtrWrappingOffset,
    // ── raw-pointer pointee casts (address + provenance preserved) ────────
    ConstPtrCast,
    ConstPtrCastMut,
    MutPtrCast,
    MutPtrCastConst,
    // ── container `as_ptr` (provenance propagation) ───────────────────────
    //
    // COMPLETED 2026-09-20. The five below the line were the whole vocabulary
    // until then, and the round-7 migration to this key therefore SILENTLY
    // NARROWED the recognizer it replaced: `is_container_as_ptr_call`'s round-6
    // string matched any `core::`/`alloc::`/`std::`-rooted path containing
    // `::as_ptr` / `::as_mut_ptr`, so `core::str::<impl str>::as_ptr`,
    // `MaybeUninit::as_ptr`, `NonNull::as_ptr` and the rest were all matched
    // there and NONE of them could be named here. MEASURED, on the fixtures
    // `asptr` and `provebounds`: 2 and 3 TYPED `CopyBoundsViolation` rows lost
    // against the seal, the only two of nine direction-B fixtures that did not
    // hold the "seal-only delta is exactly the retired stand-in" accounting.
    //
    // `String::as_ptr` DOES NOT EXIST in this sysroot (`alloc/src/string.rs` has
    // no such inherent method): `s.as_ptr()` on a `String` derefs to `str`, so
    // the row below it is the one a `String` receiver actually reaches. The
    // `StringAsPtr` declaration is kept — an older sysroot had it — and is
    // simply unreachable here.
    SliceAsPtr,
    SliceAsMutPtr,
    VecAsPtr,
    VecAsMutPtr,
    StringAsPtr,
    StrAsPtr,
    StrAsMutPtr,
    MaybeUninitAsPtr,
    MaybeUninitAsMutPtr,
    NonNullAsPtr,
    NonNullAsMutPtr,
    UniqueAsPtr,
    CStrAsPtr,
    CellAsPtr,
    RefCellAsPtr,
    BoxAsPtr,
    BoxAsMutPtr,
    RawSlicePtrAsPtr,
    RawSlicePtrAsMutPtr,
    // THE OMISSIONS, CLOSED 2026-09-20 — and they were MEASURED ROW LOSSES,
    // not the fail-closed misses the sweep claimed. See `DECLS` for the
    // three-lane numbers per item.
    RcAsPtr,
    ArcAsPtr,
    WeakAsPtr,
    AtomicAsPtr,
    SliceAssumeInitRef,
    // ── the safe box allocation the mint admits ───────────────────────────
    BoxNew,
    BoxNewUninit,
    // ── W4 (2026-09-25): SAFE items whose RESULT carries a value fact ─────
    // None of these is an unsafe fn, so `call_has_unsafe_model_keyed` (gated on
    // the callee's unsafe signature at its only call site) never sees them.
    // ALLOC-LEN: a length that an existing live allocation bounds, and the
    // `String` capacity constructor whose element stride is definitionally 1.
    StrLen,
    SliceLen,
    StringLen,
    VecLen,
    StringWithCapacity,
    // STR-OFFSET: the str searches whose `Some(i)` / `true` result bounds an
    // offset, and the `Option -> Result -> ControlFlow` hops a `?` or
    // `ok_or` puts between the search and the payload read.
    StrFind,
    StrRfind,
    StrStartsWith,
    StrEndsWith,
    OptionOkOr,
    OptionOkOrElse,
    /// `core::ops::try_trait::Try::branch` — the TRAIT method; see
    /// [`CalleeOwner::TraitDecl`]: this tag alone does not name an impl.
    TryBranch,
    // ── W4 round 3 (2026-09-29): the str split whose panic is TWO-sided ───
    // `str::split_at(mid)` / `split_at_mut(mid)` panic when `mid > len` OR when
    // `mid` is not a UTF-8 char boundary. The tag is how the call-site panic lane
    // (`panic_calls::slice_method_panic_body`, `SplitAt`) learns the receiver is
    // a `str` and not a `[T]` — the two are one `[u8]` after extraction — so it
    // charges the char-boundary half, which no formula term models.
    StrSplitAt,
    StrSplitAtMut,
    // ── bounded iterator producers (W4 ITER-HOF (c), 2026-09-25) ──────────
    //
    // Consumed ONLY by the unbounded-allocation lane's bounded-source walk
    // (`trust_vcgen::generate::alloc_vcs::key_is_bounded_keyed_producer`), which
    // grants a `collect` over them: a sub-range of an already-built map/set yields
    // at most its length, and a `char` case mapping at most three `char`s. No
    // unsafe-mint recognizer names them, and the recognizer guard in
    // `trust_vcgen::sep_engine` refuses every tag it does not name.
    BTreeMapRange,
    BTreeMapRangeMut,
    BTreeSetRange,
    CharToLowercase,
    CharToUppercase,
    // ── STR_BYTES_POSITION_BOUND (2026-10-04) ───────────────────────────────
    // `str::bytes` builds the iterator, and `Iterator::position` on it returns
    // `Some(i)` only for `i < items remaining <= len(s)`
    // (`generate::str_offset::str_bytes_position_dest_facts`).
    StrBytes,
    /// `core::iter::traits::iterator::Iterator::position` — the TRAIT method, as
    /// the extractor keys it (the unresolved trait-method DefId). Like
    /// [`SysrootItem::TryBranch`] it names NO impl: a consumer must pin `Self`
    /// from the receiver (the bound lane requires a `&mut` of a local built by
    /// [`SysrootItem::StrBytes`]).
    IteratorPosition,
    // STR_BYTES_POSITION_BOUND, widened 2026-10-04: core `<[T]>::iter` builds a
    // `slice::Iter`, and the TRAIT method `Iterator::rposition` searches from the
    // back; both bound `Some(i)` by the slice length.
    SliceIter,
    /// `core::iter::traits::iterator::Iterator::rposition` — the TRAIT method, naming
    /// no impl (see [`SysrootItem::IteratorPosition`]).
    IteratorRposition,
    // MEM_REPLACE_SWAP (2026-10-05): the free `core::mem::replace` / `core::mem::swap`,
    // whose effect on their `&mut` arguments is exact
    // (`generate::call_facts::mem_replace_swap_facts`).
    MemReplace,
    MemSwap,
    // MEM_REPLACE_SWAP, widened (2026-10-05): the free `core::mem::take`, which is
    // `replace(dest, T::default())`; the lane admits it only at types whose default it
    // models exactly (an integer's `0`, a std `Vec`'s length `0`).
    MemTake,
    /// `core::clone::Clone::clone` — the TRAIT method, naming no impl. A consumer
    /// fixes the impl by type: `clone` returns `Self`, so a std-`Vec` destination makes
    /// alloc's `impl Clone for Vec<T, A>` the only candidate (coherence).
    /// VEC_CLONE_LEN (2026-10-05, `guards::slice_last_some_nonempty_definitions`).
    CloneClone,
    /// `core::option::Option::<&T>::copied` and `Option::<&mut T>::copied` — both
    /// inherent on `Option`, one row (TINV-21, 2026-10-06). `T: Copy`, so the body is
    /// `match self { Some(&v) => Some(v), None => None }`: a bitwise copy, no user code,
    /// it writes only its destination and keeps the variant. Consumed ONLY by the
    /// `get`-`Some` recognizer's `copied` hop (`guards::option_copied_hop`). `cloned` is
    /// deliberately NOT declared: it runs a user `Clone::clone`.
    OptionCopied,
    // ── std thread creation (REFUSAL ONLY, never a minting authority) ─────
    //
    // These five are NOT in `DECLS` and `sysroot_item_for` never returns them.
    // The extractor mints them from std's own `rustc_diagnostic_item`s
    // (`thread_spawn`, `thread_builder_spawn`, `thread_builder_spawn_unchecked`,
    // `thread_builder_spawn_scoped`, `thread_scope_spawn`) through the SAME
    // classifier the compiler's spawn census uses
    // (`trust_mir_extract::concurrency_effects::is_std_thread_spawn`), so the
    // router's refusal and the census can no longer disagree about which calls
    // are spawns. A structural (owner, leaf) declaration would be a second,
    // independent identity — exactly the drift this carrier retires. See
    // [`std_thread_spawn_item_for_diagnostic_name`].
    ThreadSpawn,
    ThreadBuilderSpawn,
    ThreadBuilderSpawnUnchecked,
    ThreadBuilderSpawnScoped,
    ThreadScopeSpawn,
}

/// The std thread-creation tags, minted ONLY from std's diagnostic items (see the
/// variants' comment). A consumer that refuses on a spawn names this set.
pub const STD_THREAD_SPAWN_ITEMS: &[SysrootItem] = &[
    SysrootItem::ThreadSpawn,
    SysrootItem::ThreadBuilderSpawn,
    SysrootItem::ThreadBuilderSpawnUnchecked,
    SysrootItem::ThreadBuilderSpawnScoped,
    SysrootItem::ThreadScopeSpawn,
];

/// Map a std `rustc_diagnostic_item` NAME to its thread-creation tag. The caller
/// (the extractor) must already have authenticated the `DefId` as living in the
/// real sysroot `std` (`is_std_thread_spawn`): the name alone is not identity,
/// since any crate under `rustc_attrs` may declare a diagnostic item.
#[must_use]
pub fn std_thread_spawn_item_for_diagnostic_name(name: &str) -> Option<SysrootItem> {
    Some(match name {
        "thread_spawn" => SysrootItem::ThreadSpawn,
        "thread_builder_spawn" => SysrootItem::ThreadBuilderSpawn,
        "thread_builder_spawn_unchecked" => SysrootItem::ThreadBuilderSpawnUnchecked,
        "thread_builder_spawn_scoped" => SysrootItem::ThreadBuilderSpawnScoped,
        "thread_scope_spawn" => SysrootItem::ThreadScopeSpawn,
        _ => return None,
    })
}

/// One row of the declaration table: the typed facts that identify an item, and
/// the tag they mint.
///
/// EVERY spelling this table replaces was taken from REAL EXTRACTED MIR
/// (`-Ztrust-dump=mir` on the sealed `trustc 1.99.0-dev (ff538f905 2026-09-19)`),
/// and each row's comment carries the spelling it supersedes so the two can be
/// compared by hand.
struct Decl {
    /// `tcx.crate_name(def_id.krate)` — the DEFINING crate. Matched as a name
    /// and NOT as a path root: it is reached only after
    /// `is_real_sysroot_crate` has already authenticated the crate, and it is
    /// unreachable from a type argument because it is not a path prefix.
    krate: &'static str,
    owner: OwnerPat,
    /// `tcx.item_name(def_id)` — the item's OWN name, a `Symbol` the compiler
    /// enumerated, never a substring of a rendering.
    leaf: &'static str,
    item: SysrootItem,
}

/// The owner half of a declaration, in the same closed vocabulary as
/// [`CalleeOwner`] but with `'static` payloads.
#[derive(Clone, Copy)]
enum OwnerPat {
    /// The FULL owner path, crate root excluded — `"ptr"`, `"slice::raw"`,
    /// `"str::converts"`. Compared BYTE-EQUAL against
    /// [`CalleeOwner::Module`], which carries the same shape.
    Module(&'static str),
    InherentAdt(&'static str),
    InherentSlice,
    InherentStr,
    InherentChar,
    InherentConstPtr,
    InherentMutPtr,
    TraitImpl {
        trait_name: &'static str,
        self_ty_adt: &'static str,
    },
    /// A trait's own method, by the trait's full path — see
    /// [`CalleeOwner::TraitDecl`] for what such a tag does NOT establish.
    TraitDecl(&'static str),
}

impl OwnerPat {
    fn matches(self, owner: CalleeOwner<'_>) -> bool {
        match (self, owner) {
            (OwnerPat::Module(m), CalleeOwner::Module(o)) => m == o,
            (OwnerPat::InherentAdt(a), CalleeOwner::Inherent(SelfTyHead::Adt(o))) => a == o,
            (OwnerPat::InherentSlice, CalleeOwner::Inherent(SelfTyHead::Slice)) => true,
            (OwnerPat::InherentStr, CalleeOwner::Inherent(SelfTyHead::Str)) => true,
            (OwnerPat::InherentChar, CalleeOwner::Inherent(SelfTyHead::Char)) => true,
            (OwnerPat::InherentConstPtr, CalleeOwner::Inherent(SelfTyHead::ConstPtr)) => true,
            (OwnerPat::InherentMutPtr, CalleeOwner::Inherent(SelfTyHead::MutPtr)) => true,
            (
                OwnerPat::TraitImpl { trait_name, self_ty_adt },
                CalleeOwner::TraitImpl { trait_name: t, self_ty: SelfTyHead::Adt(s) },
            ) => trait_name == t && self_ty_adt == s,
            (OwnerPat::TraitDecl(path), CalleeOwner::TraitDecl(o)) => path == o,
            _ => false,
        }
    }
}

/// THE DECLARATION TABLE. Total over [`SysrootItem`] — `every_sysroot_item_is_declared`
/// below is RED for a variant that is added here and not declared, which is what
/// keeps the vocabulary closed rather than merely documented.
const DECLS: &[Decl] = &[
    // core::ptr::read::<u64>, …::read_volatile, …::read_unaligned, …::write*
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "read",
        item: SysrootItem::PtrRead,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "read_volatile",
        item: SysrootItem::PtrReadVolatile,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "read_unaligned",
        item: SysrootItem::PtrReadUnaligned,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "write",
        item: SysrootItem::PtrWrite,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "write_volatile",
        item: SysrootItem::PtrWriteVolatile,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "write_unaligned",
        item: SysrootItem::PtrWriteUnaligned,
    },
    // core::ptr::copy::<u8>, core::ptr::copy_nonoverlapping::<u8>
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "copy",
        item: SysrootItem::PtrCopy,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "copy_nonoverlapping",
        item: SysrootItem::PtrCopyNonOverlapping,
    },
    // core::ptr::drop_in_place::<alloc::string::String>
    Decl {
        krate: "core",
        owner: OwnerPat::Module("ptr"),
        leaf: "drop_in_place",
        item: SysrootItem::PtrDropInPlace,
    },
    // core::ptr::mut_ptr::<impl *mut alloc::string::String>::drop_in_place
    Decl {
        krate: "core",
        owner: OwnerPat::InherentMutPtr,
        leaf: "drop_in_place",
        item: SysrootItem::RawPtrDropInPlace,
    },
    // alloc::alloc::alloc / alloc_zeroed / dealloc / realloc
    Decl {
        krate: "alloc",
        owner: OwnerPat::Module("alloc"),
        leaf: "alloc",
        item: SysrootItem::AllocAlloc,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::Module("alloc"),
        leaf: "alloc_zeroed",
        item: SysrootItem::AllocAllocZeroed,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::Module("alloc"),
        leaf: "dealloc",
        item: SysrootItem::AllocDealloc,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::Module("alloc"),
        leaf: "realloc",
        item: SysrootItem::AllocRealloc,
    },
    // <alloc::alloc::Global as core::alloc::Allocator>::allocate / ::deallocate
    Decl {
        krate: "core",
        owner: OwnerPat::TraitImpl { trait_name: "Allocator", self_ty_adt: "Global" },
        leaf: "allocate",
        item: SysrootItem::GlobalAllocatorAllocate,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::TraitImpl { trait_name: "Allocator", self_ty_adt: "Global" },
        leaf: "deallocate",
        item: SysrootItem::GlobalAllocatorDeallocate,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::TraitImpl { trait_name: "Allocator", self_ty_adt: "Global" },
        leaf: "allocate",
        item: SysrootItem::GlobalAllocatorAllocate,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::TraitImpl { trait_name: "Allocator", self_ty_adt: "Global" },
        leaf: "deallocate",
        item: SysrootItem::GlobalAllocatorDeallocate,
    },
    // core::slice::<impl [u32]>::get_unchecked::<usize>, …_mut
    Decl {
        krate: "core",
        owner: OwnerPat::InherentSlice,
        leaf: "get_unchecked",
        item: SysrootItem::SliceGetUnchecked,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentSlice,
        leaf: "get_unchecked_mut",
        item: SysrootItem::SliceGetUncheckedMut,
    },
    // core::str::<impl str>::get_unchecked::<core::ops::range::RangeFrom<usize>>
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "get_unchecked",
        item: SysrootItem::StrGetUnchecked,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "get_unchecked_mut",
        item: SysrootItem::StrGetUncheckedMut,
    },
    // core::slice::raw::from_raw_parts::<'_, u8>, …_mut
    Decl {
        krate: "core",
        owner: OwnerPat::Module("slice::raw"),
        leaf: "from_raw_parts",
        item: SysrootItem::SliceFromRawParts,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("slice::raw"),
        leaf: "from_raw_parts_mut",
        item: SysrootItem::SliceFromRawPartsMut,
    },
    // core::str::converts::from_raw_parts::<'_>, …_mut
    Decl {
        krate: "core",
        owner: OwnerPat::Module("str::converts"),
        leaf: "from_raw_parts",
        item: SysrootItem::StrFromRawParts,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("str::converts"),
        leaf: "from_raw_parts_mut",
        item: SysrootItem::StrFromRawPartsMut,
    },
    // alloc::vec::Vec::<u8>::from_raw_parts / ::set_len
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "from_raw_parts",
        item: SysrootItem::VecFromRawParts,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "set_len",
        item: SysrootItem::VecSetLen,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "with_capacity",
        item: SysrootItem::VecWithCapacity,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "with_capacity_in",
        item: SysrootItem::VecWithCapacityIn,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "reserve",
        item: SysrootItem::VecReserve,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "reserve_exact",
        item: SysrootItem::VecReserveExact,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "resize",
        item: SysrootItem::VecResize,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "resize_with",
        item: SysrootItem::VecResizeWith,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::Module("vec"),
        leaf: "from_elem",
        item: SysrootItem::VecFromElem,
    },
    // alloc::string::String::from_raw_parts / ::from_utf8_unchecked
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("String"),
        leaf: "from_raw_parts",
        item: SysrootItem::StringFromRawParts,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("String"),
        leaf: "from_utf8_unchecked",
        item: SysrootItem::StringFromUtf8Unchecked,
    },
    // core::num::nonzero::NonZero::<usize>::new_unchecked
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("NonZero"),
        leaf: "new_unchecked",
        item: SysrootItem::NonZeroNewUnchecked,
    },
    // core::ptr::non_null::NonNull::<u8>::new_unchecked
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("NonNull"),
        leaf: "new_unchecked",
        item: SysrootItem::NonNullNewUnchecked,
    },
    // core::ptr::unique::Unique::<u8>::new_unchecked
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Unique"),
        leaf: "new_unchecked",
        item: SysrootItem::UniqueNewUnchecked,
    },
    // core::char::from_u32_unchecked (free fn)
    Decl {
        krate: "core",
        owner: OwnerPat::Module("char"),
        leaf: "from_u32_unchecked",
        item: SysrootItem::CharFromU32Unchecked,
    },
    // core::char::methods::<impl char>::from_u32_unchecked (inherent)
    Decl {
        krate: "core",
        owner: OwnerPat::InherentChar,
        leaf: "from_u32_unchecked",
        item: SysrootItem::CharMethodsFromU32Unchecked,
    },
    // core::str::converts::from_utf8_unchecked / …_mut
    Decl {
        krate: "core",
        owner: OwnerPat::Module("str::converts"),
        leaf: "from_utf8_unchecked",
        item: SysrootItem::StrFromUtf8Unchecked,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("str::converts"),
        leaf: "from_utf8_unchecked_mut",
        item: SysrootItem::StrFromUtf8UncheckedMut,
    },
    // core::ffi::c_str::CStr::from_bytes_with_nul_unchecked
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("CStr"),
        leaf: "from_bytes_with_nul_unchecked",
        item: SysrootItem::CStrFromBytesWithNulUnchecked,
    },
    // core::mem::maybe_uninit::MaybeUninit::<u32>::assume_init and siblings
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("MaybeUninit"),
        leaf: "assume_init",
        item: SysrootItem::MaybeUninitAssumeInit,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("MaybeUninit"),
        leaf: "assume_init_ref",
        item: SysrootItem::MaybeUninitAssumeInitRef,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("MaybeUninit"),
        leaf: "assume_init_mut",
        item: SysrootItem::MaybeUninitAssumeInitMut,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("MaybeUninit"),
        leaf: "assume_init_read",
        item: SysrootItem::MaybeUninitAssumeInitRead,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("MaybeUninit"),
        leaf: "assume_init_drop",
        item: SysrootItem::MaybeUninitAssumeInitDrop,
    },
    // alloc::boxed::Box::<MaybeUninit<u32>>::assume_init
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Box"),
        leaf: "assume_init",
        item: SysrootItem::BoxAssumeInit,
    },
    // alloc::boxed::box_assume_init_into_vec_unsafe::<u64, 2> (the vec! machinery)
    Decl {
        krate: "alloc",
        owner: OwnerPat::Module("boxed"),
        leaf: "box_assume_init_into_vec_unsafe",
        item: SysrootItem::BoxAssumeInitIntoVecUnsafe,
    },
    // alloc::boxed::Box::<T>::new / ::new_uninit
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Box"),
        leaf: "new",
        item: SysrootItem::BoxNew,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Box"),
        leaf: "new_uninit",
        item: SysrootItem::BoxNewUninit,
    },
    // core::option::Option::<u32>::unwrap_unchecked / ::unwrap / ::expect
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Option"),
        leaf: "unwrap_unchecked",
        item: SysrootItem::OptionUnwrapUnchecked,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Option"),
        leaf: "unwrap",
        item: SysrootItem::OptionUnwrap,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Option"),
        leaf: "expect",
        item: SysrootItem::OptionExpect,
    },
    // core::result::Result::<u32, ()>::unwrap_unchecked / ::unwrap / ::expect
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Result"),
        leaf: "unwrap_unchecked",
        item: SysrootItem::ResultUnwrapUnchecked,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Result"),
        leaf: "unwrap",
        item: SysrootItem::ResultUnwrap,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Result"),
        leaf: "expect",
        item: SysrootItem::ResultExpect,
    },
    // core::mem::transmute_copy::<u32, f32>, core::mem::transmute
    Decl {
        krate: "core",
        owner: OwnerPat::Module("mem"),
        leaf: "transmute",
        item: SysrootItem::MemTransmute,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("mem"),
        leaf: "transmute_copy",
        item: SysrootItem::MemTransmuteCopy,
    },
    // core::mem::zeroed::<T> / core::mem::uninitialized::<T>
    Decl {
        krate: "core",
        owner: OwnerPat::Module("mem"),
        leaf: "zeroed",
        item: SysrootItem::MemZeroed,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("mem"),
        leaf: "uninitialized",
        item: SysrootItem::MemUninitialized,
    },
    // core::hint::unreachable_unchecked
    Decl {
        krate: "core",
        owner: OwnerPat::Module("hint"),
        leaf: "unreachable_unchecked",
        item: SysrootItem::HintUnreachableUnchecked,
    },
    // core::alloc::layout::Layout::from_size_align[_unchecked]
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Layout"),
        leaf: "from_size_align",
        item: SysrootItem::LayoutFromSizeAlign,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Layout"),
        leaf: "from_size_align_unchecked",
        item: SysrootItem::LayoutFromSizeAlignUnchecked,
    },
    // core::ptr::const_ptr::<impl *const T>::add / offset / wrapping_*
    Decl {
        krate: "core",
        owner: OwnerPat::InherentConstPtr,
        leaf: "add",
        item: SysrootItem::ConstPtrAdd,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentConstPtr,
        leaf: "offset",
        item: SysrootItem::ConstPtrOffset,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentConstPtr,
        leaf: "wrapping_add",
        item: SysrootItem::ConstPtrWrappingAdd,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentConstPtr,
        leaf: "wrapping_offset",
        item: SysrootItem::ConstPtrWrappingOffset,
    },
    // core::ptr::mut_ptr::<impl *mut T>::add / offset / wrapping_*
    Decl {
        krate: "core",
        owner: OwnerPat::InherentMutPtr,
        leaf: "add",
        item: SysrootItem::MutPtrAdd,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentMutPtr,
        leaf: "offset",
        item: SysrootItem::MutPtrOffset,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentMutPtr,
        leaf: "wrapping_add",
        item: SysrootItem::MutPtrWrappingAdd,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentMutPtr,
        leaf: "wrapping_offset",
        item: SysrootItem::MutPtrWrappingOffset,
    },
    // core::ptr::const_ptr::<impl *const T>::cast / ::cast_mut
    Decl {
        krate: "core",
        owner: OwnerPat::InherentConstPtr,
        leaf: "cast",
        item: SysrootItem::ConstPtrCast,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentConstPtr,
        leaf: "cast_mut",
        item: SysrootItem::ConstPtrCastMut,
    },
    // core::ptr::mut_ptr::<impl *mut T>::cast / ::cast_const
    Decl {
        krate: "core",
        owner: OwnerPat::InherentMutPtr,
        leaf: "cast",
        item: SysrootItem::MutPtrCast,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentMutPtr,
        leaf: "cast_const",
        item: SysrootItem::MutPtrCastConst,
    },
    // core::slice::<impl [T]>::as_ptr / as_mut_ptr
    Decl {
        krate: "core",
        owner: OwnerPat::InherentSlice,
        leaf: "as_ptr",
        item: SysrootItem::SliceAsPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentSlice,
        leaf: "as_mut_ptr",
        item: SysrootItem::SliceAsMutPtr,
    },
    // alloc::vec::Vec::<T>::as_ptr / as_mut_ptr, alloc::string::String::as_ptr
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "as_ptr",
        item: SysrootItem::VecAsPtr,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "as_mut_ptr",
        item: SysrootItem::VecAsMutPtr,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("String"),
        leaf: "as_ptr",
        item: SysrootItem::StringAsPtr,
    },
    // THE SWEEP (2026-09-20). Every INHERENT `as_ptr`/`as_mut_ptr` in `core` and
    // `alloc` whose result aliases the receiver, enumerated from the sysroot
    // source rather than from memory:
    //   core/src/str/mod.rs                <impl str>::as_ptr / as_mut_ptr
    //   core/src/mem/maybe_uninit.rs       MaybeUninit::as_ptr / as_mut_ptr
    //   core/src/ptr/non_null.rs           NonNull::as_ptr, NonNull<[T]>::as_mut_ptr
    //   core/src/ptr/unique.rs             Unique::as_ptr
    //   core/src/ffi/c_str.rs              CStr::as_ptr
    //   core/src/cell.rs                   Cell::as_ptr, RefCell::as_ptr
    //   core/src/ptr/const_ptr.rs          <*const [T]>::as_ptr, <*const [T; N]>::as_ptr
    //   core/src/ptr/mut_ptr.rs            <*mut [T]>::as_mut_ptr, <*mut [T; N]>::as_mut_ptr
    //   alloc/src/boxed.rs                 Box::as_ptr / as_mut_ptr
    //
    // THE OMISSION NOTE THAT STOOD HERE WAS WRONG, AND "NOT MEASURED" IS WHY.
    // It read: "DELIBERATELY NOT DECLARED […] the twelve
    // `core::sync::atomic::Atomic*::as_ptr` methods and `Rc`/`Arc::as_ptr`.
    // Their receivers are not tracked buffers, so binding `dest`'s provenance
    // SIZE to a `container_byte_len` they do not have states nothing the engine
    // can use; a miss here is the fail-closed direction […] NOT MEASURED, so
    // they stay out." A fixture was built (`reports/unsafe-mint-round9-.../
    // direction-b/rcasptr.rs`) and it refuted the claim on all three lanes:
    // holding them out did not fail closed, it turned a TYPED row into a WEAKER
    // one. MEASURED, fix lane against BOTH the seal and the tip:
    //
    //     from_rc      typed `copy bounds violation in
    //     from_arc     core::slice::raw::from_raw_parts::<'_, u8> (src)`  LOST,
    //     from_atomic  replaced by `[unsafe:sep:call] … (unverified)`
    //     vec_control  (declared receiver) unchanged on all three lanes
    //
    //     census  seal 27 | tip 24 | fix 21    -> after this commit, fix 24,
    //                                             row-identical to the tip
    //
    // The whole `Atomic*` family is ONE inherent ADT in this sysroot
    // (`pub type AtomicU32 = Atomic<u32>;`, `pub type AtomicBool =
    // Atomic<bool>;`, `pub type AtomicPtr<T> = Atomic<*mut T>;`, and the
    // `atomic_int!` macro emits `pub type $atomic_type = Atomic<$int_type>;`),
    // so `InherentAdt("Atomic")` declares all fourteen of them with one row.
    //
    // THE RE-SWEEP, because "the same reasoning" was applied in more than one
    // place. Each candidate got a call site in `direction-b/sweep.rs` and three
    // lanes; two more were losses and are declared, two were measured harmless
    // and stay out WITH THE MEASUREMENT:
    //
    //   * `rc::Weak::as_ptr` / `sync::Weak::as_ptr` — LOSS. Both seal and tip
    //     carry the typed `from_raw_parts (src)` row (the round-6 string matched
    //     `::as_ptr` on them too); the fix lost it. Both ADTs are named `Weak`
    //     in crate `alloc`, so one row declares both — deliberate: they are the
    //     same operation on the same shape of receiver.
    //   * `<[MaybeUninit<T>]>::assume_init_ref` — LOSS, and against the SEAL
    //     alone. The seal mints `[unsafe:sep:assume_init] the value must be
    //     fully initialized`; the tip and the fix mint nothing. The note holding
    //     it out of `ASSUME_INIT_ITEMS` said its Self "is a primitive slice, not
    //     a crate-rooted path, so it never passed `callee_is_std_crate_rooted`"
    //     — measured false: the seal charges it.
    //   * `UnsafeCell::get` — MEASURED HARMLESS, stays out. `sweep::from_unsafe_cell`
    //     carries `[unsafe:sep:call] … (unverified)` on seal, tip AND fix: it was
    //     never tracked on any lane, so declaring it would be a WIDENING of what
    //     the engine claims to model, not the repair of a loss. A widening needs
    //     its own argument about the aliasing it asserts; this commit is about
    //     rows that went missing.
    //   * `<*const T>::sub` / `wrapping_sub` — MEASURED HARMLESS, stays out, and
    //     here the exclusion is SEMANTIC rather than an omission: the engine's
    //     offset arm adds the operand, and `sub` subtracts it, so declaring them
    //     would compute the WRONG address and could discharge a genuinely
    //     out-of-bounds offset. `sweep::const_ptr_sub` and
    //     `sweep::const_ptr_wrapping_sub` are row-identical between seal and tip
    //     modulo the retired blanket lint, so nothing is being lost by leaving
    //     them alone.
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "as_ptr",
        item: SysrootItem::StrAsPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "as_mut_ptr",
        item: SysrootItem::StrAsMutPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("MaybeUninit"),
        leaf: "as_ptr",
        item: SysrootItem::MaybeUninitAsPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("MaybeUninit"),
        leaf: "as_mut_ptr",
        item: SysrootItem::MaybeUninitAsMutPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("NonNull"),
        leaf: "as_ptr",
        item: SysrootItem::NonNullAsPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("NonNull"),
        leaf: "as_mut_ptr",
        item: SysrootItem::NonNullAsMutPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Unique"),
        leaf: "as_ptr",
        item: SysrootItem::UniqueAsPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("CStr"),
        leaf: "as_ptr",
        item: SysrootItem::CStrAsPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Cell"),
        leaf: "as_ptr",
        item: SysrootItem::CellAsPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("RefCell"),
        leaf: "as_ptr",
        item: SysrootItem::RefCellAsPtr,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Box"),
        leaf: "as_ptr",
        item: SysrootItem::BoxAsPtr,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Box"),
        leaf: "as_mut_ptr",
        item: SysrootItem::BoxAsMutPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentConstPtr,
        leaf: "as_ptr",
        item: SysrootItem::RawSlicePtrAsPtr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentMutPtr,
        leaf: "as_mut_ptr",
        item: SysrootItem::RawSlicePtrAsMutPtr,
    },
    // alloc::rc::Rc::<T>::as_ptr — an ASSOCIATED fn (`Rc::as_ptr(this)`), still
    // an inherent item of `Rc`, so the owner is the same shape as a method's.
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Rc"),
        leaf: "as_ptr",
        item: SysrootItem::RcAsPtr,
    },
    // alloc::sync::Arc::<T>::as_ptr
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Arc"),
        leaf: "as_ptr",
        item: SysrootItem::ArcAsPtr,
    },
    // alloc::rc::Weak::<T>::as_ptr AND alloc::sync::Weak::<T>::as_ptr. ONE row
    // for both: the owner is the self-type ADT's own `item_name`, and both ADTs
    // are named `Weak` in crate `alloc`. They are the same operation returning
    // the same aliasing pointer, so collapsing them is deliberate rather than an
    // accident of the matcher.
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Weak"),
        leaf: "as_ptr",
        item: SysrootItem::WeakAsPtr,
    },
    // core::sync::atomic::Atomic::<T>::as_ptr — the WHOLE `Atomic*` family.
    // `AtomicBool`, `AtomicPtr<T>` and every `AtomicI*`/`AtomicU*` are type
    // ALIASES for `Atomic<T>` in this sysroot, so the self-type ADT's item name
    // is `Atomic` for all of them and one declaration reaches all fourteen.
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Atomic"),
        leaf: "as_ptr",
        item: SysrootItem::AtomicAsPtr,
    },
    // core::mem::maybe_uninit::<impl [MaybeUninit<T>]>::assume_init_ref — the
    // SLICE form (unstable `maybe_uninit_slice`). Its owner is the primitive
    // slice, not an ADT, which is exactly why the old crate-rooted string could
    // not name it; the key can.
    Decl {
        krate: "core",
        owner: OwnerPat::InherentSlice,
        leaf: "assume_init_ref",
        item: SysrootItem::SliceAssumeInitRef,
    },
    // W4 (2026-09-25). `str::len` and `[T]::len` are `core` inherents,
    // `String::len`/`Vec::len`/`String::with_capacity` are `alloc` inherents,
    // each verified against this tree's `library/` at the declared owner.
    Decl { krate: "core", owner: OwnerPat::InherentStr, leaf: "len", item: SysrootItem::StrLen },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentSlice,
        leaf: "len",
        item: SysrootItem::SliceLen,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("String"),
        leaf: "len",
        item: SysrootItem::StringLen,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("Vec"),
        leaf: "len",
        item: SysrootItem::VecLen,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("String"),
        leaf: "with_capacity",
        item: SysrootItem::StringWithCapacity,
    },
    Decl { krate: "core", owner: OwnerPat::InherentStr, leaf: "find", item: SysrootItem::StrFind },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "rfind",
        item: SysrootItem::StrRfind,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "starts_with",
        item: SysrootItem::StrStartsWith,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "ends_with",
        item: SysrootItem::StrEndsWith,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Option"),
        leaf: "ok_or",
        item: SysrootItem::OptionOkOr,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Option"),
        leaf: "ok_or_else",
        item: SysrootItem::OptionOkOrElse,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::TraitDecl("ops::try_trait::Try"),
        leaf: "branch",
        item: SysrootItem::TryBranch,
    },
    // W4 round 3 (2026-09-29). core::str::<impl str>::split_at / split_at_mut —
    // `library/core/src/str/mod.rs` (`impl str`), both reaching
    // `slice_error_fail` on a non-boundary `mid`. The slice twins
    // (`core::slice::<impl [T]>::split_at`) are a different owner and stay
    // undeclared: their only panic is `mid > len`.
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "split_at",
        item: SysrootItem::StrSplitAt,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "split_at_mut",
        item: SysrootItem::StrSplitAtMut,
    },
    // alloc::collections::btree::map::BTreeMap::<u64, String>::range::<u64, Range<u64>>
    // (measured, unaimed-90 d1/p11), ::range_mut, and BTreeSet::<T>::range. The
    // self-type ADTs' own `item_name`s are `BTreeMap`/`BTreeSet`; both are
    // defined in `alloc`.
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("BTreeMap"),
        leaf: "range",
        item: SysrootItem::BTreeMapRange,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("BTreeMap"),
        leaf: "range_mut",
        item: SysrootItem::BTreeMapRangeMut,
    },
    Decl {
        krate: "alloc",
        owner: OwnerPat::InherentAdt("BTreeSet"),
        leaf: "range",
        item: SysrootItem::BTreeSetRange,
    },
    // core::char::methods::<impl char>::to_lowercase / ::to_uppercase
    Decl {
        krate: "core",
        owner: OwnerPat::InherentChar,
        leaf: "to_lowercase",
        item: SysrootItem::CharToLowercase,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::InherentChar,
        leaf: "to_uppercase",
        item: SysrootItem::CharToUppercase,
    },
    // STR_BYTES_POSITION_BOUND (2026-10-04). `core::str::<impl str>::bytes`
    // (`library/core/src/str/mod.rs`) and the TRAIT method
    // `Iterator::position` (`library/core/src/iter/traits/iterator.rs`). The
    // call is keyed on the trait method; `str::Bytes`'s own `position`
    // (`library/core/src/str/iter.rs`) only forwards to `Copied<slice::Iter<u8>>`,
    // which inherits the default. A `TraitImpl` owner would never match: the
    // extractor keys the unresolved trait method.
    Decl {
        krate: "core",
        owner: OwnerPat::InherentStr,
        leaf: "bytes",
        item: SysrootItem::StrBytes,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::TraitDecl("iter::traits::iterator::Iterator"),
        leaf: "position",
        item: SysrootItem::IteratorPosition,
    },
    // Widened 2026-10-04: core `<[T]>::iter` (`library/core/src/slice/mod.rs`) and
    // `Iterator::rposition`. `slice::Iter` overrides both `position` and `rposition`
    // (`library/core/src/slice/iter/macros.rs`) with an `i < n` assertion on the
    // remaining length; `str::Bytes` forwards both to `Copied<slice::Iter<u8>>`, which
    // runs the default searches (a counting `try_fold`, and `try_rfold` from `len()`).
    Decl {
        krate: "core",
        owner: OwnerPat::InherentSlice,
        leaf: "iter",
        item: SysrootItem::SliceIter,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::TraitDecl("iter::traits::iterator::Iterator"),
        leaf: "rposition",
        item: SysrootItem::IteratorRposition,
    },
    // MEM_REPLACE_SWAP (2026-10-05): `library/core/src/mem/mod.rs` `pub const fn
    // replace<T>(dest: &mut T, src: T) -> T` and `pub const fn swap<T>(x: &mut T, y: &mut T)`.
    Decl {
        krate: "core",
        owner: OwnerPat::Module("mem"),
        leaf: "replace",
        item: SysrootItem::MemReplace,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("mem"),
        leaf: "swap",
        item: SysrootItem::MemSwap,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::Module("mem"),
        leaf: "take",
        item: SysrootItem::MemTake,
    },
    Decl {
        krate: "core",
        owner: OwnerPat::TraitDecl("clone::Clone"),
        leaf: "clone",
        item: SysrootItem::CloneClone,
    },
    // TINV-21 (2026-10-06): core::option::Option::<&u8>::copied (measured, the P1
    // `peek` inventory body). `library/core/src/option.rs` declares it twice, in
    // `impl<T> Option<&T>` and `impl<T> Option<&mut T>`; both impls' self-type head is
    // the ADT `Option`, so this one row tags both. `cloned` stays undeclared.
    Decl {
        krate: "core",
        owner: OwnerPat::InherentAdt("Option"),
        leaf: "copied",
        item: SysrootItem::OptionCopied,
    },
];

/// Resolve typed owner/leaf facts to a [`SysrootItem`].
///
/// THE ONE PLACE A NAME IS STILL COMPARED, and why it is not a text parse: the
/// `&str`s compared here are `Symbol::as_str()` of items the COMPILER
/// enumerated — `tcx.item_name`, the parent module's `item_name`, the impl's
/// self-type ADT `item_name`, the trait's `item_name` — from a crate
/// `is_real_sysroot_crate` already authenticated. They are the sysroot's own
/// item names, not attacker-supplied content, and no walk here can descend into
/// a generic argument because a generic argument is neither a module child nor
/// an associated item. A `char` const generic holding `'>'`, a `fn() -> T`, a
/// `&'static str` const generic holding `"::<"` — none of them can appear in any
/// of these four symbols.
///
/// The caller MUST have authenticated the crate first; this function does not
/// (and cannot) do it, which is why it is `pub(crate)`-adjacent in spirit and
/// documented as a half of the rule rather than the whole of it.
/// Is `item` REACHABLE — does some [`DECLS`] row mint it?
///
/// A `SysrootItem` variant with no declaration is a tag NO extractor can ever
/// produce, so every recognizer that names it silently misses the call it meant
/// to recognize and the site falls through to its fail-closed stand-in — a loss
/// of TYPED rows that is invisible without a test. `every_sysroot_item_is_declared`
/// below keeps the enum total; this function is what lets a CONSUMER assert the
/// same thing about the tag set ITS recognizer names (see the keyed half of
/// `trust_vcgen::sep_engine`'s recognizer guard), so the gap is a test failure
/// rather than a comment.
#[must_use]
pub fn item_is_declared(item: SysrootItem) -> bool {
    DECLS.iter().any(|d| d.item == item) || STD_THREAD_SPAWN_ITEMS.contains(&item)
}

/// Every declared item whose LEAF NAME is `leaf`, in declaration order.
///
/// The inverse of [`item_is_declared`], and it exists for the same reason: a
/// consumer that groups items by what the sysroot calls them — the
/// `as_ptr`/`as_mut_ptr` family, say — can assert that its group is CLOSED over
/// the table, so a declaration added here without being added there is RED
/// instead of silently inert.
#[must_use]
pub fn declared_items_with_leaf(leaf: &str) -> Vec<SysrootItem> {
    DECLS.iter().filter(|d| d.leaf == leaf).map(|d| d.item).collect()
}

pub fn sysroot_item_for(krate: &str, owner: CalleeOwner<'_>, leaf: &str) -> Option<SysrootItem> {
    DECLS
        .iter()
        .find(|d| d.leaf == leaf && d.krate == krate && d.owner.matches(owner))
        .map(|d| d.item)
}

/// The DIVERGING-ENTRY class of a callee (DIVERGE-ENTRY-1): the callee is one of
/// the sysroot's own panic, abort or UB-if-reached entry points, so a call to it
/// that cannot return may be lowered as "this program point must be proven
/// unreachable" (`Assert(false)` + one row + `Unreachable`) INSTEAD of the
/// absent-callee may-panic row an unknown callee carries.
///
/// Minted ONLY by the extractor (`callee_key_for`), from `(TyCtxt, DefId)` alone,
/// and only when all three hold:
///
/// * the defining crate is a real sysroot crate (`is_real_sysroot_crate`, the
///   same artifact-residency verdict as [`CalleeKey::krate_is_real_sysroot`]);
/// * the `DefId` is NOT an item of a TRAIT (`tcx.trait_of_assoc` is `None`). A
///   call to a trait method carries the TRAIT's `DefId` with `Self` in the
///   generic arguments, so residency names the trait's crate while the body that
///   runs is the impl's — a verify-off dependency's `impl From<*mut u32> for V`
///   is keyed `core` like any other `From::from` (measured on the stage 1 of
///   `4463aeeb6d`);
/// * the GENERIC-FREE definition path (`safe_def_path_str`, which renders the
///   item's own declared parameters and never the call's arguments) is a panic,
///   abort or UB entry by the extractor's name predicates. The call's rendering
///   is never read: its generic arguments are user content, and
///   `<dep::panicking::V as core::convert::From<*mut u32>>::from` CONTAINS
///   `::panicking::`.
///
/// `None` on the key — every other callee, a frozen or serialized key from before
/// this field (serde default), a hand-built key — means "not a diverging entry",
/// and the consumer keeps the ordinary call arms. This is the identity the bridge's
/// diverging-site arm reads; a NAME is never one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DivergingEntry {
    /// A panic entry point (`core::panicking::*`, `std::panicking::begin_panic`, …)
    /// or a panic/abort terminal (`option::unwrap_failed`, `raw_vec::handle_error`,
    /// `process::abort`, …). Charged with the pinned panic wording.
    PanicOrAbort,
    /// A call whose execution is undefined behavior (`hint::unreachable_unchecked`,
    /// `intrinsics::unreachable`). Charged with the UB wording.
    UbIfReached,
}

/// The compiler-minted identity of a call's callee, shared by unsafe contracts
/// and allocation classification. Type arguments cannot affect this identity.
///
/// # What is deliberately absent
///
/// The generic arguments. MEASURED on this tree: of the recognizers in the
/// unsafe mint, NONE consults a generic argument — every one strips them. The
/// type information the typed arms need comes from MIR, not the path
/// (`decide_site`'s `zeroed`/`uninitialized` arms read `place_ty(func, dest)`,
/// the layout arm reads `args[0]` as a MIR operand, the mmap arm reads
/// `args.len() == 6`). So the arguments can be absent from identity with no
/// recognizer losing anything — and their absence is exactly what makes the
/// decision invariant under substitution.
// DELIBERATELY NOT `Default`, the same rule as `CalleeIdentity`: there is no
// blank key that could be minted by a `..Default::default()` struct update.
// Absence is carried by `Option` and by nothing else.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CalleeKey {
    /// The closed-vocabulary tag for a recognized sysroot item, resolved
    /// from `DefId` by the extractor. `None` = not one of
    /// them, which every MINTING recognizer must answer with false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sysroot_item: Option<SysrootItem>,
    /// `is_real_sysroot_crate(tcx, def_id.krate)` — the artifact-residency
    /// IDENTITY verdict, separated at last from the ambiguity verdict beside it.
    /// The rendered `__trust_crate@<id>::` stamp COLLAPSES the two: both the
    /// duplicate-name rule and the sysroot-impersonation rule mint the same
    /// prefix and no consumer can tell which fired.
    pub krate_is_real_sysroot: bool,
    /// Rule 1, UNIQUENESS: another loaded crate (or the local crate) renders the
    /// same name, so the name picks neither. Independent of the field above.
    pub krate_name_is_ambiguous: bool,
    /// `tcx.stable_crate_id(def_id.krate).as_u64()`.
    pub stable_crate_id: u64,
    /// The defining crate's `tcx.crate_name`, as a NAME and not as a root
    /// anchor: it is what the external-map crate-root list needs, and it is
    /// unreachable from a type argument because it is not a path prefix.
    pub krate_name: String,
    /// `Some(leaf)` iff the item's `DefPath` parent is `DefPathData::ForeignMod`
    /// — the structured form of the `{extern#N}` TEXT test. The leaf is
    /// `tcx.item_name`, a `Symbol`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub foreign_block_leaf: Option<String>,
    /// Trust (G1 review, 2026-10-27): `Some(symbol)` iff the callee is a foreign
    /// FUNCTION declared in an `extern` block of a crate OTHER than the one being
    /// compiled, and `symbol` is the symbol the linker resolves for it
    /// (`tcx.symbol_name(Instance::mono(..))`: the `#[link_name]` value when one is
    /// written, else the item's own name). `None` for every other callee — a Rust
    /// item, a foreign static, and a foreign function the LOCAL crate declares.
    ///
    /// [`CalleeKey::foreign_block_leaf`] is the declaration's Rust NAME: an
    /// `extern` block can write `#[link_name = "malloc"] fn __error()`, whose leaf is
    /// `__error` and whose callee is `malloc`. A consumer that believes a documented
    /// contract of a C SYMBOL (`trust_vcgen::ffi_pointer_contract`) keys on this
    /// field, never on the leaf. Absent from a key serialized before it existed, which
    /// reads as `None` (no symbol, no contract): the fail-closed direction.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub upstream_foreign_link_symbol: Option<String>,
    /// [`DivergingEntry`]: `Some` iff the callee is one of the sysroot's own
    /// panic, abort or UB-if-reached entry points, decided from the `DefId` (see
    /// the type). Read through [`CalleeKey::opt_diverging_entry`].
    /// `skip_serializing_if` keeps every other key's serialization byte-identical,
    /// and `default` reads a key serialized before this field as `None`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diverging_entry: Option<DivergingEntry>,
}

impl CalleeKey {
    /// Does this key name exactly one of `items`?
    ///
    /// THE FUNNEL, structured. `None` — a pre-carrier producer, an indirect
    /// call, a non-sysroot callee, a sysroot item not in the vocabulary — is
    /// false, and false here means the call keeps its fail-closed stand-in.
    pub fn is_one_of(&self, items: &[SysrootItem]) -> bool {
        self.sysroot_item.is_some_and(|i| items.contains(&i))
    }

    /// Does an OPTIONAL key name exactly one of `items`? The `None` arm is the
    /// fail-closed rule written once, so no caller has to remember it.
    pub fn opt_is_one_of(key: Option<&CalleeKey>, items: &[SysrootItem]) -> bool {
        key.is_some_and(|k| k.is_one_of(items))
    }

    /// The key's item when it is part of the MODELED vocabulary: a `DECLS` row
    /// the minting recognizers may name. A refusal-only tag
    /// ([`STD_THREAD_SPAWN_ITEMS`]) is `None` here. Consumers that read "the key
    /// names a sysroot item" as "Trust models this callee" (the unsafe-call
    /// model gate, the sep-coverage gate) must ask this, never
    /// `sysroot_item.is_some()`: a spawn tag is minted to REFUSE, and reading
    /// it as a model deletes the fail-closed `[unsafe:unmodeled-call]` row of
    /// the `unsafe fn` `Builder::spawn_unchecked` (measured 2026-09-28).
    #[must_use]
    pub fn modeled_sysroot_item(&self) -> Option<SysrootItem> {
        self.sysroot_item.filter(|item| !item_is_refusal_only(*item))
    }

    /// Is the callee DEFINED in a real sysroot crate? (SYSROOT-ANCHOR-1)
    ///
    /// This is [`CalleeKey::krate_is_real_sysroot`] — the extractor's
    /// `is_real_sysroot_crate(tcx, def_id.krate)`, the artifact-residency
    /// verdict, never a crate-NAME test — read through an OPTIONAL key, with the
    /// fail-closed rule written once: `None` (an indirect call, a pre-carrier
    /// producer, a synthesized call) is false.
    ///
    /// What it does and does not say. It names the crate of the callee's
    /// `DefId`. For a free function, an intrinsic, or an inherent method of a
    /// primitive scalar or `str`, that crate is the crate whose body runs. For a
    /// TRAIT method it is NOT: `<E as core::cmp::Ord>::min` is keyed on core's
    /// trait-method `DefId` while a user impl's body runs (NAME-ANCHOR-2), so a
    /// consumer that needs "std's body runs" for a trait method must pin `Self`
    /// as well. A diverging site is such a consumer: it reads
    /// [`CalleeKey::opt_diverging_entry`], never this alone (DIVERGE-ENTRY-1).
    #[must_use]
    pub fn opt_is_real_sysroot(key: Option<&CalleeKey>) -> bool {
        key.is_some_and(|k| k.krate_is_real_sysroot)
    }

    /// The callee's [`DivergingEntry`] class, read through an OPTIONAL key
    /// (DIVERGE-ENTRY-1). `None` — no key, a key with no class, or a class on a
    /// key whose `krate_is_real_sysroot` is false (which the extractor never
    /// mints) — means "not a diverging entry": the call keeps the ordinary call
    /// arms and, absent, its absent-callee row.
    #[must_use]
    pub fn opt_diverging_entry(key: Option<&CalleeKey>) -> Option<DivergingEntry> {
        key.filter(|k| k.krate_is_real_sysroot).and_then(|k| k.diverging_entry)
    }
}

/// The entry of `paths` that the rendered callee `func` IS, when the callee is
/// defined in a real sysroot crate (SYSROOT-ANCHOR-1).
///
/// `func` matches an entry `p` when it is exactly `p`, or `p` followed by ONE
/// trailing `::<…>` group (a turbofish, or a producer's trailing `::<__trust_…>`
/// marker): the rest after `p` must be empty, or start with `::<` and end with
/// `>`. A turbofish anywhere else does not match, and neither does a longer leaf
/// (`…::sin_x` is not `…::sin`). The key gate comes FIRST: a `None` key or a
/// key whose `krate_is_real_sysroot` is false answers `None` before any string
/// is read, so a user crate cannot reach the comparison at all.
///
/// # The doc rule, which every caller's `paths` must obey
///
/// `paths` may name ONLY items whose owner has no generic parameter: free
/// functions (`core::mem::size_of`), intrinsics, and inherent methods of a
/// primitive scalar or of `str` (`core::f64::<impl f64>::sin`). For those, every
/// byte of the rendering before the trailing turbofish is fixed by the callee's
/// `DefId`, and the key pins that `DefId` to the sysroot. An owner WITH a
/// generic parameter — `<impl [T]>`, `<impl *const [T]>`, `Vec::<T>`,
/// `Option::<T>` — renders the INSTANTIATED type in the middle of the path, so
/// user-chosen content sits inside the prefix being compared; and a trait
/// method names the trait, not the impl that runs. Those must use
/// [`SysrootItem`] (or a `Self` pin from MIR types) instead.
///
/// The S-F64METHOD spoof is the reason the comparison is a PREFIX of the whole
/// rendering and never a substring or a suffix: `core::cmp::max_by_key::<f64,
/// …, PhantomData<m::f64::cos<1>>>` is a real core callee (`krate_is_real_sysroot`
/// is true) whose rendering CONTAINS `f64::cos`, and it matches no entry.
///
/// The trailing-group test is a shape check, not a bracket parser (this module
/// exists because bracket scanners desynchronize). It needs no parser: the
/// callee is a sysroot item and the prefix is its own path, so only a sysroot
/// item's own path can put `::<` directly after the entry.
#[must_use]
pub fn sysroot_exact_path<'p>(
    key: Option<&CalleeKey>,
    func: &str,
    paths: &[&'p str],
) -> Option<&'p str> {
    if !CalleeKey::opt_is_real_sysroot(key) {
        return None;
    }
    paths.iter().copied().find(|p| match func.strip_prefix(p) {
        Some(rest) => rest.is_empty() || (rest.starts_with("::<") && rest.ends_with('>')),
        None => false,
    })
}

/// Whether `item` is a refusal-only tag: minted so a consumer can refuse the
/// call, never evidence that Trust models it. See
/// [`CalleeKey::modeled_sysroot_item`].
#[must_use]
pub fn item_is_refusal_only(item: SysrootItem) -> bool {
    STD_THREAD_SPAWN_ITEMS.contains(&item)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vec_storage_items_require_the_exact_structured_owner_and_leaf() {
        let methods = [
            ("with_capacity", SysrootItem::VecWithCapacity),
            ("with_capacity_in", SysrootItem::VecWithCapacityIn),
            ("reserve", SysrootItem::VecReserve),
            ("reserve_exact", SysrootItem::VecReserveExact),
            ("resize", SysrootItem::VecResize),
            ("resize_with", SysrootItem::VecResizeWith),
        ];
        for (leaf, item) in methods {
            let vec = CalleeOwner::Inherent(SelfTyHead::Adt("Vec"));
            assert_eq!(sysroot_item_for("alloc", vec, leaf), Some(item));
            assert_eq!(sysroot_item_for("user", vec, leaf), None);
            assert_eq!(
                sysroot_item_for("alloc", CalleeOwner::Inherent(SelfTyHead::Adt("HashMap")), leaf),
                None
            );
            assert_eq!(sysroot_item_for("alloc", CalleeOwner::Module("vec"), leaf), None);
            let encoded = serde_json::to_string(&item).unwrap();
            assert_eq!(serde_json::from_str::<SysrootItem>(&encoded).unwrap(), item);
        }
        assert_eq!(
            sysroot_item_for("alloc", CalleeOwner::Module("vec"), "from_elem"),
            Some(SysrootItem::VecFromElem)
        );
        assert_eq!(sysroot_item_for("alloc", CalleeOwner::Module("other::vec"), "from_elem"), None);
        assert_eq!(sysroot_item_for("user", CalleeOwner::Module("vec"), "from_elem"), None);
    }

    /// EVERY `SysrootItem` variant must appear in `DECLS`. A variant added to
    /// the vocabulary and never declared would be a tag no extractor can mint
    /// and every recognizer silently misses — a fail-closed hole that is
    /// invisible without this test.
    ///
    /// The list below is the totality witness: it is `SysrootItem`'s full
    /// variant set, written out, so adding a variant without declaring it is RED
    /// here AND the `match` below fails to compile if a variant is removed.
    #[test]
    fn every_sysroot_item_is_declared() {
        let all = ALL_SYSROOT_ITEMS;
        let mut missing = Vec::new();
        for item in all {
            if !item_is_declared(*item) {
                missing.push(format!("{item:?}"));
            }
        }
        assert!(missing.is_empty(), "SysrootItem variants with no declaration: {missing:?}");
    }

    /// The mirror: every declaration mints a variant that is in the witness list,
    /// so the witness cannot drift below the enum.
    #[test]
    fn every_declaration_is_in_the_totality_witness() {
        for d in DECLS {
            assert!(
                ALL_SYSROOT_ITEMS.contains(&d.item),
                "declaration mints {:?}, which the totality witness does not list",
                d.item
            );
        }
    }

    /// The spawn tags are minted from diagnostic items only: no structural
    /// `(krate, owner, leaf)` row reaches them, and every diagnostic name the
    /// census classifier accepts maps to exactly one of them.
    #[test]
    fn thread_spawn_items_are_minted_by_diagnostic_item_only() {
        for item in STD_THREAD_SPAWN_ITEMS {
            assert!(!DECLS.iter().any(|d| d.item == *item), "{item:?} has a structural row");
            assert!(item_is_declared(*item));
            assert!(ALL_SYSROOT_ITEMS.contains(item));
        }
        let names = [
            "thread_spawn",
            "thread_builder_spawn",
            "thread_builder_spawn_unchecked",
            "thread_builder_spawn_scoped",
            "thread_scope_spawn",
        ];
        let minted: Vec<_> =
            names.iter().filter_map(|n| std_thread_spawn_item_for_diagnostic_name(n)).collect();
        assert_eq!(minted, STD_THREAD_SPAWN_ITEMS);
        for near in ["thread_scope", "thread_local_macro", "spawn", "thread_spawn_x", ""] {
            assert_eq!(std_thread_spawn_item_for_diagnostic_name(near), None, "{near}");
        }
        for (owner, leaf) in [
            (CalleeOwner::Module("thread::functions"), "spawn"),
            (CalleeOwner::Inherent(SelfTyHead::Adt("Builder")), "spawn"),
            (CalleeOwner::Inherent(SelfTyHead::Adt("Builder")), "spawn_scoped"),
            (CalleeOwner::Inherent(SelfTyHead::Adt("Scope")), "spawn"),
        ] {
            assert_eq!(sysroot_item_for("std", owner, leaf), None);
        }
    }

    /// A NON-sysroot crate name can never resolve, whatever it is spelled.
    /// (The crate authentication itself is the extractor's job; this pins that
    /// the table does not admit a name the mint never meant.)
    #[test]
    fn a_user_crate_name_resolves_to_nothing() {
        for krate in ["mycrate", "userkrate", "evilcrate", "libc", "std"] {
            assert_eq!(sysroot_item_for(krate, CalleeOwner::Module("ptr"), "read"), None);
            assert_eq!(
                sysroot_item_for(krate, CalleeOwner::Inherent(SelfTyHead::Adt("Vec")), "set_len"),
                None
            );
        }
    }

    /// THE TERMINATION PROPERTY, at the table: the resolution's inputs are four
    /// `Symbol`s, so no rendering of a generic argument can reach it. These are
    /// the REAL adversarial shapes from the round-6 review, and every one of them
    /// resolves to the SAME tag as its plain-argument twin, because the argument
    /// is not an input at all.
    #[test]
    fn adversarial_type_arguments_are_not_in_the_domain() {
        // `core::ptr::read::<chargen::Tok<'(', '>'>>` and
        // `core::ptr::read::<fn() -> u8>` and `core::ptr::read::<u8>` all arrive
        // here as exactly these four symbols.
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Module("ptr"), "read"),
            Some(SysrootItem::PtrRead)
        );
        assert_eq!(
            sysroot_item_for("alloc", CalleeOwner::Inherent(SelfTyHead::Adt("Vec")), "set_len"),
            Some(SysrootItem::VecSetLen)
        );
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Inherent(SelfTyHead::Slice), "get_unchecked"),
            Some(SysrootItem::SliceGetUnchecked)
        );
    }

    /// THE PATH IS PART OF THE IDENTITY. Every `Module` declaration must match
    /// its OWN full owner path exactly, and must NOT match a same-leaf item
    /// under any other path.
    ///
    /// Until 2026-09-20 `OwnerPat::Module` carried only the IMMEDIATE parent
    /// module's name, so `(core, Module("ptr"), "read")` read as "a fn named
    /// `read` whose parent module is named `ptr`, anywhere in `core`" — the
    /// structured key was LESS specific than the three-segment string
    /// `core::ptr::read` it replaced. There was a totality test over the enum
    /// and none over the paths, which is exactly why this one is written
    /// GENERICALLY over `DECLS`: a row added with a truncated path is RED here
    /// without anyone having to think of it.
    #[test]
    fn a_module_declaration_matches_its_own_path_and_no_other() {
        for d in DECLS {
            let OwnerPat::Module(path) = d.owner else { continue };
            assert_eq!(
                sysroot_item_for(d.krate, CalleeOwner::Module(path), d.leaf),
                Some(d.item),
                "{}::{path}::{} must resolve to its own declaration",
                d.krate,
                d.leaf
            );
            // Same leaf, a DIFFERENT owner path. Each decoy is a shape the
            // truncated key admitted: the last segment alone (what the old
            // payload WAS for a multi-segment owner), the first segment alone,
            // the path nested under another module, the path with a module
            // appended, and the crate root itself.
            let last = path.rsplit("::").next().unwrap_or(path);
            let first = path.split("::").next().unwrap_or(path);
            let decoys = [
                last.to_string(),
                first.to_string(),
                format!("wrapper::{path}"),
                format!("{path}::inner"),
                String::new(),
            ];
            for decoy in decoys {
                if decoy == path {
                    continue;
                }
                assert_eq!(
                    sysroot_item_for(d.krate, CalleeOwner::Module(&decoy), d.leaf),
                    None,
                    "{}::{decoy}::{} is NOT {:?} — a same-leaf item under another \
                     path must not inherit a declaration",
                    d.krate,
                    d.leaf,
                    d.item
                );
            }
        }
    }

    /// The two owner paths the immediate-parent key could not tell apart from
    /// their last segment, spelled out as real extracted MIR spells them.
    #[test]
    fn the_multi_segment_owner_paths_are_whole() {
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Module("slice::raw"), "from_raw_parts"),
            Some(SysrootItem::SliceFromRawParts)
        );
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Module("str::converts"), "from_raw_parts"),
            Some(SysrootItem::StrFromRawParts)
        );
        // `raw` and `converts` alone were the WHOLE key until this commit, and
        // either one names a module a user crate is free to write.
        assert_eq!(sysroot_item_for("core", CalleeOwner::Module("raw"), "from_raw_parts"), None);
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Module("converts"), "from_raw_parts"),
            None
        );
        // And the two do not trade declarations.
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Module("slice::raw"), "from_utf8_unchecked"),
            None
        );
    }

    /// W4 (2026-09-25): the value-fact items resolve at their own owner and at no
    /// same-leaf neighbour. `find`/`len`/`starts_with` are among the most common
    /// method names a user crate writes, so the owner half is the whole identity.
    #[test]
    fn w4_value_fact_items_resolve_only_at_their_owner() {
        let str_owner = CalleeOwner::Inherent(SelfTyHead::Str);
        let slice_owner = CalleeOwner::Inherent(SelfTyHead::Slice);
        for (leaf, item) in [
            ("len", SysrootItem::StrLen),
            ("find", SysrootItem::StrFind),
            ("rfind", SysrootItem::StrRfind),
            ("starts_with", SysrootItem::StrStartsWith),
            ("ends_with", SysrootItem::StrEndsWith),
            ("split_at", SysrootItem::StrSplitAt),
            ("split_at_mut", SysrootItem::StrSplitAtMut),
        ] {
            assert_eq!(sysroot_item_for("core", str_owner, leaf), Some(item));
            // A user crate, the `alloc` crate, and a user type's inherent method.
            assert_eq!(sysroot_item_for("mycrate", str_owner, leaf), None);
            assert_eq!(sysroot_item_for("alloc", str_owner, leaf), None);
            assert_eq!(
                sysroot_item_for("core", CalleeOwner::Inherent(SelfTyHead::Adt("Str")), leaf),
                None
            );
            // A TRAIT method of the same leaf (`Iterator::find`, a user trait's
            // `len`) is not the inherent item.
            assert_eq!(
                sysroot_item_for(
                    "core",
                    CalleeOwner::TraitDecl("iter::traits::iterator::Iterator"),
                    leaf
                ),
                None
            );
        }
        assert_eq!(sysroot_item_for("core", slice_owner, "len"), Some(SysrootItem::SliceLen));
        assert_eq!(sysroot_item_for("core", slice_owner, "find"), None);
        // W4 round 3: the SLICE `split_at` is not the str item — its receiver has
        // no char boundaries, and tagging it would refuse `[u8]::split_at`.
        assert_eq!(sysroot_item_for("core", slice_owner, "split_at"), None);
        assert_eq!(sysroot_item_for("core", slice_owner, "split_at_mut"), None);
        let string = CalleeOwner::Inherent(SelfTyHead::Adt("String"));
        let vec = CalleeOwner::Inherent(SelfTyHead::Adt("Vec"));
        assert_eq!(sysroot_item_for("alloc", string, "len"), Some(SysrootItem::StringLen));
        assert_eq!(sysroot_item_for("alloc", vec, "len"), Some(SysrootItem::VecLen));
        assert_eq!(
            sysroot_item_for("alloc", string, "with_capacity"),
            Some(SysrootItem::StringWithCapacity)
        );
        // `VecDeque::with_capacity` / `HashMap::len` are other owners.
        assert_eq!(
            sysroot_item_for("alloc", CalleeOwner::Inherent(SelfTyHead::Adt("VecDeque")), "len"),
            None
        );
        let option = CalleeOwner::Inherent(SelfTyHead::Adt("Option"));
        assert_eq!(sysroot_item_for("core", option, "ok_or"), Some(SysrootItem::OptionOkOr));
        assert_eq!(
            sysroot_item_for("core", option, "ok_or_else"),
            Some(SysrootItem::OptionOkOrElse)
        );
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Inherent(SelfTyHead::Adt("Result")), "ok_or"),
            None
        );
    }

    /// STR_BYTES_POSITION_BOUND: `bytes` only as the core `str` inherent, and
    /// `position` only as the core `Iterator` TRAIT method.
    #[test]
    fn str_bytes_and_iterator_position_are_keyed_exactly() {
        let iterator = CalleeOwner::TraitDecl("iter::traits::iterator::Iterator");
        let str_owner = CalleeOwner::Inherent(SelfTyHead::Str);
        assert_eq!(
            sysroot_item_for("core", iterator, "position"),
            Some(SysrootItem::IteratorPosition)
        );
        assert_eq!(sysroot_item_for("core", str_owner, "bytes"), Some(SysrootItem::StrBytes));
        for krate in ["alloc", "std", "mycrate"] {
            assert_eq!(sysroot_item_for(krate, iterator, "position"), None);
            assert_eq!(sysroot_item_for(krate, str_owner, "bytes"), None);
        }
        assert_eq!(sysroot_item_for("core", CalleeOwner::TraitDecl("Iterator"), "position"), None);
        assert_eq!(
            sysroot_item_for(
                "core",
                CalleeOwner::TraitImpl {
                    trait_name: "Iterator",
                    self_ty: SelfTyHead::Adt("Bytes")
                },
                "position"
            ),
            None
        );
        assert_eq!(sysroot_item_for("core", str_owner, "position"), None);
        assert_eq!(sysroot_item_for("core", iterator, "bytes"), None);
        // `CStr::bytes` and `[u8]`-side owners are not the str inherent.
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Inherent(SelfTyHead::Adt("CStr")), "bytes"),
            None
        );
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Inherent(SelfTyHead::Slice), "bytes"),
            None
        );
        assert_eq!(declared_items_with_leaf("position"), vec![SysrootItem::IteratorPosition]);
        assert_eq!(declared_items_with_leaf("bytes"), vec![SysrootItem::StrBytes]);
        // Widened: the slice `iter` and the `rposition` trait method, and nothing else.
        let slice_owner = CalleeOwner::Inherent(SelfTyHead::Slice);
        assert_eq!(sysroot_item_for("core", slice_owner, "iter"), Some(SysrootItem::SliceIter));
        assert_eq!(sysroot_item_for("core", str_owner, "iter"), None);
        assert_eq!(sysroot_item_for("alloc", slice_owner, "iter"), None);
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Inherent(SelfTyHead::Adt("Vec")), "iter"),
            None
        );
        assert_eq!(
            sysroot_item_for("core", iterator, "rposition"),
            Some(SysrootItem::IteratorRposition)
        );
        assert_eq!(sysroot_item_for("mycrate", iterator, "rposition"), None);
        assert_eq!(declared_items_with_leaf("iter"), vec![SysrootItem::SliceIter]);
        // MEM_REPLACE_SWAP: only the `core::mem` free functions.
        let mem = CalleeOwner::Module("mem");
        assert_eq!(sysroot_item_for("core", mem, "replace"), Some(SysrootItem::MemReplace));
        assert_eq!(sysroot_item_for("core", mem, "swap"), Some(SysrootItem::MemSwap));
        assert_eq!(sysroot_item_for("core", mem, "take"), Some(SysrootItem::MemTake));
        assert_eq!(sysroot_item_for("mycrate", mem, "take"), None);
        assert_eq!(sysroot_item_for("core", CalleeOwner::Module("option"), "take"), None);
        // VEC_CLONE_LEN: only core's `Clone` trait method.
        let clone = CalleeOwner::TraitDecl("clone::Clone");
        assert_eq!(sysroot_item_for("core", clone, "clone"), Some(SysrootItem::CloneClone));
        assert_eq!(sysroot_item_for("mycrate", clone, "clone"), None);
        assert_eq!(sysroot_item_for("core", CalleeOwner::TraitDecl("Clone"), "clone"), None);
        assert_eq!(sysroot_item_for("core", clone, "clone_from"), None);
        // TINV-21: core's inherent `Option::copied` only; never `cloned`, never another
        // crate's or another owner's `copied`.
        let option = CalleeOwner::Inherent(SelfTyHead::Adt("Option"));
        assert_eq!(sysroot_item_for("core", option, "copied"), Some(SysrootItem::OptionCopied));
        assert_eq!(sysroot_item_for("core", option, "cloned"), None);
        assert_eq!(sysroot_item_for("mycrate", option, "copied"), None);
        assert_eq!(sysroot_item_for("alloc", option, "copied"), None);
        let iterator = CalleeOwner::TraitDecl("iter::traits::iterator::Iterator");
        assert_eq!(sysroot_item_for("core", iterator, "copied"), None);
        let result = CalleeOwner::Inherent(SelfTyHead::Adt("Result"));
        assert_eq!(sysroot_item_for("core", result, "copied"), None);
        assert_eq!(declared_items_with_leaf("copied"), vec![SysrootItem::OptionCopied]);
        assert_eq!(sysroot_item_for("mycrate", mem, "replace"), None);
        assert_eq!(sysroot_item_for("core", CalleeOwner::Module("ptr"), "swap"), None);
        assert_eq!(sysroot_item_for("core", slice_owner, "swap"), None);
        assert_eq!(declared_items_with_leaf("rposition"), vec![SysrootItem::IteratorRposition]);
    }

    /// The TRAIT-DECLARATION owner is keyed on the trait's WHOLE path, and it is
    /// a different owner from every impl of that trait.
    #[test]
    fn a_trait_declaration_owner_is_its_whole_path() {
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::TraitDecl("ops::try_trait::Try"), "branch"),
            Some(SysrootItem::TryBranch)
        );
        for decoy in ["Try", "try_trait::Try", "ops::Try", "wrapper::ops::try_trait::Try", ""] {
            assert_eq!(sysroot_item_for("core", CalleeOwner::TraitDecl(decoy), "branch"), None);
        }
        assert_eq!(
            sysroot_item_for("mycrate", CalleeOwner::TraitDecl("ops::try_trait::Try"), "branch"),
            None
        );
        // An IMPL of `Try` (the UFCS-direct spelling) is not the trait method.
        assert_eq!(
            sysroot_item_for(
                "core",
                CalleeOwner::TraitImpl { trait_name: "Try", self_ty: SelfTyHead::Adt("Option") },
                "branch"
            ),
            None
        );
        assert_eq!(sysroot_item_for("core", CalleeOwner::Module("ops::try_trait"), "branch"), None);
    }

    /// An owner the resolver could not classify never matches a declaration.
    #[test]
    fn an_unclassified_owner_fails_closed() {
        assert_eq!(sysroot_item_for("core", CalleeOwner::Other, "read"), None);
        assert_eq!(
            sysroot_item_for("core", CalleeOwner::Inherent(SelfTyHead::Other), "get_unchecked"),
            None
        );
        // A user trait implemented on a sysroot type: the round-5 UFCS refusal,
        // now structural.
        assert_eq!(
            sysroot_item_for(
                "core",
                CalleeOwner::TraitImpl {
                    trait_name: "Sneaky",
                    self_ty: SelfTyHead::Adt("NonZero")
                },
                "read"
            ),
            None
        );
    }

    /// `is_one_of` is the funnel, and its `None` arm is the fail-closed rule.
    #[test]
    fn a_key_with_no_item_matches_nothing() {
        let key = CalleeKey {
            sysroot_item: None,
            krate_is_real_sysroot: false,
            krate_name_is_ambiguous: false,
            stable_crate_id: 0xdead_beef,
            krate_name: "core".to_string(),
            foreign_block_leaf: None,
            upstream_foreign_link_symbol: None,
            diverging_entry: None,
        };
        assert!(!key.is_one_of(&[SysrootItem::PtrRead, SysrootItem::VecSetLen]));
        assert!(!CalleeKey::opt_is_one_of(None, &[SysrootItem::PtrRead]));
        assert!(!CalleeKey::opt_is_one_of(Some(&key), &[SysrootItem::PtrRead]));
    }

    /// A key with no sysroot item and the given residency verdict.
    fn residency_key(krate_name: &str, krate_is_real_sysroot: bool) -> CalleeKey {
        CalleeKey {
            sysroot_item: None,
            krate_is_real_sysroot,
            krate_name_is_ambiguous: false,
            stable_crate_id: 0x5eed,
            krate_name: krate_name.to_string(),
            foreign_block_leaf: None,
            upstream_foreign_link_symbol: None,
            diverging_entry: None,
        }
    }

    /// SYSROOT-ANCHOR-1: residency is read from the key alone. A user crate
    /// that calls itself `core` is still `false`, and an absent key is `false`.
    #[test]
    fn opt_is_real_sysroot_reads_residency_and_fails_closed_on_none() {
        assert!(!CalleeKey::opt_is_real_sysroot(None));
        assert!(!CalleeKey::opt_is_real_sysroot(Some(&residency_key("core", false))));
        assert!(!CalleeKey::opt_is_real_sysroot(Some(&residency_key("dep", false))));
        assert!(CalleeKey::opt_is_real_sysroot(Some(&residency_key("core", true))));
    }

    /// DIVERGE-ENTRY-1: the diverging-entry class is read from the extractor's
    /// stamp, and residency alone is not one. A real `core` key WITHOUT the stamp
    /// is what a call to a core TRAIT method carries (`From::from`, `Default::default`,
    /// `Into::into`) while a dependency's impl body runs; it must answer `None`. A
    /// stamp on a non-sysroot key (never minted) answers `None` too.
    #[test]
    fn opt_diverging_entry_needs_the_stamp_and_residency() {
        assert_eq!(CalleeKey::opt_diverging_entry(None), None);
        assert_eq!(CalleeKey::opt_diverging_entry(Some(&residency_key("core", true))), None);
        for entry in [DivergingEntry::PanicOrAbort, DivergingEntry::UbIfReached] {
            let stamped = CalleeKey { diverging_entry: Some(entry), ..residency_key("core", true) };
            assert_eq!(CalleeKey::opt_diverging_entry(Some(&stamped)), Some(entry));
            let forged = CalleeKey { diverging_entry: Some(entry), ..residency_key("core", false) };
            assert_eq!(CalleeKey::opt_diverging_entry(Some(&forged)), None);
            let user = CalleeKey { diverging_entry: Some(entry), ..residency_key("dep", false) };
            assert_eq!(CalleeKey::opt_diverging_entry(Some(&user)), None);
        }
    }

    /// DIVERGE-ENTRY-1: a key serialized before the field existed (a frozen dump,
    /// a cached bundle) reads back with NO class, so it can never select the
    /// diverging-site encoding; and an unstamped key serializes exactly as before.
    #[test]
    fn diverging_entry_is_absent_from_old_and_unstamped_keys() {
        let old = r#"{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":1,"krate_name":"core"}"#;
        let key: CalleeKey = serde_json::from_str(old).expect("an old key deserializes");
        assert_eq!(key.diverging_entry, None);
        assert_eq!(CalleeKey::opt_diverging_entry(Some(&key)), None);
        assert_eq!(serde_json::to_string(&key).unwrap(), old);
        let stamped = CalleeKey { diverging_entry: Some(DivergingEntry::UbIfReached), ..key };
        let encoded = serde_json::to_string(&stamped).unwrap();
        assert!(encoded.contains(r#""diverging_entry":"UbIfReached""#), "{encoded}");
        assert_eq!(serde_json::from_str::<CalleeKey>(&encoded).unwrap(), stamped);
    }

    const F64_PATHS: &[&str] = &["core::f64::<impl f64>::sin", "std::f64::<impl f64>::sin"];

    /// The key gate comes first: neither a missing key nor a non-sysroot key
    /// reaches the string, even when the string is exactly an entry.
    #[test]
    fn sysroot_exact_path_refuses_a_missing_or_non_sysroot_key() {
        let exact = "core::f64::<impl f64>::sin";
        assert_eq!(sysroot_exact_path(None, exact, F64_PATHS), None);
        let forged = residency_key("core", false);
        assert_eq!(sysroot_exact_path(Some(&forged), exact, F64_PATHS), None);
        let user = residency_key("dep", false);
        assert_eq!(sysroot_exact_path(Some(&user), exact, F64_PATHS), None);
    }

    #[test]
    fn sysroot_exact_path_matches_the_exact_entry_and_not_a_longer_leaf() {
        let core = residency_key("core", true);
        let std = residency_key("std", true);
        assert_eq!(
            sysroot_exact_path(Some(&core), "core::f64::<impl f64>::sin", F64_PATHS),
            Some("core::f64::<impl f64>::sin")
        );
        assert_eq!(
            sysroot_exact_path(Some(&std), "std::f64::<impl f64>::sin", F64_PATHS),
            Some("std::f64::<impl f64>::sin")
        );
        for other in [
            "core::f64::<impl f64>::sin_x",
            "core::f64::<impl f64>::sinh",
            "core::f64::<impl f64>::si",
            "core::f64::<impl f64>::cos",
            "core::f32::<impl f32>::sin",
            "xcore::f64::<impl f64>::sin",
            "__trust_crate@1::core::f64::<impl f64>::sin",
            "",
        ] {
            assert_eq!(sysroot_exact_path(Some(&core), other, F64_PATHS), None, "{other}");
        }
    }

    /// The S-F64METHOD spoof: a REAL core callee whose rendering carries a user
    /// type spelling `f64::cos` in its generic arguments. Only a prefix of the
    /// whole rendering counts, so it matches nothing.
    #[test]
    fn sysroot_exact_path_refuses_the_generic_argument_spoof() {
        let core = residency_key("core", true);
        let spoof = "core::cmp::max_by_key::<f64, {closure@m.rs:3:30}, \
                     core::marker::PhantomData<m::f64::cos<1>>>";
        let cos = &["core::f64::<impl f64>::cos", "std::f64::<impl f64>::cos"];
        assert_eq!(sysroot_exact_path(Some(&core), spoof, cos), None);
        // And a path that merely ENDS with an entry is not that entry.
        let suffix = "core::cmp::max_by_key::<f64, m::core::f64::<impl f64>::cos>";
        assert_eq!(sysroot_exact_path(Some(&core), suffix, cos), None);
    }

    /// One trailing `::<…>` group is accepted; a turbofish anywhere else, or
    /// followed by more path, is not.
    #[test]
    fn sysroot_exact_path_accepts_a_turbofish_only_at_the_end() {
        let core = residency_key("core", true);
        let paths = &["core::mem::size_of"];
        assert_eq!(
            sysroot_exact_path(Some(&core), "core::mem::size_of::<u32>", paths),
            Some("core::mem::size_of")
        );
        assert_eq!(
            sysroot_exact_path(
                Some(&core),
                "core::mem::size_of::<__trust_args@00000000000000010000000000000023>",
                paths
            ),
            Some("core::mem::size_of")
        );
        for other in [
            "core::mem::size_of::<u32>::extra",
            "core::mem::size_of<u32>",
            "core::mem::size_of::",
            "core::mem::size_of::<",
            "core::mem::size_of_val::<u32>",
            "core::mem::size_of::x",
        ] {
            assert_eq!(sysroot_exact_path(Some(&core), other, paths), None, "{other}");
        }
    }
}

/// The totality witness for [`SysrootItem`] — every variant, written out.
///
/// Public because the RECOGNIZER GUARD in `trust-vcgen` enumerates the
/// vocabulary to assert that every MINTING recognizer refuses every tag it does
/// not name, which is the structured replacement for the old "user-crate
/// rebuild" spelling refutation.
pub const ALL_SYSROOT_ITEMS: &[SysrootItem] = &[
    SysrootItem::PtrRead,
    SysrootItem::PtrReadVolatile,
    SysrootItem::PtrReadUnaligned,
    SysrootItem::PtrWrite,
    SysrootItem::PtrWriteVolatile,
    SysrootItem::PtrWriteUnaligned,
    SysrootItem::PtrCopy,
    SysrootItem::PtrCopyNonOverlapping,
    SysrootItem::PtrDropInPlace,
    SysrootItem::RawPtrDropInPlace,
    SysrootItem::AllocDealloc,
    SysrootItem::AllocRealloc,
    SysrootItem::AllocAlloc,
    SysrootItem::AllocAllocZeroed,
    SysrootItem::GlobalAllocatorAllocate,
    SysrootItem::GlobalAllocatorDeallocate,
    SysrootItem::SliceGetUnchecked,
    SysrootItem::SliceGetUncheckedMut,
    SysrootItem::StrGetUnchecked,
    SysrootItem::StrGetUncheckedMut,
    SysrootItem::SliceFromRawParts,
    SysrootItem::SliceFromRawPartsMut,
    SysrootItem::StrFromRawParts,
    SysrootItem::StrFromRawPartsMut,
    SysrootItem::VecFromRawParts,
    SysrootItem::StringFromRawParts,
    SysrootItem::VecSetLen,
    SysrootItem::VecWithCapacity,
    SysrootItem::VecWithCapacityIn,
    SysrootItem::VecReserve,
    SysrootItem::VecReserveExact,
    SysrootItem::VecResize,
    SysrootItem::VecResizeWith,
    SysrootItem::VecFromElem,
    SysrootItem::NonZeroNewUnchecked,
    SysrootItem::NonNullNewUnchecked,
    SysrootItem::UniqueNewUnchecked,
    SysrootItem::CharFromU32Unchecked,
    SysrootItem::CharMethodsFromU32Unchecked,
    SysrootItem::StrFromUtf8Unchecked,
    SysrootItem::StrFromUtf8UncheckedMut,
    SysrootItem::StringFromUtf8Unchecked,
    SysrootItem::CStrFromBytesWithNulUnchecked,
    SysrootItem::MaybeUninitAssumeInit,
    SysrootItem::MaybeUninitAssumeInitRef,
    SysrootItem::MaybeUninitAssumeInitMut,
    SysrootItem::MaybeUninitAssumeInitRead,
    SysrootItem::MaybeUninitAssumeInitDrop,
    SysrootItem::BoxAssumeInit,
    SysrootItem::BoxAssumeInitIntoVecUnsafe,
    SysrootItem::OptionUnwrapUnchecked,
    SysrootItem::ResultUnwrapUnchecked,
    SysrootItem::OptionUnwrap,
    SysrootItem::OptionExpect,
    SysrootItem::ResultUnwrap,
    SysrootItem::ResultExpect,
    SysrootItem::MemTransmute,
    SysrootItem::MemTransmuteCopy,
    SysrootItem::MemZeroed,
    SysrootItem::MemUninitialized,
    SysrootItem::HintUnreachableUnchecked,
    SysrootItem::LayoutFromSizeAlign,
    SysrootItem::LayoutFromSizeAlignUnchecked,
    SysrootItem::ConstPtrAdd,
    SysrootItem::ConstPtrOffset,
    SysrootItem::ConstPtrWrappingAdd,
    SysrootItem::ConstPtrWrappingOffset,
    SysrootItem::MutPtrAdd,
    SysrootItem::MutPtrOffset,
    SysrootItem::MutPtrWrappingAdd,
    SysrootItem::MutPtrWrappingOffset,
    SysrootItem::ConstPtrCast,
    SysrootItem::ConstPtrCastMut,
    SysrootItem::MutPtrCast,
    SysrootItem::MutPtrCastConst,
    SysrootItem::SliceAsPtr,
    SysrootItem::SliceAsMutPtr,
    SysrootItem::VecAsPtr,
    SysrootItem::VecAsMutPtr,
    SysrootItem::StringAsPtr,
    SysrootItem::StrAsPtr,
    SysrootItem::StrAsMutPtr,
    SysrootItem::MaybeUninitAsPtr,
    SysrootItem::MaybeUninitAsMutPtr,
    SysrootItem::NonNullAsPtr,
    SysrootItem::NonNullAsMutPtr,
    SysrootItem::UniqueAsPtr,
    SysrootItem::CStrAsPtr,
    SysrootItem::CellAsPtr,
    SysrootItem::RefCellAsPtr,
    SysrootItem::BoxAsPtr,
    SysrootItem::BoxAsMutPtr,
    SysrootItem::RawSlicePtrAsPtr,
    SysrootItem::RawSlicePtrAsMutPtr,
    SysrootItem::RcAsPtr,
    SysrootItem::ArcAsPtr,
    SysrootItem::WeakAsPtr,
    SysrootItem::AtomicAsPtr,
    SysrootItem::SliceAssumeInitRef,
    SysrootItem::BoxNew,
    SysrootItem::BoxNewUninit,
    SysrootItem::StrLen,
    SysrootItem::SliceLen,
    SysrootItem::StringLen,
    SysrootItem::VecLen,
    SysrootItem::StringWithCapacity,
    SysrootItem::StrFind,
    SysrootItem::StrRfind,
    SysrootItem::StrStartsWith,
    SysrootItem::StrEndsWith,
    SysrootItem::OptionOkOr,
    SysrootItem::OptionOkOrElse,
    SysrootItem::TryBranch,
    SysrootItem::StrSplitAt,
    SysrootItem::StrSplitAtMut,
    SysrootItem::BTreeMapRange,
    SysrootItem::BTreeMapRangeMut,
    SysrootItem::BTreeSetRange,
    SysrootItem::CharToLowercase,
    SysrootItem::CharToUppercase,
    SysrootItem::StrBytes,
    SysrootItem::IteratorPosition,
    SysrootItem::SliceIter,
    SysrootItem::IteratorRposition,
    SysrootItem::MemReplace,
    SysrootItem::MemSwap,
    SysrootItem::MemTake,
    SysrootItem::CloneClone,
    SysrootItem::OptionCopied,
    SysrootItem::ThreadSpawn,
    SysrootItem::ThreadBuilderSpawn,
    SysrootItem::ThreadBuilderSpawnUnchecked,
    SysrootItem::ThreadBuilderSpawnScoped,
    SysrootItem::ThreadScopeSpawn,
];
