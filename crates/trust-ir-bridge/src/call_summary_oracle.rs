// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # Bridge call-summary soundness + completeness oracle (rung-1 frontier)
//!
//! `total_no_panic_call_summary` decides which callees the bridge may lower to an
//! obligation-free `Inst::Undef` (treated as cannot-panic) instead of a real, may-panic
//! `Inst::Call`. Mis-including a callee that CAN panic is the exact false-proof class of
//! the 2026-06-19 sweep (HOLE-6C: a user type ending in a total suffix; hunt-9:
//! `saturating_div` still panics on div-by-zero). This is the bridge-domain analogue of
//! the trust-mc program-space oracle: it pins that soundness-critical string decision
//! against curated GROUND-TRUTH std semantics, in two directions:
//!
//!   * SOUNDNESS — every genuinely-panicking / user-code-dispatching callee, and every
//!     adversarial user type that merely *ends* in a total suffix, MUST be classified
//!     not-total. A regression that flips one to total is a false-proof; this test fails.
//!   * COMPLETENESS — of the genuinely-total std callees, how many does the allowlist
//!     recognize? Unrecognized totals are precision lost to conservatism — rung-1's
//!     target. Reported (not failed): it quantifies the bridge precision gap.

use crate::lower::{is_element_free_total_std_type, total_no_panic_call_summary};

/// Callees that GENUINELY PANIC or dispatch into user code (Hash/Eq/Ord/Display/Drop or
/// a closure) — every one MUST be classified not-total. Strings are realistic
/// monomorphized def-paths (the decision strips `<…>` generics, then anchors on
/// core/alloc/std and suffix-matches).
const PANICKING: &[&str] = &[
    "core::option::Option::<u32>::unwrap",     // panics on None
    "core::option::Option::<u32>::expect",     // panics on None
    "core::result::Result::<u32, ()>::unwrap", // panics on Err
    "core::result::Result::<u32, ()>::expect", // panics on Err
    "alloc::vec::Vec::<u32>::remove",          // panics on OOB index
    "alloc::vec::Vec::<u32>::insert",          // panics on OOB index
    "alloc::vec::Vec::<u32>::swap_remove",     // panics on OOB index
    // `push` is NOT total: growing the vector calls `RawVec::grow_one`, whose
    // capacity computation ends in `raw_vec::capacity_overflow()` — a real
    // `panic!`, documented by std as "Panics if the new capacity exceeds
    // `isize::MAX` bytes". It sat in SHOULD_BE_TOTAL, which asserts "cannot
    // panic", so the oracle was demanding a summary that would have been FALSE.
    // The element type does not rescue it: the overflow path is in the
    // allocator, not in element code, so the primitive spelling panics too.
    "alloc::vec::Vec::<u32>::push", // capacity overflow -> capacity_overflow()
    "<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index", // Vec[i] OOB panic
    "<[u32] as core::ops::index::Index<usize>>::index", // slice[i] OOB panic
    "core::option::Option::<u32>::map", // runs a user closure
    "core::option::Option::<u32>::unwrap_or_else", // runs a user closure
    "alloc::string::ToString::to_string", // dispatches to Display::fmt (user)
    "std::collections::hash::map::HashMap::<u32, u32>::get", // Hash+Eq on key (user)
    // `<[T]>::contains` is total or not DEPENDING ON THE ELEMENT TYPE, so the pin has
    // to name a USER element — the same convention this list already uses for
    // `Vec::<ElemT>::dedup` ("PartialEq on elements (user)") and
    // `BTreeMap::<UserOrdK, u32>::get` ("Ord on the KEY").
    //
    // CORRECTED 2026-08-20: this entry used to be spelled `<impl [u32]>` while giving
    // "Eq on elements (user)" as its reason. For a PRIMITIVE element the reason does
    // not hold — `PartialEq for u32` is core's built-in and coherence forbids a user
    // impl, so `<[u32]>::contains` runs no user code at all (its `SliceContains`
    // impls in `library/core/src/slice/cmp.rs` are memchr / a constant-lane
    // `chunks_exact` SIMD scan / `iter().any`, none of which panics). The entry was
    // pinning the right HAZARD with the wrong WITNESS. It now names a user element,
    // and the primitive spelling is pinned in the opposite direction in
    // SHOULD_BE_TOTAL below — so the oracle constrains BOTH sides of the element
    // distinction instead of only forbidding the union.
    "core::slice::<impl [ElemT]>::contains", // Eq on elements (user)
    "core::slice::<impl [mycrate::Widget]>::contains", // ditto, spelled-out user path
    "core::num::<impl i32>::saturating_div", // hunt-9: still panics on div-by-zero
    "core::num::<impl i32>::saturating_rem", // hunt-9: still panics on rem-by-zero
    "core::num::<impl i32>::wrapping_div",   // wraps only MIN/-1; panics on div-by-zero
    "core::num::<impl i32>::wrapping_rem",   // wraps only MIN/-1; panics on rem-by-zero
    "core::num::<impl i64>::wrapping_div_euclid", // euclid twin: same zero-divisor panic
    "core::num::<impl i32>::overflowing_div", // (val, bool) pair; panics on div-by-zero
    "core::num::<impl i32>::overflowing_rem", // (val, bool) pair; panics on rem-by-zero
    // SUBTLE traps (the class that makes rung-1 recovery dangerous — encoded as guards so a
    // future "obviously total" addition that overlooks them is caught):
    "core::result::Result::<u32, ErrT>::unwrap_or", // consumes self; DROPS the Err payload
    // (a user Drop can panic) — unlike
    // Option::unwrap_or, whose None has no payload.
    "core::mem::take::<MyT>", // dispatches to Default::default() (user)
    "alloc::vec::Vec::<ElemT>::truncate", // DROPS removed elements (user Drop)
    "alloc::vec::Vec::<ElemT>::dedup", // PartialEq on elements (user)
    "alloc::vec::Vec::<ElemT>::retain", // runs a user closure
    "core::option::Option::<MyT>::map_or", // runs a user closure
    "core::option::Option::<MyT>::get_or_insert_with", // runs a user closure
    // NEAR-NEIGHBOR pins for the T3 aterm-scrollback totals (`Vec::shrink_to_fit` /
    // `BTreeMap::iter` / `MaybeUninit::new` / `RangeInclusive::new`): the closest
    // sibling of each new entry that must NOT ride it. Flipping any of these to
    // total is the regression this oracle exists to catch.
    "alloc::vec::Vec::<u32>::shrink_to", // DELIBERATE pin: the PARAMETERIZED
    // shrink sibling is kept unmodeled/
    // fail-closed — the exact `_fit`
    // suffix must never widen to it
    "alloc::collections::btree::map::BTreeMap::<UserOrdK, u32>::get", // Ord on the KEY
    // (user code can panic) — the keyed
    // lookup the iter-ctor entry must
    // never be confused with
    "core::mem::maybe_uninit::MaybeUninit::<u32>::assume_init", // the UNWRAP direction:
    // init-validity is the unsafe
    // caller's obligation (and
    // assert_inhabited panics for
    // uninhabited T); a total summary
    // would silently drop it
    // ==================================================================
    // CALLER-SUPPLIED-DISPATCH (FRONT B, R13). Every entry below used to sit in
    // `SHOULD_BE_TOTAL` — i.e. this oracle's own GROUND TRUTH asserted they were
    // "genuinely total (no user code, cannot panic)" and the completeness test
    // printed them as "precision GAPS — rung-1 target", which is a written
    // instruction to re-grant them. Three of the four had ALREADY been retired as
    // false proofs (`4178c86097`) and are pinned must-fail-closed in
    // `lower.rs::callbacks_traits_growth_and_broad_families_fail_closed`, so the
    // two lists in this crate directly contradicted each other. They are moved
    // here, where the SOUNDNESS test makes a re-grant a hard failure.
    //
    // Each is backed by an EXECUTED panic witness (deployed driver
    // sha256:18e5a9a90a1697f6, `-Z trust-policy=advisory`), with an isolating
    // control that does NOT panic on the same call shape:
    //
    //   K1-a  Vec::<u8, PanicAlloc>::push            -> PANICKED
    //   K2-a  Vec::<u8, Global>::push                -> no panic
    //   K1-b  Vec::<u8, ShrinkPanicAlloc>::shrink_to_fit (len 1 < cap 64) -> PANICKED
    //   K2-b  same allocator, push only (no shrink)  -> no panic
    //   K2-b' Vec::<u8, Global>::shrink_to_fit       -> no panic
    //   K1-c  <Y as From<X>>::from with a panicking user impl -> PANICKED
    //   K2-c  u32::from(7u8)                         -> no panic
    //   K1-d  X.into() through the same user impl    -> PANICKED
    //   K1-e  CELL.try_with(|_| panic!())            -> PANICKED
    //   K2-e  CELL.try_with(|c| c.get())             -> no panic
    "alloc::vec::Vec::<u8, my_crate::MyAlloc>::push", // `Vec<T, A>` is generic over
    // `A: Allocator`; the growth path calls
    // `A::allocate`, which is CALLER-SELECTED
    // user code. `strip_generics` erases `A`,
    // so a summary keyed on the rendered path
    // cannot tell the two apart. Retired in
    // `4178c86097` with a measured false proof.
    "alloc::vec::Vec::<u32>::push", // the exact spelling this oracle used to assert TOTAL
    "alloc::vec::Vec::<u32>::shrink_to_fit", // SAME allocator-generic defect as `push`, one
    // step further along: `shrink_to_fit` calls
    // `A::shrink`. The old justification here
    // ("realloc-shrink with no element drops") is
    // true about DROPS and silent about the
    // allocator. K1-b isolates it: delegate
    // `allocate` to `Global` and panic only in
    // `shrink`, and the panic still fires.
    "core::convert::From::from", // `From` is an ORDINARY user-implementable trait.
    // `impl From<X> for Y { fn from(_) -> Y { panic!() } }`
    // is safe, stable code. "Infallible conversion" is a
    // CONVENTION, not a guarantee — `TryFrom` is about the
    // RESULT TYPE, not about panic-freedom. A `From::from`
    // total grant discharges every `.into()` in the crate.
    "core::convert::Into::into", // the blanket `impl<T, U: From<T>> Into<U> for T` forwards
    // to exactly the `From::from` above, so it inherits the
    // whole defect and is reachable from bare `.into()`.
    "std::thread::local::LocalKey::<core::cell::Cell<u32>>::try_with::<{closure@a.rs:1:1}, u32>",
    // `LocalKey::try_with` RUNS THE CALLER'S CLOSURE. Its `Result` return
    // totalizes only the TLS-access failure (destroyed thread-local), never the
    // closure body. Retired as a false proof in an earlier Front B round (see the
    // long note at `lower.rs`'s `total_no_panic_call_summary`, which records
    // `S4::c_try_with -> 1 PROVED` for `CELL.try_with(|_| panic!()).unwrap_or(0)`).
    // Pinned here because R13's brief named `rational::{ensure_healthy,poisoned,val}`
    // — 37 of the 160 ny-cert absent-callee rows — as a "registry coverage" target,
    // and the single callee that would clear all 37 at once is this one.
    "std::thread::local::LocalKey::<core::cell::Cell<u32>>::with::<{closure@a.rs:1:1}, u32>",
    // the sibling: `with` ALSO runs the closure AND panics itself
    // (`panic_access_error`) when the thread-local is touched during its own
    // destruction. Strictly worse than `try_with`; kept adjacent so a widening
    // that reasons "the `Result` return makes it total" cannot reach either.
    "std::sys::thread_local::native::lazy::Storage::<core::cell::Cell<u32>, ()>::get_or_init::<fn() -> core::cell::Cell<u32> {P13B::LAZYX::__rust_std_internal_init_fn}>",
    // FALSE PROOF #13 (R13 integrator) — the INNER half of the same TLS access that
    // `try_with`/`with` above are the OUTER half of. The native-TLS lazy `Storage`
    // state machine has no panic path of its own, but it DRIVES the `thread_local!`
    // initializer, and that initializer expression is USER-WRITTEN. The retired grant
    // argued the init fn `__rust_std_internal_init_fn` "carries its OWN obligation, so
    // a panicking initializer is REFUTED there, never masked here" — the identical
    // argument `lower.rs` rejects for `try_with` forty lines later. MEASURED on
    // sha256:a6fff08aa20b2f23: with `Cell::new(panic!("boom"))` as the initializer,
    // `__rust_std_internal_init_fn` is FAILED while its sole caller
    // `LAZYX::{constant#0}::{closure#0}` is PROVED 1/1. Pinned here so any future
    // "the state machine cannot panic" widening is a hard test failure.
    // The const-init (eager) sibling `native::eager::Storage::get` drives no callable
    // and is NOT pinned — it is a legitimate future completeness target.
];

/// Adversarial USER types whose path merely ENDS in a genuine total suffix — the HOLE-6C
/// / Attack-5 false-proof shape. None start with core/alloc/std, so all MUST be not-total.
const ADVERSARIAL: &[&str] = &[
    "mycrate::vec::Vec::<u32>::new", // ends in ::Vec::new but is a USER Vec
    "myapp::text::str::find",        // ends in ::str::find but is a USER str
    "userlib::Option::<u32>::is_some", // ends in ::Option::is_some but USER
    "company::collections::String::len", // ends in ::String::len but USER
    "mycrate::slice::first_mut",     // ends in ::slice::first_mut but USER (anchor must reject)
    "userlib::Vec::<u32>::as_mut_slice", // ends in ::Vec::as_mut_slice but USER
    "company::collections::String::from_utf16_lossy", // ends in the new total suffix but USER
    // The T3 aterm-scrollback additions' user-path twins (crate-origin anchor must
    // reject every one — HOLE-6C shape):
    "mycrate::vec::Vec::<u32>::shrink_to_fit", // USER Vec ending in the new suffix
    "mycrate::collections::BTreeMap::<String, u32>::iter", // USER BTreeMap
    "userlib::mem::MaybeUninit::<u32>::new",   // USER MaybeUninit
    "company::ops::RangeInclusive::<usize>::new", // USER RangeInclusive
];

/// GENUINELY-TOTAL std callees (no user code, cannot panic). Recognition rate = the
/// bridge's call-summary COMPLETENESS. Entries marked `// GAP` are total but currently
/// unrecognized — the precision rung-1 must reclaim.
///
/// FRONT B (R13) — THIS LIST IS AN ASSERTION, NOT A WISHLIST. Every entry claims the
/// callee cannot panic on ANY input, and `call_summary_oracle_completeness` prints the
/// unrecognized ones as "rung-1 targets", which reads as an authorization to grant
/// them. Four entries were WRONG and are now pinned in `PANICKING` with executed
/// witnesses (`Vec::push`, `Vec::shrink_to_fit`, `From::from`, `Into::into`); three of
/// the four had already been retired as measured false proofs in `4178c86097` and were
/// simultaneously pinned must-fail-closed in `lower.rs`, so this file was contradicting
/// its own crate. A printed GAP is a hypothesis to audit, never a decision.
const SHOULD_BE_TOTAL: &[&str] = &[
    "alloc::vec::Vec::<u32>::new",
    // MERGE (b62 <- origin/main): BOTH sides independently derived that `Vec::push`
    // is not total. Upstream's eae43893f9 ("Vec::push is not total — it panics on
    // capacity overflow") deleted the entry; our FRONT B / R13 moved it to PANICKING
    // with an executed witness. The resulting TOTAL list is identical either way; only
    // this tombstone differs, and it is kept because it names where the entry went.
    // `Vec::push` REMOVED (FRONT B, R13) — it is in `PANICKING` now. See the
    // caller-supplied-dispatch block there for the executed witness.
    "alloc::vec::Vec::<u32>::len",
    "alloc::vec::Vec::<u32>::is_empty",
    "alloc::vec::Vec::<u32>::capacity",
    "core::str::<impl str>::len",
    "core::str::<impl str>::is_empty",
    "core::str::<impl str>::find",
    "core::option::Option::<u32>::is_some",
    "core::option::Option::<u32>::is_none",
    "core::slice::<impl [u32]>::get",
    "core::slice::<impl [u32]>::len",
    // B2 (2026-08-20): `<[PRIM]>::contains`. One call to `cmp::SliceContains::
    // slice_contains`, whose impls for primitives are memchr (`u8`/`i8`), a
    // constant-lane `chunks_exact` SIMD scan, or `iter().any` — all over the BUILT-IN
    // `PartialEq`, which coherence forbids a user crate from replacing. No user code,
    // no allocation, no panic path. Its USER-element twin is pinned in PANICKING
    // above, so this pair is what keeps the element distinction honest in both
    // directions.
    "core::slice::<impl [u32]>::contains",
    "core::slice::<impl [i32]>::contains",
    "core::slice::<impl [u8]>::contains",
    "core::slice::<impl [char]>::contains",
    // B3 (2026-08-20): `BufReader::new` — `Box::new_uninit_slice(DEFAULT_BUF_SIZE)`
    // plus two struct constructions; `R` is only moved. Constant-size raw uninit
    // allocation, so no layout arithmetic and no user code. The CALLER-SUPPLIED
    // `with_capacity` sibling is deliberately not here and is pinned as a near-miss
    // in the bridge's own fail-closed test.
    "std::io::buffered::bufreader::BufReader::<std::fs::File>::new",
    "alloc::string::String::new",
    "alloc::string::String::len",
    // rung-1 recovery: the UTF-16 total pair. `str::encode_utf16` is a lazy iterator
    // factory (&self-only, no alloc, no user code); `String::from_utf16_lossy` decodes
    // `&[u16]` replacing ill-formed units with U+FFFD (no user code, no closure, never
    // panics — OOM excluded). Both abort whole-function lowering when unrecognized.
    "core::str::<impl str>::encode_utf16",
    "alloc::string::String::from_utf16_lossy",
    // GAP candidates — genuinely total (return Option, move out, run NO user code and
    // NO element Drop, cannot panic), currently NOT in the allowlist. The precision
    // rung-1 reclaims by adding them.
    //
    // FRONT B (R13) — READ THIS BEFORE RECLAIMING ANY GAP. A `// GAP` line here is a
    // claim that the callee is total on ALL inputs, and the completeness test prints
    // every unrecognized entry as a "rung-1 target". Four entries were removed from
    // this list in R13 because the claim was FALSE (`Vec::push`, `Vec::shrink_to_fit`,
    // `From::from`, `Into::into` — all caller-supplied dispatch, all now pinned in
    // `PANICKING` with executed witnesses). The test's output is a suggestion, not an
    // authorization: before adding any entry, check that no `A: Allocator`, no user
    // trait impl, no closure, and no `Pattern`/`Hash`/`Ord`/`Drop` of a caller-chosen
    // type is reachable from the body.
    "alloc::vec::Vec::<u32>::pop",
    "alloc::string::String::pop",
    // rung-1 recovery: the `&mut` structural-accessor twins of already-recognized total
    // accessors (`first`/`last`/`get_mut`/`as_slice`). Bounds-checked, return Option<&mut T> /
    // &mut [T], run NO element user code, cannot panic — same soundness class as their `&` twins.
    "core::slice::<impl [u32]>::first_mut",
    "core::slice::<impl [u32]>::last_mut",
    "alloc::vec::Vec::<u32>::as_mut_slice",
    // rung-1 recovery: the integer endian/bit-twiddling family (`core::num` inherent
    // const fns). Copy scalar operands by value, no user code, no Drop, panic-free
    // (fixed-length byte arrays => no bounds check; rotate shift masked mod BITS;
    // is_multiple_of is the panic-free divisibility predicate). Same soundness class
    // as the recognized checked_*/saturating_* arithmetic.
    // The wrapping_/overflowing_ non-division families: defined wraparound on
    // Copy scalars (or the `(value, overflowed)` pair), no user code, no panic
    // — the checked_/saturating_ soundness class. The DIVISION members are in
    // PANICKING above (zero divisor still panics).
    // Inherent saturating/checked add/sub/mul: total by clamp / Option-return;
    // div/rem stay in PANICKING (zero-divisor panic).
    "core::num::<impl usize>::saturating_add",
    "core::num::<impl i64>::saturating_sub",
    "core::num::<impl u32>::saturating_mul",
    "core::num::<impl usize>::checked_add",
    "core::num::<impl i128>::checked_sub",
    "core::num::<impl i128>::checked_mul",
    // checked div/rem/pow/neg — TOTAL by Option-return (None on zero divisor / overflow
    // / MIN), the non-panicking twins of the PANICKING plain div/rem. Recognized via the
    // `core::num::checked_{div,rem,pow,neg}` EXACT_TOTAL entries.
    "core::num::<impl usize>::checked_div",
    "core::num::<impl u128>::checked_rem",
    "core::num::<impl i128>::checked_pow",
    "core::num::<impl i128>::checked_neg",
    "core::num::<impl i128>::wrapping_neg",
    // FRONT B (R13) — the `wrapping_*` entries below are GENUINELY TOTAL (the claim
    // is correct) but they are NOT a completeness gap to close in this list, and
    // `lower.rs` pins `core::num::<impl u64>::wrapping_add` must-fail-closed on
    // purpose. Reason: `translate_chc`'s `wrapping_arith_binop` arm models these
    // PRECISELY (an exact modular value), and the extractor stamps the u8/u16/u32/u64
    // add/sub/mul trio with the tcx-authenticated
    // `@trust-rustc-total-primitive-method::` marker
    // (`trust-mir-extract::tcx_marked_unsigned_wrapping_primitive_path`: crate-of-
    // `Sized`-lang-item + inherent primitive impl + exact `(U,U) -> U` signature), so
    // the bridge lowers `a.wrapping_add(1)` to a `BinOp Add` with
    // `proofs: ["Wrapping"]` and emits NO call at all. MEASURED on driver
    // sha256:18e5a9a90a1697f6 with `-Z trust-dump=native-bundle`. Moving them into the
    // flat summary would REPLACE that exact value with an unconstrained `Undef` —
    // a precision LOSS wearing a completeness-gain label. They stay listed here only
    // as ground truth about their totality.
    "core::num::<impl u32>::wrapping_add",
    "core::num::<impl u64>::wrapping_sub",
    "core::num::<impl i64>::wrapping_mul",
    "core::num::<impl u32>::wrapping_shl",
    // wrapping shift — TOTAL: masks the shift amount mod BITS (never a wide-shift panic).
    "core::num::<impl u64>::wrapping_shr",
    "core::num::<impl i32>::overflowing_add",
    "core::num::<impl u64>::overflowing_mul",
    "core::num::<impl u32>::from_le_bytes",
    "core::num::<impl u32>::from_be_bytes",
    "core::num::<impl u32>::from_ne_bytes",
    "core::num::<impl u32>::to_le_bytes",
    "core::num::<impl u32>::to_be_bytes",
    "core::num::<impl u32>::to_ne_bytes",
    "core::num::<impl u32>::to_le",
    "core::num::<impl u32>::to_be",
    "core::num::<impl u32>::to_ne",
    "core::num::<impl u32>::trailing_zeros",
    "core::num::<impl u32>::leading_zeros",
    "core::num::<impl u32>::count_ones",
    "core::num::<impl u64>::rotate_left",
    "core::num::<impl u64>::rotate_right",
    "core::num::<impl u32>::swap_bytes",
    "core::num::<impl usize>::is_multiple_of",
    // `core::convert::From::from` / `Into::into` REMOVED (FRONT B, R13). The old
    // rationale — "TOTAL by the `From`/`Into` contract (fallible conversion is
    // `TryFrom`/`TryInto`)" — confuses the RESULT TYPE with panic-freedom. `From` is
    // an ordinary user-implementable trait; `impl From<X> for Y { fn from(_) -> Y {
    // panic!() } }` is safe stable code, and the executed K1-c/K1-d witnesses panic.
    // Both are in `PANICKING` now, matching `lower.rs`'s long-standing fail-closed pin.
    // T3 rung-1 recovery (aterm-scrollback batch): the zero-comparison in-order
    // iterator ctor (`BTreeMap::iter`), the const union wrap (`MaybeUninit::new`),
    // and the const struct ctor (`RangeInclusive::new`) — see the allowlist entries'
    // per-entry justifications; their panicking/parameterized near-neighbors are
    // pinned in PANICKING above. (`Vec::shrink_to_fit` was in this batch and is
    // REMOVED in R13: it is allocator-generic, exactly like the retired `Vec::push`,
    // and the K1-b witness isolates the `A::shrink` panic.)
    "alloc::collections::btree::map::BTreeMap::<alloc::string::String, u32>::iter",
    "core::mem::maybe_uninit::MaybeUninit::<u32>::new",
    "core::ops::range::RangeInclusive::<usize>::new",
];

// ===========================================================================
// FRONT B (R13) — CROSS-LIST CONTRADICTION DETECTOR
//
// This crate holds TWO independent statements about the same callees, and until
// R13 they disagreed. `lower.rs`'s soundness pins assert a set of callees must
// FAIL CLOSED; this file's `SHOULD_BE_TOTAL` asserted several of the SAME callees
// are "genuinely total (no user code, cannot panic)" and the completeness test
// advertised them as "rung-1 targets" to reclaim. Nothing compared the two.
//
// The detector below does. It normalizes both sides to a generic-erased FAMILY
// KEY (`alloc::vec::Vec::<u8, MyAlloc>::push` and `alloc::vec::Vec::<u32>::push`
// both key to `alloc::vec::Vec::push`), because generic erasure is exactly the
// step that let the two spellings drift apart in the first place.
// ===========================================================================

/// The identities `lower.rs`'s `callbacks_traits_growth_and_broad_families_fail_closed`
/// pins as must-fail-closed. Mirrored here BY VALUE on purpose: if that pin list is
/// edited, this copy goes stale and the mirror-liveness assertion below fires.
const LOWER_RS_FAIL_CLOSED_PINS: &[&str] = &[
    "alloc::vec::Vec::<u8>::with_capacity",
    "alloc::vec::Vec::<u8>::shrink_to_fit",
    "alloc::vec::Vec::<u8>::push",
    "alloc::vec::Vec::<u8, my_crate::MyAlloc>::push",
    "alloc::string::String::with_capacity",
    "core::str::<impl str>::to_ascii_lowercase",
    "std::ffi::OsStr::to_string_lossy",
    "core::sync::atomic::AtomicU64::load",
    "core::hash::Hasher::write_u64",
    "std::fs::read",
    "std::io::Read::read_to_end",
    "core::convert::From::from",
    "core::convert::Into::into",
    "core::num::<impl u64>::wrapping_add",
    "std::sync::Mutex::<T>::lock",
    "core::mem::zeroed::<T>",
    "core::fmt::Formatter::debug_struct",
    "core::fmt::Display::fmt",
    "core::iter::Iterator::next",
    "core::option::Option::<T>::unwrap_or",
    "core::result::Result::<T, E>::ok",
    "my_crate::core::mem::size_of",
];

/// The ONLY family a `SHOULD_BE_TOTAL` entry may share with a fail-closed pin, and
/// why. `wrapping_add`/`sub`/`mul` genuinely cannot panic — the two lists do not
/// disagree about the FACT. They disagree about the MECHANISM, deliberately: the
/// extractor stamps these with the tcx-authenticated
/// `@trust-rustc-total-primitive-method::` marker and `translate_chc` models them as
/// an exact modular `BinOp`, so admitting them to the FLAT summary would replace a
/// precise value with an unconstrained `Undef`. Fail-closed there is a precision
/// choice, not a totality claim.
const DOCUMENTED_MECHANISM_EXEMPTIONS: &[&str] = &["core::num::wrapping_add"];

/// Erase generic argument groups and `<impl T>` / `<T as Trait>` segments, keeping
/// the plain identifier spine. `::` inside a `<…>` group is NOT a segment break.
fn family_key(callee: &str) -> String {
    let mut segments: Vec<String> = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32;
    let mut chars = callee.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '<' => {
                depth += 1;
                current.push(c);
            }
            '>' => {
                depth -= 1;
                current.push(c);
            }
            ':' if depth == 0 && chars.peek() == Some(&':') => {
                chars.next();
                segments.push(std::mem::take(&mut current));
            }
            _ => current.push(c),
        }
    }
    segments.push(current);
    segments.retain(|s| !s.is_empty() && !s.contains('<'));
    segments.join("::")
}

/// Families claimed total by `should_be_total` that the crate ALSO pins must-fail-closed.
fn ground_truth_contradictions(should_be_total: &[&str]) -> Vec<String> {
    let pinned: Vec<String> = LOWER_RS_FAIL_CLOSED_PINS.iter().map(|c| family_key(c)).collect();
    let exempt: Vec<String> =
        DOCUMENTED_MECHANISM_EXEMPTIONS.iter().map(|c| (*c).to_string()).collect();
    let mut hits: Vec<String> = Vec::new();
    for &callee in should_be_total {
        let key = family_key(callee);
        // A single-segment key (a bare trait-qualified method) is too weak to
        // attribute; skip rather than risk a false collision.
        if key.split("::").count() < 2 {
            continue;
        }
        if pinned.contains(&key) && !exempt.contains(&key) {
            hits.push(format!("{callee}  (family `{key}`)"));
        }
    }
    hits.sort();
    hits.dedup();
    hits
}

/// The exact `SHOULD_BE_TOTAL` membership as it stood BEFORE R13, for the four
/// entries that were wrong. Kept as data so the detector's ability to fire is
/// demonstrated on every run, without reverting anything.
const PRE_R13_FALSIFIED_ENTRIES: &[&str] = &[
    "alloc::vec::Vec::<u32>::push",
    "alloc::vec::Vec::<u32>::shrink_to_fit",
    "core::convert::From::from",
    "core::convert::Into::into",
];

#[test]
fn oracle_ground_truth_does_not_contradict_the_fail_closed_pins() {
    // (1) THE DETECTOR FIRES ON UNFIXED INPUT. Feed it the pre-R13 list; all four
    // falsified entries must be reported. Without this the test could pass because
    // the check is vacuous rather than because the tree is consistent.
    let on_unfixed = ground_truth_contradictions(PRE_R13_FALSIFIED_ENTRIES);
    assert_eq!(
        on_unfixed.len(),
        PRE_R13_FALSIFIED_ENTRIES.len(),
        "the contradiction detector must flag every pre-R13 falsified entry; got {on_unfixed:?}"
    );

    // (2) THE MIRROR IS LIVE. Every pinned identity must still fail closed in the
    // real predicate — otherwise `LOWER_RS_FAIL_CLOSED_PINS` has gone stale against
    // `lower.rs` and (1) is measuring a fossil.
    let mirror_broken: Vec<&str> =
        LOWER_RS_FAIL_CLOSED_PINS.iter().copied().filter(|c| total_no_panic_call_summary(c)).collect();
    assert!(
        mirror_broken.is_empty(),
        "these are mirrored from `lower.rs`'s fail-closed pin but are now classified \
         TOTAL — either a false proof landed or the mirror is stale: {mirror_broken:?}"
    );

    // (3) THE TREE IS CONSISTENT.
    let contradictions = ground_truth_contradictions(SHOULD_BE_TOTAL);
    assert!(
        contradictions.is_empty(),
        "`SHOULD_BE_TOTAL` claims these callees cannot panic on any input, while this \
         crate simultaneously pins their family must-fail-closed. One of the two is a \
         false proof waiting to be reclaimed — resolve it, do not silence it:\n  {}",
        contradictions.join("\n  ")
    );
}

#[test]
fn call_summary_oracle_soundness() {
    let mut violations: Vec<String> = Vec::new();
    for &callee in PANICKING.iter().chain(ADVERSARIAL.iter()) {
        if total_no_panic_call_summary(callee) {
            violations.push(format!(
                "FALSE PROVE source: `{callee}` is classified cannot-panic (total), but it \
                 panics or dispatches into user code — its panic obligation would be dropped"
            ));
        }
    }
    assert!(
        violations.is_empty(),
        "bridge call-summary SOUNDNESS violations ({} of {}):\n{}",
        violations.len(),
        PANICKING.len() + ADVERSARIAL.len(),
        violations.join("\n")
    );
    eprintln!(
        "bridge call-summary oracle: {} panicking + {} adversarial callees, all correctly \
         classified not-total (no false-proof source)",
        PANICKING.len(),
        ADVERSARIAL.len()
    );
}

/// K-PARAMETERIZED std types: their derived Clone/PartialEq/Default/Ord/Hash dispatch
/// INTO the element/payload type `K` (whose user impl we cannot see and which can panic).
/// The Attack-5 contract: every one MUST be classified NOT element-free-total, so the
/// call fails closed. `def_path_str` carries no generics, so each name is bare.
const K_PARAMETERIZED: &[&str] = &[
    "alloc::vec::Vec",
    "alloc::boxed::Box",
    "core::option::Option",
    "core::result::Result",
    "std::collections::hash::map::HashMap",
    "alloc::collections::btree::map::BTreeMap",
    "alloc::rc::Rc",
    "alloc::sync::Arc",
    "alloc::collections::vec_deque::VecDeque",
    "core::cell::RefCell",
    "core::cmp::Reverse",
    // THE HOLE this oracle found: `Wrapping<T>` is an UNBOUNDED transparent newtype
    // (unlike `NonZero<T>`, whose `ZeroablePrimitive` bound is sealed to primitives), so
    // `Wrapping<UserType>`'s derived Clone/eq/cmp dispatch into the user type — exactly
    // the Attack-5 shape closed for Vec/Box. Must be NOT element-free.
    "core::num::Wrapping",
    "mycrate::domain::MyAdt", // a user ADT
];

/// Genuinely ELEMENT-FREE total std leaves: parameter-free (String bottoms out in u8;
/// Ordering/Duration have no element) or sealed-to-primitive (NonZero). MUST be total.
const ELEMENT_FREE: &[&str] = &[
    "alloc::string::String",
    "std::string::String",
    "core::cmp::Ordering",
    "core::time::Duration",
    "std::time::Duration",
    "core::num::NonZeroU32",
    "core::num::NonZeroI64",
];

#[test]
fn element_free_oracle_soundness() {
    let mut violations: Vec<String> = Vec::new();
    for &name in K_PARAMETERIZED {
        if is_element_free_total_std_type(name) {
            violations.push(format!(
                "FALSE PROVE source: `{name}` is classified element-free-total, but it is \
                 K-parameterized — its Clone/eq/cmp dispatches into the element type, which \
                 can panic (Attack-5 shape); the panic obligation would be dropped"
            ));
        }
    }
    assert!(
        violations.is_empty(),
        "element-free SOUNDNESS violations ({} of {}):\n{}",
        violations.len(),
        K_PARAMETERIZED.len(),
        violations.join("\n")
    );
    // And the genuine element-free leaves must still be recognized (no over-removal).
    let missing: Vec<&str> =
        ELEMENT_FREE.iter().copied().filter(|n| !is_element_free_total_std_type(n)).collect();
    assert!(
        missing.is_empty(),
        "element-free leaves wrongly rejected (precision regression): {}",
        missing.join(", ")
    );
    eprintln!(
        "element-free oracle: {} K-parameterized types all not-total (no Attack-5 source), \
         {} element-free leaves all total",
        K_PARAMETERIZED.len(),
        ELEMENT_FREE.len()
    );
}

#[test]
fn call_summary_oracle_completeness() {
    let recognized: Vec<&str> =
        SHOULD_BE_TOTAL.iter().copied().filter(|c| total_no_panic_call_summary(c)).collect();
    let gaps: Vec<&str> =
        SHOULD_BE_TOTAL.iter().copied().filter(|c| !total_no_panic_call_summary(c)).collect();
    eprintln!(
        "bridge call-summary COMPLETENESS: {}/{} genuinely-total callees recognized ({}%)",
        recognized.len(),
        SHOULD_BE_TOTAL.len(),
        recognized.len() * 100 / SHOULD_BE_TOTAL.len().max(1)
    );
    if !gaps.is_empty() {
        eprintln!("  precision GAPS (total but unrecognized — rung-1 target): {}", gaps.join(", "));
    }
    // Non-vacuity: the allowlist must recognize a solid base of total callees.
    assert!(
        recognized.len() >= 8,
        "expected the allowlist to recognize the common total std callees, got {}",
        recognized.len()
    );
}
