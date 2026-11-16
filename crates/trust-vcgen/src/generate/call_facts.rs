// Dest-value facts for calls the VC lane models exactly rather than havocking:
// `Ord::min/max/clamp`, `bool::from`, the saturating and wrapping-negate
// families, and `f{32,64}::to_bits`. Each recognizer pairs a callee-path test
// with the formula that pins the destination local to the callee's result.

use super::*;

/// Extract the method name of an `Ord` trait call, e.g.
/// `<usize as core::cmp::Ord>::min` -> `Some("min")`. Returns the EXACT method (so
/// `min_by`/`min_by_key` — whose result bound is comparator-dependent and would
/// be UNSOUND to assume — are distinguished from `min`). Matches only the `Ord`
/// trait (integer/ordered types; floats have no `Ord`), so `a <= min(a,b)` holds.
pub(super) fn ord_method(callee: &str) -> Option<&str> {
    // Method = final path segment, minus turbofish generics. Exact match so
    // `min_by`/`min_by_key` (comparator-dependent — unsound to bound) are excluded.
    // The robust `method_tail` strips a TRAILING monomorphization turbofish group
    // (`…::min::<__trust_args@HASH>`) that a naive `rsplit("::")` returns INSTEAD of
    // `min` — leaving `method` empty so a real `<u32 as core::cmp::Ord>::min::<…>`
    // matched nothing, and its `min(x,31) <= 31` result-fact was never emitted →
    // `corner_count`'s `shift < 32` precondition at `(n as u32).min(31)` was falsely
    // refuted. Recognition-only fix (same fact set); gated TRUST_ORD_MIN_TAG_FIX for A/B.
    static ORD_MIN_TAG_FIX: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let method = if callee.trim_end().ends_with('>')
        && *ORD_MIN_TAG_FIX
            .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_ORD_MIN_TAG_FIX"))
    {
        method_tail(callee)
    } else {
        let last = callee.rsplit("::").next()?;
        last.split('<').next().unwrap_or(last).trim()
    };
    if !matches!(method, "min" | "max" | "clamp") {
        return None;
    }
    // Scope to the standard-library ordered ops across the spellings
    // `safe_def_path_str` may produce: the `Ord` trait method
    // (`core::cmp::Ord::min`, `<T as core::cmp::Ord>::min`) or the `cmp` free
    // function (`core::cmp::min`). A user `mymod::min` matches none of these and is
    // (soundly) not assumed to satisfy the min/max bounds.
    //
    // Trust (2026-10-03, NAME-ANCHOR-1): anchored by POSITION, not by substring.
    // An unqualified path must be ROOTED at `core::cmp::`/`std::cmp::` (the
    // producer stamps a crate that impersonates a sysroot name, so such a root is
    // std's); a qualified one must have a trait half — split at the qualifier's
    // own top-level ` as ` — that IS `core::cmp::Ord` or `std::cmp::Ord`. The
    // substring tests this replaces admitted spellings a user can produce: the
    // bare `as Ord>::` (the producer renders std's trait untrimmed and
    // crate-qualified, so a bare `Ord` names some other trait — a user `trait
    // Ord` renders under its own crate, but nothing here checked that), and
    // `as core::cmp::Ord>::` anywhere in the string, including inside a generic
    // argument of a user callee.
    //
    // Trust (2026-10-04, NAME-ANCHOR-2): this anchors the TRAIT METHOD, never the
    // impl that runs. `Ord::min`/`max`/`clamp` are PROVIDED methods any impl may
    // override, so `<user::E as core::cmp::Ord>::min` passes here (its DefId, and
    // its `callee_key`, are core's) while the body that runs is the user's. So no
    // fact-minting consumer calls this: each asks [`primitive_int_ord_method`],
    // which also pins `Self` to a primitive integer. (The untyped
    // `is_ord_{min,max,clamp}_call` wrappers are deleted for that reason.)
    let std_shaped = callee.starts_with("core::cmp::")
        || callee.starts_with("std::cmp::")
        || vc_qualified_trait_method(callee).is_some_and(|(trait_path, _)| {
            matches!(trait_path, "core::cmp::Ord" | "std::cmp::Ord")
        });
    if std_shaped { Some(method) } else { None }
}

/// Trust (2026-10-04, NAME-ANCHOR-2): the `Ord` method (`"min"`, `"max"` or
/// `"clamp"`) of the call `dest = callee(args..)` ONLY when the impl that runs is
/// a primitive integer's — the one question every `min`/`max`/`clamp` result fact
/// (`dest <= arg`, `dest >= c`, `lo <= dest <= hi`, and every const bound read off
/// such a call) must ask.
///
/// WHY THE TRAIT PATH IS NOT ENOUGH. [`ord_method`] anchors std's TRAIT, and
/// `Ord::min`/`max`/`clamp` are provided methods an impl may override. A user
/// `impl Ord for E` on a `#[repr(u8)]` enum whose `min` returns `E::B` renders as
/// `<ordenum::E as core::cmp::Ord>::min`, with `callee_key` `krate_name: core`,
/// `krate_is_real_sysroot: true` — the DefId is core's trait method. The call-dest
/// lane minted `dest <= arg` for it; the Clean kernel certified the `+ 100`
/// overflow row and the elision deleted the check, so `f(E::A)` returned 44 where
/// vanilla Rust panics (measured on a stage 1 of integ/wave11 `936573497e`, under
/// certify, default, strict and memory-safe;
/// `tests/ui/trust/ord_min_max_requires_primitive_self{,_run}.rs`). The free
/// `core::cmp::min::<T>` forwards to `T::min`, so it has the same hole.
///
/// WHAT NAMES THE IMPL. `Ord::min(self, other: Self) -> Self`, `max` and `clamp`
/// (and `cmp::min<T>`/`max<T>`, which return `T`) return `Self`, so the
/// DESTINATION's declared type is `Self`. When it is a primitive integer
/// (`Ty::Int`/`Ty::PtrSizedInt`) the impl is core's: the orphan rule forbids any
/// other crate to implement `Ord` for a primitive, and core's integer impls do not
/// override these methods' semantics. Every argument must be `Self` too — a place
/// of exactly the destination's type, or an integer constant (whose extracted
/// width is not the declared one: `ConstValue::Int` is typed i64) — so an
/// extraction that disagrees with itself is refused rather than guessed. This is
/// the gate trust-ir-bridge's `native_ord_minmax_facts`/`bridge_ord_method`
/// already apply.
///
/// Fail closed: `None` for every other shape, and the caller mints nothing.
pub(crate) fn primitive_int_ord_method<'c>(
    func: &VerifiableFunction,
    callee: &'c str,
    args: &[Operand],
    dest: &Place,
) -> Option<&'c str> {
    if !matches!(args.len(), 2 | 3) {
        return None;
    }
    let self_ty = crate::place_ty_cow(func, dest)?;
    if !matches!(self_ty.as_ref(), Ty::Int { .. } | Ty::PtrSizedInt { .. }) {
        return None;
    }
    let method = ord_method(callee)?;
    let arg_is_self = |arg: &Operand| match arg {
        Operand::Copy(place) | Operand::Move(place) => {
            crate::place_ty_cow(func, place).is_some_and(|ty| ty.as_ref() == self_ty.as_ref())
        }
        Operand::Constant(_) => {
            crate::operand_ty_cow(func, arg).is_some_and(|ty| matches!(ty.as_ref(), Ty::Int { .. }))
        }
        _ => false,
    };
    args.iter().all(arg_is_self).then_some(method)
}

/// Trust (2026-10-03, NAME-ANCHOR-1): the GENUINE std length method — `Vec`,
/// slice, `str`, `String` (`total_summary_len_call`) or `VecDeque` — whose result
/// IS the length of the place its receiver borrows.
///
/// WHY. The length-of-place recognizers (`container_len::operand_is_len_of_place`
/// arm (a), `container_len::len_def_block`, `panic_calls::operand_is_len_of_base`)
/// keyed on `method_tail(callee) == "len"` alone, so a user trait method NAMED
/// `len` — `<alloc::vec::Vec<u32> as mycrate::L>::len`, which may return anything —
/// was read as the `Vec`'s length. The field-guard lane then minted
/// `coll_len(w.v) > j` from `if j < L::len(&w.v)`, and the `w.v[j]` row came back
/// `slice proved`, kernel-certified, on an index that panics (measured on a stage 1
/// of `a0877b2a62`; `tests/ui/trust/len_guard_field_user_trait_len.rs`).
///
/// ONE MATCHER: the one the `_len == coll_len(base)` tie already uses
/// (`guards::slice_last_some_nonempty_definitions`), so the recognizer that reads a
/// length and the one that ties it to `coll_len` agree on what a length call is.
/// `total_summary_len_call` is root-anchored, refuses any ` as `-qualified trait
/// path and a stamped impersonator crate, and wants the exact `::len` leaf. A miss
/// is fail-closed: no fact is minted and the bounds row stays unproved.
pub(super) fn is_std_inherent_len_call(callee: &str) -> bool {
    trust_types::total_call_summaries::total_summary_len_call(callee)
        || super::collection_range::is_std_vecdeque_method(callee, &["len"])
}

/// Trust (2026-10-06, LEN-KEY-1): [`is_std_inherent_len_call`] OR the call's
/// compiler-minted [`trust_types::CalleeKey`] names std's own INHERENT `len` —
/// `Vec::len`, `<[T]>::len`, `str::len` or `String::len` — by DefId.
///
/// WHY. The string matcher wants the exact `::len` leaf, so it declines the
/// producer's trailing `::<__trust_args@HASH>` tag. That tag is appended to EVERY
/// generic callee whenever the crate graph merely CONTAINS a duplicate crate name,
/// and an ordinary Cargo graph does: a crates.io `memchr` (pulled in by
/// `serde_json`) shares its name with std's own `memchr` dependency. In such a
/// graph `alloc::vec::Vec::<T>::len::<__trust_args@…>` read as "not a length",
/// so `args.len() == 2 && args[0] == x` lost its field-guard fact and every
/// `args[k]` row went `slice proved` -> `slice failed` (tla-cert 29 rows, measured
/// on the stage 1 of `c797f90c1`; NAME-ANCHOR-1, 35a45d66a3, replaced the
/// tag-tolerant `method_tail` test with the exact matcher).
///
/// WHY THE KEY AND NOT A NORMALIZED STRING. The key is minted from `(TyCtxt,
/// DefId)` alone, and a `sysroot_item` tag only for a DefId of a
/// residency-authenticated sysroot crate (`krate_is_real_sysroot`). The four
/// items are INHERENT methods, so the DefId IS the function that runs (unlike a
/// trait method, NAME-ANCHOR-2): no user `len` — a free fn, a user trait method
/// on std's `Vec`, a crate built `--crate-name alloc` — can carry it. The string
/// arm stays exactly as NAME-ANCHOR-1 left it; this only admits the genuine call
/// the rendering hid. A key-less call, or a key without one of these four tags,
/// falls to the string arm and nothing else (fail-closed).
pub(super) fn is_std_inherent_len_call_or_key(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
) -> bool {
    is_std_inherent_len_call(callee) || callee_key_is_std_inherent_len(callee_key)
}

/// The key half of [`is_std_inherent_len_call_or_key`]: a residency-authenticated
/// sysroot DefId tagged as one of std's four inherent `len` methods.
pub(crate) fn callee_key_is_std_inherent_len(callee_key: Option<&trust_types::CalleeKey>) -> bool {
    use trust_types::SysrootItem as S;
    callee_key.is_some_and(|key| {
        key.krate_is_real_sysroot
            && matches!(key.sysroot_item, Some(S::VecLen | S::SliceLen | S::StrLen | S::StringLen))
    })
}

/// The exact renderings [`is_bool_from_call`] accepts: std's `From<bool>` impl
/// for each primitive integer, as the extractor spells it
/// (`<usize as core::convert::From<bool>>::from`, measured on
/// `scratchpad/stage1-w11fix` for `usize::from(b)` and `u32::from(b)`), its
/// `std::` re-export spelling, and the bare trait-method paths
/// `{core,std}::convert::{From::from,Into::into}`.
const BOOL_FROM_PATHS: &[&str] = &[
    "<u8 as core::convert::From<bool>>::from",
    "<u16 as core::convert::From<bool>>::from",
    "<u32 as core::convert::From<bool>>::from",
    "<u64 as core::convert::From<bool>>::from",
    "<u128 as core::convert::From<bool>>::from",
    "<usize as core::convert::From<bool>>::from",
    "<i8 as core::convert::From<bool>>::from",
    "<i16 as core::convert::From<bool>>::from",
    "<i32 as core::convert::From<bool>>::from",
    "<i64 as core::convert::From<bool>>::from",
    "<i128 as core::convert::From<bool>>::from",
    "<isize as core::convert::From<bool>>::from",
    "<u8 as std::convert::From<bool>>::from",
    "<u16 as std::convert::From<bool>>::from",
    "<u32 as std::convert::From<bool>>::from",
    "<u64 as std::convert::From<bool>>::from",
    "<u128 as std::convert::From<bool>>::from",
    "<usize as std::convert::From<bool>>::from",
    "<i8 as std::convert::From<bool>>::from",
    "<i16 as std::convert::From<bool>>::from",
    "<i32 as std::convert::From<bool>>::from",
    "<i64 as std::convert::From<bool>>::from",
    "<i128 as std::convert::From<bool>>::from",
    "<isize as std::convert::From<bool>>::from",
    "core::convert::From::from",
    "std::convert::From::from",
    "core::convert::Into::into",
    "std::convert::Into::into",
];

/// The standard `bool -> integer` conversion (`usize::from(b)` etc.), whose result is
/// exactly `b as {int}` and so lies in {0, 1}. Recognized so the call result (otherwise
/// havoc'd) can be soundly bounded, matching the `bool as {int}` CAST path
/// (`cast_definition_formula` -> `bool_to_int_formula`). The extractor renders
/// `usize::from(b)` as the impl-qualified `<usize as core::convert::From<bool>>::from`;
/// the bare trait-method paths are kept for a producer that renders the trait. The
/// CALLER gates on a BOOL arg and an int-typed dest, which together pin this to
/// `From<bool>`/`Into<int>` for a primitive int — so `usize::from(u8)` (non-bool arg)
/// and a non-primitive `From<bool>` newtype (non-int dest) are both excluded.
///
/// Trust (2026-10-04, NUM-METHOD-ANCHOR-1): the callee must be DEFINED in a real
/// sysroot crate (its compiler-minted key) and its rendering must be EXACTLY one of
/// [`BOOL_FROM_PATHS`] (one trailing turbofish allowed), through the shared
/// [`trust_types::callee_key::sysroot_exact_path`]. The substring test this replaces
/// accepted `From<bool>` plus `as core::` ANYWHERE, so a user generic
/// `conv::<From<bool>, <T as core::ops::Not>::Output>(flag)` returning 7 — rendered
/// `crate::conv::<crate::From<bool>, <T as core::ops::bit::Not>::Output>` — had its
/// result pinned to `{0, 1}` and `[_; 2][x as usize]` read `bounds proved` (measured
/// on `scratchpad/stage1-w11fix`; the program panics with index 7). Every entry
/// names an item whose `Self` and trait arguments are primitives spelled in the
/// path, so the orphan rule leaves core's impl as the only one that can run.
pub(super) fn is_bool_from_call(callee: &str, callee_key: Option<&trust_types::CalleeKey>) -> bool {
    trust_types::callee_key::sysroot_exact_path(callee_key, callee, BOOL_FROM_PATHS).is_some()
}

/// Trust (2026-09-24, TRUST-09): the std conversion between two PRIMITIVE INTEGER
/// types — `<usize as core::convert::From<u8>>::from` (`usize::from(b)`) and its
/// dual `<u8 as core::convert::Into<usize>>::into` (`b.into()`), the exact
/// spellings the extractor renders for them (measured on stage1 `5242fb1fe`: the
/// impl form, not the trait-method form [`is_bool_from_call`] also accepts).
///
/// Every such impl is LOSSLESS — std implements `From<A> for B` between primitive
/// integers only where every `A` value is a `B` value (`u8 -> usize`, `i8 -> i64`,
/// `u16 -> i32`, …; the lossy directions are `TryFrom`), and the orphan rule forbids
/// any other crate to implement a std trait between two std types. So the result is
/// the argument's value, which the call's havoc otherwise hides:
/// `TABLE[usize::from(byte)]` over a `[_; 256]` was refuted with index 256.
///
/// EXACT MATCH, not a substring: both type names must be primitive integer names
/// and the path must be the `core`/`std` `convert` trait, so neither a user trait
/// named `From` nor a generic argument spelling a primitive can satisfy it. `char`
/// and `bool` sources are left to their own recognizers.
pub(super) fn is_std_int_from_into_call(callee: &str) -> bool {
    const INTS: &[&str] =
        &["u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize"];
    let Some(rest) = callee.strip_prefix('<') else { return false };
    let Some((self_ty, rest)) = rest.split_once(" as ") else { return false };
    let Some(rest) =
        rest.strip_prefix("core::convert::").or_else(|| rest.strip_prefix("std::convert::"))
    else {
        return false;
    };
    let other_ty = if let Some(r) = rest.strip_prefix("From<") {
        r.strip_suffix(">>::from")
    } else if let Some(r) = rest.strip_prefix("Into<") {
        r.strip_suffix(">>::into")
    } else {
        None
    };
    other_ty.is_some_and(|other| INTS.contains(&other)) && INTS.contains(&self_ty)
}

/// Trust (2026-09-29): the ARGUMENT of the lossless std integer conversion that is
/// `local`'s ONE value — `local = <B as From<A>>::from(a)` or `local = <A as
/// Into<B>>::into(a)` between primitive integers ([`is_std_int_from_into_call`]) —
/// whose result IS `a`'s value.
///
/// WHY. The `dest == arg` fact `semantic_guard` states for these calls is an
/// `Int`-sorted equation and is withheld at width 128 (`Formula::Int` cannot carry
/// the `±2^127` range), while signed 128-bit add/sub/neg are decided on a
/// bitvector core over FRESH operand variables that only a STRUCTURAL encoding
/// constrains. A widening spelled `x as i128` has that encoding
/// (`v2_widening_bv_source`: zero/sign-extension of an `x`-width variable); the
/// SAME widening spelled `i128::from(x)` had none, so `i128::from(x) + 1` was
/// refuted at `i128::MAX` (trust-ir-conformance `generate.rs:468/477`, measured
/// 2026-09-29 on the installed `321aaeda7` and on a Trust `main` stage 1).
///
/// `None` unless the local holds exactly this one value
/// (`local_defs::unique_value_call`: no second call destination, no whole or
/// partial store, no escaping `&mut`), the call writes the WHOLE local, has one
/// argument, and is neither foreign nor declared `unsafe`. Callers still check the
/// operand types themselves: the value-preserving claim is for the std impls, and
/// every one of them is a strict widening, so a caller that also requires
/// `dest width > arg width` (and no signed-to-unsigned step) admits exactly them.
pub(crate) fn lossless_int_conversion_arg(
    func: &VerifiableFunction,
    local: usize,
) -> Option<&Operand> {
    if crate::local_defs::is_parameter(func, local)
        || !super::terminator_presence_for(func).has_bare_dest_call
    {
        return None;
    }
    // The per-body memoised value count first: a local holding more (or fewer)
    // than one value cannot have a unique defining call, and this keeps the
    // uncached write walk of `unique_value_call` off every multiply-assigned local
    // the constant fold asks about (measured: without it the version-oracle scaling
    // ladder's `body_scan_items` grew 3.5x per doubling).
    if !crate::local_defs::holds_one_value(func, local) {
        return None;
    }
    let Terminator::Call {
        func: callee, args, dest, is_foreign: false, is_unsafe_sig: false, ..
    } = crate::local_defs::unique_value_call(func, local)?
    else {
        return None;
    };
    if dest.local != local
        || !dest.projections.is_empty()
        || args.len() != 1
        || !is_std_int_from_into_call(callee)
    {
        return None;
    }
    args.first()
}

/// Trust (2026-10-03, cap from-range): the CLOSED set of lossless std scalar
/// conversions whose result is the argument's value, as `(source, destination)`
/// primitive type names — transcribed from the impls themselves, not inferred:
///
///  * `library/core/src/convert/num.rs` `impl_from_bool!` (lines 58-59):
///    `From<bool>` for every integer, body `b as Self` — `false → 0`, `true → 1`;
///  * `library/core/src/convert/num.rs` `impl_from!` (lines 79-121): the integer
///    widenings, body `small as Self`, each guarded in-source by
///    `debug_assert!(<$large>::MIN <= <$small>::MIN && <$small>::MAX <= <$large>::MAX)`
///    — the value is preserved;
///  * `library/core/src/char/convert.rs` (lines 40, 59, 80): `From<char>` for
///    `u32`/`u64`/`u128`, body `c as uN` — the scalar value.
///
/// The `Into` spelling is the blanket `impl<T, U: From<T>> Into<U> for T`
/// (`library/core/src/convert/mod.rs`), whose body is `U::from(self)`: the same
/// conversion. Floats, `TryFrom`, the reflexive `From<T> for T` (no range to
/// gain) and `From<u8> for char` (destination not an integer) are deliberately
/// absent: the table admits only what it names.
const STD_LOSSLESS_SCALAR_FROM: &[(&str, &str)] = &[
    // convert/num.rs:58-59 — bool → every integer.
    ("bool", "u8"),
    ("bool", "u16"),
    ("bool", "u32"),
    ("bool", "u64"),
    ("bool", "u128"),
    ("bool", "usize"),
    ("bool", "i8"),
    ("bool", "i16"),
    ("bool", "i32"),
    ("bool", "i64"),
    ("bool", "i128"),
    ("bool", "isize"),
    // convert/num.rs:79-89 — unsigned → unsigned.
    ("u8", "u16"),
    ("u8", "u32"),
    ("u8", "u64"),
    ("u8", "u128"),
    ("u8", "usize"),
    ("u16", "u32"),
    ("u16", "u64"),
    ("u16", "u128"),
    ("u32", "u64"),
    ("u32", "u128"),
    ("u64", "u128"),
    // convert/num.rs:92-102 — signed → signed.
    ("i8", "i16"),
    ("i8", "i32"),
    ("i8", "i64"),
    ("i8", "i128"),
    ("i8", "isize"),
    ("i16", "i32"),
    ("i16", "i64"),
    ("i16", "i128"),
    ("i32", "i64"),
    ("i32", "i128"),
    ("i64", "i128"),
    // convert/num.rs:105-114 — unsigned → strictly wider signed.
    ("u8", "i16"),
    ("u8", "i32"),
    ("u8", "i64"),
    ("u8", "i128"),
    ("u16", "i32"),
    ("u16", "i64"),
    ("u16", "i128"),
    ("u32", "i64"),
    ("u32", "i128"),
    ("u64", "i128"),
    // convert/num.rs:119-121 — the pointer-width conversions std guarantees on
    // every target (`usize`/`isize` are at least 16 bits).
    ("u16", "usize"),
    ("u8", "isize"),
    ("i16", "isize"),
    // char/convert.rs:40,59,80 — char → its scalar value.
    ("char", "u32"),
    ("char", "u64"),
    ("char", "u128"),
];

/// Trust (2026-10-03, cap from-range): `Some((source, destination))` iff `callee`
/// is the extractor's IMPL spelling of one of the [`STD_LOSSLESS_SCALAR_FROM`]
/// conversions — `<B as core::convert::From<A>>::from` or
/// `<A as core::convert::Into<B>>::into` (also under `std::`). The names are only
/// half the authentication: a generic parameter may be NAMED `u64`, so the caller
/// must also find the two declared types to be those primitives (see
/// [`lossless_conversion_source_range`]); with both sides primitive, coherence
/// leaves `core` as the only crate that can supply the impl (E0117 forbids any
/// other).
pub(crate) fn std_lossless_scalar_conversion(callee: &str) -> Option<(&'static str, &'static str)> {
    let rest = callee.strip_prefix('<')?;
    let (self_ty, rest) = rest.split_once(" as ")?;
    let rest =
        rest.strip_prefix("core::convert::").or_else(|| rest.strip_prefix("std::convert::"))?;
    let (src, dst) = if let Some(r) = rest.strip_prefix("From<") {
        (r.strip_suffix(">>::from")?, self_ty)
    } else {
        (self_ty, rest.strip_prefix("Into<")?.strip_suffix(">>::into")?)
    };
    STD_LOSSLESS_SCALAR_FROM.iter().copied().find(|&(s, d)| s == src && d == dst)
}

/// Whether the DECLARED type `ty` is the primitive spelled `name`. `usize`/`isize`
/// accept the faithful `PtrSizedInt` or the extractor's `Int` carrier at one of the
/// pointer widths Rust targets have (16, 32 or 64 bits — the extractor lowers
/// `usize` to `Int` at the target's width); an `Int` of any other width is not a
/// pointer-sized integer and is refused. `char` accepts the faithful `Char` and the
/// legacy `Int{32, unsigned}` carrier the verifier lane still receives for it.
fn declared_ty_is_primitive(ty: &Ty, name: &str) -> bool {
    let fixed =
        |w: u32, s: bool| matches!(ty, Ty::Int { width, signed } if *width == w && *signed == s);
    match name {
        "bool" => matches!(ty, Ty::Bool),
        "char" => matches!(ty, Ty::Char) || fixed(32, false),
        "u8" => fixed(8, false),
        "u16" => fixed(16, false),
        "u32" => fixed(32, false),
        "u64" => fixed(64, false),
        "u128" => fixed(128, false),
        "i8" => fixed(8, true),
        "i16" => fixed(16, true),
        "i32" => fixed(32, true),
        "i64" => fixed(64, true),
        "i128" => fixed(128, true),
        "usize" => {
            matches!(ty, Ty::PtrSizedInt { signed: false })
                || [16, 32, 64].into_iter().any(|w| fixed(w, false))
        }
        "isize" => {
            matches!(ty, Ty::PtrSizedInt { signed: true })
                || [16, 32, 64].into_iter().any(|w| fixed(w, true))
        }
        _ => false,
    }
}

/// The value range of the primitive spelled `name`: `bool` is the integer pair
/// `{0, 1}` (the 1-bit unsigned range — `b as {int}`), `char` the Unicode-scalar
/// carrier, an integer its own type range.
fn primitive_value_range(name: &str) -> Option<crate::range::RustScalarRange> {
    use crate::range::RustScalarRange;
    let int = |width: u32, signed: bool| Some(RustScalarRange::Integer { width, signed });
    match name {
        "bool" => int(1, false),
        "char" => Some(RustScalarRange::Char),
        "u8" => int(8, false),
        "u16" => int(16, false),
        "u32" => int(32, false),
        "u64" => int(64, false),
        "i8" => int(8, true),
        "i16" => int(16, true),
        "i32" => int(32, true),
        "i64" => int(64, true),
        // No table row has a 128-bit or pointer-width SOURCE.
        _ => None,
    }
}

/// The inclusive integer hull of a scalar range.
fn scalar_range_hull(range: crate::range::RustScalarRange) -> (i128, u128) {
    match range {
        crate::range::RustScalarRange::Char => (0, char::MAX as u128),
        crate::range::RustScalarRange::Integer { width, signed: true } => {
            (crate::range::signed_min(width), crate::range::signed_max(width) as u128)
        }
        crate::range::RustScalarRange::Integer { width, signed: false } => {
            (0, crate::range::unsigned_max(width))
        }
    }
}

/// Trust (2026-10-03, cap from-range): the SOURCE type's value range, when every
/// value `local` can hold is the result of a lossless std scalar conversion from
/// that one source type — `local = u64::from(x)` with `x: u32` holds a `u32`'s
/// value, so `local` lies in `0..=u32::MAX`, not merely in `u64`.
///
/// WHY THIS IS NOT THE `semantic_guard` `dest == arg` FACT AGAIN. That fact is a
/// PATH fact: it is threaded from the call to its successors and is lost wherever
/// the guard walk weakens a block (every loop header revisited with different
/// guards collapses to `true`, and so does everything it dominates). Inside a
/// loop the destination was therefore a free `u64` again, and
/// `u64::from(e.index) + u64::from(e.len)` was REFUTED at `u64::MAX` —
/// tla-model-ir `model.rs:1081/1083` on stage 1 (measured 2026-10-03). A RANGE
/// fact needs no path: it is true of the local at every read.
///
/// SOUNDNESS. `local_defs::value_calls` answers only when call destinations are
/// the local's ONLY write channel — not a parameter, no `Assign` beside the calls
/// (bar the call-through-temp spelling, whose value is the call's), no projected
/// store, no escaping `&mut`, no unlocatable write — so every value any read can
/// observe is some call's result. Each call must be the authenticated impl
/// spelling ([`std_lossless_scalar_conversion`]), take one argument, be neither
/// foreign nor declared `unsafe`, write its WHOLE destination, and have BOTH the
/// destination's and the argument's DECLARED types be the two spelled primitives
/// — a generic parameter named `u32` is a `Ty::Param`, not `Ty::Int`, and fails
/// here. With both sides primitive, the impl is `core`'s by coherence, and its
/// body is the value-preserving cast cited on [`STD_LOSSLESS_SCALAR_FROM`]. Every
/// call must agree on the source range (otherwise `None`: the declared range
/// stands), and the source hull must lie inside the declared destination hull —
/// true of every table row; checked so a mis-rendered spelling fails closed.
///
/// `None` means "no refinement": the caller keeps the declared type range.
pub(crate) fn lossless_conversion_source_range(
    func: &VerifiableFunction,
    local: usize,
) -> Option<crate::range::RustScalarRange> {
    if crate::local_defs::is_parameter(func, local)
        || !super::terminator_presence_for(func).has_bare_dest_call
    {
        return None;
    }
    let local_ty = crate::local_ty_ref(func, local)?;
    let declared = crate::range::rust_scalar_range(local_ty)?;
    if !matches!(declared, crate::range::RustScalarRange::Integer { width, .. } if width >= 8) {
        return None;
    }
    if !matches!(crate::local_defs::unique_value_def(func, local), None | Some(Rvalue::Use(_))) {
        return None;
    }
    let calls = crate::local_defs::value_calls(func, local)?;
    let mut source: Option<crate::range::RustScalarRange> = None;
    for call in calls {
        let Terminator::Call {
            func: callee,
            args,
            dest,
            is_foreign: false,
            is_unsafe_sig: false,
            ..
        } = call
        else {
            return None;
        };
        if !dest.projections.is_empty() || args.len() != 1 {
            return None;
        }
        let (src_name, dst_name) = std_lossless_scalar_conversion(callee)?;
        if !declared_ty_is_primitive(local_ty, dst_name)
            || (dest.local != local
                && !declared_ty_is_primitive(crate::local_ty_ref(func, dest.local)?, dst_name))
            || !declared_ty_is_primitive(crate::operand_ty_cow(func, &args[0])?.as_ref(), src_name)
        {
            return None;
        }
        let range = primitive_value_range(src_name)?;
        match source {
            None => source = Some(range),
            Some(seen) if seen == range => {}
            Some(_) => return None,
        }
    }
    let source = source?;
    let (src_lo, src_hi) = scalar_range_hull(source);
    let (dst_lo, dst_hi) = scalar_range_hull(declared);
    (dst_lo <= src_lo && src_hi <= dst_hi).then_some(source)
}

/// Whether `callee` is rooted at the genuine `core`/`std` primitive-number
/// inherent implementation. Callers use this before minting value-range facts;
/// a same-named user function must leave the destination unconstrained.
pub(super) fn is_std_num_intrinsic(callee: &str) -> bool {
    (callee.starts_with("core::") || callee.starts_with("std::")) && callee.contains("::num::")
}

/// The std `NonZero<T>::get` accessor — `core::num::nonzero::NonZero::<u32>::get`
/// and every `T` sibling — whose result is the wrapped value of a `NonZero<T>`.
///
/// The extractor lowers `NonZero`'s field `pattern_type!(T is 1..)` to the bare
/// carrier `T` (`ty_convert`'s `TyKind::Pat` arm), and the accessor is an opaque
/// `Terminator::Call`, so the destination is otherwise a free integer and every
/// `a / d.get()` false-refutes at `d.get() == 0`.
///
/// AUTHORITY / SOUNDNESS: `NonZero<T>`'s VALIDITY INVARIANT — no defined
/// execution ever holds a zero `NonZero<T>` (`new_unchecked(0)` is declared
/// immediate UB) — plus `get`'s definition as the identity projection of the
/// wrapped value. Same shape as the `saturating_*` / `wrapping_neg` / `to_bits`
/// recognizers below: a trusted model of a NAMED std function, CRATE-ORIGIN
/// anchored so a user-defined `mymod::NonZero::get` cannot inject it.
///
/// THE MATCH IS ON THE DEFINITION PATH, NOT ON SUBSTRINGS. Every conjunct of the
/// substring form (`::num::`, `NonZero`) is satisfiable by a GENERIC ARGUMENT of an
/// unrelated function: real compiler output for `let d: NonZeroU32 = c.get();` on a
/// `&Cell<NonZeroU32>` is the callee
/// `core::cell::Cell::<core::num::nonzero::NonZero<u32>>::get`, which satisfies all
/// of them and is not `NonZero::get`. `strip_generic_args` erases every balanced
/// `<…>` group first, reducing that path to `core::cell::Cell::get` and the genuine
/// one to `core::num::nonzero::NonZero::get`; the OWNER segment is then required to
/// be exactly `NonZero`, which no generic argument can supply.
/// `cell_of_nonzero_get_is_not_nonzero_get` is the row that fails when the check is
/// returned to substrings.
pub(super) fn is_nonzero_get_call(callee: &str) -> bool {
    if !(callee.starts_with("core::") || callee.starts_with("std::"))
        || !callee.contains("::num::")
        || !callee.contains("::NonZero")
        || method_tail(callee) != "get"
    {
        return false;
    }
    let path = strip_generic_args(callee);
    let mut segs = path.rsplit("::");
    let (Some("get"), Some("NonZero")) = (segs.next(), segs.next()) else {
        return false;
    };
    (path.starts_with("core::") || path.starts_with("std::")) && path.contains("::num::")
}

/// `callee` with every BALANCED `<…>` group removed, so what remains is the
/// definition path: `core::cell::Cell::<core::num::nonzero::NonZero<u32>>::get`
/// becomes `core::cell::Cell::get`. Nesting is handled by depth, and an UNBALANCED
/// `<` truncates the rest (fail-closed: a path a recognizer cannot parse must not
/// match one that it can).
fn strip_generic_args(callee: &str) -> std::borrow::Cow<'_, str> {
    if !callee.contains('<') && !callee.contains(":::") {
        return std::borrow::Cow::Borrowed(callee);
    }
    let mut out = String::with_capacity(callee.len());
    let mut depth = 0u32;
    let mut prev_dash = false;
    for ch in callee.chars() {
        match ch {
            '<' => {
                depth += 1;
                prev_dash = false;
            }
            '>' if prev_dash => {
                if depth == 0 {
                    out.push('>');
                }
                prev_dash = false;
            }
            '>' => {
                depth = depth.saturating_sub(1);
                prev_dash = false;
            }
            ':' if depth == 0 && out.ends_with("::") => {
                prev_dash = false;
            }
            _ => {
                if depth == 0 {
                    out.push(ch);
                }
                prev_dash = ch == '-';
            }
        }
    }
    std::borrow::Cow::Owned(out)
}

/// The std integer `wrapping_neg` inherent method (`core::num::<impl i128>::
/// wrapping_neg` and the `iN`/`uN` siblings). CRATE-ORIGIN anchored like
/// `fp_abs_call_width` — a user-defined `mymod::wrapping_neg` must NOT match
/// (matching it would inject a false value-definition, a false-PROVE channel).
pub(super) fn is_int_wrapping_neg_call(callee: &str) -> bool {
    if !(callee.starts_with("core::") || callee.starts_with("std::"))
        || !callee.contains("::num::")
    {
        return false;
    }
    let tail = callee.rsplit("::").next().unwrap_or(callee);
    let tail = tail.split('<').next().unwrap_or(tail).trim();
    tail == "wrapping_neg"
}

/// The std integer `saturating_add` / `saturating_sub` inherent method
/// (`core::num::<impl u32>::saturating_add` and the `iN`/`uN` siblings), or
/// `None`. CRATE-ORIGIN anchored exactly like `is_int_wrapping_neg_call` — a
/// user-defined `mymod::saturating_add` must NOT match (it would inject a false
/// value-definition, a false-PROVE channel).
pub(super) fn saturating_add_sub_method(callee: &str) -> Option<&'static str> {
    // Trust (std-intrinsics lane): the METHOD spelling below is what a user crate
    // calling `x.saturating_add(y)` produces. The METHOD BODY — and any code
    // compiled with `#![feature(core_intrinsics)]` — instead calls the body-less
    // rustc intrinsic, which the extractor stamps
    // `@trust-rustc-intrinsic::core::intrinsics::saturating_add::<T>` (measured
    // against the stage2 `-Ztrust-dump=mir:` output). That path fails the
    // `core::`/`std::` prefix test below, so the intrinsic form was havoc'd while
    // the identical method form was modeled exactly.
    //
    // Route BOTH spellings to the SAME clamp construction in
    // `saturating_call_dest_value`: the MIN/MAX saturation boundary is then
    // stated in exactly one place. Restating it for the intrinsic would be a
    // second place to get the saturation edge wrong.
    //
    // The intrinsic lane admits ONLY add/sub — `library/core/src/intrinsics/mod.rs`
    // declares no `saturating_mul` intrinsic, so a marked path spelling one is a
    // misextraction or a forgery and must decline (the method arm below keeps
    // `saturating_mul`, which IS a real library method).
    if let Some(intrinsic) = marked_saturating_intrinsic(callee) {
        return Some(intrinsic);
    }
    if !(callee.starts_with("core::") || callee.starts_with("std::"))
        || !callee.contains("::num::")
    {
        return None;
    }
    let tail = callee.rsplit("::").next().unwrap_or(callee);
    let tail = tail.split('<').next().unwrap_or(tail).trim();
    match tail {
        "saturating_add" => Some("saturating_add"),
        "saturating_sub" => Some("saturating_sub"),
        // Trust (flywheel feedback): named by the trust-convergence hardening
        // batch — `saturating_mul` yielded coverage-gap Unknowns while add/sub
        // proved. Same exact-total clamp axiom applies (`clamp(a*b, MIN, MAX)`
        // is the std semantics for every input; the nonlinear product routes
        // through the existing ay nonlinear-relaxation retry).
        "saturating_mul" => Some("saturating_mul"),
        _ => None,
    }
}

/// If `terminator` is a std `saturating_add`/`saturating_sub` call whose result
/// type is a `<= 64`-bit integer, the EXACT clamped result value
/// `clamp(argL ± argR, MIN, MAX)` (an `Ite`), plus the destination place. Both
/// the general call-dest fact (for an intermediate result, e.g.
/// `arr[i.saturating_sub(1)]`) and the return-slot pin (for a function that
/// returns the saturating result directly, so a `#[ensures]` over it connects)
/// use this ONE definition. `None` for a non-saturating call, wrong arity, or a
/// `> 64`-bit result (i128 `MIN`/`MAX` unlowerable in the Int lane — fail-closed,
/// dest stays havoc'd). SOUND: `clamp(x±y, MIN, MAX)` is the exact, total std
/// semantics for EVERY input (saturating arithmetic never panics).
pub(super) fn saturating_call_dest_value<'a>(
    func: &VerifiableFunction,
    terminator: &'a Terminator,
) -> Option<(&'a Place, Formula)> {
    let Terminator::Call { func: callee, args, dest, .. } = terminator else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (width, signed) = match crate::local_ty_ref(func, dest.local) {
        Some(Ty::Int { width, signed }) if *width <= 64 => (*width, *signed),
        _ => return None,
    };
    let method = saturating_add_sub_method(callee)?;
    let a = crate::operand_to_formula(func, &args[0]);
    let b = crate::operand_to_formula(func, &args[1]);
    let raw = match method {
        "saturating_add" => Formula::Add(Box::new(a), Box::new(b)),
        "saturating_mul" => Formula::Mul(Box::new(a), Box::new(b)),
        _ => Formula::Sub(Box::new(a), Box::new(b)),
    };
    let min_f = crate::range::type_min_formula(width, signed);
    let max_f = crate::range::type_max_formula(width, signed);
    // clamp: ite(raw > MAX, MAX, ite(raw < MIN, MIN, raw))
    let clamped = Formula::Ite(
        Box::new(Formula::Gt(Box::new(raw.clone()), Box::new(max_f.clone()))),
        Box::new(max_f),
        Box::new(Formula::Ite(
            Box::new(Formula::Lt(Box::new(raw.clone()), Box::new(min_f.clone()))),
            Box::new(min_f),
            Box::new(raw),
        )),
    );
    Some((dest, clamped))
}

/// If `terminator` is a std `wrapping_neg` call whose operand is an integer, the
/// EXACT two's-complement result value (an `Ite`) plus the destination place —
/// SIGNED: `ite(x == MIN, MIN, 0 - x)` (exact at every width); UNSIGNED
/// (`width <= 64`): `ite(x == 0, 0, (0 - x) + 2^width)`. Mirrors the inline
/// `wrapping_neg` model below and is reused by the return-slot pin so a
/// `#[ensures]` over `x.wrapping_neg()` connects to `_0`. `None` for a
/// non-`wrapping_neg` call or an unsigned `> 64`-bit result (fail-closed).
pub(super) fn wrapping_neg_call_dest_value<'a>(
    func: &VerifiableFunction,
    terminator: &'a Terminator,
) -> Option<(&'a Place, Formula)> {
    let Terminator::Call { func: callee, args, dest, .. } = terminator else {
        return None;
    };
    if args.len() != 1 || !is_int_wrapping_neg_call(callee) {
        return None;
    }
    let (width, signed) =
        crate::operand_ty_cow(func, &args[0]).as_deref().and_then(|ty| match ty {
            Ty::Int { width, signed } => Some((*width, *signed)),
            _ => None,
        })?;
    // The receiver's DECLARED width (from the callee path) must AGREE with the operand's
    // resolved width, or no fact is emitted (fail-closed).
    //
    // WITNESS — a live false proof before this check:
    //
    //     const K: i128 = i64::MIN as i128;
    //     let n = K.wrapping_neg();      // truly +2^63
    //
    // `operand_ty`'s `ConstValue::Int(v)` arm picks its width from the VALUE
    // (`i64` when `v` fits `i64`, else `i128`) because trust-types' `Int(i128)` carries
    // no width. `i64::MIN` fits `i64`, so an `i128` receiver resolved to width 64 and the
    // model emitted `ite(x == i64::MIN, i64::MIN, 0 - x)` — asserting the NEGATIVE
    // `i64::MIN` where the true `i128` result is the POSITIVE `+2^63`. Unlike the
    // bit-count bound (an inequality, where the wider width is the weaker and therefore
    // safe resolution — see `bitcount_receiver_width`), this is an EXACT VALUE
    // definition: a wrong width is wrong in BOTH directions, so only exact agreement is
    // admissible and disagreement must emit nothing. Pinned by
    // `wrapping_neg_declines_when_the_path_width_disagrees_with_the_operand`.
    match super::callee_summaries::std_num_impl_receiver_width(callee) {
        Some(declared) if declared == width => {}
        _ => return None,
    }
    let x = crate::operand_to_formula(func, &args[0]);
    let neg = Formula::Sub(Box::new(Formula::Int(0)), Box::new(x.clone()));
    let value = if signed {
        let min = crate::range::type_min_formula(width, true);
        Formula::Ite(
            Box::new(Formula::Eq(Box::new(x), Box::new(min.clone()))),
            Box::new(min),
            Box::new(neg),
        )
    } else if width <= 64 {
        let modulus = Formula::Int(1i128 << width);
        Formula::Ite(
            Box::new(Formula::Eq(Box::new(x), Box::new(Formula::Int(0)))),
            Box::new(Formula::Int(0)),
            Box::new(Formula::Add(Box::new(neg), Box::new(modulus))),
        )
    } else {
        return None;
    };
    Some((dest, value))
}

/// The std UNSIGNED `div_ceil` inherent methods, one per receiver, with that
/// receiver's width (pointer-width `usize` at the pinned 64-bit target, as
/// `Ty::int_width` and `callee_summaries::std_num_impl_receiver_width` read it).
/// Primitive-scalar inherent methods, so the whole rendering before an optional
/// trailing turbofish is fixed by the callee's `DefId` — the doc rule of
/// [`trust_types::callee_key::sysroot_exact_path`]. Signed `iN::div_ceil` is
/// unstable (`int_roundings`) and is deliberately absent: it also panics on
/// `MIN.div_ceil(-1)` and rounds toward +inf for negative quotients, a different
/// definition this lane does not state. `u128` is absent: its operands exceed the
/// `i128`-backed Int literal lane the sibling exact-value models also decline.
const UNSIGNED_DIV_CEIL_PATHS: &[(&str, u32)] = &[
    ("core::num::<impl u8>::div_ceil", 8),
    ("core::num::<impl u16>::div_ceil", 16),
    ("core::num::<impl u32>::div_ceil", 32),
    ("core::num::<impl u64>::div_ceil", 64),
    ("core::num::<impl usize>::div_ceil", 64),
];

const UNSIGNED_DIV_CEIL_PATH_NAMES: &[&str] = &[
    "core::num::<impl u8>::div_ceil",
    "core::num::<impl u16>::div_ceil",
    "core::num::<impl u32>::div_ceil",
    "core::num::<impl u64>::div_ceil",
    "core::num::<impl usize>::div_ceil",
];

/// If `terminator` is a std unsigned `a.div_ceil(b)` call (`u8`..=`u64`, `usize`)
/// whose destination is an unsigned integer of the receiver's width, the fact
/// that pins that destination (named by `dest_var`) to its EXACT value:
///
/// ```text
/// b != 0  ⇒  dest * b >= a  ∧  dest * b < a + b
/// ```
///
/// over the mathematical integers (the Int sort: the products and sums are not
/// machine operations and cannot wrap).
///
/// SOUNDNESS. `library/core/src/num/uint_macros.rs` defines
/// `div_ceil(self, rhs)` as `let d = self / rhs; let r = self % rhs; if r > 0 { d + 1 }
/// else { d }`: the ceiling of `self / rhs` (`d + 1` never overflows — `r > 0`
/// forces `rhs >= 2`, so `d <= MAX / 2`). For `a >= 0` and `b >= 1`,
/// `dest = ceil(a / b)` iff `b * (dest - 1) < a <= b * dest`, which is the
/// consequent above — a DEFINITION, not a bound: exactly one integer satisfies
/// it. The ONLY other behavior is the `rhs == 0` panic, which this fact does not
/// model away: the call does not return there, so a fact about its destination
/// holds on every execution that reaches a reader of it, and the zero divisor is
/// charged on its own by `panic_calls::divzero_call` (a `DivisionByZero` row on
/// the call block, which this fact — about the post-call destination — cannot
/// discharge). The `b != 0` antecedent keeps the fact from saying anything at the
/// zero divisor: unguarded, the two bounds contradict each other at `b == 0`,
/// a vacuity this must never introduce.
///
/// WHY NOT `dest == (a + b - 1) / b`. That is the same value, but every `Div`
/// lowers through the signed `mod` encoding, and ay's strict certification
/// rejects an UNSAT proof that reasons through it (`unverified-trust-rule`):
/// with it, `n <= 2^16 ⇒ n.div_ceil(8) < 2^28` and `ensures result <= 32` over
/// `u8::div_ceil(8)` stayed UNKNOWN. For a constant divisor the characterization
/// is linear. (The hand-written `(n + 7) / 8` proves for the same reason: its
/// `Div` rvalue also carries the linear `quotient <= dividend` fact.)
///
/// ANCHOR. The callee must be one of [`UNSIGNED_DIV_CEIL_PATHS`] under a
/// real-sysroot [`trust_types::CalleeKey`] (`sysroot_exact_path`): a user
/// `fn div_ceil` or a generic argument spelling one matches nothing and the dest
/// stays havoc'd (a false value definition would be a false-PROVE channel). The
/// path's declared width must equal the destination's resolved width and both
/// operands must resolve to integers — the exact-value agreement rule of
/// `wrapping_neg_call_dest_value`, fail-closed on any disagreement.
pub(super) fn div_ceil_call_dest_fact(
    func: &VerifiableFunction,
    terminator: &Terminator,
    dest_var: &Formula,
) -> Option<Formula> {
    let (_, a, b) = div_ceil_call_operands(func, terminator)?;
    Some(div_ceil_fact_from_operands(dest_var, a, b))
}

pub(super) fn div_ceil_fact_from_operands(dest_var: &Formula, a: Formula, b: Formula) -> Formula {
    let scaled = Formula::Mul(Box::new(dest_var.clone()), Box::new(b.clone()));
    Formula::Implies(
        Box::new(Formula::Not(Box::new(Formula::Eq(
            Box::new(b.clone()),
            Box::new(Formula::Int(0)),
        )))),
        Box::new(Formula::And(vec![
            Formula::Ge(Box::new(scaled.clone()), Box::new(a.clone())),
            Formula::Lt(Box::new(scaled), Box::new(Formula::Add(Box::new(a), Box::new(b)))),
        ])),
    )
}

/// The recognizer behind [`div_ceil_call_dest_fact`]: the destination place and
/// the two operand formulas of a std unsigned `div_ceil` call, or `None` (see the
/// ANCHOR paragraph there for every gate).
pub(super) fn div_ceil_call_operands<'a>(
    func: &VerifiableFunction,
    terminator: &'a Terminator,
) -> Option<(&'a Place, Formula, Formula)> {
    let Terminator::Call { func: callee, args, dest, callee_key, .. } = terminator else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    if !dest.projections.is_empty() {
        return None;
    }
    let path = trust_types::callee_key::sysroot_exact_path(
        callee_key.as_ref(),
        callee,
        UNSIGNED_DIV_CEIL_PATH_NAMES,
    )?;
    let declared = UNSIGNED_DIV_CEIL_PATHS.iter().find(|(p, _)| *p == path).map(|(_, w)| *w)?;
    if !matches!(
        crate::local_ty_ref(func, dest.local),
        Some(Ty::Int { width, signed: false }) if *width == declared
    ) || !args.iter().all(|arg| {
        crate::operand_ty_cow(func, arg).as_deref().is_some_and(|t| t.int_width().is_some())
    }) {
        return None;
    }
    Some((
        dest,
        crate::operand_to_formula(func, &args[0]),
        crate::operand_to_formula(func, &args[1]),
    ))
}

/// Recognize a std float BIT-REINTERPRETATION intrinsic on a `Terminator::Call`
/// — `f64::to_bits`/`f32::to_bits` (float → u{w}) and
/// `f64::from_bits`/`f32::from_bits` (u{w} → float) — and return the EXACT
/// value-definition fact tying the call's dest to the SHARED bitvector symbol of
/// its operand. Covers BOTH the method spelling (`v.to_bits()`) and the UFCS /
/// fully-qualified spelling (`f64::to_bits(v)`): both lower to the identical
/// `Terminator::Call` (same callee path, one arg), so matching on the callee path
/// + arity is spelling-agnostic — exactly as the `wrapping_*`/`saturating_*`
/// family recognizers do.
///
/// SOUNDNESS — this is an EXACT model, NOT an over-approximation. `to_bits` /
/// `from_bits` are pure REINTERPRETATIONS of the same storage bits: they copy the
/// 64-/32-bit pattern VERBATIM, with NO rounding, NO value conversion, and NO
/// NaN normalization at the value level (the bit pattern is preserved exactly).
/// The float local ALREADY holds its IEEE-754 bit pattern as a single
/// `Sort::BitVec(width)` symbol (`sort_for_ty(Ty::Float{w}) == BitVec(w)`), and
/// that SAME symbol is what the float-comparison lowering reads under `FpFromBits`
/// (`guards::fp_operand`). Reusing it here re-correlates the two lanes:
///   * `to_bits(v)`: `dest(u{w}: Int) == bv2int(v_bits)` — the unsigned-int dest
///     equals the unsigned value of `v`'s shared bitvector. So an fp fact over the
///     same bitvector constrains the int lane: e.g. `v != 0.0`
///     (`fp.eq(fp_from_bits(v_bits), +0.0)` false) forces `v_bits != 0`, hence
///     `bits != 0`, so `bits - 1` provably cannot underflow (the crown_deep
///     `f64_next_up_compat` shape).
///   * `from_bits(b)`: `dest_bits == int2bv(b)` — the float dest's bitvector IS
///     the u-int argument reinterpreted, the inverse identity.
///
/// CRATE-ORIGIN anchored (`core::`/`std::`/`alloc::` + a `::f64::`/`::f32::`
/// segment) exactly like `fp_abs_call_width`, so a user-defined `mymod::to_bits`
/// is NOT matched (that would inject a false value-definition — a false-PROVE
/// channel). Fail-closed to `None` on any mismatch (dest stays free → at worst a
/// missed proof, never a wrong one). The width-typed operand/dest gate keeps a
/// spoofed path from binding an ill-typed dest.
pub(super) fn float_bits_call_dest_fact(
    func: &VerifiableFunction,
    terminator: &Terminator,
) -> Option<Formula> {
    let Terminator::Call { func: callee, args, dest, .. } = terminator else {
        return None;
    };
    if !dest.projections.is_empty() || args.len() != 1 {
        return None;
    }
    let std_origin = callee.starts_with("core::")
        || callee.starts_with("std::")
        || callee.starts_with("alloc::");
    if !std_origin {
        return None;
    }
    let last = callee.rsplit("::").next()?;
    let method = last.split('<').next().unwrap_or(last).trim();
    if !matches!(method, "to_bits" | "from_bits") {
        return None;
    }
    let width = if callee.contains("::f64::") {
        64u32
    } else if callee.contains("::f32::") {
        32u32
    } else {
        return None;
    };
    match method {
        // float → u{w}. The dest is INT-sorted (source-level integer VCs use
        // mathematical Int); it equals the UNSIGNED reinterpretation
        // (`bv2int`) of the operand's IEEE bitvector — the SAME
        // `Var(v, BitVec(w))` the fp comparisons read. `operand_to_formula`
        // yields exactly that symbol for a float local (and the correct constant
        // bitvector for a float literal). The operand type gate confirms the
        // width and rejects a non-float arg (fail-closed).
        "to_bits" => {
            match crate::operand_ty_cow(func, &args[0]).as_deref() {
                Some(Ty::Float { width: w }) if *w == width => {}
                _ => return None,
            }
            let dest_name = crate::place_to_var_name(func, dest);
            let v_bits = crate::operand_to_formula(func, &args[0]);
            Some(Formula::Eq(
                Box::new(Formula::Var(dest_name, Sort::Int)),
                Box::new(Formula::BvToInt(Box::new(v_bits), width, false)),
            ))
        }
        // u{w} → float. The dest is BitVec(w)-sorted (its IEEE bit pattern); it
        // equals the u-int argument reinterpreted as bits (`int2bv`). The dest
        // type gate confirms the width and rejects a non-float dest.
        "from_bits" => {
            match crate::local_ty_ref(func, dest.local) {
                Some(Ty::Float { width: w }) if *w == width => {}
                _ => return None,
            }
            let dest_name = crate::place_to_var_name(func, dest);
            let arg = crate::operand_to_formula(func, &args[0]);
            Some(Formula::Eq(
                Box::new(Formula::Var(dest_name, Sort::BitVec(width))),
                Box::new(Formula::IntToBv(Box::new(arg), width)),
            ))
        }
        _ => None,
    }
}

#[cfg(test)]
mod ord_method_spelling_tests {
    use super::ord_method;

    /// The spellings `ord_method` DOES recognize. Both the free function and the
    /// fully-qualified trait-impl form resolve to the method name.
    #[test]
    fn recognized_spellings() {
        assert_eq!(ord_method("core::cmp::max"), Some("max"));
        assert_eq!(ord_method("core::cmp::min"), Some("min"));
        assert_eq!(ord_method("<u32 as core::cmp::Ord>::max"), Some("max"));
        assert_eq!(ord_method("core::cmp::Ord::clamp"), Some("clamp"));
    }

    /// MEASURED GAP, pinned so it is a known boundary rather than a surprise.
    ///
    /// `trust-mir-extract` writes a monomorphized free-function call as
    /// `core::cmp::max::<u32>` (verified against the extracted MIR of
    /// `tests/fixtures/hv_havoc_decline_fx.rs`), and `ord_method` splits the path
    /// on `::` and takes the LAST segment — which for that spelling is `<u32>`,
    /// not `max`. So the `Ord::min/max` result model does NOT fire on the form
    /// the compiler actually emits for `core::cmp::max(x, 1)`.
    ///
    /// Closing this is a fact-ADDING change (it makes the verifier assume a bound
    /// it does not assume today) and belongs in its own review, not in a
    /// drop-only reclassification pass.
    #[test]
    fn turbofish_free_function_spelling_is_not_recognized_today() {
        assert_eq!(ord_method("core::cmp::max::<u32>"), None);
        assert_eq!(ord_method("core::cmp::min::<usize>"), None);
    }

    /// The comparator-taking variants must stay unrecognized in every spelling:
    /// their result bound depends on the closure, so assuming `min` semantics
    /// would be UNSOUND.
    #[test]
    fn comparator_variants_are_never_recognized() {
        for callee in [
            "core::cmp::min_by",
            "core::cmp::max_by_key",
            "<u32 as core::cmp::Ord>::min_by",
            "core::cmp::Ord::max_by_key",
        ] {
            assert_eq!(ord_method(callee), None, "{callee} is comparator-dependent");
        }
    }

    /// A user function that merely spells `min` is not `core::cmp::min`.
    #[test]
    fn user_paths_are_not_credited() {
        assert_eq!(ord_method("mycrate::util::min"), None);
        assert_eq!(ord_method("mycrate::cmp::min"), None);
    }
}

#[cfg(test)]
mod lossless_conversion_tests {
    use trust_types::Ty;

    use super::{declared_ty_is_primitive, std_lossless_scalar_conversion};

    /// `usize`/`isize` are the faithful `PtrSizedInt` or the `Int` carrier at a
    /// real pointer width; an `Int` at any other width is a different type and
    /// must not authenticate a pointer-width conversion.
    #[test]
    fn pointer_width_carrier_is_pinned_to_real_pointer_widths() {
        for w in [16, 32, 64] {
            assert!(declared_ty_is_primitive(&Ty::Int { width: w, signed: false }, "usize"));
            assert!(declared_ty_is_primitive(&Ty::Int { width: w, signed: true }, "isize"));
        }
        assert!(declared_ty_is_primitive(&Ty::PtrSizedInt { signed: false }, "usize"));
        assert!(declared_ty_is_primitive(&Ty::PtrSizedInt { signed: true }, "isize"));
        for w in [1, 8, 128] {
            assert!(!declared_ty_is_primitive(&Ty::Int { width: w, signed: false }, "usize"));
            assert!(!declared_ty_is_primitive(&Ty::Int { width: w, signed: true }, "isize"));
        }
        assert!(!declared_ty_is_primitive(&Ty::Int { width: 64, signed: true }, "usize"));
        assert!(!declared_ty_is_primitive(&Ty::PtrSizedInt { signed: true }, "usize"));
    }

    /// Both spellings of the closed table resolve; narrowing, reflexive and
    /// user-crate spellings do not.
    #[test]
    fn recognizer_admits_only_the_closed_table() {
        assert_eq!(
            std_lossless_scalar_conversion("<i64 as core::convert::From<i32>>::from"),
            Some(("i32", "i64"))
        );
        assert_eq!(
            std_lossless_scalar_conversion("<char as core::convert::Into<u32>>::into"),
            Some(("char", "u32"))
        );
        for callee in [
            "<u32 as core::convert::From<u64>>::from",
            "<u64 as core::convert::From<u64>>::from",
            "<i32 as core::convert::From<u32>>::from",
            "<u16 as core::convert::From<char>>::from",
            "<usize as core::convert::From<u32>>::from",
            "<u64 as mycrate::convert::From<u32>>::from",
        ] {
            assert_eq!(std_lossless_scalar_conversion(callee), None, "{callee}");
        }
    }
}

/// Trust (2026-10-05, VEC_FROM_ELEM_LEN): on the success edge of `v = alloc::vec::from_elem(x, n)`
/// — the `vec![x; n]` macro, tagged `SysrootItem::VecFromElem` from a real-sysroot `DefId` —
/// the length abstraction of `v` (its own name, `guards::coll_len_var`) equals `n`.
///
/// VERSIONING. The fact names `v` by the token the statement oracle gives it at the
/// TARGET block's entry, not by an assumed `s{b}_t`: a later `Drop(v)` writes `v*`, a
/// descendant name that rebinds the read `v`, so the oracle spells `v` there as the join
/// `e_s{b}_t` (measured, `vec![7u8; n]` then `v[i]`). Nothing runs between the call's
/// return and that point, so the value that token denotes on this edge is the call's
/// result, and the fact is a semantic guard: it rides only success edges and is weakened
/// at any join one of whose predecessors lacks it, so the unwind path (where `v` was
/// never written) cannot carry it. `n` is versioned at the call. Every gate miss emits
/// nothing.
///
/// Two gates from the 2026-10-05 adversarial review, each closing a confirmed false
/// proof:
///  * the success TARGET has the call block as its SOLE predecessor. Returning straight
///    into a loop header made the target-entry token the header's PHI, which also covers
///    the values reaching around the back edge (`v.clear()` in the loop), and a back edge
///    that adds no facts does not weaken the guard. With one predecessor the token at
///    the target denotes the call's result, and a later read through the header gets a
///    different (join) token, so the fact does not connect there;
///  * the body mentions NO `ConstValue::OpaqueScalar`. Such a constant (an associated
///    const or `size_of` in a generic body) carries no occurrence identity, so
///    `vec![x; B::N]` and a guard `i < A::N` would share one SMT term and this fact would
///    bridge two different values (`f::<Ten, One>(5)` panics).
pub(crate) fn vec_from_elem_len_facts(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    vec_from_elem_len_fact(sv, func, block).into_iter().collect()
}

fn vec_from_elem_len_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<Formula> {
    let Terminator::Call { args, dest, target: Some(target), callee_key: Some(key), .. } =
        &block.terminator
    else {
        return None;
    };
    if !key.krate_is_real_sysroot
        || key.sysroot_item != Some(trust_types::SysrootItem::VecFromElem)
        || args.len() != 2
        || target.0 == 0
        || !dest.projections.is_empty()
        || !crate::guards::place_is_std_vec(func, dest)
    {
        return None;
    }
    let count = &args[1];
    if !matches!(crate::operand_ty_cow(func, count)?.as_ref(), Ty::Int { signed: false, .. }) {
        return None;
    }
    if !sole_predecessor_is(func, *target, block.id) || body_mentions_opaque_scalar(func) {
        return None;
    }
    let dest_name = place_to_var_name(func, dest);
    if super::block_defs::terminator_args_read_name(func, args, &dest_name) {
        return None;
    }
    let tok = sv.version_token_at(func, *target, 0, &dest_name)?;
    let n = version_rename_owned_at(
        crate::operand_to_formula(func, count),
        sv,
        func,
        block.id,
        block.stmts.len(),
    );
    Some(Formula::Eq(Box::new(Formula::Var(format!("{dest_name}#{tok}"), Sort::Int)), Box::new(n)))
}

/// Whether block `target`'s only CFG predecessor (normal and unwind edges) is `from`.
/// `bb0` never qualifies: it also has the implicit function-entry edge.
pub(super) fn sole_predecessor_is(
    func: &VerifiableFunction,
    target: trust_types::BlockId,
    from: trust_types::BlockId,
) -> bool {
    if target.0 == 0 {
        return false;
    }
    if let Some(ans) = crate::fn_memo::sole_predecessors(func)
        .and_then(|table| table.sole_predecessor_is(target, from))
    {
        return ans;
    }
    let mut preds = func.body.blocks.iter().filter(|b| b.terminator.has_in_cfg_successor(target));
    preds.next().is_some_and(|b| b.id == from) && preds.next().is_none()
}

/// Whether any `ConstValue::OpaqueScalar` occurs anywhere in `func`'s body (all blocks,
/// dead blocks and nested `StructScalarFieldsRef` carriers included), using `trust_types`'s
/// exhaustive wildcard-free AST traversal and memoized per function in `fn_memo`.
pub(crate) fn body_mentions_opaque_scalar(func: &VerifiableFunction) -> bool {
    crate::fn_memo::body_mentions_opaque_scalar(func, || func.body.contains_opaque_scalar())
}

/// Trust (2026-10-05, MEM_REPLACE_SWAP): the exact effect of `core::mem::replace` and
/// `core::mem::swap` on the places their `&mut` arguments borrow, as semantic guards on
/// the call's success edge:
///
/// ```text
///   old = replace(&mut P, new)  ⇒  P_after == new  ∧  old == P_before
///   swap(&mut P, &mut Q)        ⇒  P_after == Q_before  ∧  Q_after == P_before
///   old = take(&mut P)          ⇒  P_after == 0    ∧  old == P_before
/// ```
///
/// `take` is `replace(&mut P, T::default())`; at the two admitted types the default's
/// abstraction is `0` (an integer's value, an empty `Vec`'s length).
///
/// Value equality implies equality of every per-name abstraction of a value of the same
/// type (an integer's value, a std `Vec`'s length), so the facts are stated over the
/// places' own names. `P_before` is versioned at the call; `P_after` and `old` by the
/// token the statement oracle gives them at the success TARGET's entry, as
/// [`vec_from_elem_len_facts`] does, under the same gates (the target's sole predecessor
/// is the call block, never `bb0`; no identity-less `OpaqueScalar` in the body). Each
/// argument must be the one value `&mut P` of a whole local, with `P` itself a WHOLE local
/// (no projection) of integer or std `Vec` type; `replace`'s destination is never `P`'s
/// local. A field, a union member, or a place behind a reference (`&mut self.f`) is NOT
/// modeled. The after-token must DIFFER from
/// the before-token: a place the oracle did not version across the call would make
/// `P == new` and `old == P` one name and could render an obligation vacuous.
pub(crate) fn mem_replace_swap_facts(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    mem_replace_swap_facts_inner(sv, func, block).unwrap_or_default()
}

fn mem_replace_swap_facts_inner(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<Vec<Formula>> {
    use trust_types::SysrootItem as S;
    let Terminator::Call { args, dest, target: Some(target), callee_key: Some(key), .. } =
        &block.terminator
    else {
        return None;
    };
    let item = key.sysroot_item?;
    if !key.krate_is_real_sysroot
        || !matches!(item, S::MemReplace | S::MemSwap | S::MemTake)
        || args.len() != if item == S::MemTake { 1 } else { 2 }
        || target.0 == 0
        || (matches!(item, S::MemReplace | S::MemTake) && !dest.projections.is_empty())
    {
        return None;
    }
    // `(before, after)` for the place the `&mut` operand borrows. Checked before the
    // whole-CFG `sole_predecessor_is` and whole-body `body_mentions_opaque_scalar`
    // scans so projected borrows (`&mut self.field`) and non-tracked ADTs decline in O(1).
    let resolve_borrowed_place = |op: &Operand| -> Option<&Place> {
        let (Operand::Copy(r) | Operand::Move(r)) = op else { return None };
        if !r.projections.is_empty() {
            return None;
        }
        let Some(Rvalue::Ref { mutable: true, place }) =
            crate::local_defs::unique_value_def(func, r.local)
        else {
            return None;
        };
        // A WHOLE LOCAL only. Three adversarial reviews (2026-10-05) found four false
        // proofs on projected places: three through a `Deref` (the pointer reseated in the
        // argument block, through a reborrow, or through a raw alias, so the name `r*` spelled
        // memory other than what `&mut *r` borrowed) and one through a UNION field (`u.b = x`
        // overwrites the bytes `u.a` names, but the versioning treats sibling fields as
        // independent, so `old` read a stale value). A local's own name always denotes its
        // own storage.
        if !place.projections.is_empty() {
            return None;
        }
        let ty = crate::local_ty_ref(func, place.local)?;
        let tracked =
            matches!(ty, Ty::Int { .. }) || crate::guards::place_is_std_vec(func, place);
        tracked.then_some(place)
    };
    let place_versions = |place: &Place| -> Option<(Formula, Formula)> {
        let name = place_to_var_name(func, place);
        let after_tok = sv.version_token_at(func, *target, 0, &name)?;
        let after = Formula::Var(format!("{name}#{after_tok}"), Sort::Int);
        let before = version_rename_owned_at(
            Formula::Var(name, Sort::Int),
            sv,
            func,
            block.id,
            block.stmts.len(),
        );
        (after != before).then_some((before, after))
    };
    let p_place = resolve_borrowed_place(&args[0])?;
    match item {
        S::MemReplace | S::MemTake => {
            // The destination must not be `P`'s own local (`x = replace(&mut x, 5)` stores
            // the OLD value back into `x` after the callee wrote `new`). rustc's MIR building
            // routes such a call through a temporary today; the gate makes it explicit.
            if p_place.local == dest.local
                || args.get(1).is_some_and(|a| {
                    matches!(a, Operand::Copy(r) | Operand::Move(r)
                        if matches!(crate::local_defs::unique_value_def(func, r.local),
                            Some(Rvalue::Ref { place, .. }) if place.local == dest.local))
                })
            {
                return None;
            }
            if !sole_predecessor_is(func, *target, block.id) || body_mentions_opaque_scalar(func) {
                return None;
            }
            let (p_before, p_after) = place_versions(p_place)?;
            let dest_name = place_to_var_name(func, dest);
            if super::block_defs::terminator_args_read_name(func, args, &dest_name) {
                return None;
            }
            let dest_tok = sv.version_token_at(func, *target, 0, &dest_name)?;
            // `take(p)` is `replace(p, T::default())`, and `place_versions` admitted only
            // the two types whose default it models: an integer's `0` and a std `Vec`'s
            // length `0` (the name of a tracked `Vec` stands for its length).
            let new = if item == S::MemTake {
                Formula::Int(0)
            } else {
                version_rename_owned_at(
                    crate::operand_to_formula(func, &args[1]),
                    sv,
                    func,
                    block.id,
                    block.stmts.len(),
                )
            };
            let old = Formula::Var(format!("{dest_name}#{dest_tok}"), Sort::Int);
            Some(vec![
                Formula::Eq(Box::new(p_after), Box::new(new)),
                Formula::Eq(Box::new(old), Box::new(p_before)),
            ])
        }
        S::MemSwap => {
            let q_place = resolve_borrowed_place(&args[1])?;
            if !sole_predecessor_is(func, *target, block.id) || body_mentions_opaque_scalar(func) {
                return None;
            }
            let (p_before, p_after) = place_versions(p_place)?;
            let (q_before, q_after) = place_versions(q_place)?;
            Some(vec![
                Formula::Eq(Box::new(p_after), Box::new(q_before)),
                Formula::Eq(Box::new(q_after), Box::new(p_before)),
            ])
        }
        _ => None,
    }
}

// Trust (2026-10-04, wave 13): test modules sit at the END of the file, so the
// `local_defs_seam_lint` test-module mask (which runs from a braceless `mod x;` to
// the next closing brace) cannot swallow a production function.
#[cfg(test)]
#[path = "bool_from_anchor_tests.rs"]
mod bool_from_anchor_tests;

/// The extractor-shaped `callee_key`s hand-built unit-test calls need now that the
/// wave-13 recognizers decide on the key (see the module doc).
#[cfg(test)]
#[path = "sysroot_callee_key_fixture_tests.rs"]
pub(super) mod sysroot_callee_key_fixture;
