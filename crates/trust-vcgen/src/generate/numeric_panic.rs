// Trust (2026-09-25, std-numeric-family): the std numeric methods that PANIC on a
// caller-supplied argument VALUE and that no call-site recognizer charged. Each
// built rc=0 on the default lane (stage-1 of origin/main `8d6aadf7e9`) with a
// verify-off driver feeding the panicking value, and exited 101. The audit
// table, with the before/after of every row, is the CLOSED entry "the std
// numeric methods that panic on an argument value were accepted" in
// `docs/KNOWN_HAZARDS.md`.
//
// WHY THEY WERE ACCEPTED. Their panic lives INSIDE the library — an `assert!`
// (`Ord::clamp`, `f64::clamp`, `char::to_digit`, `ilog`'s base), a call to a
// `#[cold]` panic helper (`ilog2`/`ilog10`/`isqrt` on a non-positive value,
// `from_str_radix`'s radix), or core's own overflow check behind
// `#[rustc_inherit_overflow_checks]` (`next_power_of_two`, `next_multiple_of`).
// The caller's MIR carries no `Assert` for any of them, the bundled member's
// internal check is REPORTED (not failed) under the default policy — it is
// core's retained runtime check — and so the caller's argument was never
// charged. The rows here charge it AT THE CALL SITE, where the argument is the
// caller's own value, exactly as `divzero_call` does for `div_euclid`.
//
// THE NIGHTLY SURFACE (Trust, NUM-NIGHTLY-UNCHARGED-1, 2026-10-06). The audit
// above covered stable methods only. The nightly methods of the same class —
// the signed `next_multiple_of` (`int_roundings`), `funnel_shl`/`funnel_shr`
// (`funnel_shifts`), `strict_cast`/`strict_cast_signed`/`strict_cast_unsigned`
// (`integer_casts`, `integer_cast_extras`) and `Duration::from_days`/
// `from_weeks` (`duration_constructors`) — built rc=0 on the default lane of
// the stage 1 of `9e11546767` and panicked on the caller's value; they are
// charged here by the same rule. (The census of the sysroot's unstable
// panicking numeric methods also names `div_floor`/`div_ceil`/`div_exact`,
// measured refused by other lanes on that stage 1, and `from_ascii_radix`,
// which ASCII-FROM-ASCII-RADIX-1 charges.)
//
// THREE DISPOSITIONS, per argument shape:
//
//   * PRECISE — a linear failure condition over the argument(s), keyed by
//     `block.id` so it inherits the block-defs / path-guard / precondition
//     machinery: `if lo <= hi { x.clamp(lo, hi) }` PROVES, an unguarded call is
//     REFUTED with a counterexample. The kind is an `Assertion` (the check is
//     std's own and stays in the binary, like `BTreeMap::range`'s), or
//     `DivisionByZero` for a zero divisor.
//   * FAIL-CLOSED — an `UnsupportedMir` row (no runtime fallback, so the
//     default policy refuses it) where no sound linear model exists: a float
//     bound that could be NaN, an `Ord::clamp` over a non-primitive type, a
//     `Duration` computed from an `f64`, `Duration`/`Instant` arithmetic whose
//     operands are not literal.
//   * DECIDED — an argument whose failure the recognizer settles from literals:
//     a literal radix, literal clamp bounds, a literal `Duration` sum, product
//     or nonzero divisor, a small literal added to a fresh `now()`. The row is
//     minted EITHER WAY with the decided value as its violation (`decided_row`):
//     `true` is refuted, `false` proves. (Until 2026-10-02 a decided-safe
//     argument minted NOTHING, which emptied the call's inventory and let
//     `certify` pass a function on zero proved rows.)
//
// IDENTITY. Every recognizer anchors on an AUTHENTICATED sysroot root
// (`trust_types::path_root_is_authenticated_sysroot_crate`: a stamped
// impersonator crate is refused) plus the exact owner and the method leaf
// (`method_tail`, arrow-aware). Trait methods are read through the qualified
// spelling `<Self as Trait>::m` with BOTH halves checked: the trait path is
// matched exactly (generics stripped) and the self type decides the model. A
// user method that merely shares a name (`MyInt::ilog2`) has a different owner
// and never matches.
//
// A STAMPED GENUINE CORE (Trust, wave 23, STAMPED-CORE-MINT-1 residual,
// 2026-10-11). The two minting functions, `numeric_value_panic_row` and
// `numeric_overflow_call`, first read past ONE well-formed leading extractor stamp
// (`after_one_identity_stamp`) and then authenticate the rest as above, because the
// extractor stamps the real core whenever a second crate named `core` is in the
// graph, or under `-Zbuild-std`. The name-only `is_numeric_value_panic_callee` and
// the grants (`is_clock_reading_callee`, the literal-`Duration` reader) do not.

use super::*;

/// The width of a primitive integer spelling.
///
/// Trust (W32-PRIMINT-PIN-1, 2026-10-06): `usize` and `isize` are POINTER-sized.
/// Their width is the TARGET's pointer width, 16, 32 or 64 bits, and a rendered
/// name does not carry it. This table used to give them 64, "the pinned 64-bit
/// target", while `ranged` ranged the operand at its declared carrier, which the
/// extractor mints at the real width (`Int { width: 32 }` on i686 and wasm32).
/// Each 32-bit violation formula then asked for a 64-bit threshold the operand
/// cannot reach, so it was UNSAT, and the panic row was published `proved`
/// (Certified, KernelRechecked) for calls that panic: `x.next_power_of_two()` at
/// `usize::MAX`, `x.strict_neg()` at `isize::MIN`, `x.strict_shl(35)`. A
/// pointer-sized owner's width is now read per call, from the declared carrier of
/// the operand the row is about ([`resolve_owner_width`]), and never assumed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum IntWidth {
    /// `u8`..`u128`, `i8`..`i128`: the same width on every target.
    Fixed(u32),
    /// `usize`, `isize`: the target's pointer width.
    Pointer,
}

/// The primitive integer spellings rustc renders inside an inherent-impl owner
/// (`core::num::<impl u32>::…`), with their width and their signedness.
const PRIMITIVE_INTS: [(&str, IntWidth, bool); 12] = [
    ("u8", IntWidth::Fixed(8), false),
    ("u16", IntWidth::Fixed(16), false),
    ("u32", IntWidth::Fixed(32), false),
    ("u64", IntWidth::Fixed(64), false),
    ("u128", IntWidth::Fixed(128), false),
    ("usize", IntWidth::Pointer, false),
    ("i8", IntWidth::Fixed(8), true),
    ("i16", IntWidth::Fixed(16), true),
    ("i32", IntWidth::Fixed(32), true),
    ("i64", IntWidth::Fixed(64), true),
    ("i128", IntWidth::Fixed(128), true),
    ("isize", IntWidth::Pointer, true),
];

/// `(width, signed)` of a primitive integer spelling.
fn primitive_int(name: &str) -> Option<(IntWidth, bool)> {
    PRIMITIVE_INTS.iter().find(|(n, ..)| *n == name.trim()).map(|(_, w, s)| (*w, *s))
}

/// The pointer widths, in bits, that a target can have. These are the carriers
/// the extractor mints for `usize`, and `call_facts::declared_ty_is_primitive`
/// pins the same set.
const POINTER_WIDTHS: [u32; 3] = [16, 32, 64];

/// The width an arm that never READS a pointer-sized owner's width passes to
/// `ranged`, which uses it only for an operand it cannot type. This is the widest
/// pointer width. In this module a range is only ever a conjunct of a violation
/// formula, so a wider one can only refuse more.
const POINTER_WIDTH_RANGE_FALLBACK: u32 = 64;

/// The TARGET pointer width that `op`, an operand of a pointer-sized type, is
/// declared at: `Some(w)` iff its declared carrier is `Ty::Int { width: w, signed }`
/// with `w` in [`POINTER_WIDTHS`] and the expected signedness.
///
/// Only a DECLARED width counts:
///   * a place's declared type;
///   * an unsigned literal (`ConstValue::Uint(_, w)`), which the extractor mints
///     at the target width;
///   * an opaque or const-generic scalar, whose declared width it carries.
///
/// Each of these answers `None`:
///   * a signed literal (`ConstValue::Int`). It carries no width, and `operand_ty`
///     types it i64 (or i128) on every target.
///   * a `Symbolic` operand, whose sort is not a declaration.
///   * the faithful `Ty::PtrSizedInt`. Its `int_width` is the pinned 64, not the
///     target's.
///   * any other width.
pub(super) fn declared_pointer_width(
    func: &VerifiableFunction,
    op: &Operand,
    signed: bool,
) -> Option<u32> {
    let (w, s) = match op {
        Operand::Copy(_) | Operand::Move(_) => match crate::operand_ty_cow(func, op)?.as_ref() {
            Ty::Int { width: w, signed: s } => (*w, *s),
            _ => return None,
        },
        Operand::Constant(ConstValue::Uint(_, w)) => (*w, false),
        Operand::Constant(
            ConstValue::OpaqueScalar { width: w, signed: s, .. }
            | ConstValue::ConstParam { width: w, signed: s, .. },
        ) => (*w, *s),
        _ => return None,
    };
    (POINTER_WIDTHS.contains(&w) && s == signed).then_some(w)
}

/// The width a row for a primitive owner of width `width` is built at, at this
/// call. A fixed-width owner is its own width. A pointer-sized owner is the
/// declared pointer width of `carrier` ([`declared_pointer_width`]), the operand
/// whose type IS `Self`: the receiver, or `*self` for a compound-assign call.
///
/// When that width is unresolved:
///   * a row that READS the width (`reads_width`) gets `None`, and the caller
///     refuses it with [`pointer_width_unresolved`]. It is never built at an
///     assumed 64 bits.
///   * a row that does not read it gets [`POINTER_WIDTH_RANGE_FALLBACK`].
pub(super) fn resolve_owner_width(
    func: &VerifiableFunction,
    width: IntWidth,
    signed: bool,
    carrier: Option<&Operand>,
    reads_width: bool,
) -> Option<u32> {
    match width {
        IntWidth::Fixed(w) => Some(w),
        IntWidth::Pointer => carrier
            .and_then(|op| declared_pointer_width(func, op, signed))
            .or((!reads_width).then_some(POINTER_WIDTH_RANGE_FALLBACK)),
    }
}

/// The fail-closed row for a pointer-sized threshold whose width is unresolved.
pub(super) fn pointer_width_unresolved(what: &str) -> Option<(Formula, VcKind)> {
    unmodeled(
        "pointer-width-unresolved",
        &format!(
            "`{what}` on `usize`/`isize` panics at a threshold set by the TARGET's pointer \
             width (`BITS`, `MIN`, `MAX`), and the declared type of its operand does not fix \
             that width here: it is a faithful `PtrSizedInt`, an untyped operand, a signed \
             literal (which carries no width), or a width other than 16, 32 or 64. Refused; \
             the row is never built at an assumed 64 bits"
        ),
    )
}

/// The leaf directly after `owner_end` (`ilog2` in `…<impl u32>::ilog2::<…>`),
/// required to BE the method tail — so a nested path under the owner never reads
/// as the owner's own method.
fn leaf_after<'a>(after_owner: &'a str, callee: &'a str) -> Option<&'a str> {
    let seg = after_owner.split("::").next()?;
    let seg = seg.split('<').next()?.trim();
    let tail = method_tail(callee);
    (seg == tail && !seg.is_empty()).then_some(tail)
}

/// `core::num::<impl T>::m` (or the `std::num::` spelling) for a primitive
/// integer `T`: `(T's width, signed, m)`. A pointer-sized `T`'s width is
/// [`IntWidth::Pointer`], resolved per call by [`resolve_owner_width`].
///
/// Trust (2026-10-06): also the identity `alloc_bounds::overflow_arith_call`
/// requires before it mints `pow`'s overflow row, so `pow` and `strict_pow` are
/// recognized by the same authenticated owner.
pub(super) fn int_inherent(callee: &str) -> Option<(IntWidth, bool, &str)> {
    let rest = callee
        .strip_prefix("core::num::<impl ")
        .or_else(|| callee.strip_prefix("std::num::<impl "))?;
    if !trust_types::path_root_is_authenticated_sysroot_crate(callee) {
        return None;
    }
    let (ty, after) = rest.split_once(">::")?;
    let (width, signed) = primitive_int(ty)?;
    Some((width, signed, leaf_after(after, callee)?))
}

/// Trust (wave-19 review, 2026-10-09): [`int_inherent`] for the MINTING arms whose
/// only effect is to ADD a row over the call's own arguments: `abs`'s negation row
/// (`unwrap_panic::is_signed_abs_mint`) and the `pow` and `unchecked_{add,sub,mul}`
/// rows of `alloc_bounds::overflow_arith_call`. It also reads core's spelling behind
/// ONE leading extractor identity stamp
/// (`__trust_crate@414739228a72f04f::core::num::<impl i32>::abs`).
///
/// WHY. The extractor stamps the GENUINE core too. Rule 1 of
/// `trust_types::sysroot_identity_stamp_required` stamps every external crate whose
/// name is ambiguous, so a second crate named `core` anywhere in the graph stamps the
/// real one; and `-Zbuild-std` builds core as an ordinary dependency, which rule 2
/// stamps. A stamp says "this name could not be authenticated", not "this is an
/// impersonator". MEASURED (review of `integ/wave19`, 2026-10-09; a verify-off
/// `--crate-name core` dependency beside the sysroot, `x.abs()` in the caller): on the
/// stage 1 of `f39efe05ca` the `negation` row was refuted at `x = i32::MIN` and the
/// default build exited 1; on the stage 1 of `46e9afaf95`, which anchored `abs` on
/// [`int_inherent`] alone (ABS-NAME-1), the row was gone, the build exited 0 on a
/// `runtime_checked` row and the binary panicked "attempt to negate with overflow";
/// `unsafe { a.unchecked_add(b) }` lost its `unchecked_overflow` row the same way
/// (UNCHECKED-NAME-1), and `a.pow(e)` had lost its row since POW-SYMEXP-1.
///
/// WHY ONLY THESE ARMS. The text after the stamp must be EXACTLY what [`int_inherent`]
/// accepts (`core::num::<impl iN/uN>::leaf` or `std::num::`, with no further stamp).
/// rustc lets a crate define an inherent method on a primitive only under core's
/// `rustc_coherence_is_core`, or under `rustc_attrs` with `#[rustc_allow_incoherent_impl]`
/// on the item (`check_primitive_impl`), so the spelling is core's or a forgery that
/// needs rustc's internal attributes. A forgery can at worst be charged a row its body
/// does not owe: a false red. Nothing that GRANTS asks this. trust-clean's
/// negation-subject admission keeps `is_signed_abs_call` (authenticated), so a row
/// minted for a stamped spelling is never clean-certified.
///
/// Trust (wave 23, STAMPED-CORE-MINT-1 residual, 2026-10-11): the numeric family's
/// two MINTING functions, [`numeric_value_panic_row`] and [`numeric_overflow_call`],
/// now read past the same one leading stamp, for every spelling they recognize (the
/// int inherent owner, and also the qualified trait, float, char, `NonZero`,
/// `Duration` and `strict_cast_from` spellings). For the trait, `Duration` and
/// `NonZero` spellings the coherence argument above does NOT hold: a crate named
/// `core` can define its own `cmp::Ord::clamp`, and it renders exactly as core's
/// does. That is still only a false red, since those arms only add rows; the reasons
/// are on [`numeric_value_panic_row`]. The name-only `is_numeric_value_panic_callee`
/// keeps [`int_inherent`]: a `true` there only withholds a fn item's admission, and
/// the item spellings are already refused in a stamped graph.
pub(super) fn int_inherent_minting(callee: &str) -> Option<(IntWidth, bool, &str)> {
    if let Some(found) = int_inherent(callee) {
        return Some(found);
    }
    int_inherent(after_one_identity_stamp(callee)?)
}

/// The text after ONE well-formed leading extractor identity stamp
/// (`__trust_crate@<16 hex digits>::`), or `None` when `callee` does not start with
/// one. The text is returned as is; a caller that authenticates it
/// (`int_inherent`, `trust_types::path_root_is_authenticated_sysroot_crate`) refuses
/// a second stamp anywhere in it.
///
/// Trust (wave-21 integration, 2026-10-09): factored out of [`int_inherent_minting`]
/// so `panic_calls::divzero_call` reads past the stamp by the same rule. Only arms
/// whose sole effect is to ADD a row over the call's own arguments may use it (see
/// [`int_inherent_minting`]'s "WHY ONLY THESE ARMS"). Since wave 23 (2026-10-11),
/// [`numeric_value_panic_row`] and [`numeric_overflow_call`] read it too.
pub(super) fn after_one_identity_stamp(callee: &str) -> Option<&str> {
    let rest = callee.strip_prefix(trust_types::TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX)?;
    let (stable_crate_id, path) = rest.split_once("::")?;
    (stable_crate_id.len() == 16 && stable_crate_id.bytes().all(|b| b.is_ascii_hexdigit()))
        .then_some(path)
}

/// `core::f64::<impl f64>::m` / `core::f32::<impl f32>::m` (or `std::`): `m`.
fn float_inherent(callee: &str) -> Option<&str> {
    let after = [
        "core::f64::<impl f64>::",
        "core::f32::<impl f32>::",
        "std::f64::<impl f64>::",
        "std::f32::<impl f32>::",
    ]
    .iter()
    .find_map(|p| callee.strip_prefix(p))?;
    if !trust_types::path_root_is_authenticated_sysroot_crate(callee) {
        return None;
    }
    leaf_after(after, callee)
}

/// `core::char::methods::<impl char>::m` (or `std::`), and the free
/// `core::char::from_digit` (`std::char::from_digit`), which is the same
/// function under its module path: `m`.
fn char_method(callee: &str) -> Option<&str> {
    if !(callee.starts_with("core::char::") || callee.starts_with("std::char::"))
        || !trust_types::path_root_is_authenticated_sysroot_crate(callee)
    {
        return None;
    }
    if let Some(after) = ["core::char::methods::<impl char>::", "std::char::methods::<impl char>::"]
        .iter()
        .find_map(|p| callee.strip_prefix(p))
    {
        return leaf_after(after, callee);
    }
    let bare = vc_strip_generics_cow(callee);
    matches!(bare.as_ref(), "core::char::from_digit" | "std::char::from_digit")
        .then_some("from_digit")
}

/// `core::num::nonzero::NonZero::<T>::m` (or a `std::num::` spelling): `m`.
/// Only `from_str_radix` and (Trust, ASCII-FROM-ASCII-RADIX-1, 2026-10-05) the
/// nightly `from_ascii_radix` are charged here — every other `NonZero` method
/// named by the audit is total (`from_ascii` fixes radix 10), or reaches a
/// primitive recognizer through `get()`.
fn nonzero_inherent(callee: &str) -> Option<&str> {
    if !(callee.starts_with("core::num::") || callee.starts_with("std::num::"))
        || !trust_types::path_root_is_authenticated_sysroot_crate(callee)
    {
        return None;
    }
    let bare = vc_strip_generics_cow(callee);
    let owner = ["core::num::nonzero::NonZero::", "std::num::NonZero::", "core::num::NonZero::"]
        .iter()
        .find(|p| bare.starts_with(**p))?;
    let leaf = &bare[owner.len()..];
    let tail = method_tail(callee);
    (!leaf.contains("::") && leaf == tail).then_some(tail)
}

/// `core::time::Duration::m` (or `std::time::Duration::m`): `m`.
fn duration_inherent(callee: &str) -> Option<&str> {
    if !(callee.starts_with("core::time::Duration") || callee.starts_with("std::time::Duration"))
        || !trust_types::path_root_is_authenticated_sysroot_crate(callee)
    {
        return None;
    }
    let bare = vc_strip_generics_cow(callee);
    let owner = ["core::time::Duration::", "std::time::Duration::"]
        .iter()
        .find(|p| bare.starts_with(**p))?;
    let leaf = &bare[owner.len()..];
    let tail = method_tail(callee);
    (!leaf.contains("::") && leaf == tail).then_some(tail)
}

/// A qualified trait-method spelling `<Self as Trait>::m` whose TRAIT half is an
/// authenticated sysroot path equal (generics stripped) to one of `traits`:
/// `(Self, trait, m)`. The SELF half is returned for the caller to judge.
fn qualified_std_trait_method<'a>(
    callee: &'a str,
    traits: &[&str],
) -> Option<(&'a str, std::borrow::Cow<'a, str>, &'a str)> {
    let q = super::iterator_yield::ParsedQualifier::parse(callee)?;
    let trait_path = q.trait_path?;
    if !trait_path.starts_with("core::")
        || !trust_types::path_root_is_authenticated_sysroot_crate(trait_path)
    {
        return None;
    }
    let bare_trait = vc_strip_generics_cow(trait_path);
    if !traits.contains(&bare_trait.as_ref()) {
        return None;
    }
    Some((q.self_ty, bare_trait, method_tail(callee)))
}

struct ParsedStdTrait<'a> {
    self_ty: &'a str,
    trait_path: &'a str,
    bare_trait: std::borrow::Cow<'a, str>,
}

/// Pre-parsed callee view shared across [`numeric_overflow_call`],
/// [`numeric_value_panic_row`], and [`callee_has_call_site_panic_family`] so
/// `<Self as Trait>::method`, `method_tail`, `vc_strip_generics_cow(trait_path)`,
/// and `int_inherent` run at most once per call rather than 11+ times.
pub(super) struct NumericCallee<'a> {
    callee: &'a str,
    tail: &'a str,
    auth_sysroot_root: bool,
    int_inh: Option<(IntWidth, bool, &'a str)>,
    qual: Option<ParsedStdTrait<'a>>,
}

impl<'a> NumericCallee<'a> {
    #[inline]
    pub(super) fn for_authenticated(callee: &'a str, tail: &'a str) -> Self {
        if callee.starts_with('<') {
            let qual = if callee.contains(" as core::") {
                super::iterator_yield::ParsedQualifier::parse(callee).and_then(|q| {
                    let trait_path = q.trait_path?;
                    if !(trait_path.starts_with("core::ops::arith::")
                        || trait_path.starts_with("core::ops::bit::")
                        || trait_path.starts_with("core::cmp::Ord")
                        || trait_path.starts_with("core::convert::num::CheckedCastFromInt")
                        || trait_path.starts_with("core::iter::"))
                        || !trust_types::path_root_is_authenticated_sysroot_crate(trait_path)
                    {
                        return None;
                    }
                    Some(ParsedStdTrait {
                        self_ty: q.self_ty,
                        trait_path,
                        bare_trait: vc_strip_generics_cow(trait_path),
                    })
                })
            } else {
                None
            };
            return Self { callee, tail, auth_sysroot_root: false, int_inh: None, qual };
        }
        if !(callee.starts_with("core::") || callee.starts_with("std::")) {
            return Self { callee, tail, auth_sysroot_root: false, int_inh: None, qual: None };
        }
        let auth_sysroot_root = trust_types::path_root_is_authenticated_sysroot_crate(callee);
        let int_inh = if auth_sysroot_root
            && (callee.starts_with("core::num::<impl ") || callee.starts_with("std::num::<impl "))
        {
            int_inherent(callee)
        } else {
            None
        };
        Self { callee, tail, auth_sysroot_root, int_inh, qual: None }
    }

    #[inline]
    pub(super) fn for_minting(raw_callee: &'a str, raw_tail: &'a str) -> Self {
        let (callee, tail) = match after_one_identity_stamp(raw_callee) {
            Some(path) => (path, method_tail(path)),
            None => (raw_callee, raw_tail),
        };
        Self::for_authenticated(callee, tail)
    }

    #[inline]
    pub(super) fn int_inherent(&self) -> Option<(IntWidth, bool, &'a str)> {
        self.int_inh
    }

    #[inline]
    fn std_trait(&self, traits: &[&str]) -> Option<(&'a str, &str, &'a str, &'a str)> {
        let q = self.qual.as_ref()?;
        traits
            .contains(&q.bare_trait.as_ref())
            .then_some((q.self_ty, q.bare_trait.as_ref(), self.tail, q.trait_path))
    }

    pub(super) fn is_int_division_operator(&self) -> bool {
        let Some((self_ty, _, _, trait_path)) = self.std_trait(INT_DIV_OPS) else {
            return false;
        };
        if !int_division_operand(self_ty) {
            return false;
        }
        match trait_path.split_once('<') {
            None => true,
            Some((_, rhs)) => int_division_operand(rhs.strip_suffix('>').unwrap_or(rhs)),
        }
    }

    pub(super) fn is_int_overflow_operator(&self) -> bool {
        let Some((self_ty, bare_trait, _, trait_path)) =
            self.std_trait(INT_OPS).or_else(|| self.std_trait(INT_ASSIGN_OPS))
        else {
            return false;
        };
        let self_ty = vc_peel_reference_prefixes(self_ty).trim();
        if bare_trait == "core::ops::arith::Neg" && is_signed_nonzero_operand(self_ty) {
            return true;
        }
        if primitive_int(self_ty).is_none() {
            return false;
        }
        match trait_path.split_once('<') {
            None => true,
            Some((_, rhs)) => {
                primitive_int(vc_peel_reference_prefixes(rhs.strip_suffix('>').unwrap_or(rhs)))
                    .is_some()
            }
        }
    }

    pub(super) fn is_value_panic_callee(&self) -> bool {
        if !self.auth_sysroot_root && self.qual.is_none() {
            return false;
        }
        if let Some((_, signed, m)) = self.int_inh {
            return int_method_can_panic_on_value(m, signed);
        }
        if self.auth_sysroot_root {
            if self.tail == "clamp" && float_inherent(self.callee) == Some("clamp") {
                return true;
            }
            if matches!(self.tail, "to_digit" | "is_digit" | "from_digit")
                && let Some(m) = char_method(self.callee)
            {
                return matches!(m, "to_digit" | "is_digit" | "from_digit");
            }
            if matches!(
                self.tail,
                "from_str_radix" | "from_ascii_radix" | "from_ascii_bytes_radix"
            ) && matches!(
                nonzero_inherent(self.callee),
                Some("from_str_radix" | "from_ascii_radix" | "from_ascii_bytes_radix")
            ) {
                return true;
            }
            if (self.callee.starts_with("core::time::Duration")
                || self.callee.starts_with("std::time::Duration"))
                && let Some(m) = duration_inherent(self.callee)
            {
                return is_panicking_duration_constructor(m);
            }
            if self.tail == "strict_cast_from" && is_strict_cast_from_callee(self.callee) {
                return true;
            }
            if self.tail == "abs" && is_signed_nonzero_negation(self.callee) {
                return true;
            }
            if self.tail == "remainder" && range_from_iter_remainder_elem(self.callee).is_some() {
                return true;
            }
            return false;
        }
        if let Some((_, _, m, _)) = self.std_trait(ORD) {
            return m == "clamp";
        }
        if self.tail == "strict_cast_from" && is_strict_cast_from_callee(self.callee) {
            return true;
        }
        if let Some((self_ty, _, _, _)) =
            self.std_trait(INT_OPS).or_else(|| self.std_trait(INT_ASSIGN_OPS))
            && primitive_int(self_ty).is_some()
            && by_value_int_op_rhs(self.callee, self_ty)
        {
            return true;
        }
        if self.qual.as_ref().is_some_and(|q| q.bare_trait == "core::ops::arith::Neg")
            && is_signed_nonzero_negation(self.callee)
        {
            return true;
        }
        if let Some((self_ty, _, m, _)) = self.std_trait(ITERATOR)
            && let Some((family, elem)) = range_self(self_ty)
        {
            return range_iter_can_panic(family, elem, m);
        }
        if let Some((self_ty, _, m, _)) = self.std_trait(STEP) {
            return step_call_can_panic(self_ty, m);
        }
        if let Some((self_ty, _, _, _)) = self.std_trait(DURATION_OPS) {
            return is_duration_ty(self_ty)
                || ((is_time_point_ty(self_ty) || self_ty.trim() == "u32")
                    && trait_rhs_is_duration(self.callee));
        }
        false
    }

    pub(super) fn overflow_call(
        &self,
        func: &VerifiableFunction,
        args: &[Operand],
    ) -> Option<NumericOverflow> {
        if !self.auth_sysroot_root && self.qual.is_none() {
            return None;
        }
        let op = if let Some((_, _, m)) = self.int_inh {
            match m {
                "strict_add" => BinOp::Add,
                "strict_sub" => BinOp::Sub,
                "strict_mul" => BinOp::Mul,
                "strict_pow" => return Some(NumericOverflow::Pow),
                _ => return None,
            }
        } else if let Some((self_ty, tr, m, _)) = self.std_trait(INT_ASSIGN_OPS) {
            primitive_int(self_ty)?;
            if !by_value_int_op_rhs(self.callee, self_ty) {
                return None;
            }
            let op = match (tr.rsplit("::").next()?, m) {
                ("AddAssign", "add_assign") => BinOp::Add,
                ("SubAssign", "sub_assign") => BinOp::Sub,
                ("MulAssign", "mul_assign") => BinOp::Mul,
                _ => return None,
            };
            let (target, rhs) = (args.first()?, args.get(1)?);
            if args.len() != 2 || !is_int_like(func, rhs) {
                return None;
            }
            return Some(NumericOverflow::AssignBinOp { op, lhs: deref_of(target)? });
        } else {
            let (self_ty, tr, m, _) = self.std_trait(INT_OPS)?;
            primitive_int(self_ty)?;
            if !by_value_int_op_rhs(self.callee, self_ty) {
                return None;
            }
            match (tr.rsplit("::").next()?, m) {
                ("Add", "add") => BinOp::Add,
                ("Sub", "sub") => BinOp::Sub,
                ("Mul", "mul") => BinOp::Mul,
                _ => return None,
            }
        };
        (args.len() == 2 && args.iter().all(|a| is_int_like(func, a)))
            .then_some(NumericOverflow::BinOp(op))
    }

    pub(super) fn value_panic_row(
        &self,
        func: &VerifiableFunction,
        args: &[Operand],
        dest: &Place,
    ) -> Option<(Formula, VcKind)> {
        if !self.auth_sysroot_root && self.qual.is_none() {
            return None;
        }
        if let Some((width, signed, m)) = self.int_inh {
            let reads_width = int_method_can_panic_on_value(m, signed)
                && !int_method_row_is_width_free(m, signed);
            let Some(width) = resolve_owner_width(func, width, signed, args.first(), reads_width)
            else {
                return pointer_width_unresolved(m);
            };
            return int_method_row(func, width, signed, m, args, dest);
        }
        if self.auth_sysroot_root {
            if self.tail == "clamp" && float_inherent(self.callee) == Some("clamp") {
                return float_clamp_row(args);
            }
            if matches!(self.tail, "to_digit" | "is_digit" | "from_digit")
                && let Some(m) = char_method(self.callee)
            {
                return match m {
                    "to_digit" | "is_digit" => radix_row(
                        func,
                        args.get(1)?,
                        2,
                        "char::to_digit: invalid radix -- radix must be in the range 2 to 36 inclusive",
                    ),
                    "from_digit" => radix_row(
                        func,
                        args.get(1)?,
                        0,
                        "char::from_digit: radix is too high (maximum 36)",
                    ),
                    _ => None,
                };
            }
            if matches!(
                self.tail,
                "from_str_radix" | "from_ascii_radix" | "from_ascii_bytes_radix"
            ) && let Some(
                m @ ("from_str_radix" | "from_ascii_radix" | "from_ascii_bytes_radix"),
            ) = nonzero_inherent(self.callee)
            {
                return radix_row(
                    func,
                    args.get(1)?,
                    2,
                    &format!("{m}: radix must lie in the range `[2, 36]`"),
                );
            }
            if (self.callee.starts_with("core::time::Duration")
                || self.callee.starts_with("std::time::Duration"))
                && let Some(m) = duration_inherent(self.callee)
            {
                return duration_method_row(func, m, args);
            }
            if self.tail == "abs" && is_signed_nonzero_negation(self.callee) {
                return unmodeled(
                    "nonzero-negation-overflow-unmodeled",
                    "NonZero<iN>::abs and unary `-` panic (\"attempt to negate with overflow\") on \
                     NonZero::<iN>::MIN; the wrapped value is not modeled — refused, never silently \
                     verified (use `checked_abs`/`checked_neg`, or operate on `get()`)",
                );
            }
            if self.tail == "strict_cast_from" && is_strict_cast_from_callee(self.callee) {
                return strict_cast_from_row(func, self.callee, args, dest);
            }
            if self.tail == "remainder"
                && let Some(elem) = range_from_iter_remainder_elem(self.callee)
            {
                return range_iter_row(func, "RangeFrom", elem, args, dest);
            }
            return None;
        }
        if self.qual.as_ref().is_some_and(|q| q.bare_trait == "core::ops::arith::Neg")
            && is_signed_nonzero_negation(self.callee)
        {
            return unmodeled(
                "nonzero-negation-overflow-unmodeled",
                "NonZero<iN>::abs and unary `-` panic (\"attempt to negate with overflow\") on \
                 NonZero::<iN>::MIN; the wrapped value is not modeled — refused, never silently \
                 verified (use `checked_abs`/`checked_neg`, or operate on `get()`)",
            );
        }
        if let Some((self_ty, tr, m, _)) = self.std_trait(INT_OPS)
            && let Some((width, signed)) = primitive_int(self_ty)
            && by_value_int_op_rhs(self.callee, self_ty)
        {
            let op = tr.rsplit("::").next().unwrap_or("");
            let reads_width = int_op_reads_width(op, m, signed);
            let Some(width) = resolve_owner_width(func, width, signed, args.first(), reads_width)
            else {
                return pointer_width_unresolved(&format!("{op}::{m}"));
            };
            return int_op_row(func, width, signed, tr, m, args);
        }
        if let Some((self_ty, tr, m, _)) = self.std_trait(INT_ASSIGN_OPS)
            && let Some((width, signed)) = primitive_int(self_ty)
            && by_value_int_op_rhs(self.callee, self_ty)
        {
            let op = tr.rsplit("::").next().unwrap_or("");
            let reads_width =
                matches!((op, m), ("ShlAssign", "shl_assign") | ("ShrAssign", "shr_assign"));
            let pointee = args.first().and_then(deref_of);
            let Some(width) =
                resolve_owner_width(func, width, signed, pointee.as_ref(), reads_width)
            else {
                return pointer_width_unresolved(&format!("{op}::{m}"));
            };
            return int_assign_op_row(func, width, tr, m, args);
        }
        if let Some((self_ty, _, m, _)) = self.std_trait(ORD) {
            return (m == "clamp").then(|| ord_clamp_row(func, self_ty, args)).flatten();
        }
        if self.tail == "strict_cast_from" && is_strict_cast_from_callee(self.callee) {
            return strict_cast_from_row(func, self.callee, args, dest);
        }
        if let Some((self_ty, _, m, _)) = self.std_trait(ITERATOR)
            && let Some((family, elem)) = range_self(self_ty)
            && range_iter_can_panic(family, elem, m)
        {
            return range_iter_row(func, family, elem, args, dest);
        }
        if let Some((self_ty, _, m, _)) = self.std_trait(STEP)
            && step_call_can_panic(self_ty, m)
        {
            return step_call_row(m);
        }
        if let Some((self_ty, tr, m, _)) = self.std_trait(DURATION_OPS) {
            return duration_op_row(func, self_ty, tr, m, args);
        }
        if let Some((_, _, m, _)) = self.std_trait(FOLD_TRAITS)
            && matches!(m, "sum")
            && crate::place_ty_cow(func, dest).is_some_and(|ty| is_duration_sum_target(&ty, 4))
        {
            return unmodeled(
                "duration-sum-overflow",
                "Iterator::sum over `Duration` panics (\"overflow in iter::sum over durations\") \
                 when the total exceeds `Duration::MAX`; the item values are not modeled — \
                 refused, never silently verified (fold with `checked_add` instead)",
            );
        }
        None
    }
}

/// `true` iff `ty` (a rendered SELF type) is the std `Duration`.
fn is_duration_ty(inner: &str) -> bool {
    let t = vc_peel_reference_prefixes(inner);
    trust_types::path_root_is_authenticated_sysroot_crate(t)
        && matches!(t, "core::time::Duration" | "std::time::Duration")
}

/// `true` iff a `sum` fold into `ty` runs `Duration`'s own `Sum`, which panics
/// ("overflow in iter::sum over durations") past `Duration::MAX`: `Duration`
/// itself, or an `Option`/`Result` whose success payload is one — core's
/// `Sum<Option<U>> for Option<T>` and `Sum<Result<U, E>> for Result<T, E>` hand
/// the unwrapped items to the payload's `Sum` (`iter::try_process`), and nest.
/// Measured on `ff3a28cc92` (review, 2026-09-28): `sum::<Option<Duration>>()`
/// and `sum::<Result<Duration, E>>()` built rc=0 and panicked at -O0 and -O.
fn is_duration_sum_target(ty: &Ty, depth: u32) -> bool {
    let Ty::Adt { name, variants, .. } = ty else { return false };
    if is_duration_ty(name) {
        return true;
    }
    if depth == 0 || !trust_types::path_root_is_authenticated_sysroot_crate(name) {
        return false;
    }
    let payload = match name.as_str() {
        "core::option::Option" => "Some",
        "core::result::Result" => "Ok",
        _ => return false,
    };
    variants.iter().any(|v| {
        v.name == payload
            && v.fields.first().is_some_and(|(_, t)| is_duration_sum_target(t, depth - 1))
    })
}

/// `true` iff `ty` (a rendered SELF type) is `std::time::Instant` or
/// `std::time::SystemTime`.
fn is_time_point_ty(inner: &str) -> bool {
    let t = vc_peel_reference_prefixes(inner);
    trust_types::path_root_is_authenticated_sysroot_crate(t)
        && matches!(t, "std::time::Instant" | "std::time::SystemTime")
}

const ORD: &[&str] = &["core::cmp::Ord"];
/// The by-value operator traits whose primitive-integer impls carry core's own
/// overflow check (`#[rustc_inherit_overflow_checks]`), reached as a CALL only
/// through an explicit `Add::add(a, b)`-style spelling (the operator itself lowers
/// to a checked `BinaryOp` the safety lane already charges).
const INT_OPS: &[&str] = &[
    "core::ops::arith::Add",
    "core::ops::arith::Sub",
    "core::ops::arith::Mul",
    "core::ops::arith::Neg",
    "core::ops::bit::Shl",
    "core::ops::bit::Shr",
];
/// The compound-assign forms of [`INT_OPS`] — `a.add_assign(b)`, and the body of
/// a generic `T: AddAssign` instantiated at a primitive — whose primitive impls
/// carry the SAME core overflow check on `*self` (`#[rustc_inherit_overflow_checks]`).
/// Measured on `ff3a28cc92` (review, 2026-09-28): `a.add_assign(b)`,
/// `sub_assign`, `mul_assign` and `shl_assign` built rc=0 with no row at all and
/// panicked at -O0. The operator spelling `a += b` lowers to a checked
/// `BinaryOp`, not a call. `DivAssign`/`RemAssign` are `divzero_call`'s
/// (measured refused).
const INT_ASSIGN_OPS: &[&str] = &[
    "core::ops::arith::AddAssign",
    "core::ops::arith::SubAssign",
    "core::ops::arith::MulAssign",
    "core::ops::bit::ShlAssign",
    "core::ops::bit::ShrAssign",
];
const DURATION_OPS: &[&str] = &[
    "core::ops::arith::Add",
    "core::ops::arith::Sub",
    "core::ops::arith::Mul",
    "core::ops::arith::Div",
    "core::ops::arith::AddAssign",
    "core::ops::arith::SubAssign",
    "core::ops::arith::MulAssign",
    "core::ops::arith::DivAssign",
];
/// The integer DIVISION operator traits. Their primitive impls panic on a zero
/// divisor in every profile (and on `MIN / -1` for a signed type), as do
/// `Wrapping<iN>`'s (`wrapping_div`/`wrapping_rem`) and `Saturating<iN>`'s
/// (`saturating_div`, `%`). See [`is_int_division_operator_callee`].
const INT_DIV_OPS: &[&str] = &[
    "core::ops::arith::Div",
    "core::ops::arith::Rem",
    "core::ops::arith::DivAssign",
    "core::ops::arith::RemAssign",
];

/// Trust (W4 ITER-HOF fix round 4, 2026-10-02): NAME-ONLY, for the compiler's
/// admission of a sysroot fn ITEM handed over as a type argument (through
/// `callee_has_call_site_panic_family`): is `callee` an integer division operator
/// — `<u32 as Div>::div`, `<u32 as Rem<&u32>>::rem`, `<i32 as DivAssign>::div_assign`,
/// `<Wrapping<u32> as Div>::div`, `<Saturating<u8> as Rem>::rem` — whose right-hand
/// side may be zero? A `NonZero` right-hand side (`<u32 as Div<NonZero<u32>>>::div`)
/// cannot be, and a float divides totally; neither is matched.
///
/// MEASURED (stage 1 of origin/main `a3be88bbde`, identically with W4 ITER-HOF):
/// `v.iter().copied().fold(7u32, core::ops::Div::div)`, `fold(7u32,
/// core::ops::Rem::rem)`, the by-reference `v.iter().fold(7u32, core::ops::Div::div)`
/// (`<u32 as Div<&u32>>::div`), `reduce(<i32 as Div>::div)` and the `Wrapping<u32>` /
/// `Saturating<u32>` folds built rc=0 with only a `native-verification-gap` row and a
/// verify-off driver panicked ("attempt to divide by zero", "attempt to calculate
/// the remainder with a divisor of zero", "attempt to divide with overflow" on
/// `[i32::MIN, -1]`), while the DIRECT call `core::ops::Div::div(a, b)` is charged a
/// `precondition of <u32 as Div>::div` row. Not part of
/// [`is_numeric_value_panic_callee`], whose by-value `INT_OPS` family is the
/// overflow-check one and whose negatives keep `<u32 as Div>::div` out on purpose.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn is_int_division_operator_callee(callee: &str) -> bool {
    NumericCallee::for_authenticated(callee, method_tail(callee)).is_int_division_operator()
}

/// A primitive integer, or a sysroot `Wrapping`/`Saturating` of one, behind any
/// number of references — the operands whose division can panic.
fn int_division_operand(inner: &str) -> bool {
    let t = vc_peel_reference_prefixes(inner).trim();
    if primitive_int(t).is_some() {
        return true;
    }
    if !(t.starts_with("core::num::") || t.starts_with("std::num::")) {
        return false;
    }
    let Some((head, arg)) = t.split_once('<') else {
        return false;
    };
    trust_types::path_root_is_authenticated_sysroot_crate(head)
        && matches!(
            head,
            "core::num::wrapping::Wrapping"
                | "core::num::saturating::Saturating"
                | "core::num::Wrapping"
                | "core::num::Saturating"
                | "std::num::Wrapping"
                | "std::num::Saturating"
        )
        && primitive_int(arg.strip_suffix('>').unwrap_or(arg)).is_some()
}

/// Trust (W4 ITER-HOF fix round 6, 2026-10-03): NAME-ONLY, for the compiler's
/// admission of a sysroot fn ITEM handed over as a type argument (through
/// `callee_has_call_site_panic_family`): is `callee` an integer operator that
/// carries core's OVERFLOW check — [`INT_OPS`] or [`INT_ASSIGN_OPS`] of a primitive
/// integer, by value or BY REFERENCE on either side (`<u32 as Add<&u32>>::add`,
/// `<&u32 as Add<u32>>::add`, `<&i32 as Neg>::neg`, `<u32 as Shl<&u32>>::shl`,
/// `<u32 as AddAssign<&u32>>::add_assign`) — or a signed `NonZero`'s negation behind a
/// reference (`<&NonZero<i32> as Neg>::neg`)?
///
/// The by-reference spellings are the ruled foundational-member class at a CALL SITE
/// (`|a, b| a + b` in a user closure — `tests/ui/trust/foundational_member_qualified_path.rs`):
/// core's retained overflow check is reported as a runtime-checked row under the
/// default policy and refused by `certify`, which is why
/// [`is_numeric_value_panic_callee`] leaves them out. Handed over as an ITEM, the
/// operator runs inside core's fold where no row of any kind is minted, so the
/// admission's own standard — an item is admitted only where a DIRECT call to it
/// would have been charged NOTHING — is not met: the direct call is charged a row.
///
/// MEASURED (stage 1 of the W4 branch `5086736f8` and of origin/main `990826872e`,
/// identical): `v.iter().fold(0u32, core::ops::Add::add)` (`<u32 as Add<&u32>>::add`),
/// `fold(1u32, Shl::shl)`, `Sub::sub`, `Mul::mul`, `Shr::shr` and an `i64` `Shl` built
/// rc=0 under the default policy AND under `-Ztrust-policy=certify`, with no row for
/// the operator, and a verify-off driver panicked ("attempt to add with overflow",
/// "attempt to shift left with overflow"); the closure twin `fold(0u32, |a, b| a + b)`
/// is refused by `certify`. `v.iter().map(core::ops::Neg::neg).collect::<Vec<i32>>()`
/// (`<&i32 as Neg>::neg`) was refused on `990826872e` only by the `collect` count and
/// built rc=0 with W4, panicking "attempt to negate with overflow" on `i32::MIN`. The
/// `Wrapping`/`Saturating` and float operators are total and are not matched; the
/// integer division operators are [`is_int_division_operator_callee`]'s.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn is_int_overflow_operator_callee(callee: &str) -> bool {
    NumericCallee::for_authenticated(callee, method_tail(callee)).is_int_overflow_operator()
}

/// A sysroot `NonZero` of a SIGNED primitive integer (references already peeled) —
/// the operand whose negation overflows at `MIN`.
fn is_signed_nonzero_operand(inner: &str) -> bool {
    let Some((head, arg)) = inner.split_once('<') else {
        return false;
    };
    trust_types::path_root_is_authenticated_sysroot_crate(head)
        && matches!(
            head,
            "core::num::nonzero::NonZero" | "core::num::NonZero" | "std::num::NonZero"
        )
        && primitive_int(arg.strip_suffix('>').unwrap_or(arg)).is_some_and(|(_, signed)| signed)
}

/// Trust (wave-19 review, 2026-10-09): the `integer_casts` trait whose
/// `strict_cast_from` is what the inherent `strict_cast::<T>` delegates to
/// (`T::strict_cast_from(self)`, core `num/uint_macros.rs` and `int_macros.rs`). It
/// is defined in `core::convert::num` and re-exported as `core::convert::
/// CheckedCastFromInt`; the extractor renders the defining path. See
/// [`is_strict_cast_from_callee`].
const CHECKED_CAST: &[&str] = &["core::convert::num::CheckedCastFromInt"];

/// Trust (wave-19 review, 2026-10-09): `<Dst as CheckedCastFromInt<Src>>::strict_cast_from`
/// (the qualified spelling of `u8::strict_cast_from(v)` and of the UFCS call), or the
/// unqualified trait-item path, under an authenticated sysroot trait. It panics
/// "attempt to cast integer with overflow" when `v` lies outside `Dst`'s range
/// (core `convert/num.rs`, `impl_int_cast!`), in every profile. NUM-NIGHTLY-UNCHARGED-1
/// charged the inherent `strict_cast*` spellings only, so this public trait spelling
/// built rc=0 on the default lane with a `runtime_checked` panic-freedom row, and
/// handed over as a fn item (`o.map(<u8 as CheckedCastFromInt<u32>>::strict_cast_from)`)
/// it was admitted with no row (measured on the stage 1 of `46e9afaf95`: a verify-off
/// driver exited 101 on 300). The total siblings `checked_cast_from` and
/// `BoundedCastFromInt::{wrapping,saturating}_cast_from` are not matched; the `unsafe`
/// `unchecked_cast_from` is refused by the unsafe lane (`[unsafe:unmodeled-call]`).
fn is_strict_cast_from_callee(callee: &str) -> bool {
    if qualified_std_trait_method(callee, CHECKED_CAST)
        .is_some_and(|(_, _, m)| m == "strict_cast_from")
    {
        return true;
    }
    trust_types::path_root_is_authenticated_sysroot_crate(callee)
        && vc_strip_generics_cow(callee)
            == "core::convert::num::CheckedCastFromInt::strict_cast_from"
}

const ITERATOR: &[&str] = &["core::iter::traits::iterator::Iterator"];
/// Trust (STEP-TRAIT-DIRECT-UNCHARGED-1, 2026-10-11): the nightly `step_trait` trait
/// whose `forward`/`backward` panic on the caller's value. See [`step_call_can_panic`].
const STEP: &[&str] = &["core::iter::range::Step"];
const FOLD_TRAITS: &[&str] =
    &["core::iter::traits::iterator::Iterator", "core::iter::traits::accum::Sum"];

/// NAME-ONLY and conservative: does `callee` fall in this module's family at
/// all (whatever its receiver and arguments)? The compiler asks it — through
/// `callee_has_call_site_panic_family` — of a sysroot function ITEM handed to a
/// callee as a type argument (`iter.map(u32::ilog2)`), where no call-site row
/// can be minted; `true` withholds the vanilla admission of that item.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn is_numeric_value_panic_callee(callee: &str) -> bool {
    NumericCallee::for_authenticated(callee, method_tail(callee)).is_value_panic_callee()
}

/// Trust (STEP-TRAIT-DIRECT-UNCHARGED-1, 2026-10-11): does `<inner as
/// core::iter::range::Step>::leaf` panic on the caller's value? `inner` is the SELF half
/// of an already-split qualified spelling whose trait half
/// [`qualified_std_trait_method`] authenticated as core's `Step` (the nightly
/// `step_trait`).
///
/// `forward(start, n)` and `backward(start, n)` panic when `start ± n` leaves the type:
/// `char`'s, `AsciiChar`'s, `Ipv4Addr`'s and `Ipv6Addr`'s run core's default body,
/// ``forward_checked(start, n).expect("overflow in `Step::forward`")`` (and `backward`'s
/// twin), an unconditional panic; the integers' and `NonZero`'s evaluate `Self::MAX + 1`
/// (`Self::MIN - 1`) under `#[rustc_inherit_overflow_checks]` exactly when the checked
/// form returns `None` (`library/core/src/iter/range.rs`). MEASURED on the stage 1 of
/// `1213387e6d` (default policy, `--crate-type lib`): `Step::forward(c, n)` and
/// `Step::backward(c, n)` on `char`, `forward` on `u8`, `NonZero<u8>`, `AsciiChar` and
/// `Ipv4Addr`, `backward` on `i32` and `Ipv6Addr`, and the closure
/// `o.map(|(c, n)| Step::forward(c, n))` each built rc=0 with one `runtime_checked` row,
/// and a verify-off driver exited 101 at `char::MAX`, `'\0'`, `u8::MAX`, `i32::MIN`,
/// `NonZero::<u8>::MAX` and `Ipv4Addr::BROADCAST`.
///
/// The SELF type must be one of core's own `Step` impls: a primitive integer, `char`,
/// or an authenticated `NonZero<int>`, `AsciiChar`, `Ipv4Addr` or `Ipv6Addr`. A user
/// type's `Step::forward` renders the same way whether the user overrode it or not, so
/// it is not read as core's. The total siblings (`forward_checked`, `backward_checked`,
/// `steps_between`) answer `false`; the `unsafe` `*_unchecked` ones are the unsafe
/// lane's.
fn step_call_can_panic(inner: &str, leaf: &str) -> bool {
    matches!(leaf, "forward" | "backward") && is_core_step_elem(inner)
}

/// Trust (STEP-ELEM-RANGEFROM-1, 2026-10-13): is `inner` (a rendered type: the SELF half
/// of a qualified `Step` spelling, or the element argument of an already-split range
/// type) one of core's own `Step` impls — a primitive integer, `char`, or an authenticated-sysroot
/// `core::num::nonzero::NonZero<int>`, `core::ascii::ascii_char::AsciiChar`,
/// `core::net::ip_addr::Ipv4Addr` or `core::net::ip_addr::Ipv6Addr`?
///
/// Every one of them panics in `Step::forward` past its `MAX` (`library/core/src/iter/
/// range.rs`): `char`'s, `AsciiChar`'s and the IP addresses' run core's default body,
/// ``forward_checked(start, n).expect("overflow in `Step::forward`")``, and the integers'
/// and `NonZero`'s evaluate `MAX + 1` under `#[rustc_inherit_overflow_checks]`. Factored
/// out of [`step_call_can_panic`] so the `RangeFrom` iteration arms
/// ([`range_iter_can_panic`], [`range_from_iter_remainder_elem`]) read the SAME set:
/// they read only `int | char`, and an open `x..` range over `Ipv4Addr`, `Ipv6Addr`,
/// `NonZero<u8>`, `AsciiChar` (or the stable `core::range::RangeFrom` iterator over one)
/// was advanced with no row.
///
/// The type token is exact and its root authenticated: a user type's `Step` (nightly
/// `step_trait`; it may be the user's own `forward`), a type parameter, a namesake in a
/// user crate and a stamped impersonator of `core` do not answer.
fn is_core_step_elem(inner: &str) -> bool {
    let t = inner.trim();
    if primitive_int(t).is_some() || t == "char" {
        return true;
    }
    if !trust_types::path_root_is_authenticated_sysroot_crate(t) {
        return false;
    }
    if matches!(
        t,
        "core::ascii::ascii_char::AsciiChar"
            | "core::net::ip_addr::Ipv4Addr"
            | "core::net::ip_addr::Ipv6Addr"
    ) {
        return true;
    }
    t.strip_prefix("core::num::nonzero::NonZero<")
        .and_then(|arg| arg.strip_suffix('>'))
        .is_some_and(|arg| primitive_int(arg).is_some())
}

/// Trust (STEP-ELEM-RANGEFROM-1, 2026-10-13): the most steps `Step::steps_between` can
/// count over `inner`, the element argument of an already-split range type, when it is
/// a NON-integer core `Step` type, as a power of two: the element spans at
/// most `2^bits - 1` steps. `char` spans at most `0x10FFFF - 0x800` (core skips the
/// surrogates), below `2^21`; `AsciiChar` counts as `u8` over `0..=127`, below `2^7`;
/// `Ipv4Addr` and `Ipv6Addr` count as `u32` and `u128`; `NonZero<uN>` counts
/// `end.get() - start.get()`, below `2^N` (`2^p` for `usize`, `p` the pointer width).
/// `None` for anything [`is_core_step_elem`] does not accept, and for the primitive
/// integers, which [`range_count_can_overflow`] reads itself.
fn non_int_step_span_bits(inner: &str, p: u32) -> Option<u32> {
    let t = inner.trim();
    if t == "char" {
        return Some(21);
    }
    if primitive_int(t).is_some() || !is_core_step_elem(t) {
        return None;
    }
    match t {
        "core::ascii::ascii_char::AsciiChar" => Some(7),
        "core::net::ip_addr::Ipv4Addr" => Some(32),
        "core::net::ip_addr::Ipv6Addr" => Some(128),
        _ => {
            let arg = t.strip_prefix("core::num::nonzero::NonZero<")?.strip_suffix('>')?;
            match primitive_int(arg)? {
                (IntWidth::Fixed(w), _) => Some(w),
                (IntWidth::Pointer, _) => Some(p),
            }
        }
    }
}

/// The fail-closed row of a direct `Step::forward` / `Step::backward` call
/// ([`step_call_can_panic`]). `start` is the caller's value, and for `char` the
/// result also skips the surrogate gap, so no linear row is built: the call is
/// refused, as an advancing `RangeFrom` call is (`range-from-step-overflow-unmodeled`).
/// A guarded call over-refuses (DECISION_QUEUE `STEP-TRAIT-DIRECT-UNCHARGED-1`).
fn step_call_row(leaf: &str) -> Option<(Formula, VcKind)> {
    if leaf == "backward" {
        unmodeled(
            "step-backward-overflow-unmodeled",
            "`Step::backward(start, n)` panics (\"overflow in `Step::backward`\", or the \
             integer overflow check) when `start - n` passes the type's MIN; its operands \
             are not modeled at this call — refused, never silently verified (use \
             `Step::backward_checked`)",
        )
    } else {
        unmodeled(
            "step-forward-overflow-unmodeled",
            "`Step::forward(start, n)` panics (\"overflow in `Step::forward`\", or the \
             integer overflow check) when `start + n` passes the type's MAX; its operands \
             are not modeled at this call — refused, never silently verified (use \
             `Step::forward_checked`)",
        )
    }
}

/// `true` iff the operator trait's right-hand type argument is ABSENT (`Rhs =
/// Self`) or a by-value primitive integer — `<u32 as Add>::add`,
/// `<u32 as Shl<i8>>::shl`. A REFERENCE argument (`<u32 as Add<&u32>>::add`, what
/// an iterator chain's `|a, b| a + b` produces) is the ruled foundational-member
/// class (`tests/ui/trust/foundational_member_qualified_path.rs`) and is left to it.
fn by_value_int_op_rhs(callee: &str, self_ty: &str) -> bool {
    let Some((trait_path, _)) = vc_qualified_trait_method(callee) else { return false };
    match trait_path.split_once('<') {
        None => true,
        Some((_, arg)) => {
            let arg = arg.trim_end_matches('>').trim();
            primitive_int(arg).is_some()
                && (arg == self_ty.trim() || trait_path.contains("::bit::"))
        }
    }
}

/// `NonZero::<iN>::abs` or `<NonZero<iN> as Neg>::neg`.
fn is_signed_nonzero_negation(callee: &str) -> bool {
    (nonzero_inherent(callee) == Some("abs")
        || qualified_std_trait_method(callee, &["core::ops::arith::Neg"])
            .is_some_and(|(t, _, _)| vc_strip_generics_cow(t) == "core::num::nonzero::NonZero"))
        && nonzero_is_signed(callee)
}

/// `NonZero::<iN>::…` — a SIGNED `NonZero` (the only ones with `abs`/`Neg`).
fn nonzero_is_signed(callee: &str) -> bool {
    ["NonZero::<i", "NonZero<i"].iter().any(|p| callee.contains(p))
}

/// `true` iff the qualified trait half carries `Duration` as its right-hand type
/// argument — `<u32 as core::ops::arith::Mul<core::time::Duration>>::mul`, the
/// `k * d` spelling — so a plain `<u32 as Mul>::mul` is never read as one.
fn trait_rhs_is_duration(callee: &str) -> bool {
    vc_qualified_trait_method(callee).is_some_and(|(trait_path, _)| {
        trait_path.split_once('<').is_some_and(|(_, arg)| is_duration_ty(arg.trim_end_matches('>')))
    })
}

/// The primitive-integer methods whose panic condition is an argument value.
/// `div_euclid`/`rem_euclid`/`div_ceil` (the zero divisor) stay with
/// `divzero_call`; the signed `div_euclid`/`rem_euclid` `MIN / -1` overflow is
/// charged here.
fn int_method_can_panic_on_value(leaf: &str, signed: bool) -> bool {
    match leaf {
        // Trust (ASCII-FROM-ASCII-RADIX-1, 2026-10-05): the nightly
        // `from_ascii_radix` (`int_from_ascii`) runs the radix check
        // `from_str_radix` delegates to; it was missed by the stable-only audit.
        "ilog"
        | "ilog2"
        | "ilog10"
        | "from_str_radix"
        | "from_ascii_radix"
        | "from_ascii_bytes_radix" => true,
        "isqrt" | "div_euclid" | "rem_euclid" => signed,
        "next_power_of_two" => !signed,
        // Trust (NUM-NIGHTLY-UNCHARGED-1, 2026-10-06): the NIGHTLY methods the
        // 2026-09-25 stable-only audit left out, each of which panics on the
        // caller's value (measured: built rc=0 on the default lane, exit 101 on
        // the panicking value). The signed `next_multiple_of` (`int_roundings`)
        // joins the unsigned one; `funnel_shl`/`funnel_shr` (`funnel_shifts`, uN
        // only) assert `n < BITS`; the `strict_cast` family (`integer_casts`,
        // `integer_cast_extras`) panics on a value outside the target's range.
        "next_multiple_of" | "strict_cast" => true,
        "funnel_shl" | "funnel_shr" | "strict_cast_signed" => !signed,
        "strict_cast_unsigned" => signed,
        // The `strict_*` family (stable 1.91): panics UNCONDITIONALLY — not only
        // under overflow checks — on overflow, a zero divisor, `MIN / -1`, an
        // over-wide shift, and (`strict_neg` on an unsigned) any nonzero value.
        "strict_add" | "strict_sub" | "strict_mul" | "strict_pow" | "strict_neg" | "strict_shl"
        | "strict_shr" | "strict_div" | "strict_div_euclid" | "strict_rem"
        | "strict_rem_euclid" => true,
        "strict_add_signed" | "strict_sub_signed" => !signed,
        "strict_add_unsigned" | "strict_sub_unsigned" | "strict_abs" => signed,
        _ => false,
    }
}

/// The members of [`int_method_can_panic_on_value`]'s family whose row in
/// [`int_method_row`] never reads `Self`'s width. Every other member's row READS
/// it, through `BITS`, `MIN`, `MAX` or the target range of a same-width cast, so
/// on a pointer-sized owner it needs a resolved width ([`resolve_owner_width`]).
///
/// The list names the width-free arms, not the width-reading ones. An arm added
/// later and left off it is refused on an unresolved pointer-sized receiver. It
/// is never built at 64 bits.
///
/// Trust (W32-PRIMINT-PIN-1, 2026-10-06).
fn int_method_row_is_width_free(leaf: &str, signed: bool) -> bool {
    match leaf {
        // `self <= 0`, `base < 2`, `self < 0`, a radix outside `[2, 36]`.
        "ilog"
        | "ilog2"
        | "ilog10"
        | "isqrt"
        | "from_str_radix"
        | "from_ascii_radix"
        | "from_ascii_bytes_radix" => true,
        // `strict_cast::<T>` ranges `self` at its own declared type and takes `T`'s
        // range from the call's destination.
        "strict_cast" => true,
        // The same-type overflow rows are the overflow-call lane's
        // ([`numeric_overflow_call`]), built at the call's destination type.
        // `int_method_row` has no arm for them.
        "strict_add" | "strict_sub" | "strict_mul" | "strict_pow" => true,
        // Unsigned: `self != 0`, and a zero divisor.
        "strict_neg" | "strict_div" | "strict_div_euclid" | "strict_rem" | "strict_rem_euclid" => {
            !signed
        }
        _ => false,
    }
}

fn is_panicking_duration_constructor(leaf: &str) -> bool {
    matches!(
        leaf,
        "new" | "from_secs_f64"
            | "from_secs_f32"
            | "mul_f64"
            | "mul_f32"
            | "div_f64"
            | "div_f32"
            | "from_mins"
            | "from_hours"
            | "from_nanos_u128"
            // Trust (NUM-NIGHTLY-UNCHARGED-1, 2026-10-06): the nightly
            // `duration_constructors` pair (`Duration::from_days(u64::MAX)`
            // built rc=0 and panicked).
            | "from_days"
            | "from_weeks"
    )
}

fn assertion(message: &str) -> VcKind {
    VcKind::Assertion { message: message.to_string() }
}

fn unmodeled(kind: &str, detail: &str) -> Option<(Formula, VcKind)> {
    Some((
        super::unsupported::unsupported_mir_fail_closed_formula(),
        VcKind::UnsupportedMir { kind: kind.to_string(), detail: detail.to_string() },
    ))
}

/// An integer-valued argument's formula, conjoined with the range of the type
/// it is read at (`width`, `signed`) — the operand's own declared type when it
/// has one, so a `char` or a widened literal is ranged correctly.
fn ranged(func: &VerifiableFunction, op: &Operand, width: u32, signed: bool) -> (Formula, Formula) {
    let f = operand_to_formula(func, op);
    let (w, s) = match crate::operand_ty_cow(func, op).as_deref() {
        Some(t @ (Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char)) => {
            (t.int_width().unwrap_or(width), t.is_signed())
        }
        _ => (width, signed),
    };
    let range = crate::range::input_range_constraint(&f, w, s);
    (f, range)
}

/// `value < MIN(Self) || value > MAX(Self)`.
fn out_of_range(value: Formula, width: u32, signed: bool) -> Formula {
    Formula::Or(vec![
        lt(value.clone(), crate::range::type_min_formula(width, signed)),
        gt(value, crate::range::type_max_formula(width, signed)),
    ])
}

fn int(v: i128) -> Formula {
    Formula::Int(v)
}

fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}

fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}

fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}

fn ge(a: Formula, b: Formula) -> Formula {
    Formula::Ge(Box::new(a), Box::new(b))
}

fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

/// `true` iff `op`'s declared type is an integer or a `char` (the `Ord` impls
/// whose `clamp` a linear comparison models exactly).
fn is_int_like(func: &VerifiableFunction, op: &Operand) -> bool {
    matches!(
        crate::operand_ty_cow(func, op).as_deref(),
        Some(Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char)
    )
}

/// The value of a float literal operand, decoded at its width.
fn const_float_value(op: &Operand) -> Option<f64> {
    match op {
        Operand::Constant(ConstValue::Float(v)) => Some(*v),
        Operand::Constant(ConstValue::FloatBits { bits, width: 64 }) => {
            Some(f64::from_bits(u64::try_from(*bits).ok()?))
        }
        Operand::Constant(ConstValue::FloatBits { bits, width: 32 }) => {
            Some(f64::from(f32::from_bits(u32::try_from(*bits).ok()?)))
        }
        _ => None,
    }
}

/// A radix argument that must lie in `lo..=36`: for a literal, a row whose violation
/// is the CONSTANT `radix < lo || radix > 36` (see `decided_row`), else the precise
/// `radix < lo || radix > 36` row.
fn radix_row(
    func: &VerifiableFunction,
    radix: &Operand,
    lo: i128,
    message: &str,
) -> Option<(Formula, VcKind)> {
    if let Some(r) = const_int_value(radix) {
        return decided_row(!(lo..=36).contains(&r), message);
    }
    let (r, range) = ranged(func, radix, 32, false);
    let violation = if lo > 0 {
        Formula::Or(vec![lt(r.clone(), int(lo)), gt(r, int(36))])
    } else {
        gt(r, int(36))
    };
    Some((Formula::And(vec![range, violation]), assertion(message)))
}

/// The same-type `a op b` overflow of a recognized numeric call — `strict_add`/
/// `strict_sub`/`strict_mul` and the by-value `Add::add`/`Sub::sub`/`Mul::mul` on a
/// primitive integer. The caller mints it with the builder the `BinaryOp`
/// statement arm uses for `a op b` (`v2_build_overflow_vc_for_operands_typed`),
/// whose bit-vector route refutes a product of two variables; an `Assertion`
/// over the LIA product is answered `Unknown` in-process and reported
/// runtime-checked — measured, `i32::strict_mul` built rc=0 that way.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn numeric_overflow_call(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> Option<NumericOverflow> {
    NumericCallee::for_minting(callee, method_tail(callee)).overflow_call(func, args)
}

/// Which overflow row [`numeric_overflow_call`] asks the safety lane to mint.
pub(super) enum NumericOverflow {
    /// `a op b` at the call's destination type — the `BinaryOp` arm's row.
    BinOp(BinOp),
    /// `*p op b` for a compound-assign call `<iN as OpAssign>::op_assign(p, b)`:
    /// `lhs` is the place `*p` (the operand `*a += b` itself reads when `a` is a
    /// `&mut iN`), typed at its pointee. The destination is `()`, so the lane
    /// types the row at `lhs`'s own type.
    AssignBinOp { op: BinOp, lhs: Operand },
    /// `base.pow(exp)` — the overflow-call lane's `pow` row.
    Pow,
}

/// `*p` for a `&mut` receiver operand `p`: the same place read through one more
/// `Deref`.
fn deref_of(op: &Operand) -> Option<Operand> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let mut place = place.clone();
            place.projections.push(Projection::Deref);
            Some(Operand::Copy(place))
        }
        _ => None,
    }
}

/// The precise or fail-closed row for a recognized numeric call, or `None` when
/// the call is not in the family or its argument provably cannot panic.
///
/// `args` are the MIR call operands (the receiver, when there is one, is arg 0);
/// `dest` is the call's destination (for the `Iterator::sum::<Duration>` fold).
///
/// Trust (wave 23, STAMPED-CORE-MINT-1 residual, 2026-10-11): this function and
/// [`numeric_overflow_call`] read the callee past ONE well-formed leading extractor
/// identity stamp ([`after_one_identity_stamp`]), as [`int_inherent_minting`] does for
/// `abs`, `pow` and `unchecked_*`. The extractor stamps the GENUINE core whenever a
/// second crate named `core` is in the graph, and under `-Zbuild-std`; it puts the
/// stamp in front of the WHOLE rendered path, the qualified trait spelling included
/// (`__trust_crate@414739228a72f04f::<i32 as core::cmp::Ord>::clamp`). Every
/// recognizer here authenticated the raw callee (`int_inherent`, or the trait half of
/// a qualified spelling, which the stamp hid), so in such a graph the family minted
/// nothing. MEASURED on the stage 1 of `5911b1325f` with a verify-off `--crate-name
/// core` dependency in the graph: `x.ilog2()`, `a.strict_add(b)`, `x.clamp(lo, hi)`,
/// `x.next_power_of_two()` and `x.strict_neg()` each built with warnings only (exit 0)
/// on a `runtime_checked` row, and a verify-on binary exited 101 on the caller's value
/// ("attempt to add with overflow", "argument of integer logarithm must be positive");
/// without the second `core` the same calls are refused. Fixtures:
/// `tests/ui/trust/stamped_genuine_core_rows_kept.rs` (revision `family`) and
/// `crates/trust-vcgen/tests/stamped_genuine_core_realmir.rs`.
///
/// WHY THIS IS SAFE HERE. Only the text after the stamp is read, and every arm
/// re-authenticates it exactly as it authenticates an unstamped callee: `int_inherent`
/// and the float, char, `NonZero`, `Duration` and `strict_cast_from` owners anchor on
/// `trust_types::path_root_is_authenticated_sysroot_crate`, and a qualified spelling
/// anchors its trait half the same way (`qualified_std_trait_method`), so a SECOND
/// stamp in the owner path or the trait half, or a stamp that is not at the front,
/// still answers `None`; a qualified spelling's SELF type is judged exactly as it is
/// for an unstamped callee (a stamped or user self type gets no row, or the
/// fail-closed `ord-clamp-bounds-unmodeled` row for `clamp`). The two functions only
/// ADD rows over the call's own arguments; the GRANTS they consult
/// (`literal_duration_nanos`, `is_fresh_clock_reading` / `is_clock_reading_callee`)
/// are asked of OTHER calls' callees and stay authenticated. A forged crate named
/// `core` that renders the same spelling (a `#![no_core]` graph, or its own
/// `cmp::Ord::clamp`) is charged a row its body may not owe: a false red, and its own
/// absent-callee row still refuses the call
/// (`tests/ui/trust/stamped_forged_core_numeric_family_refused.rs`). The cost in a
/// stamped graph is the other direction of the same rule: a literal `Duration` or a
/// fresh `Instant::now()` operand whose defining call is itself stamped is not read
/// as decided, so its arithmetic now mints the fail-closed row instead of nothing.
/// The name-only [`is_numeric_value_panic_callee`] and the rotate grant in
/// `callee_has_call_site_panic_family` keep [`int_inherent`] as it is.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn numeric_value_panic_row(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    dest: &Place,
) -> Option<(Formula, VcKind)> {
    NumericCallee::for_minting(callee, method_tail(callee)).value_panic_row(func, args, dest)
}

/// Classification of the call's DESTINATION when it is an integer: the MIR
/// return place of a `-> T` cast, so it IS the target type, never a parse of the
/// rendered turbofish.
///
/// Trust (W32-PRIMINT-PIN-1, wave-21 integration 2026-10-09): only the carrier
/// `Ty::Int` answers `DestIntTy::Int`. It is minted at the target's real width,
/// `usize`/`isize` included. A faithful `PtrSizedInt` destination does not carry
/// that width (its `int_width` is the pinned 64), so it answers
/// `DestIntTy::FaithfulPtrSized`, and each caller refuses it with
/// [`pointer_width_unresolved`] instead of ranging it at 64 bits.
#[derive(Clone, Copy)]
enum DestIntTy {
    Int(u32, bool),
    FaithfulPtrSized,
}

fn classify_dest_int(func: &VerifiableFunction, dest: &Place) -> Option<DestIntTy> {
    match crate::place_ty_cow(func, dest)?.as_ref() {
        Ty::Int { width, signed } => Some(DestIntTy::Int(*width, *signed)),
        Ty::PtrSizedInt { .. } => Some(DestIntTy::FaithfulPtrSized),
        _ => None,
    }
}

/// Trust (wave-19 review, 2026-10-09): the row of
/// `<Dst as CheckedCastFromInt<Src>>::strict_cast_from(v)` ([`is_strict_cast_from_callee`]),
/// the same out-of-range row the inherent `strict_cast::<Dst>()` takes. `Dst` is read
/// from the call's DESTINATION type and must agree with the rendered `Self`; `Src` is
/// the trait's type argument and must agree with the argument's own declared type
/// when it has one. A generic or non-primitive side, or a spelling that names neither
/// (the unqualified trait-item path), gets the fail-closed
/// `strict-cast-target-unmodeled` row: refused, never assumed to fit.
///
/// Trust (W32-PRIMINT-PIN-1, wave-21 integration 2026-10-09): a pointer-sized side
/// takes its width from a declared carrier, never from the pinned 64. A `usize`/`isize`
/// `Dst` is as wide as the destination's `Ty::Int` carrier, which must be a pointer
/// width; a `usize`/`isize` `Src` is as wide as the argument's declared carrier
/// ([`declared_pointer_width`]). A faithful `PtrSizedInt` destination, or a
/// pointer-sized `Src` whose argument does not fix the width, is refused with
/// [`pointer_width_unresolved`].
fn strict_cast_from_row(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    dest: &Place,
) -> Option<(Formula, VcKind)> {
    let refused = || {
        unmodeled(
            "strict-cast-target-unmodeled",
            "CheckedCastFromInt::strict_cast_from panics (\"attempt to cast integer with \
             overflow\") when the value lies outside the target's range; the source or the \
             target is not a primitive integer here (a generic side), so the range is not \
             modeled — refused, never silently verified (use `checked_cast_from`)",
        )
    };
    let dst_self = vc_qualified_self_ty(callee).and_then(primitive_int);
    let src_arg = vc_qualified_trait_method(callee).and_then(|(trait_path, _)| {
        let (_, arg) = trait_path.split_once('<')?;
        primitive_int(arg.strip_suffix('>').unwrap_or(arg))
    });
    let dst = match classify_dest_int(func, dest) {
        Some(DestIntTy::FaithfulPtrSized) => return pointer_width_unresolved("strict_cast_from"),
        Some(DestIntTy::Int(w, s)) => Some((w, s)),
        None => None,
    };
    let (Some(x), Some(dst), Some(src)) = (args.first(), dst, src_arg) else {
        return refused();
    };
    // The rendered `Self` must BE the destination's type: the same signedness, and
    // the same width, where a pointer-sized `Self` matches any pointer-width carrier.
    let dst_is_self = dst_self.is_some_and(|(w, s)| {
        s == dst.1
            && match w {
                IntWidth::Fixed(w) => w == dst.0,
                IntWidth::Pointer => POINTER_WIDTHS.contains(&dst.0),
            }
    });
    if !dst_is_self {
        return refused();
    }
    let src = match src {
        (IntWidth::Fixed(w), s) => (w, s),
        (IntWidth::Pointer, s) => match declared_pointer_width(func, x, s) {
            Some(w) => (w, s),
            None => return pointer_width_unresolved("strict_cast_from"),
        },
    };
    if let Some(t @ (Ty::Int { .. } | Ty::PtrSizedInt { .. })) =
        crate::operand_ty_cow(func, x).as_deref()
        && (t.int_width(), t.is_signed()) != (Some(src.0), src.1)
    {
        return refused();
    }
    let (xf, xr) = ranged(func, x, src.0, src.1);
    Some((
        Formula::And(vec![xr, out_of_range(xf, dst.0, dst.1)]),
        assertion("strict_cast_from: attempt to cast integer with overflow"),
    ))
}

/// The row of a recognized `core::num::<impl T>::m` call. `width` is `T`'s width
/// AT THIS CALL. For a pointer-sized `T` it is the receiver's declared pointer
/// width, which [`numeric_value_panic_row`] resolves before calling here. An
/// unresolved width reaches this function only for a width-free arm
/// ([`int_method_row_is_width_free`]) or a method outside the family.
fn int_method_row(
    func: &VerifiableFunction,
    width: u32,
    signed: bool,
    m: &str,
    args: &[Operand],
    dest: &Place,
) -> Option<(Formula, VcKind)> {
    match m {
        // `ilog2()`/`ilog10()`: `self <= 0` (signed) / `self == 0` (unsigned)
        // panics "argument of integer logarithm must be positive".
        "ilog2" | "ilog10" => {
            let x = args.first()?;
            if const_int_value(x).is_some_and(|v| v > 0) {
                return None;
            }
            let (xf, range) = ranged(func, x, width, signed);
            Some((
                Formula::And(vec![range, le(xf, int(0))]),
                assertion(&format!("{m}: argument of integer logarithm must be positive")),
            ))
        }
        // `ilog(base)`: `assert!(base >= 2)` first, then `self <= 0` panics.
        "ilog" => {
            let x = args.first()?;
            let b = args.get(1)?;
            if const_int_value(x).is_some_and(|v| v > 0)
                && const_int_value(b).is_some_and(|v| v >= 2)
            {
                return None;
            }
            let (xf, xr) = ranged(func, x, width, signed);
            let (bf, br) = ranged(func, b, width, signed);
            Some((
                Formula::And(vec![xr, br, Formula::Or(vec![lt(bf, int(2)), le(xf, int(0))])]),
                assertion(
                    "ilog: base of integer logarithm must be at least 2, and the argument positive",
                ),
            ))
        }
        // signed `isqrt()`: `self < 0` panics "argument of integer square root
        // cannot be negative". The unsigned `isqrt` is total.
        "isqrt" if signed => {
            let x = args.first()?;
            if const_int_value(x).is_some_and(|v| v >= 0) {
                return None;
            }
            let (xf, range) = ranged(func, x, width, signed);
            Some((
                Formula::And(vec![range, lt(xf, int(0))]),
                assertion("isqrt: argument of integer square root cannot be negative"),
            ))
        }
        // unsigned `next_power_of_two()`: `self > 2^(BITS-1)` overflows the
        // internal `+ 1` ("attempt to add with overflow" under overflow checks).
        "next_power_of_two" if !signed => {
            let x = args.first()?;
            let top =
                if width >= 128 { Formula::UInt(1u128 << 127) } else { int(1i128 << (width - 1)) };
            if let Some(v) = const_int_value(x)
                && width < 128
                && v <= (1i128 << (width - 1))
            {
                return None;
            }
            let (xf, range) = ranged(func, x, width, signed);
            Some((
                Formula::And(vec![range, gt(xf, top)]),
                assertion("next_power_of_two: attempt to add with overflow"),
            ))
        }
        // unsigned `next_multiple_of(rhs)`: `self % rhs` panics on `rhs == 0`,
        // and `self + (rhs - self % rhs)` overflows under overflow checks. The
        // overflow is over-approximated LINEARLY by `self + rhs - 1 > MAX` (the
        // added amount is at most `rhs - 1`): it can refuse a `self` that is
        // already a multiple, never accept an overflowing one.
        "next_multiple_of" if !signed => {
            let x = args.first()?;
            let rhs = args.get(1)?;
            let (xf, xr) = ranged(func, x, width, signed);
            let (rf, rr) = ranged(func, rhs, width, signed);
            let max = crate::range::type_max_formula(width, false);
            let sum = Formula::Sub(
                Box::new(Formula::Add(Box::new(xf), Box::new(rf.clone()))),
                Box::new(int(1)),
            );
            Some((
                Formula::And(vec![xr, rr, Formula::Or(vec![eq(rf, int(0)), gt(sum, max)])]),
                assertion("next_multiple_of: divide by zero, or attempt to add with overflow"),
            ))
        }
        // Trust (NUM-NIGHTLY-UNCHARGED-1, 2026-10-06): signed `next_multiple_of(rhs)`
        // (nightly `int_roundings`). Core returns `self` at once on `rhs == -1` (so
        // `MIN % -1` is never computed), then `r = self % rhs` panics on `rhs == 0`;
        // `r + rhs` (opposite signs) and `rhs - m` (same sign, `|m| < |rhs|`) cannot
        // overflow, and the result is `self + d` with `d` in `[1, rhs - 1]` (`rhs >
        // 0`) or `[rhs + 1, -1]` (`rhs < -1`), added under overflow checks. The
        // overflow is over-approximated LINEARLY, in unbounded integers, by `self +
        // rhs - 1 > MAX` / `self + rhs + 1 < MIN`: like the unsigned arm, it can
        // refuse a `self` that is already a multiple, never accept an overflowing one.
        "next_multiple_of" if signed => {
            let x = args.first()?;
            let rhs = args.get(1)?;
            // A literal `0` always panics and a literal `-1` never does (core's early
            // return), whatever `self` is: decided, and minted either way. (Measured:
            // the in-process solver answers the undecided `-1` row `unknown` — its
            // UNSAT proof fails strict certification — which would refuse a call that
            // cannot panic.)
            if let Some(r @ (0 | -1)) = const_int_value(rhs) {
                return decided_row(
                    r == 0,
                    "next_multiple_of: divide by zero, or attempt to add with overflow",
                );
            }
            let (xf, xr) = ranged(func, x, width, signed);
            let (rf, rr) = ranged(func, rhs, width, signed);
            let up = Formula::Sub(
                Box::new(Formula::Add(Box::new(xf.clone()), Box::new(rf.clone()))),
                Box::new(int(1)),
            );
            let down = Formula::Add(
                Box::new(Formula::Add(Box::new(xf), Box::new(rf.clone()))),
                Box::new(int(1)),
            );
            Some((
                Formula::And(vec![
                    xr,
                    rr,
                    Formula::Or(vec![
                        eq(rf.clone(), int(0)),
                        Formula::And(vec![
                            gt(rf.clone(), int(0)),
                            gt(up, crate::range::type_max_formula(width, true)),
                        ]),
                        Formula::And(vec![
                            lt(rf, int(-1)),
                            lt(down, crate::range::type_min_formula(width, true)),
                        ]),
                    ]),
                ]),
                assertion("next_multiple_of: divide by zero, or attempt to add with overflow"),
            ))
        }
        // Trust (NUM-NIGHTLY-UNCHARGED-1, 2026-10-06): `funnel_shl/funnel_shr(rhs, n:
        // u32)` (nightly `funnel_shifts`, uN only): `assert!(n < Self::BITS)` —
        // "attempt to funnel shift left/right with overflow". `n` is the THIRD
        // operand. A literal `n` is decided (the row is minted either way).
        "funnel_shl" | "funnel_shr" => {
            let n = args.get(2)?;
            let message = if m == "funnel_shl" {
                "funnel_shl: attempt to funnel shift left with overflow"
            } else {
                "funnel_shr: attempt to funnel shift right with overflow"
            };
            if let Some(v) = const_int_value(n) {
                return decided_row(!(0..i128::from(width)).contains(&v), message);
            }
            let (nf, nr) = ranged(func, n, 32, false);
            Some((Formula::And(vec![nr, ge(nf, int(i128::from(width)))]), assertion(message)))
        }
        // Trust (NUM-NIGHTLY-UNCHARGED-1, 2026-10-06): the `strict_cast` family
        // (nightly `integer_casts` / `integer_cast_extras`) panics "attempt to cast
        // integer with overflow" iff `self` lies outside the TARGET's range.
        // `strict_cast_signed` (uN -> iN) and `strict_cast_unsigned` (iN -> uN)
        // keep the width and flip the signedness. `strict_cast::<T>`'s target is
        // the call's DESTINATION type — the MIR return place of `-> T`, so it IS
        // `T` — never a parse of the rendered turbofish. A destination that is not
        // a primitive integer (a generic `T`) is refused, never assumed to fit.
        "strict_cast" | "strict_cast_signed" | "strict_cast_unsigned" => {
            let x = args.first()?;
            // Trust (W32-PRIMINT-PIN-1, 2026-10-06): a `usize`/`isize` target is the
            // legacy carrier `Ty::Int` at the target's real pointer width. A faithful
            // `PtrSizedInt` destination does not carry that width (its `int_width` is
            // the pinned 64), so it is refused, not ranged at 64 bits.
            let target = match m {
                "strict_cast_signed" => Some((width, true)),
                "strict_cast_unsigned" => Some((width, false)),
                _ => match classify_dest_int(func, dest) {
                    Some(DestIntTy::FaithfulPtrSized) => return pointer_width_unresolved(m),
                    Some(DestIntTy::Int(w, s)) => Some((w, s)),
                    None => None,
                },
            };
            let Some((tw, ts)) = target else {
                return unmodeled(
                    "strict-cast-target-unmodeled",
                    "strict_cast::<T> panics (\"attempt to cast integer with overflow\") when \
                     the value lies outside T's range; T is not a primitive integer here (a \
                     generic target), so the range is not modeled — refused, never silently \
                     verified (use `checked_cast`)",
                );
            };
            let (xf, xr) = ranged(func, x, width, signed);
            Some((
                Formula::And(vec![xr, out_of_range(xf, tw, ts)]),
                assertion(&format!("{m}: attempt to cast integer with overflow")),
            ))
        }
        // signed `div_euclid`/`rem_euclid`: `self == MIN && rhs == -1` panics
        // "attempt to divide with overflow" / "calculate the remainder with
        // overflow" (the zero divisor is `divzero_call`'s `DivisionByZero` row).
        "div_euclid" | "rem_euclid" if signed => {
            let x = args.first()?;
            let rhs = args.get(1)?;
            if const_int_value(rhs).is_some_and(|v| v != -1)
                || const_int_value(x).is_some_and(|v| v != crate::range::signed_min(width))
            {
                return None;
            }
            let (xf, xr) = ranged(func, x, width, signed);
            let (rf, rr) = ranged(func, rhs, width, signed);
            Some((
                Formula::And(vec![
                    xr,
                    rr,
                    eq(xf, crate::range::type_min_formula(width, true)),
                    eq(rf, int(-1)),
                ]),
                assertion(&format!("{m}: attempt to divide with overflow (MIN / -1)")),
            ))
        }
        // `strict_add_signed/strict_sub_signed` (unsigned self, signed rhs) and
        // `strict_add_unsigned/strict_sub_unsigned` (signed self, unsigned rhs):
        // the MATHEMATICAL result leaves `Self`'s range. Each operand is ranged at
        // its own declared type. (The same-type `strict_add/sub/mul` are minted by
        // the overflow-call lane — see [`numeric_overflow_call`].)
        "strict_add_signed"
        | "strict_sub_signed"
        | "strict_add_unsigned"
        | "strict_sub_unsigned" => {
            let (a, b) = (args.first()?, args.get(1)?);
            let rhs_signed = matches!(m, "strict_add_signed" | "strict_sub_signed");
            let (af, ar) = ranged(func, a, width, signed);
            let (bf, br) = ranged(func, b, width, rhs_signed);
            let result = if m.starts_with("strict_add") {
                Formula::Add(Box::new(af), Box::new(bf))
            } else {
                Formula::Sub(Box::new(af), Box::new(bf))
            };
            Some((
                Formula::And(vec![ar, br, out_of_range(result, width, signed)]),
                assertion(&format!("{m}: arithmetic overflow")),
            ))
        }
        // `strict_neg`: signed `self == MIN`; unsigned ANY `self != 0`.
        // `strict_abs` (signed): `self == MIN`.
        "strict_neg" | "strict_abs" => {
            let x = args.first()?;
            let (xf, xr) = ranged(func, x, width, signed);
            let bad = if signed {
                eq(xf, crate::range::type_min_formula(width, true))
            } else {
                Formula::Not(Box::new(eq(xf, int(0))))
            };
            Some((
                Formula::And(vec![xr, bad]),
                assertion(&format!("{m}: attempt to negate with overflow")),
            ))
        }
        // `strict_shl/strict_shr(rhs: u32)`: `rhs >= BITS`. `BITS` is the RECEIVER's
        // width, resolved from `self`'s declared carrier for `usize`/`isize`. It is
        // not the `u32` shift amount's width.
        "strict_shl" | "strict_shr" => {
            let b = args.get(1)?;
            if const_int_value(b).is_some_and(|v| (0..i128::from(width)).contains(&v)) {
                return None;
            }
            let (bf, br) = ranged(func, b, 32, false);
            Some((
                Formula::And(vec![br, ge(bf, int(i128::from(width)))]),
                assertion(&format!("{m}: attempt to shift with overflow")),
            ))
        }
        // `strict_div/strict_div_euclid/strict_rem/strict_rem_euclid`: a zero
        // divisor, and (signed) `MIN / -1`.
        "strict_div" | "strict_div_euclid" | "strict_rem" | "strict_rem_euclid" => {
            let (x, rhs) = (args.first()?, args.get(1)?);
            if v2_divisor_is_nonzero_constant(rhs)
                && (!signed || const_int_value(rhs).is_some_and(|v| v != -1))
            {
                return None;
            }
            let (xf, xr) = ranged(func, x, width, signed);
            let (rf, rr) = ranged(func, rhs, width, signed);
            let mut bad = vec![eq(rf.clone(), int(0))];
            if signed {
                bad.push(Formula::And(vec![
                    eq(xf, crate::range::type_min_formula(width, true)),
                    eq(rf, int(-1)),
                ]));
            }
            Some((
                Formula::And(vec![xr, rr, Formula::Or(bad)]),
                assertion(&format!("{m}: divide by zero, or attempt to divide with overflow")),
            ))
        }
        // `{int}::from_str_radix(src, radix)`: radix outside `[2, 36]` panics
        // before the string is read. Its nightly sibling `from_ascii_radix`
        // (which `from_str_radix` calls) panics on the same radix (Trust,
        // ASCII-FROM-ASCII-RADIX-1, 2026-10-05).
        "from_str_radix" | "from_ascii_radix" | "from_ascii_bytes_radix" => {
            radix_row(func, args.get(1)?, 2, &format!("{m}: radix must lie in the range `[2, 36]`"))
        }
        _ => None,
    }
}

/// `true` iff [`int_op_row`]'s row for `leaf::m` (the operator trait's last
/// segment and its method) reads `Self`'s width. Only
/// `Add::add`, `Sub::sub` and `Mul::mul` do not. Those are the overflow-call
/// lane's rows ([`numeric_overflow_call`]), built at the call's destination type.
///
/// Trust (W32-PRIMINT-PIN-1, 2026-10-06).
fn int_op_reads_width(leaf: &str, m: &str, signed: bool) -> bool {
    match (leaf, m) {
        ("Add", "add") | ("Sub", "sub") | ("Mul", "mul") => false,
        // No unsigned `Neg` impl exists, and `int_op_row` mints nothing for one.
        ("Neg", "neg") => signed,
        _ => true,
    }
}

/// `Add::add(a, b)` / `Sub::sub` / `Mul::mul` / `Neg::neg(a)` / `Shl::shl(a, b)` /
/// `Shr::shr` on a primitive integer, BY VALUE: exactly the obligation the
/// operator spelling `a + b` owes (its checked `BinaryOp` is refuted by the
/// safety lane), so the explicit trait call can no longer skip it.
fn int_op_row(
    func: &VerifiableFunction,
    width: u32,
    signed: bool,
    tr: &str,
    m: &str,
    args: &[Operand],
) -> Option<(Formula, VcKind)> {
    let a = args.first()?;
    if !is_int_like(func, a) {
        return None;
    }
    let (af, ar) = ranged(func, a, width, signed);
    let op = tr.rsplit("::").next()?;
    match (op, m) {
        // `Add::add`/`Sub::sub`/`Mul::mul` are minted by the overflow-call lane
        // (see [`numeric_overflow_call`]).
        ("Neg", "neg") if signed => Some((
            Formula::And(vec![ar, eq(af, crate::range::type_min_formula(width, true))]),
            assertion("Neg::neg: attempt to negate with overflow"),
        )),
        ("Shl", "shl") | ("Shr", "shr") => shift_overflow_row(func, width, op, m, args.get(1)?),
        _ => None,
    }
}

/// A shift by `b` on a `width`-bit primitive panics ("attempt to shift with
/// overflow") iff `b < 0 || b >= width`; `None` for a literal in range.
fn shift_overflow_row(
    func: &VerifiableFunction,
    width: u32,
    op: &str,
    m: &str,
    b: &Operand,
) -> Option<(Formula, VcKind)> {
    if !is_int_like(func, b) {
        return None;
    }
    if const_int_value(b).is_some_and(|v| (0..i128::from(width)).contains(&v)) {
        return None;
    }
    let (bw, bs) = crate::operand_ty_cow(func, b)
        .and_then(|t| Some((t.int_width()?, t.is_signed())))
        .unwrap_or((32, false));
    let (bf, br) = ranged(func, b, bw, bs);
    Some((
        Formula::And(vec![
            br,
            Formula::Or(vec![lt(bf.clone(), int(0)), ge(bf, int(i128::from(width)))]),
        ]),
        assertion(&format!("{op}::{m}: attempt to shift with overflow")),
    ))
}

/// `<iN as OpAssign>::op_assign(&mut a, b)` on a primitive integer, BY VALUE `b`.
/// `ShlAssign`/`ShrAssign`: the shift row over `b`, the only operand their panic
/// depends on. `AddAssign`/`SubAssign`/`MulAssign` are minted by the
/// overflow-call lane ([`numeric_overflow_call`]'s `AssignBinOp`); they reach
/// here only for a shape that lane declined — a right operand that is not an
/// integer, or a receiver that is not a place — and are refused.
fn int_assign_op_row(
    func: &VerifiableFunction,
    width: u32,
    tr: &str,
    m: &str,
    args: &[Operand],
) -> Option<(Formula, VcKind)> {
    let op = tr.rsplit("::").next()?;
    match (op, m) {
        ("ShlAssign", "shl_assign") | ("ShrAssign", "shr_assign") => {
            shift_overflow_row(func, width, op, m, args.get(1)?)
        }
        ("AddAssign", "add_assign") | ("SubAssign", "sub_assign") | ("MulAssign", "mul_assign") => {
            unmodeled(
                "int-assign-op-overflow-unmodeled",
                "AddAssign/SubAssign/MulAssign on a primitive integer panics (\"attempt to \
                 add/subtract/multiply with overflow\") under overflow checks; this call's \
                 operands are not modeled — refused, never silently verified (use \
                 `checked_add`/`wrapping_add` or the `+=` operator)",
            )
        }
        _ => None,
    }
}

/// Trust (2026-10-02, KNOWN_HAZARDS "`certify` exits 0 on a literal `clamp` whose only
/// row is a `native-verification-gap` `unknown`"): a row whose failure condition the
/// recognizer DECIDED from literal arguments. It is emitted either way, with the decided
/// value as its violation formula. It used to be emitted only when it could fail, and a
/// literal that could not (`x.clamp(-10, 10)`) charged NOTHING: the call's only
/// obligation vanished, the bridged inventory was empty, and `certify` passed a function
/// with zero proved rows on the empty-inventory early return. A `false` violation is an
/// obligation the ordinary discharge proves, so the call is now charged and its proof is
/// on its own row.
fn decided_row(fails: bool, message: &str) -> Option<(Formula, VcKind)> {
    Some((Formula::Bool(fails), assertion(message)))
}

/// `f32::clamp`/`f64::clamp(self, min, max)`: `min > max` OR either is NaN.
/// The verifier's float guards are not IEEE-faithful for NaN, so no path fact
/// may discharge it: literal bounds are decided here, everything else is
/// refused (the idiom `x.clamp(0.0, 1.0)` stays green).
fn float_clamp_row(args: &[Operand]) -> Option<(Formula, VcKind)> {
    let (lo, hi) = (args.get(1)?, args.get(2)?);
    if let (Some(a), Some(b)) = (const_float_value(lo), const_float_value(hi)) {
        // `a <= b` is false for a NaN on either side, which is std's own test.
        return decided_row(!(a <= b), "float clamp: min > max, or either was NaN");
    }
    unmodeled(
        "float-clamp-bounds-unmodeled",
        "f32/f64::clamp panics when min > max or either bound is NaN; a non-literal float \
         bound's NaN-ness is not modeled, so the ordering cannot be established — refused, \
         never silently verified (clamp with literal bounds, or `max(lo).min(hi)`)",
    )
}

/// `Ord::clamp(self, min, max)`: `assert!(min <= max)`. Precise for an integer
/// or `char` self type (`min > max`); fail-closed for every other `Ord` type,
/// whose ordering the verifier cannot compare.
fn ord_clamp_row(
    func: &VerifiableFunction,
    self_ty: &str,
    args: &[Operand],
) -> Option<(Formula, VcKind)> {
    let (lo, hi) = (args.get(1)?, args.get(2)?);
    let self_ty = self_ty.trim();
    let primitive = primitive_int(self_ty).is_some() || self_ty == "char";
    if primitive && is_int_like(func, lo) && is_int_like(func, hi) {
        if let (Some(a), Some(b)) = (const_int_value(lo), const_int_value(hi)) {
            return decided_row(a > b, "Ord::clamp: min > max");
        }
        // `min > max` reads no width. Both bounds are typed (`is_int_like`), so this
        // width is only `ranged`'s fallback.
        let (width, signed) = match primitive_int(self_ty) {
            Some((IntWidth::Fixed(w), s)) => (w, s),
            Some((IntWidth::Pointer, s)) => (POINTER_WIDTH_RANGE_FALLBACK, s),
            None => (32, false),
        };
        let (lf, lr) = ranged(func, lo, width, signed);
        let (hf, hr) = ranged(func, hi, width, signed);
        return Some((Formula::And(vec![lr, hr, gt(lf, hf)]), assertion("Ord::clamp: min > max")));
    }
    if is_duration_ty(self_ty)
        && let (Some(a), Some(b)) =
            (literal_duration_nanos(func, lo, 6), literal_duration_nanos(func, hi, 6))
    {
        return decided_row(a > b, "Ord::clamp: min > max");
    }
    unmodeled(
        "ord-clamp-bounds-unmodeled",
        "Ord::clamp panics when min > max; the ordering of this type's bounds is not \
         modeled (only primitive integers and `char` are), so it cannot be established — \
         refused, never silently verified (use `max(lo).min(hi)`)",
    )
}

// ---- integer / char range iteration --------------------------------------------

/// A range ITERATOR type (a rendered SELF type, `&mut` peeled): `(family, T)`,
/// where `family` is the `core::ops` name whose panics [`range_iter_can_panic`]
/// and [`range_iter_row`] model. Two spellings answer:
///
///   * `core::ops::range::{Range,RangeFrom,RangeInclusive}<T>`, the legacy
///     ranges, which are their own iterators;
///   * `core::range::iter::{RangeIter,RangeFromIter,RangeInclusiveIter}<T>`, the
///     by-value iterators of the stable `core::range` types (1.95/1.96), as
///     families `Range`, `RangeFrom` and `RangeInclusive`.
///
/// The peel matters for the explicit `<&mut RangeFrom<u8> as Iterator>::next(..)`,
/// which forwards to the range's own `next` inside the library and built rc=0
/// unpeeled (review of `ff3a28cc92`, 2026-09-28).
///
/// Trust (NEW-RANGE-ITER-UNCHARGED-1, 2026-10-11): the second spelling. Core's
/// `RangeFromIter::{next, nth}` call `Step::forward`, which panics past `MAX`
/// (an unconditional `expect` for `char`, the overflow check for an integer), and
/// `RangeIter::count` / `RangeInclusiveIter::count` forward to the legacy range's
/// `count` ("count overflowed usize") (`library/core/src/range/iter.rs`). Only
/// the `core::ops` spelling answered, so on the stage 1 of `1213387e6d`
/// `RangeFrom::from(c..).into_iter()` followed by `next(); next()`, `nth`, `find`
/// and `position`, and `RangeInclusive::from(a..=b).into_iter().count()` over
/// `u64` built rc=0 under the default policy and panicked at `char::MAX`, while the
/// `core::ops` twin `(c..)` was refused (`tests/ui/trust/new_range_iter_step_charged.rs`).
/// The new iterators' `count` receiver is an `into_iter` call result, so its bounds
/// are not traced and a too-wide count takes the fail-closed
/// `range-count-overflow-unmodeled` row. The type token is matched EXACTLY: the
/// `core::range::{Range,RangeFrom,RangeInclusive}` types themselves are
/// `IntoIterator`, not `Iterator`, and never answer here.
pub(super) fn range_self(inner: &str) -> Option<(&str, &str)> {
    let t = vc_peel_reference_prefixes(inner);
    if !trust_types::path_root_is_authenticated_sysroot_crate(t) {
        return None;
    }
    let (family, elem) = if let Some(rest) = t.strip_prefix("core::ops::range::") {
        let (name, elem) = rest.split_once('<')?;
        let family = match name {
            "Range" | "RangeFrom" | "RangeInclusive" => name,
            _ => return None,
        };
        (family, elem)
    } else {
        let rest = t.strip_prefix("core::range::iter::")?;
        let (name, elem) = rest.split_once('<')?;
        let family = match name {
            "RangeIter" => "Range",
            "RangeFromIter" => "RangeFrom",
            "RangeInclusiveIter" => "RangeInclusive",
            _ => return None,
        };
        (family, elem)
    };
    Some((family, elem.strip_suffix('>')?.trim()))
}

/// Trust (NEW-RANGE-REMAINDER-UNCHARGED-1, wave-24 review, 2026-10-12): the element
/// type `T` of `core::range::iter::RangeFromIter::<T>::remainder`, the nightly inherent
/// method (`new_range_remainder`), for a core `Step` `T` ([`is_core_step_elem`]); `None`
/// for every other callee.
///
/// `remainder(self)` returns `RangeFrom { start: Step::forward(self.start, 1) }` when the
/// iterator is EXHAUSTED (`library/core/src/range/iter.rs`, under
/// `#[rustc_inherit_overflow_checks]`): a `next()` that yielded `MAX` sets `exhausted`
/// instead of panicking, so the remainder of an iterator that reached `MAX` panics
/// ("overflow in `Step::forward`" for `char`, the add-overflow check for an integer).
/// It is an INHERENT method, so the `Iterator` arm ([`range_self`],
/// [`range_iter_can_panic`]) never saw it, and NEW-RANGE-ITER-UNCHARGED-1's fix left it
/// uncharged: on the stage 1 of `51eac007f3`, `let mut it = RangeFrom::from(c..)
/// .into_iter(); it.by_ref().take(1).for_each(drop); it.remainder()` built rc=0 under
/// the default policy with one `runtime_checked` row, and a verify-off driver exited
/// 101 at `char::MAX` and `u8::MAX`. Core's `ops::RangeFrom` has no such method. Whether
/// the iterator is exhausted is the caller's loop-carried state, so the call takes the
/// same fail-closed `range-from-step-overflow-unmodeled` row as an advancing `RangeFrom`
/// call. The other new iterators' `remainder` methods move their fields and cannot
/// panic. Trust (STEP-ELEM-RANGEFROM-1, 2026-10-13): `NonZero`, `AsciiChar` and the
/// IP-address elements, recorded here as the family's residual, are now matched too,
/// through [`is_core_step_elem`]. The type token is exact: a user `RangeFromIter`, a
/// user element type or a stamped impersonator root does not answer.
fn range_from_iter_remainder_elem(callee: &str) -> Option<&str> {
    let elem = callee
        .strip_prefix("core::range::iter::RangeFromIter::<")?
        .strip_suffix(">::remainder")?
        .trim();
    if !trust_types::path_root_is_authenticated_sysroot_crate(callee) {
        return None;
    }
    is_core_step_elem(elem).then_some(elem)
}

/// The `Iterator` methods on a `RangeFrom` that do NOT advance it at their own
/// call: `size_hint`, `by_ref`, and the lazy ADAPTORS, which move the range
/// into (or borrow it for) a struct whose own `next` advances it later, inside
/// the library, with no call site in the user's body. Every OTHER method —
/// `next`/`nth` and each consumer (`find`, `any`, `position`, `count`, `fold`,
/// `sum`, `collect`, ...) — advances it here and is charged. The adaptors are
/// the recorded survivor (`(1u8..).zip(v)`, `(0u8..).take(n)`).
const RANGE_FROM_NON_ADVANCING: &[&str] = &[
    "size_hint",
    "by_ref",
    "take",
    "skip",
    "step_by",
    "chain",
    "zip",
    "map",
    "filter",
    "filter_map",
    "enumerate",
    "peekable",
    "skip_while",
    "take_while",
    "map_while",
    "scan",
    "flat_map",
    "flatten",
    "fuse",
    "inspect",
    "cloned",
    "copied",
    "cycle",
    "array_chunks",
    "intersperse",
    "intersperse_with",
    "map_windows",
];

/// Which range iterations panic on a VALUE (the audit's §8):
///  * `RangeFrom<T>` over a core `Step` type `T` ([`is_core_step_elem`]) —
///    `Step::forward` past `MAX` (an overflow check for an integer or `NonZero`, an
///    unconditional `expect` for `char`, `AsciiChar` and the IP addresses), in
///    `next`/`nth` and in every consumer that calls them (widened from `next`/`nth`
///    after the review of `ff3a28cc92` measured `find`/`any`/`position`/`count` rc=0
///    and panicking at -O0); see [`RANGE_FROM_NON_ADVANCING`]. Trust
///    (STEP-ELEM-RANGEFROM-1, 2026-10-13): this read `int | char` only, so the
///    non-integer core `Step` types were advanced with no row;
///  * `Range<T>::count` and `RangeInclusive<T>::count` — "count overflowed
///    usize" — when the count can exceed the TARGET's `usize::MAX`
///    ([`range_count_can_overflow`]).
///
/// Every other method cannot.
///
/// For a count, the answer is for EVERY pointer width in [`POINTER_WIDTHS`]. A
/// name carries no target. At a call, [`range_iter_row`] then decides for the
/// call's own target, from its `usize` destination. Trust (W32-PRIMINT-PIN-1,
/// 2026-10-06): this gate used to read only the 64-bit answer (`Range<u128>`, and
/// `RangeInclusive` of a 64- or 128-bit element). On i686 and wasm32,
/// `(a..=b).count()` over `u32` and `(a..b).count()` over `u64` got no count row.
/// Both panic there: under `cfg(target_pointer_width = "32")`, core's `Step`
/// impls for `u64`/`i64` are "wider than usize". And the `usize` row was PROVED,
/// because its `usize::MAX` was the 64-bit one.
fn range_iter_can_panic(leaf: &str, elem: &str, m: &str) -> bool {
    match (leaf, m) {
        ("RangeFrom", _) => is_core_step_elem(elem) && !RANGE_FROM_NON_ADVANCING.contains(&m),
        ("Range" | "RangeInclusive", "count") => {
            POINTER_WIDTHS.iter().any(|&p| range_count_can_overflow(leaf, elem, p))
        }
        _ => false,
    }
}

/// Can `count` on a `leaf<elem>` range exceed `usize::MAX` on a target whose
/// pointers are `p` bits wide?
///
/// Core computes `Step::steps_between(start, end)` and calls
/// `.expect("count overflowed usize")` on it. `RangeInclusive` also adds one,
/// through `checked_add`. A `w`-bit element spans at most `2^w - 1` steps. So
/// `Range` can overflow iff `w > p`, and `RangeInclusive` iff `w >= p`. A
/// `usize`/`isize` element is `p` bits wide. A `char` spans at most
/// `0x10FFFF - 0x800` steps (core skips the surrogates), which is below `2^21`.
/// Trust (STEP-ELEM-RANGEFROM-1, 2026-10-13): the other core `Step` elements take their
/// span from [`non_int_step_span_bits`] (`Ipv6Addr` 128, `Ipv4Addr` 32, `NonZero<uN>`
/// N, `AsciiChar` 7); they answered `false` here, so `(a..b).count()` over `Ipv6Addr`
/// had no row on a 64-bit target. A user element still answers `false`: its
/// `steps_between` is the user's own.
fn range_count_can_overflow(leaf: &str, elem: &str, p: u32) -> bool {
    let span_bits = match primitive_int(elem) {
        Some((IntWidth::Fixed(w), _)) => w,
        Some((IntWidth::Pointer, _)) => p,
        None => match non_int_step_span_bits(elem, p) {
            Some(bits) => bits,
            None => return false,
        },
    };
    if leaf == "Range" { span_bits > p } else { span_bits >= p }
}

/// The target's pointer width, read from a call's `usize` destination: its
/// declared carrier `Ty::Int { width: p, signed: false }`, with `p` in
/// [`POINTER_WIDTHS`].
fn usize_destination_width(func: &VerifiableFunction, dest: &Place) -> Option<u32> {
    match crate::place_ty_cow(func, dest)?.as_ref() {
        Ty::Int { width, signed: false } if POINTER_WIDTHS.contains(width) => Some(*width),
        _ => None,
    }
}

fn range_iter_row(
    func: &VerifiableFunction,
    family: &str,
    elem: &str,
    args: &[Operand],
    dest: &Place,
) -> Option<(Formula, VcKind)> {
    if family == "RangeFrom" {
        // The receiver is `&mut RangeFrom`, advanced by every call — its CURRENT
        // start is loop-carried state no single call site pins. Refused.
        return unmodeled(
            "range-from-step-overflow-unmodeled",
            "iterating an `a..` range over a core `Step` type panics when the next value \
             would pass the type's MAX (`Step::forward` overflow); the range's current \
             start is not modeled at this call — refused, never silently verified \
             (iterate a bounded `a..=MAX` range, or use `checked_add`)",
        );
    }
    // Trust (W32-PRIMINT-PIN-1, 2026-10-06): `count` returns `usize`, so the
    // call's destination is declared at the target's pointer width. The bound is
    // that target's `usize::MAX`, not the 64-bit one.
    let Some(p) = usize_destination_width(func, dest) else {
        return pointer_width_unresolved("Iterator::count");
    };
    if !range_count_can_overflow(family, elem, p) {
        // Total on this target: the 64-bit host's `Range<u64>` and
        // `RangeInclusive<u32>`. There is no row, as there was none before.
        return None;
    }
    let Some((elem_width, signed)) = primitive_int(elem) else {
        // A count over a NON-integer core `Step` element that can exceed this target's
        // `usize` (`range_count_can_overflow`): `Ipv6Addr` on 64 bits, `Ipv4Addr` or
        // `NonZero<u32>` inclusive on 32, `char` only on 16. Its step count (the
        // surrogate gap for `char`, the `to_bits` view for the addresses) is not
        // modeled. Trust (STEP-ELEM-RANGEFROM-1, 2026-10-13): this message named
        // `char` only, the one non-integer element that reached it before.
        return unmodeled(
            "range-count-overflow-unmodeled",
            "Iterator::count on a range over a non-integer core `Step` type panics \
             (\"count overflowed usize\") when the step count exceeds this target's \
             usize::MAX; this range's step count is not modeled — refused, never silently \
             verified",
        );
    };
    let width = match elem_width {
        IntWidth::Fixed(w) => w,
        IntWidth::Pointer => p,
    };
    let usize_max = int((1i128 << p) - 1);
    let receiver = operand_local(args.first()?);
    let bounds = receiver.and_then(|local| {
        if family == "Range" {
            match trace_local_to_range_family(func, local, 8)? {
                RangeFamilyOperands::Exclusive(s, e) => Some((s, e)),
                _ => None,
            }
        } else if let Some(LocalDef::Call { callee, args }) = local_def(func, local)
            && is_range_inclusive_new_call(callee)
            && args.len() == 2
        {
            Some((&args[0], &args[1]))
        } else {
            None
        }
    });
    let Some((start, end)) = bounds else {
        return unmodeled(
            "range-count-overflow-unmodeled",
            "Iterator::count on an `a..b` range whose element is wider than this target's \
             usize, or on an `a..=b` range whose element is at least as wide, panics \
             (\"count overflowed usize\") when the step count exceeds usize::MAX; this \
             range's bounds are not traced — refused, never silently verified",
        );
    };
    let (sf, sr) = ranged(func, start, width, signed);
    let (ef, er) = ranged(func, end, width, signed);
    let steps = Formula::Sub(Box::new(ef.clone()), Box::new(sf.clone()));
    let bad = if family == "Range" {
        Formula::And(vec![lt(sf, ef), gt(steps, usize_max)])
    } else {
        Formula::And(vec![le(sf, ef), ge(steps, usize_max)])
    };
    Some((Formula::And(vec![sr, er, bad]), assertion("Iterator::count: count overflowed usize")))
}

// ---- Duration / Instant / SystemTime ------------------------------------------

const NANOS_PER_SEC: u128 = 1_000_000_000;

/// The value (in nanoseconds) of a `Duration` this function builds from
/// LITERALS: `Duration::from_secs/from_millis/from_micros/from_nanos(c)` or
/// `Duration::new(s, n)` with in-range literals, possibly through copies.
/// `None` for anything else — a parameter, a computed value, a constant item.
fn literal_duration_nanos(func: &VerifiableFunction, op: &Operand, depth: u32) -> Option<u128> {
    if depth == 0 {
        return None;
    }
    let local = operand_local(op)?;
    match local_def(func, local)? {
        LocalDef::Rvalue(Rvalue::Use(inner)) => literal_duration_nanos(func, inner, depth - 1),
        LocalDef::Call { callee, args } => {
            // `a + b`, `a - b`, `d * k`, `k * d` over literal operands — the
            // result of an arithmetic call this function already decided (a
            // call that cannot be decided is charged at its own site).
            if let Some((self_ty, tr, _)) = qualified_std_trait_method(callee, DURATION_OPS) {
                let (a, b) = (args.first()?, args.get(1)?);
                let factor =
                    |op: &Operand| const_int_value(op).and_then(|v| u128::try_from(v).ok());
                let nanos = match (tr.rsplit("::").next()?, is_duration_ty(self_ty)) {
                    ("Add", true) => literal_duration_nanos(func, a, depth - 1)?
                        .checked_add(literal_duration_nanos(func, b, depth - 1)?)?,
                    ("Sub", true) => literal_duration_nanos(func, a, depth - 1)?
                        .checked_sub(literal_duration_nanos(func, b, depth - 1)?)?,
                    ("Mul", true) => {
                        literal_duration_nanos(func, a, depth - 1)?.checked_mul(factor(b)?)?
                    }
                    ("Mul", false) => {
                        literal_duration_nanos(func, b, depth - 1)?.checked_mul(factor(a)?)?
                    }
                    _ => return None,
                };
                return (nanos <= duration_max_nanos()).then_some(nanos);
            }
            let m = duration_inherent(callee)?;
            let lit = |i: usize| -> Option<u128> {
                args.get(i).and_then(const_int_value).and_then(|v| u128::try_from(v).ok())
            };
            let nanos = match m {
                "from_secs" => lit(0)?.checked_mul(NANOS_PER_SEC)?,
                "from_millis" => lit(0)?.checked_mul(1_000_000)?,
                "from_micros" => lit(0)?.checked_mul(1_000)?,
                "from_nanos" => lit(0)?,
                "new" => {
                    let (s, n) = (lit(0)?, lit(1)?);
                    s.checked_mul(NANOS_PER_SEC)?.checked_add(n)?
                }
                _ => return None,
            };
            // `Duration::MAX` is `u64::MAX` seconds + 999_999_999 ns.
            (nanos <= u128::from(u64::MAX) * NANOS_PER_SEC + (NANOS_PER_SEC - 1)).then_some(nanos)
        }
        _ => None,
    }
}

/// `Duration`'s value ceiling, in nanoseconds.
fn duration_max_nanos() -> u128 {
    u128::from(u64::MAX) * NANOS_PER_SEC + (NANOS_PER_SEC - 1)
}

/// A literal `Duration` small enough that adding it to (or subtracting it from)
/// a FRESH CLOCK READING — `Instant::now()` / `SystemTime::now()` taken in this
/// function ([`is_fresh_clock_reading`]) — cannot overflow: at most 2^62
/// seconds. That reading's position is hidden clock state (policy B); only the
/// caller-visible `Duration` is charged.
///
/// It is NOT a bound for an arbitrary time point. A caller can build an
/// `Instant`/`SystemTime` at the representable edge (`checked_add` to the
/// largest value that fits, or the unstable `SystemTime::MAX`) and hand it in:
/// `fn f(t: Instant) -> Instant { t + Duration::from_secs(1) }` built rc=0 and
/// panicked "overflow when adding duration to instant" at -O0 and -O (review
/// of `ff3a28cc92`, 2026-09-28) while this carve-out ignored the receiver.
const TIME_POINT_LITERAL_CEILING_SECS: u128 = 1 << 62;

/// `std::time::Instant::now` / `std::time::SystemTime::now`, on an
/// authenticated sysroot root.
pub(super) fn is_clock_reading_callee(callee: &str) -> bool {
    trust_types::path_root_is_authenticated_sysroot_crate(callee)
        && matches!(
            vc_strip_generics_cow(callee).as_ref(),
            "std::time::Instant::now" | "std::time::SystemTime::now"
        )
}

/// `true` iff `op` holds, at every read, the result of ONE `Instant::now()` /
/// `SystemTime::now()` call this function made — directly, or through
/// whole-local copies. Asked through the `local_defs` resolvers, which decline
/// a PARAMETER (its entry value is the caller's), a second write (a
/// loop-carried `t = t + d`), and a `&mut` alias (`LocalWrite::Escape`, so an
/// assign-form `t += d` receiver never qualifies). An opaque constant time point
/// is NOT a reading: `UNIX_EPOCH` and the unstable `SystemTime::MAX` both lower
/// to one.
fn is_fresh_clock_reading(func: &VerifiableFunction, op: &Operand, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }
    let Some(local) = operand_local(op) else { return false };
    if let Some(Terminator::Call { func: callee, .. }) =
        crate::local_defs::unique_value_call(func, local)
    {
        return is_clock_reading_callee(callee);
    }
    match crate::local_defs::unique_value_def(func, local) {
        Some(Rvalue::Use(inner)) => is_fresh_clock_reading(func, inner, depth - 1),
        _ => false,
    }
}

fn duration_method_row(
    func: &VerifiableFunction,
    m: &str,
    args: &[Operand],
) -> Option<(Formula, VcKind)> {
    match m {
        // `Duration::new(secs, nanos)`: panics "overflow in Duration::new" iff
        // `nanos >= 1e9` and `secs + nanos / 1e9 > u64::MAX`. `nanos: u32`, so the
        // carry is 1..=4 — expanded as a disjunction to stay linear and exact.
        "new" => {
            let (s, n) = (args.first()?, args.get(1)?);
            let (sf, sr) = ranged(func, s, 64, false);
            let (nf, nr) = ranged(func, n, 32, false);
            let max = u128::from(u64::MAX);
            let carries = (1u32..=4)
                .map(|q| {
                    Formula::And(vec![
                        ge(nf.clone(), int(i128::from(q) * 1_000_000_000)),
                        gt(sf.clone(), Formula::UInt(max - u128::from(q))),
                    ])
                })
                .collect();
            Some((
                Formula::And(vec![sr, nr, Formula::Or(carries)]),
                assertion("Duration::new: overflow in Duration::new"),
            ))
        }
        // `from_mins(m)` / `from_hours(h)`: `m > u64::MAX / 60` / `h > u64::MAX /
        // 3600` panics "overflow in Duration::from_mins/hours". The nightly
        // `from_days(d)` / `from_weeks(w)` (Trust, NUM-NIGHTLY-UNCHARGED-1,
        // 2026-10-06) test `d > u64::MAX / 86_400` / `w > u64::MAX / 604_800`
        // the same way (core `time.rs`: "overflow in Duration::from_days/weeks").
        "from_mins" | "from_hours" | "from_days" | "from_weeks" => {
            let per: u128 = match m {
                "from_mins" => 60,
                "from_hours" => 3_600,
                "from_days" => 86_400,
                _ => 604_800,
            };
            let x = args.first()?;
            let (xf, xr) = ranged(func, x, 64, false);
            Some((
                Formula::And(vec![xr, gt(xf, Formula::UInt(u128::from(u64::MAX) / per))]),
                assertion(&format!("Duration::{m}: overflow")),
            ))
        }
        // `from_nanos_u128(n)`: `n / 1e9 > u64::MAX` panics.
        "from_nanos_u128" => {
            let x = args.first()?;
            let (xf, xr) = ranged(func, x, 128, false);
            let ceiling = (u128::from(u64::MAX) + 1) * NANOS_PER_SEC - 1;
            Some((
                Formula::And(vec![xr, gt(xf, Formula::UInt(ceiling))]),
                assertion("Duration::from_nanos_u128: overflow"),
            ))
        }
        // `from_secs_f64/f32(s)`: panics on a negative, NaN, infinite or >= 2^64
        // value. Only a literal in `[0, 2^63)` is decided; the rest is refused.
        "from_secs_f64" | "from_secs_f32" => {
            if let Some(v) = args.first().and_then(const_float_value)
                && (0.0..9.2e18).contains(&v)
            {
                return None;
            }
            unmodeled(
                "duration-from-float-unmodeled",
                "Duration::from_secs_f64/f32 panics on a negative, NaN, infinite or too-large \
                 value; a non-literal float's value is not modeled — refused, never silently \
                 verified (use `Duration::try_from_secs_f64`)",
            )
        }
        // `mul_f64/mul_f32/div_f64/div_f32`: the result goes through
        // `from_secs_f64` and panics on a negative, NaN or too-large product —
        // which depends on the receiver as well as the factor. Refused.
        "mul_f64" | "mul_f32" | "div_f64" | "div_f32" => unmodeled(
            "duration-float-scale-unmodeled",
            "Duration::mul_f64/div_f64 (and the f32 forms) panic when the scaled value is \
             negative, NaN or exceeds Duration::MAX; the float product is not modeled — \
             refused, never silently verified (use `Duration::try_from_secs_f64` on the \
             scaled seconds)",
        ),
        _ => None,
    }
}

/// `Duration` `+ - * /` (and the `*Assign` forms, and `u32 * Duration`), and
/// `Instant`/`SystemTime` `± Duration`.
fn duration_op_row(
    func: &VerifiableFunction,
    self_ty: &str,
    tr: &str,
    m: &str,
    args: &[Operand],
) -> Option<(Formula, VcKind)> {
    let op = tr.rsplit("::").next()?;
    if is_time_point_ty(self_ty) {
        // `Instant/SystemTime + - Duration` (and the assign forms): panics when
        // the result is not representable. Charged unless the time point is a
        // fresh clock reading taken BY VALUE in this function and the Duration
        // is a literal no larger than `TIME_POINT_LITERAL_CEILING_SECS`.
        if !matches!(op, "Add" | "Sub" | "AddAssign" | "SubAssign")
            || !matches!(m, "add" | "sub" | "add_assign" | "sub_assign")
        {
            return None;
        }
        // `Instant - Instant` saturates (no panic): its right operand is not a
        // Duration.
        let rhs = args.get(1)?;
        if !matches!(crate::operand_ty_cow(func, rhs).as_deref(), Some(Ty::Adt { name, .. }) if is_duration_ty(name))
        {
            return None;
        }
        // An assign form's receiver is `&mut` state that earlier iterations may
        // have advanced; a by-value receiver must trace to `now()` itself.
        if matches!(op, "Add" | "Sub")
            && is_fresh_clock_reading(func, args.first()?, 6)
            && literal_duration_nanos(func, rhs, 6)
                .is_some_and(|n| n / NANOS_PER_SEC <= TIME_POINT_LITERAL_CEILING_SECS)
        {
            return decided_row(false, &format!("time point {op}: overflow"));
        }
        return unmodeled(
            "time-point-duration-overflow",
            "Instant/SystemTime + or - a Duration panics when the result is not \
             representable; only a small literal Duration added to or subtracted from \
             a fresh `Instant::now()`/`SystemTime::now()` reading is bounded — here the \
             Duration is not such a literal, or the time point is caller-supplied, \
             loop-carried or a constant — refused, never silently verified (use \
             `checked_add`/`checked_sub`)",
        );
    }
    let self_is_duration = is_duration_ty(self_ty);
    // `k * d` — `<u32 as Mul<Duration>>::mul`; a plain `u32` product is not ours.
    let self_is_u32 = self_ty.trim() == "u32"
        && matches!(crate::operand_ty_cow(func, args.get(1)?).as_deref(), Some(Ty::Adt { name, .. }) if is_duration_ty(name));
    if !self_is_duration && !self_is_u32 {
        return None;
    }
    match (op, self_is_duration) {
        // `d / k`, `d /= k`: panics "divide by zero error when dividing duration by
        // scalar" iff `k == 0` — exact, the `DivisionByZero` shape.
        ("Div" | "DivAssign", true) => {
            let k = args.get(1)?;
            if !is_int_like(func, k) {
                return None;
            }
            if v2_divisor_is_nonzero_constant(k) {
                // Decided: a nonzero literal divisor. Mint the row (see `decided_row`).
                return Some((Formula::Bool(false), VcKind::DivisionByZero));
            }
            Some((v2_divisor_is_zero_formula(func, k), VcKind::DivisionByZero))
        }
        // `a + b`, `a - b`, `d * k`, `k * d` (and assign forms): decided when every
        // operand is a literal; otherwise refused — `Duration`'s value is not
        // modeled, and the caller's operand can be `Duration::MAX`.
        ("Add" | "Sub" | "Mul" | "AddAssign" | "SubAssign" | "MulAssign", _) => {
            let (a, b) = (args.first()?, args.get(1)?);
            let decided = match op {
                "Add" => literal_duration_nanos(func, a, 6)
                    .zip(literal_duration_nanos(func, b, 6))
                    .map(|(x, y)| x + y <= duration_max_nanos()),
                "Sub" => literal_duration_nanos(func, a, 6)
                    .zip(literal_duration_nanos(func, b, 6))
                    .map(|(x, y)| x >= y),
                "Mul" if self_is_duration => literal_duration_nanos(func, a, 6)
                    .zip(const_int_value(b).and_then(|v| u128::try_from(v).ok()))
                    .map(|(x, k)| x.checked_mul(k).is_some_and(|p| p <= duration_max_nanos())),
                "Mul" => literal_duration_nanos(func, b, 6)
                    .zip(const_int_value(a).and_then(|v| u128::try_from(v).ok()))
                    .map(|(x, k)| x.checked_mul(k).is_some_and(|p| p <= duration_max_nanos())),
                _ => None,
            };
            // A literal factor of 0 or 1 cannot overflow whatever the Duration.
            let trivial_factor = op.starts_with("Mul")
                && const_int_value(if self_is_duration { b } else { a })
                    .is_some_and(|k| k == 0 || k == 1);
            match decided {
                Some(true) => decided_row(false, &format!("Duration {op}: overflow")),
                _ if trivial_factor => decided_row(false, &format!("Duration {op}: overflow")),
                Some(false) => decided_row(true, &format!("Duration {op}: overflow")),
                None => unmodeled(
                    "duration-arith-overflow-unmodeled",
                    "Duration + - * panics (\"overflow when adding/subtracting/multiplying \
                     durations\") when the result leaves [0, Duration::MAX]; a non-literal \
                     Duration's value is not modeled — refused, never silently verified (use \
                     `checked_add`/`checked_sub`/`checked_mul` or the `saturating_` forms)",
                ),
            }
        }
        _ => None,
    }
}
