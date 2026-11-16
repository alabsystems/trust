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
///
/// Trust (2026-10-06, DIVZERO-NAME-1): this MINTS core's zero-divisor row over the
/// caller's own argument, so it answers only for the callees whose zero-divisor
/// panic is core's:
///   * `div_euclid` / `div_ceil` / `rem_euclid` under an AUTHENTICATED sysroot root
///     (`trust_types::path_root_is_authenticated_sysroot_crate`: a `core::` /
///     `alloc::` / `std::` path that carries no `__trust_crate@` stamp). That is
///     wider than `numeric_panic::int_inherent` on purpose: core's
///     `Wrapping`/`Saturating`/`NonZero` owners keep exactly the row they had, so
///     no sysroot spelling loses one;
///   * `step_by` only as std's `Iterator::step_by` (`iterator_yield::callee_is_step_by`:
///     the generic `core::iter::…::Iterator::step_by` and every qualified `<X as
///     core::iter::traits::iterator::Iterator>::step_by`, a user iterator that
///     inherits std's panicking default included).
///
/// It used to read the last path segment alone, so a USER function or method
/// merely named `div_ceil`, `rem_euclid`, `div_euclid` or `step_by` — `Q::div_ceil(a,
/// b) { a ^ b }`, a free `rem_euclid(a, b) { a | b }`, `S::step_by(&self, n) -> n`,
/// a user trait's `<u8 as Euclid>::rem_euclid` — was charged `divisor != 0` over
/// its own arguments and REFUTED with a counterexample (`a = 0, b = 0`) for a
/// division that never happens. Measured on the stage 1 of `4ccd862830`: each
/// caller was refused ("Level 0 safety verification incomplete" plus "strict
/// verification failed", `[divzero]`/`[remzero] FAILED`) while the callee's own row
/// read `no_obligations | proved | trust-structural`, and a verify-off build of the
/// same calls returned 0. A user namesake mints no row here; whatever it does is in
/// its own body, which is verified as its own function (a user `fn div_ceil(a, b)
/// { a / b }` is refuted there, through its own `BinaryOp(Div)` row).
///
/// Every spelling this answers `Some` for, [`divzero_call_name_only`] answers the
/// same for; the deny-list `callee_has_call_site_panic_family` reads that twin.
///
/// Trust (wave-21 integration, 2026-10-09; STAMPED-CORE-MINT-1's rule): the owner
/// check also reads past ONE well-formed leading `__trust_crate@<16 hex>::` stamp
/// (`numeric_panic::after_one_identity_stamp`), as `numeric_panic::int_inherent_minting`
/// does for `abs`, `pow` and `unchecked_*`. The extractor stamps the GENUINE core
/// whenever a second crate named `core` is in the graph, or under `-Zbuild-std`; a
/// stamp says "not authenticated", not "impersonator". The tail-only recognizer
/// minted core's row for those stamped spellings, and an authenticated-root check
/// alone would drop it. MEASURED on the stage 1 of `4e580ff4ab` (main before this
/// wave) with a verify-off aux named `core` in the graph
/// (`tests/ui/trust/stamped_genuine_core_divzero_row_kept.rs`): `a.div_euclid(b)` and `a.rem_euclid(b)` over
/// `u32` are refused with `[divzero]` / `[remzero] FAILED` (a = 0, b = 0) beside one
/// `runtime_checked` absent-callee row. That row alone still refuses the function
/// under the default policy (the guarded twins are refused on it), so dropping the
/// zero-divisor row would turn a refutation with a counterexample into a bare
/// "not fully verified", not flip a verdict. The row is kept all the same. This arm
/// only ADDS a row over the call's own argument, so a forged stamped spelling can at
/// worst be charged a row it does not owe (a false red), as the tail-only matcher
/// charged every spelling.
pub(super) fn divzero_call(callee: &str) -> Option<(usize, VcKind)> {
    let row = divzero_call_name_only(callee)?;
    let core_owned = |path: &str| {
        let tail = path.rsplit("::").next().unwrap_or(path);
        let tail = tail.split('<').next().unwrap_or(tail).trim();
        if tail == "step_by" {
            super::iterator_yield::callee_is_step_by(path)
        } else {
            trust_types::path_root_is_authenticated_sysroot_crate(path)
        }
    };
    (core_owned(callee)
        || super::numeric_panic::after_one_identity_stamp(callee).is_some_and(core_owned))
    .then_some(row)
}

/// The method-tail view of [`divzero_call`], with no owner check: `div_euclid`,
/// `div_ceil` and `step_by` name `DivisionByZero` and `rem_euclid` names
/// `RemainderByZero` on arg 1, whatever crate or type the callee belongs to.
///
/// Trust (2026-10-06, DIVZERO-NAME-1): only `callee_has_call_site_panic_family`
/// reads this. There a `Some` only WITHHOLDS the vanilla admission of a
/// real-sysroot fn item the compiler has already authenticated
/// (`foreign_fn_item_type_arg_is_accounted`), so keeping the wider match leaves that
/// gate's answer byte-identical rather than moving it by a change nobody measured.
/// It must never mint a row — the same split as
/// `alloc_bounds::overflow_arith_call_name_only` and
/// `unwrap_panic::is_signed_abs_call_name_only`.
pub(super) fn divzero_call_name_only(callee: &str) -> Option<(usize, VcKind)> {
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
        // Trust (2026-09-30): the rest of the primitive-integer division family
        // (`trust_ir_bridge::is_panicking_primitive_int_div_method`). Each reports or
        // clamps the `MIN / -1` overflow and PANICS on a zero divisor, like `a / b`.
        // They had no row here because the bridge refused every such call with a
        // fatal absent-callee assumption; now that it lowers the call's exact panic
        // condition, this row is what refutes an unguarded call with a
        // counterexample (`wrapping_div_zero_false_proof.rs`). Anchored to std's own
        // `num` methods, so a user method of the same name gains no obligation.
        "wrapping_div"
        | "overflowing_div"
        | "saturating_div"
        | "wrapping_div_euclid"
        | "overflowing_div_euclid"
            if super::call_facts::is_std_num_intrinsic(callee) =>
        {
            Some((1, VcKind::DivisionByZero))
        }
        "wrapping_rem" | "overflowing_rem" | "wrapping_rem_euclid" | "overflowing_rem_euclid"
            if super::call_facts::is_std_num_intrinsic(callee) =>
        {
            Some((1, VcKind::RemainderByZero))
        }
        _ => None,
    }
}

/// The primitive integer type a `core::num::<impl T>::method` (or `std::num::`)
/// callee is a method of, read from the impl's self type in the path.
fn std_num_impl_receiver_ty(callee: &str) -> Option<Ty> {
    let rest = callee
        .strip_prefix("core::num::<impl ")
        .or_else(|| callee.strip_prefix("std::num::<impl "))?;
    let name = &rest[..rest.find('>')?];
    Some(match name {
        "i8" => Ty::Int { width: 8, signed: true },
        "i16" => Ty::Int { width: 16, signed: true },
        "i32" => Ty::Int { width: 32, signed: true },
        "i64" => Ty::Int { width: 64, signed: true },
        "i128" => Ty::Int { width: 128, signed: true },
        "isize" => Ty::isize(),
        "u8" => Ty::Int { width: 8, signed: false },
        "u16" => Ty::Int { width: 16, signed: false },
        "u32" => Ty::Int { width: 32, signed: false },
        "u64" => Ty::Int { width: 64, signed: false },
        "u128" => Ty::Int { width: 128, signed: false },
        "usize" => Ty::usize(),
        _ => return None,
    })
}

/// Trust (2026-09-30): the SIGNED `MIN / -1` overflow a std `div_euclid` or
/// `rem_euclid` call panics on besides a zero divisor ("if `self / rhs` results in
/// an overflow", `library/core/src/num/int_macros.rs`), the residual
/// [`divzero_call`]'s zero-divisor row never covered. Returns the violation
/// `self == MIN && rhs == -1` and its kind for a two-argument call on a signed
/// integer receiver; `None` for any other call, including the unsigned forms,
/// which cannot overflow.
pub(super) fn signed_euclid_overflow_call(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> Option<(Formula, VcKind)> {
    let [lhs, rhs] = args else { return None };
    let op = match method_tail(callee) {
        "div_euclid" => BinOp::Div,
        "rem_euclid" => BinOp::Rem,
        _ => return None,
    };
    if !super::call_facts::is_std_num_intrinsic(callee) {
        return None;
    }
    // The type is the callee's (`core::num::<impl i8>::div_euclid`), never an
    // operand's: an untyped literal reads as i64, so `(-128i8).div_euclid(-1)` got
    // the violation `-128 == i64::MIN && -1 == -1`, unsatisfiable, and the
    // panicking call proved at i8/i16/i32 (review round 17). Each operand must be
    // of that type or a literal that fits it.
    let ty = std_num_impl_receiver_ty(callee)?;
    let Ty::Int { width, signed: true } = ty else { return None };
    if !(1..=128).contains(&width) {
        return None;
    }
    let min = if width == 128 { i128::MIN } else { -(1i128 << (width - 1)) };
    let max = if width == 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
    let operand_fits = |op: &Operand| match op {
        Operand::Constant(ConstValue::Int(v)) => (min..=max).contains(v),
        _ => crate::operand_ty_cow(func, op).as_deref() == Some(&ty),
    };
    if !operand_fits(lhs) || !operand_fits(rhs) {
        return None;
    }
    let violation = Formula::And(vec![
        Formula::Eq(Box::new(operand_to_formula(func, lhs)), Box::new(Formula::Int(min))),
        Formula::Eq(Box::new(operand_to_formula(func, rhs)), Box::new(Formula::Int(-1))),
    ]);
    Some((violation, VcKind::ArithmeticOverflow { op, operand_tys: (ty.clone(), ty) }))
}

/// Recognize a slice method whose runtime panic is an out-of-bounds / zero-size
/// argument with no caller-visible `Projection::Index`. Mirrors [`divzero_call`]:
/// returns `None` for any unrecognized call so the recognizer NEVER broadly
/// fail-closes on every `Call` (that would break drop-in Rust). The callee path
/// is matched on its final segment so it works regardless of the `<impl [T]>` /
/// `core::slice::<impl [T]>::` qualification the MIR carries.
///
/// Trust (2026-10-11, SLICE-ZERO-SIZE-NAME-1): the three tail arms that MINT core's
/// slice row over the call's own arguments — `split_at`/`split_at_mut` (`mid > len`),
/// `chunks*`/`rchunks*`/`windows` (`n == 0`) and `swap` (`i >= len || j >= len`) —
/// answer only when the callee's ROOT is a sysroot crate, read past ONE well-formed
/// leading `__trust_crate@<16 hex>::` stamp (STAMPED-CORE-MINT-1's rule, as
/// [`divzero_call`] applies it). They used to read the last path segment alone, so
/// a USER method merely NAMED like one of them was charged core's row and REFUTED:
/// `impl Grid { fn windows(&self, n: usize) -> usize { self.w ^ n } }` called as
/// `g.windows(k)` was `[divzero] FAILED; counterexample: k = 0` plus "guaranteed
/// Level 0 safety violation", and `impl Tr for [u8] { fn swap(&self, i, j) -> usize
/// { i ^ j } }` was `[slice] FAILED` — while each callee's own row read
/// `no_obligations | proved | trust-structural`. Measured on the stage 1 of
/// `1213387e6d` (`scratchpad/scout24/szn/{ns2,ns3,sib}.rs`): rc=1 under the default
/// and `certify` policies; stock rustc 1.97.1 runs the same calls and prints `7 7 0`.
/// The rendered user spellings are `ns2::Grid::windows`, `<ns3::G2 as
/// ns3::Tiles>::chunks_exact`, `ns3::W::<[T]>::windows` and `<[u8] as
/// sib::Tr>::swap`; none is rooted at a sysroot crate, and whatever such a method
/// does is in its own body, verified as its own function.
///
/// WHY THE ROOT, NOT `trust_types::path_root_is_authenticated_sysroot_crate`. That
/// predicate also refuses a stamp ANYWHERE in the path, which is right for a matcher
/// that GRANTS, and wrong here, where answering `None` is the grant (the row is not
/// owed). Core's own method is rendered with its instantiation, and a fn-item element
/// type renders its def path through the stamping renderer (the deque tests pin
/// `…VecDeque::<fn(u32) -> __trust_crate@<id>::alloc::Id {…}>::swap`), so `a.swap(i,
/// j)` over `a: [Id; 3]`, `Id` a tuple-struct constructor of a crate the graph does not
/// authenticate, is `core::slice::<impl [fn(u32) -> __trust_crate@<id>::…]>::swap`:
/// core's method, with a stamp in its element type. The authenticated-root predicate
/// would drop core's row for it, a silent pass of an out-of-range swap. The owner of
/// an inherent `…::<impl X>::m`
/// path is the crate at its root (only the crate defining `[T]` can impl it), and a
/// trait method renders `<X as Trait>::m`, whose `<` is no sysroot root; so the root
/// alone decides ownership. A FORGED crate built `--crate-name core` (rendered behind a
/// leading stamp) is still charged — a row it may not owe, i.e. a false red, the
/// trade [`divzero_call`] documents. Not the keyed
/// `iterator_yield::vc_callee_is_slice_inherent` either: a call with no `callee_key`
/// would lose its row, which fails open.
///
/// The other arms are unchanged: the owner-checked `collection_method_panic`
/// (consulted first), `RangeIndex`, `VecPanicMethod` and `BTreeRange`. Every spelling
/// this answers `Some` for, [`slice_method_panic_name_only`] answers the same for;
/// the deny-list `callee_has_call_site_panic_family` reads that twin.
impl SliceMethodPanic {
    pub(super) fn classify_with_tail(callee: &str, tail: &str) -> Option<Self> {
        let panic = Self::classify_name_only_with_tail(callee, tail)?;
        // `collection_method_panic` never answers these three shapes (it owner-checks
        // its own members), so they come from the tail arms below.
        let minted_by_tail = matches!(
            panic,
            SliceMethodPanic::SplitAt { .. }
                | SliceMethodPanic::NonZeroArg { .. }
                | SliceMethodPanic::SwapIndices { .. }
        );
        let sysroot_rooted = |path: &str| {
            path.starts_with("core::") || path.starts_with("alloc::") || path.starts_with("std::")
        };
        let owned_by_sysroot = sysroot_rooted(callee)
            || super::numeric_panic::after_one_identity_stamp(callee).is_some_and(sysroot_rooted);
        (!minted_by_tail || owned_by_sysroot).then_some(panic)
    }

    pub(super) fn classify_name_only_with_tail(callee: &str, tail: &str) -> Option<Self> {
        if let Some(panic) = Self::classify_collection_with_tail(callee, tail) {
            return Some(panic);
        }
        match tail {
            "split_at" | "split_at_mut" => Some(SliceMethodPanic::SplitAt { mid_idx: 1 }),
            "chunks" | "chunks_mut" | "chunks_exact" | "chunks_exact_mut" | "rchunks"
            | "rchunks_mut" | "rchunks_exact" | "rchunks_exact_mut" | "windows" => {
                Some(SliceMethodPanic::NonZeroArg { n_idx: 1 })
            }
            "swap" => Some(SliceMethodPanic::SwapIndices { i_idx: 1, j_idx: 2 }),
            "remove" | "swap_remove" => {
                Some(SliceMethodPanic::VecPanicMethod { index_idx: 1, insert: false })
            }
            "insert" => Some(SliceMethodPanic::VecPanicMethod { index_idx: 1, insert: true }),
            "index" | "index_mut" => Some(SliceMethodPanic::RangeIndex),
            "range" | "range_mut" if is_btree_range_call(callee) => {
                Some(SliceMethodPanic::BTreeRange { range_idx: 1 })
            }
            _ => None,
        }
    }
}

pub(super) fn slice_method_panic(callee: &str) -> Option<SliceMethodPanic> {
    SliceMethodPanic::classify_with_tail(callee, method_tail(callee))
}

/// The method-tail view of [`slice_method_panic`], with no owner check on the
/// `split_at`/`chunks*`/`rchunks*`/`windows`/`swap` arms: whatever crate or type the
/// callee belongs to.
///
/// Trust (2026-10-11, SLICE-ZERO-SIZE-NAME-1): only `callee_has_call_site_panic_family`
/// reads this. There a `Some` only WITHHOLDS the vanilla admission of a real-sysroot
/// fn item the compiler has already authenticated, so keeping the wider match leaves
/// that gate's answer byte-identical. It must never mint a row — the same split as
/// [`divzero_call_name_only`].
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn slice_method_panic_name_only(callee: &str) -> Option<SliceMethodPanic> {
    SliceMethodPanic::classify_name_only_with_tail(callee, method_tail(callee))
}

/// True iff `op`'s type is a PANICKING slice-index range — exclusive `Range`,
/// `RangeTo`, `RangeFrom`, or `RangeInclusive`. `RangeFull` (`s[..]`, never panics)
/// and scalar `usize` (`Vec`/`HashMap` index) are excluded. Authoritative
/// discrimination for `RangeIndex`, robust to the erased generic callee path.
pub(super) fn operand_is_panicking_range(func: &VerifiableFunction, op: &Operand) -> bool {
    match crate::operand_ty_cow(func, op).as_deref() {
        Some(Ty::Adt { name, .. }) => {
            matches!(
                range_family_adt_name(name),
                // Trust (2026-09-25, std-range-family): `..=b` (`RangeToInclusive`) was
                // missing, so `s[..=b]` emitted no row at all and built rc=0.
                Some("Range" | "RangeTo" | "RangeFrom" | "RangeInclusive" | "RangeToInclusive")
            )
            // Trust (UTF8-CORE-RANGE-INDEX-1, 2026-10-05): the new range API's own
            // index types (`core::range::*`), which panic exactly like their
            // `core::ops` namesakes. See `new_range_index_adt_name`.
            || new_range_index_adt_name(name).is_some()
        }
        // Trust (2026-09-25, std-range-family): `s[(Bound, Bound)]` — the tuple
        // `SliceIndex` impl, which panics exactly like `start..end`. It was not a
        // "range" here, so the index emitted no row and built rc=0.
        Some(Ty::Tuple(elems)) => {
            elems.len() == 2
                && elems.iter().all(|t| {
                    matches!(t, Ty::Adt { name, .. } if name.split('<').next().is_some_and(|h| {
                        matches!(h, "core::ops::range::Bound" | "std::ops::Bound")
                    }))
                })
        }
        _ => false,
    }
}

/// Trust (UTF8-CORE-RANGE-INDEX-1, 2026-10-05): the NEW range API's own index
/// types — `core::range::{Range, RangeFrom, RangeInclusive, RangeToInclusive}`,
/// stable since 1.95/1.96, and what the plain `a..b`, `a..`, `a..=b` and `..=b`
/// syntax builds under `#![feature(new_range)]`. Each is a `SliceIndex<[T]>` and a
/// `SliceIndex<str>` (`library/core/src/slice/index.rs`,
/// `library/core/src/str/traits.rs`) that panics exactly like its `core::ops`
/// namesake: out of bounds, start past end, and for `str` a non-char-boundary
/// endpoint.
///
/// THE DEFECT, measured on the stage 1 of `dc15b882f6` (main plus wave 16): `&s[
/// core::range::RangeFrom::from(1..)]`, `&v[core::range::Range::from(0..5)]` and
/// their `&String`, `&mut str`, `&Vec`, `&mut Vec`, `&[u8; 3]` and `new_range`
/// twins built rc=0 under the default policy at `-O0` and `-O3`, with one
/// runtime-checked absent-callee row each, and panicked at run time ("start byte
/// index 1 is not a char boundary", "range end index 5 out of range for slice of
/// length 3"). [`range_family_adt_name`] knows only the `core::ops` paths, so
/// [`operand_is_panicking_range`] did not see a range and the `RangeIndex` arm
/// emitted no row.
///
/// SEPARATE FROM [`range_family_adt_name`] on purpose: the iterator-yield and
/// bounded-source lanes share that function, and these types are `IntoIterator`,
/// not `Iterator`, with different field layouts (`RangeInclusive { start, last }`
/// carries no `exhausted` flag). No tracer reads them, so admitting one here
/// sends the `RangeIndex` arm to its untraceable fail-close: an always-violated
/// `SliceBoundsCheck` (and, for a `str`, no char-boundary credit), the row the
/// same index over an untraceable `core::ops` range gets. A GUARDED index over one
/// of these types is therefore refused too: a fail-closed capability loss
/// (docs/DECISION_QUEUE.md, UTF8-CORE-RANGE-1) until a tracer reads their layouts.
///
/// NOT HERE: `core::range::RangeTo` and `core::range::RangeFull` are re-exports of
/// the `core::ops` types, which the extractor prints by their definitional
/// `core::ops::range::` path (measured), so the existing arm sees them; and
/// `RangeFull` never panics. EXACT-PATH gated, generics stripped: a user type
/// named `range::Range`, or a path that merely ends in one of these names, is not
/// matched. `std::range::` is accepted beside `core::range::` for the same reason
/// [`range_family_adt_name`] accepts `std::ops::`; a match can only ADD a row.
pub(super) fn new_range_index_adt_name(name: &str) -> Option<&'static str> {
    if !(name.starts_with("core::range::") || name.starts_with("std::range::")) {
        return None;
    }
    let stripped = vc_strip_generics_cow(name);
    let tail = ["core::range::", "std::range::"]
        .into_iter()
        .find_map(|prefix| stripped.strip_prefix(prefix))?;
    match tail {
        "Range" => Some("Range"),
        "RangeFrom" => Some("RangeFrom"),
        "RangeInclusive" => Some("RangeInclusive"),
        "RangeToInclusive" => Some("RangeToInclusive"),
        _ => None,
    }
}

/// Trust (CONST-RANGE-INDEX-1, 2026-10-06): what a std range-index CALLEE's own
/// instantiation says about its range argument, read from the callee spelling
/// instead of from the argument operand.
///
/// THE DEFECT, measured on the stage 1 of `0ac7a96d9f` (`integ/wave18`): a range
/// that reaches the index as a CONSTANT operand had no type. `const R:
/// core::range::RangeInclusive<usize> = …; &a[R]`, `&s[const { … }]`, `const Q:
/// core::ops::Range<usize> = 0..5; &v[Q]`, and the bodies GVN folds to a constant
/// under `-Copt-level=3 -Zmir-opt-level=2` (`&mut s[0..5]` becomes
/// `<core::range::Range<usize> as SliceIndex<str>>::index_mut(const …, s)`) all
/// reach this arm with the range as `Operand::Constant(OpaqueConst)`.
/// `operand_ty_cow` has no type for it, so [`operand_is_panicking_range`] answered
/// `false`, the arm returned `None` at `range_operand?`, and the index built rc=0
/// under the default and strict policies, then panicked ("range end index 4 out of
/// range for slice of length 3", "start byte index 1 is not a char boundary").
///
/// The callee is rendered from the call's own instantiation
/// (`safe_def_path_str_with_args`), so the range TYPE is written there even when
/// the operand carries none: `<[u8] as core::ops::index::Index<core::range::Range<
/// usize>>>::index` (the trait's argument) or `<core::range::Range<usize> as
/// core::slice::index::SliceIndex<str>>::index_mut` (the Self type). When that type
/// is a panicking range, the argument in its position IS that range, whatever the
/// operand says, and the arm takes it as an untraceable one: the always-violated
/// fail-close (no tracer reads a constant).
///
/// EXACT-PATH gated on the trait (`Index`/`IndexMut`/`SliceIndex` of `core`/`std`)
/// and on the range type ([`range_type_name_is_panicking`]); the method must be
/// `index`/`index_mut`. `RangeFull` is not a panicking range. A match can only ADD
/// a row, so a stamped impersonator can only be refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct CalleeRangeIndex {
    /// The argument position of the range: 1 for `Index::index(self, range)`, 0
    /// for `SliceIndex::index(range, slice)`.
    pub(super) range_arg: usize,
    /// The indexed value is a `str`: the `Index` Self type is `str`, or the
    /// `SliceIndex` argument is `str`. The `::<__trust_str_index>` marker is minted
    /// only for the `Index` form (`apply_str_index_marker` reads the FIRST generic,
    /// which is the range in the `SliceIndex` form), so the inlined `SliceIndex<str>`
    /// call carried no `str` identity at all.
    pub(super) receiver_is_str: bool,
}

/// See [`CalleeRangeIndex`].
pub(super) fn callee_panicking_range_index(callee: &str) -> Option<CalleeRangeIndex> {
    if !callee.starts_with('<') || !matches!(method_tail(callee), "index" | "index_mut") {
        return None;
    }
    let q = super::iterator_yield::ParsedQualifier::parse(callee)?;
    let trait_path = q.trait_path?;
    let self_ty = q.self_ty.trim();
    let open = trait_path.find('<')?;
    let head = trait_path[..open].trim();
    let generic = trait_path[open + 1..].trim_end().strip_suffix('>')?.trim();
    let (range_ty, range_arg, receiver_is_str) = match head {
        "core::ops::index::Index"
        | "core::ops::index::IndexMut"
        | "core::ops::Index"
        | "core::ops::IndexMut"
        | "std::ops::Index"
        | "std::ops::IndexMut" => (generic, 1, self_ty == "str"),
        "core::slice::index::SliceIndex" | "core::slice::SliceIndex" | "std::slice::SliceIndex" => {
            (self_ty, 0, generic == "str")
        }
        _ => return None,
    };
    range_type_name_is_panicking(range_ty)
        .then_some(CalleeRangeIndex { range_arg, receiver_is_str })
}

/// The RENDERED-type twin of [`operand_is_panicking_range`]: `core::ops`'s `Range`,
/// `RangeTo`, `RangeFrom`, `RangeInclusive` and `RangeToInclusive`, the
/// `core::range` index types, and the `(Bound<usize>, Bound<usize>)` pair. Not
/// `RangeFull`, not a reference to a range, not a user type of the same name.
fn range_type_name_is_panicking(range_ty: &str) -> bool {
    let ty = range_ty.trim();
    if let Some(inner) = ty.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        let Some((lhs, rhs)) = split_once_top_level_comma(inner) else {
            return false;
        };
        return [lhs, rhs].into_iter().all(|elem| {
            matches!(
                vc_strip_generics_cow(elem.trim()).as_ref(),
                "core::ops::range::Bound"
                    | "core::ops::Bound"
                    | "std::ops::range::Bound"
                    | "std::ops::Bound"
            )
        });
    }
    matches!(
        range_family_adt_name(ty),
        Some("Range" | "RangeTo" | "RangeFrom" | "RangeInclusive" | "RangeToInclusive")
    ) || new_range_index_adt_name(ty).is_some()
}

/// Split a rendered generic-argument list at its unique depth-0 comma (an arrow's `>`
/// is not a bracket, as in `vc_strip_generics`), without allocating a `Vec`.
fn split_once_top_level_comma(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    let (mut comma_idx, mut depth) = (None, 0i32);
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'<' | b'(' | b'[' => depth += 1,
            b'>' if i > 0 && bytes[i - 1] == b'-' => {}
            b'>' | b')' | b']' => depth -= 1,
            b',' if depth == 0 => {
                if comma_idx.is_some() {
                    return None;
                }
                comma_idx = Some(i);
            }
            _ => {}
        }
    }
    let idx = comma_idx?;
    Some((&s[..idx], &s[idx + 1..]))
}

/// The range argument of a `RangeIndex` call: the first operand whose TYPE is a
/// panicking range ([`operand_is_panicking_range`]), else the operand in the
/// position the callee's instantiation names as one ([`callee_panicking_range_
/// index`]). `None` = not a range index. ONE answer for the arm and for every
/// caller that routes on "is this a range index", so they cannot disagree.
pub(super) fn range_index_range_operand<'a>(
    func: &VerifiableFunction,
    callee: &str,
    args: &'a [Operand],
) -> Option<&'a Operand> {
    args.iter()
        .find(|arg| operand_is_panicking_range(func, arg))
        .or_else(|| args.get(callee_panicking_range_index(callee)?.range_arg))
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
/// Trust (VEC-AS-SLICE, 2026-09-25): an owned std `Vec` TYPE, as the producer
/// actually spells it. Since `dbd23a51b0` the extractor lowers the authenticated
/// `alloc::vec::Vec<T, A>` to `Ty::Seq { elem }` (its `is_std_vec` `DefId` test),
/// never to a `Ty::Adt`, so the NAME test below had not seen a real `Vec` since: the
/// `#7c` owned-`Vec` index row, its fail-honest backstop and the `&Vec` `is_empty`
/// guard all went silent, and only the bundled-member Assert gate stood between
/// `v[i]` and a vacuous proof. `Ty::Seq` is minted for std's `Vec` ALONE, so it is a
/// stronger identity than any name; the name arm stays for the faithful lane, which
/// keeps `Vec`'s physical ADT spelling (`alloc::vec::Vec`, the exact path
/// [`is_owned_slice_container_name`] now requires).
pub(crate) fn ty_is_owned_slice_container(ty: &Ty) -> bool {
    match ty {
        Ty::Seq { .. } => true,
        Ty::Adt { name, .. } => is_owned_slice_container_name(name),
        _ => false,
    }
}

/// True iff the `Ty::Adt` name `name` is std's `Vec` — the only owned deref-to-slice
/// container for which range length-recovery is SOUND. The call-site receiver is
/// `&Vec` and `slice_len_formula` returns `None` (the deref happens inside the `Index`
/// impl), so the length must come from the container's own abstract var. `String` is
/// DELIBERATELY EXCLUDED: a `String` range index `&s[..k]` carries an unmodeled
/// `byte_index_not_char_boundary` panic (e.g. `s="é"` is 2 bytes, so a `k <= s.len()`
/// guard with `k==1` proves the byte bound yet `&s[..1]` still panics) — recovering
/// its byte length would false-PROVE that panic. `VecDeque` is non-contiguous and has
/// no range-`Index` impl, so it never reaches this path. `Vec<T>` range index panics
/// only on OOB / start>end, both modeled — so its length recovery is sound.
///
/// Trust (OWNED-VEC-NAME-1, 2026-10-04): std's `Vec` by its EXACT path
/// ([`super::unwrap_panic::is_std_vec_adt_name`]: `alloc::vec::Vec` /
/// `std::vec::Vec`), never by the last path segment. The old test was
/// `tail == "Vec"`, which every user type named `Vec` passes, and the soundness of
/// each consumer is a fact about std's `Vec` alone: one length for one container,
/// read by `len`/`is_empty` and bounding `Index<usize>`. A user `struct Vec` reaches
/// std's `Vec` methods only through its OWN `Deref`, which need not return the same
/// `Vec` twice. Measured on the stage 1 of `38e6c69b1c` (`scratchpad/stage1-w11fix`):
/// a user `struct Vec` whose `deref` alternates two fields had
/// `if w.is_empty() { return 0; } w.len() - 1` proved and its overflow check elided
/// (default, strict, certify), and `if i < w.len() { w[i] }` read `slice proved`
/// (default, strict); with the struct renamed `Wrap` the same code read
/// `overflow:sub` FAILED and the `slice` row unknown, so the name was the proof. The
/// producer renders every ADT name crate-qualified (`with_resolve_crate_name`) and
/// stamps one whose crate impersonates `alloc`/`std`, so the exact path is std's. The
/// extractor gives a real `Vec` `Ty::Seq` (the arm above), so no real `Vec` is lost.
///
/// The same tail test also granted `value_facts`' `Vec` index/value tie (two `index`
/// calls at one index read one element, a theorem about std's `Index` impl only): a
/// user `Vec` whose safe `Index` returns a different element on each call (a `Cell`
/// flip) made `if v[0] < s.len() { s[v[0]] }` kernel-certified PROVED on the
/// compiler's vcgen entry, and the program panics (`tests/data/user_type_named_vec.rs`,
/// pinned by `opaque_deref_store_reseat::a_user_type_named_vec_gets_no_std_vec_fact`).
pub(crate) fn is_owned_slice_container_name(name: &str) -> bool {
    super::unwrap_panic::is_std_vec_adt_name(name)
}

/// Trust (2026-09-28): `ty` is a std `Vec`. That is either `Ty::Seq`, the extractor's
/// rendering of `Vec<T, A>` (minted only from the `Vec` diagnostic item), or an ADT whose
/// name passes [`is_owned_slice_container_name`] (the faithful lane and older artifacts).
/// Every owned-`Vec` gate asks this. When they matched only the ADT, the `Seq` migration
/// silently blinded all of them: a guarded `v[i]` over `&Vec<u32>` emitted no bounds row,
/// and the bridge's matching gate poisoned the function. Upstream's
/// [`ty_is_owned_slice_container`] is the same predicate (merged 2026-10-14); this
/// name delegates to it so the two can never drift apart.
pub(crate) fn ty_is_owned_vec(ty: &Ty) -> bool {
    ty_is_owned_slice_container(ty)
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
pub(super) fn operand_is_owned_container_receiver(
    func: &VerifiableFunction,
    operand: &Operand,
) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    let ty = crate::local_ty_ref(func, p.local);
    let adt_ty = match ty {
        Some(Ty::Ref { inner, .. }) => Some(inner.as_ref()),
        other => other,
    };
    adt_ty.is_some_and(ty_is_owned_slice_container)
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
    if !(name.contains("HashMap") || name.contains("BTreeMap")) {
        return false;
    }
    let base = name.split('<').next().unwrap_or(name);
    let tail = base.rsplit("::").next().unwrap_or(base).trim();
    matches!(tail, "HashMap" | "BTreeMap")
}

/// True iff `operand` (after peeling one `&`/`&mut`) is a receiver whose type is a
/// panicking std map container — see [`is_panicking_map_container_name`]. Used at
/// the index site to surface `m[&k]` as a visible key-presence obligation rather
/// than the former silent None-skip (a panic-freedom false-accept).
pub(super) fn operand_is_map_container_receiver(
    func: &VerifiableFunction,
    operand: &Operand,
) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    let ty = crate::local_ty_ref(func, p.local);
    let adt_ty = match ty {
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
        && crate::place_ty_cow(func, &base_place)
            .as_deref()
            .is_some_and(ty_is_owned_slice_container)
    {
        return Some((base, guards::coll_len_var_place(func, &base_place)));
    }
    let base_ty = crate::local_ty_ref(func, base);
    let adt_ty = match base_ty {
        Some(Ty::Ref { mutable: false, inner }) if peel_shared_ref => Some(inner.as_ref()),
        // Trust (2026-07-06): a `&mut Vec` receiver (the base-tracer now resolves a
        // `&mut Vec` param through its `&(*v)` reborrow temps) is admitted for scalar-
        // index abstract-length recovery too — its length-stability is enforced by the
        // `local_is_mutably_borrowed` gate below (every resize reborrows `&mut *v`, which
        // trips it → declines). So the common read idiom `if i < v.len() { v[i] }` over a
        // `&mut Vec` recovers `coll_len(v)` on BOTH the guard and the index and PROVES,
        // while `let n=v.len(); v.push(x); v[n]` stays REFUTABLE (the push trips the gate).
        // Trust (VEC-LEN-PARAM-COPY-1, 2026-10-07): "every resize reborrows `&mut *v`"
        // is false on real MIR, which hands the parameter to `push`/`truncate` as
        // `copy _1`. `local_mut_borrows_may_resize` now counts the pointer's own
        // whole-local uses too, so such a push trips the gate (Unknown) rather than
        // relying on the path-definition kill to refute a minted row.
        Some(Ty::Ref { mutable: true, inner }) if peel_shared_ref => Some(inner.as_ref()),
        other => other,
    };
    if !adt_ty.is_some_and(ty_is_owned_slice_container) {
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
    // `_len = X.len()` is a Call (not a Statement::Assign), so `unique_value_def`
    // returns None for it — scan the Call terminators directly, reusing the same
    // std-length matcher (`is_std_inherent_len_call`, Trust 2026-10-03,
    // NAME-ANCHOR-1: it was `method_tail == "len"`, which a user trait method NAMED
    // `len` satisfies) + unique-base trace the tie site keys on. CRUCIAL: the len
    // dest itself must be UNIQUELY whole-local defined (`base_collection_local_unique ==
    // itself`), else a REASSIGNED length carrier — the b7 `let mut end = chars.len();`
    // decremented in a loop — would be misread as a stable `chars.len()`, and the seeded
    // `end == coll_len` tie (versioned at the len call) would NOT hold at the later slice
    // use, false-REFUTEing a safe slice.
    if super::terminator_presence_for(func).has_bare_dest_call
        && let Some(args) =
            crate::find_local_write_term(func, &func.body.blocks, p.local, |_block, term| {
                match term {
                    // Trust (2026-10-06, LEN-KEY-1): or its DefId key (see
                    // `is_std_inherent_len_call_or_key`).
                    Terminator::Call { func: callee, args, dest, callee_key, .. }
                        if dest.local == p.local
                            && dest.projections.is_empty()
                            && is_std_inherent_len_call_or_key(callee, callee_key.as_ref()) =>
                    {
                        Some(args)
                    }
                    _ => None,
                }
            })
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
    // A slice-view length carrier: `Len(place)` / `PtrMetadata(&place)` over the base.
    match crate::local_defs::unique_value_def(func, p.local) {
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
            crate::local_defs::unique_value_def(func, p.local)
        {
            return operand_is_nonneg_const(rhs)
                && operand_within_abstract_len(func, lhs, base, fuel - 1);
        }
        return false;
    }
    if !p.projections.is_empty() {
        return false;
    }
    if let Some(Rvalue::Use(inner)) = crate::local_defs::unique_value_def(func, p.local) {
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

/// The receiver length the `RangeIndex` row bounds its range by: the first argument
/// with a modeled slice length, by its licensed canonical root name
/// (`callee_summaries::param_slice_len`) or else its own (`slice_len_formula`). `None`
/// when no argument has one (an owned `Vec`/`String` receiver, a user type).
///
/// Trust (2026-10-15, TRUST-KI-1015-1): shared with the result-length fact
/// (`range_index_len`), as [`range_bound_at_call_formula`] is.
pub(super) fn range_index_receiver_len(
    func: &VerifiableFunction,
    args: &[Operand],
) -> Option<Formula> {
    args.iter().find_map(|arg| {
        param_slice_len(func, arg, 8).or_else(|| crate::slice_len_formula(func, arg))
    })
}

/// Trust (2026-10-01): the formula of the bound operand `bound` of the range aggregate
/// `range_local` AT the range-indexing call, when that is exactly the value the range
/// was built from: the aggregate is defined by a statement of the very block whose
/// terminator passes `range_local` to a call, no later statement of that block writes
/// the bound's source local, and neither local ever escapes (`&mut`/raw borrows).
/// `None` for a constant or projected bound (each has its own resolution).
fn range_bound_unchanged_until_call(
    func: &VerifiableFunction,
    range_local: usize,
    bound: &Operand,
) -> Option<Formula> {
    if !super::terminator_presence_for(func).has_call {
        return None;
    }
    let (Operand::Copy(b) | Operand::Move(b)) = bound else { return None };
    if !b.projections.is_empty() {
        return None;
    }
    let whole = |op: &Operand, local: usize| matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == local && p.projections.is_empty());
    // The local whose value the bound carries: `b` itself, or the source `k` of a
    // single-assignment temp `b = copy k` (`_7 = copy k; _6 = RangeTo { end: move _7 }`).
    // The VC names the SOURCE: the call block's own `b = copy k` is not one of the
    // definitions the path formula conjoins, while `k`'s version at the call is.
    let source = match crate::local_defs::unique_value_def(func, b.local) {
        Some(Rvalue::Use(Operand::Copy(k) | Operand::Move(k)))
            if k.projections.is_empty()
                && crate::local_defs::is_single_static_assignment(func, b.local) =>
        {
            k.local
        }
        _ => b.local,
    };
    let mut last_checked_block: Option<BlockId> = None;
    let found = crate::any_local_write_stmt(
        func,
        &func.body.blocks,
        range_local,
        |block, _stmt| {
            if last_checked_block == Some(block.id) {
                return false;
            }
            last_checked_block = Some(block.id);
            let Terminator::Call { args, .. } = &block.terminator else { return false };
            if !args.iter().any(|arg| whole(arg, range_local)) {
                return false;
            }
            let Some((def, ops)) = block.stmts.iter().enumerate().find_map(|(at, stmt)| match stmt
            {
                Statement::Assign { place, rvalue: Rvalue::Aggregate(_, ops), .. }
                    if place.local == range_local && place.projections.is_empty() =>
                {
                    Some((at, ops))
                }
                _ => None,
            }) else {
                return false;
            };
            if !ops.iter().any(|op| whole(op, b.local)) {
                return false;
            }
            // Where `source` was read on the way into the aggregate: the aggregate itself,
            // or the temp's `b = copy source`, which must sit earlier in this same block.
            let read_at = if source == b.local {
                Some(def)
            } else {
                block.stmts[..def].iter().position(|stmt| {
                    matches!(stmt, Statement::Assign { place, rvalue: Rvalue::Use(src), .. }
                        if place.local == b.local && place.projections.is_empty() && whole(src, source))
                })
            };
            let Some(read_at) = read_at else { return false };
            // Neither the bound's source after it was read, nor the range itself after it
            // was built (a PARAMETER range reassigned in the body still has its entry value
            // elsewhere, but here the call reads this block's last write), may change
            // before the call.
            let untouched = |local: usize, from: usize| {
                block.stmts[from + 1..].iter().all(|stmt| {
                    matches!(stmt.local_write(local), trust_types::LocalWrite::Untouched)
                })
            };
            // Merge 2026-10-14: nor may the call block write the source BEFORE that read.
            // The VC names `source` at the call, and a write of it in the call block is one
            // of that block's own definitions, which the path formula does not conjoin (the
            // reason the temp is named by its source above). The name was then FREE: a bound
            // read out of memory into a temp of the call block (`_9 = copy (*_7); _8 =
            // RangeTo { end: move _9 }`, the temp being its own source) was refuted on an
            // arbitrary model — `ploss_adv` `pb15_folded_guard_first_ctl` (`_9 > 8` with
            // `_9` free) and the controls `pc02` / `pc06`. Declining hands the bound to the
            // next lane (`range_bound_use::range_bound_at_call` names it by its version at
            // the read, or declines to Unknown); it never makes a refutation a proof.
            let untouched_before = |local: usize, to: usize| {
                block.stmts[..to].iter().all(|stmt| {
                    matches!(stmt.local_write(local), trust_types::LocalWrite::Untouched)
                })
            };
            untouched_before(source, read_at)
                && untouched(source, read_at)
                && untouched(range_local, def)
        },
    );
    if !found {
        return None;
    }
    if crate::any_local_write_stmt(func, &func.body.blocks, source, |_block, stmt| {
        crate::stmt_escapes_local(func, stmt, source)
    }) || (b.local != source
        && crate::any_local_write_stmt(func, &func.body.blocks, b.local, |_block, stmt| {
            crate::stmt_escapes_local(func, stmt, b.local)
        }))
    {
        return None;
    }
    // Review round 34 (2026-10-01): the block above must be THE call being verified,
    // not just some call that reads the range. A `Copy` range reused at a second
    // indexing call after the bound was reassigned matched the FIRST call's block for
    // both rows, and the second row read the new bound: proved, and it panicked. So
    // the range local must be read by exactly ONE terminator and by no statement
    // other than its own aggregate definition; the one call reading it is then the
    // call this row is for.
    let mut seen_terminator_read = false;
    for block in &func.body.blocks {
        if crate::contracts::terminator_mentions_local_anywhere(&block.terminator, range_local) {
            if seen_terminator_read {
                return None;
            }
            seen_terminator_read = true;
        }
        if block.stmts.iter().any(|stmt| {
            let is_own_def = matches!(stmt, Statement::Assign { place, rvalue: Rvalue::Aggregate(..), .. }
                if place.local == range_local && place.projections.is_empty());
            !is_own_def
                && !matches!(stmt, Statement::StorageLive(l) | Statement::StorageDead(l) if *l == range_local)
                && crate::contracts::statement_mentions_local_anywhere(stmt, range_local)
        }) {
            return None;
        }
    }
    if !seen_terminator_read {
        return None;
    }
    Some(crate::place_to_formula(func, &Place::local(source)))
}

/// Trust (2026-10-17, gate RCA precision T5) — the formula of a PROJECTED range bound
/// (`self.buf[self.len..N]`, `self.buf[self.buf_len..]`, `buf[*filled..]`) that is read
/// out of memory IN THE INDEX CALL'S OWN BLOCK: the debug-MIR chain
///
/// ```text
/// r: _20 = copy ((*_1).1)                   // the -O0 bound temp, one assignment
/// a: _19 = Range { start: move _20, end: N } // the range the call receives
///    _17 = index_mut(move _18, move _19)    // the call terminating this block
/// ```
///
/// answered by the place `P` read at `r` (`(*_1).1`), spelled bare: the slice lane
/// renames the violation at the call (`v2_formula_with_slice_len_ties_recorded`), so
/// the name denotes `P`'s value AT THE CALL, exactly as an ordinary read of `P` there
/// would be named.
///
/// Every other resolution declines this shape. `P`'s storage is written elsewhere in
/// the body (`self.len = N` after the copy, `*filled += n` in the loop), so neither the
/// global resolver (no projected write anywhere) nor `range_bound_use` (memory behind a
/// pointer only from a parameter never written through a projection) may name it, and
/// `range_bound_unchanged_until_call` names only a whole LOCAL. The row was the
/// fail-closed `slice-range-bounds-unresolved` Unknown, where the seal (321aaeda75)
/// published the `slice_bounds_check` row PROVED (aterm-core `stack_response.rs:46`,
/// aterm-digest `sha256.rs:150`, astream-aead `stream.rs:468`).
///
/// SOUNDNESS. Everything between the read `r` and the call is a statement of this one
/// block, and the call is the block's terminator, so the value the range holds is `P`'s
/// value at `r`. It is also `P`'s value at the call when no statement of the block
/// before the call writes `P`'s storage or re-points it. Admitted statements are
/// exactly: whole-local assignments to locals that are not `P`'s root, not the root of
/// `P`'s referent fold (`crate::canonical_place`: `*z` with `z = &len` names `len`, a
/// body local an assignment changes), and that do not rewrite the range or the bound
/// temp; and the markers that write nothing (`StorageLive`/`StorageDead`, `Retag`,
/// `PlaceMention`, `Coverage`, `ConstEvalCounter`, `Nop`). A store through any
/// projection, a discriminant write, `Deinit`, an intrinsic, `copy_nonoverlapping` or an
/// unsupported statement anywhere in the block declines, so neither a direct store nor a
/// store through an aliasing pointer can sit between the read and the call (the H1
/// STALE-BOUND-CALL-RENAME and LAUNDERED-ALIAS-STORE shapes write the pointee between
/// the range and the call, which here would be such a statement or a second block).
/// `P` has only `Deref` and `Field` projections, before and after the fold, so it names
/// one storage location whichever index local the body changes. With the value at the
/// call equal to the bound, the violation stated on the name at the call is the
/// violation of the range the call receives; whether that name is modelled faithfully at
/// the call is the encoding's ordinary question for any read of `P` at the call.
///
/// PRECISION, not soundness: the name is handed back only when `P`'s version token at
/// the call is its token at the block's ENTRY, i.e. the oracle versions no definition of
/// `P` inside the call block. A definition there (an in-block havoc) is not one of the
/// definitions the slice lane conjoins (it conjoins only the block's length ties), so
/// the name would be free and the row refuted on an arbitrary model, the class-10 shape
/// the merge of 2026-10-14 declined in `range_bound_unchanged_until_call`.
fn projected_bound_read_in_call_block(
    func: &VerifiableFunction,
    range_operand: &Operand,
    bound: &Operand,
    call_block: &trust_types::BasicBlock,
) -> Option<Formula> {
    use trust_types::Projection;
    let (Operand::Copy(range) | Operand::Move(range)) = range_operand else { return None };
    let (Operand::Copy(b) | Operand::Move(b)) = bound else { return None };
    if !range.projections.is_empty() || !b.projections.is_empty() {
        return None;
    }
    let whole = |op: &Operand, local: usize| matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == local && p.projections.is_empty());
    let Terminator::Call { args, .. } = &call_block.terminator else { return None };
    if !args.iter().any(|arg| whole(arg, range.local)) {
        return None;
    }
    // `a`: the aggregate that builds the range from THIS bound operand (by identity).
    let agg_at = call_block.stmts.iter().position(|stmt| {
        matches!(stmt, Statement::Assign { place, rvalue: Rvalue::Aggregate(_, ops), .. }
            if place.local == range.local
                && place.projections.is_empty()
                && ops.iter().any(|op| std::ptr::eq(op, bound)))
    })?;
    // `r`: the bound temp's one assignment, `b = copy P`, earlier in this block.
    let read_at = call_block.stmts[..agg_at].iter().position(|stmt| {
        matches!(stmt, Statement::Assign { place, .. }
            if place.local == b.local && place.projections.is_empty())
    })?;
    let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)), .. } =
        &call_block.stmts[read_at]
    else {
        return None;
    };
    let deref_or_field = |p: &Place| {
        !p.projections.is_empty()
            && p.projections.iter().all(|q| matches!(q, Projection::Deref | Projection::Field(_)))
    };
    if !deref_or_field(src) {
        return None;
    }
    for (at, stmt) in call_block.stmts.iter().enumerate() {
        match stmt {
            Statement::Assign { place, .. } => {
                let rewrites_chain = (place.local == range.local && at != agg_at)
                    || (place.local == b.local && at != read_at);
                if !place.projections.is_empty()
                    || place.local == src.local
                    || rewrites_chain
                {
                    return None;
                }
            }
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Retag { .. }
            | Statement::PlaceMention(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => {}
            _ => return None,
        }
    }
    if !crate::local_defs::is_single_static_assignment(func, b.local) {
        return None;
    }
    let canonical = crate::canonical_place(func, src);
    if !canonical
        .projections
        .iter()
        .all(|q| matches!(q, Projection::Deref | Projection::Field(_)))
    {
        return None;
    }
    if canonical.local != src.local
        && call_block.stmts.iter().any(|stmt| {
            matches!(stmt, Statement::Assign { place, .. } if place.local == canonical.local)
        })
    {
        return None;
    }
    let name = crate::place_to_var_name(func, src);
    let sort = crate::place_sort(func, src).unwrap_or(Sort::Int);
    let sv = super::stmt_versions_for(func);
    let at_entry = sv.version_token_at(func, call_block.id, 0, &name);
    let at_call = sv.version_token_at(func, call_block.id, call_block.stmts.len(), &name);
    (at_entry == at_call).then(|| Formula::var_owned(name, sort))
}

/// Trust: 2026-10-14 (follow-up of dd584167118) — THE formula a range bound takes in
/// an obligation stated AT THE CALL that receives the range: `bound` is an operand of
/// the range `range_operand` passed to the call terminating `call_block`, and the
/// answer names the value that bound has at that call. Every lane that states a range
/// bound at its call asks this and nothing else: the slice range-index lane (its
/// violation, the `char_indices` / `find` endpoint facts conjoined onto it, the
/// `is_char_boundary` axiom, and its `a..=b` / `(Bound, Bound)` fallback),
/// `BTreeMap`/`BTreeSet::range`, and `VecDeque::range`/`range_mut`. It is one function
/// so that the lanes cannot diverge again: dd584167118 moved the slice violation off
/// the joined-copy fallback and left the facts conjoined onto that same violation, the
/// char-boundary axiom and the BTree lane on it.
///
/// Three resolutions, in order. Each is sound on its own; the order only decides
/// precision:
///  1. [`super::iterator_yield::resolve_range_bound_formula_exact`]: a constant, or a
///     name of ONE value (a single-assignment local, a licensed slice length);
///  2. [`range_bound_unchanged_until_call`]: the bound's source named at the call, when
///     the range is built in the call's own block and nothing writes the source
///     between the read and the call;
///  2b. [`projected_bound_read_in_call_block`] (2026-10-17): a PROJECTED source
///     (`(*self).len`, `*filled`) read into the bound temp in the call's own block,
///     named at the call when no statement of that block writes memory or re-points it;
///  3. [`super::range_bound_use::range_bound_at_call`]: the source named by its SSA
///     version at the statement that read it into the range, when that IS its value at
///     the call (`same_value_at_call`).
///
/// Anything else is `None`, and every caller turns `None` into its shared fail-closed
/// `UnsupportedMir` row: Unknown, never proved, never refuted on an arbitrary model.
///
/// NOT ASKED: the joined-copy fallback of
/// [`super::iterator_yield::resolve_range_bound_formula`], which resolves a copy of a
/// multiply-written local (`_t = copy k`) to the copy's own bare name. That name is one
/// value, and a fact keyed on a payload may use it (the yield lanes do: a hypothesis on
/// a free name is only weaker). An obligation stated at the call meets the copy's value
/// only through the copy's definition `_t == k#<token at the copy>`, and that reaches
/// the row only where the copy's block is conjoined: the CALL block's own definitions in
/// the BTree / VecDeque lanes, or the dominating path definitions; never the slice
/// lane's own call block (it conjoins only length ties), and not a copy made in a loop
/// body ahead of a write of `k`. Where it does not reach, `_t` is a FREE variable of the
/// row, which is then refuted on an arbitrary model (class 10). Measured before this
/// change (`tests/range_bound_joined_copy_realmir.rs`): the correct `if k >= 8 { return
/// } b[..=k]` was refuted at `_10 = 8` (`sl_inclusive_ctl`), and the loop probes
/// `bt_joined_after_bug` / `bt_stale_guard_bug` at the impossible `usize` value `_15 =
/// -1`. Where it does reach, its token names a reaching-definition SET, not a value: a
/// guard after a conditional write of `k` can share the copy's token while reading
/// another value, the false-PROVE shape `range_bound_use::same_value_at_call` refuses
/// (`joined_after_bug`). The path definitions withheld the copy's definition in every
/// such probe (none PROVED); this resolution does not depend on that.
pub(super) fn range_bound_at_call_formula(
    func: &VerifiableFunction,
    range_operand: &Operand,
    bound: &Operand,
    call_block: &trust_types::BasicBlock,
) -> Option<Formula> {
    super::iterator_yield::resolve_range_bound_formula_exact(func, bound, 8)
        .or_else(|| {
            let (Operand::Copy(range) | Operand::Move(range)) = range_operand else {
                return None;
            };
            if !range.projections.is_empty() {
                return None;
            }
            range_bound_unchanged_until_call(func, range.local, bound)
        })
        .or_else(|| projected_bound_read_in_call_block(func, range_operand, bound, call_block))
        .or_else(|| {
            super::range_bound_use::range_bound_at_call(func, range_operand, bound, call_block)
        })
}

/// Trust (2026-10-02, class 10 — false refutation): the `UnsupportedMir` kinds the
/// slice range-index arm declines to when the obligation cannot be STATED. A bound or
/// a receiver length that does not resolve is a coverage gap, not a violation; the
/// arm used to emit the always-violated `Bool(true)` as a REFUTABLE
/// `SliceBoundsCheck` there, which FAILED with an arbitrary model on correct code.
pub(super) const RANGE_INDEX_BOUNDS_UNRESOLVED: &str = "slice-range-bounds-unresolved";
/// See [`RANGE_INDEX_BOUNDS_UNRESOLVED`].
pub(super) const RANGE_INDEX_LEN_UNRESOLVED: &str = "slice-range-len-unresolved";

/// The declined row: the shared fail-closed formula
/// (`unsupported::unsupported_mir_fail_closed_formula`, SAT, so no consumer reads it
/// as discharged) under `VcKind::UnsupportedMir` (Unknown — never proved, never
/// refuted, never dispatched).
fn range_index_declined(kind: &str, detail: &str) -> Option<(Formula, VcKind)> {
    Some((
        super::unsupported::unsupported_mir_fail_closed_formula(),
        VcKind::UnsupportedMir { kind: kind.into(), detail: detail.into() },
    ))
}

pub(super) fn slice_method_panic_body(
    func: &VerifiableFunction,
    panic: &SliceMethodPanic,
    // Trust (CONST-RANGE-INDEX-1, 2026-10-06): the rendered callee. The
    // `RangeIndex` arm reads the range TYPE from its instantiation when the range
    // operand carries none (a constant); see `callee_panicking_range_index`.
    callee: &str,
    args: &[Operand],
    // Trust (str char-boundary soundness): true iff the receiver is a `str`
    // (the `::<__trust_str_index>` marker from `func_operand_name`). A str
    // range-index carries an UNMODELED UTF-8 char-boundary panic on top of the
    // byte-bounds check, so the RangeIndex arm fails closed unless every endpoint
    // is provably a char boundary. `[u8]`/`[T]` slices pass `false` and are
    // byte-identical to before.
    receiver_is_str: bool,
    // Trust (2026-10-02, class 10): the block whose `Call` terminator this is. When the
    // global resolver declines a multiply-assigned bound, the RangeIndex arm locates the
    // statement that read it INTO the range this call receives and names it by its
    // version there (`range_bound_use::range_bound_at_call`).
    call_block: &trust_types::BasicBlock,
) -> Option<(Formula, VcKind)> {
    // The receiver slice is arg 0; its modeled `__slice_len` (or a constant array
    // length) is the bound. `slice_len_formula` returns `None` for anything whose
    // length Trust does not model (non-slice receivers), so a `swap` on a tuple or
    // a method on an unmodeled type yields no obligation.
    let receiver = args.first()?;
    match panic {
        SliceMethodPanic::SplitAt { mid_idx } => {
            let mid = args.get(*mid_idx)?;
            // W4 round 3 (2026-09-29): a `str` receiver ALSO panics on a `mid` that
            // is not a char boundary — see `str_split_at_panic_body`.
            if receiver_is_str {
                return str_split_at_panic_body(func, receiver, mid);
            }
            let len = crate::slice_len_formula(func, receiver)?;
            // `mid` is a `usize` (>= 0 by type), so the only failure of a `[T]`
            // split is `mid > len`.
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
            // Trust (2026-10-09, sweep c05): the one case with no stale tie: this is
            // the SOLE resize of a `&mut Vec` parameter, and nothing that uses the
            // vector is reachable after it (`value_facts::vec_sole_mutator_block`).
            // Every length read happened before it, so `coll_len(v)` is the length
            // the call sees, and the real precondition is checked.
            if let Some(Operand::Copy(p) | Operand::Move(p)) = Some(receiver)
                && p.projections.is_empty()
                && let Some(base) = (if crate::local_defs::is_parameter(func, p.local) {
                    Some(Place::local(p.local))
                } else {
                    crate::guards::base_collection_place_unique(func, p.local)
                })
                && base.projections.is_empty()
                && super::value_facts::vec_sole_mutator_block(func, base.local).is_some()
                && let Some(index) = args.get(*index_idx)
            {
                let len = crate::guards::coll_len_var(func, base.local);
                let idx = crate::operand_to_formula(func, index);
                let violation = if *insert {
                    Formula::Gt(Box::new(idx), Box::new(len))
                } else {
                    Formula::Ge(Box::new(idx), Box::new(len))
                };
                return Some((violation, VcKind::SliceBoundsCheck));
            }
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
            // Trust (CONST-RANGE-INDEX-1, 2026-10-06): the range argument is the
            // first operand TYPED as a panicking range, or else the operand in the
            // position the callee's instantiation names as one — a constant range
            // (`const R: Range<usize>`, `const { .. }`, a GVN-folded aggregate) has
            // no operand type, and the arm used to return `None` below for it. A
            // range found only through the callee is never traced (no tracer reads
            // a constant), so it takes the untraceable-range fail-close.
            let range_operand: Option<&Operand> = range_index_range_operand(func, callee, args);
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
            // Trust (2026-09-25, std-range-family): `deque[i]` / `deque[i] = x` — the
            // `VecDeque` `Index<usize>` impl panics ("Out of bounds access") at
            // `i >= len`. The owned-`Vec` recovery below never matches a deque, so
            // the index emitted no row and built rc=0. See `collection_range`.
            if range_operand.is_none()
                && let Some(row) = super::collection_range::deque_scalar_index_body(func, args)
            {
                return Some(row);
            }
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
            // Trust (2026-10-15, TRUST-KI-1015-1): the shared `range_index_receiver_len`
            // (the first argument with a length, as before), which the result-length
            // fact reads too. Deferred until after `range_operand?` so scalar `Vec[i]`,
            // `VecDeque[i]`, `HashMap[&k]`, and `RangeFull` calls skip slice-length tracing.
            let len = range_index_receiver_len(func, args);
            // The `SliceIndex<str>` form (an inlined `str` index, range first)
            // carries no `::<__trust_str_index>` marker; its instantiation says
            // `str`, so the char-boundary fail-close below applies to it too.
            let receiver_is_str = receiver_is_str
                || callee_panicking_range_index(callee).is_some_and(|c| c.receiver_is_str);
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
                        //
                        // The formula is the SHARED fail-closed one (`Bool(true)`, SAT)
                        // — the SAME polarity every other `UnsupportedMir` emitter in
                        // this tree uses, and for the reason
                        // `unsupported::unsupported_mir_fail_closed_formula` states: a
                        // VC is a VIOLATION formula, so an UNSAT one reads as "no
                        // violation". This site was the only emitter deviating, with
                        // `Formula::Bool(false)`, and `UnsupportedMir::proof_level()`
                        // is `L0Safety` — so every consumer that selects rows by PROOF
                        // LEVEL instead of by kind read this DECLINED row as
                        // DISCHARGED. Two shipped fixtures pin it:
                        // `trust-clean/tests/unsupported_row_polarity_gate.rs` requires
                        // this row's formula to be SAT and its fixture (which panics at
                        // `end > v.len()`) not to certify, and
                        // `trust-clean/fixtures/decline-handling-2026-08-25` carries the
                        // same body, which reached `ProofStatus::Certified` /
                        // `is_assumable` while the polarity was inverted.
                        Some(_) => {
                            return Some((
                                super::unsupported::unsupported_mir_fail_closed_formula(),
                                VcKind::UnsupportedMir {
                                    kind: "SliceBoundsCheck".to_string(),
                                    detail: "slice length is a non-derivable owned-Vec \
                                             abstract placeholder; fail-honest to Unknown \
                                             rather than false-REFUTE a provably-safe slice"
                                        .to_string(),
                                },
                            ));
                        }
                        // A None soft-len: no length is modeled for this receiver at all (an
                        // ambiguous conditional-merge base, a user `Index<Range<usize>>`
                        // ADT).
                        //
                        // Trust (2026-10-02, class 10 — false refutation): this arm was the
                        // always-violated `Bool(true)` as a REFUTABLE `SliceBoundsCheck`
                        // ("so real OOBs are still caught"). A length that does not resolve
                        // is a COVERAGE GAP, not a violation: the row FAILED with an
                        // arbitrary model on every correct program that reaches it, and a
                        // real OOB was "caught" by the same arbitrary model, not by a
                        // witness. Declined to `UnsupportedMir` (Unknown, never proved) like
                        // the soft-len arm above.
                        None => {
                            return range_index_declined(
                                RANGE_INDEX_LEN_UNRESOLVED,
                                "slice range index whose receiver length is not modeled at \
                                 the call (no slice length, no recoverable owned-container \
                                 length) — the bounds cannot be established; reported \
                                 Unknown, never refuted on an arbitrary model and never \
                                 silently verified",
                            );
                        }
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
            let charindices_roots: std::cell::OnceCell<FxHashSet<usize>> =
                std::cell::OnceCell::new();
            let get_charindices_roots = || -> &FxHashSet<usize> {
                charindices_roots.get_or_init(|| {
                    args.iter()
                        .filter(|a| !operand_is_panicking_range(func, a))
                        .filter_map(|a| charindices_shared_slice_root(func, a))
                        .collect()
                })
            };
            let bound_is_yield = |op: &Operand| {
                !matches!(op, Operand::Constant(_))
                    && operand_is_charindices_yield_of(func, op, get_charindices_roots())
            };
            let bound_is_zero =
                |op: &Operand| matches!(op, Operand::Constant(ConstValue::Uint(0, _)));
            // Resolve each bound with `resolve_range_bound_formula` (NOT plain
            // `operand_to_formula`): it traces the `Range { start: _t, .. }` field
            // operand through its `_t = a` Use-copy to the underlying param symbol
            // and canonicalizes a `PtrMetadata`/`Len` bound to the same
            // `slice_len_formula` term — so a `b <= s.len()` guard discharges the
            // `b > len` violation (exactly how the range-iterator yield facts connect).
            //
            // Trust: 2026-09-16 (round A5) — a bound whose root local is not
            // single-valued no longer resolves GLOBALLY to its bare name: never a
            // bare-name spelling the version rename could bind to a value the range
            // was not built from.
            //
            // Trust (2026-10-01, ordsweep2 strings/c15): such a bound is still exact AT
            // THIS CALL when the range aggregate is built in the call's own block, no
            // later statement of that block writes the bound local, and the local
            // never escapes (`range_bound_unchanged_until_call`): the VC is read at the
            // call, where the version rename binds the bare name to the version
            // current there, which is the one the range was built from.
            //
            // Trust: 2026-10-02 (class 10 — false refutation) — otherwise it is named by
            // its SSA VERSION AT THE STATEMENT THAT READ IT INTO THE RANGE
            // (`range_bound_use`): `len#<token there>`, which the call-point rename
            // leaves alone. Never the bare name renamed at the call (the seal's
            // answer): a write and a guard between the range's construction and the
            // call then discharge a violation about a value the range does not hold
            // (`stale_guard_bug`, proved and certified on the seal, panics). `while
            // len > 8 { len -= 1 } out[..len]` and the early-return `if size + len >
            // 23 { return } buf[len..]` (smol_str) prove again on it; they had FAILED
            // on an arbitrary model.
            //
            // Trust: 2026-10-10 (review round 110) — the joined-copy fallback (a copy of
            // a multiply-written local resolving to its own bare name,
            // `resolve_range_bound_formula`) is NOT asked here: the copy is connected to
            // its value only where its block's defs are conjoined, and the call block's
            // are not (`_7 = copy k; &b[..k]` was refuted with `_7` free). The exact
            // resolution (`resolve_range_bound_formula_exact`) is.
            //
            // Merge 2026-10-14: the local lanes (exact, unchanged-until-call) and
            // upstream's SSA-at-read lane are tried in that order; each is independently
            // sound, so the order only decides precision. The soundness line asked the
            // joined-copy fallback last, where the only alternative was the
            // always-violated `Bool(true)`; against upstream's DECLINE (class 10) it
            // turned an unresolved bound into a refutable row on a copy temp the call
            // does not connect to any value — `clip_escaped` (`bump(&mut len);
            // buf[..len]`) was REFUTED on `_8 = 9` with `n = 0`, and the stale-guard and
            // joined probes on a free `_5` / `_7` / `_14`: the arbitrary-model FAILED
            // class 10 removed. Had the copy's own def (`_14 == len#<token at the
            // read>`) reached the call, it would be upstream's shared-token false-PROVE
            // shape (`joined_after_bug`: a guard after `if c { len = n }` shares that
            // token); on the merged tree it did not (each probe FAILED, none PROVED).
            // Such a bound now declines (`tests/slice_range_bound_at_call.rs`).
            //
            // Trust: 2026-10-14 — those three lanes are `range_bound_at_call_formula`,
            // shared with every other obligation that states a range bound at its call
            // (the BTree and VecDeque range lanes). The facts conjoined onto this
            // violation (the `char_indices` / `find` endpoint facts below) and the
            // `is_char_boundary` axiom state the bound through the SAME resolution. They
            // asked the joined-copy fallback after dd584167118, so a tested endpoint `e
            // = n` with `n` multiply written got its axiom on the copy `e` while the
            // violation read `n#<token>`, and the two met only through `e`'s path
            // definition (`cb_join_tested_ctl` proved on it); they now name one term.
            let resolve_bound = |op: &Operand| -> Option<Formula> {
                range_bound_at_call_formula(func, range_operand, op, call_block)
            };
            let yield_facts = |x: &Formula, len: &Formula| -> Vec<Formula> {
                vec![
                    Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(0))),
                    Formula::Le(
                        Box::new(x.clone()),
                        Box::new(Formula::Sub(Box::new(len.clone()), Box::new(Formula::Int(1)))),
                    ),
                ]
            };
            // W4 STR-OFFSET (2026-09-25): a bound that IS the offset of an
            // authenticated `str::find`/`rfind` match over the SAME root string —
            // the match start `i`, or the match end `i + K` with `K` the constant
            // exact match length — is a char boundary by `core::str`'s contract,
            // and `i + m <= len`. Credited exactly like a CharIndices yield:
            // structurally for the boundary, VC-locally for the bounds, and only
            // when EVERY explicit endpoint is boundary-safe. See `str_offset`.
            let search_facts =
                |op: &Operand, resolved: &Formula, len: &Formula| -> Option<Vec<Formula>> {
                    if matches!(op, Operand::Constant(_)) {
                        return None;
                    }
                    str_search_endpoint_facts(func, op, get_charindices_roots(), resolved, len)
                };
            let endpoint_yield_or_search_facts =
                |op: &Operand, resolved: &Formula, len: &Formula| -> Option<Vec<Formula>> {
                    if bound_is_zero(op) {
                        Some(Vec::new())
                    } else if bound_is_yield(op) {
                        Some(yield_facts(resolved, len))
                    } else {
                        search_facts(op, resolved, len)
                    }
                };
            let traced = range_local.and_then(|l| trace_local_to_range_family(func, l, 8));
            // A bound that resolves NO way is a coverage gap, not a violation:
            // the row is the shared fail-closed `UnsupportedMir` (Unknown — never
            // proved, never dispatched), exactly as the soft-length arm above. It was
            // the always-violated `Bool(true)` as a REFUTABLE `SliceBoundsCheck`,
            // which FAILED with an arbitrary model on correct code (class 10).
            let range_bounds_unresolved = || {
                range_index_declined(
                    RANGE_INDEX_BOUNDS_UNRESOLVED,
                    "slice range index whose bound does not resolve to a single value at \
                     the call (a multiply-written local changed between the range's \
                     construction and the call, an escaped or projected bound, or a \
                     range the tracer cannot read) — reported Unknown, never refuted on \
                     an arbitrary model and never silently verified",
                )
            };
            enum ResolvedRangeBounds<'a> {
                Exclusive {
                    start: &'a Operand,
                    start_f: Formula,
                    start_credited: bool,
                    end: &'a Operand,
                    end_f: Formula,
                    end_credited: Option<bool>,
                },
                To {
                    end: &'a Operand,
                    end_f: Formula,
                    end_credited: bool,
                },
                From {
                    start: &'a Operand,
                    start_f: Formula,
                    start_credited: bool,
                },
                Untraced,
            }
            let (violation, resolved_bounds) = match traced {
                Some(RangeFamilyOperands::Exclusive(start, end)) => {
                    let (Some(s), Some(e)) = (resolve_bound(start), resolve_bound(end)) else {
                        return range_bounds_unresolved();
                    };
                    let base = Formula::Or(vec![
                        Formula::Gt(Box::new(s.clone()), Box::new(e.clone())),
                        Formula::Gt(Box::new(e.clone()), Box::new(len.clone())),
                    ]);
                    let start_facts = endpoint_yield_or_search_facts(start, &s, &len);
                    let start_credited = start_facts.is_some();
                    let mut end_credited = None;
                    let violation = if let Some(mut sf) = start_facts
                        && let Some(ef) = {
                            let ef = endpoint_yield_or_search_facts(end, &e, &len);
                            end_credited = Some(ef.is_some());
                            ef
                        }
                    {
                        sf.extend(ef);
                        if sf.is_empty() {
                            base
                        } else {
                            sf.push(base);
                            Formula::And(sf)
                        }
                    } else {
                        base
                    };
                    (
                        violation,
                        ResolvedRangeBounds::Exclusive {
                            start,
                            start_f: s,
                            start_credited,
                            end,
                            end_f: e,
                            end_credited,
                        },
                    )
                }
                Some(RangeFamilyOperands::To(end)) => {
                    // `&s[..i]` at a yielded `i`: `i <= len - 1` refutes `i > len`;
                    // start 0 is always a boundary — panic-free by the contract.
                    let Some(e) = resolve_bound(end) else { return range_bounds_unresolved() };
                    let base = Formula::Gt(Box::new(e.clone()), Box::new(len.clone()));
                    let end_facts = endpoint_yield_or_search_facts(end, &e, &len);
                    let end_credited = end_facts.is_some();
                    let violation = if let Some(mut conjuncts) = end_facts
                        && !conjuncts.is_empty()
                    {
                        conjuncts.push(base);
                        Formula::And(conjuncts)
                    } else {
                        base
                    };
                    (violation, ResolvedRangeBounds::To { end, end_f: e, end_credited })
                }
                Some(RangeFamilyOperands::From(start)) => {
                    // `&s[i..]` at a yielded `i`: `i <= len - 1` refutes `i > len`;
                    // the implicit end `len` is trivially valid — panic-free (the
                    // heck `capitalize` idiom).
                    let Some(s) = resolve_bound(start) else { return range_bounds_unresolved() };
                    let base = Formula::Gt(Box::new(s.clone()), Box::new(len.clone()));
                    let start_facts = endpoint_yield_or_search_facts(start, &s, &len);
                    let start_credited = start_facts.is_some();
                    let violation = if let Some(mut conjuncts) = start_facts
                        && !conjuncts.is_empty()
                    {
                        conjuncts.push(base);
                        Formula::And(conjuncts)
                    } else {
                        base
                    };
                    (violation, ResolvedRangeBounds::From { start, start_f: s, start_credited })
                }
                // `range_operand` is CONFIRMED a panicking range
                // (`operand_is_panicking_range`), but its aggregate could not be
                // traced to bounds — a `RangeInclusive` (the `+1` is not modeled),
                // a by-param `Range<usize>`, or a cross-block construction. A missing
                // bound is a MISSING OOB obligation, so it must never be a silent
                // skip; it is the declined `UnsupportedMir` row (Trust 2026-10-02,
                // class 10: it was the always-violated `Bool(true)` as a refutable
                // `SliceBoundsCheck`). (`RangeFull` is excluded by
                // `operand_is_panicking_range`, so a genuinely-total `s[..]` never
                // reaches here.)
                //
                // Trust (2026-09-25, std-range-family): the shapes the tracer above
                // does not read — `a..=b`, `..=b`, `(Bound, Bound)` — get the exact
                // `slice::range` condition when their bounds resolve
                // (`collection_range::index_range_violation`); anything else is the
                // declined row.
                //
                // Trust (UTF8-CORE-RANGE-INDEX-1, 2026-10-05): a `core::range::*`
                // index (`new_range_index_adt_name`) always lands here: neither tracer
                // reads the new layouts. It was the always-violated fail-close (a
                // refuted `SliceBoundsCheck`); since the class-10 merge it is the same
                // declined row as every other untraceable range (RANGE-DECLINE): still
                // charged, never proved, an Unknown that the strict policy counts as
                // fatal (`strict_l0_verification_failure`), and no longer refuted on an
                // all-zero model (`tests/core_range_index_realmir.rs`).
                //
                // Trust: 2026-10-14 — its bounds are read through `resolve_bound`, as the
                // traced shapes' are; they asked the joined-copy fallback, which named
                // the free `_10` of `_10 = copy k; RangeToInclusive { end: move _10 }`.
                None => {
                    match super::collection_range::index_range_violation(
                        func,
                        range_operand,
                        &len,
                        &resolve_bound,
                    ) {
                        Some(violation) => (violation, ResolvedRangeBounds::Untraced),
                        None => return range_bounds_unresolved(),
                    }
                }
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
            // disjunct provable), a `str::find`/`rfind` `Some` payload (a match
            // start; its bounds half is a global fact, 2026-09-29) or the constant
            // 0. The implicit endpoints are
            // boundaries by construction — `..e` starts at 0, `s..` ends at `len`
            // (a string's byte length is always a boundary) — so only the EXPLICIT
            // endpoint(s) are checked. `[u8]`/`[T]` slices (`receiver_is_str ==
            // false`) are untouched: they carry no char-boundary panic. A str slice
            // at a non-yield computed offset is refused (a genuinely boundary-safe
            // computed offset that is not a traced yield is conservatively
            // rejected), never a false PROVE.
            //
            // Trust (2026-10-02, class 10 — false refutation): refused as the
            // declined `UnsupportedMir` row, the same row `str_split_at_panic_body`
            // gives the same unmodeled char boundary. It was the always-violated
            // `Bool(true)` as a REFUTABLE `SliceBoundsCheck`: a correct `&s[i..]` at
            // a boundary-safe offset this lane cannot credit FAILED with an
            // arbitrary model.
            let violation = if receiver_is_str {
                // Trust (2026-09-29): an endpoint that is not boundary-safe by
                // construction may still have been TESTED: `if s.is_char_boundary(n) {
                // &s[..n] }`. The test's result `b` is exactly "`n` is a boundary of
                // `s`", which also makes `n <= len`. So a tested endpoint contributes
                // the condition `b` and the axiom `b -> n <= len`, and the violation
                // becomes `axioms && (!b || bounds)` — refuted only on a path where the
                // test held (`char_boundary_tests_of`).
                let endpoint_condition = |op: &Operand,
                                          resolved: Formula,
                                          credited: Option<bool>|
                 -> Option<Option<(Formula, Formula)>> {
                    let is_credited = credited.unwrap_or_else(|| {
                        endpoint_yield_or_search_facts(op, &resolved, &len).is_some()
                    });
                    if is_credited || operand_is_str_find_payload_of(func, op, get_charindices_roots())
                    {
                        return Some(None);
                    }
                    let tested = char_boundary_tests_of(func, op, get_charindices_roots())?;
                    let at_most_len = Formula::Le(Box::new(resolved), Box::new(len.clone()));
                    let axiom =
                        Formula::Or(vec![Formula::Not(Box::new(tested.clone())), at_most_len]);
                    Some(Some((tested, axiom)))
                };
                let tested: Option<Vec<(Formula, Formula)>> = match resolved_bounds {
                    ResolvedRangeBounds::Exclusive {
                        start,
                        start_f,
                        start_credited,
                        end,
                        end_f,
                        end_credited,
                    } => (|| {
                        let start_cond =
                            endpoint_condition(start, start_f, Some(start_credited))?;
                        let end_cond = endpoint_condition(end, end_f, end_credited)?;
                        let mut out = Vec::with_capacity(
                            usize::from(start_cond.is_some()) + usize::from(end_cond.is_some()),
                        );
                        if let Some(c) = start_cond {
                            out.push(c);
                        }
                        if let Some(c) = end_cond {
                            out.push(c);
                        }
                        Some(out)
                    })(),
                    ResolvedRangeBounds::To { end, end_f, end_credited } => {
                        endpoint_condition(end, end_f, Some(end_credited))
                            .map(|c| c.into_iter().collect())
                    }
                    ResolvedRangeBounds::From { start, start_f, start_credited } => {
                        endpoint_condition(start, start_f, Some(start_credited))
                            .map(|c| c.into_iter().collect())
                    }
                    // A range the tracer cannot read (`a..=b`): no endpoint is credited.
                    ResolvedRangeBounds::Untraced => None,
                };
                match tested {
                    Some(tested) if tested.is_empty() => violation,
                    Some(tested) => {
                        let (conditions, mut conjuncts): (Vec<_>, Vec<_>) =
                            tested.into_iter().unzip();
                        conjuncts.push(Formula::Or(vec![
                            Formula::Not(Box::new(Formula::And(conditions))),
                            violation,
                        ]));
                        Formula::And(conjuncts)
                    }
                    None => {
                        return range_index_declined(
                            "str-range-char-boundary-unmodeled",
                            "str range index panics when an endpoint is not a UTF-8 char \
                             boundary; char boundaries are not modeled, and an explicit \
                             endpoint is not a boundary this verifier can establish by \
                             structure (the constant 0, a `char_indices` offset, a \
                             `find`/`rfind` match start or exact match end, or a tested \
                             `is_char_boundary`) — reported Unknown, never silently \
                             verified",
                        );
                    }
                }
            } else {
                violation
            };
            Some((violation, VcKind::SliceBoundsCheck))
        }
        SliceMethodPanic::BTreeRange { range_idx } => {
            btree_range_panic_body(func, args.get(*range_idx)?, call_block)
        }
        SliceMethodPanic::CollectionRange { .. }
        | SliceMethodPanic::ResizingIndexArg { .. }
        | SliceMethodPanic::CharBoundaryArg { .. }
        | SliceMethodPanic::SliceRepeat { .. }
        | SliceMethodPanic::DequeSwap { .. }
        | SliceMethodPanic::ConstChunkSize { .. }
        | SliceMethodPanic::VecIntoFlattened => {
            super::collection_range::collection_method_panic_body(func, panic, args, call_block)
        }
    }
}

/// W4 round 3 (2026-09-29): is this `split_at`/`split_at_mut` call the `str`
/// method? `str` is extracted as `[u8]`, so the receiver's type cannot tell a
/// `str` split from a `[u8]` split; the callee can. The DefId key
/// (`SysrootItem::StrSplitAt`/`StrSplitAtMut`) is the identity. A call whose key
/// is absent (a producer that mints none) but whose rendered path is the
/// `core::str` inherent is ALSO answered `true`: a `true` here can only ADD the
/// char-boundary refusal, never remove a row, so the rendered spelling is a
/// fail-closed stand-in and not an authority.
pub(super) fn callee_is_str_split_at(callee: &str, key: Option<&trust_types::CalleeKey>) -> bool {
    use trust_types::SysrootItem as S;
    if trust_types::CalleeKey::opt_is_one_of(key, &[S::StrSplitAt, S::StrSplitAtMut]) {
        return true;
    }
    matches!(method_tail(callee), "split_at" | "split_at_mut")
        && callee.contains("str::<impl str>::")
}

/// W4 round 3 (2026-09-29): the failure body of `str::split_at(mid)` /
/// `str::split_at_mut(mid)`.
///
/// The method panics when `mid > len` OR when `mid` is not a UTF-8 char boundary
/// (`library/core/src/str/mod.rs`, `slice_error_fail`). `str` is extracted as
/// `[u8]`, so only the first half is a formula term. Until this round the `SplitAt`
/// arm charged `mid > len` and nothing else, and the call's
/// `[trust-absent-callee-assumption] ... may panic` row was tolerated as
/// runtime-checked because the call-site lane owned the family. So every proof of
/// `mid <= len` was taken as panic-freedom: on main `if !s.is_empty() {
/// s.split_at(1) }` built rc=0 and panicked on `"é"`, and W4's `str::len` tie and
/// affix length facts widened it to `s.split_at(s.len() / 2)` (adversarial round
/// 2, m40/m10/m10b/m13/m41, and m42/m43 on main).
///
/// The rule is the str range-index rule (`slice_method_panic_body`, RangeIndex):
/// the byte-bounds row stands only when `mid` is PROVABLY a char boundary of the
/// receiver, by structure. The credited shapes:
///  * the constant `0`;
///  * a `char_indices()` yield of the receiver's root (`0 <= mid <= len - 1`,
///    VC-locally, as in the range lane);
///  * a `str::find`/`rfind` match start or exact match end over the receiver's root
///    (`str_offset::str_search_endpoint_facts`, VC-locally);
///  * an authenticated `str::len` of the receiver's root — a string's byte length
///    is always a boundary; the `mid <= len` half is then the ordinary row.
///
/// Anything else — a guarded constant (`split_at(2)` after `starts_with("é")`, a
/// correct program), `len / 2`, `len - 1`, a `find` payload `+ 1`, a `&mut str`
/// receiver (whose root no shared-root gate admits) — is the fail-closed
/// `UnsupportedMir` row: refused, never a proof. Its receiver length need not be
/// modeled; an unmodeled one is refused the same way rather than skipped.
fn str_split_at_panic_body(
    func: &VerifiableFunction,
    receiver: &Operand,
    mid: &Operand,
) -> Option<(Formula, VcKind)> {
    let unmodeled = || {
        Some((
            super::unsupported::unsupported_mir_fail_closed_formula(),
            VcKind::UnsupportedMir {
                kind: "str-split-at-char-boundary-unmodeled".into(),
                detail: "str::split_at/split_at_mut panics when `mid` exceeds the length or \
                         is not a char boundary; char boundaries are not modeled, and `mid` \
                         is not a boundary this verifier can establish by structure (the \
                         constant 0, a `char_indices` offset, a `find`/`rfind` match start \
                         or exact match end, or the `len()` of the same string) — refused, \
                         never silently verified"
                    .into(),
            },
        ))
    };
    let Some(len) = crate::slice_len_formula(func, receiver) else { return unmodeled() };
    if const_int_value(mid) == Some(0) {
        let mid_f = crate::operand_to_formula(func, mid);
        return Some((Formula::Gt(Box::new(mid_f), Box::new(len)), VcKind::SliceBoundsCheck));
    }
    let roots: FxHashSet<usize> =
        charindices_shared_slice_root(func, receiver).into_iter().collect();
    if roots.is_empty() {
        return unmodeled();
    }
    let mid_f = crate::operand_to_formula(func, mid);
    let bounds_row = |mut facts: Vec<Formula>, violation: Formula| {
        let body = if facts.is_empty() {
            violation
        } else {
            facts.push(violation);
            Formula::And(facts)
        };
        Some((body, VcKind::SliceBoundsCheck))
    };
    if operand_is_charindices_yield_of(func, mid, &roots) {
        let violation = Formula::Gt(Box::new(mid_f.clone()), Box::new(len.clone()));
        return bounds_row(
            vec![
                Formula::Ge(Box::new(mid_f.clone()), Box::new(Formula::Int(0))),
                Formula::Le(
                    Box::new(mid_f),
                    Box::new(Formula::Sub(Box::new(len), Box::new(Formula::Int(1)))),
                ),
            ],
            violation,
        );
    }
    if let Some(facts) = str_search_endpoint_facts(func, mid, &roots, &mid_f, &len) {
        return bounds_row(facts, Formula::Gt(Box::new(mid_f), Box::new(len)));
    }
    if super::str_offset::operand_is_str_len_of_root(func, mid, &roots) {
        return bounds_row(Vec::new(), Formula::Gt(Box::new(mid_f), Box::new(len)));
    }
    unmodeled()
}

/// Trust (2026-09-25, F5): `BTreeMap::range(r)` / `BTreeSet::range(r)` PANIC
/// ("range start is greater than range end", "range start and end are equal and
/// excluded") on a caller-supplied range whose bounds are out of order, once the
/// map is non-empty (`search_tree_for_bifurcation`). Built exit 0 with a single
/// advisory for the bundled member, and panicked.
///
/// The violation, per argument shape:
///  * `a..b` (Included/Excluded) and `a..=b` (Included/Included): `a > b`;
///  * `(Bound, Bound)` with integer payloads: `s > e`, or `s >= e` when both are
///    `Excluded`; no obligation when either side is `Unbounded`;
///  * `..b`, `a..`, `..=b`, `..`: an `Unbounded` side — no obligation;
///  * anything else (a range whose endpoints do not trace to single-valued
///    integers, a user `RangeBounds`, a reference-payload `Bound`): the
///    fail-closed `UnsupportedMir` row. The check compares with `T::cmp`, so a
///    non-integer key is not modeled.
///
/// An EMPTY map does not panic; the obligation ignores that and is therefore
/// conservative, never a false proof. The kind is an `Assertion`: the check is
/// std's own and stays in the binary, exactly like an `assert!`.
///
/// Trust: 2026-10-14 — the bounds are named AT THE CALL (`range_bound_at_call_formula`,
/// the slice range-index lane's resolution), never by the joined-copy fallback. A copy
/// temp of a multiply-written bound (`_15 = copy k`) is connected to the row only where
/// its definition reaches it; in a loop body ahead of a write of `k` (`let r = a..k; if
/// c { k = n } if a > k { return } m.range(r)`) it did not, and the row was refuted at
/// the impossible `_15 = -1`. Such a bound now declines; one whose value at the read is
/// its value at the call is named by its version there and proves under its guard
/// (`tests/range_bound_joined_copy_realmir.rs`).
fn btree_range_panic_body(
    func: &VerifiableFunction,
    range: &Operand,
    call_block: &trust_types::BasicBlock,
) -> Option<(Formula, VcKind)> {
    let ordered = |msg: &str, violation: Formula| {
        Some((violation, VcKind::Assertion { message: format!("BTreeMap/BTreeSet::range: {msg}") }))
    };
    let unmodeled = || {
        Some((
            super::unsupported::unsupported_mir_fail_closed_formula(),
            VcKind::UnsupportedMir {
                kind: "btree-range-bounds-unmodeled".into(),
                detail: "BTreeMap/BTreeSet::range panics when the range start is greater \
                         than its end (or both are equal and excluded); the bounds of this \
                         range argument are not integer values this verifier can compare, \
                         so the ordering is not established — refused, never silently \
                         verified"
                    .into(),
            },
        ))
    };
    let int_bound = |op: &Operand| -> Option<Formula> {
        let is_int = crate::operand_ty_cow(func, op).is_some_and(|t| {
            matches!(t.as_ref(), Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char)
        });
        if !is_int {
            return None;
        }
        range_bound_at_call_formula(func, range, op, call_block)
    };
    let gt = |s: Formula, e: Formula| Formula::Gt(Box::new(s), Box::new(e));
    // The argument's own TYPE settles the never-panicking families first, so an
    // untraceable `RangeFrom` parameter is not refused.
    if let Some(ty) = crate::operand_ty_cow(func, range)
        && let Ty::Adt { name, .. } = ty.as_ref()
        && matches!(
            range_family_adt_name(name),
            Some("RangeTo" | "RangeFrom" | "RangeFull" | "RangeToInclusive")
        )
    {
        return None;
    }
    let Some(local) = operand_local(range) else {
        return unmodeled();
    };
    if let Some(RangeFamilyOperands::Exclusive(start, end)) =
        trace_local_to_range_family(func, local, 8)
    {
        return match (int_bound(start), int_bound(end)) {
            (Some(s), Some(e)) => ordered("range start is greater than range end", gt(s, e)),
            _ => unmodeled(),
        };
    }
    // `a..=b` spelled as the constructor call `RangeInclusive::new(a, b)`.
    if let Some(LocalDef::Call { callee, args }) = local_def(func, local)
        && is_range_inclusive_new_call(callee)
        && args.len() == 2
    {
        return match (int_bound(&args[0]), int_bound(&args[1])) {
            (Some(s), Some(e)) => ordered("range start is greater than range end", gt(s, e)),
            _ => unmodeled(),
        };
    }
    match crate::local_defs::unique_value_def(func, local) {
        // `a..=b`, as the aggregate optimized MIR renders it.
        Some(Rvalue::Aggregate(AggregateKind::Adt { name, .. }, ops))
            if range_family_adt_name(name) == Some("RangeInclusive") && ops.len() == 3 =>
        {
            match (int_bound(&ops[0]), int_bound(&ops[1])) {
                (Some(s), Some(e)) => ordered("range start is greater than range end", gt(s, e)),
                _ => unmodeled(),
            }
        }
        // `(start_bound, end_bound)`.
        Some(Rvalue::Aggregate(AggregateKind::Tuple, ops)) if ops.len() == 2 => {
            // `Bound` is `Included(T) = 0`, `Excluded(T) = 1`, `Unbounded = 2`.
            let bound = |op: &Operand| -> Option<(usize, Option<&Operand>)> {
                let l = operand_local(op)?;
                match crate::local_defs::unique_value_def(func, l)? {
                    Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, payload)
                        if name.split('<').next().is_some_and(|h| {
                            matches!(h, "core::ops::range::Bound" | "std::ops::Bound")
                        }) =>
                    {
                        Some((*variant, payload.first()))
                    }
                    _ => None,
                }
            };
            match (bound(&ops[0]), bound(&ops[1])) {
                (Some((2, _)), Some(_)) | (Some(_), Some((2, _))) => None,
                (Some((sv, Some(s))), Some((ev, Some(e)))) if sv <= 1 && ev <= 1 => {
                    match (int_bound(s), int_bound(e)) {
                        (Some(s), Some(e)) if sv == 1 && ev == 1 => ordered(
                            "range start is greater than range end, or both are equal and excluded",
                            Formula::Ge(Box::new(s), Box::new(e)),
                        ),
                        (Some(s), Some(e)) => {
                            ordered("range start is greater than range end", gt(s, e))
                        }
                        _ => unmodeled(),
                    }
                }
                _ => unmodeled(),
            }
        }
        _ => unmodeled(),
    }
}

/// Trust (2026-09-25, F5): the INHERENT `BTreeMap::range` / `BTreeSet::range`
/// (and `BTreeMap::range_mut`, which runs the same bound check — measured, a
/// `range_mut(5..1)` built rc=0 and panicked once `range` was charged),
/// anchored on the genuine `alloc` module path (generics stripped), so a user
/// method named `range` never matches and a stamped impersonator's path does not
/// start with `alloc::`.
pub(super) fn is_btree_range_call(callee: &str) -> bool {
    if callee.contains(" as ") || trust_types::path_has_unauthenticated_crate_stamp(callee) {
        return false;
    }
    matches!(
        vc_strip_generics_cow(callee).as_ref(),
        "alloc::collections::btree::map::BTreeMap::range"
            | "alloc::collections::btree::map::BTreeMap::range_mut"
            | "alloc::collections::btree::set::BTreeSet::range"
            | "std::collections::BTreeMap::range"
            | "std::collections::BTreeMap::range_mut"
            | "std::collections::BTreeSet::range"
    )
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
            let mut lhs_ty = crate::operand_ty(func, lhs)?;
            let mut rhs_ty = crate::operand_ty(func, rhs)?;
            // Trust (LITERAL-PAIR-WIDTH-1, 2026-10-13): TWO width-less signed
            // literals (`i8::MAX.unchecked_add(1)`, `100i8.unchecked_mul(2)`) carry
            // no width, and `int_op_type` answers the i64 `operand_ty` fabricates for
            // a bare literal: the row read `127 + 1 outside i64` (UNSAT) and shipped
            // `unchecked_overflow:add` PROVED, clean-kernel-certified, for a call
            // whose precondition fails on every run. `unchecked_{add,sub,mul}`
            // returns its operands' type, so the DESTINATION is the operation's
            // type, exactly as the `Pow` arm below reads it. A destination that is
            // not a fixed-width integer gets the `Pow` arm's fail-closed body
            // (`Formula::Bool(true)`, refutable, no proof authority), never `None`:
            // the caller reads `None` as "no obligation", which would make the call
            // vacuously safe. Every other argument pair keeps `int_op_type`.
            let (width, signed) = if v2_operands_are_literal_pair(lhs, rhs) {
                let dest_ty = crate::place_ty(func, dest);
                let Some((dest_ty, (width, signed))) = dest_ty.and_then(|ty| {
                    let descriptor = crate::fixed_width_integer_descriptor(&ty)?;
                    Some((ty, descriptor))
                }) else {
                    let width = lhs_ty.int_width().unwrap_or(64);
                    return Some((Formula::Bool(true), op, lhs_ty, rhs_ty, width));
                };
                lhs_ty = dest_ty.clone();
                rhs_ty = dest_ty;
                (width, signed)
            } else {
                int_op_type(func, lhs, rhs)?
            };
            let lhs_f = operand_to_formula(func, lhs);
            let rhs_f = operand_to_formula(func, rhs);
            let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
            let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);
            let result = match op {
                BinOp::Add => Formula::Add(Box::new(lhs_f), Box::new(rhs_f)),
                BinOp::Sub => Formula::Sub(Box::new(lhs_f), Box::new(rhs_f)),
                BinOp::Mul => Formula::Mul(Box::new(lhs_f), Box::new(rhs_f)),
                _ => return None,
            };
            let min_f = crate::range::type_min_formula(width, signed);
            let max_f = crate::range::type_max_formula(width, signed);
            let out_of_range = Formula::Or(vec![
                Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
                Formula::Gt(Box::new(result), Box::new(max_f)),
            ]);
            let body = Formula::And(vec![lhs_range, rhs_range, out_of_range]);
            // `width` is the REAL operand width (`int_op_type`'s non-constant operand,
            // or the destination for a literal pair); the call arm records it on the
            // authenticated obligation.
            Some((body, op, lhs_ty, rhs_ty, width))
        }
        OverflowCall::Pow => {
            // `base.pow(exp)` — the receiver is the first arg, the exponent the
            // second. The result type == receiver type for `pow`; take the width
            // from the destination place (falling back to the base operand).
            let base = args.first()?;
            let exp = args.get(1)?;
            let result_ty = crate::place_ty_cow(func, dest)
                .or_else(|| crate::operand_ty_cow(func, base))?
                .into_owned();
            let width = result_ty.int_width()?;
            let signed = result_ty.is_signed();
            // Trust (2026-10-05, POW-SYMEXP-1): every body below is EXACT — it is
            // satisfiable at an in-type `(base, exp)` iff `base^exp` leaves the
            // type, which is precisely when core's `checked_pow` answers `None`
            // and `pow`/`strict_pow` panic (an intermediate square can overflow
            // only when the final result does). The fitting-base table that makes
            // the symbolic arm exact is defined for real integer widths only, so
            // any other width fails closed instead of guessing.
            let fail_closed =
                |ty: Ty| Some((Formula::Bool(true), BinOp::Mul, ty.clone(), ty, width));
            if !(2..=128).contains(&width) {
                return fail_closed(result_ty);
            }
            let max_f = crate::range::type_max_formula(width, signed);
            let min_f = crate::range::type_min_formula(width, signed);

            let base_f = operand_to_formula(func, base);

            // A LITERAL base decides everything by one number: the least exponent
            // `t` whose power leaves the type. Overflow is UPWARD CLOSED in the
            // exponent for `|base| >= 2` (`|b^(k+1)| >= 2|b^k| > 2*MAX >= |MIN|`),
            // whatever the base's sign — so `(-2i32).pow(e)` overflows exactly for
            // `e >= 32` (`(-2)^31 == i32::MIN` fits), and `2i32.pow(e)` exactly for
            // `e >= 31`. A base in `{-1, 0, 1}` never overflows: no obligation
            // (mirrors the BinaryOp path skipping a provably-safe op).
            if let Some(b) = const_int_value(base) {
                // `None`: the base never overflows — no obligation.
                let t = pow_literal_base_overflow_threshold(b, width, signed)?;
                if let Some(e) = const_int_value(exp) {
                    // BOTH operands literal: decided concretely. A power that fits
                    // (e.g. `2u32.pow(3)` == 8, or `(-2i32).pow(31)` == MIN) gets NO
                    // obligation — mirrors the const-size allocation skip, a
                    // trivially-safe constant must produce no obligation at all,
                    // not a vacuous one. A provably-overflowing one (and a negative
                    // "exponent" no `u32` can hold) gets a fail-closed obligation.
                    if (0..i128::from(t)).contains(&e) {
                        return None;
                    }
                    return fail_closed(result_ty);
                }
                let exp_f = operand_to_formula(func, exp);
                let body = Formula::Ge(Box::new(exp_f), Box::new(Formula::Int(i128::from(t))));
                return Some((body, BinOp::Mul, result_ty.clone(), result_ty, width));
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
                    // Not a value a `u32` exponent can hold: a malformed body.
                    // Trust (POW-SYMEXP-1): fail closed instead of minting nothing.
                    return fail_closed(result_ty);
                }
                if e <= 1 {
                    return None; // base^0 == 1, base^1 == base: cannot overflow
                }
                // Cap the unroll so a pathological constant exponent cannot blow up
                // the formula; a larger constant exponent takes the exact
                // fitting-base model below (only `|base| <= 1` survives it).
                if e <= i128::from(width) {
                    let base_range = crate::range::input_range_constraint(&base_f, width, signed);
                    let mut product = base_f.clone();
                    for _ in 1..e - 1 {
                        product = Formula::Mul(Box::new(product), Box::new(base_f.clone()));
                    }
                    product = Formula::Mul(Box::new(product), Box::new(base_f));
                    let out_of_range = Formula::Or(vec![
                        Formula::Gt(Box::new(product.clone()), Box::new(max_f)),
                        Formula::Lt(Box::new(product), Box::new(min_f)),
                    ]);
                    let body = Formula::And(vec![base_range, out_of_range]);
                    return Some((body, BinOp::Mul, result_ty.clone(), result_ty, width));
                }
            }

            // SYMBOLIC base with a SYMBOLIC exponent (or a constant one above the
            // width). Trust (2026-10-05, POW-SYMEXP-1): this arm used to build
            // `base >= 2 AND exp >= W` (`W - 1` when signed), described as a
            // "sound linear over-approximation". It was the opposite: a condition
            // that GUARANTEES overflow, not one every overflow satisfies, so as the
            // satisfiable-iff-violation body it PROVED the row for any negative
            // base (`(-2i32).pow(e)`, `if b < 0 { b.pow(e) }`) and for any guard
            // that bounds the exponent below the width (`if e < 32 { b.pow(e) }`,
            // which overflows at `3u32.pow(21)`). The row was kernel-certified and
            // the default lane accepted a `pow` that panics.
            //
            // The body is now EXACT and still linear: for each exponent `k` in
            // `2..W` the bases whose `k`-th power fits form an interval `[lo_k,
            // hi_k]` (`pow_fitting_base_interval`), so the violation is
            // `OR_k (exp == k AND base outside [lo_k, hi_k])` — runs of `k` sharing
            // an interval merged into one `k1 <= exp <= k2` disjunct — plus
            // `exp >= W AND |base| >= 2` (`2^W` exceeds both `MAX` and `|MIN|`).
            // Exponents 0 and 1 never overflow. A dominating guard on the exponent,
            // the base or both (`b < 10 && e < 5`) discharges it; anything that
            // admits an overflowing pair is refuted with that pair.
            let exp_f = operand_to_formula(func, exp);
            let base_range = crate::range::input_range_constraint(&base_f, width, signed);
            let violation = pow_symbolic_violation(&base_f, &exp_f, width, signed);
            // Two conjuncts, like the constant-exponent body: never the canonical
            // three-conjunct arithmetic core `v2_arith_overflow_seed_record` seeds.
            let body = Formula::And(vec![base_range, violation]);
            Some((body, BinOp::Mul, result_ty.clone(), result_ty, width))
        }
    }
}

/// Trust (2026-10-05, POW-SYMEXP-1): the largest `r >= 0` with `r^k <= n`, for
/// `k >= 1` — by binary search with checked arithmetic, so no rounding and no
/// wrap. For `k >= 2` the root of any `u128` is at most `2^64 - 1`, which bounds
/// the search.
pub(super) fn pow_root_floor(n: u128, k: u32) -> u128 {
    if k <= 1 {
        return n;
    }
    // Invariant: `lo^k <= n` and `hi^k > n` (or `hi^k` overflows `u128`, which
    // `(2^64)^2 == 2^128` does).
    let (mut lo, mut hi) = (0u128, 1u128 << 64);
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match mid.checked_pow(k) {
            Some(p) if p <= n => lo = mid,
            _ => hi = mid,
        }
    }
    lo
}

/// Trust (2026-10-05, POW-SYMEXP-1): the closed interval `[lo, hi]` of bases `b`
/// of the integer type `(width, signed)` whose `b^k` is again a value of that
/// type, for an exponent `k >= 2` and `2 <= width <= 128`.
///
/// `b^k` is monotone in `|b|` (and, for odd `k`, in `b`), so the set is an
/// interval: `hi` is the largest `r >= 0` with `r^k <= MAX`; for a signed type
/// with even `k` the lower end is `-hi` (the power is positive), and with odd
/// `k` it is `-s` for the largest `s` with `s^k <= |MIN| == 2^(W-1)`. So
/// `i32` at `k = 31` is `[-2, 1]` (`(-2)^31 == i32::MIN`), and an unsigned type
/// has `lo == 0`. Every `hi`/`lo` fits `i128` (at most `2^64` in magnitude).
pub(super) fn pow_fitting_base_interval(width: u32, signed: bool, k: u32) -> (i128, i128) {
    // `k >= width` leaves only `|b| <= 1` (`2^k >= 2^W` exceeds MAX and |MIN|);
    // answered directly so a huge constant exponent costs nothing.
    if k >= width {
        return (if signed { -1 } else { 0 }, 1);
    }
    let to_i128 = |v: u128| i128::try_from(v).unwrap_or(i128::MAX);
    if signed {
        // `MAX == 2^(W-1) - 1 >= 0` and `|MIN| == 2^(W-1) <= 2^127`, both `u128`.
        let pos_max = crate::range::signed_max(width).unsigned_abs();
        let neg_mag = pos_max + 1;
        let hi = pow_root_floor(pos_max, k);
        let lo_mag = if k.is_multiple_of(2) { hi } else { pow_root_floor(neg_mag, k) };
        (-to_i128(lo_mag), to_i128(hi))
    } else {
        (0, to_i128(pow_root_floor(crate::range::unsigned_max(width), k)))
    }
}

/// Trust (2026-10-05, POW-SYMEXP-1): for a LITERAL base `b`, the least exponent
/// `t` with `b^t` outside the integer type `(width, signed)`; `None` when no
/// exponent overflows (`b` in `{0, 1}`, and `-1` when signed). Overflow is upward
/// closed in the exponent for `|b| >= 2`, so the violation for a symbolic
/// exponent is exactly `exp >= t`. A literal that is not a value of the type at
/// all (a malformed body) answers `Some(0)`: every exponent is charged.
pub(super) fn pow_literal_base_overflow_threshold(
    b: i128,
    width: u32,
    signed: bool,
) -> Option<u32> {
    // `|b| >= 2` past the early returns, so the power leaves the type within 128
    // steps; `acc` stays inside the type until it does, and a failed
    // `checked_mul` means the true power left the carrier, hence the type too.
    if signed {
        let (min, max) = (crate::range::signed_min(width), crate::range::signed_max(width));
        if b < min || b > max {
            return Some(0);
        }
        if (-1..=1).contains(&b) {
            return None;
        }
        let mut acc: i128 = 1;
        for t in 1..=129u32 {
            match acc.checked_mul(b) {
                Some(v) if (min..=max).contains(&v) => acc = v,
                _ => return Some(t),
            }
        }
    } else {
        // Computed in `u128`, so `u128`'s top half counts as fitting
        // (`2u128.pow(127)` fits). A `u128` literal above `i128::MAX` never
        // arrives here: `const_int_value` does not return it.
        let max = crate::range::unsigned_max(width);
        let Ok(b) = u128::try_from(b) else {
            return Some(0);
        };
        if b > max {
            return Some(0);
        }
        if b <= 1 {
            return None;
        }
        let mut acc: u128 = 1;
        for t in 1..=129u32 {
            match acc.checked_mul(b) {
                Some(v) if v <= max => acc = v,
                _ => return Some(t),
            }
        }
    }
    Some(0)
}

/// Trust (2026-10-05, POW-SYMEXP-1): the exact violation of `base.pow(exp)` over
/// a symbolic exponent — `OR_k (exp in run_k AND base outside [lo_k, hi_k])` for
/// the runs of `k in 2..W` that share a fitting interval, plus
/// `exp >= W AND |base| >= 2`. See `pow_fitting_base_interval`.
///
/// Spelled as ONE flat `Or` of `And`s of order atoms over `base`/`exp` and a
/// literal — `k1 <= exp AND exp <= k2 AND base > hi`, and for a signed type a
/// sibling `... AND base < lo` — rather than `exp == k AND (base > hi OR base <
/// lo)`. The set is the same; the flat spelling is what the clean-kernel
/// certifier's disjunctive lane reads (each disjunct a conjunction of order atoms
/// refuted against the context; it skips an equality and does not look inside a
/// nested `Or`), so a guard that excludes every overflow keeps a
/// kernel-certified row (`overflow_call_tests::guarded_pow_rows_stay_kernel_certified`).
fn pow_symbolic_violation(base_f: &Formula, exp_f: &Formula, width: u32, signed: bool) -> Formula {
    let int = |v: i128| Box::new(Formula::Int(v));
    let mut disjuncts = Vec::new();
    let mut push_outside = |mut exp_atoms: Vec<Formula>, (lo, hi): (i128, i128)| {
        // `lo == 0` for an unsigned type, whose base is never negative.
        if signed {
            let mut above = Vec::with_capacity(exp_atoms.len() + 1);
            above.extend_from_slice(&exp_atoms);
            above.push(Formula::Gt(Box::new(base_f.clone()), int(hi)));
            disjuncts.push(Formula::And(above));
            exp_atoms.push(Formula::Lt(Box::new(base_f.clone()), int(lo)));
            disjuncts.push(Formula::And(exp_atoms));
        } else {
            exp_atoms.push(Formula::Gt(Box::new(base_f.clone()), int(hi)));
            disjuncts.push(Formula::And(exp_atoms));
        }
    };
    let mut k = 2u32;
    while k < width {
        let interval = pow_fitting_base_interval(width, signed, k);
        let mut last = k;
        while last + 1 < width && pow_fitting_base_interval(width, signed, last + 1) == interval {
            last += 1;
        }
        push_outside(
            vec![
                Formula::Ge(Box::new(exp_f.clone()), int(i128::from(k))),
                Formula::Le(Box::new(exp_f.clone()), int(i128::from(last))),
            ],
            interval,
        );
        k = last + 1;
    }
    push_outside(
        vec![Formula::Ge(Box::new(exp_f.clone()), int(i128::from(width)))],
        pow_fitting_base_interval(width, signed, width),
    );
    Formula::Or(disjuncts)
}

/// The signed integer value of a literal operand, if it is one.
pub(super) fn const_int_value(op: &Operand) -> Option<i128> {
    match op {
        Operand::Constant(ConstValue::Int(v)) => Some(*v),
        Operand::Constant(ConstValue::Uint(v, _)) => i128::try_from(*v).ok(),
        _ => None,
    }
}
