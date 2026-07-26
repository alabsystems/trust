// Panic-freedom for the `Option`/`Result` unwrap family. The obligation is
// discharged by pinning the receiver's discriminant tag: trace the value back
// to the call or construction that fixed it, and refute the panicking variant.
// Also the catalogue of std methods that panic on out-of-range arguments.

use super::*;

/// Trust (reliability E1): a call to a std slice/`Vec` method that PANICS on an
/// out-of-range argument (`> len`) but is NOT in `is_known_panicking_method`
/// (Option/Result unwrap family) nor `slice_method_panic` (the precisely-modeled
/// `split_at`/`chunks`/`swap`/range-index lane). These have a normal-return target
/// (the rotated/split slice) but an unmodeled internal panic path:
///   * `<[T]>::rotate_left(mid)` / `rotate_right(mid)` — panic when `mid > len`.
///   * `Vec`/`String`/`VecDeque`::`split_off(at)` — panic when `at > len`.
///   * `Vec`/`String`/`VecDeque`::`drain(range)` — panic when `start > end` or
///     `end > len` (`v.drain(0..99)` on a shorter Vec panics at runtime). The no-arg
///     `HashMap`/`HashSet`/`BinaryHeap::drain()` are TOTAL (drain everything, never
///     panic) — discriminated below by arg count (a range-taking drain has arg 1;
///     a total drain has only the receiver).
///   * `<[T]>::copy_within(src, dest)` — panic when the source range is out of range
///     or `dest + src.len() > len`.
///   * `<[T]>::select_nth_unstable(i)` / `_by` / `_by_key` — panic when `i >= len`.
/// They are surfaced as an UnsupportedMir → Unknown obligation, which can only make
/// the default headline MORE conservative (Unknown, never Proved) — so an
/// over-match is honest-but-imprecise, never unsound.
///
/// SOUNDNESS of the slice/`Vec` discrimination — `rotate_left`/`rotate_right` ALSO
/// name TOTAL integer methods (`u32::rotate_left`, never panics); flagging those
/// would only be over-conservative (Unknown, not a false proof), but we exclude
/// them anyway to keep the default headline clean. The receiver must be a confirmed
/// slice/`Vec`, established by EITHER (a) a modeled slice length on arg 0
/// (`slice_len_formula`/`param_slice_len`, true for `&[T]`/`&mut [T]` receivers),
/// OR (b) a callee path that names the slice/`Vec` container (`slice` / `vec::Vec`
/// / `[T]`) and is NOT an integer-`num` method. An integer rotate renders as
/// `core::num::<impl u32>::rotate_left` (matches neither (a) nor (b)) and is
/// EXCLUDED; an owned `Vec::split_off` (whose `&Vec` receiver has no modeled
/// slice length) is caught by (b).
pub(super) fn is_bounds_panicking_slice_mutator(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> bool {
    if !matches!(
        method_tail(callee),
        "rotate_left"
            | "rotate_right"
            | "split_off"
            | "drain"
            // Slice-only bounds-panicking methods (no total same-name method exists,
            // so no name-collision exclusion is needed like the integer-`rotate` case):
            //   * `<[T]>::copy_within(src, dest)` — panics if `src` is out of range or
            //     `dest + src.len() > len`.
            //   * `<[T]>::select_nth_unstable(i)` / `_by` / `_by_key` — panic if `i >= len`.
            | "copy_within"
            | "select_nth_unstable"
            | "select_nth_unstable_by"
            | "select_nth_unstable_by_key"
            // `Vec::extend_from_within(range)` (T: Copy) — panics on an out-of-range
            // `range` (`start > end` / `end > len`). Unique name (no total same-name
            // method), `Vec` receiver. It ALSO has a capacity-overflow panic path on
            // reallocation; the whole-call fail-honest Unknown covers BOTH soundly
            // (never Proved), so no separate overflow model is needed here.
            | "extend_from_within"
    ) {
        return false;
    }
    // `drain` DISCRIMINATION: only the range-taking drains (`Vec`/`String`/`VecDeque`,
    // whose call carries the receiver PLUS a range arg) panic on a bad range. The no-arg
    // `HashMap`/`HashSet`/`BinaryHeap::drain()` drain everything and are TOTAL — their
    // call has ONLY the receiver (args.len() == 1). Excluding them avoids an unnecessary
    // (still sound: Unknown, non-fatal) over-refusal of a total method. rotate/split_off
    // both take a scalar arg, so they naturally have args.len() == 2 and are unaffected.
    if method_tail(callee) == "drain" && args.len() < 2 {
        return false;
    }
    // (a) A modeled slice length on the receiver (arg 0) proves a slice receiver.
    let receiver_is_modeled_slice = args.first().is_some_and(|recv| {
        param_slice_len(func, recv, 8).is_some() || crate::slice_len_formula(func, recv).is_some()
    });
    if receiver_is_modeled_slice {
        return true;
    }
    // (b) Path-based fallback for owned `Vec`/`String`/`VecDeque` receivers (no
    // modeled slice length). EXCLUDE integer methods, which render as
    // `core::num::<impl u32>::rotate_left` — `num`/`<impl u`/`<impl i` markers.
    let is_integer_method =
        callee.contains("::num::") || callee.contains("<impl u") || callee.contains("<impl i");
    if is_integer_method {
        return false;
    }
    callee.contains("slice")
        || callee.contains("vec::Vec")
        || callee.contains("Vec::")
        || callee.contains("[T]")
        || callee.contains("collections::")
}

/// Trust (hunt-15 Class D): a call to a std method that PANICS on its failure
/// variant — `Option`/`Result` `unwrap`/`expect`/`unwrap_err`/`expect_err`. These
/// have a normal-return target (the success value) but an unmodeled internal panic
/// path, so the canonical pipeline surfaces them as Unknown to keep the headline from
/// over-crediting. `unwrap_unchecked`/`unwrap_or*` are EXCLUDED: the former is UB
/// (a different obligation class), the latter are total (no panic). The
/// `Option`/`Result` path guard avoids an unrelated user `unwrap`/`expect`; an
/// over-match would only be over-conservative (Unknown), never unsound.
pub(super) fn is_known_panicking_method(callee: &str) -> bool {
    matches!(method_tail(callee), "unwrap" | "expect" | "unwrap_err" | "expect_err")
        && (callee.contains("Option") || callee.contains("Result"))
}

/// Trust (signed `iN::abs` panic-freedom, 2026-07-06): the std inherent
/// `i8/i16/i32/i64/i128/isize::abs` PANICS (debug) / wraps (release) when its
/// receiver is `iN::MIN` — the exact same overflow as `-x` (there is no positive
/// representation of `MIN`). `-x` is caught by `v2_build_negation_raw_vc`, but
/// `x.abs()` lowers to an OPAQUE `Call` to `core::num::<impl iN>::abs`, so without
/// this recognizer the panic path is unmodeled and a genuinely-unsafe `x.abs()`
/// compiles clean — a hole in panic-freedom and an inconsistency with the caught
/// `-x`. Anchored to the std `core::num`/`std::num` inherent-impl path and the exact
/// `abs` method tail, so `wrapping_abs`/`unsigned_abs`/`checked_abs`/
/// `overflowing_abs` (which do NOT panic) and any user `.abs()` are excluded; the
/// body additionally gates on a SIGNED-INT receiver, so a float `abs` (total) is
/// never matched.
pub(super) fn is_signed_abs_call(callee: &str) -> bool {
    method_tail(callee) == "abs"
        && (callee.contains("core::num::") || callee.contains("std::num::"))
}

/// The panic-freedom VIOLATION formula (and the receiver's signed-int type) for a
/// signed `iN::abs` call: SAT iff the receiver can be `iN::MIN` (its sole panic
/// input). Mirrors the negation-overflow obligation (`v2_build_negation_raw_vc`)
/// exactly, so a bounded/guarded receiver (`if x != iN::MIN { x.abs() }`, `(x &
/// 0x7f).abs()`) proves and an unconstrained one stays refutable. The type is
/// returned so the emitted obligation carries `VcKind::NegationOverflow { ty }` —
/// abs-at-MIN IS a negation overflow, and that kind routes identically to `-x`
/// (BV-capable discharge), where a plain `Assertion` panic-freedom kind does NOT
/// discharge the BV bound and would FALSE-refute `(x & 0x7f).abs()`. `None` for a
/// non-signed-int receiver (a float `abs` is total — no panic).
pub(super) fn signed_abs_panic_body(func: &VerifiableFunction, args: &[Operand]) -> Option<(Formula, Ty)> {
    let arg = args.first()?;
    let ty = crate::operand_ty(func, arg)?;
    let Ty::Int { width, signed: true } = ty else {
        return None;
    };
    let value = operand_to_formula(func, arg);
    let int_min = crate::range::type_min_formula(width, true);
    let body = Formula::And(vec![
        crate::range::input_range_constraint(&value, width, true),
        Formula::Eq(Box::new(value), Box::new(int_min)),
    ]);
    Some((body, ty))
}

/// Trust (unwrap panic-freedom, dominated-safe): the std enum def-paths, the
/// expected variant-name pair, and the PANIC-variant name for a std
/// `Option`/`Result` `unwrap`-family call. `None` for anything else — in
/// particular a USER extension-trait `unwrap`/`expect` (whose panic semantics
/// are arbitrary; modeling them could mint a false panic-freedom proof) never
/// matches: the caller additionally anchors the callee path on the std enum
/// def-path prefix, which a user item can never carry under `safe_def_path_str`.
pub(super) fn std_unwrap_family_panic_variant(
    callee: &str,
) -> Option<(&'static [&'static str], &'static [&'static str], &'static str)> {
    const OPTION_PATHS: &[&str] = &["core::option::Option", "std::option::Option"];
    const OPTION_VARIANTS: &[&str] = &["None", "Some"];
    const RESULT_PATHS: &[&str] = &["core::result::Result", "std::result::Result"];
    const RESULT_VARIANTS: &[&str] = &["Ok", "Err"];
    // Anchor on the callee PREFIX (the method's self type), never a substring:
    // `Result::<Option<T>, E>::unwrap` mentions BOTH enums in its generic args,
    // but only the prefix names the receiver.
    let is_option = OPTION_PATHS.iter().any(|p| callee.starts_with(p));
    let is_result = RESULT_PATHS.iter().any(|p| callee.starts_with(p));
    match method_tail(callee) {
        // `unwrap`/`expect` panic on the FAILURE variant.
        "unwrap" | "expect" if is_option => Some((OPTION_PATHS, OPTION_VARIANTS, "None")),
        "unwrap" | "expect" if is_result => Some((RESULT_PATHS, RESULT_VARIANTS, "Err")),
        // `unwrap_err`/`expect_err` (Result-only) panic on the SUCCESS variant.
        "unwrap_err" | "expect_err" if is_result => Some((RESULT_PATHS, RESULT_VARIANTS, "Ok")),
        _ => None,
    }
}

/// Trust (tag-transparent hop): a std `Option`/`Result` `as_ref` call — its
/// result's discriminant EQUALS its receiver's discriminant by definition, so
/// tag-origin resolution may hop through it. `as_mut` is deliberately excluded:
/// its `&mut self` borrow already unpins the receiver, so the chain fails
/// closed anyway, and a mutable reborrow could feed a `SetDiscriminant`.
pub(super) fn std_as_ref_call(callee: &str) -> bool {
    const OPTION_PATHS: [&str; 2] = ["core::option::Option", "std::option::Option"];
    const RESULT_PATHS: [&str; 2] = ["core::result::Result", "std::result::Result"];
    method_tail(callee) == "as_ref"
        && (OPTION_PATHS.iter().any(|p| callee.starts_with(p))
            || RESULT_PATHS.iter().any(|p| callee.starts_with(p)))
}

/// Trust (tag-transparent hop): [`unwrap_receiver_origin`] extended THROUGH std
/// `as_ref` calls — for `o.as_ref().is_some()` / `o.as_ref().unwrap()` the tag
/// origin resolves to `o` itself, because `as_ref` preserves the discriminant
/// exactly. Each hop requires the full probe borrow shape (the call's single
/// argument is a Copy/Move of a bare local whose unique def is a SHARED borrow
/// of a bare local) and re-runs the pinned-origin resolution on the referent,
/// so an unpinned link still fails closed. Depth-capped like the base resolver.
pub(super) fn unwrap_tag_origin(func: &VerifiableFunction, local: usize) -> Option<usize> {
    let mut cur = unwrap_receiver_origin(func, local)?;
    for _ in 0..4 {
        let Some((callee, args)) = unwrap_origin_call_def(func, cur) else {
            return Some(cur);
        };
        if !std_as_ref_call(callee) {
            return Some(cur);
        }
        let Some(Operand::Copy(p) | Operand::Move(p)) = args.first() else {
            return Some(cur);
        };
        if !p.projections.is_empty() {
            return Some(cur);
        }
        // SOUNDNESS (aliased reseat, audit r4): the as_ref receiver temp `p`
        // must be PINNED before its `&referent` def is trusted — a reseated `p`
        // has a stale borrow def, so the hop would resolve to the wrong origin.
        // Stop the hop (keep the current pinned origin) on an unpinned link.
        if !unwrap_receiver_local_is_pinned(func, p.local) {
            return Some(cur);
        }
        let Some(Rvalue::Ref { mutable: false, place: referent }) =
            crate::unique_whole_local_def(func, p.local)
        else {
            return Some(cur);
        };
        if !referent.projections.is_empty() {
            return Some(cur);
        }
        cur = unwrap_receiver_origin(func, referent.local)?;
    }
    Some(cur)
}

/// Trust (tag-transparent hop, observer-gate contract): does this block's
/// terminator define an `as_ref` result whose tag-origin resolution CONNECTS
/// back to `origin`? Only then is the as_ref call a connected (whitelisted)
/// observer — the fires-only discipline every modeled channel follows.
pub(super) fn as_ref_hop_connected(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    origin: usize,
) -> bool {
    let Terminator::Call { func: callee, dest, .. } = &block.terminator else {
        return false;
    };
    std_as_ref_call(callee)
        && dest.projections.is_empty()
        && unwrap_tag_origin(func, dest.local) == Some(origin)
}

/// Trust (probe-call model): the std enum def-paths and the PROBED variant name
/// for a std `Option`/`Result` state probe (`is_some`/`is_none`/`is_ok`/`is_err`).
/// `None` for anything else — a USER extension-trait probe never matches (the
/// caller additionally anchors the receiver type on the std enum def-path, which
/// a user item can never carry under `safe_def_path_str`). The probe's return
/// value is EXACTLY `receiver.__tag == probe_tag`, which is what
/// [`probe_call_definitions`] records.
pub(super) fn std_option_result_probe_variant(
    callee: &str,
) -> Option<(&'static [&'static str], &'static str)> {
    const OPTION_PATHS: &[&str] = &["core::option::Option", "std::option::Option"];
    const RESULT_PATHS: &[&str] = &["core::result::Result", "std::result::Result"];
    let is_option = OPTION_PATHS.iter().any(|p| callee.starts_with(p));
    let is_result = RESULT_PATHS.iter().any(|p| callee.starts_with(p));
    match method_tail(callee) {
        "is_some" if is_option => Some((OPTION_PATHS, "Some")),
        "is_none" if is_option => Some((OPTION_PATHS, "None")),
        "is_ok" if is_result => Some((RESULT_PATHS, "Ok")),
        "is_err" if is_result => Some((RESULT_PATHS, "Err")),
        _ => None,
    }
}

/// Trust (probe-call model): the PATH-DEFINITION facts a modeled std probe call
/// terminator establishes on its success edge — for `_g = o.is_some()` (MIR:
/// `_b = &o; _g = is_some(move _b)`), the exact result semantics
///   `(_g ∧ tag == PROBE) ∨ (¬_g ∧ tag ≠ PROBE)`
/// plus the variant-range fact `tag ∈ {variant tags}` over the SAME tag term, so
/// a two-variant complement (`is_err() == false ⇒ tag == Ok`) also discharges.
/// The tag term is the SHARED one the unwrap lane cites
/// ([`receiver_tag_term_any`]): a dominating `if o.is_some()` guard (`_g`, via
/// the bool path guard) then pins the very variable the unwrap VC's body tests,
/// turning the un-inlined probe idiom from a fail-closed UNKNOWN into a PROVED
/// obligation — and an `if o.is_none()`-guarded unwrap into a refutation.
///
/// Fail-closed (`Vec::new()`) on every unrecognized shape: non-probe callee,
/// projected/non-SSA bool dest, a receiver that is not a shared borrow of a
/// pinned bare local, a non-modeled enum layout, or no derivable tag term.
/// SOUNDNESS: `is_*` are TOTAL and return exactly the discriminant test of the
/// receiver AT THE CALL; the receiver origin is pinned
/// (`unwrap_receiver_origin`), so its tag at the call equals the recorded term
/// (a construction tag, a prior read's dest, or the free entry-tag field of a
/// pinned parameter). The fact is threaded only to the call's successor (the
/// path-definition fixpoint pushes terminator outflow to `ClauseTarget::Block`
/// targets), never before the call.
pub(super) fn probe_call_definitions(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return Vec::new();
    };
    let Some((enum_paths, probe_variant)) = std_option_result_probe_variant(callee) else {
        return Vec::new();
    };
    // Result: a bare SSA bool local (the guard temp).
    if !dest.projections.is_empty() || !is_single_static_assignment(func, dest.local) {
        return Vec::new();
    }
    if !crate::local_ty_ref(func, dest.local).is_some_and(|t| matches!(t, Ty::Bool)) {
        return Vec::new();
    }
    // Receiver: probes take `&self` — a Copy/Move of a bare local whose unique
    // def is a shared borrow of a bare local (the `is_ok`-call shape).
    let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else {
        return Vec::new();
    };
    if !recv.projections.is_empty() {
        return Vec::new();
    }
    // SOUNDNESS (aliased reseat, audit r4): pin `recv` before trusting its
    // `&referent` def — a reseated probe receiver has a stale borrow def, so the
    // fact would be minted over the wrong subject while the probe reads another.
    if !unwrap_receiver_local_is_pinned(func, recv.local) {
        return Vec::new();
    }
    let Some(Rvalue::Ref { mutable: false, place: referent }) =
        crate::unique_whole_local_def(func, recv.local)
    else {
        return Vec::new();
    };
    if !referent.projections.is_empty() {
        return Vec::new();
    }
    // Tag-transparent: `o.as_ref().is_some()` probes the as_ref RESULT, whose
    // discriminant equals `o`'s — resolve the origin THROUGH the hop so the
    // fact cites `o`'s own tag term (the one the unwrap obligation tests).
    let Some(origin) = unwrap_tag_origin(func, referent.local) else {
        return Vec::new();
    };
    let Some(ty) = crate::local_ty_ref(func, origin) else {
        return Vec::new();
    };
    let Some((name, variants)) = modeled_std_enum_shape(ty) else {
        return Vec::new();
    };
    if !enum_paths.contains(&name) {
        return Vec::new();
    }
    let Some(probe_tag) = variants.iter().find(|v| v.name == probe_variant).map(|v| v.discriminant)
    else {
        return Vec::new();
    };
    let Some(tag) = receiver_tag_term_any(func, origin, variants) else {
        return Vec::new();
    };
    let guard = Formula::Var(place_to_var_name(func, dest), Sort::Bool);
    let probed = Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(probe_tag)));
    let semantics = Formula::Or(vec![
        Formula::And(vec![guard.clone(), probed.clone()]),
        Formula::And(vec![Formula::Not(Box::new(guard)), Formula::Not(Box::new(probed))]),
    ]);
    let range = Formula::Or(
        variants
            .iter()
            .map(|v| Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(v.discriminant))))
            .collect(),
    );
    vec![semantics, range]
}

/// Trust (eq-guard channel): the std-spelled UNRESOLVED `PartialEq` trait
/// method — `Some(negated)`. Exact match, no turbofish (the unresolved trait
/// method's def-path carries none): the extractor keeps this spelling for
/// `Option`/`Result` receivers (`std_enum_partial_eq_keeps_name` pre-empts the
/// total-clone sentinel exactly for them), so the name arrives here for both
/// the concrete-total and the generic case. Anything else — including the
/// ambiguous `__trust_total_clone` sentinel, which also covers `lt`/`le`/
/// `gt`/`ge` — never matches (attaching equality semantics to the sentinel
/// would be UNSOUND: `o < None` is not `o == None`).
pub(super) fn std_partial_eq_callee(callee: &str) -> Option<bool> {
    match callee {
        "std::cmp::PartialEq::eq" | "core::cmp::PartialEq::eq" => Some(false),
        "std::cmp::PartialEq::ne" | "core::cmp::PartialEq::ne" => Some(true),
        _ => None,
    }
}

/// Trust (eq-guard channel): classify one `PartialEq::{eq,ne}` argument as the
/// RECEIVER side — byte-for-byte the probe receiver shape: a Copy/Move of a
/// bare local whose unique def is a SHARED borrow of a bare local, resolved
/// through the pinned/tag-transparent origin chain.
pub(super) fn eq_side_receiver(func: &VerifiableFunction, arg: &Operand) -> Option<usize> {
    let (Operand::Copy(place) | Operand::Move(place)) = arg else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    // SOUNDNESS (aliased reseat, audit r4): pin the eq receiver before trusting
    // its `&referent` def — a reseated receiver has a stale borrow def.
    if !unwrap_receiver_local_is_pinned(func, place.local) {
        return None;
    }
    let Some(Rvalue::Ref { mutable: false, place: referent }) =
        crate::unique_whole_local_def(func, place.local)
    else {
        return None;
    };
    if !referent.projections.is_empty() {
        return None;
    }
    unwrap_tag_origin(func, referent.local)
}

/// Trust (eq-guard channel): classify one `PartialEq::{eq,ne}` argument as the
/// PINNED PAYLOAD-LESS-VARIANT side — `(enum def-path, variant index)`. Three
/// recognized shapes, every one immutable by construction:
///   * the promoted literal (`o == None`): the argument IS the
///     [`trust_types::ConstValue::UnitVariantRef`] constant the extractor
///     recovers from the promoted `&Option<T>::None`;
///   * the const-copied local (`_4 = const promoted[0]`): a bare local whose
///     unique def is a `Use` of that constant;
///   * the let-bound construction (`let n = None; o == n` → `_5 = &n`): a bare
///     local whose unique def is a shared borrow of a PINNED bare local whose
///     unique def is a ZERO-OPERAND ADT aggregate (`ops.is_empty()` — the
///     payload-less gate; a `Some(x)` construction never matches).
pub(super) fn eq_side_pinned_unit(func: &VerifiableFunction, arg: &Operand) -> Option<(String, usize)> {
    if let Operand::Constant(trust_types::ConstValue::UnitVariantRef { enum_name, variant }) = arg {
        return Some((enum_name.clone(), *variant));
    }
    let (Operand::Copy(place) | Operand::Move(place)) = arg else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    // SOUNDNESS (aliased reseat, audit r4): pin `place` before trusting its
    // const/`&referent` def — a reseated unit-variant side would compare against
    // a DIFFERENT variant than the recorded one (false fact).
    if !unwrap_receiver_local_is_pinned(func, place.local) {
        return None;
    }
    match crate::unique_whole_local_def(func, place.local)? {
        Rvalue::Use(Operand::Constant(trust_types::ConstValue::UnitVariantRef {
            enum_name,
            variant,
        })) => Some((enum_name.clone(), *variant)),
        Rvalue::Ref { mutable: false, place: referent } if referent.projections.is_empty() => {
            if !unwrap_receiver_local_is_pinned(func, referent.local) {
                return None;
            }
            match crate::unique_whole_local_def(func, referent.local)? {
                Rvalue::Aggregate(
                    AggregateKind::Adt { name, variant, active_field: None, .. },
                    ops,
                ) if ops.is_empty() => Some((name.clone(), *variant)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Trust (eq-guard channel): the PATH-DEFINITION facts a modeled
/// `Option`/`Result` `PartialEq::{eq,ne}`-against-a-payload-less-variant call
/// establishes — for `_g = (o == None)`:
///   `(_g ∧ tag == UNIT_TAG) ∨ (¬_g ∧ tag ≠ UNIT_TAG)`    (polarity flipped for `ne`)
/// plus the variant-range fact over the SAME shared tag term, exactly the probe
/// channel's pair — so `if o == None { 0 } else { o.unwrap() }` PROVES and
/// `if o == None { o.unwrap() }` REFUTES.
///
/// SOUNDNESS: the callee is the unresolved std trait method and the receiver
/// TYPE is anchored to the std enum def-path; coherence (orphan rule — Option/
/// Result are foreign, non-fundamental) forbids any user impl, and core's impl
/// against a payload-less variant returns EXACTLY the discriminant test (the
/// `(Some, Some)` payload arm is unreachable, no user code runs). Payload-
/// carrying comparisons NEVER model: the pinned side requires a zero-operand
/// construction / unit-variant const AND `vd.fields.is_empty()` — `o == Some(x)`
/// and `o == p` fail closed (and keep the observer gate shut).
pub(super) fn eq_unit_call_definitions(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return Vec::new();
    };
    let Some(negated) = std_partial_eq_callee(callee) else {
        return Vec::new();
    };
    if !dest.projections.is_empty() || !is_single_static_assignment(func, dest.local) {
        return Vec::new();
    }
    if !crate::local_ty_ref(func, dest.local).is_some_and(|t| matches!(t, Ty::Bool)) {
        return Vec::new();
    }
    if args.len() != 2 {
        return Vec::new();
    }
    // Exactly one receiver + one pinned unit, either order.
    let classified = [(0usize, 1usize), (1, 0)].into_iter().find_map(|(r, u)| {
        let origin = eq_side_receiver(func, &args[r])?;
        let (enum_name, variant) = eq_side_pinned_unit(func, &args[u])?;
        Some((origin, enum_name, variant))
    });
    let Some((origin, unit_enum, variant)) = classified else {
        return Vec::new();
    };
    let Some(ty) = crate::local_ty_ref(func, origin) else {
        return Vec::new();
    };
    let Some((name, variants)) = modeled_std_enum_shape(ty) else {
        return Vec::new();
    };
    // Same std flavor on both sides (Option-vs-Option or Result-vs-Result).
    const OPTION_PATHS: [&str; 2] = ["core::option::Option", "std::option::Option"];
    const RESULT_PATHS: [&str; 2] = ["core::result::Result", "std::result::Result"];
    let same_flavor = (OPTION_PATHS.contains(&name) && OPTION_PATHS.contains(&unit_enum.as_str()))
        || (RESULT_PATHS.contains(&name) && RESULT_PATHS.contains(&unit_enum.as_str()));
    if !same_flavor {
        return Vec::new();
    }
    let Some(vd) = variants.get(variant) else {
        return Vec::new();
    };
    // The load-bearing payload-less gate: equality against a variant WITH a
    // payload is never a pure tag test.
    if !vd.fields.is_empty() {
        return Vec::new();
    }
    let unit_tag = vd.discriminant;
    let Some(tag) = receiver_tag_term_any(func, origin, variants) else {
        return Vec::new();
    };
    let guard = Formula::Var(place_to_var_name(func, dest), Sort::Bool);
    let probed = Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(unit_tag)));
    let (pos, neg) = if negated {
        (Formula::Not(Box::new(probed.clone())), probed)
    } else {
        (probed.clone(), Formula::Not(Box::new(probed)))
    };
    let semantics = Formula::Or(vec![
        Formula::And(vec![guard.clone(), pos]),
        Formula::And(vec![Formula::Not(Box::new(guard)), neg]),
    ]);
    let range = Formula::Or(
        variants
            .iter()
            .map(|v| Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(v.discriminant))))
            .collect(),
    );
    vec![semantics, range]
}

/// The SMT variable for a FIELD place's discriminant tag — the `__tag` field of
/// the flattened std enum at `(*base).field`, named via `place_to_var_name` so
/// the unwrap refutation and the guard's injected fact cite the SAME term.
/// Fail-closed when the layout carries no Int tag (niche/bool tag).
pub(super) fn field_tag_var(func: &VerifiableFunction, field_place: &Place) -> Option<Formula> {
    let explicit = crate::explicit_discriminant_field_for_place(func, field_place).ok()?;
    if !matches!(explicit.ty, Ty::Int { .. }) {
        return None;
    }
    Some(Formula::Var(place_to_var_name(func, &explicit.place), Sort::Int))
}

/// A field subject `(*base).field` has a FREE entry tag (⇒ refutable when
/// unguarded, pinnable by a guard) exactly when `base` is a pinned PARAMETER:
/// its pointee's field is initialized at entry and — via
/// [`unwrap_receiver_local_is_pinned`]'s `place_source_is_stable` (no rebind,
/// no `&mut`/`&raw mut`, no projected store) — cannot be reseated or mutated in
/// the body, so its tag is a single free value on every execution.
///
/// SOUNDNESS (raw-pointer / `&mut`-cast alias, audit r2): for a Deref-rooted
/// field (`(*base).f`) the pointee must be IMMUTABLE, i.e. `base` must be a
/// SHARED `&T`. A `&mut`/`*mut`/`*const` base admits a mutation alias the
/// syntactic pinning gate cannot see (`p = copy base; SetDiscriminant((*p).f)`
/// or `p = base as *mut _; …` sets `(*base).f` through a DIFFERENT local, so
/// `place_source_is_stable(base)` — which only inspects writes rooted at `base`
/// — still reports pinned). A by-value field (`base.f`, no Deref) carries no
/// such indirection: the field is part of the pinned value.
pub(super) fn field_subject_is_pinned(func: &VerifiableFunction, field_place: &Place) -> bool {
    let base = field_place.local;
    if !((1..=func.body.arg_count).contains(&base) && unwrap_receiver_local_is_pinned(func, base)) {
        return false;
    }
    if field_place.projections.first() == Some(&trust_types::Projection::Deref) {
        // Deref-rooted field: the base must be a shared reference so the pointee
        // (and thus the field) cannot be mutated through any pointer alias.
        matches!(crate::local_ty_ref(func, base), Some(Ty::Ref { mutable: false, .. }))
    } else {
        // By-value field of a pinned aggregate param — no indirection.
        true
    }
}

/// The SUBJECT place a field guard's receiver borrows: `self` inside a
/// `&self` helper is `*receiver`, so the caller subject is the reborrow's
/// referent (`_r = &(subj); is_ready(move _r)`) or, for a directly-passed
/// `&Struct` receiver, its deref (`*x`). Bare copy hops are followed.
/// Fail-closed (`None`) on a projected pred actual or a too-deep chain.
///
/// SOUNDNESS (aliased reseat, audit r3): EVERY hop local must be PINNED before
/// its `unique_whole_local_def` is trusted — exactly as [`unwrap_receiver_origin`]
/// does for the whole-pointee lane. Without it, a reference local reseated
/// through an ALIAS (`let mut r=o; mem::swap(&mut r, &mut r2); check(r)`) has a
/// stale `Use(Copy(o))` def (the `&mut r` write is invisible to
/// `unique_whole_local_def`), so the guard subject would mis-resolve to `*o`
/// while `r` points at `r2` at the call — threading the guard's fact onto the
/// WRONG subject and discharging a genuinely-panicking `o.slot.unwrap()` (a safe
/// -code FALSE PROVE). A `&mut`/alias-reseated `cur` fails `place_source_is_stable`.
pub(super) fn guard_receiver_subject(func: &VerifiableFunction, recv: &Place) -> Option<Place> {
    if !recv.projections.is_empty() {
        return None;
    }
    let mut cur = recv.local;
    for _ in 0..4 {
        if !unwrap_receiver_local_is_pinned(func, cur) {
            return None;
        }
        match crate::unique_whole_local_def(func, cur) {
            Some(Rvalue::Ref { mutable: false, place: referent }) => {
                return Some(referent.clone());
            }
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local != cur =>
            {
                cur = p.local;
            }
            // No reborrow def: `cur` is a directly-passed `&Struct` value — the
            // subject is its deref (`place_ty_cow` fails closed if not a ref).
            _ => {
                return Some(Place {
                    local: cur,
                    projections: vec![trust_types::Projection::Deref],
                });
            }
        }
    }
    None
}

/// Trust (inferred contract, call-site consumer): the guard-helper twin of
/// [`probe_call_definitions`] — for `_g = my_check(&o)` where `my_check` has an
/// INFERRED [`ReturnBoolPredSummary`], emit the probe-shaped fact pair
///   `(_g ∧ tag REL T) ∨ (¬_g ∧ ¬(tag REL T))`   +   `tag ∈ {variant tags}`
/// over the CALLER's shared tag term. Returns the resolved pred ORIGIN too, so
/// the observer gate can require origin equality (a future multi-arg
/// summarized call must not exempt an unrelated Option passed elsewhere).
///
/// SOUNDNESS: the summary was derived from the callee BODY by a fail-closed
/// whole-CFG proof over an entry-pinned shared-ref param (see
/// `function_return_bool_pred_summary`); the use-site cross-checks re-anchor
/// the enum (def-path + variant tags must MATCH the summary — never applied
/// across enums or instantiating layouts), and the receiver resolution is the
/// probe channel's own pinned borrow discipline.
pub(super) fn inferred_pred_call_model(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(InferredSubject, Vec<Formula>)> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return None;
    };
    let summary = crate::callee_return_bool_pred(callee)?;
    if !dest.projections.is_empty() || !is_single_static_assignment(func, dest.local) {
        return None;
    }
    if !crate::local_ty_ref(func, dest.local).is_some_and(|t| matches!(t, Ty::Bool)) {
        return None;
    }
    if args.len() != summary.params.len() {
        return None;
    }
    // The pred actual: a borrow temp / directly-passed shared ref.
    let arg = args.get(summary.pred_param.checked_sub(1)?)?;
    let (Operand::Copy(recv) | Operand::Move(recv)) = arg else {
        return None;
    };
    if !recv.projections.is_empty() {
        return None;
    }
    // Resolve the subject whose tag the contract constrains, and the tag term
    // over it — whole pointee (`&Enum` param) or a field (`&Struct` param,
    // `pred_field`). Both re-anchor the summary's enum at the use site.
    let (subject, tag, variant_tags) = match summary.pred_field {
        None => {
            // The guard actual is either a shared BORROW of the enum (`check(&o)`,
            // or `check(o)` where `o: &Enum` — recv resolves to `&(caller local)`)
            // or the enum passed BY VALUE (`check(o)` where `o: Enum` is Copy —
            // recv IS the caller's enum local). Resolve the pinned origin in both;
            // the enum cross-check below rejects any non-enum misresolution.
            // SOUNDNESS (aliased reseat, audit r4): the Ref arm may trust
            // `recv`'s `&referent` def ONLY when `recv` is PINNED — a reseated
            // `recv` (`let mut b=&o; let m=&mut b; *m=&o2`) has a stale `&o` def
            // while it points at `o2` at the call, so the fact would be minted
            // over the WRONG subject. An unpinned recv falls to the `_` arm,
            // whose `unwrap_tag_origin` pin-checks and returns None (fail-closed).
            let origin = match crate::unique_whole_local_def(func, recv.local) {
                Some(Rvalue::Ref { mutable: false, place: referent })
                    if referent.projections.is_empty()
                        && unwrap_receiver_local_is_pinned(func, recv.local) =>
                {
                    unwrap_tag_origin(func, referent.local)?
                }
                _ => unwrap_tag_origin(func, recv.local)?,
            };
            let ty = crate::local_ty_ref(func, origin)?;
            let (name, variants) = modeled_std_enum_shape(ty)?;
            if name != summary.enum_name {
                return None;
            }
            let variant_tags: Vec<i128> = variants.iter().map(|v| v.discriminant).collect();
            let tag = receiver_tag_term_any(func, origin, variants)?;
            (InferredSubject::Local(origin), tag, variant_tags)
        }
        Some(field_idx) => {
            let mut field_place = guard_receiver_subject(func, recv)?;
            field_place.projections.push(trust_types::Projection::Field(field_idx));
            if !field_subject_is_pinned(func, &field_place) {
                return None;
            }
            let field_ty = crate::place_ty_cow(func, &field_place)?;
            let (name, variants) = modeled_std_enum_shape(field_ty.as_ref())?;
            if name != summary.enum_name {
                return None;
            }
            let variant_tags: Vec<i128> = variants.iter().map(|v| v.discriminant).collect();
            let tag = field_tag_var(func, &field_place)?;
            (InferredSubject::Field(field_place), tag, variant_tags)
        }
    };
    if variant_tags != summary.variants || !variant_tags.contains(&summary.pred_tag) {
        return None;
    }
    let guard = Formula::Var(place_to_var_name(func, dest), Sort::Bool);
    let mut probed = Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(summary.pred_tag)));
    if !summary.pred_is_eq {
        probed = Formula::Not(Box::new(probed));
    }
    // Emit the fact at the summary's STRENGTH:
    //   Iff         `(g ∧ probed) ∨ (¬g ∧ ¬probed)`  — proves + refutes both guards
    //   ImpliesTrue `g ⇒ probed`  = `¬g ∨ probed`     — proves `if g {unwrap}`, ¬g inconclusive
    //   ImpliesFalse`¬g ⇒ probed` = `g ∨ probed`      — proves `if g {} else {unwrap}`
    // The weaker forms are SOUND: they assert strictly less than the iff, so a
    // wrong-polarity guard simply stays fail-closed (never a spurious discharge).
    let not_g = Formula::Not(Box::new(guard.clone()));
    let semantics = match summary.kind {
        ReturnBoolPredKind::Iff => Formula::Or(vec![
            Formula::And(vec![guard.clone(), probed.clone()]),
            Formula::And(vec![not_g, Formula::Not(Box::new(probed.clone()))]),
        ]),
        ReturnBoolPredKind::ImpliesTrue => Formula::Or(vec![not_g, probed.clone()]),
        ReturnBoolPredKind::ImpliesFalse => Formula::Or(vec![guard.clone(), probed.clone()]),
    };
    let range = Formula::Or(
        variant_tags
            .iter()
            .map(|t| Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(*t))))
            .collect(),
    );
    Some((subject, vec![semantics, range]))
}

/// The path-definition facts of a modeled guard-helper call (empty when the
/// model does not fire).
pub(super) fn inferred_pred_call_definitions(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    inferred_pred_call_model(func, block).map(|(_, facts)| facts).unwrap_or_default()
}

/// Observer-gate connectedness for a WHOLE-pointee guard-helper call: fires-only
/// AND origin-equal (see [`inferred_pred_call_model`]).
pub(super) fn inferred_pred_call_connects(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    origin: usize,
) -> bool {
    matches!(
        inferred_pred_call_model(func, block),
        Some((InferredSubject::Local(o), _)) if o == origin
    )
}

/// Observer-gate connectedness for a FIELD guard-helper call: fires-only AND
/// field-place-equal, so `if x.is_ready() { x.slot.unwrap() }` connects only to
/// the `x.slot` unwrap and never an unrelated field or Option.
pub(super) fn inferred_pred_call_connects_field(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    field_place: &Place,
) -> bool {
    matches!(
        inferred_pred_call_model(func, block),
        Some((InferredSubject::Field(fp), _)) if &fp == field_place
    )
}

/// Trust (unwrap/probe shared tag term): the ONE variable both the unwrap
/// refutation body and the probe result semantics cite for a pinned receiver —
/// the recognized pinning shapes first ([`unwrap_receiver_tag_term`]:
/// construction- or read-pinned), else the FREE entry-tag field of a pinned
/// PARAMETER ([`receiver_entry_tag_var`]). Sharing this term is the proof
/// mechanism: the probe fact links the guard bool to the tag, the path guard
/// pins the bool, and the unwrap body tests the same tag ⇒ UNSAT ⇒ PROVED.
pub(super) fn receiver_tag_term_any(
    func: &VerifiableFunction,
    origin: usize,
    variants: &[trust_types::VariantDef],
) -> Option<Formula> {
    unwrap_receiver_tag_term(func, origin, variants).or_else(|| {
        if (1..=func.body.arg_count).contains(&origin) {
            receiver_entry_tag_var(func, origin)
        } else {
            None
        }
    })
}

/// The receiver local's discriminant TAG cannot change after initialization:
/// [`crate::place_source_is_stable`] (at most one whole-local store, no projected
/// store, no `&mut`/`&raw mut` borrow, no `SetDiscriminant`/`Deinit`, no
/// projected call-dest) PLUS the parameter refinement — a PARAMETER is
/// initialized at entry WITHOUT any `Assign`, so a `mut` param with one body
/// store has TWO values and must NOT count as pinned (`place_source_is_stable`
/// alone would admit it).
pub(super) fn unwrap_receiver_local_is_pinned(func: &VerifiableFunction, local: usize) -> bool {
    if !crate::place_source_is_stable(func, local) {
        return false;
    }
    let is_param = (1..=func.body.arg_count).contains(&local);
    !(is_param && guards::whole_local_def_count(func, local) > 0)
}

/// Follow value-preserving whole-local move/copy hops (`_5 = move _2`, the
/// compiler-inserted receiver temp) from the unwrap receiver back to its ORIGIN
/// local. Every hop local AND the origin must be pinned (see above), so the
/// receiver's tag at the call IS the origin's tag on every execution. `None`
/// (fail-closed) on any unpinned link or a cyclic/deep chain.
pub(super) fn unwrap_receiver_origin(func: &VerifiableFunction, local: usize) -> Option<usize> {
    let mut cur = local;
    for _ in 0..8 {
        if !unwrap_receiver_local_is_pinned(func, cur) {
            return None;
        }
        match crate::unique_whole_local_def(func, cur) {
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local != cur =>
            {
                cur = p.local;
            }
            _ => return Some(cur),
        }
    }
    None
}

/// `src` — the operand place of a `Discriminant` read — denotes the pinned
/// origin's value: the origin local itself (bare), or a deref of a single-def
/// SHARED borrow of it (`_b = &_r; _d = discriminant(*_b)`, the `is_ok`-inlined
/// shape). A shared borrow cannot mutate its referent, and the pinned-origin
/// gates already exclude any `&mut`/raw alias of the origin.
pub(super) fn discriminant_src_is_pinned_origin(
    func: &VerifiableFunction,
    src: &Place,
    origin: usize,
) -> bool {
    if src.local == origin && src.projections.is_empty() {
        return true;
    }
    // SOUNDNESS (aliased reseat, audit r5): use the PARAM-refined pin (not raw
    // `place_source_is_stable`) — a reference PARAMETER reseated once in the body
    // (`_3 = &a` on one branch) is "stable" by the raw check but its `*_3` at the
    // read denotes the ENTRY pointee on the other branch, not `a`. The legit
    // compiler-temp shape (`_b = &origin; discr(*_b)`) has `_b` a non-param, so
    // the wrapper is identical there and nothing regresses.
    matches!(src.projections.as_slice(), [trust_types::Projection::Deref])
        && unwrap_receiver_local_is_pinned(func, src.local)
        && matches!(
            crate::unique_whole_local_def(func, src.local),
            Some(Rvalue::Ref { mutable: false, place })
                if place.local == origin && place.projections.is_empty()
        )
}

/// The SMT term denoting the pinned receiver's discriminant tag at the call.
/// Two recognized pinning shapes, mirroring the ny-cert instances:
///   (b) CONSTRUCTION-pinned: the origin's unique whole-local def is an ADT
///       aggregate (`let x = Ok(v); … x.unwrap()`). The tag is the GROUND
///       constant of that variant — identical on EVERY execution of the single
///       def (loops included: re-executing `x = Ok(v)` never changes the tag),
///       so the term is exact, not merely path-pinned.
///   (a) READ-pinned: a discriminant read `_d = Discriminant(origin)` (directly
///       or through a single-def shared borrow) whose dest `_d` is a bare,
///       non-parameter, pinned local with EXACTLY that read as its one
///       definition. The term is `_d`'s variable: a dominating `match`/`if`
///       switch guard pins it (`_d == OK_TAG`) on every guarded path, and the
///       S2c version machinery keeps a multi-write `_d` name-disjoint
///       (fail-closed) instead of stale.
/// `None` (fail-closed) when neither shape applies.
pub(super) fn unwrap_receiver_tag_term(
    func: &VerifiableFunction,
    origin: usize,
    variants: &[trust_types::VariantDef],
) -> Option<Formula> {
    if let Some(Rvalue::Aggregate(kind, _)) = crate::unique_whole_local_def(func, origin)
        && let AggregateKind::Adt { variant, active_field: None, .. } = kind
    {
        let tag = variants.get(*variant)?.discriminant;
        return Some(Formula::Int(tag));
    }
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
            else {
                continue;
            };
            if !dest.projections.is_empty() || !discriminant_src_is_pinned_origin(func, src, origin)
            {
                continue;
            }
            // `_d` itself must be single-valued: a bare non-param local whose ONE
            // whole-local definition is exactly this read (a second write would
            // leave the term stale vs. the tag; `unique_whole_local_def` returns
            // `None` on any second def, so the `Discriminant` match below implies
            // THIS statement is the sole def).
            if (1..=func.body.arg_count).contains(&dest.local)
                || !crate::place_source_is_stable(func, dest.local)
                || !matches!(
                    crate::unique_whole_local_def(func, dest.local),
                    Some(Rvalue::Discriminant(_))
                )
            {
                continue;
            }
            return Some(Formula::Var(place_to_var_name(func, dest), Sort::Int));
        }
    }
    None
}

/// Trust (unwrap panic-freedom, dominated-safe): the SOLVABLE refutation body
/// for a std `Option`/`Result` `unwrap`-family call whose receiver's
/// discriminant is PINNED by real dataflow — `receiver_tag == PANIC_TAG` in the
/// same "SAT ⇒ violation / UNSAT ⇒ proved" convention as the UnboundedAllocation
/// lane. `None` (⇒ keep the fail-closed `Call::…::panic-freedom-unverified`
/// UnsupportedMir row) for EVERY case outside the recognized shape:
///   * a non-std callee path (user extension-trait `unwrap`),
///   * a projected / non-place receiver,
///   * a receiver type that is not the MODELED flattened std enum from
///     `lower_enum_adt` (std def-path name + explicit `__tag` slot + both
///     variant defs with their real discriminant tags),
///   * an unpinned receiver (reassigned, `&mut`-borrowed, `SetDiscriminant`,
///     projected store, `mut` parameter with a body store),
///   * no recognizable tag pinning (neither construction- nor read-pinned).
/// SOUNDNESS: the body may only UNDER-constrain (a free tag var is trivially
/// SAT ⇒ the row FAILS closed); the conjoined context (block defs, path guards,
/// preconditions, discriminant range facts) consists exclusively of the same
/// unconditionally-true facts every other v2 lane threads.
pub(crate) fn unwrap_panic_freedom_body(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> Option<Formula> {
    let (enum_paths, variant_names, panic_variant) = std_unwrap_family_panic_variant(callee)?;
    let (Operand::Copy(recv) | Operand::Move(recv)) = args.first()? else {
        return None;
    };
    // Whole-LOCAL receiver first (the bare-enum-local shapes a–d); then the
    // FIELD receiver path (`x.slot.unwrap()`), which the whole-local path
    // fails closed on.
    unwrap_whole_local_tag_refutation(func, recv, enum_paths, variant_names, panic_variant)
        .or_else(|| unwrap_field_tag_refutation(func, recv, enum_paths, panic_variant))
}

/// Whole-LOCAL receiver refutation (shapes a–d): the receiver is a bare enum
/// local. Fail-closed on a projected/field receiver — see
/// [`unwrap_field_tag_refutation`].
pub(super) fn unwrap_whole_local_tag_refutation(
    func: &VerifiableFunction,
    recv: &Place,
    enum_paths: &'static [&'static str],
    variant_names: &'static [&'static str],
    panic_variant: &'static str,
) -> Option<Formula> {
    // Receiver: a bare local. Projections are not traced — fail closed.
    if !recv.projections.is_empty() {
        return None;
    }
    // Receiver type: the MODELED flattened std enum (`lower_enum_adt` shape —
    // the shared `modeled_std_enum_shape` gate), additionally anchored to the
    // callee flavor's def-paths (an Option method never models a Result
    // receiver and vice versa).
    let ty = crate::local_ty_ref(func, recv.local)?;
    let (name, variants) = modeled_std_enum_shape(ty)?;
    debug_assert!(variant_names.iter().all(|v| variants.iter().any(|vd| vd.name == *v)));
    if !enum_paths.contains(&name) {
        return None;
    }
    let panic_tag = variants.iter().find(|vd| vd.name == panic_variant)?.discriminant;
    // Tag-transparent: `o.as_ref().unwrap()` unwraps the as_ref RESULT, whose
    // discriminant equals `o`'s — resolve through the hop so the obligation
    // tests the guard-connected origin tag.
    let origin = unwrap_tag_origin(func, recv.local)?;
    if let Some(tag_term) = unwrap_receiver_tag_term(func, origin, variants) {
        return Some(Formula::Eq(Box::new(tag_term), Box::new(Formula::Int(panic_tag))));
    }
    // (c) SUMMARY-pinned: the pinned origin's unique def is a Call to a LOCAL
    // callee with a return-discriminant summary (`compute_return_disc_summaries`,
    // threaded per crate like the const-return bounds). The refutation body
    // becomes `tag_expr(actual args) == PANIC_TAG` — ground for constant
    // arguments (`Rat::new(1, 2).unwrap()` proves outright); for pinned
    // symbolic arguments the VC keeps the caller's context, so a dominating
    // `if d != 0` guard proves it and an unguarded call stays SAT (failed).
    // (Falls through on any miss so shape (d) below can still fire.)
    if let Some((call_callee, call_args)) = unwrap_origin_call_def(func, origin)
        && let Some(summary) = crate::callee_return_disc_summary(call_callee)
        && summary.enum_name == name
        && let Some(tag_expr) = return_disc_tag_expr(func, &summary, call_args)
    {
        return Some(Formula::Eq(Box::new(tag_expr), Box::new(Formula::Int(panic_tag))));
    }
    // (d) PARAM-pinned fallback: the origin is a pinned PARAMETER (a `mut` param
    // with a body store was already rejected by `unwrap_receiver_local_is_pinned`
    // inside `unwrap_receiver_origin`), and the body contains NO other channel
    // that could observe its tag (`origin_tag_observed_elsewhere` — a
    // discriminant read, a copy that is matched on, or ANY call receiving the
    // origin / a borrow of it, all of which could dominate the unwrap with a
    // guard this lane cannot see). With no observer, the tag is a FREE entry
    // value: SAT with model `tag == PANIC_TAG` is a GENUINE `None`/`Err`
    // argument reaching the unwrap — a real refutation with a real witness, not
    // a coverage gap. This is what turns the bare `f(o: Option<u32>) ->
    // { o.unwrap() }` from a fail-closed UNKNOWN into FAILED(o = None).
    // SOUNDNESS: under-constraining only (a free tag is trivially SAT ⇒ fails
    // closed); the observer gate exists for PRECISION (never mint a spurious
    // ground counterexample on a guarded-but-unrecognized shape — those keep
    // today's fail-closed UnsupportedMir row).
    if (1..=func.body.arg_count).contains(&origin) && !origin_tag_observed_elsewhere(func, origin) {
        let tag_var = receiver_entry_tag_var(func, origin)?;
        return Some(Formula::Eq(Box::new(tag_var), Box::new(Formula::Int(panic_tag))));
    }
    None
}

/// FIELD receiver refutation: `x.slot.unwrap()` where `slot` is a modeled-enum
/// field of a PINNED param base. Mints the tag term over the field place — the
/// SAME var an inferred field-guard contract (`if x.is_ready() { … }`,
/// `pred_field`) cites — so a dominating field guard proves the unwrap and an
/// unguarded field unwrap refutes with a field-`None`/`Err` witness. The field
/// path is the exact analogue of the whole-local shape (d): free entry tag,
/// fires-only observer gate. Fail-closed on any deviation.
pub(super) fn unwrap_field_tag_refutation(
    func: &VerifiableFunction,
    recv: &Place,
    enum_paths: &'static [&'static str],
    panic_variant: &'static str,
) -> Option<Formula> {
    let field_place = unwrap_field_place(func, recv)?;
    if !field_subject_is_pinned(func, &field_place) {
        return None;
    }
    let field_ty = crate::place_ty_cow(func, &field_place)?;
    let (name, variants) = modeled_std_enum_shape(field_ty.as_ref())?;
    if !enum_paths.contains(&name) {
        return None;
    }
    let panic_tag = variants.iter().find(|vd| vd.name == panic_variant)?.discriminant;
    let tag_var = field_tag_var(func, &field_place)?;
    // Fires-only: with NO OPAQUE observer of the field the tag is a free entry
    // value ⇒ refute. A CONNECTED field guard is exempt (shape (d) still fires,
    // and its threaded fact discharges the obligation).
    if field_tag_observed_elsewhere(func, &field_place) {
        return None;
    }
    Some(Formula::Eq(Box::new(tag_var), Box::new(Formula::Int(panic_tag))))
}

/// The FIELD place an unwrap receiver consumes: the receiver is the projected
/// field operand directly (`recv` = `(*base).field`), or a bare temp whose
/// unique def copies from such a field place. Restricted to a SIMPLE field of
/// the param pointee — `[Field]` (by-value base) or `[Deref, Field]` (`&Struct`
/// base) — so the base local is exactly `field_place.local` and its stability
/// is decidable. Fail-closed otherwise.
pub(super) fn unwrap_field_place(func: &VerifiableFunction, recv: &Place) -> Option<Place> {
    fn is_simple_field(projs: &[trust_types::Projection]) -> bool {
        matches!(
            projs,
            [trust_types::Projection::Field(_)]
                | [trust_types::Projection::Deref, trust_types::Projection::Field(_)]
        )
    }
    if is_simple_field(&recv.projections) {
        return Some(recv.clone());
    }
    // Bare temp copied from a field place. SOUNDNESS (aliased reseat, audit r3):
    // the temp must be PINNED before its copy def is trusted — a `&mut`-reseated
    // temp (`_t = copy((*x).f); m = &mut _t; *m = None; _t.unwrap()`) has a stale
    // `Use(Copy((*x).f))` def while the unwrap operates on the mutated value, so
    // a guard on `(*x).f` would falsely discharge it. Fail-closed on an unpinned
    // temp (mirrors `guard_receiver_subject` / `unwrap_receiver_origin`).
    if recv.projections.is_empty()
        && unwrap_receiver_local_is_pinned(func, recv.local)
        && let Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p))) =
            crate::unique_whole_local_def(func, recv.local)
        && is_simple_field(&p.projections)
    {
        return Some(p.clone());
    }
    None
}

/// FIELD observer gate (the whole-local [`origin_tag_observed_elsewhere`]
/// analogue): does the body contain an OPAQUE channel through which the field's
/// discriminant could be observed and guarded — a `Discriminant` read touching
/// the base, or ANY non-unwrap call receiving the base struct / a borrow or
/// copy of it (all of which could read the field and dominate the unwrap with a
/// guard this lane cannot see)? A CONNECTED field guard
/// ([`inferred_pred_call_connects_field`]) is exempt. Conservative (broad) so a
/// missed observer can only SUPPRESS a refutation (fail-closed), never mint a
/// spurious one.
pub(super) fn field_tag_observed_elsewhere(func: &VerifiableFunction, field_place: &Place) -> bool {
    let base = field_place.local;
    let touches_base = |place: &Place| -> bool {
        if place.local == base {
            return true;
        }
        // A borrow whose referent roots at the base.
        if let Some(Rvalue::Ref { place: r, .. }) = crate::unique_whole_local_def(func, place.local)
            && (r.local == base || unwrap_receiver_origin(func, r.local) == Some(base))
        {
            return true;
        }
        // A MULTI-HOP copy/move alias of the base — matches the whole-local
        // twin's `unwrap_tag_origin` reach (a one-hop check would let a 2-hop
        // `_a = copy base; _b = copy _a; observe(_b)` slip past the gate and
        // spuriously refute a possibly-guarded field unwrap).
        unwrap_receiver_origin(func, place.local) == Some(base)
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::Discriminant(src), .. } = stmt
                && touches_base(src)
            {
                return true;
            }
        }
        if let Terminator::Call { func: callee, args, .. } = &block.terminator
            && std_unwrap_family_panic_variant(callee).is_none()
            && !inferred_pred_call_connects_field(func, block, field_place)
        {
            for arg in args {
                let (Operand::Copy(place) | Operand::Move(place)) = arg else {
                    continue;
                };
                if touches_base(place) {
                    return true;
                }
            }
        }
    }
    false
}

/// Trust (unwrap panic-freedom, shape (d)): the SMT variable denoting a pinned
/// PARAMETER receiver's discriminant tag at function entry — the explicit
/// `__tag`/`discriminant` field of the flattened std-enum layout, named exactly
/// as `set_discriminant_definitions` / the aggregate-field lane write it, so a
/// (rare) explicit tag consumer cites the same term. Fail-closed (`None`) when
/// the layout carries no Int tag field (e.g. a bool-tag or niche layout).
pub(super) fn receiver_entry_tag_var(func: &VerifiableFunction, origin: usize) -> Option<Formula> {
    let bare = Place { local: origin, projections: Vec::new() };
    let explicit = crate::explicit_discriminant_field_for_place(func, &bare).ok()?;
    if !matches!(explicit.ty, Ty::Int { .. }) {
        return None;
    }
    Some(Formula::Var(place_to_var_name(func, &explicit.place), Sort::Int))
}

/// Trust (unwrap panic-freedom, shape (d) observer gate): does the body contain
/// ANY channel other than the unwrap-family calls themselves through which the
/// pinned parameter `origin`'s discriminant could be observed — and therefore a
/// guard this lane cannot connect to the free entry-tag variable?
///   * a `Discriminant` read of the origin (direct, through a single-def shared
///     borrow, or of a pinned COPY of the origin — `let c = o; match c { … }`);
///   * ANY call receiving the origin, a shared borrow of it, or a pinned copy
///     of it as an argument (an `is_some`-style probe, a `PartialEq` against
///     `None`, an `as_ref` chain, a user helper — all could return tag
///     information that dominates the unwrap).
/// `true` ⇒ the caller keeps today's fail-closed UnsupportedMir row instead of
/// minting a possibly-spurious refutation. Unwrap-family calls are exempt: they
/// CONSUME the tag (their own VCs refute or prove per-site) and never produce a
/// guard value.
pub(super) fn origin_tag_observed_elsewhere(func: &VerifiableFunction, origin: usize) -> bool {
    let is_origin_alias = |place: &Place| -> bool {
        if !place.projections.is_empty() {
            return false;
        }
        if place.local == origin {
            return true;
        }
        // A pinned copy of the origin (`let c = o;`), a tag-transparent
        // `as_ref` RESULT of it, or a single-def shared borrow of it (or of a
        // tag-transparent-connected local — `_e = &(o.as_ref())`) — all carry
        // the same tag onward, so an unmodeled consumer of any of them is an
        // opaque guard channel. Following the referent through `unwrap_tag_origin`
        // closes the as_ref-then-shared-borrow leak (a borrow of the as_ref
        // RESULT is a real observer the literal `referent.local == origin` check
        // missed).
        unwrap_tag_origin(func, place.local) == Some(origin)
            || matches!(
                crate::unique_whole_local_def(func, place.local),
                Some(Rvalue::Ref { mutable: false, place: referent })
                    if referent.projections.is_empty()
                        && (referent.local == origin
                            || unwrap_tag_origin(func, referent.local) == Some(origin))
            )
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::Discriminant(src), .. } = stmt
                && (discriminant_src_is_pinned_origin(func, src, origin) || is_origin_alias(src))
            {
                return true;
            }
        }
        if let Terminator::Call { func: callee, args, .. } = &block.terminator
            && std_unwrap_family_panic_variant(callee).is_none()
            // A tag-transparent `as_ref` whose result CONNECTS back to this
            // origin (`unwrap_tag_origin(dest) == origin` — the exact hop the
            // probe/unwrap models resolve) is a CONNECTED observer, not an
            // opaque one: every downstream consumer of its result is itself
            // alias-tracked by `is_origin_alias`, so a dangerous consumer still
            // trips this gate. An as_ref whose hop does NOT connect (e.g. a
            // reassigned dest) stays an opaque observer — fires-only, never a
            // blanket name exemption (a blanket exemption would let shape (d)
            // mint a spurious refutation for a guarded-but-unconnected chain).
            && !as_ref_hop_connected(func, block, origin)
            // A MODELED probe call (`is_some`-family whose result semantics
            // `probe_call_definitions` records over the SHARED tag term) is a
            // CONNECTED observer, not an opaque one: its guard constrains the
            // same free entry-tag variable shape (d) cites, so a dominating
            // `if o.is_some()` proves the unwrap and an unguarded one still
            // refutes. An UNmodeled probe (failed gates) stays an opaque
            // observer and keeps the fail-closed row.
            && probe_call_definitions(func, block).is_empty()
            // Same fires-only contract for a MODELED `o == None` / `o != None`
            // equality guard; `o == Some(x)` / `o == p` never model and stay
            // opaque observers.
            && eq_unit_call_definitions(func, block).is_empty()
            // And for a guard-helper call with an INFERRED contract — fires-only
            // AND origin-equal, so a summarized call constraining THIS origin's
            // tag is connected, while the same callee taking an unrelated
            // Option (or failing any gate) stays an opaque observer.
            && !inferred_pred_call_connects(func, block, origin)
        {
            for arg in args {
                let (Operand::Copy(place) | Operand::Move(place)) = arg else {
                    continue;
                };
                if is_origin_alias(place) {
                    return true;
                }
            }
        }
    }
    false
}

/// The unique `Call` that defines the PINNED unwrap-receiver origin (bare
/// dest, normally returning). Pinnedness (`unwrap_receiver_origin`'s
/// `place_source_is_stable` chain) already guarantees AT MOST one whole-local
/// store of the origin across statements AND call dests, so the first match is
/// THE defining call on every execution that reaches the unwrap.
pub(super) fn unwrap_origin_call_def<'a>(
    func: &'a VerifiableFunction,
    origin: usize,
) -> Option<(&'a str, &'a [Operand])> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, target: Some(_), .. } =
            &block.terminator
            && dest.local == origin
            && dest.projections.is_empty()
        {
            return Some((callee.as_str(), args));
        }
    }
    None
}

/// Trust (return-discriminant summary, use site): the summarized callee's
/// returned TAG as a term over THIS call's actual arguments.
///   * Unconditional: the ground variant tag (argument-independent).
///   * Guard-conditioned: `ite(cond[formals := actuals], then_tag, else_tag)`,
///     via the capture-avoiding [`substitute_summary_params`]. Every actual
///     must itself resolve through [`entry_stable_operand_formula`] (a
///     constant, or a pinned caller parameter/const-defined local): the
///     substituted term must still denote the CALL-TIME argument value at the
///     downstream unwrap block, and a reassignable actual could go stale in
///     between (the S2c class) — refused, fail-closed. Arity and
///     free-vars ⊆ formals are re-checked so a malformed summary can never
///     leave an unbound callee symbol to capture a caller local.
pub(super) fn return_disc_tag_expr(
    func: &VerifiableFunction,
    summary: &ReturnDiscSummary,
    args: &[Operand],
) -> Option<Formula> {
    match &summary.cases {
        ReturnDiscCases::Unconditional { tag } => Some(Formula::Int(*tag)),
        ReturnDiscCases::GuardConditioned { cond, then_tag, else_tag } => {
            if summary.params.len() != args.len()
                || !cond.free_variables().iter().all(|v| summary.params.iter().any(|p| p == v))
            {
                return None;
            }
            let mut replacements: Vec<(String, Formula)> = Vec::with_capacity(args.len());
            for (formal, actual) in summary.params.iter().zip(args) {
                replacements.push((formal.clone(), entry_stable_operand_formula(func, actual)?));
            }
            let cond = substitute_summary_params(cond, &replacements);
            Some(Formula::Ite(
                Box::new(cond),
                Box::new(Formula::Int(*then_tag)),
                Box::new(Formula::Int(*else_tag)),
            ))
        }
    }
}

/// Shared bridge for [`collect_terminator_unsupported`] and the dominated-success
/// recognizer, so every known-panicking call keeps exactly one obligation.
pub(super) fn unwrap_panic_freedom_modeled(func: &VerifiableFunction, callee: &str, args: &[Operand]) -> bool {
    unwrap_panic_freedom_body(func, callee, args).is_some()
}

/// Trust (unwrap panic-freedom, dominated-safe): one solvable VC per recognized
/// `unwrap`/`expect` call, replacing that call's fail-closed
/// `Call::…::panic-freedom-unverified` UnsupportedMir row (the suppression in
/// [`collect_terminator_unsupported`] keys on the SAME
/// [`unwrap_panic_freedom_body`] recognizer, so the two can never drift — every
/// call gets exactly one of {solvable VC, UnsupportedMir row}).
///
/// The body `receiver_tag == PANIC_TAG` is conjoined with the SAME discharge
/// context the UnboundedAllocation lane assembles — same-block defs, live
/// path-definition facts, arg/local/datatype type ranges, versioned
/// preconditions, dominating path guards (S2c-exempt), assert-passed semantic
/// guards, global invariant facts (which carry the discriminant variant-range
/// and CSE facts), and the final SSA version-token collapse. Verdict
/// convention: SAT ⇒ the panic variant's tag is reachable at the call ⇒ the row
/// stays failed; UNSAT ⇒ the discriminant is pinned to the success variant on
/// every path ⇒ panic-freedom PROVED.
pub(super) fn unwrap_panic_freedom_vcs_with_blocks(
    func: &VerifiableFunction,
) -> Vec<(BlockId, VerificationCondition)> {
    let mut sites: Vec<(&trust_types::BasicBlock, &str, &SourceSpan, Formula, Option<VcKind>)> =
        Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, target, span, .. } = &block.terminator
        else {
            continue;
        };
        // A normally-returning known-panicking std call. Two independent sources:
        //   * Option/Result unwrap-family (`is_known_panicking_method`), unless the
        //     slice->array recognizer already proved it infallible (row suppressed);
        //   * signed `iN::abs` (`is_signed_abs_call`) — panics at `iN::MIN`, never
        //     flagged by the UnsupportedMir arm, so it is added ONLY here (no
        //     double-flag). Both flow through the SAME guard-aware assembly below,
        //     so a dominating guard proves the obligation and an unguarded call
        //     stays refutable.
        if target.is_none() {
            continue;
        }
        // `(body, kind_override)`: abs carries an explicit `NegationOverflow { ty }`
        // kind (routes like `-x`, BV-capable discharge); unwrap uses the default
        // `Assertion` panic-freedom kind computed at the tail (`None`).
        let (body, kind_override): (Option<Formula>, Option<VcKind>) = if is_signed_abs_call(callee)
        {
            match signed_abs_panic_body(func, args) {
                Some((body, ty)) => (Some(body), Some(VcKind::NegationOverflow { ty })),
                None => (None, None),
            }
        } else if is_known_panicking_method(callee)
                && !unwrap_is_infallible_slice_to_array(func, callee, args, dest)
                // Trust (countdown-loop piece, B0): const-int conversion `expect`s
                // that provably succeed carry no panic path — no VC (see the
                // UnsupportedMir twin's suppression for the rationale).
                && expect_infallible_const_int_conversion(func, callee, args, dest).is_none()
        {
            (unwrap_panic_freedom_body(func, callee, args), None)
        } else {
            (None, None)
        };
        let Some(body) = body else {
            continue;
        };
        sites.push((block, callee, span, body, kind_override));
    }
    if sites.is_empty() {
        return Vec::new();
    }
    let guard_paths_map = v2_build_path_guard_map(func);
    let semantic_guards = build_semantic_guard_map(func);
    let may_reassigned = v2_may_reassigned_per_block(func);
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = StmtVersionCtx::build(func);
    let path_definition_map = v2_build_path_definition_map(func);
    let global_facts = build_global_invariant_facts(func);
    let empty = FxHashSet::default();
    let mut vcs = Vec::new();
    for (block, callee, span, body, kind_override) in sites {
        let mut formula = v2_formula_with_block_defs(func, block, body);
        // Live path-definition facts (the safety-lane channel): predecessor
        // definitions that made the path reachable (e.g. the bool `is_ok` temp).
        if let Some(path_defs) = path_definition_map.get(&block.id)
            && !path_defs.is_empty()
        {
            let live = v2_live_path_defs(func, block, path_defs);
            if !live.is_empty() {
                let mut conjuncts = live;
                conjuncts.push(formula);
                formula = Formula::And(conjuncts);
            }
        }
        formula = conjoin_arg_type_ranges(func, formula);
        formula = conjoin_local_type_ranges(func, formula);
        formula = conjoin_datatype_field_ranges(func, formula);
        // Trust S2c: whole-VC version rename FIRST; the threaded facts below
        // (path guards, semantic guards, global facts) are conjoined AFTER,
        // EXEMPT from the rename — same discipline as the allocation lane.
        let killed = may_reassigned.get(&block.id).unwrap_or(&empty);
        formula =
            conjoin_preconditions_versioned(func, block.id, &func.preconditions, killed, formula);
        if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
            formula = v2_formula_with_path_guards(func, &sv, block_guard_paths, formula);
        }
        if let Some(sem_guards) = semantic_guards.get(&block.id)
            && !sem_guards.is_empty()
        {
            let mut conjuncts = sem_guards.clone();
            conjuncts.push(formula);
            formula = Formula::And(conjuncts);
        }
        // Function-wide invariant facts — notably the discriminant variant-range
        // fact `d ∈ {variant tags}` (a true type invariant: it deletes phantom-tag
        // counterexamples but can never exclude the real panic tag, which is a
        // member of the set — the refutation stays reachable).
        if !global_facts.is_empty() {
            let mut conjuncts = global_facts.clone();
            conjuncts.push(formula);
            formula = Formula::And(conjuncts);
        }
        formula = normalize_ssa_version_tokens(func, &formula);
        let m = method_tail(callee);
        let kind = kind_override
            .unwrap_or_else(|| VcKind::Assertion { message: format!("Call::{m}::panic-freedom") });
        vcs.push((
            block.id,
            VerificationCondition {
                kind,
                function: func.name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            },
        ));
    }
    vcs
}

pub(super) fn generate_unwrap_panic_freedom_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    unwrap_panic_freedom_vcs_with_blocks(func).into_iter().map(|(_, vc)| vc).collect()
}

/// Trust (hardened PanicBoundary twin consistency): the fully-assembled
/// panic-freedom refutation formula for the `unwrap`/`expect` call at block
/// `ordinal`, or `None` when the call is not a recognized pinned shape. The
/// hardened lane swaps its fail-closed `Bool(true)` PanicBoundary twin for this
/// formula so BOTH rows keyed to the same call are decided by the SAME solvable
/// obligation (UNSAT ⇒ both prove; SAT ⇒ both stay failed) instead of the twin
/// wedging at Unknown after the primary row proves.
pub(crate) fn unwrap_panic_freedom_formula_at_block(
    func: &VerifiableFunction,
    ordinal: usize,
) -> Option<Formula> {
    unwrap_panic_freedom_vcs_with_blocks(func)
        .into_iter()
        .find(|(id, _)| id.0 == ordinal)
        .map(|(_, vc)| vc.formula)
}

/// Trust (Problem B): recognize the INFALLIBLE `Result::unwrap` whose receiver is
/// the success-by-construction of a slice -> ARRAY `TryInto`/`TryFrom` conversion
/// on a slice of STATICALLY-KNOWN length `N` equal to the target array length `N`.
/// The standard-library impl `<&[T] as TryFrom<&[T; N]>>` (and the `TryInto`
/// mirror) returns `Ok` IFF `slice.len() == N`; when the slice length is
/// statically `N`, the conversion CANNOT return `Err`, so the `unwrap` CANNOT
/// panic. Returning `true` SUPPRESSES the `Call::unwrap::panic-freedom-unverified`
/// UnsupportedMir obligation for exactly these provably-infallible unwraps.
///
/// SOUNDNESS — the suppression is sound ONLY because every gate below is a HARD
/// requirement; ANY ambiguity returns `false` (keep the obligation as Unknown):
///   * The unwrapped value is a `Result` (`unwrap` on `Result`), so the only
///     panic path is the `Err` arm — there is no `None` arm to reason about.
///   * The receiver `args[0]` is a BARE LOCAL `_r` (no projections): we trace a
///     whole-local value, never a field/element of an aggregate.
///   * `_r` is defined by EXACTLY ONE `Call` terminator (a single, unambiguous
///     def) whose callee is a slice->array `try_into`/`try_from` conversion.
///   * The TARGET array length `N` is read from the conversion's RESULT type — the
///     `[T; N]` inside `Result<[T; N], _>` — and the unwrap's own destination type
///     `[T; N]`; BOTH must agree on `N`. (`array_len_of_result` / `array_len_of`.)
///   * The conversion's slice ARGUMENT has a STATICALLY-KNOWN length that is
///     EXACTLY `N` — established only from a constant `Subslice { from, to,
///     from_end: false }` projection (length `to - from`) or a chain that ends in
///     one. A runtime-variable range (`bytes[len-8..]`, `bytes[off..off+8]`) does
///     NOT lower to a constant `Subslice` (it is a separate `slice::index` Call
///     whose result length is not statically `N`), so `slice_static_len` returns
///     `None` and the obligation is KEPT — we never assume the dynamic length
///     equals `N`. A genuinely-wrong-length conversion (e.g. `bytes[0..7]` into
///     `[u8; 8]`) has `to - from != N`, so the equality check fails and the
///     obligation is KEPT. An arbitrary `Result::unwrap` (not a slice->array
///     conversion) never matches and is STILL flagged.
/// Trust (Part B): `true` IFF the `Call` terminator in block `ordinal` is a
/// `Result::unwrap` that is PROVABLY INFALLIBLE — the success-by-construction of a
/// slice->array `try_into`/`try_from` whose slice length provably equals the array
/// length (the SAME [`unwrap_is_infallible_slice_to_array`] predicate the
/// `Call::unwrap::panic-freedom` per-statement suppression uses). The hardened
/// `PanicBoundary` lane calls this to SUPPRESS the `Result::unwrap` twin for exactly
/// these infallible unwraps; a genuinely-fallible unwrap (unknown length, user Index
/// impl, non-`try_into` Result) does NOT match and the twin is still emitted
/// (fail-closed). Any other terminator / a non-unwrap call returns `false`.
pub(crate) fn unwrap_call_at_block_is_infallible(
    func: &VerifiableFunction,
    ordinal: usize,
) -> bool {
    func.body.blocks.iter().any(|block| {
        block.id.0 == ordinal
            && matches!(
                &block.terminator,
                Terminator::Call { func: callee, args, dest, .. }
                    if unwrap_is_infallible_slice_to_array(func, callee, args, dest)
                        // Trust (countdown-loop piece, B0): the const-int
                        // conversion `expect` twin — success-by-construction.
                        || expect_infallible_const_int_conversion(func, callee, args, dest)
                            .is_some()
            )
    })
}
