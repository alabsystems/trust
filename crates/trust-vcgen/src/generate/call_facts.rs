// Dest-value facts for calls the VC lane models exactly rather than havocking:
// `Ord::min/max/clamp`, `bool::from`, the saturating and wrapping-negate
// families, and `f{32,64}::to_bits`. Each recognizer pairs a callee-path test
// with the formula that pins the destination local to the callee's result.

use super::*;

/// Extract the method name of an `Ord` trait call, e.g.
/// `<usize as Ord>::min` -> `Some("min")`. Returns the EXACT method (so
/// `min_by`/`min_by_key` — whose result bound is comparator-dependent and would
/// be UNSOUND to assume — are distinguished from `min`). Matches only the `Ord`
/// trait (integer/ordered types; floats have no `Ord`), so `a <= min(a,b)` holds.
pub(super) fn ord_method(callee: &str) -> Option<&str> {
    // Method = last path segment, minus any turbofish generics. Exact match so
    // `min_by`/`min_by_key` (comparator-dependent — unsound to bound) are excluded.
    let last = callee.rsplit("::").next()?;
    let method = last.split('<').next().unwrap_or(last).trim();
    if !matches!(method, "min" | "max" | "clamp") {
        return None;
    }
    // Scope to the standard-library ordered ops across the spellings
    // `safe_def_path_str` may produce: the `Ord` trait method
    // (`core::cmp::Ord::min`, `<T as ...Ord>::min`) or the `cmp` free function
    // (`core::cmp::min`). A user `mymod::min` matches none of these and is
    // (soundly) not assumed to satisfy the min/max bounds.
    let std_shaped = ((callee.starts_with("core::") || callee.starts_with("std::"))
        && callee.contains("::cmp::"))
        || callee.contains("as core::cmp::Ord>::")
        || callee.contains("as std::cmp::Ord>::")
        || callee.contains("as Ord>::");
    if std_shaped { Some(method) } else { None }
}

pub(super) fn is_ord_min_call(callee: &str) -> bool {
    ord_method(callee) == Some("min")
}

pub(super) fn is_ord_max_call(callee: &str) -> bool {
    ord_method(callee) == Some("max")
}

pub(super) fn is_ord_clamp_call(callee: &str) -> bool {
    ord_method(callee) == Some("clamp")
}

/// The standard `bool -> integer` conversion (`usize::from(b)` etc.), whose result is
/// exactly `b as {int}` and so lies in {0, 1}. Recognized so the call result (otherwise
/// havoc'd) can be soundly bounded, matching the `bool as {int}` CAST path
/// (`cast_definition_formula` -> `bool_to_int_formula`). `safe_def_path_str` resolves
/// `usize::from(b)` to the TRAIT-method spelling `core/std::convert::From::from` (NOT the
/// impl `<usize as From<bool>>::from`), so match that and the `Into` dual; the full impl
/// spelling is also accepted. The CALLER gates on a BOOL arg and an int-typed dest, which
/// together pin this to `From<bool>`/`Into<int>` for a primitive int — so `usize::from(u8)`
/// (non-bool arg) and a non-primitive `From<bool>` newtype (non-int dest) are both excluded.
pub(super) fn is_bool_from_call(callee: &str) -> bool {
    (callee.contains("From<bool>")
        && (callee.contains("as core::")
            || callee.contains("as std::")
            || callee.contains("as From<bool>")))
        || ((callee.starts_with("core::") || callee.starts_with("std::"))
            && (callee.ends_with("convert::From::from")
                || callee.ends_with("convert::Into::into")))
}

/// Whether `callee` is rooted at the genuine `core`/`std` primitive-number
/// inherent implementation. Callers use this before minting value-range facts;
/// a same-named user function must leave the destination unconstrained.
pub(super) fn is_std_num_intrinsic(callee: &str) -> bool {
    (callee.starts_with("core::") || callee.starts_with("std::"))
        && callee.contains("::num::")
}

/// The std integer `wrapping_neg` inherent method (`core::num::<impl i128>::
/// wrapping_neg` and the `iN`/`uN` siblings). CRATE-ORIGIN anchored like
/// `fp_abs_call_width` — a user-defined `mymod::wrapping_neg` must NOT match
/// (matching it would inject a false value-definition, a false-PROVE channel).
pub(super) fn is_int_wrapping_neg_call(callee: &str) -> bool {
    let tail = callee.rsplit("::").next().unwrap_or(callee);
    let tail = tail.split('<').next().unwrap_or(tail).trim();
    if tail != "wrapping_neg" {
        return false;
    }
    (callee.starts_with("core::") || callee.starts_with("std::")) && callee.contains("::num::")
}

/// The std integer `saturating_add` / `saturating_sub` inherent method
/// (`core::num::<impl u32>::saturating_add` and the `iN`/`uN` siblings), or
/// `None`. CRATE-ORIGIN anchored exactly like `is_int_wrapping_neg_call` — a
/// user-defined `mymod::saturating_add` must NOT match (it would inject a false
/// value-definition, a false-PROVE channel).
pub(super) fn saturating_add_sub_method(callee: &str) -> Option<&'static str> {
    let tail = callee.rsplit("::").next().unwrap_or(callee);
    let tail = tail.split('<').next().unwrap_or(tail).trim();
    let method = match tail {
        "saturating_add" => "saturating_add",
        "saturating_sub" => "saturating_sub",
        // Trust (flywheel feedback): named by the trust-convergence hardening
        // batch — `saturating_mul` yielded coverage-gap Unknowns while add/sub
        // proved. Same exact-total clamp axiom applies (`clamp(a*b, MIN, MAX)`
        // is the std semantics for every input; the nonlinear product routes
        // through the existing ay nonlinear-relaxation retry).
        "saturating_mul" => "saturating_mul",
        _ => return None,
    };
    let std_num =
        (callee.starts_with("core::") || callee.starts_with("std::")) && callee.contains("::num::");
    std_num.then_some(method)
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
    let method = saturating_add_sub_method(callee)?;
    if args.len() != 2 {
        return None;
    }
    let (width, signed) = func
        .body
        .locals
        .iter()
        .find(|d| d.index == dest.local)
        .and_then(|d| match &d.ty {
            Ty::Int { width, signed } => Some((*width, *signed)),
            _ => None,
        })
        .filter(|&(w, _)| w <= 64)?;
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
    if !is_int_wrapping_neg_call(callee) || args.len() != 1 {
        return None;
    }
    let (width, signed) =
        crate::operand_ty_cow(func, &args[0]).as_deref().and_then(|ty| match ty {
            Ty::Int { width, signed } => Some((*width, *signed)),
            _ => None,
        })?;
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
    let last = callee.rsplit("::").next()?;
    let method = last.split('<').next().unwrap_or(last).trim();
    let std_origin = callee.starts_with("core::")
        || callee.starts_with("std::")
        || callee.starts_with("alloc::");
    if !std_origin {
        return None;
    }
    let width = if callee.contains("::f64::") {
        64u32
    } else if callee.contains("::f32::") {
        32u32
    } else {
        return None;
    };
    let dest_name = crate::place_to_var_name(func, dest);
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
            match func.body.locals.iter().find(|d| d.index == dest.local).map(|d| &d.ty) {
                Some(Ty::Float { width: w }) if *w == width => {}
                _ => return None,
            }
            let arg = crate::operand_to_formula(func, &args[0]);
            Some(Formula::Eq(
                Box::new(Formula::Var(dest_name, Sort::BitVec(width))),
                Box::new(Formula::IntToBv(Box::new(arg), width)),
            ))
        }
        _ => None,
    }
}
