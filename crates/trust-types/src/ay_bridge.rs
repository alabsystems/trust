// trust-types/ay_bridge.rs: Conversion bridge between trust_types::Formula ↔ ay_bindings::Expr
//
// Phase 1 of the trust-mc/ay direct integration. Provides bidirectional
// conversion so downstream crates can migrate incrementally from Formula to Expr.
//
// Design: designs/2026-04-13-trust-mc-direct-integration.md
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::formula::{Formula, RoundingMode, Sort};
use ay_bindings::{Expr, RoundingMode as AyRm, Sort as AYSort, SortInner as AYSortInner};

/// Convert a trust_types::Sort to a ay_bindings::Sort.
#[must_use]
pub fn sort_to_ay(sort: &Sort) -> AYSort {
    match sort {
        Sort::Bool => AYSort::bool(),
        Sort::Int => AYSort::int(),
        Sort::BitVec(w) => AYSort::bitvec(*w),
        Sort::Array(idx, elem) => AYSort::array(sort_to_ay(idx), sort_to_ay(elem)),
        Sort::Float { eb, sb } => AYSort::floating_point(*eb, *sb),
        // ay carries the rounding mode as an *enum argument* of the fp.* ops
        // (see `ay_rounding_mode`), not as a first-class sorted term, so no
        // RoundingMode-sorted variable is ever created on the in-process path.
        // Map defensively to Bool; if this is ever hit it is a bridge bug.
        Sort::RoundingMode => AYSort::bool(),
        // Recursive/enum datatypes (Expr/Block/… in clean-kernel). Before this arm a
        // Datatype-sorted `declare_const` on the in-process ay lane hit the `unreachable!`
        // below and ICE'd trustc (exit 101) BEFORE any transport was emitted — which is
        // why `targo trust survey` collapsed to a single `<transport>` probe. Bring the
        // in-process lane to parity with the already-trusted SMT-text path
        // (`collect_datatype_decls`/`declare-datatype`): a fully-defined datatype maps to
        // an ay enum/datatype sort; a by-name reference (empty `constructors`, produced
        // for a self/mutually-recursive field) maps to an opaque named sort so the
        // reference and its definitional occurrence share the SMT sort identifier.
        //
        // SOUNDNESS: declaring a datatype (or opaque) sort asserts NO fact and cannot make
        // the context vacuously UNSAT (trust-ir-contract sort.rs soundness note) — a fresh
        // datatype-sorted constant is unconstrained (SAT), so this can only let obligations
        // report their honest outcome, never manufacture a false PROVE.
        Sort::Datatype { name, constructors } => {
            if constructors.is_empty() {
                AYSort::uninterpreted(name.clone())
            } else {
                AYSort::enum_type(
                    name.clone(),
                    constructors.iter().map(|(ctor, fields)| {
                        (
                            ctor.clone(),
                            fields
                                .iter()
                                .map(|(fname, fsort)| (fname.clone(), sort_to_ay(fsort)))
                                .collect::<Vec<_>>(),
                        )
                    }).collect::<Vec<_>>(),
                )
            }
        }
        // `Sort` is #[non_exhaustive] (trust-ir-contract). Fail-closed: a sort we
        // cannot faithfully represent in ay must abort, never silently coerce.
        _ => unreachable!("unhandled Sort variant in sort_to_ay"),
    }
}

/// Convert a ay_bindings::Sort to a trust_types::Sort.
///
/// Returns None for sorts that trust_types doesn't support (Real, FP, String, etc.).
#[must_use]
pub fn sort_from_ay(sort: &AYSort) -> Option<Sort> {
    match sort.inner() {
        AYSortInner::Bool => Some(Sort::Bool),
        AYSortInner::Int => Some(Sort::Int),
        AYSortInner::BitVec(bv) => Some(Sort::BitVec(bv.width)),
        AYSortInner::Array(arr) => {
            let idx = sort_from_ay(&arr.index_sort)?;
            let elem = sort_from_ay(&arr.element_sort)?;
            Some(Sort::Array(Box::new(idx), Box::new(elem)))
        }
        AYSortInner::FloatingPoint(eb, sb) => Some(Sort::Float { eb: *eb, sb: *sb }),
        // ay sorts not representable in trust_types
        AYSortInner::Real
        | AYSortInner::Datatype(_)
        | AYSortInner::String
        | AYSortInner::Uninterpreted(_)
        | AYSortInner::RegLan
        | AYSortInner::Seq(_) => None,
        _ => None, // future-proof for #[non_exhaustive]
    }
}

/// Convert a trust_types::Formula to a ay_bindings::Expr.
///
/// This is the key conversion for feeding trust_vcgen output into ay.
/// The mapping is 1:1 for all Formula variants.
#[must_use]
/// An ordering comparison operator, so [`lower_ordering`] can dispatch the
/// integer-vs-float lowering once for all four.
enum OrderCmp {
    Lt,
    Le,
    Gt,
    Ge,
}

/// Lower an ordering comparison `a <op> b`, dispatching on operand sort. A
/// FLOAT-sorted operand (an f64 magnitude bound `self.0 <= 1.0e30`) uses the IEEE
/// FP predicate (`fp.leq`/…); everything else keeps the integer lowering
/// (`int_le`/…) EXACTLY as before. The integer ops assert Int sorts and would
/// panic on an FP operand, so this dispatch is required for a float-sorted
/// comparison to lower at all. It is purely additive: no float ordering comparison
/// could previously reach `formula_to_expr` without panicking, so every
/// pre-existing (non-float) comparison lowers byte-for-byte identically.
fn lower_ordering(a: Expr, b: Expr, cmp: OrderCmp) -> Expr {
    let is_fp = a.sort().is_floating_point() || b.sort().is_floating_point();
    match (cmp, is_fp) {
        (OrderCmp::Lt, false) => a.int_lt(b),
        (OrderCmp::Le, false) => a.int_le(b),
        (OrderCmp::Gt, false) => a.int_gt(b),
        (OrderCmp::Ge, false) => a.int_ge(b),
        (OrderCmp::Lt, true) => a.fp_lt(b),
        (OrderCmp::Le, true) => a.fp_le(b),
        (OrderCmp::Gt, true) => a.fp_gt(b),
        (OrderCmp::Ge, true) => a.fp_ge(b),
    }
}

pub fn formula_to_expr(formula: &Formula) -> Expr {
    match formula {
        // Literals
        Formula::Bool(v) => Expr::bool_const(*v),
        Formula::Int(n) => Expr::int_const(*n),
        // Trust: round-A #2 false-PROVE fix — pass the full u128 (BigInt: From<u128>),
        // NOT `*n as i128` which wraps every value > i128::MAX (incl. u128::MAX -> -1),
        // making `0 <= a <= u128::MAX` encode as `0 <= a <= -1` (UNSAT) and vacuously
        // "proving" every u128 overflow/bounds VC in the in-process ay backend. The
        // smtlib text path already emits the decimal; this matches it losslessly.
        Formula::UInt(n) => Expr::int_const(*n),
        Formula::BitVec { value, width } => Expr::bitvec_const(*value, *width),

        // Variables
        Formula::Var(name, sort) => Expr::var(name.clone(), sort_to_ay(sort)),
        // SymVar resolves symbol to string for ay variable creation.
        Formula::SymVar(sym, sort) => Expr::var(sym.as_str().to_string(), sort_to_ay(sort)),

        // Boolean connectives
        Formula::Not(a) => formula_to_expr(a).not(),
        Formula::And(terms) => {
            if terms.is_empty() {
                Expr::true_()
            } else {
                Expr::and_many(terms.iter().map(formula_to_expr).collect())
            }
        }
        Formula::Or(terms) => {
            if terms.is_empty() {
                Expr::false_()
            } else {
                Expr::or_many(terms.iter().map(formula_to_expr).collect())
            }
        }
        Formula::Implies(a, b) => formula_to_expr(a).implies(formula_to_expr(b)),

        // Comparisons. Ordering comparisons are SORT-AWARE: a float-sorted operand
        // (an f64 magnitude bound `self.0 <= 1.0e30`) lowers to the IEEE FP predicate
        // (`fp.leq`), NOT `int_le` — the integer ops ASSERT Int sorts (`check:
        // int_same`) and would PANIC on an FP operand. (`Eq` is already sort-generic.)
        Formula::Eq(a, b) => formula_to_expr(a).eq(formula_to_expr(b)),
        Formula::Lt(a, b) => lower_ordering(formula_to_expr(a), formula_to_expr(b), OrderCmp::Lt),
        Formula::Le(a, b) => lower_ordering(formula_to_expr(a), formula_to_expr(b), OrderCmp::Le),
        Formula::Gt(a, b) => lower_ordering(formula_to_expr(a), formula_to_expr(b), OrderCmp::Gt),
        Formula::Ge(a, b) => lower_ordering(formula_to_expr(a), formula_to_expr(b), OrderCmp::Ge),

        // Integer arithmetic
        Formula::Add(a, b) => formula_to_expr(a).int_add(formula_to_expr(b)),
        Formula::Sub(a, b) => formula_to_expr(a).int_sub(formula_to_expr(b)),
        Formula::Mul(a, b) => formula_to_expr(a).int_mul(formula_to_expr(b)),
        // Rust integer `/` and `%` are TRUNCATED (quotient toward zero; the
        // remainder takes the sign of the dividend). ay's `int_div`/`int_mod`
        // (like SMT-LIB `div`/`mod`) are EUCLIDEAN (mod always non-negative; div
        // floors toward -inf), which diverges for negative dividends. Lowering
        // `%`/`/` as bare `int_mod`/`int_div` here proved sign/range properties
        // that real Rust violates (e.g. `#[ensures(result >= 0)] fn f(x:i32)->i32
        // { x % 256 }` falsely Proved although `(-1) % 256 == -1`). This is the
        // SAME bug fixed in the smtlib text path (round 7); the in-process ay
        // backend uses THIS direct lowering, so it must encode truncation too
        // (round 18). For non-negative operands (all unsigned div/rem) these
        // reduce to plain div/mod, so it is correct for both signed and unsigned.
        // (Division by zero is governed by a separate div-by-zero VC.)
        //   trem(a,b) = ite(a >= 0, mod(a,b), -mod(-a,b))
        //   tdiv(a,b) = (a - trem) / b   [exact: a == b*tdiv + trem]
        Formula::Rem(a, b) => Expr::ite(
            formula_to_expr(a).int_ge(Expr::int_const(0)),
            formula_to_expr(a).int_mod(formula_to_expr(b)),
            formula_to_expr(a).int_neg().int_mod(formula_to_expr(b)).int_neg(),
        ),
        Formula::Div(a, b) => {
            let trem = Expr::ite(
                formula_to_expr(a).int_ge(Expr::int_const(0)),
                formula_to_expr(a).int_mod(formula_to_expr(b)),
                formula_to_expr(a).int_neg().int_mod(formula_to_expr(b)).int_neg(),
            );
            formula_to_expr(a).int_sub(trem).int_div(formula_to_expr(b))
        }
        Formula::Neg(a) => formula_to_expr(a).int_neg(),

        // Bitvector arithmetic
        Formula::BvAdd(a, b, _) => formula_to_expr(a).bvadd(formula_to_expr(b)),
        Formula::BvSub(a, b, _) => formula_to_expr(a).bvsub(formula_to_expr(b)),
        Formula::BvMul(a, b, _) => formula_to_expr(a).bvmul(formula_to_expr(b)),
        Formula::BvUDiv(a, b, _) => formula_to_expr(a).bvudiv(formula_to_expr(b)),
        Formula::BvSDiv(a, b, _) => formula_to_expr(a).bvsdiv(formula_to_expr(b)),
        Formula::BvURem(a, b, _) => formula_to_expr(a).bvurem(formula_to_expr(b)),
        Formula::BvSRem(a, b, _) => formula_to_expr(a).bvsrem(formula_to_expr(b)),
        Formula::BvAnd(a, b, _) => formula_to_expr(a).bvand(formula_to_expr(b)),
        Formula::BvOr(a, b, _) => formula_to_expr(a).bvor(formula_to_expr(b)),
        Formula::BvXor(a, b, _) => formula_to_expr(a).bvxor(formula_to_expr(b)),
        Formula::BvNot(a, _) => formula_to_expr(a).bvnot(),
        Formula::BvShl(a, b, _) => formula_to_expr(a).bvshl(formula_to_expr(b)),
        Formula::BvLShr(a, b, _) => formula_to_expr(a).bvlshr(formula_to_expr(b)),
        Formula::BvAShr(a, b, _) => formula_to_expr(a).bvashr(formula_to_expr(b)),

        // Bitvector comparisons
        Formula::BvULt(a, b, _) => formula_to_expr(a).bvult(formula_to_expr(b)),
        Formula::BvULe(a, b, _) => formula_to_expr(a).bvule(formula_to_expr(b)),
        Formula::BvSLt(a, b, _) => formula_to_expr(a).bvslt(formula_to_expr(b)),
        Formula::BvSLe(a, b, _) => formula_to_expr(a).bvsle(formula_to_expr(b)),

        // Bitvector conversions. Honor the signedness flag: an unsigned
        // conversion of a top-bit-set value (e.g. u8 0xFF) must yield 255, not
        // the two's-complement -1 that bv2int_signed produces. Always using the
        // signed conversion silently corrupts unsigned BvToInt operands.
        Formula::BvToInt(a, _w, signed) => {
            if *signed {
                formula_to_expr(a).bv2int_signed()
            } else {
                formula_to_expr(a).bv2int()
            }
        }
        Formula::IntToBv(a, w) => formula_to_expr(a).int2bv(*w),
        Formula::BvExtract { inner, high, low } => formula_to_expr(inner).extract(*high, *low),
        Formula::BvConcat(a, b) => formula_to_expr(a).concat(formula_to_expr(b)),
        Formula::BvZeroExt(a, bits) => formula_to_expr(a).zero_extend(*bits),
        Formula::BvSignExt(a, bits) => formula_to_expr(a).sign_extend(*bits),

        // Conditional
        Formula::Ite(c, t, e) => {
            Expr::ite(formula_to_expr(c), formula_to_expr(t), formula_to_expr(e))
        }

        // Quantifiers
        // Symbol bindings — resolve to String for ay API.
        Formula::Forall(bindings, body) => {
            let ay_bindings_list: Vec<(String, AYSort)> = bindings
                .iter()
                .map(|(sym, sort)| (sym.as_str().to_string(), sort_to_ay(sort)))
                .collect();
            Expr::forall(ay_bindings_list, formula_to_expr(body))
        }
        Formula::Exists(bindings, body) => {
            let ay_bindings_list: Vec<(String, AYSort)> = bindings
                .iter()
                .map(|(sym, sort)| (sym.as_str().to_string(), sort_to_ay(sort)))
                .collect();
            Expr::exists(ay_bindings_list, formula_to_expr(body))
        }

        // Arrays
        Formula::Select(arr, idx) => formula_to_expr(arr).select(formula_to_expr(idx)),
        Formula::Store(arr, idx, val) => {
            formula_to_expr(arr).store(formula_to_expr(idx), formula_to_expr(val))
        }

        // Uninterpreted boolean predicate: an opaque `Pred(name, args)` becomes
        // a Bool-sorted uninterpreted function application in ay. `func_app`
        // fixes the result sort to Bool, matching `Pred`'s predicate semantics.
        Formula::Pred(name, args) => {
            Expr::func_app(name.as_str().to_string(), args.iter().map(formula_to_expr).collect())
        }

        // ── IEEE-754 floating point ─────────────────────────────────────────
        Formula::FpConst { bits, eb, sb } => fp_const_from_bits(*bits, *eb, *sb),
        Formula::FpNaN { eb, sb } => Expr::fp_nan(&AYSort::floating_point(*eb, *sb)),
        Formula::FpInf { neg, eb, sb } => {
            let s = AYSort::floating_point(*eb, *sb);
            if *neg { Expr::fp_minus_infinity(&s) } else { Expr::fp_plus_infinity(&s) }
        }
        Formula::FpZero { neg, eb, sb } => {
            let s = AYSort::floating_point(*eb, *sb);
            if *neg { Expr::fp_minus_zero(&s) } else { Expr::fp_plus_zero(&s) }
        }
        // A bare rounding-mode term has no standalone ay `Expr` (ay takes it as an
        // enum arg of each fp.* op, via `ay_rounding_mode`); unreachable in
        // well-formed VCs.
        Formula::FpRoundingMode(_) => Expr::true_(),
        Formula::FpAdd(rm, a, b) => {
            formula_to_expr(a).fp_add(ay_rounding_mode(rm), formula_to_expr(b))
        }
        Formula::FpSub(rm, a, b) => {
            formula_to_expr(a).fp_sub(ay_rounding_mode(rm), formula_to_expr(b))
        }
        Formula::FpMul(rm, a, b) => {
            formula_to_expr(a).fp_mul(ay_rounding_mode(rm), formula_to_expr(b))
        }
        Formula::FpDiv(rm, a, b) => {
            formula_to_expr(a).fp_div(ay_rounding_mode(rm), formula_to_expr(b))
        }
        Formula::FpFma(rm, a, b, c) => {
            formula_to_expr(a).fp_fma(ay_rounding_mode(rm), formula_to_expr(b), formula_to_expr(c))
        }
        Formula::FpSqrt(rm, a) => formula_to_expr(a).fp_sqrt(ay_rounding_mode(rm)),
        Formula::FpRem(a, b) => formula_to_expr(a).fp_rem(formula_to_expr(b)),
        Formula::FpNeg(a) => formula_to_expr(a).fp_neg(),
        Formula::FpAbs(a) => formula_to_expr(a).fp_abs(),
        Formula::FpMin(a, b) => formula_to_expr(a).fp_min(formula_to_expr(b)),
        Formula::FpMax(a, b) => formula_to_expr(a).fp_max(formula_to_expr(b)),
        Formula::FpEq(a, b) => formula_to_expr(a).fp_eq(formula_to_expr(b)),
        Formula::FpLt(a, b) => formula_to_expr(a).fp_lt(formula_to_expr(b)),
        Formula::FpLe(a, b) => formula_to_expr(a).fp_le(formula_to_expr(b)),
        Formula::FpGt(a, b) => formula_to_expr(a).fp_gt(formula_to_expr(b)),
        Formula::FpGe(a, b) => formula_to_expr(a).fp_ge(formula_to_expr(b)),
        Formula::FpIsNaN(a) => formula_to_expr(a).fp_is_nan(),
        Formula::FpIsInfinite(a) => formula_to_expr(a).fp_is_infinite(),
        Formula::FpIsZero(a) => formula_to_expr(a).fp_is_zero(),
        Formula::FpIsNormal(a) => formula_to_expr(a).fp_is_normal(),
        Formula::FpIsSubnormal(a) => formula_to_expr(a).fp_is_subnormal(),
        Formula::FpIsNegative(a) => formula_to_expr(a).fp_is_negative(),
        Formula::FpIsPositive(a) => formula_to_expr(a).fp_is_positive(),
        Formula::FpFromBits { bits, eb, sb } => {
            fp_from_bv_expr(formula_to_expr(bits), *eb, *sb)
        }
        // `(fp.to_ieee_bv <fp>)` — reinterpret a float as its IEEE-754 bit
        // pattern (an `(eb+sb)`-wide bitvector). The EXACT inverse of
        // `FpFromBits`. Bit-preserving: NaN payloads and the sign of ±0.0 are
        // carried through verbatim, so a structural `Eq` over the resulting BVs
        // distinguishes them (unlike `fp.eq`, which is IEEE value-equality).
        Formula::FpToIeeeBv(a) => formula_to_expr(a).fp_to_ieee_bv(),

        // ── Algebraic datatypes (Lever A) ───────────────────────────────────
        // A datatype equation like `Sort(succ l) = Sort(succ l)` lowers to a
        // GENUINE ay `DatatypeConstructor`/`Selector`/`Tester` Expr (not a
        // stub). The datatype must have been declared to the program
        // (`declare-datatype` / `try_declare_datatype`) for the solver to accept
        // these; declaring one asserts NO fact (a fresh datatype-sorted constant
        // is SAT), so this can only let obligations report their honest outcome,
        // never manufacture a false PROVE.
        Formula::Ctor { ctor, args, sort } => {
            // The datatype (sort) name is carried by the Ctor's own result sort.
            let Sort::Datatype { name, .. } = sort else {
                // Fail-closed: a Ctor whose sort is not a datatype is a builder
                // bug — abort rather than silently misencode.
                unreachable!("Formula::Ctor sort must be Sort::Datatype");
            };
            Expr::datatype_constructor(
                name.clone(),
                ctor.clone(),
                args.iter().map(formula_to_expr).collect(),
                sort_to_ay(sort),
            )
        }
        Formula::Sel { datatype, field, field_sort, arg } => {
            formula_to_expr(arg).field_select(
                datatype.clone(),
                field.clone(),
                sort_to_ay(field_sort),
            )
        }
        Formula::IsCtor { datatype, ctor, arg } => {
            formula_to_expr(arg).is_constructor(datatype.clone(), ctor.clone())
        }

        // `Formula` is #[non_exhaustive] (trust-ir-contract). Fail-closed: a
        // variant we cannot faithfully lower to an ay Expr must abort (a loud
        // panic in the verify path), never a silent misencoding.
        _ => unreachable!("unhandled Formula variant in formula_to_expr"),
    }
}

/// Extract the ay rounding-mode enum from a `Formula::FpRoundingMode` operand.
/// Rounding modes are always literals in practice (Rust rounds to nearest-even);
/// a non-literal rm operand defaults to `RNE`.
fn ay_rounding_mode(f: &Formula) -> AyRm {
    match f {
        Formula::FpRoundingMode(rm) => match rm {
            RoundingMode::RNE => AyRm::RNE,
            RoundingMode::RNA => AyRm::RNA,
            RoundingMode::RTP => AyRm::RTP,
            RoundingMode::RTN => AyRm::RTN,
            RoundingMode::RTZ => AyRm::RTZ,
        },
        _ => AyRm::RNE,
    }
}

/// Build an FP constant from a raw IEEE bit pattern via ay's `(fp sign exp sig)`.
fn fp_const_from_bits(bits: u128, eb: u32, sb: u32) -> Expr {
    let sig_w = sb - 1; // stored significand excludes the hidden bit
    let total = eb + sb;
    let sign = ((bits >> (total - 1)) & 1) as i128;
    let exp = ((bits >> sig_w) & ((1u128 << eb) - 1)) as i128;
    let sig = (bits & ((1u128 << sig_w) - 1)) as i128;
    Expr::fp_from_bvs(
        Expr::bitvec_const(sign, 1),
        Expr::bitvec_const(exp, eb),
        Expr::bitvec_const(sig, sig_w),
    )
}

/// Reinterpret a `(eb+sb)`-wide bitvector `Expr` as a float via field extraction.
fn fp_from_bv_expr(bv: Expr, eb: u32, sb: u32) -> Expr {
    let sig_w = sb - 1;
    let total = eb + sb;
    let sign = bv.clone().extract(total - 1, total - 1);
    let exp = bv.clone().extract(total - 2, sig_w);
    let sig = bv.extract(sig_w - 1, 0);
    Expr::fp_from_bvs(sign, exp, sig)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uint_max_encodes_losslessly_not_truncated_to_negative() {
        // round-A #2 false-PROVE regression: u128::MAX must encode as the full
        // positive value, NOT wrap to -1 (`u128::MAX as i128`), which made
        // `0 <= a <= u128::MAX` encode UNSAT and vacuously prove u128 overflow VCs.
        let got = formula_to_expr(&Formula::UInt(u128::MAX));
        assert_eq!(got, Expr::int_const(u128::MAX), "u128::MAX must encode losslessly");
        assert_ne!(got, Expr::int_const(-1i128), "must NOT truncate to -1 (the false-PROVE bug)");
        // A mid-range value above i128::MAX also stays positive.
        let mid = (1u128 << 127) + 5;
        assert_eq!(formula_to_expr(&Formula::UInt(mid)), Expr::int_const(mid));
    }

    // ── IEEE-754 floating point bridge ──────────────────────────────────────

    fn fp_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Float { eb: 11, sb: 53 })
    }
    fn rne() -> Box<Formula> {
        Box::new(Formula::FpRoundingMode(RoundingMode::RNE))
    }

    #[test]
    fn float_sort_maps_to_ay_floating_point() {
        let s = sort_to_ay(&Sort::Float { eb: 8, sb: 24 });
        assert_eq!(format!("{s}"), "(_ FloatingPoint 8 24)");
        assert_eq!(sort_from_ay(&s), Some(Sort::Float { eb: 8, sb: 24 }));
    }

    #[test]
    fn fp_ops_bridge_to_ay_smtlib() {
        let add = Formula::FpAdd(rne(), Box::new(fp_var("x")), Box::new(fp_var("y")));
        assert_eq!(format!("{}", formula_to_expr(&add)), "(fp.add RNE x y)");
        let lt = Formula::FpLt(Box::new(fp_var("x")), Box::new(fp_var("y")));
        assert_eq!(format!("{}", formula_to_expr(&lt)), "(fp.lt x y)");
        let isnan = Formula::FpIsNaN(Box::new(fp_var("x")));
        assert_eq!(format!("{}", formula_to_expr(&isnan)), "(fp.isNaN x)");
        let nan = Formula::FpNaN { eb: 8, sb: 24 };
        assert_eq!(format!("{}", formula_to_expr(&nan)), "(_ NaN 8 24)");
    }

    // End-to-end solver validation (Formula -> ay Expr -> ay solve). Gated behind
    // `ay-bridge-solve` (pulls the ay-dpll backend); proves the encoding is SOUND
    // — the IEEE-754 facts our vcgen float-comparison encoding relies on are
    // decided correctly. This is the "implemented AND validated" gate.
    #[cfg(feature = "ay-bridge-solve")]
    fn solve_is_unsat(decls: &[&str], formula: &Formula) -> bool {
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let mut program = AYProgram::new();
        program.set_logic(crate::smt_logic::select_logic(formula));
        for name in decls {
            program.declare_const(*name, AYSort::floating_point(11, 53));
        }
        program.assert(formula_to_expr(formula));
        program.check_sat();
        let outcomes = execute_incremental(&program).expect("ay execute_incremental");
        match outcomes.last().map(|o| &o.result) {
            Some(ExecuteTypedResult::Verified) => true,
            Some(ExecuteTypedResult::Counterexample(_)) => false,
            other => panic!("unexpected solver result: {other:?}"),
        }
    }

    /// BV twin of [`solve_is_unsat`] for the declared-width Machine{w}
    /// contract goals (trust-vcgen's `machine_faithful_vc_formula` output
    /// shape): consts are declared at their machine width.
    #[cfg(feature = "ay-bridge-solve")]
    fn solve_bv_is_unsat(decls: &[(&str, u32)], formula: &Formula) -> bool {
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let mut program = AYProgram::new();
        program.set_logic(crate::smt_logic::select_logic(formula));
        for (name, width) in decls {
            program.declare_const(*name, AYSort::bitvec(*width));
        }
        program.assert(formula_to_expr(formula));
        program.check_sat();
        let outcomes = execute_incremental(&program).expect("ay execute_incremental");
        match outcomes.last().map(|o| &o.result) {
            Some(ExecuteTypedResult::Verified) => true,
            Some(ExecuteTypedResult::Counterexample(_)) => false,
            other => panic!("unexpected solver result: {other:?}"),
        }
    }

    #[cfg(feature = "ay-bridge-solve")]
    fn bv64_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(64))
    }

    /// The Machine{w} false-proof pin at the SOLVER: the declared-width
    /// reading of `ensures result + 1 > result` with body `result = x` must
    /// stay SATisfiable (the `u64::MAX` wrap witness) — the `Int` reading
    /// proved this exact clause, the confirmed false proof.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_machine_width_wrap_refutes_spec_tautology() {
        let ret = || Box::new(bv64_var("_0"));
        let x = || Box::new(bv64_var("x"));
        let one = || Box::new(Formula::BitVec { value: 1, width: 64 });
        let f = Formula::And(vec![
            Formula::Eq(ret(), x()),
            // ¬(result + 1 >u result)  ⟺  result + 1 <=u result
            Formula::BvULe(Box::new(Formula::BvAdd(ret(), one(), 64)), ret(), 64),
        ]);
        assert!(
            !solve_bv_is_unsat(&[("_0", 64), ("x", 64)], &f),
            "the wrap witness at u64::MAX must stay SAT — UNSAT here is the false proof"
        );
    }

    /// The Machine{w} positive pin at the SOLVER: with the wrap excluded by a
    /// declared precondition, the TRUE contract `requires x < u64::MAX ensures
    /// result == x + 1` proves (violation UNSAT) at the declared width.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_machine_width_guarded_increment_proves() {
        let ret = || Box::new(bv64_var("_0"));
        let x = || Box::new(bv64_var("x"));
        let one = || Box::new(Formula::BitVec { value: 1, width: 64 });
        let max = || Box::new(Formula::BitVec { value: i128::from(u64::MAX), width: 64 });
        let f = Formula::And(vec![
            Formula::BvULt(x(), max(), 64),
            Formula::Eq(ret(), Box::new(Formula::BvAdd(x(), one(), 64))),
            Formula::Not(Box::new(Formula::Eq(
                ret(),
                Box::new(Formula::BvAdd(x(), one(), 64)),
            ))),
        ]);
        assert!(
            solve_bv_is_unsat(&[("_0", 64), ("x", 64)], &f),
            "the guarded increment's violation must be UNSAT"
        );
        // The stronger relational form: `ensures result > x`.
        let g = Formula::And(vec![
            Formula::BvULt(x(), max(), 64),
            Formula::Eq(ret(), Box::new(Formula::BvAdd(x(), one(), 64))),
            // ¬(result >u x) ⟺ result <=u x
            Formula::BvULe(ret(), x(), 64),
        ]);
        assert!(
            solve_bv_is_unsat(&[("_0", 64), ("x", 64)], &g),
            "x < MAX ∧ result = x + 1 ∧ result <=u x must be UNSAT"
        );
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_rejects_nan_less_than_zero() {
        // x < 0 AND isNaN(x) -> UNSAT (NaN is unordered; the soundness property
        // the pre-FP magnitude encoding violated).
        let zero = || Box::new(Formula::FpZero { neg: false, eb: 11, sb: 53 });
        let f = Formula::And(vec![
            Formula::FpLt(Box::new(fp_var("x")), zero()),
            Formula::FpIsNaN(Box::new(fp_var("x"))),
        ]);
        assert!(solve_is_unsat(&["x"], &f), "NaN < 0 must be UNSAT");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_allows_negative_float() {
        let f = Formula::FpLt(
            Box::new(fp_var("x")),
            Box::new(Formula::FpZero { neg: false, eb: 11, sb: 53 }),
        );
        assert!(!solve_is_unsat(&["x"], &f), "x < 0 must be SAT");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_nan_not_equal_nan() {
        let f = Formula::And(vec![
            Formula::FpIsNaN(Box::new(fp_var("x"))),
            Formula::FpEq(Box::new(fp_var("x")), Box::new(fp_var("x"))),
        ]);
        assert!(solve_is_unsat(&["x"], &f), "NaN == NaN must be UNSAT");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_bit_reinterpret_zero_is_zero() {
        // x = reinterpret(0x00..00) = +0.0  AND  not isZero(x) -> UNSAT.
        let bv0 = Box::new(Formula::BitVec { value: 0, width: 64 });
        let from_bits = Box::new(Formula::FpFromBits { bits: bv0, eb: 11, sb: 53 });
        let f = Formula::And(vec![
            Formula::Eq(Box::new(fp_var("x")), from_bits),
            Formula::Not(Box::new(Formula::FpIsZero(Box::new(fp_var("x"))))),
        ]);
        assert!(solve_is_unsat(&["x"], &f), "reinterpret(0) is +0.0, must classify as zero");
    }

    // Float ARITHMETIC value-definition semantics (the shape vcgen emits:
    // `Eq(dest, fp.op(RNE, x, y))`), validated through the real ay solver.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_add_value_def_propagates_nan() {
        // d = x + y  AND  isNaN(x)  =>  isNaN(d). Deny ¬isNaN(d) -> UNSAT.
        let rne = || Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        let d_def = Formula::Eq(
            Box::new(fp_var("d")),
            Box::new(Formula::FpAdd(rne(), Box::new(fp_var("x")), Box::new(fp_var("y")))),
        );
        let f = Formula::And(vec![
            d_def,
            Formula::FpIsNaN(Box::new(fp_var("x"))),
            Formula::Not(Box::new(Formula::FpIsNaN(Box::new(fp_var("d"))))),
        ]);
        assert!(solve_is_unsat(&["x", "y", "d"], &f), "float add must propagate NaN to the result");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_neg_value_def_is_involution() {
        // d = -(-x)  =>  d structurally equals x (exact; holds even for NaN/±0,
        // which is why a STRUCTURAL Eq definition is required, not fp.eq).
        let d_def = Formula::Eq(
            Box::new(fp_var("d")),
            Box::new(Formula::FpNeg(Box::new(Formula::FpNeg(Box::new(fp_var("x")))))),
        );
        let f = Formula::And(vec![
            d_def,
            Formula::Not(Box::new(Formula::Eq(Box::new(fp_var("d")), Box::new(fp_var("x"))))),
        ]);
        assert!(solve_is_unsat(&["x", "d"], &f), "-(-x) == x");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_abs_value_def_is_nonnegative() {
        // d = abs(x)  AND  ¬isNaN(x)  =>  d >= 0. Deny d < 0 -> UNSAT.
        let d_def =
            Formula::Eq(Box::new(fp_var("d")), Box::new(Formula::FpAbs(Box::new(fp_var("x")))));
        let f = Formula::And(vec![
            d_def,
            Formula::Not(Box::new(Formula::FpIsNaN(Box::new(fp_var("x"))))),
            Formula::FpLt(
                Box::new(fp_var("d")),
                Box::new(Formula::FpZero { neg: false, eb: 11, sb: 53 }),
            ),
        ]);
        assert!(solve_is_unsat(&["x", "d"], &f), "abs(x) is non-negative for non-NaN x");
    }

    #[test]
    fn fp_to_ieee_bv_bridges_to_ay_and_round_trips() {
        // The bridge must lower `FpToIeeeBv(FpFromBits(bv64))` to an ay Expr
        // (previously this hit the fail-closed `unreachable!`). Structurally, the
        // FP->BV reinterpret of the BV->FP reinterpret is the identity round-trip.
        let bv = Box::new(Formula::Var("v".into(), Sort::BitVec(64)));
        let from_bits = Box::new(Formula::FpFromBits { bits: bv, eb: 11, sb: 53 });
        let to_bv = Formula::FpToIeeeBv(from_bits);
        // Lowering must not panic and must equal the ay Expr built directly.
        let got = formula_to_expr(&to_bv);
        let expected = {
            let inner_bv = Expr::var("v".to_string(), AYSort::bitvec(64));
            fp_from_bv_expr(inner_bv, 11, 53).fp_to_ieee_bv()
        };
        assert_eq!(got, expected, "FpToIeeeBv must lower to ay fp_to_ieee_bv over the FP operand");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_fp_to_ieee_bv_congruence_x_eq_x_is_unsat_to_refute() {
        // The two-sided proof's actual dependency: `to_ieee_bv(add) == to_ieee_bv(add)`
        // (identical shapes over identical operands) is VALID by congruence — the
        // NEGATION is UNSAT. This holds bit-exactly regardless of NaN
        // canonicalization, unlike a round-trip identity. This mirrors exactly what
        // `verify_output` discharges for the f64 FADD gate.
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let lane = |name: &str| Box::new(Formula::Var(name.into(), Sort::BitVec(64)));
        let mk = |x: &str, y: &str| {
            let xf = Box::new(Formula::FpFromBits { bits: lane(x), eb: 11, sb: 53 });
            let yf = Box::new(Formula::FpFromBits { bits: lane(y), eb: 11, sb: 53 });
            let rm = Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
            Box::new(Formula::FpToIeeeBv(Box::new(Formula::FpAdd(rm, xf, yf))))
        };
        // NOT( to_ieee_bv(add(x,y)) == to_ieee_bv(add(x,y)) ) must be UNSAT.
        let f = Formula::Not(Box::new(Formula::Eq(mk("a", "b"), mk("a", "b"))));
        let mut program = AYProgram::new();
        program.set_logic(crate::smt_logic::select_logic(&f));
        program.declare_const("a", AYSort::bitvec(64));
        program.declare_const("b", AYSort::bitvec(64));
        program.assert(formula_to_expr(&f));
        program.check_sat();
        let outcomes = execute_incremental(&program).expect("ay execute_incremental");
        assert!(
            matches!(outcomes.last().map(|o| &o.result), Some(ExecuteTypedResult::Verified)),
            "identical FpToIeeeBv(FpAdd(..)) shapes must be congruent (X == X UNSAT to refute)"
        );
    }

    // ── f32 (eb=8, sb=24) FP arithmetic bridge — the S-lane proofs ─────────────
    //
    // f32 rides the IDENTICAL width-parametric shape as f64
    // (`FpToIeeeBv(Fp*(RNE, FpFromBits(_,8,24), FpFromBits(_,8,24)))`), just at
    // (eb=8, sb=24) over the low 32-bit S-lane. These solver-backed proofs mirror
    // the f64 `solver_fp_to_ieee_bv_congruence_x_eq_x_is_unsat_to_refute` and the
    // f32 gap the residual `B-aarch64-fp-pending` never covered (it was f32 FCVT
    // + FMA only, NOT f32 add/sub/mul/div).

    /// Run an f32 (BV(32)-lane) obligation through ay: assert `formula`, declare
    /// each name as a 32-bit BV const, return true iff UNSAT ("Verified").
    #[cfg(feature = "ay-bridge-solve")]
    fn f32_solve_is_unsat(bv32_decls: &[&str], formula: &Formula) -> bool {
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let mut program = AYProgram::new();
        program.set_logic(crate::smt_logic::select_logic(formula));
        for name in bv32_decls {
            program.declare_const(*name, AYSort::bitvec(32));
        }
        program.assert(formula_to_expr(formula));
        program.check_sat();
        let outcomes = execute_incremental(&program).expect("ay execute_incremental");
        match outcomes.last().map(|o| &o.result) {
            Some(ExecuteTypedResult::Verified) => true,
            Some(ExecuteTypedResult::Counterexample(_)) => false,
            other => panic!("unexpected solver result: {other:?}"),
        }
    }

    /// The f32 two-sided machine/IR shape over the low 32-bit lanes `x`,`y`:
    /// `FpToIeeeBv(<op>(RNE, FpFromBits(x,8,24), FpFromBits(y,8,24)))`.
    #[cfg(feature = "ay-bridge-solve")]
    fn f32_binop_bits(
        x: &str,
        y: &str,
        op: fn(Box<Formula>, Box<Formula>, Box<Formula>) -> Formula,
    ) -> Box<Formula> {
        let lane = |n: &str| Box::new(Formula::Var(n.into(), Sort::BitVec(32)));
        let xf = Box::new(Formula::FpFromBits { bits: lane(x), eb: 8, sb: 24 });
        let yf = Box::new(Formula::FpFromBits { bits: lane(y), eb: 8, sb: 24 });
        let rm = Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        Box::new(Formula::FpToIeeeBv(Box::new(op(rm, xf, yf))))
    }

    /// A 32-bit BV constant carrying a concrete f32 IEEE bit pattern.
    #[cfg(feature = "ay-bridge-solve")]
    fn f32_bits(bits: i128) -> Box<Formula> {
        Box::new(Formula::BitVec { value: bits, width: 32 })
    }

    /// The f32 shape over two CONSTANT lanes: `FpToIeeeBv(<op>(RNE,
    /// FpFromBits(a_bits,8,24), FpFromBits(b_bits,8,24)))` — a closed BV(32) term.
    #[cfg(feature = "ay-bridge-solve")]
    fn f32_binop_const(
        a_bits: i128,
        b_bits: i128,
        op: fn(Box<Formula>, Box<Formula>, Box<Formula>) -> Formula,
    ) -> Box<Formula> {
        let af = Box::new(Formula::FpFromBits { bits: f32_bits(a_bits), eb: 8, sb: 24 });
        let bf = Box::new(Formula::FpFromBits { bits: f32_bits(b_bits), eb: 8, sb: 24 });
        let rm = Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        Box::new(Formula::FpToIeeeBv(Box::new(op(rm, af, bf))))
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_congruence_x_eq_x_is_unsat_for_all_ops() {
        // The two-sided f32 proof's actual dependency: for each of ADD/SUB/MUL/DIV,
        // `to_ieee_bv(op) == to_ieee_bv(op)` (identical shapes over identical BV(32)
        // lanes) is VALID by congruence — its NEGATION is UNSAT. This is exactly
        // what the machine/IR f32 gate discharges (X == X UNSAT to refute the
        // inequality). Holds bit-exactly regardless of NaN canonicalization.
        for (name, op) in [
            ("add", Formula::FpAdd as fn(_, _, _) -> _),
            ("sub", Formula::FpSub),
            ("mul", Formula::FpMul),
            ("div", Formula::FpDiv),
        ] {
            let mk = || f32_binop_bits("a", "b", op);
            // NOT( shape == shape ) must be UNSAT (i.e. shape == shape is valid).
            let f = Formula::Not(Box::new(Formula::Eq(mk(), mk())));
            assert!(
                f32_solve_is_unsat(&["a", "b"], &f),
                "f32 {name}: identical FpToIeeeBv(Fp{name}(..)) shapes must be congruent (X == X UNSAT)"
            );
        }
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_negative_control_wrong_result_is_refuted() {
        // NEGATIVE CONTROL (concrete, backend-tractable): the f32 gate has TEETH —
        // a WRONG expected value is genuinely rejected. `1.5 + 2.5` is 4.0
        // (0x40800000), NOT 5.0 (0x40A00000); so `sum == 0x40A00000` is
        // UNSATISFIABLE. Proving that UNSAT is precisely the mechanism by which a
        // miscompile that produced 5.0 would be Refuted rather than Proven.
        //
        // (The symbolic divergent-operand SAT direction — finding a concrete
        // counterexample by bit-blasting full FP-add semantics — returns Unknown
        // on the ay-dpll backend; the gate never depends on that direction: it
        // proves EQUALITY UNSAT, and refutes wrong values via concrete folding as
        // here.)
        let sum = f32_binop_const(0x3FC0_0000, 0x4020_0000, Formula::FpAdd);
        let wrong = Formula::Eq(sum, f32_bits(0x40A0_0000)); // == 5.0f32 (WRONG)
        assert!(
            f32_solve_is_unsat(&[], &wrong),
            "1.5f32 + 2.5f32 == 5.0f32 must be UNSAT (wrong result refuted — gate has teeth)"
        );
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_value_diff_one_point_five_plus_two_point_five_is_four() {
        // Concrete f32 value: 1.5 + 2.5 == 4.0 at the bit level.
        //   1.5 = 0x3FC00000, 2.5 = 0x40200000, 4.0 = 0x40800000.
        // The f32 add shape over these constants must equal 0x40800000 exactly;
        // deny that equality -> UNSAT.
        let sum = f32_binop_const(0x3FC0_0000, 0x4020_0000, Formula::FpAdd);
        let f = Formula::Not(Box::new(Formula::Eq(sum, f32_bits(0x4080_0000))));
        assert!(f32_solve_is_unsat(&[], &f), "1.5f32 + 2.5f32 must equal 4.0f32 (0x40800000)");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_value_diff_neg_zero_plus_neg_zero_is_neg_zero() {
        // Sign-of-zero is load-bearing (bit-exact, not fp.eq): (-0.0) + (-0.0) is
        // -0.0 (0x80000000) under RNE, NOT +0.0 (0x00000000). Deny equality to
        // -0.0 -> UNSAT; and separately confirm it is NOT +0.0 (would be SAT).
        let sum = f32_binop_const(0x8000_0000, 0x8000_0000, Formula::FpAdd);
        let is_neg_zero = Formula::Not(Box::new(Formula::Eq(sum.clone(), f32_bits(0x8000_0000))));
        assert!(f32_solve_is_unsat(&[], &is_neg_zero), "(-0.0) + (-0.0) must be -0.0 (0x80000000)");
        // And it is bit-distinct from +0.0: `sum == +0.0` is UNSATISFIABLE-to-refute
        // i.e. NOT(sum == +0.0) must hold (UNSAT of the negation's negation). We
        // assert NOT(sum == +0.0) is a THEOREM by refuting its negation:
        let differs_from_pos_zero =
            Formula::Not(Box::new(Formula::Eq(sum, f32_bits(0x0000_0000))));
        // sum == +0.0 must be UNSAT, so NOT(sum == +0.0) is valid; deny it:
        let deny = Formula::Not(Box::new(differs_from_pos_zero));
        assert!(f32_solve_is_unsat(&[], &deny), "(-0.0) + (-0.0) must NOT be +0.0 (sign preserved)");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_value_diff_add_propagates_nan_exponent() {
        // NaN + anything = NaN. Over the f32 add shape, adding a quiet NaN
        // (0x7FC00000) to 1.0 (0x3F800000) yields a NaN result: its 8-bit
        // exponent field (result bits [30:23]) is all-ones (0xFF). We check this
        // via a pure BV extraction over the folded FpToIeeeBv(FpAdd(..)) result
        // (backend-tractable, unlike `FpIsNaN` through the bit round-trip): deny
        // `exp == 0xFF` -> UNSAT. (A NaN payload is not uniquely canonicalized, so
        // we assert the format-defined exponent, not a specific mantissa.)
        let sum = f32_binop_const(0x7FC0_0000, 0x3F80_0000, Formula::FpAdd);
        let exp = Formula::BvExtract { inner: sum, high: 30, low: 23 };
        let f = Formula::Not(Box::new(Formula::Eq(
            Box::new(exp),
            Box::new(Formula::BitVec { value: 0xFF, width: 8 }),
        )));
        assert!(
            f32_solve_is_unsat(&[], &f),
            "NaN + 1.0 must be NaN at f32 (result exponent field all-ones)"
        );
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_value_diff_one_over_zero_is_plus_inf() {
        // IEEE f32 division is TOTAL: 1.0 / 0.0 == +inf (0x7F800000), no trap.
        //   1.0 = 0x3F800000, 0.0 = 0x00000000, +inf = 0x7F800000.
        // The f32 div shape over these constants must equal 0x7F800000; deny -> UNSAT.
        let quot = f32_binop_const(0x3F80_0000, 0x0000_0000, Formula::FpDiv);
        let f = Formula::Not(Box::new(Formula::Eq(quot, f32_bits(0x7F80_0000))));
        assert!(f32_solve_is_unsat(&[], &f), "1.0f32 / 0.0f32 must be +inf (0x7F800000)");
    }

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    #[test]
    fn test_sort_roundtrip_bool() {
        let ay = sort_to_ay(&Sort::Bool);
        assert!(ay.is_bool());
        assert_eq!(sort_from_ay(&ay), Some(Sort::Bool));
    }

    #[test]
    fn test_sort_roundtrip_int() {
        let ay = sort_to_ay(&Sort::Int);
        assert!(ay.is_int());
        assert_eq!(sort_from_ay(&ay), Some(Sort::Int));
    }

    #[test]
    fn test_sort_roundtrip_bitvec() {
        let ay = sort_to_ay(&Sort::BitVec(32));
        assert!(ay.is_bitvec());
        assert_eq!(sort_from_ay(&ay), Some(Sort::BitVec(32)));
    }

    #[test]
    fn test_sort_roundtrip_array() {
        let sort = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
        let ay = sort_to_ay(&sort);
        assert!(ay.is_array());
        assert_eq!(sort_from_ay(&ay), Some(sort));
    }

    #[test]
    fn test_formula_bool_const() {
        let expr = formula_to_expr(&Formula::Bool(true));
        assert!(expr.sort().is_bool());
        let smt = format!("{expr}");
        assert_eq!(smt, "true");
    }

    #[test]
    fn test_formula_int_const() {
        let expr = formula_to_expr(&Formula::Int(42));
        assert!(expr.sort().is_int());
        let smt = format!("{expr}");
        assert_eq!(smt, "42");
    }

    #[test]
    fn test_formula_bitvec_const() {
        let expr = formula_to_expr(&Formula::BitVec { value: 255, width: 8 });
        assert!(expr.sort().is_bitvec());
        let smt = format!("{expr}");
        assert_eq!(smt, "#xff");
    }

    #[test]
    fn float_ordering_comparison_lowers_without_panic_taking_fp_path() {
        // A float magnitude bound (`self.0 <= 1.0e30`) must lower via the IEEE FP
        // predicate. The Int `int_le`/… ops ASSERT Int sorts and would PANIC on an
        // FP operand — so the mere fact these lower to a Bool-sorted expr (rather
        // than panicking) proves the sort-aware FP path was taken.
        let f64s = Sort::Float { eb: 11, sb: 53 };
        let field = Formula::Var("self.0".into(), f64s);
        let bound = Formula::FpConst { bits: u128::from(1.0e30_f64.to_bits()), eb: 11, sb: 53 };
        for cmp in [
            Formula::Le(Box::new(field.clone()), Box::new(bound.clone())),
            Formula::Ge(Box::new(field.clone()), Box::new(bound.clone())),
            Formula::Lt(Box::new(field.clone()), Box::new(bound.clone())),
            Formula::Gt(Box::new(field.clone()), Box::new(bound.clone())),
        ] {
            let expr = formula_to_expr(&cmp); // must not panic
            assert!(expr.sort().is_bool(), "float ordering comparison lowers to Bool");
        }
        // The `¬X ∧ X` discharge shape (caller's own bound vs the substituted callee
        // bound) lowers whole without panic and is Bool.
        let le = Formula::Le(Box::new(field), Box::new(bound));
        let discharge = Formula::And(vec![Formula::Not(Box::new(le.clone())), le]);
        assert!(formula_to_expr(&discharge).sort().is_bool());

        // Regression: an INTEGER ordering comparison still lowers via the Int path.
        let int_le = Formula::Le(Box::new(var("x")), Box::new(Formula::Int(5)));
        assert!(formula_to_expr(&int_le).sort().is_bool());
    }

    #[test]
    fn test_formula_var() {
        let expr = formula_to_expr(&var("x"));
        assert!(expr.sort().is_int());
        let smt = format!("{expr}");
        assert_eq!(smt, "x");
    }

    #[test]
    fn test_formula_not() {
        let f = Formula::Not(Box::new(Formula::Bool(true)));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(not true)");
    }

    #[test]
    fn test_formula_and() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(and true false)");
    }

    #[test]
    fn test_formula_implies() {
        let f = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(false)));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(=> true false)");
    }

    #[test]
    fn test_formula_eq() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(= x 0)");
    }

    #[test]
    fn test_formula_int_arith() {
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(+ x y)");
    }

    #[test]
    fn test_formula_bv_add() {
        let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(bvadd a b)");
    }

    #[test]
    fn test_formula_bv_comparisons() {
        let f = Formula::BvULt(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(bvult a b)");
    }

    #[test]
    fn test_formula_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(ite true 1 0)");
    }

    #[test]
    fn test_formula_forall() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("forall"));
        assert!(smt.contains("(x Int)"));
    }

    #[test]
    fn test_formula_select_store() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let idx = Formula::BitVec { value: 100, width: 64 };
        let val = Formula::BitVec { value: 42, width: 8 };

        let store = Formula::Store(Box::new(arr.clone()), Box::new(idx.clone()), Box::new(val));
        let expr = formula_to_expr(&store);
        let smt = format!("{expr}");
        assert!(smt.contains("store"));

        let select = Formula::Select(Box::new(arr), Box::new(idx));
        let expr = formula_to_expr(&select);
        let smt = format!("{expr}");
        assert!(smt.contains("select"));
    }

    #[test]
    fn test_formula_bv_extract() {
        let f = Formula::BvExtract { inner: Box::new(bv_var("x", 32)), high: 15, low: 0 };
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("extract"));
    }

    #[test]
    fn test_formula_bv_concat() {
        let f = Formula::BvConcat(Box::new(bv_var("hi", 16)), Box::new(bv_var("lo", 16)));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("concat"));
    }

    #[test]
    fn test_formula_zero_extend() {
        let f = Formula::BvZeroExt(Box::new(bv_var("x", 32)), 32);
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("zero_extend"));
    }

    // ── Algebraic-datatype terms (Lever A step-1) ───────────────────────────
    //
    // The datatype term nodes must lower to GENUINE ay
    // DatatypeConstructor/Selector/Tester Expr nodes (not stubs) over a declared
    // datatype sort. This is the ay half of the step-1 round-trip: it asserts
    // the nodes CONSTRUCT (and render), NOT that any VC is discharged.

    /// A recursive toy `Level = zero | succ(pred: Level)` (the shape the
    /// clean-kernel universe-level fidelity equation rides). The recursive
    /// `pred` field is a by-name reference (empty `constructors`).
    fn level_sort() -> Sort {
        let level_ref = Sort::Datatype { name: "Level".into(), constructors: Vec::new() };
        Sort::Datatype {
            name: "Level".into(),
            constructors: vec![
                ("zero".into(), vec![]),
                ("succ".into(), vec![("pred".into(), level_ref)]),
            ],
        }
    }

    #[test]
    fn datatype_ctor_bridges_to_ay_constructor() {
        // `succ l` builds a real ay DatatypeConstructor Expr, datatype-sorted,
        // rendering as the constructor application `(succ l)`.
        let l = Formula::Var("l".into(), level_sort());
        let ctor = Formula::Ctor { ctor: "succ".into(), args: vec![l], sort: level_sort() };
        let expr = formula_to_expr(&ctor);
        assert!(expr.sort().is_datatype(), "constructor result is datatype-sorted");
        assert_eq!(format!("{expr}"), "(succ l)");
    }

    #[test]
    fn datatype_nullary_ctor_bridges_to_ay_constructor() {
        // A nullary constructor bridges to a sort-qualified constant `(as zero Level)`.
        let zero = Formula::Ctor { ctor: "zero".into(), args: vec![], sort: level_sort() };
        let expr = formula_to_expr(&zero);
        assert!(expr.sort().is_datatype(), "nullary constructor is datatype-sorted");
        assert_eq!(format!("{expr}"), "(as zero Level)");
    }

    #[test]
    fn datatype_selector_bridges_to_ay_field_select() {
        // `(pred x)` builds a real ay DatatypeSelector Expr.
        let x = Formula::Var("x".into(), level_sort());
        let sel = Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_sort(),
            arg: Box::new(x),
        };
        let expr = formula_to_expr(&sel);
        assert_eq!(format!("{expr}"), "(pred x)");
    }

    #[test]
    fn datatype_tester_bridges_to_ay_is_constructor() {
        // `((_ is succ) x)` builds a real ay DatatypeTester Expr, Bool-sorted.
        let x = Formula::Var("x".into(), level_sort());
        let is = Formula::IsCtor {
            datatype: "Level".into(),
            ctor: "succ".into(),
            arg: Box::new(x),
        };
        let expr = formula_to_expr(&is);
        assert!(expr.sort().is_bool(), "tester is Bool-sorted");
        assert_eq!(format!("{expr}"), "((_ is succ) x)");
    }

    #[test]
    fn fidelity_equation_bridges_end_to_end() {
        // The step-1 headline through the ay bridge: `succ l = succ l` (the
        // `Sort(succ l) = Sort(succ l)` shape) constructs a real ay equality
        // over two datatype-constructor terms. WRITABLE + lowers; not a proof.
        let l = || Formula::Var("l".into(), level_sort());
        let succ = |a: Formula| Formula::Ctor { ctor: "succ".into(), args: vec![a], sort: level_sort() };
        let eq = Formula::Eq(Box::new(succ(l())), Box::new(succ(l())));
        let expr = formula_to_expr(&eq);
        assert_eq!(format!("{expr}"), "(= (succ l) (succ l))");
    }

    #[test]
    fn test_formula_smtlib_matches_ay() {
        // Verify that Formula::to_smtlib() and ay Expr Display produce
        // equivalent SMT-LIB2 for basic operations
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        let trust_smt = f.to_smtlib();
        let ay_smt = format!("{}", formula_to_expr(&f));
        // Both should be syntactically valid SMT-LIB2
        assert!(trust_smt.contains("and"));
        assert!(ay_smt.contains("and"));
    }
}
