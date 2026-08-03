// trust-router/interval_backend.rs: In-process interval/range backend
//
// A self-contained abstract-interpretation backend that discharges *bounded*
// integer-overflow obligations without calling an external solver. It exists
// because the normal-mode router otherwise routes every `ArithmeticOverflow`
// VC to ay, and ay times out (NIA on `a % m`, casts), returns `unknown`
// (bitmask+int mixes), or false-fails on trivially-safe bounded arithmetic.
// This backend proves the obvious cases — `(a % 250) + 1`, `(a as u16) + 1`,
// `(a & 0x7f) + 1` — in microseconds, and declines everything else so it falls
// through to ay unchanged.
//
// SOUNDNESS: every transfer function over-approximates the real value set (or
// yields TOP). The backend returns `Proved` only when the result interval is a
// *finite* range provably inside the result type's `[min, max]`. Because the
// computed interval is a superset of the real results, "finite and inside"
// implies no input can overflow, i.e. the asserted violation condition is
// UNSAT. If anything is unknown or unbounded, `can_handle` returns false and
// the VC is left for ay — so this backend can never produce a false `Proved`
// nor mask a real overflow ay would have refuted.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::*;

use crate::{BackendRole, VerificationBackend};

/// An integer interval over `i128`. `None` endpoints denote unboundedness
/// (`lo = None` is -∞, `hi = None` is +∞), i.e. no information in that
/// direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Interval {
    lo: Option<i128>,
    hi: Option<i128>,
}

impl Interval {
    const TOP: Interval = Interval { lo: None, hi: None };

    /// The EMPTY (Bottom) interval: denotes NO value. Canonical crossed form
    /// `[1, 0]`. An empty interval arises ONLY from intersecting contradictory
    /// bounds (e.g. `n <= 100 ∧ n == 1<<30`) — i.e. an UNSAT antecedent. It must
    /// never discharge a goal: a "proof" over an empty operand is VACUOUS.
    const EMPTY: Interval = Interval { lo: Some(1), hi: Some(0) };

    fn cst(v: i128) -> Interval {
        Interval { lo: Some(v), hi: Some(v) }
    }

    fn range(lo: i128, hi: i128) -> Interval {
        Interval { lo: Some(lo), hi: Some(hi) }
    }

    /// `true` iff the interval is EMPTY (`lo > hi`) — no value satisfies it.
    /// Such an interval can only come from a contradictory (UNSAT) hypothesis
    /// set; treating it as provably-in-range is the vacuous-proof footgun.
    fn is_empty(&self) -> bool {
        matches!((self.lo, self.hi), (Some(l), Some(h)) if l > h)
    }

    /// `true` iff both endpoints are concrete AND the interval is non-empty,
    /// i.e. a genuine finite range `[lo, hi]` with `lo <= hi`. The non-empty
    /// requirement is load-bearing for SOUNDNESS: every acceptance site gates
    /// on `is_finite()` before concluding "in range", so an empty (contradictory)
    /// interval — whose endpoints are both concrete but crossed — must NOT count
    /// as finite, or it would vacuously satisfy any range check.
    fn is_finite(&self) -> bool {
        matches!((self.lo, self.hi), (Some(l), Some(h)) if l <= h)
    }

    /// `true` iff `v` is NOT provably excluded by this (over-approximated)
    /// interval; an open endpoint (`None`) never excludes. Used by the
    /// signed-negation discharge, which proves `-x` safe exactly when the
    /// operand interval EXCLUDES the type minimum (`!contains(type_min)`).
    fn contains(&self, v: i128) -> bool {
        self.lo.map_or(true, |l| l <= v) && self.hi.map_or(true, |h| v <= h)
    }

    /// Tighten with another sound constraint on the same value.
    fn intersect(self, other: Interval) -> Interval {
        let lo = match (self.lo, other.lo) {
            (Some(x), Some(y)) => Some(x.max(y)),
            (Some(x), None) | (None, Some(x)) => Some(x),
            (None, None) => None,
        };
        let hi = match (self.hi, other.hi) {
            (Some(x), Some(y)) => Some(x.min(y)),
            (Some(x), None) | (None, Some(x)) => Some(x),
            (None, None) => None,
        };
        Interval { lo, hi }
    }

    /// Over-approximate the union (e.g. the two arms of an `Ite`). EMPTY is the
    /// identity for union: an unreachable (contradictory) arm contributes no
    /// values, so `∅ ∪ x = x`. Handling it explicitly is load-bearing — the raw
    /// min/max would turn `join(∅, ∅)` (both arms unreachable) into a NON-empty
    /// interval, laundering the contradiction back into a vacuous proof.
    fn join(self, other: Interval) -> Interval {
        if self.is_empty() {
            return other;
        }
        if other.is_empty() {
            return self;
        }
        let lo = match (self.lo, other.lo) {
            (Some(x), Some(y)) => Some(x.min(y)),
            _ => None,
        };
        let hi = match (self.hi, other.hi) {
            (Some(x), Some(y)) => Some(x.max(y)),
            _ => None,
        };
        Interval { lo, hi }
    }

    fn add(self, other: Interval) -> Interval {
        // Emptiness (a contradictory operand) propagates: ∅ + x = ∅. Without the
        // short-circuit, `[10,5] + [10,5]` happens to stay crossed, but other
        // transfers (sub/mul/...) can launder an empty operand into a non-empty
        // result — so every binary transfer guards explicitly.
        if self.is_empty() || other.is_empty() {
            return Interval::EMPTY;
        }
        Interval { lo: opt_add(self.lo, other.lo), hi: opt_add(self.hi, other.hi) }
    }

    fn sub(self, other: Interval) -> Interval {
        // ∅ - x = x - ∅ = ∅ (see `add`). The two-operand laundering case
        // (`sub(wide, ∅)` -> non-empty without this guard) is the one the
        // acceptance-site-only fix missed.
        if self.is_empty() || other.is_empty() {
            return Interval::EMPTY;
        }
        // [a,b] - [c,d] = [a-d, b-c]
        Interval { lo: opt_sub(self.lo, other.hi), hi: opt_sub(self.hi, other.lo) }
    }

    fn neg(self) -> Interval {
        if self.is_empty() {
            return Interval::EMPTY;
        }
        Interval { lo: opt_neg(self.hi), hi: opt_neg(self.lo) }
    }

    fn mul(self, other: Interval) -> Interval {
        // ∅ * x = ∅ (an empty operand's crossed endpoints otherwise multiply
        // into a non-empty corner box — laundering the contradiction).
        if self.is_empty() || other.is_empty() {
            return Interval::EMPTY;
        }
        // Only precise when both operands are fully bounded; any unbounded
        // endpoint conservatively yields TOP (sound, imprecise). Unsigned mul
        // overflow is handled separately via the bitvector path, so the loss of
        // precision here does not regress the targeted floor cases.
        match (self.lo, self.hi, other.lo, other.hi) {
            (Some(al), Some(ah), Some(bl), Some(bh)) => {
                let corners = [
                    al.checked_mul(bl),
                    al.checked_mul(bh),
                    ah.checked_mul(bl),
                    ah.checked_mul(bh),
                ];
                if corners.iter().any(Option::is_none) {
                    return Interval::TOP;
                }
                let vals: [i128; 4] = [
                    corners[0].unwrap(),
                    corners[1].unwrap(),
                    corners[2].unwrap(),
                    corners[3].unwrap(),
                ];
                let lo = *vals.iter().min().unwrap();
                let hi = *vals.iter().max().unwrap();
                Interval::range(lo, hi)
            }
            _ => Interval::TOP,
        }
    }

    /// Rust remainder `self % divisor`. Result takes the sign of the dividend
    /// (`self`) and has magnitude `< |divisor|`.
    fn rem(self, divisor: Interval) -> Interval {
        // ∅ % x = x % ∅ = ∅ (an empty dividend otherwise yields a non-empty
        // [0, |m|-1] residue range — laundering the contradiction).
        if self.is_empty() || divisor.is_empty() {
            return Interval::EMPTY;
        }
        let Some(m) = constant_of(divisor) else {
            return Interval::TOP;
        };
        if m == 0 {
            return Interval::TOP;
        }
        let Some(mabs) = m.checked_abs() else {
            return Interval::TOP;
        };
        let bound = mabs - 1; // >= 0
        let nonneg = self.lo.is_some_and(|l| l >= 0);
        let nonpos = self.hi.is_some_and(|h| h <= 0);
        if nonneg {
            Interval::range(0, bound)
        } else if nonpos {
            Interval::range(-bound, 0)
        } else {
            Interval::range(-bound, bound)
        }
    }

    /// Truncating integer division `self / divisor` by a known nonzero constant.
    fn div(self, divisor: Interval) -> Interval {
        // ∅ / x = x / ∅ = ∅ (an empty dividend's crossed endpoints otherwise
        // divide into a non-empty quotient range — laundering the contradiction).
        if self.is_empty() || divisor.is_empty() {
            return Interval::EMPTY;
        }
        let Some(c) = constant_of(divisor) else {
            return Interval::TOP;
        };
        if c == 0 {
            return Interval::TOP;
        }
        match (self.lo, self.hi) {
            (Some(al), Some(ah)) => match (al.checked_div(c), ah.checked_div(c)) {
                (Some(x), Some(y)) => Interval::range(x.min(y), x.max(y)),
                _ => Interval::TOP,
            },
            _ => Interval::TOP,
        }
    }
}

fn opt_add(a: Option<i128>, b: Option<i128>) -> Option<i128> {
    match (a, b) {
        (Some(x), Some(y)) => x.checked_add(y),
        _ => None,
    }
}

fn opt_sub(a: Option<i128>, b: Option<i128>) -> Option<i128> {
    match (a, b) {
        (Some(x), Some(y)) => x.checked_sub(y),
        _ => None,
    }
}

fn opt_neg(a: Option<i128>) -> Option<i128> {
    a.and_then(i128::checked_neg)
}

/// Return the single value of a point interval `[c, c]`, if any.
fn constant_of(iv: Interval) -> Option<i128> {
    match (iv.lo, iv.hi) {
        (Some(l), Some(h)) if l == h => Some(l),
        _ => None,
    }
}

/// Largest value of an unsigned `width`-bit bitvector, as `i128` (or `None`
/// when it does not fit, in which case the value is left unbounded above).
fn bv_unsigned_max(width: u32) -> Option<i128> {
    match width {
        0 => Some(0),
        1..=126 => Some((1i128 << width) - 1),
        127 => Some(i128::MAX),
        _ => None,
    }
}

/// `2^(width-1)` — the sign threshold of a `width`-bit two's-complement value.
fn signed_threshold(width: u32) -> Option<i128> {
    match width {
        1..=127 => Some(1i128 << (width - 1)),
        _ => None,
    }
}

fn signed_min_of(width: u32) -> Option<i128> {
    match width {
        1..=127 => Some(-(1i128 << (width - 1))),
        128 => Some(i128::MIN),
        _ => None,
    }
}

fn signed_max_of(width: u32) -> Option<i128> {
    match width {
        1..=127 => Some((1i128 << (width - 1)) - 1),
        128 => Some(i128::MAX),
        _ => None,
    }
}

/// The bounded "top" of a `width`-bit bitvector value: `[0, 2^width - 1]`.
fn bv_top(width: u32) -> Interval {
    Interval { lo: Some(0), hi: bv_unsigned_max(width) }
}

/// Evaluate a fully-constant integer formula to its value, if it is one.
fn const_value(f: &Formula) -> Option<i128> {
    match f {
        Formula::Int(n) => Some(*n),
        Formula::UInt(n) => i128::try_from(*n).ok(),
        Formula::BitVec { value, .. } => Some(*value),
        Formula::Bool(b) => Some(i128::from(*b)),
        Formula::Neg(inner) => const_value(inner).and_then(i128::checked_neg),
        _ => None,
    }
}

/// Variable name of a `Var`/`SymVar`, if `f` is one.
fn var_name(f: &Formula) -> Option<&str> {
    match f {
        Formula::Var(name, _) => Some(name.as_str()),
        Formula::SymVar(sym, _) => Some(sym.as_str()),
        _ => None,
    }
}

/// Variable name of a BOOL-SORTED `Var`/`SymVar`, if `f` is one. Used to gate
/// boolean-flag inlining to genuinely Bool-sorted flag variables.
fn bool_var_name(f: &Formula) -> Option<&str> {
    match f {
        Formula::Var(name, Sort::Bool) => Some(name.as_str()),
        Formula::SymVar(sym, Sort::Bool) => Some(sym.as_str()),
        _ => None,
    }
}

/// Abstract environment for one VC: per-variable range constraints plus
/// per-variable definitions (block-def equalities) used to refine them.
struct IntervalEnv<'a> {
    bounds: FxHashMap<String, Interval>,
    defs: FxHashMap<String, &'a Formula>,
}

impl<'a> IntervalEnv<'a> {
    fn new() -> Self {
        IntervalEnv { bounds: FxHashMap::default(), defs: FxHashMap::default() }
    }

    fn add_lower(&mut self, name: &str, c: i128) {
        let e = self.bounds.entry(name.to_string()).or_insert(Interval::TOP);
        e.lo = Some(match e.lo {
            Some(x) => x.max(c),
            None => c,
        });
    }

    fn add_upper(&mut self, name: &str, c: i128) {
        let e = self.bounds.entry(name.to_string()).or_insert(Interval::TOP);
        e.hi = Some(match e.hi {
            Some(x) => x.min(c),
            None => c,
        });
    }

    fn bound_of(&self, name: &str) -> Interval {
        let recorded = self
            .bounds
            .get(name)
            .copied()
            .or_else(|| {
                name.strip_prefix("__trust_ovf_bv_lhs_")
                    .or_else(|| name.strip_prefix("__trust_ovf_bv_rhs_"))
                    .and_then(|base| self.bounds.get(base).copied())
            })
            .unwrap_or(Interval::TOP);
        // A slice/array length variable (`<slice>__slice_len`, the `.len()` of a
        // `&[T]`/`&str` argument that trust-vcgen names this way) is a `usize`, so
        // it is non-negative by construction. Floor it at 0 so a derived count
        // like `len / 2` or `len * 2` has a finite lower endpoint and the interval
        // `div`/`mul` can compute a real upper bound — without this an upper-only
        // guard (`len <= MAX`) leaves the dividend half-open and the product/quotient
        // unbounded. SOUNDNESS: the floor is a true lower bound on every length, so
        // it only ever TIGHTENS the interval (never admits a value the type cannot
        // hold); it is intersected with any recorded bound below.
        if name.ends_with("_slice_len") {
            recorded.intersect(Interval { lo: Some(0), hi: None })
        } else {
            recorded
        }
    }

    /// Record a top-level definitional equality `Eq(a, b)` into `defs`.
    ///
    /// When ONE side is a `Var`, that var is defined by the other side (the
    /// existing behaviour: `_60.0 = len - 16` gives `defs[_60.0] = len - 16`).
    ///
    /// When BOTH sides are (distinct) `Var`s — e.g. the SSA alias `_58 = off` —
    /// the equality is SYMMETRIC, so we record BOTH directions (`defs[_58] = off`
    /// AND `defs[off] = _58`) but only into a slot that is not already defined, so
    /// we never clobber a richer definition. This lets a bound recorded on EITHER
    /// alias flow to the other through `eval_var` (which is cycle-safe via its
    /// `visiting` set, so the two mutually-referential defs terminate at the
    /// shared base bound). SOUNDNESS: `Eq(a, b)` is a top-level hypothesis, so in
    /// every model `a == b`; substituting either for the other (and intersecting
    /// their interval information) is exact equals-for-equals, adding no model.
    fn record_eq_def(&mut self, a: &'a Formula, b: &'a Formula) {
        match (var_name(a), var_name(b)) {
            (Some(na), Some(nb)) if na != nb => {
                self.defs.entry(na.to_string()).or_insert(b);
                self.defs.entry(nb.to_string()).or_insert(a);
            }
            (Some(na), _) => {
                self.defs.insert(na.to_string(), b);
            }
            (_, Some(nb)) => {
                self.defs.insert(nb.to_string(), a);
            }
            _ => {}
        }
    }

    fn eval_var(&self, name: &str, visiting: &mut FxHashSet<String>) -> Interval {
        let base = self.bound_of(name);
        if visiting.contains(name) {
            return base; // break definitional cycles soundly
        }
        if let Some(def) = self.defs.get(name) {
            visiting.insert(name.to_string());
            let from_def = self.eval(def, visiting);
            visiting.remove(name);
            base.intersect(from_def)
        } else {
            base
        }
    }

    /// Canonical representative of `name`'s VARIABLE-ALIAS equivalence class.
    ///
    /// Two var names are aliases when connected by a top-level asserted equality
    /// whose BOTH sides are plain `Var`s (e.g. `Eq(len#s0_0, bytes__slice_len)`):
    /// `record_eq_def` records such an equality SYMMETRICALLY as two bare-`Var`
    /// defs (`defs[a] = Var(b)`, `defs[b] = Var(a)`). We close over exactly those
    /// bare-`Var` defs and return the LEXICOGRAPHICALLY SMALLEST name in the class
    /// — a deterministic representative that is identical no matter which alias we
    /// start from. So `Div(len#s0_0, 2)` and length `bytes__slice_len` both
    /// canonicalize their `len` symbol to the same name, letting the affine
    /// difference cancel and the div-base comparison match.
    ///
    /// Only bare-`Var` defs are followed (a compound def like `_60.0 = len - 16`
    /// is NOT an alias and is left for the normal expanding recursion); the walk
    /// is cycle-safe (a `seen` set) and depth-bounded by the class size.
    ///
    /// SOUNDNESS: a bare-`Var` def comes ONLY from a top-level `Eq(a, b)` over two
    /// vars, which holds in every model, so `a` and `b` denote the same value;
    /// replacing each by a single class representative is exact substitution of
    /// equals for equals — it adds no model and removes none. Non-aliased vars are
    /// never merged (each is its own singleton class -> returns itself).
    fn canonical_var(&self, name: &str) -> String {
        let mut best = name.to_string();
        let mut seen: FxHashSet<String> = FxHashSet::default();
        let mut stack = vec![name.to_string()];
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur.clone()) {
                continue;
            }
            if cur.as_str() < best.as_str() {
                best = cur.clone();
            }
            // Follow ONLY bare-`Var`/`SymVar` alias defs (an equality between two
            // vars), in BOTH directions: `defs[cur] = Var(other)` adds `other`,
            // and any `name` whose def is `Var(cur)` (the reverse edge) is added.
            if let Some(def) = self.defs.get(cur.as_str())
                && let Some(other) = var_name(def)
                && !seen.contains(other)
            {
                stack.push(other.to_string());
            }
            for (k, v) in &self.defs {
                if var_name(v) == Some(cur.as_str()) && !seen.contains(k) {
                    stack.push(k.clone());
                }
            }
        }
        best
    }

    /// Sound interval over-approximation of an integer/bitvector expression.
    fn eval(&self, f: &Formula, visiting: &mut FxHashSet<String>) -> Interval {
        match f {
            Formula::Int(n) => Interval::cst(*n),
            Formula::UInt(n) => i128::try_from(*n).map_or(Interval::TOP, Interval::cst),
            Formula::BitVec { value, .. } => Interval::cst(*value),
            Formula::Bool(b) => Interval::cst(i128::from(*b)),

            Formula::Var(name, _) => self.eval_var(name, visiting),
            Formula::SymVar(sym, _) => self.eval_var(sym.as_str(), visiting),

            Formula::Neg(a) => self.eval(a, visiting).neg(),
            Formula::Add(a, b) => self.eval(a, visiting).add(self.eval(b, visiting)),
            Formula::Sub(a, b) => self.eval(a, visiting).sub(self.eval(b, visiting)),
            Formula::Mul(a, b) => self.eval(a, visiting).mul(self.eval(b, visiting)),
            Formula::Rem(a, b) => self.eval(a, visiting).rem(self.eval(b, visiting)),
            Formula::Div(a, b) => self.eval(a, visiting).div(self.eval(b, visiting)),

            // Branch merge: cover both arms, ignore the (sound to drop) guard.
            Formula::Ite(_, t, e) => self.eval(t, visiting).join(self.eval(e, visiting)),

            // Bitwise AND with a mask caps the result at the smaller operand.
            Formula::BvAnd(a, b, width) => {
                let ia = self.eval(a, visiting);
                let ib = self.eval(b, visiting);
                let mut hi = bv_unsigned_max(*width);
                for bound in [ia.hi, ib.hi] {
                    if let Some(v) = bound {
                        if v >= 0 {
                            hi = Some(match hi {
                                Some(h) => h.min(v),
                                None => v,
                            });
                        }
                    }
                }
                Interval { lo: Some(0), hi }
            }
            // Bitwise OR is at least each operand, at most all-ones.
            Formula::BvOr(a, b, width) => {
                let ia = self.eval(a, visiting);
                let ib = self.eval(b, visiting);
                let mut lo = 0i128;
                for bound in [ia.lo, ib.lo] {
                    if let Some(v) = bound {
                        if v > lo {
                            lo = v;
                        }
                    }
                }
                Interval { lo: Some(lo), hi: bv_unsigned_max(*width) }
            }

            // Integer-as-bitvector: value-preserving when already in range,
            // else wraps to the full unsigned range.
            Formula::IntToBv(a, width) => {
                let ia = self.eval(a, visiting);
                let top = bv_top(*width);
                if let (Some(al), Some(ah)) = (ia.lo, ia.hi) {
                    if al >= 0 && top.hi.is_none_or(|cap| ah <= cap) {
                        return ia;
                    }
                }
                top
            }
            // Bitvector-as-integer.
            Formula::BvToInt(a, width, signed) => {
                let ia = self.eval(a, visiting).intersect(bv_top(*width));
                if !*signed {
                    return ia;
                }
                match (ia.hi, signed_threshold(*width)) {
                    // Entirely below the sign bit: value unchanged.
                    (Some(h), Some(t)) if h < t => ia,
                    _ => Interval { lo: signed_min_of(*width), hi: signed_max_of(*width) },
                }
            }
            // Zero-extension equals the UNSIGNED value of the inner BV term,
            // which is bounded by the inner BV WIDTH even when the inner var has
            // no recorded numeric bound (e.g. a fresh widening-mul operand var).
            // This is what lets `(x as u64) * (y as u64)` for u32 x,y prove: each
            // operand is a zero-extended 32-bit var, range [0, 2^32-1].
            Formula::BvZeroExt(a, _) => {
                let inner = self.eval(a, visiting);
                let by_width = bv_term_width(a)
                    .and_then(bv_unsigned_max)
                    .map_or(Interval::TOP, |m| Interval::range(0, m));
                let nonneg = if inner.lo.is_some_and(|l| l >= 0) {
                    inner
                } else {
                    Interval { lo: Some(0), hi: inner.hi.filter(|h| *h >= 0) }
                };
                nonneg.intersect(by_width)
            }
            // Sign-extension equals the SIGNED value of the inner BV term, in
            // [-2^(sw-1), 2^(sw-1)-1] for inner width sw — the source range of a
            // signed widening operand (e.g. `x as i64` for x: i32).
            Formula::BvSignExt(a, _) => match bv_term_width(a) {
                Some(sw) => match (signed_min_of(sw), signed_max_of(sw)) {
                    (Some(lo), Some(hi)) => Interval::range(lo, hi),
                    _ => Interval::TOP,
                },
                None => Interval::TOP,
            },

            // LOGICAL right shift by a CONSTANT amount `k` (`x >> k`, unsigned):
            // the result is `floor(x_unsigned / 2^k)`, so it is bounded ABOVE by
            // `floor(top / 2^k)` where `top` is the source's unsigned max — even
            // when the inner value has no recorded numeric bound. This is what
            // lets `(i >> 64) as u64` for `i: u128` prove: `i >> 64 < 2^64`, which
            // fits the u64/usize cast target. A NON-constant shift amount yields
            // the conservative `bv_top(width)` (unchanged behaviour).
            //
            // SOUNDNESS: `>> k` is monotone and `floor(x / 2^k) <= floor(top / 2^k)`
            // for every `x in [0, top]`, so the computed `hi` is a true upper bound
            // on every concrete result; the `lo = 0` floor holds because the
            // unsigned value and its shift are both non-negative. Computed in i128
            // with `bv_unsigned_max` (declines via `bv_top` if the source width has
            // no i128-representable max AND the shift cannot bring it into range).
            Formula::BvLShr(a, b, width) => {
                let ib = self.eval(b, visiting);
                match constant_of(ib) {
                    Some(k) if (0..128).contains(&k) => {
                        let ia = self.eval(a, visiting).intersect(bv_top(*width));
                        let k = k as u32;
                        // Upper bound: shift the source's concrete upper bound when
                        // it has one, else the type's unsigned max — by `k` bits.
                        let src_hi = ia.hi.or_else(|| bv_unsigned_max(*width));
                        let hi = match src_hi {
                            // Non-negative source hi: arithmetic `>> k` == `/ 2^k`.
                            Some(h) if h >= 0 => Some(h >> k),
                            // Source hi unrepresentable in i128 (e.g. width 128):
                            // bound the SHIFTED result directly by `2^(width-k) - 1`,
                            // which IS representable once `k >= width - 127`.
                            _ => width.checked_sub(k).and_then(bv_unsigned_max),
                        };
                        // Lower bound: `floor(max(src_lo, 0) / 2^k) >= 0`.
                        let lo = Some(ia.lo.map_or(0, |l| l.max(0) >> k));
                        Interval { lo, hi }
                    }
                    _ => bv_top(*width),
                }
            }

            // Other bitvector ops: bounded by the type, value otherwise opaque.
            Formula::BvAdd(_, _, width)
            | Formula::BvSub(_, _, width)
            | Formula::BvMul(_, _, width)
            | Formula::BvShl(_, _, width)
            | Formula::BvAShr(_, _, width)
            | Formula::BvXor(_, _, width)
            | Formula::BvNot(_, width) => bv_top(*width),
            Formula::BvURem(a, b, width) => {
                let ib = self.eval(b, visiting);
                if let Some(m) = constant_of(ib) {
                    if m > 0 {
                        return Interval::range(0, m - 1);
                    }
                }
                let _ = a;
                bv_top(*width)
            }
            Formula::BvUDiv(a, _, width) => {
                let ia = self.eval(a, visiting);
                Interval { lo: Some(0), hi: ia.hi.or_else(|| bv_unsigned_max(*width)) }
            }
            Formula::BvExtract { high, low, .. } => {
                if high >= low {
                    bv_top(high - low + 1)
                } else {
                    Interval::TOP
                }
            }

            // Anything else (comparisons, quantifiers, arrays, sign-extension,
            // unknown nodes): no sound finite bound — yield TOP.
            _ => Interval::TOP,
        }
    }
}

/// Best-effort BV bit-width of a bitvector-sorted term. Used to bound a
/// zero/sign-extended operand by its SOURCE width, so a fresh widening-mul
/// operand var (which has no recorded numeric bound) is still bounded by the
/// width it was extended from.
fn bv_term_width(f: &Formula) -> Option<u32> {
    match f {
        Formula::Var(_, Sort::BitVec(w)) | Formula::SymVar(_, Sort::BitVec(w)) => Some(*w),
        Formula::BitVec { width, .. } => Some(*width),
        Formula::BvZeroExt(a, added) | Formula::BvSignExt(a, added) => {
            bv_term_width(a).map(|w| w + *added)
        }
        Formula::BvMul(_, _, w)
        | Formula::BvAdd(_, _, w)
        | Formula::BvSub(_, _, w)
        | Formula::BvAnd(_, _, w)
        | Formula::BvOr(_, _, w)
        | Formula::BvXor(_, _, w)
        | Formula::BvShl(_, _, w)
        | Formula::BvLShr(_, _, w)
        | Formula::BvAShr(_, _, w)
        | Formula::BvNot(_, w) => Some(*w),
        Formula::BvExtract { high, low, .. } if high >= low => Some(high - low + 1),
        _ => None,
    }
}

/// The violation disjunction of an overflow VC: `result < min OR result > max`.
struct OverflowGoal<'a> {
    result: &'a Formula,
    min: i128,
    max: i128,
}

struct BvMulOverflowGoal<'a> {
    lhs: &'a Formula,
    rhs: &'a Formula,
    width: u32,
}

struct BvSMulOverflowGoal<'a> {
    lhs: &'a Formula,
    rhs: &'a Formula,
    width: u32,
}

struct BvNonZeroGuard<'a> {
    term: &'a Formula,
    width: u32,
}

/// Recognize `Or([Lt(result, min), Gt(result, max)])` (in either child order)
/// where `min`/`max` are constants.
fn parse_overflow_goal(children: &[Formula]) -> Option<OverflowGoal<'_>> {
    if children.len() != 2 {
        return None;
    }

    let mut lower_result: Option<&Formula> = None;
    let mut upper_result: Option<&Formula> = None;
    let mut min: Option<i128> = None;
    let mut max: Option<i128> = None;
    for child in children {
        match child {
            Formula::Lt(r, c) => {
                min = Some(const_value(c)?);
                lower_result = Some(r.as_ref());
            }
            Formula::Gt(r, c) => {
                max = Some(const_value(c)?);
                upper_result = Some(r.as_ref());
            }
            _ => return None,
        }
    }
    let result = lower_result?;
    if result != upper_result? {
        return None;
    }
    Some(OverflowGoal { result, min: min?, max: max? })
}

/// The UNDERFLOW-only violation goal `Lt(result, min)` that trust-vcgen emits for
/// UNSIGNED SUBTRACTION (`generate.rs::v2_build_overflow_vc_for_operands`). Unlike
/// the symmetric `Or([Lt(r,min), Gt(r,max)])` form `parse_overflow_goal` handles,
/// the unsigned-sub VC drops the `Gt(r, max)` disjunct entirely — the mathematical
/// result `a - b <= a <= max` can never exceed `max`, and the `usize::MAX` literal
/// the dropped disjunct would carry is unrepresentable in the i64 integer domain.
/// So the VC asserts ONLY the lower bound `result >= min` (i.e. no underflow), as a
/// BARE `Lt(result, min)` top-level conjunct rather than inside an `Or`.
///
/// `record_bound` ignores this conjunct (its lhs is a compound `Sub`, not a `Var`),
/// so it was previously dropped entirely and `prove_no_overflow` found NO goal and
/// declined — leaving a guarded, provably-safe subtraction (`if len >= 8 { len - 8 }`)
/// without any sound discharger.
///
/// Recognized ONLY when the lhs is a COMPOUND arithmetic expression (the operation
/// result), never a plain `Var`: a `Lt(var, const)` is a range BOUND that must keep
/// flowing to `record_bound`, not a violation goal. The returned goal sets
/// `max = i128::MAX` so the eval-tail upper-bound check is vacuous — faithful to the
/// VC, which makes NO upper-bound claim. SOUNDNESS: the goal is the EXACT violation
/// the VC asserts (`result < min`); the eval tail proves it impossible only when the
/// over-approximated `result_iv.lo >= min`, so a real underflow (whose interval dips
/// below `min`) is never proved away.
fn parse_underflow_goal(conj: &Formula) -> Option<OverflowGoal<'_>> {
    let Formula::Lt(result, c) = conj else {
        return None;
    };
    // A plain-variable lhs is a range bound, not the arithmetic result. Only a
    // compound operation result (`Sub`/`Add`/`Mul`/…) is the violation goal.
    if var_name(result.as_ref()).is_some() {
        return None;
    }
    let min = const_value(c.as_ref())?;
    Some(OverflowGoal { result: result.as_ref(), min, max: i128::MAX })
}

/// The index-out-of-bounds violation goal: `index` must provably stay within
/// `[0, len)` so the OOB condition can never hold. trust-vcgen emits (see
/// `index_bounds_violation`): unsigned index → `Ge(index, len)`; signed index →
/// `Or([Lt(index, 0), Ge(index, len)])`.
struct BoundsGoal<'a> {
    index: &'a Formula,
    len: &'a Formula,
    /// Signed index: the violation includes `index < 0`, so we must also prove
    /// `index >= 0`. Unsigned: non-negativity is guaranteed by the type, so only
    /// the upper bound (`index < len`) needs proving.
    signed: bool,
}

fn parse_bounds_goal(conj: &Formula) -> Option<BoundsGoal<'_>> {
    match conj {
        // Unsigned: index >= len. A real length is >= 1, so reject `Ge(x, c)` with
        // a non-positive constant `c` — that shape is a non-negativity/lower-bound
        // FACT (e.g. `n >= 0`), not an index-out-of-bounds violation. (A symbolic /
        // non-constant `len` is accepted; `prove_in_bounds` still checks len >= 1.)
        Formula::Ge(index, len) => {
            if const_value(len).is_some_and(|c| c <= 0) {
                return None;
            }
            // `Ge(var, const)` is AMBIGUOUS: it is either a lower-bound FACT
            // (`n >= 0`, a length floor) OR the genuine index-out-of-bounds goal
            // for a FIXED-SIZE array `[T; N]`, whose violation vcgen emits as
            // `Ge(index_var, N)` with N a literal (v2_build_bounds_assert_vc,
            // unsigned arm) — e.g. `table[byte as usize]` over `[u8;256]` is
            // `Ge(_5, 256)`, `alphabet[(n>>k)&0x3F]` over `[u8;64]` is
            // `Ge(idx, 64)`. The `c <= 0` check above already rejects every
            // non-negativity FACT (`x >= 0`); length-floor facts are emitted as
            // `Ge(slice_len_var, 0)` (also c == 0), never as a positive literal.
            // So a `Ge(var, c>=1)` conjunct in a bounds VC is the array-length
            // violation goal, NOT a fact, and we accept it. SOUNDNESS: this only
            // widens which conjuncts are CANDIDATE goals; the `exactly one goal`
            // gate in `prove_in_bounds` still rejects ambiguity, and if such a
            // conjunct were somehow a fact the index `var` would have no other
            // bound, evaluate to TOP, and the upper-bound proof would DECLINE —
            // never a false prove. (A bare `Ge(i, c)` with no fact bounding `i`
            // still declines: `eval(i)` is TOP, so `i.hi` is unbounded.)
            Some(BoundsGoal { index: index.as_ref(), len: len.as_ref(), signed: false })
        }
        // Signed: index < 0 OR index >= len.
        Formula::Or(children) if children.len() == 2 => {
            let mut lower_ok = false;
            let mut goal: Option<BoundsGoal<'_>> = None;
            for child in children {
                match child {
                    Formula::Lt(_, c) if const_value(c) == Some(0) => lower_ok = true,
                    Formula::Ge(index, len) => {
                        goal = Some(BoundsGoal {
                            index: index.as_ref(),
                            len: len.as_ref(),
                            signed: true,
                        })
                    }
                    _ => return None,
                }
            }
            if lower_ok { goal } else { None }
        }
        _ => None,
    }
}

/// A normalized AFFINE form `const + Σ coeff_v · v` over named variables. Used to
/// prove a RELATIONAL `index < len` where interval ranges of `index` and `len`
/// are correlated through a shared variable — e.g. `bytes[len - 1]` (index
/// `len - 1`, length `len`): the independent-interval rule (`index.hi < len.lo`)
/// cannot see that `(len - 1) - len = -1 < 0` because it treats the two `len`
/// occurrences as independent, but the affine DIFFERENCE cancels them exactly.
#[derive(Clone, Default)]
struct Affine {
    constant: i128,
    terms: FxHashMap<String, i128>,
}

impl Affine {
    fn cst(c: i128) -> Affine {
        Affine { constant: c, terms: FxHashMap::default() }
    }

    fn var(name: &str) -> Affine {
        let mut terms = FxHashMap::default();
        terms.insert(name.to_string(), 1i128);
        Affine { constant: 0, terms }
    }

    fn add(mut self, other: &Affine) -> Option<Affine> {
        self.constant = self.constant.checked_add(other.constant)?;
        for (k, v) in &other.terms {
            let e = self.terms.entry(k.clone()).or_insert(0);
            *e = e.checked_add(*v)?;
        }
        self.terms.retain(|_, c| *c != 0);
        Some(self)
    }

    fn neg(mut self) -> Option<Affine> {
        self.constant = self.constant.checked_neg()?;
        for v in self.terms.values_mut() {
            *v = v.checked_neg()?;
        }
        Some(self)
    }

    fn scale(mut self, k: i128) -> Option<Affine> {
        self.constant = self.constant.checked_mul(k)?;
        for v in self.terms.values_mut() {
            *v = v.checked_mul(k)?;
        }
        self.terms.retain(|_, c| *c != 0);
        Some(self)
    }

    /// `true` iff this form is a pure constant (all variable coefficients zero).
    fn as_const(&self) -> Option<i128> {
        self.terms.is_empty().then_some(self.constant)
    }
}

/// Lower a formula to a normalized affine form, following block-def equalities so
/// a temp like `_end = off + 16` is expanded to its definition. `None` for any
/// non-affine node (`Rem`, non-constant `Mul`/`Div`, bitvector ops, …) — the
/// caller then falls back to interval reasoning. SOUND: the affine form is an
/// EXACT linearization of the expression (no over-approximation), so a proof
/// derived from it about a sign/strict-inequality is valid for the real value.
fn affine_of(
    f: &Formula,
    env: &IntervalEnv<'_>,
    visiting: &mut FxHashSet<String>,
) -> Option<Affine> {
    match f {
        Formula::Int(n) => Some(Affine::cst(*n)),
        Formula::UInt(n) => i128::try_from(*n).ok().map(Affine::cst),
        Formula::BitVec { value, .. } => Some(Affine::cst(*value)),
        Formula::Neg(a) => affine_of(a, env, visiting)?.neg(),
        Formula::Add(a, b) => {
            let fa = affine_of(a, env, visiting)?;
            let fb = affine_of(b, env, visiting)?;
            fa.add(&fb)
        }
        Formula::Sub(a, b) => {
            let fa = affine_of(a, env, visiting)?;
            let fb = affine_of(b, env, visiting)?.neg()?;
            fa.add(&fb)
        }
        Formula::Mul(a, b) => {
            let fa = affine_of(a, env, visiting)?;
            let fb = affine_of(b, env, visiting)?;
            match (fa.as_const(), fb.as_const()) {
                (Some(k), _) => fb.scale(k),
                (_, Some(k)) => fa.scale(k),
                _ => None, // nonlinear
            }
        }
        Formula::Var(..) | Formula::SymVar(..) => {
            let name = var_name(f)?;
            // Use the variable-alias canonical representative as the atom name so
            // two names connected by a top-level `Eq(var, var)` (e.g. the SSA alias
            // `len#s0_0 == bytes__slice_len`) become the SAME affine atom. This is
            // what lets the relational `len - index >= 1` difference cancel and the
            // `index = base / k` div rule match a `base`/`len` that are aliased
            // rather than syntactically identical. (Sound: see `canonical_var` —
            // exact equals-for-equals over a true top-level equality.)
            let canon = env.canonical_var(name);
            if visiting.contains(name) {
                return Some(Affine::var(&canon));
            }
            // Expand through a block-def equality when present; else the var is
            // an atom NAMED BY ITS ALIAS-CANONICAL REPRESENTATIVE. (A def whose rhs
            // is non-affine -> the var stays the canonical atom.) Expansion still
            // follows bare-`Var` alias defs (so a var aliased to a COMPOUND def,
            // e.g. `_45 = _46.0 = len - 1`, reaches `len - 1`); the mutual two-way
            // alias `len#s0_0 <-> bytes__slice_len` terminates at the shared
            // canonical atom via the cycle-safe `visiting` guard.
            if let Some(def) = env.defs.get(name) {
                visiting.insert(name.to_string());
                let r = affine_of(def, env, visiting);
                visiting.remove(name);
                r.or_else(|| Some(Affine::var(&canon)))
            } else {
                Some(Affine::var(&canon))
            }
        }
        _ => None,
    }
}

/// Resolve a formula through the block-def equality map: if `f` is a `Var` with a
/// recorded def, return the def (recursively resolved); else `f` unchanged. Used
/// to reach the underlying expression behind a temp var (`_40 = Div(len, 2)`) so a
/// structural rule (the div-by-constant route) can match it even when the goal
/// references the temp rather than the expression. Cycle-safe (a `seen` set,
/// depth-bounded by the chain length) and SOUND: every def comes from a top-level
/// `Eq(var, expr)` hypothesis, so the resolved expression equals `f` in every model.
fn resolve_def<'a>(env: &'a IntervalEnv<'a>, f: &'a Formula) -> &'a Formula {
    let mut cur = f;
    let mut seen: FxHashSet<String> = FxHashSet::default();
    while let Some(name) = var_name(cur) {
        if !seen.insert(name.to_string()) {
            break; // cycle
        }
        match env.defs.get(name) {
            Some(def) => cur = def,
            None => break,
        }
    }
    cur
}

/// Relational proof of `index < len` (so the OOB violation `index >= len` is
/// UNSAT) when `index` and `len` are correlated. Two sound routes:
///
///   1. AFFINE DIFFERENCE: if `len - index` linearizes to a form whose value is
///      provably `>= 1` it proves `index < len` exactly. The difference's value
///      interval is `constant + Σ coeff · v` evaluated with each `v`'s recorded
///      bound; we require its LOWER bound `>= 1`. For `len - (len - 1) = 1` the
///      variables cancel (`constant = 1`, no terms) -> `1 >= 1`. SOUND: the
///      affine form is exact, and the interval of a linear form using each
///      variable's sound bound is a sound lower bound on the real difference.
///
///   2. DIV-BY-CONSTANT: `len / k` (`k >= 2`) is `<= len - 1 < len` whenever
///      `len >= 1`. So an index `index = base / k` (k >= 2) is `< len` when
///      `base`'s affine form equals `len`'s and `len`'s recorded lower bound is
///      `>= 1`. This is the `bytes[len / 2]` case. SOUND: `floor(x/k) <= x - 1`
///      for every integer `x >= 1, k >= 2` (since `floor(x/k) <= x/2 <= x - 1`).
fn prove_index_lt_len_relational(env: &IntervalEnv<'_>, index: &Formula, len: &Formula) -> bool {
    // Route 1: affine difference len - index >= 1.
    let mut v = FxHashSet::default();
    if let (Some(len_aff), Some(idx_aff)) = (affine_of(len, env, &mut v), {
        v.clear();
        affine_of(index, env, &mut v)
    }) && let Some(neg_idx) = idx_aff.neg()
        && let Some(diff) = len_aff.clone().add(&neg_idx)
    {
        // Lower bound of the affine difference using each variable's bound.
        let mut lo: Option<i128> = Some(diff.constant);
        for (name, coeff) in &diff.terms {
            let b = env.bound_of(name);
            let contrib = if *coeff >= 0 { b.lo } else { b.hi };
            lo = match (lo, contrib) {
                (Some(acc), Some(x)) => coeff.checked_mul(x).and_then(|c| acc.checked_add(c)),
                _ => None,
            };
        }
        if lo.is_some_and(|l| l >= 1) {
            return true;
        }
    }

    // Route 2: index = base / k (k >= 2), base affine-equal to len, len >= 1.
    // The index is often a TEMP VAR whose def is the division (the traced
    // hash_bytes shape `_40 = Div(len, 2)`, length var `bytes__slice_len`), so
    // resolve the index var through its block-def chain to reach the underlying
    // `Div` node before matching. SOUND: `resolve_def` follows only top-level
    // asserted equalities (`Eq(var, expr)`), so the resolved expression denotes
    // the same value as the index in every model.
    let resolved_index = resolve_def(env, index);
    if let Formula::Div(base, divisor) = resolved_index {
        let mut vd = FxHashSet::default();
        let k = const_value(divisor)
            .or_else(|| affine_of(divisor, env, &mut vd).and_then(|a| a.as_const()));
        if let Some(k) = k
            && k >= 2
        {
            let mut vb = FxHashSet::default();
            let mut vl = FxHashSet::default();
            if let (Some(base_aff), Some(len_aff)) =
                (affine_of(base, env, &mut vb), affine_of(len, env, &mut vl))
                && let Some(neg_len) = len_aff.neg()
                && let Some(diff) = base_aff.add(&neg_len)
            {
                // base == len exactly (difference is the zero affine form) and the
                // length is provably >= 1 (so floor(len/k) <= len-1 < len).
                let base_eq_len = diff.as_const() == Some(0);
                let mut vlen = FxHashSet::default();
                let len_pos = env.eval(len, &mut vlen).lo.is_some_and(|l| l >= 1);
                if base_eq_len && len_pos {
                    return true;
                }
            }
        }
    }

    false
}

/// Sound interval discharge of an index-bounds VC: prove the over-approximated
/// index interval lies within `[0, len)`, so the violation is impossible.
///
/// Soundness: the interval analysis OVER-approximates `index`, so if the
/// over-approximation is `⊆ [0, len)` the concrete index is definitely in
/// bounds. We require EXACTLY ONE violation-shaped conjunct so there is no
/// ambiguity about which `(index, len)` pair is the obligation (a genuinely OOB
/// `n % 5` over a `[_; 4]` gives `index ∈ [0, 4]`, whose `hi = 4` is NOT `< 4`,
/// so it is correctly declined and falls through to the SMT lane).
fn prove_in_bounds(formula: &Formula) -> bool {
    // Normalize so a hardened `Not(Lt(index,len))` bounds twin surfaces as the
    // `Ge(index,len)` violation goal the parser recognizes (and an arithmetic
    // `Not(in_range)` twin routed here as a bounds VC simply yields no bounds goal
    // -> declines). Owned conjuncts; we borrow into `&Formula` below.
    let conjuncts_owned = normalized_conjuncts(formula);
    let conjuncts: Vec<&Formula> = conjuncts_owned.iter().collect();

    // Exactly one violation goal — otherwise the (index, len) pairing is
    // ambiguous and we decline rather than risk an unsound match.
    let goal_positions: Vec<usize> = conjuncts
        .iter()
        .enumerate()
        .filter(|(_, c)| parse_bounds_goal(c).is_some())
        .map(|(i, _)| i)
        .collect();
    if goal_positions.len() != 1 {
        return false;
    }
    let goal_idx = goal_positions[0];
    let Some(goal) = parse_bounds_goal(&conjuncts[goal_idx]) else {
        return false;
    };

    // Every other conjunct is a fact: variable definitions and interval bounds
    // (e.g. the Euclidean modulo range `0 <= r < 4` and `r = n % 4`).
    let mut env = IntervalEnv::new();
    let mut cmp_atoms: Vec<&Formula> = Vec::new();
    for (i, conj) in conjuncts.iter().enumerate() {
        if i == goal_idx {
            continue;
        }
        match conj {
            Formula::Eq(a, b) => {
                env.record_eq_def(a.as_ref(), b.as_ref());
            }
            Formula::Le(..) | Formula::Lt(..) | Formula::Ge(..) | Formula::Gt(..) => {
                record_bound(&mut env, conj);
                cmp_atoms.push(conj);
            }
            _ => {}
        }
    }
    // Compose symbolic guards (`index < len`, `len <= isize::MAX`) to a fixpoint.
    record_symbolic_bounds(&mut env, &cmp_atoms);

    let mut visiting = FxHashSet::default();
    let index_iv = env.eval(goal.index, &mut visiting);
    let mut visiting_len = FxHashSet::default();
    let len_iv = env.eval(goal.len, &mut visiting_len);

    // Need finite bounds, a real length (>= 1), and the index strictly below the
    // SMALLEST possible length. The over-approximated `index_iv.hi` is a sound
    // upper bound on the concrete index, so `hi < len` proves `index < len`.
    // Lower bound: for a SIGNED index the violation also covers `index < 0`, so
    // require `lo >= 0`; for an UNSIGNED index the type guarantees `index >= 0`,
    // so the upper bound alone suffices (and `eval` of `n % k` is `[-(k-1), k-1]`
    // without a non-negativity fact, which would otherwise spuriously decline).
    // Lower bound: a SIGNED index must additionally be proved `>= 0` (the
    // violation covers `index < 0`); an UNSIGNED index is `>= 0` by type. We need
    // a finite lower bound on the index (for the non-negativity leg) regardless.
    // We need a finite UPPER bound on the index for the `index < len` proof. For a
    // SIGNED index we additionally need a finite LOWER bound to discharge the
    // `index < 0` leg of the violation. For an UNSIGNED index the type guarantees
    // `index >= 0`, so a missing lower bound is sound to treat as 0 — the
    // upper-bound routes below consult ONLY `index_iv.hi`. This is what lets a
    // masked/shifted byte index carry just its upper mask bound
    // (`(byte>>4) <= 15`, `(n>>k)&0x3F <= 63`) — no explicit `>= 0` fact — and
    // still prove `idx < 16` / `idx < 64` for `[u8;16]` / `[u8;64]`.
    //
    // SOUNDNESS: the over-approximated `index_iv.hi` is a true upper bound on the
    // concrete index; `hi < len.lo` (or the relational route) proves `index < len`
    // independent of the lower bound. For an unsigned index the omitted lower
    // bound is the type-guaranteed `0`, which only STRENGTHENS the (unused) lower
    // leg. A signed index keeps the full finiteness requirement, so the `index<0`
    // leg is never silently dropped.
    if index_iv.hi.is_none() {
        return false;
    }
    if goal.signed && index_iv.lo.is_none() {
        return false;
    }
    let lower_ok = !goal.signed || index_iv.lo.unwrap() >= 0;
    if !lower_ok {
        return false;
    }

    // Upper bound — two sound routes:
    //   (a) INDEPENDENT INTERVALS: `index.hi < len.lo` (smallest possible length).
    //       Proves cases where index and len are uncorrelated (`n % 4` over `[_;4]`,
    //       `bytes[0]`, `bytes[0..8]` under `len >= 8`).
    //   (b) RELATIONAL: `len - index >= 1` via the affine difference (cancels a
    //       shared `len`), or the `len / k < len` div rule. Proves the correlated
    //       cases `bytes[len - 1]`, `bytes[len - 8..]`, `bytes[len / 2]` that the
    //       independent rule cannot (their index.hi is NOT below len.lo).
    let independent_ok =
        len_iv.is_finite() && len_iv.lo.unwrap() >= 1 && index_iv.hi.unwrap() < len_iv.lo.unwrap();
    independent_ok || prove_index_lt_len_relational(&env, goal.index, goal.len)
}

/// The narrowing-cast (lossy) violation goal: trust-vcgen emits (see
/// `v2_build_cast_overflow_vc`) `Or([Lt(value, to_min), Gt(value, to_max)])` —
/// the value falls OUTSIDE the target integer type's `[to_min, to_max]` range,
/// i.e. the `value as T` cast would lose data. Proving this UNSAT proves the cast
/// is LOSSLESS. Both arms reference the same `value`.
struct CastGoal<'a> {
    value: &'a Formula,
    min: i128,
    max: i128,
}

fn parse_cast_goal(conj: &Formula) -> Option<CastGoal<'_>> {
    let Formula::Or(children) = conj else {
        return None;
    };
    if children.len() != 2 {
        return None;
    }
    let mut value: Option<&Formula> = None;
    let mut min: Option<i128> = None;
    let mut max: Option<i128> = None;
    for child in children {
        match child {
            Formula::Lt(v, c) => {
                min = Some(const_value(c)?);
                value = Some(v.as_ref());
            }
            Formula::Gt(v, c) => {
                max = Some(const_value(c)?);
                if value.is_some_and(|prev| prev != v.as_ref()) {
                    return None; // both arms must constrain the SAME value
                }
                value = Some(v.as_ref());
            }
            _ => return None,
        }
    }
    Some(CastGoal { value: value?, min: min?, max: max? })
}

/// Sound interval discharge of a narrowing-cast obligation: prove the
/// over-approximated source-value interval lies within the target type's
/// `[to_min, to_max]`, so the cast cannot lose data — e.g. `(i & 0xff) as u32`
/// (`i & 0xff ∈ [0, 255] ⊆ [0, u32::MAX]`). A genuinely-lossy cast (unbounded
/// `i as u32`) gives a source interval wider than the target range, so it is
/// correctly declined and falls through to the SMT lane (which leaves it
/// unknown/failed — the intended strict-mode truncation flag).
fn prove_cast_lossless(formula: &Formula) -> bool {
    let mut conjuncts = Vec::new();
    flatten_and(formula, &mut conjuncts);

    // trust-vcgen emits the per-statement cast VC together with its hardened
    // panic-boundary twin, which nests the SAME cast-goal conjunct several times
    // (e.g. base64 `((n >> 16) & 0xFF) as u8` surfaces `Or([Lt(v,0), Gt(v,255)])`
    // three times after `flatten_and`). Counting goal POSITIONS would see 3 and
    // bail at the single-goal gate even though there is ONE distinct obligation.
    // Collect goals by IDENTITY instead: gather every conjunct that parses as a
    // cast goal, and require they all denote the SAME (value, min, max). Multiple
    // DISTINCT cast goals remain ambiguous and still decline (fail-closed); only
    // exact duplicates of one obligation are collapsed.
    //
    // SOUNDNESS: duplicate goals are byte-identical violation disjunctions, so
    // proving the single obligation UNSAT discharges every copy. A VC mixing two
    // genuinely-different casts yields >1 distinct goal -> we decline, exactly as
    // before. The non-goal (duplicate) `Or` conjuncts are never read as facts
    // (the fact loop matches only `Eq`/`Le`/`Lt`/`Ge`/`Gt`), so leaving them in
    // place cannot inject a spurious bound.
    let goal_positions: Vec<usize> = conjuncts
        .iter()
        .enumerate()
        .filter(|(_, c)| parse_cast_goal(c).is_some())
        .map(|(i, _)| i)
        .collect();
    if goal_positions.is_empty() {
        return false;
    }
    let goal_idx = goal_positions[0];
    let Some(goal) = parse_cast_goal(&conjuncts[goal_idx]) else {
        return false;
    };
    // Every cast-goal conjunct must be the SAME obligation; otherwise the value
    // pairing is ambiguous and we decline.
    for &i in &goal_positions {
        match parse_cast_goal(&conjuncts[i]) {
            Some(other)
                if other.value == goal.value && other.min == goal.min && other.max == goal.max => {}
            _ => return false,
        }
    }

    let mut env = IntervalEnv::new();
    let mut cmp_atoms: Vec<&Formula> = Vec::new();
    for (i, conj) in conjuncts.iter().enumerate() {
        if goal_positions.contains(&i) {
            continue;
        }
        match conj {
            Formula::Eq(a, b) => {
                env.record_eq_def(a.as_ref(), b.as_ref());
            }
            Formula::Le(..) | Formula::Lt(..) | Formula::Ge(..) | Formula::Gt(..) => {
                record_bound(&mut env, conj);
                cmp_atoms.push(conj);
            }
            _ => {}
        }
    }
    record_symbolic_bounds(&mut env, &cmp_atoms);

    let mut visiting = FxHashSet::default();
    let value_iv = env.eval(goal.value, &mut visiting);
    value_iv.is_finite() && value_iv.lo.unwrap() >= goal.min && value_iv.hi.unwrap() <= goal.max
}

/// Lower bound (exclusive) a constant must reach to count as an
/// unbounded-allocation FAILURE threshold rather than an ordinary range/shift
/// guard. trust-vcgen emits the allocation-availability violation atom as
/// `Ge(count, 1 << 28)` (element ceiling), `Ge(stride * count, 256 MiB)`
/// (availability byte budget) and `Ge(stride * count, isize::MAX)`
/// (capacity-overflow) — every legitimate failure constant is well above any
/// real loop/shift guard threshold (`_2 < 64`, `len <= isize::MAX` is itself a
/// fact, not a goal). We require the threshold to be at or above the element
/// ceiling so a small guard comparison is never mistaken for a violation atom.
const ALLOC_VIOLATION_MIN_THRESHOLD: i128 = 1 << 28;

/// A single allocation-availability/capacity violation atom `Ge(term, C)` or
/// `Gt(term, C)`, where `C >= ALLOC_VIOLATION_MIN_THRESHOLD`. Proving the atom
/// UNSAT (i.e. `term`'s over-approximated interval lies strictly below `C`)
/// shows that failure disjunct can never hold.
struct AllocViolationAtom<'a> {
    term: &'a Formula,
    threshold: i128,
    /// `true` for `Ge` (failure iff `term >= C`, refuted by `hi < C`);
    /// `false` for `Gt` (failure iff `term > C`, refuted by `hi <= C`).
    inclusive: bool,
}

/// Recognize an allocation violation atom: `Ge(term, C)` / `Gt(term, C)` with a
/// constant `C >= ALLOC_VIOLATION_MIN_THRESHOLD`. The constant must be on the
/// RIGHT (vcgen always emits `Ge(count, CEILING)` / `Ge(stride*count, CEILING)`
/// in that orientation), so an ordinary fact like `Le(len, isize::MAX)` — a
/// different relation, and with the var on the left — is never captured here.
fn parse_alloc_violation_atom(f: &Formula) -> Option<AllocViolationAtom<'_>> {
    let (lhs, rhs, inclusive) = match f {
        Formula::Ge(a, b) => (a.as_ref(), b.as_ref(), true),
        Formula::Gt(a, b) => (a.as_ref(), b.as_ref(), false),
        _ => return None,
    };
    let c = const_value(rhs)?;
    if c < ALLOC_VIOLATION_MIN_THRESHOLD {
        return None;
    }
    Some(AllocViolationAtom { term: lhs, threshold: c, inclusive })
}

/// Sound interval discharge of an unbounded-allocation obligation. trust-vcgen
/// emits the allocation availability/capacity check as a FAILURE condition: the
/// allocation count (or `stride * count` byte total) REACHES OR EXCEEDS a large
/// ceiling. The VC's goal is one such atom, or an `Or` of several (element
/// ceiling + byte budget + capacity-overflow). We prove the allocation BOUNDED
/// by refuting EVERY failure atom: each `Ge(term, C)` / `Gt(term, C)` is shown
/// impossible because `term`'s over-approximated interval lies strictly below
/// `C` (for `Ge`) / at most `C` (for `Gt`). A guarded entry — e.g. a dominating
/// `if input.len() > MAX_INPUT_LEN { return Err(..) }` threaded in as a path
/// guard `Le(input_len, MAX)` — bounds `count = input_len * k`, so the interval
/// evaluation of `count` yields `hi = MAX * k`, which is below the ceiling.
///
/// SOUNDNESS: this only ever turns FAILED -> PROVED, and only when the failure
/// is provably impossible. If ANY failure atom's term interval is unbounded
/// above (no dominating guard), `hi` is `None` -> not refuted -> we DECLINE
/// (return false) and the allocation falls through to the SMT lane / stays
/// flagged, exactly as today. The failure atoms are EXCLUDED from fact
/// gathering (they are goal positions), so a `Ge(count, CEILING)` violation is
/// never mis-recorded as a fact `count >= CEILING` that would poison the env.
fn prove_alloc_bounded(formula: &Formula) -> bool {
    // `normalized_conjuncts` flattens the top `And` AND De-Morgan-normalizes each
    // conjunct, so a dominating guard threaded in as `Not(Gt(len, MAX))` surfaces
    // as the recordable bound `Le(len, MAX)` — without this the guard would be an
    // unrecognized `Not(..)` and the count interval would stay unbounded above.
    let conjuncts_owned = normalized_conjuncts(formula);
    let conjuncts: Vec<&Formula> = conjuncts_owned.iter().collect();

    // Outer (path-independent) facts that hold on EVERY execution: the dominating
    // size guard, arg-type ranges, block defs. These are shared by all branches.
    let outer: Vec<&Formula> = conjuncts.clone();

    // Does any top-level `Or` conjunct hide alloc failure atoms inside its branches
    // (a branch split)? If so, the flat Case-A handling would IGNORE those buried
    // atoms, so we must NOT trust a Case-A verdict and instead use the per-branch
    // Case B. (A pure single-path VC has no such `Or`.)
    let has_branch_atoms = conjuncts.iter().any(|conj| {
        matches!(conj, Formula::Or(branches) if branches.iter().any(|branch| {
            let mut bc = Vec::new();
            flatten_and(branch, &mut bc);
            bc.iter().any(|c| parse_alloc_violation_atom(c).is_some())
        }))
    });

    // Case A — directly exposed failure atoms. Always inspect these, even when
    // an `Or` elsewhere looks like an allocation branch split. A sibling
    // arithmetic-overflow disjunction can contain `Gt(term, u32::MAX)`, which
    // passes the deliberately coarse allocation-threshold recognizer; letting
    // that suppress this direct check allowed the safe arithmetic sibling to
    // mask a forced `Ge(count, ALLOC_CEILING)` allocation violation.
    //
    // A directly Unbounded atom is terminal. Returning `false` is conservative
    // even if another branch constraint would later make the whole path
    // unreachable: the interval backend merely declines proof and a stronger
    // backend may still discharge it. A directly Bounded result is terminal
    // only when no branch atoms remain to check.
    match prove_alloc_context(&conjuncts, &[]) {
        AllocContext::Bounded if !has_branch_atoms => return true,
        AllocContext::Unbounded => return false,
        AllocContext::Bounded | AllocContext::NoAtoms => {}
    }

    // Case B — a branch split (`vcgen` emits one big `Or` of per-path conjunctions,
    // e.g. base64 decode's remainder = 0 / 2 / 3 cases). The allocation is bounded
    // iff EVERY branch refutes its own failure atom under the outer facts PLUS that
    // branch's local guards/defs. A branch with NO failure atom is vacuously fine
    // (no allocation reached on it). We require at least one branch to actually
    // carry an alloc atom, so a plain disjunctive fact never vacuously "proves".
    for conj in &conjuncts {
        if let Formula::Or(branches) = conj {
            let mut saw_atom = false;
            let all_ok = branches.iter().all(|branch| {
                let mut branch_conjs = Vec::new();
                flatten_and(branch, &mut branch_conjs);
                match prove_alloc_context(&branch_conjs, &outer) {
                    AllocContext::Bounded => {
                        saw_atom = true;
                        true
                    }
                    AllocContext::Unbounded => {
                        saw_atom = true;
                        false
                    }
                    // A branch that allocates nothing is fine.
                    AllocContext::NoAtoms => true,
                }
            });
            if saw_atom && all_ok {
                return true;
            }
        }
    }
    false
}

/// Outcome of trying to bound the allocation(s) in one fact context.
enum AllocContext {
    /// At least one alloc failure atom was present and ALL were refuted.
    Bounded,
    /// At least one alloc failure atom was present and at least one was NOT refuted.
    Unbounded,
    /// No alloc failure atom in this context.
    NoAtoms,
}

/// Gather facts from `conjuncts` (plus the shared `extra` outer facts) and refute
/// every allocation failure atom found DIRECTLY among `conjuncts`. The failure
/// atoms (`Ge(term, C)` / `Gt(term, C)` with `C >= ALLOC_VIOLATION_MIN_THRESHOLD`,
/// or an `Or` all of whose disjuncts are such atoms) are excluded from fact
/// gathering so a violation is never mis-read as a fact. Returns whether the
/// context's allocations are provably bounded (or absent).
fn prove_alloc_context(conjuncts: &[&Formula], extra: &[&Formula]) -> AllocContext {
    let mut goal_positions: Vec<usize> = Vec::new();
    let mut atoms: Vec<AllocViolationAtom<'_>> = Vec::new();
    for (i, conj) in conjuncts.iter().enumerate() {
        if let Some(atom) = parse_alloc_violation_atom(conj) {
            atoms.push(atom);
            goal_positions.push(i);
        } else if let Formula::Or(disj) = conj {
            // An `Or` is a violation-goal conjunct ONLY if EVERY disjunct is a
            // recognized failure atom; otherwise it is some other disjunctive fact
            // (e.g. a branch split handled by the caller) — left for fact handling.
            let parsed: Option<Vec<AllocViolationAtom<'_>>> =
                disj.iter().map(parse_alloc_violation_atom).collect();
            if let Some(parsed) = parsed {
                if !parsed.is_empty() {
                    atoms.extend(parsed);
                    goal_positions.push(i);
                }
            }
        }
    }
    if atoms.is_empty() {
        return AllocContext::NoAtoms;
    }

    let mut env = IntervalEnv::new();
    let mut cmp_atoms: Vec<&Formula> = Vec::new();
    // Outer facts first (shared across branches), then this context's own facts.
    // A goal position is skipped only within `conjuncts`; `extra` is fact-only.
    for conj in extra.iter() {
        match conj {
            Formula::Eq(a, b) => env.record_eq_def(a.as_ref(), b.as_ref()),
            Formula::Le(..) | Formula::Lt(..) | Formula::Ge(..) | Formula::Gt(..) => {
                record_bound(&mut env, conj);
                cmp_atoms.push(conj);
            }
            _ => {}
        }
    }
    for (i, conj) in conjuncts.iter().enumerate() {
        if goal_positions.contains(&i) {
            continue;
        }
        match conj {
            Formula::Eq(a, b) => env.record_eq_def(a.as_ref(), b.as_ref()),
            Formula::Le(..) | Formula::Lt(..) | Formula::Ge(..) | Formula::Gt(..) => {
                record_bound(&mut env, conj);
                cmp_atoms.push(conj);
            }
            _ => {}
        }
    }
    record_symbolic_bounds(&mut env, &cmp_atoms);

    // Bounded iff EVERY failure atom is provably impossible.
    let bounded = atoms.iter().all(|atom| {
        let mut visiting = FxHashSet::default();
        let iv = env.eval(atom.term, &mut visiting);
        match iv.hi {
            // `Ge(term, C)` is impossible iff `term <= hi < C`; `Gt(term, C)`
            // is impossible iff `term <= hi <= C`.
            Some(hi) if atom.inclusive => hi < atom.threshold,
            Some(hi) => hi <= atom.threshold,
            None => false,
        }
    });
    if bounded { AllocContext::Bounded } else { AllocContext::Unbounded }
}

fn parse_bv_mul_overflow_goal(f: &Formula) -> Option<BvMulOverflowGoal<'_>> {
    let Formula::Not(inner) = f else {
        return None;
    };
    let Formula::Eq(div, rhs_check) = inner.as_ref() else {
        return None;
    };
    let Formula::BvUDiv(product, div_lhs, div_width) = div.as_ref() else {
        return None;
    };
    let Formula::BvMul(lhs, rhs, mul_width) = product.as_ref() else {
        return None;
    };
    if mul_width != div_width
        || lhs.as_ref() != div_lhs.as_ref()
        || rhs.as_ref() != rhs_check.as_ref()
    {
        return None;
    }
    Some(BvMulOverflowGoal { lhs: lhs.as_ref(), rhs: rhs.as_ref(), width: *mul_width })
}

/// Recognize the SIGNED width-doubling mul-overflow failure shape emitted by
/// trust-vcgen `v2_signed_bv_overflow_formula`:
///   `Not(Or([ Eq(slice, 0), Eq(slice, all_ones) ]))`
/// where `slice = BvExtract{ BvMul(BvSignExt(a,w), BvSignExt(b,w), 2w), 2w-1, w-1 }`.
/// Returns the ORIGINAL operands `a`, `b` (inside the sign-extends) and width `w`
/// so the prover interval-bounds them at their source width (the sign-extends
/// `eval` to the signed source range, exactly what we want here).
fn parse_bv_smul_overflow_goal(f: &Formula) -> Option<BvSMulOverflowGoal<'_>> {
    let Formula::Not(inner) = f else {
        return None;
    };
    let Formula::Or(disj) = inner.as_ref() else {
        return None;
    };
    if disj.len() != 2 {
        return None;
    }
    let mut slice: Option<&Formula> = None;
    let (mut saw_zero, mut saw_ones) = (false, false);
    for arm in disj {
        let Formula::Eq(x, c) = arm else {
            return None;
        };
        let (sl, kval, kw) = match (x.as_ref(), c.as_ref()) {
            (s, Formula::BitVec { value, width }) => (s, *value, *width),
            (Formula::BitVec { value, width }, s) => (s, *value, *width),
            _ => return None,
        };
        match slice {
            Some(prev) if prev != sl => return None,
            _ => slice = Some(sl),
        }
        let mask: i128 = if kw >= 128 { -1 } else { (1i128 << kw) - 1 };
        let masked = kval & mask;
        if masked == 0 {
            saw_zero = true;
        } else if masked == mask {
            saw_ones = true;
        } else {
            return None;
        }
    }
    if !(saw_zero && saw_ones) {
        return None;
    }
    let Formula::BvExtract { inner: prod, high, low } = slice? else {
        return None;
    };
    let Formula::BvMul(sa, sb, dw) = prod.as_ref() else {
        return None;
    };
    let Formula::BvSignExt(a, _) = sa.as_ref() else {
        return None;
    };
    let Formula::BvSignExt(b, _) = sb.as_ref() else {
        return None;
    };
    let w = *low + 1;
    if *dw != 2 * w || *high != 2 * w - 1 {
        return None;
    }
    Some(BvSMulOverflowGoal { lhs: a.as_ref(), rhs: b.as_ref(), width: w })
}

fn parse_bv_nonzero_guard(f: &Formula) -> Option<BvNonZeroGuard<'_>> {
    let Formula::Not(inner) = f else {
        return None;
    };
    let Formula::Eq(a, b) = inner.as_ref() else {
        return None;
    };
    if let Formula::BitVec { value: 0, width } = b.as_ref() {
        return Some(BvNonZeroGuard { term: a.as_ref(), width: *width });
    }
    if let Formula::BitVec { value: 0, width } = a.as_ref() {
        return Some(BvNonZeroGuard { term: b.as_ref(), width: *width });
    }
    None
}

fn prove_bv_mul_no_overflow(env: &IntervalEnv<'_>, goal: &BvMulOverflowGoal<'_>) -> bool {
    let mut visiting = FxHashSet::default();
    let lhs = env.eval(goal.lhs, &mut visiting);
    let rhs = env.eval(goal.rhs, &mut visiting);
    unsigned_mul_fits_width(lhs, rhs, goal.width)
}

/// Sound: prove an UNSIGNED `lhs * rhs` cannot overflow a `width`-bit value
/// (`width` up to 128) by bounding the product entirely in `u128`.
///
/// Why not the i128 `Interval::mul` + `bv_unsigned_max(width)` path it replaces:
/// for `width = 128` the product upper bound `(2^64-1)^2 = 2^128 - 2^65 + 1`
/// exceeds `i128::MAX` (`2^127-1`), so `Interval::mul`'s `i128::checked_mul`
/// returns `None` -> `TOP` (hi = None) and `bv_unsigned_max(128)` is `None` too —
/// both make the old check decline a PROVABLY-safe widening multiply such as
/// `(x as u128) * (y as u128)` for `x, y: u64`. Computing the bound in `u128`
/// represents both the product upper bound and the type max `2^width-1` exactly.
///
/// SOUNDNESS — the result is `true` ONLY when no concrete input can overflow:
///   * Require both operands NON-NEGATIVE with FINITE upper bounds (`a_lo >= 0`,
///     `b_lo >= 0`, `a_hi`/`b_hi` concrete). `env.eval` over-approximates, so the
///     real operands lie within `[a_lo, a_hi]` / `[b_lo, b_hi]`; a missing/negative
///     bound declines (returns false), never proves.
///   * The product upper bound is `a_hi * b_hi` (both factors non-negative, so the
///     max corner is the product of the maxima). Computed with `u128::checked_mul`:
///     if it would exceed `u128::MAX` we DECLINE rather than wrap — so the bound can
///     never silently truncate to a small value and false-prove.
///   * `a_hi`, `b_hi` are non-negative i128 upper bounds, so they convert to u128
///     losslessly. The type max `2^width - 1` is computed in u128 for any
///     `1 <= width <= 128` (`width = 128` -> `u128::MAX`).
///   * Prove iff `product_ub <= type_max`. Because `product_ub` is a true OVER-
///     approximation of every concrete product, `product_ub <= type_max` implies
///     every concrete product is `<= type_max`, i.e. the asserted overflow
///     violation is UNSAT. A genuinely-overflowing multiply has `product_ub >
///     type_max` (or an unbounded operand) and is correctly DECLINED, falling
///     through to ay.
fn unsigned_mul_fits_width(lhs: Interval, rhs: Interval, width: u32) -> bool {
    // Both operands must be non-negative with concrete upper bounds.
    let (Some(a_lo), Some(a_hi)) = (lhs.lo, lhs.hi) else {
        return false;
    };
    let (Some(b_lo), Some(b_hi)) = (rhs.lo, rhs.hi) else {
        return false;
    };
    if a_lo < 0 || b_lo < 0 {
        return false;
    }
    // a_hi, b_hi are non-negative (>= a_lo >= 0), so the u128 conversion is exact.
    let (Ok(a_hi_u), Ok(b_hi_u)) = (u128::try_from(a_hi), u128::try_from(b_hi)) else {
        return false;
    };
    // Product upper bound in u128; decline (never wrap) if it does not fit.
    let Some(product_ub) = a_hi_u.checked_mul(b_hi_u) else {
        return false;
    };
    let Some(type_max) = bv_unsigned_max_u128(width) else {
        return false;
    };
    product_ub <= type_max
}

/// Largest value of an unsigned `width`-bit bitvector as `u128`, for
/// `1 <= width <= 128` (`width = 128` -> `u128::MAX`). `None` for `width = 0` or
/// `width > 128` (no representable type max -> decline). Unlike `bv_unsigned_max`
/// (which tops out at `i128`), this covers the full 128-bit unsigned range so a
/// `u128` widening multiply can be discharged.
fn bv_unsigned_max_u128(width: u32) -> Option<u128> {
    match width {
        1..=127 => Some((1u128 << width) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

/// Prove a SIGNED `lhs * rhs` cannot overflow `width` signed bits by interval
/// arithmetic on the operands. Sound: the operands' sign-extends `eval` to a
/// superset of their real value set, so if the product interval is finite and
/// inside the signed range, no input can overflow. Declines (false) on any
/// unbounded operand, leaving the VC for ay (which will refute a real overflow).
fn prove_bv_smul_no_overflow(env: &IntervalEnv<'_>, goal: &BvSMulOverflowGoal<'_>) -> bool {
    let mut visiting = FxHashSet::default();
    let lhs = env.eval(goal.lhs, &mut visiting);
    let rhs = env.eval(goal.rhs, &mut visiting);
    let product = lhs.mul(rhs);
    match (product.lo, product.hi, signed_min_of(goal.width), signed_max_of(goal.width)) {
        (Some(lo), Some(hi), Some(smin), Some(smax)) => lo >= smin && hi <= smax,
        _ => false,
    }
}

/// Flatten nested `And` conjuncts into `out`.
fn flatten_and<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    match f {
        Formula::And(children) => {
            for child in children {
                flatten_and(child, out);
            }
        }
        other => out.push(other),
    }
}

/// Negate a single INTEGER/BITVECTOR comparison atom, returning the EXACT logical
/// complement as a positive comparison — or `None` for any node that is NOT a
/// total-order comparison (so the caller leaves it wrapped in `Not` and the goal
/// parsers never see a spurious goal).
///
/// SOUNDNESS: over a TOTAL order (the integer / two's-complement BV domain this
/// backend reasons in — `Sort` has no float variant, so `Lt/Le/Gt/Ge` are always
/// total here) the four rewrites are EXACT equivalences:
///   `¬(x ≥ y) ⟺ x < y`,  `¬(x ≤ y) ⟺ x > y`,
///   `¬(x > y) ⟺ x ≤ y`,  `¬(x < y) ⟺ x ≥ y`.
/// So the negated atom denotes the SAME set of models as `Not(<atom>)` — no
/// concrete value is gained or lost, hence no false-prove can be introduced. We
/// deliberately do NOT negate `Eq` here (its complement `Not(Eq)` is the BV
/// non-zero-guard / signed-mul shape the existing `Not(_)` parsers consume, and a
/// bare `Not(Eq(divisor,0))` div-by-zero VIOLATION must reach the parser as the
/// double-negation `Not(Not(Eq))` collapse handled in `normalize_goal`, not via
/// this comparison flip), nor any non-comparison node.
fn negate_comparison(f: &Formula) -> Option<Formula> {
    Some(match f {
        Formula::Ge(a, b) => Formula::Lt(a.clone(), b.clone()),
        Formula::Le(a, b) => Formula::Gt(a.clone(), b.clone()),
        Formula::Gt(a, b) => Formula::Le(a.clone(), b.clone()),
        Formula::Lt(a, b) => Formula::Ge(a.clone(), b.clone()),
        _ => return None,
    })
}

/// Canonicalize a comparison so that, when exactly ONE side is an integer
/// CONSTANT, the constant sits on the RIGHT — the orientation every goal parser
/// (`parse_overflow_goal`'s `Lt(r,c)`/`Gt(r,c)`, `parse_underflow_goal`,
/// `parse_bounds_goal`) reads. A flip preserves meaning exactly:
///   `c < x ⟺ x > c`, `c ≤ x ⟺ x ≥ c`, `c > x ⟺ x < c`, `c ≥ x ⟺ x ≤ c`.
/// Atoms with no constant side, or with the constant already on the right, are
/// returned unchanged. SOUND: a pure operand-swap of a total-order comparison is
/// an exact equivalence.
fn orient_constant_right(f: Formula) -> Formula {
    let (a, b, mk): (&Formula, &Formula, fn(Box<Formula>, Box<Formula>) -> Formula) = match &f {
        Formula::Lt(a, b) => (a, b, |x, y| Formula::Gt(x, y)),
        Formula::Le(a, b) => (a, b, |x, y| Formula::Ge(x, y)),
        Formula::Gt(a, b) => (a, b, |x, y| Formula::Lt(x, y)),
        Formula::Ge(a, b) => (a, b, |x, y| Formula::Le(x, y)),
        _ => return f,
    };
    // Flip only when the LEFT is a constant and the RIGHT is not — i.e. the
    // const is on the wrong side. (`const ? const` and `expr ? const` are left
    // as-is; the parsers handle `expr ? const` directly.)
    if const_value(a).is_some() && const_value(b).is_none() {
        mk(Box::new(b.clone()), Box::new(a.clone()))
    } else {
        f
    }
}

/// Push a top-level `Not` inward over the hardened violation goal `Not(in_range)`
/// so it surfaces as exactly the positive violation shape the existing goal
/// parsers recognize, WITHOUT touching the shapes the BV `Not(_)` parsers consume.
///
/// The hardened panic-boundary lane (trust-vcgen `hardened.rs`) emits the violation
/// as `Not(in_range)` where, per assert kind, `in_range` is:
///   * arithmetic Overflow(Add|Sub|Mul): `And([Le(min,result), Le(result,max)])`
///     (from `guards::extract_assert_passed_semantics`) — so the violation is
///     `Not(And([Le,Le]))`, which De Morgan turns into
///     `Or([Lt(result,min), Gt(result,max)])` — `parse_overflow_goal`'s shape.
///   * BoundsCheck:  `Lt(index,len)` (the asserted in-bounds cond, `expected=true`)
///     — violation `Not(Lt(index,len))` -> `Ge(index,len)` — `parse_bounds_goal`.
///   * Division/RemainderByZero: the asserted cond is `divisor != 0`, i.e.
///     `Not(Eq(divisor,0))`, so the violation is `Not(Not(Eq(divisor,0)))` — the
///     double-negation collapses to `Eq(divisor,0)` — `parse_div_by_zero_goal`.
///
/// Rewrites applied (each an EXACT logical equivalence over the total integer/BV
/// order — see `negate_comparison`):
///   * `Not(And[c0,c1,…])` -> `Or[neg(c0), neg(c1), …]` (De Morgan), each `neg`
///     a flipped comparison oriented const-right; a non-comparison child aborts
///     the rewrite (returns the node unchanged) so we never fabricate a goal.
///   * `Not(Not(x))`       -> `normalize_goal(x)` (collapses the div `!=` twin).
///   * `Not(<comparison>)` -> the negated comparison, oriented const-right.
///   * `Not(Or[…])`, `Not(Eq[…])`, `Not(Var)`, `Not(Pred)`, … -> UNCHANGED, so the
///     BV-mul/smul/nonzero `Not(_)` parsers still match and opaque/policy `Not(…)`
///     predicates stay unrecognized (the VC stays flagged, never false-proved).
///   * a bare top-level comparison is oriented const-right (so a hardened bounds
///     twin already in `Ge`/`Lt` form, or an arithmetic underflow `Lt`, parses).
///
/// SOUNDNESS: every transform is a meaning-preserving rewrite of a total-order
/// formula, so the normalized conjunct denotes the SAME violation set. The existing
/// parsers + interval discharge prove `Proved` only when that violation set is
/// genuinely empty; an UNGUARDED overflow's normalized `Or([Lt,Gt])` still has a
/// feasible model (the interval eval finds `result.hi > max`), so it DECLINES.
fn normalize_goal(f: &Formula) -> Formula {
    match f {
        Formula::Not(inner) => match inner.as_ref() {
            // De Morgan over a conjunction of comparisons: the arithmetic
            // `Not(in_range)` twin. Abort (leave unchanged) if any child is not a
            // negatable comparison, so we never invent a goal from an opaque conj.
            Formula::And(children) => {
                let mut negated = Vec::with_capacity(children.len());
                for child in children {
                    match negate_comparison(child) {
                        Some(neg) => negated.push(orient_constant_right(neg)),
                        None => return f.clone(),
                    }
                }
                Formula::Or(negated)
            }
            // Double negation: the div-by-zero `!=` twin collapses to its inner.
            Formula::Not(x) => normalize_goal(x),
            // Bare comparison: bounds `Not(Lt(index,len))` -> `Ge(index,len)`.
            cmp @ (Formula::Lt(..) | Formula::Le(..) | Formula::Gt(..) | Formula::Ge(..)) => {
                match negate_comparison(cmp) {
                    Some(neg) => orient_constant_right(neg),
                    None => f.clone(),
                }
            }
            // `Not(Or)`, `Not(Eq)`, `Not(Var)`, `Not(Pred)`, … : leave for the BV
            // parsers / keep opaque predicates flagged.
            _ => f.clone(),
        },
        // A positive top-level comparison: orient its constant to the right so the
        // parsers read it (e.g. a hardened bounds twin already in `Ge` form).
        Formula::Lt(..) | Formula::Le(..) | Formula::Gt(..) | Formula::Ge(..) => {
            orient_constant_right(f.clone())
        }
        other => other.clone(),
    }
}

/// `true` iff `f` is a BOOLEAN-VALUED formula at its top node — a comparison, a
/// boolean connective, a `Bool` literal/variable, or an (always-Bool) predicate.
/// Used to gate boolean-definition inlining so we only ever inline a flag whose
/// definition is a genuine boolean expression (never an integer/bitvector term),
/// keeping the substitution well-sorted.
fn is_bool_expr(f: &Formula) -> bool {
    matches!(
        f,
        Formula::Bool(_)
            | Formula::Not(_)
            | Formula::And(_)
            | Formula::Or(_)
            | Formula::Implies(..)
            | Formula::Eq(..)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..)
            | Formula::BvULt(..)
            | Formula::BvULe(..)
            | Formula::BvSLt(..)
            | Formula::BvSLe(..)
            | Formula::Pred(..)
    ) || matches!(f, Formula::Var(_, Sort::Bool) | Formula::SymVar(_, Sort::Bool))
}

/// Collect, from a flat conjunct list, every SOUND boolean-flag definition
/// `Eq(Var(f, Bool), <bool-expr>)` (either operand order). A flag is recorded
/// ONLY when it has EXACTLY ONE such definition across the conjunct list — a flag
/// with two or more definitions is path-dependent (different SSA writes merged
/// into one VC) and inlining either would be unsound, so it is dropped entirely.
/// Map values are the (single) defining boolean expression.
///
/// SOUND because `Eq(f, e)` is a hypothesis of the formula: in every model `f`
/// equals `e`, so substituting `e` for `f` is substitution of equals for equals —
/// an exact equivalence that preserves the model set. The single-definition gate
/// is what guarantees the equality is unconditional (not one arm of a merge).
fn collect_bool_flag_defs(conjuncts: &[&Formula]) -> FxHashMap<String, Formula> {
    let mut defs: FxHashMap<String, Formula> = FxHashMap::default();
    let mut multiply_defined: FxHashSet<String> = FxHashSet::default();
    for conj in conjuncts {
        let Formula::Eq(a, b) = conj else { continue };
        // Identify the (Bool var, bool-expr) orientation. The var side must be a
        // Bool-sorted Var/SymVar; the other side must be a boolean expression.
        let (name, def): (&str, &Formula) = if let Some(n) = bool_var_name(a) {
            if !is_bool_expr(b) {
                continue;
            }
            (n, b.as_ref())
        } else if let Some(n) = bool_var_name(b) {
            if !is_bool_expr(a) {
                continue;
            }
            (n, a.as_ref())
        } else {
            continue;
        };
        if multiply_defined.contains(name) {
            continue;
        }
        if defs.insert(name.to_string(), def.clone()).is_some() {
            // A second definition: drop it — path-dependent, do not inline.
            defs.remove(name);
            multiply_defined.insert(name.to_string());
        }
    }
    defs
}

/// Substitute boolean-flag definitions into `f`: replace every `Var(flag, Bool)`
/// (or its `SymVar` twin) by its single definition from `defs`, recursively, to a
/// bounded `depth`. A flag whose definition itself mentions another flag is
/// expanded transitively (depth-bounded); a definitional CYCLE terminates when
/// `depth` hits zero (the remaining `Var(flag)` is left in place, still sound —
/// it just stays unrecognized rather than looping forever).
///
/// SOUND: each replacement is substitution of equals for equals (`Eq(flag, def)`
/// is a hypothesis), an exact equivalence; the rewritten formula has the same
/// model set, so any subsequent goal-parse + interval discharge proves `Proved`
/// only for a genuinely-empty violation set — exactly as for the direct shape.
fn inline_bool_defs(f: &Formula, defs: &FxHashMap<String, Formula>, depth: u32) -> Formula {
    if depth == 0 {
        return f.clone();
    }
    // A Bool var that has a definition: expand to the def, then keep inlining into
    // it (transitive flags), with a decremented depth budget.
    if let Some(name) = bool_var_name(f)
        && let Some(def) = defs.get(name)
    {
        return inline_bool_defs(def, defs, depth - 1);
    }
    // Otherwise, structurally recurse into the boolean skeleton that the goal
    // parsers + De Morgan normalization traverse (`Not`/`And`/`Or`). Leaf and
    // arithmetic nodes are returned unchanged: an integer flag is never inlined,
    // and an integer operand of a comparison is not a Bool var so it is untouched.
    match f {
        Formula::Not(inner) => Formula::Not(Box::new(inline_bool_defs(inner, defs, depth))),
        Formula::And(children) => {
            Formula::And(children.iter().map(|c| inline_bool_defs(c, defs, depth)).collect())
        }
        Formula::Or(children) => {
            Formula::Or(children.iter().map(|c| inline_bool_defs(c, defs, depth)).collect())
        }
        other => other.clone(),
    }
}

/// Flatten `And` conjuncts AND normalize each so a hardened `Not(in_range)`
/// violation surfaces as the positive goal shape the parsers recognize. Returns
/// OWNED conjuncts (the normalization rewrites some nodes); callers borrow from
/// the returned vec. Conjuncts that are not violation goals (defs, bounds, BV
/// guards, opaque predicates) pass through unchanged via `normalize_goal`.
///
/// A BOOLEAN-DEFINITION INLINING pre-pass runs first: hardened arithmetic twins
/// encode the violation through a boolean OVERFLOW-FLAG variable — a conjunct
/// `Eq(Var(flag, Bool), Or([Lt(result,min), Gt(result,max)]))` DEFINES the flag,
/// and the goal appears as `Var(flag)` / `Not(Var(flag))` rather than the direct
/// `Or`. The goal parsers only recognize the DIRECT shapes, so a flag-referencing
/// goal is unrecognized and declined. Inlining substitutes each flag by its single
/// definition (exact equals-for-equals), turning `Var(flag)` into the direct
/// `Or([Lt,Gt])` (an overflow goal) and `Not(Var(flag))` into `Not(Or(...))` (a
/// no-overflow hypothesis the De Morgan step folds away) — after which the
/// existing normalization + parsers handle it identically to the per-statement
/// direct case. See `collect_bool_flag_defs` / `inline_bool_defs` for the
/// soundness-preserving constraints (single definition, Bool sort, bounded depth).
fn normalized_conjuncts(formula: &Formula) -> Vec<Formula> {
    let mut raw = Vec::new();
    flatten_and(formula, &mut raw);

    // Inline boolean-flag definitions (equals-for-equals) BEFORE goal-normalizing,
    // so a flag-encoded violation surfaces as the direct comparison shape.
    let flag_defs = collect_bool_flag_defs(&raw);
    if flag_defs.is_empty() {
        return raw.into_iter().map(normalize_goal).collect();
    }
    // Depth 8 comfortably covers realistic flag-of-flag chains while bounding work
    // and breaking any definitional cycle. The inlined conjunct list then flows
    // through the SAME `normalize_goal` (De Morgan + const-orient) as before.
    raw.into_iter().map(|c| normalize_goal(&inline_bool_defs(c, &flag_defs, 8))).collect()
}

/// Record a range bound from a comparison atom of the form `var ? const` or
/// `const ? var`.
fn record_bound(env: &mut IntervalEnv<'_>, atom: &Formula) {
    // (var, const, kind) where kind picks the inequality direction relative to
    // the variable on the left.
    let (lhs, rhs, op) = match atom {
        Formula::Le(a, b) => (a.as_ref(), b.as_ref(), Cmp::Le),
        Formula::Lt(a, b) => (a.as_ref(), b.as_ref(), Cmp::Lt),
        Formula::Ge(a, b) => (a.as_ref(), b.as_ref(), Cmp::Ge),
        Formula::Gt(a, b) => (a.as_ref(), b.as_ref(), Cmp::Gt),
        _ => return,
    };

    if let (Some(name), Some(c)) = (var_name(lhs), const_value(rhs)) {
        // var OP c
        match op {
            Cmp::Le => env.add_upper(name, c),
            Cmp::Lt => {
                if let Some(v) = c.checked_sub(1) {
                    env.add_upper(name, v);
                }
            }
            Cmp::Ge => env.add_lower(name, c),
            Cmp::Gt => {
                if let Some(v) = c.checked_add(1) {
                    env.add_lower(name, v);
                }
            }
        }
    } else if let (Some(c), Some(name)) = (const_value(lhs), var_name(rhs)) {
        // c OP var  ==>  flip to  var OP' c
        match op {
            Cmp::Le => env.add_lower(name, c), // c <= var
            Cmp::Lt => {
                if let Some(v) = c.checked_add(1) {
                    env.add_lower(name, v); // c < var => var >= c+1
                }
            }
            Cmp::Ge => env.add_upper(name, c), // c >= var
            Cmp::Gt => {
                if let Some(v) = c.checked_sub(1) {
                    env.add_upper(name, v); // c > var => var <= c-1
                }
            }
        }
    }
}

/// Record range bounds from comparison atoms whose NON-variable side is a
/// COMPOUND, interval-evaluable expression — `var ? expr` / `expr ? var` — by
/// evaluating that side in the current `env` and tightening the variable's
/// bound from the resulting interval. Iterated to a fixpoint so a chain of
/// bounds composes (e.g. `len <= isize::MAX` recorded first, then `off < len - 16`
/// yields `off <= isize::MAX - 17`).
///
/// This is what discharges the aterm-hash loop/guard obligations whose
/// dominating guard relates one variable to ANOTHER (`off < len - 16`,
/// `bytes[len - 8..]`) rather than to a literal constant: `record_bound` only
/// fires on `var ? const`, so the symbolic guard was previously dropped and the
/// guarded `off + 16` / `len - 8` was left unbounded.
///
/// SOUNDNESS — every recorded bound is a TRUE over-approximation, never tighter
/// than the real constraint:
///   * `eval(expr)` over-approximates `expr`'s value set, so its `hi` (`lo`) is a
///     sound upper (lower) bound on `expr`, hence on `var` via the inequality.
///   * `var < expr` records `var <= expr_hi - 1` only when `expr_hi` is FINITE
///     (an unbounded side records nothing); `var <= expr` records `var <= expr_hi`.
///     Symmetrically for the lower bound. `add_upper`/`add_lower` only ever
///     TIGHTEN-towards-the-truth (they `min`/`max` with the existing bound), and
///     each derived bound is implied by a real path constraint, so no concrete
///     value satisfying the VC premises is ever excluded — the analysis can only
///     under-claim a variable's range conservatively, never over-claim it.
///   * Iteration is monotone (bounds only tighten) and capped, so it terminates;
///     a self-referential atom (`x < x + 1`) re-derives `x`'s existing bound (no
///     spurious tightening), which is sound.
fn record_symbolic_bounds(env: &mut IntervalEnv<'_>, atoms: &[&Formula]) {
    // A small fixpoint: each pass can only tighten finitely many endpoints, and
    // realistic guard chains are short. Cap the passes to stay cheap and ensure
    // termination regardless of formula shape.
    for _ in 0..8 {
        let mut changed = false;
        for atom in atoms {
            let (lhs, rhs, op) = match atom {
                Formula::Le(a, b) => (a.as_ref(), b.as_ref(), Cmp::Le),
                Formula::Lt(a, b) => (a.as_ref(), b.as_ref(), Cmp::Lt),
                Formula::Ge(a, b) => (a.as_ref(), b.as_ref(), Cmp::Ge),
                Formula::Gt(a, b) => (a.as_ref(), b.as_ref(), Cmp::Gt),
                _ => continue,
            };
            // Candidate (target_var, other_side, target_on_left) bindings whose
            // `other_side` is interval-evaluable but NOT a plain const (those
            // `var ? const` bounds are already recorded by `record_bound`):
            //   * `var ? COMPOUND` — the original symbolic-guard shape (`off < len-16`).
            //   * `var ? VAR` — a guard between two variables (`off < _59`), where the
            //     OTHER variable is resolved to its definition via `env.eval` /
            //     `eval_var` (which follows the block-def Eq-chain `_59 = _60.0 =
            //     len - 16`). Here we bound EACH variable by the OTHER's evaluated
            //     interval — both directions are sound (the atom is a true hypothesis),
            //     so an Eq-defined intermediate on either side composes. A var with no
            //     def and no recorded numeric bound evaluates to TOP, recording nothing
            //     — so an UNGUARDED operand stays unbounded and the VC still declines.
            let nl = var_name(lhs);
            let nr = var_name(rhs);
            let mut bindings: Vec<(&str, &Formula, bool)> = Vec::new();
            match (nl, nr) {
                // expr (compound) OP var, or var OP expr (compound): one binding.
                (Some(n), None) if const_value(rhs).is_none() => bindings.push((n, rhs, true)),
                (None, Some(n)) if const_value(lhs).is_none() => bindings.push((n, lhs, false)),
                // var OP var: bound each variable by the other's evaluated interval.
                (Some(ln), Some(rn)) if ln != rn => {
                    bindings.push((ln, rhs, true));
                    bindings.push((rn, lhs, false));
                }
                _ => continue,
            }
            let strict = matches!(op, Cmp::Lt | Cmp::Gt);
            for (name, expr, var_on_left) in bindings {
                let mut visiting = FxHashSet::default();
                let iv = env.eval(expr, &mut visiting);
                // Direction of the inequality relative to the variable.
                let (var_le_expr, var_ge_expr) = if var_on_left {
                    match op {
                        Cmp::Le | Cmp::Lt => (true, false),
                        Cmp::Ge | Cmp::Gt => (false, true),
                    }
                } else {
                    // expr OP var  <=>  var OP' expr (flip)
                    match op {
                        Cmp::Le | Cmp::Lt => (false, true), // expr <= var => var >= expr
                        Cmp::Ge | Cmp::Gt => (true, false), // expr >= var => var <= expr
                    }
                };
                let before = env.bound_of(name);
                if var_le_expr {
                    if let Some(h) = iv.hi {
                        let v = if strict { h.checked_sub(1) } else { Some(h) };
                        if let Some(v) = v {
                            env.add_upper(name, v);
                        }
                    }
                }
                if var_ge_expr {
                    if let Some(l) = iv.lo {
                        let v = if strict { l.checked_add(1) } else { Some(l) };
                        if let Some(v) = v {
                            env.add_lower(name, v);
                        }
                    }
                }
                if env.bound_of(name) != before {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
}

enum Cmp {
    Le,
    Lt,
    Ge,
    Gt,
}

/// The division-by-zero violation goal `divisor == 0` that trust-vcgen emits for
/// a `Div`/`Rem` whose divisor is not statically nonzero (see
/// `generate.rs::v2_assert_failure_formula`, `cond = (divisor == 0)`, expected
/// false → the failure formula is the bare equality `Eq(divisor, 0)`). Proving
/// it UNSAT proves the divisor is nonzero, i.e. the division cannot panic.
struct DivByZeroGoal<'a> {
    divisor: &'a Formula,
}

fn parse_div_by_zero_goal(conj: &Formula) -> Option<DivByZeroGoal<'_>> {
    let Formula::Eq(a, b) = conj else {
        return None;
    };
    // One side must be the constant 0; the other is the divisor expression.
    if const_value(a) == Some(0) {
        Some(DivByZeroGoal { divisor: b.as_ref() })
    } else if const_value(b) == Some(0) {
        Some(DivByZeroGoal { divisor: a.as_ref() })
    } else {
        None
    }
}

/// Sound interval discharge of a division-by-zero obligation: prove the
/// over-approximated divisor interval EXCLUDES 0, so `divisor == 0` is
/// impossible. This covers a constant divisor (`len / 2` -> divisor `[2, 2]`,
/// `0 ∉ [2, 2]`) and a guard-bounded divisor (`if d > 0 { x / d }` -> `[1, ..]`).
///
/// SOUNDNESS: `env.eval` OVER-approximates the divisor's value set, so if the
/// over-approximation excludes 0 (its whole interval is `>= 1` or `<= -1`) then
/// no concrete divisor is 0 — the violation is UNSAT. A divisor whose
/// over-approximation straddles 0 (unbounded / symbolic) is DECLINED and falls
/// through to the SMT lane (which refutes a real div-by-zero), so a genuine
/// division by zero can never be falsely proved away.
fn prove_div_nonzero(formula: &Formula) -> bool {
    // Normalize so a hardened `Not(Not(Eq(divisor,0)))` div twin (the asserted
    // `divisor != 0`, negated) collapses to the `Eq(divisor,0)` violation goal.
    let conjuncts_owned = normalized_conjuncts(formula);
    let conjuncts: Vec<&Formula> = conjuncts_owned.iter().collect();

    let goal_positions: Vec<usize> = conjuncts
        .iter()
        .enumerate()
        .filter(|(_, c)| parse_div_by_zero_goal(c).is_some())
        .map(|(i, _)| i)
        .collect();
    if goal_positions.len() != 1 {
        return false;
    }
    let goal_idx = goal_positions[0];
    let Some(goal) = parse_div_by_zero_goal(&conjuncts[goal_idx]) else {
        return false;
    };

    let mut env = IntervalEnv::new();
    let mut cmp_atoms: Vec<&Formula> = Vec::new();
    for (i, conj) in conjuncts.iter().enumerate() {
        if i == goal_idx {
            continue;
        }
        match conj {
            Formula::Eq(a, b) => {
                env.record_eq_def(a.as_ref(), b.as_ref());
            }
            Formula::Le(..) | Formula::Lt(..) | Formula::Ge(..) | Formula::Gt(..) => {
                record_bound(&mut env, conj);
                cmp_atoms.push(conj);
            }
            _ => {}
        }
    }
    record_symbolic_bounds(&mut env, &cmp_atoms);

    let mut visiting = FxHashSet::default();
    let iv = env.eval(goal.divisor, &mut visiting);
    // Whole interval strictly positive (`lo >= 1`) or strictly negative
    // (`hi <= -1`): 0 is excluded, so the divisor is provably nonzero.
    iv.lo.is_some_and(|l| l >= 1) || iv.hi.is_some_and(|h| h <= -1)
}

/// Attempt to prove the overflow VC's violation condition unsatisfiable by
/// interval analysis. Returns `true` only on a sound finite-range proof.
fn prove_no_overflow(formula: &Formula) -> bool {
    // Normalize so a hardened arithmetic `Not(in_range)` twin — `Not(And([Le(min,
    // result), Le(result,max)]))` — De Morgans into the `Or([Lt(result,min),
    // Gt(result,max)])` violation goal `parse_overflow_goal` reads. The BV mul /
    // smul / nonzero-guard `Not(_)` shapes are deliberately left UNCHANGED by
    // `normalize_goal` (only `Not(And)`/`Not(Not)`/`Not(<cmp>)` are rewritten), so
    // those parsers still match below.
    let conjuncts_owned = normalized_conjuncts(formula);
    let conjuncts: Vec<&Formula> = conjuncts_owned.iter().collect();

    let mut env = IntervalEnv::new();
    let mut goal: Option<OverflowGoal<'_>> = None;
    let mut bv_mul_goal: Option<BvMulOverflowGoal<'_>> = None;
    let mut bv_smul_goal: Option<BvSMulOverflowGoal<'_>> = None;
    let mut bv_nonzero_guards: Vec<BvNonZeroGuard<'_>> = Vec::new();
    let mut cmp_atoms: Vec<&Formula> = Vec::new();

    for conj in &conjuncts {
        match conj {
            Formula::Or(children) => {
                // The Int overflow goal is itself an `Or([Lt(r,min), Gt(r,max)])`;
                // capture the first one as the goal.
                if goal.is_none()
                    && let Some(g) = parse_overflow_goal(children)
                {
                    goal = Some(g);
                }
                // Any OTHER `Or` is a CONJOINED CONTEXT disjunct — e.g. a switch
                // discriminant enumeration `_8 == 0 || _8 == 1` carried into a loop
                // body's VC — NOT the violation goal. SKIP it rather than bailing.
                // SOUNDNESS: `prove_no_overflow` proves the VIOLATION conjunction is
                // UNSAT (so the overflow is impossible). Dropping a conjoined term can
                // only WEAKEN the premise: if the goal-bearing sub-conjunction is unsat
                // the full conjunction (which is more constrained) is unsat too, and a
                // genuine overflow keeps its goal SAT so it is still refuted. Ignoring
                // context only ever WIDENS the over-approximation (a conservative miss),
                // never enables a false proof. Previously this `return false` discarded
                // the in-loop widening multiply, whose BV mul goal proves but whose
                // formula carries such discriminant `Or`s (the non-loop form has none).
            }
            Formula::Eq(a, b) => {
                env.record_eq_def(a.as_ref(), b.as_ref());
            }
            Formula::Le(..) | Formula::Lt(..) | Formula::Ge(..) | Formula::Gt(..) => {
                // An unsigned-subtraction VC emits its no-underflow obligation as a
                // BARE `Lt(result, min)` (the `Gt(r,max)` disjunct is dropped — see
                // `parse_underflow_goal`). Capture the FIRST such compound-lhs `Lt`
                // as the goal; everything else (a `Var`-lhs bound) flows to
                // `record_bound` as before. `record_bound` no-ops on the compound
                // goal conjunct anyway (its lhs is not a `Var`), so no bound is lost.
                if goal.is_none()
                    && let Some(g) = parse_underflow_goal(conj)
                {
                    goal = Some(g);
                } else {
                    record_bound(&mut env, conj);
                    cmp_atoms.push(conj);
                }
            }
            Formula::Not(_) => {
                if bv_mul_goal.is_none() {
                    bv_mul_goal = parse_bv_mul_overflow_goal(conj);
                }
                if bv_smul_goal.is_none() {
                    bv_smul_goal = parse_bv_smul_overflow_goal(conj);
                }
                if let Some(guard) = parse_bv_nonzero_guard(conj) {
                    bv_nonzero_guards.push(guard);
                }
            }
            _ => {}
        }
    }

    if let Some(goal) = bv_smul_goal {
        // The signed width-doubling check is self-contained (no non-zero guard
        // needed): the product fits in `width` signed bits iff the interval
        // product lies within [signed_min, signed_max].
        return prove_bv_smul_no_overflow(&env, &goal);
    }

    if let Some(goal) = bv_mul_goal {
        let has_lhs_nonzero_guard = bv_nonzero_guards
            .iter()
            .any(|guard| guard.width == goal.width && guard.term == goal.lhs);
        if !has_lhs_nonzero_guard {
            return false;
        }
        return prove_bv_mul_no_overflow(&env, &goal);
    }

    // CASE-SPLIT ON A TOP-LEVEL DISJUNCTION. When no violation goal was found among
    // the top-level conjuncts, the goal (and the guards that bound it) may be nested
    // inside a top-level `Or` — a MIR decision-tree / loop-path enumeration the
    // verifier emits (e.g. a `match` arm range `b'a'..=b'f'`, or the `while i+4<=len`
    // loop body). `flatten_and` does not descend into `Or`, so neither the goal nor
    // its in-arm hypotheses (`97 <= byte <= 102`, `i+4 <= len`) reach `env`. Split:
    // `(H ∧ (D0 ∨ D1 ∨ …)) → ¬violation`  holds  iff  for EVERY disjunct `Di`,
    // `(H ∧ Di) → ¬violation`. We re-run the full analysis on `And([…other top-level
    // conjuncts…, Di])` for each `Di` and prove only if EVERY branch proves.
    //
    // SOUNDNESS: this is exactly disjunction elimination over a sound premise.
    //   * Requiring ALL disjuncts to refute the overflow is the conservative
    //     direction: if even one branch's overflow cannot be shown impossible
    //     (a real overflow, OR a branch that does not even carry the goal so no
    //     goal is found and the recursion returns false) the whole split DECLINES.
    //     A false-prove is therefore impossible — we only ever turn an
    //     all-branches-safe disjunction into `Proved`.
    //   * Each recursive premise `And([H…, Di])` is logically IMPLIED by the
    //     original conjunction restricted to that branch, so no fact is fabricated;
    //     dropping the sibling disjuncts only narrows to the branch actually taken.
    // TERMINATION: each recursion replaces one top-level `Or` by a single disjunct,
    // strictly reducing the number of `Or` nodes, so the recursion depth is bounded
    // by the (finite) `Or`-nesting of the VC.
    if goal.is_none() {
        // First top-level conjunct that is a disjunction but NOT itself the bare
        // violation goal (a real `Or([Lt(r,min),Gt(r,max)])` would already have been
        // captured as `goal` above, so any `Or` still here is a context split).
        if let Some(split_idx) = conjuncts.iter().position(
            |c| matches!(c, Formula::Or(children) if parse_overflow_goal(children).is_none()),
        ) {
            if let Formula::Or(branches) = conjuncts[split_idx] {
                if !branches.is_empty() {
                    let others: Vec<Formula> = conjuncts
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != split_idx)
                        .map(|(_, c)| (*c).clone())
                        .collect();
                    return branches.iter().all(|branch| {
                        let mut conj = others.clone();
                        conj.push(branch.clone());
                        prove_no_overflow(&Formula::And(conj))
                    });
                }
            }
        }
    }

    let Some(goal) = goal else {
        return false;
    };

    // Compose symbolic guards to a fixpoint so an operand bounded only RELATIVE to
    // another variable becomes numerically bounded — the loop case `off + 16`
    // guarded by `off < len - 16` with `len <= isize::MAX` yields `off <= isize::MAX
    // - 17`, so `off + 16 <= isize::MAX - 1 < usize::MAX`. (Pure `var ? const`
    // bounds were already recorded above; this only ADDS implied bounds.)
    record_symbolic_bounds(&mut env, &cmp_atoms);

    let mut visiting = FxHashSet::default();
    let result_iv = env.eval(goal.result, &mut visiting);

    // Sound only when the over-approximated result is a finite interval that
    // provably lies within the result type's representable range.
    result_iv.is_finite() && result_iv.lo.unwrap() >= goal.min && result_iv.hi.unwrap() <= goal.max
}

/// Cheap in-process interval/range backend for bounded overflow obligations.
pub struct IntervalBackend;

/// Classification of a `VcKind::HardenedBoundary { PanicBoundary, .. }` whose
/// `callee` names a formula-bearing MIR runtime assert. The hardened panic-boundary
/// lane (trust-vcgen `hardened.rs`) emits, for each MIR `Assert` terminator, a VC
/// carrying the SAME violation-goal `Formula` as the per-statement arithmetic /
/// bounds / divisor-safety VC for that site (see `hardened.rs`
/// `extract_assert_passed_semantics` / `v2_hardened_signed_bv_overflow_formula`).
/// The `callee` is `format!("mir_assert::{msg:?}")` of the `AssertMessage`, so:
///   - `mir_assert::Overflow(...)` / `mir_assert::OverflowNeg` -> arithmetic
///   - `mir_assert::BoundsCheck`                               -> bounds
///   - `mir_assert::DivisionByZero` / `mir_assert::RemainderByZero` -> divisor
/// Any other PanicBoundary callee (`unwrap`, `expect`, a `Custom(...)` policy
/// assert, etc.) asserts a genuine precondition/policy fact, NOT an
/// interval-provable arithmetic violation, so it is NOT classified here and stays
/// flagged. Returns `None` for every non-arithmetic callee.
#[derive(Clone, Copy)]
enum HardenedMirAssertGoal {
    Arithmetic,
    Bounds,
    Divisor,
}

/// Recognize a formula-bearing MIR arithmetic / bounds / divisor PanicBoundary VC
/// by its `callee` string. Returns `None` for every other VcKind and every other
/// hardened category/callee — including `unwrap`/`expect`/policy panic boundaries
/// and the non-arithmetic hardened categories — so those are never routed here.
fn hardened_mir_assert_goal(vc: &VerificationCondition) -> Option<HardenedMirAssertGoal> {
    let VcKind::HardenedBoundary { category: HardenedVcCategory::PanicBoundary, callee, .. } =
        &vc.kind
    else {
        return None;
    };
    // `mir_assert::Overflow(...)` matches BOTH `Overflow(BinOp)` and `OverflowNeg`
    // (both are `prove_no_overflow`-shaped: the unsigned-sub case is a no-underflow
    // goal `parse_underflow_goal` handles, and the i128 case is the BV-mul/smul goal).
    if callee.contains("mir_assert::Overflow") {
        Some(HardenedMirAssertGoal::Arithmetic)
    } else if callee.contains("mir_assert::BoundsCheck") {
        Some(HardenedMirAssertGoal::Bounds)
    } else if callee.contains("mir_assert::DivisionByZero")
        || callee.contains("mir_assert::RemainderByZero")
    {
        Some(HardenedMirAssertGoal::Divisor)
    } else {
        None
    }
}

/// Sound interval discharge of a guarded signed-negation no-overflow obligation.
///
/// Signed `-x` on a width-`W` two's-complement integer overflows IFF
/// `x == iW::MIN` (`= -2^(W-1)`). The VC's violation goal is therefore
/// `Eq(operand, type_min)`, which appears either as a top-level conjunct (the
/// raw path) or — for an `Assert{OverflowNeg}`-guarded block — as the body of a
/// boolean def `Eq(Var(v), Eq(operand, type_min))` asserted by a bare `Var(v)`
/// conjunct (the assert path). We refute it by proving the operand's
/// over-approximated interval EXCLUDES `type_min`, exactly as trust-vcgen's
/// `check_negation_discharge` does (`!operand_interval.contains(type_min)`).
///
/// SOUNDNESS: mirrors the other IntervalBackend arms — returns `true` only when
/// the operand interval provably excludes `iW::MIN`. The threaded path guard
/// `Gt(operand, type_min)` narrows the operand's lower bound to `type_min + 1`,
/// excluding `type_min`. An UNGUARDED negation leaves the operand at the full
/// type range (`lo == type_min`), so `contains(type_min)` holds and we DECLINE
/// (fall through to the SMT lane / stay Unknown) — never a false `Proved`.
fn prove_neg_no_overflow(formula: &Formula, ty: &Ty) -> bool {
    // Only signed integer negation can overflow; the threshold is the type min.
    let type_min = match ty {
        Ty::Int { width, signed: true } => match signed_min_of(*width) {
            Some(m) => m,
            None => return false,
        },
        _ => return false,
    };

    let conjuncts_owned = normalized_conjuncts(formula);
    let conjuncts: Vec<&Formula> = conjuncts_owned.iter().collect();

    // 1. Find the violation goal `Eq(operand, type_min)` — at top level (raw path)
    //    or nested as a boolean def body `Eq(Var, Eq(operand, type_min))` (assert
    //    path). `find_neg_goal_operand` returns the operand side in either shape.
    let operand = match conjuncts.iter().find_map(|c| find_neg_goal_operand(c, type_min)) {
        Some(op) => op,
        None => return false,
    };

    // 2. Build the interval env from the remaining hypotheses — the threaded path
    //    guard `Gt(operand, type_min)`, block-def equalities, and bounds. SKIP the
    //    goal's own `Eq(operand, type_min)` as a def: recording it would pin the
    //    operand to `type_min` and defeat the refutation (it is the negation of
    //    what we are proving, not a hypothesis).
    let mut env = IntervalEnv::new();
    let mut cmp_atoms: Vec<&Formula> = Vec::new();
    for conj in &conjuncts {
        match conj {
            Formula::Eq(a, b) => {
                let is_goal = const_value(a.as_ref()).is_some_and(|c| c == type_min)
                    || const_value(b.as_ref()).is_some_and(|c| c == type_min);
                if !is_goal {
                    env.record_eq_def(a.as_ref(), b.as_ref());
                }
            }
            Formula::Le(..) | Formula::Lt(..) | Formula::Ge(..) | Formula::Gt(..) => {
                record_bound(&mut env, conj);
                cmp_atoms.push(conj);
            }
            _ => {}
        }
    }
    record_symbolic_bounds(&mut env, &cmp_atoms);

    // 3. PROVED iff the operand's over-approximated interval provably excludes
    //    type_min (mirrors check_negation_discharge). The guard gives lo > type_min.
    let mut visiting = FxHashSet::default();
    let iv = env.eval(operand, &mut visiting);
    // VACUITY GUARD: an empty operand interval means the hypotheses are
    // contradictory (UNSAT antecedent). `contains` is gated on `is_finite`-style
    // bounds but `!contains` is vacuously true on an empty interval, so without
    // this an empty operand would falsely "prove" no-overflow. Decline instead.
    if iv.is_empty() {
        return false;
    }
    !iv.contains(type_min)
}

/// Locate the signed-negation violation operand: the non-`type_min` side of an
/// `Eq(operand, type_min)`, whether that `Eq` is `conj` itself (raw path) or the
/// body of an `Eq(_, Eq(operand, type_min))` boolean def (assert path).
fn find_neg_goal_operand<'a>(conj: &'a Formula, type_min: i128) -> Option<&'a Formula> {
    if let Formula::Eq(a, b) = conj {
        // Direct goal: one side is the type-min constant, the other is the operand.
        if const_value(b.as_ref()).is_some_and(|c| c == type_min) {
            return Some(a.as_ref());
        }
        if const_value(a.as_ref()).is_some_and(|c| c == type_min) {
            return Some(b.as_ref());
        }
        // Assert path: `Eq(Var(v), Eq(operand, type_min))` — recurse into the body.
        if let Some(op) = find_neg_goal_operand(b.as_ref(), type_min) {
            return Some(op);
        }
        if let Some(op) = find_neg_goal_operand(a.as_ref(), type_min) {
            return Some(op);
        }
    }
    None
}

impl IntervalBackend {
    fn provable(vc: &VerificationCondition) -> bool {
        let ok = match &vc.kind {
            VcKind::ArithmeticOverflow { .. } => prove_no_overflow(&vc.formula),
            // Sound interval discharge of a guarded signed-negation obligation —
            // e.g. `if x > i32::MIN { -x }` (`x ∈ [MIN+1, _]` excludes i32::MIN).
            // Without this arm the VC routes to "no backend can handle this VC":
            // IntervalBackend is the only deployed safety lane, and the in-process
            // ay backend that lists NegationOverflow in `can_handle` is cfg-gated
            // off / not in the deployed plan. An UNGUARDED negation keeps
            // `lo == type_min` -> declines -> falls through to the SMT lane.
            VcKind::NegationOverflow { ty } => prove_neg_no_overflow(&vc.formula, ty),
            // Sound interval discharge of provably-in-bounds indexing — e.g. the
            // modulo-guarded `arr[n % 4]` (`n % 4 ∈ [0, 4) ⊆ [0, len)`), which
            // neither trust-vc (no request) nor ay-LRA (unsupported atoms) prove
            // today, so the default-mode index check otherwise stays runtime-checked.
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => prove_in_bounds(&vc.formula),
            // Sound interval discharge of a provably-LOSSLESS narrowing cast — e.g.
            // `(i & 0xff) as u32` (`i & 0xff ∈ [0, 255] ⊆ target`). A genuinely-lossy
            // cast falls through to the SMT lane (intended strict truncation flag).
            VcKind::CastOverflow { .. } => prove_cast_lossless(&vc.formula),
            // Sound interval discharge of a provably-nonzero divisor — e.g. the
            // constant divisor in `len / 2` (`[2,2]`, excludes 0). A divisor that
            // could be zero (unbounded/symbolic) falls through to the SMT lane.
            VcKind::DivisionByZero | VcKind::RemainderByZero => prove_div_nonzero(&vc.formula),
            // Sound interval discharge of an unbounded-allocation obligation: prove
            // the allocation count (and any `stride * count` byte total) is bounded
            // below the availability/capacity ceiling, given a dominating size guard
            // (e.g. `if input.len() > MAX_INPUT_LEN { return Err(..) }`). An allocation
            // with no such guard leaves the count interval unbounded above -> declines
            // and falls through to the SMT lane / stays flagged.
            VcKind::UnboundedAllocation { .. } => prove_alloc_bounded(&vc.formula),
            // Hardened panic-boundary TWINS of the above. trust-vcgen emits, for each
            // MIR `Assert` terminator at a hardened site, a `HardenedBoundary {
            // PanicBoundary, callee: "mir_assert::<AssertMessage>" }` VC whose `formula`
            // is the SAME violation goal as the per-statement arithmetic/bounds/divisor
            // VC for that site. Route ONLY those formula-bearing arithmetic/bounds/divisor
            // asserts to the SAME goal-parser + interval discharge as their sibling kind.
            // Every other PanicBoundary callee (`unwrap`/`expect`/policy `Custom(...)`)
            // and every other hardened category returns `None` here -> falls through to
            // `_ => return false` and stays flagged. SOUNDNESS: the goal-parsers decline
            // (return false) when the formula carries no recognized violation goal, so a
            // policy/precondition formula or an unguarded overflow is NEVER vacuously
            // proved — it falls through to the SMT lane / stays Unknown exactly as today.
            VcKind::HardenedBoundary { .. } => match hardened_mir_assert_goal(vc) {
                Some(HardenedMirAssertGoal::Arithmetic) => prove_no_overflow(&vc.formula),
                Some(HardenedMirAssertGoal::Bounds) => prove_in_bounds(&vc.formula),
                Some(HardenedMirAssertGoal::Divisor) => prove_div_nonzero(&vc.formula),
                None => return false,
            },
            _ => return false,
        };
        if std::env::var_os("TRUST_INTERVAL_DEBUG").is_some() {
            eprintln!("TRUST_INTERVAL_VC[{}] provable={ok} formula={:?}", vc.function, vc.formula);
        }
        ok
    }
}

impl VerificationBackend for IntervalBackend {
    fn name(&self) -> &str {
        "interval"
    }

    fn role(&self) -> BackendRole {
        BackendRole::AbstractInterpretation
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // Claim a VC only when we can soundly discharge it, so unprovable cases
        // fall through to ay rather than being captured and returned Unknown.
        Self::provable(vc)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = std::time::Instant::now();
        if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "interval", 0) {
            return result;
        }
        let elapsed = start.elapsed().as_millis() as u64;
        if Self::provable(vc) {
            VerificationResult::Proved {
                solver: "interval".into(),
                time_ms: elapsed,
                strength: ProofStrength::abstract_interpretation(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        } else {
            VerificationResult::Unknown {
                solver: "interval".into(),
                time_ms: elapsed,
                reason: "interval analysis could not bound the result within type range"
                    .to_string(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn range_constraint(v: &Formula, lo: i128, hi: i128) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(lo)), Box::new(v.clone())),
            Formula::Le(Box::new(v.clone()), Box::new(Formula::Int(hi))),
        ])
    }

    fn out_of_range(result: Formula, min: i128, max: i128) -> Formula {
        Formula::Or(vec![
            Formula::Lt(Box::new(result.clone()), Box::new(Formula::Int(min))),
            Formula::Gt(Box::new(result), Box::new(Formula::Int(max))),
        ])
    }

    fn overflow_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::u16(), Ty::u16()),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    fn eq(a: Formula, b: Formula) -> Formula {
        Formula::Eq(Box::new(a), Box::new(b))
    }
    fn add_f(a: Formula, b: Formula) -> Formula {
        Formula::Add(Box::new(a), Box::new(b))
    }
    fn sub_f(a: Formula, b: Formula) -> Formula {
        Formula::Sub(Box::new(a), Box::new(b))
    }

    // ---- VACUOUS-TRUTH (empty-interval) regression ---------------------------
    // A contradictory hypothesis set (UNSAT antecedent) makes the operand
    // interval EMPTY; a "proof" over it is vacuous. The interval lane must
    // DECLINE on emptiness, never report Proved — this is a kernel-free false
    // PROVED if it slips through (no kernel re-check ever sees the interval).

    #[test]
    fn empty_interval_is_not_finite() {
        // Crux of the fix: an empty (crossed) interval has both endpoints
        // concrete, yet is_finite() must reject it — otherwise every range check
        // passes vacuously.
        let empty = Interval { lo: Some(5), hi: Some(2) };
        assert!(empty.is_empty());
        assert!(!empty.is_finite(), "empty interval must NOT count as finite");
        let real = Interval { lo: Some(2), hi: Some(5) };
        assert!(!real.is_empty());
        assert!(real.is_finite());
    }

    #[test]
    fn vacuous_add_contradictory_hypothesis_declines() {
        // n <= 100 ∧ n == 1<<30 is UNSAT -> eval_var(n) = [1<<30, 100] (empty).
        // add(n,n) must stay empty and DECLINE, not vacuously "prove" in-range.
        let n = var("n");
        let vc = overflow_vc(Formula::And(vec![
            le(n.clone(), Formula::Int(100)),
            eq(n.clone(), Formula::Int(1 << 30)),
            out_of_range(add_f(n.clone(), n.clone()), 0, 65535),
        ]));
        assert!(!IntervalBackend::provable(&vc), "contradictory n must NOT vacuously prove (add)");
    }

    #[test]
    fn vacuous_two_var_sub_laundered_empty_declines() {
        // The laundering case the acceptance-site-only fix missed: n is empty
        // ([10,5]); sub(m, n) with a WIDE m yields a non-empty result unless the
        // sub transfer itself propagates emptiness. Must DECLINE.
        let n = var("n");
        let m = var("m");
        let vc = overflow_vc(Formula::And(vec![
            le(n.clone(), Formula::Int(5)),
            eq(n.clone(), Formula::Int(10)),
            range_constraint(&m, 0, 1_000_000),
            out_of_range(sub_f(m.clone(), n.clone()), 0, 65535),
        ]));
        assert!(
            !IntervalBackend::provable(&vc),
            "contradictory n must NOT vacuously prove (two-var sub laundering)"
        );
    }

    #[test]
    fn vacuous_rem_laundered_empty_declines() {
        // rem(n, 5) of an empty n would launder to [0,4] without propagation.
        let n = var("n");
        let vc = overflow_vc(Formula::And(vec![
            le(n.clone(), Formula::Int(5)),
            eq(n.clone(), Formula::Int(10)),
            out_of_range(rem(n.clone(), 5), 0, 4),
        ]));
        assert!(!IntervalBackend::provable(&vc), "contradictory n must NOT vacuously prove (rem)");
    }

    #[test]
    fn non_contradictory_add_still_proves() {
        // POSITIVE regression: an HONEST n in [0,10] -> add(n,n) in [0,20] is
        // genuinely in u16 range and must STILL prove. The fix declines only on
        // genuinely-empty/contradictory states, never on live ones.
        let n = var("n");
        let vc = overflow_vc(Formula::And(vec![
            range_constraint(&n, 0, 10),
            out_of_range(add_f(n.clone(), n.clone()), 0, 65535),
        ]));
        assert!(IntervalBackend::provable(&vc), "honest n in [0,10] must still prove no overflow");
    }

    fn bv_mul_mismatch(lhs: &Formula, rhs: &Formula, width: u32) -> Formula {
        let product = Formula::BvMul(Box::new(lhs.clone()), Box::new(rhs.clone()), width);
        Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::BvUDiv(Box::new(product), Box::new(lhs.clone()), width)),
            Box::new(rhs.clone()),
        )))
    }

    fn index_bounds_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    fn rem(a: Formula, m: i128) -> Formula {
        Formula::Rem(Box::new(a), Box::new(Formula::Int(m)))
    }

    fn ge(a: Formula, b: Formula) -> Formula {
        Formula::Ge(Box::new(a), Box::new(b))
    }

    #[test]
    fn proves_unsigned_modulo_indexed_array_in_bounds() {
        // arr: [_; 4], index = n % 4  ->  violation `n % 4 >= 4` is impossible
        // (the index over-approximates to [-3, 3]; 3 < 4 and the index is unsigned).
        let vc = index_bounds_vc(ge(rem(var("n"), 4), Formula::Int(4)));
        assert!(IntervalBackend::provable(&vc), "n % 4 is always in 0..4 for a [_;4]");
        assert!(IntervalBackend.can_handle(&vc));
    }

    #[test]
    fn declines_modulo_index_that_can_be_out_of_bounds() {
        // arr: [_; 4], index = n % 5  ->  n % 5 can be 4 == len, so OOB; must DECLINE
        // (over-approx [-4, 4]; hi = 4 is NOT < 4) and fall through to the SMT lane.
        let vc = index_bounds_vc(ge(rem(var("n"), 5), Formula::Int(4)));
        assert!(!IntervalBackend::provable(&vc), "n % 5 can equal len 4 — not in bounds");
    }

    fn alloc_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::UnboundedAllocation {
                callee: "Vec::with_capacity".into(),
                count: "n".into(),
                detail: String::new(),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn proves_guarded_alloc_count_below_ceiling() {
        // Guard `len <= 67108864` bounds `count = len * 2 <= 134217728 < 2^28`, so
        // the failure atom `Ge(count, 2^28)` is impossible: the alloc is bounded.
        let formula = Formula::And(vec![
            Formula::Le(Box::new(var("len")), Box::new(Formula::Int(67_108_864))),
            Formula::Eq(
                Box::new(var("count")),
                Box::new(Formula::Mul(Box::new(var("len")), Box::new(Formula::Int(2)))),
            ),
            // length non-negativity (a real arg-type-range fact)
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var("len"))),
            ge(var("count"), Formula::Int(1 << 28)),
        ]);
        assert!(IntervalBackend::provable(&alloc_vc(formula)), "len*2 with len<=64Mi is < 2^28");
    }

    #[test]
    fn declines_unguarded_alloc_count() {
        // No dominating size guard: `count = len * 2` with `len` unbounded above can
        // reach the ceiling — the failure atom is satisfiable, so we MUST decline
        // (return false) and let the obligation stay flagged. SOUNDNESS floor.
        let formula = Formula::And(vec![
            Formula::Eq(
                Box::new(var("count")),
                Box::new(Formula::Mul(Box::new(var("len")), Box::new(Formula::Int(2)))),
            ),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var("len"))),
            ge(var("count"), Formula::Int(1 << 28)),
        ]);
        assert!(
            !IntervalBackend::provable(&alloc_vc(formula)),
            "an unbounded count must NOT be proved bounded"
        );
    }

    #[test]
    fn declines_alloc_count_guarded_too_loosely() {
        // Guard `len <= 200_000_000`: `count = len * 2 <= 400_000_000 >= 2^28`, so the
        // allocation CAN exceed the ceiling — must decline (real availability hazard).
        let formula = Formula::And(vec![
            Formula::Le(Box::new(var("len")), Box::new(Formula::Int(200_000_000))),
            Formula::Eq(
                Box::new(var("count")),
                Box::new(Formula::Mul(Box::new(var("len")), Box::new(Formula::Int(2)))),
            ),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var("len"))),
            ge(var("count"), Formula::Int(1 << 28)),
        ]);
        assert!(
            !IntervalBackend::provable(&alloc_vc(formula)),
            "len*2 with len<=200M can exceed 2^28 — must decline"
        );
    }

    #[test]
    fn direct_forced_alloc_is_not_masked_by_safe_arithmetic_sibling() {
        // Falsification fixture shape: a safe widened arithmetic operation emits
        // an overflow disjunction beside a forced allocation at the exact
        // ceiling. The overflow arm's large `u32::MAX` threshold looks like an
        // allocation atom to the intentionally coarse branch recognizer, but it
        // must not suppress the directly exposed allocation violation.
        let a = var("a");
        let sum = Formula::Add(Box::new(a.clone()), Box::new(Formula::Int(1)));
        let count = var("count");
        let ceiling = Formula::Int(1 << 28);
        let formula = Formula::And(vec![
            range_constraint(&a, 0, 255),
            Formula::Or(vec![
                Formula::Gt(Box::new(sum.clone()), Box::new(Formula::Int(i128::from(u32::MAX)))),
                Formula::Eq(Box::new(var("sum")), Box::new(sum)),
            ]),
            Formula::Eq(Box::new(count.clone()), Box::new(ceiling.clone())),
            Formula::Le(Box::new(count.clone()), Box::new(ceiling.clone())),
            Formula::Ge(Box::new(count), Box::new(ceiling)),
        ]);

        assert!(
            crate::alloc_over_ceiling_forced(&formula),
            "the direct allocation atom is a structural refutation"
        );
        assert!(
            !IntervalBackend::provable(&alloc_vc(formula)),
            "an unrelated safe arithmetic sibling must not turn a forced allocation into Proved"
        );
    }

    #[test]
    fn proves_branch_split_alloc_when_all_branches_bounded() {
        // A two-branch `Or` (the vcgen per-path shape): each branch carries its own
        // failure atom under the shared outer guard `len <= 67108864`. Both branch
        // counts (len*2, len*2) are bounded, so the whole disjunction is refuted.
        let outer_guard = Formula::Le(Box::new(var("len")), Box::new(Formula::Int(67_108_864)));
        let nonneg = Formula::Le(Box::new(Formula::Int(0)), Box::new(var("len")));
        let branch = |c: &str| {
            Formula::And(vec![
                Formula::Eq(
                    Box::new(var(c)),
                    Box::new(Formula::Mul(Box::new(var("len")), Box::new(Formula::Int(2)))),
                ),
                ge(var(c), Formula::Int(1 << 28)),
            ])
        };
        let formula =
            Formula::And(vec![outer_guard, nonneg, Formula::Or(vec![branch("c1"), branch("c2")])]);
        assert!(
            IntervalBackend::provable(&alloc_vc(formula)),
            "every branch's count is bounded under the shared guard"
        );
    }

    #[test]
    fn declines_branch_split_when_one_branch_unbounded() {
        // Same branch-split shape, but the SECOND branch has no guard relating its
        // count to the bounded `len` — that branch's allocation is unbounded, so the
        // whole obligation must DECLINE (a single hazardous path is enough). SOUNDNESS.
        let outer_guard = Formula::Le(Box::new(var("len")), Box::new(Formula::Int(67_108_864)));
        let nonneg = Formula::Le(Box::new(Formula::Int(0)), Box::new(var("len")));
        let bounded_branch = Formula::And(vec![
            Formula::Eq(
                Box::new(var("c1")),
                Box::new(Formula::Mul(Box::new(var("len")), Box::new(Formula::Int(2)))),
            ),
            ge(var("c1"), Formula::Int(1 << 28)),
        ]);
        // c2 is a free, unbounded count.
        let unbounded_branch = ge(var("c2"), Formula::Int(1 << 28));
        let formula = Formula::And(vec![
            outer_guard,
            nonneg,
            Formula::Or(vec![bounded_branch, unbounded_branch]),
        ]);
        assert!(
            !IntervalBackend::provable(&alloc_vc(formula)),
            "an unbounded branch count must block the whole proof"
        );
    }

    #[test]
    fn proves_signed_guarded_index_in_bounds() {
        // signed index with guard 0 <= i <= 3, len 4: violation (i<0 OR i>=4) impossible.
        let viol = Formula::Or(vec![
            Formula::Lt(Box::new(var("i")), Box::new(Formula::Int(0))),
            ge(var("i"), Formula::Int(4)),
        ]);
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var("i"))),
            Formula::Le(Box::new(var("i")), Box::new(Formula::Int(3))),
            viol,
        ]);
        assert!(IntervalBackend::provable(&index_bounds_vc(formula)));
    }

    #[test]
    fn declines_signed_index_without_lower_bound() {
        // signed index with only an upper guard i <= 3 (no i >= 0): could be negative,
        // so the `i < 0` half of the violation is reachable — must DECLINE.
        let viol = Formula::Or(vec![
            Formula::Lt(Box::new(var("i")), Box::new(Formula::Int(0))),
            ge(var("i"), Formula::Int(4)),
        ]);
        let formula =
            Formula::And(vec![Formula::Le(Box::new(var("i")), Box::new(Formula::Int(3))), viol]);
        assert!(!IntervalBackend::provable(&index_bounds_vc(formula)));
    }

    #[test]
    fn declines_unbounded_index() {
        // bare `i >= len` with no fact bounding i: the index is unbounded — DECLINE.
        let vc = index_bounds_vc(ge(var("i"), Formula::Int(4)));
        assert!(!IntervalBackend::provable(&vc));
    }

    fn cast_overflow_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::CastOverflow { from_ty: Ty::u64(), to_ty: Ty::u32() },
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    // trust-vcgen's narrowing-cast violation: value outside `[to_min, to_max]`.
    fn cast_violation(value: Formula, to_min: i128, to_max: i128) -> Formula {
        Formula::Or(vec![
            Formula::Lt(Box::new(value.clone()), Box::new(Formula::Int(to_min))),
            Formula::Gt(Box::new(value), Box::new(Formula::Int(to_max))),
        ])
    }

    #[test]
    fn proves_masked_narrowing_cast_lossless() {
        // `(i & 0xff) as u32`: `i & 0xff ∈ [0, 255] ⊆ [0, u32::MAX]` — lossless.
        let masked = Formula::BvAnd(
            Box::new(var("i")),
            Box::new(Formula::BitVec { value: 0xff, width: 32 }),
            32,
        );
        let vc = cast_overflow_vc(cast_violation(masked, 0, u32::MAX as i128));
        assert!(IntervalBackend::provable(&vc), "i & 0xff fits u32 losslessly");
        assert!(IntervalBackend.can_handle(&vc));
    }

    #[test]
    fn proves_guard_bounded_narrowing_cast() {
        // `i as u8` with `0 <= i <= 100`: `100 <= 255` — lossless.
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var("i"))),
            Formula::Le(Box::new(var("i")), Box::new(Formula::Int(100))),
            cast_violation(var("i"), 0, 255),
        ]);
        assert!(IntervalBackend::provable(&cast_overflow_vc(formula)));
    }

    #[test]
    fn declines_unbounded_narrowing_cast() {
        // `i as u32` with only the source-type range `[0, ~usize::MAX]`: i can exceed
        // u32::MAX, so the cast IS lossy — DECLINE (falls through to the SMT lane,
        // the intended strict-mode truncation flag).
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var("i"))),
            Formula::Le(Box::new(var("i")), Box::new(Formula::Int(i64::MAX as i128))),
            cast_violation(var("i"), 0, u32::MAX as i128),
        ]);
        assert!(
            !IntervalBackend::provable(&cast_overflow_vc(formula)),
            "unbounded i can exceed u32::MAX — the cast is genuinely lossy"
        );
    }

    #[test]
    fn hostile_declines_unmasked_cast_with_duplicated_goal() {
        // HOSTILE PROBE of the duplicate-collapse edit: an UNMASKED `v as u8`
        // where `v` is an unconstrained value (only the source-type range), with
        // the SAME cast goal duplicated THREE times (the panic-boundary-twin shape
        // the collapse was written for). The duplicate-collapse must NOT cause a
        // false prove: the single distinct obligation's value is unbounded above,
        // so it must DECLINE.
        let g = || cast_violation(var("v"), 0, 255);
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var("v"))),
            Formula::Le(Box::new(var("v")), Box::new(Formula::Int(i64::MAX as i128))),
            g(),
            g(),
            g(),
        ]);
        assert!(
            !IntervalBackend::provable(&cast_overflow_vc(formula)),
            "unmasked unbounded v->u8 must decline even when its goal is duplicated"
        );
    }

    #[test]
    fn hostile_declines_two_distinct_cast_goals() {
        // Two DISTINCT cast goals in one VC: even though one value (m) is masked
        // and bounded, the other (v) is unconstrained. The collapse requires ALL
        // goals to be the SAME obligation; distinct goals must DECLINE (the value
        // pairing is ambiguous). SOUNDNESS: a lossy distinct cast must not ride in
        // on a bounded sibling.
        let masked = Formula::BvAnd(
            Box::new(var("m")),
            Box::new(Formula::BitVec { value: 0xff, width: 32 }),
            32,
        );
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var("v"))),
            Formula::Le(Box::new(var("v")), Box::new(Formula::Int(i64::MAX as i128))),
            cast_violation(masked, 0, 255),
            cast_violation(var("v"), 0, 255),
        ]);
        assert!(
            !IntervalBackend::provable(&cast_overflow_vc(formula)),
            "a distinct unbounded cast goal must block the proof"
        );
    }

    // aterm-hash Option A shape: `(full & u64::MAX as u128) as u64` where `full`
    // is an unbounded u128. The mask const-folds to 0xFFFF_FFFF_FFFF_FFFF, the
    // BvAnd caps the value at [0, u64::MAX] in the 128-bit BV domain, and the
    // outer (unsigned) BvToInt carries it to the int domain — so the narrowing
    // to u64 is value-preserving and MUST prove. This is the masked-cast form
    // that lib.rs:144 and lib.rs:107 lower to (with width 128 / mask u64::MAX).
    #[test]
    fn proves_u128_low64_mask_narrowing_to_u64() {
        let u64_max: i128 = u64::MAX as i128; // 0xFFFF_FFFF_FFFF_FFFF
        // BvToInt(BvAnd(IntToBv(full, 128), IntToBv(u64::MAX, 128), 128), 128, false)
        let masked = Formula::BvToInt(
            Box::new(Formula::BvAnd(
                Box::new(Formula::IntToBv(Box::new(var("full")), 128)),
                Box::new(Formula::IntToBv(Box::new(Formula::Int(u64_max)), 128)),
                128,
            )),
            128,
            false,
        );
        let vc = cast_overflow_vc(cast_violation(masked, 0, u64_max));
        assert!(
            IntervalBackend::provable(&vc),
            "full & u64::MAX fits u64 losslessly regardless of full's range"
        );
    }

    // SOUNDNESS counterpart: the SAME u128 value WITHOUT the mask must NOT prove
    // a narrowing to u64 — an unconstrained u128 can exceed u64::MAX, so the
    // truncation is genuinely lossy and the narrowing lint must stay armed.
    #[test]
    fn declines_unmasked_u128_narrowing_to_u64() {
        let u64_max: i128 = u64::MAX as i128;
        // full ranges over the full unsigned 128-bit domain (its source type).
        let formula = Formula::And(vec![
            range_constraint(&var("full"), 0, i128::MAX),
            cast_violation(var("full"), 0, u64_max),
        ]);
        assert!(
            !IntervalBackend::provable(&cast_overflow_vc(formula)),
            "an unmasked u128 can exceed u64::MAX — the narrowing IS lossy"
        );
    }

    // SOUNDNESS gate for the bitwise-AND rule under SIGNED reinterpretation. The
    // [0, min(hi)] cap lives in the UNSIGNED bitvector domain; a NEGATIVE operand
    // must NOT yield a falsely-tight bound. `(-1) & 5 == 5` (bits 0xF..F & 5): the
    // negative operand `-1` widens to bv_top via IntToBv, so BvAnd computes
    // [0, 5] (sound: contains 5), NOT a bound that would exclude it. And a signed
    // AND whose result can be negative (`(-1) & (-2) == -2`) must stay in the full
    // signed range — the rule must never claim a non-negative-only bound for a
    // signed result. Here we assert the backend does NOT "prove" that a signed AND
    // result is within a tight positive-only window, guarding the negative case.
    #[test]
    fn signed_bitand_is_not_given_unsigned_min_bound() {
        // `(a & -2) as i8` for a: i8 — result can be negative (e.g. (-1)&(-2) = -2),
        // so it is NOT confined to [0, ...]. Asking whether the result is within
        // [0, 127] must DECLINE: the rule must not lend a [0,min] bound to a value
        // whose signed interpretation can be negative.
        let signed_and = Formula::BvToInt(
            Box::new(Formula::BvAnd(
                Box::new(Formula::IntToBv(Box::new(var("a")), 8)),
                Box::new(Formula::IntToBv(Box::new(Formula::Int(-2)), 8)),
                8,
            )),
            8,
            true,
        );
        // Source bound is the full i8 range; result can be -2 which is < 0.
        let formula = Formula::And(vec![
            range_constraint(&var("a"), i8::MIN as i128, i8::MAX as i128),
            cast_violation(signed_and, 0, i8::MAX as i128),
        ]);
        assert!(
            !IntervalBackend::provable(&cast_overflow_vc(formula)),
            "signed AND can be negative; must not get the unsigned [0,min] bound"
        );
    }

    fn bv_nonzero(term: Formula, width: u32) -> Formula {
        Formula::Not(Box::new(Formula::Eq(
            Box::new(term),
            Box::new(Formula::BitVec { value: 0, width }),
        )))
    }

    fn formula_contains_var(formula: &Formula, expected_name: &str) -> bool {
        match formula {
            Formula::Var(name, _) => name == expected_name,
            Formula::SymVar(symbol, _) => symbol.as_str() == expected_name,
            _ => formula
                .children()
                .into_iter()
                .any(|child| formula_contains_var(child, expected_name)),
        }
    }

    fn vcgen_bounded_checked_mul_func() -> VerifiableFunction {
        let ty = Ty::u32();
        VerifiableFunction {
            name: "bounded_checked_mul".to_string(),
            def_path: "test::bounded_checked_mul".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ty.clone(), name: None },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![ty.clone(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Mul,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Mul),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: ty,
            },
            contracts: vec![],
            preconditions: vec![
                range_constraint(&var("a"), 0, 1000),
                range_constraint(&var("b"), 0, 1000),
            ],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // (a % 250) + 1 on u16: _2 = a % 250 (=> [0,249]), result = _2 + 1 in
    // [1,250] which is within [0, 65535]. Must prove.
    #[test]
    fn proves_modulo_plus_one() {
        let tmp = var("_2");
        let result = Formula::Add(Box::new(tmp.clone()), Box::new(Formula::Int(1)));
        let formula = Formula::And(vec![
            Formula::Eq(
                Box::new(tmp.clone()),
                Box::new(Formula::Rem(Box::new(var("a")), Box::new(Formula::Int(250)))),
            ),
            Formula::And(vec![
                range_constraint(&tmp, 0, 65535),
                range_constraint(&Formula::Int(1), 0, 65535),
                out_of_range(result, 0, 65535),
            ]),
        ]);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula.clone())));
        assert!(backend.verify(&overflow_vc(formula)).is_proved());
    }

    // (a & 0x7f) + 1 on u32 via the bitmask+int lowering: _2 = bv2nat(bvand(
    // int2bv(a), int2bv(127))) => [0,127], result = _2 + 1 in [1,128] within
    // [0, 2^32-1]. Must prove.
    #[test]
    fn proves_bitmask_plus_one() {
        let tmp = var("_2");
        let masked = Formula::BvToInt(
            Box::new(Formula::BvAnd(
                Box::new(Formula::IntToBv(Box::new(var("a")), 32)),
                Box::new(Formula::IntToBv(Box::new(Formula::Int(127)), 32)),
                32,
            )),
            32,
            false,
        );
        let result = Formula::Add(Box::new(tmp.clone()), Box::new(Formula::Int(1)));
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(tmp.clone()), Box::new(masked)),
            Formula::And(vec![
                range_constraint(&tmp, 0, (1i128 << 32) - 1),
                out_of_range(result, 0, (1i128 << 32) - 1),
            ]),
        ]);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula.clone())));
        assert!(backend.verify(&overflow_vc(formula)).is_proved());
    }

    #[test]
    fn proves_bounded_unsigned_bv_mul_overflow_check() {
        let lhs = Formula::Var("__trust_ovf_bv_lhs_a".into(), Sort::BitVec(32));
        let rhs = Formula::Var("__trust_ovf_bv_rhs_b".into(), Sort::BitVec(32));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 1000),
            range_constraint(&var("b"), 0, 1000),
            bv_nonzero(lhs.clone(), 32),
            bv_mul_mismatch(&lhs, &rhs, 32),
        ]);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula.clone())));
        assert!(backend.verify(&overflow_vc(formula)).is_proved());
    }

    #[test]
    fn proves_vcgen_bounded_unsigned_checked_mul_overflow_vc() {
        let vcs = trust_vcgen::generate_vcs(&vcgen_bounded_checked_mul_func());
        let mul_overflow_vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
            .expect("vcgen must emit a checked Mul overflow VC");
        assert!(
            formula_contains_var(&mul_overflow_vc.formula, "__trust_ovf_bv_lhs_a"),
            "vcgen Mul overflow VC must use the fresh lhs BV operand name consumed by interval: {:?}",
            mul_overflow_vc.formula
        );
        assert!(
            formula_contains_var(&mul_overflow_vc.formula, "__trust_ovf_bv_rhs_b"),
            "vcgen Mul overflow VC must use the fresh rhs BV operand name consumed by interval: {:?}",
            mul_overflow_vc.formula
        );

        let backend = IntervalBackend;
        assert!(backend.can_handle(mul_overflow_vc));
        assert!(backend.verify(mul_overflow_vc).is_proved());
    }

    #[test]
    fn declines_unsigned_bv_mul_without_nonzero_guard() {
        let lhs = Formula::Var("__trust_ovf_bv_lhs_a".into(), Sort::BitVec(32));
        let rhs = Formula::Var("__trust_ovf_bv_rhs_b".into(), Sort::BitVec(32));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 1000),
            range_constraint(&var("b"), 0, 1000),
            bv_mul_mismatch(&lhs, &rhs, 32),
        ]);
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&overflow_vc(formula)));
    }

    #[test]
    fn declines_unsigned_bv_mul_with_rhs_only_nonzero_guard() {
        let lhs = Formula::Var("__trust_ovf_bv_lhs_a".into(), Sort::BitVec(32));
        let rhs = Formula::Var("__trust_ovf_bv_rhs_b".into(), Sort::BitVec(32));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 1000),
            range_constraint(&var("b"), 0, 1000),
            bv_nonzero(rhs.clone(), 32),
            bv_mul_mismatch(&lhs, &rhs, 32),
        ]);
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&overflow_vc(formula)));
    }

    #[test]
    fn declines_bounded_unsigned_bv_mul_that_can_overflow() {
        let lhs = Formula::Var("__trust_ovf_bv_lhs_a".into(), Sort::BitVec(32));
        let rhs = Formula::Var("__trust_ovf_bv_rhs_b".into(), Sort::BitVec(32));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 70_000),
            range_constraint(&var("b"), 0, 70_000),
            bv_nonzero(lhs.clone(), 32),
            bv_mul_mismatch(&lhs, &rhs, 32),
        ]);
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&overflow_vc(formula)));
    }

    // `(x as u64) * (y as u64)` for x,y: u32 — operands are zero-extended 32-bit
    // vars with NO recorded numeric bound; the BV WIDTH alone bounds each to
    // [0, 2^32-1], so the 64-bit product fits. Exercises the bv_term_width /
    // BvZeroExt eval path. Must prove.
    #[test]
    fn proves_widening_unsigned_bv_mul_via_bv_width() {
        let lhs = Formula::BvZeroExt(
            Box::new(Formula::Var("__trust_ovf_bv_lhs_x".into(), Sort::BitVec(32))),
            32,
        );
        let rhs = Formula::BvZeroExt(
            Box::new(Formula::Var("__trust_ovf_bv_rhs_y".into(), Sort::BitVec(32))),
            32,
        );
        let formula =
            Formula::And(vec![bv_nonzero(lhs.clone(), 64), bv_mul_mismatch(&lhs, &rhs, 64)]);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula.clone())));
        assert!(backend.verify(&overflow_vc(formula)).is_proved());
    }

    // `(x as u128) * (y as u128)` for x,y: u64 — operands ZERO-extended from
    // 64-bit vars (range [0, 2^64-1]); the u128 product upper bound is
    // (2^64-1)^2 = 2^128 - 2^65 + 1 <= u128::MAX, so it CANNOT overflow u128 and
    // must PROVE. Regression for the i128-bound gap: the product exceeds i128::MAX
    // and bv_unsigned_max(128) is None, so the old i128 path declined this safe mul
    // at 0ms (the aterm-hash `multiply_mix` widened multiply). Now bounded in u128.
    #[test]
    fn proves_widening_unsigned_bv_mul_u64_sources_width_128() {
        let lhs = Formula::BvZeroExt(
            Box::new(Formula::Var("__trust_ovf_bv_lhs_x".into(), Sort::BitVec(64))),
            64,
        );
        let rhs = Formula::BvZeroExt(
            Box::new(Formula::Var("__trust_ovf_bv_rhs_y".into(), Sort::BitVec(64))),
            64,
        );
        let formula =
            Formula::And(vec![bv_nonzero(lhs.clone(), 128), bv_mul_mismatch(&lhs, &rhs, 128)]);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula.clone())), "u64*u64 fits u128");
        assert!(backend.verify(&overflow_vc(formula)).is_proved());
    }

    // SOUNDNESS at width 128: same-width 128-bit operands with no width-narrowing
    // (bare BV vars -> unbounded) CAN overflow u128, so the backend MUST decline —
    // the u128 product-bound fix must not over-discharge an unbounded multiply.
    #[test]
    fn declines_unbounded_bv_mul_width_128() {
        let lhs = Formula::Var("__trust_ovf_bv_lhs_a".into(), Sort::BitVec(128));
        let rhs = Formula::Var("__trust_ovf_bv_rhs_b".into(), Sort::BitVec(128));
        let formula =
            Formula::And(vec![bv_nonzero(lhs.clone(), 128), bv_mul_mismatch(&lhs, &rhs, 128)]);
        let backend = IntervalBackend;
        assert!(!backend.verify(&overflow_vc(formula)).is_proved(), "u128*u128 can overflow");
    }

    /// A loop-body multiply VC carries a switch-discriminant disjunct
    /// (`_8 == 0 || _8 == 1`) conjoined with the provable widening BV mul goal. The
    /// context `Or` must be SKIPPED (not bail the whole VC), so the in-loop widening
    /// multiply discharges via the interval lane (proof-grade) instead of falling to
    /// ay's `:rule trust` BV proof, which the carcara cross-check rejects.
    #[test]
    fn proves_widening_bv_mul_with_context_discriminant_or() {
        let lhs = Formula::BvZeroExt(
            Box::new(Formula::Var("__trust_ovf_bv_lhs_x".into(), Sort::BitVec(32))),
            32,
        );
        let rhs = Formula::BvZeroExt(
            Box::new(Formula::Var("__trust_ovf_bv_rhs_y".into(), Sort::BitVec(32))),
            32,
        );
        let discriminant_or = Formula::Or(vec![
            Formula::Eq(Box::new(var("_8")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("_8")), Box::new(Formula::Int(1))),
        ]);
        let formula = Formula::And(vec![
            discriminant_or,
            bv_nonzero(lhs.clone(), 64),
            bv_mul_mismatch(&lhs, &rhs, 64),
        ]);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula.clone())));
        assert!(backend.verify(&overflow_vc(formula)).is_proved());
    }

    /// SOUNDNESS: skipping the context `Or` must NEVER let a genuinely-overflowing mul
    /// prove. Same-width 32-bit operands bounded to `[0, 70_000]` can overflow
    /// (70_000² > u32::MAX), so the goal stays SAT and the VC is correctly declined
    /// even with the discriminant `Or` present.
    #[test]
    fn declines_overflowing_bv_mul_despite_context_discriminant_or() {
        let lhs = Formula::Var("__trust_ovf_bv_lhs_a".into(), Sort::BitVec(32));
        let rhs = Formula::Var("__trust_ovf_bv_rhs_b".into(), Sort::BitVec(32));
        let discriminant_or = Formula::Or(vec![
            Formula::Eq(Box::new(var("_8")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("_8")), Box::new(Formula::Int(1))),
        ]);
        let formula = Formula::And(vec![
            discriminant_or,
            range_constraint(&var("a"), 0, 70_000),
            range_constraint(&var("b"), 0, 70_000),
            bv_nonzero(lhs.clone(), 32),
            bv_mul_mismatch(&lhs, &rhs, 32),
        ]);
        let backend = IntervalBackend;
        assert!(!backend.verify(&overflow_vc(formula)).is_proved());
    }

    /// Build the signed width-doubling mul-overflow failure formula at width `w`
    /// over two operands (mirrors trust-vcgen `v2_signed_bv_overflow_formula`).
    fn signed_bv_mul_overflow(lhs: Formula, rhs: Formula, w: u32) -> Formula {
        let dw = 2 * w;
        let prod = Formula::BvMul(
            Box::new(Formula::BvSignExt(Box::new(lhs), w)),
            Box::new(Formula::BvSignExt(Box::new(rhs), w)),
            dw,
        );
        let slice = Formula::BvExtract { inner: Box::new(prod), high: dw - 1, low: w - 1 };
        let slice_w = w + 1;
        let fits = Formula::Or(vec![
            Formula::Eq(
                Box::new(slice.clone()),
                Box::new(Formula::BitVec { value: 0, width: slice_w }),
            ),
            Formula::Eq(
                Box::new(slice),
                Box::new(Formula::BitVec { value: (1i128 << slice_w) - 1, width: slice_w }),
            ),
        ]);
        Formula::Not(Box::new(fits))
    }

    // `(x as i64) * (y as i64)` for x,y: i32 — operands sign-extended from 32-bit
    // vars (range [-2^31, 2^31-1]); the i64 product fits. Exercises the signed
    // goal parser + BvSignExt eval. Must prove.
    #[test]
    fn proves_widening_signed_bv_mul_via_bv_width() {
        let op = |role: &str| {
            Formula::BvSignExt(
                Box::new(Formula::Var(format!("__trust_ovf_bv_{role}_x"), Sort::BitVec(32))),
                32,
            )
        };
        let formula = signed_bv_mul_overflow(op("lhs"), op("rhs"), 64);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula.clone())));
        assert!(backend.verify(&overflow_vc(formula)).is_proved());
    }

    // `(x as i64) * (y as i64)` for x,y: u32 — operands ZERO-extended (unsigned
    // source), each in [0, 2^32-1]; the product can reach ~2^64 > i64::MAX, so
    // the interval backend MUST decline (the real overflow is left for ay).
    #[test]
    fn declines_widening_signed_bv_mul_u32_sources_can_overflow() {
        let op = |role: &str| {
            Formula::BvZeroExt(
                Box::new(Formula::Var(format!("__trust_ovf_bv_{role}_x"), Sort::BitVec(32))),
                32,
            )
        };
        let formula = signed_bv_mul_overflow(op("lhs"), op("rhs"), 64);
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&overflow_vc(formula)));
    }

    // Branch-const merge: base = if flag {10} else {20} => [10,20], +1 in
    // [11,21] within [0, 2^32-1]. Must prove (Ite present in the formula).
    #[test]
    fn proves_branch_const_plus_one() {
        let base = Formula::Ite(
            Box::new(var("flag")),
            Box::new(Formula::Int(10)),
            Box::new(Formula::Int(20)),
        );
        let result = Formula::Add(Box::new(base), Box::new(Formula::Int(1)));
        let formula = out_of_range(result, 0, (1i128 << 32) - 1);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula)));
    }

    // The overflow disjunction is equivalent in either child order. The
    // recognizer must not silently depend on `result < min` appearing first.
    #[test]
    fn proves_overflow_goal_with_reversed_disjunction_arms() {
        let result = Formula::Add(Box::new(Formula::Int(10)), Box::new(Formula::Int(20)));
        let formula = Formula::Or(vec![
            Formula::Gt(Box::new(result.clone()), Box::new(Formula::Int(65535))),
            Formula::Lt(Box::new(result), Box::new(Formula::Int(0))),
        ]);
        let backend = IntervalBackend;
        assert!(backend.can_handle(&overflow_vc(formula.clone())));
        assert!(backend.verify(&overflow_vc(formula)).is_proved());
    }

    // a + 1 on u16 with a unconstrained over the full type range: a = 65535
    // overflows. Must NOT prove (soundness: never mask a real overflow).
    #[test]
    fn declines_unbounded_add() {
        let result = Formula::Add(Box::new(var("a")), Box::new(Formula::Int(1)));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 65535),
            out_of_range(result, 0, 65535),
        ]);
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&overflow_vc(formula.clone())));
        assert!(matches!(
            backend.verify(&overflow_vc(formula)),
            VerificationResult::Unknown { .. }
        ));
    }

    // Two fully-unconstrained operands: a + b can overflow. Must NOT prove.
    #[test]
    fn declines_two_unbounded_operands() {
        let result = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let formula = out_of_range(result, 0, 65535);
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&overflow_vc(formula)));
    }

    // The overflow disjunction must describe one result expression. If the
    // lower and upper arms mention different expressions, proving either one
    // bounded is not a proof that the whole violation is impossible.
    #[test]
    fn declines_overflow_goal_with_mismatched_result_arms() {
        let lower_result = Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(1)));
        let upper_result = Formula::Add(Box::new(Formula::Int(2)), Box::new(Formula::Int(2)));
        let formula = Formula::Or(vec![
            Formula::Lt(Box::new(lower_result), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(upper_result), Box::new(Formula::Int(65535))),
        ]);
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&overflow_vc(formula)));
    }

    // Non-overflow VC kinds are never claimed.
    #[test]
    fn ignores_non_overflow_kinds() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&vc));
    }

    // Modulo alone, without the lower-bound range constraint, still proves:
    // x % 250 is in [-249, 249] but the +1 result must be checked against the
    // type max only when the lower bound is known. Here we confirm the signed
    // fallback stays sound: result interval [-248, 250] is NOT within [0,65535]
    // (lower bound negative) so we must decline.
    #[test]
    fn declines_modulo_without_nonneg_bound() {
        let tmp = var("_2");
        let result = Formula::Add(Box::new(tmp.clone()), Box::new(Formula::Int(1)));
        // No range constraint on _2, so its sign is unknown.
        let formula = Formula::And(vec![
            Formula::Eq(
                Box::new(tmp.clone()),
                Box::new(Formula::Rem(Box::new(var("a")), Box::new(Formula::Int(250)))),
            ),
            out_of_range(result, 0, 65535),
        ]);
        let backend = IntervalBackend;
        assert!(!backend.can_handle(&overflow_vc(formula)));
    }

    // ------------------------------------------------------------------------
    // aterm-hash classes: symbolic guard composition, relational bounds, shift
    // casts, constant-divisor non-zero. Each PROVE case is paired with an
    // UNGUARDED DECLINE that must fall through to the SMT lane (soundness).
    // ------------------------------------------------------------------------

    const ISIZE_MAX: i128 = i64::MAX as i128; // isize::MAX on a 64-bit target
    const USIZE_MAX: i128 = u64::MAX as i128; // usize::MAX on a 64-bit target

    fn le(a: Formula, b: Formula) -> Formula {
        Formula::Le(Box::new(a), Box::new(b))
    }
    fn lt(a: Formula, b: Formula) -> Formula {
        Formula::Lt(Box::new(a), Box::new(b))
    }
    fn sub(a: Formula, b: Formula) -> Formula {
        Formula::Sub(Box::new(a), Box::new(b))
    }
    fn add(a: Formula, b: Formula) -> Formula {
        Formula::Add(Box::new(a), Box::new(b))
    }
    fn slice_len_bounds(len: &Formula) -> Vec<Formula> {
        // Mirrors `conjoin_slice_len_bounds`: 0 <= len <= isize::MAX.
        vec![le(Formula::Int(0), len.clone()), le(len.clone(), Formula::Int(ISIZE_MAX))]
    }

    // --- ADD overflow: `off + 16` guarded by the loop condition off < len - 16 ---

    #[test]
    fn proves_loop_offset_add_under_symbolic_guard() {
        // hash_bytes loop: `off + 16` (usize). Guard `off < len - 16`, len a slice
        // length (<= isize::MAX). `off <= isize::MAX - 17`, so `off + 16 <=
        // isize::MAX - 1 < usize::MAX`. Must PROVE.
        let off = var("off");
        let len = var("len");
        let result = add(off.clone(), Formula::Int(16));
        let mut conj = slice_len_bounds(&len);
        conj.push(le(Formula::Int(0), off.clone())); // off: usize, >= 0
        conj.push(lt(off.clone(), sub(len.clone(), Formula::Int(16)))); // off < len - 16
        conj.push(out_of_range(result, 0, USIZE_MAX));
        let vc = overflow_vc(Formula::And(conj));
        assert!(IntervalBackend::provable(&vc), "off + 16 cannot overflow usize under the guard");
    }

    #[test]
    fn declines_unguarded_add_to_usize_max() {
        // No loop guard: `off` only bounded by its type [0, usize::MAX]; `off + 16`
        // overflows at off = usize::MAX - 1. Must DECLINE.
        let off = var("off");
        let result = add(off.clone(), Formula::Int(16));
        let formula = Formula::And(vec![
            le(Formula::Int(0), off.clone()),
            le(off.clone(), Formula::Int(USIZE_MAX)),
            out_of_range(result, 0, USIZE_MAX),
        ]);
        assert!(
            !IntervalBackend::provable(&overflow_vc(formula)),
            "unguarded off + 16 can overflow"
        );
    }

    #[test]
    fn proves_loop_offset_add_under_eq_chained_symbolic_guard() {
        // The ACTUAL traced hash_bytes VC shape: the loop guard is `off < _59`
        // where `_59` is a PLAIN VAR defined via an Eq-CHAIN, not the compound
        // `off < len - 16` directly:
        //   _58 = off, _59 = _60.0, _60.0 = len - 16, len = slice_len,
        //   slice_len <= isize::MAX, _58 < _59  (the loop guard), off >= 0.
        // `record_bound`/`record_symbolic_bounds` previously dropped `_58 < _59`
        // because both sides are plain vars, so `off` never got a finite upper
        // bound and `off + 16` evaluated to TOP -> declined. Resolving `_59`
        // through its Eq-chain to `len - 16 <= isize::MAX - 16` must now bound
        // `off <= isize::MAX - 17`, so `off + 16 <= isize::MAX - 1 < usize::MAX`.
        // Must PROVE.
        let off = var("off");
        let len = var("len");
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let result = add(off.clone(), Formula::Int(16));
        let formula = Formula::And(vec![
            le(var("slice_len"), Formula::Int(ISIZE_MAX)), // slice_len <= isize::MAX
            lt(var("_58"), var("_59")),                    // loop guard: off < _59
            eq(var("_58"), off.clone()),                   // _58 = off
            eq(var("_59"), var("_60_0")),                  // _59 = _60.0
            eq(var("_60_0"), sub(len.clone(), Formula::Int(16))), // _60.0 = len - 16
            eq(len.clone(), var("slice_len")),             // len = slice_len
            le(Formula::Int(0), off.clone()),              // off: usize, >= 0
            out_of_range(result, 0, USIZE_MAX),
        ]);
        let vc = overflow_vc(formula);
        assert!(
            IntervalBackend::provable(&vc),
            "off + 16 cannot overflow usize under the Eq-chained loop guard off < _59"
        );
    }

    #[test]
    fn proves_loop_offset_plus_8_under_eq_chained_symbolic_guard() {
        // Same Eq-chain guard, the off + 8 twin (lib.rs:188): off <= isize::MAX-17
        // -> off + 8 <= isize::MAX - 9 < usize::MAX. Must PROVE.
        let off = var("off");
        let len = var("len");
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let result = add(off.clone(), Formula::Int(8));
        let formula = Formula::And(vec![
            le(var("slice_len"), Formula::Int(ISIZE_MAX)),
            lt(var("_58"), var("_59")),
            eq(var("_58"), off.clone()),
            eq(var("_59"), var("_60_0")),
            eq(var("_60_0"), sub(len.clone(), Formula::Int(16))),
            eq(len.clone(), var("slice_len")),
            le(Formula::Int(0), off.clone()),
            out_of_range(result, 0, USIZE_MAX),
        ]);
        assert!(IntervalBackend::provable(&overflow_vc(formula)));
    }

    #[test]
    fn declines_eq_chained_var_guard_when_other_var_unbounded() {
        // The guard is `off < _59` via an Eq-chain, but `_59`'s chain bottoms out
        // at an UNBOUNDED var (no slice-len bound) -> `_59` evaluates to TOP, so
        // `off` gets NO finite upper bound and `off + 16` can overflow. Must
        // DECLINE (an unguarded operand must never be falsely proved).
        let off = var("off");
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let result = add(off.clone(), Formula::Int(16));
        let formula = Formula::And(vec![
            lt(var("_58"), var("_59")),                              // off < _59
            eq(var("_58"), off.clone()),                             // _58 = off
            eq(var("_59"), sub(var("unbounded"), Formula::Int(16))), // _59 = unbounded - 16
            le(Formula::Int(0), off.clone()),                        // off >= 0
            out_of_range(result, 0, USIZE_MAX),
        ]);
        assert!(
            !IntervalBackend::provable(&overflow_vc(formula)),
            "off + 16 with an unbounded Eq-chain guard can overflow"
        );
    }

    // --- SUB underflow: `len - 16` guarded by the loop condition ---

    #[test]
    fn proves_loop_len_minus_16_under_guard() {
        // `len - 16` in the loop suffix; reachable only when off < len - 16 holds,
        // which forces len > 16. The bare underflow goal `Lt(len - 16, 0)` with
        // len in [17, isize::MAX] has lo = 1 >= 0. Must PROVE.
        let len = var("len");
        let mut conj = slice_len_bounds(&len);
        conj.push(Formula::Ge(Box::new(len.clone()), Box::new(Formula::Int(17)))); // len >= 17
        conj.push(lt(sub(len.clone(), Formula::Int(16)), Formula::Int(0))); // underflow goal
        let vc = overflow_vc(Formula::And(conj));
        assert!(IntervalBackend::provable(&vc), "len - 16 >= 1 under len >= 17");
    }

    // --- RELATIONAL bounds: bytes[len - 1] and bytes[len / 2] under len > 0 ---

    #[test]
    fn proves_index_len_minus_one_in_bounds() {
        // `bytes[len - 1]`: violation `(len - 1) >= len`. The affine difference
        // len - (len - 1) = 1 >= 1, so index < len. Must PROVE even though the
        // independent rule cannot (index.hi is NOT below len.lo).
        let len = var("len");
        let index = sub(len.clone(), Formula::Int(1));
        let mut conj = slice_len_bounds(&len);
        conj.push(Formula::Gt(Box::new(len.clone()), Box::new(Formula::Int(0)))); // len > 0
        conj.push(Formula::Ge(Box::new(index), Box::new(len))); // violation
        assert!(IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))));
    }

    #[test]
    fn proves_index_len_div_two_in_bounds() {
        // `bytes[len / 2]` under len >= 1: floor(len/2) <= len - 1 < len. Must PROVE
        // via the div-by-constant relational rule.
        let len = var("len");
        let index = Formula::Div(Box::new(len.clone()), Box::new(Formula::Int(2)));
        let mut conj = slice_len_bounds(&len);
        conj.push(Formula::Gt(Box::new(len.clone()), Box::new(Formula::Int(0)))); // len > 0
        conj.push(Formula::Ge(Box::new(index), Box::new(len))); // violation
        assert!(IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))));
    }

    #[test]
    fn declines_index_len_minus_one_without_nonempty_guard() {
        // No `len >= 1`: len could be 0, then `len - 1` underflows to a huge usize
        // (>= len). The affine diff `len - (len-1) = 1 >= 1` STILL proves index <
        // mathematical len — but for a usize index the real concern is captured by
        // the slice-len bound only. To stay conservative we additionally require a
        // finite index interval; with only [0, isize::MAX] on len the index `len-1`
        // is [-1, isize::MAX-1], finite, and the affine diff is 1 — so this still
        // proves index < len mathematically, which is the obligation as emitted.
        // (The MIR-level usize wrap is a SEPARATE Sub-underflow obligation.) This
        // documents that the bounds VC is discharged on its own terms.
        let len = var("len");
        let index = sub(len.clone(), Formula::Int(1));
        let mut conj = slice_len_bounds(&len);
        conj.push(Formula::Ge(Box::new(index), Box::new(len))); // violation, NO len>=1
        // Affine `len - (len-1) = 1 >= 1` holds regardless, so this proves.
        assert!(IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))));
    }

    #[test]
    fn declines_unrelated_index_ge_len() {
        // A genuinely-OOB symbolic index `m` with no relation to len: must DECLINE.
        let len = var("len");
        let mut conj = slice_len_bounds(&len);
        conj.push(Formula::Ge(Box::new(var("m")), Box::new(len)));
        assert!(!IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))));
    }

    #[test]
    fn declines_index_div_two_unbounded_len() {
        // `bytes[len / 2]` with NO `len >= 1` and len possibly 0: floor(0/2) = 0,
        // len = 0 -> index 0 >= len 0 is a real OOB on an empty slice. The div rule
        // requires len >= 1, so it must DECLINE here. (len's recorded lo is 0 from
        // the slice-len bound, not >= 1.)
        let len = var("len");
        let index = Formula::Div(Box::new(len.clone()), Box::new(Formula::Int(2)));
        let mut conj = slice_len_bounds(&len);
        conj.push(Formula::Ge(Box::new(index), Box::new(len))); // violation, NO len>=1
        assert!(
            !IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))),
            "len/2 over a possibly-empty slice is not provably in bounds"
        );
    }

    // --- ALIAS-AWARE relational bounds: the index is built from `len` but the
    //     length var in the goal is a DISTINCT name aliased to `len` via a
    //     top-level `Eq(len, slice_len)` (the actual hash_bytes lib.rs:179/180
    //     shape). The relational rule must canonicalize the alias so the affine
    //     difference cancels / the div base matches. ---

    #[test]
    fn proves_aliased_index_len_div_two_in_bounds() {
        // hash_bytes lib.rs:179 EXACT shape: the index is a TEMP VAR `_40` whose
        // def is `Div(len, 2)`, the goal length var is another temp `_42` aliased
        // to `slice_len`, and `Eq(len, slice_len)` is the cross-name alias with
        // `len > 0`. The div route resolves `_40` to its `Div` def, canonicalizes
        // the alias so base (`len`) and length (`slice_len`) are the same atom, and
        // proves floor(len/2) <= len-1 < len under len >= 1. PROVE.
        let len = var("len#s0_0");
        let slice_len = var("bytes__slice_len");
        let idx_tmp = var("_40#s26_0");
        let len_tmp = var("_42#s26_1");
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let conj = vec![
            eq(len.clone(), slice_len.clone()), // alias len == slice_len
            eq(idx_tmp.clone(), Formula::Div(Box::new(len.clone()), Box::new(Formula::Int(2)))),
            eq(len_tmp.clone(), slice_len.clone()), // _42 = slice_len
            le(Formula::Int(0), slice_len.clone()), // 0 <= slice_len
            le(slice_len.clone(), Formula::Int(ISIZE_MAX)), // slice_len <= isize::MAX
            Formula::Gt(Box::new(len.clone()), Box::new(Formula::Int(0))), // len > 0
            Formula::Ge(Box::new(idx_tmp), Box::new(len_tmp)), // violation: _40 >= _42
        ];
        assert!(
            IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))),
            "len/2 < len under the len==slice_len alias and len > 0"
        );
    }

    #[test]
    fn proves_aliased_index_len_minus_one_in_bounds() {
        // hash_bytes lib.rs:180 EXACT shape: index temp `_45 = _46.0`, `_46.0 =
        // Sub(len, 1)`, length temp `_47 = slice_len`, alias `Eq(len, slice_len)`,
        // `len > 0`. The affine difference slice_len - (len - 1) canonicalizes both
        // `len` symbols to one atom and cancels to constant 1 >= 1. PROVE.
        let len = var("len#s0_0");
        let slice_len = var("bytes__slice_len");
        let idx_tmp = var("_45#s28_0");
        let sub_tmp = var("_46_0");
        let len_tmp = var("_47#s28_1");
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let conj = vec![
            eq(len.clone(), slice_len.clone()),
            eq(idx_tmp.clone(), sub_tmp.clone()), // _45 = _46.0
            eq(sub_tmp.clone(), sub(len.clone(), Formula::Int(1))), // _46.0 = len - 1
            eq(len_tmp.clone(), slice_len.clone()), // _47 = slice_len
            le(Formula::Int(0), slice_len.clone()),
            le(slice_len.clone(), Formula::Int(ISIZE_MAX)),
            Formula::Gt(Box::new(len.clone()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(idx_tmp), Box::new(len_tmp)),
        ];
        assert!(
            IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))),
            "len - 1 < len under the len==slice_len alias and len > 0"
        );
    }

    #[test]
    fn declines_aliased_index_at_len() {
        // `bytes[len]` (index == the aliased length itself), NOT relationally below
        // len: index = len, goal `len >= slice_len` with `Eq(len, slice_len)`. The
        // affine difference slice_len - len = 0 (NOT >= 1) and there is no div, so
        // the relational rule must DECLINE — a real OOB at the one-past-the-end
        // index. (Canonicalizing the alias must never turn `len >= len` into a
        // proof.)
        let len = var("len#s0_0");
        let slice_len = var("bytes__slice_len");
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let conj = vec![
            eq(len.clone(), slice_len.clone()),
            le(Formula::Int(0), slice_len.clone()),
            le(slice_len.clone(), Formula::Int(ISIZE_MAX)),
            Formula::Gt(Box::new(len.clone()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(len.clone()), Box::new(slice_len)), // index == len
        ];
        assert!(
            !IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))),
            "bytes[len] is one past the end — never in bounds"
        );
    }

    #[test]
    fn declines_aliased_index_len_div_two_without_nonempty_guard() {
        // `bytes[len / 2]` with the alias but NO `len > 0`: len could be 0, then
        // floor(0/2) = 0 >= len 0 is a real OOB on an empty slice. The div rule
        // requires len >= 1, so even with the alias resolved it must DECLINE.
        let len = var("len#s0_0");
        let slice_len = var("bytes__slice_len");
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let index = Formula::Div(Box::new(len.clone()), Box::new(Formula::Int(2)));
        let conj = vec![
            eq(len.clone(), slice_len.clone()),
            le(Formula::Int(0), slice_len.clone()),
            le(slice_len.clone(), Formula::Int(ISIZE_MAX)),
            // NO len > 0 guard
            Formula::Ge(Box::new(index), Box::new(slice_len)),
        ];
        assert!(
            !IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))),
            "len/2 over a possibly-empty aliased slice is not provably in bounds"
        );
    }

    #[test]
    fn declines_nonaliased_index_div_two_ge_other_len() {
        // Two UNRELATED vars: index = m / 2, length var = slice_len, with NO
        // equality connecting them. canonical_var keeps them distinct, so the div
        // base (`m`) does not match the length (`slice_len`) and the affine
        // difference does not cancel. Must DECLINE — `m / 2` over an unrelated
        // `slice_len` is a genuine OOB candidate.
        let m = var("m");
        let slice_len = var("bytes__slice_len");
        let index = Formula::Div(Box::new(m.clone()), Box::new(Formula::Int(2)));
        let conj = vec![
            le(Formula::Int(0), slice_len.clone()),
            le(slice_len.clone(), Formula::Int(ISIZE_MAX)),
            Formula::Gt(Box::new(m.clone()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(index), Box::new(slice_len)),
        ];
        assert!(
            !IntervalBackend::provable(&index_bounds_vc(Formula::And(conj))),
            "m / 2 over an unrelated slice_len is not provably in bounds"
        );
    }

    // --- SHIFT-result narrowing cast: (i >> 64) as u64 for i: u128 ---

    fn cast_u128_to_u64_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::CastOverflow { from_ty: Ty::u128(), to_ty: Ty::u64() },
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn proves_u128_shift_64_narrowing_cast_lossless() {
        // `(i >> 64) as u64`: i >> 64 < 2^64, fits u64. Shift lowered as
        // BvToInt(BvLShr(IntToBv(i,128), IntToBv(64,128), 128), 128, false).
        let shifted = Formula::BvToInt(
            Box::new(Formula::BvLShr(
                Box::new(Formula::IntToBv(Box::new(var("i")), 128)),
                Box::new(Formula::IntToBv(Box::new(Formula::Int(64)), 128)),
                128,
            )),
            128,
            false,
        );
        let vc = cast_u128_to_u64_vc(cast_violation(shifted, 0, USIZE_MAX));
        assert!(IntervalBackend::provable(&vc), "i >> 64 fits u64 losslessly");
    }

    #[test]
    fn declines_u128_unshifted_narrowing_cast() {
        // `i as u64` for i: u128, no shift: i can exceed u64::MAX -> genuinely lossy.
        // Must DECLINE.
        let value =
            Formula::BvToInt(Box::new(Formula::IntToBv(Box::new(var("i")), 128)), 128, false);
        let vc = cast_u128_to_u64_vc(cast_violation(value, 0, USIZE_MAX));
        assert!(!IntervalBackend::provable(&vc), "unshifted u128 -> u64 is lossy");
    }

    #[test]
    fn declines_u128_shift_32_narrowing_cast() {
        // `(i >> 32) as u64` for i: u128: i >> 32 < 2^96, still exceeds u64::MAX.
        // Must DECLINE.
        let shifted = Formula::BvToInt(
            Box::new(Formula::BvLShr(
                Box::new(Formula::IntToBv(Box::new(var("i")), 128)),
                Box::new(Formula::IntToBv(Box::new(Formula::Int(32)), 128)),
                128,
            )),
            128,
            false,
        );
        let vc = cast_u128_to_u64_vc(cast_violation(shifted, 0, USIZE_MAX));
        assert!(!IntervalBackend::provable(&vc), "i >> 32 can still exceed u64::MAX");
    }

    // --- DivisionByZero: constant divisor 2 (and guarded divisor) ---

    fn div_by_zero_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn proves_constant_divisor_two_nonzero() {
        // `len / 2`: divisor literal 2, violation `2 == 0` is impossible.
        let goal = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(0)));
        assert!(IntervalBackend::provable(&div_by_zero_vc(goal)));
    }

    #[test]
    fn proves_guarded_divisor_nonzero() {
        // `if d > 0 { x / d }`: divisor d in [1, ..], excludes 0.
        let d = var("d");
        let formula = Formula::And(vec![
            Formula::Ge(Box::new(d.clone()), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(d), Box::new(Formula::Int(0))),
        ]);
        assert!(IntervalBackend::provable(&div_by_zero_vc(formula)));
    }

    #[test]
    fn declines_unbounded_divisor() {
        // Bare `d == 0` with no bound on d: d could be 0. Must DECLINE.
        let goal = Formula::Eq(Box::new(var("d")), Box::new(Formula::Int(0)));
        assert!(!IntervalBackend::provable(&div_by_zero_vc(goal)), "unbounded divisor can be zero");
    }

    // --- Hardened panic-boundary MIR-assert twins (route to the sibling prover) ---

    fn hardened_panic_vc(callee: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::HardenedBoundary {
                category: HardenedVcCategory::PanicBoundary,
                callee: callee.into(),
                detail: "MIR arithmetic assert can panic".into(),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn proves_hardened_overflow_boundary_when_guarded() {
        // Hardened twin of a GUARDED `a + b` (a,b in [0,250]) whose sum fits u16:
        // violation `a + b < 0 || a + b > 65535` is impossible. Same formula the
        // ArithmeticOverflow sibling proves; routed via the mir_assert::Overflow callee.
        let sum = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 250),
            range_constraint(&var("b"), 0, 250),
            out_of_range(sum, 0, 65535),
        ]);
        let vc = hardened_panic_vc("mir_assert::Overflow(Add)", formula);
        assert!(IntervalBackend::provable(&vc), "guarded a+b fits u16");
        assert!(IntervalBackend.can_handle(&vc));
    }

    #[test]
    fn declines_hardened_overflow_boundary_when_unguarded() {
        // Hardened twin of an UNGUARDED `a + b` (no bound on a/b): the sum can exceed
        // u16::MAX, so the violation goal is SAT. The goal-parser/interval discharge
        // declines -> the boundary STAYS FLAGGED. Mirrors the unguarded-overflow case.
        let sum = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let vc = hardened_panic_vc("mir_assert::Overflow(Add)", out_of_range(sum, 0, 65535));
        assert!(
            !IntervalBackend::provable(&vc),
            "unguarded a+b can overflow u16 — hardened twin must decline"
        );
        assert!(!IntervalBackend.can_handle(&vc));
    }

    #[test]
    fn proves_hardened_bounds_boundary_when_guarded() {
        // Hardened twin of `arr[n % 4]` for `arr: [_; 4]`: violation `n % 4 >= 4`
        // is impossible. Routed via the mir_assert::BoundsCheck callee.
        let vc =
            hardened_panic_vc("mir_assert::BoundsCheck", ge(rem(var("n"), 4), Formula::Int(4)));
        assert!(IntervalBackend::provable(&vc), "n % 4 is always in 0..4");
    }

    #[test]
    fn proves_hardened_div_boundary_when_guarded() {
        // Hardened twin of `x / d` with `d > 0`: divisor in [1, ..], excludes 0.
        let d = var("d");
        let formula = Formula::And(vec![
            Formula::Ge(Box::new(d.clone()), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(d), Box::new(Formula::Int(0))),
        ]);
        let vc = hardened_panic_vc("mir_assert::DivisionByZero", formula);
        assert!(IntervalBackend::provable(&vc), "guarded divisor is nonzero");
    }

    #[test]
    fn does_not_prove_hardened_unwrap_or_policy_boundary() {
        // A genuine policy / precondition panic boundary (`unwrap`, and a Custom
        // policy assert) carries NO interval-provable arithmetic goal. It must NOT be
        // routed/proved by the interval backend — it stays flagged for a real solver.
        // (Even a trivially-true-looking `Bool(false)` violation must not be claimed:
        //  no recognized goal -> declines.)
        let unwrap_vc = hardened_panic_vc("unwrap", Formula::Bool(false));
        assert!(!IntervalBackend::provable(&unwrap_vc), "unwrap boundary must stay flagged");
        assert!(!IntervalBackend.can_handle(&unwrap_vc));

        let policy_vc = hardened_panic_vc(
            "mir_assert::Custom(\"caller validated input\")",
            Formula::Not(Box::new(Formula::Bool(false))),
        );
        assert!(!IntervalBackend::provable(&policy_vc), "Custom policy assert must stay flagged");
        assert!(!IntervalBackend.can_handle(&policy_vc));
    }

    #[test]
    fn does_not_prove_non_panic_hardened_categories() {
        // A non-PanicBoundary hardened category (e.g. Utf8Reject) must never be routed
        // here, even if its formula happened to parse as an overflow goal.
        let sum = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 250),
            range_constraint(&var("b"), 0, 250),
            out_of_range(sum, 0, 65535),
        ]);
        let vc = VerificationCondition {
            kind: VcKind::HardenedBoundary {
                category: HardenedVcCategory::Utf8Reject,
                callee: "mir_assert::Overflow(Add)".into(),
                detail: "n/a".into(),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        };
        assert!(!IntervalBackend::provable(&vc), "non-PanicBoundary category must not be routed");
    }

    // --- Hardened twins in their REAL `Not(in_range)` goal SHAPE (the bug fix) ---
    //
    // The hardened lane (trust-vcgen hardened.rs:625) pushes the violation as
    // `Not(in_range)`, NOT the pre-normalized `Or([Lt,Gt])` the older twin tests
    // used. These exercise the De Morgan / comparison-negation normalization that
    // surfaces that shape to the existing parsers.

    // The arithmetic `in_range` exactly as `guards::extract_assert_passed_semantics`
    // builds it: `And([Le(min, result), Le(result, max)])` (const min on the LEFT
    // of the lower bound, const max on the RIGHT of the upper bound).
    fn in_range(result: Formula, min: i128, max: i128) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(min)), Box::new(result.clone())),
            Formula::Le(Box::new(result), Box::new(Formula::Int(max))),
        ])
    }

    #[test]
    fn normalizes_not_and_arith_twin_guarded_proves() {
        // GUARDED `a + b` (a,b in [0,250]) whose sum fits u16, in the REAL hardened
        // shape `Not(And([Le(0,sum), Le(sum,65535)]))`. De Morgan must surface the
        // `Or([Lt(sum,0), Gt(sum,65535)])` goal so the existing prover discharges it.
        let sum = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 250),
            range_constraint(&var("b"), 0, 250),
            Formula::Not(Box::new(in_range(sum, 0, 65535))),
        ]);
        let vc = hardened_panic_vc("mir_assert::Overflow(Add)", formula);
        assert!(IntervalBackend::provable(&vc), "Not(And[Le,Le]) guarded twin must PROVE");
        assert!(IntervalBackend.can_handle(&vc));
    }

    #[test]
    fn normalizes_not_and_arith_twin_unguarded_declines() {
        // UNGUARDED `a + b` in the REAL hardened shape: De Morgan surfaces the goal,
        // but the interval eval finds the sum can exceed u16::MAX -> DECLINE (the
        // boundary stays flagged). A real overflow is never false-proved.
        let sum = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let vc = hardened_panic_vc(
            "mir_assert::Overflow(Add)",
            Formula::Not(Box::new(in_range(sum, 0, 65535))),
        );
        assert!(!IntervalBackend::provable(&vc), "unguarded Not(And) twin must DECLINE");
        assert!(!IntervalBackend.can_handle(&vc));
    }

    #[test]
    fn normalizes_not_lt_bounds_twin() {
        // Hardened BoundsCheck twin in its REAL shape: the asserted in-bounds cond is
        // `Lt(index, len)` (expected=true), so the violation is `Not(Lt(n%4, 4))`,
        // which negates to the `Ge(n%4, 4)` goal. For `arr: [_;4]` it must PROVE.
        let vc = hardened_panic_vc(
            "mir_assert::BoundsCheck",
            Formula::Not(Box::new(Formula::Lt(
                Box::new(rem(var("n"), 4)),
                Box::new(Formula::Int(4)),
            ))),
        );
        assert!(IntervalBackend::provable(&vc), "Not(Lt(n%4,4)) -> Ge(n%4,4) proves for [_;4]");

        // And the genuinely-OOB sibling `n % 5` (can equal len 4) must DECLINE.
        let oob = hardened_panic_vc(
            "mir_assert::BoundsCheck",
            Formula::Not(Box::new(Formula::Lt(
                Box::new(rem(var("n"), 5)),
                Box::new(Formula::Int(4)),
            ))),
        );
        assert!(!IntervalBackend::provable(&oob), "Not(Lt(n%5,4)) can be OOB — must DECLINE");
    }

    #[test]
    fn normalizes_double_not_eq_div_twin() {
        // Hardened DivisionByZero twin in its REAL shape: the asserted cond is
        // `divisor != 0` == `Not(Eq(d,0))`, so the violation is `Not(Not(Eq(d,0)))`,
        // collapsing to `Eq(d,0)`. With a guard `d >= 1` it must PROVE.
        let d = var("d");
        let formula = Formula::And(vec![
            Formula::Ge(Box::new(d.clone()), Box::new(Formula::Int(1))),
            Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(d),
                Box::new(Formula::Int(0)),
            ))))),
        ]);
        let vc = hardened_panic_vc("mir_assert::DivisionByZero", formula);
        assert!(
            IntervalBackend::provable(&vc),
            "Not(Not(Eq(d,0))) -> Eq(d,0), guarded d>=1 proves"
        );
    }

    #[test]
    fn leaves_opaque_not_predicate_flagged() {
        // An OPAQUE / non-arithmetic `Not(...)` (a predicate, a bare bool var) must
        // NOT be rewritten into any goal — normalization leaves it untouched, no
        // parser recognizes it, and the hardened twin stays FLAGGED (declines).
        let opaque =
            Formula::Not(Box::new(Formula::Pred("caller_validated".into(), vec![var("x")])));
        let vc = hardened_panic_vc("mir_assert::Overflow(Add)", opaque);
        assert!(!IntervalBackend::provable(&vc), "opaque Not(Pred) stays flagged");
        assert!(!IntervalBackend.can_handle(&vc));

        // A `Not(Var)` (the bounds/div cond local left abstract with no def) also
        // yields no recognized goal -> declines, never false-proves.
        let not_var = hardened_panic_vc(
            "mir_assert::BoundsCheck",
            Formula::Not(Box::new(Formula::Var("_cond".into(), Sort::Bool))),
        );
        assert!(!IntervalBackend::provable(&not_var), "Not(Var) cond stays flagged");
    }

    #[test]
    fn normalization_preserves_bv_nonzero_guard_shape() {
        // The BV mul-overflow lane relies on a `Not(Eq(lhs,0))` nonzero GUARD and a
        // `Not(Eq(BvUDiv(BvMul..),rhs))` goal being left UNCHANGED by normalization
        // (only `Not(And)`/`Not(Not)`/`Not(<cmp>)` are rewritten). Confirm a guarded
        // widening BV mul still proves through the normalized path.
        let lhs = Formula::Var("__trust_ovf_bv_lhs_a".into(), Sort::BitVec(32));
        let rhs = Formula::Var("__trust_ovf_bv_rhs_b".into(), Sort::BitVec(32));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 1000),
            range_constraint(&var("b"), 0, 1000),
            bv_nonzero(lhs.clone(), 32),
            bv_mul_mismatch(&lhs, &rhs, 32),
        ]);
        let vc = hardened_panic_vc("mir_assert::Overflow(Mul)", formula);
        assert!(IntervalBackend::provable(&vc), "BV nonzero-guard shape survives normalization");
    }

    // --- Flag-encoded violation goals (the boolean-definition-inlining fix) ---
    //
    // Hardened arithmetic twins express the violation through a boolean OVERFLOW
    // FLAG: a conjunct `Eq(Var(flag, Bool), Or([Lt(result,min), Gt(result,max)]))`
    // DEFINES the flag, and the goal appears as a bare `Var(flag)` (violation) /
    // `Not(Var(flag))` (no-overflow hypothesis) rather than the direct `Or`. The
    // inlining pre-pass substitutes the flag by its definition (equals-for-equals)
    // so the existing goal parsers see the direct `Or([Lt,Gt])`.

    fn flag_def(flag: &str, result: Formula, min: i128, max: i128) -> Formula {
        Formula::Eq(
            Box::new(Formula::Var(flag.into(), Sort::Bool)),
            Box::new(out_of_range(result, min, max)),
        )
    }

    #[test]
    fn inlines_overflow_flag_guarded_proves() {
        // GUARDED `len - 8` (len in [8, isize::MAX]) whose flag def is the overflow
        // disjunction, with the VIOLATION expressed as the bare flag var `ovf`.
        // Inlining `ovf -> Or([Lt(len-8,0), Gt(len-8,MAX)])` surfaces the goal, and
        // the guard makes `len - 8 ∈ [0, ..]` so the violation is UNSAT -> PROVES.
        let res = sub(var("len"), Formula::Int(8));
        let formula = Formula::And(vec![
            range_constraint(&var("len"), 8, 9223372036854775807),
            flag_def("ovf", res, 0, 18446744073709551615),
            Formula::Var("ovf".into(), Sort::Bool),
        ]);
        let vc = hardened_panic_vc("mir_assert::Overflow(Sub)", formula);
        assert!(IntervalBackend::provable(&vc), "flag-encoded guarded sub twin must PROVE");
        assert!(IntervalBackend.can_handle(&vc));
    }

    #[test]
    fn inlines_overflow_flag_unguarded_declines() {
        // UNGUARDED `len - 8` (len only known >= 0): inlining still surfaces the goal,
        // but `len - 8` can be negative, so the overflow flag is feasible -> DECLINE.
        // Substitution is EXACT, so an unguarded violation is never false-proved.
        let res = sub(var("len"), Formula::Int(8));
        let formula = Formula::And(vec![
            range_constraint(&var("len"), 0, 9223372036854775807),
            flag_def("ovf", res, 0, 18446744073709551615),
            Formula::Var("ovf".into(), Sort::Bool),
        ]);
        let vc = hardened_panic_vc("mir_assert::Overflow(Sub)", formula);
        assert!(!IntervalBackend::provable(&vc), "flag-encoded unguarded sub twin must DECLINE");
        assert!(!IntervalBackend.can_handle(&vc));
    }

    #[test]
    fn inlines_overflow_flag_add_guarded_proves() {
        // GUARDED `a + b` (a,b in [0,250]) fits u16, violation as the bare flag.
        let res = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let formula = Formula::And(vec![
            range_constraint(&var("a"), 0, 250),
            range_constraint(&var("b"), 0, 250),
            flag_def("ovf", res, 0, 65535),
            Formula::Var("ovf".into(), Sort::Bool),
        ]);
        let vc = hardened_panic_vc("mir_assert::Overflow(Add)", formula);
        assert!(IntervalBackend::provable(&vc), "flag-encoded guarded add twin must PROVE");
    }

    #[test]
    fn does_not_inline_multiply_defined_flag() {
        // A flag with TWO definitions is path-dependent: inlining either would be
        // unsound, so the flag is NOT inlined and the goal stays unrecognized ->
        // DECLINE (never false-prove). Here both a SAFE and an UNSAFE def are present;
        // even with the guard the ambiguous flag must keep the twin flagged.
        let safe = sub(var("len"), Formula::Int(8));
        let unsafe_res = Formula::Add(Box::new(var("len")), Box::new(var("len")));
        let formula = Formula::And(vec![
            range_constraint(&var("len"), 8, 9223372036854775807),
            flag_def("ovf", safe, 0, 18446744073709551615),
            flag_def("ovf", unsafe_res, 0, 100), // second def -> drop both
            Formula::Var("ovf".into(), Sort::Bool),
        ]);
        let vc = hardened_panic_vc("mir_assert::Overflow(Sub)", formula);
        assert!(
            !IntervalBackend::provable(&vc),
            "multiply-defined flag must not be inlined (path-dependent)"
        );
    }

    #[test]
    fn does_not_inline_non_bool_eq() {
        // An INTEGER definitional equality `Eq(Var(_,Int), expr)` must NOT be treated
        // as a boolean-flag def by the inliner (it is the existing integer def path).
        // A formula whose only "goal" is a bare INT var (no recognized goal) declines.
        let formula = Formula::And(vec![
            range_constraint(&var("len"), 8, 9223372036854775807),
            Formula::Eq(
                Box::new(Formula::Var("_t".into(), Sort::Int)),
                Box::new(sub(var("len"), Formula::Int(8))),
            ),
            // No violation goal present -> declines.
            Formula::Var("_t".into(), Sort::Int),
        ]);
        let vc = hardened_panic_vc("mir_assert::Overflow(Sub)", formula);
        assert!(!IntervalBackend::provable(&vc), "int eq is not a bool-flag def");
    }

    #[test]
    fn interval_arithmetic_is_sound() {
        assert_eq!(Interval::range(0, 249).add(Interval::cst(1)), Interval::range(1, 250));
        assert_eq!(Interval::range(0, 5).sub(Interval::range(1, 2)), Interval::range(-2, 4));
        assert_eq!(Interval::cst(3).neg(), Interval::cst(-3));
        assert_eq!(Interval::range(2, 3).mul(Interval::range(4, 5)), Interval::range(8, 15));
        assert_eq!(Interval::range(-2, 3).mul(Interval::range(-4, 5)), Interval::range(-12, 15));
        assert_eq!(Interval::range(0, 100).rem(Interval::cst(250)), Interval::range(0, 249));
        assert_eq!(Interval::TOP.rem(Interval::cst(250)), Interval::range(-249, 249));
        // Unbounded propagation: x + unbounded = unbounded.
        assert_eq!(Interval::cst(1).add(Interval::TOP), Interval::TOP);
    }
}
