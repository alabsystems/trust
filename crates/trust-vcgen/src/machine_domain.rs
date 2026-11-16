// EXACTNESS RULES FOR MEETING TWO MACHINE INTEGER DOMAINS.
//
// The machine-faithful translator (`contracts::machine_faithful_translate`)
// lowers a formula into pure declared-width QF_BV. Every value leaf in it
// carries the `(width, signed)` its Rust declaration states. When two leaves
// with DIFFERENT declared domains have to meet under one operator, something
// has to convert — and the whole soundness of the lane rests on that conversion
// being exactly what the machine does.
//
// THE TWO KINDS OF CONVERSION ARE NOT INTERCHANGEABLE, and this module keeps
// them in two types that cannot be passed to each other's call sites:
//
//   * [`ValueConversion`] — preserves the MATHEMATICAL VALUE. This is what a
//     meeting of operands needs: after the conversion the term denotes the same
//     integer it denoted before, so the surrounding comparison/equality decides
//     the same question. `Identity`, `ZeroExtend`, `SignExtend` — and nothing
//     else. The type deliberately CANNOT express a truncation or a signedness
//     reinterpretation, so no call site can request one by accident.
//
//   * [`PatternResize`] — preserves only the BIT PATTERN's low bits. It is NOT
//     value-preserving and is admissible in exactly one place: a Rust shift
//     AMOUNT, where rustc itself resizes the count and then masks it by
//     `lhs_width - 1`, making every discarded bit unobservable. It is
//     constructed only by [`shift_amount_resize_and_mask`], which applies the
//     mask itself so the bare truncation can never escape to another caller.
//
// A truncating conversion lowered as the identity is this tree's canonical
// false-proof bug (`tests/ui/contracts/contract_truncating_cast_stays_refused.rs`
// is the sibling lane's adversarial fixture for it in the mathematical-integer
// domain). [`value_preserving_conversion`] is the bit-vector-domain twin of
// that lane's `value_preserving_int_cast` and admits exactly the same set:
// same-signedness widening, unsigned into a STRICTLY wider signed target,
// identity — nothing else.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;

/// A Rust integer type's verification domain: its declared bit width and
/// signedness. `usize`/`isize` arrive here already resolved at the target
/// pointer width by `contracts::machine_int_ty_for_var`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub(crate) struct MachineDomain {
    pub(crate) width: u32,
    pub(crate) signed: bool,
}

/// The Rust integer widths this lane models. Every one is a power of two, which
/// is what makes the shift mask commute with a resize (see
/// [`shift_amount_resize_and_mask`]).
///
/// Trust: the set itself now lives in the strict-lane VERIFIED crate
/// `trust-widthconv`, which also owns the conversion rule table below. This is
/// a thin adapter from its `u8` 0/1 answer to the `bool` this module's callers
/// expect; there is no second copy of the width set here.
pub(crate) fn width_supported(width: u32) -> bool {
    trust_widthconv::width_supported(width) == 1
}

impl MachineDomain {
    pub(crate) fn new(width: u32, signed: bool) -> Option<Self> {
        width_supported(width).then_some(Self { width, signed })
    }

    pub(crate) fn parts(self) -> (u32, bool) {
        (self.width, self.signed)
    }

    /// `u32`, `i64`, … — for diagnostics.
    pub(crate) fn rust_name(self) -> String {
        format!("{}{}", if self.signed { 'i' } else { 'u' }, self.width)
    }
}

/// A conversion that preserves the MATHEMATICAL VALUE of the term.
///
/// There is no `Truncate` and no `Reinterpret` variant, and that absence is the
/// point: a caller that needs to move a value between domains can only ever be
/// handed something exact, or nothing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ValueConversion {
    /// The domains already agree.
    Identity,
    /// Prepend `extra` zero bits. Exact for a source whose values are all
    /// non-negative — i.e. an unsigned source.
    ZeroExtend(u32),
    /// Replicate the sign bit `extra` times. Exact for a two's-complement
    /// signed source: sign extension is the identity on the represented
    /// integer.
    SignExtend(u32),
}

impl ValueConversion {
    pub(crate) fn apply(self, value: Formula) -> Formula {
        match self {
            ValueConversion::Identity => value,
            ValueConversion::ZeroExtend(extra) => Formula::BvZeroExt(Box::new(value), extra),
            ValueConversion::SignExtend(extra) => Formula::BvSignExt(Box::new(value), extra),
        }
    }
}

/// THE RULE TABLE. `Some(conversion)` iff moving a value from `src` to `dst`
/// preserves the mathematical integer it denotes, for EVERY value of `src`.
///
///  1. `src == dst`                                   -> `Identity`.
///  2. unsigned -> unsigned, `dst.width > src.width`  -> `ZeroExtend`.
///     Every `src` value lies in `0 ..= 2^ws - 1`, which is a subset of
///     `0 ..= 2^wt - 1`, and zero extension is the inclusion map.
///  3. signed -> signed, `dst.width > src.width`      -> `SignExtend`.
///     Two's-complement sign extension is by definition the map that keeps the
///     represented integer; `-2^(ws-1) ..= 2^(ws-1)-1` is inside
///     `-2^(wt-1) ..= 2^(wt-1)-1` whenever `ws < wt`.
///  4. unsigned -> signed, `dst.width > src.width`    -> `ZeroExtend`.
///     The largest source value is `2^ws - 1`; since `ws < wt` and both are
///     integers, `ws <= wt - 1`, so `2^ws - 1 <= 2^(wt-1) - 1` = the signed
///     `wt` maximum. Zero extension (NOT sign extension) is the inclusion map,
///     because the source has no sign bit to replicate. The widest real case,
///     `u64 -> i128`, is `2^64 - 1 < 2^127`.
///  5. signed -> unsigned, ANY widths                 -> REFUSED.
///     `-1i32` denotes `-1`; no unsigned domain contains it. There is no
///     conversion, only a reinterpretation, and a reinterpretation changes the
///     value.
///  6. equal widths, signedness differs               -> REFUSED.
///     The bit pattern is unchanged but the value is not: `255u8` and `-1i8`
///     share `0xff`. `u8 -> i8` is exactly the sibling lane's fourth refused
///     neighbour.
///  7. `dst.width < src.width` (narrowing), ANY signedness -> REFUSED.
///     `2^32` is a `u64`; no `u32` denotes it. Modelling this as the identity
///     is the canonical false-proof bug this module exists to make
///     unrepresentable.
///
/// Rows 5-7 could in principle be admitted under a PROVEN range premise (a
/// signed value known non-negative, a wide value known to fit). This lane does
/// not carry such premises, so it refuses: an honest refusal is a correct
/// outcome, an unproven premise is not.
pub(crate) fn value_preserving_conversion(
    src: MachineDomain,
    dst: MachineDomain,
) -> Option<ValueConversion> {
    // Trust: rows 1-7 are DECIDED in the strict-lane VERIFIED crate
    // `trust-widthconv`, whose 100-point exhaustive oracle checks them against
    // the seven prose rules above and whose `replaced_consumer_body_is_
    // reproduced_exactly` runs this function's ORIGINAL body against the
    // replacement over `0..=200` x `0..=200` x both signednesses. Nothing is
    // re-decided here: this maps the answer onto the local type, which is the
    // one thing the verified crate cannot do (it may not name an enum).
    let code = trust_widthconv::conversion_code(
        src.width,
        u8::from(src.signed),
        dst.width,
        u8::from(dst.signed),
    );
    let extra = trust_widthconv::extension_bits(src.width, dst.width);
    match code {
        trust_widthconv::CONVERSION_IDENTITY => Some(ValueConversion::Identity),
        trust_widthconv::CONVERSION_ZERO_EXTEND => Some(ValueConversion::ZeroExtend(extra)),
        trust_widthconv::CONVERSION_SIGN_EXTEND => Some(ValueConversion::SignExtend(extra)),
        // `CONVERSION_REFUSED`, and any code this match does not name.
        _ => None,
    }
}

/// The single domain in which two operands can meet EXACTLY, with the
/// conversion each one needs to get there. `None` when no such domain exists in
/// the Rust width set.
///
/// Both operands must be able to reach the joined domain by a
/// [`value_preserving_conversion`], so the join inherits the rule table's
/// refusals: `u32` and `i32` have no exact join (neither fits the other, and
/// the join is not allowed to invent `i64`, which would silently change the
/// wrap width of any arithmetic beneath it); `u8` and `i8` likewise.
///
/// NOTE ON SCOPE: a join is only ever correct under an operator whose meaning
/// is the MATHEMATICAL relation between the two values — comparison and
/// equality. It is NEVER correct under wrapping arithmetic: `x + 1` for a `u32`
/// `x` wraps at `2^32`, and evaluating it in a joined 64-bit domain would make
/// `x + 1 > x` valid when the machine falsifies it at `u32::MAX`. Callers must
/// not use this to widen an arithmetic operand.
pub(crate) fn join(
    left: MachineDomain,
    right: MachineDomain,
) -> Option<(MachineDomain, ValueConversion, ValueConversion)> {
    // Trust: the joined WIDTH is `trust_widthconv::join_width`, whose clause
    // pair (`result >= left_width`, `result >= right_width`) is the reason a
    // candidate narrower than either operand may be skipped: a value-preserving
    // conversion never narrows (row 7), so the narrower candidate could not
    // have been reached from the wider operand and this loop would have
    // rejected it anyway. `a_width_below_an_operand_is_unreachable_from_it`
    // pins that converse.
    let joined_width = trust_widthconv::join_width(left.width, right.width);
    for candidate in [left, right] {
        if candidate.width != joined_width {
            continue;
        }
        if let (Some(from_left), Some(from_right)) = (
            value_preserving_conversion(left, candidate),
            value_preserving_conversion(right, candidate),
        ) {
            return Some((candidate, from_left, from_right));
        }
    }
    None
}

/// A resize of a BIT PATTERN. NOT value-preserving: `Truncate` discards high
/// bits outright. Constructible only through
/// [`shift_amount_resize_and_mask`], which masks the result so those bits
/// cannot be observed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum PatternResize {
    Identity,
    ZeroExtend(u32),
    /// Keep bits `high ..= 0`.
    Truncate {
        high: u32,
    },
}

impl PatternResize {
    fn apply(self, value: Formula) -> Formula {
        match self {
            PatternResize::Identity => value,
            PatternResize::ZeroExtend(extra) => Formula::BvZeroExt(Box::new(value), extra),
            PatternResize::Truncate { high } => {
                Formula::BvExtract { inner: Box::new(value), high, low: 0 }
            }
        }
    }
}

/// The resize rustc performs on a shift COUNT, followed immediately by rustc's
/// mask. The mask is applied here, in the same expression, so no caller can
/// take delivery of the unmasked truncation.
///
/// WHY A TRUNCATION IS EXACT HERE AND NOWHERE ELSE. `rustc_codegen_ssa`'s
/// `build_shift_expr_rhs` builds `lhs_width - 1` in the COUNT's own type, ANDs
/// the count with it, then truncates (count wider) or ZERO-extends (count
/// narrower, even when the count's Rust type is signed) to the shifted value's
/// width. This function reverses those two steps: resize first, mask second.
/// The orders agree because the mask `lhs_width - 1` observes only the low
/// `log2(lhs_width)` bits — at most 7 of them, since `lhs_width <= 128` — while
/// every Rust integer width is at least 8 bits. Zero extension and truncation
/// both leave the low 8 bits alone, so masking before or after selects the same
/// count.
///
/// Zero extension is right even for a SIGNED count. `(x: u64) << (-1i8)`:
/// rustc computes `0xff & 0x3f = 0x3f` in `i8` and zero-extends to `63u64`;
/// this function zero-extends `0xff` to `255u64` and masks to `63`. Sign
/// extension would give `2^64 - 1` and mask to `63` as well, so the two happen
/// to agree — but zero extension is what rustc emits, and matching rustc rather
/// than a coincidence is what keeps this exact if the mask ever moves.
///
/// `None` for an unsupported width on either side.
pub(crate) fn shift_amount_resize_and_mask(
    amount: Formula,
    source_width: u32,
    target_width: u32,
) -> Option<Formula> {
    let resize = shift_amount_resize(source_width, target_width)?;
    Some(Formula::BvAnd(
        Box::new(resize.apply(amount)),
        // Trust: the mask is `trust_widthconv::shift_mask`, whose clause
        // `result <= target_width` makes a mask wider than the value being
        // shifted unstatable — the direction that would admit a shift count
        // `>= width` (Rust UB) as a defined operation.
        Box::new(Formula::BitVec {
            value: i128::from(trust_widthconv::shift_mask(target_width)),
            width: target_width,
        }),
        target_width,
    ))
}

/// The resize half of [`shift_amount_resize_and_mask`], separated only so the
/// rule can be stated and tested on its own. Private: the mask is not optional.
fn shift_amount_resize(source_width: u32, target_width: u32) -> Option<PatternResize> {
    if !width_supported(source_width) || !width_supported(target_width) {
        return None;
    }
    Some(match source_width.cmp(&target_width) {
        std::cmp::Ordering::Less => PatternResize::ZeroExtend(target_width - source_width),
        std::cmp::Ordering::Greater => PatternResize::Truncate { high: target_width - 1 },
        std::cmp::Ordering::Equal => PatternResize::Identity,
    })
}

/// What a scan of a formula's value leaves found about their declared domains.
///
/// The distinction the old `Option<(u32, bool)>` could not draw, and which the
/// `e4.machine.mixed-domain` diagnostic therefore could not report: a formula
/// with NO domain-constraining leaf, a formula whose leaves DISAGREE, and a
/// formula containing a leaf that is not a machine value at all (a slice, a
/// reference, an unresolvable name) are three different refusals with three
/// different fixes.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) struct DomainScan {
    /// Every distinct declared domain reached, in a stable order.
    pub(crate) domains: Vec<MachineDomain>,
    /// Value leaves that carry no machine domain at all, by name.
    pub(crate) non_machine_leaves: Vec<String>,
}

impl DomainScan {
    pub(crate) fn observe(&mut self, domain: MachineDomain) {
        if !self.domains.contains(&domain) {
            self.domains.push(domain);
        }
    }

    pub(crate) fn observe_non_machine(&mut self, name: &str) {
        if !self.non_machine_leaves.iter().any(|seen| seen == name) {
            self.non_machine_leaves.push(name.to_string());
        }
    }

    /// The one domain every leaf agrees on. `None` when a leaf is not a machine
    /// value, when two leaves disagree, or when nothing constrains the domain
    /// at all.
    ///
    /// This is EXACTLY the predicate the translator has always used; the extra
    /// structure exists to explain a `None`, never to turn one into a `Some`.
    pub(crate) fn uniform(&self) -> Option<MachineDomain> {
        if !self.non_machine_leaves.is_empty() {
            return None;
        }
        match self.domains.as_slice() {
            [only] => Some(*only),
            _ => None,
        }
    }

    /// The single domain every observed domain can reach by a
    /// [`value_preserving_conversion`], if one of them is it. `None` when the
    /// disagreement is inexact (a signedness mix, or a `u128` with a signed
    /// partner) and therefore cannot be recovered by widening at all.
    pub(crate) fn exact_join(&self) -> Option<MachineDomain> {
        let mut joined = *self.domains.first()?;
        for domain in &self.domains[1..] {
            joined = join(joined, *domain)?.0;
        }
        Some(joined)
    }

    /// The refusal ledger for a diagnostic: exactly which of the three reasons
    /// applies, with the names and types involved, and — for a disagreement —
    /// whether widening could ever recover it. That last verdict is the
    /// difference between "this needs plumbing" and "this needs a premise no
    /// one has proved".
    pub(crate) fn refusal_detail(&self) -> String {
        let mut parts = Vec::new();
        if self.domains.len() > 1 {
            let mut names: Vec<String> =
                self.domains.iter().map(|domain| domain.rust_name()).collect();
            names.sort();
            let recoverable = match self.exact_join() {
                Some(joined) => format!("exact widening join at {}", joined.rust_name()),
                None => "no exact widening join exists".to_string(),
            };
            parts.push(format!("declared domains disagree: {} ({recoverable})", names.join(", ")));
        }
        if !self.non_machine_leaves.is_empty() {
            let mut names = self.non_machine_leaves.clone();
            names.sort();
            parts.push(format!("leaves with no machine domain: {}", names.join(", ")));
        }
        if parts.is_empty() {
            parts.push("no leaf declares a machine domain".to_string());
        }
        parts.join("; ")
    }
}

#[cfg(test)]
mod tests;
