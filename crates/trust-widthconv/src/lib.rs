#![no_std]
//! The Rust machine-integer WIDTH RULES the bit-vector lane meets two operands
//! with: which widths exist, whether moving a value between two of them
//! preserves the value, how many bits an extension adds, and the mask rustc
//! applies to a shift count.
//!
//! # Why this crate exists
//!
//! `trust_vcgen::machine_domain` opens with the reason, and it is the sharpest
//! statement of a false-proof hazard anywhere in the tree:
//!
//! > *A truncating conversion lowered as the identity is this tree's canonical
//! > false-proof bug.*
//!
//! `value_preserving_conversion` is the rule table that decides it. If it ever
//! answers `Identity` for `u64 -> u32`, every comparison beneath that cast is
//! decided in the wrong domain and the solver is handed a proposition nobody
//! stated. Nothing downstream re-checks it: the conversion is applied to the
//! `Formula` and the bit-vector translation proceeds. This is a
//! **false-hypothesis** site, not a cosmetic helper.
//!
//! The width SET that gates the whole table — `8 | 16 | 32 | 64 | 128` — is
//! written by hand **five times inside `trust-vcgen` alone**:
//!
//! | site | shape |
//! |---|---|
//! | `trust-vcgen/src/machine_domain.rs:53` | `width_supported` — the one this crate replaced |
//! | `trust-vcgen/src/contracts.rs:4036` | `rust_machine_width_supported` — a byte-identical second copy |
//! | `trust-vcgen/src/lib.rs:620` | `machine_int_domain`'s `matches!` |
//! | `trust-vcgen/src/lib.rs:873` | the `IntToBv` guard |
//! | `trust-vcgen/src/lib.rs:886` | the `BvToInt` guard |
//!
//! and **twenty-two more times outside it**, where — exactly as the nine
//! two's-complement bound sites of `trust-intbound` disagreed about their
//! domain — the copies **do not agree about whether `128` is a width**.
//! `trust-clean-carrier`, `trust-clean-origin` (4 sites), `trust-clean/prove`,
//! `trust-clean/clean_ground` and `trust-types/admissible_body` (4 sites) all
//! spell `8 | 16 | 32 | 64`; `trust-clean/trustir_adt`,
//! `trust-clean/mirsem/adt_shapes`, `trust-clean/mirsem/adt_compose`,
//! `trust-ir-bridge/lower` and `trust-machine-sem/concrete` spell
//! `8 | 16 | 32 | 64 | 128`. Those two answers are both defensible for their own
//! lane and the disagreement is invisible until a `u128` crosses between them.
//! This crate collapses the five inside `trust-vcgen`, which are the ones that
//! gate the conversion table, and leaves the rest named so a later reader can
//! see the split rather than rediscover it.
//!
//! # The domain is a set of FIVE SMALL NUMBERS, and that is what makes it verifiable
//!
//! `machine_domain` is *about* 128-bit values and it never *computes* on one.
//! Every arithmetic operation in the rule table is on a WIDTH:
//! `dst.width - src.width` and `target_width - 1`, over numbers drawn from
//! `{8, 16, 32, 64, 128}`. The values being converted are `Formula` nodes and
//! never enter the arithmetic. So the whole table lives in `u32` with room to
//! spare, and the `u128` blocker that stops
//! `docs/STRICT_VERIFICATION_FRAGMENT.md` §16.0's other eight sites does not
//! arise here at all. This is that section's rule at its cleanest: price a
//! candidate off the numbers it ADDS AND SUBTRACTS, not off the numbers it is
//! about.
//!
//! # THE SENTINEL, AND WHY IT POINTS THE OTHER WAY FROM `trust-intbound`
//!
//! Every function here is TOTAL — a `requires` is fatal under the strict lane
//! (fragment map §3) — so an out-of-domain width returns a sentinel.
//!
//! §16.1 records that `trust-intbound`'s sentinels are the WIDEST value,
//! because its answers are RANGE BOUNDS conjoined onto VCs and a bound that is
//! too narrow is a false hypothesis. **Every sentinel in this crate is the
//! NARROW end (`0`), and that is the same rule applied to a different use, not
//! a different rule.** Nothing here is a bound:
//!
//! | function | the answer is | too WIDE | too NARROW | so the sentinel is |
//! |---|---|---|---|---|
//! | [`width_supported`] | an admission test | admits an unmodelled width | fail-closed | `0` |
//! | [`conversion_code`] | an admission test with a tag | **admits a truncation as the identity — the canonical false proof** | fail-closed | `0` = REFUSED |
//! | [`extension_bits`] | a bit count for `BvZeroExt`/`BvSignExt` | malformed (too wide a result) | malformed | `0` |
//! | [`shift_mask`] | rustc's shift-count mask | **admits a shift count `>= width`, which is Rust UB, as a defined shift** | masks to `0`, a defined no-op shift | `0` |
//!
//! The two bolded cells are why. For `trust-intbound` the unsound direction was
//! NARROW; here it is WIDE in both of the load-bearing cases. **The direction
//! is a property of the consumer's use, and it is not stable across crates even
//! within one lane** — which is exactly what §15.5 says and is worth one more
//! data point, since this crate reached the opposite answer from the previous
//! one by applying the identical argument.
//!
//! # What is proved, and what is only tested
//!
//! The clause language accepts `result` against a bare literal or a bare
//! parameter and nothing built from an operator (fragment map §13.9, §14.8), so
//! `conversion_code(...) == 2` is not statable. Each clause's doc names the
//! wrong implementation it still admits. Every VALUE is pinned instead by
//! `oracle.rs`'s tests, which are **EXHAUSTIVE OVER THE WHOLE DOMAIN**: the
//! conversion table has 5 x 2 x 5 x 2 = 100 in-domain points and they are all
//! checked against a table transcribed from the seven prose rules in
//! `machine_domain`'s header, plus `0..=200` x `0..=200` for the width
//! predicates. There is no sampling anywhere in this crate's oracle.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

// Bootstrap rustc cannot parse Trust's native signature clauses, while the
// verified lane must retain those exact clause tokens. Each invocation below
// owns its function body once. Trust injects `cfg(trust_verify)` only while
// verification is active, selecting the native-clause expansion; an ordinary
// compiler emits the same function and body without the clauses.
#[cfg(trust_verify)]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret
            $($clauses)+
        { $($body)* }
    };
}

#[cfg(not(trust_verify))]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret { $($body)* }
    };
}

// ---------------------------------------------------------------------------
// The width set.
// ---------------------------------------------------------------------------

trust_contract_fn! {
/// `1` iff `w` is one of the five Rust machine integer widths this lane models
/// — `8`, `16`, `32`, `64`, `128` — and `0` otherwise.
///
/// **Call this before reading any other answer here.** The other four functions
/// are total and fail closed on an unsupported width, but they fail closed to
/// values that are also legitimate answers (`conversion_code` -> `0` is also
/// "this conversion is refused"; `shift_mask` -> `0` is also `shift_mask(1)`),
/// so this is the only function that distinguishes "unsupported" from "the
/// answer happens to be zero".
///
/// **Clause `result <= 1`.** Admits a function that always returns `0` (nothing
/// is a machine width — fail-closed, safe, useless) and one that always returns
/// `1` (**every** width is a machine width — the unsound direction). Neither is
/// ruled out by the clause; both are ruled out by
/// `width_supported_is_exactly_the_five_rust_widths`, which checks all of
/// `0..=200` against a literal set written from the Rust language reference
/// rather than from this file.
pub fn width_supported(w: u32) -> u8
clauses [ensures result <= 1]
{
    raw_width_supported(w)
}
}

/// The constants live in THIS body, not one call further down: fragment map
/// §12.4 — a contracted wrapper discharges only when the bundled member's OWN
/// body contains the pinning constants, and a one-hop delegation to a pinning
/// helper pins nothing.
fn raw_width_supported(w: u32) -> u8 {
    if w == 8 {
        return 1;
    }
    if w == 16 {
        return 1;
    }
    if w == 32 {
        return 1;
    }
    if w == 64 {
        return 1;
    }
    if w == 128 {
        return 1;
    }
    0
}

// ---------------------------------------------------------------------------
// The conversion rule table.
// ---------------------------------------------------------------------------

/// A conversion that would DISCARD or REINTERPRET bits. Never emit anything.
pub const CONVERSION_REFUSED: u8 = 0;
/// The two domains already agree; emit the operand unchanged.
pub const CONVERSION_IDENTITY: u8 = 1;
/// Prepend [`extension_bits`] zero bits (`BvZeroExt`).
pub const CONVERSION_ZERO_EXTEND: u8 = 2;
/// Replicate the sign bit [`extension_bits`] times (`BvSignExt`).
pub const CONVERSION_SIGN_EXTEND: u8 = 3;

trust_contract_fn! {
/// Which value-preserving conversion moves a `src` value into the `dst` domain,
/// as one of the four `CONVERSION_*` codes. `signed` arguments are `1` for a
/// signed domain and `0` for an unsigned one; **any other value is refused**,
/// so a caller that forgets to normalise a flag gets a refusal rather than a
/// silently-wrong row.
///
/// This is a transcription of the seven prose rules in
/// `trust_vcgen::machine_domain`'s header and it changes none of them:
///
/// 1. `src == dst` -> identity.
/// 2. unsigned -> unsigned, strictly wider -> zero-extend.
/// 3. signed -> signed, strictly wider -> sign-extend.
/// 4. unsigned -> signed, strictly wider -> zero-extend (the source has no sign
///    bit to replicate, and `2^ws - 1 <= 2^(wt-1) - 1` whenever `ws < wt`).
/// 5. signed -> unsigned, any widths -> REFUSED (`-1i32` is in no unsigned
///    domain).
/// 6. equal widths, signedness differs -> REFUSED (`255u8` and `-1i8` share
///    `0xff` and denote different integers).
/// 7. any narrowing -> REFUSED. **This is the row the false-proof bug lives in.**
///
/// **Clause `result <= 3`.** This is a weak clause and the doc says so rather
/// than dressing it up: it rules out a garbage code that no `apply` arm handles
/// and nothing else. It still admits a function that always returns `0` (refuse
/// everything — fail-closed and useless) *and* one that always returns `3`
/// (sign-extend everything, including every narrowing — **the exact unsound
/// answer this table exists to prevent**). The clause language cannot state
/// `result == 0 when dst_width < src_width` — an implication over parameters is
/// not writable (§13.9). What rules those out is
/// `conversion_code_matches_the_seven_prose_rules`, which is exhaustive over
/// all 100 in-domain points, and `narrowing_is_refused_at_every_pair`, which
/// re-derives the narrowing row alone from the width ORDER rather than from the
/// table. The strict lane cannot see a wrong code here — `trust_widthconv_strict_gate.sh`
/// mutation D exhibits one at exit 0.
pub fn conversion_code(src_width: u32, src_signed: u8, dst_width: u32, dst_signed: u8) -> u8
clauses [ensures result <= 3]
{
    raw_conversion_code(src_width, src_signed, dst_width, dst_signed)
}
}

fn raw_conversion_code(src_width: u32, src_signed: u8, dst_width: u32, dst_signed: u8) -> u8 {
    if raw_width_supported(src_width) == 0 {
        return 0;
    }
    if raw_width_supported(dst_width) == 0 {
        return 0;
    }
    // A signedness flag that is neither 0 nor 1 is a caller defect. Fail closed
    // rather than letting `!= 1` read it as "unsigned", which would answer
    // ZeroExtend for a domain whose signedness is not known.
    if src_signed > 1 {
        return 0;
    }
    if dst_signed > 1 {
        return 0;
    }
    if src_width == dst_width {
        // Row 1, then row 6.
        if src_signed == dst_signed {
            return 1;
        }
        return 0;
    }
    // Row 7. Every remaining pair is a strict widening.
    if dst_width < src_width {
        return 0;
    }
    if src_signed == 1 {
        // Row 3 (signed -> signed), then row 5 (signed -> unsigned).
        if dst_signed == 1 {
            return 3;
        }
        return 0;
    }
    // Rows 2 and 4: an unsigned source widens by zero extension into either
    // signedness.
    2
}

trust_contract_fn! {
/// How many bits a widening from `src_width` to `dst_width` prepends — the
/// `extra` operand of `BvZeroExt` / `BvSignExt`. `0` when the pair is not a
/// widening, or when either width is outside `8..=128`.
///
/// **Clauses `result <= 120` and `result <= dst_width`.** `120` is the widest
/// real extension (`u8 -> i128`), and it is far inside `u32`, so the bound is
/// not the vacuous type maximum §16.7 had to settle for. The pair rules out
/// every implementation that returns something TOO LARGE, including the
/// plausible-looking `return dst_width` (`128` violates the literal bound) and
/// any arm that answers a wider extension than its own destination can hold. It
/// does **not** rule out a function that always returns `0`, which is the
/// fail-closed direction and is the sentinel this function already uses;
/// `extension_bits_is_the_width_difference` is exhaustive over `0..=200` x
/// `0..=200` and rules that out.
///
/// **WHY THIS IS A FIFTEEN-ARM CONSTANT CHAIN AND NOT `dst_width - src_width`.**
/// It was written as the subtraction first, guarded exactly as the clauses need
/// (`dst_width <= 128`, `src_width >= 8`, `src_width <= dst_width`, so
/// `result <= 128 - 8` and `result <= dst_width` both follow by linear
/// arithmetic over `u32`). Measured 2026-08-30, that form reports **6 proved /
/// 4 UNKNOWN** of its 10 postcondition rows — while its
/// `arithmetic_overflow_sub` row PROVES, so the subtraction's own safety is
/// established and it is the BOUND ON THE DIFFERENCE that is not. The chain
/// below is the identical function over the whole live domain and proves every
/// row. See `docs/STRICT_VERIFICATION_FRAGMENT.md` §17.1.
///
/// The chain is also exact where the subtraction was a superset: `9..=127` is
/// not a Rust width and is now refused rather than answered.
pub fn extension_bits(src_width: u32, dst_width: u32) -> u32
clauses [ensures result <= 120 ensures result <= dst_width]
{
    if dst_width == 128 {
        if src_width == 8 {
            return 120;
        }
        if src_width == 16 {
            return 112;
        }
        if src_width == 32 {
            return 96;
        }
        if src_width == 64 {
            return 64;
        }
        return 0;
    }
    if dst_width == 64 {
        if src_width == 8 {
            return 56;
        }
        if src_width == 16 {
            return 48;
        }
        if src_width == 32 {
            return 32;
        }
        return 0;
    }
    if dst_width == 32 {
        if src_width == 8 {
            return 24;
        }
        if src_width == 16 {
            return 16;
        }
        return 0;
    }
    if dst_width == 16 {
        if src_width == 8 {
            return 8;
        }
        return 0;
    }
    0
}
}

// ---------------------------------------------------------------------------
// The shift count mask.
// ---------------------------------------------------------------------------

trust_contract_fn! {
/// The mask rustc ANDs a shift COUNT with before shifting a `target_width`-bit
/// value: `target_width - 1`, i.e. `7`, `15`, `31`, `63`, `127`. `0` for an
/// unsupported width.
///
/// `rustc_codegen_ssa`'s `build_shift_expr_rhs` builds `lhs_width - 1` in the
/// count's own type and ANDs the count with it. A verifier that models the mask
/// as anything WIDER admits a shift count `>= target_width` as a defined
/// operation — which in Rust is UB — so the unsound direction here is up, and
/// the sentinel is `0` (mask everything away, giving a defined shift by zero).
///
/// **Clauses `result <= 127` and `result <= target_width`.** The second is the
/// load-bearing one and it is a bound against a PARAMETER: it makes a mask that
/// is wider than the value being shifted unstatable, which is precisely the
/// unsound direction above. Together they rule out every too-large answer,
/// including `target_width` itself (the off-by-one that admits a shift by
/// exactly the width) — no: `result <= target_width` admits exactly that
/// off-by-one, and `shift_mask_is_one_below_the_width` is what rules it out.
/// The clause pair admits any implementation returning something too SMALL,
/// including a constant `0`; too small is the fail-closed direction (it turns
/// a real shift into a no-op and the obligation becomes unprovable, never
/// falsely proved).
pub fn shift_mask(target_width: u32) -> u32
clauses [ensures result <= 127 ensures result <= target_width]
{
    if target_width == 8 {
        return 7;
    }
    if target_width == 16 {
        return 15;
    }
    if target_width == 32 {
        return 31;
    }
    if target_width == 64 {
        return 63;
    }
    if target_width == 128 {
        return 127;
    }
    0
}
}

// ---------------------------------------------------------------------------
// The join.
// ---------------------------------------------------------------------------

trust_contract_fn! {
/// The only width at which two operands of widths `left_width` and
/// `right_width` can meet without either being narrowed: the wider of the two.
///
/// A value-preserving conversion never narrows (rule 7 of [`conversion_code`]),
/// so a meeting width strictly below either operand is unreachable from that
/// operand and no candidate outside `{left_width, right_width}` may be invented
/// — inventing `i64` for a `u32`/`i32` pair would silently change the wrap
/// width of any arithmetic beneath it. This function answers only the WIDTH;
/// whether the meeting is legal at all is [`conversion_code`]'s question and
/// the caller must still ask it (`u32` and `i32` have no exact join at any
/// width).
///
/// **Clauses `result >= left_width` and `result >= right_width`.** Two variable
/// bounds in the SAME direction, which fragment map §14.1 measures as
/// discharging (it is the OPPOSITE-direction pair that does not). Together they
/// pin the result to `>= max(left_width, right_width)`, so the only surviving
/// wrong implementations return something too WIDE — and too wide is the
/// fail-closed direction here, because a width outside the supported set is
/// refused by [`width_supported`] at the caller and a supported-but-too-wide
/// one is refused by [`conversion_code`]'s narrowing row on the way back down.
/// A `min` in place of the `max`, a constant `0`, and returning `left_width`
/// unconditionally are all refuted by the clause pair alone —
/// `trust_widthconv_strict_gate.sh` mutation C watches the last of those fail.
pub fn join_width(left_width: u32, right_width: u32) -> u32
clauses [ensures result >= left_width ensures result >= right_width]
{
    if left_width > right_width {
        return left_width;
    }
    right_width
}
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The five Rust machine integer widths, written from the Rust language
    /// reference (`u8`/`u16`/`u32`/`u64`/`u128` and their signed twins) rather
    /// than read out of this crate. Every "is this a width" assertion below
    /// compares against THIS list, so a mutation of `raw_width_supported` has
    /// nothing to agree with.
    const RUST_WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];

    /// The rule table, TRANSCRIBED FROM THE SEVEN PROSE RULES in
    /// `trust_vcgen::machine_domain`'s header comment, in the order they are
    /// written there. It shares no code with `raw_conversion_code`: the
    /// implementation dispatches on `src_width == dst_width` first and then on
    /// signedness, and this oracle dispatches on the seven rules in their
    /// stated order. Two different control flows, one answer.
    fn rule_table_oracle(src_w: u32, src_s: bool, dst_w: u32, dst_s: bool) -> u8 {
        // Rule 1: the domains already agree.
        if src_w == dst_w && src_s == dst_s {
            return CONVERSION_IDENTITY;
        }
        // Rule 6: equal widths, signedness differs.
        if src_w == dst_w {
            return CONVERSION_REFUSED;
        }
        // Rule 7: any narrowing.
        if dst_w < src_w {
            return CONVERSION_REFUSED;
        }
        // Rule 5: signed source, unsigned target, at any widths.
        if src_s && !dst_s {
            return CONVERSION_REFUSED;
        }
        // Rule 3: signed -> signed, strictly wider.
        if src_s && dst_s {
            return CONVERSION_SIGN_EXTEND;
        }
        // Rules 2 and 4: unsigned source, strictly wider, either target
        // signedness.
        CONVERSION_ZERO_EXTEND
    }

    fn flag(b: bool) -> u8 {
        if b { 1 } else { 0 }
    }

    // -----------------------------------------------------------------------
    // width_supported
    // -----------------------------------------------------------------------

    #[test]
    fn width_supported_is_exactly_the_five_rust_widths() {
        for w in 0..=200u32 {
            let want = u8::from(RUST_WIDTHS.contains(&w));
            assert_eq!(width_supported(w), want, "width_supported({w})");
        }
    }

    /// The clause `result <= 1` is satisfied by a constant `0` and by a
    /// constant `1`. This is the test that separates them, and it is the reason
    /// the doc names both.
    #[test]
    fn width_supported_is_neither_constant() {
        assert_eq!(width_supported(32), 1);
        assert_eq!(width_supported(33), 0);
    }

    // -----------------------------------------------------------------------
    // conversion_code
    // -----------------------------------------------------------------------

    /// EXHAUSTIVE over the whole in-domain space: 5 x 2 x 5 x 2 = 100 points,
    /// every one checked against the prose rules. No sampling.
    #[test]
    fn conversion_code_matches_the_seven_prose_rules() {
        let mut checked = 0;
        for src_w in RUST_WIDTHS {
            for src_s in [false, true] {
                for dst_w in RUST_WIDTHS {
                    for dst_s in [false, true] {
                        let want = rule_table_oracle(src_w, src_s, dst_w, dst_s);
                        assert_eq!(
                            conversion_code(src_w, flag(src_s), dst_w, flag(dst_s)),
                            want,
                            "conversion_code({src_w}, {src_s}, {dst_w}, {dst_s})"
                        );
                        checked += 1;
                    }
                }
            }
        }
        assert_eq!(checked, 100, "the domain is 5 x 2 x 5 x 2 and must be walked whole");
    }

    /// Rule 7 alone, re-derived from the width ORDER rather than from the
    /// table. This is the row the canonical false-proof bug lives in, so it
    /// gets an assertion that does not go through `rule_table_oracle` either.
    #[test]
    fn narrowing_is_refused_at_every_pair() {
        for src_w in RUST_WIDTHS {
            for dst_w in RUST_WIDTHS {
                if dst_w >= src_w {
                    continue;
                }
                for src_s in 0..=1u8 {
                    for dst_s in 0..=1u8 {
                        assert_eq!(
                            conversion_code(src_w, src_s, dst_w, dst_s),
                            CONVERSION_REFUSED,
                            "a narrowing {src_w} -> {dst_w} was not refused"
                        );
                    }
                }
            }
        }
    }

    /// The specific answer the module doc names as the false proof: `u64 ->
    /// u32` must never be the identity.
    #[test]
    fn u64_to_u32_is_not_the_identity() {
        assert_eq!(conversion_code(64, 0, 32, 0), CONVERSION_REFUSED);
        assert_ne!(conversion_code(64, 0, 32, 0), CONVERSION_IDENTITY);
    }

    /// Rule 4's widest real case, and the one whose justification is an
    /// inequality rather than an inclusion: `u64 -> i128` is ZERO extension,
    /// not sign extension.
    #[test]
    fn unsigned_into_wider_signed_is_zero_extension() {
        assert_eq!(conversion_code(64, 0, 128, 1), CONVERSION_ZERO_EXTEND);
        assert_eq!(conversion_code(8, 0, 16, 1), CONVERSION_ZERO_EXTEND);
    }

    /// An unsupported width refuses on either side, and an out-of-range
    /// signedness flag refuses too — the fail-closed direction the doc claims.
    #[test]
    fn conversion_code_fails_closed_off_the_domain() {
        assert_eq!(conversion_code(24, 0, 32, 0), CONVERSION_REFUSED);
        assert_eq!(conversion_code(32, 0, 24, 0), CONVERSION_REFUSED);
        assert_eq!(conversion_code(0, 0, 32, 0), CONVERSION_REFUSED);
        for bad in 2..=255u8 {
            assert_eq!(conversion_code(8, bad, 16, 0), CONVERSION_REFUSED, "src_signed={bad}");
            assert_eq!(conversion_code(8, 0, 16, bad), CONVERSION_REFUSED, "dst_signed={bad}");
        }
    }

    // -----------------------------------------------------------------------
    // extension_bits
    // -----------------------------------------------------------------------

    /// EXHAUSTIVE over `0..=200` x `0..=200`. The oracle is the arithmetic
    /// difference, computed here and nowhere in the crate — the shipped body is
    /// a constant chain precisely so that it cannot be checking itself.
    #[test]
    fn extension_bits_is_the_width_difference() {
        for src_w in 0..=200u32 {
            for dst_w in 0..=200u32 {
                let in_domain = RUST_WIDTHS.contains(&src_w) && RUST_WIDTHS.contains(&dst_w);
                let want = if in_domain && dst_w >= src_w { dst_w - src_w } else { 0 };
                assert_eq!(extension_bits(src_w, dst_w), want, "extension_bits({src_w}, {dst_w})");
            }
        }
    }

    /// The clause pair admits a constant `0`. This is what rules it out.
    #[test]
    fn extension_bits_is_not_the_constant_zero() {
        assert_eq!(extension_bits(8, 128), 120);
        assert_eq!(extension_bits(32, 64), 32);
    }

    /// The two functions must agree about which pairs are conversions at all:
    /// `extension_bits` is nonzero exactly where `conversion_code` is a strict
    /// widening. Pins the guard superset the doc used to carry.
    #[test]
    fn extension_bits_agrees_with_conversion_code_on_the_supported_set() {
        for src_w in RUST_WIDTHS {
            for dst_w in RUST_WIDTHS {
                let widening = dst_w > src_w;
                assert_eq!(
                    extension_bits(src_w, dst_w) > 0,
                    widening,
                    "extension_bits({src_w}, {dst_w}) disagrees with the widening order"
                );
                // Where a conversion IS admitted and is not the identity, the
                // extension amount is what its `apply` will use.
                if conversion_code(src_w, 0, dst_w, 0) == CONVERSION_ZERO_EXTEND {
                    assert_eq!(extension_bits(src_w, dst_w), dst_w - src_w);
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // shift_mask
    // -----------------------------------------------------------------------

    /// The oracle is `w - 1`, which is what `rustc_codegen_ssa`'s
    /// `build_shift_expr_rhs` builds. EXHAUSTIVE over `0..=200`.
    #[test]
    fn shift_mask_is_one_below_the_width() {
        for w in 0..=200u32 {
            let want = if RUST_WIDTHS.contains(&w) { w - 1 } else { 0 };
            assert_eq!(shift_mask(w), want, "shift_mask({w})");
        }
    }

    /// THE SENTINEL DIRECTION, stated as an assertion rather than as prose.
    /// A mask at or above the width would admit a shift count `>= width`, which
    /// is Rust UB, as a defined operation. Every answer this function gives
    /// must be strictly below the width it is a mask for, and the unsupported
    /// answer must be the NARROW end (`0`), not a wide one.
    #[test]
    fn shift_mask_is_strictly_below_its_width_and_the_sentinel_is_narrow() {
        for w in RUST_WIDTHS {
            assert!(shift_mask(w) < w, "shift_mask({w}) = {} is not below {w}", shift_mask(w));
        }
        for w in [0u32, 1, 7, 9, 63, 65, 127, 129, 200] {
            assert_eq!(shift_mask(w), 0, "the unsupported sentinel must be the narrow end");
        }
    }

    /// The mask must select every bit position a legal shift count can name,
    /// and no more: `0..w` must all survive the mask and `w` must not.
    #[test]
    fn shift_mask_admits_exactly_the_legal_counts() {
        for w in RUST_WIDTHS {
            let m = shift_mask(w);
            for count in 0..w {
                assert_eq!(count & m, count, "a legal count {count} was masked at width {w}");
            }
            assert_ne!(w & m, w, "the illegal count {w} survived the mask at width {w}");
        }
    }

    // -----------------------------------------------------------------------
    // join_width
    // -----------------------------------------------------------------------

    /// EXHAUSTIVE over `0..=200` x `0..=200` against an independent `max`.
    #[test]
    fn join_width_is_the_wider_of_the_two() {
        for a in 0..=200u32 {
            for b in 0..=200u32 {
                let want = if a > b { a } else { b };
                assert_eq!(join_width(a, b), want, "join_width({a}, {b})");
            }
        }
    }

    /// The join must be one of the two operands — never an invented width.
    /// `machine_domain::join`'s doc singles this out: inventing `i64` for a
    /// `u32`/`i32` pair would silently change the wrap width of any arithmetic
    /// beneath it.
    #[test]
    fn join_width_invents_no_width() {
        for a in RUST_WIDTHS {
            for b in RUST_WIDTHS {
                let j = join_width(a, b);
                assert!(j == a || j == b, "join_width({a}, {b}) = {j} is neither operand");
            }
        }
    }

    /// Both operands must be able to REACH the joined width by a conversion
    /// this crate admits, whenever their signednesses allow it at all. This is
    /// the property `machine_domain::join` relies on when it stops trying the
    /// narrower candidate.
    #[test]
    fn both_operands_reach_the_joined_width_when_signedness_allows() {
        for a in RUST_WIDTHS {
            for b in RUST_WIDTHS {
                for s in 0..=1u8 {
                    let j = join_width(a, b);
                    assert_ne!(
                        conversion_code(a, s, j, s),
                        CONVERSION_REFUSED,
                        "{a} cannot reach the join {j}"
                    );
                    assert_ne!(
                        conversion_code(b, s, j, s),
                        CONVERSION_REFUSED,
                        "{b} cannot reach the join {j}"
                    );
                }
            }
        }
    }

    /// The CONVERSE, which is what licenses `join` to skip the narrower
    /// candidate: a width strictly below either operand is unreachable from
    /// that operand, so trying it could never have succeeded.
    #[test]
    fn a_width_below_an_operand_is_unreachable_from_it() {
        for a in RUST_WIDTHS {
            for candidate in RUST_WIDTHS {
                if candidate >= a {
                    continue;
                }
                for s in 0..=1u8 {
                    assert_eq!(
                        conversion_code(a, s, candidate, s),
                        CONVERSION_REFUSED,
                        "{a} reached the narrower {candidate}"
                    );
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // The replaced consumer, reproduced exactly.
    // -----------------------------------------------------------------------

    /// `trust_vcgen::machine_domain::value_preserving_conversion`'s ORIGINAL
    /// body, transcribed verbatim from the pre-extraction source, run against
    /// the replacement over the whole domain plus a margin of unsupported
    /// widths. This is the analogue of `trust-intbound`'s
    /// `replaced_consumer_body_is_reproduced_exactly`, and it is the only thing
    /// in this crate that asserts the extraction did not change what the
    /// verifier computes.
    fn original_value_preserving_conversion(
        src_w: u32,
        src_s: bool,
        dst_w: u32,
        dst_s: bool,
    ) -> Option<(u8, u32)> {
        fn original_width_supported(width: u32) -> bool {
            matches!(width, 8 | 16 | 32 | 64 | 128)
        }
        if !original_width_supported(src_w) || !original_width_supported(dst_w) {
            return None;
        }
        if src_w == dst_w && src_s == dst_s {
            return Some((CONVERSION_IDENTITY, 0));
        }
        if dst_w < src_w {
            return None;
        }
        let extra = dst_w - src_w;
        match (src_s, dst_s) {
            (false, false) => Some((CONVERSION_ZERO_EXTEND, extra)),
            (true, true) => Some((CONVERSION_SIGN_EXTEND, extra)),
            (false, true) if extra > 0 => Some((CONVERSION_ZERO_EXTEND, extra)),
            _ => None,
        }
    }

    #[test]
    fn replaced_consumer_body_is_reproduced_exactly() {
        for src_w in 0..=200u32 {
            for dst_w in 0..=200u32 {
                for src_s in [false, true] {
                    for dst_s in [false, true] {
                        let want = original_value_preserving_conversion(src_w, src_s, dst_w, dst_s);
                        let code = conversion_code(src_w, flag(src_s), dst_w, flag(dst_s));
                        let got = if code == CONVERSION_REFUSED {
                            None
                        } else if code == CONVERSION_IDENTITY {
                            Some((code, 0))
                        } else {
                            Some((code, extension_bits(src_w, dst_w)))
                        };
                        assert_eq!(
                            got, want,
                            "extraction diverges at ({src_w}, {src_s}) -> ({dst_w}, {dst_s})"
                        );
                    }
                }
            }
        }
    }

    /// The shift mask half of the same reproduction: the original built
    /// `target_width - 1` inline.
    #[test]
    fn replaced_shift_mask_is_reproduced_exactly() {
        for w in 0..=200u32 {
            let original = if matches!(w, 8 | 16 | 32 | 64 | 128) { Some(w - 1) } else { None };
            let got = if width_supported(w) == 1 { Some(shift_mask(w)) } else { None };
            assert_eq!(got, original, "shift mask diverges at width {w}");
        }
    }
}
