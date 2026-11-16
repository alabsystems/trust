// EXACT semantics for the body-less rustc arithmetic/bitvector intrinsics.
//
// A `#[rustc_intrinsic]` marked `must_be_overridden` has NO MIR in any build, so
// there is nothing to bundle and nothing to lower: a model is the only route by
// which a call to one can ever be discharged. Until now the only model was the
// BOOLEAN `is_total_rustc_intrinsic` (trust-ir-bridge `lower.rs`): "this call
// cannot panic". That is true, and it is also everything the verifier knew — the
// destination was left an unconstrained havoc, so `x.count_ones() <= 32` was not
// merely unproved, it was REFUTABLE (the SMT lane is free to pick 4 billion).
//
// This module replaces the boolean with a DEFINITION for the intrinsics whose
// meaning is exactly expressible in the bitvector theory Trust already has
// (`Formula::{IntToBv, BvExtract, BvConcat, BvToInt}`), so those intrinsics move
// from "named axiom" to "defined function" and stop being trusted facts.
//
// # THE SOUNDNESS STAKE IS THE OPPOSITE OF THE USUAL ONE
//
// Every other lane in this crate REMOVES hypotheses when it is unsure; being
// wrong there costs completeness. This module ADDS facts to the hypothesis set.
// A wrong definition here is not an incompleteness — it is a FALSE PROOF that
// silently validates wrong programs forever. Three rules follow, and they are
// enforced by the tests in `intrinsic_semantics_tests.rs`:
//
//  1. Every definition below is checked EXHAUSTIVELY at width 8 (all 256 inputs,
//     both signednesses) against the real Rust operation, through a generic
//     SMT-LIB evaluator that knows nothing about intrinsics.
//  2. Every definition has a falsification fixture (real extracted MIR, in
//     `tests/intrinsic_semantics_realmir.rs`) that must be REFUTED and would be
//     wrongly PROVED under an off-by-one width, a wrong signedness, or a
//     reversed byte/bit order.
//  3. Where an exact definition is NOT certain or NOT affordable, this module
//     emits only the RANGE fact `0 <= r <= W`. That is legitimate, strictly
//     better than the previous unconstrained havoc, and much safer than a guess.
//
// # WHAT IS DEFINED, AND WHAT IS DELIBERATELY ONLY BOUNDED
//
// | intrinsic     | signature          | model                                   |
// |---------------|--------------------|-----------------------------------------|
// | `ctpop`       | `fn(T) -> u32`     | EXACT: `Σ_{i<W} bit_i`, plus `0<=r<=W`  |
// | `bswap`       | `fn(T) -> T`       | EXACT: byte cascade (W=8 is IDENTITY)   |
// | `bitreverse`  | `fn(T) -> T`       | EXACT: bit cascade                      |
// | `cttz`        | `fn(T) -> u32`     | `0<=r<=W`, `r == W <-> x == 0`, and     |
// |               |                    | EXACT `ctpop(!x & (x-1))` for a         |
// |               |                    | CONSTANT argument                       |
// | `ctlz`        | `fn(T) -> u32`     | same, exact term over the bit-reversed  |
// |               |                    | word, same constant-argument gate       |
//
// An earlier revision left `ctlz`/`cttz` at the bound + iff only, on the ground
// that the obvious exact form — a W-deep `Ite` chain over the bit extracts — is
// pruned by trust-mc and blows past `ITE_ELIM_CASE_CAP` in the lifting pass.
// That objection was to the ENCODING, not to exactness: `cttz(x)` is also
// `ctpop(!x & (x - 1))` — the mask of trailing zeros has a 1 exactly below the
// lowest set bit (and is all-ones at `x == 0`, giving the required `W`) — which
// is Ite-free, linear in `W` (`12W - 1` nodes, see the cost table), and made of
// operators the BV theory already carries (`BvNot`/`BvSub`/`BvAnd`); `ctlz` is
// the same composition over `bitreverse(x)`.
//
// # WHY THE EXACT COUNTING TERM IS GATED ON A CONSTANT ARGUMENT
//
// Measured (2026-08-30, realmir harness, in-process ay, debug build): with the
// exact `cttz`/`ctlz` equation in the hypothesis set for a FREE argument, the
// load-bearing clause family this model exists to serve — `x >= 1 ensures
// result <= W-1`, the fact that makes `1 << (W - 1 - r)` a defined shift —
// DEGRADES CATASTROPHICALLY, even though its cheap iff+range proof is still
// present in the same hypothesis set:
//
// | free-argument row               | W  | without exact | with exact        |
// |---------------------------------|----|---------------|-------------------|
// | `x>=1 -> cttz(x) <= W-1` (TRUE) |  8 |       —       | Proved, 7.8 s     |
// | `x>=1 -> ctlz(x) <= W-1` (TRUE) |  8 |       —       | Proved, 8.3 s     |
// | `x>=1 -> cttz(x) <= 15`  (TRUE) | 16 |       —       | TIMEOUT at 120 s  |
// | `x>=1 -> ctlz(x) <= 15`  (TRUE) | 16 |       —       | TIMEOUT at 120 s  |
// | `x>=1 -> cttz(x) <= 31`  (TRUE) | 32 | Proved, 8 ms  | TIMEOUT at 120 s  |
//
// ("—" = not measured; the without-exact path is width-independent — the same
// three-step iff+range derivation the measured 8 ms row takes.)
//
// The equation is not wrong — the width-8 differential is exhaustive — but its
// presence sends the solver into Int<->BV saturation it does not return from.
// (`ctpop` does not hit this: its own free-argument bound row `<= W` is decided
// by the range fact alone, which the solver does find.) So the exact equation
// is emitted ONLY when the argument operand is a compile-time CONSTANT
// (`Operand::Constant`, e.g. `cttz(8u32)` — dumps confirm literals arrive so):
// the term is then fully concrete, the solver folds it (measured 2-18 ms
// across widths 8-32, BOTH verdict directions, realmir literal rows), and
// there is no free-variable search
// for it to pollute. A parameter pinned by `requires x == 8` is NOT a constant
// operand and deliberately stays on the iff+range facts — fail-closed on
// completeness, never on soundness; `tests/intrinsic_semantics_realmir.rs`
// pins both sides of the gate AND the 8 ms free-row proof as a regression
// guard against re-widening.
//
// The bound + iff facts are emitted at EVERY width — they are Int-lane facts
// the BV-declining consumers (trust-wp) can still use, and outside the
// constant gate they are all there is, exactly as before this module learned
// the counting definitions.
//
// THE `_nonzero` SIBLINGS ARE EXCLUDED BY NAME. `ctlz_nonzero`/`cttz_nonzero`
// are `unsafe` and UB at zero; they carry a precondition a caller can violate,
// so they must be PROVED, never modeled. The exact-name match below is what
// keeps them out, and `marked_intrinsic_recognizer_excludes_partial_siblings`
// pins it.
//
// THE ZERO EDGE CASES THAT CATCH A WRONG DEFINITION: `ctlz(0)` and `cttz(0)` are
// `W`, not `0` (that is precisely what distinguishes them from the `_nonzero`
// forms), and `bswap` at width 8 is the IDENTITY, not a reversal.

use super::*;

/// The rustc intrinsics this module gives a value semantics.
///
/// Deliberately NOT an alias of trust-ir-bridge's `is_total_rustc_intrinsic`
/// list nor of trust-clean's `PureTotalIntrinsic`: those two answer different
/// questions (panic-freedom, and kernel-certified call admission) over larger
/// sets. An entry here means "Trust can state what this call RETURNS", which is
/// a strictly stronger claim, so the set is its own and is smaller.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ValueModeledIntrinsic {
    /// `ctpop<T>(x: T) -> u32` — population count. Backs `T::count_ones`.
    Ctpop,
    /// `ctlz<T>(x: T) -> u32` — leading zeros; `ctlz(0) == W`. Backs
    /// `T::leading_zeros`. NOT `ctlz_nonzero`, which is UB at zero.
    Ctlz,
    /// `cttz<T>(x: T) -> u32` — trailing zeros; `cttz(0) == W`. Backs
    /// `T::trailing_zeros`. NOT `cttz_nonzero`, which is UB at zero.
    Cttz,
    /// `bswap<T>(x: T) -> T` — byte-order reversal. Backs `T::swap_bytes`.
    Bswap,
    /// `bitreverse<T>(x: T) -> T` — bit-order reversal. Backs `T::reverse_bits`.
    Bitreverse,
}

/// Widths at which an exact bitvector expansion is emitted. Above this the
/// bit-count intrinsics keep their range facts and `bswap`/`bitreverse` emit
/// NOTHING (fail closed — an unmodeled dest is the status quo, never a guess).
///
/// TERM COST, MEASURED as `Formula` nodes in the emitted term over a variable
/// argument (`emitted_term_counts_match_the_documented_cost_table` pins every
/// cell). The argument subterm is duplicated once per bit because `Formula` is a
/// tree, so this counts it; production adds one outer `BvToInt` to the two
/// cascades.
///
/// | intrinsic    | W=8 | W=16 | W=32 | W=64 | W=128 | closed form   |
/// |--------------|-----|------|------|------|-------|---------------|
/// | `ctpop`      |  39 |   79 |  159 |  319 |   639 | `5W - 1`      |
/// | `bitreverse` |  31 |   63 |  127 |  255 |   511 | `4W - 1`      |
/// | `bswap`      |   3 |    7 |   15 |   31 |    63 | `4·(W/8) - 1` |
/// | `cttz`       |  95 |  191 |  383 |   —  |    —  | `12W - 1`     |
/// | `ctlz`       | 559 | 2143 | 8383 |   —  |    —  | `8W² + 6W - 1`|
///
/// (`cttz` duplicates its 9-node trailing-zeros mask once per extracted bit;
/// `ctlz` duplicates the whole `4W - 1`-node reversal cascade the same way —
/// quadratic, but only ever emitted over a constant argument, where it folds.)
///
/// TERM DEPTH is bounded separately and is the number that actually bit: the
/// combine is a BALANCED fold ([`balanced_fold`]), so depth is logarithmic, and
/// the same test pins every cell.
///
/// | intrinsic    | W=8 | W=16 | W=32 | W=64 | W=128 |
/// |--------------|-----|------|------|------|-------|
/// | `ctpop`      |   7 |    8 |    9 |   10 |    11 |
/// | `bitreverse` |   6 |    7 |    8 |    9 |    10 |
/// | `bswap`      |   3 |    4 |    5 |    6 |     7 |
/// | `cttz`       |   9 |   10 |   11 |    — |     — |
/// | `ctlz`       |  13 |   15 |   17 |    — |     — |
///
/// # WHY THE CAP IS 32 AND NOT 64
///
/// END-TO-END SOLVER COST, measured on the real-MIR corpus in
/// `tests/intrinsic_semantics_realmir.rs` with the in-process ay backend
/// (`nodes` counts the WHOLE postcondition obligation, not just the definition):
///
/// | fixture                       | W  | nodes | verdict | solve    |
/// |-------------------------------|----|-------|---------|----------|
/// | `ctpop(x) <= 8`   (TRUE)      |  8 |   110 | Proved  |     3 ms |
/// | `ctpop(x) <= 7`   (FALSE)     |  8 |   110 | Refuted |  3816 ms |
/// | `ctpop(x) <= 32`  (TRUE)      | 32 |   350 | Proved  |    26 ms |
/// | `ctpop(0) == 0`   (TRUE)      | 32 |   353 | Proved  |   909 ms |
/// | `ctpop(!0) == 32` (TRUE)      | 32 |   353 | Proved  |   668 ms |
/// | `ctpop(x) >= 1`   (FALSE)     | 32 |   350 | Refuted |   876 ms |
/// | `ctpop(x) <= 31`  (FALSE)     | 32 |   350 | Unknown | 34107 ms |
/// | `bswap(x)` byte order (TRUE)  | 32 |    34 | Proved  |    52 ms |
/// | `bitreverse(1) == 128` (TRUE) |  8 |    50 | Proved  |    61 ms |
///
/// Two readings, both load-bearing:
///
///  * PROVING a true clause is cheap — tens of milliseconds for the range
///    consequence, under a second for the exact ones. That is the direction the
///    lane exists for, and it is affordable at 32.
///  * REFUTING a false one is where the exact expansion is paid for: the solver
///    must construct a 32-bit witness word, and one row already blew a 30-second
///    budget. Doubling to 64 doubles the term AND the search space, and I could
///    NOT measure it — the corpus above is the widest end-to-end data there is
///    without a stage2 rebuild (~1.8 h), which was not available.
///
/// So 64 is DECLINED for lack of measurement, not because it is known bad.
/// Declining is fail-closed: a `u64` `count_ones` keeps its `[0, 64]` range fact
/// (which is what makes `x.count_ones() <= 64` provable at every width) and its
/// destination is otherwise modeled exactly as it was before this lane existed.
/// Raise the cap when a corpus sweep says 64 is affordable — and re-measure the
/// refutation column, not just the proof column.
///
/// 128 is excluded for a second, independent reason: the Int lane cannot carry
/// a `u128` value (`Formula::Int` is i128-backed and `Formula::has_large_integers`
/// rejects anything past i64 in the trust-wp lane), which is why every other
/// range/value builder in this crate gates on `width < 128`.
const MAX_EXACT_INTRINSIC_WIDTH: u32 = 32;

/// Is this operand a compile-time constant — the gate on the exact `cttz`/
/// `ctlz` equation?
///
/// The module header carries the full measured table; the short version: the
/// counting equations are CORRECT at every emitted width (exhaustive width-8
/// differential, edge patterns at 16/32), but for a FREE argument their
/// presence sends ay into Int<->BV saturation that turns the 8 ms iff+range
/// proof of `x >= 1 -> r <= W-1` into a 120 s timeout. For a CONSTANT argument
/// there is nothing to search — the term folds — and the solve is 2-18 ms at
/// widths 8-32 in BOTH verdict directions (measured, `tests/
/// intrinsic_semantics_realmir.rs`). So constants get the definition and free
/// arguments keep the iff+range model that already serves the shift-
/// definedness clause family. `argument_is_stable` has already admitted the
/// operand; this narrows WHICH admitted operands get the exact equation.
fn argument_is_compile_time_constant(operand: &Operand) -> bool {
    matches!(operand, Operand::Constant(_))
}

/// STRICT, fail-closed classification of a `Terminator::Call` callee path into
/// the value-modeled intrinsic set.
///
/// # Why the marker is REQUIRED here
///
/// `TRUST_RUSTC_INTRINSIC_PATH_PREFIX` (`@trust-rustc-intrinsic::`) is stamped
/// by the MIR extractor only after rustc's `TyCtxt` confirms the direct `FnDef`
/// is an exact modeled compiler intrinsic, and `@` cannot occur in a Rust
/// identifier — so authored source cannot manufacture it by declaring a
/// lookalike `mycrate::intrinsics::ctpop`. Measured against the stage2 dump
/// (`-Ztrust-dump=mir:`) for `core::intrinsics::ctpop(x)`: the callee arrives as
/// `@trust-rustc-intrinsic::core::intrinsics::ctpop::<u32>`, so a bit intrinsic
/// ALWAYS arrives marked and requiring the marker costs no capability.
///
/// Contrast trust-clean's `PureTotalIntrinsic::classify`, which additionally
/// admits an UNMARKED legacy spelling for the saturating pair. That is benign
/// there because its model is an OPAQUE `call_result` asserting nothing. Here
/// the model asserts a VALUE, so an unmarked path — which a user crate can
/// spell — is refused outright.
///
/// After the marker, the grammar is exactly trust-clean's
/// `classify_intrinsic_segments`: generic segments dropped, `intrinsics` as the
/// penultimate segment, at most one crate root and it must be `core`/`std`.
/// A forged root (`evil::intrinsics::ctpop`), extra segments
/// (`a::intrinsics::ctpop::b`), or a partial sibling (`ctlz_nonzero`) decline.
pub(crate) fn classify_value_modeled_intrinsic(callee: &str) -> Option<ValueModeledIntrinsic> {
    let marked = callee.strip_prefix(trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX)?;
    match marked_intrinsic_name(marked)? {
        "ctpop" => Some(ValueModeledIntrinsic::Ctpop),
        "ctlz" => Some(ValueModeledIntrinsic::Ctlz),
        "cttz" => Some(ValueModeledIntrinsic::Cttz),
        "bswap" => Some(ValueModeledIntrinsic::Bswap),
        "bitreverse" => Some(ValueModeledIntrinsic::Bitreverse),
        // `ctlz_nonzero` / `cttz_nonzero` (UB at zero — a PRECONDITION, not a
        // total function), `unchecked_*`, `transmute`, and every unmodeled name
        // decline. Fail closed: an unrecognized intrinsic keeps its havoc'd dest.
        _ => None,
    }
}

/// The `saturating_add`/`saturating_sub` intrinsic under the MARKED spelling, or
/// `None`.
///
/// `library/core/src/intrinsics/mod.rs` declares exactly two: `saturating_add`
/// and `saturating_sub`. There is NO `saturating_mul` intrinsic — `T::saturating_mul`
/// is an ordinary library method — so this lane must never admit that name, even
/// though the sibling METHOD recognizer (`saturating_add_sub_method`) does.
///
/// Returns the same `&'static str` tags that recognizer returns, so both feed
/// ONE clamp construction (`saturating_call_dest_value`). The MIN/MAX boundary
/// is therefore stated in exactly one place; a restated boundary would be a
/// second place to get the saturation edge wrong.
pub(crate) fn marked_saturating_intrinsic(callee: &str) -> Option<&'static str> {
    let marked = callee.strip_prefix(trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX)?;
    match marked_intrinsic_name(marked)? {
        "saturating_add" => Some("saturating_add"),
        "saturating_sub" => Some("saturating_sub"),
        _ => None,
    }
}

/// The intrinsic NAME of a marker-stripped def path, under the exact grammar
/// `[core|std::]intrinsics::<name>[::<generics>]`. `None` for anything else.
fn marked_intrinsic_name(marked: &str) -> Option<&str> {
    // Drop the monomorphization/generic segments (`<u8>`, `<impl …>`).
    let mut segments = marked.split("::").filter(|s| !s.starts_with('<'));
    let s0 = segments.next()?;
    let s1 = segments.next()?;
    match (segments.next(), segments.next()) {
        // `intrinsics::<name>` — the dump's truncated spelling.
        (None, _) if s0 == "intrinsics" => Some(s1),
        // At most one crate root, and it must be a real std/core root.
        (Some(s2), None) if matches!(s0, "core" | "std") && s1 == "intrinsics" => Some(s2),
        // Extra or foreign segments ⇒ fail closed.
        _ => None,
    }
}

/// `x` reinterpreted as a width-`width` bitvector.
///
/// SMT-LIB `((_ int2bv w) t)` is `t mod 2^w`, so this is the two's-complement
/// bit pattern for a NEGATIVE `x` as well as the plain binary encoding for a
/// non-negative one — exactly the machine word the intrinsic operates on. This
/// is the same Int↔BV bridge `symbolic_binop` uses to model `&`/`|`/`^`/`<<`.
fn as_bits(x: &Formula, width: u32) -> Formula {
    Formula::IntToBv(Box::new(x.clone()), width)
}

/// Bit `i` of the BV-sorted `xb` (LSB is bit 0) as an Int-sorted `0`/`1`.
///
/// `BvToInt(_, 1, /*signed=*/false)` is load-bearing: the SIGNED reading of a
/// 1-bit vector is `{0, -1}`, which would make the population count a count of
/// zeros minus ones. `ctpop_exhaustive_width8_matches_rust` catches that.
fn bv_bit_as_int(xb: &Formula, i: u32) -> Formula {
    Formula::BvToInt(
        Box::new(Formula::BvExtract { inner: Box::new(xb.clone()), high: i, low: i }),
        1,
        false,
    )
}

/// Population count of an ALREADY-BV-SORTED term, as the sum of its extracted
/// bits. Shared by `ctpop_value` (over `int2bv(x)`), `cttz_value` (over the
/// trailing-zeros mask) and `ctlz_value` (over the reversed word's mask).
fn ctpop_of_bits(xb: &Formula, width: u32) -> Formula {
    balanced_fold((0..width).map(|i| bv_bit_as_int(xb, i)).collect(), |a, b| {
        Formula::Add(Box::new(a), Box::new(b))
    })
}

/// `ctpop(x)` as the SUM OF THE EXTRACTED BITS — the definition, not a bound.
///
/// `Σ_{i=0}^{W-1} bit_i(x)`. Exact at every width and for both signednesses
/// (population count is a function of the bit pattern alone). Left-nested `Add`
/// so the term is linear-arithmetic shaped for the Int lane.
///
/// Deliberately NOT the SWAR/`x - ((x >> 1) & 0x5555…)` cascade, which is ~12
/// terms instead of ~3W but is far easier to get subtly wrong and would need a
/// per-width magic-constant table — a second place to get it wrong.
pub(super) fn ctpop_value(x: &Formula, width: u32) -> Formula {
    ctpop_of_bits(&as_bits(x, width), width)
}

/// The TRAILING-ZEROS MASK of a BV-sorted word: `!xb & (xb - 1)`.
///
/// For a nonzero word with `t` trailing zeros, `xb - 1` flips exactly the low
/// `t` zeros to ones and the lowest set bit to zero, and `!xb` has ones exactly
/// where `xb` has zeros — so the conjunction keeps the low `t` bits (both
/// factors are 1 there), clears bit `t` (`!xb` is 0 there), and clears every
/// higher bit (`xb - 1` equals `xb` there, so the factors are complementary).
/// At `xb == 0` the subtraction WRAPS to all-ones and `!xb` is all-ones, so the
/// mask is all-ones — population count `W`, which is exactly `cttz(0)`. The
/// zero case therefore needs no special arm; the wrap IS the definition.
fn trailing_zeros_mask(xb: Formula, width: u32) -> Formula {
    let one = as_bits(&Formula::Int(1), width);
    Formula::BvAnd(
        Box::new(Formula::BvNot(Box::new(xb.clone()), width)),
        Box::new(Formula::BvSub(Box::new(xb), Box::new(one), width)),
        width,
    )
}

/// `cttz(x)` EXACTLY, as `ctpop(!x & (x - 1))` — Ite-free and linear in `W`.
///
/// Exact for both signednesses for the same reason `ctpop` is: `int2bv`
/// recovers the bit pattern, and trailing-zero count is a function of the bit
/// pattern alone. The width-8 differential checks all 256 inputs of each.
pub(super) fn cttz_value(x: &Formula, width: u32) -> Formula {
    ctpop_of_bits(&trailing_zeros_mask(as_bits(x, width), width), width)
}

/// `ctlz(x)` EXACTLY, as `cttz` of the BIT-REVERSED word: the reversal maps
/// leading zeros to trailing zeros, and [`bitreverse_bits`] is the already-
/// tested cascade (its own exhaustive differential runs at widths 8-64).
///
/// The reversal cascade is duplicated once per extracted bit of the outer
/// popcount, so this term is QUADRATIC in `W` (`8W² + 6W - 1` nodes) — benign
/// under the constant-argument gate, where the whole term folds.
pub(super) fn ctlz_value(x: &Formula, width: u32) -> Formula {
    ctpop_of_bits(&trailing_zeros_mask(bitreverse_bits(x, width), width), width)
}

/// `bswap(x)` as the byte cascade: the result's HIGH byte is `x`'s LOW byte.
///
/// `concat` puts its first argument in the HIGH bits, so folding
/// `concat(concat(byte_0, byte_1), byte_2) …` lays byte 0 highest — a reversal.
///
/// AT WIDTH 8 THIS IS THE IDENTITY (one byte, no concat), which is the real
/// `u8::swap_bytes` semantics and a trap for any implementation that "reverses"
/// unconditionally. `None` for a width that is not a positive multiple of 8.
pub(super) fn bswap_bits(x: &Formula, width: u32) -> Option<Formula> {
    if width == 0 || width % 8 != 0 {
        return None;
    }
    let xb = as_bits(x, width);
    let byte =
        |k: u32| Formula::BvExtract { inner: Box::new(xb.clone()), high: 8 * k + 7, low: 8 * k };
    Some(balanced_fold((0..width / 8).map(byte).collect(), |hi, lo| {
        Formula::BvConcat(Box::new(hi), Box::new(lo))
    }))
}

/// `bitreverse(x)` as the bit cascade: the result's MSB is `x`'s LSB.
///
/// Same fold direction as [`bswap_bits`], one bit at a time. At width 8,
/// `1u8.reverse_bits() == 128` — unlike `bswap`, this is never the identity for
/// a width above 1, which is what separates the two definitions in the tests.
pub(super) fn bitreverse_bits(x: &Formula, width: u32) -> Formula {
    let xb = as_bits(x, width);
    let bit = |i: u32| Formula::BvExtract { inner: Box::new(xb.clone()), high: i, low: i };
    balanced_fold((0..width).map(bit).collect(), |hi, lo| {
        Formula::BvConcat(Box::new(hi), Box::new(lo))
    })
}

/// Combine `items` left-to-right with `combine`, as a BALANCED tree.
///
/// ORDER-PRESERVING, so it is usable for the non-commutative `BvConcat` as well
/// as for `Add`: each pass pairs ADJACENT elements and a trailing odd element
/// carries forward untouched, so the leaf sequence is never permuted. Node count
/// is identical to a left-nested fold (`n - 1` internal nodes for `n` leaves);
/// only the DEPTH changes, from `n` to `ceil(log2 n)`.
///
/// WHY THIS IS NOT A MICRO-OPTIMIZATION. A left-nested 32-term sum is a
/// 32-DEEP `Formula`, and every consumer in the pipeline walks it by ordinary
/// recursion — the VC generator, the SSA-versioning rebinder, the SMT/ay bridge,
/// the printer. Measured before this change: the `ctpop::<u32>` obligations
/// overflowed libtest's default 2 MiB thread stack in a debug build. Balanced,
/// the same obligation is 5 levels deep instead of 32, which puts these terms
/// back in the same depth class as ordinary arithmetic the pipeline already
/// handles everywhere.
///
/// Panics on an empty input; every caller passes `width >= 1` leaves.
fn balanced_fold(
    mut items: Vec<Formula>,
    combine: impl Fn(Formula, Formula) -> Formula,
) -> Formula {
    while items.len() > 1 {
        let len = items.len();
        let mut write = 0;
        let mut read = 0;
        while read + 1 < len {
            let left = std::mem::replace(&mut items[read], Formula::Bool(false));
            let right = std::mem::replace(&mut items[read + 1], Formula::Bool(false));
            items[write] = combine(left, right);
            write += 1;
            read += 2;
        }
        if read < len {
            if write != read {
                items.swap(write, read);
            }
            write += 1;
        }
        items.truncate(write);
    }
    items.pop().unwrap_or(Formula::Bool(false))
}

/// The width and signedness of `operand`'s integer type, or `None` for a
/// non-integer (the intrinsics are declared `<T: Copy>`, so the type — not the
/// name — is what pins the model to an integer).
fn int_operand_shape(func: &VerifiableFunction, operand: &Operand) -> Option<(u32, bool)> {
    match crate::operand_ty_cow(func, operand).as_deref() {
        Some(Ty::Int { width, signed }) => Some((*width, *signed)),
        _ => None,
    }
}

/// Every fact Trust can state about `subject`, the destination of a
/// value-modeled intrinsic call at `terminator`. Empty when the terminator is
/// not such a call, when the argument is not an integer, or when the width is
/// past [`MAX_EXACT_INTRINSIC_WIDTH`] and no bound applies.
///
/// `subject` is passed in rather than derived because the two consumers name the
/// destination differently: the guard-map lane uses the `place_to_var_name`
/// alias (`__ret` for the return slot), while the postcondition lane must use
/// the RAW `_0` the `#[ensures]` clause reads. Identical facts, two names — the
/// same split the saturating/`wrapping_neg`/clamp pins already carry.
///
/// # Soundness gates (any miss ⇒ no facts at all)
///
///  * the callee is the MARKED intrinsic spelling under the exact grammar
///    ([`classify_value_modeled_intrinsic`]) — a user function cannot spell it;
///  * arity 1 and the destination is a whole local (no projection);
///  * the destination local is single-static-assignment — otherwise
///    `let p = &mut d; *p = huge` between the call and the use makes the fact
///    stale, the same hazard `is_single_static_assignment` closes for the
///    min/max/clamp and saturating pins;
///  * the ARGUMENT is a whole-local copy/move of a single-static-assignment
///    local, or a constant. Every fact here MENTIONS the argument, so an
///    argument that can be rewritten between the call and the use would tie the
///    destination to the WRONG value — a strictly stronger gate than the
///    saturating pin needs, applied because these facts also flow through the
///    postcondition lane where no versioning re-binds them.
pub(crate) fn value_modeled_intrinsic_facts<'a>(
    func: &VerifiableFunction,
    terminator: &'a Terminator,
    subject: &Formula,
) -> Option<(&'a Place, Vec<Formula>)> {
    let Terminator::Call { func: callee, args, dest, .. } = terminator else {
        return None;
    };
    if args.len() != 1 || !dest.projections.is_empty() {
        return None;
    }
    let dest_shape = match crate::local_ty_ref(func, dest.local) {
        Some(Ty::Int { width, signed }) => (*width, *signed),
        _ => return None,
    };
    let (width, signed) = int_operand_shape(func, &args[0])?;
    if width == 0 {
        return None;
    }
    let kind = classify_value_modeled_intrinsic(callee)?;
    // The DESTINATION type must agree with the intrinsic's declared signature, or
    // this is a misextraction and every fact below would be sorted wrongly.
    // `library/core/src/intrinsics/mod.rs`:
    //   `ctpop`/`ctlz`/`cttz` : `fn(T) -> u32`  — any integer dest is consistent,
    //                           and the `[0, W]` bound is about the COUNT, so the
    //                           dest width is irrelevant to its truth;
    //   `bswap`/`bitreverse`  : `fn(T) -> T`    — the dest must be EXACTLY `T`,
    //                           because the emitted `BvToInt(_, width, signed)`
    //                           reads the result under `T`'s width/signedness.
    if matches!(kind, ValueModeledIntrinsic::Bswap | ValueModeledIntrinsic::Bitreverse)
        && dest_shape != (width, signed)
    {
        return None;
    }
    if !is_single_static_assignment(func, dest.local) {
        return None;
    }
    if !argument_is_stable(func, &args[0]) {
        return None;
    }
    let x = crate::operand_to_formula(func, &args[0]);
    let mut facts = Vec::new();
    match kind {
        // `ctpop`/`ctlz`/`cttz` return `u32`, NOT `T` — checked against
        // `library/core/src/intrinsics/mod.rs`. The result is a COUNT in
        // `[0, W]`, so both bounds hold at every width and are emitted even
        // when the exact expansion is declined.
        ValueModeledIntrinsic::Ctpop
        | ValueModeledIntrinsic::Ctlz
        | ValueModeledIntrinsic::Cttz => {
            facts.push(Formula::Ge(Box::new(subject.clone()), Box::new(Formula::Int(0))));
            facts.push(Formula::Le(
                Box::new(subject.clone()),
                Box::new(Formula::Int(i128::from(width))),
            ));
        }
        ValueModeledIntrinsic::Bswap | ValueModeledIntrinsic::Bitreverse => {}
    }
    match kind {
        ValueModeledIntrinsic::Ctpop if width <= MAX_EXACT_INTRINSIC_WIDTH => {
            facts.push(Formula::Eq(Box::new(subject.clone()), Box::new(ctpop_value(&x, width))));
        }
        // `ctlz(x) == W  <->  x == 0`, and the same for `cttz`. Both directions
        // are definitional: a zero word has W leading (and W trailing) zeros,
        // and a word with ANY bit set has at most W-1 of either. Emitted at
        // EVERY width — they are pure Int-lane facts a BV-declining consumer
        // (trust-wp fail-closes on every `Bv*` node) can still use, they are
        // what decides the free-argument shift-definedness clause family
        // (`x != 0 -> r < W`), and outside the constant gate below they are
        // all there is.
        ValueModeledIntrinsic::Ctlz | ValueModeledIntrinsic::Cttz => {
            let is_w = || {
                Formula::Eq(Box::new(subject.clone()), Box::new(Formula::Int(i128::from(width))))
            };
            let is_zero = || Formula::Eq(Box::new(x.clone()), Box::new(Formula::Int(0)));
            facts.push(Formula::Implies(Box::new(is_w()), Box::new(is_zero())));
            facts.push(Formula::Implies(Box::new(is_zero()), Box::new(is_w())));
            // The EXACT definitions (verified-sysroot §5 step 1 remainder,
            // 2026-08-30): `cttz` as `ctpop(!x & (x-1))`, `ctlz` as the same
            // mask over the bit-reversed word — emitted ONLY for a
            // compile-time-constant argument, under the shared width cap. The
            // gate is a MEASURED interference boundary, not a soundness one:
            // see `argument_is_compile_time_constant` and the module header
            // table. Outside it the arm keeps exactly the facts it emitted
            // before — fail-closed on completeness, never a guess.
            if argument_is_compile_time_constant(&args[0]) && width <= MAX_EXACT_INTRINSIC_WIDTH {
                let def = match kind {
                    ValueModeledIntrinsic::Cttz => cttz_value(&x, width),
                    _ => ctlz_value(&x, width),
                };
                facts.push(Formula::Eq(Box::new(subject.clone()), Box::new(def)));
            }
        }
        ValueModeledIntrinsic::Bswap if width <= MAX_EXACT_INTRINSIC_WIDTH => {
            if let Some(bits) = bswap_bits(&x, width) {
                facts.push(Formula::Eq(
                    Box::new(subject.clone()),
                    Box::new(Formula::BvToInt(Box::new(bits), width, signed)),
                ));
            }
        }
        ValueModeledIntrinsic::Bitreverse if width <= MAX_EXACT_INTRINSIC_WIDTH => {
            facts.push(Formula::Eq(
                Box::new(subject.clone()),
                Box::new(Formula::BvToInt(Box::new(bitreverse_bits(&x, width)), width, signed)),
            ));
        }
        // Past the width cap: `bswap`/`bitreverse` have no bound to fall back on
        // (every value of `T` is a possible result), so nothing is emitted and
        // the destination keeps exactly the modeling it had before this module.
        ValueModeledIntrinsic::Ctpop
        | ValueModeledIntrinsic::Bswap
        | ValueModeledIntrinsic::Bitreverse => {}
    }
    // Nothing to say ⇒ `None`, so a caller's `else if let` chain falls through to
    // the lane that would have handled the call before this module existed.
    (!facts.is_empty()).then_some((dest, facts))
}

/// Is `operand` safe to name inside a fact that must remain true at every point
/// where the fact is used?
///
/// A constant always is. A whole-local copy/move is only when the local has ONE
/// meaning everywhere: either exactly one visible def
/// (`is_single_static_assignment`, which also fails on any `&mut`/`AddressOf` of
/// the local and so closes the write-through-a-pointer staleness hole) or no def
/// at all because it is an entry parameter ([`is_abi_written_parameter`]).
/// A projection is never admitted: the fact would name the base local while
/// depending on a field that can be written independently.
fn argument_is_stable(func: &VerifiableFunction, operand: &Operand) -> bool {
    match operand {
        Operand::Constant(_) => true,
        Operand::Copy(place) | Operand::Move(place) => {
            place.projections.is_empty()
                && (is_single_static_assignment(func, place.local)
                    || is_abi_written_parameter(func, place.local))
        }
        _ => false,
    }
}

/// A local with NO def anywhere in the body — an ENTRY PARAMETER, written once
/// by the ABI before the first block and never again.
///
/// This is the shape the compiler actually emits for `ctpop(x)` on a parameter
/// (`args: [Copy(_1)]`, measured on the stage2 dump). Since the parameter-entry-def
/// budget landed, `is_single_static_assignment` answers `true` for such a local too
/// and this arm no longer decides anything on its own; it is kept because it is
/// STRICTER on one shape the other is not — a `Deref`-first store `*x = …` spends no
/// budget there and is refused here.
///
/// SOUND for the same reason single-assignment is: the symbol has ONE meaning at
/// every program point. The `local_mut_escapes` conjunct closes the write
/// channel a def scan cannot see — `let p = &mut x; *p = other;` stores through
/// `*p`, whose place local is `p`, so it is invisible to the scan below. A
/// `Deref`-first store (`*x = …`) mutates the pointee rather than the local, but
/// it is refused anyway: an integer argument can never be its target, so the
/// strictness costs nothing.
fn is_abi_written_parameter(func: &VerifiableFunction, local: usize) -> bool {
    if local == 0 || local > func.body.arg_count {
        return false;
    }
    if local_mut_escapes(func, local) {
        return false;
    }
    func.body.blocks.iter().all(|block| {
        block
            .stmts
            .iter()
            .all(|stmt| !matches!(stmt, Statement::Assign { place, .. } if place.local == local))
            && !matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == local)
    })
}
