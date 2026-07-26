// trust-semantics: clean-kernel definitions for Trust's safety predicates.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Kernel-checked denotations for Trust's safety predicates — Stage 1 of
//! `PROOF_OF_PERFECTION.md`.
//!
//! Historically `RustVIR.noOverflow` was an opaque `Expr::const_str` (an
//! uninterpreted symbol; see `clean-rust-sem/proof_obligation.rs`): the
//! verifier could *mention* "no overflow" but the kernel had no idea what it
//! meant. This crate replaces that placeholder with a REAL clean-kernel
//! [`clean_kernel::Declaration::Definition`]:
//!
//! ```text
//! RustVIR.noOverflow : Int -> Int -> Int -> Prop
//!   := fun (min result max : Int) => And (Int.le min result) (Int.le result max)
//! ```
//!
//! i.e. `min <= result <= max`. The definition type-checks against a clean
//! [`Environment`] (the kernel accepts it — see [`overflow_safety_env`]), so the
//! safety property now has a denotation the kernel understands.
//!
//! The companion [`noOverflow_violation_formula`] emits the VIOLATION (the
//! negation, `result < min OR result > max`) as a [`trust_types::Formula`] in
//! the **exact** shape `trust-vcgen`'s `range.rs` emits for an overflow VC, so
//! the kernel definition and the SMT obligation denote the same arithmetic
//! fact. The two min/max helpers here are byte-for-byte copies of range.rs's
//! `type_min_formula` / `type_max_formula`. The copy is locked from the OTHER
//! side: `trust-vcgen`'s `range.rs` takes this crate as a dev-dependency and
//! compares both the helpers and the emitted violation term against its own
//! definitions. It has to be that direction — `range.rs` is `pub(crate)`, and a
//! comparison written here could only restate the encoding rather than read
//! it.
//!
//! ## Honesty / scope
//!
//! ONLY the **Add/Sub** overflow class on the **QF_LIA (Int)** fragment is
//! modeled here: `min <= result <= max` over mathematical integers is linear
//! and decidable. **Mul** overflow and **signed-div `INT_MIN / -1`** are
//! emitted by the VC generator as **BitVec** obligations (outside QF_LIA, see
//! `generate.rs::v2_unsigned_bv_overflow_formula` /
//! `v2_signed_bv_overflow_formula`); those are NOT coerced into this Int
//! definition and remain fail-closed in the verifier. Folding a BitVec
//! overflow into this Int `min <= result <= max` shape would change its
//! meaning and risk a false-PROVE — so we deliberately do not.

#![forbid(unsafe_code)]

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level};
use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// Integer type bounds — byte-identical to trust-vcgen/src/range.rs.
//
// CARDINAL: these MUST agree with range.rs exactly so the violation formula
// this crate emits matches the overflow VC the generator emits. The two
// functions are copied verbatim (not re-implemented); the tests that hold them
// equal live in trust-vcgen's `range.rs`, where the authoritative definitions
// are in scope. The tests below pin values only, and cannot detect a change
// range.rs makes to its encoding.
// ---------------------------------------------------------------------------

/// Maximum value for an integer type, as a [`Formula`].
///
/// For unsigned 128-bit this is [`Formula::UInt`] (`u128::MAX > i128::MAX`,
/// so it cannot be a [`Formula::Int`]); everything else is [`Formula::Int`].
/// Mirrors `trust_vcgen::range::type_max_formula`.
///
/// TOTAL (panic-free for every `u32` width) without changing the result for any
/// in-domain unsigned width (`8/16/32/64/128`): the historical `(1i128 << width)
/// - 1` `else` arm UNDERFLOWED at `width == 127` (`1 << 127` is `i128::MIN`, then
/// `- 1`) and SHIFT-OVERFLOWED at `width >= 129`. Those out-of-domain widths now
/// saturate to `i128::MAX` (exactly `2^127 - 1`, the true 127-bit unsigned max, and
/// the value the historical wrapping arithmetic produced) — a defined,
/// non-panicking over-approximation that never makes a real value look in-range.
#[must_use]
pub fn type_max_formula(width: u32, signed: bool) -> Formula {
    if signed {
        Formula::Int(signed_max(width))
    } else if width == 128 {
        Formula::UInt(u128::MAX)
    } else if width <= 126 {
        // 1 <= width <= 126: `2^width - 1` fits i128 and `1i128 << width` is in range.
        Formula::Int((1i128 << width) - 1)
    } else {
        // width == 127 (`2^127 - 1 = i128::MAX`) or out-of-domain `width >= 129`.
        Formula::Int(i128::MAX)
    }
}

/// Minimum value for an integer type, as a [`Formula`].
/// Mirrors `trust_vcgen::range::type_min_formula`.
#[must_use]
pub fn type_min_formula(width: u32, signed: bool) -> Formula {
    if signed { Formula::Int(signed_min(width)) } else { Formula::Int(0) }
}

/// Minimum value for a signed integer of the given bit width.
/// Mirrors `trust_vcgen::range::signed_min`.
///
/// # Trust contract (precondition)
///
/// The only meaningful signed bit-widths are `1 <= width && width <= 128`.
/// Under the staged Trust verifier this is the precondition to attach:
///
/// ```text
/// #[requires(1 <= width && width <= 128)]
/// ```
///
/// (Expressed here as a doc contract rather than a `#[requires(..)]` attribute
/// because that attribute desugars through `#![feature(contracts)]`, an
/// unstable feature the dev-time stable toolchain rejects with `E0554`; the
/// integrator re-attaches it once building under `trustc`.) Under that
/// precondition the body is panic-free: `width >= 1` makes `width - 1` not
/// underflow, and the `else` branch only runs when `width != 128`, so
/// `width <= 127` and the shift amount `width - 1 <= 126 < 128` is in range.
///
/// The body below is *total* (panic-free for every `u32`) WITHOUT changing the
/// result for any in-contract width: for `1 <= width <= 128` it returns exactly
/// `-(1i128 << (width - 1))` (and `i128::MIN` at `width == 128`), identical to
/// the historical body. Out-of-domain widths (`width == 0` or `width > 128`),
/// which previously panicked, now return the saturated extreme `i128::MIN`
/// instead of overflowing — a defined, non-panicking value. Routing an
/// out-of-contract width to a concrete bound (rather than fabricating an
/// arbitrary in-range value) keeps this a sound over-approximation: it never
/// makes a real over-/under-flow look in-range.
#[must_use]
pub fn signed_min(width: u32) -> i128 {
    // `1 <= width <= 127`: `width - 1` in `0..=126`, shift in range.
    // `width == 128`: i128::MIN. `width == 0` or `width > 128`: saturate to MIN.
    if width == 128 {
        i128::MIN
    } else if width >= 1 && width <= 127 {
        -(1i128 << (width - 1))
    } else {
        // Out-of-contract (width == 0 or width > 128): previously panicked.
        i128::MIN
    }
}

/// Maximum value for a signed integer of the given bit width.
/// Mirrors `trust_vcgen::range::signed_max`.
///
/// # Trust contract (precondition)
///
/// The only meaningful signed bit-widths are `1 <= width && width <= 128`.
/// Under the staged Trust verifier this is the precondition to attach:
///
/// ```text
/// #[requires(1 <= width && width <= 128)]
/// ```
///
/// (Same rationale as [`signed_min`] for why this is a doc contract and not a
/// `#[requires(..)]` attribute on stable dev builds.) Under that precondition
/// the body is panic-free: `width >= 1` makes `width - 1` not underflow, and the
/// `else` branch only runs when `width != 128`, so `width <= 127` and the shift
/// amount `width - 1 <= 126 < 128` is in range.
///
/// Total without changing in-contract results: for `1 <= width <= 128` it
/// returns exactly `(1i128 << (width - 1)) - 1` (and `i128::MAX` at
/// `width == 128`), identical to the historical body. Out-of-domain widths
/// (`width == 0` or `width > 128`), which previously panicked, saturate to
/// `i128::MAX` — a defined, non-panicking value that is a sound
/// over-approximation (never makes a real overflow look in-range).
#[must_use]
pub fn signed_max(width: u32) -> i128 {
    if width == 128 {
        i128::MAX
    } else if width >= 1 && width <= 127 {
        (1i128 << (width - 1)) - 1
    } else {
        // Out-of-contract (width == 0 or width > 128): previously panicked.
        i128::MAX
    }
}

// ---------------------------------------------------------------------------
// The overflow VIOLATION formula (trust-types side).
// ---------------------------------------------------------------------------

/// The overflow **violation** (negation of `min <= result <= max`) for an
/// integer type of the given `width`/`signed`, over a result variable named
/// `result_var`:
///
/// ```text
/// result < min  OR  result > max
/// ```
///
/// CARDINAL: this is byte-identical in shape to the `out_of_range` formula
/// `trust-vcgen`'s overflow VC generator builds (`generate.rs`):
///
/// ```text
/// Formula::Or(vec![
///     Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
///     Formula::Gt(Box::new(result),         Box::new(max_f)),
/// ])
/// ```
///
/// with `min_f = type_min_formula(width, signed)` and
/// `max_f = type_max_formula(width, signed)`. Matching this shape is what lets
/// a kernel-checked `RustVIR.noOverflow` denotation correspond to the same
/// proof obligation the SMT path refutes — proving the *right* thing.
///
/// Only meaningful for the Add/Sub Int (QF_LIA) class; Mul / signed-div remain
/// BitVec and fail-closed (see crate docs). `result_var` is the same Int-sorted
/// result term name the generator threads through `operand_to_formula`.
#[must_use]
#[allow(non_snake_case)]
pub fn noOverflow_violation_formula(width: u32, signed: bool, result_var: &str) -> Formula {
    let result = Formula::Var(result_var.to_string(), Sort::Int);
    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);
    // EXACT shape of generate.rs's `out_of_range`.
    Formula::Or(vec![
        Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
        Formula::Gt(Box::new(result), Box::new(max_f)),
    ])
}

/// The overflow **safe-range** predicate `min <= result <= max` for an integer
/// type, over a result variable named `result_var`, as a [`trust_types::Formula`]:
///
/// ```text
/// min <= result  AND  result <= max
/// ```
///
/// This is the trust-types reflection of the kernel [`noOverflow_definition`]
/// body. It is the logical negation of [`noOverflow_violation_formula`] (the
/// VC asserts the violation and the solver refutes it; this is the property a
/// successful refutation establishes). Same fragment/scope caveats apply.
#[must_use]
#[allow(non_snake_case)]
pub fn noOverflow_safe_range_formula(width: u32, signed: bool, result_var: &str) -> Formula {
    let result = Formula::Var(result_var.to_string(), Sort::Int);
    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);
    Formula::And(vec![
        Formula::Le(Box::new(min_f), Box::new(result.clone())),
        Formula::Le(Box::new(result), Box::new(max_f)),
    ])
}

// ---------------------------------------------------------------------------
// The clean-kernel side: a REAL `RustVIR.noOverflow` Definition.
// ---------------------------------------------------------------------------

/// Fully-qualified kernel name of the overflow safety predicate.
pub const NO_OVERFLOW_NAME: &str = "RustVIR.noOverflow";

/// The `Int` kernel type. Matches `trust-certify`'s `int_ty`.
fn int_ty() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

/// `Prop` — the sort the predicate lands in.
fn prop_ty() -> Expr {
    Expr::prop()
}

/// `@LE.le Int instLEInt a b`. (`LE.le @Int instLEInt` δ-reduces to `Int.le`,
/// i.e. `min <= result`.) Matches `trust-certify`'s `le_int`, so the kernel
/// denotation here is the SAME order relation the certifier reconstructs.
fn le_int(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]), int_ty()),
                Expr::const_(Name::from_string("instLEInt"), vec![]),
            ),
            a,
        ),
        b,
    )
}

/// `And p q` — conjunction in `Prop`. Registered by [`Environment::init_and`].
fn and_prop(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
}

/// Register the `LE Int` instance (`instLEInt := @LE.mk Int Int.le`) so the
/// `le_int` props type-check. `Int.le` is provided by `init_int_ord_lemmas`.
/// Idempotent; fail-closed (returns `None` if any decl is rejected).
fn ensure_hle(env: &mut Environment) -> Option<()> {
    env.init_le().ok()?;
    if env.get_const(&Name::from_string("instLEInt")).is_some() {
        return Some(());
    }
    let int = int_ty();
    let inst_type =
        Expr::app(Expr::const_(Name::from_string("LE"), vec![Level::zero()]), int.clone());
    let inst_value = Expr::app(
        Expr::app(Expr::const_(Name::from_string("LE.mk"), vec![Level::zero()]), int.clone()),
        Expr::const_(Name::from_string("Int.le"), vec![]),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instLEInt"),
        level_params: vec![],
        type_: inst_type,
        value: inst_value,
        is_reducible: true,
    })
    .ok()?;
    Some(())
}

/// The type of the predicate: `Int -> Int -> Int -> Prop`.
fn no_overflow_type() -> Expr {
    Expr::arrow(int_ty(), Expr::arrow(int_ty(), Expr::arrow(int_ty(), prop_ty())))
}

/// The body: `fun (min result max : Int) => And (Int.le min result) (Int.le result max)`.
///
/// Built with de Bruijn indices: under the three lambdas, `min` = bvar(2),
/// `result` = bvar(1), `max` = bvar(0). The body is
/// `And (le min result) (le result max)` = `min <= result <= max`.
fn no_overflow_body() -> Expr {
    let min = Expr::bvar(2);
    let result = Expr::bvar(1);
    let max = Expr::bvar(0);
    let lower = le_int(min, result.clone()); // min <= result
    let upper = le_int(result, max); // result <= max
    let body = and_prop(lower, upper);
    // λ (min : Int). λ (result : Int). λ (max : Int). body
    Expr::lam(
        BinderInfo::Default,
        int_ty(),
        Expr::lam(
            BinderInfo::Default,
            int_ty(),
            Expr::lam(BinderInfo::Default, int_ty(), body),
        ),
    )
}

/// The [`clean_kernel::Declaration`] for `RustVIR.noOverflow` — a real
/// `Definition` (NOT a `const_str` placeholder, NOT an `Axiom`, NOT a
/// `Theorem`-wrapping-an-`Axiom` restatement): its body literally computes
/// `min <= result <= max`. The kernel re-checks the body against the declared
/// type when this is added to an environment (see [`overflow_safety_env`]).
#[must_use]
pub fn noOverflow_definition() -> Declaration {
    Declaration::Definition {
        name: Name::from_string(NO_OVERFLOW_NAME),
        level_params: vec![],
        type_: no_overflow_type(),
        value: no_overflow_body(),
        // Reducible so consumers can δ-unfold the predicate to its `And`-of-
        // bounds body during def-eq, exactly as they would the SMT formula.
        is_reducible: true,
    }
}

/// `RustVIR.noOverflow min result max`, the kernel proposition that
/// `min <= result <= max` for the three given Int terms. Consumers that have a
/// concrete `min`/`result`/`max` apply the predicate via this helper.
#[must_use]
#[allow(non_snake_case)]
pub fn noOverflow_app(min: Expr, result: Expr, max: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(NO_OVERFLOW_NAME), vec![]), [min, result, max])
}

/// Build a clean [`Environment`] with Int arithmetic + ordering lemmas, the
/// `LE Int` / `And` support, and the real `RustVIR.noOverflow` definition
/// installed and kernel-checked.
///
/// Mirrors `trust-certify::build_env` (Int order lemmas) but adds the overflow
/// predicate. Returns `None` (fail-closed) if any declaration — including the
/// `noOverflow` definition's kernel re-check — is rejected. A returned `Some`
/// is positive evidence the kernel ACCEPTED the `min <= result <= max`
/// denotation.
#[must_use]
pub fn overflow_safety_env() -> Option<Environment> {
    let mut env = Environment::new();
    env.init_int_ord_lemmas().ok()?;
    env.init_and().ok()?;
    ensure_hle(&mut env)?;
    env.add_decl(noOverflow_definition()).ok()?;
    Some(env)
}

// ---------------------------------------------------------------------------
// Additional RustVIR panic-freedom predicates (ported from the trust-wp spikes
// `trust-rustvir-defs` / `trust-ownership-defs`, verified kernel-valid on stable).
// Same structure as `noOverflow`: a real `Definition` whose body computes the
// safety condition, `is_reducible` so consumers δ-unfold it during def-eq.
// ---------------------------------------------------------------------------

/// Fully-qualified kernel name of the subtraction-underflow safety predicate.
pub const NO_NEG_OVERFLOW_SUB_NAME: &str = "RustVIR.noNegOverflowSub";

/// The body `fun (a b : Int) => Int.le b a`: `a - b` does not underflow when `b <= a`.
/// Under the two lambdas, `a` = bvar(1) and `b` = bvar(0).
fn no_neg_overflow_sub_body() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        int_ty(),
        Expr::lam(BinderInfo::Default, int_ty(), le_int(Expr::bvar(0), Expr::bvar(1))),
    )
}

/// The [`clean_kernel::Declaration`] for `RustVIR.noNegOverflowSub` — a real
/// `Definition` `Int -> Int -> Prop := fun a b => b <= a`.
#[must_use]
pub fn noNegOverflowSub_definition() -> Declaration {
    Declaration::Definition {
        name: Name::from_string(NO_NEG_OVERFLOW_SUB_NAME),
        level_params: vec![],
        type_: Expr::arrow(int_ty(), Expr::arrow(int_ty(), prop_ty())),
        value: no_neg_overflow_sub_body(),
        is_reducible: true,
    }
}

/// `RustVIR.noNegOverflowSub a b`, the kernel proposition that `b <= a`.
#[must_use]
#[allow(non_snake_case)]
pub fn noNegOverflowSub_app(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(NO_NEG_OVERFLOW_SUB_NAME), vec![]), [a, b])
}

/// A [`Environment`] with the overflow predicate AND the subtraction-underflow
/// predicate installed and kernel-checked — extends [`overflow_safety_env`].
/// `Some` is positive evidence the kernel accepted both denotations. Fail-closed.
#[must_use]
pub fn rustvir_safety_env() -> Option<Environment> {
    let mut env = overflow_safety_env()?;
    env.add_decl(noNegOverflowSub_definition()).ok()?;
    Some(env)
}

/// `@Int.lt a b` — the strict order (provided by `init_int_ord_lemmas`).
fn lt_int(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Int.lt"), vec![]), [a, b])
}
/// `Int.ofNat 0` — the integer zero.
fn int_zero() -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), Expr::nat_lit(0))
}
/// A binary `Int → Int → Prop` Definition with the given two-lambda body.
fn binary_int_pred(name: &str, body: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::arrow(int_ty(), Expr::arrow(int_ty(), prop_ty())),
        value: Expr::lam(BinderInfo::Default, int_ty(), Expr::lam(BinderInfo::Default, int_ty(), body)),
        is_reducible: true,
    }
}

/// `RustVIR.inBounds idx len := And (0 <= idx) (idx < len)`.
pub const IN_BOUNDS_NAME: &str = "RustVIR.inBounds";
/// `RustOwnership.borrowValid now end := now < end` (valid while now precedes lifetime end).
pub const BORROW_VALID_NAME: &str = "RustOwnership.borrowValid";
/// `RustLifetime.outlives ea eb := eb <= ea` (`'a` outlives `'b`).
pub const OUTLIVES_NAME: &str = "RustLifetime.outlives";
/// `RustOwnership.placeInitialized gen := 0 < gen` (initialized once written).
pub const PLACE_INITIALIZED_NAME: &str = "RustOwnership.placeInitialized";
/// `RustTypeInvariant.wellFormed v cap := v < cap` (within the type's capacity).
pub const WELL_FORMED_NAME: &str = "RustTypeInvariant.wellFormed";

/// The full RustVIR / ownership panic-freedom vocabulary as real `Definition`s, ported
/// from the trust-wp spikes (`trust-rustvir-defs` / `trust-ownership-defs`) and installed
/// on top of [`overflow_safety_env`]. `Some` iff the kernel accepts every body. Fail-closed.
#[must_use]
pub fn rustvir_full_env() -> Option<Environment> {
    let mut env = overflow_safety_env()?;
    // panic-freedom
    env.add_decl(noNegOverflowSub_definition()).ok()?;
    // inBounds idx len := And (0 <= idx) (idx < len)   (idx = bvar1, len = bvar0)
    env.add_decl(binary_int_pred(IN_BOUNDS_NAME, and_prop(le_int(int_zero(), Expr::bvar(1)), lt_int(Expr::bvar(1), Expr::bvar(0))))).ok()?;
    // ownership / type invariants
    env.add_decl(binary_int_pred(BORROW_VALID_NAME, lt_int(Expr::bvar(1), Expr::bvar(0)))).ok()?; // now < end
    env.add_decl(binary_int_pred(OUTLIVES_NAME, le_int(Expr::bvar(0), Expr::bvar(1)))).ok()?; // eb <= ea
    env.add_decl(binary_int_pred(WELL_FORMED_NAME, lt_int(Expr::bvar(1), Expr::bvar(0)))).ok()?; // v < cap
    // placeInitialized gen := 0 < gen   (unary)
    env.add_decl(Declaration::Definition {
        name: Name::from_string(PLACE_INITIALIZED_NAME),
        level_params: vec![],
        type_: Expr::arrow(int_ty(), prop_ty()),
        value: Expr::lam(BinderInfo::Default, int_ty(), lt_int(int_zero(), Expr::bvar(0))),
        is_reducible: true,
    })
    .ok()?;
    Some(env)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- (a) the RustVIR.noOverflow definition type-checks in the kernel ----

    #[test]
    fn test_no_overflow_definition_kernel_accepts() {
        // overflow_safety_env adds the Definition via env.add_decl, which runs
        // the kernel type-check of the body against `Int -> Int -> Int -> Prop`.
        // A Some means the clean kernel ACCEPTED the min<=result<=max denotation.
        let env = overflow_safety_env().expect("kernel must accept RustVIR.noOverflow definition");
        // The constant is present and is a real (non-opaque) declaration.
        assert!(
            env.get_const(&Name::from_string(NO_OVERFLOW_NAME)).is_some(),
            "RustVIR.noOverflow must be registered as a kernel constant"
        );
    }

    #[test]
    fn test_no_overflow_is_definition_not_axiom() {
        // Guard against regressing to an opaque placeholder: it must be a
        // Definition with a real body, never an Axiom or const_str.
        match noOverflow_definition() {
            Declaration::Definition { name, type_, value, .. } => {
                assert_eq!(name, Name::from_string(NO_OVERFLOW_NAME));
                assert_eq!(type_, no_overflow_type());
                assert_eq!(value, no_overflow_body());
            }
            other => panic!("expected Declaration::Definition, got {other:?}"),
        }
    }

    // ---- (b) the denotation matches the arithmetic fact for a witness ----

    /// For a concrete overflowing witness (i8, result = 200, max = 127), the
    /// violation formula must be SATISFIED (result > max) and the safe-range
    /// formula must EXCLUDE it (result <= max is false). This is the arithmetic
    /// fact the kernel `min <= result <= max` denotes, checked directly.
    #[test]
    fn test_i8_overflow_witness_violates_and_is_excluded() {
        let (width, signed) = (8u32, true);
        // i8: min = -128, max = 127.
        assert_eq!(type_min_formula(width, signed), Formula::Int(-128));
        assert_eq!(type_max_formula(width, signed), Formula::Int(127));

        let witness: i128 = 200; // out of i8 range — a real overflow.
        let min = signed_min(width);
        let max = signed_max(width);

        // Safe range `min <= witness <= max` is FALSE for the witness ...
        let in_range = min <= witness && witness <= max;
        assert!(!in_range, "200 must NOT be in i8 safe range");

        // ... and the violation `witness < min OR witness > max` is TRUE.
        let violates = witness < min || witness > max;
        assert!(violates, "200 must satisfy the i8 overflow violation");

        // The formulae we emit denote exactly these two facts (structurally).
        let viol = noOverflow_violation_formula(width, signed, "r");
        match &viol {
            Formula::Or(disj) => {
                assert_eq!(disj.len(), 2);
                // r < min : with r = 200, min = -128 -> false
                // r > max : with r = 200, max = 127 -> true  => Or is true.
                assert!(matches!(
                    &disj[0],
                    Formula::Lt(_, m) if matches!(m.as_ref(), Formula::Int(-128))
                ));
                assert!(matches!(
                    &disj[1],
                    Formula::Gt(_, m) if matches!(m.as_ref(), Formula::Int(127))
                ));
            }
            other => panic!("expected Or, got {other:?}"),
        }

        let safe = noOverflow_safe_range_formula(width, signed, "r");
        // safe is the boolean negation of viol; cross-check via the witness.
        assert!(eval_against_witness(&viol, witness));
        assert!(!eval_against_witness(&safe, witness));
    }

    /// An in-range witness (i8, result = 100): violation FALSE, safe-range TRUE.
    #[test]
    fn test_i8_in_range_witness_is_safe() {
        let (width, signed) = (8u32, true);
        let witness: i128 = 100;
        let viol = noOverflow_violation_formula(width, signed, "r");
        let safe = noOverflow_safe_range_formula(width, signed, "r");
        assert!(!eval_against_witness(&viol, witness), "100 must not violate i8 range");
        assert!(eval_against_witness(&safe, witness), "100 must be in i8 safe range");
    }

    /// Tiny evaluator: substitute the single Int variable with `value` and
    /// evaluate the (closed, ground) order formula to a bool. Supports exactly
    /// the connectives the two formulae use — this is the denotation check.
    fn eval_against_witness(f: &Formula, value: i128) -> bool {
        fn term(f: &Formula, value: i128) -> i128 {
            match f {
                Formula::Var(_, Sort::Int) => value,
                Formula::Int(n) => *n,
                Formula::UInt(n) => *n as i128,
                other => panic!("unexpected term in witness eval: {other:?}"),
            }
        }
        match f {
            Formula::Or(disj) => disj.iter().any(|d| eval_against_witness(d, value)),
            Formula::And(conj) => conj.iter().all(|c| eval_against_witness(c, value)),
            Formula::Lt(a, b) => term(a, value) < term(b, value),
            Formula::Le(a, b) => term(a, value) <= term(b, value),
            Formula::Gt(a, b) => term(a, value) > term(b, value),
            Formula::Ge(a, b) => term(a, value) >= term(b, value),
            other => panic!("unexpected connective in witness eval: {other:?}"),
        }
    }

    // ---- (c) the violation formula shape EQUALS range.rs's emitted shape ----

    /// Re-derivation of range.rs's `out_of_range` (the overflow VC failure
    /// body) from OUR copied bound helpers, asserting our public emitter
    /// produces the byte-identical `Formula`. This is an internal consistency
    /// check only: both sides are this crate's, so it cannot witness a change
    /// range.rs makes. The check that can is in trust-vcgen's `range.rs`.
    fn range_rs_out_of_range_shape(width: u32, signed: bool, var: &str) -> Formula {
        // Mirrors generate.rs::v2_build_overflow_vc_for_operands exactly:
        //   let result = Var(var, Int);
        //   let min_f = type_min_formula(...); let max_f = type_max_formula(...);
        //   Or([ Lt(result, min_f), Gt(result, max_f) ])
        let result = Formula::Var(var.to_string(), Sort::Int);
        let min_f = type_min_formula(width, signed);
        let max_f = type_max_formula(width, signed);
        Formula::Or(vec![
            Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
            Formula::Gt(Box::new(result), Box::new(max_f)),
        ])
    }

    #[test]
    fn test_violation_formula_matches_range_rs_shape() {
        for &(width, signed) in
            &[(8u32, true), (8, false), (16, true), (32, false), (64, true), (128, false)]
        {
            let ours = noOverflow_violation_formula(width, signed, "result");
            let expected = range_rs_out_of_range_shape(width, signed, "result");
            assert_eq!(
                ours, expected,
                "violation formula must be byte-identical to range.rs out_of_range for \
                 width={width} signed={signed}"
            );
        }
    }

    /// Pin our copied bound helpers to the values range.rs's own tests pin
    /// (u8=255, i8=127, u128=UInt::MAX, i128=MAX, ...). A duplicated table of
    /// constants, so it catches a careless edit here but not a redefinition
    /// there.
    #[test]
    fn test_bounds_match_range_rs_values() {
        assert_eq!(type_max_formula(8, false), Formula::Int(255));
        assert_eq!(type_max_formula(8, true), Formula::Int(127));
        assert_eq!(type_max_formula(128, false), Formula::UInt(u128::MAX));
        assert_eq!(type_max_formula(128, true), Formula::Int(i128::MAX));
        assert_eq!(type_min_formula(32, false), Formula::Int(0));
        assert_eq!(type_min_formula(32, true), Formula::Int(-(1i128 << 31)));
        assert_eq!(type_min_formula(128, true), Formula::Int(i128::MIN));
        assert_eq!(signed_min(8), -128);
        assert_eq!(signed_max(8), 127);
        assert_eq!(signed_min(128), i128::MIN);
        assert_eq!(signed_max(128), i128::MAX);
    }

    // ---- (d) panic-free hardening guardrail ----

    /// ADVERSARIAL: the historical bodies panicked on out-of-domain widths —
    /// `Overflow(Sub)` at `width == 0` (`width - 1` underflows) and
    /// `Overflow(Shl)` for `width >= 129` (`1i128 << (width-1)` shifts by
    /// `>= 128`). This asserts the hardened bodies are TOTAL: they return a
    /// defined value (never panic) at exactly those boundary widths. If anyone
    /// reverts to the panicking arithmetic this test crashes.
    #[test]
    fn test_signed_bounds_are_total_no_panic_out_of_domain() {
        // width == 0: previously `Overflow(Sub)`.
        let _ = signed_min(0);
        let _ = signed_max(0);
        // width == 129: previously `Overflow(Shl)` (shift by 128).
        let _ = signed_min(129);
        let _ = signed_max(129);
        // Extreme width: shift amount astronomically out of range.
        let _ = signed_min(u32::MAX);
        let _ = signed_max(u32::MAX);

        // Out-of-domain results saturate to the type extremes (defined, sound).
        assert_eq!(signed_min(0), i128::MIN);
        assert_eq!(signed_max(0), i128::MAX);
        assert_eq!(signed_min(129), i128::MIN);
        assert_eq!(signed_max(129), i128::MAX);

        // CARDINAL: in-contract widths are BYTE-IDENTICAL to the historical
        // `-(1<<(w-1))` / `(1<<(w-1))-1` formula — no semantic drift for any
        // meaningful width. (range.rs's mirror must match these same values.)
        for w in 1u32..=127 {
            assert_eq!(signed_min(w), -(1i128 << (w - 1)), "signed_min drift at width {w}");
            assert_eq!(signed_max(w), (1i128 << (w - 1)) - 1, "signed_max drift at width {w}");
        }
        assert_eq!(signed_min(128), i128::MIN);
        assert_eq!(signed_max(128), i128::MAX);

        // type_max_formula: previously `Overflow(Sub)` at width 127 (`(1<<127)-1`
        // underflows) and `Overflow(Shl)` at width >= 129. Now TOTAL; in-domain
        // unsigned widths (8/16/32/64/128) are byte-identical to the historical body.
        let _ = type_max_formula(127, false);
        let _ = type_max_formula(129, false);
        let _ = type_max_formula(u32::MAX, false);
        assert_eq!(type_max_formula(127, false), Formula::Int(i128::MAX));
        assert_eq!(type_max_formula(129, false), Formula::Int(i128::MAX));
        assert_eq!(type_max_formula(8, false), Formula::Int(255));
        assert_eq!(type_max_formula(64, false), Formula::Int((1i128 << 64) - 1));
        assert_eq!(type_max_formula(128, false), Formula::UInt(u128::MAX));
    }
}
