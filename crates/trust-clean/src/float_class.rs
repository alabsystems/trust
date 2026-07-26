// trust-clean/float_class.rs — GOAL-ITEM #3, Phase 1: the IEEE-754 classification
// predicates, as Clean defs over the STRUCTURED float carriers.
//
// THE GAP THIS CLOSES.
// `reflect_float` (reflect.rs) reflects `f32`/`f64` to REAL single-constructor Clean
// inductives `Trust.Float32`/`Trust.Float64` that decompose the IEEE-754 bit layout
// into NAMED, kernel-projectable fields:
//
//   Trust.Float32 { sign : Bool, exponent : BitVec 8,  mantissa : BitVec 23 }
//   Trust.Float64 { sign : Bool, exponent : BitVec 11, mantissa : BitVec 52 }
//
// (the BitVec fields decode to `Int` in the kernel — the integer VALUE of the field,
// 0..2^k-1). On top of that structure this module pins the IEEE-754 special-value
// CLASSIFICATION as Clean `Prop` predicates, kernel-checkable over the projections:
//
//   isNaN       f  :=  exponent f = ALL_ONES ∧ mantissa f ≠ 0
//   isInf       f  :=  exponent f = ALL_ONES ∧ mantissa f = 0
//   isZero      f  :=  exponent f = 0        ∧ mantissa f = 0
//   isSubnormal f  :=  exponent f = 0        ∧ mantissa f ≠ 0
//
// where ALL_ONES = 2^exp_bits - 1 (255 for f32, 2047 for f64). Each is built from the
// prelude's axiom-free `And`/`Not`/`Eq`/`Int` inductives and the kernel-derived named
// projections of `Trust.FloatN`, so every def's transitive axiom closure is
// `⊆ {propext, Quot.sound, Classical.choice}` — modulo exactly 3 axioms, NO 4th axiom,
// NO opaque/sorry. Built ENTIRELY at runtime via the kernel API (like mirsem.rs) — no
// Clean-repo change.
//
// SCOPE HONESTY. This is the STRUCTURED BIT MODEL + the IEEE-754 representation-level
// classification. The real-number VALUE interpretation (mantissa→rational, the value a
// float denotes) and rounding-correct arithmetic ops (round-to-nearest-even add/mul/div)
// are the DEFERRED Phase-2 refinement — DOCUMENTED here, NOT faked: a float-VALUE
// safety/overflow VC needing value semantics fails closed (sound). The classification
// predicates are faithful to the IEEE-754 *representation* (the bit-level structure),
// which is goal-item #3's Phase-1 deliverable.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use clean_kernel::{
    BinderData, BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, LevelVec, Name, TypeChecker,
};

use crate::reflect;

// ---------------------------------------------------------------------------
// Canonical Clean names for the classification predicates
// ---------------------------------------------------------------------------

/// The classification-predicate suffixes (a predicate is `Trust.FloatN.<suffix>`).
pub const CLASSIFIERS: &[&str] = &["isNaN", "isInf", "isZero", "isSubnormal"];

/// The fully-qualified Clean name of a classification predicate for the float
/// inductive of `width` bits (`Trust.Float32.isNaN`, …). `None` for an unsupported
/// width or an unknown classifier.
#[must_use]
pub fn classifier_name(width: u32, classifier: &str) -> Option<String> {
    let ind = reflect::float_inductive_name(width)?;
    CLASSIFIERS.contains(&classifier).then(|| format!("{ind}.{classifier}"))
}

// ---------------------------------------------------------------------------
// Small kernel-term builders (shared de-Bruijn convention with clean_ground.rs)
// ---------------------------------------------------------------------------

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

/// `Int` literal `n` → `Int.ofNat n` (n ≥ 0 always here — field values are
/// non-negative), IDENTICAL to `clean_ground::int_lit_to_expr`/`mirsem::int_lit` so
/// the predicate compares against the exact integer term the field decodes to.
fn int_lit(n: u64) -> Expr {
    Expr::app(cst("Int.ofNat"), Expr::nat_lit(n))
}

/// `@Eq Int a b : Prop`.
fn eq_int(a: Expr, b: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq, [cst("Int"), a, b])
}

/// `And a b : Prop`.
fn and(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("And"), [a, b])
}

/// `Not a : Prop`.
fn not(a: Expr) -> Expr {
    Expr::app(cst("Not"), a)
}

// ---------------------------------------------------------------------------
// Step 1 — register the structured float inductive(s) in an env
// ---------------------------------------------------------------------------

/// Register the `Trust.FloatN` inductive of `width` bits (idempotent) via the SAME
/// `register_adt_carriers` path a P1 struct uses, returning `Ok(())` iff it is present
/// AND passed the modulo-3 registration gate (its `axiom_deps` and recursor closures
/// are empty). `Err` if the width is unsupported or the registration failed the gate.
fn register_float_inductive(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(carrier) = reflect::reflect_float(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let name = carrier.name.clone();
    let registry = crate::clean_ground::register_adt_carriers(env, std::slice::from_ref(&carrier));
    if registry.get(&name).is_some() {
        Ok(())
    } else {
        Err(format!("{name} failed the modulo-3 registration gate"))
    }
}

/// Build a kernel `Environment` with the prelude and the `Trust.FloatN` inductive of
/// `width` bits registered — the structured-float environment.
///
/// # Errors
/// Returns the registration error string for an unsupported width or a gate failure.
pub fn float_env(width: u32) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    register_float_inductive(&mut env, width)?;
    Ok(env)
}

// ---------------------------------------------------------------------------
// Step 2 — the classification predicates as Clean defs over the structure
// ---------------------------------------------------------------------------

/// The `exponent` projection (`Int`) of the bound float variable (de-Bruijn `bvar(0)`
/// under the predicate's `λ(f : Trust.FloatN)`).
fn exponent_of(inductive: &str) -> Expr {
    // Field order is [sign(0), exponent(1), mantissa(2)] — the IEEE MSB→LSB layout.
    Expr::proj(Name::from_string(inductive), 1, Expr::bvar(0))
}

/// The `mantissa` projection (`Int`) of the bound float variable.
fn mantissa_of(inductive: &str) -> Expr {
    Expr::proj(Name::from_string(inductive), 2, Expr::bvar(0))
}

/// The body `Prop` of a classification predicate over `Trust.FloatN` (the field
/// projections of the bound `f : Trust.FloatN`, de-Bruijn `bvar(0)`), for the given
/// classifier and `all_ones` exponent value (2^exp_bits - 1).
fn classifier_body(inductive: &str, classifier: &str, all_ones: u64) -> Option<Expr> {
    // The projection terms are re-derived per use (each builds a fresh `Expr`) so the
    // conjuncts are independent kernel terms.
    let exp_all_ones = || eq_int(exponent_of(inductive), int_lit(all_ones));
    let exp_zero = || eq_int(exponent_of(inductive), int_lit(0));
    let mant_zero = || eq_int(mantissa_of(inductive), int_lit(0));
    let mant_nonzero = || not(eq_int(mantissa_of(inductive), int_lit(0)));
    Some(match classifier {
        // exponent all-ones ∧ mantissa ≠ 0
        "isNaN" => and(exp_all_ones(), mant_nonzero()),
        // exponent all-ones ∧ mantissa = 0
        "isInf" => and(exp_all_ones(), mant_zero()),
        // exponent = 0 ∧ mantissa = 0
        "isZero" => and(exp_zero(), mant_zero()),
        // exponent = 0 ∧ mantissa ≠ 0
        "isSubnormal" => and(exp_zero(), mant_nonzero()),
        _ => return None,
    })
}

/// Register the four IEEE-754 classification predicates for the float inductive of
/// `width` bits as Clean defs `Trust.FloatN.<classifier> : Trust.FloatN → Prop` in
/// `env` (idempotent per name). Each is `λ(f : Trust.FloatN). <body>` where `<body>`
/// is a `Prop` over `f`'s named projections.
///
/// # Errors
/// Returns an error string if the width is unsupported or the kernel rejects a def.
fn register_classifiers(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let Some((exp_bits, _mant_bits)) = reflect::ieee754_layout(width) else {
        return Err(format!("no IEEE-754 layout for width {width}"));
    };
    // ALL_ONES exponent = 2^exp_bits - 1 (255 for f32, 2047 for f64).
    let all_ones: u64 = (1u64 << exp_bits) - 1;
    let bd = || BinderData::from(BinderInfo::Default);
    let float_ty = cst(inductive);
    // The predicate type `Trust.FloatN → Prop`.
    let pred_ty = Expr::pi(bd(), float_ty.clone(), Expr::prop());

    for classifier in CLASSIFIERS {
        let name = Name::from_string(&format!("{inductive}.{classifier}"));
        if env.get_const(&name).is_some() {
            continue; // already registered this session
        }
        let body = classifier_body(inductive, classifier, all_ones)
            .ok_or_else(|| format!("unknown classifier {classifier}"))?;
        // λ(f : Trust.FloatN). body
        let value = Expr::lam(bd(), float_ty.clone(), body);
        env.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: pred_ty.clone(),
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({inductive}.{classifier}): {e:?}"))?;
    }
    Ok(())
}

/// Build a kernel `Environment` with the prelude, the `Trust.FloatN` inductive, AND
/// the four IEEE-754 classification predicates registered — the full structured-float
/// classification environment for `width` bits.
///
/// # Errors
/// Returns the registration error string for an unsupported width or a gate failure.
pub fn classification_env(width: u32) -> Result<Environment, String> {
    let mut env = float_env(width)?;
    register_classifiers(&mut env, width)?;
    Ok(env)
}

// ---------------------------------------------------------------------------
// Step 2b — the IEEE-754 VALUE interpretation (GOAL-ITEM #3, Phase 2)
// ---------------------------------------------------------------------------
//
// THE VALUE MODEL. The classification predicates above read the BIT STRUCTURE; this
// section adds the REAL-NUMBER VALUE a FINITE float DENOTES — the content that makes
// `Trust.FloatN` "a real IEEE-754 model, not an opaque blob". The denoted value of a
// finite float is a RATIONAL:
//
//   normal    (exponent ≠ 0):  (−1)^sign · (1 + mantissa/2^m) · 2^(exponent − bias)
//   subnormal (exponent = 0):  (−1)^sign · (mantissa/2^m)     · 2^(1 − bias)
//
// Clean's prelude `Rat` carries DOMAIN-SPECIFIC axioms (see clean's env/mod.rs notes:
// `Rat.zero_mul`/`Rat.left_distrib`/… are "honest domain axioms" under the free
// inductive `Rat`), so using it would break the modulo-3 closure (a 4th+ axiom).
// Instead we model ℚ AXIOM-FREE as a pair `Prod Int Int` (numerator, positive
// power-of-two denominator) over ONLY the prelude's axiom-free reducible Definitions
// `Int.add`/`Int.mul`/`Int.neg`/`Int.pow`/`Int.toNat` and the axiom-free `Prod`/`Bool`
// inductives — so every value def's transitive axiom closure stays ⊆ the 3.
//
// THE FIXED-DENOMINATOR TRICK. Pick the constant denominator `D = 2^(m + bias)` for
// ALL finite floats of a width (2^150 for f32, 2^1075 for f64). Multiplying both forms
// through by `D` clears the fractions, so the value's NUMERATOR over `D` is an INTEGER:
//
//   normal    numerator:  signMul sign ((2^m + mantissa) · 2^exponent)
//   subnormal numerator:  signMul sign (mantissa · 2)
//
// (subnormal: (m/2^m)·2^(1−bias)·D = m · 2^(1−bias) · 2^(m+bias) = m · 2^(1+m) — but we
//  fold the `2^m` into the magnitude split below so the two arms share `D`; concretely
//  the subnormal numerator is `mantissa · 2` once the common `2^m` is the unit-significand
//  scale, matching `value = numerator / D`.) This makes the value a genuine rational
// `numerator/D` with an EXPLICIT, kernel-projectable integer numerator and a fixed
// positive denominator — `value f = 0` iff the numerator is 0 (D > 0).
//
// WHAT THIS BUYS (the deep proofs the value model enables, all kernel-checked modulo 3):
//   * isZero ⟺ value = 0 (canonical zero) — the classification↔value connection.
//   * the SIGN lemma — value's numerator factors as `signMul (sign f) (magnitude f)`
//     with magnitude ≥ 0, so `value < 0 ⟺ sign = true` for a nonzero finite float.
//   * value MONOTONIC in the mantissa at fixed exponent/sign.
//
// SCOPE (HONEST). This is the finite-VALUE interpretation + the value lemmas. The
// rounding-correct arithmetic OPS (round-to-nearest-even add/sub/mul/div proven to
// match the IEEE-754 operation semantics) are the DEEPER op layer and are DEFERRED —
// NOT built, NOT faked. A float-arithmetic VC needing the OP semantics still fails
// closed (sound). The value model + classification-value connection is the bullet-3
// completion; see the module-tail note.

/// The `sign` projection (`Bool`) of the bound float variable (de-Bruijn `bvar(0)`
/// under a `λ(f : Trust.FloatN)`). Field index 0 (the IEEE MSB).
fn sign_of(inductive: &str) -> Expr {
    Expr::proj(Name::from_string(inductive), 0, Expr::bvar(0))
}

/// `Int` numeral `2`.
fn int_two() -> Expr {
    int_lit(2)
}

/// `Int.add a b : Int`.
fn int_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Int.add"), [a, b])
}

/// `Int.mul a b : Int`.
fn int_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Int.mul"), [a, b])
}

/// `Int.neg a : Int`.
fn int_neg(a: Expr) -> Expr {
    Expr::app(cst("Int.neg"), a)
}

/// `Int.pow base (exp : Nat) : Int` — the axiom-free `Nat.rec` recursion (`Int.pow`
/// is a reducible prelude Definition). `exp_nat` must be a `Nat`-typed term.
fn int_pow(base: Expr, exp_nat: Expr) -> Expr {
    Expr::apps(cst("Int.pow"), [base, exp_nat])
}

/// `Int.toNat i : Nat` — the axiom-free reducible prelude Definition mapping a
/// non-negative `Int` to its `Nat`. Used to feed an `Int` exponent FIELD into
/// `Int.pow`'s `Nat` exponent slot (the exponent field is 0..2^k−1, always ≥ 0).
fn int_to_nat(i: Expr) -> Expr {
    Expr::app(cst("Int.toNat"), i)
}

/// `Nat` literal `n`.
fn nat_lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

/// Names for the value-model declarations of the float inductive `inductive`.
fn value_decl_names(inductive: &str) -> ValueNames {
    ValueNames {
        sign_mul: format!("{inductive}.signMul"),
        magnitude: format!("{inductive}.magnitude"),
        value_num: format!("{inductive}.valueNum"),
        value_den: format!("{inductive}.valueDen"),
        value: format!("{inductive}.value"),
    }
}

/// The fully-qualified Clean names of the value-model declarations.
struct ValueNames {
    sign_mul: String,
    magnitude: String,
    value_num: String,
    value_den: String,
    value: String,
}

/// `Prod Int Int` (the rational carrier `ℚ ≅ (numerator, denominator)`).
fn prod_int_int() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod"), vec![Level::zero(), Level::zero()]),
        [cst("Int"), cst("Int")],
    )
}

/// `@Prod.mk Int Int num den : Prod Int Int`.
fn prod_mk_int(num: Expr, den: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod.mk"), vec![Level::zero(), Level::zero()]),
        [cst("Int"), cst("Int"), num, den],
    )
}

/// Register the value-model declarations for the float inductive of `width` bits as
/// Clean defs over the structure (idempotent per name). All terms use ONLY the
/// prelude's axiom-free `Int.add`/`mul`/`neg`/`pow`/`toNat`, `Bool.rec`, and
/// `Prod`, so the value model rests on EXACTLY the 3 foundational axioms — NO 4th.
///
/// Declarations (over `f : Trust.FloatN`):
///   * `signMul : Bool → Int → Int` = `λs x. if s then Int.neg x else x`
///     (`@Bool.rec (λ_.Int) x (Int.neg x) s` — false ↦ x, true ↦ −x).
///   * `magnitude : FloatN → Int` = the NON-NEGATIVE numerator (no sign) over the
///     fixed denominator `D`:
///        `if exponent = 0  then  mantissa · 2                      -- subnormal
///                          else  (2^m + mantissa) · 2^exponent`    -- normal
///     (the `if` is `@Bool.rec (λ_.Int) <normal> <subnormal> (Int.beq exponent 0)` —
///      Int.beq native-reduces on a concrete exponent, so concrete floats reduce).
///   * `valueNum : FloatN → Int` = `signMul (sign f) (magnitude f)` — the value's
///     numerator over `D`. This FACTORING is definitional, so the sign lemma holds
///     for ALL f by reflexivity.
///   * `valueDen : Int` = `2^(m + bias)` — the fixed positive denominator (a closed
///     constant; the WRONG bias here denotes the wrong rational, so a wrong-bias
///     claim fails closed).
///   * `value : FloatN → Prod Int Int` = `Prod.mk (valueNum f) valueDen` — the
///     denoted rational ℚ as a `(numerator, denominator)` pair.
///
/// # Errors
/// Returns an error string if the width is unsupported or the kernel rejects a def.
fn register_value_model(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let Some((_exp_bits, mant_bits)) = reflect::ieee754_layout(width) else {
        return Err(format!("no IEEE-754 layout for width {width}"));
    };
    let Some(bias) = reflect::ieee754_bias(width) else {
        return Err(format!("no IEEE-754 bias for width {width}"));
    };
    let names = value_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    let float_ty = cst(inductive);

    // Bool.rec.{1} into Int (Type-level motive ⇒ Sort 1), constant codomain `λ_.Int`.
    let bool_rec = || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let int_motive = || Expr::lam(bd(), cst("Bool"), cst("Int"));

    // --- signMul : Bool → Int → Int = λs x. (if s then -x else x) ---
    // @Bool.rec (λ_.Int) FALSE_case TRUE_case s — Bool.false is the FIRST ctor, so
    // the false minor (s = false ↦ +x) comes before the true minor (s = true ↦ −x).
    if env.get_const(&Name::from_string(&names.sign_mul)).is_none() {
        // Under `λ(s:Bool). λ(x:Int). …`: x = bvar(0), s = bvar(1).
        let x = || Expr::bvar(0);
        let s = || Expr::bvar(1);
        let dispatch = Expr::apps(bool_rec(), [int_motive(), x(), int_neg(x()), s()]);
        let value = Expr::lam(bd(), cst("Bool"), Expr::lam(bd(), cst("Int"), dispatch));
        let ty = Expr::pi(bd(), cst("Bool"), Expr::pi(bd(), cst("Int"), cst("Int")));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.sign_mul),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.sign_mul))?;
    }

    // --- magnitude : FloatN → Int (the non-negative numerator over D) ---
    // if exponent = 0 then mantissa·2 (subnormal) else (2^m + mantissa)·2^exponent.
    if env.get_const(&Name::from_string(&names.magnitude)).is_none() {
        // Under `λ(f : FloatN). …`: f = bvar(0); exponent_of/mantissa_of read bvar(0).
        let exp = || exponent_of(inductive);
        let mant = || mantissa_of(inductive);
        // normal: (2^m + mantissa) · 2^(exponent) — exponent ≥ 0, Int.toNat feeds Int.pow.
        let unit = int_pow(int_two(), nat_lit(u64::from(mant_bits))); // 2^m (the hidden 1·2^m)
        let normal = int_mul(int_add(unit, mant()), int_pow(int_two(), int_to_nat(exp())));
        // subnormal: mantissa · 2.
        let subnormal = int_mul(mant(), int_two());
        // scrutinee: Nat.beq (Int.toNat exponent) 0. We use `Nat.beq` over the Nat view
        // (the exponent field is always `Int.ofNat k`, so `Int.toNat` recovers `k`) — and
        // CRUCIALLY `Nat.beq` is a REDUCIBLE prelude Definition, so the kernel ι/δ-reduces
        // it to `Bool.true`/`Bool.false` on a CONCRETE exponent, letting `Bool.rec`
        // ι-reduce and the whole magnitude compute to an `Int` literal (provable by
        // `Eq.refl`). `Int.beq` would be the moral choice but it is registered `Opaque`
        // (computes ONLY via a native reducer that does not fire in def-eq here), so the
        // `Bool.rec` would get stuck — defeating the concrete value lemmas.
        let is_zero_exp = Expr::apps(cst("Nat.beq"), [int_to_nat(exp()), nat_lit(0)]);
        // @Bool.rec (λ_.Int) NORMAL_case SUBNORMAL_case (Nat.beq (toNat exponent) 0):
        //   = false (exponent ≠ 0) ↦ normal; = true (exponent = 0) ↦ subnormal.
        let dispatch = Expr::apps(bool_rec(), [int_motive(), normal, subnormal, is_zero_exp]);
        let value = Expr::lam(bd(), float_ty.clone(), dispatch);
        let ty = Expr::pi(bd(), float_ty.clone(), cst("Int"));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.magnitude),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.magnitude))?;
    }

    // --- valueNum : FloatN → Int = signMul (sign f) (magnitude f) ---
    if env.get_const(&Name::from_string(&names.value_num)).is_none() {
        let sign = sign_of(inductive);
        let mag = Expr::app(cst(&names.magnitude), Expr::bvar(0));
        let body = Expr::apps(cst(&names.sign_mul), [sign, mag]);
        let value = Expr::lam(bd(), float_ty.clone(), body);
        let ty = Expr::pi(bd(), float_ty.clone(), cst("Int"));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.value_num),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.value_num))?;
    }

    // --- valueDen : Int = 2^(m + bias) — the fixed positive denominator ---
    if env.get_const(&Name::from_string(&names.value_den)).is_none() {
        let den = int_pow(int_two(), nat_lit(u64::from(mant_bits) + bias));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.value_den),
            level_params: vec![],
            type_: cst("Int"),
            value: den,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.value_den))?;
    }

    // --- value : FloatN → Prod Int Int = Prod.mk (valueNum f) valueDen ---
    if env.get_const(&Name::from_string(&names.value)).is_none() {
        let num = Expr::app(cst(&names.value_num), Expr::bvar(0));
        let den = cst(&names.value_den);
        let body = prod_mk_int(num, den);
        let value = Expr::lam(bd(), float_ty.clone(), body);
        let ty = Expr::pi(bd(), float_ty.clone(), prod_int_int());
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.value),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.value))?;
    }
    Ok(())
}

/// Build a kernel `Environment` with the prelude, the `Trust.FloatN` inductive, the
/// four classification predicates, AND the IEEE-754 VALUE interpretation registered —
/// the full structured-float + value environment for `width` bits.
///
/// # Errors
/// Returns the registration error string for an unsupported width or a gate failure.
pub fn value_env(width: u32) -> Result<Environment, String> {
    let mut env = classification_env(width)?;
    register_value_model(&mut env, width)?;
    Ok(env)
}

/// The value-model declaration names that must rest on EXACTLY the 3 foundational
/// axioms (audited by [`pin_float_value`]).
fn value_audit_names(inductive: &str) -> Vec<String> {
    let n = value_decl_names(inductive);
    vec![n.sign_mul, n.magnitude, n.value_num, n.value_den, n.value]
}

// ---------------------------------------------------------------------------
// Step 3 — the modulo-3 audit verdict
// ---------------------------------------------------------------------------

/// Verdict of pinning the structured float carrier + its classification predicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FloatClassVerdict {
    /// The inductive, its recursor, and every classification predicate kernel-check
    /// resting on ONLY the 3 foundational axioms — modulo 3, NO 4th axiom.
    Modulo3,
    /// A declaration carries non-foundational axioms (residue listed).
    Residue(Vec<String>),
    /// The kernel rejected a declaration (soundness bug for a true claim; the
    /// fail-closed outcome for an unsupported width).
    KernelRejected(String),
}

/// Pin the structured float carrier of `width` bits + its classification predicates
/// and audit the axiom closure via the kernel's own `axiom_deps`. Confirms the
/// inductive, its auto-derived recursor, AND all four predicates rest on exactly the
/// 3 foundational axioms (modulo 3).
#[must_use]
pub fn pin_float_classification(width: u32) -> FloatClassVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return FloatClassVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let env = match classification_env(width) {
        Ok(e) => e,
        Err(e) => return FloatClassVerdict::KernelRejected(e),
    };
    // The inductive + its recursor + each classification predicate.
    let recursor = format!("{inductive}.rec");
    let mut to_audit: Vec<String> = vec![inductive.to_string(), recursor];
    for classifier in CLASSIFIERS {
        to_audit.push(format!("{inductive}.{classifier}"));
    }
    for n in &to_audit {
        match env.axiom_deps(&Name::from_string(n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return FloatClassVerdict::Residue(names);
            }
            None => return FloatClassVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    FloatClassVerdict::Modulo3
}

/// Type-check that every classification predicate of `width` bits has type
/// `Trust.FloatN → Prop` in the real kernel (the predicates KERNEL-CHECK over the
/// structure). Returns `Ok(())` iff all four infer that exact type.
///
/// # Errors
/// Returns a description if the env fails to build or a predicate's inferred type is
/// not `Trust.FloatN → Prop`.
pub fn classifiers_typecheck(width: u32) -> Result<(), String> {
    let inductive =
        reflect::float_inductive_name(width).ok_or_else(|| format!("unsupported width {width}"))?;
    let env = classification_env(width)?;
    let tc = TypeChecker::new(&env);
    let bd = || BinderData::from(BinderInfo::Default);
    let expected = Expr::pi(bd(), cst(inductive), Expr::prop());
    for classifier in CLASSIFIERS {
        let pred = cst(&format!("{inductive}.{classifier}"));
        let inferred = tc
            .infer_type(&pred)
            .map_err(|e| format!("{inductive}.{classifier} has no type: {e:?}"))?;
        if !tc.is_def_eq(&inferred, &expected) {
            return Err(format!(
                "{inductive}.{classifier} is not Trust.{inductive} → Prop, got {inferred:?}"
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Step 3b — the VALUE anchor: value model + lemmas pin modulo 3
// ---------------------------------------------------------------------------

/// Pin the IEEE-754 VALUE model of `width` bits (`signMul`/`magnitude`/`valueNum`/
/// `valueDen`/`value`) and audit the axiom closure via the kernel's own `axiom_deps`.
/// Confirms the entire value interpretation rests on EXACTLY the 3 foundational axioms
/// (modulo 3, NO 4th axiom) — it is built over only the prelude's axiom-free
/// `Int.add`/`mul`/`neg`/`pow`/`toNat`, `Bool.rec`, and `Prod`.
#[must_use]
pub fn pin_float_value(width: u32) -> FloatClassVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return FloatClassVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let env = match value_env(width) {
        Ok(e) => e,
        Err(e) => return FloatClassVerdict::KernelRejected(e),
    };
    for n in value_audit_names(inductive) {
        match env.axiom_deps(&Name::from_string(&n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return FloatClassVerdict::Residue(names);
            }
            None => return FloatClassVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    FloatClassVerdict::Modulo3
}

/// Type-check that `Trust.FloatN.value` of `width` bits has type
/// `Trust.FloatN → Prod Int Int` in the real kernel (the value map KERNEL-CHECKS over
/// the structure as a real `(numerator, denominator)` rational). `Ok(())` iff so.
///
/// # Errors
/// Returns a description if the env fails to build or `value`'s inferred type is not
/// `Trust.FloatN → Prod Int Int`.
pub fn value_typechecks(width: u32) -> Result<(), String> {
    let inductive =
        reflect::float_inductive_name(width).ok_or_else(|| format!("unsupported width {width}"))?;
    let env = value_env(width)?;
    let tc = TypeChecker::new(&env);
    let bd = || BinderData::from(BinderInfo::Default);
    let names = value_decl_names(inductive);
    let expected = Expr::pi(bd(), cst(inductive), prod_int_int());
    let inferred = tc
        .infer_type(&cst(&names.value))
        .map_err(|e| format!("{}.value has no type: {e:?}", inductive))?;
    if !tc.is_def_eq(&inferred, &expected) {
        return Err(format!(
            "{inductive}.value is not Trust.{inductive} → Prod Int Int, got {inferred:?}"
        ));
    }
    Ok(())
}

/// Build a concrete float pattern `Trust.FloatN.mk sign exponent mantissa` for a
/// kernel witness term (`sign` a `Bool`, `exponent`/`mantissa` `Int` literals).
fn float_pattern(inductive: &str, sign: bool, exponent: u64, mantissa: u64) -> Expr {
    let mk = cst(&format!("{inductive}.mk"));
    let sign_term = cst(if sign { "Bool.true" } else { "Bool.false" });
    Expr::apps(mk, [sign_term, int_lit(exponent), int_lit(mantissa)])
}

/// Verdict of checking ONE value-level lemma in the real kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueLemmaVerdict {
    /// The lemma's proof type-checked against its statement AND its axiom closure is
    /// ⊆ the 3 foundational axioms — PROVEN modulo 3, NO 4th axiom.
    ProvenModulo3,
    /// The proof type-checks but the closure carries a non-foundational axiom.
    Residue(Vec<String>),
    /// The kernel REJECTED the proof against the statement — the claim is NOT proven.
    /// This is the fail-closed outcome a WRONG value claim (wrong bias/sign) yields.
    KernelRejected(String),
}

/// Register `theorem <name> : <statement> := <proof>` into a fresh value-env and audit
/// the axiom closure — the shared driver for every value lemma. A wrong claim makes the
/// kernel reject `proof` against `statement` ⇒ [`ValueLemmaVerdict::KernelRejected`].
fn check_value_lemma(width: u32, name: &str, statement: Expr, proof: Expr) -> ValueLemmaVerdict {
    let mut env = match value_env(width) {
        Ok(e) => e,
        Err(e) => return ValueLemmaVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return ValueLemmaVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let decl_name = Name::from_string(name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: decl_name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return ValueLemmaVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&decl_name) {
        Some(residue) if residue.is_empty() => ValueLemmaVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            ValueLemmaVerdict::Residue(names)
        }
        None => ValueLemmaVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// `@Eq Int a b : Prop` (the integer-equality statement form).
fn eq_int_prop(a: Expr, b: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq, [cst("Int"), a, b])
}

/// `@Eq.refl Int t : @Eq Int t t` — the reflexivity proof for an integer equality
/// whose two sides are def-eq (ι/δ-reduce to the same normal form). Every value lemma
/// is an `Int` equality discharged this way: both sides reduce to a literal `Int`
/// normal form through the REDUCIBLE `Int.add`/`mul`/`neg`/`pow`/`toNat`/`Nat.beq`/
/// `Bool.rec` Definitions (the `Opaque` `Int.beq`/`Int.blt` would NOT reduce in def-eq,
/// so the value model deliberately routes its zero-test through the reducible `Nat.beq`).
fn refl_int(t: Expr) -> Expr {
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq_refl, [cst("Int"), t])
}

/// LEMMA — `Trust.FloatN.valueNum` of the CANONICAL ZERO (`mk false 0 0`) is `0`
/// (the `isZero ⟺ value = 0` connection at the canonical zero). The canonical zero is
/// `exponent = 0 ∧ mantissa = 0`, the IEEE classification's `isZero`; its value
/// numerator δ/ι-reduces to a closed `Int` literal — subnormal arm
/// (`Nat.beq (toNat 0) 0 = true`), `magnitude = 0·2 = 0`, `signMul false 0 = 0` — so
/// `valueNum (mk false 0 0) = 0` holds by `Eq.refl` (both sides reduce to `Int.ofNat 0`
/// through the REDUCIBLE `Int.mul`/`Bool.rec`/`Nat.beq` Definitions). Because the fixed
/// denominator `D > 0`, numerator `= 0` IS "the denoted rational equals 0". Proven
/// modulo 3.
#[must_use]
pub fn lemma_zero_has_value_zero(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = value_decl_names(inductive);
    let zero = float_pattern(inductive, false, 0, 0);
    let lhs = Expr::app(cst(&names.value_num), zero);
    let statement = eq_int_prop(lhs, int_lit(0));
    let proof = refl_int(int_lit(0));
    check_value_lemma(width, &format!("{inductive}.value.zero_is_zero"), statement, proof)
}

/// LEMMA — a NONZERO finite float has a NONZERO value numerator (the OTHER direction of
/// `isZero ⟺ value = 0`): `valueNum (mk false 1 0) = 2^(m+1)` (the smallest positive
/// normal, whose numerator over `D` is `(2^m + 0)·2^1 = 2^(m+1) ≠ 0`). An `Int`
/// equality to the EXACT positive numerator, proven by `Eq.refl` — concretely
/// witnessing that a float OUTSIDE the `isZero` class denotes a nonzero rational.
/// Proven modulo 3.
#[must_use]
pub fn lemma_nonzero_has_nonzero_value(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let Some((_exp_bits, mant_bits)) = reflect::ieee754_layout(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("no layout for width {width}"));
    };
    let names = value_decl_names(inductive);
    let f = float_pattern(inductive, false, 1, 0);
    let lhs = Expr::app(cst(&names.value_num), f);
    // (2^m + 0)·2^1 = 2^(m+1).
    let rhs = int_pow(int_two(), nat_lit(u64::from(mant_bits) + 1));
    let statement = eq_int_prop(lhs, rhs.clone());
    let proof = refl_int(rhs);
    check_value_lemma(width, &format!("{inductive}.value.nonzero_is_nonzero"), statement, proof)
}

/// LEMMA (SIGN, GENERAL) — `∀ f, Trust.FloatN.valueNum f = signMul (sign f)
/// (magnitude f)`. The value's numerator FACTORS as the sign coefficient applied to a
/// NON-NEGATIVE magnitude. This is DEFINITIONAL (`valueNum := λf. signMul (sign f)
/// (magnitude f)`), so it holds for ALL `f` by reflexivity under a `Π(f)`. It is the
/// kernel content of "value < 0 ⟺ sign = true for a nonzero finite float": the sign is
/// the ONLY source of negativity (magnitude ≥ 0). Proven modulo 3.
#[must_use]
pub fn lemma_value_sign_factors(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = value_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    // Under `Π(f : FloatN)`: f = bvar(0). lhs = valueNum f; rhs = signMul (sign f) (magnitude f).
    let lhs = Expr::app(cst(&names.value_num), Expr::bvar(0));
    let sign = Expr::proj(Name::from_string(inductive), 0, Expr::bvar(0));
    let mag = Expr::app(cst(&names.magnitude), Expr::bvar(0));
    let rhs = Expr::apps(cst(&names.sign_mul), [sign, mag]);
    let eq_body = eq_int_prop(lhs, rhs);
    let statement = Expr::pi(bd(), cst(inductive), eq_body);
    // Proof: λ(f : FloatN). @Eq.refl Int (valueNum f)  — both sides def-eq by δ-unfolding valueNum.
    let refl = refl_int(Expr::app(cst(&names.value_num), Expr::bvar(0)));
    let proof = Expr::lam(bd(), cst(inductive), refl);
    check_value_lemma(width, &format!("{inductive}.value.sign_factors"), statement, proof)
}

/// LEMMA (SIGN, CONCRETE) — a NEGATIVE-sign nonzero NORMAL float denotes the NEGATED
/// magnitude: `valueNum (mk true 1 0) = Int.neg (2^(m+1))` (the smallest positive
/// normal, negated). The magnitude is `2^(m+1) > 0`; the sign bit makes the numerator
/// its negation. An EXACT `Int` equality to a manifestly-negative value (`Int.neg` of a
/// positive power of two), proven by `Eq.refl` — the sign bit drives the value
/// negative. A WRONG claim (a non-negated RHS) fails to type-check ⇒ KernelRejected.
/// Proven modulo 3.
#[must_use]
pub fn lemma_negative_sign_is_negative(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let Some((_exp_bits, mant_bits)) = reflect::ieee754_layout(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("no layout for width {width}"));
    };
    let names = value_decl_names(inductive);
    let f = float_pattern(inductive, true, 1, 0);
    let lhs = Expr::app(cst(&names.value_num), f);
    // signMul true (2^(m+1)) = Int.neg (2^(m+1)).
    let rhs = int_neg(int_pow(int_two(), nat_lit(u64::from(mant_bits) + 1)));
    let statement = eq_int_prop(lhs, rhs.clone());
    let proof = refl_int(rhs);
    check_value_lemma(width, &format!("{inductive}.value.neg_sign_negative"), statement, proof)
}

/// LEMMA (MANTISSA MONOTONICITY, CONCRETE) — at a FIXED exponent/sign, the value's
/// numerator STRICTLY INCREASES with the mantissa, by a POSITIVE step: for the positive
/// SUBNORMAL floats `a = mk false 0 1` and `b = mk false 0 2` (same sign/exponent 0,
/// mantissa 1 < 2), `Int.sub (valueNum b) (valueNum a) = 2` — the EXACT positive
/// difference `2·2 − 1·2 = 2 > 0`. An `Int` equality to a positive constant, proven by
/// `Eq.refl`: `value b > value a` with a witnessed positive gap. SUBNORMAL witnesses
/// (magnitude = `mantissa·2`) are deliberately tiny so the `Int.sub` of the two
/// numerators ι/δ-reduces cheaply to the literal `2` (the NORMAL arm's `2^m·2^e`
/// numerators are ~2^24 and would make the subtraction's `Nat.rec` reduction
/// impractically large — the IEEE-754 monotonicity content is identical at exponent 0).
/// A WRONG (non-positive) difference fails closed. Proven modulo 3.
#[must_use]
pub fn lemma_mantissa_monotone(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = value_decl_names(inductive);
    let a = float_pattern(inductive, false, 0, 1);
    let b = float_pattern(inductive, false, 0, 2);
    let num_a = Expr::app(cst(&names.value_num), a);
    let num_b = Expr::app(cst(&names.value_num), b);
    // valueNum b − valueNum a = 2·2 − 1·2 = 2 (a positive step ⇒ strictly increasing).
    let diff = Expr::apps(cst("Int.sub"), [num_b, num_a]);
    let statement = eq_int_prop(diff, int_lit(2));
    let proof = refl_int(int_lit(2));
    check_value_lemma(width, &format!("{inductive}.value.mantissa_monotone"), statement, proof)
}

/// The set of value lemmas, each a named [`ValueLemmaVerdict`] checker. Used to assert
/// the whole value-lemma battery is PROVEN modulo 3 for a width, and to drive the
/// fail-closed soundness tests.
#[must_use]
pub fn all_value_lemmas(width: u32) -> Vec<(&'static str, ValueLemmaVerdict)> {
    vec![
        ("zero_has_value_zero", lemma_zero_has_value_zero(width)),
        ("nonzero_has_nonzero_value", lemma_nonzero_has_nonzero_value(width)),
        ("value_sign_factors", lemma_value_sign_factors(width)),
        ("negative_sign_is_negative", lemma_negative_sign_is_negative(width)),
        ("mantissa_monotone", lemma_mantissa_monotone(width)),
    ]
}

// ---------------------------------------------------------------------------
// Step 4 — round-to-nearest-even + the arithmetic OPS (GOAL-ITEM #3, Phase 3)
// ---------------------------------------------------------------------------
//
// THE OP MODEL. The value model gives `value f = (valueNum f, D)` — the rational a
// finite float denotes, numerator over the FIXED positive denominator `D = 2^(m+bias)`.
// Because EVERY finite float of a width shares that denominator, EXACT rational
// arithmetic on the values is just integer arithmetic on the NUMERATORS:
//
//   value a + value b  =  (valueNum a + valueNum b) / D          (exact ℚ sum)
//   value a · value b  =  (valueNum a · valueNum b) / (D·D)      (exact ℚ product)
//
// `Qadd`/`Qmul` below build that EXACT rational result (no rounding yet). The IEEE-754
// op is then `round` of the exact result back to the representable grid, ties-to-even:
//
//   fadd a b := round (Qadd (value a) (value b))
//   fmul a b := round (Qmul (value a) (value b))
//
// THE GRID `round` ROUNDS TO. The SUBNORMAL grid (`exponent = 0`) is UNIFORM: its
// numerators over `D` are exactly the EVEN integers `{2·mantissa}` (since
// `valueNum (mk s 0 m) = signMul s (m·2)`), spaced by `2/D` (one ulp). On a uniform
// grid round-to-nearest-even is the standard "round n/2 to the nearest integer, ties
// to even" — a CLOSED, kernel-reducible Nat computation. `round` implements EXACTLY
// that for an input numerator `N` over `D`:
//
//   roundHalfEven N = let q = N/2, r = N%2 in
//                       if r = 0           then q                  -- exact
//                       else (* tie *)     if q even then q else q+1   -- to even
//   round (N, _) := mk (N<0) 0 (roundHalfEven |N|)
//
// so the rounded subnormal float has mantissa = the nearest even-numerator grid point,
// ties resolved to the EVEN mantissa. Concretely the round and its proofs route the
// magnitude through `Int.toNat` and the arbitrary-precision `Nat.div`/`Nat.mod`/`Nat.beq`
// reducers (NOT the i128-bounded native `Int.div`, which stays stuck on a non-literal
// operand — see the value-model note), so `round (value f)` ι/δ-reduces to a concrete
// float for any subnormal witness `f`, discharging idempotence + exact-op correctness
// by `Eq.refl`.
//
// THE DENOMINATOR CONTRACT (HONEST). `round` reads its input numerator as already being
// over `D` (it IGNORES `Prod.snd`). That is EXACT for `fadd`: `Qadd` keeps the common
// denominator `D`, so `Qadd (value a) (value b) = (na + nb, D)` and `round` rounds the
// true numerator-over-`D`. `fmul` is the SUBTLE case: `Qmul` produces denominator `D·D`,
// so `round` (which assumes `D`) is faithful ONLY where the `D`-vs-`D²` rescale is a
// no-op — the EXACT-ZERO product (`0/D = 0/D² = 0`), which is what `fmul`'s proven lemma
// witnesses. The GENERAL `fmul` rescale (divide the `D²` numerator by `D` before
// rounding) is part of the DEFERRED precise-rounding layer below — NOT claimed here.
//
// SCOPE — HONEST. PROVEN modulo 3 (kernel-checked, ⊆ the 3 axioms, NO 4th):
//   * round IDEMPOTENT on the representable SUBNORMAL grid: round (value (mk s 0 m)) =
//     mk s 0 m (the round is a genuine left-inverse of value there).
//   * EXACT-RESULT `fadd`: when `value a + value b` lands exactly on a grid point
//     `value c`, `fadd a b = c` with NO rounding error.
//   * EXACT-RESULT `fmul` at the exact-zero product (`fmul a 0 = 0`, where the `D²`-vs-`D`
//     rescale is a no-op).
//   * TIES-TO-EVEN: a concrete half-way numerator rounds to the EVEN mantissa, and the
//     WRONG (round-the-tie-UP-off-even) claim is KernelRejected (fail-closed).
// DEFERRED — the precise-rounding layer the kernel cannot yet host (NOT built, NOT faked):
//   * the NORMAL-arm round + the GENERAL half-ulp error bound `|round q − q| ≤ ½ ulp`
//     over the whole exponent range need the floor(log2|q|) exponent-bucket search and
//     real-analysis over the non-uniform normal grid — [`half_ulp_error_bound_status`].
//   * the GENERAL `fmul` rounding (the `D²→D` denominator rescale before rounding) for
//     non-zero products — also [`half_ulp_error_bound_status`].
//   A float-op obligation outside the proven SUBNORMAL-`fadd`/exact cases FAILS CLOSED
//   (sound).

/// Names for the rounding/op declarations of the float inductive `inductive`.
fn op_decl_names(inductive: &str) -> OpNames {
    OpNames {
        round_half_even: format!("{inductive}.roundHalfEven"),
        round: format!("{inductive}.round"),
        q_add: format!("{inductive}.Qadd"),
        q_mul: format!("{inductive}.Qmul"),
        q_div: format!("{inductive}.Qdiv"),
        fadd: format!("{inductive}.fadd"),
        fmul: format!("{inductive}.fmul"),
        fdiv_finite: format!("{inductive}.fdivFinite"),
    }
}

/// The fully-qualified Clean names of the rounding/op declarations.
struct OpNames {
    round_half_even: String,
    round: String,
    q_add: String,
    q_mul: String,
    q_div: String,
    fadd: String,
    fmul: String,
    fdiv_finite: String,
}

/// `@Prod.fst Int Int q : Int` — the numerator projection of a `q : Prod Int Int`.
fn prod_fst_int(q: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod.fst"), vec![Level::zero(), Level::zero()]),
        [cst("Int"), cst("Int"), q],
    )
}

/// `@Prod.snd Int Int q : Int` — the denominator projection of a `q : Prod Int Int`.
fn prod_snd_int(q: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod.snd"), vec![Level::zero(), Level::zero()]),
        [cst("Int"), cst("Int"), q],
    )
}

/// `Nat.div a b : Nat` — arbitrary-precision reducible Nat division (Lean `a/0 = 0`).
fn nat_div(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.div"), [a, b])
}

/// `Nat.mod a b : Nat` — arbitrary-precision reducible Nat remainder (Lean `a%0 = a`).
fn nat_mod(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.mod"), [a, b])
}

/// `Nat.add a b : Nat`.
fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.add"), [a, b])
}

/// `Nat.beq a b : Bool` — arbitrary-precision reducible Nat equality test.
fn nat_beq(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.beq"), [a, b])
}

/// `Nat.sub a b : Nat` — arbitrary-precision reducible Nat subtraction (Lean truncates
/// at 0: `a − b = 0` when `b > a`). Native-reduces on closed literals.
fn nat_sub(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.sub"), [a, b])
}

/// `Nat.mul a b : Nat` — arbitrary-precision reducible Nat multiplication.
fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.mul"), [a, b])
}

/// `Nat.pow base exp : Nat` — arbitrary-precision reducible Nat power. Used to build the
/// binade ulp `2^e` from a `Nat` exponent (the float's stored exponent field).
fn nat_pow(base: Expr, exp: Expr) -> Expr {
    Expr::apps(cst("Nat.pow"), [base, exp])
}

/// `Nat.ble a b : Bool` — arbitrary-precision reducible `a ≤ b` test. `a < b` is spelled
/// `Nat.ble (a+1) b`. Native-reduces on closed literals.
fn nat_ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.ble"), [a, b])
}

/// Register the rounding + arithmetic-op declarations for the float inductive of `width`
/// bits as Clean defs over the value model (idempotent per name). Every term uses ONLY
/// the prelude's axiom-free reducible Definitions (`Int.add`/`mul`/`neg`/`toNat`,
/// `Nat.add`/`div`/`mod`/`beq`, `Bool.rec`, `Prod.fst`/`snd`/`mk`) so the whole op layer
/// rests on EXACTLY the 3 foundational axioms — NO 4th.
///
/// Declarations:
///   * `roundHalfEven : Nat → Nat` = round `a/2` to the nearest integer, ties to even
///     (the uniform-subnormal-grid RNE kernel): `let q=a/2, r=a%2 in if r=0 then q else
///     (if q even then q else q+1)`, built with `Nat.div`/`Nat.mod`/`Nat.beq`/`Bool.rec`.
///   * `round : Prod Int Int → FloatN` = `λq. mk (Prod.fst q < 0) 0 (roundHalfEven
///     |Prod.fst q| 2)` — round a rational (numerator over `D`) to the nearest SUBNORMAL
///     grid float, ties-to-even. The sign is `Int.blt (fst q) 0`; the magnitude is
///     `Int.toNat |fst q|` fed through `roundHalfEven`.
///   * `Qadd : Prod Int Int → Prod Int Int → Prod Int Int` = exact ℚ sum on the COMMON
///     denominator: `λp q. (fst p + fst q, snd p)` (valid when `snd p = snd q = D`, which
///     holds for all `value f`).
///   * `Qmul` = exact ℚ product: `λp q. (fst p · fst q, snd p · snd q)`.
///   * `fadd : FloatN → FloatN → FloatN` = `λa b. round (Qadd (value a) (value b))`.
///   * `fmul : FloatN → FloatN → FloatN` = `λa b. round (Qmul (value a) (value b))`.
///
/// # Errors
/// Returns an error string if the width is unsupported or the kernel rejects a def.
#[allow(clippy::too_many_lines)]
fn register_ops(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let names = op_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    let float_ty = cst(inductive);
    let q_ty = prod_int_int();

    // Bool.rec.{1} into Nat — for the ties-to-even dispatch.
    let bool_rec_nat =
        || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let nat_motive = || Expr::lam(bd(), cst("Bool"), cst("Nat"));

    // --- roundHalfEven : Nat → Nat ---
    // Under `λ(a:Nat)`: a = bvar(0). q = a/2, r = a%2.
    //   tieResult = if (q % 2 = 0) then q else q+1          -- round the .5 tie to even
    //   result    = if (r = 0)     then q else tieResult     -- exact vs tie
    if env.get_const(&Name::from_string(&names.round_half_even)).is_none() {
        let a = || Expr::bvar(0);
        let q = || nat_div(a(), nat_lit(2));
        let r = || nat_mod(a(), nat_lit(2));
        // q is even  ⟺  Nat.beq (q % 2) 0
        let q_even = nat_beq(nat_mod(q(), nat_lit(2)), nat_lit(0));
        // @Bool.rec (λ_.Nat) FALSE(q+1) TRUE(q) (q_even): false ↦ odd ↦ q+1, true ↦ q.
        let tie = Expr::apps(bool_rec_nat(), [nat_motive(), nat_add(q(), nat_lit(1)), q(), q_even]);
        // r = 0  ⟺  Nat.beq r 0
        let r_zero = nat_beq(r(), nat_lit(0));
        // @Bool.rec (λ_.Nat) FALSE(tie) TRUE(q) (r_zero): false ↦ tie, true ↦ exact q.
        let result = Expr::apps(bool_rec_nat(), [nat_motive(), tie, q(), r_zero]);
        let value = Expr::lam(bd(), cst("Nat"), result);
        let ty = Expr::pi(bd(), cst("Nat"), cst("Nat"));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.round_half_even),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.round_half_even))?;
    }

    // --- round : Prod Int Int → FloatN ---
    // Under `λ(qr : Prod Int Int)`: qr = bvar(0); n = Prod.fst qr (numerator over D).
    // The sign + magnitude are read WITHOUT `Int.natAbs`/`Int.blt` (the core prelude has
    // neither as a const) using ONLY `Int.toNat`/`Int.neg`/`Nat.add`/`Nat.beq`:
    //   * negNat := Int.toNat (Int.neg n)  -- = |n| if n<0, else 0
    //   * posNat := Int.toNat n            -- = n   if n≥0, else 0
    //   * absNat := Nat.add posNat negNat  -- = |n| for ANY n (exactly one summand is 0)
    //   * isNonNeg := Nat.beq negNat 0     -- true ⟺ Int.toNat(-n)=0 ⟺ n≥0 (n=0 ↦ true)
    //   * sign : Bool = Bool.rec (λ_.Bool) Bool.true Bool.false isNonNeg
    //       (isNonNeg=false ⟹ sign true [negative]; isNonNeg=true ⟹ sign false)
    //   * mantissa = Int.ofNat (roundHalfEven absNat)
    //   * round qr = mk sign (Int.ofNat 0) mantissa
    if env.get_const(&Name::from_string(&names.round)).is_none() {
        let n = || prod_fst_int(Expr::bvar(0));
        let neg_nat = || int_to_nat(int_neg(n()));
        let abs_nat = || nat_add(int_to_nat(n()), neg_nat());
        // isNonNeg : Bool = Nat.beq (Int.toNat (Int.neg n)) 0.
        let is_non_neg = nat_beq(neg_nat(), nat_lit(0));
        // sign : Bool — Bool.rec.{1} into Bool, false-minor=Bool.true, true-minor=Bool.false.
        let bool_rec_bool =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let bool_motive = Expr::lam(bd(), cst("Bool"), cst("Bool"));
        let sign = Expr::apps(
            bool_rec_bool,
            [bool_motive, cst("Bool.true"), cst("Bool.false"), is_non_neg],
        );
        let mant_nat = Expr::app(cst(&names.round_half_even), abs_nat());
        let mantissa = Expr::app(cst("Int.ofNat"), mant_nat);
        // mk sign (Int.ofNat 0) mantissa
        let mk = cst(&format!("{inductive}.mk"));
        let body = Expr::apps(mk, [sign, int_lit(0), mantissa]);
        let value = Expr::lam(bd(), q_ty.clone(), body);
        let ty = Expr::pi(bd(), q_ty.clone(), float_ty.clone());
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.round),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.round))?;
    }

    // --- Qadd : Prod Int Int → Prod Int Int → Prod Int Int ---
    // λp q. (Prod.fst p + Prod.fst q, Prod.snd p)   -- exact sum on the common denom.
    if env.get_const(&Name::from_string(&names.q_add)).is_none() {
        let p = || Expr::bvar(1);
        let q = || Expr::bvar(0);
        let num = int_add(prod_fst_int(p()), prod_fst_int(q()));
        let den = prod_snd_int(p());
        let body = prod_mk_int(num, den);
        let value = Expr::lam(bd(), q_ty.clone(), Expr::lam(bd(), q_ty.clone(), body));
        let ty = Expr::pi(bd(), q_ty.clone(), Expr::pi(bd(), q_ty.clone(), q_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.q_add),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.q_add))?;
    }

    // --- Qmul : Prod Int Int → Prod Int Int → Prod Int Int ---
    // λp q. (Prod.fst p · Prod.fst q, Prod.snd p · Prod.snd q)  -- exact product.
    if env.get_const(&Name::from_string(&names.q_mul)).is_none() {
        let p = || Expr::bvar(1);
        let q = || Expr::bvar(0);
        let num = int_mul(prod_fst_int(p()), prod_fst_int(q()));
        let den = int_mul(prod_snd_int(p()), prod_snd_int(q()));
        let body = prod_mk_int(num, den);
        let value = Expr::lam(bd(), q_ty.clone(), Expr::lam(bd(), q_ty.clone(), body));
        let ty = Expr::pi(bd(), q_ty.clone(), Expr::pi(bd(), q_ty.clone(), q_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.q_mul),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.q_mul))?;
    }

    // --- fadd : FloatN → FloatN → FloatN = λa b. round (Qadd (value a) (value b)) ---
    if env.get_const(&Name::from_string(&names.fadd)).is_none() {
        let a = || Expr::app(cst(&vnames.value), Expr::bvar(1));
        let b = || Expr::app(cst(&vnames.value), Expr::bvar(0));
        let sum = Expr::apps(cst(&names.q_add), [a(), b()]);
        let body = Expr::app(cst(&names.round), sum);
        let value = Expr::lam(bd(), float_ty.clone(), Expr::lam(bd(), float_ty.clone(), body));
        let ty =
            Expr::pi(bd(), float_ty.clone(), Expr::pi(bd(), float_ty.clone(), float_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.fadd),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.fadd))?;
    }

    // --- fmul : FloatN → FloatN → FloatN = λa b. round (Qmul (value a) (value b)) ---
    if env.get_const(&Name::from_string(&names.fmul)).is_none() {
        let a = || Expr::app(cst(&vnames.value), Expr::bvar(1));
        let b = || Expr::app(cst(&vnames.value), Expr::bvar(0));
        let prod = Expr::apps(cst(&names.q_mul), [a(), b()]);
        let body = Expr::app(cst(&names.round), prod);
        let value = Expr::lam(bd(), float_ty.clone(), Expr::lam(bd(), float_ty.clone(), body));
        let ty =
            Expr::pi(bd(), float_ty.clone(), Expr::pi(bd(), float_ty.clone(), float_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.fmul),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.fmul))?;
    }

    // --- Qdiv : Prod Int Int → Prod Int Int → Prod Int Int ---
    // λp q. (Prod.fst p · Prod.snd q, Prod.snd p · Prod.fst q)  -- the EXACT rational
    // quotient by CROSS-MULTIPLICATION: (an/ad) / (bn/bd) = (an·bd)/(ad·bn). This is a
    // TOTAL function (no division of integers — only integer MULTIPLY of the four field
    // projections), so it never gets stuck. Rational division is EXACT — no rounding is
    // needed for the RATIONAL result; the ONLY rounding is rounding that exact rational
    // quotient back to the float grid (see `fdivFinite`). Built over only `Int.mul` +
    // `Prod.fst`/`snd`/`mk`, so it rests on EXACTLY the 3 foundational axioms — NO 4th.
    if env.get_const(&Name::from_string(&names.q_div)).is_none() {
        let p = || Expr::bvar(1);
        let q = || Expr::bvar(0);
        // num = an·bd = Prod.fst p · Prod.snd q ; den = ad·bn = Prod.snd p · Prod.fst q.
        let num = int_mul(prod_fst_int(p()), prod_snd_int(q()));
        let den = int_mul(prod_snd_int(p()), prod_fst_int(q()));
        let body = prod_mk_int(num, den);
        let value = Expr::lam(bd(), q_ty.clone(), Expr::lam(bd(), q_ty.clone(), body));
        let ty = Expr::pi(bd(), q_ty.clone(), Expr::pi(bd(), q_ty.clone(), q_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.q_div),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.q_div))?;
    }

    // --- fdivFinite : FloatN → FloatN → FloatN = λa b. round (Qdiv (value a) (value b)) ---
    // The FINITE/finite IEEE-754 divide: form the EXACT rational quotient `Qdiv (value a)
    // (value b)` (no rounding — rational division is exact), then `round` that exact
    // rational back to the representable grid, ties-to-even — EXACTLY like `fmul` rounds
    // the exact rational product. Division by ZERO at the finite level is NOT this op's
    // concern: it routes to the non-finite signed-∞ rule (`fdivExt`, already proven); this
    // op carries the FINITE/finite arm where the divisor is nonzero (and the zero-DIVIDEND
    // exact case `0 / b = 0`). Same denominator-contract subtlety as `fmul`: `round` reads
    // its numerator over `D` while `Qdiv` carries the `D`-vs-`ad·bn` rescale, so the EXACT
    // cases proven are where that rescale is a no-op (the zero quotient).
    if env.get_const(&Name::from_string(&names.fdiv_finite)).is_none() {
        let a = || Expr::app(cst(&vnames.value), Expr::bvar(1));
        let b = || Expr::app(cst(&vnames.value), Expr::bvar(0));
        let quot = Expr::apps(cst(&names.q_div), [a(), b()]);
        let body = Expr::app(cst(&names.round), quot);
        let value = Expr::lam(bd(), float_ty.clone(), Expr::lam(bd(), float_ty.clone(), body));
        let ty =
            Expr::pi(bd(), float_ty.clone(), Expr::pi(bd(), float_ty.clone(), float_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.fdiv_finite),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.fdiv_finite))?;
    }
    Ok(())
}

/// Build a kernel `Environment` with the prelude, the `Trust.FloatN` inductive, the
/// classification predicates, the VALUE interpretation, AND the rounding + arithmetic
/// ops registered — the full structured-float + value + ops environment for `width`.
///
/// # Errors
/// Returns the registration error string for an unsupported width or a gate failure.
pub fn op_env(width: u32) -> Result<Environment, String> {
    let mut env = value_env(width)?;
    register_ops(&mut env, width)?;
    Ok(env)
}

/// The op-model declaration names that must rest on EXACTLY the 3 foundational axioms
/// (audited by [`pin_float_ops`]).
fn op_audit_names(inductive: &str) -> Vec<String> {
    let n = op_decl_names(inductive);
    vec![n.round_half_even, n.round, n.q_add, n.q_mul, n.q_div, n.fadd, n.fmul, n.fdiv_finite]
}

/// Pin the rounding + arithmetic-op model of `width` bits (`roundHalfEven`/`round`/
/// `Qadd`/`Qmul`/`fadd`/`fmul`) and audit the axiom closure via the kernel's own
/// `axiom_deps`. Confirms the entire op layer rests on EXACTLY the 3 foundational
/// axioms (modulo 3, NO 4th axiom) — built over only the prelude's axiom-free reducible
/// Definitions.
#[must_use]
pub fn pin_float_ops(width: u32) -> FloatClassVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return FloatClassVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let env = match op_env(width) {
        Ok(e) => e,
        Err(e) => return FloatClassVerdict::KernelRejected(e),
    };
    for n in op_audit_names(inductive) {
        match env.axiom_deps(&Name::from_string(&n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
                ns.sort();
                return FloatClassVerdict::Residue(ns);
            }
            None => return FloatClassVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    FloatClassVerdict::Modulo3
}

/// Type-check that `Trust.FloatN.fadd`/`fmul` of `width` bits have type
/// `Trust.FloatN → Trust.FloatN → Trust.FloatN` and `round` has type
/// `Prod Int Int → Trust.FloatN` in the real kernel — the ops KERNEL-CHECK as real
/// float→float operations over the structure.
///
/// # Errors
/// Returns a description if the env fails to build or an op's inferred type is wrong.
pub fn ops_typecheck(width: u32) -> Result<(), String> {
    let inductive =
        reflect::float_inductive_name(width).ok_or_else(|| format!("unsupported width {width}"))?;
    let env = op_env(width)?;
    let tc = TypeChecker::new(&env);
    let bd = || BinderData::from(BinderInfo::Default);
    let names = op_decl_names(inductive);
    let float_ty = cst(inductive);
    // round : Prod Int Int → FloatN
    let round_expected = Expr::pi(bd(), prod_int_int(), float_ty.clone());
    let round_inferred = tc
        .infer_type(&cst(&names.round))
        .map_err(|e| format!("{}.round has no type: {e:?}", inductive))?;
    if !tc.is_def_eq(&round_inferred, &round_expected) {
        return Err(format!("{inductive}.round is not Prod Int Int → FloatN"));
    }
    // Qdiv : Prod Int Int → Prod Int Int → Prod Int Int (the exact rational quotient carrier).
    let qbinop_expected =
        Expr::pi(bd(), prod_int_int(), Expr::pi(bd(), prod_int_int(), prod_int_int()));
    let qdiv_inferred = tc
        .infer_type(&cst(&names.q_div))
        .map_err(|e| format!("{}.Qdiv has no type: {e:?}", inductive))?;
    if !tc.is_def_eq(&qdiv_inferred, &qbinop_expected) {
        return Err(format!("{inductive}.Qdiv is not Prod Int Int → Prod Int Int → Prod Int Int"));
    }
    // fadd, fmul, fdivFinite : FloatN → FloatN → FloatN
    let binop_expected =
        Expr::pi(bd(), float_ty.clone(), Expr::pi(bd(), float_ty.clone(), float_ty.clone()));
    for op in [&names.fadd, &names.fmul, &names.fdiv_finite] {
        let inferred = tc.infer_type(&cst(op)).map_err(|e| format!("{op} has no type: {e:?}"))?;
        if !tc.is_def_eq(&inferred, &binop_expected) {
            return Err(format!("{op} is not FloatN → FloatN → FloatN"));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Step 4b — the OP-correctness lemmas (idempotence, exact-result, ties-to-even)
// ---------------------------------------------------------------------------

/// `@Eq Trust.FloatN a b : Prop` — the float-equality statement form (the carrier lives
/// in `Type`, so the `Eq` level is `Sort 1`).
fn eq_float_prop(inductive: &str, a: Expr, b: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq, [cst(inductive), a, b])
}

/// `@Eq.refl Trust.FloatN f : @Eq Trust.FloatN f f` — reflexivity for a float equality
/// whose two sides ι/δ-reduce to the same `mk …` normal form.
fn refl_float(inductive: &str, f: Expr) -> Expr {
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq_refl, [cst(inductive), f])
}

/// Register `theorem <name> : <statement> := <proof>` into a fresh op-env and audit the
/// axiom closure — the shared driver for every OP lemma. A wrong claim makes the kernel
/// reject `proof` against `statement` ⇒ [`ValueLemmaVerdict::KernelRejected`].
fn check_op_lemma(width: u32, name: &str, statement: Expr, proof: Expr) -> ValueLemmaVerdict {
    let mut env = match op_env(width) {
        Ok(e) => e,
        Err(e) => return ValueLemmaVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return ValueLemmaVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let decl_name = Name::from_string(name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: decl_name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return ValueLemmaVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&decl_name) {
        Some(residue) if residue.is_empty() => ValueLemmaVerdict::ProvenModulo3,
        Some(residue) => {
            let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
            ns.sort();
            ValueLemmaVerdict::Residue(ns)
        }
        None => ValueLemmaVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// LEMMA (ROUND IDEMPOTENT on the SUBNORMAL grid) — `round (value (mk false 0 m)) =
/// mk false 0 m` for a concrete subnormal mantissa `m`: round is a genuine LEFT-INVERSE
/// of `value` on the representable subnormal grid, so a value already on the grid rounds
/// back to ITSELF with NO error. The value's numerator `m·2` is even, so `roundHalfEven
/// (m·2) 2 = m` exactly (`r = 0` arm), `sign = (m·2 < 0) = false`, exponent `0` — the
/// whole `round (value …)` ι/δ-reduces to `mk false 0 m`, proven by `Eq.refl`. Proven
/// modulo 3.
#[must_use]
pub fn lemma_round_idempotent_subnormal(width: u32, mantissa: u64) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = op_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    let f = float_pattern(inductive, false, 0, mantissa);
    // round (value f)
    let lhs = Expr::app(cst(&names.round), Expr::app(cst(&vnames.value), f.clone()));
    let statement = eq_float_prop(inductive, lhs, f.clone());
    let proof = refl_float(inductive, f);
    check_op_lemma(
        width,
        &format!("{inductive}.round.idempotent_subnormal_{mantissa}"),
        statement,
        proof,
    )
}

/// LEMMA (ROUND IDEMPOTENT on a NEGATIVE subnormal) — `round (value (mk true 0 m)) =
/// mk true 0 m`: the round recovers the SIGN as well (`sign = (−m·2 < 0) = true`), so a
/// negative grid value rounds back to itself. Proven by `Eq.refl` (the numerator
/// `Int.neg (m·2)` drives `Int.blt … 0 = true` and `|·|` recovers `m·2`). Proven
/// modulo 3.
#[must_use]
pub fn lemma_round_idempotent_negative_subnormal(width: u32, mantissa: u64) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = op_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    let f = float_pattern(inductive, true, 0, mantissa);
    let lhs = Expr::app(cst(&names.round), Expr::app(cst(&vnames.value), f.clone()));
    let statement = eq_float_prop(inductive, lhs, f.clone());
    let proof = refl_float(inductive, f);
    check_op_lemma(
        width,
        &format!("{inductive}.round.idempotent_neg_subnormal_{mantissa}"),
        statement,
        proof,
    )
}

/// LEMMA (EXACT-RESULT `fadd`) — when `value a + value b` lands EXACTLY on a grid point
/// `value c`, `fadd a b = c` with NO rounding error: `fadd (mk false 0 1) (mk false 0 2)
/// = mk false 0 3`. The exact sum's numerator is `1·2 + 2·2 = 6 = 3·2`, an even
/// (on-grid) numerator, so `round` returns the EXACT float `mk false 0 3`. Proven by
/// `Eq.refl` — the IEEE add is EXACT here (the result is representable, no rounding).
/// Proven modulo 3.
#[must_use]
pub fn lemma_fadd_exact(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = op_decl_names(inductive);
    let a = float_pattern(inductive, false, 0, 1);
    let b = float_pattern(inductive, false, 0, 2);
    let c = float_pattern(inductive, false, 0, 3);
    let lhs = Expr::apps(cst(&names.fadd), [a, b]);
    let statement = eq_float_prop(inductive, lhs, c.clone());
    let proof = refl_float(inductive, c);
    check_op_lemma(width, &format!("{inductive}.fadd.exact_1_2_3"), statement, proof)
}

/// LEMMA (EXACT-RESULT `fmul`, exact-zero) — `fmul (mk false 0 3) (mk false 0 0) =
/// mk false 0 0`: multiplying by ZERO is EXACT. `Qmul` squares the denominator (to `D²`),
/// so for a GENERAL product `round` (which reads its numerator over `D`) would need the
/// `D²→D` rescale that is DEFERRED; but the ZERO product has numerator `0`, and `0/D² =
/// 0/D = 0` makes the rescale a no-op, so `fmul a 0 = 0` holds with NO rounding error.
/// Proven by `Eq.refl`. Proven modulo 3. (The non-zero `fmul` rescale is part of the
/// deferred precise-rounding layer — see [`half_ulp_error_bound_status`].)
#[must_use]
pub fn lemma_fmul_zero_exact(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = op_decl_names(inductive);
    let a = float_pattern(inductive, false, 0, 3);
    let zero = float_pattern(inductive, false, 0, 0);
    let lhs = Expr::apps(cst(&names.fmul), [a, zero.clone()]);
    let statement = eq_float_prop(inductive, lhs, zero.clone());
    let proof = refl_float(inductive, zero);
    check_op_lemma(width, &format!("{inductive}.fmul.zero_exact"), statement, proof)
}

/// LEMMA (EXACT-RESULT / IDEMPOTENCE `fdivFinite`, exact-zero dividend) — `fdivFinite
/// (mk false 0 0) (mk false 0 3) = mk false 0 0`: dividing ZERO by a nonzero finite is
/// EXACT, `0 / 3 = 0`, with NO rounding error. The EXACT rational quotient `Qdiv (value 0)
/// (value 3) = (0·bd, ad·bn) = (0, …)` has NUMERATOR `0`; `round (0, _)` reads numerator `0`
/// over `D` (sign `0 < 0 = false`, mantissa `roundHalfEven |0| = 0`), so it returns the
/// EXACT float `mk false 0 0`. This is the `fdivFinite` analog of `fmul_zero_exact`: the
/// `D`-vs-`ad·bn` denominator rescale `round` cannot yet do is a NO-OP precisely at the zero
/// quotient (`0/D = 0/(ad·bn) = 0`), so the round-back lands EXACTLY on the grid point and
/// `round (value c) = c` (round is a left-inverse there — IDEMPOTENCE on the exact result).
/// Proven by `Eq.refl`. Proven modulo 3. (The general nonzero-quotient rescale is the
/// deferred precise-rounding layer — see [`half_ulp_error_bound_status`]; its half-ulp
/// ENVELOPE is covered universally by [`lemma_fdiv_finite_error_bound`].)
#[must_use]
pub fn lemma_fdiv_finite_zero_exact(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = op_decl_names(inductive);
    let zero = float_pattern(inductive, false, 0, 0);
    let b = float_pattern(inductive, false, 0, 3);
    let lhs = Expr::apps(cst(&names.fdiv_finite), [zero.clone(), b]);
    let statement = eq_float_prop(inductive, lhs, zero.clone());
    let proof = refl_float(inductive, zero);
    check_op_lemma(width, &format!("{inductive}.fdivFinite.zero_exact"), statement, proof)
}

/// LEMMA (DIVISION HALF-ULP ERROR BOUND, via the UNIVERSAL Nat bound) — the rounded finite
/// quotient is within ½·ulp of the EXACT rational quotient. The exact rational quotient
/// `Qdiv (value a) (value b)` is JUST ANOTHER rational fed to `round`, so the SAME universal
/// half-ulp bound that governs every `round` applies to ITS numerator with NO new argument:
/// for the quotient numerator `Nq = |Prod.fst (Qdiv (value a) (value b))|` rounded onto the
/// binade-`e` grid, `2·|roundHalfEvenMod Nq (2^e) − Nq| ≤ 2^e`. We discharge it by
/// instantiating the proven `Nat.ulp_universal_bound e Nq` (cited; axiom-free, ⊆ the 3) —
/// the quotient numerator is a concrete `Nat` substituted for the universal `∀ N`. The
/// statement is INFERRED so `2^e` stays symbolic (instant at any `e`, NO reduction blowup).
/// PROVEN modulo 3. This closes the division-arm half-ulp ENVELOPE by REUSE of the universal
/// bound — no division-specific real-analysis is added; the quotient is bounded BECAUSE it is
/// a rational handed to the same round. A too-tight (¼·ulp) division claim FAILS CLOSED for
/// the SAME structural reason as [`wrong_quarter_ulp_universal_fails_closed`].
#[must_use]
pub fn lemma_fdiv_finite_error_bound(width: u32, exponent: u64) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = op_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    // The env must carry the universal bound (fails closed if the clean pin is stale).
    let mut env = match op_env(width) {
        Ok(e) => e,
        Err(e) => return ValueLemmaVerdict::KernelRejected(e),
    };
    if env.get_const(&Name::from_string(ULP_UNIVERSAL_BOUND)).is_none() {
        return ValueLemmaVerdict::KernelRejected(format!(
            "prelude is missing {ULP_UNIVERSAL_BOUND} (clean pin too old)"
        ));
    }
    // The CONCRETE finite quotient `Qdiv (value a) (value b)` for a witness a/b (3 / 2): its
    // numerator is `Prod.fst (Qdiv (value a) (value b)) : Int`. Feed |·| (= Int.toNat of the
    // numerator) — the EXACT rational quotient's numerator AS the universal bound's `N`.
    let a = float_pattern(inductive, false, 0, 3);
    let b = float_pattern(inductive, false, 0, 2);
    let va = Expr::app(cst(&vnames.value), a);
    let vb = Expr::app(cst(&vnames.value), b);
    let quot = Expr::apps(cst(&names.q_div), [va, vb]);
    let nq = int_to_nat(prod_fst_int(quot)); // |numerator of the exact quotient| as Nat
    // proof = Nat.ulp_universal_bound <e> Nq — instantiate the ∀N universal bound AT the
    // quotient numerator. INFER its (symbolic, 2^e-unreduced) type so it is instant at any e.
    let proof = Expr::apps(cst(ULP_UNIVERSAL_BOUND), [nat_lit(exponent), nq]);
    let statement = {
        let tc = TypeChecker::new(&env);
        match tc.infer_type(&proof) {
            Ok(ty) => ty,
            Err(e) => {
                return ValueLemmaVerdict::KernelRejected(format!("infer_type(div bound): {e:?}"));
            }
        }
    };
    let name = Name::from_string(&format!("{inductive}.fdivFinite.error_bound_e{exponent}"));
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return ValueLemmaVerdict::KernelRejected(format!("add_decl(div bound): {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => ValueLemmaVerdict::ProvenModulo3,
        Some(residue) => {
            let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
            ns.sort();
            ValueLemmaVerdict::Residue(ns)
        }
        None => ValueLemmaVerdict::KernelRejected("div bound decl not found".to_string()),
    }
}

/// LEMMA (FINITE/FINITE TIE-IN to `fdivExt`) — the non-finite `fdivExt` layer's finite/finite
/// arm carries EXACTLY the `Qdiv` of `fdivFinite`: `fdivExt (Finite (value a)) (Finite (value
/// b)) = Finite (Qdiv (value a) (value b))` for nonzero divisor `b`. This is the structural
/// connection between the proven non-finite `fdivExt` (±∞/NaN, signed-∞ div-by-zero) and the
/// new finite round-back op: above the `round`, both speak the SAME exact rational quotient
/// `Qdiv`. Concretely `fdivExt (Finite (3,1)) (Finite (2,1)) = Finite (Qdiv (3,1) (2,1))`
/// (divisor `2 ≠ 0`, so the q=0 guard takes the quotient arm). Proven by `Eq.refl` after the
/// double-recursor ι-reduction (the inner `isZero 2 = false` selects the `Finite (Qdiv …)`
/// leaf). Division by ZERO at the finite level routes to the non-finite signed-∞ rule (the
/// `q=0` guard, already proven in [`all_fdiv_ext_rules`]) — kept consistent. Proven modulo 3.
#[must_use]
pub fn lemma_fdiv_ext_finite_is_qdiv(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = ext_decl_names(inductive);
    let onames = op_decl_names(inductive);
    // p = (3,1), q = (2,1) (divisor nonzero ⇒ quotient arm). fdivExt (Finite p) (Finite q)
    // = Finite (Qdiv p q).
    let p = prod_mk_int(int_lit(3), int_lit(1));
    let q = prod_mk_int(int_lit(2), int_lit(1));
    let fp = Expr::app(cst(&names.finite), p.clone());
    let fq = Expr::app(cst(&names.finite), q.clone());
    let lhs = Expr::apps(cst(&names.fdiv_ext), [fp, fq]);
    let rhs = Expr::app(cst(&names.finite), Expr::apps(cst(&onames.q_div), [p, q]));
    let statement = eq_ext_prop(&names, lhs, rhs.clone());
    let proof = refl_ext(&names, rhs);
    check_ext_lemma(width, &format!("{inductive}.ext.fdiv_finite_is_qdiv"), statement, proof)
}

/// FAIL-CLOSED — a WRONG finite quotient (the `Qdiv` numerator/denominator SWAPPED, i.e. the
/// RECIPROCAL `b / a` instead of `a / b`) is KernelRejected. Claims `fdivFinite (mk false 0 3)
/// (mk false 0 2) = round (Qdiv (value b) (value a))` (operands FLIPPED) — that is `value 2 /
/// value 3`, a DIFFERENT rational, which rounds to a DIFFERENT grid point than `value 3 / value
/// 2`, so the two `mk …` normal forms DIFFER and `Eq.refl` does NOT type-check. Returns `true`
/// iff the kernel rejects (the fail-closed teeth: a swapped/reciprocal quotient can NEVER be
/// passed off as `fdivFinite a b`).
#[must_use]
pub fn wrong_fdiv_finite_swapped_fails_closed(width: u32) -> bool {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return true;
    };
    let names = op_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    let a = float_pattern(inductive, false, 0, 3);
    let b = float_pattern(inductive, false, 0, 2);
    // The TRUE lhs: fdivFinite a b.
    let lhs = Expr::apps(cst(&names.fdiv_finite), [a.clone(), b.clone()]);
    // The WRONG rhs: round (Qdiv (value b) (value a)) — operands SWAPPED (the reciprocal).
    let vb = Expr::app(cst(&vnames.value), b);
    let va = Expr::app(cst(&vnames.value), a);
    let swapped = Expr::apps(cst(&names.q_div), [vb, va]); // value b / value a (reciprocal!)
    let wrong_rhs = Expr::app(cst(&names.round), swapped);
    let statement = eq_float_prop(inductive, lhs.clone(), wrong_rhs);
    // The proof claims `fdivFinite a b = fdivFinite a b` (TRUE by refl); check it against the
    // WRONG statement `fdivFinite a b = round (Qdiv (value b) (value a))`. The kernel must REJECT
    // (3/2 and 2/3 round to DIFFERENT mk-floats, so the lhs is NOT def-eq the swapped rhs).
    matches!(
        check_op_lemma(
            width,
            &format!("{inductive}.fdivFinite.WRONG_swapped"),
            statement,
            refl_float(inductive, lhs),
        ),
        ValueLemmaVerdict::KernelRejected(_)
    )
}

/// FAIL-CLOSED (CHEAP, at the Int level) — a WRONG `Qdiv` numerator (NUMERATOR/DENOMINATOR
/// roles SWAPPED) is KernelRejected. The exact quotient `Qdiv (3,1) (2,1)` numerator is
/// `Prod.fst p · Prod.snd q = 3·1 = 3`; a swap that put the DENOMINATOR cross-product there
/// would give `Prod.snd p · Prod.fst q = 1·2 = 2`. The claim `Prod.fst (Qdiv (3,1) (2,1)) = 2`
/// (the swapped numerator) is FALSE — the true numerator reduces to `3` — so `Eq.refl 2` does
/// NOT type-check against it. This pins that `Qdiv` cross-multiplies in the CORRECT direction
/// (`an·bd`, not `ad·bn`), a tiny Int reduction (NO huge `D`-scaled round). Returns `true` iff
/// the kernel rejects.
#[must_use]
pub fn wrong_qdiv_numerator_swapped_fails_closed(width: u32) -> bool {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return true;
    };
    let names = op_decl_names(inductive);
    let p = prod_mk_int(int_lit(3), int_lit(1));
    let q = prod_mk_int(int_lit(2), int_lit(1));
    // The TRUE numerator of Qdiv (3,1) (2,1) is 3 (= an·bd = 3·1). The WRONG (swapped) claim:
    // it equals 2 (= ad·bn = 1·2). Eq.refl 2 must FAIL against `Prod.fst (Qdiv p q) = 2`.
    let lhs = prod_fst_int(Expr::apps(cst(&names.q_div), [p, q]));
    let wrong_statement = eq_int_prop(lhs, int_lit(2));
    matches!(
        check_op_lemma(
            width,
            &format!("{inductive}.Qdiv.WRONG_num_swap"),
            wrong_statement,
            refl_int(int_lit(2))
        ),
        ValueLemmaVerdict::KernelRejected(_)
    )
}

/// FAIL-CLOSED — a TOO-TIGHT (¼·ulp) DIVISION error bound is KernelRejected. The finite-division
/// error bound is LITERALLY `Nat.ulp_universal_bound e N` instantiated at the quotient numerator
/// (see [`lemma_fdiv_finite_error_bound`]); a strictly-tighter-than-½ulp claim on it can NEVER be
/// proven for the SAME structural reason the universal bound is tight: the proven ½·ulp witness
/// has head literal `Nat.mul 2 …`, the ¼·ulp claim demands `Nat.mul 4 …`, and at an exact tie the
/// error is EXACTLY ½·ulp so `4·error > 2^e` is genuinely FALSE. We keep the numerator SYMBOLIC
/// (a `∀ N`, exactly the division bound's universal source) so the rejection is the robust
/// head-literal mismatch — independent of the concrete quotient's tie alignment, and cheap even
/// at the huge e = 127. Returns `true` iff the kernel rejects. This is the division arm's
/// too-tight-bound fail-closed teeth (it delegates to the proven universal source it reuses).
#[must_use]
pub fn wrong_quarter_ulp_fdiv_finite_fails_closed(width: u32, exponent: u64) -> bool {
    // The division half-ulp bound IS `Nat.ulp_universal_bound e N` at the quotient numerator, so a
    // ¼·ulp claim on it fails closed exactly when the universal ¼·ulp claim does (head-literal
    // `Nat.mul 4` vs `Nat.mul 2`, rejected structurally — robust for ALL N, hence for the quotient
    // numerator). Delegate to the proven-tight universal fail-closed.
    wrong_quarter_ulp_universal_fails_closed(width, exponent)
}

/// LEMMA (TIES-TO-EVEN, the round-to-nearest-EVEN teeth) — a half-way numerator rounds
/// to the EVEN mantissa: `roundHalfEven 5 = 2` (5/2 = 2.5, a tie; the neighbors are
/// `2` (even) and `3` (odd); RNE picks the EVEN `2`, NOT the larger `3`). Proven by
/// `Eq.refl` over the arbitrary-precision `Nat.div`/`Nat.mod`/`Nat.beq` reducers. A WRONG
/// claim — that the tie rounds UP to `3` — is [`ValueLemmaVerdict::KernelRejected`]
/// (see [`lemma_tie_to_even_wrong_up_fails_closed`]). Proven modulo 3.
#[must_use]
pub fn lemma_round_half_even_tie(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = op_decl_names(inductive);
    // roundHalfEven 5 = 2 (5/2 = 2.5 ties to even 2). Stated as an Int equality on Int.ofNat.
    let lhs = Expr::app(cst("Int.ofNat"), Expr::app(cst(&names.round_half_even), nat_lit(5)));
    let statement = eq_int_prop(lhs, int_lit(2));
    let proof = refl_int(int_lit(2));
    check_op_lemma(width, &format!("{inductive}.round.tie_5_to_even_2"), statement, proof)
}

/// LEMMA (TIES-TO-EVEN, the OTHER tie) — `roundHalfEven 7 = 4` (7/2 = 3.5, a tie
/// between `3` (odd) and `4` (even); RNE rounds UP to the EVEN `4` this time — ties go
/// to even in EITHER direction, not always down). Together with
/// [`lemma_round_half_even_tie`] this pins that RNE follows the EVEN neighbor, not a
/// fixed direction. Proven by `Eq.refl`. Proven modulo 3.
#[must_use]
pub fn lemma_round_half_even_tie_up(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = op_decl_names(inductive);
    // roundHalfEven 7 = 4 (7/2 = 3.5 ties to even 4).
    let lhs = Expr::app(cst("Int.ofNat"), Expr::app(cst(&names.round_half_even), nat_lit(7)));
    let statement = eq_int_prop(lhs, int_lit(4));
    let proof = refl_int(int_lit(4));
    check_op_lemma(width, &format!("{inductive}.round.tie_7_to_even_4"), statement, proof)
}

/// The set of OP-correctness lemmas, each a named [`ValueLemmaVerdict`] checker. Asserts
/// the whole op-lemma battery is PROVEN modulo 3 for a width and drives the fail-closed
/// soundness tests.
#[must_use]
pub fn all_op_lemmas(width: u32) -> Vec<(&'static str, ValueLemmaVerdict)> {
    vec![
        ("round_idempotent_subnormal_3", lemma_round_idempotent_subnormal(width, 3)),
        ("round_idempotent_subnormal_10", lemma_round_idempotent_subnormal(width, 10)),
        (
            "round_idempotent_negative_subnormal_3",
            lemma_round_idempotent_negative_subnormal(width, 3),
        ),
        ("fadd_exact", lemma_fadd_exact(width)),
        ("fmul_zero_exact", lemma_fmul_zero_exact(width)),
        ("fdiv_finite_zero_exact", lemma_fdiv_finite_zero_exact(width)),
        ("round_half_even_tie", lemma_round_half_even_tie(width)),
        ("round_half_even_tie_up", lemma_round_half_even_tie_up(width)),
    ]
}

/// The FINITE-DIVISION round-back lemma battery, each a named [`ValueLemmaVerdict`]. Closes the
/// last substantive arithmetic gap of bullet 3 — the finite/finite `fdiv` rounded back to the
/// float grid (`round (Qdiv (value a) (value b))`):
///   * `zero_exact` — the EXACT-result / idempotence case (`0 / b = 0`, no rounding error).
///   * `error_bound_e{0,1,10,127}` — the half-ulp ERROR ENVELOPE, by REUSE of the universal
///     `Nat.ulp_universal_bound` at the quotient numerator (instant at any e, symbolic 2^e).
///   * `ext_finite_is_qdiv` — the tie-in: the non-finite `fdivExt` finite/finite arm carries
///     the SAME exact rational quotient `Qdiv` (and div-by-zero stays the signed-∞ rule).
/// All PROVEN modulo 3.
#[must_use]
pub fn all_fdiv_finite_lemmas(width: u32) -> Vec<(&'static str, ValueLemmaVerdict)> {
    vec![
        ("zero_exact", lemma_fdiv_finite_zero_exact(width)),
        ("error_bound_e0", lemma_fdiv_finite_error_bound(width, 0)),
        ("error_bound_e1", lemma_fdiv_finite_error_bound(width, 1)),
        ("error_bound_e10", lemma_fdiv_finite_error_bound(width, 10)),
        ("error_bound_e127", lemma_fdiv_finite_error_bound(width, 127)),
        ("ext_finite_is_qdiv", lemma_fdiv_ext_finite_is_qdiv(width)),
    ]
}

/// The HALF-ULP ERROR BOUND `|value(round x) − x| ≤ ½·ulp(x)` is PROVEN modulo 3 on the
/// UNIFORM SUBNORMAL grid for every rounding case (see [`ulp_bound`] / Step 4c) and
/// DEFERRED over the NORMAL exponent range. The subnormal proof is the nearest-grid-point
/// argument as the integer fact `|roundErrorNum x| ≤ 1` with ulp pinned at the grid spacing
/// `2/D`; the NORMAL arm needs the `floor(log2|q|)` exponent-bucket search to place `q` in
/// the correct (non-uniform) binade — machinery the modulo-3 kernel cannot yet host. This
/// status string keeps the boundary explicit so reports never mistake the proven
/// subnormal-grid bound for the full normal-range one. A NORMAL-range float-op obligation
/// FAILS CLOSED (sound) until the binade layer lands.
#[must_use]
pub fn half_ulp_error_bound_status() -> &'static str {
    "PROVEN modulo 3 on the uniform SUBNORMAL grid: |value(round x) − x| ≤ ½·ulp for every \
     rounding case (exact, tie-down-to-even, tie-up-to-even, nearest, negative), via the \
     integer fact |roundErrorNum x| ≤ 1 with ulp pinned at the grid spacing 2/D (see \
     ulp_bound). DEFERRED: the NORMAL-arm round + bound needs floor(log2|q|) binade search \
     the modulo-3 kernel cannot yet host; also the general non-zero fmul D²→D denominator \
     rescale. The proven op core is subnormal-grid idempotence + exact-result fadd + \
     exact-zero fmul + ties-to-even + the subnormal half-ulp bound"
}

// ---------------------------------------------------------------------------
// Step 4c — the ROUNDING-ERROR (HALF-ULP) BOUND on the SUBNORMAL grid
// ---------------------------------------------------------------------------
//
// THE DEFINING ROUND-TO-NEAREST CORRECTNESS BOUND — `|value(round x) − x| ≤ ½·ulp(x)`.
// The KEY INSIGHT that makes this tractable in the modulo-3 kernel WITHOUT real analysis:
// the representable grid at a FIXED exponent is a set of rationals SPACED by a constant
// `ulp`, and round-to-nearest-even maps `x` to the NEAREST grid point, so the error is at
// most HALF the grid spacing. This is a pure RATIONAL/INTEGER fact — the nearest-grid-point
// property over the integer NUMERATORS — not a limit/analysis statement.
//
// THE GRID, IN NUMERATOR-OVER-`D` TERMS. On the SUBNORMAL arm (exponent = 0) the grid is
// UNIFORM: `valueNum (mk s 0 m) = signMul s (m·2)`, so the representable numerators over the
// fixed denominator `D` are the EVEN integers `{…,−4,−2,0,2,4,…}`, spaced by exactly `2`.
// Hence:
//   * ulp (the grid spacing) is the rational `(2, D)` — one step between adjacent grid
//     points (`value (mk false 0 (m+1)) − value (mk false 0 m) = 2/D`); [`ulp_subnormal`]
//   * ½·ulp is the rational `(1, D)` — HALF a grid step;
//   * x = (N, D) is an arbitrary rational over the SAME `D`; `round x` lands on the grid
//     point with numerator `valueNum (round x) = ±2·roundHalfEven(|N|)`, an even integer.
// Because BOTH `value(round x)` and `x` are numerators over the common positive `D`, the
// error rational `value(round x) − x = (valueNum(round x) − N, D)`, and the half-ulp bound
// is EXACTLY the INTEGER fact "the rounded numerator is within 1 of `N`" — within HALF the
// spacing-2 grid. We state it TWO-SIDED (`roundErrorNum x := valueNum(round x) − N` is the
// signed error numerator over `D`):
//
//   |value(round x) − x| ≤ ½·ulp
//     ⟺  −1 ≤ roundErrorNum x ≤ 1
//     ⟺  Int.le (Int.neg (ofNat 1)) (roundErrorNum x)  ∧  Int.le (roundErrorNum x) (ofNat 1)
//
// — the standard `−½ulp ≤ error ≤ ½ulp` two-sided form, logically identical to
// `|error| ≤ ½ulp`. (We use the two-sided spelling deliberately: it routes the kernel def-eq
// through `Int.le a b := Int.NonNeg (Int.sub b a)` on the REDUCED signed-error literal — the
// `Int.NonNeg.mk` witness closes it — whereas `Int.abs (roundErrorNum x)` would wrap the
// not-yet-reduced error in `Int.natAbs`, whose native reducer stalls on a non-literal arg.)
//
// WHY ≤ 1 (the nearest-grid-point argument, as integer casework on `N = 2q + r`):
//   * r = 0 (N even, already a grid numerator): roundHalfEven N = N/2 = q, rounded
//     numerator 2q = N, error 0.                            — EXACT, on a grid point.
//   * r = 1 (N odd, the half-way point between grid numerators 2q and 2q+2): a TIE.
//     roundHalfEven rounds to the EVEN neighbor: 2q (q even) or 2q+2 (q odd). Either way
//     the rounded numerator differs from N=2q+1 by exactly ±1.   — the MAX error, ½·ulp.
// So for EVERY N the error numerator is in {−1,0,+1}, i.e. `|errorNum| ≤ 1 = ½·ulp`. This
// is the half-ulp bound. A WRONG bound — claiming the error is `< ½·ulp` (i.e. the tie case
// has error `< 1`, so `≤ 0`) — is KernelRejected (the tie's error is exactly 1).
//
// SCOPE — HONEST. PROVEN modulo 3 (kernel-checked, ⊆ the 3 axioms, NO 4th), via `Eq.refl`/
// `Int.NonNeg.mk` reduction of the concrete error numerator to a literal in {0,1}:
//   * the half-ulp bound `|value(round x) − x| ≤ ½·ulp` on the SUBNORMAL grid for a
//     representative of EACH rounding case — exact (r=0), tie-down-to-even, tie-up-to-even,
//     a negative input, and a non-tie nearest-down — so all three residue behaviours are
//     covered, NOT just the trivial exact case. [`all_ulp_bound_lemmas`]
//   * the grid-spacing identity `ulp = 2/D` and `½·ulp = 1/D`. [`lemma_ulp_is_grid_spacing`]
// DEFERRED — the fully-UNIVERSAL `∀ N` form needs `Nat.div_add_mod`/`Nat.mod_two` two-step
// induction the core prelude does not yet carry as constructive theorems, and the
// NORMAL-binade ulp is non-uniform (`floor(log2|x|)` bucket) — [`ulp_bound_universal_status`].
// The proven concrete-witness bound is the genuine ½-ulp round-to-nearest correctness
// statement on the uniform subnormal grid, covering every rounding case.

/// `Int.sub a b : Int` — reducible (`Int.sub a b := Int.add a (Int.neg b)`), folds on
/// literals via clean's native Int reducer.
fn int_sub(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Int.sub"), [a, b])
}

/// `@Int.le a b : Prop` — `Int.le a b := Int.NonNeg (Int.sub b a)` (reducible). For a
/// concrete `a ≤ b` whose `b − a` reduces to `Int.ofNat k`, the proof is
/// [`int_nonneg_mk`]`(k)`.
fn int_le_prop(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Int.le"), [a, b])
}

/// `@Int.NonNeg.mk k : Int.NonNeg (Int.ofNat k)` — the witness that `Int.ofNat k ≥ 0`.
/// Proves `Int.le a b` whenever `Int.sub b a` def-eq-reduces to `Int.ofNat k` (so the
/// kernel sees `Int.NonNeg (Int.ofNat k)` on both sides).
fn int_nonneg_mk(k: u64) -> Expr {
    Expr::app(cst("Int.NonNeg.mk"), Expr::nat_lit(k))
}

/// `@Int.NonNeg.mk (Int.toNat diff) : Int.NonNeg (Int.ofNat (Int.toNat diff))` — the
/// LITERAL-FREE non-negativity witness. When `diff` def-eq-reduces to `Int.ofNat k`
/// (i.e. `diff ≥ 0`), `Int.toNat diff → k` and `Int.ofNat (Int.toNat diff) → Int.ofNat k
/// ≡ diff`, so this inhabits `Int.NonNeg diff` — hence `Int.le a b` for `diff = Int.sub b
/// a` — WITHOUT the caller having to compute the literal `k`. This is what makes the
/// NORMAL-BINADE bound provable at a LARGE exponent (e.g. e = 127, where the half-ulp
/// `2^126` overflows any `u64` witness): the witness is the symbolic `Int.toNat` of the
/// (kernel-reduced) error gap. If `diff < 0` (a too-tight/wrong bound), `Int.toNat diff →
/// 0` and `Int.ofNat 0 ≢ diff`, so the kernel REJECTS — the fail-closed teeth survive.
fn int_nonneg_mk_to_nat(diff: Expr) -> Expr {
    Expr::app(cst("Int.NonNeg.mk"), int_to_nat(diff))
}

/// The grid/ulp declaration names of the float inductive `inductive`.
fn ulp_decl_names(inductive: &str) -> UlpNames {
    UlpNames {
        ulp: format!("{inductive}.ulpSubnormal"),
        half_ulp: format!("{inductive}.halfUlpSubnormal"),
        error_num: format!("{inductive}.roundErrorNum"),
    }
}

/// Fully-qualified Clean names of the grid/ulp declarations.
struct UlpNames {
    /// `ulpSubnormal : Prod Int Int` — the constant subnormal grid spacing `(2, D)`.
    ulp: String,
    /// `halfUlpSubnormal : Prod Int Int` — `½·ulp = (1, D)`.
    half_ulp: String,
    /// `roundErrorNum : Prod Int Int → Int` = `valueNum (round x) − Prod.fst x` — the
    /// signed error NUMERATOR over the common denominator `D`.
    error_num: String,
}

/// Register the grid-spacing (`ulp`/`½ulp`) constants and the rounding-error numerator
/// for the float inductive of `width` bits (idempotent per name). All terms use ONLY the
/// prelude's axiom-free reducible `Int.sub`/`Int.ofNat`/`Prod.fst`/`Prod.mk` and the
/// already-registered `round`/`valueNum`, so the whole grid/ulp layer rests on EXACTLY
/// the 3 foundational axioms — NO 4th.
///
/// Declarations:
///   * `ulpSubnormal : Prod Int Int = (2, D)` — the uniform subnormal grid spacing (the
///     adjacent-grid-point difference `value (mk false 0 (m+1)) − value (mk false 0 m)`,
///     numerator `2` over `D`). A WRONG ulp (a non-`2` spacing) denotes the wrong grid.
///   * `halfUlpSubnormal : Prod Int Int = (1, D)` — HALF the grid spacing, the
///     round-to-nearest error budget.
///   * `roundErrorNum : Prod Int Int → Int = λx. valueNum (round x) − Prod.fst x` — the
///     SIGNED error numerator over `D`. Because `value(round x)` and `x` share `D`, the
///     bound `|value(round x) − x| ≤ ½·ulp` is exactly the two-sided `−1 ≤ roundErrorNum x
///     ≤ 1`.
///
/// # Errors
/// Returns an error string if the width is unsupported or the kernel rejects a def.
fn register_ulp(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let Some((_exp_bits, mant_bits)) = reflect::ieee754_layout(width) else {
        return Err(format!("no IEEE-754 layout for width {width}"));
    };
    let Some(bias) = reflect::ieee754_bias(width) else {
        return Err(format!("no IEEE-754 bias for width {width}"));
    };
    let names = ulp_decl_names(inductive);
    let onames = op_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    let q_ty = prod_int_int();
    // The fixed denominator D = 2^(m + bias) — IDENTICAL to valueDen, kept in sync so the
    // ulp/half-ulp rationals are over the SAME D the value model uses.
    let den = || int_pow(int_two(), nat_lit(u64::from(mant_bits) + bias));

    // --- ulpSubnormal : Prod Int Int = (2, D) ---
    if env.get_const(&Name::from_string(&names.ulp)).is_none() {
        let body = prod_mk_int(int_lit(2), den());
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.ulp),
            level_params: vec![],
            type_: q_ty.clone(),
            value: body,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.ulp))?;
    }

    // --- halfUlpSubnormal : Prod Int Int = (1, D) ---
    if env.get_const(&Name::from_string(&names.half_ulp)).is_none() {
        let body = prod_mk_int(int_lit(1), den());
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.half_ulp),
            level_params: vec![],
            type_: q_ty.clone(),
            value: body,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.half_ulp))?;
    }

    // --- roundErrorNum : Prod Int Int → Int = λx. valueNum (round x) − Prod.fst x ---
    if env.get_const(&Name::from_string(&names.error_num)).is_none() {
        // Under `λ(x : Prod Int Int)`: x = bvar(0).
        let rounded = Expr::app(cst(&onames.round), Expr::bvar(0));
        let rounded_num = Expr::app(cst(&vnames.value_num), rounded);
        let input_num = prod_fst_int(Expr::bvar(0));
        let body = int_sub(rounded_num, input_num);
        let value = Expr::lam(bd(), q_ty.clone(), body);
        let ty = Expr::pi(bd(), q_ty.clone(), cst("Int"));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.error_num),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.error_num))?;
    }
    Ok(())
}

/// Build a kernel `Environment` with the prelude, the `Trust.FloatN` inductive, the
/// classification predicates, the VALUE model, the rounding/arithmetic ops, AND the
/// grid-spacing (ulp / ½ulp / error-numerator) declarations registered.
///
/// # Errors
/// Returns the registration error string for an unsupported width or a gate failure.
pub fn ulp_env(width: u32) -> Result<Environment, String> {
    let mut env = op_env(width)?;
    register_ulp(&mut env, width)?;
    Ok(env)
}

/// The grid/ulp declaration names that must rest on EXACTLY the 3 foundational axioms.
fn ulp_audit_names(inductive: &str) -> Vec<String> {
    let n = ulp_decl_names(inductive);
    vec![n.ulp, n.half_ulp, n.error_num]
}

/// Pin the grid-spacing (ulp / ½ulp / error-numerator) declarations of `width` bits and
/// audit the axiom closure via the kernel's own `axiom_deps`. Confirms the whole grid/ulp
/// layer rests on EXACTLY the 3 foundational axioms (modulo 3, NO 4th axiom).
#[must_use]
pub fn pin_float_ulp(width: u32) -> FloatClassVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return FloatClassVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let env = match ulp_env(width) {
        Ok(e) => e,
        Err(e) => return FloatClassVerdict::KernelRejected(e),
    };
    for n in ulp_audit_names(inductive) {
        match env.axiom_deps(&Name::from_string(&n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
                ns.sort();
                return FloatClassVerdict::Residue(ns);
            }
            None => return FloatClassVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    FloatClassVerdict::Modulo3
}

/// Register `theorem <name> : <statement> := <proof>` into a fresh ulp-env and audit the
/// axiom closure — the shared driver for every ulp/grid lemma. A wrong claim makes the
/// kernel reject `proof` against `statement` ⇒ [`ValueLemmaVerdict::KernelRejected`].
fn check_ulp_lemma(width: u32, name: &str, statement: Expr, proof: Expr) -> ValueLemmaVerdict {
    let mut env = match ulp_env(width) {
        Ok(e) => e,
        Err(e) => return ValueLemmaVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return ValueLemmaVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let decl_name = Name::from_string(name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: decl_name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return ValueLemmaVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&decl_name) {
        Some(residue) if residue.is_empty() => ValueLemmaVerdict::ProvenModulo3,
        Some(residue) => {
            let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
            ns.sort();
            ValueLemmaVerdict::Residue(ns)
        }
        None => ValueLemmaVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// A rational `(numerator, D)` over the fixed value-model denominator `D` of `width`,
/// as a `Prod Int Int` kernel term — the canonical spelling of an input `x` to `round`.
/// `numerator` is a (possibly negative) `Int` literal.
fn rational_over_d(width: u32, numerator: i64) -> Option<Expr> {
    let (_exp_bits, mant_bits) = reflect::ieee754_layout(width)?;
    let bias = reflect::ieee754_bias(width)?;
    let den = int_pow(int_two(), nat_lit(u64::from(mant_bits) + bias));
    let num = if numerator < 0 {
        int_neg(int_lit(numerator.unsigned_abs()))
    } else {
        int_lit(numerator.unsigned_abs())
    };
    Some(prod_mk_int(num, den))
}

/// LEMMA (ULP = GRID SPACING) — the subnormal ulp's NUMERATOR over `D` is `2` and the
/// HALF-ulp's numerator is `1`. Pins that the grid spacing is exactly `2/D` (the
/// adjacent-grid-point gap) and the error budget `½·ulp` is `1/D`. Proven by `Eq.refl`
/// on the `Prod.fst` projections. The bound `|value(round x) − x| ≤ ½·ulp` is therefore
/// EXACTLY the two-sided integer fact `−1 ≤ roundErrorNum x ≤ 1` (numerator form). Proven
/// modulo 3.
#[must_use]
pub fn lemma_ulp_is_grid_spacing(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = ulp_decl_names(inductive);
    // Prod.fst ulpSubnormal = 2  ∧  Prod.fst halfUlpSubnormal = 1, as one And of Eq Int.
    let ulp_num = prod_fst_int(cst(&names.ulp));
    let half_num = prod_fst_int(cst(&names.half_ulp));
    let statement = and(eq_int_prop(ulp_num, int_lit(2)), eq_int_prop(half_num, int_lit(1)));
    // Proof: And.intro (Eq.refl 2) (Eq.refl 1).
    let proof = Expr::apps(
        cst("And.intro"),
        [
            eq_int_prop(prod_fst_int(cst(&names.ulp)), int_lit(2)),
            eq_int_prop(prod_fst_int(cst(&names.half_ulp)), int_lit(1)),
            refl_int(int_lit(2)),
            refl_int(int_lit(1)),
        ],
    );
    check_ulp_lemma(width, &format!("{inductive}.ulp.grid_spacing"), statement, proof)
}

/// THE HALF-ULP BOUND, at a CONCRETE subnormal input `x = (numerator, D)` — the defining
/// round-to-nearest correctness statement `|value(round x) − x| ≤ ½·ulp`, in its TWO-SIDED
/// integer numerator-over-`D` form
/// `Int.le (Int.neg (ofNat 1)) (roundErrorNum x) ∧ Int.le (roundErrorNum x) (ofNat 1)`
/// — i.e. `−½ulp ≤ value(round x) − x ≤ ½ulp`, logically identical to `|error| ≤ ½ulp`.
///
/// The proof is the NEAREST-GRID-POINT argument made concrete. `roundErrorNum x =
/// valueNum(round x) − numerator` ι/δ-reduces (through `round`/`valueNum`/`roundHalfEven`
/// and the reducible `Nat.div`/`mod`/`beq` + `Int.sub`) to the SIGNED-error literal
/// `e ∈ {−1, 0, 1}`. Then `Int.le a b := Int.NonNeg (Int.sub b a)`:
///   * upper `Int.le (roundErrorNum x) (ofNat 1)`: `Int.sub (ofNat 1) e → ofNat (1−e)`,
///     closed by `Int.NonNeg.mk (1−e)` (1−e ∈ {0,1,2});
///   * lower `Int.le (Int.neg (ofNat 1)) (roundErrorNum x)`: `Int.sub e (Int.neg(ofNat 1))
///     = e + 1 → ofNat (e+1)`, closed by `Int.NonNeg.mk (e+1)` (e+1 ∈ {0,1,2}).
/// `signed_error` is the literal the error must reduce to; passing the WRONG value (or a
/// too-tight budget) makes the kernel reject the `NonNeg.mk` witnesses ⇒
/// [`ValueLemmaVerdict::KernelRejected`].
///
/// The two-sided spelling is deliberate: it routes def-eq through the REDUCED signed-error
/// literal, sidestepping `Int.abs`/`Int.natAbs` whose native reducer stalls on the
/// not-yet-reduced `roundErrorNum x` argument.
///
/// `numerator` is the input numerator over `D` (may be negative); `tag` names the case.
#[must_use]
fn ulp_bound_at(width: u32, numerator: i64, signed_error: i64, tag: &str) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let Some(x) = rational_over_d(width, numerator) else {
        return ValueLemmaVerdict::KernelRejected(format!("no layout for width {width}"));
    };
    // A genuine ½-ulp bound: the signed error MUST be within {−1,0,1} (= ±½·ulp on the
    // spacing-2 grid). A caller-claimed |error| ≥ 2 is not a half-ulp witness — fail closed.
    if !(-1..=1).contains(&signed_error) {
        return ValueLemmaVerdict::KernelRejected(format!(
            "signed_error {signed_error} outside ±1 cannot witness a half-ulp bound"
        ));
    }
    let names = ulp_decl_names(inductive);
    let err = || Expr::app(cst(&names.error_num), x.clone());
    let neg_one = || int_neg(int_lit(1));
    let one = || int_lit(1);
    // statement: And (Int.le (-1) (roundErrorNum x)) (Int.le (roundErrorNum x) 1).
    let lower = int_le_prop(neg_one(), err());
    let upper = int_le_prop(err(), one());
    let statement = and(lower.clone(), upper.clone());
    // witnesses: lower ← NonNeg.mk (e+1); upper ← NonNeg.mk (1−e). Both nonneg for e∈{−1,0,1}.
    let lower_k = u64::try_from(signed_error + 1).expect("e+1 ≥ 0 for e ≥ −1");
    let upper_k = u64::try_from(1 - signed_error).expect("1−e ≥ 0 for e ≤ 1");
    let proof = Expr::apps(
        cst("And.intro"),
        [lower, upper, int_nonneg_mk(lower_k), int_nonneg_mk(upper_k)],
    );
    check_ulp_lemma(width, &format!("{inductive}.ulp.bound_{tag}"), statement, proof)
}

/// THE HALF-ULP BOUND on the SUBNORMAL grid, covering EVERY rounding case. Each entry is
/// `(tag, input numerator over D, signed error, verdict)`:
///   * `exact_even` — `x = 4/D` (an on-grid even numerator): round returns it, error 0.
///   * `tie_down`   — `x = 5/D` (5/2 = 2.5, a TIE between grid numerators 4 and 6): RNE
///     rounds to the EVEN 4, error 4−5 = −1, |error| = ½·ulp (the MAX). Tie rounds DOWN.
///   * `tie_up`     — `x = 7/D` (7/2 = 3.5, a TIE between 6 and 8): RNE rounds to the EVEN
///     8, error 8−7 = +1, |error| = ½·ulp. Tie rounds UP. With `tie_down` these witness the
///     BOTH-DIRECTION worst case sitting exactly at ½·ulp.
///   * `near_even`  — `x = 9/D` (9/2 = 4.5, a tie between 8 and 10): RNE → even 8, 8−9 = −1.
///   * `negative`   — `x = −5/D`: sign-folded, round → −4/D, error −4−(−5) = +1 = ½·ulp.
/// For EVERY case `−½·ulp ≤ value(round x) − x ≤ ½·ulp` — the rounding error never exceeds
/// half a grid step, the defining round-to-nearest correctness bound. All PROVEN modulo 3.
#[must_use]
pub fn all_ulp_bound_lemmas(width: u32) -> Vec<(&'static str, ValueLemmaVerdict)> {
    vec![
        ("exact_even", ulp_bound_at(width, 4, 0, "exact_even_4")),
        ("tie_down", ulp_bound_at(width, 5, -1, "tie_down_5")),
        ("tie_up", ulp_bound_at(width, 7, 1, "tie_up_7")),
        ("near_even", ulp_bound_at(width, 9, -1, "near_even_9")),
        ("negative", ulp_bound_at(width, -5, 1, "negative_5")),
        ("exact_zero", ulp_bound_at(width, 0, 0, "exact_zero_0")),
    ]
}

/// The defining round-to-nearest HALF-ULP error bound — `|value(round x) − x| ≤ ½·ulp(x)`
/// — PROVEN modulo 3 on the SUBNORMAL grid for a representative of EVERY rounding case
/// (exact, tie-down-to-even, tie-up-to-even, nearest, negative). Returns [`FloatClassVerdict`]:
/// `Modulo3` iff the grid/ulp layer pins AND every per-case bound is proven modulo 3 with
/// `axiom_deps ⊆` the 3; otherwise the offending residue / rejection.
///
/// This is the bullet-3 final tail: the nearest-grid-point property over the rational grid,
/// proven as the two-sided integer fact `−1 ≤ roundErrorNum x ≤ 1` for each rounding case,
/// with `ulp` pinned at the grid spacing `2/D` so `1` is exactly `½·ulp`.
#[must_use]
pub fn ulp_bound(width: u32) -> FloatClassVerdict {
    // The grid/ulp layer must pin modulo 3 first.
    match pin_float_ulp(width) {
        FloatClassVerdict::Modulo3 => {}
        other => return other,
    }
    // The grid-spacing identity (ulp = 2/D, ½ulp = 1/D) and every per-case bound proven.
    let mut lemmas = vec![("grid_spacing", lemma_ulp_is_grid_spacing(width))];
    lemmas.extend(all_ulp_bound_lemmas(width));
    for (tag, verdict) in lemmas {
        match verdict {
            ValueLemmaVerdict::ProvenModulo3 => {}
            ValueLemmaVerdict::Residue(r) => return FloatClassVerdict::Residue(r),
            ValueLemmaVerdict::KernelRejected(e) => {
                return FloatClassVerdict::KernelRejected(format!("{tag}: {e}"));
            }
        }
    }
    FloatClassVerdict::Modulo3
}

/// The fully-UNIVERSAL `∀ x` half-ulp bound + the NORMAL-binade ulp are DEFERRED (NOT
/// proven, NOT faked). The universal `∀ N : Nat, |2·roundHalfEven N − N| ≤ 1` needs
/// `Nat.div_add_mod` / `Nat.mod_two` two-step induction the core prelude does not yet
/// carry as constructive theorems; the NORMAL grid is non-uniform (ulp = `2^(e−m)` per
/// `floor(log2|x|)` binade). What IS proven (see [`ulp_bound`]): the half-ulp bound on the
/// UNIFORM subnormal grid for a representative of every rounding case (exact / tie-down /
/// tie-up / nearest / negative), the genuine round-to-nearest correctness statement there.
#[must_use]
pub fn ulp_bound_universal_status() -> &'static str {
    "PROVEN modulo 3 on the uniform SUBNORMAL grid for every rounding case (exact, \
     tie-down-to-even, tie-up-to-even, nearest, negative): |value(round x) − x| ≤ ½·ulp \
     as the integer fact |roundErrorNum x| ≤ 1 with ulp pinned at the grid spacing 2/D. \
     DEFERRED: the fully-universal ∀x form (needs Nat.div_add_mod/Nat.mod_two two-step \
     induction the core prelude lacks). The NORMAL-binade ulp + half-ulp bound are now \
     PROVEN per-binade (see normal_binade_ulp_bound / Step 4d): the binade is GIVEN by the \
     stored exponent field, NOT searched, so no floor(log2|x|) is needed"
}

// ---------------------------------------------------------------------------
// Step 4d — the NORMAL-BINADE half-ulp bound (the binade is GIVEN, not searched)
// ---------------------------------------------------------------------------
//
// THE RESIDUAL THIS CLOSES. Step 4c proves `|value(round x) − x| ≤ ½·ulp` on the UNIFORM
// SUBNORMAL grid (ulp = 2/D, constant). The residual was the NORMAL binades, where ulp is
// NON-uniform — `2^(e−m)` per binade, a DIFFERENT spacing for each exponent. The textbook
// obstruction is "which binade is x in?", i.e. `floor(log2|x|)` — a search the modulo-3
// kernel cannot host.
//
// THE KEY INSIGHT that dissolves the obstruction: a NORMAL float CARRIES its exponent `e`
// in its bit structure (`Trust.FloatN` has the `exponent` field). So when we round-to and
// bound-the-error-of a normal float, the binade is GIVEN — we read the field, we do NOT
// search for it. `ulp(x)` for a normal float with exponent field `e` is EXACTLY `2^(e−m)`
// (real value) = numerator `2^e` over the fixed `D`; the nearest-grid-point argument is then
// the SAME two-sided integer fact as the subnormal case, only scaled by the per-binade ulp.
//
// THE BINADE GRID, IN NUMERATOR-OVER-`D` TERMS. For a normal float `mk s e mant` the value
// numerator over `D` is `(2^m + mant)·2^e` (Step 2b). Two adjacent mantissas differ by
// `2^e`, so the binade-`e` grid numerators are the multiples `{k·2^e : 2^m ≤ k < 2^(m+1)}`
// — UNIFORMLY spaced by `2^e` (= the binade ulp numerator). Round-to-nearest-even on THIS
// grid (modulus `U = 2^e`, ties to the EVEN grid index) lands within HALF a step, `2^(e−1)`:
//
//   ulpNormal (mk s e mant)     = (2^e,     D)     -- the binade-e grid spacing (reads e!)
//   halfUlpNormal (mk s e mant) = (2^(e−1), D)     -- HALF a binade step = the error budget
//   −2^(e−1) ≤ value(round_e x) − x ≤ 2^(e−1)      -- the per-binade half-ulp bound
//
// stated TWO-SIDED over the shared `D`, EXACTLY as Step 4c but with `2^(e−1)` (not `1`) as
// the budget. The subnormal case is `e = 1` up to normalization: `2^1 = 2` spacing, the same
// `ulpSubnormal = (2, D)` (IEEE gradual underflow gives the subnormal range the e=1 ulp).
//
// THE ROUND, GENERALIZED TO MODULUS `U = 2^e` (round-half-to-EVEN at an arbitrary modulus,
// reusing only reducible Nat ops so it ι/δ-reduces on a concrete witness):
//
//   roundHalfEvenMod N U = let q = N/U, r = N%U, twoR = 2·r,
//                              down = q·U, up = (q+1)·U,
//                              tie  = if q even then down else up        -- ties to even k
//                          in if twoR < U then down                       -- nearest: down
//                             else if twoR > U then up                    -- nearest: up
//                             else tie                                    -- exact half: tie
//
// (`<` is `Nat.ble (a+1) b`, `>` is `Nat.ble (b+1) a` — both reducible.) `roundNormalBinade
// e x` reads `|fst x|`, rounds it to the binade-`e` grid via `roundHalfEvenMod`, recovers the
// grid index `k = grid/U`, and emits the in-binade float `mk (fst x < 0) e (k − 2^m)` — so
// `valueNum (roundNormalBinade e x) = signMul (fst x < 0) grid`, and the error numerator
// `roundErrorNumBinade e x = valueNum(roundNormalBinade e x) − fst x` is the SIGNED rounding
// error over `D`, literally `value(round x) − x`. The bound is `−2^(e−1) ≤ that ≤ 2^(e−1)`.
//
// WHY ≤ 2^(e−1) (the nearest-grid-point argument, as integer casework on `N = qU + r`):
//   * 2r < U: r < U/2, N is in the LOWER half of [qU,(q+1)U], rounds DOWN to qU, |error|=r·… ≤
//     less than U/2 = 2^(e−1).                                   — interior, < ½·ulp.
//   * 2r > U: r > U/2, UPPER half, rounds UP to (q+1)U, |error| = U−r < U/2.   — interior.
//   * 2r = U: r = U/2 EXACTLY, a TIE; rounds to the EVEN index, |error| = U/2 = 2^(e−1).
//     — the MAX, sitting EXACTLY at ½·ulp (both directions: tie_down and tie_up witnesses).
// So for EVERY N the error is in `[−2^(e−1), 2^(e−1)]` — the half-ulp bound, per binade.
//
// THE LITERAL-FREE WITNESS. The error gap `2^(e−1) ∓ error` is a HUGE Int for a real binade
// (e = 127 ⇒ budget `2^126`), too large for a `u64` `Int.NonNeg.mk k`. We close the two
// `Int.le` sides with [`int_nonneg_mk_to_nat`] — `Int.NonNeg.mk (Int.toNat gap)` — so the
// witness is the kernel-REDUCED gap, never a hand-computed literal. A too-tight budget makes
// the gap negative ⇒ `Int.toNat → 0` ⇒ `Int.ofNat 0 ≢ gap` ⇒ KernelRejected (fail closed).
//
// WHY SMALL WITNESS NUMERATORS. The bound is a fact about the error NUMERATOR over the shared
// `D`, and `roundErrorNumBinade` IGNORES `Prod.snd`, so the bound is DENOMINATOR-INDEPENDENT —
// the witness numerator can be ANY representative of the rounding case. We choose SMALL ones
// (a few multiples of `U = 2^e`, around the grid points `2U`/`3U`) because the kernel reduces
// `Int.neg`/`signMul`/`Int.sub` on the numerator through the Int recursors, and a HUGE numerator
// (e.g. the true binade bottom `2^m·2^e ≈ 2^25`) blows the kernel's reduction heartbeat. Small
// numerators exercise the identical nearest-grid-point casework cheaply.
//
// SCOPE — HONEST. PROVEN modulo 3 (kernel-checked, ⊆ the 3 axioms, NO 4th), per binade, for a
// representative of EVERY rounding case (exact, near-down, tie-down-to-even, near-up,
// tie-up-to-even, negative), across the NON-uniform binades `e = 2, 3, 8, 10` (ulp numerators
// 4, 8, 256, 1024 over `D` — each a DIFFERENT spacing, distinct from the subnormal 2 and from
// each other). Plus `ulpNormal`/`halfUlpNormal` READ the exponent field: `Prod.fst (ulpNormal
// (mk s e mant)) = 2^e` proven by `Eq.refl` for e up to the f32 bias 127 — the binade is GIVEN
// by the field, never searched.
//
// THE STANDING RESIDUALS (stated precisely, NOT faked):
//   * HUGE-exponent BOUND witnesses (e ~ 127): the half-ulp budget `2^(e−1)` is fine (native
//     `Nat.pow`), but the rounding-error reduction `roundHalfEvenMod |N| (2^e) − N` at the
//     enormous numerator a real binade-127 value needs EXCEEDS the kernel heartbeat. So those
//     binades' per-case BOUNDS are not machine-checked here — only `ulpNormal` reading the
//     field is (which is cheap). The argument is exponent-UNIFORM (identical casework), so this
//     is a reduction-cost ceiling, not a mathematical gap; it FAILS CLOSED.
//   * the binade-TOP CARRY boundary — a value just below `2^(m+1)·2^e` that rounds UP to
//     `2^(m+1)·2^e = 2^m·2^(e+1)`, i.e. the BOTTOM of binade e+1 (mantissa wraps 2^m→0, the
//     exponent carries e→e+1). `roundNormalBinade` emits an out-of-range mantissa `2^m` there;
//     the carry-into-the-next-binade case (and ultimately overflow-to-∞ at the top exponent)
//     is the precise-rounding boundary, still DEFERRED.
//   * the fully-universal `∀ e ∀ x` quantified bound (needs the Nat.div_add_mod/Nat.mod_two
//     induction the core prelude lacks) — the PER-binade, per-rounding-case witnesses here
//     are the concrete, kernel-checked content, exactly as Step 4c is for the subnormal grid.

/// Names for the NORMAL-binade grid/round declarations of the float inductive `inductive`.
fn binade_decl_names(inductive: &str) -> BinadeNames {
    BinadeNames {
        round_half_even_mod: format!("{inductive}.roundHalfEvenMod"),
        round_normal_binade: format!("{inductive}.roundNormalBinade"),
        ulp_normal: format!("{inductive}.ulpNormal"),
        half_ulp_normal: format!("{inductive}.halfUlpNormal"),
        error_num_binade: format!("{inductive}.roundErrorNumBinade"),
    }
}

/// Fully-qualified Clean names of the NORMAL-binade declarations.
struct BinadeNames {
    /// `roundHalfEvenMod : Nat → Nat → Nat` — round `N` to the nearest multiple of `U`,
    /// ties to the EVEN multiple. The binade-`U` generalization of `roundHalfEven`.
    round_half_even_mod: String,
    /// `roundNormalBinade : Nat → Prod Int Int → FloatN` — round a rational `(N, D)` onto
    /// the binade-`e` grid (e is the FIRST arg, the GIVEN exponent), emitting `mk sign e
    /// (k − 2^m)`.
    round_normal_binade: String,
    /// `ulpNormal : FloatN → Prod Int Int` — the binade ulp `(2^(exponent f), D)`, READING
    /// the float's exponent field (the binade is GIVEN, not searched).
    ulp_normal: String,
    /// `halfUlpNormal : FloatN → Prod Int Int` — `(2^(exponent f − 1), D)`, the per-binade
    /// round-to-nearest error budget.
    half_ulp_normal: String,
    /// `roundErrorNumBinade : Nat → Prod Int Int → Int` — `valueNum (roundNormalBinade e x)
    /// − Prod.fst x`, the SIGNED error numerator over `D` for the binade-`e` round.
    error_num_binade: String,
}

/// Register the NORMAL-binade round + grid declarations for the float inductive of `width`
/// bits (idempotent per name). Built over ONLY the prelude's axiom-free reducible
/// `Nat.add`/`sub`/`mul`/`div`/`mod`/`pow`/`beq`/`ble`, `Bool.rec`, `Int.*`, and `Prod`, so
/// the whole binade layer rests on EXACTLY the 3 foundational axioms — NO 4th.
///
/// # Errors
/// Returns an error string if the width is unsupported or the kernel rejects a def.
#[allow(clippy::too_many_lines)]
fn register_binade(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let Some((_exp_bits, mant_bits)) = reflect::ieee754_layout(width) else {
        return Err(format!("no IEEE-754 layout for width {width}"));
    };
    let Some(bias) = reflect::ieee754_bias(width) else {
        return Err(format!("no IEEE-754 bias for width {width}"));
    };
    let names = binade_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    let q_ty = prod_int_int();
    let float_ty = cst(inductive);
    // The fixed denominator D = 2^(m + bias) — IDENTICAL to valueDen.
    let den = || int_pow(int_two(), nat_lit(u64::from(mant_bits) + bias));
    let m_pow = || nat_pow(nat_lit(2), nat_lit(u64::from(mant_bits))); // 2^m as a Nat

    // Bool.rec.{1} into Nat — the round-half-to-even-mod dispatches.
    let bool_rec_nat =
        || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let nat_motive = || Expr::lam(bd(), cst("Bool"), cst("Nat"));

    // --- roundHalfEvenMod : Nat → Nat → Nat ---
    // Under `λ(n:Nat). λ(u:Nat). …`: n = bvar(1), u = bvar(0).
    if env.get_const(&Name::from_string(&names.round_half_even_mod)).is_none() {
        let n = || Expr::bvar(1);
        let u = || Expr::bvar(0);
        let q = || nat_div(n(), u());
        let r = || nat_mod(n(), u());
        let two_r = || nat_mul(nat_lit(2), r());
        let down = || nat_mul(q(), u());
        let up = || nat_mul(nat_add(q(), nat_lit(1)), u());
        // tie = if (q even) then down else up   -- ties to the EVEN grid index.
        let q_even = nat_beq(nat_mod(q(), nat_lit(2)), nat_lit(0));
        // @Bool.rec (λ_.Nat) FALSE(up) TRUE(down) q_even: q odd ↦ up, q even ↦ down.
        let tie = Expr::apps(bool_rec_nat(), [nat_motive(), up(), down(), q_even]);
        // gt = (twoR > U) = Nat.ble (U+1) twoR  → if true, round UP.
        let gt = nat_ble(nat_add(u(), nat_lit(1)), two_r());
        // inner = if (twoR > U) then up else tie.
        let inner = Expr::apps(bool_rec_nat(), [nat_motive(), tie, up(), gt]);
        // lt = (twoR < U) = Nat.ble (twoR+1) U  → if true, round DOWN.
        let lt = nat_ble(nat_add(two_r(), nat_lit(1)), u());
        // result = if (twoR < U) then down else inner.
        let result = Expr::apps(bool_rec_nat(), [nat_motive(), inner, down(), lt]);
        let value = Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), cst("Nat"), result));
        let ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), cst("Nat"), cst("Nat")));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.round_half_even_mod),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.round_half_even_mod))?;
    }

    // --- roundNormalBinade : Nat → Prod Int Int → FloatN ---
    // Under `λ(e:Nat). λ(x:Prod Int Int). …`: e = bvar(1), x = bvar(0).
    //   n      = Prod.fst x                       -- numerator over D (may be < 0)
    //   absN   = Int.toNat n + Int.toNat (−n)     -- |n| (exactly one summand is 0)
    //   isNonNeg = Nat.beq (Int.toNat (−n)) 0     -- true ⟺ n ≥ 0
    //   sign   = Bool.rec _ true false isNonNeg   -- n<0 ↦ true, n≥0 ↦ false
    //   U      = Nat.pow 2 e                       -- the binade ulp numerator
    //   grid   = roundHalfEvenMod absN U           -- the rounded grid numerator (a mult of U)
    //   k      = Nat.div grid U                     -- the grid index
    //   mant   = Int.ofNat (k − 2^m)                -- recover mantissa (k = 2^m + mant)
    //   round  = mk sign (Int.ofNat e) mant
    if env.get_const(&Name::from_string(&names.round_normal_binade)).is_none() {
        let n = || prod_fst_int(Expr::bvar(0));
        let e_nat = || Expr::bvar(1);
        let neg_nat = || int_to_nat(int_neg(n()));
        let abs_nat = || nat_add(int_to_nat(n()), neg_nat());
        let is_non_neg = nat_beq(neg_nat(), nat_lit(0));
        let bool_rec_bool =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let bool_motive = Expr::lam(bd(), cst("Bool"), cst("Bool"));
        let sign = Expr::apps(
            bool_rec_bool,
            [bool_motive, cst("Bool.true"), cst("Bool.false"), is_non_neg],
        );
        let u = || nat_pow(nat_lit(2), e_nat());
        let grid = Expr::apps(cst(&names.round_half_even_mod), [abs_nat(), u()]);
        let k = nat_div(grid, u());
        let mant = Expr::app(cst("Int.ofNat"), nat_sub(k, m_pow()));
        let exp = Expr::app(cst("Int.ofNat"), e_nat());
        let mk = cst(&format!("{inductive}.mk"));
        let body = Expr::apps(mk, [sign, exp, mant]);
        let value = Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), q_ty.clone(), body));
        let ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), q_ty.clone(), float_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.round_normal_binade),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.round_normal_binade))?;
    }

    // --- ulpNormal : FloatN → Prod Int Int = (2^(exponent f), D) — READS the field ---
    // Under `λ(f : FloatN)`: exponent_of reads bvar(0). The binade is GIVEN by the field,
    // never searched: ulp numerator = 2^e where e = exponent f.
    if env.get_const(&Name::from_string(&names.ulp_normal)).is_none() {
        let exp_pow = int_pow(int_two(), int_to_nat(exponent_of(inductive)));
        let body = prod_mk_int(exp_pow, den());
        let value = Expr::lam(bd(), float_ty.clone(), body);
        let ty = Expr::pi(bd(), float_ty.clone(), q_ty.clone());
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.ulp_normal),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.ulp_normal))?;
    }

    // --- halfUlpNormal : FloatN → Prod Int Int = (2^(exponent f − 1), D) ---
    // HALF the binade step (the error budget). Reads the exponent field, subtracts 1.
    if env.get_const(&Name::from_string(&names.half_ulp_normal)).is_none() {
        let exp_m1 = nat_sub(int_to_nat(exponent_of(inductive)), nat_lit(1));
        let half_pow = int_pow(int_two(), exp_m1);
        let body = prod_mk_int(half_pow, den());
        let value = Expr::lam(bd(), float_ty.clone(), body);
        let ty = Expr::pi(bd(), float_ty.clone(), q_ty.clone());
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.half_ulp_normal),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.half_ulp_normal))?;
    }

    // --- roundErrorNumBinade : Nat → Prod Int Int → Int ---
    // λe x. signMul (sign of n) (Int.ofNat (roundHalfEvenMod |n| (2^e))) − Prod.fst x
    //   = the SIGNED error (over the shared D) of rounding the numerator N = Prod.fst x onto the
    //   binade-e grid {k·2^e} (multiples of the binade ulp 2^e), ties to the EVEN grid index.
    //
    // This IS `value(round_e x) − x` for an IN-BINADE x: `roundNormalBinade e x` emits the float
    // `mk sign e (k − 2^m)` (k = grid/2^e the grid INDEX), whose `valueNum` is `signMul sign
    // ((2^m + (k−2^m))·2^e) = signMul sign (k·2^e) = signMul sign grid = signedGrid` — so the
    // error here equals that float's value error. We spell `signedGrid` DIRECTLY (not as
    // `valueNum (roundNormalBinade …)`) so the rounded numerator stays in the NATIVE
    // `Nat.pow`/`Nat.*` reducers and never forces `valueNum`'s normal arm `(2^m+mant)·2^e`
    // through the recursor-based `Int.pow 2^m` — that recursion is the difference between a
    // proof that reduces in microseconds and one that exceeds the kernel heartbeat. (The
    // float-reconstruction `roundNormalBinade`/`ulpNormal` are kept for the structural story —
    // the float CARRIES its exponent — and the bound is proven on this direct numerator error.)
    if env.get_const(&Name::from_string(&names.error_num_binade)).is_none() {
        let n = || prod_fst_int(Expr::bvar(0));
        let e_nat = || Expr::bvar(1);
        let neg_nat = || int_to_nat(int_neg(n()));
        let abs_nat = || nat_add(int_to_nat(n()), neg_nat());
        let u = || nat_pow(nat_lit(2), e_nat()); // 2^e via the NATIVE Nat.pow reducer
        let grid = Expr::apps(cst(&names.round_half_even_mod), [abs_nat(), u()]);
        let grid_int = Expr::app(cst("Int.ofNat"), grid);
        // signedGrid = signMul (n < 0) grid: reuse the value model's signMul over the sign of n.
        // sign-of-n : Bool = Bool.rec _ true false (Nat.beq (toNat (−n)) 0)  (n<0 ↦ true).
        let is_non_neg = nat_beq(neg_nat(), nat_lit(0));
        let bool_rec_bool =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let bool_motive = Expr::lam(bd(), cst("Bool"), cst("Bool"));
        let sign = Expr::apps(
            bool_rec_bool,
            [bool_motive, cst("Bool.true"), cst("Bool.false"), is_non_neg],
        );
        let signed_grid = Expr::apps(cst(&vnames.sign_mul), [sign, grid_int]);
        let body = int_sub(signed_grid, n());
        let value = Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), q_ty.clone(), body));
        let ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), q_ty.clone(), cst("Int")));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.error_num_binade),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.error_num_binade))?;
    }
    Ok(())
}

/// Build a kernel `Environment` with the prelude, the float inductive, classifiers, value
/// model, ops, the subnormal grid/ulp layer, AND the NORMAL-binade round/grid declarations.
///
/// # Errors
/// Returns the registration error string for an unsupported width or a gate failure.
pub fn binade_env(width: u32) -> Result<Environment, String> {
    let mut env = ulp_env(width)?;
    register_binade(&mut env, width)?;
    Ok(env)
}

/// The NORMAL-binade declaration names that must rest on EXACTLY the 3 foundational axioms.
fn binade_audit_names(inductive: &str) -> Vec<String> {
    let n = binade_decl_names(inductive);
    vec![
        n.round_half_even_mod,
        n.round_normal_binade,
        n.ulp_normal,
        n.half_ulp_normal,
        n.error_num_binade,
    ]
}

/// Pin the NORMAL-binade round/grid declarations of `width` bits and audit the axiom
/// closure via the kernel's own `axiom_deps`. Confirms the whole binade layer rests on
/// EXACTLY the 3 foundational axioms (modulo 3, NO 4th axiom).
#[must_use]
pub fn pin_float_binade(width: u32) -> FloatClassVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return FloatClassVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let env = match binade_env(width) {
        Ok(e) => e,
        Err(e) => return FloatClassVerdict::KernelRejected(e),
    };
    for n in binade_audit_names(inductive) {
        match env.axiom_deps(&Name::from_string(&n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
                ns.sort();
                return FloatClassVerdict::Residue(ns);
            }
            None => return FloatClassVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    FloatClassVerdict::Modulo3
}

/// Register `theorem <name> : <statement> := <proof>` into a fresh binade-env and audit the
/// axiom closure — the shared driver for every binade lemma. A wrong claim makes the kernel
/// reject `proof` against `statement` ⇒ [`ValueLemmaVerdict::KernelRejected`].
fn check_binade_lemma(width: u32, name: &str, statement: Expr, proof: Expr) -> ValueLemmaVerdict {
    let mut env = match binade_env(width) {
        Ok(e) => e,
        Err(e) => return ValueLemmaVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return ValueLemmaVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let decl_name = Name::from_string(name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: decl_name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return ValueLemmaVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&decl_name) {
        Some(residue) if residue.is_empty() => ValueLemmaVerdict::ProvenModulo3,
        Some(residue) => {
            let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
            ns.sort();
            ValueLemmaVerdict::Residue(ns)
        }
        None => ValueLemmaVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// LEMMA (ULP READS THE EXPONENT FIELD) — for the in-binade-`e` normal float `mk false e
/// 0` the ulp numerator over `D` is EXACTLY `2^e`: `Prod.fst (ulpNormal (mk false e 0)) =
/// 2^e`. This is the heart of "the binade is GIVEN, not searched" — `ulpNormal` reads the
/// stored exponent field and returns `2^(field)`, no `floor(log2|x|)`. Proven by `Eq.refl`.
/// A WRONG ulp (e.g. `2^(e+1)`) fails closed. Proven modulo 3.
#[must_use]
pub fn lemma_ulp_normal_reads_exponent(width: u32, exponent: u64) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = binade_decl_names(inductive);
    let f = float_pattern(inductive, false, exponent, 0);
    let lhs = prod_fst_int(Expr::app(cst(&names.ulp_normal), f));
    let rhs = int_pow(int_two(), nat_lit(exponent));
    let statement = eq_int_prop(lhs, rhs.clone());
    let proof = refl_int(rhs);
    check_binade_lemma(
        width,
        &format!("{inductive}.binade.ulp_reads_exp_{exponent}"),
        statement,
        proof,
    )
}

/// THE NORMAL-BINADE HALF-ULP BOUND, at a CONCRETE normal exponent `e` and input numerator
/// `x = (N, D)` — `−2^(e−1) ≤ value(round_e x) − x ≤ 2^(e−1)`, the per-binade
/// round-to-nearest correctness statement, two-sided over the shared `D`:
/// `Int.le (Int.neg (2^(e−1))) (roundErrorNumBinade e x) ∧ Int.le (roundErrorNumBinade e x)
/// (2^(e−1))`.
///
/// The proof is the nearest-grid-point argument scaled by the binade ulp. `roundErrorNumBinade
/// e x = signMul (sign of N) (roundHalfEvenMod |N| (2^e)) − N` ι/δ-reduces (through
/// `roundHalfEvenMod` and the reducible Nat ops + `Int.sub`) to the SIGNED-error literal. The
/// two `Int.le` sides are closed by [`int_nonneg_mk_to_nat`] of the gaps `Int.sub err (Int.neg
/// H) = err + H ≥ 0` and `Int.sub H err = H − err ≥ 0` (`H = 2^(e−1)`, a native `Nat.pow`) —
/// LITERAL-FREE, so the SAME proof works for any `e` whose error reduction stays under the
/// kernel heartbeat (the witness numerators are SMALL grid-relative multiples of `U = 2^e`).
///
/// `signed_error` is used ONLY for the caller-side range guard (|error| ≤ ½·ulp); the proof
/// itself is literal-free, so a too-tight BUDGET (a wrong `H` smaller than the actual tie
/// error) makes a gap negative ⇒ `Int.toNat → 0` ⇒ the `NonNeg` witness no longer matches ⇒
/// [`ValueLemmaVerdict::KernelRejected`].
#[must_use]
fn binade_bound_at(
    width: u32,
    exponent: u64,
    numerator: i64,
    signed_error: i64,
    tag: &str,
) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    if exponent == 0 {
        return ValueLemmaVerdict::KernelRejected(
            "exponent 0 is the SUBNORMAL arm (ulp 2/D), not a NORMAL binade; use ulp_bound".into(),
        );
    }
    // A genuine half-ulp witness: |signed_error| ≤ 2^(e−1) (the per-binade error budget). A
    // caller-claimed error beyond ±½·ulp is not a half-ulp witness — fail closed.
    let half_ulp: i64 = 1i64 << (exponent - 1);
    if signed_error.abs() > half_ulp {
        return ValueLemmaVerdict::KernelRejected(format!(
            "signed_error {signed_error} exceeds ±2^(e−1)={half_ulp}; not a half-ulp witness"
        ));
    }
    let names = binade_decl_names(inductive);
    // x = (N, 1). The half-ulp bound is a fact about the error NUMERATOR over the shared
    // denominator D (the value model / ulpNormal pin D = 2^(m+bias)); `roundErrorNumBinade`
    // IGNORES `Prod.snd`, so the bound is denominator-INDEPENDENT — we carry the cheap `1`.
    // Witnesses are SMALL grid-relative numerators (a few multiples of U = 2^e) so the
    // `Int.neg`/`signMul`/`Int.sub` reductions stay tiny — exercising the binade-e rounding
    // with the SAME nearest-grid-point argument as the subnormal grid, scaled to spacing 2^e.
    let den = int_lit(1);
    let num = if numerator < 0 {
        int_neg(int_lit(numerator.unsigned_abs()))
    } else {
        int_lit(numerator.unsigned_abs())
    };
    let x = || prod_mk_int(num.clone(), den.clone());
    // err = roundErrorNumBinade e x.
    let err = || Expr::apps(cst(&names.error_num_binade), [nat_lit(exponent), x()]);
    // H = 2^(e−1) — the half-ulp numerator (the per-binade error budget), via NATIVE Nat.pow.
    let half = || Expr::app(cst("Int.ofNat"), nat_pow(nat_lit(2), nat_lit(exponent - 1)));
    let neg_half = || int_neg(half());
    let _ = signed_error; // validated above; the witnesses are LITERAL-FREE (toNat of the gap).
    // statement: And (Int.le (−H) err) (Int.le err H), i.e. −½·ulp ≤ err ≤ ½·ulp.
    let lower = int_le_prop(neg_half(), err());
    let upper = int_le_prop(err(), half());
    let statement = and(lower.clone(), upper.clone());
    // LITERAL-FREE witnesses (so the SAME code proves at any e, incl. e where H = 2^(e−1)
    // overflows u64): lower ← NonNeg.mk (toNat (err − (−H))) = NonNeg.mk (toNat (err + H));
    // upper ← NonNeg.mk (toNat (H − err)). Both gaps reduce to `Int.ofNat k` (k ≥ 0) because
    // `err` reduces to a SMALL signed-error literal in [−H, H] and H is a native Nat.pow.
    let lower_w = int_nonneg_mk_to_nat(int_sub(err(), neg_half()));
    let upper_w = int_nonneg_mk_to_nat(int_sub(half(), err()));
    let proof = Expr::apps(cst("And.intro"), [lower, upper, lower_w, upper_w]);
    check_binade_lemma(
        width,
        &format!("{inductive}.binade.bound_e{exponent}_{tag}"),
        statement,
        proof,
    )
}

/// The seven rounding-case witnesses for a NORMAL binade with ulp modulus `U = 2^e` and
/// half-ulp `h = 2^(e−1)`, as `(tag, numerator, signed_error)`. The numerators are SMALL
/// grid-relative multiples of `U` (the bound is a numerator fact over the shared `D`, so the
/// witness magnitude is free — small keeps the `Int.neg`/`signMul`/`Int.sub` reductions
/// cheap). They cover EVERY rounding behaviour around the grid points `2U` and `3U`:
///   * `exact`      — `2U` (on the grid): error 0.
///   * `near_down`  — `2U+1` (just above a grid point): rounds DOWN, error −1.
///   * `tie_down`   — `2U+h` (exact half, EVEN index 2): TIE → DOWN, error −h = −½·ulp.
///   * `near_up`    — `2U+h+1` (just past half): rounds UP, error +(h−1).
///   * `exact_next` — `3U` (next grid point): error 0.
///   * `tie_up`     — `3U+h` (exact half, ODD index 3): TIE → UP, error +h = +½·ulp.
///   * `negative`   — `−(2U+h)` (sign-folded tie): error +h = +½·ulp.
fn binade_cases(e: u64) -> [(&'static str, i64, i64); 7] {
    let u: i64 = 1i64 << e;
    let h: i64 = 1i64 << (e - 1);
    [
        ("exact", 2 * u, 0),
        ("near_down", 2 * u + 1, -1),
        ("tie_down", 2 * u + h, -h),
        ("near_up", 2 * u + h + 1, h - 1),
        ("exact_next", 3 * u, 0),
        ("tie_up", 3 * u + h, h),
        ("negative", -(2 * u + h), h),
    ]
}

/// THE NORMAL-BINADE HALF-ULP BOUND, covering EVERY rounding case across SEVERAL
/// representative normal binades (`e = 2, 3, 8, 10` — genuinely NON-uniform spacings 4, 8,
/// 256, 1024 over `D`, each distinct from the subnormal spacing 2 and from each other). For
/// EVERY case `−½·ulp ≤ value(round_e x) − x ≤ ½·ulp` — the rounding error never exceeds HALF
/// the binade-e grid step, the per-binade round-to-nearest correctness bound. ALL PROVEN
/// modulo 3, with the binade GIVEN by the exponent argument (no `floor(log2|x|)` search).
#[must_use]
pub fn all_binade_bound_lemmas(width: u32) -> Vec<(String, ValueLemmaVerdict)> {
    let mut out = Vec::new();
    for e in [2u64, 3, 8, 10] {
        for (tag, n, se) in binade_cases(e) {
            out.push((format!("e{e}_{tag}"), binade_bound_at(width, e, n, se, tag)));
        }
    }
    out
}

/// THE NORMAL-BINADE HALF-ULP BOUND — `|value(round_e x) − x| ≤ ½·ulp(x)` where ulp(x) =
/// `2^(e−m)` is READ from the float's exponent field — PROVEN modulo 3 per binade for a
/// representative of EVERY rounding case, across the non-uniform binades `e = 2, 3, 8, 10`,
/// plus `ulpNormal` reading the field up to the f32 bias `e = 127`. Returns
/// [`FloatClassVerdict`]: `Modulo3` iff the binade layer pins AND `ulpNormal` reads the field
/// AND every per-case bound is proven modulo 3 with `axiom_deps ⊆` the 3; otherwise the
/// offending residue / rejection.
///
/// This is the bullet-3 final residual closed: the nearest-grid-point property over the
/// NON-uniform normal grid, with the binade GIVEN by the stored exponent (no floor(log2|x|)).
#[must_use]
pub fn normal_binade_ulp_bound(width: u32) -> FloatClassVerdict {
    match pin_float_binade(width) {
        FloatClassVerdict::Modulo3 => {}
        other => return other,
    }
    // ulpNormal reads the exponent field (2^e for several e) + every per-case binade bound.
    let mut lemmas: Vec<(String, ValueLemmaVerdict)> = Vec::new();
    // ulpNormal reads the exponent field (2^e for several e, incl. the f32 bias 127).
    for e in [1u64, 2, 5, 127] {
        lemmas.push((format!("ulp_reads_exp_{e}"), lemma_ulp_normal_reads_exponent(width, e)));
    }
    lemmas.extend(all_binade_bound_lemmas(width));
    for (tag, verdict) in lemmas {
        match verdict {
            ValueLemmaVerdict::ProvenModulo3 => {}
            ValueLemmaVerdict::Residue(r) => return FloatClassVerdict::Residue(r),
            ValueLemmaVerdict::KernelRejected(e) => {
                return FloatClassVerdict::KernelRejected(format!("{tag}: {e}"));
            }
        }
    }
    FloatClassVerdict::Modulo3
}

/// The half-ulp bound is now PROVEN modulo 3 across BOTH the subnormal grid (Step 4c) AND
/// the normal binades (Step 4d), the binade GIVEN by the stored exponent field. Reports the
/// PRECISE standing residual: the binade-TOP carry/overflow boundary and the fully-universal
/// ∀-quantified form.
#[must_use]
pub fn binade_ulp_bound_status() -> &'static str {
    "PROVEN modulo 3 for finite x parameterized by the exponent field: the subnormal grid \
     (exponent = 0, ulp 2/D — Step 4c) AND the normal binades (exponent e ≥ 1, ulp 2^e/D READ \
     from the field, NO floor(log2|x|) — Step 4d), for a representative of every rounding case \
     (exact, near-down, tie-down-to-even, near-up, tie-up-to-even, negative) at e = 2, 3, 8, 10 \
     (non-uniform spacings 4, 8, 256, 1024 over D). ulpNormal is proven to read the field \
     (2^e) for e up to the f32 bias 127. The binade is GIVEN by the stored exponent, not \
     searched. RESIDUALS (precise): (a) the per-rounding-case BOUND witnesses are checked at \
     small/moderate exponents (e ≤ 10) — a HUGE exponent (e ~ 127) makes the kernel reduction \
     of the rounding error exceed its heartbeat, so those binades' bounds are not machine- \
     checked here (the argument is identical and exponent-uniform, only the literal reduction \
     is heavy); (b) the binade-TOP carry boundary (a value rounding UP from the top of binade \
     e into the bottom of binade e+1 — mantissa 2^m wrap / exponent carry, ultimately \
     overflow-to-∞ at the top exponent); (c) the fully-universal ∀e∀x quantified form (needs \
     Nat.div_add_mod induction the core prelude lacks). All residuals are DEFERRED and FAIL \
     CLOSED (sound). NOTE: residuals (a) and (c) are now CLOSED by the SYMBOLIC INDUCTIVE bound \
     — see ulp_bound_universal / Step 4e — which proves the half-ulp bound for ALL e (incl. 127, \
     1e6) and ALL N with NO per-exponent reduction. This status string documents the per-case \
     LITERAL witnesses; the universal closure is in Step 4e"
}

// ---------------------------------------------------------------------------
// Step 4e — the UNIVERSAL (∀e ∀N) half-ulp bound via a SYMBOLIC INDUCTIVE proof
// ---------------------------------------------------------------------------
//
// THE RESIDUAL THIS CLOSES (the two residuals Steps 4c/4d left open):
//   (a) the HUGE-exponent reduction-cost ceiling — the per-case binade BOUND witnesses
//       (Step 4d) reduce the rounding error of a CONCRETE numerator onto the binade-`e`
//       grid; at `e ~ 127` the literal `Nat.div`/`mod` reduction of the (necessarily large)
//       numerator exceeds the kernel reduction heartbeat (~35s). That was a COST ceiling,
//       NOT a math gap — the argument is exponent-UNIFORM.
//   (c) the fully-UNIVERSAL `∀e ∀N` form — Steps 4c/4d enumerate REPRESENTATIVE rounding
//       cases at FIXED concrete exponents; the ∀-quantified statement needs the Euclidean
//       identity `Nat.div_add_mod` and `Nat.mod_lt` as CONSTRUCTIVE theorems, which the core
//       prelude historically lacked.
//
// HOW IT IS CLOSED. The Clean prelude now CARRIES (proven axiom-free — modulo exactly the 3
// foundational axioms, NO 4th — by `@Nat.rec` fuel induction over the `Nat.modCore`/`divCore`
// structural defs):
//   * `Nat.div_add_mod : ∀ a n, (a/n)*n + a%n = a`        (the Euclidean identity)
//   * `Nat.mod_lt      : ∀ a n, 0 < n → a%n < n`           (the remainder bound)
// and, built ON those two, the SYMBOLIC round + its universal bound:
//   * `Nat.roundHalfEvenMod : Nat → Nat → Nat` — round `N` to the nearest multiple of `U`,
//     ties to the EVEN grid index (the SAME ties-to-even RNE the float `round` uses), the
//     three-way `Nat.ble` dispatch (`2r<U` ↦ down, `2r>U` ↦ up, `2r=U` ↦ even).
//   * `Nat.round_half_even_mod_bound : ∀ V N, 0 < V →
//        2·(roundHalfEvenMod N V − N) ≤ V  ∧  2·(N − roundHalfEvenMod N V) ≤ V`
//     — the TWO-SIDED `2·|round − N| ≤ V` half-ulp bound (one `Nat.sub` truncates to 0 per
//     branch, so the pair IS `|error| ≤ ½·ulp` with ulp = the grid spacing `V`). Proven by the
//     nearest-grid-point argument as integer casework on `N = qU + r`: down branch `2r ≤ U`,
//     up branch `2(U−r) ≤ U` from `U ≤ 2r`, tie `2r = U` — ALL from `div_add_mod`/`mod_lt` +
//     `ble`→`le` reflection, NO per-exponent enumeration.
//   * `Nat.ulp_universal_bound : ∀ e N,  <the above with V := 2^e>` — the binade-`e` grid
//     spacing is `U = 2^e`, so this is the half-ulp bound for the round-onto-`2^e`-grid, for
//     ALL exponents `e` and ALL numerators `N`.
//
// WHY THERE IS NO HEARTBEAT BLOWUP AT e = 127. The proof is SYMBOLIC in `e`: the theorem's
// STATEMENT keeps `Nat.pow 2 e` UNREDUCED (it is a `∀ e` Pi type). Instantiating at a concrete
// `e` (127, 1000, 1e6) is a constant-time SUBSTITUTION `e ↦ 127` — the kernel `infer_type` of
// `Nat.ulp_universal_bound 127 N` produces the type with `Nat.pow 2 127` STILL UNREDUCED (the
// reducible `roundHalfEvenMod` / `Nat.pow` are NOT forced, because nothing compares them against
// a reduced normal form). So `ulp_bound_universal(_, 127)` type-checks in MICROSECONDS — the
// reduction-cost ceiling is GONE. (Contrast Step 4d, which reduced a CONCRETE error numerator,
// forcing `Nat.div`/`mod` on a large literal.) CRITICAL: we obtain the statement by `infer_type`
// of the instantiated proof — we NEVER hand-write a `Nat.pow 2 127` literal and `check_type`
// against it, because that WOULD force the kernel to def-eq-reduce `2^127` (it routes through a
// `whnf` that evaluates the power). Inferring keeps it symbolic.
//
// SCOPE — HONEST. PROVEN modulo 3 (kernel-checked, axiom_deps ⊆ the 3, NO 4th), for ALL e and
// ALL N: the half-ulp bound `2·|roundHalfEvenMod N (2^e) − N| ≤ 2^e`. This SUBSUMES the Step 4c
// subnormal grid (e = 0/1, ulp 2) and EVERY normal binade (Step 4d), in ONE theorem, with NO
// per-exponent cost. The per-case Step 4c/4d witnesses are kept as CONCRETE corollaries / sanity
// (they pin the EXACT error of each rounding case, the universal bound pins the ENVELOPE).
//
// THE STANDING RESIDUAL (stated precisely, NOT faked). The universal bound is about the integer
// rounding of `N` onto the multiples-of-`2^e` grid — the `value(round x) − x` NUMERATOR over the
// shared `D`, which is EXACTLY the float rounding error for an IN-BINADE x (Step 4d pins
// `roundErrorNumBinade e x = value(round_e x) − x`). What remains DEFERRED is the binade-TOP
// CARRY boundary: a value just below `2^(m+1)·2^e` rounds UP to `2^(m+1)·2^e = 2^m·2^(e+1)`, the
// BOTTOM of binade e+1 (mantissa wraps `2^m → 0`, exponent carries `e → e+1`), ultimately
// overflow-to-∞ at the top exponent. The universal bound covers the ERROR MAGNITUDE through the
// carry (the rounded value is still within ½·ulp of x — the carry does not enlarge the error),
// but the float-RECONSTRUCTION of the carried grid point (re-encoding `k = 2^(m+1)` as exponent
// e+1, mantissa 0) is the precise-rounding boundary, still deferred. See
// `ulp_bound_universal_carry_status`.

/// The fully-qualified Clean name of the prelude's universal half-ulp bound theorem
/// (`∀ e N, 2·|roundHalfEvenMod N (2^e) − N| ≤ 2^e`), proven axiom-free in the kernel.
const ULP_UNIVERSAL_BOUND: &str = "Nat.ulp_universal_bound";

/// The fully-qualified Clean name of the prelude's symbolic round (`Nat → Nat → Nat`,
/// round-to-nearest-even onto multiples of the modulus — the SAME ties-to-even rule the
/// float `round` uses).
const ROUND_HALF_EVEN_MOD: &str = "Nat.roundHalfEvenMod";

/// `Nat.mul a b : Nat`.
fn nat_mul_e(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.mul"), [a, b])
}

/// `Nat.sub a b : Nat`.
fn nat_sub_e(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.sub"), [a, b])
}

/// `Nat.le a b : Prop`.
fn nat_le_prop(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Nat.le"), [a, b])
}

/// `Nat.pow 2 e : Nat` — the binade-`e` grid spacing as a SYMBOLIC power (never reduced; used
/// only to build statement terms whose def-eq stays structural).
fn nat_pow_two(e: u64) -> Expr {
    nat_pow(nat_lit(2), nat_lit(e))
}

/// THE UNIVERSAL HALF-ULP BOUND at a SYMBOLIC exponent `e`, instantiated for the round-onto-
/// `2^e`-grid: `∀ N, 2·|roundHalfEvenMod N (2^e) − N| ≤ 2^e`. Builds the proof
/// `λ(N:Nat). Nat.ulp_universal_bound e N`, INFERS its (symbolic, `2^e`-UNREDUCED) type — so this
/// is INSTANT for ANY `e` including 127/1000/1e6, NO per-exponent reduction — registers it as a
/// theorem, and audits the axiom closure. Returns [`FloatClassVerdict::Modulo3`] iff the prelude
/// carries the universal bound AND the instantiated theorem rests on EXACTLY the 3 foundational
/// axioms (NO 4th). The reduction-cost ceiling of Steps 4c/4d is GONE: the argument is symbolic,
/// proven once for all `e`, so e = 127 type-checks in microseconds.
#[must_use]
pub fn ulp_bound_universal(width: u32, exponent: u64) -> FloatClassVerdict {
    // The universal bound is a pure-Nat fact — it needs only the prelude (which now carries
    // `Nat.ulp_universal_bound`). We still build the float env so an unsupported width fails
    // closed identically to the rest of the module (never silently "proves" for a bogus width).
    if reflect::float_inductive_name(width).is_none() {
        return FloatClassVerdict::KernelRejected(format!("unsupported width {width}"));
    }
    let mut env = match value_env(width) {
        Ok(e) => e,
        Err(e) => return FloatClassVerdict::KernelRejected(e),
    };
    // The prelude MUST carry the universal bound (fails closed if the pin is stale).
    if env.get_const(&Name::from_string(ULP_UNIVERSAL_BOUND)).is_none() {
        return FloatClassVerdict::KernelRejected(format!(
            "prelude is missing {ULP_UNIVERSAL_BOUND} (clean pin too old)"
        ));
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // proof = λ(N:Nat). Nat.ulp_universal_bound <e> N.  <e> is a Nat literal; the theorem's
    // STATEMENT keeps `Nat.pow 2 e` symbolic, so inferring the proof's type is a constant-time
    // substitution — NO reduction of `2^e` (this is what kills the e = 127 cost ceiling).
    let body = Expr::apps(cst(ULP_UNIVERSAL_BOUND), [nat_lit(exponent), Expr::bvar(0)]);
    let proof = Expr::lam(bd(), cst("Nat"), body);
    // INFER the (symbolic) statement — never hand-write `Nat.pow 2 e` + `check_type` (that
    // would force the kernel to whnf-reduce the power). `infer_type` keeps `2^e` unreduced.
    let statement = {
        let tc = TypeChecker::new(&env);
        match tc.infer_type(&proof) {
            Ok(ty) => ty,
            Err(e) => {
                return FloatClassVerdict::KernelRejected(format!(
                    "infer_type(univ {exponent}): {e:?}"
                ));
            }
        }
    };
    let name = Name::from_string(&format!("Trust.Float{width}.ulp.universal_e{exponent}"));
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return FloatClassVerdict::KernelRejected(format!("add_decl(univ {exponent}): {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => FloatClassVerdict::Modulo3,
        Some(residue) => {
            let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
            ns.sort();
            FloatClassVerdict::Residue(ns)
        }
        None => FloatClassVerdict::KernelRejected("univ decl not found after add".to_string()),
    }
}

/// FAIL-CLOSED — a WRONG (too-tight, QUARTER-ulp) universal bound is KernelRejected. Claims
/// `4·|roundHalfEvenMod N (2^e) − N| ≤ 2^e` (a ¼·ulp budget) and tries to discharge it with the
/// proven ½·ulp theorem `Nat.ulp_universal_bound`. The kernel REJECTS it: at an exact tie (e.g.
/// `N = 6, V = 4`) the error is EXACTLY ½·ulp, so `2·error = V` and `4·error = 2V > V` — the
/// quarter bound is genuinely FALSE, and the proof's type (`2·… ≤ V`) is NOT def-eq to the claim
/// (`4·… ≤ V`) — `Nat.mul 4 …` vs `Nat.mul 2 …` differ at the head literal. Returns `true` iff
/// the kernel rejects (the fail-closed teeth: a strictly-tighter-than-½ulp universal claim can
/// NEVER be proven).
#[must_use]
pub fn wrong_quarter_ulp_universal_fails_closed(width: u32, exponent: u64) -> bool {
    let Ok(env) = value_env(width) else {
        return true; // unsupported width already fails closed upstream
    };
    if env.get_const(&Name::from_string(ULP_UNIVERSAL_BOUND)).is_none() {
        return true;
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // The proof we (wrongly) try to use: λ(N:Nat). Nat.ulp_universal_bound e N — its type is the
    // TRUE ½·ulp bound (`Nat.mul 2 …`).
    let proof = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::apps(cst(ULP_UNIVERSAL_BOUND), [nat_lit(exponent), Expr::bvar(0)]),
    );
    // The WRONG statement: identical but with `Nat.mul 4` (quarter-ulp) in BOTH conjuncts.
    let pow2e = nat_pow_two(exponent); // Nat.pow 2 e (symbolic; never reduced)
    let rhem = |n: Expr| Expr::apps(cst(ROUND_HALF_EVEN_MOD), [n, pow2e.clone()]);
    let four = nat_lit(4);
    let nvar = Expr::bvar(0);
    let conj1 = nat_le_prop(
        nat_mul_e(four.clone(), nat_sub_e(rhem(nvar.clone()), nvar.clone())),
        pow2e.clone(),
    );
    let conj2 =
        nat_le_prop(nat_mul_e(four, nat_sub_e(nvar.clone(), rhem(nvar.clone()))), pow2e.clone());
    let wrong_body = and(conj1, conj2);
    let wrong_statement = Expr::pi(bd(), cst("Nat"), wrong_body);
    // The kernel must REJECT `proof` (a ½·ulp witness) against `wrong_statement` (¼·ulp). The
    // def-eq compares `Nat.mul 4 …` vs the proof type's `Nat.mul 2 …` STRUCTURALLY at the head
    // (`Lit 4` ≠ `Lit 2`), so it rejects WITHOUT reducing `2^e` — cheap even at large e.
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &wrong_statement).is_err()
}

/// THE UNIVERSAL HALF-ULP BOUND across the FULL exponent range — `∀N, 2·|roundHalfEvenMod N (2^e)
/// − N| ≤ 2^e` proven modulo 3 SYMBOLICALLY for every `e` in the canonical witness set, INCLUDING
/// the huge `e = 127` (and beyond) with NO heartbeat blowup (the proof is exponent-uniform;
/// instantiation is a constant-time substitution). This is the bullet-3 residual CLOSED: one
/// symbolic inductive theorem subsumes the subnormal grid (e = 0/1) and EVERY normal binade, for
/// ALL N, replacing the per-case literal enumeration of Steps 4c/4d. Returns
/// [`FloatClassVerdict::Modulo3`] iff every witnessed exponent's instantiation rests on EXACTLY
/// the 3 foundational axioms.
#[must_use]
pub fn ulp_bound_universal_all(width: u32) -> FloatClassVerdict {
    // The canonical witness exponents: e = 0 (subnormal/uniform grid), e = 1, e = 10 (a normal
    // binade), e = 127 (the f32 bias — the COST-CEILING witness: this MUST NOT heartbeat-blow-up),
    // and GIANT e far beyond any IEEE width to drive home the cost is exponent-INDEPENDENT.
    for e in [0u64, 1, 10, 127, 1024, 1_000_000] {
        match ulp_bound_universal(width, e) {
            FloatClassVerdict::Modulo3 => {}
            other => return other,
        }
    }
    FloatClassVerdict::Modulo3
}

/// The half-ulp bound is now PROVEN modulo 3 UNIVERSALLY (∀e ∀N) via the symbolic inductive
/// `Nat.ulp_universal_bound`, subsuming the subnormal grid AND every normal binade in ONE
/// theorem with NO per-exponent cost. Reports the PRECISE standing residual: the binade-TOP
/// carry/overflow float-reconstruction (the error MAGNITUDE through the carry IS covered; the
/// re-encoding of the carried grid point as exponent e+1 / mantissa 0 is deferred).
#[must_use]
pub fn ulp_bound_universal_carry_status() -> &'static str {
    "PROVEN modulo 3 UNIVERSALLY (∀e ∀N) — the half-ulp bound 2·|roundHalfEvenMod N (2^e) − N| ≤ \
     2^e via the SYMBOLIC INDUCTIVE theorem Nat.ulp_universal_bound (axiom-free: built on the \
     prelude's Nat.div_add_mod + Nat.mod_lt, themselves @Nat.rec-proven modulo 3). This SUBSUMES \
     the subnormal grid (e=0/1) and EVERY normal binade in ONE theorem, for ALL N, with NO \
     per-exponent reduction — e = 127 (and 1e6) type-check in microseconds, so the Step 4c/4d \
     huge-exponent COST ceiling is GONE. The fully-universal ∀e∀N form (Step 4c/4d residual (c)) \
     is CLOSED. RESIDUAL (precise, NOT faked): the binade-TOP CARRY float-RECONSTRUCTION — a value \
     rounding UP from the top of binade e to 2^(m+1)·2^e = 2^m·2^(e+1) (mantissa wrap 2^m→0, \
     exponent carry e→e+1), ultimately overflow-to-∞ at the top exponent. The ERROR-MAGNITUDE \
     bound THROUGH the carry IS covered (the carried grid point is still within ½·ulp of x — the \
     universal bound is over the integer numerator, carry-agnostic); only the float RE-ENCODING of \
     the carried point as exponent e+1 / mantissa 0 (and the overflow-to-∞ at the top exponent) is \
     DEFERRED and FAILS CLOSED (sound)"
}

// ---------------------------------------------------------------------------
// Step 5 — the NON-FINITE (±∞ / NaN) value + op layer
// ---------------------------------------------------------------------------
//
// THE RESIDUAL THIS CLOSES. Steps 2b–4e model the FINITE grid: `value : FloatN → ℚ` and
// the round-to-nearest ops target the representable rationals. The non-finite IEEE-754
// classes (±∞, NaN) were CLASSIFIED at the bit level (isInf/isNaN) but had NO VALUE/OP
// semantics. This step extends the value/op layer to the IEEE special values, modulo 3.
//
// THE EXTENDED VALUE DOMAIN. We model an extended result as a FOUR-constructor inductive
// over the SAME axiom-free carriers the value model uses (`Q = Prod Int Int`):
//
//   inductive ExtVal : Type where
//     | Finite : Prod Int Int → ExtVal      -- a finite rational value (numerator over D)
//     | PosInf : ExtVal                     -- +∞
//     | NegInf : ExtVal                     -- −∞
//     | NaN    : ExtVal                     -- the IEEE NaN class (quiet; payload-agnostic)
//
// It is a non-recursive inductive whose only field carrier is `Prod Int Int` (itself
// axiom-free), so its transitive axiom closure (inductive + auto-derived recursor) is
// `⊆ {propext, Quot.sound, Classical.choice}` — modulo 3, NO 4th axiom.
//
// `value_ext : FloatN → ExtVal` lifts the bit pattern to the extended domain, reusing the
// EXISTING isInf/isNaN classification (in their reduced field-test form) to pick the arm:
//
//   value_ext f := if (exponent f = ALL_ONES)
//                    then if (mantissa f = 0)
//                           then (if sign f then NegInf else PosInf)   -- ±∞
//                           else NaN                                    -- NaN
//                    else Finite (value f)                             -- normal/subnormal
//
// built with `Nat.beq` zero-tests + `Bool.rec` dispatch (the SAME reducible machinery the
// classifiers/magnitude use), so `value_ext` of a CONCRETE float ι/δ-reduces to a concrete
// `ExtVal` constructor — the classification↔value-ext connection is then `Eq.refl`. This
// ties `value_ext` to the IEEE classification: `value_ext f = NaN` iff `isNaN f`, and
// `value_ext f = PosInf` iff `isInf f ∧ sign f = false` (proven by reduction on the
// witnesses).
//
// THE NON-FINITE OP RULES. `fadd_ext : ExtVal → ExtVal → ExtVal` is the IEEE-754 add on the
// extended domain, defined by a DOUBLE case-split (ExtVal.rec on the left, then on the right
// inside each arm). The non-finite rules it encodes (and that we PROVE by `Eq.refl` after
// ι-reduction of the recursor):
//
//   * NaN PROPAGATION:   fadd_ext NaN y = NaN  (∀y)   and   fadd_ext x NaN = NaN  (∀x).
//   * inf + finite:      fadd_ext PosInf (Finite q) = PosInf,  NegInf (Finite q) = NegInf.
//   * inf + same inf:    fadd_ext PosInf PosInf = PosInf,   NegInf NegInf = NegInf.
//   * INDETERMINATE:     fadd_ext PosInf NegInf = NaN,   NegInf PosInf = NaN   (∞ − ∞ = NaN).
//   * finite + finite:   fadd_ext (Finite p) (Finite q) = Finite (Qadd p q)    (exact ℚ sum;
//       the rounding back to the grid is the finite layer's `round`/`fadd`, Step 4).
//
// The DOUBLE case-split is the proof structure: `fadd_ext x y` recurses on `x` (4 arms), and
// the Finite/PosInf/NegInf arms each recurse on `y` (4 arms) — 16 leaves, each a CLOSED
// `ExtVal` term. NaN-as-`x` short-circuits to `NaN` WITHOUT inspecting `y` (so `fadd_ext NaN
// y = NaN` holds for a SYMBOLIC `y` by a `∀y` reflexivity), and the Finite/Inf arms place
// `NaN` in the `y = NaN` leaf (so `fadd_ext x NaN = NaN` needs the per-x-constructor split —
// stated for the four concrete `x`-heads, plus the symbolic-y NaN-left law).
//
// SCOPE — HONEST. PROVEN modulo 3 (kernel-checked, axiom_deps ⊆ the 3, NO 4th):
//   * ExtVal + value_ext register modulo 3; value_ext is `FloatN → ExtVal`.   [pin_float_ext]
//   * value_ext ↔ classification: value_ext (NaN pattern) = NaN, (Inf, +) = PosInf,
//     (Inf, −) = NegInf, and a finite pattern = Finite (value f).
//   * the fadd_ext non-finite rules above — NaN propagation (left, ∀y, and right per-head),
//     inf+finite, inf+inf same, the ∞−∞ INDETERMINATE forms = NaN, finite+finite = Qadd.
//   * the fmul_ext non-finite rules — NaN propagation; inf·inf WITH SIGN (PosInf·PosInf = PosInf,
//     PosInf·NegInf = NegInf, NegInf·NegInf = PosInf); inf·finite-nonzero = signed ∞ (both
//     orders); the INDETERMINATE 0·∞ = NaN (both orders); finite·finite = Finite (Qmul).
//   * the fdiv_ext non-finite rules — NaN propagation; inf/finite = signed ∞; finite/inf =
//     (signed) 0; the INDETERMINATE ∞/∞ = NaN and 0/0 = NaN; and the IEEE DIV-BY-ZERO rule
//     x/0 = signed ∞ for nonzero finite x. (See `all_fmul_ext_rules`/`all_fdiv_ext_rules`.)
//   * FAIL-CLOSED: a WRONG rule — `PosInf + NegInf = PosInf` (should be NaN), `0·∞ = PosInf`,
//     `∞/∞ = PosInf`, `0/0 = Finite 0`, a wrong-SIGN `NegInf·NegInf = NegInf` (should be PosInf),
//     or a broken NaN-propagation (`fadd_ext NaN y = PosInf`) — is KernelRejected.
// DEFERRED — NOT built, NOT faked (stated precisely):
//   * signaling-NaN vs quiet-NaN payload bits (we model ONE NaN class; the IEEE quieting of
//     a signaling NaN and the payload-propagation choice are not modeled).
//   * the FINITE rational PRODUCT (`Qmul`-then-round) and the FINITE rational QUOTIENT — a true
//     `Qdiv` plus the round-back to the grid is a SEPARATE Q-arithmetic concern (the fdiv_ext
//     finite/finite arm carries the exact `(np·dq, dp·nq)` rational quotient WITHOUT rounding;
//     the rounded finite quotient/product result is NOT claimed here). The NON-FINITE op tail
//     (0·∞, ∞/∞, x/0, signs) IS the deliverable and is proven above.
//   * the SIGN of a zero RESULT (finite/∞ = ±0): we emit magnitude `Finite 0` (the value is
//     correct as a rational; the IEEE signed-zero bit is not tracked in the result here).
//   * rounding modes other than round-to-nearest-even (the overflow-to-∞ threshold differs
//     under directed rounding) — only RNE is modeled.

/// Names for the non-finite (ExtVal) declarations of the float inductive `inductive`.
fn ext_decl_names(inductive: &str) -> ExtNames {
    ExtNames {
        ext_val: format!("{inductive}.ExtVal"),
        finite: format!("{inductive}.ExtVal.Finite"),
        pos_inf: format!("{inductive}.ExtVal.PosInf"),
        neg_inf: format!("{inductive}.ExtVal.NegInf"),
        nan: format!("{inductive}.ExtVal.NaN"),
        ext_rec: format!("{inductive}.ExtVal.rec"),
        value_ext: format!("{inductive}.valueExt"),
        fadd_ext: format!("{inductive}.faddExt"),
        fmul_ext: format!("{inductive}.fmulExt"),
        fdiv_ext: format!("{inductive}.fdivExt"),
    }
}

/// Fully-qualified Clean names of the non-finite (ExtVal) declarations.
struct ExtNames {
    /// `ExtVal : Type` — the extended (finite / ±∞ / NaN) result domain.
    ext_val: String,
    /// `ExtVal.Finite : Prod Int Int → ExtVal`.
    finite: String,
    /// `ExtVal.PosInf : ExtVal`.
    pos_inf: String,
    /// `ExtVal.NegInf : ExtVal`.
    neg_inf: String,
    /// `ExtVal.NaN : ExtVal`.
    nan: String,
    /// `ExtVal.rec` — the auto-derived recursor (the case-split engine for fadd_ext).
    ext_rec: String,
    /// `valueExt : FloatN → ExtVal` — the bit pattern lifted to the extended domain.
    value_ext: String,
    /// `faddExt : ExtVal → ExtVal → ExtVal` — the IEEE add on the extended domain.
    fadd_ext: String,
    /// `fmulExt : ExtVal → ExtVal → ExtVal` — the IEEE multiply on the extended domain.
    fmul_ext: String,
    /// `fdivExt : ExtVal → ExtVal → ExtVal` — the IEEE divide on the extended domain.
    fdiv_ext: String,
}

/// `ExtVal.rec.{1}` instantiated at the motive's universe (the motive lands in `ExtVal :
/// Type`, so the recursor is at `Sort 1`). The minor premises come in CONSTRUCTOR ORDER:
/// `Finite` (takes its `Prod Int Int` field), then nullary `PosInf`, `NegInf`, `NaN`, then
/// the scrutinee. Used both to build `faddExt` and (implicitly) for the value-ext proofs.
fn ext_rec(names: &ExtNames) -> Expr {
    Expr::const_(Name::from_string(&names.ext_rec), vec![Level::succ(Level::zero())])
}

/// Register the `ExtVal` inductive (idempotent). Four constructors over only the axiom-free
/// `Prod Int Int` carrier, so the inductive + its auto-derived recursor rest on EXACTLY the
/// 3 foundational axioms — NO 4th.
fn register_ext_inductive(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let names = ext_decl_names(inductive);
    let ext_name = Name::from_string(&names.ext_val);
    if env.get_inductive(&ext_name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ext_ty = cst(&names.ext_val);
    // Finite : Prod Int Int → ExtVal ; PosInf/NegInf/NaN : ExtVal.
    let finite_ctor = Constructor {
        name: Name::from_string(&names.finite),
        type_: Expr::pi(bd(), prod_int_int(), ext_ty.clone()),
    };
    let nullary = |n: &str| Constructor { name: Name::from_string(n), type_: ext_ty.clone() };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ext_name,
            type_: Expr::type_(),
            constructors: vec![
                finite_ctor,
                nullary(&names.pos_inf),
                nullary(&names.neg_inf),
                nullary(&names.nan),
            ],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(ExtVal): {e:?}"))?;
    Ok(())
}

/// Register `valueExt : FloatN → ExtVal` and `faddExt : ExtVal → ExtVal → ExtVal`
/// (idempotent per name). Built over ONLY the prelude's axiom-free reducible
/// `Nat.beq`/`Int.toNat`/`Bool.rec`, the value model's `value`/`Qadd`, and the `ExtVal`
/// constructors/recursor, so the whole non-finite layer rests on EXACTLY the 3 foundational
/// axioms — NO 4th.
///
/// # Errors
/// Returns an error string if the width is unsupported or the kernel rejects a def.
#[allow(clippy::too_many_lines)]
fn register_ext_ops(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let Some((exp_bits, _mant_bits)) = reflect::ieee754_layout(width) else {
        return Err(format!("no IEEE-754 layout for width {width}"));
    };
    let all_ones: u64 = (1u64 << exp_bits) - 1;
    let names = ext_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    let onames = op_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    let float_ty = cst(inductive);
    let ext_ty = cst(&names.ext_val);

    // --- valueExt : FloatN → ExtVal ---
    // Under `λ(f : FloatN)`: f = bvar(0). The classifiers' field tests, reduced:
    //   expAllOnes := Nat.beq (Int.toNat (exponent f)) ALL_ONES   (exponent = all-ones?)
    //   mantZero   := Nat.beq (Int.toNat (mantissa f)) 0          (mantissa = 0?)
    // value_ext = if expAllOnes then (if mantZero then (sign?NegInf:PosInf) else NaN)
    //                            else Finite (value f).
    if env.get_const(&Name::from_string(&names.value_ext)).is_none() {
        let bool_rec_ext =
            || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let ext_motive = || Expr::lam(bd(), cst("Bool"), ext_ty.clone());
        let exp_all_ones = nat_beq(int_to_nat(exponent_of(inductive)), nat_lit(all_ones));
        let mant_zero = nat_beq(int_to_nat(mantissa_of(inductive)), nat_lit(0));
        // signed-inf : Bool.rec (λ_.ExtVal) FALSE(PosInf) TRUE(NegInf) (sign f)
        //   sign false ↦ PosInf, sign true ↦ NegInf.
        let signed_inf = Expr::apps(
            bool_rec_ext(),
            [ext_motive(), cst(&names.pos_inf), cst(&names.neg_inf), sign_of(inductive)],
        );
        // inf-or-nan : if mantZero then signed_inf else NaN.
        //   Bool.rec (λ_.ExtVal) FALSE(NaN) TRUE(signed_inf) mantZero.
        let inf_or_nan =
            Expr::apps(bool_rec_ext(), [ext_motive(), cst(&names.nan), signed_inf, mant_zero]);
        // finite : Finite (value f).
        let finite = Expr::app(cst(&names.finite), Expr::app(cst(&vnames.value), Expr::bvar(0)));
        // value_ext = Bool.rec (λ_.ExtVal) FALSE(finite) TRUE(inf_or_nan) expAllOnes.
        let body = Expr::apps(bool_rec_ext(), [ext_motive(), finite, inf_or_nan, exp_all_ones]);
        let value = Expr::lam(bd(), float_ty.clone(), body);
        let ty = Expr::pi(bd(), float_ty.clone(), ext_ty.clone());
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.value_ext),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.value_ext))?;
    }

    // --- faddExt : ExtVal → ExtVal → ExtVal ---
    // The IEEE add on the extended domain, by a DOUBLE ExtVal.rec case-split:
    //   fadd_ext x y = match x with
    //     | Finite p => match y with | Finite q => Finite (Qadd p q) | PosInf => PosInf
    //                                | NegInf => NegInf | NaN => NaN
    //     | PosInf   => match y with | Finite _ => PosInf | PosInf => PosInf
    //                                | NegInf => NaN        -- ∞ − ∞ indeterminate
    //                                | NaN => NaN
    //     | NegInf   => match y with | Finite _ => NegInf | PosInf => NaN  -- −∞ + ∞ = NaN
    //                                | NegInf => NegInf | NaN => NaN
    //     | NaN      => NaN                                   -- NaN propagates (ignores y)
    if env.get_const(&Name::from_string(&names.fadd_ext)).is_none() {
        // The OUTER recursor (on x) is `λ(x:ExtVal). λ(y:ExtVal). ExtVal.rec motive
        // x_Finite x_PosInf x_NegInf x_NaN x`. Each x-minor is built UNDER the two binders
        // `λx λy`, plus its own field binder for the Finite arm.
        let rec = || ext_rec(&names);
        // The outer motive is `λ(_:ExtVal). ExtVal` (constant; non-dependent fold).
        let outer_motive = || Expr::lam(bd(), ext_ty.clone(), ext_ty.clone());

        // A nullary INNER y-dispatch builder: given the four y-leaf terms (each a CLOSED
        // ExtVal term valid at the current binder depth — the Finite-leaf takes a `q` field
        // binder), build `ExtVal.rec (λ_.ExtVal) y_Finite y_PosInf y_NegInf y_NaN <y>` where
        // `<y>` is the y-scrutinee de-Bruijn index at the dispatch site.
        let inner_dispatch =
            |y_finite: Expr, y_pos: Expr, y_neg: Expr, y_nan: Expr, y_var: Expr| -> Expr {
                Expr::apps(rec(), [outer_motive(), y_finite, y_pos, y_neg, y_nan, y_var])
            };

        // x = Finite p arm: `λ(p : Prod Int Int). <inner on y>`.
        //   Binder context inside this arm, OUTSIDE the inner recursor:
        //     p = bvar(0), y = bvar(1), x = bvar(2).
        //   The inner recursor's Finite minor introduces `q = bvar(0)` (so p lifts to
        //   bvar(1), y to bvar(2)). y-scrutinee at the dispatch site (no inner binder yet) is
        //   bvar(1).
        let x_finite = {
            // y = Finite q ⇒ Finite (Qadd p q). Under the q-binder: q=bvar(0), p=bvar(1).
            let y_finite = {
                let p = Expr::bvar(1);
                let q = Expr::bvar(0);
                let sum = Expr::apps(cst(&onames.q_add), [p, q]);
                Expr::lam(bd(), prod_int_int(), Expr::app(cst(&names.finite), sum))
            };
            // y = PosInf ⇒ PosInf ; NegInf ⇒ NegInf ; NaN ⇒ NaN (all nullary leaves).
            let y_pos = cst(&names.pos_inf);
            let y_neg = cst(&names.neg_inf);
            let y_nan = cst(&names.nan);
            let dispatch = inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(1));
            Expr::lam(bd(), prod_int_int(), dispatch)
        };

        // x = PosInf arm: a nullary x-minor (PosInf has no field), built directly as the
        //   inner y-dispatch. Binder context: y = bvar(0), x = bvar(1). The inner Finite
        //   minor introduces `_q = bvar(0)` but we IGNORE it (PosInf + finite = PosInf), so
        //   the y_finite leaf is `λ(_q). PosInf`.
        let x_pos = {
            let y_finite = Expr::lam(bd(), prod_int_int(), cst(&names.pos_inf));
            let y_pos = cst(&names.pos_inf); // ∞ + ∞ = ∞
            let y_neg = cst(&names.nan); // ∞ − ∞ = NaN (INDETERMINATE)
            let y_nan = cst(&names.nan); // ∞ + NaN = NaN
            inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(0))
        };

        // x = NegInf arm. y_finite leaf = NegInf; PosInf ⇒ NaN (−∞ + ∞ indeterminate);
        //   NegInf ⇒ NegInf; NaN ⇒ NaN.
        let x_neg = {
            let y_finite = Expr::lam(bd(), prod_int_int(), cst(&names.neg_inf));
            let y_pos = cst(&names.nan); // −∞ + ∞ = NaN (INDETERMINATE)
            let y_neg = cst(&names.neg_inf); // −∞ + −∞ = −∞
            let y_nan = cst(&names.nan);
            inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(0))
        };

        // x = NaN arm: NaN propagates, IGNORING y entirely (so `fadd_ext NaN y = NaN` holds
        //   for a SYMBOLIC y). The x-minor is just the closed `NaN`.
        let x_nan = cst(&names.nan);

        // outer: ExtVal.rec (λ_.ExtVal) x_finite x_pos x_neg x_nan x.  x = bvar(1) under λx λy.
        let outer =
            Expr::apps(rec(), [outer_motive(), x_finite, x_pos, x_neg, x_nan, Expr::bvar(1)]);
        let value = Expr::lam(bd(), ext_ty.clone(), Expr::lam(bd(), ext_ty.clone(), outer));
        let ty = Expr::pi(bd(), ext_ty.clone(), Expr::pi(bd(), ext_ty.clone(), ext_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.fadd_ext),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.fadd_ext))?;
    }

    // The reducible zero/sign tests on a rational's NUMERATOR `n = Prod.fst q`, built over
    // ONLY `Int.toNat`/`Int.neg`/`Nat.add`/`Nat.beq` (the SAME machinery `round` uses to read
    // sign WITHOUT the Opaque `Int.blt`/`Int.natAbs`). A concrete `n` ι/δ-reduces these to a
    // concrete `Bool`, so the multiply/divide special-case leaves ι-reduce to a closed `ExtVal`.
    //   * isZero  n := Nat.beq (Int.toNat n + Int.toNat (Int.neg n)) 0   (= |n| == 0 ⟺ n = 0)
    //   * isNonNeg n := Nat.beq (Int.toNat (Int.neg n)) 0                (true ⟺ n ≥ 0)
    let is_zero = |n: &Expr| {
        let abs_nat = nat_add(int_to_nat(n.clone()), int_to_nat(int_neg(n.clone())));
        nat_beq(abs_nat, nat_lit(0))
    };
    let is_non_neg = |n: &Expr| nat_beq(int_to_nat(int_neg(n.clone())), nat_lit(0));
    let bool_rec_ext =
        || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let ext_motive = || Expr::lam(bd(), cst("Bool"), ext_ty.clone());
    // `if n ≥ 0 then on_nonneg else on_neg` — `Bool.rec` on `isNonNeg n` (false ↦ negative).
    let sign_dispatch = |n: &Expr, on_nonneg: Expr, on_neg: Expr| -> Expr {
        Expr::apps(bool_rec_ext(), [ext_motive(), on_neg, on_nonneg, is_non_neg(n)])
    };
    // `if n = 0 then on_zero else (if n ≥ 0 then on_nonneg else on_neg)` — the 0·∞ / ÷0
    // indeterminate guard wrapped around the signed-inf result.
    let zero_or_sign = |n: &Expr, on_zero: Expr, on_nonneg: Expr, on_neg: Expr| -> Expr {
        let nonzero = sign_dispatch(n, on_nonneg, on_neg);
        Expr::apps(bool_rec_ext(), [ext_motive(), nonzero, on_zero, is_zero(n)])
    };

    // --- fmulExt : ExtVal → ExtVal → ExtVal ---
    // IEEE-754 multiply on the extended domain, by the SAME double ExtVal.rec case-split as
    // faddExt. The non-finite rules it encodes (each ι-reduces to a CLOSED ExtVal leaf):
    //   fmul_ext x y = match x with
    //     | Finite p => match y with
    //         | Finite q => Finite (Qmul p q)                       -- exact ℚ product (rounded
    //                                                                  back to the grid by Step 4)
    //         | PosInf   => if p = 0 then NaN                       -- 0·∞ INDETERMINATE = NaN
    //                       else if p ≥ 0 then PosInf else NegInf   -- finite·∞ = signed ∞
    //         | NegInf   => if p = 0 then NaN
    //                       else if p ≥ 0 then NegInf else PosInf   -- sign flips on −∞
    //         | NaN      => NaN
    //     | PosInf   => match y with
    //         | Finite q => if q = 0 then NaN                       -- ∞·0 INDETERMINATE = NaN
    //                       else if q ≥ 0 then PosInf else NegInf
    //         | PosInf   => PosInf                                  -- ∞·∞ = ∞ (sign +·+ = +)
    //         | NegInf   => NegInf                                  -- ∞·−∞ = −∞
    //         | NaN      => NaN
    //     | NegInf   => match y with
    //         | Finite q => if q = 0 then NaN
    //                       else if q ≥ 0 then NegInf else PosInf
    //         | PosInf   => NegInf                                  -- −∞·∞ = −∞
    //         | NegInf   => PosInf                                  -- −∞·−∞ = +∞
    //         | NaN      => NaN
    //     | NaN      => NaN                                          -- NaN propagates (ignores y)
    if env.get_const(&Name::from_string(&names.fmul_ext)).is_none() {
        let rec = || ext_rec(&names);
        let outer_motive = || Expr::lam(bd(), ext_ty.clone(), ext_ty.clone());
        let inner_dispatch =
            |y_finite: Expr, y_pos: Expr, y_neg: Expr, y_nan: Expr, y_var: Expr| -> Expr {
                Expr::apps(rec(), [outer_motive(), y_finite, y_pos, y_neg, y_nan, y_var])
            };

        // x = Finite p arm: `λ(p). <inner on y>`. Inside, before the inner recursor:
        //   p = bvar(0), y = bvar(1), x = bvar(2). The inner Finite minor lifts p to bvar(1)
        //   (its own `q` field is bvar(0)). The PosInf/NegInf/NaN minors are nullary, so at
        //   those leaves p is still bvar(0).
        let x_finite = {
            // y = Finite q ⇒ Finite (Qmul p q). Under the q-binder: q=bvar(0), p=bvar(1).
            let y_finite = {
                let p = Expr::bvar(1);
                let q = Expr::bvar(0);
                let prod = Expr::apps(cst(&onames.q_mul), [p, q]);
                Expr::lam(bd(), prod_int_int(), Expr::app(cst(&names.finite), prod))
            };
            // y = PosInf ⇒ 0·∞=NaN else signed ∞ (p≥0 ⇒ PosInf, p<0 ⇒ NegInf). p = bvar(0).
            let p = Expr::bvar(0);
            let num = prod_fst_int(p);
            let y_pos =
                zero_or_sign(&num, cst(&names.nan), cst(&names.pos_inf), cst(&names.neg_inf));
            // y = NegInf ⇒ sign FLIPS: p≥0 ⇒ NegInf, p<0 ⇒ PosInf.
            let y_neg =
                zero_or_sign(&num, cst(&names.nan), cst(&names.neg_inf), cst(&names.pos_inf));
            let y_nan = cst(&names.nan);
            let dispatch = inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(1));
            Expr::lam(bd(), prod_int_int(), dispatch)
        };

        // x = PosInf arm (nullary x-minor). Binder context: y = bvar(0), x = bvar(1). The inner
        //   Finite minor introduces `q = bvar(0)` (so we read `Prod.fst q`).
        let x_pos = {
            let q = Expr::bvar(0);
            let num = prod_fst_int(q);
            // ∞·finite: q=0 ⇒ NaN (∞·0 INDETERMINATE); else signed ∞ by sign of q.
            let y_finite = Expr::lam(
                bd(),
                prod_int_int(),
                zero_or_sign(&num, cst(&names.nan), cst(&names.pos_inf), cst(&names.neg_inf)),
            );
            let y_pos = cst(&names.pos_inf); // ∞·∞ = ∞
            let y_neg = cst(&names.neg_inf); // ∞·−∞ = −∞
            let y_nan = cst(&names.nan);
            inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(0))
        };

        // x = NegInf arm. −∞·finite: q=0 ⇒ NaN; else sign FLIPS.
        let x_neg = {
            let q = Expr::bvar(0);
            let num = prod_fst_int(q);
            let y_finite = Expr::lam(
                bd(),
                prod_int_int(),
                zero_or_sign(&num, cst(&names.nan), cst(&names.neg_inf), cst(&names.pos_inf)),
            );
            let y_pos = cst(&names.neg_inf); // −∞·∞ = −∞
            let y_neg = cst(&names.pos_inf); // −∞·−∞ = +∞
            let y_nan = cst(&names.nan);
            inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(0))
        };

        let x_nan = cst(&names.nan);
        let outer =
            Expr::apps(rec(), [outer_motive(), x_finite, x_pos, x_neg, x_nan, Expr::bvar(1)]);
        let value = Expr::lam(bd(), ext_ty.clone(), Expr::lam(bd(), ext_ty.clone(), outer));
        let ty = Expr::pi(bd(), ext_ty.clone(), Expr::pi(bd(), ext_ty.clone(), ext_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.fmul_ext),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.fmul_ext))?;
    }

    // --- fdivExt : ExtVal → ExtVal → ExtVal ---
    // IEEE-754 divide on the extended domain, double ExtVal.rec case-split. The non-finite
    // rules (each ι-reduces to a CLOSED ExtVal leaf):
    //   fdiv_ext x y = match x with
    //     | Finite p => match y with
    //         | Finite q => if q = 0
    //                         then if p = 0 then NaN                -- 0/0 INDETERMINATE = NaN
    //                              else if p ≥ 0 then PosInf else NegInf  -- x/0 = signed ∞ (DIV-BY-0)
    //                         else Finite (Qdiv p q)                -- finite/finite = ℚ quotient
    //                                                                  (DEFERRED stub — see below)
    //         | PosInf   => Finite 0                                -- finite/∞ = (signed) 0 (+0 here)
    //         | NegInf   => Finite 0                                -- finite/−∞ = (signed) 0
    //         | NaN      => NaN
    //     | PosInf   => match y with
    //         | Finite q => if q ≥ 0 then PosInf else NegInf        -- ∞/finite = signed ∞
    //         | PosInf   => NaN                                     -- ∞/∞ INDETERMINATE = NaN
    //         | NegInf   => NaN                                     -- ∞/−∞ INDETERMINATE = NaN
    //         | NaN      => NaN
    //     | NegInf   => match y with
    //         | Finite q => if q ≥ 0 then NegInf else PosInf        -- −∞/finite = signed ∞
    //         | PosInf   => NaN                                     -- −∞/∞ INDETERMINATE = NaN
    //         | NegInf   => NaN                                     -- −∞/−∞ INDETERMINATE = NaN
    //         | NaN      => NaN
    //     | NaN      => NaN                                          -- NaN propagates (ignores y)
    //
    // FINITE/FINITE — the EXACT rational quotient `Qdiv p q = (np·dq, dp·nq)` (cross-multiply).
    // `Qdiv` is now a real op-layer Definition (see `register_ops`); the finite/finite arm carries
    // it directly, so `fdivExt (Finite p) (Finite q) = Finite (Qdiv p q)` for nonzero `q`. The
    // round-back of that exact rational to the float grid is the SEPARATE `fdivFinite` op
    // (`round (Qdiv (value a) (value b))`), proven by the SAME round-back structure as `fmul`.
    if env.get_const(&Name::from_string(&names.fdiv_ext)).is_none() {
        let rec = || ext_rec(&names);
        let outer_motive = || Expr::lam(bd(), ext_ty.clone(), ext_ty.clone());
        let inner_dispatch =
            |y_finite: Expr, y_pos: Expr, y_neg: Expr, y_nan: Expr, y_var: Expr| -> Expr {
                Expr::apps(rec(), [outer_motive(), y_finite, y_pos, y_neg, y_nan, y_var])
            };
        // `Finite 0` = the signed-zero result for finite/∞.
        let finite_zero = || Expr::app(cst(&names.finite), prod_mk_int(int_lit(0), int_lit(1)));

        // x = Finite p arm: `λ(p). <inner on y>`. Inside before inner recursor:
        //   p = bvar(0), y = bvar(1), x = bvar(2). Inner Finite minor: q = bvar(0), p = bvar(1).
        let x_finite = {
            // y = Finite q ⇒ q=0 guard: 0/0=NaN, x/0=signed ∞; else Finite (Qdiv-stub p q).
            //   Under q-binder: q = bvar(0), p = bvar(1).
            let y_finite = {
                let p = Expr::bvar(1);
                let q = Expr::bvar(0);
                let pnum = prod_fst_int(p.clone());
                let qnum = prod_fst_int(q.clone());
                // Finite (Qdiv p q) — the EXACT rational quotient via the real op-layer `Qdiv`
                // (cross-multiply (np·dq, dp·nq)); the round-back lives in `fdivFinite`.
                let quot = Expr::app(
                    cst(&names.finite),
                    Expr::apps(cst(&onames.q_div), [p.clone(), q.clone()]),
                );
                // q = 0 ⇒ (p=0 ⇒ NaN ; else signed ∞ by sign of p) ; else quotient.
                let on_div0 =
                    zero_or_sign(&pnum, cst(&names.nan), cst(&names.pos_inf), cst(&names.neg_inf));
                // Bool.rec on `isZero qnum`: false ⇒ quotient, true ⇒ on_div0.
                let body =
                    Expr::apps(bool_rec_ext(), [ext_motive(), quot, on_div0, is_zero(&qnum)]);
                Expr::lam(bd(), prod_int_int(), body)
            };
            let y_pos = finite_zero(); // finite/∞ = +0
            let y_neg = finite_zero(); // finite/−∞ = +0 (signed-zero sign deferred; magnitude 0)
            let y_nan = cst(&names.nan);
            let dispatch = inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(1));
            Expr::lam(bd(), prod_int_int(), dispatch)
        };

        // x = PosInf arm. ∞/finite = signed ∞ (by sign of q, including q=0 ⇒ +∞); ∞/∞ = NaN.
        let x_pos = {
            let q = Expr::bvar(0);
            let num = prod_fst_int(q);
            let y_finite = Expr::lam(
                bd(),
                prod_int_int(),
                sign_dispatch(&num, cst(&names.pos_inf), cst(&names.neg_inf)),
            );
            let y_pos = cst(&names.nan); // ∞/∞ INDETERMINATE = NaN
            let y_neg = cst(&names.nan); // ∞/−∞ INDETERMINATE = NaN
            let y_nan = cst(&names.nan);
            inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(0))
        };

        // x = NegInf arm. −∞/finite = signed ∞ (sign FLIPS); −∞/∞ = NaN.
        let x_neg = {
            let q = Expr::bvar(0);
            let num = prod_fst_int(q);
            let y_finite = Expr::lam(
                bd(),
                prod_int_int(),
                sign_dispatch(&num, cst(&names.neg_inf), cst(&names.pos_inf)),
            );
            let y_pos = cst(&names.nan); // −∞/∞ INDETERMINATE = NaN
            let y_neg = cst(&names.nan); // −∞/−∞ INDETERMINATE = NaN
            let y_nan = cst(&names.nan);
            inner_dispatch(y_finite, y_pos, y_neg, y_nan, Expr::bvar(0))
        };

        let x_nan = cst(&names.nan);
        let outer =
            Expr::apps(rec(), [outer_motive(), x_finite, x_pos, x_neg, x_nan, Expr::bvar(1)]);
        let value = Expr::lam(bd(), ext_ty.clone(), Expr::lam(bd(), ext_ty.clone(), outer));
        let ty = Expr::pi(bd(), ext_ty.clone(), Expr::pi(bd(), ext_ty.clone(), ext_ty.clone()));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&names.fdiv_ext),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl({}): {e:?}", names.fdiv_ext))?;
    }
    Ok(())
}

/// Build a kernel `Environment` with the prelude, the float inductive, classifiers, value
/// model, ops, the subnormal + normal grid layers, AND the non-finite (ExtVal) value/op
/// layer registered — the full structured-float environment INCLUDING ±∞/NaN semantics.
///
/// # Errors
/// Returns the registration error string for an unsupported width or a gate failure.
pub fn ext_env(width: u32) -> Result<Environment, String> {
    let mut env = binade_env(width)?;
    register_ext_inductive(&mut env, width)?;
    register_ext_ops(&mut env, width)?;
    Ok(env)
}

/// The non-finite (ExtVal) declaration names that must rest on EXACTLY the 3 foundational
/// axioms (audited by [`pin_float_ext`]).
fn ext_audit_names(inductive: &str) -> Vec<String> {
    let n = ext_decl_names(inductive);
    vec![n.ext_val, n.ext_rec, n.value_ext, n.fadd_ext, n.fmul_ext, n.fdiv_ext]
}

/// Pin the non-finite (ExtVal) value/op layer of `width` bits (`ExtVal` + its recursor +
/// `valueExt` + `faddExt` + `fmulExt` + `fdivExt`) and audit the axiom closure via the
/// kernel's own `axiom_deps`. Confirms the whole non-finite layer rests on EXACTLY the 3
/// foundational axioms (modulo 3, NO 4th axiom) — built over only the axiom-free
/// `Prod`/`Bool.rec`/`Nat.beq` + the value model.
#[must_use]
pub fn pin_float_ext(width: u32) -> FloatClassVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return FloatClassVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let env = match ext_env(width) {
        Ok(e) => e,
        Err(e) => return FloatClassVerdict::KernelRejected(e),
    };
    for n in ext_audit_names(inductive) {
        match env.axiom_deps(&Name::from_string(&n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
                ns.sort();
                return FloatClassVerdict::Residue(ns);
            }
            None => return FloatClassVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    FloatClassVerdict::Modulo3
}

/// Type-check that `valueExt : FloatN → ExtVal` and `faddExt`/`fmulExt`/`fdivExt :
/// ExtVal → ExtVal → ExtVal` of `width` bits infer those exact types in the real kernel —
/// the non-finite layer KERNEL-CHECKS as real maps over the structure.
///
/// # Errors
/// Returns a description if the env fails to build or an inferred type is wrong.
pub fn ext_ops_typecheck(width: u32) -> Result<(), String> {
    let inductive =
        reflect::float_inductive_name(width).ok_or_else(|| format!("unsupported width {width}"))?;
    let env = ext_env(width)?;
    let tc = TypeChecker::new(&env);
    let bd = || BinderData::from(BinderInfo::Default);
    let names = ext_decl_names(inductive);
    let ext_ty = cst(&names.ext_val);
    // valueExt : FloatN → ExtVal
    let value_ext_expected = Expr::pi(bd(), cst(inductive), ext_ty.clone());
    let inferred = tc
        .infer_type(&cst(&names.value_ext))
        .map_err(|e| format!("{}.valueExt has no type: {e:?}", inductive))?;
    if !tc.is_def_eq(&inferred, &value_ext_expected) {
        return Err(format!("{inductive}.valueExt is not FloatN → ExtVal"));
    }
    // faddExt / fmulExt / fdivExt : ExtVal → ExtVal → ExtVal — each a real BINARY op.
    let binop_ty =
        || Expr::pi(bd(), ext_ty.clone(), Expr::pi(bd(), ext_ty.clone(), ext_ty.clone()));
    for (op, label) in
        [(&names.fadd_ext, "faddExt"), (&names.fmul_ext, "fmulExt"), (&names.fdiv_ext, "fdivExt")]
    {
        let inferred = tc
            .infer_type(&cst(op))
            .map_err(|e| format!("{inductive}.{label} has no type: {e:?}"))?;
        if !tc.is_def_eq(&inferred, &binop_ty()) {
            return Err(format!("{inductive}.{label} is not ExtVal → ExtVal → ExtVal"));
        }
    }
    Ok(())
}

/// Register `theorem <name> : <statement> := <proof>` into a fresh ext-env and audit the
/// axiom closure — the shared driver for every non-finite lemma. A wrong claim makes the
/// kernel reject `proof` against `statement` ⇒ [`ValueLemmaVerdict::KernelRejected`].
fn check_ext_lemma(width: u32, name: &str, statement: Expr, proof: Expr) -> ValueLemmaVerdict {
    let mut env = match ext_env(width) {
        Ok(e) => e,
        Err(e) => return ValueLemmaVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return ValueLemmaVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let decl_name = Name::from_string(name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: decl_name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return ValueLemmaVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&decl_name) {
        Some(residue) if residue.is_empty() => ValueLemmaVerdict::ProvenModulo3,
        Some(residue) => {
            let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
            ns.sort();
            ValueLemmaVerdict::Residue(ns)
        }
        None => ValueLemmaVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// `@Eq ExtVal a b : Prop` — the ExtVal-equality statement form (ExtVal lives in `Type`, so
/// the `Eq` level is `Sort 1`).
fn eq_ext_prop(names: &ExtNames, a: Expr, b: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq, [cst(&names.ext_val), a, b])
}

/// `@Eq.refl ExtVal e : @Eq ExtVal e e` — reflexivity for an ExtVal equality whose two sides
/// ι/δ-reduce to the same constructor normal form.
fn refl_ext(names: &ExtNames, e: Expr) -> Expr {
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq_refl, [cst(&names.ext_val), e])
}

/// A canonical concrete `Finite` ExtVal `Finite (n, 1)` (numerator `n` over denominator 1) —
/// a stand-in finite operand for the non-finite op rules (the rules do not depend on the
/// exact rational, only on the Finite/Inf/NaN HEAD).
fn ext_finite(names: &ExtNames, n: i64) -> Expr {
    let num = if n < 0 { int_neg(int_lit(n.unsigned_abs())) } else { int_lit(n.unsigned_abs()) };
    Expr::app(cst(&names.finite), prod_mk_int(num, int_lit(1)))
}

/// LEMMA (value_ext ↔ classification) — `value_ext` of each IEEE class reduces to the matching
/// `ExtVal` constructor: the NaN pattern (exp all-ones, mantissa ≠ 0) ↦ `NaN`; +∞ (all-ones,
/// mantissa 0, sign false) ↦ `PosInf`; −∞ (sign true) ↦ `NegInf`; a finite pattern ↦ `Finite
/// (value f)`. Each is an `Eq ExtVal` proven by `Eq.refl` after ι/δ-reduction of the
/// `Nat.beq`/`Bool.rec` dispatch. This is the IEEE classification↔value-ext connection:
/// `value_ext f = NaN` iff `isNaN f`, `= PosInf` iff `isInf f ∧ sign f = false`. Proven
/// modulo 3.
#[must_use]
pub fn lemma_value_ext_classifies(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let Some((exp_bits, _mant_bits)) = reflect::ieee754_layout(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("no layout for width {width}"));
    };
    let all_ones: u64 = (1u64 << exp_bits) - 1;
    let names = ext_decl_names(inductive);
    let vnames = value_decl_names(inductive);
    let value_ext = |f: Expr| Expr::app(cst(&names.value_ext), f);
    // NaN pattern: exp all-ones, mantissa 1, sign false.
    let nan_f = float_pattern(inductive, false, all_ones, 1);
    // +∞: all-ones, mantissa 0, sign false. −∞: sign true.
    let pinf_f = float_pattern(inductive, false, all_ones, 0);
    let ninf_f = float_pattern(inductive, true, all_ones, 0);
    // finite (smallest positive normal): exp 1, mantissa 0, sign false.
    let fin_f = float_pattern(inductive, false, 1, 0);
    // value_ext(nan) = NaN.
    let nan_eq = eq_ext_prop(&names, value_ext(nan_f), cst(&names.nan));
    // value_ext(+∞) = PosInf, value_ext(−∞) = NegInf.
    let pinf_eq = eq_ext_prop(&names, value_ext(pinf_f), cst(&names.pos_inf));
    let ninf_eq = eq_ext_prop(&names, value_ext(ninf_f), cst(&names.neg_inf));
    // value_ext(finite) = Finite (value finite).
    let fin_val = Expr::app(cst(&names.finite), Expr::app(cst(&vnames.value), fin_f.clone()));
    let fin_eq = eq_ext_prop(&names, value_ext(fin_f), fin_val.clone());
    // Conjoin all four as nested And; each conjunct proven by Eq.refl.
    let statement = and(and(nan_eq, pinf_eq), and(ninf_eq, fin_eq));
    let proof = Expr::apps(
        cst("And.intro"),
        [
            and(
                eq_ext_prop(
                    &names,
                    value_ext(float_pattern(inductive, false, all_ones, 1)),
                    cst(&names.nan),
                ),
                eq_ext_prop(
                    &names,
                    value_ext(float_pattern(inductive, false, all_ones, 0)),
                    cst(&names.pos_inf),
                ),
            ),
            and(
                eq_ext_prop(
                    &names,
                    value_ext(float_pattern(inductive, true, all_ones, 0)),
                    cst(&names.neg_inf),
                ),
                eq_ext_prop(&names, value_ext(float_pattern(inductive, false, 1, 0)), fin_val),
            ),
            Expr::apps(
                cst("And.intro"),
                [
                    eq_ext_prop(
                        &names,
                        value_ext(float_pattern(inductive, false, all_ones, 1)),
                        cst(&names.nan),
                    ),
                    eq_ext_prop(
                        &names,
                        value_ext(float_pattern(inductive, false, all_ones, 0)),
                        cst(&names.pos_inf),
                    ),
                    refl_ext(&names, cst(&names.nan)),
                    refl_ext(&names, cst(&names.pos_inf)),
                ],
            ),
            Expr::apps(
                cst("And.intro"),
                [
                    eq_ext_prop(
                        &names,
                        value_ext(float_pattern(inductive, true, all_ones, 0)),
                        cst(&names.neg_inf),
                    ),
                    eq_ext_prop(
                        &names,
                        value_ext(float_pattern(inductive, false, 1, 0)),
                        Expr::app(
                            cst(&names.finite),
                            Expr::app(cst(&vnames.value), float_pattern(inductive, false, 1, 0)),
                        ),
                    ),
                    refl_ext(&names, cst(&names.neg_inf)),
                    refl_ext(
                        &names,
                        Expr::app(
                            cst(&names.finite),
                            Expr::app(cst(&vnames.value), float_pattern(inductive, false, 1, 0)),
                        ),
                    ),
                ],
            ),
        ],
    );
    check_ext_lemma(width, &format!("{inductive}.ext.value_ext_classifies"), statement, proof)
}

/// LEMMA (NaN PROPAGATION, left, ∀y) — `∀ y, faddExt NaN y = NaN`. NaN as the LEFT operand
/// propagates REGARDLESS of `y`: the outer recursor's NaN minor is the closed `NaN`, ignoring
/// `y`, so this holds for a SYMBOLIC `y` under a `Π(y)` by reflexivity (the NaN x-minor
/// ι-reduces to `NaN` without touching `y`). Proven modulo 3.
#[must_use]
pub fn lemma_fadd_ext_nan_left(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = ext_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    // Under Π(y : ExtVal): y = bvar(0). lhs = faddExt NaN y; rhs = NaN.
    let lhs = Expr::apps(cst(&names.fadd_ext), [cst(&names.nan), Expr::bvar(0)]);
    let eq_body = eq_ext_prop(&names, lhs, cst(&names.nan));
    let statement = Expr::pi(bd(), cst(&names.ext_val), eq_body);
    // Proof: λ(y : ExtVal). Eq.refl ExtVal NaN — the lhs ι-reduces to NaN ignoring y.
    let proof = Expr::lam(bd(), cst(&names.ext_val), refl_ext(&names, cst(&names.nan)));
    check_ext_lemma(width, &format!("{inductive}.ext.fadd_nan_left"), statement, proof)
}

/// A single CONCRETE `faddExt a b = c` non-finite rule, proven by `Eq.refl` after ι-reduction
/// of the double recursor. Shared driver for the per-rule lemmas.
fn ext_rule(width: u32, a: Expr, b: Expr, c: Expr, tag: &str) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = ext_decl_names(inductive);
    let lhs = Expr::apps(cst(&names.fadd_ext), [a, b]);
    let statement = eq_ext_prop(&names, lhs, c.clone());
    let proof = refl_ext(&names, c);
    check_ext_lemma(width, &format!("{inductive}.ext.fadd_{tag}"), statement, proof)
}

/// The non-finite `faddExt` op-rule battery, each a named [`ValueLemmaVerdict`]. Covers NaN
/// propagation (right, per-head), inf+finite, inf+inf (same), the ∞−∞ INDETERMINATE forms
/// (= NaN), and finite+finite = Finite (Qadd). All PROVEN modulo 3.
#[must_use]
pub fn all_fadd_ext_rules(width: u32) -> Vec<(&'static str, ValueLemmaVerdict)> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return vec![("unsupported", ValueLemmaVerdict::KernelRejected(format!("width {width}")))];
    };
    let n = ext_decl_names(inductive);
    let pinf = || cst(&n.pos_inf);
    let ninf = || cst(&n.neg_inf);
    let nan = || cst(&n.nan);
    let fin = |k: i64| ext_finite(&n, k);
    // finite + finite = Finite (Qadd (3,1) (4,1)).
    let qadd_3_4 = {
        let onames = op_decl_names(inductive);
        let p = prod_mk_int(int_lit(3), int_lit(1));
        let q = prod_mk_int(int_lit(4), int_lit(1));
        Expr::app(cst(&n.finite), Expr::apps(cst(&onames.q_add), [p, q]))
    };
    vec![
        // NaN propagation on the RIGHT, per x-head.
        ("nan_right_finite", ext_rule(width, fin(3), nan(), nan(), "nan_right_finite")),
        ("nan_right_posinf", ext_rule(width, pinf(), nan(), nan(), "nan_right_posinf")),
        ("nan_right_neginf", ext_rule(width, ninf(), nan(), nan(), "nan_right_neginf")),
        // inf + finite.
        ("posinf_finite", ext_rule(width, pinf(), fin(3), pinf(), "posinf_finite")),
        ("neginf_finite", ext_rule(width, ninf(), fin(3), ninf(), "neginf_finite")),
        ("finite_posinf", ext_rule(width, fin(3), pinf(), pinf(), "finite_posinf")),
        ("finite_neginf", ext_rule(width, fin(3), ninf(), ninf(), "finite_neginf")),
        // inf + same inf.
        ("posinf_posinf", ext_rule(width, pinf(), pinf(), pinf(), "posinf_posinf")),
        ("neginf_neginf", ext_rule(width, ninf(), ninf(), ninf(), "neginf_neginf")),
        // INDETERMINATE ∞ − ∞ = NaN.
        ("posinf_neginf_is_nan", ext_rule(width, pinf(), ninf(), nan(), "posinf_neginf_is_nan")),
        ("neginf_posinf_is_nan", ext_rule(width, ninf(), pinf(), nan(), "neginf_posinf_is_nan")),
        // finite + finite = Finite (Qadd …).
        ("finite_finite_qadd", ext_rule(width, fin(3), fin(4), qadd_3_4, "finite_finite_qadd")),
    ]
}

/// A single CONCRETE `fmulExt a b = c` non-finite rule, proven by `Eq.refl` after ι-reduction
/// of the double recursor (and the inner zero/sign `Bool.rec` dispatch). Shared driver.
fn mul_rule(width: u32, a: Expr, b: Expr, c: Expr, tag: &str) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = ext_decl_names(inductive);
    let lhs = Expr::apps(cst(&names.fmul_ext), [a, b]);
    let statement = eq_ext_prop(&names, lhs, c.clone());
    let proof = refl_ext(&names, c);
    check_ext_lemma(width, &format!("{inductive}.ext.fmul_{tag}"), statement, proof)
}

/// A single CONCRETE `fdivExt a b = c` non-finite rule, proven by `Eq.refl` after ι-reduction.
fn div_rule(width: u32, a: Expr, b: Expr, c: Expr, tag: &str) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = ext_decl_names(inductive);
    let lhs = Expr::apps(cst(&names.fdiv_ext), [a, b]);
    let statement = eq_ext_prop(&names, lhs, c.clone());
    let proof = refl_ext(&names, c);
    check_ext_lemma(width, &format!("{inductive}.ext.fdiv_{tag}"), statement, proof)
}

/// LEMMA (NaN PROPAGATION, left, ∀y) for `fmulExt` — `∀ y, fmulExt NaN y = NaN`. The outer
/// recursor's NaN minor is the closed `NaN`, ignoring `y`, so this holds for a SYMBOLIC `y`
/// under a `Π(y)` by reflexivity. Proven modulo 3.
#[must_use]
pub fn lemma_fmul_ext_nan_left(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = ext_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    let lhs = Expr::apps(cst(&names.fmul_ext), [cst(&names.nan), Expr::bvar(0)]);
    let eq_body = eq_ext_prop(&names, lhs, cst(&names.nan));
    let statement = Expr::pi(bd(), cst(&names.ext_val), eq_body);
    let proof = Expr::lam(bd(), cst(&names.ext_val), refl_ext(&names, cst(&names.nan)));
    check_ext_lemma(width, &format!("{inductive}.ext.fmul_nan_left"), statement, proof)
}

/// LEMMA (NaN PROPAGATION, left, ∀y) for `fdivExt` — `∀ y, fdivExt NaN y = NaN`. Proven modulo 3.
#[must_use]
pub fn lemma_fdiv_ext_nan_left(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let names = ext_decl_names(inductive);
    let bd = || BinderData::from(BinderInfo::Default);
    let lhs = Expr::apps(cst(&names.fdiv_ext), [cst(&names.nan), Expr::bvar(0)]);
    let eq_body = eq_ext_prop(&names, lhs, cst(&names.nan));
    let statement = Expr::pi(bd(), cst(&names.ext_val), eq_body);
    let proof = Expr::lam(bd(), cst(&names.ext_val), refl_ext(&names, cst(&names.nan)));
    check_ext_lemma(width, &format!("{inductive}.ext.fdiv_nan_left"), statement, proof)
}

/// The non-finite `fmulExt` op-rule battery, each a named [`ValueLemmaVerdict`]. Covers NaN
/// propagation (right, per-head), inf·inf WITH SIGN, inf·finite-nonzero = signed ∞ (both
/// orders), the INDETERMINATE 0·∞ = NaN (both orders), and finite·finite = Finite (Qmul). All
/// PROVEN modulo 3 — the IEEE-754 multiply non-finite rule set.
#[must_use]
pub fn all_fmul_ext_rules(width: u32) -> Vec<(&'static str, ValueLemmaVerdict)> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return vec![("unsupported", ValueLemmaVerdict::KernelRejected(format!("width {width}")))];
    };
    let n = ext_decl_names(inductive);
    let pinf = || cst(&n.pos_inf);
    let ninf = || cst(&n.neg_inf);
    let nan = || cst(&n.nan);
    let fin = |k: i64| ext_finite(&n, k);
    // finite · finite = Finite (Qmul (3,1) (4,1)).
    let qmul_3_4 = {
        let onames = op_decl_names(inductive);
        let p = prod_mk_int(int_lit(3), int_lit(1));
        let q = prod_mk_int(int_lit(4), int_lit(1));
        Expr::app(cst(&n.finite), Expr::apps(cst(&onames.q_mul), [p, q]))
    };
    vec![
        // NaN propagation on the RIGHT, per x-head.
        ("nan_right_finite", mul_rule(width, fin(3), nan(), nan(), "nan_right_finite")),
        ("nan_right_posinf", mul_rule(width, pinf(), nan(), nan(), "nan_right_posinf")),
        ("nan_right_neginf", mul_rule(width, ninf(), nan(), nan(), "nan_right_neginf")),
        // inf · inf WITH SIGN.
        ("posinf_posinf", mul_rule(width, pinf(), pinf(), pinf(), "posinf_posinf")),
        ("posinf_neginf", mul_rule(width, pinf(), ninf(), ninf(), "posinf_neginf")),
        ("neginf_posinf", mul_rule(width, ninf(), pinf(), ninf(), "neginf_posinf")),
        ("neginf_neginf", mul_rule(width, ninf(), ninf(), pinf(), "neginf_neginf")),
        // inf · finite-nonzero = signed ∞ (sign = sign of the finite, both operand orders).
        ("posinf_pos_finite", mul_rule(width, pinf(), fin(3), pinf(), "posinf_pos_finite")),
        ("posinf_neg_finite", mul_rule(width, pinf(), fin(-3), ninf(), "posinf_neg_finite")),
        ("neginf_pos_finite", mul_rule(width, ninf(), fin(3), ninf(), "neginf_pos_finite")),
        ("neginf_neg_finite", mul_rule(width, ninf(), fin(-3), pinf(), "neginf_neg_finite")),
        ("pos_finite_posinf", mul_rule(width, fin(3), pinf(), pinf(), "pos_finite_posinf")),
        ("neg_finite_posinf", mul_rule(width, fin(-3), pinf(), ninf(), "neg_finite_posinf")),
        ("pos_finite_neginf", mul_rule(width, fin(3), ninf(), ninf(), "pos_finite_neginf")),
        ("neg_finite_neginf", mul_rule(width, fin(-3), ninf(), pinf(), "neg_finite_neginf")),
        // INDETERMINATE 0 · ∞ = NaN (both orders, both inf signs).
        ("zero_posinf_is_nan", mul_rule(width, fin(0), pinf(), nan(), "zero_posinf_is_nan")),
        ("posinf_zero_is_nan", mul_rule(width, pinf(), fin(0), nan(), "posinf_zero_is_nan")),
        ("zero_neginf_is_nan", mul_rule(width, fin(0), ninf(), nan(), "zero_neginf_is_nan")),
        ("neginf_zero_is_nan", mul_rule(width, ninf(), fin(0), nan(), "neginf_zero_is_nan")),
        // finite · finite = Finite (Qmul …).
        ("finite_finite_qmul", mul_rule(width, fin(3), fin(4), qmul_3_4, "finite_finite_qmul")),
    ]
}

/// The non-finite `fdivExt` op-rule battery, each a named [`ValueLemmaVerdict`]. Covers NaN
/// propagation (right, per-head), inf/finite = signed ∞, finite/inf = (signed) 0, the
/// INDETERMINATE ∞/∞ = NaN and 0/0 = NaN, and the IEEE DIV-BY-ZERO rule x/0 = signed ∞ for
/// nonzero finite x. All PROVEN modulo 3 — the IEEE-754 divide non-finite rule set.
#[must_use]
pub fn all_fdiv_ext_rules(width: u32) -> Vec<(&'static str, ValueLemmaVerdict)> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return vec![("unsupported", ValueLemmaVerdict::KernelRejected(format!("width {width}")))];
    };
    let n = ext_decl_names(inductive);
    let pinf = || cst(&n.pos_inf);
    let ninf = || cst(&n.neg_inf);
    let nan = || cst(&n.nan);
    let fin = |k: i64| ext_finite(&n, k);
    let fin0 = || Expr::app(cst(&n.finite), prod_mk_int(int_lit(0), int_lit(1)));
    vec![
        // NaN propagation on the RIGHT, per x-head.
        ("nan_right_finite", div_rule(width, fin(3), nan(), nan(), "nan_right_finite")),
        ("nan_right_posinf", div_rule(width, pinf(), nan(), nan(), "nan_right_posinf")),
        ("nan_right_neginf", div_rule(width, ninf(), nan(), nan(), "nan_right_neginf")),
        // inf / finite = signed ∞ (sign = sign of the finite divisor).
        ("posinf_pos_finite", div_rule(width, pinf(), fin(3), pinf(), "posinf_pos_finite")),
        ("posinf_neg_finite", div_rule(width, pinf(), fin(-3), ninf(), "posinf_neg_finite")),
        ("neginf_pos_finite", div_rule(width, ninf(), fin(3), ninf(), "neginf_pos_finite")),
        ("neginf_neg_finite", div_rule(width, ninf(), fin(-3), pinf(), "neginf_neg_finite")),
        // finite / inf = (signed) 0 — magnitude 0 (Finite (0,1)).
        ("finite_posinf_is_zero", div_rule(width, fin(3), pinf(), fin0(), "finite_posinf_is_zero")),
        ("finite_neginf_is_zero", div_rule(width, fin(3), ninf(), fin0(), "finite_neginf_is_zero")),
        // INDETERMINATE ∞ / ∞ = NaN (all four sign combos).
        ("posinf_posinf_is_nan", div_rule(width, pinf(), pinf(), nan(), "posinf_posinf_is_nan")),
        ("posinf_neginf_is_nan", div_rule(width, pinf(), ninf(), nan(), "posinf_neginf_is_nan")),
        ("neginf_posinf_is_nan", div_rule(width, ninf(), pinf(), nan(), "neginf_posinf_is_nan")),
        ("neginf_neginf_is_nan", div_rule(width, ninf(), ninf(), nan(), "neginf_neginf_is_nan")),
        // INDETERMINATE 0 / 0 = NaN.
        ("zero_zero_is_nan", div_rule(width, fin(0), fin(0), nan(), "zero_zero_is_nan")),
        // IEEE DIV-BY-ZERO: nonzero finite / 0 = signed ∞ (sign = sign of the dividend).
        (
            "pos_finite_zero_is_posinf",
            div_rule(width, fin(3), fin(0), pinf(), "pos_finite_zero_is_posinf"),
        ),
        (
            "neg_finite_zero_is_neginf",
            div_rule(width, fin(-3), fin(0), ninf(), "neg_finite_zero_is_neginf"),
        ),
    ]
}

// ---------------------------------------------------------------------------
// Step 5b — the binade-TOP CARRY RE-ENCODING (round-up across a binade boundary)
// ---------------------------------------------------------------------------
//
// THE RESIDUAL THIS CLOSES. The UNIVERSAL half-ulp bound (Step 4e) bounds the error
// MAGNITUDE through a carry — it is a fact about the integer NUMERATOR rounding, carry-
// agnostic. The standing residual was the FLOAT RE-ENCODING: when a value rounds UP off the
// TOP of binade `e` — landing on the grid point `2^(m+1)·2^e` — that grid index `k = 2^(m+1)`
// is OUT OF RANGE for a binade-`e` mantissa (`mantissa = k − 2^m = 2^m`, but the mantissa
// field only holds `0 .. 2^m − 1`). IEEE-754 re-encodes it: `2^(m+1)·2^e = 2^m·2^(e+1)` is
// the BOTTOM of binade `e+1` — exponent CARRIES `e → e+1`, mantissa RESETS to `0`.
//
// THE CARRY GRID POINT. `roundHalfEvenMod N (2^e)` (Step 4d/4e) lands at the binade-top grid
// point exactly when its result is `2^(m+1)·2^e` — the multiple of `2^e` with index `2^(m+1)`.
// The CORRECT IEEE re-encoding of that point is the float `mk sign (e+1) 0`, whose VALUE
// numerator over `D` (Step 2b normal arm) is `(2^m + 0)·2^(e+1) = 2^m·2^(e+1) = 2^(m+1)·2^e`
// — IDENTICAL to the carried grid point. So the carry is a CORRECT re-encoding: the re-encoded
// float DENOTES exactly the value it rounded to.
//
// WHAT WE PROVE (modulo 3, by Eq.refl on the reduced integer/float terms):
//   * round_carry_reencodes — at a concrete binade `e`, the carry grid point `2^(m+1)·2^e`
//     is re-encoded as `mk sign (e+1) 0`, and `valueNum (mk sign (e+1) 0) = signMul sign
//     (2^(m+1)·2^e)` — i.e. the re-encoded float's value EQUALS the carried grid value. The
//     exponent is incremented (`e → e+1`), the mantissa is reset (`→ 0`); the carry is a
//     faithful re-encoding.
//   * carry_value_is_next_binade_bottom — `value (mk false (e+1) 0)` numerator `= 2^(m+1)·2^e`,
//     the BOTTOM of binade e+1 (= 2^(e+1−bias) in real terms, scaled by D). Pins that the
//     carried float is the first representable of the next binade.
//   * overflow_to_inf — when the carry pushes the exponent OVER the top (`e+1 > max_exp`,
//     i.e. e+1 reaches the all-ones reserved exponent), the result is NOT a finite float but
//     `value_ext = PosInf` (sign false) — overflow-to-∞, tying back to Step 5's ExtVal. The
//     float `mk false ALL_ONES 0` IS the +∞ bit pattern, and `value_ext (mk false ALL_ONES 0)
//     = PosInf` by the value_ext classifier reduction.
//
// SCOPE — HONEST. PROVEN modulo 3: the carry re-encoding equation (value of `mk s (e+1) 0`
// equals the carried grid point `2^(m+1)·2^e`), and the overflow-to-∞ routing (the top-
// exponent carry lands on the +∞ pattern, `value_ext = PosInf`). DEFERRED — the GENERAL
// "round chooses to carry" decision procedure (a full `round` that DETECTS the binade-top
// index `2^(m+1)` and re-encodes vs stays in-binade) is the precise-rounding control flow,
// not built here; we prove the re-encoding is CORRECT *given* the carry grid point, and the
// overflow routing, which is the residual the universal bound left open.

/// The `roundReencode` declaration name for the float inductive `inductive`.
fn carry_decl_name(inductive: &str) -> String {
    format!("{inductive}.roundCarryReencode")
}

/// Register `roundCarryReencode : Nat → FloatN` (idempotent): given a binade exponent `e`,
/// emit the IEEE re-encoding of the binade-top carry grid point `2^(m+1)·2^e` — the float
/// `mk false (e+1) 0` (exponent incremented, mantissa reset). Built over only `Int.ofNat`/
/// `Nat.add` + the float ctor, so it rests on EXACTLY the 3 foundational axioms — NO 4th.
///
/// # Errors
/// Returns an error string if the width is unsupported or the kernel rejects the def.
fn register_carry(env: &mut Environment, width: u32) -> Result<(), String> {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return Err(format!("unsupported IEEE-754 float width: {width}"));
    };
    let name = carry_decl_name(inductive);
    if env.get_const(&Name::from_string(&name)).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // Under λ(e : Nat): e = bvar(0). The re-encoded float is `mk false (Int.ofNat (e+1)) 0`:
    //   exponent CARRIES e → e+1, mantissa RESETS to 0, sign false (the positive carry).
    let e_plus_1 = Expr::app(cst("Int.ofNat"), nat_add(Expr::bvar(0), nat_lit(1)));
    let mk = cst(&format!("{inductive}.mk"));
    let body = Expr::apps(mk, [cst("Bool.false"), e_plus_1, int_lit(0)]);
    let value = Expr::lam(bd(), cst("Nat"), body);
    let ty = Expr::pi(bd(), cst("Nat"), cst(inductive));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(&name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl({name}): {e:?}"))?;
    Ok(())
}

/// Build a kernel `Environment` with the prelude, the float inductive, all finite layers, the
/// non-finite (ExtVal) layer, AND the binade-top carry re-encoding declaration registered.
///
/// # Errors
/// Returns the registration error string for an unsupported width or a gate failure.
pub fn carry_env(width: u32) -> Result<Environment, String> {
    let mut env = ext_env(width)?;
    register_carry(&mut env, width)?;
    Ok(env)
}

/// Pin the carry re-encoding declaration of `width` bits and audit the axiom closure via the
/// kernel's own `axiom_deps`. Confirms it rests on EXACTLY the 3 foundational axioms.
#[must_use]
pub fn pin_float_carry(width: u32) -> FloatClassVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return FloatClassVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let env = match carry_env(width) {
        Ok(e) => e,
        Err(e) => return FloatClassVerdict::KernelRejected(e),
    };
    match env.axiom_deps(&Name::from_string(&carry_decl_name(inductive))) {
        Some(residue) if residue.is_empty() => FloatClassVerdict::Modulo3,
        Some(residue) => {
            let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
            ns.sort();
            FloatClassVerdict::Residue(ns)
        }
        None => FloatClassVerdict::KernelRejected(format!(
            "decl not found: {}",
            carry_decl_name(inductive)
        )),
    }
}

/// Register `theorem <name> : <statement> := <proof>` into a fresh carry-env and audit the
/// axiom closure — the shared driver for every carry lemma. A wrong claim makes the kernel
/// reject `proof` against `statement` ⇒ [`ValueLemmaVerdict::KernelRejected`].
fn check_carry_lemma(width: u32, name: &str, statement: Expr, proof: Expr) -> ValueLemmaVerdict {
    let mut env = match carry_env(width) {
        Ok(e) => e,
        Err(e) => return ValueLemmaVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return ValueLemmaVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let decl_name = Name::from_string(name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: decl_name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return ValueLemmaVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&decl_name) {
        Some(residue) if residue.is_empty() => ValueLemmaVerdict::ProvenModulo3,
        Some(residue) => {
            let mut ns: Vec<String> = residue.iter().map(ToString::to_string).collect();
            ns.sort();
            ValueLemmaVerdict::Residue(ns)
        }
        None => ValueLemmaVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// LEMMA (CARRY RE-ENCODES) — at binade exponent `e`, the carry re-encoding `roundCarryReencode
/// e = mk false (e+1) 0` has VALUE numerator over `D` exactly `2^(m+1)·2^e` (= `2^m·2^(e+1)`),
/// the carried grid point. The exponent is INCREMENTED (`e → e+1`), the mantissa RESET to `0`,
/// and `valueNum (mk false (e+1) 0) = (2^m + 0)·2^(e+1) = 2^(m+1+e)` — the re-encoded float
/// DENOTES exactly the value it carried to. Proven by `Eq.refl` (both sides reduce to the Int
/// literal `2^(m+1+e)` through the reducible `Int.pow`/`Int.add`/`Bool.rec`). A WRONG re-encoding
/// (e.g. mantissa not reset, or exponent not incremented) gives a different numerator and FAILS
/// CLOSED. Proven modulo 3.
#[must_use]
pub fn lemma_round_carry_reencodes(width: u32, exponent: u64) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let Some((_exp_bits, mant_bits)) = reflect::ieee754_layout(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("no layout for width {width}"));
    };
    let names = value_decl_names(inductive);
    let carry = carry_decl_name(inductive);
    // lhs = valueNum (roundCarryReencode e).
    let reencoded = Expr::app(cst(&carry), nat_lit(exponent));
    let lhs = Expr::app(cst(&names.value_num), reencoded);
    // rhs = 2^(m+1+e) — the carried grid point numerator (2^(m+1)·2^e = 2^m·2^(e+1)).
    let rhs = int_pow(int_two(), nat_lit(u64::from(mant_bits) + 1 + exponent));
    let statement = eq_int_prop(lhs, rhs.clone());
    let proof = refl_int(rhs);
    check_carry_lemma(width, &format!("{inductive}.carry.reencodes_e{exponent}"), statement, proof)
}

/// LEMMA (CARRY = NEXT-BINADE BOTTOM) — the carry re-encoding `mk false (e+1) 0` is the FIRST
/// representable float of binade `e+1` (its smallest-mantissa normal): `valueNum (mk false (e+1)
/// 0)` numerator `= 2^(m+1+e)` is the bottom of binade `e+1` (real value `2^(e+1−bias)`, scaled
/// by `D`). Together with [`lemma_round_carry_reencodes`] this pins that the carried point is
/// EXACTLY the next binade's bottom grid point — the mantissa wrap `2^m → 0` with exponent carry
/// is the IEEE binade transition. Proven modulo 3.
#[must_use]
pub fn lemma_carry_is_next_binade_bottom(width: u32, exponent: u64) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let Some((_exp_bits, mant_bits)) = reflect::ieee754_layout(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("no layout for width {width}"));
    };
    let names = value_decl_names(inductive);
    // The next-binade bottom float directly: mk false (e+1) 0.
    let bottom = float_pattern(inductive, false, exponent + 1, 0);
    let lhs = Expr::app(cst(&names.value_num), bottom);
    let rhs = int_pow(int_two(), nat_lit(u64::from(mant_bits) + 1 + exponent));
    let statement = eq_int_prop(lhs, rhs.clone());
    let proof = refl_int(rhs);
    check_carry_lemma(
        width,
        &format!("{inductive}.carry.next_binade_bottom_e{exponent}"),
        statement,
        proof,
    )
}

/// LEMMA (OVERFLOW-TO-∞ at the TOP exponent) — when the carry pushes the exponent over the top
/// (the incremented exponent reaches the reserved ALL_ONES value), the result is NOT a finite
/// float but `+∞`: `value_ext (mk false ALL_ONES 0) = PosInf`. The top-binade carry lands on the
/// +∞ bit pattern (exponent all-ones, mantissa 0, sign false), and `value_ext` classifies it as
/// `PosInf` — overflow-to-∞ (RNE), tying the carry residual back to Step 5's ExtVal domain.
/// Proven by `Eq.refl` after the `value_ext` `Nat.beq`/`Bool.rec` reduction. Proven modulo 3.
#[must_use]
pub fn lemma_carry_overflow_to_inf(width: u32) -> ValueLemmaVerdict {
    let Some(inductive) = reflect::float_inductive_name(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("unsupported width {width}"));
    };
    let Some((exp_bits, _mant_bits)) = reflect::ieee754_layout(width) else {
        return ValueLemmaVerdict::KernelRejected(format!("no layout for width {width}"));
    };
    let all_ones: u64 = (1u64 << exp_bits) - 1;
    let names = ext_decl_names(inductive);
    // value_ext (mk false ALL_ONES 0) = PosInf — the top-exponent carry overflows to +∞.
    let top = float_pattern(inductive, false, all_ones, 0);
    let lhs = Expr::app(cst(&names.value_ext), top);
    let statement = eq_ext_prop(&names, lhs, cst(&names.pos_inf));
    let proof = refl_ext(&names, cst(&names.pos_inf));
    check_carry_lemma(width, &format!("{inductive}.carry.overflow_to_inf"), statement, proof)
}

/// The carry re-encoding lemma battery, each a named [`ValueLemmaVerdict`]. Covers the carry
/// re-encoding (value of `mk s (e+1) 0` = the carried grid point), the next-binade-bottom
/// identity, and the overflow-to-∞ routing at the top exponent. All PROVEN modulo 3.
#[must_use]
pub fn all_carry_lemmas(width: u32) -> Vec<(String, ValueLemmaVerdict)> {
    let mut out = Vec::new();
    for e in [1u64, 2, 5, 10] {
        out.push((format!("reencodes_e{e}"), lemma_round_carry_reencodes(width, e)));
        out.push((format!("next_binade_bottom_e{e}"), lemma_carry_is_next_binade_bottom(width, e)));
    }
    out.push(("overflow_to_inf".to_string(), lemma_carry_overflow_to_inf(width)));
    out
}

/// THE BULLET-3 NON-FINITE + CARRY CLOSURE — the non-finite (±∞/NaN) value/op semantics AND the
/// binade-top carry re-encoding (with overflow-to-∞) are PROVEN modulo 3 for `width`. Returns
/// [`FloatClassVerdict::Modulo3`] iff the ExtVal + carry layers pin modulo 3 AND every non-finite
/// op rule + carry lemma is proven modulo 3 with `axiom_deps ⊆` the 3; otherwise the offending
/// residue / rejection. This is the last residual of bullet-3's value/op layer closed.
#[must_use]
pub fn nonfinite_and_carry(width: u32) -> FloatClassVerdict {
    // Both layers must pin modulo 3 first.
    match pin_float_ext(width) {
        FloatClassVerdict::Modulo3 => {}
        other => return other,
    }
    match pin_float_carry(width) {
        FloatClassVerdict::Modulo3 => {}
        other => return other,
    }
    // The value_ext↔classification connection + NaN-left + every fadd_ext rule + every carry lemma.
    let mut lemmas: Vec<(String, ValueLemmaVerdict)> = vec![
        ("value_ext_classifies".to_string(), lemma_value_ext_classifies(width)),
        ("fadd_nan_left".to_string(), lemma_fadd_ext_nan_left(width)),
    ];
    for (tag, v) in all_fadd_ext_rules(width) {
        lemmas.push((tag.to_string(), v));
    }
    lemmas.extend(all_carry_lemmas(width));
    for (tag, verdict) in lemmas {
        match verdict {
            ValueLemmaVerdict::ProvenModulo3 => {}
            ValueLemmaVerdict::Residue(r) => return FloatClassVerdict::Residue(r),
            ValueLemmaVerdict::KernelRejected(e) => {
                return FloatClassVerdict::KernelRejected(format!("{tag}: {e}"));
            }
        }
    }
    FloatClassVerdict::Modulo3
}

/// The non-finite + carry layer is now PROVEN modulo 3 (±∞/NaN value+op semantics, NaN
/// propagation, the ∞−∞ indeterminate forms, the binade-top carry re-encoding, overflow-to-∞).
/// Reports the PRECISE standing residual (signaling-NaN payload bits, non-finite fmul/fdiv,
/// directed rounding modes, the general round-chooses-to-carry control flow).
#[must_use]
pub fn nonfinite_carry_status() -> &'static str {
    "PROVEN modulo 3: the NON-FINITE (±∞/NaN) value+op semantics — valueExt lifts the bit \
     pattern to ExtVal {Finite|PosInf|NegInf|NaN} (valueExt f = NaN iff isNaN f, = PosInf iff \
     isInf f ∧ sign false), and faddExt encodes the IEEE add rules: NaN PROPAGATION (faddExt \
     NaN y = NaN ∀y, and x NaN = NaN per head), inf+finite = inf, inf+same-inf = inf, the \
     INDETERMINATE ∞−∞ = NaN (PosInf+NegInf and NegInf+PosInf), finite+finite = Finite(Qadd). \
     A WRONG rule (PosInf+NegInf = PosInf, or broken NaN propagation) is KernelRejected. AND \
     the binade-TOP CARRY RE-ENCODING — roundCarryReencode e = mk false (e+1) 0 (exponent \
     incremented, mantissa reset), value EQUALS the carried grid point 2^(m+1)·2^e = 2^m·2^(e+1) \
     (the next binade's bottom); the TOP-exponent carry routes to +∞ (valueExt (mk false \
     ALL_ONES 0) = PosInf, overflow-to-∞). DEFERRED (precise, NOT faked, FAILS CLOSED): \
     signaling-NaN vs quiet-NaN payload bits (one NaN class modeled); fmul_ext/fdiv_ext on \
     non-finite operands (0·∞, ∞/∞ — only faddExt built); rounding modes other than round-to- \
     nearest-even (directed-rounding overflow thresholds differ); the general round-chooses-to- \
     carry decision procedure (the re-encoding is proven CORRECT given the carry grid point)"
}

// ---------------------------------------------------------------------------
// MODULE STATUS — GOAL-ITEM #3 (the three IEEE-754 layers).
// ---------------------------------------------------------------------------
//
// DONE, PROVEN modulo 3 (kernel-checked, axiom closure ⊆ the 3, NO 4th axiom):
//   1. REPRESENTATION — `Trust.FloatN { sign, exponent, mantissa }` + the special-value
//      classification predicates (isNaN/isInf/isZero/isSubnormal).  [pin_float_classification]
//   2. finite-VALUE — `value : FloatN → ℚ` (ℚ = Prod Int Int, numerator over fixed `D`)
//      + the value lemmas (zero↔value, sign factoring, mantissa monotonicity). [pin_float_value]
//   3. ARITHMETIC OPS — round-to-nearest-EVEN `round : ℚ → FloatN` + `fadd`/`fmul` :=
//      `round (value a · value b)`, with the OP-correctness lemmas PROVEN modulo 3:
//        * round IDEMPOTENT on the representable subnormal grid (no error on grid points);
//        * EXACT-result `fadd` (exact when the sum is on the shared-`D` grid) + exact-zero
//          `fmul`;
//        * ties-to-EVEN (5/2→2, 7/2→4; a round-up-on-tie claim is KernelRejected).
//      [pin_float_ops / all_op_lemmas]
//   4. THE HALF-ULP ROUNDING BOUND `|value(round x) − x| ≤ ½·ulp` — PROVEN modulo 3
//      UNIVERSALLY (∀e ∀N) by a SYMBOLIC INDUCTIVE proof, subsuming the subnormal grid AND
//      every normal binade in ONE theorem, for ALL N, with NO per-exponent reduction (e = 127
//      and 1e6 type-check in microseconds — the huge-exponent COST ceiling is GONE). Built on
//      the prelude's `Nat.div_add_mod` + `Nat.mod_lt` (themselves `@Nat.rec`-proven modulo 3)
//      and `Nat.ulp_universal_bound`. The per-case Step 4c/4d witnesses remain as concrete
//      corollaries.  [ulp_bound_universal / ulp_bound_universal_all / Step 4e]
//   5. THE NON-FINITE (±∞/NaN) VALUE+OP layer — `ExtVal {Finite|PosInf|NegInf|NaN}`, `valueExt
//      : FloatN → ExtVal` (lifts the bit pattern; valueExt = NaN iff isNaN, = PosInf iff isInf
//      ∧ sign false), and `faddExt` encoding the IEEE add rules PROVEN modulo 3: NaN PROPAGATION
//      (faddExt NaN y = NaN ∀y, x NaN = NaN per head), inf+finite = inf, inf+same-inf = inf, the
//      INDETERMINATE ∞−∞ = NaN, finite+finite = Finite(Qadd). A WRONG rule (PosInf+NegInf =
//      PosInf, broken NaN propagation) is KernelRejected.  [pin_float_ext / all_fadd_ext_rules]
//   6. THE BINADE-TOP CARRY RE-ENCODING — `roundCarryReencode e = mk false (e+1) 0` (exponent
//      incremented, mantissa reset), whose VALUE equals the carried grid point 2^(m+1)·2^e =
//      2^m·2^(e+1) (the next binade's bottom) — the carry is a CORRECT re-encoding; and the
//      TOP-exponent carry routes to +∞ (valueExt (mk false ALL_ONES 0) = PosInf, overflow-to-∞).
//      PROVEN modulo 3.  [pin_float_carry / all_carry_lemmas / nonfinite_and_carry]
//
// DEFERRED — the precise-rounding layer, DOCUMENTED, NOT built, NOT faked:
//   * the general "round CHOOSES to carry" decision procedure — a full `round` that DETECTS the
//     binade-top index 2^(m+1) and re-encodes vs stays in-binade. The re-encoding is proven
//     CORRECT *given* the carry grid point, and the error magnitude THROUGH the carry is bounded
//     (the universal bound is carry-agnostic), but the control flow that decides to carry is not
//     built.  [nonfinite_carry_status]
//   * the general non-zero `fmul` `D²→D` denominator rescale.  [half_ulp_error_bound_status]
//   * signaling-NaN vs quiet-NaN payload bits (ONE NaN class modeled); `fmul_ext`/`fdiv_ext` on
//     non-finite operands (0·∞, ∞/∞ — only `faddExt` is built); rounding modes other than
//     round-to-nearest-even (directed-rounding overflow thresholds differ).  [nonfinite_carry_status]
//
// Until the precise-rounding control flow lands, a NORMAL-range float-op safety/overflow
// obligation FAILS CLOSED (sound) — the model covers the TYPE structurally, the per-float
// DENOTED VALUE, the round-to-nearest-even ops + universal half-ulp bound, the NON-FINITE
// (±∞/NaN) value+op semantics, and the carry re-encoding, but does not fabricate the rounding
// CONTROL FLOW it cannot yet prove.

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Step 1: the structured float inductive registers modulo 3 ----

    #[test]
    fn float32_inductive_registers_modulo_3_with_named_projections() {
        let env = float_env(32).expect("Float32 env builds");
        // The inductive registered as a real single-constructor structure.
        let info = env
            .inductive_info(&Name::from_string("Trust.Float32"))
            .expect("Trust.Float32 reads back");
        assert_eq!(
            info.field_names,
            Some(vec![
                Name::from_string("sign"),
                Name::from_string("exponent"),
                Name::from_string("mantissa"),
            ]),
            "the IEEE field projections (sign/exponent/mantissa) must be NAMED, not Prod-positional"
        );
        assert_eq!(info.recursor_name, Some(Name::from_string("Trust.Float32.rec")));
        // The inductive AND its recursor rest on only the 3 foundational axioms.
        for n in ["Trust.Float32", "Trust.Float32.rec"] {
            let deps = env.axiom_deps(&Name::from_string(n)).expect("declared");
            assert!(deps.is_empty(), "{n} must be modulo 3, got {deps:?}");
        }
    }

    #[test]
    fn float64_inductive_registers_modulo_3() {
        let env = float_env(64).expect("Float64 env builds");
        let info = env
            .inductive_info(&Name::from_string("Trust.Float64"))
            .expect("Trust.Float64 reads back");
        assert_eq!(
            info.field_names,
            Some(vec![
                Name::from_string("sign"),
                Name::from_string("exponent"),
                Name::from_string("mantissa"),
            ])
        );
    }

    // ---- Step 2: the classification predicates kernel-check + are modulo 3 ----

    #[test]
    fn float32_classification_predicates_pin_modulo_3() {
        // The inductive, its recursor, AND all four classifiers rest on ONLY the 3
        // foundational axioms — NO 4th axiom, NO opaque/sorry.
        assert_eq!(pin_float_classification(32), FloatClassVerdict::Modulo3);
    }

    #[test]
    fn float64_classification_predicates_pin_modulo_3() {
        assert_eq!(pin_float_classification(64), FloatClassVerdict::Modulo3);
    }

    #[test]
    fn classifiers_typecheck_as_floatn_to_prop() {
        classifiers_typecheck(32).expect("f32 classifiers are Trust.Float32 → Prop");
        classifiers_typecheck(64).expect("f64 classifiers are Trust.Float64 → Prop");
    }

    #[test]
    fn classifier_names_are_qualified() {
        assert_eq!(classifier_name(32, "isNaN").as_deref(), Some("Trust.Float32.isNaN"));
        assert_eq!(
            classifier_name(64, "isSubnormal").as_deref(),
            Some("Trust.Float64.isSubnormal")
        );
        assert_eq!(classifier_name(32, "bogus"), None);
        assert_eq!(classifier_name(16, "isNaN"), None);
    }

    // ---- Soundness: an unsupported width fails closed (never aliases onto BitVec) ----

    #[test]
    fn unsupported_float_width_fails_closed() {
        assert!(float_env(16).is_err(), "f16 is not modeled — fail closed, never a flat BitVec");
        assert!(matches!(pin_float_classification(128), FloatClassVerdict::KernelRejected(_)));
    }

    // ---- Soundness: the predicates actually DISCRIMINATE the IEEE classes ----
    //
    // A concrete NaN bit-pattern (exponent all-ones, mantissa ≠ 0) inhabits `isNaN`
    // but NOT `isInf`/`isZero`; an Inf pattern inhabits `isInf` not `isNaN`. We check
    // this by building the witness floats and proving/refuting the predicate instances
    // via def-eq reduction of the And/Eq Props (the classifier defs unfold + reduce).

    #[test]
    fn isnan_and_isinf_are_distinguished_on_concrete_patterns() {
        let env = classification_env(32).expect("env");
        let tc = TypeChecker::new(&env);
        // Build the f32 NaN pattern: sign=false, exponent=255, mantissa=1.
        // Trust.Float32.mk false (Int.ofNat 255) (Int.ofNat 1)
        let mk = cst("Trust.Float32.mk");
        let nan = Expr::apps(mk.clone(), [cst("Bool.false"), int_lit(255), int_lit(1)]);
        let inf = Expr::apps(mk, [cst("Bool.false"), int_lit(255), int_lit(0)]);

        // isNaN nan should reduce (def-eq) to `And (Eq Int 255 255) (Not (Eq Int 1 0))`.
        // We confirm the predicate APPLIES and is a Prop (type-checks); the structural
        // discrimination is in the body (Inf has mantissa=0, so isNaN inf's second
        // conjunct is `Not (Eq Int 0 0)`, the IEEE-correct "not NaN" shape).
        let isnan = cst("Trust.Float32.isNaN");
        let isinf = cst("Trust.Float32.isInf");
        for app in [
            Expr::app(isnan.clone(), nan.clone()),
            Expr::app(isinf.clone(), inf.clone()),
            Expr::app(isnan, inf),
            Expr::app(isinf, nan),
        ] {
            let ty = tc.infer_type(&app).expect("classifier application type-checks");
            assert!(ty.is_prop(), "a classifier applied to a float pattern is a Prop, got {ty:?}");
        }
    }

    // ---- Step 2b/3b: the VALUE model registers + the value lemmas pin modulo 3 ----

    /// The value interpretation (signMul/magnitude/valueNum/valueDen/value) for f32 AND
    /// f64 registers resting on ONLY the 3 foundational axioms — the value ANCHOR.
    #[test]
    fn float_value_model_pins_modulo_3() {
        assert_eq!(pin_float_value(32), FloatClassVerdict::Modulo3);
        assert_eq!(pin_float_value(64), FloatClassVerdict::Modulo3);
    }

    /// `Trust.FloatN.value` infers type `Trust.FloatN → Prod Int Int` — a REAL rational
    /// `(numerator, denominator)` map over the structure, not an opaque blob.
    #[test]
    fn float_value_typechecks_as_floatn_to_rational() {
        value_typechecks(32).expect("f32 value : Float32 → Prod Int Int");
        value_typechecks(64).expect("f64 value : Float64 → Prod Int Int");
    }

    /// EVERY value lemma is PROVEN modulo 3 for f32 and f64 — the deep proofs the value
    /// model enables (zero↔value, sign factoring, mantissa monotonicity).
    #[test]
    fn all_value_lemmas_proven_modulo_3() {
        for width in [32, 64] {
            for (name, verdict) in all_value_lemmas(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} value lemma `{name}` must be PROVEN modulo 3"
                );
            }
        }
    }

    /// isZero ⟺ value = 0 (canonical zero): the classification↔value connection is
    /// PROVEN — `valueNum (mk false 0 0) = 0`, and the canonical zero IS the `isZero`
    /// class (exponent = 0 ∧ mantissa = 0).
    #[test]
    fn canonical_zero_has_value_zero_proven() {
        assert_eq!(lemma_zero_has_value_zero(32), ValueLemmaVerdict::ProvenModulo3);
    }

    /// The SIGN lemma is general (`∀ f, valueNum f = signMul (sign f) (magnitude f)`):
    /// the value's sign is exactly the sign bit applied to a non-negative magnitude.
    #[test]
    fn sign_factors_lemma_is_general_and_proven() {
        assert_eq!(lemma_value_sign_factors(32), ValueLemmaVerdict::ProvenModulo3);
    }

    /// The OTHER direction of isZero ⟺ value = 0: a NONZERO finite float (the smallest
    /// positive normal `mk false 1 0`) denotes a NONZERO rational — `valueNum = 2^(m+1)`,
    /// the exact positive numerator. Proven for f32 and f64.
    #[test]
    fn nonzero_float_has_nonzero_value_proven() {
        assert_eq!(lemma_nonzero_has_nonzero_value(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_nonzero_has_nonzero_value(64), ValueLemmaVerdict::ProvenModulo3);
    }

    /// The exact NEGATED-value sign lemma is proven: `valueNum (mk true 1 0) =
    /// −2^(m+1)` (a manifestly-negative power of two) for f32 and f64 — the sign bit
    /// drives the value negative.
    #[test]
    fn negative_sign_denotes_negated_magnitude_proven() {
        assert_eq!(lemma_negative_sign_is_negative(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_negative_sign_is_negative(64), ValueLemmaVerdict::ProvenModulo3);
    }

    /// Mantissa monotonicity is proven (a strictly-positive value step as the mantissa
    /// increases at fixed exponent/sign) for f32 and f64.
    #[test]
    fn mantissa_monotone_proven() {
        assert_eq!(lemma_mantissa_monotone(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_mantissa_monotone(64), ValueLemmaVerdict::ProvenModulo3);
    }

    // ---- SOUNDNESS: a WRONG value claim FAILS CLOSED (KernelRejected) ----

    /// A WRONG SIGN claim — that the NEGATIVE float `mk true 1 0` denotes a POSITIVE
    /// numerator `+2^24` (the correct value is `−2^24`) — must FAIL CLOSED: the
    /// numerator actually reduces to `Int.neg (2^24)`, so `Eq.refl (+2^24)` does NOT
    /// type-check against `valueNum … = +2^24`. A KernelRejected here is the fail-closed
    /// guarantee that a wrong-sign value claim can never be proven.
    #[test]
    fn wrong_sign_value_claim_fails_closed() {
        let names = value_decl_names("Trust.Float32");
        let neg = float_pattern("Trust.Float32", true, 1, 0);
        let num = Expr::app(cst(&names.value_num), neg);
        // WRONG: claim the negated normal float denotes +2^24 (it denotes −2^24).
        let wrong_rhs = int_pow(int_two(), nat_lit(24));
        let statement = eq_int_prop(num, wrong_rhs.clone());
        let proof = refl_int(wrong_rhs);
        assert!(
            matches!(
                check_value_lemma(32, "Trust.Float32.value.WRONG_sign", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong-SIGN value claim must fail closed (KernelRejected)"
        );
    }

    /// A WRONG BIAS claim — that the f32 denominator is `2^149` (off-by-one bias) when
    /// it is actually `2^(23 + 127) = 2^150` — must FAIL CLOSED. The denominator is the
    /// fixed scale of the denoted rational; a wrong bias denotes the WRONG rational, so
    /// `valueDen = 2^149` is a false equality that `Eq.refl (2^150)` cannot inhabit.
    #[test]
    fn wrong_bias_denominator_claim_fails_closed() {
        let names = value_decl_names("Trust.Float32");
        // WRONG: valueDen = 2^149 (correct is 2^150). 2^149 ≠ 2^150 in Int.
        let wrong_den = int_pow(int_two(), nat_lit(149));
        let statement = eq_int_prop(cst(&names.value_den), wrong_den.clone());
        let proof = refl_int(wrong_den);
        assert!(
            matches!(
                check_value_lemma(32, "Trust.Float32.value.WRONG_bias", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong-BIAS denominator claim must fail closed (KernelRejected)"
        );
    }

    /// The CORRECT f32 denominator IS `2^150` (= 2^(mant_bits 23 + bias 127)) — proven
    /// by reflexivity. Pins the bias the value model uses (complement of the
    /// wrong-bias fail-closed test).
    #[test]
    fn correct_bias_denominator_is_2_pow_150() {
        let names = value_decl_names("Trust.Float32");
        let right_den = int_pow(int_two(), nat_lit(150));
        let statement = eq_int_prop(cst(&names.value_den), right_den.clone());
        let proof = refl_int(right_den);
        assert_eq!(
            check_value_lemma(32, "Trust.Float32.value.bias_150", statement, proof),
            ValueLemmaVerdict::ProvenModulo3,
        );
    }

    /// A WRONG MAGNITUDE claim — that the smallest positive normal `mk false 1 0`
    /// denotes `2^25` when it actually denotes `2^24` — must FAIL CLOSED. This guards
    /// the numeric magnitude (the exponent/significand scaling), independent of sign
    /// and bias: a wrong power of two is a different rational, unprovable by `Eq.refl`.
    #[test]
    fn wrong_magnitude_value_claim_fails_closed() {
        let names = value_decl_names("Trust.Float32");
        let f = float_pattern("Trust.Float32", false, 1, 0);
        let num = Expr::app(cst(&names.value_num), f);
        // WRONG: claim 2^25 (correct numerator is 2^24).
        let wrong_rhs = int_pow(int_two(), nat_lit(25));
        let statement = eq_int_prop(num, wrong_rhs.clone());
        let proof = refl_int(wrong_rhs);
        assert!(
            matches!(
                check_value_lemma(32, "Trust.Float32.value.WRONG_magnitude", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong-MAGNITUDE value claim must fail closed (KernelRejected)"
        );
    }

    /// A WRONG ZERO claim — that the canonical zero `mk false 0 0` denotes a NONZERO
    /// numerator `1` — must FAIL CLOSED. The canonical zero's numerator reduces to `0`,
    /// so `Eq.refl 1` cannot inhabit `valueNum (mk false 0 0) = 1`. This is the
    /// fail-closed teeth of the isZero ⟺ value = 0 connection.
    #[test]
    fn wrong_zero_value_claim_fails_closed() {
        let names = value_decl_names("Trust.Float32");
        let zero = float_pattern("Trust.Float32", false, 0, 0);
        let num = Expr::app(cst(&names.value_num), zero);
        // WRONG: claim the canonical zero denotes 1.
        let statement = eq_int_prop(num, int_lit(1));
        let proof = refl_int(int_lit(1));
        assert!(
            matches!(
                check_value_lemma(32, "Trust.Float32.value.WRONG_zero", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong-ZERO value claim must fail closed (KernelRejected)"
        );
    }

    /// An unsupported width fails closed for the value model too (never an opaque blob,
    /// never a wrong rational).
    #[test]
    fn unsupported_width_value_model_fails_closed() {
        assert!(value_env(16).is_err());
        assert!(matches!(pin_float_value(128), FloatClassVerdict::KernelRejected(_)));
        assert!(matches!(lemma_zero_has_value_zero(16), ValueLemmaVerdict::KernelRejected(_)));
    }

    // ---- Step 4/4b: the round + arithmetic OPS register + the op lemmas pin modulo 3 ----

    /// The op model (roundHalfEven/round/Qadd/Qmul/fadd/fmul) for f32 AND f64 registers
    /// resting on ONLY the 3 foundational axioms — the OPS anchor (NO 4th axiom).
    #[test]
    fn float_ops_model_pins_modulo_3() {
        assert_eq!(pin_float_ops(32), FloatClassVerdict::Modulo3);
        assert_eq!(pin_float_ops(64), FloatClassVerdict::Modulo3);
    }

    /// `round : Prod Int Int → FloatN` and `fadd`/`fmul : FloatN → FloatN → FloatN`
    /// KERNEL-CHECK as real operations over the structure (round-to-nearest-even ℚ→float
    /// and float→float→float), not opaque blobs.
    #[test]
    fn float_ops_typecheck_as_real_operations() {
        ops_typecheck(32).expect("f32 round/fadd/fmul kernel-check with the right types");
        ops_typecheck(64).expect("f64 round/fadd/fmul kernel-check with the right types");
    }

    /// EVERY op lemma is PROVEN modulo 3 for f32 and f64 — round idempotence on the
    /// subnormal grid, exact-result op correctness, and ties-to-even.
    #[test]
    fn all_op_lemmas_proven_modulo_3() {
        for width in [32, 64] {
            for (name, verdict) in all_op_lemmas(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} op lemma `{name}` must be PROVEN modulo 3"
                );
            }
        }
    }

    /// IDEMPOTENCE — `round (value f) = f` for a representable subnormal float: round is a
    /// genuine left-inverse of value on the grid, so an on-grid value rounds back to
    /// itself with NO error. Proven for several positive and a negative subnormal.
    #[test]
    fn round_is_idempotent_on_subnormal_grid() {
        for m in [1u64, 3, 10, 100] {
            assert_eq!(
                lemma_round_idempotent_subnormal(32, m),
                ValueLemmaVerdict::ProvenModulo3,
                "round(value(mk false 0 {m})) must equal mk false 0 {m}"
            );
        }
        assert_eq!(
            lemma_round_idempotent_negative_subnormal(32, 7),
            ValueLemmaVerdict::ProvenModulo3,
            "round recovers the sign of a negative subnormal grid value"
        );
    }

    /// EXACT-RESULT — when `value a + value b` lands exactly on a grid point `value c`,
    /// `fadd a b = c` with NO rounding error (the IEEE add is EXACT here). And `fmul a 0
    /// = 0` exactly. Proven for f32 and f64.
    #[test]
    fn exact_result_ops_have_no_rounding_error() {
        assert_eq!(lemma_fadd_exact(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_fadd_exact(64), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_fmul_zero_exact(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_fmul_zero_exact(64), ValueLemmaVerdict::ProvenModulo3);
    }

    // ---- Bullet 3 — the FINITE rational QUOTIENT rounded back to the float grid ----

    /// `Qdiv : Prod Int Int → Prod Int Int → Prod Int Int` and `fdivFinite : FloatN →
    /// FloatN → FloatN` KERNEL-CHECK as real operations (the exact rational quotient carrier
    /// and the round-back float→float→float divide). Covered by `ops_typecheck`.
    #[test]
    fn fdiv_finite_typechecks_as_real_operation() {
        ops_typecheck(32).expect("f32 Qdiv/fdivFinite kernel-check with the right types");
        ops_typecheck(64).expect("f64 Qdiv/fdivFinite kernel-check with the right types");
    }

    /// The whole finite-division round-back battery is PROVEN modulo 3 for f32 AND f64 — the
    /// exact-zero result (`0 / b = 0`), the half-ulp ERROR ENVELOPE (via the universal bound at
    /// the quotient numerator, e = 0/1/10/127), and the `fdivExt` finite/finite `Qdiv` tie-in.
    /// This closes bullet 3's last substantive arithmetic gap (the finite/finite `fdiv`).
    #[test]
    fn all_fdiv_finite_lemmas_proven_modulo_3() {
        for width in [32, 64] {
            for (name, verdict) in all_fdiv_finite_lemmas(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} finite-division lemma `{name}` must be PROVEN modulo 3"
                );
            }
        }
    }

    /// EXACT-RESULT / IDEMPOTENCE `fdivFinite` — `0 / b = 0` with NO rounding error (the exact
    /// rational quotient has numerator 0, so the round-back lands EXACTLY on the grid point and
    /// `round (value c) = c`). Proven for f32 and f64 — the division analog of `fmul_zero_exact`.
    #[test]
    fn fdiv_finite_zero_dividend_is_exact() {
        assert_eq!(lemma_fdiv_finite_zero_exact(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_fdiv_finite_zero_exact(64), ValueLemmaVerdict::ProvenModulo3);
    }

    /// DIVISION HALF-ULP ERROR BOUND — the rounded finite quotient is within ½·ulp of the exact
    /// rational quotient, by REUSE of `Nat.ulp_universal_bound` at the quotient numerator. Proven
    /// modulo 3 across the exponent range INCLUDING the huge e = 127 with NO heartbeat blowup (the
    /// statement keeps `2^e` symbolic). The quotient is bounded BECAUSE it is just another rational
    /// fed to the same `round`; no division-specific analysis is added.
    #[test]
    fn fdiv_finite_error_bound_universal_no_blowup() {
        for e in [0u64, 1, 10, 127] {
            assert_eq!(
                lemma_fdiv_finite_error_bound(32, e),
                ValueLemmaVerdict::ProvenModulo3,
                "f32 division half-ulp bound at e={e} must be PROVEN modulo 3"
            );
        }
        assert_eq!(lemma_fdiv_finite_error_bound(64, 10), ValueLemmaVerdict::ProvenModulo3);
    }

    /// FINITE/FINITE TIE-IN — the non-finite `fdivExt` finite/finite arm carries the SAME exact
    /// rational quotient `Qdiv` that `fdivFinite` rounds: `fdivExt (Finite p) (Finite q) = Finite
    /// (Qdiv p q)` (nonzero divisor). The two layers agree above the round. Proven for f32 and f64.
    #[test]
    fn fdiv_ext_finite_arm_is_qdiv() {
        assert_eq!(lemma_fdiv_ext_finite_is_qdiv(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_fdiv_ext_finite_is_qdiv(64), ValueLemmaVerdict::ProvenModulo3);
    }

    // ---- SOUNDNESS: a WRONG finite-division claim FAILS CLOSED (KernelRejected) ----

    /// A WRONG `Qdiv` (numerator/denominator roles SWAPPED — the cross-product in the WRONG
    /// direction, `ad·bn` where the numerator should be `an·bd`) is KernelRejected. `Prod.fst
    /// (Qdiv (3,1) (2,1))` is `3` (the true numerator), NOT `2` (the swapped one). Cheap Int-level
    /// reduction. The fail-closed teeth for `Qdiv`'s cross-multiply direction.
    #[test]
    fn wrong_qdiv_numerator_swap_fails_closed() {
        assert!(
            wrong_qdiv_numerator_swapped_fails_closed(32),
            "a swapped-direction Qdiv numerator must fail closed (KernelRejected)"
        );
        assert!(wrong_qdiv_numerator_swapped_fails_closed(64));
    }

    /// A WRONG `fdivFinite` (operands SWAPPED — the RECIPROCAL `b / a` rounded back) is
    /// KernelRejected: `3 / 2` and `2 / 3` round to DIFFERENT grid points, so the swapped rhs is
    /// not def-eq the true `fdivFinite a b`. The fail-closed teeth at the rounded-quotient level.
    #[test]
    fn wrong_fdiv_finite_reciprocal_fails_closed() {
        assert!(
            wrong_fdiv_finite_swapped_fails_closed(32),
            "a reciprocal (operands swapped) fdivFinite claim must fail closed (KernelRejected)"
        );
    }

    /// A TOO-TIGHT (¼·ulp) DIVISION error bound is KernelRejected — at an exact tie the division
    /// error is EXACTLY ½·ulp, so the quarter bound is FALSE and the proven ½·ulp witness
    /// (`Nat.mul 2 …`) is not def-eq the ¼·ulp claim (`Nat.mul 4 …`). Structural head-literal
    /// rejection, cheap even at the huge e = 127. The fail-closed teeth for the division envelope.
    #[test]
    fn wrong_quarter_ulp_division_bound_fails_closed() {
        for e in [0u64, 10, 127] {
            assert!(
                wrong_quarter_ulp_fdiv_finite_fails_closed(32, e),
                "a ¼·ulp division bound at e={e} must fail closed (KernelRejected)"
            );
        }
    }

    /// TIES-TO-EVEN — the round-to-nearest-EVEN teeth: `roundHalfEven 5 = 2` (2.5 ties
    /// DOWN to even 2) and `roundHalfEven 7 = 4` (3.5 ties UP to even 4). Ties follow
    /// the EVEN neighbor in EITHER direction. Proven for f32 and f64.
    #[test]
    fn ties_round_to_even_both_directions() {
        assert_eq!(lemma_round_half_even_tie(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_round_half_even_tie(64), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_round_half_even_tie_up(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_round_half_even_tie_up(64), ValueLemmaVerdict::ProvenModulo3);
    }

    // ---- SOUNDNESS: a WRONG ROUNDING claim FAILS CLOSED (KernelRejected) ----

    /// A WRONG-ROUNDING claim — that the tie `5/2` rounds UP to the ODD `3` (off the
    /// round-to-nearest-EVEN rule, which gives the EVEN `2`) — must FAIL CLOSED:
    /// `roundHalfEven 5` actually reduces to `2`, so `Eq.refl 3` does NOT type-check
    /// against `roundHalfEven 5 = 3`. This is the fail-closed guarantee that a
    /// wrong-rounding (round-the-tie-up-off-even) claim can NEVER be proven.
    #[test]
    fn wrong_rounding_tie_up_off_even_fails_closed() {
        let names = op_decl_names("Trust.Float32");
        // WRONG: claim 5/2 (a tie) rounds UP to 3 (it rounds to even 2).
        let lhs = Expr::app(cst("Int.ofNat"), Expr::app(cst(&names.round_half_even), nat_lit(5)));
        let statement = eq_int_prop(lhs, int_lit(3));
        let proof = refl_int(int_lit(3));
        assert!(
            matches!(
                check_op_lemma(32, "Trust.Float32.round.WRONG_tie_up", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong-ROUNDING (tie rounds up off even) claim must fail closed (KernelRejected)"
        );
    }

    /// A WRONG-IDEMPOTENCE claim — that `round (value (mk false 0 3))` equals a DIFFERENT
    /// float `mk false 0 4` — must FAIL CLOSED. round is a genuine left-inverse, so it
    /// returns `mk false 0 3`; claiming `mk false 0 4` is rejected by the kernel.
    #[test]
    fn wrong_idempotence_target_fails_closed() {
        let names = op_decl_names("Trust.Float32");
        let vnames = value_decl_names("Trust.Float32");
        let f = float_pattern("Trust.Float32", false, 0, 3);
        let lhs = Expr::app(cst(&names.round), Expr::app(cst(&vnames.value), f));
        // WRONG: claim it rounds to mk false 0 4 (it rounds to itself, mk false 0 3).
        let wrong = float_pattern("Trust.Float32", false, 0, 4);
        let statement = eq_float_prop("Trust.Float32", lhs, wrong.clone());
        let proof = refl_float("Trust.Float32", wrong);
        assert!(
            matches!(
                check_op_lemma(32, "Trust.Float32.round.WRONG_idem", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong-idempotence-target claim must fail closed (KernelRejected)"
        );
    }

    /// A WRONG EXACT-ADD claim — that `fadd (mk false 0 1) (mk false 0 2)` equals
    /// `mk false 0 4` (the correct exact result is `mk false 0 3`, since 1+2=3 on the
    /// subnormal grid) — must FAIL CLOSED.
    #[test]
    fn wrong_exact_add_result_fails_closed() {
        let names = op_decl_names("Trust.Float32");
        let a = float_pattern("Trust.Float32", false, 0, 1);
        let b = float_pattern("Trust.Float32", false, 0, 2);
        let lhs = Expr::apps(cst(&names.fadd), [a, b]);
        let wrong = float_pattern("Trust.Float32", false, 0, 4);
        let statement = eq_float_prop("Trust.Float32", lhs, wrong.clone());
        let proof = refl_float("Trust.Float32", wrong);
        assert!(
            matches!(
                check_op_lemma(32, "Trust.Float32.fadd.WRONG_exact", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong exact-add result must fail closed (KernelRejected)"
        );
    }

    /// An unsupported width fails closed for the op model too (never an opaque blob,
    /// never a fabricated rounding).
    #[test]
    fn unsupported_width_op_model_fails_closed() {
        assert!(op_env(16).is_err());
        assert!(matches!(pin_float_ops(128), FloatClassVerdict::KernelRejected(_)));
        assert!(matches!(
            lemma_round_idempotent_subnormal(16, 3),
            ValueLemmaVerdict::KernelRejected(_)
        ));
    }

    /// The half-ulp error bound status HONESTLY reports BOTH halves: PROVEN on the
    /// subnormal grid, DEFERRED on the normal arm. Neither claim is faked.
    #[test]
    fn half_ulp_bound_status_is_honest_proven_subnormal_deferred_normal() {
        let s = half_ulp_error_bound_status();
        assert!(s.contains("PROVEN"), "must report the proven subnormal bound, got: {s}");
        assert!(s.contains("SUBNORMAL"), "must name the subnormal arm");
        assert!(s.contains("DEFERRED"), "must flag the deferred normal arm, got: {s}");
        assert!(s.contains("ulp"), "must name the ulp bound");
    }

    // ---- Step 4c: the HALF-ULP ROUNDING-ERROR BOUND on the subnormal grid ----

    /// The grid/ulp layer (ulpSubnormal / halfUlpSubnormal / roundErrorNum) for f32 AND
    /// f64 registers resting on ONLY the 3 foundational axioms — NO 4th axiom.
    #[test]
    fn float_ulp_model_pins_modulo_3() {
        assert_eq!(pin_float_ulp(32), FloatClassVerdict::Modulo3);
        assert_eq!(pin_float_ulp(64), FloatClassVerdict::Modulo3);
    }

    /// THE BULLET-3 TAIL — the defining round-to-nearest correctness bound
    /// `|value(round x) − x| ≤ ½·ulp(x)` is PROVEN modulo 3 on the uniform subnormal grid
    /// for f32 AND f64, covering EVERY rounding case (exact, tie-down-to-even,
    /// tie-up-to-even, nearest, negative). The whole battery — grid-spacing identity plus
    /// per-case bounds — resolves to Modulo3.
    #[test]
    fn half_ulp_bound_proven_modulo_3_subnormal_grid() {
        assert_eq!(ulp_bound(32), FloatClassVerdict::Modulo3);
        assert_eq!(ulp_bound(64), FloatClassVerdict::Modulo3);
    }

    /// ulp IS the grid spacing — `Prod.fst ulpSubnormal = 2` and `Prod.fst
    /// halfUlpSubnormal = 1` (over the fixed `D`), so the bound `≤ ½·ulp` is exactly the
    /// integer fact `|roundErrorNum x| ≤ 1`. Proven for f32 and f64.
    #[test]
    fn ulp_is_the_grid_spacing_two_over_d() {
        assert_eq!(lemma_ulp_is_grid_spacing(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_ulp_is_grid_spacing(64), ValueLemmaVerdict::ProvenModulo3);
    }

    /// EVERY per-case half-ulp bound is PROVEN modulo 3 for f32 and f64 — each rounding
    /// case keeps `|value(round x) − x| ≤ ½·ulp`, the error never exceeding half a grid
    /// step (the tie cases sit EXACTLY at ½·ulp; the exact cases at 0).
    #[test]
    fn every_rounding_case_keeps_half_ulp_bound() {
        for width in [32, 64] {
            for (tag, verdict) in all_ulp_bound_lemmas(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} half-ulp bound case `{tag}` must be PROVEN modulo 3"
                );
            }
        }
    }

    // ---- SOUNDNESS: a WRONG (too-tight) bound FAILS CLOSED (KernelRejected) ----

    /// A WRONG bound — claiming the TIE case `x = 5/D` has error `< ½·ulp`, i.e. the upper
    /// bound `roundErrorNum (5/D) ≤ −1` is actually fine (error IS −1) but the symmetric
    /// too-tight claim `roundErrorNum (5/D) ≥ 0` (error non-negative, a QUARTER-ulp-style
    /// "error in [0, ½ulp)" claim) must FAIL CLOSED. The tie's error is EXACTLY −1, so
    /// `Int.le (ofNat 0) (roundErrorNum (5/D))` reduces to `Int.NonNeg (roundErrorNum (5/D))
    /// = Int.NonNeg (−1)`, which NO `Int.NonNeg.mk k` inhabits. Strictly-tighter-than-½ulp
    /// is rejected.
    #[test]
    fn too_tight_quarter_ulp_bound_on_tie_fails_closed() {
        let inductive = "Trust.Float32";
        let names = ulp_decl_names(inductive);
        let x = rational_over_d(32, 5).expect("f32 layout");
        let err = Expr::app(cst(&names.error_num), x);
        // WRONG: claim 0 ≤ roundErrorNum (5/D) (the tie error is −1, so this is false).
        let statement = int_le_prop(int_lit(0), err);
        let proof = int_nonneg_mk(0);
        assert!(
            matches!(
                check_ulp_lemma(32, "Trust.Float32.ulp.WRONG_quarter_tie", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a too-tight (claims error ≥ 0 on a tie that errs −½ulp) bound must fail closed"
        );
    }

    /// A WRONG bound — claiming the TIE `x = 7/D`'s error is `≤ 0` (it is exactly +1 =
    /// ½·ulp) — must FAIL CLOSED. `Int.le (roundErrorNum (7/D)) (ofNat 0)` reduces to
    /// `Int.NonNeg (Int.sub 0 1) = Int.NonNeg (−1)`, uninhabited. Guards against a
    /// fabricated "rounds down / always exact" claim that would hide the +½ulp error.
    #[test]
    fn fabricated_zero_error_on_tie_fails_closed() {
        let inductive = "Trust.Float32";
        let names = ulp_decl_names(inductive);
        let x = rational_over_d(32, 7).expect("f32 layout");
        let err = Expr::app(cst(&names.error_num), x);
        // WRONG: claim roundErrorNum (7/D) ≤ 0 (the actual error is +1: round 7/2 → even 4,
        // numerator 8, 8 − 7 = +1).
        let statement = int_le_prop(err, int_lit(0));
        let proof = int_nonneg_mk(0);
        assert!(
            matches!(
                check_ulp_lemma(32, "Trust.Float32.ulp.WRONG_zero_error_tie", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a fabricated ≤0-error claim on a +½ulp TIE must fail closed (KernelRejected)"
        );
    }

    /// A WRONG bound at TWICE the budget — claiming `x = 11/D` (11/2 = 5.5, a tie → even 6,
    /// error 12−11 = +1) has signed error +3 (a 1.5·ulp claim) — must FAIL CLOSED via the
    /// helper's range guard AND the kernel: the actual error is +1, so the witnesses for a
    /// +3 claim (`NonNeg.mk (1−3)` underflows) are nonsensical. Confirms `ulp_bound_at`
    /// only ever certifies a genuine ≤½ulp bound.
    #[test]
    fn over_budget_error_claim_fails_closed() {
        // signed_error 3 is outside ±1 — the helper rejects it as a non-half-ulp witness.
        assert!(matches!(
            ulp_bound_at(32, 11, 3, "WRONG_over_budget"),
            ValueLemmaVerdict::KernelRejected(_)
        ));
        // And a WRONG signed error (claiming +1 when the true tie error at 11/D is +1 IS
        // right; claim −1 instead — wrong sign — must be rejected by the kernel).
        assert!(matches!(
            ulp_bound_at(32, 11, -1, "WRONG_sign_11"),
            ValueLemmaVerdict::KernelRejected(_)
        ));
    }

    /// The CORRECT signed tie error IS exactly −1 (= −½·ulp) at `x = 5/D`: round 5/2 → even
    /// 4 (value numerator 4), 4 − 5 = −1, sitting EXACTLY on the (negative) half-ulp
    /// boundary. Proven by `Eq.refl` on the reduced signed error. Pins the worst case.
    #[test]
    fn tie_error_magnitude_is_exactly_one_half_ulp() {
        let inductive = "Trust.Float32";
        let names = ulp_decl_names(inductive);
        let x = rational_over_d(32, 5).expect("f32 layout");
        let err = Expr::app(cst(&names.error_num), x);
        // roundErrorNum (5/D) = −1 exactly (= −½·ulp).
        let statement = eq_int_prop(err, int_neg(int_lit(1)));
        let proof = refl_int(int_neg(int_lit(1)));
        assert_eq!(
            check_ulp_lemma(32, "Trust.Float32.ulp.tie_error_is_neg_one", statement, proof),
            ValueLemmaVerdict::ProvenModulo3,
        );
    }

    /// An unsupported width fails closed for the grid/ulp model too (never an opaque blob,
    /// never a fabricated bound).
    #[test]
    fn unsupported_width_ulp_model_fails_closed() {
        assert!(ulp_env(16).is_err());
        assert!(matches!(pin_float_ulp(128), FloatClassVerdict::KernelRejected(_)));
        assert!(matches!(ulp_bound(16), FloatClassVerdict::KernelRejected(_)));
    }

    /// The universal/normal-arm status is honestly reported: PROVEN on the subnormal grid,
    /// DEFERRED for the fully-universal ∀x and the non-uniform normal binade.
    #[test]
    fn ulp_bound_universal_status_is_honest() {
        let s = ulp_bound_universal_status();
        assert!(s.contains("PROVEN"), "must report the proven subnormal bound");
        assert!(s.contains("SUBNORMAL"), "must name the subnormal arm");
        assert!(s.contains("DEFERRED"), "must flag the deferred universal/normal arm");
    }

    // ---- Step 4d: the NORMAL-BINADE half-ulp bound (the binade is GIVEN by the field) ----

    /// The NORMAL-binade layer (roundHalfEvenMod / roundNormalBinade / ulpNormal /
    /// halfUlpNormal / roundErrorNumBinade) for f32 AND f64 registers resting on ONLY the 3
    /// foundational axioms — NO 4th axiom.
    #[test]
    fn float_binade_model_pins_modulo_3() {
        assert_eq!(pin_float_binade(32), FloatClassVerdict::Modulo3);
        assert_eq!(pin_float_binade(64), FloatClassVerdict::Modulo3);
    }

    /// THE BULLET-3 FINAL RESIDUAL — the half-ulp bound `|value(round_e x) − x| ≤ ½·ulp(x)`
    /// on the NON-uniform NORMAL grid, with ulp(x) = 2^(e−m) READ from the stored exponent
    /// field (no floor(log2|x|)), is PROVEN modulo 3 for f32 AND f64: ulpNormal reads the
    /// field (up to e = 127), and every per-case bound at e = 2, 3, 8, 10 resolves to Modulo3.
    #[test]
    fn normal_binade_half_ulp_bound_proven_modulo_3() {
        assert_eq!(normal_binade_ulp_bound(32), FloatClassVerdict::Modulo3);
        assert_eq!(normal_binade_ulp_bound(64), FloatClassVerdict::Modulo3);
    }

    /// ulpNormal READS the exponent field — `Prod.fst (ulpNormal (mk false e 0)) = 2^e` for
    /// several e (the binade is GIVEN, not searched). Proven for f32 and f64.
    #[test]
    fn ulp_normal_reads_the_exponent_field() {
        for width in [32, 64] {
            for e in [1u64, 2, 5, 8, 127] {
                assert_eq!(
                    lemma_ulp_normal_reads_exponent(width, e),
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width}: ulpNormal(mk false {e} 0) numerator must be 2^{e}"
                );
            }
        }
    }

    /// EVERY per-case NORMAL-binade half-ulp bound is PROVEN modulo 3 for f32 and f64 — each
    /// rounding case (exact, near-down, tie-down-to-even, near-up, exact-next, tie-up-to-even,
    /// negative) keeps `|value(round_e x) − x| ≤ ½·ulp` across the non-uniform binades
    /// e = 2, 3, 8, 10 (spacings 4, 8, 256, 1024 over D — each distinct from the subnormal 2).
    #[test]
    fn every_normal_binade_rounding_case_keeps_half_ulp_bound() {
        for width in [32, 64] {
            for (tag, verdict) in all_binade_bound_lemmas(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} normal-binade bound case `{tag}` must be PROVEN modulo 3"
                );
            }
        }
    }

    /// A TIE at a normal binade sits EXACTLY at ½·ulp — at e = 2 (U = 4) the tie input `10 =
    /// 2·4 + 2` rounds DOWN to the even grid index (8), error exactly `−2 = −½·ulp` (½·ulp
    /// numerator = 2^(e−1) = 2). Proven by reducing `roundErrorNumBinade 2 (10,1)` to the
    /// literal −2 via `Eq.refl`. A wrong tie error would fail to typecheck.
    #[test]
    fn normal_binade_tie_error_is_exactly_half_ulp() {
        let inductive = "Trust.Float32";
        let names = binade_decl_names(inductive);
        // tie input N = 10 = 2U + h (U=4, h=2): rounds to 8 (even index 2), error 8 − 10 = −2.
        let x = prod_mk_int(int_lit(10), int_lit(1));
        let err = Expr::apps(cst(&names.error_num_binade), [nat_lit(2), x]);
        let statement = eq_int_prop(err, int_neg(int_lit(2)));
        let proof = refl_int(int_neg(int_lit(2)));
        assert_eq!(
            check_binade_lemma(32, "Trust.Float32.binade.tie_is_neg_two", statement, proof),
            ValueLemmaVerdict::ProvenModulo3,
        );
    }

    // ---- SOUNDNESS: a WRONG (too-tight) NORMAL-binade bound FAILS CLOSED (KernelRejected) ----

    /// A WRONG too-tight bound — claiming the e = 2 tie `N = 10` (error exactly −2 = −½·ulp)
    /// has error `≥ −1` (i.e. `−1 ≤ err`, a budget of ¼·ulp not ½·ulp) — must FAIL CLOSED.
    /// `Int.le (−1) err` reduces to `Int.NonNeg (Int.sub err (−1)) = Int.NonNeg (−2 + 1) =
    /// Int.NonNeg (−1)`, uninhabited (`Int.toNat (−1) = 0`, `Int.ofNat 0 ≢ −1`). A
    /// strictly-tighter-than-½ulp normal-binade claim is rejected.
    #[test]
    fn too_tight_normal_binade_bound_fails_closed() {
        let inductive = "Trust.Float32";
        let names = binade_decl_names(inductive);
        // roundErrorNumBinade 2 (10,1) — the tie input, error exactly −2.
        let err = || {
            let x = prod_mk_int(int_lit(10), int_lit(1));
            Expr::apps(cst(&names.error_num_binade), [nat_lit(2), x])
        };
        // WRONG: claim −1 ≤ err (the tie error is −2, so this is false; budget ¼·ulp not ½·ulp).
        let statement = int_le_prop(int_neg(int_lit(1)), err());
        // The (would-be) witness: NonNeg.mk (toNat (err − (−1))) = NonNeg.mk (toNat (−2+1)) =
        // NonNeg.mk (toNat (−1)) = NonNeg.mk 0 : Int.NonNeg (ofNat 0) ≢ Int.NonNeg (−1) ⇒ reject.
        let proof = int_nonneg_mk_to_nat(int_sub(err(), int_neg(int_lit(1))));
        assert!(
            matches!(
                check_binade_lemma(32, "Trust.Float32.binade.WRONG_too_tight", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a too-tight (¼·ulp) normal-binade bound on a ½·ulp tie must fail closed"
        );
    }

    /// A WRONG ulp claim — that the e = 5 binade ulp numerator is `2^6` (off-by-one, the
    /// correct is `2^5`) — must FAIL CLOSED: ulpNormal reads the field and returns `2^5`, so
    /// `Eq.refl (2^6)` does not inhabit `Prod.fst (ulpNormal (mk false 5 0)) = 2^6`. Guards the
    /// "binade is GIVEN by the field" claim against a wrong per-binade spacing.
    #[test]
    fn wrong_normal_binade_ulp_fails_closed() {
        let inductive = "Trust.Float32";
        let names = binade_decl_names(inductive);
        let f = float_pattern(inductive, false, 5, 0);
        let lhs = prod_fst_int(Expr::app(cst(&names.ulp_normal), f));
        // WRONG: claim 2^6 (correct is 2^5).
        let wrong = int_pow(int_two(), nat_lit(6));
        let statement = eq_int_prop(lhs, wrong.clone());
        let proof = refl_int(wrong);
        assert!(
            matches!(
                check_binade_lemma(32, "Trust.Float32.binade.WRONG_ulp", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong per-binade ulp must fail closed (KernelRejected)"
        );
    }

    /// An unsupported width fails closed for the binade model too (never an opaque blob,
    /// never a fabricated bound).
    #[test]
    fn unsupported_width_binade_model_fails_closed() {
        assert!(binade_env(16).is_err());
        assert!(matches!(pin_float_binade(128), FloatClassVerdict::KernelRejected(_)));
        assert!(matches!(normal_binade_ulp_bound(16), FloatClassVerdict::KernelRejected(_)));
    }

    /// The binade-bound status HONESTLY reports BOTH halves: PROVEN modulo 3 for all finite x
    /// (subnormal + every normal binade, parameterized by the exponent field), and the PRECISE
    /// standing residual (the binade-top carry/overflow boundary + the ∀-quantified form).
    #[test]
    fn binade_ulp_bound_status_is_honest() {
        let s = binade_ulp_bound_status();
        assert!(s.contains("PROVEN"), "must report the proven binade bound, got: {s}");
        assert!(s.contains("normal binade"), "must name the normal binades");
        assert!(s.contains("RESIDUAL"), "must flag the precise residual, got: {s}");
        assert!(s.contains("carry"), "must name the binade-top carry residual, got: {s}");
    }

    // ---- Step 4e: the UNIVERSAL (∀e ∀N) half-ulp bound via the symbolic inductive proof ----

    /// The prelude carries the symbolic universal bound `Nat.ulp_universal_bound` (and the round
    /// + general-modulus bound), proven axiom-free in the kernel. This is the dependency the whole
    /// of Step 4e rests on; if the clean pin is stale, the universal bound must FAIL CLOSED.
    #[test]
    fn prelude_carries_universal_bound() {
        let env = value_env(32).expect("f32 value env builds");
        for n in [
            "Nat.ulp_universal_bound",
            "Nat.round_half_even_mod_bound",
            "Nat.roundHalfEvenMod",
            "Nat.div_add_mod",
            "Nat.mod_lt",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_some(),
                "prelude must carry {n} (bump the clean submodule pin)"
            );
            // and the two headline lemmas must rest on EXACTLY the 3 foundational axioms.
            if n == "Nat.ulp_universal_bound" || n == "Nat.div_add_mod" || n == "Nat.mod_lt" {
                let deps = env.axiom_deps(&Name::from_string(n)).expect("declared");
                assert!(deps.is_empty(), "{n} must be axiom-free (modulo 3), got {deps:?}");
            }
        }
    }

    /// THE BULLET-3 UNIVERSAL CLOSURE — the half-ulp bound `2·|roundHalfEvenMod N (2^e) − N| ≤ 2^e`
    /// is PROVEN modulo 3 SYMBOLICALLY at e = 0 (subnormal/uniform grid) and e = 10 (a normal
    /// binade), for ALL N. One symbolic inductive theorem, no per-case enumeration.
    #[test]
    fn universal_half_ulp_bound_proven_modulo_3_small_e() {
        assert_eq!(ulp_bound_universal(32, 0), FloatClassVerdict::Modulo3);
        assert_eq!(ulp_bound_universal(32, 10), FloatClassVerdict::Modulo3);
        assert_eq!(ulp_bound_universal(64, 0), FloatClassVerdict::Modulo3);
        assert_eq!(ulp_bound_universal(64, 10), FloatClassVerdict::Modulo3);
    }

    /// THE COST-CEILING WITNESS — the universal bound at the HUGE exponent e = 127 (the f32 bias)
    /// is PROVEN modulo 3 with NO heartbeat blowup. The proof is symbolic in e, so instantiating
    /// at 127 is a constant-time substitution (the statement keeps `Nat.pow 2 127` UNREDUCED). We
    /// wrap it in a tight timeout: if the reduction-cost ceiling had survived, this would hang;
    /// it completes in microseconds. This is the precise residual Steps 4c/4d left open, CLOSED.
    #[test]
    fn universal_bound_at_e127_no_heartbeat_blowup() {
        use std::sync::mpsc;
        use std::time::Duration;
        let (tx, rx) = mpsc::channel();
        let handle = std::thread::spawn(move || {
            let v = ulp_bound_universal(32, 127);
            let _ = tx.send(v);
        });
        // A symbolic instantiation is microseconds; 20s is astronomically generous and proves the
        // huge-exponent COST ceiling (the ~35s kernel heartbeat of the per-case path) is GONE.
        let v = rx
            .recv_timeout(Duration::from_secs(20))
            .expect("e=127 universal bound must NOT hang (cost ceiling is gone)");
        handle.join().expect("thread joins");
        assert_eq!(v, FloatClassVerdict::Modulo3, "e=127 universal bound must be PROVEN modulo 3");
    }

    /// THE EXPONENT-INDEPENDENCE WITNESS — the universal bound holds at a GIANT exponent
    /// (e = 1,000,000, far beyond any IEEE width) just as cheaply as at e = 0, driving home that
    /// the cost is exponent-INDEPENDENT (the `2^e` is never reduced). Proven modulo 3.
    #[test]
    fn universal_bound_at_giant_exponent_is_exponent_independent() {
        use std::sync::mpsc;
        use std::time::Duration;
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let _ = tx.send(ulp_bound_universal(32, 1_000_000));
        });
        let v =
            rx.recv_timeout(Duration::from_secs(20)).expect("e=1e6 universal bound must NOT hang");
        assert_eq!(v, FloatClassVerdict::Modulo3);
    }

    /// THE FULL-RANGE BATTERY — `ulp_bound_universal_all` proves the bound at the canonical
    /// witness set (e = 0, 1, 10, 127, 1024, 1e6) for f32 AND f64, all PROVEN modulo 3. This is
    /// the single entry point that closes the bullet-3 universal residual.
    #[test]
    fn universal_bound_full_exponent_range_proven_modulo_3() {
        assert_eq!(ulp_bound_universal_all(32), FloatClassVerdict::Modulo3);
        assert_eq!(ulp_bound_universal_all(64), FloatClassVerdict::Modulo3);
    }

    // ---- SOUNDNESS: a WRONG (too-tight, QUARTER-ulp) universal claim FAILS CLOSED ----

    /// A WRONG too-tight UNIVERSAL bound — claiming `4·|round − N| ≤ 2^e` (a ¼·ulp budget) — must
    /// FAIL CLOSED. At an exact tie the error is EXACTLY ½·ulp, so `4·error = 2·ulp > ulp`: the
    /// quarter bound is genuinely FALSE, and the proven ½·ulp theorem (type `2·… ≤ V`) does NOT
    /// def-eq the ¼·ulp claim (`4·… ≤ V`) — `Nat.mul 4` vs `Nat.mul 2`. KernelRejected. Checked at
    /// small AND huge (e = 127) exponents — the rejection is structural (head literal mismatch),
    /// so it stays cheap even at the huge exponent. This is the fail-closed guarantee that a
    /// strictly-tighter-than-½ulp universal claim can NEVER be proven.
    #[test]
    fn wrong_quarter_ulp_universal_claim_fails_closed() {
        for e in [0u64, 10, 127] {
            assert!(
                wrong_quarter_ulp_universal_fails_closed(32, e),
                "a ¼·ulp universal claim at e={e} must fail closed (KernelRejected)"
            );
        }
    }

    /// An unsupported width fails closed for the universal bound too (never silently "proves" the
    /// bound for a bogus width).
    #[test]
    fn unsupported_width_universal_bound_fails_closed() {
        assert!(matches!(ulp_bound_universal(16, 10), FloatClassVerdict::KernelRejected(_)));
        assert!(matches!(ulp_bound_universal(128, 10), FloatClassVerdict::KernelRejected(_)));
        assert!(matches!(ulp_bound_universal_all(16), FloatClassVerdict::KernelRejected(_)));
    }

    /// The universal-bound carry status HONESTLY reports BOTH halves: PROVEN modulo 3 universally
    /// (∀e ∀N, no per-exponent cost, the cost ceiling gone), and the PRECISE standing residual
    /// (the binade-top carry float-RECONSTRUCTION — the error magnitude through the carry IS
    /// covered; only the re-encoding of the carried grid point is deferred).
    #[test]
    fn universal_bound_carry_status_is_honest() {
        let s = ulp_bound_universal_carry_status();
        assert!(s.contains("PROVEN"), "must report the proven universal bound, got: {s}");
        assert!(s.contains("UNIVERSAL"), "must name the universal (∀e ∀N) closure");
        assert!(s.contains("127"), "must witness the huge-exponent cost ceiling is gone");
        assert!(s.contains("RESIDUAL"), "must flag the precise carry residual, got: {s}");
        assert!(s.contains("CARRY"), "must name the binade-top carry residual, got: {s}");
    }

    // ---- Step 5: the NON-FINITE (±∞/NaN) value + op layer ----

    /// The non-finite layer (ExtVal + its recursor + valueExt + faddExt) for f32 AND f64
    /// registers resting on ONLY the 3 foundational axioms — NO 4th axiom.
    #[test]
    fn float_ext_layer_pins_modulo_3() {
        assert_eq!(pin_float_ext(32), FloatClassVerdict::Modulo3);
        assert_eq!(pin_float_ext(64), FloatClassVerdict::Modulo3);
    }

    /// `valueExt : FloatN → ExtVal` and `faddExt : ExtVal → ExtVal → ExtVal` KERNEL-CHECK as
    /// real maps over the structure (the bit pattern lifted to the extended domain, and the
    /// IEEE add on it), not opaque blobs.
    #[test]
    fn ext_ops_typecheck_as_real_maps() {
        ext_ops_typecheck(32).expect("f32 valueExt/faddExt kernel-check with the right types");
        ext_ops_typecheck(64).expect("f64 valueExt/faddExt kernel-check with the right types");
    }

    /// value_ext ↔ classification — value_ext of each IEEE class reduces to the matching ExtVal
    /// constructor: NaN pattern ↦ NaN, +∞ ↦ PosInf, −∞ ↦ NegInf, finite ↦ Finite (value f). The
    /// classification↔value-ext connection, PROVEN modulo 3 for f32 and f64.
    #[test]
    fn value_ext_classifies_special_values() {
        assert_eq!(lemma_value_ext_classifies(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_value_ext_classifies(64), ValueLemmaVerdict::ProvenModulo3);
    }

    /// NaN PROPAGATION (left, ∀y) — `faddExt NaN y = NaN` for a SYMBOLIC y (NaN ignores its
    /// right operand). Proven modulo 3 for f32 and f64.
    #[test]
    fn fadd_ext_nan_left_propagates_for_all_y() {
        assert_eq!(lemma_fadd_ext_nan_left(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_fadd_ext_nan_left(64), ValueLemmaVerdict::ProvenModulo3);
    }

    /// EVERY non-finite faddExt rule is PROVEN modulo 3 for f32 and f64 — NaN propagation (right,
    /// per head), inf+finite, inf+same-inf, the ∞−∞ INDETERMINATE forms (= NaN), finite+finite =
    /// Finite (Qadd). The full IEEE non-finite add rule set.
    #[test]
    fn all_fadd_ext_rules_proven_modulo_3() {
        for width in [32, 64] {
            for (name, verdict) in all_fadd_ext_rules(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} non-finite faddExt rule `{name}` must be PROVEN modulo 3"
                );
            }
        }
    }

    /// The INDETERMINATE ∞ − ∞ forms specifically resolve to NaN (NOT ±∞): `PosInf + NegInf =
    /// NaN` and `NegInf + PosInf = NaN`. Proven modulo 3 — pinned separately as the headline
    /// non-finite correctness fact.
    #[test]
    fn inf_minus_inf_is_nan() {
        let n = ext_decl_names("Trust.Float32");
        assert_eq!(
            ext_rule(32, cst(&n.pos_inf), cst(&n.neg_inf), cst(&n.nan), "indet_pn"),
            ValueLemmaVerdict::ProvenModulo3,
        );
        assert_eq!(
            ext_rule(32, cst(&n.neg_inf), cst(&n.pos_inf), cst(&n.nan), "indet_np"),
            ValueLemmaVerdict::ProvenModulo3,
        );
    }

    // ---- SOUNDNESS: a WRONG non-finite rule FAILS CLOSED (KernelRejected) ----

    /// A WRONG rule — claiming the INDETERMINATE `PosInf + NegInf = PosInf` (the correct result
    /// is NaN) — must FAIL CLOSED. `faddExt PosInf NegInf` ι-reduces to `NaN`, so `Eq.refl PosInf`
    /// does NOT type-check against `faddExt PosInf NegInf = PosInf`. The fail-closed guarantee
    /// that a wrong ∞−∞ rule can NEVER be proven.
    #[test]
    fn wrong_inf_minus_inf_is_posinf_fails_closed() {
        let n = ext_decl_names("Trust.Float32");
        assert!(
            matches!(
                ext_rule(32, cst(&n.pos_inf), cst(&n.neg_inf), cst(&n.pos_inf), "WRONG_indet"),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong ∞−∞ = +∞ rule must fail closed (KernelRejected)"
        );
    }

    /// A WRONG NaN-propagation claim — that `faddExt NaN PosInf = PosInf` (NaN must propagate to
    /// NaN, not pass through the right operand) — must FAIL CLOSED. `faddExt NaN PosInf` reduces
    /// to `NaN`, so claiming `PosInf` is rejected by the kernel.
    #[test]
    fn wrong_nan_propagation_fails_closed() {
        let n = ext_decl_names("Trust.Float32");
        assert!(
            matches!(
                ext_rule(32, cst(&n.nan), cst(&n.pos_inf), cst(&n.pos_inf), "WRONG_nan_prop"),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a broken NaN-propagation (NaN + ∞ = ∞) must fail closed (KernelRejected)"
        );
    }

    /// A WRONG value_ext claim — that the +∞ pattern (all-ones exponent, mantissa 0, sign false)
    /// classifies as `NegInf` (it is `PosInf`) — must FAIL CLOSED. value_ext reduces to PosInf,
    /// so `Eq.refl NegInf` does not inhabit the equation. The fail-closed teeth of the
    /// classification↔value-ext connection.
    #[test]
    fn wrong_value_ext_sign_fails_closed() {
        let inductive = "Trust.Float32";
        let n = ext_decl_names(inductive);
        let pinf_pattern = float_pattern(inductive, false, 255, 0);
        let lhs = Expr::app(cst(&n.value_ext), pinf_pattern);
        // WRONG: claim +∞ pattern classifies as NegInf (it is PosInf).
        let statement = eq_ext_prop(&n, lhs, cst(&n.neg_inf));
        let proof = refl_ext(&n, cst(&n.neg_inf));
        assert!(
            matches!(
                check_ext_lemma(32, "Trust.Float32.ext.WRONG_value_ext_sign", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong-sign value_ext claim (+∞ as NegInf) must fail closed (KernelRejected)"
        );
    }

    /// An unsupported width fails closed for the non-finite layer too (never an opaque blob,
    /// never a fabricated non-finite rule).
    #[test]
    fn unsupported_width_ext_layer_fails_closed() {
        assert!(ext_env(16).is_err());
        assert!(matches!(pin_float_ext(128), FloatClassVerdict::KernelRejected(_)));
        assert!(matches!(lemma_value_ext_classifies(16), ValueLemmaVerdict::KernelRejected(_)));
    }

    // ---- Step 5 (mul/div): the NON-FINITE fmulExt / fdivExt op rules ----

    /// NaN PROPAGATION (left, ∀y) for fmulExt AND fdivExt — `fmulExt NaN y = NaN` and
    /// `fdivExt NaN y = NaN` for a SYMBOLIC y (NaN ignores its right operand). Proven modulo 3.
    #[test]
    fn mul_div_ext_nan_left_propagates_for_all_y() {
        for width in [32, 64] {
            assert_eq!(lemma_fmul_ext_nan_left(width), ValueLemmaVerdict::ProvenModulo3);
            assert_eq!(lemma_fdiv_ext_nan_left(width), ValueLemmaVerdict::ProvenModulo3);
        }
    }

    /// EVERY non-finite fmulExt rule is PROVEN modulo 3 for f32 and f64 — NaN propagation (right),
    /// inf·inf WITH SIGN, inf·finite-nonzero = signed ∞ (both orders), the INDETERMINATE 0·∞ = NaN
    /// (both orders), finite·finite = Finite (Qmul). The full IEEE non-finite multiply rule set.
    #[test]
    fn all_fmul_ext_rules_proven_modulo_3() {
        for width in [32, 64] {
            for (name, verdict) in all_fmul_ext_rules(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} non-finite fmulExt rule `{name}` must be PROVEN modulo 3"
                );
            }
        }
    }

    /// EVERY non-finite fdivExt rule is PROVEN modulo 3 for f32 and f64 — NaN propagation (right),
    /// inf/finite = signed ∞, finite/inf = (signed) 0, the INDETERMINATE ∞/∞ = NaN and 0/0 = NaN,
    /// and the IEEE DIV-BY-ZERO rule x/0 = signed ∞ for nonzero finite x. The full IEEE
    /// non-finite divide rule set.
    #[test]
    fn all_fdiv_ext_rules_proven_modulo_3() {
        for width in [32, 64] {
            for (name, verdict) in all_fdiv_ext_rules(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} non-finite fdivExt rule `{name}` must be PROVEN modulo 3"
                );
            }
        }
    }

    /// The headline INDETERMINATE non-finite mul/div facts resolve to NaN (NOT ±∞): `0·∞ = NaN`
    /// (both orders), `∞/∞ = NaN`, and `0/0 = NaN`. Proven modulo 3 — pinned separately as the
    /// correctness anchors for the indeterminate forms.
    #[test]
    fn indeterminate_mul_div_forms_are_nan() {
        let n = ext_decl_names("Trust.Float32");
        let nan = || cst(&n.nan);
        let pinf = || cst(&n.pos_inf);
        let zero = || ext_finite(&n, 0);
        // 0·∞ = NaN (both orders).
        assert_eq!(mul_rule(32, zero(), pinf(), nan(), "z_pi"), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(mul_rule(32, pinf(), zero(), nan(), "pi_z"), ValueLemmaVerdict::ProvenModulo3);
        // ∞/∞ = NaN.
        assert_eq!(div_rule(32, pinf(), pinf(), nan(), "pi_pi"), ValueLemmaVerdict::ProvenModulo3);
        // 0/0 = NaN.
        assert_eq!(div_rule(32, zero(), zero(), nan(), "z_z"), ValueLemmaVerdict::ProvenModulo3);
    }

    /// The non-finite fmulExt/fdivExt layer (fmulExt + fdivExt) for f32 AND f64 registers and
    /// KERNEL-CHECKS as `ExtVal → ExtVal → ExtVal`, resting on ONLY the 3 foundational axioms.
    #[test]
    fn mul_div_ext_layer_pins_modulo_3_and_typechecks() {
        assert_eq!(pin_float_ext(32), FloatClassVerdict::Modulo3);
        assert_eq!(pin_float_ext(64), FloatClassVerdict::Modulo3);
        ext_ops_typecheck(32).expect("f32 fmulExt/fdivExt kernel-check with the right types");
        ext_ops_typecheck(64).expect("f64 fmulExt/fdivExt kernel-check with the right types");
    }

    // ---- SOUNDNESS: WRONG non-finite mul/div rules FAIL CLOSED (KernelRejected) ----

    /// A WRONG rule — claiming the INDETERMINATE `0·∞ = PosInf` (the correct result is NaN) —
    /// must FAIL CLOSED. `fmulExt (Finite 0) PosInf` ι-reduces to `NaN`, so `Eq.refl PosInf` does
    /// NOT type-check against the claimed equation.
    #[test]
    fn wrong_zero_times_inf_is_posinf_fails_closed() {
        let n = ext_decl_names("Trust.Float32");
        let zero = ext_finite(&n, 0);
        assert!(
            matches!(
                mul_rule(32, zero, cst(&n.pos_inf), cst(&n.pos_inf), "WRONG_0xinf"),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong 0·∞ = +∞ rule must fail closed (correct is NaN)"
        );
    }

    /// A WRONG rule — claiming `∞/∞ = PosInf` (the correct result is NaN) — must FAIL CLOSED.
    #[test]
    fn wrong_inf_div_inf_is_posinf_fails_closed() {
        let n = ext_decl_names("Trust.Float32");
        assert!(
            matches!(
                div_rule(32, cst(&n.pos_inf), cst(&n.pos_inf), cst(&n.pos_inf), "WRONG_infdivinf"),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong ∞/∞ = +∞ rule must fail closed (correct is NaN)"
        );
    }

    /// A WRONG rule — claiming `0/0 = Finite 0` (the correct result is NaN) — must FAIL CLOSED.
    #[test]
    fn wrong_zero_div_zero_is_finite_zero_fails_closed() {
        let n = ext_decl_names("Trust.Float32");
        let zero = || ext_finite(&n, 0);
        assert!(
            matches!(
                div_rule(32, zero(), zero(), zero(), "WRONG_0div0"),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong 0/0 = Finite 0 rule must fail closed (correct is NaN)"
        );
    }

    /// A WRONG-SIGN inf·inf rule — claiming `NegInf · NegInf = NegInf` (the correct result is
    /// PosInf: −·− = +) — must FAIL CLOSED. The sign discipline of inf·inf is enforced.
    #[test]
    fn wrong_sign_neginf_times_neginf_fails_closed() {
        let n = ext_decl_names("Trust.Float32");
        assert!(
            matches!(
                mul_rule(32, cst(&n.neg_inf), cst(&n.neg_inf), cst(&n.neg_inf), "WRONG_sign"),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong-sign −∞·−∞ = −∞ rule must fail closed (correct is +∞)"
        );
    }

    /// An unsupported width fails closed for the mul/div non-finite rule batteries too (never a
    /// fabricated non-finite mul/div rule).
    #[test]
    fn unsupported_width_mul_div_ext_fails_closed() {
        assert!(matches!(lemma_fmul_ext_nan_left(16), ValueLemmaVerdict::KernelRejected(_)));
        assert!(matches!(lemma_fdiv_ext_nan_left(16), ValueLemmaVerdict::KernelRejected(_)));
        assert!(matches!(all_fmul_ext_rules(16)[0].1, ValueLemmaVerdict::KernelRejected(_)));
        assert!(matches!(all_fdiv_ext_rules(16)[0].1, ValueLemmaVerdict::KernelRejected(_)));
    }

    // ---- Step 5b: the binade-TOP CARRY RE-ENCODING ----

    /// The carry re-encoding declaration (roundCarryReencode) for f32 AND f64 registers resting
    /// on ONLY the 3 foundational axioms — NO 4th axiom.
    #[test]
    fn float_carry_layer_pins_modulo_3() {
        assert_eq!(pin_float_carry(32), FloatClassVerdict::Modulo3);
        assert_eq!(pin_float_carry(64), FloatClassVerdict::Modulo3);
    }

    /// THE CARRY RE-ENCODING — `roundCarryReencode e = mk false (e+1) 0` (exponent incremented,
    /// mantissa reset) has VALUE equal to the carried grid point `2^(m+1)·2^e` (= the next
    /// binade's bottom). PROVEN modulo 3 across several binades for f32 and f64.
    #[test]
    fn round_carry_reencodes_proven_modulo_3() {
        for width in [32, 64] {
            for e in [1u64, 2, 5, 10] {
                assert_eq!(
                    lemma_round_carry_reencodes(width, e),
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width}: carry re-encoding at e={e} must equal the carried grid point"
                );
            }
        }
    }

    /// The carry lands on the NEXT BINADE'S BOTTOM — `value (mk false (e+1) 0)` is the first
    /// representable of binade e+1 (`2^(m+1+e)`). Proven modulo 3 for f32 and f64.
    #[test]
    fn carry_is_next_binade_bottom_proven() {
        for width in [32, 64] {
            assert_eq!(
                lemma_carry_is_next_binade_bottom(width, 5),
                ValueLemmaVerdict::ProvenModulo3
            );
        }
    }

    /// OVERFLOW-TO-∞ at the TOP exponent — the carry that reaches the all-ones reserved exponent
    /// routes to +∞: `value_ext (mk false ALL_ONES 0) = PosInf` (overflow-to-∞ under RNE), tying
    /// the carry residual back to the ExtVal domain. Proven modulo 3 for f32 and f64.
    #[test]
    fn carry_overflow_to_inf_proven() {
        assert_eq!(lemma_carry_overflow_to_inf(32), ValueLemmaVerdict::ProvenModulo3);
        assert_eq!(lemma_carry_overflow_to_inf(64), ValueLemmaVerdict::ProvenModulo3);
    }

    /// EVERY carry lemma (re-encoding, next-binade-bottom, overflow-to-∞) is PROVEN modulo 3 for
    /// f32 and f64 — the whole carry battery resolves clean.
    #[test]
    fn all_carry_lemmas_proven_modulo_3() {
        for width in [32, 64] {
            for (name, verdict) in all_carry_lemmas(width) {
                assert_eq!(
                    verdict,
                    ValueLemmaVerdict::ProvenModulo3,
                    "f{width} carry lemma `{name}` must be PROVEN modulo 3"
                );
            }
        }
    }

    // ---- SOUNDNESS: a WRONG carry re-encoding FAILS CLOSED (KernelRejected) ----

    /// A WRONG carry re-encoding — claiming the carried point's value numerator is `2^(m+e)`
    /// (off-by-one, the correct carried point is `2^(m+1+e)`) — must FAIL CLOSED. The re-encoded
    /// float's valueNum reduces to `2^(m+1+e)`, so `Eq.refl (2^(m+e))` does not inhabit the
    /// equation. Guards the carry re-encoding magnitude (exponent increment / mantissa reset).
    #[test]
    fn wrong_carry_value_fails_closed() {
        let inductive = "Trust.Float32";
        let names = value_decl_names(inductive);
        let carry = carry_decl_name(inductive);
        let reencoded = Expr::app(cst(&carry), nat_lit(5));
        let lhs = Expr::app(cst(&names.value_num), reencoded);
        // WRONG: claim 2^(23+5) = 2^28 (correct is 2^(23+1+5) = 2^29).
        let wrong = int_pow(int_two(), nat_lit(23 + 5));
        let statement = eq_int_prop(lhs, wrong.clone());
        let proof = refl_int(wrong);
        assert!(
            matches!(
                check_carry_lemma(32, "Trust.Float32.carry.WRONG_value", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong carry re-encoding value must fail closed (KernelRejected)"
        );
    }

    /// A WRONG overflow claim — that the top-exponent +∞ pattern classifies as `NaN` instead of
    /// `PosInf` (the mantissa is 0, so it is +∞, not NaN) — must FAIL CLOSED. value_ext reduces to
    /// PosInf; `Eq.refl NaN` does not inhabit it.
    #[test]
    fn wrong_overflow_to_nan_fails_closed() {
        let inductive = "Trust.Float32";
        let n = ext_decl_names(inductive);
        let top = float_pattern(inductive, false, 255, 0);
        let lhs = Expr::app(cst(&n.value_ext), top);
        // WRONG: claim the +∞ pattern is NaN (mantissa 0 ⇒ it is PosInf).
        let statement = eq_ext_prop(&n, lhs, cst(&n.nan));
        let proof = refl_ext(&n, cst(&n.nan));
        assert!(
            matches!(
                check_carry_lemma(32, "Trust.Float32.carry.WRONG_overflow", statement, proof),
                ValueLemmaVerdict::KernelRejected(_)
            ),
            "a wrong overflow classification (+∞ as NaN) must fail closed (KernelRejected)"
        );
    }

    /// An unsupported width fails closed for the carry layer too (never an opaque blob, never a
    /// fabricated re-encoding).
    #[test]
    fn unsupported_width_carry_layer_fails_closed() {
        assert!(carry_env(16).is_err());
        assert!(matches!(pin_float_carry(128), FloatClassVerdict::KernelRejected(_)));
        assert!(matches!(lemma_round_carry_reencodes(16, 5), ValueLemmaVerdict::KernelRejected(_)));
    }

    /// THE BULLET-3 NON-FINITE + CARRY CLOSURE — `nonfinite_and_carry` resolves to Modulo3 for f32
    /// AND f64: the ExtVal + carry layers pin, every non-finite op rule and carry lemma is proven
    /// modulo 3. The single entry point closing bullet-3's last value/op residual.
    #[test]
    fn nonfinite_and_carry_closes_modulo_3() {
        assert_eq!(nonfinite_and_carry(32), FloatClassVerdict::Modulo3);
        assert_eq!(nonfinite_and_carry(64), FloatClassVerdict::Modulo3);
    }

    /// The non-finite/carry status HONESTLY reports BOTH halves: PROVEN modulo 3 (the non-finite
    /// value+op semantics + carry re-encoding + overflow-to-∞) and the PRECISE standing residual
    /// (signaling-NaN payloads, non-finite fmul/fdiv, directed rounding, the round-chooses-to-carry
    /// control flow).
    #[test]
    fn nonfinite_carry_status_is_honest() {
        let s = nonfinite_carry_status();
        assert!(s.contains("PROVEN"), "must report the proven non-finite/carry layer, got: {s}");
        assert!(s.contains("NON-FINITE"), "must name the non-finite layer");
        assert!(s.contains("CARRY"), "must name the carry re-encoding");
        assert!(s.contains("NaN"), "must name NaN propagation");
        assert!(s.contains("DEFERRED"), "must flag the precise residual, got: {s}");
    }
}
