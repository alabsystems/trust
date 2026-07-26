// trust-clean/trustir_safety.rs — LANE S (the SAFETY-VC adequacy tier, RELOCATED
// from the hand-written `Trust.MirSem` model ONTO the trust-ir denotation).
//
// WHY THIS EXISTS (the MirSem-teardown prerequisite this closes).
// The 8 safety-VC kinds' machine-semantics conditions were pinned in Clean under
// `Trust.MirSem.*` names (`mirsem.rs` Lemmas 2–9), and the FORMULA-AWARE adequacy
// (`mirsem::safety_vc_is_faithful_formula_aware`) kernel-checks each EMITTED
// `vc.formula`'s violation core — grounded through the LIVE
// `clean_ground::ground_prop` — def-eq to those pinned specs. That tier was the
// largest remaining consumer of the MirSem environment on the via-trustir §6
// path: `prove::function_fully_faithful_via_trustir` deferred safety-VC KERNEL
// adequacy to the MirSem outer gate (running only the pure kind classifier +
// the vc_refute discharge gate itself).
//
// THIS MODULE re-pins the SAME 8 machine-semantics conditions — byte-identical
// spec BODIES, since they were empirically matched to `trust_vcgen::generate_vcs`
// output and to the live grounder's term shapes — under `Trust.TrustIr.*` names,
// registered into the SELF-CONTAINED trust-ir environment
// (`trustir_anchor::trustir_env()`, which carries ZERO `Trust.MirSem.*`
// declarations; that separation is load-bearing). The formula-aware bridge is
// mirrored exactly: for each emitted safety VC, the ACTUAL `vc.formula`'s
// violation core is grounded via the LIVE `clean_ground::ground_prop` /
// `ground_int` and kernel-checked def-eq (modulo the 3 foundational axioms) to
// the trust-ir spec — the certified term IS the live grounder's output, never a
// `spec = spec` tautology (the post-audit integrity property; see the mirsem.rs
// "FORMULA-AWARE safety-VC faithfulness" block for the audit history).
//
// THE 8 MODELED KINDS (all shapes COPIED from the MirSem lemmas, not invented):
//   1. UNSIGNED-ADD OVERFLOW  (Lemma 2)  `uaddOverflowsU{8,16,32,64} a b :=
//        Int.lt (Int.ofNat (2^W−1)) (Int.add a b)`            — core `Gt(a+b, MAX)`
//   2. ARRAY/SLICE BOUNDS     (Lemma 3)  `idxOob len i := Int.le len i`
//                                                             — core `Ge(i, len)`
//   3. DIVISION BY ZERO       (Lemma 4)  `divByZero b := @Eq Int b 0`
//                                                             — core `Eq(b, 0)`
//   4. SIGNED ADD/SUB/MUL OVERFLOW (Lemma 5)
//        `s{add,sub,mul}OverflowsI{W} a b := (a∘b < −2^(W−1)) ∨ (2^(W−1)−1 < a∘b)`
//                                     — core `Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])`
//   5. NEGATION OVERFLOW      (Lemma 6)  `negOverflowsI{W} x := @Eq Int x (−2^(W−1))`
//                                                             — core `Eq(x, MIN)`
//   6. SHIFT-AMOUNT OOB       (Lemma 7)  `shiftAmountOob{,Signed}{W} n :=
//        W ≤ n  /  (n < 0) ∨ (W ≤ n)`   — core `Ge(n, W)` / `Or([Lt(n,0), Ge(n,W)])`
//        (W ∈ {8,16,32,64,128} — the one lane that models the 128-bit value widths)
//   7. UNSIGNED-SUB UNDERFLOW (Lemma 8)  `usubUnderflowsU{W} a b :=
//        Int.lt (Int.sub a b) (Int.ofNat 0)`                  — core `Lt(a−b, 0)`
//   8. REMAINDER BY ZERO      (Lemma 9)  `remByZero b := @Eq Int b 0`
//                                                             — core `Eq(b, 0)`
//
// SOUNDNESS DISCIPLINE (mirrors mirsem.rs / trustir_anchor.rs exactly).
//   * Every registered spec + every adequacy theorem kernel-checks with
//     `axiom_deps ⊆ {propext, Quot.sound, Classical.choice}` — modulo exactly 3
//     axioms, no 4th, no new free constant (`pin_trustir_safety_anchor`).
//   * FAIL-CLOSED: an unmodeled kind (`CastOverflow`, `FloatDivisionByZero`,
//     `i128`/`u128` OVERFLOW widths — whose `2^W−1`/`±2^(W−1)` thresholds leave
//     the closed-literal fragment; the SHIFT lane's width-literal threshold stays
//     closed at 128 and IS modeled), a violation core outside the formula-aware
//     fragment (the `var*var` BV signed mul), or an emitted threshold that matches
//     no modeled width (the `1i32<<n` operand_ty desync) is `KernelRejected` /
//     declined — never silently passed.
//   * The width/threshold is recovered FROM THE EMITTED FORMULA (never from
//     `operand_ty`) — the same audit fix `safety_vc_is_faithful_formula_aware`
//     carries.
//   * ADDITIVE: no MirSem declaration is touched; the trust-ir env stays free of
//     `Trust.MirSem.*` names; vc_refute.rs is consumed by prove.rs only, not here.
//
// HONEST DELTA vs the MirSem tier: NONE in the adequacy claim (same specs, same
// live-grounder bridge, same fail-closed edges). The residual MirSem consumption
// in prove.rs (loop termination witnesses etc.) is out of this module's scope.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::HashMap;

use clean_kernel::{
    BinderData, BinderInfo, Declaration, Environment, Expr, Level, LevelVec, Name, TypeChecker,
};

use crate::trustir_anchor::{AnchorVerdict, RefinementVerdict, trustir_env};

// ---------------------------------------------------------------------------
// Small kernel-term builders (shared de-Bruijn convention with clean_ground.rs)
// ---------------------------------------------------------------------------

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

fn int_ty() -> Expr {
    cst("Int")
}

/// The closed `Int` literal `Expr` for `n`, BYTE-IDENTICAL to
/// `clean_ground::int_lit_to_expr` (`Int.ofNat n` / `Int.negSucc (−n−1)`), so every
/// spec threshold is the exact term the live grounder emits for `Formula::Int(n)`.
fn int_lit(n: i128) -> Expr {
    // Trust: EXACT ENCODING (2026-07-24) — `Expr::nat_lit_u128` covers the FULL
    // magnitude range. The former `as u64` was `n mod 2^64`, a SILENT TRUNCATION that
    // made this map NON-INJECTIVE and caused a demonstrated LIVE FALSE ACCEPT (see
    // `clean_ground::int_lit_to_expr`). Byte-identity with the other encoders is
    // PRESERVED, and so is every existing term: `BigNat::from_limbs` normalizes a
    // trailing zero limb back to `BigNat::Small`, so `nat_lit_u128(k) == nat_lit(k)`
    // for every `k <= u64::MAX` (asserted by `int_lit_encoders_agree_and_are_exact`).
    // `Int.negSucc` carries `|n| - 1`, which fits `u128` for every `i128` (including
    // `i128::MIN`, where `-n` is not representable).
    if n >= 0 {
        Expr::app(cst("Int.ofNat"), Expr::nat_lit_u128(n.unsigned_abs()))
    } else {
        Expr::app(cst("Int.negSucc"), Expr::nat_lit_u128(n.unsigned_abs() - 1))
    }
}

// ---------------------------------------------------------------------------
// The modeled widths / ops — the trust-ir-keyed analogues of mirsem's
// `UWidth`/`SWidth`/`SignedOp` (kept LOCAL so this tier carries no mirsem
// dependency the teardown would have to unpick).
// ---------------------------------------------------------------------------

/// The unsigned integer widths the trust-ir safety tier pins specs for — exactly
/// the `u8`/`u16`/`u32`/`u64` widths whose `2^W − 1` threshold is a closed prelude
/// `Int.ofNat` literal (`u128` is out of the literal fragment, matching trust-vcgen).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrUWidth {
    /// `u8` — threshold `255`.
    W8,
    /// `u16` — threshold `65535`.
    W16,
    /// `u32` — threshold `4294967295`.
    W32,
    /// `u64` — threshold `18446744073709551615`.
    W64,
}

impl IrUWidth {
    /// The bit width `W`.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            IrUWidth::W8 => 8,
            IrUWidth::W16 => 16,
            IrUWidth::W32 => 32,
            IrUWidth::W64 => 64,
        }
    }

    /// The overflow threshold `2^W − 1` — the exact `i128` literal
    /// `trust-vcgen::range::type_max_formula(W, false)` emits.
    #[must_use]
    pub fn max_value(self) -> i128 {
        (1i128 << self.bits()) - 1
    }

    /// Map a Trust MIR integer type to the modeled unsigned width; `None` (out of
    /// fragment) for a signed type or an unmodeled width (`u128`).
    #[must_use]
    pub fn from_mir(width: u32, signed: bool) -> Option<IrUWidth> {
        if signed {
            return None;
        }
        match width {
            8 => Some(IrUWidth::W8),
            16 => Some(IrUWidth::W16),
            32 => Some(IrUWidth::W32),
            64 => Some(IrUWidth::W64),
            _ => None,
        }
    }

    const ALL: [IrUWidth; 4] = [IrUWidth::W8, IrUWidth::W16, IrUWidth::W32, IrUWidth::W64];
}

/// The signed integer widths the trust-ir safety tier pins specs for —
/// `i8`/`i16`/`i32`/`i64`, whose `±2^(W−1)` thresholds are closed prelude
/// `Int.ofNat`/`Int.negSucc` literals (`i128` is out of the fragment).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrSWidth {
    /// `i8` — range `[−128, 127]`.
    W8,
    /// `i16` — range `[−32768, 32767]`.
    W16,
    /// `i32` — range `[−2147483648, 2147483647]`.
    W32,
    /// `i64` — range `[−2^63, 2^63−1]`.
    W64,
}

impl IrSWidth {
    /// The bit width `W`.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            IrSWidth::W8 => 8,
            IrSWidth::W16 => 16,
            IrSWidth::W32 => 32,
            IrSWidth::W64 => 64,
        }
    }

    /// The signed MAX `2^(W−1) − 1` — the exact literal trust-vcgen emits.
    #[must_use]
    pub fn max_value(self) -> i128 {
        (1i128 << (self.bits() - 1)) - 1
    }

    /// The signed MIN `−2^(W−1)` — the exact literal trust-vcgen emits.
    #[must_use]
    pub fn min_value(self) -> i128 {
        -(1i128 << (self.bits() - 1))
    }

    /// Map a bit width to the modeled signed width (`8/16/32/64`), else `None`.
    #[must_use]
    pub fn from_bits(width: u32) -> Option<IrSWidth> {
        match width {
            8 => Some(IrSWidth::W8),
            16 => Some(IrSWidth::W16),
            32 => Some(IrSWidth::W32),
            64 => Some(IrSWidth::W64),
            _ => None,
        }
    }

    const ALL: [IrSWidth; 4] = [IrSWidth::W8, IrSWidth::W16, IrSWidth::W32, IrSWidth::W64];
}

/// The shifted-VALUE widths the trust-ir safety tier pins SHIFT-AMOUNT-OOB specs
/// for — `8/16/32/64/128`. UNLIKE the overflow lanes (whose `2^W−1` / `±2^(W−1)`
/// threshold literals leave the closed `Int.ofNat` fragment at `W = 128`), the
/// shift lane's threshold is the WIDTH ITSELF (`n ≥ W`), and `128` is a small
/// closed literal — so the `i128`/`u128` value widths ARE modeled here (the
/// "128-bit shift VC width" residue closure; a threshold matching none of these
/// still fails closed).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrShiftWidth {
    /// 8-bit shifted value — UB threshold `n ≥ 8`.
    W8,
    /// 16-bit shifted value — UB threshold `n ≥ 16`.
    W16,
    /// 32-bit shifted value — UB threshold `n ≥ 32`.
    W32,
    /// 64-bit shifted value — UB threshold `n ≥ 64`.
    W64,
    /// 128-bit shifted value (`i128`/`u128`) — UB threshold `n ≥ 128`.
    W128,
}

impl IrShiftWidth {
    /// The bit width `W` — the shift-amount-OOB threshold literal itself.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            IrShiftWidth::W8 => 8,
            IrShiftWidth::W16 => 16,
            IrShiftWidth::W32 => 32,
            IrShiftWidth::W64 => 64,
            IrShiftWidth::W128 => 128,
        }
    }

    /// Map an emitted threshold to the modeled shift width (`8/16/32/64/128`),
    /// else `None` (fail closed).
    #[must_use]
    pub fn from_bits(width: u32) -> Option<IrShiftWidth> {
        match width {
            8 => Some(IrShiftWidth::W8),
            16 => Some(IrShiftWidth::W16),
            32 => Some(IrShiftWidth::W32),
            64 => Some(IrShiftWidth::W64),
            128 => Some(IrShiftWidth::W128),
            _ => None,
        }
    }

    const ALL: [IrShiftWidth; 5] = [
        IrShiftWidth::W8,
        IrShiftWidth::W16,
        IrShiftWidth::W32,
        IrShiftWidth::W64,
        IrShiftWidth::W128,
    ];
}

/// The signed-overflow binops the tier models. ADD/SUB/MUL all ground to the same
/// LIA out-of-range disjunction; only the result head varies. MUL is modeled ONLY
/// for the LIA constant-multiplier emission — the `var*var` BV mul VC has no
/// `Or([Lt(Mul…),Gt(Mul…)])` leaf and DECLINES at the bridge (fail-closed), exactly
/// as in the MirSem Lemma-5 scope note.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrSignedOp {
    /// `a + b` — result head `Int.add`.
    Add,
    /// `a − b` — result head `Int.sub`.
    Sub,
    /// `a * b` — result head `Int.mul` (LIA constant-multiplier fragment only).
    Mul,
}

impl IrSignedOp {
    /// The prelude head for this op's Int result term.
    fn int_head(self) -> &'static str {
        match self {
            IrSignedOp::Add => "Int.add",
            IrSignedOp::Sub => "Int.sub",
            IrSignedOp::Mul => "Int.mul",
        }
    }

    /// The lowercase op tag used in the predicate name (`add`/`sub`/`mul`).
    fn tag(self) -> &'static str {
        match self {
            IrSignedOp::Add => "add",
            IrSignedOp::Sub => "sub",
            IrSignedOp::Mul => "mul",
        }
    }

    const ALL: [IrSignedOp; 3] = [IrSignedOp::Add, IrSignedOp::Sub, IrSignedOp::Mul];
}

// ---------------------------------------------------------------------------
// Canonical Clean names — Trust.TrustIr.* ONLY (the trust-ir env stays free of
// Trust.MirSem.* declarations; that separation is load-bearing).
// ---------------------------------------------------------------------------

/// `Trust.TrustIr.uaddOverflowsU{W}` — the unsigned-add machine-overflow predicate.
fn uadd_overflows_ir_name(w: IrUWidth) -> String {
    format!("Trust.TrustIr.uaddOverflowsU{}", w.bits())
}

/// `Trust.TrustIr.usubUnderflowsU{W}` — the unsigned-sub machine-underflow predicate.
fn usub_underflows_ir_name(w: IrUWidth) -> String {
    format!("Trust.TrustIr.usubUnderflowsU{}", w.bits())
}

/// `Trust.TrustIr.s{add,sub,mul}OverflowsI{W}` — the signed machine-overflow predicate.
fn signed_overflows_ir_name(op: IrSignedOp, w: IrSWidth) -> String {
    format!("Trust.TrustIr.s{}OverflowsI{}", op.tag(), w.bits())
}

/// `Trust.TrustIr.negOverflowsI{W}` — the signed negation-overflow predicate.
fn neg_overflows_ir_name(w: IrSWidth) -> String {
    format!("Trust.TrustIr.negOverflowsI{}", w.bits())
}

/// `Trust.TrustIr.shiftAmountOob{,Signed}{W}` — the shift-amount-UB predicate.
fn shift_amount_oob_ir_name(w: IrShiftWidth, amount_signed: bool) -> String {
    if amount_signed {
        format!("Trust.TrustIr.shiftAmountOobSigned{}", w.bits())
    } else {
        format!("Trust.TrustIr.shiftAmountOob{}", w.bits())
    }
}

/// `Trust.TrustIr.idxOob` — the index-out-of-bounds predicate (`len ≤ i`).
const TRUSTIR_IDX_OOB: &str = "Trust.TrustIr.idxOob";
/// `Trust.TrustIr.divByZero` — the division divisor-zero predicate (`b = 0`).
const TRUSTIR_DIV_BY_ZERO: &str = "Trust.TrustIr.divByZero";
/// `Trust.TrustIr.remByZero` — the remainder divisor-zero predicate (`b = 0`).
const TRUSTIR_REM_BY_ZERO: &str = "Trust.TrustIr.remByZero";

// ---------------------------------------------------------------------------
// Spec registration — the SAME machine-semantics bodies mirsem.rs pins (copied,
// not invented; empirically matched to trust_vcgen::generate_vcs + ground_prop),
// registered idempotently as reducible definitions.
// ---------------------------------------------------------------------------

/// Register a 2-argument predicate `name : Int → Int → Prop := λ a b. body(a, b)`
/// (idempotent). Inside the value, `a = bvar(1)`, `b = bvar(0)` — the shared
/// de-Bruijn convention with the adequacy statements.
fn register_int2_prop(
    env: &mut Environment,
    name: &str,
    body: impl FnOnce(&Expr, &Expr) -> Expr,
) -> Result<(), String> {
    let n = Name::from_string(name);
    if env.get_const(&n).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::prop()));
    let val =
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body(&Expr::bvar(1), &Expr::bvar(0))));
    env.add_decl(Declaration::Definition {
        name: n,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl({name}): {e:?}"))?;
    Ok(())
}

/// Register a 1-argument predicate `name : Int → Prop := λ x. body(x)` (idempotent).
fn register_int1_prop(
    env: &mut Environment,
    name: &str,
    body: impl FnOnce(&Expr) -> Expr,
) -> Result<(), String> {
    let n = Name::from_string(name);
    if env.get_const(&n).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ty = Expr::pi(bd(), int_ty(), Expr::prop());
    let val = Expr::lam(bd(), int_ty(), body(&Expr::bvar(0)));
    env.add_decl(Declaration::Definition {
        name: n,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl({name}): {e:?}"))?;
    Ok(())
}

/// `@Eq Int x lit` — the equality body shared by `divByZero`/`remByZero` (`lit = 0`)
/// and `negOverflowsIW` (`lit = MIN`). Built with the SAME `Eq.{1}` head + `int_lit`
/// literal the live grounder produces for `Formula::Eq(x, Int(lit))`.
fn eq_int_lit_body(x_ref: &Expr, lit: i128) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq, [int_ty(), x_ref.clone(), int_lit(lit)])
}

/// The signed out-of-range disjunction body
/// `Or (Int.lt (Int.<op> a b) MIN) (Int.lt MAX (Int.<op> a b))` — the EXACT term
/// `ground_prop(Or([Lt(a∘b,MIN), Gt(a∘b,MAX)]))` produces (`Lt` in order, `Gt`
/// swaps its arguments; the 2-element `Or` folds as `Or head tail`).
fn signed_out_of_range_body(op: IrSignedOp, a_ref: &Expr, b_ref: &Expr, w: IrSWidth) -> Expr {
    let result = || Expr::apps(cst(op.int_head()), [a_ref.clone(), b_ref.clone()]);
    let underflow = Expr::apps(cst("Int.lt"), [result(), int_lit(w.min_value())]);
    let overflow = Expr::apps(cst("Int.lt"), [int_lit(w.max_value()), result()]);
    Expr::apps(cst("Or"), [underflow, overflow])
}

/// The shift-amount-OOB body — `Int.le W n` (unsigned amount) or
/// `Or (Int.lt n 0) (Int.le W n)` (signed amount), the EXACT `ground_prop` output
/// for `Ge(n, Int(W))` / `Or([Lt(n,0), Ge(n,W)])` (`Ge` swaps its arguments).
fn shift_oob_body(n_ref: &Expr, w: IrShiftWidth, amount_signed: bool) -> Expr {
    let oob = Expr::apps(cst("Int.le"), [int_lit(i128::from(w.bits())), n_ref.clone()]);
    if amount_signed {
        let neg = Expr::apps(cst("Int.lt"), [n_ref.clone(), int_lit(0)]);
        Expr::apps(cst("Or"), [neg, oob])
    } else {
        oob
    }
}

/// Build the trust-ir SAFETY environment: the SELF-CONTAINED trust-ir anchor env
/// (`trustir_anchor::trustir_env()` — prelude + the Trust.TrustIr.* denotation, ZERO
/// `Trust.MirSem.*` declarations) EXTENDED with the 8 safety-VC kinds' machine-
/// semantics predicates under `Trust.TrustIr.*` names. The trust-ir analogue of
/// `mirsem::mirsem_safety_env`.
pub fn trustir_safety_env() -> Result<Environment, String> {
    // Trust (perf): fixed VC-independent prelude (trustir_env + per-width overflow
    // lemmas), previously rebuilt per VC. Memoize once (OnceLock) + Arc-backed
    // clone — the proven `certification_env` pattern; soundness unchanged.
    static MEMO: std::sync::OnceLock<Result<Environment, String>> = std::sync::OnceLock::new();
    MEMO.get_or_init(trustir_safety_env_uncached).clone()
}

fn trustir_safety_env_uncached() -> Result<Environment, String> {
    let mut env = trustir_env()?;
    for w in IrUWidth::ALL {
        // Kind 1 — unsigned-add OVERFLOW: `Int.lt (2^W−1) (Int.add a b)`.
        register_int2_prop(&mut env, &uadd_overflows_ir_name(w), |a, b| {
            let sum = Expr::apps(cst("Int.add"), [a.clone(), b.clone()]);
            Expr::apps(cst("Int.lt"), [int_lit(w.max_value()), sum])
        })?;
        // Kind 7 — unsigned-sub UNDERFLOW: `Int.lt (Int.sub a b) 0`.
        register_int2_prop(&mut env, &usub_underflows_ir_name(w), |a, b| {
            let diff = Expr::apps(cst("Int.sub"), [a.clone(), b.clone()]);
            Expr::apps(cst("Int.lt"), [diff, int_lit(0)])
        })?;
    }
    // Kind 4 — SIGNED add/sub/mul overflow (the full out-of-range disjunction).
    for op in IrSignedOp::ALL {
        for w in IrSWidth::ALL {
            register_int2_prop(&mut env, &signed_overflows_ir_name(op, w), |a, b| {
                signed_out_of_range_body(op, a, b, w)
            })?;
        }
    }
    // Kind 5 — NEGATION overflow (per modeled signed width).
    for w in IrSWidth::ALL {
        register_int1_prop(&mut env, &neg_overflows_ir_name(w), |x| {
            eq_int_lit_body(x, w.min_value())
        })?;
    }
    // Kind 6 — SHIFT-amount OOB (per shifted-value width / amount signedness).
    // The shift widths INCLUDE 128 (`IrShiftWidth`, not `IrSWidth`): the threshold
    // is the width literal itself, which stays a closed `Int.ofNat` at 128.
    for w in IrShiftWidth::ALL {
        register_int1_prop(&mut env, &shift_amount_oob_ir_name(w, false), |n| {
            shift_oob_body(n, w, false)
        })?;
        register_int1_prop(&mut env, &shift_amount_oob_ir_name(w, true), |n| {
            shift_oob_body(n, w, true)
        })?;
    }
    // Kind 2 — BOUNDS: `idxOob len i := Int.le len i`.
    register_int2_prop(&mut env, TRUSTIR_IDX_OOB, |len, i| {
        Expr::apps(cst("Int.le"), [len.clone(), i.clone()])
    })?;
    // Kinds 3 + 8 — DIV / REM by zero: `b = 0`.
    register_int1_prop(&mut env, TRUSTIR_DIV_BY_ZERO, |b| eq_int_lit_body(b, 0))?;
    register_int1_prop(&mut env, TRUSTIR_REM_BY_ZERO, |b| eq_int_lit_body(b, 0))?;
    Ok(env)
}

/// Pin the trust-ir SAFETY anchor and audit its axiom closure: EVERY registered
/// safety-spec definition (all 8 kinds, all widths/ops/signedness) must rest on
/// `⊆ {propext, Quot.sound, Classical.choice}` — the kernel's own `axiom_deps`,
/// EMPTY residue per registration. The trust-ir analogue of
/// `mirsem::pin_overflow_anchor` + its per-kind siblings, in one audit.
#[must_use]
pub fn pin_trustir_safety_anchor() -> AnchorVerdict {
    let env = match trustir_safety_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    let mut names: Vec<String> = Vec::new();
    for w in IrUWidth::ALL {
        names.push(uadd_overflows_ir_name(w));
        names.push(usub_underflows_ir_name(w));
    }
    for op in IrSignedOp::ALL {
        for w in IrSWidth::ALL {
            names.push(signed_overflows_ir_name(op, w));
        }
    }
    for w in IrSWidth::ALL {
        names.push(neg_overflows_ir_name(w));
    }
    for w in IrShiftWidth::ALL {
        names.push(shift_amount_oob_ir_name(w, false));
        names.push(shift_amount_oob_ir_name(w, true));
    }
    names.push(TRUSTIR_IDX_OOB.to_string());
    names.push(TRUSTIR_DIV_BY_ZERO.to_string());
    names.push(TRUSTIR_REM_BY_ZERO.to_string());
    for n in &names {
        match env.axiom_deps(&Name::from_string(n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut rs: Vec<String> = residue.iter().map(ToString::to_string).collect();
                rs.sort();
                return AnchorVerdict::Residue(rs);
            }
            None => return AnchorVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    AnchorVerdict::Modulo3
}

// ---------------------------------------------------------------------------
// FORMULA-AWARE bridge machinery (mirrors mirsem's exactly; the LIVE grounder's
// output is what gets kernel-certified, never a hand-built shape).
// ---------------------------------------------------------------------------

/// Build the de-Bruijn grounding map for a list of operand variable names, assigning
/// `names[0] = bvar(n−1)`, …, `names[n−1] = bvar(0)` — the convention `ground_prop`
/// expects (a leading binder is the OUTERMOST, highest index).
fn debruijn_params(names: &[&str]) -> HashMap<String, Expr> {
    let n = names.len();
    let mut m = HashMap::new();
    for (i, name) in names.iter().enumerate() {
        m.insert((*name).to_string(), Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    }
    m
}

/// The variable name of an integer `Formula::Var` leaf (the only operand shape the
/// formula-aware grounder maps to a de-Bruijn binder). Anything else ⇒ `None`
/// (outside the fragment; the caller fails closed).
fn formula_var_name(f: &trust_types::Formula) -> Option<&str> {
    match f {
        trust_types::Formula::Var(n, _) => Some(n.as_str()),
        _ => None,
    }
}

/// Search a VC `Formula` tree for the FIRST leaf matching `pred`, descending through
/// `And`/`Or`/`Not`/`Implies` (the connective structure block-defs + range bounds +
/// the violation disjunction are built from).
fn find_violation_leaf<'a>(
    f: &'a trust_types::Formula,
    pred: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    if pred(f) {
        return Some(f);
    }
    match f {
        F::And(v) | F::Or(v) => v.iter().find_map(|x| find_violation_leaf(x, pred)),
        F::Not(a) => find_violation_leaf(a, pred),
        F::Implies(a, b) => find_violation_leaf(a, pred).or_else(|| find_violation_leaf(b, pred)),
        _ => None,
    }
}

/// Like [`find_violation_leaf`] but ALSO descends into the children of an `Eq` whose
/// predicate does not itself match — reaching a violation core buried inside a
/// GUARD-BINDING equality `Eq(Var aux, <core>)` (the precondition-guarded `abs`
/// negation case). Used ONLY by the NEGATION certifier; its predicate (`Eq(Var, Int)`)
/// cannot match a guard-binding `Eq` (whose RHS is a comparison, not an `Int`), so
/// the deeper descent never produces a false core.
fn find_violation_leaf_through_eq<'a>(
    f: &'a trust_types::Formula,
    pred: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    if pred(f) {
        return Some(f);
    }
    match f {
        F::And(v) | F::Or(v) => v.iter().find_map(|x| find_violation_leaf_through_eq(x, pred)),
        F::Not(a) => find_violation_leaf_through_eq(a, pred),
        F::Implies(a, b) => find_violation_leaf_through_eq(a, pred)
            .or_else(|| find_violation_leaf_through_eq(b, pred)),
        F::Eq(a, b) => find_violation_leaf_through_eq(a, pred)
            .or_else(|| find_violation_leaf_through_eq(b, pred)),
        _ => None,
    }
}

/// Whether an integer operand `Formula` is in the formula-aware fragment — a bare
/// `Var` (mapped to a de-Bruijn binder) OR an integer CONSTANT (`Int`/`UInt`,
/// grounded to a closed literal, no binder). A nested arithmetic / field / pointer
/// operand is OUTSIDE the fragment ⇒ the caller fails closed.
fn operand_in_fragment(t: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    matches!(t, F::Var(_, _) | F::Int(_) | F::UInt(_))
}

/// The two operand `Formula`s of a computed binary sub-term `Add(a,b)` / `Sub(a,b)` /
/// `Mul(a,b)` — the OVERFLOW-family violation cores carry the operands inside this
/// computed result. `Mul` covers the LIA constant-multiplier signed mul; a `var*var`
/// mul is a BV formula with no such leaf, so it never spuriously matches.
fn binop_operands(
    t: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula)> {
    use trust_types::Formula as F;
    match t {
        F::Add(a, b) | F::Sub(a, b) | F::Mul(a, b)
            if operand_in_fragment(a) && operand_in_fragment(b) =>
        {
            Some((a, b))
        }
        _ => None,
    }
}

/// The distinct `Var` operand names of a list of operand `Formula`s, in first-
/// appearance order (a constant operand contributes no name).
fn distinct_var_names<'a>(operands: &[&'a trust_types::Formula]) -> Vec<&'a str> {
    let mut names: Vec<&str> = Vec::new();
    for op in operands {
        if let Some(n) = formula_var_name(op) {
            if !names.contains(&n) {
                names.push(n);
            }
        }
    }
    names
}

/// THE BRIDGE CHECK (trust-ir keyed): kernel-check that the LIVE grounding of `core`
/// (via `clean_ground::ground_prop` under `params`) is def-eq, modulo the 3
/// foundational axioms, to the trust-ir spec term `spec` (built over the SAME
/// de-Bruijn refs). Registers `theorem Trust.TrustIr.Safety.bridge :
/// ∀ (x⃗ : Int), @Eq Prop <live-grounded core> <spec> := λ x⃗. Eq.refl Prop <grounded>`
/// into the trust-ir safety env — it type-checks IFF the two `Prop` terms are def-eq
/// — then audits the axiom closure. `ProvenModulo3` ONLY on a genuine kernel def-eq
/// with EMPTY residue; the grounder declining, a shape mismatch, or a non-def-eq
/// spec (wrong threshold / width / relation) is `KernelRejected` (fail-closed).
///
/// The certified LHS **is** the live grounder's output — this is the post-audit
/// "names the LIVE grounder output" property; it is NOT `Eq.refl` of `spec = spec`.
fn live_ground_def_eq_spec_ir(
    core: &trust_types::Formula,
    params: &HashMap<String, Expr>,
    spec: &Expr,
    binder_count: usize,
) -> RefinementVerdict {
    let mut env = match trustir_safety_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let Some(grounded) = crate::clean_ground::ground_prop(core, params) else {
        // The live grounder declined this core ⇒ no cert (fail closed).
        return RefinementVerdict::KernelRejected(
            "the live grounder (clean_ground::ground_prop) declined the violation core".to_string(),
        );
    };
    let bd = || BinderData::from(BinderInfo::Default);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut statement = Expr::apps(eq, [Expr::prop(), grounded.clone(), spec.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut proof = Expr::apps(eq_refl, [Expr::prop(), grounded]);
    for _ in 0..binder_count {
        statement = Expr::pi(bd(), int_ty(), statement);
        proof = Expr::lam(bd(), int_ty(), proof);
    }
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            // NOT def-eq ⇒ the emitted core is not the spec ⇒ fail closed.
            return RefinementVerdict::KernelRejected(format!(
                "safety-VC adequacy check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Safety.bridge");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add safety-VC adequacy: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "safety-VC adequacy decl not found after add".to_string(),
        ),
    }
}

/// FORMULA-AWARE bridge for an OVERFLOW-family core whose operands appear inside a
/// COMPUTED `Add`/`Sub`/`Mul` sub-term. Grounds each operand POSITION through the
/// SAME live `ground_int` (a `Var` → its de-Bruijn binder; an integer CONSTANT →
/// its closed literal, NO binder) and applies `spec_of` to those grounded operand
/// terms, so the spec is built over the exact terms the grounder produces (handling
/// repeated operands `x + x` AND mixed const operands `x + 1` uniformly).
fn overflow_family_live_def_eq_ir(
    core: &trust_types::Formula,
    operands: &[&trust_types::Formula],
    spec_of: &dyn Fn(&[Expr]) -> Expr,
) -> RefinementVerdict {
    let distinct = distinct_var_names(operands);
    let params = debruijn_params(&distinct);
    let mut grounded_ops: Vec<Expr> = Vec::with_capacity(operands.len());
    for op in operands {
        match crate::clean_ground::ground_int(op, &params) {
            Some(e) => grounded_ops.push(e),
            None => {
                // The live grounder declined this operand ⇒ fail closed.
                return RefinementVerdict::KernelRejected(
                    "the live grounder (clean_ground::ground_int) declined an operand".to_string(),
                );
            }
        }
    }
    let spec = spec_of(&grounded_ops);
    live_ground_def_eq_spec_ir(core, &params, &spec, distinct.len())
}

// ---------------------------------------------------------------------------
// Width recovery FROM THE EMITTED FORMULA (never from operand_ty — the audit fix).
// ---------------------------------------------------------------------------

/// Map an unsigned-overflow MAX threshold literal `2^W − 1` (read from the emitted
/// `Gt(a+b, Int(MAX))` disjunct) to its bit width. `None` (fail closed) for a
/// threshold that is not exactly some modeled `2^W − 1`.
fn uwidth_of_unsigned_max(max: i128) -> Option<IrUWidth> {
    IrUWidth::ALL.into_iter().find(|w| w.max_value() == max)
}

/// Map a signed out-of-range `(MIN, MAX)` threshold pair (read from the emitted
/// `Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])`) to its modeled width — requiring BOTH bounds
/// to agree on the SAME `W` (a mismatched pair fails closed).
fn swidth_of_signed_bounds(min: i128, max: i128) -> Option<IrSWidth> {
    IrSWidth::ALL.into_iter().find(|w| w.min_value() == min && w.max_value() == max)
}

/// Map a negation-overflow MIN threshold literal `−2^(W−1)` (read from the emitted
/// `Eq(x, Int(MIN))` core) to its modeled width. `None` (fail closed) otherwise.
fn swidth_of_signed_min(min: i128) -> Option<IrSWidth> {
    IrSWidth::ALL.into_iter().find(|w| w.min_value() == min)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-SUB case of a modeled width
/// (`op == Sub`, both operands unsigned at the same `u8..u64` width), return that
/// width. The underflow threshold (`0`) carries no width in the formula, so — as in
/// the MirSem Lemma-8 tier — the width names the tally bucket only (the spec body is
/// width-invariant and the def-eq holds at every modeled width).
fn usub_underflow_vc_width(kind: &trust_types::VcKind) -> Option<IrUWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    let wa = IrUWidth::from_mir(*wa, *sa)?;
    let wb = IrUWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

// ---------------------------------------------------------------------------
// The per-VC formula-aware adequacy (the trust-ir relocation of
// `mirsem::safety_vc_is_faithful_formula_aware`).
// ---------------------------------------------------------------------------

/// The modeled safety-VC kind a trust-ir adequacy certificate is keyed by — the
/// trust-ir analogue of `mirsem::SafetyVcKind`, carried for diagnostics/tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrSafetyVcKind {
    /// Unsigned-add overflow at the given width (kind 1).
    UAddOverflow(IrUWidth),
    /// Unsigned-sub underflow at the given width (kind 7).
    USubUnderflow(IrUWidth),
    /// Signed add/sub/mul overflow at the given op + width (kind 4).
    SignedOverflow(IrSignedOp, IrSWidth),
    /// Signed negation overflow at the given width (kind 5).
    NegOverflow(IrSWidth),
    /// Shift-amount OOB at the given value width + amount signedness (kind 6).
    /// Keyed by [`IrShiftWidth`] — the one lane whose modeled widths include 128.
    ShiftOob(IrShiftWidth, bool),
    /// Array/slice index out of bounds (kind 2).
    Bounds,
    /// Division by zero (kind 3).
    DivByZero,
    /// Remainder by zero (kind 8).
    RemByZero,
}

/// Whether a `VcKind` is a SAFETY obligation (a runtime-UB / panic check) — kept in
/// LOCKSTEP with `mirsem::is_safety_vc_kind` (asserted by test): the function-level
/// gate must select the SAME safety subset on both tiers.
fn is_safety_vc_kind(kind: &trust_types::VcKind) -> bool {
    use trust_types::VcKind as K;
    matches!(
        kind,
        K::ArithmeticOverflow { .. }
            | K::ShiftOverflow { .. }
            | K::DivisionByZero
            | K::RemainderByZero
            | K::IndexOutOfBounds
            | K::SliceBoundsCheck
            | K::CastOverflow { .. }
            | K::NegationOverflow { .. }
            | K::FloatDivisionByZero
    )
}

/// FORMULA-AWARE adequacy for ONE safety VC, keyed to the TRUST-IR specs, with the
/// classified kind on success: ground the ACTUAL emitted violation core through the
/// LIVE `clean_ground::ground_prop` and kernel-check it def-eq (modulo 3) to the
/// `Trust.TrustIr.*` machine-semantics predicate for THAT kind — recovering the
/// width/threshold FROM THE EMITTED FORMULA (never `operand_ty`). Fail-closed on
/// every edge: an unmodeled kind/width, a core outside the formula-aware fragment
/// (the `var*var` BV mul), or an emitted threshold matching no modeled spec is
/// `KernelRejected`, never silently passed.
fn trustir_safety_vc_adequate_kind(
    vc: &trust_types::VerificationCondition,
) -> (Option<IrSafetyVcKind>, RefinementVerdict) {
    use trust_types::{Formula as F, VcKind as K};
    let declined = |msg: &str| (None, RefinementVerdict::KernelRejected(msg.to_string()));
    match &vc.kind {
        // BOUNDS (kind 2): the emitted core is `Ge(i, len)`; the index is a variable,
        // the length a variable (slice) or constant (fixed array). Live-ground the
        // WHOLE core → `Int.le (g len) (g i)`; spec `idxOob (g len) i` over the SAME
        // grounded length term + index bvar.
        K::IndexOutOfBounds | K::SliceBoundsCheck => {
            let Some(leaf) = find_violation_leaf(&vc.formula, &|f| {
                matches!(f, F::Ge(a, b)
                    if formula_var_name(a).is_some()
                        && (formula_var_name(b).is_some() || matches!(&**b, F::Int(_))))
            }) else {
                return declined("bounds VC: no `Ge(index, len)` violation core found");
            };
            let F::Ge(i_f, len_f) = leaf else { unreachable!("guarded by the finder") };
            let Some(i_name) = formula_var_name(i_f) else {
                return declined("bounds VC: index operand is not a Var");
            };
            // Bind the index at bvar 0; a length VARIABLE (if any) at bvar 1.
            let (params, binder_count, len_expr) = match formula_var_name(len_f) {
                Some(len_name) => {
                    let mut m = HashMap::new();
                    m.insert(len_name.to_string(), Expr::bvar(1));
                    m.insert(i_name.to_string(), Expr::bvar(0));
                    (m, 2usize, Expr::bvar(1))
                }
                None => {
                    let F::Int(n) = &**len_f else {
                        return declined("bounds VC: length operand is neither Var nor Int");
                    };
                    let mut m = HashMap::new();
                    m.insert(i_name.to_string(), Expr::bvar(0));
                    (m, 1usize, int_lit(*n))
                }
            };
            let spec = Expr::apps(cst(TRUSTIR_IDX_OOB), [len_expr, Expr::bvar(0)]);
            (
                Some(IrSafetyVcKind::Bounds),
                live_ground_def_eq_spec_ir(leaf, &params, &spec, binder_count),
            )
        }
        // DIV / REM by zero (kinds 3/8): the emitted core is `Eq(b, 0)`. Live-ground
        // → `@Eq Int b (Int.ofNat 0)`; spec `divByZero b` / `remByZero b`.
        K::DivisionByZero | K::RemainderByZero => {
            let Some(leaf) = find_violation_leaf(&vc.formula, &|f| {
                matches!(f, F::Eq(a, b)
                    if formula_var_name(a).is_some() && matches!(&**b, F::Int(0)))
            }) else {
                return declined("div/rem VC: no `Eq(divisor, 0)` violation core found");
            };
            let F::Eq(b_f, _) = leaf else { unreachable!("guarded by the finder") };
            let Some(b_name) = formula_var_name(b_f) else {
                return declined("div/rem VC: divisor operand is not a Var");
            };
            let params = debruijn_params(&[b_name]);
            let (spec_name, kind) = if matches!(vc.kind, K::DivisionByZero) {
                (TRUSTIR_DIV_BY_ZERO, IrSafetyVcKind::DivByZero)
            } else {
                (TRUSTIR_REM_BY_ZERO, IrSafetyVcKind::RemByZero)
            };
            let spec = Expr::app(cst(spec_name), Expr::bvar(0));
            (Some(kind), live_ground_def_eq_spec_ir(leaf, &params, &spec, 1))
        }
        // SHIFT-amount OOB (kind 6): the emitted core is `Ge(n, Int(W))` — W is the
        // EMITTED threshold, read from the formula (NOT operand_ty, which fabricates
        // i64 for a const shifted value). A signed amount adds the `Lt(n,0)` disjunct.
        K::ShiftOverflow { shift_ty, .. } => {
            let amount_signed = matches!(shift_ty, trust_types::Ty::Int { signed: true, .. });
            // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR relocation — the amount operand may
            // be a VARIABLE (the original shape) OR a CLOSED LITERAL (`x >> 44`'s
            // emitted `Ge(Int(44), Int(64))`, the `ExprMeta::loose_bvar_range`-class
            // constant shift). Mirrors `mirsem.rs`'s Lemma-7 closed-literal arm
            // byte-for-byte, ported onto the trust-ir spec names.
            let Some(ge) = find_violation_leaf(&vc.formula, &|f| {
                matches!(f, F::Ge(a, b)
                    if (formula_var_name(a).is_some() || matches!(&**a, F::Int(_)))
                        && matches!(&**b, F::Int(_)))
            }) else {
                return declined("shift VC: no `Ge(amount, W)` threshold disjunct found");
            };
            let F::Ge(n_f, w_f) = ge else { unreachable!("guarded by the finder") };
            let F::Int(threshold) = &**w_f else { unreachable!("guarded by the finder") };
            // The EMITTED threshold W must be a modeled shift-width literal
            // (`8/16/32/64/128` — the 128-bit value widths ARE in this lane's set).
            let Some(w) = u32::try_from(*threshold).ok().and_then(IrShiftWidth::from_bits) else {
                return declined("shift VC: emitted threshold is not a modeled width");
            };
            // Trust: M6 rung 6 — the CLOSED-LITERAL amount arm (unsigned only, exactly
            // mirroring the mirsem-side gate: a literal SIGNED amount has no observed
            // real-MIR `Or` core at a literal, so it stays declined rather than guessed).
            if let F::Int(k) = &**n_f {
                if amount_signed {
                    return declined("shift VC: literal-amount signed shift — outside the arm");
                }
                let spec = Expr::app(cst(&shift_amount_oob_ir_name(w, amount_signed)), int_lit(*k));
                return (
                    Some(IrSafetyVcKind::ShiftOob(w, amount_signed)),
                    live_ground_def_eq_spec_ir(ge, &HashMap::new(), &spec, 0),
                );
            }
            let Some(n_name) = formula_var_name(n_f) else {
                return declined("shift VC: amount operand is not a Var");
            };
            let params = debruijn_params(&[n_name]);
            // The core to ground is the unsigned `Ge(n,W)` or the full signed `Or`.
            let core: &F = if amount_signed {
                let Some(or) = find_violation_leaf(&vc.formula, &|f| match f {
                    F::Or(v) => {
                        v.iter().any(|x| {
                            matches!(x, F::Lt(a, b)
                        if formula_var_name(a) == Some(n_name) && matches!(&**b, F::Int(0)))
                        }) && v.iter().any(|x| {
                            matches!(x, F::Ge(a, b)
                        if formula_var_name(a) == Some(n_name)
                            && matches!(&**b, F::Int(t) if *t == *threshold))
                        })
                    }
                    _ => false,
                }) else {
                    return declined("shift VC: signed amount without the `Or([n<0, n≥W])` core");
                };
                or
            } else {
                ge
            };
            let spec = Expr::app(cst(&shift_amount_oob_ir_name(w, amount_signed)), Expr::bvar(0));
            (
                Some(IrSafetyVcKind::ShiftOob(w, amount_signed)),
                live_ground_def_eq_spec_ir(core, &params, &spec, 1),
            )
        }
        // ARITHMETIC OVERFLOW / UNDERFLOW (kinds 1/4/7): the violation core carries a
        // COMPUTED `Add`/`Sub`/`Mul` sub-term. Operand signedness only SELECTS which
        // shape to look for; the threshold (hence the certified width) is read FROM
        // THE FORMULA.
        K::ArithmeticOverflow { op, operand_tys: (a_ty, b_ty) } => {
            use trust_types::{BinOp, Ty};
            let (Ty::Int { signed: sa, .. }, Ty::Int { signed: sb, .. }) = (a_ty, b_ty) else {
                return declined("overflow VC: non-integer operand types");
            };
            match op {
                // UNSIGNED-ADD OVERFLOW (kind 1): the load-bearing disjunct is
                // `Gt(Add(a,b), Int(MAX))`, MAX = 2^W−1 read from the formula.
                BinOp::Add if !sa && !sb => {
                    let Some(leaf) = find_violation_leaf(&vc.formula, &|f| match f {
                        F::Gt(lhs, rhs) => {
                            binop_operands(lhs).is_some() && matches!(&**rhs, F::Int(_))
                        }
                        _ => false,
                    }) else {
                        return declined("uadd VC: no `Gt(a+b, MAX)` overflow disjunct found");
                    };
                    let F::Gt(add_t, max_f) = leaf else { unreachable!("guarded by the finder") };
                    let Some((a_op, b_op)) = binop_operands(add_t) else {
                        return declined("uadd VC: operands outside the formula-aware fragment");
                    };
                    let F::Int(max) = &**max_f else { unreachable!("guarded by the finder") };
                    let Some(w) = uwidth_of_unsigned_max(*max) else {
                        return declined("uadd VC: emitted threshold is not a modeled 2^W−1");
                    };
                    let name = uadd_overflows_ir_name(w);
                    (
                        Some(IrSafetyVcKind::UAddOverflow(w)),
                        overflow_family_live_def_eq_ir(leaf, &[a_op, b_op], &|ops| {
                            Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                        }),
                    )
                }
                // SIGNED ADD/SUB/MUL OVERFLOW (kind 4): the full out-of-range
                // `Or([Lt(a∘b, MIN), Gt(a∘b, MAX)])`, MIN+MAX read from the formula
                // (and required to agree on the SAME width). MUL matches only the LIA
                // constant-multiplier emission; a `var*var` BV mul has no such leaf ⇒
                // declines (fail-closed, the honest deferred gap).
                BinOp::Add | BinOp::Sub | BinOp::Mul if *sa && *sb => {
                    let sop = match op {
                        BinOp::Add => IrSignedOp::Add,
                        BinOp::Sub => IrSignedOp::Sub,
                        _ => IrSignedOp::Mul,
                    };
                    let Some(or) = find_violation_leaf(&vc.formula, &|f| match f {
                        F::Or(v) if v.len() == 2 => {
                            let lt_min = matches!(&v[0], F::Lt(l, r)
                                if binop_operands(l).is_some() && matches!(&**r, F::Int(_)));
                            let gt_max = matches!(&v[1], F::Gt(l, r)
                                if binop_operands(l).is_some() && matches!(&**r, F::Int(_)));
                            lt_min && gt_max
                        }
                        _ => false,
                    }) else {
                        return declined(
                            "signed overflow VC: no `Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])` core \
                             (a var*var BV mul stays honestly deferred)",
                        );
                    };
                    let F::Or(v) = or else { unreachable!("guarded by the finder") };
                    let (F::Lt(under_t, min_f), F::Gt(over_t, max_f)) = (&v[0], &v[1]) else {
                        unreachable!("guarded by the finder")
                    };
                    // Both disjuncts must reference the SAME computed `a∘b` operands.
                    let Some((a_op, b_op)) = binop_operands(under_t) else {
                        return declined("signed overflow VC: operands outside the fragment");
                    };
                    if binop_operands(over_t) != Some((a_op, b_op)) {
                        return declined("signed overflow VC: disjunct operand mismatch");
                    }
                    let (F::Int(min), F::Int(max)) = (&**min_f, &**max_f) else {
                        unreachable!("guarded by the finder")
                    };
                    let Some(w) = swidth_of_signed_bounds(*min, *max) else {
                        return declined(
                            "signed overflow VC: emitted (MIN,MAX) match no modeled width",
                        );
                    };
                    let name = signed_overflows_ir_name(sop, w);
                    (
                        Some(IrSafetyVcKind::SignedOverflow(sop, w)),
                        overflow_family_live_def_eq_ir(or, &[a_op, b_op], &|ops| {
                            Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                        }),
                    )
                }
                // UNSIGNED-SUB UNDERFLOW (kind 7): the single core `Lt(Sub(a,b), 0)`.
                // The `0` threshold carries no width; the operand width names the
                // tally bucket only (the spec body is width-invariant).
                BinOp::Sub if !sa && !sb => {
                    let Some(w) = usub_underflow_vc_width(&vc.kind) else {
                        return declined("usub VC: operand widths unmodeled or mismatched");
                    };
                    let Some(leaf) = find_violation_leaf(&vc.formula, &|f| match f {
                        F::Lt(lhs, rhs) => {
                            matches!(&**lhs, F::Sub(_, _))
                                && binop_operands(lhs).is_some()
                                && matches!(&**rhs, F::Int(0))
                        }
                        _ => false,
                    }) else {
                        return declined("usub VC: no `Lt(a−b, 0)` underflow disjunct found");
                    };
                    let F::Lt(sub_t, _) = leaf else { unreachable!("guarded by the finder") };
                    let Some((a_op, b_op)) = binop_operands(sub_t) else {
                        return declined("usub VC: operands outside the formula-aware fragment");
                    };
                    let name = usub_underflows_ir_name(w);
                    (
                        Some(IrSafetyVcKind::USubUnderflow(w)),
                        overflow_family_live_def_eq_ir(leaf, &[a_op, b_op], &|ops| {
                            Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                        }),
                    )
                }
                _ => declined("overflow VC: op/signedness combination is not modeled"),
            }
        }
        // NEGATION OVERFLOW (kind 5): the core `Eq(x, Int(MIN))`, MIN read from the
        // formula. Uses the `Eq`-descending finder so a precondition-guarded `abs`
        // (core buried as the RHS of an SSA guard-binding `Eq`) is reached.
        K::NegationOverflow { .. } => {
            let Some(leaf) = find_violation_leaf_through_eq(&vc.formula, &|f| match f {
                F::Eq(lhs, rhs) => formula_var_name(lhs).is_some() && matches!(&**rhs, F::Int(_)),
                _ => false,
            }) else {
                return declined("negation VC: no `Eq(x, MIN)` violation core found");
            };
            let F::Eq(x_f, min_f) = leaf else { unreachable!("guarded by the finder") };
            if formula_var_name(x_f).is_none() {
                return declined("negation VC: negated operand is not a Var");
            }
            let F::Int(min) = &**min_f else { unreachable!("guarded by the finder") };
            let Some(w) = swidth_of_signed_min(*min) else {
                return declined("negation VC: emitted threshold is not a modeled −2^(W−1)");
            };
            let name = neg_overflows_ir_name(w);
            (
                Some(IrSafetyVcKind::NegOverflow(w)),
                overflow_family_live_def_eq_ir(leaf, &[x_f], &|ops| {
                    Expr::app(cst(&name), ops[0].clone())
                }),
            )
        }
        // Every other kind — CastOverflow, FloatDivisionByZero, and every non-safety
        // kind — is UNMODELED here ⇒ fail closed (never silently passed).
        other => (
            None,
            RefinementVerdict::KernelRejected(format!(
                "safety-VC kind not modeled by the trust-ir safety tier: {other:?}"
            )),
        ),
    }
}

/// FORMULA-AWARE adequacy for ONE safety VC on the TRUST-IR specs — the trust-ir
/// relocation of `mirsem::safety_vc_is_faithful_formula_aware`. `ProvenModulo3` IFF
/// the ACTUAL `vc.formula`'s violation core, grounded through the LIVE
/// `clean_ground::ground_prop`, is kernel-proven def-eq to the pinned
/// `Trust.TrustIr.*` machine-semantics predicate for the VC's kind (width/threshold
/// recovered from the EMITTED formula), with EMPTY axiom residue. Anything else —
/// unmodeled kind/width/shape, grounder decline, non-def-eq spec — is
/// `KernelRejected`/`Residue` (fail-closed).
#[must_use]
pub fn trustir_safety_vc_adequate(vc: &trust_types::VerificationCondition) -> RefinementVerdict {
    trustir_safety_vc_adequate_kind(vc).1
}

// ---------------------------------------------------------------------------
// The function-level gate (the trust-ir relocation of the MirSem
// `function_fully_faithful_witness` clause (b) consumption of
// `function_safety_vcs_faithful`).
// ---------------------------------------------------------------------------

/// Whether EVERY safety VC this function's REAL emitter run
/// (`trust_vcgen::generate_vcs`) raises is kernel-certified ADEQUATE on the
/// trust-ir specs — the via-trustir SAFETY-VC KERNEL-ADEQUACY pillar (Lane S).
///
/// Semantics mirror the MirSem composition (`function_fully_faithful_witness`
/// clause (b) over `function_safety_vcs_faithful`) EXACTLY:
///   * an UNMODELED safety VC (kind, width, or formula shape) ⇒ `false` — even one
///     means the reflection is not end-to-end kernel-proven (fail-closed);
///   * every MODELED safety VC must certify `ProvenModulo3` through the LIVE-
///     grounder def-eq bridge ⇒ else `false`;
///   * a function that emits NO safety VC at all is VACUOUSLY faithful (`true`) —
///     nothing unsafe to capture (the same vacuously-safe edge the MirSem witness
///     admits with `safety = None`).
///
/// Non-safety VCs (postconditions, contracts, temporal, …) are not this gate's
/// concern and are skipped, exactly as in the MirSem tier.
#[must_use]
pub fn function_safety_vcs_faithful_via_trustir(func: &trust_types::VerifiableFunction) -> bool {
    // Drive the REAL emitter so the gate is over the VCs that ACTUALLY get raised
    // (the same empirical grounding the MirSem tier rests on).
    let vcs = trust_vcgen::generate_vcs(func);
    vcs.iter()
        .filter(|vc| is_safety_vc_kind(&vc.kind))
        .all(|vc| matches!(trustir_safety_vc_adequate(vc), RefinementVerdict::ProvenModulo3))
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, Statement,
        Terminator, Ty, UnOp, VcKind, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    // ---- function synthesizers (mirroring mirsem's own per-kind test bodies:
    // `Rvalue::BinaryOp` is the UNCHECKED form that empirically raises the
    // implicit safety VC through `trust_vcgen::generate_vcs`) ----

    fn int_ty_of(width: u32, signed: bool) -> Ty {
        Ty::Int { width, signed }
    }

    /// `fn f(a: T, b: T) -> T { a OP b }` — the canonical 2-operand binop body.
    fn binop_func(op: BinOp, width: u32, signed: bool) -> VerifiableFunction {
        let t = || int_ty_of(width, signed);
        VerifiableFunction {
            name: "f".into(),
            def_path: "crate::f".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: t(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: t(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: t(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: t(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn neg(x: iW) -> iW { -x }` — raises `NegationOverflow{ty: iW}` (core `Eq(x, MIN)`).
    fn neg_func(width: u32) -> VerifiableFunction {
        let i = || int_ty_of(width, true);
        VerifiableFunction {
            name: "neg".into(),
            def_path: "crate::neg".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: i(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: i(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: i(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn shf(x: u32, n: aW) -> u32 { x << n }` — raises `ShiftOverflow` (core `Ge(n, 32)`).
    fn shift_func(amount_signed: bool) -> VerifiableFunction {
        shift_func_of(32, false, amount_signed)
    }

    /// `fn shf(x: <W,signed>, n: a32) -> _ { x << n }` — the width-parametrized
    /// shift fixture (core `Ge(n, W)`, plus the `Lt(n,0)` disjunct when signed).
    fn shift_func_of(
        value_width: u32,
        value_signed: bool,
        amount_signed: bool,
    ) -> VerifiableFunction {
        let val = || int_ty_of(value_width, value_signed);
        let amt = int_ty_of(32, amount_signed);
        VerifiableFunction {
            name: "shf".into(),
            def_path: "crate::shf".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: val(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: val(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: amt, name: Some("n".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Shl,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: val(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Trust: M6 rung 6, SHR→TRUST-IR ANCHOR relocation — `fn f(x: u64) -> u32 {
    /// (x >> k) as u32 }` for a CLOSED-LITERAL shift amount `k` — the REAL
    /// `ExprMeta::loose_bvar_range` shape (self's field read collapses to a bare
    /// param read here; the leaf under test is the Shr+Cast pair, mirroring
    /// `mirsem`'s own `literal_shift_in_range_...` synthesizer).
    fn shift_func_literal(k: u128) -> VerifiableFunction {
        let u64t = || int_ty_of(64, false);
        let u32t = || int_ty_of(32, false);
        VerifiableFunction {
            name: "range".into(),
            def_path: "crate::range".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: u32t(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: u64t(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: u64t(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Shr,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(trust_types::ConstValue::Uint(k, 32)),
                            ),
                            span: Default::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Cast(Operand::Move(Place::local(2)), u32t()),
                            span: Default::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: u32t(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Trust: M6 rung 6, SHR→TRUST-IR ANCHOR relocation — the CLOSED-LITERAL
    /// shift-amount adequacy arm, both sides of the fail-closed boundary:
    ///   * IN-RANGE (`x >> 44`, u64): the ShiftOverflow VC's literal core
    ///     `Ge(Int(44), Int(64))` is kernel-certified ADEQUATE on the trust-ir
    ///     lane too (mirrors mirsem's `literal_shift_in_range_...` pin, ported);
    ///   * a SIGNED literal amount stays DECLINED (no observed real-MIR `Or`
    ///     core at a literal — the same honest scope mirsem's arm carries).
    #[test]
    fn kind6_shift_literal_amount_adequate_modulo_3_unsigned_signed_declines() {
        let func_u = shift_func_literal(44);
        let (kind_u, verdict_u) =
            adequacy_of_first(&func_u, |k| matches!(k, VcKind::ShiftOverflow { .. }));
        assert_eq!(verdict_u, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind_u, Some(IrSafetyVcKind::ShiftOob(IrShiftWidth::W64, false)));
        assert!(function_safety_vcs_faithful_via_trustir(&func_u));

        // A signed literal amount: build the same shape with a SIGNED shift type
        // (mirsem's `amount_signed` guard) — declines (fail-closed, no false cert).
        let mut func_s = shift_func_literal(44);
        if let Ty::Int { signed, .. } = &mut func_s.body.locals[2].ty {
            *signed = true;
        }
        // The VC's own `shift_ty` is derived from the emitter's own typing, not
        // this test's override — the adequacy arm's `amount_signed` gate is
        // exercised directly instead, matching the mirsem-side control's scope.
        let vcs = trust_vcgen::generate_vcs(&func_u);
        if let Some(vc) = vcs.iter().find(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. })) {
            let mut signed_vc = vc.clone();
            if let VcKind::ShiftOverflow { shift_ty, .. } = &mut signed_vc.kind {
                *shift_ty = Ty::Int { width: 32, signed: true };
            }
            let (_, verdict_s) = trustir_safety_vc_adequate_kind(&signed_vc);
            assert!(
                matches!(verdict_s, RefinementVerdict::KernelRejected(_)),
                "a literal-amount SIGNED shift must stay declined, got {verdict_s:?}"
            );
        }
    }

    /// `fn f(x: u128) -> u128 { x >> k }` for a CLOSED-LITERAL amount `k` — the
    /// 128-bit-value twin of [`shift_func_literal`] (no narrowing cast needed;
    /// the emitted core is `Ge(Int(k), Int(128))`).
    fn shift_func_literal_128(k: u128) -> VerifiableFunction {
        let u128t = || int_ty_of(128, false);
        VerifiableFunction {
            name: "shr128".into(),
            def_path: "crate::shr128".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: u128t(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: u128t(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Shr,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(trust_types::ConstValue::Uint(k, 32)),
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: u128t(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn idxf(arr: [i32; 8], i: usize) -> i32 { arr[i] }` — raises
    /// `IndexOutOfBounds` with the exact formula `Ge(Var i, Int 8)`.
    fn idx_array_func() -> VerifiableFunction {
        let i = || int_ty_of(32, true);
        let arr_ty = Ty::Array { elem: Box::new(i()), len: 8 };
        let usize_ty = int_ty_of(64, false);
        VerifiableFunction {
            name: "idxf".into(),
            def_path: "crate::idxf".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: i(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: arr_ty, name: Some("arr".into()) },
                    LocalDecl { index: 2, ty: usize_ty, name: Some("i".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Index(2)],
                        })),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: i(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// `fn id(x: i32) -> i32 { x }` — emits NO safety VC (the vacuous case).
    fn identity_func() -> VerifiableFunction {
        let i = || int_ty_of(32, true);
        VerifiableFunction {
            name: "id".into(),
            def_path: "crate::id".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: i(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: i(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: i(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Find the FIRST emitted safety VC of the given classifying predicate and
    /// return its trust-ir adequacy `(kind, verdict)`.
    fn adequacy_of_first(
        func: &VerifiableFunction,
        pred: impl Fn(&VcKind) -> bool,
    ) -> (Option<IrSafetyVcKind>, RefinementVerdict) {
        let vcs = trust_vcgen::generate_vcs(func);
        let vc = vcs
            .iter()
            .find(|vc| pred(&vc.kind))
            .expect("the emitter must raise the expected safety VC");
        trustir_safety_vc_adequate_kind(vc)
    }

    // ---- the anchor audit: every registered spec is modulo 3 (empty residue) ----

    #[test]
    fn trustir_safety_anchor_pins_modulo_3() {
        // EVERY Trust.TrustIr.* safety-spec registration (all 8 kinds × widths/ops/
        // signedness) rests on ⊆ {propext, Quot.sound, Classical.choice} — the
        // kernel's own axiom_deps, EMPTY residue. No 4th axiom, no new free constant.
        assert_eq!(pin_trustir_safety_anchor(), AnchorVerdict::Modulo3);
    }

    #[test]
    fn trustir_safety_env_carries_no_mirsem_declaration() {
        // THE SEPARATION PROBE (load-bearing): the trust-ir safety env must carry
        // ZERO Trust.MirSem.* declarations — the tier is keyed to the trust-ir
        // denotation, not the hand-written MirSem model.
        let env = trustir_safety_env().expect("trust-ir safety env builds");
        for n in [
            "Trust.MirSem.uadd_overflows_u32",
            "Trust.MirSem.idx_oob",
            "Trust.MirSem.div_by_zero",
            "Trust.MirSem.rem_by_zero",
            "Trust.MirSem.sadd_overflows_i32",
            "Trust.MirSem.neg_overflows_i32",
            "Trust.MirSem.shift_amount_oob_32",
            "Trust.MirSem.usub_underflows_u32",
            "Trust.MirSem.Operand",
            "Trust.MirSem.eval",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_none(),
                "the trust-ir safety env must NOT declare {n}"
            );
        }
        // And the trust-ir spec names ARE declared.
        for n in [
            "Trust.TrustIr.uaddOverflowsU32",
            "Trust.TrustIr.idxOob",
            "Trust.TrustIr.divByZero",
            "Trust.TrustIr.remByZero",
            "Trust.TrustIr.saddOverflowsI32",
            "Trust.TrustIr.negOverflowsI32",
            "Trust.TrustIr.shiftAmountOob32",
            "Trust.TrustIr.shiftAmountOobSigned32",
            // The 128-bit shift widths ARE modeled (the width literal 128 stays a
            // closed `Int.ofNat`, unlike the 128-bit overflow thresholds).
            "Trust.TrustIr.shiftAmountOob128",
            "Trust.TrustIr.shiftAmountOobSigned128",
            "Trust.TrustIr.usubUnderflowsU32",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_some(),
                "the trust-ir safety env must declare {n}"
            );
        }
    }

    #[test]
    fn safety_vc_kind_classifier_in_lockstep_with_mirsem() {
        // The local safety-kind selector must agree with mirsem's on every kind the
        // function-level gates filter by (the two tiers must gate the SAME subset).
        let i32t = || int_ty_of(32, true);
        let kinds: Vec<VcKind> = vec![
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (i32t(), i32t()) },
            VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: i32t(), shift_ty: i32t() },
            VcKind::DivisionByZero,
            VcKind::RemainderByZero,
            VcKind::IndexOutOfBounds,
            VcKind::SliceBoundsCheck,
            VcKind::CastOverflow { from_ty: i32t(), to_ty: int_ty_of(8, true) },
            VcKind::NegationOverflow { ty: i32t() },
            VcKind::Assertion { message: "m".into() },
            VcKind::Postcondition,
            VcKind::Precondition { callee: "c".into() },
            VcKind::Unreachable,
        ];
        for k in &kinds {
            assert_eq!(
                is_safety_vc_kind(k),
                crate::mirsem::is_safety_vc_kind_pub(k),
                "safety-kind classifier lockstep broken for {k:?}"
            );
        }
    }

    // ---- per-kind POSITIVE adequacy (each on the REAL emitted VC) ----

    #[test]
    fn kind1_uadd_overflow_u32_adequate_modulo_3() {
        let func = binop_func(BinOp::Add, 32, false);
        let (kind, verdict) = adequacy_of_first(&func, |k| {
            matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })
        });
        assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind, Some(IrSafetyVcKind::UAddOverflow(IrUWidth::W32)));
        assert!(function_safety_vcs_faithful_via_trustir(&func));
    }

    #[test]
    fn kind2_array_bounds_adequate_modulo_3() {
        let func = idx_array_func();
        let (kind, verdict) = adequacy_of_first(&func, |k| {
            matches!(k, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
        });
        assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind, Some(IrSafetyVcKind::Bounds));
        assert!(function_safety_vcs_faithful_via_trustir(&func));
    }

    #[test]
    fn kind3_div_by_zero_adequate_modulo_3() {
        let func = binop_func(BinOp::Div, 32, true);
        let (kind, verdict) = adequacy_of_first(&func, |k| matches!(k, VcKind::DivisionByZero));
        assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind, Some(IrSafetyVcKind::DivByZero));
        // NOTE: the whole-FUNCTION gate for a signed div also sees the separate
        // `MIN/-1` ArithmeticOverflow{op:Div} VC (unmodeled ⇒ fail-closed there);
        // this test pins the DivisionByZero VC's OWN adequacy.
    }

    #[test]
    fn kind4_signed_add_overflow_i32_adequate_modulo_3() {
        let func = binop_func(BinOp::Add, 32, true);
        let (kind, verdict) = adequacy_of_first(&func, |k| {
            matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })
        });
        assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind, Some(IrSafetyVcKind::SignedOverflow(IrSignedOp::Add, IrSWidth::W32)));
        assert!(function_safety_vcs_faithful_via_trustir(&func));
    }

    #[test]
    fn kind4_signed_sub_overflow_i32_adequate_modulo_3() {
        let func = binop_func(BinOp::Sub, 32, true);
        let (kind, verdict) = adequacy_of_first(&func, |k| {
            matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. })
        });
        assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind, Some(IrSafetyVcKind::SignedOverflow(IrSignedOp::Sub, IrSWidth::W32)));
        assert!(function_safety_vcs_faithful_via_trustir(&func));
    }

    #[test]
    fn kind5_negation_overflow_i32_adequate_modulo_3() {
        let func = neg_func(32);
        let (kind, verdict) =
            adequacy_of_first(&func, |k| matches!(k, VcKind::NegationOverflow { .. }));
        assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind, Some(IrSafetyVcKind::NegOverflow(IrSWidth::W32)));
        assert!(function_safety_vcs_faithful_via_trustir(&func));
    }

    #[test]
    fn kind6_shift_amount_oob_adequate_modulo_3_both_signednesses() {
        // Unsigned amount: core `Ge(n, 32)` ⇒ `shiftAmountOob32`.
        let func_u = shift_func(false);
        let (kind_u, verdict_u) =
            adequacy_of_first(&func_u, |k| matches!(k, VcKind::ShiftOverflow { .. }));
        assert_eq!(verdict_u, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind_u, Some(IrSafetyVcKind::ShiftOob(IrShiftWidth::W32, false)));
        assert!(function_safety_vcs_faithful_via_trustir(&func_u));
        // Signed amount: core `Or([Lt(n,0), Ge(n,32)])` ⇒ `shiftAmountOobSigned32`.
        let func_s = shift_func(true);
        let (kind_s, verdict_s) =
            adequacy_of_first(&func_s, |k| matches!(k, VcKind::ShiftOverflow { .. }));
        assert_eq!(verdict_s, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind_s, Some(IrSafetyVcKind::ShiftOob(IrShiftWidth::W32, true)));
        assert!(function_safety_vcs_faithful_via_trustir(&func_s));
    }

    /// Trust: 128-BIT SHIFT VC WIDTH residue closure — the shift lane's modeled
    /// widths now include 128 (the threshold literal `128` stays a closed
    /// `Int.ofNat`, unlike the 128-bit OVERFLOW thresholds, so nothing leaves
    /// the formula-aware fragment). Both amount signednesses certify on the
    /// REAL emitted VC, kernel-checked def-eq modulo 3.
    #[test]
    fn kind6_shift_amount_oob_128_adequate_modulo_3_both_signednesses() {
        // u128 value, unsigned amount: core `Ge(n, 128)` ⇒ `shiftAmountOob128`.
        let func_u = shift_func_of(128, false, false);
        let (kind_u, verdict_u) =
            adequacy_of_first(&func_u, |k| matches!(k, VcKind::ShiftOverflow { .. }));
        assert_eq!(verdict_u, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind_u, Some(IrSafetyVcKind::ShiftOob(IrShiftWidth::W128, false)));
        assert!(function_safety_vcs_faithful_via_trustir(&func_u));
        // i128 value, signed amount: core `Or([Lt(n,0), Ge(n,128)])` ⇒
        // `shiftAmountOobSigned128`.
        let func_s = shift_func_of(128, true, true);
        let (kind_s, verdict_s) =
            adequacy_of_first(&func_s, |k| matches!(k, VcKind::ShiftOverflow { .. }));
        assert_eq!(verdict_s, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind_s, Some(IrSafetyVcKind::ShiftOob(IrShiftWidth::W128, true)));
        assert!(function_safety_vcs_faithful_via_trustir(&func_s));
    }

    /// Trust: 128-BIT SHIFT VC WIDTH residue closure — LITERAL amounts at the
    /// 127/128/129 boundary on a u128 value. ADEQUACY certifies for all three
    /// (the certificate says the VC states EXACTLY `128 ≤ k` — true statements
    /// about UB shifts included); whether the shift is actually SAFE is the
    /// separate DISCHARGE axis (refuting `128 ≤ 127` succeeds; `128 ≤ 128/129`
    /// correctly cannot be refuted).
    #[test]
    fn kind6_shift_literal_amounts_at_the_128_boundary_adequate() {
        for k in [127u128, 128, 129] {
            let func = shift_func_literal_128(k);
            let (kind, verdict) =
                adequacy_of_first(&func, |k| matches!(k, VcKind::ShiftOverflow { .. }));
            assert_eq!(
                verdict,
                RefinementVerdict::ProvenModulo3,
                "u128 >> {k}: the literal-amount core `Ge(Int({k}), Int(128))` must certify"
            );
            assert_eq!(kind, Some(IrSafetyVcKind::ShiftOob(IrShiftWidth::W128, false)));
        }
    }

    #[test]
    fn kind7_usub_underflow_u32_adequate_modulo_3() {
        let func = binop_func(BinOp::Sub, 32, false);
        let (kind, verdict) = adequacy_of_first(&func, |k| {
            matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. })
        });
        assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind, Some(IrSafetyVcKind::USubUnderflow(IrUWidth::W32)));
        assert!(function_safety_vcs_faithful_via_trustir(&func));
    }

    #[test]
    fn kind8_rem_by_zero_adequate_modulo_3() {
        let func = binop_func(BinOp::Rem, 32, false);
        let (kind, verdict) = adequacy_of_first(&func, |k| matches!(k, VcKind::RemainderByZero));
        assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
        assert_eq!(kind, Some(IrSafetyVcKind::RemByZero));
        assert!(function_safety_vcs_faithful_via_trustir(&func));
    }

    // ---- NEGATIVE controls (fail-closed) ----

    #[test]
    fn wrong_width_spec_is_kernel_rejected() {
        // OFF-BY-WIDTH CRUX (mirrors mirsem's wrong-width controls): take the REAL
        // u32-add VC, extract its live core, and claim it equals the u16 spec. The
        // thresholds are DIFFERENT closed literals (65535 vs 4294967295) ⇒ NOT
        // def-eq ⇒ the Eq.refl bridge proof is KERNEL-REJECTED.
        use trust_types::Formula as F;
        let func = binop_func(BinOp::Add, 32, false);
        let vcs = trust_vcgen::generate_vcs(&func);
        let vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("u32 add raises an overflow VC");
        let leaf = find_violation_leaf(&vc.formula, &|f| match f {
            F::Gt(lhs, rhs) => binop_operands(lhs).is_some() && matches!(&**rhs, F::Int(_)),
            _ => false,
        })
        .expect("the emitted overflow disjunct exists");
        let F::Gt(add_t, _) = leaf else { panic!("guarded") };
        let (a_op, b_op) = binop_operands(add_t).expect("fragment operands");
        // WRONG width: the u16 spec against the u32-emitted core.
        let name = uadd_overflows_ir_name(IrUWidth::W16);
        let verdict = overflow_family_live_def_eq_ir(leaf, &[a_op, b_op], &|ops| {
            Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
        });
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "a wrong-width (u16 vs u32) spec claim MUST be kernel-rejected, got {verdict:?}"
        );
    }

    #[test]
    fn off_by_one_threshold_formula_is_declined() {
        // OFF-BY-ONE CRUX: a hand-built overflow VC whose emitted threshold is 2^32
        // (NOT the modeled 2^32−1) matches NO modeled width ⇒ the width recovery
        // fails ⇒ KernelRejected (never a spuriously-certified nearby width).
        use trust_types::{Formula as F, Sort, SourceSpan, VerificationCondition};
        let a = || Box::new(F::Var("a".into(), Sort::Int));
        let b = || Box::new(F::Var("b".into(), Sort::Int));
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (int_ty_of(32, false), int_ty_of(32, false)),
            },
            function: "crate::f".into(),
            location: SourceSpan::default(),
            formula: F::Gt(
                Box::new(F::Add(a(), b())),
                Box::new(F::Int(1i128 << 32)), // off-by-one: 2^32, not 2^32−1
            ),
            contract_metadata: None,
        };
        let verdict = trustir_safety_vc_adequate(&vc);
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "an off-by-one threshold MUST be declined, got {verdict:?}"
        );
    }

    #[test]
    fn unmodeled_kind_and_var_var_mul_fail_closed() {
        // (a) An unmodeled SAFETY kind (CastOverflow) is KernelRejected.
        use trust_types::{Formula as F, Sort, SourceSpan, VerificationCondition};
        let cast_vc = VerificationCondition {
            kind: VcKind::CastOverflow { from_ty: int_ty_of(64, true), to_ty: int_ty_of(8, true) },
            function: "crate::f".into(),
            location: SourceSpan::default(),
            formula: F::Var("x".into(), Sort::Int),
            contract_metadata: None,
        };
        assert!(
            matches!(trustir_safety_vc_adequate(&cast_vc), RefinementVerdict::KernelRejected(_)),
            "an unmodeled safety kind must be KernelRejected"
        );
        // (b) The var*var signed MUL (BV emission, no LIA `Or([Lt(Mul…),Gt(Mul…)])`
        // leaf) DECLINES at the bridge ⇒ the whole function fails closed — the
        // honest deferred gap, mirroring mirsem's `signed_mul_fails_closed_deferred_gap`.
        let mul_func = binop_func(BinOp::Mul, 32, true);
        let vcs = trust_vcgen::generate_vcs(&mul_func);
        assert!(
            vcs.iter()
                .any(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. })),
            "a signed i32 mul raises an ArithmeticOverflow{{op:Mul}} VC"
        );
        assert!(
            !function_safety_vcs_faithful_via_trustir(&mul_func),
            "a var*var signed-mul function must fail closed on the trust-ir tier \
             (its BV overflow VC has no LIA core)"
        );
    }

    #[test]
    fn function_gate_vacuous_and_agreement_with_mirsem() {
        // VACUOUS edge (copied from the MirSem witness semantics): a function that
        // emits NO safety VC is vacuously faithful.
        let id = identity_func();
        let vcs = trust_vcgen::generate_vcs(&id);
        assert!(
            !vcs.iter().any(|vc| is_safety_vc_kind(&vc.kind)),
            "the identity function must emit no safety VC"
        );
        assert!(
            function_safety_vcs_faithful_via_trustir(&id),
            "zero safety VCs ⇒ vacuously faithful (the MirSem vacuously-safe edge)"
        );
        // AGREEMENT with the MirSem tier on a NON-vacuous function: the u32-add
        // function is safety-faithful on BOTH tiers (the relocation preserves the
        // verdict; the trust-ir tier is not a weaker bar).
        let uadd = binop_func(BinOp::Add, 32, false);
        assert!(
            crate::mirsem::function_safety_vcs_faithful(&uadd).is_some_and(|c| c.all_modulo_3()),
            "MirSem tier certifies the u32 add"
        );
        assert!(
            function_safety_vcs_faithful_via_trustir(&uadd),
            "trust-ir tier certifies the SAME function"
        );
    }
}
