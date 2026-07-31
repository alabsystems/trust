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

// ---------------------------------------------------------------------------
// Trust: EMITTER-ANCHORED VIOLATION SELECTION (2026-07-29) — the trust-ir
// relocation of the shift-core selection fix
// (`mirsem::vc_faithful::emitted_shift_violation`, commit f1e45ccb0fe),
// generalized to every kind this tier certifies.
//
// THE DEFECT THIS REPLACES. This file used to locate each kind's violation core
// with `find_violation_leaf(&vc.formula, pred)`: the FIRST leaf matching a shape
// predicate in a pre-order walk of the WHOLE VC formula, descending into `Not` and
// into `Implies` hypotheses BEFORE conclusions. But `vc.formula` is NOT the
// violation — every
// `v2_build_*` emitter in `trust_vcgen::generate::checked_vcs` /
// `overflow_vc` / `safety` wraps its violation in
//
//   * same-block definitions      (`combine_relevant_block_defs`)
//   * dominating path guards      (`v2_formula_with_path_guards`)
//   * the function's `#[requires]` (`conjoin_preconditions_versioned`)
//   * parameter / local / field / slice-len type bounds (`conjoin_*_ranges`)
//
// and every one of those hypotheses is a comparison of the same syntactic family
// as a violation. So the scan silently certified a HYPOTHESIS, i.e. minted a
// kernel-checked adequacy certificate about a proposition the VC does not contain.
// MEASURED on the committed `bit_field` fixture (`<u8 as BitField>::get_bit`,
// real core `Ge(bit, 8)`), through this very tier:
//
//   no precondition      -> KernelRejected (`Ge(bit,0)` picked; width 0 unmodeled)
//   `Ge(bit, 64)` added  -> ShiftOob(W64) ProvenModulo3   FORGED, gate flips true
//   `Ge(other, 32)`      -> ShiftOob(W32) ProvenModulo3   FORGED, `other` is never
//                                                         shifted by
//
// and the same on `idx_array` (`Ge(p,q)` certified in place of `Ge(i,8)`), on
// div-by-zero (`Eq(z,0)` certified in place of `Eq(b,0)`) and on negation
// (`Eq(k,-128)` mints `NegOverflow(W8)` for an `i32` negation).
//
// It does NOT need a hostile `#[requires]`. `itoa`'s `<u8 as Sealed>::write` carries
// a dominating `Assert{Overflow(Add)}` whose guard is threaded in as
// `Not(Gt(Add(_43, 2), u64::MAX))`; the scan descends the `Not` and returns that
// `Gt`, so the body's own `u8` add `Gt(Add(_63, 48), 255)` was certified
// `UAddOverflow(W64)` — wrong width AND wrong operands, on unmodified real-crate
// code (pinned by `selection_tests::a_dominating_overflow_guard_can_never_supply_
// the_certified_add`).
//
// THE REPLACEMENT. The violation is located from the EMITTER'S OWN CONSTRUCTION,
// and the loose scan is DELETED rather than kept as a fallback — a fallback keeps
// the forgery lane open. Two construction facts do the work:
//
//  (1) POSITION. Every wrapper listed above conjoins the VC body as the LAST
//      element: `combine_relevant_block_defs` (`conjuncts.push(formula)`,
//      block_defs.rs:696), `versioned::conjoin` (`conj.push(vc)`, versioned.rs:67),
//      `conjoin_arg_type_ranges` / `conjoin_local_type_ranges_excluding` /
//      `conjoin_datatype_field_ranges_excluding` / `conjoin_slice_len_bounds`
//      (`bounds.push(formula)`, type_ranges.rs:126/207/…), the semantic-guard
//      splice (`conjuncts.push(vc.formula)`, safety.rs:896) and
//      `v2_formula_with_path_guards`, which FLATTENS the body's `And` after the
//      guards (safety.rs:1112) and — when a block has several guard paths — wraps
//      the per-path conjunctions in an `Or`. So the violation is reachable from the
//      formula root by taking the LAST conjunct of each `And` and every `And`
//      disjunct of an `Or`; a hypothesis is never on that path. (The `Or` descent is
//      restricted to `And` disjuncts because that is the only shape the multi-path
//      split builds — see `violation_candidates`.)
//
//  (2) SHAPE. Where the emitter builds a distinctive range/violation GROUP the
//      located node must also sit in it, with its operands agreeing structurally:
//        * shift  — `And([input_range_constraint(n), invalid(n)])`
//                   (`v2_shift_violation_formula`, checked_vcs.rs:494)
//        * arith  — `And([input_range(a), input_range(b), out_of_range(a∘b)])`
//                   (`v2_build_overflow_vc_for_operands`, overflow_vc.rs:467)
//        * neg    — `And([input_range(v), Eq(v, INT_MIN)])`
//                   (`v2_build_negation_raw_vc`, checked_vcs.rs:775)
//      A GROUP, NOT AN ARITY: `v2_formula_with_path_guards` FLATTENS the emitter's
//      `And` into the guard conjunction (safety.rs:1110-1115), so those conjuncts
//      can arrive as siblings of dominating guards rather than as a nested
//      pair/triple. The check is "the violation is LAST and each operand's
//      `input_range_constraint` is SOMEWHERE among the siblings" — see
//      `has_range_sibling`. Bounds and div/rem-by-zero emit their violation BARE
//      (`Ge(i,len)` / `Eq(d,0)`), so no group exists and (1) is the whole
//      discriminator for them.
//
// AMBIGUITY FAILS CLOSED. The located set must collapse to a SINGLETON up to
// structural equality — the discipline `resolve_certified_callee` already applies
// at every tier — because two DIFFERENT violations reachable at the body position
// give no principled way to say which one this VC's kind is about. (Duplicates of
// the same proposition are fine and common: the path-guard `Or` repeats the body
// once per path.)
//
// MEASURED over the 2326 committed fixture functions, comparing the OLD first match
// against the emitter's own violation BY VALUE. The corpus emits 772 safety VCs; the
// 85 `ArithmeticOverflow` VCs whose op/signedness combination this tier does not model
// (`arith-other`: the BV `var*var` mul lane and the mixed-signedness forms) decline
// before the locator and are excluded from the table, so its denominator is 687:
//
//   kind    VCs   old == emitted   old DIFFERS   emitted absent, old supplied one
//   bounds   68        13              20                   34
//   divrem   65        40               8                    0
//   neg      12        12               0                    0
//   shift   133        27             106                    0
//   signed  100        93               0                    0
//   uadd    120        89              25                    2
//   usub    189       189               0                    0
//   TOTAL   687       463             159                   36
//
// i.e. 195 of the 687 MODELED safety VCs (28% of them; 25% of the 772 the corpus
// actually emits — quote whichever, but not the 28% against the 772) had their
// kernel-checked adequacy certificate read off a proposition the VC does not contain.
// Certified rows move 551 -> 584 and the function-level
// `function_safety_vcs_faithful_via_trustir` gate moves 240 -> 238 of the 362
// safety-VC-bearing functions.
//
// Trust: THE ACCOUNTING BELOW IS RE-MEASURED AND CORRECTED (2026-07-29, lane-B
// finding [3]). It used to read "30 WITHDRAWN against 28 RECOVERED", split 27/3, with
// `arrayvec::…::retain::process_one` listed among the recoveries. All three are wrong,
// and the first two were wrong in opposite directions, so the arithmetic still landed
// on 238. The two baselines are also now kept apart: PRE-AUDIT means the committed
// f1e45ccb0fe blob of this file; PRE-FIX means the first version of the audit fix, the
// one the reviewer read. Everything in this paragraph is PRE-AUDIT -> now.
//
// 29 function certificates WITHDRAWN against 27 RECOVERED (240 - 29 + 27 = 238).
//
// ALL 29 withdrawals lose the gate on a `SliceBoundsCheck` row — not 27 bounds plus
// three arithmetic-bearing bodies: `byteorder::read_*`/`write_*` (20),
// `arrayvec::drain_range` / `extend_from_slice` / `swap_pop` (3), `slice::first` and
// `slice::last` (3 dumps, 2 functions), `BigNat::from_limbs`,
// `ascii_utils::check_ascii_printable` and `parser__fold_exprs`. Every one of them
// declines with "this VC's OWN emitted `Ge(index, len)` violation could not be located
// unambiguously", i.e. on the slice-RANGE shape this tier does not model — the real
// violation is `Gt(start,end) ∨ Gt(end,len)`, or (arrayvec `swap_pop`) the `Ge`-spelled
// twin `Or([Ge(index,len), Ge(end,len)])`, and `idxOob` covers one disjunct of it.
// Where the pre-audit `true` came from, MEASURED by re-running the old pre-order scan
// over these functions' 34 now-declining bounds rows: 30 located a non-negativity
// hypothesis `Ge(x, Int 0)` (`conjoin_slice_len_bounds`' `Ge(buf__slice_len, 0)` and the
// extractor's parameter-domain bounds), 3 located `Ge(self__slice_len, Int 1)`, and 1
// (`swap_pop`) located the RHS of the block definition `Eq(_5, Ge(index, len))` — a
// different length term from the one its own body compares against.
//
// The 27 recovered are the whole `BitField::get_bit`/`set_bit` family (12 integer
// types x 2 = 24) — the shift-width collision of
// `reports/2026-07-29-ladder-fixture-refreeze.md` §5 — plus
// `one_less_than_next_power_of_two`, `udiv` and `unsafe_div`.
// `arrayvec::ArrayVec::<T, CAP>::retain::process_one` is NOT among them: it is green
// PRE-AUDIT with 3 certified rows and green now, net unchanged. It is the +1 gate
// against the PRE-FIX tree, which is a different comparison — see the next paragraph.
//
// WHAT A WITHDRAWAL COSTS — the earlier blanket "no withdrawal is a capability loss"
// was FALSE and is retracted. The selection accepts a node the VC BODY occupies, or —
// on the ASSERT route alone, whose body is the bare condition local — the right-hand
// side of that local's MIR-CONFIRMED defining statement; nothing else. But a locator
// can still be too strict and decline a node that IS the body. That happened:
// requiring the arithmetic
// range/violation group to be EXACTLY a 3-element `And` missed the two
// `Or([Lt(g+1,0), Gt(g+1,u64::MAX)])` rows of
// `arrayvec::ArrayVec::<T, CAP>::retain::process_one`, whose group a dominating guard
// had been flattened into — a legitimate certificate, dropped for an arity that the
// emitter does not actually guarantee. Fixed here; against the PRE-FIX tree (not the
// pre-audit one) that is arith located 453 -> 455, certified 582 -> 584, gate
// 237 -> 238, with no row withdrawn in exchange, and the shape checks no longer fix an
// arity anywhere. The claim that survives is the narrow one:
// a declined row is either a row whose pre-fix certificate was about something else,
// or a row whose violation this tier does not model — never a row this tier could
// have certified about its own violation.
//
// ROUND 3 — THREE MORE TIGHTENINGS, ALL MEASURED AT ZERO COST. Corpus: the same 2326
// committed fixture functions / 772 emitted safety VCs, base f1e45ccb0fe + the audit
// fix. Certified 584 and gate 238-of-362 BEFORE and AFTER, with 0 of the 772 per-VC
// verdicts differing (row-by-row diff, not just the totals):
//   * the assert-condition route now confirms the located binding against the MIR
//     ([`violation_candidates_resolved`]) — a `#[requires]` that binds the assert's
//     condition local was otherwise indistinguishable from its block definition, and
//     minted `NegOverflow(W32)` for a negation of a variable the body never negates;
//   * `LocatedViolation::all_siblings` fails closed on an EMPTY sibling set instead of
//     passing vacuously;
//   * the bounds and div/rem locators assert the body position themselves
//     ([`candidate_at_body_position`]) instead of inheriting it from the producer.
// The third is a no-op today by construction and is pinned as one; the first two have
// regression tests verified to FAIL on the reverted tree.
//
// ROUND 4 — TWO MORE, ALSO MEASURED AT ZERO COST, plus one comment retracted. Same
// corpus (2326 fixture functions, 772 emitted safety VCs). Certified 584 and gate
// 238-of-362 BEFORE and AFTER, with 0 of the 772 per-VC verdicts differing (row-by-row
// diff of `(file, vc index, kind, minted kind, ProvenModulo3?)`, not just the totals):
//   * NEGATION — the certified variable must, on the assert-condition route, BE the
//     operand the assert's own target block negates, and the width must come from THAT
//     variable's type ([`assert_negation_subject`]). Round 3 authenticated which
//     comparison the condition local was bound to but never what the VC was about, so a
//     dominating `assert!(!(x == i32::MIN))` over a negation of an unrelated `y` still
//     minted `negOverflowsI32 x` — and minted a 32-bit certificate about an `i8` when
//     `x` was narrowed.
//   * UADD VACUITY — the range side condition is now a universal over EVERY occurrence
//     of the located violation, not a pre-filter on the set the universal ranges over
//     ([`emitted_arith_violation_located`]); and that lane declines on a mixed `Or`,
//     whose bare disjunct the candidate producer cannot see at all.
// RETRACTED: the claim that a MIXED path-guard `Or` is unreachable. It is reachable
// through an unwind edge; see [`violation_candidates`], which now says so and says what
// is true instead.
//
// ROUND 5 — THE SELECTION IS ONE LOCATOR, AND EVERY DEFENCE IS SHARED BY EVERY LANE.
// Round 4's fixes were per-lane, and three of the five survivors it left were not "a
// defence that failed" but "a defence a lane never had" — which is also how the same
// defect kept coming back in the sibling MirSem tier. Six changes, ALL MEASURED AT ZERO
// COST over the same corpus:
//
//   MEASUREMENT COMMAND (re-run it; do not transcribe this paragraph):
//     cd crates && RUSTC_BOOTSTRAP=1 \
//       TRUSTIR_CENSUS_OUT=/tmp/rows.txt cargo test --offline -p trust-clean --lib -- \
//       --ignored --nocapture selection_tests::trustir_corpus_census
//   BEFORE and AFTER, 2026-07-31: funcs=2326 safetyVCs=772 certified=584 gate=238/362,
//   per-kind bounds 33/68, divrem 63/65, neg 12/12, shift 81/133, signed 93/122,
//   uadd 114/120, usub 188/189, arith-other 0/63 — and a row-by-row `diff` of the two
//   `(fixture, vc index, kind, minted kind, ProvenModulo3?)` dumps is EMPTY modulo the
//   `Bounds` → `Bounds { signed: false }` label change. 0 rows withdrawn, 0 recovered.
//
//   * ONE LOCATOR ([`locate_violation`]). Each lane used to `filter` the candidates by
//     its own shape predicate and only then collapse to a singleton, so a body position
//     the lane did not recognize was DROPPED from the set the ambiguity rule ranged
//     over. The agreement rule now runs over the UNFILTERED occurrences and the shape
//     predicate is applied to the collapsed node.
//   * THE MIXED `Or` DECLINES FOR EVERY LANE, at the producer
//     ([`violation_candidates_resolved`]) — round 4 declined on it in the arithmetic
//     lane alone, leaving bounds, shift and div/rem certifying off a guarded twin while
//     a body position they never examined sat in the same formula.
//   * A RANGELESS OCCURRENCE FAILS THE SIDE CONDITION INSTEAD OF DROPPING OUT OF IT
//     ([`LocatedViolation::all_siblings`], now over `Option<&[Formula]>`).
//   * THE NEGATION SUBJECT GATE IS KEYED ON THE SUBJECT, NOT THE ROUTE
//     ([`negation_subjects`]) — round 4's gate ran only on the assert-condition route,
//     so the same forgery re-minted through the direct route, which this API accepts
//     from any caller. The width now comes from the CERTIFIED VARIABLE's own
//     `operand_ty`.
//   * MIXED-WIDTH ARITHMETIC MUST JUSTIFY ITS NARROWING
//     ([`mixed_width_narrowing_is_justified`]) — "a width either operand type mentions"
//     is a free choice when the two differ. OBSERVED on the reverted tree: a
//     two-bare-`Var` body under kind `(i8, i64)` minted
//     `(Some(SignedOverflow(Add, W8)), ProvenModulo3)` with nothing narrowing anything.
//     The `(i64, i8)` mirror image at `W64` is asserted by the same regression test but
//     was NOT separately observed — the first assertion aborts the pre-fix run.
//   * THE SIGNED-INDEX BOUNDS FORM IS A NAMED GAP ([`bounds_violation_shape`],
//     `IrSafetyVcKind::Bounds { signed }`), not a shape mismatch that declined for the
//     right reason by accident.
// The shift lane's `operand_ty`-vs-threshold gap is NOT closed and is now DOCUMENTED
// here as well as in the MirSem twin, with its own re-measured pair census — see the
// `K::ShiftOverflow` arm. An honest matched deferral, not a silent asymmetry.
//
// HONEST LIMIT ON THAT ZERO. "Zero cost" is a corpus fact and, for both tightenings, it
// is zero for a REASON worth stating rather than because the checks are no-ops:
//   * (ROUND 4, SUPERSEDED BY ROUND 5 — kept because the reason it was zero then is not
//     the reason it is zero now.) The round-4 negation subject check fired only on the
//     assert-condition route, and 0 of the corpus's 12 certified negation rows take that
//     route — 5 are `abs` calls and 7 are raw `Rvalue::UnaryOp(Neg, ..)`, both of which
//     carry the emitter's own range/violation pair and are located with
//     `siblings: Some(..)`. Round 5 runs the subject check on EVERY route, so those 12
//     rows now go THROUGH it rather than around it, and it is still zero-cost for a
//     different and stronger reason: all 12 name a subject the MIR really does negate or
//     pass to `iN::abs`, at that subject's own declared width (MEASURED 2026-07-31 —
//     neg 12 certified of 12, unchanged, in the census above);
//   * the mixed-`Or` decline is NOT free in general. The emitter really does build a
//     mixed `Or` for a `Drop` with a `Cleanup` unwind edge over a bare (non-`And`) VC
//     body. It is free HERE as a CORPUS FACT (0 of the 772 safety VCs carry a mixed
//     `Or`, and 0 of those are arithmetic; re-taken 2026-07-30), NOT because arithmetic
//     bodies are always `And`s. `overflow_vc` alone builds four bodies for this kind —
//     the Int-path `And([lhs_range, rhs_range, out_of_range])` (overflow_vc.rs:467), the
//     `var*var` BV mul (:409-414), the signed-128 add/sub BV formula (:307-312, BARE
//     when no block-defs or guards are conjoined onto it), and a bare
//     `Formula::Bool(false)` for a corner-bounded signed-128 `Mul` (:261) — and
//     `checked_vcs.rs:42-50` emits one whose body is the bare assert-condition local.
//     Any of those whose body is still BARE at the path-guard splice — the
//     `Bool(false)`, either BV formula when `terms.is_empty()`, or the assert-condition
//     local when no block-def is relevant — WILL be declined by this lane on a
//     `Drop`+`Cleanup` CFG. The Int-path `And` body will NOT be: the empty-guard path
//     pushes the body unchanged (`generate/safety.rs:1079` is `terms.push(formula.clone())`),
//     so an `And` body yields an `And` disjunct and the `Or` is never mixed —
//     `contains_mixed_or` needs both an `And` and a non-`And` disjunct. That scoping is
//     load-bearing: the first draft of this correction said "any of those", which was
//     itself false for exactly the body it had just listed first.
//     The decline is the fail-closed direction and is preferred to quantifying a
//     soundness side condition over half the paths.
//
// PARTIAL ADEQUACY — TWO INSTANCES, BOTH NOW CHECKED RATHER THAN ARGUED. Where the
// emitter's violation is a two-disjunct `Or` and the pinned spec models one disjunct,
// grounding that disjunct alone mints a certificate about LESS than the VC states.
// This tier has exactly two such lanes and closes them differently:
//   * uadd — `Or([Lt(a+b,0), Gt(a+b,MAX)])`, spec `uaddOverflows`. Grounded on the
//     `Gt`, which is sound only because the conjoined unsigned ranges make the `Lt`
//     unsatisfiable. That vacuity is now a REQUIRED side condition (the discarded
//     disjunct must be `Lt` over the same sum against `0`, and both operands must
//     carry a sibling range with lower bound `0`), not a comment. 120/120 located
//     uadd `Or` cores satisfy it.
//   * signed-index bounds — `Or([Lt(i,0), Ge(i,len)])`, spec `idxOob`, which models
//     `i ≥ len` only and has no vacuity argument available. DECLINED outright: the
//     `Or`'s disjuncts are no longer candidates at all (`violation_candidates`
//     descends only `And` disjuncts of an `Or`, the sole shape the multi-path guard
//     split builds). 0 of the corpus's 33 certified bounds rows came from that
//     position. Modeling it needs an `idxOobSigned` spec — a capability gap, recorded
//     as one.
//
// THE SINGLETON NOW COSTS NOTHING. Over the same corpus, running each locator WITHOUT
// the singleton collapse: bounds 33 located / 0 multi-distinct, divrem 63/0, neg 12/0,
// shift 133/0 (the exact analogue of the MirSem fix's 77/77), signed 93/0, uadd 120/0,
// usub 189/0. The one multi-distinct row the earlier measurement reported (bounds,
// 34 located / 1 multi) was the signed-index `Or` whose disjuncts are no longer
// candidates at all; it was in the `old_none` bucket, i.e. not certified before the
// fix either, so no verdict ever depended on it. The collapse stays: it is the
// fail-closed answer to an ambiguity the emitter could reintroduce, not a no-op that
// happens to be free today.

/// Whether `f` is an integer LITERAL — the only shape `range::type_min_formula` /
/// `type_max_formula` produce for a bound.
fn is_int_literal(f: &trust_types::Formula) -> bool {
    matches!(f, trust_types::Formula::Int(_) | trust_types::Formula::UInt(_))
}

/// Whether `f` is the integer literal `0` (either integer spelling).
fn is_zero_literal(f: &trust_types::Formula) -> bool {
    matches!(f, trust_types::Formula::Int(0) | trust_types::Formula::UInt(0))
}

/// The term an `input_range_constraint` constrains, with its LOWER bound.
/// `range::input_range_constraint` builds VERBATIM `And([Le(Int lo, t), Le(t, Int hi)])`
/// (range.rs:92) — anything else is not one and returns `None`.
fn range_constraint_parts(
    f: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula)> {
    use trust_types::Formula as F;
    let F::And(v) = f else { return None };
    let [F::Le(lo, t_lo), F::Le(t_hi, hi)] = v.as_slice() else { return None };
    (is_int_literal(lo) && is_int_literal(hi) && t_lo == t_hi).then(|| (&**t_lo, &**lo))
}

/// The term an `input_range_constraint` constrains (see [`range_constraint_parts`]).
fn range_constrained_term(f: &trust_types::Formula) -> Option<&trust_types::Formula> {
    range_constraint_parts(f).map(|(t, _)| t)
}

/// Whether some conjunct of `sibs` is an `input_range_constraint` on `term` — the
/// emitter's own operand bound. The ARITY of `sibs` is deliberately not fixed: a
/// dominating path guard is FLATTENED into the same `And` as the emitter's
/// range/violation group (`v2_formula_with_path_guards`, safety.rs:1110-1115,
/// `Formula::And(inner) => conj.extend(inner)`), so the group's own conjuncts are
/// siblings of the guards rather than a nested pair/triple. Anchoring is unchanged:
/// the caller still requires the violation to be the LAST conjunct, which is the
/// only position the VC body ever occupies.
fn has_range_sibling(sibs: &[trust_types::Formula], term: &trust_types::Formula) -> bool {
    sibs.iter().any(|s| range_constrained_term(s) == Some(term))
}

/// As [`has_range_sibling`], and the bound's LOWER end is exactly `0` — i.e. the
/// emitter proved `term ≥ 0` alongside the violation (an UNSIGNED operand range).
fn has_nonneg_range_sibling(sibs: &[trust_types::Formula], term: &trust_types::Formula) -> bool {
    sibs.iter().any(|s| {
        range_constraint_parts(s).is_some_and(|(t, lo)| t == term && is_zero_literal(lo))
    })
}

/// Whether `node` sits at the emitter's BODY position in `sibs`: the LAST conjunct,
/// by identity (not by value — a hypothesis equal to the body must not qualify).
fn is_body_position(sibs: &[trust_types::Formula], node: &trust_types::Formula) -> bool {
    sibs.last().is_some_and(|last| std::ptr::eq(last, node))
}

/// One candidate for THIS VC's own violation: the node, plus the conjunct list of
/// the `And` it was taken as the LAST element of (`None` when it sits directly
/// under an `Or` or is the whole formula — then no emitter pair can be checked).
#[derive(Clone, Copy)]
struct ViolationCandidate<'a> {
    node: &'a trust_types::Formula,
    siblings: Option<&'a [trust_types::Formula]>,
}

/// Every node the VC BODY can occupy, per construction fact (1) above: descend the
/// LAST conjunct of each `And`, and the `And` disjuncts of an `Or` (the multi-path
/// guard split) — keeping the `Or` itself, because a violation can BE an `Or` (the
/// signed out-of-range and signed-shift forms). Hypotheses are unreachable from here.
///
/// WHY THE `Or` DESCENT IS RESTRICTED TO `And` DISJUNCTS.
///
/// Trust: CORRECTED (2026-07-29, lane-A cross-lane finding). This comment used to say
/// "`v2_formula_with_path_guards` builds every disjunct as `Formula::And(conj)` — a
/// bare non-`And` disjunct is therefore never a wrapper artifact". The first clause is
/// FALSE OF THAT FUNCTION: an EMPTY-guard path pushes the RAW body
/// (`if guards.is_empty() { terms.push(formula.clone()) }`, safety.rs:1078-1080), and
/// only a non-empty one pushes `And([guards…, body…])` (safety.rs:1115). Considered
/// alone, the splice can therefore emit a MIXED `Or`.
///
/// Trust: CORRECTED AGAIN (2026-07-30, round-4 defect [8] — the SECOND false claim at
/// this site, introduced by the commit that fixed the first). The replacement text
/// argued that the mixed `Or` is UNREACHABLE, because `v2_build_path_guard_map`
/// "pushes a guard on EVERY edge it follows (`next_guards.push(..)`, safety.rs:1047),
/// so only `bb0` can receive an empty path". THAT IS FALSE, and the counterexample is
/// four lines below the line it cites. safety.rs:1051-1053 is
/// `for target in block.terminator.unguarded_successors() { queue.push_back((target,
/// succ_guards.clone(), path_blocks.clone())) }` — the guard list threaded UNCHANGED —
/// and `Terminator::unguarded_successors` (trust-types/src/model.rs:6882-6900) returns
/// the `Goto`/`Call`/`Drop`/`Opaque` targets AND, for every terminator that has one,
/// the `unwind_cleanup_target` (model.rs:6872-6879, which covers `Call`, `Assert` and
/// `Drop`). An EMPTY path therefore reaches every block reachable from `bb0` along
/// unguarded edges, and a block reachable by both a guarded and an unguarded edge gets
/// a MIXED path list. The instance two committed tests actually drive:
/// `bb0 = Drop { target: bb1, unwind: Cleanup(bb2) }` — BOTH edges unguarded, so `bb2`
/// inherits `bb0`'s empty list — `bb1 = SwitchInt` (a `discovered_clauses` edge, so its
/// edge to `bb3` pushes a guard), `bb2 = Goto(bb3)`. `bb3`'s list is `[[g], []]`, which
/// safety.rs:1078-1080 + 1115 + 1121 splice into an `Or` with one `And([g, body…])`
/// disjunct and one BARE `body` disjunct — provided the body is not itself an `And`,
/// which is why both tests use an assert whose condition local this block does NOT
/// define. The two tests are lane A's
/// `mirsem::obligation_region_tests::a_mixed_path_guard_or_can_never_supply_a_bounds_core`
/// (obligation_region_tests.rs:913, `assert!(contains_mixed_or(&vc.formula))` at :955)
/// and this file's own
/// `selection_tests::a_mixed_path_guard_or_is_emitter_reachable_through_an_unwind_edge`.
/// So: the mixed `Or` is EMITTER-REACHABLE. Do not re-derive an impossibility argument
/// here.
///
/// WHAT IS TRUE, stated as what it is — one measurement and one direction.
///
/// MEASURED (re-taken 2026-07-30, not inherited; RE-CONFIRMED 2026-07-31 by
/// `selection_tests::trustir_corpus_census`, which now counts this population itself):
/// over the 2326 committed fixture functions, of the 772 safety VCs they emit, 0 contain
/// an `Or` anywhere with both an `And` and a non-`And` disjunct. That is a corpus fact
/// about the fixtures, not a property of the emitter.
///
/// DIRECTION: skipping a bare disjunct can only DROP a candidate, never admit one, so
/// it cannot let a hypothesis be certified — the failure mode this restriction exists
/// for. In every mixed `Or` traced through `v2_formula_with_path_guards`, the bare
/// disjunct is the RAW `formula` argument (safety.rs:1078-1080), i.e. the same body the
/// guarded disjuncts carry flattened alongside their guards (safety.rs:1112-1113), so
/// what is dropped is a DUPLICATE of a candidate that survives. That is a statement
/// about the traced cases, not a proof over all inputs.
///
/// WHERE DROPPING A DUPLICATE IS NOT HARMLESS, the consumer says so itself: a lane that
/// reads a SIDE CONDITION off the surviving occurrences' siblings would then quantify
/// over the guarded paths only. That is round-4 defect [3].
///
/// Trust: AND IT IS NOT ONLY THE SIDE-CONDITION LANE (2026-07-31, round-5 defect [7]).
/// Round 4 closed it by declining on a mixed `Or` inside `emitted_arith_violation_located`
/// — "the one such lane". That was wrong about the scope: a lane that reads its CERTIFIED
/// PROPOSITION off the surviving occurrences is equally exposed, since the unexamined
/// bare disjunct is a body position stating something this tier never read. All four
/// other lanes do exactly that. The decline therefore lives in
/// [`violation_candidates_resolved`] now, where every lane inherits it, and no consumer
/// relies on this paragraph.
///
/// Every OTHER `Or` reachable here IS a violation:
/// `Or([Lt(i,0), Ge(i,len)])` (signed index), `Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])`
/// (out-of-range), `Or([Lt(n,0), Ge(n,W)])` (signed shift amount) — and its disjuncts
/// are HALVES of that violation, not violations. Descending into them let the tier
/// certify half a proposition: the signed-index bounds VC minted `idxOob(len, i)`, a
/// kernel certificate that says nothing about the `i < 0` half the VC also states.
/// That is the same defect class as certifying a hypothesis (a certificate about a
/// proposition other than the one the VC carries), so it fails closed here instead.
fn violation_candidates<'a>(
    f: &'a trust_types::Formula,
    siblings: Option<&'a [trust_types::Formula]>,
    out: &mut Vec<ViolationCandidate<'a>>,
) {
    use trust_types::Formula as F;
    match f {
        F::And(v) => match v.last() {
            Some(last) => violation_candidates(last, Some(v.as_slice()), out),
            // Trust: AN EMPTY `And` IS AN OCCURRENCE, NOT A NON-EVENT (2026-07-31,
            // round-6 F4). This arm used to be `if let Some(last)`, so an empty `And`
            // yielded NO candidate — and `Or([And([core]), And([])])` therefore
            // presented exactly one occurrence, the lane's own core, which agrees with
            // itself and mints. `clean_ground::ground_prop` folds an empty `And` to
            // `True` (`F::And(v) => fold_prop(v, "And", "True", params)`,
            // clean_ground.rs:8526), so that VC's obligation is `core ∨ True` —
            // identically true — while the certificate states `core`. The parent `Or`
            // is `is_path_guard_splice` by round 5's own predicate and so is filtered
            // out of [`locate_violation`]'s domain, leaving nothing that mentions the
            // vacuous disjunct at all. Emitting the empty `And` as its own candidate
            // makes the agreement rule FAIL on it (it is not the core), which is this
            // file's standing verb: a body position no lane can read is an obligation
            // this tier declines, never one it drops.
            //
            // MEASURED 2026-07-31 over `crates/trust-clean/fixtures`, by running
            //     cd crates && RUSTC_BOOTSTRAP=1 \
            //       TRUSTIR_CENSUS_OUT=<path> cargo test --offline -p trust-clean --lib \
            //       -- --ignored --nocapture selection_tests::trustir_corpus_census
            // on this tree and on the same tree with this arm reverted to
            // `if let Some(last)`, then `diff`ing the two per-VC row dumps: funcs=2326,
            // safetyVCs=772, certified=584, gate=238/362 on BOTH, and the 772 rows are
            // byte-identical — 0 certificates withdrawn.
            //
            // CONSEQUENCE FOR THE SPLICE FILTER, and the reason this is the right level
            // to fix it: `violation_candidates` now yields AT LEAST ONE candidate for
            // every input (empty `And` pushes itself; non-empty `And` recurses on a
            // `last` that exists; `Or` and every leaf push themselves). So each `And`
            // disjunct of a path-guard splice is represented by a body position of its
            // own, and dropping the splice `Or` in [`locate_violation`] can no longer
            // silence a disjunct outright. Before this arm, `And([])` was the one
            // formula with zero candidates, which is exactly what made the drop lossy.
            None => out.push(ViolationCandidate { node: f, siblings }),
        },
        F::Or(v) => {
            out.push(ViolationCandidate { node: f, siblings });
            for d in v {
                if matches!(d, F::And(_)) {
                    violation_candidates(d, None, out);
                }
            }
        }
        other => out.push(ViolationCandidate { node: other, siblings }),
    }
}

/// The base place name of a versioned VC variable — `_6#s3_0` names the same place as
/// `_6`. The staleness machinery stamps `#token` suffixes on defs and body reads
/// (`version_rename_at` / `version_block_def_at_establish`), so a comparison against a
/// term freshly lowered from the MIR (which carries bare names) must be on the base.
///
/// Trust: deliberately a LOCAL twin of `mirsem::vc_faithful::base_var_name`, which is
/// private to that module; this file is the trust-ir relocation of that tier and
/// already keeps its own `formula_var_name` for the same reason.
fn base_var_name(f: &trust_types::Formula) -> Option<&str> {
    let n = formula_var_name(f)?;
    Some(n.split('#').next().unwrap_or(n))
}

/// Structural equality of two `Formula`s that ignores the `#token` version stamps the
/// staleness machinery puts on place variables (`_6#s3_0` and `_6` name the same
/// place). Used to compare a conjunct of the WRAPPED, version-renamed VC formula
/// against a term freshly lowered from the MIR.
///
/// Trust: the local twin of `mirsem::vc_faithful::formula_agrees_modulo_versions`
/// (same reason as [`base_var_name`]).
fn formula_agrees_modulo_versions(a: &trust_types::Formula, b: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    match (a, b) {
        (F::Var(x, sx), F::Var(y, sy)) => {
            sx == sy && x.as_str().split('#').next() == y.as_str().split('#').next()
        }
        (F::And(u), F::And(v)) | (F::Or(u), F::Or(v)) => {
            u.len() == v.len()
                && u.iter().zip(v).all(|(x, y)| formula_agrees_modulo_versions(x, y))
        }
        (F::Not(x), F::Not(y)) | (F::Neg(x), F::Neg(y)) => formula_agrees_modulo_versions(x, y),
        (F::Implies(x1, x2), F::Implies(y1, y2))
        | (F::Eq(x1, x2), F::Eq(y1, y2))
        | (F::Lt(x1, x2), F::Lt(y1, y2))
        | (F::Le(x1, x2), F::Le(y1, y2))
        | (F::Gt(x1, x2), F::Gt(y1, y2))
        | (F::Ge(x1, x2), F::Ge(y1, y2))
        | (F::Add(x1, x2), F::Add(y1, y2))
        | (F::Sub(x1, x2), F::Sub(y1, y2))
        | (F::Mul(x1, x2), F::Mul(y1, y2))
        | (F::Div(x1, x2), F::Div(y1, y2))
        | (F::Rem(x1, x2), F::Rem(y1, y2)) => {
            formula_agrees_modulo_versions(x1, y1) && formula_agrees_modulo_versions(x2, y2)
        }
        // Every other shape (literals, bitvector terms, selects, calls, …) carries no
        // version stamp of its own; exact equality is the right test.
        _ => a == b,
    }
}

/// The comparison the assert's condition local named `want` is DEFINED by in THIS
/// function's MIR, lowered exactly as the VC emitter lowers it.
///
/// Requires, all of them, or `None`:
///   * a block whose terminator is an `expected == false` `Assert` on the local named
///     `want` — the only lowering that makes a bare `Var(_c)` the obligation body
///     (`v2_assert_failure_formula` emits `Not(Var _c)` for `expected == true`, a shape
///     [`violation_candidates_resolved`] does not admit at all),
///   * exactly ONE statement in THAT block assigning it (the region
///     `extract_block_definitions_until` reads; SSA, so a second assignment means the
///     name does not identify a unique definition), and
///   * that statement being the `_c := (x == k)` comparison the `expected == false`
///     `DivisionByZero` / `RemainderByZero` / `OverflowNeg` lowering emits, lowered
///     through the emitter's OWN `trust_vcgen::operand_to_formula`.
///
/// Two asserts on the same local in different blocks are admitted only if they resolve
/// to the SAME comparison; otherwise the VC's own assert is ambiguous ⇒ fail closed.
///
/// Trust: the local twin of `mirsem::vc_faithful::mir_assert_condition_core` (same
/// reason as [`base_var_name`]).
fn mir_assert_condition_core(
    func: &trust_types::VerifiableFunction,
    want: &str,
) -> Option<trust_types::Formula> {
    use trust_types::{BinOp, Formula as F, Operand, Rvalue, Statement, Terminator};
    let names = |p: &trust_types::Place| trust_vcgen::place_to_var_name(func, p) == want;
    let mut found: Vec<F> = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Assert { cond, expected: false, .. } = &block.terminator else {
            continue;
        };
        let (Operand::Copy(p) | Operand::Move(p)) = cond else { continue };
        if !names(p) {
            continue;
        }
        let mut defs = block.stmts.iter().filter_map(|s| match s {
            Statement::Assign { place, rvalue, .. } if names(place) => Some(rvalue),
            _ => None,
        });
        let Some(rvalue) = defs.next() else { return None }; // asserted, never defined
        if defs.next().is_some() {
            return None; // two definitions in the assert's own block ⇒ fail closed
        }
        let Rvalue::BinaryOp(BinOp::Eq, a, b) = rvalue else { return None };
        found.push(F::Eq(
            Box::new(trust_vcgen::operand_to_formula(func, a)),
            Box::new(trust_vcgen::operand_to_formula(func, b)),
        ));
    }
    let first = found.first()?.clone();
    found.iter().all(|f| *f == first).then_some(first)
}

/// The `(variable name, MIR type)` of the operand the ASSERT-NEGATION emitter takes as
/// its subject in THIS function — the consumer-side twin of
/// `v2_find_target_neg_operand` (`block_defs.rs:881-895`), which is what
/// `v2_build_assert_negation_vc` reads at `checked_vcs.rs:65` and whose
/// `crate::operand_ty` at `checked_vcs.rs:69` becomes `VcKind::NegationOverflow { ty }`.
///
/// For every block whose terminator is an `expected == false`
/// `Assert { msg: AssertMessage::OverflowNeg, target, .. }` — the sole call site of that
/// producer (`safety.rs:177-178`) and the only assert polarity whose body is the bare
/// `Var(_c)` this lane resolves — take the FIRST `Rvalue::UnaryOp(UnOp::Neg, operand)`
/// statement of `target`, exactly as `v2_find_target_neg_operand`'s `find_map` does.
/// Collapse to the single `(name, ty)` they all agree on.
///
/// `None` — fail closed — when there is no such assert, when its target block has no
/// negation (in which case the emitter itself returns `None` at `checked_vcs.rs:65` and
/// `safety.rs:179-189` emits a `v2_recognized_assert_proof_gap_vc` instead, so no
/// `NegationOverflow` VC of this lane exists), when the negated operand is not a place,
/// or when two such asserts disagree.
fn assert_negation_subject(
    func: &trust_types::VerifiableFunction,
) -> Option<(String, trust_types::Ty)> {
    use trust_types::{AssertMessage, Operand, Rvalue, Statement, Terminator, UnOp};
    let mut found: Option<(String, trust_types::Ty)> = None;
    for block in &func.body.blocks {
        let Terminator::Assert { expected: false, msg: AssertMessage::OverflowNeg, target, .. } =
            &block.terminator
        else {
            continue;
        };
        let target_block = func.body.blocks.get(target.0)?;
        let operand = target_block.stmts.iter().find_map(|stmt| {
            let Statement::Assign { rvalue, .. } = stmt else { return None };
            match rvalue {
                Rvalue::UnaryOp(UnOp::Neg, operand) => Some(operand),
                _ => None,
            }
        })?;
        let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
        let entry =
            (trust_vcgen::place_to_var_name(func, p), trust_vcgen::operand_ty(func, operand)?);
        match &found {
            Some(prev) if *prev != entry => return None, // ambiguous ⇒ fail closed
            _ => found = Some(entry),
        }
    }
    found
}

/// EVERY `(variable name, MIR type)` this function's MIR offers as a NEGATION-FAMILY
/// SUBJECT, over all THREE `VcKind::NegationOverflow` producers:
///   * `v2_build_negation_raw_vc` and `v2_build_assert_negation_vc` — the operand of a
///     `Rvalue::UnaryOp(UnOp::Neg, ..)` statement (the second reads it through
///     `v2_find_target_neg_operand`, block_defs.rs:881-895, which is a `find_map` over
///     one target block's statements; taking every `Neg` in the body is the superset of
///     that and cannot exclude the one it picks);
///   * `signed_abs_panic_body` (unwrap_panic.rs:138-151) — the FIRST argument of an
///     opaque `iN::abs` call, which has no `Neg` in the MIR at all.
/// The type is the emitter's OWN `crate::operand_ty` of that operand — the same read
/// `checked_vcs.rs:69` and `unwrap_panic.rs:140` turn into `VcKind::NegationOverflow
/// { ty }`.
///
/// A non-place operand (a negated CONSTANT) contributes nothing: it has no variable
/// name to authenticate, and its emitted core is `Eq(Int k, MIN)`, which the caller
/// declines earlier for having no `Var`.
///
/// Trust: KEY THE GATE ON THE SUBJECT, NOT ON THE ROUTE (2026-07-31, round-5 defects
/// [1]/[8]). Round 4 added [`assert_negation_subject`] and keyed it on
/// `via_condition_local` — the ROUTE the core was located by. That closed the
/// emitter-driven forgery and left the API-driven one open: a hand-built
/// `And([input_range_constraint(x, 32, true), Eq(x, -2147483648)])` under
/// `VcKind::NegationOverflow { ty: i32 }` arrives with `siblings: Some(..)` and a range
/// sibling on `x`, so it takes the DIRECT route, the route-keyed gate never runs, and
/// `negOverflowsI32 x` is minted for a function whose MIR negates an unrelated `y` —
/// exactly the certificate round 4 says it closed. The subject check now runs on EVERY
/// route (the caller keeps the assert-route check as well: that one pins the subject to
/// the assert's OWN target block, which this whole-body union deliberately does not).
fn negation_subjects(func: &trust_types::VerifiableFunction) -> Vec<(String, trust_types::Ty)> {
    use trust_types::{Operand, Rvalue, Statement, Terminator, UnOp};
    let mut out: Vec<(String, trust_types::Ty)> = Vec::new();
    let mut push = |op: &Operand| {
        let (Operand::Copy(p) | Operand::Move(p)) = op else { return };
        let Some(ty) = trust_vcgen::operand_ty(func, op) else { return };
        let entry = (trust_vcgen::place_to_var_name(func, p), ty);
        if !out.contains(&entry) {
            out.push(entry);
        }
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::UnaryOp(UnOp::Neg, operand), .. } = stmt {
                push(operand);
            }
        }
        if let Terminator::Call { func: callee, args, .. } = &block.terminator
            && is_signed_abs_callee(callee)
            && let Some(arg) = args.first()
        {
            push(arg);
        }
    }
    out
}

/// Whether `callee` is the std signed `iN::abs` whose panic-at-`iN::MIN`
/// `signed_abs_panic_body` models as a `NegationOverflow` — the consumer-side twin of
/// `unwrap_panic::is_signed_abs_call` (unwrap_panic.rs:123-126), which is
/// `pub(super)` inside `trust-vcgen` and so cannot be called from here. Kept a twin
/// for the same reason [`base_var_name`] is one.
///
/// A DIVERGENCE FROM THE ORIGINAL IS NOT SYMMETRIC, so it is worth naming which way it
/// cuts: this predicate only ADMITS a subject that the MIR itself passes to a call of
/// this shape. Too NARROW and a legitimate `abs` row loses its certificate
/// (over-rejection — 5 of the corpus's 12 certified negation rows are `abs` calls, so
/// the corpus census would catch it immediately); too WIDE and the admissible set grows
/// by the first argument of another `core::num`/`std::num` call in the SAME function —
/// never by an arbitrary variable.
fn is_signed_abs_callee(callee: &str) -> bool {
    callee_method_tail(callee) == "abs"
        && (callee.contains("core::num::") || callee.contains("std::num::"))
}

/// The method-name tail of a callee path, turbofishes stripped — a verbatim twin of
/// `trust_vcgen::generate::alloc_bounds::method_tail` (alloc_bounds.rs:162-202), which
/// is `pub(crate)` there. See [`is_signed_abs_callee`] for why an exact copy matters
/// and which way a drift would cut.
fn callee_method_tail(callee: &str) -> &str {
    let mut base = callee.trim();
    while base.ends_with('>') {
        let bytes = base.as_bytes();
        let mut depth = 0i32;
        let mut open = None;
        for (i, &b) in bytes.iter().enumerate().rev() {
            match b {
                b'>' => depth += 1,
                b'<' => {
                    depth -= 1;
                    if depth == 0 {
                        open = Some(i);
                        break;
                    }
                }
                _ => {}
            }
        }
        match open {
            Some(i) => base = base[..i].trim_end_matches(':'),
            None => break, // unbalanced `<…>` — avoid an infinite loop
        }
    }
    let tail = base.rsplit("::").next().unwrap_or(base);
    tail.split('<').next().unwrap_or(tail).trim()
}

/// The candidate set for `formula`, with the ASSERT-CONDITION indirection resolved
/// against the MIR `func` the emitter itself read.
///
/// `v2_assert_failure_formula` (overflow_vc.rs:1834) makes the body of an
/// assert-driven VC the bare condition local — `Var(_c)` when the assert expects
/// `false`, `Not(Var(_c))` when it expects `true` — and `v2_formula_with_block_defs`
/// conjoins that local's own definition `Eq(Var(_c), <core>)` as a hypothesis. The
/// core is therefore genuinely inside a block-def for this family (the
/// precondition-guarded `abs`: `_6 = (x == i32::MIN); assert!(!_6)`).
///
/// SIBLING ANCHORING IS NECESSARY BUT NOT SUFFICIENT. `combine_relevant_block_defs`
/// conjoins the defs and the body into ONE `And` (`conjuncts.push(formula)`,
/// block_defs.rs:696), and the only wrapper that can come between them FLATTENS rather
/// than nests (`v2_formula_with_path_guards`, safety.rs:1110-1115) — so the definition
/// of the condition local is always a conjunct of the SAME `And` whose last element is
/// the `Var(_c)` body. Measured over the 2326 committed fixture functions: of the 40
/// condition-local body occurrences in the corpus's safety VCs, 40 have their
/// definition as a direct sibling and 0 are reachable only by a wider walk — so the
/// anchoring costs nothing and deletes the residual whole-formula scan.
///
/// Trust: A DIRECT SIBLING IS NOT A BLOCK-DEF (2026-07-29, lane-B finding [1]). This
/// function used to accept ANY direct sibling `Eq(Var(_c), rhs)` as "the definition",
/// on the argument that only a block-def can sit there. That argument is FALSE.
/// `combine_relevant_block_defs` returns the body BARE when the block has no def
/// (`if keep_rev.is_empty() { return formula; }`, block_defs.rs:693-695), and
/// `versioned::conjoin` (versioned.rs:62-68) then makes every PRECONDITION a direct
/// sibling of that bare `Var(_c)` body. MEASURED through the real
/// `trust_vcgen::generate_vcs`: `bb0 = Assert { cond: ok, expected: false, msg:
/// OverflowNeg }`, `bb1 = _0 = Neg(k)` with `k: i32`, and
/// `#[requires] ok == (other == i32::MIN)` emitted `And([Eq(ok, Eq(other, -2147483648)),
/// Var(ok, Bool)])` and certified `NegOverflow(W32)` — for an operand the body never
/// negates. The width cross-check is no defense: the forger picks the matching literal.
///
/// So the located binding is now CONFIRMED against the MIR
/// ([`mir_assert_condition_core`]): the function must carry an `expected == false`
/// `Assert` on this local in a block that DEFINES it with exactly one statement, that
/// statement must be the `_c := (x == k)` comparison, and the sibling binding must BE
/// that definition — operand for operand through the emitter's own
/// `trust_vcgen::operand_to_formula`, modulo the `#token` version stamps
/// `version_block_def_at_establish` adds. A `#[requires]`/`#[ensures]` cannot
/// manufacture a body statement, so the contract surface is closed rather than merely
/// outnumbered. This is the same standard `mirsem::vc_faithful::assert_condition_binding`
/// applies on the MirSem lane.
///
/// COST: zero. Measured over the same 2326 fixture functions — 37 safety VCs carry a
/// `Var(_, Bool)` body, 40 occurrences in all; 40 have a single direct-sibling binding,
/// the MIR defines the asserted local for 40 of 40, and the sibling binding agrees with
/// that definition modulo version stamps in 40 of 40. Certified rows and the function
/// gate are unchanged (584 and 238 of 362), with 0 of the 772 per-VC verdicts differing.
///
/// The scan it replaces recursed into `Not`, into every `Or` disjunct and into both
/// sides of `Implies`, and accepted ANY `Eq(Var(name), rhs)` occurrence as "the
/// definition". That is the very defect this file's header describes, one level down:
/// a NEGATED equation `Not(Eq(_6, Eq(z,0)))` is not what `_6` means, yet it supplied
/// the certified core (demonstrated by the reviewer on the post-fix tree, and pinned
/// by `selection_tests::only_a_direct_positive_sibling_conjunct_can_define_the_certified_core`).
///
/// POLARITY. Only the `expected == false` spelling — a BARE `Var(_c)` body, whose
/// violation IS the definition's right-hand side — is resolved. For `Not(Var(_c))`
/// the violation is `Not(rhs)`, so handing `rhs` to a shape matcher would certify the
/// COMPLEMENT of what the VC states. No modeled kind's shape currently matches an
/// `expected == true` condition (rustc spells those `Lt(index, len)` / `Ne(d, 0)`,
/// which the `Ge` / `Eq(_, 0)` matchers reject), so refusing the negative polarity
/// outright costs nothing today and closes the hazard permanently. The definition
/// side is now held to the same rule: only a positive, direct `Eq(Var(_c), rhs)`
/// CONJUNCT counts, so a negated or disjoined occurrence contributes nothing.
///
/// SORT. The body occurrence must be a `Sort::Bool` variable — an assert condition
/// local is boolean by construction (`v2_assert_failure_formula`), and an integer
/// `Var` body is not a condition indirection at all. 0 of the corpus's 40
/// occurrences are non-`Bool`, so this too costs nothing.
fn violation_candidates_resolved<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
) -> Vec<ViolationCandidate<'a>> {
    // Trust: THE MIXED `Or` DECLINES FOR EVERY LANE (2026-07-31, round-5 defect [7]).
    // `violation_candidates` descends only the `And` disjuncts of an `Or`, so a BARE
    // disjunct — the shape an empty-guard path pushes (`terms.push(formula.clone())`,
    // safety.rs:1078-1080) — contributes NO occurrence at all. Round 4 closed that for
    // the arithmetic lane only, by declining there; the bounds, shift and div/rem lanes
    // kept certifying off the guarded twin while a body position they never examined sat
    // in the same formula. A dropped body position is a body position no side condition
    // and no ambiguity collapse can see, so the decline belongs at the PRODUCER, where
    // every lane inherits it. MEASURED over the 2326 committed fixture functions
    // (`selection_tests::trustir_corpus_census`, 2026-07-31): 0 of the 772 emitted safety
    // VCs contain a mixed `Or` anywhere, so this withdraws no row of that corpus —
    // certified 584 and gate 238-of-362 before and after, 0 of the 772 per-VC verdicts
    // differing. The shape IS emitter-reachable (see [`violation_candidates`]); this is a
    // corpus fact, not an impossibility claim.
    if contains_mixed_or(formula) {
        return Vec::new();
    }
    let mut cands = Vec::new();
    violation_candidates(formula, None, &mut cands);

    // Trust: A RESOLVED CONDITION LOCAL REPLACES ITS BODY OCCURRENCE (2026-07-31,
    // round-5 defect [6]). The resolved core used to be APPENDED, leaving the `Var(_c)`
    // body in the candidate list for the consumers to drop on a shape mismatch. Dropping
    // is the wrong verb everywhere in this file: a body position that no lane recognizes
    // is an obligation this tier cannot read, and the tier must decline rather than
    // certify off a different occurrence. Replacing means an UNRESOLVED `Var(_c)` stays
    // in the list, matches no `is_core`, and so fails [`locate_violation`]'s agreement
    // rule instead of vanishing from it.
    cands
        .into_iter()
        .map(|c| resolved_condition_local(func, &c).unwrap_or(c))
        .collect()
}

/// The assert-condition indirection resolved for ONE candidate: if `c` is a `Var(_c,
/// Bool)` body whose MIR-confirmed defining comparison is a direct sibling conjunct,
/// the candidate for that comparison; `None` when `c` is not that shape or the
/// resolution fails (in which case the caller keeps `c` itself, so the unread body
/// position still counts against the locator).
///
/// See [`violation_candidates_resolved`] for why each clause is required.
fn resolved_condition_local<'a>(
    func: &trust_types::VerifiableFunction,
    c: &ViolationCandidate<'a>,
) -> Option<ViolationCandidate<'a>> {
    use trust_types::Formula as F;
    // The body names the condition local POSITIVELY (`Var(_c)`, never `Not(Var(_c))` —
    // that shape is not a candidate at all) and as a BOOLEAN.
    let F::Var(name, trust_types::Sort::Bool) = c.node else { return None };
    // Its definition must be a DIRECT conjunct of the same `And`.
    let sibs = c.siblings?;
    // … and the MIR must actually DEFINE it, at the assert this body came from.
    // No such definition ⇒ the assert-condition route does not exist for this VC
    // and every sibling `Eq(Var(_c), …)` is a hypothesis ⇒ fail closed.
    let base = base_var_name(c.node)?;
    let mir_core = mir_assert_condition_core(func, base)?;
    let defs: Vec<&'a trust_types::Formula> = sibs
        .iter()
        .filter_map(|s| match s {
            F::Eq(l, r) if matches!(&**l, F::Var(n, _) if n == name) => Some(&**r),
            _ => None,
        })
        .collect();
    let first = defs.first().copied()?;
    // One binding, and it must BE the MIR's own definition.
    (defs.iter().all(|d| *d == first) && formula_agrees_modulo_versions(first, &mir_core))
        .then_some(ViolationCandidate { node: first, siblings: None })
}

/// A located violation together with EVERY body-position occurrence of it: the
/// conjunct list it was the last element of, or `None` for an occurrence that carries
/// no such list (the whole formula, or an assert-condition core resolved against the
/// MIR). The multi-path guard split repeats the same body once per path, so a side
/// condition read off the siblings (the uadd vacuity check) must hold on ALL of them,
/// not on whichever happens to be first: two paths could in principle conjoin
/// different operand ranges around the same violation.
struct LocatedViolation<'a> {
    node: &'a trust_types::Formula,
    sibling_sets: Vec<Option<&'a [trust_types::Formula]>>,
}

impl<'a> LocatedViolation<'a> {
    /// Whether `pred` holds of EVERY body-position occurrence's sibling list — and
    /// there is at least one occurrence, and none of them lacks a sibling list.
    ///
    /// Trust: FAIL CLOSED ON THE EMPTY SET (2026-07-29, lane-B finding [2]). This used
    /// to be a bare `.all()`, documented as "vacuously true is impossible: the
    /// constructor rejects an empty set". That was FALSE: the constructor rejected an
    /// empty CANDIDATE list but built `sibling_sets` by `filter_map`ping the candidates'
    /// `siblings`, which is empty whenever every candidate carries `None`.
    ///
    /// Trust: AND A RANGELESS OCCURRENCE MUST FAIL, NOT DROP (2026-07-31, round-5
    /// defects [5]/[6]). Making the empty set fail was only half of it: `filter_map`
    /// SILENTLY DISCARDED the `None`-sibling occurrences, so a violation occurring once
    /// with the emitter's operand ranges beside it and once WITHOUT them (the same body
    /// reached through the assert-condition indirection, or as a bare disjunct) had the
    /// second occurrence excluded from the universal instead of failing it — and the
    /// uadd vacuity argument, which is a claim about EVERY path the violation sits on,
    /// passed on the paths that happened to carry evidence. `sibling_sets` now records
    /// EVERY occurrence, `None` included, and an occurrence with no sibling list has no
    /// range evidence and therefore FAILS this universal.
    fn all_siblings(&self, pred: impl Fn(&'a [trust_types::Formula]) -> bool) -> bool {
        !self.sibling_sets.is_empty() && self.sibling_sets.iter().all(|s| s.is_some_and(&pred))
    }
}

/// Whether `f` is a PATH-GUARD `Or` splice rather than a violation: a non-empty `Or`
/// every disjunct of which is an `And`. That is the only shape
/// `v2_formula_with_path_guards` builds when every path carries a guard
/// (safety.rs:1115 + :1121), and no modeled violation has it — the three `Or`-shaped
/// violations this tier knows (`Or([Lt,Gt])` out-of-range, `Or([Lt,Ge])` signed shift,
/// `Or([Lt,Ge])` signed index) have COMPARISON disjuncts. [`violation_candidates`]
/// keeps such an `Or` as a candidate because a violation CAN be an `Or`; this predicate
/// is how [`locate_violation`] tells the splice back out again, so that the splice does
/// not count as a second, disagreeing body position.
///
/// The MIXED `Or` (some `And` disjuncts, some not) is not classified here at all: it is
/// declined outright, for every lane, in [`violation_candidates_resolved`].
///
/// Trust: THIS DROP IS ONLY SAFE BECAUSE EVERY DISJUNCT STILL SPEAKS (2026-07-31,
/// round-6 F4). Removing the splice `Or` from [`locate_violation`]'s domain removes the
/// only node that MENTIONS all of its disjuncts at once, so it is sound only while each
/// disjunct contributes a body position of its own. It did not: an EMPTY `And` disjunct
/// yielded no candidate at all, and `Or([And([core]), And([])])` — identically true,
/// since `clean_ground::ground_prop` folds an empty `And` to `True` — presented the
/// lane's own core as the sole occurrence and minted. `violation_candidates`'s `F::And`
/// arm now emits a candidate for the empty `And`, which restores the invariant this
/// predicate depends on: every formula yields at least one candidate.
fn is_path_guard_splice(f: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    matches!(f, F::Or(v) if !v.is_empty() && v.iter().all(|d| matches!(d, F::And(_))))
}

/// THE ONE LOCATOR every kind's lane goes through: the single proposition this VC's
/// BODY states, together with every body-position occurrence of it.
///
/// `None` — fail closed — unless ALL of:
///   * at least one body-position occurrence exists,
///   * every occurrence that is not a path-guard `Or` splice names the STRUCTURALLY
///     SAME proposition (two different bodies give no principled way to say which one
///     the VC's kind is about),
///   * every one of them really is at the emitter's body position
///     ([`candidate_at_body_position`]), and
///   * that proposition matches the lane's own shape predicate `is_core`.
///
/// Trust: THE AGREEMENT RULE RANGES OVER THE UNFILTERED SET (2026-07-31, round-5
/// defects [5]/[6]/[7]). Each lane used to `filter` the candidates by its own `is_core`
/// and only THEN collapse to a singleton, so a body position the lane did not recognize
/// — an unresolved `Var(_c)` condition local, a different violation on another guarded
/// path — was DROPPED from the set the ambiguity rule ranged over instead of failing
/// it. A universal quantified over a set that the very predicate under test has already
/// pruned proves nothing about what it dropped. `is_core` is now applied to the
/// COLLAPSED node, after every occurrence has had to agree with it.
fn locate_violation<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
    is_core: impl Fn(&'a trust_types::Formula) -> bool,
) -> Option<LocatedViolation<'a>> {
    let occurrences: Vec<ViolationCandidate<'a>> = violation_candidates_resolved(func, formula)
        .into_iter()
        .filter(|c| !is_path_guard_splice(c.node))
        .collect();
    let first = *occurrences.first()?;
    if !occurrences.iter().all(|c| c.node == first.node) {
        return None; // two different body propositions ⇒ ambiguous ⇒ fail closed
    }
    if !occurrences.iter().all(candidate_at_body_position) {
        return None;
    }
    if !is_core(first.node) {
        return None;
    }
    Some(LocatedViolation {
        node: first.node,
        sibling_sets: occurrences.iter().map(|c| c.siblings).collect(),
    })
}

/// Whether a candidate sits at the emitter's BODY position.
///
/// A candidate carrying a sibling list must be the LAST conjunct of it
/// ([`is_body_position`]). One carrying none is either the whole formula — which IS
/// the body — or an assert-condition core resolved by
/// [`violation_candidates_resolved`], which is anchored to the MIR's own definition
/// rather than to a position.
///
/// Trust: A CONSUMER-SIDE CHECK (2026-07-29, lane-B finding [4]). Every candidate
/// [`violation_candidates`] yields with `Some(sibs)` satisfies this by construction, so
/// the check is a no-op today — measured: certified/gate unchanged at 584 / 238-of-362
/// over the 2326-function corpus with it added to the bounds and div/rem locators. It
/// is here because those two locators' own docs name POSITION as their whole
/// discriminator, and a future widening of the producer (re-admitting a non-`And` `Or`
/// disjunct, descending a second wrapper shape) must not be silently accepted by the
/// two lanes that have no emitter pair to fall back on.
fn candidate_at_body_position(c: &ViolationCandidate<'_>) -> bool {
    match c.siblings {
        Some(sibs) => is_body_position(sibs, c.node),
        None => true,
    }
}

/// Trust: SHIFT — the emitted violation, located from `v2_shift_violation_formula`'s
/// verbatim `And([input_range_constraint(n, shift_ty), invalid])` pair
/// (checked_vcs.rs:494) with the SAME shifted-amount term on both sides.
fn emitted_shift_violation<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
) -> Option<&'a trust_types::Formula> {
    let located = locate_violation(func, formula, |n| shift_violation_shape(n).is_some())?;
    let (n, _, _) = shift_violation_shape(located.node)?;
    // The emitter's own `input_range_constraint(n)` must sit beside the violation at
    // EVERY occurrence of it — a universal, not a filter: an occurrence lacking it used
    // to drop out of the located set instead of failing this check (round-5 defect [5]).
    located.all_siblings(|sibs| has_range_sibling(sibs, n)).then_some(located.node)
}

/// The SHAPE of a shift VC's emitted violation, destructured into
/// `(amount, threshold W, is_signed_form)` — exactly the two forms
/// `v2_shift_violation_formula` builds (checked_vcs.rs:537):
///   * unsigned amount — `Ge(n, Int W)`
///   * signed amount   — `Or([Lt(n, Int 0), Ge(n, Int W)])`
/// `None` for anything else (fail-closed).
fn shift_violation_shape(
    invalid: &trust_types::Formula,
) -> Option<(&trust_types::Formula, i128, bool)> {
    use trust_types::Formula as F;
    match invalid {
        F::Ge(n, w) => {
            let F::Int(t) = &**w else { return None };
            Some((&**n, *t, false))
        }
        F::Or(disjuncts) => {
            let [F::Lt(n_lt, zero), F::Ge(n_ge, w)] = disjuncts.as_slice() else { return None };
            if !matches!(&**zero, F::Int(0)) || n_lt != n_ge {
                return None;
            }
            let F::Int(t) = &**w else { return None };
            Some((&**n_ge, *t, true))
        }
        _ => None,
    }
}

/// Trust: ARITHMETIC OVERFLOW/UNDERFLOW — the emitted violation, located from
/// `v2_build_overflow_vc_for_operands`'s verbatim
/// `And([input_range(lhs), input_range(rhs), out_of_range])` triple
/// (overflow_vc.rs:467), with the group's two constrained terms required to be
/// EXACTLY the computed operands inside `out_of_range`.
///
/// THE GROUP IS NOT AN ARITY. The emitter builds `And([range(a), range(b), oor])`,
/// but `v2_formula_with_path_guards` FLATTENS that `And` into the guard conjunction
/// (safety.rs:1110-1115), so on a guarded block with no block-defs and no
/// type-range wrapper the same three conjuncts arrive as `[guard…, range(a),
/// range(b), oor]`. Requiring `Some([ra, rb, last])` therefore declined a violation
/// that IS at the body position — MEASURED: 2 rows over the 2326-function corpus
/// (`arrayvec::ArrayVec::<T, CAP>::retain::process_one`'s two
/// `Or([Lt(g+1,0), Gt(g+1,u64::MAX)])` VCs), located 453 → 455. Anchoring is
/// unchanged: [`is_body_position`] still pins the violation to the LAST conjunct.
///
/// THE RANGE PAIR IS A SIDE CONDITION, NOT A FILTER.
///
/// Trust: A REJECTED OCCURRENCE MUST FAIL, NOT DROP (2026-07-30, round-4 defect [3]).
/// The range-sibling requirement used to sit inside the `filter` that builds `found`.
/// The uadd caller then quantified its vacuity check over `found`'s sibling sets — a
/// universal over a set the very same predicate had already pruned, so an occurrence
/// carrying NO range evidence was EXCLUDED from the universal instead of FAILING it.
/// Demonstrated: `Or([And([g1, urange(a), urange(b), oor]), And([g2, oor])])` certified
/// `uaddOverflowsU8` off the first disjunct alone, and `a = −1, b = 0` satisfies the
/// second path's `Lt(a+b, 0)` half — the certificate was strictly weaker than the
/// emitted obligation. The range pair is no longer part of the filter that builds
/// `found`; it is applied AFTER the collapse, as a universal over every occurrence that
/// SURVIVES that filter — i.e. every body-position occurrence carrying a sibling set. So
/// an occurrence with siblings but NO range evidence now FAILS the side condition instead
/// of being excluded from it.
///
/// Trust: AND SO DOES AN OCCURRENCE CARRYING NO SIBLING SET AT ALL (2026-07-31, round-5
/// defects [5]/[6]). The round-4 text ended "occurrences carrying no sibling set at all
/// are still dropped by the filter" — which is the same defect one notch smaller: an
/// occurrence with no sibling list has NO range evidence whatever, so it is the strongest
/// possible counterexample to the vacuity claim and the weakest possible reason to
/// exclude it. [`locate_violation`] no longer filters on `siblings.is_some()`, and
/// [`LocatedViolation::all_siblings`] fails on a `None`.
///
/// AND THE OCCURRENCE SET MUST BE COMPLETE. `violation_candidates` descends only the
/// `And` disjuncts of an `Or`, so a BARE disjunct — the shape an empty-guard path
/// pushes (`terms.push(formula.clone())`, safety.rs:1078-1080) — contributes no
/// occurrence at all, and the universal above would range over the guarded twins only.
/// The MIXED `Or` that requires is not hypothetical: it is emitter-reachable through an
/// unwind edge (see [`violation_candidates`]'s note and
/// `mirsem::obligation_region_tests::a_mixed_path_guard_or_can_never_supply_a_bounds_core`).
/// The mixed `Or` therefore DECLINES outright rather than this lane reasoning about
/// which half it can see.
///
/// Trust: THAT DECLINE HAS MOVED TO THE PRODUCER (2026-07-31, round-5 defect [7]).
/// Round 4 put the `contains_mixed_or` call HERE, in the arithmetic lane alone. The
/// unexamined body position is not an arithmetic-lane fact: the bounds, shift and
/// div/rem lanes read their certified proposition from the same candidate set and had
/// no such decline, so each of them could certify off a guarded twin while an
/// unexamined bare disjunct stated something else. [`violation_candidates_resolved`]
/// now returns NO candidates for a formula containing a mixed `Or`, so every lane
/// inherits it and this one keeps its property by construction. MEASURED (re-taken
/// 2026-07-31 with `selection_tests::trustir_corpus_census`): 0 of the 772 safety VCs
/// the 2326-function corpus emits contain a mixed `Or` at all, so the decline withdraws
/// nothing there.
fn emitted_arith_violation_located<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
) -> Option<LocatedViolation<'a>> {
    use trust_types::Formula as F;
    fn computed(f: &F) -> Option<(&trust_types::Formula, &trust_types::Formula)> {
        match f {
            // `Or([Lt(a∘b, MIN), Gt(a∘b, MAX)])` — the general out-of-range form.
            F::Or(v) => {
                let [F::Lt(l, lo), F::Gt(r, hi)] = v.as_slice() else { return None };
                if !is_int_literal(lo) || !is_int_literal(hi) || l != r {
                    return None;
                }
                binop_operands(l)
            }
            // `Lt(a−b, Int 0)` — the unsigned-sub underflow-only form.
            F::Lt(l, lo) if is_int_literal(lo) => binop_operands(l),
            _ => None,
        }
    }
    let located = locate_violation(func, formula, |n| computed(n).is_some())?;
    let (a, b) = computed(located.node)?;
    located
        .all_siblings(|sibs| has_range_sibling(sibs, a) && has_range_sibling(sibs, b))
        .then_some(located)
}

/// Whether `f` contains, anywhere, an `Or` with BOTH an `And` disjunct and a non-`And`
/// one — the MIXED path-guard shape [`violation_candidates`] descends only half of.
///
/// Trust: the production twin of the test-only predicate lane A wrote for the same
/// shape (`mirsem::obligation_region_tests::contains_mixed_or`, which that lane's
/// committed `a_mixed_path_guard_or_can_never_supply_a_bounds_core` asserts the emitter
/// really produces for a `Drop` with a `Cleanup` unwind edge).
fn contains_mixed_or(f: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    let here = matches!(f, F::Or(v)
        if v.iter().any(|d| matches!(d, F::And(_)))
            && v.iter().any(|d| !matches!(d, F::And(_))));
    here || match f {
        F::And(v) | F::Or(v) => v.iter().any(contains_mixed_or),
        F::Not(a) => contains_mixed_or(a),
        F::Implies(a, b) => contains_mixed_or(a) || contains_mixed_or(b),
        _ => false,
    }
}

/// [`emitted_arith_violation_located`], keeping only the located node.
fn emitted_arith_violation<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
) -> Option<&'a trust_types::Formula> {
    emitted_arith_violation_located(func, formula).map(|c| c.node)
}

/// Trust: NEGATION OVERFLOW — the emitted violation `Eq(v, Int INT_MIN)`.
/// `v2_build_negation_raw_vc` (checked_vcs.rs:775) builds the verbatim pair
/// `And([input_range_constraint(v, W, true), Eq(v, type_min_formula(W, true))])`;
/// `signed_abs_panic_body` (unwrap_panic.rs:138-151) builds the SAME pair for an
/// `iN::abs` call's argument — the THIRD producer of this kind, whose subject is an
/// opaque `Call` argument rather than a negated operand;
/// `v2_build_assert_negation_vc` (checked_vcs.rs:57) instead makes the body the
/// assert's condition local, whose own definition supplies the same `Eq(v, MIN)` —
/// resolved by [`violation_candidates_resolved`], never by a free scan.
///
/// Returns the located core AND whether any occurrence of it arrived WITHOUT the
/// emitter's own range/violation group beside it (`siblings: None`) — i.e. through the
/// assert-condition indirection, or as the whole formula. It is `true` if ANY occurrence
/// took that route, not only if all did (fail-closed).
///
/// Trust: THAT FLAG NO LONGER KEYS THE SUBJECT CHECK (2026-07-31, round-5 defects
/// [1]/[8]). It used to, on the argument that the direct route is authenticated by the
/// body position — true of the EMITTER, false of a VC handed to this API. The caller now
/// authenticates the subject on every route against [`negation_subjects`] and uses this
/// flag only to additionally demand the STRICTER assert-route read
/// ([`assert_negation_subject`]), which pins the subject to that assert's own target
/// block.
fn emitted_neg_violation<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
) -> Option<(&'a trust_types::Formula, bool)> {
    use trust_types::Formula as F;
    let is_core = |f: &F| {
        matches!(f, F::Eq(l, r) if formula_var_name(l).is_some() && matches!(&**r, F::Int(_)))
    };
    let located = locate_violation(func, formula, is_core)?;
    let F::Eq(v, _) = located.node else { return None };
    // The raw lane must sit in the emitter's own range/violation group over the SAME
    // negated operand (arity unfixed — see `emitted_arith_violation_located`); the
    // assert lane reaches the core through the condition local's MIR-confirmed
    // definition and carries no group, so it has no range sibling to require.
    //
    // Trust: A GROUPLESS OCCURRENCE FAILS, IT DOES NOT DROP (2026-07-31, round-5
    // defect [5]). This used to be a `filter`: an occurrence WITH siblings but without
    // the emitter's range constraint was silently removed from the located set, and the
    // certificate was read off whichever occurrences remained. Now it fails the lane.
    if !located
        .sibling_sets
        .iter()
        .all(|s| s.is_none_or(|sibs| has_range_sibling(sibs, v)))
    {
        return None;
    }
    let indirect = located.sibling_sets.iter().any(Option::is_none);
    Some((located.node, indirect))
}

/// Trust: BOUNDS — the emitted violation. `v2_build_bounds_assert_vc`
/// (checked_vcs.rs:244) emits it BARE, as `Ge(index, len)` for an unsigned index or
/// `Or([Lt(index, 0), Ge(index, len)])` for a signed one, so no emitter pair exists
/// and POSITION is the whole discriminator: the located node must be one the VC
/// BODY can occupy. A precondition / guard / type-bound `Ge(a,b)` — which the old
/// pre-order scan certified in its place — is not on that path. That discriminator is
/// now asserted HERE, by [`candidate_at_body_position`], and not left to the producer.
///
/// THE SIGNED-INDEX FORM IS DECLINED, NOT HALF-CERTIFIED. `idxOob len i` models
/// `i ≥ len` only, so grounding the `Ge` disjunct of `Or([Lt(i,0), Ge(i,len)])` mints
/// a certificate that is silent about the `i < 0` half the VC also states. That is a
/// certificate about a proposition other than the VC's violation — the same defect
/// class as certifying a hypothesis, one disjunct smaller. Since
/// [`violation_candidates`] no longer descends into non-`And` `Or` disjuncts, the
/// bare `Ge` half is not a candidate; and the `Or` itself is now RECOGNIZED, with its
/// signedness, by [`bounds_violation_shape`], so the caller declines it BY NAME rather
/// than by failing a `Ge`-only matcher (round-5 defect [4] — the right verdict was
/// being reached as if the shape were not a bounds violation at all).
/// MEASURED: 0 of the corpus's 33 certified
/// bounds rows came from that position, so closing it withdrew nothing; modeling the
/// signed form properly needs an `idxOobSigned` spec, which is a capability gap, not
/// a selection bug. The UNSIGNED `Or`-free form — every bounds row the corpus
/// actually certifies — is unaffected.
fn emitted_bounds_violation<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
) -> Option<(&'a trust_types::Formula, bool)> {
    let located = locate_violation(func, formula, |n| bounds_violation_shape(n).is_some())?;
    let (_, _, signed) = bounds_violation_shape(located.node)?;
    Some((located.node, signed))
}

/// The SHAPE of a bounds VC's emitted violation, destructured into
/// `(index, len, is_signed_form)` — exactly the two forms `v2_build_bounds_assert_vc`
/// builds (checked_vcs.rs:244):
///   * unsigned index — `Ge(i, len)`
///   * signed index   — `Or([Lt(i, Int 0), Ge(i, len)])`
/// `None` for anything else (fail-closed).
///
/// Trust: THE SIGNEDNESS IS PART OF THE SHAPE (2026-07-31, round-5 defect [4]). The
/// signed form used to be turned away by a `Ge`-only matcher — the right VERDICT
/// (`idxOob` models `i ≥ len` and says nothing about the `i < 0` half, so certifying it
/// would be a certificate about a strictly smaller proposition than the VC states), but
/// reached as a shape MISMATCH, indistinguishable in the decline message from "this is
/// not a bounds violation at all". Recognising the signed form and naming the gap makes
/// the decline the deliberate statement it is: `IrSafetyVcKind::Bounds { signed }` can
/// only ever be minted at `signed: false`, and the `signed: true` half is a MODELING
/// gap awaiting an `idxOobSigned` spec, not a selection failure. This mirrors
/// [`shift_violation_shape`], which has carried its signedness since the shift lane was
/// written, and the length operand is admitted in the same two spellings as before (a
/// slice-length `Var` or a fixed-array `Int`).
fn bounds_violation_shape(
    f: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula, bool)> {
    use trust_types::Formula as F;
    let ge = |a: &'_ F, b: &'_ F| {
        formula_var_name(a).is_some() && (formula_var_name(b).is_some() || matches!(b, F::Int(_)))
    };
    match f {
        F::Ge(i, len) if ge(i, len) => Some((&**i, &**len, false)),
        F::Or(disjuncts) => {
            let [F::Lt(i_lt, zero), F::Ge(i_ge, len)] = disjuncts.as_slice() else { return None };
            if !matches!(&**zero, F::Int(0)) || i_lt != i_ge || !ge(i_ge, len) {
                return None;
            }
            Some((&**i_ge, &**len, true))
        }
        _ => None,
    }
}

/// Trust: DIV/REM BY ZERO — the emitted violation `Eq(divisor, Int 0)`
/// (`v2_divisor_is_zero_formula`, block_defs.rs:199). Emitted bare, like bounds, so
/// POSITION is the discriminator — asserted HERE by [`candidate_at_body_position`],
/// not left to the producer; a `#[requires] z == 0` on an unrelated variable no
/// longer supplies the certified divisor. The assert-driven twin
/// (`checked_div`/`guarded_div`, whose body is the bare condition local) reaches its
/// core through [`violation_candidates_resolved`], which confirms the binding against
/// the MIR's own defining statement.
fn emitted_divzero_violation<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    let is_core = |f: &F| {
        matches!(f, F::Eq(a, b)
            if formula_var_name(a).is_some() && matches!(&**b, F::Int(0)))
    };
    locate_violation(func, formula, is_core).map(|c| c.node)
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

/// Trust: WIDTH CROSS-CHECK (defense in depth, the analogue of the shift lane's
/// signedness cross-check against `shift_ty`). The certified width is recovered from
/// the EMITTED THRESHOLD — deliberately, because `operand_ty` fabricates `i64` for a
/// signed constant operand and would mis-key the spec. That makes the threshold a
/// SINGLE POINT OF FAILURE: if the located node is not this VC's violation, its
/// threshold silently names the wrong width and nothing contradicts it. So the
/// recovered width must ALSO be a width this VC's own `operand_tys` mentions.
///
/// It is "mentions", not "both equal", precisely because of the fabricated-`i64`
/// constant: `int_op_type` (type_ranges.rs:540) recovers `(width, signed)` from the
/// NON-CONSTANT operand, so `100i8 + x` legitimately emits the `i8` thresholds under
/// `operand_tys = (i64, i8)`. That is not a hypothetical — MEASURED over the 2326
/// committed fixture functions, 41 of the 207 certified arithmetic rows have only ONE
/// of their two operand types at the emitted width (`bump_i32`, `accum`,
/// `bounded_iter`, the `mass-harvest` int-pred dumps, …), so requiring agreement with
/// BOTH would withdraw 41 legitimate certificates. Requiring agreement with at least
/// one withdraws none and still kills the measured forgeries — itoa's `u8::write`
/// minted `UAddOverflow(W64)` under `operand_tys = (u8, u8)`, a width neither operand
/// type mentions.
///
/// MEASURED cost: 0 of 207.
fn arith_width_agrees_with_kind(kind: &trust_types::VcKind, bits: u32) -> bool {
    let trust_types::VcKind::ArithmeticOverflow { operand_tys: (a, b), .. } = kind else {
        return false;
    };
    a.int_width() == Some(bits) || b.int_width() == Some(bits)
}

/// Trust: MIXED-WIDTH NARROWING MUST BE JUSTIFIED (2026-07-31, round-5 defect [2]).
/// [`arith_width_agrees_with_kind`] accepts a width EITHER of the VC's two operand types
/// mentions, because `operand_ty` fabricates `i64` for an untyped integer constant and
/// `int_op_type` (type_ranges.rs:540) recovers the real `(width, signed)` from the
/// NON-constant operand — so `100i8 + x` legitimately emits `i8` thresholds under
/// `operand_tys = (i64, i8)`. But "either" is a DISJUNCTION over two unrelated widths,
/// and when the two differ it lets the certified width be whichever one the located
/// threshold happens to name: kind `(i8, i64)` certifies at 8 and kind `(i64, i8)` at 64,
/// for the same body, with two bare `Var` operands and nothing in the VC narrowing
/// anything. The lane-A twin of this hole is
/// `mirsem::vc_faithful`'s `min(wa, wb)`, closed there the same way.
///
/// So when the widths differ, require BOTH:
///   * the certified width to be the NARROWER of the two — the width the emitter's own
///     `int_op_type` would have recovered; and
///   * the WIDER position to be an integer LITERAL in the located core — the constant
///     that justifies the narrowing in the first place.
///
/// The position mapping is the emitter's own, and it was RE-READ in this tree rather
/// than carried over: both producers that build the LIA `Or([Lt(a∘b, MIN), Gt(a∘b,
/// MAX)])` core take `operand_tys` and the computed `Add/Sub/Mul` from the SAME
/// `(lhs, rhs)` pair in the SAME order —
///   * `generate/overflow_vc.rs:428-434` builds `result` from `lhs_f`/`rhs_f`, `:467`
///     is `And([lhs_range, rhs_range, out_of_range])`, and `:499` is
///     `VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) }`;
///   * `generate/panic_calls.rs:929-951` does the same for the
///     `unchecked_{add,sub,mul}` call path and returns `(body, op, lhs_ty, rhs_ty)`,
///     which `generate/safety.rs:292` puts into `operand_tys: (lhs_ty, rhs_ty)`.
/// If some FUTURE producer paired them the other way round
/// this would look at the wrong position and REFUSE — over-rejection, never
/// over-acceptance, since equal widths short-circuit to `true` and only the
/// differing-width branch can return `false`.
///
/// EQUAL widths return `true` unconditionally: there is nothing to justify, and this must
/// not become a second, silent same-width restriction.
///
/// COST, MEASURED IN THIS TREE (2026-07-31,
/// `selection_tests::trustir_corpus_census` over `crates/trust-clean/fixtures`): **zero**.
/// 51 of the 772 emitted safety VCs are `ArithmeticOverflow` with DIFFERING kind widths;
/// 43 of them locate a violation at all, and in 43 of 43 the wider position holds an
/// integer literal. The other 8 decline upstream of this check. Certified 584 and gate
/// 238-of-362 before and after, with an EMPTY row-by-row diff.
fn mixed_width_narrowing_is_justified(
    kind: &trust_types::VcKind,
    bits: u32,
    a_op: &trust_types::Formula,
    b_op: &trust_types::Formula,
) -> bool {
    use trust_types::{Formula as F, Ty, VcKind as K};
    let K::ArithmeticOverflow { operand_tys: (a_ty, b_ty), .. } = kind else {
        return false; // not this kind ⇒ the caller has no business here (fail closed)
    };
    let (Ty::Int { width: wa, .. }, Ty::Int { width: wb, .. }) = (a_ty, b_ty) else {
        return false;
    };
    if wa == wb {
        return true; // nothing was narrowed; the width cross-check has real content already
    }
    let wider = if wa > wb { a_op } else { b_op };
    bits == *wa.min(wb) && matches!(wider, F::Int(_) | F::UInt(_))
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
    /// Array/slice index out of bounds (kind 2), at the emitted violation's own index
    /// SIGNEDNESS. Only `signed: false` is mintable: `idxOob` models `len ≤ i` alone,
    /// so the signed form's `i < 0` disjunct has no spec and the lane declines rather
    /// than certifying half of it — see [`bounds_violation_shape`]. The field exists so
    /// that gap is a stated variant rather than a shape mismatch.
    Bounds { signed: bool },
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
///
/// `func` must be the function this VC was EMITTED FROM. It is not consulted for the
/// obligation — the certified core still comes out of `vc.formula` — but the
/// assert-condition indirection is confirmed against its MIR
/// ([`violation_candidates_resolved`]), which is the only thing that distinguishes the
/// emitter's own block definition of a condition local from a `#[requires]` that binds
/// the same name.
fn trustir_safety_vc_adequate_kind(
    func: &trust_types::VerifiableFunction,
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
            let Some((leaf, signed_index)) = emitted_bounds_violation(func, &vc.formula) else {
                return declined(
                    "bounds VC: this VC's OWN emitted `Ge(index, len)` violation could not be \
                     located unambiguously",
                );
            };
            if signed_index {
                // The KIND GAP, stated as one (round-5 defect [4]): the emitted
                // violation is `Or([Lt(i,0), Ge(i,len)])` and `idxOob` models the `Ge`
                // disjunct alone, so a certificate here would be about a strictly
                // smaller proposition than the VC's own body. Closing it needs an
                // `idxOobSigned` spec, not a change to this selection.
                return declined(
                    "bounds VC: the emitted violation is the SIGNED `Or([Lt(i,0), Ge(i,len)])` \
                     form, whose `i < 0` disjunct this tier has no spec for — declined \
                     rather than half-certified",
                );
            }
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
                Some(IrSafetyVcKind::Bounds { signed: false }),
                live_ground_def_eq_spec_ir(leaf, &params, &spec, binder_count),
            )
        }
        // DIV / REM by zero (kinds 3/8): the emitted core is `Eq(b, 0)`. Live-ground
        // → `@Eq Int b (Int.ofNat 0)`; spec `divByZero b` / `remByZero b`.
        K::DivisionByZero | K::RemainderByZero => {
            let Some(leaf) = emitted_divzero_violation(func, &vc.formula) else {
                return declined(
                    "div/rem VC: this VC's OWN emitted `Eq(divisor, 0)` violation could not be \
                     located unambiguously",
                );
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
            let Some(invalid) = emitted_shift_violation(func, &vc.formula) else {
                return declined(
                    "shift VC: this VC's OWN emitted `And([input_range(n), invalid(n)])` \
                     violation could not be located unambiguously",
                );
            };
            // Destructure the emitter's own construction (`shift_violation_shape` is
            // what located it, so the re-match succeeds), and require the located
            // form's SIGNEDNESS to agree with `shift_ty` — a disagreement means the VC
            // and its own kind describe different obligations, so the tier fails closed
            // rather than picking one.
            let Some((n_f, threshold, located_signed)) = shift_violation_shape(invalid) else {
                return declined("shift VC: located violation is not a modeled shift shape");
            };
            if located_signed != amount_signed {
                return declined(
                    "shift VC: the emitted violation's signedness disagrees with `shift_ty`",
                );
            }
            // The EMITTED threshold W must be a modeled shift-width literal
            // (`8/16/32/64/128` — the 128-bit value widths ARE in this lane's set).
            //
            // Trust: NO WIDTH CROSS-CHECK HERE — A DELIBERATE, MEASURED DEFERRAL
            // (2026-07-31, round-5 defect [3]; the matched twin of the note at the same
            // place in `mirsem::vc_faithful`'s shift arm, which has carried it since
            // round 4 while THIS lane carried the same omission UNDOCUMENTED). The four
            // other width-from-formula arms all cross-check the recovered width against
            // the VC's own kind. This one does not, because the kind's width is not
            // evidence about the certified width IN EITHER DIRECTION: for a CONSTANT
            // shifted value (`1i32 << bit`) the extractor fabricates `i64` in
            // `operand_ty`, so the kind's width and the emitted threshold disagree on
            // REAL rows.
            //
            // MEASURED IN THIS TREE, 2026-07-31, over all of `crates/trust-clean/fixtures`
            // (2326 functions), by `selection_tests::trustir_corpus_census`:
            //
            //   cd crates && RUSTC_BOOTSTRAP=1 cargo test --offline \
            //     -p trust-clean --lib -- --ignored --nocapture \
            //     selection_tests::trustir_corpus_census
            //
            // 133 shift VCs, every one of which locates a `shift_violation_shape`; the
            // `(operand_ty width, emitted threshold)` pairs, exhaustively:
            //
            //   agree:    (8,8) 5   (16,16) 13   (32,32) 41   (64,64) 49   (128,128) 13
            //   disagree: (64,8) 3  (64,16) 3    (64,32) 3    (64,128) 3
            //
            // i.e. 12 of 133 disagree, and NOT ONE-SIDEDLY: 9 rows are KIND-WIDER (64
            // against 8/16/32) and 3 are KIND-NARROWER (64 against 128 — the i128
            // `BitField::get_bit`/`set_bit` rows). So no one-sided comparison is
            // available: `kind_w >= threshold` drops the 3 i128 rows, `kind_w <=
            // threshold` drops the other 9, and equality drops all 12 — contradicting
            // `selection_tests::bit_field_get_bit_certifies_its_own_shift_width_under_a_
            // ge_spelled_precondition`, which pins the EMITTED threshold as the honest
            // one. (Which rows these are was NOT re-measured here; only the pair census
            // above was.)
            //
            // WHAT IS AND IS NOT CLAIMED. Not "the kind and the formula agree" — they
            // measurably do not on 12 rows. The claim is that `operand_ty` is not
            // evidence about the certified width here, so no SOUND comparison against it
            // exists; closing the gap needs the EMITTER to record the true shifted width
            // in the `VcKind`, a trust-vcgen change deliberately not attempted from the
            // consumer side. Until then the certified width comes from the emitted
            // threshold and the position-selected body alone, and the kind cross-check
            // this arm CAN make is SIGNEDNESS, which it makes immediately above.
            let Some(w) = u32::try_from(threshold).ok().and_then(IrShiftWidth::from_bits) else {
                return declined("shift VC: emitted threshold is not a modeled width");
            };
            // Trust: M6 rung 6 — the CLOSED-LITERAL amount arm (unsigned only, exactly
            // mirroring the mirsem-side gate: a literal SIGNED amount has no observed
            // real-MIR `Or` core at a literal, so it stays declined rather than guessed).
            if let F::Int(k) = n_f {
                if amount_signed {
                    return declined("shift VC: literal-amount signed shift — outside the arm");
                }
                let spec = Expr::app(cst(&shift_amount_oob_ir_name(w, amount_signed)), int_lit(*k));
                return (
                    Some(IrSafetyVcKind::ShiftOob(w, amount_signed)),
                    live_ground_def_eq_spec_ir(invalid, &HashMap::new(), &spec, 0),
                );
            }
            let Some(n_name) = formula_var_name(n_f) else {
                return declined("shift VC: amount operand is not a Var");
            };
            let params = debruijn_params(&[n_name]);
            // The core to ground is the located violation ITSELF — the unsigned
            // `Ge(n,W)` or the full signed `Or([n<0, n≥W])`, whichever the emitter
            // built. No second scan: a separate search for the `Or` was another
            // whole-formula walk, and so another way to read the certificate off a
            // hypothesis.
            let spec = Expr::app(cst(&shift_amount_oob_ir_name(w, amount_signed)), Expr::bvar(0));
            (
                Some(IrSafetyVcKind::ShiftOob(w, amount_signed)),
                live_ground_def_eq_spec_ir(invalid, &params, &spec, 1),
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
                    // The emitter's own out-of-range core is
                    // `Or([Lt(a+b, Int 0), Gt(a+b, Int MAX)])` and the certificate
                    // below grounds only the `Gt` disjunct — see the PARTIAL-ADEQUACY
                    // guard beneath, which turns "the `Lt` half is vacuous" from a
                    // comment into a checked side condition. The disjunct is taken
                    // FROM the located `Or`, never from a second walk of the formula.
                    let Some(cand) = emitted_arith_violation_located(func, &vc.formula) else {
                        return declined(
                            "uadd VC: this VC's OWN emitted `And([range(a), range(b), \
                             out_of_range])` violation could not be located unambiguously",
                        );
                    };
                    let F::Or(disjuncts) = cand.node else {
                        return declined("uadd VC: emitted violation is not the `Or` range form");
                    };
                    let [F::Lt(under_t, zero_f), leaf @ F::Gt(..)] = disjuncts.as_slice() else {
                        return declined("uadd VC: no `Gt(a+b, MAX)` disjunct in the violation");
                    };
                    let F::Gt(add_t, max_f) = leaf else { unreachable!("guarded by the finder") };
                    let Some((a_op, b_op)) = binop_operands(add_t) else {
                        return declined("uadd VC: operands outside the formula-aware fragment");
                    };
                    // PARTIAL ADEQUACY, MADE A CHECK. The located violation is a
                    // two-disjunct `Or`; the kernel certificate covers the `Gt` half
                    // only. That is sound EXACTLY WHEN the discarded half is
                    // unsatisfiable under the conjuncts the emitter puts beside it —
                    // `Lt(a+b, 0)` with `0 ≤ a` and `0 ≤ b` conjoined. Both facts are
                    // now REQUIRED rather than argued: the discarded disjunct must be
                    // `Lt(<the same a+b>, 0)`, and each operand must carry an
                    // `input_range_constraint` SIBLING whose lower bound is literally
                    // `0` — at EVERY body position the violation occupies, not just
                    // the first: the multi-path guard split repeats the same violation
                    // once per path with each path's own conjuncts, so a first-
                    // occurrence check would pass on a formula whose second path drops
                    // the lower bound. (MEASURED: all 120 located uadd `Or` cores in
                    // the 2326-function corpus satisfy both facts on every path, so the
                    // check costs no row — but an emitter change that stops emitting
                    // the unsigned lower bound now fails closed instead of silently
                    // certifying half a proposition.) The signed-index BOUNDS lane is
                    // the other member of this pattern and is closed the other way, by
                    // declining — see `emitted_bounds_violation`.
                    //
                    // Trust: THE UNIVERSAL IS ONLY AS GOOD AS ITS DOMAIN (2026-07-30,
                    // round-4 defect [3]). `all_siblings` below is a universal over the
                    // occurrences `emitted_arith_violation_located` collected, and that
                    // collection used to PRE-FILTER on the weaker `has_range_sibling`
                    // form of the same predicate — so an occurrence with no range
                    // evidence dropped out of the domain instead of failing the
                    // quantifier, and the quantifier passed on the survivors.
                    // `Or([And([g1, urange(a), urange(b), oor]), And([g2, oor])])`
                    // certified `uaddOverflowsU8` with `a = −1, b = 0` refuting it on
                    // the second path. Both halves of the domain are now the locator's
                    // responsibility and are documented there: it no longer prunes on
                    // the range pair, and it declines on a mixed `Or`, whose bare
                    // disjunct `violation_candidates` cannot see at all.
                    if under_t != add_t || !is_zero_literal(zero_f) {
                        return declined(
                            "uadd VC: the discarded `Lt(a+b, 0)` disjunct is not over the \
                             same computed sum, so the `Gt`-only certificate would cover \
                             less than the emitted violation",
                        );
                    }
                    if !cand.all_siblings(|sibs| {
                        has_nonneg_range_sibling(sibs, a_op)
                            && has_nonneg_range_sibling(sibs, b_op)
                    }) {
                        return declined(
                            "uadd VC: the operand ranges do not pin both operands to `≥ 0`, \
                             so the discarded `Lt(a+b, 0)` disjunct is not provably vacuous",
                        );
                    }
                    let F::Int(max) = &**max_f else {
                        return declined("uadd VC: emitted threshold is not an `Int` literal");
                    };
                    let Some(w) = uwidth_of_unsigned_max(*max) else {
                        return declined("uadd VC: emitted threshold is not a modeled 2^W−1");
                    };
                    if !arith_width_agrees_with_kind(&vc.kind, w.bits()) {
                        return declined(
                            "uadd VC: the width recovered from the emitted threshold is not a \
                             width this VC's own `operand_tys` mentions",
                        );
                    }
                    if !mixed_width_narrowing_is_justified(&vc.kind, w.bits(), a_op, b_op) {
                        return declined(
                            "uadd VC: this VC's operand types have DIFFERENT widths and the \
                             certified width is not the narrower one justified by a literal in \
                             the wider position",
                        );
                    }
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
                    let Some(or) = emitted_arith_violation(func, &vc.formula) else {
                        return declined(
                            "signed overflow VC: this VC's OWN emitted `And([range(a), \
                             range(b), Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])])` violation could not be \
                             located unambiguously (a var*var BV mul stays honestly deferred)",
                        );
                    };
                    let F::Or(v) = or else {
                        return declined("signed overflow VC: emitted violation is not the `Or` form");
                    };
                    let [F::Lt(under_t, min_f), F::Gt(over_t, max_f)] = v.as_slice() else {
                        return declined("signed overflow VC: unexpected disjunct shape");
                    };
                    // Both disjuncts must reference the SAME computed `a∘b` operands.
                    let Some((a_op, b_op)) = binop_operands(under_t) else {
                        return declined("signed overflow VC: operands outside the fragment");
                    };
                    if binop_operands(over_t) != Some((a_op, b_op)) {
                        return declined("signed overflow VC: disjunct operand mismatch");
                    }
                    let (F::Int(min), F::Int(max)) = (&**min_f, &**max_f) else {
                        return declined(
                            "signed overflow VC: emitted (MIN,MAX) are not `Int` literals",
                        );
                    };
                    let Some(w) = swidth_of_signed_bounds(*min, *max) else {
                        return declined(
                            "signed overflow VC: emitted (MIN,MAX) match no modeled width",
                        );
                    };
                    if !arith_width_agrees_with_kind(&vc.kind, w.bits()) {
                        return declined(
                            "signed overflow VC: the width recovered from the emitted (MIN,MAX) \
                             is not a width this VC's own `operand_tys` mentions",
                        );
                    }
                    if !mixed_width_narrowing_is_justified(&vc.kind, w.bits(), a_op, b_op) {
                        return declined(
                            "signed overflow VC: this VC's operand types have DIFFERENT widths \
                             and the certified width is not the narrower one justified by a \
                             literal in the wider position",
                        );
                    }
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
                    let Some(leaf) = emitted_arith_violation(func, &vc.formula) else {
                        return declined(
                            "usub VC: this VC's OWN emitted `And([range(a), range(b), \
                             Lt(a−b, 0)])` violation could not be located unambiguously",
                        );
                    };
                    let F::Lt(sub_t, zero) = leaf else {
                        return declined("usub VC: emitted violation is not the `Lt(a−b, 0)` form");
                    };
                    if !matches!(&**sub_t, F::Sub(_, _)) || !matches!(&**zero, F::Int(0)) {
                        return declined("usub VC: emitted violation is not the `Lt(a−b, 0)` form");
                    }
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
        // formula. The raw lane sits in the emitter's own `And([range(x), Eq(x,MIN)])`
        // pair; the ASSERT lane (`abs`) makes the body the assert's condition local
        // and the core is that local's OWN definition — reached through the emitter's
        // construction, not through a scan that would equally have accepted a
        // constant-assignment block-def `Eq(k, -128)` and certified `NegOverflow(W8)`
        // for an `i32` negation (MEASURED before this fix).
        K::NegationOverflow { ty } => {
            let Some((leaf, via_condition_local)) = emitted_neg_violation(func, &vc.formula) else {
                return declined(
                    "negation VC: this VC's OWN emitted `Eq(x, MIN)` violation could not be \
                     located unambiguously",
                );
            };
            let F::Eq(x_f, min_f) = leaf else { unreachable!("guarded by the finder") };
            let Some(x_name) = base_var_name(x_f) else {
                return declined("negation VC: negated operand is not a Var");
            };
            let F::Int(min) = &**min_f else { unreachable!("guarded by the finder") };
            let Some(w) = swidth_of_signed_min(*min) else {
                return declined("negation VC: emitted threshold is not a modeled −2^(W−1)");
            };
            // ON THE ASSERT-CONDITION ROUTE, THE CERTIFIED VARIABLE MUST BE THE ONE THE
            // EMITTER NEGATED.
            //
            // Trust: SUBJECT AUTHENTICATION (2026-07-30, round-4 defect [2]). The two
            // checks that existed authenticated the OTHER two coordinates and were then
            // never brought into contact with the subject:
            // [`violation_candidates_resolved`] authenticates WHICH COMPARISON the body's
            // condition local is bound to, and the width cross-check below authenticates
            // the emitted threshold against `vc.kind`'s stored `ty`. Neither asks what
            // the located `Eq(x, MIN)` is ABOUT. So a dominating
            // `assert!(!(x == i32::MIN))` over a negation of an UNRELATED `y` located a
            // genuine, MIR-confirmed comparison — on `x` — and certified
            // `negOverflowsI32 x`, while `y`, the operand actually negated, appeared
            // nowhere in the VC formula or in the certified proposition. The width
            // cross-check could not see it: `vc.kind`'s `ty` is `operand_ty` of `y`
            // (`checked_vcs.rs:69`), the threshold is `x`'s literal, and a forger picks
            // them equal. Narrowing `x` to `i8` still minted a 32-bit certificate about
            // an `i8` — a type that cannot hold −2³¹ — because NEITHER SIDE of that
            // width comparison describes `x`: the left is `y`'s type and the right is
            // the literal the forger wrote into `x`'s comparison.
            //
            // The subject is now recovered from the MIR ([`assert_negation_subject`],
            // the consumer-side twin of `v2_find_target_neg_operand`), and on this route
            // the width is checked against THE CERTIFIED VARIABLE'S OWN TYPE as well as
            // against `vc.kind`'s.
            //
            // Trust: THE GATE IS NOW KEYED ON THE SUBJECT, NOT ON THE ROUTE
            // (2026-07-31, round-5 defects [1]/[8]). What round 4 wrote below this line
            // ran only when `via_condition_local`, on the argument that the DIRECT route
            // is authenticated by the body position: the `abs` and raw-`Neg` producers
            // both emit the violation inside their own
            // `And([input_range_constraint(v, W, true), Eq(v, MIN)])` pair
            // (unwrap_panic.rs:146-149 and checked_vcs.rs:828-833), so their core sits
            // at the body position over that pair's own subject. That argument is sound
            // about the EMITTER and says nothing about a VC handed to this API directly:
            // a hand-built formula of exactly that shape over an unrelated `x` takes the
            // direct route, and the route-keyed gate never runs. Keying on the route
            // authenticated the WAY THE CORE WAS FOUND; the defect is about WHAT THE
            // CERTIFICATE IS ABOUT, so the subject is now cross-checked on EVERY route,
            // against [`negation_subjects`] — the union of what all three producers can
            // take as a subject — and the width is read off THE CERTIFIED VARIABLE'S OWN
            // `operand_ty`, never off `vc.kind`'s `ty` (which describes whatever local
            // the emitter was called about) and never off the threshold alone (which the
            // forger writes).
            //
            // The `abs` producer is why this is a UNION and not `v2_find_target_neg_operand`
            // alone: `signed_abs_panic_body` (unwrap_panic.rs:138-151, routed at
            // :1382-1387) models `iN::abs`'s panic at `iN::MIN` as this kind with no
            // `Rvalue::UnaryOp(UnOp::Neg, ..)` in the MIR at all, and requiring one
            // unconditionally withdrew 5 of the corpus's 12 certified negation rows
            // (MEASURED, round 4: `mass-harvest-2026-07-17/int-preds`, e.g. `w_i8_abs`,
            // whose whole body is `_0 = core::num::<impl i8>::abs(x)`).
            let subjects = negation_subjects(func);
            let Some((_, subject_ty)) = subjects.iter().find(|(n, _)| n == x_name) else {
                return declined(
                    "negation VC: the certified variable is not a subject this function's MIR \
                     negates or passes to `iN::abs`, so the certificate would be about a \
                     variable no negation of this function is over",
                );
            };
            if !subject_ty.is_signed() || subject_ty.int_width() != Some(w.bits()) {
                return declined(
                    "negation VC: the width recovered from the emitted `INT_MIN` threshold is \
                     not the width of the CERTIFIED VARIABLE's own type",
                );
            }
            // AND ON THE ASSERT-CONDITION ROUTE, THE STRICTER READ IS ALSO REQUIRED: the
            // subject must be the operand THAT ASSERT'S OWN TARGET BLOCK negates, which
            // the whole-body union above deliberately does not pin (a function with two
            // negations offers both names to the union). Kept alongside, not replaced by,
            // the subject check: this one is the exact consumer-side twin of
            // `v2_find_target_neg_operand`, the read the emitter itself performed.
            if via_condition_local {
                let Some((subject, subject_ty)) = assert_negation_subject(func) else {
                    return declined(
                        "negation VC: the assert-condition route's negated subject could not \
                         be recovered unambiguously from the MIR",
                    );
                };
                if subject != x_name {
                    return declined(
                        "negation VC: the certified variable is not the operand the assert's \
                         own target block negates, so the certificate would be about a \
                         different subject",
                    );
                }
                if !subject_ty.is_signed() || subject_ty.int_width() != Some(w.bits()) {
                    return declined(
                        "negation VC: the width recovered from the emitted `INT_MIN` \
                         threshold is not the width of the CERTIFIED VARIABLE's own type",
                    );
                }
            }
            // WIDTH CROSS-CHECK (defense in depth). A disagreement between the emitted
            // `INT_MIN` threshold and the VC's own stored `ty` means the located
            // `Eq(x, MIN)` is not this VC's violation: the pre-fix tier minted
            // `NegOverflow(W8)` for an `i32` negation off an `Eq(k, -128)` hypothesis,
            // and the condition-local lane could still reach a lone `Eq(k, -128)`
            // definition. MEASURED cost: 0 — all 12 certified negation rows over the
            // 2326-function corpus already agree.
            //
            // Trust: WHAT MAKES THEM AGREE IS NOT UNIFORM (2026-07-30). The round-3
            // text here said "BOTH negation emitters take the `INT_MIN` literal from
            // `ty.int_width()` itself (checked_vcs.rs:788/73)". That is right for TWO of
            // the three producers and WRONG for the one it names second:
            //   * `v2_build_negation_raw_vc` — `let width = ty.int_width()?`
            //     (checked_vcs.rs:788) feeding `type_min_formula(width, true)` at :829.
            //     BY CONSTRUCTION.
            //   * `signed_abs_panic_body` — `let Ty::Int { width, signed: true } = ty`
            //     (unwrap_panic.rs:141) feeding the same call at :145. BY CONSTRUCTION.
            //   * `v2_build_assert_negation_vc` — NOT by construction. Its `let width =
            //     ty.int_width()?` at checked_vcs.rs:73 is consumed only by the
            //     `width >= 128` BV branch (:82-118); the modeled-width path returns
            //     `v2_assert_failure_formula(func, cond, expected)` (:120-130), whose
            //     threshold is whatever CONSTANT THE MIR'S OWN COMPARISON carries,
            //     reached through the condition local's block definition. There the
            //     agreement is a property of the lowering, not of the emitter — so on
            //     that route this is a real check rather than a tautology.
            // It is KEPT alongside the subject check above rather than replaced by it:
            // this one compares the threshold to the VC's own stored type, that one
            // compares it to the negated operand's type, and on the assert route those
            // are two different reads of the MIR.
            if ty.int_width() != Some(w.bits()) {
                return declined(
                    "negation VC: the width recovered from the emitted `INT_MIN` threshold \
                     disagrees with the VC kind's own negated type",
                );
            }
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
///
/// `func` must be the function `vc` was emitted from — see
/// [`trustir_safety_vc_adequate_kind`] for what it is used for and why the VC alone is
/// not enough.
#[must_use]
pub fn trustir_safety_vc_adequate(
    func: &trust_types::VerifiableFunction,
    vc: &trust_types::VerificationCondition,
) -> RefinementVerdict {
    trustir_safety_vc_adequate_kind(func, vc).1
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
        .all(|vc| matches!(trustir_safety_vc_adequate(func, vc), RefinementVerdict::ProvenModulo3))
}

// ===========================================================================
// Tests
// ===========================================================================

// Trust: EMITTER-ANCHORED VIOLATION SELECTION (2026-07-29) — the per-kind
// regression pins for the false-certificate lane this file used to carry.
#[cfg(test)]
#[path = "trustir_safety_selection_tests.rs"]
mod selection_tests;

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
            let (_, verdict_s) = trustir_safety_vc_adequate_kind(&func_u, &signed_vc);
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
        trustir_safety_vc_adequate_kind(func, vc)
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
        // `signed: false` is the only mintable half — the signed `Or([Lt(i,0),
        // Ge(i,len)])` form declines for want of an `idxOobSigned` spec.
        assert_eq!(kind, Some(IrSafetyVcKind::Bounds { signed: false }));
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
        let core =
            emitted_arith_violation(&func, &vc.formula).expect("the emitted violation exists");
        let F::Or(disjuncts) = core else { panic!("the u32-add core is the `Or` range form") };
        let leaf = &disjuncts[1];
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
        let verdict = trustir_safety_vc_adequate(&binop_func(BinOp::Add, 32, false), &vc);
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
            matches!(
                trustir_safety_vc_adequate(&binop_func(BinOp::Add, 32, false), &cast_vc),
                RefinementVerdict::KernelRejected(_)
            ),
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
