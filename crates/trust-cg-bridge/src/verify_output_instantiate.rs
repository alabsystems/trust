// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! B4 — the O(1) structured-instantiation [PROVED] path for the live gate.
//!
//! Reflects the gate's REAL `(machine_out, auto)` Formulas (built by the gate's
//! own `symbolic_machine_output` / `trust_ir_semantics`) — PURELY STRUCTURALLY,
//! NON-FOLDING — into clean-kernel `Clean.BVC.BvF` terms, then discharges
//! `bvfEval(reflect machine_out) = bvfEval(reflect auto)` by the clean KERNEL
//! `check_type` of a `bvfEval`-headed proof composed from the coercion lemmas
//! (`bvf_add_cong` / `bvf_or_cong2` / `bvf_zext_cong` / `bvf_extract_cong1` /
//! `bvf_or_zero_id` / `bvf_extract_zeroext_id`). All proved by `Eq.subst`, empty
//! domain-axiom closure; see clean `bitvec_coercion`.
//!
//! # Fail-safe invariant (the spine of B4)
//!
//! This path is STRICTLY ADDITIVE. [`try_o1_instantiation_discharge`] returns
//! `Some(theorem)` ONLY when the clean kernel `check_type` SUCCEEDS; on ANY
//! non-match, reflection error, or kernel rejection it returns `None`, and the
//! caller FALLS THROUGH to the existing slow SAT-reflection path (unchanged).
//! A bug in the reflection/matcher can only cause fall-through (lose speed),
//! NEVER a false [PROVED] — the kernel `check_type` is the sole authority, and
//! the obligation it is checked against is the REAL reflected Formula (not a
//! synthetic term the matcher builds). Moreover the divergence (SAT) check
//! (`discharge_equal_pre`) runs BEFORE this path and is the sole gate for
//! Refuted, so a divergent obligation never reaches here.
//!
//! Only the `add@N` fragment (Leaf/Const/Add/ZeroExt/ExtractLow/Or, the ops the
//! gate emits for integer add) is recognized; everything else returns `None`.

#![cfg(feature = "kernel-recheck")]

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, Level, TypeChecker};
use std::fmt;
use std::sync::{Condvar, LazyLock, Mutex};
use trust_types::{Formula, Sort};

/// Stack for the kernel `check_type` of the discharge (deep `bvfEval` reduction
/// over 32/64-bit `List Bool` literals) — mirror the slow path's big stack.
use clean_auto::proved_gate::RECHECK_STACK_BYTES;

/// Kernel reduction needs a 256 MiB native stack. The Rust test harness and
/// parallel bridge callers used to reserve one such stack per proof without a
/// bound, so `spawn` could fail under contention and silently downgrade a
/// valid proof to [VALIDATED]. Four workers cap the bridge's stack reservation
/// at 1 GiB while retaining useful parallelism.
const MAX_CONCURRENT_RECHECK_THREADS: usize = 4;

static RECHECK_THREAD_PERMITS: LazyLock<(Mutex<usize>, Condvar)> =
    LazyLock::new(|| (Mutex::new(0), Condvar::new()));

struct RecheckThreadPermit;

impl RecheckThreadPermit {
    fn acquire() -> Self {
        let (active, available) = &*RECHECK_THREAD_PERMITS;
        let mut active = active.lock().unwrap_or_else(|poison| poison.into_inner());
        while *active >= MAX_CONCURRENT_RECHECK_THREADS {
            active = available.wait(active).unwrap_or_else(|poison| poison.into_inner());
        }
        *active += 1;
        Self
    }
}

impl Drop for RecheckThreadPermit {
    fn drop(&mut self) {
        let (active, available) = &*RECHECK_THREAD_PERMITS;
        let mut active = active.lock().unwrap_or_else(|poison| poison.into_inner());
        debug_assert!(*active > 0);
        *active = active.saturating_sub(1);
        available.notify_one();
    }
}

#[derive(Debug)]
pub(crate) enum RecheckThreadError {
    Spawn(std::io::Error),
    Panicked,
}

impl fmt::Display for RecheckThreadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Spawn(error) => write!(f, "failed to spawn kernel re-check thread: {error}"),
            Self::Panicked => f.write_str("kernel re-check thread panicked"),
        }
    }
}

/// Run one kernel proof check on the shared bounded large-stack pool.
pub(crate) fn run_recheck_thread<T, F>(name: &str, check: F) -> Result<T, RecheckThreadError>
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    let _permit = RecheckThreadPermit::acquire();
    std::thread::Builder::new()
        .stack_size(RECHECK_STACK_BYTES)
        .name(name.to_string())
        .spawn(check)
        .map_err(RecheckThreadError::Spawn)?
        .join()
        .map_err(|_| RecheckThreadError::Panicked)
}

/// The slow bit-blast certificate lane shares the same stack permits as the
/// O(1) instantiation lane. Calling clean-auto's convenience wrapper directly
/// would create an uncoordinated 256 MiB stack and reintroduce the resource
/// race this module is responsible for preventing.
pub(crate) fn kernel_recheck_proved_grade_bounded(
    proof: &ay_proof::BvBlastProof,
) -> clean_auto::proved_gate::GateRecheck {
    use clean_auto::proved_gate::{GateRecheck, kernel_recheck_proved_grade};

    let proof = proof.clone();
    match run_recheck_thread("trust-mpos-kernel-recheck", move || {
        let mut env = Environment::with_prelude();
        if let Err(error) = env.init_resolution_soundness() {
            return GateRecheck::Rejected {
                reason: format!("init_resolution_soundness failed: {error:?}"),
            };
        }
        kernel_recheck_proved_grade(&env, &proof)
    }) {
        Ok(outcome) => outcome,
        Err(error) => GateRecheck::Rejected { reason: error.to_string() },
    }
}

/// clean-kernel `Expr` helpers (mirror the `Clean.BVC.*` ctor names).
pub(crate) mod kx {
    use super::{Expr, Level, Name};
    pub fn nat_lit(n: u32) -> Expr {
        let mut a = Expr::const_str("Nat.zero");
        for _ in 0..n {
            a = Expr::app(Expr::const_str("Nat.succ"), a);
        }
        a
    }
    pub fn bool_ty() -> Expr {
        Expr::const_str("Bool")
    }
    pub fn list_bool() -> Expr {
        Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), bool_ty())
    }
    pub fn nil() -> Expr {
        Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), bool_ty())
    }
    pub fn cons(h: Expr, t: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [bool_ty(), h, t],
        )
    }
    pub fn bits(value: i128, width: u32) -> Expr {
        let mut acc = nil();
        for k in (0..width).rev() {
            let b = if ((value >> k) & 1) == 1 {
                Expr::const_str("Bool.true")
            } else {
                Expr::const_str("Bool.false")
            };
            acc = cons(b, acc);
        }
        acc
    }
    pub fn leaf(l: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.BvF.Leaf"), l)
    }
    pub fn const_(l: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.BvF.Const"), l)
    }
    pub fn add(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.Add"), [a, b])
    }
    pub fn sub(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.Sub"), [a, b])
    }
    pub fn and(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.And"), [a, b])
    }
    pub fn xor(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.Xor"), [a, b])
    }
    pub fn zext(e: Expr, k: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.ZeroExt"), [e, k])
    }
    pub fn extract(e: Expr, tag: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.ExtractLow"), [e, tag])
    }
    pub fn or(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.Or"), [a, b])
    }
    pub fn mul(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.Mul"), [a, b])
    }
    pub fn div(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.Div"), [a, b])
    }
    pub fn shl(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.Shl"), [a, b])
    }
    pub fn lshr(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.LShr"), [a, b])
    }
    pub fn ashr(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.BvF.AShr"), [a, b])
    }
    pub fn evalf(e: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.bvfEval"), e)
    }
    pub fn all_false(l: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.bvAllFalse"), l)
    }
    pub fn eq_list(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [list_bool(), a, b],
        )
    }
    pub fn eq_refl_list(v: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [list_bool(), v],
        )
    }
    pub fn eq_trans_list(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(Level::zero())]),
            [list_bool(), a, b, c, h1, h2],
        )
    }
    // bvfEval-headed lemma applications.
    pub fn add_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_add_cong"), [a, ap, b, bp, ha, hb])
    }
    pub fn sub_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_sub_cong"), [a, ap, b, bp, ha, hb])
    }
    pub fn and_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_and_cong"), [a, ap, b, bp, ha, hb])
    }
    pub fn xor_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_xor_cong"), [a, ap, b, bp, ha, hb])
    }
    pub fn mul_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_mul_cong"), [a, ap, b, bp, ha, hb])
    }
    pub fn div_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_div_cong"), [a, ap, b, bp, ha, hb])
    }
    pub fn shl_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_shl_cong"), [a, ap, b, bp, ha, hb])
    }
    pub fn lshr_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_lshr_cong"), [a, ap, b, bp, ha, hb])
    }
    pub fn ashr_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_ashr_cong"), [a, ap, b, bp, ha, hb])
    }
    /// `divGuardBridge b z dv h : bvIteVal (bvIsZero b) z dv = dv`, given `h : bvIsZero b = false`.
    /// Collapses the machine div-by-zero guard `Ite(b==0, 0, div)` to its else-branch under `b≠0`.
    pub fn div_guard_bridge(b: Expr, z: Expr, dv: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.divGuardBridge"), [b, z, dv, h])
    }
    pub fn or_cong2(c: Expr, x: Expr, xp: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_or_cong2"), [c, x, xp, h])
    }
    pub fn zext_cong(x: Expr, xp: Expr, k: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_zext_cong"), [x, xp, k, h])
    }
    pub fn extract_cong1(x: Expr, xp: Expr, tag: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_extract_cong1"), [x, xp, tag, h])
    }
    pub fn or_zero_id(e: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.bvf_or_zero_id"), e)
    }
    pub fn add_zero_id(e: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.bvf_add_zero_id"), e)
    }
    pub fn extract_zeroext_id(e: Expr, k: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_extract_zeroext_id"), [e, k])
    }

    // ── EQ-compare value-discharge builders (the predicate substrate) ──────────
    pub fn btrue() -> Expr {
        Expr::const_str("Bool.true")
    }
    pub fn bfalse() -> Expr {
        Expr::const_str("Bool.false")
    }
    /// `bvDiv a b` — the List Bool → List Bool → List Bool unsigned-division VALUE
    /// (distinct from `div`, which builds the `BvF.Div` inductive node).
    pub fn bv_div(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvDiv"), [a, b])
    }
    /// `bvMul a b` — the List Bool → List Bool → List Bool multiply VALUE (for the rem composite).
    pub fn bv_mul(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvMul"), [a, b])
    }
    /// `bvSDiv a b` — the List Bool → List Bool → List Bool SIGNED (sign-magnitude, round-to-zero)
    /// division VALUE; the signed counterpart of `bv_div`.
    pub fn bv_sdiv(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvSDiv"), [a, b])
    }
    /// `Eq.{1} Bool a b` — boolean equality (for the `bvIsZero b = false` hypothesis).
    pub fn eq_bool(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [bool_ty(), a, b],
        )
    }
    pub fn bnot(x: Expr) -> Expr {
        Expr::app(Expr::const_str("Bool.not"), x)
    }
    pub fn bv_beq(xs: Expr, ys: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvBeq"), [xs, ys])
    }
    pub fn bv_ult(xs: Expr, ys: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvUlt"), [xs, ys])
    }
    pub fn bv_ule(xs: Expr, ys: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvULe"), [xs, ys])
    }
    pub fn bv_slt_real(xs: Expr, ys: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvSLtReal"), [xs, ys])
    }
    pub fn bv_sle_real(xs: Expr, ys: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvSLeReal"), [xs, ys])
    }
    pub fn band(x: Expr, y: Expr) -> Expr {
        Expr::apps(Expr::const_str("Bool.and"), [x, y])
    }
    pub fn bxor(x: Expr, y: Expr) -> Expr {
        Expr::apps(Expr::const_str("Bool.xor"), [x, y])
    }
    pub fn last_bit(xs: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.bvLastBit"), xs)
    }
    pub fn bv_is_zero(xs: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.bvIsZero"), xs)
    }
    pub fn bv_not(xs: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.bvNot"), xs)
    }
    pub fn add_rec_m(xs: Expr, ys: Expr, c: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVI.addRecM"), [xs, ys, c])
    }
    pub fn bv_ite_val(p: Expr, vt: Expr, ve: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvIteVal"), [p, vt, ve])
    }
    // ── Memory model (bvSelect/bvStore array + read-over-write keystone) ─────────
    pub fn bv_select(m: Expr, a: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvSelect"), [m, a])
    }
    pub fn bv_store(m: Expr, a: Expr, v: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvStore"), [m, a, v])
    }
    /// `selectStoreSame m a v : bvSelect (bvStore m a v) a = v` — the same-address
    /// read-over-write keystone (the load returns the stored value; `m` never inspected).
    pub fn select_store_same(m: Expr, a: Expr, v: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.selectStoreSame"), [m, a, v])
    }
    /// The abstracted underlying memory: the CLOSED array `fun (_ : List Bool) => List.nil`
    /// of type `List Bool → List Bool`. `selectStoreSame` is parametric over `m` and never
    /// inspects it, so abstracting the ~28-store frame stack as this one closed term is sound
    /// (the load short-circuits at the pointer store, above the frame). No axiom needed.
    pub fn opaque_mem() -> Expr {
        Expr::lam(clean_kernel::expr::BinderInfo::Default, list_bool(), nil())
    }
    pub fn bv_len(xs: Expr) -> Expr {
        Expr::app(Expr::const_str("Clean.BVC.bvLen"), xs)
    }
    pub fn eq_refl_nat(v: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [Expr::const_str("Nat"), v],
        )
    }
    pub fn eq_refl_bool(v: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [Expr::const_str("Bool"), v],
        )
    }
    /// A concrete width-`w` list of FRESH opaque per-bit `Bool` axioms named
    /// `BVC_EQBIT_{tag}_{k}` — makes `bvLen` reduce to `w` concretely (the eq
    /// length guard is then `refl`). Returns the cons-list + the axiom names.
    pub fn opaque_bit_list(tag: &str, w: u32, axioms: &mut Vec<String>) -> Expr {
        let mut acc = nil();
        for k in (0..w).rev() {
            let nm = format!("BVC_EQBIT_{tag}_{k}");
            axioms.push(nm.clone());
            acc = cons(Expr::const_str(&nm), acc);
        }
        acc
    }
}

/// A reflected `Formula`: the structural `BvF`, its wrapper-stripped core, and a
/// kernel proof `Eq (List Bool) (bvfEval bvf) (bvfEval core)`.
pub(crate) struct Reflected {
    pub(crate) bvf: Expr,
    pub(crate) core: Expr,
    pub(crate) proof: Expr,
}

/// Reflect a gate `Formula` (add@N fragment) into a `BvF` Expr + stripped core +
/// the `bvfEval`-headed kernel proof. PURELY STRUCTURAL / NON-FOLDING. Returns
/// `Err` for any node outside the recognized fragment (→ caller falls through).
/// Also returns the set of symbolic leaf names that need a `List Bool` axiom.
pub(crate) fn reflect_formula(
    f: &Formula,
    leaves: &mut Vec<(String, u32)>,
) -> Result<Reflected, String> {
    match f {
        Formula::Var(name, Sort::BitVec(w)) => {
            leaves.push((name.clone(), *w));
            let leaf_list = Expr::const_str(&format!("BVC_LEAF_{name}_{w}"));
            let l = kx::leaf(leaf_list);
            Ok(Reflected { bvf: l.clone(), core: l.clone(), proof: kx::eq_refl_list(kx::evalf(l)) })
        }
        Formula::BitVec { value, width } => {
            let c = kx::const_(kx::bits(*value, *width));
            Ok(Reflected { bvf: c.clone(), core: c.clone(), proof: kx::eq_refl_list(kx::evalf(c)) })
        }
        // MADD identity: `BvAdd(0, x)` (AArch64 `madd Wd,Wn,Wm,WZR` adds the zero
        // register) is `x`. Strip it like `BvOr(0,·)`: core = x.core, proof composes a
        // one-sided add-congruence with `bvf_add_zero_id` (addRecM allFalse · false = ·).
        // This makes the mul machine core (which carries the MADD wrapper) match the IR
        // BvMul core (which doesn't). Mirrors the BvOr(0,·) arm exactly.
        Formula::BvAdd(l, r, _w) if matches!(&**l, Formula::BitVec { value: 0, .. }) => {
            let rx = reflect_formula(r, leaves)?;
            let const_af = kx::const_(kx::all_false(kx::evalf(rx.core.clone())));
            let bvf = kx::add(const_af.clone(), rx.bvf.clone());
            let core = rx.core.clone();
            // step_a : eval(Add af x.bvf) = eval(Add af x.core)  [add_cong, left side refl]
            let refl_af = kx::eq_refl_list(kx::evalf(const_af.clone()));
            let step_a = kx::add_cong(
                const_af.clone(),
                const_af.clone(),
                rx.bvf.clone(),
                rx.core.clone(),
                refl_af,
                rx.proof,
            );
            // step_b : eval(Add (Const allFalse(x.core)) x.core) = eval(x.core)  [bvf_add_zero_id]
            let step_b = kx::add_zero_id(rx.core.clone());
            let proof = kx::eq_trans_list(
                kx::evalf(kx::add(const_af.clone(), rx.bvf.clone())),
                kx::evalf(kx::add(const_af, rx.core.clone())),
                kx::evalf(rx.core.clone()),
                step_a,
                step_b,
            );
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvAdd(l, r, _w) => {
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::add(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::add(rl.core.clone(), rr.core.clone());
            let proof = kx::add_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvSub(l, r, _w) => {
            // SUB — the exact add analogue (traced #40-followup): BvSub core in the
            // same coercion wrappers. bvf_sub_cong is the bvfEval-headed Sub congruence.
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::sub(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::sub(rl.core.clone(), rr.core.clone());
            let proof = kx::sub_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvAnd(l, r, _w) => {
            // AND — exact add analogue (traced #41): native BvAnd(wn0,wn1) (operands
            // ALIGNED, not commuted) in the same coercion wrappers. Pure coercion-id.
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::and(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::and(rl.core.clone(), rr.core.clone());
            let proof = kx::and_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvXor(l, r, _w) => {
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::xor(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::xor(rl.core.clone(), rr.core.clone());
            let proof = kx::xor_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvMul(l, r, _w) => {
            // MUL — exact add analogue (traced #59): the LIR `madd Wd,Wn,Wm,WZR`
            // reflects back to BvMul(wrap(X0),wrap(X1)) (operands ALIGNED), the SAME
            // BvMul primitive the IR auto-spec uses. Pure coercion-identity over the
            // shared BvF.Mul; bvf_mul_cong cancels it by congruence (the multiplier
            // VALUE is not load-bearing — both sides compute the identical bvMul).
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::mul(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::mul(rl.core.clone(), rr.core.clone());
            let proof = kx::mul_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvUDiv(l, r, _w) => {
            // UNSIGNED DIV — the exact mul analogue: the LIR `udiv` reflects to `BvF.Div`
            // over the SAME operand wrappers the IR `BvUDiv` carries; `bvf_div_cong` cancels
            // the shared `BvF.Div` by congruence (the quotient VALUE is not load-bearing —
            // both sides compute the identical `bvDiv`). SIGNED FOOTGUN GUARD: `BvSDiv` is
            // DELIBERATELY NOT reflected (it stays in the `other` Err arm) — SDIV rounds toward
            // zero, which differs from `bvDiv`'s `Nat.div` floor for negatives, so signed div
            // must NEVER reflect to `BvF.Div`; it correctly stays [VALIDATED].
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::div(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::div(rl.core.clone(), rr.core.clone());
            let proof = kx::div_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvShl(l, r, _w) => {
            // SHIFTS — coercion-identity (the mul analogue): machine and IR carry the SAME
            // BvShl over the SAME operands (the amount is BvAnd(b, w-1) on both sides — the
            // BvAnd arm reflects it), differing only in operand coercion wrappers. bvf_shl_cong
            // cancels the shared BvF.Shl by congruence (the shift VALUE is not load-bearing).
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::shl(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::shl(rl.core.clone(), rr.core.clone());
            let proof = kx::shl_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvLShr(l, r, _w) => {
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::lshr(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::lshr(rl.core.clone(), rr.core.clone());
            let proof = kx::lshr_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvAShr(l, r, _w) => {
            let rl = reflect_formula(l, leaves)?;
            let rr = reflect_formula(r, leaves)?;
            let bvf = kx::ashr(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::ashr(rl.core.clone(), rr.core.clone());
            let proof = kx::ashr_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvOr(lhs, rhs, _w) => {
            if let Formula::BitVec { value: 0, .. } = &**lhs {
                let rx = reflect_formula(rhs, leaves)?;
                let const_af = kx::const_(kx::all_false(kx::evalf(rx.core.clone())));
                let bvf = kx::or(const_af.clone(), rx.bvf.clone());
                let core = rx.core.clone();
                let step_a =
                    kx::or_cong2(const_af.clone(), rx.bvf.clone(), rx.core.clone(), rx.proof);
                let step_b = kx::or_zero_id(rx.core.clone());
                let proof = kx::eq_trans_list(
                    kx::evalf(kx::or(const_af.clone(), rx.bvf.clone())),
                    kx::evalf(kx::or(const_af, rx.core.clone())),
                    kx::evalf(rx.core.clone()),
                    step_a,
                    step_b,
                );
                Ok(Reflected { bvf, core, proof })
            } else {
                Err("reflect: BvOr lhs is not BitVec{0} (outside add@N wrapper fragment)".into())
            }
        }
        // MEMORY STORE-LOAD ROUNDTRIP: `Select(Store(M, a, v), a)` — a load at the SAME
        // address as the immediately-covering store returns the stored value `v`, THROUGH
        // any underlying memory. Reflect it as `BvF.Leaf (bvSelect (bvStore M' a' v') a')`
        // whose `bvfEval` (≡ the bvSelect term, since bvfEval(Leaf l) ⟶ l) is bridged to the
        // stored value's core by `selectStoreSame`. M' is the closed `opaque_mem` (the ~28
        // frame stores under the pointer store are never analyzed — selectStoreSame short-
        // circuits). a' / v' are the (bvfEval of the) reflected address / value cores, so the
        // enclosing readout wrappers reflect over this Leaf and the o1 coercion path proves
        // machine == auto once both loads reduce to the shared stored-byte core.
        Formula::Select(mem, load_addr) => {
            if let Formula::Store(_under, store_addr, val) = &**mem {
                if **store_addr == **load_addr {
                    let ra = reflect_formula(load_addr, leaves)?;
                    let rv = reflect_formula(val, leaves)?;
                    let a_list = kx::evalf(ra.core);
                    let v_list = kx::evalf(rv.core.clone());
                    let m = kx::opaque_mem();
                    let sel_term = kx::bv_select(
                        kx::bv_store(m.clone(), a_list.clone(), v_list.clone()),
                        a_list.clone(),
                    );
                    // bvf: Leaf(sel_term); evalf(bvf) ≡ sel_term. core: the stored value's core.
                    // proof: selectStoreSame m a' v' : sel_term = v_list = evalf(core).
                    let bvf = kx::leaf(sel_term);
                    let core = rv.core;
                    let proof = kx::select_store_same(m, a_list, v_list);
                    return Ok(Reflected { bvf, core, proof });
                }
                return Err(
                    "reflect: Select store/load address mismatch (aliasing not in fragment)".into(),
                );
            }
            Err("reflect: Select over non-Store (bare memory read outside fragment)".into())
        }
        Formula::BvExtract { inner, high, low } => {
            if *low != 0 {
                return Err("reflect: BvExtract low != 0 (outside fragment)".into());
            }
            if let Formula::BvZeroExt(z, k) = &**inner {
                let rz = reflect_formula(z, leaves)?;
                let kn = kx::nat_lit(*k);
                let tag = rz.core.clone();
                let zext_bvf = kx::zext(rz.bvf.clone(), kn.clone());
                let zext_core = kx::zext(rz.core.clone(), kn.clone());
                let bvf = kx::extract(zext_bvf.clone(), tag.clone());
                let core = rz.core.clone();
                let inner_eq = kx::zext_cong(rz.bvf.clone(), rz.core.clone(), kn.clone(), rz.proof);
                let step_a =
                    kx::extract_cong1(zext_bvf.clone(), zext_core.clone(), tag.clone(), inner_eq);
                let step_b = kx::extract_zeroext_id(rz.core.clone(), kn);
                let proof = kx::eq_trans_list(
                    kx::evalf(kx::extract(zext_bvf, tag.clone())),
                    kx::evalf(kx::extract(zext_core, tag)),
                    kx::evalf(rz.core.clone()),
                    step_a,
                    step_b,
                );
                let _ = high;
                Ok(Reflected { bvf, core, proof })
            } else {
                // Bare extract of a leaf (operand wn = Extract[w-1:0](Var X)): part
                // of the SHARED core, identical on both sides — core = bvf, refl.
                let ri = reflect_formula(inner, leaves)?;
                let w = high - low + 1;
                let tag = kx::const_(kx::bits(0, w));
                let bvf = kx::extract(ri.bvf.clone(), tag);
                Ok(Reflected {
                    bvf: bvf.clone(),
                    core: bvf.clone(),
                    proof: kx::eq_refl_list(kx::evalf(bvf)),
                })
            }
        }
        other => Err(format!("reflect: Formula outside add@N reflection fragment: {other:?}")),
    }
}

/// True iff `e`'s Debug still carries the wrapper ctors (non-folding check — the
/// kernel, not the Rust reflection, cancels them).
#[cfg(test)]
pub(crate) fn reflection_contains_wrapper(e: &Expr) -> bool {
    let s = format!("{e:?}");
    s.contains("\"Or\"") && s.contains("\"ZeroExt\"") && s.contains("\"ExtractLow\"")
}

/// Build the discharge env: BVC coercion layer + the symbolic-leaf `List Bool`
/// axioms the reflection introduced. NOTE: these per-operand leaf axioms are
/// `List Bool` opaques used ONLY to state the symbolic obligation; they are NOT
/// dependencies of the `Clean.BVC.bvf_*` theorems (whose axiom closure stays
/// empty), so they do not enter the [PROVED] grade's trusted closure.
pub(crate) fn discharge_env(leaves: &[(String, u32)]) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    env.init_bv_coercion().map_err(|e| format!("init_bv_coercion: {e:?}"))?;
    for (name, w) in leaves {
        // idempotent: a repeated (name,w) is fine (add_decl of an existing axiom
        // with the same type is a no-op-or-error we tolerate).
        let _ = env.add_decl(clean_kernel::Declaration::Axiom {
            name: Name::from_string(&format!("BVC_LEAF_{name}_{w}")),
            level_params: vec![],
            type_: kx::list_bool(),
        });
    }
    Ok(env)
}

/// THE B4 O(1) DISCHARGE. Attempt to discharge `machine_out == auto` (an add@N
/// obligation ay already proved equal) by O(1) structured instantiation in the
/// clean kernel. Returns `Some(theorem_label)` iff the kernel `check_type`
/// SUCCEEDS against the REAL reflected obligation; `None` on any non-match,
/// reflection error, or kernel rejection (→ caller falls through to the slow
/// path). Fail-safe: a wrong reflection yields a conclusion that ≠ the real
/// obligation, the kernel rejects, and we return `None` — never a false [PROVED].
#[must_use]
/// Const-eval the constant Ite branches (literal / BvAdd / BvOr folds).
fn eq_const_bv_value(f: &Formula) -> Option<u128> {
    match f {
        Formula::BitVec { value, width } => {
            let w = *width;
            Some(if w >= 128 { *value as u128 } else { (*value as u128) & ((1u128 << w) - 1) })
        }
        Formula::BvAdd(l, r, _) => Some(eq_const_bv_value(l)?.wrapping_add(eq_const_bv_value(r)?)),
        Formula::BvOr(l, r, _) => Some(eq_const_bv_value(l)? | eq_const_bv_value(r)?),
        _ => None,
    }
}

/// `Ite(p, c1, c2)` with `{1,0}`/`{0,1}` constant branches → `(p, then_is_one)`.
fn eq_strip_ite(f: &Formula) -> Option<(&Formula, bool)> {
    if let Formula::Ite(p, t, e) = f {
        match (eq_const_bv_value(t)?, eq_const_bv_value(e)?) {
            (1, 0) => Some((p, true)),
            (0, 1) => Some((p, false)),
            _ => None,
        }
    } else {
        None
    }
}

/// Strip the machine's 32-bit return-register readout. Depending on target
/// optimization, the decoder produces either `Extract[31:0](·)` directly or
/// preserves an identity `Or(0, ·)` beneath the extract.
///
/// Callers immediately require the stripped value to be an `Ite` whose branches
/// are exactly 0 and 1, so accepting the direct form cannot erase arbitrary
/// high-bit semantics: extracting either constant branch yields the same 32-bit
/// branch value.
fn eq_strip_reg_wrapper(f: &Formula) -> Option<&Formula> {
    if let Formula::BvExtract { inner, high: 31, low: 0 } = f {
        if let Formula::BvOr(z, x, _) = &**inner {
            if matches!(&**z, Formula::BitVec { value: 0, .. }) {
                return Some(x);
            }
        }
        return Some(inner);
    }
    None
}

/// THE EQ-COMPARE O(1) DISCHARGE. Recognizes the gate's REAL eq obligation:
///   auto    = Ite(Eq(la, ra), 1@32, 0@32)
///   machine = W( Ite(Not(Eq(BvSub(la',ra',w), 0@w)), 0, 1) )
/// NON-FOLDING: requires the machine to literally carry the Ite/Not/Eq/BvSub flag
/// structure. OPERAND-IDENTITY KERNEL-TIED (the eq#47 fix): the discharge builds the
/// goal from the REAL machine operand keys (`operand_key` peels each operand Formula
/// to its underlying register+width), so matched operands share one per-bit list while
/// DIVERGENT operands (auto X1 vs machine X2) key to distinct lists — the kernel
/// `check_type` then FORCES operand identity and REJECTS a divergent eq. NOT proved at
/// fresh/abstract operands: the kernel, not a Rust pre-check, is the operand-identity
/// authority. (ay has already proved the specific instance equal; here the clean KERNEL
/// re-derives the eq-encoding correctness at the real operands.) On any mismatch ⟹ None.
fn try_eq_value_discharge(machine_out: &Formula, auto: &Formula) -> Option<String> {
    let (auto_pred, auto_then_one) = eq_strip_ite(auto)?;
    if !auto_then_one {
        return None;
    }
    if !matches!(auto_pred, Formula::Eq(_, _)) {
        return None;
    }
    let inner = eq_strip_reg_wrapper(machine_out)?;
    let (mach_pred, mach_then_one) = eq_strip_ite(inner)?;
    if mach_then_one {
        return None; // must be the INVERTED CSET `pred ? 0 : 1`
    }
    let eq_inner = match mach_pred {
        Formula::Not(i) => &**i,
        _ => return None,
    };
    let (sub_f, zero_f) = match eq_inner {
        Formula::Eq(l, r) => (&**l, &**r),
        _ => return None,
    };
    if eq_const_bv_value(zero_f) != Some(0) {
        return None;
    }
    let (la2, ra2) = match sub_f {
        Formula::BvSub(l, r, w) if *w > 0 => (&**l, &**r),
        _ => return None,
    };
    let (la, ra) = match auto_pred {
        Formula::Eq(l, r) => (&**l, &**r),
        _ => return None,
    };

    // CANONICAL per-operand key: peel the operand Formula down to the underlying
    // register var + width, so auto's `Wlo(Xk)` and machine's `Wop(Xk)` (different
    // Formula expressions, SAME register) yield the SAME key — and hence the SAME
    // per-bit list. DIVERGENT operands (auto X1 vs machine X2) yield DIFFERENT keys
    // -> different bit-lists -> the kernel check_type FAILS (no false [PROVED]).
    let key_la = operand_key(la)?;
    let key_ra = operand_key(ra)?;
    let key_la2 = operand_key(la2)?;
    let key_ra2 = operand_key(ra2)?;

    // Per-bit lists keyed by the REAL operand. Concrete length so bvLen reduces.
    let mut bit_axioms: Vec<String> = Vec::new();
    let w = 32u32;
    let bits_a = kx::opaque_bit_list(&key_la, w, &mut bit_axioms);
    let bits_b = kx::opaque_bit_list(&key_ra, w, &mut bit_axioms);
    let bits_a2 = kx::opaque_bit_list(&key_la2, w, &mut bit_axioms);
    let bits_b2 = kx::opaque_bit_list(&key_ra2, w, &mut bit_axioms);
    let one_v = kx::evalf(kx::const_(kx::bits(1, w)));
    let zero_v = kx::evalf(kx::const_(kx::bits(0, w)));

    // auto value: bvIteVal (bvBeq <real la> <real ra>) one zero  — the REAL auto operands.
    let auto_val =
        kx::bv_ite_val(kx::bv_beq(bits_a.clone(), bits_b.clone()), one_v.clone(), zero_v.clone());
    // machine value: bvIteVal (not (bvIsZero (addRecM <real la2> (bvNot <real ra2>) true))) zero one
    let sub_e = kx::add_rec_m(bits_a2.clone(), kx::bv_not(bits_b2.clone()), kx::btrue());
    let mach_val = kx::bv_ite_val(kx::bnot(kx::bv_is_zero(sub_e)), zero_v.clone(), one_v.clone());

    // GOAL ties to the REAL obligation: value(real machine) == value(real auto).
    let goal = kx::eq_list(mach_val, auto_val);
    // eq_value_bridge instantiated at the MACHINE operands (la2, ra2) proves
    //   mach_val == bvIteVal (bvBeq <la2> <ra2>) one zero.
    // The kernel must then defeq that RHS to `auto_val` = bvIteVal (bvBeq <la> <ra>) one zero,
    // i.e. require <la2> ≡ <la> and <ra2> ≡ <ra> (the operands MATCH). Divergent
    // operands have distinct per-bit lists -> the RHS ≠ auto_val -> check_type FAILS.
    let len_refl = kx::eq_refl_nat(kx::bv_len(bits_a2.clone()));
    let discharge = Expr::apps(
        Expr::const_str("Clean.BVC.eq_value_bridge"),
        [bits_a2, bits_b2, one_v, zero_v, len_refl],
    );

    let result = run_recheck_thread("trust-eq-o1-instantiate", move || {
        let env = eq_discharge_env(&bit_axioms).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();

    result.map(|()| "Clean.BVC.eq_value_bridge (O(1) eq@N, real-operand)".to_string())
}

/// THE ULT-COMPARE O(1) DISCHARGE. Recognizes the gate's REAL ult obligation:
///   auto    = Ite(BvULt(la, ra), 1@32, 0@32)
///   machine = W( Ite(Not(BvULt(la', ra')), 0, 1) )
/// BOTH sides use the SAME `BvULt` predicate (no carry/borrow bridge — traced):
/// the discharge is PURE branch-inversion (`ult_value_bridge`/`iteVal_not`), tied
/// to the REAL operands via the operand-key per-bit lists so a divergent-operand
/// ult is KERNEL-REJECTED (ay out of TCB). NON-FOLDING (requires the Ite/Not/BvULt
/// flag structure); on any mismatch ⟹ None.
fn try_ult_value_discharge(machine_out: &Formula, auto: &Formula) -> Option<String> {
    let (auto_pred, auto_then_one) = eq_strip_ite(auto)?;
    if !auto_then_one {
        return None;
    }
    let (la, ra) = match auto_pred {
        Formula::BvULt(l, r, _) => (&**l, &**r),
        _ => return None,
    };
    let inner = eq_strip_reg_wrapper(machine_out)?;
    let (mach_pred, mach_then_one) = eq_strip_ite(inner)?;
    if mach_then_one {
        return None; // must be the INVERTED CSET `pred ? 0 : 1`
    }
    let ult_inner = match mach_pred {
        Formula::Not(i) => &**i,
        _ => return None,
    };
    let (la2, ra2) = match ult_inner {
        Formula::BvULt(l, r, _) => (&**l, &**r),
        _ => return None,
    };

    // Real-operand keys (same discipline as eq): matched operands share bits,
    // divergent operands key differently -> kernel check_type FAILS.
    let key_la = operand_key(la)?;
    let key_ra = operand_key(ra)?;
    let key_la2 = operand_key(la2)?;
    let key_ra2 = operand_key(ra2)?;
    let mut bit_axioms: Vec<String> = Vec::new();
    let w = 32u32;
    let bits_a = kx::opaque_bit_list(&key_la, w, &mut bit_axioms);
    let bits_b = kx::opaque_bit_list(&key_ra, w, &mut bit_axioms);
    let bits_a2 = kx::opaque_bit_list(&key_la2, w, &mut bit_axioms);
    let bits_b2 = kx::opaque_bit_list(&key_ra2, w, &mut bit_axioms);
    let one_v = kx::evalf(kx::const_(kx::bits(1, w)));
    let zero_v = kx::evalf(kx::const_(kx::bits(0, w)));

    // p = bvUlt over REAL operands. auto = bvIteVal p one zero ; machine =
    // bvIteVal (not p2) zero one  where p2 = bvUlt over the MACHINE operands.
    let p_auto = kx::bv_ult(bits_a.clone(), bits_b.clone());
    let p_mach = kx::bv_ult(bits_a2.clone(), bits_b2.clone());
    let auto_val = kx::bv_ite_val(p_auto, one_v.clone(), zero_v.clone());
    let mach_val = kx::bv_ite_val(kx::bnot(p_mach), zero_v.clone(), one_v.clone());
    let goal = kx::eq_list(mach_val, auto_val);
    // ult_value_bridge <la2> <ra2> one zero proves
    //   bvIteVal (not (bvUlt <la2><ra2>)) zero one = bvIteVal (bvUlt <la2><ra2>) one zero.
    // The kernel must defeq the RHS to auto_val (bvUlt <la><ra>) -> requires
    // <la2>≡<la>, <ra2>≡<ra> (operands MATCH); divergent -> check_type FAILS.
    let discharge = Expr::apps(
        Expr::const_str("Clean.BVC.ult_value_bridge"),
        [bits_a2, bits_b2, one_v, zero_v],
    );

    let result = run_recheck_thread("trust-ult-o1-instantiate", move || {
        let env = eq_discharge_env(&bit_axioms).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();
    result.map(|()| "Clean.BVC.ult_value_bridge (O(1) ult@N, real-operand)".to_string())
}

/// THE SLT-COMPARE O(1) DISCHARGE. Recognizes the gate's REAL signed-LT obligation:
///   auto    = Ite(BvSLt(la, ra), 1@32, 0@32)
///   machine = W( Ite( Eq(Eq(N,1bit), V), 0, 1 ) )   (inverted AArch64 `LT` flag)
/// where  N = Extract[31:31](BvSub(la', ra', 32))                       (sign of la'−ra')
///        V = And([ Not(Eq(msb la', msb ra')), Not(Eq(N, msb la')) ])   (signed overflow)
/// The machine genuinely computes the NZCV `N⊕V` flag from the SUB and the operand
/// sign bits (NOT a `BvSLt` predicate). Discharges via `slt_value_bridge` (the kernel
/// N⊕V theorem `slt_flag_bridge` + branch-inversion), tied to the REAL operand keys so a
/// divergent-operand slt is KERNEL-REJECTED (ay out of TCB). NON-FOLDING (requires the
/// exact Eq/Eq/And/Not/BvSub/Extract flag structure); on any mismatch ⟹ None.
fn try_slt_value_discharge(machine_out: &Formula, auto: &Formula) -> Option<String> {
    let (auto_pred, auto_then_one) = eq_strip_ite(auto)?;
    if !auto_then_one {
        return None;
    }
    let (la, ra) = match auto_pred {
        Formula::BvSLt(l, r, _) => (&**l, &**r),
        _ => return None,
    };
    let inner = eq_strip_reg_wrapper(machine_out)?;
    let (mach_pred, mach_then_one) = eq_strip_ite(inner)?;
    if mach_then_one {
        return None; // must be the INVERTED CSET `pred ? 0 : 1`
    }
    // mach_pred = Eq( Eq(N, 1bit), V )  where the OUTER Eq is `(N==1) == V` (booleans).
    let (n_is_one, v_cond) = match mach_pred {
        Formula::Eq(l, r) => (&**l, &**r),
        _ => return None,
    };
    // n_is_one = Eq(N, 1bit) ; pull N (the sign bit of the SUB).
    let n_bit = match n_is_one {
        Formula::Eq(l, r) if eq_const_bv_value(r) == Some(1) => &**l,
        _ => return None,
    };
    // N = Extract[31:31]( BvSub(la2, ra2, 32) )
    let sub_f = match strip_msb_extract(n_bit) {
        Some(inner) => inner,
        None => return None,
    };
    let (la2, ra2) = match sub_f {
        Formula::BvSub(l, r, _) => (&**l, &**r),
        _ => return None,
    };
    // V = And([ Not(Eq(msb la3, msb ra3)), Not(Eq(N3, msb la3')) ]) — verify the
    // overflow flag shape and that its operands match the SUB operands (la2,ra2).
    let v_parts = match v_cond {
        Formula::And(parts) if parts.len() == 2 => parts,
        _ => return None,
    };
    // part0 = Not(Eq(msb la3, msb ra3))
    let (msb_la3, msb_ra3) = match &v_parts[0] {
        Formula::Not(i) => match &**i {
            Formula::Eq(l, r) => (&**l, &**r),
            _ => return None,
        },
        _ => return None,
    };
    let la3 = strip_msb_extract_operand(msb_la3)?;
    let ra3 = strip_msb_extract_operand(msb_ra3)?;
    // part1 = Not(Eq(N', msb la4)) — N' is the SUB sign bit again; we only need la4's key.
    let (_n_again, msb_la4) = match &v_parts[1] {
        Formula::Not(i) => match &**i {
            Formula::Eq(l, r) => (&**l, &**r),
            _ => return None,
        },
        _ => return None,
    };
    let la4 = strip_msb_extract_operand(msb_la4)?;

    // OPERAND-IDENTITY KERNEL-TIED (as eq/ult/ule): reflect every operand position to its
    // OWN key, build mach_val from the REAL machine keys (SUB la2/ra2 + the sign-bit operands
    // la3/ra3/la4) and auto_val from the auto keys la/ra, and instantiate slt_value_bridge at
    // the MACHINE SUB keys (la2,ra2). The kernel `check_type` then FORCES (by defeq) that all
    // sign-bit operands ≡ the SUB operands AND the auto operands ≡ the machine operands.
    // Divergence ANYWHERE -> distinct per-bit lists -> kernel REJECTS. No Rust pre-check.
    let key_la = operand_key(la)?;
    let key_ra = operand_key(ra)?;
    let key_la2 = operand_key(la2)?;
    let key_ra2 = operand_key(ra2)?;
    let key_la3 = operand_key(la3)?;
    let key_ra3 = operand_key(ra3)?;
    let key_la4 = operand_key(la4)?;
    let mut bit_axioms: Vec<String> = Vec::new();
    let w = 32u32;
    let bits_a = kx::opaque_bit_list(&key_la, w, &mut bit_axioms);
    let bits_b = kx::opaque_bit_list(&key_ra, w, &mut bit_axioms);
    let bits_a2 = kx::opaque_bit_list(&key_la2, w, &mut bit_axioms);
    let bits_b2 = kx::opaque_bit_list(&key_ra2, w, &mut bit_axioms);
    let bits_a3 = kx::opaque_bit_list(&key_la3, w, &mut bit_axioms);
    let bits_b3 = kx::opaque_bit_list(&key_ra3, w, &mut bit_axioms);
    let bits_a4 = kx::opaque_bit_list(&key_la4, w, &mut bit_axioms);
    let one_v = kx::evalf(kx::const_(kx::bits(1, w)));
    let zero_v = kx::evalf(kx::const_(kx::bits(0, w)));

    // Build the N⊕V machine condition over the REAL machine keys (the same `rhs(a,b,true)`
    // shape slt_value_bridge proves): N = bvLastBit(addRecM la2 (bvNot ra2) true);
    // V = and(bxor(lastBit la3, lastBit ra3), bxor(N, lastBit la4)). All distinct keys.
    let n_flag =
        kx::last_bit(kx::add_rec_m(bits_a2.clone(), kx::bv_not(bits_b2.clone()), kx::btrue()));
    let v_flag = kx::band(
        kx::bxor(kx::last_bit(bits_a3.clone()), kx::last_bit(bits_b3.clone())),
        kx::bxor(n_flag.clone(), kx::last_bit(bits_a4.clone())),
    );
    let m_cond = kx::bxor(n_flag, v_flag);
    let mach_val = kx::bv_ite_val(kx::bnot(m_cond), zero_v.clone(), one_v.clone());
    // auto value (auto operand keys): bvIteVal (bvSLtReal la ra) one zero
    let auto_val = kx::bv_ite_val(
        kx::bv_slt_real(bits_a.clone(), bits_b.clone()),
        one_v.clone(),
        zero_v.clone(),
    );
    let goal = kx::eq_list(mach_val, auto_val);
    // slt_value_bridge <la2> <ra2> one zero (consh)(lenh) proves
    //   bvIteVal (not (xor N V)) zero one == bvIteVal (bvSLtReal <la2><ra2>) one zero,
    // with N,V over (la2,ra2). The kernel must defeq this to BOTH the goal's mach_val
    // (forcing la3≡la2, ra3≡ra2, la4≡la2) and auto_val (forcing la≡la2, ra≡ra2). All
    // seven positions kernel-tied. consh: bvIsCons <la2> = true (width 32 > 0, by refl);
    // lenh: bvLen <la2> = bvLen <ra2> (both width 32, by refl).
    let consh = kx::eq_refl_bool(kx::btrue());
    let len_refl = kx::eq_refl_nat(kx::bv_len(bits_a2.clone()));
    let discharge = Expr::apps(
        Expr::const_str("Clean.BVC.slt_value_bridge"),
        [bits_a2, bits_b2, one_v, zero_v, consh, len_refl],
    );

    let result = run_recheck_thread("trust-slt-o1-instantiate", move || {
        let env = eq_discharge_env(&bit_axioms).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();
    result.map(|()| "Clean.BVC.slt_value_bridge (O(1) slt@N, real-operand)".to_string())
}

/// Peel `Extract[31:31](inner)` (the MSB/sign-bit extract) and return `inner`.
fn strip_msb_extract(f: &Formula) -> Option<&Formula> {
    match f {
        Formula::BvExtract { inner, high: 31, low: 31 } => Some(&**inner),
        _ => None,
    }
}

/// Peel an MSB/sign-bit extract down to the underlying operand Formula whose
/// `operand_key` identifies the register. The sign-bit form is
/// `Extract[31:31]( <operand-wrapper that operand_key peels> )`.
fn strip_msb_extract_operand(f: &Formula) -> Option<&Formula> {
    strip_msb_extract(f)
}

/// THE ULE-COMPARE O(1) DISCHARGE. Recognizes the gate's REAL ule obligation:
///   auto    = Ite(BvULe(la, ra), 1@32, 0@32)
///   machine = W( Ite(And([Not(BvULt(la',ra')), Not(Eq(BvSub(la',ra',w), 0))]), 0, 1) )
/// (the inverted Hi/> condition). Discharges via `ule_value_bridge` (De Morgan +
/// subtract-zero + branch-inversion) at the REAL operand keys; divergent operands
/// kernel-REJECTED. NON-FOLDING (requires the And/Not/BvULt/Eq/BvSub structure).
fn try_ule_value_discharge(machine_out: &Formula, auto: &Formula) -> Option<String> {
    let (auto_pred, auto_then_one) = eq_strip_ite(auto)?;
    if !auto_then_one {
        return None;
    }
    let (la, ra) = match auto_pred {
        Formula::BvULe(l, r, _) => (&**l, &**r),
        _ => return None,
    };
    let inner = eq_strip_reg_wrapper(machine_out)?;
    let (mach_pred, mach_then_one) = eq_strip_ite(inner)?;
    if mach_then_one {
        return None; // inverted CSET `pred ? 0 : 1`
    }
    // mach_pred = And([Not(BvULt(la',ra')), Not(Eq(BvSub(la',ra',w), 0))])
    let parts = match mach_pred {
        Formula::And(parts) if parts.len() == 2 => parts,
        _ => return None,
    };
    let ult_term = match &parts[0] {
        Formula::Not(i) => &**i,
        _ => return None,
    };
    let (la2, ra2) = match ult_term {
        Formula::BvULt(l, r, _) => (&**l, &**r),
        _ => return None,
    };
    // second conjunct: Not(Eq(BvSub(la3,ra3,w), 0))
    let eq_term = match &parts[1] {
        Formula::Not(i) => &**i,
        _ => return None,
    };
    let (sub_f, zero_f) = match eq_term {
        Formula::Eq(l, r) => (&**l, &**r),
        _ => return None,
    };
    if eq_const_bv_value(zero_f) != Some(0) {
        return None;
    }
    let (la3, ra3) = match sub_f {
        Formula::BvSub(l, r, _) => (&**l, &**r),
        _ => return None,
    };

    // OPERAND-IDENTITY KERNEL-TIED (exactly as eq/ult): reflect each of the four
    // machine/auto operand positions to its OWN key, build mach_val from the REAL
    // machine keys (the ULT conjunct la2/ra2 and the SUB la3/ra3 — as the real
    // Formula has them) and auto_val from the auto keys la/ra, and instantiate
    // ule_value_bridge at the MACHINE (ult-conjunct) keys. The kernel `check_type`
    // then FORCES (by defeq): the SUB operands ≡ the ULT operands (la3≡la2, ra3≡ra2,
    // since the bridge's single a,b appears in both conjunct and sub), AND the auto
    // operands ≡ the machine operands (la≡la2, ra≡ra2, via the bridge RHS == auto_val).
    // Divergence ANYWHERE -> distinct per-bit lists -> kernel REJECTS. No Rust
    // pre-check: the KERNEL is the sole operand-identity authority, like eq/ult.
    let key_la = operand_key(la)?;
    let key_ra = operand_key(ra)?;
    let key_la2 = operand_key(la2)?;
    let key_ra2 = operand_key(ra2)?;
    let key_la3 = operand_key(la3)?;
    let key_ra3 = operand_key(ra3)?;
    let mut bit_axioms: Vec<String> = Vec::new();
    let w = 32u32;
    let bits_a = kx::opaque_bit_list(&key_la, w, &mut bit_axioms);
    let bits_b = kx::opaque_bit_list(&key_ra, w, &mut bit_axioms);
    let bits_a2 = kx::opaque_bit_list(&key_la2, w, &mut bit_axioms);
    let bits_b2 = kx::opaque_bit_list(&key_ra2, w, &mut bit_axioms);
    let bits_a3 = kx::opaque_bit_list(&key_la3, w, &mut bit_axioms);
    let bits_b3 = kx::opaque_bit_list(&key_ra3, w, &mut bit_axioms);
    let one_v = kx::evalf(kx::const_(kx::bits(1, w)));
    let zero_v = kx::evalf(kx::const_(kx::bits(0, w)));

    // machine value (REAL machine operand positions): the ult conjunct over (la2,ra2)
    // and the sub over (la3,ra3) — distinct keys, as the real Formula has them.
    let m_pred = kx::band(
        kx::bnot(kx::bv_ult(bits_a2.clone(), bits_b2.clone())),
        kx::bnot(kx::bv_is_zero(kx::add_rec_m(
            bits_a3.clone(),
            kx::bv_not(bits_b3.clone()),
            kx::btrue(),
        ))),
    );
    let mach_val = kx::bv_ite_val(m_pred, zero_v.clone(), one_v.clone());
    // auto value (auto operand keys): bvIteVal (bvULe la ra) one zero
    let auto_val =
        kx::bv_ite_val(kx::bv_ule(bits_a.clone(), bits_b.clone()), one_v.clone(), zero_v.clone());
    let goal = kx::eq_list(mach_val, auto_val);
    // ule_value_bridge instantiated at the MACHINE ULT-conjunct keys (la2,ra2):
    //   proves mach_val' = bvIteVal (and (not(bvUlt la2 ra2))(not(bvIsZero(sub la2 ra2)))) zero one
    //          == bvIteVal (bvULe la2 ra2) one zero.
    // The kernel must defeq this to BOTH the goal's mach_val (forcing la3≡la2, ra3≡ra2)
    // and auto_val (forcing la≡la2, ra≡ra2). All four positions kernel-tied.
    let len_refl = kx::eq_refl_nat(kx::bv_len(bits_a2.clone()));
    let discharge = Expr::apps(
        Expr::const_str("Clean.BVC.ule_value_bridge"),
        [bits_a2, bits_b2, one_v, zero_v, len_refl],
    );

    let result = run_recheck_thread("trust-ule-o1-instantiate", move || {
        let env = eq_discharge_env(&bit_axioms).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();
    result.map(|()| "Clean.BVC.ule_value_bridge (O(1) ule@N, real-operand)".to_string())
}

/// THE SLE-COMPARE O(1) DISCHARGE. Recognizes the gate's REAL signed-≤ obligation:
///   auto    = Ite(BvSLe(la, ra), 1@32, 0@32)
///   machine = W( Ite( And([ Not(Eq(BvSub(la',ra',32), 0)),  Eq(Eq(N,1), V) ]), 0, 1 ) )
/// i.e. the inverted `a > b` flag `And(a≠b, a>=s b)`, where the second conjunct is the
/// SAME NZCV `N==V` (signed-NLT) flag as slt. Discharges via `sle_value_bridge` (the
/// subtract-zero bridge + slt flag bridge + De Morgan + branch-inversion), tied to the
/// REAL operand keys so a divergent-operand sle is KERNEL-REJECTED (ay out of TCB).
/// NON-FOLDING (requires the exact And/Not/Eq/BvSub/Eq/Eq/And flag structure); else None.
fn try_sle_value_discharge(machine_out: &Formula, auto: &Formula) -> Option<String> {
    let (auto_pred, auto_then_one) = eq_strip_ite(auto)?;
    if !auto_then_one {
        return None;
    }
    let (la, ra) = match auto_pred {
        Formula::BvSLe(l, r, _) => (&**l, &**r),
        _ => return None,
    };
    let inner = eq_strip_reg_wrapper(machine_out)?;
    let (mach_pred, mach_then_one) = eq_strip_ite(inner)?;
    if mach_then_one {
        return None; // inverted CSET `pred ? 0 : 1`
    }
    // mach_pred = And([ Not(Eq(BvSub(lz,rz), 0)),  Eq(Eq(N,1), V) ])
    let parts = match mach_pred {
        Formula::And(parts) if parts.len() == 2 => parts,
        _ => return None,
    };
    // conjunct 0: Not(Eq(BvSub(lz,rz,32), 0))  — the `a≠b` (subtract-zero) condition.
    let eq_term = match &parts[0] {
        Formula::Not(i) => &**i,
        _ => return None,
    };
    let (subz_f, zero_f) = match eq_term {
        Formula::Eq(l, r) => (&**l, &**r),
        _ => return None,
    };
    if eq_const_bv_value(zero_f) != Some(0) {
        return None;
    }
    let (lz, rz) = match subz_f {
        Formula::BvSub(l, r, _) => (&**l, &**r),
        _ => return None,
    };
    // conjunct 1: Eq(Eq(N,1), V) — the signed N==V (NLT) flag (same N,V parsing as slt).
    let (n_is_one, v_cond) = match &parts[1] {
        Formula::Eq(l, r) => (&**l, &**r),
        _ => return None,
    };
    let n_bit = match n_is_one {
        Formula::Eq(l, r) if eq_const_bv_value(r) == Some(1) => &**l,
        _ => return None,
    };
    let sub_f = strip_msb_extract(n_bit)?;
    let (la2, ra2) = match sub_f {
        Formula::BvSub(l, r, _) => (&**l, &**r),
        _ => return None,
    };
    let v_parts = match v_cond {
        Formula::And(parts) if parts.len() == 2 => parts,
        _ => return None,
    };
    let (msb_la3, msb_ra3) = match &v_parts[0] {
        Formula::Not(i) => match &**i {
            Formula::Eq(l, r) => (&**l, &**r),
            _ => return None,
        },
        _ => return None,
    };
    let la3 = strip_msb_extract_operand(msb_la3)?;
    let ra3 = strip_msb_extract_operand(msb_ra3)?;
    let (_n_again, msb_la4) = match &v_parts[1] {
        Formula::Not(i) => match &**i {
            Formula::Eq(l, r) => (&**l, &**r),
            _ => return None,
        },
        _ => return None,
    };
    let la4 = strip_msb_extract_operand(msb_la4)?;

    // OPERAND-IDENTITY KERNEL-TIED: reflect EVERY position to its own key — auto (la,ra),
    // the subtract-zero conjunct (lz,rz), the N-flag SUB (la2,ra2), and the V sign bits
    // (la3,ra3,la4). Build mach_val from the REAL machine keys + auto_val from the auto keys,
    // and instantiate sle_value_bridge at the SUB keys (la2,ra2). The kernel check_type then
    // forces all positions ≡ (la2,ra2) and the auto operands ≡ them. Divergence -> distinct
    // per-bit lists -> kernel REJECTS. No Rust pre-check.
    let key_la = operand_key(la)?;
    let key_ra = operand_key(ra)?;
    let key_lz = operand_key(lz)?;
    let key_rz = operand_key(rz)?;
    let key_la2 = operand_key(la2)?;
    let key_ra2 = operand_key(ra2)?;
    let key_la3 = operand_key(la3)?;
    let key_ra3 = operand_key(ra3)?;
    let key_la4 = operand_key(la4)?;
    let mut bit_axioms: Vec<String> = Vec::new();
    let w = 32u32;
    let bits_a = kx::opaque_bit_list(&key_la, w, &mut bit_axioms);
    let bits_b = kx::opaque_bit_list(&key_ra, w, &mut bit_axioms);
    let bits_lz = kx::opaque_bit_list(&key_lz, w, &mut bit_axioms);
    let bits_rz = kx::opaque_bit_list(&key_rz, w, &mut bit_axioms);
    let bits_a2 = kx::opaque_bit_list(&key_la2, w, &mut bit_axioms);
    let bits_b2 = kx::opaque_bit_list(&key_ra2, w, &mut bit_axioms);
    let bits_a3 = kx::opaque_bit_list(&key_la3, w, &mut bit_axioms);
    let bits_b3 = kx::opaque_bit_list(&key_ra3, w, &mut bit_axioms);
    let bits_a4 = kx::opaque_bit_list(&key_la4, w, &mut bit_axioms);
    let one_v = kx::evalf(kx::const_(kx::bits(1, w)));
    let zero_v = kx::evalf(kx::const_(kx::bits(0, w)));

    // machine value = bvIteVal (and (not(isZero(sub lz rz))) (not(xor N V))) zero one
    //   N = bvLastBit(addRecM la2 (bvNot ra2) true); V = and(bxor(msb la3,msb ra3),bxor(N,msb la4)).
    let n_flag =
        kx::last_bit(kx::add_rec_m(bits_a2.clone(), kx::bv_not(bits_b2.clone()), kx::btrue()));
    let v_flag = kx::band(
        kx::bxor(kx::last_bit(bits_a3.clone()), kx::last_bit(bits_b3.clone())),
        kx::bxor(n_flag.clone(), kx::last_bit(bits_a4.clone())),
    );
    let isz =
        kx::bv_is_zero(kx::add_rec_m(bits_lz.clone(), kx::bv_not(bits_rz.clone()), kx::btrue()));
    let m_pred = kx::band(kx::bnot(isz), kx::bnot(kx::bxor(n_flag, v_flag)));
    let mach_val = kx::bv_ite_val(m_pred, zero_v.clone(), one_v.clone());
    let auto_val = kx::bv_ite_val(
        kx::bv_sle_real(bits_a.clone(), bits_b.clone()),
        one_v.clone(),
        zero_v.clone(),
    );
    let goal = kx::eq_list(mach_val, auto_val);
    // sle_value_bridge <la2> <ra2> one zero (consh)(lenh) — the bridge's single (a,b) appears in
    // BOTH the subtract-zero conjunct and the N/V flag, so the kernel forces lz≡la2, rz≡ra2,
    // la3≡la2, ra3≡ra2, la4≡la2 AND the auto operands ≡ (la2,ra2). All nine positions kernel-tied.
    let consh = kx::eq_refl_bool(kx::btrue());
    let len_refl = kx::eq_refl_nat(kx::bv_len(bits_a2.clone()));
    let discharge = Expr::apps(
        Expr::const_str("Clean.BVC.sle_value_bridge"),
        [bits_a2, bits_b2, one_v, zero_v, consh, len_refl],
    );

    let result = run_recheck_thread("trust-sle-o1-instantiate", move || {
        let env = eq_discharge_env(&bit_axioms).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();
    result.map(|()| "Clean.BVC.sle_value_bridge (O(1) sle@N, real-operand)".to_string())
}

#[cfg(test)]
pub(crate) fn try_sle_value_discharge_for_test(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    try_sle_value_discharge(machine_out, auto)
}

#[cfg(test)]
pub(crate) fn try_ule_value_discharge_for_test(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    try_ule_value_discharge(machine_out, auto)
}

/// Test shim for the ult discharge (verify_output's ult controls).
#[cfg(test)]
pub(crate) fn try_ult_value_discharge_for_test(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    try_ult_value_discharge(machine_out, auto)
}

/// Test shim for the slt discharge (verify_output's slt controls).
#[cfg(test)]
pub(crate) fn try_slt_value_discharge_for_test(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    try_slt_value_discharge(machine_out, auto)
}

/// Canonical key for an eq operand Formula: peel the operand wrappers
/// (`Extract[31:0]`, `BvZeroExt`, `BvOr(0,·)`) down to the underlying register
/// `Var(name, _)` and return `{name}_{width}`. Auto's bare `Extract[31:0](Xk)`
/// and machine's wrapped `Extract[31:0](ZeroExt(Or(0, Extract[31:0](Xk)),32))`
/// peel to the SAME key. Returns None for any non-canonical operand.
fn operand_key(f: &Formula) -> Option<String> {
    match f {
        Formula::Var(name, sort) => {
            let w = match sort {
                Sort::BitVec(w) => *w,
                _ => return None,
            };
            Some(format!("REG_{name}_{w}"))
        }
        // Peel wrappers to the underlying register, but the OUTERMOST extract's
        // slice `[high:low]` defines the operand's identity (low/high bits, width).
        // The canonical W-register eq form is Extract[31:0] on BOTH sides (auto's
        // bare `Extract[31:0](X)` and machine's `Extract[31:0](ZeroExt(Or(0,
        // Extract[31:0](X)),32))`), so both reduce to the SAME register `X` with
        // the SAME outer slice `[31:0]` -> identical key. A genuinely different
        // outer slice (`Extract[15:0]`) keys differently -> divergence rejected.
        // Inner wrappers (ZeroExt, Or(0,·), the inner re-extract) are identity on
        // the canonical form and are peeled WITHOUT contributing to the key.
        Formula::BvExtract { inner, high, low } => {
            Some(format!("SLICE{high}_{low}__{}", reg_root_key(inner)?))
        }
        Formula::BvZeroExt(inner, _) => operand_key(inner),
        Formula::BvOr(l, r, _) => {
            // Or(0, x) wrapper: peel the non-zero side.
            if matches!(&**l, Formula::BitVec { value: 0, .. }) {
                operand_key(r)
            } else if matches!(&**r, Formula::BitVec { value: 0, .. }) {
                operand_key(l)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Peel the canonical operand-wrapper layers (`ZeroExt`, `Or(0,·)`, and the inner
/// width-coercion re-extract that is IDENTITY on the already-sliced value) down to
/// the register `Var` root, returning `REG_{name}_{w}`. Used by `operand_key`'s
/// outer-`BvExtract` arm: the OUTER slice fixes the operand identity; the inner
/// wrappers are identity and contribute nothing to the key (so auto's bare extract
/// and machine's wrapped extract of the same register share one key).
fn reg_root_key(f: &Formula) -> Option<String> {
    match f {
        Formula::Var(name, Sort::BitVec(w)) => Some(format!("REG_{name}_{w}")),
        Formula::BvExtract { inner, .. } => reg_root_key(inner),
        Formula::BvZeroExt(inner, _) => reg_root_key(inner),
        Formula::BvOr(l, r, _) => {
            if matches!(&**l, Formula::BitVec { value: 0, .. }) {
                reg_root_key(r)
            } else if matches!(&**r, Formula::BitVec { value: 0, .. }) {
                reg_root_key(l)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Test shim: run only the eq-compare discharge (used by verify_output's eq
/// negative controls to exercise the matcher + kernel guard directly).
#[cfg(test)]
pub(crate) fn try_eq_value_discharge_for_test(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    try_eq_value_discharge(machine_out, auto)
}

/// Discharge env for the eq path: BVC layer + fresh opaque per-bit `Bool` axioms.
fn eq_discharge_env(bit_axioms: &[String]) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    env.init_bv_coercion().map_err(|e| format!("init_bv_coercion: {e:?}"))?;
    for nm in bit_axioms {
        let _ = env.add_decl(clean_kernel::Declaration::Axiom {
            name: Name::from_string(nm),
            level_params: vec![],
            type_: kx::bool_ty(),
        });
    }
    Ok(env)
}

/// Peel the div readout/coercion wrappers down to the guarded `Ite`. Each accepted layer is a
/// width-PRESERVING identity on the 32-bit value: `Extract[31:0]` (NOT a bit-dropping slice —
/// `high:31, low:0` is structurally required, matching the slow reflect path's `low != 0`
/// rejection), `ZeroExt` (adds high zero bits, identity on the low 32), and `Or(0, ·)`. This is the
/// same matcher-trusted readout strip the compares use; it is NOT independently kernel-re-checked —
/// it is backed by ay's prior width-matched UNSAT over the FULL wrapped `machine_out` (a
/// width-changing wrapper makes the equality SAT, so the strip is never reached on such a shape).
/// Stops at the first non-wrapper node.
fn div_peel_to_ite(f: &Formula) -> Option<&Formula> {
    match f {
        Formula::Ite(..) => Some(f),
        // [31:0] ONLY — a bit-dropping slice (high < 31 or low != 0) is NOT a value identity; reject it.
        Formula::BvExtract { inner, high: 31, low: 0 } => div_peel_to_ite(inner),
        Formula::BvZeroExt(z, _) => div_peel_to_ite(z),
        Formula::BvOr(l, r, _) if matches!(&**l, Formula::BitVec { value: 0, .. }) => {
            div_peel_to_ite(r)
        }
        _ => None,
    }
}

/// THE UNSIGNED-DIV CONDITIONAL O(1) DISCHARGE. Recognizes the gate's REAL udiv obligation:
///   auto    = BvUDiv(Wa, Wb)
///   machine = W_zext( Ite(Eq(Wb', 0@w), 0@w, BvUDiv(Wa', Wb')) )   (the architectural ÷0=0 guard)
/// Under the gate precondition `b != 0` (reflected as `bvIsZero <b> = false`), `divGuardBridge`
/// collapses the machine `Ite` to its `BvUDiv` else-branch = auto. THE PROOF is `divGuardBridge`
/// PARTIALLY applied at the MACHINE operand bit-lists, leaving the `b != 0` hypothesis OPEN — so
/// the discharge term has the CONDITIONAL type `(bvIsZero <b2> = false) -> (mach_val = bvDiv <a2><b2>)`,
/// exactly the gate's conditional obligation. OPERAND-IDENTITY KERNEL-TIED (eq/ult discipline): the
/// kernel `check_type` against the conditional goal must defeq the conclusion RHS `bvDiv <a2><b2>` to
/// the goal's auto_val `bvDiv <a><b>`, FORCING <a2>≡<a>, <b2>≡<b>; divergent operands key to distinct
/// bit-lists -> REJECT (no false [PROVED]). Handles BOTH unsigned (auto `BvUDiv` -> `bvDiv`) and
/// SIGNED (auto `BvSDiv` -> `bvSDiv`, sign-magnitude round-to-zero); the machine op must MATCH auto's
/// signedness (a unsigned-machine / signed-auto cross is rejected). On any mismatch / kernel rejection
/// ⟹ None (fail-closed).
///
/// KERNEL-INDEPENDENCE SCOPE (honest): the kernel `check_type` independently re-establishes the
/// DIVISION-SEMANTICS CORE — the ÷0-guard collapse (`divGuardBridge`) and operand identity
/// (<a2>≡<a>, <b2>≡<b>). It does NOT re-check the readout-WRAPPER faithfulness: those layers are
/// stripped by the matcher (`div_peel_to_ite`, in the TCB) and their value-preservation is backed by
/// ay's prior width-matched UNSAT over the unstripped formulas — so a strip bug can only MIS-GRADE an
/// already-ay-proven obligation, never fabricate a [PROVED]. (This readout-strip residual is shared
/// with the eq/ult/… value discharges; it is matcher-trusted, not ay-free.)
pub(crate) fn try_div_conditional_discharge(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    // auto = BvUDiv(a, b) [unsigned] OR BvSDiv(a, b) [signed]
    let (a, b, signed) = match auto {
        Formula::BvUDiv(l, r, _) => (&**l, &**r, false),
        Formula::BvSDiv(l, r, _) => (&**l, &**r, true),
        _ => return None,
    };
    // machine = W( Ite(Eq(b2, 0), 0, BvU/SDiv(a2, b2)) ), W = nested Extract/ZeroExt/Or(0,·)
    let inner = div_peel_to_ite(machine_out)?;
    let (pred, then_b, else_b) = match inner {
        Formula::Ite(p, t, e) => (&**p, &**t, &**e),
        _ => return None,
    };
    if eq_const_bv_value(then_b) != Some(0) {
        return None; // then-branch must be the ÷0 result 0
    }
    // predicate is `Eq(b2, 0)` (zero on either side)
    let b_pred = match pred {
        Formula::Eq(l, r) if eq_const_bv_value(r) == Some(0) => &**l,
        Formula::Eq(l, r) if eq_const_bv_value(l) == Some(0) => &**r,
        _ => return None,
    };
    let (a2, b2) = match (else_b, signed) {
        (Formula::BvUDiv(l, r, _), false) => (&**l, &**r),
        (Formula::BvSDiv(l, r, _), true) => (&**l, &**r),
        _ => return None, // machine div op must match auto's signedness
    };

    let key_a = operand_key(a)?;
    let key_b = operand_key(b)?;
    let key_a2 = operand_key(a2)?;
    let key_b2 = operand_key(b2)?;
    // SOUNDNESS: the ÷0-guard predicate divisor (b_pred) must key-match the udiv divisor (b2), so the
    // hypothesis `bvIsZero <b2> = false` collapses the SAME guard the value is divided under. This Rust
    // check is LOAD-BEARING: the kernel ties b2≡b to the auto side, but the guard predicate operand is
    // not otherwise kernel-constrained to equal b2, so a mismatched guard register must be refused here.
    if operand_key(b_pred)? != key_b2 {
        return None;
    }

    let mut bit_axioms: Vec<String> = Vec::new();
    let w = 32u32;
    let bits_a = kx::opaque_bit_list(&key_a, w, &mut bit_axioms);
    let bits_b = kx::opaque_bit_list(&key_b, w, &mut bit_axioms);
    let bits_a2 = kx::opaque_bit_list(&key_a2, w, &mut bit_axioms);
    let bits_b2 = kx::opaque_bit_list(&key_b2, w, &mut bit_axioms);
    let zero_v = kx::evalf(kx::const_(kx::bits(0, w)));

    // value fn: unsigned -> bvDiv ; signed -> bvSDiv (the quotient divGuardBridge collapses to).
    let valfn = |x: Expr, y: Expr| if signed { kx::bv_sdiv(x, y) } else { kx::bv_div(x, y) };
    // mach_val = bvIteVal (bvIsZero <b2>) zero (val <a2> <b2>) ; auto_val = val <a> <b>.
    let mach_val = kx::bv_ite_val(
        kx::bv_is_zero(bits_b2.clone()),
        zero_v.clone(),
        valfn(bits_a2.clone(), bits_b2.clone()),
    );
    let auto_val = valfn(bits_a, bits_b);
    // CONDITIONAL goal: (bvIsZero <b2> = false) -> (mach_val = auto_val).
    let h_type = kx::eq_bool(kx::bv_is_zero(bits_b2.clone()), kx::bfalse());
    let goal = Expr::arrow(h_type, kx::eq_list(mach_val, auto_val));
    // discharge = divGuardBridge <b2> zero (val <a2> <b2>)  [h LEFT OPEN] : the conditional proof.
    let discharge = Expr::apps(
        Expr::const_str("Clean.BVC.divGuardBridge"),
        [bits_b2.clone(), zero_v, valfn(bits_a2, bits_b2)],
    );

    let result = run_recheck_thread("trust-div-o1-instantiate", move || {
        let env = eq_discharge_env(&bit_axioms).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();
    let label = if signed { "sdiv" } else { "udiv" };
    result.map(|()| format!("Clean.BVC.divGuardBridge (O(1) {label}@N conditional, real-operand)"))
}

/// Test surface: the conditional udiv discharge (used by verify_output's div B4 tests).
#[cfg(test)]
pub(crate) fn try_div_conditional_discharge_for_test(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    try_div_conditional_discharge(machine_out, auto)
}

/// Reconstruct the eval-level (List Bool) VALUE of an unsigned-rem composite Formula:
/// peel matcher-trusted coercion wrappers (Extract[31:0]/ZeroExt/Or-zero), map the composite
/// nodes to their bvfEval functions (BvSub -> addRecM a (bvNot b) true; BvMul -> bvMul;
/// BvUDiv -> bvDiv; the ÷0-guarded Ite -> bvIteVal (bvIsZero <b>) ..), and key register operands
/// to opaque per-bit lists. A register operand (possibly wrapped) is detected by operand_key and
/// becomes a leaf; composites/structural-wrappers fail operand_key and recurse. Both the machine
/// (heavily wrapped) and the auto (bare) rem formulas reconstruct to the IDENTICAL clean value
/// WHEN their operands key the same — so eq_list(V_machine, V_auto) closes by REFLEXIVITY and the
/// kernel forces operand identity (divergent operands key to distinct bit-lists -> refl ill-typed).
/// MATCHER-TRUSTED (the wrapper peel + node->eval mapping is in the TCB, ay-backed); the kernel work
/// is the operand-tied STRUCTURAL equality (refl), NOT a semantic collapse (rem is DEFINED as this
/// composite, so there is no further semantic content — the inner udiv is identical on both sides).
fn rem_to_val(f: &Formula, w: u32, axioms: &mut Vec<String>) -> Option<Expr> {
    // A register operand (possibly wrapped) -> opaque per-bit list keyed by register.
    if let Some(key) = operand_key(f) {
        return Some(kx::opaque_bit_list(&key, w, axioms));
    }
    match f {
        Formula::BvSub(l, r, _) => {
            let vl = rem_to_val(l, w, axioms)?;
            let vr = rem_to_val(r, w, axioms)?;
            Some(kx::add_rec_m(vl, kx::bv_not(vr), kx::btrue()))
        }
        Formula::BvMul(l, r, _) => {
            let vl = rem_to_val(l, w, axioms)?;
            let vr = rem_to_val(r, w, axioms)?;
            Some(kx::bv_mul(vl, vr))
        }
        Formula::BvUDiv(l, r, _) => {
            let vl = rem_to_val(l, w, axioms)?;
            let vr = rem_to_val(r, w, axioms)?;
            Some(kx::bv_div(vl, vr))
        }
        Formula::BvSDiv(l, r, _) => {
            let vl = rem_to_val(l, w, axioms)?;
            let vr = rem_to_val(r, w, axioms)?;
            Some(kx::bv_sdiv(vl, vr))
        }
        Formula::Ite(p, t, e) => {
            let b_pred = match &**p {
                Formula::Eq(l, r) if eq_const_bv_value(r) == Some(0) => &**l,
                Formula::Eq(l, r) if eq_const_bv_value(l) == Some(0) => &**r,
                _ => return None,
            };
            let vb = rem_to_val(b_pred, w, axioms)?;
            let vt = rem_to_val(t, w, axioms)?;
            let ve = rem_to_val(e, w, axioms)?;
            Some(kx::bv_ite_val(kx::bv_is_zero(vb), vt, ve))
        }
        Formula::BitVec { value, width } => {
            Some(kx::evalf(kx::const_(kx::bits(*value as i128, *width))))
        }
        // structural coercion wrappers (value-preserving identities), peeled (matcher-trusted, [31:0] only).
        Formula::BvExtract { inner, high: 31, low: 0 } => rem_to_val(inner, w, axioms),
        Formula::BvZeroExt(z, _) => rem_to_val(z, w, axioms),
        Formula::BvOr(l, r, _) if matches!(&**l, Formula::BitVec { value: 0, .. }) => {
            rem_to_val(r, w, axioms)
        }
        _ => None,
    }
}

/// THE UNSIGNED-REM O(1) DISCHARGE. The machine bytes (udiv then msub) and the auto-spec are the
/// IDENTICAL composite a - Ite(b==0,0,udiv(a,b)) * b up to value-preserving coercion wrappers (the
/// auto-spec mirrors the machine lowering by construction). So both reconstruct (rem_to_val) to the
/// SAME clean value over key-matched operands, and the obligation closes by REFLEXIVITY. The gate's
/// b!=0 precondition is satisfied VACUOUSLY — the unconditional equality is strictly stronger. The
/// kernel check_type forces operand identity (a divergent operand keys to a distinct bit-list, so
/// refl is ill-typed -> REJECT). Honest scope: the kernel verifies the operand-tied STRUCTURAL
/// equality only; the composite reconstruction is matcher-trusted + ay-backed (see rem_to_val). The
/// inner udiv is identical on both sides (its correctness is the separate div [PROVED]). On any
/// mismatch / kernel rejection ⟹ None (fail-closed -> [VALIDATED]).
pub(crate) fn try_rem_conditional_discharge(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    // Cheap shape gate: the unsigned-rem auto-spec is a BvSub at the root.
    if !matches!(auto, Formula::BvSub(_, _, _)) {
        return None;
    }
    let w = 32u32;
    let mut axioms: Vec<String> = Vec::new();
    let v_m = rem_to_val(machine_out, w, &mut axioms)?;
    let v_a = rem_to_val(auto, w, &mut axioms)?;
    let goal = kx::eq_list(v_m.clone(), v_a);
    let discharge = kx::eq_refl_list(v_m);
    let result = run_recheck_thread("trust-urem-o1-instantiate", move || {
        let env = eq_discharge_env(&axioms).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();
    result.map(|()| {
        "Clean.BVC refl (O(1) urem@N composite, matcher-reconstructed, real-operand)".to_string()
    })
}

/// Test surface: the unsigned-rem discharge (used by verify_output's rem B4 tests).
#[cfg(test)]
pub(crate) fn try_rem_conditional_discharge_for_test(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    try_rem_conditional_discharge(machine_out, auto)
}

pub(crate) fn try_o1_instantiation_discharge(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    // EQ-compare value discharge FIRST (strictly additive; falls through on
    // any non-match to the bitvector-core path below).
    if let Some(t) = try_eq_value_discharge(machine_out, auto) {
        return Some(t);
    }
    if let Some(t) = try_ult_value_discharge(machine_out, auto) {
        return Some(t);
    }
    if let Some(t) = try_slt_value_discharge(machine_out, auto) {
        return Some(t);
    }
    if let Some(t) = try_ule_value_discharge(machine_out, auto) {
        return Some(t);
    }
    if let Some(t) = try_sle_value_discharge(machine_out, auto) {
        return Some(t);
    }

    let mut leaves: Vec<(String, u32)> = Vec::new();
    let rm = reflect_formula(machine_out, &mut leaves).ok()?;
    let ra = reflect_formula(auto, &mut leaves).ok()?;

    // The discharge term: bvfEval(rm.bvf) = bvfEval(ra.bvf), via
    //   rm.proof : bvfEval(rm.bvf) = bvfEval(rm.core)
    //   Eq.symm ra.proof : bvfEval(ra.core) = bvfEval(ra.bvf)
    // chained through the SHARED core (rm.core ≡ ra.core by defeq) by Eq.trans.
    let goal = kx::eq_list(kx::evalf(rm.bvf.clone()), kx::evalf(ra.bvf.clone()));
    let sym_ra = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
        [kx::list_bool(), kx::evalf(ra.bvf.clone()), kx::evalf(ra.core.clone()), ra.proof],
    );
    let discharge = kx::eq_trans_list(
        kx::evalf(rm.bvf),
        kx::evalf(rm.core),
        kx::evalf(ra.bvf),
        rm.proof,
        sym_ra,
    );

    // Run the kernel check on a big stack (deep bvfEval reduction). The kernel
    // check_type is the SOLE authority: success ⟹ the discharge proves the REAL
    // reflected obligation with empty domain axioms (the bvf_* lemmas are
    // empty-closure; the leaf axioms are not among their deps). Any panic/failure
    // ⟹ None (fall through).
    let result = run_recheck_thread("trust-mpos-o1-instantiate", move || {
        let env = discharge_env(&leaves).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();

    result.map(|()| "Clean.BVC.bvf_wrapper_id+congruence (O(1) add@N)".to_string())
}

/// Does the formula contain a `Select` node (a memory read)? Cheap guard so the
/// memory discharge only fires on store-load obligations.
fn formula_contains_select(f: &Formula) -> bool {
    match f {
        Formula::Select(..) => true,
        Formula::Store(a, b, c) => {
            formula_contains_select(a) || formula_contains_select(b) || formula_contains_select(c)
        }
        Formula::BvExtract { inner, .. } => formula_contains_select(inner),
        Formula::BvZeroExt(x, _) | Formula::Not(x) => formula_contains_select(x),
        Formula::BvAdd(l, r, _)
        | Formula::BvSub(l, r, _)
        | Formula::BvOr(l, r, _)
        | Formula::BvAnd(l, r, _)
        | Formula::BvXor(l, r, _) => formula_contains_select(l) || formula_contains_select(r),
        _ => false,
    }
}

/// MEMORY-PATH reflection — the CONCRETE-CONS, FAITHFUL (non-stripping) variant that
/// makes sub-register (u8/u16) readout coercions REDUCE. Differs from `reflect_formula`:
///   (1) register leaves reflect as a CONCRETE `opaque_bit_list` (a cons of `w` fresh
///       per-bit `Bool` axioms), NOT a single opaque `List Bool` leaf — so `bvfEval`
///       of every `ZeroExt`/`ExtractLow`/`Or`/`Add` over them REDUCES computationally
///       (append/take/zipOr on a concrete cons), collapsing the whole readout to the
///       byte's bits with NO width-matched coercion-identity lemma required;
///   (2) wrappers are NON-STRIPPING: `core = W(inner.core)` (the wrapper is kept in
///       BOTH bvf and core, proof by the plain congruence lemma), so equality is
///       discharged by defeq REDUCTION of both cores to the same concrete byte;
///   (3) the store-load `Select(Store(M,a,v),a)` bridges via `selectStoreSame` (the ONE
///       non-reducing point — `bvSelect` is stuck on `bvBeq a a`), abstracting the
///       underlying memory (frame stack) as the closed `opaque_mem`.
/// Returns `None` for any node outside this fragment (→ caller falls through, [VALIDATED]).
fn reflect_mem(f: &Formula, bit_axioms: &mut Vec<String>) -> Option<Reflected> {
    match f {
        Formula::Var(name, Sort::BitVec(w)) => {
            let key = operand_key(f).unwrap_or_else(|| name.clone());
            let bits = kx::opaque_bit_list(&key, *w, bit_axioms);
            let bvf = kx::leaf(bits);
            Some(Reflected {
                bvf: bvf.clone(),
                core: bvf.clone(),
                proof: kx::eq_refl_list(kx::evalf(bvf)),
            })
        }
        Formula::BitVec { value, width } => {
            let bvf = kx::const_(kx::bits(*value, *width));
            Some(Reflected {
                bvf: bvf.clone(),
                core: bvf.clone(),
                proof: kx::eq_refl_list(kx::evalf(bvf)),
            })
        }
        Formula::BvZeroExt(inner, k) => {
            let ri = reflect_mem(inner, bit_axioms)?;
            let kn = kx::nat_lit(*k);
            let bvf = kx::zext(ri.bvf.clone(), kn.clone());
            let core = kx::zext(ri.core.clone(), kn.clone());
            let proof = kx::zext_cong(ri.bvf, ri.core, kn, ri.proof);
            Some(Reflected { bvf, core, proof })
        }
        Formula::BvExtract { inner, high, low } if *low == 0 => {
            let ri = reflect_mem(inner, bit_axioms)?;
            let w = high + 1;
            let tag = kx::const_(kx::bits(0, w));
            let bvf = kx::extract(ri.bvf.clone(), tag.clone());
            let core = kx::extract(ri.core.clone(), tag.clone());
            let proof = kx::extract_cong1(ri.bvf, ri.core, tag, ri.proof);
            Some(Reflected { bvf, core, proof })
        }
        Formula::BvOr(l, r, _) if matches!(&**l, Formula::BitVec { value: 0, .. }) => {
            let ri = reflect_mem(r, bit_axioms)?;
            let const_af = kx::const_(kx::all_false(kx::evalf(ri.core.clone())));
            let bvf = kx::or(const_af.clone(), ri.bvf.clone());
            let core = kx::or(const_af.clone(), ri.core.clone());
            let proof = kx::or_cong2(const_af, ri.bvf, ri.core, ri.proof);
            Some(Reflected { bvf, core, proof })
        }
        Formula::BvAdd(l, r, _) => {
            let rl = reflect_mem(l, bit_axioms)?;
            let rr = reflect_mem(r, bit_axioms)?;
            let bvf = kx::add(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::add(rl.core.clone(), rr.core.clone());
            let proof = kx::add_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Some(Reflected { bvf, core, proof })
        }
        Formula::Select(mem, load_addr) => {
            let Formula::Store(_under, store_addr, val) = &**mem else { return None };
            // Reflect the store and load addresses SEPARATELY (they may be value-equal but
            // structurally different wrappings of the pointer). The load is built FAITHFULLY
            // at `a_load`, but proved by `selectStoreSame` instantiated at `a_store`: the
            // kernel accepts it iff `a_load ≡ a_store` by DEFEQ (both concrete-cons addresses
            // reduce to the same pointer bits) — so a genuine store/load ALIAS mismatch is
            // KERNEL-REJECTED, never a false [PROVED].
            let ra_store = reflect_mem(store_addr, bit_axioms)?;
            let ra_load = reflect_mem(load_addr, bit_axioms)?;
            let rv = reflect_mem(val, bit_axioms)?;
            let a_store = kx::evalf(ra_store.core);
            let a_load = kx::evalf(ra_load.core);
            let v_list = kx::evalf(rv.core.clone());
            let m = kx::opaque_mem();
            // Faithful value: read at a_load from a store at a_store.
            let sel_term =
                kx::bv_select(kx::bv_store(m.clone(), a_store.clone(), v_list.clone()), a_load);
            let bvf = kx::leaf(sel_term);
            let core = rv.core;
            // selectStoreSame m a_store v : bvSelect (bvStore m a_store v) a_store = v ;
            // typechecks against `sel_term = v` iff a_load ≡ a_store.
            let proof = kx::select_store_same(m, a_store, v_list);
            Some(Reflected { bvf, core, proof })
        }
        _ => None,
    }
}

/// THE MEMORY STORE-LOAD [PROVED] DISCHARGE. `machine_out == auto` where auto is a
/// store-load roundtrip `Select(Store(MEM, a, v), a)` (possibly under readout wrappers).
/// Reflects BOTH sides via `reflect_mem` (concrete-cons leaves + faithful wrappers +
/// the `selectStoreSame` bridge) and discharges `evalf(machine.bvf) = evalf(auto.bvf)`
/// through the shared core by `Eq.trans` — the kernel's defeq REDUCES both cores to the
/// SAME concrete byte-cons (keyed by the shared operand, so a divergent-operand read is
/// KERNEL-REJECTED). Returns `Some(label)` iff the kernel `check_type` SUCCEEDS; `None`
/// on any non-match / reduction failure / rejection (→ [VALIDATED], never a false [PROVED]).
pub(crate) fn try_mem_store_load_discharge(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    if !formula_contains_select(auto) {
        return None;
    }
    let mut bit_axioms: Vec<String> = Vec::new();
    let rm = reflect_mem(machine_out, &mut bit_axioms)?;
    let ra = reflect_mem(auto, &mut bit_axioms)?;
    let goal = kx::eq_list(kx::evalf(rm.bvf.clone()), kx::evalf(ra.bvf.clone()));
    let sym_ra = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
        [kx::list_bool(), kx::evalf(ra.bvf.clone()), kx::evalf(ra.core.clone()), ra.proof],
    );
    let discharge = kx::eq_trans_list(
        kx::evalf(rm.bvf),
        kx::evalf(rm.core),
        kx::evalf(ra.bvf),
        rm.proof,
        sym_ra,
    );
    let result = run_recheck_thread("trust-mem-store-load", move || {
        let env = eq_discharge_env(&bit_axioms).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();
    result.map(|()| "Clean.BVC.selectStoreSame+readout-reduction (memory store-load)".to_string())
}

// ── Test-support surface (used by verify_output's B2b/B4 tests) ────────────────
#[cfg(test)]
pub(crate) mod test_support {
    use super::{Reflected, discharge_env as denv, reflect_formula as reflect};
    use clean_kernel::{Environment, Expr};
    use trust_types::Formula;

    /// Reflect a Formula (collecting leaf axioms internally).
    pub(crate) fn reflect_formula(f: &Formula) -> Result<Reflected, String> {
        let mut leaves = Vec::new();
        reflect(f, &mut leaves)
    }
    /// Does `reflect_mem` accept this formula? (true iff Some).
    pub(crate) fn reflect_mem_ok(f: &Formula) -> bool {
        let mut ax = Vec::new();
        super::reflect_mem(f, &mut ax).is_some()
    }
    pub(crate) fn mem_discharge(m: &Formula, a: &Formula) -> Option<String> {
        super::try_mem_store_load_discharge(m, a)
    }
    /// Env with the BVC layer + the given symbolic leaves.
    pub(crate) fn env_with_leaves(leaves: &[(&str, u32)]) -> Environment {
        let owned: Vec<(String, u32)> =
            leaves.iter().map(|(n, w)| ((*n).to_string(), *w)).collect();
        denv(&owned).expect("discharge_env")
    }
    pub(crate) fn contains_wrapper(e: &Expr) -> bool {
        super::reflection_contains_wrapper(e)
    }
}
