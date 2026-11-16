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

use std::fmt;
use std::sync::{Condvar, LazyLock, Mutex};

/// Stack for the kernel `check_type` of the discharge (deep `bvfEval` reduction
/// over 32/64-bit `List Bool` literals) — mirror the slow path's big stack.
use clean_auto::proved_gate::RECHECK_STACK_BYTES;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, Level, TypeChecker};
use trust_types::{Formula, Sort};

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

/// Run `route` on a fresh [`RECHECK_STACK_BYTES`] stack on the calling thread.
///
/// The routes reflect a Formula by recursion, one frame per node, and build
/// and drop kernel terms as deep, before any kernel check reaches the pool. On
/// the caller's own stack a deep Formula overflowed it and aborted the process
/// instead of declining (a 2 MiB thread, a 16-deep left-nested `^` chain, in a
/// debug build). The stack is switched, not the thread, so thread-locals (the
/// test hooks among them) and panics behave as they did on the caller's stack.
fn on_route_stack<T>(route: impl FnOnce() -> T) -> T {
    stacker::grow(RECHECK_STACK_BYTES, route)
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
    /// The raw Formula variable identity is one string component. Parsing it
    /// as a dotted declaration name would identify numeric components such
    /// as `01` and `1`, so a kernel goal could mention a different variable.
    pub fn leaf_name(name: &str, width: u32) -> Name {
        Name::anon().str(format!("BVC_LEAF_{name}_{width}"))
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
    /// The GENERAL two-sided OR congruence — the sibling of [`and_cong`] /
    /// [`xor_cong`]. [`or_cong2`] above fixes the LEFT operand, which covers the
    /// `Orr Wd, WZR, Ws` register-move wrapper and nothing else; this one covers
    /// a machine `Orr` with two real operands, i.e. a user-level `|`.
    pub fn or_cong(a: Expr, ap: Expr, b: Expr, bp: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.bvf_or_cong"), [a, ap, b, bp, ha, hb])
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
    /// The CALLER-PROVIDED memory `BVC_MEM_{key}` — an OPAQUE axiom of type
    /// `List Bool → List Bool` (registered by `discharge_env`). Opaque is the whole
    /// point: a read from it is stuck, so the only way two reads discharge against
    /// each other is `selectAddrCong` on defeq addresses.
    pub fn mem_const(key: &str) -> Expr {
        Expr::const_str(&format!("BVC_MEM_{key}"))
    }
    /// `selectAddrCong m a a' (h : a = a') : bvSelect m a = bvSelect m a'` — the
    /// address congruence at a FIXED array (the caller-provided-memory keystone).
    pub fn select_addr_cong(m: Expr, a: Expr, ap: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::const_str("Clean.BVC.selectAddrCong"), [m, a, ap, h])
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

/// Is `f` STRUCTURALLY GUARANTEED to contain no memory write?
///
/// FAIL-CLOSED BY CONSTRUCTION: this is a whitelist of the node kinds
/// [`reflect_formula`] itself recurses through, and every other node — including
/// every node this walker does not know how to look inside — answers `false`
/// ("might store"). Adding a `Formula` variant therefore CANNOT silently widen
/// the read-only fragment; it can only keep it closed until someone adds the
/// variant here deliberately. `Formula::Store` is the one explicit `false`.
///
/// This is the side condition for the bare-read arm of `reflect_formula`. It has
/// to be a property of the WHOLE obligation, not of the read: the hazard is that
/// one syntactic memory name denotes the pre-state on one side and a post-store
/// state on the other, which modelling both as the same opaque constant would
/// silently equate. No write anywhere ⟹ no such divergence.
fn is_store_free(f: &Formula) -> bool {
    match f {
        // Leaves.
        Formula::Var(..) | Formula::SymVar(..) | Formula::BitVec { .. } => true,
        // THE point of the walk.
        Formula::Store(..) => false,
        // Unary.
        Formula::Not(x)
        | Formula::BvNot(x, _)
        | Formula::BvZeroExt(x, _)
        | Formula::BvSignExt(x, _) => is_store_free(x),
        Formula::BvExtract { inner, .. } => is_store_free(inner),
        // Binary.
        Formula::BvAdd(l, r, _)
        | Formula::BvSub(l, r, _)
        | Formula::BvMul(l, r, _)
        | Formula::BvUDiv(l, r, _)
        | Formula::BvSDiv(l, r, _)
        | Formula::BvURem(l, r, _)
        | Formula::BvSRem(l, r, _)
        | Formula::BvAnd(l, r, _)
        | Formula::BvOr(l, r, _)
        | Formula::BvXor(l, r, _)
        | Formula::BvShl(l, r, _)
        | Formula::BvLShr(l, r, _)
        | Formula::BvAShr(l, r, _) => is_store_free(l) && is_store_free(r),
        Formula::BvConcat(l, r) | Formula::Select(l, r) => is_store_free(l) && is_store_free(r),
        // EVERYTHING ELSE — including nodes whose children this walker cannot
        // see into — is treated as possibly-storing.
        _ => false,
    }
}

/// Reflection state threaded through [`reflect_formula`]: the symbolic leaves and
/// caller memories that need axioms, plus the ONE policy bit that decides whether
/// a bare memory read (a load from state the function never wrote) is in the
/// fragment.
pub(crate) struct ReflectCtx {
    /// `(name, width)` of each symbolic register leaf → a `BVC_LEAF_*` axiom.
    pub(crate) leaves: Vec<(String, u32)>,
    /// Each distinct caller-provided memory read → a `BVC_MEM_*` array axiom.
    pub(crate) mems: Vec<String>,
    /// May a bare `Select(MEM, a)` be admitted? See [`ReflectCtx::for_obligation`].
    caller_memory_readable: bool,
    /// The add-commutation retry ([`ReflectCtx::commuting`]): variables are
    /// rendered at their width and `Add` operands are put in one order, each
    /// reordering justified by a kernel theorem. Off everywhere else.
    commuting: bool,
    /// How many `Add` nodes the commuting reflection reordered.
    add_swaps: usize,
    /// The strength-reduction retry ([`ReflectCtx::strength`]): a standalone
    /// `ZeroExt` is in the fragment, every wrapper tag of the GOAL (`bvf`) is
    /// built from the Formula's own reflection rather than from a rewritten
    /// core, and (with `strength_steps`) the `strength` rewrite steps are
    /// spliced into the cores. Off everywhere else.
    strength: bool,
    /// Whether the `strength` step builders run. Always set with `strength`
    /// outside tests; a test turns it off to show the goal does not depend on
    /// them (`strength_dry`).
    strength_steps: bool,
    /// The strength theorem each spliced step instantiates, in order.
    strength_used: Vec<&'static str>,
    /// How many strength steps were spliced (at most `strength::MAX_REWRITES`).
    strength_rewrites: usize,
    /// BRANCH-SPLIT-1: the `branch_reflect` arms (bit-vector `Ite`, the
    /// faithful `BvUDiv`) are active. Off in every legacy context.
    branching: bool,
    /// Whether the `branch_reflect` step builders run (ground selection, the
    /// division guard, `mul_add_self`, `sub_zero`). Off when the goal is built
    /// ([`ReflectCtx::branching_goal`]).
    branching_steps: bool,
    /// How many branch steps were spliced (at most
    /// `branch_reflect::BRANCH_MAX_REWRITES`), on their own counter.
    branch_rewrites: usize,
    /// A branch step was refused because the counter was full.
    branch_cap_hit: bool,
    /// CANCEL-1: whether the `cancel` step builder runs at a `Sub` node. Set
    /// only by [`ReflectCtx::cancel`], and effective only together with
    /// `strength_steps` (the hook tests both), so every other context,
    /// strength and branching included, reflects exactly as before.
    cancel_steps: bool,
    /// CONSTDIV-1: the `const_div::umulh` goal arm (the 128-bit
    /// multiply-high) is active. Set only by the `const_div` contexts (the
    /// step-(4) rewrite and the step-(5) route); off in every other context.
    const_div: bool,
    /// Whether the `const_div` step builders run (multiplier fold, magic
    /// quotient, remainder tail). Off when the goal is built.
    const_div_steps: bool,
}

impl ReflectCtx {
    /// The FAIL-CLOSED constructor: caller memory is NOT readable. Any caller that
    /// has not proved the read-only side condition gets this, and a bare read is
    /// refused exactly as it was before this fragment was widened.
    pub(crate) fn closed() -> Self {
        Self {
            leaves: Vec::new(),
            mems: Vec::new(),
            caller_memory_readable: false,
            commuting: false,
            add_swaps: 0,
            strength: false,
            strength_steps: false,
            strength_used: Vec::new(),
            strength_rewrites: 0,
            branching: false,
            branching_steps: false,
            branch_rewrites: 0,
            branch_cap_hit: false,
            cancel_steps: false,
            const_div: false,
            const_div_steps: false,
        }
    }

    /// The reflection the branch split states its goal with: the strength
    /// reflection with every step builder off, plus the `branch_reflect`
    /// arms. Nothing in it depends on a rewrite step.
    fn branching_goal() -> Self {
        let mut ctx = Self::strength();
        ctx.strength_steps = false;
        ctx.branching = true;
        ctx
    }

    /// The reflection the branch split proves with: [`ReflectCtx::strength`]
    /// plus the `branch_reflect` arms and their steps. Its `bvf` is the goal's
    /// (`branching_bvf_matches_the_goal`).
    fn branching() -> Self {
        let mut ctx = Self::strength();
        ctx.branching = true;
        ctx.branching_steps = true;
        ctx
    }

    /// The reflection of the strength-reduction retry: the commuting
    /// reflection plus the standalone `ZeroExt` arm, Formula-only goal tags
    /// and the rewrite steps of `strength`. Caller memory stays unreadable.
    fn strength() -> Self {
        let mut ctx = Self::commuting();
        ctx.strength = true;
        ctx.strength_steps = true;
        ctx
    }

    /// The reflection of the additive-cancellation retry (CANCEL-1):
    /// [`ReflectCtx::strength`] plus the `cancel` step at `Sub` nodes.
    /// [`ReflectCtx::strength`] keeps `cancel_steps` off, so the strength route
    /// is unchanged by it.
    fn cancel() -> Self {
        let mut ctx = Self::strength();
        ctx.cancel_steps = true;
        ctx
    }

    /// [`ReflectCtx::cancel`] with every step builder off (strength's and the
    /// cancel step): the goal it reflects must be byte-identical.
    #[cfg(test)]
    fn cancel_dry() -> Self {
        let mut ctx = Self::cancel();
        ctx.strength_steps = false;
        ctx.cancel_steps = false;
        ctx
    }

    /// [`ReflectCtx::strength`] with the step builders off: the goal it
    /// reflects must be byte-identical (T-U10).
    #[cfg(test)]
    fn strength_dry() -> Self {
        let mut ctx = Self::strength();
        ctx.strength_steps = false;
        ctx
    }

    /// Splice `steps` (each `before` the current core) into a node whose goal
    /// is `bvf`, whose core is `core` and whose proof is
    /// `bvfEval bvf = bvfEval core`. A step whose `before` is not the current
    /// core, or one past `strength::MAX_REWRITES`, is not spliced: the core
    /// then stays where it is, and the cores of the two sides fail to meet.
    fn splice(
        &mut self,
        bvf: &Expr,
        steps: Vec<strength::Step>,
        core: &mut Expr,
        proof: &mut Expr,
    ) {
        for step in steps {
            if step.before != *core || self.strength_rewrites >= strength::MAX_REWRITES {
                return;
            }
            *proof = step.chain(bvf, proof.clone());
            *core = step.core;
            self.strength_used.push(step.theorem);
            self.strength_rewrites += 1;
        }
    }

    /// Do the strength step builders run at this node?
    fn strength_steps(&self) -> bool {
        self.strength && self.strength_steps
    }

    /// The reflection of the add-commutation retry. Caller memory stays
    /// unreadable (the retry covers scalar obligations only), so a memory read
    /// is refused exactly as under [`ReflectCtx::closed`].
    fn commuting() -> Self {
        let mut ctx = Self::closed();
        ctx.commuting = true;
        ctx
    }

    /// Admit bare reads for THIS obligation iff NEITHER side writes memory.
    ///
    /// A read-only body reads the same untouched pre-state on both sides, so two
    /// reads at provably-equal addresses are equal by `Clean.BVC.selectAddrCong` —
    /// a congruence over the address at a FIXED array, which never interprets the
    /// array. The moment a store exists anywhere the argument collapses: a read
    /// could be before or after it, and `selectAddrCong` says nothing about that.
    /// Aliasing and read-after-write stay OUT of the fragment.
    pub(crate) fn for_obligation(machine: &Formula, auto: &Formula) -> Self {
        // START CLOSED, then open only on evidence — never the other way round.
        let mut ctx = Self::closed();
        ctx.caller_memory_readable = is_store_free(machine) && is_store_free(auto);
        ctx
    }
}

/// The stable identity of a memory term, used to name its `BVC_MEM_*` axiom.
///
/// Only a NAMED, ARRAY-SORTED variable qualifies. Two bare reads discharge
/// against each other only when they name the same memory, so this key is what
/// separates "the caller's memory" from anything else; a derived or unnamed
/// memory term has no such identity and is refused. Requiring `Sort::Array`
/// keeps the key from being minted for a term that is not a memory at all.
fn memory_key(f: &Formula) -> Option<String> {
    match f {
        Formula::Var(name, Sort::Array(..)) => Some(name.clone()),
        _ => None,
    }
}

/// Reflect a gate `Formula` (add@N fragment) into a `BvF` Expr + stripped core +
/// the `bvfEval`-headed kernel proof. PURELY STRUCTURAL / NON-FOLDING. Returns
/// `Err` for any node outside the recognized fragment (→ caller falls through).
/// Also records, in `ctx`, the symbolic leaves and caller memories that need an
/// axiom to state the obligation.
pub(crate) fn reflect_formula(f: &Formula, ctx: &mut ReflectCtx) -> Result<Reflected, String> {
    let out = reflect_node(f, ctx)?;
    // BRANCH-SPLIT-1: the `mul_add_self` / `sub_zero` steps run after a node is
    // reflected, under `branching_steps` only; every legacy context returns
    // the node as reflected.
    let out = if ctx.branching_steps { branch_reflect::post_step(f, out, ctx) } else { out };
    // CONSTDIV (stage A): the magic-quotient and remainder-tail steps, under
    // `const_div_steps` only.
    if ctx.const_div_steps { Ok(const_div::post_step(f, out, ctx)) } else { Ok(out) }
}

/// One node of [`reflect_formula`] (children go back through it).
fn reflect_node(f: &Formula, ctx: &mut ReflectCtx) -> Result<Reflected, String> {
    match f {
        // CONSTDIV (stage A): exactly the 64-bit multiply-high shape, under
        // `ctx.const_div` only (`const_div::umulh`).
        Formula::BvExtract { high: 127, low: 64, .. } if ctx.const_div => const_div::umulh(f, ctx),
        // BRANCH-SPLIT-1: the bit-vector `Ite` and the faithful unsigned
        // division, active only under `ctx.branching` (`branch_reflect`).
        Formula::Ite(c, a, e) if ctx.branching => branch_reflect::ite(c, a, e, ctx),
        Formula::BvUDiv(l, r, _w) if ctx.branching => branch_reflect::udiv(l, r, ctx),
        Formula::BvExtract { inner, high, low } if *low != 0 && ctx.branching => {
            branch_reflect::high_extract(inner, *high, *low, ctx)
        }
        Formula::BvSignExt(x, k) if ctx.branching => branch_reflect::sign_ext(x, *k, ctx),
        Formula::Var(name, Sort::BitVec(w)) => {
            ctx.leaves.push((name.clone(), *w));
            // The commuting retry needs the variable's width in the term: the
            // length premise of `addRecM_comm` is unprovable for an opaque
            // `List Bool` (see `add_comm`). Everything else keeps the opaque leaf.
            let leaf_list = if ctx.commuting {
                add_comm::bit_leaf(name, *w)
            } else {
                Expr::const_(kx::leaf_name(name, *w), vec![])
            };
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
            let rx = reflect_formula(r, ctx)?;
            if ctx.strength {
                return Ok(strength_zero_wrapper(rx, kx::add, kx::add_cong, kx::add_zero_id));
            }
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
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
            let bvf = kx::add(rl.bvf.clone(), rr.bvf.clone());
            let mut core = kx::add(rl.core.clone(), rr.core.clone());
            let mut proof =
                kx::add_cong(rl.bvf, rl.core.clone(), rr.bvf, rr.core.clone(), rl.proof, rr.proof);
            // THE STRENGTH RETRY: `(x + y) + x * c1` becomes `x * (c1 + 1) + y`
            // (`Trust.BVS.collect_add`) before the operands are ordered.
            // The operands the ordering below looks at are those of the core as
            // it now stands.
            let (mut op_l, mut op_r) = (rl.core, rr.core);
            if ctx.strength_steps()
                && let Some(step) = strength::add_step(&op_l, &op_r)
            {
                ctx.splice(&bvf, vec![step], &mut core, &mut proof);
                let Some(operands) = add_operands(&core) else {
                    return Ok(Reflected { bvf, core, proof });
                };
                (op_l, op_r) = operands;
            }
            // THE COMMUTED RETRY (PKG-C5c). `bvf` above is the Formula's own
            // operand order and is what the goal is stated over; only the CORE,
            // the waypoint the two sides meet at, takes the canonical order, and
            // the step from one order to the other is an instance of the kernel
            // theorem `Trust.BVC.addRecM_comm` under a proved equal-length
            // premise. No step is available (`None`) for an Add neither of whose
            // operands is a multiply, or for an operand whose length `add_comm`
            // cannot prove; the Add then stays in source order.
            if ctx.commuting
                && let Some(step) = add_comm::canonical_step(&op_l, &op_r)
            {
                let swapped = kx::add(op_r, op_l);
                let proof = kx::eq_trans_list(
                    kx::evalf(bvf.clone()),
                    kx::evalf(core),
                    kx::evalf(swapped.clone()),
                    proof,
                    step,
                );
                ctx.add_swaps += 1;
                return Ok(Reflected { bvf, core: swapped, proof });
            }
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvConcat(high, low) => {
            memory_reflection::width(f).ok_or("reflect: malformed concatenation widths")?;
            let high = reflect_formula(high, ctx)?;
            let low = reflect_formula(low, ctx)?;
            let make = |h, l| Expr::apps(Expr::const_str("Clean.BVC.BvF.Concat"), [h, l]);
            let bvf = make(high.bvf.clone(), low.bvf.clone());
            let core = make(high.core.clone(), low.core.clone());
            let proof = Expr::apps(
                Expr::const_str("Clean.BVC.bvf_concat_cong"),
                [high.bvf, high.core, low.bvf, low.core, high.proof, low.proof],
            );
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvSub(l, r, _w) => {
            // SUB — the exact add analogue (traced #40-followup): BvSub core in the
            // same coercion wrappers. bvf_sub_cong is the bvfEval-headed Sub congruence.
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
            let bvf = kx::sub(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::sub(rl.core.clone(), rr.core.clone());
            if ctx.strength_steps()
                && let Some(step) = strength::sub_step(&rl.core, &rr.core)
            {
                // THE STRENGTH RETRY: `(x * c1 + y) - x` becomes
                // `x * (c1 - 1) + y` (`Trust.BVS.collect_sub`), an `Add`
                // whose operands are then ordered as at an `Add` node.
                let mut core = core;
                let mut proof = kx::sub_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
                ctx.splice(&bvf, vec![step], &mut core, &mut proof);
                if let Some((op_l, op_r)) = add_operands(&core)
                    && let Some(swap) = add_comm::canonical_step(&op_l, &op_r)
                {
                    let swapped = kx::add(op_r, op_l);
                    proof = kx::eq_trans_list(
                        kx::evalf(bvf.clone()),
                        kx::evalf(core),
                        kx::evalf(swapped.clone()),
                        proof,
                        swap,
                    );
                    core = swapped;
                    ctx.add_swaps += 1;
                }
                return Ok(Reflected { bvf, core, proof });
            }
            if ctx.strength_steps()
                && ctx.cancel_steps
                && let Some(step) = cancel::sub_cancel_step(&rl.core, &rr.core)
            {
                // THE CANCEL RETRY (CANCEL-1): `(c + x) - c` becomes `x`
                // (`Trust.BVA.add_sub_cancel`). `x` is a core this reflection
                // already built, its own `Add` operands already ordered.
                let mut core = core;
                let mut proof = kx::sub_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
                ctx.splice(&bvf, vec![step], &mut core, &mut proof);
                return Ok(Reflected { bvf, core, proof });
            }
            let proof = kx::sub_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvAnd(l, r, _w) => {
            // AND — exact add analogue (traced #41): native BvAnd(wn0,wn1) (operands
            // ALIGNED, not commuted) in the same coercion wrappers. Pure coercion-id.
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
            let bvf = kx::and(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::and(rl.core.clone(), rr.core.clone());
            let proof = kx::and_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvXor(l, r, _w) => {
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
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
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
            let bvf = kx::mul(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::mul(rl.core.clone(), rr.core.clone());
            let proof = kx::mul_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvUDiv(l, r, _w) => {
            // NOT FAITHFUL AT /0: `BvF.Div` is `bvDiv`, whose value at a zero
            // divisor is not SMT `bvudiv`'s all-ones. This arm is sound only
            // under congruence (both sides carry the same `Div`, whatever it
            // computes). `branch_reflect::udiv` is the faithful reflection.
            // UNSIGNED DIV — the exact mul analogue: the LIR `udiv` reflects to `BvF.Div`
            // over the SAME operand wrappers the IR `BvUDiv` carries; `bvf_div_cong` cancels
            // the shared `BvF.Div` by congruence (the quotient VALUE is not load-bearing —
            // both sides compute the identical `bvDiv`). SIGNED FOOTGUN GUARD: `BvSDiv` is
            // DELIBERATELY NOT reflected (it stays in the `other` Err arm) — SDIV rounds toward
            // zero, which differs from `bvDiv`'s `Nat.div` floor for negatives, so signed div
            // must NEVER reflect to `BvF.Div`; it correctly stays [VALIDATED].
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
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
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
            let bvf = kx::shl(rl.bvf.clone(), rr.bvf.clone());
            let mut core = kx::shl(rl.core.clone(), rr.core.clone());
            // THE STRENGTH RETRY: a shift by a constant is a multiply by a
            // power of two (`Trust.BVS.shl_mul`), after the AArch64 `lsl #k`
            // alias of UBFM has dropped its zero-extension
            // (`Trust.BVS.shl_hi_out`).
            let steps = if ctx.strength_steps() {
                strength::shl_steps(&rl.core, &rr.core)
            } else {
                Vec::new()
            };
            let mut proof = kx::shl_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            ctx.splice(&bvf, steps, &mut core, &mut proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvLShr(l, r, _w) => {
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
            let bvf = kx::lshr(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::lshr(rl.core.clone(), rr.core.clone());
            let proof = kx::lshr_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvAShr(l, r, _w) => {
            let rl = reflect_formula(l, ctx)?;
            let rr = reflect_formula(r, ctx)?;
            let bvf = kx::ashr(rl.bvf.clone(), rr.bvf.clone());
            let core = kx::ashr(rl.core.clone(), rr.core.clone());
            let proof = kx::ashr_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvOr(lhs, rhs, _w) => {
            if let Formula::BitVec { value: 0, .. } = &**lhs {
                let rx = reflect_formula(rhs, ctx)?;
                if ctx.strength {
                    return Ok(strength_zero_wrapper(rx, kx::or, kx::or_cong, kx::or_zero_id));
                }
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
                // THE GENERAL TWO-OPERAND `Orr`, i.e. a user-level `|`.
                //
                // The arm above handles only `BvOr(BitVec{0}, x)` — the
                // `Orr Wd, WZR, Ws` register-move wrapper — because for a long
                // time `Clean.BVC.bvf_or_cong2` (left operand FIXED) was the only
                // OR congruence that existed. Every other binary op has had the
                // general two-sided form, so `|` was the single binary shape with
                // no O(1) coercion-identity route: it fell out of this function
                // with an `Err` and back onto bit-blast + SAT + kernel re-check.
                //
                // (c) MEASURED before `bvf_or_cong` existed, one function through
                // `--emit=link`: `(x ^ y) ^ (x & y)` cost 2.76 s / 0.99 GB while
                // `(x ^ y) | (x & y)` — the identical shape, one instruction
                // different — cost 20.94 s / 27.41 GB, and the five-op form
                // reached 54.78 GB. The ay-side export is NOT the cause and was
                // measured to rule it out: the OR and XOR bit-blasts are
                // identical in size (225 vars / 161 lemmas / 642 clauses / 225
                // steps) and in time (~30 ms). The whole difference was taking
                // this fallback at all.
                //
                // Structurally this is exactly the `BvAnd`/`BvXor` arms above.
                let rl = reflect_formula(lhs, ctx)?;
                let rr = reflect_formula(rhs, ctx)?;
                let bvf = kx::or(rl.bvf.clone(), rr.bvf.clone());
                let core = kx::or(rl.core.clone(), rr.core.clone());
                let proof = kx::or_cong(rl.bvf, rl.core, rr.bvf, rr.core, rl.proof, rr.proof);
                Ok(Reflected { bvf, core, proof })
            }
        }
        // The scalar reflector retains its old store-free policy. Production
        // memory obligations instead use the original-term memory reflector.
        Formula::Select(mem, load_addr) => {
            if matches!(&**mem, Formula::Store(..)) {
                return Err("reflect: storing memory requires the original-term memory path".into());
            }
            // ── BARE MEMORY READ — a load through a CALLER-PROVIDED pointer ────
            //
            // `Select(MEM, a)` over a memory the function never wrote is what a
            // `&T` parameter dereference reflects to, and it is what used to put
            // reference parameters outside the fragment entirely: the store-load
            // arm above needs an immediately-covering store to bridge through
            // `selectStoreSame`, and there is no store.
            //
            // It is ADMITTED here under ONE side condition, checked by the caller
            // over the WHOLE obligation and defaulted to refusal
            // (`ReflectCtx::closed`): the body performs NO STORE on either side.
            // Then both sides read the same untouched pre-state, and the two reads
            // are equal as soon as their ADDRESSES are — `Clean.BVC.selectAddrCong`
            // transports that address equality under `bvSelect` at a fixed array.
            //
            // The memory is an OPAQUE `BVC_MEM_*` AXIOM, deliberately NOT the
            // closed `opaque_mem` (`fun _ => List.nil`) the store-load path uses.
            // `opaque_mem` is safe there only because `selectStoreSame` never
            // inspects it; here it would REDUCE — `bvSelect (fun _ => nil) a ⟶ nil`
            // for EVERY `a` — and every bare read in the universe would discharge
            // against every other. With an axiom the read is stuck, the ONLY bridge
            // is the address congruence, and a read at a different address (or from
            // a differently-named memory) leaves the two cores non-defeq and is
            // KERNEL-REJECTED.
            if !ctx.caller_memory_readable {
                return Err(
                    "reflect: Select over non-Store (bare memory read outside fragment)".into()
                );
            }
            let Some(key) = memory_key(mem) else {
                return Err(
                    "reflect: Select over an unnamed memory (bare memory read outside fragment)"
                        .into(),
                );
            };
            ctx.mems.push(key.clone());
            let ra = reflect_formula(load_addr, ctx)?;
            let m = kx::mem_const(&key);
            let a_bvf = kx::evalf(ra.bvf);
            let a_core = kx::evalf(ra.core);
            // bvf / core are Leaf-wrapped reads at the bvf-side / core-side address;
            // `bvfEval (Leaf l) ⟶ l`, so the proof below IS the required
            // `bvfEval(bvf) = bvfEval(core)`.
            let bvf = kx::leaf(kx::bv_select(m.clone(), a_bvf.clone()));
            let core = kx::leaf(kx::bv_select(m.clone(), a_core.clone()));
            let proof = kx::select_addr_cong(m, a_bvf, a_core, ra.proof);
            Ok(Reflected { bvf, core, proof })
        }
        Formula::BvExtract { inner, high, low } => {
            if *low != 0 {
                return Err("reflect: BvExtract low != 0 (outside fragment)".into());
            }
            memory_reflection::width(f).ok_or("reflect: invalid extract bounds or widths")?;
            if let Formula::BvZeroExt(z, k) = &**inner {
                if high.checked_add(1) != memory_reflection::width(z) {
                    return Err("reflect: extract width differs from zero-extension input".into());
                }
                let rz = reflect_formula(z, ctx)?;
                let kn = kx::nat_lit(*k);
                if ctx.strength {
                    return Ok(strength_extract_zext(rz, kn));
                }
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
                let branch_steps_before = ctx.branch_rewrites;
                let ri = reflect_formula(inner, ctx)?;
                // This arm drops the child's core, so a branch step under it
                // would be counted without appearing in the proof.
                if ctx.branching_steps && ctx.branch_rewrites != branch_steps_before {
                    return Err("reflect: extract over a branch step (outside fragment)".into());
                }
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
        // A STANDALONE zero-extension, under strength only (the s09 `rung`
        // return `ZeroExt(h(x), 32)` and the UBFM operand
        // `ZeroExt(Extract(x, 62, 0), 1)`): a congruence, with the extension
        // amount a `succ` chain of at most 63. Outside strength it stays out of
        // the fragment, as before.
        Formula::BvZeroExt(z, k) if ctx.strength => {
            if !(1..=63).contains(k) || !memory_reflection::width(f).is_some_and(|w| w <= 64) {
                return Err("reflect: zero-extension outside the strength fragment".into());
            }
            let rz = reflect_formula(z, ctx)?;
            let kn = kx::nat_lit(*k);
            Ok(Reflected {
                bvf: kx::zext(rz.bvf.clone(), kn.clone()),
                core: kx::zext(rz.core.clone(), kn.clone()),
                proof: kx::zext_cong(rz.bvf, rz.core, kn, rz.proof),
            })
        }
        other => Err(format!("reflect: Formula outside add@N reflection fragment: {other:?}")),
    }
}

/// The operands of a `BvF.Add` core.
fn add_operands(core: &Expr) -> Option<(Expr, Expr)> {
    let is_add = matches!(core.get_app_fn().kind(),
        clean_kernel::ExprKind::Const(name, _) if *name == Name::from_string("Clean.BVC.BvF.Add"));
    match core.get_app_args().as_slice() {
        [l, r] if is_add => Some(((*l).clone(), (*r).clone())),
        _ => None,
    }
}

/// A zero wrapper `op (Const (allFalse ·)) x` (`Or` or `Add` with a zero
/// left operand) under strength. The GOAL side takes its zero from the
/// Formula's own reflection, `allFalse (bvfEval x.bvf)`, never from the
/// rewritten core, so what is proved does not depend on the step builders
/// (T-U10). The proof bridges that zero to `allFalse (bvfEval x.core)` by
/// `congrArg bvAllFalse x.proof` inside the two-sided congruence `cong`, then
/// drops the wrapper with `zero_id` at the core.
fn strength_zero_wrapper(
    rx: Reflected,
    op: fn(Expr, Expr) -> Expr,
    cong: fn(Expr, Expr, Expr, Expr, Expr, Expr) -> Expr,
    zero_id: fn(Expr) -> Expr,
) -> Reflected {
    let (eval_bvf, eval_core) = (kx::evalf(rx.bvf.clone()), kx::evalf(rx.core.clone()));
    let zero_bvf = kx::const_(kx::all_false(eval_bvf.clone()));
    let zero_core = kx::const_(kx::all_false(eval_core.clone()));
    // `allFalse (eval bvf) = allFalse (eval core)`, which is
    // `bvfEval zero_bvf = bvfEval zero_core` by computation of `bvfEval (Const l)`.
    let zeros = kterm::congr_arg(
        kx::list_bool(),
        kx::list_bool(),
        eval_bvf,
        eval_core,
        Expr::const_str("Clean.BVC.bvAllFalse"),
        rx.proof.clone(),
    );
    let bvf = op(zero_bvf.clone(), rx.bvf.clone());
    let mid = op(zero_core.clone(), rx.core.clone());
    let step_a = cong(zero_bvf, zero_core, rx.bvf, rx.core.clone(), zeros, rx.proof);
    let step_b = zero_id(rx.core.clone());
    let proof = kx::eq_trans_list(
        kx::evalf(bvf.clone()),
        kx::evalf(mid),
        kx::evalf(rx.core.clone()),
        step_a,
        step_b,
    );
    Reflected { bvf, core: rx.core, proof }
}

/// `ExtractLow (ZeroExt z k) tag` (the 32-bit return readout) under strength.
/// The GOAL's length tag is the Formula's own reflection `z.bvf`, never the
/// rewritten core. The proof: congruence through the zero-extension, then
/// `congrArg (λ t. bvTakeLen t (bvfEval (ZeroExt z.core k))) z.proof` to move
/// the tag to `z.core` (`bvfEval (ExtractLow e tag)` computes to
/// `bvTakeLen (bvfEval tag) (bvfEval e)`), then `bvf_extract_zeroext_id`.
fn strength_extract_zext(rz: Reflected, kn: Expr) -> Reflected {
    let zext_bvf = kx::zext(rz.bvf.clone(), kn.clone());
    let zext_core = kx::zext(rz.core.clone(), kn.clone());
    let bvf = kx::extract(zext_bvf.clone(), rz.bvf.clone());
    let inner_eq = kx::zext_cong(rz.bvf.clone(), rz.core.clone(), kn.clone(), rz.proof.clone());
    let step_a = kx::extract_cong1(zext_bvf, zext_core.clone(), rz.bvf.clone(), inner_eq);
    let take_from = {
        let mut fr = kterm::Fresh::new();
        let (t_id, t) = fr.local();
        let body =
            Expr::apps(Expr::const_str("Clean.BVC.bvTakeLen"), [t, kx::evalf(zext_core.clone())]);
        kterm::lams(vec![(t_id, kx::list_bool())], body)
    };
    let step_m = kterm::congr_arg(
        kx::list_bool(),
        kx::list_bool(),
        kx::evalf(rz.bvf.clone()),
        kx::evalf(rz.core.clone()),
        take_from,
        rz.proof,
    );
    let step_b = kx::extract_zeroext_id(rz.core.clone(), kn);
    let at_tag_bvf = kx::evalf(kx::extract(zext_core.clone(), rz.bvf.clone()));
    let at_tag_core = kx::evalf(kx::extract(zext_core, rz.core.clone()));
    let to_core_tag =
        kx::eq_trans_list(kx::evalf(bvf.clone()), at_tag_bvf, at_tag_core.clone(), step_a, step_m);
    let proof = kx::eq_trans_list(
        kx::evalf(bvf.clone()),
        at_tag_core,
        kx::evalf(rz.core.clone()),
        to_core_tag,
        step_b,
    );
    Reflected { bvf, core: rz.core, proof }
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
pub(crate) fn discharge_env(
    leaves: &[(String, u32)],
    mems: &[String],
) -> Result<Environment, String> {
    // THE BASE IS A CONSTANT, AND IT IS THE EXPENSIVE PART.
    //
    // `Environment::with_prelude()` kernel-type-checks every prelude
    // declaration, and `init_bv_coercion()` adds the BVC layer on top. Neither
    // depends on `leaves` — only the axioms added below do — so the pair was
    // being rebuilt from scratch for EVERY obligation.
    //
    // (c) MEASURED (debug build; the ratio is the point, not the absolutes):
    // building the base costs 7.42 s and cloning it costs 878 us — **8,447x**.
    // After the `bvf_or_cong` repair put `|` on the O(1) path, a process sample
    // put essentially ALL remaining discharge-thread time in `with_prelude`, so
    // this was the entire residual cost of the fast path.
    //
    // Memoizing is sound because the base is a deterministic, immutable
    // construction: every caller CLONES it before adding its own
    // `BVC_LEAF_*` axioms, so no caller can observe another's mutation, and a
    // clone carries the same kernel-checked declarations the build produced.
    static BASE: std::sync::OnceLock<Result<Environment, String>> = std::sync::OnceLock::new();
    let base = BASE.get_or_init(|| {
        let mut env = Environment::with_prelude();
        env.init_bv_coercion().map_err(|e| format!("init_bv_coercion: {e:?}"))?;
        Ok(env)
    });
    let mut env = base.as_ref().map_err(Clone::clone)?.clone();
    for (name, w) in leaves {
        // idempotent: a repeated (name,w) is fine (add_decl of an existing axiom
        // with the same type is a no-op-or-error we tolerate).
        let _ = env.add_decl(clean_kernel::Declaration::Axiom {
            name: kx::leaf_name(name, *w),
            level_params: vec![],
            type_: kx::list_bool(),
        });
    }
    // The caller-provided memories: OPAQUE `List Bool → List Bool` axioms, one per
    // distinct memory name. Same status as the leaf axioms — they only state the
    // obligation and are NOT dependencies of `Clean.BVC.selectAddrCong` (whose
    // axiom closure stays empty), so the [PROVED] grade's trusted closure is
    // unchanged. Opaque is load-bearing: an INTERPRETED memory would let reads at
    // different addresses reduce to the same value.
    for name in mems {
        let _ = env.add_decl(clean_kernel::Declaration::Axiom {
            name: Name::from_string(&format!("BVC_MEM_{name}")),
            level_params: vec![],
            type_: Expr::arrow(kx::list_bool(), kx::list_bool()),
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

/// An exact 32-bit operand and identity wrappers around that SAME value. Unlike
/// `operand_key`, this must not erase nested truncation: low16(X) widened back
/// to 32 bits is not W(X), and W(X) != 0 cannot justify dividing by low16(X).
/// The tracked width is the actual intermediate Formula width; the value always
/// fits in 32 bits. This deliberately accepts no arithmetic or sign extension.
fn div_operand_identity(f: &Formula) -> Option<(String, u32)> {
    match f {
        Formula::Var(_, Sort::BitVec(32)) => Some((operand_key(f)?, 32)),
        Formula::BvExtract { inner, high: 31, low: 0 } => {
            if matches!(&**inner, Formula::Var(_, Sort::BitVec(64))) {
                return Some((operand_key(f)?, 32));
            }
            let (key, width) = div_operand_identity(inner)?;
            (width >= 32).then_some((key, 32))
        }
        Formula::BvZeroExt(inner, extra) => {
            let (key, width) = div_operand_identity(inner)?;
            let width = width.checked_add(*extra)?;
            (width <= 128).then_some((key, width))
        }
        Formula::BvOr(left, right, width) => {
            let other = match (&**left, &**right) {
                (Formula::BitVec { value: 0, width: zero_width }, other) if zero_width == width => {
                    other
                }
                (other, Formula::BitVec { value: 0, width: zero_width }) if zero_width == width => {
                    other
                }
                _ => return None,
            };
            let (key, actual_width) = div_operand_identity(other)?;
            (actual_width == *width).then_some((key, actual_width))
        }
        _ => None,
    }
}

fn div_operand_key(f: &Formula) -> Option<String> {
    let (key, width) = div_operand_identity(f)?;
    if width != 32 {
        return None;
    }
    // Kernel Name::from_string normalizes numeric dotted components: raw
    // Formula variables X.1.tail and X.01.tail must not become the same opaque
    // bit constants. Fixed two-digit UTF-8 byte encoding is injective and has
    // no dots, so the kernel goal retains exact Formula variable identity.
    let encoded: String = key.as_bytes().iter().map(|byte| format!("{byte:02x}")).collect();
    Some(format!("DIV32_{encoded}"))
}

/// Reflect exactly the supplied nonzero predicate. Do not invent a premise,
/// simplify an unrelated Boolean expression, or drop a stronger/weaker clause.
fn div_precondition_key(pre: &Formula) -> Option<String> {
    let Formula::Not(inner) = pre else { return None };
    let Formula::Eq(left, right) = &**inner else { return None };
    let operand = match (&**left, &**right) {
        (Formula::BitVec { value: 0, width: 32 }, operand)
        | (operand, Formula::BitVec { value: 0, width: 32 }) => operand,
        _ => return None,
    };
    div_operand_key(operand)
}

/// THE UNSIGNED-DIV CONDITIONAL O(1) DISCHARGE. Recognizes the gate's REAL udiv obligation:
///   auto    = BvUDiv(Wa, Wb)
///   machine = W_zext( Ite(Eq(Wb', 0@w), 0@w, BvUDiv(Wa', Wb')) )   (the architectural ÷0=0 guard)
/// Under the gate precondition `b != 0` (reflected as `bvIsZero <b> = false`), `divGuardBridge`
/// collapses the machine `Ite` to its `BvUDiv` else-branch = auto. THE PROOF is `divGuardBridge`
/// PARTIALLY applied at the MACHINE operand bit-lists, leaving the `b != 0` hypothesis OPEN — so
/// the discharge term has the CONDITIONAL type `(bvIsZero <b2> = false) -> (mach_val = bvDiv <a2><b2>)`,
/// The goal hypothesis is reflected independently from the ACTUAL supplied
/// precondition. Kernel checking must unify it with that open hypothesis; the
/// machine's divisor cannot supply an assumption absent from the input claim.
/// OPERAND-IDENTITY KERNEL-TIED (eq/ult discipline): the
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
/// ay's prior width-matched UNSAT over the unstripped formulas. That is a remaining
/// kernel-grade limitation, not independent proof of the whole wrapped formula.
/// (This readout-strip residual is shared
/// with the eq/ult/… value discharges; it is matcher-trusted, not ay-free.)
pub(crate) fn try_div_conditional_discharge(
    machine_out: &Formula,
    auto: &Formula,
    pre: &Formula,
) -> Option<String> {
    let key_pre = div_precondition_key(pre)?;
    // auto = BvUDiv(a, b) [unsigned] OR BvSDiv(a, b) [signed]
    let (a, b, signed) = match auto {
        Formula::BvUDiv(l, r, 32) => (&**l, &**r, false),
        Formula::BvSDiv(l, r, 32) => (&**l, &**r, true),
        _ => return None,
    };
    // machine = W( Ite(Eq(b2, 0), 0, BvU/SDiv(a2, b2)) ), W = nested Extract/ZeroExt/Or(0,·)
    let inner = div_peel_to_ite(machine_out)?;
    let (pred, then_b, else_b) = match inner {
        Formula::Ite(p, t, e) => (&**p, &**t, &**e),
        _ => return None,
    };
    if !matches!(then_b, Formula::BitVec { value: 0, width: 32 }) {
        return None; // then-branch must be the ÷0 result 0
    }
    // predicate is `Eq(b2, 0)` (zero on either side)
    let b_pred = match pred {
        Formula::Eq(l, r) if matches!(&**r, Formula::BitVec { value: 0, width: 32 }) => &**l,
        Formula::Eq(l, r) if matches!(&**l, Formula::BitVec { value: 0, width: 32 }) => &**r,
        _ => return None,
    };
    let (a2, b2) = match (else_b, signed) {
        (Formula::BvUDiv(l, r, 32), false) => (&**l, &**r),
        (Formula::BvSDiv(l, r, 32), true) => (&**l, &**r),
        _ => return None, // machine div op must match auto's signedness
    };

    let key_a = div_operand_key(a)?;
    let key_b = div_operand_key(b)?;
    let key_a2 = div_operand_key(a2)?;
    let key_b2 = div_operand_key(b2)?;
    // SOUNDNESS: the ÷0-guard predicate divisor (b_pred) must key-match the udiv divisor (b2), so the
    // hypothesis `bvIsZero <b2> = false` collapses the SAME guard the value is divided under. This Rust
    // check is LOAD-BEARING: the kernel ties b2≡b to the auto side, but the guard predicate operand is
    // not otherwise kernel-constrained to equal b2, so a mismatched guard register must be refused here.
    if div_operand_key(b_pred)? != key_b2 {
        return None;
    }

    let mut bit_axioms: Vec<String> = Vec::new();
    let w = 32u32;
    let bits_a = kx::opaque_bit_list(&key_a, w, &mut bit_axioms);
    let bits_b = kx::opaque_bit_list(&key_b, w, &mut bit_axioms);
    let bits_a2 = kx::opaque_bit_list(&key_a2, w, &mut bit_axioms);
    let bits_b2 = kx::opaque_bit_list(&key_b2, w, &mut bit_axioms);
    let bits_pre = kx::opaque_bit_list(&key_pre, w, &mut bit_axioms);
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
    // The goal uses the supplied precondition, NOT the machine divisor. A
    // theorem instantiated at b2 only checks when these are the same predicate.
    let h_type = kx::eq_bool(kx::bv_is_zero(bits_pre), kx::bfalse());
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
    pre: &Formula,
) -> Option<String> {
    try_div_conditional_discharge(machine_out, auto, pre)
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
    on_route_stack(|| o1_routes(machine_out, auto))
}

/// The routes of [`try_o1_instantiation_discharge`], in order.
fn o1_routes(machine_out: &Formula, auto: &Formula) -> Option<String> {
    // Memory and concatenation must check both original terms, including every
    // array identity/store/query. Never fall back to the stripped scalar goal.
    if formula_contains_select(machine_out)
        || formula_contains_select(auto)
        || memory_reflection::contains_concat(machine_out)
        || memory_reflection::contains_concat(auto)
    {
        return memory_reflection::discharge(machine_out, auto);
    }
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

    // The shared-core discharge is tried first and is unchanged. Only when it
    // declines is the same equation retried with `Add` operands commuted into
    // one order (PKG-C5c: `madd` renders its addend first, source `x * 3 + 7`
    // renders it second). A declined retry is `None`, as before it existed.
    //
    // Only when both decline is it retried once more with the strength-reduction
    // rewrites (`strength`): trust-cg emits `x * 3 + 7` as
    // `(x + 7) + (x << 1)`, which no wrapper strip or operand order joins to
    // the source. A declined retry is `None`, as before it existed.
    //
    // Only when all three decline is it retried with additive cancellation as
    // well (`cancel`, CANCEL-1): trust-cg folds `(c + x) - c + 1` to `x + 1`.
    // This chain runs per item inside `try_kernel_recheckable_proof`, so it
    // precedes everything step (5) of `call_event.rs` tries after a declined
    // conjunction: `closed_branch::retry`, then the branch routes
    // (`try_branch_split_conjunction`: BRANCH-SPLIT-1, then DIV-SPLIT-1, then
    // CONSTDIV-1), which are not in this chain. A declined retry is `None`, as before it existed.
    try_shared_core_discharge(machine_out, auto)
        .or_else(|| try_add_comm_discharge(machine_out, auto, AddCommFilter::On))
        .or_else(|| try_strength_discharge(machine_out, auto, StrengthFilter::On))
        .or_else(|| try_cancel_discharge(machine_out, auto, CancelFilter::On))
}

/// The two sides reflect to cores the kernel finds definitionally equal; the
/// discharge chains each side's congruence proof through that shared core.
fn try_shared_core_discharge(machine_out: &Formula, auto: &Formula) -> Option<String> {
    // The read-only side condition is decided ONCE, over BOTH whole formulas,
    // before any reflection runs — it is a property of the obligation, not of an
    // individual read. `for_obligation` is the only constructor that can turn the
    // bare-read arm on; everything else uses `ReflectCtx::closed`.
    let mut ctx = ReflectCtx::for_obligation(machine_out, auto);
    let rm = reflect_formula(machine_out, &mut ctx).ok()?;
    let ra = reflect_formula(auto, &mut ctx).ok()?;
    let ReflectCtx { leaves, mems, .. } = ctx;
    let read_caller_memory = !mems.is_empty();

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
        let env = discharge_env(&leaves, &mems).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok().map(|()| ())
    })
    .ok()
    .flatten();

    result.map(|()| {
        if read_caller_memory {
            "Clean.BVC.selectAddrCong+congruence (O(1) caller-memory read, no-store body)"
                .to_string()
        } else {
            "Clean.BVC.bvf_wrapper_id+congruence (O(1) add@N)".to_string()
        }
    })
}

/// Whether [`try_add_comm_discharge`] declines before the kernel runs when no
/// `Add` was reordered or the two cores are still different terms. `Off`
/// exists for the tests that hand the kernel a false equation and assert that
/// the KERNEL, not this filter, rejects it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AddCommFilter {
    On,
    #[cfg(test)]
    Off,
}

/// THE COMMUTED RETRY (PKG-C5c). Reflect both sides again with the operands of
/// every `Add` that has a multiply operand in one canonical order, and check
/// the resulting term in the kernel.
///
/// What is proved, and by what. The goal is
/// `bvfEval (reflect machine_out) = bvfEval (reflect auto)`, where `reflect`
/// keeps each Formula's own operand order and renders a `w`-bit variable as `w`
/// opaque `Bool` constants. The proof is each side's congruence proof to its
/// core, as in [`try_shared_core_discharge`], except that at an `Add` node whose
/// operands are out of order the core takes the other order and the proof
/// gains one step, an instance of
/// `Trust.BVC.addRecM_comm : ∀ xs ys c, bvLen xs = bvLen ys → addRecM xs ys c = addRecM ys xs c`
/// with its length premise proved from `Trust.BVC.len_addRecM` /
/// `Trust.BVC.len_bvMul` and computation on the concrete leaves. Those are
/// kernel-checked theorems with an empty axiom closure (`add_comm`).
///
/// The kernel's `check_type` of the whole term against that goal is the only
/// authority. The operand order, the swap decisions and the length proofs are
/// all inside the checked term; if any is wrong the check fails and this
/// returns `None`. `Sub` is never reordered, an `Add` without a multiply
/// operand is never reordered (`add_comm`, "Scope"), and an `Add` whose operand
/// lengths are not proved equal is never reordered.
fn try_add_comm_discharge(
    machine_out: &Formula,
    auto: &Formula,
    filter: AddCommFilter,
) -> Option<String> {
    let mut ctx = ReflectCtx::commuting();
    let rm = reflect_formula(machine_out, &mut ctx).ok()?;
    let ra = reflect_formula(auto, &mut ctx).ok()?;
    // Decline without the kernel when it could not help. With no `Add`
    // reordered this is the first attempt over again; with two cores that are
    // still different terms the kernel would have to decide two bit-level
    // adders equal by unfolding them, which is not this route's job and has no
    // useful time bound. Both tests only ever decline; they accept nothing.
    if filter == AddCommFilter::On && (ctx.add_swaps == 0 || rm.core != ra.core) {
        return None;
    }
    let ReflectCtx { leaves, .. } = ctx;

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
    run_recheck_thread("trust-mpos-o1-add-comm", move || {
        let env = add_comm::commuting_env(&leaves).ok()?;
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&discharge, &goal).ok()
    })
    .ok()
    .flatten()
    .map(|()| add_comm::THEOREM_LABEL.to_string())
}

/// Whether [`try_strength_discharge`] declines before the kernel runs when no
/// strength step was spliced or the two cores are still different terms.
/// `Off` exists for the tests that hand the kernel a false equation and assert
/// that the KERNEL, not this filter, rejects it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum StrengthFilter {
    On,
    #[cfg(test)]
    Off,
}

/// No side of a strength obligation has more Formula nodes than this.
const STRENGTH_MAX_NODES: usize = 256;

/// The pre-filter of the strength route, run on each side before anything is
/// reflected: every node is a variable, a constant, `+`, `-`, `*`, `|`, `^`,
/// `<<`, a zero-extension or a low extract (`low == 0`), the only kinds the
/// measured strength-reduced shapes and their register-move and zero-extension
/// wrappers use; every width (each variable, constant, operation, extract and
/// zero-extension result) is in `1..=64` and consistent with its operands';
/// every zero-extension amount is in `1..=63`; and there are at most
/// [`STRENGTH_MAX_NODES`] nodes. So nothing downstream (`kx::bits`,
/// `kx::nat_lit`, `add_comm::bit_leaf`, the step builders) is ever handed an
/// unbounded width, amount or list, and no node whose reflection this route
/// does not need (division, right shifts, `&`) widens the reflection residual
/// it trusts.
fn strength_fragment(f: &Formula) -> bool {
    /// The width of `f`, or `None` outside the fragment.
    fn walk(f: &Formula, nodes: &mut usize) -> Option<u32> {
        *nodes += 1;
        if *nodes > STRENGTH_MAX_NODES {
            return None;
        }
        let width = match f {
            Formula::Var(_, Sort::BitVec(w)) | Formula::BitVec { width: w, .. } => *w,
            Formula::BvZeroExt(x, k) => {
                if !(1..=63).contains(k) {
                    return None;
                }
                walk(x, nodes)?.checked_add(*k)?
            }
            Formula::BvExtract { inner, high, low: 0 } => {
                let inner_width = walk(inner, nodes)?;
                if *high >= inner_width {
                    return None;
                }
                high + 1
            }
            Formula::BvAdd(l, r, w)
            | Formula::BvSub(l, r, w)
            | Formula::BvMul(l, r, w)
            | Formula::BvOr(l, r, w)
            | Formula::BvXor(l, r, w)
            | Formula::BvShl(l, r, w) => {
                if walk(l, nodes)? != *w || walk(r, nodes)? != *w {
                    return None;
                }
                *w
            }
            _ => return None,
        };
        (1..=64).contains(&width).then_some(width)
    }
    walk(f, &mut 0).is_some()
}

/// A strength obligation as the kernel will see it: the goal
/// `bvfEval (reflect machine) = bvfEval (reflect auto)`, the discharge term,
/// the variables it states, and the label a success carries.
struct StrengthObligation {
    goal: Expr,
    discharge: Expr,
    leaves: Vec<(String, u32)>,
    label: String,
}

/// Reflect both sides under [`ReflectCtx::strength`] and build the discharge:
/// each side's proof to its core, chained through the shared core. `None`
/// when a side is outside [`strength_fragment`] or the reflection, and, with
/// [`StrengthFilter::On`], when no strength step was spliced (the older routes
/// already had this obligation) or the cores are still different terms (the
/// kernel would have to decide two bit-level circuits equal by unfolding them).
fn strength_obligation(
    machine_out: &Formula,
    auto: &Formula,
    filter: StrengthFilter,
) -> Option<StrengthObligation> {
    if !strength_fragment(machine_out) || !strength_fragment(auto) {
        return None;
    }
    let mut ctx = ReflectCtx::strength();
    let rm = reflect_formula(machine_out, &mut ctx).ok()?;
    let ra = reflect_formula(auto, &mut ctx).ok()?;
    if filter == StrengthFilter::On && (ctx.strength_rewrites == 0 || rm.core != ra.core) {
        return None;
    }
    let label = strength::label(&ctx.strength_used, ctx.add_swaps);
    let (goal, discharge) = meet(rm, ra);
    Some(StrengthObligation { goal, discharge, leaves: ctx.leaves, label })
}

/// The goal `bvfEval rm.bvf = bvfEval ra.bvf` and its discharge: each side's
/// proof to its core, chained through the shared core.
fn meet(rm: Reflected, ra: Reflected) -> (Expr, Expr) {
    let goal = kx::eq_list(kx::evalf(rm.bvf.clone()), kx::evalf(ra.bvf.clone()));
    let sym_ra = kterm::symm(
        kx::list_bool(),
        kx::evalf(ra.bvf.clone()),
        kx::evalf(ra.core.clone()),
        ra.proof,
    );
    let discharge = kx::eq_trans_list(
        kx::evalf(rm.bvf),
        kx::evalf(rm.core),
        kx::evalf(ra.bvf),
        rm.proof,
        sym_ra,
    );
    (goal, discharge)
}

#[cfg(test)]
thread_local! {
    /// How many strength kernel checks this thread started (T-U7).
    static STRENGTH_KERNEL_RUNS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// THE STRENGTH-REDUCTION RETRY. Reflect both sides with the rewrite steps of
/// `strength` spliced into the cores (a shift by a constant becomes a
/// multiply; a multiply absorbs an added or subtracted multiplicand), and
/// check the resulting term in the kernel.
///
/// What is proved, and by what. The goal is
/// `bvfEval (reflect machine_out) = bvfEval (reflect auto)`, built from the two
/// Formulas alone: under strength every node's `bvf`, including the zero and
/// length tags of the wrappers, is the Formula's own reflection, independent
/// of the step builders. The proof is each side's congruence proof to its
/// core, where a rewritten node's proof gains one step per rewrite, an
/// instance of a `Trust.BVS.*` theorem whose closed premises (lengths and
/// values of constants of at most 64 bits) the kernel computes. Those
/// theorems, the value theory under them and every lemma the reflection
/// splices are audited in `strength::strength_base` (proved, empty domain and
/// foundational axiom closure). The term is declared as a theorem of the goal
/// in the per-obligation environment (`strength::admit_obligation`), so the
/// kernel's type-check of the whole term against the goal is the only
/// authority: a wrong match, constant or length proof makes it fail, and this
/// returns `None`. That declaration's transitive axiom closure must then hold
/// only the per-bit `BVC_LEAFBIT_*` `Bool` constants that state the
/// obligation, so nothing the term reaches, directly or through a citation,
/// may rest on another axiom.
///
/// Trusted, as for every route here: that the reflection is faithful to the
/// Formula (the F1 residual), which now includes the standalone `ZeroExt` arm.
fn try_strength_discharge(
    machine_out: &Formula,
    auto: &Formula,
    filter: StrengthFilter,
) -> Option<String> {
    strength_discharge_in(machine_out, auto, filter, strength::strength_env)
}

/// [`try_strength_discharge`] in the environment `env_of` builds (a test
/// hands it a doctored one).
fn strength_discharge_in(
    machine_out: &Formula,
    auto: &Formula,
    filter: StrengthFilter,
    env_of: fn(&[(String, u32)]) -> Result<Environment, String>,
) -> Option<String> {
    let StrengthObligation { goal, discharge, leaves, label } =
        strength_obligation(machine_out, auto, filter)?;
    #[cfg(test)]
    STRENGTH_KERNEL_RUNS.with(|runs| runs.set(runs.get() + 1));
    run_recheck_thread("trust-mpos-o1-strength", move || {
        let mut env = env_of(&leaves).ok()?;
        strength::admit_obligation(&mut env, goal, discharge).ok()
    })
    .ok()
    .flatten()
    .map(|()| label)
}

/// Whether [`try_cancel_discharge`] declines before the kernel runs when no
/// cancellation was spliced or the two cores are still different terms. `Off`
/// exists for the tests that hand the kernel a false equation and assert that
/// the KERNEL, not this filter, rejects it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CancelFilter {
    On,
    #[cfg(test)]
    Off,
}

#[cfg(test)]
thread_local! {
    /// How many cancel kernel checks this thread started.
    static CANCEL_KERNEL_RUNS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// A cancel obligation as the kernel will see it. `None` when a side is outside
/// [`strength_fragment`] or the reflection, and, with [`CancelFilter::On`],
/// when the discharge term cites no `add_sub_cancel` (the older routes already
/// had this obligation) or the cores are still different terms. The label
/// names only theorems the term cites.
fn cancel_obligation(
    machine_out: &Formula,
    auto: &Formula,
    filter: CancelFilter,
) -> Option<StrengthObligation> {
    if !strength_fragment(machine_out) || !strength_fragment(auto) {
        return None;
    }
    let mut ctx = ReflectCtx::cancel();
    let rm = reflect_formula(machine_out, &mut ctx).ok()?;
    let ra = reflect_formula(auto, &mut ctx).ok()?;
    let cores_meet = rm.core == ra.core;
    // A cheap first filter on the context's record of the steps.
    let recorded = ctx.strength_used.contains(&cancel::names::ADD_SUB_CANCEL);
    if filter == CancelFilter::On && (!recorded || !cores_meet) {
        return None;
    }
    let (goal, discharge) = meet(rm, ra);
    // The filter and the label then read the theorems the discharge term
    // itself cites, not the context's record: an arm that drops its child's
    // core (the bare `BvExtract`) drops a step spliced beneath it from the
    // proof while the record still counts it.
    let mut cited = std::collections::HashSet::new();
    discharge.used_constants_dag(clean_kernel::expr::UsedConstants::ConstantsOnly, &mut cited);
    let cites = |n: &str| cited.contains(&Name::from_string(n));
    if filter == CancelFilter::On && !cites(cancel::names::ADD_SUB_CANCEL) {
        return None;
    }
    let used: Vec<&'static str> = ctx.strength_used.iter().copied().filter(|n| cites(n)).collect();
    let label = cancel::label(&used, usize::from(cites(add_comm::names::ADD_REC_M_COMM)));
    Some(StrengthObligation { goal, discharge, leaves: ctx.leaves, label })
}

/// THE ADDITIVE-CANCELLATION RETRY (CANCEL-1). Reflect both sides under
/// [`ReflectCtx::cancel`] (the strength reflection with
/// `Trust.BVA.add_sub_cancel` spliced at every `Sub` whose cores are
/// `(c + x) - c`, at 32 or 64 bits), and check the resulting term in the
/// kernel.
///
/// What is proved, and by what: as for [`try_strength_discharge`]. The goal is
/// `bvfEval (reflect machine_out) = bvfEval (reflect auto)`, built from the two
/// Formulas alone (the `Sub` node's `bvf` is the Formula's own, whatever the
/// step does to its core). The theorem is checked by `add_decl` and audited in
/// `cancel::cancel_base` (empty domain and foundational axiom closure, through
/// everything it cites); the term is admitted only through
/// `strength::admit_obligation`, whose transitive axiom closure may hold only
/// the per-bit `BVC_LEAFBIT_*` leaves. A wrong match or length proof makes
/// the kernel check fail, and this returns `None`.
///
/// Trusted, as for every route here: that the reflection is faithful to the
/// Formula (the F1 residual). This route adds no reflection arm.
fn try_cancel_discharge(
    machine_out: &Formula,
    auto: &Formula,
    filter: CancelFilter,
) -> Option<String> {
    cancel_discharge_in(machine_out, auto, filter, cancel::cancel_env)
}

/// [`try_cancel_discharge`] in the environment `env_of` builds (a test hands
/// it a doctored one).
fn cancel_discharge_in(
    machine_out: &Formula,
    auto: &Formula,
    filter: CancelFilter,
    env_of: fn(&[(String, u32)]) -> Result<Environment, String>,
) -> Option<String> {
    let StrengthObligation { goal, discharge, leaves, label } =
        cancel_obligation(machine_out, auto, filter)?;
    #[cfg(test)]
    CANCEL_KERNEL_RUNS.with(|runs| runs.set(runs.get() + 1));
    run_recheck_thread("trust-mpos-o1-cancel", move || {
        let mut env = env_of(&leaves).ok()?;
        strength::admit_obligation(&mut env, goal, discharge).ok()
    })
    .ok()
    .flatten()
    .map(|()| label)
}

/// Does the formula contain a `Select` node (a memory read)? Cheap guard so the
/// memory discharge only fires on store-load obligations.
pub(crate) fn formula_contains_select(f: &Formula) -> bool {
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
        | Formula::BvXor(l, r, _)
        | Formula::BvMul(l, r, _)
        | Formula::BvUDiv(l, r, _)
        | Formula::BvSDiv(l, r, _)
        | Formula::BvShl(l, r, _)
        | Formula::BvLShr(l, r, _)
        | Formula::BvAShr(l, r, _)
        | Formula::BvConcat(l, r) => formula_contains_select(l) || formula_contains_select(r),
        _ => false,
    }
}

// Memory obligations use a separate original-term reflector. The previous
// concrete-cons shortcut erased the underlying memory and substituted stripped
// children into its goal; that is insufficient for a kernel-instantiated grade.
#[path = "verify_output_instantiate/memory_reflection.rs"]
mod memory_reflection;

// Kernel term builders for the bridge-side theorems (`add_comm`).
#[path = "verify_output_instantiate/kterm.rs"]
mod kterm;

// Add commutation for the multiply-then-add (MADD) shape: the kernel theorems
// and the per-obligation proof steps of `try_add_comm_discharge`.
#[path = "verify_output_instantiate/add_comm.rs"]
mod add_comm;

// An untrusted `+`/`*` normaliser over `Nat` that emits kernel proof terms,
// and the value theory (`Trust.BVV.*`: order, `/` and `%`, powers of two,
// bits and lists) whose proofs use it. Every term is checked by `add_decl`.
#[path = "verify_output_instantiate/nat_ring.rs"]
mod nat_ring;

#[path = "verify_output_instantiate/bv_value.rs"]
mod bv_value;

// The strength-reduction theorems (`Trust.BVS.*`: a shift by a constant is a
// multiply, a multiply absorbs an added or subtracted multiplicand), their
// audited environment, and the guarded per-obligation rewrite steps that
// `try_strength_discharge` splices into the reflection.
#[path = "verify_output_instantiate/strength.rs"]
mod strength;

// Additive cancellation (CANCEL-1, `Trust.BVA.add_sub_cancel`): the theorem,
// its audited environment, and the guarded step `try_cancel_discharge`
// splices into the reflection.
#[path = "verify_output_instantiate/cancel.rs"]
mod cancel;

// The route's unit tests (T-U4, T-U5, T-U7 to T-U12).
#[cfg(test)]
#[path = "verify_output_instantiate/strength_route_tests.rs"]
mod strength_route_tests;

// The branch split (BRANCH-SPLIT-1): the kernel theory of `bvIteVal` and the
// comparison bridges (`Trust.BVB.*`, `Trust.BVS.mul_add_self`), and the route
// that proves a conjunction of branching obligations by an atom case split.
#[path = "verify_output_instantiate/branch_theory.rs"]
mod branch_theory;

#[path = "verify_output_instantiate/branch_reflect.rs"]
mod branch_reflect;

#[path = "verify_output_instantiate/branch_split.rs"]
mod branch_split;

// The guarded symbolic division split (DIV-SPLIT-1), tried only where the branch split declined,
// and the dispatch that orders the two (the step-(5) branch routes).
#[path = "verify_output_instantiate/div_split.rs"]
mod div_split;

#[path = "verify_output_instantiate/branch_dispatch.rs"]
mod branch_dispatch;

// CONSTDIV: the constant-division theory and route. Stage B1 (DECISION_QUEUE
// CONSTDIV-1) wires the step-(4) rewrite: call_event.rs hands each item's
// machine side to `const_div_step4`. Stage B2 wires the conjunction route
// (`const_div::try_conjunction`) as the third step-(5) branch route
// (`branch_dispatch.rs`), tried only after the branch and division splits
// decline and only on a conj with a multiply-high.
#[path = "verify_output_instantiate/const_div.rs"]
mod const_div;
#[path = "verify_output_instantiate/const_div_theory.rs"]
mod const_div_theory;
#[cfg(feature = "test-hooks")]
pub use branch_dispatch::without_const_div_conjunction;
pub(crate) use const_div::step4_rewrite as const_div_step4;
#[cfg(feature = "test-hooks")]
pub use const_div::{HookCall, record_const_div_rewrites, without_const_div_rewrite};

// Loop L1 spike (unwired, test-only): `Trust.Loop.sim` and the cut-point lockstep route.
#[cfg(test)]
#[path = "verify_output_instantiate/loop_sim.rs"]
mod loop_sim;

/// The step-(5) branch routes as the call-event gate calls them (call_event.rs and
/// call_event/closed_branch.rs, DECISION_QUEUE BRANCH-SPLIT-1, DIV-SPLIT-1 and CONSTDIV-1): the
/// branch split, then, on its decline, the guarded symbolic division split, then, on its decline
/// and only with a multiply-high in the conj, the constant division route (`branch_dispatch.rs`,
/// which this returns unchanged). `Some(KernelInstantiated)` when the kernel accepts a split, `None`
/// otherwise. Under `test-hooks` each call's outcome is also recorded for
/// [`record_branch_split_calls`]; the recording changes no result.
pub(crate) fn try_branch_split_conjunction(
    items: &[(Formula, Formula)],
) -> Option<crate::verify_output::ProvenEvidence> {
    let evidence = branch_dispatch::try_conjunction(items);
    #[cfg(feature = "test-hooks")]
    BRANCH_SPLIT_CALLS.with(|calls| {
        if let Some(calls) = calls.borrow_mut().as_mut() {
            calls.push(evidence.is_some());
        }
    });
    evidence
}

#[cfg(feature = "test-hooks")]
thread_local! {
    static BRANCH_SPLIT_CALLS: std::cell::RefCell<Option<Vec<bool>>> =
        const { std::cell::RefCell::new(None) };
}

/// TEST HOOK (`test-hooks` only): run `body` and return, with its result, one entry per call
/// the call-event gate made to the branch split on THIS thread while it ran (`true` when the
/// route returned kernel evidence, `false` when it declined). It observes the route; it grants
/// nothing and changes no verdict. It lets a gate test pin WHERE step (5) calls the route (only
/// inside `kernel_eligible`, after `closed_branch::retry`, never over kernel evidence), which the
/// evidence alone cannot show when the route would decline anyway.
#[cfg(feature = "test-hooks")]
#[doc(hidden)]
pub fn record_branch_split_calls<R>(body: impl FnOnce() -> R) -> (R, Vec<bool>) {
    let outer = BRANCH_SPLIT_CALLS.with(|calls| calls.borrow_mut().replace(Vec::new()));
    let result = body();
    let calls = BRANCH_SPLIT_CALLS.with(|calls| std::mem::replace(&mut *calls.borrow_mut(), outer));
    (result, calls.unwrap_or_default())
}

/// The original typed mixed goal is checked as one CIC conjunction.
pub(crate) fn try_original_conjunction_discharge(
    items: &[(Formula, Formula)],
) -> Option<crate::original_conjunction_certificate::CheckedOriginalConjunction> {
    on_route_stack(|| memory_reflection::discharge_conjunction(items))
}

pub(crate) fn try_mem_store_load_discharge(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<String> {
    on_route_stack(|| {
        if !formula_contains_select(machine_out) && !formula_contains_select(auto) {
            return None;
        }
        memory_reflection::discharge(machine_out, auto)
    })
}

// ── Test-support surface (used by verify_output's B2b/B4 tests) ────────────────
#[cfg(test)]
pub(crate) mod test_support {
    use clean_kernel::{Environment, Expr};
    use trust_types::Formula;

    use super::{ReflectCtx, Reflected, discharge_env as denv, reflect_formula as reflect};

    /// Reflect a Formula under the FAIL-CLOSED policy (no bare caller-memory read).
    pub(crate) fn reflect_formula(f: &Formula) -> Result<Reflected, String> {
        reflect(f, &mut ReflectCtx::closed())
    }
    /// Reflect a Formula under the policy the pair `(machine, auto)` earns — the
    /// bare-read arm is live only if `is_store_free` holds on BOTH.
    pub(crate) fn reflect_formula_for(
        f: &Formula,
        machine: &Formula,
        auto: &Formula,
    ) -> Result<Reflected, String> {
        reflect(f, &mut ReflectCtx::for_obligation(machine, auto))
    }
    /// The read-only side condition itself, for direct testing.
    pub(crate) fn store_free(f: &Formula) -> bool {
        super::is_store_free(f)
    }
    /// Does `reflect_mem` accept this formula? (true iff Some).
    pub(crate) fn reflect_mem_ok(f: &Formula) -> bool {
        super::memory_reflection::accepts(f)
    }
    pub(crate) fn mem_discharge(m: &Formula, a: &Formula) -> Option<String> {
        super::try_mem_store_load_discharge(m, a)
    }
    /// Env with the BVC layer + the given symbolic leaves.
    pub(crate) fn env_with_leaves(leaves: &[(&str, u32)]) -> Environment {
        let owned: Vec<(String, u32)> =
            leaves.iter().map(|(n, w)| ((*n).to_string(), *w)).collect();
        denv(&owned, &[]).expect("discharge_env")
    }
    pub(crate) fn contains_wrapper(e: &Expr) -> bool {
        super::reflection_contains_wrapper(e)
    }
}

pub(crate) use memory_reflection::{
    OriginalParameterRole, install_original_frame_bank, original_conjunction_goal,
    original_conjunction_goal_version, original_conjunction_model, original_parameter_roles,
    original_reflexive_equation,
};
