// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! LOOP L1 spike (unwired, test-only): a loop function's cut-point lockstep
//! simulation as ONE kernel-checked Clean goal.
//!
//! # What is proved
//!
//! One header `H`. The IR state `A` is the `Prod` of its shared variables
//! (block parameters, then live-ins); the machine state `B` is the `Prod` of
//! the registers the machine segment from the cut address reads: the coupled
//! registers (named by the IR cut variable they hold), the frame registers
//! (every AAPCS64 callee-saved register — SP, X19-X28, X29, X30 and the low
//! halves of D8-D15 — is required; X18 may be added) and the scratch (havoc)
//! registers. A register is read by a segment as `fit_w (proj_j s)`, the
//! concrete `w`-bit spine `bhead (btail^k (proj_j s))`, which is exactly what
//! a `BVC_LEAFBIT_{name}_{w}_{k}` leaf spine becomes under [`substitute`].
//!
//! The declared type, built from the Formulas alone under
//! `ReflectCtx::branching_goal` (through `branch_split::goal_of`, so the
//! branch width walk is part of it), is
//!
//! ```text
//! G := Entry κ ∧ (CovIR ∧ (CovM ∧ ∀ n, Obs κ (itA n) (itB n)))
//! itA n := Nat.rec (λ _. A) (a0 κ) (λ _ x. fA x) n      (itB likewise)
//! ```
//!
//! with `κ` the entry leaves `bit_leaf(e)` (the only constants it mentions).
//! [`goal_of`] DERIVES every observation from the step itself: each IR step
//! must be `Ite(c_IR, value, CUT_j)` and each machine step
//! `Ite(c_M, value, self)` or `self`, one `c` per side (a goal-shape check no
//! filter bypasses), and
//!
//! - `Entry`: on the entry segment, the reach-the-header bits agree
//!   (`bit(reach_IR) = bit(reach_M)`), the masked direct-return values agree
//!   (`Ite(reach, 0, ret)`), and for every frame register the direct-return
//!   path's value is its entry leaf `K_f` (stated unmasked, so stronger);
//! - `CovIR`, `CovM`: `∀ a` (`∀ b`), `bit(c ∨ reach_ret) = 1` and
//!   `bit(c ∧ reach_ret) = 0`, with `c` the step's own condition and
//!   `reach_ret` the executor's condition for reaching `ret`: the segment
//!   goes back exactly when it does not return;
//! - `Obs κ a b`: `bit(c_IR) = bit(c_M)`, `Ite(c_IR, 0, ret_IR) =
//!   Ite(c_M, 0, ret_M)`, and for every frame register the exit path's value
//!   at `ret` is `K_f` (unmasked: required of every state the invariant
//!   admits).
//!
//! # The proof
//!
//! The registered, audited, axiom-free theorem [`names::SIM`] (lockstep
//! `Nat.rec` induction) applied to
//!
//! ```text
//! Rel κ a b := ⋀_j proj_j a = proj_{loc j} b  ∧  ⋀_f proj_f b = Ψ_f κ
//! ```
//!
//! where `Ψ_f κ` is the ENTRY SEGMENT's value of frame register `f` (the
//! prologue moves SP, so the invariant is not the entry leaf `K_f`), and to
//! six lemmas, each a `Declaration::Theorem` whose statement quantifies the
//! entry values `κ` and states nothing about any leaf: `entry`, `cov_ir`,
//! `cov_m`, `base`, `step`, `obs` (checked in that order). They are added to
//! [`loop_base`] BEFORE any leaf is declared, so a leftover cut or havoc
//! constant in a lemma is an unknown constant and the kernel refuses it. Each
//! lemma is assembled from per-item proofs over leaf constants (refl, then
//! `branch_split::obligation`, then the strength and cancel routes; the
//! bit-blast route is not used: its kernel goal is `Unsat cs`, which does not
//! compose), with every cut, havoc and entry bit constant replaced by the
//! matching bit of a binder ([`substitute`]), the machine side rewritten from
//! the IR's projections to the machine's by `Eq.subst` with the invariant's
//! hypotheses, and the frame side rewritten to `Ψ_f`. The discharge then
//! applies the lemmas to `κ`, and is admitted through
//! `strength::admit_obligation` in an environment holding only
//! [`loop_base`], the lemmas and the entry-leaf bits.
//!
//! # Trusted, outside the kernel
//!
//! As for every reflected route: the Formula reflection (`branch_split` width
//! walk and `branch_reflect` goal arms). Newly, the two symbolic executors'
//! outputs this goal takes as given: the segment Formulas (`entry_*`,
//! `step_*`), the condition under which each header segment reaches `ret`
//! (`reach_ret_*`), the value it returns there (`ret_*`), the frame values on
//! the exit and direct-return paths, and the entry segment's reach bit and
//! direct-return value; and that the cut decomposition is complete (every
//! cycle passes the header, and the machine run from the header stops only at
//! the header or `ret`). The kernel checks that the executor's `reach_ret` is
//! the complement of the condition the step branches on; it does not check
//! that the Formulas are what the code does.
//!
//! # What only declines
//!
//! The route choice and the check that a route's goal is the item's
//! statement. [`LoopFilter::Off`] bypasses them (an item with no route gets
//! `Eq.refl`), so a test shows the KERNEL rejecting; it also skips the
//! strength route, whose filter-off term would shadow the cancel route. The
//! shape and naming checks of [`goal_of`] (the step forms, the frame set,
//! declared leaves are entry names, disjoint from `CUT_*` and `*_HAVOC`) are
//! part of the goal and are never bypassed.

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use clean_kernel::{
    ConstantKind, Declaration, Environment, Expr, ExprFolderOpt, FVarId, Level, LevelVec,
};
use trust_types::{Formula, Sort};

use super::branch_split::{self, BranchFilter, Decline};
use super::kterm::{self, Fresh, bhead, btail, lams, lb, nat, nat_rec_prop, nat_rec1, pis, prop};
use super::{
    CancelFilter, StrengthFilter, add_comm, branch_theory, cancel, cancel_obligation, kx,
    on_route_stack, run_recheck_thread, strength, strength_obligation,
};

pub(crate) mod names {
    /// `∀ A B R fA fB a0 b0, R a0 b0 → (∀ a b, R a b → R (fA a) (fB b)) →
    /// ∀ n, R (itA n) (itB n)`.
    pub(crate) const SIM: &str = "Trust.Loop.sim";
    pub(crate) const BASE: &str = "Trust.Loop.obl.base";
    pub(crate) const STEP: &str = "Trust.Loop.obl.step";
    pub(crate) const OBS: &str = "Trust.Loop.obl.obs";
    pub(crate) const COV_IR: &str = "Trust.Loop.obl.cov_ir";
    pub(crate) const COV_M: &str = "Trust.Loop.obl.cov_m";
    pub(crate) const ENTRY: &str = "Trust.Loop.obl.entry";
}

/// Whether the decline-only Rust checks run (route choice, route goal equals
/// the item statement). `Off` exists for tests: the kernel must reject. `Off`
/// also skips the strength route (its filter-off term would shadow cancel's)
/// and hands `Eq.refl` to an item no route proves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoopFilter {
    On,
    Off,
}

// ── the generic theorem ──────────────────────────────────────────────────────

fn ty1() -> Expr {
    Expr::sort(kterm::l1())
}

/// `dom → cod` (a non-dependent `Pi`).
fn arrow(fr: &mut Fresh, dom: Expr, cod: Expr) -> Expr {
    let (id, _) = fr.local();
    pis(vec![(id, dom)], cod)
}

fn app2(f: &Expr, x: Expr, y: Expr) -> Expr {
    Expr::apps(f.clone(), [x, y])
}

/// `@Nat.rec.{1} (λ _ => ty) z (λ _ x => f x) n`, the `n`-th iterate.
pub(crate) fn iter(fr: &mut Fresh, ty: &Expr, z: &Expr, f: &Expr, n: &Expr) -> Expr {
    let motive = {
        let (w_id, _) = fr.local();
        lams(vec![(w_id, nat())], ty.clone())
    };
    let succ = {
        let (m_id, _) = fr.local();
        let (x_id, x) = fr.local();
        lams(vec![(m_id, nat()), (x_id, ty.clone())], Expr::app(f.clone(), x))
    };
    nat_rec1(motive, z.clone(), succ, n.clone())
}

/// The statement of [`names::SIM`].
pub(crate) fn sim_statement() -> Expr {
    let mut fr = Fresh::new();
    let (ta_id, ta) = fr.local();
    let (tb_id, tb) = fr.local();
    let r_ty = {
        let inner = arrow(&mut fr, tb.clone(), prop());
        arrow(&mut fr, ta.clone(), inner)
    };
    let (r_id, r) = fr.local();
    let fa_ty = arrow(&mut fr, ta.clone(), ta.clone());
    let fb_ty = arrow(&mut fr, tb.clone(), tb.clone());
    let (fa_id, fa) = fr.local();
    let (fb_id, fb) = fr.local();
    let (a0_id, a0) = fr.local();
    let (b0_id, b0) = fr.local();
    let hb_ty = app2(&r, a0.clone(), b0.clone());
    let hs_ty = {
        let (x_id, x) = fr.local();
        let (y_id, y) = fr.local();
        let hyp = app2(&r, x.clone(), y.clone());
        let concl = app2(&r, Expr::app(fa.clone(), x), Expr::app(fb.clone(), y));
        let body = arrow(&mut fr, hyp, concl);
        pis(vec![(x_id, ta.clone()), (y_id, tb.clone())], body)
    };
    let (hb_id, _) = fr.local();
    let (hs_id, _) = fr.local();
    let concl = {
        let (n_id, n) = fr.local();
        let ia = iter(&mut fr, &ta, &a0, &fa, &n);
        let ib = iter(&mut fr, &tb, &b0, &fb, &n);
        pis(vec![(n_id, nat())], app2(&r, ia, ib))
    };
    pis(
        vec![
            (ta_id, ty1()),
            (tb_id, ty1()),
            (r_id, r_ty),
            (fa_id, fa_ty),
            (fb_id, fb_ty),
            (a0_id, ta),
            (b0_id, tb),
            (hb_id, hb_ty),
            (hs_id, hs_ty),
        ],
        concl,
    )
}

/// The proof of [`names::SIM`]: `Nat.rec` into `Prop` on `n`, the successor
/// case `hs (itA m) (itB m) ih` (its type is the motive at `succ m` by
/// ι-reduction of the iterates).
pub(crate) fn sim_proof() -> Expr {
    let mut fr = Fresh::new();
    let (ta_id, ta) = fr.local();
    let (tb_id, tb) = fr.local();
    let r_ty = {
        let inner = arrow(&mut fr, tb.clone(), prop());
        arrow(&mut fr, ta.clone(), inner)
    };
    let (r_id, r) = fr.local();
    let fa_ty = arrow(&mut fr, ta.clone(), ta.clone());
    let fb_ty = arrow(&mut fr, tb.clone(), tb.clone());
    let (fa_id, fa) = fr.local();
    let (fb_id, fb) = fr.local();
    let (a0_id, a0) = fr.local();
    let (b0_id, b0) = fr.local();
    let hb_ty = app2(&r, a0.clone(), b0.clone());
    let hs_ty = {
        let (x_id, x) = fr.local();
        let (y_id, y) = fr.local();
        let hyp = app2(&r, x.clone(), y.clone());
        let concl = app2(&r, Expr::app(fa.clone(), x), Expr::app(fb.clone(), y));
        let body = arrow(&mut fr, hyp, concl);
        pis(vec![(x_id, ta.clone()), (y_id, tb.clone())], body)
    };
    let (hb_id, hb) = fr.local();
    let (hs_id, hs) = fr.local();
    let (n_id, n) = fr.local();
    let motive = {
        let (m_id, m) = fr.local();
        let ia = iter(&mut fr, &ta, &a0, &fa, &m);
        let ib = iter(&mut fr, &tb, &b0, &fb, &m);
        lams(vec![(m_id, nat())], app2(&r, ia, ib))
    };
    let succ = {
        let (m_id, m) = fr.local();
        let ia = iter(&mut fr, &ta, &a0, &fa, &m);
        let ib = iter(&mut fr, &tb, &b0, &fb, &m);
        let (ih_id, ih) = fr.local();
        let ih_ty = app2(&r, ia.clone(), ib.clone());
        lams(vec![(m_id, nat()), (ih_id, ih_ty)], Expr::apps(hs, [ia, ib, ih]))
    };
    let body = nat_rec_prop(motive, hb, succ, n);
    lams(
        vec![
            (ta_id, ty1()),
            (tb_id, ty1()),
            (r_id, r_ty),
            (fa_id, fa_ty),
            (fb_id, fb_ty),
            (a0_id, ta),
            (b0_id, tb),
            (hb_id, hb_ty),
            (hs_id, hs_ty),
            (n_id, nat()),
        ],
        body,
    )
}

/// How [`names::SIM`] enters a base (tests doctor it).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SimDecl {
    Theorem,
    Axiom,
}

/// The cancel base (strength + `add_sub_cancel`) plus the branch theorems,
/// both audited, plus [`names::SIM`] (audited when `audit`).
pub(crate) fn build_loop_base(sim: SimDecl, audit: bool) -> Result<Environment, String> {
    let mut env = branch_theory::build_base(cancel::cancel_base()?.clone())?;
    add_comm::audit_theorems(&env, &cancel::audited())?;
    let name = Name::from_string(names::SIM);
    let decl = match sim {
        SimDecl::Theorem => Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sim_statement(),
            value: sim_proof(),
        },
        SimDecl::Axiom => Declaration::Axiom { name, level_params: vec![], type_: sim_statement() },
    };
    env.add_decl(decl).map_err(|e| format!("{}: {e:?}", names::SIM))?;
    if audit {
        add_comm::audit_theorems(&env, &[names::SIM])?;
    }
    Ok(env)
}

/// The leaf-free base every loop obligation clones, built and audited once
/// per process (`Err`, and a panic during the build, are kept). Call it on a
/// kernel re-check thread.
pub(crate) fn loop_base() -> Result<&'static Environment, String> {
    static BASE: OnceLock<Result<Environment, String>> = OnceLock::new();
    BASE.get_or_init(|| {
        std::panic::catch_unwind(|| build_loop_base(SimDecl::Theorem, true))
            .unwrap_or_else(|_| Err("the loop base build panicked".to_string()))
    })
    .as_ref()
    .map_err(Clone::clone)
}

// ── the pair ─────────────────────────────────────────────────────────────────

/// The AAPCS64 callee-saved registers every loop pair must carry as frame
/// registers (D8-D15: their low halves).
pub(crate) const REQUIRED_FRAME: [&str; 21] = [
    "SP", "X19", "X20", "X21", "X22", "X23", "X24", "X25", "X26", "X27", "X28", "X29", "X30", "D8",
    "D9", "D10", "D11", "D12", "D13", "D14", "D15",
];
/// Frame registers a pair may carry beyond [`REQUIRED_FRAME`].
const OPTIONAL_FRAME: [&str; 1] = ["X18"];

/// What a machine register is at the header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Role {
    /// Holds IR shared variable `j`; the segment reads it by the IR's cut name.
    Coupled(usize),
    /// The frame register `arch` (an entry of [`REQUIRED_FRAME`] or
    /// `X18`), whose entry value is the leaf `entry`.
    Frame { arch: String, entry: String },
    /// Scratch: read, never related.
    Havoc,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Reg {
    /// The leaf name the header segment reads this register by.
    pub(crate) name: String,
    pub(crate) width: u32,
    pub(crate) role: Role,
}

/// The entry segment's other exit: the direct return that skips the loop.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct EntryPath {
    /// Whether the IR entry segment reaches the header (Bool, entry leaves).
    pub(crate) reach_ir: Formula,
    /// Whether the machine entry segment reaches the header.
    pub(crate) reach_m: Formula,
    /// What the IR returns when it does not.
    pub(crate) ret_ir: Formula,
    /// What the machine returns when it does not.
    pub(crate) ret_m: Formula,
    /// Per frame register (in `regs` order), its value at `ret` on the
    /// direct-return path.
    pub(crate) frame_m: Vec<Formula>,
}

/// One loop's segment Formulas, in the shapes the CER emits. The exit bit,
/// the masked return values and the coverage items are derived from these
/// by [`goal_of`], never taken as given.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct LoopPair {
    /// The IR shared variables at the header: `(cut name, width)`.
    pub(crate) ir_vars: Vec<(String, u32)>,
    /// Their arrival values from the entry segment (over entry leaves).
    pub(crate) entry_ir: Vec<Formula>,
    /// The frozen header step `Ite(c_IR, value, CUT_j)` per variable, one
    /// condition `c_IR` (the segment goes back to the header) for all.
    pub(crate) step_ir: Vec<Formula>,
    /// When the IR header segment reaches `ret` (Bool, over the cut names).
    pub(crate) reach_ret_ir: Formula,
    /// The value the IR header segment returns at `ret`.
    pub(crate) ret_ir: Formula,
    /// The machine state at the header.
    pub(crate) regs: Vec<Reg>,
    /// Each register's value at the header after the entry run.
    pub(crate) entry_m: Vec<Formula>,
    /// Each register after one header segment: `Ite(c_M, value, self)`, or
    /// `self` when the segment leaves it alone, one condition `c_M` for all.
    pub(crate) step_m: Vec<Formula>,
    /// When the machine header segment reaches `ret`.
    pub(crate) reach_ret_m: Formula,
    /// The value the machine returns at `ret` (the return register).
    pub(crate) ret_m: Formula,
    /// Per frame register (in `regs` order), its value at `ret` on the exit path.
    pub(crate) exit_frame_m: Vec<Formula>,
    /// The entry segment's direct-return path.
    pub(crate) entry: EntryPath,
}

// ── Formula helpers (the spike's fragment) ───────────────────────────────────

fn bin(f: &Formula) -> Option<(&Formula, &Formula)> {
    match f {
        Formula::Eq(l, r)
        | Formula::BvAdd(l, r, _)
        | Formula::BvSub(l, r, _)
        | Formula::BvMul(l, r, _)
        | Formula::BvUDiv(l, r, _)
        | Formula::BvAnd(l, r, _)
        | Formula::BvOr(l, r, _)
        | Formula::BvXor(l, r, _)
        | Formula::BvShl(l, r, _)
        | Formula::BvLShr(l, r, _)
        | Formula::BvULt(l, r, _)
        | Formula::BvULe(l, r, _)
        | Formula::BvSLt(l, r, _) => Some((l, r)),
        _ => None,
    }
}

/// The bit-vector variables of `f`, first occurrence first.
fn vars(f: &Formula, out: &mut Vec<(String, u32)>) -> Result<(), String> {
    match f {
        Formula::Var(n, Sort::BitVec(w)) => {
            if !out.iter().any(|(m, v)| m == n && v == w) {
                out.push((n.clone(), *w));
            }
            Ok(())
        }
        Formula::Bool(_) | Formula::BitVec { .. } => Ok(()),
        Formula::Not(x) | Formula::BvZeroExt(x, _) | Formula::BvExtract { inner: x, .. } => {
            vars(x, out)
        }
        Formula::And(xs) | Formula::Or(xs) => xs.iter().try_for_each(|x| vars(x, out)),
        Formula::Ite(c, a, e) => {
            vars(c, out)?;
            vars(a, out)?;
            vars(e, out)
        }
        _ => {
            let (l, r) = bin(f).ok_or_else(|| format!("loop: node outside the fragment: {f:?}"))?;
            vars(l, out)?;
            vars(r, out)
        }
    }
}

fn vars_of(f: &Formula) -> Result<Vec<(String, u32)>, String> {
    let mut out = Vec::new();
    vars(f, &mut out)?;
    Ok(out)
}

fn has_ite(f: &Formula) -> bool {
    match f {
        Formula::Ite(..) => true,
        Formula::Not(x) | Formula::BvZeroExt(x, _) | Formula::BvExtract { inner: x, .. } => {
            has_ite(x)
        }
        Formula::And(xs) | Formula::Or(xs) => xs.iter().any(has_ite),
        _ => bin(f).is_some_and(|(l, r)| has_ite(l) || has_ite(r)),
    }
}

/// `f` with each variable named in `m` replaced (Formula level).
fn subst_formula(f: &Formula, m: &HashMap<String, Formula>) -> Result<Formula, String> {
    let b = |x: &Formula| subst_formula(x, m).map(Box::new);
    Ok(match f {
        Formula::Var(n, _) => m.get(n).cloned().unwrap_or_else(|| f.clone()),
        Formula::Bool(_) | Formula::BitVec { .. } => f.clone(),
        Formula::Not(x) => Formula::Not(b(x)?),
        Formula::BvZeroExt(x, k) => Formula::BvZeroExt(b(x)?, *k),
        Formula::BvExtract { inner, high, low } => {
            Formula::BvExtract { inner: b(inner)?, high: *high, low: *low }
        }
        Formula::And(xs) => {
            Formula::And(xs.iter().map(|x| subst_formula(x, m)).collect::<Result<_, _>>()?)
        }
        Formula::Or(xs) => {
            Formula::Or(xs.iter().map(|x| subst_formula(x, m)).collect::<Result<_, _>>()?)
        }
        Formula::Ite(c, a, e) => Formula::Ite(b(c)?, b(a)?, b(e)?),
        Formula::Eq(l, r) => Formula::Eq(b(l)?, b(r)?),
        Formula::BvAdd(l, r, w) => Formula::BvAdd(b(l)?, b(r)?, *w),
        Formula::BvSub(l, r, w) => Formula::BvSub(b(l)?, b(r)?, *w),
        Formula::BvMul(l, r, w) => Formula::BvMul(b(l)?, b(r)?, *w),
        Formula::BvUDiv(l, r, w) => Formula::BvUDiv(b(l)?, b(r)?, *w),
        Formula::BvAnd(l, r, w) => Formula::BvAnd(b(l)?, b(r)?, *w),
        Formula::BvOr(l, r, w) => Formula::BvOr(b(l)?, b(r)?, *w),
        Formula::BvXor(l, r, w) => Formula::BvXor(b(l)?, b(r)?, *w),
        Formula::BvShl(l, r, w) => Formula::BvShl(b(l)?, b(r)?, *w),
        Formula::BvLShr(l, r, w) => Formula::BvLShr(b(l)?, b(r)?, *w),
        Formula::BvULt(l, r, w) => Formula::BvULt(b(l)?, b(r)?, *w),
        Formula::BvULe(l, r, w) => Formula::BvULe(b(l)?, b(r)?, *w),
        Formula::BvSLt(l, r, w) => Formula::BvSLt(b(l)?, b(r)?, *w),
        _ => return Err(format!("loop: node outside the fragment: {f:?}")),
    })
}

fn bv(name: &str, w: u32) -> Formula {
    Formula::Var(name.to_string(), Sort::BitVec(w))
}

/// A cut or havoc name: never declared as a leaf.
fn is_step_name(n: &str) -> bool {
    n.starts_with("CUT_") || n.contains("_HAVOC")
}

/// The width of a bit-vector Formula of the spike's fragment.
fn width(f: &Formula) -> Option<u32> {
    match f {
        Formula::Var(_, Sort::BitVec(w)) | Formula::BitVec { width: w, .. } => Some(*w),
        Formula::Ite(_, a, _) => width(a),
        Formula::BvAdd(_, _, w)
        | Formula::BvSub(_, _, w)
        | Formula::BvMul(_, _, w)
        | Formula::BvUDiv(_, _, w)
        | Formula::BvAnd(_, _, w)
        | Formula::BvOr(_, _, w)
        | Formula::BvXor(_, _, w)
        | Formula::BvShl(_, _, w)
        | Formula::BvLShr(_, _, w) => Some(*w),
        _ => None,
    }
}

fn lit(value: i128, width: u32) -> Formula {
    Formula::BitVec { value, width }
}

/// `Ite(c, 1, 0)` at one bit.
fn bit(c: &Formula) -> Formula {
    Formula::Ite(Box::new(c.clone()), Box::new(lit(1, 1)), Box::new(lit(0, 1)))
}

/// `Ite(c, 0, ret)`: the value returned when the segment does not go on.
fn masked(c: &Formula, ret: &Formula) -> Result<Formula, String> {
    let w = width(ret).ok_or("loop: a return value has no width")?;
    Ok(Formula::Ite(Box::new(c.clone()), Box::new(lit(0, w)), Box::new(ret.clone())))
}

/// `[bit(c ∨ reach_ret) = 1, bit(c ∧ reach_ret) = 0]`.
fn coverage(c: &Formula, reach_ret: &Formula) -> Vec<(Formula, Formula)> {
    vec![
        (bit(&Formula::Or(vec![c.clone(), reach_ret.clone()])), lit(1, 1)),
        (bit(&Formula::And(vec![c.clone(), reach_ret.clone()])), lit(0, 1)),
    ]
}

/// The one condition every step branches on: each step must be
/// `Ite(c, value, self)` (or `self` when `plain` allows it), `self` the
/// variable the step updates.
fn step_condition(
    steps: &[Formula],
    selves: &[(String, u32)],
    plain: bool,
) -> Result<Formula, String> {
    let mut cond: Option<&Formula> = None;
    for (f, (n, w)) in steps.iter().zip(selves) {
        let me = bv(n, *w);
        match f {
            Formula::Ite(c, _, e) if **e == me => {
                if cond.is_some_and(|c0| c0 != &**c) {
                    return Err("loop: the steps branch on different conditions".into());
                }
                cond = Some(&**c);
            }
            _ if plain && *f == me => {}
            _ => return Err(format!("loop: the step of {n} is not Ite(c, value, {n})")),
        }
    }
    cond.cloned().ok_or_else(|| "loop: no step branches".into())
}

/// The observations and coverage items [`goal_of`] derives from a pair.
struct Derived {
    cond_ir: Formula,
    cond_m: Formula,
    out_ir: Formula,
    out_m: Formula,
    cover_ir: Vec<(Formula, Formula)>,
    cover_m: Vec<(Formula, Formula)>,
    entry_items: Vec<(Formula, Formula)>,
}

// ── kernel term helpers ──────────────────────────────────────────────────────

/// `bvfEval R(f)` under `ReflectCtx::branching_goal`, inside the branch
/// width walk (`branch_split::goal_of` on `(f, f)`).
fn eval_of(f: &Formula) -> Result<Expr, String> {
    let (_, sides, _) = branch_split::goal_of(&[(f.clone(), f.clone())])?;
    sides.into_iter().next().map(|(l, _)| l).ok_or_else(|| "loop: empty reflection".into())
}

/// `bvfEval R(l) = bvfEval R(r)`, both sides inside the walk at one width.
fn statement(l: &Formula, r: &Formula) -> Result<Expr, String> {
    Ok(branch_split::goal_of(&[(l.clone(), r.clone())])?.0)
}

fn conj(props: &[Expr]) -> Expr {
    let (last, init) = props.split_last().expect("a conjunction has a conjunct");
    init.iter()
        .rev()
        .fold(last.clone(), |acc, p| Expr::apps(Expr::const_str("And"), [p.clone(), acc]))
}

fn conj_intro(props: &[Expr], proofs: Vec<Expr>) -> Expr {
    assert_eq!(props.len(), proofs.len(), "one proof per conjunct");
    let mut proofs = proofs;
    let mut acc = proofs.pop().expect("a conjunction has a conjunct");
    for i in (0..props.len() - 1).rev() {
        let p = proofs.pop().expect("one proof per conjunct");
        acc = Expr::apps(
            Expr::const_str("And.intro"),
            [props[i].clone(), conj(&props[i + 1..]), p, acc],
        );
    }
    acc
}

/// Conjunct `i` of `h : conj props`.
fn conj_get(props: &[Expr], h: &Expr, i: usize) -> Expr {
    let mut cur = h.clone();
    for t in 0..i {
        cur = Expr::apps(
            Expr::const_str("And.right"),
            [props[t].clone(), conj(&props[t + 1..]), cur],
        );
    }
    if i + 1 == props.len() {
        cur
    } else {
        Expr::apps(Expr::const_str("And.left"), [props[i].clone(), conj(&props[i + 1..]), cur])
    }
}

fn prod_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::zero(), Level::zero()])
}

/// `Prod LB (Prod LB (… LB))` with `n` components (`LB` when `n = 1`).
fn state_ty(n: usize) -> Expr {
    let mut t = lb();
    for _ in 1..n {
        t = Expr::apps(prod_const("Prod"), [lb(), t]);
    }
    t
}

fn state_mk(vals: Vec<Expr>) -> Expr {
    let mut it = vals.into_iter().rev();
    let mut acc = it.next().expect("a state has a component");
    let mut ty = lb();
    for v in it {
        acc = Expr::apps(prod_const("Prod.mk"), [lb(), ty.clone(), v, acc]);
        ty = Expr::apps(prod_const("Prod"), [lb(), ty]);
    }
    acc
}

fn state_proj(n: usize, j: usize, x: &Expr) -> Expr {
    if n == 1 {
        return x.clone();
    }
    let mut cur = x.clone();
    for _ in 0..j {
        cur = Expr::proj(Name::from_string("Prod"), 1, cur);
    }
    if j + 1 == n { cur } else { Expr::proj(Name::from_string("Prod"), 0, cur) }
}

/// The bit constants of the leaf `(name, w)`, least significant first, read
/// off `add_comm::bit_leaf` itself.
fn bit_consts(name: &str, w: u32) -> Vec<Name> {
    let mut out = Vec::new();
    let mut e = add_comm::bit_leaf(name, w);
    loop {
        let (head, tail) = {
            let args = e.get_app_args();
            if args.len() != 3 {
                break;
            }
            (args[1].clone(), args[2].clone())
        };
        if let clean_kernel::ExprKind::Const(n, _) = head.kind() {
            out.push(n.clone());
        }
        e = tail;
    }
    out
}

/// A substitution: leaf `(name, w)` ↦ the list term its bits are read from.
type Sigma = Vec<(String, u32, Expr)>;

struct Subst {
    consts: HashMap<Name, Expr>,
    fvars: Vec<(FVarId, Expr)>,
    cache: HashMap<usize, (Arc<Expr>, Option<Arc<Expr>>)>,
}

impl ExprFolderOpt for Subst {
    fn fold_const_opt(&mut self, name: &Name, levels: &LevelVec) -> Option<Expr> {
        if !levels.is_empty() {
            return None;
        }
        self.consts.get(name).cloned()
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        self.fvars.iter().find(|(v, _)| *v == id).map(|(_, e)| e.clone())
    }
    // Every replacement is closed under binders, so a result depends only on
    // the node: memoize on the node's address to keep the walk linear in the DAG.
    fn fold_expr_arc_opt(&mut self, e: &Arc<Expr>) -> Option<Arc<Expr>> {
        let key = Arc::as_ptr(e) as usize;
        if let Some((_, r)) = self.cache.get(&key) {
            return r.clone();
        }
        let r = self.fold_expr_opt(e).map(Arc::new);
        self.cache.insert(key, (e.clone(), r.clone()));
        r
    }
}

/// Replace each bit constant `BVC_LEAFBIT_{name}_{w}_{k}` of each leaf in
/// `s` by `bhead (btail^k y)`, so the leaf's spine becomes `fit_w y`. Syntax
/// only: the kernel re-checks every term this produces.
pub(crate) fn substitute(e: &Expr, s: &[(String, u32, Expr)]) -> Expr {
    let mut consts = HashMap::new();
    for (name, w, y) in s {
        let mut t = y.clone();
        for c in bit_consts(name, *w) {
            consts.insert(c, bhead(t.clone()));
            t = btail(t);
        }
    }
    e.fold_opt_or_clone(&mut Subst { consts, fvars: Vec::new(), cache: HashMap::new() })
}

fn replace_fvars(e: &Expr, fvars: &[(FVarId, Expr)]) -> Expr {
    e.fold_opt_or_clone(&mut Subst {
        consts: HashMap::new(),
        fvars: fvars.to_vec(),
        cache: HashMap::new(),
    })
}

// ── per-item proofs ──────────────────────────────────────────────────────────

/// A proof of `statement(l, r)` over leaf constants.
fn item_proof(l: &Formula, r: &Formula, filter: LoopFilter) -> Result<Expr, Decline> {
    let goal = statement(l, r).map_err(Decline::Filter)?;
    let (gl, gr) = {
        let (_, sides, _) =
            branch_split::goal_of(&[(l.clone(), r.clone())]).map_err(Decline::Filter)?;
        sides.into_iter().next().ok_or_else(|| Decline::Filter("loop: empty".into()))?
    };
    let refl = kterm::refl(lb(), gl.clone());
    // (a) the reflections are one term.
    if gl == gr {
        return Ok(refl);
    }
    // (a') a closed 1-bit item: the kernel decides it by evaluation.
    let closed = vars_of(l).is_ok_and(|v| v.is_empty()) && vars_of(r).is_ok_and(|v| v.is_empty());
    if closed && branch_split::goal_of(&[(l.clone(), l.clone())]).is_ok() && one_bit(l) {
        return Ok(refl);
    }
    let checked = |g: &Expr, p: Expr| -> Option<Expr> {
        (filter == LoopFilter::Off || *g == goal).then_some(p)
    };
    // (b) the branch split.
    if has_ite(l) || has_ite(r) {
        let bf = if filter == LoopFilter::On { BranchFilter::On } else { BranchFilter::Off };
        if let Ok(o) = branch_split::obligation(&[(l.clone(), r.clone())], bf)
            && let Some(p) = checked(&o.goal, o.proof)
        {
            return Ok(p);
        }
    } else {
        // (c) strength, then cancel.
        let sf = if filter == LoopFilter::On { StrengthFilter::On } else { StrengthFilter::Off };
        if let Some(o) = strength_obligation(l, r, sf)
            && filter == LoopFilter::On
            && let Some(p) = checked(&o.goal, o.discharge)
        {
            return Ok(p);
        }
        let cf = if filter == LoopFilter::On { CancelFilter::On } else { CancelFilter::Off };
        if let Some(o) = cancel_obligation(l, r, cf)
            && let Some(p) = checked(&o.goal, o.discharge)
        {
            return Ok(p);
        }
    }
    match filter {
        LoopFilter::On => {
            Err(Decline::Filter(format!("loop: no composing route proves {l:?} = {r:?}")))
        }
        // Off: hand the kernel a term anyway.
        LoopFilter::Off => Ok(refl),
    }
}

fn one_bit(f: &Formula) -> bool {
    match f {
        Formula::BitVec { width, .. } => *width == 1,
        Formula::Ite(_, a, _) => one_bit(a),
        _ => false,
    }
}

// ── the model: every term, built from the Formulas ───────────────────────────

/// Test-only forgeries (N7).
#[derive(Clone, Debug, Default)]
pub(crate) struct Knobs {
    /// Leave this IR cut variable's bit constants in the step's coupled proofs.
    pub(crate) keep_cut: Option<String>,
}

struct Model<'p> {
    p: &'p LoopPair,
    d: Derived,
    k: usize,
    m: usize,
    loc: Vec<usize>,
    frames: Vec<usize>,
    /// The entry leaves, in order: the binders `κ`.
    entry: Vec<(String, u32)>,
    kappa: Vec<(FVarId, Expr)>,
    a_ty: Expr,
    b_ty: Expr,
    fr: Fresh,
}

/// What [`shape`] returns: `loc`, the frame indices, the entry leaves.
type Shaped = (Vec<usize>, Vec<usize>, Vec<(String, u32)>);

/// The goal-shaping checks (never bypassed): shapes, names, widths, the
/// frame set, the step forms.
fn shape(p: &LoopPair) -> Result<Shaped, String> {
    let k = p.ir_vars.len();
    let m = p.regs.len();
    if k == 0 || m == 0 || p.entry_ir.len() != k || p.step_ir.len() != k {
        return Err("loop: IR state shape".into());
    }
    if p.entry_m.len() != m || p.step_m.len() != m {
        return Err("loop: machine state shape".into());
    }
    let mut step_names: Vec<(String, u32)> = Vec::new();
    for (n, w) in &p.ir_vars {
        if !n.starts_with("CUT_") || step_names.iter().any(|(x, _)| x == n) {
            return Err(format!("loop: IR cut name {n}"));
        }
        step_names.push((n.clone(), *w));
    }
    let ir_names = step_names.clone();
    let mut loc = vec![usize::MAX; k];
    let mut frames = Vec::new();
    let mut frame_entries: Vec<(String, u32)> = Vec::new();
    let mut archs: Vec<&str> = Vec::new();
    for (i, r) in p.regs.iter().enumerate() {
        match &r.role {
            Role::Coupled(j) => {
                if *j >= k || loc[*j] != usize::MAX || p.ir_vars[*j] != (r.name.clone(), r.width) {
                    return Err(format!("loop: coupled register {}", r.name));
                }
                loc[*j] = i;
            }
            Role::Frame { arch, entry } => {
                let known = REQUIRED_FRAME.contains(&arch.as_str())
                    || OPTIONAL_FRAME.contains(&arch.as_str());
                if !known
                    || archs.contains(&arch.as_str())
                    || !r.name.starts_with("CUT_")
                    || is_step_name(entry)
                    || frame_entries.iter().any(|(e, _)| e == entry)
                    || step_names.iter().any(|(x, _)| *x == r.name)
                {
                    return Err(format!("loop: frame register {} ({arch})", r.name));
                }
                archs.push(arch.as_str());
                frames.push(i);
                frame_entries.push((entry.clone(), r.width));
                step_names.push((r.name.clone(), r.width));
            }
            Role::Havoc => {
                if !r.name.ends_with("_HAVOC")
                    || r.name.starts_with("CUT_")
                    || step_names.iter().any(|(x, _)| *x == r.name)
                {
                    return Err(format!("loop: havoc register {}", r.name));
                }
                step_names.push((r.name.clone(), r.width));
            }
        }
    }
    if loc.contains(&usize::MAX) {
        return Err("loop: an IR variable has no register".into());
    }
    if let Some(missing) = REQUIRED_FRAME.iter().find(|a| !archs.contains(*a)) {
        return Err(format!("loop: the frame lacks {missing}"));
    }
    if p.exit_frame_m.len() != frames.len() || p.entry.frame_m.len() != frames.len() {
        return Err("loop: frame observation shape".into());
    }
    let within = |f: &Formula, allowed: &[(String, u32)]| -> Result<(), String> {
        for v in vars_of(f)? {
            if !allowed.contains(&v) {
                return Err(format!("loop: {} is not a leaf of this segment", v.0));
            }
        }
        Ok(())
    };
    for f in p.step_ir.iter().chain([&p.reach_ret_ir, &p.ret_ir]) {
        within(f, &ir_names)?;
    }
    let m_side = p.step_m.iter().chain([&p.reach_ret_m, &p.ret_m]).chain(&p.exit_frame_m);
    for f in m_side {
        within(f, &step_names)?;
    }
    // The declared leaves: entry names only, disjoint from cut and havoc names.
    let mut entry: Vec<(String, u32)> = Vec::new();
    let e = &p.entry;
    let entry_side = p.entry_ir.iter().chain(&p.entry_m).chain(&e.frame_m);
    for f in entry_side.chain([&e.reach_ir, &e.reach_m, &e.ret_ir, &e.ret_m]) {
        vars(f, &mut entry)?;
    }
    for fe in frame_entries {
        if !entry.contains(&fe) {
            entry.push(fe);
        }
    }
    for (n, w) in &entry {
        if is_step_name(n) || entry.iter().any(|(x, v)| x == n && v != w) {
            return Err(format!("loop: {n} cannot be a declared entry leaf"));
        }
    }
    Ok((loc, frames, entry))
}

/// The exit bit, the masked returns, the coverage and the entry items,
/// derived from the step's own conditions (never bypassed).
fn derive(p: &LoopPair, frames: &[usize]) -> Result<Derived, String> {
    let selves_m: Vec<(String, u32)> = p.regs.iter().map(|r| (r.name.clone(), r.width)).collect();
    let c_ir = step_condition(&p.step_ir, &p.ir_vars, false)?;
    let c_m = step_condition(&p.step_m, &selves_m, true)?;
    let (wr, wm) = (width(&p.ret_ir), width(&p.ret_m));
    if wr.is_none() || wr != wm {
        return Err("loop: the IR and machine return values differ in width".into());
    }
    let e = &p.entry;
    let (er, em) = (width(&e.ret_ir), width(&e.ret_m));
    if er.is_none() || er != em {
        return Err("loop: the direct-return values differ in width".into());
    }
    let mut entry_items = vec![
        (bit(&e.reach_ir), bit(&e.reach_m)),
        (masked(&e.reach_ir, &e.ret_ir)?, masked(&e.reach_m, &e.ret_m)?),
    ];
    for (t, &fi) in frames.iter().enumerate() {
        let Role::Frame { entry, .. } = &p.regs[fi].role else {
            return Err("loop: not a frame register".into());
        };
        entry_items.push((e.frame_m[t].clone(), bv(entry, p.regs[fi].width)));
    }
    Ok(Derived {
        cond_ir: bit(&c_ir),
        cond_m: bit(&c_m),
        out_ir: masked(&c_ir, &p.ret_ir)?,
        out_m: masked(&c_m, &p.ret_m)?,
        cover_ir: coverage(&c_ir, &p.reach_ret_ir),
        cover_m: coverage(&c_m, &p.reach_ret_m),
        entry_items,
    })
}

impl<'p> Model<'p> {
    fn new(p: &'p LoopPair) -> Result<Self, String> {
        let (loc, frames, entry) = shape(p)?;
        let d = derive(p, &frames)?;
        let mut fr = Fresh::new();
        let kappa = entry.iter().map(|_| fr.local()).collect::<Vec<_>>();
        let (k, m) = (p.ir_vars.len(), p.regs.len());
        Ok(Self { p, d, k, m, loc, frames, entry, kappa, a_ty: state_ty(k), b_ty: state_ty(m), fr })
    }

    fn s_kappa(&self) -> Sigma {
        self.entry
            .iter()
            .zip(&self.kappa)
            .map(|((n, w), (_, v))| (n.clone(), *w, v.clone()))
            .collect()
    }
    fn s_ir(&self, a: &Expr) -> Sigma {
        let k = self.k;
        self.p
            .ir_vars
            .iter()
            .enumerate()
            .map(|(j, (n, w))| (n.clone(), *w, state_proj(k, j, a)))
            .collect()
    }
    /// The machine-only leaves (frame and havoc registers) read from `b`.
    fn s_mach(&self, b: &Expr) -> Sigma {
        let m = self.m;
        self.p
            .regs
            .iter()
            .enumerate()
            .filter(|(_, r)| !matches!(r.role, Role::Coupled(_)))
            .map(|(i, r)| (r.name.clone(), r.width, state_proj(m, i, b)))
            .collect()
    }
    fn s_b(&self, b: &Expr) -> Sigma {
        let mut s = self.s_mach(b);
        for (j, (n, w)) in self.p.ir_vars.iter().enumerate() {
            s.push((n.clone(), *w, state_proj(self.m, self.loc[j], b)));
        }
        s
    }
    fn s_joint(&self, a: &Expr, b: &Expr) -> Sigma {
        let mut s = self.s_ir(a);
        s.extend(self.s_mach(b));
        s
    }

    /// `Ψ_f κ`: the entry segment's value of frame register `i`.
    fn psi(&self, i: usize) -> Result<Expr, String> {
        Ok(substitute(&eval_of(&self.p.entry_m[i])?, &self.s_kappa()))
    }
    fn frame_entry(&self, i: usize) -> Result<Formula, String> {
        match &self.p.regs[i].role {
            Role::Frame { entry, .. } => Ok(bv(entry, self.p.regs[i].width)),
            _ => Err("loop: not a frame register".into()),
        }
    }

    fn a0(&self) -> Result<Expr, String> {
        let s = self.s_kappa();
        let vals = self.p.entry_ir.iter().map(|f| Ok(substitute(&eval_of(f)?, &s)));
        Ok(state_mk(vals.collect::<Result<_, String>>()?))
    }
    fn b0(&self) -> Result<Expr, String> {
        let s = self.s_kappa();
        let vals = self.p.entry_m.iter().map(|f| Ok(substitute(&eval_of(f)?, &s)));
        Ok(state_mk(vals.collect::<Result<_, String>>()?))
    }
    fn fa(&mut self) -> Result<Expr, String> {
        let (a_id, a) = self.fr.local();
        let s = self.s_ir(&a);
        let vals = self.p.step_ir.iter().map(|f| Ok(substitute(&eval_of(f)?, &s)));
        Ok(lams(vec![(a_id, self.a_ty.clone())], state_mk(vals.collect::<Result<_, String>>()?)))
    }
    fn fb(&mut self) -> Result<Expr, String> {
        let (b_id, b) = self.fr.local();
        let s = self.s_b(&b);
        let vals = self.p.step_m.iter().map(|f| Ok(substitute(&eval_of(f)?, &s)));
        Ok(lams(vec![(b_id, self.b_ty.clone())], state_mk(vals.collect::<Result<_, String>>()?)))
    }

    fn rel_props(&self, a: &Expr, b: &Expr) -> Result<Vec<Expr>, String> {
        let mut out = Vec::new();
        for j in 0..self.k {
            out.push(kx::eq_list(state_proj(self.k, j, a), state_proj(self.m, self.loc[j], b)));
        }
        for &f in &self.frames {
            out.push(kx::eq_list(state_proj(self.m, f, b), self.psi(f)?));
        }
        Ok(out)
    }
    fn rel(&mut self) -> Result<Expr, String> {
        let (a_id, a) = self.fr.local();
        let (b_id, b) = self.fr.local();
        let body = conj(&self.rel_props(&a, &b)?);
        Ok(lams(vec![(a_id, self.a_ty.clone()), (b_id, self.b_ty.clone())], body))
    }

    fn obs_props(&self, a: &Expr, b: &Expr) -> Result<Vec<Expr>, String> {
        let (sa, sb) = (self.s_ir(a), self.s_b(b));
        let mut out = vec![
            kx::eq_list(
                substitute(&eval_of(&self.d.cond_ir)?, &sa),
                substitute(&eval_of(&self.d.cond_m)?, &sb),
            ),
            kx::eq_list(
                substitute(&eval_of(&self.d.out_ir)?, &sa),
                substitute(&eval_of(&self.d.out_m)?, &sb),
            ),
        ];
        for (t, &f) in self.frames.iter().enumerate() {
            out.push(kx::eq_list(
                substitute(&eval_of(&self.p.exit_frame_m[t])?, &sb),
                substitute(&eval_of(&self.frame_entry(f)?)?, &self.s_kappa()),
            ));
        }
        Ok(out)
    }
    fn obs(&mut self) -> Result<Expr, String> {
        let (a_id, a) = self.fr.local();
        let (b_id, b) = self.fr.local();
        let body = conj(&self.obs_props(&a, &b)?);
        Ok(lams(vec![(a_id, self.a_ty.clone()), (b_id, self.b_ty.clone())], body))
    }

    fn items_props(items: &[(Formula, Formula)], s: &Sigma) -> Result<Vec<Expr>, String> {
        items.iter().map(|(l, r)| Ok(substitute(&statement(l, r)?, s))).collect()
    }
    fn entry_items(&self) -> Vec<(Formula, Formula)> {
        self.d.entry_items.clone()
    }

    /// Every statement, closed over `κ` (fvars).
    fn statements(&mut self) -> Result<Statements, String> {
        let (fa, fb, rel, obs) = (self.fa()?, self.fb()?, self.rel()?, self.obs()?);
        let (a0, b0) = (self.a0()?, self.b0()?);
        let kap = self.kappa.clone();
        let entry = conj(&Self::items_props(&self.entry_items(), &self.s_kappa())?);
        let cov_ir = {
            let (a_id, a) = self.fr.local();
            let props = Self::items_props(&self.d.cover_ir, &self.s_ir(&a))?;
            pis(vec![(a_id, self.a_ty.clone())], conj(&props))
        };
        let cov_m = {
            let (b_id, b) = self.fr.local();
            let props = Self::items_props(&self.d.cover_m, &self.s_b(&b))?;
            pis(vec![(b_id, self.b_ty.clone())], conj(&props))
        };
        let base = app2(&rel, a0.clone(), b0.clone());
        let (a_id, a) = self.fr.local();
        let (b_id, b) = self.fr.local();
        let (h_id, _) = self.fr.local();
        let hyp = app2(&rel, a.clone(), b.clone());
        let tele = |extra: Vec<(FVarId, Expr)>| {
            let mut v = kap.clone().into_iter().map(|(id, _)| (id, lb())).collect::<Vec<_>>();
            v.extend(extra);
            v
        };
        let ab = vec![(a_id, self.a_ty.clone()), (b_id, self.b_ty.clone()), (h_id, hyp)];
        let step = pis(
            tele(ab.clone()),
            app2(&rel, Expr::app(fa.clone(), a.clone()), Expr::app(fb.clone(), b.clone())),
        );
        let obs_ty = pis(tele(ab), app2(&obs, a, b));
        Ok(Statements {
            fa,
            fb,
            rel,
            obs,
            a0,
            b0,
            entry_ty: pis(tele(vec![]), entry.clone()),
            entry,
            cov_ir,
            cov_m,
            base_ty: pis(tele(vec![]), base),
            step_ty: step,
            obs_ty,
        })
    }

    /// `G` with `κ := bit_leaf(entry)`, and the pieces the discharge needs.
    fn goal(&mut self, st: &Statements) -> GoalParts {
        let kg: Vec<Expr> = self.entry.iter().map(|(n, w)| add_comm::bit_leaf(n, *w)).collect();
        let inst_map: Vec<(FVarId, Expr)> =
            self.kappa.iter().zip(&kg).map(|((id, _), e)| (*id, e.clone())).collect();
        let inst = |e: &Expr| replace_fvars(e, &inst_map);
        let (rel, obs, a0, b0) = (inst(&st.rel), inst(&st.obs), inst(&st.a0), inst(&st.b0));
        let (n_id, n) = self.fr.local();
        let ita = iter(&mut self.fr, &self.a_ty, &a0, &st.fa, &n);
        let itb = iter(&mut self.fr, &self.b_ty, &b0, &st.fb, &n);
        let loop_ty = pis(vec![(n_id, nat())], app2(&obs, ita.clone(), itb.clone()));
        let props = vec![inst(&st.entry), st.cov_ir.clone(), st.cov_m.clone(), loop_ty];
        GoalParts { goal: conj(&props), props, kg, rel, a0, b0, n_id, n, ita, itb }
    }

    // ── the lemma proofs ──

    /// `joint` item `l = r` (IR left, machine right) at `(a, b)` under `h`:
    /// substitute, then rewrite each coupled leaf the machine side reads from
    /// `proj_j a` to `proj_{loc j} b` by `Eq.subst`.
    fn joint(
        &mut self,
        raw: &Expr,
        l: &Formula,
        r: &Formula,
        ab: (&Expr, &Expr),
        h: (&Expr, &[Expr]),
        keep_cut: Option<&str>,
    ) -> Result<Expr, String> {
        let (a, b) = ab;
        let left = substitute(&eval_of(l)?, &self.s_ir(a));
        let rv = eval_of(r)?;
        let mut s = self.s_joint(a, b);
        if let Some(name) = keep_cut {
            s.retain(|(n, _, _)| n != name);
        }
        let mut pi = substitute(raw, &s);
        let rvars = vars_of(r)?;
        for i in 0..self.k {
            let (name, _) = &self.p.ir_vars[i];
            if !rvars.iter().any(|(n, _)| n == name) {
                continue;
            }
            let (y_id, y) = self.fr.local();
            let mut s = self.s_mach(b);
            for (i2, (n2, w2)) in self.p.ir_vars.iter().enumerate() {
                let tgt = match i2.cmp(&i) {
                    std::cmp::Ordering::Less => state_proj(self.m, self.loc[i2], b),
                    std::cmp::Ordering::Equal => y.clone(),
                    std::cmp::Ordering::Greater => state_proj(self.k, i2, a),
                };
                s.push((n2.clone(), *w2, tgt));
            }
            let motive = lams(vec![(y_id, lb())], kx::eq_list(left.clone(), substitute(&rv, &s)));
            pi = kterm::eq_subst(
                lb(),
                motive,
                state_proj(self.k, i, a),
                state_proj(self.m, self.loc[i], b),
                conj_get(h.1, h.0, i),
                pi,
            );
        }
        Ok(pi)
    }

    fn proofs(
        &mut self,
        filter: LoopFilter,
        knobs: &Knobs,
        st: &Statements,
    ) -> Result<Vec<Lemma>, Decline> {
        let f = |e: String| Decline::Filter(e);
        let p = self.p;
        let kap_bind: Vec<(FVarId, Expr)> = self.kappa.iter().map(|(id, _)| (*id, lb())).collect();
        let sk = self.s_kappa();
        let mut lemmas = Vec::new();

        // entry
        let items = self.entry_items();
        let props = Self::items_props(&items, &sk).map_err(f)?;
        let mut pfs = Vec::new();
        for (l, r) in &items {
            pfs.push(substitute(&item_proof(l, r, filter)?, &sk));
        }
        lemmas.push(Lemma::new(
            names::ENTRY,
            st.entry_ty.clone(),
            lams(kap_bind.clone(), conj_intro(&props, pfs)),
        ));

        // coverage
        let covers = [
            (names::COV_IR, self.d.cover_ir.clone(), true),
            (names::COV_M, self.d.cover_m.clone(), false),
        ];
        for (name, items, ir_side) in covers {
            let (x_id, x) = self.fr.local();
            let (s, ty) = if ir_side {
                (self.s_ir(&x), self.a_ty.clone())
            } else {
                (self.s_b(&x), self.b_ty.clone())
            };
            let props = Self::items_props(&items, &s).map_err(f)?;
            let mut pfs = Vec::new();
            for (l, r) in &items {
                pfs.push(substitute(&item_proof(l, r, filter)?, &s));
            }
            let stmt = if ir_side { st.cov_ir.clone() } else { st.cov_m.clone() };
            lemmas.push(Lemma::new(name, stmt, lams(vec![(x_id, ty)], conj_intro(&props, pfs))));
        }

        // base
        let props = self.rel_props(&st.a0, &st.b0).map_err(f)?;
        let mut pfs = Vec::new();
        for j in 0..self.k {
            let raw = item_proof(&p.entry_ir[j], &p.entry_m[self.loc[j]], filter)?;
            pfs.push(substitute(&raw, &sk));
        }
        for &fi in &self.frames {
            pfs.push(kterm::refl(lb(), self.psi(fi).map_err(f)?));
        }
        lemmas.push(Lemma::new(
            names::BASE,
            st.base_ty.clone(),
            lams(kap_bind.clone(), conj_intro(&props, pfs)),
        ));

        // step and obs share the binders (κ, a, b, h)
        let (a_id, a) = self.fr.local();
        let (b_id, b) = self.fr.local();
        let (h_id, h) = self.fr.local();
        let hprops = self.rel_props(&a, &b).map_err(f)?;
        let mut binders = kap_bind.clone();
        binders.push((a_id, self.a_ty.clone()));
        binders.push((b_id, self.b_ty.clone()));
        binders.push((h_id, app2(&st.rel, a.clone(), b.clone())));

        let fa_a = Expr::app(st.fa.clone(), a.clone());
        let fb_b = Expr::app(st.fb.clone(), b.clone());
        let props = self.rel_props(&fa_a, &fb_b).map_err(f)?;
        let mut pfs = Vec::new();
        for j in 0..self.k {
            let (l, r) = (&p.step_ir[j], &p.step_m[self.loc[j]]);
            let raw = item_proof(l, r, filter)?;
            let keep = knobs.keep_cut.as_deref();
            pfs.push(self.joint(&raw, l, r, (&a, &b), (&h, &hprops), keep).map_err(f)?);
        }
        for (t, &fi) in self.frames.clone().iter().enumerate() {
            let reg = &p.regs[fi];
            let leaf = bv(&reg.name, reg.width);
            let raw = item_proof(&p.step_m[fi], &leaf, filter)?;
            let sb = self.s_b(&b);
            let lhs = substitute(&eval_of(&p.step_m[fi]).map_err(f)?, &sb);
            let pi = substitute(&raw, &sb);
            let (y_id, y) = self.fr.local();
            let mut sy: Sigma = sb.into_iter().filter(|(n, _, _)| *n != reg.name).collect();
            sy.push((reg.name.clone(), reg.width, y));
            let rhs = substitute(&eval_of(&leaf).map_err(f)?, &sy);
            let motive = lams(vec![(y_id, lb())], kx::eq_list(lhs, rhs));
            pfs.push(kterm::eq_subst(
                lb(),
                motive,
                state_proj(self.m, fi, &b),
                self.psi(fi).map_err(f)?,
                conj_get(&hprops, &h, self.k + t),
                pi,
            ));
        }
        lemmas.push(Lemma::new(
            names::STEP,
            st.step_ty.clone(),
            lams(binders.clone(), conj_intro(&props, pfs)),
        ));

        // obs
        let props = self.obs_props(&a, &b).map_err(f)?;
        let mut pfs = Vec::new();
        let observed = [
            (self.d.cond_ir.clone(), self.d.cond_m.clone()),
            (self.d.out_ir.clone(), self.d.out_m.clone()),
        ];
        for (l, r) in &observed {
            let raw = item_proof(l, r, filter)?;
            pfs.push(self.joint(&raw, l, r, (&a, &b), (&h, &hprops), None).map_err(f)?);
        }
        let frame_map: HashMap<String, Formula> = self
            .frames
            .iter()
            .map(|&fi| (p.regs[fi].name.clone(), p.entry_m[fi].clone()))
            .collect();
        for (t, &fi) in self.frames.clone().iter().enumerate() {
            let exit = &p.exit_frame_m[t];
            let at_entry = subst_formula(exit, &frame_map).map_err(f)?;
            let k_f = self.frame_entry(fi).map_err(f)?;
            let raw = item_proof(&at_entry, &k_f, filter)?;
            let rk = substitute(&eval_of(&k_f).map_err(f)?, &sk);
            let mut se = sk.clone();
            se.extend(self.s_b(&b).into_iter().filter(|(n, _, _)| !self.is_frame_name(n)));
            let mut pi = substitute(&raw, &se);
            let ev = eval_of(exit).map_err(f)?;
            let reads: Vec<usize> = {
                let vs = vars_of(exit).map_err(f)?;
                self.frames
                    .iter()
                    .copied()
                    .filter(|&g| vs.iter().any(|(n, _)| *n == p.regs[g].name))
                    .collect()
            };
            for (pos, &g) in reads.iter().enumerate() {
                let (y_id, y) = self.fr.local();
                let mut s: Sigma =
                    self.s_b(&b).into_iter().filter(|(n, _, _)| !self.is_frame_name(n)).collect();
                for &g2 in &self.frames {
                    let reg = &p.regs[g2];
                    let tgt = if reads[..pos].contains(&g2) {
                        state_proj(self.m, g2, &b)
                    } else if g2 == g {
                        y.clone()
                    } else {
                        self.psi(g2).map_err(f)?
                    };
                    s.push((reg.name.clone(), reg.width, tgt));
                }
                let motive = lams(vec![(y_id, lb())], kx::eq_list(substitute(&ev, &s), rk.clone()));
                let tg = self.frames.iter().position(|&x| x == g).expect("a frame register");
                let hg = conj_get(&hprops, &h, self.k + tg);
                let psi_g = self.psi(g).map_err(f)?;
                let pg = state_proj(self.m, g, &b);
                pi = kterm::eq_subst(
                    lb(),
                    motive,
                    psi_g.clone(),
                    pg.clone(),
                    kterm::symm(lb(), pg, psi_g, hg),
                    pi,
                );
            }
            pfs.push(pi);
        }
        lemmas.push(Lemma::new(
            names::OBS,
            st.obs_ty.clone(),
            lams(binders, conj_intro(&props, pfs)),
        ));
        Ok(lemmas)
    }

    fn is_frame_name(&self, n: &str) -> bool {
        self.frames.iter().any(|&g| self.p.regs[g].name == n)
    }
}

struct Statements {
    fa: Expr,
    fb: Expr,
    rel: Expr,
    obs: Expr,
    a0: Expr,
    b0: Expr,
    entry: Expr,
    entry_ty: Expr,
    cov_ir: Expr,
    cov_m: Expr,
    base_ty: Expr,
    step_ty: Expr,
    obs_ty: Expr,
}

struct GoalParts {
    goal: Expr,
    props: Vec<Expr>,
    kg: Vec<Expr>,
    rel: Expr,
    a0: Expr,
    b0: Expr,
    n_id: FVarId,
    n: Expr,
    ita: Expr,
    itb: Expr,
}

/// A lemma the obligation declares before any leaf exists.
#[derive(Clone, Debug)]
pub(crate) struct Lemma {
    pub(crate) name: &'static str,
    pub(crate) type_: Expr,
    pub(crate) value: Expr,
}

impl Lemma {
    fn new(name: &'static str, type_: Expr, value: Expr) -> Self {
        Self { name, type_, value }
    }
}

/// A goal, its lemmas, its discharge and the leaves the environment declares.
#[derive(Clone, Debug)]
pub(crate) struct LoopObligation {
    pub(crate) goal: Expr,
    pub(crate) lemmas: Vec<Lemma>,
    pub(crate) proof: Expr,
    pub(crate) leaves: Vec<(String, u32)>,
}

/// `G` for `pair`, from the Formulas alone (no route runs).
pub(crate) fn goal_of(pair: &LoopPair) -> Result<Expr, String> {
    on_route_stack(|| {
        let mut model = Model::new(pair)?;
        let st = model.statements()?;
        Ok(model.goal(&st).goal)
    })
}

/// Build `(G, lemmas, π)`; nothing here is checked by the kernel yet.
pub(crate) fn obligation(
    pair: &LoopPair,
    filter: LoopFilter,
    knobs: &Knobs,
) -> Result<LoopObligation, Decline> {
    on_route_stack(|| {
        let mut model = Model::new(pair).map_err(Decline::Filter)?;
        let st = model.statements().map_err(Decline::Filter)?;
        let g = model.goal(&st);
        let lemmas = model.proofs(filter, knobs, &st)?;
        let lem = |name: &str| Expr::apps(Expr::const_str(name), g.kg.clone());
        let sim = Expr::apps(
            Expr::const_str(names::SIM),
            [
                model.a_ty.clone(),
                model.b_ty.clone(),
                g.rel.clone(),
                st.fa.clone(),
                st.fb.clone(),
                g.a0.clone(),
                g.b0.clone(),
                lem(names::BASE),
                lem(names::STEP),
                g.n.clone(),
            ],
        );
        let at_n = Expr::apps(lem(names::OBS), [g.ita.clone(), g.itb.clone(), sim]);
        let loop_pf = lams(vec![(g.n_id, nat())], at_n);
        let proof = conj_intro(
            &g.props,
            vec![
                lem(names::ENTRY),
                Expr::const_str(names::COV_IR),
                Expr::const_str(names::COV_M),
                loop_pf,
            ],
        );
        Ok(LoopObligation { goal: g.goal, lemmas, proof, leaves: model.entry.clone() })
    })
}

/// What an admitted obligation leaves behind (the module is test-only).
#[derive(Clone, Debug)]
pub(crate) struct Admitted {
    pub(crate) label: String,
    /// Exactly the type handed to `strength::admit_obligation`.
    pub(crate) declared: Expr,
    /// `axiom_deps` of the admitted declaration, sorted.
    pub(crate) closure: Vec<String>,
    pub(crate) kernel_ms: u128,
}

/// Where the lemmas are checked: before any leaf (the route), or after the
/// entry leaves are declared (a test, to show a type mismatch rather than an
/// unknown constant).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LemmaEnv {
    LeafFree,
    WithLeaves,
}

/// Declare the lemmas, then the leaves, then admit `goal` in `env`.
pub(crate) fn admit_in(
    env: &mut Environment,
    ob: &LoopObligation,
    where_: LemmaEnv,
) -> Result<Admitted, Decline> {
    let t0 = std::time::Instant::now();
    if where_ == LemmaEnv::WithLeaves {
        add_comm::add_leaf_bits(env, &ob.leaves);
    }
    for lemma in &ob.lemmas {
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(lemma.name),
            level_params: vec![],
            type_: lemma.type_.clone(),
            value: lemma.value.clone(),
        })
        .map_err(|e| Decline::Kernel(format!("kernel: {}: {e:?}", lemma.name)))?;
    }
    if where_ == LemmaEnv::LeafFree {
        add_comm::add_leaf_bits(env, &ob.leaves);
    }
    strength::admit_obligation(env, ob.goal.clone(), ob.proof.clone()).map_err(Decline::Kernel)?;
    let name = Name::from_string(strength::OBLIGATION);
    let mut closure: Vec<String> = env
        .axiom_deps(&name)
        .ok_or_else(|| Decline::Kernel("obligation: no closure".into()))?
        .iter()
        .map(ToString::to_string)
        .collect();
    closure.sort();
    let mut used = std::collections::HashSet::new();
    ob.proof.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    for lemma in &ob.lemmas {
        lemma.value.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    }
    let mut parts: Vec<String> = used
        .into_iter()
        .filter(|n| {
            let s = n.to_string();
            ["Trust.Loop.", "Trust.BV", "Clean.BVC."].iter().any(|p| s.starts_with(p))
                && env.get_const(n).is_some_and(|i| i.kind == ConstantKind::Theorem)
        })
        .map(|n| n.to_string())
        .collect();
    parts.sort();
    Ok(Admitted {
        label: parts.join("+"),
        declared: ob.goal.clone(),
        closure,
        kernel_ms: t0.elapsed().as_millis(),
    })
}

/// Check `ob` on a kernel re-check thread in the environment `base` builds
/// there (a test hands it a doctored one).
pub(crate) fn admit_with<F>(
    ob: LoopObligation,
    base: F,
    where_: LemmaEnv,
) -> Result<Admitted, Decline>
where
    F: FnOnce() -> Result<Environment, String> + Send + 'static,
{
    run_recheck_thread("trust-loop-sim", move || {
        let mut env = base().map_err(Decline::Environment)?;
        admit_in(&mut env, &ob, where_)
    })
    .map_err(|e| Decline::Environment(e.to_string()))
    .and_then(|r| r)
}

/// Check `ob` in a clone of [`loop_base`], lemmas before any leaf.
pub(crate) fn admit(ob: LoopObligation) -> Result<Admitted, Decline> {
    admit_with(ob, || loop_base().cloned(), LemmaEnv::LeafFree)
}

/// Build the obligation, check it in the kernel, and name it.
pub(crate) fn prove(pair: &LoopPair, filter: LoopFilter) -> Result<Admitted, Decline> {
    admit(obligation(pair, filter, &Knobs::default())?)
}

#[cfg(test)]
#[path = "loop_sim/tests.rs"]
mod tests;
