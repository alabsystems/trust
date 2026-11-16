// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! LOOP L1 spike tests: P1-P3 (the theorem, the lockstep proofs, the declared
//! goal against an independent reference) and N1-N11. N1-N6 and N8-N10 run
//! with the Rust filter off and assert WHICH lemma the kernel refuses; N5 is
//! the admission closure; N7 is an unknown constant in the kernel plus a
//! goal-shape refusal in Rust; N11 is goal-shape refusals in Rust only.
//!
//! What the positives are: each machine segment is the IR Formula with the
//! branch condition respelled (`Not(Not(c))`, or AArch64 `b.hi` after
//! `cmp n, i` in the `hi` fixture) and the identical entry values, the frame
//! moved by the SP prologue and restored by the epilogue. The machine
//! registers are named by the IR cut names, so the location map is the
//! identity on names.

use std::collections::BTreeSet;
use std::time::Instant;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, ConstantKind, Declaration, Expr, Level};
use trust_types::{Formula, Sort};

use super::super::add_comm::{audit_theorems, bit_leaf};
use super::super::kterm::{self, Fresh, bhead, btail, nat, prop};
use super::super::{branch_split, kx, run_recheck_thread};
use super::*;

// ── Formulas ─────────────────────────────────────────────────────────────────

fn var(name: &str, w: u32) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(w))
}
fn bx(f: Formula) -> Box<Formula> {
    Box::new(f)
}
fn ite(c: Formula, a: Formula, e: Formula) -> Formula {
    Formula::Ite(bx(c), bx(a), bx(e))
}
fn not(x: Formula) -> Formula {
    Formula::Not(bx(x))
}
fn add(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvAdd(bx(l), bx(r), w)
}
fn sub(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvSub(bx(l), bx(r), w)
}
fn ult(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvULt(bx(l), bx(r), w)
}
fn ule(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvULe(bx(l), bx(r), w)
}
/// AArch64 `b.hi` after `cmp a, b`: `a >u b`.
fn hi(a: Formula, b: Formula, w: u32) -> Formula {
    Formula::And(vec![
        not(ult(a.clone(), b.clone(), w)),
        not(Formula::Eq(bx(sub(a, b, w)), bx(lit(0, w)))),
    ])
}

/// The frame: SP, X18, the callee-saved X19-X28, X29, X30 and the low
/// halves of D8-D15, each 64 bits.
const FRAME: [&str; 22] = [
    "SP", "X18", "X19", "X20", "X21", "X22", "X23", "X24", "X25", "X26", "X27", "X28", "X29",
    "X30", "D8", "D9", "D10", "D11", "D12", "D13", "D14", "D15",
];
/// `-16` at 64 bits: the prologue's `sub sp, sp, #16` as an add of `-16`, the
/// epilogue's `add sp, sp, #16` as a subtract of `-16` (the shape CANCEL-1
/// takes; the real `sub`/`add` spelling needs a sub-add cancellation theorem
/// that does not exist yet, so it is NOT covered).
const SP_DOWN: i128 = (1i128 << 64) - 16;

fn frame_cut(r: &str) -> String {
    format!("CUT_M_{r}")
}
fn frame_entry(r: &str) -> String {
    format!("{r}_0")
}
/// `(SP_0 - 16) + 16`, spelled as CANCEL-1 takes it.
fn sp_restored(sp: Formula) -> Formula {
    sub(sp, lit(SP_DOWN, 64), 64)
}

/// How the machine spells the loop condition `ctr <u bound`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum MCond {
    /// `Not(Not(ctr <u bound))`.
    NotNot,
    /// `b.hi` after `cmp bound, ctr`.
    Hi,
    /// `Not(Not(ctr <=u bound))`: one iteration late (N4, N8a).
    Late,
}

/// One loop: `(cut name, entry value, value on the back edge)` per IR shared
/// variable (block params, then live-ins), the counter and bound of
/// `while ctr < bound`, the returned variable and the scratch register's
/// back-edge value.
struct Shape {
    w: u32,
    vars: Vec<(&'static str, Formula, Formula)>,
    ctr: &'static str,
    bound: &'static str,
    ret: Formula,
    scratch: Formula,
    mcond: MCond,
}

fn c_ir_of(s: &Shape) -> Formula {
    ult(var(s.ctr, s.w), var(s.bound, s.w), s.w)
}
fn c_m_of(s: &Shape) -> Formula {
    let (c, b, w) = (var(s.ctr, s.w), var(s.bound, s.w), s.w);
    match s.mcond {
        MCond::NotNot => not(not(ult(c, b, w))),
        MCond::Hi => hi(b, c, w),
        MCond::Late => not(not(ule(c, b, w))),
    }
}

fn build(s: Shape) -> LoopPair {
    let w = s.w;
    let c_ir = c_ir_of(&s);
    let c_m = c_m_of(&s);
    let mut regs = Vec::new();
    let mut entry_m = Vec::new();
    let mut step_m = Vec::new();
    for (j, (cut, entry, back)) in s.vars.iter().enumerate() {
        regs.push(Reg { name: (*cut).into(), width: w, role: Role::Coupled(j) });
        entry_m.push(entry.clone());
        step_m.push(ite(c_m.clone(), back.clone(), var(cut, w)));
    }
    regs.push(Reg { name: "X11_HAVOC".into(), width: w, role: Role::Havoc });
    entry_m.push(var("X11_0", w));
    step_m.push(ite(c_m.clone(), s.scratch.clone(), var("X11_HAVOC", w)));
    regs.push(Reg { name: "X12_HAVOC".into(), width: 64, role: Role::Havoc });
    entry_m.push(var("X12_0", 64));
    step_m.push(var("X12_HAVOC", 64));
    let mut exit_frame_m = Vec::new();
    let mut direct = Vec::new();
    for r in FRAME {
        regs.push(Reg {
            name: frame_cut(r),
            width: 64,
            role: Role::Frame { arch: r.into(), entry: frame_entry(r) },
        });
        step_m.push(var(&frame_cut(r), 64));
        if r == "SP" {
            let down = add(lit(SP_DOWN, 64), var(&frame_entry(r), 64), 64);
            entry_m.push(down.clone());
            exit_frame_m.push(sp_restored(var(&frame_cut(r), 64)));
            direct.push(sp_restored(down));
        } else {
            entry_m.push(var(&frame_entry(r), 64));
            exit_frame_m.push(var(&frame_cut(r), 64));
            direct.push(var(&frame_entry(r), 64));
        }
    }
    LoopPair {
        ir_vars: s.vars.iter().map(|(c, _, _)| ((*c).to_string(), w)).collect(),
        entry_ir: s.vars.iter().map(|(_, e, _)| e.clone()).collect(),
        step_ir: s.vars.iter().map(|(c, _, b)| ite(c_ir.clone(), b.clone(), var(c, w))).collect(),
        reach_ret_ir: not(c_ir),
        ret_ir: s.ret.clone(),
        regs,
        entry_m,
        step_m,
        reach_ret_m: not(c_m),
        ret_m: s.ret.clone(),
        exit_frame_m,
        entry: EntryPath {
            reach_ir: Formula::Bool(true),
            reach_m: Formula::Bool(true),
            ret_ir: lit(0, w),
            ret_m: lit(0, w),
            frame_m: direct,
        },
    }
}

const I: &str = "CUT_bb1_v1";
const N: &str = "CUT_bb1_v0";
const S: &str = "CUT_bb1_v2";

/// `fn count_to(n) { let mut i = 0; while i < n { i += 1 } i }` at O0:
/// i in X9, n in X0, X11 scratch.
fn count_to_shape(w: u32) -> Shape {
    Shape {
        w,
        vars: vec![(I, lit(0, w), add(var(I, w), lit(1, w), w)), (N, var("n", w), var(N, w))],
        ctr: I,
        bound: N,
        ret: var(I, w),
        scratch: add(var(I, w), lit(1, w), w),
        mcond: MCond::NotNot,
    }
}
fn count_to(w: u32) -> LoopPair {
    build(count_to_shape(w))
}

/// `fn sum_to(x) { let (mut s, mut i) = (0, 0); while i < x { s += i; i += 1 } s }`
/// (the s06 shape): i in X9, s in X10, x in X0.
fn sum_to(w: u32) -> LoopPair {
    build(Shape {
        w,
        vars: vec![
            (I, lit(0, w), add(var(I, w), lit(1, w), w)),
            (S, lit(0, w), add(var(S, w), var(I, w), w)),
            (N, var("x", w), var(N, w)),
        ],
        ctr: I,
        bound: N,
        ret: var(S, w),
        scratch: add(var(S, w), var(I, w), w),
        mcond: MCond::NotNot,
    })
}

/// `count_to` whose entry segment returns 0 directly when `n == 0`
/// (`cbz x0, ret`).
fn count_to_guarded(w: u32) -> LoopPair {
    let mut p = count_to(w);
    let guard = not(Formula::Eq(bx(var("n", w)), bx(lit(0, w))));
    p.entry.reach_ir = guard.clone();
    p.entry.reach_m = guard;
    p
}

fn reg_index(p: &LoopPair, name: &str) -> usize {
    p.regs.iter().position(|r| r.name == name).expect("a register")
}
fn frame_pos(r: &str) -> usize {
    FRAME.iter().position(|x| *x == r).expect("a frame register")
}

fn declined(r: &Result<Admitted, Decline>) -> bool {
    matches!(r, Err(Decline::Filter(_)))
}
/// The whole outcome, for assertions.
fn full(r: &Result<Admitted, Decline>) -> String {
    match r {
        Ok(a) => format!("ADMITTED {}", a.label),
        Err(d) => format!("{d:?}"),
    }
}
/// The outcome cut to a printable length.
fn msg(r: &Result<Admitted, Decline>) -> String {
    full(r).chars().take(400).collect()
}
/// The kernel's `add_decl` refused lemma `lemma` with a `TypeCheckFailed`
/// whose source contains `kind`.
fn refused_at(r: &Result<Admitted, Decline>, lemma: &str, kind: &str) -> bool {
    match r {
        Err(Decline::Kernel(m)) => {
            m.starts_with(&format!("kernel: {lemma}: TypeCheckFailed")) && m.contains(kind)
        }
        _ => false,
    }
}

/// The bit constants of the entry leaves of `p` (what may be declared).
fn entry_bits(p: &LoopPair) -> BTreeSet<String> {
    entry_leaves(p).iter().flat_map(|(n, w)| bit_consts(n, *w)).map(|n| n.to_string()).collect()
}
fn entry_leaves(p: &LoopPair) -> Vec<(String, u32)> {
    let mut leaves: Vec<(String, u32)> = Vec::new();
    let e = &p.entry;
    let all = p.entry_ir.iter().chain(&p.entry_m).chain(&e.frame_m);
    for f in all.chain([&e.reach_ir, &e.reach_m, &e.ret_ir, &e.ret_m]) {
        super::vars(f, &mut leaves).expect("fragment");
    }
    for r in &p.regs {
        if let Role::Frame { entry, .. } = &r.role
            && !leaves.iter().any(|(n, _)| n == entry)
        {
            leaves.push((entry.clone(), r.width));
        }
    }
    leaves
}

// ── P0: the substitution is syntax ───────────────────────────────────────────

/// A leaf's spine becomes `fit_w y` exactly, other constants stay.
#[test]
fn substitution_turns_a_leaf_spine_into_fit() {
    let y = Expr::const_str("Y");
    let spine = bit_leaf("CUT_x", 3);
    let got = substitute(&spine, &[("CUT_x".into(), 3, y.clone())]);
    let mut want = kx::nil();
    for k in (0..3).rev() {
        let mut t = y.clone();
        for _ in 0..k {
            t = btail(t);
        }
        want = kx::cons(bhead(t), want);
    }
    assert_eq!(got, want);
    let other = bit_leaf("n", 3);
    assert_eq!(substitute(&other, &[("CUT_x".into(), 3, y)]), other);
}

// ── P1 ───────────────────────────────────────────────────────────────────────

/// The statement written with raw de Bruijn indices, independently of the
/// builders: binders A B R fA fB a0 b0 hb hs n.
fn reference_statement() -> Expr {
    let b = Expr::bvar;
    let pi = |t: Expr, body: Expr| Expr::pi(BinderInfo::Default, t, body);
    let lam = |t: Expr, body: Expr| Expr::lam(BinderInfo::Default, t, body);
    let ty = Expr::sort(Level::succ(Level::zero()));
    let rec1 = || Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let ita = Expr::apps(
        rec1(),
        [lam(nat(), b(10)), b(4), lam(nat(), lam(b(10), Expr::app(b(8), b(0)))), b(0)],
    );
    let itb = Expr::apps(
        rec1(),
        [lam(nat(), b(9)), b(3), lam(nat(), lam(b(9), Expr::app(b(7), b(0)))), b(0)],
    );
    let concl = pi(nat(), Expr::apps(b(7), [ita, itb]));
    let hs = pi(
        b(7),
        pi(
            b(7),
            pi(
                Expr::apps(b(7), [b(1), b(0)]),
                Expr::apps(b(8), [Expr::app(b(7), b(2)), Expr::app(b(6), b(1))]),
            ),
        ),
    );
    let hb = Expr::apps(b(4), [b(1), b(0)]);
    let r_ty = pi(b(1), pi(b(1), prop()));
    pi(
        ty.clone(),
        pi(
            ty,
            pi(
                r_ty,
                pi(pi(b(2), b(3)), pi(pi(b(2), b(3)), pi(b(4), pi(b(4), pi(hb, pi(hs, concl)))))),
            ),
        ),
    )
}

fn fnv1a(s: &str) -> u64 {
    s.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
}

#[test]
fn sim_is_a_proved_axiom_free_theorem() {
    let t = Instant::now();
    let stmt = sim_statement();
    assert_eq!(stmt, reference_statement(), "the statement is not the pinned one");
    eprintln!("[loop-sim] SIM statement fnv1a {:016x}", fnv1a(&format!("{stmt:?}")));
    run_recheck_thread("loop-sim-p1", || {
        let env = loop_base().expect("the loop base builds");
        let info = env.get_const(&Name::from_string(names::SIM)).expect("SIM is declared");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some());
        assert_eq!(info.type_, sim_statement());
        audit_theorems(env, &[names::SIM]).expect("SIM audit");
        // A proof that skips the induction (`hb` for every `n`) is refused.
        let mut env = env.clone();
        let bad = {
            let b = Expr::bvar;
            let lam = |t: Expr, body: Expr| Expr::lam(BinderInfo::Default, t, body);
            let Some(Domains(tys)) = pi_domains(&sim_statement()) else {
                panic!("SIM is a Pi telescope")
            };
            let mut body = b(2); // hb, under hb hs n
            for t in tys.into_iter().rev() {
                body = lam(t, body);
            }
            body
        };
        let r = env.add_decl(Declaration::Theorem {
            name: Name::from_string("Trust.Loop.sim_wrong"),
            level_params: vec![],
            type_: sim_statement(),
            value: bad,
        });
        let e = format!("{:?}", r.expect_err("a proof without induction was accepted"));
        assert!(e.contains("TypeMismatch"), "not refused as a type mismatch: {e}");
    })
    .expect("kernel thread");
    eprintln!("[loop-sim] P1 sim_is_a_proved_axiom_free_theorem: {:?}", t.elapsed());
}

struct Domains(Vec<Expr>);

/// The ten binder domains of the SIM statement (A … hs, n).
fn pi_domains(e: &Expr) -> Option<Domains> {
    let mut out = Vec::new();
    let mut cur = e.clone();
    while let clean_kernel::ExprKind::Pi(_, ty, body) = cur.kind() {
        out.push((**ty).clone());
        let next = (**body).clone();
        cur = next;
        if out.len() == 10 {
            break;
        }
    }
    (out.len() == 10).then_some(Domains(out))
}

// ── P2 ───────────────────────────────────────────────────────────────────────

fn assert_proved(name: &str, pair: &LoopPair) {
    let t = Instant::now();
    let r = prove(pair, LoopFilter::On);
    let a = match r {
        Ok(a) => a,
        Err(d) => panic!("{name}: {d:?}"),
    };
    eprintln!(
        "[loop-sim] P2 {name}: proved in {:?} (lemmas+admission+closure {} ms), label {}",
        t.elapsed(),
        a.kernel_ms,
        a.label
    );
    for lemma in [names::SIM, names::BASE, names::STEP, names::OBS, names::ENTRY] {
        assert!(a.label.split('+').any(|p| p == lemma), "{name}: label {} lacks {lemma}", a.label);
    }
    for c in &a.closure {
        assert!(c.starts_with("BVC_LEAFBIT_"), "{name}: closure holds {c}");
        assert!(!c.contains("CUT_") && !c.contains("_HAVOC"), "{name}: closure holds {c}");
    }
    let closure: BTreeSet<String> = a.closure.iter().cloned().collect();
    assert_eq!(closure, entry_bits(pair), "{name}: the closure is not exactly the entry-leaf bits");
}

#[test]
fn count_to_8_lockstep_is_kernel_proved() {
    assert_proved("count_to@8", &count_to(8));
}

#[test]
fn count_to_32_lockstep_is_kernel_proved() {
    assert_proved("count_to@32", &count_to(32));
}

#[test]
fn count_to_64_lockstep_is_kernel_proved() {
    assert_proved("count_to@64", &count_to(64));
}

#[test]
fn sum_to_64_lockstep_is_kernel_proved() {
    assert_proved("sum_to@64", &sum_to(64));
}

/// The machine branches with `b.hi` after `cmp n, i` (`And[Not(n < i),
/// Not(n - i == 0)]`), a different spelling of `i < n`: proved, so the
/// refusals below are not mere syntactic difference.
#[test]
fn count_to_hi_lockstep_is_kernel_proved() {
    assert_proved("count_to/b.hi@8", &build(Shape { mcond: MCond::Hi, ..count_to_shape(8) }));
}

/// The negatives below hand the kernel filter-off terms; for the correct
/// pairs those terms are admitted, so a refusal is not vacuous.
#[test]
fn filter_off_admits_the_correct_pairs() {
    for (name, pair) in [("count_to@8", count_to(8)), ("sum_to@64", sum_to(64))] {
        let r = prove(&pair, LoopFilter::Off);
        assert!(r.is_ok(), "{name} with the filter off: {}", msg(&r));
    }
}

// ── P3: the declared type against an independent reference ─────────────────

fn r_ev(f: &Formula) -> Expr {
    let (_, sides, _) = branch_split::goal_of(&[(f.clone(), f.clone())]).expect("reflects");
    sides[0].0.clone()
}
fn r_stmt(l: &Formula, r: &Formula) -> Expr {
    branch_split::goal_of(&[(l.clone(), r.clone())]).expect("reflects").0
}
fn r_and(mut ps: Vec<Expr>) -> Expr {
    let mut acc = ps.pop().expect("a conjunct");
    while let Some(p) = ps.pop() {
        acc = Expr::apps(Expr::const_str("And"), [p, acc]);
    }
    acc
}
fn r_prod(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::zero(), Level::zero()])
}
fn r_ty(n: usize) -> Expr {
    (1..n).fold(kterm::lb(), |t, _| Expr::apps(r_prod("Prod"), [kterm::lb(), t]))
}
fn r_mk(vals: Vec<Expr>) -> Expr {
    let n = vals.len();
    let mut acc = vals[n - 1].clone();
    for (i, v) in vals[..n - 1].iter().enumerate().rev() {
        acc = Expr::apps(r_prod("Prod.mk"), [kterm::lb(), r_ty(n - 1 - i), v.clone(), acc]);
    }
    acc
}
fn r_proj(n: usize, j: usize, x: &Expr) -> Expr {
    let mut cur = x.clone();
    if n == 1 {
        return cur;
    }
    for _ in 0..j {
        cur = Expr::proj(Name::from_string("Prod"), 1, cur);
    }
    if j + 1 < n {
        cur = Expr::proj(Name::from_string("Prod"), 0, cur);
    }
    cur
}
fn r_iter(fr: &mut Fresh, ty: &Expr, z: Expr, f: &Expr, n: &Expr) -> Expr {
    let (w_id, _) = fr.local();
    let (m_id, _) = fr.local();
    let (x_id, x) = fr.local();
    let rec1 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    Expr::apps(
        rec1,
        [
            kterm::lams(vec![(w_id, nat())], ty.clone()),
            z,
            kterm::lams(vec![(m_id, nat()), (x_id, ty.clone())], Expr::app(f.clone(), x)),
            n.clone(),
        ],
    )
}
/// The condition of the first `Ite` among `steps`.
fn r_cond(steps: &[Formula]) -> Formula {
    steps
        .iter()
        .find_map(|f| match f {
            Formula::Ite(c, _, _) => Some((**c).clone()),
            _ => None,
        })
        .expect("a branching step")
}
fn r_width(f: &Formula) -> u32 {
    match f {
        Formula::Var(_, Sort::BitVec(w)) | Formula::BitVec { width: w, .. } => *w,
        Formula::BvAdd(_, _, w) | Formula::BvSub(_, _, w) => *w,
        Formula::Ite(_, a, _) => r_width(a),
        other => panic!("no width: {other:?}"),
    }
}
fn r_bit(c: &Formula) -> Formula {
    ite(c.clone(), lit(1, 1), lit(0, 1))
}
fn r_masked(c: &Formula, ret: &Formula) -> Formula {
    ite(c.clone(), lit(0, r_width(ret)), ret.clone())
}

/// `G` written out from the design, not through `Model`: the four conjuncts,
/// the derived coverage and observation items, the `Nat.rec` iterates.
fn reference_goal(p: &LoopPair) -> Expr {
    let (k, m) = (p.ir_vars.len(), p.regs.len());
    let (ta, tb) = (r_ty(k), r_ty(m));
    let sk: Vec<(String, u32, Expr)> =
        entry_leaves(p).into_iter().map(|(n, w)| (n.clone(), w, bit_leaf(&n, w))).collect();
    let sa = |a: &Expr| -> Vec<(String, u32, Expr)> {
        p.ir_vars.iter().enumerate().map(|(j, (n, w))| (n.clone(), *w, r_proj(k, j, a))).collect()
    };
    let sb = |b: &Expr| -> Vec<(String, u32, Expr)> {
        p.regs.iter().enumerate().map(|(i, r)| (r.name.clone(), r.width, r_proj(m, i, b))).collect()
    };
    let at = |f: &Formula, s: &[(String, u32, Expr)]| substitute(&r_ev(f), s);
    let (c_ir, c_m) = (r_cond(&p.step_ir), r_cond(&p.step_m));
    let frames: Vec<(usize, String)> = p
        .regs
        .iter()
        .enumerate()
        .filter_map(|(i, r)| match &r.role {
            Role::Frame { entry, .. } => Some((i, entry.clone())),
            _ => None,
        })
        .collect();
    let mut fr = Fresh::new();

    let (a_id, a) = fr.local();
    let fa = kterm::lams(
        vec![(a_id, ta.clone())],
        r_mk(p.step_ir.iter().map(|f| at(f, &sa(&a))).collect()),
    );
    let (b_id, b) = fr.local();
    let fb = kterm::lams(
        vec![(b_id, tb.clone())],
        r_mk(p.step_m.iter().map(|f| at(f, &sb(&b))).collect()),
    );
    let a0 = r_mk(p.entry_ir.iter().map(|f| at(f, &sk)).collect());
    let b0 = r_mk(p.entry_m.iter().map(|f| at(f, &sk)).collect());

    let (oa_id, oa) = fr.local();
    let (ob_id, ob) = fr.local();
    let mut obs = vec![
        kx::eq_list(at(&r_bit(&c_ir), &sa(&oa)), at(&r_bit(&c_m), &sb(&ob))),
        kx::eq_list(
            at(&r_masked(&c_ir, &p.ret_ir), &sa(&oa)),
            at(&r_masked(&c_m, &p.ret_m), &sb(&ob)),
        ),
    ];
    for (t, (i, entry)) in frames.iter().enumerate() {
        let k_f = var(entry, p.regs[*i].width);
        obs.push(kx::eq_list(at(&p.exit_frame_m[t], &sb(&ob)), at(&k_f, &sk)));
    }
    let obs = kterm::lams(vec![(oa_id, ta.clone()), (ob_id, tb.clone())], r_and(obs));

    let (n_id, n) = fr.local();
    let ita = r_iter(&mut fr, &ta, a0, &fa, &n);
    let itb = r_iter(&mut fr, &tb, b0, &fb, &n);
    let loop_ = kterm::pis(vec![(n_id, nat())], Expr::apps(obs, [ita, itb]));

    let cover = |c: &Formula, rr: &Formula, s: &[(String, u32, Expr)]| {
        r_and(vec![
            substitute(&r_stmt(&r_bit(&Formula::Or(vec![c.clone(), rr.clone()])), &lit(1, 1)), s),
            substitute(&r_stmt(&r_bit(&Formula::And(vec![c.clone(), rr.clone()])), &lit(0, 1)), s),
        ])
    };
    let (x_id, x) = fr.local();
    let cov_ir = kterm::pis(vec![(x_id, ta)], cover(&c_ir, &p.reach_ret_ir, &sa(&x)));
    let (y_id, y) = fr.local();
    let cov_m = kterm::pis(vec![(y_id, tb)], cover(&c_m, &p.reach_ret_m, &sb(&y)));

    let e = &p.entry;
    let mut entry = vec![
        substitute(&r_stmt(&r_bit(&e.reach_ir), &r_bit(&e.reach_m)), &sk),
        substitute(
            &r_stmt(&r_masked(&e.reach_ir, &e.ret_ir), &r_masked(&e.reach_m, &e.ret_m)),
            &sk,
        ),
    ];
    for (t, (i, entry_leaf)) in frames.iter().enumerate() {
        let k_f = var(entry_leaf, p.regs[*i].width);
        entry.push(substitute(&r_stmt(&e.frame_m[t], &k_f), &sk));
    }
    r_and(vec![r_and(entry), cov_ir, cov_m, loop_])
}

/// The declared type is the reference `G`; so is `goal_of` on every
/// mutant of every `LoopPair` field, and each mutant changes it.
#[test]
fn declared_type_is_the_independent_goal() {
    let t = Instant::now();
    let pair = count_to(8);
    let a = prove(&pair, LoopFilter::On).unwrap_or_else(|d| panic!("{d:?}"));
    let g = goal_of(&pair).expect("goal");
    assert_eq!(a.declared, g);
    assert_eq!(g, reference_goal(&pair), "goal_of is not the reference G");
    for (name, p) in [
        ("sum_to@64", sum_to(64)),
        ("count_to/b.hi@8", build(Shape { mcond: MCond::Hi, ..count_to_shape(8) })),
        ("count_to/guarded@8", count_to_guarded(8)),
    ] {
        assert_eq!(goal_of(&p).expect("goal"), reference_goal(&p), "{name}");
    }
    let w = 8;
    let c_m = c_m_of(&count_to_shape(w));
    let x19 = reg_index(&pair, &frame_cut("X19"));
    type Mutate = fn(&mut LoopPair, &Formula, usize);
    let mutants: [(&str, Mutate); 17] = [
        ("entry_ir", |p, _, _| p.entry_ir[0] = lit(2, 8)),
        ("step_ir value", |p, _, _| {
            p.step_ir[0] = ite(ult(var(I, 8), var(N, 8), 8), lit(2, 8), var(I, 8));
        }),
        ("reach_ret_ir", |p, _, _| p.reach_ret_ir = ult(var(N, 8), var(I, 8), 8)),
        ("ret_ir", |p, _, _| p.ret_ir = var(N, 8)),
        ("entry_m", |p, _, _| p.entry_m[0] = lit(2, 8)),
        ("step_m value", |p, c, _| p.step_m[0] = ite(c.clone(), lit(2, 8), var(I, 8))),
        ("step_m frame", |p, c, x19| {
            p.step_m[x19] = ite(c.clone(), var("X12_HAVOC", 64), var(&frame_cut("X19"), 64));
        }),
        ("reach_ret_m", |p, _, _| p.reach_ret_m = ult(var(N, 8), var(I, 8), 8)),
        ("ret_m", |p, _, _| p.ret_m = var(N, 8)),
        ("exit_frame_m", |p, _, _| p.exit_frame_m[1] = var(&frame_cut("X19"), 64)),
        ("entry.reach_ir", |p, _, _| p.entry.reach_ir = Formula::Bool(false)),
        ("entry.reach_m", |p, _, _| p.entry.reach_m = Formula::Bool(false)),
        ("entry.ret_ir", |p, _, _| p.entry.ret_ir = lit(1, 8)),
        ("entry.ret_m", |p, _, _| p.entry.ret_m = lit(1, 8)),
        ("entry.frame_m", |p, _, _| p.entry.frame_m[1] = var("X19_0", 64)),
        ("frame entry leaf", |p, _, x19| {
            p.regs[x19].role = Role::Frame { arch: "X19".into(), entry: "X19_1".into() };
        }),
        ("step conditions", |p, _, _| *p = build(Shape { mcond: MCond::Hi, ..count_to_shape(8) })),
    ];
    for (name, mutate) in mutants {
        let mut p = pair.clone();
        mutate(&mut p, &c_m, x19);
        assert_ne!(p, pair, "{name}: the mutation did not apply");
        let gm = goal_of(&p).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_ne!(gm, g, "{name}: the goal does not depend on it");
        assert_eq!(gm, reference_goal(&p), "{name}: goal_of is not the reference G");
    }
    eprintln!("[loop-sim] P3 declared_type_is_the_independent_goal: {:?}", t.elapsed());
}

// ── negatives ────────────────────────────────────────────────────────────────

fn c_m8() -> Formula {
    c_m_of(&count_to_shape(8))
}

/// The route declines with the filter on; with it off, the kernel refuses
/// lemma `lemma` with a type mismatch.
fn assert_kernel_refuses(name: &str, bad: &LoopPair, lemma: &str) {
    let t = Instant::now();
    let on = prove(bad, LoopFilter::On);
    assert!(declined(&on), "{name}: the route did not decline: {}", msg(&on));
    let off = prove(bad, LoopFilter::Off);
    assert!(refused_at(&off, lemma, "TypeMismatch"), "{name}: filter off: {}", msg(&off));
    eprintln!("[loop-sim] {name}: off -> refused at {lemma}  ({:?})", t.elapsed());
}

/// The correct pair's STEP and OBS proofs, under `bad`'s own (filter-off)
/// entry, coverage and base lemmas: the kernel refuses `bad`'s step.
fn assert_step_splice_refused(name: &str, bad: &LoopPair) {
    let good = obligation(&count_to(8), LoopFilter::On, &Knobs::default()).expect("good");
    let mut ob = obligation(bad, LoopFilter::Off, &Knobs::default()).expect("bad");
    for l in &mut ob.lemmas {
        if l.name == names::STEP || l.name == names::OBS {
            l.value = good.lemmas.iter().find(|g| g.name == l.name).expect("lemma").value.clone();
        }
    }
    let r = admit(ob);
    assert!(refused_at(&r, names::STEP, "TypeMismatch"), "{name}: splice: {}", msg(&r));
    eprintln!("[loop-sim] {name}: correct Step/Obs spliced -> refused at {}", names::STEP);
}

/// N1: the machine latch keeps `i` (`X9' = Ite(c, X9, X9)`).
#[test]
fn n1_stale_latch_is_refused_by_the_kernel() {
    let mut bad = count_to(8);
    bad.step_m[0] = ite(c_m8(), var(I, 8), var(I, 8));
    assert_kernel_refuses("N1 stale latch", &bad, names::STEP);
    assert_step_splice_refused("N1 stale latch", &bad);
}

/// N2: `X9' = Ite(c, 1, X9)` equals `i + 1` only at `i = 0`, the entry
/// state; the step lemma quantifies every related state.
#[test]
fn n2_entry_only_latch_is_refused_by_the_kernel() {
    let mut bad = count_to(8);
    bad.step_m[0] = ite(c_m8(), lit(1, 8), var(I, 8));
    assert_kernel_refuses("N2 entry-only latch", &bad, names::STEP);
}

/// N3: a callee-saved register clobbered in the body, and SP not restored on
/// the exit path.
#[test]
fn n3_clobbered_frame_is_refused_by_the_kernel() {
    let mut bad = count_to(8);
    let x19 = reg_index(&bad, &frame_cut("X19"));
    bad.step_m[x19] = ite(c_m8(), var("X12_HAVOC", 64), var(&frame_cut("X19"), 64));
    assert_kernel_refuses("N3 clobbered X19", &bad, names::STEP);
    let mut bad = count_to(8);
    bad.exit_frame_m[frame_pos("SP")] = var(&frame_cut("SP"), 64);
    assert_kernel_refuses("N3 SP not restored", &bad, names::OBS);
}

/// N4: the machine exits one iteration late (`<=`).
#[test]
fn n4_off_by_one_exit_is_refused_by_the_kernel() {
    let bad = build(Shape { mcond: MCond::Late, ..count_to_shape(8) });
    assert_kernel_refuses("N4 late exit", &bad, names::STEP);
    assert_step_splice_refused("N4 late exit", &bad);
}

fn step_ty(ob: &LoopObligation) -> Expr {
    ob.lemmas.iter().find(|l| l.name == names::STEP).expect("step").type_.clone()
}
fn set_step(ob: &mut LoopObligation, value: Expr) {
    ob.lemmas.iter_mut().find(|l| l.name == names::STEP).expect("step").value = value;
}
fn closure_refusal(axioms: &str) -> Decline {
    Decline::Kernel(format!("obligation reaches axioms [\"{axioms}\"]"))
}

/// N5: a theorem that reaches an axiom: `sorry` as the step, SIM declared as
/// an axiom, and a `BVC_LEAFBIT_*`-named axiom whose type is the step.
#[test]
fn n5_axioms_are_refused_by_admission() {
    let t = Instant::now();
    let good = obligation(&count_to(8), LoopFilter::Off, &Knobs::default()).expect("good");
    // (a) sorry. The loop base declares no `sorry`, so a step that names it
    // is refused by the kernel before the closure audit ...
    let mut ob = good.clone();
    let sorry = Expr::const_(Name::from_string("sorry"), vec![Level::zero()]);
    set_step(&mut ob, Expr::app(sorry, step_ty(&good)));
    let r = admit(ob);
    assert!(
        matches!(&r, Err(Decline::Kernel(m)) if m.contains("UnknownConst") && m.contains("sorry")),
        "N5a undeclared: {}",
        msg(&r)
    );
    // ... and where `sorry` IS declared (an axiom of the step's type), the
    // admission closure refuses the theorem that reaches it.
    let mut ob = good.clone();
    let ty = step_ty(&good);
    set_step(&mut ob, Expr::const_str("sorry"));
    let r = admit_with(
        ob,
        move || {
            let mut env = loop_base()?.clone();
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("sorry"),
                level_params: vec![],
                type_: ty,
            })
            .map_err(|e| format!("{e:?}"))?;
            Ok(env)
        },
        LemmaEnv::LeafFree,
    );
    assert_eq!(r.as_ref().err(), Some(&closure_refusal("sorry")), "N5a declared: {}", msg(&r));
    // (b) SIM as an axiom: the audit refuses it, and so does admission.
    let audit = run_recheck_thread("loop-sim-n5b", || {
        let env = build_loop_base(SimDecl::Axiom, false)?;
        audit_theorems(&env, &[names::SIM])
    })
    .expect("kernel thread");
    assert!(audit.is_err(), "N5b: the audit took SIM as an axiom");
    let r = admit_with(good.clone(), || build_loop_base(SimDecl::Axiom, false), LemmaEnv::LeafFree);
    assert_eq!(r.as_ref().err(), Some(&closure_refusal(names::SIM)), "N5b: {}", msg(&r));
    // (c) a leaf-named axiom of the step's type
    let mut ob = good.clone();
    let ty = step_ty(&good);
    set_step(&mut ob, Expr::const_str("BVC_LEAFBIT_forge"));
    let r = admit_with(
        ob,
        move || {
            let mut env = loop_base()?.clone();
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("BVC_LEAFBIT_forge"),
                level_params: vec![],
                type_: ty,
            })
            .map_err(|e| format!("{e:?}"))?;
            Ok(env)
        },
        LemmaEnv::LeafFree,
    );
    assert_eq!(r.as_ref().err(), Some(&closure_refusal("BVC_LEAFBIT_forge")), "N5c: {}", msg(&r));
    eprintln!("[loop-sim] N5 a/b/c refused by the admission closure ({:?})", t.elapsed());
}

/// N6: the IR's exit condition misses `i == n` (`reach_ret := n <u i`), so
/// the header segment neither goes back nor returns there.
#[test]
fn n6_incomplete_coverage_is_refused_by_the_kernel() {
    let mut bad = count_to(8);
    bad.reach_ret_ir = ult(var(N, 8), var(I, 8), 8);
    assert_kernel_refuses("N6 coverage", &bad, names::COV_IR);
}

/// N7: a step proof that keeps a cut leaf constant is refused by the kernel
/// (the constant is undeclared where the lemma is checked). Then, a Rust
/// goal-shape refusal, not kernel evidence: an entry formula that mentions a
/// cut or havoc name is refused as a goal whatever the filter.
#[test]
fn n7_unsubstituted_cut_leaf_is_refused() {
    let t = Instant::now();
    let knobs = Knobs { keep_cut: Some(N.into()) };
    let ob = obligation(&count_to(8), LoopFilter::Off, &knobs).expect("forged");
    let r = admit(ob);
    assert!(
        refused_at(&r, names::STEP, "UnknownConst")
            && full(&r).contains("BVC_LEAFBIT_CUT_bb1_v0_8_0"),
        "N7a: {}",
        msg(&r)
    );
    for (what, leaf) in [("cut", var(N, 8)), ("havoc", var("X11_HAVOC", 8))] {
        let mut bad = count_to(8);
        bad.entry_ir[1] = leaf;
        for filter in [LoopFilter::On, LoopFilter::Off] {
            let r = prove(&bad, filter);
            assert!(declined(&r), "N7b {what} leaf declared ({filter:?}): {}", msg(&r));
        }
    }
    eprintln!("[loop-sim] N7: {:?}", t.elapsed());
}

/// N8a: the step agrees (no variable changes on the back edge) but the exit
/// decision differs at `i == n`; the return value is 0 either way, so only
/// the exit-bit conjunct of Obs is false.
#[test]
fn n8a_exit_bit_mismatch_is_refused_by_the_kernel() {
    let bad = build(Shape {
        vars: vec![(I, lit(0, 8), var(I, 8)), (N, var("n", 8), var(N, 8))],
        ret: lit(0, 8),
        scratch: var(I, 8),
        mcond: MCond::Late,
        ..count_to_shape(8)
    });
    assert_kernel_refuses("N8a exit bit", &bad, names::OBS);
}

/// N8b: the machine returns `i + 1`; the step and exit bit agree, only the
/// masked-return conjunct of Obs is false.
#[test]
fn n8b_wrong_return_value_is_refused_by_the_kernel() {
    let mut bad = count_to(8);
    bad.ret_m = add(var(I, 8), lit(1, 8), 8);
    assert_kernel_refuses("N8b return value", &bad, names::OBS);
}

/// N9: the machine enters the loop in the wrong state: `i` starts at 1, or
/// `n` is read from the wrong argument register.
#[test]
fn n9_wrong_entry_state_is_refused_by_the_kernel() {
    let mut bad = count_to(8);
    bad.entry_m[0] = lit(1, 8);
    assert_kernel_refuses("N9 i starts at 1", &bad, names::BASE);
    let mut bad = count_to(8);
    bad.entry_m[1] = var("x", 8);
    assert_kernel_refuses("N9 n from the wrong register", &bad, names::BASE);
}

/// N10: the entry segment returns directly when `n == 0`; that path must
/// restore the frame. The guarded pair proves; with X19 clobbered, or SP not
/// restored, on the direct-return path, the kernel refuses the entry lemma.
#[test]
fn n10_direct_return_frame_is_refused_by_the_kernel() {
    assert_proved("count_to/guarded@8", &count_to_guarded(8));
    let mut bad = count_to_guarded(8);
    bad.entry.frame_m[frame_pos("X19")] = var("X12_0", 64);
    assert_kernel_refuses("N10 X19 clobbered on the direct return", &bad, names::ENTRY);
    let mut bad = count_to_guarded(8);
    bad.entry.frame_m[frame_pos("SP")] = add(lit(SP_DOWN, 64), var(&frame_entry("SP"), 64), 64);
    assert_kernel_refuses("N10 SP not restored on the direct return", &bad, names::ENTRY);
}

/// N11 (Rust goal-shape refusals, whatever the filter): a pair without a
/// callee-saved frame register, an IR step whose exit arm is not its own
/// cut, and machine steps that branch on different conditions.
#[test]
fn n11_goal_shape_is_refused_whatever_the_filter() {
    let mut no_x19 = count_to(8);
    let x19 = reg_index(&no_x19, &frame_cut("X19"));
    no_x19.regs.remove(x19);
    no_x19.entry_m.remove(x19);
    no_x19.step_m.remove(x19);
    no_x19.exit_frame_m.remove(frame_pos("X19"));
    no_x19.entry.frame_m.remove(frame_pos("X19"));
    let mut wrong_arm = count_to(8);
    wrong_arm.step_ir[0] =
        ite(ult(var(I, 8), var(N, 8), 8), add(var(I, 8), lit(1, 8), 8), var(N, 8));
    let mut two_conds = count_to(8);
    let hi_c = c_m_of(&Shape { mcond: MCond::Hi, ..count_to_shape(8) });
    two_conds.step_m[0] = ite(hi_c, add(var(I, 8), lit(1, 8), 8), var(I, 8));
    for (name, bad, why) in [
        ("no X19", no_x19, "the frame lacks X19"),
        ("exit arm", wrong_arm, "is not Ite(c, value,"),
        ("two conditions", two_conds, "different conditions"),
    ] {
        assert!(goal_of(&bad).is_err_and(|e| e.contains(why)), "N11 {name}");
        for filter in [LoopFilter::On, LoopFilter::Off] {
            let r = prove(&bad, filter);
            assert!(declined(&r) && full(&r).contains(why), "N11 {name} ({filter:?}): {}", msg(&r));
        }
    }
}
