// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Tests of the additive-cancellation route (CANCEL-1): the theorem and its
//! audit, the step and its guards, and the route
//! ([`super::super::try_cancel_discharge`]).

use std::collections::HashSet;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use clean_kernel::expr::UsedConstants;
use clean_kernel::{ConstantKind, TypeChecker};
use trust_types::{Formula, Sort};

use super::super::kterm::refl;
use super::super::{
    AddCommFilter, CANCEL_KERNEL_RUNS, CancelFilter, ReflectCtx, StrengthFilter,
    cancel_discharge_in, cancel_obligation, reflect_formula, run_recheck_thread, strength_fragment,
    try_add_comm_discharge, try_cancel_discharge, try_mem_store_load_discharge,
    try_o1_instantiation_discharge, try_shared_core_discharge, try_strength_discharge,
};
use super::*;

// ── Formulas ─────────────────────────────────────────────────────────────────

fn var(name: &str, w: u32) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(w))
}
fn lit(value: i128, width: u32) -> Formula {
    Formula::BitVec { value, width }
}
fn add(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvAdd(Box::new(l), Box::new(r), w)
}
fn sub(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvSub(Box::new(l), Box::new(r), w)
}
fn mul(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvMul(Box::new(l), Box::new(r), w)
}
fn shl(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvShl(Box::new(l), Box::new(r), w)
}
fn extract(x: Formula, high: u32) -> Formula {
    Formula::BvExtract { inner: Box::new(x), high, low: 0 }
}
fn zext(x: Formula, k: u32) -> Formula {
    Formula::BvZeroExt(Box::new(x), k)
}
fn or(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvOr(Box::new(l), Box::new(r), w)
}

/// The variable of a `w`-bit rung: `X0`, or its low 32 bits.
fn x(w: u32) -> Formula {
    if w == 64 { var("X0", 64) } else { extract(var("X0", 64), w - 1) }
}

/// r08's `big`: `MAX - 1000` at `w` bits, the SSA value the spec uses twice.
fn big(w: u32) -> Formula {
    sub(lit((1i128 << w) - 1, w), lit(1000, w), w)
}

/// r08's cancelled term, `(big + x) - big`.
fn cancellable(w: u32) -> Formula {
    sub(add(big(w), x(w), w), big(w), w)
}

/// r08's specification, `((big + x) - big) + addend`.
fn r08_spec(w: u32, addend: i128) -> Formula {
    add(sub(add(big(w), x(w), w), big(w), w), lit(addend, w), w)
}

/// r08 at O2: the machine computes `x + addend`, the spec `((big + x) - big) + 1`.
fn r08(w: u32, addend: i128) -> (Formula, Formula) {
    (add(x(w), lit(addend, w), w), r08_spec(w, 1))
}

/// s02, a strength shape with no cancellation: `(x + 7) + (x << 1)` against
/// `x * 3 + 7`.
fn s02() -> (Formula, Formula) {
    let x = || var("X0", 64);
    (
        add(add(x(), lit(7, 64), 64), shl(x(), lit(1, 64), 64), 64),
        add(mul(x(), lit(3, 64), 64), lit(7, 64), 64),
    )
}

/// The label of one cancellation and nothing else.
const R08_LABEL: &str =
    "Trust.BVA.add_sub_cancel+Clean.BVC congruence (O(1) add@N, additive cancellation)";

// ── kernel helpers ───────────────────────────────────────────────────────────

/// The watchdog every kernel check in these tests runs under.
const LIMIT: Duration = Duration::from_secs(180);

/// How many cancel kernel checks this thread has started.
fn kernel_runs() -> usize {
    CANCEL_KERNEL_RUNS.with(std::cell::Cell::get)
}

/// Build the memoized base, outside any watchdog.
fn warm() {
    run_recheck_thread("cancel-warm", || cancel_base().map(|_| ()))
        .expect("kernel thread")
        .expect("the cancel base builds");
}

/// The commuting-mode reflection of `f`'s core (variables as concrete bit
/// lists).
fn core(f: &Formula) -> Expr {
    reflect_formula(f, &mut ReflectCtx::commuting()).expect("in fragment").core
}

/// The kernel's verdict on `val : ty` in the cancel environment, under the
/// watchdog: PANICS if the kernel has not answered within [`LIMIT`].
fn kernel_check(what: &str, leaves: &[(&str, u32)], val: Expr, ty: Expr) -> Result<(), String> {
    warm();
    let leaves: Vec<(String, u32)> = leaves.iter().map(|(n, w)| ((*n).to_string(), *w)).collect();
    let (tx, rx) = mpsc::channel();
    let start = Instant::now();
    std::thread::spawn(move || {
        let verdict = run_recheck_thread("cancel-test", move || {
            let env = cancel_env(&leaves)?;
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(&val, &ty).map_err(|e| format!("{e:?}"))
        })
        .map_err(|e| e.to_string())
        .and_then(|r| r);
        let _ = tx.send(verdict);
    });
    let verdict = rx
        .recv_timeout(LIMIT)
        .unwrap_or_else(|_| panic!("{what}: the kernel ran past the {LIMIT:?} watchdog"));
    let shown = verdict.as_ref().err().map(|e| e.chars().take(200).collect::<String>());
    println!("WATCHDOG {what}: {shown:?} in {:?}", start.elapsed());
    verdict
}

/// The cancel route with the filter OFF under the watchdog.
fn cancel_unfiltered(what: &str, machine: &Formula, auto: &Formula) -> Option<String> {
    warm();
    let (machine, auto) = (machine.clone(), auto.clone());
    let (tx, rx) = mpsc::channel();
    let start = Instant::now();
    std::thread::spawn(move || {
        let _ = tx.send(try_cancel_discharge(&machine, &auto, CancelFilter::Off));
    });
    let verdict = rx
        .recv_timeout(LIMIT)
        .unwrap_or_else(|_| panic!("{what}: the kernel ran past the {LIMIT:?} watchdog"));
    println!("WATCHDOG {what}: {verdict:?} in {:?}", start.elapsed());
    verdict
}

/// `bvfEval step.before = bvfEval step.core`.
fn step_goal(s: &Step) -> Expr {
    kx::eq_list(kx::evalf(s.before.clone()), kx::evalf(s.core.clone()))
}

/// A concrete bit list, least significant bit first.
fn bl(bits: &[bool]) -> Expr {
    bits.iter()
        .rev()
        .fold(kx::nil(), |acc, &b| kx::cons(if b { kx::btrue() } else { kx::bfalse() }, acc))
}

/// Every application of `Nat.mod`, `Nat.div`, `bvTwoPow`, `natToBvAux`,
/// `bvMul` or `bvShl` to closed arguments in `e`.
fn closed_heavy_apps(e: &Expr, found: &mut Vec<String>) {
    if let ExprKind::Const(name, _) = e.get_app_fn().kind() {
        let n = name.to_string();
        let args = e.get_app_args();
        let arity = match n.as_str() {
            "Nat.mod"
            | "Nat.div"
            | "Clean.BVC.natToBvAux"
            | "Clean.BVC.bvMul"
            | "Clean.BVC.bvShl" => 2,
            "Clean.BVC.bvTwoPow" => 1,
            _ => usize::MAX,
        };
        if args.len() == arity && args.iter().all(|a| !a.has_loose_bvars()) {
            found.push(format!("{e}"));
        }
    }
    match e.kind() {
        ExprKind::App(f, a) => {
            closed_heavy_apps(f, found);
            closed_heavy_apps(a, found);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            closed_heavy_apps(ty, found);
            closed_heavy_apps(body, found);
        }
        _ => {}
    }
}

// ── the theorem ──────────────────────────────────────────────────────────────

/// The theorem registers, and every audited name (it and its citations) is a
/// `Theorem` carrying its proof with empty domain and foundational axiom
/// closures. Independently of `add_decl`, the proof re-checks against its
/// statement in the strength base.
#[test]
fn add_sub_cancel_is_kernel_checked_and_audited() {
    run_recheck_thread("cancel-theorem", || {
        let start = Instant::now();
        let env = cancel_base().expect("the cancel base builds and passes its audit");
        println!("BUILD-TIME cancel layer (with the strength base) {:?}", start.elapsed());
        for name in audited() {
            let n = Name::from_string(name);
            let info = env.get_const(&n).unwrap_or_else(|| panic!("{name} is present"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name}");
            assert!(info.value.is_some(), "{name} carries its proof");
            let deps = env.axiom_deps(&n).unwrap_or_else(|| panic!("{name}: no closure"));
            assert!(deps.is_empty(), "{name} reaches an axiom: {deps:?}");
            let found =
                env.foundational_axiom_deps(&n).unwrap_or_else(|| panic!("{name}: no closure"));
            assert!(found.is_empty(), "{name} reaches a foundational axiom: {found:?}");
        }
        let base = strength::strength_base().expect("strength base");
        assert!(base.get_const(&Name::from_string(names::ADD_SUB_CANCEL)).is_none());
        for (name, type_, value) in theorems().expect("builder") {
            let tc = TypeChecker::with_mode(base, base.mode());
            tc.check_type(&value, &type_).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        }
    })
    .expect("kernel thread");
}

/// The statement, as text: a change to what the theorem says is a visible
/// diff here and not only in the proof builder.
#[test]
fn the_statement_is_pinned() {
    let all = theorems().expect("builder");
    assert_eq!(all.len(), 1);
    assert_eq!(all[0].0, names::ADD_SUB_CANCEL);
    assert_eq!(
        all[0].1.to_string(),
        "(x : List Bool) -> (x1 : List Bool) -> Clean.BVC.bvLen x = Clean.BVC.bvLen x1 -> Clean.BVI.addRecM (Clean.BVI.addRecM x x1 Bool.false) (Clean.BVC.bvNot x) Bool.true = x1"
    );
}

/// `base` with `name` replaced by an axiom of the same statement.
fn axiomatized(mut env: Environment, name: &str) -> Environment {
    let n = Name::from_string(name);
    let type_ = env.get_const(&n).expect("present").type_.clone();
    assert!(env.forget_decl(&n), "{name} removed");
    env.add_decl(Declaration::Axiom { name: n, level_params: vec![], type_ })
        .expect("axiom of the same statement");
    env
}

/// The audit fails closed: a value lemma the proof cites replaced by an axiom
/// of the same statement, and the theorem's name already taken by an axiom,
/// each make the build `Err`. The untouched base builds.
#[test]
fn the_cancel_audit_fails_closed() {
    run_recheck_thread("cancel-audit-negative", || {
        let base = strength::strength_base().expect("strength base").clone();
        build_base(base.clone()).expect("the untouched base builds");
        for name in [bvv::NAT_TO_BV_TO_NAT, bvv::BV_NOT_VAL] {
            let err = build_base(axiomatized(base.clone(), name)).expect_err(name);
            assert!(err.starts_with("audit:"), "{name}: {err}");
        }
        let mut env = base;
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(names::ADD_SUB_CANCEL),
            level_params: vec![],
            type_: Expr::const_str("True"),
        })
        .expect("axiom");
        let err = build_base(env).expect_err("name taken");
        assert!(err.contains(names::ADD_SUB_CANCEL), "{err}");
    })
    .expect("kernel thread");
}

/// The route half: in an environment whose audit fails, the route declines
/// the r08 obligation it proves in the real environment.
#[test]
fn a_failed_audit_makes_the_route_decline() {
    fn doctored(leaves: &[(String, u32)]) -> Result<Environment, String> {
        let base = axiomatized(strength::strength_base()?.clone(), bvv::NAT_TO_BV_TO_NAT);
        let mut env = build_base(base)?;
        add_comm::add_leaf_bits(&mut env, leaves);
        Ok(env)
    }
    let (machine, auto) = r08(64, 1);
    let err = run_recheck_thread("cancel-doctored", || doctored(&[]).map(|_| ()))
        .expect("kernel thread")
        .expect_err("the doctored base fails its audit");
    assert!(err.starts_with("audit:"), "{err}");
    assert_eq!(cancel_discharge_in(&machine, &auto, CancelFilter::On, doctored), None);
    assert_eq!(
        cancel_discharge_in(&machine, &auto, CancelFilter::On, cancel_env).as_deref(),
        Some(R08_LABEL),
        "the real environment proves it"
    );
}

/// The premise is needed: at `c = [t]`, `x = [t, f]` (lengths 1 and 2) the
/// conclusion is false and the kernel refuses `Eq.refl` for it; at
/// `c = [t, f]`, `x = [t, t]` the instance is accepted and the conclusion
/// computes.
#[test]
fn the_premise_is_needed() {
    let lhs = |c: &Expr, x: &Expr| {
        addm(addm(c.clone(), x.clone(), kx::bfalse()), kx::bv_not(c.clone()), kx::btrue())
    };
    let (c, x) = (bl(&[true]), bl(&[true, false]));
    assert!(
        kernel_check("unequal lengths", &[], refl(lb(), lhs(&c, &x)), eq(lb(), lhs(&c, &x), x))
            .is_err(),
        "the conclusion at unequal lengths was accepted"
    );
    let (c, x) = (bl(&[true, false]), bl(&[true, true]));
    let h = refl(nat(), nlit(2));
    kernel_check(
        "the instance at width 2",
        &[],
        cite(names::ADD_SUB_CANCEL, [c.clone(), x.clone(), h]),
        eq(lb(), lhs(&c, &x), x.clone()),
    )
    .expect("the instance holds");
    kernel_check("refl at width 2", &[], refl(lb(), x.clone()), eq(lb(), lhs(&c, &x), x))
        .expect("the true conclusion computes");
}

// ── the step ─────────────────────────────────────────────────────────────────

/// The step on r08's spec core, at 64 and 32 bits: `(big + x) - big` becomes
/// `x`, and the step term is a proof of `bvfEval before = bvfEval core`.
#[test]
fn the_step_is_kernel_checked() {
    for w in [64, 32] {
        let (l, r) = (core(&add(big(w), x(w), w)), core(&big(w)));
        let s = sub_cancel_step(&l, &r).expect("the step applies");
        assert_eq!(s.theorem, names::ADD_SUB_CANCEL);
        assert_eq!(s.before, kx::sub(l.clone(), r.clone()));
        assert_eq!(s.core, core(&x(w)));
        let start = Instant::now();
        kernel_check(&format!("step at {w}"), &[("X0", 64)], s.proof.clone(), step_goal(&s))
            .unwrap_or_else(|e| panic!("width {w}: {e}"));
        println!("STEP width {w}: {:?}", start.elapsed());
    }
}

/// The guards decline, in Rust: a subtrahend other than the added `c`, a
/// minuend that is not an `Add`, widths other than 32 and 64, and `c` and `x`
/// of different widths.
#[test]
fn guards_decline_outside_the_family() {
    let (l, r) = (core(&add(big(64), x(64), 64)), core(&big(64)));
    assert!(sub_cancel_step(&l, &r).is_some(), "the control applies");
    let other = core(&sub(lit(-1, 64), lit(999, 64), 64));
    assert!(sub_cancel_step(&l, &other).is_none(), "c differs by one");
    assert!(sub_cancel_step(&l, &core(&x(64))).is_none(), "x subtracted");
    assert!(sub_cancel_step(&r, &r).is_none(), "the minuend is not an Add");
    let swapped = core(&add(x(64), big(64), 64));
    assert!(sub_cancel_step(&swapped, &r).is_none(), "(x + c) - c is not offered");
    for w in [8, 16] {
        let xw = extract(var("X0", 64), w - 1);
        let l = core(&add(big(w), xw, w));
        assert!(sub_cancel_step(&l, &core(&big(w))).is_none(), "{w} bits");
    }
    let mixed = kx::add(core(&big(32)), core(&x(64)));
    assert!(sub_cancel_step(&mixed, &core(&big(32))).is_none(), "32-bit c, 64-bit x");
}

/// Forged step terms, bypassing the Rust guards, fail in the kernel under the
/// watchdog: the instance for `c` stated against a goal that subtracts
/// `c' = c + 1`, and an instance at a 32-bit `c` and a 64-bit `x` whose length
/// premise is built from the two length proofs. The honest instance in the
/// same harness is accepted.
#[test]
fn forged_instances_fail_in_the_kernel() {
    let leaf = [("X0", 64)];
    let (l, r) = (core(&add(big(64), x(64), 64)), core(&big(64)));
    let honest = sub_cancel_step(&l, &r).expect("step");
    let other = core(&sub(lit(-1, 64), lit(999, 64), 64));
    let forged_goal =
        kx::eq_list(kx::evalf(kx::sub(l.clone(), other.clone())), kx::evalf(core(&x(64))));
    assert!(
        kernel_check("c' = c + 1", &leaf, honest.proof.clone(), forged_goal).is_err(),
        "the instance was accepted for a different subtrahend"
    );
    kernel_check("honest", &leaf, honest.proof.clone(), step_goal(&honest))
        .expect("the control holds");

    let (c, xx) = (core(&big(32)), core(&x(64)));
    let (pc, wc) = core_len(&c).expect("c length");
    let (px, wx) = core_len(&xx).expect("x length");
    assert_eq!((wc, wx), (32, 64));
    let (ec, ex) = (kx::evalf(c.clone()), kx::evalf(xx.clone()));
    let n = kx::nat_lit(wc);
    let h = trans(nat(), len(&ec), n.clone(), len(&ex), pc, symm(nat(), len(&ex), n, px));
    let proof = cite(names::ADD_SUB_CANCEL, [ec, ex, h]);
    let goal = kx::eq_list(kx::evalf(kx::sub(kx::add(c.clone(), xx.clone()), c)), kx::evalf(xx));
    assert!(kernel_check("width mismatch", &leaf, proof, goal).is_err(), "accepted");
}

// ── the route ────────────────────────────────────────────────────────────────

/// r08 at 64 and 32 bits is proved through the public entry
/// `try_o1_instantiation_discharge` and through the cancel route, and by
/// neither the add-commutation nor the strength route. The label names
/// exactly the one theorem.
#[test]
fn r08_is_proved_by_the_cancel_route_only() {
    assert_eq!(label(&[names::ADD_SUB_CANCEL], 0), R08_LABEL);
    for w in [64, 32] {
        let (machine, auto) = r08(w, 1);
        assert!(strength_fragment(&machine) && strength_fragment(&auto), "{w}");
        let start = Instant::now();
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::On), None, "{w}");
        assert_eq!(try_strength_discharge(&machine, &auto, StrengthFilter::On), None, "{w}");
        assert_eq!(
            try_cancel_discharge(&machine, &auto, CancelFilter::On).as_deref(),
            Some(R08_LABEL),
            "{w}: cancel"
        );
        println!("CANCEL r08 width {w}: {:?}", start.elapsed());
        let start = Instant::now();
        assert_eq!(
            try_o1_instantiation_discharge(&machine, &auto).as_deref(),
            Some(R08_LABEL),
            "{w}: public entry"
        );
        println!("O1 r08 width {w}: {:?}", start.elapsed());
    }
}

/// The goal does not depend on the step builders (the T-U10 analogue): under
/// [`ReflectCtx::cancel`] and [`ReflectCtx::cancel_dry`] the `bvf` of each
/// side is byte-identical; the dry context splices no step at all, and the
/// step-on context splices at least one cancellation on the spec side. The
/// strength context splices none (its route is unchanged).
///
/// Besides r08 (the cancellation under a bare `Add`), the cancellation sits
/// under the wrappers whose goal tags the non-strength arms build from the
/// child's core: `Add(0, ·)` at 64 bits and the 32-bit readout
/// `Extract[31:0](ZeroExt(Or(0, ·), 32))`, so goal independence there is
/// pinned by this test and not only by `ctx.strength` routing those arms to
/// `strength_zero_wrapper` and `strength_extract_zext`.
#[test]
fn the_goal_does_not_depend_on_the_step_builders() {
    let readout32 = extract(zext(or(lit(0, 32), cancellable(32), 32), 32), 31);
    let pairs = [
        ("r08 64", r08(64, 1)),
        ("r08 32", r08(32, 1)),
        ("r08 x+2", r08(64, 2)),
        ("Add(0, cancel) at 64", (x(64), add(lit(0, 64), cancellable(64), 64))),
        ("Extract(ZeroExt(Or(0, cancel))) at 32", (x(32), readout32)),
    ];
    for (what, (machine, auto)) in &pairs {
        for f in [machine, auto] {
            let mut on = ReflectCtx::cancel();
            let mut dry = ReflectCtx::cancel_dry();
            let a = reflect_formula(f, &mut on).expect("reflects");
            let b = reflect_formula(f, &mut dry).expect("reflects");
            assert_eq!(format!("{:?}", a.bvf), format!("{:?}", b.bvf), "{what}: {f:?}");
            assert_eq!(dry.strength_rewrites, 0, "{what}: dry spliced a step");
            assert!(dry.strength_used.is_empty(), "{what}");
            assert_eq!(a.core != b.core, on.strength_rewrites > 0, "{what}: {f:?}");
        }
        let mut on = ReflectCtx::cancel();
        reflect_formula(auto, &mut on).expect("reflects");
        let cancels = on.strength_used.iter().filter(|n| **n == names::ADD_SUB_CANCEL).count();
        assert!(cancels >= 1, "{what}: the spec side was not cancelled");
        let mut strength = ReflectCtx::strength();
        reflect_formula(auto, &mut strength).expect("reflects");
        assert!(!strength.strength_used.contains(&names::ADD_SUB_CANCEL), "{what}");
    }
}

/// A narrow width keeps the bit-blast: at 4 bits `(c + x) - c + 1` against
/// `x + 1` splices no cancellation, the cancel route and the public O(1) entry
/// decline, and `try_kernel_recheckable_proof` grades it `KernelRecheckable`
/// (the bit-blast certificate), not `KernelInstantiated`.
#[test]
fn a_narrow_width_takes_the_bit_blast() {
    use crate::verify_output::{ProvenEvidence, try_kernel_recheckable_proof};
    let w = 4;
    let xw = var("N0", w);
    let k = sub(lit(15, w), lit(3, w), w);
    let auto = add(sub(add(k.clone(), xw.clone(), w), k, w), lit(1, w), w);
    let machine = add(xw, lit(1, w), w);
    let mut ctx = ReflectCtx::cancel();
    reflect_formula(&auto, &mut ctx).expect("reflects");
    assert_eq!(ctx.strength_rewrites, 0, "a cancellation was spliced at {w} bits");
    let before = kernel_runs();
    assert_eq!(try_cancel_discharge(&machine, &auto, CancelFilter::On), None);
    assert_eq!(kernel_runs(), before, "a cancel kernel check started");
    assert_eq!(try_o1_instantiation_discharge(&machine, &auto), None);
    let start = Instant::now();
    let evidence = try_kernel_recheckable_proof(&machine, &auto, None);
    println!("BIT-BLAST width {w}: {:?}", start.elapsed());
    assert!(
        matches!(evidence, Some(ProvenEvidence::KernelRecheckable(_))),
        "width {w}: {evidence:?}"
    );
}

/// Kernel rejection with the filter OFF, each under the watchdog, on pairs
/// where a cancellation still fires and only the closing equation is false:
/// a machine `x + 2` against r08's spec (64 bits), and a machine `x` against
/// it (32 bits). With the filter on each declines before the kernel. The r08
/// control is accepted with the filter off.
#[test]
fn wrong_cancellations_are_rejected_by_the_kernel() {
    let cases = [
        ("x + 2 at 64", add(x(64), lit(2, 64), 64), r08_spec(64, 1)),
        ("x at 32", x(32), r08_spec(32, 1)),
    ];
    for (what, machine, auto) in &cases {
        let before = kernel_runs();
        assert_eq!(try_cancel_discharge(machine, auto, CancelFilter::On), None, "{what}");
        assert_eq!(kernel_runs(), before, "{what}: a kernel check started with the filter on");
        let mut ctx = ReflectCtx::cancel();
        let rm = reflect_formula(machine, &mut ctx).expect("reflects");
        let ra = reflect_formula(auto, &mut ctx).expect("reflects");
        assert_ne!(rm.core, ra.core, "{what}");
        assert!(ctx.strength_used.contains(&names::ADD_SUB_CANCEL), "{what}: no step fired");
        assert_eq!(cancel_unfiltered(what, machine, auto), None, "{what}: the kernel accepted");
    }
    let (machine, auto) = r08(64, 1);
    assert_eq!(cancel_unfiltered("r08 control", &machine, &auto).as_deref(), Some(R08_LABEL));
}

/// A pair with no cancellation is not this route's: s02 (strength steps, no
/// cancellation) and a pair whose cores already meet decline before any kernel
/// check.
#[test]
fn a_pair_with_no_cancellation_is_declined_before_the_kernel() {
    let (s02_m, s02_a) = s02();
    let plain = add(x(64), lit(1, 64), 64);
    let before = kernel_runs();
    assert_eq!(try_cancel_discharge(&s02_m, &s02_a, CancelFilter::On), None);
    assert_eq!(try_cancel_discharge(&plain, &plain, CancelFilter::On), None);
    assert!(cancel_obligation(&plain, &plain, CancelFilter::On).is_none());
    assert_eq!(kernel_runs(), before, "a cancel kernel check started");
}

/// Nothing the theorem states or proves applies `Nat.mod`, `Nat.div`,
/// `bvTwoPow`, `natToBvAux`, `bvMul` or `bvShl` to closed data, nor does the
/// r08 obligation's goal or discharge. Every constant they use is a leaf bit
/// or not an axiom, and every theorem they cite is audited (here or in the
/// strength base).
#[test]
fn every_citation_is_audited_and_nothing_computes_on_closed_data() {
    let (machine, auto) = r08(64, 1);
    let ob = cancel_obligation(&machine, &auto, CancelFilter::On).expect("r08 obligation");
    let mut found = Vec::new();
    closed_heavy_apps(&nmod(nlit(5), nlit(2)), &mut found);
    assert_eq!(found.len(), 1, "the walker sees what it looks for");
    run_recheck_thread("cancel-citations", move || {
        let env = cancel_env(&ob.leaves).expect("cancel env");
        let audited: HashSet<Name> =
            strength::audited().into_iter().chain(audited()).map(Name::from_string).collect();
        let mut terms: Vec<(String, Expr)> = Vec::new();
        for (name, ty, val) in theorems().expect("builder") {
            terms.push((format!("{name} statement"), ty));
            terms.push((format!("{name} proof"), val));
        }
        terms.push(("r08 goal".into(), ob.goal.clone()));
        terms.push(("r08 discharge".into(), ob.discharge.clone()));
        for (what, term) in terms {
            let mut found = Vec::new();
            closed_heavy_apps(&term, &mut found);
            assert!(found.is_empty(), "{what} computes on closed data: {found:?}");
            let mut used = HashSet::new();
            term.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
            for c in used {
                if c.to_string().starts_with("BVC_LEAFBIT_") {
                    continue;
                }
                let info = env.get_const(&c).unwrap_or_else(|| panic!("{what}: {c} absent"));
                assert_ne!(info.kind, ConstantKind::Axiom, "{what} cites the axiom {c}");
                if info.kind == ConstantKind::Theorem {
                    assert!(audited.contains(&c), "{what} cites {c}, which is not audited");
                }
            }
        }
        let mut env = env;
        strength::admit_obligation(&mut env, ob.goal, ob.discharge).expect("admitted");
    })
    .expect("kernel thread");
}

// ── what the reviews found untested ──────────────────────────────────────────

/// A cancellation spliced beneath a bare `BvExtract` (low 0, inner not a
/// `ZeroExt`) is dropped from the proof, since that arm replaces its child's
/// core with its own `bvf`; the context's record still counts it. The route's
/// filter and label read the discharge term instead: with the filter on the
/// pair declines before any kernel check, and with it off the label names no
/// theorem the term does not cite.
#[test]
fn a_cancellation_dropped_beneath_a_bare_extract_does_not_count() {
    let f = zext(extract(cancellable(64), 31), 32);
    assert!(strength_fragment(&f));
    let mut ctx = ReflectCtx::cancel();
    reflect_formula(&f, &mut ctx).expect("reflects");
    assert!(ctx.strength_used.contains(&names::ADD_SUB_CANCEL), "the record counts the step");
    let before = kernel_runs();
    assert!(cancel_obligation(&f, &f, CancelFilter::On).is_none());
    assert_eq!(try_cancel_discharge(&f, &f, CancelFilter::On), None);
    assert_eq!(kernel_runs(), before, "a cancel kernel check started");
    let ob = cancel_obligation(&f, &f, CancelFilter::Off).expect("in fragment");
    assert_eq!(ob.label, LABEL_TAIL, "the label names a theorem the term does not cite");
}

/// Without the cancel route r08 is [VALIDATED]. For a scalar item with no
/// precondition and no `Select`, `try_kernel_recheckable_proof` tries the
/// memory route, the O(1) routes, the 128-bit pair split, the bit-blast and the
/// wide-multiply citation, in that order. On r08 at 64 and 32 bits the memory,
/// shared-core, add-commutation and strength routes decline, the item is no
/// register pair and holds no multiply, and ay's bit-blast refutation is over
/// `MAX_RECHECKABLE_REFUTATION_STEPS`, so the bit-blast declines it before any
/// kernel re-check (the step counts are printed).
#[test]
fn r08_is_validated_without_the_cancel_route() {
    use crate::verify_output::{MAX_RECHECKABLE_REFUTATION_STEPS, formula_to_bvexpr};
    for w in [64, 32] {
        let (machine, auto) = r08(w, 1);
        assert_eq!(try_mem_store_load_discharge(&machine, &auto), None, "{w}: memory");
        assert_eq!(try_shared_core_discharge(&machine, &auto), None, "{w}: shared core");
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::On), None, "{w}");
        assert_eq!(try_strength_discharge(&machine, &auto, StrengthFilter::On), None, "{w}");
        let lhs = formula_to_bvexpr(&machine).expect("the machine side lowers");
        let rhs = formula_to_bvexpr(&auto).expect("the spec side lowers");
        let start = Instant::now();
        let proof = ay_proof::export_bv_blast_proof_expr(&lhs, &rhs).expect("ay refutes it");
        let steps = proof.refutation.steps.len();
        println!("BIT-BLAST r08 width {w}: {steps} refutation steps in {:?}", start.elapsed());
        assert!(
            steps > MAX_RECHECKABLE_REFUTATION_STEPS,
            "{w}: {steps} steps, within the bit-blast's {MAX_RECHECKABLE_REFUTATION_STEPS}"
        );
    }
}

/// The route order is pinned: cancel runs only after the older routes. A pair
/// the shared-core route and the cancel route both prove (r08's spec against
/// itself) keeps shared-core's label, and a pair the strength route and the
/// cancel route both prove (`(big + ·) - big` around each side of s02) keeps
/// strength's.
#[test]
fn an_earlier_route_keeps_a_pair_it_proves() {
    let spec = r08_spec(64, 1);
    let shared = try_shared_core_discharge(&spec, &spec).expect("shared core proves it");
    assert_eq!(
        try_cancel_discharge(&spec, &spec, CancelFilter::On).as_deref(),
        Some(R08_LABEL),
        "cancel proves it too"
    );
    assert_eq!(try_o1_instantiation_discharge(&spec, &spec), Some(shared));

    let wrap = |f: Formula| sub(add(big(64), f, 64), big(64), 64);
    let (m, a) = s02();
    let (m, a) = (wrap(m), wrap(a));
    let strength = try_strength_discharge(&m, &a, StrengthFilter::On).expect("strength proves it");
    let cancel = try_cancel_discharge(&m, &a, CancelFilter::On).expect("cancel proves it too");
    assert!(cancel.contains(names::ADD_SUB_CANCEL), "{cancel}");
    assert_ne!(cancel, strength);
    assert_eq!(try_o1_instantiation_discharge(&m, &a), Some(strength));
}

/// [`CITED`] lists exactly the theorems the proof of `add_sub_cancel` and the
/// step terms (at 64 and 32 bits) cite directly, apart from the ring
/// normaliser's vocabulary (`nat_ring::CITED`, `nat_ring::names::ALL`), which
/// [`audited`] adds whole: none missing, none stale. And the production
/// environment, `cancel_env`, passes `audit_theorems` over [`audited`].
#[test]
fn cited_is_exactly_what_the_proofs_cite() {
    run_recheck_thread("cancel-cited", || {
        let env = cancel_env(&[("X0".to_string(), 64)]).expect("cancel env");
        audit_theorems(&env, &audited()).expect("the production environment passes the audit");
        let mut used = HashSet::new();
        for (_, _, proof) in theorems().expect("builder") {
            proof.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
        }
        for w in [64, 32] {
            let (l, r) = (core(&add(big(w), x(w), w)), core(&big(w)));
            let step = sub_cancel_step(&l, &r).expect("step");
            step.proof.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
        }
        let theorem = |n: &Name| env.get_const(n).is_some_and(|i| i.kind == ConstantKind::Theorem);
        let own: HashSet<Name> = names::ALL
            .iter()
            .chain(&nat_ring::CITED)
            .chain(&nat_ring::names::ALL)
            .map(|n| Name::from_string(n))
            .collect();
        let cited: HashSet<Name> = CITED.iter().map(|n| Name::from_string(n)).collect();
        let mut direct: Vec<String> = used
            .iter()
            .filter(|n| theorem(n) && !own.contains(*n))
            .map(ToString::to_string)
            .collect();
        let mut listed: Vec<String> =
            cited.iter().filter(|n| theorem(n)).map(ToString::to_string).collect();
        direct.sort();
        listed.sort();
        assert_eq!(direct, listed, "the theorems cited directly, against CITED");
        let stale: Vec<String> =
            cited.iter().filter(|n| !used.contains(*n)).map(ToString::to_string).collect();
        assert!(stale.is_empty(), "CITED names {stale:?}, which no term cites");
    })
    .expect("kernel thread");
}
