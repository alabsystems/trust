// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Tests of the strength-reduced-multiply route ([`super::try_strength_discharge`])
//! and of the reflection it shares with the older routes.

use std::collections::HashSet;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, Declaration, Environment, Expr, ExprKind, TypeChecker};
use trust_types::{Formula, Sort};

use super::bv_value::names as bvv;
use super::strength::{self, names};
use super::{
    AddCommFilter, ReflectCtx, STRENGTH_KERNEL_RUNS, STRENGTH_MAX_NODES, StrengthFilter, kx,
    reflect_formula, run_recheck_thread, strength_discharge_in, strength_fragment,
    strength_obligation, try_add_comm_discharge, try_mem_store_load_discharge,
    try_o1_instantiation_discharge, try_original_conjunction_discharge, try_shared_core_discharge,
    try_strength_discharge,
};

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
fn or(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvOr(Box::new(l), Box::new(r), w)
}
fn xor(l: Formula, r: Formula, w: u32) -> Formula {
    Formula::BvXor(Box::new(l), Box::new(r), w)
}
fn zext(x: Formula, k: u32) -> Formula {
    Formula::BvZeroExt(Box::new(x), k)
}
fn extract(x: Formula, high: u32) -> Formula {
    Formula::BvExtract { inner: Box::new(x), high, low: 0 }
}
fn x64() -> Formula {
    var("X0", 64)
}
fn x32() -> Formula {
    extract(x64(), 31)
}

// ── the measured step-(5) Formulas (slice1-final.md, "Step 1 measurement") ──

/// s02: `(x + 7) + (x << 1)` against `x * 3 + 7`.
fn s02() -> (Formula, Formula) {
    (
        add(add(x64(), lit(7, 64), 64), shl(x64(), lit(1, 64), 64), 64),
        add(mul(x64(), lit(3, 64), 64), lit(7, 64), 64),
    )
}
/// s08 `rung`: `(x + x) + (x << 1)` against `x * 3 + x`.
fn s08_rung() -> (Formula, Formula) {
    (
        add(add(x64(), x64(), 64), shl(x64(), lit(1, 64), 64), 64),
        add(mul(x64(), lit(3, 64), 64), x64(), 64),
    )
}
/// s09 `h` (32 bits): `(3 + (x << 3)) - x` against `x * 7 + 3`.
fn s09_h() -> (Formula, Formula) {
    (
        sub(add(lit(3, 32), shl(x32(), lit(3, 32), 32), 32), x32(), 32),
        add(mul(x32(), lit(7, 32), 32), lit(3, 32), 32),
    )
}
/// s09 `rung`: the same, behind the register-move and zero-extension
/// wrappers of the 64-bit return.
fn s09_rung() -> (Formula, Formula) {
    let w = || or(lit(0, 32), x32(), 32);
    (
        or(lit(0, 64), zext(sub(add(lit(3, 32), shl(w(), lit(3, 32), 32), 32), w(), 32), 32), 64),
        zext(add(mul(x32(), lit(7, 32), 32), lit(3, 32), 32), 32),
    )
}
/// s14 / s15: `(x + 1) ^ (UBFM lsl #1)` against `(x + 1) ^ (x * 2)`.
fn s14() -> (Formula, Formula) {
    (
        xor(add(x64(), lit(1, 64), 64), shl(zext(extract(x64(), 62), 1), lit(1, 64), 64), 64),
        xor(add(x64(), lit(1, 64), 64), mul(x64(), lit(2, 64), 64), 64),
    )
}

/// FNV-1a, so a pin does not depend on std's unspecified hasher.
fn fnv1a(s: &str) -> u64 {
    s.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
}

/// T-U11. Outside strength the reflection is unchanged: `closed()` and
/// `commuting()` produce byte-identical `bvf`, `core` and `proof` (and the
/// same refusals) on a corpus with an Extract over a ZeroExt, an Or-zero and
/// an Add-zero wrapper, a standalone ZeroExt, and the measured rungs.
///
/// Where the pin comes from: this test was first run, with the value unset,
/// on the tree of commit `8681b13bfa`, before any reflection change. There
/// `verify_output_instantiate.rs` differed from main `4d0e2740cf` only in its
/// `mod` declarations (`git diff 4d0e2740cf 8681b13bfa --
/// crates/trust-cg-bridge/src/verify_output_instantiate.rs`), and the one
/// other input, the `add_comm` step terms the commuting reflection splices,
/// is pinned to main's bytes by `add_comm`'s `ADD_COMM_PIN`, itself measured
/// on main's `add_comm.rs` before its helpers moved. So the value is main's
/// reflector's output.
#[test]
fn non_strength_reflection_is_byte_pinned() {
    use std::fmt::Write as _;
    let wrapped = extract(zext(or(lit(0, 32), add(x32(), var("W1", 32), 32), 32), 32), 31);
    let mut corpus = vec![
        wrapped,
        or(lit(0, 64), add(lit(7, 64), mul(x64(), lit(3, 64), 64), 64), 64),
        add(lit(0, 64), mul(x64(), var("X1", 64), 64), 64),
        zext(x32(), 32),
    ];
    for (m, a) in [s02(), s08_rung(), s09_h(), s09_rung(), s14()] {
        corpus.push(m);
        corpus.push(a);
    }
    let mut s = String::new();
    for f in &corpus {
        for (mode, mut ctx) in
            [("closed", ReflectCtx::closed()), ("commuting", ReflectCtx::commuting())]
        {
            match reflect_formula(f, &mut ctx) {
                Ok(r) => writeln!(
                    s,
                    "{mode}\n{:?}\n{:?}\n{:?}\n{:?} {}",
                    r.bvf, r.core, r.proof, ctx.leaves, ctx.add_swaps
                )
                .unwrap(),
                Err(e) => writeln!(s, "{mode} Err {e}").unwrap(),
            }
        }
    }
    assert_eq!((s.len(), fnv1a(&s)), (8_361_520, 12_354_292_827_586_967_593), "REFLECT_PIN");
}

// ── helpers ──────────────────────────────────────────────────────────────────

/// How many strength kernel checks this thread has started.
fn kernel_runs() -> usize {
    STRENGTH_KERNEL_RUNS.with(std::cell::Cell::get)
}

/// The strength route under a watchdog: PANICS if the kernel has not answered
/// within the limit. The memoized base is built first, outside the limit.
fn strength_bounded(what: &str, machine: &Formula, auto: &Formula) -> Option<String> {
    const LIMIT: Duration = Duration::from_secs(180);
    run_recheck_thread("strength-route-warm", || strength::strength_base().map(|_| ()))
        .expect("kernel thread")
        .expect("the strength base builds");
    let (machine, auto) = (machine.clone(), auto.clone());
    let (tx, rx) = mpsc::channel();
    let start = Instant::now();
    std::thread::spawn(move || {
        let _ = tx.send(try_strength_discharge(&machine, &auto, StrengthFilter::Off));
    });
    let verdict = rx
        .recv_timeout(LIMIT)
        .unwrap_or_else(|_| panic!("{what}: the kernel ran past the {LIMIT:?} watchdog"));
    println!("WATCHDOG {what}: {verdict:?} in {:?}", start.elapsed());
    verdict
}

/// Whether `e` is ground data: no bound variable and no leaf bit, so the
/// kernel could compute with it.
fn ground(e: &Expr) -> bool {
    let mut used = HashSet::new();
    e.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    !e.has_loose_bvars() && !used.iter().any(|c| c.to_string().starts_with("BVC_LEAFBIT_"))
}

/// Every application of `Nat.mod`, `Nat.div`, `bvTwoPow`, `natToBvAux`,
/// `bvMul` or `bvShl` to closed arguments in `e`, and every reflected
/// `BvF.Mul` or `BvF.Shl` node whose two operands are ground: `bvfEval` of
/// such a node is one reduction step from `bvMul` or `bvShl` on closed data.
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
            found.push(n.clone());
        }
        let node = matches!(n.as_str(), "Clean.BVC.BvF.Mul" | "Clean.BVC.BvF.Shl");
        if node && args.len() == 2 && args.iter().all(|a| ground(a)) {
            found.push(n);
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

/// The positive cases: the measured Formulas and the label each must carry.
fn positives() -> Vec<(&'static str, Formula, Formula, String)> {
    let (s02_m, s02_a) = s02();
    let (s08_m, s08_a) = s08_rung();
    let (h_m, h_a) = s09_h();
    let (r_m, r_a) = s09_rung();
    let (s14_m, s14_a) = s14();
    // The bare-shift fixture of the measurement: S1 alone.
    let bare_m = xor(add(x64(), lit(1, 64), 64), shl(x64(), lit(1, 64), 64), 64);
    let add_label = strength::label(&[names::SHL_MUL, names::COLLECT_ADD], 0);
    let sub_label = strength::label(&[names::SHL_MUL, names::COLLECT_SUB], 1);
    vec![
        ("s02", s02_m, s02_a, add_label.clone()),
        ("s08 rung", s08_m, s08_a, add_label),
        ("s09 h", h_m, h_a, sub_label.clone()),
        ("s09 rung", r_m, r_a, sub_label),
        ("s14", s14_m, s14_a.clone(), strength::label(&[names::SHL_HI_OUT, names::SHL_MUL], 0)),
        ("bare shift", bare_m, s14_a, strength::label(&[names::SHL_MUL], 0)),
    ]
}

// ── the tests ────────────────────────────────────────────────────────────────

// Raw Formula names are identities, not dotted Lean declaration spellings.
// In particular `01` and `1` inside a name must not become the same Nat
// component when the reflection states its kernel obligation.
const NUMERIC_NAME: &str = "X.01.a";
const OTHER_NUMERIC_NAME: &str = "X.1.a";

#[test]
fn raw_name_identity_survives_both_scalar_reflectors() {
    for (mut ctx, mode) in [(ReflectCtx::closed(), "opaque"), (ReflectCtx::commuting(), "per-bit")]
    {
        let x = reflect_formula(&var(NUMERIC_NAME, 64), &mut ctx).expect("first variable");
        let y = reflect_formula(&var(OTHER_NUMERIC_NAME, 64), &mut ctx).expect("second variable");
        assert_ne!(x.bvf, y.bvf, "{mode}: distinct Formula identities collapsed");
        assert_eq!(
            ctx.leaves,
            vec![(NUMERIC_NAME.to_string(), 64), (OTHER_NUMERIC_NAME.to_string(), 64)]
        );
    }
}

#[test]
fn raw_name_identity_shared_core_kernel_rejects_cross_variable_equality() {
    let (x, y) = (var(NUMERIC_NAME, 64), var(OTHER_NUMERIC_NAME, 64));
    assert!(try_shared_core_discharge(&x, &x).is_some(), "same-variable positive");
    // The shared route has no structural core-equality filter: this reaches
    // the kernel, whose goal must still distinguish the two opaque leaves.
    assert_eq!(try_shared_core_discharge(&x, &y), None, "different variables are not equal");
}

#[test]
fn raw_name_identity_commuting_kernel_rejects_cross_variable_equality() {
    let x = var(NUMERIC_NAME, 64);
    let y = var(OTHER_NUMERIC_NAME, 64);
    let machine = add(lit(7, 64), mul(x.clone(), lit(3, 64), 64), 64);
    let valid = add(mul(x, lit(3, 64), 64), lit(7, 64), 64);
    let invalid = add(mul(y, lit(3, 64), 64), lit(7, 64), 64);
    assert!(
        try_add_comm_discharge(&machine, &valid, AddCommFilter::On).is_some(),
        "same-variable positive"
    );
    // Filter off makes rejection depend on the actual kernel goal, rather
    // than only on the pre-filter noticing the different reflected cores.
    assert_eq!(try_add_comm_discharge(&machine, &invalid, AddCommFilter::Off), None);
    assert_eq!(try_add_comm_discharge(&machine, &invalid, AddCommFilter::On), None);
}

#[test]
fn raw_name_identity_strength_kernel_rejects_cross_variable_equality() {
    let x = var(NUMERIC_NAME, 64);
    let y = var(OTHER_NUMERIC_NAME, 64);
    let machine = add(add(x.clone(), lit(7, 64), 64), shl(x.clone(), lit(1, 64), 64), 64);
    let valid = add(mul(x, lit(3, 64), 64), lit(7, 64), 64);
    let invalid = add(mul(y, lit(3, 64), 64), lit(7, 64), 64);
    assert!(strength_bounded("same numeric name", &machine, &valid).is_some());
    // At x=0, y=1 these evaluate to 7 and 10. The filter-off check must
    // reject through the kernel even though both routes apply the same
    // legitimate strength-reduction theorems.
    assert_eq!(strength_bounded("distinct numeric names", &machine, &invalid), None);
    assert_eq!(try_strength_discharge(&machine, &invalid, StrengthFilter::On), None);
    assert_eq!(try_o1_instantiation_discharge(&machine, &invalid), None);
}

/// T-U4. The measured step-(5) pairs (s02, s08 `rung`, s09 `h`, s09 `rung`,
/// s14, and the bare-shift fixture) are proved through the public entry
/// `try_o1_instantiation_discharge` and through the strength route, and by
/// neither older route. Each label names exactly the theorems used:
/// `addRecM_comm` only for s09, where `3 + x * 8` is reordered.
#[test]
fn measured_rungs_are_proved_by_the_strength_route_only() {
    for (what, machine, auto, label) in positives() {
        assert!(strength_fragment(&machine) && strength_fragment(&auto), "{what}");
        let start = Instant::now();
        assert_eq!(try_shared_core_discharge(&machine, &auto), None, "{what}: shared core");
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::On), None, "{what}");
        assert_eq!(
            try_strength_discharge(&machine, &auto, StrengthFilter::On).as_deref(),
            Some(label.as_str()),
            "{what}: strength"
        );
        assert_eq!(
            try_o1_instantiation_discharge(&machine, &auto).as_deref(),
            Some(label.as_str()),
            "{what}: public entry"
        );
        assert_eq!(label.contains("addRecM_comm"), what.starts_with("s09"), "{what}: {label}");
        println!("T-U4 {what}: {label} in {:?}", start.elapsed());
    }
}

/// T-U5. Kernel rejection with the filter OFF, each under a watchdog: the
/// object computes something else, the route hands the kernel the term
/// anyway, and the KERNEL refuses it. With the filter on each declines
/// before the kernel. The s02 control is accepted with the filter off, so
/// the `None`s are about the equations and not about a broken harness.
#[test]
fn wrong_objects_are_rejected_by_the_kernel() {
    let (s02_m, _) = s02();
    let (_, s14_a) = s14();
    let (_, h_a) = s09_h();
    let y32 = extract(var("X1", 64), 31);
    let cases = [
        ("s02 vs x*3+8", s02_m.clone(), add(mul(x64(), lit(3, 64), 64), lit(8, 64), 64)),
        ("s02 vs x*5+7", s02_m.clone(), add(mul(x64(), lit(5, 64), 64), lit(7, 64), 64)),
        (
            "s14 shift 2",
            xor(add(x64(), lit(1, 64), 64), shl(zext(extract(x64(), 62), 1), lit(2, 64), 64), 64),
            s14_a,
        ),
        (
            "s09 swapped sub",
            sub(x32(), add(lit(3, 32), shl(x32(), lit(3, 32), 32), 32), 32),
            h_a.clone(),
        ),
        (
            "S4 other multiplicand",
            sub(add(lit(3, 32), shl(x32(), lit(3, 32), 32), 32), y32, 32),
            h_a,
        ),
    ];
    for (what, machine, auto) in &cases {
        // The filter, not the kernel, declines each case, and no kernel check
        // starts. The cores always differ; every case but `s14 shift 2` has a
        // rewrite (there no step applies: the shift is not the
        // zero-extension amount, and `shl_mul` takes a variable operand), so
        // the cores test alone declines the other four.
        let before = kernel_runs();
        assert_eq!(try_strength_discharge(machine, auto, StrengthFilter::On), None, "{what}");
        assert_eq!(kernel_runs(), before, "{what}: a kernel check started with the filter on");
        let mut ctx = ReflectCtx::strength();
        let rm = reflect_formula(machine, &mut ctx).expect("reflects");
        let ra = reflect_formula(auto, &mut ctx).expect("reflects");
        assert_ne!(rm.core, ra.core, "{what}");
        assert_eq!(ctx.strength_rewrites > 0, *what != "s14 shift 2", "{what}");
        assert_eq!(strength_bounded(what, machine, auto), None, "{what}: the kernel accepted");
    }
    let (_, s02_a) = s02();
    assert!(strength_bounded("s02 control", &s02_m, &s02_a).is_some(), "the control holds");
}

/// T-U7. The guards decline before any kernel thread starts: a shift by the
/// width, by `2^62`, by a constant 129 or 200 bits wide, and a zero-extension
/// by four million. The first two are inside the pre-filter, and the step
/// builder splices nothing; the last three are outside it. Then, for every
/// positive case, no per-obligation term (goal or discharge) applies
/// `Nat.mod`, `Nat.div`, `bvTwoPow`, `natToBvAux`, `bvMul` or `bvShl` to
/// closed data, nor holds a `BvF.Mul` or `BvF.Shl` of ground operands; every
/// theorem the discharge names is audited; and the obligation is admitted,
/// so its transitive axiom closure is the leaf bits.
#[test]
fn guards_decline_before_the_kernel_and_nothing_computes_on_closed_data() {
    let auto = mul(x64(), lit(2, 64), 64);
    let in_fragment = [shl(x64(), lit(64, 64), 64), shl(x64(), lit(1 << 62, 64), 64)];
    let outside =
        [shl(x64(), lit(1, 129), 64), shl(x64(), lit(1, 200), 64), zext(x64(), 4_000_000)];
    let before = kernel_runs();
    for machine in &in_fragment {
        assert!(strength_fragment(machine), "{machine:?}");
        let mut ctx = ReflectCtx::strength();
        reflect_formula(machine, &mut ctx).expect("reflects");
        assert_eq!(ctx.strength_rewrites, 0, "{machine:?}: a step was spliced");
        assert_eq!(try_strength_discharge(machine, &auto, StrengthFilter::On), None);
    }
    for machine in &outside {
        assert!(!strength_fragment(machine), "{machine:?}");
        assert_eq!(try_strength_discharge(machine, &auto, StrengthFilter::On), None);
        assert_eq!(try_strength_discharge(&auto, machine, StrengthFilter::On), None);
    }
    assert_eq!(kernel_runs(), before, "a kernel check started");

    // The walker sees what it looks for.
    let mut found = Vec::new();
    closed_heavy_apps(
        &Expr::apps(Expr::const_str("Nat.mod"), [kx::nat_lit(5), kx::nat_lit(2)]),
        &mut found,
    );
    assert_eq!(found, ["Nat.mod"]);
    let mut found = Vec::new();
    let c = |v| kx::const_(kx::bits(v, 64));
    closed_heavy_apps(&kx::evalf(kx::mul(c(3), c(5))), &mut found);
    let leafy = reflect_formula(&mul(x64(), lit(3, 64), 64), &mut ReflectCtx::strength())
        .expect("reflects")
        .core;
    closed_heavy_apps(&kx::evalf(leafy), &mut found);
    assert_eq!(found, ["Clean.BVC.BvF.Mul"], "a ground multiply only");

    for (what, machine, auto, _) in positives() {
        let ob = strength_obligation(&machine, &auto, StrengthFilter::On).expect(what);
        let mut found = Vec::new();
        closed_heavy_apps(&ob.goal, &mut found);
        closed_heavy_apps(&ob.discharge, &mut found);
        assert!(found.is_empty(), "{what}: {found:?}");
        let (goal, discharge, leaves) = (ob.goal, ob.discharge, ob.leaves);
        let (unaudited, admitted) = run_recheck_thread("strength-route-axioms", move || {
            let mut env = strength::strength_env(&leaves).expect("strength env");
            let audited: HashSet<Name> =
                strength::audited().into_iter().map(Name::from_string).collect();
            let mut used = HashSet::new();
            discharge.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
            goal.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
            let mut unaudited: Vec<String> = used
                .iter()
                .filter(|c| {
                    env.get_const(c).is_none_or(|info| info.kind == ConstantKind::Theorem)
                        && !audited.contains(*c)
                })
                .map(ToString::to_string)
                .collect();
            unaudited.sort();
            (unaudited, strength::admit_obligation(&mut env, goal, discharge))
        })
        .expect("kernel thread");
        assert!(unaudited.is_empty(), "{what} names unaudited theorems {unaudited:?}");
        admitted.unwrap_or_else(|e| panic!("{what}: {e}"));
    }
}

/// A pair whose cores meet with no rewrite (here only through the
/// strength-only standalone `ZeroExt` arm) is not this route's: it declines
/// before any kernel check, and the label could name no strength theorem.
#[test]
fn a_pair_with_no_rewrite_is_declined_before_the_kernel() {
    let f = zext(add(var("W0", 32), lit(3, 32), 32), 32);
    assert!(strength_fragment(&f));
    let mut ctx = ReflectCtx::strength();
    let rm = reflect_formula(&f, &mut ctx).expect("reflects");
    let ra = reflect_formula(&f, &mut ctx).expect("reflects");
    assert_eq!((ctx.strength_rewrites, rm.core == ra.core), (0, true));
    let before = kernel_runs();
    assert_eq!(try_strength_discharge(&f, &f, StrengthFilter::On), None);
    assert_eq!(kernel_runs(), before, "a kernel check started");
    assert!(strength_obligation(&f, &f, StrengthFilter::On).is_none());
}

/// `n >= 1` operands, each built by `node`, joined by `^` as a balanced tree
/// (depth `ceil(log2 n)`), so the reflection's recursion stays shallow.
fn xor_tree(n: usize, node: &impl Fn() -> Formula) -> Formula {
    if n == 1 { node() } else { xor(xor_tree(n / 2, node), xor_tree(n - n / 2, node), 64) }
}

/// At most `strength::MAX_REWRITES` steps are spliced. Sixteen shifts by one
/// are all rewritten and the pair is proved; with seventeen the last shift
/// stays a shift, the cores differ, and the route declines before the kernel.
#[test]
fn the_rewrite_cap_holds() {
    let shift = || shl(x64(), lit(1, 64), 64);
    let double = || mul(x64(), lit(2, 64), 64);
    let at_cap = strength::MAX_REWRITES;
    assert_eq!(at_cap, 16);

    let (machine, auto) = (xor_tree(at_cap, &shift), xor_tree(at_cap, &double));
    assert_eq!(
        try_strength_discharge(&machine, &auto, StrengthFilter::On),
        Some(strength::label(&[names::SHL_MUL], 0)),
        "{at_cap} shifts are proved"
    );

    let (machine, auto) = (xor_tree(at_cap + 1, &shift), xor_tree(at_cap + 1, &double));
    assert!(strength_fragment(&machine) && strength_fragment(&auto));
    let mut ctx = ReflectCtx::strength();
    let rm = reflect_formula(&machine, &mut ctx).expect("reflects");
    let ra = reflect_formula(&auto, &mut ctx).expect("reflects");
    assert_eq!(ctx.strength_rewrites, at_cap);
    assert_ne!(rm.core, ra.core, "the last shift is not rewritten");
    let before = kernel_runs();
    assert_eq!(try_strength_discharge(&machine, &auto, StrengthFilter::On), None);
    assert_eq!(kernel_runs(), before, "a kernel check started");
}

/// The pre-filter admits at most `STRENGTH_MAX_NODES` nodes per side, and
/// only the node kinds the strength shapes use.
#[test]
fn the_pre_filter_bounds_size_and_kinds() {
    assert_eq!(STRENGTH_MAX_NODES, 256);
    // `k` leaves joined by `+`: `2k - 1` nodes.
    let sum = |k: usize, w: u32| {
        let leaf = || var("W0", w);
        (1..k).fold(leaf(), |acc, _| add(acc, leaf(), w))
    };
    assert!(strength_fragment(&sum(128, 64)), "255 nodes");
    assert!(strength_fragment(&zext(sum(128, 32), 32)), "256 nodes");
    assert!(!strength_fragment(&sum(129, 64)), "257 nodes");
    let auto = mul(x64(), lit(2, 64), 64);
    let before = kernel_runs();
    assert_eq!(try_strength_discharge(&sum(129, 64), &auto, StrengthFilter::On), None);
    assert_eq!(kernel_runs(), before, "a kernel check started");

    let (a, b) = (|| Box::new(x64()), || Box::new(lit(3, 64)));
    for outside in [
        Formula::BvUDiv(a(), b(), 64),
        Formula::BvAnd(a(), b(), 64),
        Formula::BvLShr(a(), b(), 64),
        Formula::BvAShr(a(), b(), 64),
        Formula::BvExtract { inner: a(), high: 40, low: 8 },
    ] {
        assert!(!strength_fragment(&outside), "{outside:?}");
        assert!(!strength_fragment(&add(outside.clone(), shl(x64(), lit(1, 64), 64), 64)));
    }
    for inside in [s02(), s08_rung(), s09_h(), s09_rung(), s14()] {
        assert!(strength_fragment(&inside.0) && strength_fragment(&inside.1), "{inside:?}");
    }
}

/// `env_of` for [`strength_discharge_in`]: the real per-obligation
/// environment with the theorem `name` replaced by an axiom of the same
/// statement, AFTER the audit ran (the audit cannot see it).
fn axiomatized(leaves: &[(String, u32)], name: &str) -> Result<Environment, String> {
    let mut env = strength::strength_env(leaves)?;
    let n = Name::from_string(name);
    let type_ = env.get_const(&n).ok_or_else(|| format!("{name} is absent"))?.type_.clone();
    if !env.forget_decl(&n) {
        return Err(format!("{name} was not removed"));
    }
    env.add_decl(Declaration::Axiom { name: n, level_params: vec![], type_ })
        .map_err(|e| format!("{e:?}"))?;
    Ok(env)
}
fn shl_mul_axiom(leaves: &[(String, u32)]) -> Result<Environment, String> {
    axiomatized(leaves, names::SHL_MUL)
}
fn bv_mul_val_axiom(leaves: &[(String, u32)]) -> Result<Environment, String> {
    axiomatized(leaves, bvv::BV_MUL_VAL)
}

/// The route's own axiom check, apart from the base audit. With
/// `Trust.BVS.shl_mul`, which the s02 discharge cites, replaced by an axiom,
/// the route declines. With `Trust.BVV.bvMul_val` replaced instead, which the
/// discharge does NOT name but `shl_mul`'s proof cites, the route declines
/// too: the check follows the transitive closure, not the term's surface.
/// The real environment proves the same pair.
#[test]
fn an_axiom_under_the_discharge_makes_the_route_decline() {
    let (machine, auto) = s02();
    let ob = strength_obligation(&machine, &auto, StrengthFilter::On).expect("s02");
    let mut named = HashSet::new();
    ob.discharge.used_constants_dag(UsedConstants::ConstantsOnly, &mut named);
    assert!(named.contains(&Name::from_string(names::SHL_MUL)), "cited directly");
    assert!(!named.contains(&Name::from_string(bvv::BV_MUL_VAL)), "cited only beneath");
    assert_eq!(strength_discharge_in(&machine, &auto, StrengthFilter::On, shl_mul_axiom), None);
    assert_eq!(
        strength_discharge_in(&machine, &auto, StrengthFilter::On, bv_mul_val_axiom),
        None,
        "an axiom beneath a cited theorem"
    );
    assert!(
        strength_discharge_in(&machine, &auto, StrengthFilter::On, strength::strength_env)
            .is_some(),
        "the real environment proves it"
    );
}

/// T-U8. UBFIZ (`ubfiz x0, x0, #1, #8`, rendered
/// `Shl(ZeroExt(Extract(x, 7, 0), 56), 1)`) is not the `lsl #1` alias: the
/// zero-extension (56) is not the shift (1), so `shl_hi_out` declines in Rust
/// and the route declines before the kernel. The alias itself is accepted.
#[test]
fn ubfiz_is_declined_in_rust() {
    let operand = |high, k| zext(extract(x64(), high), k);
    let core =
        |f: &Formula| reflect_formula(f, &mut ReflectCtx::strength()).expect("reflects").core;
    let one = core(&lit(1, 64));
    assert!(strength::shl_hi_out_step(&core(&operand(7, 56)), &one).is_none());
    assert!(strength::shl_hi_out_step(&core(&operand(62, 1)), &one).is_some());
    let before = kernel_runs();
    let machine = shl(operand(7, 56), lit(1, 64), 64);
    for auto in [mul(operand(7, 56), lit(2, 64), 64), mul(x64(), lit(2, 64), 64)] {
        assert_eq!(try_strength_discharge(&machine, &auto, StrengthFilter::On), None);
    }
    assert_eq!(kernel_runs(), before, "a kernel check started");
}

/// The value of `f` with `X0 = x0`, computed in Rust: `(value, width)`.
fn eval(f: &Formula, x0: u64) -> (u128, u32) {
    let mask = |v: u128, w: u32| if w >= 128 { v } else { v & ((1u128 << w) - 1) };
    match f {
        Formula::Var(name, Sort::BitVec(64)) if name == "X0" => (u128::from(x0), 64),
        Formula::BitVec { value, width } => (mask(*value as u128, *width), *width),
        Formula::BvAdd(l, r, w) => (mask(eval(l, x0).0.wrapping_add(eval(r, x0).0), *w), *w),
        Formula::BvSub(l, r, w) => (mask(eval(l, x0).0.wrapping_sub(eval(r, x0).0), *w), *w),
        Formula::BvOr(l, r, w) => (eval(l, x0).0 | eval(r, x0).0, *w),
        Formula::BvXor(l, r, w) => (eval(l, x0).0 ^ eval(r, x0).0, *w),
        Formula::BvZeroExt(x, k) => {
            let (v, w) = eval(x, x0);
            (v, w + k)
        }
        Formula::BvExtract { inner, high, low } => {
            let (v, _) = eval(inner, x0);
            (mask(v >> low, high - low + 1), high - low + 1)
        }
        other => panic!("not evaluated here: {other:?}"),
    }
}

/// `f` with the variable `X0` replaced by the constant `x0`.
fn substitute(f: &Formula, x0: u64) -> Formula {
    let s = |g: &Formula| Box::new(substitute(g, x0));
    match f {
        Formula::Var(name, Sort::BitVec(64)) if name == "X0" => lit(i128::from(x0), 64),
        Formula::BvAdd(l, r, w) => Formula::BvAdd(s(l), s(r), *w),
        Formula::BvSub(l, r, w) => Formula::BvSub(s(l), s(r), *w),
        Formula::BvOr(l, r, w) => Formula::BvOr(s(l), s(r), *w),
        Formula::BvXor(l, r, w) => Formula::BvXor(s(l), s(r), *w),
        Formula::BvZeroExt(x, k) => Formula::BvZeroExt(s(x), *k),
        Formula::BvExtract { inner, high, low } => {
            Formula::BvExtract { inner: s(inner), high: *high, low: *low }
        }
        other => other.clone(),
    }
}

/// T-U9. The new `ZeroExt` arm, and the strength forms of the Or-zero,
/// Add-zero and Extract-over-ZeroExt wrappers, are faithful: at concrete
/// inputs the kernel computes `bvfEval` of the reflected goal (and of its
/// core) to exactly the value Rust computes for the Formula. The Formulas are
/// the s14 UBFM operand and the s09 `rung` wrappers around their arithmetic.
/// The multiply and the shift are left out: computing them on closed 64-bit
/// data is exactly what the kernel must never be asked to do (`bvShl` and
/// `bvMul` unfold to `natToBvAux` and `%` on closed numbers), and they are
/// not part of the arm under test.
#[test]
fn zero_extension_reflection_is_faithful() {
    let w = || or(lit(0, 32), x32(), 32);
    let formulas = [
        zext(extract(x64(), 62), 1),
        or(lit(0, 64), zext(sub(add(lit(3, 32), w(), 32), w(), 32), 32), 64),
        zext(add(x32(), lit(3, 32), 32), 32),
        extract(zext(add(x32(), lit(3, 32), 32), 32), 31),
        add(lit(0, 64), zext(x32(), 32), 64),
        xor(add(x64(), lit(1, 64), 64), zext(extract(x64(), 62), 1), 64),
    ];
    let inputs = [0, 1, 1 << 31, 1 << 63, u64::MAX];
    let mut checks = Vec::new();
    for f in &formulas {
        for &x0 in &inputs {
            let g = substitute(f, x0);
            let (value, width) = eval(f, x0);
            let mut ctx = ReflectCtx::strength();
            let r = reflect_formula(&g, &mut ctx).expect("reflects");
            assert!(ctx.leaves.is_empty());
            let expected = kx::bits(value as i128, width);
            for side in [r.bvf.clone(), r.core.clone()] {
                checks.push((
                    format!("{f:?} at {x0:#x}"),
                    kx::eq_refl_list(expected.clone()),
                    kx::eq_list(kx::evalf(side), expected.clone()),
                ));
            }
            checks.push((
                format!("{f:?} proof at {x0:#x}"),
                r.proof,
                kx::eq_list(kx::evalf(r.bvf), kx::evalf(r.core)),
            ));
        }
    }
    let failures = run_recheck_thread("strength-route-faithful", move || {
        let env = strength::strength_env(&[]).expect("strength env");
        let tc = TypeChecker::with_mode(&env, env.mode());
        checks
            .into_iter()
            .filter_map(|(what, val, ty)| {
                tc.check_type(&val, &ty).err().map(|e| format!("{what}: {e:?}"))
            })
            .collect::<Vec<_>>()
    })
    .expect("kernel thread");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// T-U10. The goal does not depend on the matcher: under strength, the
/// `bvf` of each side is byte-identical with the step builders on and off,
/// on every positive and negative case, while the cores differ wherever a
/// step was spliced.
#[test]
fn the_goal_does_not_depend_on_the_step_builders() {
    let mut pairs: Vec<(String, Formula, Formula)> =
        positives().into_iter().map(|(w, m, a, _)| (w.to_string(), m, a)).collect();
    let (s02_m, _) = s02();
    pairs.push(("s02 wrong".into(), s02_m, add(mul(x64(), lit(3, 64), 64), lit(8, 64), 64)));
    pairs.push((
        "extract over zext".into(),
        extract(zext(add(x32(), shl(x32(), lit(1, 32), 32), 32), 32), 31),
        mul(x32(), lit(3, 32), 32),
    ));
    for (what, machine, auto) in &pairs {
        for f in [machine, auto] {
            let mut on = ReflectCtx::strength();
            let mut dry = ReflectCtx::strength_dry();
            let a = reflect_formula(f, &mut on).expect("reflects");
            let b = reflect_formula(f, &mut dry).expect("reflects");
            assert_eq!(format!("{:?}", a.bvf), format!("{:?}", b.bvf), "{what}: {f:?}");
            assert_eq!(dry.strength_rewrites, 0);
            assert_eq!(a.core != b.core, on.strength_rewrites > 0, "{what}: {f:?}");
        }
        let mut on = ReflectCtx::strength();
        reflect_formula(machine, &mut on).expect("reflects");
        assert!(on.strength_rewrites > 0, "{what}: the machine side was not rewritten");
    }
}

/// T-U12. b4 controls: `X0 + X1` against `X1 + X0` is not this route's (no
/// step applies), at 32 and 64 bits, and it declines before the kernel.
#[test]
fn a_plain_commuted_add_is_declined() {
    let before = kernel_runs();
    for w in [32, 64] {
        let (a, b) = (var("X0", w), var("X1", w));
        let machine = add(a.clone(), b.clone(), w);
        let auto = add(b, a, w);
        assert_eq!(try_strength_discharge(&machine, &auto, StrengthFilter::On), None);
        assert_eq!(try_o1_instantiation_discharge(&machine, &auto), None);
    }
    assert_eq!(kernel_runs(), before, "a strength kernel check started");
}

/// `n >= 1` operands, each built by `node`, joined by `w`-bit `^` nested to the
/// left (depth `n`), the shape whose reflection recursed past a small stack.
fn xor_chain(n: usize, w: u32, node: &impl Fn() -> Formula) -> Formula {
    (1..n).fold(node(), |chain, _| xor(chain, node(), w))
}

/// Run `route` on a thread with a 2 MiB stack, as a test or a small compiler
/// thread would. An overflow there aborts the whole test process.
fn on_small_stack<T: Send + 'static>(route: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(route)
        .expect("spawn a 2 MiB thread")
        .join()
        .expect("the route did not panic")
}

/// The routes reflect on a stack grown on the calling thread, not on the
/// caller's own. Measured before that in a debug build: sixteen left-nested
/// `x << 1` operands against `x * 2` overflowed a 2 MiB caller in the commuted
/// retry and aborted the process. Now the same pair is proved by the strength
/// route, a 64-deep pair of one Formula by the shared core, and a 64-deep
/// chain of caller-memory reads by the memory route.
#[test]
fn a_deep_formula_is_reflected_off_the_callers_stack() {
    let shift = || shl(x64(), lit(1, 64), 64);
    let double = || mul(x64(), lit(2, 64), 64);
    let at_cap = strength::MAX_REWRITES;
    let (machine, auto) = (xor_chain(at_cap, 64, &shift), xor_chain(at_cap, 64, &double));
    assert_eq!(
        on_small_stack(move || try_o1_instantiation_discharge(&machine, &auto)),
        Some(strength::label(&[names::SHL_MUL], 0)),
        "{at_cap} left-nested shifts are proved"
    );

    let deep = xor_chain(64, 64, &shift);
    let same = deep.clone();
    assert!(
        on_small_stack(move || try_o1_instantiation_discharge(&deep, &same)).is_some(),
        "a 64-deep Formula equals itself"
    );

    let mem = || {
        Formula::Var(
            "MEM".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        )
    };
    let read = || Formula::Select(Box::new(mem()), Box::new(var("P", 64)));
    let reads = xor_chain(64, 8, &read);
    let same = reads.clone();
    assert!(
        on_small_stack(move || try_mem_store_load_discharge(&reads, &same)).is_some(),
        "64 left-nested reads equal themselves"
    );
}

/// The stack is switched, not the thread: a test hook a caller sets is still
/// seen by the route. Under `without_production` the original-conjunction
/// route's production guard still fires on the caller.
#[test]
fn the_route_stack_keeps_the_callers_thread_locals() {
    let items = vec![(x64(), x64())];
    let fired = std::panic::catch_unwind(|| {
        crate::original_conjunction_certificate::without_production(|| {
            try_original_conjunction_discharge(&items)
        })
    });
    assert!(fired.is_err(), "the production guard did not fire under without_production");

    let (machine, auto) = s02();
    let before = kernel_runs();
    assert!(try_o1_instantiation_discharge(&machine, &auto).is_some());
    assert_eq!(kernel_runs(), before + 1, "the strength kernel run was not counted here");
}
