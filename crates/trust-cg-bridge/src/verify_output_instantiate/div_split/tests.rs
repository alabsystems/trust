// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::time::{Duration, Instant};

use clean_kernel::{Expr, ExprKind, TypeChecker};
use trust_types::{Formula, Sort};

use super::super::branch_split::{self, BranchFilter, Decline};
use super::super::kterm::{eq, lb, refl};
use super::super::{ReflectCtx, branch_dispatch, branch_theory, kx, reflect_formula};
use super::{
    DECLARED, LABEL_TAIL, MUTANT, Mutant, goal_of, has_symbolic_divisor, in_walk, kernel_check,
    prove, try_conjunction, walk_view,
};
use crate::verify_output::{Discharge, ProvenEvidence, discharge_valid};

type Items = Vec<(Formula, Formula)>;

fn var(name: &str, w: u32) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(w))
}
fn lit(value: i128, width: u32) -> Formula {
    Formula::BitVec { value, width }
}
fn x64() -> Formula {
    var("X0", 64)
}
fn bx(f: Formula) -> Box<Formula> {
    Box::new(f)
}
fn ult(a: Formula, b: Formula, w: u32) -> Formula {
    Formula::BvULt(bx(a), bx(b), w)
}
fn ite(c: Formula, a: Formula, e: Formula) -> Formula {
    Formula::Ite(bx(c), bx(a), bx(e))
}
fn feq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(bx(a), bx(b))
}
fn udiv(a: Formula, b: Formula) -> Formula {
    Formula::BvUDiv(bx(a), bx(b), 64)
}
fn or0(a: Formula) -> Formula {
    Formula::BvOr(bx(lit(0, 64)), bx(a), 64)
}
/// The machine's `UDIV` model: `ite(b == 0, 0, a / b)`.
fn machine_udiv(a: Formula, b: Formula) -> Formula {
    ite(feq(b.clone(), lit(0, 64)), lit(0, 64), udiv(a, b))
}

const WALK_DECLINE: &str = "branch: a side is outside the width walk";
const DIV_WALK_DECLINE: &str = "div: a side is outside the width walk";
const ARMS_DIFFER: &str = "div: the arms of a case differ";

/// The filters' decline at a leaf whose arms differ.
fn arms_differ(r: &Result<ProvenEvidence, Decline>) -> bool {
    matches!(r, Err(Decline::Filter(m)) if m == ARMS_DIFFER)
}

fn fnv1a(s: &str) -> u64 {
    s.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
}

/// Does `t` occur in `e` (through applications)?
fn occurs(e: &Expr, t: &Expr) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![e.clone()];
    while let Some(x) = stack.pop() {
        if x == *t {
            return true;
        }
        if let ExprKind::App(f, a) = x.kind() {
            for y in [Expr::clone(f), Expr::clone(a)] {
                if seen.insert(y.clone()) {
                    stack.push(y);
                }
            }
        }
    }
    false
}

/// The kernel's `add_decl` type check refused the discharge.
fn kernel_refused(r: &Result<ProvenEvidence, Decline>) -> bool {
    matches!(r, Err(Decline::Kernel(m)) if m.starts_with("kernel: TypeCheckFailed"))
}

fn is_div_label(e: &ProvenEvidence) -> bool {
    matches!(e, ProvenEvidence::KernelInstantiated { theorem, original: None }
        if theorem.ends_with(LABEL_TAIL) && !theorem.contains("BRANCH-SPLIT-1"))
}

fn label_of(e: &ProvenEvidence) -> &str {
    match e {
        ProvenEvidence::KernelInstantiated { theorem, .. } => theorem,
        other => panic!("not a kernel instantiation: {other:?}"),
    }
}

/// The watchdog every route call in these tests runs under: PANICS if the
/// route (the Rust build and the kernel) has not answered within it.
const LIMIT: Duration = Duration::from_secs(240);

/// `prove(items, filter)` under [`LIMIT`], with `mutant` set on the route's
/// thread.
fn watched(
    what: &str,
    items: &Items,
    filter: BranchFilter,
    mutant: Mutant,
) -> Result<ProvenEvidence, Decline> {
    let items = items.clone();
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .name(format!("div-split-test {what}"))
        .stack_size(64 << 20)
        .spawn(move || {
            MUTANT.with(|m| m.set(mutant));
            let _ = tx.send(prove(&items, filter));
        })
        .expect("spawn");
    rx.recv_timeout(LIMIT)
        .unwrap_or_else(|_| panic!("{what}: the route ran past the {LIMIT:?} watchdog"))
}

// ── the s21 fixtures ─────────────────────────────────────────────────────────

/// s21_div_var (`if x != 0 { 1000 / x } else { 0 }` over `u64`): the
/// step-(5) conjunction the gate reached on aarch64-apple-darwin in the
/// fixture configuration (`tests/div_split_gate.rs`), captured with
/// `TRUST_GATE_TRACE=1` (the branch split's `[branch-split] conj` line,
/// <home>/trust-cp-logs/s3-design/s21-conj.txt). Item 0 is the result,
/// item 1 the (4b) check. O0's machine guard is `subs`/`b.ne`, O2's `cbnz`.
fn s21(opt: &str) -> Items {
    let text = match opt {
        "O0" => include_str!("fixtures/s21_div_var-O0.json"),
        "O2" => include_str!("fixtures/s21_div_var-O2.json"),
        other => panic!("no s21 fixture {other}"),
    };
    serde_json::from_str(text).expect("fixture parses")
}

const OPTS: [&str; 2] = ["O0", "O2"];

fn map_machine(items: &Items, g: &mut dyn FnMut(Formula) -> Formula) -> Items {
    let mut out = items.clone();
    out[0].0 = out[0].0.clone().map(&mut |f| g(f));
    out
}
fn map_spec(items: &Items, g: &mut dyn FnMut(Formula) -> Formula) -> Items {
    let mut out = items.clone();
    out[0].1 = out[0].1.clone().map(&mut |f| g(f));
    out
}

fn is_x(f: &Formula) -> bool {
    matches!(f, Formula::Var(n, Sort::BitVec(64)) if n.as_str() == "X0")
}
fn is_lit(f: &Formula, v: i128) -> bool {
    matches!(f, Formula::BitVec { value, width: 64 } if *value == v)
}
fn is_zero_or(f: &Formula) -> bool {
    matches!(f, Formula::BvOr(a, b, 64) if is_lit(a, 0) && is_lit(b, 0))
}

/// s21 is kernel-[PROVED] by the route at O0 and O2, with this route's
/// label; the branch split declines it at the walk. Prints the label and
/// the time (not a bound).
#[test]
fn s21_is_proved_by_the_div_split() {
    for opt in OPTS {
        let items = s21(opt);
        assert!(has_symbolic_divisor(&items), "{opt}");
        assert_eq!(
            branch_split::prove(&items, BranchFilter::On),
            Err(Decline::Filter(WALK_DECLINE.into())),
            "{opt}: the branch split"
        );
        let t = Instant::now();
        let got = watched(opt, &items, BranchFilter::On, Mutant::None);
        let ms = t.elapsed().as_millis();
        let e = got.unwrap_or_else(|d| panic!("{opt}: declined: {d:?}"));
        assert!(is_div_label(&e), "{opt}: {e:?}");
        println!("s21 {opt}: {ms} ms: {}", label_of(&e));
        assert_eq!(try_conjunction(&items), Some(e), "{opt}: the production entry");
    }
}

/// The declared type is G, built from the original items alone; and G is
/// not just whatever `goal_of` builds: on s21 it states the division by the
/// frozen faithful arm (the goal reflection of `1000 / X0`, with its
/// `bvIsZero` guard on X0, occurs in it), and its bytes are pinned
/// (`DIV_GOAL_PIN`, like the branch split's `BRANCH_GOAL_PIN`). The frozen
/// `branch_split::goal_of` refuses s21 at its walk; where it admits, the two
/// agree (`goal_of_agrees_with_the_branch_split_goal`).
#[test]
fn declared_type_is_the_independent_goal() {
    use std::fmt::Write as _;
    let mut pin = String::new();
    for opt in OPTS {
        let items = s21(opt);
        let (goal, sides, leaves) = goal_of(&items).expect("goal");
        DECLARED.with(|d| *d.borrow_mut() = None);
        prove(&items, BranchFilter::On).expect("proved");
        let declared = DECLARED.with(|d| d.borrow_mut().take()).expect("declared");
        assert_eq!(declared, goal, "{opt}");
        assert_eq!(branch_split::goal_of(&items).err().as_deref(), Some(WALK_DECLINE));
        // The faithful division, reflected on its own under the same context.
        let mut ctx = ReflectCtx::branching_goal();
        let division = reflect_formula(&udiv(lit(1000, 64), x64()), &mut ctx).expect("udiv");
        let quotient = kx::evalf(division.bvf);
        assert!(occurs(&goal, &quotient), "{opt}: G does not state 1000 / X0 faithfully");
        let mut ctx = ReflectCtx::branching_goal();
        let x = kx::evalf(reflect_formula(&x64(), &mut ctx).expect("X0").bvf);
        assert!(occurs(&goal, &kx::bv_is_zero(x)), "{opt}: G has no bvIsZero guard on X0");
        // The walk's view (BvAdd) is never what G states.
        let mut ctx = ReflectCtx::branching_goal();
        let sum = reflect_formula(&walk_view(&udiv(lit(1000, 64), x64())), &mut ctx).expect("add");
        assert!(!occurs(&goal, &kx::evalf(sum.bvf)), "{opt}: G states the walk's view");
        writeln!(pin, "{opt}\n{goal:?}\n{sides:?}\n{leaves:?}").unwrap();
    }
    println!("DIV_GOAL_PIN ({}, {})", pin.len(), fnv1a(&pin));
    assert_eq!((pin.len(), fnv1a(&pin)), (3626700, 10467708134080052093), "DIV_GOAL_PIN");
}

// ── the walk ─────────────────────────────────────────────────────────────────

/// The branch split's corpus (`branch_split/tests.rs` `branch_corpus`).
fn branch_corpus() -> Vec<Formula> {
    let ult = Formula::BvULt(bx(x64()), bx(lit(2, 64)), 64);
    vec![
        Formula::Ite(bx(ult.clone()), bx(lit(10, 64)), bx(x64())),
        Formula::Ite(bx(ult.clone()), bx(Formula::Bool(true)), bx(Formula::Bool(false))),
        Formula::Eq(bx(x64()), bx(lit(0, 64))),
        ult,
        Formula::BvULe(bx(x64()), bx(lit(2, 64)), 64),
        Formula::BvSLt(bx(x64()), bx(lit(2, 64)), 64),
        Formula::BvUDiv(bx(x64()), bx(lit(2, 64)), 64),
        Formula::BvUDiv(bx(x64()), bx(lit(1i128 << 64, 64)), 64),
        Formula::BvAnd(bx(x64()), bx(lit(1, 64)), 64),
        Formula::BvLShr(bx(x64()), bx(lit(1, 64)), 64),
        Formula::BvExtract { inner: bx(x64()), high: 0, low: 0 },
        Formula::BvExtract { inner: bx(x64()), high: 63, low: 1 },
        Formula::BvZeroExt(bx(lit(10, 32)), 32),
    ]
}

/// The branch split's walk refusal battery (`branch_split/tests.rs`
/// `branch_fragment_refusals`), the symbolic divisor left out.
fn refusal_battery() -> Vec<(&'static str, Formula)> {
    let c = ult(x64(), lit(2, 64), 64);
    let it = |a: Formula, b: Formula| ite(c.clone(), a, b);
    let in_cond = |cond: Formula| it(ite(cond, x64(), x64()), x64());
    vec![
        ("signed division", it(Formula::BvSDiv(bx(x64()), bx(lit(2, 64)), 64), x64())),
        ("select", it(Formula::Select(bx(x64()), bx(x64())), x64())),
        ("concat", it(Formula::BvConcat(bx(lit(0, 32)), bx(lit(0, 32))), x64())),
        ("128-bit literal", it(lit(1, 128), lit(1, 128))),
        ("mixed-width arms", it(lit(1, 64), lit(1, 32))),
        ("empty And", in_cond(Formula::And(vec![]))),
        ("Eq of a Bool and a bit-vector", in_cond(feq(Formula::Bool(true), x64()))),
        ("Eq of a bit-vector and a Bool", in_cond(feq(x64(), c.clone()))),
        ("AShr by a variable", it(Formula::BvAShr(bx(x64()), bx(x64()), 64), x64())),
        ("AShr by the width", it(Formula::BvAShr(bx(x64()), bx(lit(64, 64)), 64), x64())),
        (
            "AShr by a closed amount past the width",
            it(
                Formula::BvAShr(
                    bx(x64()),
                    bx(Formula::BvAnd(bx(lit(200, 64)), bx(lit(127, 64)), 64)),
                    64,
                ),
                x64(),
            ),
        ),
        ("AShr amount of another width", it(Formula::BvAShr(bx(x64()), bx(lit(2, 32)), 64), x64())),
        (
            "SignExt of a variable",
            it(
                Formula::BvSignExt(
                    bx(Formula::BvExtract { inner: bx(x64()), high: 31, low: 0 }),
                    32,
                ),
                x64(),
            ),
        ),
        (
            "SignExt past 64 bits",
            in_cond(feq(
                Formula::BvSignExt(bx(lit(1, 32)), 33),
                Formula::BvSignExt(bx(lit(1, 32)), 33),
            )),
        ),
        ("Eq of widths 64 and 32", in_cond(feq(x64(), lit(0, 32)))),
        ("ULt of widths 64 and 32", in_cond(ult(x64(), lit(2, 32), 64))),
        ("ULt declared at 32 over 64", in_cond(ult(x64(), lit(2, 64), 32))),
        ("ULe of widths 64 and 32", in_cond(Formula::BvULe(bx(x64()), bx(lit(2, 32)), 64))),
        ("SLt declared at 32 over 64", in_cond(Formula::BvSLt(bx(x64()), bx(lit(2, 64)), 32))),
        ("Extract{1,1}", it(Formula::BvExtract { inner: bx(x64()), high: 1, low: 1 }, lit(0, 1))),
        ("ZeroExt past 64", it(Formula::BvZeroExt(bx(x64()), 1), x64())),
        ("BvNot", it(Formula::BvNot(bx(x64()), 64), x64())),
        ("BvSLe", in_cond(Formula::BvSLe(bx(x64()), bx(lit(2, 64)), 64))),
        ("nine-way And", in_cond(Formula::And(vec![c.clone(); 9]))),
        // Inside the walk (positives of the same battery).
        ("plain", it(x64(), lit(1, 64))),
        ("eight-way And", in_cond(Formula::And(vec![c.clone(); 8]))),
        ("Bool equality", in_cond(feq(Formula::Bool(true), c.clone()))),
        ("AShr below the width", it(Formula::BvAShr(bx(x64()), bx(lit(63, 64)), 64), x64())),
        ("closed SignExt", it(Formula::BvSignExt(bx(lit(2, 32)), 32), x64())),
    ]
}

/// The captured branch fixtures (`branch_split/fixtures`).
fn branch_fixtures() -> Vec<(&'static str, Items)> {
    let parse = |t: &str| -> Items { serde_json::from_str(t).expect("fixture parses") };
    vec![
        (
            "s04 O0",
            parse(include_str!("../branch_split/fixtures/s04_if-O0-aarch64-apple-darwin.json")),
        ),
        (
            "s05 O0",
            parse(include_str!(
                "../branch_split/fixtures/s05_if_chain-O0-aarch64-apple-darwin.json"
            )),
        ),
        (
            "s05 O2",
            parse(include_str!(
                "../branch_split/fixtures/s05_if_chain-O2-aarch64-apple-darwin.json"
            )),
        ),
        (
            "r02 O0",
            parse(include_str!("../branch_split/fixtures/r02_branch-O0-aarch64-apple-darwin.json")),
        ),
        (
            "r02 O2",
            parse(include_str!("../branch_split/fixtures/r02_branch-O2-aarch64-apple-darwin.json")),
        ),
        (
            "s07 O0",
            parse(include_str!(
                "../branch_split/fixtures/s07_local_call-O0-aarch64-apple-darwin.json"
            )),
        ),
    ]
}

/// The frozen walk as `goal_of` applies it: `true` unless it refuses at the
/// walk.
fn branch_walk(items: &Items) -> bool {
    branch_split::goal_of(items).err().as_deref() != Some(WALK_DECLINE)
}

/// Without a symbolic divisor `walk_view` is the identity and [`in_walk`]
/// agrees with `branch_split::goal_of`'s walk on the branch corpus (each
/// formula against itself and every pair), the walk's refusal battery and
/// the captured fixtures. With one, it admits exactly the divisions
/// `goal_of` refused for a variable and nothing else of the battery.
#[test]
fn div_walk_agrees_with_goal_of_without_symbolic_divisors() {
    let mut n = 0;
    let corpus = branch_corpus();
    for f in &corpus {
        for g in &corpus {
            let items = vec![(f.clone(), g.clone())];
            assert!(!has_symbolic_divisor(&items));
            assert_eq!(walk_view(f), *f);
            assert_eq!(in_walk(&items), branch_walk(&items), "{f:?} = {g:?}");
            n += 1;
        }
    }
    for (what, f) in refusal_battery() {
        let items = vec![(f.clone(), f)];
        assert_eq!(in_walk(&items), branch_walk(&items), "{what}");
        n += 1;
    }
    for (what, items) in branch_fixtures() {
        assert!(!has_symbolic_divisor(&items), "{what}");
        assert_eq!(in_walk(&items), branch_walk(&items), "{what}");
        assert!(in_walk(&items), "{what}");
        n += 1;
    }
    // Symbolic divisors: admitted at one width, refused otherwise.
    let c = ult(x64(), lit(2, 64), 64);
    let admitted = [
        udiv(lit(1000, 64), x64()),
        udiv(x64(), x64()),
        ite(c.clone(), udiv(x64(), Formula::BvAdd(bx(x64()), bx(lit(1, 64)), 64)), x64()),
        udiv(udiv(lit(7, 64), x64()), x64()),
    ];
    for f in admitted {
        let items = vec![(f.clone(), f.clone())];
        assert!(has_symbolic_divisor(&items), "{f:?}");
        assert!(!branch_walk(&items), "{f:?}: the branch walk admits it");
        assert!(in_walk(&items), "{f:?}");
    }
    let x32 = var("Y", 32);
    let refused = [
        ("divisor of another width", Formula::BvUDiv(bx(x64()), bx(x32.clone()), 64)),
        ("declared width differs", Formula::BvUDiv(bx(x64()), bx(x64()), 32)),
        ("signed division by a variable", Formula::BvSDiv(bx(x64()), bx(x64()), 64)),
        ("remainder by a variable", Formula::BvURem(bx(x64()), bx(x64()), 64)),
        ("divisor outside the walk", udiv(x64(), Formula::BvNot(bx(x64()), 64))),
        ("dividend outside the walk", udiv(Formula::BvNot(bx(x64()), 64), x64())),
        (
            "AShr by a symbolic quotient",
            Formula::BvAShr(bx(x64()), bx(udiv(lit(7, 64), x64())), 64),
        ),
    ];
    for (what, f) in refused {
        let items = vec![(f.clone(), f.clone())];
        assert!(!in_walk(&items), "{what}");
        for filter in [BranchFilter::On, BranchFilter::Off] {
            assert_eq!(
                prove(&items, filter),
                Err(Decline::Filter(DIV_WALK_DECLINE.into())),
                "{what}, {filter:?}"
            );
        }
    }
    // A Bool-sorted item is not a bit-vector equation, whatever its
    // divisions.
    let b = feq(udiv(lit(7, 64), x64()), lit(0, 64));
    assert!(!in_walk(&vec![(b.clone(), b)]));
    println!("div walk agreement: {n} cases");
}

/// The copied goal loop is the frozen one: on every case of the walk
/// agreement (no symbolic divisor) `div_split::goal_of` equals
/// `branch_split::goal_of` in all three components where that one admits,
/// refuses at the walk where that one does, and gives the same reflection
/// error otherwise.
#[test]
fn goal_of_agrees_with_the_branch_split_goal() {
    let mut cases: Vec<(String, Items)> = Vec::new();
    let corpus = branch_corpus();
    for f in &corpus {
        for g in &corpus {
            cases.push((format!("{f:?} = {g:?}"), vec![(f.clone(), g.clone())]));
        }
    }
    for (what, f) in refusal_battery() {
        cases.push((what.into(), vec![(f.clone(), f)]));
    }
    for (what, items) in branch_fixtures() {
        cases.push((what.into(), items));
    }
    let (mut admitted, mut walk, mut other) = (0, 0, 0);
    for (what, items) in &cases {
        assert!(!has_symbolic_divisor(items), "{what}");
        match (branch_split::goal_of(items), goal_of(items)) {
            (Ok(b), Ok(d)) => {
                assert_eq!(d, b, "{what}");
                admitted += 1;
            }
            (Err(b), Err(d)) if b == WALK_DECLINE => {
                assert_eq!(d, DIV_WALK_DECLINE, "{what}");
                walk += 1;
            }
            (Err(b), Err(d)) => {
                assert_eq!(d, b, "{what}");
                other += 1;
            }
            (b, d) => panic!("{what}: the branch split {:?}, the div split {:?}", b.err(), d.err()),
        }
    }
    assert!(admitted > 0 && walk > 0, "{admitted} {walk} {other}");
    println!(
        "goal agreement: {} cases, {admitted} admitted, {walk} refused at the walk, {other} other",
        cases.len()
    );
}

#[test]
fn the_pre_filter_reads_divisors_only() {
    let s = |l: Formula, r: Formula| has_symbolic_divisor(&vec![(l, r)]);
    assert!(s(udiv(lit(1, 64), x64()), lit(0, 64)));
    assert!(s(lit(0, 64), udiv(lit(1, 64), x64())));
    assert!(s(udiv(lit(1, 64), Formula::BvAdd(bx(x64()), bx(lit(1, 64)), 64)), lit(0, 64)));
    assert!(!s(udiv(x64(), lit(3, 64)), lit(0, 64)), "a variable dividend only");
    assert!(!s(udiv(x64(), Formula::BvAnd(bx(lit(6, 64)), bx(lit(9, 64)), 64)), x64()));
    assert!(!s(Formula::BvSDiv(bx(x64()), bx(x64()), 64), x64()), "signed division");
    assert!(!s(Formula::BvURem(bx(x64()), bx(x64()), 64), x64()), "remainder");
}

/// The pre-filter is load-bearing for the route's scope: a division-free
/// conjunction the deep split proves (a guard inside a `mov` wrapper's core,
/// as s21's machine has, with the division replaced by `x + 5`) is declined
/// by the branch split, and the production entry does not try it.
#[test]
fn a_division_free_deep_guard_is_out_of_scope() {
    let guard = feq(x64(), lit(0, 64));
    let plus5 = Formula::BvAdd(bx(x64()), bx(lit(5, 64)), 64);
    let items =
        vec![(or0(ite(guard.clone(), lit(0, 64), plus5.clone())), ite(guard, lit(0, 64), plus5))];
    assert!(!has_symbolic_divisor(&items));
    assert!(branch_split::prove(&items, BranchFilter::On).is_err(), "the branch split proves it");
    let deep = watched("division-free", &items, BranchFilter::On, Mutant::None);
    assert!(matches!(&deep, Ok(e) if is_div_label(e)), "the deep split: {deep:?}");
    assert_eq!(try_conjunction(&items), None, "the production entry tried it");
    assert_eq!(branch_dispatch::try_conjunction(&items), None, "the dispatch tried it");
}

// ── mutants (design §2.5), the Rust checks bypassed ──────────────────────────

/// Mutants 1-7: each refused by the KERNEL with the filters Off (3, signed
/// division, by the walk), and each declined with the filters On. Each runs
/// under the watchdog.
#[test]
fn mutants_are_refused_by_the_kernel() {
    let mut seen = Vec::new();
    for opt in OPTS {
        let items = s21(opt);
        let swap_machine_guard = |f: Formula| match f {
            Formula::Ite(c, a, e) if is_zero_or(&e) => Formula::Ite(c, e, a),
            f => f,
        };
        let swap_spec_guard = |f: Formula| match f {
            Formula::Ite(c, a, e) if matches!(*a, Formula::BvUDiv(..)) => Formula::Ite(c, e, a),
            f => f,
        };
        let spec_div = |g: &dyn Fn(Box<Formula>, Box<Formula>) -> Formula| {
            map_spec(&items, &mut |f| match f {
                Formula::BvUDiv(a, b, 64) => g(a, b),
                f => f,
            })
        };
        let machine_guard_one = map_machine(&items, &mut |f| match f {
            Formula::Ite(c, z, d)
                if matches!(*d, Formula::BvUDiv(..))
                    && matches!(&*c, Formula::Eq(x, k) if is_x(x) && is_lit(k, 0)) =>
            {
                Formula::Ite(bx(feq(x64(), lit(1, 64))), z, d)
            }
            f => f,
        });
        let cases: Vec<(&str, Items)> = vec![
            ("1a machine guard flipped", map_machine(&items, &mut |f| swap_machine_guard(f))),
            ("1b spec guard flipped", map_spec(&items, &mut |f| swap_spec_guard(f))),
            ("2a divisor swapped", spec_div(&|a, b| Formula::BvUDiv(b, a, 64))),
            ("2b dividend 1001", spec_div(&|_, b| Formula::BvUDiv(bx(lit(1001, 64)), b, 64))),
            ("6 machine guard x == 1", machine_guard_one),
        ];
        for (what, m) in &cases {
            assert_ne!(m, &items, "{opt} {what}: the mutation did not apply");
            let on = watched(what, m, BranchFilter::On, Mutant::None);
            assert!(arms_differ(&on), "{opt} {what}: with the filters on: {on:?}");
            let off = watched(what, m, BranchFilter::Off, Mutant::None);
            assert!(kernel_refused(&off), "{opt} {what}: filters off: {off:?}");
            seen.push(format!("{opt} {what}: on {on:?}"));
        }
        // 3: udiv -> sdiv is outside the walk: no G is stated.
        let sdiv = spec_div(&|a, b| Formula::BvSDiv(a, b, 64));
        for filter in [BranchFilter::On, BranchFilter::Off] {
            assert_eq!(
                watched("3 sdiv", &sdiv, filter, Mutant::None),
                Err(Decline::Filter(DIV_WALK_DECLINE.into())),
                "{opt} 3 sdiv {filter:?}"
            );
        }
        // 4: the deep abstraction writes a wrong value; the motive keeps the
        // right one.
        for filter in [BranchFilter::On, BranchFilter::Off] {
            let r = watched("4 deep", &items, filter, Mutant::DeepWrong);
            match filter {
                BranchFilter::Off => assert!(kernel_refused(&r), "{opt} 4 deep, off: {r:?}"),
                BranchFilter::On => assert!(arms_differ(&r), "{opt} 4 deep, on: {r:?}"),
            }
            seen.push(format!("{opt} 4 deep {filter:?}: {r:?}"));
        }
    }
    // 5: a wrong leaf comparison passes a leaf whose arms differ; the kernel
    // refuses it. The machine's guard in a core decides 0 at x == 0, the spec
    // divides there (all-ones): a false obligation.
    let d = udiv(lit(1000, 64), x64());
    let guard = feq(x64(), lit(0, 64));
    let five = vec![(or0(machine_udiv(lit(1000, 64), x64())), ite(guard, d.clone(), d.clone()))];
    let control = watched("5 control", &five, BranchFilter::On, Mutant::None);
    assert!(arms_differ(&control), "5: the correct comparison declines: {control:?}");
    let r = watched("5 norm", &five, BranchFilter::On, Mutant::NormElse);
    assert!(kernel_refused(&r), "5 norm else-arm: {r:?}");
    seen.push(format!("5 norm: {r:?}"));
    // 7: an unguarded faithful U against the machine's guarded division: the
    // atom `bvBeq X 0` never stands in for `bvIsZero X`.
    let seven = vec![(machine_udiv(lit(1000, 64), x64()), d)];
    let on = watched("7", &seven, BranchFilter::On, Mutant::None);
    assert!(arms_differ(&on), "7 on: {on:?}");
    let off = watched("7", &seven, BranchFilter::Off, Mutant::None);
    assert!(kernel_refused(&off), "7 off: {off:?}");
    seen.push(format!("7: on {on:?}"));
    println!("{seen:#?}");
}

/// PRECISION: the machine's zero arm changed (`ite(x == 0, 1, U)`) is an
/// equivalent mutant at s21 (the source guard prunes that arm); the route
/// proves it.
#[test]
fn a_pruned_zero_arm_is_an_equivalent_twin_the_route_proves() {
    for opt in OPTS {
        let items = map_machine(&s21(opt), &mut |f| match f {
            Formula::Ite(c, z, d) if matches!(*d, Formula::BvUDiv(..)) && is_lit(&z, 0) => {
                Formula::Ite(c, bx(lit(1, 64)), d)
            }
            f => f,
        });
        assert_ne!(items, s21(opt));
        let r = watched("zero arm 1", &items, BranchFilter::On, Mutant::None);
        assert!(matches!(&r, Ok(e) if is_div_label(e)), "{opt}: {r:?}");
    }
}

// ── the dispatch ─────────────────────────────────────────────────────────────

/// The branch split keeps what it proves (its label), and the division split
/// answers where it declines. The ORDER is not observable in a result: the
/// two routes admit disjoint conjunctions (the branch split's walk refuses
/// every symbolic divisor, `div_walk_agrees_with_goal_of_without_symbolic_divisors`,
/// and the division split runs only with one), so a reversed dispatch gives
/// the same answers; it would only try the cheaper pre-filter first. What is
/// load-bearing is the fallback, which this test and the gate fail without.
#[test]
fn the_dispatch_keeps_the_branch_split_and_falls_back_to_the_div_split() {
    let (_, s05) = branch_fixtures().swap_remove(2);
    let e = branch_dispatch::try_conjunction(&s05).expect("s05");
    assert!(label_of(&e).ends_with(branch_theory::LABEL_TAIL), "{e:?}");
    assert_eq!(Some(e), branch_split::try_branch_split_conjunction(&s05));
    assert_eq!(try_conjunction(&s05), None, "the division split is not tried on s05");
    for opt in OPTS {
        let items = s21(opt);
        assert_eq!(branch_split::try_branch_split_conjunction(&items), None, "{opt}");
        let e = branch_dispatch::try_conjunction(&items).expect("s21");
        assert!(is_div_label(&e), "{opt}: {e:?}");
    }
}

// ── the goal's division arm against SMT-LIB ──────────────────────────────────

/// The goal reflection of `a / b` at width 64 computes SMT `bvudiv` (and
/// all-ones at a zero divisor) on non-power-of-two pairs: the kernel
/// accepts `Eq.refl` of the value and refuses it with its low bit flipped;
/// ay agrees on the same claims. On the route's kernel pool.
#[test]
fn goal_udiv_agrees_with_smt_on_non_power_of_two_pairs() {
    let max64 = u64::MAX as u128;
    let max32 = u32::MAX as u128;
    // (dividend, divisor, width). The 32-bit zero divisors check the arm's
    // all-ones at a width other than 64 (the remainder composite multiplies
    // the quotient by 0 there, so S3c's 32-bit pairs never see it).
    let pairs: [(u128, u128, u32); 8] = [
        (1000, 7, 64),
        (max64, 0x1234567, 64),
        (1000, 0, 64),
        (7, 1000, 64),
        (max64, 3, 64),
        (0x1234_5678_9abc, 0x10001, 64),
        (max32, 0, 32),
        (7, 0, 32),
    ];
    for (a, b, w) in pairs {
        let max = if w == 64 { max64 } else { (1u128 << w) - 1 };
        let want = if b == 0 { max } else { a / b };
        let udiv_w = |l: Formula, r: Formula| Formula::BvUDiv(bx(l), bx(r), w);
        let f = udiv_w(lit(a as i128, w), lit(b as i128, w));
        if w == 64 {
            let symbolic = udiv(lit(a as i128, 64), x64());
            // The walk admits the symbolic form.
            assert!(in_walk(&vec![(symbolic.clone(), symbolic)]));
        }
        let r = kernel_check("div-split-smt", move || {
            let env = branch_theory::branch_base().map_err(Decline::Environment)?.clone();
            let mut ctx = ReflectCtx::branching_goal();
            let stated = kx::evalf(reflect_formula(&f, &mut ctx).map_err(Decline::Filter)?.bvf);
            let check = |v: u128| {
                let good = kx::bits(v as i128, w);
                TypeChecker::with_mode(&env, env.mode())
                    .check_type(&refl(lb(), good.clone()), &eq(lb(), stated.clone(), good))
            };
            Ok((check(want).is_ok(), format!("{:?}", check(want ^ 1))))
        });
        let (good, flipped) = r.unwrap_or_else(|d| panic!("{a} / {b} ({w}): {d:?}"));
        assert!(good, "{a} / {b} ({w}): the kernel did not compute {want}");
        assert!(flipped.starts_with("Err(TypeMismatch"), "{a} / {b} ({w}) flipped: {flipped}");
        let claim = |v: u128| feq(udiv_w(lit(a as i128, w), lit(b as i128, w)), lit(v as i128, w));
        assert!(matches!(discharge_valid(&claim(want)), Discharge::Proven), "ay: {a} / {b} ({w})");
        assert!(
            matches!(discharge_valid(&claim(want ^ 1)), Discharge::CounterExample),
            "ay: {a} / {b} ({w}) flipped"
        );
    }
}

// ── PKG-C5c-S3c: unsigned remainder by a variable ───────────────────────────

/// `if y != 0 { x % y } else { 0 }` over `u64` (`tests/div_split_gate.rs`
/// `REM_IR`, stage-1 trustc 80c41bb667's dump): the step-(5) conjunction the
/// gate reached on aarch64-apple-darwin in the fixture configuration, the
/// division split's `[div-split] conj` line when the gate's
/// `rem_var_is_kernel_proved_by_the_div_split` runs under `TRUST_GATE_TRACE=1`
/// (the bridge compiled trust-cg at its pin af577ca17a and clean at
/// e64e4b7901; 2026-11-15). The
/// aarch64-unknown-linux-gnu conjunction is byte-identical at each level. Item
/// 0 is the result, item 1 the (4b) `rem_by_zero` check. Both sides state the
/// remainder as `X0 - ite(X1 == 0, 0, X0 / X1) * X1` (machine: `udiv` then
/// `msub`; spec: `eval_binop`'s `Rem` arm); O0's machine guard is
/// `subs`/`b.ne` (`BvSub(X1, 0)`), O2's `cbnz`.
fn rem_var(opt: &str) -> Items {
    let text = match opt {
        "O0" => include_str!("fixtures/rem_var-O0.json"),
        "O2" => include_str!("fixtures/rem_var-O2.json"),
        other => panic!("no rem_var fixture {other}"),
    };
    serde_json::from_str(text).expect("fixture parses")
}

fn x1() -> Formula {
    var("X1", 64)
}
fn is_x1(f: &Formula) -> bool {
    matches!(f, Formula::Var(n, Sort::BitVec(64)) if n.as_str() == "X1")
}
fn mul(a: Formula, b: Formula) -> Formula {
    Formula::BvMul(bx(a), bx(b), 64)
}
fn sub(a: Formula, b: Formula) -> Formula {
    Formula::BvSub(bx(a), bx(b), 64)
}
/// The remainder as both sides state it: `a - ite(b == 0, 0, a / b) * b`.
fn urem_composite(a: Formula, b: Formula) -> Formula {
    sub(a.clone(), mul(machine_udiv(a, b.clone()), b))
}

fn has_native_urem(items: &Items) -> bool {
    let mut hit = false;
    for (l, r) in items {
        for side in [l, r] {
            side.visit(&mut |g| hit |= matches!(g, Formula::BvURem(..)));
        }
    }
    hit
}

/// The remainder is kernel-[PROVED] by the route at O0 and O2 with this
/// route's label; the branch split declines it at the walk. Prints the label
/// and the time (not a bound).
#[test]
fn rem_var_is_proved_by_the_div_split() {
    for opt in OPTS {
        let items = rem_var(opt);
        assert!(has_symbolic_divisor(&items), "{opt}");
        assert_eq!(
            branch_split::prove(&items, BranchFilter::On),
            Err(Decline::Filter(WALK_DECLINE.into())),
            "{opt}: the branch split"
        );
        let t = Instant::now();
        let got = watched(opt, &items, BranchFilter::On, Mutant::None);
        let ms = t.elapsed().as_millis();
        let e = got.unwrap_or_else(|d| panic!("{opt}: declined: {d:?}"));
        assert!(is_div_label(&e), "{opt}: {e:?}");
        println!("rem_var {opt}: {ms} ms: {}", label_of(&e));
        assert_eq!(try_conjunction(&items), Some(e), "{opt}: the production entry");
    }
}

/// The declared type is G, built from the original items alone; G states
/// the remainder through the frozen faithful division arm: the goal
/// reflection of `X0 / X1`, `bvIsZero` of X1, and the whole composite
/// `X0 - ite(X1 == 0, 0, X0 / X1) * X1` (its `BvF.Mul` and `BvF.Sub` over
/// them) occur in it, the walk's `BvAdd(X0, X1)` view does not, and its
/// bytes are pinned (`REM_GOAL_PIN`).
#[test]
fn rem_declared_type_is_the_independent_goal() {
    use std::fmt::Write as _;
    let mut pin = String::new();
    for opt in OPTS {
        let items = rem_var(opt);
        let (goal, sides, leaves) = goal_of(&items).expect("goal");
        DECLARED.with(|d| *d.borrow_mut() = None);
        prove(&items, BranchFilter::On).expect("proved");
        let declared = DECLARED.with(|d| d.borrow_mut().take()).expect("declared");
        assert_eq!(declared, goal, "{opt}");
        assert_eq!(branch_split::goal_of(&items).err().as_deref(), Some(WALK_DECLINE));
        let stated = |f: &Formula| {
            let mut ctx = ReflectCtx::branching_goal();
            kx::evalf(reflect_formula(f, &mut ctx).expect("reflects").bvf)
        };
        assert!(occurs(&goal, &stated(&udiv(x64(), x1()))), "{opt}: G does not state X0 / X1");
        let mut ctx = ReflectCtx::branching_goal();
        let y = kx::evalf(reflect_formula(&x1(), &mut ctx).expect("X1").bvf);
        assert!(occurs(&goal, &kx::bv_is_zero(y)), "{opt}: G has no bvIsZero guard on X1");
        assert!(
            occurs(&goal, &stated(&urem_composite(x64(), x1()))),
            "{opt}: G does not state the remainder composite"
        );
        assert!(
            !occurs(&goal, &stated(&walk_view(&udiv(x64(), x1())))),
            "{opt}: G states the walk's view"
        );
        writeln!(pin, "{opt}\n{goal:?}\n{sides:?}\n{leaves:?}").unwrap();
    }
    println!("REM_GOAL_PIN ({}, {})", pin.len(), fnv1a(&pin));
    assert_eq!((pin.len(), fnv1a(&pin)), (4286712, 17152423202715301835), "REM_GOAL_PIN");
}

/// Remainder mutants: each declined with the filters On (`div: the arms of a
/// case differ`) and refused by the KERNEL with the filters Off, under the
/// watchdog. (1) the machine's top guard's arms swapped; (2) the spec's;
/// (3) the spec's quotient `X1 / X0`; (4) the spec's multiplier `X0`
/// (`x - q*x`); (5) the machine's minuend `X1` (`y - q*y`); (6) the
/// machine's `BvSub` made `BvAdd` (`madd`); (7) the machine's quotient guard
/// `X1 == 1`; (8) the spec's minuend `1001`. Builder mutants: the deep
/// abstraction writing the atom's negation (refused by the kernel with the
/// filters on and off), and the leaf comparison reading `bvIteVal true a e`
/// as `e` on a remainder item whose arms differ.
#[test]
fn rem_mutants_are_refused_by_the_kernel() {
    fn is_rem_sub(f: &Formula) -> bool {
        matches!(f, Formula::BvSub(_, m, 64) if matches!(**m, Formula::BvMul(..)))
    }
    let mut seen = Vec::new();
    for opt in OPTS {
        let items = rem_var(opt);
        let cases: Vec<(&str, Items)> = vec![
            (
                "1 machine guard flipped",
                map_machine(&items, &mut |f| match f {
                    Formula::Ite(c, a, e) if is_zero_or(&e) => Formula::Ite(c, e, a),
                    f => f,
                }),
            ),
            (
                "2 spec guard flipped",
                map_spec(&items, &mut |f| match f {
                    Formula::Ite(c, a, e) if is_rem_sub(&a) => Formula::Ite(c, e, a),
                    f => f,
                }),
            ),
            (
                "3 spec quotient X1 / X0",
                map_spec(&items, &mut |f| match f {
                    Formula::BvUDiv(a, b, 64) => Formula::BvUDiv(b, a, 64),
                    f => f,
                }),
            ),
            (
                "4 spec multiplier X0",
                map_spec(&items, &mut |f| match f {
                    Formula::BvMul(q, y, 64) if is_x1(&y) => Formula::BvMul(q, bx(x64()), 64),
                    f => f,
                }),
            ),
            (
                "5 machine minuend X1",
                map_machine(&items, &mut |f| match f {
                    Formula::BvSub(a, m, 64) if is_x(&a) && matches!(*m, Formula::BvMul(..)) => {
                        Formula::BvSub(bx(x1()), m, 64)
                    }
                    f => f,
                }),
            ),
            (
                "6 machine msub -> madd",
                map_machine(&items, &mut |f| match f {
                    Formula::BvSub(a, m, 64) if matches!(*m, Formula::BvMul(..)) => {
                        Formula::BvAdd(a, m, 64)
                    }
                    f => f,
                }),
            ),
            (
                "7 machine quotient guard X1 == 1",
                map_machine(&items, &mut |f| match f {
                    Formula::Ite(c, z, d)
                        if matches!(*d, Formula::BvUDiv(..))
                            && matches!(&*c, Formula::Eq(y, k) if is_x1(y) && is_lit(k, 0)) =>
                    {
                        Formula::Ite(bx(feq(x1(), lit(1, 64))), z, d)
                    }
                    f => f,
                }),
            ),
            (
                "8 spec minuend 1001",
                map_spec(&items, &mut |f| match f {
                    Formula::BvSub(a, m, 64) if is_x(&a) && matches!(*m, Formula::BvMul(..)) => {
                        Formula::BvSub(bx(lit(1001, 64)), m, 64)
                    }
                    f => f,
                }),
            ),
        ];
        for (what, m) in &cases {
            assert_ne!(m, &items, "{opt} {what}: the mutation did not apply");
            let t = Instant::now();
            let on = watched(what, m, BranchFilter::On, Mutant::None);
            assert!(arms_differ(&on), "{opt} {what}: with the filters on: {on:?}");
            let off = watched(what, m, BranchFilter::Off, Mutant::None);
            assert!(kernel_refused(&off), "{opt} {what}: filters off: {off:?}");
            seen.push(format!("{opt} {what}: {} ms", t.elapsed().as_millis()));
        }
        // The deep abstraction writing the atom's negation into the cores
        // writes it into BOTH sides' quotient guards alike (each side states
        // `ite(y == 0, 0, x / y)`), so the leaf comparison passes it even with
        // the filters on (unlike s21, whose spec has no such guard): the
        // KERNEL refuses it either way (measured 2026-11-15).
        for filter in [BranchFilter::On, BranchFilter::Off] {
            let r = watched("deep", &items, filter, Mutant::DeepWrong);
            assert!(kernel_refused(&r), "{opt} deep, {filter:?}: {r:?}");
            seen.push(format!("{opt} deep {filter:?}: kernel refused"));
        }
    }
    // The leaf comparison read wrong: at y == 0 the machine's core selects 0
    // (`bvIteVal true 0 R` after the deep substitution) and the spec selects
    // the remainder `R`, which is X0 there: a false obligation whenever
    // X0 != 0. Read correctly it declines; read `true` as the else arm, it
    // passes the filter and the kernel refuses it.
    let r = urem_composite(x64(), x1());
    let guard = feq(x1(), lit(0, 64));
    let item = vec![(or0(ite(guard.clone(), lit(0, 64), r.clone())), ite(guard, r.clone(), r))];
    let control = watched("norm control", &item, BranchFilter::On, Mutant::None);
    assert!(arms_differ(&control), "norm: the correct comparison declines: {control:?}");
    let off = watched("norm off", &item, BranchFilter::Off, Mutant::None);
    assert!(kernel_refused(&off), "norm: filters off: {off:?}");
    let wrong = watched("norm else", &item, BranchFilter::On, Mutant::NormElse);
    assert!(kernel_refused(&wrong), "norm else-arm: {wrong:?}");
    seen.push(format!("norm else: {wrong:?}"));
    println!("{seen:#?}");
}

/// PRECISION: the machine's quotient zero arm changed (`ite(y == 0, 1, U)`)
/// is an equivalent mutant (the source guard prunes that arm, and at a zero
/// divisor the product is 0 whatever the quotient); the route proves it.
#[test]
fn rem_pruned_zero_arm_is_an_equivalent_twin() {
    for opt in OPTS {
        let items = map_machine(&rem_var(opt), &mut |f| match f {
            Formula::Ite(c, z, d) if matches!(*d, Formula::BvUDiv(..)) && is_lit(&z, 0) => {
                Formula::Ite(c, bx(lit(1, 64)), d)
            }
            f => f,
        });
        assert_ne!(items, rem_var(opt));
        let r = watched("rem zero arm 1", &items, BranchFilter::On, Mutant::None);
        assert!(matches!(&r, Ok(e) if is_div_label(e)), "{opt}: {r:?}");
    }
}

/// FAIL-CLOSED PIN for "no `BvURem` arm" (PKG-C5c-S3c): the spec states an
/// unsigned `%` as the composite `a - ite(b == 0, 0, a / b) * b`
/// (`verify_output::eval_binop`'s `Rem` arm), exactly; each captured
/// remainder conjunction holds that composite on both sides and no
/// `BvURem`. The route has no native-`BvURem` arm: the walk and the
/// pre-filter refuse one (`div_walk_agrees_with_goal_of_without_symbolic_divisors`
/// "remainder by a variable", `the_pre_filter_reads_divisors_only`
/// "remainder"). This test reads `eval_binop`'s `Rem` arm live and the
/// captured fixtures, so it fails when that arm moves (or when a re-captured
/// conjunction holds a native `BvURem`); a machine-side change (the lifter
/// or trust-cg's isel) that emits one is caught instead by `div_split_gate.rs`
/// `rem_var_is_kernel_proved_by_the_div_split` (the walk refuses the native
/// node, so that cell is no longer kernel-[PROVED]). Either way, see the S3c
/// design's contingency (a native arm) before widening anything.
#[test]
fn remainder_reaches_the_gate_as_the_composite() {
    let stated = crate::verify_output::eval_binop(trust_types::BinOp::Rem, x64(), x1(), 64, false)
        .expect("the remainder arm");
    assert_eq!(stated, urem_composite(x64(), x1()), "eval_binop's Rem arm moved");
    for opt in OPTS {
        let items = rem_var(opt);
        assert!(!has_native_urem(&items), "{opt}: a native BvURem reached the gate");
        for (side, f) in [("machine", &items[0].0), ("spec", &items[0].1)] {
            let mut hit = false;
            f.visit(&mut |g| hit |= *g == stated);
            assert!(hit, "{opt}: the {side} side does not hold the composite");
        }
    }
}

/// PKG-C5c-S3c: G of the unsigned remainder composite the gate states for
/// `a % b` (`verify_output::eval_binop`'s `Rem` arm, `a - ite(b == 0, 0,
/// a / b) * b`) is SMT `bvurem`, `a` at a zero divisor, whatever the
/// quotient's value there: form (A) is the gate's own statement (quotient 0
/// at zero, AArch64's), form (B) the unguarded `a - (a / b) * b` (quotient
/// all-ones at zero under G and SMT-LIB). For each pair and form the kernel
/// accepts `Eq.refl` of the Rust value against `bvfEval R_goal(form)` and
/// refuses it with the low bit flipped, ay agrees on the same claims, ay
/// agrees on the native `BvURem` node (`Solver::try_bvurem`), and the walk
/// admits the composite at a symbolic divisor: four readings (kernel G, ay on
/// the composite, ay on native `bvurem`, Rust) agree. On the route's kernel
/// pool, env `branch_base()`.
#[test]
fn goal_urem_composite_agrees_with_smt_bvurem() {
    let max = u64::MAX as u128;
    let m32 = u128::from(u32::MAX);
    let pairs: [(u128, u128, u32); 13] = [
        (1000, 7, 64),
        (max, 0x1234567, 64),
        (1000, 0, 64),
        (0, 0, 64),
        (max, 0, 64),
        (7, 1000, 64),
        (max, 3, 64),
        (max, max, 64),
        (1 << 63, (1 << 63) + 1, 64),
        (0x1234_5678_9abc, 0x10001, 64),
        (0, 5, 64),
        (m32, 0, 32),
        (m32, 10, 32),
    ];
    let mut seen = Vec::new();
    for (a, b, w) in pairs {
        let want = if b == 0 { a } else { a % b };
        let (la, lb_) = (lit(a as i128, w), lit(b as i128, w));
        let composite = |l: Formula, r: Formula| {
            crate::verify_output::eval_binop(trust_types::BinOp::Rem, l, r, w, false)
                .expect("the remainder arm")
        };
        let form_a = composite(la.clone(), lb_.clone());
        let form_b = Formula::BvSub(
            bx(la.clone()),
            bx(Formula::BvMul(
                bx(Formula::BvUDiv(bx(la.clone()), bx(lb_.clone()), w)),
                bx(lb_.clone()),
                w,
            )),
            w,
        );
        for (form, f) in [("A", form_a), ("B", form_b)] {
            let stated_f = f.clone();
            let t = Instant::now();
            let r = kernel_check("div-split-urem-smt", move || {
                let env = branch_theory::branch_base().map_err(Decline::Environment)?.clone();
                let mut ctx = ReflectCtx::branching_goal();
                let stated =
                    kx::evalf(reflect_formula(&stated_f, &mut ctx).map_err(Decline::Filter)?.bvf);
                let check = |v: u128| {
                    let good = kx::bits(v as i128, w);
                    TypeChecker::with_mode(&env, env.mode())
                        .check_type(&refl(lb(), good.clone()), &eq(lb(), stated.clone(), good))
                };
                Ok((check(want).is_ok(), format!("{:?}", check(want ^ 1))))
            });
            let ms = t.elapsed().as_millis();
            let (good, flipped) = r.unwrap_or_else(|d| panic!("({form}) {a} % {b} @{w}: {d:?}"));
            assert!(good, "({form}) {a} % {b} @{w}: the kernel did not compute {want}");
            assert!(
                flipped.starts_with("Err(TypeMismatch"),
                "({form}) {a} % {b} @{w} flipped: {flipped}"
            );
            let claim = |v: u128| feq(f.clone(), lit(v as i128, w));
            assert!(
                matches!(discharge_valid(&claim(want)), Discharge::Proven),
                "ay: ({form}) {a} % {b} @{w}"
            );
            assert!(
                matches!(discharge_valid(&claim(want ^ 1)), Discharge::CounterExample),
                "ay: ({form}) {a} % {b} @{w} flipped"
            );
            seen.push(format!("({form}) {a} % {b} @{w} = {want}: kernel {ms} ms"));
        }
        let native =
            |v: u128| feq(Formula::BvURem(bx(la.clone()), bx(lb_.clone()), w), lit(v as i128, w));
        assert!(
            matches!(discharge_valid(&native(want)), Discharge::Proven),
            "ay native bvurem: {a} % {b} @{w}"
        );
        assert!(
            matches!(discharge_valid(&native(want ^ 1)), Discharge::CounterExample),
            "ay native bvurem: {a} % {b} @{w} flipped"
        );
        let symbolic = composite(la, var("X1", w));
        assert!(in_walk(&vec![(symbolic.clone(), symbolic)]), "{a} % X1 @{w}: the walk");
    }
    println!("{seen:#?}");
}

/// The pool wrapper maps a panic on the kernel thread to a decline.
#[test]
fn a_panicking_kernel_thread_is_a_decline() {
    let r: Result<(), Decline> = kernel_check("div-split-panic", || panic!("deliberate"));
    assert!(matches!(r, Err(Decline::Environment(_))), "{r:?}");
}
