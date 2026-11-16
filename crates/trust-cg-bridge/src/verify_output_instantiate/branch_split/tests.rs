// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, Declaration, Expr, TypeChecker};
use trust_types::{Formula, Sort};

use super::super::branch_reflect::{
    CLOSED_SEEN, CLOSED_WHITELIST, ashr_amount_fold, bool_goal, closed_ok,
};
use super::super::branch_theory::{self, names};
use super::super::kterm::{Fresh, bool_ty, eq, lams, lb, nat, pis, refl, to_nat};
use super::super::{ReflectCtx, kx, o1_routes, reflect_formula, run_recheck_thread};
use super::{BranchFilter, DECLARED, Decline, branch_fragment, goal_of, obligation, prove};
use crate::verify_output::{Discharge, ProvenEvidence, discharge_valid};

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
const U64_MAX: i128 = u64::MAX as i128;

/// FNV-1a, so a pin does not depend on std's unspecified hasher.
fn fnv1a(s: &str) -> u64 {
    s.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
}

/// The kernel's `add_decl` type check refused the discharge (and not the
/// environment, a thread panic or the axiom-closure audit).
fn kernel_refused(r: &Result<ProvenEvidence, Decline>) -> bool {
    matches!(r, Err(Decline::Kernel(m)) if m.starts_with("kernel: TypeCheckFailed"))
}

/// The corpus of plan §5 ("Byte identity").
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

/// The legacy contexts' reflection of `f` (and `o1_routes(l, r)`), written
/// to `s` for a byte pin.
fn legacy_dump(s: &mut String, f: &Formula, l: &Formula, r: &Formula) {
    use std::fmt::Write as _;
    for (mode, mut ctx) in [
        ("closed", ReflectCtx::closed()),
        ("for_obligation", ReflectCtx::for_obligation(l, r)),
        ("commuting", ReflectCtx::commuting()),
        ("strength", ReflectCtx::strength()),
    ] {
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

/// The legacy contexts reflect the branch corpus exactly as the parent
/// commit (5d79168624) did, and `o1_routes` gives the same answers. Both
/// legacy pins were measured on 2026-11-14 by compiling this file's
/// `branch_corpus`, `legacy_dump` and fixture loop into the parent's own
/// `verify_output_instantiate.rs` (`git show 5d79168624:…`, no branch
/// module) and running it under `targo --unverified test -p trust-cg-bridge
/// --features kernel-recheck,test-hooks`; both values equal this tree's.
#[test]
fn legacy_reflection_is_byte_pinned_on_branch_corpus() {
    use std::fmt::Write as _;
    let mut s = String::new();
    for f in &branch_corpus() {
        legacy_dump(&mut s, f, f, f);
        writeln!(s, "o1 {:?}", o1_routes(f, f)).unwrap();
    }
    println!("LEGACY_PIN ({}, {})", s.len(), fnv1a(&s));
    assert_eq!((s.len(), fnv1a(&s)), (2325371, 302647481424284459), "LEGACY_PIN");
}

/// The distinct fixture conjunctions (`fixture_identities` pins which files
/// are copies).
const DISTINCT: [&str; 5] = [
    "s04_if-O0-aarch64-apple-darwin",
    "s05_if_chain-O0-aarch64-apple-darwin",
    "s05_if_chain-O2-aarch64-apple-darwin",
    "r02_branch-O0-aarch64-apple-darwin",
    "r02_branch-O2-aarch64-apple-darwin",
];

/// The legacy contexts reflect every side of every distinct fixture exactly
/// as the parent commit (5d79168624) did, and `o1_routes` gives the same
/// answer per item: the shapes the legacy routes see in S3 (`BvOr(0, v)`,
/// `Not(Not(..))`, the HI `And`, `Extract{0,0}`, the r02 guard). Measured on
/// the parent as `legacy_reflection_is_byte_pinned_on_branch_corpus` says.
#[test]
fn legacy_reflection_is_byte_pinned_on_the_fixtures() {
    use std::fmt::Write as _;
    let mut s = String::new();
    for name in DISTINCT {
        for (l, r) in fixture(name) {
            legacy_dump(&mut s, &l, &l, &r);
            legacy_dump(&mut s, &r, &l, &r);
            writeln!(s, "o1 {:?}", o1_routes(&l, &r)).unwrap();
        }
    }
    println!("LEGACY_FIXTURE_PIN ({}, {})", s.len(), fnv1a(&s));
    assert_eq!((s.len(), fnv1a(&s)), LEGACY_FIXTURE_PIN, "LEGACY_FIXTURE_PIN");
}
const LEGACY_FIXTURE_PIN: (usize, u64) = (59574, 8638902213480661797);

/// Every branch theorem is a proved `Theorem` in the branch base (each was
/// type-checked by `add_decl`), and the base passes the audit.
#[test]
fn branch_theorems_are_kernel_checked() {
    run_recheck_thread("branch-theorems", || {
        let env = branch_theory::branch_base().expect("branch base");
        for name in names::ALL {
            let info =
                env.get_const(&Name::from_string(name)).unwrap_or_else(|| panic!("{name} missing"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name}");
            assert!(info.value.is_some(), "{name} has no proof");
        }
    })
    .expect("kernel thread");
}

/// The kernel rejects false neighbours of the Bool theorems, with the same
/// proof shape: the theorems are not accepted because the checker is blind.
#[test]
fn false_branch_identities_are_rejected() {
    run_recheck_thread("branch-false", || {
        let env = branch_theory::branch_base().expect("branch base").clone();
        let tc = TypeChecker::with_mode(&env, env.mode());
        // `bvIteVal true a e = e` by `Eq.refl e`.
        let mut fr = Fresh::new();
        let (a_id, a) = fr.local();
        let (e_id, e) = fr.local();
        let ty = pis(
            vec![(a_id, lb()), (e_id, lb())],
            eq(lb(), kx::bv_ite_val(kx::btrue(), a.clone(), e.clone()), e.clone()),
        );
        let pf = lams(vec![(a_id, lb()), (e_id, lb())], refl(lb(), e));
        assert!(tc.check_type(&pf, &ty).is_err(), "ite_true with the else arm was accepted");
        // `not (not x) = not x`, by the proof of `not_not`.
        let (x_id, x) = fr.local();
        let ty =
            pis(vec![(x_id, bool_ty())], eq(bool_ty(), kx::bnot(kx::bnot(x.clone())), kx::bnot(x)));
        let pf = Expr::const_str(names::NOT_NOT);
        assert!(tc.check_type(&pf, &ty).is_err(), "not_not stated wrongly was accepted");
        // A declared theorem whose proof is another theorem's is refused by add_decl.
        let mut env2 = env.clone();
        let wrong = env2.add_decl(Declaration::Theorem {
            name: Name::from_string("Trust.BVB.test_wrong"),
            level_params: vec![],
            type_: env.get_const(&Name::from_string(names::HI_ULT)).unwrap().type_.clone(),
            value: Expr::const_str(names::NOT_ULE_ULT_SWAP),
        });
        assert!(wrong.is_err(), "hi_ult accepted not_ule_ult_swap's proof");
    })
    .expect("kernel thread");
}

/// `mul_add_self`'s value premise `V c2 = succ (V c1)` is the kernel's: an
/// instance with `c2 ≠ c1 + 1` is ill-typed.
#[test]
fn mul_add_self_refuses_a_wrong_successor() {
    run_recheck_thread("branch-mul-add-self", || {
        let env = branch_theory::branch_base().expect("branch base").clone();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let w = 8;
        let x = kx::bits(7, w);
        let len = || refl(nat(), kx::nat_lit(w));
        let inst = |c1: i128, c2: i128| {
            let (c1l, c2l) = (kx::bits(c1, w), kx::bits(c2, w));
            branch_theory::mul_add_self_inst(
                x.clone(),
                c1l,
                c2l.clone(),
                kx::nat_lit(w - 1),
                len(),
                len(),
                len(),
                refl(nat(), to_nat(c2l)),
            )
        };
        assert!(tc.infer_type_full(&inst(3, 4)).is_ok(), "the true instance was refused");
        for (c1, c2) in [(3, 5), (3, 3), (4, 3)] {
            assert!(
                tc.infer_type_full(&inst(c1, c2)).is_err(),
                "c1 = {c1}, c2 = {c2} was accepted"
            );
        }
    })
    .expect("kernel thread");
}

/// `divGuardBridge`'s premise `bvIsZero b = false` is the kernel's: at a
/// zero divisor (a masked `1 << 64`, or `6 & 9`) the instance is ill-typed.
#[test]
fn div_guard_refuses_a_zero_divisor() {
    run_recheck_thread("branch-div-guard", || {
        let env = branch_theory::branch_base().expect("branch base").clone();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let a = kx::const_(kx::bits(7, 64));
        let inst = |b: Expr| {
            let eb = kx::evalf(b.clone());
            kx::div_guard_bridge(
                eb,
                kx::bv_not(kx::all_false(kx::evalf(a.clone()))),
                kx::evalf(kx::div(a.clone(), b)),
                refl(bool_ty(), kx::bfalse()),
            )
        };
        assert!(
            tc.infer_type_full(&inst(kx::const_(kx::bits(2, 64)))).is_ok(),
            "7 / 2 was refused"
        );
        let masked = kx::const_(kx::bits(1i128 << 64, 64));
        assert!(tc.infer_type_full(&inst(masked)).is_err(), "the guard accepted 1 << 64");
        let anded = kx::and(kx::const_(kx::bits(6, 64)), kx::const_(kx::bits(9, 64)));
        assert!(tc.infer_type_full(&inst(anded)).is_err(), "the guard accepted 6 & 9");
    })
    .expect("kernel thread");
}

// ── fixtures ─────────────────────────────────────────────────────────────────

type Items = Vec<(Formula, Formula)>;

/// The captured call-event conjunctions (`fixtures/HEADER.md`), as text.
fn fixture_text(name: &str) -> &'static str {
    match name {
        "s04_if-O0-aarch64-apple-darwin" => {
            include_str!("fixtures/s04_if-O0-aarch64-apple-darwin.json")
        }
        "s04_if-O0-aarch64-unknown-linux-gnu" => {
            include_str!("fixtures/s04_if-O0-aarch64-unknown-linux-gnu.json")
        }
        "s04_if-O2-aarch64-apple-darwin" => {
            include_str!("fixtures/s04_if-O2-aarch64-apple-darwin.json")
        }
        "s04_if-O2-aarch64-unknown-linux-gnu" => {
            include_str!("fixtures/s04_if-O2-aarch64-unknown-linux-gnu.json")
        }
        "s05_if_chain-O0-aarch64-apple-darwin" => {
            include_str!("fixtures/s05_if_chain-O0-aarch64-apple-darwin.json")
        }
        "s05_if_chain-O0-aarch64-unknown-linux-gnu" => {
            include_str!("fixtures/s05_if_chain-O0-aarch64-unknown-linux-gnu.json")
        }
        "s05_if_chain-O2-aarch64-apple-darwin" => {
            include_str!("fixtures/s05_if_chain-O2-aarch64-apple-darwin.json")
        }
        "s05_if_chain-O2-aarch64-unknown-linux-gnu" => {
            include_str!("fixtures/s05_if_chain-O2-aarch64-unknown-linux-gnu.json")
        }
        "r02_branch-O0-aarch64-apple-darwin" => {
            include_str!("fixtures/r02_branch-O0-aarch64-apple-darwin.json")
        }
        "r02_branch-O2-aarch64-apple-darwin" => {
            include_str!("fixtures/r02_branch-O2-aarch64-apple-darwin.json")
        }
        "r02_branch-O0-aarch64-unknown-linux-gnu" => {
            include_str!("fixtures/r02_branch-O0-aarch64-unknown-linux-gnu.json")
        }
        "r02_branch-O2-aarch64-unknown-linux-gnu" => {
            include_str!("fixtures/r02_branch-O2-aarch64-unknown-linux-gnu.json")
        }
        S07 => include_str!("fixtures/s07_local_call-O0-aarch64-apple-darwin.json"),
        other => panic!("no fixture {other}"),
    }
}

fn fixture(name: &str) -> Items {
    serde_json::from_str(fixture_text(name)).expect("fixture parses")
}

const S04_S05: [&str; 8] = [
    "s04_if-O0-aarch64-apple-darwin",
    "s04_if-O0-aarch64-unknown-linux-gnu",
    "s04_if-O2-aarch64-apple-darwin",
    "s04_if-O2-aarch64-unknown-linux-gnu",
    "s05_if_chain-O0-aarch64-apple-darwin",
    "s05_if_chain-O0-aarch64-unknown-linux-gnu",
    "s05_if_chain-O2-aarch64-apple-darwin",
    "s05_if_chain-O2-aarch64-unknown-linux-gnu",
];

const R02: [&str; 4] = [
    "r02_branch-O0-aarch64-apple-darwin",
    "r02_branch-O0-aarch64-unknown-linux-gnu",
    "r02_branch-O2-aarch64-apple-darwin",
    "r02_branch-O2-aarch64-unknown-linux-gnu",
];

/// The twelve files hold five distinct conjunctions: s04's four files are
/// one (the IR is the same at O0 and O2 and the bridge emits the same
/// object), and each s05 / r02 file equals its other-triple twin. The triple
/// dimension of the fixture tests adds no coverage; a future divergence
/// fails here.
#[test]
fn fixture_identities() {
    let t = fixture_text;
    for name in &S04_S05[1..4] {
        assert_eq!(t(name), t(S04_S05[0]), "{name}");
    }
    for (a, b) in [
        ("s05_if_chain-O0-aarch64-apple-darwin", "s05_if_chain-O0-aarch64-unknown-linux-gnu"),
        ("s05_if_chain-O2-aarch64-apple-darwin", "s05_if_chain-O2-aarch64-unknown-linux-gnu"),
        ("r02_branch-O0-aarch64-apple-darwin", "r02_branch-O0-aarch64-unknown-linux-gnu"),
        ("r02_branch-O2-aarch64-apple-darwin", "r02_branch-O2-aarch64-unknown-linux-gnu"),
    ] {
        assert_eq!(t(a), t(b), "{a} / {b}");
    }
    for (i, a) in DISTINCT.iter().enumerate() {
        for b in &DISTINCT[i + 1..] {
            assert_ne!(t(a), t(b), "{a} / {b}");
        }
    }
}

/// Rewrite every node of `f` bottom-up with `g`.
fn map(f: &Formula, g: &dyn Fn(Formula) -> Formula) -> Formula {
    let m = |x: &Formula| Box::new(map(x, g));
    let out = match f {
        Formula::Not(x) => Formula::Not(m(x)),
        Formula::And(xs) => Formula::And(xs.iter().map(|x| map(x, g)).collect()),
        Formula::Or(xs) => Formula::Or(xs.iter().map(|x| map(x, g)).collect()),
        Formula::Ite(c, a, e) => Formula::Ite(m(c), m(a), m(e)),
        Formula::Eq(a, b) => Formula::Eq(m(a), m(b)),
        Formula::BvAdd(a, b, w) => Formula::BvAdd(m(a), m(b), *w),
        Formula::BvSub(a, b, w) => Formula::BvSub(m(a), m(b), *w),
        Formula::BvMul(a, b, w) => Formula::BvMul(m(a), m(b), *w),
        Formula::BvUDiv(a, b, w) => Formula::BvUDiv(m(a), m(b), *w),
        Formula::BvAnd(a, b, w) => Formula::BvAnd(m(a), m(b), *w),
        Formula::BvOr(a, b, w) => Formula::BvOr(m(a), m(b), *w),
        Formula::BvXor(a, b, w) => Formula::BvXor(m(a), m(b), *w),
        Formula::BvShl(a, b, w) => Formula::BvShl(m(a), m(b), *w),
        Formula::BvLShr(a, b, w) => Formula::BvLShr(m(a), m(b), *w),
        Formula::BvAShr(a, b, w) => Formula::BvAShr(m(a), m(b), *w),
        Formula::BvULt(a, b, w) => Formula::BvULt(m(a), m(b), *w),
        Formula::BvULe(a, b, w) => Formula::BvULe(m(a), m(b), *w),
        Formula::BvSLt(a, b, w) => Formula::BvSLt(m(a), m(b), *w),
        Formula::BvExtract { inner, high, low } => {
            Formula::BvExtract { inner: m(inner), high: *high, low: *low }
        }
        Formula::BvZeroExt(x, k) => Formula::BvZeroExt(m(x), *k),
        Formula::BvSignExt(x, k) => Formula::BvSignExt(m(x), *k),
        other => other.clone(),
    };
    g(out)
}

/// The spec side of every item rewritten by `g`.
fn mutate_spec(items: &Items, g: &dyn Fn(Formula) -> Formula) -> Items {
    items.iter().map(|(l, r)| (l.clone(), map(r, g))).collect()
}

/// The machine side of every item rewritten by `g`.
fn mutate_machine(items: &Items, g: &dyn Fn(Formula) -> Formula) -> Items {
    items.iter().map(|(l, r)| (map(l, g), r.clone())).collect()
}

fn is_branch_label(e: &ProvenEvidence) -> bool {
    matches!(e, ProvenEvidence::KernelInstantiated { theorem, original: None }
        if theorem.ends_with(branch_theory::LABEL_TAIL) && theorem.contains("Trust.BVB.ite_cong"))
}

fn is_x(f: &Formula) -> bool {
    matches!(f, Formula::Var(n, _) if n == "X0")
}
fn is_lit(f: &Formula, v: i128) -> bool {
    matches!(f, Formula::BitVec { value, .. } if *value == v)
}

/// Swap the arms of the outermost spec `Ite` of every item.
fn swap_spec_arms(items: &Items) -> Items {
    items
        .iter()
        .map(|(l, r)| match r {
            Formula::Ite(c, a, e) => (l.clone(), Formula::Ite(c.clone(), e.clone(), a.clone())),
            other => (l.clone(), other.clone()),
        })
        .collect()
}

/// A literal `from` (at any width) as `to`.
fn relit(from: i128, to: i128) -> impl Fn(Formula) -> Formula {
    move |f| match f {
        Formula::BitVec { value, width } if value == from => lit(to, width),
        other => other,
    }
}

/// `x < k` (in either operand order) with `k` replaced.
fn rethreshold(k: i128, to: i128) -> impl Fn(Formula) -> Formula {
    move |f| match f {
        Formula::BvULt(a, b, w) if is_x(&a) && is_lit(&b, k) => {
            Formula::BvULt(a, bx(lit(to, w)), w)
        }
        Formula::BvULt(a, b, w) if is_lit(&a, k) && is_x(&b) => {
            Formula::BvULt(bx(lit(to, w)), b, w)
        }
        other => other,
    }
}

/// The spec's carrier `Not(Eq(Ite(x < k, 1, 0), 0))` with its `Not` dropped.
fn drop_polarity(k: i128) -> impl Fn(Formula) -> Formula {
    move |f| match f {
        Formula::Not(inner)
            if matches!(&*inner, Formula::Eq(i, _)
                if matches!(&**i, Formula::Ite(c, ..)
                    if matches!(&**c, Formula::BvULt(a, b, _) if is_x(a) && is_lit(b, k)))) =>
        {
            *inner
        }
        other => other,
    }
}

/// The plan's mutants (§5), built from the fixture `items`. Each is `(what,
/// items')`; a mutant that does not apply to `items` is left out.
fn mutants(items: &Items) -> Vec<(&'static str, Items)> {
    let all: Vec<(&'static str, Items)> = vec![
        // spec side
        ("spec arm 10 -> 11", mutate_spec(items, &relit(10, 11))),
        ("spec arm 1 -> 3", mutate_spec(items, &relit(1, 3))),
        ("spec swapped arms", swap_spec_arms(items)),
        (
            "spec x*3 -> x*5",
            mutate_spec(items, &|f| match f {
                Formula::BvMul(a, b, w) if is_lit(&b, 3) => Formula::BvMul(a, bx(lit(5, w)), w),
                other => other,
            }),
        ),
        (
            "spec >100 -> >=100",
            mutate_spec(items, &|f| match f {
                Formula::BvULt(a, b, w) if is_lit(&a, 100) && is_x(&b) => Formula::BvULe(a, b, w),
                other => other,
            }),
        ),
        (
            "spec bit0 -> bit1 (&1 -> &2)",
            mutate_spec(items, &|f| match f {
                Formula::BvAnd(a, b, w) if is_x(&a) && is_lit(&b, 1) => {
                    Formula::BvAnd(a, bx(lit(2, w)), w)
                }
                other => other,
            }),
        ),
        (
            "spec &1 -> &3",
            mutate_spec(items, &|f| match f {
                Formula::BvAnd(a, b, w) if is_x(&a) && is_lit(&b, 1) => {
                    Formula::BvAnd(a, bx(lit(3, w)), w)
                }
                other => other,
            }),
        ),
        ("spec x<2 -> x<3", mutate_spec(items, &rethreshold(2, 3))),
        ("spec x<5 -> x<6", mutate_spec(items, &rethreshold(5, 6))),
        ("spec wrong polarity (x<2)", mutate_spec(items, &drop_polarity(2))),
        ("spec wrong polarity (x<5)", mutate_spec(items, &drop_polarity(5))),
        // machine side
        (
            "machine mov #10 -> #11",
            mutate_machine(items, &|f| match f {
                Formula::BvOr(z, v, w) if is_lit(&z, 0) && is_lit(&v, 10) => {
                    Formula::BvOr(z, bx(lit(11, w)), w)
                }
                other => other,
            }),
        ),
        ("machine x<5 -> x<6", mutate_machine(items, &rethreshold(5, 6))),
        ("machine x<2 -> x<3", mutate_machine(items, &rethreshold(2, 3))),
        ("machine cmp #100 -> #101 (b.hi)", mutate_machine(items, &hi_cmp(true, true))),
        ("machine x-100 -> x-101 in b.hi", mutate_machine(items, &hi_cmp(false, true))),
        (
            "machine arm x-100 -> x-101",
            mutate_machine(items, &|f| match f {
                Formula::BvOr(z, s, w)
                    if is_lit(&z, 0)
                        && matches!(&*s, Formula::BvSub(a, b, _) if is_x(a) && is_lit(b, 100)) =>
                {
                    Formula::BvOr(z, bx(Formula::BvSub(bx(x64()), bx(lit(101, 64)), 64)), w)
                }
                other => other,
            }),
        ),
        (
            "machine tbz bit0 -> bit1",
            mutate_machine(items, &|f| match f {
                Formula::BvExtract { inner, high: 0, low: 0 } if is_x(&inner) => {
                    Formula::BvExtract {
                        inner: bx(Formula::BvLShr(inner, bx(lit(1, 64)), 64)),
                        high: 0,
                        low: 0,
                    }
                }
                other => other,
            }),
        ),
        (
            "machine &1 -> &3",
            mutate_machine(items, &|f| match f {
                Formula::BvAnd(a, b, w) if is_x(&a) && is_lit(&b, 1) => {
                    Formula::BvAnd(a, bx(lit(3, w)), w)
                }
                other => other,
            }),
        ),
        (
            "machine lsl #1 -> #2",
            mutate_machine(items, &|f| match f {
                Formula::BvShl(a, b, w) if is_x(&a) && is_lit(&b, 1) => {
                    Formula::BvShl(a, bx(lit(2, w)), w)
                }
                other => other,
            }),
        ),
        (
            "machine x*3 -> x*5",
            mutate_machine(items, &|f| match f {
                Formula::BvMul(a, b, w) if is_x(&a) && is_lit(&b, 3) => {
                    Formula::BvMul(a, bx(lit(5, w)), w)
                }
                other => other,
            }),
        ),
    ];
    all.into_iter().filter(|(_, m)| m != items).collect()
}

/// In the machine `b.hi` condition `And[Not(x < 100), Not(x - 100 == 0)]`,
/// `100` becomes `101` in the comparison (`cmp`) and/or the difference.
fn hi_cmp(cmp: bool, diff: bool) -> impl Fn(Formula) -> Formula {
    move |f| match f {
        Formula::And(xs) if xs.len() == 2 => {
            let fix = |x: &Formula, on: bool| {
                if !on {
                    return x.clone();
                }
                map(x, &|g| match g {
                    Formula::BvULt(a, b, w) if cmp && is_x(&a) && is_lit(&b, 100) => {
                        Formula::BvULt(a, bx(lit(101, w)), w)
                    }
                    Formula::BvSub(a, b, w) if diff && is_x(&a) && is_lit(&b, 100) => {
                        Formula::BvSub(a, bx(lit(101, w)), w)
                    }
                    other => other,
                })
            };
            Formula::And(vec![fix(&xs[0], cmp), fix(&xs[1], diff)])
        }
        other => other,
    }
}

/// Every mutant name the exit test must have applied to some fixture.
/// The r02 mutants are in `r02_is_proved_and_its_mutants_are_not`.
const MUTANTS: [&str; 21] = [
    "spec arm 10 -> 11",
    "spec arm 1 -> 3",
    "spec swapped arms",
    "spec x*3 -> x*5",
    "spec >100 -> >=100",
    "spec bit0 -> bit1 (&1 -> &2)",
    "spec &1 -> &3",
    "spec x<2 -> x<3",
    "spec x<5 -> x<6",
    "spec wrong polarity (x<2)",
    "spec wrong polarity (x<5)",
    "machine mov #10 -> #11",
    "machine x<5 -> x<6",
    "machine x<2 -> x<3",
    "machine cmp #100 -> #101 (b.hi)",
    "machine x-100 -> x-101 in b.hi",
    "machine arm x-100 -> x-101",
    "machine tbz bit0 -> bit1",
    "machine &1 -> &3",
    "machine lsl #1 -> #2",
    "machine x*3 -> x*5",
];

/// BRANCH-SPLIT-1 exit test: every s04 and s05 conjunction (both opts, both
/// triples; three distinct inputs, `fixture_identities`) is
/// `KernelInstantiated` with a branch label; every mutant (s04 and s05,
/// spec and machine side) is not proved, and with the Rust checks bypassed
/// it is the kernel's type check that refuses it.
#[test]
fn branch_split_proves_s04_s05_and_refuses_mutants() {
    for name in S04_S05 {
        let items = fixture(name);
        let routed = super::try_branch_split_conjunction(&items);
        assert!(routed.as_ref().is_some_and(is_branch_label), "{name}: the route gave {routed:?}");
        let got = prove(&items, BranchFilter::On);
        match &got {
            Ok(e) => assert!(is_branch_label(e), "{name}: label {e:?}"),
            Err(d) => panic!("{name}: declined {d:?}"),
        }
    }
    // The positives do not depend on a Rust check either.
    for name in DISTINCT.iter().filter(|n| !n.starts_with("r02")) {
        let got = prove(&fixture(name), BranchFilter::Off);
        assert!(matches!(&got, Ok(e) if is_branch_label(e)), "{name} with the filter off: {got:?}");
    }
    let mut applied = std::collections::HashSet::new();
    for name in S04_S05 {
        let items = fixture(name);
        for (what, m) in mutants(&items) {
            applied.insert(what);
            assert!(prove(&m, BranchFilter::On).is_err(), "{name}: mutant '{what}' proved");
            let off = prove(&m, BranchFilter::Off);
            assert!(kernel_refused(&off), "{name}: mutant '{what}' with the filter off: {off:?}");
        }
    }
    for what in MUTANTS {
        assert!(applied.contains(what), "the mutant '{what}' applied to no fixture");
    }
}

/// The declared type is the goal built from the items alone: the exact type
/// `prove` handed to `strength::admit_obligation` (the `DECLARED` hook)
/// equals a reference built here by the reflection under `branching_goal`
/// and an `And` fold, without `goal_of` or `obligation`.
#[test]
fn declared_type_is_the_independent_goal() {
    let named = S04_S05.iter().chain(&R02).map(|n| (n.to_string(), fixture(n)));
    for (name, items) in named.chain(s10()) {
        let mut ctx = ReflectCtx::branching_goal();
        let mut eqs = Vec::new();
        for (l, r) in &items {
            let rl = reflect_formula(l, &mut ctx).expect("goal");
            let rr = reflect_formula(r, &mut ctx).expect("goal");
            eqs.push(kx::eq_list(kx::evalf(rl.bvf), kx::evalf(rr.bvf)));
        }
        let mut reference = eqs.pop().expect("one item");
        while let Some(e) = eqs.pop() {
            reference = Expr::apps(Expr::const_str("And"), [e, reference]);
        }
        DECLARED.with(|d| *d.borrow_mut() = None);
        prove(&items, BranchFilter::On).unwrap_or_else(|d| panic!("{name}: {d:?}"));
        let declared = DECLARED.with(|d| d.borrow_mut().take()).expect("the hook saw no type");
        assert_eq!(declared, reference, "{name}");
    }
}

/// `branching()` (steps on) and `branching_goal()` (steps off) reflect the
/// same `bvf` (the T-U10 property extended to the branch arms).
#[test]
fn branching_bvf_matches_the_goal() {
    let mut corpus: Vec<Formula> = branch_corpus();
    for name in DISTINCT {
        for (l, r) in fixture(name) {
            corpus.push(l);
            corpus.push(r);
        }
    }
    for (_, items) in s10() {
        for (l, r) in items {
            corpus.push(l);
            corpus.push(r);
        }
    }
    for f in &corpus {
        let a = reflect_formula(f, &mut ReflectCtx::branching_goal()).map(|r| r.bvf);
        let b = reflect_formula(f, &mut ReflectCtx::branching()).map(|r| r.bvf);
        assert_eq!(a, b, "{f:?}");
    }
}

/// The branch corpus under `branching_goal()`, pinned at S1: a change to a
/// goal arm needs a waiver on `branch_reflect.rs`.
#[test]
fn branching_goal_reflection_is_byte_pinned() {
    use std::fmt::Write as _;
    let mut s = String::new();
    for f in &branch_corpus() {
        let mut ctx = ReflectCtx::branching_goal();
        match reflect_formula(f, &mut ctx) {
            Ok(r) => {
                writeln!(s, "{:?}\n{:?}\n{:?}\n{:?}", r.bvf, r.core, r.proof, ctx.leaves).unwrap()
            }
            Err(e) => writeln!(s, "Err {e}").unwrap(),
        }
    }
    println!("BRANCH_GOAL_PIN ({}, {})", s.len(), fnv1a(&s));
    assert_eq!((s.len(), fnv1a(&s)), (1172280, 17568974519860709913), "BRANCH_GOAL_PIN");
}

/// The goal condition of a nested `Ite` is built with the step builders off:
/// a step under it would be discarded, so it is neither built nor counted.
#[test]
fn a_discarded_goal_condition_takes_no_step() {
    let cond = feq(Formula::BvSub(bx(x64()), bx(lit(0, 64)), 64), lit(0, 64));
    let f = Formula::BvMul(bx(ite(cond, lit(1, 64), lit(2, 64))), bx(lit(3, 64)), 64);
    let mut ctx = ReflectCtx::branching();
    reflect_formula(&f, &mut ctx).expect("reflects");
    assert_eq!(ctx.branch_rewrites, 0, "a discarded goal reflection took a branch step");
    // The same condition in a proving position takes its `sub_zero` step.
    let mut ctx = ReflectCtx::branching();
    let sub = Formula::BvSub(bx(x64()), bx(lit(0, 64)), 64);
    reflect_formula(&sub, &mut ctx).expect("reflects");
    assert_eq!(ctx.branch_rewrites, 1);
}

/// A width mismatch inside a comparison is not seen by the kernel: `bvBeq`
/// reads the common prefix, so `0:32 == 2^32:64` is `true` to it. This is why
/// comparison widths are trusted residual, and why the walk is part of the
/// goal: the route refuses the shape with the filter on and with it off.
#[test]
fn ill_sorted_comparison_is_kernel_blind_and_refused_by_the_goal() {
    run_recheck_thread("branch-ill-sorted", || {
        let env = branch_theory::branch_base().expect("base").clone();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ill = kx::bv_beq(kx::bits(0, 32), kx::bits(1i128 << 32, 64));
        let claim = eq(bool_ty(), ill, kx::btrue());
        assert!(tc.check_type(&refl(bool_ty(), kx::btrue()), &claim).is_ok());
    })
    .expect("kernel thread");
    let ult = ult(x64(), lit(2, 64), 64);
    let ill = feq(lit(0, 32), lit(1i128 << 32, 64));
    let machine = ite(ult.clone(), ite(ill, lit(10, 64), lit(11, 64)), lit(10, 64));
    let spec = ite(ult, lit(10, 64), lit(10, 64));
    let items = vec![(machine.clone(), spec)];
    assert!(!branch_fragment(&machine), "the walk accepted an ill-sorted comparison");
    assert!(goal_of(&items).is_err(), "the goal stated an ill-sorted comparison");
    let walk = Decline::Filter("branch: a side is outside the width walk".into());
    assert_eq!(prove(&items, BranchFilter::On), Err(walk.clone()));
    assert_eq!(prove(&items, BranchFilter::Off), Err(walk));
}

/// The walk refuses each shape outside plan §4, with the filter on and off.
#[test]
fn branch_fragment_refusals() {
    let c = ult(x64(), lit(2, 64), 64);
    let it = |a: Formula, b: Formula| ite(c.clone(), a, b);
    // Under a symbolic `Ite`, as the shapes arise; the walk decides either way.
    let in_cond = |cond: Formula| it(ite(cond, x64(), x64()), x64());
    let refused = [
        ("symbolic divisor", it(Formula::BvUDiv(bx(x64()), bx(x64()), 64), x64())),
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
        ("ULe declared at 32 over 64", in_cond(Formula::BvULe(bx(x64()), bx(lit(2, 64)), 32))),
        ("SLt of widths 64 and 32", in_cond(Formula::BvSLt(bx(x64()), bx(lit(2, 32)), 64))),
        ("SLt declared at 32 over 64", in_cond(Formula::BvSLt(bx(x64()), bx(lit(2, 64)), 32))),
        ("Extract{1,1}", it(Formula::BvExtract { inner: bx(x64()), high: 1, low: 1 }, lit(0, 1))),
        (
            "Extract high u32::MAX",
            it(Formula::BvExtract { inner: bx(x64()), high: u32::MAX, low: 1 }, x64()),
        ),
        ("ZeroExt past 64", it(Formula::BvZeroExt(bx(x64()), 1), x64())),
        ("BvNot", it(Formula::BvNot(bx(x64()), 64), x64())),
        ("BvSLe", in_cond(Formula::BvSLe(bx(x64()), bx(lit(2, 64)), 64))),
        ("nine-way And", in_cond(Formula::And(vec![c.clone(); 9]))),
    ];
    for (what, f) in refused {
        assert!(!branch_fragment(&f), "{what}");
        let items = vec![(f.clone(), f)];
        for filter in [BranchFilter::On, BranchFilter::Off] {
            assert_eq!(
                prove(&items, filter),
                Err(Decline::Filter("branch: a side is outside the width walk".into())),
                "{what}, {filter:?}"
            );
        }
    }
    assert!(branch_fragment(&it(x64(), lit(1, 64))));
    assert!(branch_fragment(&in_cond(Formula::And(vec![c.clone(); 8]))));
    // A Bool equality, a closed arithmetic-shift amount below the width and
    // a closed sign extension are inside the walk.
    assert!(branch_fragment(&in_cond(feq(Formula::Bool(true), c.clone()))));
    assert!(branch_fragment(&it(Formula::BvAShr(bx(x64()), bx(lit(63, 64)), 64), x64())));
    assert!(branch_fragment(&it(Formula::BvAShr(bx(x64()), bx(s10_amount()), 64), x64())));
    assert!(branch_fragment(&it(Formula::BvSignExt(bx(lit(2, 32)), 32), x64())));
    assert!(branch_fragment(&it(
        Formula::BvExtract { inner: bx(x64()), high: 63, low: 1 }.clone(),
        Formula::BvExtract { inner: bx(x64()), high: 62, low: 0 }
    )));
}

/// A closed comparison that is not a literal one is refused, not abstracted:
/// `Eq(BvUDiv(8, 2), 4)` would have the kernel evaluate `bvDiv` on closed
/// data (plan §2).
#[test]
fn closed_comparison_off_the_whitelist_is_refused() {
    let closed = feq(Formula::BvUDiv(bx(lit(8, 64)), bx(lit(2, 64)), 64), lit(4, 64));
    let side = ite(ult(x64(), lit(2, 64), 64), ite(closed, x64(), lit(0, 64)), x64());
    assert!(branch_fragment(&side));
    let items = vec![(side.clone(), side)];
    for filter in [BranchFilter::On, BranchFilter::Off] {
        assert_eq!(
            prove(&items, filter),
            Err(Decline::Filter(
                "branch: a closed comparison off the closed-data whitelist".into()
            )),
            "{filter:?}"
        );
    }
}

/// Every closed term the route has the kernel evaluate on the fixtures (the
/// ground conditions, the `Eq.refl` premises, the concrete comparisons and
/// every leaf condition of the split) uses only the plan §2 whitelist, which
/// is pinned here exactly; `closed_ok` refuses an off-list head, a long list,
/// a large literal and a free variable.
#[test]
fn closed_data_is_whitelisted() {
    use std::collections::HashSet;

    use clean_kernel::expr::UsedConstants;
    assert_eq!(
        CLOSED_WHITELIST,
        [
            "Bool",
            "Bool.true",
            "Bool.false",
            "Bool.not",
            "Bool.and",
            "Bool.or",
            "Bool.xor",
            "Bool.rec",
            "List.cons",
            "List.nil",
            "Clean.BVC.bvfEval",
            "Clean.BVC.BvF.Const",
            "Clean.BVC.BvF.Leaf",
            "Clean.BVC.BvF.ExtractLow",
            "Clean.BVC.BvF.And",
            "Clean.BVC.bvIteVal",
            "Clean.BVC.bvBeq",
            "Clean.BVC.bvIsZero",
            "Clean.BVC.bvUlt",
            "Clean.BVC.carryOut",
            "Clean.BVC.bvULe",
            "Clean.BVC.bvSLtReal",
            "Clean.BVC.bvFlipMsb",
            "Clean.BVC.bvTakeLen",
            "Clean.BVC.bvZipAnd",
            "Clean.BVC.bvZeroExt",
            "Clean.BVC.bvAppend",
            "Clean.BVC.bvReplF",
            "Clean.BVC.bvLastBit",
            "Clean.BVI.btail",
            "Clean.BVC.bvLen",
            "Clean.BVC.bvToNat",
            "Nat.zero",
            "Nat.succ",
            "Nat.add",
            "Nat.mul",
        ]
    );
    CLOSED_SEEN.with(|s| s.borrow_mut().clear());
    for name in DISTINCT {
        obligation(&fixture(name), BranchFilter::On).unwrap_or_else(|d| panic!("{name}: {d:?}"));
    }
    for (name, items) in s10() {
        obligation(&items, BranchFilter::On).unwrap_or_else(|d| panic!("{name}: {d:?}"));
    }
    let seen = CLOSED_SEEN.with(|s| std::mem::take(&mut *s.borrow_mut()));
    let mut heads = HashSet::new();
    for e in &seen {
        assert!(closed_ok(e), "an off-whitelist closed term was emitted: {e:?}");
        e.used_constants_dag(UsedConstants::ConstantsOnly, &mut heads);
    }
    let heads: HashSet<String> = heads.into_iter().map(|n| n.to_string()).collect();
    // Each site was reached: a ground condition and the division premise
    // (r02), the `mul_add_self` premises (s05 O2), the `tbz` comparison
    // (s05 O2), the leaf conditions, and s10's shift-amount fold.
    for want in [
        "Clean.BVC.bvIsZero",
        "Clean.BVC.bvToNat",
        "Clean.BVC.BvF.ExtractLow",
        "Clean.BVC.bvBeq",
        "Bool.not",
        "Clean.BVC.BvF.And",
        "Clean.BVC.bvLastBit",
    ] {
        assert!(heads.contains(want), "no closed term used {want}");
    }
    for never in [
        "Clean.BVC.bvMul",
        "Clean.BVC.bvDiv",
        "Clean.BVC.bvShl",
        "Clean.BVC.bvLShr",
        "Clean.BVC.natToBvAux",
        "Nat.div",
        "Nat.mod",
        "Clean.BVC.BvF.Mul",
        "Clean.BVC.BvF.Div",
        "Clean.BVC.bvAShr",
        "Clean.BVC.BvF.AShr",
    ] {
        assert!(!heads.contains(never), "{never} was evaluated on closed data");
    }
    // `closed_ok` refuses what is off the list.
    let div = kx::evalf(kx::div(kx::const_(kx::bits(8, 64)), kx::const_(kx::bits(2, 64))));
    assert!(!closed_ok(&div));
    assert!(!closed_ok(&kx::bits(0, 65)));
    assert!(closed_ok(&kx::bits(0, 64)));
    assert!(!closed_ok(&Expr::nat_lit_u128(1u128 << 64)));
    assert!(closed_ok(&Expr::nat_lit(64)));
    // A split variable is opaque, like a leaf bit.
    assert!(closed_ok(&Fresh::new().local().1));
}

/// The label names only theorems that occur in the admitted term.
#[test]
fn label_names_only_constants_in_the_proof() {
    use std::collections::HashSet;

    use clean_kernel::expr::UsedConstants;
    let items = fixture("s05_if_chain-O2-aarch64-apple-darwin");
    let ob = obligation(&items, BranchFilter::On).expect("obligation");
    let proof = ob.proof.clone();
    let label = run_recheck_thread("branch-label", move || {
        let env = branch_theory::env(&ob.leaves).expect("env");
        branch_theory::label(&env, &ob.proof)
    })
    .expect("thread");
    let mut used = HashSet::new();
    proof.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    let used: HashSet<String> = used.into_iter().map(|n| n.to_string()).collect();
    let parts: Vec<&str> = label.split('+').collect();
    let (tail, names) = parts.split_last().expect("label");
    assert_eq!(*tail, branch_theory::LABEL_TAIL);
    assert!(!names.is_empty());
    for n in names {
        assert!(used.contains(*n), "{n} is in the label but not in the proof");
    }
    for want in ["Trust.BVB.hi_ult", "Trust.BVB.beq_and_lowbit", "Trust.BVS.mul_add_self"] {
        assert!(names.contains(&want), "{want} missing from {label}");
    }
}

/// `const_bits` reads a literal `Const` of 1 to 64 bits and nothing else.
#[test]
fn const_bits_decoder() {
    let c = |v: i128, w: u32| kx::const_(kx::bits(v, w));
    assert_eq!(branch_theory::const_bits(&c(5, 8)), Some((8, 5)));
    assert_eq!(branch_theory::const_bits(&c(1i128 << 64, 64)), Some((64, 0)));
    assert_eq!(branch_theory::const_bits(&c(0, 65)), None);
    assert_eq!(branch_theory::const_bits(&kx::const_(kx::nil())), None);
    assert_eq!(branch_theory::const_bits(&kx::leaf(kx::bits(1, 4))), None);
    let opaque = kx::const_(kx::cons(Expr::const_str("BVC_LEAFBIT_X0_64_0"), kx::nil()));
    assert_eq!(branch_theory::const_bits(&opaque), None);
}

/// An axiom of the goal's type is not a discharge: `admit_obligation`
/// refuses a term whose axiom closure leaves the leaf bits.
#[test]
fn an_axiom_under_the_discharge_is_refused() {
    let items = fixture("s05_if_chain-O2-aarch64-apple-darwin");
    let ob = obligation(&items, BranchFilter::On).expect("obligation");
    let refused = run_recheck_thread("branch-axiom", move || {
        let mut env = branch_theory::env(&ob.leaves).expect("env");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Trust.BVB.test_axiom"),
            level_params: vec![],
            type_: ob.goal.clone(),
        })
        .expect("axiom");
        super::super::strength::admit_obligation(
            &mut env,
            ob.goal,
            Expr::const_str("Trust.BVB.test_axiom"),
        )
    })
    .expect("thread");
    assert!(
        matches!(&refused, Err(m) if m.starts_with("obligation reaches axioms")),
        "an axiom was admitted as the discharge, or refused for another reason: {refused:?}"
    );
}

/// The faithful division: `x / 0` is all-ones and `7 / 2` is `3`, as the
/// kernel computes the goal reflection, and the kernel refuses each value
/// off by one bit.
#[test]
fn udiv_reflection_is_faithful_at_zero() {
    let cases = [(5, 0, 255), (7, 2, 3), (255, 1, 255), (0, 0, 255)];
    run_recheck_thread("branch-udiv", move || {
        let env = branch_theory::branch_base().expect("base").clone();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for (a, b, q) in cases {
            let f = Formula::BvUDiv(bx(lit(a, 8)), bx(lit(b, 8)), 8);
            let r = reflect_formula(&f, &mut ReflectCtx::branching_goal()).expect("reflect");
            let claim = kx::eq_list(kx::evalf(r.bvf.clone()), kx::bits(q, 8));
            assert!(tc.check_type(&kx::eq_refl_list(kx::bits(q, 8)), &claim).is_ok(), "{a} / {b}");
            let wrong = kx::eq_list(kx::evalf(r.bvf), kx::bits(q ^ 1, 8));
            let pf = kx::eq_refl_list(kx::bits(q ^ 1, 8));
            assert!(tc.check_type(&pf, &wrong).is_err(), "{a} / {b} accepted as {}", q ^ 1);
        }
    })
    .expect("thread");
}

/// The faithful division through the route: a spec `x / 0` (a literal 0, a
/// masked `1 << 64`, and `6 & 9`) against a machine all-ones is a true
/// obligation the kernel proves with the Rust checks bypassed (the leaf arm
/// comparison is syntactic, so the filter declines it); against a machine 0
/// (Lean's `n / 0`) it is false and the kernel refuses it.
#[test]
fn faithful_udiv_through_the_route() {
    let c = ult(x64(), lit(2, 64), 64);
    let divisors =
        [lit(0, 64), lit(1i128 << 64, 64), Formula::BvAnd(bx(lit(6, 64)), bx(lit(9, 64)), 64)];
    for d in divisors {
        let spec = ite(c.clone(), Formula::BvUDiv(bx(x64()), bx(d.clone()), 64), x64());
        let ones = vec![(ite(c.clone(), lit(U64_MAX, 64), x64()), spec.clone())];
        assert!(prove(&ones, BranchFilter::On).is_err(), "{d:?}");
        let off = prove(&ones, BranchFilter::Off);
        assert!(matches!(&off, Ok(e) if is_branch_label(e)), "x / {d:?} = all-ones: {off:?}");
        let zero = vec![(ite(c.clone(), lit(0, 64), x64()), spec)];
        assert!(prove(&zero, BranchFilter::On).is_err(), "{d:?}");
        let off = prove(&zero, BranchFilter::Off);
        assert!(kernel_refused(&off), "x / {d:?} = 0 with the filter off: {off:?}");
    }
}

/// A bare extract drops its child's core, so it refuses a child that took a
/// branch step (here a ground selection).
#[test]
fn extract_over_a_branch_step_is_refused() {
    let ground = ite(feq(lit(1, 64), lit(1, 64)), x64(), lit(0, 64));
    let f = Formula::BvExtract { inner: bx(ground.clone()), high: 31, low: 0 };
    let got = reflect_formula(&f, &mut ReflectCtx::branching()).map(|r| r.bvf);
    assert_eq!(got, Err("reflect: extract over a branch step (outside fragment)".into()));
    assert!(reflect_formula(&f, &mut ReflectCtx::branching_goal()).is_ok());
    // The selection itself is a kernel-checked step.
    let r = reflect_formula(&ground, &mut ReflectCtx::branching()).expect("ground");
    assert_ne!(r.core, r.bvf);
}

/// The caps: seven distinct atoms, 33 branch steps, 40 leaves in one
/// condition; and the walk's node and junct bounds.
#[test]
fn caps_decline() {
    let atom = |k: i128| ult(x64(), lit(k, 64), 64);
    let mut side = lit(0, 64);
    for k in 1..=7 {
        side = ite(atom(k), lit(k, 64), side);
    }
    let items = vec![(side.clone(), side)];
    assert_eq!(prove(&items, BranchFilter::On), Err(Decline::Filter("branch: cap (atoms)".into())));
    let ground = || ite(feq(lit(1, 64), lit(1, 64)), x64(), lit(0, 64));
    let mut sum = ground();
    for _ in 0..32 {
        sum = Formula::BvAdd(bx(sum), bx(ground()), 64);
    }
    let lhs = ite(atom(2), sum, lit(0, 64));
    let items = vec![(lhs.clone(), lhs)];
    assert_eq!(prove(&items, BranchFilter::On), Err(Decline::Filter("branch: cap (steps)".into())));
    // 5 × 8 = 40 leaves (one atom) in one condition.
    let wide = Formula::Or(vec![Formula::And(vec![atom(2); 8]); 5]);
    let side = ite(wide, lit(1, 64), lit(2, 64));
    let items = vec![(side.clone(), side)];
    assert_eq!(
        prove(&items, BranchFilter::On),
        Err(Decline::Filter("branch: cap (condition)".into()))
    );
    // The walk counts nodes: 1 + 2 · 520 + 2 > 1024.
    let mut chain = x64();
    for _ in 0..520 {
        chain = Formula::BvAdd(bx(chain), bx(x64()), 64);
    }
    assert!(!branch_fragment(&ite(atom(2), chain.clone(), x64())));
    let mut short = x64();
    for _ in 0..400 {
        short = Formula::BvAdd(bx(short), bx(x64()), 64);
    }
    assert!(branch_fragment(&ite(atom(2), short, x64())));
}

/// S4: r02 (`lsr #1` + `msub` against the spec's `x % 2`, both conjuncts)
/// is `KernelInstantiated` through `zext_drop1_div2`. Its mutants are not,
/// and with the Rust checks bypassed the kernel's type check refuses each:
/// `lsr #2`, `movz #4`, a zero divisor in the spec (`1 << 64`, `6 & 9`),
/// the wrong ground choice, and one false conjunct among true ones (either
/// conjunct).
#[test]
fn r02_is_proved_and_its_mutants_are_not() {
    for name in R02 {
        let items = fixture(name);
        assert_eq!(items.len(), 2, "{name}");
        let got = prove(&items, BranchFilter::On);
        assert!(
            matches!(&got, Ok(e @ ProvenEvidence::KernelInstantiated { theorem, .. })
                if is_branch_label(e) && theorem.contains("Trust.BVS.zext_drop1_div2")),
            "{name}: {got:?}"
        );
        // Each conjunct alone is proved too.
        for item in &items {
            let one = vec![item.clone()];
            assert!(prove(&one, BranchFilter::On).is_ok(), "{name}: a conjunct alone");
        }
        let lsr2 = mutate_machine(&items, &|f| match f {
            Formula::BvZeroExt(x, 1) => match *x {
                Formula::BvExtract { inner, high: 63, low: 1 } => {
                    Formula::BvZeroExt(bx(Formula::BvExtract { inner, high: 63, low: 2 }), 2)
                }
                other => Formula::BvZeroExt(bx(other), 1),
            },
            other => other,
        });
        let movz4 = mutate_machine(&items, &|f| match f {
            Formula::BvMul(a, b, w) if matches!(&*a, Formula::BvZeroExt(..)) && is_lit(&b, 2) => {
                Formula::BvMul(a, bx(lit(4, 64)), w)
            }
            other => other,
        });
        let divisor = |d: Formula| {
            mutate_spec(&items, &move |f| match f {
                Formula::BvUDiv(a, b, w) if is_x(&a) && is_lit(&b, 2) => {
                    Formula::BvUDiv(a, bx(d.clone()), w)
                }
                other => other,
            })
        };
        let ground = mutate_spec(&items, &|f| match f {
            Formula::Ite(c, a, e) if matches!(&*e, Formula::BvUDiv(..)) => {
                Formula::Ite(bx(Formula::Not(c)), a, e)
            }
            other => other,
        });
        let mut check_false = items.clone();
        check_false[1].1 = lit(1, 1);
        let mutants = [
            ("lsr #2", lsr2),
            ("movz #4", movz4),
            ("spec x / (1 << 64)", divisor(lit(1i128 << 64, 64))),
            ("spec x / (6 & 9)", divisor(Formula::BvAnd(bx(lit(6, 64)), bx(lit(9, 64)), 64))),
            ("spec wrong ground choice", ground),
            ("the check conjunct false", check_false),
        ];
        for (what, m) in mutants {
            assert_ne!(m, items, "{name}: the mutant '{what}' changed nothing");
            // Exactly one conjunct is false; the other is the fixture's.
            let changed: Vec<usize> = (0..2).filter(|&i| m[i] != items[i]).collect();
            assert_eq!(changed.len(), 1, "{name}: '{what}' changed {changed:?}");
            assert!(prove(&m, BranchFilter::On).is_err(), "{name}: mutant '{what}' proved");
            let off = prove(&m, BranchFilter::Off);
            assert!(kernel_refused(&off), "{name}: mutant '{what}' with the filter off: {off:?}");
        }
    }
}

// ── faithfulness: the goal against SMT-LIB and ay ────────────────────────────

/// A closed SMT-LIB value: a Bool, or a bit-vector `(value, width)`.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Val {
    B(bool),
    V(u128, u32),
}

fn mask(w: u32) -> u128 {
    if w >= 128 { u128::MAX } else { (1u128 << w) - 1 }
}

/// SMT-LIB `QF_BV` semantics of a closed, well-sorted Formula, written here
/// from the SMT-LIB definitions (test-local, independent of the kernel's
/// operator definitions and of the reflection).
fn smt(f: &Formula) -> Val {
    let bv = |f: &Formula| match smt(f) {
        Val::V(v, w) => (v, w),
        other => panic!("not a bit-vector: {other:?}"),
    };
    let b = |f: &Formula| match smt(f) {
        Val::B(x) => x,
        other => panic!("not a Bool: {other:?}"),
    };
    let signed = |(v, w): (u128, u32)| {
        if (v >> (w - 1)) & 1 == 1 { v as i128 - (1i128 << w) } else { v as i128 }
    };
    let bin = |x: &Formula, y: &Formula, w: u32, op: &dyn Fn(u128, u128) -> u128| {
        Val::V(op(bv(x).0, bv(y).0) & mask(w), w)
    };
    match f {
        Formula::Bool(x) => Val::B(*x),
        Formula::BitVec { value, width } => Val::V((*value as u128) & mask(*width), *width),
        Formula::Not(x) => Val::B(!b(x)),
        Formula::And(xs) => Val::B(xs.iter().all(|x| b(x))),
        Formula::Or(xs) => Val::B(xs.iter().any(|x| b(x))),
        Formula::Ite(c, p, q) => {
            if b(c) {
                smt(p)
            } else {
                smt(q)
            }
        }
        Formula::Eq(x, y) => Val::B(smt(x) == smt(y)),
        Formula::BvULt(x, y, _) => Val::B(bv(x).0 < bv(y).0),
        Formula::BvULe(x, y, _) => Val::B(bv(x).0 <= bv(y).0),
        Formula::BvSLt(x, y, _) => Val::B(signed(bv(x)) < signed(bv(y))),
        Formula::BvAdd(x, y, w) => bin(x, y, *w, &|a, c| a.wrapping_add(c)),
        Formula::BvSub(x, y, w) => bin(x, y, *w, &|a, c| a.wrapping_sub(c)),
        Formula::BvMul(x, y, w) => bin(x, y, *w, &|a, c| a.wrapping_mul(c)),
        Formula::BvAnd(x, y, w) => bin(x, y, *w, &|a, c| a & c),
        Formula::BvOr(x, y, w) => bin(x, y, *w, &|a, c| a | c),
        Formula::BvXor(x, y, w) => bin(x, y, *w, &|a, c| a ^ c),
        Formula::BvShl(x, y, w) => {
            let ww = *w;
            bin(x, y, ww, &move |a, s| if s >= u128::from(ww) { 0 } else { a << s })
        }
        Formula::BvLShr(x, y, w) => {
            let ww = *w;
            bin(x, y, ww, &move |a, s| if s >= u128::from(ww) { 0 } else { a >> s })
        }
        // `bvashr`: the sign bit fills from the top; an amount at or past the
        // width leaves only sign bits.
        Formula::BvAShr(x, y, w) => {
            let (a, s) = (bv(x).0, bv(y).0);
            let v = signed((a, *w)) >> s.min(u128::from(*w) - 1).min(127);
            Val::V((v as u128) & mask(*w), *w)
        }
        Formula::BvUDiv(x, y, w) => {
            let ww = *w;
            bin(x, y, ww, &move |a, c| if c == 0 { mask(ww) } else { a / c })
        }
        Formula::BvZeroExt(x, k) => {
            let (v, w) = bv(x);
            Val::V(v, w + k)
        }
        // `sign_extend`: `k` copies of the sign bit above the operand.
        Formula::BvSignExt(x, k) => {
            let (v, w) = bv(x);
            let v = if (v >> (w - 1)) & 1 == 1 { v | (mask(w + k) & !mask(w)) } else { v };
            Val::V(v, w + k)
        }
        Formula::BvExtract { inner, high, low } => {
            let (v, _) = bv(inner);
            let w = high - low + 1;
            Val::V((v >> low) & mask(w), w)
        }
        other => panic!("outside the SMT evaluator: {other:?}"),
    }
}

/// `f` with `X0` replaced by the 64-bit literal `v`.
fn at(f: &Formula, v: u128) -> Formula {
    map(f, &|g| if is_x(&g) { lit(v as i128, 64) } else { g })
}

/// The closed instances of plan §5's faithfulness test.
fn smt_cases() -> Vec<Formula> {
    let mut out = Vec::new();
    let values = |w: u32| -> Vec<u128> {
        let mut v = vec![0, 1, mask(w), 1u128 << (w - 1)];
        if w > 2 {
            v.push(2);
            v.push(0x5a5a_5a5a_5a5a_5a5a & mask(w));
        }
        v.sort_unstable();
        v.dedup();
        v
    };
    let l = |v: u128, w: u32| lit(v as i128, w);
    for w in [1, 32, 64] {
        let vs = values(w);
        for &a in &vs {
            for &c in &vs {
                let (x, y) = (l(a, w), l(c, w));
                let bxy = |f: fn(Box<Formula>, Box<Formula>, u32) -> Formula| {
                    f(bx(x.clone()), bx(y.clone()), w)
                };
                out.push(feq(x.clone(), y.clone()));
                out.push(bxy(Formula::BvULt));
                out.push(bxy(Formula::BvULe));
                out.push(bxy(Formula::BvSLt));
                out.push(bxy(Formula::BvAdd));
                out.push(bxy(Formula::BvSub));
                out.push(bxy(Formula::BvMul));
                out.push(bxy(Formula::BvAnd));
                out.push(bxy(Formula::BvOr));
                out.push(bxy(Formula::BvXor));
                out.push(bxy(Formula::BvUDiv));
                // A bit-vector Ite on a comparison, both ways.
                out.push(ite(bxy(Formula::BvULt), x.clone(), y.clone()));
                out.push(ite(bxy(Formula::BvSLt), y.clone(), x.clone()));
            }
            // Shifts, including shift amounts at and past the width.
            for s in [0, 1, u128::from(w - 1), u128::from(w), u128::from(w) + 1] {
                if s > mask(w) {
                    continue;
                }
                out.push(Formula::BvShl(bx(l(a, w)), bx(l(s, w)), w));
                out.push(Formula::BvLShr(bx(l(a, w)), bx(l(s, w)), w));
            }
            // Each literal Ite condition.
            for c in [true, false] {
                out.push(ite(Formula::Bool(c), l(a, w), l(!a & mask(w), w)));
            }
        }
    }
    // Divisors 0, a masked 1 << 64 and powers of two, at width 64.
    for a in [0u128, 7, u128::from(u64::MAX), 1 << 63] {
        let x = l(a, 64);
        for d in [0i128, 1i128 << 64, 1, 2, 4, 1 << 32, 1 << 63, 3] {
            out.push(Formula::BvUDiv(bx(x.clone()), bx(lit(d, 64)), 64));
        }
        out.push(Formula::BvUDiv(
            bx(x.clone()),
            bx(Formula::BvAnd(bx(lit(6, 64)), bx(lit(9, 64)), 64)),
            64,
        ));
        // The high extract, k in {1, 32, 63}, and the low extracts.
        for k in [1, 32, 63] {
            out.push(Formula::BvExtract { inner: bx(x.clone()), high: 63, low: k });
        }
        out.push(Formula::BvExtract { inner: bx(x.clone()), high: 0, low: 0 });
        out.push(Formula::BvExtract { inner: bx(x.clone()), high: 31, low: 0 });
        out.push(Formula::BvZeroExt(
            bx(Formula::BvExtract { inner: bx(x.clone()), high: 63, low: 1 }),
            1,
        ));
    }
    out.push(Formula::BvExtract { inner: bx(l(0xdead_beef, 32)), high: 31, low: 1 });
    out.push(Formula::BvZeroExt(bx(l(0xdead_beef, 32)), 32));
    out.push(Formula::BvZeroExt(bx(l(1, 1)), 63));
    // The arithmetic shift: amounts 0, 1, w-1 and w (and w+1 where it fits)
    // on INT_MIN, -1, 0, 1 and a pattern, at widths 1, 8, 32 and 64.
    for w in [1u32, 8, 32, 64] {
        let int_min = 1u128 << (w - 1);
        for a in [int_min, mask(w), 0, 1, 0x5a5a_5a5a_5a5a_5a5a & mask(w)] {
            for s in [0, 1, u128::from(w - 1), u128::from(w), u128::from(w) + 1] {
                if s > mask(w) {
                    continue;
                }
                out.push(Formula::BvAShr(bx(l(a, w)), bx(l(s, w)), w));
            }
        }
    }
    // The sign extension, sign bit 0 and 1, to 64 bits and to a middle width.
    for (w, k) in [(1u32, 63u32), (1, 7), (8, 56), (8, 24), (32, 32), (32, 1), (63, 1)] {
        for a in [0, 1, mask(w), 1u128 << (w - 1), 0x5a5a_5a5a_5a5a_5a5a & mask(w)] {
            out.push(Formula::BvSignExt(bx(l(a, w)), k));
        }
    }
    // The amount s10's spec computes, and the arithmetic shift by it.
    out.push(s10_amount());
    out.push(Formula::BvAShr(bx(l(1 << 63, 64)), bx(s10_amount()), 64));
    // Bool Ite in both polarities, and the connectives.
    let t = Formula::Bool(true);
    let fl = Formula::Bool(false);
    let lt = ult(l(1, 8), l(2, 8), 8);
    let ge = ult(l(2, 8), l(1, 8), 8);
    for c in [t.clone(), fl.clone(), lt.clone(), ge.clone()] {
        // An equality of two conditions, each pair.
        for d in [t.clone(), fl.clone(), lt.clone(), ge.clone()] {
            out.push(feq(c.clone(), d));
        }
        out.push(ite(c.clone(), t.clone(), fl.clone()));
        out.push(ite(c.clone(), fl.clone(), t.clone()));
        out.push(ite(c.clone(), lt.clone(), ge.clone()));
        out.push(Formula::Not(bx(c.clone())));
        out.push(Formula::And(vec![c.clone(), lt.clone(), t.clone()]));
        out.push(Formula::Or(vec![fl.clone(), c.clone()]));
        out.push(Formula::And(vec![c.clone()]));
    }
    // The fixtures' sides at chosen values of `X0`.
    for name in DISTINCT {
        for (lft, rgt) in fixture(name) {
            for v in [0u128, 1, 2, 3, 99, 100, 101, 102, 1 << 63, u128::from(u64::MAX)] {
                out.push(at(&lft, v));
                out.push(at(&rgt, v));
            }
        }
    }
    // s10's sides, and the flag condition on its own, across the signed
    // boundary and at INT_MIN / INT_MAX.
    for (_, items) in s10() {
        for (lft, rgt) in items {
            let Formula::Ite(cond, ..) = &lft else { panic!("s10's machine side is an Ite") };
            for v in S10_VALUES {
                out.push(at(&lft, v));
                out.push(at(&rgt, v));
                out.push(at(cond, v));
            }
        }
    }
    out
}

/// `X0` values at which the s10 sides are evaluated: around 100 and the
/// signed boundary (INT_MIN, INT_MAX, -1, -100).
const S10_VALUES: [u128; 10] = [
    0,
    1,
    99,
    100,
    101,
    1 << 63,
    (1 << 63) - 1,
    u64::MAX as u128,
    (u64::MAX - 99) as u128,
    (1 << 63) + 100,
];

/// The goal reflection means what the Formula means. For each closed case
/// the kernel computes `bvfEval R(f)` (or `B(f)`) under `branching_goal` to
/// the SMT-LIB value (`Eq.refl` checks) and refuses the value with its low
/// bit flipped (or the other Bool); ay proves `f = value` valid and finds a
/// counterexample to the flipped value. The cases cover plan §5's edge
/// inputs and every fixture side at ten values of `X0`.
#[test]
fn branch_reflection_agrees_with_smt() {
    let cases: Vec<(Formula, Val)> = smt_cases()
        .into_iter()
        .map(|f| {
            let v = smt(&f);
            (f, v)
        })
        .collect();
    // The fixtures are true obligations under SMT-LIB semantics.
    for name in DISTINCT {
        for (lft, rgt) in fixture(name) {
            for v in [0u128, 1, 2, 3, 99, 100, 101, 102, 1 << 63, u128::from(u64::MAX)] {
                assert_eq!(smt(&at(&lft, v)), smt(&at(&rgt, v)), "{name} at X0 = {v}");
            }
        }
    }
    for (name, items) in s10() {
        for (lft, rgt) in items {
            for v in S10_VALUES {
                assert_eq!(smt(&at(&lft, v)), smt(&at(&rgt, v)), "{name} at X0 = {v}");
            }
        }
    }
    let n = cases.len();
    let kernel_cases = cases.clone();
    let bad = run_recheck_thread("branch-smt", move || {
        let env = branch_theory::branch_base().expect("base").clone();
        // One checker per check: the heartbeat budget is per checker.
        let check =
            |e: &Expr, ty: &Expr| TypeChecker::with_mode(&env, env.mode()).check_type(e, ty);
        let mut bad = Vec::new();
        for (f, want) in &kernel_cases {
            let mut ctx = ReflectCtx::branching_goal();
            let (stated, good, flip) = match want {
                Val::V(v, w) => match reflect_formula(f, &mut ctx) {
                    Ok(r) => {
                        (kx::evalf(r.bvf), kx::bits(*v as i128, *w), kx::bits((*v ^ 1) as i128, *w))
                    }
                    Err(e) => {
                        bad.push(format!("{f:?}: the goal reflection refused it: {e}"));
                        continue;
                    }
                },
                Val::B(b) => match bool_goal(f, &mut ctx) {
                    Ok(g) => {
                        let lit = |x: bool| if x { kx::btrue() } else { kx::bfalse() };
                        (g, lit(*b), lit(!*b))
                    }
                    Err(e) => {
                        bad.push(format!("{f:?}: B refused it: {e}"));
                        continue;
                    }
                },
            };
            let ty = if matches!(want, Val::B(_)) { bool_ty() } else { lb() };
            let ok = check(&refl(ty.clone(), good.clone()), &eq(ty.clone(), stated.clone(), good));
            if let Err(e) = ok {
                bad.push(format!("{f:?}: the kernel did not compute {want:?}: {e:?}"));
            }
            // A refusal for lack of budget is not a refusal of the value.
            match check(&refl(ty.clone(), flip.clone()), &eq(ty, stated, flip)) {
                Err(e) if format!("{e:?}").starts_with("TypeMismatch") => {}
                other => bad.push(format!("{f:?}: the flipped value of {want:?}: {other:?}")),
            }
        }
        bad
    })
    .expect("kernel thread");
    assert!(bad.is_empty(), "{} of {n} cases disagree:\n{}", bad.len(), bad.join("\n"));
    // ay, on the same cases.
    let mut ay_bad = Vec::new();
    for (f, want) in &cases {
        let (claim, flipped) = match *want {
            Val::V(v, w) => {
                (feq(f.clone(), lit(v as i128, w)), feq(f.clone(), lit((v ^ 1) as i128, w)))
            }
            Val::B(true) => (f.clone(), Formula::Not(bx(f.clone()))),
            Val::B(false) => (Formula::Not(bx(f.clone())), f.clone()),
        };
        if !matches!(discharge_valid(&claim), Discharge::Proven) {
            ay_bad.push(format!("{f:?}: ay did not prove {want:?}"));
        }
        if !matches!(discharge_valid(&flipped), Discharge::CounterExample) {
            ay_bad.push(format!("{f:?}: ay found no counterexample to the flipped {want:?}"));
        }
    }
    assert!(
        ay_bad.is_empty(),
        "{} of {n} cases disagree with ay:\n{}",
        ay_bad.len(),
        ay_bad.join("\n")
    );
    println!("branch_reflection_agrees_with_smt: {n} cases");
}

// ── conjunctions with no atoms (s07_local_call) ──────────────────────────────

/// s07_local_call at O0 (`fixtures/HEADER.md`): five Ite-free items, two
/// ground reach indicators `Ite(true, 1, 0)`, two call arguments and the
/// result over the call-result leaves `CER_R@24` / `CER_R@30`, the machine
/// side under `mov` (ORR from XZR) wrappers `BvOr(0, v)`. Not in [`DISTINCT`]:
/// the legacy pin is the parent's, and `branch_reflection_agrees_with_smt`'s
/// `at` substitutes only `X0`.
const S07: &str = "s07_local_call-O0-aarch64-apple-darwin";

fn label_of(e: &ProvenEvidence) -> Option<&str> {
    match e {
        ProvenEvidence::KernelInstantiated { theorem, original: None } => Some(theorem.as_str()),
        _ => None,
    }
}

/// s07's label, measured (2026-11-14, `s07_is_proved_without_atoms` and the
/// gate's `s07_local_call_is_kernel_proved_without_atoms`): the zero-wrapper
/// strip (`bvf_or_cong` over `bvf_or_zero_id`), `bvf_add_cong` above it, and
/// `ite_cong` from `reflect_value`'s congruence over the top-level reach
/// indicators `Ite(true, 1, 0)`, which stay `Ite`s in both views. No
/// `ite_true` / `ite_false`: the two views of each s07 item are equal, so each
/// closes by `Eq.refl` and none reaches `Split::select` (an atom-free item
/// whose views differ can: `atom_free_literal_condition_closes_by_selection`).
const S07_LABEL: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_or_cong+Clean.BVC.bvf_or_zero_id+\
                         Trust.BVB.ite_cong+kernel atom case split (O(1) branching conjunction, \
                         BRANCH-SPLIT-1)";

/// The route's label on s07, whose conjunction has no atoms.
fn is_atom_free_label(e: &ProvenEvidence) -> bool {
    label_of(e).is_some_and(|t| t == S07_LABEL && t.ends_with(branch_theory::LABEL_TAIL))
}

/// BRANCH-SPLIT-1 on a conjunction with no atoms: s07 is proved with the
/// Rust checks on and off, the declared type is the goal built from the items
/// alone, and the label is the atom-free one.
#[test]
fn s07_is_proved_without_atoms() {
    let items = fixture(S07);
    assert_eq!(items.len(), 5);
    let routed = super::try_branch_split_conjunction(&items);
    assert!(routed.as_ref().is_some_and(is_atom_free_label), "the route gave {routed:?}");
    let off = prove(&items, BranchFilter::Off);
    assert!(matches!(&off, Ok(e) if is_atom_free_label(e)), "with the filter off: {off:?}");
    let mut ctx = ReflectCtx::branching_goal();
    let mut eqs = Vec::new();
    for (l, r) in &items {
        let rl = reflect_formula(l, &mut ctx).expect("goal");
        let rr = reflect_formula(r, &mut ctx).expect("goal");
        eqs.push(kx::eq_list(kx::evalf(rl.bvf), kx::evalf(rr.bvf)));
    }
    let mut reference = eqs.pop().expect("one item");
    while let Some(e) = eqs.pop() {
        reference = Expr::apps(Expr::const_str("And"), [e, reference]);
    }
    DECLARED.with(|d| *d.borrow_mut() = None);
    prove(&items, BranchFilter::On).expect("s07");
    let declared = DECLARED.with(|d| d.borrow_mut().take()).expect("the hook saw no type");
    assert_eq!(declared, reference);
}

/// s07's mutants, each with exactly one item false: not proved, and with the
/// Rust checks bypassed it is the kernel's type check that refuses each.
#[test]
fn s07_mutants_are_refused_by_the_kernel() {
    let items = fixture(S07);
    let var64 = |n: &str| var(n, 64);
    let or0 = |v: Formula| Formula::BvOr(bx(lit(0, 64)), bx(v), 64);
    let add = |a: Formula, b: Formula| Formula::BvAdd(bx(a), bx(b), 64);
    let at = |i: usize, machine: Option<Formula>, spec: Option<Formula>| {
        let mut m = items.clone();
        if let Some(f) = machine {
            m[i].0 = f;
        }
        if let Some(f) = spec {
            m[i].1 = f;
        }
        m
    };
    let mutants = [
        ("item 3 machine +1 -> +2", at(3, Some(add(or0(x64()), lit(2, 64))), None)),
        (
            "item 4 machine CER_R@30 -> CER_R@24",
            at(4, Some(or0(add(or0(var64("CER_R@24")), var64("CER_R@24")))), None),
        ),
        ("item 1 machine X0 -> X1", at(1, Some(var64("X1")), None)),
        (
            "item 3 machine BvOr(0, X0) -> BvOr(1, X0)",
            at(3, Some(add(Formula::BvOr(bx(lit(1, 64)), bx(x64()), 64), lit(1, 64))), None),
        ),
        (
            "item 0 spec Ite(true, 1, 0) -> Ite(false, 1, 0)",
            at(0, None, Some(ite(Formula::Bool(false), lit(1, 1), lit(0, 1)))),
        ),
    ];
    for (what, m) in mutants {
        let changed: Vec<usize> = (0..items.len()).filter(|&i| m[i] != items[i]).collect();
        assert_eq!(changed.len(), 1, "'{what}' changed {changed:?}");
        let on = prove(&m, BranchFilter::On);
        assert!(on.is_err(), "mutant '{what}' proved: {on:?}");
        let off = prove(&m, BranchFilter::Off);
        assert!(kernel_refused(&off), "mutant '{what}' with the filter off: {off:?}");
    }
}

/// An atom-free item whose views differ, `Ite(true, X0, X1) = X0`, closes by
/// the kernel-checked leaf selection (`ite_true`), not by `Eq.refl`: with no
/// atoms `Split::go` builds no `Bool.rec` but still selects the arm a literal
/// condition decides. With the condition `false` the item is false, and with
/// the Rust checks bypassed the kernel refuses the term. This is what an
/// `Eq.refl` shortcut for atom-free items would get wrong.
#[test]
fn atom_free_literal_condition_closes_by_selection() {
    let item = |c: bool| vec![(ite(Formula::Bool(c), x64(), var("X1", 64)), x64())];
    let selected = |e: &ProvenEvidence| {
        is_branch_label(e) && label_of(e).is_some_and(|t| t.contains("Trust.BVB.ite_true"))
    };
    for filter in [BranchFilter::On, BranchFilter::Off] {
        let got = prove(&item(true), filter);
        assert!(matches!(&got, Ok(e) if selected(e)), "{filter:?}: {got:?}");
    }
    assert!(prove(&item(false), BranchFilter::On).is_err(), "Ite(false, X0, X1) = X0 proved");
    let off = prove(&item(false), BranchFilter::Off);
    assert!(kernel_refused(&off), "Ite(false, X0, X1) = X0 with the filter off: {off:?}");
}

/// s07 with the two call results added in the other order
/// (`branch_split_gate.rs` `s07_commuted_sum_is_an_equivalent_twin_the_route_declines`,
/// its conj as `TRUST_GATE_TRACE=1` captured it on both triples, 2026-11-14):
/// the item is true, but the route has no operand-order step, so the arms it
/// reaches differ and it declines for exactly that reason.
#[test]
fn s07_commuted_sum_is_declined_because_the_arms_differ() {
    let mut items = fixture(S07);
    let or0 = |v: Formula| Formula::BvOr(bx(lit(0, 64)), bx(v), 64);
    let (r24, r30) = (var("CER_R@24", 64), var("CER_R@30", 64));
    assert_eq!(items[4].0, or0(Formula::BvAdd(bx(or0(r24.clone())), bx(r30.clone()), 64)));
    items[4].0 = or0(Formula::BvAdd(bx(r30), bx(or0(r24)), 64));
    assert_eq!(
        prove(&items, BranchFilter::On),
        Err(Decline::Filter("branch: the arms of a case differ".into()))
    );
}

/// An ill-sorted item with no atoms (a 64-bit side against a 32-bit extract)
/// is refused by the walk, with the filter on and off: dropping the
/// precondition left the walk inside the goal.
#[test]
fn an_ill_sorted_atom_free_item_is_refused_by_the_walk() {
    let narrow = Formula::BvExtract { inner: bx(x64()), high: 31, low: 0 };
    let items = vec![(x64(), narrow)];
    let walk = Decline::Filter("branch: a side is outside the width walk".into());
    for filter in [BranchFilter::On, BranchFilter::Off] {
        assert_eq!(prove(&items, filter), Err(walk.clone()), "{filter:?}");
    }
}

// ── the closed-branch fold's value at O2 (s23_enum_local) ────────────────────

/// The folded s23 O2 value's label, measured (2026-11-14, here and in
/// `call_event/closed_branch/tests.rs` `s23_o2_value_is_proved_by_the_branch_split`):
/// the `tbz` bridge (concrete leaf bits, by `Eq.refl`) and `beq_and_lowbit`
/// meet on bit 0 of `X0`, split once, and each leaf selects its arms.
const S23_O2_LABEL: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_and_cong+Trust.BVB.beq_and_lowbit+\
                            Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVB.ite_true+kernel atom \
                            case split (O(1) branching conjunction, BRANCH-SPLIT-1)";

/// `X0[0:0] == 0`: the machine's `tbz w0, #0` test.
fn tbz0() -> Formula {
    feq(Formula::BvExtract { inner: bx(x64()), high: 0, low: 0 }, lit(0, 1))
}

/// s23's value item at O2 after `call_event/closed_branch.rs` folded its two
/// ground tag tests and canonicalized the spec's carrier: the machine's `tbz`
/// test against the spec's `x & 1 == 0`, both arms `5` and `x + 1`.
fn s23_folded(machine_test: Formula) -> Items {
    let x1 = Formula::BvAdd(bx(x64()), bx(lit(1, 64)), 64);
    let spec_test = feq(Formula::BvAnd(bx(x64()), bx(lit(1, 64)), 64), lit(0, 64));
    vec![(ite(machine_test, lit(5, 64), x1.clone()), ite(spec_test, lit(5, 64), x1))]
}

/// The folded s23 O2 value is proved by the route (the `tbz` and `beq_and_lowbit`
/// bridges meet on one atom). Its mutants are not, and with the Rust checks
/// bypassed the kernel refuses each: the spec's arms swapped, the machine
/// testing the low two bits (`Extract{1,0} == 0`), and the machine arms both
/// `5` (the `E::B` tag test folded wrongly). The `tbz #1` mutant
/// (`Extract{1,1}`) is outside the walk, so the goal refuses it under both
/// filters.
#[test]
fn s23_folded_value_is_proved_and_its_mutants_are_not() {
    let items = s23_folded(tbz0());
    let got = prove(&items, BranchFilter::On);
    assert!(matches!(&got, Ok(e) if is_branch_label(e)), "{got:?}");
    assert_eq!(got.as_ref().ok().and_then(label_of), Some(S23_O2_LABEL));
    assert!(matches!(&prove(&items, BranchFilter::Off), Ok(e) if is_branch_label(e)));
    let swapped = swap_spec_arms(&items);
    let two_bits =
        s23_folded(feq(Formula::BvExtract { inner: bx(x64()), high: 1, low: 0 }, lit(0, 2)));
    let mut both_five = items.clone();
    both_five[0].0 = ite(tbz0(), lit(5, 64), lit(5, 64));
    for (what, m) in
        [("spec arms swapped", swapped), ("low two bits", two_bits), ("arms 5, 5", both_five)]
    {
        assert!(prove(&m, BranchFilter::On).is_err(), "'{what}' proved");
        let off = prove(&m, BranchFilter::Off);
        assert!(kernel_refused(&off), "'{what}' with the filter off: {off:?}");
    }
    let bit1 = s23_folded(feq(Formula::BvExtract { inner: bx(x64()), high: 1, low: 1 }, lit(0, 1)));
    let walk = Decline::Filter("branch: a side is outside the width walk".into());
    for filter in [BranchFilter::On, BranchFilter::Off] {
        assert_eq!(prove(&bit1, filter), Err(walk.clone()), "tbz #1, {filter:?}");
    }
}

/// The route's obligation (G, the proof term and the leaves) on every conj it
/// proved before s10: the distinct r02/s04/s05 fixtures, s07 and the folded
/// s23 O2 value.
fn branch_proof_dump() -> String {
    use std::fmt::Write as _;
    let mut cases: Vec<(String, Items)> =
        DISTINCT.iter().map(|n| (n.to_string(), fixture(n))).collect();
    cases.push((S07.to_string(), fixture(S07)));
    cases.push(("s23 O2 folded".to_string(), s23_folded(tbz0())));
    let mut s = String::new();
    for (name, items) in cases {
        match obligation(&items, BranchFilter::On) {
            Ok(ob) => {
                writeln!(s, "{name}\n{:?}\n{:?}\n{:?}", ob.goal, ob.proof, ob.leaves).unwrap()
            }
            Err(d) => writeln!(s, "{name} Err {d:?}").unwrap(),
        }
    }
    s
}

/// The proving terms of r02/s04/s05/s07/s23 are byte for byte the parent's:
/// s10's new walk arms, flag bridge and shift-amount fold change no term the
/// route built before. Measured 2026-11-14 on the parent blobs (branch_split.rs
/// 1dc8e025, branch_reflect.rs 76c7c87f, branch_theory.rs 974c9e1f, with
/// verify_output_instantiate.rs and this file at 8bbb1226c3 plus this test) by
/// `targo --unverified test -p trust-cg-bridge --features kernel-recheck,test-hooks
/// --lib -- branch_proof --nocapture`; the value equals this tree's.
#[test]
fn branch_proofs_are_byte_pinned_on_the_fixtures() {
    let s = branch_proof_dump();
    assert!(!s.contains(" Err "), "a pinned conj no longer builds:\n{s}");
    println!("BRANCH_PROOF_PIN ({}, {})", s.len(), fnv1a(&s));
    assert_eq!((s.len(), fnv1a(&s)), BRANCH_PROOF_PIN, "BRANCH_PROOF_PIN");
}
const BRANCH_PROOF_PIN: (usize, u64) = (261459387, 15557453021653289454);

// ── s10_signed: the signed flags, the arithmetic shift, the sign extension ───

/// s10_signed's step-(5) conj (`h(a: i64) -> i64 { if a < 100 { a - 200 }
/// else { a >> 2 } }`), as the branch split's own `TRUST_GATE_TRACE=1` line
/// `[branch-split] conj <json>` printed it on 2026-11-14 (before this route
/// admitted it: "a side is outside the width walk"), for `h` in the gate's
/// configuration (`branch_split_gate.rs`
/// `S10_IR`). O0: the machine side is `b.lt`'s `N != V` after `cmp x0, #100`,
/// the arms under the `mov` wrappers `BvOr(0, v)`, the shift amount
/// `sxtw(2) & 63` modeled as ASRV's `amount & 63`; the spec's amount is
/// `sext(2) & 63`, the same Formula. The `aarch64-unknown-linux-gnu` capture
/// is byte-identical.
const S10_O0: &str = r#"[[{"Ite":[{"Not":{"Eq":[{"Eq":[{"BvExtract":{"inner":{"BvSub":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":100,"width":64}},64]},"high":63,"low":63}},{"BitVec":{"value":1,"width":1}}]},{"And":[{"Not":{"Eq":[{"BvExtract":{"inner":{"Var":["X0",{"BitVec":64}]},"high":63,"low":63}},{"BvExtract":{"inner":{"BitVec":{"value":100,"width":64}},"high":63,"low":63}}]}},{"Not":{"Eq":[{"BvExtract":{"inner":{"BvSub":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":100,"width":64}},64]},"high":63,"low":63}},{"BvExtract":{"inner":{"Var":["X0",{"BitVec":64}]},"high":63,"low":63}}]}}]}]}},{"BvOr":[{"BitVec":{"value":0,"width":64}},{"BvSub":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":200,"width":64}},64]},64]},{"BvOr":[{"BitVec":{"value":0,"width":64}},{"BvAShr":[{"Var":["X0",{"BitVec":64}]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":2,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]},64]}]},{"Ite":[{"Not":{"Eq":[{"Ite":[{"BvSLt":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":100,"width":64}},64]},{"BitVec":{"value":1,"width":32}},{"BitVec":{"value":0,"width":32}}]},{"BitVec":{"value":0,"width":32}}]}},{"BvSub":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":200,"width":64}},64]},{"BvAShr":[{"Var":["X0",{"BitVec":64}]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":2,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]}]}]]"#;

/// The same at O2 (the same conj for `h` and for `rung`, which inlines it, on
/// both triples): the machine's amount is the literal `2 & 63`, so the two
/// amounts differ until the shift-amount fold makes both `Const 2`.
const S10_O2: &str = r#"[[{"Ite":[{"Not":{"Eq":[{"Eq":[{"BvExtract":{"inner":{"BvSub":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":100,"width":64}},64]},"high":63,"low":63}},{"BitVec":{"value":1,"width":1}}]},{"And":[{"Not":{"Eq":[{"BvExtract":{"inner":{"Var":["X0",{"BitVec":64}]},"high":63,"low":63}},{"BvExtract":{"inner":{"BitVec":{"value":100,"width":64}},"high":63,"low":63}}]}},{"Not":{"Eq":[{"BvExtract":{"inner":{"BvSub":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":100,"width":64}},64]},"high":63,"low":63}},{"BvExtract":{"inner":{"Var":["X0",{"BitVec":64}]},"high":63,"low":63}}]}}]}]}},{"BvOr":[{"BitVec":{"value":0,"width":64}},{"BvSub":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":200,"width":64}},64]},64]},{"BvOr":[{"BitVec":{"value":0,"width":64}},{"BvAShr":[{"Var":["X0",{"BitVec":64}]},{"BvAnd":[{"BitVec":{"value":2,"width":64}},{"BitVec":{"value":63,"width":64}},64]},64]},64]}]},{"Ite":[{"Not":{"Eq":[{"Ite":[{"BvSLt":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":100,"width":64}},64]},{"BitVec":{"value":1,"width":32}},{"BitVec":{"value":0,"width":32}}]},{"BitVec":{"value":0,"width":32}}]}},{"BvSub":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":200,"width":64}},64]},{"BvAShr":[{"Var":["X0",{"BitVec":64}]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":2,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]}]}]]"#;

fn s10() -> Vec<(String, Items)> {
    [("s10_signed O0", S10_O0), ("s10_signed O2", S10_O2)]
        .into_iter()
        .map(|(n, t)| (n.to_string(), serde_json::from_str(t).expect("s10 conj parses")))
        .collect()
}

/// The spec's shift amount, `sext(2:32) & 63 & 63`.
fn s10_amount() -> Formula {
    let and63 = |f: Formula| Formula::BvAnd(bx(f), bx(lit(63, 64)), 64);
    and63(and63(Formula::BvSignExt(bx(lit(2, 32)), 32)))
}

/// What every s10 proof must name: the signed flag bridge and the arm
/// selection.
fn is_s10_label(e: &ProvenEvidence) -> bool {
    is_branch_label(e) && label_of(e).is_some_and(|t| t.contains(names::SLT_FLAGS))
}

/// The machine condition `Not(Eq(N == 1, V))` (`b.lt` after `cmp x, k`) at
/// width `w`, or `Eq(N == 1, V)` (`b.ge`) when `lt` is false.
fn flag_cond(x: Formula, k: Formula, w: u32, lt: bool) -> Formula {
    let sign = |f: Formula| Formula::BvExtract { inner: bx(f), high: w - 1, low: w - 1 };
    let d = Formula::BvSub(bx(x.clone()), bx(k.clone()), w);
    let n = feq(sign(d.clone()), lit(1, 1));
    let v = Formula::And(vec![
        Formula::Not(bx(feq(sign(x.clone()), sign(k)))),
        Formula::Not(bx(feq(sign(d), sign(x)))),
    ]);
    let ge = feq(n, v);
    if lt { Formula::Not(bx(ge)) } else { ge }
}

/// The machine side of an s10 item, rewritten by `g` inside its condition
/// only (the arms are left as captured).
fn mutate_machine_cond(items: &Items, g: &dyn Fn(Formula) -> Formula) -> Items {
    items
        .iter()
        .map(|(l, r)| match l {
            Formula::Ite(c, a, e) => (ite(map(c, g), (**a).clone(), (**e).clone()), r.clone()),
            other => (other.clone(), r.clone()),
        })
        .collect()
}

/// BRANCH-SPLIT-1 for s10_signed: both captured conjs are proved, with the
/// Rust checks on and off, through `Trust.BVB.slt_flags`; each mutant is not
/// proved, and with the Rust checks bypassed it is the kernel's type check
/// that refuses it. The mutants are the signed-flag ones (the second operand's
/// sign in V, `N == 0`, the difference reversed, `N` read from two bits), a
/// spec `ult` against the machine's `b.lt`, a machine shift by 1, a spec shift
/// by 3, a machine `sub #201`, and the spec's arms swapped. (A machine `lsr
/// #2` is not among them: under `x >= 100` it equals `asr #2`, so it is a
/// true obligation, not a mutant.)
#[test]
fn s10_signed_is_proved_and_its_mutants_are_refused_by_the_kernel() {
    let k100 = lit(100, 64);
    let ext = |f: Formula, h: u32, l: u32| Formula::BvExtract { inner: bx(f), high: h, low: l };
    let sub100 = Formula::BvSub(bx(x64()), bx(k100.clone()), 64);
    for (name, items) in s10() {
        let on = prove(&items, BranchFilter::On);
        assert!(matches!(&on, Ok(e) if is_s10_label(e)), "{name}: {on:?}");
        let off = prove(&items, BranchFilter::Off);
        assert!(matches!(&off, Ok(e) if is_s10_label(e)), "{name} with the filter off: {off:?}");
        println!("S10_LABEL {name}: {:?}", on.as_ref().ok().and_then(label_of));
        let (s1, x1, k1, sub1) = (sub100.clone(), x64(), k100.clone(), sub100.clone());
        let mutants: Vec<(&str, Items)> = vec![
            (
                "V reads the second operand's sign for the first's",
                mutate_machine_cond(&items, &move |f| match f {
                    Formula::Eq(a, b)
                        if *a == ext(s1.clone(), 63, 63) && *b == ext(x1.clone(), 63, 63) =>
                    {
                        feq(*a, ext(k1.clone(), 63, 63))
                    }
                    other => other,
                }),
            ),
            (
                "N compared with 0:1",
                mutate_machine_cond(&items, &|f| match f {
                    Formula::Eq(a, b)
                        if is_lit(&b, 1) && matches!(*b, Formula::BitVec { width: 1, .. }) =>
                    {
                        feq(*a, lit(0, 1))
                    }
                    other => other,
                }),
            ),
            (
                "the difference reversed (k - x)",
                mutate_machine_cond(&items, &move |f| {
                    if f == sub1 { Formula::BvSub(bx(lit(100, 64)), bx(x64()), 64) } else { f }
                }),
            ),
            (
                "N read from bits 63..62",
                mutate_machine_cond(&items, &|f| match f {
                    Formula::Eq(a, b)
                        if matches!(&*a, Formula::BvExtract { inner, .. } if matches!(**inner, Formula::BvSub(..)))
                            && matches!(*b, Formula::BitVec { width: 1, .. }) =>
                    {
                        let Formula::BvExtract { inner, .. } = *a else { unreachable!() };
                        feq(Formula::BvExtract { inner, high: 63, low: 62 }, lit(1, 2))
                    }
                    other => other,
                }),
            ),
            (
                "spec x < 100 unsigned",
                mutate_spec(&items, &|f| match f {
                    Formula::BvSLt(a, b, w) => Formula::BvULt(a, b, w),
                    other => other,
                }),
            ),
            ("machine asr #2 -> #1", mutate_machine(&items, &relit(2, 1))),
            (
                "spec shift by 3",
                mutate_spec(&items, &|f| match f {
                    Formula::BvSignExt(x, k) if is_lit(&x, 2) => {
                        Formula::BvSignExt(bx(lit(3, 32)), k)
                    }
                    other => other,
                }),
            ),
            ("machine sub #200 -> #201", mutate_machine(&items, &relit(200, 201))),
            ("spec swapped arms", swap_spec_arms(&items)),
        ];
        for (what, m) in mutants {
            assert_ne!(m, items, "{name}: the mutant '{what}' changed nothing");
            assert!(prove(&m, BranchFilter::On).is_err(), "{name}: mutant '{what}' proved");
            let off = prove(&m, BranchFilter::Off);
            assert!(kernel_refused(&off), "{name}: mutant '{what}' with the filter off: {off:?}");
        }
    }
}

/// The flag bridge at widths 8, 32 and 64, both polarities: `b.lt` (`N !=
/// V`) against the spec's `x <s 100`, and `b.ge` (`N == V`) against the same
/// compare with the arms swapped, are proved through `slt_flags`. `b.ge`
/// against the unswapped arms (the wrong polarity) is not, and with the Rust
/// checks bypassed the kernel refuses it.
#[test]
fn flag_bridge_is_kernel_checked_at_each_width() {
    for w in [8u32, 32, 64] {
        let x = var("X0", w);
        let k = lit(100, w);
        let slt = Formula::BvSLt(bx(x.clone()), bx(k.clone()), w);
        let spec = ite(slt, lit(1, w), lit(2, w));
        let lt = vec![(
            ite(flag_cond(x.clone(), k.clone(), w, true), lit(1, w), lit(2, w)),
            spec.clone(),
        )];
        let ge = vec![(
            ite(flag_cond(x.clone(), k.clone(), w, false), lit(2, w), lit(1, w)),
            spec.clone(),
        )];
        for (what, items) in [("b.lt", &lt), ("b.ge", &ge)] {
            let got = prove(items, BranchFilter::On);
            assert!(matches!(&got, Ok(e) if is_s10_label(e)), "w = {w} {what}: {got:?}");
        }
        let wrong = vec![(ite(flag_cond(x, k, w, false), lit(1, w), lit(2, w)), spec)];
        assert!(prove(&wrong, BranchFilter::On).is_err(), "w = {w}: b.ge with b.lt's arms");
        let off = prove(&wrong, BranchFilter::Off);
        assert!(kernel_refused(&off), "w = {w}: b.ge with b.lt's arms, filter off: {off:?}");
    }
}

/// A Bool equality is in the walk, so `B` states it, but its proving view
/// exists only through the flag bridge: any other declines, with the Rust
/// checks on and off.
#[test]
fn a_bool_equality_outside_the_flag_bridge_declines() {
    let c = ult(x64(), lit(2, 64), 64);
    let side = ite(feq(c.clone(), Formula::Bool(true)), x64(), lit(0, 64));
    assert!(branch_fragment(&side));
    let items = vec![(side.clone(), side)];
    for filter in [BranchFilter::On, BranchFilter::Off] {
        assert_eq!(
            prove(&items, filter),
            Err(Decline::Filter("branch: a Bool equality outside the flag bridge".into())),
            "{filter:?}"
        );
    }
}

/// The shift-amount fold is a kernel-checked `Eq.refl`: on s10's closed amount
/// (`sext(2) & 63 & 63`) the step to `Const 2` type-checks and the step to
/// `Const 3` (a wrong value from Rust) does not. It skips (`None`) a literal
/// amount, a value too wide for the amount and an amount off the closed-data
/// whitelist (`BvF.Mul`).
#[test]
fn ashr_amount_fold_is_kernel_checked() {
    let mut ctx = ReflectCtx::branching();
    let amt = reflect_formula(&s10_amount(), &mut ctx).expect("amount").core;
    let x = kx::const_(kx::bits(-8, 64));
    let core = kx::ashr(x.clone(), amt);
    let fold = |v: u128| ashr_amount_fold(&core, v, 64).expect("folds");
    let (good, bad) = (fold(2), fold(3));
    assert_eq!(good.1, kx::ashr(x.clone(), kx::const_(kx::bits(2, 64))));
    assert!(ashr_amount_fold(&kx::ashr(x.clone(), kx::const_(kx::bits(2, 64))), 2, 64).is_none());
    assert!(ashr_amount_fold(&core, 1 << 64, 64).is_none());
    let mul = kx::mul(kx::const_(kx::bits(1, 64)), kx::const_(kx::bits(2, 64)));
    assert!(ashr_amount_fold(&kx::ashr(x.clone(), mul), 2, 64).is_none());
    // A negative sign extension whose sign bits survive the mask: the kernel
    // computes the goal arm's fill, so the fold to SMT-LIB's 62 type-checks and
    // the fold to 14 (the value with the sign bits filled with `false`) does not.
    let neg = reflect_formula(&neg_sext_amount(), &mut ctx).expect("amount").core;
    let neg_core = kx::ashr(x, neg);
    let (neg_good, neg_bad) = (
        ashr_amount_fold(&neg_core, 62, 64).expect("folds"),
        ashr_amount_fold(&neg_core, 14, 64).expect("folds"),
    );
    run_recheck_thread("branch-ashr-fold", move || {
        let env = branch_theory::branch_base().expect("base").clone();
        let tc = TypeChecker::with_mode(&env, env.mode());
        assert!(tc.infer_type_full(&good.0).is_ok(), "the fold to 2 was refused");
        assert!(tc.infer_type_full(&bad.0).is_err(), "the fold to 3 was accepted");
        assert!(tc.infer_type_full(&neg_good.0).is_ok(), "the fold to 62 was refused");
        assert!(tc.infer_type_full(&neg_bad.0).is_err(), "the fold to 14 was accepted");
    })
    .expect("kernel thread");
}

/// `sext(-2:4, 60) & 63`, 62 under SMT-LIB: bits 4 and 5 of the amount are
/// sign-extension bits, so a wrong fill changes the amount (to 14 with
/// `false`), unlike s10's `sext(2:32) & 63`, whose fill the mask discards.
fn neg_sext_amount() -> Formula {
    Formula::BvAnd(bx(Formula::BvSignExt(bx(lit(14, 4)), 60)), bx(lit(63, 64)), 64)
}

/// The s10 shape with the spec's amount `sext(-2:4, 60) & 63` against the
/// machine's `asr #62` (`62 & 63`): proved with the Rust checks on and off,
/// through the flag bridge and the fold, whose `Eq.refl` makes the kernel
/// compute the sign-extension goal arm's fill (`smt` agrees: 62). The machine's
/// `asr #63` is not proved, and with the Rust checks bypassed the kernel
/// refuses it (`x >> 62` and `x >> 63` differ for `x` in `[2^62, 2^63)`).
#[test]
fn negative_sign_extension_amount_is_proved_and_its_mutant_refused() {
    assert_eq!(smt(&neg_sext_amount()), Val::V(62, 64));
    let k100 = lit(100, 64);
    let sub200 = Formula::BvSub(bx(x64()), bx(lit(200, 64)), 64);
    let ashr = |amt: Formula| Formula::BvAShr(bx(x64()), bx(amt), 64);
    let machine_amt = |v: i128| Formula::BvAnd(bx(lit(v, 64)), bx(lit(63, 64)), 64);
    let spec = ite(
        Formula::BvSLt(bx(x64()), bx(k100.clone()), 64),
        sub200.clone(),
        ashr(neg_sext_amount()),
    );
    let item = |v: i128| {
        vec![(
            ite(flag_cond(x64(), k100.clone(), 64, true), sub200.clone(), ashr(machine_amt(v))),
            spec.clone(),
        )]
    };
    for filter in [BranchFilter::On, BranchFilter::Off] {
        let got = prove(&item(62), filter);
        assert!(matches!(&got, Ok(e) if is_s10_label(e)), "{filter:?}: {got:?}");
    }
    assert!(prove(&item(63), BranchFilter::On).is_err(), "asr #63 proved");
    let off = prove(&item(63), BranchFilter::Off);
    assert!(kernel_refused(&off), "asr #63 with the filter off: {off:?}");
}

/// The `slt_flags` instance against the goal-shaped flag condition (as
/// `high_extract` and `bool_goal` state it) at widths 8, 32 and 64: accepted
/// at `(x, k)`; refused with the operands swapped, with `N` compared with
/// `[false]`, and with `N` read one bit low (`btail^(w-2)`).
#[test]
fn slt_flags_instance_is_kernel_checked_at_each_width() {
    run_recheck_thread("branch-slt-flags", || {
        for w in [8u32, 32, 64] {
            let mut env = branch_theory::branch_base().expect("base").clone();
            super::super::add_comm::add_leaf_bits(&mut env, &[("X0".to_string(), w)]);
            let tc = TypeChecker::with_mode(&env, env.mode());
            let ex = kx::evalf(kx::leaf(super::super::add_comm::bit_leaf("X0", w)));
            let ek = kx::evalf(kx::const_(kx::bits(100, w)));
            let d = kx::evalf(kx::sub(
                kx::leaf(super::super::add_comm::bit_leaf("X0", w)),
                kx::const_(kx::bits(100, w)),
            ));
            let sign = |l: Expr, n: u32| {
                kx::evalf(kx::const_((0..n).fold(l, |acc, _| super::super::kterm::btail(acc))))
            };
            let one = |b: i128| kx::evalf(kx::const_(kx::bits(b, 1)));
            let flags = |n_lit: i128, n_drop: u32| {
                kx::bxor(
                    kx::bv_beq(sign(d.clone(), n_drop), one(n_lit)),
                    kx::band(
                        kx::bnot(kx::bv_beq(sign(ex.clone(), w - 1), sign(ek.clone(), w - 1))),
                        kx::bnot(kx::bv_beq(sign(d.clone(), w - 1), sign(ex.clone(), w - 1))),
                    ),
                )
            };
            let stmt = |g: Expr| eq(bool_ty(), g, kx::bv_slt_real(ex.clone(), ek.clone()));
            let inst = |a: &Expr, b: &Expr| {
                branch_theory::slt_flags_inst(
                    a.clone(),
                    b.clone(),
                    refl(bool_ty(), kx::btrue()),
                    refl(nat(), kx::nat_lit(w)),
                )
            };
            assert!(tc.check_type(&inst(&ex, &ek), &stmt(flags(1, w - 1))).is_ok(), "w = {w}");
            for (what, p, g) in [
                ("swapped operands", inst(&ek, &ex), flags(1, w - 1)),
                ("N == 0", inst(&ex, &ek), flags(0, w - 1)),
                ("N one bit low", inst(&ex, &ek), flags(1, w - 2)),
            ] {
                assert!(tc.check_type(&p, &stmt(g)).is_err(), "w = {w}: {what} was accepted");
            }
        }
    })
    .expect("kernel thread");
}

/// Every theorem the s10 discharges name is audited by the branch base
/// (`branch_theory::audited`), `Clean.BVC.slt_flag_bridge` among them; s10's
/// O2 label also names the shift-amount fold's `bvf_ashr_cong`.
#[test]
fn s10_label_theorems_are_audited() {
    let audited = branch_theory::audited();
    for (name, items) in s10() {
        let ob = obligation(&items, BranchFilter::On).unwrap_or_else(|d| panic!("{name}: {d:?}"));
        let label = run_recheck_thread("branch-s10-label", move || {
            let env = branch_theory::env(&ob.leaves).expect("env");
            branch_theory::label(&env, &ob.proof)
        })
        .expect("thread");
        let parts: Vec<&str> = label.split('+').collect();
        let (_, theorems) = parts.split_last().expect("label");
        for t in theorems {
            assert!(audited.contains(t), "{name}: {t} is in the label but not audited");
        }
        for want in [names::SLT_FLAGS, "Clean.BVC.bvf_ashr_cong"] {
            assert!(theorems.contains(&want), "{name}: {want} missing from {label}");
        }
    }
    assert!(audited.contains(&"Clean.BVC.slt_flag_bridge"));
}

/// The time s10's discharge takes, printed (`S10_MS`) for the record, not
/// asserted: the Rust build of the obligation, then the kernel's admission in
/// `branch_theory::env` (the base already built, so its one-time cost is
/// excluded).
#[test]
fn s10_kernel_time_is_reported() {
    for (name, items) in s10() {
        let t = std::time::Instant::now();
        let ob = obligation(&items, BranchFilter::On).unwrap_or_else(|d| panic!("{name}: {d:?}"));
        let build = t.elapsed();
        let admit = run_recheck_thread("branch-s10-time", move || {
            let mut env = branch_theory::env(&ob.leaves).expect("env");
            let t = std::time::Instant::now();
            super::super::strength::admit_obligation(&mut env, ob.goal, ob.proof)
                .expect("admitted");
            t.elapsed()
        })
        .expect("thread");
        println!(
            "S10_MS {name}: build {:.1} ms, kernel {:.1} ms",
            build.as_secs_f64() * 1e3,
            admit.as_secs_f64() * 1e3
        );
    }
}
