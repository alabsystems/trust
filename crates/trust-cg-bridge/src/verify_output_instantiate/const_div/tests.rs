// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::time::Instant;

use clean_kernel::name::Name;
use clean_kernel::{
    ConstantKind, Declaration, Expr, ExprKind, KernelEnvError, TypeChecker, TypeError,
};
use trust_types::{Formula, Sort};

use super::super::branch_split::{BranchFilter, Decline};
use super::super::const_div_theory::{self as theory, const_div_base, const_div_env, names};
use super::super::kterm::{bool_ty, eq, lb, nadd, nat, nble, nlit, nmul, refl, two_pow};
use super::super::{ReflectCtx, kx, on_route_stack, reflect_formula, run_recheck_thread, strength};
use super::{
    GoalEval, MUTANT, Mutant, children, collect_magic, const_div_rewrite, differential, eval_bv,
    goal_of, magic_formula, magic_params, nat_u128, obligation, points, prove, replace,
    rewrite_with, step4_rewrite, try_conjunction,
};
use crate::verify_output::{Discharge, ProvenEvidence, discharge_valid};

// ── the shapes ───────────────────────────────────────────────────────────────
//
// The machine sides are the AArch64 semantics (`trust-machine-sem`) of the
// trust-cg bytes for s20 (`x % 7`), `x / 3` and `x / 7`, after `abi_fold`:
// `compiled_bytes_are_the_hand_built_shapes` compiles each at O0 and O2 for
// both triples and compares (all twelve cells equal; s20 at O0 ends in an
// `orr x0, xzr, x2` move, the standalone divisions at O0 do not). The spec sides are hand-built from the
// call-event spec builder's reading (its items are private to the frozen
// `call_event.rs`, so they are not captured here): `x % d` as
// `x - (if d == 0 then 0 else x / d) * d`, and `x / d` as a bare `BvUDiv`
// (HYPOTHESISED for the standalone division; no gate capture exists).

const MK7: u64 = 0x2492_4924_9249_2493;
const MK3: u64 = 0xAAAA_AAAA_AAAA_AAAB;

type Items = Vec<(Formula, Formula)>;

fn bx(f: Formula) -> Box<Formula> {
    Box::new(f)
}
fn lit(value: i128, width: u32) -> Formula {
    Formula::BitVec { value, width }
}
fn x64() -> Formula {
    Formula::Var("X0".into(), Sort::BitVec(64))
}
fn add(a: Formula, b: Formula) -> Formula {
    Formula::BvAdd(bx(a), bx(b), 64)
}
fn sub(a: Formula, b: Formula) -> Formula {
    Formula::BvSub(bx(a), bx(b), 64)
}
fn shl(a: Formula, n: i128) -> Formula {
    Formula::BvShl(bx(a), bx(lit(n, 64)), 64)
}
fn lshr(a: Formula, n: i128) -> Formula {
    Formula::BvLShr(bx(a), bx(lit(n, 64)), 64)
}
fn udiv(a: Formula, d: i128) -> Formula {
    Formula::BvUDiv(bx(a), bx(lit(d, 64)), 64)
}
/// The MOVZ/MOVK chain of `v`, exactly as `sem_mov_imm` builds it: `MOVZ
/// lo16`, then per half-word `BvOr(BvAnd(prev, inv_mask), imm << sh)` with
/// `inv_mask = !(0xffff << sh) & -1` (a NEGATIVE `i128` at width 64).
fn movk(v: u64) -> Formula {
    let mut f = lit(i128::from(v & 0xffff), 64);
    for sh in [16u32, 32, 48] {
        let imm = i128::from((v >> sh) & 0xffff);
        let inv = !(0xffff_i128 << sh);
        f = Formula::BvOr(
            bx(Formula::BvAnd(bx(f), bx(lit(inv, 64)), 64)),
            bx(lit(imm << sh, 64)),
            64,
        );
    }
    f
}
/// AArch64 `umulh a, b`.
fn umulh(a: Formula, b: Formula) -> Formula {
    Formula::BvExtract {
        inner: bx(Formula::BvMul(
            bx(Formula::BvZeroExt(bx(a), 64)),
            bx(Formula::BvZeroExt(bx(b), 64)),
            128,
        )),
        high: 127,
        low: 64,
    }
}
/// AArch64 `ubfm v, #k, #63` (`lsr #k`).
fn ubfm(v: Formula, k: u32) -> Formula {
    Formula::BvZeroExt(bx(Formula::BvExtract { inner: bx(v), high: 63, low: k }), k)
}
/// The add-back quotient of magicu(7) at `x`: `t = mh + ((x - mh) >> 1)`,
/// then `t >> k`; the halving as `lsr #1` (O2, shifted register) or UBFM #1
/// (O0).
fn q7_at(x: Formula, mk: u64, ubfm_half: bool, k: u32) -> Formula {
    let mh = umulh(x.clone(), movk(mk));
    let d = sub(x, mh.clone());
    let h = if ubfm_half { ubfm(d, 1) } else { lshr(d, 1) };
    ubfm(add(mh, h), k)
}
fn q7(mk: u64, ubfm_half: bool, k: u32) -> Formula {
    q7_at(x64(), mk, ubfm_half, k)
}
fn q3_at(x: Formula) -> Formula {
    ubfm(umulh(x, movk(MK3)), 1)
}
/// `x + (q - (q << shift))`, the remainder tail of `x % 7`.
fn rem7_tail_at(x: Formula, q: Formula, shift: i128) -> Formula {
    add(x, sub(q.clone(), shl(q, shift)))
}
fn rem7_tail(q: Formula, shift: i128) -> Formula {
    rem7_tail_at(x64(), q, shift)
}
/// The spec of `x % d`: `x - (if d == 0 then 0 else x / d) * m`.
fn rem_spec(d: i128, m: i128) -> Formula {
    let guarded = Formula::Ite(
        bx(Formula::Eq(bx(lit(d, 64)), bx(lit(0, 64)))),
        bx(lit(0, 64)),
        bx(udiv(x64(), d)),
    );
    sub(x64(), Formula::BvMul(bx(guarded), bx(lit(m, 64)), 64))
}
fn mov_wrap(f: Formula) -> Formula {
    Formula::BvOr(bx(lit(0, 64)), bx(f), 64)
}

/// s20 (`x % 7`) at O2: `add x3, x2, x1, lsr #1`.
fn s20_o2() -> Items {
    vec![(rem7_tail(q7(MK7, false, 2), 3), rem_spec(7, 7))]
}
/// s20 at O0: UBFM #1 for the halving and the `orr x0, xzr, x2` move.
fn s20_o0() -> Items {
    vec![(mov_wrap(rem7_tail(q7(MK7, true, 2), 3)), rem_spec(7, 7))]
}
/// `x / 3` at O2: `ubfm x1, x2, #1, #63` over `umulh x2, x0, x1`.
fn div3_o2() -> Items {
    vec![(q3_at(x64()), udiv(x64(), 3))]
}
/// `x / 3` at O0: the O2 shape (measured: trust-cg emits no `orr` move for
/// the standalone division at O0, unlike s20).
fn div3_o0() -> Items {
    div3_o2()
}
/// `x / 3` under an `orr x0, xzr, ·` move (the s20 O0 form of the move).
fn div3_orr() -> Items {
    vec![(mov_wrap(q3_at(x64())), udiv(x64(), 3))]
}
/// The standalone add-back quotient against `x / 7`.
fn div7(ubfm_half: bool) -> Items {
    vec![(q7(MK7, ubfm_half, 2), udiv(x64(), 7))]
}

fn label(e: &ProvenEvidence) -> &str {
    match e {
        ProvenEvidence::KernelInstantiated { theorem, original: None } => theorem,
        other => panic!("not a kernel instantiation: {other:?}"),
    }
}

fn kernel_refused(r: &Result<ProvenEvidence, Decline>) -> bool {
    matches!(r, Err(Decline::Kernel(m)) if m.starts_with("kernel: TypeCheckFailed"))
}

fn with_mutant<T>(m: Mutant, f: impl FnOnce() -> T) -> T {
    MUTANT.with(|c| c.set(m));
    let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    MUTANT.with(|c| c.set(Mutant::None));
    out.unwrap_or_else(|p| std::panic::resume_unwind(p))
}

fn head_is(e: &Expr, name: &str) -> bool {
    matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

/// Every value of the shapes agrees with Rust arithmetic (the shapes are the
/// compiled algorithms, not a test artefact).
#[test]
fn captured_shapes_compute_the_division() {
    on_route_stack(|| {
        let xs = [
            0u128,
            1,
            2,
            3,
            6,
            7,
            8,
            99,
            1 << 63,
            (1 << 63) - 1,
            u128::from(u64::MAX) - 1,
            u128::from(u64::MAX),
        ];
        for items in [s20_o2(), s20_o0(), div3_o2(), div3_orr(), div7(false), div7_orr()] {
            for (m, s) in &items {
                for x in xs {
                    let env = |n: &str| (n == "X0").then_some(x);
                    assert_eq!(eval_bv(m, &env), eval_bv(s, &env), "at {x:#x}");
                }
            }
        }
        assert_eq!(magic_params(u128::from(MK7), 2, true), Some((7, 5)));
        assert_eq!(magic_params(u128::from(MK3), 1, false), Some((3, 1)));
        assert_eq!(magic_params(u128::from(MK7) + 2, 2, true), None, "the band filter");
    })
}

// ── the bytes the shapes stand for ───────────────────────────────────────────

/// The producer's `-Ztrust-dump=ir:` text of ladder rung s20 (`x % 7`); `d3`
/// and `d7` are the same function with `udiv` by 3 and 7.
const S20_IR: &str = r#"; TrustIr text format v1
module "rung"
file 0 "tests/trust-f1-ladder/micro/s20_rem_const.rs"

functy.0 = (u64) -> (u64)

fn @rung(functy.0) {
    ; #producer: trust
    ; #body-gate: gated "trust-direct-lane-structural"
    ; #display-path: "rung"
    ; #names: %0="x"
bb0(%0: u64):
    %1 = const u64 7
    %2 = const u64 0
    %3 = icmp ne u64 %1, %2
    assert %3, rem_by_zero  ; #proof: div_nonzero
    %4 = urem u64 %0, %1
    ret %4
}

obligation 0 arithmetic_safety pending "direct THIR Assert (rem_by_zero) at L1C53 of `rung::rung`: remainder divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED." function 0 source "trust-thir-lower/direct-assert@1" assertion "rung::rung#L1C53#rem_by_zero#o0" range 0 1 53 1 58 site f0/bb0#3
"#;

const DARWIN: &str = "aarch64-apple-darwin";
const LINUX: &str = "aarch64-unknown-linux-gnu";

/// `x0` after the compiled bytes of `ir` run from a symbolic state, through
/// `abi_fold` (the call-event gate's item before step (4)).
fn machine_x0(ir: &str, triple: &str, opt: trust_cg_codegen::pipeline::OptLevel) -> Formula {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{CodegenLicensePolicy, Compiler, CompilerConfig, UnlicensedBodyPolicy};
    use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};
    let folded: String = ir
        .lines()
        .filter(|l| !l.trim_start().starts_with("assert "))
        .collect::<Vec<_>>()
        .join("\n");
    let module = trust_ir::parser::parse_module(&folded).expect("the IR parses");
    let license = CodegenLicensePolicy::default()
        .with_unlicensed(UnlicensedBodyPolicy::Permit)
        .with_recognized_authority("trust-direct-lane-structural");
    let object = Compiler::new_for_target_spec(
        CompilerConfig { opt_level: opt, parallel: false, ..CompilerConfig::default() },
        TargetSpec::parse(triple).expect("triple"),
    )
    .with_codegen_license(license)
    .compile(&module)
    .expect("trust-cg compiles the rung")
    .object_code;
    let obj = crate::compiled_object::CompiledObject::parse(&object).expect("object");
    let sec = obj
        .sections
        .iter()
        .find(|s| s.class == crate::compiled_object::SectionClass::Code)
        .expect("a code section");
    let mut state = MachineState::symbolic();
    for (i, w) in sec.bytes.chunks(4).enumerate() {
        let insn = trust_disasm::decode_aarch64(w, (i * 4) as u64).expect("decodes");
        if insn.opcode == trust_disasm::Opcode::Ret {
            return crate::verify_output::abi_fold(&state.gpr[0]);
        }
        let effects = Aarch64Semantics.effects(&state, &insn).expect("semantics");
        state.apply_effects(&effects).expect("effects apply");
    }
    panic!("{triple} {opt:?}: no ret");
}

/// The hand-built machine sides are exactly the trust-cg bytes' semantics
/// (O0 and O2, both triples), so what the positives prove is what the gate's
/// machine side states; any cell that differs must still be proved.
#[test]
fn compiled_bytes_are_the_hand_built_shapes() {
    use trust_cg_codegen::pipeline::OptLevel;
    on_route_stack(|| {
        let d3 = S20_IR
            .replace("urem u64 %0, %1", "udiv u64 %0, %1")
            .replace("const u64 7", "const u64 3");
        let d7 = S20_IR.replace("urem u64 %0, %1", "udiv u64 %0, %1");
        let cells: [(&str, String, Items, Items); 3] = [
            ("s20", S20_IR.to_string(), s20_o0(), s20_o2()),
            ("d3", d3, div3_o0(), div3_o2()),
            ("d7", d7, div7_o0(), div7(false)),
        ];
        let mut differ = Vec::new();
        for (name, ir, o0, o2) in &cells {
            for triple in [DARWIN, LINUX] {
                for (opt, hand) in [(OptLevel::O0, o0), (OptLevel::O2, o2)] {
                    let m = machine_x0(ir, triple, opt);
                    if m != hand[0].0 {
                        differ.push(format!(
                            "{name} {triple} {opt:?}:\n  bytes {m:?}\n  hand  {:?}",
                            hand[0].0
                        ));
                    }
                }
            }
        }
        assert!(differ.is_empty(), "{} cells differ:\n{}", differ.len(), differ.join("\n"));
    })
}

/// `x / 7` at O0: the UBFM halving (measured: no `orr` move).
fn div7_o0() -> Items {
    div7(true)
}
/// `x / 7` with the UBFM halving under an `orr` move.
fn div7_orr() -> Items {
    vec![(mov_wrap(q7(MK7, true, 2)), udiv(x64(), 7))]
}

// ── the theory ───────────────────────────────────────────────────────────────

#[test]
fn const_div_theorems_are_kernel_checked() {
    on_route_stack(|| {
        let t = Instant::now();
        let kinds = run_recheck_thread("constdiv-base", || {
            let env = const_div_base().expect("const_div_base").clone();
            names::ALL
                .iter()
                .map(|n| {
                    (
                        *n,
                        env.get_const(&Name::from_string(n))
                            .map(|i| i.kind == ConstantKind::Theorem),
                    )
                })
                .collect::<Vec<_>>()
        })
        .expect("thread");
        for (n, k) in &kinds {
            assert_eq!(*k, Some(true), "{n} is not a kernel-checked theorem");
        }
        assert_eq!(kinds.len(), 24);
        println!(
            "const_div_base: {} theorems built and audited in {} ms",
            kinds.len(),
            t.elapsed().as_millis()
        );
    })
}

/// The magic premises are decided by the kernel's literal arithmetic on
/// values above 2^64 (`Nat.ble`, `Nat.mul`, `Nat.add`, `bvTwoPow` on Big
/// naturals): at the band's boundary the largest admissible `e` is accepted
/// and `e + 1` refused, at `p = 67` and `p = 126`; and `d * M = 2^p + e` is
/// refused when only its high limb is wrong, both with `e` built from
/// literals below 2^64 (as the route builds it) and as one Big literal.
#[test]
fn big_literal_premises_are_decided_by_the_kernel() {
    on_route_stack(|| {
        let bad = run_recheck_thread("constdiv-big", || {
            let env = const_div_base().expect("base").clone();
            let tc = || TypeChecker::with_mode(&env, env.mode());
            let w64 = kx::nat_lit(64);
            let band = |e: u128, p: u32| {
                let en = nat_u128(e);
                let lo = nadd(nmul(en.clone(), two_pow(w64.clone())), nlit(1));
                let hi = nadd(two_pow(nlit(u64::from(p))), en);
                kx::eq_bool(nble(lo, hi), kx::btrue())
            };
            let holds = |ty: &Expr, proof: &Expr| tc().check_type(proof, ty).is_ok();
            let rt = kx::eq_refl_bool(kx::btrue());
            let mut bad = Vec::new();
            for p in [67u32, 126] {
                let e_max = ((1u128 << p) - 1) / u128::from(u64::MAX);
                if !holds(&band(e_max, p), &rt) {
                    bad.push(format!("p={p}: the band at e={e_max:#x} was refused"));
                }
                if holds(&band(e_max + 1, p), &rt) {
                    bad.push(format!("p={p}: the band at e={:#x} was ACCEPTED", e_max + 1));
                }
            }
            // magicu(7) with the add-back: 7 * (2^64 + MK7) = 2^67 + 5.
            let m = nadd(two_pow(w64.clone()), nlit(MK7));
            let lhs = nmul(nlit(7), m);
            let rhs = |e: Expr| nadd(two_pow(nlit(67)), e);
            let pr = refl(nat(), lhs.clone());
            let cases = [
                (nat_u128(5), true),
                (nat_u128(5 + (1u128 << 64)), false),
                (Expr::nat_lit_u128(5 + (1u128 << 64)), false),
            ];
            for (e, want) in cases {
                if holds(&eq(nat(), lhs.clone(), rhs(e.clone())), &pr) != want {
                    bad.push(format!("d*M = 2^67 + {e:?}: expected {want}"));
                }
            }
            let big = Expr::nat_lit_u128((1u128 << 67) + 5);
            if !holds(&eq(nat(), lhs.clone(), big), &pr) {
                bad.push("d*M = Big(2^67 + 5) was refused".into());
            }
            let big_off = Expr::nat_lit_u128((1u128 << 67) + 5 + (1u128 << 64));
            if holds(&eq(nat(), lhs, big_off), &pr) {
                bad.push("d*M = Big(2^67 + 2^64 + 5) was ACCEPTED".into());
            }
            bad
        })
        .expect("thread");
        assert!(bad.is_empty(), "{}", bad.join("\n"));
    })
}

/// The route's closed-data list is the branch split's, every entry kept and
/// in order, followed by exactly `Nat.ble` and `bvTwoPow`. A fixed-length
/// copy once overwrote the branch list's last two entries (`Nat.add`,
/// `Nat.mul`) when that list grew, so `note_closed` refused every magic
/// premise and no quotient step fired.
#[test]
fn constdiv_whitelist_extends_the_branch_list() {
    use super::super::branch_reflect::CLOSED_WHITELIST;
    use super::{CONSTDIV_WHITELIST, note_closed};
    let n = CLOSED_WHITELIST.len();
    assert_eq!(CONSTDIV_WHITELIST.len(), n + 2);
    assert_eq!(&CONSTDIV_WHITELIST[..n], &CLOSED_WHITELIST[..]);
    assert_eq!(&CONSTDIV_WHITELIST[n..], &["Nat.ble", "Clean.BVC.bvTwoPow"]);
    assert!(CONSTDIV_WHITELIST.iter().all(|s| !s.is_empty()));
    // The magic premises' arithmetic is admitted (`j + k`, `d * M`).
    assert!(note_closed(&nadd(nlit(2), nmul(nlit(3), nlit(4)))));
    assert!(note_closed(&nble(nlit(1), nlit(7))));
    // What the branch list must not gain without a review of this route
    // too: an entry there reaches this filter (and the kernel evaluates
    // 128-bit products, quotients and shifts on closed data here).
    for never in [
        "Clean.BVC.bvMul",
        "Clean.BVC.bvDiv",
        "Clean.BVC.bvShl",
        "Clean.BVC.bvLShr",
        "Clean.BVC.bvAShr",
        "Clean.BVC.natToBvAux",
        "Nat.div",
        "Nat.mod",
        "Nat.rec",
        "Clean.BVC.BvF.Mul",
        "Clean.BVC.BvF.Div",
        "Clean.BVC.BvF.Shl",
        "Clean.BVC.BvF.LShr",
        "Clean.BVC.BvF.AShr",
        "Clean.BVC.BvF.Or",
    ] {
        assert!(!CONSTDIV_WHITELIST.contains(&never), "{never} is on the closed-data list");
    }
}

/// Every closed term the positives offer the kernel passes its own filter
/// (the MOVZ/MOVK fold leaf-free), every filter site is reached, and none
/// multiplies, divides or shifts closed data.
#[test]
fn constdiv_closed_data_is_whitelisted() {
    use std::collections::HashSet;

    use clean_kernel::expr::UsedConstants;

    use super::{CONSTDIV_SEEN, MOVK_EXTRA, closed_ok_with, has_leaf_bit};
    on_route_stack(|| {
        CONSTDIV_SEEN.with(|s| s.borrow_mut().clear());
        for (name, items) in [
            ("s20 O2", s20_o2()),
            ("s20 O0", s20_o0()),
            ("x/3 O2", div3_o2()),
            ("x/3 under orr", div3_orr()),
            ("x/7 lsr", div7(false)),
            ("x/7 ubfm O0", div7_o0()),
            ("x/7 ubfm under orr", div7_orr()),
        ] {
            obligation(&items, BranchFilter::On).unwrap_or_else(|d| panic!("{name}: {d:?}"));
        }
        let seen = CONSTDIV_SEEN.with(|s| std::mem::take(&mut *s.borrow_mut()));
        let mut heads = HashSet::new();
        let mut folds = 0;
        for (e, movk) in &seen {
            if *movk {
                folds += 1;
                assert!(!has_leaf_bit(e), "a MOVZ/MOVK fold mentions a leaf bit: {e:?}");
                assert!(closed_ok_with(e, &MOVK_EXTRA), "an off-list MOVZ/MOVK fold: {e:?}");
            } else {
                assert!(closed_ok_with(e, &[]), "an off-whitelist closed premise: {e:?}");
            }
            e.used_constants_dag(UsedConstants::ConstantsOnly, &mut heads);
        }
        assert!(folds > 0, "no MOVZ/MOVK multiplier was folded");
        let heads: HashSet<String> = heads.into_iter().map(|n| n.to_string()).collect();
        // The fold (`Or`, `And`), the magic premises (`bvLen`, `j + k`,
        // `d * M`, `2^p + e`, the band), the halving `lsr #1` and the
        // remainder tail (`succ c`, `2^n`).
        for want in [
            "Clean.BVC.BvF.Or",
            "Clean.BVC.BvF.And",
            "Clean.BVC.bvLen",
            "Clean.BVC.bvToNat",
            "Clean.BVC.bvTwoPow",
            "Nat.add",
            "Nat.mul",
            "Nat.ble",
            "Nat.succ",
        ] {
            assert!(heads.contains(want), "no closed term used {want}");
        }
        for never in [
            "Clean.BVC.bvMul",
            "Clean.BVC.bvDiv",
            "Clean.BVC.bvShl",
            "Clean.BVC.bvLShr",
            "Clean.BVC.bvAShr",
            "Clean.BVC.natToBvAux",
            "Nat.div",
            "Nat.mod",
            "Clean.BVC.BvF.Mul",
            "Clean.BVC.BvF.Div",
            "Clean.BVC.BvF.Shl",
            "Clean.BVC.BvF.LShr",
            "Clean.BVC.BvF.AShr",
        ] {
            assert!(!heads.contains(never), "{never} was evaluated on closed data");
        }
    })
}

// ── the positives ────────────────────────────────────────────────────────────

fn proves(name: &str, items: &Items, want: &[&str]) {
    let t = Instant::now();
    let r = prove(items, BranchFilter::On);
    let ms = t.elapsed().as_millis();
    let ev = r.unwrap_or_else(|d| panic!("{name}: declined: {d:?}"));
    let l = label(&ev);
    for w in want {
        assert!(l.contains(w), "{name}: label {l} lacks {w}");
    }
    println!("const-div {name}: proved in {ms} ms (with the differential): {l}");
    assert!(try_conjunction(items).is_some(), "{name}: try_conjunction");
}

#[test]
fn s20_rem7_is_proved_at_o0_and_o2() {
    on_route_stack(|| {
        proves("s20 O2", &s20_o2(), &[names::MAGIC_ADDBACK, names::REM_TAIL, names::LSHR_K]);
        proves("s20 O0", &s20_o0(), &[names::MAGIC_ADDBACK, names::REM_TAIL, names::UBFM_K]);
    })
}

/// The spec side here (a bare `BvUDiv`) is hypothesised: no gate capture of
/// a standalone division exists. The machine side is the compiled bytes'.
#[test]
fn div3_is_proved_at_o0_and_o2() {
    on_route_stack(|| {
        proves("x/3 O2", &div3_o2(), &[names::MAGIC_NOADD]);
        assert_eq!(div3_o0(), div3_o2(), "the O0 bytes are the O2 shape");
        proves("x/3 under orr", &div3_orr(), &[names::MAGIC_NOADD]);
    })
}

#[test]
fn addback_div7_is_proved() {
    on_route_stack(|| {
        proves("x/7 lsr", &div7(false), &[names::MAGIC_ADDBACK, names::LSHR_K]);
        proves("x/7 ubfm O0", &div7_o0(), &[names::MAGIC_ADDBACK, names::UBFM_K]);
        proves("x/7 ubfm under orr", &div7_orr(), &[names::MAGIC_ADDBACK, names::UBFM_K]);
    })
}

/// Per obligation, measured apart: building the obligation (reflection and
/// step builders), building the environment, kernel admission, and the
/// differential with its check count. Debug build. Run it alone
/// (`--ignored --test-threads=1`): run in parallel it measures contention.
#[test]
#[ignore = "timing: run alone with --test-threads=1"]
fn timing_per_component() {
    on_route_stack(|| {
        let _ = prove(&div3_o2(), BranchFilter::Off); // the base, once per process
        for (name, items) in [
            ("s20 O2", s20_o2()),
            ("s20 O0", s20_o0()),
            ("x/3 O2", div3_o2()),
            ("x/7 O0", div7_o0()),
        ] {
            let t = Instant::now();
            let ob = obligation(&items, BranchFilter::On).expect("obligation");
            let build_ms = t.elapsed().as_millis();
            let t = Instant::now();
            let checks = differential(&items, &ob.sides, &ob.leaves).expect("differential");
            let diff_us = t.elapsed().as_micros();
            let line = run_recheck_thread("constdiv-ms", move || {
                let t = Instant::now();
                let mut env = const_div_env(&ob.leaves).expect("env");
                let env_ms = t.elapsed().as_millis();
                let t = Instant::now();
                strength::admit_obligation(&mut env, ob.goal, ob.proof).expect("admitted");
                let kernel_ms = t.elapsed().as_millis();
                format!(
                    "build {build_ms} ms, env {env_ms} ms, kernel {kernel_ms} ms, differential \
                     {diff_us} us for {checks} checks"
                )
            })
            .expect("thread");
            println!("const-div timing (debug) {name}: {line}");
        }
    })
}

/// The axiom closure of an admitted discharge is only `BVC_LEAFBIT_*`.
#[test]
fn closure_is_only_leaf_bits() {
    on_route_stack(|| {
        let ob = obligation(&s20_o2(), BranchFilter::On).expect("obligation");
        let deps = run_recheck_thread("constdiv-closure", move || {
            let mut env = const_div_env(&ob.leaves).expect("env");
            strength::admit_obligation(&mut env, ob.goal, ob.proof).expect("admitted");
            let mut deps: Vec<String> = env
                .axiom_deps(&Name::from_string(strength::OBLIGATION))
                .expect("closure")
                .iter()
                .map(|n| n.to_string())
                .collect();
            deps.sort();
            deps
        })
        .expect("thread");
        assert!(!deps.is_empty());
        assert!(deps.iter().all(|d| d.starts_with("BVC_LEAFBIT_")), "closure: {deps:?}");
    })
}

// ── the declared goal ────────────────────────────────────────────────────────

/// The declared type is the goal of the items alone: built with every step
/// builder fault active it is the same `Expr`, it mentions no `Trust.BVD`
/// constant (the theory only proves it), and its spec side keeps the
/// faithful all-ones-at-/0 division (`spec_division_is_faithful_at_zero`).
#[test]
fn declared_goal_is_independent_of_the_steps() {
    on_route_stack(|| {
        for items in [s20_o2(), div3_o2()] {
            let (goal, _, _) = goal_of(&items).expect("goal");
            for m in [
                Mutant::ForceDivisor(4),
                Mutant::ForceDivisor(8),
                Mutant::RemMulPow,
                Mutant::NoBandFilter,
                Mutant::AxiomBand,
            ] {
                let ob = with_mutant(m, || obligation(&items, BranchFilter::Off)).expect("built");
                assert!(ob.goal == goal, "{m:?} changed the declared goal");
            }
            let mut used = std::collections::HashSet::new();
            goal.used_constants_dag(clean_kernel::expr::UsedConstants::ConstantsOnly, &mut used);
            let bvd: Vec<String> = used
                .iter()
                .map(ToString::to_string)
                .filter(|n| n.starts_with("Trust.BVD."))
                .collect();
            assert!(bvd.is_empty(), "the goal mentions {bvd:?}");
        }
    })
}

/// The goal reflection of a division by zero is SMT's all-ones (the
/// faithful `branch_reflect::udiv`), in the kernel; the legacy reflection
/// (`BvF.Div`, not faithful at /0) computes another value, so forcing it at
/// the spec would change the goal; and a machine side that computes the
/// legacy value against `x / 0` is never admitted.
#[test]
fn spec_division_is_faithful_at_zero() {
    on_route_stack(|| {
        let f = udiv(lit(5, 64), 0);
        let mut goal_ctx = ReflectCtx::const_div_goal();
        let faithful = kx::evalf(reflect_formula(&f, &mut goal_ctx).expect("goal").bvf);
        let mut legacy_ctx = ReflectCtx::closed();
        let legacy = kx::evalf(reflect_formula(&f, &mut legacy_ctx).expect("legacy").bvf);
        assert!(faithful != legacy, "the goal reflection is the legacy one");
        let bad = run_recheck_thread("constdiv-div0", move || {
            let env = const_div_base().expect("base").clone();
            let ones = kx::bits(-1, 64);
            let is = |side: &Expr, v: &Expr| {
                TypeChecker::with_mode(&env, env.mode())
                    .check_type(&refl(lb(), v.clone()), &eq(lb(), side.clone(), v.clone()))
                    .is_ok()
            };
            let mut bad = Vec::new();
            if !is(&faithful, &ones) {
                bad.push("the goal side of 5 / 0 is not all-ones");
            }
            if is(&legacy, &ones) {
                bad.push("the legacy side of 5 / 0 is all-ones (the test shows nothing)");
            }
            bad
        })
        .expect("thread");
        assert!(bad.is_empty(), "{bad:?}");
        never_admitted("machine 0 vs x / 0", vec![(lit(0, 64), udiv(x64(), 0))], Some(At::Goal));
    })
}

fn fnv1a(s: &str) -> u64 {
    s.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
}

/// The goal reflection of the route (the trusted residual's `umulh` arm and
/// the reflections it reuses) is byte-pinned over the positive corpus: any
/// change to what a goal states fails here and needs review.
#[test]
fn const_div_goal_reflection_is_byte_pinned() {
    use std::fmt::Write as _;
    on_route_stack(|| {
        let mut s = String::new();
        let corpus: Vec<Formula> =
            [s20_o2(), s20_o0(), div3_o2(), div3_orr(), div7(false), div7_orr()]
                .into_iter()
                .flat_map(|items| items.into_iter().flat_map(|(m, sp)| [m, sp]))
                .chain([umulh(x64(), lit(i128::from(MK3), 64)), udiv(x64(), 0)])
                .collect();
        for f in &corpus {
            let mut ctx = ReflectCtx::const_div_goal();
            match reflect_formula(f, &mut ctx) {
                Ok(r) => writeln!(s, "{:?}\n{:?}\n{:?}\n{:?}", r.bvf, r.core, r.proof, ctx.leaves)
                    .unwrap(),
                Err(e) => writeln!(s, "Err {e}").unwrap(),
            }
        }
        println!("CONSTDIV_GOAL_PIN ({}, {})", s.len(), fnv1a(&s));
        assert_eq!((s.len(), fnv1a(&s)), (45894241, 14936031398188556064), "CONSTDIV_GOAL_PIN");
    })
}

// ── the mutants ──────────────────────────────────────────────────────────────

/// Where the kernel refused a term: the premise whose expected type did not
/// match, read from the kernel's own `TypeMismatch`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum At {
    /// `Nat.ble (e * 2^64 + 1) (2^p + e) = true`.
    Band,
    /// `V c * M = 2^p + e`.
    Hdm,
    /// `succ (V c) = 2^(V n)` (the remainder tail).
    Hv,
    /// An equation over `List Bool`: the step chain does not reach the
    /// declared goal (the conclusion is bound to the goal).
    Goal,
    Other,
}

fn classify(e: &KernelEnvError) -> At {
    let KernelEnvError::TypeCheckFailed {
        source: TypeError::TypeMismatch { expected, .. }, ..
    } = e
    else {
        return At::Other;
    };
    let args = expected.get_app_args();
    if !head_is(expected, "Eq") || args.len() != 3 {
        return At::Other;
    }
    let (ty, lhs) = (args[0], args[1]);
    if *ty == bool_ty() && head_is(lhs, "Nat.ble") {
        At::Band
    } else if *ty == nat() && head_is(lhs, "Nat.mul") {
        At::Hdm
    } else if *ty == nat() && head_is(lhs, "Nat.succ") {
        At::Hv
    } else if *ty == lb() {
        At::Goal
    } else {
        At::Other
    }
}

/// Build `items`' obligation under `m` with the Rust filters off, declare it
/// as `admit_obligation` does, and say where the kernel refused it (`Err`
/// when it was ACCEPTED, or the walk refused it).
fn refusal_point(items: &Items, m: Mutant) -> Result<(At, String), String> {
    let ob = with_mutant(m, || obligation(items, BranchFilter::Off))
        .map_err(|d| format!("not built: {d:?}"))?;
    run_recheck_thread("constdiv-at", move || {
        let mut env = const_div_env(&ob.leaves).expect("env");
        for (name, ty) in ob.axioms {
            env.add_decl(Declaration::Axiom { name, level_params: vec![], type_: ty })
                .expect("axiom");
        }
        match env.add_decl(Declaration::Theorem {
            name: Name::from_string(strength::OBLIGATION),
            level_params: vec![],
            type_: ob.goal,
            value: ob.proof,
        }) {
            Ok(()) => Err("ACCEPTED by the kernel".to_string()),
            Err(e) => {
                let s = format!("{e}");
                Ok((classify(&e), s.chars().take(600).collect()))
            }
        }
    })
    .expect("thread")
}

/// A hook mutant: the production path refuses it in the kernel, and the
/// kernel's mismatch is at `want`.
fn refused_at(name: &str, m: Mutant, items: Items, want: At) {
    let r = with_mutant(m, || prove(&items, BranchFilter::Off));
    assert!(kernel_refused(&r), "{name}: not refused by the kernel: {r:?}");
    let (at, why) = refusal_point(&items, m).unwrap_or_else(|e| panic!("{name}: {e}"));
    assert_eq!(at, want, "{name}: refused elsewhere: {why}");
}

#[test]
fn wrong_magic_constant_is_refused_at_the_band() {
    on_route_stack(|| {
        let items = vec![(rem7_tail(q7(MK7 + 2, false, 2), 3), rem_spec(7, 7))];
        // With the filter on, the band filter declines first: `magic_params`
        // offers no divisor, so no quotient step fires and the cores do not
        // meet (the honest multiplier is offered one).
        assert_eq!(magic_params(u128::from(MK7), 2, true), Some((7, 5)));
        assert_eq!(magic_params(u128::from(MK7 + 2), 2, true), None);
        let r = prove(&items, BranchFilter::On);
        assert!(
            matches!(&r, Err(Decline::Filter(m)) if m.contains("the cores do not meet")),
            "{r:?}"
        );
        assert!(try_conjunction(&items).is_none());
        refused_at("MK+2", Mutant::NoBandFilter, items, At::Band);
    })
}

#[test]
fn wrong_shift_is_refused() {
    on_route_stack(|| {
        // `t >> 1` after the add-back claimed as x / 7: 7 * M = 2^66 + (2^66 + 5),
        // an error term the band refuses. `t >> 3`: 7 * M < 2^68, no error term.
        let s1 = vec![(q7(MK7, false, 1), udiv(x64(), 7))];
        let s3 = vec![(q7(MK7, false, 3), udiv(x64(), 7))];
        refused_at("shift 1", Mutant::ForceDivisor(7), s1, At::Band);
        refused_at("shift 3", Mutant::ForceDivisor(7), s3, At::Hdm);
    })
}

#[test]
fn off_by_one_divisor_is_refused() {
    on_route_stack(|| {
        let d8 = vec![(q7(MK7, false, 2), udiv(x64(), 8))];
        let d6 = vec![(q7(MK7, false, 2), udiv(x64(), 6))];
        let d4 = vec![(q3_at(x64()), udiv(x64(), 4))];
        refused_at("d=8", Mutant::ForceDivisor(8), d8, At::Band);
        refused_at("d=6", Mutant::ForceDivisor(6), d6, At::Hdm);
        refused_at("d=4", Mutant::ForceDivisor(4), d4, At::Band);
    })
}

#[test]
fn missing_addback_is_refused() {
    on_route_stack(|| {
        // magicu(7)'s multiplier without the add-back: 7 * MK7 < 2^66.
        let k2 = vec![(ubfm(umulh(x64(), movk(MK7)), 2), udiv(x64(), 7))];
        let k3 = vec![(ubfm(umulh(x64(), movk(MK7)), 3), udiv(x64(), 7))];
        refused_at("no add k=2", Mutant::ForceDivisor(7), k2, At::Hdm);
        refused_at("no add k=3", Mutant::ForceDivisor(7), k3, At::Hdm);
    })
}

#[test]
fn wrong_remainder_multiplier_is_refused() {
    on_route_stack(|| {
        // `q - (q << 3)` claimed as `q * 8`, against a spec that multiplies by 8.
        let items = vec![(rem7_tail(q7(MK7, false, 2), 3), rem_spec(7, 8))];
        refused_at("rem *8", Mutant::RemMulPow, items, At::Hv);
    })
}

#[test]
fn a_premise_faked_by_an_axiom_is_refused() {
    on_route_stack(|| {
        let r = with_mutant(Mutant::AxiomBand, || prove(&div3_o2(), BranchFilter::Off));
        assert!(
            matches!(&r, Err(Decline::Kernel(m)) if m.starts_with("obligation reaches axioms")),
            "an axiom premise was admitted, or refused for another reason: {r:?}"
        );
        // A false band faked by an axiom: the kernel accepts the term, admission does not.
        let wrong = vec![(ubfm(umulh(x64(), movk(MK3 + 4)), 1), udiv(x64(), 3))];
        let r = with_mutant(Mutant::AxiomBand, || prove(&wrong, BranchFilter::Off));
        assert!(
            matches!(&r, Err(Decline::Kernel(m)) if m.starts_with("obligation reaches axioms")),
            "{r:?}"
        );
    })
}

/// No hook: the builders are honest and the spec is wrong. The kernel ties
/// the conclusion to the declared goal and refuses at the goal binding.
/// The quotient step fires on both machine sides (the rewrite reaches
/// `x / 7`), so the refusal is the spec's, not a missing step's.
#[test]
fn an_honest_term_against_a_wrong_spec_is_refused_at_the_goal() {
    on_route_stack(|| {
        let q = udiv(x64(), 7);
        let (r, _) = const_div_rewrite(&q7(MK7, false, 2)).expect("the quotient step fired");
        assert_eq!(r, q);
        let (r, _) = const_div_rewrite(&rem7_tail(q7(MK7, false, 2), 3))
            .expect("the quotient step fired under the tail");
        assert_eq!(r, rem7_tail(q, 3));
        never_admitted("x/7 vs udiv 8", vec![(q7(MK7, false, 2), udiv(x64(), 8))], Some(At::Goal));
        never_admitted(
            "x%7 vs rem_spec(6,6)",
            vec![(rem7_tail(q7(MK7, false, 2), 3), rem_spec(6, 6))],
            Some(At::Goal),
        );
    })
}

/// Never admitted: `try_conjunction` declines, and with the Rust filters
/// off the kernel refuses at `at` (or, for `None`, the walk refuses the
/// goal, so no term is ever built).
fn never_admitted(name: &str, items: Items, at: Option<At>) {
    assert!(try_conjunction(&items).is_none(), "{name}: try_conjunction ADMITTED it");
    let r = prove(&items, BranchFilter::Off);
    match at {
        None => {
            assert!(goal_of(&items).is_err(), "{name}: the walk admitted the goal");
            assert!(matches!(r, Err(Decline::Filter(_))), "{name}: {r:?}");
        }
        Some(want) => {
            assert!(matches!(&r, Err(Decline::Kernel(_))), "{name}: not a kernel refusal: {r:?}");
            let (got, why) =
                refusal_point(&items, Mutant::None).unwrap_or_else(|e| panic!("{name}: {e}"));
            assert_eq!(got, want, "{name}: refused elsewhere: {why}");
        }
    }
}

/// The design's mutant list, each a wrong machine or IR Formula through the
/// honest builders (no hook).
#[test]
fn design_mutants_are_never_admitted() {
    on_route_stack(|| {
        let x = x64;
        let mh7 = || umulh(x(), movk(MK7));
        // t = mh + h, then t >> 2, then the remainder tail, from parts.
        let s20_from = |mh: Formula, h: Formula, tail: &dyn Fn(Formula) -> Formula| {
            vec![(tail(ubfm(add(mh, h), 2)), rem_spec(7, 7))]
        };
        let tail3 = |q: Formula| rem7_tail(q, 3);
        let half = |d: Formula| lshr(d, 1);
        let g = Some(At::Goal);
        // the MOVK lanes
        never_admitted(
            "MOVK 0x2492->0x2493",
            vec![(rem7_tail(q7(MK7 + (1 << 48), false, 2), 3), rem_spec(7, 7))],
            g,
        );
        never_admitted(
            "MOVK 0xaaab->0xaaac",
            vec![(ubfm(umulh(x(), movk(MK3 + 1)), 1), udiv(x(), 3))],
            g,
        );
        // UMULH -> MUL (the low half)
        let mul_lo = Formula::BvMul(bx(x()), bx(movk(MK7)), 64);
        never_admitted("UMULH->MUL", s20_from(mul_lo.clone(), half(sub(x(), mul_lo)), &tail3), g);
        // the add-back: sub -> add, swapped operands, lsr #2
        never_admitted("add-back add", s20_from(mh7(), half(add(x(), mh7())), &tail3), g);
        never_admitted("add-back swapped", s20_from(mh7(), half(sub(mh7(), x())), &tail3), g);
        never_admitted("add-back lsr #2", s20_from(mh7(), lshr(sub(x(), mh7()), 2), &tail3), g);
        // the remainder tail: lsl #3 -> #2, lsl -> add, final add -> sub
        let q = || q7(MK7, false, 2);
        never_admitted("lsl #2", vec![(rem7_tail(q(), 2), rem_spec(7, 7))], g);
        never_admitted(
            "lsl -> add",
            vec![(add(x(), sub(q(), add(q(), lit(3, 64)))), rem_spec(7, 7))],
            g,
        );
        never_admitted(
            "final add -> sub",
            vec![(sub(x(), sub(q(), shl(q(), 3))), rem_spec(7, 7))],
            g,
        );
        // the IR side
        let s20m = || s20_o2().remove(0).0;
        never_admitted("urem 6", vec![(s20m(), rem_spec(6, 6))], g);
        never_admitted("udiv for urem", vec![(s20m(), udiv(x(), 7))], g);
        never_admitted("divisor 3->5", vec![(q3_at(x()), udiv(x(), 5))], g);
        // divisor 0
        let guarded0 = Formula::Ite(
            bx(Formula::Eq(bx(lit(0, 64)), bx(lit(0, 64)))),
            bx(lit(0, 64)),
            bx(udiv(x(), 0)),
        );
        never_admitted("magic vs guarded /0", vec![(q3_at(x()), guarded0)], g);
        never_admitted("magic vs udiv(x, 0)", vec![(q3_at(x()), udiv(x(), 0))], g);
        // the 32-bit UMULL form (a correct magic, outside the route): within
        // the 64-bit walk, so the kernel, not the walk, refuses it.
        let w = Formula::BvExtract { inner: bx(x()), high: 31, low: 0 };
        let umull =
            Formula::BvMul(bx(Formula::BvZeroExt(bx(w.clone()), 32)), bx(lit(0xAAAA_AAAB, 64)), 64);
        never_admitted(
            "32-bit UMULL",
            vec![(
                lshr(umull, 33),
                Formula::BvZeroExt(bx(Formula::BvUDiv(bx(w), bx(lit(3, 32)), 32)), 32),
            )],
            g,
        );
    })
}

// ── the width walk ───────────────────────────────────────────────────────────

#[test]
fn wider_shapes_are_refused_by_the_walk() {
    on_route_stack(|| {
        let x = x64();
        let w32 = Formula::Var("W".into(), Sort::BitVec(32));
        let mul128 = Formula::BvMul(
            bx(Formula::BvZeroExt(bx(x.clone()), 64)),
            bx(Formula::BvZeroExt(bx(movk(MK3)), 64)),
            128,
        );
        let frame = |inner: Formula| Formula::BvExtract { inner: bx(inner), high: 127, low: 64 };
        let cases = [
            // the low half of the product
            Formula::BvExtract { inner: bx(mul128.clone()), high: 63, low: 0 },
            // the high half minus a bit
            Formula::BvExtract { inner: bx(mul128.clone()), high: 126, low: 63 },
            // 32-bit operands extended by 96
            frame(Formula::BvMul(
                bx(Formula::BvZeroExt(bx(w32.clone()), 96)),
                bx(Formula::BvZeroExt(bx(lit(3, 32)), 96)),
                128,
            )),
            // a 128-bit add in the same frame
            frame(Formula::BvAdd(
                bx(Formula::BvZeroExt(bx(x.clone()), 64)),
                bx(Formula::BvZeroExt(bx(x.clone()), 64)),
                128,
            )),
            // SMULH: sign-extended operands
            frame(Formula::BvMul(
                bx(Formula::BvSignExt(bx(x.clone()), 64)),
                bx(Formula::BvSignExt(bx(movk(MK3)), 64)),
                128,
            )),
            // a 128-bit literal multiplier
            frame(Formula::BvMul(
                bx(Formula::BvZeroExt(bx(x.clone()), 64)),
                bx(lit(i128::from(MK3), 128)),
                128,
            )),
            // a bare 128-bit product
            mul128,
        ];
        for f in cases {
            let items = vec![(
                ubfm(Formula::BvExtract { inner: bx(f.clone()), high: 63, low: 0 }, 1),
                udiv(x64(), 3),
            )];
            assert!(goal_of(&[(f.clone(), x64())]).is_err(), "the walk admitted {f:?}");
            assert!(goal_of(&items).is_err(), "the walk admitted {f:?} inside a quotient");
        }
        // The exact multiply-high frame with an operand outside the fragment:
        // refused by the walk AND by the goal arm itself.
        let bad_operands = [
            // a sign-extended x (a correct magic applied to it)
            (Formula::BvSignExt(bx(w32), 32), movk(MK3)),
            // a 128-bit literal inside a 64-bit operand
            (Formula::BvExtract { inner: bx(lit(5, 128)), high: 63, low: 0 }, movk(MK3)),
            // a variable divisor inside the multiplier
            (x.clone(), udiv_var(x.clone())),
        ];
        for (a, b) in bad_operands {
            let f = umulh(a, b);
            assert!(goal_of(&[(f.clone(), x64())]).is_err(), "the walk admitted {f:?}");
            let mut ctx = ReflectCtx::const_div_goal();
            assert!(reflect_formula(&f, &mut ctx).is_err(), "the umulh arm reflected {f:?}");
        }
        // The arms s10 added to the branch split's walk are not this walk's:
        // an arithmetic shift by a closed amount, a sign extension of a
        // closed operand, and a Bool equality, each alone and around a quotient.
        let ashr = Formula::BvAShr(bx(x64()), bx(lit(3, 64)), 64);
        let sext = Formula::BvSignExt(bx(lit(3, 32)), 32);
        let bool_eq = Formula::Ite(
            bx(Formula::Eq(
                bx(Formula::BvULt(bx(x64()), bx(lit(7, 64)), 64)),
                bx(Formula::Bool(true)),
            )),
            bx(x64()),
            bx(lit(0, 64)),
        );
        for f in [ashr, sext, bool_eq] {
            assert!(goal_of(&[(f.clone(), x64())]).is_err(), "the walk admitted {f:?}");
            assert!(goal_of(&[(x64(), f.clone())]).is_err(), "the walk admitted {f:?} (spec)");
            let around = add(q3_at(x64()), f.clone());
            assert!(
                goal_of(&[(around, udiv(x64(), 3))]).is_err(),
                "the walk admitted {f:?} beside a quotient"
            );
        }
        // A variable divisor anywhere.
        never_admitted("variable divisor", vec![(q3_at(x64()), udiv_var(x64()))], None);
    })
}

fn udiv_var(x: Formula) -> Formula {
    Formula::BvUDiv(bx(x), bx(Formula::Var("Y".into(), Sort::BitVec(64))), 64)
}

// ── the differential ─────────────────────────────────────────────────────────

/// The differential agrees on the true goal and declines a goal whose
/// reflection is wrong: one wrong at many inputs (another multiplier), and
/// one wrong just below 2^64 and right at small inputs (magicu(7)'s
/// multiplier plus 2; it is also wrong at two of the fixed pseudo-random
/// points, so this test alone does not pin the top band:
/// `points_cover_the_top_band` does).
#[test]
fn differential_declines_a_misreflected_goal() {
    on_route_stack(|| {
        let items = div3_o2();
        let (_, sides, leaves) = goal_of(&items).expect("goal");
        let bad_items = vec![(ubfm(umulh(x64(), movk(MK3 ^ 0x10)), 1), udiv(x64(), 3))];
        let (_, bad_sides, _) = goal_of(&bad_items).expect("goal");
        // Wrong just below 2^64, right at the small inputs.
        let top = u128::from(u64::MAX);
        let near = q7(MK7 + 2, false, 2);
        let at = |x: u128| eval_bv(&near, &|n: &str| (n == "X0").then_some(x)).map(|v| v.0);
        let wrong_at: Vec<u128> =
            (0..7).map(|i| top - i).filter(|&x| at(x) != Some(x / 7)).collect();
        assert!(!wrong_at.is_empty(), "MK7+2 is right just below 2^64");
        for x in [0u128, 1, 6, 7, 8, 1 << 63] {
            assert_eq!(at(x), Some(x / 7), "MK7+2 is wrong at {x:#x} too");
        }
        let items7 = div7(false);
        let (_, sides7, leaves7) = goal_of(&items7).expect("goal");
        let (_, near_sides, _) = goal_of(&[(near, udiv(x64(), 7))]).expect("goal");
        let t = Instant::now();
        let good = differential(&items, &sides, &leaves);
        println!("differential (x/3): {:?} in {} us", good, t.elapsed().as_micros());
        let bad = differential(&items, &bad_sides, &leaves);
        let good7 = differential(&items7, &sides7, &leaves7);
        let bad7 = differential(&items7, &near_sides, &leaves7);
        assert!(good.is_ok(), "{good:?}");
        assert!(bad.is_err(), "the differential accepted a misreflected goal");
        assert!(good7.is_ok(), "{good7:?}");
        assert!(bad7.is_err(), "the differential accepted a goal wrong only at {wrong_at:x?}");
        println!("differential: MK7+2 wrong at {wrong_at:x?}: {bad7:?}");
    })
}

// ── the step-(4) rewrite ─────────────────────────────────────────────────────

#[test]
fn rewrite_replaces_the_magic_core() {
    on_route_stack(|| {
        let (m, _) = s20_o2().remove(0);
        let (rewritten, cert) = const_div_rewrite(&m).expect("rewrite");
        let q = udiv(x64(), 7);
        assert_eq!(rewritten, rem7_tail(q.clone(), 3));
        assert_eq!(cert.replaced.len(), 1);
        assert_eq!(cert.replaced[0].1, q);
        assert!(cert.theorem.contains(names::MAGIC_ADDBACK), "{}", cert.theorem);
        assert!(cert.binds(), "the admitted goal is not the replaced pairs'");
        let (m3, _) = div3_o2().remove(0);
        let (r3, c3) = const_div_rewrite(&m3).expect("rewrite x/3");
        assert_eq!(r3, udiv(x64(), 3));
        assert!(c3.theorem.contains(names::MAGIC_NOADD));
        // A cert whose goal is another rewrite's does not bind.
        let mut swapped = c3.clone();
        swapped.goal = cert.goal.clone();
        assert!(!swapped.binds(), "a foreign goal binds");
        // Nothing to rewrite, and a magic outside the band.
        assert!(const_div_rewrite(&x64()).is_none());
        assert!(const_div_rewrite(&ubfm(umulh(x64(), movk(MK3 + 4)), 1)).is_none());
    })
}

/// `replace` opens every node `collect_magic` searches: a quotient under
/// each node kind `children` lists is found and replaced, and in
/// `if (q as i64) < y { q } else { 0 }` both copies of `q` (one under the
/// `BvSLt`) are replaced, the certificate counting one quotient at two
/// sites.
#[test]
fn replace_reaches_every_node_the_search_reaches() {
    let q = q3_at(x64());
    let d = udiv(x64(), 3);
    let y = Formula::Var("Y".into(), Sort::BitVec(64));
    let bq = || bx(q.clone());
    let by = || bx(y.clone());
    let wrappers = vec![
        Formula::Not(bx(Formula::Eq(bq(), by()))),
        Formula::BvNot(bq(), 64),
        Formula::BvZeroExt(bq(), 64),
        Formula::BvSignExt(bq(), 64),
        Formula::BvExtract { inner: bq(), high: 31, low: 0 },
        Formula::And(vec![Formula::Eq(bq(), by())]),
        Formula::Or(vec![Formula::Eq(by(), bq())]),
        Formula::Ite(bx(Formula::Bool(true)), bq(), by()),
        Formula::Store(by(), bq(), by()),
        Formula::Implies(bx(Formula::Bool(true)), bx(Formula::Eq(bq(), by()))),
        Formula::BvAdd(bq(), by(), 64),
        Formula::BvSub(by(), bq(), 64),
        Formula::BvMul(bq(), by(), 64),
        Formula::BvUDiv(by(), bq(), 64),
        Formula::BvSDiv(bq(), by(), 64),
        Formula::BvURem(by(), bq(), 64),
        Formula::BvSRem(bq(), by(), 64),
        Formula::BvAnd(bq(), by(), 64),
        Formula::BvOr(by(), bq(), 64),
        Formula::BvXor(bq(), by(), 64),
        Formula::BvShl(by(), bq(), 64),
        Formula::BvLShr(bq(), by(), 64),
        Formula::BvAShr(by(), bq(), 64),
        Formula::BvULt(bq(), by(), 64),
        Formula::BvULe(by(), bq(), 64),
        Formula::BvSLt(bq(), by(), 64),
        Formula::BvSLe(by(), bq(), 64),
        Formula::BvConcat(bq(), by()),
        Formula::Select(by(), bq()),
    ];
    for w in &wrappers {
        assert!(!children(w).is_empty(), "{w:?}: a leaf to the search");
        let mut found = Vec::new();
        collect_magic(w, &mut found);
        assert_eq!(found, vec![(q.clone(), d.clone())], "{w:?}: the search");
        let mut hits = vec![0];
        let r = replace(w, &found, &mut hits);
        let mut left = Vec::new();
        collect_magic(&r, &mut left);
        assert!(hits == [1] && left.is_empty(), "{w:?}: not replaced ({hits:?})");
    }
    on_route_stack(|| {
        let slt = Formula::BvSLt(bq(), by(), 64);
        let m = Formula::Ite(bx(slt), bq(), bx(lit(0, 64)));
        let (r, cert) = const_div_rewrite(&m).expect("rewrite");
        let want = Formula::Ite(
            bx(Formula::BvSLt(bx(d.clone()), by(), 64)),
            bx(d.clone()),
            bx(lit(0, 64)),
        );
        assert_eq!(r, want);
        assert_eq!((cert.replaced.len(), cert.sites), (1, 2));
        let (_, note) = step4_rewrite("value(return)", &m).expect("the hook rewrites");
        assert!(note.contains("(1 magic quotient(s) replaced by `x / d` at 2 site(s)"), "{note}");
    })
}

/// The differential's points include, for each literal divisor `d`, the
/// `min(d, 64)` values just below 2^64 (where a slightly wrong magic first
/// errs), the largest multiple of `d` below 2^64 and the value before it,
/// and `d - 1, d, d + 1`, besides the edges. Pins the top band, which the
/// misreflection test alone does not.
#[test]
fn points_cover_the_top_band() {
    let top = u128::from(u64::MAX);
    for d in [3u128, 7, 10, 100, 1 << 40] {
        let p = points(&[d]);
        for e in [0, 1, (1 << 63) - 1, 1 << 63, top, d - 1, d, d + 1] {
            assert!(p.contains(&e), "d = {d}: {e:#x} missing");
        }
        for i in 0..d.min(64) {
            assert!(p.contains(&(top - i)), "d = {d}: 2^64 - 1 - {i} missing");
        }
        let q = top / d * d;
        assert!(p.contains(&q) && p.contains(&(q - 1)), "d = {d}: {q:#x} or the one before");
    }
}

/// The gate's magic + 2 byte mutants (`constdiv_gate.rs`) are declined at
/// the search, before any kernel work: `magic_params` puts magicu(3) + 2 and
/// magicu(7) + 2 outside the Granlund-Montgomery band, so `magic_formula`
/// does not match and the hook returns `None` (ay then faces the old miter).
#[test]
fn magic_plus_two_is_declined_at_the_band() {
    let m3 = ubfm(umulh(x64(), movk(MK3 + 2)), 1);
    let m7 = q7(MK7 + 2, false, 2);
    let m7_o0 = q7(MK7 + 2, true, 2);
    assert!(magic_params(u128::from(MK3 + 2), 1, false).is_none());
    assert!(magic_params(u128::from(MK7 + 2), 2, true).is_none());
    for m in [&m3, &m7, &m7_o0] {
        assert!(magic_formula(m).is_none(), "{m:?}");
        assert!(step4_rewrite("value(return)", m).is_none(), "{m:?}");
    }
    // The unmutated twins match.
    assert!(magic_formula(&q3_at(x64())).is_some() && magic_formula(&q7(MK7, false, 2)).is_some());
}

/// The rewrite's guard is the kernel: with the differential off and the
/// builder forced to claim x / 4 for the x / 3 core, the kernel refuses at
/// the band and no rewrite is returned.
#[test]
fn rewrite_guard_is_the_kernel() {
    on_route_stack(|| {
        let m3 = q3_at(x64());
        let r = with_mutant(Mutant::ForceDivisor(4), || rewrite_with(&m3, BranchFilter::Off));
        assert!(
            matches!(&r, Err(Some(Decline::Kernel(k))) if k.starts_with("kernel: TypeCheckFailed")),
            "{:?}",
            r.as_ref().map(|(f, _)| f)
        );
        let (at, why) = refusal_point(&vec![(m3.clone(), udiv(x64(), 4))], Mutant::ForceDivisor(4))
            .expect("refused");
        assert_eq!(at, At::Band, "{why}");
        assert!(with_mutant(Mutant::ForceDivisor(4), || const_div_rewrite(&m3)).is_none());
    })
}

// ── reflection against SMT ───────────────────────────────────────────────────

/// The goal reflection, evaluated by the kernel on closed inputs, computes
/// the value Rust computes, refuses that value with bit 0 flipped, and ay
/// proves the same value and refutes the flipped one. The cases: bare
/// `umulh(x, MK)` (MOVK chain and literal multiplier) at the edge inputs
/// for d = 3 and 7; the whole magic shapes (x / 3, x / 7 in both halving
/// forms, s20's `x % 7`) at closed x; and a faithful division by zero.
#[test]
fn reflection_agrees_with_smt() {
    on_route_stack(|| {
        let mut cases: Vec<(Formula, u128, u32)> = Vec::new();
        for (d, mk) in [(3u128, MK3), (7, MK7)] {
            for x in [0u128, 1, d - 1, d, 1 << 63, u128::from(u64::MAX)] {
                let xl = lit(x as i128, 64);
                let fs = [umulh(xl.clone(), movk(mk)), umulh(xl.clone(), lit(i128::from(mk), 64))];
                for f in fs {
                    let (v, w) = eval_bv(&f, &|_| None).expect("value");
                    assert_eq!(v, (x * u128::from(mk)) >> 64, "Rust umulh at {x:#x}");
                    cases.push((f, v, w));
                }
            }
        }
        for x in [0u128, 6, 7, u128::from(u64::MAX)] {
            let xl = || lit(x as i128, 64);
            let shapes = [
                (q3_at(xl()), x / 3),
                (q7_at(xl(), MK7, false, 2), x / 7),
                (q7_at(xl(), MK7, true, 2), x / 7),
                (rem7_tail_at(xl(), q7_at(xl(), MK7, false, 2), 3), x % 7),
            ];
            for (f, want) in shapes {
                let (v, w) = eval_bv(&f, &|_| None).expect("value");
                assert_eq!(v, want, "Rust value of {f:?}");
                cases.push((f, v, w));
            }
        }
        cases.push((udiv(lit(5, 64), 0), u128::from(u64::MAX), 64));
        let n = cases.len();
        let kernel_cases = cases.clone();
        let bad = run_recheck_thread("constdiv-smt", move || {
            let env = const_div_base().expect("base").clone();
            let check = |e: &clean_kernel::Expr, ty: &clean_kernel::Expr| {
                TypeChecker::with_mode(&env, env.mode()).check_type(e, ty)
            };
            let mut bad = Vec::new();
            for (f, v, w) in &kernel_cases {
                let mut ctx = ReflectCtx::const_div_goal();
                let stated = match reflect_formula(f, &mut ctx) {
                    Ok(r) => kx::evalf(r.bvf),
                    Err(e) => {
                        bad.push(format!("{f:?}: refused: {e}"));
                        continue;
                    }
                };
                let good = kx::bits(*v as i128, *w);
                let flip = kx::bits((*v ^ 1) as i128, *w);
                if let Err(e) = check(&refl(lb(), good.clone()), &eq(lb(), stated.clone(), good)) {
                    bad.push(format!("{f:?}: the kernel did not compute {v:#x}: {e:?}"));
                }
                match check(&refl(lb(), flip.clone()), &eq(lb(), stated, flip)) {
                    Err(e) if format!("{e:?}").starts_with("TypeMismatch") => {}
                    other => bad.push(format!("{f:?}: the flipped value of {v:#x}: {other:?}")),
                }
            }
            bad
        })
        .expect("thread");
        assert!(bad.is_empty(), "{} of {n} cases disagree:\n{}", bad.len(), bad.join("\n"));
        let mut ay_bad = Vec::new();
        for (f, v, w) in &cases {
            let claim = Formula::Eq(bx(f.clone()), bx(lit(*v as i128, *w)));
            let flipped = Formula::Eq(bx(f.clone()), bx(lit((*v ^ 1) as i128, *w)));
            if !matches!(discharge_valid(&claim), Discharge::Proven) {
                ay_bad.push(format!("{f:?}: ay did not prove {v:#x}"));
            }
            if !matches!(discharge_valid(&flipped), Discharge::CounterExample) {
                ay_bad.push(format!("{f:?}: ay found no counterexample to the flipped {v:#x}"));
            }
        }
        assert!(
            ay_bad.is_empty(),
            "{} of {n} cases disagree with ay:\n{}",
            ay_bad.len(),
            ay_bad.join("\n")
        );
        println!("reflection_agrees_with_smt: {n} cases");
    })
}

/// The label lists the `Trust.BVD` theorems the term cites.
#[test]
fn label_names_the_cited_theorems() {
    on_route_stack(|| {
        let ob = obligation(&div3_o2(), BranchFilter::On).expect("obligation");
        let l = run_recheck_thread("constdiv-label", move || {
            let env = const_div_env(&ob.leaves).expect("env");
            theory::label(&env, &ob.proof)
        })
        .expect("thread");
        assert!(l.contains(names::MAGIC_NOADD) && l.ends_with(theory::LABEL_TAIL), "{l}");
    })
}

// ── the goal evaluator against the kernel ────────────────────────────────────

/// `e` with each `BVC_LEAFBIT_*` constant of `bits` replaced by its literal.
fn subst_bits(
    e: &Expr,
    bits: &std::collections::HashMap<Name, bool>,
    memo: &mut std::collections::HashMap<Expr, Expr>,
) -> Expr {
    if let Some(r) = memo.get(e) {
        return r.clone();
    }
    let out = match e.kind() {
        ExprKind::Const(n, _) => match bits.get(n) {
            Some(true) => kx::btrue(),
            Some(false) => kx::bfalse(),
            None => e.clone(),
        },
        ExprKind::App(f, a) => Expr::app(subst_bits(f, bits, memo), subst_bits(a, bits, memo)),
        ExprKind::Lam(bd, ty, body) => {
            Expr::lam(*bd, subst_bits(ty, bits, memo), subst_bits(body, bits, memo))
        }
        ExprKind::Pi(bd, ty, body) => {
            Expr::pi(*bd, subst_bits(ty, bits, memo), subst_bits(body, bits, memo))
        }
        _ => e.clone(),
    };
    memo.insert(e.clone(), out.clone());
    out
}

/// The leaf bits of `X0` at `x`.
fn x0_bits(x: u128) -> std::collections::HashMap<Name, bool> {
    let list = super::add_comm::bit_leaf("X0", 64);
    super::spine(&list)
        .expect("leaf")
        .iter()
        .enumerate()
        .filter_map(|(k, b)| match b.kind() {
            ExprKind::Const(n, _) => Some((n.clone(), (x >> k) & 1 == 1)),
            _ => None,
        })
        .collect()
}

/// The closed per-head cases: every bit-vector head and condition the goal
/// reflection emits, at operands that reach each edge the evaluator models
/// (a zero divisor, a shift amount at and past the width, unequal and equal
/// signed and unsigned comparisons, a high and a low extract, the
/// multiply-high).
fn head_cases() -> Vec<Formula> {
    let a: i128 = 0xF00D_CAFE_1234_5678_u64 as i128;
    let b: i128 = 0x0000_0000_DEAD_BEEF;
    let l = |v: i128| lit(v, 64);
    let bin = |op: fn(Box<Formula>, Box<Formula>, u32) -> Formula, x: i128, y: i128| {
        op(bx(l(x)), bx(l(y)), 64)
    };
    let cond = |c: Formula| Formula::Ite(bx(c), bx(l(a)), bx(l(b)));
    let mut out = vec![
        bin(Formula::BvAdd, a, b),
        bin(Formula::BvSub, b, a),
        bin(Formula::BvMul, a, b),
        bin(Formula::BvAnd, a, b),
        bin(Formula::BvOr, a, b),
        bin(Formula::BvXor, a, b),
        bin(Formula::BvUDiv, a, b),
        bin(Formula::BvUDiv, a, 0),
        Formula::BvZeroExt(bx(lit(b, 32)), 32),
        Formula::BvExtract { inner: bx(l(a)), high: 63, low: 5 },
        Formula::BvExtract { inner: bx(Formula::BvZeroExt(bx(lit(b, 32)), 32)), high: 31, low: 0 },
        umulh(l(a), l(b)),
        umulh(l(a), movk(MK7)),
        cond(Formula::Eq(bx(l(a)), bx(l(a)))),
        cond(Formula::Eq(bx(l(a)), bx(l(b)))),
        cond(Formula::BvULt(bx(l(b)), bx(l(a)), 64)),
        cond(Formula::BvULe(bx(l(a)), bx(l(b)), 64)),
        cond(Formula::BvSLt(bx(l(a)), bx(l(b)), 64)),
        cond(Formula::BvSLt(bx(l(b)), bx(l(a)), 64)),
        cond(Formula::Not(bx(Formula::Eq(bx(l(a)), bx(l(b)))))),
        cond(Formula::And(vec![
            Formula::Eq(bx(l(a)), bx(l(a))),
            Formula::BvULt(bx(l(a)), bx(l(b)), 64),
        ])),
        cond(Formula::Or(vec![
            Formula::Eq(bx(l(a)), bx(l(b))),
            Formula::BvULt(bx(l(b)), bx(l(a)), 64),
        ])),
    ];
    for n in [0, 3, 63, 64, 70] {
        out.push(bin(Formula::BvShl, a, n));
        out.push(bin(Formula::BvLShr, a, n));
    }
    out
}

/// The evaluator the differential reads goal sides with computes what the
/// kernel computes: on every closed per-head case ([`head_cases`]) and on
/// the goal sides of the positives (s20 at O0 and O2, x / 3, x / 7 in both
/// halvings) at the edge points and two others, the kernel accepts
/// `Eq.refl` of the evaluator's value against the stated side, and refuses
/// that value with bit 0 flipped. Without this, a disagreement in the
/// differential could be the model's and not the reflection's.
#[test]
fn goal_evaluator_agrees_with_the_kernel() {
    on_route_stack(|| {
        let mut cases: Vec<(String, Expr, std::collections::HashMap<Name, bool>)> = Vec::new();
        for f in head_cases() {
            let mut ctx = ReflectCtx::const_div_goal();
            let r = reflect_formula(&f, &mut ctx).unwrap_or_else(|e| panic!("{f:?}: {e}"));
            cases.push((format!("{f:?}"), kx::evalf(r.bvf), Default::default()));
        }
        let top = u128::from(u64::MAX);
        for (name, items) in [
            ("s20 O2", s20_o2()),
            ("s20 O0", s20_o0()),
            ("x/3", div3_o2()),
            ("x/7 lsr", div7(false)),
            ("x/7 ubfm", div7(true)),
        ] {
            let (_, sides, _) = goal_of(&items).expect("goal");
            for x in [0u128, 6, 1 << 63, top - 1, top, 0x1234_5678_9abc_def0] {
                let bits = x0_bits(x);
                for (side, g) in [("machine", &sides[0].0), ("spec", &sides[0].1)] {
                    let mut memo = Default::default();
                    let stated = subst_bits(g, &bits, &mut memo);
                    cases.push((format!("{name} {side} at {x:#x}"), stated, bits.clone()));
                }
            }
        }
        let n = cases.len();
        let mut bad = Vec::new();
        let mut values = Vec::new();
        for (what, stated, bits) in &cases {
            match GoalEval::new(bits).list(stated) {
                Some(v) => values.push((what.clone(), stated.clone(), v)),
                None => bad.push(format!("{what}: the evaluator gives no value")),
            }
        }
        let kernel_bad = run_recheck_thread("constdiv-goal-eval", move || {
            let env = const_div_base().expect("base").clone();
            let check =
                |e: &Expr, ty: &Expr| TypeChecker::with_mode(&env, env.mode()).check_type(e, ty);
            let list = |v: &[bool]| {
                v.iter().rev().fold(kx::nil(), |acc, &b| {
                    kx::cons(if b { kx::btrue() } else { kx::bfalse() }, acc)
                })
            };
            let mut bad = Vec::new();
            for (what, stated, v) in &values {
                let good = list(v);
                if let Err(e) = check(&refl(lb(), good.clone()), &eq(lb(), stated.clone(), good)) {
                    bad.push(format!(
                        "{what}: the kernel does not compute the evaluator's value: {e:?}"
                    ));
                }
                let mut flipped = v.clone();
                if let Some(b0) = flipped.first_mut() {
                    *b0 = !*b0;
                }
                let flip = list(&flipped);
                match check(&refl(lb(), flip.clone()), &eq(lb(), stated.clone(), flip)) {
                    Err(e) if format!("{e:?}").starts_with("TypeMismatch") => {}
                    other => bad.push(format!("{what}: the flipped value: {other:?}")),
                }
            }
            bad
        })
        .expect("thread");
        bad.extend(kernel_bad);
        assert!(bad.is_empty(), "{} of {n} cases disagree:\n{}", bad.len(), bad.join("\n"));
        println!("goal_evaluator_agrees_with_the_kernel: {n} cases");
    })
}

/// The differential is consulted on the production path: handed goal sides
/// a misreflection would give (the right side forged to zero; the kernel
/// still checks the true goal, which it accepts), `prove` declines at the
/// differential, and the same items without the fault are proved.
#[test]
fn prove_declines_when_the_differential_disagrees() {
    on_route_stack(|| {
        for items in [div3_o2(), s20_o2()] {
            assert!(prove(&items, BranchFilter::On).is_ok(), "the twin is not proved");
            let r = with_mutant(Mutant::ForgedSides, || prove(&items, BranchFilter::On));
            assert!(
                matches!(&r, Err(Decline::Filter(m)) if m.starts_with("differential: at")),
                "{r:?}"
            );
            let (m, _) = items[0].clone();
            assert!(
                with_mutant(Mutant::ForgedSides, || step4_rewrite("value(return)", &m)).is_none()
            );
        }
    })
}

/// A certificate whose admitted goal is not the replaced pairs' is never
/// used: `const_div_rewrite` and the step-(4) hook return `None`, while the
/// same machine side without the fault is rewritten, the note naming the
/// item, the count and the admitted theorem.
#[test]
fn a_certificate_that_does_not_bind_is_not_used() {
    on_route_stack(|| {
        let m3 = q3_at(x64());
        let (rewritten, note) = step4_rewrite("value(return)", &m3).expect("the twin rewrites");
        assert_eq!(rewritten, udiv(x64(), 3));
        assert!(
            note.starts_with("; value(return) was decided by ay on its CONSTDIV rewrite (1 magic")
                && note.contains(names::MAGIC_NOADD)
                && note.contains(theory::LABEL_TAIL),
            "{note}"
        );
        assert!(with_mutant(Mutant::ForeignGoal, || const_div_rewrite(&m3)).is_none());
        assert!(with_mutant(Mutant::ForeignGoal, || step4_rewrite("value(return)", &m3)).is_none());
        let (m20, _) = s20_o0().remove(0);
        assert!(step4_rewrite("value(return)", &m20).is_some());
        assert!(
            with_mutant(Mutant::ForeignGoal, || step4_rewrite("value(return)", &m20)).is_none()
        );
    })
}

/// The differential, measured per obligation (debug build): the Rust
/// evaluator replaces the kernel's evaluation of each goal side, which cost
/// 4.3 to 9.8 s per obligation for 22 to 30 checks (stage A, debug). Bound
/// generously against a loaded machine; the measured value is printed.
#[test]
fn differential_is_fast() {
    on_route_stack(|| {
        for (name, items) in
            [("s20 O2", s20_o2()), ("s20 O0", s20_o0()), ("x/3", div3_o2()), ("x/7", div7(true))]
        {
            let (_, sides, leaves) = goal_of(&items).expect("goal");
            let t = Instant::now();
            let checks = differential(&items, &sides, &leaves).expect("agrees");
            let ms = t.elapsed().as_millis();
            println!("differential {name}: {checks} checks in {ms} ms");
            assert!(checks >= 40, "{name}: only {checks} checks");
            assert!(ms < 1_000, "{name}: the differential took {ms} ms");
        }
    })
}

// ── stage B2: the step-(5) route (DECISION_QUEUE CONSTDIV-1) ─────────────────
//
// The call-event gate's step (5) hands the dispatch (`branch_dispatch.rs`)
// the ORIGINAL conjunction: each item's two sides under the reach guard
// `ite(d != 0, 1, 0) != 0` the producer's `assert` leaves, and the (4b)
// check item `ite(not reach, 1, 0) == 0`. [`gate_conj`] builds it from the
// hand-built shapes above; `gate_conjunctions_are_the_captured_ones` pins
// that it is, byte for byte, what the gate's own `TRUST_GATE_TRACE=1` line
// `[branch-split] conj <json>` printed for `constdiv_gate.rs`'s cells
// (2026-11-15, aa5bb6efee plus this stage; identical on both triples, and
// for x / 3 at O0 and O2).

/// `ite(d != 0, 1, 0) != 0` at the producer's 32-bit `icmp` width.
fn reach(d: i128) -> Formula {
    let icmp = Formula::Ite(
        bx(Formula::Not(bx(Formula::Eq(bx(lit(d, 64)), bx(lit(0, 64)))))),
        bx(lit(1, 32)),
        bx(lit(0, 32)),
    );
    Formula::Not(bx(Formula::Eq(bx(icmp), bx(lit(0, 32)))))
}

/// `items` as step (5) receives them for a divisor `d`: each side under the
/// reach guard (`0` off it), then the (4b) check item.
fn gate_conj(items: Items, d: i128) -> Items {
    let guard = |f: Formula| Formula::Ite(bx(reach(d)), bx(f), bx(lit(0, 64)));
    let mut conj: Items = items.into_iter().map(|(l, r)| (guard(l), guard(r))).collect();
    conj.push((
        Formula::Ite(bx(Formula::Not(bx(reach(d)))), bx(lit(1, 1)), bx(lit(0, 1))),
        lit(0, 1),
    ));
    conj
}

fn gate_s20_o0() -> Items {
    gate_conj(s20_o0(), 7)
}
fn gate_s20_o2() -> Items {
    gate_conj(s20_o2(), 7)
}
fn gate_div3() -> Items {
    gate_conj(div3_o2(), 3)
}

/// The labels the kernel's admission gives the three gate conjunctions,
/// pinned exactly (`constdiv_gate.rs` pins the same three on the gate).
const LABEL_S20_O0: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_and_cong+\
Clean.BVC.bvf_div_cong+Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+Clean.BVC.bvf_or_zero_id+\
Clean.BVC.bvf_shl_cong+Clean.BVC.bvf_sub_cong+Clean.BVC.bvf_zext_cong+Clean.BVC.divGuardBridge+\
Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVD.magic_addback+Trust.BVD.rem_tail+\
Trust.BVD.ubfm_k+Trust.BVV.len_natToBv+Trust.BVD constant division (magic multiply-high, \
kernel-checked)";
const LABEL_S20_O2: &str = "Clean.BVC.bvf_add_cong+Clean.BVC.bvf_and_cong+\
Clean.BVC.bvf_div_cong+Clean.BVC.bvf_lshr_cong+Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+\
Clean.BVC.bvf_shl_cong+Clean.BVC.bvf_sub_cong+Clean.BVC.bvf_zext_cong+Clean.BVC.divGuardBridge+\
Trust.BVB.ite_cong+Trust.BVB.ite_false+Trust.BVD.lshr_k+Trust.BVD.magic_addback+\
Trust.BVD.rem_tail+Trust.BVV.len_natToBv+Trust.BVD constant division (magic multiply-high, \
kernel-checked)";
const LABEL_DIV3: &str = "Clean.BVC.bvf_and_cong+Clean.BVC.bvf_div_cong+\
Clean.BVC.bvf_mul_cong+Clean.BVC.bvf_or_cong+Clean.BVC.bvf_zext_cong+Clean.BVC.divGuardBridge+\
Trust.BVB.ite_cong+Trust.BVD.magic_noadd+Trust.BVD constant division (magic multiply-high, \
kernel-checked)";

/// The gate's step-(5) conjunctions are the hand-built ones: JSON length and
/// FNV-1a of `serde_json::to_string`, as the gate's trace line printed them.
#[test]
fn gate_conjunctions_are_the_captured_ones() {
    for (name, items, want) in [
        ("s20 O0", gate_s20_o0(), (3827, 18053156794246319964)),
        ("s20 O2", gate_s20_o2(), (3759, 16451400732185672535)),
        ("x/3", gate_div3(), (1536, 5975927846732980783)),
    ] {
        let s = serde_json::to_string(&items).expect("json");
        assert_eq!((s.len(), fnv1a(&s)), want, "{name}: {s}");
    }
}

/// The dispatch proves each gate conjunction by THIS route: the branch split
/// and the division split decline it (the 128-bit product is outside the
/// branch walk; no divisor has a variable), and the constant division route
/// returns `KernelInstantiated` with its exact label. Its kernel cost per
/// obligation is measured (debug build, printed) and bounded.
#[test]
fn the_dispatch_proves_the_gate_conjunctions_by_const_div() {
    use super::super::{branch_dispatch, div_split};
    on_route_stack(|| {
        let _ = prove(&div3_o2(), BranchFilter::Off); // the base, once per process
        for (name, items, want) in [
            ("s20 O0", gate_s20_o0(), LABEL_S20_O0),
            ("s20 O2", gate_s20_o2(), LABEL_S20_O2),
            ("x/3", gate_div3(), LABEL_DIV3),
        ] {
            assert!(super::super::branch_split::try_branch_split_conjunction(&items).is_none());
            assert!(div_split::try_conjunction(&items).is_none(), "{name}: div split");
            let t = Instant::now();
            let ev = branch_dispatch::try_conjunction(&items)
                .unwrap_or_else(|| panic!("{name}: the dispatch declined"));
            let ms = t.elapsed().as_millis();
            println!("const-div dispatch {name}: {ms} ms: {}", label(&ev));
            assert_eq!(label(&ev), want, "{name}");
            assert!(ms < 20_000, "{name}: the route took {ms} ms");
        }
    })
}

/// The gate conjunctions with the spec's divisor one off (and s20's
/// remainder multiplier one off): each item under the reach guard, then the
/// (4b) check item, exactly as [`gate_conj`] builds the true ones.
fn wrong_gate_conjs() -> [(&'static str, Items); 5] {
    [
        ("s20 O2 / 6", gate_conj(vec![(s20_o2()[0].0.clone(), rem_spec(6, 6))], 7)),
        ("s20 O2 * 6", gate_conj(vec![(s20_o2()[0].0.clone(), rem_spec(7, 6))], 7)),
        ("s20 O0 / 8", gate_conj(vec![(s20_o0()[0].0.clone(), rem_spec(8, 8))], 7)),
        ("x/3 / 2", gate_conj(vec![(q3_at(x64()), udiv(x64(), 2))], 3)),
        ("x/3 / 4", gate_conj(vec![(q3_at(x64()), udiv(x64(), 4))], 3)),
    ]
}

/// The route admits only the conjunction, never the step-(4) certificate:
/// for each of [`wrong_gate_conjs`], the machine side's magic quotients are
/// still certified by the step-(4) rewrite (asserted), yet the dispatch
/// declines.
#[test]
fn the_dispatch_admits_only_the_conjunction() {
    use super::super::branch_dispatch;
    on_route_stack(|| {
        for (name, items) in wrong_gate_conjs() {
            assert!(
                step4_rewrite("value(return)", &items[0].0).is_some(),
                "{name}: the step-(4) certificate is missing"
            );
            assert_eq!(branch_dispatch::try_conjunction(&items), None, "{name}: ADMITTED");
        }
    })
}

/// The KERNEL, not only the Rust filters, refuses each of
/// [`wrong_gate_conjs`] through the whole stage-B2 composition (every item
/// under the reach guard, through `Trust.BVB.ite_cong`, then the closed
/// (4b) check item that [`closed_meet`](super::closed_meet) lets through):
/// with the filters on the core meet declines it first (pinned, so a
/// change of the declining layer is seen); with the filters off the term
/// reaches the kernel and the kernel refuses it. The true twins are proved
/// with the filters off too, so the refusal is the wrong divisor's.
#[test]
fn wrong_gate_conjunctions_are_refused_by_the_kernel() {
    on_route_stack(|| {
        for (name, items) in
            [("s20 O0", gate_s20_o0()), ("s20 O2", gate_s20_o2()), ("x/3", gate_div3())]
        {
            let r = prove(&items, BranchFilter::Off);
            assert!(r.is_ok(), "{name}, the true twin, filters off: {r:?}");
        }
        for (name, items) in wrong_gate_conjs() {
            let on = prove(&items, BranchFilter::On);
            assert!(
                matches!(&on, Err(Decline::Filter(m)) if m == "const-div: the cores do not meet"),
                "{name}, filters on: {on:?}"
            );
            let off = prove(&items, BranchFilter::Off);
            assert!(kernel_refused(&off), "{name}, filters off: {off:?}");
        }
    })
}

/// [`closed_meet`](super::closed_meet) lets a closed item with differing
/// cores through only when each core stays on [`CONSTDIV_WHITELIST`](super::CONSTDIV_WHITELIST):
/// `3 * 5 == 15` is variable-free and equal in Rust evaluation, yet its
/// left core multiplies closed data (`BvF.Mul`, off the list), so the
/// filter declines it, although the kernel, filters off, proves it (the
/// item is true; the list bounds what the kernel evaluates, it does not
/// decide truth).
#[test]
fn closed_meet_declines_closed_data_off_the_whitelist() {
    use super::{closed_meet, has_var, no_vars, note_closed};
    on_route_stack(|| {
        let (l, r) = (Formula::BvMul(bx(lit(3, 64)), bx(lit(5, 64)), 64), lit(15, 64));
        let mut ctx = ReflectCtx::const_div_proving();
        let rl = reflect_formula(&l, &mut ctx).expect("reflects");
        let rr = reflect_formula(&r, &mut ctx).expect("reflects");
        assert_ne!(rl.core, rr.core, "the cores meet: closed_meet is not consulted");
        assert!(!has_var(&l) && !has_var(&r));
        assert_eq!(eval_bv(&l, &no_vars), eval_bv(&r, &no_vars));
        assert!(!note_closed(&kx::evalf(rl.core.clone())), "the product core is on the list");
        assert!(!closed_meet(&l, &r, &rl.core, &rr.core));
        let item = [(l, r)];
        let on = prove(&item, BranchFilter::On);
        assert!(
            matches!(&on, Err(Decline::Filter(m)) if m == "const-div: the cores do not meet"),
            "filters on: {on:?}"
        );
        assert!(prove(&item, BranchFilter::Off).is_ok(), "the kernel refuses a true closed item");
    })
}

/// [`closed_meet`](super::closed_meet) asks both Formula sides to be
/// variable-free, not only to evaluate: `if 1 == 1 { c } else { x }` against
/// `0`, with `c` the closed check value `ite(3 == 0, 1, 0)`, evaluates in
/// Rust without `x` (the dead arm), and its proving core drops that arm, so
/// the cores differ only as the check item's do and mention no leaf bit; the
/// variable alone makes the filter decline it. The kernel, filters off,
/// proves it (it is true).
#[test]
fn closed_meet_needs_both_sides_variable_free() {
    use super::{closed_meet, has_var, no_vars};
    on_route_stack(|| {
        let c = Formula::Ite(bx(Formula::Not(bx(reach(3)))), bx(lit(1, 64)), bx(lit(0, 64)));
        let l = Formula::Ite(bx(Formula::Eq(bx(lit(1, 64)), bx(lit(1, 64)))), bx(c), bx(x64()));
        let r = lit(0, 64);
        assert!(has_var(&l));
        assert_eq!(eval_bv(&l, &no_vars), Some((0, 64)), "the dead arm is evaluated");
        let mut ctx = ReflectCtx::const_div_proving();
        let rl = reflect_formula(&l, &mut ctx).expect("reflects");
        let rr = reflect_formula(&r, &mut ctx).expect("reflects");
        assert_ne!(rl.core, rr.core, "the cores meet: closed_meet is not consulted");
        assert!(!closed_meet(&l, &r, &rl.core, &rr.core));
        let item = [(l, r)];
        let on = prove(&item, BranchFilter::On);
        assert!(
            matches!(&on, Err(Decline::Filter(m)) if m == "const-div: the cores do not meet"),
            "filters on: {on:?}"
        );
        let off = prove(&item, BranchFilter::Off);
        assert!(off.is_ok(), "the kernel refuses a true item: {off:?}");
    })
}

/// The step-(4) rewrite can certify a variable-free pair: a closed dividend
/// (`umulh(100, M3) >> 1`, as unfolded O0 bytes might give) is rewritten to
/// `100 / 3`, its pair `(core, BvUDiv(100, 3))` mentions no variable, and
/// its two proving cores are EQUAL, so that pair is admitted by the core
/// meet, not by [`closed_meet`](super::closed_meet).
#[test]
fn a_closed_dividend_pair_meets_without_closed_meet() {
    use super::has_var;
    on_route_stack(|| {
        let m = q3_at(lit(100, 64));
        let q = udiv(lit(100, 64), 3);
        let (rewritten, cert) = const_div_rewrite(&m).expect("the closed quotient rewrites");
        assert_eq!(rewritten, q);
        assert_eq!(cert.replaced, vec![(m.clone(), q.clone())]);
        assert!(!has_var(&m) && !has_var(&q));
        let mut ctx = ReflectCtx::const_div_proving();
        let cl = reflect_formula(&m, &mut ctx).expect("reflects").core;
        let cr = reflect_formula(&q, &mut ctx).expect("reflects").core;
        assert_eq!(cl, cr, "the closed pair's cores differ");
    })
}

/// The pre-filter: the dispatch tries the route only when some side holds
/// the exact multiply-high. The remainder tail `x + (q - (q << 3))` against
/// `x - q * 7` with `q = x / 7` has none: the route on its own proves it
/// (`Trust.BVD.rem_tail`), the branch and division splits decline it, and
/// the dispatch declines it too.
#[test]
fn the_pre_filter_keeps_the_route_to_multiply_highs() {
    use super::super::{branch_dispatch, div_split};
    on_route_stack(|| {
        let q = udiv(x64(), 7);
        let items =
            vec![(rem7_tail(q.clone(), 3), sub(x64(), Formula::BvMul(bx(q), bx(lit(7, 64)), 64)))];
        assert!(
            !items
                .iter()
                .any(|(l, r)| branch_dispatch::has_umulh(l) || branch_dispatch::has_umulh(r))
        );
        let ev = try_conjunction(&items).expect("the route alone proves it");
        assert!(label(&ev).contains(names::REM_TAIL), "{}", label(&ev));
        assert!(super::super::branch_split::try_branch_split_conjunction(&items).is_none());
        assert!(div_split::try_conjunction(&items).is_none());
        assert_eq!(branch_dispatch::try_conjunction(&items), None, "the pre-filter let it through");
    })
}

/// The pre-filter reads exactly the multiply-high shape, at any depth, and
/// nothing near it.
#[test]
fn the_pre_filter_reads_the_multiply_high_shape_only() {
    use super::super::branch_dispatch::has_umulh;
    let near = |lz: u32, rz: u32, high: u32, low: u32| Formula::BvExtract {
        inner: bx(Formula::BvMul(
            bx(Formula::BvZeroExt(bx(x64()), lz)),
            bx(Formula::BvZeroExt(bx(movk(MK3)), rz)),
            128,
        )),
        high,
        low,
    };
    assert!(has_umulh(&umulh(x64(), movk(MK3))));
    assert!(has_umulh(&near(64, 64, 127, 64)));
    assert!(gate_s20_o0().iter().any(|(l, _)| has_umulh(l)), "inside a guarded core");
    assert!(!gate_s20_o0().iter().any(|(_, r)| has_umulh(r)), "the spec side has none");
    for f in [
        near(64, 64, 63, 0),
        near(64, 64, 127, 63),
        near(63, 65, 127, 64),
        Formula::BvMul(bx(x64()), bx(movk(MK3)), 64),
        udiv(x64(), 3),
    ] {
        assert!(!has_umulh(&f), "{f:?}");
    }
}

/// The closed-core meet (decline-only): the (4b) check item's two cores
/// differ (`ite` over a closed condition against `0`), and the route
/// accepts that item only because both sides are closed, evaluate to one
/// value and stay on the whitelist; the kernel then decides it. A closed
/// check item that is FALSE (`d = 0`: the condition holds, the left side is
/// `1`) is declined by that filter, and with the filters off the kernel
/// refuses it.
#[test]
fn a_closed_check_item_is_decided_by_the_kernel() {
    on_route_stack(|| {
        let check = gate_div3().pop().expect("the check item");
        let r = prove(std::slice::from_ref(&check), BranchFilter::On);
        assert!(r.is_ok(), "the true check item: {r:?}");
        let false_check = gate_conj(Vec::new(), 0).pop().expect("the check item at d = 0");
        let r = prove(std::slice::from_ref(&false_check), BranchFilter::On);
        assert!(
            matches!(&r, Err(Decline::Filter(m)) if m.contains("cores do not meet")),
            "the false check item: {r:?}"
        );
        let r = prove(std::slice::from_ref(&false_check), BranchFilter::Off);
        assert!(kernel_refused(&r), "the false check item, filters off: {r:?}");
    })
}

/// r01's step-(5) conjunctions at O0 and O2, as the gate's trace line printed them for
/// `constdiv_gate.rs`'s r01 cells (2026-11-15; identical on both triples): `value(return)`
/// under the reach guard, then the (4b) check item.
const R01_O0: &str = r#"[[{"Ite":[{"Not":{"Eq":[{"Ite":[{"Not":{"Eq":[{"BitVec":{"value":3,"width":64}},{"BitVec":{"value":0,"width":64}}]}},{"BitVec":{"value":1,"width":32}},{"BitVec":{"value":0,"width":32}}]},{"BitVec":{"value":0,"width":32}}]}},{"BvOr":[{"BitVec":{"value":0,"width":64}},{"BvAdd":[{"BvSub":[{"BvOr":[{"BvShl":[{"BvAdd":[{"BvZeroExt":[{"BvExtract":{"inner":{"BvExtract":{"inner":{"BvMul":[{"BvZeroExt":[{"Var":["X0",{"BitVec":64}]},64]},{"BvZeroExt":[{"BvOr":[{"BvAnd":[{"BvOr":[{"BvAnd":[{"BvOr":[{"BvAnd":[{"BitVec":{"value":43691,"width":64}},{"BitVec":{"value":-4294901761,"width":64}},64]},{"BitVec":{"value":2863267840,"width":64}},64]},{"BitVec":{"value":-281470681743361,"width":64}},64]},{"BitVec":{"value":187647121162240,"width":64}},64]},{"BitVec":{"value":"-18446462598732840961","width":64}},64]},{"BitVec":{"value":12297641732488560640,"width":64}},64]},64]},128]},"high":127,"low":64}},"high":63,"low":1}},1]},{"BvMul":[{"BvXor":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":85,"width":64}},64]},{"BitVec":{"value":2,"width":64}},64]},64]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":3,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]},{"BvAnd":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":7,"width":64}},64]},64]},{"BvLShr":[{"Var":["X0",{"BitVec":64}]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":1,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]},64]},{"BitVec":{"value":11,"width":64}},64]},64]},{"BitVec":{"value":0,"width":64}}]},{"Ite":[{"Not":{"Eq":[{"Ite":[{"Not":{"Eq":[{"BitVec":{"value":3,"width":64}},{"BitVec":{"value":0,"width":64}}]}},{"BitVec":{"value":1,"width":32}},{"BitVec":{"value":0,"width":32}}]},{"BitVec":{"value":0,"width":32}}]}},{"BvAdd":[{"BvSub":[{"BvOr":[{"BvShl":[{"BvAdd":[{"BvUDiv":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":3,"width":64}},64]},{"BvMul":[{"BvXor":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":85,"width":64}},64]},{"BitVec":{"value":2,"width":64}},64]},64]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":3,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]},{"BvAnd":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":7,"width":64}},64]},64]},{"BvLShr":[{"Var":["X0",{"BitVec":64}]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":1,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]},64]},{"BitVec":{"value":11,"width":64}},64]},{"BitVec":{"value":0,"width":64}}]}],[{"Ite":[{"Not":{"Not":{"Eq":[{"Ite":[{"Not":{"Eq":[{"BitVec":{"value":3,"width":64}},{"BitVec":{"value":0,"width":64}}]}},{"BitVec":{"value":1,"width":32}},{"BitVec":{"value":0,"width":32}}]},{"BitVec":{"value":0,"width":32}}]}}},{"BitVec":{"value":1,"width":1}},{"BitVec":{"value":0,"width":1}}]},{"BitVec":{"value":0,"width":1}}]]"#;
const R01_O2: &str = r#"[[{"Ite":[{"Not":{"Eq":[{"Ite":[{"Not":{"Eq":[{"BitVec":{"value":3,"width":64}},{"BitVec":{"value":0,"width":64}}]}},{"BitVec":{"value":1,"width":32}},{"BitVec":{"value":0,"width":32}}]},{"BitVec":{"value":0,"width":32}}]}},{"BvAdd":[{"BvSub":[{"BvOr":[{"BvShl":[{"BvAdd":[{"BvZeroExt":[{"BvExtract":{"inner":{"BvExtract":{"inner":{"BvMul":[{"BvZeroExt":[{"Var":["X0",{"BitVec":64}]},64]},{"BvZeroExt":[{"BvOr":[{"BvAnd":[{"BvOr":[{"BvAnd":[{"BvOr":[{"BvAnd":[{"BitVec":{"value":43691,"width":64}},{"BitVec":{"value":-4294901761,"width":64}},64]},{"BitVec":{"value":2863267840,"width":64}},64]},{"BitVec":{"value":-281470681743361,"width":64}},64]},{"BitVec":{"value":187647121162240,"width":64}},64]},{"BitVec":{"value":"-18446462598732840961","width":64}},64]},{"BitVec":{"value":12297641732488560640,"width":64}},64]},64]},128]},"high":127,"low":64}},"high":63,"low":1}},1]},{"BvShl":[{"BvXor":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":85,"width":64}},64]},{"BitVec":{"value":1,"width":64}},64]},64]},{"BvAnd":[{"BitVec":{"value":3,"width":64}},{"BitVec":{"value":63,"width":64}},64]},64]},{"BvAnd":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":7,"width":64}},64]},64]},{"BvLShr":[{"Var":["X0",{"BitVec":64}]},{"BvAnd":[{"BitVec":{"value":1,"width":64}},{"BitVec":{"value":63,"width":64}},64]},64]},64]},{"BitVec":{"value":11,"width":64}},64]},{"BitVec":{"value":0,"width":64}}]},{"Ite":[{"Not":{"Eq":[{"Ite":[{"Not":{"Eq":[{"BitVec":{"value":3,"width":64}},{"BitVec":{"value":0,"width":64}}]}},{"BitVec":{"value":1,"width":32}},{"BitVec":{"value":0,"width":32}}]},{"BitVec":{"value":0,"width":32}}]}},{"BvAdd":[{"BvSub":[{"BvOr":[{"BvShl":[{"BvAdd":[{"BvUDiv":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":3,"width":64}},64]},{"BvMul":[{"BvXor":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":85,"width":64}},64]},{"BitVec":{"value":2,"width":64}},64]},64]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":3,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]},{"BvAnd":[{"Var":["X0",{"BitVec":64}]},{"BitVec":{"value":7,"width":64}},64]},64]},{"BvLShr":[{"Var":["X0",{"BitVec":64}]},{"BvAnd":[{"BvAnd":[{"BvSignExt":[{"BitVec":{"value":1,"width":32}},32]},{"BitVec":{"value":63,"width":64}},64]},{"BitVec":{"value":63,"width":64}},64]},64]},64]},{"BitVec":{"value":11,"width":64}},64]},{"BitVec":{"value":0,"width":64}}]}],[{"Ite":[{"Not":{"Not":{"Eq":[{"Ite":[{"Not":{"Eq":[{"BitVec":{"value":3,"width":64}},{"BitVec":{"value":0,"width":64}}]}},{"BitVec":{"value":1,"width":32}},{"BitVec":{"value":0,"width":32}}]},{"BitVec":{"value":0,"width":32}}]}}},{"BitVec":{"value":1,"width":1}},{"BitVec":{"value":0,"width":1}}]},{"BitVec":{"value":0,"width":1}}]]"#;

/// r01 stays [VALIDATED] at stage B2 (`constdiv_gate.rs` `r01_gets_past_step_4_on_the_rewrite`)
/// because the CONSTDIV walk refuses `value(return)` at its shift amounts: the producer lowers
/// `<< 3` and `>> 1` with the amounts `(sext i32 3 to u64) & 63 & 63` and `(sext i32 1 to u64) & 63
/// & 63` (on the spec side, and at O0 on the machine side; at O2 the machine's `lsr` amount is
/// `1 & 63`), and this module's walk (the branch walk before s10) has no sign-extension arm and
/// admits a logical right shift only by a literal amount. Those are the only refusals: with each
/// `SignExt(v, 32)` of a 32-bit literal replaced by its 64-bit value and each variable-free
/// non-literal `lshr` amount by its value, every side passes the walk at one width. The route
/// declines both conjunctions as captured.
#[test]
fn r01_declines_at_the_shift_amounts_only() {
    use super::walk;
    for (name, json) in [("O0", R01_O0), ("O2", R01_O2)] {
        let items: Items = serde_json::from_str(json).expect("fixture parses");
        assert_eq!(items.len(), 2, "{name}");
        let why = goal_of(&items).err().unwrap_or_default();
        assert!(why.contains("outside the width walk"), "{name}: {why}");
        assert!(walk(&items[0].1, &mut 0).is_none(), "{name}: the spec side passes the walk");
        on_route_stack(|| assert!(try_conjunction(&items).is_none(), "{name}: admitted"));
        let fix = |f: &Formula| {
            f.clone().map(&mut |n| match n {
                Formula::BvSignExt(x, 32) => match *x {
                    Formula::BitVec { value, width: 32 } if value >= 0 => {
                        Formula::BitVec { value, width: 64 }
                    }
                    x => Formula::BvSignExt(Box::new(x), 32),
                },
                Formula::BvLShr(l, r, 64) if !matches!(*r, Formula::BitVec { .. }) => {
                    match eval_bv(&r, &|_| None) {
                        Some((v, 64)) => Formula::BvLShr(l, bx(lit(v as i128, 64)), 64),
                        _ => Formula::BvLShr(l, r, 64),
                    }
                }
                n => n,
            })
        };
        let fixed: Items = items.iter().map(|(l, r)| (fix(l), fix(r))).collect();
        assert_ne!(fixed, items, "{name}: nothing was replaced");
        for (i, (l, r)) in fixed.iter().enumerate() {
            let w = walk(l, &mut 0);
            assert!(w.is_some() && w == walk(r, &mut 0), "{name} item {i}: {w:?}");
        }
    }
}
