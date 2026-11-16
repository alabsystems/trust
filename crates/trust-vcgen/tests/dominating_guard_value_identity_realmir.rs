// Real-MIR cover for a FALSE PROOF in the dominating-guard fact miner, and for the
// precision the fix keeps: a guard fact may bound an operation's operand only when the
// operation reads the very VALUE the guard tested.
//
//   pub fn loop_kill(mut a: i64, c: bool, c2: bool) -> i64 {
//       loop {
//           if a > -1000 && a < 1000 {
//               if c {
//                   a = i64::MAX;
//                   if c2 { continue; }
//               }
//               return a * a;          // c && !c2: i64::MAX * i64::MAX
//           } else {
//               return 0;
//           }
//       }
//   }
//
// really overflows (`c = true, c2 = false`), and the deployed pair PROVED it (the
// interval backend, both lanes) on the retired miner.
//
// THE DEFECT. The retired miner (`overflow_vc::v2_dominating_linear_facts_matching`)
// kept a guard fact when the subject's VERSION TOKEN at the guard equalled its token
// at the multiply. A version token spells the subject's reaching-definition SET (D15),
// and a loop makes two points share a set across a write: `a` reaches the guard as
// `{entry, a = MAX}` (the `continue` edge) and reaches the multiply as `{entry, a =
// MAX}` too (the `!c` edge and the `!c2` edge), so the guard's `-1000 < a < 1000`
// bounded an operand that, on the `c && !c2` path, is `i64::MAX`. The 128-bit
// negation lane, which shares the miner since 2026-09-21, inherited it
// (`neg128_dominating_guard_realmir`'s `loop_kill` twin).
//
// THE FIX. `generate::dominating_facts` keys every fact on the SSA VALUE its subject
// holds at the guard (`version_ssa::ValueId`: the def statement, or the join, whose
// value the read sees) and offers it only below a DOMINATING guarded edge. `a` at the
// guard is the loop header's join; at the multiply it is the join at the multiply's
// own block, where `a = MAX` meets the guarded value — a different value, so no fact.
//
// THE PRECISION KEPT. `loop_fresh` re-tests the value each iteration reads and writes
// `a` only AFTER the multiply; the guard and the multiply read the same join, the fact
// lands, and the row stays unrefuted.
//
//   pub fn loop_fresh(mut a: i64, n: u32) -> i64 {
//       let mut r = 0;
//       let mut i = 0;
//       while i < n {
//           if a > -1000 && a < 1000 { r = a * a; }
//           a = a.wrapping_mul(3);
//           i += 1;
//       }
//       r
//   }
//
// Fixtures are this tree's stage1's own extraction, both lanes:
//
//   rustc --edition 2021 --crate-type lib     -Ztrust-verify=on -Ztrust-policy=advisory \
//         -Ztrust-dump=mir:<dir> mul64_guard_value_identity.rs
//   rustc --edition 2021 --crate-type lib -O  (same)
use trust_types::{
    BinOp, Formula, VcKind, VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const LANES: [&str; 2] = ["default", "release"];

fn load(name: &str, lane: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/mul64_guard_{name}_{lane}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn mul_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
        .collect()
}

/// The deployed backend pair, in the compiler's order.
fn router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![
        Box::new(trust_router::interval_backend::IntervalBackend),
        Box::new(test_router::test_ay_backend()),
    ])
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

/// Every `fresh BV operand var CMP constant` atom of the row — the dominating facts
/// `v2_bv_mul_dominating_guard_constraints` rendered onto the operands.
fn operand_bound_atoms(vc: &VerificationCondition) -> Vec<String> {
    fn walk(f: &Formula, out: &mut Vec<String>) {
        let is_operand =
            |f: &Formula| matches!(f, Formula::Var(name, _) if name.starts_with("__trust_ovf_bv_"));
        let is_const = |f: &Formula| matches!(f, Formula::BitVec { .. });
        match f {
            Formula::BvSLt(a, b, _)
            | Formula::BvSLe(a, b, _)
            | Formula::BvULt(a, b, _)
            | Formula::BvULe(a, b, _)
                if (is_operand(a) && is_const(b)) || (is_const(a) && is_operand(b)) =>
            {
                out.push(format!("{f:?}"));
            }
            _ => {
                for child in f.children() {
                    walk(child, out);
                }
            }
        }
    }
    let mut out = Vec::new();
    walk(&vc.formula, &mut out);
    out
}

/// Anti-vacuity: each fixture still multiplies under a guard, in both lanes.
#[test]
fn every_fixture_still_raises_a_multiply_row() {
    for name in ["loop_kill", "loop_fresh"] {
        for lane in LANES {
            assert!(!mul_rows(&load(name, lane)).is_empty(), "{name} {lane}: no multiply row");
        }
    }
}

/// THE FALSE PROOF, closed. `loop_kill`'s guard bounds a value the multiply does not
/// read on every path, so no guard bound may reach the operands — and the row, which
/// really overflows, is REFUTED.
#[test]
fn a_guard_killed_inside_the_loop_bounds_nothing_and_the_overflow_is_refuted() {
    for lane in LANES {
        let rows = mul_rows(&load("loop_kill", lane));
        for vc in &rows {
            let atoms = operand_bound_atoms(vc);
            assert!(
                atoms.is_empty(),
                "loop_kill {lane}: the guard tested a value the multiply does not read on the \
                 `c && !c2` path; it must not bound the operands: {atoms:?}"
            );
            let result = verdict(vc);
            assert!(
                matches!(result, VerificationResult::Failed { .. }),
                "loop_kill {lane}: `i64::MAX * i64::MAX` is reachable, so the row must be \
                 refuted: {result:?}"
            );
        }
    }
}

/// THE PRECISION KEPT. `loop_fresh`'s guard tests the value each iteration multiplies;
/// the bound reaches the operands and the safe row is not refuted.
#[test]
fn a_guard_on_the_value_the_iteration_reads_still_bounds_it() {
    for lane in LANES {
        let rows = mul_rows(&load("loop_fresh", lane));
        for vc in &rows {
            let atoms = operand_bound_atoms(vc);
            assert!(
                !atoms.is_empty(),
                "loop_fresh {lane}: the guard and the multiply read the same loop value; the \
                 bound must reach the operands"
            );
            let result = verdict(vc);
            assert!(
                !matches!(result, VerificationResult::Failed { .. }),
                "loop_fresh {lane}: `|a| < 1000` bounds `a * a` well inside i64; a refutation \
                 rejects valid Rust: {result:?}"
            );
        }
    }
}
