// Real-MIR cover for a loop guard that a later write in the loop body dropped
// (a false refutation of valid Rust).
//
//   pub fn nat_gcd(mut a: u64, mut b: u64) -> u64 {   // clean-kernel, verbatim
//       while b != 0 { let t = b; b = a % b; a = t; }
//       a
//   }
//
// rustc lowers the loop to
//
//   bb1: _6 = Ne(_3, 0);  switch _6 -> [0: bb2 (return), otherwise: bb3]
//   bb3: _7 = Eq(_3, 0);  assert(!_7, RemainderByZero) -> bb4
//   bb4: _8 = Rem(_4, _3); _5 = _3; _3 = _8; _4 = _5;  goto bb1
//
// Two RemainderByZero rows share the `a % b` span: `:0` from the assert and `:1`
// from the `Rem` statement at `bb4[0]`. `v2_live_path_defs` killed every entry
// fact of bb4 that mentions `_3`, because `bb4[2]` writes `_3`. That write comes
// AFTER the remainder reads `_3`. So row `:1` lost `_6 == (_3 != 0)` and
// `_7 == (_3 == 0)`, kept the path guards `_6` and `!_7` as FREE booleans, and ay
// refuted it with the infeasible model `_6 = true, _7 = false, _3 = 0`. The
// strict default lane then failed the compile of this safe function.
// `v2_live_path_defs_at_point` keeps the entry facts the statement row still
// reads and versions them at the row's own use point.
//
// Both directions are pinned, on the MIR `-Ztrust-dump=mir:<dir>` extracted
// from the stage1 compiler:
//
//  * SAFE (`nat_gcd`): every RemainderByZero row carries the loop guard's
//    definition and every one is PROVED.
//  * MUTANT (`gcd_mutant`, `while a != 0 { .. a % b .. }`): the guard no longer
//    protects the divisor. The function must still be refuted, with a model that
//    names a real execution (`a != 0`, `b == 0`).
use trust_types::{
    Counterexample, CounterexampleValue, Formula, VcKind, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn safe_fixture() -> VerifiableFunction {
    load(include_str!("fixtures/nat_gcd_loop_guarded_rem_mir.json"))
}

fn mutant_fixture() -> VerifiableFunction {
    load(include_str!("fixtures/nat_gcd_unguarded_rem_mutant_mir.json"))
}

fn rem_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::RemainderByZero))
        .collect()
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

/// Subjects of every defining equality `Var(v) == rhs` anywhere in the
/// `And`-spine of `f`.
fn defined_names(f: &Formula, out: &mut Vec<String>) {
    match f {
        Formula::And(xs) => xs.iter().for_each(|x| defined_names(x, out)),
        Formula::Eq(lhs, _) => {
            if let Formula::Var(name, _) = lhs.as_ref() {
                out.push(name.clone());
            }
        }
        _ => {}
    }
}

/// Boolean free variables of `f` that no conjunct defines. A path guard is a
/// boolean MIR local, and a guard with no definition is exactly the defect: the
/// solver can pick its value independently of the value it tests.
fn undefined_bool_vars(f: &Formula) -> Vec<String> {
    let mut defined = Vec::new();
    defined_names(f, &mut defined);
    let mut bools = Vec::new();
    collect_bool_vars(f, &mut bools);
    bools.retain(|v| !defined.contains(v));
    bools.sort();
    bools.dedup();
    bools
}

fn collect_bool_vars(f: &Formula, out: &mut Vec<String>) {
    if let Formula::Var(name, trust_types::Sort::Bool) = f {
        out.push(name.clone());
    }
    for child in f.children() {
        collect_bool_vars(child, out);
    }
}

/// The loop guard `_6 == Not(_3#v == 0)` is present with `_3` at the version the
/// remainder reads (the loop-header join token, not the post-write `bb4[2]` one).
fn has_guard_definition(f: &Formula, divisor_prefix: &str) -> bool {
    fn walk(f: &Formula, divisor_prefix: &str) -> bool {
        match f {
            Formula::And(xs) => xs.iter().any(|x| walk(x, divisor_prefix)),
            Formula::Eq(lhs, rhs) => {
                matches!(lhs.as_ref(), Formula::Var(n, _) if n == "_6")
                    && matches!(rhs.as_ref(), Formula::Not(inner)
                        if matches!(inner.as_ref(), Formula::Eq(a, _)
                            if matches!(a.as_ref(), Formula::Var(v, _)
                                if v.starts_with(divisor_prefix) && !v.ends_with("#s4_2"))))
            }
            _ => false,
        }
    }
    walk(f, divisor_prefix)
}

fn model_int(cex: &Counterexample, base: &str) -> Option<i128> {
    cex.assignments.iter().find_map(|(name, value)| {
        let root = name.split('#').next().unwrap_or(name);
        match value {
            CounterexampleValue::Int(v) if root == base => Some(*v),
            CounterexampleValue::Uint(v) if root == base => i128::try_from(*v).ok(),
            _ => None,
        }
    })
}

#[test]
fn loop_guarded_remainder_keeps_its_guard_and_is_proved() {
    let func = safe_fixture();
    let rows = rem_rows(&func);
    assert_eq!(rows.len(), 2, "the assert row and the Rem statement row; got {rows:#?}");

    for (index, vc) in rows.iter().enumerate() {
        let free = undefined_bool_vars(&vc.formula);
        assert!(
            free.is_empty(),
            "row {index}: path-guard booleans with no definition {free:?} — the loop \
             guard was dropped\nformula: {:?}",
            vc.formula
        );
        assert!(
            has_guard_definition(&vc.formula, "_3#"),
            "row {index}: the loop guard `_6 == (_3 != 0)` must be conjoined at the \
             divisor version the remainder reads\nformula: {:?}",
            vc.formula
        );
        // PROVED, not merely "not refuted": with the guard restored both rows
        // discharge (the strict stage1 compile of the same function proves and
        // kernel-certifies them). Accepting Unknown here would let a later
        // change silently downgrade this row and still pass.
        let result = verdict(vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "row {index}: `a % b` under `while b != 0` is safe and must be PROVED; a \
             refutation is a false refutation of valid Rust and Unknown is a lost \
             proof. got {result:?}\nformula: {:?}",
            vc.formula
        );
    }
}

#[test]
fn unguarded_remainder_mutant_is_still_refuted_with_a_real_model() {
    let func = mutant_fixture();
    let rows = rem_rows(&func);
    assert_eq!(rows.len(), 2, "the assert row and the Rem statement row; got {rows:#?}");

    let mut refuted = 0;
    for vc in &rows {
        // Restoring the guard must not leave the mutant's guard undefined either.
        let free = undefined_bool_vars(&vc.formula);
        assert!(free.is_empty(), "undefined path-guard booleans {free:?}: {:?}", vc.formula);
        match verdict(vc) {
            VerificationResult::Failed { counterexample, .. } => {
                refuted += 1;
                let cex = counterexample.expect("a refutation must carry its model");
                // `_4` is `a`, `_3` is `b` at the loop header. The only executions
                // that panic enter the loop (`a != 0`) with `b == 0`.
                let a = model_int(&cex, "_4").expect("the model assigns the loop's `a`");
                let b = model_int(&cex, "_3").expect("the model assigns the divisor `b`");
                assert!(
                    a != 0 && b == 0,
                    "the counterexample must be a real panicking state (a != 0, b == 0); \
                     got {cex:?}"
                );
            }
            VerificationResult::Proved { .. } => {}
            other => panic!("every mutant row must get a definite verdict; got {other:?}"),
        }
    }
    assert!(refuted >= 1, "`while a != 0 {{ .. a % b .. }}` divides by zero at a=1, b=0");
}
