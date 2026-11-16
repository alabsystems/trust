// Real-MIR end-to-end cover for the NESTED branch-merge grounding
// (`guards::nested_switch_branch_merge_definitions`), on the exact falsification
// fixtures `proved/cursor_clamp_assert.rs` and `mutant/cursor_clamp_assert.rs`.
//
//   pub fn cursor_clamp_assert(col: u32, width: u32) -> u32 {
//       let clamped = if col < width { col } else if width > 0 { width - 1 } else { 0 };
//       assert!(width == 0 || clamped < width);
//       clamped
//   }
//
// The `if / else if / else` lowers to a NESTED `SwitchInt` partition: arm `col`
// hangs off the outer switch, arms `width - 1` / `0` off an inner one. The
// single-switch merge recogniser requires every join arm to share ONE switch, so
// it declines, the merged local stays a free variable, the assert's
// path-feasibility formula is ungrounded, and the whole-function panic-freedom
// catch-all is never discharged (measured: `[ASSERT_REFUTE] grounded=false
// free=["_6.1", "_9#s7_0", "col", "width"]`).
//
// Both directions are load-bearing and are checked separately:
//
//  * SAFE fixture: the refutation formula must be GROUNDED, UNSAT, and
//    KERNEL-CERTIFIED. A model here would be a FALSE REFUTATION of correct Rust;
//    an uncertified UNSAT is reported `Unknown` and discharges nothing.
//  * MUTANT fixture (`else { width }`, so `clamped == width` is reachable): the
//    formula must stay SAT/refuted. That shape is a plain single-switch diamond,
//    so it exercises the "the nested lane did not disturb the existing lane"
//    direction as well.
//
// Three separable levers have to hold for this to pass, and each is pinned by an
// assertion below that was measured to FAIL with that lever alone disabled:
//
//   1. `guards::nested_switch_branch_merge_definitions` — grounds `clamped`.
//   2. the per-path split in `generate_full_assert_refutation_candidates_impl` — without
//      it the combined formula is `Unknown` ("(incomplete self-check-rejected)").
//   3. the boolean-discriminant inlining in `guards::nested_switch_route_guard` —
//      without it the parts still prove but 2 of 3 (and the catch-all residual)
//      fail kernel certification.
//
// The fixtures are the REAL MIR extracted with `-Ztrust-dump=mir:<dir>` from the
// two falsification fixtures, so this is not a hand-built approximation of the
// lowering.
use trust_types::{Formula, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn proved_fixture() -> VerifiableFunction {
    load(include_str!("fixtures/cursor_clamp_assert_proved_mir.json"))
}

fn mutant_fixture() -> VerifiableFunction {
    load(include_str!("fixtures/cursor_clamp_assert_mutant_mir.json"))
}

/// The refutation VCs the compiler's `refute_full_assert_obligations` would run.
fn refutation_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
    trust_vcgen::generate_full_assert_refutation_vcs_with_context(func, &context)
}

/// Every free variable of `f` that is neither an entry parameter nor PINNED by a
/// defining `Eq(Var(v), rhs)` conjunct of `f` itself — the refute lane's own
/// notion of "ungrounded" (`assert_refutation.rs`'s `is_free || resolved`),
/// re-derived here from the published formula rather than from lane internals.
fn unpinned_free_vars(func: &VerifiableFunction, f: &Formula) -> Vec<String> {
    let params: Vec<String> = func
        .body
        .locals
        .iter()
        .take(func.body.arg_count + 1)
        .skip(1)
        .enumerate()
        .map(|(i, decl)| decl.name.clone().unwrap_or_else(|| format!("_{}", i + 1)))
        .collect();
    let mut defined: Vec<String> = Vec::new();
    collect_definitions(f, &mut defined);
    let mut out: Vec<String> = f
        .free_variables()
        .into_iter()
        .filter(|v| {
            let base = v.split('#').next().unwrap_or(v);
            !params.iter().any(|p| p == base) && !defined.iter().any(|d| d == v)
        })
        .collect();
    out.sort();
    out.dedup();
    out
}

/// Subjects of top-level (`And`-nested) defining equalities `Var(v) == rhs`.
fn collect_definitions(f: &Formula, out: &mut Vec<String>) {
    match f {
        Formula::And(xs) => {
            for x in xs {
                collect_definitions(x, out);
            }
        }
        Formula::Eq(lhs, _) => {
            if let Formula::Var(name, _) = lhs.as_ref() {
                out.push(name.clone());
            }
        }
        _ => {}
    }
}

/// Does some conjunct define a variable as an `Ite` whose branches contain a
/// further `Ite` — the nested-partition shape this lane exists to emit?
fn formula_contains_nested_ite(f: &Formula) -> bool {
    fn has_ite(f: &Formula) -> bool {
        match f {
            Formula::Ite(..) => true,
            Formula::And(xs) | Formula::Or(xs) => xs.iter().any(has_ite),
            Formula::Not(x) => has_ite(x),
            Formula::Eq(a, b) => has_ite(a) || has_ite(b),
            _ => false,
        }
    }
    fn walk(f: &Formula) -> bool {
        match f {
            Formula::And(xs) | Formula::Or(xs) => xs.iter().any(walk),
            Formula::Eq(lhs, rhs) => {
                matches!(lhs.as_ref(), Formula::Var(..))
                    && matches!(rhs.as_ref(), Formula::Ite(c, t, e)
                        if has_ite(c) || has_ite(t) || has_ite(e))
            }
            _ => false,
        }
    }
    walk(f)
}

/// The SAFE fixture's assert must be discharged: one refutation VC, grounded on
/// the entry parameters, and decided UNSAT by the real in-process ay.
#[test]
fn nested_merge_grounds_and_proves_the_safe_cursor_clamp_assert() {
    let func = proved_fixture();
    let vcs = refutation_vcs(&func);
    // Three control-flow paths reach the assert's failure block (`col < width`,
    // `width == 0`, `width > 0`), so the per-path split emits three obligations.
    assert_eq!(vcs.len(), 3, "one obligation per path to the failure block; got {}", vcs.len());

    for vc in &vcs {
        let ungrounded = unpinned_free_vars(&func, &vc.formula);
        assert!(
            ungrounded.is_empty(),
            "the panic-path formula must be grounded on the entry parameters; still free: \
             {ungrounded:?}\nformula: {:?}",
            vc.formula
        );
        // The lane's actual artifact: the nested `Ite` for the merged local.
        assert!(
            formula_contains_nested_ite(&vc.formula),
            "the nested branch-merge fact `clamped == Ite(.., Ite(..))` must be present; \
             formula: {:?}",
            vc.formula
        );
    }

    let router = test_router::deterministic_test_router();
    for (index, vc) in vcs.iter().enumerate() {
        let results = router.verify_all(std::slice::from_ref(vc));
        let (_, result) = results.into_iter().next().expect("one verdict per VC");
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "path {index}: the SAFE fixture's panic path must be UNSAT (Proved = \
             unreachable); got {result:?}\nformula: {:?}",
            vc.formula
        );
    }

    // KERNEL CERTIFICATION — the direction that actually decides the fixture
    // under `-Ztrust-policy=certify`. An ay `Proved` with no kernel token is
    // reported `Unknown`, so proving the parts is not enough: every part, AND
    // the catch-all's residual violation (the `Or` of the proved parts, which is
    // what `refute_full_assert_obligations` writes onto the whole-function
    // panic-freedom row), must mint a `CleanCic` certificate.
    //
    // This is the assertion that pins the boolean-discriminant inlining in
    // `guards::nested_switch_route_guard`. MEASURED with that inlining disabled
    // and everything else unchanged: all three parts are still ay-`Proved`, but
    // parts 0 and 2 and the residual `Or` all certify=false — the fixture stays
    // undischarged. It is not a cosmetic spelling choice.
    for (index, vc) in vcs.iter().enumerate() {
        assert!(
            trust_certify::certify_vc(vc).is_some(),
            "path {index}: the proved panic path must kernel-certify; formula: {:?}",
            vc.formula
        );
    }
    let residual = Formula::Or(vcs.iter().map(|vc| vc.formula.clone()).collect());
    assert!(
        trust_certify::certify_violation(&residual).is_some(),
        "the whole-function panic-freedom catch-all's grounded residual must \
         kernel-certify; formula: {residual:?}"
    );
}

/// The MUTANT clamps to `width`, so `clamped == width` reaches the assert
/// failure. It must STILL be refuted — the nested lane must not have weakened
/// the refutation of a genuinely-broken program.
#[test]
fn mutant_cursor_clamp_assert_is_still_refuted() {
    let func = mutant_fixture();
    let vcs = refutation_vcs(&func);
    // Two paths reach the mutant's failure block (`col < width`, `col >= width`).
    assert_eq!(vcs.len(), 2, "one obligation per path to the failure block; got {}", vcs.len());

    let router = test_router::deterministic_test_router();
    let mut refuted = 0;
    for vc in &vcs {
        let ungrounded = unpinned_free_vars(&func, &vc.formula);
        assert!(
            ungrounded.is_empty(),
            "the mutant's panic-path formula must stay grounded; still free: \
             {ungrounded:?}\nformula: {:?}",
            vc.formula
        );
        let results = router.verify_all(std::slice::from_ref(vc));
        let (_, result) = results.into_iter().next().expect("one verdict per VC");
        assert!(
            matches!(result, VerificationResult::Failed { .. } | VerificationResult::Proved { .. }),
            "every mutant path must get a definite verdict; got {result:?}\nformula: {:?}",
            vc.formula
        );
        if matches!(result, VerificationResult::Failed { .. }) {
            refuted += 1;
        }
    }
    assert_eq!(
        refuted, 1,
        "exactly the `col >= width` path reaches the assert failure, so exactly one \
         obligation must be REFUTED (the build must still fail on the mutant)"
    );
}
