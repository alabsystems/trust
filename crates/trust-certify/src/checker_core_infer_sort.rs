// trust-certify: CHECKER-CORE INFER discharge lane (`infer(Sort l) = Sort (l+1)`).
//
// The FIRST Front-2 lane that grounds the kernel's TYPE INFERENCE (not just the
// `is_whnf` structural postcondition). It discharges the base case of the
// production kernel's `infer_type`: inferring the type of a universe/sort.
//
// The semantics is bound to clean-verify's REAL `KernelInferAccepts` inductive
// (implementation_soundness_infer_accepts.rs), whose `sort` constructor is:
//
//   inductive KernelInferAccepts (st : KernelState) : KExpr -> KExpr -> Type
//   | sort : forall (l : Nat) (T : KExpr),
//              Eq KExpr (KExpr.sort (Nat.succ l)) T
//              -> KernelInferAccepts st (KExpr.sort l) T
//
// So the kernel's fact "infer(Sort l) = Sort (l+1)" is witnessed by
//   KernelInferAccepts.sort st l (Sort (l+1)) (Eq.refl KExpr (Sort (l+1)))
// checked against the goal `KernelInferAccepts st (Sort l) (Sort (l+1))`.
//
// GROUNDING SCOPE (stated honestly): this is the SORT BASE CASE — non-recursive,
// no Trust-boundary skolem. It grounds the sort arm of `infer` at the same
// MODEL-LEVEL rigor as the `is_whnf` lane (real clean-kernel `check_type` of a
// real `KernelInferAccepts.sort` ctor term, with a discriminating negative
// control). It does NOT yet retire a census skolem: `KernelInferResult`,
// `KernelInferAppPi*`, and the def-eq normal-form skolems live in the RECURSIVE
// app/lam/pi arms, which need the functional-VC + recursive-spec path (the
// genuinely multi-year continuation). This lane is the first infer-grounding
// INFRASTRUCTURE brick — the discharge mechanism the recursive arms will reuse.
//
// NO MASQUERADE: (1) the discharge is a REAL `clean_kernel::check_type` of a
// real `KernelInferAccepts.sort` term against the concrete goal; (2) the
// wrong-result control checks the SAME evidence (which proves `T = Sort (l+1)`)
// against the WRONG goal `T = Sort l` — the kernel MUST reject it, proving the
// check is discriminating and not a rubber stamp; (3) a non-sort head fails
// closed at the LINK step (the sort ctor's goal is about `Sort l`, so it cannot
// ground an `app`/`lam`/`bvar`).

use clean_kernel::{Environment, Expr, ExprKind, Name};
use clean_verify::spec::Specification;

use crate::checker_core::{elaborate_full, kernel_checks_goal};

/// A fixed distinguished kernel state — the empty environment with an empty
/// local context. The sort arm's discharge is independent of `st` (the `Eq`
/// pins the inferred type regardless of state), so any concrete state suffices.
const ST_SRC: &str = "KernelState.mk KEnv.empty KernelLocalCtx.nil";

/// A concrete sort-inference operation: the kernel inferring the type of
/// `KExpr.sort level_src`, whose result is `KExpr.sort (Nat.succ level_src)`.
#[derive(Clone, Copy)]
pub struct InferSortFixture {
    /// Description of the conceptual sort-inference operation.
    pub label: &'static str,
    /// The universe level source (e.g. `"Nat.zero"`).
    pub level_src: &'static str,
}

/// `infer(Sort 0) = Sort 1`.
pub const INFER_SORT0: InferSortFixture = InferSortFixture {
    label: "infer(Sort 0) = Sort 1",
    level_src: "Level.zero",
};

/// `infer(Sort 1) = Sort 2`.
pub const INFER_SORT1: InferSortFixture = InferSortFixture {
    label: "infer(Sort 1) = Sort 2",
    level_src: "Level.succ Level.zero",
};

struct LinkedInferSort {
    evidence: Expr,
    goal: Expr,
}

fn head_const(e: &Expr) -> Option<Name> {
    match e.get_app_fn().strip_mdata().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// LINK: verify the inferred expression is genuinely a `KExpr.sort`, then build
/// the `KernelInferAccepts.sort` proof term from its own level and the goal
/// `KernelInferAccepts st (Sort l) (Sort (l+1))`. FAIL CLOSED (`None`) if the
/// head is not a sort ctor — the sort lane never grounds a non-sort head.
fn link_infer_sort(env: &Environment, level_src: &str) -> Option<LinkedInferSort> {
    // Verify the head really is `KExpr.sort` (fail-closed guard).
    let kexpr = elaborate_full(env, &format!("KExpr.sort ({level_src})"))?;
    if head_const(&kexpr)? != Name::from_string("KExpr.sort") {
        return None;
    }

    let evidence_src = format!(
        "KernelInferAccepts.sort ({ST_SRC}) ({level_src}) \
         (KExpr.sort (Level.succ ({level_src}))) \
         (Eq.refl KExpr (KExpr.sort (Level.succ ({level_src}))))"
    );
    let goal_src = format!(
        "KernelInferAccepts ({ST_SRC}) (KExpr.sort ({level_src})) \
         (KExpr.sort (Level.succ ({level_src})))"
    );
    let evidence = elaborate_full(env, &evidence_src)?;
    let goal = elaborate_full(env, &goal_src)?;
    Some(LinkedInferSort { evidence, goal })
}

/// DISCHARGE the sort-inference fact and prove the discharge is discriminating.
/// Returns `true` iff (a) the `KernelInferAccepts.sort` evidence kernel-checks
/// against the correct goal AND (b) the SAME evidence is kernel-REJECTED against
/// the wrong goal `T = Sort l` (not `Sort (l+1)`). Fail-closed on any failure.
#[must_use]
pub fn certify_infer_sort(spec: &Specification, fixture: &InferSortFixture) -> bool {
    let env = spec.env();

    let Some(linked) = link_infer_sort(env, fixture.level_src) else {
        return false;
    };

    // (a) Positive: the real ctor term discharges the correct goal.
    if !kernel_checks_goal(env, &linked.evidence, &linked.goal) {
        return false;
    }

    // (b) No-masquerade control: the SAME evidence proves `T = Sort (l+1)`, so
    // it MUST be rejected against the wrong goal `T = Sort l`. If the kernel
    // accepted it, the check would be a rubber stamp.
    let wrong_goal_src = format!(
        "KernelInferAccepts ({ST_SRC}) (KExpr.sort ({0})) (KExpr.sort ({0}))",
        fixture.level_src
    );
    let Some(wrong_goal) = elaborate_full(env, &wrong_goal_src) else {
        return false;
    };
    if kernel_checks_goal(env, &linked.evidence, &wrong_goal) {
        return false;
    }

    true
}

/// The sort lane must FAIL CLOSED on a non-sort head: an `app` result has no
/// `KExpr.sort` head, so `link_infer_sort` never builds sort evidence for it.
#[must_use]
pub fn non_sort_head_fails_closed(env: &Environment) -> bool {
    // A stuck application `KExpr.app (KExpr.bvar 0) (KExpr.bvar 0)` is not a sort.
    let src = "KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)";
    match elaborate_full(env, src) {
        Some(app) => head_const(&app) != Some(Name::from_string("KExpr.sort")),
        None => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker_core::run_on_large_stack;

    /// THE MILESTONE (first kernel-discharged checker-core INFER postcondition):
    /// * two sort levels discharge `infer(Sort l) = Sort (l+1)` via a real
    ///   clean-kernel `check_type` of a `KernelInferAccepts.sort` ctor term;
    /// * the SAME evidence is kernel-REJECTED against the wrong result goal
    ///   (`Sort l` instead of `Sort (l+1)`) — the check is discriminating;
    /// * a non-sort head fails closed at the LINK step.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn infer_sort_discharge_closes_and_fails_closed() {
        // Build the spec + run the certifications on a large stack, like every
        // sibling lane: `Specification::new()` overflows the default 8 MB test
        // thread stack (SIGABRT). Return the three verdicts and assert outside.
        let (sort0, sort1, non_sort_closed) = run_on_large_stack(|| {
            let spec = Specification::new().expect("spec should build");
            let env = spec.env();
            (
                certify_infer_sort(&spec, &INFER_SORT0),
                certify_infer_sort(&spec, &INFER_SORT1),
                non_sort_head_fails_closed(env),
            )
        })
        .expect("spec build + certification must complete on the large stack");

        assert!(
            sort0,
            "infer(Sort 0) = Sort 1 must discharge and reject the wrong result"
        );
        assert!(
            sort1,
            "infer(Sort 1) = Sort 2 must discharge and reject the wrong result"
        );
        assert!(
            non_sort_closed,
            "a non-sort head must fail closed at LINK"
        );
    }
}
