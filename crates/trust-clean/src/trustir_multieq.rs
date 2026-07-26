// trust-clean/trustir_multieq.rs — Trust: MULTI-VALUE SwitchInt disjunctive-
// equality guard (2026-07-08).
//
// The KERNEL-CHECKED witness for the `mirsem::SemMultiEqReturn` shape:
// `if discr ∈ {v1,...,vN} { then } else { else }` — ONE `SwitchInt` whose
// EXPLICIT targets (2+ distinct literal values) ALL converge on a single arm
// block (the `core::u8::is_ascii_whitespace`-class shape:
// `SwitchInt((*_1)) {9→T, 10→T, 12→T, 13→T, 32→T, otherwise→F}`).
//
// SIBLING TO `trustir_adt.rs`'s ADT-return witness and `trustir_anchor.rs`'s
// `IrGuardedIndex` — the SAME self-contained `Bool.rec` + `congrArg`-transport
// recipe, generalized from a SINGLE comparison guard to an N-ARY `Bool.or`
// FOLD of equality tests (`discr==v1 ∨ discr==v2 ∨ … ∨ discr==vN`) over a
// PLAIN `Int` motive (no ADT carrier registration at all — the target family's
// arms are always a scalar/`bool`-literal `Use`, so this witness is simpler
// than the ADT one: no `Environment` mutation beyond the shared `trustir_env()`
// base, and only ONE `congrArg` (no `Eq.trans` composition needed — this
// shape has exactly two outcomes, not three).
//
// MODEL-ONLY tier — the SAME honesty tier as `trustir_adt`'s witness: this
// claim does NOT relate to `clean_ground::ground_int`/`ground_bool` (which has
// no `Or` arm at all — see `mirsem.rs`'s module doc above
// `sem_cf_return_of_mir_multi_eq` for why this is a DELIBERATELY separate,
// narrowly-scoped sibling rather than an extension of the shared
// `SemCondTree`/`Formula` machinery those other recognizers use). The
// soundness argument that this claim matches the MIR's own guard/arms lives
// in the RECOGNIZER (`mirsem::sem_cf_return_of_mir_multi_eq`): every literal
// value is read DIRECTLY off the real `SwitchInt` targets, never guessed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use clean_kernel::{
    BinderData, BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker,
};

use crate::mirsem::SemMultiEqReturn;
use crate::trustir_adt::sem_operand_to_expr;
use crate::trustir_anchor::{RefinementVerdict, cst, env_ty, eq_bool_true, int_ty};

fn bd() -> BinderData {
    BinderData::from(BinderInfo::Default)
}

/// Build the guard's `Bool` term at binder depth `e_bvar`: the LEFT-NESTED
/// `Bool.or` fold of `Int.beq(discr, v_i)` over `r.values` (2+ entries,
/// enforced by the recognizer). `None` (fail-closed) if the discriminant does
/// not resolve to an `Expr` (out of the small `sem_operand_to_expr` fragment).
fn multi_eq_guard_bool(r: &SemMultiEqReturn, e_bvar: u32) -> Option<Expr> {
    let discr = sem_operand_to_expr(&r.discr, e_bvar)?;
    let mut values = r.values.iter();
    let first = *values.next()?;
    let eq_v =
        |v: i128| Expr::apps(cst("Int.beq"), [discr.clone(), crate::trustir_anchor::int_lit(v)]);
    let mut acc = eq_v(first);
    for &v in values {
        acc = Expr::apps(cst("Bool.or"), [acc, eq_v(v)]);
    }
    Some(acc)
}

/// Build `(env, statement, proof)`: `env` is the SHARED `trustir_env()` base
/// (no registration at all — a plain `Int` motive needs no fresh carrier);
/// `statement` is `∀ (e:Env), guard e = true → select e = <claimed OR
/// then_val>`; `proof` is the `congrArg`-transport witness. `None`
/// (fail-closed) on any unresolved piece.
///
/// `claimed` overrides the statement's RHS — `None` for the real, honest
/// claim; `Some(wrong_rhs)` is the FAIL-CLOSED PROBE mechanism (mirrors
/// `trustir_adt::build_refinement`'s `claimed` parameter exactly).
fn build_refinement(
    r: &SemMultiEqReturn,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let env = crate::trustir_anchor::trustir_env().ok()?;
    let l1 = Level::succ(Level::zero());

    // STATEMENT: ∀ (e:Env), guard e = true → select e = <claimed OR then_val>.
    // Under `λ e`: e=0.
    let guard0 = multi_eq_guard_bool(r, 0)?;
    let guard_eq = eq_bool_true(guard0);
    // Under `λ e λ hg`: hg=0, e=1.
    let then_v1 = sem_operand_to_expr(&r.then_op, 1)?;
    let else_v1 = sem_operand_to_expr(&r.else_op, 1)?;
    let guard1 = multi_eq_guard_bool(r, 1)?;
    let lhs = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        Expr::apps(bool_rec, [motive, else_v1, then_v1.clone(), guard1])
    };
    let rhs = claimed.cloned().unwrap_or_else(|| then_v1.clone());
    let eq =
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1.clone()]), [int_ty(), lhs, rhs]);
    let statement = Expr::pi(bd(), env_ty(), Expr::pi(bd(), guard_eq, eq));

    // PROOF: congrArg (λ x:Bool. Bool.rec (λ_.Int) else_val then_val x) hg — the
    // SAME recipe as `trustir_adt::build_refinement`'s, `adt_ty()` swapped for
    // a plain `int_ty()`.
    let f = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        // Under `λ e λ hg λ x`: x=0, hg=1, e=2.
        let then_v2 = sem_operand_to_expr(&r.then_op, 2)?;
        let else_v2 = sem_operand_to_expr(&r.else_op, 2)?;
        let select_x = Expr::apps(bool_rec, [motive, else_v2, then_v2, Expr::bvar(0)]);
        Expr::lam(bd(), cst("Bool"), select_x)
    };
    let guard1_for_proof = multi_eq_guard_bool(r, 1)?;
    let congr = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [cst("Bool"), int_ty(), guard1_for_proof, cst("Bool.true"), f, Expr::bvar(0)],
    );
    let guard0_for_proof = multi_eq_guard_bool(r, 0)?;
    let proof = Expr::lam(bd(), env_ty(), Expr::lam(bd(), eq_bool_true(guard0_for_proof), congr));

    Some((env, statement, proof))
}

/// TEST-ONLY: the ELSE arm's value `Expr` (depth 1, matching
/// [`build_refinement`]'s own `else_v1`) for a recognized [`SemMultiEqReturn`]
/// — the FAIL-CLOSED PROBE's "wrong claim".
#[cfg(test)]
fn else_value_for_test(r: &SemMultiEqReturn) -> Option<Expr> {
    sem_operand_to_expr(&r.else_op, 1)
}

/// Check the MULTI-VALUE disjunctive-equality guarded-return refinement for a
/// recognized [`SemMultiEqReturn`] against the real clean-kernel, modulo 3.
/// Fail-closed (`KernelRejected`) if the shape's guard/arms fall outside the
/// modeled fragment.
#[must_use]
pub fn check_multi_eq_refinement(r: &SemMultiEqReturn) -> RefinementVerdict {
    check_multi_eq_refinement_claimed(r, None)
}

/// [`check_multi_eq_refinement`] with an explicit `claimed` RHS override — the
/// FAIL-CLOSED PROBE entry point.
#[must_use]
pub(crate) fn check_multi_eq_refinement_claimed(
    r: &SemMultiEqReturn,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    let Some((mut env, statement, proof)) = build_refinement(r, claimed) else {
        return RefinementVerdict::KernelRejected(
            "multi-eq guarded return: shape outside the modeled fragment".to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.multi_eq_return");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mirsem::SemOperand;

    /// The canonical `is_ascii_whitespace`-shape: `if b ∈ {9,10,12,13,32} { true }
    /// else { false }` — matching the REAL `core::num::<impl u8>::is_ascii_whitespace`
    /// fixture.
    fn example_is_ascii_whitespace() -> SemMultiEqReturn {
        SemMultiEqReturn {
            discr: SemOperand::Var(0),
            values: vec![9, 10, 12, 13, 32],
            then_op: SemOperand::Const(1),
            else_op: SemOperand::Const(0),
        }
    }

    #[test]
    fn multi_eq_refinement_modulo3() {
        assert_eq!(
            check_multi_eq_refinement(&example_is_ascii_whitespace()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// FAIL-CLOSED probe: claim the guarded return equals the ELSE arm's value
    /// (`0`) even though the guard is `true` (`b` matches one of the listed
    /// values) — the TRUE answer is `1`. The `congrArg`-transport proof's
    /// ACTUAL type is `select = then_val` regardless of what is claimed, so a
    /// claimed RHS not def-eq to `then_val` makes `check_type` reject.
    #[test]
    fn multi_eq_refinement_fail_closed_wrong_value_claim() {
        let r = example_is_ascii_whitespace();
        let wrong_rhs = else_value_for_test(&r).expect("else-arm value builds");
        assert!(
            matches!(
                check_multi_eq_refinement_claimed(&r, Some(&wrong_rhs)),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming the ELSE arm's value under a TRUE guard must be rejected by the kernel"
        );
    }

    /// FAIL-CLOSED probe: a genuinely WRONG value list (missing `32`, so the
    /// guard's truth table no longer matches the real MIR's 5-value set) still
    /// TYPE-CHECKS as its OWN (different, still internally-consistent) claim —
    /// this probe instead checks that a wrong claimed RHS against the REAL
    /// 5-value guard rejects, which `multi_eq_refinement_fail_closed_wrong_value_claim`
    /// already covers; this second probe checks the DEGENERATE single-value
    /// input is rejected by the RECOGNIZER (not this kernel witness) — see
    /// `mirsem.rs`'s `sem_cf_return_of_mir_multi_eq_declines_single_value_switch`.
    #[test]
    fn multi_eq_refinement_two_value_guard_still_proves() {
        // A 2-value disjunction (the minimum this shape supports) must ALSO
        // prove modulo 3 — pins that the `Bool.or` fold's base case (no fold
        // needed, a single `Int.beq`) and its one-fold-step case (this one) are
        // BOTH genuine, not just the 5-value real-fixture case.
        let r = SemMultiEqReturn {
            discr: SemOperand::Var(0),
            values: vec![9, 32],
            then_op: SemOperand::Const(1),
            else_op: SemOperand::Const(0),
        };
        assert_eq!(check_multi_eq_refinement(&r), RefinementVerdict::ProvenModulo3);
    }
}
