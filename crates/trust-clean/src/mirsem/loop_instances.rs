// Per-instance preservation proofs for the recognised invariant shapes --
// counter, countdown, stride, accumulator and conditional-update. Each proves
// its invariant survives one step of the specific loop body, which is what the
// generic invariant rule consumes.

use super::*;

/// The CONCRETE preservation PROOF for the untouched-local invariant `I := λ e.
/// e[r] = c` over body `body` (which does NOT assign `r`):
/// `λ (e : Env)(hI : I e)(_hg : eval_cond e cond = true). hI`.
///
/// The codomain `I (exec e body)` ι-reduces (through `exec`/`set`) to `I e` because
/// `exec e body` leaves index `r` untouched (`set … r ι-reduces to `e r` for each
/// body assignment, whose index `iₖ ≠ r` ⇒ `Nat.beq iₖ r ≡ false`), so the proof is
/// the hypothesis `hI` itself. `claimed_local` builds the proof against the SAME
/// `λ e hI _. hI` shape but for a possibly-WRONG local; the kernel rejects when that
/// local IS assigned (the def-eq reduction no longer collapses to `I e`).
pub(super) fn loop_instance_preservation_proof(lf: &SemLoopFunction, claimed_local: Option<u64>) -> Expr {
    // SYNTHESIZED invariant: a GENUINE arithmetic preservation proof (NOT `hI`).
    match &lf.synth_inv {
        Some(SynthInvariant::CounterGeConst { i_idx, c }) => {
            return counter_ge_const_preservation_proof(lf, *i_idx, *c);
        }
        Some(SynthInvariant::CounterLeBound { i_idx, bound_idx }) => {
            return counter_le_bound_preservation_proof(lf, *i_idx, *bound_idx);
        }
        Some(SynthInvariant::CounterInRange { i_idx, c, bound_idx }) => {
            return counter_in_range_preservation_proof(lf, *i_idx, *c, *bound_idx);
        }
        Some(SynthInvariant::CounterLeBoundSucc { i_idx, bound_idx }) => {
            return counter_le_bound_succ_preservation_proof(lf, *i_idx, *bound_idx);
        }
        Some(SynthInvariant::CounterInRangeSucc { i_idx, c, bound_idx }) => {
            return counter_in_range_succ_preservation_proof(lf, *i_idx, *c, *bound_idx);
        }
        Some(SynthInvariant::CountdownGeConst { i_idx, c }) => {
            return countdown_ge_const_preservation_proof(lf, *i_idx, *c);
        }
        Some(SynthInvariant::StrideGeConst { i_idx, c, k }) => {
            return stride_ge_const_preservation_proof(lf, *i_idx, *c, *k);
        }
        Some(SynthInvariant::CondIncrGeConst { count_idx, c, .. }) => {
            return cond_incr_ge_const_preservation_proof(lf, *count_idx, *c);
        }
        Some(SynthInvariant::AccumGeConst { s_idx, c, .. }) => {
            // The accumulator lower bound `c ≤ s` is preserved by EXACTLY the same inductive
            // step as the counter lower bound (`Int.le_trans` + `Int.le_self_add_one`), built
            // at the ACCUMULATOR index `s_idx`. The multi-statement body's net effect at
            // `s_idx` is `s + 1` (the `i := i+1` statement leaves `s_idx` untouched —
            // `Nat.beq i_idx s_idx ≡ false` — so `(exec e [s:=s+1; i:=i+1]) s_idx ≡ (e s_idx)+1`),
            // so the codomain reduces to `Int.le c ((e s_idx)+1)` and the same proof retypes.
            return counter_ge_const_preservation_proof(lf, *s_idx, *c);
        }
        Some(SynthInvariant::AccumEqCounter { s_idx, i_idx, n_idx }) => {
            // The RELATIONAL conjoined invariant `s == i ∧ i ≤ n`: `And.intro` of the
            // congruence-based equality preservation (`s == i → s+1 == i+1`) and the
            // guard-aware upper-bound preservation (`i < n → i+1 ≤ n`).
            return accum_eq_counter_preservation_proof(lf, *s_idx, *i_idx, *n_idx);
        }
        Some(SynthInvariant::AccumEqCounterSet { accum_idxs, i_idx, n_idx, .. }) => {
            // The GENERAL RELATIONAL invariant `(⋀ₖ aₖ == i) ∧ (i ≤ n)`: a NESTED right-folded
            // `And.intro` of one congruence step per accumulator + the guard upper bound.
            // (Preservation is over ALL accumulators uniformly — independent of `ret_idx`.)
            return accum_eq_counter_set_preservation_proof(lf, accum_idxs, *i_idx, *n_idx);
        }
        Some(SynthInvariant::CondUpdateGeConst { m_idx, c, i_idx, .. }) => {
            // The CONDITIONALLY-UPDATED accumulator `c ≤ m ∧ 0 ≤ i`: `And.intro` of a `Bool.rec`
            // case-split over the update condition (LEFT, `c ≤ m`) and the counter lower bound
            // (RIGHT, `0 ≤ i → 0 ≤ i+1`).
            return cond_update_ge_const_preservation_proof(lf, *m_idx, *c, *i_idx);
        }
        None => {}
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(claimed_local);
    let cond_expr = lf.cond.to_cond_expr();
    // λ (e : Env). λ (hI : I e). λ (_hg : eval_cond e cond = true). hI
    //   inside `λ e`: e = 0; lift I by 1 for `I e`.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the guard's eval_cond is at this depth.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: hI = 1 ⇒ return hI.
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, Expr::bvar(1))))
}

/// The GENUINE inductive preservation PROOF for the SYNTHESIZED interval lower-bound
/// invariant `I := λ e. Int.le (int_lit c) (e i_idx)` (`c ≤ i`) over the counter body
/// `[i := i + 1]`:
/// `λ (e : Env)(hI : I e)(_hg : eval_cond e cond = true).
///    Int.le_trans c (e i) ((e i)+1) hI (Int.le_self_add_one (e i))`.
///
/// The codomain `I (exec e body)` ι-reduces (through `exec`/`set`) to
/// `Int.le c ((e i_idx) + 1)` — `(exec e [i:=i+1]) i_idx ≡ (e i_idx)+1`. From the
/// loop-carried hypothesis `hI : Int.le c (e i)` and the constructive prelude bridge
/// `Int.le_self_add_one (e i) : Int.le (e i) ((e i) + 1)`, `Int.le_trans` chains them
/// to `Int.le c ((e i)+1)` — EXACTLY the reduced codomain. This is a real inductive
/// arithmetic step that genuinely USES the hypothesis `hI` (the lower bound is
/// carried, not re-derived). The `_hg` guard is genuinely UNNEEDED (the lower bound
/// holds regardless of the guard), but the binder is kept so the proof has the EXACT
/// preservation type `loopInvariantRule` expects. The `+1` in both `Int.le_self_add_one`
/// (`Int.add a (Int.ofNat (Nat.succ Nat.zero))`) and the body (`eval_rvalue` →
/// `Int.add (e i) (int_lit 1)`) reduce to the SAME normal form, so the application
/// type-checks.
///
/// FAIL-CLOSED: a WRONG synthesized constant (e.g. `c = 1`, the false claim `1 ≤ i`
/// at `i = 0`) is preserved as a STATEMENT here (`1 ≤ i → 1 ≤ i+1` is valid), but is
/// FALSE at the loop ENTRY `i = 0` — so it does not connect to the postcondition;
/// and a constant `c` that does not match the inferred lower bound makes the
/// per-function instance's invariant differ from what the corollary needs. The
/// load-bearing fail-closed property is enforced two ways: (a) the strengthen
/// inferrer only proposes the ACTUAL inferred bound, and (b) the
/// `wrong_synth_invariant_*` test confirms a non-preserved synthesized invariant
/// (one whose `Int.le_self_add_one` chain does not retype) is KernelRejected.
pub(super) fn counter_ge_const_preservation_proof(lf: &SemLoopFunction, i_idx: u64, c: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the guard `eval_cond e cond = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let c_lit = int_lit(c);
    // `i + 1` exactly as `Int.le_self_add_one` spells it (canonical `+1`).
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    // Int.le_self_add_one (e i) : Int.le (e i) ((e i) + 1)
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_i.clone());
    // Int.le_trans c (e i) ((e i)+1) hI (Int.le_self_add_one (e i)) : Int.le c ((e i)+1)
    let proof =
        Expr::apps(cst("Int.le_trans"), [c_lit, e_i, i_plus_one, Expr::bvar(1), self_le_succ]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The GUARD-AWARE preservation PROOF for the SYNTHESIZED interval UPPER-bound invariant
/// `I := λ e. Int.le (e i_idx) (e bound_idx)` (`i ≤ n`) over the counter body
/// `[i := i + 1]`:
/// `λ (e : Env)(_hI : I e)(hg : eval_cond e cond = true).
///    of_decide_eq_true (Int.lt (e i) (e n)) (Int.decLt (e i)(e n)) hg`.
///
/// The codomain `I (exec e body)` ι-reduces (through `exec`/`set`) to `Int.le ((e i_idx)
/// + 1) (e bound_idx)` — `(exec e [i:=i+1]) i_idx ≡ (e i_idx)+1` and `(exec e [i:=i+1])
/// bound_idx ≡ e bound_idx` (the body never assigns the bound). The guard `hg :
/// eval_cond e (i<n) = true` is def-eq `decide (Int.lt (e i)(e n)) (Int.decLt …) = true`,
/// so `of_decide_eq_true … hg : Int.lt (e i_idx) (e bound_idx)`. And `Int.lt a b` UNFOLDS
/// (it is the reducible kernel definition `Int.lt a b := Int.le (Int.add a (ofNat 1)) b`)
/// to EXACTLY `Int.le ((e i_idx)+1) (e bound_idx)` — the reduced codomain. This is the
/// crux: the upper bound is re-established SOLELY from the guard (`i < n ⇒ i+1 ≤ n`), so
/// the loop-carried hypothesis `_hI : i ≤ n` is genuinely UNNEEDED here (kept only so the
/// proof has the EXACT preservation type `loopInvariantRule` expects). This is the
/// COMPLEMENT of [`counter_ge_const_preservation_proof`], which uses the hypothesis but
/// ignores the guard.
///
/// FAIL-CLOSED: a WRONG bound index (claiming `i ≤ m` for an `m` the guard does not
/// mention) makes `Int.lt (e i)(e bound)` (extracted from the guard `i<n`) NOT def-eq to
/// the codomain `Int.le (i+1)(e m)` ⇒ the application is ill-typed ⇒ KernelRejected. A
/// non-`Lt` guard makes `eval_cond` not reduce to a `decide (Int.lt …)`, so
/// `of_decide_eq_true` does not apply ⇒ KernelRejected. See the `wrong_synth_upper_*`
/// tests.
pub(super) fn counter_le_bound_preservation_proof(lf: &SemLoopFunction, i_idx: u64, bound_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ _hI`: _hI = 0, e = 1; the guard `eval_cond e cond = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ _hI λ hg`: hg = 0, _hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let e_b = Expr::app(Expr::bvar(2), Expr::nat_lit(bound_idx)); // e bound_idx
    // p := Int.lt (e i) (e n) ; inst := Int.decLt (e i) (e n).
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_b.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i, e_b]);
    // of_decide_eq_true p inst hg : p ≡ Int.lt (e i)(e n) ≡ Int.le ((e i)+1)(e n)
    //   — the reduced codomain `I (exec e [i:=i+1])`.
    let proof = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The preservation PROOF for the CONJOINED range invariant `I := λ e. And (c ≤ i)
/// (i ≤ n)` over the counter body `[i := i + 1]`:
/// `λ (e : Env)(hI : I e)(hg : eval_cond e cond = true).
///    And.intro <c ≤ i+1> <i+1 ≤ n>`.
///
/// The codomain `I (exec e body)` ι-reduces to `And (Int.le c ((e i)+1)) (Int.le ((e i)+1)
/// (e n))`. `And.intro` packages (a) the LOWER conjunct, proved EXACTLY as
/// [`counter_ge_const_preservation_proof`] (`Int.le_trans c (e i) ((e i)+1)
/// (And.left hI) (Int.le_self_add_one (e i))`, which USES `hI`'s lower conjunct), and
/// (b) the UPPER conjunct, proved EXACTLY as [`counter_le_bound_preservation_proof`]
/// (`of_decide_eq_true … hg`, the guard def-eq `Int.lt i n ≡ Int.le (i+1) n`). So the
/// conjunction's preservation USES the hypothesis (lower half) AND the guard (upper
/// half) — neither is vacuous. Fail-closed the same two ways as its conjuncts.
pub(super) fn counter_in_range_preservation_proof(
    lf: &SemLoopFunction,
    i_idx: u64,
    c: i128,
    bound_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the guard `eval_cond e cond = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ hg`: hg = 0, hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let e_b = Expr::app(Expr::bvar(2), Expr::nat_lit(bound_idx)); // e bound_idx
    let c_lit = int_lit(c);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    // The two conjunct PROPS the reduced codomain `And A B` carries.
    let prop_lo = Expr::apps(cst("Int.le"), [c_lit.clone(), i_plus_one.clone()]); // c ≤ i+1
    let prop_hi = Expr::apps(cst("Int.le"), [i_plus_one.clone(), e_b.clone()]); // i+1 ≤ n
    // hI : And (c ≤ e i) (i ≤ n). And.left/And.right project the conjuncts.
    let and_lo = Expr::apps(cst("Int.le"), [c_lit.clone(), e_i.clone()]); // c ≤ i
    let and_hi = Expr::apps(cst("Int.le"), [e_i.clone(), e_b.clone()]); // i ≤ n
    let h_lo = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [and_lo.clone(), and_hi.clone(), Expr::bvar(1)],
    ); // And.left … hI : c ≤ e i
    // LOWER conjunct proof: Int.le_trans c (e i) ((e i)+1) h_lo (Int.le_self_add_one (e i)).
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_i.clone());
    let proof_lo = Expr::apps(
        cst("Int.le_trans"),
        [c_lit, e_i.clone(), i_plus_one.clone(), h_lo, self_le_succ],
    );
    // UPPER conjunct proof: of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg
    //   : Int.lt (e i)(e n) ≡ Int.le ((e i)+1)(e n).
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_b.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i, e_b]);
    let proof_hi = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    // And.intro A B proof_lo proof_hi : And A B.
    let proof = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [prop_lo, prop_hi, proof_lo, proof_hi],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The preservation PROOF for the RELATIONAL conjoined invariant `I := λ e. (s == i) ∧
/// (i ≤ n)` over the LOCKSTEP accumulator body `[s := s + 1; i := i + 1]` (PART 1):
/// `λ (e : Env)(hI : I e)(hg : eval_cond e cond = true).
///    And.intro <s+1 == i+1> <i+1 ≤ n>`.
///
/// The codomain `I (exec e body)` ι-reduces to `And (@Eq Int ((e s)+1) ((e i)+1))
/// (Int.le ((e i)+1) (e n))` — `(exec e [s:=s+1; i:=i+1]) s ≡ (e s)+1`, `… i ≡ (e i)+1`,
/// `… n ≡ e n` (the body never assigns `n`). `And.intro` packages:
///
///  * (LEFT, the RELATIONAL step) `@congrArg Int Int (e s) (e i) (λ x. Int.add x 1)
///    (And.left hI)` : `@Eq Int ((λ x. x+1)(e s)) ((λ x. x+1)(e i))`, which β-reduces to
///    EXACTLY `@Eq Int ((e s)+1) ((e i)+1)` — the reduced LEFT codomain. This GENUINELY USES
///    the relational hypothesis `s == i` (`And.left hI`); a WRONG relational invariant (an
///    `s == i + 1` claim, or `s == i` on a body whose `s` update is not `+1`) makes the
///    reduced codomain's left operand `(e s)+δ` (δ ≠ 1) NOT def-eq to `congrArg`'s `(e s)+1`
///    ⇒ ill-typed ⇒ KernelRejected (fail-closed).
///
///  * (RIGHT, the guard step) `of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg` :
///    `Int.lt (e i)(e n) ≡ Int.le ((e i)+1)(e n)` — the reduced RIGHT codomain, re-established
///    SOLELY from the `Lt` guard, exactly as [`counter_le_bound_preservation_proof`].
pub(super) fn accum_eq_counter_preservation_proof(
    lf: &SemLoopFunction,
    s_idx: u64,
    i_idx: u64,
    n_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the guard `eval_cond e cond = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ hg`: hg = 0, hI = 1, e = 2.
    let e_s = Expr::app(Expr::bvar(2), Expr::nat_lit(s_idx)); // e s_idx
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let e_n = Expr::app(Expr::bvar(2), Expr::nat_lit(n_idx)); // e n_idx
    let s_plus_one = Expr::apps(cst("Int.add"), [e_s.clone(), int_one()]);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    let eq_of = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), a, b],
        )
    };
    // The two conjunct PROPS the reduced codomain `And A B` carries.
    let prop_eq = eq_of(s_plus_one.clone(), i_plus_one.clone()); // (s+1) == (i+1)
    let prop_hi = Expr::apps(cst("Int.le"), [i_plus_one, e_n.clone()]); // i+1 ≤ n
    // hI : And (@Eq Int (e s)(e i)) (Int.le (e i)(e n)). Project the conjuncts.
    let and_eq = eq_of(e_s.clone(), e_i.clone()); // s == i
    let and_hi = Expr::apps(cst("Int.le"), [e_i.clone(), e_n.clone()]); // i ≤ n
    let h_eq = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [and_eq.clone(), and_hi.clone(), Expr::bvar(1)],
    ); // And.left … hI : s == i
    // LEFT (RELATIONAL) proof: @congrArg Int Int (e s)(e i) (λ x. Int.add x 1) h_eq.
    //   succ-add closure: `λ (x : Int). Int.add x 1` — its application β-reduces to `· + 1`,
    //   the SAME normal form the body's `eval_rvalue` produces, so congrArg's output type
    //   `@Eq Int ((e s)+1) ((e i)+1)` def-eq matches the reduced codomain.
    let add_one_fn =
        Expr::lam(bd(), int_ty(), Expr::apps(cst("Int.add"), [Expr::bvar(0), int_one()]));
    let l1 = Level::succ(Level::zero());
    let proof_eq = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [int_ty(), int_ty(), e_s, e_i.clone(), add_one_fn, h_eq],
    );
    // RIGHT (guard) proof: of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg.
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i, e_n]);
    let proof_hi = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    // And.intro A B proof_eq proof_hi : And A B.
    let proof = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [prop_eq, prop_hi, proof_eq, proof_hi],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The preservation PROOF for the GENERAL RELATIONAL invariant `I := λ e. (a₀ == i) ∧ … ∧
/// (aₘ == i) ∧ (i ≤ n)` over the `m+1`-statement LOCKSTEP body `[a₀:=a₀+1; …; aₘ:=aₘ+1;
/// i:=i+1]` (PART 1: GENERAL OCTAGON over >2 variables):
/// `λ (e)(hI)(hg). And.intro <a₀+1==i+1> (And.intro <a₁+1==i+1> (… (of_decide_eq_true … hg)))`.
///
/// The codomain `I (exec e body)` ι-reduces to the SAME nested `And` with each `aₖ` and `i`
/// stepped to `aₖ+1`/`i+1` (`n` untouched). The proof MIRRORS the invariant's right-fold:
///
///  * For EACH accumulator `aₖ`, the LEFT conjunct is the congruence `aₖ == i → aₖ+1 == i+1`
///    (`@congrArg Int Int (e aₖ)(e i)(λ x. x+1) hₖ`, exactly as the 2-var
///    [`accum_eq_counter_preservation_proof`]), where `hₖ : aₖ == i` is projected from `hI`
///    by a chain of `And.left`/`And.right`. A WRONG relation (`aₖ == i + δ`, δ ≠ 0, or a
///    non-lockstep `aₖ` update) makes `congrArg`'s output `(e aₖ)+1 == (e i)+1` NOT def-eq
///    to the reduced codomain `(e aₖ)+δ == (e i)+1` ⇒ ill-typed ⇒ KernelRejected (fail-closed).
///  * The INNERMOST (cap) conjunct is the guard-aware upper bound `i+1 ≤ n` from the `Lt`
///    guard (`of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg`), as in the 2-var case.
pub(super) fn accum_eq_counter_set_preservation_proof(
    lf: &SemLoopFunction,
    accum_idxs: &[u64],
    i_idx: u64,
    n_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the guard `eval_cond e cond = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ hg`: hg = 0, hI = 1, e = 2.
    let e_at = |idx: u64| Expr::app(Expr::bvar(2), Expr::nat_lit(idx));
    let e_i = e_at(i_idx);
    let e_n = e_at(n_idx);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    let eq_of = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), a, b],
        )
    };
    let add_one_fn =
        || Expr::lam(bd(), int_ty(), Expr::apps(cst("Int.add"), [Expr::bvar(0), int_one()]));
    let l1 = || Level::succ(Level::zero());

    // The hypothesis `hI : (a₀==i) ∧ ((a₁==i) ∧ (… ∧ (i≤n)))` is a nested right-fold. To project
    // `hₖ : aₖ==i` we walk `And.left` after peeling `k` `And.right`s. We compute, for each level,
    // the LEFT prop (`aₖ==i`) and the RIGHT prop (`rest`), so the `And.left`/`And.right` projectors
    // are fully applied. Build the RIGHT-prop suffix list `rest[k]` (the conjunction of conjuncts
    // from `k` onward, capped by `i≤n`).
    let cap_le = Expr::apps(cst("Int.le"), [e_i.clone(), e_n.clone()]); // i ≤ n
    let n = accum_idxs.len();
    // suffix_prop[k] = And (aₖ==i) (And (a_{k+1}==i) (… (i≤n))) ; suffix_prop[n] = (i≤n).
    let mut suffix_prop = vec![cap_le.clone(); n + 1];
    suffix_prop[n] = cap_le.clone();
    for k in (0..n).rev() {
        let eqk = eq_of(e_at(accum_idxs[k]), e_i.clone());
        suffix_prop[k] = Expr::apps(cst("And"), [eqk, suffix_prop[k + 1].clone()]);
    }
    // The projected hypothesis `hI_rest[k] : suffix_prop[k]` (hI_rest[0] = hI = bvar(1)).
    // hI_rest[k+1] = And.right (aₖ==i) (suffix_prop[k+1]) hI_rest[k].
    let mut h_rest = Expr::bvar(1); // : suffix_prop[0]
    // Reduced codomain conjunct PROPS: each `aₖ+1 == i+1`, capped by `i+1 ≤ n`.
    // Build the proof BOTTOM-UP: start from the cap (guard upper bound), then wrap each
    // accumulator's congruence `And.intro` around it (outermost = a₀). We need each level's
    // RIGHT-codomain prop to type `And.intro`; compute the reduced suffix props too.
    // reduced_suffix[k] = And (aₖ+1==i+1) (… (i+1≤n)) ; reduced_suffix[n] = (i+1≤n).
    let cap_le_succ = Expr::apps(cst("Int.le"), [i_plus_one.clone(), e_n.clone()]); // i+1 ≤ n
    let mut reduced_suffix = vec![cap_le_succ.clone(); n + 1];
    reduced_suffix[n] = cap_le_succ.clone();
    for k in (0..n).rev() {
        let ak1 = Expr::apps(cst("Int.add"), [e_at(accum_idxs[k]), int_one()]);
        let eqk_succ = eq_of(ak1, i_plus_one.clone());
        reduced_suffix[k] = Expr::apps(cst("And"), [eqk_succ, reduced_suffix[k + 1].clone()]);
    }

    // Project each `hₖ : aₖ==i` from the running `h_rest`, and accumulate the And.intro chain
    // by recording per-level (left_proof, left_prop, right_prop) and folding from the cap.
    // We first collect the LEFT congruence proofs in order, advancing `h_rest`.
    let mut left_proofs: Vec<(Expr, Expr)> = Vec::with_capacity(n); // (left_proof, left_prop = aₖ+1==i+1)
    for k in 0..n {
        let eqk_prop = eq_of(e_at(accum_idxs[k]), e_i.clone()); // aₖ == i
        let rest_prop = suffix_prop[k + 1].clone(); // the right operand of this And
        // hₖ = And.left (aₖ==i) rest_prop h_rest : aₖ == i
        let hk = Expr::apps(
            Expr::const_(Name::from_string("And.left"), vec![]),
            [eqk_prop.clone(), rest_prop.clone(), h_rest.clone()],
        );
        // congruence: @congrArg Int Int (e aₖ)(e i)(λ x. x+1) hₖ : aₖ+1 == i+1.
        let proof_eqk = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
            [int_ty(), int_ty(), e_at(accum_idxs[k]), e_i.clone(), add_one_fn(), hk],
        );
        let ak1 = Expr::apps(cst("Int.add"), [e_at(accum_idxs[k]), int_one()]);
        let left_prop = eq_of(ak1, i_plus_one.clone()); // aₖ+1 == i+1
        left_proofs.push((proof_eqk, left_prop));
        // advance h_rest := And.right (aₖ==i) rest_prop h_rest : rest_prop
        h_rest = Expr::apps(
            Expr::const_(Name::from_string("And.right"), vec![]),
            [eqk_prop, rest_prop, h_rest],
        );
    }

    // CAP proof: of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg : i+1 ≤ n (def-eq).
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i.clone(), e_n.clone()]);
    let mut proof = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    // Fold the congruence And.intros around the cap, innermost (aₘ) first.
    for k in (0..n).rev() {
        let (left_proof, left_prop) = &left_proofs[k];
        let right_prop = reduced_suffix[k + 1].clone();
        proof = Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [left_prop.clone(), right_prop, left_proof.clone(), proof],
        );
    }
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The CONDITIONAL-UPDATE preservation PROOF for the synthesized invariant `I := λ e.
/// And (Int.le c (e m_idx)) (Int.le 0 (e i_idx))` (`c ≤ m ∧ 0 ≤ i`) over the body
/// `[m := Sel (i>m) i m; i := i+1]` (Trust: Step 6CU):
/// `λ (e)(hI)(_hg). And.intro <c ≤ m'> <0 ≤ i+1>` where `m' = iteI e (i>m) (e i)(e m)`.
///
/// The codomain `I (exec e body)` ι-reduces to `And (Int.le c (iteI e (i>m) (e i)(e m)))
/// (Int.le 0 ((e i)+1))` — `(exec e body) m_idx ≡ eval_rvalue e (Sel (i>m) i m) ≡
/// iteI e (i>m) (eval e (Var i)) (eval e (Var m)) ≡ iteI e (i>m) (e i)(e m)` (the second
/// statement `i := i+1` leaves `m_idx` untouched), and `(exec e body) i_idx ≡ (e i)+1`.
///
///  * (LEFT, the CASE-SPLIT) `iteI e (i>m) (e i)(e m) ≡ Bool.rec (λ_:Bool. Int) (e m)(e i)
///    (eval_cond e (i>m))`, so `Int.le c (iteI …)` is proved by `@Bool.rec.{0}`
///    over `eval_cond e (i>m)` with motive `λ b. Int.le c (Bool.rec (λ_.Int)(e m)(e i) b)`:
///      - FALSE-arm: `Bool.rec _ (e m)(e i) Bool.false ≡ e m`, goal `Int.le c (e m)` ←
///        `And.left hI` (the ELSE-arm: `m` unchanged, still `c ≤ m`).
///      - TRUE-arm: `Bool.rec _ (e m)(e i) Bool.true ≡ e i`, goal `Int.le c (e i)`. With the
///        TRACTABLE interval bound `c = 0` this is `Int.le 0 (e i)` ← `And.right hI` (the
///        THEN-arm: `m := i`, and `0 ≤ i` from the counter lower bound). A `c ≠ 0` makes the
///        TRUE-arm goal `Int.le c (e i)` NOT def-eq to `And.right hI : Int.le 0 (e i)` ⇒
///        ill-typed ⇒ KernelRejected (fail-closed on a then-arm-breaking `c`).
///  * (RIGHT, the counter step) `Int.le 0 ((e i)+1)` from `And.right hI : Int.le 0 (e i)` by
///    `Int.le_trans 0 (e i) ((e i)+1) (And.right hI) (Int.le_self_add_one (e i))` — the SAME
///    inductive lower-bound step as [`counter_ge_const_preservation_proof`].
///
/// The loop GUARD `_hg : eval_cond e (i<n) = true` is genuinely UNNEEDED (the lower bounds
/// hold regardless of the guard), kept only so the proof has the EXACT preservation type.
/// `i_idx`/`m_idx` are read from the synth invariant; the UPDATE condition `(i>m)` is read
/// from the body's `Sel` statement.
pub(super) fn cond_update_ge_const_preservation_proof(
    lf: &SemLoopFunction,
    m_idx: u64,
    c: i128,
    i_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr(); // the LOOP guard `i < n`.
    // The UPDATE condition `(i>m)` from the body's `Sel` statement (`m := Sel cond i m`).
    let upd_cond = lf
        .body
        .iter()
        .find_map(|s| match &s.rvalue {
            SemRvalue::Sel(c, _, _) => Some(c.clone()),
            _ => None,
        })
        .expect("CondUpdateGeConst body must carry a Sel statement");
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the loop guard `eval_cond e cond = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2.
    let e_m = Expr::app(Expr::bvar(2), Expr::nat_lit(m_idx)); // e m_idx
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let c_lit = int_lit(c);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    // The update condition `(i>m)` as a `Cond` term, lifted to the `λ e λ hI λ _hg` depth (e=2).
    let upd_cond_expr = upd_cond.to_cond_expr().lift(3);
    let eval_upd = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(2), upd_cond_expr]);

    // hI : And (Int.le c (e m)) (Int.le 0 (e i)). Project the conjuncts.
    let prop_lo_m = Expr::apps(cst("Int.le"), [c_lit.clone(), e_m.clone()]); // c ≤ m
    let prop_lo_i = Expr::apps(cst("Int.le"), [int_lit(0), e_i.clone()]); // 0 ≤ i
    let h_lo_m = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [prop_lo_m.clone(), prop_lo_i.clone(), Expr::bvar(1)],
    ); // And.left … hI : c ≤ m  (ELSE-arm witness)
    let h_lo_i = Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [prop_lo_m.clone(), prop_lo_i.clone(), Expr::bvar(1)],
    ); // And.right … hI : 0 ≤ i  (THEN-arm witness when c = 0; also the RIGHT-conjunct source)

    // ---- LEFT conjunct: Int.le c (iteI e (i>m) (e i)(e m)) by Bool.rec case-split. ----
    // iteI e (i>m) (e i)(e m) ≡ Bool.rec (λ_.Int) (e m)(e i) (eval_cond e (i>m)).
    let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
    // motive : λ (b : Bool). Int.le c (Bool.rec (λ_.Int) (e m)(e i) b).
    //   inside `λ b`: b=0; e is at depth +1 ⇒ e=3, c-literal is closed.
    let case_motive = {
        let e_m_b = Expr::app(Expr::bvar(3), Expr::nat_lit(m_idx));
        let e_i_b = Expr::app(Expr::bvar(3), Expr::nat_lit(i_idx));
        let bool_rec_b =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let chosen =
            Expr::apps(bool_rec_b, [int_motive.clone().lift(1), e_m_b, e_i_b, Expr::bvar(0)]);
        Expr::lam(bd(), cst("Bool"), Expr::apps(cst("Int.le"), [int_lit(c), chosen]))
    };
    // FALSE-minor : Int.le c (Bool.rec _ (e m)(e i) Bool.false) ≡ Int.le c (e m) ← h_lo_m.
    let false_minor = h_lo_m.clone();
    // TRUE-minor  : Int.le c (Bool.rec _ (e m)(e i) Bool.true) ≡ Int.le c (e i). With c = 0
    //   this is `Int.le 0 (e i)` ← h_lo_i (def-eq ONLY when c = 0 ⇒ fail-closed otherwise).
    let true_minor = h_lo_i.clone();
    let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    // @Bool.rec.{0} case_motive false_minor true_minor (eval_cond e (i>m)) : Int.le c (iteI …).
    let proof_lo_m = Expr::apps(bool_rec0, [case_motive, false_minor, true_minor, eval_upd]);

    // ---- RIGHT conjunct: Int.le 0 ((e i)+1) from h_lo_i by le_trans + le_self_add_one. ----
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_i.clone());
    let proof_lo_i = Expr::apps(
        cst("Int.le_trans"),
        [int_lit(0), e_i.clone(), i_plus_one.clone(), h_lo_i, self_le_succ],
    );

    // The reduced codomain conjunct PROPS (the `And A B` the codomain carries).
    // LEFT: Int.le c (iteI e (i>m) (e i)(e m)) — spelled via `iteI` (def-eq to the Bool.rec form).
    let ite_m = {
        let e_i_arm = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx));
        let e_m_arm = Expr::app(Expr::bvar(2), Expr::nat_lit(m_idx));
        let upd_cond_expr2 = upd_cond.to_cond_expr().lift(3);
        Expr::apps(cst(MIRSEM_ITE_I), [Expr::bvar(2), upd_cond_expr2, e_i_arm, e_m_arm])
    };
    let prop_lo_m_cod = Expr::apps(cst("Int.le"), [int_lit(c), ite_m]); // c ≤ iteI …
    let prop_lo_i_cod = Expr::apps(cst("Int.le"), [int_lit(0), i_plus_one]); // 0 ≤ i+1
    // And.intro A B proof_lo_m proof_lo_i : And A B.
    let proof = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [prop_lo_m_cod, prop_lo_i_cod, proof_lo_m, proof_lo_i],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The CONDITIONAL-INCREMENT preservation PROOF for the synthesized invariant `I := λ e.
/// Int.le c (e count_idx)` (`c ≤ count`) over the body `[tmp := count+1; count :=
/// Sel(cond, tmp, count); i := i+k]` (Trust: Step 6CI, Increment B, real-loop-leaf
/// frontier — sibling to [`cond_update_ge_const_preservation_proof`], over an `Add`
/// then-arm rather than a `Sel` then-arm):
/// `λ (e)(hI)(_hg). <Bool.rec case-split over eval_cond e upd_cond>`.
///
/// The codomain `I (exec e body)` ι-reduces to `Int.le c (iteI e upd_cond ((e count)+1)
/// (e count))` — `(exec e body) count_idx ≡ eval_rvalue e' (Sel upd_cond tmp count)`
/// where `e' = set e tmp_idx ((e count)+1)` (the FIRST statement's commit) `≡ iteI e'
/// upd_cond (e' tmp_idx)(e' count_idx) ≡ iteI e upd_cond ((e count)+1)(e count)`
/// (`tmp_idx ≠ count_idx`, and the update condition's env reads are UNTOUCHED by the
/// synthetic `tmp` commit — the extractor's disjointness guard, `find_cond_incr_accum` +
/// the caller's `touches_forbidden` check).
///
///  * FALSE-arm (`iteI …` reduces to `e count`): `Int.le c (e count)` ← `hI` DIRECTLY —
///    UNLIKE [`cond_update_ge_const_preservation_proof`] (whose invariant is a
///    CONJUNCTION, needing `And.left`), the invariant here IS this exact bare fact.
///  * TRUE-arm (`iteI …` reduces to `(e count)+1`): `Int.le c ((e count)+1)` ← the
///    ORDINARY inductive step `Int.le_trans c (e count) ((e count)+1) hI
///    (Int.le_self_add_one (e count))` — EXACTLY [`counter_ge_const_preservation_proof`]'s
///    proof, instantiated at `count_idx`.
///
/// The loop GUARD `_hg` is genuinely UNNEEDED (the lower bound holds regardless of the
/// guard — kept only so the proof has the EXACT preservation type). FAIL-CLOSED: a WRONG
/// `c` makes the TRUE-arm's `Int.le_trans` chain not retype against the reduced codomain
/// ⇒ ill-typed ⇒ KernelRejected.
pub(super) fn cond_incr_ge_const_preservation_proof(lf: &SemLoopFunction, count_idx: u64, c: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr(); // the OUTER loop guard `i < n`.
    // The UPDATE condition from the body's `Sel` statement (`count := Sel(upd_cond, tmp,
    // count)`) — the ONE statement whose idx is `count_idx` and whose rvalue is `Sel`.
    let upd_cond = lf
        .body
        .iter()
        .find_map(|s| match &s.rvalue {
            SemRvalue::Sel(c, _, _) if s.idx == count_idx => Some(c.clone()),
            _ => None,
        })
        .expect("CondIncrGeConst body must carry a count := Sel(cond, tmp, count) statement");

    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the LOOP guard `eval_cond e cond = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2.
    let e_count = Expr::app(Expr::bvar(2), Expr::nat_lit(count_idx));
    let c_lit = int_lit(c);
    let count_plus_one = Expr::apps(cst("Int.add"), [e_count.clone(), int_one()]);
    // The update condition, lifted to the `λ e λ hI λ _hg` depth (e = 2).
    let upd_cond_expr = upd_cond.to_cond_expr().lift(3);
    let eval_upd = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(2), upd_cond_expr]);

    // ---- Bool.rec case-split: Int.le c (Bool.rec (λ_.Int) (e count)((e count)+1) b). ----
    let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
    // motive : λ (b : Bool). Int.le c (Bool.rec (λ_.Int) (e count)((e count)+1) b).
    //   inside `λ b`: b = 0; e is at depth +1 ⇒ e = 3, the `c` literal is closed.
    let case_motive = {
        let e_count_b = Expr::app(Expr::bvar(3), Expr::nat_lit(count_idx));
        let count_plus_one_b = Expr::apps(cst("Int.add"), [e_count_b.clone(), int_one()]);
        let bool_rec_b =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let chosen = Expr::apps(
            bool_rec_b,
            [int_motive.clone().lift(1), e_count_b, count_plus_one_b, Expr::bvar(0)],
        );
        Expr::lam(bd(), cst("Bool"), Expr::apps(cst("Int.le"), [int_lit(c), chosen]))
    };
    // FALSE-minor : Int.le c (Bool.rec _ (e count)((e count)+1) Bool.false) ≡ Int.le c
    //   (e count) ← hI DIRECTLY (bvar(1) — the invariant's hypothesis binder).
    let false_minor = Expr::bvar(1);
    // TRUE-minor  : Int.le c (Bool.rec _ (e count)((e count)+1) Bool.true) ≡ Int.le c
    //   ((e count)+1) ← Int.le_trans c (e count)((e count)+1) hI (Int.le_self_add_one (e count)).
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_count.clone());
    let true_minor = Expr::apps(
        cst("Int.le_trans"),
        [c_lit, e_count, count_plus_one, Expr::bvar(1), self_le_succ],
    );
    let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    // @Bool.rec.{0} case_motive false_minor true_minor (eval_cond e upd_cond) : Int.le c
    //   (iteI e upd_cond ((e count)+1)(e count)).
    let proof = Expr::apps(bool_rec0, [case_motive, false_minor, true_minor, eval_upd]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// `@Int.add_le_add_right a b hab c : Int.le (Int.add a c) (Int.add b c)` — the
/// constructive (modulo-3) prelude monotone-add lemma, applied at the concrete args.
pub(super) fn add_le_add_right(a: Expr, b: Expr, hab: Expr, c: Expr) -> Expr {
    Expr::apps(cst("Int.add_le_add_right"), [a, b, hab, c])
}

/// The GUARD-AWARE preservation PROOF for the `≤`-guarded counter loop's UPPER-bound
/// invariant `I := λ e. Int.le (e i_idx) (Int.add (e bound_idx) 1)` (`i ≤ n+1`) over the
/// body `[i := i+1]`:
/// `λ (e)(_hI)(hg). Int.add_le_add_right (e i) (e n) <guard:i≤n> 1`.
///
/// The codomain `I (exec e [i:=i+1])` ι-reduces to `Int.le ((e i)+1) ((e n)+1)`. The `Le`
/// guard `hg : eval_cond e (i ≤ n) = true` is def-eq `decide (Int.le (e i)(e n)) … = true`,
/// so `of_decide_eq_true … hg : Int.le (e i)(e n)`. `Int.add_le_add_right` adds `1` on the
/// right of BOTH sides ⇒ `Int.le ((e i)+1)((e n)+1)` — EXACTLY the reduced codomain. This
/// genuinely USES the guard (a `Le` guard, unlike `Lt`, only re-establishes `i ≤ n+1`, not
/// `i ≤ n`). FAIL-CLOSED: a too-tight `CounterLeBound` (`i ≤ n`) on a `Le`-guarded loop has
/// codomain `Int.le (i+1) n`, which the guard `i ≤ n` does NOT provide ⇒ KernelRejected.
pub(super) fn counter_le_bound_succ_preservation_proof(
    lf: &SemLoopFunction,
    i_idx: u64,
    bound_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ _hI`: _hI = 0, e = 1; the guard `eval_cond e cond = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ _hI λ hg`: hg = 0, _hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let e_b = Expr::app(Expr::bvar(2), Expr::nat_lit(bound_idx)); // e bound_idx
    // p := Int.le (e i)(e n) ; inst := Int.decLe (e i)(e n).  The Le guard extracts `i ≤ n`.
    let p = Expr::apps(cst("Int.le"), [e_i.clone(), e_b.clone()]);
    let inst = Expr::apps(cst("Int.decLe"), [e_i.clone(), e_b.clone()]);
    let hg = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // : Int.le (e i)(e n)
    // Int.add_le_add_right (e i)(e n) hg 1 : Int.le ((e i)+1)((e n)+1) — the reduced codomain.
    let proof = add_le_add_right(e_i, e_b, hg, int_one());
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The preservation PROOF for the `≤`-guarded CONJOINED range `I := λ e. (c ≤ i) ∧ (i ≤
/// n+1)` over the body `[i := i+1]`. `And.intro` of (a) the LOWER conjunct (proved as in
/// [`counter_ge_const_preservation_proof`], `Int.le_trans` + `Int.le_self_add_one`, USES
/// `And.left hI`) and (b) the UPPER conjunct (proved as in
/// [`counter_le_bound_succ_preservation_proof`], `Int.add_le_add_right` on the `Le` guard).
pub(super) fn counter_in_range_succ_preservation_proof(
    lf: &SemLoopFunction,
    i_idx: u64,
    c: i128,
    bound_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ hg`: hg = 0, hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let e_b = Expr::app(Expr::bvar(2), Expr::nat_lit(bound_idx)); // e bound_idx
    let c_lit = int_lit(c);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    let b_plus_one = Expr::apps(cst("Int.add"), [e_b.clone(), int_one()]);
    // The two conjunct PROPS the reduced codomain `And A B` carries.
    let prop_lo = Expr::apps(cst("Int.le"), [c_lit.clone(), i_plus_one.clone()]); // c ≤ i+1
    let prop_hi = Expr::apps(cst("Int.le"), [i_plus_one.clone(), b_plus_one]); // i+1 ≤ n+1
    // hI : And (c ≤ e i) (e i ≤ e n + 1). And.left/And.right project the conjuncts.
    let and_lo = Expr::apps(cst("Int.le"), [c_lit.clone(), e_i.clone()]); // c ≤ i
    let and_hi_b1 = Expr::apps(cst("Int.add"), [e_b.clone(), int_one()]);
    let and_hi = Expr::apps(cst("Int.le"), [e_i.clone(), and_hi_b1]); // i ≤ n+1
    let h_lo = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [and_lo.clone(), and_hi.clone(), Expr::bvar(1)],
    ); // And.left … hI : c ≤ e i
    // LOWER conjunct: Int.le_trans c (e i) ((e i)+1) h_lo (Int.le_self_add_one (e i)).
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_i.clone());
    let proof_lo = Expr::apps(
        cst("Int.le_trans"),
        [c_lit, e_i.clone(), i_plus_one.clone(), h_lo, self_le_succ],
    );
    // UPPER conjunct: extract `i ≤ n` from the Le guard, then add 1 on both sides.
    let p = Expr::apps(cst("Int.le"), [e_i.clone(), e_b.clone()]);
    let inst = Expr::apps(cst("Int.decLe"), [e_i.clone(), e_b.clone()]);
    let hg = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // : i ≤ n
    let proof_hi = add_le_add_right(e_i, e_b, hg, int_one()); // : i+1 ≤ n+1
    let proof = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [prop_lo, prop_hi, proof_lo, proof_hi],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The GUARD-USING preservation PROOF for the COUNTDOWN loop's lower-bound invariant
/// `I := λ e. Int.le (int_lit c) (e i_idx)` (`c ≤ i`, with `c = 0`) over the body
/// `[i := i - 1]`, under the guard `i > 0`:
/// `λ (e)(_hI)(hg). countdownGe0 (e i) <guard: 0 < i>`  — for the canonical `c = 0`.
///
/// The codomain `I (exec e [i:=i-1])` ι-reduces to `Int.le 0 (Int.sub (e i) 1)`. The `Gt`
/// guard `hg : eval_cond e (i > 0) = true` is def-eq `decide (Int.lt 0 (e i)) … = true`
/// (the SWAPPED arm), so `of_decide_eq_true … hg : Int.lt 0 (e i)`, and the kernel-checked
/// `countdownGe0 (e i) … : Int.le 0 (Int.sub (e i) 1)` — EXACTLY the reduced codomain. The
/// lower bound is re-established from the guard (`0 < i ⇒ 0 ≤ i-1`), so the hypothesis `_hI`
/// is unneeded (kept for the preservation type). FAIL-CLOSED: a non-zero `c` (e.g. `1 ≤ i`,
/// false at the terminal `i = 0`) has codomain `Int.le c (i-1)` that `countdownGe0` (which
/// proves only `0 ≤ i-1`) does not retype against ⇒ KernelRejected; an INCREMENT body has
/// codomain `Int.le 0 (i+1)` ≠ `Int.le 0 (i-1)` ⇒ KernelRejected.
pub(super) fn countdown_ge_const_preservation_proof(lf: &SemLoopFunction, i_idx: u64, c: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ _hI λ hg`: hg = 0, _hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let _ = c; // only c = 0 is sound; a non-zero c is rejected by the kernel (see doc).
    // Extract `Int.lt 0 (e i)` from the SWAPPED Gt guard `decide (Int.lt 0 (e i))`.
    let zero = int_lit(0);
    let p = Expr::apps(cst("Int.lt"), [zero.clone(), e_i.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [zero.clone(), e_i.clone()]);
    let hlt = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // : 0 < e i
    // countdownGe0 (e i) hlt : Int.le 0 (Int.sub (e i) 1) — the reduced codomain.
    let proof = Expr::apps(cst(MIRSEM_COUNTDOWN_GE0), [e_i, hlt]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The preservation PROOF for the STRIDE loop's lower-bound invariant `I := λ e. Int.le
/// (int_lit c) (e i_idx)` (`c ≤ i`) over the body `[i := i + k]` (`k ≥ 1`):
/// `λ (e)(hI)(_hg). Int.le_trans c (e i) ((e i)+k) hI (strideSelfLe (e i))`
/// where `strideSelfLe (e i) : Int.le (e i) (Int.add (e i) k)` (since `k ≥ 0`).
///
/// The codomain `I (exec e [i:=i+k])` ι-reduces to `Int.le c (Int.add (e i) k)`. From the
/// loop-carried hypothesis `hI : Int.le c (e i)` and `strideSelfLe (e i) : Int.le (e i)
/// ((e i)+k)` (the kernel-checked `i ≤ i+k` for the concrete positive `k`), `Int.le_trans`
/// chains to `Int.le c ((e i)+k)` — EXACTLY the reduced codomain. This is the stride
/// analogue of [`counter_ge_const_preservation_proof`] (`k = 1` recovers it via
/// `Int.le_self_add_one`). FAIL-CLOSED: a DECREMENT body's codomain `Int.le c (i-k)` ≠
/// `Int.le c (i+k)` ⇒ KernelRejected; `strideSelfLe` is built per-`k` and only type-checks
/// for the ACTUAL stride.
pub(super) fn stride_ge_const_preservation_proof(lf: &SemLoopFunction, i_idx: u64, c: i128, k: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let c_lit = int_lit(c);
    let i_plus_k = Expr::apps(cst("Int.add"), [e_i.clone(), int_lit(k)]); // i + k
    // strideSelfLe (e i) : Int.le (e i) (Int.add (e i) k)  — i ≤ i+k for this fixed k ≥ 0.
    let self_le = stride_self_le_term(k, e_i.clone());
    // Int.le_trans c (e i) ((e i)+k) hI strideSelfLe : Int.le c ((e i)+k).
    let proof = Expr::apps(cst("Int.le_trans"), [c_lit, e_i, i_plus_k, Expr::bvar(1), self_le]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The CONCRETE preservation TYPE this loop function's invariant must satisfy:
/// `∀ (e : Env), I e → eval_cond e cond = true → I (exec e body)` — the exact shape
/// `loopInvariantRule`'s first argument expects, at the closed `(I, cond, body)`.
/// `claimed_local` overrides the invariant's pinned local (fail-closed hook).
///
/// Built (and consumed) by the genuineness test that checks the def-eq preservation
/// proof directly against this type; the production instance check feeds the same
/// preservation proof into `loopInvariantRule` (the application carries the type
/// implicitly), so this standalone builder is test-only.
#[cfg(test)]
pub(super) fn loop_instance_preservation_type(lf: &SemLoopFunction, claimed_local: Option<u64>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(claimed_local);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();
    // ∀ (e:Env), (I e) → (eval_cond e cond = true) → (I (exec e body))
    //   1st arrow domain `I e`: under `∀ e` ⇒ e=0, I lifted +1.
    let dom1 = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    //   2nd arrow domain `eval_cond e cond = true`: under `∀ e` + 1 arrow ⇒ e=1.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_expr.clone().lift(2)]);
    let dom2 = eq_bool_true(guard);
    //   codomain `I (exec e body)`: under `∀ e` + 2 arrows ⇒ e=2.
    let exec_body = Expr::apps(cst(MIRSEM_EXEC), [Expr::bvar(2), body_expr.lift(3)]);
    let cod = Expr::app(i_expr.lift(3), exec_body);
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

/// The PER-FUNCTION partial-correctness CONCLUSION TYPE — `loopInvariantRule`
/// SPECIALIZED at this function's closed `(I, cond, body)`:
/// `∀ (n : Nat)(e : Env), I e → I (exec_loop e cond body n)`. This is the
/// loop-carried invariant maintained for an ARBITRARY iteration count `n` — the
/// per-function instance the certificate kernel-checks. `claimed_local` overrides the
/// invariant local (fail-closed hook).
pub(super) fn loop_instance_conclusion_type(lf: &SemLoopFunction, claimed_local: Option<u64>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(claimed_local);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();
    // ∀ (n:Nat)(e:Env), I e → I (exec_loop e cond body n)
    //   inside `∀ n ∀ e`: e=0, n=1. `I e`: I lifted +2.
    let i_e = Expr::app(i_expr.clone().lift(2), Expr::bvar(0));
    //   `I (exec_loop e cond body n)`: under one more arrow ⇒ e=1, n=2; I lifted +3.
    let looped = exec_loop_app(Expr::bvar(1), cond_expr.lift(3), body_expr.lift(3), Expr::bvar(2));
    let i_loop = Expr::app(i_expr.lift(3), looped);
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    Expr::pi(bd(), cst("Nat"), body_e)
}

/// The PER-FUNCTION partial-correctness PROOF — `loopInvariantRule` APPLIED to this
/// function's closed `(I, cond, body, preservation)`:
/// `loopInvariantRule I cond body <preservation>`. Type-checking this APPLICATION at
/// the conclusion type IS the per-function corollary: the general while-rule,
/// instantiated here, proves THIS loop's invariant survives every iteration. No new
/// induction — it reuses the kernel-checked general proof. `claimed_local` overrides
/// the invariant local (fail-closed hook).
pub(super) fn loop_instance_proof(lf: &SemLoopFunction, claimed_local: Option<u64>) -> Expr {
    let i_expr = lf.invariant_expr(claimed_local);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();
    let pres = loop_instance_preservation_proof(lf, claimed_local);
    Expr::apps(cst(MIRSEM_LOOP_INVARIANT_RULE), [i_expr, cond_expr, body_expr, pres])
}

/// The TYPE of `andLeftTrue`: `∀ (a b : Bool), Eq Bool (Bool.and a b) Bool.true →
/// Eq Bool a Bool.true`.
pub(super) fn and_left_true_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let eq_bool = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), x, y],
        )
    };
    // ∀ (a : Bool)(b : Bool), (Bool.and a b = true) → (a = true)
    //   inside `∀ a ∀ b`: b=0, a=1.
    let band = Expr::apps(cst("Bool.and"), [Expr::bvar(1), Expr::bvar(0)]);
    let dom = eq_bool(band, cst("Bool.true"));
    // codomain under the arrow: a=2.
    let cod = eq_bool(Expr::bvar(2), cst("Bool.true"));
    let arrow = Expr::pi(bd(), dom, cod);
    Expr::pi(bd(), cst("Bool"), Expr::pi(bd(), cst("Bool"), arrow))
}

/// The PROOF of `andLeftTrue` by `Bool.rec` on `a`:
/// `λ (a b : Bool). @Bool.rec (λ a'. Bool.and a' b = true → a' = true)
///    (λ h. h)                          -- a'=false: Bool.and false b ≡ false, dom ≡ cod ≡ (false=true)
///    (λ _. Eq.refl Bool Bool.true)     -- a'=true : cod ≡ (true=true)
///    a`.
pub(super) fn and_left_true_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let eq_bool = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), x, y],
        )
    };
    // Under `λ (a : Bool) λ (b : Bool)`: b=0, a=1.
    // motive : λ (a' : Bool). (Bool.and a' b = true) → (a' = true)
    //   inside `λ a'`: a'=0, b=1, a=2.
    let motive = {
        let band = Expr::apps(cst("Bool.and"), [Expr::bvar(0), Expr::bvar(1)]);
        let dom = eq_bool(band, cst("Bool.true"));
        // codomain under the `dom →` arrow: a'=1.
        let cod = eq_bool(Expr::bvar(1), cst("Bool.true"));
        Expr::lam(bd(), cst("Bool"), Expr::pi(bd(), dom, cod))
    };
    // false_minor : (Bool.and false b = true) → (false = true)
    //   Bool.and false b ≡ false, so dom ≡ (false = true) ≡ cod ⇒ λ h. h.
    //   built under `λ a λ b` (no extra binder yet): b = bvar(0).
    let false_minor = {
        let band_f = Expr::apps(cst("Bool.and"), [cst("Bool.false"), Expr::bvar(0)]);
        let dom = eq_bool(band_f, cst("Bool.true"));
        Expr::lam(bd(), dom, Expr::bvar(0))
    };
    // true_minor : (Bool.and true b = true) → (true = true)
    //   cod ≡ (true = true) ⇒ λ _. Eq.refl Bool Bool.true.
    //   built under `λ a λ b`: b = bvar(0).
    let true_minor = {
        let band_t = Expr::apps(cst("Bool.and"), [cst("Bool.true"), Expr::bvar(0)]);
        let dom = eq_bool(band_t, cst("Bool.true"));
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), cst("Bool.true")],
        );
        Expr::lam(bd(), dom, refl)
    };
    // @Bool.rec.{0} motive false_minor true_minor a   (Prop motive ⇒ Bool.rec.{0}).
    let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let rec_app = Expr::apps(bool_rec0, [motive, false_minor, true_minor, Expr::bvar(1)]);
    Expr::lam(bd(), cst("Bool"), Expr::lam(bd(), cst("Bool"), rec_app))
}

/// Register `Trust.MirSem.andLeftTrue` (idempotent) — the `Bool.and` left-projection.
pub(super) fn register_and_left_true(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_AND_LEFT_TRUE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = and_left_true_type();
    let proof = and_left_true_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&proof, &ty).map_err(|e| format!("andLeftTrue check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: proof })
        .map_err(|e| format!("add_decl(andLeftTrue): {e:?}"))?;
    Ok(())
}

/// `andLeftTrue a b h : Eq Bool a Bool.true` — extract the LEFT component's truth from
/// `h : Bool.and a b = true`.
pub(super) fn and_left_true_app(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_AND_LEFT_TRUE), [a, b, h])
}

/// Build the env `loopInvariantRule` lives in (the whole-program env that registers
/// `stepLoop`/`exec_loop`/`stepPreservesInv`/`loopInvariantRule` + dependencies,
/// modulo 3). Reused by the per-function instance check.
///
/// Trust: HONEST FLOOR inc-2 (2026-07-23) — this is GATE-ITER-GEN-KEY-DISCIPLINE's
/// "blanket env-level theorem-instantiation surface" chokepoint. It registers ONLY the
/// generic loop meta-theory (`exec_loop` etc.) — it grounds NO per-function loop and learns
/// NO two-key symbol, so the F12 grounder fence keeps `iter_seq`/`iter_len`/`iter_has_next2`
/// out of every `exec_loop` term BY CONSTRUCTION (see the `SemIterStep` F12 record). The
/// per-function decline half is enforced downstream, where a concrete projected loop flows:
/// `loop_refinement_witness` / `iter_loop_partial_witness` call
/// [`sem_loop_function_carries_entry_iter_handle`] fail-closed.
pub(crate) fn loop_instance_env() -> Result<Environment, String> {
    let mut env = mirsem_env()?;
    register_step_loop(&mut env)?;
    register_exec_loop(&mut env)?;
    register_step_preserves_inv(&mut env)?;
    // The constructive Int-order lemma suite — needed by the SYNTHESIZED-invariant
    // preservation proof (`Int.le_trans` + `Int.le_self_add_one`). Idempotent and
    // modulo 3; harmless for the untouched-local equality path (which does not use it).
    env.init_int_ord_lemmas().map_err(|e| format!("init_int_ord_lemmas: {e:?}"))?;
    // The COUNTDOWN lower-bound lemma `0 < i → 0 ≤ i-1`, needed by the countdown
    // shape's preservation proof. Idempotent, modulo 3.
    register_countdown_ge0(&mut env)?;
    let rule_ty = loop_invariant_rule_type(None);
    let rule_proof = loop_invariant_rule_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&rule_proof, &rule_ty)
            .map_err(|e| format!("loopInvariantRule check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_LOOP_INVARIANT_RULE),
        level_params: vec![],
        type_: rule_ty,
        value: rule_proof,
    })
    .map_err(|e| format!("add_decl(loopInvariantRule): {e:?}"))?;
    Ok(env)
}

/// Build the env the NESTED-LOOP layer lives in: everything `loop_instance_env`
/// provides (`exec_loop`/`loopInvariantRule` for the INNER loop) PLUS the `OStmt`
/// layer (`execO`/`stepLoopO`/`exec_loopO`/`stepPreservesInvO`/`loopInvariantRuleO`)
/// for the OUTER loop. Modulo 3 (every new decl is a def or a `Nat.rec`/`Bool.rec`
/// proof). Reused by the nested per-function instance check.
pub(crate) fn nested_loop_env() -> Result<Environment, String> {
    let mut env = loop_instance_env()?;
    register_ostmt_inductive(&mut env)?;
    register_exec_o(&mut env)?;
    register_step_loop_o(&mut env)?;
    register_exec_loop_o(&mut env)?;
    register_step_preserves_inv_o(&mut env)?;
    register_loop_invariant_rule_o(&mut env)?;
    Ok(env)
}

/// Kernel-check the PER-FUNCTION loop-invariant INSTANCE for a concrete loop function
/// `lf` against the real clean-kernel: build the per-function conclusion type
/// `∀ n e, I e → I (exec_loop e cond body n)` and the proof `loopInvariantRule I cond
/// body <preservation>`, `check_type`, register, and audit ⊆ 3.
///
/// A [`RefinementVerdict::ProvenModulo3`] means: the GENERAL Hoare while-rule,
/// INSTANTIATED at THIS function's concrete invariant/guard/body and fed a CONCRETE
/// preservation proof, kernel-checks modulo exactly 3 — the loop rule is WIRED for
/// this function. `claimed_local = Some(l)` overrides the invariant's pinned local
/// (the fail-closed hook: a WRONG invariant about a local the body ASSIGNS makes the
/// def-eq preservation proof ill-typed ⇒ KernelRejected).
pub(super) fn check_loop_refinement_instance_inner(
    lf: &SemLoopFunction,
    claimed_local: Option<u64>,
) -> RefinementVerdict {
    let mut env = match loop_instance_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = loop_instance_conclusion_type(lf, claimed_local);
    let proof = loop_instance_proof(lf, claimed_local);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!("loop instance check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.loopInstance.partialCorrect");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add loop instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("loop instance axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("loop instance decl not found".to_string()),
    }
}

/// Kernel-check the PER-FUNCTION partial-correctness loop instance for `lf` (the
/// honest invariant). See [`check_loop_refinement_instance_inner`].
#[must_use]
pub fn check_loop_refinement_instance(lf: &SemLoopFunction) -> RefinementVerdict {
    check_loop_refinement_instance_inner(lf, None)
}

/// Mint a [`LoopRefinementCertificate`] for `lf` IF the per-function loop instance
/// kernel-checks modulo 3. Fail-closed: returns `None` when the body ASSIGNS the
/// invariant's pinned local (the untouched-local invariant is not preserved, so the
/// instance is unsound to claim — we never even attempt the kernel check), or when
/// the kernel rejects the instance. A returned certificate is a genuine modulo-3
/// per-function loop refinement.
#[must_use]
pub fn loop_refinement_witness(lf: &SemLoopFunction) -> Option<LoopRefinementCertificate> {
    // Trust: HONEST FLOOR inc-2 (2026-07-23) — GATE-ITER-GEN-KEY-DISCIPLINE clause-(i) decline
    // half, WIRED at this loop-instance chokepoint. A projected loop that smuggles the two-key
    // entry-time iterator handle is non-composable by mechanism (the F12 grounder fence + the
    // standing composition refusal — see the `SemIterStep` doc); decline fail-closed. VACUOUSLY
    // FALSE today (every projected loop is ghost/param-var-only), so this is byte-green — it is
    // regression protection, not a live gate.
    if sem_loop_function_carries_entry_iter_handle(lf) {
        return None;
    }
    // SOUNDNESS GUARD (untouched-local form ONLY): the equality invariant `I := λ e.
    // e[inv_local] = c` is preserved DEFINITIONALLY only if the body never assigns
    // `inv_local`. If it does, the invariant is NOT trivially preserved — fail closed.
    // The SYNTHESIZED form carries a GENUINE arithmetic preservation proof (it DOES
    // expect the body to assign the counter), so this definitional guard does NOT
    // apply — its soundness is enforced by the kernel check below (a wrong synthesized
    // invariant is ill-typed ⇒ KernelRejected ⇒ `None`).
    if lf.synth_inv.is_none() && lf.body_assigns(lf.inv_local) {
        return None;
    }
    match check_loop_refinement_instance(lf) {
        RefinementVerdict::ProvenModulo3 => Some(LoopRefinementCertificate {
            function: lf.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// The break PRESERVATION PROOF for the synthesized upper-bound invariant `I := λ e.
/// e[i] ≤ e[n]` under the COMBINED guard `cond ∧ ¬brk`:
/// `λ (e)(_hI)(hcomb : (eval_cond e cond ∧ ¬eval_cond e brk) = true).
///    of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …)
///       (andLeftTrue (eval_cond e cond) (Bool.not (eval_cond e brk)) hcomb)`.
///
/// `andLeftTrue` projects `eval_cond e cond = true` out of the combined guard, and then
/// the proof is IDENTICAL to [`counter_le_bound_preservation_proof`]: `of_decide_eq_true`
/// turns `eval_cond e (i<n) = true` into `Int.lt (e i)(e n)`, which is DEFINITIONALLY
/// `Int.le ((e i)+1)(e n)` — EXACTLY the reduced codomain `I (exec e [i:=i+1])`. The
/// break-condition's truth (the RIGHT component) is genuinely UNNEEDED for `i ≤ n`. A
/// WRONG break invariant — one not preserved by the body under the combined guard (e.g.
/// `i ≤ n-1`, false after the last guarded step) — makes the reduced codomain differ ⇒
/// `of_decide_eq_true` does not retype ⇒ KernelRejected.
pub(super) fn break_le_bound_preservation_proof(
    blf: &SemBreakLoopFunction,
    i_idx: u64,
    bound_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = blf.invariant_expr();
    let cond_expr = blf.cond.to_cond_expr();
    let brk_expr = blf.brk.to_cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ _hI`: _hI = 0, e = 1; the COMBINED guard `(cond ∧ ¬brk) = true`.
    let comb =
        combined_brk_guard(&Expr::bvar(1), &cond_expr.clone().lift(2), &brk_expr.clone().lift(2));
    let comb_eq = eq_bool_true(comb);
    // inside `λ e λ _hI λ hcomb`: hcomb = 0, _hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx)); // e i_idx
    let e_b = Expr::app(Expr::bvar(2), Expr::nat_lit(bound_idx)); // e bound_idx
    // The two Bool components of the combined guard at this depth.
    let g_cond = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(2), cond_expr.lift(3)]);
    let g_brk = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(2), brk_expr.lift(3)]);
    let not_brk = Expr::app(cst("Bool.not"), g_brk);
    // hg := andLeftTrue (eval_cond e cond) (Bool.not (eval_cond e brk)) hcomb : eval_cond e cond = true.
    let hg = and_left_true_app(g_cond, not_brk, Expr::bvar(0));
    // p := Int.lt (e i)(e n) ; inst := Int.decLt (e i)(e n).
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_b.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i, e_b]);
    // of_decide_eq_true p inst hg : Int.lt (e i)(e n) ≡ Int.le ((e i)+1)(e n).
    let proof = Expr::apps(of_decide_eq_true_term(), [p, inst, hg]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), comb_eq, proof)))
}

/// The PER-FUNCTION break-loop CONCLUSION TYPE — `loopInvariantRuleBrk` SPECIALIZED at
/// this function's `(I, cond, brk, body)`:
/// `∀ (n : Nat)(e : Env), I e → I (exec_loopBrk e cond brk body n)`. The invariant holds
/// at the env reached after `n` combined-guarded steps — i.e. at EITHER exit point.
pub(super) fn break_loop_conclusion_type(blf: &SemBreakLoopFunction) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = blf.invariant_expr();
    let cond_expr = blf.cond.to_cond_expr();
    let brk_expr = blf.brk.to_cond_expr();
    let body_expr = blf.body_list_expr();
    // ∀ (n e), I e → I (exec_loopBrk e cond brk body n)
    let i_e = Expr::app(i_expr.clone().lift(2), Expr::bvar(0));
    let looped = exec_loop_brk_app(
        Expr::bvar(1),
        cond_expr.lift(3),
        brk_expr.lift(3),
        body_expr.lift(3),
        Expr::bvar(2),
    );
    let i_loop = Expr::app(i_expr.lift(3), looped);
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    Expr::pi(bd(), cst("Nat"), body_e)
}

/// The PER-FUNCTION break-loop PROOF — `loopInvariantRuleBrk I cond brk body <pres>`.
pub(super) fn break_loop_proof(blf: &SemBreakLoopFunction) -> Expr {
    let i_expr = blf.invariant_expr();
    let cond_expr = blf.cond.to_cond_expr();
    let brk_expr = blf.brk.to_cond_expr();
    let body_expr = blf.body_list_expr();
    let pres = match &blf.synth_inv {
        SynthInvariant::CounterLeBound { i_idx, bound_idx } => {
            break_le_bound_preservation_proof(blf, *i_idx, *bound_idx)
        }
        // Other synth forms are DEFERRED for the break shape; build a deliberately
        // ill-typed placeholder so the kernel rejects (fail-closed) rather than
        // silently accepting an unsupported claim. (No such call path is wired today.)
        _ => break_le_bound_preservation_proof(blf, 0, 0),
    };
    Expr::apps(cst(MIRSEM_LOOP_INVARIANT_RULE_BRK), [i_expr, cond_expr, brk_expr, body_expr, pres])
}

/// Build the env the break-loop layer lives in: everything `loop_instance_env` provides
/// PLUS the break-loop family (`stepLoopBrk`/`exec_loopBrk`/`stepPreservesInvBrk`/
/// `loopInvariantRuleBrk`) and `andLeftTrue`. Modulo 3.
pub(crate) fn break_loop_env() -> Result<Environment, String> {
    let mut env = loop_instance_env()?;
    register_and_left_true(&mut env)?;
    register_step_loop_brk(&mut env)?;
    register_exec_loop_brk(&mut env)?;
    register_step_preserves_inv_brk(&mut env)?;
    register_loop_invariant_rule_brk(&mut env)?;
    Ok(env)
}

/// Kernel-check the PER-FUNCTION break-loop INSTANCE for `blf` against the real
/// clean-kernel: build `∀ n e, I e → I (exec_loopBrk e cond brk body n)` and the proof
/// `loopInvariantRuleBrk I cond brk body <pres>`, `check_type`, register, and audit ⊆ 3.
/// A [`RefinementVerdict::ProvenModulo3`] means the break-able Hoare while-rule,
/// INSTANTIATED at THIS loop's `(I, cond, brk, body)` and fed a combined-guard
/// preservation proof, kernel-checks modulo exactly 3 — the invariant holds at BOTH exit
/// points (guard-false AND break).
#[must_use]
pub fn check_break_loop_instance(blf: &SemBreakLoopFunction) -> RefinementVerdict {
    let mut env = match break_loop_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = break_loop_conclusion_type(blf);
    let proof = break_loop_proof(blf);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!("break loop check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.breakLoopInstance.partialCorrect");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add break loop instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("break loop axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("break loop decl not found".to_string()),
    }
}

/// Mint a [`BreakLoopCertificate`] for `blf` IF the per-function break-loop instance
/// kernel-checks modulo 3. Fail-closed: only the wired `CounterLeBound` synthesized
/// invariant is attempted, and a WRONG bound (not preserved by the body under the
/// combined guard) is KernelRejected ⇒ `None`.
#[must_use]
pub fn break_loop_witness(blf: &SemBreakLoopFunction) -> Option<BreakLoopCertificate> {
    // Only the guard-aware upper bound `i ≤ n` is wired for the break shape today.
    if !matches!(blf.synth_inv, SynthInvariant::CounterLeBound { .. }) {
        return None;
    }
    match check_break_loop_instance(blf) {
        RefinementVerdict::ProvenModulo3 => Some(BreakLoopCertificate {
            function: blf.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// The INNER untouched-local invariant `Ir := λ (e' : Env). @Eq Int (e' t_idx) (e t_idx)`,
/// built so that the OUTER env `e` is the de Bruijn ref `e_ref` (it sits OUTSIDE the
/// `λ e'` this introduces, so callers pass `e_ref` at the depth BEFORE `λ e'`). Used
/// by the inner `loopInvariantRule` instance — it states the inner loop keeps `t_idx`
/// equal to whatever it was in the OUTER env `e`.
pub(super) fn nested_inner_invariant_expr(t_idx: u64, e_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `λ (e' : Env)`: e' = bvar(0); e_ref lifted by 1.
    let e_prime_at = Expr::app(Expr::bvar(0), Expr::nat_lit(t_idx));
    let e_at = Expr::app(e_ref.clone().lift(1), Expr::nat_lit(t_idx));
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [int_ty(), e_prime_at, e_at],
    );
    Expr::lam(bd(), env_ty(), eq)
}

/// The INNER preservation proof `∀ e', Ir e' → eval_cond e' cond_inner = true →
/// Ir (exec e' inner_body)`. Because `inner_body` never writes `t_idx`, the codomain
/// `Ir (exec e' inner_body) ≡ Eq Int (e' t_idx) (e t_idx) ≡ Ir e'` is def-eq to the
/// hypothesis, so the proof is `λ e' hr _hg. hr`. `e_ref` is the OUTER env, at the
/// depth BEFORE this builder's binders. FAIL-CLOSED: if `inner_body` DID write
/// `t_idx`, `(exec e' inner_body) t_idx` would not ι-reduce to `e' t_idx`, so the
/// codomain would differ from `Ir e'` and `hr` would be ill-typed ⇒ KernelRejected.
pub(super) fn nested_inner_preservation_proof(nlf: &SemNestedLoopFunction, e_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let ir = nested_inner_invariant_expr(nlf.t_idx, e_ref);
    let cond_inner = nlf.cond_inner.to_cond_expr();
    // inside `λ e'`: e' = bvar(0); Ir lifted +1 for `Ir e'`.
    let ir_e = Expr::app(ir.clone().lift(1), Expr::bvar(0));
    // inside `λ e' λ hr`: hr = 0, e' = 1; the guard `eval_cond e' cond_inner = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_inner.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e' λ hr λ _hg`: hr = 1 ⇒ return hr.
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), ir_e, Expr::lam(bd(), guard_eq, Expr::bvar(1))))
}

/// The OUTER preservation proof `∀ e, I e → eval_cond e cond_outer = true →
/// I (execO e outer_body)` for the nested loop. The `outer_body` runs the inner loop
/// (symbolic fuel ref `fuel_ref`, bound OUTSIDE this term) then the counter increment;
/// neither writes `t_idx`, so the codomain reduces to `Eq Int ((exec_loop e cond_inner
/// inner_body fuel) t_idx) (int_lit t_const)`. We bridge it with:
///   inner_keeps := loopInvariantRule Ir cond_inner inner_body <inner_pres> fuel e (Eq.refl …)
///                  : Eq Int ((exec_loop e cond_inner inner_body fuel) t_idx) (e t_idx)
///   proof       := Eq.trans … inner_keeps hI
///                  : Eq Int ((exec_loop …) t_idx) (int_lit t_const).
/// `fuel_ref` is at the depth BEFORE the `λ e λ hI λ _hg` this builder introduces.
pub(super) fn nested_outer_preservation_proof(nlf: &SemNestedLoopFunction, fuel_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = nlf.invariant_expr();
    let cond_outer = nlf.cond_outer.to_cond_expr();
    // inside `λ e`: e = bvar(0); I lifted +1 for `I e`.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the guard `eval_cond e cond_outer = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_outer.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2. `fuel_ref` lifted +3.
    let e_ref = Expr::bvar(2);
    let fuel = fuel_ref.clone().lift(3);
    let t_lit_e = Expr::app(e_ref.clone(), Expr::nat_lit(nlf.t_idx)); // e t_idx
    let cond_inner = nlf.cond_inner.to_cond_expr();
    let inner_body = nlf.inner_body_list_expr();
    // exec_loop e cond_inner inner_body fuel  (the inner-loop result env).
    let inner_result =
        exec_loop_app(e_ref.clone(), cond_inner.clone(), inner_body.clone(), fuel.clone());
    let inner_result_at_t = Expr::app(inner_result, Expr::nat_lit(nlf.t_idx)); // (exec_loop …) t_idx

    // Ir := λ e'. Eq Int (e' t_idx) (e t_idx)   (e = bvar(2) at this depth).
    let ir = nested_inner_invariant_expr(nlf.t_idx, &e_ref);
    // inner_pres : ∀ e', Ir e' → guard_inner → Ir (exec e' inner_body)
    let inner_pres = nested_inner_preservation_proof(nlf, &e_ref);
    // Eq.refl Int (e t_idx) : Ir e   (Ir e ≡ Eq Int (e t_idx) (e t_idx)).
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl_ir_e = Expr::apps(eq_refl.clone(), [int_ty(), t_lit_e.clone()]);
    // inner_keeps := loopInvariantRule Ir cond_inner inner_body inner_pres fuel e refl_ir_e
    //   : Ir (exec_loop e cond_inner inner_body fuel)
    //   ≡ Eq Int ((exec_loop …) t_idx) (e t_idx).
    let inner_keeps = Expr::apps(
        cst(MIRSEM_LOOP_INVARIANT_RULE),
        [ir, cond_inner, inner_body, inner_pres, fuel, e_ref.clone(), refl_ir_e],
    );
    // hI : Eq Int (e t_idx) (int_lit t_const)  (hI = bvar(1)).
    let h_i = Expr::bvar(1);
    // Eq.trans Int ((exec_loop …) t_idx) (e t_idx) (int_lit t_const) inner_keeps hI
    //   : Eq Int ((exec_loop …) t_idx) (int_lit t_const)
    //   — which is def-eq to `I (execO e outer_body)` (the outer Assign leaves t_idx, and
    //     execO threads through exec_loop for the Loop arm).
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(Level::zero())]);
    let proof = Expr::apps(
        eq_trans,
        [int_ty(), inner_result_at_t, t_lit_e, int_lit(nlf.t_const), inner_keeps, h_i],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The PER-FUNCTION nested-loop CONCLUSION TYPE — `loopInvariantRuleO` SPECIALIZED at
/// the function's `(I, cond_outer, outer_body(fuel))`, universally quantified over the
/// inner fuel `f`: `∀ (f n : Nat)(e : Env), I e → I (exec_loopO e cond_outer
/// (outer_body f) n)`.
pub(super) fn nested_loop_conclusion_type(nlf: &SemNestedLoopFunction) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = nlf.invariant_expr();
    let cond_outer = nlf.cond_outer.to_cond_expr();
    // ∀ (f : Nat). [ ∀ (n : Nat)(e : Env), I e → I (exec_loopO e cond_outer (outer_body f) n) ]
    // inside `∀ f ∀ n ∀ e`: e=0, n=1, f=2.
    let i_e = Expr::app(i_expr.clone().lift(3), Expr::bvar(0));
    // under one more arrow: e=1, n=2, f=3.
    let outer_body = nlf.outer_body_list_expr(Expr::bvar(3));
    let looped = exec_loop_o_app(Expr::bvar(1), cond_outer.lift(4), outer_body, Expr::bvar(2));
    let i_loop = Expr::app(i_expr.lift(4), looped);
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    Expr::pi(bd(), cst("Nat"), body_n)
}

/// The PER-FUNCTION nested-loop PROOF — `λ (f : Nat). loopInvariantRuleO I cond_outer
/// (outer_body f) <outer_pres f>`. Type-checking it at the conclusion type IS the
/// nested-loop corollary: the OUTER while-rule, instantiated here with an OUTER
/// preservation proof that runs the inner loop to completion (via the inner
/// `loopInvariantRule`), proves the outer invariant survives every outer iteration.
pub(super) fn nested_loop_proof(nlf: &SemNestedLoopFunction) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = nlf.invariant_expr();
    let cond_outer = nlf.cond_outer.to_cond_expr();
    // inside `λ (f : Nat)`: f = bvar(0).
    let outer_body = nlf.outer_body_list_expr(Expr::bvar(0));
    let outer_pres = nested_outer_preservation_proof(nlf, &Expr::bvar(0));
    let inst = Expr::apps(
        cst(MIRSEM_LOOP_INVARIANT_RULE_O),
        [i_expr.lift(1), cond_outer.lift(1), outer_body, outer_pres],
    );
    Expr::lam(bd(), cst("Nat"), inst)
}

/// Kernel-check the PER-FUNCTION nested-loop INSTANCE for `nlf` against the real
/// clean-kernel: build `∀ f n e, I e → I (exec_loopO e cond_outer (outer_body f) n)`
/// and the proof `λ f. loopInvariantRuleO I cond_outer (outer_body f) <outer_pres>`,
/// `check_type`, register, and audit ⊆ 3. A [`RefinementVerdict::ProvenModulo3`] means
/// the OUTER Hoare while-rule, INSTANTIATED at THIS nested loop's `(I, cond_outer,
/// outer_body)` and fed an OUTER preservation proof that runs the inner loop to
/// completion, kernel-checks modulo exactly 3.
#[must_use]
pub fn check_nested_loop_instance(nlf: &SemNestedLoopFunction) -> RefinementVerdict {
    let mut env = match nested_loop_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = nested_loop_conclusion_type(nlf);
    let proof = nested_loop_proof(nlf);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!("nested loop check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.nestedLoopInstance.partialCorrect");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add nested loop instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("nested loop axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("nested loop decl not found".to_string()),
    }
}

/// Mint a [`NestedLoopCertificate`] for `nlf` IF the per-function nested-loop instance
/// kernel-checks modulo 3. Fail-closed: returns `None` when the OUTER counter is the
/// untouched local, or when the INNER body assigns the untouched local (the
/// untouched-local invariant is then unsound to claim — we never attempt the check),
/// or when the kernel rejects. A returned certificate is a genuine modulo-3
/// per-function nested-loop refinement.
#[must_use]
pub fn nested_loop_witness(nlf: &SemNestedLoopFunction) -> Option<NestedLoopCertificate> {
    // SOUNDNESS GUARD: the untouched-local invariant `I := λ e. e[t_idx] = c` is
    // preserved only if NEITHER the inner body NOR the outer counter-assignment writes
    // `t_idx`. The outer body assigns ONLY `counter_idx`; the inner body assigns its
    // own locals. Fail closed if either touches the untouched local.
    if nlf.counter_idx == nlf.t_idx || nlf.inner_assigns(nlf.t_idx) {
        return None;
    }
    match check_nested_loop_instance(nlf) {
        RefinementVerdict::ProvenModulo3 => Some(NestedLoopCertificate {
            function: nlf.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// The INNER lower-bound preservation proof `∀ e', Ir e' → eval_cond e' cond_inner = true
/// → Ir (exec e' inner_body)` for `Ir := λ e'. c ≤ e'[s_idx]`, over the inner body that
/// INCREMENTS `s_idx` by `+1`:
/// `λ (e')(hr : c ≤ e'[s])(_hg). Int.le_trans c (e' s) ((e' s)+1) hr (Int.le_self_add_one (e' s))`.
///
/// The codomain `Ir (exec e' inner_body)` ι-reduces to `Int.le c ((e' s_idx)+1)` —
/// `(exec e' [s:=s+1; j:=j+1]) s_idx ≡ (e' s_idx)+1` (the `j:=j+1` leaves `s_idx`
/// untouched). From `hr : c ≤ e' s` and `Int.le_self_add_one (e' s) : (e' s) ≤ (e' s)+1`,
/// `Int.le_trans` chains to `c ≤ (e' s)+1` — EXACTLY the reduced codomain. This GENUINELY
/// USES the loop-carried hypothesis `hr` (monotone lower bound, carried, not re-derived).
/// FAIL-CLOSED: a DECREMENT inner body gives codomain `c ≤ (e' s)-1`, NOT def-eq to the
/// `Int.le_self_add_one` output `c ≤ (e' s)+1` ⇒ ill-typed ⇒ KernelRejected.
pub(super) fn monotone_inner_preservation_proof(mlf: &SemMonotoneNestedLoopFunction) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let ir = mlf.invariant_expr();
    let cond_inner = mlf.cond_inner.to_cond_expr();
    // inside `λ e'`: e' = 0; `Ir e'` for the hypothesis binder.
    let ir_e = Expr::app(ir.clone().lift(1), Expr::bvar(0));
    // inside `λ e' λ hr`: hr = 0, e' = 1; the guard `eval_cond e' cond_inner = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_inner.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e' λ hr λ _hg`: _hg = 0, hr = 1, e' = 2.
    let e_s = Expr::app(Expr::bvar(2), Expr::nat_lit(mlf.s_idx)); // e' s_idx
    let c_lit = int_lit(mlf.c);
    let s_plus_one = Expr::apps(cst("Int.add"), [e_s.clone(), int_one()]);
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_s.clone());
    // Int.le_trans c (e' s) ((e' s)+1) hr (Int.le_self_add_one (e' s)) : Int.le c ((e' s)+1).
    let proof =
        Expr::apps(cst("Int.le_trans"), [c_lit, e_s, s_plus_one, Expr::bvar(1), self_le_succ]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), ir_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The OUTER preservation proof `∀ e, I e → eval_cond e cond_outer = true →
/// I (execO e outer_body)` for the MONOTONE nested loop. The outer codomain
/// `I (execO e outer_body) ≡ Int.le c ((execO e [Loop(…); Assign(i,i+1)]) s_idx)` reduces
/// (the outer `Assign(i, …)` leaves `s_idx`, and `execO`'s `Loop` arm threads through
/// `exec_loop`) to `Int.le c ((exec_loop e cond_inner inner_body fuel) s_idx)`. We
/// inhabit it DIRECTLY with the INNER `loopInvariantRule` at `Ir := λ e'. c ≤ e'[s]`:
///   inner_keeps := loopInvariantRule Ir cond_inner inner_body <inner_pres> fuel e hI
///                  : Ir (exec_loop e cond_inner inner_body fuel)
///                  ≡ Int.le c ((exec_loop …) s_idx).
/// `hI : I e ≡ Ir e` is fed DIRECTLY as the base (no `Eq.refl`/`Eq.trans` — `I` and `Ir`
/// are the SAME predicate). `fuel_ref` is at the depth BEFORE `λ e λ hI λ _hg`.
pub(super) fn monotone_outer_preservation_proof(mlf: &SemMonotoneNestedLoopFunction, fuel_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = mlf.invariant_expr();
    let cond_outer = mlf.cond_outer.to_cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the guard `eval_cond e cond_outer = true`.
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), cond_outer.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2. `fuel_ref` lifted +3.
    let e_ref = Expr::bvar(2);
    let fuel = fuel_ref.clone().lift(3);
    let cond_inner = mlf.cond_inner.to_cond_expr();
    let inner_body = mlf.inner_body_list_expr();
    // Ir := λ e'. Int.le c (e' s_idx)  — the SAME predicate as `I` (closed; does NOT
    // reference the outer `e`).
    let ir = mlf.invariant_expr();
    // inner_pres : ∀ e', Ir e' → guard_inner → Ir (exec e' inner_body)
    let inner_pres = monotone_inner_preservation_proof(mlf);
    // inner_keeps := loopInvariantRule Ir cond_inner inner_body inner_pres fuel e hI
    //   : Ir (exec_loop e cond_inner inner_body fuel)
    //   ≡ Int.le c ((exec_loop …) s_idx)  — DEF-EQ to the outer codomain.
    // hI : I e ≡ Ir e  (hI = bvar(1)).
    let inner_keeps = Expr::apps(
        cst(MIRSEM_LOOP_INVARIANT_RULE),
        [
            ir,
            cond_inner,
            inner_body,
            inner_pres,
            fuel,
            e_ref,
            Expr::bvar(1), // hI : Ir e
        ],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, inner_keeps)))
}

/// The PER-FUNCTION monotone-nested-loop CONCLUSION TYPE — `loopInvariantRuleO`
/// SPECIALIZED at `(I, cond_outer, outer_body(fuel))`, universally quantified over the
/// inner fuel `f`: `∀ (f n : Nat)(e : Env), I e → I (exec_loopO e cond_outer (outer_body
/// f) n)`. (Structurally identical to `nested_loop_conclusion_type`, at the lower-bound
/// invariant.)
pub(super) fn monotone_nested_conclusion_type(mlf: &SemMonotoneNestedLoopFunction) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = mlf.invariant_expr();
    let cond_outer = mlf.cond_outer.to_cond_expr();
    // inside `∀ f ∀ n ∀ e`: e=0, n=1, f=2.
    let i_e = Expr::app(i_expr.clone().lift(3), Expr::bvar(0));
    // under one more arrow: e=1, n=2, f=3.
    let outer_body = mlf.outer_body_list_expr(Expr::bvar(3));
    let looped = exec_loop_o_app(Expr::bvar(1), cond_outer.lift(4), outer_body, Expr::bvar(2));
    let i_loop = Expr::app(i_expr.lift(4), looped);
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    Expr::pi(bd(), cst("Nat"), body_n)
}

/// The PER-FUNCTION monotone-nested-loop PROOF — `λ (f : Nat). loopInvariantRuleO I
/// cond_outer (outer_body f) <outer_pres f>`.
pub(super) fn monotone_nested_proof(mlf: &SemMonotoneNestedLoopFunction) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = mlf.invariant_expr();
    let cond_outer = mlf.cond_outer.to_cond_expr();
    // inside `λ (f : Nat)`: f = bvar(0).
    let outer_body = mlf.outer_body_list_expr(Expr::bvar(0));
    let outer_pres = monotone_outer_preservation_proof(mlf, &Expr::bvar(0));
    let inst = Expr::apps(
        cst(MIRSEM_LOOP_INVARIANT_RULE_O),
        [i_expr.lift(1), cond_outer.lift(1), outer_body, outer_pres],
    );
    Expr::lam(bd(), cst("Nat"), inst)
}

/// Kernel-check the PER-FUNCTION monotone-nested-loop INSTANCE for `mlf`: build `∀ f n e,
/// I e → I (exec_loopO e cond_outer (outer_body f) n)` and the proof `λ f.
/// loopInvariantRuleO I cond_outer (outer_body f) <outer_pres>`, `check_type`, register,
/// audit ⊆ 3. A [`RefinementVerdict::ProvenModulo3`] means the OUTER while-rule,
/// INSTANTIATED at THIS nested loop whose INNER loop INCREMENTS the outer-invariant
/// variable `s`, and fed an OUTER preservation proof that composes the INNER loop's OWN
/// lower-bound invariant, kernel-checks modulo exactly 3.
#[must_use]
pub fn check_monotone_nested_loop_instance(
    mlf: &SemMonotoneNestedLoopFunction,
) -> RefinementVerdict {
    let mut env = match nested_loop_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = monotone_nested_conclusion_type(mlf);
    let proof = monotone_nested_proof(mlf);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "monotone nested loop check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.MirSem.monotoneNestedLoopInstance.partialCorrect");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add monotone nested instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "monotone nested loop axiom residue: {names:?}"
            ))
        }
        None => {
            RefinementVerdict::KernelRejected("monotone nested loop decl not found".to_string())
        }
    }
}

/// Mint a [`MonotoneNestedLoopCertificate`] for `mlf` IF the per-function instance
/// kernel-checks modulo 3. Fail-closed: returns `None` when the OUTER counter IS the
/// accumulator `s_idx` (the outer increment would then also write `s`, but the invariant
/// is about `s` and the outer increment is `i:=i+1` — a counter≡accumulator collision is
/// rejected), or when the inner body does NOT actually keep `s` non-decreasing (then the
/// kernel rejects the preservation ⇒ `None`). A returned certificate is a genuine
/// modulo-3 per-function monotone-nested-loop refinement.
#[must_use]
pub fn monotone_nested_loop_witness(
    mlf: &SemMonotoneNestedLoopFunction,
) -> Option<MonotoneNestedLoopCertificate> {
    // SOUNDNESS GUARD: the outer counter must DIFFER from the accumulator (the outer
    // `Assign(counter, counter+1)` must not be the accumulator update — the accumulator
    // is updated by the INNER loop), and the inner loop must actually WRITE `s_idx` (else
    // it is not the monotone-modifies-outer shape — use the untouched-local certificate).
    if mlf.counter_idx == mlf.s_idx || !mlf.inner_assigns(mlf.s_idx) {
        return None;
    }
    match check_monotone_nested_loop_instance(mlf) {
        RefinementVerdict::ProvenModulo3 => Some(MonotoneNestedLoopCertificate {
            function: mlf.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}
