// Ranking functions and their decrease proofs, plus the `Int`/`Nat` monotonicity
// lemmas the rankings need. Termination is what upgrades a partial loop verdict
// to total correctness, so a loop whose ranking cannot be synthesised stays
// partial rather than being assumed to halt.

use super::*;

// ===========================================================================
// Step 6LT — PER-FUNCTION TOTAL CORRECTNESS (the loop TERMINATION half, WIRED).
//
// `loop_refinement_witness` above instantiates `loopInvariantRule` (PARTIAL
// correctness) per-function. This step ADDS the TERMINATION half: it instantiates
// the general well-founded-ranking termination rule (`loopRankTerminates`) and the
// composed `loopTotalCorrect` theorem at a concrete compiled loop, with a PROVIDED
// ranking `R` and a CONCRETE kernel-checked decrease proof.
//
// HONESTY (critical): the ranking `R` is PROVIDED, not SYNTHESIZED — exactly like
// the invariant is provided, not inferred. We recognize the ONE structured-counter
// shape `while i < n { i = i + 1 }` and supply `R := λ e. Int.toNat (n - i)` (the
// counter's distance to the bound). The DECREASE hypothesis `∀ e, eval_cond e cond =
// true → R (exec e body) < R e` is then a GENUINE kernel proof over Int/Nat
// arithmetic (NOT definitional): from the guard `i < n` we extract `Int.lt i n`
// (`Int.NonNeg (n - (i+1))`) via a hand-built `of_decide_eq_true`, then prove
// `Nat.lt (toNat (n-(i+1))) (toNat (n-i))` using the prelude's constructive Int
// order lemmas (`Int.sub_add_sub_cancel`, `Int.add_one_sub_self`) — both available,
// axiom-free, modulo 3. A WRONG ranking (one that does NOT strictly decrease, e.g.
// `R := λ e. i`) fails to supply a valid decrease proof ⇒ the per-function instance
// is KernelRejected (fail-closed). What this does NOT do: synthesize rankings for
// arbitrary loops (DEFERRED, like invariant inference) or prove termination of any
// loop shape but the recognized increment-toward-a-bound counter.
// ===========================================================================
/// `Int.ofNat 1` in the canonical `Int.ofNat (Nat.succ Nat.zero)` form the prelude's
/// `Int.lt`/`Int.add_one_sub_self`/`Int.sub_add_sub_cancel` all use for the literal 1.
pub(super) fn int_one() -> Expr {
    Expr::app(cst("Int.ofNat"), Expr::app(cst("Nat.succ"), cst("Nat.zero")))
}

/// The TYPE of `countdownGe0`: `∀ (i : Int), Int.lt (Int.ofNat 0) i → Int.le (Int.ofNat 0)
/// (Int.sub i (Int.ofNat 1))` — "if `0 < i` then `0 ≤ i - 1`". The arithmetic core the
/// countdown loop's lower-bound preservation rests on (`i > 0 ⇒ i-1 ≥ 0`).
pub(super) fn countdown_ge0_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `∀ i`: i = 0.
    let lt = Expr::apps(cst("Int.lt"), [int_lit(0), Expr::bvar(0)]);
    // conclusion under one more arrow: i = 1.
    let sub = Expr::apps(cst("Int.sub"), [Expr::bvar(1), int_one()]);
    let le = Expr::apps(cst("Int.le"), [int_lit(0), sub]);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), lt, le))
}

/// The PROOF of `countdownGe0` (see [`countdown_ge0_type`]):
/// `λ (i : Int)(h : Int.lt 0 i). Int.add_le_add_right (Int.add 0 1) i h (Int.neg 1)`.
///
/// `h : Int.lt 0 i` is DEFINITIONALLY `Int.le (Int.add 0 1) i` (`Int.lt a b := Int.le
/// (a+1) b`), so it fits `Int.add_le_add_right`'s `Int.le a b` premise at `a := Int.add 0
/// 1`, `b := i`. The lemma adds `Int.neg 1` on the right of both sides ⇒ `Int.le (Int.add
/// (Int.add 0 1)(Int.neg 1)) (Int.add i (Int.neg 1))`. The LHS reduces to `Int.ofNat 0`
/// (`(0+1)+(-1) = 0`) and the RHS `Int.add i (Int.neg 1)` is DEFINITIONALLY `Int.sub i 1`
/// (`Int.sub a b := Int.add a (Int.neg b)`), so the result is def-eq to the declared
/// `Int.le 0 (Int.sub i 1)`. Constructive: only `Int.add_le_add_right` (modulo 3).
pub(super) fn countdown_ge0_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // under `λ (i : Int) λ (h : Int.lt 0 i)`: h = 0, i = 1.
    let i = || Expr::bvar(1);
    let h = || Expr::bvar(0);
    // a := Int.add 0 1  (= the unfolded `Int.lt 0 i` lhs `0+1`).
    let a = Expr::apps(cst("Int.add"), [int_lit(0), int_one()]);
    let neg_one = Expr::app(cst("Int.neg"), int_one());
    // Int.add_le_add_right (0+1) i h (neg 1) : Int.le ((0+1)+(-1)) (i+(-1)) ≡ Int.le 0 (i-1).
    let body = add_le_add_right(a, i(), h(), neg_one);
    // h binder type `Int.lt 0 i` under `λ i` (before λ h): i = 0.
    let h_ty = Expr::apps(cst("Int.lt"), [int_lit(0), Expr::bvar(0)]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), h_ty, body))
}

/// Register `countdownGe0` (idempotent). Requires the constructive Int-order lemma suite
/// (`Int.add_le_add_right`) already loaded via `init_int_ord_lemmas`.
pub(super) fn register_countdown_ge0(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_COUNTDOWN_GE0);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    env.init_int_ord_lemmas().map_err(|e| format!("init_int_ord_lemmas: {e:?}"))?;
    let ty = countdown_ge0_type();
    let proof = countdown_ge0_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&proof, &ty).map_err(|e| format!("countdownGe0 check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: proof })
        .map_err(|e| format!("add_decl(countdownGe0): {e:?}"))?;
    Ok(())
}

/// The TYPE of `countdownRankDecrease`: `∀ (i : Int), Int.lt (Int.ofNat 0) i →
/// Nat.lt (Int.toNat (Int.sub i (Int.ofNat 1))) (Int.toNat i)` — the countdown ranking
/// `toNat(i)` strictly decreases each `i := i-1` step (while `i > 0`).
// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port
// (`trustir_termination.rs`) — the builder is NAME-INDEPENDENT (prelude constants only),
// so the port reuses it byte-identically under the `Trust.TrustIr.*` registration.
pub(crate) fn countdown_rank_decrease_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lt = Expr::apps(cst("Int.lt"), [int_lit(0), Expr::bvar(0)]);
    // conclusion under one more arrow: i = 1.
    let sub = Expr::apps(cst("Int.sub"), [Expr::bvar(1), int_one()]);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let concl = nat_lt(to_nat(sub), to_nat(Expr::bvar(1)));
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), lt, concl))
}

/// The PROOF of `countdownRankDecrease`:
/// `λ (i)(h : Int.lt 0 i). @Eq.subst Int (λ y. Nat.lt (toNat(i-1)) (toNat y)) (Int.sub i 0) i
///    (Int.add_zero i) (loopRankDecrease 0 i h)`.
///
/// `loopRankDecrease 0 i h : Nat.lt (toNat(Int.sub i (Int.add 0 1))) (toNat(Int.sub i 0))`.
/// `Int.add 0 1` reduces to `Int.ofNat 1` (`Int.add` recurses on its `ofNat 0` first arg), so
/// the FIRST `toNat` arg is already `toNat(i-1)`. The SECOND `toNat(Int.sub i 0)` is NOT
/// def-eq to `toNat i` (`Int.sub i 0 ≡ Int.add i 0`, STUCK for symbolic `i` — `Int.add`
/// recurses on its FIRST arg), so we TRANSPORT it to `toNat i` along `Int.add_zero i :
/// Int.add i 0 = i` (used at the def-eq type `Int.sub i 0 = i`) via `Eq.subst`. Reuses the
/// kernel-checked `loopRankDecrease`; the only added content is the `Int.add_zero` transport.
pub(super) fn countdown_rank_decrease_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // under `λ (i : Int) λ (h : Int.lt 0 i)`: h=0, i=1.
    let i = || Expr::bvar(1);
    let h = || Expr::bvar(0);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let sub = |a: Expr, b: Expr| Expr::apps(cst("Int.sub"), [a, b]);
    let i_minus_1 = sub(i(), int_one());
    let sub_i_0 = sub(i(), int_lit(0));
    // raw := loopRankDecrease 0 i h : Nat.lt (toNat(i-(0+1))) (toNat(i-0)).
    let raw = Expr::apps(cst(MIRSEM_LOOP_RANK_DECREASE), [int_lit(0), i(), h()]);
    // motive := λ (y : Int). Nat.lt (toNat(i-1)) (toNat y)   (i-1 lifted by 1 under `λ y`).
    let motive =
        Expr::lam(bd(), int_ty(), nat_lt(to_nat(i_minus_1.clone().lift(1)), to_nat(Expr::bvar(0))));
    // h0 := Int.add_zero i : Int.add i 0 = i  (used at def-eq type `Int.sub i 0 = i`).
    let h0 = Expr::app(cst("Int.add_zero"), i());
    // @Eq.subst Int motive (Int.sub i 0) i h0 raw : Nat.lt (toNat(i-1)) (toNat i).
    let body = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), motive, sub_i_0, i(), h0, raw],
    );
    let h_ty = Expr::apps(cst("Int.lt"), [int_lit(0), Expr::bvar(0)]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), h_ty, body))
}

/// Register `countdownRankDecrease` (idempotent). Requires `loopRankDecrease` (which
/// `register_loop_rank_decrease` provides) — registers it as a dependency.
pub(super) fn register_countdown_rank_decrease(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_COUNTDOWN_RANK_DECREASE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    register_loop_rank_decrease(env)?; // provides loopRankDecrease + Int-order lemmas.
    let ty = countdown_rank_decrease_type();
    let proof = countdown_rank_decrease_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&proof, &ty)
            .map_err(|e| format!("countdownRankDecrease check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: proof })
        .map_err(|e| format!("add_decl(countdownRankDecrease): {e:?}"))?;
    Ok(())
}

/// The CONCRETE proof term `strideSelfLe : Int.le x (Int.add x (int_lit k))` — "`x ≤ x+k`"
/// for a fixed positive stride `k`, built INLINE (no env decl) by transporting:
/// ```text
/// raw  := Int.add_le_add_left (ofNat 0) (ofNat k) (Int.ofNat_zero_le k) x
///         : Int.le (Int.add x (ofNat 0)) (Int.add x (ofNat k))
/// h0   := Int.add_zero x : Eq Int (Int.add x (ofNat 0)) x
/// out  := @Eq.subst Int (λ y. Int.le y (Int.add x (ofNat k))) (Int.add x (ofNat 0)) x h0 raw
///         : Int.le x (Int.add x (ofNat k))
/// ```
/// The transport REWRITES the stuck LHS `Int.add x (ofNat 0)` to `x` (it is NOT def-eq for a
/// SYMBOLIC `x`, because `Int.add` recurses on its FIRST argument). The result has the EXACT
/// codomain shape `Int.le (e i) ((e i)+k)` the stride preservation needs. Requires `k ≥ 1`;
/// `Int.ofNat_zero_le` only applies to the `ofNat`-shaped stride literal.
pub(super) fn stride_self_le_term(k: i128, x: Expr) -> Expr {
    debug_assert!(k >= 1, "stride must be a positive constant");
    let bd = || BinderData::from(BinderInfo::Default);
    let k_nat = Expr::nat_lit(u64::try_from(k).unwrap_or(0));
    let zero_le_k = Expr::app(cst("Int.ofNat_zero_le"), k_nat);
    let x_plus_0 = Expr::apps(cst("Int.add"), [x.clone(), int_lit(0)]);
    let x_plus_k = Expr::apps(cst("Int.add"), [x.clone(), int_lit(k)]);
    // raw : Int.le (x+0) (x+k).
    let raw =
        Expr::apps(cst("Int.add_le_add_left"), [int_lit(0), int_lit(k), zero_le_k, x.clone()]);
    // h0 : Eq Int (Int.add x 0) x.
    let h0 = Expr::app(cst("Int.add_zero"), x.clone());
    // motive : λ (y : Int). Int.le y (x+k)   (x+k lifted by 1 under `λ y`).
    let motive = Expr::lam(
        bd(),
        int_ty(),
        Expr::apps(cst("Int.le"), [Expr::bvar(0), x_plus_k.clone().lift(1)]),
    );
    // @Eq.subst Int motive (x+0) x h0 raw : Int.le x (x+k).
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), motive, x_plus_0, x, h0, raw],
    )
}

/// `@Eq Int a b`.
pub(super) fn eq_int(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [int_ty(), a, b],
    )
}

/// `@congrArg α β a b f h : @Eq β (f a) (f b)`.
pub(super) fn congr_arg(alpha: Expr, beta: Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ),
        [alpha, beta, a, b, f, h],
    )
}

/// `@Eq.symm α a b h : @Eq α b a` (α : Sort 1).
pub(super) fn eq_symm_int(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
        [int_ty(), a, b, h],
    )
}

/// `@Eq.trans α a b c hab hbc : @Eq α a c` (α : Sort 1).
pub(super) fn eq_trans_int(a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(Level::zero())]),
        [int_ty(), a, b, c, hab, hbc],
    )
}

/// The TYPE of `loopRankDecrease`: `∀ (a b : Int), Int.lt a b → Nat.lt (Int.toNat (Int.sub
/// b (Int.add a 1))) (Int.toNat (Int.sub b a))`.
// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn loop_rank_decrease_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `∀ a ∀ b`: b=0, a=1.
    let a = Expr::bvar(1);
    let b = Expr::bvar(0);
    let lt_ab = Expr::apps(cst("Int.lt"), [a.clone(), b.clone()]);
    // conclusion under one more arrow (`Int.lt a b →`): b=1, a=2.
    let a2 = Expr::bvar(2);
    let b2 = Expr::bvar(1);
    let sub_b_a1 = Expr::apps(
        cst("Int.sub"),
        [b2.clone(), Expr::apps(cst("Int.add"), [a2.clone(), int_one()])],
    );
    let sub_b_a = Expr::apps(cst("Int.sub"), [b2, a2]);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let concl = nat_lt(to_nat(sub_b_a1), to_nat(sub_b_a));
    let after_h = Expr::pi(bd(), lt_ab, concl);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), after_h))
}

/// The PROOF of `loopRankDecrease` (see [`loop_rank_decrease_type`]).
// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn loop_rank_decrease_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Under `λ (a : Int) λ (b : Int) λ (h : Int.lt a b)`: h=0, b=1, a=2.
    // `h : Int.lt a b ≡ Int.NonNeg (Int.sub b (Int.add a 1))`.
    let a = || Expr::bvar(2);
    let b = || Expr::bvar(1);
    let h = || Expr::bvar(0);
    let a1 = || Expr::apps(cst("Int.add"), [a(), int_one()]);
    let sub_b_a1 = || Expr::apps(cst("Int.sub"), [b(), a1()]);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);

    // --- `Int.NonNeg.rec` motive : λ (x : Int)(_ : Int.NonNeg x).
    //        Eq Int (Int.add x (Int.ofNat 1)) (Int.sub b a)            -- bridging eq
    //        → Nat.lt (Int.toNat x) (Int.toNat (Int.sub b a)) ---
    // The bridging equation `x + 1 = b - a` is taken as a HYPOTHESIS so the minor (at
    // `x := Int.ofNat k`) can DISCHARGE it: `Int.add (ofNat k)(ofNat 1) ≡ ofNat (succ k)`
    // REDUCES, so the hyp there is `ofNat (succ k) = b - a` — exactly the fact the
    // termination step needs. After the recursor the motive is INSTANTIATED at the real
    // index `x := Int.sub b (a+1)` and APPLIED to the proved bridge `e_succ` (below).
    //   under `λ x λ hx`: x=1, hx=0, h=2, b=3, a=4.
    let rec_motive = {
        let nonneg_x = Expr::app(cst("Int.NonNeg"), Expr::bvar(0)); // under `λ x`: x=0
        // dom `Eq Int (Int.add x 1) (Int.sub b a)`  under `λ x λ hx`: x=1, b=3, a=4.
        let dom = eq_int(
            Expr::apps(cst("Int.add"), [Expr::bvar(1), int_one()]),
            Expr::apps(cst("Int.sub"), [Expr::bvar(3), Expr::bvar(4)]),
        );
        // cod `Nat.lt (toNat x) (toNat (sub b a))` under `λ x λ hx (bridge →)`: x=2, b=4, a=5.
        let cod = nat_lt(
            to_nat(Expr::bvar(2)),
            to_nat(Expr::apps(cst("Int.sub"), [Expr::bvar(4), Expr::bvar(5)])),
        );
        let arrow = Expr::pi(bd(), dom, cod);
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), nonneg_x, arrow))
    };

    // --- `Int.NonNeg.rec` minor : λ (k : Nat) λ (heq : Int.add (ofNat k) 1 = b - a).
    //         close the branch (x ≡ ofNat k) ---
    //   under `λ k λ heq` (on top of a,b,h): heq=0, k=1, h=2, b=3, a=4.
    // Here `heq : @Eq Int (Int.add (Int.ofNat k) (Int.ofNat 1)) (Int.sub b a)` and the LHS
    // REDUCES (both operands are constructors) to `Int.ofNat (Nat.succ k)`, so `heq` is
    // def-eq `@Eq Int (Int.ofNat (Nat.succ k)) (Int.sub b a)` — the termination fact. Goal:
    //   Nat.lt (Int.toNat (Int.ofNat k)) (Int.toNat (Int.sub b a)) ≡ Nat.lt k (toNat (sub b a)).
    let rec_minor = {
        // refs under `λ k λ heq`: heq=0, k=1, h=2, b=3, a=4.
        let a = || Expr::bvar(4);
        let b = || Expr::bvar(3);
        let k = || Expr::bvar(1);
        let heq = || Expr::bvar(0);
        let sub_b_a = || Expr::apps(cst("Int.sub"), [b(), a()]);
        let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
        let succ_k = || Expr::app(cst("Nat.succ"), k());
        let ofnat_succ_k = || Expr::app(cst("Int.ofNat"), succ_k());

        // e_succ_nat : @Eq Nat (Int.toNat (Int.ofNat (Nat.succ k))) (Int.toNat (Int.sub b a))
        //            ≡ @Eq Nat (Nat.succ k) (Int.toNat (Int.sub b a))   (toNat reduces).
        //   = congrArg Int Nat (ofNat (succ k)) (sub b a) Int.toNat heq.
        let e_succ_nat =
            congr_arg(int_ty(), cst("Nat"), ofnat_succ_k(), sub_b_a(), cst("Int.toNat"), heq());
        // Goal: Nat.lt (toNat (ofNat k)) (toNat (sub b a)) ≡ Nat.le (succ k) (toNat (sub b a)).
        // Transport @Nat.le.refl (succ k) : Nat.le (succ k) (succ k) along e_succ_nat.
        let le_refl = Expr::app(Expr::const_(Name::from_string("Nat.le.refl"), vec![]), succ_k());
        let motive_m = Expr::lam(
            bd(),
            cst("Nat"),
            // under `λ m` (on top of heq,k,h,b,a): m=0, k=2.
            Expr::apps(cst("Nat.le"), [Expr::app(cst("Nat.succ"), Expr::bvar(2)), Expr::bvar(0)]),
        );
        let eq_subst = Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
            [cst("Nat"), motive_m, succ_k(), to_nat(sub_b_a()), e_succ_nat, le_refl],
        );
        // heq binder type `Int.add (ofNat k) 1 = b - a` under `λ k` (before λ heq): k=0, b=2, a=3.
        let heq_ty = eq_int(
            Expr::apps(cst("Int.add"), [Expr::app(cst("Int.ofNat"), Expr::bvar(0)), int_one()]),
            Expr::apps(cst("Int.sub"), [Expr::bvar(2), Expr::bvar(3)]),
        );
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), heq_ty, eq_subst))
    };

    // The proved BRIDGE `e_succ : @Eq Int (Int.add (Int.sub b (a+1)) (Int.ofNat 1)) (Int.sub
    // b a)` — what the recursor result (motive at the real index `x := sub b (a+1)`) is
    // applied to. Built at the OUTER `λ a λ b λ h` depth (a=2,b=1,h=0).
    //   e_cancel : Int.sub_add_sub_cancel a (a+1) b : (b-(a+1)) + ((a+1)-a) = b-a.
    //   e_one    : Int.add_one_sub_self a : (a+1)-a = 1.
    let e_succ = {
        let a = || Expr::bvar(2);
        let b = || Expr::bvar(1);
        let a1 = || Expr::apps(cst("Int.add"), [a(), int_one()]);
        let sub_b_a1 = || Expr::apps(cst("Int.sub"), [b(), a1()]);
        let sub_b_a = || Expr::apps(cst("Int.sub"), [b(), a()]);
        let sub_a1_a = || Expr::apps(cst("Int.sub"), [a1(), a()]);
        let e_cancel = Expr::apps(cst("Int.sub_add_sub_cancel"), [a(), a1(), b()]);
        let e_one = Expr::apps(cst("Int.add_one_sub_self"), [a()]);
        // add_fn = λ t. Int.add (sub b (a+1)) t   (under `λ t` on top of a,b,h: t=0,h=1,b=2,a=3)
        let add_fn = Expr::lam(
            bd(),
            int_ty(),
            Expr::apps(
                cst("Int.add"),
                [
                    Expr::apps(
                        cst("Int.sub"),
                        [
                            Expr::bvar(2),                                          // b
                            Expr::apps(cst("Int.add"), [Expr::bvar(3), int_one()]), // a+1
                        ],
                    ),
                    Expr::bvar(0), // t
                ],
            ),
        );
        let e_one_cong = congr_arg(int_ty(), int_ty(), sub_a1_a(), int_one(), add_fn, e_one);
        let add_chain = || Expr::apps(cst("Int.add"), [sub_b_a1(), sub_a1_a()]);
        let add_one = || Expr::apps(cst("Int.add"), [sub_b_a1(), int_one()]);
        // Eq.trans (Eq.symm e_one_cong) e_cancel : (b-(a+1)) + 1 = b-a.
        eq_trans_int(
            add_one(),
            add_chain(),
            sub_b_a(),
            eq_symm_int(add_chain(), add_one(), e_one_cong),
            e_cancel,
        )
    };

    // @Int.NonNeg.rec motive minor (Int.sub b (a+1)) h : motive (sub b (a+1)) h
    //   ≡ (Int.add (sub b (a+1)) 1 = b-a) → Nat.lt (toNat (sub b (a+1))) (toNat (sub b a)).
    // APPLY to the bridge `e_succ` ⇒ the goal `Nat.lt (toNat (sub b (a+1))) (toNat (sub b a))`.
    let rec_app = Expr::app(
        Expr::apps(
            Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            [rec_motive, rec_minor, sub_b_a1(), h()],
        ),
        e_succ,
    );
    let _ = to_nat;
    // The `h` binder TYPE `Int.lt a b` is evaluated under `λ a λ b` (BEFORE `λ h`), so
    // there `a = bvar(1)`, `b = bvar(0)` — NOT the `a()/b()` indices (those hold INSIDE
    // the proof body, under all three binders).
    let h_binder_ty = Expr::apps(cst("Int.lt"), [Expr::bvar(1), Expr::bvar(0)]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), h_binder_ty, rec_app)))
}

/// Register the prelude Int-order lemmas the per-function decrease proof needs
/// (`Int.sub_add_sub_cancel`, `Int.add_one_sub_self`, …) and then `loopRankDecrease`
/// itself. Idempotent. Both prelude registrations are constructive (axiom closure
/// ⊆ the 3 foundational axioms); see the probe in this module's tests.
pub(super) fn register_loop_rank_decrease(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_LOOP_RANK_DECREASE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    // The constructive Int-order lemma suite (registers `Int.sub_add_sub_cancel`,
    // `Int.add_one_sub_self`, `Int.add_comm/assoc/zero`, `Int.NonNeg.*`, … all modulo 3).
    env.init_int_ord_lemmas().map_err(|e| format!("init_int_ord_lemmas: {e:?}"))?;
    let ty = loop_rank_decrease_type();
    let proof = loop_rank_decrease_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&proof, &ty).map_err(|e| format!("loopRankDecrease check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: proof })
        .map_err(|e| format!("add_decl(loopRankDecrease): {e:?}"))?;
    Ok(())
}

// ===========================================================================
// `toNatMono` — `Int.le a b → Nat.le (Int.toNat a) (Int.toNat b)` — and the two
// constructive sub-lemmas it rests on (`ofNat`-cast both directions). Each is a
// kernel-checked `Declaration::Theorem` resting on ONLY the 3 foundational axioms.
// ===========================================================================
/// `@Int.ofNat n`.
pub(super) fn int_ofnat(n: Expr) -> Expr {
    Expr::app(cst("Int.ofNat"), n)
}

/// `@Int.le a b`.
pub(super) fn int_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Int.le"), [a, b])
}

// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn ofnat_le_ofnat_of_le_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `∀ m ∀ p`: p=0, m=1.
    let h_ty = nat_le(Expr::bvar(1), Expr::bvar(0));
    // conclusion under `Nat.le m p →`: p=1, m=2.
    let concl = int_le(int_ofnat(Expr::bvar(2)), int_ofnat(Expr::bvar(1)));
    let after_h = Expr::pi(bd(), h_ty, concl);
    Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), cst("Nat"), after_h))
}

// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn ofnat_le_ofnat_of_le_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Under `λ (m : Nat) λ (p : Nat) λ (h : Nat.le m p)`: h=0, p=1, m=2.
    let m = || Expr::bvar(2);
    let of_m = || int_ofnat(m());

    // motive : λ (t : Nat) λ (_ : Nat.le m t). Int.le (ofNat m) (ofNat t)
    //   under `λ t λ ht` (on top of h,p,m): ht=0, t=1, h=2, p=3, m=4.
    let motive = {
        let le_mt = nat_le(Expr::bvar(3), Expr::bvar(0)); // under `λ t`: t=0, m=3.
        let body = int_le(int_ofnat(Expr::bvar(4)), int_ofnat(Expr::bvar(1))); // under `λ t λ ht`: m=4, t=1.
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), le_mt, body))
    };

    // refl_case : Int.le (ofNat m) (ofNat m) := Int.le_refl (ofNat m).
    let refl_case = Expr::app(cst("Int.le_refl"), of_m());

    // step_case : λ (t : Nat) λ (ht : Nat.le m t) λ (ih : Int.le (ofNat m)(ofNat t)).
    //   Int.le_trans (ofNat m)(ofNat t)(ofNat (succ t)) ih (Int.le_self_add_one (ofNat t))
    //   under `λ t λ ht λ ih` (on top of h,p,m): ih=0, ht=1, t=2, h=3, p=4, m=5.
    let step_case = {
        let m_in = || int_ofnat(Expr::bvar(5)); // m
        let of_t = || int_ofnat(Expr::bvar(2)); // t
        let of_succ_t = || int_ofnat(Expr::app(cst("Nat.succ"), Expr::bvar(2)));
        let ih = || Expr::bvar(0);
        let self_add_one = Expr::app(cst("Int.le_self_add_one"), of_t());
        let body =
            Expr::apps(cst("Int.le_trans"), [m_in(), of_t(), of_succ_t(), ih(), self_add_one]);
        // binder types: ht : Nat.le m t (under `λ t`: t=0, m=3); ih : Int.le (ofNat m)(ofNat t)
        // (under `λ t λ ht`: t=1, m=4).
        let ht_ty = nat_le(Expr::bvar(3), Expr::bvar(0));
        let ih_ty = int_le(int_ofnat(Expr::bvar(4)), int_ofnat(Expr::bvar(1)));
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), ht_ty, Expr::lam(bd(), ih_ty, body)))
    };

    // @Nat.le.rec m motive refl_case step_case p h : Int.le (ofNat m)(ofNat p).
    let p = || Expr::bvar(1);
    let h = || Expr::bvar(0);
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
        [m(), motive, refl_case, step_case, p(), h()],
    );
    // binder types under outer lambdas: h : Nat.le m p (under `λ m λ p`: p=0, m=1).
    let h_binder_ty = nat_le(Expr::bvar(1), Expr::bvar(0));
    Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), h_binder_ty, rec_app)))
}

// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn le_of_ofnat_le_ofnat_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `∀ m ∀ p`: p=0, m=1.
    let h_ty = int_le(int_ofnat(Expr::bvar(1)), int_ofnat(Expr::bvar(0)));
    // conclusion under `Int.le (ofNat m)(ofNat p) →`: p=1, m=2.
    let concl = nat_le(Expr::bvar(2), Expr::bvar(1));
    let after_h = Expr::pi(bd(), h_ty, concl);
    Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), cst("Nat"), after_h))
}

pub(super) fn le_of_ofnat_le_ofnat_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Under `λ (m : Nat) λ (p : Nat) λ (h : Int.le (ofNat m)(ofNat p))`: h=0, p=1, m=2.
    // (`h` itself is consumed only inside the `inr` minor, where it is re-derived at the
    // shifted depth; the outer body never references it directly.)
    let m = || Expr::bvar(2);
    let p = || Expr::bvar(1);
    let succ = |x: Expr| Expr::app(cst("Nat.succ"), x);

    // disc := Nat.le_or_lt m p : Or (Nat.le m p) (Nat.le (succ p) m).
    let lhs_prop = || nat_le(m(), p());
    let rhs_prop = || nat_le(succ(p()), m());
    let disc = Expr::apps(cst("Nat.le_or_lt"), [m(), p()]);

    // motive : λ (_ : Or (Nat.le m p)(Nat.le (succ p) m)). Nat.le m p  (constant).
    //   under `λ _or` (on top of h,p,m): m=3, p=2.
    let or_ty = Expr::apps(cst("Or"), [lhs_prop(), rhs_prop()]);
    let motive = Expr::lam(bd(), or_ty.clone(), nat_le(Expr::bvar(3), Expr::bvar(2)));

    // inl_minor : λ (hle : Nat.le m p). hle.
    //   under `λ hle` (on top of h,p,m): hle=0.
    let inl_minor = {
        let hle_ty = nat_le(m(), p()); // under outer `λ m λ p λ h`: m=2,p=1; the Or.rec minor
        // binder type is evaluated at the SAME depth as the Or.rec application, i.e. h/p/m
        // visible as 0/1/2; under `λ hle` the body sees hle=0.
        Expr::lam(bd(), hle_ty, Expr::bvar(0))
    };

    // inr_minor : λ (hlt : Nat.le (succ p) m).
    //   fwd  := ofNatLeOfNatOfLe (succ p) m hlt : Int.le (ofNat (succ p)) (ofNat m)
    //   chain:= Int.le_trans (ofNat (succ p)) (ofNat m) (ofNat p) fwd h
    //           : Int.le (ofNat (succ p)) (ofNat p) ≡ Int.lt (ofNat p)(ofNat p)
    //   bad  := Int.lt_irrefl (ofNat p) chain : False     -- Int.lt_irrefl gives `Not (lt p p)`
    //   @False.elim (Nat.le m p) bad : Nat.le m p
    //   under `λ hlt` (on top of h,p,m): hlt=0, h=1, p=2, m=3.
    let inr_minor = {
        let m = || Expr::bvar(3);
        let p = || Expr::bvar(2);
        let h = || Expr::bvar(1);
        let hlt = || Expr::bvar(0);
        let of_succ_p = || int_ofnat(succ(p()));
        let of_m = || int_ofnat(m());
        let of_p = || int_ofnat(p());
        let fwd = Expr::apps(cst(MIRSEM_OFNAT_LE_OFNAT_OF_LE), [succ(p()), m(), hlt()]);
        let chain = Expr::apps(cst("Int.le_trans"), [of_succ_p(), of_m(), of_p(), fwd, h()]);
        // Int.lt_irrefl (ofNat p) : Not (Int.lt (ofNat p)(ofNat p)) ≡ Int.lt (ofNat p)(ofNat p) → False.
        // chain : Int.le (ofNat (succ p))(ofNat p) ≡ Int.lt (ofNat p)(ofNat p)  (def-eq).
        let bad = Expr::app(Expr::app(cst("Int.lt_irrefl"), of_p()), chain);
        let false_elim = Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [nat_le(m(), p()), bad],
        );
        // hlt binder type `Nat.le (succ p) m` is evaluated BEFORE `λ hlt`, at depth 3:
        // p=bvar(1), m=bvar(2).
        let hlt_ty = nat_le(succ(Expr::bvar(1)), Expr::bvar(2));
        Expr::lam(bd(), hlt_ty, false_elim)
    };

    // @Or.rec (Nat.le m p) (Nat.le (succ p) m) motive inl_minor inr_minor disc : Nat.le m p.
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Or.rec"), vec![]),
        [lhs_prop(), rhs_prop(), motive, inl_minor, inr_minor, disc],
    );
    let h_binder_ty = int_le(int_ofnat(Expr::bvar(1)), int_ofnat(Expr::bvar(0)));
    Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), h_binder_ty, rec_app)))
}

/// `∀ (a b : Int), Int.le a b → Nat.le (Int.toNat a) (Int.toNat b)`.
// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn to_nat_mono_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    // inside `∀ a ∀ b`: b=0, a=1.
    let h_ty = int_le(Expr::bvar(1), Expr::bvar(0));
    // conclusion under `Int.le a b →`: b=1, a=2.
    let concl = nat_le(to_nat(Expr::bvar(2)), to_nat(Expr::bvar(1)));
    let after_h = Expr::pi(bd(), h_ty, concl);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), after_h))
}

/// Proof of `toNatMono`. Outer `@Int.rec.{0}` case-split on `a`:
/// - `a = negSucc m`: `toNat a ≡ Nat.zero`, goal `Nat.le 0 (toNat b)` = `Nat.zero_le`.
/// - `a = ofNat m`: `toNat a ≡ m`. Inner `@Int.rec.{0}` on `b`:
///   - `b = ofNat p`: goal `Int.le (ofNat m)(ofNat p) → Nat.le m p` = `leOfOfNatLeOfNat m p`.
///   - `b = negSucc q`: `Int.le (ofNat m)(negSucc q)` is uninhabitable. `toNat b ≡ 0`,
///     goal `Nat.le m 0`. The hypothesis `Int.le (ofNat m)(negSucc q) ≡ NonNeg (sub
///     (negSucc q)(ofNat m))` is eliminated by `@Int.NonNeg.rec`: its only minor is at
///     index `ofNat n`, but the bridge equation `ofNat n = sub (negSucc q)(ofNat m)`
///     forced through the motive is discharged to `False` (the difference reduces to a
///     `negSucc`, never an `ofNat`), via `Int.lt_irrefl`-style — but more simply the WHOLE
///     `negSucc q` arm reuses `leOfOfNatLeOfNat` only on the `ofNat` index, so here we
///     close it directly through the `NonNeg.rec` False bridge built in `tonat_vacuous_term`.
pub(super) fn to_nat_mono_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let negsucc = |x: Expr| Expr::app(cst("Int.negSucc"), x);

    // Outer motive Ma := λ (a : Int). Int.le a b → Nat.le (toNat a)(toNat b)
    //   ...but `b` is the SECOND outer binder, BELOW the `λ a` we are recursing on inside the
    // proof body. We recurse on `a` FIRST. To keep `b` in scope, the recursion happens UNDER
    // `λ a λ b`. Under `λ (a : Int) λ (b : Int)`: b=0, a=1. The Int.rec target is `a`.
    //   Ma := λ (x : Int). Int.le x b → Nat.le (toNat x)(toNat b)   (b lifted by 1 under λ x).
    let outer_motive = {
        // under `λ x` (on top of b,a): x=0, b=1.
        let dom = int_le(Expr::bvar(0), Expr::bvar(1));
        // cod is UNDER the Pi's (anonymous) domain binder: that binder=0, x=1, b=2.
        let cod = nat_le(to_nat(Expr::bvar(1)), to_nat(Expr::bvar(2)));
        Expr::lam(bd(), int_ty(), Expr::pi(bd(), dom, cod))
    };

    // ofNat minor : λ (m : Nat). Int.le (ofNat m) b → Nat.le m (toNat b)
    //   (toNat (ofNat m) ≡ m). Inner `@Int.rec.{0}` on `b`.
    //   under `λ m` (on top of b,a): m=0, b=1, a=2.
    let ofnat_minor = {
        // Inner recursion on `b`. We are under `λ m λ (hle : Int.le (ofNat m) b)`? No — the
        // minor's RESULT TYPE is `motive (ofNat m)` = `Int.le (ofNat m) b → Nat.le m (toNat b)`,
        // an arrow. So the minor is `λ m. (the arrow)`; build the arrow's inhabitant as
        // `λ (hle : Int.le (ofNat m) b). <Nat.le m (toNat b)>` by inner Int.rec on b.
        //   under `λ m λ hle` (on top of b,a): hle=0, m=1, b=2, a=3.
        let m = || Expr::bvar(1);
        let hle = || Expr::bvar(0);

        // Inner motive Mb := λ (y : Int). Int.le (ofNat m) y → Nat.le m (toNat y)
        //   But here `b` is being recursed; the inner Int.rec target is `b`. The inner motive
        //   must abstract the value we case on, which is `b`. Its result also must yield the
        //   goal `Nat.le m (toNat b)` from `hle : Int.le (ofNat m) b`. We instead structure the
        //   inner recursion to PRODUCE `Nat.le m (toNat b)` directly given the discriminator on
        //   `b`, carrying `hle` via an arrow in the inner motive.
        //   Mb := λ (y : Int). Int.le (ofNat m) y → Nat.le m (toNat y)
        //   under `λ y` (on top of hle,m,b,a): y=0, m=2.
        let inner_motive = {
            let dom = int_le(int_ofnat(Expr::bvar(2)), Expr::bvar(0)); // under λ y: m=2, y=0.
            // cod is UNDER the Pi's (anonymous) domain binder: that binder=0, y=1, m=3.
            let cod = nat_le(Expr::bvar(3), to_nat(Expr::bvar(1)));
            Expr::lam(bd(), int_ty(), Expr::pi(bd(), dom, cod))
        };

        // inner ofNat minor : λ (p : Nat). Int.le (ofNat m)(ofNat p) → Nat.le m p
        //   = leOfOfNatLeOfNat m p   (toNat (ofNat p) ≡ p).
        //   under `λ p` (on top of hle,m,b,a): p=0, m=2.
        let inner_ofnat_minor = {
            // leOfOfNatLeOfNat m p : Int.le (ofNat m)(ofNat p) → Nat.le m p.
            Expr::lam(
                bd(),
                cst("Nat"),
                Expr::apps(cst(MIRSEM_LE_OF_OFNAT_LE_OFNAT), [Expr::bvar(2), Expr::bvar(0)]),
            )
        };

        // inner negSucc minor : λ (q : Nat). Int.le (ofNat m)(negSucc q) → Nat.le m (toNat (negSucc q))
        //   ≡ Int.le (ofNat m)(negSucc q) → Nat.le m Nat.zero.   VACUOUS.
        //   under `λ q` (on top of hle,m,b,a): q=0, m=2.
        //   Build the arrow inhabitant `λ (hbad : Int.le (ofNat m)(negSucc q)). <Nat.le m 0>`.
        //   `hbad ≡ NonNeg (sub (negSucc q)(ofNat m))`. Eliminate via @Int.NonNeg.rec with an
        //   equation-carrying motive `λ x _. Eq Int x (sub (negSucc q)(ofNat m)) → Nat.le m 0`.
        //   At the only minor `x := ofNat n`, the bridge `heq : ofNat n = sub (negSucc q)(ofNat m)`
        //   is impossible: `sub (negSucc q)(ofNat m)` reduces to a `negSucc`. We discharge it to
        //   `False` via `Int.noConfusion`-free path: transport `Int.le_refl`/`lt_irrefl`? Simpler:
        //   build `bad : Int.lt (sub (negSucc q)(ofNat m)) (ofNat 0)` is hard. Use the
        //   `ofNat_le_negSucc_false` reasoning encoded directly below in `tonat_vacuous_term`.
        let inner_negsucc_minor = tonat_vacuous_term();

        // @Int.rec.{0} inner_motive inner_ofnat_minor inner_negsucc_minor b : Mb b
        //   = (Int.le (ofNat m) b → Nat.le m (toNat b)).  Apply to hle.
        let inner_rec = Expr::apps(
            Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            [inner_motive, inner_ofnat_minor, inner_negsucc_minor, Expr::bvar(2)],
        );
        let applied = Expr::app(inner_rec, hle());
        let _ = m;
        // hle binder type `Int.le (ofNat m) b` under `λ m` (before λ hle): m=0, b=1.
        let hle_ty = int_le(int_ofnat(Expr::bvar(0)), Expr::bvar(1));
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), hle_ty, applied))
    };

    // negSucc minor : λ (m : Nat). Int.le (negSucc m) b → Nat.le (toNat (negSucc m)) (toNat b)
    //   ≡ Int.le (negSucc m) b → Nat.le Nat.zero (toNat b).  Close with `Nat.zero_le`.
    //   under `λ m` (on top of b,a): m=0, b=1, a=2.
    let negsucc_minor = {
        // λ (m : Nat) λ (_ : Int.le (negSucc m) b). Nat.zero_le (toNat b)
        //   under `λ m λ _h` (on top of b,a): _h=0, m=1, b=2, a=3.
        let zero_le = Expr::app(cst("Nat.zero_le"), to_nat(Expr::bvar(2)));
        let h_ty = int_le(negsucc(Expr::bvar(0)), Expr::bvar(1)); // under λ m: m=0, b=1.
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), h_ty, zero_le))
    };

    // @Int.rec.{0} outer_motive ofnat_minor negsucc_minor a : Ma a
    //   = (Int.le a b → Nat.le (toNat a)(toNat b)).
    let outer_rec = Expr::apps(
        Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
        [outer_motive, ofnat_minor, negsucc_minor, Expr::bvar(1)],
    );
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), outer_rec))
}

/// The vacuous-branch term for `toNatMono`'s `b = negSucc q` arm. Built as the inner `Int.rec`
/// `negSucc` minor `λ (q : Nat). (Int.le (ofNat m)(negSucc q) → Nat.le m Nat.zero)` (the minor's
/// RESULT TYPE is `inner_motive (negSucc q)`, an arrow). At the construction depth (inside the
/// `ofnat_minor`'s `λ m λ hle`, then the inner `Int.rec`'s `λ q`): q=0, hle=1, m=2, b=3, a=4.
pub(super) fn tonat_vacuous_term() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // `λ (q : Nat). <arrow at q=0, m=2>`.
    Expr::lam(bd(), cst("Nat"), tonat_vacuous_arrow(Expr::bvar(2), Expr::bvar(0)))
}

/// The arrow inhabitant `Int.le (ofNat m)(negSucc q) → Nat.le m Nat.zero`, given Exprs `m`, `q`
/// valid JUST BELOW the `λ q` (before `λ hbad`). Refutes the hypothesis:
/// ```text
/// h1   := ofNatLeOfNatOfLe 0 m (Nat.zero_le m) : Int.le (ofNat 0) (ofNat m)
/// h2   := Int.le_trans (ofNat 0)(ofNat m)(negSucc q) h1 hbad : Int.le (ofNat 0)(negSucc q)
///         ≡ Int.NonNeg (Int.sub (negSucc q)(ofNat 0)) ≡ Int.NonNeg (Int.subNatNat 0 (succ q))
/// e    := Int.subNatNat_zero_succ q : Int.subNatNat 0 (succ q) = Int.negSucc q
/// nn   := @Eq.subst Int (λ x. Int.NonNeg x) (subNatNat 0 (succ q)) (negSucc q) e h2
///         : Int.NonNeg (negSucc q)
/// bad  := negSuccNotNonNeg q nn : False
/// out  := @False.elim (Nat.le m 0) bad : Nat.le m 0
/// ```
pub(super) fn tonat_vacuous_arrow(m: Expr, q: Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let negsucc = |x: Expr| Expr::app(cst("Int.negSucc"), x);
    let subnatnat = |a: Expr, b: Expr| Expr::apps(cst("Int.subNatNat"), [a, b]);
    let succ = |x: Expr| Expr::app(cst("Nat.succ"), x);
    // Under `λ hbad`: hbad=0, m/q lifted by 1.
    let m1 = || m.clone().lift(1);
    let q1 = || q.clone().lift(1);

    // h1 : Int.le (ofNat 0)(ofNat m).
    let h1 = Expr::apps(
        cst(MIRSEM_OFNAT_LE_OFNAT_OF_LE),
        [cst("Nat.zero"), m1(), Expr::app(cst("Nat.zero_le"), m1())],
    );
    // h2 : Int.le (ofNat 0)(negSucc q)  (≡ NonNeg (subNatNat 0 (succ q))).
    let h2 = Expr::apps(
        cst("Int.le_trans"),
        [
            int_ofnat(cst("Nat.zero")),
            int_ofnat(m1()),
            negsucc(q1()),
            h1,
            Expr::bvar(0), // hbad
        ],
    );
    // e : Int.subNatNat 0 (succ q) = Int.negSucc q.
    let e = Expr::app(cst("Int.subNatNat_zero_succ"), q1());
    // nn : Int.NonNeg (negSucc q)  := Eq.subst (λ x. NonNeg x) (subNatNat 0 (succ q)) (negSucc q) e h2.
    let nonneg_motive = Expr::lam(bd(), int_ty(), Expr::app(cst("Int.NonNeg"), Expr::bvar(0)));
    let nn = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), nonneg_motive, subnatnat(cst("Nat.zero"), succ(q1())), negsucc(q1()), e, h2],
    );
    // bad : False := negSuccNotNonNeg q nn.
    let bad = Expr::apps(cst(MIRSEM_NEGSUCC_NOT_NONNEG), [q1(), nn]);
    // out : Nat.le m 0 := @False.elim (Nat.le m 0) bad.
    let out = Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [nat_le(m1(), cst("Nat.zero")), bad],
    );
    // hbad binder type `Int.le (ofNat m)(negSucc q)` at depth BEFORE λ hbad (m,q unlifted).
    let hbad_ty = int_le(int_ofnat(m), negsucc(q));
    Expr::lam(bd(), hbad_ty, out)
}

// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn negsucc_not_nonneg_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let negsucc = |x: Expr| Expr::app(cst("Int.negSucc"), x);
    // inside `∀ q`: q=0.
    let h_ty = Expr::app(cst("Int.NonNeg"), negsucc(Expr::bvar(0)));
    let concl = cst("False");
    let after_h = Expr::pi(bd(), h_ty, concl);
    Expr::pi(bd(), cst("Nat"), after_h)
}

// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn negsucc_not_nonneg_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let negsucc = |x: Expr| Expr::app(cst("Int.negSucc"), x);
    // Under `λ (q : Nat) λ (h : Int.NonNeg (negSucc q))`: h=0, q=1.
    let q = || Expr::bvar(1);

    // motive : λ (x : Int) λ (_ : NonNeg x). Eq Int x (negSucc q) → False
    //   under `λ x λ hx` (on top of h,q): x=1, hx=0, h=2, q=3.
    let rec_motive = {
        let nonneg_x = Expr::app(cst("Int.NonNeg"), Expr::bvar(0)); // under λ x: x=0.
        // dom : Eq Int x (negSucc q)   under `λ x λ hx`: x=1, q=3.
        let dom = eq_int(Expr::bvar(1), negsucc(Expr::bvar(3)));
        let cod = cst("False"); // under λ x λ hx: q=3, but cod uses no q.
        let arrow = Expr::pi(bd(), dom, cod);
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), nonneg_x, arrow))
    };

    // minor : λ (n : Nat) λ (heq : Eq Int (ofNat n)(negSucc q)). Int.noConfusion ... heq
    //   under `λ n λ heq` (on top of h,q): heq=0, n=1, h=2, q=3.
    let rec_minor = {
        let n = || Expr::bvar(1);
        let q_in = || Expr::bvar(3);
        let heq = || Expr::bvar(0);
        // @Int.noConfusion.{0} False (ofNat n) (negSucc q) heq : False.
        let no_conf = Expr::apps(
            Expr::const_(Name::from_string("Int.noConfusion"), vec![Level::zero()]),
            [cst("False"), int_ofnat(n()), negsucc(q_in()), heq()],
        );
        // heq binder type `Eq Int (ofNat n)(negSucc q)` under `λ n`: n=0, q=2.
        let heq_ty = eq_int(int_ofnat(Expr::bvar(0)), negsucc(Expr::bvar(2)));
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), heq_ty, no_conf))
    };

    // @Int.NonNeg.rec motive minor (negSucc q) h : motive (negSucc q) h
    //   ≡ (Eq Int (negSucc q)(negSucc q) → False). Apply to Eq.refl.
    // Note `h ≡ NonNeg (negSucc q)` def-eq (sub by ofNat 0 reduces), so the rec INDEX is the
    // def-eq `negSucc q`.
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
        [rec_motive, rec_minor, negsucc(q()), Expr::bvar(0)],
    );
    let eq_refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [int_ty(), negsucc(q())],
    );
    let body = Expr::app(rec_app, eq_refl);
    let h_binder_ty = Expr::app(cst("Int.NonNeg"), negsucc(Expr::bvar(0)));
    Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), h_binder_ty, body))
}

/// Register `toNatMono` (idempotent). Pulls in the Int-order lemma suite plus the two
/// `ofNat`-cast sub-lemmas and the `negSucc`-refutation helper, each kernel-checked ⊆ 3.
pub(super) fn register_to_nat_mono(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_TONAT_MONO);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    env.init_int_ord_lemmas().map_err(|e| format!("init_int_ord_lemmas: {e:?}"))?;

    // Sub-lemma 1: ofNatLeOfNatOfLe (forward cast).
    register_checked_theorem(
        env,
        MIRSEM_OFNAT_LE_OFNAT_OF_LE,
        ofnat_le_ofnat_of_le_type(),
        ofnat_le_ofnat_of_le_proof(),
    )?;
    // Sub-lemma 2: leOfOfNatLeOfNat (converse cast).
    register_checked_theorem(
        env,
        MIRSEM_LE_OF_OFNAT_LE_OFNAT,
        le_of_ofnat_le_ofnat_type(),
        le_of_ofnat_le_ofnat_proof(),
    )?;
    // Sub-lemma 3: negSuccNotNonNeg (refutes `0 ≤ negSucc q`).
    register_checked_theorem(
        env,
        MIRSEM_NEGSUCC_NOT_NONNEG,
        negsucc_not_nonneg_type(),
        negsucc_not_nonneg_proof(),
    )?;
    // The monotonicity lemma itself.
    register_checked_theorem(env, MIRSEM_TONAT_MONO, to_nat_mono_type(), to_nat_mono_proof())?;
    Ok(())
}

/// Helper: `check_type` a `(type, proof)` and register it as a `Declaration::Theorem`
/// (idempotent on `name`). Mirrors the inline pattern in `register_loop_rank_decrease`.
pub(super) fn register_checked_theorem(
    env: &mut Environment,
    name_str: &str,
    ty: Expr,
    proof: Expr,
) -> Result<(), String> {
    let name = Name::from_string(name_str);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&proof, &ty).map_err(|e| format!("{name_str} check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: proof })
        .map_err(|e| format!("add_decl({name_str}): {e:?}"))?;
    Ok(())
}

/// `∀ (a b k : Int), Int.lt a b → Int.le (Int.ofNat 1) k →
///    Nat.lt (Int.toNat (Int.sub b (Int.add a k))) (Int.toNat (Int.sub b a))`.
// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — name-independent.
pub(crate) fn stride_rank_decrease_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let sub = |a: Expr, b: Expr| Expr::apps(cst("Int.sub"), [a, b]);
    let add = |a: Expr, b: Expr| Expr::apps(cst("Int.add"), [a, b]);
    // inside `∀ a ∀ b ∀ k`: k=0, b=1, a=2.
    let lt_ab = Expr::apps(cst("Int.lt"), [Expr::bvar(2), Expr::bvar(1)]);
    // after `Int.lt a b →`: k=1, b=2, a=3.
    let le_1k = int_le(int_one(), Expr::bvar(1));
    // conclusion after `Int.le 1 k →`: k=2, b=3, a=4.
    let a = || Expr::bvar(4);
    let b = || Expr::bvar(3);
    let k = || Expr::bvar(2);
    let concl = nat_lt(to_nat(sub(b(), add(a(), k()))), to_nat(sub(b(), a())));
    let after_le = Expr::pi(bd(), le_1k, concl);
    let after_lt = Expr::pi(bd(), lt_ab, after_le);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), after_lt)))
}

/// Proof of `strideRankDecrease`. See [`stride_rank_decrease_type`].
/// ```text
/// raw  := loopRankDecrease a b hlt : Nat.lt (toNat(b-(a+1))) (toNat(b-a))
/// hadd := Int.add_le_add_left 1 k hk a : Int.le (a+1) (a+k)
/// E    : (b-(a+1)) - (b-(a+k)) = (a+k) - (a+1)            [add_sub_add_left + neg_neg + add_comm]
/// hsub := Eq.subst (NonNeg) ((a+k)-(a+1)) ((b-(a+1))-(b-(a+k))) (Eq.symm E) hadd
///         : Int.le (b-(a+k)) (b-(a+1))                    [≡ NonNeg ((b-(a+1))-(b-(a+k)))]
/// mono := toNatMono (b-(a+k)) (b-(a+1)) hsub : Nat.le (toNat(b-(a+k))) (toNat(b-(a+1)))
/// out  := Nat.lt_of_le_of_lt (toNat(b-(a+k))) (toNat(b-(a+1))) (toNat(b-a)) mono raw
/// ```
pub(super) fn stride_rank_decrease_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Under `λ a λ b λ k λ (hlt : Int.lt a b) λ (hk : Int.le 1 k)`: hk=0, hlt=1, k=2, b=3, a=4.
    let a = || Expr::bvar(4);
    let b = || Expr::bvar(3);
    let k = || Expr::bvar(2);
    let hlt = || Expr::bvar(1);
    let hk = || Expr::bvar(0);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let sub = |x: Expr, y: Expr| Expr::apps(cst("Int.sub"), [x, y]);
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    let neg = |x: Expr| Expr::app(cst("Int.neg"), x);
    let a1 = || add(a(), int_one()); // a + 1
    let ak = || add(a(), k()); // a + k
    let sub_b_a1 = || sub(b(), a1()); // b - (a+1)
    let sub_b_ak = || sub(b(), ak()); // b - (a+k)
    let sub_b_a = || sub(b(), a()); // b - a

    // raw := loopRankDecrease a b hlt : Nat.lt (toNat(b-(a+1))) (toNat(b-a)).
    let raw = Expr::apps(cst(MIRSEM_LOOP_RANK_DECREASE), [a(), b(), hlt()]);

    // hadd := Int.add_le_add_left 1 k hk a : Int.le (a+1)(a+k).
    let hadd = Expr::apps(cst("Int.add_le_add_left"), [int_one(), k(), hk(), a()]);

    // Build E : ((b-(a+1)) - (b-(a+k))) = ((a+k) - (a+1)).
    //  e1 := Int.add_sub_add_left (neg(a+k)) (neg(a+1)) b
    //        : (b + neg(a+1)) - (b + neg(a+k)) = neg(a+1) - neg(a+k)
    //        [LHS ≡ (b-(a+1)) - (b-(a+k)) def-eq via Int.sub unfold].
    //  NB `Int.add_sub_add_left a' b' c : (c+b')-(c+a') = b'-a'` — the FIRST arg is the
    //  SUBTRAHEND side (a'), the SECOND is the minuend side (b'). We want LHS minuend
    //  `b + neg(a+1)` (so b' = neg(a+1)) and subtrahend `b + neg(a+k)` (so a' = neg(a+k)).
    let e1 = Expr::apps(cst("Int.add_sub_add_left"), [neg(ak()), neg(a1()), b()]);
    //  e2 := congrArg Int Int (neg(neg(a+k))) (a+k) (λ t. neg(a+1) + t) (Int.neg_neg (a+k))
    //        : neg(a+1) + neg(neg(a+k)) = neg(a+1) + (a+k)
    //        [LHS ≡ neg(a+1) - neg(a+k) def-eq].
    let neg_neg_ak = Expr::app(cst("Int.neg_neg"), ak()); // neg(neg(a+k)) = a+k
    let add_fn = {
        // λ (t : Int). Int.add (neg(a+1)) t   under `λ t`: t=0, and a/k lifted by 1.
        let a_l = Expr::bvar(5); // a was bvar(4); +1 under λ t → 5
        let body = add(neg(add(a_l, int_one())), Expr::bvar(0));
        Expr::lam(bd(), int_ty(), body)
    };
    let e2 = congr_arg(int_ty(), int_ty(), neg(neg(ak())), ak(), add_fn, neg_neg_ak);
    //  e3 := Int.add_comm (neg(a+1)) (a+k) : neg(a+1) + (a+k) = (a+k) + neg(a+1)
    //        [RHS ≡ (a+k) - (a+1) def-eq].
    let e3 = Expr::apps(cst("Int.add_comm"), [neg(a1()), ak()]);

    // Endpoints (stated in `sub` form; def-eq to the `add`/`neg` forms the lemmas produce):
    let lhs = || sub(sub_b_a1(), sub_b_ak()); // (b-(a+1)) - (b-(a+k))
    let mid1 = || sub(neg(a1()), neg(ak())); // neg(a+1) - neg(a+k)
    let mid2 = || add(neg(a1()), ak()); // neg(a+1) + (a+k)
    let rhs = || sub(ak(), a1()); // (a+k) - (a+1)
    // e23 := Eq.trans mid1 mid2 rhs e2 e3 : mid1 = rhs.
    let e23 = eq_trans_int(mid1(), mid2(), rhs(), e2, e3);
    // E := Eq.trans lhs mid1 rhs e1 e23 : lhs = rhs.
    let e_full = eq_trans_int(lhs(), mid1(), rhs(), e1, e23);

    // hsub := @Eq.subst Int (λ y. Int.NonNeg y) rhs lhs (Eq.symm E) hadd
    //         : Int.NonNeg lhs ≡ Int.le (b-(a+k)) (b-(a+1)).
    // hadd : Int.le (a+1)(a+k) ≡ Int.NonNeg ((a+k)-(a+1)) = NonNeg rhs.
    let nonneg_motive = Expr::lam(bd(), int_ty(), Expr::app(cst("Int.NonNeg"), Expr::bvar(0)));
    let e_sym = eq_symm_int(lhs(), rhs(), e_full);
    let hsub = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), nonneg_motive, rhs(), lhs(), e_sym, hadd],
    );

    // mono := toNatMono (b-(a+k)) (b-(a+1)) hsub : Nat.le (toNat(b-(a+k))) (toNat(b-(a+1))).
    let mono = Expr::apps(cst(MIRSEM_TONAT_MONO), [sub_b_ak(), sub_b_a1(), hsub]);

    // out := Nat.lt_of_le_of_lt (toNat(b-(a+k))) (toNat(b-(a+1))) (toNat(b-a)) mono raw.
    let out = Expr::apps(
        cst("Nat.lt_of_le_of_lt"),
        [to_nat(sub_b_ak()), to_nat(sub_b_a1()), to_nat(sub_b_a()), mono, raw],
    );

    // Binder types (evaluated at their OWN depth, before the inner binders):
    //   hlt : Int.lt a b   under `λ a λ b λ k`: a=2, b=1.
    let hlt_ty = Expr::apps(cst("Int.lt"), [Expr::bvar(2), Expr::bvar(1)]);
    //   hk : Int.le 1 k    under `λ a λ b λ k λ hlt`: k=1.
    let hk_ty = int_le(int_one(), Expr::bvar(1));
    Expr::lam(
        bd(),
        int_ty(),
        Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), hlt_ty, Expr::lam(bd(), hk_ty, out))),
        ),
    )
}

/// Register `strideRankDecrease` (idempotent). Requires `loopRankDecrease` and `toNatMono`.
pub(super) fn register_stride_rank_decrease(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STRIDE_RANK_DECREASE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    register_loop_rank_decrease(env)?;
    register_to_nat_mono(env)?;
    register_checked_theorem(
        env,
        MIRSEM_STRIDE_RANK_DECREASE,
        stride_rank_decrease_type(),
        stride_rank_decrease_proof(),
    )?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Per-function ranking + the concrete decrease proof, then the `loopTotalCorrect`
// instance. The recognized shape is the counter-increment loop
//   `while (Var i_idx) < (Var n_idx) { (Var i_idx) := (Var i_idx) + 1 }`
// with the PROVIDED ranking `R := λ e. Int.toNat (Int.sub (e n_idx) (e i_idx))`.
// ---------------------------------------------------------------------------
/// If `lf` is the recognized counter-increment loop `while i < n { i = i + 1 }`,
/// return `(i_idx, n_idx)` — the counter local index and the bound parameter index.
/// Fail-closed (`None`) otherwise: a different guard op, a non-`Var` operand, a body
/// that is not the single `i := i + 1` increment, etc. This is the soundness gate the
/// PROVIDED ranking rests on (the ranking is only a valid measure for THIS shape).
pub(super) fn recognize_counter_loop(lf: &SemLoopFunction) -> Option<(u64, u64)> {
    // Guard must be a single `Lt (Var i) (Var n)` leaf.
    let SemCondTree::Leaf(cond) = &lf.cond else { return None };
    if cond.op != SemCmpOp::Lt {
        return None;
    }
    let SemOperand::Var(i_idx) = cond.a else { return None };
    let SemOperand::Var(n_idx) = cond.b else { return None };
    if i_idx == n_idx {
        return None;
    }
    // Body must be exactly one stmt `Assign(i_idx, Bin Add (Var i_idx) (Const 1))`.
    if lf.body.len() != 1 {
        return None;
    }
    let stmt = &lf.body[0];
    if stmt.idx != i_idx {
        return None;
    }
    let SemRvalue::Bin(SemBinOp::Add, ref ba, ref bb) = stmt.rvalue else { return None };
    let SemOperand::Var(add_var) = *ba else { return None };
    let SemOperand::Const(add_const) = *bb else { return None };
    if add_var != i_idx || add_const != 1 {
        return None;
    }
    Some((i_idx, n_idx))
}

/// If `lf` is the recognized STRIDE counter loop `while i < n { i = i + k }` (`k ≥ 1` a
/// positive constant), return `(i_idx, n_idx)` — the counter and bound env indices. The
/// stride generalizes [`recognize_counter_loop`]'s `+1` to any positive `+k`. Fail-closed
/// (`None`) for a non-`Lt` guard, a non-`Var` operand, a body that is not the single
/// `i := i + k` increment, or a NON-positive `k` (the lower-bound preservation and the
/// stride ranking both require `k ≥ 1`). Test-only shape DISJOINTNESS check — production
/// dispatch lives in `prove::extract_synth_loop_function` (over the source guard/body ops).
#[cfg(test)]
pub(super) fn recognize_stride_loop(lf: &SemLoopFunction) -> Option<(u64, u64)> {
    let SemCondTree::Leaf(cond) = &lf.cond else { return None };
    if cond.op != SemCmpOp::Lt {
        return None;
    }
    let SemOperand::Var(i_idx) = cond.a else { return None };
    let SemOperand::Var(n_idx) = cond.b else { return None };
    if i_idx == n_idx {
        return None;
    }
    if lf.body.len() != 1 {
        return None;
    }
    let stmt = &lf.body[0];
    if stmt.idx != i_idx {
        return None;
    }
    let SemRvalue::Bin(SemBinOp::Add, ref ba, ref bb) = stmt.rvalue else { return None };
    let SemOperand::Var(add_var) = *ba else { return None };
    let SemOperand::Const(k) = *bb else { return None };
    if add_var != i_idx || k < 1 {
        return None;
    }
    Some((i_idx, n_idx))
}

/// If `lf` is the recognized COUNTDOWN loop `while i > 0 { i = i - 1 }`, return `i_idx` —
/// the counter env index. Fail-closed (`None`) for a non-`Gt` guard, a guard whose bound
/// operand is not the constant `0`, a body that is not the single `i := i - 1` decrement,
/// etc. The guard must be `Gt (Var i) (Const 0)` (so `eval_cond` yields `decide (Int.lt 0
/// i)` via the SWAPPED `Gt` arm) and the body `Assign(i, Sub (Var i) (Const 1))`. Test-only
/// shape DISJOINTNESS check — production dispatch lives in `prove::extract_synth_loop_function`.
#[cfg(test)]
pub(super) fn recognize_countdown_loop(lf: &SemLoopFunction) -> Option<u64> {
    let SemCondTree::Leaf(cond) = &lf.cond else { return None };
    if cond.op != SemCmpOp::Gt {
        return None;
    }
    let SemOperand::Var(i_idx) = cond.a else { return None };
    let SemOperand::Const(0) = cond.b else { return None };
    if lf.body.len() != 1 {
        return None;
    }
    let stmt = &lf.body[0];
    if stmt.idx != i_idx {
        return None;
    }
    let SemRvalue::Bin(SemBinOp::Sub, ref ba, ref bb) = stmt.rvalue else { return None };
    let SemOperand::Var(sub_var) = *ba else { return None };
    let SemOperand::Const(1) = *bb else { return None };
    if sub_var != i_idx {
        return None;
    }
    Some(i_idx)
}

/// If `lf` is the recognized `≤`-guarded counter loop `while i ≤ n { i = i + 1 }`, return
/// `(i_idx, n_idx)`. IDENTICAL to [`recognize_counter_loop`] except the guard op is `Le`
/// (not `Lt`). The `Le` guard re-establishes only `i ≤ n+1`, so the synthesized upper bound
/// is `i ≤ n+1` ([`SynthInvariant::CounterLeBoundSucc`]). Test-only shape DISJOINTNESS check
/// — production dispatch lives in `prove::extract_synth_loop_function`.
#[cfg(test)]
pub(super) fn recognize_counter_le_loop(lf: &SemLoopFunction) -> Option<(u64, u64)> {
    let SemCondTree::Leaf(cond) = &lf.cond else { return None };
    if cond.op != SemCmpOp::Le {
        return None;
    }
    let SemOperand::Var(i_idx) = cond.a else { return None };
    let SemOperand::Var(n_idx) = cond.b else { return None };
    if i_idx == n_idx {
        return None;
    }
    if lf.body.len() != 1 {
        return None;
    }
    let stmt = &lf.body[0];
    if stmt.idx != i_idx {
        return None;
    }
    let SemRvalue::Bin(SemBinOp::Add, ref ba, ref bb) = stmt.rvalue else { return None };
    let SemOperand::Var(add_var) = *ba else { return None };
    let SemOperand::Const(add_const) = *bb else { return None };
    if add_var != i_idx || add_const != 1 {
        return None;
    }
    Some((i_idx, n_idx))
}

/// The ranking TERM BUILDER `R := λ (e : Env). Int.toNat (Int.sub (e n_idx) (e i_idx))`
/// — the counter's distance to the bound (`toNat(n - i)`). A genuine `Env → Nat`. This is
/// the closed-term realization of whatever `(i_idx, n_idx)` the ranking SYNTHESIZER
/// ([`synthesize_counter_ranking`]) proposes; the genuineness test reuses it with a WRONG
/// override (e.g. `λ e. e[i_idx]`-as-Nat) so the per-function instance fails closed.
pub(super) fn counter_loop_ranking(i_idx: u64, n_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `λ (e : Env)`: e = bvar(0).
    let e_at = |idx: u64| Expr::app(Expr::bvar(0), Expr::nat_lit(idx));
    let sub = Expr::apps(cst("Int.sub"), [e_at(n_idx), e_at(i_idx)]);
    Expr::lam(bd(), env_ty(), Expr::app(cst("Int.toNat"), sub))
}

/// SYNTHESIZE the well-founded ranking for `lf` — the termination measure is INFERRED
/// from the loop STRUCTURE, not hand-supplied. The heuristic (the dual of the guard-aware
/// upper-bound invariant synthesis): a counter loop whose guard is `counter < bound` and
/// whose body INCREMENTS the counter (`counter := counter + 1`) strictly closes the gap
/// `bound - counter` each iteration, so the synthesizer PROPOSES the ranking `R := λ e.
/// toNat(bound - counter)`. The proposal is purely structural — `recognize_counter_loop`
/// returns `(i_idx, bound_idx)` from the `Lt`-guard + `+1`-increment shape, and the
/// ranking is `toNat((e bound_idx) - (e i_idx))`. The clean kernel then VERIFIES the
/// decrease (`Nat.lt (R (exec e body)) (R e)`) via the kernel-checked `loopRankDecrease`
/// lemma — synthesis PROPOSES, the kernel VERIFIES. Returns `(ranking, decrease_proof)`,
/// or `None` for any shape the heuristic does not recognize (fail-closed: no ranking is
/// proposed, so no termination is claimed). HONEST SCOPE: only the increment-toward-a-Lt-
/// bound counter is recognized; non-`+1` strides, non-`Lt` guards, multi-statement bodies,
/// and nested loops are DEFERRED.
pub(super) fn synthesize_counter_ranking(lf: &SemLoopFunction) -> Option<(Expr, Expr)> {
    // SHAPE-AWARE dispatch: the synthesized invariant (when present) names the loop
    // shape, which selects the structural ranking + its decrease proof. For the
    // ORIGINAL `Lt`-guard + `+1` shape (synth_inv absent or one of the Lt-family
    // variants), fall through to the default `recognize_counter_loop` path so every
    // existing certificate reduces byte-identically.
    match &lf.synth_inv {
        // ≤-GUARDED `+1` loop `while i ≤ n { i = i+1 }`: ranking toNat((n+1) - i).
        Some(SynthInvariant::CounterLeBoundSucc { i_idx, bound_idx })
        | Some(SynthInvariant::CounterInRangeSucc { i_idx, bound_idx, .. }) => {
            let (i_idx, bound_idx) = (*i_idx, *bound_idx);
            let ranking = counter_loop_succ_ranking(i_idx, bound_idx);
            let decrease = counter_loop_le_decrease_proof(lf, i_idx, bound_idx);
            return Some((ranking, decrease));
        }
        // COUNTDOWN `while i > 0 { i = i-1 }`: ranking toNat(i).
        Some(SynthInvariant::CountdownGeConst { i_idx, .. }) => {
            let i_idx = *i_idx;
            let ranking = countdown_loop_ranking(i_idx);
            let decrease = countdown_loop_decrease_proof(lf, i_idx);
            return Some((ranking, decrease));
        }
        // STRIDE `while i < n { i = i+k }` (k ≥ 1): the ranking `toNat(n − i)` STRICTLY
        // decreases each `+k` step (the gap closes by `k ≥ 1`). Termination is now TOTAL —
        // the decrease is the kernel-checked `strideRankDecrease` (built on the `toNatMono`
        // monotonicity lemma `Int.le a b → Nat.le (toNat a)(toNat b)`): from `i < n` and
        // `1 ≤ k`, `toNat(n − (i+k)) < toNat(n − i)`. The bound index `n_idx` is recovered
        // from the loop guard `i < n` (a `Lt`-leaf, `cond.b = Var n_idx`); a non-`Lt`/non-`Var`
        // guard yields no ranking (fail-closed). A wrong (non-positive / mismatched) `k`
        // makes the decrease ill-typed ⇒ KernelRejected.
        Some(SynthInvariant::StrideGeConst { i_idx, k, .. }) => {
            let (i_idx, k) = (*i_idx, *k);
            let SemCondTree::Leaf(cond) = &lf.cond else { return None };
            if cond.op != SemCmpOp::Lt {
                return None;
            }
            let SemOperand::Var(av) = cond.a else { return None };
            let SemOperand::Var(n_idx) = cond.b else { return None };
            if av != i_idx || k < 1 {
                return None;
            }
            let ranking = stride_loop_ranking(i_idx, n_idx);
            let decrease = stride_loop_decrease_proof(lf, i_idx, n_idx, k);
            return Some((ranking, decrease));
        }
        // ACCUMULATOR `while i < n { s = s+1; i = i+1 }`: the INVARIANT is about `s`, but
        // TERMINATION is via the GUARD counter `i`. The ranking is `toNat(n − i)` over
        // `i_idx`, decreasing each iteration because the body's `i := i+1` statement
        // increments `i` (and the `s := s+1` statement does not touch `i_idx`, so the
        // ranking's decrease retypes through the multi-statement `exec`). Same ranking +
        // decrease as the `+1` counter, instantiated at the accum's `(i_idx, n_idx)`.
        Some(SynthInvariant::AccumGeConst { i_idx, n_idx, .. }) => {
            let (i_idx, n_idx) = (*i_idx, *n_idx);
            let ranking = counter_loop_ranking(i_idx, n_idx);
            let decrease = counter_loop_decrease_proof(lf, i_idx, n_idx);
            return Some((ranking, decrease));
        }
        // RELATIONAL ACCUMULATOR `while i < n { s = s+1; i = i+1 }`: termination is via the
        // GUARD counter `i` exactly as the bare accumulator (`toNat(n − i)`, decreasing each
        // `i := i+1` step). The relational invariant is over `(s, i)` but the ranking measures
        // only `i`, so the SAME ranking + decrease as the `+1` counter retypes here.
        Some(SynthInvariant::AccumEqCounter { i_idx, n_idx, .. }) => {
            let (i_idx, n_idx) = (*i_idx, *n_idx);
            let ranking = counter_loop_ranking(i_idx, n_idx);
            let decrease = counter_loop_decrease_proof(lf, i_idx, n_idx);
            return Some((ranking, decrease));
        }
        // GENERAL RELATIONAL ACCUMULATOR `while i < n { a₀=a₀+1; …; aₘ=aₘ+1; i=i+1 }`: like the
        // 2-var relational accumulator, termination is via the GUARD counter `i` alone
        // (`toNat(n − i)`, decreasing each `i := i+1` step); the accumulators do not affect the
        // ranking (the other body statements leave `i_idx` untouched, so the decrease retypes
        // through the multi-statement `exec`).
        Some(SynthInvariant::AccumEqCounterSet { i_idx, n_idx, .. }) => {
            let (i_idx, n_idx) = (*i_idx, *n_idx);
            let ranking = counter_loop_ranking(i_idx, n_idx);
            let decrease = counter_loop_decrease_proof(lf, i_idx, n_idx);
            return Some((ranking, decrease));
        }
        // CONDITIONALLY-UPDATED accumulator `while i < n { if i>m { m=i }; i=i+1 }`: the
        // INVARIANT is about `m` (conditionally updated), but TERMINATION is via the GUARD
        // counter `i` exactly as the bare accumulator (`toNat(n − i)`, decreasing each
        // `i := i+1` step). The conditional `m := Sel (i>m) i m` statement leaves `i_idx`
        // untouched (`Nat.beq m_idx i_idx ≡ false`), so the SAME ranking + decrease as the
        // `+1` counter retypes through the 2-statement `exec`.
        Some(SynthInvariant::CondUpdateGeConst { i_idx, n_idx, .. }) => {
            let (i_idx, n_idx) = (*i_idx, *n_idx);
            let ranking = counter_loop_ranking(i_idx, n_idx);
            let decrease = counter_loop_decrease_proof(lf, i_idx, n_idx);
            return Some((ranking, decrease));
        }
        // CONDITIONAL-INCREMENT accumulator (Trust: Step 6CI, Increment B, real-loop-leaf
        // frontier) `while i < n { count := count + Cast(<bool>, IntTy); i := i + k }`:
        // the INVARIANT is about `count`, but TERMINATION is via the GUARD counter `i`
        // (here the walking pointer) exactly as the bare accumulator (`toNat(n − i)`,
        // decreasing each `i := i+k` step). The conditional `count := Sel(cond, tmp,
        // count)` statement and its `tmp := count+1` predecessor both leave `i_idx`
        // untouched, so the SAME ranking + decrease as the `+1` counter retypes through
        // the 3-statement `exec`.
        Some(SynthInvariant::CondIncrGeConst { i_idx, n_idx, .. }) => {
            let (i_idx, n_idx) = (*i_idx, *n_idx);
            let ranking = counter_loop_ranking(i_idx, n_idx);
            let decrease = counter_loop_decrease_proof(lf, i_idx, n_idx);
            return Some((ranking, decrease));
        }
        _ => {}
    }
    let (i_idx, bound_idx) = recognize_counter_loop(lf)?;
    // PROPOSE: ranking = distance to the bound, toNat(bound - counter).
    let ranking = counter_loop_ranking(i_idx, bound_idx);
    // The CONCRETE decrease proof the kernel verifies against (via `loopRankDecrease`).
    let decrease = counter_loop_decrease_proof(lf, i_idx, bound_idx);
    Some((ranking, decrease))
}

/// The ranking TERM `R := λ e. Int.toNat (Int.sub (Int.add (e bound_idx) 1) (e i_idx))` —
/// the distance to `n+1` for the `≤`-guarded counter loop `while i ≤ n { i = i+1 }` (which
/// runs until `i = n+1`). The `Le`-guard analogue of [`counter_loop_ranking`].
pub(super) fn counter_loop_succ_ranking(i_idx: u64, bound_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_at = |idx: u64| Expr::app(Expr::bvar(0), Expr::nat_lit(idx));
    let b1 = Expr::apps(cst("Int.add"), [e_at(bound_idx), int_one()]);
    let sub = Expr::apps(cst("Int.sub"), [b1, e_at(i_idx)]);
    Expr::lam(bd(), env_ty(), Expr::app(cst("Int.toNat"), sub))
}

/// The decrease PROOF for the `≤`-guarded `+1` loop's ranking `R := toNat((n+1)-i)`:
/// `λ (e)(hg). loopRankDecrease (e i) (Int.add (e n) 1) <hlt: i < n+1>`.
/// `hlt := Int.add_le_add_right (e i)(e n) <guard: i ≤ n> 1 : Int.le (i+1)(n+1) ≡ Int.lt i (n+1)`.
/// `loopRankDecrease i (n+1) hlt : Nat.lt (toNat((n+1)-(i+1))) (toNat((n+1)-i))` = the decrease
/// for `R` over `[i:=i+1]` (the body makes `R(exec) = toNat((n+1)-(i+1))`).
pub(super) fn counter_loop_le_decrease_proof(lf: &SemLoopFunction, i_idx: u64, bound_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let cond_expr = lf.cond.to_cond_expr();
    // under `λ e λ hg`: hg=0, e=1.
    let e_i = Expr::app(Expr::bvar(1), Expr::nat_lit(i_idx));
    let e_n = Expr::app(Expr::bvar(1), Expr::nat_lit(bound_idx));
    let b1 = Expr::apps(cst("Int.add"), [e_n.clone(), int_one()]);
    // Extract `i ≤ n` from the Le guard, then add 1 on both sides ⇒ `i+1 ≤ n+1` ≡ `i < n+1`.
    let p = Expr::apps(cst("Int.le"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLe"), [e_i.clone(), e_n.clone()]);
    let hg = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // i ≤ n
    let hlt = add_le_add_right(e_i.clone(), e_n, hg, int_one()); // i+1 ≤ n+1 ≡ i < n+1
    let body = Expr::apps(cst(MIRSEM_LOOP_RANK_DECREASE), [e_i, b1, hlt]);
    let guard_eq = eq_bool_true(Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(0), cond_expr]));
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), guard_eq, body))
}

/// The ranking TERM `R := λ e. Int.toNat (e i_idx)` for the COUNTDOWN loop
/// `while i > 0 { i = i-1 }` — `i` itself (it decreases to 0).
pub(super) fn countdown_loop_ranking(i_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(i_idx));
    Expr::lam(bd(), env_ty(), Expr::app(cst("Int.toNat"), e_i))
}

/// The decrease PROOF for the countdown ranking `R := toNat(i)`:
/// `λ (e)(hg). countdownRankDecrease (e i) <hlt: 0 < i>`.
/// `hlt := of_decide_eq_true (Int.lt 0 (e i)) … hg` from the SWAPPED `Gt` guard `decide
/// (Int.lt 0 (e i))`; `countdownRankDecrease i hlt : Nat.lt (toNat(i-1)) (toNat i)` = the
/// decrease for `R` over `[i:=i-1]` (the body makes `R(exec) = toNat(i-1)`).
pub(super) fn countdown_loop_decrease_proof(lf: &SemLoopFunction, i_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let cond_expr = lf.cond.to_cond_expr();
    // under `λ e λ hg`: hg=0, e=1.
    let e_i = Expr::app(Expr::bvar(1), Expr::nat_lit(i_idx));
    let zero = int_lit(0);
    let p = Expr::apps(cst("Int.lt"), [zero.clone(), e_i.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [zero, e_i.clone()]);
    let hlt = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // 0 < i
    let body = Expr::apps(cst(MIRSEM_COUNTDOWN_RANK_DECREASE), [e_i, hlt]);
    let guard_eq = eq_bool_true(Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(0), cond_expr]));
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), guard_eq, body))
}

/// The ranking TERM for the STRIDE loop `while i < n { i = i + k }` — IDENTICAL to the
/// `+1` counter ranking `R := λ e. Int.toNat (Int.sub (e n_idx) (e i_idx))` (`toNat(n − i)`):
/// the measure is the distance to the bound REGARDLESS of stride, and `toNat` floors a
/// possible overshoot to 0. The stride only changes the DECREASE proof (see
/// [`stride_loop_decrease_proof`]), not the measure.
pub(super) fn stride_loop_ranking(i_idx: u64, n_idx: u64) -> Expr {
    counter_loop_ranking(i_idx, n_idx)
}

/// The CONCRETE decrease PROOF for the STRIDE loop `while i < n { i = i + k }` (`k ≥ 1`):
/// `λ (e)(hg). strideRankDecrease (e i) (e n) (int_lit k) <hlt: i<n> <hk: 1≤k>`.
///
/// The ranking is `R := toNat(n − i)` (same as the `+1` counter), so over the stride body
/// `[i := i+k]` the kernel-expected decrease `Nat.lt (R (exec e body)) (R e)` reduces to
/// `Nat.lt (toNat((e n) − ((e i)+k))) (toNat((e n) − (e i)))` — EXACTLY the conclusion of
/// `strideRankDecrease` (with `a := e i`, `b := e n`, `k := int_lit k`). The two hypotheses:
///   * `hlt : Int.lt (e i)(e n)` is extracted from the guard `eval_cond e (i<n) = true` by
///     the inline `of_decide_eq_true` (def-eq `decide (Int.lt (e i)(e n)) (Int.decLt …) = true`).
///   * `hk : Int.le (Int.ofNat 1) (int_lit k)` is a CLOSED decidable fact (both sides are
///     `Int.ofNat` literals for `k ≥ 1`), proved by `of_decide_eq_true (Int.le 1 k)
///     (Int.decLe 1 k) (Eq.refl true)` — `decide` on the closed literal pair REDUCES to
///     `Bool.true`, so `Eq.refl Bool.true` retypes. (`int_lit k = Int.ofNat k` for `k ≥ 1`.)
/// This is the stride analogue of [`counter_loop_decrease_proof`]; the `+1` case `k=1` is
/// also covered by `strideRankDecrease` but the production dispatch keeps the dedicated
/// `loopRankDecrease` path for `k=1` so existing certificates reduce byte-identically.
pub(super) fn stride_loop_decrease_proof(lf: &SemLoopFunction, i_idx: u64, n_idx: u64, k: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let cond_expr = lf.cond.to_cond_expr();
    // under `λ (e : Env) λ (hg : eval_cond e cond = true)`: hg=0, e=1.
    let e_i = Expr::app(Expr::bvar(1), Expr::nat_lit(i_idx)); // e i_idx
    let e_n = Expr::app(Expr::bvar(1), Expr::nat_lit(n_idx)); // e n_idx
    let k_lit = int_lit(k); // Int.ofNat k (k ≥ 1)
    // hlt : Int.lt (e i)(e n) — extracted from the `Lt` guard.
    let p_lt = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst_lt = Expr::apps(cst("Int.decLt"), [e_i.clone(), e_n.clone()]);
    let hlt = Expr::apps(of_decide_eq_true_term(), [p_lt, inst_lt, Expr::bvar(0)]);
    // hk : Int.le (Int.ofNat 1) (int_lit k) — a CLOSED decidable literal fact.
    let p_le = int_le(int_one(), k_lit.clone());
    let inst_le = Expr::apps(cst("Int.decLe"), [int_one(), k_lit.clone()]);
    let refl_true = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [cst("Bool"), cst("Bool.true")],
    );
    let hk = Expr::apps(of_decide_eq_true_term(), [p_le, inst_le, refl_true]);
    // strideRankDecrease (e i) (e n) (int_lit k) hlt hk :
    //   Nat.lt (toNat ((e n) − ((e i)+k))) (toNat ((e n) − (e i))).
    let body = Expr::apps(cst(MIRSEM_STRIDE_RANK_DECREASE), [e_i, e_n, k_lit, hlt, hk]);
    let guard_eq = eq_bool_true(Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(0), cond_expr]));
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), guard_eq, body))
}

/// The CONCRETE decrease PROOF for the counter loop: `loopRankDecrease` applied at the
/// concrete `(a := e i_idx, b := e n_idx)` under the guard hypothesis, packaged as the
/// `decrease_hyp_type` term `∀ e, eval_cond e cond = true → Nat.lt (R (exec e body)) (R e)`.
///
/// The body of the lambda is `loopRankDecrease (e i_idx) (e n_idx) hlt` where `hlt :
/// Int.lt (e i_idx) (e n_idx)` is extracted from the guard `eval_cond e cond = true`
/// (def-eq `decide (Int.lt (e i_idx) (e n_idx)) (Int.decLt …) = true`) by the inline
/// `of_decide_eq_true`. The result type `Nat.lt (toNat (n-(i+1))) (toNat (n-i))` is
/// def-eq to `Nat.lt (R (exec e body)) (R e)` (the ranking and the body reductions).
pub(super) fn counter_loop_decrease_proof(lf: &SemLoopFunction, i_idx: u64, n_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let cond_expr = lf.cond.to_cond_expr();
    // under `λ (e : Env) λ (hg : eval_cond e cond = true)`: hg=0, e=1.
    let e_i = Expr::app(Expr::bvar(1), Expr::nat_lit(i_idx)); // e i_idx
    let e_n = Expr::app(Expr::bvar(1), Expr::nat_lit(n_idx)); // e n_idx
    // p := Int.lt (e i_idx) (e n_idx) ; inst := Int.decLt (e i_idx) (e n_idx).
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i.clone(), e_n.clone()]);
    // hg : @Eq Bool (eval_cond e cond) Bool.true  — and `eval_cond e cond` def-eq
    //   `decide p inst`, so `of_decide_eq_true p inst hg : p`.
    let hlt = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    // loopRankDecrease (e i_idx) (e n_idx) hlt :
    //   Nat.lt (toNat (sub (e n) (add (e i) 1))) (toNat (sub (e n) (e i)))
    let body = Expr::apps(cst(MIRSEM_LOOP_RANK_DECREASE), [e_i, e_n, hlt]);
    // guard hypothesis type `eval_cond e cond = true` (under `λ e`): e=0.
    let guard_eq = eq_bool_true(Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(0), cond_expr]));
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), guard_eq, body))
}

/// The inline `of_decide_eq_true : ∀ (p : Prop)(inst : Decidable p), decide p inst =
/// true → p`. Built once (a closed term, no env decl): case on `inst` via
/// `@Decidable.rec.{0}` at the threaded-equation motive `λ d. decide p d = true → p`;
/// the `isFalse` arm reduces `decide p (isFalse _)` to `Bool.false`, contradicting `=
/// Bool.true` via `Bool.noConfusion` ⇒ `False.elim`; the `isTrue` arm returns the
/// proof `hp : p`. Axiom-free (only `Decidable.rec`/`Bool.noConfusion`/`False.elim`).
pub(super) fn of_decide_eq_true_term() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let prop = Expr::prop();
    let eq_bool = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), x, y],
        )
    };
    let decide = |p: Expr, inst: Expr| Expr::apps(cst("decide"), [p, inst]);

    // motive : λ (d : Decidable p). decide p d = Bool.true → p
    //   under `λ (p:Prop) λ (inst) λ (h) λ (d:Decidable p)`: d=0, h=1, inst=2, p=3.
    let motive = {
        // the `λ d` binder TYPE `Decidable p` is evaluated BEFORE `λ d` (under `λ p λ inst
        // λ h`), so there p=2.
        let d_binder_ty = Expr::apps(cst("Decidable"), [Expr::bvar(2)]);
        // inside `λ d`: d=0, h=1, inst=2, p=3.
        let dec = decide(Expr::bvar(3), Expr::bvar(0));
        let dom = eq_bool(dec, cst("Bool.true"));
        // codomain `p` after the `→`: p lifts +1 ⇒ p=4.
        Expr::lam(bd(), d_binder_ty, Expr::pi(bd(), dom, Expr::bvar(4)))
    };
    // isFalse minor : λ (hnp : p → False) λ (he : decide p (isFalse p hnp) = true). False.elim …
    //   under `λ p λ inst λ h λ hnp λ he`: he=0, hnp=1, h=2, inst=3, p=4.
    let is_false_minor = {
        // hnp : p → False  (under `λ p λ inst λ h`: p=2) ⇒ `λ (_:p). False` with p=3 inside.
        let hnp_ty = Expr::pi(bd(), Expr::bvar(2), cst("False"));
        // he : decide p (isFalse p hnp) = true (under +hnp: p=3, hnp=0).
        let isfalse = Expr::apps(cst("Decidable.isFalse"), [Expr::bvar(3), Expr::bvar(0)]);
        let he_ty = eq_bool(decide(Expr::bvar(3), isfalse), cst("Bool.true"));
        // body (under +he): p=4, hnp=1, he=0.
        //   @Bool.noConfusion.{0} False Bool.false Bool.true he : False  (decide…isFalse ≡ false)
        let no_conf = Expr::apps(
            Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]),
            [cst("False"), cst("Bool.false"), cst("Bool.true"), Expr::bvar(0)],
        );
        // @False.elim.{0} p no_conf : p
        let felim = Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [Expr::bvar(4), no_conf],
        );
        Expr::lam(bd(), hnp_ty, Expr::lam(bd(), he_ty, felim))
    };
    // isTrue minor : λ (hp : p) λ (_he : decide p (isTrue p hp) = true). hp
    //   under `λ p λ inst λ h λ hp`: hp=0, h=1, inst=2, p=3.
    let is_true_minor = {
        let hp_ty = Expr::bvar(2); // p
        // _he type (under +hp: p=3, hp=0).
        let istrue = Expr::apps(cst("Decidable.isTrue"), [Expr::bvar(3), Expr::bvar(0)]);
        let he_ty = eq_bool(decide(Expr::bvar(3), istrue), cst("Bool.true"));
        // body returns hp (under +_he: hp=1).
        Expr::lam(bd(), hp_ty, Expr::lam(bd(), he_ty, Expr::bvar(1)))
    };
    // @Decidable.rec.{0} p motive isFalse isTrue inst : motive inst ≡ decide p inst = true → p
    //   under `λ p λ inst λ h`: h=0, inst=1, p=2.
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Decidable.rec"), vec![Level::zero()]),
        [Expr::bvar(2), motive, is_false_minor, is_true_minor, Expr::bvar(1)],
    );
    // apply to `h` ⇒ p.
    let applied = Expr::app(rec_app, Expr::bvar(0));
    // λ (p:Prop) λ (inst:Decidable p) λ (h : decide p inst = true). applied
    let inst_ty = Expr::apps(cst("Decidable"), [Expr::bvar(0)]); // under `λ p`: p=0
    let h_ty = eq_bool(decide(Expr::bvar(1), Expr::bvar(0)), cst("Bool.true")); // under `λ p λ inst`: p=1,inst=0
    Expr::lam(bd(), prop, Expr::lam(bd(), inst_ty, Expr::lam(bd(), h_ty, applied)))
}

// ---------------------------------------------------------------------------
// The per-function `loopTotalCorrect` INSTANCE: conclusion type, proof, env, check.
// ---------------------------------------------------------------------------
/// The per-function TOTAL-CORRECTNESS CONCLUSION TYPE — `loopTotalCorrect` SPECIALIZED
/// at this function's concrete `(I, R, cond, body)`, after feeding the concrete `pres`
/// and `decrease` proofs:
/// `∀ (e : Env), I e → And (I (exec_loop e cond body (R e)))
///                         (eval_cond (exec_loop e cond body (R e)) cond = false)`.
/// This is TOTAL correctness for THIS loop: the (untouched-local) invariant holds at the
/// halting state AND the loop halts within `R e` guarded steps. `ranking` is the
/// PROVIDED `R := λ e. toNat(n - i)` (or a wrong override, for the fail-closed test).
pub(super) fn loop_total_instance_conclusion_type(lf: &SemLoopFunction, ranking: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();
    // ∀ (e:Env), I e → And A B   (A,B at fuel `R e`).
    //   under `∀ e`: e=0. `I e`: I lifted +1.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    //   under `∀ e` + `I e →`: e=1.
    let r_e = Expr::app(ranking.clone().lift(2), Expr::bvar(1)); // R e
    let looped = exec_loop_app(
        Expr::bvar(1),
        cond_expr.clone().lift(2),
        body_expr.clone().lift(2),
        r_e.clone(),
    );
    let a = Expr::app(i_expr.lift(2), looped.clone());
    let b = eq_bool_false(eval_cond_app(looped, cond_expr.lift(2)));
    let and_ab = Expr::apps(cst("And"), [a, b]);
    let after_hi = Expr::pi(bd(), i_e, and_ab);
    Expr::pi(bd(), env_ty(), after_hi)
}

/// The per-function TOTAL-CORRECTNESS PROOF — the general `loopTotalCorrect` theorem
/// APPLIED to this function's concrete `(I, R, cond, body, pres, decrease)`:
/// `loopTotalCorrect I R cond body <preservation> <decrease>`. Type-checking this
/// application at the conclusion type IS the per-function corollary. `ranking` is the
/// PROVIDED `R`; `decrease` is the concrete decrease proof for it (a WRONG ranking with a
/// decrease proof that does not type-check against the conclusion fails closed).
pub(super) fn loop_total_instance_proof(lf: &SemLoopFunction, ranking: &Expr, decrease: &Expr) -> Expr {
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();
    let pres = loop_instance_preservation_proof(lf, None);
    Expr::apps(
        cst(MIRSEM_LOOP_TOTAL_CORRECT),
        [i_expr, ranking.clone(), cond_expr, body_expr, pres, decrease.clone()],
    )
}

/// Build the env the per-function total-correctness instance lives in: the whole loop
/// meta-theory (`loopInvariantRule`, `loopRankTerminates`, `loopTotalCorrect`, all their
/// dependencies) PLUS `loopRankDecrease` and the Int-order lemmas it needs — all modulo 3.
pub(crate) fn loop_total_correct_instance_env() -> Result<Environment, String> {
    let mut env = loop_total_correct_env()?; // loopInvariantRule + loopRankTerminates + deps
    register_loop_total_correct(&mut env)?; // the composed theorem
    register_loop_rank_decrease(&mut env)?; // the per-function arithmetic decrease lemma
    register_countdown_ge0(&mut env)?; // the countdown lower-bound lemma `0 < i → 0 ≤ i-1`
    register_countdown_rank_decrease(&mut env)?; // the countdown ranking-decrease lemma
    register_stride_rank_decrease(&mut env)?; // the STRIDE ranking-decrease lemma (toNat-mono based)
    Ok(env)
}

/// Kernel-check the per-function TOTAL-CORRECTNESS instance for `lf` with the PROVIDED
/// `ranking` and its `decrease` proof. Builds the conclusion type and the
/// `loopTotalCorrect I R cond body pres decrease` proof, `check_type`s, registers, and
/// audits ⊆ 3. A wrong ranking (decrease proof not matching the conclusion's fuel `R e`)
/// is `KernelRejected` (fail-closed).
pub(super) fn check_loop_total_correct_instance_inner(
    lf: &SemLoopFunction,
    ranking: &Expr,
    decrease: &Expr,
) -> RefinementVerdict {
    let mut env = match loop_total_correct_instance_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = loop_total_instance_conclusion_type(lf, ranking);
    let proof = loop_total_instance_proof(lf, ranking, decrease);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "loop total instance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.MirSem.loopInstance.totalCorrect");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add loop total instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "loop total instance axiom residue: {names:?}"
            ))
        }
        None => RefinementVerdict::KernelRejected("loop total instance decl not found".to_string()),
    }
}

/// Kernel-check the per-function TOTAL-CORRECTNESS instance for the recognized counter
/// loop `lf` with the SYNTHESIZED ranking. The ranking `R := λ e. toNat(bound - counter)`
/// is INFERRED from the loop structure by [`synthesize_counter_ranking`] (not
/// hand-supplied); the kernel then VERIFIES its decrease. See
/// [`check_loop_total_correct_instance_inner`].
#[must_use]
pub fn check_loop_total_correct_instance(lf: &SemLoopFunction) -> RefinementVerdict {
    let Some((ranking, decrease)) = synthesize_counter_ranking(lf) else {
        return RefinementVerdict::KernelRejected(
            "ranking synthesis did not recognize the loop shape".to_string(),
        );
    };
    check_loop_total_correct_instance_inner(lf, &ranking, &decrease)
}

/// Mint a [`LoopTotalCorrectCertificate`] for `lf` IF it is the recognized
/// counter-increment loop AND the per-function `loopTotalCorrect` instance (with the
/// SYNTHESIZED ranking + concrete decrease proof) kernel-checks modulo 3. Fail-closed:
/// returns `None` when ranking synthesis does not recognize the shape, when the body
/// assigns the invariant local (partial-correctness soundness guard, untouched-local form
/// only), or when the kernel rejects.
#[must_use]
pub fn loop_total_correct_witness(lf: &SemLoopFunction) -> Option<LoopTotalCorrectCertificate> {
    // SOUNDNESS GUARD (partial half, untouched-local form ONLY): the equality invariant
    // must not be assigned by the body. The SYNTHESIZED form carries a genuine kernel
    // preservation proof and DOES assign the counter, so the guard does not apply (its
    // soundness is enforced by the kernel check below).
    if lf.synth_inv.is_none() && lf.body_assigns(lf.inv_local) {
        return None;
    }
    // SHAPE GATE (termination half): ranking synthesis must recognize the counter loop and
    // PROPOSE a measure. A different shape ⇒ no synthesized ranking ⇒ no certificate.
    let _ = synthesize_counter_ranking(lf)?;
    match check_loop_total_correct_instance(lf) {
        RefinementVerdict::ProvenModulo3 => Some(LoopTotalCorrectCertificate {
            function: lf.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}
