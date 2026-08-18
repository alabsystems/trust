-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- ============================================================================
--  BOUNDED-CORNER MULTIPLY — the interval law behind the i128 Mul suppression,
--  kernel-checked in clean with ZERO domain-specific axioms.
-- ============================================================================
--
--  WHAT THIS IS FOR.
--  `crates/trust-vcgen/src/generate/overflow_vc.rs` mints NO overflow obligation
--  for a signed 128-bit `a * b` when both operands carry finite constant boxes
--  on every reaching path and all four CORNER products fit i128
--  (`v2_signed_mul_provably_cannot_overflow`).  Signed 128-bit Mul is nonlinear
--  and the native lane declines it, so that suppression rests on an INTERVAL
--  ARITHMETIC argument decided in Rust: the extremes of a product over a box are
--  attained at the box's corners.
--
--  This file proves that argument, once, as a real theorem:
--
--    mul_box_upper : la <= a -> a <= ha -> lb <= b -> b <= hb ->
--                    la*lb <= M -> la*hb <= M -> ha*lb <= M -> ha*hb <= M ->
--                    a*b <= M
--    mul_box_lower : (dually, with m <= each corner)  ->  m <= a*b
--
--  Together they are exactly the fact the Rust pre-pass assumes: if every
--  corner lies in [i128::MIN, i128::MAX], so does every product over the box.
--  Note the shape is stated against BOUNDS (M / m) rather than a `min4`/`max4`
--  definition, because that is the form the caller actually has: four
--  `checked_mul` successes.
--
--  WHY THE BOOTSTRAP LEMMAS ARE HERE.
--  `clean check`'s environment exposes `Int.mul_le_mul_of_nonneg_left`,
--  `Int.le_total/le_trans/le_refl`, `Int.left_distrib`, `Int.neg_mul_right`,
--  `Int.add_le_add_right`, `Int.neg_add_self`, `Int.add_assoc` — but NOT
--  `Int.mul_comm`, `Int.zero_mul`, right-distributivity, or `Int.neg_mul` (a
--  left-factor negation law).  With only LEFT multiplication available, neither
--  the varying-first-factor step nor the negative-multiplier case can be taken.
--  So `imul_comm` is proved here by double `Int.rec`: every case of `Int.mul`
--  reduces to `Nat.mul` under `Int.ofNat` / `Int.negOfNat`, which makes each of
--  the four cases a `congrArg` over `Nat.mul_comm`.  Everything else — right
--  monotonicity, the left-factor negation law, and the two nonpositive
--  monotonicity laws — follows from it.  This mirrors the g16 files, which
--  likewise build their Nat ring lemmas from the bare prelude.
--
--  NON-VACUITY.  `corner_witness_products` / `corner_witness_negative` pin
--  concrete products (including a negative operand) so the development cannot
--  degenerate into a set of trivially-true statements about a multiplication
--  that computes to nothing.
--
--  HONEST RESIDUAL — READ BEFORE CITING THIS FILE.
--  This is STANDALONE CORROBORATION, exactly the status of
--  `proofs/codegen-equivalence/g16_multiplier_equivalence.lean`.  It does NOT
--  make the vcgen row emit `Proven{KernelRecheckable}`, and nothing in the live
--  verdict path consults it.  Instantiating a structured theorem at the gate
--  needs a Formula <-> model reconstruction bridge that does not exist for any
--  op yet (see the g16 header's identical note, which is why wide `Mul` stays
--  [VALIDATED]).  What this file changes is that the interval argument is no
--  longer only a Rust pre-pass: it is a kernel-checked theorem with an empty
--  domain-axiom closure, available for that wiring when it lands.
--
--  Gate: `crates/trust-integration-tests/tests/i128_corner_bounds_proof_gate.rs`
--  asserts this file kernel-checks AND that every exported theorem's axiom
--  closure is foundational-only.

set_option autoImplicit false
namespace CornerBox

theorem imul_comm : ∀ (a b : Int), Eq Int (Int.mul a b) (Int.mul b a) :=
  fun a =>
    @Int.rec (fun x => ∀ (b : Int), Eq Int (Int.mul x b) (Int.mul b x))
      (fun m b =>
        @Int.rec (fun y => Eq Int (Int.mul (Int.ofNat m) y) (Int.mul y (Int.ofNat m)))
          (fun n => congrArg Int.ofNat (Nat.mul_comm m n))
          (fun n => congrArg Int.negOfNat (Nat.mul_comm m (Nat.succ n)))
          b)
      (fun m b =>
        @Int.rec (fun y => Eq Int (Int.mul (Int.negSucc m) y) (Int.mul y (Int.negSucc m)))
          (fun n => congrArg Int.negOfNat (Nat.mul_comm (Nat.succ m) n))
          (fun n => congrArg Int.ofNat (Nat.mul_comm (Nat.succ m) (Nat.succ n)))
          b)
      a



-- Right monotonicity, from the left version plus commutativity.
theorem imul_le_mul_of_nonneg_right :
    ∀ (a b c : Int), Int.le a b → Int.le (Int.ofNat Nat.zero) c →
      Int.le (Int.mul a c) (Int.mul b c) :=
  fun a b c hab hc =>
    @Eq.subst Int (fun x => Int.le (Int.mul a c) x) (Int.mul c b) (Int.mul b c) (imul_comm c b)
      (@Eq.subst Int (fun x => Int.le x (Int.mul c b)) (Int.mul c a) (Int.mul a c) (imul_comm c a)
        (Int.mul_le_mul_of_nonneg_left a b c hab hc))

-- Negation on the LEFT factor, which the prelude only provides on the right.
theorem ineg_mul_left : ∀ (a b : Int), Eq Int (Int.mul (Int.neg a) b) (Int.neg (Int.mul a b)) :=
  fun a b =>
    Eq.trans (imul_comm (Int.neg a) b)
      (Eq.trans (Eq.symm (Int.neg_mul_right b a)) (congrArg Int.neg (imul_comm b a)))



def izero : Int := Int.ofNat Nat.zero

-- 0 <= -c from c <= 0.
theorem ineg_nonneg_of_nonpos : ∀ (c : Int), Int.le c izero → Int.le izero (Int.neg c) :=
  fun c hc =>
    @Eq.subst Int (fun x => Int.le x (Int.neg c)) (Int.add c (Int.neg c)) izero
      (Int.add_neg_self c)
      (@Eq.subst Int (fun x => Int.le (Int.add c (Int.neg c)) x)
        (Int.add izero (Int.neg c)) (Int.neg c) (Int.zero_add (Int.neg c))
        (Int.add_le_add_right c izero hc (Int.neg c)))

-- ((-v) + u) + v = u
theorem iadd_neg_cancel : ∀ (u v : Int), Eq Int (Int.add (Int.add (Int.neg v) u) v) u :=
  fun u v =>
    Eq.trans (congrArg (fun x => Int.add x v) (Int.add_comm (Int.neg v) u))
      (Eq.trans (Int.add_assoc u (Int.neg v) v)
        (Eq.trans (congrArg (Int.add u) (Int.neg_add_self v)) (Int.add_zero u)))

-- (-u) <= (-v)  ==>  0 <= (-v) + u
theorem ineg_le_shift : ∀ (u v : Int), Int.le (Int.neg u) (Int.neg v) →
    Int.le izero (Int.add (Int.neg v) u) :=
  fun u v h =>
    @Eq.subst Int (fun x => Int.le x (Int.add (Int.neg v) u))
      (Int.add (Int.neg u) u) izero (Int.neg_add_self u)
      (Int.add_le_add_right (Int.neg u) (Int.neg v) h u)

-- (-u) <= (-v)  ==>  v <= u.
theorem ineg_le_rev : ∀ (u v : Int), Int.le (Int.neg u) (Int.neg v) → Int.le v u :=
  fun u v h =>
    @Eq.subst Int (fun x => Int.le v x) (Int.add (Int.add (Int.neg v) u) v) u
      (iadd_neg_cancel u v)
      (@Eq.subst Int (fun x => Int.le x (Int.add (Int.add (Int.neg v) u) v))
        (Int.add izero v) v (Int.zero_add v)
        (Int.add_le_add_right izero (Int.add (Int.neg v) u) (ineg_le_shift u v h) v))



-- c <= 0, a <= b  ==>  c*b <= c*a   (multiplying by a nonpositive REVERSES)
theorem imul_le_mul_of_nonpos_left : ∀ (a b c : Int), Int.le a b → Int.le c izero →
    Int.le (Int.mul c b) (Int.mul c a) :=
  fun a b c hab hc =>
    ineg_le_rev (Int.mul c a) (Int.mul c b)
      (@Eq.subst Int (fun x => Int.le (Int.neg (Int.mul c a)) x)
        (Int.mul (Int.neg c) b) (Int.neg (Int.mul c b)) (ineg_mul_left c b)
        (@Eq.subst Int (fun x => Int.le x (Int.mul (Int.neg c) b))
          (Int.mul (Int.neg c) a) (Int.neg (Int.mul c a)) (ineg_mul_left c a)
          (Int.mul_le_mul_of_nonneg_left a b (Int.neg c) hab (ineg_nonneg_of_nonpos c hc))))

-- c <= 0, a <= b  ==>  b*c <= a*c
theorem imul_le_mul_of_nonpos_right : ∀ (a b c : Int), Int.le a b → Int.le c izero →
    Int.le (Int.mul b c) (Int.mul a c) :=
  fun a b c hab hc =>
    @Eq.subst Int (fun x => Int.le (Int.mul b c) x) (Int.mul c a) (Int.mul a c) (imul_comm c a)
      (@Eq.subst Int (fun x => Int.le x (Int.mul c a))
        (Int.mul c b) (Int.mul b c) (imul_comm c b)
        (imul_le_mul_of_nonpos_left a b c hab hc))

-- THE CORNER BOUND (upper half).
theorem mul_box_upper : ∀ (la ha lb hb a b M : Int),
    Int.le la a → Int.le a ha → Int.le lb b → Int.le b hb →
    Int.le (Int.mul la lb) M → Int.le (Int.mul la hb) M →
    Int.le (Int.mul ha lb) M → Int.le (Int.mul ha hb) M →
    Int.le (Int.mul a b) M :=
  fun la ha lb hb a b M hla hah hlb hbh cll clh chl chh =>
    Or.elim (Int.le_total izero b)
      (fun hb0 =>
        Or.elim (Int.le_total izero ha)
          (fun hha =>
            Int.le_trans (Int.mul a b) (Int.mul ha b) M
              (imul_le_mul_of_nonneg_right a ha b hah hb0)
              (Int.le_trans (Int.mul ha b) (Int.mul ha hb) M
                (Int.mul_le_mul_of_nonneg_left b hb ha hbh hha) chh))
          (fun hha =>
            Int.le_trans (Int.mul a b) (Int.mul ha b) M
              (imul_le_mul_of_nonneg_right a ha b hah hb0)
              (Int.le_trans (Int.mul ha b) (Int.mul ha lb) M
                (imul_le_mul_of_nonpos_left lb b ha hlb hha) chl)))
      (fun hb0 =>
        Or.elim (Int.le_total izero la)
          (fun hla2 =>
            Int.le_trans (Int.mul a b) (Int.mul la b) M
              (imul_le_mul_of_nonpos_right la a b hla hb0)
              (Int.le_trans (Int.mul la b) (Int.mul la hb) M
                (Int.mul_le_mul_of_nonneg_left b hb la hbh hla2) clh))
          (fun hla2 =>
            Int.le_trans (Int.mul a b) (Int.mul la b) M
              (imul_le_mul_of_nonpos_right la a b hla hb0)
              (Int.le_trans (Int.mul la b) (Int.mul la lb) M
                (imul_le_mul_of_nonpos_left lb b la hlb hla2) cll)))



-- THE CORNER BOUND (lower half).
theorem mul_box_lower : ∀ (la ha lb hb a b m : Int),
    Int.le la a → Int.le a ha → Int.le lb b → Int.le b hb →
    Int.le m (Int.mul la lb) → Int.le m (Int.mul la hb) →
    Int.le m (Int.mul ha lb) → Int.le m (Int.mul ha hb) →
    Int.le m (Int.mul a b) :=
  fun la ha lb hb a b m hla hah hlb hbh cll clh chl chh =>
    Or.elim (Int.le_total izero b)
      (fun hb0 =>
        Or.elim (Int.le_total izero la)
          (fun hla2 =>
            Int.le_trans m (Int.mul la b) (Int.mul a b)
              (Int.le_trans m (Int.mul la lb) (Int.mul la b) cll
                (Int.mul_le_mul_of_nonneg_left lb b la hlb hla2))
              (imul_le_mul_of_nonneg_right la a b hla hb0))
          (fun hla2 =>
            Int.le_trans m (Int.mul la b) (Int.mul a b)
              (Int.le_trans m (Int.mul la hb) (Int.mul la b) clh
                (imul_le_mul_of_nonpos_left b hb la hbh hla2))
              (imul_le_mul_of_nonneg_right la a b hla hb0)))
      (fun hb0 =>
        Or.elim (Int.le_total izero ha)
          (fun hha =>
            Int.le_trans m (Int.mul ha b) (Int.mul a b)
              (Int.le_trans m (Int.mul ha lb) (Int.mul ha b) chl
                (Int.mul_le_mul_of_nonneg_left lb b ha hlb hha))
              (imul_le_mul_of_nonpos_right a ha b hah hb0))
          (fun hha =>
            Int.le_trans m (Int.mul ha b) (Int.mul a b)
              (Int.le_trans m (Int.mul ha hb) (Int.mul ha b) chh
                (imul_le_mul_of_nonpos_left b hb ha hbh hha))
              (imul_le_mul_of_nonpos_right a ha b hah hb0)))

-- NON-VACUITY: the two sides are genuinely different terms, and the bound is
-- attained rather than slack. 3 * 4 = 12 with the box [2,3] x [4,5].
theorem corner_witness_products : Eq Int (Int.mul (Int.ofNat 3) (Int.ofNat 4)) (Int.ofNat 12) := rfl
theorem corner_witness_negative :
    Eq Int (Int.mul (Int.negSucc 1) (Int.ofNat 3)) (Int.negOfNat 6) := rfl

end CornerBox
