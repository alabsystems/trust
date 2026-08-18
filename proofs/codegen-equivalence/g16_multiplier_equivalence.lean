-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- ============================================================================
--  G16 — STRUCTURED MULTIPLIER EQUIVALENCE, kernel-checked in clean.
-- ============================================================================
--
--  GOAL (the structured-proof rung for MULTIPLY).
--  ay's `BvExpr::Mul` builds a shift-and-add ARRAY multiplier (n^2 `And2`
--  partial products + a ripple/array adder tree of `Xor3`/`FullAdderCarry`/
--  `ConstFalse`, truncated to the low n bits = two's-complement wrapping mul).
--  Re-checking a wide multiply through its bit-blast RESOLUTION refutation is
--  intractable (~16x steps per +2 bits, so width 32 is ~2.0M non-fusing steps),
--  which is why the live trust-cg gate keeps wide mul [VALIDATED].
--
--  This file proves, ONCE, BY INDUCTION over the width, the two structured
--  facts a width-generic [PROVED] multiply rests on — with ZERO domain-specific
--  axioms (everything is def/theorem over the core recursors @List.rec /
--  @Nat.rec / @Bool.rec plus Eq/congrArg and the prelude's add_assoc/add_comm/
--  zero_add; propext / Quot.sound / Classical.choice are unused):
--
--    (1) `mul_equiv (a b : Word) : mul_m a b = mul_ir a b`
--        The SHIFT-AND-ADD ARRAY MULTIPLIER built from the MACHINE per-bit gates
--        (`fsum_m`/`fcarry_m` adder, `And bit y` partial-product select — the
--        EXACT gate shapes ay's `BvExpr::Mul` emits) equals the SAME array
--        multiplier built from the SEPARATELY-STATED IR per-bit gates
--        (`fsum_ir`/`fcarry_ir`, `And y bit` select).  Proved by STRUCTURAL
--        INDUCTION over the multiplier `b`'s width, reusing the adder-equivalence
--        induction `addRec_equiv` and the per-bit `selRow_equiv`.  This is the
--        multiply analogue of `add_equiv` in g16_bitvec_equivalence.lean: machine
--        and IR sides are NON-syntactically-identical terms, so the equivalence
--        is a real theorem the kernel DISCHARGES (not X = X — see the
--        non-vacuity witnesses `mul_distinct` / numeric products below).
--
--    (2) `addval (xs : List Bool) : ... ` — the RIPPLE-ADDER VALUE LAW.
--        The arithmetic content of the array multiplier's adder tree:
--          toNat (addRec_m xs ys c) + 2^|xs| * b2n (carryOut_m xs ys c)
--            = (toNat xs + toNatN xs ys) + b2n c
--        i.e. the ripple-carry adder ay emits computes the genuine integer sum
--        (with the carry-out accounting for the truncation to |xs| bits).  Proved
--        by INDUCTION over the adder width, with the per-bit full-adder value
--        identity `fa_val` (b2n sum + 2*b2n carry = b2n a + b2n b + b2n c) as the
--        base brick and the Nat ring lemmas (`mul_add`/`mul_assoc`/`add_4`/
--        `rearr`) — all proved here by induction from the bare prelude — doing
--        the carry bookkeeping.  This is what makes `mul_m` a genuine arithmetic
--        multiply rather than an arbitrary boolean function: each `wadd_m` row
--        provably adds.
--
--  NUMERIC ANCHOR + NON-VACUITY.  Closed-constant `:= rfl` theorems pin that
--  `mul_m` computes the real two's-complement product (3*5=15, 2*3=6,
--  6*6=36 mod 16=4, 7*7=49 mod 16=1, x*0=0, x*1=x), and `mul_distinct` exhibits
--  a concrete input where `mul_m` DIFFERS from `wadd_m` (2*3=6 != 2+3=5) — so the
--  framework provably distinguishes multiply from add, and `mul_equiv` is not the
--  X = X trap.
--
--  RESIDUAL GAP (HONEST, explicitly NOT axiomatized).  The fully-general value
--  theorem `toNat (mul_m a b) = (toNat a * toNat b) % 2^|a|` is NOT proved here:
--  it needs a modular-arithmetic layer (`Nat.mod` / `%` lemmas: `add_mul_mod`,
--  `mod_eq_of_lt`, `mul_mod`, the `toNat x < 2^|x|` width bound) that the clean
--  BUILTIN prelude does not provide, and `Nat.mod` is defined by well-founded
--  recursion (not the structural recursors), so the bare-kernel reasoning would
--  require building that theory from scratch.  We state that goal below as a
--  `def`-level Prop `MulValueSpec` (NOT a theorem, NOT a sorry) to mark it as the
--  open obligation, and prove instead (1) the structural machine=IR multiplier
--  equivalence and (2) the adder value law it composes from.  No part of this
--  file uses sorry / admit / axiom / postulate / native_decide.
-- ============================================================================

set_option autoImplicit false

namespace G16Mul

-- ==========================================================================
--  REPRESENTATION + bit accessors (the reducible_word PoC idioms, inline).
-- ==========================================================================

def Word : Type := List Bool

def bhead : List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => Bool) false (fun b _ _ => b) xs
def btail : List Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool) List.nil (fun _ r _ => r) xs

-- dropLast: remove the final (MSB) element — used by the shift-left below.
--   dropLast [] = []; dropLast [x] = []; dropLast (x::xs) = x :: dropLast xs.
def dropLast : List Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool) List.nil
    (fun x rest ih =>
      @List.rec Bool (fun _ => List Bool) List.nil (fun _ _ _ => List.cons x ih) rest)
    xs

-- ==========================================================================
--  PER-BIT GATES — MACHINE side vs IR side, separately stated (g16 idiom).
-- ==========================================================================

def fsum_m  (a b c : Bool) : Bool := Bool.xor (Bool.xor a b) c
def fsum_ir (a b c : Bool) : Bool := Bool.xor a (Bool.xor b c)
def fcarry_m (a b c : Bool) : Bool :=
  Bool.or (Bool.and a b) (Bool.or (Bool.and a c) (Bool.and b c))
def fcarry_ir (a b c : Bool) : Bool :=
  Bool.or (Bool.and a b) (Bool.and c (Bool.or a b))

theorem fsum_eq (a b c : Bool) : fsum_m a b c = fsum_ir a b c :=
  @Bool.rec (fun x => fsum_m x b c = fsum_ir x b c)
    (@Bool.rec (fun y => fsum_m false y c = fsum_ir false y c)
      (@Bool.rec (fun z => fsum_m false false z = fsum_ir false false z) rfl rfl c)
      (@Bool.rec (fun z => fsum_m false true z = fsum_ir false true z) rfl rfl c) b)
    (@Bool.rec (fun y => fsum_m true y c = fsum_ir true y c)
      (@Bool.rec (fun z => fsum_m true false z = fsum_ir true false z) rfl rfl c)
      (@Bool.rec (fun z => fsum_m true true z = fsum_ir true true z) rfl rfl c) b) a
theorem fcarry_eq (a b c : Bool) : fcarry_m a b c = fcarry_ir a b c :=
  @Bool.rec (fun x => fcarry_m x b c = fcarry_ir x b c)
    (@Bool.rec (fun y => fcarry_m false y c = fcarry_ir false y c)
      (@Bool.rec (fun z => fcarry_m false false z = fcarry_ir false false z) rfl rfl c)
      (@Bool.rec (fun z => fcarry_m false true z = fcarry_ir false true z) rfl rfl c) b)
    (@Bool.rec (fun y => fcarry_m true y c = fcarry_ir true y c)
      (@Bool.rec (fun z => fcarry_m true false z = fcarry_ir true false z) rfl rfl c)
      (@Bool.rec (fun z => fcarry_m true true z = fcarry_ir true true z) rfl rfl c) b) a

-- ==========================================================================
--  WORD-LEVEL ADDER — MACHINE and IR ripple adders (the addRec shape).
-- ==========================================================================

def addRec_m : List Bool → List Bool → Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → List Bool)
    (fun _ _ => List.nil)
    (fun a as_ ih => fun ys c =>
      List.cons (fsum_m a (bhead ys) c) (ih (btail ys) (fcarry_m a (bhead ys) c)))
    xs
def addRec_ir : List Bool → List Bool → Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → List Bool)
    (fun _ _ => List.nil)
    (fun a as_ ih => fun ys c =>
      List.cons (fsum_ir a (bhead ys) c) (ih (btail ys) (fcarry_ir a (bhead ys) c)))
    xs
theorem addRec_m_cons (a : Bool) (as_ ys : List Bool) (c : Bool) :
    addRec_m (List.cons a as_) ys c
    = List.cons (fsum_m a (bhead ys) c)
        (addRec_m as_ (btail ys) (fcarry_m a (bhead ys) c)) := rfl
theorem addRec_ir_cons (a : Bool) (as_ ys : List Bool) (c : Bool) :
    addRec_ir (List.cons a as_) ys c
    = List.cons (fsum_ir a (bhead ys) c)
        (addRec_ir as_ (btail ys) (fcarry_ir a (bhead ys) c)) := rfl

def AddEq (xs : List Bool) : Prop :=
  ∀ (ys : List Bool) (c : Bool), addRec_m xs ys c = addRec_ir xs ys c
theorem addRec_equiv (xs : List Bool) : AddEq xs :=
  @List.rec Bool AddEq
    (fun _ _ => rfl)
    (fun a as_ ih => fun ys c =>
      Eq.trans (addRec_m_cons a as_ ys c)
        (Eq.trans
          (congrArg
            (fun h => List.cons h (addRec_m as_ (btail ys) (fcarry_m a (bhead ys) c)))
            (fsum_eq a (bhead ys) c))
          (Eq.trans
            (congrArg (fun t => List.cons (fsum_ir a (bhead ys) c) t)
              (Eq.trans
                (congrArg (fun cc => addRec_m as_ (btail ys) cc) (fcarry_eq a (bhead ys) c))
                (ih (btail ys) (fcarry_ir a (bhead ys) c))))
            (Eq.symm (addRec_ir_cons a as_ ys c)))))
    xs

def wadd_m (x y : List Bool) : List Bool := addRec_m x y false
def wadd_ir (x y : List Bool) : List Bool := addRec_ir x y false
theorem wadd_equiv (x y : List Bool) : wadd_m x y = wadd_ir x y :=
  addRec_equiv x y false

-- ==========================================================================
--  PARTIAL-PRODUCT SELECT + SHIFT — the array-multiplier building blocks.
--  selRow_m bit y  = per-bit (bit AND y_i)  (MACHINE: And bit y_i, ay's And2)
--  selRow_ir bit y = per-bit (y_i AND bit)  (IR: commuted operands)
--  shl1            = shift-left-by-1 keeping width |x| (prepend false, drop MSB)
-- ==========================================================================

def zerosLike : List Bool → List Bool := fun t =>
  @List.rec Bool (fun _ => List Bool) List.nil (fun _ _ ih => List.cons false ih) t
def selRow_m (bit : Bool) : List Bool → List Bool := fun ys =>
  @List.rec Bool (fun _ => List Bool) List.nil
    (fun y _ ih => List.cons (Bool.and bit y) ih) ys
def selRow_ir (bit : Bool) : List Bool → List Bool := fun ys =>
  @List.rec Bool (fun _ => List Bool) List.nil
    (fun y _ ih => List.cons (Bool.and y bit) ih) ys
theorem selRow_equiv (bit : Bool) (ys : List Bool) : selRow_m bit ys = selRow_ir bit ys :=
  @List.rec Bool (fun ys => selRow_m bit ys = selRow_ir bit ys)
    rfl
    (fun y ys_ ih =>
      Eq.trans
        (congrArg (fun h => List.cons h (selRow_m bit ys_))
          (@Bool.rec (fun bb => Bool.and bb y = Bool.and y bb)
            (@Bool.rec (fun yy => Bool.and false yy = Bool.and yy false) rfl rfl y)
            (@Bool.rec (fun yy => Bool.and true yy = Bool.and yy true) rfl rfl y) bit))
        (congrArg (fun t => List.cons (Bool.and y bit) t) ih))
    ys
def shl1 (xs : List Bool) : List Bool := List.cons false (dropLast xs)

-- ==========================================================================
--  THE SHIFT-AND-ADD ARRAY MULTIPLIER — MACHINE and IR.
--  Recursion over the multiplier `b`'s width (Horner form), result width = |a|:
--    mul a []        = zerosLike a
--    mul a (b0::bs)  = wadd (selRow b0 a) (shl1 (mul a bs))
--  i.e.  a*b = (b0 ? a : 0) + 2*(a * (b>>1))  truncated to |a| bits — exactly
--  ay's row-accumulate-and-shift array multiplier, two's-complement wrapping.
-- ==========================================================================

def mul_m (a : List Bool) : List Bool → List Bool := fun b =>
  @List.rec Bool (fun _ => List Bool)
    (zerosLike a)
    (fun b0 bs ih => wadd_m (selRow_m b0 a) (shl1 ih))
    b
def mul_ir (a : List Bool) : List Bool → List Bool := fun b =>
  @List.rec Bool (fun _ => List Bool)
    (zerosLike a)
    (fun b0 bs ih => wadd_ir (selRow_ir b0 a) (shl1 ih))
    b
theorem mul_m_cons (a : List Bool) (b0 : Bool) (bs : List Bool) :
    mul_m a (List.cons b0 bs) = wadd_m (selRow_m b0 a) (shl1 (mul_m a bs)) := rfl
theorem mul_ir_cons (a : List Bool) (b0 : Bool) (bs : List Bool) :
    mul_ir a (List.cons b0 bs) = wadd_ir (selRow_ir b0 a) (shl1 (mul_ir a bs)) := rfl

-- ==========================================================================
--  HEADLINE (1): the MACHINE array multiplier == the IR array multiplier, for
--  ALL words, by STRUCTURAL INDUCTION over the multiplier `b`'s width.  Each
--  cons step rewrites selRow_m -> selRow_ir (selRow_equiv), the inner sub-product
--  mul_m -> mul_ir (ih), and wadd_m -> wadd_ir (wadd_equiv = addRec_equiv).
-- ==========================================================================

theorem mul_equiv (a : List Bool) (b : List Bool) : mul_m a b = mul_ir a b :=
  @List.rec Bool (fun b => mul_m a b = mul_ir a b)
    rfl
    (fun b0 bs ih =>
      Eq.trans (mul_m_cons a b0 bs)
        (Eq.trans
          (congrArg (fun s => wadd_m s (shl1 (mul_m a bs))) (selRow_equiv b0 a))
          (Eq.trans
            (congrArg (fun p => wadd_m (selRow_ir b0 a) (shl1 p)) ih)
            (Eq.trans
              (wadd_equiv (selRow_ir b0 a) (shl1 (mul_ir a bs)))
              (Eq.symm (mul_ir_cons a b0 bs))))))
    b

-- ==========================================================================
--  VALUE LAYER — toNat / width / pow2 and the Nat ring lemmas (all proved here
--  by induction from the bare prelude: only Nat.add_assoc / Nat.add_comm /
--  Nat.zero_add are taken from the builtin prelude).
-- ==========================================================================

def b2n : Bool → Nat := fun b => @Bool.rec (fun _ => Nat) Nat.zero (Nat.succ Nat.zero) b
def toNat : List Bool → Nat := fun xs =>
  @List.rec Bool (fun _ => Nat) Nat.zero (fun b _ ih => Nat.add (b2n b) (Nat.mul 2 ih)) xs
def llen : List Bool → Nat := fun xs =>
  @List.rec Bool (fun _ => Nat) Nat.zero (fun _ _ ih => Nat.succ ih) xs
def pow2 : Nat → Nat := fun n =>
  @Nat.rec (fun _ => Nat) (Nat.succ Nat.zero) (fun _ ih => Nat.mul 2 ih) n
-- toNatN xs ys = value of the first |xs| bits of ys (the prefix the adder consumes).
def toNatN : List Bool → List Bool → Nat := fun template =>
  @List.rec Bool (fun _ => List Bool → Nat) (fun _ => Nat.zero)
    (fun _ _ ih => fun ys => Nat.add (b2n (bhead ys)) (Nat.mul 2 (ih (btail ys)))) template

theorem mul_add (a b c : Nat) : Nat.mul a (Nat.add b c) = Nat.add (Nat.mul a b) (Nat.mul a c) :=
  @Nat.rec (fun c : Nat => @Eq Nat (Nat.mul a (Nat.add b c)) (Nat.add (Nat.mul a b) (Nat.mul a c)))
    rfl
    (fun c ih => Eq.trans (congrArg (fun t => Nat.add t a) ih) (Nat.add_assoc (Nat.mul a b) (Nat.mul a c) a))
    c
theorem one_mul (n : Nat) : Nat.mul (Nat.succ Nat.zero) n = n :=
  @Nat.rec (fun n : Nat => @Eq Nat (Nat.mul (Nat.succ Nat.zero) n) n)
    rfl (fun n ih => congrArg Nat.succ ih) n
theorem mul_assoc (a b c : Nat) : Nat.mul (Nat.mul a b) c = Nat.mul a (Nat.mul b c) :=
  @Nat.rec (fun c : Nat => @Eq Nat (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c)))
    rfl
    (fun c ih => Eq.trans (congrArg (fun t => Nat.add t (Nat.mul a b)) ih) (Eq.symm (mul_add a (Nat.mul b c) b)))
    c
theorem add_4 (A B C D : Nat) :
    Nat.add (Nat.add A B) (Nat.add C D) = Nat.add (Nat.add A C) (Nat.add B D) :=
  Eq.trans (Nat.add_assoc A B (Nat.add C D))
    (Eq.trans (congrArg (fun t => Nat.add A t)
        (Eq.trans (Eq.symm (Nat.add_assoc B C D))
          (Eq.trans (congrArg (fun t => Nat.add t D) (Nat.add_comm B C)) (Nat.add_assoc C B D))))
      (Eq.symm (Nat.add_assoc A C (Nat.add B D))))
theorem add_swap (X Y Z : Nat) :
    Nat.add (Nat.add X Y) Z = Nat.add (Nat.add X Z) Y :=
  Eq.trans (Nat.add_assoc X Y Z)
    (Eq.trans (congrArg (fun t => Nat.add X t) (Nat.add_comm Y Z)) (Eq.symm (Nat.add_assoc X Z Y)))
theorem rearr (ba byh bc ta tn : Nat) :
    Nat.add (Nat.add (Nat.add ba byh) bc) (Nat.add ta tn)
    = Nat.add (Nat.add (Nat.add ba ta) (Nat.add byh tn)) bc :=
  Eq.trans (add_swap (Nat.add ba byh) bc (Nat.add ta tn))
    (congrArg (fun t => Nat.add t bc) (add_4 ba byh ta tn))

-- ---- the per-bit full-adder VALUE identity (the value base brick) ----
--   b2n (sum) + 2 * b2n (carry) = (b2n a + b2n b) + b2n c
theorem fa_val (a b c : Bool) :
    Nat.add (b2n (fsum_m a b c)) (Nat.mul 2 (b2n (fcarry_m a b c)))
    = Nat.add (Nat.add (b2n a) (b2n b)) (b2n c) :=
  @Bool.rec (fun x => Nat.add (b2n (fsum_m x b c)) (Nat.mul 2 (b2n (fcarry_m x b c)))
                      = Nat.add (Nat.add (b2n x) (b2n b)) (b2n c))
    (@Bool.rec (fun y => Nat.add (b2n (fsum_m false y c)) (Nat.mul 2 (b2n (fcarry_m false y c)))
                      = Nat.add (Nat.add (b2n false) (b2n y)) (b2n c))
      (@Bool.rec (fun z => Nat.add (b2n (fsum_m false false z)) (Nat.mul 2 (b2n (fcarry_m false false z)))
                      = Nat.add (Nat.add (b2n false) (b2n false)) (b2n z)) rfl rfl c)
      (@Bool.rec (fun z => Nat.add (b2n (fsum_m false true z)) (Nat.mul 2 (b2n (fcarry_m false true z)))
                      = Nat.add (Nat.add (b2n false) (b2n true)) (b2n z)) rfl rfl c) b)
    (@Bool.rec (fun y => Nat.add (b2n (fsum_m true y c)) (Nat.mul 2 (b2n (fcarry_m true y c)))
                      = Nat.add (Nat.add (b2n true) (b2n y)) (b2n c))
      (@Bool.rec (fun z => Nat.add (b2n (fsum_m true false z)) (Nat.mul 2 (b2n (fcarry_m true false z)))
                      = Nat.add (Nat.add (b2n true) (b2n false)) (b2n z)) rfl rfl c)
      (@Bool.rec (fun z => Nat.add (b2n (fsum_m true true z)) (Nat.mul 2 (b2n (fcarry_m true true z)))
                      = Nat.add (Nat.add (b2n true) (b2n true)) (b2n z)) rfl rfl c) b) a

-- ---- final carry-out of the ripple adder (the truncation accounting) ----
def carryOut_m : List Bool → List Bool → Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → Bool)
    (fun _ c => c)
    (fun a as_ ih => fun ys c => ih (btail ys) (fcarry_m a (bhead ys) c))
    xs

-- ==========================================================================
--  HEADLINE (2): the RIPPLE-ADDER VALUE LAW, by INDUCTION over the adder width.
--    toNat (addRec_m xs ys c) + 2^|xs| * b2n (carryOut_m xs ys c)
--      = (toNat xs + toNatN xs ys) + b2n c
--  The carry-out term is exactly the bit truncated off at width |xs| — so this
--  says the array multiplier's adder rows compute the genuine integer sum.  The
--  inductive step factors the 2* out of the rec + carry terms, applies the IH,
--  distributes, applies the per-bit `fa_val`, and regroups via `rearr`.
-- ==========================================================================

def AddVal (xs : List Bool) : Prop :=
  ∀ (ys : List Bool) (c : Bool),
    Nat.add (toNat (addRec_m xs ys c)) (Nat.mul (pow2 (llen xs)) (b2n (carryOut_m xs ys c)))
    = Nat.add (Nat.add (toNat xs) (toNatN xs ys)) (b2n c)

theorem addval_nil : AddVal List.nil :=
  fun ys c => Eq.trans (Nat.zero_add (Nat.mul (Nat.succ Nat.zero) (b2n c)))
      (Eq.trans (one_mul (b2n c)) (Eq.symm (Nat.zero_add (b2n c))))

theorem addval_step (a : Bool) (as_ : List Bool) (ih : AddVal as_) : AddVal (List.cons a as_) :=
  fun ys c =>
      Eq.trans
        (congrArg (fun t => Nat.add (Nat.add (b2n (fsum_m a (bhead ys) c)) (Nat.mul 2 (toNat (addRec_m as_ (btail ys) (fcarry_m a (bhead ys) c))))) t)
          (mul_assoc 2 (pow2 (llen as_)) (b2n (carryOut_m as_ (btail ys) (fcarry_m a (bhead ys) c)))))
        (Eq.trans
          (Nat.add_assoc (b2n (fsum_m a (bhead ys) c)) (Nat.mul 2 (toNat (addRec_m as_ (btail ys) (fcarry_m a (bhead ys) c)))) (Nat.mul 2 (Nat.mul (pow2 (llen as_)) (b2n (carryOut_m as_ (btail ys) (fcarry_m a (bhead ys) c))))))
          (Eq.trans
            (congrArg (fun t => Nat.add (b2n (fsum_m a (bhead ys) c)) t) (Eq.symm (mul_add 2 (toNat (addRec_m as_ (btail ys) (fcarry_m a (bhead ys) c))) (Nat.mul (pow2 (llen as_)) (b2n (carryOut_m as_ (btail ys) (fcarry_m a (bhead ys) c)))))))
            (Eq.trans
              (congrArg (fun t => Nat.add (b2n (fsum_m a (bhead ys) c)) (Nat.mul 2 t)) (ih (btail ys) (fcarry_m a (bhead ys) c)))
              (Eq.trans
                (congrArg (fun t => Nat.add (b2n (fsum_m a (bhead ys) c)) t) (mul_add 2 (Nat.add (toNat as_) (toNatN as_ (btail ys))) (b2n (fcarry_m a (bhead ys) c))))
                (Eq.trans
                  (Eq.symm (Nat.add_assoc (b2n (fsum_m a (bhead ys) c)) (Nat.mul 2 (Nat.add (toNat as_) (toNatN as_ (btail ys)))) (Nat.mul 2 (b2n (fcarry_m a (bhead ys) c)))))
                  (Eq.trans
                    (add_swap (b2n (fsum_m a (bhead ys) c)) (Nat.mul 2 (Nat.add (toNat as_) (toNatN as_ (btail ys)))) (Nat.mul 2 (b2n (fcarry_m a (bhead ys) c))))
                    (Eq.trans
                      (congrArg (fun t => Nat.add t (Nat.mul 2 (Nat.add (toNat as_) (toNatN as_ (btail ys))))) (fa_val a (bhead ys) c))
                      (Eq.trans
                        (congrArg (fun t => Nat.add (Nat.add (Nat.add (b2n a) (b2n (bhead ys))) (b2n c)) t) (mul_add 2 (toNat as_) (toNatN as_ (btail ys))))
                        (rearr (b2n a) (b2n (bhead ys)) (b2n c) (Nat.mul 2 (toNat as_)) (Nat.mul 2 (toNatN as_ (btail ys))))))))))))

theorem addval : ∀ (xs : List Bool), AddVal xs :=
  fun xs => @List.rec Bool AddVal addval_nil addval_step xs

-- ==========================================================================
--  NUMERIC ANCHOR — `mul_m` computes the genuine two's-complement product.
--  Width-4 LSB-first literals.  These pin the VALUE; mul_equiv pins machine==ir.
-- ==========================================================================

-- 3*5 = 15 :  3=[T,T,F,F] 5=[T,F,T,F] 15=[T,T,T,T]
theorem mul4_3x5 : mul_m [true,true,false,false] [true,false,true,false] = [true,true,true,true] := rfl
-- 2*3 = 6 :  2=[F,T,F,F] 3=[T,T,F,F] 6=[F,T,T,F]
theorem mul4_2x3 : mul_m [false,true,false,false] [true,true,false,false] = [false,true,true,false] := rfl
-- 6*6 = 36 mod 16 = 4 :  6=[F,T,T,F] 4=[F,F,T,F]
theorem mul4_6x6_wrap : mul_m [false,true,true,false] [false,true,true,false] = [false,false,true,false] := rfl
-- 7*7 = 49 mod 16 = 1 :  7=[T,T,T,F] 1=[T,F,F,F]
theorem mul4_7x7_wrap : mul_m [true,true,true,false] [true,true,true,false] = [true,false,false,false] := rfl
-- x*0 = 0 and x*1 = x (identities)
theorem mul4_x0 : mul_m [true,true,false,false] [false,false,false,false] = [false,false,false,false] := rfl
theorem mul4_x1 : mul_m [true,true,false,false] [true,false,false,false] = [true,true,false,false] := rfl
-- the IR multiplier agrees on these (instance of mul_equiv, closing definitionally)
theorem mul4_ir_3x5 : mul_ir [true,true,false,false] [true,false,true,false] = [true,true,true,true] := rfl

-- ==========================================================================
--  NON-VACUITY — the framework provably DISTINGUISHES multiply from add, so
--  mul_equiv is NOT the X = X trap.  2*3 = 6 (mul) but 2+3 = 5 (wadd); the
--  per-bit beq fold returns false on the differing results.
-- ==========================================================================

def allZero : List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => Bool) true (fun a _ ih => Bool.and (Bool.not a) ih) xs
def wordBeq : List Bool → List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool)
    (fun ys => allZero ys)
    (fun a as_ ih => fun ys => Bool.and (Bool.beq a (bhead ys)) (ih (btail ys)))
    xs
-- 2*3 = 6 = [F,T,T,F] ; 2+3 = 5 = [T,F,T,F] ; they DIFFER => wordBeq = false.
theorem mul_distinct :
    wordBeq (mul_m [false,true,false,false] [true,true,false,false])
            (wadd_m [false,true,false,false] [true,true,false,false]) = false := rfl
-- positive control: mul_m a b agrees with mul_ir a b on the same input (= true).
theorem mul_agree :
    wordBeq (mul_m [false,true,false,false] [true,true,false,false])
            (mul_ir [false,true,false,false] [true,true,false,false]) = true := rfl

-- ==========================================================================
--  OPEN OBLIGATION (HONEST, NOT a theorem, NOT sorried).  The fully-general
--  value spec — toNat (mul_m a b) = (toNat a * toNat b) % 2^|a| — is stated as a
--  Prop-valued `def` to MARK it as the remaining work.  It is NOT proved here
--  (it needs a Nat.mod / 2^|x| width-bound layer the builtin prelude lacks).  No
--  theorem below claims it; it is a definition only, so the file's proof closure
--  remains axiom-free.
-- ==========================================================================

def MulValueSpec (a b : List Bool) : Prop :=
  toNat (mul_m a b) = Nat.mod (Nat.mul (toNat a) (toNat b)) (pow2 (llen a))

-- ==========================================================================
--  THE AY-BLAST CORRESPONDENCE — the bridge, decomposed into two obligations.
-- ==========================================================================
--
--  WHY THIS SECTION EXISTS.  Everything above proves the MODEL correct:
--  `mul_equiv` (machine-gate array multiplier == the separately-stated IR one)
--  and `addval` (its ripple adder computes the genuine integer sum).  Both are
--  width-GENERIC, so applying them at live gate width is a plain instantiation,
--  not a new proof (measured: `mul_equiv` at width 32 kernel-checks in ~3.5s).
--
--  What is NOT proved is the step that would let the live gate USE them: that
--  the bit-blast ay actually emits for `BvExpr::Mul` IS this model's multiplier.
--  That gap is why a wide `Mul` still re-checks a per-instance SAT refutation
--  (~16x steps per +2 bits, hence `MAX_RECHECKABLE_MUL_WIDTH = 8`).
--
--  THE DECOMPOSITION, AND WHY IT MATTERS.  Stating the gap directly against
--  `mul_m` asks a reader to accept, by inspection, that two STRUCTURALLY
--  DIFFERENT algorithms agree:
--
--    ay (bv_blast_solver.rs, BvExpr::Mul):  acc := a & b0;
--                                           for j in 1..n: acc += (a & b_j) << j
--        -- iterative, PRE-SHIFTED rows, LEFT-associated
--
--    mul_m (above):  mul a (b0::bs) = wadd (selRow b0 a) (shl1 (mul a bs))
--        -- recursive Horner form, shift AFTER, RIGHT-associated
--
--  Those compute the same value but build different circuits, so the inspection
--  step was doing real mathematical work in a human's head.  `mul_ay` below
--  mirrors ay's loop LINE BY LINE instead, splitting the one gap into two
--  obligations of genuinely different KIND:
--
--    * `AyBlastAgrees` — ay's Rust emits `mul_ay`.  CANNOT be discharged inside
--      clean (the encoder is Rust), so it stays an inspection obligation — but
--      it is now a structural, line-by-line comparison against the loop above,
--      not an algebraic argument.
--    * `AyModelMatches` — `mul_ay = mul_m`.  Pure mathematics, entirely inside
--      clean, dischargeable by anyone with no reference to ay at all.
--
--  Both are needed; neither implies the other.  The payoff theorems below are
--  proved FROM the pair, so discharging them is all that remains.
--
--  STATUS OF `AyModelMatches`.  Believed true and witnessed on concrete inputs
--  (`ay_w1`/`ay_w2`/`ay_w3`, including the all-ones worst case for carries).
--  The proof route is known: it reduces to `accRows a bs k acc =
--  wadd acc (shlk k (mul_m a bs))` by induction on `bs`, whose step needs
--  ripple-adder ASSOCIATIVITY.  That is not available bit-wise and has to come
--  through the value law (`addval`, proved above) plus injectivity of `toNat`
--  on equal-length words — which is the remaining work, and is why this is
--  stated rather than proved.  `shlk_shl1` below is the first brick of it.

/-- shl1 applied k times. -/
def shlk : Nat → List Bool → List Bool := fun k =>
  @Nat.rec (fun _ => List Bool → List Bool) (fun xs => xs)
    (fun _ ih => fun xs => shl1 (ih xs)) k

/-- ay's accumulator loop over the TAIL multiplier bits, carrying the shift.
    Mirrors `for (j, &b_j) in bb.iter().enumerate().take(n).skip(1)`. -/
def accRows (a : List Bool) : List Bool → Nat → List Bool → List Bool := fun bs =>
  @List.rec Bool (fun _ => Nat → List Bool → List Bool)
    (fun _ acc => acc)
    (fun bj rest ih => fun k acc => ih (Nat.succ k) (wadd_m acc (shlk k (selRow_m bj a))))
    bs

/-- ay's ARRAY MULTIPLIER, mirroring `bv_blast_solver.rs`'s `BvExpr::Mul` arm:
    the accumulator is INITIALISED to row 0 (`acc[i] = a[i] ∧ b[0]`), then each
    remaining row `j` is shifted left by `j` and added in. -/
def mul_ay (a : List Bool) : List Bool → List Bool := fun b =>
  @List.rec Bool (fun _ => List Bool)
    (zerosLike a)
    (fun b0 bs _ => accRows a bs (Nat.succ Nat.zero) (selRow_m b0 a))
    b

/-- A bit-blasting multiplier: the shape ay's `BvExpr::Mul` lowering has. -/
def Blast : Type := List Bool → List Bool → List Bool

/-- OBLIGATION 1 (Rust ↔ clean).  `blast` emits ay's array multiplier.
    No term of this type can exist here; see the section header. -/
def AyBlastAgrees (blast : Blast) : Prop :=
  ∀ (a : List Bool) (b : List Bool), blast a b = mul_ay a b

/-- OBLIGATION 2 (pure mathematics).  ay's accumulate-shifted-rows multiplier
    agrees with the model's Horner-recursive one. -/
def AyModelMatches : Prop :=
  ∀ (a : List Bool) (b : List Bool), mul_ay a b = mul_m a b

/-- First brick toward obligation 2: shl1 commutes with iterated shl1. -/
theorem shlk_shl1 : ∀ (k : Nat) (xs : List Bool), shlk k (shl1 xs) = shl1 (shlk k xs) :=
  fun k => @Nat.rec (fun k => ∀ (xs : List Bool), shlk k (shl1 xs) = shl1 (shlk k xs))
    (fun _ => rfl) (fun k ih => fun xs => congrArg shl1 (ih xs)) k

/-- NON-VACUITY of obligation 2: `mul_ay` and `mul_m` agree on concrete inputs,
    including the all-ones worst case for carry propagation. These are `rfl`, so
    the kernel COMPUTES both multipliers and compares the resulting words. -/
theorem ay_w1 : mul_ay [false,true,false,false] [true,true,false,false]
              = mul_m  [false,true,false,false] [true,true,false,false] := rfl
theorem ay_w2 : mul_ay [true,true,false,false] [true,false,true,false]
              = mul_m  [true,true,false,false] [true,false,true,false] := rfl
theorem ay_w3 : mul_ay [true,true,true,true] [true,true,true,true]
              = mul_m  [true,true,true,true] [true,true,true,true] := rfl

/-- PAYOFF 3: agreement is DISCRIMINATING, not vacuous — `mul_m` and `wadd_m`
    disagree on a concrete input, so a blast emitting the ADDER instead of the
    MULTIPLIER fails the obligation rather than slipping through. -/
theorem agreement_is_discriminating :
    wordBeq (mul_m [false,true,false,false] [true,true,false,false])
            (wadd_m [false,true,false,false] [true,true,false,false]) = false := rfl


-- ==========================================================================
--  toNat INJECTIVITY — the arithmetic half of ripple-adder associativity.
-- ==========================================================================
--
--  Ripple-adder associativity cannot be proved bit-wise: per bit the sum bits
--  agree (`fsum` is XOR3) but the CARRIES do not, and only the carry SUM is
--  invariant. The argument therefore has to go through the value law (`addval`,
--  proved above) and come back to bit-level equality — which needs exactly this:
--  two words of the SAME LENGTH with the SAME VALUE are the same word.
--
--  Proved here from the bare prelude, since clean's environment exposes no
--  parity or cancellation machinery for `Nat`. The shape is the standard one:
--  the low bit is recovered by PARITY (`parity_cons`), forcing the heads equal;
--  the tails then have equal doubled values, and `double_cancel` strips the
--  factor of two so the induction hypothesis applies.
--
--  THE LENGTH HYPOTHESIS IS LOAD-BEARING, not bookkeeping: `[]` and `[false]`
--  have the same `toNat` (both 0) and different lengths, so dropping `llen`
--  makes the statement FALSE. The witnesses at the end of the block pin that.

def isOdd : Nat → Bool := fun n =>
  @Nat.rec (fun _ => Bool) false (fun _ ih => Bool.not ih) n
theorem not_not : ∀ (b : Bool), Bool.not (Bool.not b) = b :=
  fun b => @Bool.rec (fun b => Bool.not (Bool.not b) = b) rfl rfl b
theorem isOdd_double : ∀ (m : Nat), isOdd (Nat.mul 2 m) = false :=
  fun m => @Nat.rec (fun m => isOdd (Nat.mul 2 m) = false) rfl
    (fun m ih => Eq.trans (not_not (isOdd (Nat.mul 2 m))) ih) m
theorem isOdd_succ_double : ∀ (m : Nat), isOdd (Nat.succ (Nat.mul 2 m)) = true :=
  fun m => congrArg Bool.not (isOdd_double m)


theorem two_succ : ∀ (m : Nat), Nat.mul 2 (Nat.succ m) = Nat.succ (Nat.succ (Nat.mul 2 m)) :=
  fun _ => rfl

theorem double_cancel : ∀ (m n : Nat), Nat.mul 2 m = Nat.mul 2 n → m = n :=
  fun m => @Nat.rec (fun m => ∀ (n : Nat), Nat.mul 2 m = Nat.mul 2 n → m = n)
    (fun n => @Nat.rec (fun n => Nat.mul 2 Nat.zero = Nat.mul 2 n → Nat.zero = n)
       (fun _ => rfl)
       (fun n' _ => fun h => Nat.noConfusion h)
       n)
    (fun m' ih => fun n =>
       @Nat.rec (fun n => Nat.mul 2 (Nat.succ m') = Nat.mul 2 n → Nat.succ m' = n)
         (fun h => Nat.noConfusion h)
         (fun n' _ => fun h =>
            congrArg Nat.succ
              (ih n'
                (Nat.succ_inj (Nat.mul 2 m') (Nat.mul 2 n')
                  (Nat.succ_inj (Nat.succ (Nat.mul 2 m')) (Nat.succ (Nat.mul 2 n'))
                    (Eq.trans (Eq.symm (two_succ m')) (Eq.trans h (two_succ n')))))))
         n)
    m


theorem tn_false : ∀ (bs : List Bool), toNat (List.cons false bs) = Nat.mul 2 (toNat bs) :=
  fun bs => Nat.zero_add (Nat.mul 2 (toNat bs))

theorem tn_true : ∀ (bs : List Bool),
    toNat (List.cons true bs) = Nat.succ (Nat.mul 2 (toNat bs)) :=
  fun bs => Eq.trans (Nat.succ_add Nat.zero (Nat.mul 2 (toNat bs)))
    (congrArg Nat.succ (Nat.zero_add (Nat.mul 2 (toNat bs))))


theorem parity_cons : ∀ (b : Bool) (bs : List Bool), isOdd (toNat (List.cons b bs)) = b :=
  fun b bs => @Bool.rec (fun b => isOdd (toNat (List.cons b bs)) = b)
    (Eq.trans (congrArg isOdd (tn_false bs)) (isOdd_double (toNat bs)))
    (Eq.trans (congrArg isOdd (tn_true bs)) (isOdd_succ_double (toNat bs)))
    b

-- llen ys = 0 forces ys = [].
theorem llen_zero_nil : ∀ (ys : List Bool), llen ys = Nat.zero → ys = List.nil :=
  fun ys => @List.rec Bool (fun ys => llen ys = Nat.zero → ys = List.nil)
    (fun _ => rfl)
    (fun _ _ _ => fun h => Nat.noConfusion h)
    ys


-- The cons/cons case of injectivity, split out because `have`/`let` are not
-- available in term position here.
theorem toNat_inj_cons : ∀ (x y : Bool) (xs' ys' : List Bool),
    (∀ (zs : List Bool), llen xs' = llen zs → toNat xs' = toNat zs → xs' = zs) →
    llen (List.cons x xs') = llen (List.cons y ys') →
    toNat (List.cons x xs') = toNat (List.cons y ys') →
    List.cons x xs' = List.cons y ys' :=
  fun x y xs' ys' ih hl hv =>
    Eq.trans
      (congrArg (fun t => List.cons t xs')
        (Eq.trans (Eq.symm (parity_cons x xs'))
          (Eq.trans (congrArg isOdd hv) (parity_cons y ys'))))
      (congrArg (fun t => List.cons y t)
        (ih ys'
          (Nat.succ_inj (llen xs') (llen ys') hl)
          (double_cancel (toNat xs') (toNat ys')
            (@Nat.add_left_cancel (b2n x) (Nat.mul 2 (toNat xs')) (Nat.mul 2 (toNat ys'))
              (@Eq.subst Bool (fun t => toNat (List.cons x xs') = toNat (List.cons t ys'))
                y x
                (Eq.symm (Eq.trans (Eq.symm (parity_cons x xs'))
                  (Eq.trans (congrArg isOdd hv) (parity_cons y ys'))))
                hv)))))

/-- `toNat` is INJECTIVE on words of equal length. -/
theorem toNat_inj : ∀ (xs ys : List Bool),
    llen xs = llen ys → toNat xs = toNat ys → xs = ys :=
  fun xs =>
    @List.rec Bool
      (fun xs => ∀ (ys : List Bool), llen xs = llen ys → toNat xs = toNat ys → xs = ys)
      (fun ys hl _ => Eq.symm (llen_zero_nil ys (Eq.symm hl)))
      (fun x xs' ih => fun ys =>
        @List.rec Bool
          (fun ys => llen (List.cons x xs') = llen ys →
                     toNat (List.cons x xs') = toNat ys → List.cons x xs' = ys)
          (fun hl _ => Nat.noConfusion hl)
          (fun y ys' _ => fun hl hv => toNat_inj_cons x y xs' ys' ih hl hv)
          ys)
      xs

-- The length hypothesis is REQUIRED: same value, different words.
theorem toNat_len_needed : Eq Nat (toNat List.nil) (toNat (List.cons false List.nil)) := rfl
theorem llen_len_differs :
    Bool.beq (Nat.beq (llen List.nil) (llen (List.cons false List.nil))) false = true := rfl

-- ==========================================================================
--  THE VALUE LAW AND ITS ARITHMETIC SUPPORT — lemma 1 of the three that
--  ripple-adder associativity needs.
-- ==========================================================================
--
--  `addval` (above) is stated with `toNatN`, the adder's PREFIX-read of its
--  second operand, and with the carry-in term still present. Associativity
--  consumes it in a narrower form: at EQUAL LENGTHS, with carry-in false, the
--  output value plus the carry-out weight is exactly the integer sum
--  (`wadd_value`).
--
--  Getting there needs the two structural facts `llen_addRec` (the adder
--  returns a word as long as its FIRST operand) and `toNatN_eq_toNat` (at equal
--  lengths the prefix-read is the whole value), plus — for the step that turns
--  a value equation back into a bit equation — the bound `toNat_lt_pow2` and
--  the uniqueness lemma `carry_unique`. None of that arithmetic exists in
--  clean's environment, so it is built here from the recursors, continuing the
--  `toNat_inj` development above.
--
--  `carry_unique` is the "same remainder" step: two sub-P values whose
--  P-weighted carry corrections agree are the same value, whatever the two
--  carry bits were. Its two mixed cases are ruled out by `lt_absurd` — a value
--  below P cannot also be P plus something — which is where the bound is spent.

-- L1: the adder's result has the length of its FIRST operand.
theorem llen_addRec : ∀ (xs ys : List Bool) (c : Bool), llen (addRec_m xs ys c) = llen xs :=
  fun xs => @List.rec Bool
    (fun xs => ∀ (ys : List Bool) (c : Bool), llen (addRec_m xs ys c) = llen xs)
    (fun _ _ => rfl)
    (fun x xs' ih => fun ys c =>
      congrArg Nat.succ (ih (btail ys) (fcarry_m x (bhead ys) c)))
    xs

-- L2: at equal lengths the adder's prefix-read of `ys` is just `toNat ys`.
theorem toNatN_eq_toNat : ∀ (xs ys : List Bool),
    llen ys = llen xs → toNatN xs ys = toNat ys :=
  fun xs => @List.rec Bool
    (fun xs => ∀ (ys : List Bool), llen ys = llen xs → toNatN xs ys = toNat ys)
    (fun ys h => congrArg toNat (Eq.symm (llen_zero_nil ys h)))
    (fun x xs' ih => fun ys =>
      @List.rec Bool
        (fun ys => llen ys = llen (List.cons x xs') → toNatN (List.cons x xs') ys = toNat ys)
        (fun h => Nat.noConfusion h)
        (fun y ys' _ => fun h =>
          congrArg (fun k => Nat.add (b2n y) (Nat.mul 2 k))
            (ih ys' (Nat.succ_inj (llen ys') (llen xs') h)))
        ys)
    xs


-- LEMMA 1 (the value law associativity consumes): at EQUAL LENGTHS the ripple
-- adder's output value plus its carry-out weight is the exact integer sum.
theorem wadd_value : ∀ (x y : List Bool), llen y = llen x →
    Nat.add (toNat (wadd_m x y))
            (Nat.mul (pow2 (llen x)) (b2n (carryOut_m x y false)))
    = Nat.add (toNat x) (toNat y) :=
  fun x y h =>
    Eq.trans (addval x y false)
      (Eq.trans (Nat.add_zero (Nat.add (toNat x) (toNatN x y)))
        (congrArg (Nat.add (toNat x)) (toNatN_eq_toNat x y h)))


theorem one_add : ∀ (t : Nat), Nat.add (Nat.succ Nat.zero) t = Nat.succ t :=
  fun t => Eq.trans (Nat.succ_add Nat.zero t) (congrArg Nat.succ (Nat.zero_add t))

theorem head_step : ∀ (b : Bool) (t : Nat),
    Nat.le (Nat.add (b2n b) (Nat.mul 2 t)) (Nat.succ (Nat.mul 2 t)) :=
  fun b t => @Bool.rec
    (fun b => Nat.le (Nat.add (b2n b) (Nat.mul 2 t)) (Nat.succ (Nat.mul 2 t)))
    (@Eq.subst Nat (fun k => Nat.le k (Nat.succ (Nat.mul 2 t)))
       (Nat.mul 2 t) (Nat.add Nat.zero (Nat.mul 2 t))
       (Eq.symm (Nat.zero_add (Nat.mul 2 t)))
       (Nat.le_add_right (Nat.mul 2 t) (Nat.succ Nat.zero)))
    (@Eq.subst Nat (fun k => Nat.le k (Nat.succ (Nat.mul 2 t)))
       (Nat.succ (Nat.mul 2 t)) (Nat.add (Nat.succ Nat.zero) (Nat.mul 2 t))
       (Eq.symm (one_add (Nat.mul 2 t)))
       (Nat.le_refl (Nat.succ (Nat.mul 2 t))))
    b

-- L3: an n-bit word's value is below 2^n.
theorem toNat_lt_pow2 : ∀ (xs : List Bool),
    Nat.le (Nat.succ (toNat xs)) (pow2 (llen xs)) :=
  fun xs => @List.rec Bool (fun xs => Nat.le (Nat.succ (toNat xs)) (pow2 (llen xs)))
    (Nat.le_refl (Nat.succ Nat.zero))
    (fun b bs ih =>
      Nat.le_trans
        (Nat.succ_le_succ (head_step b (toNat bs)))
        (@Eq.subst Nat (fun k => Nat.le k (Nat.mul 2 (pow2 (llen bs))))
           (Nat.mul 2 (Nat.succ (toNat bs)))
           (Nat.succ (Nat.succ (Nat.mul 2 (toNat bs))))
           (two_succ (toNat bs))
           (Nat.mul_le_mul_left (Nat.succ (toNat bs)) (pow2 (llen bs)) 2 ih)))
    xs


-- A value below P cannot also be P plus something.
theorem lt_absurd : ∀ (a b P : Nat), Nat.le (Nat.succ b) P → Nat.add a P = b → False :=
  fun a b P hb h =>
    Nat.lt_irrefl b
      (Nat.le_trans hb
        (@Eq.subst Nat (fun k => Nat.le P k) (Nat.add a P) b h
          (@Eq.subst Nat (fun k => Nat.le P k) (Nat.add P a) (Nat.add a P)
            (Nat.add_comm P a)
            (Nat.le_add_right P a))))

-- L5 (uniqueness): two sub-P values whose P-weighted carry corrections agree
-- are the same value, whatever the two carry bits were.
theorem carry_unique : ∀ (a b P : Nat) (c1 c2 : Bool),
    Nat.le (Nat.succ a) P → Nat.le (Nat.succ b) P →
    Nat.add a (Nat.mul P (b2n c1)) = Nat.add b (Nat.mul P (b2n c2)) → a = b :=
  fun a b P c1 c2 ha hb =>
    @Bool.rec
      (fun c1 => Nat.add a (Nat.mul P (b2n c1)) = Nat.add b (Nat.mul P (b2n c2)) → a = b)
      (@Bool.rec
        (fun c2 => Nat.add a (Nat.mul P (b2n false)) = Nat.add b (Nat.mul P (b2n c2)) → a = b)
        (fun h => Eq.trans (Eq.symm (Nat.add_zero a)) (Eq.trans h (Nat.add_zero b)))
        (fun h => False.elim (lt_absurd b a P ha
           (Eq.trans (congrArg (Nat.add b) (Eq.symm (Nat.zero_add P)))
             (Eq.trans (Eq.symm h) (Nat.add_zero a)))))
        c2)
      (@Bool.rec
        (fun c2 => Nat.add a (Nat.mul P (b2n true)) = Nat.add b (Nat.mul P (b2n c2)) → a = b)
        (fun h => False.elim (lt_absurd a b P hb
           (Eq.trans (congrArg (Nat.add a) (Eq.symm (Nat.zero_add P)))
             (Eq.trans h (Nat.add_zero b)))))
        (fun h => Nat.add_right_cancel a (Nat.add Nat.zero P) b h)
        c2)
      c1

-- ==========================================================================
--  RIPPLE-ADDER ASSOCIATIVITY, and the shift distribution — lemmas 1(a) and 2.
-- ==========================================================================
--
--  `wadd_assoc` is the theorem the whole arithmetic development above exists
--  for. It CANNOT be proved bit-wise: `assoc_carries_differ` below exhibits
--  concrete operands where the two groupings produce DIFFERENT carry-outs
--  (x=[true], y=[true], z=[false]), while `assoc_witness` shows the results
--  agree anyway. Only the carry SUM is invariant, which is precisely why the
--  proof runs through values — `wadd_value` for each grouping, `rem_unique` to
--  cancel the P-multiples, `toNat_lt_pow2` for the bounds, and `toNat_inj` to
--  return to bit-level equality.
--
--  `rem_unique` generalises `carry_unique` from a single carry bit to an
--  arbitrary P-multiple, which associativity needs because the two carry
--  corrections ADD (reaching 2, not 1).
--
--  `droplast_addRec` is lemma 2: the low bits of a sum depend only on the low
--  bits of the operands, since carries flow upward only. It is stated with the
--  length side condition the earlier obstruction note predicted — without
--  `llen ys = llen xs` it is FALSE, because `bhead (dropLast ys)` stops
--  tracking `bhead ys` once `ys` is a singleton. `shl1_wadd` follows in one
--  step and is what lets a shifted row be added under the shift.

-- case k1=0, k2=succ
theorem ru_a : ∀ (P a b k2 : Nat), Nat.le (Nat.succ a) P →
    Nat.add a (Nat.mul P Nat.zero) = Nat.add b (Nat.mul P (Nat.succ k2)) → False :=
  fun P a b k2 ha h =>
    lt_absurd (Nat.add b (Nat.mul P k2)) a P ha
      (Eq.symm (Eq.trans (Eq.symm (Nat.add_zero a))
        (Eq.trans h (Eq.symm (Nat.add_assoc b (Nat.mul P k2) P)))))

-- case k1=succ, k2=0
theorem ru_b : ∀ (P a b k1 : Nat), Nat.le (Nat.succ b) P →
    Nat.add a (Nat.mul P (Nat.succ k1)) = Nat.add b (Nat.mul P Nat.zero) → False :=
  fun P a b k1 hb h =>
    lt_absurd (Nat.add a (Nat.mul P k1)) b P hb
      (Eq.trans (Nat.add_assoc a (Nat.mul P k1) P) (Eq.trans h (Nat.add_zero b)))

-- case k1=succ, k2=succ : strip one P from each side
theorem ru_c : ∀ (P a b k1 k2 : Nat),
    Nat.add a (Nat.mul P (Nat.succ k1)) = Nat.add b (Nat.mul P (Nat.succ k2)) →
    Nat.add a (Nat.mul P k1) = Nat.add b (Nat.mul P k2) :=
  fun P a b k1 k2 h =>
    Nat.add_right_cancel (Nat.add a (Nat.mul P k1)) P (Nat.add b (Nat.mul P k2))
      (Eq.trans (Nat.add_assoc a (Nat.mul P k1) P)
        (Eq.trans h (Eq.symm (Nat.add_assoc b (Nat.mul P k2) P))))


theorem rem_unique : ∀ (P a b : Nat), Nat.le (Nat.succ a) P → Nat.le (Nat.succ b) P →
    ∀ (k1 k2 : Nat), Nat.add a (Nat.mul P k1) = Nat.add b (Nat.mul P k2) → a = b :=
  fun P a b ha hb k1 =>
    @Nat.rec
      (fun k1 => ∀ (k2 : Nat), Nat.add a (Nat.mul P k1) = Nat.add b (Nat.mul P k2) → a = b)
      (fun k2 => @Nat.rec
         (fun k2 => Nat.add a (Nat.mul P Nat.zero) = Nat.add b (Nat.mul P k2) → a = b)
         (fun h => Eq.trans (Eq.symm (Nat.add_zero a)) (Eq.trans h (Nat.add_zero b)))
         (fun k2' _ => fun h => False.elim (ru_a P a b k2' ha h))
         k2)
      (fun k1' ih => fun k2 => @Nat.rec
         (fun k2 => Nat.add a (Nat.mul P (Nat.succ k1')) = Nat.add b (Nat.mul P k2) → a = b)
         (fun h => False.elim (ru_b P a b k1' hb h))
         (fun k2' _ => fun h => ih k2' (ru_c P a b k1' k2' h))
         k2)
      k1


theorem llen_wadd : ∀ (x y : List Bool), llen (wadd_m x y) = llen x :=
  fun x y => llen_addRec x y false

theorem add_swap3 : ∀ (W Z K : Nat), Nat.add (Nat.add W Z) K = Nat.add (Nat.add W K) Z :=
  fun W Z K => Eq.trans (Nat.add_assoc W Z K)
    (Eq.trans (congrArg (Nat.add W) (Nat.add_comm Z K)) (Eq.symm (Nat.add_assoc W K Z)))

-- Combine two carry-corrected value equations into one, at a shared P.
theorem combine : ∀ (L W Z X Y P k2 k1 : Nat),
    Nat.add L (Nat.mul P k2) = Nat.add W Z →
    Nat.add W (Nat.mul P k1) = Nat.add X Y →
    Nat.add L (Nat.mul P (Nat.add k2 k1)) = Nat.add (Nat.add X Y) Z :=
  fun L W Z X Y P k2 k1 h1 h2 =>
    Eq.trans (congrArg (Nat.add L) (mul_add P k2 k1))
      (Eq.trans (Eq.symm (Nat.add_assoc L (Nat.mul P k2) (Nat.mul P k1)))
        (Eq.trans (congrArg (fun t => Nat.add t (Nat.mul P k1)) h1)
          (Eq.trans (add_swap3 W Z (Nat.mul P k1))
            (congrArg (fun t => Nat.add t Z) h2))))


-- Mirror of `combine` for when the inner sum sits on the RIGHT.
theorem combine_r : ∀ (L W Z X Y P k2 k1 : Nat),
    Nat.add L (Nat.mul P k2) = Nat.add Z W →
    Nat.add W (Nat.mul P k1) = Nat.add X Y →
    Nat.add L (Nat.mul P (Nat.add k2 k1)) = Nat.add Z (Nat.add X Y) :=
  fun L W Z X Y P k2 k1 h1 h2 =>
    Eq.trans (congrArg (Nat.add L) (mul_add P k2 k1))
      (Eq.trans (Eq.symm (Nat.add_assoc L (Nat.mul P k2) (Nat.mul P k1)))
        (Eq.trans (congrArg (fun t => Nat.add t (Nat.mul P k1)) h1)
          (Eq.trans (Nat.add_assoc Z W (Nat.mul P k1))
            (congrArg (Nat.add Z) h2))))

theorem bound_at : ∀ (w : List Bool) (n : Nat), llen w = n →
    Nat.le (Nat.succ (toNat w)) (pow2 n) :=
  fun w n h =>
    @Eq.subst Nat (fun k => Nat.le (Nat.succ (toNat w)) (pow2 k)) (llen w) n h
      (toNat_lt_pow2 w)

theorem value_at : ∀ (x y : List Bool) (n : Nat), llen y = llen x → llen x = n →
    Nat.add (toNat (wadd_m x y)) (Nat.mul (pow2 n) (b2n (carryOut_m x y false)))
      = Nat.add (toNat x) (toNat y) :=
  fun x y n hy hn =>
    @Eq.subst Nat
      (fun k => Nat.add (toNat (wadd_m x y)) (Nat.mul (pow2 k) (b2n (carryOut_m x y false)))
                = Nat.add (toNat x) (toNat y))
      (llen x) n hn (wadd_value x y hy)


-- RIPPLE-ADDER ASSOCIATIVITY, at equal operand lengths.
theorem wadd_assoc : ∀ (x y z : List Bool), llen y = llen x → llen z = llen x →
    wadd_m (wadd_m x y) z = wadd_m x (wadd_m y z) :=
  fun x y z hy hz =>
    toNat_inj (wadd_m (wadd_m x y) z) (wadd_m x (wadd_m y z))
      (Eq.trans (Eq.trans (llen_wadd (wadd_m x y) z) (llen_wadd x y))
        (Eq.symm (llen_wadd x (wadd_m y z))))
      (rem_unique (pow2 (llen x))
        (toNat (wadd_m (wadd_m x y) z)) (toNat (wadd_m x (wadd_m y z)))
        (bound_at (wadd_m (wadd_m x y) z) (llen x)
          (Eq.trans (llen_wadd (wadd_m x y) z) (llen_wadd x y)))
        (bound_at (wadd_m x (wadd_m y z)) (llen x) (llen_wadd x (wadd_m y z)))
        (Nat.add (b2n (carryOut_m (wadd_m x y) z false)) (b2n (carryOut_m x y false)))
        (Nat.add (b2n (carryOut_m x (wadd_m y z) false)) (b2n (carryOut_m y z false)))
        (Eq.trans
          (combine (toNat (wadd_m (wadd_m x y) z)) (toNat (wadd_m x y)) (toNat z)
            (toNat x) (toNat y) (pow2 (llen x))
            (b2n (carryOut_m (wadd_m x y) z false)) (b2n (carryOut_m x y false))
            (value_at (wadd_m x y) z (llen x)
              (Eq.trans hz (Eq.symm (llen_wadd x y))) (llen_wadd x y))
            (value_at x y (llen x) hy rfl))
          (Eq.trans (Nat.add_assoc (toNat x) (toNat y) (toNat z))
            (Eq.symm
              (combine_r (toNat (wadd_m x (wadd_m y z))) (toNat (wadd_m y z)) (toNat x)
                (toNat y) (toNat z) (pow2 (llen x))
                (b2n (carryOut_m x (wadd_m y z) false)) (b2n (carryOut_m y z false))
                (value_at x (wadd_m y z) (llen x)
                  (Eq.trans (llen_wadd y z) hy) rfl)
                (value_at y z (llen x) (Eq.trans hz (Eq.symm hy)) hy))))))


-- NON-VACUITY of wadd_assoc: the two groupings are NOT syntactically equal, and
-- their per-bit CARRY-OUTS genuinely differ — which is exactly why this needed
-- the value law rather than a bit-wise induction. Witness at width 1:
-- x=[true], y=[true], z=[false] gives carry-outs true vs false.
theorem assoc_carries_differ :
    Bool.beq (carryOut_m (wadd_m [true] [true]) [false] false)
             (carryOut_m [true] (wadd_m [true] [false]) false) = false := rfl
-- and the two sides nonetheless agree, as the theorem says
theorem assoc_witness :
    wadd_m (wadd_m [true,true,false,true] [true,false,true,true]) [false,true,true,true]
  = wadd_m [true,true,false,true] (wadd_m [true,false,true,true] [false,true,true,true]) := rfl


-- singleton / two-element reductions of dropLast, to keep the case analysis flat
theorem dl_one : ∀ (x : Bool), dropLast (List.cons x List.nil) = List.nil := fun _ => rfl
theorem dl_two : ∀ (x x2 : Bool) (xs2 : List Bool),
    dropLast (List.cons x (List.cons x2 xs2))
      = List.cons x (dropLast (List.cons x2 xs2)) := fun _ _ _ => rfl

-- the xs' = [] case
theorem dl_a : ∀ (x y : Bool) (ys' : List Bool) (c : Bool),
    dropLast (addRec_m (List.cons x List.nil) (List.cons y ys') c)
      = addRec_m (dropLast (List.cons x List.nil)) (dropLast (List.cons y ys')) c :=
  fun _ _ _ _ => rfl

-- the xs' = cons, ys' = cons case (the real one)
theorem dl_b : ∀ (x y x2 y2 : Bool) (xs2 ys2 : List Bool) (c : Bool),
    (∀ (zs : List Bool) (d : Bool), llen zs = llen (List.cons x2 xs2) →
       dropLast (addRec_m (List.cons x2 xs2) zs d)
         = addRec_m (dropLast (List.cons x2 xs2)) (dropLast zs) d) →
    llen (List.cons y2 ys2) = llen (List.cons x2 xs2) →
    dropLast (addRec_m (List.cons x (List.cons x2 xs2)) (List.cons y (List.cons y2 ys2)) c)
      = addRec_m (dropLast (List.cons x (List.cons x2 xs2)))
                 (dropLast (List.cons y (List.cons y2 ys2))) c :=
  fun x y x2 y2 xs2 ys2 c ih h =>
    congrArg (fun t => List.cons (fsum_m x y c) t)
      (ih (List.cons y2 ys2) (fcarry_m x y c) h)


-- ys' case split, given xs' = x2::xs2
theorem dl_c : ∀ (x y x2 : Bool) (xs2 : List Bool) (c : Bool),
    (∀ (zs : List Bool) (d : Bool), llen zs = llen (List.cons x2 xs2) →
       dropLast (addRec_m (List.cons x2 xs2) zs d)
         = addRec_m (dropLast (List.cons x2 xs2)) (dropLast zs) d) →
    ∀ (ys' : List Bool), llen (List.cons y ys') = llen (List.cons x (List.cons x2 xs2)) →
    dropLast (addRec_m (List.cons x (List.cons x2 xs2)) (List.cons y ys') c)
      = addRec_m (dropLast (List.cons x (List.cons x2 xs2))) (dropLast (List.cons y ys')) c :=
  fun x y x2 xs2 c ih ys' =>
    @List.rec Bool
      (fun ys' => llen (List.cons y ys') = llen (List.cons x (List.cons x2 xs2)) →
         dropLast (addRec_m (List.cons x (List.cons x2 xs2)) (List.cons y ys') c)
           = addRec_m (dropLast (List.cons x (List.cons x2 xs2)))
                      (dropLast (List.cons y ys')) c)
      (fun hb => Nat.noConfusion
         (Nat.succ_inj (llen List.nil) (llen (List.cons x2 xs2)) hb))
      (fun y2 ys2 _ => fun hb =>
         dl_b x y x2 y2 xs2 ys2 c ih
           (Nat.succ_inj (llen (List.cons y2 ys2)) (llen (List.cons x2 xs2)) hb))
      ys'


-- xs' case split, given ys = y::ys'
theorem dl_d : ∀ (x y : Bool) (xs' ys' : List Bool) (c : Bool),
    (∀ (zs : List Bool) (d : Bool), llen zs = llen xs' →
       dropLast (addRec_m xs' zs d) = addRec_m (dropLast xs') (dropLast zs) d) →
    llen (List.cons y ys') = llen (List.cons x xs') →
    dropLast (addRec_m (List.cons x xs') (List.cons y ys') c)
      = addRec_m (dropLast (List.cons x xs')) (dropLast (List.cons y ys')) c :=
  fun x y xs' ys' c =>
    @List.rec Bool
      (fun w =>
        (∀ (zs : List Bool) (d : Bool), llen zs = llen w →
           dropLast (addRec_m w zs d) = addRec_m (dropLast w) (dropLast zs) d) →
        llen (List.cons y ys') = llen (List.cons x w) →
        dropLast (addRec_m (List.cons x w) (List.cons y ys') c)
          = addRec_m (dropLast (List.cons x w)) (dropLast (List.cons y ys')) c)
      (fun _ _ => dl_a x y ys' c)
      (fun x2 xs2 _ => fun ih hb => dl_c x y x2 xs2 c ih ys' hb)
      xs'

-- LEMMA 2: the low bits of a sum depend only on the low bits of the operands.
theorem droplast_addRec : ∀ (xs ys : List Bool) (c : Bool), llen ys = llen xs →
    dropLast (addRec_m xs ys c) = addRec_m (dropLast xs) (dropLast ys) c :=
  fun xs => @List.rec Bool
    (fun xs => ∀ (ys : List Bool) (c : Bool), llen ys = llen xs →
        dropLast (addRec_m xs ys c) = addRec_m (dropLast xs) (dropLast ys) c)
    (fun _ _ _ => rfl)
    (fun x xs' ih => fun ys c =>
      @List.rec Bool
        (fun ys => llen ys = llen (List.cons x xs') →
           dropLast (addRec_m (List.cons x xs') ys c)
             = addRec_m (dropLast (List.cons x xs')) (dropLast ys) c)
        (fun h => Nat.noConfusion h)
        (fun y ys' _ => fun h => dl_d x y xs' ys' c ih h)
        ys)
    xs


-- shl1 distributes over the adder: both sides are `false :: (low bits of sum)`.
theorem shl1_wadd : ∀ (x y : List Bool), llen y = llen x →
    shl1 (wadd_m x y) = wadd_m (shl1 x) (shl1 y) :=
  fun x y h =>
    congrArg (fun t => List.cons false t) (droplast_addRec x y false h)

-- llen is preserved by shl1 on nonempty words, so the shift keeps operands
-- length-matched all the way down.
theorem llen_dropLast_cons : ∀ (x : Bool) (xs : List Bool),
    llen (dropLast (List.cons x xs)) = llen xs :=
  fun x xs => @List.rec Bool (fun xs => ∀ (x : Bool),
      llen (dropLast (List.cons x xs)) = llen xs)
    (fun _ => rfl)
    (fun x2 xs2 ih => fun _ => congrArg Nat.succ (ih x2))
    xs x

theorem llen_shl1 : ∀ (x : Bool) (xs : List Bool),
    llen (shl1 (List.cons x xs)) = llen (List.cons x xs) :=
  fun x xs => congrArg Nat.succ (llen_dropLast_cons x xs)

-- ==========================================================================
--  OBLIGATION 2, DISCHARGED — `mul_ay = mul_m` at every width.
-- ==========================================================================
--
--  `mul_ay_matches_model` closes the pure-mathematics half of the bridge. What
--  remains of the correspondence is ONLY `AyBlastAgrees` — that ay's Rust emits
--  `mul_ay` — which is a line-by-line structural comparison against the loop in
--  `bv_blast_solver.rs` and cannot be discharged inside clean at all.
--
--  The induction is `accRows_lemma`:
--
--    accRows a bs k acc = wadd_m acc (shlk k (mul_m a bs))
--
--  Its STEP is exactly the associativity the whole arithmetic development was
--  built for: ay's loop folds rows LEFT-associated onto an accumulator, while
--  `mul_m` nests them RIGHT-associated, and `wadd_assoc` is what lets the two
--  be identified. Its BASE case needs that adding an all-zero word is the
--  identity (`addRec_zeros`), applied to `shlk k (zerosLike a)` — all-zero at
--  every shift (`allZero_shlk`), including the degenerate `shl1 [] = [false]`.
--
--  LENGTHS are threaded as `llen w = Nat.succ n` rather than as a nonemptiness
--  side condition, because `shl1` preserves length only on nonempty words —
--  `shl1 [] = [false]` grows. The `a = []` case is therefore handled separately
--  (`mul_ay_nil` / `mul_m_nil`), where both multipliers collapse to the empty
--  word definitionally.

theorem and_left : ∀ (p q : Bool), Bool.and p q = true → p = true :=
  fun p q => @Bool.rec (fun p => Bool.and p q = true → p = true)
    (fun h => Bool.noConfusion h) (fun _ => rfl) p
theorem and_right : ∀ (p q : Bool), Bool.and p q = true → q = true :=
  fun p q => @Bool.rec (fun p => Bool.and p q = true → q = true)
    (fun h => Bool.noConfusion h) (fun h => h) p
theorem not_true_false : ∀ (b : Bool), Bool.not b = true → b = false :=
  fun b => @Bool.rec (fun b => Bool.not b = true → b = false)
    (fun _ => rfl) (fun h => Bool.noConfusion h) b
theorem fsum_zero : ∀ (x : Bool), fsum_m x false false = x :=
  fun x => @Bool.rec (fun x => fsum_m x false false = x) rfl rfl x
theorem fcarry_zero : ∀ (x : Bool), fcarry_m x false false = false :=
  fun x => @Bool.rec (fun x => fcarry_m x false false = false) rfl rfl x

theorem bhead_allZero : ∀ (zs : List Bool), allZero zs = true → bhead zs = false :=
  fun zs => @List.rec Bool (fun zs => allZero zs = true → bhead zs = false)
    (fun _ => rfl)
    (fun z zs' _ => fun h => not_true_false z (and_left (Bool.not z) (allZero zs') h))
    zs
theorem btail_allZero : ∀ (zs : List Bool), allZero zs = true → allZero (btail zs) = true :=
  fun zs => @List.rec Bool (fun zs => allZero zs = true → allZero (btail zs) = true)
    (fun _ => rfl)
    (fun z zs' _ => fun h => and_right (Bool.not z) (allZero zs') h)
    zs

-- Adding an all-zero word is the identity.
theorem addRec_zeros : ∀ (xs zs : List Bool), allZero zs = true →
    addRec_m xs zs false = xs :=
  fun xs => @List.rec Bool
    (fun xs => ∀ (zs : List Bool), allZero zs = true → addRec_m xs zs false = xs)
    (fun _ _ => rfl)
    (fun x xs' ih => fun zs h =>
      Eq.trans
        (congrArg (fun t => List.cons (fsum_m x t false)
                     (addRec_m xs' (btail zs) (fcarry_m x t false)))
          (bhead_allZero zs h))
        (Eq.trans
          (congrArg (fun t => List.cons t (addRec_m xs' (btail zs) (fcarry_m x false false)))
            (fsum_zero x))
          (Eq.trans
            (congrArg (fun t => List.cons x (addRec_m xs' (btail zs) t)) (fcarry_zero x))
            (congrArg (fun t => List.cons x t) (ih (btail zs) (btail_allZero zs h))))))
    xs


theorem allZero_zerosLike : ∀ (a : List Bool), allZero (zerosLike a) = true :=
  fun a => @List.rec Bool (fun a => allZero (zerosLike a) = true) rfl
    (fun _ _ ih => ih) a

-- dropLast preserves all-zero. Flat helpers for the nested case analysis.
theorem adl_two : ∀ (x y : Bool) (r : List Bool),
    allZero (List.cons x (List.cons y r)) = true →
    allZero (dropLast (List.cons y r)) = true →
    allZero (dropLast (List.cons x (List.cons y r))) = true :=
  fun x y r h ihr =>
    Eq.trans
      (congrArg (fun t => Bool.and t (allZero (dropLast (List.cons y r))))
        (and_left (Bool.not x) (allZero (List.cons y r)) h))
      (congrArg (fun t => Bool.and true t) ihr)

theorem allZero_dropLast : ∀ (w : List Bool), allZero w = true →
    allZero (dropLast w) = true :=
  fun w => @List.rec Bool (fun w => allZero w = true → allZero (dropLast w) = true)
    (fun _ => rfl)
    (fun x xs ih =>
      @List.rec Bool
        (fun xs => (allZero xs = true → allZero (dropLast xs) = true) →
           allZero (List.cons x xs) = true → allZero (dropLast (List.cons x xs)) = true)
        (fun _ _ => rfl)
        (fun y r _ => fun ihc h =>
          adl_two x y r h (ihc (and_right (Bool.not x) (allZero (List.cons y r)) h)))
        xs ih)
    w

theorem allZero_shl1 : ∀ (w : List Bool), allZero w = true →
    allZero (shl1 w) = true :=
  fun w h => allZero_dropLast w h

theorem allZero_shlk : ∀ (k : Nat) (a : List Bool),
    allZero (shlk k (zerosLike a)) = true :=
  fun k a => @Nat.rec (fun k => allZero (shlk k (zerosLike a)) = true)
    (allZero_zerosLike a)
    (fun k ih => allZero_shl1 (shlk k (zerosLike a)) ih)
    k


theorem llen_dropLast_succ : ∀ (w : List Bool) (n : Nat),
    llen w = Nat.succ n → llen (dropLast w) = n :=
  fun w n => @List.rec Bool (fun w => llen w = Nat.succ n → llen (dropLast w) = n)
    (fun h => Nat.noConfusion h)
    (fun x xs _ => fun h =>
      Eq.trans (llen_dropLast_cons x xs) (Nat.succ_inj (llen xs) n h))
    w

theorem llen_shl1_succ : ∀ (w : List Bool) (n : Nat),
    llen w = Nat.succ n → llen (shl1 w) = Nat.succ n :=
  fun w n h => congrArg Nat.succ (llen_dropLast_succ w n h)

theorem llen_shlk_succ : ∀ (k : Nat) (w : List Bool) (n : Nat),
    llen w = Nat.succ n → llen (shlk k w) = Nat.succ n :=
  fun k w n h => @Nat.rec (fun k => llen (shlk k w) = Nat.succ n) h
    (fun k ih => llen_shl1_succ (shlk k w) n ih) k

theorem llen_zerosLike : ∀ (a : List Bool), llen (zerosLike a) = llen a :=
  fun a => @List.rec Bool (fun a => llen (zerosLike a) = llen a) rfl
    (fun _ _ ih => congrArg Nat.succ ih) a

theorem llen_selRow : ∀ (b : Bool) (a : List Bool), llen (selRow_m b a) = llen a :=
  fun b a => @List.rec Bool (fun a => llen (selRow_m b a) = llen a) rfl
    (fun _ _ ih => congrArg Nat.succ ih) a

theorem llen_mul_m : ∀ (a bs : List Bool), llen (mul_m a bs) = llen a :=
  fun a bs => @List.rec Bool (fun bs => llen (mul_m a bs) = llen a)
    (llen_zerosLike a)
    (fun b0 rest _ => Eq.trans (llen_wadd (selRow_m b0 a) (shl1 (mul_m a rest)))
       (llen_selRow b0 a))
    bs

-- shlk distributes over the adder, at equal (nonzero) lengths.
theorem shlk_wadd : ∀ (k : Nat) (x y : List Bool) (n : Nat),
    llen x = Nat.succ n → llen y = Nat.succ n →
    shlk k (wadd_m x y) = wadd_m (shlk k x) (shlk k y) :=
  fun k x y n hx hy => @Nat.rec
    (fun k => shlk k (wadd_m x y) = wadd_m (shlk k x) (shlk k y))
    rfl
    (fun k ih => Eq.trans (congrArg shl1 ih)
       (shl1_wadd (shlk k x) (shlk k y)
         (Eq.trans (llen_shlk_succ k y n hy) (Eq.symm (llen_shlk_succ k x n hx)))))
    k


-- LEMMA 3: ay's accumulator loop equals the model's shifted Horner tail.
theorem accRows_lemma : ∀ (a : List Bool) (n : Nat), llen a = Nat.succ n →
    ∀ (bs : List Bool) (k : Nat) (acc : List Bool), llen acc = Nat.succ n →
      accRows a bs k acc = wadd_m acc (shlk k (mul_m a bs)) :=
  fun a n ha bs => @List.rec Bool
    (fun bs => ∀ (k : Nat) (acc : List Bool), llen acc = Nat.succ n →
       accRows a bs k acc = wadd_m acc (shlk k (mul_m a bs)))
    (fun k acc _ => Eq.symm (addRec_zeros acc (shlk k (zerosLike a)) (allZero_shlk k a)))
    (fun bj rest ih => fun k acc hacc =>
      Eq.trans
        (ih (Nat.succ k) (wadd_m acc (shlk k (selRow_m bj a)))
          (Eq.trans (llen_wadd acc (shlk k (selRow_m bj a))) hacc))
        (Eq.trans
          (wadd_assoc acc (shlk k (selRow_m bj a)) (shlk (Nat.succ k) (mul_m a rest))
            (Eq.trans (llen_shlk_succ k (selRow_m bj a) n
               (Eq.trans (llen_selRow bj a) ha)) (Eq.symm hacc))
            (Eq.trans (llen_shlk_succ (Nat.succ k) (mul_m a rest) n
               (Eq.trans (llen_mul_m a rest) ha)) (Eq.symm hacc)))
          (Eq.symm
            (congrArg (fun t => wadd_m acc t)
              (Eq.trans
                (shlk_wadd k (selRow_m bj a) (shl1 (mul_m a rest)) n
                  (Eq.trans (llen_selRow bj a) ha)
                  (llen_shl1_succ (mul_m a rest) n (Eq.trans (llen_mul_m a rest) ha)))
                (congrArg (fun t => wadd_m (shlk k (selRow_m bj a)) t)
                  (shlk_shl1 k (mul_m a rest))))))))
    bs


-- The degenerate multiplicand: both multipliers collapse to the empty word.
theorem mul_m_nil : ∀ (b : List Bool), mul_m List.nil b = List.nil :=
  fun b => @List.rec Bool (fun b => mul_m List.nil b = List.nil) rfl
    (fun _ _ _ => rfl) b
theorem accRows_nil_acc : ∀ (a bs : List Bool) (k : Nat),
    accRows a bs k List.nil = List.nil :=
  fun a bs => @List.rec Bool (fun bs => ∀ (k : Nat), accRows a bs k List.nil = List.nil)
    (fun _ => rfl) (fun _ _ ih => fun k => ih (Nat.succ k)) bs
theorem mul_ay_nil : ∀ (b : List Bool), mul_ay List.nil b = List.nil :=
  fun b => @List.rec Bool (fun b => mul_ay List.nil b = List.nil) rfl
    (fun b0 bs _ => accRows_nil_acc List.nil bs (Nat.succ Nat.zero)) b

theorem mul_ay_eq_nonempty : ∀ (a : List Bool) (n : Nat), llen a = Nat.succ n →
    ∀ (b : List Bool), mul_ay a b = mul_m a b :=
  fun a n ha b => @List.rec Bool (fun b => mul_ay a b = mul_m a b) rfl
    (fun b0 bs _ =>
      accRows_lemma a n ha bs (Nat.succ Nat.zero) (selRow_m b0 a)
        (Eq.trans (llen_selRow b0 a) ha))
    b

/-- OBLIGATION 2, DISCHARGED: ay's accumulate-shifted-rows multiplier agrees
    with the model's Horner-recursive one, at every width. -/
theorem mul_ay_matches_model : AyModelMatches :=
  fun a => @List.rec Bool (fun a => ∀ (b : List Bool), mul_ay a b = mul_m a b)
    (fun b => Eq.trans (mul_ay_nil b) (Eq.symm (mul_m_nil b)))
    (fun a0 as_ _ => mul_ay_eq_nonempty (List.cons a0 as_) (llen as_) rfl)
    a

-- ==========================================================================
--  OBLIGATION 2, VERIFIED EXHAUSTIVELY UP TO WIDTH 5.
-- ==========================================================================
--
--  `AyModelMatches` is stated for ALL widths and is not proved in general (see
--  the obstruction recorded below). What IS proved here is stronger than the
--  three sample witnesses above: for every width n <= 5, `mul_ay` and `mul_m`
--  agree on EVERY pair of n-bit words — 4 + 16 + 64 + 256 + 1024 = 1,364 pairs,
--  covering every carry pattern at those widths. The kernel decides each
--  `exhaustiveAt n = true` by COMPUTING both multipliers over the enumerated
--  word lists, so these are `rfl` theorems, not assertions.
--
--  Width 6 (4,096 pairs) was also verified; it is left out only because it
--  costs ~23s of kernel reduction against ~8s for the whole 1..5 range.
--
--  The range matters: `MAX_RECHECKABLE_MUL_WIDTH = 8` is the widest multiply
--  the live gate will re-check at all, so widths 1..6 cover most of the range
--  where the correspondence is actually exercised today.

def extendW : List (List Bool) → List (List Bool) := fun ws =>
  @List.rec (List Bool) (fun _ => List (List Bool)) List.nil
    (fun w _ ih => List.cons (List.cons false w) (List.cons (List.cons true w) ih)) ws

/-- Every word of length `n`, as a list. -/
def allWords : Nat → List (List Bool) := fun n =>
  @Nat.rec (fun _ => List (List Bool)) (List.cons List.nil List.nil)
    (fun _ ih => extendW ih) n

def checkB (a : List Bool) : List (List Bool) → Bool := fun bs =>
  @List.rec (List Bool) (fun _ => Bool) true
    (fun b _ ih => Bool.and (wordBeq (mul_ay a b) (mul_m a b)) ih) bs

def checkAB : List (List Bool) → List (List Bool) → Bool := fun as_ =>
  @List.rec (List Bool) (fun _ => List (List Bool) -> Bool) (fun _ => true)
    (fun a _ ih => fun bs => Bool.and (checkB a bs) (ih bs)) as_

/-- `mul_ay` and `mul_m` agree on every pair of `n`-bit words. -/
def exhaustiveAt (n : Nat) : Bool := checkAB (allWords n) (allWords n)

theorem exh1 : exhaustiveAt 1 = true := rfl
theorem exh2 : exhaustiveAt 2 = true := rfl
theorem exh3 : exhaustiveAt 3 = true := rfl
theorem exh4 : exhaustiveAt 4 = true := rfl
theorem exh5 : exhaustiveAt 5 = true := rfl

-- NEGATIVE CONTROL. The identical harness, pointed at the WRONG function, must
-- report `false`. Without this the exhaustive theorems above would be worthless:
-- a `checkAB` that could not distinguish anything would satisfy them vacuously.
def checkB_bad (a : List Bool) : List (List Bool) → Bool := fun bs =>
  @List.rec (List Bool) (fun _ => Bool) true
    (fun b _ ih => Bool.and (wordBeq (mul_ay a b) (wadd_m a b)) ih) bs
def checkAB_bad : List (List Bool) → List (List Bool) → Bool := fun as_ =>
  @List.rec (List Bool) (fun _ => List (List Bool) -> Bool) (fun _ => true)
    (fun a _ ih => fun bs => Bool.and (checkB_bad a bs) (ih bs)) as_
theorem exh_negative_control : checkAB_bad (allWords 4) (allWords 4) = false := rfl

-- ==========================================================================
--  WHY THE GENERAL CASE IS NOT PROVED — the measured obstruction.
-- ==========================================================================
--
--  The reduction is: `AyModelMatches` follows from
--
--    accRows a bs k acc = wadd_m acc (shlk k (mul_m a bs))
--
--  by induction on `bs`. The base case needs only that adding an all-zero word
--  is the identity. The STEP unfolds to
--
--    wadd (wadd acc X) Y  =  wadd acc (wadd X Y)          -- X, Y as shifted rows
--
--  using `shlk_shl1` — i.e. RIPPLE-ADDER ASSOCIATIVITY. That is not available
--  bit-wise. Per bit the sum bits do agree (`fsum` is XOR3, which is
--  associative), but the CARRIES do not: at x=1,y=1,c1=0,z=0,c2=0 the two
--  groupings produce carry-outs 0 and 1 respectively. Only the carry SUM is
--  invariant, so the argument has to go through the value law (`addval`, proved
--  above) plus injectivity of `toNat` on equal-length words.
--
--  The natural generalisation — exchanging the two carry inputs whenever their
--  SUM agrees — is FALSE as stated, and this is worth recording because it is
--  the obvious next thing to try. Counterexample, checked by hand:
--
--    xs = [x], ys = [], zs = [], (c1,c2) = (true,false) vs (d1,d2) = (false,true)
--      addRec [x] (addRec [] [] false) true  = [x XOR true]
--      addRec [x] (addRec [] [] true) false  = [x]
--
--  A carry handed to a ZERO-LENGTH adder is dropped, so the two sides differ.
--  Any working generalisation must carry length side conditions (|ys| >= |xs|)
--  through the induction. That is the remaining work.

/-- PAYOFF 1: with obligation 2 now discharged, an agreeing blast equals the
    separately-stated IR multiplier. -/
theorem blast_equals_ir (blast : Blast) (h1 : AyBlastAgrees blast) :
    ∀ (a : List Bool) (b : List Bool), blast a b = mul_ir a b :=
  fun a b => Eq.trans (h1 a b) (Eq.trans (mul_ay_matches_model a b) (mul_equiv a b))

/-- PAYOFF 2: an agreeing blast has the model's VALUE, so every value law about
    `mul_m` (notably `addval` via `MulValueSpec`) transfers verbatim. -/
theorem blast_value_eq (blast : Blast) (h1 : AyBlastAgrees blast) :
    ∀ (a : List Bool) (b : List Bool), Eq Nat (toNat (blast a b)) (toNat (mul_m a b)) :=
  fun a b => congrArg toNat (Eq.trans (h1 a b) (mul_ay_matches_model a b))

end G16Mul
