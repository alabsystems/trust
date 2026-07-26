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

end G16Mul
