-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B for RUNG 2, the GENERAL recursion case — beyond the obligation-free fixpoint that
-- recursive_summary.lean's `obligation_free_recursion_total` covers and that the trust-mc
-- implementation (commit 681557917, `try_direct_call_summary`) ships. The general case is a
-- recursive callee that DOES carry per-level obligations. Its sound modular discharge is the
-- assume-guarantee / Park-induction step: model the recursive call by the inductive hypothesis
-- (assume safe), and VERIFY the body's per-level obligation UNIVERSALLY — for every recursion
-- level / every input. If every level's obligation is discharged, the callee panics at NO depth.
--
-- This is the formal foundation for the NEXT Rung-2 implementation step: verify g's standalone VC
-- with self-calls havoced, and cache g as panic-free if it is SAFE for all inputs (a PDR /
-- inductive-invariant pass). The shipped lightweight summary's accept-when-empty rule is the
-- degenerate `ob ≡ false` instance of the theorem below.
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b

-- A conjunction of discharges: if both operands are known false, the disjunction is false. The
-- inductive step's core (current level discharged ∧ deeper calls safe ⟹ this prefix safe).
theorem bor_both_false (a b : Bool) (ha : a = false) (hb : b = false) : bor a b = false := by
  simp only [ha, hb, bor]

-- `ob k` = the body's panic obligation at recursion level `k` (with the recursive call's result
-- HAVOCED — exactly what the universal verification of g's body checks). `panicsByDepth ob d` is
-- whether the callee can panic within `d` levels of unrolling: the disjunction of every level's
-- obligation down to the base. (The obligation-free fixpoint is the special case `ob ≡ false`.)
def panicsByDepth (ob : Nat -> Bool) (d : Nat) : Bool :=
  match d with
  | Nat.zero => ob Nat.zero
  | Nat.succ d2 => bor (ob (Nat.succ d2)) (panicsByDepth ob d2)

-- THE GENERAL RECURSION SOUNDNESS: if every level's obligation is discharged (false for ALL
-- recursion levels — the universal verification result the PDR pass computes), the callee panics
-- at NO depth. Proven via the `Nat` recursor applied as a TERM (the motive is flat,
-- `fun d => _ = false`; the inductive step composes the discharged current level `hob (succ d)`
-- with the induction hypothesis for the deeper calls through `bor_both_false`). Using the kernel
-- recursor sidesteps clean's `induction`-tactic limits, as in the unbounded-Tarski proof.
def general_recursion_total (ob : Nat -> Bool) (hob : (k : Nat) -> (ob k = false)) :
    (d : Nat) -> (panicsByDepth ob d = false) :=
  @Nat.rec.{0}
    (fun d => (panicsByDepth ob d = false))
    (hob Nat.zero)
    (fun d ih => bor_both_false (ob (Nat.succ d)) (panicsByDepth ob d) (hob (Nat.succ d)) ih)

-- NECESSITY of the UNIVERSAL check — discharging only SOME levels is UNSOUND. A callee whose body
-- can panic at level ≥ 1 (`obBug k = (k ≥ 1)`) panics once unrolled, so a summary that skipped
-- that level's obligation would be a false proof. The theorem's hypothesis (EVERY level
-- discharged) genuinely fails here, so it does not — and must not — apply.
def obBug : Nat -> Bool
  | Nat.zero => false
  | Nat.succ _ => true
theorem obBug_level1_not_discharged : obBug (Nat.succ Nat.zero) = true := rfl
theorem obBug_panics_once_unrolled : panicsByDepth obBug (Nat.succ Nat.zero) = true := rfl

-- The shipped obligation-free fixpoint is exactly the degenerate `ob ≡ false` instance: every
-- level trivially discharged ⇒ safe at every depth, via the same general theorem.
theorem obligation_free_is_the_degenerate_case :
    panicsByDepth (fun _ => false) (Nat.succ (Nat.succ Nat.zero)) = false :=
  general_recursion_total (fun _ => false) (fun _ => rfl) (Nat.succ (Nat.succ Nat.zero))
