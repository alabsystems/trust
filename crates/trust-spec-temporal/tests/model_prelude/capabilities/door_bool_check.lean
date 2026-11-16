-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02b Clean capability matrix II (model_prelude_kernel.rs, clean_capabilities_doors):
-- the Bool door (B1A-D54; FiniteModelCheck.lean:112-121). A door is a recursor over its
-- computation, an identity on the computed Bool, so the kernel reduces the whole
-- computation as a major premise, with full whnf. The test elaborates mutated, stuck,
-- budget-starved and non-door statements after this file and classifies each refusal.

namespace Trust
namespace Model

-- The computation: a raw-recursor loop (no match, no if, no &&).
def sumTo (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun k acc => Nat.add (Nat.succ k) acc) n

-- The door: `Bool.rec` over the computed answer, the identity on Bool.
def checkSum (n lit : Nat) : Bool :=
  @Bool.rec (fun _ => Bool) false true (Nat.beq (sumTo n) lit)

theorem door_pass : checkSum 100 5050 = true := rfl

-- A continuation chain whose every step has a definition at its head. Reduced at the
-- top level of a definitional-equality check, each step spends one iteration of the
-- kernel's lazy-delta loop (capped at 10 000 iterations, clean tc/def_eq/delta.rs:65).
def idK (b : Bool) : Bool := b

def chain (n : Nat) : Bool :=
  @Nat.rec (fun _ => Bool) true (fun _ acc => idK acc) n

-- The same chain behind a door: the chain is the major premise of `Bool.rec`, so it is
-- reduced with full whnf and never reaches the lazy-delta loop.
def chainDoor (n : Nat) : Bool :=
  @Bool.rec (fun _ => Bool) false true (chain n)

theorem chain_door_short : chainDoor 100 = true := rfl
theorem chain_door_long : chainDoor 20000 = true := rfl

end Model
end Trust
