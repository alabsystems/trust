-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-09 sanity facts for Trust.List and Trust.Graph (model_prelude_kernel.rs,
-- sanity_files): elaborated after the whole model prelude, and every theorem below is
-- accepted by check_model_theorem (kernel re-check, constructive, axiom-free, audited).
-- Computed facts are Bool doors closed by rfl (B1A-D54); the mutated-literal doors of
-- SANITY_MUTANTS must each be refuted (class Definite), so these doors are not vacuous.
-- Definitional facts (the design's equations, 40:55-65) are closed by rfl.

namespace Trust
namespace Temporal
namespace Sanity

-- ---- Member: the alias and FiniteModel.Member are one predicate (B1A-D04) ----

theorem member_alias {α : Type} (value : α) (values : List α) :
    Member value values = FiniteModel.Member value values := rfl
theorem member_to_finite_model {α : Type} (value : α) (values : List α)
    (h : Member value values) : FiniteModel.Member value values := h
theorem member_from_finite_model {α : Type} (value : α) (values : List α)
    (h : FiniteModel.Member value values) : Member value values := h
theorem member_head : Member 2 [2, 5] := FiniteModel.Member.head [5]
theorem member_tail : Member 5 [2, 5] :=
  FiniteModel.Member.tail 2 [5] (FiniteModel.Member.head [])
-- FiniteModel's `everyMember` consumes an alias proof unchanged.
theorem member_every : Nat.beq 5 5 = true :=
  FiniteModel.everyMember (fun x => Nat.beq x x = true) 5 [2, 5]
    (And.intro rfl (And.intro rfl True.intro)) member_tail

-- ---- Distinct ----

theorem distinct_nil {α : Type} : Distinct ([] : List α) = True := rfl
theorem distinct_cons {α : Type} (head : α) (tail : List α) :
    Distinct (head :: tail) = (¬ Member head tail ∧ Distinct tail) := rfl
theorem true_ne_false (h : true = false) : False := @Bool.noConfusion False true false h
theorem false_ne_true (h : false = true) : False := @Bool.noConfusion False false true h
-- `everyMember` over the predicate "differs from the value": a member would differ from
-- itself.
theorem not_member_one : ¬ Member 1 [2] := fun h =>
  true_ne_false
    (@FiniteModel.everyMember Nat (fun x => Nat.beq x 1 = false) 1 [2]
      (And.intro rfl True.intro) h)
theorem not_member_nil : ¬ Member 2 ([] : List Nat) := fun h =>
  true_ne_false
    (@FiniteModel.everyMember Nat (fun x => Nat.beq x 2 = false) 2 [] True.intro h)
theorem distinct_one_two : Distinct [1, 2] :=
  And.intro not_member_one (And.intro not_member_nil True.intro)
theorem not_distinct_one_one : ¬ Distinct [1, 1] := fun h =>
  h.1 (FiniteModel.Member.head [])

-- ---- the Bool helpers, through doors ----

def optIs (o : Option Nat) (v : Nat) : Bool :=
  @Option.rec Nat (fun _ => Bool) false (fun x => Nat.beq x v) o
def optNone (o : Option Nat) : Bool :=
  @Option.rec Nat (fun _ => Bool) true (fun _ => false) o

theorem memBy_hit : memBy Nat.beq 3 [1, 2, 3] = true := rfl
theorem memBy_miss : Bool.not (memBy Nat.beq 4 [1, 2, 3]) = true := rfl
theorem memBy_nil : Bool.not (memBy Nat.beq 1 []) = true := rfl

-- The first matching entry wins.
theorem lookupBy_first : optIs (lookupBy Nat.beq 2 [(1, 10), (2, 20), (2, 30)]) 20 = true := rfl
theorem lookupBy_miss : optNone (lookupBy Nat.beq 3 [(1, 10), (2, 20)]) = true := rfl
theorem lookupBy_nil : optNone (lookupBy Nat.beq 3 ([] : List (Nat × Nat))) = true := rfl

theorem nthD_zero : Nat.beq (nthD [5, 6, 7] 0 9) 5 = true := rfl
theorem nthD_one : Nat.beq (nthD [5, 6, 7] 1 9) 6 = true := rfl
theorem nthD_last : Nat.beq (nthD [5, 6, 7] 2 9) 7 = true := rfl
theorem nthD_past : Nat.beq (nthD [5, 6, 7] 3 9) 9 = true := rfl
theorem nthD_nil : Nat.beq (nthD [] 0 4) 4 = true := rfl

theorem allB_true : allB (fun x => Nat.blt 0 x) [1, 2] = true := rfl
theorem allB_false : Bool.not (allB (fun x => Nat.blt 0 x) [1, 0]) = true := rfl
theorem allB_nil : allB (fun x => Nat.blt 0 x) [] = true := rfl

theorem anyB_true : anyB (Nat.beq 2) [1, 2] = true := rfl
theorem anyB_false : Bool.not (anyB (Nat.beq 3) [1, 2]) = true := rfl
theorem anyB_nil : Bool.not (anyB (Nat.beq 3) []) = true := rfl

-- insertBy appends a new element and leaves a present one where it is.
-- The whole list, through a door (TASK-STATE 4.8): length and every position.
theorem insertBy_new :
    Bool.and (Nat.beq (List.length (insertBy Nat.beq 3 [1, 2])) 3)
      (Bool.and (Nat.beq (nthD (insertBy Nat.beq 3 [1, 2]) 0 0) 1)
        (Bool.and (Nat.beq (nthD (insertBy Nat.beq 3 [1, 2]) 1 0) 2)
          (Nat.beq (nthD (insertBy Nat.beq 3 [1, 2]) 2 0) 3))) = true := rfl
theorem insertBy_present :
    Bool.and (Nat.beq (List.length (insertBy Nat.beq 2 [1, 2])) 2)
      (Bool.and (Nat.beq (nthD (insertBy Nat.beq 2 [1, 2]) 0 0) 1)
        (Nat.beq (nthD (insertBy Nat.beq 2 [1, 2]) 1 0) 2)) = true := rfl
theorem insertBy_new_door : Nat.beq (nthD (insertBy Nat.beq 3 [1, 2]) 2 0) 3 = true := rfl
theorem insertBy_present_door : Nat.beq (List.length (insertBy Nat.beq 2 [1, 2])) 2 = true := rfl

theorem lengthEqB_equal : lengthEqB [1, 2] [true, false] = true := rfl
theorem lengthEqB_shorter : Bool.not (lengthEqB [1] [true, false]) = true := rfl
theorem lengthEqB_longer : Bool.not (lengthEqB [1, 2] [true]) = true := rfl
theorem lengthEqB_nil : lengthEqB ([] : List Nat) ([] : List Bool) = true := rfl

-- ---- Graph: the design's equations (40:55-65), by rfl ----

theorem chain_nil {S : Type} (M : StateMachine S) (s : S) : Chain M s [] = True := rfl
theorem chain_cons {S : Type} (M : StateMachine S) (s t : S) (rest : List S) :
    Chain M s (t :: rest) = (M.next s t ∧ Chain M t rest) := rfl
theorem lastOf_nil {S : Type} (s : S) : lastOf s [] = s := rfl
theorem lastOf_cons {S : Type} (s t : S) (rest : List S) : lastOf s (t :: rest) = lastOf t rest := rfl
theorem firstAtEnd_nil {S : Type} (Y : S → Prop) (s : S) : FirstAtEnd Y s [] = True := rfl
theorem firstAtEnd_cons {S : Type} (Y : S → Prop) (s t : S) (rest : List S) :
    FirstAtEnd Y s (t :: rest) = (¬ Y s ∧ FirstAtEnd Y t rest) := rfl
theorem witnessPath_def {S : Type} (M : StateMachine S) (w : List S) :
    WitnessPath M w = (∃ s₀ p, w = s₀ :: p ∧ M.init s₀ ∧ Chain M s₀ p) := rfl
theorem terminal_def {S : Type} (M : StateMachine S) (s : S) :
    Terminal M s = (¬ ∃ t, M.next s t) := rfl

-- ---- Graph: facts on a counter and on a machine with no step ----

def counter : StateMachine Nat := StateMachine.mk (fun s => s = 0) (fun s t => t = s + 1)
def halted : StateMachine Nat := StateMachine.mk (fun s => s = 0) (fun _ _ => False)

theorem counter_not_terminal : ¬ Terminal counter 0 := fun h => h (Exists.intro 1 rfl)
theorem halted_terminal : Terminal halted 0 := fun h => Exists.elim h (fun _ step => step)
theorem reach_two : Reach counter 2 := Reach.step (Reach.step (Reach.init rfl) rfl) rfl
theorem star_zero_two : Star counter 0 2 := Star.tail (Star.tail (Star.refl 0) rfl) rfl
theorem chain_counter : Chain counter 0 [1, 2] := And.intro rfl (And.intro rfl True.intro)
theorem witness_counter : WitnessPath counter [0, 1, 2] :=
  Exists.intro 0 (Exists.intro [1, 2] (And.intro rfl (And.intro rfl chain_counter)))
theorem maxPath_counter : MaxPath counter 0 (fun n => n) :=
  And.intro rfl (fun _ => Or.inl rfl)
theorem maxPath_halted : MaxPath halted 0 (fun _ => 0) :=
  And.intro rfl (fun _ => Or.inr (And.intro halted_terminal rfl))
theorem lastOf_door : Nat.beq (lastOf 0 [1, 2, 3]) 3 = true := rfl
theorem lastOf_nil_door : Nat.beq (lastOf 4 []) 4 = true := rfl
-- Y = "is 2": it holds at no position of [0, 1, 2] before the last.
theorem firstAtEnd_counter : FirstAtEnd (fun s => Nat.beq s 2 = true) 0 [1, 2] :=
  And.intro (fun h => false_ne_true h) (And.intro (fun h => false_ne_true h) True.intro)

end Sanity
end Temporal
end Trust
