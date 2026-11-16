/- Boundary/noncollapse and mathematical source-equation controls only.
   These hand-written source functions are explicit witnesses, not substitutes
   for captured genuine CIC definitions or their environment-custody checks. -/
import CanonicalClosureSourceRefinement

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64

theorem raw_maximum_roundtrip :
    (UInt64.ofNat (wordModulus - 1)).toNat = wordModulus - 1 :=
  uint64_toNat_ofNat_bounded _ (by decide)

theorem high_half_survives :
    (UInt64.ofNat (2 ^ 32)).toNat = 2 ^ 32 ∧
    word (UInt64.ofNat (2 ^ 32)) ≠ rawWord 0 := by
  refine ⟨uint64_toNat_ofNat_bounded _ (by decide), ?_⟩
  have encoded := word_ofNat_bounded (2 ^ 32) (by decide)
  intro collapsed
  have same : rawWord (2 ^ 32) = rawWord 0 := encoded.symm.trans collapsed
  exact (by decide : (2 ^ 32 : Nat) ≠ 0) (rawWord_injective same)

/-- Boundedness matters: ofNat wraps at the first value outside the carrier,
    whereas the unbounded raw Value is still distinct. -/
theorem out_of_range_wraps :
    word (UInt64.ofNat wordModulus) = rawWord 0 ∧ rawWord wordModulus ≠ rawWord 0 := by
  refine ⟨?_, ?_⟩
  · rw [word_ofNat_mod, Nat.mod_self]
  · intro same
    exact (by decide : wordModulus ≠ 0) (rawWord_injective same)

theorem raw_wrap_result : ((wordModulus - 1) * 2 + 3) % wordModulus = 1 := by decide

theorem raw_wrap_execution (world : MachineState) :
    Sem.run (evalFunctionInContext (context 0) callerId
      [rawWord (wordModulus - 1), rawWord 3, rawWord 2] 3 .abort) (entryState world) =
      .ok ([rawWord 1], rawCallerState world (wordModulus - 1) 3 2) :=
  raw_caller_evaluates 0 world (wordModulus - 1) 3 2 (by decide) (by decide) (by decide)

theorem narrower_modulus_changes_result :
    (2 ^ 32) % wordModulus ≠ (2 ^ 32) % (2 ^ 32) := by decide

def equationMake (a b x : UInt64) : UInt64 := a * x + b
def equationApply (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x
def equationCall (a b x : UInt64) : UInt64 := equationApply (equationMake a b) x

theorem closed_equation_witness : SourceEquations equationMake equationApply equationCall :=
  ⟨by intro a b x; rfl, by intro f x; rfl, by intro a b x; rfl⟩

theorem closed_refinement_witness : SourceRefines equationMake equationApply equationCall :=
  source_refines_of_closed_equalities equationMake equationApply equationCall rfl rfl rfl

def changedEquationMake (a b x : UInt64) : UInt64 := a + x + b
def swappedEquationMake (a b x : UInt64) : UInt64 := b * x + a
def shiftedEquationApply (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f (x + 1)
def changedEquationCall (a b x : UInt64) : UInt64 := b * x + a

theorem changed_make_equation_refused :
    ¬ SourceEquations changedEquationMake equationApply equationCall := by
  intro equations
  exact (by decide : (10 : UInt64) ≠ 13) (equations.make_eq 2 3 5)

theorem swapped_make_equation_refused :
    ¬ SourceEquations swappedEquationMake equationApply equationCall := by
  intro equations
  exact (by decide : (17 : UInt64) ≠ 13) (equations.make_eq 2 3 5)

theorem shifted_apply_equation_refused :
    ¬ SourceEquations equationMake shiftedEquationApply equationCall := by
  intro equations
  exact (by decide : (1 : UInt64) ≠ 0) (equations.apply_eq (fun x => x) 0)

theorem changed_call_equation_refused :
    ¬ SourceEquations equationMake equationApply changedEquationCall := by
  intro equations
  exact (by decide : (17 : UInt64) ≠ 13) (equations.call_eq 2 3 5)

/-- These conclusions refute the full relation, not just a producer label. -/
theorem changed_source_refinement_refused :
    ¬ SourceRefines changedEquationMake equationApply equationCall :=
  fun refined => changed_make_equation_refused refined.equations

theorem shifted_source_refinement_refused :
    ¬ SourceRefines equationMake shiftedEquationApply equationCall :=
  fun refined => shifted_apply_equation_refused refined.equations

theorem changed_caller_refinement_refused :
    ¬ SourceRefines equationMake equationApply changedEquationCall :=
  fun refined => changed_call_equation_refused refined.equations

#print axioms raw_wrap_execution
#print axioms closed_refinement_witness
#print axioms changed_source_refinement_refused
end CanonicalClosure
