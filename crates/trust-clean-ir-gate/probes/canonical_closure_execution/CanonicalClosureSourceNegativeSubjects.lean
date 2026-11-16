/- Indexed replay controls over actual Lean mathematical fixture definitions.
   These are not captured-frontdoor source controls. The different verifier
   checks the same original proof against each genuinely changed proposition;
   importing a false proposition as DATA never supplies a proof of it. -/
import CanonicalClosureWordControls

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64

theorem make_equation_advice : ∀ a b x, equationMake a b x = a * x + b := by
  intro a b x
  rfl

theorem apply_equation_advice : ∀ f x, equationApply f x = f x := by
  intro f x
  rfl

theorem call_equation_advice : ∀ a b x,
    equationCall a b x = equationApply (equationMake a b) x := by
  intro a b x
  rfl

def changed_make_equation_subject : Prop :=
  ∀ a b x, changedEquationMake a b x = a * x + b

def swapped_make_equation_subject : Prop :=
  ∀ a b x, swappedEquationMake a b x = a * x + b

def shifted_apply_equation_subject : Prop :=
  ∀ f x, shiftedEquationApply f x = f x

def changed_call_equation_subject : Prop :=
  ∀ a b x, changedEquationCall a b x = equationApply (equationMake a b) x

def changed_make_refinement_subject : Prop :=
  SourceRefines changedEquationMake equationApply equationCall

def swapped_make_refinement_subject : Prop :=
  SourceRefines swappedEquationMake equationApply equationCall

def shifted_apply_refinement_subject : Prop :=
  SourceRefines equationMake shiftedEquationApply equationCall

def changed_call_refinement_subject : Prop :=
  SourceRefines equationMake equationApply changedEquationCall

#print axioms make_equation_advice
#print axioms apply_equation_advice
#print axioms call_equation_advice
end CanonicalClosure
