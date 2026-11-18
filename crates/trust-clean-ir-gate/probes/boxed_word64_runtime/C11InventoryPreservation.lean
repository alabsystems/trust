-- Copyright 2026 Andrew Yates | Apache-2.0
import C11InventoryContext

/-! Custody of the complete captured input/records through supported source
transitions. These are parser-state DATA facts, not successful C execution or
a source/target authentication premise. Local edits cannot erase the baseline. -/
namespace C11InventoryContext

def SameCaptured (before after : State) : Prop :=
  after.context.capturedInput = before.context.capturedInput ∧
  after.context.captured = before.context.captured

theorem step_preserves_capture (before after : State)
    (directive : C11ConditionalHeaders.Directive)
    (accepted : step before directive = some after) : SameCaptured before after := by
  cases directive with
  | condition expression =>
      cases selected : active before <;>
        cases observed : condition before expression <;>
        simp_all [step, SameCaptured]
      all_goals subst after; exact ⟨rfl, rfl⟩
  | elifCondition expression =>
      cases stack : before.stack with
      | nil => simp [step, stack] at accepted
      | cons frame rest =>
          cases saw : frame.sawElse <;>
            cases parent : frame.parent <;>
            cases taken : frame.taken <;>
            cases observed : condition before expression <;>
            simp_all [step, SameCaptured]
          all_goals subst after; exact ⟨rfl, rfl⟩
  | base directive =>
      cases directive with
      | empty => cases accepted; exact ⟨rfl, rfl⟩
      | ordinary tokens =>
          cases selected : active before <;> simp_all [step, SameCaptured]
          all_goals subst after; exact ⟨rfl, rfl⟩
      | ifdef name =>
          cases found : lookup before.context name <;> simp_all [step, SameCaptured]
          all_goals subst after; exact ⟨rfl, rfl⟩
      | ifndef name =>
          cases found : lookup before.context name <;> simp_all [step, SameCaptured]
          all_goals subst after; exact ⟨rfl, rfl⟩
      | otherwise =>
          cases stack : before.stack with
          | nil => simp [step, stack] at accepted
          | cons frame rest =>
              cases saw : frame.sawElse <;> simp_all [step, SameCaptured]
              all_goals subst after; exact ⟨rfl, rfl⟩
      | endif =>
          cases stack : before.stack with
          | nil => simp [step, stack] at accepted
          | cons frame rest =>
              simp_all [step, SameCaptured]
              all_goals subst after; exact ⟨rfl, rfl⟩
      | define name tokens =>
          cases reserved : (name == "defined") <;>
            cases selected : active before <;>
            cases found : lookup before.context name with
            | none => simp_all [step, SameCaptured]
            | some binding =>
                cases binding <;> simp_all [step, SameCaptured]
                all_goals subst after; exact ⟨rfl, rfl⟩
      | undef name =>
          cases selected : active before <;> simp_all [step, SameCaptured]
          all_goals subst after; exact ⟨rfl, rfl⟩
end C11InventoryContext
