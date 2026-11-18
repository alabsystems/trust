-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderGlobal
import C11HeaderExecutionControls

/-! Global-scenario witnesses/control failures for the restricted relation.
No implication that the real C runtime's allowed interference/rights are these
inputs, or that the missing C11/source adequacy theorem has been proved. -/
namespace C11HeaderGlobalControls
open C11HeaderAST C11HeaderGlobal

def race (observed old : UInt32) : Execution :=
  { distinguished := 1, events := [
    { thread := 0, operation := .initial observed, modification := some 0 },
    { thread := 1, operation := .load observed, readsFrom := some 0 },
    { thread := 2, operation := .store old, modification := some 1 },
    { thread := 1, operation := .rmw true 1 old (old - 1) .release,
      modification := some 2, readsFrom := some 2 },
    { thread := 1, operation := .acquireFence }] }

theorem race_trace (observed old : UInt32) :
    project (race observed old) = some
      [.load 0 observed, .rmw 1 old (old - 1) .release, .fence .acquire] := by rfl

/-- No selected successful-run premise: every pair of words gives a concrete
finite checked scenario in this explicit restricted relation. This is not the
missing C11 adequacy theorem. -/
theorem arbitrary_race_coherent (observed old : UInt32) :
    check (race observed old) = true := by
  simp [check, race, shape, modificationOrder, readFromValid, written, C11HeaderGlobal.read, List.range_succ,
    coherent, hb, ordered, sourceRank]

/-- Whole finite scenario, not just an arithmetic count relation. -/
theorem zero_race_has_coherent_scenario : check (race 4 0) = true := by rfl

theorem sticky_race_has_coherent_scenario : check (race 1 0xE0000000) = true := by rfl

/-- Same value is not enough: the RMW must still read its immediate predecessor. -/
theorem wrong_predecessor_even_with_equal_values_refused :
    check { distinguished := 1, events := [
      { thread := 0, operation := .initial 8, modification := some 0 },
      { thread := 1, operation := .load 8, readsFrom := some 0 },
      { thread := 2, operation := .store 8, modification := some 1 },
      { thread := 1, operation := .rmw true 1 8 7 .release,
        modification := some 2, readsFrom := some 0 }] } = false := by rfl

theorem duplicate_modification_rank_refused :
    check { distinguished := 1, events := [
      { thread := 0, operation := .initial 1, modification := some 0 },
      { thread := 2, operation := .store 2, modification := some 1 },
      { thread := 3, operation := .store 3, modification := some 1 }] } = false := by rfl

theorem wrong_rmw_arithmetic_refused :
    check { distinguished := 1, events := [
      { thread := 0, operation := .initial 8, modification := some 0 },
      { thread := 1, operation := .rmw true 1 8 9 .release,
        modification := some 1, readsFrom := some 0 }] } = false := by rfl

/-- A source-thread write cannot be read backwards by its later relaxed load. -/
theorem backwards_after_rmw_refused :
    check { distinguished := 1, events := [
      { thread := 0, operation := .initial 8, modification := some 0 },
      { thread := 1, operation := .rmw true 1 8 7 .release,
        modification := some 1, readsFrom := some 0 },
      { thread := 1, operation := .load 8, readsFrom := some 0 }] } = false := by rfl

/-- Other threads' RMWs/release operations are unsupported, never silently
classified as relaxed constant stores or deprived of synchronization effects. -/
theorem foreign_release_rmw_refused :
    check { distinguished := 1, events := [
      { thread := 0, operation := .initial 8, modification := some 0 },
      { thread := 2, operation := .rmw true 1 8 7 .release,
        modification := some 1, readsFrom := some 0 }] } = false := by rfl

/-- The actual zero-race AST execution and the finite global DATA relation
agree on the complete local trace, including the acquire fence. This still
supplies no actual-TU, C11 adequacy, allocator or ARC permission. -/
theorem zero_race_control_and_global :
    check (race 4 0) = true ∧
    project (race 4 0) = some [.load 0 4, .rmw 1 0 0xFFFFFFFF .release, .fence .acquire] ∧
    (C11HeaderExecutionControls.dropRun
      (C11HeaderExecutionControls.machine 4 [{}, { interference := [0] }])).map
      (fun (result, machine) => (result, machine.atomic.history, machine.atomic.events)) =
    .ok (some true, [4, 0, 0xFFFFFFFF],
      [.load 0 4, .rmw 1 0 0xFFFFFFFF .release, .fence .acquire]) :=
  ⟨zero_race_has_coherent_scenario, race_trace 4 0,
    C11HeaderExecutionControls.zero_race_wraps_and_fences⟩

#print axioms zero_race_has_coherent_scenario
#print axioms wrong_predecessor_even_with_equal_values_refused
end C11HeaderGlobalControls
