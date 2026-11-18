-- Copyright 2026 Andrew Yates | Apache-2.0
import C11InventoryContext
import C11PredefinedLookupCuts
import C11AssertHeaderActual
namespace C11AssertInventory
open C11InventoryContext C11PredefinedLookupCuts
/-! Closed COMPLETE-input/inventory-MODEL relation only. No actual frontend
completeness, implicit builtin absence, target/TU or C execution follows. -/
def runLine (state : State) (line : List String) : Option State := do
  let directive ← C11ConditionalHeaders.parseLine line
  step state directive
def actualLines : List (List String) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], ["#", "ifndef", "_ASSERT_H_"], ["#", "define", "_ASSERT_H_"], [], ["#", "ifndef", "__cplusplus"], ["#", "if", "defined", "(", "__STDC_VERSION__", ")", "&&", "__STDC_VERSION__", ">=", "201112L"], ["#", "define", "static_assert", "_Static_assert"], ["#", "endif"], ["#", "endif"], [], ["#", "endif"]]
 theorem actual_source_lines : C11HeaderGuards.lines C11AssertHeaderCuts.assertHeader_tokens = some actualLines := by rfl
def state0 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
def state1 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step0 : runLine state0 [] = some state1 := by
  rfl
def state2 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step1 : runLine state1 [] = some state2 := by
  rfl
def state3 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step2 : runLine state2 [] = some state3 := by
  rfl
def state4 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step3 : runLine state3 [] = some state4 := by
  rfl
def state5 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step4 : runLine state4 [] = some state5 := by
  rfl
def state6 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step5 : runLine state5 [] = some state6 := by
  rfl
def state7 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step6 : runLine state6 [] = some state7 := by
  rfl
def state8 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step7 : runLine state7 [] = some state8 := by
  rfl
def state9 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step8 : runLine state8 [] = some state9 := by
  rfl
def state10 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step9 : runLine state9 [] = some state10 := by
  rfl
def state11 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step10 : runLine state10 [] = some state11 := by
  rfl
def state12 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step11 : runLine state11 [] = some state12 := by
  rfl
def state13 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step12 : runLine state12 [] = some state13 := by
  rfl
def state14 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step13 : runLine state13 [] = some state14 := by
  rfl
def state15 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step14 : runLine state14 [] = some state15 := by
  rfl
def state16 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step15 : runLine state15 [] = some state16 := by
  rfl
def state17 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step16 : runLine state16 [] = some state17 := by
  rfl
def state18 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step17 : runLine state17 [] = some state18 := by
  rfl
def state19 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step18 : runLine state18 [] = some state19 := by
  rfl
def state20 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step19 : runLine state19 [] = some state20 := by
  rfl
def state21 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step20 : runLine state20 [] = some state21 := by
  rfl
def state22 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step21 : runLine state21 [] = some state22 := by
  rfl
def state23 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [] }
theorem line_step22 : runLine state22 [] = some state23 := by
  rfl
def state24 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [] }, stack := [{ parent := true, active := true, taken := true }] }
theorem lookup_state23 : lookup state23.context "_ASSERT_H_" = some none := by
  rw [lookup_capture_fallback _ _ (by rfl) (by rfl)]
  simp only [state23]
  rw [captured_guard_lookup] <;> rfl

theorem parsed_line23 : C11ConditionalHeaders.parseLine ["#", "ifndef", "_ASSERT_H_"] = some (.base (.ifndef "_ASSERT_H_")) := by rfl
theorem line_step23 : runLine state23 ["#", "ifndef", "_ASSERT_H_"] = some state24 := by
  rw [runLine, parsed_line23]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [C11InventoryContext.step.eq_def]
  dsimp only
  rw [lookup_state23] <;> rfl
def state25 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("_ASSERT_H_", [])] }, stack := [{ parent := true, active := true, taken := true }] }
theorem lookup_state24 : lookup state24.context "_ASSERT_H_" = some none := by
  rw [lookup_capture_fallback _ _ (by rfl) (by rfl)]
  simp only [state24]
  rw [captured_guard_lookup] <;> rfl

theorem parsed_line24 : C11ConditionalHeaders.parseLine ["#", "define", "_ASSERT_H_"] = some (.base (.define "_ASSERT_H_" [])) := by rfl
theorem line_step24 : runLine state24 ["#", "define", "_ASSERT_H_"] = some state25 := by
  rw [runLine, parsed_line24]
  simp only [Option.bind_eq_bind, Option.bind_some]
  simpa only [state24, state25] using
    (define_fresh state24 "_ASSERT_H_" [] (by rfl) (by rfl) lookup_state24)

def state26 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("_ASSERT_H_", [])] }, stack := [{ parent := true, active := true, taken := true }] }
theorem line_step25 : runLine state25 [] = some state26 := by
  rfl
def state27 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("_ASSERT_H_", [])] }, stack := [{ parent := true, active := true, taken := true }, { parent := true, active := true, taken := true }] }
theorem lookup_state26 : lookup state26.context "__cplusplus" = some none := by
  rw [lookup_capture_fallback _ _ (by rfl) (by rfl)]
  simp only [state26]
  rw [captured_cpp_lookup] <;> rfl

theorem parsed_line26 : C11ConditionalHeaders.parseLine ["#", "ifndef", "__cplusplus"] = some (.base (.ifndef "__cplusplus")) := by rfl
theorem line_step26 : runLine state26 ["#", "ifndef", "__cplusplus"] = some state27 := by
  rw [runLine, parsed_line26]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [C11InventoryContext.step.eq_def]
  dsimp only
  rw [lookup_state26] <;> rfl
def state28 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("_ASSERT_H_", [])] }, stack := [{ parent := true, active := true, taken := true }, { parent := true, active := true, taken := true }, { parent := true, active := true, taken := true }] }
theorem version_lookup_state27 : lookup state27.context "__STDC_VERSION__" = some (some (.captured C11PredefinedData.record355)) := by
  rw [lookup_capture_fallback _ _ (by rfl) (by rfl)]
  simp only [state27]
  rw [captured_version_lookup] <;> rfl

theorem version_value_state27 : value 64 state27.context "__STDC_VERSION__" = some 201112 := by
  rw [value, version_lookup_state27] <;> rfl

theorem source_condition_state27 : condition state27 (C11PPConditions.Expr.and (.defined "__STDC_VERSION__") (.compare .ge (.identifier "__STDC_VERSION__") (.number 201112))) = some true := by
  simp only [condition, resolve, version_lookup_state27, version_value_state27]
  rfl

theorem parsed_line27 : C11ConditionalHeaders.parseLine ["#", "if", "defined", "(", "__STDC_VERSION__", ")", "&&", "__STDC_VERSION__", ">=", "201112L"] = some (.condition (C11PPConditions.Expr.and (.defined "__STDC_VERSION__") (.compare .ge (.identifier "__STDC_VERSION__") (.number 201112)))) := by rfl
theorem line_step27 : runLine state27 ["#", "if", "defined", "(", "__STDC_VERSION__", ")", "&&", "__STDC_VERSION__", ">=", "201112L"] = some state28 := by
  rw [runLine, parsed_line27]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [C11InventoryContext.step.eq_def]
  dsimp only
  rw [source_condition_state27] <;> rfl
def state29 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("static_assert", ["_Static_assert"]), ("_ASSERT_H_", [])] }, stack := [{ parent := true, active := true, taken := true }, { parent := true, active := true, taken := true }, { parent := true, active := true, taken := true }] }
theorem lookup_state28 : lookup state28.context "static_assert" = some none := by
  rw [lookup_capture_fallback _ _ (by rfl) (by rfl)]
  simp only [state28]
  rw [captured_static_lookup] <;> rfl

theorem parsed_line28 : C11ConditionalHeaders.parseLine ["#", "define", "static_assert", "_Static_assert"] = some (.base (.define "static_assert" ["_Static_assert"])) := by rfl
theorem line_step28 : runLine state28 ["#", "define", "static_assert", "_Static_assert"] = some state29 := by
  rw [runLine, parsed_line28]
  simp only [Option.bind_eq_bind, Option.bind_some]
  simpa only [state28, state29] using
    (define_fresh state28 "static_assert" ["_Static_assert"] (by rfl) (by rfl) lookup_state28)

def state30 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("static_assert", ["_Static_assert"]), ("_ASSERT_H_", [])] }, stack := [{ parent := true, active := true, taken := true }, { parent := true, active := true, taken := true }] }
theorem line_step29 : runLine state29 ["#", "endif"] = some state30 := by
  rfl
def state31 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("static_assert", ["_Static_assert"]), ("_ASSERT_H_", [])] }, stack := [{ parent := true, active := true, taken := true }] }
theorem line_step30 : runLine state30 ["#", "endif"] = some state31 := by
  rfl
def state32 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("static_assert", ["_Static_assert"]), ("_ASSERT_H_", [])] }, stack := [{ parent := true, active := true, taken := true }] }
theorem line_step31 : runLine state31 [] = some state32 := by
  rfl
def state33 : State := { context := { capturedInput := C11PredefinedData.actualCharacters, captured := C11PredefinedData.actualRecords, locals := [("static_assert", ["_Static_assert"]), ("_ASSERT_H_", [])] }, stack := [] }
theorem line_step32 : runLine state32 ["#", "endif"] = some state33 := by
  rfl

/-- Small generic composition: concrete inventories stay opaque in the proof
term rather than being normalized by a whole-program simplifier. -/
theorem fold_step (line : List String) (tail : List (List String))
    (before middle after : State)
    (head : runLine before line = some middle)
    (rest : tail.foldlM runLine middle = some after) :
    (line :: tail).foldlM runLine before = some after := by
  simp only [List.foldlM_cons, Option.bind_eq_bind]
  rw [head]
  simpa only [Option.bind_some] using rest

def suffix33 : List (List String) := []
theorem run_suffix33 : suffix33.foldlM runLine state33 = some state33 := by rfl
def suffix32 : List (List String) := ["#", "endif"] :: suffix33
theorem run_suffix32 : suffix32.foldlM runLine state32 = some state33 :=
  fold_step _ _ _ _ _ line_step32 run_suffix33
def suffix31 : List (List String) := [] :: suffix32
theorem run_suffix31 : suffix31.foldlM runLine state31 = some state33 :=
  fold_step _ _ _ _ _ line_step31 run_suffix32
def suffix30 : List (List String) := ["#", "endif"] :: suffix31
theorem run_suffix30 : suffix30.foldlM runLine state30 = some state33 :=
  fold_step _ _ _ _ _ line_step30 run_suffix31
def suffix29 : List (List String) := ["#", "endif"] :: suffix30
theorem run_suffix29 : suffix29.foldlM runLine state29 = some state33 :=
  fold_step _ _ _ _ _ line_step29 run_suffix30
def suffix28 : List (List String) := ["#", "define", "static_assert", "_Static_assert"] :: suffix29
theorem run_suffix28 : suffix28.foldlM runLine state28 = some state33 :=
  fold_step _ _ _ _ _ line_step28 run_suffix29
def suffix27 : List (List String) := ["#", "if", "defined", "(", "__STDC_VERSION__", ")", "&&", "__STDC_VERSION__", ">=", "201112L"] :: suffix28
theorem run_suffix27 : suffix27.foldlM runLine state27 = some state33 :=
  fold_step _ _ _ _ _ line_step27 run_suffix28
def suffix26 : List (List String) := ["#", "ifndef", "__cplusplus"] :: suffix27
theorem run_suffix26 : suffix26.foldlM runLine state26 = some state33 :=
  fold_step _ _ _ _ _ line_step26 run_suffix27
def suffix25 : List (List String) := [] :: suffix26
theorem run_suffix25 : suffix25.foldlM runLine state25 = some state33 :=
  fold_step _ _ _ _ _ line_step25 run_suffix26
def suffix24 : List (List String) := ["#", "define", "_ASSERT_H_"] :: suffix25
theorem run_suffix24 : suffix24.foldlM runLine state24 = some state33 :=
  fold_step _ _ _ _ _ line_step24 run_suffix25
def suffix23 : List (List String) := ["#", "ifndef", "_ASSERT_H_"] :: suffix24
theorem run_suffix23 : suffix23.foldlM runLine state23 = some state33 :=
  fold_step _ _ _ _ _ line_step23 run_suffix24
def suffix22 : List (List String) := [] :: suffix23
theorem run_suffix22 : suffix22.foldlM runLine state22 = some state33 :=
  fold_step _ _ _ _ _ line_step22 run_suffix23
def suffix21 : List (List String) := [] :: suffix22
theorem run_suffix21 : suffix21.foldlM runLine state21 = some state33 :=
  fold_step _ _ _ _ _ line_step21 run_suffix22
def suffix20 : List (List String) := [] :: suffix21
theorem run_suffix20 : suffix20.foldlM runLine state20 = some state33 :=
  fold_step _ _ _ _ _ line_step20 run_suffix21
def suffix19 : List (List String) := [] :: suffix20
theorem run_suffix19 : suffix19.foldlM runLine state19 = some state33 :=
  fold_step _ _ _ _ _ line_step19 run_suffix20
def suffix18 : List (List String) := [] :: suffix19
theorem run_suffix18 : suffix18.foldlM runLine state18 = some state33 :=
  fold_step _ _ _ _ _ line_step18 run_suffix19
def suffix17 : List (List String) := [] :: suffix18
theorem run_suffix17 : suffix17.foldlM runLine state17 = some state33 :=
  fold_step _ _ _ _ _ line_step17 run_suffix18
def suffix16 : List (List String) := [] :: suffix17
theorem run_suffix16 : suffix16.foldlM runLine state16 = some state33 :=
  fold_step _ _ _ _ _ line_step16 run_suffix17
def suffix15 : List (List String) := [] :: suffix16
theorem run_suffix15 : suffix15.foldlM runLine state15 = some state33 :=
  fold_step _ _ _ _ _ line_step15 run_suffix16
def suffix14 : List (List String) := [] :: suffix15
theorem run_suffix14 : suffix14.foldlM runLine state14 = some state33 :=
  fold_step _ _ _ _ _ line_step14 run_suffix15
def suffix13 : List (List String) := [] :: suffix14
theorem run_suffix13 : suffix13.foldlM runLine state13 = some state33 :=
  fold_step _ _ _ _ _ line_step13 run_suffix14
def suffix12 : List (List String) := [] :: suffix13
theorem run_suffix12 : suffix12.foldlM runLine state12 = some state33 :=
  fold_step _ _ _ _ _ line_step12 run_suffix13
def suffix11 : List (List String) := [] :: suffix12
theorem run_suffix11 : suffix11.foldlM runLine state11 = some state33 :=
  fold_step _ _ _ _ _ line_step11 run_suffix12
def suffix10 : List (List String) := [] :: suffix11
theorem run_suffix10 : suffix10.foldlM runLine state10 = some state33 :=
  fold_step _ _ _ _ _ line_step10 run_suffix11
def suffix9 : List (List String) := [] :: suffix10
theorem run_suffix9 : suffix9.foldlM runLine state9 = some state33 :=
  fold_step _ _ _ _ _ line_step9 run_suffix10
def suffix8 : List (List String) := [] :: suffix9
theorem run_suffix8 : suffix8.foldlM runLine state8 = some state33 :=
  fold_step _ _ _ _ _ line_step8 run_suffix9
def suffix7 : List (List String) := [] :: suffix8
theorem run_suffix7 : suffix7.foldlM runLine state7 = some state33 :=
  fold_step _ _ _ _ _ line_step7 run_suffix8
def suffix6 : List (List String) := [] :: suffix7
theorem run_suffix6 : suffix6.foldlM runLine state6 = some state33 :=
  fold_step _ _ _ _ _ line_step6 run_suffix7
def suffix5 : List (List String) := [] :: suffix6
theorem run_suffix5 : suffix5.foldlM runLine state5 = some state33 :=
  fold_step _ _ _ _ _ line_step5 run_suffix6
def suffix4 : List (List String) := [] :: suffix5
theorem run_suffix4 : suffix4.foldlM runLine state4 = some state33 :=
  fold_step _ _ _ _ _ line_step4 run_suffix5
def suffix3 : List (List String) := [] :: suffix4
theorem run_suffix3 : suffix3.foldlM runLine state3 = some state33 :=
  fold_step _ _ _ _ _ line_step3 run_suffix4
def suffix2 : List (List String) := [] :: suffix3
theorem run_suffix2 : suffix2.foldlM runLine state2 = some state33 :=
  fold_step _ _ _ _ _ line_step2 run_suffix3
def suffix1 : List (List String) := [] :: suffix2
theorem run_suffix1 : suffix1.foldlM runLine state1 = some state33 :=
  fold_step _ _ _ _ _ line_step1 run_suffix2
def suffix0 : List (List String) := [] :: suffix1
theorem run_suffix0 : suffix0.foldlM runLine state0 = some state33 :=
  fold_step _ _ _ _ _ line_step0 run_suffix1

theorem actual_lines_suffix : actualLines = suffix0 := by rfl

theorem complete_lines_run : actualLines.foldlM runLine state0 = some state33 :=
  (congrArg (fun lines => lines.foldlM runLine state0) actual_lines_suffix).trans run_suffix0

/-- This is a pipeline DATA composition lemma, not a successful C-run premise.
The closed theorem below supplies all three concrete checked equations. -/
theorem pipeline_success (tokens : List String) (lines : List (List String))
    (before after : State)
    (lexicalLines : C11HeaderGuards.lines tokens = some lines)
    (flow : lines.foldlM runLine before = some after)
    (emptyStack : after.stack = []) :
    (do
      let lines ← C11HeaderGuards.lines tokens
      let state ← lines.foldlM runLine before
      if state.stack.isEmpty then some state else none) = some after := by
  rw [lexicalLines]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [flow]
  simp only [Option.bind_some, emptyStack] <;> rfl

theorem complete_header_inventory_model :
    process C11PredefinedData.actualCharacters C11AssertHeaderData.assertHeader_0 = some state33 :=
  (process_readers _ _ _ _ C11PredefinedCuts.complete_captured_records
    C11AssertDirectiveCuts.complete_source_supported
    C11AssertHeaderActual.complete_source_final_newline
    C11AssertHeaderCuts.assertHeader_source_lex).trans
    (pipeline_success _ _ state0 state33 actual_source_lines complete_lines_run rfl)
end C11AssertInventory
