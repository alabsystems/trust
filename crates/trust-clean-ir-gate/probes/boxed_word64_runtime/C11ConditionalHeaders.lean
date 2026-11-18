-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderGuards
import C11PPConditions
import C11DirectiveLexer
import C11DirectiveLines
import C11ConditionCuts
import C11ConditionDirectiveCuts

/-! #if/#elif transitions derived from complete parsed condition tokens.
The proposed initial object context is explicit DATA, not actual predefined/
include/TU authentication. All source lines parse before execution; unsupported
syntax never becomes a false Boolean. Output remains active and UNEXPANDED.
Includes, general expressions/extensions and full preprocessing remain owed. -/
namespace C11ConditionalHeaders
open C11HeaderGuards
inductive Directive where
  | base (directive : C11HeaderGuards.Directive)
  | condition (expression : C11PPConditions.Expr)
  | elifCondition (expression : C11PPConditions.Expr)
  deriving DecidableEq, BEq, Repr

def parseLine : List String → Option Directive
  | "#" :: "if" :: rest => do return .condition (← C11PPConditions.parseTokens rest)
  | "#" :: "elif" :: rest => do return .elifCondition (← C11PPConditions.parseTokens rest)
  | tokens => do return .base (← C11HeaderGuards.parseLine tokens)

def condition (state : State) (expression : C11PPConditions.Expr) : Option Bool := do
  if state.macros.any (fun entry => entry.1 == "defined") then none else do
    let resolved ← C11PPConditions.resolve { macros := state.macros } expression
    return C11PPConditions.evaluate resolved != 0

def step (state : State) : Directive → Option State
  | .base (.define "defined" _) => none
  | .base directive => C11HeaderGuards.step state directive
  | .condition expression => do
      let parent := active state
      let selected ← if parent then condition state expression else some false
      return { state with stack := { parent := parent, active := parent && selected, taken := parent && selected } :: state.stack }
  | .elifCondition expression => do
      let frame :: rest := state.stack | none
      if frame.sawElse then none else do
        let selected ← if frame.parent && !frame.taken then condition state expression else some false
        return { state with stack := { frame with active := frame.parent && !frame.taken && selected, taken := frame.taken || selected } :: rest }

def processTokens (initialMacros : List (String × List String)) (tokens : List String) : Option State := do
  if !validInitial initialMacros || initialMacros.any (fun entry => entry.1 == "defined") then none else do
    let lines ← C11HeaderGuards.lines tokens
    let state ← lines.foldlM (fun state line => do
      let directive ← parseLine line
      step state directive) { macros := initialMacros }
    if state.stack.isEmpty then some state else none

def process (initialMacros : List (String × List String)) (source : String) : Option State := do
  if !C11DirectiveLines.supported source then none else do
    if !source.isEmpty && source.toList.getLast? != some '\n' then none else do
      let tokens ← C11DirectiveLexer.tokenize source
      processTokens initialMacros tokens

/-- Unit control using actual stdbool condition forms, NOT a quotation of its
whole header. Actual include/extension context is intentionally not claimed. -/
def branchControl := C11ConditionData.branch_0

theorem branch_source_supported : C11DirectiveLines.supported branchControl = true :=
  C11ConditionDirectiveCuts.complete_source_supported

theorem branch_source_newline : branchControl.toList.getLast? = some '\n' := by
  unfold branchControl
  rw [← C11ConditionCuts.branch_string_exact,
      C11ConditionCuts.branch_node_0_16_characters]
  rfl

theorem branch_source_tokens : C11DirectiveLexer.tokenize branchControl = some C11ConditionCuts.branch_tokens :=
  C11ConditionCuts.branch_source_lex

theorem source_conditions_choose_branch :
    (process [("__STDC_VERSION__", ["201112L"])] branchControl).map
      (fun state => state.reversedOutput.reverse) = some [["selected"]] := by
  unfold process
  rw [branch_source_supported, branch_source_newline]
  rw [Bool.and_comm]
  rw [branch_source_tokens]
  rfl

theorem earlier_taken_branch_suppresses_elif :
    (process [] "#if 1\nfirst\n#elif 1\nsecond\n#endif\n").map
      (fun state => state.reversedOutput.reverse) = some [["first"]] := by rfl

theorem elif_after_else_refused : process [] "#if 0\n#else\n#elif 1\n#endif\n" = none := by rfl

theorem malformed_condition_cannot_hide :
    process [] "#if 0 && unknown_function()\nwrong\n#endif\n" = none := by rfl

theorem false_rhs_expansion_still_checked :
    process [("bad", ["1", "+", "1"])] "#if 0 && bad\nwrong\n#endif\n" = none := by rfl

theorem defined_operator_cannot_be_context_masked :
    process [("defined", ["0"])] "#if defined(x)\nwrong\n#endif\n" = none := by rfl

theorem defined_operator_cannot_be_source_masked :
    process [] "#define defined 0\n#if 1\nwrong\n#endif\n" = none := by rfl

#print axioms source_conditions_choose_branch
#print axioms malformed_condition_cannot_hide
end C11ConditionalHeaders
