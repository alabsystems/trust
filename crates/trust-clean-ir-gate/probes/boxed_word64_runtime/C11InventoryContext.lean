-- Copyright 2026 Andrew Yates | Apache-2.0
import C11ConditionalHeaders
import C11PredefinedRecords

/-! Supported header processing retains the WHOLE original inventory and input,
with explicit local edits/tombstones. It does not replace that inventory by a
selected list of known macro names. The inventory is captured DATA, not proof
of compiler/predefined-target authenticity, a complete actual TU, general macro
validity/expansion or C execution. Every branch derives from parsed source IN THIS INVENTORY MODEL.
Captured -dM absence is not actual frontend absence (builtin operators may be
omitted by -dM); no actual-world context completeness is inferred here.
Unsupported reached replacements refuse; unused opaque tails stay retained. -/
namespace C11InventoryContext
open C11HeaderGuards
structure Context where
  capturedInput : List Char := []
  captured : List C11PredefinedRecords.Record := []
  locals : List (String × List String) := []
  removed : List String := []
  deriving Repr
inductive Binding where
  | captured (record : C11PredefinedRecords.Record)
  | localTokens (tokens : List String)
  deriving Repr

def lookup (context : Context) (name : String) : Option (Option Binding) := do
  match context.locals.filter (fun entry => entry.1 == name) with
  | [] =>
      if context.removed.contains name then some none else do
        let record ← C11PredefinedRecords.lookup context.captured name
        return record.map Binding.captured
  | [(_, tokens)] => some (some (.localTokens tokens))
  | _ => none

/-- Checked fallback retains poison/refusal; it does not assume a successful
lookup or actual-world absence. Opaque parameters prevent expanding a whole
captured roster just to expose its fixed lookup operation. -/
theorem lookup_capture_fallback (context : Context) (name : String)
    (noLocal : context.locals.filter (fun entry => entry.1 == name) = [])
    (notRemoved : context.removed.contains name = false) :
    lookup context name = (C11PredefinedRecords.lookup context.captured name).map
      (fun record => record.map Binding.captured) := by
  unfold lookup
  rw [noLocal, notRemoved]
  cases C11PredefinedRecords.lookup context.captured name <;> rfl

def value : Nat → Context → String → Option Nat
  | 0, _, _ => none
  | fuel + 1, context, name => do
      if name == "defined" || name == "_Pragma" || name == "__VA_ARGS__" then none else
        match ← lookup context name with
        | none => some 0
        | some binding => do
          let tokens ← match binding with
            | .localTokens tokens => some tokens
            | .captured record =>
                if record.functionLike then some ["0"]
                else CAtomicDropSyntax.tokenize record.tail.toUTF8.data.toList
          let [token] := tokens | none
          match C11PPConditions.number token with
          | some result => some result
          | none =>
              if C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes token) []
              then value fuel context token else none

def resolve (context : Context) : C11PPConditions.Expr → Option C11PPConditions.Resolved
  | .number n => some (.number n)
  | .defined name => do
      let binding ← lookup context name
      return .number (if binding.isSome then 1 else 0)
  | .identifier name => do return .number (← value 64 context name)
  | .not operand => do return .not (← resolve context operand)
  | .and left right => do return .and (← resolve context left) (← resolve context right)
  | .compare operation left right => do return .compare operation (← resolve context left) (← resolve context right)

structure State where
  context : Context
  stack : List Frame := []
  reversedOutput : List (List String) := []
  deriving Repr

def active (state : State) : Bool := match state.stack with
  | [] => true
  | frame :: _ => frame.active
private def push (state : State) (selected : Bool) : State :=
  { state with stack := { parent := active state, active := active state && selected, taken := active state && selected } :: state.stack }

def condition (state : State) (expression : C11PPConditions.Expr) : Option Bool := do
  let resolved ← resolve state.context expression
  return C11PPConditions.evaluate resolved != 0

def step (state : State) : C11ConditionalHeaders.Directive → Option State
  | .condition expression => do
      let selected ← if active state then condition state expression else some false
      return push state selected
  | .elifCondition expression => do
      let frame :: rest := state.stack | none
      if frame.sawElse then none else do
        let selected ← if frame.parent && !frame.taken then condition state expression else some false
        return { state with stack := { frame with active := frame.parent && !frame.taken && selected, taken := frame.taken || selected } :: rest }
  | .base directive => match directive with
    | .empty => some state
    | .ordinary tokens => some (if active state then
        { state with reversedOutput := tokens :: state.reversedOutput } else state)
    | .ifdef name => do return push state (← lookup state.context name).isSome
    | .ifndef name => do return push state (!(← lookup state.context name).isSome)
    | .otherwise => do
        let frame :: rest := state.stack | none
        if frame.sawElse then none else
          some { state with stack := { frame with active := frame.parent && !frame.taken, taken := true, sawElse := true } :: rest }
    | .endif => do
        let _ :: rest := state.stack | none
        return { state with stack := rest }
    | .define name tokens => do
        if name == "defined" then none else
          if !active state then some state else
            if (← lookup state.context name).isSome then none else
              some { state with context := { state.context with
                  locals := (name, tokens) :: state.context.locals } }
    | .undef name =>
        if !active state then some state else
          some { state with context := { state.context with
              locals := state.context.locals.filter (fun entry => entry.1 != name), removed := if state.context.removed.contains name then state.context.removed
                else name :: state.context.removed } }

/-- Source-model definition update under checked parser-state facts. The
complete baseline remains opaque and unchanged in this generic proof. -/
theorem define_fresh (state : State) (name : String) (tokens : List String)
    (ordinaryName : (name == "defined") = false)
    (selected : active state = true)
    (fresh : lookup state.context name = some none) :
    step state (.base (.define name tokens)) =
      some { state with context := { state.context with locals := (name, tokens) :: state.context.locals } } := by
  simp only [step, ordinaryName, selected, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [fresh]
  rfl

private def processTokens (context : Context) (tokens : List String) : Option State := do
  let lines ← C11HeaderGuards.lines tokens
  let state ← lines.foldlM (fun state line => do
    let directive ← C11ConditionalHeaders.parseLine line
    step state directive) { context := context }
  if state.stack.isEmpty then some state else none

/-- Fixed complete readers at both boundaries; no materializer callback,
external branch Boolean, selected-name inventory or success certificate. -/
def process (capturedInput : List Char) (source : String) : Option State := do
  let captured ← C11PredefinedRecords.finish (C11PredefinedRecords.feed (some {}) capturedInput)
  if !C11DirectiveLines.supported source then none else do
    if !source.isEmpty && source.toList.getLast? != some '\n' then none else do
      let tokens ← C11DirectiveLexer.tokenize source
      processTokens { capturedInput := capturedInput, captured := captured } tokens

/-- Fixed complete readers compose with the exact token transition pipeline.
The arguments are checked reader equations, not a caller materializer/Boolean.
All actual data premises must be discharged separately. -/
theorem process_readers (input : List Char) (source : String)
    (records : List C11PredefinedRecords.Record) (tokens : List String)
    (inventory : C11PredefinedRecords.finish (C11PredefinedRecords.feed (some {}) input) = some records)
    (supported : C11DirectiveLines.supported source = true)
    (newline : source.toList.getLast? = some '\n')
    (lexed : C11DirectiveLexer.tokenize source = some tokens) :
    process input source = (do
      let lines ← C11HeaderGuards.lines tokens
      let state ← lines.foldlM (fun state line => do
        let directive ← C11ConditionalHeaders.parseLine line
        step state directive) { context := { capturedInput := input, captured := records } }
      if state.stack.isEmpty then some state else none) := by
  unfold process
  rw [inventory, supported, newline]
  rw [Bool.and_comm, lexed]
  rfl

theorem source_undef_replaces_captured_binding :
    (process "#define x 1\n".toList "#undef x\n#define x 0\n#if x\nwrong\n#else\nselected\n#endif\n").map
      (fun state => state.reversedOutput.reverse) = some [["selected"]] := by rfl

theorem local_alias_can_reach_captured_binding :
    (process "#define x 1\n".toList "#define alias x\n#if alias\nselected\n#endif\n").map
      (fun state => state.reversedOutput.reverse) = some [["selected"]] := by rfl

theorem unsupported_reached_capture_refused :
    process "#define x unsupported + body\n".toList "#if x\nwrong\n#endif\n" = none := by rfl

theorem malformed_capture_cannot_be_skipped :
    process "not a record\n".toList "#if 0\nwrong\n#endif\n" = none := by rfl
end C11InventoryContext
