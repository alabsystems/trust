-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderDeclarations
import C11DirectiveLines

/-! Source directive/guard processing for the supported header subset.
Branch decisions are derived from parsed source and macro presence, never from
producer Boolean annotations. Ordinary-line output is ACTIVE BUT UNEXPANDED;
this is not a full C preprocessor/type/source-execution certificate. Proposed
initial context completeness, includes, #if/#elif expression evaluation,
function macros and target/predefined-context binding remain separate. -/
namespace C11HeaderGuards
open C11HeaderDeclarations
inductive Directive where
  | empty
  | ifdef (name : String)
  | ifndef (name : String)
  | otherwise
  | endif
  | define (name : String) (replacement : List String)
  | undef (name : String)
  | ordinary (tokens : List String)
  deriving DecidableEq, BEq, Repr
private def reservedOperator (name : String) : Bool := name == "_Pragma" || name == "__VA_ARGS__"
private def identifier (name : String) : Bool :=
  C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes name) []

def parseLine : List String → Option Directive
  | [] => some .empty
  | ["#", "ifdef", name] => if identifier name then some (.ifdef name) else none
  | ["#", "ifndef", name] => if identifier name then some (.ifndef name) else none
  | ["#", "else"] => some .otherwise
  | ["#", "endif"] => some .endif
  | ["#", "undef", name] => if identifier name then some (.undef name) else none
  | "#" :: "define" :: name :: replacement =>
      if identifier name && !reservedOperator name && replacement.head? != some "(" &&
        !replacement.contains "#" && !replacement.contains "##"
      then some (.define name replacement) else none
  | "#" :: _ => none
  | tokens => some (.ordinary tokens)

structure Frame where
  parent : Bool
  active : Bool
  taken : Bool
  sawElse : Bool := false
  deriving DecidableEq, BEq, Repr
structure State where
  macros : List (String × List String) := []
  stack : List Frame := []
  reversedOutput : List (List String) := []
  deriving DecidableEq, BEq, Repr

def active (state : State) : Bool :=
  match state.stack with | [] => true | frame :: _ => frame.active
private def defined (state : State) (name : String) : Bool :=
  state.macros.any (fun entry => entry.1 == name)
private def push (state : State) (condition : Bool) : State :=
  { state with stack := { parent := active state, active := active state && condition, taken := active state && condition } :: state.stack }

/-- Duplicate definitions refuse conservatively. A future general preprocessor
must check C's compatible-redefinition rule, never silently select first/last. -/
def step (state : State) : Directive → Option State
  | .empty => some state
  | .ifdef name => some (push state (defined state name))
  | .ifndef name => some (push state (!defined state name))
  | .otherwise => do
      let frame :: rest := state.stack | none
      if frame.sawElse then none else
        some { state with stack := { frame with active := frame.parent && !frame.taken, taken := true, sawElse := true } :: rest }
  | .endif => do
      let _ :: rest := state.stack | none
      some { state with stack := rest }
  | .define name replacement =>
      if !active state then some state
      else if defined state name then none
      else some { state with macros := state.macros ++ [(name, replacement)] }
  | .undef name =>
      if !active state then some state
      else some { state with macros := state.macros.filter (fun entry => entry.1 != name) }
  | .ordinary tokens =>
      if active state then some { state with reversedOutput := tokens :: state.reversedOutput }
      else some state

/-- Physical newlines remain separators. Nonempty trailing source tokens are
not discarded; a missing terminating newline refuses this complete-file API. -/
def lines (tokens : List String) : Option (List (List String)) :=
  let (done, pending) := tokens.foldl (fun (done, pending) token =>
    if token == "\n" then (pending.reverse :: done, []) else (done, token :: pending)) ([], [])
  if pending.isEmpty then some done.reverse else none

def validInitial (macros : List (String × List String)) : Bool :=
  macros.all (fun entry => identifier entry.1 && !reservedOperator entry.1) &&
    (macros.map (·.1)).eraseDups.length == macros.length

def processTokens (initialMacros : List (String × List String)) (tokens : List String) : Option State := do
  if !validInitial initialMacros then none else do
    let lines ← lines tokens
    let state ← lines.foldlM (fun state line => do
      let directive ← parseLine line
      step state directive) { macros := initialMacros }
    if state.stack.isEmpty then some state else none

def process (initialMacros : List (String × List String)) (source : String) : Option State := do
  if !C11DirectiveLines.supported source then none else do
    if !source.isEmpty && source.toList.getLast? != some '\n' then none else do
      let tokens ← C11DeclarationLexer.tokenize source
      processTokens initialMacros tokens

/-- Guard-pattern unit control only; the separate full-owner subject retains
all actual SDK header bytes including its copyright/comment prefix. -/
def header : String := "#ifndef _UINT32_T\n#define _UINT32_T\ntypedef unsigned int uint32_t;\n#endif\n"

theorem first_guard_include : (process [] header).map (fun state =>
    (state.macros, state.reversedOutput.reverse, state.stack)) =
    some ([("_UINT32_T", [])], [["typedef", "unsigned", "int", "uint32_t", ";"]], []) := by rfl

theorem repeated_guard_include : (process [("_UINT32_T", [])] header).map (fun state =>
    (state.macros, state.reversedOutput, state.stack)) = some ([("_UINT32_T", [])], [], []) := by rfl

theorem inactive_define_does_not_poison :
    (process [] "#ifdef absent\n#define changed yes\n#endif\n").map (·.macros) = some [] := by rfl

theorem undef_changes_later_guard :
    (process [("present", [])] "#undef present\n#ifndef present\nselected\n#endif\n").map
      (fun state => state.reversedOutput.reverse) = some [["selected"]] := by rfl

theorem duplicate_else_refused : process [] "#ifndef x\n#else\n#else\n#endif\n" = none := by rfl

theorem unmatched_endif_refused : process [] "#endif\n" = none := by rfl

theorem unclosed_guard_refused : process [] "#ifndef x\n" = none := by rfl

theorem unknown_directive_refused : process [] "#include other\n" = none := by rfl

theorem unknown_conditional_refused : process [] "#if expression\n#endif\n" = none := by rfl

theorem duplicate_input_context_refused : process [("x", []), ("x", [])] "" = none := by rfl
theorem comment_only_missing_newline_refused : process [] "/* comment */" = none := by rfl

theorem ordinary_missing_newline_refused : process [] "typedef int X;" = none := by rfl
theorem multiline_directive_comment_source_refused :
    process [] "#define X /*\n*/ typedef unsigned int uint32_t;\n#ifndef X\nnot_selected\n#endif\n" = none := by rfl

theorem manufactured_directive_source_refused :
    process [] "ordinary /*\n*/ #define X 1\n" = none := by rfl
end C11HeaderGuards
