-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderAtomic

/-! Execution of the typed restricted AST against the explicit atomic projection.
This interprets SOURCE control flow (including && and early return), not a header
arithmetic oracle. A single symbolic object/address is modeled; no assertion about
actual clean_obj layout, pointer tags, lifetime, C aliasing, or source-owned rights.
Macro values are looked up, never inferred from familiar names. Resolution of the
AST intrinsic/type/field roles against the actual preprocessed TU remains owed. -/
namespace C11HeaderExecution
open C11HeaderAST C11HeaderAtomic

abbrev Value : Ty → Type
  | .u32 => UInt32
  | .boolean => Bool
  | .objectPtr => Bool -- scalar-tag observation only; not a C pointer encoding
  | .atomicPtr | .unit => Unit
structure Machine where
  atomic : State
  scalar : Bool := false
  headerAccessible : Bool := true
  macros : List (String × UInt32) := []
  deriving Repr
inductive Fault where
  | atomic : Error → Fault
  | missingMacro (name : String)
  deriving DecidableEq, Repr
abbrev Eval (α : Type) := StateT Machine (Except Fault) α

def atom (operation : State → Except Error (α × State)) : Eval α := fun machine =>
  match operation machine.atomic with
  | .error error => .error (.atomic error)
  | .ok (value, state) => .ok (value, { machine with atomic := state })

def evaluate : {t : Ty} → Expr t → Eval (Value t)
  | _, .argument => do return (← get).scalar
  | _, .headerAddress object => do
      let scalar ← evaluate object
      if scalar || !(← get).headerAccessible then throw (.atomic .invalidAddress)
      return ()
  | _, .scalar object => do
      let value ← evaluate object
      return value
  | _, .word value => pure value
  | _, .macro name => do
      let some value := (← get).macros.lookup name | throw (.missingMacro name)
      return value
  | _, .truth value => pure value
  | _, .load pointer => do
      let _ ← evaluate pointer
      atom C11HeaderAtomic.load
  | _, .fetchAdd pointer value order => do
      let _ ← evaluate pointer
      let operand ← evaluate value
      atom (rmw false operand order)
  | _, .fetchSub pointer value order => do
      let _ ← evaluate pointer
      let operand ← evaluate value
      atom (rmw true operand order)
  | _, .ge a b => do return decide ((← evaluate a) ≥ (← evaluate b))
  | _, .lt a b => do return decide ((← evaluate a) < (← evaluate b))
  | _, .ne a b => do return (← evaluate a) != (← evaluate b)
  | _, .not a => do return !(← evaluate a)
  | _, .and a b => do
      if ← evaluate a then evaluate b else pure false

def execute : Stmt t → Eval (Option (Value t))
  | .skip => pure none
  | .block body => execute body
  | .sequence a b => do
      match ← execute a with
      | some value => pure (some value)
      | none => execute b
  | .branch condition yes no => do
      if ← evaluate condition then execute yes else execute no
  | .expression expression => do
      let _ ← evaluate expression
      pure none
  | .fence order => do
      let machine ← get
      match C11HeaderAtomic.fence order machine.atomic with
      | .error error => throw (.atomic error)
      | .ok state => set { machine with atomic := state }
      pure none
  | .ret value => do return some (← evaluate value)

/-- Short-circuiting does not perform the RHS atomic action. -/
theorem false_and (right : Expr .boolean) (machine : Machine) :
    evaluate (.and (.truth false) right) machine = .ok (false, machine) := by rfl
/-- The second statement cannot run after a return. -/
theorem return_skips_tail (value : Bool) (tail : Stmt .boolean) (machine : Machine) :
    execute (.sequence (.ret (.truth value)) tail) machine =
      .ok (some value, machine) := by rfl

end C11HeaderExecution
