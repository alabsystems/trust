-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderAtomic

/-! A finite, explicitly restricted global atomic scenario for the next proof
layer. ALL other threads perform constant relaxed stores only. The distinguished
thread performs relaxed loads, one or more RMWs and acquire fences; it has no
ordinary memory actions. Hence there is no cross-thread acquire/release edge in
this scenario. This restriction is checked, not assumed from the first load.

The validator checks per-object modification order, immediate RMW predecessor,
read-from values and the four coherence rules against initialization and
sequenced-before. N1570 5.1.2.4 and 7.17.3 are the normative input. This is NOT a
full C11 axiomatic model or a proved adequacy theorem: global initialization,
thread creation/join, source expressions, mixed accesses, fences outside this
slice, C types/layout/lifetime and independent source rights remain separate.
No candidate event table or `check = true` earns runtime permission. -/
namespace C11HeaderGlobal
open C11HeaderAST
inductive Operation where
  | initial (value : UInt32)
  | store (value : UInt32) -- this slice permits RELAXED constant stores only
  | load (value : UInt32)
  | rmw (subtract : Bool) (operand old new : UInt32) (order : Order)
  | acquireFence
  deriving DecidableEq, Repr
structure Event where
  thread : Nat
  operation : Operation
  modification : Option Nat := none
  readsFrom : Option Nat := none -- event-table index, not a value or rank
  deriving DecidableEq, Repr
structure Execution where
  distinguished : Nat
  events : List Event
  deriving DecidableEq, Repr

def written : Operation → Option UInt32
  | .initial value | .store value => some value
  | .rmw _ _ _ value _ => some value
  | _ => none

def read : Operation → Option UInt32
  | .load value | .rmw _ _ value _ _ => some value
  | _ => none

def hb (events : List Event) (a b : Nat) : Bool :=
  a < b && (a == 0 || (events[a]?.map (·.thread)) == (events[b]?.map (·.thread)))

/-- Initial event happens before all worker events; otherwise only same-thread
sequenced-before is present in this checked no-cross-synchronization scenario. -/
def shape (execution : Execution) (index : Nat) (event : Event) : Bool :=
  match event.operation with
  | .initial _ => index == 0 && event.modification == some 0 && event.readsFrom == none
  | .store _ => index != 0 && event.thread != execution.distinguished &&
      event.modification.isSome && event.readsFrom == none
  | .load _ => event.thread == execution.distinguished && event.modification == none && event.readsFrom.isSome
  | .rmw subtract operand old new order => event.thread == execution.distinguished &&
      event.modification.isSome && event.readsFrom.isSome && order != .acquire &&
      decide (new = if subtract then old - operand else old + operand)
  | .acquireFence => event.thread == execution.distinguished &&
      event.modification == none && event.readsFrom == none

/-- The matching write exists, has the observed value and is in modification
order. For an RMW, its own modification rank is EXACTLY source rank + 1. -/
def readFromValid (events : List Event) (event : Event) : Bool :=
  match read event.operation, event.readsFrom with
  | none, none => true
  | some value, some source =>
      match events[source]? with
      | none => false
      | some writer =>
          written writer.operation == some value && writer.modification.isSome &&
          match event.operation with
          | .rmw .. => event.modification == writer.modification.map (· + 1)
          | _ => true
  | _, _ => false

def sourceRank (events : List Event) (event : Event) : Option Nat :=
  event.readsFrom.bind (fun source => events[source]?.bind (·.modification))

def ordered (relation : Nat → Nat → Bool) : Option Nat → Option Nat → Bool
  | some a, some b => relation a b
  | _, _ => true

def coherent (events : List Event) (i j : Nat) (a b : Event) : Bool :=
  if hb events i j then
    -- write/write, write/read, read/write, read/read coherence respectively.
    ordered (fun x y => x < y) a.modification b.modification &&
    ordered (fun x y => x ≤ y) a.modification (sourceRank events b) &&
    ordered (fun x y => x < y) (sourceRank events a) b.modification &&
    ordered (fun x y => x ≤ y) (sourceRank events a) (sourceRank events b)
  else true

/-- Dense total modification order: exactly one event at every rank below the
number of writes, and every writer's rank lies inside that range. -/
def modificationOrder (events : List Event) : Bool :=
  let writes := events.filter (fun event => (written event.operation).isSome)
  writes.all (fun event => match event.modification with
    | none => false
    | some rank => rank < writes.length) &&
  (List.range writes.length).all (fun rank =>
    (writes.filter (fun event => event.modification == some rank)).length == 1) &&
  events.all (fun event => event.modification.isSome == (written event.operation).isSome)

def check (execution : Execution) : Bool :=
  !execution.events.isEmpty &&
  (execution.events[0]?.map (fun event => match event.operation with
    | .initial _ => true | _ => false)) == some true &&
  execution.events.zipIdx.all (fun (event, index) => shape execution index event) &&
  modificationOrder execution.events &&
  execution.events.all (readFromValid execution.events) &&
  execution.events.zipIdx.all (fun (a, i) =>
    execution.events.zipIdx.all (fun (b, j) => coherent execution.events i j a b))

/-- Exact DATA transport from the event table to the fragment's local atomic
trace. Missing RF metadata or foreign non-store actions refuse; they are not
silently erased. Global consistency must be checked separately. -/
def project (execution : Execution) : Option (List C11HeaderAtomic.Event) :=
  execution.events.foldl (fun accumulated event => do
    let output ← accumulated
    match event.operation with
    | .initial _ | .store _ => return output
    | .load value =>
        if event.thread != execution.distinguished then none else do
          let rank ← sourceRank execution.events event
          return output ++ [.load rank value]
    | .rmw _ _ old value order =>
        if event.thread != execution.distinguished then none else do
          let rank ← sourceRank execution.events event
          return output ++ [.rmw rank old value order]
    | .acquireFence =>
        if event.thread != execution.distinguished then none
        else return output ++ [.fence .acquire]) (some [])

/-- A checked RMW's read is attached to the actual immediately preceding
write, with its exact value. Equal numeric values at another rank cannot witness
this property. This is a local checker-soundness fact, not C11 adequacy. -/
theorem read_from_rmw_sound (events : List Event) (event : Event)
    (subtract : Bool) (operand old value : UInt32) (order : Order)
    (operation : event.operation = .rmw subtract operand old value order)
    (accepted : readFromValid events event = true) :
    ∃ source writer rank,
      event.readsFrom = some source ∧ events[source]? = some writer ∧
      written writer.operation = some old ∧ writer.modification = some rank ∧
      event.modification = some (rank + 1) := by
  cases rf : event.readsFrom with
  | none => simp [readFromValid, operation, rf, C11HeaderGlobal.read] at accepted
  | some source =>
    cases lookup : events[source]? with
    | none => simp [readFromValid, operation, rf, lookup, C11HeaderGlobal.read] at accepted
    | some writer =>
      cases modification : writer.modification with
      | none => simp [readFromValid, operation, rf, lookup, modification, C11HeaderGlobal.read] at accepted
      | some rank =>
        have facts : written writer.operation = some old ∧
            event.modification = some (rank + 1) := by
          simpa [readFromValid, operation, rf, lookup, modification, C11HeaderGlobal.read] using accepted
        exact ⟨source, writer, rank, rfl, lookup, facts.1, modification, facts.2⟩

/-- A checked finite scenario is DATA satisfying the explicit relation above;
this is intentionally not named C11 source correctness or a permission token. -/
structure CheckedScenario (execution : Execution) : Prop where
  accepted : check execution = true

end C11HeaderGlobal
