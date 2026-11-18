-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderAST

/-! A one-object atomic MODIFICATION-ORDER PROJECTION for the C fragments.
N1570 7.17.3p14 requires RMW to read the immediately preceding modification;
5.1.2.4 coherence constrains successive reads. A relaxed observation need not
be the later RMW's OLD. This is NOT full C11 consistency: cross-thread HB,
release sequences, fence synchronization, no-thin-air, lifetime, lock-free/target
and mixed/non-atomic access require a separate checked global execution owner.
The interference is INPUT DATA, not a certificate that a real C11 execution exists.
Unlike SC semAtomic, fences remain explicit events, with no invented HB edge. -/
namespace C11HeaderAtomic
open C11HeaderAST
structure Packet where
  interference : List UInt32 := []
  readFrom : Nat := 0
  deriving Repr
inductive Event where
  | load (readFrom : Nat) (value : UInt32)
  | rmw (predecessor : Nat) (old new : UInt32) (order : Order)
  | fence (order : Order)
  deriving DecidableEq, Repr
structure State where
  history : List UInt32
  readFloor : Nat := 0
  schedule : List Packet := []
  events : List Event := []
  deriving Repr
inductive Error where
  | emptyHistory | exhaustedSchedule | invalidReadFrom | coherenceViolation
  | unsupportedOrder | invalidAddress
  deriving DecidableEq, Repr

def load (s : State) : Except Error (UInt32 × State) := do
  let packet :: rest := s.schedule | throw .exhaustedSchedule
  let history := s.history ++ packet.interference
  if s.history.isEmpty then throw .emptyHistory
  if packet.readFrom < s.readFloor then throw .coherenceViolation
  let some value := history[packet.readFrom]? | throw .invalidReadFrom
  return (value, { s with history := history, readFloor := packet.readFrom, schedule := rest, events := s.events ++ [.load packet.readFrom value] })

def rmw (subtract : Bool) (operand : UInt32) (order : Order) (s : State) :
    Except Error (UInt32 × State) := do
  if order == .acquire then throw .unsupportedOrder
  let packet :: rest := s.schedule | throw .exhaustedSchedule
  if s.history.isEmpty then throw .emptyHistory
  let history := s.history ++ packet.interference
  let some old := history.getLast? | throw .emptyHistory
  let index := history.length - 1
  if index < s.readFloor then throw .coherenceViolation
  let value := if subtract then old - operand else old + operand
  return (old, { s with history := history ++ [value], readFloor := history.length, schedule := rest, events := s.events ++ [.rmw index old value order] })

/-- Fence event only: synchronization is a global-execution obligation. -/
def fence (order : Order) (s : State) : Except Error State :=
  if order == .acquire then .ok { s with events := s.events ++ [.fence order] }
  else .error .unsupportedOrder
end C11HeaderAtomic
